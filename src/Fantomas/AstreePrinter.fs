module internal Fantomas.AstreePrinter

open Fantomas
open Fantomas.FsAstTypes
open Fantomas.ASTree
open Fantomas.Context
open FSharp.Compiler

let genTrivia node f =
    let contentBefore = node.Trivias |> List.collect (fun t -> t.ContentBefore)
    let contentAfter = node.Trivias |> List.collect (fun t -> t.ContentAfter)
    col sepNone contentBefore printTriviaContent +> f +> col sepNone contentAfter printTriviaContent

let genLId (lids: Id list) = lids |> List.map (fun x -> x.Ident) |> String.concat "."
let genAccess (SourceParser.Access s) = !- s

let rec genSource (astContext: CodePrinter.ASTContext) node =
    let getProp chooser = node.Properties |> List.pick chooser
    let tryGetProp chooser = node.Properties |> List.tryPick chooser
    let gen = genSource astContext
    let genChilds sep = col sep node.Childs gen
    let genMore sep xs = col sep xs gen
    let tryGetFirstChild typeFilter = List.tryHead (node.Childs |> List.filter (fun n -> typeFilter n.Type))
    let getFirstChild typeFilter = List.head (node.Childs |> List.filter (fun n -> typeFilter n.Type))
    let filterChilds typeFilter = node.Childs |> List.filter (fun n -> typeFilter n.Type)
    match node.Type with
    | File -> genChilds sepNone
    | SigFile -> genChilds sepNone
    | SynModuleOrNamespace_AnonModule
    | SynModuleOrNamespace_DeclaredNamespace
    | SynModuleOrNamespace_GlobalNamespace
    | SynModuleOrNamespace_NamedModule ->
        let moduleKind = getProp (function IsModule x -> Some x | _ -> None)
        let isRecursive = getProp (function IsRecursive x -> Some x | _ -> None)
        let s = getProp (function LongIdent x -> Some x | _ -> None) |> genLId
        let ao = tryGetProp (function Access x -> Some x | _ -> None)
        let sepModuleAndFirstDecl =
            let firstDecl = tryGetFirstChild FsAstType.isSynModuleDecl
            match firstDecl with
            | None ->
                if moduleKind.IsModule then
                    sepNlnForEmptyModule node.Range.Value +> sepNln
                else
                    sepNlnForEmptyNamespace node.Range.Value +> sepNln
            | Some mdl ->
                //let attrRanges = getRangesFromAttributesFromModuleDeclaration mdl
                //sepNlnConsideringTriviaContentBeforeWithAttributes mdl.Range attrRanges +> sepNln
                sepNln

        let genTriviaForLongIdent (f: Context -> Context) =
            match node.Type with
            | SynModuleOrNamespace_DeclaredNamespace ->
                let lId = filterChilds (function FsAstType.Ident -> true | _ -> false) 
                lId
                |> List.fold (fun (acc: Context -> Context) (ident) -> acc |> (genTrivia ident)) f
            | _ -> f

        let moduleOrNamespace = ifElse moduleKind.IsModule (!- "module ") (!- "namespace ")
        let recursive = ifElse isRecursive (!- "rec ") sepNone
        let namespaceFn = ifElse (s = "") (!- "global") (!- s)
        let namespaceIsGlobal = not moduleKind.IsModule && s = ""

        let sep = 
            if namespaceIsGlobal 
            then sepNln +> sepNlnConsideringTriviaContentBefore node.Range.Value
            else sepModuleAndFirstDecl

        let expr =
            //genPreXmlDoc px
            //+> genAttributes astContext ats
            //+>
            ifElse (moduleKind = SyntaxTree.SynModuleOrNamespaceKind.AnonModule)
                 sepNone
                 (genTriviaForLongIdent (moduleOrNamespace +> opt sepSpace ao genAccess +> recursive +> namespaceFn +> sep))

        expr +> genChilds sepNone
    
    | SynModuleDecl_Let -> genChilds sepNone
    | Binding ->
        let pat = getFirstChild FsAstType.isSynPat
        let body = getFirstChild FsAstType.isSynExpr
        let valData = getFirstChild ((=)FsAstType.SynValData)
        let attributes = filterChilds ((=)FsAstType.SynAttributeList)
        let ao = tryGetProp (function Access x -> Some x | _ -> None)
        let isMutable = getProp (function IsMutable x -> Some x | _ -> None)
        let isInline = getProp (function IsInline x -> Some x | _ -> None)
        let pref = "let" //TODO: "and"
        
        let genPat = gen pat
//            match e, p with
//            | TypedExpr(Typed, _, t),  PatLongIdent(ao, s, ps, tpso) when (List.length ps > 1)->
//                genPatWithReturnType ao s ps tpso (Some t) astContext
//            | _,  PatLongIdent(ao, s, ps, tpso) when (List.length ps > 1)->
//                genPatWithReturnType ao s ps tpso None astContext
//            | _ ->
//                genPat astContext p

        let genAttr =
            ifElse astContext.IsFirstChild
                (genMore sepNone attributes -- pref)
                (!- pref +> genMore sepNone attributes)
        let afterLetKeyword =
            opt sepSpace ao genAccess
            +> ifElse isMutable (!- "mutable ") sepNone
            +> ifElse isInline (!- "inline ") sepNone

//        let rangeBetweenBindingPatternAndExpression =
//            mkRange "range between binding pattern and expression" b.RangeOfBindingSansRhs.End e.Range.Start

        //genPreXmlDoc px
        //+>
        genAttr // this already contains the `let` or `and` keyword
        +> leadingExpressionIsMultiline
               (afterLetKeyword +> genPat
                //+> enterNodeTokenByName rangeBetweenBindingPatternAndExpression "EQUALS"
                )
               //(genExprSepEqPrependType astContext p e (Some(valInfo)))
                (fun _ -> gen body)
    
    |> genTrivia node
        
