module Fantomas.AstTransformer

open Fantomas.FsAstTypes
open FSharp.Compiler.Range
open FSharp.Compiler.SyntaxTree
open Fantomas.TriviaTypes

let rec (|Sequentials|_|) = function
    | SynExpr.Sequential(_, isTrueSeq, e, Sequentials es, range) ->
        Some((isTrueSeq, e, None, range)::es)
    | SynExpr.Sequential(_, isTrueSeq, e1, e2, range) ->
        Some [isTrueSeq, e1, Some e2, range]
    | _ -> None

type FsAstNode = obj

type Node =
    { Type: FsAstType
      Range: range option
      Properties: FsAstProp list
      Childs: Node list
      FsAstNode: FsAstNode }

module Helpers =
    let r(r: FSharp.Compiler.Range.range): range option =
        Some r

    let p = id
    let inline (==>) a b = (a,box b)

    let noRange =
        None

    let i (id: Ident) : Id =
        { Ident = id.idText
          Range = r id.idRange}

    let li (id: LongIdent) =
        id |> List.map i

    let lid (id: LongIdentWithDots) = li id.Lid

module private Ast =
    open Helpers

    let rec visit(ast: SynModuleOrNamespace ): Node =
        visitSynModuleOrNamespace ast

    and visitSynModuleOrNamespace (modOrNs: SynModuleOrNamespace): Node =
        match modOrNs with
        | SynModuleOrNamespace(longIdent,isRecursive,isModule,decls,_,attrs,access,range) ->
            let collectIdents (idents: LongIdent) =
                idents
                |> List.map (fun ident ->
                    { Type = FsAstType.Ident
                      Range = r ident.idRange
                      Properties = []
                      FsAstNode = ident
                      
                      
                      Childs = [] })
            {Type =
                match isModule with
                | SynModuleOrNamespaceKind.AnonModule -> FsAstType.SynModuleOrNamespace_AnonModule
                | SynModuleOrNamespaceKind.DeclaredNamespace -> FsAstType.SynModuleOrNamespace_DeclaredNamespace
                | SynModuleOrNamespaceKind.GlobalNamespace -> FsAstType.SynModuleOrNamespace_GlobalNamespace
                | SynModuleOrNamespaceKind.NamedModule -> FsAstType.SynModuleOrNamespace_NamedModule
             Range = r range
             Properties =
                 p [yield FsAstProp.IsRecursive (isRecursive)
                    yield FsAstProp.IsModule (isModule)
                    yield FsAstProp.LongIdent (li longIdent)
                    if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = modOrNs
             
             
             Childs =
                 [yield! (if isModule = SynModuleOrNamespaceKind.DeclaredNamespace then collectIdents longIdent else [])
                  yield! attrs |> List.map visitSynAttributeList
                  yield! (decls |> List.map visitSynModuleDecl)]}

    and visitSynModuleDecl(ast: SynModuleDecl) : Node =
        match ast with
        | SynModuleDecl.ModuleAbbrev(ident,longIdent,range) ->
            {Type = FsAstType.SynModuleDecl_ModuleAbbrev
             Range = r range
             Properties =
                 p [FsAstProp.Ident (i ident)
                    FsAstProp.LongIdent (li longIdent)]
             FsAstNode = ast
             
             
             Childs = []}
        | SynModuleDecl.NestedModule(sci,isRecursive,decls,_,range) ->
            {Type = FsAstType.SynModuleDecl_NestedModule
             Range = r range
             Properties = p [FsAstProp.IsRecursive (isRecursive)]
             FsAstNode = ast
             
             
             Childs =
                 [yield visitSynComponentInfo sci
                  yield! (decls |> List.map visitSynModuleDecl)]}
        | SynModuleDecl.Let(_,bindings,range) ->
            {Type = FsAstType.SynModuleDecl_Let
             Range = r range
             Properties = p []
             FsAstNode = ast
             
             
             Childs = bindings |> List.map visitSynBinding}
        | SynModuleDecl.DoExpr(_,expr,range) ->
            {Type = FsAstType.SynModuleDecl_DoExpr
             Range = r range
             Properties = p []
             FsAstNode = ast
             
             
             Childs = [visitSynExpr expr]}
        | SynModuleDecl.Types(typeDefs,range) ->
            {Type = FsAstType.SynModuleDecl_Types
             Range = r range
             Properties = p []
             FsAstNode = ast
             
             
             Childs = typeDefs |> List.map visitSynTypeDefn}
        | SynModuleDecl.Exception(exceptionDef,range) ->
            {Type = FsAstType.SynModuleDecl_Exception
             Range = r range
             Properties = p []
             FsAstNode = ast
             
             
             Childs = [visitSynExceptionDefn exceptionDef]}
        | SynModuleDecl.Open(longDotId,range) ->
            {Type = FsAstType.SynModuleDecl_Open
             Range = r range
             Properties = p [FsAstProp.LongIdent (lid longDotId)]
             FsAstNode = ast
             
             
             Childs = []}
        | SynModuleDecl.Attributes(attrs,range) ->
            {Type = FsAstType.SynModuleDecl_Attributes
             Range = r range
             Properties = p []
             FsAstNode = ast
             
             
             Childs = attrs |> List.map visitSynAttributeList}
        | SynModuleDecl.HashDirective(hash,range) ->
            {Type = FsAstType.SynModuleDecl_HashDirective
             Range = r range
             Properties = p []
             FsAstNode = ast
             
             
             Childs = [visitParsedHashDirective hash]}
        | SynModuleDecl.NamespaceFragment(moduleOrNamespace) ->
            {Type = FsAstType.SynModuleDecl_NamespaceFragment
             Range = noRange
             Properties = p []
             FsAstNode = ast
             
             
             Childs = [visitSynModuleOrNamespace moduleOrNamespace]}

    and visitSynExpr(synExpr: SynExpr): Node =
        match synExpr with
        | SynExpr.Paren(expr,leftParenRange,rightParenRange,range) ->
            {Type = FsAstType.SynExpr_Paren
             Range = r range
             Properties =
                 p [yield FsAstProp.LeftParenRange (leftParenRange)
                    if rightParenRange.IsSome then yield FsAstProp.RightParenRange (rightParenRange.Value)]
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.Quote(operator,isRaw,quotedSynExpr,isFromQueryExpression,range) ->
            {Type = FsAstType.SynExpr_Quote
             Range = r range
             Properties =
                 p [FsAstProp.IsRaw (isRaw)
                    FsAstProp.IsFromQueryExpression (isFromQueryExpression)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr operator
                  yield visitSynExpr quotedSynExpr]}
        | SynExpr.Const(constant,range) ->
            {Type = FsAstType.SynExpr_Const
             Range = r range
             Properties = p [FsAstProp.Constant (constant)]
             FsAstNode = synExpr
             
             
             Childs = []}
        | SynExpr.Typed(expr,typeName,range) ->
            {Type = FsAstType.SynExpr_Typed
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield visitSynType typeName]}
        | SynExpr.Tuple(isStruct,exprs,commaRanges,range) ->
            {Type = FsAstType.SynExpr_Tuple
             Range = r range
             Properties = p [FsAstProp.IsStruct isStruct; FsAstProp.CommaRanges (commaRanges)]
             FsAstNode = synExpr
             
             
             Childs = [yield! exprs |> List.map visitSynExpr]}
        | SynExpr.ArrayOrList(isList,exprs,range) ->
            {Type = FsAstType.SynExpr_StructTuple
             Range = r range
             Properties = p [FsAstProp.IsList (isList)]
             FsAstNode = synExpr
             
             
             Childs = [yield! exprs |> List.map visitSynExpr]}
        | SynExpr.Record(_,_,recordFields,range) ->
            {Type = FsAstType.SynExpr_Record
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield! recordFields |> List.map visitRecordField]}
        | SynExpr.AnonRecd(_,_,recordFields,range) ->
            {Type = FsAstType.SynExpr_AnonRecd
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield! recordFields |> List.map visitAnonRecordField]}
        | SynExpr.New(isProtected,typeName,expr,range) ->
            {Type = FsAstType.SynExpr_New
             Range = r range
             Properties = p [FsAstProp.IsProtected (isProtected)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield visitSynType typeName]}
        | SynExpr.ObjExpr(objType,argOptions,bindings,extraImpls,newExprRange,range) ->
            {Type = FsAstType.SynExpr_ObjExpr
             Range = r range
             Properties = p [FsAstProp.NewExprRange (newExprRange)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynType objType
                  if argOptions.IsSome then yield visitArgsOption argOptions.Value
                  yield! extraImpls |> List.map visitSynInterfaceImpl
                  yield! bindings |> List.map visitSynBinding]}
        | SynExpr.While(_,whileExpr,doExpr,range) ->
            {Type = FsAstType.SynExpr_While
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr whileExpr
                  yield visitSynExpr doExpr]}
        | SynExpr.For(_,ident,identBody,_,toBody,doBody,range) ->
            {Type = FsAstType.SynExpr_For
             Range = r range
             Properties = p [FsAstProp.Ident (i ident)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr identBody
                  yield visitSynExpr toBody
                  yield visitSynExpr doBody]}
        | SynExpr.ForEach(_,(SeqExprOnly seqExprOnly),isFromSource,pat,enumExpr,bodyExpr,range) ->
            {Type = FsAstType.SynExpr_ForEach
             Range = r range
             Properties =
                 p [FsAstProp.IsFromSource (isFromSource)
                    FsAstProp.SeqExprOnly (seqExprOnly)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynPat pat
                  yield visitSynExpr enumExpr
                  yield visitSynExpr bodyExpr]}
        | SynExpr.ArrayOrListOfSeqExpr(isArray,expr,range) ->
            {Type = FsAstType.SynExpr_ArrayOrListOfSeqExpr
             Range = r range
             Properties = p [FsAstProp.IsArray (isArray)]
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.CompExpr(isArrayOrList,isNotNakedRefCell,expr,range) ->
            {Type = FsAstType.SynExpr_CompExpr
             Range = r range
             Properties =
                 p [FsAstProp.IsArrayOrList (isArrayOrList)
                    FsAstProp.IsNotNakedRefCell (!isNotNakedRefCell)]
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.Lambda(fromMethod,inLambdaSeq,args,body,range) ->
            {Type = FsAstType.SynExpr_Lambda
             Range = r range
             Properties =
                 p [FsAstProp.FromMethod (fromMethod)
                    FsAstProp.InLambdaSeq (inLambdaSeq)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynSimplePats args
                  yield visitSynExpr body]}
        | SynExpr.MatchLambda(isExnMatch,_,matchClauses,_,range) ->
            {Type = FsAstType.SynExpr_MatchLambda
             Range = r range
             Properties = p [FsAstProp.IsExnMatch (isExnMatch)]
             FsAstNode = synExpr
             
             
             Childs = [yield! matchClauses |> List.map visitSynMatchClause]}
        | SynExpr.Match(_,expr,clauses,range) ->
            {Type = FsAstType.SynExpr_Match
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield! clauses |> List.map visitSynMatchClause]}
        | SynExpr.Do(expr,range) ->
            {Type = FsAstType.SynExpr_Do
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.Assert(expr,range) ->
            {Type = FsAstType.SynExpr_Assert
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.App(atomicFlag,isInfix,funcExpr,argExpr,range) ->
            {Type = FsAstType.SynExpr_App
             Range = r range
             Properties =
                 p [FsAstProp.AtomicFlag (atomicFlag)
                    FsAstProp.IsInfix (isInfix)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr funcExpr
                  yield visitSynExpr argExpr]}
        | SynExpr.TypeApp(expr,lESSrange,typeNames,commaRanges,gREATERrange,typeArgsRange,range) ->
            {Type = FsAstType.SynExpr_TypeApp
             Range = r range
             Properties =
                 p [yield FsAstProp.LESSrange (lESSrange)
                    yield FsAstProp.CommaRanges ((commaRanges))
                    if gREATERrange.IsSome then yield FsAstProp.GREATERrange (gREATERrange.Value)
                    yield FsAstProp.TypeArgsRange (typeArgsRange)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield! typeNames |> List.map visitSynType]}
        | SynExpr.LetOrUse(isRecursive,isUse,bindings,body,range) ->
            {Type = FsAstType.SynExpr_LetOrUse
             Range = r range
             Properties =
                 p [FsAstProp.IsRecursive (isRecursive)
                    FsAstProp.IsUse (isUse)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield! bindings |> List.map visitSynBinding
                  yield visitSynExpr body]}
        | SynExpr.TryWith(tryExpr,tryRange,withCases,withRange,range,_,_) ->
            {Type = FsAstType.SynExpr_TryWith
             Range = r range
             Properties =
                 p [FsAstProp.TryRange (tryRange)
                    FsAstProp.WithRange (withRange)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr tryExpr
                  yield! withCases |> List.map visitSynMatchClause]}
        | SynExpr.TryFinally(tryExpr,finallyExpr,range,_,_) ->
            {Type = FsAstType.SynExpr_TryFinally
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr tryExpr
                  yield visitSynExpr finallyExpr]}
        | SynExpr.Lazy(ex,range) ->
            {Type = FsAstType.SynExpr_Lazy
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr ex]}
        | Sequentials xs -> // use tail-rec active pattern to avoid stack overflow
            let rec cons xs =
                match xs with
                | [] -> failwith "should not happen" // expr2Opt is always Some in last item
                | ((isTrueSeq,expr1,expr2Opt,range)::rest) ->
                    {Type = FsAstType.SynExpr_Sequential
                     Range = r range
                     Properties = p [FsAstProp.IsTrueSeq (isTrueSeq)]
                     FsAstNode = synExpr
                     
                     
                     Childs =
                         [yield visitSynExpr expr1
                          yield expr2Opt |> Option.map visitSynExpr |> Option.defaultWith (fun () -> cons rest)]}
            cons xs
        | SynExpr.Sequential(_,isTrueSeq,expr1,expr2,range) ->
            {Type = FsAstType.SynExpr_Sequential
             Range = r range
             Properties = p [FsAstProp.IsTrueSeq (isTrueSeq)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr1
                  yield visitSynExpr expr2]}
        | SynExpr.SequentialOrImplicitYield(seqPoint,expr1,expr2,ifNotStmt,range) ->
            {Type = FsAstType.SynExpr_SequentialOrImplicitYield
             Range = r range
             FsAstNode = synExpr
             
             
             Properties = p [FsAstProp.SeqPoint (seqPoint)] // https://fsharp.github.io/FSharp.Compiler.Service/reference/fsharp-compiler-ast-sequencepointinfoforseq.html
             Childs = [ yield visitSynExpr expr1
                        yield visitSynExpr expr2
                        yield visitSynExpr ifNotStmt ]}
        | SynExpr.IfThenElse(ifExpr,thenExpr,elseExpr,_,isFromErrorRecovery,ifToThenRange,range) ->
            {Type = FsAstType.SynExpr_IfThenElse
             Range = r range
             Properties =
                 p [FsAstProp.IsFromErrorRecovery (isFromErrorRecovery)
                    FsAstProp.IfToThenRange (ifToThenRange)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr ifExpr
                  yield visitSynExpr thenExpr
                  if elseExpr.IsSome then yield visitSynExpr elseExpr.Value]}
        | SynExpr.Ident(id) ->
            {Type = FsAstType.SynExpr_Ident
             Range = (i id).Range
             Properties = p [FsAstProp.Ident (i id)]
             FsAstNode = synExpr
             
             
             Childs = []}
        | SynExpr.LongIdent(isOptional,longDotId,_,range) ->
            let ids = visitLongIdentWithDots longDotId
            {Type = FsAstType.SynExpr_LongIdent
             Range = r range
             Properties =
                 p [FsAstProp.IsOptional (isOptional)
                    FsAstProp.LongDotId (lid longDotId)]
             FsAstNode = synExpr
             
             
             Childs = ids}
        | SynExpr.LongIdentSet(longDotId,expr,range) ->
            {Type = FsAstType.SynExpr_LongIdentSet
             Range = r range
             Properties = p [FsAstProp.LongDotId (lid longDotId)]
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.DotGet(expr,rangeOfDot,longDotId,range) ->
            // Idents are collected as childs here to deal with unit test ``Fluent api with comments should remain on same lines``
            let ids = visitLongIdentWithDots longDotId
            {Type = FsAstType.SynExpr_DotGet
             Range = r range
             Properties =
                 p [FsAstProp.RangeOfDot (rangeOfDot)
                    FsAstProp.LongDotId (lid longDotId)]
             FsAstNode = synExpr
             
             
             Childs = [
                 yield visitSynExpr expr
                 yield! ids
             ]}
        | SynExpr.DotSet(expr,longDotId,e2,range) ->
            {Type = FsAstType.SynExpr_DotSet
             Range = r range
             Properties = p [FsAstProp.LongDotId (lid longDotId)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield visitSynExpr e2]}
        | SynExpr.Set(e1,e2,range) ->
            {Type = FsAstType.SynExpr_Set
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr e1
                  yield visitSynExpr e2]}
        | SynExpr.DotIndexedGet(objectExpr,indexExprs,dotRange,range) ->
            {Type = FsAstType.SynExpr_DotIndexedGet
             Range = r range
             Properties = p [FsAstProp.DotRange  (dotRange)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr objectExpr
                  yield! indexExprs |> List.map visitSynIndexerArg]}
        | SynExpr.DotIndexedSet(objectExpr,indexExprs,valueExpr,leftOfSetRange,dotRange,range) ->
            {Type = FsAstType.SynExpr_DotIndexedSet
             Range = r range
             Properties =
                 p [FsAstProp.LeftOfSetRange  (leftOfSetRange)
                    FsAstProp.DotRange  (dotRange)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr objectExpr
                  yield! indexExprs |> List.map visitSynIndexerArg
                  yield visitSynExpr valueExpr]}
        | SynExpr.NamedIndexedPropertySet(longDotId,e1,e2,range) ->
            {Type = FsAstType.SynExpr_NamedIndexedPropertySet
             Range = r range
             Properties = p [FsAstProp.LongDotId (lid longDotId)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr e1
                  yield visitSynExpr e2]}
        | SynExpr.DotNamedIndexedPropertySet(expr,longDotId,e1,e2,range) ->
            {Type = FsAstType.SynExpr_DotNamedIndexedPropertySet
             Range = r range
             Properties = p [FsAstProp.LongDotId (lid longDotId)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield visitSynExpr e1
                  yield visitSynExpr e2]}
        | SynExpr.TypeTest(expr,typeName,range) ->
            {Type = FsAstType.SynExpr_TypeTest
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield visitSynType typeName]}
        | SynExpr.Upcast(expr,typeName,range) ->
            {Type = FsAstType.SynExpr_Upcast
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield visitSynType typeName]}
        | SynExpr.Downcast(expr,typeName,range) ->
            {Type = FsAstType.SynExpr_Downcast
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield visitSynType typeName]}
        | SynExpr.InferredUpcast(expr,range) ->
            {Type = FsAstType.SynExpr_InferredUpcast
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.InferredDowncast(expr,range) ->
            {Type = FsAstType.SynExpr_InferredDowncast
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.Null(range) ->
            {Type = FsAstType.SynExpr_Null
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = []}
        | SynExpr.AddressOf(isByref,expr,refRange,range) ->
            {Type = FsAstType.SynExpr_AddressOf
             Range = r range
             Properties =
                 p [FsAstProp.IsByref (isByref)
                    FsAstProp.RefRange  (refRange)]
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.TraitCall(typars,sign,expr,range) ->
            {Type = FsAstType.SynExpr_AddressOf
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs =
                 [yield! typars |> List.map visitSynTypar
                  yield visitSynMemberSig sign
                  yield visitSynExpr expr]}
        | SynExpr.JoinIn(expr,inrange,expr2,range) ->
            {Type = FsAstType.SynExpr_JoinIn
             Range = r range
             Properties = p [FsAstProp.InRange  (inrange)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield visitSynExpr expr2]}
        | SynExpr.ImplicitZero(range) ->
            {Type = FsAstType.SynExpr_ImplicitZero
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = []}
        | SynExpr.YieldOrReturn(_,expr,range) ->
            {Type = FsAstType.SynExpr_YieldOrReturn
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.YieldOrReturnFrom(_,expr,range) ->
            {Type = FsAstType.SynExpr_YieldOrReturnFrom
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.LetOrUseBang(_,isUse,isFromSource,pat,rhsExpr,andBangs,body,range) ->
            {Type = FsAstType.SynExpr_LetOrUseBang
             Range = r range
             Properties =
                 p [FsAstProp.IsUse (isUse)
                    FsAstProp.IsFromSource (isFromSource)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynPat pat
                  yield visitSynExpr rhsExpr
                  yield! andBangs |> List.collect (fun (_,_,_,pat,body,_) -> visitSynPat pat :: [visitSynExpr body])
                  yield visitSynExpr body]}
        | SynExpr.MatchBang(_,expr,clauses,range) ->
            {Type = FsAstType.SynExpr_MatchBang
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr expr
                  yield! clauses |> List.map visitSynMatchClause]}
        | SynExpr.DoBang(expr,range) ->
            {Type = FsAstType.SynExpr_DoBang
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.LibraryOnlyILAssembly(_,_,_,_,range) ->
            {Type = FsAstType.SynExpr_LibraryOnlyILAssembly
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = []}
        | SynExpr.LibraryOnlyStaticOptimization(_,_,_,range) ->
            {Type = FsAstType.SynExpr_LibraryOnlyStaticOptimization
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = []}
        | SynExpr.LibraryOnlyUnionCaseFieldGet(expr,longId,_,range) ->
            {Type = FsAstType.SynExpr_LibraryOnlyUnionCaseFieldGet
             Range = r range
             Properties = p [FsAstProp.LongId (li longId)]
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.LibraryOnlyUnionCaseFieldSet(e1,longId,_,e2,range) ->
            {Type = FsAstType.SynExpr_LibraryOnlyUnionCaseFieldSet
             Range = r range
             Properties = p [FsAstProp.LongId (li longId)]
             FsAstNode = synExpr
             
             
             Childs =
                 [yield visitSynExpr e1
                  yield visitSynExpr e2]}
        | SynExpr.ArbitraryAfterError(debugStr,range) ->
            {Type = FsAstType.SynExpr_ArbitraryAfterError
             Range = r range
             Properties = p [FsAstProp.DebugStr (debugStr)]
             FsAstNode = synExpr
             
             
             Childs = []}
        | SynExpr.FromParseError(expr,range) ->
            {Type = FsAstType.SynExpr_FromParseError
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.DiscardAfterMissingQualificationAfterDot(expr,range) ->
            {Type = FsAstType.SynExpr_DiscardAfterMissingQualificationAfterDot
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}
        | SynExpr.Fixed(expr,range) ->
            {Type = FsAstType.SynExpr_Fixed
             Range = r range
             Properties = p []
             FsAstNode = synExpr
             
             
             Childs = [yield visitSynExpr expr]}

    and visitRecordField((longId,_) as rfn: RecordFieldName,expr: SynExpr option, _: BlockSeparator option) =
        {Type = FsAstType.RecordField
         Range = r longId.Range
         Properties = p [FsAstProp.LongId (lid longId)]
         FsAstNode = rfn
         
         
         Childs =
             [if expr.IsSome then yield visitSynExpr expr.Value]}
    and visitAnonRecordField(ident: Ident,expr: SynExpr) =
        {Type = FsAstType.AnonRecordField
         Range = noRange
         Properties = p [FsAstProp.Ident (i ident)]
         FsAstNode = expr
         
         
         Childs =
             [yield visitSynExpr expr]}
    and visitAnonRecordTypeField(ident: Ident,t: SynType) =
        {Type = FsAstType.AnonRecordTypeField
         Range = noRange
         Properties = p [FsAstProp.Ident (i ident)]
         FsAstNode = t
         
         
         Childs =
             [yield visitSynType t]}

    and visitSynMemberSig(ms: SynMemberSig): Node =
        match ms with
        | SynMemberSig.Member(valSig,_,range) ->
            {Type = FsAstType.SynMemberSig_Member
             Range = r range
             Properties = p []
             FsAstNode = ms
             
             
             Childs = [yield visitSynValSig valSig]}
        | SynMemberSig.Interface(typeName,range) ->
            {Type = FsAstType.SynMemberSig_Interface
             Range = r range
             Properties = p []
             FsAstNode = ms
             
             
             Childs = [yield visitSynType typeName]}
        | SynMemberSig.Inherit(typeName,range) ->
            {Type = FsAstType.SynMemberSig_Inherit
             Range = r range
             Properties = p []
             FsAstNode = ms
             
             
             Childs = [yield visitSynType typeName]}
        | SynMemberSig.ValField(f,range) ->
            {Type = FsAstType.SynMemberSig_ValField
             Range = r range
             Properties = p []
             FsAstNode = ms
             
             
             Childs = [yield visitSynField f]}
        | SynMemberSig.NestedType(typedef,range) ->
            {Type = FsAstType.SynMemberSig_NestedType
             Range = r range
             Properties = p []
             FsAstNode = ms
             
             
             Childs = [yield visitSynTypeDefnSig typedef]}

    and visitSynIndexerArg(ia: SynIndexerArg): Node =
        match ia with
        | SynIndexerArg.One(e,_fromEnd,_) ->
            {Type = FsAstType.SynIndexerArg_One
             Range = noRange
             Properties = p []
             FsAstNode = ia
             
             
             Childs = [yield visitSynExpr e]}
        | SynIndexerArg.Two(e1,_fromEnd1,e2,_fromEnd2,_,_) ->
            {Type = FsAstType.SynIndexerArg_Two
             Range = noRange
             Properties = p []
             FsAstNode = ia
             
             
             Childs =
                 [yield visitSynExpr e1
                  yield visitSynExpr e2]}

    and visitSynMatchClause(mc: SynMatchClause): Node =
        match mc with
        | SynMatchClause.Clause(pat,e1,e2,range,_) ->
            {Type = FsAstType.SynMatchClause_Clause
             Range = r range
             Properties = p []
             FsAstNode = mc
             
             
             Childs =
                 [yield visitSynPat pat
                  if e1.IsSome then yield visitSynExpr e1.Value
                  yield visitSynExpr e2]}

    and visitArgsOption(expr: SynExpr,ident: Ident option) =
        {Type = FsAstType.ArgOptions
         Range = noRange
         Properties = p [if ident.IsSome then yield FsAstProp.Ident (i ident.Value)]
         FsAstNode = expr
         
         
         Childs = [yield visitSynExpr expr]}

    and visitSynInterfaceImpl(ii: SynInterfaceImpl): Node =
        match ii with
        | InterfaceImpl(typ,bindings,range) ->
            {Type = FsAstType.InterfaceImpl
             Range = r range
             Properties = p []
             FsAstNode = ii
             
             
             Childs =
                 [yield visitSynType typ
                  yield! (bindings |> List.map visitSynBinding)]}

    and visitSynTypeDefn(td: SynTypeDefn) =
        match td with
        | TypeDefn(sci,stdr,members,range) ->
            {Type = FsAstType.TypeDefn
             Range = r range
             Properties = p []
             FsAstNode = td
             
             
             Childs =
                 [yield visitSynComponentInfo sci
                  yield visitSynTypeDefnRepr stdr
                  yield! (members |> List.map visitSynMemberDefn)]}

    and visitSynTypeDefnSig(typeDefSig: SynTypeDefnSig): Node =
        match typeDefSig with
        | TypeDefnSig(sci, synTypeDefnSigReprs,memberSig,range) ->
            {Type = FsAstType.TypeDefnSig
             Range = r range
             Properties = p []
             FsAstNode = typeDefSig
             
             
             Childs =
                 [yield visitSynComponentInfo sci
                  yield visitSynTypeDefnSigRepr synTypeDefnSigReprs
                  yield! (memberSig |> List.map visitSynMemberSig)]}

    and visitSynTypeDefnSigRepr(stdr: SynTypeDefnSigRepr): Node =
        match stdr with
        | SynTypeDefnSigRepr.ObjectModel(kind,members,range) ->
            {Type = FsAstType.SynTypeDefnSigRepr_ObjectModel
             Range = r range
             Properties = p []
             FsAstNode = stdr
             
             
             Childs =
                 [yield visitSynTypeDefnKind kind
                  yield! (members |> List.map visitSynMemberSig)]}
        | SynTypeDefnSigRepr.Simple(simpleRepr,range) ->
            {Type = FsAstType.SynTypeDefnSigRepr_ObjectModel
             Range = r range
             Properties = p []
             FsAstNode = stdr
             
             
             Childs = [yield visitSynTypeDefnSimpleRepr simpleRepr]}
        | SynTypeDefnSigRepr.Exception(exceptionRepr) ->
            {Type = FsAstType.SynTypeDefnSigRepr_Exception
             Range = noRange
             Properties = p []
             FsAstNode = stdr
             
             
             Childs = [yield visitSynExceptionDefnRepr exceptionRepr]}

    and visitSynMemberDefn(mbrDef: SynMemberDefn): Node =
        match mbrDef with
        | SynMemberDefn.Open(longIdent,range) ->
            {Type = FsAstType.SynMemberDefn_Open
             Range = r range
             Properties = p [FsAstProp.LongIdent (li longIdent)]
             FsAstNode = mbrDef
             
             
             Childs = []}
        | SynMemberDefn.Member(memberDefn,range) ->
            {Type = FsAstType.SynMemberDefn_Member
             Range = r range
             Properties = p []
             FsAstNode = mbrDef
             
             
             Childs = [yield visitSynBinding memberDefn]}
        | SynMemberDefn.ImplicitCtor(access,attrs,ctorArgs,selfIdentifier,range) ->
            {Type = FsAstType.SynMemberDefn_ImplicitCtor
             Range = r range
             Properties =
                 p [if selfIdentifier.IsSome then yield FsAstProp.SelfIdent (i selfIdentifier.Value)
                    if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = mbrDef
             
             
             Childs =
                 [yield! attrs |> List.map visitSynAttributeList
                  yield visitSynSimplePats ctorArgs]}
        | SynMemberDefn.ImplicitInherit(inheritType,inheritArgs,inheritAlias,range) ->
            {Type = FsAstType.SynMemberDefn_ImplicitInherit
             Range = r range
             Properties = p [if inheritAlias.IsSome then yield FsAstProp.InheritAlias (i inheritAlias.Value)]
             FsAstNode = mbrDef
             
             
             Childs =
                 [yield visitSynType inheritType
                  yield visitSynExpr inheritArgs]}
        | SynMemberDefn.LetBindings(bindings,isStatic,isRecursive,range) ->
            {Type = FsAstType.SynMemberDefn_LetBindings
             Range = r range
             Properties =
                 p [FsAstProp.IsStatic (isStatic)
                    FsAstProp.IsRecursive (isRecursive)]
             FsAstNode = mbrDef
             
             
             Childs = [yield! bindings |> List.map visitSynBinding]}
        | SynMemberDefn.AbstractSlot(valSig,_,range) ->
            {Type = FsAstType.SynMemberDefn_AbstractSlot
             Range = r range
             Properties = p []
             FsAstNode = mbrDef
             
             
             Childs = [yield visitSynValSig valSig]}
        | SynMemberDefn.Interface(typ,members,range) ->
            {Type = FsAstType.SynMemberDefn_Interface
             Range = r range
             Properties = p []
             FsAstNode = mbrDef
             
             
             Childs =
                 [yield visitSynType typ
                  if members.IsSome then yield! members.Value |> List.map visitSynMemberDefn]}
        | SynMemberDefn.Inherit(typ,ident,range) ->
            {Type = FsAstType.SynMemberDefn_Inherit
             Range = r range
             Properties = p [if ident.IsSome then yield FsAstProp.Ident (i ident.Value)]
             FsAstNode = mbrDef
             
             
             Childs = [yield visitSynType typ]}
        | SynMemberDefn.ValField(fld,range) ->
            {Type = FsAstType.SynMemberDefn_ValField
             Range = r range
             Properties = p []
             FsAstNode = mbrDef
             
             
             Childs = [yield visitSynField fld]}
        | SynMemberDefn.NestedType(typeDefn,access,range) ->
            {Type = FsAstType.SynMemberDefn_NestedType
             Range = r range
             Properties = p [if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = mbrDef
             
             
             Childs = [yield visitSynTypeDefn typeDefn]}
        | SynMemberDefn.AutoProperty(attrs,isStatic,ident,typeOpt,propKind,_,_,access,synExpr,getSetRange,range) ->
            {Type = FsAstType.SynMemberDefn_AutoProperty
             Range = r range
             Properties =
                 p [yield FsAstProp.IsStatic (isStatic)
                    yield FsAstProp.Ident (i ident)
                    yield FsAstProp.PropKind (propKind)
                    if access.IsSome then yield FsAstProp.Access  access.Value
                    if getSetRange.IsSome then yield FsAstProp.GetSetRange ((getSetRange.Value))]
             FsAstNode = mbrDef
             
             
             Childs =
                 [yield! attrs |> List.map visitSynAttributeList
                  if typeOpt.IsSome then yield visitSynType typeOpt.Value
                  yield visitSynExpr synExpr]}

    and visitSynSimplePat(sp: SynSimplePat): Node =
        match sp with
        | SynSimplePat.Id(ident,_,isCompilerGenerated,isThisVar,isOptArg,range) ->
            {Type = FsAstType.SynSimplePat_Id
             Range = r range
             Properties =
                 p [FsAstProp.IsCompilerGenerated (isCompilerGenerated)
                    FsAstProp.IsThisVar (isThisVar)
                    FsAstProp.IsOptArg (isOptArg)
                    FsAstProp.Ident (i ident)]
             FsAstNode = sp
             
             
             Childs = []}
        | SynSimplePat.Typed(simplePat,typ,range) ->
            {Type = FsAstType.SynSimplePat_Typed
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs =
                 [yield visitSynSimplePat simplePat
                  yield visitSynType typ]}
        | SynSimplePat.Attrib(simplePat,attrs,range) ->
            {Type = FsAstType.SynSimplePat_Attrib
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs =
                 [yield visitSynSimplePat simplePat
                  yield! attrs |> List.map visitSynAttributeList]}

    and visitSynSimplePats(sp: SynSimplePats): Node =
        match sp with
        | SynSimplePats.SimplePats(pats,range) ->
            {Type = FsAstType.SynSimplePats_SimplePats
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs = [yield! pats |> List.map visitSynSimplePat]}
        | SynSimplePats.Typed(pats,typ,range) ->
            {Type = FsAstType.SynSimplePats_Typed
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs =
                 [yield visitSynSimplePats pats
                  yield visitSynType typ]}

    and visitSynBinding(binding: SynBinding): Node =
        match binding with
        | Binding(access,kind,mustInline,isMutable,attrs,_,valData,headPat,returnInfo,expr,range,_) ->
            {Type = FsAstType.Binding
             Range = r range
             Properties =
                 p [yield FsAstProp.MustInline (mustInline)
                    yield FsAstProp.IsMutable (isMutable)
                    yield FsAstProp.Kind (kind)
                    if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = binding
             
             
             Childs =
                 [yield! attrs |> List.map visitSynAttributeList
                  yield visitSynValData valData
                  yield visitSynPat headPat
                  if returnInfo.IsSome then yield visitSynBindingReturnInfo returnInfo.Value
                  yield visitSynExpr expr]}

    and visitSynValData(svd: SynValData): Node =
        match svd with
        | SynValData(_,svi,ident) ->
            {Type = FsAstType.SynValData
             Range = noRange
             Properties = p [ if ident.IsSome then yield FsAstProp.Ident ((ident.Value |> i))]
             FsAstNode = svd
             
             
             Childs = [yield visitSynValInfo svi]}

    and visitSynValSig(svs: SynValSig): Node =
        match svs with
        | ValSpfn(attrs,ident,explicitValDecls,synType,arity,isInline,isMutable,_,access,expr,range) ->
            {Type = FsAstType.ValSpfn
             Range = r range
             Properties =
                 p [yield FsAstProp.Ident (i ident)
                    yield FsAstProp.IsMutable (isMutable)
                    yield FsAstProp.IsInline (isInline)
                    if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = svs
             
             
             Childs =
                 [yield! attrs |> List.map visitSynAttributeList
                  yield visitSynValTyparDecls explicitValDecls
                  yield visitSynType synType
                  yield visitSynValInfo arity
                  if expr.IsSome then yield visitSynExpr expr.Value]}

    and visitSynValTyparDecls(valTypeDecl: SynValTyparDecls): Node =
        match valTypeDecl with
        | SynValTyparDecls(typardecls,_,_) ->
            {Type = FsAstType.SynValTyparDecls
             Range = noRange
             Properties = p []
             FsAstNode = valTypeDecl
             
             
             Childs = [yield! typardecls |> List.map visitSynTyparDecl]}

    and visitSynTyparDecl(std: SynTyparDecl): Node =
        match std with
        | TyparDecl(attrs,typar) ->
            {Type = FsAstType.TyparDecl
             Range = noRange
             Properties = p []
             FsAstNode = std
             
             
             Childs =
                 [yield! attrs |> List.map visitSynAttributeList
                  yield visitSynTypar typar]}

    and visitSynTypar(typar: SynTypar): Node =
        match typar with
        | Typar(ident,staticReq,isComGen) ->
            {Type = FsAstType.ValSpfn
             Range = noRange
             Properties =
                 p [FsAstProp.Ident (i ident)
                    FsAstProp.IsComGen (isComGen)
                    FsAstProp.StaticReq (staticReq)]
             FsAstNode = typar
             
             
             Childs = []}

    and visitSynBindingReturnInfo(returnInfo: SynBindingReturnInfo): Node =
        match returnInfo with
        | SynBindingReturnInfo(typeName,range,attrs) ->
            {Type = FsAstType.ComponentInfo
             Range = r range
             Properties = p []
             FsAstNode = returnInfo
             
             
             Childs =
                 [yield visitSynType typeName
                  yield! (attrs |> List.map visitSynAttributeList)]}

    and visitSynPat(sp: SynPat): Node =
        match sp with
        | SynPat.Const(sc,range) ->
            {Type = FsAstType.SynPat_Const
             Range = r range
             Properties = p [FsAstProp.Const (sc)]
             FsAstNode = sp
             
             
             Childs = []}
        | SynPat.Wild(range) ->
            {Type = FsAstType.SynPat_Wild
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs = []}
        | SynPat.Named(synPat,ident,isSelfIdentifier,access,range) ->
            {Type = FsAstType.SynPat_Named
             Range = r range
             Properties =
                 p [yield FsAstProp.Ident (i ident)
                    yield FsAstProp.IsSelfIdentifier (isSelfIdentifier)
                    if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = sp
             
             
             Childs = [yield visitSynPat synPat]}
        | SynPat.Typed(synPat,synType,range) ->
            {Type = FsAstType.SynPat_Typed
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs =
                 [yield visitSynPat synPat
                  yield visitSynType synType]}
        | SynPat.Attrib(synPat,attrs,range) ->
            {Type = FsAstType.SynPat_Attrib
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs =
                 [yield visitSynPat synPat
                  yield! attrs |> List.map visitSynAttributeList]}
        | SynPat.Or(synPat,synPat2,range) ->
            {Type = FsAstType.SynPat_Or
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs =
                 [yield visitSynPat synPat
                  yield visitSynPat synPat2]}
        | SynPat.Ands(pats,range) ->
            {Type = FsAstType.SynPat_Ands
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs = [yield! pats |> List.map visitSynPat]}
        | SynPat.LongIdent(longDotId,ident,svtd,ctorArgs,access,range) ->
            {Type = FsAstType.SynPat_LongIdent
             Range = r range
             Properties =
                 p [if ident.IsSome then yield FsAstProp.Ident ((ident.Value |> i))
                    yield FsAstProp.LongDotId (lid longDotId)
                    if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = sp
             
             
             Childs =
                 [if svtd.IsSome then yield visitSynValTyparDecls svtd.Value
                  yield visitSynConstructorArgs ctorArgs]}
        | SynPat.Tuple(isStruct,pats,range) ->
            {Type = FsAstType.SynPat_Tuple
             Range = r range
             Properties = p [FsAstProp.IsStruct (isStruct)]
             FsAstNode = sp
             
             
             Childs = [yield! pats |> List.map visitSynPat]}
        | SynPat.Paren(pat,range) ->
            {Type = FsAstType.SynPat_Paren
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs = [visitSynPat pat]}
        | SynPat.ArrayOrList(_,pats,range) ->
            {Type = FsAstType.SynPat_ArrayOrList
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs = [yield! pats |> List.map visitSynPat]}
        | SynPat.Record(pats,range) ->
            {Type = FsAstType.SynPat_Record
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs = [yield! pats |> List.map(snd >> visitSynPat)]}
        | SynPat.Null(range) ->
            {Type = FsAstType.SynPat_Null
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs = []}
        | SynPat.OptionalVal(ident,range) ->
            {Type = FsAstType.SynPat_OptionalVal
             Range = r range
             Properties = p [FsAstProp.Ident (i ident)]
             FsAstNode = sp
             
             
             Childs = []}
        | SynPat.IsInst(typ,range) ->
            {Type = FsAstType.SynPat_IsInst
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs = [visitSynType typ]}
        | SynPat.QuoteExpr(expr,range) ->
            {Type = FsAstType.SynPat_QuoteExpr
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs = [visitSynExpr expr]}
        | SynPat.DeprecatedCharRange(c,c2,range) ->
            {Type = FsAstType.SynPat_DeprecatedCharRange
             Range = r range
             Properties =
                 p [FsAstProp.C (c)
                    FsAstProp.C2 (c2)]
             FsAstNode = sp
             
             
             Childs = []}
        | SynPat.InstanceMember(ident,ident2,ident3,access,range) ->
            {Type = FsAstType.SynPat_InstanceMember
             Range = r range
             Properties =
                 p [yield FsAstProp.Ident (i ident)
                    yield FsAstProp.Ident2 (i ident2)
                    if ident3.IsSome then yield FsAstProp.Ident3 ((ident3.Value |> i))
                    if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = sp
             
             
             Childs = []}
        | SynPat.FromParseError(pat,range) ->
            {Type = FsAstType.SynPat_FromParseError
             Range = r range
             Properties = p []
             FsAstNode = sp
             
             
             Childs = [visitSynPat pat]}

    and visitSynConstructorArgs(ctorArgs: SynArgPats): Node =
        match ctorArgs with
        | Pats(pats) ->
            {Type = FsAstType.Pats
             Range = noRange
             Properties = p []
             FsAstNode = ctorArgs
             
             
             Childs = [yield! pats |> List.map visitSynPat]}
        | NamePatPairs(pats,range) ->
            {Type = FsAstType.NamePatPairs
             Range = r range
             Properties = p []
             FsAstNode = ctorArgs
             
             
             Childs = [yield! pats |> List.map(snd >> visitSynPat)]}

    and visitSynComponentInfo(sci: SynComponentInfo): Node =
        match sci with
        | ComponentInfo(attribs,typeParams,_,longId,_,preferPostfix,access,range) ->
            {Type = FsAstType.ComponentInfo
             Range = r range
             Properties =
                 p [yield FsAstProp.LongIdent (li longId)
                    yield FsAstProp.PreferPostfix (preferPostfix)
                    if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = sci
             
             
             Childs =
                 [yield! (attribs |> List.map visitSynAttributeList)
                  yield! (typeParams |> List.map(visitSynTyparDecl))]}

    and visitSynTypeDefnRepr(stdr: SynTypeDefnRepr): Node =
        match stdr with
        | SynTypeDefnRepr.ObjectModel(kind,members,range) ->
            {Type = FsAstType.SynTypeDefnRepr_ObjectModel
             Range = r range
             Properties = p []
             FsAstNode = stdr
             
             
             Childs =
                 [yield visitSynTypeDefnKind kind
                  yield! (members |> List.map visitSynMemberDefn)]}
        | SynTypeDefnRepr.Simple(simpleRepr,range) ->
            {Type = FsAstType.SynTypeDefnRepr_ObjectModel
             Range = r range
             Properties = p []
             FsAstNode = stdr
             
             
             Childs = [yield visitSynTypeDefnSimpleRepr simpleRepr]}
        | SynTypeDefnRepr.Exception(exceptionRepr) ->
            {Type = FsAstType.SynTypeDefnRepr_Exception
             Range = noRange
             Properties = p []
             FsAstNode = stdr
             
             
             Childs = [yield visitSynExceptionDefnRepr exceptionRepr]}

    and visitSynTypeDefnKind(kind: SynTypeDefnKind) =
        match kind with
        | TyconUnspecified ->
            {Type = FsAstType.SynTypeDefnKind_TyconUnspecified
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs = []}
        | TyconClass ->
            {Type = FsAstType.SynTypeDefnKind_TyconClass
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs = []}
        | TyconInterface ->
            {Type = FsAstType.SynTypeDefnKind_TyconInterface
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs = []}
        | TyconStruct ->
            {Type = FsAstType.SynTypeDefnKind_TyconStruct
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs = []}
        | TyconRecord ->
            {Type = FsAstType.SynTypeDefnKind_TyconRecord
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs = []}
        | TyconUnion ->
            {Type = FsAstType.SynTypeDefnKind_TyconUnion
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs = []}
        | TyconAbbrev ->
            {Type = FsAstType.SynTypeDefnKind_TyconAbbrev
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs = []}
        | TyconHiddenRepr ->
            {Type = FsAstType.SynTypeDefnKind_TyconHiddenRepr
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs = []}
        | TyconAugmentation ->
            {Type = FsAstType.SynTypeDefnKind_TyconAugmentation
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs = []}
        | TyconILAssemblyCode ->
            {Type = FsAstType.SynTypeDefnKind_TyconILAssemblyCode
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs = []}
        | TyconDelegate(typ,valinfo) ->
            {Type = FsAstType.SynTypeDefnKind_TyconDelegate
             Range = noRange
             Properties = p []
             FsAstNode = kind
             
             
             Childs =
                 [yield visitSynType typ
                  yield visitSynValInfo valinfo]}

    and visitSynTypeDefnSimpleRepr(arg: SynTypeDefnSimpleRepr) =
        match arg with
        | SynTypeDefnSimpleRepr.None(range) ->
            {Type = FsAstType.SynTypeDefnSimpleRepr_None
             Range = r range
             Properties = p []
             FsAstNode = arg
             
             
             Childs = []}
        | SynTypeDefnSimpleRepr.Union(access,unionCases,range) ->
            {Type = FsAstType.SynTypeDefnSimpleRepr_Union
             Range = r range
             Properties = p [if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = arg
             
             
             Childs = [yield! unionCases |> List.map visitSynUnionCase]}
        | SynTypeDefnSimpleRepr.Enum(enumCases,range) ->
            {Type = FsAstType.SynTypeDefnSimpleRepr_Enum
             Range = r range
             Properties = p []
             FsAstNode = arg
             
             
             Childs = [yield! enumCases |> List.map visitSynEnumCase]}
        | SynTypeDefnSimpleRepr.Record(access,recordFields,range) ->
            {Type = FsAstType.SynTypeDefnSimpleRepr_Record
             Range = r range
             Properties = p [if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = arg
             
             
             Childs = [yield! recordFields |> List.map visitSynField]}
        | SynTypeDefnSimpleRepr.General(_,_,_,_,_,_,_,range) ->
            {Type = FsAstType.SynTypeDefnSimpleRepr_General
             Range = r range
             Properties = p []
             FsAstNode = arg
             
             
             Childs = []}
        | SynTypeDefnSimpleRepr.LibraryOnlyILAssembly(_,range) ->
            {Type = FsAstType.SynTypeDefnSimpleRepr_LibraryOnlyILAssembly
             Range = r range
             Properties = p []
             FsAstNode = arg
             
             
             Childs = []}
        | SynTypeDefnSimpleRepr.TypeAbbrev(_,typ,range) ->
            {Type = FsAstType.SynTypeDefnSimpleRepr_TypeAbbrev
             Range = r range
             Properties = p []
             FsAstNode = arg
             
             
             Childs = [visitSynType typ]}
        | SynTypeDefnSimpleRepr.Exception(edr) ->
            {Type = FsAstType.SynTypeDefnSimpleRepr_Exception
             Range = noRange
             Properties = p []
             FsAstNode = arg
             
             
             Childs = [visitSynExceptionDefnRepr edr]}

    and visitSynExceptionDefn(exceptionDef: SynExceptionDefn): Node =
        match exceptionDef with
        | SynExceptionDefn(sedr,members,range) ->
            {Type = FsAstType.SynExceptionDefn
             Range = r range
             Properties = p []
             FsAstNode = exceptionDef
             
             
             Childs =
                 [yield visitSynExceptionDefnRepr sedr
                  yield! (members |> List.map visitSynMemberDefn)]}

    and visitSynExceptionDefnRepr(sedr: SynExceptionDefnRepr): Node =
        match sedr with
        | SynExceptionDefnRepr(attrs,unionCase,longId,_,access,range) ->
            {Type = FsAstType.SynExceptionDefnRepr
             Range = r range
             Properties =
                 p [if longId.IsSome then yield FsAstProp.LongIdent ((longId.Value |> li))
                    if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = sedr
             
             
             Childs =
                 [yield! attrs |> List.map visitSynAttributeList
                  yield visitSynUnionCase unionCase]}

    and visitSynAttribute(attr: SynAttribute): Node =
        {Type = FsAstType.SynAttribute
         Range = r attr.Range
         Properties =
             p [if attr.Target.IsSome then yield FsAstProp.Target (i attr.Target.Value)
                yield FsAstProp.TypeName (lid attr.TypeName)
                yield FsAstProp.AppliesToGetterAndSetter (attr.AppliesToGetterAndSetter)
                yield FsAstProp.TypeName (lid attr.TypeName)]
         FsAstNode = attr
         
         
         Childs = [visitSynExpr attr.ArgExpr]}

    and visitSynAttributeList(attrs: SynAttributeList): Node =
        {Type = FsAstType.SynAttributeList
         Range = r attrs.Range
         Properties = p []
         FsAstNode = attrs
         
         
         Childs = attrs.Attributes |> List.map visitSynAttribute
        }

    and visitSynUnionCase(uc: SynUnionCase): Node =
        match uc with
        | UnionCase(attrs,ident,uct,_,access,range) ->
            {Type = FsAstType.UnionCase
             Range = r range
             Properties =
                 p [yield FsAstProp.Ident (i ident)
                    if access.IsSome then yield FsAstProp.Access  access.Value]
             FsAstNode = uc
             
             
             Childs =
                 [yield visitSynUnionCaseType uct
                  yield! attrs |> List.map visitSynAttributeList]}

    and visitSynUnionCaseType(uct: SynUnionCaseType) =
        match uct with
        | UnionCaseFields(cases) ->
            {Type = FsAstType.UnionCaseFields
             Range = noRange
             Properties = p []
             FsAstNode = uct
             
             
             Childs = [yield! cases |> List.map visitSynField]}
        | UnionCaseFullType(stype,valInfo) ->
            {Type = FsAstType.UnionCaseFullType
             Range = noRange
             Properties = p []
             FsAstNode = uct
             
             
             Childs =
                 [yield visitSynType stype
                  yield visitSynValInfo valInfo]}

    and visitSynEnumCase(sec: SynEnumCase): Node =
        match sec with
        | EnumCase(attrs,ident,_,_,range) ->
            {Type = FsAstType.EnumCase
             Range = r range
             Properties = p []
             FsAstNode = sec
             
             
             Childs = [yield! attrs |> List.map visitSynAttributeList; yield visitIdent ident]}

    and visitSynField(sfield: SynField): Node =
        match sfield with
        | Field(attrs,isStatic,ident,typ,_,_,access,range) ->
            {Type = FsAstType.Field
             Range = r range
             Properties =
                 p [if ident.IsSome then yield FsAstProp.Ident ((ident.Value |> i))
                    yield FsAstProp.IsStatic (isStatic)
                    if access.IsSome then yield FsAstProp.Access (access.Value)]
             FsAstNode = sfield
             
             
             Childs =
                 [yield! attrs |> List.map visitSynAttributeList
                  yield visitSynType typ]}

    and visitSynType(st: SynType) =
        match st with
        | SynType.LongIdent(li) ->
            {Type = FsAstType.SynType_LongIdent
             Range = noRange
             Properties = p [FsAstProp.LongIdent (lid li)]
             FsAstNode = st
             
             
             Childs = []}
        | SynType.App(typeName,lESSrange,typeArgs,commaRanges,gREATERrange,isPostfix,range) ->
            {Type = FsAstType.SynType_App
             Range = r range
             Properties =
                 p [if lESSrange.IsSome then yield FsAstProp.LESSrange (lESSrange.Value)
                    yield FsAstProp.CommaRanges (commaRanges)
                    if gREATERrange.IsSome then yield FsAstProp.GREATERrange (gREATERrange.Value)
                    yield FsAstProp.IsPostfix (isPostfix)]
             FsAstNode = st
             
             
             Childs =
                 [yield! typeArgs |> List.map visitSynType
                  yield visitSynType typeName]}
        | SynType.LongIdentApp(typeName,longDotId,lESSRange,typeArgs,commaRanges,gREATERrange,range) ->
            {Type = FsAstType.SynType_LongIdentApp
             Range = r range
             Properties =
                 p [yield FsAstProp.LongDotId (lid longDotId)
                    if lESSRange.IsSome then yield FsAstProp.LESSRange (lESSRange.Value)
                    yield FsAstProp.CommaRanges (commaRanges)
                    if gREATERrange.IsSome then yield FsAstProp.GREATERrange (gREATERrange.Value)]
             FsAstNode = st
             
             
             Childs =
                 [yield! typeArgs |> List.map visitSynType
                  yield visitSynType typeName]}
        | SynType.Tuple(isStruct,typeNames,range) ->
            {Type = FsAstType.SynType_Tuple
             Range = r range
             Properties = p [FsAstProp.IsStruct (isStruct)]
             FsAstNode = st
             
             
             Childs = [yield! typeNames |> List.map(snd >> visitSynType)]}
        | SynType.Array(_,elementType,range) ->
            {Type = FsAstType.SynType_Array
             Range = r range
             Properties = p []
             FsAstNode = st
             
             
             Childs = [yield visitSynType elementType]}
        | SynType.Fun(argType,returnType,range) ->
            {Type = FsAstType.SynType_Fun
             Range = r range
             Properties = p []
             FsAstNode = st
             
             
             Childs =
                 [yield visitSynType argType
                  yield visitSynType returnType]}
        | SynType.Var(genericName,range) ->
            {Type = FsAstType.SynType_Var
             Range = r range
             Properties = p []
             FsAstNode = st
             
             
             Childs = [yield visitSynTypar genericName]}
        | SynType.Anon(range) ->
            {Type = FsAstType.SynType_Anon
             Range = r range
             Properties = p []
             FsAstNode = st
             
             
             Childs = []}
        | SynType.WithGlobalConstraints(typeName,_,range) ->
            {Type = FsAstType.SynType_WithGlobalConstraints
             Range = r range
             Properties = p []
             FsAstNode = st
             
             
             Childs = [yield visitSynType typeName]}
        | SynType.HashConstraint(synType,range) ->
            {Type = FsAstType.SynType_HashConstraint
             Range = r range
             Properties = p []
             FsAstNode = st
             
             
             Childs = [yield visitSynType synType]}
        | SynType.MeasureDivide(dividendType,divisorType,range) ->
            {Type = FsAstType.SynType_MeasureDivide
             Range = r range
             Properties = p []
             FsAstNode = st
             
             
             Childs =
                 [yield visitSynType dividendType
                  yield visitSynType divisorType]}
        | SynType.MeasurePower(measureType,_,range) ->
            {Type = FsAstType.SynType_MeasurePower
             Range = r range
             Properties = p []
             FsAstNode = st
             
             
             Childs = [yield visitSynType measureType]}
        | SynType.StaticConstant(constant,range) ->
            {Type = FsAstType.SynType_StaticConstant
             Range = r range
             Properties = p [FsAstProp.Constant (constant)]
             FsAstNode = st
             
             
             Childs = []}
        | SynType.StaticConstantExpr(expr,range) ->
            {Type = FsAstType.SynType_StaticConstantExpr
             Range = r range
             Properties = p []
             FsAstNode = st
             
             
             Childs = [yield visitSynExpr expr]}
        | SynType.StaticConstantNamed(expr,typ,range) ->
            {Type = FsAstType.SynType_StaticConstantNamed
             Range = r range
             Properties = p []
             FsAstNode = st
             
             
             Childs =
                 [yield visitSynType expr
                  yield visitSynType typ]}
        | SynType.AnonRecd(isStruct,typeNames,range) ->
            {Type = FsAstType.SynType_AnonRecd
             Range = r range
             Properties = p [FsAstProp.IsStruct (isStruct)]
             FsAstNode = st
             
             
             Childs = List.map visitAnonRecordTypeField typeNames}

    and visitSynValInfo(svi: SynValInfo) =
        match svi with
        | SynValInfo(args,arg) ->
            {Type = FsAstType.SynValInfo
             Range = noRange
             Properties = p []
             FsAstNode = svi
             
             
             Childs =
                 [yield! args |> List.collect(List.map visitSynArgInfo)
                  yield visitSynArgInfo arg]}

    and visitSynArgInfo(sai: SynArgInfo) =
        match sai with
        | SynArgInfo(attrs,optional,ident) ->
            {Type = FsAstType.SynArgInfo
             Range = noRange
             Properties =
                 p [if ident.IsSome then yield FsAstProp.Ident (i ident.Value)
                    yield FsAstProp.Optional (optional)]
             FsAstNode = sai
             
             
             Childs = [yield! attrs |> List.map visitSynAttributeList]}

    and visitParsedHashDirective(hash: ParsedHashDirective): Node =
        match hash with
        | ParsedHashDirective(ident,longIdent,range) ->
            {Type = FsAstType.ParsedHashDirective
             Range = r range
             Properties =
                 p [FsAstProp.Ident { Ident = ident; Range = None }
                    FsAstProp.LongIdent (longIdent |> List.map (fun x -> { Ident = x; Range = None }))]
             FsAstNode = hash
             
             
             Childs = []}

    and visitSynModuleOrNamespaceSig(modOrNs: SynModuleOrNamespaceSig): Node =
        match modOrNs with
        | SynModuleOrNamespaceSig(longIdent,isRecursive,isModule,decls,_,attrs,access,range) ->
            {Type =
                match isModule with
                | SynModuleOrNamespaceKind.AnonModule -> FsAstType.SynModuleOrNamespaceSig_AnonModule
                | SynModuleOrNamespaceKind.DeclaredNamespace -> FsAstType.SynModuleOrNamespaceSig_DeclaredNamespace
                | SynModuleOrNamespaceKind.GlobalNamespace -> FsAstType.SynModuleOrNamespaceSig_GlobalNamespace
                | SynModuleOrNamespaceKind.NamedModule -> FsAstType.SynModuleOrNamespaceSig_NamedModule
             Range = r range
             Properties =
                 p [yield FsAstProp.IsRecursive (isRecursive)
                    yield FsAstProp.IsModule (isModule)
                    yield FsAstProp.LongIdent (li longIdent)
                    if access.IsSome then yield FsAstProp.Access (access.Value)]
             FsAstNode = modOrNs
             
             
             Childs =
                 [yield! (if isModule = SynModuleOrNamespaceKind.DeclaredNamespace then visitLongIdent longIdent else [])
                  yield! attrs |> List.map visitSynAttributeList
                  yield! (decls |> List.map visitSynModuleSigDecl)]}

    and visitSynModuleSigDecl(ast: SynModuleSigDecl) : Node =
        match ast with
        | SynModuleSigDecl.ModuleAbbrev(ident,longIdent,range) ->
            {Type = FsAstType.SynModuleSigDecl_ModuleAbbrev
             Range = r range
             Properties =
                 p [FsAstProp.Ident (i ident)
                    FsAstProp.LongIdent (li longIdent)]
             FsAstNode = ast
             
             
             Childs = []}
        | SynModuleSigDecl.NestedModule(sci,isRecursive,decls,range) ->
            {Type = FsAstType.SynModuleSigDecl_NestedModule
             Range = r range
             Properties = p [FsAstProp.IsRecursive (isRecursive)]
             FsAstNode = ast
             
             
             Childs =
                 [yield visitSynComponentInfo sci
                  yield! (decls |> List.map visitSynModuleSigDecl)]}
        | SynModuleSigDecl.Val(SynValSig.ValSpfn _ as node, _) ->
            visitSynValSig node
        | SynModuleSigDecl.Types(typeDefs,range) ->
            {Type = FsAstType.SynModuleSigDecl_Types
             Range = r range
             Properties = p []
             FsAstNode = ast
             
             
             Childs = typeDefs |> List.map visitSynTypeDefnSig}
        | SynModuleSigDecl.Open(longId,range) ->
            {Type = FsAstType.SynModuleSigDecl_Open
             Range = r range
             Properties = p [FsAstProp.LongIdent (li longId)]
             FsAstNode = ast
             
             
             Childs = []}
        | SynModuleSigDecl.HashDirective(hash,range) ->
            {Type = FsAstType.SynModuleSigDecl_HashDirective
             Range = r range
             Properties = p []
             FsAstNode = ast
             
             
             Childs = [visitParsedHashDirective hash]}
        | SynModuleSigDecl.NamespaceFragment(moduleOrNamespace) ->
            {Type = FsAstType.SynModuleDecl_NamespaceFragment
             Range = noRange
             Properties = p []
             FsAstNode = ast
             
             
             Childs = [visitSynModuleOrNamespaceSig moduleOrNamespace]}
        | SynModuleSigDecl.Exception(synExceptionSig, range) ->
            {Type = FsAstType.SynModuleSigDecl_Exception
             Range = r range
             Properties = p []
             FsAstNode = ast
             
             
             Childs = [visitSynExceptionSig synExceptionSig]}

    and visitSynExceptionSig(exceptionDef: SynExceptionSig): Node =
        match exceptionDef with
        | SynExceptionSig(sedr,members,range) ->
            {Type = FsAstType.SynExceptionSig
             Range = r range
             Properties = p []
             FsAstNode = exceptionDef
             
             
             Childs =
                 [yield visitSynExceptionDefnRepr sedr
                  yield! (members |> List.map visitSynMemberSig)]}

    and visitLongIdentWithDots (lid: LongIdentWithDots): Node list =
        match lid with
        | LongIdentWithDots(ids,_) ->
            List.map visitIdent ids

    and visitLongIdent (li: LongIdent) : Node list =
        List.map visitIdent li

    and visitIdent (ident: Ident) : Node =
        { Type = FsAstType.Ident
          Range = r ident.idRange
          Properties = []
          FsAstNode = ident
          
          
          Childs = [] }


let astToNode (hds: ParsedHashDirective list) (mdls: SynModuleOrNamespace list): Node =
    let children =
        [ yield! List.map Ast.visit mdls
          yield! List.map Ast.visitParsedHashDirective hds ]
    {Type = FsAstType.File
     Range = None
     Properties = []
     FsAstNode = mdls
     
     
     Childs = children}

let sigAstToNode (ast: SynModuleOrNamespaceSig list) : Node =
    let children = List.map Ast.visitSynModuleOrNamespaceSig ast
    {Type = FsAstType.SigFile
     Range = None
     Properties = []
     FsAstNode = ast
     
     
     Childs = children}
