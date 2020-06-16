module internal Fantomas.Trivia

open Fantomas
open Fantomas.AstTransformer
open Fantomas.TriviaTypes
open FSharp.Compiler.Range
open FSharp.Compiler.SyntaxTree

let private isMainNodeButNotAnonModule (node: TriviaNodeAssigner) =
    match node.Type with
    | MainNode(t) when (t <> "SynModuleOrNamespace.AnonModule") -> true
    | _ -> false
    
let isMainNode (node: TriviaNode) =
    match node.Type with
    | MainNode(_) -> true
    | _ -> false
    
let isToken (node: TriviaNode) =
    match node.Type with
    | Token(_) -> true
    | _ -> false

let rec private flattenNodeToList (node: Node) =
    [ yield node
      yield! (node.Childs |> List.map flattenNodeToList |> List.collect id) ]
    
let filterNodes nodes =
    let filterOutNodeTypes =
        set [
            "SynExpr.Sequential" // some Sequential nodes are not visited in CodePrinter
            "SynModuleOrNamespace.DeclaredNamespace" // LongIdent inside Namespace is being processed as children.
            "SynModuleOrNamespaceSig.DeclaredNamespace"
            "SynExpr.LetOrUse"
            "SynTypeDefnRepr.ObjectModel"
            "TypeDefnSig"
            "SynTypeDefnSigRepr.ObjectModel"
        ]
    nodes |> List.filter (fun (n: Node) -> not (Set.contains n.Type filterOutNodeTypes))

let private findFirstNodeOnLine (nodes: TriviaNode list) lineNumber : TriviaNode option =
    nodes
    |> List.filter (fun { Range =r  } -> r.StartLine = lineNumber)
    |> List.tryHead

let inline private mainNodeIs name (t:TriviaNodeAssigner) =
    match t.Type with
    | MainNode(mn) -> mn = name
    | _ -> false

let private nodesContainsBothAnonModuleAndOpen (nodes: TriviaNodeAssigner list) =
    List.exists (mainNodeIs "SynModuleOrNamespace.AnonModule") nodes &&
    List.exists (mainNodeIs "SynModuleDecl.Open") nodes

// the member keyword is not part of an AST node range
// so it is not an ideal candidate node to have trivia content
let inline private isNotMemberKeyword (node: TriviaNodeAssigner) =
    match node.Type with
    | Token({ TokenInfo = ti }) when (ti.TokenName = "MEMBER") -> false
    | _ -> true

let private findFirstNodeAfterLine (nodes: TriviaNodeAssigner list) lineNumber : TriviaNodeAssigner option =
    nodes
    |> List.filter (fun n -> n.Range.StartLine > lineNumber && isNotMemberKeyword n)
    |> fun filteredNodes ->
        match filteredNodes with
        | moduleAndOpens when (nodesContainsBothAnonModuleAndOpen moduleAndOpens) ->
            moduleAndOpens
            |> List.filter (fun t -> t.Type = MainNode("SynModuleDecl.Open"))
            |> List.tryHead
        | _ ->
            filteredNodes
            |> List.tryHead

let private findLastNodeOnLine (nodes: TriviaNodeAssigner list) lineNumber : TriviaNodeAssigner option =
    nodes
    |> List.filter (fun tn -> tn.Range.EndLine = lineNumber)
    |> List.sortByDescending (fun tn -> tn.Range.EndColumn, tn.Range.StartColumn)
    |> List.tryHead

let private findLastNode (nodes: TriviaNodeAssigner list) : TriviaNodeAssigner option =
    match nodes with
    | [] -> None
    | nodes ->
        nodes
        |> List.filter isMainNodeButNotAnonModule
        |> List.maxBy (fun tn -> tn.Range.EndLine)
        |> Some

let private findNodeOnLineAndColumn (nodes: TriviaNodeAssigner list) line column =
    nodes
    |> List.tryFindBack (fun tn -> tn.Range.StartLine = line && tn.Range.StartColumn = column)

let private findMemberDefnMemberNodeOnLine (nodes: TriviaNodeAssigner list) line =
    nodes
    |> List.tryFind (fun tn ->
        match tn.Type, tn.Range.StartLine = line with
        | MainNode("SynMemberDefn.Member"), true
        | MainNode("SynMemberSig.Member"), true
        | Token { TokenInfo = { TokenName = "MEMBER" } }, true -> true
        | _ -> false)

let private findNodeBeforeLineAndColumn (nodes: TriviaNodeAssigner list) line column =
    nodes
    |> List.tryFindBack (fun tn ->
        let range = tn.Range
        range.StartLine <= line && range.StartColumn <= column)

let private findNodeBeforeLineFromStart (nodes: TriviaNodeAssigner list) line =
    nodes
    |> List.filter (fun tn -> tn.Range.EndLine < line)
    |> List.sortByDescending (fun tn -> tn.Range.EndLine, -tn.Range.StartColumn)
    |> List.tryFind (fun tn -> tn.Range.StartLine < line)
    
let private findNodeBeforeLineFromEnd (nodes: TriviaNode list) line =
    nodes
    |> List.tryFindBack (fun { Range = range } -> range.StartLine < line)

let private findNodeAfterLineAndColumn (nodes: TriviaNodeAssigner list) line column =
    nodes
    |> List.tryFind (fun tn ->
        let range = tn.Range
        (range.StartLine > line) || (range.StartLine = line && range.StartColumn > column)
    )

let private findConstNodeOnLineAndColumn (nodes: TriviaNodeAssigner list) line column =
    nodes
    |> List.tryFind (fun tn ->
        match tn.Type, line = tn.Range.StartLine, column = tn.Range.StartColumn with
        | MainNode("SynExpr.Const"), true, true -> true
        | _ -> false
    )

let private findConstNodeAfter (nodes: TriviaNodeAssigner list) (range: range) =
    nodes
    |> List.tryFind (fun tn ->
        match tn.Type, range.StartLine = tn.Range.StartLine, range.StartColumn + 1 = tn.Range.StartColumn with
        | MainNode("SynExpr.Const"), true, true -> true
        | _ -> false
    )

let private mapNodeToTriviaNode (node: Node) =
    node.Range
    |> Option.map (fun range -> TriviaNodeAssigner(MainNode(node.Type), range, Some node.FsAstNode))

let private commentIsAfterLastTriviaNode (triviaNodes: TriviaNodeAssigner list) (range: range) =
    match List.filter isMainNodeButNotAnonModule triviaNodes with
    | [tn] when (mainNodeIs "SynModuleOrNamespaceSig.NamedModule" tn) -> true
    | mainNodes -> mainNodes |> List.forall (fun tn -> tn.Range.EndLine < range.StartLine)

let private updateTriviaNode (lens: TriviaNodeAssigner -> unit)  (triviaNodes: TriviaNodeAssigner list) triviaNode =
    match triviaNode with
    | Some tNode ->
        // There are situations where the same range can be linked to multiple different AST nodes.
        // F.ex a getter and setter in one line.
        // We want to be sure that one node will be projected by the lens function.
        let index =
            triviaNodes
            |> List.findIndex (fun tn -> tn = tNode)
        
        lens triviaNodes.[index]

        triviaNodes
//        |> List.mapi (fun idx tn -> if idx = index then lens tn else tn)
    | None -> triviaNodes

let private findBindingThatStartsWith (triviaNodes: TriviaNodeAssigner list) column line =
    triviaNodes
    |> List.tryFind (fun t ->
        match t.Type with
        | MainNode("Binding") when (t.Range.StartColumn = column && t.Range.StartLine = line) ->
            true
        | MainNode("SynPat.Named") when (t.Range.StartColumn = column && t.Range.StartLine = line) ->
            true
        | _ -> false
    )

let private findParsedHashOnLineAndEndswith (triviaNodes: TriviaNodeAssigner list) startLine endColumn =
    triviaNodes
    |> List.tryFind (fun t ->
        match t.Type with
        | MainNode("ParsedHashDirective") when (t.Range.StartLine = startLine && t.Range.EndColumn >= endColumn) ->
            true
        | _ -> false
    )

// Only return the attributeList when the trivia is under it and above the AST node of which the attribute is a child node.
// f.ex.
// [<Foo()>]
// #if BAR
// let meh = ()
// The trivia '#if BAR' should be linked to the [<Foo()>] attribute
//
// The reason for this is that the range of the attribute is not part of the range of the parent binding.
// This can lead to weird results when used in CodePrinter.
let private triviaBetweenAttributeAndParentBinding (triviaNodes: TriviaNodeAssigner list) line =
    let filteredNodes =
        triviaNodes
        |> List.filter (fun t ->
            match t.Type with
            | MainNode("SynAttributeList")
            | MainNode("SynModuleDecl.Let")
            | MainNode("SynModuleDecl.Types")
            | MainNode("SynModuleSigDecl.NestedModule")
            | MainNode("ValSpfn")
            | MainNode("SynMemberDefn.Member")
            | MainNode("SynMemberDefn.LetBindings")
            | MainNode("Field") -> true
            | _ -> false
        )
        |> List.pairwise

    filteredNodes |> List.tryFind (function
        | f, a when (f.Type = MainNode("Field")
                     && a.Type = MainNode("SynAttributeList")
                     && f.Range.StartLine = a.Range.StartLine
                     && a.Range.StartLine + 1 = f.Range.EndLine) -> true
        | a, p when (a.Type = MainNode("SynAttributeList") && a.Range.StartLine < line && a.Range.StartLine = a.Range.EndLine) ->
            match p.Type with
              | MainNode("SynModuleDecl.Let") when (p.Range.StartLine > line) -> true
              | MainNode("SynAttributeList") when (p.Range.StartLine > line) -> true
              | MainNode("SynModuleDecl.Types") when (p.Range.StartLine > line) -> true
              | _ -> false
        | _ -> false)
    |> Option.bind (fun (a,_) -> if a.Type = MainNode("SynAttributeList") then Some a else None)

let private findASTNodeOfTypeThatContains (nodes: TriviaNodeAssigner list) typeName range =
    nodes
    |> List.filter (fun t ->
        match t.Type with
        | TriviaNodeType.MainNode(mnt) when (mnt = typeName) -> RangeHelpers.``range contains`` t.Range range
        | _ -> false)
    |> List.tryHead

let private addTriviaToTriviaNode triviaBetweenAttributeAndParentBinding (startOfSourceCode:int) (triviaNodes: TriviaNodeAssigner list) trivia =
    match trivia with
    | { Item = Comment(LineCommentOnSingleLine(_)) as comment; Range = range } when (commentIsAfterLastTriviaNode triviaNodes range) ->
        // Comment on is on its own line after all Trivia nodes, most likely at the end of a module
        findLastNode triviaNodes
        |> updateTriviaNode (fun tn -> tn.ContentAfter.Add(comment)) triviaNodes

    | { Item = Comment(LineCommentOnSingleLine(_) as comment); Range = range } ->
        findFirstNodeAfterLine triviaNodes range.StartLine
        |> updateTriviaNode (fun tn -> tn.ContentBefore.Add (Comment(comment))) triviaNodes

    | { Item = Comment(BlockComment(comment, _,_)); Range = range } ->
        let nodeAfter = findNodeAfterLineAndColumn triviaNodes range.StartLine range.StartColumn
        let nodeBefore = findNodeBeforeLineAndColumn triviaNodes range.StartLine range.StartColumn
        match nodeBefore, nodeAfter with
        | (Some n), _ when n.Range.EndLine = range.StartLine ->
            Some n |> updateTriviaNode (fun tn -> tn.ContentAfter.Add(Comment(BlockComment(comment,false,false)))) triviaNodes
        | _, (Some n) ->
            Some n |> updateTriviaNode (fun tn -> 
                let newline = tn.Range.StartLine > range.EndLine
                tn.ContentBefore.Add(Comment(BlockComment(comment,false, newline)))) triviaNodes
        | (Some _), _ when (commentIsAfterLastTriviaNode triviaNodes range) ->
            findLastNode triviaNodes
            |> updateTriviaNode (fun tn ->
                tn.ContentAfter.Add(Comment(BlockComment(comment, true, false)))) triviaNodes
        | (Some n), _ ->
            Some n |> updateTriviaNode (fun tn ->
                tn.ContentAfter.Add(Comment(BlockComment(comment,true,false)))) triviaNodes
        | None, None -> triviaNodes

    | { Item = Comment(LineCommentAfterSourceCode(_) as comment); Range = range } ->
        findLastNodeOnLine  triviaNodes range.EndLine
        |> updateTriviaNode (fun tn -> tn.ContentAfter.Add(Comment(comment))) triviaNodes

    // Newlines are only relevant if they occur after the first line of source code
    | { Item = Newline; Range = range } when (range.StartLine > startOfSourceCode) ->
        match triviaBetweenAttributeAndParentBinding triviaNodes range.StartLine with
        | Some _ as node ->
            updateTriviaNode (fun tn -> tn.ContentAfter.Add(Newline)) triviaNodes node
        | _ ->
            let nodeAfterLine = findFirstNodeAfterLine triviaNodes range.StartLine
            match nodeAfterLine with
            | Some _ ->
                nodeAfterLine
                |> updateTriviaNode (fun tn -> tn.ContentBefore.Add(Newline)) triviaNodes
            | None ->
                // try and find a node above
                findNodeBeforeLineFromStart triviaNodes range.StartLine
                |> updateTriviaNode (fun tn -> tn.ContentAfter.Add(Newline)) triviaNodes

    | { Item = Keyword({ Content = keyword} as kw); Range = range } when (keyword = "override" || keyword = "default" || keyword = "member" || keyword = "abstract") ->
        findMemberDefnMemberNodeOnLine triviaNodes range.StartLine
        |> updateTriviaNode (fun tn -> tn.ContentItself <- Some (Keyword(kw))) triviaNodes

    | { Item = Keyword({ TokenInfo = {TokenName = tn}} as kw); Range = range } when (tn = "QMARK") ->
        findConstNodeAfter triviaNodes range
        |> updateTriviaNode (fun tn -> tn.ContentBefore.Add(Keyword(kw))) triviaNodes

    | { Item = Keyword({ Content = keyword}); Range = range } when (keyword = "if" || keyword = "then" || keyword = "else" || keyword = "elif") ->
        findNodeOnLineAndColumn triviaNodes range.StartLine range.StartColumn
        |> Option.orElseWith(fun () -> findASTNodeOfTypeThatContains triviaNodes "SynExpr.IfThenElse" range)
        |> updateTriviaNode (fun tn -> tn.ContentItself <- Some trivia.Item) triviaNodes

    | { Item = Keyword(keyword); Range = range } ->
        findNodeOnLineAndColumn triviaNodes range.StartLine range.StartColumn
        |> fun nodeOnLineAndColumn ->
            match nodeOnLineAndColumn with
            | Some _ ->
                nodeOnLineAndColumn
                |> updateTriviaNode (fun tn -> tn.ContentBefore.Add(Keyword(keyword))) triviaNodes
            | None ->
                findParsedHashOnLineAndEndswith triviaNodes range.StartLine range.EndColumn
                |> updateTriviaNode (fun tn -> tn.ContentBefore.Add(Keyword(keyword))) triviaNodes

    | { Item = Directive(dc) as directive; Range = range } ->
        match triviaBetweenAttributeAndParentBinding triviaNodes range.StartLine with
        | Some _ as node ->
            updateTriviaNode (fun tn -> tn.ContentAfter.Add(directive)) triviaNodes node
        | _ ->
            match findNodeAfterLineAndColumn triviaNodes range.EndLine range.EndColumn with
            | Some _ as node ->
                updateTriviaNode (fun tn -> tn.ContentBefore.Add(directive)) triviaNodes node
            | None ->
                let findNode nodes = findNodeBeforeLineFromStart nodes range.StartLine

                findNode triviaNodes
                |> updateTriviaNode (fun tn ->
                    let directive = Directive dc
                    tn.ContentAfter.Add(directive)) triviaNodes

    | { Item = StringContent(_) as siNode; Range = range } ->
        findNodeOnLineAndColumn triviaNodes range.StartLine range.StartColumn
        |> updateTriviaNode (fun tn -> tn.ContentItself <- Some siNode) triviaNodes

    | { Item = Number(_) as number; Range = range  } ->
        findConstNodeOnLineAndColumn triviaNodes range.StartLine range.StartColumn
        |> updateTriviaNode (fun tn -> tn.ContentItself <- Some number) triviaNodes

    | { Item = CharContent(_) as chNode; Range = range } ->
        findNodeOnLineAndColumn triviaNodes range.StartLine range.StartColumn
        |> updateTriviaNode (fun tn -> tn.ContentItself <- Some chNode) triviaNodes
        
    | { Item = IdentOperatorAsWord(_) as ifw; Range = range } ->
        findBindingThatStartsWith triviaNodes range.StartColumn range.StartLine
        |> updateTriviaNode (fun tn -> tn.ContentItself <- Some ifw) triviaNodes

    | { Item = IdentBetweenTicks(_) as iNode; Range = range } ->
        triviaNodes
        |> List.tryFind (fun t ->
            let isIdent =
                match t.Type with
                | MainNode("SynExpr.Ident")
                | MainNode("SynPat.Named")
                | MainNode("SynPat.LongIdent")
                | MainNode("Ident") -> true
                | _ -> false
            isIdent && (t.Range.StartColumn = range.StartColumn || t.Range.StartColumn = range.StartColumn + 1) && t.Range.StartLine = range.StartLine
        )
        |> updateTriviaNode (fun tn -> tn.ContentItself <- Some iNode) triviaNodes

    | _ ->
        triviaNodes

let private triviaNodeIsNotEmpty (triviaNode:TriviaNodeAssigner) =
    not(Seq.isEmpty triviaNode.ContentAfter) || not(Seq.isEmpty triviaNode.ContentBefore) || Option.isSome triviaNode.ContentItself


(*
    1. Collect TriviaNode from tokens and AST
    2. Collect TriviaContent from tokens
    3. Merge trivias with triviaNodes
    4. genTrivia should use ranges to identify what extra content should be added from what triviaNode
*)
let collectTrivia tokens lineCount (ast: ParsedInput) =
    let node =
        match ast with
        | ParsedInput.ImplFile (ParsedImplFileInput.ParsedImplFileInput(_, _, _, _, hds, mns, _)) ->            
            Fantomas.AstTransformer.astToNode hds mns

        | ParsedInput.SigFile (ParsedSigFileInput.ParsedSigFileInput(_, _, _ , _, mns)) ->
            Fantomas.AstTransformer.sigAstToNode mns

    let startOfSourceCode =
        match node.Range with
        | Some r -> r.StartLine
        | None -> 1
            
    let triviaNodesFromAST =
        flattenNodeToList node
        |> filterNodes
        |> List.choose mapNodeToTriviaNode

    let hasAnyAttributes = List.exists (fun (tn:TriviaNodeAssigner) -> match tn.Type with | MainNode("SynAttributeList") -> true | _ -> false) triviaNodesFromAST
    let triviaBetweenAttributeAndParentBinding = if hasAnyAttributes then triviaBetweenAttributeAndParentBinding else (fun _ _ -> None)
    let triviaNodesFromTokens = TokenParser.getTriviaNodesFromTokens tokens
    let triviaNodes = triviaNodesFromAST @ triviaNodesFromTokens |> List.sortBy (fun n -> n.Range.Start.Line, n.Range.Start.Column)
    
    let trivias = TokenParser.getTriviaFromTokens tokens lineCount

    let collectedTrivias =
        match trivias with
        | [] -> []
        | _ ->
            List.fold (addTriviaToTriviaNode triviaBetweenAttributeAndParentBinding startOfSourceCode) triviaNodes trivias
            |> List.choose (fun tn ->
                if triviaNodeIsNotEmpty tn then
                    (tn.AstNode |> Option.map (fun _ -> tn.Range),
                     { Type = tn.Type
                       Range = tn.Range
                       ContentBefore = Seq.toList tn.ContentBefore
                       ContentItself = tn.ContentItself
                       ContentAfter = Seq.toList tn.ContentAfter })
                    |> Some
                else
                    None)
    let triviaDict = 
        collectedTrivias |> Seq.choose (function | Some r, t -> Some (toRange r, t) | _ -> None) 
        //|> Dbg.tee (Seq.toArray >> printfn "%A")
        |> Seq.groupBy fst |> Seq.map (fun (r, g) -> r, g |> Seq.map snd |> Seq.toList)
        |> Map.ofSeq
    let tokenTrivias = collectedTrivias |> List.choose (function | None, t -> Some t | _ -> None)
    tokenTrivias, triviaDict