module internal Fantomas.Trivia

open Fantomas
open Fantomas.AstTransformer
open Fantomas.ASTree
open Fantomas.TriviaTypes
open FSharp.Compiler.Range
open FSharp.Compiler.SyntaxTree
open Fantomas.FsAstTypes

let private isMainNodeButNotAnonModule (node: TriviaNode) =
    match node.Type with
    | MainNode(t) when (t <> SynModuleOrNamespace_AnonModule) -> true
    | _ -> false
    
let isMainNode (node: TriviaNode) =
    match node.Type with
    | MainNode(_) -> true
    | _ -> false
    
let isToken (node: TriviaNode) =
    match node.Type with
    | Token(_) -> true
    | _ -> false

let rec private flattenNodeToList (node: ASTree) =
    [ yield node
      yield! (node.Childs |> List.map flattenNodeToList |> List.collect id) ]
    
let filterNode =
    let filterOutNodeTypes =
        set [
            SynExpr_Sequential // some Sequential nodes are not visited in CodePrinter
            SynModuleOrNamespace_DeclaredNamespace // LongIdent inside Namespace is being processed as children.
            SynModuleOrNamespaceSig_DeclaredNamespace
            SynExpr_LetOrUse
            SynTypeDefnRepr_ObjectModel
            TypeDefnSig
            SynTypeDefnSigRepr_ObjectModel
        ]
    fun (n: ASTree) -> not (Set.contains n.Type filterOutNodeTypes)

let private findFirstNodeOnLine (nodes: TriviaNode list) lineNumber : TriviaNode option =
    nodes
    |> List.filter (fun { Range =r  } -> r.StartLine = lineNumber)
    |> List.sortBy (fun { Range = r } -> r.StartColumn)
    |> List.tryHead
    
let private nodesContainsBothAnonModuleAndOpen (nodes: TriviaNode list) =
    let mainNodeIs name t =  t.Type = MainNode(name)
    List.exists (mainNodeIs SynModuleOrNamespace_AnonModule) nodes &&
    List.exists (mainNodeIs SynModuleDecl_Open) nodes

// the member keyword is not part of an AST node range
// so it is not an ideal candidate node to have trivia content
let private isNotMemberKeyword (node: TriviaNode) =
    match node.Type with
    | Token({ TokenInfo = ti }) when (ti.TokenName = "MEMBER") -> false
    | _ -> true

let private findFirstNodeAfterLine (nodes: TriviaNode list) lineNumber : TriviaNode option =
    nodes
    |> List.filter (fun n -> n.Range.StartLine > lineNumber && isNotMemberKeyword n)
    |> fun filteredNodes ->
        match filteredNodes with
        | moduleAndOpens when (nodesContainsBothAnonModuleAndOpen moduleAndOpens) ->
            moduleAndOpens
            |> List.filter (fun t -> t.Type = MainNode(SynModuleDecl_Open))
            |> List.sortBy (fun t -> t.Range.StartLine)
            |> List.tryHead
        | _ ->
            filteredNodes
            |> List.sortBy (fun { Range = r } -> r.StartLine, r.StartColumn)
            |> List.tryHead

let private findLastNodeOnLine (nodes: TriviaNode list) lineNumber : TriviaNode option =
    nodes
    |> List.filter (fun { Range = r } -> r.EndLine = lineNumber)
    |> List.sortByDescending (fun { Range = r } -> r.EndColumn, r.StartColumn)
    |> List.tryHead

let private findLastNode (nodes: TriviaNode list) : TriviaNode option =
    match nodes with
    | [] -> None
    | nodes ->
        nodes
        |> List.filter isMainNodeButNotAnonModule
        |> List.maxBy (fun tn -> tn.Range.EndLine)
        |> Some

let private findNodeOnLineAndColumn (nodes: TriviaNode list) line column =
    nodes
    |> List.tryFindBack (fun { Range = range } -> range.StartLine = line && range.StartColumn = column)

let private findMemberDefnMemberNodeOnLine (nodes: TriviaNode list) line =
    nodes
    |> List.tryFind (fun { Type = t; Range = r } ->
        match t, r.StartLine = line with
        | MainNode(SynMemberDefn_Member), true
        | MainNode(SynMemberSig_Member), true
        | Token { TokenInfo = { TokenName = "MEMBER" } }, true -> true
        | _ -> false)

let private findNodeBeforeLineAndColumn (nodes: TriviaNode list) line column =
    nodes
    |> List.tryFindBack (fun { Range = range } -> range.StartLine <= line && range.StartColumn <= column)

let private findNodeBeforeLineFromStart (nodes: TriviaNode list) line =
    nodes
    |> List.filter (fun { Range = range } -> range.EndLine < line)
    |> List.sortByDescending (fun { Range = range } -> range.EndLine, -range.StartColumn)
    |> List.tryFind (fun { Range = range } -> range.StartLine < line)
    
let private findNodeBeforeLineFromEnd (nodes: TriviaNode list) line =
    nodes
    |> List.tryFindBack (fun { Range = range } -> range.StartLine < line)

let private findNodeAfterLineAndColumn (nodes: TriviaNode list) line column =
    nodes
    |> List.tryFind (fun { Range = range } ->
        (range.StartLine > line) || (range.StartLine = line && range.StartColumn > column)
    )

let private findConstNodeOnLineAndColumn (nodes: TriviaNode list) line column =
    nodes
    |> List.tryFind (fun { Type = t; Range = r } ->
        match t, line = r.StartLine, column = r.StartColumn with
        | MainNode(SynExpr_Const), true, true -> true
        | _ -> false
    )

let private findConstNodeAfter (nodes: TriviaNode list) (range: range) =
    nodes
    |> List.tryFind (fun { Type = t; Range = r } ->
        match t, range.StartLine = r.StartLine, range.StartColumn + 1 = r.StartColumn with
        | MainNode(SynExpr_Const), true, true -> true
        | _ -> false
    )

let private mapNodeToTriviaNode (node: ASTree) =
    node.Range
    |> Option.map (fun range ->
        { Type = MainNode(node.Type)
          ContentAfter = []
          ContentItself = None
          ContentBefore = []
          Range = range }
    )
    
let private commentIsAfterLastTriviaNode (triviaNodes: TriviaNode list) (range: range) =
    match List.filter isMainNodeButNotAnonModule triviaNodes with
    | [{ Type = MainNode(SynModuleOrNamespaceSig_NamedModule) }] -> true
    | mainNodes -> mainNodes |> List.forall (fun tn -> tn.Range.EndLine < range.StartLine)

let private updateTriviaNode lens (triviaNodes: TriviaNode list) (triviaDict : System.Collections.Generic.IDictionary<TriviaNode,ASTree>) triviaNode =
    match triviaNode with
    | Some tNode ->
        // There are situations where the same range can be linked to multiple different AST nodes.
        // F.ex a getter and setter in one line.
        // We want to be sure that one node will be projected by the lens function.
        let index =
            triviaNodes
            |> List.findIndex (fun tn -> tn = tNode)
        
        triviaNodes
        |> List.mapi (fun idx tn -> if idx = index then let t = lens tn in triviaDict.Add(t, triviaDict.[tn]); triviaDict.Remove tn; t else tn)
    | None -> triviaNodes

/// like updateTriviaNode, but returns None when triviaNode is None
let private tryUpdateTriviaNode lens (triviaNodes: TriviaNode list) triviaDict triviaNode =
    triviaNode |> Option.map (fun tn -> updateTriviaNode lens triviaNodes triviaDict (Some tn))
    
let private findBindingThatStartsWith (triviaNodes: TriviaNode list) column line =
    triviaNodes
    |> List.tryFind (fun t ->
        match t.Type with
        | MainNode(Binding) when (t.Range.StartColumn = column && t.Range.StartLine = line) ->
            true
        | MainNode(SynPat_Named) when (t.Range.StartColumn = column && t.Range.StartLine = line) ->
            true
        | _ -> false
    )

let private findParsedHashOnLineAndEndswith triviaNodes startLine endColumn =
    triviaNodes
    |> List.tryFind (fun t ->
        match t.Type with
        | MainNode(ParsedHashDirective) when (t.Range.StartLine = startLine && t.Range.EndColumn >= endColumn) ->
            true
        | _ -> false
    )

// Only return the attributeList when the trivia is under it and above the AST node of which the attribute is a child node.
// f.ex.
// [Foo()]
// #if BAR
// let meh = ()
// The trivia '#if BAR' should be linked to the [Foo()] attribute
//
// The reason for this is that the range of the attribute is not part of the range of the parent binding.
// This can lead to weird results when used in CodePrinter.
let private triviaBetweenAttributeAndParentBinding triviaNodes line =
    let filteredNodes =
        triviaNodes
        |> List.filter (fun t ->
            match t.Type with
            | MainNode(SynAttribute)
            | MainNode(SynExpr_Paren)
            | MainNode(SynExpr_Tuple)
            | MainNode(SynExpr_Const) ->
                false
            | MainNode(_) -> true
            | _ -> false
        )
        |> List.indexed

    let parentBinding =
        filteredNodes
        |> List.tryFind (fun (_,t) ->
            match t.Type with
            | MainNode(SynModuleDecl_Let) when (t.Range.StartLine > line) -> true
            | MainNode(SynAttributeList) when (t.Range.StartLine > line) -> true
            | MainNode(SynModuleDecl_Types) when (t.Range.StartLine > line) -> true
            | _ -> false
        )

    let attributeList =
        filteredNodes
        |> List.tryFind (fun (_,t) ->
            match t.Type with
            | MainNode(SynAttributeList) when (t.Range.StartLine < line) -> true
            | _ -> false
        )

    match attributeList, parentBinding with
    | Some (ai,a), Some (mdli,_) when (ai + 1 = mdli && a.Range.StartLine = a.Range.EndLine) -> Some a
    | _ -> None

let private findASTNodeOfTypeThatContains (nodes: TriviaNode list) typeName range =
    nodes
    |> List.filter (fun t ->
        match t.Type with
        | TriviaNodeType.MainNode(mnt) when (mnt = typeName) -> RangeHelpers.``range contains`` t.Range range
        | _ -> false)
    |> List.tryHead

let private addTriviaToTriviaNode (startOfSourceCode:int) (triviaDict: System.Collections.Generic.IDictionary<TriviaNode,ASTree>) triviaNodes trivia =
    match trivia with
    | { Item = Comment(LineCommentOnSingleLine(_)) as comment; Range = range } when (commentIsAfterLastTriviaNode triviaNodes range) ->
        // Comment on is on its own line after all Trivia nodes, most likely at the end of a module
        findLastNode triviaNodes
        |> updateTriviaNode (fun tn -> { tn with ContentAfter = List.appendItem tn.ContentAfter comment }) triviaNodes triviaDict

    | { Item = Comment(LineCommentOnSingleLine(_) as comment); Range = range } ->
        findFirstNodeAfterLine triviaNodes range.StartLine
        |> updateTriviaNode (fun tn -> { tn with ContentBefore = List.appendItem  tn.ContentBefore (Comment(comment)) }) triviaNodes triviaDict

    | { Item = Comment(BlockComment(comment, _,_)); Range = range } ->
        let nodeAfter = findNodeAfterLineAndColumn triviaNodes range.StartLine range.StartColumn
        let nodeBefore = findNodeBeforeLineAndColumn triviaNodes range.StartLine range.StartColumn
        match nodeBefore, nodeAfter with
        | (Some n), _ when n.Range.EndLine = range.StartLine ->
            Some n |> updateTriviaNode (fun tn ->
                { tn with ContentAfter = tn.ContentAfter @ [Comment(BlockComment(comment,false,false))] }) triviaNodes triviaDict
        | _, (Some n) ->
            Some n |> updateTriviaNode (fun tn -> 
                let newline = tn.Range.StartLine > range.EndLine
                { tn with ContentBefore = tn.ContentBefore @ [Comment(BlockComment(comment,false, newline))] }) triviaNodes triviaDict
        | (Some _), _ when (commentIsAfterLastTriviaNode triviaNodes range) ->
            findLastNode triviaNodes
            |> updateTriviaNode (fun tn ->
                { tn with ContentAfter = tn.ContentAfter @ [Comment(BlockComment(comment, true, false))] }) triviaNodes triviaDict
        | (Some n), _ ->
            Some n |> updateTriviaNode (fun tn ->
                { tn with ContentAfter = tn.ContentAfter @ [Comment(BlockComment(comment,true,false))] }) triviaNodes triviaDict
        | None, None -> triviaNodes

    | { Item = Comment(LineCommentAfterSourceCode(_) as comment); Range = range } ->
        findLastNodeOnLine  triviaNodes range.EndLine
        |> updateTriviaNode (fun tn -> { tn with ContentAfter = List.appendItem tn.ContentAfter (Comment(comment)) }) triviaNodes triviaDict

    // Newlines are only relevant if they occur after the first line of source code
    | { Item = Newline; Range = range } when (range.StartLine > startOfSourceCode) ->
        match triviaBetweenAttributeAndParentBinding triviaNodes range.StartLine with
        | Some _ as node ->
            updateTriviaNode (fun tn -> { tn with ContentAfter = List.appendItem tn.ContentAfter Newline }) triviaNodes triviaDict node
        | _ ->
            let nodeAfterLine = findFirstNodeAfterLine triviaNodes range.StartLine
            match nodeAfterLine with
            | Some _ ->
                nodeAfterLine
                |> updateTriviaNode (fun tn -> { tn with ContentBefore = List.appendItem tn.ContentBefore Newline }) triviaNodes triviaDict
            | None ->
                // try and find a node above
                findNodeBeforeLineFromStart triviaNodes range.StartLine
                |> updateTriviaNode (fun tn -> { tn with ContentAfter = List.appendItem tn.ContentAfter Newline }) triviaNodes triviaDict

    | { Item = Keyword({ Content = keyword} as kw); Range = range } when (keyword = "override" || keyword = "default" || keyword = "member" || keyword = "abstract") ->
        findMemberDefnMemberNodeOnLine triviaNodes range.StartLine
        |> updateTriviaNode (fun tn -> { tn with ContentItself = Some (Keyword(kw)) }) triviaNodes triviaDict

    | { Item = Keyword({ TokenInfo = {TokenName = tn}} as kw); Range = range } when (tn = "QMARK") ->
        findConstNodeAfter triviaNodes range
        |> updateTriviaNode (fun tn -> { tn with ContentBefore = List.appendItem tn.ContentBefore (Keyword(kw)) }) triviaNodes triviaDict

    | { Item = Keyword({ Content = keyword}); Range = range } when (keyword = "if" || keyword = "then" || keyword = "else" || keyword = "elif") ->
        findNodeOnLineAndColumn triviaNodes range.StartLine range.StartColumn
        |> Option.orElseWith(fun () -> findASTNodeOfTypeThatContains triviaNodes SynExpr_IfThenElse range)
        |> updateTriviaNode (fun tn -> { tn with ContentItself = Some trivia.Item }) triviaNodes triviaDict

    | { Item = Keyword(keyword); Range = range } ->
        findNodeOnLineAndColumn triviaNodes range.StartLine range.StartColumn
        |> fun nodeOnLineAndColumn ->
            match nodeOnLineAndColumn with
            | Some _ ->
                nodeOnLineAndColumn
                |> updateTriviaNode (fun tn -> { tn with ContentBefore = List.appendItem tn.ContentBefore (Keyword(keyword)) }) triviaNodes triviaDict
            | None ->
                findParsedHashOnLineAndEndswith triviaNodes range.StartLine range.EndColumn
                |> updateTriviaNode (fun tn -> { tn with ContentBefore = List.appendItem tn.ContentBefore (Keyword(keyword)) }) triviaNodes triviaDict

    | { Item = Directive(dc) as directive; Range = range } ->
        match triviaBetweenAttributeAndParentBinding triviaNodes range.StartLine with
        | Some _ as node ->
            updateTriviaNode (fun tn -> { tn with ContentAfter = List.appendItem tn.ContentAfter directive }) triviaNodes triviaDict node
        | _ ->
            match findNodeAfterLineAndColumn triviaNodes range.EndLine range.EndColumn with
            | Some _ as node ->
                updateTriviaNode (fun tn -> { tn with ContentBefore = List.appendItem tn.ContentBefore directive }) triviaNodes triviaDict node
            | None ->
                let findNode nodes = findNodeBeforeLineFromStart nodes range.StartLine

                findNode triviaNodes
                |> updateTriviaNode (fun tn ->
                    let directive = Directive dc
                    { tn with ContentAfter = List.appendItem tn.ContentAfter directive }) triviaNodes triviaDict

    | { Item = StringContent(_) as siNode; Range = range } ->
        findNodeOnLineAndColumn triviaNodes range.StartLine range.StartColumn
        |> updateTriviaNode (fun tn -> { tn with ContentItself = Some siNode }) triviaNodes triviaDict

    | { Item = Number(_) as number; Range = range  } ->
        findConstNodeOnLineAndColumn triviaNodes range.StartLine range.StartColumn
        |> updateTriviaNode (fun tn -> { tn with ContentItself = Some number }) triviaNodes triviaDict

    | { Item = CharContent(_) as chNode; Range = range } ->
        findNodeOnLineAndColumn triviaNodes range.StartLine range.StartColumn
        |> updateTriviaNode (fun tn -> { tn with ContentItself = Some chNode }) triviaNodes triviaDict
        
    | { Item = IdentOperatorAsWord(_) as ifw; Range = range } ->
        findBindingThatStartsWith triviaNodes range.StartColumn range.StartLine
        |> updateTriviaNode (fun tn -> { tn with ContentItself = Some ifw }) triviaNodes triviaDict

    | { Item = IdentBetweenTicks(_) as iNode; Range = range } ->
        triviaNodes
        |> List.tryFind (fun t ->
            let isIdent =
                match t.Type with
                | MainNode(SynExpr_Ident)
                | MainNode(SynPat_Named)
                | MainNode(SynPat_LongIdent)
                | MainNode(FsAstType.Ident) -> true
                | _ -> false
            isIdent && (t.Range.StartColumn = range.StartColumn || t.Range.StartColumn = range.StartColumn + 1) && t.Range.StartLine = range.StartLine
        )
        |> updateTriviaNode (fun tn -> { tn with ContentItself = Some iNode }) triviaNodes triviaDict

    | _ ->
        triviaNodes

let private triviaNodeIsNotEmpty triviaNode =
    not(List.isEmpty triviaNode.ContentAfter) || not(List.isEmpty triviaNode.ContentBefore) || Option.isSome triviaNode.ContentItself

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
            Fantomas.ASTree.fromAst hds mns

        | ParsedInput.SigFile (ParsedSigFileInput.ParsedSigFileInput(_, _, _ , _, mns)) ->
            Fantomas.ASTree.fromSigAst mns

    let startOfSourceCode =
        match node.Range with
        | Some r -> r.StartLine
        | None -> 1
            
    let triviaNodesFromASTDict =
        flattenNodeToList node
        |> List.filter filterNode
        |> List.choose (fun n -> mapNodeToTriviaNode n |> Option.map (fun t -> t, n))
        |> Dict.ofSeq
    let triviaNodesFromAST = triviaNodesFromASTDict.Keys |> Seq.toList
    let triviaNodesFromTokens = TokenParser.getTriviaNodesFromTokens tokens
    let triviaNodes = triviaNodesFromAST @ triviaNodesFromTokens |> List.sortBy (fun n -> n.Range.Start.Line, n.Range.Start.Column)
    
    let trivias = TokenParser.getTriviaFromTokens tokens lineCount

    let collectedTrivias =
        match trivias with
        | [] -> []
        | _ ->
            List.fold (addTriviaToTriviaNode startOfSourceCode triviaNodesFromASTDict) triviaNodes trivias
            |> List.filter (triviaNodeIsNotEmpty) // only keep nodes where something special needs to happen.
    
    let d = collectedTrivias |> List.groupBy (fun t -> triviaNodesFromASTDict |> Dict.tryGet t) |> dict
    node |> ASTree.map (fun n -> Dict.tryGet (Some n) d |> Option.map (fun ts -> { n with Trivias = ts }) |> Option.defaultValue n)