module Fantomas.Context

open System
open System.IO
open System.Collections.Generic
open System.CodeDom.Compiler
open FSharp.Compiler.Range
open Fantomas.FormatConfig
open Fantomas.Trivia
open Fantomas.TriviaTypes

/// Wrapping IndentedTextWriter with current column position
type ColumnIndentedTextWriter(tw : TextWriter, ?isDummy) =
    let isDummy = isDummy |> Option.defaultValue false
    let indentWriter = new IndentedTextWriter(tw, " ")
    let mutable col = indentWriter.Indent

    // on newline, bigger from Indent and atColumn is selected
    // that way we avoid bigger than indentSpace indentation when indent is used after atCurrentColumn
    let mutable atColumn = 0
    
    let applyAtColumn f =
        let newIndent = f atColumn
        indentWriter.Indent <- newIndent

    member __.IsDummy = isDummy
    
    member __.ApplyAtColumn f = applyAtColumn f
    
    member __.Write(s : string) =
        match s.LastIndexOf('\n') with
        | -1 -> col <- col + s.Length
        | i ->
            applyAtColumn (fun x -> max indentWriter.Indent x)
            col <- s.Length - i - 1
        indentWriter.Write(s)

    member __.WriteLine(s : string) =
        applyAtColumn (fun x -> max indentWriter.Indent x)
        col <- indentWriter.Indent
        indentWriter.WriteLine(s)

    /// Current column of the page in an absolute manner
    member __.Column 
        with get() = col
        and set i = col <- i

    member __.Indent 
        with get() = indentWriter.Indent
        and set i = indentWriter.Indent <- i

    member __.AtColumn 
        with get() = atColumn
        and set i = atColumn <- i    

    member __.InnerWriter = indentWriter.InnerWriter

    interface IDisposable with
        member __.Dispose() =
            indentWriter.Dispose()    

type internal Context = 
    { Config : FormatConfig; 
      Writer : ColumnIndentedTextWriter;
      mutable BreakLines : bool;
      BreakOn : string -> bool;
      /// The original source string to query as a last resort 
      Content : string; 
      /// Positions of new lines in the original source string
      Positions : int []; 
      /// Comments attached to appropriate locations
      Comments : Dictionary<pos, string list>;
      /// Compiler directives attached to appropriate locations
      Directives : Dictionary<pos, string>
      Trivia : Dictionary<AstTransformer.FsAstNode, TriviaNode list>
      TriviaIndexes : list<AstTransformer.FsAstNode * TriviaTypes.TriviaIndex> //TODO: use PersistentHashMap
      NodePath : AstTransformer.FsAstNode list}

    /// Initialize with a string writer and use space as delimiter
    static member Default = 
        { Config = FormatConfig.Default;
          Writer = new ColumnIndentedTextWriter(new StringWriter());
          BreakLines = true; BreakOn = (fun _ -> false); 
          Content = ""; Positions = [||]; Comments = Dictionary();
          Directives = Dictionary(); Trivia = Dictionary(); TriviaIndexes = [];
          NodePath = [] }

    static member create config defines (content : string) maybeAst =
        let content = String.normalizeNewLine content
        let positions = 
            content.Split('\n')
            |> Seq.map (fun s -> String.length s + 1)
            |> Seq.scan (+) 0
            |> Seq.toArray
        //let (comments, directives, _) = filterCommentsAndDirectives content
        let tokens = TokenParser.tokenize defines content
        let trivia =
            maybeAst |> Option.map (Trivia.collectTrivia tokens)
            |> Option.defaultValue Context.Default.Trivia

        { Context.Default with 
            Config = config; Content = content; Positions = positions; 
            Comments = null; Directives = null; Trivia = trivia }

    member x.CurrentNode = x.NodePath |> List.tryHead
    
    member x.With(writer : ColumnIndentedTextWriter, ?keepPageWidth) =
        let keepPageWidth = keepPageWidth |> Option.defaultValue false
        writer.Indent <- x.Writer.Indent
        writer.Column <- x.Writer.Column
        writer.AtColumn <- x.Writer.AtColumn
        // Use infinite column width to encounter worst-case scenario
        let config = { x.Config with PageWidth = if keepPageWidth then x.Config.PageWidth else Int32.MaxValue }
        { x with Writer = writer; Config = config }

let internal dump (ctx: Context) =
    ctx.Writer.InnerWriter.ToString()

// A few utility functions from https://github.com/fsharp/powerpack/blob/master/src/FSharp.Compiler.CodeDom/generator.fs

/// Indent one more level based on configuration
let internal indent (ctx : Context) = 
    ctx.Writer.Indent <- ctx.Writer.Indent + ctx.Config.IndentSpaceNum
    // if atColumn is bigger then after indent, then we use atColumn as base for indent
    ctx.Writer.ApplyAtColumn (fun x -> if x >= ctx.Writer.Indent then x + ctx.Config.IndentSpaceNum else ctx.Writer.Indent)
    ctx

/// Unindent one more level based on configuration
let internal unindent (ctx : Context) = 
    ctx.Writer.Indent <- max ctx.Writer.AtColumn (ctx.Writer.Indent - ctx.Config.IndentSpaceNum)
    ctx

/// Increase indent by i spaces
let internal incrIndent i (ctx : Context) = 
    ctx.Writer.Indent <- ctx.Writer.Indent + i
    ctx

/// Decrease indent by i spaces
let internal decrIndent i (ctx : Context) = 
    ctx.Writer.Indent <- max 0 (ctx.Writer.Indent - i)
    ctx

/// Apply function f at an absolute indent level (use with care)
let internal atIndentLevel alsoSetIndent level (f : Context -> Context) ctx =
    if level < 0 then
        invalidArg "level" "The indent level cannot be negative."
    let oldLevel = ctx.Writer.Indent
    let oldColumn = ctx.Writer.AtColumn
    if alsoSetIndent then ctx.Writer.Indent <- level
    ctx.Writer.AtColumn <- level
    let result = f ctx
    ctx.Writer.AtColumn <- oldColumn
    ctx.Writer.Indent <- oldLevel
    result

/// Set minimal indentation (`atColumn`) at current column position - next newline will be indented on `max indent atColumn`
/// Example:
/// { X = // indent=0, atColumn=2
///     "some long string" // indent=4, atColumn=2
///   Y = 1 // indent=0, atColumn=2
/// }
/// `atCurrentColumn` was called on `X`, then `indent` was called, but "some long string" have indent only 4, because it is bigger than `atColumn` (2).
let internal atCurrentColumn (f : _ -> Context) (ctx : Context) =
    atIndentLevel false ctx.Writer.Column f ctx

/// Write everything at current column indentation, set `indent` and `atColumn` on current column position
/// /// Example (same as above):
/// { X = // indent=2, atColumn=2
///       "some long string" // indent=6, atColumn=2
///   Y = 1 // indent=2, atColumn=2
/// }
/// `atCurrentColumn` was called on `X`, then `indent` was called, "some long string" have indent 6, because it is indented from `atCurrentColumn` pos (2).
let internal atCurrentColumnIndent (f : _ -> Context) (ctx : Context) =
    atIndentLevel true ctx.Writer.Column f ctx

/// Function composition operator
let internal (+>) (ctx : Context -> Context) (f : _ -> Context) x =
    f (ctx x)

/// Break-line and append specified string
let internal (++) (ctx : Context -> Context) (str : string) x =
    let c = ctx x
    c.Writer.WriteLine("")
    c.Writer.Write(str)
    c

/// Break-line if config says so
let internal (+-) (ctx : Context -> Context) (str : string) x =
    let c = ctx x
    if c.BreakOn str then 
        c.Writer.WriteLine("")
    else
        c.Writer.Write(" ")
    c.Writer.Write(str)
    c

/// Append specified string without line-break
let internal (--) (ctx : Context -> Context) (str : string) x =
    let c = ctx x
    c.Writer.Write(str)
    c

let internal (!-) (str : string) = id -- str 
let internal (!+) (str : string) = id ++ str 

/// Print object converted to string
let internal str (o : 'T) (ctx : Context) =
    ctx.Writer.Write(o.ToString())
    ctx

/// Similar to col, and supply index as well
let internal coli f' (c : seq<'T>) f (ctx : Context) =
    let mutable tryPick = true
    let mutable st = ctx
    let mutable i = 0
    let e = c.GetEnumerator()   
    while (e.MoveNext()) do
        if tryPick then tryPick <- false else st <- f' st
        st <- f i (e.Current) st
        i  <- i + 1
    st

/// Process collection - keeps context through the whole processing
/// calls f for every element in sequence and f' between every two elements 
/// as a separator. This is a variant that works on typed collections.
let internal col f' (c : seq<'T>) f (ctx : Context) =
    let mutable tryPick = true
    let mutable st = ctx
    let e = c.GetEnumerator()   
    while (e.MoveNext()) do
        if tryPick then tryPick <- false else st <- f' st
        st <- f (e.Current) st
    st

/// Similar to col, apply one more function f2 at the end if the input sequence is not empty
let internal colPost f2 f1 (c : seq<'T>) f (ctx : Context) =
    if Seq.isEmpty c then ctx
    else f2 (col f1 c f ctx)

/// Similar to col, apply one more function f2 at the beginning if the input sequence is not empty
let internal colPre f2 f1 (c : seq<'T>) f (ctx : Context) =
    if Seq.isEmpty c then ctx
    else col f1 c f (f2 ctx)

/// If there is a value, apply f and f' accordingly, otherwise do nothing
let internal opt (f' : Context -> _) o f (ctx : Context) =
    match o with
    | Some x -> f' (f x ctx)
    | None -> ctx

/// Similar to opt, but apply f2 at the beginning if there is a value
let internal optPre (f2 : _ -> Context) (f1 : Context -> _) o f (ctx : Context) =
    match o with
    | Some x -> f1 (f x (f2 ctx))
    | None -> ctx

/// b is true, apply f1 otherwise apply f2
let internal ifElse b (f1 : Context -> Context) f2 (ctx : Context) =
    if b then f1 ctx else f2 ctx

let internal ifElseCtx cond (f1 : Context -> Context) f2 (ctx : Context) =
    if cond ctx then f1 ctx else f2 ctx

/// Repeat application of a function n times
let internal rep n (f : Context -> Context) (ctx : Context) =
    [1..n] |> List.fold (fun c _ -> f c) ctx

let internal wordAnd = !- " and "
let internal wordOr = !- " or "
let internal wordOf = !- " of "   

// Separator functions
        
let internal sepDot = !- "."
let internal sepSpace = !- " "      
let internal sepNln = !+ ""
let internal sepStar = !- " * "
let internal sepEq = !- " ="
let internal sepArrow = !- " -> "
let internal sepWild = !- "_"
let internal sepNone = id
let internal sepBar = !- "| "

/// opening token of list
let internal sepOpenL (ctx : Context) =  
    if ctx.Config.SpaceAroundDelimiter then str "[ " ctx else str "[" ctx 

/// closing token of list
let internal sepCloseL (ctx : Context) =
    if ctx.Config.SpaceAroundDelimiter then str " ]" ctx else str "]" ctx 

/// opening token of list
let internal sepOpenLFixed = !- "["

/// closing token of list
let internal sepCloseLFixed = !- "]"

/// opening token of array
let internal sepOpenA (ctx : Context) =
    if ctx.Config.SpaceAroundDelimiter then str "[| " ctx else str "[|" ctx 

/// closing token of array
let internal sepCloseA (ctx : Context) = 
    if ctx.Config.SpaceAroundDelimiter then str " |]" ctx else str "|]" ctx 

/// opening token of list
let internal sepOpenAFixed = !- "[|"
/// closing token of list
let internal sepCloseAFixed = !- "|]"

/// opening token of sequence or record
let internal sepOpenS (ctx : Context) = 
    if ctx.Config.SpaceAroundDelimiter then str "{ " ctx else str "{" ctx 

/// closing token of sequence or record
let internal sepCloseS (ctx : Context) = 
    if ctx.Config.SpaceAroundDelimiter then str " }" ctx else str "}" ctx

/// opening token of anon record
let internal sepOpenAnonRecd (ctx : Context) =
    if ctx.Config.SpaceAroundDelimiter then str "{| " ctx else str "{|" ctx 

/// closing token of anon record
let internal sepCloseAnonRecd (ctx : Context) =
    if ctx.Config.SpaceAroundDelimiter then str " |}" ctx else str "|}" ctx

/// opening token of sequence
let internal sepOpenSFixed = !- "{"

/// closing token of sequence
let internal sepCloseSFixed = !- "}"

/// opening token of tuple
let internal sepOpenT = !- "("

/// closing token of tuple
let internal sepCloseT = !- ")"

let internal autoNlnCheck f sep (ctx : Context) =
    if not ctx.BreakLines then false else
    // Create a dummy context to evaluate length of current operation
    use colWriter = new ColumnIndentedTextWriter(new StringWriter(), isDummy = true)
    let dummyCtx = ctx.With(colWriter)
    let col = (dummyCtx |> sep |> f).Writer.Column
    // This isn't accurate if we go to new lines
    col > ctx.Config.PageWidth

let internal futureNlnCheck f (ctx : Context) =
    if not ctx.BreakLines then false else
    // Create a dummy context to evaluate length of current operation
    use colWriter = new ColumnIndentedTextWriter(new StringWriter(), isDummy = true)
    let dummyCtx = ctx.With(colWriter, true)
    let writer = (dummyCtx |> f).Writer
    let str = writer.InnerWriter.ToString()
    let withoutStringConst = 
        str.Replace("\\\\", System.String.Empty).Replace("\\\"", System.String.Empty).Split([|'"'|])
        |> Seq.indexed |> Seq.filter (fun (i, _) -> i % 2 = 0) |> Seq.map snd |> String.concat System.String.Empty
    let lines = withoutStringConst.Split([|Environment.NewLine|], StringSplitOptions.None) 
    //printfn "futureNlnCheck: %i %s" writer.Column str
    (lines |> Seq.length) >= 2 || writer.Column > ctx.Config.PageWidth

let internal autoNlnByFuture f = ifElseCtx (futureNlnCheck f) (sepNln +> f) f
let internal autoIndentNlnByFuture f = ifElseCtx (futureNlnCheck f) (indent +> sepNln +> f +> unindent) f

/// Set a checkpoint to break at an appropriate column
let internal autoNlnOrAddSep f sep (ctx : Context) =
    let isNln = autoNlnCheck f sep ctx
    if isNln then
       f (sepNln ctx)
    else
       f (sep ctx)

let internal autoNln f (ctx : Context) = autoNlnOrAddSep f sepNone ctx

let internal autoNlnOrSpace f (ctx : Context) = autoNlnOrAddSep f sepSpace ctx

/// Similar to col, skip auto newline for index 0
let internal colAutoNlnSkip0i f' (c : seq<'T>) f (ctx : Context) = 
    coli f' c (fun i c -> if i = 0 then f i c else autoNln (f i c)) ctx

/// Similar to col, skip auto newline for index 0
let internal colAutoNlnSkip0 f' c f = colAutoNlnSkip0i f' c (fun _ -> f)

/// Skip all auto-breaking newlines
let internal noNln f (ctx : Context) : Context = 
    ctx.BreakLines <- false
    let res = f ctx
    ctx.BreakLines <- true
    res 

let internal sepColon (ctx : Context) = 
    if ctx.Config.SpaceBeforeColon then str " : " ctx else str ": " ctx

let internal sepColonFixed = !- ":"

let internal sepComma (ctx : Context) = 
    if ctx.Config.SpaceAfterComma then str ", " ctx else str "," ctx

let internal sepSemi (ctx : Context) = 
    if ctx.Config.SpaceAfterSemicolon then str "; " ctx else str ";" ctx

let internal sepSemiNln (ctx : Context) =
    // sepNln part is essential to indentation
    if ctx.Config.SemicolonAtEndOfLine then (!- ";" +> sepNln) ctx else sepNln ctx

let internal sepBeforeArg (ctx : Context) = 
    if ctx.Config.SpaceBeforeArgument then str " " ctx else str "" ctx

/// Conditional indentation on with keyword
let internal indentOnWith (ctx : Context) =
    if ctx.Config.IndentOnTryWith then indent ctx else ctx

/// Conditional unindentation on with keyword
let internal unindentOnWith (ctx : Context) =
    if ctx.Config.IndentOnTryWith then unindent ctx else ctx

let internal sortAndDeduplicate by l (ctx : Context) =
    if ctx.Config.ReorderOpenDeclaration then
        l |> Seq.distinctBy by |> Seq.sortBy by |> List.ofSeq
    else l

/// Don't put space before and after these operators
let internal NoSpaceInfixOps = set [".."; "?"]

/// Always break into newlines on these operators
let internal NewLineInfixOps = set ["|>"; "||>"; "|||>"; ">>"; ">>="]

/// Never break into newlines on these operators
let internal NoBreakInfixOps = set ["="; ">"; "<";]

let internal getTriviaIndex node (ctx: Context) =
    ctx.TriviaIndexes |> List.tryFind (fun (n,_) -> n = node) |> Option.map snd
    |> Option.defaultValue (TriviaIndex (0,0))

let internal getTriviaIndexBefore node (ctx: Context) = getTriviaIndex node ctx |> fun (TriviaIndex (i,_)) -> i
let internal getTriviaIndexAfter node (ctx: Context) = getTriviaIndex node ctx |> fun (TriviaIndex (_,i)) -> i

let internal increaseTriviaIndex node (deltaBefore, deltaAfter) (ctx: Context) =
    let indexes =
        if ctx.TriviaIndexes |> List.exists (fun (n,_) -> n = node) then
            ctx.TriviaIndexes |> List.map (fun (n,TriviaIndex (i,j)) ->
                if n = node then n, TriviaIndex (i+deltaBefore, j+deltaAfter) else n, TriviaIndex (i,j))
        else (node, TriviaIndex (deltaBefore, deltaAfter)) :: ctx.TriviaIndexes
    { ctx with TriviaIndexes = indexes }

let internal printComment c =
    match c with
    // | XmlComment s -> !- "///" -- s +> sepNln
    | LineCommentAfterSourceCode s
    | LineCommentOnSingleLine s -> !- s +> sepNln
    | BlockComment s -> !- "(*" -- s -- "*)"

let internal printCommentsBefore node (ctx: Context) =
    ctx.Trivia |> Dict.tryGet node
    |> Option.bind (Trivia.getMainNode (getTriviaIndexBefore node ctx))
    |> Option.map (fun n -> col sepNone n.CommentsBefore printComment
                            +> increaseTriviaIndex node (1,0))
    |> Option.defaultValue (!-"")
    |> fun f -> f ctx

let internal printCommentsAfter node (ctx: Context) =
    ctx.Trivia |> Dict.tryGet node
    |> Option.bind (Trivia.getMainNode (getTriviaIndexAfter node ctx))
    |> Option.map (fun n -> col sepNone n.CommentsAfter printComment
                            +> increaseTriviaIndex node (0,1))
    |> Option.defaultValue (!-"")
    |> fun f -> f ctx

let internal enterNode node (ctx: Context) =
    if Some node <> ctx.CurrentNode then
        let ctx' = { ctx with NodePath = node :: ctx.NodePath }
        ctx'.CurrentNode |> Option.map (fun n -> printCommentsBefore n ctx') |> Option.defaultValue ctx'
    else ctx
    
let internal leaveNode node (ctx: Context) =
    assert (Some node = ctx.CurrentNode)
    let ctx' = { ctx with NodePath = List.tail ctx.NodePath }
    ctx'.CurrentNode |> Option.map (fun n -> printCommentsAfter n ctx') |> Option.defaultValue ctx'
