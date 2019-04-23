module internal Fantomas.TokenParser

open FSharp.Compiler.AbstractIL.Internal.Library
open System
open FSharp.Compiler.SourceCodeServices
open System.Text.RegularExpressions
open Fantomas
open Fantomas.TriviaTypes

type Token =
    { TokenInfo:FSharpTokenInfo
      LineNumber: int
      Content: string }

// workaround for cases where tokenizer dont output "delayed" part of operator after ">."
// See https://github.com/fsharp/FSharp.Compiler.Service/issues/874
let private isTokenAfterGreater token (greaterToken: Token) =
    let greaterToken = greaterToken.TokenInfo
    greaterToken.TokenName = "GREATER" && token.TokenName <> "GREATER" && greaterToken.RightColumn <> (token.LeftColumn + 1)

let getTokenText (sourceCodeLines: string list) line (token: FSharpTokenInfo) =
    sourceCodeLines.[line - 1].Substring(token.LeftColumn, token.RightColumn - token.LeftColumn + 1)

/// Tokenize a single line of F# code
let rec private tokenizeLine (tokenizer:FSharpLineTokenizer) sourceCodeLines state lineNumber tokens =
  match tokenizer.ScanToken(state), List.tryHead tokens with
  | (Some tok, state), Some greaterToken when (isTokenAfterGreater tok greaterToken) ->
      let extraTokenInfo =
        { tok with
                TokenName = "DELAYED"
                LeftColumn = greaterToken.TokenInfo.RightColumn + 1
                Tag = -1
                CharClass = FSharpTokenCharKind.Operator
                RightColumn = tok.LeftColumn - 1 }

      let extraToken =
          { TokenInfo = extraTokenInfo; LineNumber = lineNumber; Content = getTokenText sourceCodeLines lineNumber extraTokenInfo }
          
      let token =
          { TokenInfo = tok; LineNumber = lineNumber; Content = getTokenText sourceCodeLines lineNumber tok }
      
      tokenizeLine tokenizer sourceCodeLines state lineNumber ([token;extraToken] @ tokens)
      
  | (Some tok, state), _ ->
      let token: Token = { TokenInfo = tok; LineNumber = lineNumber; Content = getTokenText sourceCodeLines lineNumber tok }
      // Tokenize the rest, in the new state
      tokenizeLine tokenizer sourceCodeLines state lineNumber (token::tokens)

  | (None, state), _ ->
      state, tokens
  
let private tokenizeLines (sourceTokenizer: FSharpSourceTokenizer) allLines state =
  allLines
  |> List.mapi (fun index line -> line, (index + 1)) // line number is needed in tokenizeLine
  |> List.fold (fun (state, tokens) (line, lineNumber) ->
      let tokenizer = sourceTokenizer.CreateLineTokenizer(line)
      let nextState, tokensOfLine =
          tokenizeLine tokenizer allLines state lineNumber []
      
      let allTokens = List.append tokens (List.rev tokensOfLine) // tokens of line are add in reversed order
      (nextState, allTokens)
  ) (state, []) // empty tokens to start with
  |> snd // ignore the state

let tokenize defines (content : string) : Token list =
    let sourceTokenizer = FSharpSourceTokenizer("INTERACTIVE" :: defines, Some "/tmp.fsx")
    let lines = String.normalizeThenSplitNewLine content |> Array.toList
    tokenizeLines sourceTokenizer lines FSharpTokenizerLexState.Initial
    
/// Regex alone won't cut it, good enough for now
let getDefines sourceCode =
    Regex.Matches(sourceCode, "#if\\s(\\S+)")
    |> Seq.cast<Match>
    |> Seq.map (fun mtc -> mtc.Value.Substring(4))
    |> Seq.toArray

let private getRangeBetween name startToken endToken =
    let start = FSharp.Compiler.Range.mkPos startToken.LineNumber startToken.TokenInfo.LeftColumn
    let endR = FSharp.Compiler.Range.mkPos endToken.LineNumber endToken.TokenInfo.RightColumn
    FSharp.Compiler.Range.mkRange name start endR
    
let private appendToList items item =
    List.singleton item
    |> (@) items


let rec private getTriviaFromTokensThemSelves (allTokens: Token list) (tokens: Token list) foundTrivia =
    match tokens with
    | headToken::rest when (headToken.TokenInfo.TokenName = "LINE_COMMENT") ->
        let lineCommentTokens =
            rest
            |> List.takeWhile (fun t -> t.TokenInfo.TokenName = "LINE_COMMENT" && t.LineNumber = headToken.LineNumber)
            
        let comment =
            lineCommentTokens
            |> (@) (List.singleton headToken)
            |> List.map (fun t -> t.Content)
            |> String.concat String.Empty
            
        let nextTokens =
            List.length lineCommentTokens
            |> fun length -> List.skip length rest
            
        let range =
            let lastToken = List.last lineCommentTokens
            getRangeBetween "line comment" headToken lastToken
            
        let info =
            let toLineComment =
                allTokens
                |> List.exists (fun t -> t.LineNumber = headToken.LineNumber && t.TokenInfo.TokenName <> "WHITESPACE" && t.TokenInfo.RightColumn < headToken.TokenInfo.LeftColumn)
                |> fun e -> if e then LineCommentAfterSourceCode else LineCommentOnSingleLine
            
            let comment =
                toLineComment comment
                |> Comment
            
            Trivia.Create comment range
            |> appendToList foundTrivia
            
        getTriviaFromTokensThemSelves allTokens nextTokens info
        
    | headToken::rest when (headToken.TokenInfo.TokenName = "COMMENT") ->
        let blockCommentTokens =
            rest
            |> List.takeWhile (fun t -> t.TokenInfo.TokenName = "COMMENT")
            
        let comment =
            blockCommentTokens
            |> (@) (List.singleton headToken)
            |> List.groupBy (fun t -> t.LineNumber)
            |> List.map (fun (_, g) ->
                g
                |> List.map (fun t -> t.Content)
                |> String.concat String.Empty
            )
            |> String.concat Environment.NewLine
            
        let nextTokens =
            List.length blockCommentTokens
            |> fun length -> List.skip length rest
            
        let range =
            let lastToken = List.last blockCommentTokens
            getRangeBetween "block comment" headToken lastToken
            
        let info =
            Trivia.Create (Comment(BlockComment(comment))) range
            |> appendToList foundTrivia
            
        getTriviaFromTokensThemSelves allTokens nextTokens info

    | headToken::rest when (headToken.TokenInfo.ColorClass = FSharpTokenColorKind.Keyword) ->
        let keyword = headToken.Content |> TriviaContent.Keyword
        let range = getRangeBetween "keyword" headToken headToken
        let info =
            Trivia.Create keyword range
            |> appendToList foundTrivia

        getTriviaFromTokensThemSelves allTokens rest info
        
    | (_)::rest -> getTriviaFromTokensThemSelves allTokens rest foundTrivia
    
    | [] -> foundTrivia

let createNewLine lineNumber =
    let pos = FSharp.Compiler.Range.mkPos lineNumber 0
    let range = FSharp.Compiler.Range.mkRange "newline" pos pos
    { Item = Newline; Range = range }

let private findEmptyNewlinesInTokens (tokens: Token list) =
    let firstLine =
        tokens
        |> List.map (fun t -> t.LineNumber)
        |> List.min

    let lastLine =
        tokens
        |> List.map (fun t -> t.LineNumber)
        |> List.max

    let completeEmptyLines =
        [firstLine .. lastLine]
        |> List.filter (fun line ->
            not (List.exists (fun t -> t.LineNumber = line) tokens)
        )
        |> List.map (fun line -> createNewLine line)

    let linesWithOnlySpaces =
        tokens
        |> List.groupBy (fun t -> t.LineNumber)
        |> List.filter (fun (_, g) -> (List.length g) = 1 && (List.head g).TokenInfo.TokenName = "WHITESPACE")
        |> List.map (fst >> createNewLine)
        
    completeEmptyLines @ linesWithOnlySpaces

let getTriviaFromTokens (tokens: Token list) =
    let fromTokens = getTriviaFromTokensThemSelves tokens tokens []
    let newLines = findEmptyNewlinesInTokens tokens

    fromTokens @ newLines