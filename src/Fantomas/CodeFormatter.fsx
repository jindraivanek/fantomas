﻿#r @"C:\Users\nojaf\.nuget\packages\FSharp.Compiler.Service\30.0.0\lib\net461\FSharp.Compiler.Service.dll"
//
//#load "Utils.fs"
//#load "FormatConfig.fs"
//#load "TokenMatcher.fs"
//#load "Context.fs"
//#load "SourceParser.fs"
//#load "SourceTransformer.fs"
//#load "CodePrinter.fs"
//#load "CodeFormatterImpl.fs"
//#load "CodeFormatter.fs"
//
//open Fantomas.FormatConfig
//open Fantomas.CodeFormatter
//open FSharp.Compiler.Range
//open FSharp.Compiler.Interactive.Shell.Settings
//open Fantomas
//
//CodeFormatter.Parse ("Program.fs", """let plus a b = a + b""")
//
//let config = { FormatConfig.Default with PreserveEndOfLine = true }
//
//let formatSrc (s : string) = 
//    formatSourceString false (s.Replace("\r\n", "\n")) config |> printfn "%A";;
//
//fsi.AddPrinter (fun (p : pos) -> p.ToString())
//fsi.AddPrinter (fun (r : range) -> r.ToString())
//
//"""
//type QueryOption =
//    | FixedQuery of string // xpath
//    | KeywordSearch of string // keyword
//
//type MessageTypeQueryMeta =
//    { Options: QueryOption list }
//
//"""
//|> formatSrc
//
//// le nojaf
//let parseAndPrint input = 
//    CodeFormatter.Parse ("Program.fs", input)   
//    |> printfn "%A"

"op_LessThanOrEqual"
|> FSharp.Compiler.PrettyNaming.DecompileOpName

"meh"
|> FSharp.Compiler.PrettyNaming.DecompileOpName