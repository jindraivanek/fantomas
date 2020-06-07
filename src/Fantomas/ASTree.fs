module Fantomas.ASTree
open FSharp.Compiler.SyntaxTree
open Fantomas.FsAstTypes
open Fantomas.AstTransformer
open FSharp.Compiler.Range
open Fantomas.TriviaTypes

[<ReferenceEquality>] // workaround for fsAstProp not being structural eq
type ASTree =
    { Type: FsAstType
      Range: range option
      Properties: FsAstProp list
      Childs: ASTree list
      Parent: ASTree option
      Trivias : TriviaNode list
      FsAstNode: FsAstNode }

let rec fromNode (n: Node) =
    {
        Type = n.Type
        Range = n.Range
        Properties = n.Properties
        Childs = n.Childs |> List.map fromNode
        Parent = None
        Trivias = []
        FsAstNode = n.FsAstNode
    }

let fromAst (hds: ParsedHashDirective list) (mdls: SynModuleOrNamespace list): ASTree =
    AstTransformer.astToNode hds mdls |> fromNode //|> updateParent None
    
let fromSigAst (ast: SynModuleOrNamespaceSig list) : ASTree =
    AstTransformer.sigAstToNode ast |> fromNode //|> updateParent None

let map f (node: ASTree) =
    let rec g node =
        let n = { node with Childs = List.map g node.Childs }
        f n
    g node //|> updateParent None