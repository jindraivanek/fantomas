module Fantomas.Tests.UtilsTests

open NUnit.Framework
open Fantomas
open Fantomas.Tests.TestHelper

let private mergeAndCompare a b expected =
    let result =
        String.merge a b
        |> String.normalizeNewLine
    let normalizedExpected = String.normalizeNewLine expected
    normalizedExpected == result

[<Test>]
let ``Merging of source code that starts with a hash`` () =
    let a = """#if NOT_DEFINED
    printfn \"meh\"
#else

#endif
"""

    let b = """#if NOT_DEFINED

#else
    printfn \"foo\"
#endif
"""

    """#if NOT_DEFINED
    printfn \"meh\"
#else
    printfn \"foo\"
#endif
"""
    |> mergeAndCompare a b

[<Test>]
let ``Merging of defines content work when source code starts with a newline`` () =
    let a = """
[<Literal>]
let private assemblyConfig() =
    #if TRACE

    #else
    let x = "x"
    #endif
    x
"""

    let b = """
[<Literal>]
let private assemblyConfig() =
    #if TRACE
    let x = ""
    #else

    #endif
    x
"""

    """
[<Literal>]
let private assemblyConfig() =
#if TRACE
    let x = ""
#else
    let x = "x"
#endif
    x
"""
    |> mergeAndCompare a b
    
[<Test>]
let ``Only split on control structure keyword`` () =
    let a = """
#if INTERACTIVE
#else
#load "../FSharpx.TypeProviders/SetupTesting.fsx"

SetupTesting.generateSetupScript __SOURCE_DIRECTORY__

#load "__setup__.fsx"
#endif
"""

    let b = """
#if INTERACTIVE
#else



#endif
    """

    """
#if INTERACTIVE
#else
#load "../FSharpx.TypeProviders/SetupTesting.fsx"

SetupTesting.generateSetupScript __SOURCE_DIRECTORY__

#load "__setup__.fsx"
#endif
"""
    |> mergeAndCompare a b