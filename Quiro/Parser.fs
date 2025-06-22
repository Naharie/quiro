[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Quiro.Parser

open FParsec
open Quiro.Parser.Internal

type ScriptLine = Quiro.Parser.Internal.ScriptLine

let isInLanguageServerMode() = isLanguageServerMode
let setLanguageServerMode status = isLanguageServerMode <- status

let parseExpression file text =
    match runParserOnString term () file text with
    | Success(result, _, _) -> Result.Ok result
    | Failure(message, _, _) -> Result.Error message

let parseGoal file text =
    match runParserOnString goal () file text with
    | Success(result, _, _) -> Result.Ok result
    | Failure(message, _, _) -> Result.Error message
  
let parseDeclaration file text =
    match runParserOnString declaration () file text with
    | Success(result, _, _) -> Result.Ok result
    | Failure(message, _, _) -> Result.Error message

let parseScript file code =
    match runParserOnString script () file code with
    | Success(result, _, _) -> Result.Ok result
    | Failure(message, _, _) -> Result.Error message