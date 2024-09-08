module Quiro.Parser

open ExtendedNumerics
open FParsec
open DataTypes
open Quiro.DataTypes

type Parser<'t> = Parser<'t, unit>

let atomTerm, atomParser =
    let letter = satisfy System.Char.IsLower
    
    let headChar = letter
    let symbols = anyOf [ '_'; '~'; '`'; '!'; '@'; '#'; ]
    let bodyChar = letter <|> symbols <|> digit
    
    let unescapedChar = noneOf [ '\\'; '\'' ]
    let escapedChar = skipChar '\\' >>. anyOf [ '\\'; '\'' ]
    
    let atomParser: _ Parser =
        let unwrappedAtom =
            headChar .>>. manyChars bodyChar
            |>> fun (head, body) -> (string head) + body
        let wrappedAtom =
            let singleQuote = skipChar '\''
            between singleQuote singleQuote (many1Chars (unescapedChar <|> escapedChar))
        
        unwrappedAtom <|> wrappedAtom
        
    let atomTerm: _ Parser = atomParser |>> Atom
        
    (atomTerm, atomParser)
let variableTerm, variableParser =
    let symbols = anyOf [ '_'; '~'; '`'; '!'; '@'; '#'; ]
    let headChar = satisfy System.Char.IsUpper
    let bodyChar = letter <|> symbols <|> digit
    
    let variableParser: _ Parser =
        headChar .>>. manyChars bodyChar
        |>> fun (head, body) -> (string head) + body
    let variableTerm: _ Parser = variableParser |>> Variable
    
    variableTerm, variableParser

let integerTerm: _ Parser =
    let options =
        NumberLiteralOptions.AllowMinusSign
        ||| NumberLiteralOptions.DefaultInteger
    
    numberLiteral options "integer"
    |>> fun literal ->
        bigint.Parse literal.String
        |> Integer
let floatTerm: _ Parser =
    let options =
        NumberLiteralOptions.AllowMinusSign
        ||| NumberLiteralOptions.AllowFraction
        ||| NumberLiteralOptions.AllowExponent
        ||| NumberLiteralOptions.DefaultFloat
    
    numberLiteral options "decimal"
    |>> fun literal ->
        BigDecimal.Parse literal.String
        |> Float

let textTerm: _ Parser =
    let quote = skipChar '"'
    let unescapedChar = noneOf [ '\\'; '"' ]
    let escapedChar = skipChar '\\' >>. anyOf [ '\\'; '"' ]
    
    between quote quote (manyChars (unescapedChar <|> escapedChar))
    |>> fun text ->
        text.ToCharArray()
        |> Array.map (int >> bigint >> Integer)
        |> Array.toList
        |> ListTerm

let simpleTerm, simpleTermRef = createParserForwardedToRef() : Parser<SimpleTerm> * Parser<SimpleTerm> ref

let listTerm: _ Parser =
    let startList = skipChar '['
    let endList = skipChar ']'
    let separator = skipChar ','
    
    between startList endList (sepBy simpleTerm separator)
    |>> ListTerm

simpleTermRef.Value <- opt spaces >>. choice [
    atomTerm
    variableTerm
    integerTerm
    floatTerm
    textTerm
    listTerm
] .>> opt spaces

let compoundParser =
    let startArgs = skipChar '('
    let endArgs = skipChar ')'
    let separator = skipChar ','
    
    let argsParser = between startArgs endArgs (sepBy simpleTerm separator)
    
    let compoundParser: _ Parser = atomParser .>>. opt argsParser
        
    compoundParser

type private GoalUnionKind = Conjunction | Disjunction

let goal: _ Parser =
    let simpleGoal =
        opt spaces >>. compoundParser .>> opt spaces
        |>> fun (functor, args) ->
            SimpleGoal(functor, args |> Option.map List.toArray |> Option.defaultValue Array.empty)
            
    simpleGoal .>>. many (choice [
        charReturn ',' Conjunction .>>. simpleGoal
        charReturn ';' Disjunction .>>. simpleGoal
    ])
    |>> fun (baseGoal, extraGoals) ->
        extraGoals
        |> List.fold (fun currentGoal (kind, additionalGoal) ->
            match kind with
            | Conjunction -> ConjunctionGoal (currentGoal, additionalGoal)
            | Disjunction -> DisjunctionGoal (currentGoal, additionalGoal)
        ) baseGoal

let rule: _ Parser =
    opt spaces >>. compoundParser .>> opt spaces .>>. opt (skipString ":-" >>. goal) .>> skipChar '.'
    |>> fun ((functor, args), goal) ->
        Rule(
            functor,
            args |> Option.map List.toArray |> Option.defaultValue Array.empty,
            goal |> Option.defaultWith (fun () -> SimpleGoal("true", Array.empty))
        )

let parse text =
    match run rule text with
    | Success(result, _, _) -> Result.Ok result
    | Failure(message, _, _) -> Result.Error message