module Quiro.Parser

open System
open ExtendedNumerics
open FParsec
open DataTypes

// Types

type Parser<'t> = Parser<'t, unit>

type Operator<'t> = {
    precedence: int
    handler: 't -> 't -> 't
}

[<Struct>]
type ScriptLine =
    | ScriptDeclaration of Declaration
    | Comment of text:string
    | BlankLine

// Utilities

let ws, ws1 = opt spaces |>> ignore, spaces1

// Expressions

let invalidAtomSymbols = Set.ofList [ '['; ']'; '('; ')'; '{'; '}'; ','; ';'; '.'; '?'  ]
let atomExpr, atomParser =
    let letter = satisfy Char.IsLower
    
    let headChar = letter
    
    let isSymbol char =
        Char.IsSymbol char || Char.IsPunctuation char
    let symbols = satisfy (fun char -> isSymbol char && (invalidAtomSymbols |> Set.contains char |> not))
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
        
    let atomTerm: _ Parser = atomParser |>> Atom <?> "atom"
        
    (atomTerm, atomParser)
let numberExpr: _ Parser =
    let options =
        NumberLiteralOptions.AllowMinusSign
        ||| NumberLiteralOptions.AllowFraction
        ||| NumberLiteralOptions.AllowExponent
        ||| NumberLiteralOptions.DefaultFloat
    
    numberLiteral options "number"
    |>> fun literal ->
        BigDecimal.Parse literal.String
        |> Float
        |> Number

let textExpr: _ Parser =
    let quote = skipChar '"'
    let unescapedChar = noneOf [ '\\'; '"' ]
    let escapedChar = skipChar '\\' >>. anyOf [ '\\'; '"' ]
    
    between quote quote (manyChars (unescapedChar <|> escapedChar))
    <?> "string"
    |>> fun text ->
        text.ToCharArray()
        |> Array.map (int >> BigDecimal >> Float >> Number)
        |> Array.toList
        |> ListTerm

let expressionNoComma, expressionNoCommaRef = createParserForwardedToRef() : Parser<Expression> * Parser<Expression> ref
let expressionWithComma, expressionWithCommaRef = createParserForwardedToRef() : Parser<Expression> * Parser<Expression> ref

let variableExpr, variableParser =
    let symbols = anyOf [ '_'; '~'; '`'; '!'; '@'; '#'; ]
    let headChar = satisfy Char.IsUpper
    let bodyChar = letter <|> symbols <|> digit
    
    let variableParser: _ Parser =
        headChar .>>. manyChars bodyChar
        |>> fun (head, body) -> (string head) + body
    let variableExpression = variableParser |>> Variable <?> "variable"
    
    variableExpression, variableParser

let listExpression: _ Parser =
    let startList = skipChar '['
    let endList = skipChar ']'
    let separator = skipChar ','
    
    between startList endList (sepBy expressionNoComma separator)
    |>> ListTerm
    <?> "list"

let listConsExpr: _ Parser =
    skipChar '[' >>. ws >>. expressionNoComma .>> ws .>> skipChar '|' .>> ws .>>. expressionNoComma .>> ws .>> skipChar ']'
    |>> ListCons
    <?> "list cons"

let compoundParser: _ Parser =
    let startArgs = skipChar '('
    let endArgs = skipChar ')'
    let separator = skipChar ','
    
    let argsParser = between startArgs endArgs (sepBy expressionNoComma separator)
    (atomParser <|> variableParser) .>>. opt argsParser
let functionCallAtomOrVar: _ Parser =
    compoundParser
    |>> fun (functor, args) ->
        match args with
        | Some args ->
            if Char.IsUpper functor[0] then
                DynamicFunctionCall(functor, args)
            else
                FunctionCall(functor, args)
        | None ->
            if Char.IsUpper functor[0] then
                Variable functor
            else
                Atom functor

let goal, goalRef = createParserForwardedToRef() : Parser<Goal> * Parser<Goal> ref

let parenExpr = skipChar '(' >>. ws >>. expressionWithComma .>> ws .>> skipChar ')'
let goalExpr = skipChar '{' >>. ws >>. goal .>> ws .>> skipChar '}' |>> GoalExpr

let operatorCommaExpression = OperatorPrecedenceParser<Expression, unit, unit>()
let operatorNoCommaExpression = OperatorPrecedenceParser<Expression, unit, unit>()

let private addExpressionOperators (doComma: bool) (operatorExpression: OperatorPrecedenceParser<Expression, unit, unit>) =
    let op name precedence =
        operatorExpression.AddOperator(InfixOperator(name, ws, precedence, Associativity.Left, fun a b -> FunctionCall(name, [ a; b ])))

    if doComma then op "," 100

    op "+" 200
    op "-" 200

    op "*" 300
    op "/" 300
    op "div" 300
    op "mod" 300
    op "rem" 300

    op "**" 400
    op "^" 400

operatorCommaExpression.TermParser <- ws >>. choice [
    functionCallAtomOrVar
    numberExpr
    textExpr
    (attempt listConsExpr <|> listExpression)
    parenExpr
] .>> ws
operatorNoCommaExpression.TermParser <- operatorCommaExpression.TermParser

addExpressionOperators true operatorCommaExpression
addExpressionOperators false operatorNoCommaExpression

expressionNoCommaRef.Value <- operatorNoCommaExpression.ExpressionParser
expressionWithCommaRef.Value <- operatorCommaExpression.ExpressionParser

// Goals

let comparisonGoal: _ Parser =
    expressionNoComma .>>. choice [
        pstring "<"
        pstring "<="
        pstring ">"
        pstring ">="
        (attempt (pstring "=:=") <|> pstring "=")
        pstring "is"
    ] .>>. expressionNoComma
    |>> fun ((exprA, op), exprB) ->
        SimpleGoal(op, [ exprA; exprB ])
let simpleGoal: _ Parser =
    compoundParser
    |>> fun (functor, args) ->
        if Char.IsUpper functor[0] then
            DynamicGoal(functor, args |> Option.defaultValue List.empty)
        else
            SimpleGoal(functor, args |> Option.defaultValue List.empty)

let junctionGoal = OperatorPrecedenceParser<Goal, unit, unit>()

junctionGoal.AddOperator(InfixOperator(",", ws, 1100, Associativity.Left, fun a b -> ConjunctionGoal(a, b)))
junctionGoal.AddOperator(InfixOperator(";", ws, 1000, Associativity.Left, fun a b -> DisjunctionGoal(a, b)))

junctionGoal.TermParser <- (attempt comparisonGoal <|> simpleGoal)

goalRef.Value <- junctionGoal.ExpressionParser

let declaration: _ Parser =
    compoundParser .>> ws .>>. opt (choice [
        skipString ":-" >>. ws >>. goal |>> Choice1Of2
        skipString "-->" >>. ws >>. expressionWithComma |>> Choice2Of2
    ]) .>> ws .>> skipChar '.'
    |>> fun ((functor, args), body) ->
        let args = args |> Option.defaultValue List.empty

        match body with
        | Some body ->
             match body with
             | Choice1Of2 goal ->
                 PredicateDeclaration(Predicate(functor, args, goal))
             | Choice2Of2 expression ->
                 FunctionDeclaration(Function(functor, args, expression))
        | None ->
            PredicateDeclaration (Predicate (functor, args, SimpleGoal ("true", List.empty)))

let comment: _ Parser = (ws) >>. skipChar '%' >>. manyChars (noneOf [ '\r'; '\t' ]) .>> ws

let script: _ Parser =
    many1 (choice [
        (ws1) >>. preturn BlankLine
        comment |>> Comment
        declaration |>> ScriptDeclaration
    ]) .>> eof
    |>> fun lines ->
        lines
        |> List.choose(function
            | ScriptDeclaration rule -> Some rule
            | _ -> None
        )

// Parse functions

let parseExpression text =
    match run expressionNoComma text with
    | Success(result, _, _) -> Result.Ok result
    | Failure(message, _, _) -> Result.Error message

let parseGoal text =
    match run goal text with
    | Success(result, _, _) -> Result.Ok result
    | Failure(message, _, _) -> Result.Error message
  
let parseDeclaration text =
    match run declaration text with
    | Success(result, _, _) -> Result.Ok result
    | Failure(message, _, _) -> Result.Error message
   
let parseScript code =
    match run script code with
    | Success(result, _, _) -> Result.Ok result
    | Failure(message, _, _) -> Result.Error message
   