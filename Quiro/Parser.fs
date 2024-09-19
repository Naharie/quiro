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
    let symbols = satisfy (fun char -> Char.IsSymbol char && invalidAtomSymbols |> Set.contains char |> not)
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
let integerExpr: _ Parser =
    let options =
        NumberLiteralOptions.AllowMinusSign
        ||| NumberLiteralOptions.DefaultInteger
    
    numberLiteral options "integer"
    |>> fun literal ->
        bigint.Parse literal.String
        |> Integer
let floatExpr: _ Parser =
    let options =
        NumberLiteralOptions.AllowMinusSign
        ||| NumberLiteralOptions.AllowFraction
        ||| NumberLiteralOptions.AllowExponent
        ||| NumberLiteralOptions.DefaultFloat
    
    numberLiteral options "decimal"
    |>> fun literal ->
        BigDecimal.Parse literal.String
        |> Float

let textExpr: _ Parser =
    let quote = skipChar '"'
    let unescapedChar = noneOf [ '\\'; '"' ]
    let escapedChar = skipChar '\\' >>. anyOf [ '\\'; '"' ]
    
    between quote quote (manyChars (unescapedChar <|> escapedChar))
    |>> fun text ->
        text.ToCharArray()
        |> Array.map (bigint >> Integer)
        |> Array.toList
        |> ListTerm

let expression, expressionRef = createParserForwardedToRef() : Parser<Expression> * Parser<Expression> ref

let variableExpr, variableParser =
    let symbols = anyOf [ '_'; '~'; '`'; '!'; '@'; '#'; ]
    let headChar = satisfy Char.IsUpper
    let bodyChar = letter <|> symbols <|> digit
    
    let variableParser: _ Parser =
        headChar .>>. manyChars bodyChar
        |>> fun (head, body) -> (string head) + body
    let variableExpression = variableParser |>> Variable
    
    variableExpression, variableParser

let listExpression: _ Parser =
    let startList = skipChar '['
    let endList = skipChar ']'
    let separator = skipChar ','
    
    between startList endList (sepBy expression separator)
    |>> ListTerm

let listConsExpr: _ Parser =
    skipChar '[' >>. ws >>. expression .>> ws .>> skipChar '|' .>> ws .>>. expression .>> ws .>> skipChar ']'
    |>> ListCons

let compoundParser =
    let startArgs = skipChar '('
    let endArgs = skipChar ')'
    let separator = skipChar ','
    
    let argsParser = between startArgs endArgs (sepBy expression separator)
    let compoundParser: _ Parser = atomParser .>>. opt argsParser
        
    compoundParser
let functionCallOrAtomExpression: _ Parser =
    compoundParser
    |>> fun (functor, args) ->
        match args with
        | Some args ->
            FunctionCall(functor, List.toArray args)
        | None ->
            Atom functor

let goal, goalRef = createParserForwardedToRef() : Parser<Goal> * Parser<Goal> ref

let parenExpr = skipChar '(' >>. ws >>. expression .>> ws .>> skipChar ')'
let goalExpr = skipChar '{' >>. ws >>. goal .>> ws .>> skipChar '}' |>> GoalExpr

let operatorExpression = OperatorPrecedenceParser<Expression, unit, unit>()

let private op name precedence =
    operatorExpression.AddOperator(InfixOperator(name, ws, precedence, Associativity.Left, fun a b -> FunctionCall(name, [| a; b |])))

op "," 600

op "+" 500
op "-" 500

op "*" 400
op "/" 400
op "div" 400
op "mod" 400
op "rem" 400

op "**" 200
op "^" 200

operatorExpression.TermParser <- ws >>. choice [
    functionCallOrAtomExpression
    integerExpr
    floatExpr
    textExpr
    listExpression
    parenExpr
] .>> ws
expressionRef.Value <- operatorExpression.ExpressionParser

// Goals

let simpleGoal: _ Parser =
   expression .>>. opt (choice [
        pstring "<"
        pstring "<="
        pstring ">"
        pstring ">="
        pstring "="
        pstring "=:="
        pstring "is"
    ] .>>. expression)
    |>> fun (exprA, maybeOp) ->
        match maybeOp with
        | Some (op, exprB) ->
            SimpleGoal(op, [| exprA; exprB |])
        | None ->
            match exprA with
            | FunctionCall(functor, args) -> SimpleGoal(functor, args)
            | _ -> failwithf "Unexpected expression in goal position when not used as an argument for a goal level operator!"

let junctionGoal = OperatorPrecedenceParser<Goal, unit, unit>()

junctionGoal.AddOperator(InfixOperator(",", ws, 1000, Associativity.Left, fun a b -> ConjunctionGoal(a, b)))
junctionGoal.AddOperator(InfixOperator(";", ws, 1100, Associativity.Left, fun a b -> DisjunctionGoal(a, b)))

junctionGoal.TermParser <- simpleGoal

goalRef.Value <- junctionGoal.ExpressionParser

let declaration: _ Parser =
    compoundParser .>> ws .>>. opt (choice [
        skipString ":-" >>. ws >>. goal |>> Choice1Of2
        skipString "-->" >>. ws >>. expression |>> Choice2Of2
    ]) .>> ws .>> skipChar '.'
    |>> fun ((functor, args), body) ->
        let args =
            args
            |> Option.defaultValue List.empty
            |> List.toArray

        match body with
        | Some body ->
             match body with
             | Choice1Of2 goal ->
                 PredicateDeclaration(Predicate(functor, args, goal))
             | Choice2Of2 expression ->
                 FunctionDeclaration(Function(functor, args, expression))
        | None ->
            PredicateDeclaration (Predicate (functor, args, SimpleGoal ("true", Array.empty)))

// Declarations

(*
partition([], _, [], []).
partition([X|Xs], Pivot, Smalls, Bigs) :-
    (   X @< Pivot ->
        Smalls = [X|Rest],
        partition(Xs, Pivot, Rest, Bigs)
    ;   Bigs = [X|Rest],
        partition(Xs, Pivot, Smalls, Rest)
    ).

quicksort([])     --> [].
quicksort([X|Xs]) -->
    { partition(Xs, X, Smaller, Bigger) },
    quicksort(Smaller), [X], quicksort(Bigger).
*)

// Support destructuring lists in a predicate's definition.

(*
maplist(_, [], []).
maplist(P, [X|Xs], [Y|Ys]) :-
   call(P, X, Y),
   maplist(P, Xs, Ys).
*)

// Scripts

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
    match run expression text with
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
   