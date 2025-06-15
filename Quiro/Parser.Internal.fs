module Quiro.Parser.Internal

open System
open System.Numerics
open ExtendedNumerics
open FParsec
open Quiro
open Quiro.AST

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

let mutable isLanguageServerMode = true
let allowIfLanguageServer v = if isLanguageServerMode then preturn v else pzero

let ws, ws1 = opt spaces |>> ignore, spaces1
let pos = getPosition |>> fun pos -> {
    file = pos.StreamName
    index = pos.Index
    line = pos.Line
    column = pos.Column
}
let maybe parser = (parser >>% true) <|>% false

let exprAST parser =
    pos .>>. parser |>> fun (location, kind) ->
        { exprKind = kind; location = location }
let goalAST parser =
    pos .>>. parser |>> fun (location, kind) ->
        { goalKind = kind; location = location }
let dcgAST parser =
    pos .>>. parser |>> fun (location, kind) ->
        { dcgKind = kind; location = location }

// Expressions

let invalidAtomSymbols = Set.ofList [ '['; ']'; '('; ')'; '{'; '}'; ','; ';'; '.'; '?'  ]
let atomExpr, atomParser =    
    let isSymbol char = Char.IsSymbol char || Char.IsPunctuation char
    let symbols allowUnderScore = satisfy (fun char -> isSymbol char && (allowUnderScore || char <> '_') && (invalidAtomSymbols |> Set.contains char |> not))

    let headChar = lower <|> symbols false
    let bodyChar = letter <|> symbols true <|> digit
    
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
        
    let atomTerm: _ Parser = exprAST (atomParser |>> ExprAtom) <?> "atom"

    (atomTerm, atomParser)

let numberExpr: _ Parser =
    pipe4
        (maybe (skipChar '-'))
        (many1Chars digit)
        (opt (attempt (skipChar '.' >>. many1Chars digit)))
        (opt (skipChar 'E' >>. many1Chars digit) <?> "number")
        (fun isNegative integerPart fractionalPart exponent ->
            let numberText =
                (if isNegative then "-" else "")
                + integerPart
                + (match fractionalPart with
                   | Some fraction -> "." + fraction
                   | None -> ""
                )
            let baseNumber = BigDecimal.Parse numberText
            let exponent =
                match exponent with
                | Some exponent -> BigInteger.Parse exponent
                | None -> BigInteger.One
            let number = BigDecimal.Pow(baseNumber, exponent)

            ExprNumber (BigFloat.Decimal number)
        )
    |> exprAST

let textExpr: _ Parser =
    let quote = skipChar '"'
    let unescapedChar = noneOf [ '\\'; '"' ]
    let escapedChar = skipChar '\\' >>. anyOf [ '\\'; '"' ]
    
    between quote quote (manyChars (unescapedChar <|> escapedChar))
    |>> ExprText
    <?> "string"
    |> exprAST

let expr, exprRef = createParserForwardedToRef() : Parser<PrologExprAST> * Parser<PrologExprAST> ref

let placeholder : _ Parser =
    eof <|> lookAhead (newline .>>. newline |>> ignore) >>= allowIfLanguageServer
let placeholderExpr = placeholder >>. preturn ExprPlaceholder |> exprAST
let placeholderGoal = placeholder >>. preturn GoalPlaceholder |> goalAST

let variableExpr, variableParser =
    let headChar = upper <|> pchar '_'
    let bodyChar = letter <|> digit
    
    let variableParser: _ Parser =
        headChar .>>. manyChars bodyChar
        |>> fun (head, body) -> (string head) + body

    let variableExpression =
        variableParser |>> ExprVariable <?> "variable"
        |> exprAST
    
    variableExpression, variableParser

let listParser, listExpression: _ Parser * _ Parser =
    let startList = skipChar '['
    let endList = (skipChar ']' <|> placeholder)
    let separator = skipChar ','
    
    let listParser =
        between startList endList (sepBy expr separator)
        <?> "list"
    
    listParser, exprAST (listParser |>> ExprListTerm)

let listConsExpr: _ Parser =
    skipChar '[' >>. ws >>. expr .>> ws .>> skipChar '|' .>> ws .>>. expr .>> ws .>> (skipChar ']' <|> placeholder)
    |>> ExprListCons
    <?> "list cons"
    |> exprAST

let termOrAtom: _ Parser =
    let startArgs = skipChar '('
    let endArgs = (skipChar ')' <|> placeholder)
    let separator = skipChar ','
    
    atomParser .>>. opt (between startArgs endArgs (sepBy expr separator))
let termOrAtomExpr: _ Parser =
    termOrAtom
    |>> fun (functor, args) ->
        match args with
        | Some args -> ExprTerm(functor, args)
        | None -> ExprAtom functor
    |> exprAST

let goal, goalRef = createParserForwardedToRef() : Parser<PrologGoalAST> * Parser<PrologGoalAST> ref

let parenExpr = skipChar '(' >>. ws >>. expr .>> ws .>> (skipChar ')' <|> placeholder)

let expression = OperatorPrecedenceParser<PrologExprAST, FileLocation, unit>()

let addExpressionOperators (operatorExpression: OperatorPrecedenceParser<PrologExprAST, FileLocation, unit>) =
    let op name precedence =
        let opPos =
            getPosition
            |>> fun streamPos ->
                {
                    file = streamPos.StreamName
                    index = streamPos.Index - int64 (String.length name)
                    line = streamPos.Line
                    column = streamPos.Column - int64 (String.length name)
                }

        operatorExpression.AddOperator(InfixOperator(name, opPos, precedence, Associativity.Left, (), fun pos a b ->
            { exprKind = ExprTerm(name, [ a; b ]); location = pos }))
    
    op "+" 200
    op "-" 200

    op "*" 300
    op "/" 300
    op "div" 300
    op "mod" 300
    op "rem" 300

    op "**" 400
    op "^" 400

expression.TermParser <- ws >>. choice [
    parenExpr
    variableExpr
    termOrAtomExpr
    numberExpr
    textExpr
    (attempt listConsExpr <|> listExpression)
    placeholderExpr
] .>> ws

addExpressionOperators expression

exprRef.Value <- expression.ExpressionParser

// Goals

let comparisonGoal: _ Parser =
    pipe3
        expr
        (choice [
            pstring "<"
            pstring "<="
            pstring ">"
            pstring ">="
            (attempt (pstring "=:=") <|> pstring "=")
            pstring "\="
            pstring "is"
        ]) expr
        (fun exprA op exprB -> GoalSimple(op, [ exprA; exprB ]))
    |> goalAST
let simpleGoal: _ Parser =
    termOrAtom
    |>> fun (functor, args) ->
        GoalSimple(functor, args |> Option.defaultValue List.empty)
    |> goalAST
let negatedGoal: _ Parser =
    skipString "\+" .>> ws >>. goal
    |>> GoalNegated
    |> goalAST

let junctionGoal = OperatorPrecedenceParser<PrologGoalAST, unit, unit>()

junctionGoal.AddOperator(InfixOperator(",", ws, 1100, Associativity.Left, fun a b ->
    {
        goalKind =
            match a.goalKind with
            | GoalConjunction parts ->
                GoalConjunction (Array.append parts [| b |])
            | _ ->
                GoalConjunction([| a; b |])
        location = a.location
    }
))
junctionGoal.AddOperator(InfixOperator(";", ws, 1000, Associativity.Left, fun a b ->
    {
        goalKind =
            match a.goalKind with
            | GoalDisjunction parts ->
                GoalDisjunction (Array.append parts [| b |])
            | _ ->
                GoalDisjunction([| a; b |])
        location = a.location
    }
))

junctionGoal.TermParser <- (choice [
    (skipChar '(' >>. goal .>> skipChar ')')
    negatedGoal
    (attempt comparisonGoal)
    simpleGoal
    placeholderGoal
])

goalRef.Value <- junctionGoal.ExpressionParser

let dcg, dcgRef = createParserForwardedToRef(): Parser<DCGAST> * Parser<DCGAST> ref

let dcgCallOrTerm =
    termOrAtom
    |>> fun (term, potentialArgs) ->
        match potentialArgs with
        | None -> DCGTerm term
        | Some args ->
            DCGCall(term, args)
    |> dcgAST

let dcgGoal =
    skipChar '{' >>. ws >>. goal .>> ws .>> skipChar '}' |>> DCGGoal
    |> dcgAST
let dcgList = listParser |>> DCGList |> dcgAST
let dcgSequence =
    sepBy1 (ws >>. choice [ dcgList; dcgGoal; dcgCallOrTerm ] .>> ws) (skipChar ',')
    |>> fun terms ->
        if terms.Length = 1 then
            terms[0].dcgKind
        else
            DCGSequence (List.toArray terms)
    |> dcgAST

dcgRef.Value <- dcgSequence

let declaration: _ Parser =
    pos .>>. termOrAtom .>> ws .>>. opt (choice [
        skipString ":-" >>. ws >>. goal |>> Choice1Of2
        skipString "-->" >>. ws >>. dcg |>> Choice2Of2
    ]) .>> ws .>> skipChar '.'
    |>> fun ((position, (functor, args)), body) ->
        let args = args |> Option.defaultValue List.empty

        match body with
        | Some body ->
             match body with
             | Choice1Of2 goal ->
                 PredicateDeclaration(functor, args, goal)
             | Choice2Of2 expression ->
                 DCGDeclaration(functor, args, expression)
        | None ->
            PredicateDeclaration (functor, args, {
                goalKind = GoalSimple ("true", List.empty)
                location = position
            })

let comment: _ Parser = ws >>. skipChar '%' >>. manyChars (noneOf [ '\r'; '\t' ]) .>> ws

let script: _ Parser =
    many1 (choice [
        ws1 >>. preturn BlankLine
        comment |>> Comment
        (pos .>>. declaration)
        |>> fun (pos, kind) ->
            ScriptDeclaration { decKind = kind; location = pos }
    ]) .>> eof
    |>> fun lines ->
        lines
        |> List.choose(function
            | ScriptDeclaration rule -> Some rule
            | _ -> None
        )