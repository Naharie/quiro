module Quiro.Parser.Internal

open System
open FParsec
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

let termAST parser =
    pos .>>. parser |>> fun (location, kind) ->
        { termKind = kind; location = location }
let dcgAST parser =
    pos .>>. parser |>> fun (location, kind) ->
        { dcgKind = kind; location = location }

// Expressions

let invalidAtomSymbols = Set.ofList [ '['; ']'; '('; ')'; '{'; '}'; ','; ';'; '.'; '?'; '|'  ]
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
        
    let atomTerm: _ Parser = termAST (atomParser |>> ExprAtom) <?> "atom"

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
                + (match exponent with
                   | Some exponent -> "E" + exponent
                   | None -> ""
                )
                
            match Double.TryParse numberText with
            | true, result -> ExprNumber result
            | false, _ -> failwith "Invalid number literal"
        )
    <|> stringReturn "nan" (ExprNumber nan)
    <|> stringReturn "infinity" (ExprNumber infinity)
    |> termAST

let textExpr: _ Parser =
    let quote = skipChar '"'
    let unescapedChar = noneOf [ '\\'; '"' ]
    let escapedChar =
        skipChar '\\' >>. choice [
            charReturn '\\' '\\'
            charReturn '"' '"'
            charReturn 't' '\t'
            charReturn 'r' '\r'
            charReturn 'n' '\n'
        ]

    between quote quote (manyChars (unescapedChar <|> escapedChar))
    |>> ExprText
    <?> "string"
    |> termAST

let term, termRef = createParserForwardedToRef() : Parser<TermAST> * Parser<TermAST> ref

let placeholder : _ Parser =
    eof <|> lookAhead (newline .>>. newline |>> ignore) >>= allowIfLanguageServer
let placeholderExpr = placeholder >>. preturn ExprPlaceholder |> termAST

let variableExpr, variableParser =
    let headChar = upper <|> pchar '_'
    let bodyChar = letter <|> digit
    
    let variableParser: _ Parser =
        headChar .>>. manyChars bodyChar
        |>> fun (head, body) -> (string head) + body

    let variableExpression =
        variableParser |>> ExprVariable <?> "variable"
        |> termAST
    
    variableExpression, variableParser

let listParser, listExpression: _ Parser * _ Parser =
    let startList = skipChar '['
    let endList = (skipChar ']' <|> placeholder)
    let separator = skipChar ','
    
    let listParser =
        between startList endList (sepBy term separator)
        <?> "list"
    
    listParser, termAST (listParser |>> ExprListTerm)

let listConsExpr: _ Parser =
    skipChar '[' >>. ws >>. term .>> ws .>> skipChar '|' .>> ws .>>. term .>> ws .>> (skipChar ']' <|> placeholder)
    |>> ExprListCons
    <?> "list cons"
    |> termAST

let termOrAtom: _ Parser =
    let startArgs = skipChar '('
    let endArgs = (skipChar ')' <|> placeholder)
    let separator = skipChar ','
    
    atomParser .>>. opt (between startArgs endArgs (sepBy term separator))
let termOrAtomExpr: _ Parser =
    termOrAtom
    |>> fun (functor, args) ->
        match args with
        | Some args -> ExprTerm(functor, args)
        | None -> ExprAtom functor
    |> termAST

let parenExpr = skipChar '(' >>. ws >>. term .>> ws .>> (skipChar ')' <|> placeholder)

let expression = OperatorPrecedenceParser<TermAST, FileLocation, unit>()

let addExpressionOperators (operatorExpression: OperatorPrecedenceParser<TermAST, FileLocation, unit>) =
    let opPos name =
        getPosition
        |>> fun streamPos ->
            {
                file = streamPos.StreamName
                index = streamPos.Index - int64 (String.length name)
                line = streamPos.Line
                column = streamPos.Column - int64 (String.length name)
            }
    
    let op name precedence =
        operatorExpression.AddOperator(InfixOperator(name, opPos name, precedence, Associativity.Left, (), fun pos a b ->
            { termKind = ExprTerm(name, [ a; b ]); location = pos }
        ))
    
    op "+" 200
    op "-" 200

    op "*" 300
    op "/" 300
    op "div" 300
    op "mod" 300
    op "rem" 300

    operatorExpression.AddOperator(PrefixOperator("-", opPos "-", 400, false, (), fun pos v ->
        { termKind = ExprTerm("-", [ v ]); location = pos }
    ))
    
    op "**" 500
    op "^" 500


expression.TermParser <- ws >>. choice [
    parenExpr
    textExpr
    numberExpr
    (attempt listConsExpr <|> listExpression)
    variableExpr
    termOrAtomExpr
    placeholderExpr
] .>> ws

addExpressionOperators expression

termRef.Value <- expression.ExpressionParser

// Goals

let goal, goalRef = createParserForwardedToRef() : Parser<TermAST> * Parser<TermAST> ref

let comparisonGoal: _ Parser =
    pipe3
        term
        (choice [
            pstring "<"
            pstring "<="
            pstring ">"
            pstring ">="
            (attempt (pstring "=:=") <|> pstring "=")
            pstring "\="
            pstring "is"
        ]) term
        (fun exprA op exprB -> ExprTerm(op, [ exprA; exprB ]))
    |> termAST
let simpleGoal: _ Parser =
    termOrAtom
    |>> fun (functor, args) ->
        ExprTerm(functor, args |> Option.defaultValue List.empty)
    |> termAST
let negatedGoal: _ Parser =
    skipString "\+" .>> ws >>. goal
    |>> ExprNegation
    |> termAST

let junctionGoal = OperatorPrecedenceParser<TermAST, unit, unit>()

junctionGoal.AddOperator(InfixOperator(",", ws, 1100, Associativity.Left, fun a b ->
    {
        termKind =
            match a.termKind with
            | ExprConjunction parts ->
                ExprConjunction (Array.append parts [| b |])
            | _ ->
                ExprConjunction([| a; b |])
        location = a.location
    }
))
junctionGoal.AddOperator(InfixOperator(";", ws, 1000, Associativity.Left, fun a b ->
    {
        termKind =
            match a.termKind with
            | ExprDisjunction parts ->
                ExprDisjunction (Array.append parts [| b |])
            | _ ->
                ExprDisjunction ([| a; b |])
        location = a.location
    }
))

junctionGoal.TermParser <- (choice [
    (skipChar '(' >>. goal .>> skipChar ')')
    negatedGoal
    (attempt comparisonGoal)
    simpleGoal
    placeholderExpr
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
    ws >>. pos .>>. termOrAtom .>> ws .>>. opt (choice [
        skipString ":-" >>. ws >>. goal |>> Choice1Of2
        skipString "-->" >>. ws >>. dcg |>> Choice2Of2
    ]) .>> ws .>> skipChar '.' .>> ws
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
                termKind = ExprAtom "true"
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