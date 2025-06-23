module Quiro.TermHelpers

open System
open System.Collections.Generic
open Quiro.Interpreter.Internal

let pred (f: InterpreterContext -> Term list -> Map<string * int, Term> seq voption) = f
let inline emptySuccess context: ((Var * Term)[] * (Var * Term)[]) seq voption = ValueSome [| Array.empty, context.substitutions |]
let inline wrap context test: ((Var * Term)[] * (Var * Term)[]) seq voption =
    if test then ValueSome [| Array.empty, context.substitutions |] else ValueNone

let private intMaxValue = float Int32.MaxValue
let private intMinValue = float Int32.MinValue

let (|IntNumber|_|) (number: Double) =
    if Double.IsNaN number then ValueNone
    elif number > intMaxValue then ValueSome Int32.MaxValue
    elif number < intMinValue then ValueSome Int32.MinValue
    elif Double.IsInteger number then ValueSome (int number)
    else ValueNone

let func (f: InterpreterContext -> Term list -> Term voption) = f
let mathFunc op = func(fun context args ->
    match args with
    | [ a; b ] ->
        let evA = evaluateExpr context a
        let evB = evaluateExpr context b
        
        match evA, evB with
        | Number a, Number b -> Number (op a b)
        | _ -> Atom "nil"
    
    | _ -> Atom "nil"
    |> ValueSome
)

let (|Eval|) context value = evaluateExpr context value
let (|HasFreeVars|_|) term =
    if hasFreeVariables term then ValueSome term else ValueNone
let (|NoFreeVars|_|) term =
    if hasFreeVariables term then ValueNone else ValueSome term

let addPred terms key handler =
    let backing =
        let mutable result = Unchecked.defaultof<ResizeArray<_>>
        
        if not (terms.nativePredicates.TryGetValue(key, &result)) then
            result <- ResizeArray()
            terms.nativePredicates.Add(key, result)

        result

    backing.Add handler
let addFunc terms key handler =
    let backing =
        let mutable result = Unchecked.defaultof<ResizeArray<_>>
        
        if not (terms.functions.TryGetValue(key, &result)) then
            result <- ResizeArray()
            terms.functions.Add(key, result)

        result

    backing.Add handler

let internal describeTable = Dictionary<string, ResizeArray<string * string>>()
let describe term signature description =
    let mutable container = Unchecked.defaultof<ResizeArray<string * string>>
    
    if not (describeTable.TryGetValue(term, &container)) then
        container <- ResizeArray()
        describeTable[term] <- container

    container.Add(signature, description)
    
let internal varArgs = HashSet<string>()
let allowVarArgs term = varArgs.Add term |> ignore