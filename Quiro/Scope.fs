module Quiro.Scope

open System
open ExtendedNumerics
open Microsoft.FSharp.Collections
open Microsoft.FSharp.Core
open Quiro.DataTypes
open Quiro.Interpreter

let rec evalArgs (context: Context) args : Expression list list =
    match args with
    | [] -> [ [] ]
    | arg :: args ->
        let arg = Internal.evaluateExpr {
            depth = context.depth + 1
            trace = context.trace
            
            expression = arg
            scope = context.scope
            
            seenGoals = context.seenGoals
            seenExpressions = context.seenExpressions
            stack = (NativeFunction "," :: context.stack)
        }
        
        arg
        |> List.map (fun (value, bindings) ->
            let scope = {
                context.scope with
                    values = Map.merge context.scope.values bindings 
            }
            let context = { context with scope = scope }
            
            evalArgs context args
            |> List.map (fun argSet -> value :: argSet)
        )
        |> List.collect id

// Native Predicates

let private makePred (handler : _ -> Map<string, Expression> list option) context args : Map<string, Expression> list option =
    evalArgs context (Array.toList args)
    |> List.choose handler
    |> List.noneOnEmpty
    |> Option.map (List.collect id)

let print = makePred (function
    | [ Variable name ] ->
        let value =
            Console.ReadLine().ToCharArray()
            |> Array.map (int >> BigDecimal >> Float >> Number)
            |> Array.toList
            |> ListTerm

        Some [ (Map.ofList [ (name, value) ]) ]
    
    | [ value ] ->
        match value with
        | ListTerm values when values |> List.forall(function | Number (Float v) -> v.DecimalPlaces = 0 | _ -> false) ->
            values
            |> List.map (function
                | Number (Float v) -> char v.WholeValue
                | _ -> ' '
            )
            |> List.toArray
            |> String
            |> Console.WriteLine

        | _ ->
            Console.WriteLine (Expression.toString value)

        Some [ Map.empty ]
    | _ ->
        None
)

let nl _ _ =
    Console.WriteLine()
    Ok (Some Seq.empty)

let lessThan = mathPred "<" (<)
let lessThanOrEqual = mathPred "<=" (<=)
let greaterThan = mathPred ">" (>)
let greaterThanOrEqual = mathPred ">=" (>=)

let exprEqual (_: Context) (args: Expression[]) =
    match args with
    | [| a; b |] ->
        if a = b then Some [] else None
    | _ -> None
let valEqual = makePred (function
    | [ a; b ] ->
        if a = b then Some [ Map.empty  ] else None
    | _ -> None
)

// Native Functions

let private makeFunc (handler: Expression list -> Expression option) (context: Context) args =
    evalArgs context (Array.toList args)
    |> List.choose handler
    |> List.noneOnEmpty
let private mathFunc handler =
    makeFunc (function
        | [ Number a; Number b ] -> Some (Number (handler a b))
        | _ -> None
    )

let unify = makeFunc (List.last >> Some)

let add = mathFunc (+)
let subtract = mathFunc (-)
let multiply = mathFunc (*)
let divide = mathFunc (/)

let modOp = mathFunc (_.Modulus)
let remainder = mathFunc (%)

let exponentiation = mathFunc _.Pow

let defaultScope = {
   parent = None
   values = Map.ofArray [|
       "nan", Number NaN
       "infinity", Number (Infinity true)
   |]

   predicates = Map.empty
   nativePredicates = Map.ofArray [|
       ("print", 1), [ print ]
       ("nl", 0), [ nl ]
       
       ("<", 2), [ lessThan ]
       ("<=", 2), [ lessThanOrEqual ]
       (">", 2), [ greaterThan ]
       (">=", 2), [ greaterThanOrEqual ]
       ("=", 2), [ exprEqual ]
       ("=:=", 2), [ valEqual ]
       ("is", 2), [ isOp ]
   |]
   
   functions = Map.empty
   nativeFunctions = Map.ofArray [|
       (",", 2), [ unify ]
       
       ("+", 2), [ add ]
       ("-", 2), [ subtract ]
       
       ("*", 2), [ multiply ]
       ("/", 2), [ divide ]
       ("div", 2), [ divide ]
       ("mod", 2), [ modOp ]
       ("rem", 2), [ remainder ]
       
       ("**", 2), [ exponentiation ]
       ("^", 2), [ exponentiation ]
   |] 
}