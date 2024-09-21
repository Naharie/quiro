module Quiro.Scope

open System
open System.Linq.Expressions
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
    Some [ Map.empty ]

let private one = Float BigDecimal.One

let lessThan (context: Context) (args: Expression[]) =
    let badUsage() = invalidOp "Can't use the < predicate on non numbers"
    
    match args with
    | [| Variable _; Variable _ |] -> raise (InsufficientSubstantiationException("<", context.stack))
    
    | [| Variable a; b |] ->
        let b =
            Internal.evaluateExpr {
                depth = context.depth + 1
                trace = context.trace
                
                expression = b
                scope = context.scope
                
                seenGoals = context.seenGoals
                seenExpressions = context.seenExpressions
                stack = (NativePredicate "<" :: context.stack) 
            }
            
        b
        |> List.collect (fun (b, bindings) ->
            match b with
            | Number b ->
                match b with
                | Range(l, _) ->
                    bindings
                    |> Map.add a (Number (Range(Infinity false, l + one)))
                    |> List.singleton
                | _ ->
                    b
                    |> Seq.map (fun v ->
                        bindings
                        |> Map.add a (Number (Range(Infinity false, Float (v - BigDecimal.One))))
                    )
                    |> Seq.toList
            | _ -> badUsage()
        )
        |> Some

    | [| a; Variable b |] ->
        let a = Internal.evaluateExpr {
            depth = context.depth + 1
            trace = context.trace
            
            expression = a
            scope = context.scope
            
            seenGoals = context.seenGoals
            seenExpressions = context.seenExpressions
            stack = (NativePredicate "<" :: context.stack) 
        }
        
        a
        |> List.collect (fun (a, bindings) ->
            match a with
            | Number a ->
                match a with
                | Range(_, h) ->
                    bindings
                    |> Map.add b  (Number (Range(h + one, Infinity true)))
                    |> List.singleton

                | _ ->
                    a
                    |> Seq.map (fun v ->
                        bindings
                        |> Map.add b (Number (Range(Float (v + BigDecimal 1), Infinity true)))
                    )
                    |> Seq.toList

            | _ -> badUsage()
        )
        |> Some
    
    | [| a; b |] ->
        let a = Internal.evaluateExpr {
            depth = context.depth + 1
            trace = context.trace
            
            expression = a
            scope = context.scope
            
            seenGoals = context.seenGoals
            seenExpressions = context.seenExpressions
            stack = (NativePredicate "<" :: context.stack) 
        }
        
        a
        |> List.choose (fun (a, bindingsA) ->
            let b = Internal.evaluateExpr {
                depth = context.depth + 1
                trace = context.trace
                
                expression = b
                scope = { emptyScope with parent = Some context.scope; values = bindingsA }
                
                seenGoals = context.seenGoals
                seenExpressions = context.seenExpressions
                stack = (NativePredicate "<" :: context.stack) 
            }
            
            b
            |> List.choose (fun (b, bindingsB) ->
                if a < b then Some (Map.merge bindingsA bindingsB) else None
            )
            |> List.noneOnEmpty
        )
        |> List.collect id
        |> List.noneOnEmpty
    | _ -> None

//let lessThanOrEqual = mathPred "<=" (<=)
//let greaterThan = mathPred ">" (>)
//let greaterThanOrEqual = mathPred ">=" (>=)

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

let isOp (context: Context) (args: Expression[]) =
    match args with
    | [| left; right |] ->
        let right = Internal.evaluateExpr {
            depth = context.depth + 1
            trace = context.trace
            
            scope = context.scope
            
            expression = right
            
            seenGoals = context.seenGoals
            seenExpressions = context.seenExpressions
            stack = (NativePredicate "is" :: context.stack) 
        }
        
        match left with
        | Variable name ->
            match Scope.lookupValue name context.scope with
            | Some leftVal ->
                right
                |> List.choose (fun (rightVal, rightBindings) ->
                    if leftVal = rightVal then Some rightBindings else None
                )
                |> Some
                
            | None ->
                right
                |> List.map (fun (rightVal, rightBindings) ->
                    rightBindings
                    |> Map.add name rightVal
                )
                |> Some
        
        | _ ->
            right
            |> List.choose (fun (rightVal, rightBindings) ->
                if left = rightVal then Some rightBindings else None
            )
            |> Some
    
    | _ -> None

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
       //("<=", 2), [ lessThanOrEqual ]
       //(">", 2), [ greaterThan ]
       //(">=", 2), [ greaterThanOrEqual ]
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