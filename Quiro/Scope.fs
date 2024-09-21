module Quiro.Scope

open System
open System.Linq.Expressions
open ExtendedNumerics
open Microsoft.FSharp.Collections
open Microsoft.FSharp.Core
open Quiro.DataTypes
open Quiro.Interpreter

// Native Predicates

let private makePred (handler : _ -> Map<string, Expression> list option) context args : Map<string, Expression> list option =
    Internal.evalArgs context args
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
        | ListTerm values ->
            let isText = values |> List.forall(function | Number (Float v) -> v.DecimalPlaces <= 0 | _ -> false)
            
            if isText then
                values
                |> List.map (function
                    | Number (Float v) -> char v.WholeValue
                    | _ -> ' '
                )
                |> List.toArray
                |> String
                |> Console.WriteLine
            else
                Console.WriteLine (Expression.toString value)

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
let private mathCompPred name (leftVar: Number -> Expression list) (rightVar: Number -> Expression list) concrete context args =
    let badUsage() = invalidOp $"Can't use the %s{name} predicate on non numbers"
    
    Internal.evalArgs context args
    |> List.choose (fun args ->
        match args with
        | [ Variable _; Variable _ ] -> raise (InsufficientSubstantiationException("<", context.stack))
        
        | [ Variable a; b ] ->
            match b with
            | Number b ->
                (leftVar b)
                |> List.map (fun b -> Map.ofList [ a, b ])
            | _ -> badUsage()
            |> Some

        | [ a; Variable b ] ->
            match a with
            | Number a ->
                (rightVar a)
                |> List.map (fun a -> Map.ofList [ b, a ])
            | _ -> badUsage()
            |> Some
        
        | [ a; b ] ->
            if concrete a b then Some [ Map.empty ] else None
        | _ -> None
    )
    |> List.collect id
    |> List.noneOnEmpty

let lessThan =
        mathCompPred "<"
            (fun b ->
                match b with
                | Range(l, _) ->
                    [ Number (Range(Infinity false, l + one)) ]
                | _ ->
                    b
                    |> Seq.map (fun v ->
                        Number (Range(Infinity false, Float (v - BigDecimal.One)))
                    )
                    |> Seq.toList
            )
            (fun a ->
                match a with
                | Range(_, h) ->
                    [ Number (Range(h + one, Infinity true)) ]

                | _ ->
                    a
                    |> Seq.map (fun v ->
                        Number (Range(Float (v + BigDecimal.One), Infinity true))
                    )
                    |> Seq.toList
            )
            (<)
let lessThanOrEqual =
        mathCompPred "<="
            (fun b ->
                match b with
                | Range(l, _) ->
                    [ Number (Range(Infinity false, l)) ]
                | _ ->
                    b
                    |> Seq.map (fun v -> Number (Range(Infinity false, Float v)))
                    |> Seq.toList
            )
            (fun a ->
                match a with
                | Range(_, h) ->
                    [ Number (Range(h, Infinity true)) ]

                | _ ->
                    a
                    |> Seq.map (fun v -> Number (Range(Float v, Infinity true)))
                    |> Seq.toList
            )
            (<=)

let greaterThan =
        mathCompPred ">"
            (fun b ->
                match b with
                | Range(_, h) ->
                    [ Number (Range(Infinity false, h + one)) ]
                | _ ->
                    b
                    |> Seq.map (fun v -> Number (Range(Float (v + BigDecimal.One), Infinity true)))
                    |> Seq.toList
            )
            (fun a ->
                match a with
                | Range(_, h) ->
                    [ Number (Range(Infinity false, h - one)) ]
                | _ ->
                    a
                    |> Seq.map (fun v -> Number (Range(Infinity false, Float (v - BigDecimal.One))))
                    |> Seq.toList
            )
            (>)
let greaterThanOrEqual =
        mathCompPred ">="
            (fun b ->
                match b with
                | Range(_, h) ->
                    [ Number (Range(Infinity false, h)) ]
                | _ ->
                    b
                    |> Seq.map (fun v -> Number (Range(Float v, Infinity true)))
                    |> Seq.toList
            )
            (fun a ->
                match a with
                | Range(_, h) ->
                    [ Number (Range(Infinity false, h)) ]
                | _ ->
                    a
                    |> Seq.map (fun v -> Number (Range(Infinity false, Float v)))
                    |> Seq.toList
            )
            (>=)

let exprEqual (_: Context) (args: Expression list) =
    match args with
    | [ a; b ] ->
        if a = b then Some [] else None
    | _ -> None
let valEqual = makePred (function
    | [ a; b ] ->
        if a = b then Some [ Map.empty  ] else None
    | _ -> None
)

let isOp (context: Context) (args: Expression list) =
    match args with
    | [ left; right ] ->
        let right = Internal.evaluateExpr {
            depth = context.depth + 1
            trace = context.trace
            
            scope = context.scope
            
            expression = right
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
    Internal.evalArgs context args
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