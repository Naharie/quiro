module Quiro.Terms

(*
// Native Predicates

let private makePred (handler : _ -> Map<string, PrologExpression> list option) context args : Map<string, PrologExpression> list option =
    evalArgs context args
    |> List.choose handler
    |> List.noneIfEmpty
    |> Option.map (List.collect id)

let println = makePred (function
    | [ Variable name ] ->
        let value = Text (Console.ReadLine())
        Some [ (Map.ofList [ (name, value) ]) ]
    
    | [ Text text ] ->
        Console.WriteLine text
        Some [ Map.empty ]
    
    | [ value ] ->
        Console.WriteLine (PrologExpression.toString value)
        Some [ Map.empty ]
    | _ ->
        None
)

let print = makePred (function
    | [ Variable name ] ->
        let value = Console.Read() |> char |> string |> Text
        Some [ (Map.ofList [ (name, value) ]) ]

    | [ Text text ] ->
        Console.Write text
        Some [ Map.empty ]
    
    | [ value ] ->
        Console.Write (PrologExpression.toString value)
        Some [ Map.empty ]
    | _ ->
        None
)

let nl _ _ =
    Console.WriteLine()
    Some [ Map.empty ]

let private one = Float BigDecimal.One
let private mathCompPred name (leftVar: Number -> PrologExpression list) (rightVar: Number -> PrologExpression list) concrete (context: InterpreterContext) args =
    let badUsage() = invalidOp $"Can't use the %s{name} predicate on non numbers"
    
    evalArgs context args
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
    |> List.noneIfEmpty

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

let exprEqual (_: InterpreterContext) (args: PrologExpression list) =
    match args with
    | [ a; b ] ->
        if a = b then Some [] else None
    | _ -> None
let valEqual = makePred (function
    | [ a; b ] ->
        if a = b then Some [ Map.empty  ] else None
    | _ -> None
)

let isOp (context: InterpreterContext) (args: PrologExpression list) =
    match args with
    | [ left; right ] ->
        let right = evaluateExpression (right, {
            context with
                depth = context.depth + 1
                stack = (NativePredicate "is" :: context.stack) 
        })
        
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

let private makeFunc (handler: PrologExpression list -> PrologExpression option) (context: InterpreterContext) args =
    evalArgs context args
    |> List.choose handler
    |> List.noneIfEmpty
let private mathFunc handler =
    makeFunc (function
        | [ Number a; Number b ] -> Some (Number (handler a b))
        | _ -> None
    )

let unify = makeFunc (fun args ->
    let areAllArgsLists = args |> List.forall (function | ListTerm _ -> true | _ -> false)
    
    if areAllArgsLists then
        args
        |> List.collect (function | ListTerm values -> values | _ -> [])
        |> ListTerm
        |> Some
    else
        Some (ListTerm args)
)

let add = mathFunc (+)
let subtract = mathFunc (-)
let multiply = mathFunc (*)
let divide = mathFunc (/)

let modOp = mathFunc (_.Modulus)
let remainder = mathFunc (%)

let exponentiation = mathFunc _.Pow

let defaultScope = {
   values = Map.ofArray [|
       "nan", Number NaN
       "infinity", Number (Infinity true)
   |]

   predicates = Map.ofArray [|
       
       
   |]
   
   nativePredicates = Map.ofArray [|
       ("println", 1), [ println ]
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
*)

()