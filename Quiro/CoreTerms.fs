module Quiro.CoreTerms

open System
open Quiro.Interpreter.Internal
open Quiro.TermHelpers

let create terms =
    let addPred = addPred terms
    
    addPred ("=", 2) (fun context args ->
        match args with
        | [ a; b ] ->
            unify a b
            |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
        | _ -> ValueNone
    )
    addPred ("\=", 2) (fun context args ->
        match args with
        | [ a; b ] ->
            unify a b
            |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
            |> function
                | ValueSome _ -> ValueNone
                | ValueNone -> emptySuccess context
        | _ -> ValueNone
    )
    
    addPred ("==", 2) (fun context args ->
        match args with
        | [ a; b ] -> wrap context (a = b)
        | _ -> ValueNone
    )
    addPred ("\==", 2) (fun context args ->
        match args with
        | [ a; b ] -> wrap context (a <> b)
        | _ -> ValueNone
    )
    
    addPred ("=:=", 2) (fun context args ->
        match args with
        | [ a; b ] ->
            let evaluatedA = evaluateExpr context a
            let evaluatedB = evaluateExpr context b
            
            wrap context (evaluatedA = evaluatedB)
        | _ -> ValueNone
    )
    addPred ("\=:=", 2) (fun context args ->
        match args with
        | [ a; b ] ->
            let evaluatedA = evaluateExpr context a
            let evaluatedB = evaluateExpr context b

            wrap context (evaluatedA <> evaluatedB)
        | _ -> ValueNone
    )
    
    describe "is" "A is B" "Evaluates the right hand side and either assigns it to the left or checks structural equality."
    addPred ("is", 2) (fun context args ->
        match args with
        | [ left; right ] ->
            let evaluatedRight = evaluateExpr context right

            if hasFreeVariables left then
                unify left evaluatedRight
                |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
            else
                wrap context (left = evaluatedRight)
            
        | _ -> ValueNone
    )
    
    describe "convert" "convert(+In, -Out) / convert(-In, +Out)" "Performs explicit conversion between one value type and another."
    addPred ("convert", 2) (fun context args ->
        match args with
        | [ Eval context left; Eval context right ] ->
            let freeL = hasFreeVariables left
            let freeR = hasFreeVariables right
            
            if freeL && freeR then ValueNone
            else
                let before, after = if freeL then right, left else left, right
                
                seq {
                    match evaluateExpr context before with
                    | Negation _
                    | Conjunction _
                    | Disjunction _
                    | ListCons _
                    | Variable _ -> Text (Term.toString before)
         
                    | Atom atom ->
                        Text atom
                        Term (atom, [])

                        if atom = "nan" then Number Double.NaN
                        if atom = "+infinity" then Number Double.PositiveInfinity
                        if atom = "-infinity" then Number Double.NegativeInfinity
                    
                    | Number num ->
                        let str = string num
                        let rec getDigits (digits: float list) number =
                            if number = 0.0 then
                                digits
                            elif number < 0.0 then
                                getDigits [] -number
                            else
                                let digit = number % 10.0
                                getDigits (digit :: digits) ((number - digit) / 10.0)

                        Text str

                        if Double.IsNaN num then Atom "nan"
                        elif Double.IsPositiveInfinity num then Atom "infinity"
                        elif not (Double.IsNegativeInfinity num) && Double.IsInteger num then
                            getDigits [] num
                            |> List.map Number
                            |> ListTerm
                            
                    | Text t ->
                        match Double.TryParse t with
                        | true, v -> Number v
                        | false, _ -> ()
                        
                        Atom t
                        ListTerm (t.ToCharArray() |> Array.map (string >> Text) |> Array.toList)
                        
                    | ListTerm items ->
                        if items |> List.forall _.IsText then
                            items
                            |> List.map (function | Text t -> t | _ -> "")
                            |> String.concat ""
                            |> Text
                        elif items |> List.forall _.IsNumber then
                            items
                            |> List.map (function | Number n -> n | _ -> 0.0)
                            |> List.fold (fun sum next ->
                                (sum * (10.0 ** (floor (log10 next) + 1.0))) + next
                            ) 0.0
                            |> Number
                            
                    | Term (functor, args) ->
                        if args.Length = 0 then Atom functor
                }
                |> Seq.chooseV (unify after >> ValueOption.map (fun frame -> frame, context.substitutions))
                |> Seq.noneIfEmpty

        | _ -> ValueNone
    )