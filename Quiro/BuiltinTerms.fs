module Quiro.BuiltinTerms.StoredTerms

open System
open System.Collections.Generic
open ExtendedNumerics
open Functional
open Microsoft.FSharp.Core
open Quiro
open Quiro.Interpreter.Internal
open Quiro.StoredRules

[<AutoOpen>]
module Helpers =
    let pred (f: InterpreterContext -> Term list -> Map<string * int, Term> seq voption) = f
    let inline emptySuccess context: ((Var * Term)[] * (Var * Term)[]) seq voption = ValueSome [| Array.empty, context.substitutions |]
    let inline wrap context test: ((Var * Term)[] * (Var * Term)[]) seq voption =
        if test then ValueSome [| Array.empty, context.substitutions |] else ValueNone
    
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

let defaultTerms() =
    let terms = emptyTerms()
    let addPred key handler =
        let backing =
            let mutable result = Unchecked.defaultof<ResizeArray<_>>
            
            if not (terms.nativePredicates.TryGetValue(key, &result)) then
                result <- ResizeArray()
                terms.nativePredicates.Add(key, result)

            result

        backing.Add handler
    let addFunc key handler =
        let backing =
            let mutable result = Unchecked.defaultof<ResizeArray<_>>
            
            if not (terms.functions.TryGetValue(key, &result)) then
                result <- ResizeArray()
                terms.functions.Add(key, result)

            result

        backing.Add handler

    let describeTable = Dictionary<string, ResizeArray<string * string>>()
    let describe term signature description =
        let mutable container = Unchecked.defaultof<ResizeArray<string * string>>
        
        if not (describeTable.TryGetValue(term, &container)) then
            container <- ResizeArray()
            describeTable[term] <- container

        container.Add(signature, description)
    
    addPred ("describe", 3) (fun context args ->
        match args with
        | [ Atom lookupTerm; Variable signatureVar; Variable descriptionVar ] ->
            match describeTable.TryGetValue lookupTerm with
            | true, container ->
                seq {
                    for signature, description in container do
                        yield [|
                            signatureVar, (Text signature)
                            descriptionVar, (Text description)
                        |], context.substitutions
                }
                |> Seq.noneIfEmpty
            | false, _ -> ValueNone

        | _ -> ValueNone
    )
    
    let varArgs = HashSet<string>()
    let allowVarArgs term = varArgs.Add term |> ignore
    
    addPred ("@meta", 2) (fun context args ->
        match args with
        | [ Atom term; Atom "var_args" | Term("var_args", []) ] -> wrap context (varArgs.Contains term)
        | _ -> ValueNone
    )

    addFunc ("+", 2) (mathFunc (+))
    addFunc ("-", 2) (mathFunc (-))
    addFunc ("*", 2) (mathFunc (*))
    addFunc ("/", 2) (mathFunc (/))
    
    describe "describe" "describe" "Prints the description(s) of the term to stdout."
    describe "describe" "describe(+Term, -Signature, -Description)" "Provides the signature(s) and description(s) of the given term."

    do
        let term, signature, description = Term.makeVar "Term", Term.makeVar "Signature", Term.makeVar "Description"
        terms.userPredicates[("describe", 1)] <- ResizeArray([|
            [ term ], Conjunction [|
                Term("describe", [ term; signature; description ])
                Term("write", [ signature ])
                Term("write", [ Text " - " ])
                Term("write", [ description ])
                Atom "nl"
            |]
        |])

    describe "nl" "nl" "Prints a newline to stdout."
    addPred ("nl", 0) (fun context _ ->
        Console.WriteLine()
        emptySuccess context
    )
    
    describe "write" "write(?Value)" "Prints a value to stdout or a reads a character from stdin."
    addPred ("write", 1) (fun context args ->
        match args[0] with
        | Variable name ->
            let value = Console.ReadLine()
            ValueSome [| [| name, (Text value) |], context.substitutions |]

        | Text text ->
            Console.Write text
            emptySuccess context

        | value ->
            Console.Write(Term.toString value)
            emptySuccess context
    )

    addPred ("<", 2) (fun context args ->
        match args with
        | [ Eval context a; Eval context b ] ->
            match a, b with
            | Variable a, Number b ->
                ValueSome (seq { for i in b - BigFloat.One.. -BigFloat.One .. BigFloat.NegativeInfinity -> [| a, (Number i) |], context.substitutions })
            | Number a, Variable b ->
                ValueSome (seq { for i in a + BigFloat.One.. BigFloat.One .. BigFloat.PositiveInfinity -> [| b, (Number i) |], context.substitutions })
            | _ -> wrap context (a < b)
        | _ -> ValueNone
    )
    addPred ("<=", 2) (fun context args ->
        match args with
        | [ Eval context a; Eval context b ] ->
            match a, b with
            | Variable a, Number b ->
                ValueSome (seq { for i in b .. -BigFloat.One .. BigFloat.NegativeInfinity -> [| a, (Number i) |], context.substitutions })
            | Number a, Variable b ->
                ValueSome (seq { for i in a .. BigFloat.One .. BigFloat.PositiveInfinity -> [| b, (Number i) |], context.substitutions })
            | _ -> wrap context (a <= b)
        | _ -> ValueNone
    )
     
    addPred (">", 2) (fun context args ->
        match args with
        | [ Eval context a; Eval context b ] ->
            match a, b with
            | Variable a, Number b ->
                ValueSome (seq { for i in b + BigFloat.One.. BigFloat.One .. BigFloat.PositiveInfinity -> [| a, (Number i) |], context.substitutions })
            | Number a, Variable b ->
                ValueSome (seq { for i in a - BigFloat.One.. -BigFloat.One .. BigFloat.NegativeInfinity -> [| b, (Number i) |], context.substitutions })
            | _ -> wrap context (a > b)
        | _ -> ValueNone
    )
    addPred (">=", 2) (fun context args ->
        match args with
        | [ Eval context a; Eval context b ] ->
            match a, b with
            | Variable a, Number b ->
                ValueSome (seq { for i in b .. BigFloat.One .. BigFloat.PositiveInfinity -> [| a, (Number i) |], context.substitutions })
            | Number a, Variable b ->
                ValueSome (seq { for i in a .. -BigFloat.One .. BigFloat.NegativeInfinity -> [| b, (Number i) |], context.substitutions })
            | _ -> wrap context (a >= b)
        | _ -> ValueNone
    )
    
    addPred ("=", 2) (fun context args ->
        match args with
        | [ a; b ] -> wrap context (a = b)
        | _ -> ValueNone
    )
    addPred ("\=", 2) (fun context args ->
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
    
    describe "not" "not(:Pred)" "Negates the success of the given predicate."
    addPred ("not", 1) (fun context args ->
        match args with
        | [ Atom _ | Term _ as pred ] ->
            tryProveGoal context pred  context.substitutions
        | _ -> ValueNone
    )
    
    allowVarArgs "call"
    describe "call" "call(Pred) / call(Pred, A) / call(Pred, A, B) / ..." "Invokes the predicate specified by the first term with the remaining terms as arguments."
    addPred ("call", 1) (fun context args ->
        match args with
        | [ ListTerm (Atom pred :: predArgs) ] ->
            tryProveGoal context (Term (pred, predArgs)) context.substitutions
        | _ -> ValueNone
    )
    
    describe "length" "length(?List, ?Length)" "Determines the length of list, generates a list of a given length, or pairs of lists and lengths."
    addPred ("length", 2) (fun context args ->
        match args with
        | [ a; b ] ->
            let freeA = hasFreeVariables a
            let freeB = hasFreeVariables b

            match freeA, freeB with
            | true, true ->
                seq {
                    for i in 0..Int32.MaxValue do
                        let constructed = ListTerm (List.init i (fun _ -> Atom "nil"))
                        let length = Number (BigFloat.Decimal (BigDecimal i))
                        
                        let results =
                            unify a constructed
                            |> ValueOption.bind (fun q ->
                                unify b length
                                |> ValueOption.map (Array.append q)
                            )
                            |> ValueOption.map (fun frame -> frame, context.substitutions)

                        match results with
                        | ValueSome r -> yield r
                        | ValueNone -> ()
                }
                |> Seq.noneIfEmpty
            
            | true, false ->
                match b with
                | Eval context (Number length) ->
                    let size =
                        if length < BigFloat.Zero || length = BigFloat.NaN then 0
                        elif length > BigFloat.Decimal (BigDecimal Int32.MaxValue) then Int32.MaxValue
                        else int (string length)
                    let constructed = ListTerm (List.init size (fun _ -> Atom "nil"))
                    unify a constructed
                    |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
                | _ -> ValueNone
            
            | false, true ->
                match a, b with
                | Eval context (ListTerm values), Variable b ->
                    ValueSome [| [| b, Number (BigFloat.Decimal (BigDecimal values.Length)) |], context.substitutions |]
                | _ -> ValueNone

            | false, false ->
                match a, b with
                | Eval context (ListTerm values), Eval context (Number length) ->
                    wrap context (BigFloat.Decimal (BigDecimal values.Length) = length)
                | _ -> ValueNone
            
        | _ -> ValueNone
    )
    
    describe "append" "append(+ListA, +ListB, -Combined) / append(-ListA, -ListB, +Combined)" "Concatenates two lists or splits a list into two parts."
    addPred ("append", 3) (fun context args ->
        match args with
        | [ a; b; c ] ->
            let freeA = hasFreeVariables a
            let freeB = hasFreeVariables b
            let freeC = hasFreeVariables c
            
            match freeA, freeB, freeC with
            | true, true, false ->
                match evaluateExpr context c with
                | ListTerm values ->
                    seq {
                        let mutable prefix = []
                        let mutable suffix = values
                        let mutable go = true
                        
                        while go do
                            let vars =
                                unify a (ListTerm prefix)
                                |> ValueOption.bind (fun q ->
                                    unify b (ListTerm suffix)
                                    |> ValueOption.map (Array.append q)
                                )
                                |> ValueOption.map (fun frame -> frame, context.substitutions)

                            match vars with
                            | ValueSome vars -> yield vars
                            | ValueNone -> ()
                            
                            match suffix with
                            | elm :: rest ->
                                prefix <- List.append prefix [ elm ]
                                suffix <- rest
                            | [] -> go <- false
                        
                    }
                    |> Seq.noneIfEmpty
                | _ -> ValueNone
            | false, false, true ->
                 match a, b with
                 | Eval context (ListTerm va), Eval context (ListTerm vb) ->
                     unify c (ListTerm (List.append va vb))
                     |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
                 | _ -> ValueNone
            | _ -> ValueNone
        
        | _ -> ValueNone
    )
    
    describe "element" "element(+List, ?Value)" "Determines if an element is contained by the list or lists all elements."
    addPred ("element", 2) (fun context args ->
        match args with
        | [ Eval context (ListTerm items); value ] ->
            seq {
                for item in items do
                    match unify item value with
                    | ValueSome bindings -> yield bindings, context.substitutions
                    | ValueNone -> ()
            }
            |> Seq.noneIfEmpty
            
        | _ -> ValueNone
    )
    
    terms