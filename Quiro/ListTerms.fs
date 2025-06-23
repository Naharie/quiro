module Quiro.ListTerms

open System
open Microsoft.FSharp.Core
open Quiro.Interpreter.Internal
open Quiro.TermHelpers

let create terms =
    let addPred = addPred terms
    
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
                        let length = Number (float i)
                        
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
                | Eval context (Number (IntNumber length)) ->
                    let constructed = ListTerm (List.init length (fun _ -> Atom "nil"))

                    unify a constructed
                    |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
                | _ -> ValueNone
            
            | false, true ->
                let eA = evaluateExpr context a
                
                match eA, b with
                | ListTerm values, Variable b ->
                    ValueSome [| [| b, Number (float values.Length) |], context.substitutions |]
                | Text data, Variable b ->
                    ValueSome [| [| b, Number (float data.Length) |], context.substitutions |]
                | _ -> ValueNone

            | false, false ->
                let eA = evaluateExpr context a
                let eB = evaluateExpr context b
                
                match eA, eB with                
                | ListTerm values, Number (IntNumber length) ->
                    wrap context (values.Length = length)

                | Text data, Number (IntNumber length) ->
                    wrap context (data.Length = length)
                    
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
                | Text data ->
                    seq {
                        let mutable index = 0
                        
                        while index <= data.Length do
                            let prefix = data.Substring(0, index)
                            let suffix = data.Substring(index)
                            
                            let vars =
                                unify a (Text prefix)
                                |> ValueOption.bind (fun q ->
                                    unify b (Text suffix)
                                    |> ValueOption.map (Array.append q)
                                )
                                |> ValueOption.map (fun frame -> frame, context.substitutions)

                            match vars with
                            | ValueSome vars -> yield vars
                            | ValueNone -> ()

                            index <- index + 1
                        
                    }
                    |> Seq.noneIfEmpty
                | _ -> ValueNone
            | false, false, true ->
                 let eA = evaluateExpr context a
                 let eB = evaluateExpr context b
                 
                 match eA, eB with
                 | Text a, Text b ->
                     unify c (Text (a + b))
                     |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
                 
                 | (ListTerm va | Text (TextList va)), (ListTerm vb | Text (TextList vb)) ->
                     unify c (ListTerm (List.append va vb))
                     |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
                     
                 | _ -> ValueNone
            | _ -> ValueNone
        
        | _ -> ValueNone
    )
    
    describe "element" "element(+List, ?Value)" "Determines if an element is contained by the list or lists all elements."
    addPred ("element", 2) (fun context args ->
        match args with
        | [ Eval context list; value ] ->
            match list with
            | ListTerm items ->
                seq {
                    for item in items do
                        match unify item value with
                        | ValueSome bindings -> yield bindings, context.substitutions
                        | ValueNone -> ()
                }
                |> Seq.noneIfEmpty
            | Text data ->
                seq {
                    for item in data do
                        match unify (Text (string item)) value with
                        | ValueSome bindings -> yield bindings, context.substitutions
                        | ValueNone -> ()
                }
                |> Seq.noneIfEmpty
                
            | _ -> ValueNone
        | _ -> ValueNone
    )
    
    describe "sort" "sort(+List, -Sorted)" "Sorts a list in ascending order."
    addPred ("sort", 2) (fun context args ->
        match args with
        | [ Eval context input; sorted ] ->
            match input with
            | ListTerm items ->
                unify sorted (ListTerm (List.sort items))
                |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
                
            | Text data ->
                unify sorted (
                    data.ToCharArray()
                    |> Array.sort
                    |> String
                    |> Text
                )
                |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))

            | _ -> ValueNone
        | _ -> ValueNone
    )
    
    describe "concat" "concat(+Groups, +Separator, -Combined) / concat(-Groups, +Separator, +Combined)" "Concatenates a list of lists with the given separator between them or separates a list on a given separator."
    addPred ("concat", 3) (fun context args ->
        match args with
        | [ NoFreeVars (Eval context (ListTerm items)); separator; combined ] ->
            let areAllText = items |> List.forall _.IsText
            
            match areAllText, separator with
            | true, Text separator ->
                items
                |> List.map (function | Text t -> t | _ -> "")
                |> String.concat separator
                |> Text
                |> unify combined
                |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
            | _, _ ->
                ListTerm [
                    let mutable first = true
                    
                    for item in items do
                        if not first then yield separator
                        
                        match item with
                        | ListTerm v -> yield! v
                        | _ -> yield item
                        
                        first <- false
                ]
                |> unify combined
                |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
        
        | [ HasFreeVars groups; separator; combined ] ->
            match separator, combined with
            | Text separator, Text combined ->
                combined.Split([| separator |], StringSplitOptions.None)
                |> Array.map Text
                |> Array.toList
                |> ListTerm
                |> unify groups
                |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
            | _, ListTerm items ->
                [
                    let group = ResizeArray()

                    for item in items do
                        if item = separator then
                            yield group.ToArray() |> List.ofArray |> ListTerm
                            group.Clear()
                        else
                            group.Add item
                        
                    if group.Count > 0 then
                        yield group.ToArray() |> List.ofArray |> ListTerm
                ]
                |> ListTerm
                |> unify groups
                |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
            
            | _, _ -> ValueNone
        | _ -> ValueNone
    )