module Quiro.BuiltinTerms.StoredTerms

open System
open Microsoft.FSharp.Core
open Quiro
open Quiro.StoredTerms

[<AutoOpen>]
module Predicates =
    let private pred (f: InterpreterContext -> PrologValue list -> Map<string, PrologValue> seq voption) = f
    let private emptySuccess: Map<string, PrologValue> seq voption = ValueSome [| Map.empty |]

    let nl = pred(fun _ args ->
        Console.WriteLine()
        emptySuccess
    )
    let write = pred(fun _ args ->
        match args[0] with
        | Variable name ->
            let value = Console.ReadLine()
            ValueSome [| Map.ofArray [| (name, Text value) |] |]
            
        | Text text ->
            Console.Write text
            emptySuccess

        | value ->
            Console.Write(PrologValue.toString value)
            emptySuccess    
    )

[<AutoOpen>]
module Functions =
    ()

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
    
    let describe term signature description =
        addPred ("describe", 3) (fun _ args ->
            match args with
            | [ Atom lookupTerm; Variable signatureVar; Variable descriptionVar ] when lookupTerm = term ->
                ValueSome [| Map.ofArray [|
                    (signatureVar, Text signature)
                    (descriptionVar, Text description)
                |] |]

            | _ -> ValueNone
        )
    
    describe "describe" "describe" "Prints the description(s) of the term to stdout."
    describe "describe" "describe(+Term, -Signature, -Description)" "Provides the signature(s) and description(s) of the given term."

    terms.userPredicates[("describe", 1)] <- ResizeArray([|
        [ Variable "Term" ], ConjunctionGoal [|
            SimpleGoal("describe", [ Variable "Term"; Variable "Signature"; Variable "Description" ])
            SimpleGoal("write", [ Variable "Signature" ])
            SimpleGoal("write", [ Text " - " ])
            SimpleGoal("write", [ Variable "Description" ])
            SimpleGoal("nl", [])
        |]
    |])
    
    describe "nl" "nl" "Prints a newline to stdout."
    addPred ("nl", 0) nl
    
    describe "write" "write(?Value)" "Prints a value to stdout or a reads a character from stdin."
    addPred ("write", 1) write

    terms