module Quiro.MetaTerms

open Quiro.Interpreter.Internal
open Quiro.TermHelpers

let create terms =
    let addPred = addPred terms
    
    describe "@meta" "@meta(+Term, +Attribute)" "Attaches the specified attribute to the given term."
    addPred ("@meta", 2) (fun context args ->
        match args with
        | [ Atom term; Atom "var_args" | Term("var_args", []) ] -> wrap context (varArgs.Contains term)
        | _ -> ValueNone
    )
    
    describe "describe" "describe" "Prints the description(s) of the term to stdout."
    describe "describe" "describe(+Term, -Signature, -Description)" "Provides the signature(s) and description(s) of the given term."

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