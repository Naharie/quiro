module Quiro.ReflectionTerms

open Quiro.TermHelpers

let create terms =
    let addPred = addPred terms
    
    describe "is_atom" "is_atom(?Value)" "Determines if a value is an atom."
    addPred ("is_atom", 1) (fun context args -> match args with | [ Atom _ ] -> emptySuccess context | _ -> ValueNone)
    
    describe "is_number" "is_number(?Value)" "Determines if a value is a number."
    addPred ("is_number", 1) (fun context args -> match args with | [ Number _ ] -> emptySuccess context | _ -> ValueNone)
    
    describe "is_string" "is_string(?Value)" "Determines if a value is a string."
    addPred ("is_string", 1) (fun context args -> match args with | [ Text _ ] -> emptySuccess context | _ -> ValueNone)
    
    describe "is_list" "is_list(?Value)" "Determines if a value is a list."
    addPred ("is_list", 1) (fun context args -> match args with | [ ListTerm _ | ListCons _ ] -> emptySuccess context | _ -> ValueNone)
    
    describe "is_term" "is_term(?Value)" "Determines if a value is a term."
    addPred ("is_term", 1) (fun context args -> match args with | [ Term _ ] -> emptySuccess context | _ -> ValueNone)
    
    describe "is_variable" "is_variable(?Value)" "Determines if a value is a variable."
    addPred ("is_variable", 1) (fun context args -> match args with | [ Variable _ ] -> emptySuccess context | _ -> ValueNone)