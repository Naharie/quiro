module Quiro.Scope

open System
open Quiro.DataTypes

let private bind (values: (string * SimpleTerm) list) =
    values
    |> Map.ofList
    |> List.singleton
    |> Some

let equalPred terms =
    match terms with
    | [| a; b |] ->
        match a, b with
        | Variable _, Variable _ -> None
        | Variable name, concrete | concrete, Variable name ->
            bind [ (name, concrete) ]
        | _, _ ->
            if a = b then Some [] else None

    | _ -> None

let writePred terms =
    match terms with
    | [| ListTerm chars |] ->
        chars
        |> List.choose (function
            | Integer intValue ->
                match Int32.TryParse(intValue.ToString()) with
                | true, charValue -> Some (char charValue)
                | false, _ -> None
            | Float floatValue ->
                match Int32.TryParse(string floatValue) with
                | true, charValue -> Some (char charValue)
                | false, _ -> None
                
            | _ -> None
        )
        |> List.toArray
        |> String
        |> Console.WriteLine
        
        Some []
    
    | [| Variable var |] ->
        let value =
            Console.ReadLine().ToCharArray()
            |> Array.map (bigint >> Integer)
            |> Array.toList
            |> ListTerm
            
        bind [ (var, value) ]
    
    | _ ->
        None
let nlPred _ =
    printfn ""
    Some []

// Helpers for defining normal (non native) rules.

/// Builds a conjunction sequence, that is, the goal: a, b, c, ...
let private sequence goals =
    match goals with
    | [] -> SimpleGoal("false", Array.empty)
    | [ goal ] -> goal
    | head :: tail ->
        tail
        |> List.fold(fun currentGoal nextGoal ->
            ConjunctionGoal(currentGoal, nextGoal)
        ) head

let inline private atom name = Atom name
let inline private var name = Variable name
let inline private goal functor args = SimpleGoal(functor, List.toArray args)
let private text (value: String) =
    value.ToCharArray()
    |> Array.map (bigint >> Integer)
    |> Array.toList
    |> ListTerm

let private describe term description =
    Rule("describe", [| atom term; var "Description" |], goal "equal" [ var "Description"; text description  ])

let defaultScope = {
    rules = Map.ofArray [|
        ("usage", 1), [
            Rule("usage", [| var "Rule" |], (sequence [
                goal "nl" []
                goal "describe" [ var "Rule"; var "Description" ]
                goal "print" [ var "Description" ]
            ]))
        ]

        ("describe", 2), [
            describe "usage" "usage(-rule) prints the usage of a given rule to stdout."
            describe "describe" "describe(-rule, +description) sets description equal to the usage description for the specified rule."
            
            describe "=" "=(?a, ?b) checks if a and b are equivalent expressions"
            
            describe "write" "write(-text) writes a string to stdout; write(+var) reads a string from stdin."
            describe "print" "print is an alias for write."
            
            describe "nl" "nl prints a newline to stdout."
        ]
    |]
    nativeRules = Map.ofArray [|
        ("=", 2), equalPred
        
        ("write", 1), writePred
        ("print", 1), writePred
        
        ("nl", 0), nlPred
    |] 
}