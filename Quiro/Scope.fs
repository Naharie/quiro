module Quiro.Scope

open System
open Quiro.DataTypes

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
    Function("describe", [| atom term; |], text description)

let defaultScope = {
   parent = None
   values = Map.empty
   
   predicates = Map.empty
   nativePredicates = Map.ofArray [||]
   
   functions = Map.empty
   nativeFunctions = Map.ofArray [||] 
}