module Quiro.DataTypes

open ExtendedNumerics
open Microsoft.FSharp.Core

type SimpleTerm =
    | Atom of atom:string
    | Integer of int:bigint
    | Float of float:BigDecimal
    | Variable of var:string
    | ListTerm of list:SimpleTerm list

module SimpleTerm =
    let rec toString (term: SimpleTerm) =
        match term with
        | Atom name -> name
        | Variable name -> name
        | Integer value -> string value
        | Float value -> string value
        | ListTerm values ->
            values
            |> List.map toString
            |> String.concat ", "
            |> fun body -> sprintf $"[ %s{body} ]"

type Goal =
    | SimpleGoal of functor:string * arguments:SimpleTerm[]
    | NegatedGoal of Goal
    | ConjunctionGoal of Goal * Goal
    | DisjunctionGoal of Goal * Goal

module Goal =
    let rec toString goal =
        match goal with
        | SimpleGoal(goal, [||]) -> goal
        | SimpleGoal(functor, args) ->
            let argsStr = args |> Array.map SimpleTerm.toString |> String.concat ", "
            $"%s{functor}(%s{argsStr})"
        | ConjunctionGoal(a, b) -> $"%s{toString a}, %s{toString b}"
        | DisjunctionGoal(a, b) -> $"%s{toString a}; %s{toString b}"

type Rule =
    | Rule of functor:string * arguments:SimpleTerm[] * goal:Goal

module Rule =
    let toString rule =
        let (Rule(functor, arguments, goal)) = rule
        let argsStr = arguments |> Array.map SimpleTerm.toString |> String.concat ", "
        $"%s{functor}(%s{argsStr}) :- %s{Goal.toString goal}"

type Scope = {
    rules: Map<(string * int), Rule list>
    nativeRules: Map<string * int, SimpleTerm[] -> Map<string, SimpleTerm> list option>
}