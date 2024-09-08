module Quiro.DataTypes

open ExtendedNumerics

type SimpleTerm =
    | Atom of string
    | Integer of bigint
    | Float of BigDecimal
    | Variable of string
    | ListTerm of SimpleTerm list

type ComplexTerm =
    | CompoundTerm of functor:string * arguments:SimpleTerm[]
    | CompoundLookup of variable:string * arguments:SimpleTerm[]

type Goal =
    | SimpleGoal of functor:string * arguments:SimpleTerm[]
    | ConjunctionGoal of Goal * Goal
    | DisjunctionGoal of Goal * Goal

type Rule =
    | Rule of functor:string * arguments:SimpleTerm[] * goal:Goal

type Scope = {
    rules: Map<(string * int), Rule list>
    nativeRules: Map<string * int, SimpleTerm[] -> Map<string, SimpleTerm> list option>
}