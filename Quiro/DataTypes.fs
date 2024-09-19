module rec Quiro.DataTypes

open System
open ExtendedNumerics
open Microsoft.FSharp.Core

type Expression =
    | Atom of atom:string
    | BooleanExpr of bool
    | Integer of int:bigint
    | Float of float:BigDecimal
    | ListTerm of list:Expression list
    | FunctionCall of target:string * args:Expression[]
    | Variable of name:string
    | ListCons of head:Expression * tail:Expression
    | GoalExpr of Goal

type Goal =
    | SimpleGoal of functor:string * arguments:Expression[]
    | NegatedGoal of Goal
    | ConjunctionGoal of Goal * Goal
    | DisjunctionGoal of Goal * Goal 

type Predicate = Predicate of functor:string * arguments:Expression[] * goal:Goal
type Function = Function of functor:string * arguments:Expression[] * body:Expression

type Declaration =
    | PredicateDeclaration of predicate:Predicate
    | FunctionDeclaration of ``function``:Function

[<Struct>]
type PrologError =
    | InsufficientSubstantiation of term:string * stack:StackFrame list

type StackFrame =
    | GoalFrame of Goal
    | ExpressionFrame of Expression

type Trace = All | OnlyTrue | NoTrace

type Context = {
    depth: int
    trace: Trace
    
    seenGoals: Set<Goal>
    seenExpressions: Set<Expression>
    
    stack: StackFrame list
    
    scope: Scope
}
and Scope = {
    parent: Scope option

    values: Map<string, Expression>
    
    predicates: Map<(string * int), Predicate list>
    nativePredicates: Map<string * int, (Context -> Expression[] -> Result<Map<string, Expression> list option, PrologError>) list>
    
    functions: Map<(string * int), Function list>
    nativeFunctions: Map<string * int, (Context -> Expression[] -> Result<Expression option, PrologError>) list>
}

// Helper Values

let emptyScope = {
    parent = None
    values = Map.empty
    
    predicates = Map.empty
    nativePredicates = Map.empty
    
    functions = Map.empty
    nativeFunctions = Map.empty 
}

// Helper modules

module Scope =
    let rec lookupValue (variable: string) (scope: Scope) =
        match scope.values |> Map.tryFind variable with
        | Some value -> Some value
        | None ->
            match scope.parent with
            | Some parent -> lookupValue variable parent
            | None -> None
    
    let lookupPredicates (key: string * int) (scope: Scope) =
        [|
            let mutable currentScope = Some scope
            
            while Option.isSome currentScope do
                match currentScope with
                | Some wrappedScope ->
                    yield!
                        wrappedScope.predicates
                        |> Map.tryFind key
                        |> Option.defaultValue List.empty
                        |> List.toArray
                        |> Array.map Choice1Of2

                    yield!
                        wrappedScope.nativePredicates
                        |> Map.tryFind key
                        |> Option.defaultValue List.empty
                        |> List.toArray
                        |> Array.map Choice2Of2
                        
                    currentScope <- wrappedScope.parent
                | None -> ()
        |]
   
    let lookupFunctions (key: string * int) (scope: Scope) =
        [|
            let mutable currentScope = Some scope
            
            while Option.isSome currentScope do
                match currentScope with
                | Some wrappedScope ->
                    yield!
                        wrappedScope.functions
                        |> Map.tryFind key
                        |> Option.defaultValue List.empty
                        |> List.toArray
                        |> Array.map Choice1Of2

                    yield!
                        wrappedScope.nativeFunctions
                        |> Map.tryFind key
                        |> Option.defaultValue List.empty
                        |> List.toArray
                        |> Array.map Choice2Of2
                        
                    currentScope <- wrappedScope.parent
                | None -> ()
        |]

module Expression =
    let rec toString (term: Expression) =
        match term with
        | Atom name -> name
        | Variable name -> name
        | Integer value -> string value
        | BooleanExpr value ->
            if value then "true" else "false"
        | Float value -> string value
        | ListTerm values ->
            values
            |> List.map toString
            |> String.concat ", "
            |> fun body -> sprintf $"[ %s{body} ]"
        | ListCons (head, tail) ->
            sprintf $"[ %s{toString head} | %s{toString tail} ]"
        | FunctionCall(functor, args) ->
            let args =
                args
                |> Array.map toString
                |> String.concat ", "
            
            $"%s{functor}(%s{args})"
        | GoalExpr goal ->
            "{ " + Goal.toString goal + " }"

module Goal =
    let rec toString goal =
        match goal with
        | SimpleGoal(goal, [||]) -> goal
        | SimpleGoal(functor, args) ->
            let argsStr = args |> Array.map Expression.toString |> String.concat ", "
            $"%s{functor}(%s{argsStr})"
        | NegatedGoal goal ->
            "\+ " + toString goal
        | ConjunctionGoal(a, b) -> $"%s{toString a}, %s{toString b}"
        | DisjunctionGoal(a, b) -> $"%s{toString a}; %s{toString b}"
      
module StackFrame =
    let displayStack (stack: StackFrame list) =
        for frame in stack do
            match frame with
            | GoalFrame goal ->
                printfn $"\tat goal %s{Goal.toString goal}"
            | ExpressionFrame expression ->
                printfn $"\tat expression %s{Expression.toString expression}"
                
module PrologError =
    let displayError error =
        match error with
        | InsufficientSubstantiation (term, stack) ->
            printfn $"The term %s{term} was not sufficiently substantiated"
            StackFrame.displayStack stack

module Predicate =
    let toString predicate =
        let (Predicate (name, args, _)) = predicate
        let args = args |> Array.map Expression.toString |> String.concat ", "
        sprintf $"%s{name}(%s{args}) :-"

module Function =
    let toString ``function`` =
        let (Function (name, args, _)) = ``function``
        let args = args |> Array.map Expression.toString |> String.concat ", "
        sprintf $"%s{name}(%s{args}) -->"

module Declaration =
    let toString value =
        match value with
        | PredicateDeclaration predicate -> Predicate.toString predicate
        | FunctionDeclaration ``function`` -> Function.toString ``function``