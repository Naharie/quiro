[<CompilationRepresentation (CompilationRepresentationFlags.ModuleSuffix)>]
module rec Quiro.DataTypes

open System
open System.Diagnostics
open Microsoft.FSharp.Core
open Quiro.DataTypes

type Expression =
    | Atom of atom:string  
    | Number of Number
    | ListTerm of list:Expression list
    
    | FunctionCall of target:string * args:Expression list
    | DynamicFunctionCall of var:string * args:Expression list
    
    | Variable of name:string
    | ListCons of head:Expression * tail:Expression
    | GoalExpr of Goal

type Goal =
    | SimpleGoal of functor:string * arguments:Expression list
    | DynamicGoal of var:string * arguments:Expression list

    | NegatedGoal of Goal
    | ConjunctionGoal of Goal * Goal
    | DisjunctionGoal of Goal * Goal 

type Predicate = Predicate of functor:string * arguments:Expression list * goal:Goal
type Function = Function of functor:string * arguments:Expression list * body:Expression

type Declaration =
    | PredicateDeclaration of predicate:Predicate
    | FunctionDeclaration of ``function``:Function

// Using exceptions may seem antithetical to functional programming and the style of F#,
// but sometimes it is the best option as it allows errors to bubble up from places that
// are constrained by the type system, such as the number type above.
type PrologException(message: string, stack: StackFrame list, inner: Exception) =
    inherit Exception(message, inner)
    new(message: string, stack: StackFrame list) = PrologException(message, stack, null)

    override _.ToString() =
        message + "\r\n" + StackFrame.toString stack

type InsufficientSubstantiationException (term: string, stack: StackFrame list) =
    inherit PrologException($"The term %s{term} was not sufficiently substantiated", stack)

type UnboundVariableException (variable: string, stack: StackFrame list) =
    inherit PrologException($"The variable %s{variable} was not bound in the current scope", stack)

type StackFrame =
    | GoalFrame of Goal
    | ExpressionFrame of Expression
    | FunctionFrame of Function
    | NativePredicate of string
    | NativeFunction of string

type Trace = All | RuleOnly | OnlyTrue | NoTrace

type Context = {
    depth: int
    trace: Trace
    
    stack: StackFrame list
    
    seenGoals: Set<string * Expression list>
    seenFunctions: Set<string * Expression list>
    scope: Scope
}
and Scope = {
    values: Map<string, Expression>
    
    predicates: Map<(string * int), Predicate list>
    nativePredicates: Map<string * int, (Context -> Expression list -> Map<string, Expression> list option) list>
    
    functions: Map<(string * int), Function list>
    nativeFunctions: Map<string * int, (Context -> Expression list -> Expression list option) list>
}

// Helper Values

let emptyScope = {
    values = Map.empty
    
    predicates = Map.empty
    nativePredicates = Map.empty
    
    functions = Map.empty
    nativeFunctions = Map.empty 
}

// Helper modules

module Scope =
    let rec lookupValue (variable: string) (scope: Scope) =
        scope.values |> Map.tryFind variable
    
    let lookupPredicates (key: string * int) (scope: Scope) =
        [|
            yield!
                scope.predicates
                |> Map.tryFind key
                |> Option.defaultValue List.empty
                |> List.toArray
                |> Array.map Choice1Of2

            yield!
                scope.nativePredicates
                |> Map.tryFind key
                |> Option.defaultValue List.empty
                |> List.toArray
                |> Array.map Choice2Of2
        |]
   
    let lookupFunctions (key: string * int) (scope: Scope) =
        [|
            yield!
                scope.functions
                |> Map.tryFind key
                |> Option.defaultValue List.empty
                |> List.toArray
                |> Array.map Choice1Of2

            yield!
                scope.nativeFunctions
                |> Map.tryFind key
                |> Option.defaultValue List.empty
                |> List.toArray
                |> Array.map Choice2Of2
        |]

module Expression =
    let rec toString (term: Expression) =
        match term with
        | Atom name -> name
        | Variable name -> name
        | Number value -> string value
        | ListTerm values ->
            values
            |> List.map toString
            |> String.concat ", "
            |> fun body -> sprintf $"[ %s{body} ]"
        | ListCons (head, tail) ->
            sprintf $"[ %s{toString head} | %s{toString tail} ]"
        | FunctionCall(functor, args) | DynamicFunctionCall(functor, args) ->
            let args =
                args
                |> List.map toString
                |> String.concat ", "
            
            $"%s{functor}(%s{args})"
        | GoalExpr goal ->
            "{ " + Goal.toString goal + " }"

module Goal =
    let rec toString goal =
        match goal with
        | SimpleGoal(goal, []) -> goal
        | SimpleGoal(functor, args) | DynamicGoal(functor, args) ->
            let argsStr = args |> List.map Expression.toString |> String.concat ", "
            $"%s{functor}(%s{argsStr})"
        | NegatedGoal goal ->
            "\+ " + toString goal
        | ConjunctionGoal(a, b) -> $"%s{toString a}, %s{toString b}"
        | DisjunctionGoal(a, b) -> $"%s{toString a}; %s{toString b}"
      
module StackFrame =
    let toString (stack: StackFrame list) =
        [
            for frame in stack do
            match frame with
            | GoalFrame goal ->
                $"\tat goal %s{Goal.toString goal}"
            | ExpressionFrame expr ->
                $"\tat expression %s{Expression.toString expr}"
            | FunctionFrame func ->
                $"\tat function %s{Function.toString func}"
                
            | NativeFunction name ->
                $"\tat native function %s{name}"
            | NativePredicate name ->
                $"\tat native predicate %s{name}"
        ]
        |> String.concat "\r\n"

module Predicate =
    let toString predicate =
        let (Predicate (name, args, _)) = predicate
        let args = args |> List.map Expression.toString |> String.concat ", "
        sprintf $"%s{name}(%s{args}) :-"

module Function =
    let toString ``function`` =
        let (Function (name, args, _)) = ``function``
        let args = args |> List.map Expression.toString |> String.concat ", "
        sprintf $"%s{name}(%s{args}) -->"

module Declaration =
    let toString value =
        match value with
        | PredicateDeclaration predicate -> Predicate.toString predicate
        | FunctionDeclaration ``function`` -> Function.toString ``function``