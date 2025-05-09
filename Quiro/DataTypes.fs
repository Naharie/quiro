[<CompilationRepresentation (CompilationRepresentationFlags.ModuleSuffix)>]
module rec Quiro.DataTypes

open System
open System.Diagnostics
open Microsoft.FSharp.Core
open Quiro.DataTypes

type PrologExpression =
    // a, 'b', 'hello'
    | Atom of atom:string
    // 1, 1.5, nan, infinity
    | Number of Number
    // "Hello World"
    | Text of string
    // [ 1, 2, 3 ]
    | ListTerm of list:PrologExpression list
    
    // func(x, y)
    | FunctionCall of target:string * args:PrologExpression list
    // Func(x, y)
    | DynamicFunctionCall of var:string * args:PrologExpression list
    
    // X, Y
    | Variable of name:string
    // [ Head | Tail ]
    | ListCons of head:PrologExpression * tail:PrologExpression
    // { Goal }
    | GoalExpr of Goal

type Goal =
    // A direct goal is a simple predication such as even(X), where the top level expression does not itself involve subgoals.
    | DirectGoal of functor:string * arguments:PrologExpression list
    // A dynamic goal is a variable, such as Pred, being invoked as a direct goal.
    | DynamicGoal of var:string * arguments:PrologExpression list

    // Attempts to prove the given goal, and upon failure returns success with no bindings, or failure with bindings that prove the goal, thereby disproving its negation.
    | NegatedGoal of Goal
    // The logical and operator; requires both sub goals to be provable to succeed.
    | ConjunctionGoal of Goal * Goal
    // The logical or operator; requires at least one of the sub goals to be provable to succeed.
    | DisjunctionGoal of Goal * Goal 

type Predicate = Predicate of functor:string * arguments:PrologExpression list * goal:Goal
type Function = Function of functor:string * arguments:PrologExpression list * body:PrologExpression

type Declaration =
    | PredicateDeclaration of predicate:Predicate
    | FunctionDeclaration of ``function``:Function

// Using exceptions may seem antithetical to functional programming and the style of F#,
// but sometimes it is the best option as it allows errors to bubble up from places that
// are constrained by the type system, such as the number type.
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
    | ExpressionFrame of PrologExpression
    | FunctionFrame of Function
    | NativePredicate of string
    | NativeFunction of string

type DebugLevel =
    // Print debug information about every single goal tested during the query.
    | All
    // Print debug information only about the rules tested during the query.
    | RuleOnly
    // Print debug information only about goals that succeed during the query.
    | OnlyTrue
    // Do not print any debug information.
    | NoDebugInfo

type InterpreterContext = {
    depth: int
    debugLevel: DebugLevel
    
    stack: StackFrame list
    
    seenGoals: Set<string * PrologExpression list>
    seenFunctions: Set<string * PrologExpression list>
    scope: Scope
}
and Scope = {
    values: Map<string, PrologExpression>
    
    predicates: Map<(string * int), Predicate list>
    nativePredicates: Map<string * int, (InterpreterContext -> PrologExpression list -> Map<string, PrologExpression> list option) list>
    
    functions: Map<(string * int), Function list>
    nativeFunctions: Map<string * int, (InterpreterContext -> PrologExpression list -> PrologExpression list option) list>
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

module PrologExpression =
    let rec toString (term: PrologExpression) =
        match term with
        | Atom name -> name
        | Variable name -> name
        | Number value -> string value
        | Text value ->
            let escaped =
                value
                    .Replace("\\", "\\\\")
                    .Replace("\"", "\\\"")
                    .Replace("\r", "\\r")
                    .Replace("\n", "\\n")
                    .Replace("\t", "\\t")
                    
            "\"" + escaped + "\""
            
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
        | DirectGoal(goal, []) -> goal
        | DirectGoal(functor, args) | DynamicGoal(functor, args) ->
            let argsStr = args |> List.map PrologExpression.toString |> String.concat ", "
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
                $"\tat expression %s{PrologExpression.toString expr}"
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
        let args = args |> List.map PrologExpression.toString |> String.concat ", "
        sprintf $"%s{name}(%s{args}) :-"

module Function =
    let toString ``function`` =
        let (Function (name, args, _)) = ``function``
        let args = args |> List.map PrologExpression.toString |> String.concat ", "
        sprintf $"%s{name}(%s{args}) -->"

module Declaration =
    let toString value =
        match value with
        | PredicateDeclaration predicate -> Predicate.toString predicate
        | FunctionDeclaration ``function`` -> Function.toString ``function``