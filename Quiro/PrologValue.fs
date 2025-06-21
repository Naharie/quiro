namespace rec Quiro

type PrologValue =
    // a, 'b', 'hello'
    | Atom of atom:string
    // 1, 1.5, nan, infinity
    | Number of BigFloat
    // "Hello World"
    | Text of string
    
    // [ Head | Tail ]
    | ListCons of head:PrologValue * tail:PrologValue
    // [ 1, 2, 3 ]
    | ListTerm of list:PrologValue list
    
    // func(x, y)
    | Term of target:string * args:PrologValue list

    // X, Y
    | Variable of name:string

type Goal =
    // A simple goal is a simple predication such as even(X), where the top level expression does not itself involve subgoals.
    | SimpleGoal of functor:string * arguments:PrologValue list

    // Inverts the result of proving the goal: success becomes failure and failure becomes success. 
    | NegatedGoal of Goal
    // The logical and operator; requires both sub goals to be provable to succeed.
    | ConjunctionGoal of Goal[]
    // The logical or operator; requires at least one of the sub goals to be provable to succeed.
    | DisjunctionGoal of Goal[]

[<RequireQualifiedAccess>]
type DCG =
    | Term of string
    | Call of functor:string * args:PrologValue list
    // { Goal }
    | Goal of Goal
    | List of PrologValue list
    | Sequence of DCG[]

module PrologValue =
    let rec toString (term: PrologValue) =
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
        | Term(functor, args) ->
            let args =
                args
                |> List.map toString
                |> String.concat ", "
            
            $"%s{functor}(%s{args})"

module Goal =
    let rec toString goal =
        match goal with
        | SimpleGoal(goal, []) -> goal
        | SimpleGoal(functor, args) ->
            let argsStr = args |> List.map PrologValue.toString |> String.concat ", "
            $"%s{functor}(%s{argsStr})"
        | NegatedGoal goal ->
            "\+ " + toString goal
        | ConjunctionGoal goals ->
            goals
            |> Array.map toString
            |> String.concat ", "
        | DisjunctionGoal goals ->
            goals
            |> Array.map toString
            |> String.concat "; "