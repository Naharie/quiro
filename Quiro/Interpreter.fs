module Quiro.Interpreter

open System
open System.Data
open Microsoft.FSharp.Quotations
open Quiro.DataTypes

/// Execute a rule, that is, add it to the list of known rules, but do not perform a query.
let execute (Rule (functor, args, _) as rule) (scope: Scope) =
    let updatedRules =
        let key = (functor, args.Length)
        let existing =
            Map.tryFind key scope.rules
            |> Option.defaultValue List.empty
        
        Map.add key (rule :: existing) scope.rules
    
    { scope with rules = updatedRules }

/// Substitutes in any values for known variables (such as X = socrates in mortal(socrates) where mortal is mortal(X) :- human(X).)
let private getConcreteArgs args bindings =
    args
    |> Array.map (function
        | Variable x as var ->
            bindings
            |> Map.tryFind x
            |> Option.defaultValue var
        | other -> other
    )

type Trace = All | OnlyTrue | NoTrace

let private trace = NoTrace

let private print depth (text: string) =
    let prefix = String.replicate depth "\t"
    Console.Write(prefix)
    Console.WriteLine(text)

type TryProveGoalArgs = {
    depth: int
    goal: Goal
    argBindings: Map<string, SimpleTerm>
    scope: Scope
    seen: Set<Goal>
}
type TestRuleArgs = {
    tryProveGoal: TryProveGoalArgs -> Map<string, SimpleTerm> list option
    depth: int
    scope: Scope
    currentGoal: string * SimpleTerm[]
    rule: Rule
    seen: Set<Goal>
}

let rec private substituteVars (goal: Goal) (vars: Map<string, SimpleTerm>) =
    match goal with
    | SimpleGoal(functor, args) ->
        SimpleGoal(
            functor,
            args
            |> Array.map(function
                | Variable name as var ->
                    vars
                    |> Map.tryFind name
                    |> Option.bind (function
                        | Variable _ -> None
                        | other -> Some other
                    )
                    |> Option.defaultValue var
                | other -> other
            )
        )
    | NegatedGoal goal -> NegatedGoal (substituteVars goal vars)
    | ConjunctionGoal(a, b) -> ConjunctionGoal(substituteVars a vars, substituteVars b vars)
    | DisjunctionGoal(a, b) -> DisjunctionGoal(substituteVars a vars, substituteVars b vars)

/// Tests a rule against a goal to see if it matches,
/// creating a table of any required bindings when it does.
let private testRule args : Map<string, SimpleTerm> list option =
    let {
        tryProveGoal = tryProveGoal
        depth = depth
        scope = scope
        currentGoal = _, outerArgs
        rule = Rule(ruleFunctor, ruleArgs, ruleGoal) as rule
        seen = seen
    } = args
    
    let argPairs = Array.zip ruleArgs outerArgs
    
    /// Build a mapping of variable names used in the goal to the supplied concrete values,
    /// all the while checking that any non-variable arguments the rule demands are satisfied.
    let isMatch, argBindings =
        argPairs
        |> Array.fold (fun (isMatch, argBindings) (ruleArg, concreteArg) ->
            if isMatch then
                match ruleArg with
                | Variable ruleVar ->
                    (true, argBindings |> Map.add ruleVar concreteArg)
                | _ ->
                    match concreteArg with
                    | Variable _ -> (true, argBindings)
                    | _ -> (ruleArg = concreteArg, argBindings)
            else
                (false, argBindings)
        ) (true, Map.empty)
    
    match trace with
    | All | OnlyTrue ->
        let ruleArgs =
            ruleArgs
            |> Array.map(function
                | Variable name as var ->
                    argBindings
                    |> Map.tryFind name
                    |> Option.defaultValue var
                | other -> other
            )
        let rule = Rule(ruleFunctor, ruleArgs, substituteVars ruleGoal argBindings)
        
        match trace with
        | All ->
            print depth $"%s{Rule.toString rule} -> %O{isMatch}"
        | OnlyTrue -> if isMatch then print depth $"%s{Rule.toString rule}"
        | NoTrace -> ()
    | OnlyTrue | NoTrace -> ()

    // If the rule matches then we need to try and prove the rule's goal.
    if isMatch then
        match tryProveGoal { depth = depth; goal = ruleGoal; scope = scope; argBindings = argBindings; seen = seen } with
        | Some newBindings ->
            (Map.empty :: newBindings)
            |> List.map (fun bindingGroup ->
                // If the goal is proven, then we need to grab all variables or values from the inner scope and copy over the value or the value the variable points to to the outer scope.
                argPairs
                |> Array.choose (fun (ruleArg, outerArg) ->
                    match outerArg, ruleArg with
                    | Variable name, Variable innerName ->
                        bindingGroup |> Map.tryFind innerName
                        |> Option.map (fun value -> name, value)
                    | Variable name, _ -> Some (name, ruleArg)
                    | _ -> None
                )
                |> Map.ofArray
            )
            |> List.filter (Map.isEmpty >> not)
            |> Some
        | None -> None
    else
        None

let rec private tryProveGoal args: Map<string, SimpleTerm> list option =
    let {
        depth = depth
        goal = goal
        argBindings = argBindings
        scope = scope
        seen = seen
    } = args
    
    let goal = substituteVars goal argBindings
    
    if seen |> Set.contains goal then
        None
    else
        match goal with
        | SimpleGoal ("true", [||]) -> Some []
        | SimpleGoal ("false", [||]) -> None

        | SimpleGoal (functor, args) ->
            let key = (functor, args.Length)
            
            match scope.rules |> Map.tryFind key with
            | Some rules ->
                let success, bindings =
                    rules
                    |> List.fold (fun (success, bindings) rule ->
                        match testRule {
                            tryProveGoal = tryProveGoal
                            depth = depth + 1
                            scope = scope
                            currentGoal = (functor, args)
                            rule = rule
                            seen = seen |> Set.add goal
                        } with
                        | Some newBindings ->
                            (true, List.append bindings newBindings)
                        | None ->
                            (success, bindings)
                    ) (false, [])
                
                if success then
                    Some bindings
                else
                    None
            
            | None ->
                match scope.nativeRules |> Map.tryFind key with
                | Some rule -> rule args
                | None -> None

        | NegatedGoal subGoal ->
            let provability = tryProveGoal { depth = depth + 1; goal = subGoal; argBindings = argBindings; scope = scope; seen = seen |> Set.add goal }
            Option.invert [] provability
        
        | ConjunctionGoal (a, b) ->
            match tryProveGoal { depth = depth + 1; goal = a; argBindings = argBindings; scope = scope; seen = seen |> Set.add goal } with
            | Some newBindings ->
                let bindings =
                    newBindings
                    |> List.map (fun bindingGroup -> Map.merge bindingGroup argBindings)
                
                // If we have at least one result then goal b was proved at least once with some set of bindings.
                let result =
                    (Map.empty :: bindings)
                    |> List.choose (fun bindingGroup ->
                        tryProveGoal { depth = depth + 1; goal = b; argBindings = bindingGroup; scope = scope; seen = seen |> Set.add goal }
                    )

                match result with
                | [] -> None
                | _ -> Some(
                    result
                    |> List.collect id
                    |> List.filter (Map.isEmpty >> not)
                )
                
            | None -> None

        | DisjunctionGoal (a, b) ->
            let args = { depth = depth + 1; goal = a; scope = scope; argBindings = argBindings; seen = seen |> Set.add goal }
            
            match tryProveGoal args with
            | Some _ as result -> result
            | None -> tryProveGoal { args with goal = b }

(*
human(socrates).
mortal(X) :- human(X).

mother_child(trude, sally).
father_child(tom, sally).
father_child(tom, erica).
father_child(mike, tom).
sibling(X, Y)      :- parent_child(Z, X), parent_child(Z, Y).
parent_child(X, Y) :- father_child(X, Y).
parent_child(X, Y) :- mother_child(X, Y).

ancestor(X, Y) :- parent_child(X, Y).
ancestor(X, Y) :- parent_child(X, Z), ancestor(Z, Y).
*)

/// Query whether a given rule is true or false.
let rec query (goal: Goal) (scope: Scope): Map<string, SimpleTerm> list option =
    tryProveGoal {
        depth = 0
        goal = goal
        scope = scope
        argBindings = Map.empty
        seen = Set.empty 
    }