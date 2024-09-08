module Quiro.Interpreter

open System
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

let private trace = true
let private print depth (text: string) =
    if trace then
        let prefix = String.replicate depth "\t"
        Console.Write(prefix)
        Console.WriteLine(text)

/// Tests a rule against a goal to see if it matches,
/// creating a table of any required bindings when it does.
let private testRule tryProveGoal depth (scope: Scope) (currentGoal: string * SimpleTerm[]) (rule: Rule) : Map<string, SimpleTerm> list option =
    let _, concreteArgs = currentGoal
    let (Rule(_, ruleArgs, ruleGoal)) = rule
    
    let argPairs = Array.zip ruleArgs concreteArgs
    
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
    
    print depth $"%s{Rule.toString rule} -> %O{isMatch}"
    
    // If the rule matches then we need to try and prove the rule's goal.
    if isMatch then
        match tryProveGoal depth ruleGoal argBindings scope with
        // 'ruleGoalBindings' contains any variables bound during the proof of the goal.
        | Some ruleGoalBindingsList ->
            // If the current goal we are evaluating has a variable in a given slot *and* that slot is a variable in the rule pattern,
            // we want to be able to capture that inner variable's values to use as values for the outer variable.
            // We insert an extra empty map here to ensure we go through the process of creating a binding set at least once
            // (The inner goal may not have created any binding sets.)
            (Map.empty :: ruleGoalBindingsList)
            // All variables bindings happen in sets so that a query such as sum(X, Y, 10) returns pairs of X and Y that add to 10 instead of disconnected lists of values.
            |> List.map (fun bindingSet ->
                argPairs
                |> Array.choose (fun (ruleArg, concreteArg) ->
                    match ruleArg, concreteArg with
                    | Variable concreteVar, Variable ruleVar ->
                        bindingSet
                        |> Map.tryFind ruleVar
                        |> Option.map (fun value ->
                            (concreteVar, value)
                        )

                    | _, Variable concreteVar ->
                        Some (concreteVar, ruleArg)
                        
                    | _ -> None
                )
                |> Map.ofArray
            )
            |> List.filter (Map.isEmpty >> not)
            |> Some

        | None -> None
    else
        None

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
                    |> Option.defaultValue var
                | other -> other
            )
        )
    | ConjunctionGoal(a, b) -> ConjunctionGoal(substituteVars a vars, substituteVars b vars)
    | DisjunctionGoal(a, b) -> DisjunctionGoal(substituteVars a vars, substituteVars b vars)
let rec private tryProveGoal (depth: int) (goal: Goal) (argBindings: Map<string, SimpleTerm>) (scope: Scope): Map<string, SimpleTerm> list option =
    let goal = substituteVars goal argBindings
 
    if trace then
        match goal with
        | SimpleGoal ("true", [||]) -> ()
        | SimpleGoal ("false", [||]) -> ()
        | _ ->
            print depth (Goal.toString goal)
    
    match goal with
    | SimpleGoal ("true", [||]) -> Some []
    | SimpleGoal ("false", [||]) -> None

    | SimpleGoal (functor, args) ->
        let key = (functor, args.Length)
        
        match scope.rules |> Map.tryFind key with
        | Some rules ->
            // Shadow test rule with a version that partially applies with all the shared args.
            let testRule = testRule tryProveGoal (depth + 1) scope (functor, args)
            
            let success, bindings =
                rules
                |> List.fold (fun (success, bindings) rule ->
                    match testRule rule with
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

    | ConjunctionGoal (a, b) ->
        match tryProveGoal (depth + 1) a argBindings scope with
        | Some newBindings ->
            let bindings =
                newBindings
                |> List.map (fun bindingGroup -> Map.merge bindingGroup argBindings)
            
            // If we have at least one result then goal b was proved at least once with some set of bindings.
            let result =
                (Map.empty :: bindings)
                |> List.choose (fun bindingGroup ->
                    tryProveGoal (depth + 1) b bindingGroup scope
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
        match tryProveGoal (depth + 1) a argBindings scope with
        | Some _ as result -> result
        | None -> tryProveGoal (depth + 1) b argBindings scope 

/// Query whether a given rule is true or false.
let rec query (rule: Rule) (scope: Scope): Result<Map<string, SimpleTerm> list option, string> =
    let (Rule(queryFunctor, queryArgs, queryGoal)) = rule
    let testedGoal = SimpleGoal (queryFunctor, queryArgs)
    
    match queryGoal with
    | SimpleGoal("true", [||]) ->
        Ok (tryProveGoal 0 testedGoal Map.empty scope)

    | SimpleGoal("false", [||]) ->
        tryProveGoal 0 testedGoal Map.empty scope
        |> Option.invert []
        |> Ok
    | _ ->
        Error "Can't query for non yes or no answers!"