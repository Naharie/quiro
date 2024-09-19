module Quiro.Interpreter

open System
open Quiro.DataTypes

/// Execute a declaration, that is, add it to the list of known declarations, but do not perform a query.
let execute declaration (scope: Scope) =
    match declaration with
    | PredicateDeclaration (Predicate (functor, args, _) as predicate) ->
        let updatedDeclarations =
            let key = (functor, args.Length)
            let existing =
                Map.tryFind key scope.predicates
                |> Option.defaultValue List.empty
            
            Map.add key (predicate :: existing) scope.predicates
        
        { scope with predicates = updatedDeclarations }

    | FunctionDeclaration (Function (functor, args, _) as ``function``) ->
        let updatedDeclarations =
            let key = (functor, args.Length)
            let existing =
                Map.tryFind key scope.functions
                |> Option.defaultValue List.empty
            
            Map.add key (``function`` :: existing) scope.functions

        { scope with functions = updatedDeclarations }

module rec Internal =
    let private print depth (text: string) =
        let prefix = String.replicate depth "\t"
        Console.Write(prefix)
        Console.WriteLine(text)

    type GoalContext = {
        depth: int
        trace: Trace
        
        goal: Goal
        
        scope: Scope
        
        seenGoals: Set<Goal>
        seenExpressions: Set<Expression>
        stack: StackFrame list
    }
    type private RuleContext = {
        depth: int
        trace: Trace
        
        currentGoal: string * Expression[]
        
        scope: Scope
        
        predicate: Predicate
        
        seenGoals: Set<Goal>
        seenExpressions: Set<Expression>
        stack: StackFrame list
    }

    let rec private substituteVarsInGoal (goal: Goal) (scope: Scope) =
        match goal with
        | SimpleGoal(functor, args) ->
            SimpleGoal(
                functor,
                args
                |> Array.map(function
                    | Variable name as var ->
                        Scope.lookupValue name scope
                        |> Option.defaultValue var
                    | other -> other
                )
            )
        | NegatedGoal goal -> NegatedGoal (substituteVarsInGoal goal scope)
        | ConjunctionGoal(a, b) -> ConjunctionGoal(substituteVarsInGoal a scope, substituteVarsInGoal b scope)
        | DisjunctionGoal(a, b) -> DisjunctionGoal(substituteVarsInGoal a scope, substituteVarsInGoal b scope)

    /// Tests a rule against a goal to see if it matches,
    /// creating a table of any required bindings when it does.
    let private testRule args : Result<Map<string, Expression> list option, PrologError> =
        let {
            depth = depth
            trace = trace
            
            currentGoal = _, outerArgs
            scope = scope
            
            predicate = Predicate(ruleFunctor, ruleArgs, ruleGoal) as rule
            
            seenGoals = seenGoals
            seenExpressions = seenExpressions
            stack = stack
        } = args
        
        let argPairs = Array.zip ruleArgs outerArgs
        
        let rec checkArgMatch ruleArg concreteArg argBindings =
            match ruleArg with
            | Variable ruleVar ->
                Some (argBindings |> Map.add ruleVar concreteArg)
                
            | ListCons (ruleHead, ruleTail) ->
                match concreteArg with
                | ListTerm (concreteHead :: concreteTail) ->
                    match checkArgMatch ruleHead concreteHead argBindings with
                    | Some argBindings ->
                        checkArgMatch ruleTail (ListTerm concreteTail) argBindings
                    | None -> None
                | _ ->
                    None

            | ListTerm ruleTerms ->
                match concreteArg with
                | ListTerm concreteTerms ->
                    if ruleTerms.Length <> concreteTerms.Length then
                        None
                    else
                        List.zip ruleTerms concreteTerms
                        |> List.fold (fun argBindings (ruleTerm, concreteTerm) ->
                            match argBindings with
                            | Some argBindings ->
                                checkArgMatch ruleTerm concreteTerm argBindings
                            | None -> None
                        ) (Some argBindings)
                | _ ->
                    None
            | _ ->
                match concreteArg with
                | Variable _ -> Some argBindings
                | _ ->
                    if ruleArg = concreteArg then Some argBindings else None
        
        /// Build a mapping of variable names used in the goal to the supplied concrete values,
        /// all the while checking that any non-variable arguments the rule demands are satisfied.
        let rawArgBindings =
            argPairs
            |> Array.fold (fun argBindings (ruleArg, concreteArg) ->
                match argBindings with
                | Some argBindings ->
                    checkArgMatch ruleArg concreteArg argBindings
                | None -> None
            ) (Some Map.empty)
        let isMatch, argBindings =
            match rawArgBindings with
            | Some bindings -> true, bindings
            | None -> false, Map.empty
            
        let subScope = {
            emptyScope with
                parent = Some scope
                values = argBindings 
        }
        
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
            let rule = Predicate(ruleFunctor, ruleArgs, substituteVarsInGoal ruleGoal subScope)
            
            match trace with
            | All ->
                print depth $"%s{Predicate.toString rule}  (%O{isMatch}?)"
            | OnlyTrue -> if isMatch then print depth $"%s{Predicate.toString rule}"
            | NoTrace -> ()
        | OnlyTrue | NoTrace -> ()

        // If the rule matches then we need to try and prove the rule's goal.
        if isMatch then
            match tryProveGoal {
                depth = depth
                trace = trace
                
                goal = ruleGoal
                
                scope = scope
                
                seenGoals = seenGoals
                seenExpressions = seenExpressions
                stack = (GoalFrame ruleGoal) :: stack 
            } with
            | Ok result ->
                match result with
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
                    |> Ok
                | None ->
                    Ok None
            | Error _ as error -> error
        else
            Ok None

    let rec tryProveGoal args: Result<Map<string, Expression> list option, PrologError> =
        let {
            depth = depth
            trace = trace
            
            goal = goal
            
            scope = scope
            
            seenGoals = seenGoals
            seenExpressions = seenExpressions
            stack = stack
        } = args
        
        if seenGoals |> Set.contains goal then
            Ok None
        else
            match goal with
            | SimpleGoal ("true", [||]) -> Ok (Some [])
            | SimpleGoal ("false", [||]) -> Ok None

            | SimpleGoal (functor, args) ->
                let key = (functor, args.Length)
                let predicates = Scope.lookupPredicates key scope
                
                let success, error, bindings =
                    predicates
                    |> Array.fold (fun (success, error, existingBindings) predicate ->
                        match predicate with
                        | Choice1Of2 userPredicate ->
                            let ruleArgs = {
                                depth = depth + 1
                                trace = trace
                                
                                currentGoal = (functor, args)
                                scope = scope
                                
                                predicate = userPredicate
                                
                                seenGoals = seenGoals |> Set.add goal
                                seenExpressions = seenExpressions 
                                stack = (GoalFrame goal) :: stack 
                            }
                            
                            match testRule ruleArgs with
                            | Ok status ->
                                match status with
                                | Some newBindings ->
                                    (true, error, List.append newBindings existingBindings)
                                | None ->
                                    (success, error, existingBindings)
                            | Error error ->
                                (success, Some error, existingBindings)
                            
                        | Choice2Of2 nativePredicate ->
                            let context: Context = {
                                depth = depth + 1
                                trace = trace
                                
                                seenGoals = seenGoals
                                seenExpressions = seenExpressions
                                
                                stack = (GoalFrame goal) :: stack
                                scope = scope
                            }

                            match nativePredicate context args with
                            | Ok bindings ->
                                match bindings with
                                | Some bindings ->
                                    (true, None, List.append bindings existingBindings)
                                | None ->
                                    (success, None, existingBindings)
                            | Error error ->
                                (success, Some error, existingBindings)
                    ) (false, None, [])
                
                if success then
                    Ok (Some bindings)
                else
                    match error with
                    | Some error ->
                        Error error
                    | None ->
                        Ok None

            | NegatedGoal subGoal ->
                let provability = tryProveGoal {
                    depth = depth + 1
                    trace = trace
                    
                    goal = subGoal
                    scope = scope
                    
                    seenGoals = seenGoals |> Set.add goal
                    seenExpressions = seenExpressions
                    stack = (GoalFrame goal) :: stack
                }
                
                match provability with
                | Ok status ->
                    Ok (Option.invert [] status)
                | Error _ ->
                    provability
            
            | ConjunctionGoal (a, b) ->
                let provabilityA = tryProveGoal {
                    depth = depth + 1
                    trace = trace
                    
                    goal = a
                    scope = scope
                    
                    seenGoals = seenGoals |> Set.add goal
                    seenExpressions = seenExpressions
                    stack = (GoalFrame goal) :: stack
                }
                
                match provabilityA with
                | Ok statusA ->
                    match statusA with
                    | Some bindingsA ->
                        let results = [
                            for bindingSetA in bindingsA do
                                let provabilityB = tryProveGoal {
                                    depth = depth + 1
                                    trace = trace
                                    
                                    goal = b
                                    scope = { emptyScope with parent = Some scope; values = bindingSetA; }
                                    
                                    seenGoals = seenGoals |> Set.add goal
                                    seenExpressions = seenExpressions
                                    stack = (GoalFrame goal) :: stack
                                }
                                
                                match provabilityB with
                                | Ok statusB ->
                                    match statusB with
                                    | Some bindingsB ->
                                        yield Choice1Of2 (bindingsB |> List.map (Map.merge bindingSetA))
                                    | None -> ()
                                | Error _ ->
                                    yield Choice2Of2 provabilityB
                        ]
                        let errors =
                            results
                            |> List.choose (function
                                | Choice1Of2 _ -> None
                                | Choice2Of2 error -> Some error
                            )  
                        let successes =
                            results
                            |> List.choose (function
                                | Choice1Of2 bindings -> Some bindings 
                                | Choice2Of2 _ -> None
                            )
                        
                        match successes with
                        | [] ->
                            match errors with
                            | [] -> Ok None
                            | error :: _ -> error
                        | _ ->
                            successes
                            |> List.collect id
                            |> Some
                            |> Ok
                    | None ->
                        Ok None
                | Error _ ->
                    provabilityA

            | DisjunctionGoal (a, b) ->
                let provability = tryProveGoal {
                    depth = depth + 1
                    trace = trace
                    
                    goal = a
                    scope = scope
                    
                    seenGoals = seenGoals |> Set.add goal
                    seenExpressions = seenExpressions
                    stack = (GoalFrame goal) :: stack
                }
                
                match provability with
                | Ok status ->
                    match status with
                    | Some _ -> provability
                    | None ->
                        tryProveGoal {
                            depth = depth + 1
                            trace = trace
                            
                            goal = b
                            scope = scope
                            
                            seenGoals = seenGoals |> Set.add goal
                            seenExpressions = seenExpressions
                            stack = (GoalFrame goal) :: stack
                        }
                | Error _ ->
                    provability

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
let rec query (goal: Goal) (scope: Scope): Result<Map<string, Expression> list option, PrologError> =
    Internal.tryProveGoal {
        depth = 0
        trace = NoTrace
        goal = goal
        scope = scope
        
        seenGoals = Set.empty
        seenExpressions = Set.empty 
        stack = [] 
    }