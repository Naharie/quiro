module Quiro.Interpreter

open System
open System.Linq.Expressions
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
        predicate: Predicate
        
        scope: Scope
        
        seenGoals: Set<Goal>
        seenExpressions: Set<Expression>
        stack: StackFrame list
    }

    type ExpressionContext = {
        depth: int
        trace: Trace
        
        expression: Expression
        
        scope: Scope
        
        seenGoals: Set<Goal>
        seenExpressions: Set<Expression>
        stack: StackFrame list
    }
    type private FunctionContext = {
        depth: int
        trace: Trace
        
        currentExpr: string * Expression[]
        func: Function
        
        scope: Scope
        
        seenGoals: Set<Goal>
        seenExpressions: Set<Expression>
        stack: StackFrame list
    }

    let rec private substituteVarsInGoal (scope: Scope) (goal: Goal) =
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
        | NegatedGoal goal -> NegatedGoal (substituteVarsInGoal scope goal)
        | ConjunctionGoal(a, b) -> ConjunctionGoal(substituteVarsInGoal scope a, substituteVarsInGoal scope b)
        | DisjunctionGoal(a, b) -> DisjunctionGoal(substituteVarsInGoal scope a, substituteVarsInGoal scope b)
    let rec private substituteVarsInExpr (scope: Scope) (expr: Expression) =
        match expr with
        | Atom _
        | Number _ -> expr
        
        | ListTerm values ->
            ListTerm (values |> List.map (substituteVarsInExpr scope))
        
        | FunctionCall(target, args) ->
            FunctionCall(target, args |> Array.map (substituteVarsInExpr scope))
        
        | Variable name ->
            Scope.lookupValue name scope
            |> Option.defaultValue expr
            
        | ListCons (head, tail) ->
            ListCons(substituteVarsInExpr scope head, substituteVarsInExpr scope tail)
            
        | GoalExpr goal ->
            GoalExpr (substituteVarsInGoal scope goal)
    
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
  
    let private testFunction args : (Expression * Map<string, Expression>) list option =
        let {
            depth = depth
            trace = trace
            
            currentExpr = functor, callArgs
            func = func
            scope = scope
            
            seenGoals = seenGoals
            seenExpressions = seenExpressions
            stack = stack
        } = args
        
        let (Function(_, funcArgs, body)) = func
        let argPairs = Array.zip funcArgs callArgs
        
        /// Build a mapping of variable names used in the goal to the supplied concrete values,
        /// all the while checking that any non-variable arguments the rule demands are satisfied.
        let rawArgBindings =
            argPairs
            |> Array.fold (fun argBindings (funcArg, concreteArg) ->
                match argBindings with
                | Some argBindings ->
                    checkArgMatch funcArg concreteArg argBindings
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
                funcArgs
                |> Array.map(function
                    | Variable name as var ->
                        argBindings
                        |> Map.tryFind name
                        |> Option.defaultValue var
                    | other -> other
                )
            let func = Function(functor, ruleArgs, body)
            
            match trace with
            | All ->
                let isMatch = if isMatch then "true" else "false"
                print depth $"%s{Function.toString func} ? %s{isMatch}"
            | OnlyTrue -> if isMatch then print depth $"%s{Function.toString func}"
            | NoTrace -> ()
        | OnlyTrue | NoTrace -> ()

        // If the function matches then we need to evaluate the function's body.
        if isMatch then
            evaluateExpr {
                depth = depth + 1
                trace = trace
                
                expression = body

                scope = subScope
                
                seenGoals = seenGoals
                seenExpressions = seenExpressions
                stack = (FunctionFrame func) :: stack 
            }
            |> Some
        else
            None
    let evaluateExpr args : (Expression * Map<string, Expression>) list =
        let {
            depth = depth
            trace = trace
            
            expression = expr
            
            scope = scope
            
            seenGoals = seenGoals
            seenExpressions = seenExpressions
            stack = stack
        } = args
        match trace with
        | All ->
            print depth (Expression.toString expr)
        | _ -> ()
        
        match expr with
        | Atom _
        | Number _
        | ListTerm _ ->
            [ expr, Map.empty ]

        | ListCons (head, tail) ->
            let head =
                evaluateExpr {
                    depth = depth + 1
                    trace = trace
                    expression = head
                    scope = scope
                    seenGoals = seenGoals
                    seenExpressions = seenExpressions
                    stack = (ExpressionFrame expr) :: stack 
                }

            head
            |> List.map (fun (head, headVars) ->
                let tail =
                    evaluateExpr {
                        depth = depth + 1
                        trace = trace
                        expression = tail
                        scope = {
                            emptyScope with
                                parent = Some scope
                                values = Map.empty 
                        }
                        seenGoals = seenGoals
                        seenExpressions = seenExpressions
                        stack = (ExpressionFrame expr) :: stack 
                    }
                
                tail
                |> List.map (fun (tail, tailVars) ->
                    match tail with
                    | ListTerm tail ->
                        ListTerm (head :: tail), (Map.merge headVars tailVars)
                    | _ ->
                        ListTerm ([ head; tail ]), (Map.merge headVars tailVars)
                )
            )
            |> List.collect id
        
        | GoalExpr goal ->
            match tryProveGoal {
                depth = depth + 1
                trace = trace
                goal = goal
                scope = scope
                
                seenGoals = seenGoals
                seenExpressions = seenExpressions 
                stack = (ExpressionFrame expr) :: stack
            } with
            | Some bindings ->
                bindings
                |> List.map (fun bindingSet -> Atom "true", bindingSet)
            | None ->
                [ Atom "false", Map.empty ]
        
        | Variable name ->
            scope
            |> Scope.lookupValue name
            |> Option.map (fun value -> [ value, Map.empty ])
            |> Option.defaultWith (fun () -> raise (UnboundVariableException (name, stack)))
    
        | FunctionCall (functor, args) ->
            let key = (functor, args.Length)
            let functions = Scope.lookupFunctions key scope
            
            functions
            |> Array.fold (fun values ``function`` ->
                match ``function`` with
                | Choice1Of2 userFunction ->
                    let funcArgs = {
                        depth = depth + 1
                        trace = trace
                        
                        func = userFunction
                        currentExpr = functor, args 
                        scope = scope
                        
                        seenGoals = seenGoals
                        seenExpressions = seenExpressions |> Set.add expr 
                        stack = (ExpressionFrame expr) :: stack 
                    }
                    
                    match testFunction funcArgs with
                    | Some results -> List.append results values
                    | None -> values
                    
                | Choice2Of2 nativeFunction ->
                    let context: Context = {
                        depth = depth + 1
                        trace = trace
                        
                        seenGoals = seenGoals
                        seenExpressions = seenExpressions
                        
                        stack = (ExpressionFrame expr) :: stack
                        scope = scope
                    }

                    try
                        match nativeFunction context args with
                        | Some results ->
                            let results =
                                results
                                |> List.map (fun expr -> expr, Map.empty)

                            List.append results values
                        | None -> values
                    with
                    | :? PrologException -> reraise()
                    | error ->
                        raise (PrologException(error.Message, stack, error))
            ) []
    
    /// Tests a rule against a goal to see if it matches, creating a table of any required bindings when it does.
    let private testRule args : Map<string, Expression> list option =
        let {
            depth = depth
            trace = trace
            
            currentGoal = _, outerArgs
            scope = scope
            
            predicate = Predicate(ruleFunctor, ruleArgs, ruleGoal)
            
            seenGoals = seenGoals
            seenExpressions = seenExpressions
            stack = stack
        } = args
        
        let argPairs = Array.zip ruleArgs outerArgs
        
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
            let rule = Predicate(ruleFunctor, ruleArgs, substituteVarsInGoal subScope ruleGoal)
            
            match trace with
            | All ->
                let isMatch = if isMatch then "true" else "false"
                print depth $"%s{Predicate.toString rule} ? %s{isMatch}"
            | OnlyTrue -> if isMatch then print depth $"%s{Predicate.toString rule}"
            | NoTrace -> ()
        | OnlyTrue | NoTrace -> ()

        // If the rule matches then we need to try and prove the rule's goal.
        if isMatch then            
            match tryProveGoal {
                depth = depth + 1
                trace = trace
                
                goal = ruleGoal

                scope = subScope
                
                seenGoals = seenGoals
                seenExpressions = seenExpressions
                stack = (GoalFrame ruleGoal) :: stack 
            } with
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
    let rec tryProveGoal args: Map<string, Expression> list option =
        let {
            depth = depth
            trace = trace
            
            goal = goal
            
            scope = scope
            
            seenGoals = seenGoals
            seenExpressions = seenExpressions
            stack = stack
        } = args

        match trace with
        | All ->
            match goal with
            | SimpleGoal ("true", [||]) -> ()
            | SimpleGoal ("false", [||]) -> ()
            | _ ->
                let printGoal = substituteVarsInGoal scope goal
                print depth (Goal.toString printGoal)
        | _ -> ()
        
        let expandedGoal = substituteVarsInGoal scope goal
        
        if seenGoals |> Set.contains expandedGoal then
            None
        else
            match goal with
            | SimpleGoal ("true", [||]) -> Some []
            | SimpleGoal ("false", [||]) -> None

            | SimpleGoal (functor, args) ->
                let key = (functor, args.Length)
                let predicates = Scope.lookupPredicates key scope
                
                let success, bindings =
                    predicates
                    |> Array.fold (fun (success, existingBindings) predicate ->
                        match predicate with
                        | Choice1Of2 userPredicate ->
                            let ruleArgs = {
                                depth = depth + 1
                                trace = trace
                                
                                currentGoal = (functor, args)
                                scope = scope
                                
                                predicate = userPredicate
                                
                                seenGoals = seenGoals |> Set.add expandedGoal
                                seenExpressions = seenExpressions 
                                stack = (GoalFrame expandedGoal) :: stack 
                            }

                            match testRule ruleArgs with
                            | Some newBindings ->
                                (true, List.append newBindings existingBindings)
                            | None ->
                                (success, existingBindings)
                            
                        | Choice2Of2 nativePredicate ->
                            let context: Context = {
                                depth = depth + 1
                                trace = trace
                                
                                seenGoals = seenGoals
                                seenExpressions = seenExpressions
                                
                                stack = (GoalFrame goal) :: stack
                                scope = scope
                            }

                            try
                                match nativePredicate context args with
                                | Some bindings ->
                                    (true, List.append bindings existingBindings)
                                | None ->
                                    (success, existingBindings)
                            with
                            | :? PrologException -> reraise()
                            | error ->
                                raise (PrologException(error.Message, stack, error))
                    ) (false, [])
                
                if success then Some bindings else None

            | NegatedGoal subGoal ->
                let provability = tryProveGoal {
                    depth = depth + 1
                    trace = trace
                    
                    goal = subGoal
                    scope = scope
                    
                    seenGoals = seenGoals |> Set.add expandedGoal
                    seenExpressions = seenExpressions
                    stack = (GoalFrame goal) :: stack
                }
                
                Option.invert [] provability
            
            | ConjunctionGoal (a, b) ->
                let provabilityA = tryProveGoal {
                    depth = depth + 1
                    trace = trace
                    
                    goal = a
                    scope = scope
                    
                    seenGoals = seenGoals |> Set.add expandedGoal
                    seenExpressions = seenExpressions
                    stack = (GoalFrame goal) :: stack
                }
                
                match provabilityA with
                | Some bindingsA ->
                    let results = [
                        for bindingSetA in (Map.empty :: bindingsA) do
                            let provabilityB = tryProveGoal {
                                depth = depth + 1
                                trace = trace
                                
                                goal = b
                                scope = { emptyScope with parent = Some scope; values = bindingSetA; }
                                
                                seenGoals = seenGoals |> Set.add expandedGoal
                                seenExpressions = seenExpressions
                                stack = (GoalFrame expandedGoal) :: stack
                            }
                            
                            match provabilityB with
                            | Some bindingsB ->
                                yield bindingsB |> List.map (Map.merge bindingSetA)
                            | None -> ()
                    ]
                    
                    match results with
                    | [] -> None
                    | _ ->
                        results
                        |> List.collect id
                        |> Some
                | None ->
                    None

            | DisjunctionGoal (a, b) ->
                let provability = tryProveGoal {
                    depth = depth + 1
                    trace = trace
                    
                    goal = a
                    scope = scope
                    
                    seenGoals = seenGoals |> Set.add goal
                    seenExpressions = seenExpressions
                    stack = (GoalFrame expandedGoal) :: stack
                }
                
                match provability with
                | Some _ -> provability
                | None ->
                    tryProveGoal {
                        depth = depth + 1
                        trace = trace
                        
                        goal = b
                        scope = scope
                        
                        seenGoals = seenGoals |> Set.add goal
                        seenExpressions = seenExpressions
                        stack = (GoalFrame expandedGoal) :: stack
                    }

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

/// Query whether a given goal is true or false.
let rec query (goal: Goal) (scope: Scope) (trace: Trace): Map<string, Expression> list option =
    Internal.tryProveGoal {
        depth = 0
        trace = trace
        goal = goal
        scope = scope
        
        seenGoals = Set.empty
        seenExpressions = Set.empty 
        stack = [] 
    }