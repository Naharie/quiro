module rec Quiro.Interpreter

open System
open Quiro.DataTypes

/// Execute a declaration, that is, add it to the list of known declarations, but do not perform a query.
let storeDeclaration declaration (scope: Scope) =
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

let private writeDebugInformation indentation (text: string) =
    let prefix = String.replicate indentation "\t"
    Console.Write(prefix)
    Console.WriteLine(text)
 
type InstantiatedGoal = string * PrologExpression list
type InstantiatedFunction = string * PrologExpression

type GoalInterpreterContext = Goal * InterpreterContext
type private RuleInterpreterContext = (string * PrologExpression list) * Predicate * InterpreterContext 

type ExpressionInterpreterContext = PrologExpression * InterpreterContext
type private FunctionInterpreterContext = (string * PrologExpression list) * Function * InterpreterContext

/// Substitutes all variables in the given goal that are defined in the provided scope.
let rec private substituteVariablesInGoal (scope: Scope) (goal: Goal) =
    match goal with
    | DirectGoal(functor, args) ->
        DirectGoal(
            functor,
            args
            |> List.map(function
                | Variable name as var ->
                    Scope.lookupValue name scope
                    |> Option.defaultValue var
                | other -> other
            )
        )
    | DynamicGoal(functor, args) ->
        DynamicGoal(
            functor,
            args
            |> List.map(function
                | Variable name as var ->
                    Scope.lookupValue name scope
                    |> Option.defaultValue var
                | other -> other
            )
        )
    | NegatedGoal goal -> NegatedGoal (substituteVariablesInGoal scope goal)
    | ConjunctionGoal(a, b) -> ConjunctionGoal(substituteVariablesInGoal scope a, substituteVariablesInGoal scope b)
    | DisjunctionGoal(a, b) -> DisjunctionGoal(substituteVariablesInGoal scope a, substituteVariablesInGoal scope b)
/// Substitutes all variables in the given expression that are defined in the provided scope.
let rec private substituteVariablesInExpression (scope: Scope) (expr: PrologExpression) =
    match expr with
    | Atom _
    | Number _
    | Text _ -> expr
    
    | ListTerm values ->
        ListTerm (values |> List.map (substituteVariablesInExpression scope))
    
    | FunctionCall(target, args) ->
        FunctionCall(target, args |> List.map (substituteVariablesInExpression scope))
    | DynamicFunctionCall(target, args) ->
        DynamicFunctionCall(target, args |> List.map (substituteVariablesInExpression scope))
    
    | Variable name ->
        Scope.lookupValue name scope
        |> Option.defaultValue expr
        
    | ListCons (head, tail) ->
        ListCons(substituteVariablesInExpression scope head, substituteVariablesInExpression scope tail)
        
    | GoalExpr goal ->
        GoalExpr (substituteVariablesInGoal scope goal)

/// Determines if the specified value matches the given argument pattern, collecting any resulting input bindings into the provided `computedBindings`.
/// The given context is used when needing to throw an error regarding insufficient substantiation.
let rec private checkIfValueMatchesArgument term (context: InterpreterContext) computedBindings argument value =
    match argument with
    // If the argument is a variable, then either we should bind the concrete value, or the "value" is itself a variable,
    // in which case we don't want to bind it until later when we are collecting outputs from a predicate.
    | Variable argumentAsAVariable ->
        // If a variable name is an underscore, then it is actually a wildcard.
        // If the value is also a variable, that is, is expecting output, then the term is insufficiently substantiated.
        // Otherwise, pass along success with no additional bindings.
        match argumentAsAVariable with
        | "_" ->
            match value with
            | Variable _ ->
                raise (InsufficientSubstantiationException(term, context.stack))
            | _ ->
                Some computedBindings
        | _ ->
            match value with
            | Variable _ -> Some computedBindings
            | _ ->
                Some (computedBindings |> Map.add argumentAsAVariable value)
    
    // For lists pattern matching, either the value is a list or it is not, and if it is a list, we need to recursively check for any pattern matching in the head and tail of the expression.
    | ListCons (argumentHead, argumentTail) ->
        match value with
        | ListTerm (valueHead :: valueTail) ->
            match checkIfValueMatchesArgument term context computedBindings argumentHead valueHead with
            | Some argBindings ->
                checkIfValueMatchesArgument term context argBindings argumentTail (ListTerm valueTail)
            | None -> None
        | _ ->
            None

    // For whole list patterns, we need an equally sized list as an input and when we get one we need to recursively check each entry of the argument for pattern matching.
    | ListTerm argumentItems ->
        match value with
        | ListTerm valueItems ->
            if argumentItems.Length <> valueItems.Length then
                None
            else
                List.zip argumentItems valueItems
                |> List.fold (fun argBindings (ruleTerm, concreteTerm) ->
                    match argBindings with
                    | Some argBindings ->
                        checkIfValueMatchesArgument term context argBindings ruleTerm concreteTerm
                    | None -> None
                ) (Some computedBindings)
        | _ ->
            None
    
    // For all other cases, simply ensure that either a: the value being tested is an output var or b: the value being tested matches the value provided as an argument pattern.
    | _ ->
        match value with
        | Variable _ -> Some computedBindings
        | _ ->
            if argument = value then Some computedBindings else None

let rec evalArgs (context: InterpreterContext) args : PrologExpression list list =
    match args with
    | [] -> [ [] ]
    | arg :: args ->
        let evaluatedArg = evaluateExpression (arg, {
            depth = context.depth + 1
            debugLevel = context.debugLevel
            
            scope = context.scope
            
            seenGoals = context.seenGoals
            seenFunctions = context.seenFunctions 
            stack = (NativeFunction "," :: context.stack)
        })
        
        evaluatedArg
        |> List.map (fun (value, bindings) ->
            let scope = {
                context.scope with
                    values = Map.merge context.scope.values bindings 
            }
            let context = { context with scope = scope }
            
            evalArgs context args
            |> List.map (fun argSet -> value :: argSet)
        )
        |> List.collect id

let private testFunction ((functor, callArgs), func, context) : (PrologExpression * Map<string, PrologExpression>) list option =
    let {
        depth = depth
        debugLevel = trace
        
        scope = scope
        
        seenGoals = seenGoals
        seenFunctions = seenFunctions
        stack = stack
    } = context
    
    let (Function(_, funcArgs, body)) = func
    let argPairs = List.zip funcArgs callArgs
    
    /// Build a mapping of variable names used in the goal to the supplied concrete values,
    /// all the while checking that any non-variable arguments the rule demands are satisfied.
    let rawArgBindings =
        argPairs
        |> List.fold (fun argBindings (funcArg, concreteArg) ->
            match argBindings with
            | Some argBindings ->
                checkIfValueMatchesArgument functor context argBindings funcArg concreteArg
            | None -> None
        ) (Some Map.empty)
    let isMatch, argBindings =
        match rawArgBindings with
        | Some bindings -> true, bindings
        | None -> false, Map.empty
     
    let subScope = { scope with values = argBindings  }
    
    match trace with
    | All | OnlyTrue ->
        let ruleArgs =
            funcArgs
            |> List.map(function
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
            writeDebugInformation depth $"%s{Function.toString func} ? %s{isMatch}"
        | OnlyTrue -> if isMatch then writeDebugInformation depth $"%s{Function.toString func}"
        | RuleOnly | NoDebugInfo -> ()
    | RuleOnly | OnlyTrue | NoDebugInfo -> ()

    // If the function matches then we need to evaluate the function's body.
    if isMatch then
        evaluateExpression (body, {
            depth = depth + 1
            debugLevel = trace
            
            scope = subScope
            
            seenGoals = seenGoals
            seenFunctions = seenFunctions 
            stack = (FunctionFrame func) :: stack 
        })
        |> Some
    else
        None
let evaluateExpression (expression, context) : (PrologExpression * Map<string, PrologExpression>) list =
    let {
        depth = depth
        debugLevel = debugLevel
        
        scope = scope
        
        seenGoals = seenGoals
        seenFunctions = seenFunctions
        stack = stack
    } = context
    
    match debugLevel with
    | All ->
        writeDebugInformation depth (PrologExpression.toString expression)
    | _ -> ()
    
    match expression with
    // Functions can be declared without arguments, and so simply invoking the name is enough to cause execution of the function.
    | Atom name when not (Array.isEmpty (Scope.lookupFunctions (name, 0) scope)) ->
        evaluateExpression (FunctionCall(name, []), { context with depth = depth + 1; })
    
    | Atom _
    | Number _
    | ListTerm _
    | Text _ ->
        [ expression, Map.empty ]

    | ListCons (head, tail) ->
        let head =
            evaluateExpression (head, {
                depth = depth + 1
                debugLevel = debugLevel
                scope = scope
                
                seenGoals = seenGoals
                seenFunctions = seenFunctions 
                stack = (ExpressionFrame expression) :: stack 
            })

        head
        |> List.map (fun (head, headVars) ->
            let tail =
                evaluateExpression (tail, {
                    depth = depth + 1
                    debugLevel = debugLevel
                    scope = scope
                    
                    seenGoals = seenGoals
                    seenFunctions = seenFunctions 
                    stack = (ExpressionFrame expression) :: stack 
                })
            
            tail
            |> List.map (fun (tail, tailVars) ->
                match tail with
                | ListTerm tail ->
                    ListTerm (head :: tail), (Map.merge headVars tailVars)
                | _ ->
                    ListTerm [ head; tail ], (Map.merge headVars tailVars)
            )
        )
        |> List.collect id
    
    | GoalExpr goal ->
        match tryProveGoal (goal, {
            depth = depth + 1
            debugLevel = debugLevel
            scope = scope
            
            seenGoals = seenGoals
            seenFunctions = seenFunctions 
            stack = (ExpressionFrame expression) :: stack
        }) with
        | Some bindings ->
            bindings
            |> List.map (fun bindingSet -> Atom "true", bindingSet)
        | None ->
            [ Atom "false", Map.empty ]
    
    | Variable name ->
        scope
        |> Scope.lookupValue name
        |> Option.map (fun value -> [ value, Map.empty ])
        |> Option.defaultValue [ expression, Map.empty ]

    | FunctionCall (functor, args) ->            
        let key = (functor, args.Length)
        let functions = Scope.lookupFunctions key scope
        
        evalArgs {
            depth = depth + 1
            debugLevel = debugLevel
            scope = scope
            
            seenGoals = seenGoals
            seenFunctions = seenFunctions 
            stack = (ExpressionFrame expression) :: stack
        } args
        |> List.map (fun args ->
            // TODO: Is this correct?
            if seenFunctions |> Map.containsKey (functor, args) then
                []
            else
                functions
                |> Array.fold (fun values ``function`` ->
                    match ``function`` with
                    | Choice1Of2 userFunction ->
                        let functionContext = {
                            depth = depth + 1
                            debugLevel = debugLevel
                            
                            scope = scope
                             
                            seenGoals = seenGoals
                            seenFunctions = seenFunctions |> Map.add (functor, args) Unresolved 
                            stack = (ExpressionFrame expression) :: stack 
                        }
                        
                        match testFunction ((functor, args), userFunction, functionContext) with
                        | Some results -> List.append results values
                        | None -> values
                        
                    | Choice2Of2 nativeFunction ->
                        let context: InterpreterContext = {
                            depth = depth + 1
                            debugLevel = debugLevel
                            
                            stack = (ExpressionFrame expression) :: stack
                            
                            seenGoals = seenGoals
                            seenFunctions = seenFunctions |> Map.add (functor, args) Unresolved 
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
        )
        |> List.collect id

    | DynamicFunctionCall (var, funcArgs) ->
        match Scope.lookupValue var scope with
        | Some (Atom name) ->
            evaluateExpression (FunctionCall(name, funcArgs), context)
           
        | Some _ ->
            let message = "Can't perform a dynamic function invocation against a variable bound to something other than an atom!"
            raise (PrologException(message, stack, InvalidOperationException(message)))
            
        | None ->
            raise (UnboundVariableException(var, stack))

/// Tests a rule against a goal to see if it matches, creating a table of any required bindings when it does.
let private testRule (((predicateHead, outerArgs), predicate, context): RuleInterpreterContext) : Map<string, PrologExpression> list option =
    let (Predicate(ruleFunctor, ruleArgs, ruleGoal)) = predicate
    let {
        depth = depth
        debugLevel = trace

        scope = scope
                
        seenGoals = seenGoals
        seenFunctions = seenFunctions
        stack = stack
    } = context
    
    let argPairs = List.zip ruleArgs outerArgs
    
    /// Build a mapping of variable names used in the goal to the supplied concrete values,
    /// all the while checking that any non-variable arguments the rule demands are satisfied.
    let rawArgBindings =
        argPairs
        |> List.fold (fun argBindings (ruleArg, concreteArg) ->
            match argBindings with
            | Some argBindings ->
                match concreteArg with
                | Variable name ->
                    let concreteArg =
                        Scope.lookupValue name scope
                        |> Option.defaultValue concreteArg
                
                    checkIfValueMatchesArgument predicateHead context argBindings ruleArg concreteArg
                | _ ->
                    checkIfValueMatchesArgument predicateHead context argBindings ruleArg concreteArg
            | None -> None
        ) (Some Map.empty)
    
    let isMatch, argBindings =
        match rawArgBindings with
        | Some bindings -> true, bindings
        | None -> false, Map.empty

    let subScope = { scope with values = argBindings  }
    
    match trace with
    | All | RuleOnly | OnlyTrue ->
        let rule = Predicate(ruleFunctor, outerArgs, substituteVariablesInGoal subScope ruleGoal)
        
        match trace with
        | All | RuleOnly ->
            let isMatch = if isMatch then "true" else "false"
            writeDebugInformation depth $"%s{Predicate.toString rule} ? %s{isMatch}"
        | OnlyTrue -> if isMatch then writeDebugInformation depth $"%s{Predicate.toString rule}"
        | NoDebugInfo -> ()
    | OnlyTrue | NoDebugInfo -> ()

    // If the rule matches then we need to try and prove the rule's goal.
    if isMatch then            
        match tryProveGoal (ruleGoal, {
            depth = depth + 1
            debugLevel = trace
            
            scope = subScope
            
            seenGoals = seenGoals
            seenFunctions = seenFunctions 
            stack = (GoalFrame ruleGoal) :: stack 
        }) with
        | Some newBindings ->
            let newBindings =
                match newBindings with
                | [] -> [ Map.empty ]
                | _ -> newBindings
            
            newBindings
            |> List.map (fun bindingGroup ->
                // If the goal is proven, then we need to grab all variables or values from the inner scope and copy over the value or the value the variable points to the outer scope.
                argPairs
                |> List.choose (fun (ruleArg, outerArg) ->
                    match outerArg, ruleArg with
                    | Variable name, Variable innerName ->
                        bindingGroup |> Map.tryFind innerName
                        |> Option.map (fun value -> name, value)
                    | Variable name, _ -> Some (name, ruleArg)
                    | _ -> None
                )
                |> Map.ofList
            )
            |> Some
        | None -> None
    else
        None
let rec tryProveGoal ((goal, context): GoalInterpreterContext): Map<string, PrologExpression> list option =
    let {
        depth = depth
        debugLevel = debugLevel
        
        scope = scope
        
        seenGoals = seenGoals
        seenFunctions = seenFunctions
        stack = stack
    } = context
    
    match debugLevel with
    | All ->
        match goal with
        | DirectGoal ("true", []) -> ()
        | DirectGoal ("false", []) -> ()
        | _ ->
            let printGoal = substituteVariablesInGoal scope goal
            writeDebugInformation depth (Goal.toString printGoal)
    | _ -> ()
    
    let expandedGoal = substituteVariablesInGoal scope goal
    
    match goal with
    | DirectGoal ("true", []) -> Some [ Map.empty ]
    | DirectGoal ("false", []) -> None

    | DirectGoal (functor, args) ->
        let key = (functor, args.Length)
        let predicates = Scope.lookupPredicates key scope
        
        evalArgs {
            depth = depth + 1
            debugLevel = debugLevel
            scope = scope
            
            seenGoals = seenGoals
            seenFunctions = seenFunctions 
            stack = (GoalFrame goal) :: stack 
        } args
        |> List.choose (fun args ->
            // TODO: Is this correct?
            if seenGoals |> Map.containsKey (functor, args) then
                None
            else        
                let success, bindings =
                    predicates
                    |> Array.fold (fun (success, existingBindings) predicate ->
                        match predicate with
                        | Choice1Of2 userPredicate ->
                            let ruleContext = {
                                context with
                                    depth = depth + 1                                    
                                    seenGoals = seenGoals |> Map.add (functor, args) Pending 
                                    stack = (GoalFrame expandedGoal) :: stack 
                            }

                            match testRule ((functor, args), userPredicate, ruleContext) with
                            | Some newBindings ->
                                (true, List.append newBindings existingBindings)
                            | None ->
                                (success, existingBindings)
                            
                        | Choice2Of2 nativePredicate ->
                            let context: InterpreterContext = {
                                context with
                                    depth = depth + 1
                                    stack = (GoalFrame goal) :: stack
                                    seenGoals = seenGoals |> Map.add (functor, args) Pending
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
        )
        |> List.collect id
        |> List.noneIfEmpty
    | DynamicGoal (var, goalArgs) ->
        match Scope.lookupValue var scope with
        | Some (Atom name) ->
            tryProveGoal (DirectGoal(name, goalArgs), context)
           
        | Some _ ->
            let message = "Can't perform a dynamic predicate invocation against a variable bound to something other than an atom!"
            raise (PrologException(message, stack, InvalidOperationException(message)))
            
        | None ->
            raise (UnboundVariableException(var, stack))
    
    // TODO: Don't use expanded goal, instead save the scope in case we need to substitute later for a stacktrace,
    // potentially allowing us to avoid iterating the goal tree twice if an exception does *not* occur.
    
    | NegatedGoal subGoal ->
        let provability = tryProveGoal (subGoal, {
            context with
                depth = depth + 1 
                stack = (GoalFrame goal) :: stack
        })
        
        Option.invert [] provability
    
    | ConjunctionGoal (a, b) ->
        let provabilityA = tryProveGoal (a, {
            context with
                depth = depth + 1
                stack = (GoalFrame goal) :: stack
        })
        
        match provabilityA with
        | Some bindingsA ->
            let results = [
                let bindingsA =
                    match bindingsA with
                    | [] -> [ Map.empty ]
                    | _ -> bindingsA
                
                for bindingSetA in bindingsA do
                    let provabilityB = tryProveGoal (b, {
                        context with
                            depth = depth + 1
                            scope = { scope with values = Map.merge scope.values bindingSetA }
                            stack = (GoalFrame expandedGoal) :: stack
                    })
                    
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
        let provability = tryProveGoal (a, {
            context with
                depth = depth + 1
                stack = (GoalFrame expandedGoal) :: stack
        })
        
        match provability with
        | Some _ -> provability
        | None ->
            tryProveGoal (b, {
                context with
                    depth = depth + 1
                    stack = (GoalFrame expandedGoal) :: stack
            })

/// Query whether a given goal is provable or not.
let rec query (goal: Goal) (scope: Scope) (trace: DebugLevel): Map<string, PrologExpression> list option =
    tryProveGoal (goal, {
        depth = 0
        debugLevel = trace
        scope = scope
         
        seenGoals = Map.empty
        seenFunctions = Map.empty
        stack = [] 
    })