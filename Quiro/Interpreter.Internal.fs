module rec Quiro.Interpreter.Internal

open System
open System.Collections.Generic
open Functional
open Quiro
open Quiro.AST

let rec reifyExpr (ast: PrologExprAST): PrologValue =
    match ast.exprKind with
    | ExprAtom atom -> Atom atom
    | ExprNumber number -> Number number
    | ExprText text -> Text text
    | ExprListTerm elements -> ListTerm (List.map reifyExpr elements)
    | ExprTerm (functor, args) -> Term(functor, List.map reifyExpr args)
    | ExprVariable variable -> Variable variable
    | ExprListCons (head, tail) -> ListCons(reifyExpr head, reifyExpr tail)
    | ExprPlaceholder ->
        raise (PrologException $"Incomplete expression (line %i{ast.location.line}, column %i{ast.location.column})")
let reifyGoal (ast: PrologGoalAST): Goal =
    match ast.goalKind with
    | GoalSimple (functor, args) -> SimpleGoal(functor, List.map reifyExpr args)
    | GoalNegated goal -> NegatedGoal (reifyGoal goal)
    
    | GoalConjunction goals -> ConjunctionGoal(Array.map reifyGoal goals)
    | GoalDisjunction goals -> DisjunctionGoal(Array.map reifyGoal goals)
    
    | GoalPlaceholder ->
        raise (PrologException $"Incomplete goal (line %i{ast.location.line}, column %i{ast.location.column})")
let reifyDCG (ast: DCGAST) =
    match ast.dcgKind with
    | DCGTerm term -> DCG.Term term
    | DCGCall (functor, args) -> DCG.Call(functor, args |> List.map reifyExpr)
    | DCGGoal goal -> DCG.Goal (reifyGoal goal)
    | DCGList values -> DCG.List (values |> List.map reifyExpr)
    | DCGSequence nested -> DCG.Sequence (nested |> Array.map reifyDCG)

let writeDebugInformation indentation (text: string) =
    let prefix = String.replicate indentation "\t"
    Console.Write(prefix)
    Console.WriteLine(text)

/// Substitutes all variables in the given goal that are defined in the provided scope.
let rec substituteVariablesInGoal (scope: Scope) (goal: Goal) =
    match goal with
    | SimpleGoal(functor, args) ->
        SimpleGoal(
            functor,
            args
            |> List.map(function
                | Variable name as var ->
                    scope
                    |> Scope.lookupValue name
                    |> ValueOption.defaultValue var
                | other -> other
            )
        )

    | NegatedGoal goal -> NegatedGoal (substituteVariablesInGoal scope goal)
    | ConjunctionGoal goals ->
        ConjunctionGoal(goals |> Array.map (substituteVariablesInGoal scope))
    | DisjunctionGoal goals ->
        DisjunctionGoal(goals |> Array.map (substituteVariablesInGoal scope))
/// Substitutes all variables in the given expression that are defined in the provided scope.
let rec substituteVariablesInExpression (scope: Scope) (expr: PrologValue) =
    match expr with
    | Atom _
    | Number _
    | Text _ -> expr
    
    | ListTerm values ->
        ListTerm (values |> List.map (substituteVariablesInExpression scope))
    
    | Term(target, args) ->
        Term(target, args |> List.map (substituteVariablesInExpression scope))
    
    | Variable name ->
        scope
        |> Scope.lookupValue name
        |> ValueOption.defaultValue expr
        
    | ListCons (head, tail) ->
        ListCons(substituteVariablesInExpression scope head, substituteVariablesInExpression scope tail)

let mergeBindings a b =
    a |> ValueOption.bind (fun a -> b |> ValueOption.map (Map.merge a))    

let rec assignVarFromValue allowOutVar var value =
    match var with
    | Variable "_" -> ValueSome Map.empty
    | Variable name ->
        match value with
        | Variable _ -> ValueSome Map.empty
        | _ -> Map.ofArray [| name, value |] |> ValueSome 
    
    | ListCons (varHead, varTail) ->
        match value with
        | ListCons (valueHead, valueTail) | ListTerm (valueHead :: Wrap ListTerm valueTail) ->
            mergeBindings
                (assignVarFromValue allowOutVar varHead valueHead)
                (assignVarFromValue allowOutVar varTail valueTail)
                
        | Variable _ when allowOutVar -> ValueSome Map.empty
        | _ -> ValueNone

    | ListTerm varItems ->
        match value with
        | ListTerm valueItems ->
            if varItems.Length <> valueItems.Length then ValueNone
            else assignVarsFromValues allowOutVar varItems valueItems

        | ListCons (valueHead, valueTail) ->
            match varItems with
            | varHead :: varTail ->
                mergeBindings
                    (assignVarFromValue allowOutVar varHead valueHead)
                    (assignVarFromValue allowOutVar (ListTerm varTail) valueTail)
            | [] -> ValueNone
            
        | Variable _ when allowOutVar -> ValueSome Map.empty
        | _ -> ValueNone
    
    | Term(varFunctor, varParameters) ->
        match value with
        | Term(valueFunctor, valueParameters) ->
            if varFunctor = "_" || varFunctor = valueFunctor then
                assignVarsFromValues allowOutVar varParameters valueParameters
            else ValueNone
            
        | Variable _ when allowOutVar -> ValueSome Map.empty
        | _ -> ValueNone
    
    | _ ->
        if allowOutVar && value.IsVariable || var = value then
            ValueSome (Map.ofArray Array.empty)
        else
            ValueNone
let rec assignVarsFromValues allowOutVar vars values =
    if vars.Length <> values.Length then
        ValueNone
    else
        List.fold2 (fun bindings varItem valueItem ->
            match bindings with
            | ValueNone -> ValueNone
            | ValueSome _ ->
                mergeBindings bindings (assignVarFromValue allowOutVar varItem valueItem)
        ) (ValueSome Map.empty) vars values

let rec assignVarFromGoal allowOutVar var goal =
    match var with
    | SimpleGoal(varFunctor, varParameters) ->
        match goal with
        | SimpleGoal (valueFunctor, valueParameters) ->
            if varFunctor = "_" || varFunctor = valueFunctor then
                assignVarsFromValues allowOutVar varParameters valueParameters
            else ValueNone
        | _ -> ValueNone

    | NegatedGoal varSubGoal ->
        match goal with
        | NegatedGoal valueSubGoal ->
            assignVarFromGoal allowOutVar varSubGoal valueSubGoal
        | _ -> ValueNone

    | ConjunctionGoal varGoals ->
        match goal with
        | ConjunctionGoal valueGoals ->
            assignVarsFromGoals allowOutVar varGoals valueGoals
        | _ -> ValueNone

    | DisjunctionGoal varGoals ->
        match goal with
        | DisjunctionGoal valueGoals ->
            assignVarsFromGoals allowOutVar varGoals valueGoals
        | _ -> ValueNone
let rec assignVarsFromGoals allowOutVar vars goals =
    if vars.Length <> goals.Length then
        ValueNone
    else 
        Array.fold2 (fun bindings varItem valueItem ->
            match bindings with
            | ValueNone -> ValueNone
            | ValueSome _ ->
                mergeBindings bindings (assignVarFromGoal allowOutVar varItem valueItem)
        ) (ValueSome Map.empty) vars goals

let emptySuccess = [| Map.empty |]

let tryProvePredicate (context: InterpreterContext) predicate argValues =
    let args, test = predicate                 
    let potentialBindings = assignVarsFromValues true args argValues

    match potentialBindings with
    | ValueSome bindings ->
        match test with
        | SimpleGoal ("true", []) ->
            let updatedScope = context.scope.CreateChild bindings
            let instantiatedArgs = args |> List.map (substituteVariablesInExpression updatedScope)
            let resultingBindings = assignVarsFromValues false argValues instantiatedArgs

            match resultingBindings with
            | ValueSome producedBindings ->
                ValueSome [| producedBindings |]
            | ValueNone -> ValueNone
        | SimpleGoal ("false", []) -> ValueNone
        | _ ->
            let contextWithBindings = context.NestScope bindings
            
            match tryProveGoal contextWithBindings test with
            | ValueSome testGoalBindings ->
                testGoalBindings
                |> Array.choose (fun bindingSet ->
                    let childScope = context.scope.CreateChild bindingSet
                    let instantiatedArgs = args |> List.map (substituteVariablesInExpression childScope)
                    let resultingBindings = assignVarsFromValues false argValues instantiatedArgs

                    resultingBindings
                    |> Option.ofValueOption
                )
                |> function | [||] -> ValueNone | v -> ValueSome v
            | ValueNone -> ValueNone
    | ValueNone -> ValueNone
let rec tryProveGoal context goal : Map<string, PrologValue>[] voption =
    match goal with
    | SimpleGoal (("true" | "repeat" | "!"), []) -> ValueSome emptySuccess
    | SimpleGoal (("false" | "fail"), []) -> ValueNone

    | SimpleGoal (functor, argValues) ->
        let key = (functor, argValues.Length)
        let userPredicates = StoredTerms.lookupPredicates context.terms key
        let nativePredicates = StoredTerms.lookupNativePredicates context.terms key
        
        let producedBindings = ResizeArray()
        let updatedContext = { context with stack = (PredicateFrame key) :: context.stack }

        let instantiatedArgValues = argValues |> List.map (substituteVariablesInExpression context.scope)
        
        for userPredicate in userPredicates do
            match tryProvePredicate updatedContext userPredicate instantiatedArgValues with
            | ValueSome newBindings ->
                // By wrapping as a ReadOnlySpan instead of using the more generic overload we avoid an IEnumerator<_> allocation
                producedBindings.AddRange(ReadOnlySpan(newBindings))
            | ValueNone -> ()

        for nativePredicate in nativePredicates do
            match nativePredicate updatedContext instantiatedArgValues with
            | ValueSome newBindings ->
                // Same trick as before
                producedBindings.AddRange(ReadOnlySpan(newBindings))
            | ValueNone -> ()

        if producedBindings.Count = 0 then
            ValueNone
        else
            ValueSome (producedBindings.ToArray())
        
    | NegatedGoal subGoal ->
        match tryProveGoal context subGoal with
        | ValueSome _ -> ValueNone
        | ValueNone -> ValueSome emptySuccess
        
    | ConjunctionGoal goals ->
        // Note: "repeat" choice points and cuts "!"
        
        let workingSets = Stack()
        let repeats = Stack()
        let results = ResizeArray()
            
        if goals.Length = 1 then
            tryProveGoal context goals[0]
        else
            workingSets.Push ([| Map.empty |], 0, 0)
            
            while workingSets.Count > 0 do
                let bindingSets, goalIndex, setIndex = workingSets.Peek()
                let repeatIndex, repeatCount = if repeats.Count > 0 then repeats.Peek() else -1, -1

                if setIndex >= bindingSets.Length && repeatIndex = goalIndex - 1 && results.Count = repeatCount then
                    workingSets.Pop() |> ignore
                    workingSets.Push (bindingSets, goalIndex, 0)
                elif setIndex < bindingSets.Length then
                    let bindingSet = bindingSets[setIndex]
                    let goal = goals[goalIndex]
                    
                    match goal with
                    // A cut means we immediately discard all choice points
                    | SimpleGoal("!", []) ->
                        let temporary = Stack()
                        
                        while workingSets.Count > 0 do
                            let b, g, _ = workingSets.Pop()
                            temporary.Push((b, g, b.Length))
                        
                        while temporary.Count > 0 do
                            workingSets.Push(temporary.Pop())

                        if goalIndex + 1 < goals.Length then
                            workingSets.Pop() |> ignore
                            workingSets.Push ([| bindingSets[setIndex] |], goalIndex + 1, 0)
                            
                    | SimpleGoal("repeat", []) ->
                        repeats.Push(goalIndex, results.Count)
                        
                        if goalIndex + 1 < goals.Length then
                            workingSets.Pop() |> ignore
                            workingSets.Push (bindingSets, goalIndex + 1, 0)
                            
                    | _ ->
                        let contextWithUpdatedBindings = context.NestScope bindingSet
                        let potentialGoalResults = tryProveGoal contextWithUpdatedBindings goal
                        
                        workingSets.Pop() |> ignore
                        workingSets.Push (bindingSets, goalIndex, setIndex + 1)
                        
                        match potentialGoalResults with
                        | ValueSome goalResults ->
                            let newBindingSets =
                                goalResults
                                |> Array.map (Map.merge bindingSet)

                            if goalIndex + 1 >= goals.Length then
                                results.AddRange(ReadOnlySpan(newBindingSets))
                            else
                                workingSets.Push (newBindingSets, goalIndex + 1, 0)
                        | ValueNone -> ()
                else
                    workingSets.Pop() |> ignore

            if results.Count = 0 then ValueNone else ValueSome (results.ToArray())
    
    | DisjunctionGoal goals ->
        let mutable result = ValueNone
        let mutable index = 0
        
        while index < goals.Length && result.IsNone do
            result <- tryProveGoal context goals[index]
            index <- index + 1

        result