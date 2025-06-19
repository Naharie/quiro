module rec Quiro.Interpreter.Internal

open System
open System.Collections.Generic
open Functional
open Microsoft.FSharp.Core
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
        SimpleGoal(functor, args |> List.map(substituteVariablesInExpression scope))
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

let private mergeBindings a b =
    a |> ValueOption.bind (fun a ->
        b |> ValueOption.bind (
            Map.fold (fun map key value ->
                match map with
                | ValueNone -> ValueNone
                | ValueSome map ->
                    match map |> Map.tryFind key with
                    | None ->
                        map |> Map.add key value |> ValueSome
                    | Some existing ->
                        if value = existing then ValueSome map else ValueNone
            ) (ValueSome a)
        )
    )    

[<Struct>] type OutVarSupport = InVarOnly | AllowOutVar

let hasFreeVariables scope expr =
    match expr with
    | Atom _ | Number _ | Text _ -> false
    | Variable var -> (Scope.lookupValue var scope) = ValueNone
    
    | ListCons(a, b) -> hasFreeVariables scope a || hasFreeVariables scope b
    
    | ListTerm values
    | Term (_, values) -> values |> List.exists (hasFreeVariables scope)

let rec assignVarFromValue (scope: Scope) (outVar: OutVarSupport) (var: PrologValue) (value: PrologValue) =
    if hasFreeVariables scope value then
        match outVar with
        | InVarOnly -> ValueNone
        | AllowOutVar -> ValueSome Map.empty
    else
    
    match var with
    | Variable "_" -> ValueSome Map.empty
    | Variable name -> Map.ofArray [| name, value |] |> ValueSome 
    
    | ListCons (varHead, varTail) ->
        match value with
        | ListCons (valueHead, valueTail) | ListTerm (valueHead :: Wrap ListTerm valueTail) ->
            mergeBindings
                (assignVarFromValue scope outVar varHead valueHead)
                (assignVarFromValue scope outVar varTail valueTail)
                
        | Variable _ when outVar.IsAllowOutVar -> ValueSome Map.empty
        | _ -> ValueNone

    | ListTerm varItems ->
        match value with
        | ListTerm valueItems ->
            if varItems.Length <> valueItems.Length then ValueNone
            else assignVarsFromValues scope outVar varItems valueItems

        | ListCons (valueHead, valueTail) ->
            match varItems with
            | varHead :: varTail ->
                mergeBindings
                    (assignVarFromValue scope outVar varHead valueHead)
                    (assignVarFromValue scope outVar (ListTerm varTail) valueTail)
            | [] -> ValueNone
            
        | Variable _ when outVar.IsAllowOutVar -> ValueSome Map.empty
        | _ -> ValueNone
    
    | Term(varFunctor, varParameters) ->
        match value with
        | Term(valueFunctor, valueParameters) ->
            if varFunctor = "_" || varFunctor = valueFunctor then
                assignVarsFromValues scope outVar varParameters valueParameters
            else ValueNone
            
        | Variable _ when outVar.IsAllowOutVar -> ValueSome Map.empty
        | _ -> ValueNone
    
    | _ ->
        if outVar.IsAllowOutVar && value.IsVariable || var = value then
            ValueSome (Map.ofArray Array.empty)
        else
            ValueNone
let rec assignVarsFromValues (scope: Scope) (outVar: OutVarSupport) (vars: PrologValue list) (values: PrologValue list) =
    if vars.Length <> values.Length then
        ValueNone
    else
        List.fold2 (fun bindings varItem valueItem ->
            match bindings with
            | ValueNone -> ValueNone
            | ValueSome _ ->
                mergeBindings bindings (assignVarFromValue scope outVar varItem valueItem)
        ) (ValueSome Map.empty) vars values

let emptySuccess = [| Map.empty |]

let evaluateExpr (context: InterpreterContext) expr =
    match expr with
    | Atom _
    | Number _
    | Text _ -> expr
    
    | ListCons(head, tail) ->
        let evaluatedHead = evaluateExpr context head
        let evaluatedTail = evaluateExpr context tail
        
        match evaluatedTail with
        | ListTerm tailValue ->
            ListTerm (evaluatedHead :: tailValue)
        | Atom "nil" ->
            ListTerm [ evaluatedHead ]
        | _ ->
            ListTerm [ evaluatedHead; evaluatedTail ]
    
    | ListTerm values ->
        ListTerm (values |> List.map (evaluateExpr context))
        
    | Variable name ->
        Scope.lookupValue name context.scope
        |> ValueOption.map (evaluateExpr context)
        |> ValueOption.defaultValue expr

    | Term (functor, args) ->
        let functions = StoredTerms.lookupFunctions context.terms (functor, args.Length)
        
        if functions.Count = 0 then expr
        else
            functions
            |> Seq.tryPick (fun func -> func context args |> Option.ofValueOption)
            |> Option.defaultValue expr

let tryProvePredicate (context: InterpreterContext) predicate argValues: Map<string, PrologValue> seq voption =
    let args, test = predicate                 
    let potentialBindings = assignVarsFromValues context.scope AllowOutVar args argValues

    match potentialBindings with
    | ValueSome bindings ->
        match test with
        | SimpleGoal ("true", []) ->
            let updatedScope = { parent = None; values = bindings }
            let instantiatedArgs = args |> List.map (substituteVariablesInExpression updatedScope)
            let resultingBindings = assignVarsFromValues updatedScope InVarOnly argValues instantiatedArgs

            match resultingBindings with
            | ValueSome producedBindings ->
                ValueSome [| producedBindings |]
            | ValueNone -> ValueNone
        | SimpleGoal ("false", []) -> ValueNone
        | _ ->
            let contextWithBindings = { context with scope = { parent = None; values = bindings } }
            
            match tryProveGoal contextWithBindings test with
            | ValueSome testGoalBindings ->
                testGoalBindings
                |> Seq.choose (fun bindingSet ->
                    let childScope = contextWithBindings.scope.CreateChild bindingSet
                    let instantiatedArgs = args |> List.map (substituteVariablesInExpression childScope)
                    let resultingBindings = assignVarsFromValues childScope InVarOnly argValues instantiatedArgs

                    resultingBindings
                    |> Option.ofValueOption
                )
                |> Seq.noneIfEmpty

            | ValueNone -> ValueNone
    | ValueNone -> ValueNone
let rec tryProveGoal context goal : Map<string, PrologValue> seq voption =
    match goal with
    | SimpleGoal (("true" | "repeat" | "!"), []) -> ValueSome emptySuccess
    | SimpleGoal (("false" | "fail"), []) -> ValueNone

    | SimpleGoal (functor, argValues) ->
        let key = (functor, argValues.Length)
        let userPredicates = StoredTerms.lookupPredicates context.terms key
        let nativePredicates = StoredTerms.lookupNativePredicates context.terms key
        
        let updatedContext = { context with stack = (PredicateFrame key) :: context.stack }
        let instantiatedArgValues = argValues |> List.map (substituteVariablesInExpression context.scope)

        seq {
            for userPredicate in userPredicates do
                match tryProvePredicate updatedContext userPredicate instantiatedArgValues with
                | ValueSome newBindings ->
                    yield! newBindings
                | ValueNone -> ()

            for nativePredicate in nativePredicates do
                match nativePredicate updatedContext instantiatedArgValues with
                | ValueSome newBindings ->
                    yield! newBindings
                | ValueNone -> ()
        }
        |> Seq.noneIfEmpty
        
    | NegatedGoal subGoal ->
        match tryProveGoal context subGoal with
        | ValueSome _ -> ValueNone
        | ValueNone -> ValueSome emptySuccess
        
    | ConjunctionGoal goals ->
        // Note: "repeat" choice points and cuts "!"
            
        if goals.Length = 1 then
            tryProveGoal context goals[0]
        else
            seq {
                let workingSets = Stack<Map<string, PrologValue> seq * IEnumerator<Map<string, PrologValue>> * int>()
                let repeats = Stack<_>()
                let mutable resultCount = 0
                
                let initial = [| Map.empty |]
                workingSets.Push (Seq.ofArray initial, (initial :> IEnumerable<_>).GetEnumerator(), 0)
            
                while workingSets.Count > 0 do
                    let source, enumerator, goalIndex = workingSets.Peek()
                    let repeatIndex, repeatCount = if repeats.Count > 0 then repeats.Peek() else -1, -1
                    let hasMore = enumerator.MoveNext()
                    
                    if not hasMore && repeatIndex = goalIndex - 1 && resultCount = repeatCount then
                        workingSets.Pop() |> ignore
                        workingSets.Push (source, source.GetEnumerator(), goalIndex)
                    elif hasMore then
                        let bindingSet = enumerator.Current
                        let goal = goals[goalIndex]
                        
                        match goal with
                        // A cut means we immediately discard all choice points
                        | SimpleGoal("!", []) ->
                            let temporary = Stack<_>()
                            
                            while workingSets.Count > 0 do
                                let _, _, g = workingSets.Pop()
                                temporary.Push((Seq.empty, Seq.empty.GetEnumerator(), g))

                            while temporary.Count > 0 do
                                workingSets.Push(temporary.Pop())

                            if goalIndex + 1 < goals.Length then
                                workingSets.Pop() |> ignore
                                
                                let source = [| bindingSet |]
                                workingSets.Push (source, (source :> IEnumerable<_>).GetEnumerator(), goalIndex + 1)
                                
                        | SimpleGoal("repeat", []) ->
                            repeats.Push(goalIndex, resultCount)

                            if goalIndex + 1 < goals.Length then
                                workingSets.Pop() |> ignore
                                workingSets.Push (source, enumerator, goalIndex + 1)
                                
                        | _ ->
                            let contextWithUpdatedBindings = context.NestScope bindingSet
                            let potentialGoalResults = tryProveGoal contextWithUpdatedBindings goal
                            
                            match potentialGoalResults with
                            | ValueSome goalResults ->
                                let newBindingSets =
                                    goalResults
                                    |> Seq.map (Map.merge bindingSet)
                                    |> Seq.cache

                                if goalIndex + 1 >= goals.Length then
                                    yield! newBindingSets
                                else
                                    workingSets.Push (newBindingSets, newBindingSets.GetEnumerator(), goalIndex + 1)
                            | ValueNone -> ()
                    else
                        workingSets.Pop() |> ignore
            }
            |> Seq.noneIfEmpty
    
    | DisjunctionGoal goals ->
        seq {
            let mutable index = 0
            let mutable hasResult = false
        
            while index < goals.Length do
                match goals[index] with
                | SimpleGoal("!", []) ->
                    if hasResult then index <- goals.Length
                | goal ->
                    match tryProveGoal context goal with
                    | ValueSome results ->
                        hasResult <- true
                        yield! results
                    | ValueNone -> ()
                    
                index <- index + 1
        }
        |> Seq.noneIfEmpty