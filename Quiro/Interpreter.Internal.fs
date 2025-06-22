module rec Quiro.Interpreter.Internal

open System
open System.Collections.Generic
open Functional
open Microsoft.FSharp.Collections
open Microsoft.FSharp.Core
open Microsoft.FSharp.Quotations
open Quiro
open Quiro.AST

let rec reifyTerm (vars: Dictionary<string, Term>) (ast: TermAST): Term =
    match ast.termKind with
    | ExprAtom atom -> Atom atom
    | ExprNumber number -> Number number
    | ExprText text -> Text text
    | ExprListTerm elements -> ListTerm (List.map (reifyTerm vars) elements)
    | ExprTerm (functor, args) -> Term(functor, List.map (reifyTerm vars) args)
    | ExprVariable name ->
        vars.TryFind name
        |> ValueOption.defaultWith (fun () ->
            let var = Term.makeVar name
            vars[name] <- var
            var
        )
    | ExprListCons (head, tail) -> ListCons(reifyTerm vars head, reifyTerm vars tail)
    | ExprNegation term -> Negation(reifyTerm vars term)
    | ExprConjunction terms -> Conjunction(terms |> Array.map (reifyTerm vars))
    | ExprDisjunction terms -> Disjunction(terms |> Array.map (reifyTerm vars))
    | ExprPlaceholder ->
        raise (PrologException $"Incomplete expression (line %i{ast.location.line}, column %i{ast.location.column})")
let reifyDCG (vars: Dictionary<string, Term>) (ast: DCGAST) =
    match ast.dcgKind with
    | DCGTerm term -> DCG.Term term
    | DCGCall (functor, args) -> DCG.Call(functor, args |> List.map (reifyTerm vars))
    | DCGGoal goal -> DCG.Goal (reifyTerm vars goal)
    | DCGList values -> DCG.List (values |> List.map (reifyTerm vars))
    | DCGSequence nested -> DCG.Sequence (nested |> Array.map (reifyDCG vars))

let rec substitute (var: Var) (value: Term) (expr: Term) =
    match expr with
    | Atom _
    | Number _
    | Text _ -> expr
    
    | Variable otherVar ->
        if var = otherVar then value else expr
    
    | ListCons (head, tail) ->
        ListCons(substitute var value head, substitute var value tail)
    | ListTerm values ->
        ListTerm (values |> List.map (substitute var value))
    
    | Term(target, args) ->
        Term(target, args |> List.map (substitute var value))
    | Negation term -> Negation(substitute var value term)
    | Conjunction terms -> Conjunction (terms |> Array.map (substitute var value))
    | Disjunction terms -> Disjunction (terms |> Array.map (substitute var value))

let rec containsVar var expr =
    match expr with
    | Atom _ | Number _ | Text _ -> false
    | Variable otherVar -> var = otherVar
    | ListCons(head, tail) -> containsVar var head || containsVar var tail
    | ListTerm(values) | Term(_, values) -> values |> List.exists (containsVar var)
    | Negation term -> containsVar var term
    | Conjunction terms | Disjunction terms -> terms |> Array.exists (containsVar var)
let collectVars expr =
    let vars = HashSet<Var>()
    
    let rec go expr =
        match expr with
        | Atom _ | Number _ | Text _ -> ()
        | Variable var -> vars.Add var |> ignore
        | ListCons(head, tail) -> go head; go tail
        | ListTerm items | Term(_, items) -> items |> List.iter go
        | Negation term -> go term
        | Conjunction terms | Disjunction terms -> terms |> Array.iter go

    go expr
    vars |> Seq.toArray
let hasFreeVariables expr =
    match expr with
    | Atom _ | Number _ | Text _ -> false
    | Variable _ -> true
    | ListCons(head, tail) -> hasFreeVariables head || hasFreeVariables tail
    | ListTerm items | Term(_, items) -> items |> List.exists hasFreeVariables
    | Negation term -> hasFreeVariables term
    | Conjunction terms | Disjunction terms -> terms |> Array.exists hasFreeVariables

let rec unify (left: Term) (right: Term) =
    match left, right with
    | l, r when l = r -> ValueSome [||]
    
    | Variable (Var("_", _)), _
    | _, Variable(Var("_", _))
    | Atom "nil", ListTerm []
    | ListTerm [], Atom "nil" -> ValueSome [||]
    
    | Variable var, other | other, Variable var ->
        if containsVar var other then ValueNone
        else ValueSome [| (var, other) |]
    
    | ListCons (lHead, lTail), ListCons(rHead, rTail)
    | ListCons (lHead, lTail), ListTerm(rHead :: Wrap ListTerm rTail)
    | ListTerm (lHead :: Wrap ListTerm lTail), ListCons (rHead, rTail) ->
        unify lHead rHead
        |> ValueOption.bind (fun subA ->
            unify lTail rTail
            |> ValueOption.map (Array.append subA)
        )

    | ListTerm lItems, ListTerm rItems ->
        if lItems.Length <> rItems.Length then ValueNone
        else unifyMany lItems rItems

    | Term(lFunc, lArgs), Term(rFunc, rArgs) ->
        if lFunc <> rFunc || lArgs.Length <> rArgs.Length then ValueNone
        else unifyMany lArgs rArgs

    | Negation lTerm, Negation rTerm -> unify lTerm rTerm
    | Conjunction lTerms, Conjunction rTerms
    | Disjunction lTerms, Disjunction rTerms ->
        Array.map2 (fun a b -> ValueOption.toOption (unify a b)) lTerms rTerms
        |> Array.choose id
        |> Array.collect id
        |> ValueSome
    
    | _, _ -> ValueNone
let rec unifyMany (left: Term list) (right: Term list) =
    if left.Length = 0 && right.Length = 0 then
        ValueSome Array.empty
    else
        let left = List.toArray left
        let right = List.toArray right
        
        Array.map2 (fun a b -> ValueOption.toOption (unify a b)) left right
        |> Array.choose id
        |> fun results ->
            if results.Length = 0 then ValueNone
            else ValueSome results
        |> ValueOption.map (Array.collect id)

let substituteAll replacements term =
    replacements
    |> Array.fold (fun term (var, value) -> substitute var value term) term

let evaluateExpr (context: InterpreterContext) expr =
    match expr with
    | Atom _
    | Number _
    | Text _
    | Variable _ -> expr
    
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

    | Term (functor, args) ->
        let functions = StoredRules.lookupFunctions context.terms (functor, args.Length)
        
        if functions.Count = 0 then expr
        else
            functions
            |> Seq.tryPick (fun func -> func context args |> Option.ofValueOption)
            |> Option.defaultValue expr
            
    | Negation _ -> raise (PrologException "Expected an expression term, but found a negation query!")
    | Conjunction _ -> raise (PrologException "Expected an expression term, but found a conjunction query!")
    | Disjunction _ -> raise (PrologException "Expected an expression term, but found a disjunction query!")

let (|AtomOrTerm|_|) atom value =
    match value with
    | Atom name | Term(name, _) when name = atom -> Some ()
    | _ -> None

let tryProvePredicate (context: InterpreterContext) (predicate: Term list * Term) argValues substitutions: ((Var * Term)[] * (Var * Term)[]) seq voption =
    let args, body = predicate                 
    let potentialBindings = unifyMany args argValues

    match potentialBindings with
    | ValueNone -> ValueNone
    | ValueSome bindings ->
        let instantiatedBody = substituteAll bindings body
        let instantiatedSubstitutions =
            substitutions
            |> Array.map (fun (before, after) ->
                before, (substituteAll bindings after)
            )
        
        tryProveGoal context instantiatedBody instantiatedSubstitutions
        |> ValueOption.map (fun results ->
            results
            |> Seq.map (fun (frame, bubbledSubstitutions) ->
                (frame |> Array.map (fun (key, value) -> key, substituteAll bindings value)), bubbledSubstitutions
            )
        )
 
let rec tryProveGoal context goal (substitutions: (Var * Term)[]) : ((Var * Term)[] * (Var * Term)[]) seq voption  =
    match goal with
    | Number _ -> raise (PrologException "Expected an invocable but found a number instead!")
    | Text _ -> raise (PrologException "Expected an invocable but found a string instead!")
    | Variable _ -> raise (PrologException "Expected an invocable but found a variable instead!")
    | ListCons _ | ListTerm _ -> raise (PrologException "Expected an invocable but found a list instead!")

    | AtomOrTerm "true" | AtomOrTerm "repeat" | AtomOrTerm "!" -> ValueSome (Seq.singleton (substitutions, substitutions))
    | AtomOrTerm "false" | AtomOrTerm "fail" -> ValueNone

    | Term (functor, argValues) | Pair [] (argValues, Atom functor) ->
        let key = (functor, argValues.Length)
        let userPredicates = StoredRules.lookupPredicates context.terms key
        let nativePredicates = StoredRules.lookupNativePredicates context.terms key

        let updatedContext = {
            context with
                stack = (PredicateFrame key) :: context.stack
                substitutions = substitutions
        }

        seq {
            for userPredicate in userPredicates do
                match tryProvePredicate updatedContext userPredicate argValues substitutions with
                | ValueSome newBindings ->
                    yield! newBindings
                | ValueNone -> ()

            for nativePredicate in nativePredicates do
                match nativePredicate updatedContext argValues with
                | ValueSome newBindings ->
                    yield! newBindings
                | ValueNone -> ()

            if functor <> "@meta" then
                match tryProveGoal context (Term ("@meta", [ Atom functor; Atom "var_args" ])) substitutions with
                | ValueSome _ ->
                    let wrappedArgs = [ ListTerm argValues ]
                    
                    for userPredicate in StoredRules.lookupPredicates context.terms (functor, 1) do
                        match tryProvePredicate updatedContext userPredicate wrappedArgs substitutions with
                        | ValueSome newBindings ->
                            yield! newBindings
                        | ValueNone -> ()
                    
                    for nativePredicate in StoredRules.lookupNativePredicates context.terms (functor, 1) do
                        match nativePredicate updatedContext wrappedArgs with
                        | ValueSome newBindings ->
                            yield! newBindings
                        | ValueNone -> ()
                    
                | ValueNone -> ()
        }
        |> Seq.noneIfEmpty

    | Negation subGoal ->
        match tryProveGoal context subGoal substitutions with
        | ValueSome _ -> ValueNone
        | ValueNone -> ValueSome [ Array.empty, Array.empty ]

    | Conjunction goals ->
        if goals.Length = 1 then
            tryProveGoal context goals[0] substitutions
        else
            seq {
                let workingSets = Stack<((Var * Term)[] * (Var * Term)[]) seq * IEnumerator<(Var * Term)[] * (Var * Term)[]> * int>()
                let repeats = Stack<_>()
                let mutable resultCount = 0

                let initial = [| Array.empty, substitutions |]
                workingSets.Push (Seq.ofArray initial, (initial :> IEnumerable<_>).GetEnumerator(), 0)
            
                while workingSets.Count > 0 do
                    let source, enumerator, goalIndex = workingSets.Peek()
                    let repeatIndex, repeatCount = if repeats.Count > 0 then repeats.Peek() else -1, -1
                    let hasMore = enumerator.MoveNext()
                    
                    if not hasMore && repeatIndex = goalIndex - 1 && resultCount = repeatCount then
                        workingSets.Pop() |> ignore
                        workingSets.Push (source, source.GetEnumerator(), goalIndex)
                    elif hasMore then
                        let bindingSet, substitutions = enumerator.Current
                        let goal = goals[goalIndex]
                        
                        match goal with
                        // A cut means we immediately discard all choice points
                        | AtomOrTerm "!" ->
                            let temporary = Stack<_>()
                            
                            while workingSets.Count > 0 do
                                let _, _, g = workingSets.Pop()
                                temporary.Push((Seq.empty, Seq.empty.GetEnumerator(), g))

                            while temporary.Count > 0 do
                                workingSets.Push(temporary.Pop())

                            if goalIndex + 1 < goals.Length then
                                workingSets.Pop() |> ignore

                                let source = [| bindingSet, substitutions |]
                                workingSets.Push (source, (source :> IEnumerable<_>).GetEnumerator(), goalIndex + 1)
                                
                        | AtomOrTerm "repeat" ->
                            repeats.Push(goalIndex, resultCount)

                            if goalIndex + 1 < goals.Length then
                                workingSets.Pop() |> ignore
                                workingSets.Push (source, enumerator, goalIndex + 1)
                                
                        | _ ->
                            let instantiatedGoal = substituteAll bindingSet goal
                            let instantiatedSubstitutions =
                                substitutions
                                |> Array.map (fun (before, after) ->
                                    before, (substituteAll bindingSet after)
                                )
                            
                            match tryProveGoal context instantiatedGoal instantiatedSubstitutions with
                            | ValueSome goalResults ->
                                let newBindingSets =
                                    goalResults
                                    |> Seq.map (fun (resultFrame, bubbledSubstitutions) ->
                                        resultFrame
                                        |> Array.map (fun (key, value) -> key, (substituteAll bindingSet value))
                                        |> Map.ofArray
                                        |> Map.merge (
                                            bindingSet
                                            |> Array.map (fun (key, value) -> key, (substituteAll resultFrame value))
                                            |> Map.ofArray
                                        )
                                        |> Seq.map (fun (KeyValue (k, v)) -> k, v)
                                        |> Seq.toArray
                                        |> fun frame -> frame, bubbledSubstitutions
                                    )
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
    
    | Disjunction goals ->
        seq {
            let mutable index = 0
            let mutable hasResult = false
        
            while index < goals.Length do
                match goals[index] with
                | AtomOrTerm "!" ->
                    if hasResult then index <- goals.Length
                | goal ->
                    match tryProveGoal context goal substitutions with
                    | ValueSome results ->
                        hasResult <- true
                        yield! results
                    | ValueNone -> ()
                    
                index <- index + 1
        }
        |> Seq.noneIfEmpty
        
    | Atom _ -> raise (PrologException "Expected an invocable but found an atom instead!")