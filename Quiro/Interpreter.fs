[<CompilationRepresentation (CompilationRepresentationFlags.ModuleSuffix)>]
module Quiro.Interpreter

open Quiro.AST
open Quiro.Interpreter.Internal

let private savePredicate (terms: StoredTerms) (functor: string) (args: PrologValue list) (body: Goal) =
    let key = (functor, args.Length)
        
    match terms.userPredicates.TryGetValue key with
    | true, existing ->
        existing.Add (args, body)
    | false, _ ->
        let container = ResizeArray()
        container.Add (args, body)
        terms.userPredicates[key] <- container

/// Save a declaration to the list of known terms.
let storeDeclaration declaration (terms: StoredTerms) =
    match declaration with
    | PredicateDeclaration (functor, args, body) ->
        let reifiedArgs = List.map reifyExpr args
        let reifiedBody = reifyGoal body
        
        savePredicate terms functor reifiedArgs reifiedBody

    | DCGDeclaration (functor, args, body) ->
        if args.Length > 0 then
            let rec checkDCG (dcg: DCGAST) =
                let loc = dcg.location
            
                match dcg.dcgKind with
                | DCGTerm _ -> raise (PrologException $"DCG definitions with explicit arguments may not invoke terms without explicit arguments (%s{loc.file}, line %i{loc.line}, column %i{loc.column}")
                | DCGSequence terms ->
                    terms
                    |> Array.iter checkDCG

                | _ -> ()
                
            checkDCG body
        
        let reifiedArgs = args |> List.map reifyExpr
        let reifiedBody = reifyDCG body
        
        let rec convertDCG start isFirstVarTerm dcg =
            let var (i: int) =
                Variable ("S" + (string i))
            
            match dcg with
            | DCG.Term term ->
                start + 1, SimpleGoal(term, [ var start; var (start + 1) ])

            | DCG.Call (functor, args) ->
                if isFirstVarTerm then
                    start, SimpleGoal(functor, List.append args [ var start ])
                else
                    start + 2, ConjunctionGoal [|
                        SimpleGoal(functor, List.append args [ var (start + 1) ])
                        SimpleGoal("append", [ var start; var (start + 1); var (start + 2) ])
                    |]

            | DCG.List values ->
                start + 1, SimpleGoal("append", [ var start; ListTerm values; var (start + 1) ])
                
            | DCG.Goal goal -> start, goal
                
            | DCG.Sequence dcgTerms ->
                let mutable counter = start
                let mutable isFirstVarTerm = true
                
                let goal = ConjunctionGoal [|
                    for term in dcgTerms do
                        let next, converted = convertDCG counter isFirstVarTerm term
                        
                        match term with
                        | DCG.Goal _ -> ()
                        | _ -> isFirstVarTerm <- false
                        
                        counter <- next
                        yield converted
                |]
                
                counter, goal

        if reifiedArgs.Length = 0 then
            match reifiedBody with
            | DCG.Term term ->
                let args = [ Variable "S1"; Variable "S2" ]
                savePredicate terms functor args (SimpleGoal(term, args))

            | DCG.Call _ ->
                let finalVar, body = convertDCG  1 true reifiedBody
                savePredicate terms functor [ Variable "S1"; Variable ("S" + string finalVar) ] body
            
            | DCG.List values ->
                let arg = List.foldBack (fun element tail -> ListCons(element, tail)) values (Variable "X")
                savePredicate terms functor [ arg; Variable "X" ] (SimpleGoal("true", List.empty))
                
            | DCG.Goal goal ->
                savePredicate terms functor [ Variable "S1"; Variable "S2" ] goal
                
            | DCG.Sequence _ ->
                let finalVar, body = convertDCG 1 true reifiedBody
                savePredicate terms functor [ Variable "S1"; Variable ("S" + string finalVar) ] body
        else
            match reifiedBody with
            | DCG.Term _ ->
                raise (PrologException $"DCG definitions with explicit arguments may not invoke terms without explicit arguments (unknown file and location")

            | DCG.Call _ ->
                let _, body = convertDCG 1 true reifiedBody
                savePredicate terms functor (List.append reifiedArgs [ Variable "S1"; ]) body
            
            | DCG.List values ->
                savePredicate terms functor (List.append reifiedArgs [ Variable "S1" ]) (SimpleGoal("is", [ Variable "S1"; ListTerm values ]))
                
            | DCG.Goal goal ->
                savePredicate terms functor reifiedArgs goal

            | DCG.Sequence _ ->
                let finalVar, body = convertDCG 1 true reifiedBody
                savePredicate terms functor (List.append reifiedArgs [ Variable ("S" + string finalVar) ]) body

/// Determine whether a given query is provable or not.
let rec query (target: Goal) (terms: StoredTerms) (debugLevel: DebugLevel): Map<string, PrologValue>[] voption =    
    let context = {
        debugLevel = debugLevel
        
        terms = terms
        scope = Scope.empty

        stack = []
    }
    
    tryProveGoal context target