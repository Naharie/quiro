[<CompilationRepresentation (CompilationRepresentationFlags.ModuleSuffix)>]
module Quiro.Interpreter

open System.Collections.Generic
open Microsoft.FSharp.Core
open Quiro.AST
open Quiro.Interpreter.Internal

let private savePredicate (terms: StoredRules) (functor: string) (args: Term list) (body: Term) =
    let key = (functor, args.Length)
        
    match terms.userPredicates.TryGetValue key with
    | true, existing ->
        existing.Add (args, body)
    | false, _ ->
        let container = ResizeArray()
        container.Add (args, body)
        terms.userPredicates[key] <- container

/// Save a declaration to the list of known terms.
let storeDeclaration declaration (terms: StoredRules) =
    match declaration with
    | PredicateDeclaration (functor, args, body) ->
        let vars = Dictionary()
        
        let reifiedArgs = List.map (reifyTerm vars) args
        let reifiedBody = reifyTerm vars body

        let makeError() =
            $"(%s{body.location.file}, line %i{body.location.line}, column %i{body.location.column})"

        match reifiedBody with
        | Number _ -> raise (PrologException $"Expected an invocable but found a number instead! %s{makeError()}")
        | Text _ -> raise (PrologException $"Expected an invocable but found a string instead! %s{makeError()}")
        | Variable _ -> raise (PrologException $"Expected an invocable but found a variable instead! %s{makeError()}")
        | ListCons _ | ListTerm _ -> raise (PrologException $"Expected an invocable but found a list instead! %s{makeError()}")
        | _ -> ()
        
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
        
        let vars = Dictionary()
        
        let reifiedArgs = args |> List.map (reifyTerm vars)
        let reifiedBody = reifyDCG vars body
        
        let var (i: int) =
            let name = "S" + string i
            let mutable var = Unchecked.defaultof<Term>
            
            if not (vars.TryGetValue (name, &var)) then
                var <- Term.makeVar name
                vars[name] <- var
                
            var
        
        let rec convertDCG start isFirstVarTerm dcg =
            
            match dcg with
            | DCG.Term term ->
                start + 1, Term(term, [ var start; var (start + 1) ])

            | DCG.Call (functor, args) ->
                if isFirstVarTerm then
                    start, Term(functor, List.append args [ var start ])
                else
                    start + 2, Conjunction [|
                        Term(functor, List.append args [ var (start + 1) ])
                        Term("append", [ var start; var (start + 1); var (start + 2) ])
                    |]

            | DCG.List values ->
                start + 1, Term("append", [ var start; ListTerm values; var (start + 1) ])
                
            | DCG.Goal goal -> start, goal
                
            | DCG.Sequence dcgTerms ->
                let mutable counter = start
                let mutable isFirstVarTerm = true
                
                let goal = Conjunction [|
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
                let args = [ var 1; var 2 ]
                savePredicate terms functor args (Term(term, args))

            | DCG.Call _ ->
                let finalVar, body = convertDCG  1 true reifiedBody
                savePredicate terms functor [ var 1; var finalVar ] body
            
            | DCG.List values ->
                let arg = List.foldBack (fun element tail -> ListCons(element, tail)) values (var 1)
                savePredicate terms functor [ arg; var 1 ] (Term("true", List.empty))
                
            | DCG.Goal goal ->
                savePredicate terms functor [ var 1; var 2 ] goal
                
            | DCG.Sequence _ ->
                let finalVar, body = convertDCG 1 true reifiedBody
                savePredicate terms functor [ var 1; var finalVar ] body
        else
            match reifiedBody with
            | DCG.Term _ ->
                raise (PrologException "DCG definitions with explicit arguments may not invoke terms without explicit arguments (unknown file and location")

            | DCG.Call _ ->
                let _, body = convertDCG 1 true reifiedBody
                savePredicate terms functor (List.append reifiedArgs [ var 1; ]) body
            
            | DCG.List values ->
                savePredicate terms functor (List.append reifiedArgs [ var 1 ]) (Term("is", [ var 1; ListTerm values ]))
                
            | DCG.Goal goal ->
                savePredicate terms functor reifiedArgs goal

            | DCG.Sequence _ ->
                let finalVar, body = convertDCG 1 true reifiedBody
                savePredicate terms functor (List.append reifiedArgs [ var finalVar ]) body

/// Determine whether a given query is provable or not.
let rec query (target: Term) (terms: StoredRules) (debugLevel: DebugLevel) =  
    let context = {
        debugLevel = debugLevel
        
        terms = terms
        substitutions = Array.empty

        stack = []
    }

    let queryVariables =
        collectVars target
        |> Array.map (fun var -> var, Variable var)

    tryProveGoal context target queryVariables