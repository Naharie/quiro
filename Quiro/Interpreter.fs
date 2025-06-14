[<CompilationRepresentation (CompilationRepresentationFlags.ModuleSuffix)>]
module Quiro.Interpreter

open System.Collections.Generic
open Quiro.AST
open Quiro.Interpreter.Internal

/// Save a declaration to the list of known terms.
let storeDeclaration declaration (scope: StoredTerms) =
    match declaration with
    | PredicateDeclaration (functor, args, body) ->
        let reifiedArgs = List.map reifyExpr args
        let key = (functor, args.Length)
        
        match scope.userPredicates.TryGetValue key with
        | true, existing ->
            existing.Add (reifiedArgs, reifyGoal body)
        | false, _ ->
            let container = ResizeArray()
            container.Add (reifiedArgs, reifyGoal body)
            scope.userPredicates[key] <- container

    | FunctionDeclaration (functor, args, body) ->
        let reifiedArgs = args |> List.map reifyExpr
        let key = (functor, args.Length)
        
        match scope.userFunctions.TryGetValue key with
        | true, existing ->
            existing.Add (reifiedArgs, reifyExpr body)
        | false, _ ->
            let container = ResizeArray()
            container.Add (reifiedArgs, reifyExpr body)
            scope.userFunctions[key] <- container

/// Determine whether a given query is provable or not.
let rec query (target: Goal) (terms: StoredTerms) (debugLevel: DebugLevel): Map<string, PrologValue>[] voption =    
    let context = {
        debugLevel = debugLevel
        
        terms = terms
        scope = Scope.empty

        stack = []
    }
    
    tryProveGoal context target