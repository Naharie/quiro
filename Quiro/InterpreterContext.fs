namespace rec Quiro

open System.Collections.Generic

type DebugLevel =
    /// Print debug information about every single goal tested during the query.
    | All
    /// Print debug information only about the rules tested during the query.
    | RuleOnly
    /// Print debug information only about goals that succeed during the query.
    | OnlyTrue
    /// Do not print any debug information.
    | NoDebugInfo

/// The instantiated form of a predicate or function.
type InstantiatedCompound = string * PrologValue

type NativePredicate = InterpreterContext -> PrologValue list -> Map<string, PrologValue>[] voption

type InterpreterContext = {
    /// The level of debug information to print out.
    debugLevel: DebugLevel

    terms: StoredTerms
    scope: Scope

    stack: StackFrame list
}
with
    member this.NestScope bindings =
        { this with scope = this.scope.CreateChild bindings }

type StoredTerms = {
    userPredicates: Dictionary<string * int, ResizeArray<PrologValue list * Goal>>
    nativePredicates: Dictionary<string * int, ResizeArray<NativePredicate>>
}

// Helper modules

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module StoredTerms =
    let emptyTerms () =
        {   
            userPredicates = Dictionary()
            nativePredicates = Dictionary() 
        }
    
    let lookupPredicates (scope: StoredTerms) (key: string * int) =
        let mutable result = Unchecked.defaultof<ResizeArray<_>>
        
        if scope.userPredicates.TryGetValue(key, &result) then
            result
        else
            ResizeArray()

    let lookupNativePredicates (scope: StoredTerms) (key: string * int) =
        let mutable result = Unchecked.defaultof<ResizeArray<_>>
        
        if scope.nativePredicates.TryGetValue(key, &result) then
            result
        else
            ResizeArray()