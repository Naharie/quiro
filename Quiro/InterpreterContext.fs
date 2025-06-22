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
type InstantiatedCompound = string * Term

type NativePredicate = InterpreterContext -> Term list -> (Var * Term)[] seq voption
type NativeFunction = InterpreterContext -> Term list -> Term voption

type InterpreterContext = {
    /// The level of debug information to print out.
    debugLevel: DebugLevel

    terms: StoredRules
    substitutions: (Var * Term)[]
    stack: StackFrame list
}

type StoredRules = {
    userPredicates: Dictionary<string * int, ResizeArray<Term list * Term>>
    nativePredicates: Dictionary<string * int, ResizeArray<NativePredicate>>
    functions: Dictionary<string * int, ResizeArray<NativeFunction>>
}

// Helper modules

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module StoredRules =
    let emptyTerms () =
        {   
            userPredicates = Dictionary()
            nativePredicates = Dictionary()
            functions = Dictionary()
        }
    
    let private emptyPredicates = ResizeArray()
    let private emptyNativePredicates = ResizeArray()
    let private emptyFunctions = ResizeArray()
    
    let lookupPredicates (scope: StoredRules) (key: string * int) =
        let mutable result = Unchecked.defaultof<ResizeArray<_>>
        
        if scope.userPredicates.TryGetValue(key, &result) then
            result
        else
            emptyPredicates

    let lookupNativePredicates (scope: StoredRules) (key: string * int) =
        let mutable result = Unchecked.defaultof<ResizeArray<_>>
        
        if scope.nativePredicates.TryGetValue(key, &result) then
            result
        else
            emptyNativePredicates
            
    let lookupFunctions (scope: StoredRules) (key: string * int) =
        let mutable result = Unchecked.defaultof<ResizeArray<_>>

        if scope.functions.TryGetValue(key, &result) then
            result
        else
            emptyFunctions