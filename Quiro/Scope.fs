namespace Quiro

type Scope = {
    parent: Scope option
    values: Map<string, PrologValue>
}
with
    member this.CreateChild bindings =
        {
            parent = Some this
            values = bindings
        }

module Scope =
    let empty = {
        parent = None
        values = Map.empty
    }
    
    let rec lookupValue name scope =
        match scope.values.TryFind name with
        | Some value -> ValueSome value
        | None ->
            match scope.parent with
            | Some parent -> lookupValue name parent
            | None -> ValueNone