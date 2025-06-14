namespace Quiro

type StackFrame =
    | PredicateFrame of functor:string * arity:int
    | FunctionFrame of functor:string * arity:int

module StackFrame =
    let toString (stack: StackFrame list) =
        [
            for frame in stack do
                match frame with
                | FunctionFrame (functor, arity) ->
                    $"\tat function %s{functor}/%i{arity}"
                | PredicateFrame (functor, arity) ->
                    $"\tat predicate %s{functor}/%i{arity}"
        ]
        |> String.concat "\r\n"