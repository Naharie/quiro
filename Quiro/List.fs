module Quiro.List

/// Wraps a list as an option, returning None if the given list is empty.
let noneIfEmpty (value: 't list) =
    match value with
    | [] -> None
    | _ -> Some value