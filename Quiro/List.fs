module Quiro.List

let noneOnEmpty (value: 't list) =
    match value with
    | [] -> None
    | _ -> Some value