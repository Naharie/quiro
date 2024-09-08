module Quiro.Option

/// Inverts the specified option, filling in newValue in the case of Some.
let invert newValue option =
    match option with
    | Some _ -> None
    | None -> Some newValue