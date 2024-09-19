// These utilities are taken from my library Functional which can be found on my GitHub profile.
module Quiro.Option

/// Inverts the specified option, flipping Some to None and None to Some filling in the specified value when needed.
let invert value option =
    match option with
    | Some _ -> None
    | None -> Some value