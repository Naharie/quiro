[<RequireQualifiedAccess>]
module Quiro.Seq

let noneIfEmpty seq =
    let cached = Seq.cache seq
    if Seq.isEmpty cached then ValueNone else ValueSome cached