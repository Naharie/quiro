[<RequireQualifiedAccess>]
module Quiro.Seq

let noneIfEmpty seq =
    let cached = Seq.cache seq
    if Seq.isEmpty cached then ValueNone else ValueSome cached
    
let chooseV (chooser: 't -> 'u voption) (sequence: #seq<'t>) =
    seq {
        for item in sequence do
            match chooser item with
            | ValueSome v -> yield v
            | ValueNone -> ()
    }