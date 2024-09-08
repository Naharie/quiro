// These utilities are taken from my library Functional which can be found on my GitHub profile.
module Quiro.Array

/// Applies a function to each element and its index, threading an accumulator through the computation.
let foldi folder state (array: 't[]) =
    if isNull array then nullArg (nameof array)

    let f = OptimizedClosures.FSharpFunc<_, _, _, _>.Adapt(folder)
    let mutable result = state

    for i = 0 to array.Length - 1 do
        result <- f.Invoke(i, result, array.[i])

    result