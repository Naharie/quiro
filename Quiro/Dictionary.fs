[<AutoOpen>]
module Functional.Dictionary

open System.Collections.Generic

type Dictionary<'tkey, 'tvalue> with
    /// <summary>Gets the value associated with the specified key.</summary>
    /// <param name="key">The key to lookup.</param>
    /// <returns>The value the key is mapped to or <c>ValueNone</c> if the dictionary does not contain the key.</returns>
    member this.TryFind key =        
        if isNull (box key) then
            ValueNone
        else
            let mutable result = Unchecked.defaultof<'tvalue>

            if this.TryGetValue (key, &result) then ValueSome result
            else ValueNone