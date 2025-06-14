[<AutoOpen>]
module Functional.ActivePatterns

/// <summary>
/// Applies the specified wrapper function to the input.
/// </summary>
/// <param name="wrapper">The function to apply.</param>
/// <param name="input">The input arg that the function will be applied to.</param>
let (|Wrap|) wrapper input = wrapper input