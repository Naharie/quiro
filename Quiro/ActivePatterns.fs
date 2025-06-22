[<AutoOpen>]
module Functional.ActivePatterns

/// <summary>
/// Applies the specified wrapper function to the input.
/// </summary>
/// <param name="wrapper">The function to apply.</param>
/// <param name="input">The input arg that the function will be applied to.</param>
let (|Wrap|) wrapper input = wrapper input

/// <summary>
/// Groups the specified value with the input as a tuple.
/// </summary>
/// <param name="value">The value to pair with the input arg.</param>
/// <param name="input">The input arg that will have the value paired with it.</param>
/// <returns>A pair of the specified value and input arg.</returns>
let (|Pair|) value input = value, input