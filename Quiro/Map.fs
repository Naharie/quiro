module Functional.Map

/// <summary>
/// Returns a new map that contains all the pairs from both maps, where keys from the second map overwrite those from the first.
/// </summary>
/// <param name="map1">The map to merge onto.</param>
/// <param name="map2">The map to merge from.</param>
/// <returns>A new map that contains all the pairs from both maps, where keys from the second map overwrite those from the first.</returns>
let merge (map1: Map<_, _>) (map2: Map<_, _>) =
    Map.fold (fun map key value ->
        map |> Map.add key value
    ) map1 map2