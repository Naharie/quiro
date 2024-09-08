// These utilities are taken from my library Functional which can be found on my GitHub profile.
module private Quiro.Map

/// Returns a new map that contains all the pairs from both maps, where keys from the second map overwrite those from the first.
let merge (map1: Map<_, _>) (map2: Map<_, _>) =
    Map.fold (fun map key value ->
        map |> Map.add key value
    ) map1 map2