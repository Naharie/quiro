module Quiro.Scope

open Quiro.DataTypes

let defaultScope = {
    rules = Map.empty
    nativeRules = Map.ofArray [||] 
}