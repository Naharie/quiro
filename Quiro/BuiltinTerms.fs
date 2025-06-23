module Quiro.BuiltinTerms

open Quiro
open Quiro.StoredRules

let defaultTerms() =
    let terms = emptyTerms()
    
    MetaTerms.create terms
    CoreTerms.create terms
    MathTerms.create terms
    ReflectionTerms.create terms
    ListTerms.create terms
    IOTerms.create terms
    
    terms