module Quiro.MathTerms

open System
open Quiro.TermHelpers

let create terms =
    let addPred = addPred terms
    let addFunc = addFunc terms
    
    addFunc ("+", 2) (mathFunc (+))
    addFunc ("-", 2) (mathFunc (-))
    addFunc ("*", 2) (mathFunc (*))
    addFunc ("/", 2) (mathFunc (/))
    
    addFunc ("-", 1) (fun context args ->
        match args with
        | [ Number n ] -> ValueSome (Number (-n))
        | _ -> ValueNone
    )
    
    addPred ("<", 2) (fun context args ->
        match args with
        | [ Eval context a; Eval context b ] ->
            match a, b with
            | Variable a, Number b ->
                ValueSome (seq { for i in b - 1.0 .. -1.0 .. Double.NegativeInfinity -> [| a, (Number i) |], context.substitutions })
            | Number a, Variable b ->
                ValueSome (seq { for i in a + 1.0.. 1.0 .. Double.PositiveInfinity -> [| b, (Number i) |], context.substitutions })
            | _ -> wrap context (a < b)
        | _ -> ValueNone
    )
    addPred ("<=", 2) (fun context args ->
        match args with
        | [ Eval context a; Eval context b ] ->
            match a, b with
            | Variable a, Number b ->
                ValueSome (seq { for i in b .. -1.0 .. Double.NegativeInfinity -> [| a, (Number i) |], context.substitutions })
            | Number a, Variable b ->
                ValueSome (seq { for i in a .. 1.0 .. Double.PositiveInfinity -> [| b, (Number i) |], context.substitutions })
            | _ -> wrap context (a <= b)
        | _ -> ValueNone
    )
     
    addPred (">", 2) (fun context args ->
        match args with
        | [ Eval context a; Eval context b ] ->
            match a, b with
            | Variable a, Number b ->
                ValueSome (seq { for i in b + 1.0.. 1.0 .. Double.PositiveInfinity -> [| a, (Number i) |], context.substitutions })
            | Number a, Variable b ->
                ValueSome (seq { for i in a - 1.0.. -1.0 .. Double.NegativeInfinity -> [| b, (Number i) |], context.substitutions })
            | _ -> wrap context (a > b)
        | _ -> ValueNone
    )
    addPred (">=", 2) (fun context args ->
        match args with
        | [ Eval context a; Eval context b ] ->
            match a, b with
            | Variable a, Number b ->
                ValueSome (seq { for i in b .. 1.0 .. Double.PositiveInfinity -> [| a, (Number i) |], context.substitutions })
            | Number a, Variable b ->
                ValueSome (seq { for i in a .. -1.0 .. Double.NegativeInfinity -> [| b, (Number i) |], context.substitutions })
            | _ -> wrap context (a >= b)
        | _ -> ValueNone
    )