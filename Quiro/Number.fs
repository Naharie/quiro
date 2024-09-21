namespace Quiro.DataTypes

open System
open System.Collections.Generic
open ExtendedNumerics
open ExtendedNumerics.Helpers

type Number =
    | Float of float:BigDecimal
    | NaN
    | Infinity of positive:bool
    | Range of Number * Number
with
    interface IEnumerable<BigDecimal> with
        member this.GetEnumerator(): IEnumerator<BigDecimal> =
            (seq {
                match this with
                | Float v -> yield v
                | NaN -> ()
                | Infinity positive ->
                    let step = if positive then BigDecimal 1 else BigDecimal -1
                    let mutable value = step
                    
                    while true do
                        yield value
                        value <- value + step
                | Range (lower, upper) ->
                    match lower, upper with
                    | Float lower, Float upper ->
                        for i in lower..upper -> i
                        
                    | Infinity true, Float _ -> ()
                    | Infinity false, Float upper ->
                        let mutable value = upper
                        let step = BigDecimal 1
                        
                        while true do
                            yield value
                            value <- value - step
                            
                    | Float _, Infinity false -> ()
                    | Float lower, Infinity true ->
                        let mutable value = lower
                        let step = BigDecimal 1
                        
                        while true do
                            yield value
                            value <- value + step

                    | _, _ -> failwith "Ranges should never be nested inside other ranges!"
            }).GetEnumerator()
        member this.GetEnumerator(): System.Collections.IEnumerator =
            (this :> IEnumerable<BigDecimal>).GetEnumerator() :> System.Collections.IEnumerator

    static member private PerformOpI opN opR opI a b =
        match a, b with
        | Float a, Float b -> Float (opN a b)
        
        | Float _, Range (l, h) -> Range(opR a l, opR a h)
        | Range (l, h), Float _ -> Range(opR b l, opR b h)
        
        | Range _, Range _ -> failwith "Refusing to perform direct math operations on a range!"
        
        | NaN, _ -> NaN
        | _, NaN -> NaN
        
        | Infinity _, Infinity _ -> NaN
        
        | Infinity _, _ -> a 
        | _, Infinity positive ->
            opI a positive
    static member private PerformOp opN opR a b =
        Number.PerformOpI opN opR (fun _ -> Infinity) a b

    static member (+) (a, b) = Number.PerformOpI (+) (+) (fun _ -> Infinity) a b
    static member (-) (a, b) = Number.PerformOpI (-) (-) (fun _ p -> Infinity (not p)) a b

    static member (*) (a, b) = Number.PerformOp (*) (*) a b
    static member (/) (a, b) =
        match b with
        | Float v when v.IsZero() -> raise (DivideByZeroException())
        | _ ->
            Number.PerformOp (/) (/) a b
    
    static member (%) (a, b) = Number.PerformOp (%) (%) a b
    member a.Modulus b = Number.PerformOp _.Modulus _.Modulus a b
    
    member a.Pow b =
        Number.PerformOp (fun a b ->
            if b.DecimalPlaces = 0 then
                BigDecimal.Pow (a, b.WholeValue)
            else
                BigDecimal.Pow(a, b, BigDecimal.Precision)
        ) _.Pow a b
        
    static member op_LessThan (a, b) =
        match a, b with
        | Float a, Float b -> a < b
        
        | Float _, Infinity p -> p
        | Infinity p, Float _ -> not p
        
        | Range _, _ | _, Range _ ->
            invalidOp "Ranges may not have relative comparison applied"
        
        | Infinity false, Infinity false -> false
        | Infinity false, _ -> true
        
        | Infinity true, _ -> false
        
        | _, Infinity false -> false
        | _, Infinity true -> true
        
        | NaN, _ | _, NaN ->
            invalidOp "Can't compare NaN to another value that way"
    static member op_LessThanOrEqual (a, b) = a = b || a < b
    
    static member op_GreaterThan (a, b) =
        match a, b with
        | Float a, Float b -> a > b
        
        | Float _, Infinity p -> not p
        | Infinity p, Float _ -> p
        
        | Range _, _ | _, Range _ ->
            invalidOp "Ranges may not have relative comparison applied"
        
        | Infinity false, _ -> false
        
        | Infinity true, Infinity true -> false
        | Infinity true, _ -> true
        
        | _, Infinity false -> true
        | _, Infinity true -> false
        
        | NaN, _ | _, NaN ->
            invalidOp "Can't compare NaN to another value that way!"
    static member op_GreaterThanOrEqual (a, b) = a = b || a > b
        
    override this.ToString() =
        match this with
        | Float v -> string v
        | NaN -> "nan"
        | Infinity positive -> if positive then "+infinity" else "-infinity"
        | Range(a, b) -> $"(%O{a}..%O{b})"