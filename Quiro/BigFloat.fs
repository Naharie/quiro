namespace Quiro

open System
open ExtendedNumerics
open ExtendedNumerics.Helpers

[<RequireQualifiedAccess; CustomEquality; CustomComparison>]
type BigFloat =
    | Decimal of float:BigDecimal
    | NaN
    | PositiveInfinity
    | NegativeInfinity
with
    static member Zero = Decimal BigDecimal.Zero
    static member One = Decimal BigDecimal.One

    static member (+) (a, b) =
        match a, b with
        | NaN, _ | _, NaN -> NaN
        | PositiveInfinity, _ | _, PositiveInfinity -> PositiveInfinity
        | NegativeInfinity, _ | _, NegativeInfinity -> NegativeInfinity

        | Decimal a, Decimal b -> Decimal (a + b)

    static member (-) (a, b) =
        match a, b with
        | NaN, _ | _, NaN -> NaN
        | PositiveInfinity, _ -> PositiveInfinity
        | _, PositiveInfinity -> NegativeInfinity
        
        | NegativeInfinity, _ -> NegativeInfinity
        | _, NegativeInfinity -> PositiveInfinity

        | Decimal a, Decimal b -> Decimal (a - b)
    
    static member (*) (a, b) =
        match a, b with
        | NaN, _ | _, NaN -> NaN
        
        | PositiveInfinity, Decimal c | Decimal c, PositiveInfinity when c.IsNegative() -> NegativeInfinity
        | PositiveInfinity, _ | _, PositiveInfinity -> PositiveInfinity
        
        | NegativeInfinity, Decimal c | Decimal c, NegativeInfinity when c.IsNegative() -> PositiveInfinity
        | NegativeInfinity, _ | _, NegativeInfinity -> NegativeInfinity

        | Decimal a, Decimal b -> Decimal (a * b)
    
    static member (/) (a, b) =
        match a, b with
        | NaN, _ | _, NaN -> NaN
        
        | PositiveInfinity, _ | _, PositiveInfinity
        | NegativeInfinity, _ | _, NegativeInfinity -> NaN

        | Decimal a, Decimal b -> Decimal (a / b)
    
    static member (%) (a, b) =
        match a, b with
        | NaN, _ | _, NaN -> NaN
        | PositiveInfinity, _ | _, PositiveInfinity
        | NegativeInfinity, _ | _, NegativeInfinity -> NaN

        | Decimal a, Decimal b -> Decimal (a % b)
    
    static member Pow(``base``, exponent) =
        match ``base``, exponent with
        | NaN, _ | _, NaN -> NaN
        
        | Decimal b, PositiveInfinity ->
            if b = BigDecimal.One then BigFloat.One else PositiveInfinity
        | _, PositiveInfinity -> PositiveInfinity

        | PositiveInfinity, Decimal e ->
            if e.IsNegative() then BigFloat.Zero else PositiveInfinity
        
        | _, NegativeInfinity -> BigFloat.Zero
        | NegativeInfinity, Decimal e ->
            if e.IsNegative() then BigFloat.Zero
            elif e.Modulus (BigDecimal 2I) = BigDecimal.Zero then PositiveInfinity
            else NegativeInfinity

        | Decimal b, Decimal e ->
            if e.DecimalPlaces = 0 then BigDecimal.Pow(b, e.WholeValue)
            else BigDecimal.Pow(b, e, BigDecimal.Precision)
            |> Decimal
            
    interface IComparable with
        override a.CompareTo other =
            match other with
            | :? BigFloat as b -> (a :> IComparable<BigFloat>).CompareTo b
            | _ -> raise (ArgumentException "Argument is not the same type as this instance")

    interface IComparable<BigFloat> with
        override a.CompareTo b =
            match a, b with
            | NaN, _ -> -1 | _, NaN -> 1
            
            | NegativeInfinity, _ -> -1
            | _, NegativeInfinity -> 1
            
            | PositiveInfinity, _ -> 1
            | _, PositiveInfinity -> -1

            | Decimal a, Decimal b -> a.CompareTo b
    
    interface IEquatable<BigFloat> with
        member a.Equals b =
            match a, b with
            | NaN, _ | _, NaN -> false
            
            | PositiveInfinity, PositiveInfinity -> true
            | PositiveInfinity, _ | _, PositiveInfinity -> false
            
            | NegativeInfinity, NegativeInfinity -> true
            | NegativeInfinity, _ | _, NegativeInfinity -> false
            
            | Decimal a, Decimal b -> a = b
            
    override this.Equals other =
        match other with
        | :? BigFloat as other -> (this :> IEquatable<BigFloat>).Equals other
        | _ -> raise (ArgumentException "Argument is not the same type as this instance")
    
    override this.GetHashCode() =
        match this with
        | NaN | PositiveInfinity | NegativeInfinity -> 2146435072
        | Decimal v -> v.GetHashCode()
    
    override this.ToString() =
        match this with
        | Decimal v -> string v
        | NaN -> "nan"
        | PositiveInfinity -> "+infinity"
        | NegativeInfinity -> "-infinity"