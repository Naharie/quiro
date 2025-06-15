namespace Quiro

open System

type PrologException(message: string, inner: Exception) =
    inherit Exception(message, inner)
    new(message: string) = PrologException(message, null)