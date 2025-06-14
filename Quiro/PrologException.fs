namespace Quiro

open System
open System.Collections.Generic

type PrologException(message: string, stack: StackFrame list, inner: Exception) =
    inherit Exception(message, inner)
    new(message: string, stack: StackFrame list) = PrologException(message, stack, null)

    override _.ToString() =
        message + "\r\n" + StackFrame.toString stack

type InsufficientSubstantiationException (term: string, stack: StackFrame list) =
    inherit PrologException($"The term %s{term} was not sufficiently substantiated", stack)

type UnboundVariableException (variable: string, stack: StackFrame list) =
    inherit PrologException($"The variable %s{variable} was not bound in the current scope", stack)