module Quiro.IOTerms

open System
open System.IO
open Microsoft.FSharp.Core
open Quiro.Interpreter.Internal
open Quiro.TermHelpers

let create terms =
    let addPred = addPred terms
    
    describe "nl" "nl" "Prints a newline to stdout."
    addPred ("nl", 0) (fun context _ ->
        Console.WriteLine()
        emptySuccess context
    )
    
    describe "write" "write(?Value)" "Prints a value to stdout or a reads a character from stdin."
    addPred ("write", 1) (fun context args ->
        match args[0] with
        | Variable name ->
            let value = Console.ReadLine()
            ValueSome [| [| name, (Text value) |], context.substitutions |]

        | Text text ->
            Console.Write text
            emptySuccess context

        | value ->
            Console.Write(Term.toString value)
            emptySuccess context
    )
    
    describe "file:process_lines" "file:process_lines(+Path, ?Lines)" "Reads all lines from a text file or writes all lines to a file."
    addPred ("file:process_lines", 2) (fun context args ->
        match args with
        | [ Text path; lines ] ->
            let isRead = hasFreeVariables lines
            
            if isRead then
                let textLines = File.ReadAllLines(path)
                let term = ListTerm (textLines |> Array.map Text |> Array.toList)
                
                unify lines term
                |> ValueOption.map (fun frame -> Seq.singleton (frame, context.substitutions))
            else
                match lines with
                | ListTerm lines ->
                    let textLines =
                        lines
                        |> List.map (function
                            | Text v -> v
                            | other -> Term.toString other
                        )
                        |> List.toArray
                    
                    File.WriteAllLines(path, textLines)
                    emptySuccess context
                | _ -> ValueNone
        | _ -> ValueNone
    )