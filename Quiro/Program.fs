open System
open System.IO
open System.Runtime.InteropServices.JavaScript
open Quiro
open Quiro.DataTypes

[<EntryPoint>]
let main args =
    let mutable scope = Scope.defaultScope
 
    printfn "End a declaration with . to store it, end a query with ? to run it."
    printfn "You can use .load <path> to load a script file."
    
    while true do
        printf "?- "
        let isQuery, shouldTrace, code =
            let raw = Console.ReadLine()
            
            if raw.EndsWith "??" then
                true, true, raw[0..^2]
            elif raw.EndsWith "?" then
                true, false, raw[0..^1]
            elif not (raw.EndsWith ".") then
                true, false, raw
            else
                false, false, raw

        if code.StartsWith ".load " then
            let path = code[6..].Trim('\'', '"')
            
            try
                let scriptCode = File.ReadAllText path
                
                match Parser.parseScript scriptCode with
                | Ok declarations ->
                    for declaration in declarations do
                        scope <- Interpreter.execute declaration scope
                    
                | Error parseError ->
                    printfn $"%s{parseError}"
            with
            | err ->
                printfn $"%O{err}"
        elif isQuery then
            match Parser.parseGoal code with
            | Ok goal ->
                let trace = if shouldTrace then All else NoTrace

                try
                    match Interpreter.query goal scope trace with
                    | Some bindings ->
                        printfn "Yes"
                        
                        if bindings.Length > 1 then
                            printfn ""

                        for bindingGroup in bindings do
                            for KeyValue(variable, value) in bindingGroup do
                                printfn $"%s{variable} = %s{Expression.toString value}"

                            if bindingGroup.Count > 1 then
                                printfn ""  

                    | None -> printfn "No\r\n"
                with
                | :? PrologException as error ->
                    printfn $"%O{error}"
            | Error message ->
                printfn $"%s{message}"
        else
            match Parser.parseDeclaration code with
            | Ok declaration ->
                scope <- Interpreter.execute declaration scope
                printfn "Stored"
            | Error message ->
                printfn $"%s{message}"
    
    0