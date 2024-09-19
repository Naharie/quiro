open System
open System.IO
open Quiro
open Quiro.DataTypes

[<EntryPoint>]
let main args =
    let mutable scope = Scope.defaultScope
 
    printfn "End a declaration with . to store it, end a query with ? to run it."
    printfn "You can use .load <path> to load a script file."
    
    // TODO: Temp
    printfn $"%A{Parser.parseExpression (Console.ReadLine())}"
    
    while true do
        printf "?- "
        let isQuery, code =
            let raw = Console.ReadLine()
            
            if raw.EndsWith "?" then
                true, raw[0..^1]
            elif not (raw.EndsWith ".") then
                true, raw
            else
                false, raw

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
                match Interpreter.query goal scope with
                | Ok status ->
                    match status with
                    | Some bindings ->
                        printfn "Yes"
                        printfn ""

                        for bindingGroup in bindings do
                            for KeyValue(variable, value) in bindingGroup do
                                printfn $"%s{variable} = %s{Expression.toString value}"

                            printfn ""  

                    | None -> printfn "No\r\n"
                    
                | Error error ->
                    PrologError.displayError error
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