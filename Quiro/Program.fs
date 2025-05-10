open System
open System.IO
open System.Runtime.InteropServices.JavaScript
open Quiro
open Quiro.DataTypes

// TODO: Allow cuts (func(x, y) -> a, b, !, c) where only c is returned.

[<EntryPoint>]
let main args =
    let mutable scope = Scope.defaultScope
    
    printfn "End a declaration with . to store it, end a query with ? to run it."
    printfn "You can use .load <path> to load a script file."
    
    while true do
        printf "?- "
        
        let isQuery, printDebugInfo, code =
            let raw = Console.ReadLine()
            
            if raw.EndsWith "??" then
                true, true, raw[0..^2]
            elif raw.EndsWith "?" then
                true, false, raw[0..^1]
            elif not (raw.EndsWith ".") then
                true, false, raw
            else
                false, false, raw

        if String.IsNullOrWhiteSpace code then ()
        elif code.StartsWith ".load " then
            try
                let scriptCode = File.ReadAllText (code[6..].Trim('\'', '"'))
                
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
                let debugLevel = if printDebugInfo then RuleOnly else NoDebugInfo
                
                try
                    match Interpreter.query goal scope debugLevel with
                    | Some bindings ->
                        printfn "Yes"
                        if bindings.Length > 1 then printfn ""

                        for bindingGroup in bindings do
                            for KeyValue(variable, value) in bindingGroup do
                                printfn $"%s{variable} = %s{PrologExpression.toString value}"

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