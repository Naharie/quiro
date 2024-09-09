open System
open System.IO
open Quiro
open Quiro.DataTypes

[<EntryPoint>]
let main args =
    let mutable scope = Scope.defaultScope
 
    printfn "You can use usage(Builtin) to view the usage for a builtin."
    printfn "[usage(Rule) :- describe(Rule, Desc), print(Desc), nl]"
    printfn "You can use .load <path> to load a script file."
    
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
                | Ok rules ->
                    for rule in rules do
                        scope <- Interpreter.execute rule scope
                    
                | Error parseError ->
                    printfn $"%s{parseError}"
            with
            | err ->
                printfn $"%O{err}"
        elif isQuery then
            match Parser.parseGoal code with
            | Ok goal ->
                match Interpreter.query goal scope with
                | Some bindings ->
                    printfn "Yes"
                    printfn ""

                    for bindingGroup in bindings do
                        for KeyValue(variable, value) in bindingGroup do
                            printfn $"%s{variable} = %s{SimpleTerm.toString value}"

                        printfn ""  

                | None -> printfn "No\r\n"
            | Error message ->
                printfn $"%s{message}"
        else
            match Parser.parseRule code with
            | Ok rule ->
                scope <- Interpreter.execute rule scope
                printfn "Stored"
            | Error message ->
                printfn $"%s{message}"
    
    0