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
                let trace = if shouldTrace then All else NoTrace
                
                try
                    match Interpreter.query goal scope trace with
                    | Some bindings ->
                        printfn "Yes"
                        
                        if bindings.Length > 1 then
                            printfn ""

                        for bindingGroup in bindings do
                            for KeyValue(variable, value) in bindingGroup do
                                match value with
                                | ListTerm values ->
                                    let isText = values |> List.forall(function | Number (Float v) -> v.DecimalPlaces <= 0 | _ -> false)
                                    
                                    if isText then
                                        let text =
                                            values
                                            |> List.map (function
                                                | Number (Float v) -> char v.WholeValue
                                                | _ -> ' '
                                            )
                                            |> List.toArray
                                            |> String
                                            |> _.Replace("\\", "\\\\").Replace("\"", "\\\"")
                                        
                                        printfn $"%s{variable} = \"%s{text}\""
                                    else
                                        printfn $"%s{variable} = %s{Expression.toString value}"

                                | _ ->
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