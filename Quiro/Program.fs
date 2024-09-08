open System
open Quiro

[<EntryPoint>]
let main args =
    let mutable scope = Scope.defaultScope
 
    while true do
        printf "?- "
        let isQuery, code =
            let raw = Console.ReadLine()
            
            if raw.EndsWith "?" then
                true, raw[0..^1] + "."
            else
                false, raw
        let rule = Parser.parse code
        
        match rule with
        | Ok rule ->
            if isQuery then
                match Interpreter.query rule scope with
                | Ok (Some bindings) ->
                    printfn "Yes"

                    for bindingGroup in bindings do
                        for KeyValue(variable, value) in bindingGroup do
                            printfn $"%s{variable} = %s{Interpreter.show value}"

                | Ok None -> printfn "No\r\n"
                | Error message -> printfn $"%s{message}"
            else
                scope <- Interpreter.execute rule scope
                printfn "Done"
        | Error message ->
            printfn $"%s{message}"
    
    0