open System
open System.IO
open Quiro

[<EntryPoint>]
let main args =
    // https://en.wikipedia.org/wiki/Prolog_syntax_and_semantics
    
    let mutable terms = StoredTerms.emptyTerms()
    
    terms.nativePredicates[("print", 1)] <- ResizeArray()
    terms.nativePredicates[("print", 1)].Add (fun _ args ->
        Console.WriteLine(PrologValue.toString args[0])
        ValueSome [| Map.empty |]
    )
    
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
        elif code.StartsWith ".toggle" then
            Parser.setLanguageServerMode (Parser.isInLanguageServerMode() |> not)
        elif code.StartsWith ".load " then
            try
                let path = code[6..].Trim('\'', '"')
                let fileName = Path.GetFileName path
                let scriptCode = File.ReadAllText path
                
                match Parser.parseScript fileName scriptCode with
                | Ok declarations ->
                    for declaration in declarations do
                        Interpreter.storeDeclaration declaration.decKind terms
                    
                | Error parseError ->
                    printfn $"%s{parseError}"
            with
            | err ->
                printfn $"%O{err}"
        elif isQuery then
            match Parser.parseGoal "<repl>" code with
            | Ok goalAST ->
                let debugLevel = if printDebugInfo then RuleOnly else NoDebugInfo
                let goal = Interpreter.Internal.reifyGoal goalAST
                
                try
                    match Interpreter.query goal terms debugLevel with
                    | ValueSome bindings ->
                        printfn "Yes"
                        if bindings.Length > 1 then printfn ""

                        for bindingGroup in bindings do
                            for KeyValue(variable, value) in bindingGroup do
                                printfn $"%s{variable} = %s{PrologValue.toString value}"

                            if bindingGroup.Count > 1 then
                                printfn ""  

                    | ValueNone -> printfn "No\r\n"
                with
                | :? PrologException as error ->
                    printfn $"%O{error}"

            | Error message ->
                printfn $"%s{message}"
        else
            match Parser.parseDeclaration "<repl>" code with
            | Ok declaration ->
                Interpreter.storeDeclaration declaration terms
                printfn "Stored"
            | Error message ->
                printfn $"%s{message}"
    
    0