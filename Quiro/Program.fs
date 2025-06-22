open System
open System.Collections.Generic
open System.IO
open Quiro
open Quiro.BuiltinTerms

[<EntryPoint>]
let main args =
    // file/process_lines(Path, Lines), sort(List, Sorted), convert/string-list concat(Groups, Separator, Combined)
    
    let mutable terms = StoredTerms.defaultTerms()
    
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
                let vars = Dictionary()
                let goal = Interpreter.Internal.reifyTerm vars goalAST
                
                try
                    match Interpreter.query goal terms debugLevel with
                    | ValueSome bindings ->
                        printfn "Yes\r\n"
                        
                        let cached = Seq.cache bindings
                        let showGroup (bindingGroup: (Var * Term)[]) =
                            for (Var (variable, _), value) in bindingGroup do
                                printfn $"%s{variable} = %s{Term.toString value}"

                            if bindingGroup.Length > 1 then
                                printfn ""  
                        
                        if cached |> Seq.tail |> Seq.isEmpty then
                            showGroup (Seq.head cached)
                        else
                            let mutable viewMore = true
                            let enumerator = cached.GetEnumerator()
                            
                            while viewMore && enumerator.MoveNext() do
                                showGroup enumerator.Current
                                Console.Write "-- "
                                viewMore <- Console.ReadKey().KeyChar = ';'
                                Console.WriteLine()

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