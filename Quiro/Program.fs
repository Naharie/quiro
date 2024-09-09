open System
open Quiro
open Quiro.DataTypes

[<EntryPoint>]
let main args =
    let mutable scope = Scope.defaultScope
 
    printfn "Enter a rule followed by a period to create a new rule or enter a query followed by a question mark to test that query."
    printfn "Only basic prolog syntax applies. Create a rules as normal [mortal(X) :- human(X).]."
    printfn "Conjunction, disjunction, and negation may be performed, but parenthesis may not be used to order operations, create a sub rule instead."
    printfn "There is no list destructuring syntax, use a goal of cons(Head, Tail, List) instead."
    printfn "Similarly, there is no syntax for variable bindings, use equal(Var, Value) instead."
    printfn "You can use usage(Builtin) to view the usage for a builtin."
    printfn "[usage(Rule) :- describe(Rule, Desc), print(Desc), nl]"
    printfn "Define describe(RuleFunctor, Description) to define usage for your own rules."
    
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

        if isQuery then
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