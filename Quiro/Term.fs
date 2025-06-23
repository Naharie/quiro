namespace rec Quiro

type Var = Var of name:string * id:int

type Term =
    // a, 'b', 'hello'
    | Atom of atom:string
    // 1, 1.5, nan, infinity
    | Number of float
    // "Hello World"
    | Text of string
    
    // X, Y
    | Variable of Var
    
    // [ Head | Tail ]
    | ListCons of head:Term * tail:Term
    // [ 1, 2, 3 ]
    | ListTerm of list:Term list
    
    // func(x, y)
    | Term of target:string * args:Term list

    | Negation of Term
    | Conjunction of Term[]
    | Disjunction of Term[]

[<RequireQualifiedAccess>]
type DCG =
    | Term of string
    | Call of functor:string * args:Term list
    // { Goal }
    | Goal of Term
    | List of Term list
    | Sequence of DCG[]

module Term =
    let makeVar =
        let mutable counter = 1
        let blank = Variable(Var("_", -1))
        
        fun name ->
            if name = "_" then blank
            else
                let var = Variable(Var(name, counter))
                counter <- counter + 1
                var

    let rec toString (term: Term) =
        match term with
        | Atom name -> name
        | Variable (Var(name, _)) -> name
        | Number value -> string value
        | Text value ->
            let escaped =
                value
                    .Replace("\\", "\\\\")
                    .Replace("\"", "\\\"")
                    .Replace("\r", "\\r")
                    .Replace("\n", "\\n")
                    .Replace("\t", "\\t")
                    
            "\"" + escaped + "\""
            
        | ListTerm values ->
            values
            |> List.map toString
            |> String.concat ", "
            |> sprintf "[ %s ]"
        | ListCons _ ->
            let rec go value =
                match value with
                | Atom "nil" | ListTerm [] -> []
                | ListCons(head, tail) -> head :: go tail
                | _ -> [ value ]

            go term
            |> List.map toString
            |> String.concat ", "
            |> sprintf "[ %s ]"
            
        | Term(functor, args) ->
            let args =
                args
                |> List.map toString
                |> String.concat ", "
            
            $"%s{functor}(%s{args})"
        | Negation term -> $"\+ {toString term}"
        | Conjunction terms ->
            terms
            |> Array.map toString
            |> String.concat ", "
        | Disjunction terms ->
            terms
            |> Array.map toString
            |> String.concat "; "