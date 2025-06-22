module rec Quiro.AST

type FileLocation = {
    file: string
    index: int64
    line: int64
    column: int64
}

type TermASTKind =
    | ExprAtom of atom:string
    | ExprNumber of BigFloat
    | ExprText of string
    | ExprListTerm of elements:TermAST list
    | ExprTerm of target:string * args:TermAST list
    | ExprVariable of name:string
    | ExprListCons of head:TermAST * tail:TermAST
    | ExprNegation of TermAST
    | ExprConjunction of TermAST[]
    | ExprDisjunction of TermAST[]
    | ExprPlaceholder

type TermAST = {
    termKind: TermASTKind
    location: FileLocation
}

type DCTAstKind =
    | DCGTerm of string
    | DCGCall of functor:string * args:TermAST list
    | DCGGoal of TermAST
    | DCGList of TermAST list
    | DCGSequence of DCGAST[]

type DCGAST = {
    dcgKind: DCTAstKind
    location: FileLocation
}

type DeclarationKind =
    | PredicateDeclaration of functor:string * arguments:TermAST list * goal:TermAST
    | DCGDeclaration of functor:string * arguments:TermAST list * body:DCGAST
    
type Declaration = {
    decKind: DeclarationKind
    location: FileLocation
}