module rec Quiro.AST

type FileLocation = {
    file: string
    index: int64
    line: int64
    column: int64
}

type PrologExprASTKind =
    | ExprAtom of atom:string
    | ExprNumber of BigFloat
    | ExprText of string
    | ExprListTerm of elements:PrologExprAST list
    | ExprTerm of target:string * args:PrologExprAST list
    | ExprVariable of name:string
    | ExprListCons of head:PrologExprAST * tail:PrologExprAST
    | ExprPlaceholder

type PrologExprAST = {
    exprKind: PrologExprASTKind
    location: FileLocation
}

type PrologGoalASTKind =
    | GoalPlaceholder
    | GoalSimple of functor:string * args:PrologExprAST list
    | GoalNegated of PrologGoalAST
    | GoalConjunction of PrologGoalAST[]
    | GoalDisjunction of PrologGoalAST[]

type DCTAstKind =
    | DCGTerm of string
    | DCGCall of functor:string * args:PrologExprAST list
    | DCGGoal of PrologGoalAST
    | DCGList of PrologExprAST list
    | DCGSequence of DCGAST[]

type DCGAST = {
    dcgKind: DCTAstKind
    location: FileLocation
}

type PrologGoalAST = {
    goalKind: PrologGoalASTKind
    location: FileLocation
}

type DeclarationKind =
    | PredicateDeclaration of functor:string * arguments:PrologExprAST list * goal:PrologGoalAST
    | DCGDeclaration of functor:string * arguments:PrologExprAST list * body:DCGAST
    
type Declaration = {
    decKind: DeclarationKind
    location: FileLocation
}