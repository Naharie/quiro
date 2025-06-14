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
    | ExprGoal of goal:PrologGoalAST
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

type PrologGoalAST = {
    goalKind: PrologGoalASTKind
    location: FileLocation
}

type DeclarationKind =
    | PredicateDeclaration of functor:string * arguments:PrologExprAST list * goal:PrologGoalAST
    | FunctionDeclaration of functor:string * arguments:PrologExprAST list * body:PrologExprAST
    
type Declaration = {
    decKind: DeclarationKind
    location: FileLocation
}