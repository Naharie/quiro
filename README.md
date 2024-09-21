# Quiro

Quiro is a simplistic prolog interpreter written in F#.
It has few builtin predicates, but the most important ones are: print, nl, <, <=, >, >=, =, =:=, and is.
It supports full logic lookups, number ranges, expressions, functions, and predicates inside functions.
When running it acts as a REPL. End a declaration with . to store it. Leave off the period or end a query with ? to execute it.
You can use .load script-path to load a script file.

The entire interpreter is contained in Interpreter.fs and all the builtins are defined in Scope.fs.
The parser is similarly stored in the file named Parser.fs.
If you don't know much prolog or don't care to come up with an example yourself, consider trying to the classic family relationship demo:

```prolog
human(socrates).
mortal(X) :- human(X).

mother_child(trude, sally).
father_child(tom, sally).
father_child(tom, erica).
father_child(mike, tom).
sibling(X, Y)      :- parent_child(Z, X), parent_child(Z, Y).
parent_child(X, Y) :- father_child(X, Y).
parent_child(X, Y) :- mother_child(X, Y).

ancestor(X, Y) :- parent_child(X, Y).
ancestor(X, Y) :- parent_child(X, Z), ancestor(Z, Y).
```

Then trying running a query such as `sibling(sally, erica)?` or `ancestor(mike, sally)?`.
Define more humans or mortal creatures and run `mortal(Y)?` to see the interpreter find all possible bindings for that variable.