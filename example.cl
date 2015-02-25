member(Key, cons(Head, Tail), Val) :-
    dif(Key,Head),
    member(Key, Tail, Val).
member(Key, cons(def(Key, Val), Tail), just(Val)).
member(Key, nil, nothing).

append(cons(H, T1), L, cons(H, T2)) :-
    append(T1, L, T2).
append(nil, L, L).

unifyall(cons(T, Tail), T) :-
    unifyall(Tail, T).
unifyall(nil, T).

unifyeach(cons(Tapp, Tail), Tdef, Cxt) :-
    duplicate_term(Tdef, pair(C1, Tapp)),
    unifyeach(Tail, Tdef, Csub),
    append(Csub, C1, Cxt).
unifyeach(nil, T, nil).

split(X, cons(def(Y, T), Tail1), Tail2, cons(def(Y, T), Tail3)) :-
    dif(X, Y),
    split(X, Tail1, Tail2, Tail3).
split(X, cons(def(X, T), Tail1), cons(T, Tail2), Tail3 ) :-
    split(X, Tail1, Tail2, Tail3).
split(X, nil, nil, nil).

nat(zero).
nat(succ(X)) :-
    nat(X).

bool(true).
bool(false).

expr(var(X), cons(def(X, Type), nil), Type).
expr(nat(X1), nil, nat) :-
    nat(X).
expr(bool(X), nil, bool) :-
    bool(X).
expr(pair(X, Y), C3, prod(A, B)) :-
    expr(X, C1, A),
    expr(Y, C2, B),
    append(C1, C2, C3).
expr(app(Fun, Arg), Cxt, B) :-
    expr(Fun, C1, arrow(A, B)),
    expr(Arg, C2, A),
    append(C1, C2, Cxt).
expr(lam(Var, Body), Cxt, arrow(A, B)) :-
    expr(Body, C1, B),
    split(Var, C1, Def, Cxt),
    unifyall(Def, A).
expr(let(Var, Body, Rhs), Cxt, T2) :-
    expr(Body, C1, T1),
    expr(Rhs, C2, T2),
    split(Var, C2, Def, C3),
    unifyeach(Def, pair(C1, T1), C4),
    append(C3, C4, Cxt).

:- expr(
  let(cast2, lam(f, lam(x, lam(y, app(app(var(f), var(x)), var(y))))), var(cast2)),
Cxt, Typ).

