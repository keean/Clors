member(Key, cons(def(Key, Val), Tail), just(Val)).
member(Key, nil, nothing).
member(Key, cons(Head, Tail), Val) :-
    member(Key, Tail, Val).

append(nil, L, L).
append(cons(H, T1), L, cons(H, T2)) :-
    append(T1, L, T2).

unifyall(nil, T).
unifyall(cons(T, Tail), T) :-
    unifyall(Tail, T).

split(X, nil, nil, nil).
split(X, cons(def(X, T), Tail1), cons(T, Tail2), Tail3 ) :-
    split(X, Tail1, Tail2, Tail3).
split(X, cons(def(Y, T), Tail1), Tail2, cons(def(Y, T), Tail3)) :-
    split(X, Tail1, Tail2, Tail3).

typing(Env, lam(Var, Body), Cxt, arrow(A, B)) :-
    typing(Env, Body, C1, B),
    split(Var, C1, Def, Cxt),
    unifyall(Def, A).
typing(Env, app(Fun, Arg), Cxt, B) :-
    typing(Env, Fun, C1, arrow(A, B)),
    typing(Env, Arg, C2, A),
    append(C1, C2, Cxt).
typing(Env, var(X), Cxt, Type) :-
    member(X, Env, just(ty2(Cxt, Type))).
typing(Env, var(X), cons(def(X, Type), nil), Type) :-
    member(X, Env, nothing).

#:- typing(cons(def(i1, ty2(nil, int)), nil), var(i1), C, T).
#:- typing(cons(def(i1, ty2(nil, int)), nil), var(x), C, T).
#:- typing(cons(def(i1, ty2(nil, int)), nil), app(var(x), var(i1)), C, T).
#:- typing(cons(def(i1, ty2(nil, int)), nil),              lam(x, app(x, i1)), C, T).
#:- typing(cons(def(i1, ty2(nil, int)), nil),               app(f, app(x, i1)), C, T).
#:- typing(cons(def(i1, ty2(nil, int)), nil),        lam(x, app(f, app(x, i1))), C, T).
:- typing(cons(def(i1, ty2(nil, int)), nil), lam(var(f), lam(var(x), app(var(f), app(var(x), var(i1))))), C, T).
#:- typing(cons(def(i1, ty2(nil, int)), cons(def(b1, ty2(nil, bool)), nil)),
#    lam(f, lam(x, lam(x, app(app(var(f), app(var(x), var(i1))), app(var(x), var(b1)))))), C, T).
#:- typing(cons(def(i1, ty2(nil, int)), cons(def(b1, ty2(nil, bool)), nil)),
#    lam(f, lam(x, app(app(var(f), app(var(x), lam(z, var(z)))), app(var(x), lam(u, lam(v, var(u))))))), C, T).
#:- typing(cons(def(i1, ty2(nil, int)), cons(def(b1, ty2(nil, bool)), nil)),
#    lam(x, app(var(x), var(x))), C, T).

