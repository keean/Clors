# conjunction as meet
rule(meet(A, B), le(meet(A, B), A)).
rule(le(meet(A, B), A), meet(A, B)).
rule(meet(A, B), le(meet(A, B), B)).
rule(le(meet(A, B), B), meet(A, B)).
rule(le(C, meet(A, B)), pair(le(C, A), le(C, B))).
rule(pair(le(C, A), le(C, B)), le(C, meet(A, B))).

# truth as greatest element
rule(A, le(A, true)).
rule(le(A, true), A).

# disjunction as join
rule(join(A, B), le(A, join(A, B))).
rule(le(A, join(A, B)), join(A, B)).
rule(join(A, B), le(B, join(A, B))).
rule(le(B, join(A, B)), join(A, B)).
rule(le(join(A, B), C), pair(le(A, C), le(B, C))).
rule(pair(le(A, C), le(B, C)), le(join(A, B), C)).

# falsehood as least element
rule(A, le(false, A)).
rule(le(false, A), A).

# implication as exponential
rule(meet(A, impl(A, B)), le(meet(A, impl(A, B)), B)).
rule(le(meet(A, impl(A, B)), B), meet(A, impl(A, B))).
rule(le(C, impl(A, B)), le(meet(A, C), B)).
rule(le(meet(A, C), B), le(C, impl(A, B))).

# inference rules, Transitive.
#rule(A, B) :- rule(B, A).
rule(A, B) :- rule(A, C), rule(C, B).
rule(pair(A, B), pair(X, Y)) :- rule(A, X), rule(B, Y).
rule(pair(A, B), pair(Y, X)) :- rule(A, X), rule(B, Y).

:- rule(meet(a, join(b, c)), join(meet(a, b), meet(a, c))).

