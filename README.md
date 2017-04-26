Clors
=====

Clors logic language. A Horn clause interpreter with sound unification (post unification cycle check), a complete search strategy (iterative-deepening), and complete inference (work-in-progress).

The complete inference is based around implementing disequality by consraint propagation which is already implemented. The negation-elimination, such that 'not member' is constructed from 'member' by term rewriting is work in progress, and my current understanding is that this requires some kind of type inference.

## Examples ##

#### Membership Test ####
Input
```
member(Key, cons(Head, Tail), Val) :-
    dif(Key,Head),
    member(Key, Tail, Val).
member(Key, cons(def(Key, Val), Tail), just(Val)).
member(Key, nil, nothing).
```
Output
```
DEPTH 3 ELAPSED TIME: 44us

PROOF:
3.	member(Key1 = b, cons(def(K1 = a, V1 = z), Tail1 = cons(def(b, y), cons(def(c, x), nil))), Val1 = just(y)) :-
	dif(Key1 = b, K1 = a),
	member(Key1 = b, Tail1 = cons(def(b, y), cons(def(c, x), nil)), Val1 = just(y)).
0.	dif(Key1 = b, K1 = a).
1.	member(Key2 = b, cons(def(Key2 = b, Val2 = y), Tail2 = cons(def(c, x), nil)), just(Val2 = y)) [Key2, Val2].
```
#### Commutativity of a Heyting algebra ####
Input
```
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
```
Output
```
DEPTH 13 ELAPSED TIME: 1281421us

PROOF:
21.	rule(A1 = meet(a, join(b, c)), B1 = join(meet(a, b), meet(a, c))) :-
	rule(A1 = meet(a, join(b, c)), C1 = le(meet(a, join(b, c)), true)),
	rule(C1 = le(meet(a, join(b, c)), true), B1 = join(meet(a, b), meet(a, c))).
7.	rule(A2 = meet(a, join(b, c)), le(A2 = meet(a, join(b, c)), true)).
21.	rule(A3 = le(meet(a, join(b, c)), true), B2 = join(meet(a, b), meet(a, c))) :-
	rule(A3 = le(meet(a, join(b, c)), true), C2 = le(join(b, c), impl(a, true))),
	rule(C2 = le(join(b, c), impl(a, true)), B2 = join(meet(a, b), meet(a, c))).
20.	rule(le(meet(A4 = a, C3 = join(b, c)), B3 = true), le(C3 = join(b, c), impl(A4 = a, B3 = true))).
21.	rule(A5 = le(join(b, c), impl(a, true)), B4 = join(meet(a, b), meet(a, c))) :-
	rule(A5 = le(join(b, c), impl(a, true)), C4 = pair(le(b, impl(a, true)), le(c, impl(a, true)))),
	rule(C4 = pair(le(b, impl(a, true)), le(c, impl(a, true))), B4 = join(meet(a, b), meet(a, c))).
13.	rule(le(join(A6 = b, B5 = c), C5 = impl(a, true)), pair(le(A6 = b, C5 = impl(a, true)), le(B5 = c, C5 = impl(a, true)))).
21.	rule(A7 = pair(le(b, impl(a, true)), le(c, impl(a, true))), B6 = join(meet(a, b), meet(a, c))) :-
	rule(A7 = pair(le(b, impl(a, true)), le(c, impl(a, true))), C6 = le(join(meet(a, b), meet(a, c)), true)),
	rule(C6 = le(join(meet(a, b), meet(a, c)), true), B6 = join(meet(a, b), meet(a, c))).
21.	rule(A8 = pair(le(b, impl(a, true)), le(c, impl(a, true))), B7 = le(join(meet(a, b), meet(a, c)), true)) :-
	rule(A8 = pair(le(b, impl(a, true)), le(c, impl(a, true))), C7 = pair(le(meet(a, b), true), le(meet(a, c), true))),
	rule(C7 = pair(le(meet(a, b), true), le(meet(a, c), true)), B7 = le(join(meet(a, b), meet(a, c)), true)).
22.	rule(pair(A9 = le(b, impl(a, true)), B8 = le(c, impl(a, true))), pair(X1 = le(meet(a, b), true), Y1 = le(meet(a, c), true))) :-
	rule(A9 = le(b, impl(a, true)), X1 = le(meet(a, b), true)),
	rule(B8 = le(c, impl(a, true)), Y1 = le(meet(a, c), true)).
19.	rule(le(C8 = b, impl(A10 = a, B9 = true)), le(meet(A10 = a, C8 = b), B9 = true)).
19.	rule(le(C9 = c, impl(A11 = a, B10 = true)), le(meet(A11 = a, C9 = c), B10 = true)).
14.	rule(pair(le(A12 = meet(a, b), C10 = true), le(B11 = meet(a, c), C10 = true)), le(join(A12 = meet(a, b), B11 = meet(a, c)), C10 = true)).
8.	rule(le(A13 = join(meet(a, b), meet(a, c)), true), A13 = join(meet(a, b), meet(a, c))).

yes.
```


