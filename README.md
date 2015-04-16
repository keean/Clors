Clors
=====

Clors logic language. A Horn clause interpreter with sound unification (post unification cycle check), a complete search strategy (iterative-deepening), and complete inference (work-in-progress).

The complete inference is based around implementing disequality by consraint propagation which is already implemented. The negation-elimination, such that 'not member' is constructed from 'member' by term rewriting is work in progress, and my current understanding is that this requires some kind of type inference.

example.cl: Compositional HM type inference.<br/>
heyting.cl: Proving distributivity of heyting algebras.
