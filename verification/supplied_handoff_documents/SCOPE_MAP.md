# Exact original-question map

All entries below are source declarations with proof bodies. **None has
been compiled or kernel-verified in this project.**

| Original scope | Source endpoint | Quantifiers and meaning |
| --- | --- | --- |
| 1997 family formulation | `JSP539.OriginalScope.erdos_664` in `JSP539/OriginalScope.lean` | Negates the assertion that every real 0<c<1 has a natural K working for every n, m, indexed family with strict c√n block sizes and pairwise intersections at most one |
| Explicit two-fifths family variant | `JSP539.OriginalScope.two_fifths` in the same file | Rules out every natural K at c=2/5, with all n, m and all candidate transversals |
| 1981 exact pairwise-balanced design formulation | `JSP539.OriginalScope.block_design` in the same file | Negates the assertion for all positive real c; every two distinct points must lie in exactly one indexed block |
| Explicit two-fifths exact-pair version | `JSP539.OriginalScope.two_fifths_exact_pairs` in the same file | Rules out every natural K even with exact pair coverage, at c=2/5 |
| Counterexample with unbounded ground-set size | `JSP539.exists_bad_fin_design` in the same file | For every K and n₀, constructs n≥n₀, m and A:Fin m→Finset(Fin n), strict two-fifths size, exact pair coverage, linear intersections, and every transversal has some intersection>K |

The exact-pair clause is an original question from 1981, not a newly invented
extension. The family and explicit two-fifths results already have public
Lean predecessors. The intended new scope here is the exact-pair clause.
The official eligibility field is still “No”; this package does not establish
prize eligibility.

`JSP539.Affine.exists_bad_exact_design` in `RandomRestriction.lean` discharges
the actual affine-plane/random-restriction construction. It has only K and n₀
as external parameters. `FiniteDesignTransport.lean` constructs the ground
and block enumerations, preserves all cardinalities and candidate
transversals, and proves uniqueness of a block index rather than only a
block set.

No statement assumes the existence of containers, a successful random sample,
an external counterexample, or a graph/design isomorphism. The finite
container theorem, tree count, eventual numerical inequalities, fair-bit
independence and exponential tails all have local proof bodies. Static source
checking found no admissions or declared nonstandard axioms; actual
`#print axioms` output must be produced by the user's compilation.

This package does not claim the stronger asymptotic log(n)/log log(n) bound
from Nie's paper. That stronger rate is not needed to refute the original
uniform-K assertions.

## Explicit real-bound adapters

`JSP539/RealScope.lean` adds `exists_bad_fin_design_real`,
`OriginalScope.erdos_664_real`, and `OriginalScope.block_design_real`.
Their universal proposed intersection bound is an arbitrary real number.
The adapter chooses its natural ceiling and invokes the unchanged construction.
This is a quantifier adapter, not a new geometric theorem.
