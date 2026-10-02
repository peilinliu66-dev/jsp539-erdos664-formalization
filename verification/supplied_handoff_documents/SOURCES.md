# Mathematical and software sources

## Original question

- [Official JSP539 entry](https://github.com/TheJustinSunPrize/awards/blob/5125fd797a5a5e63588406feceb8f08ca72c491a/problems/catalog-0501-0600.md#JSP-000539)
- [Erdős problem 664](https://www.erdosproblems.com/664)
- Erdős, *On the combinatorial problems which I would most like to see
  solved*, Combinatorica (1981), 25–42: exact pairwise-balanced formulation
- Alon, [*A remark on a problem of Erdős*](https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf):
  earlier negative answer for pairwise intersections at most one

## Proof sources and changes made here

1. Jiaxi Nie, [*Block Designs with Large Transversal–Block Intersections*,
   arXiv:2609.07736v1](https://arxiv.org/html/2609.07736v1), September 2026.
   Theorem 1.2 supplies the mathematical resolution of the exact-design
   version. This project uses its random-restriction/container route with
   fixed k=K+2. It uses an affine plane, a coarser but sufficient finite
   disjoint-trace packing, and the size constant 2/5. It does not claim the
   paper's quantitative logarithmic lower bound. The paper is listed under
   CC BY-NC-ND 4.0; its text or figures are not redistributed in this package.
   The new Lean files implement the mathematical ideas with independently
   written proof bodies.
2. Marcelo Campos and Wojciech Samotij,
   [*Towards an optimal hypergraph container lemma*, arXiv:2408.06617](https://arxiv.org/abs/2408.06617),
   Theorem A and Section 3. The finite algorithm, potential charging,
   deterministic reconstruction, and shrinking consequence are proved in
   the project. Container existence is not an assumption of the endpoint.
   [Published article](https://link.springer.com/article/10.1007/s00493-026-00214-1)
3. The elementary probability arguments are independently written as
   normalized finite sums. No external Janson or Chernoff theorem is assumed.
   The line-tail constant follows from exponential Markov at log(11/10).

## Copied software

Five explicitly Apache-2.0-licensed helpers from
[plby/lean-proofs](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos565):
`Hypergraph`, `ContainerFuel`, `ContainerInvariants`, `ContainerWeight`,
and `ContainerSelector`. Their original attribution and namespace are
preserved. Imports are redirected to `LicensedContainers`. An unused
`FiniteAnalysis` import is replaced with `Mathlib`; that upstream file is
not copied. Exact file hashes and modifications are recorded separately.

No upstream `ContainerA`, `ContainerConsistency`, E664 implementation,
probability library without an explicit file license, or paper full text
is included. `Mathlib` and its dependency versions are pinned in the manifest.

## Bounded prior-source assessment

Selection evidence was frozen on 2026-10-02 before implementation. Official
PRs 1021, 1644, 1824, 2823 and 4027 were checked in every state, with their
comments and linked source repositories. The substantive earlier plby and
Cyr endpoints cover the at-most-once family; randomizing incidences
independently does not preserve exact pair coverage. Other located sources
were finite examples, statements, or explicit assumptions at the exact-design
endpoint. This supports a concrete additional-scope target, not a global
first-formalization guarantee.

At the catalog pin, the displayed eligibility field is **“Eligible to claim:
No”**. The work targets the original 1981 exact-pair clause, which the located
prior partial-design implementations do not discharge. That additional
original scope does not by itself establish prize eligibility or overturn
the organizer's earlier priority decision for the partial-design result.

The dated evidence artifact is
`JSP539_SELECTION_EVIDENCE_NOT_A_PROOF_20261002.zip`, SHA256
`4dd9de96a4a4ab019053733f1fae6ec4b88be1c7293cd2bad469075c1382c79c`.
It is not a proof or a compilation receipt. This handoff has remained
private; its timestamps are not public proof-priority evidence.
