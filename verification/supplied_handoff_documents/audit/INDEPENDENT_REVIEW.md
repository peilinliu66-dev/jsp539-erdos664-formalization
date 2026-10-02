# JSP539: independent mathematical and source review

Review date: 2026-10-02, 07:21–07:30 UTC.

## Conclusion and limits

No mathematical gap was identified in the fixed-bound route reviewed here.
The original quantifiers are reached by genuine finite geometry, a finite
container construction, and a joint random-restriction argument. The
additional real-bound adapter makes the ceiling conversion explicit in Lean
source rather than leaving it to prose.

**This is not a Lean build, elaboration result, expanded-axiom output, or kernel
check. Every source file remains UNCOMPILED.** Finite tests below are sanity
checks of independent Python implementations, not verification of Lean code
or of unbounded mathematical claims. API and tactic repairs may remain.
This review does not establish public priority or prize eligibility.

## Mathematical stages checked

1. Affine geometry and random traces. The universe is the actual field plane
   ZMod(q) squared for a prime q, with q² points and q(q+1) distinct lines.
   Lines have q points; distinct points have a unique line; every point has
   q+1 incident lines. All line traces are retained. The strict size estimate
   and q≥5 force at least three points per trace, so no distinct lines become
   duplicate blocks. Exact pair coverage is preserved before reindexing.
2. Balanced chunks. For |X|>2kq, gamma=floor(|X|/(2q)) is at least k≥2,
   and |X|≤3 gamma q. The source constructs partitions, counts incidences,
   and derives at least q² chunks. The k-uniform edges are actual k-subsets
   of chunks. The codegree bounds use at-most-one intersections, not an
   independence assumption or an oracle for balanced supersaturation.
3. Container algorithm. The finite state tracks antichain, rank, nonempty
   edge, low-link, and potential-budget invariants. Its generated upset
   strictly grows at a nonterminal step. Fingerprints record accepted seeds;
   replay from the final fingerprint reproduces every decision. A small
   family is counted by its actual fingerprints. The theorem's public
   premises are finite uniformity and the numerical p range, matching
   Campos–Samotij Theorem A, rather than assuming the desired containers.
4. Shrink and count. With p=1/(gamma log(q)³), the displayed higher codegree
   condition implies that a light cover leaves at most one quarter of the
   edges. The degree-one bound then deletes at least 3|X|/(40k) vertices.
   The full tree is counted to depth ceil(40k log q)+1, padding terminal
   nodes by one child. Its logarithmic size is O_k(q/log q+log²q)=o(q).
5. Container probability. For each fixed container C of size at most 2kq,
   incidence counting gives at least q²/2 short lines. Either a trace is
   empty, or a maximal packing yields at least q/(16k) disjoint nonempty
   traces of size at most 4k. The probability calculation is on the same
   full fair-bit function space and proves independence only for disjoint
   coordinate supports. It gives exp(-c_k q), c_k=2^(-4k)/(16k)>0.
6. Line-size probability. The independently derived finite MGF at
   t=log(11/10) is (21/22)^q. The elementary logarithm bounds give exponent
   at most -3q/550≤-q/200. The union over all q(q+1) lines tends to zero.
   The union bound over all containers also tends to zero. Neither
   conditioning nor independence between those two bad-event families is
   assumed; their sum is eventually less than one.
7. Original scope. k=K+2 stays fixed while q tends to infinity, but K is
   arbitrary. The chosen prime exceeds all thresholds and 3n₀+5. A single
   retained line ensures |R|≥n₀. Since |R|≤q², every block has size strictly
   greater than (2/5)sqrt(|R|). A bounded-intersection transversal is a k-arc
   and lies in an excluded container, yielding the contradiction. Finite
   point and block enumerations preserve exact uniqueness of block indices.
   The real-bound adapter uses ceil(K), including negative proposed bounds.

These are checks of the key definitions, construction/assembly bodies and
the written mathematical estimates. They are not a line-by-line independent
kernel certification of the copied helpers or Mathlib dependencies.

## Reproducible finite checks

Run `python3 audit/check_finite_mathematics.py` from the extracted package.
The script is self-contained and needs only Python's standard library.

The completed run made 616,660 assertions with fixed seed 539664. It tested
affine planes at q=2,3,5,7,11; all retention subsets for q≤3 and sampled larger
ones; exact pair coverage and distinct traces; 600 short-line samples; 240
valid chunk constructions and their sampled codegrees; 12,341 exact
binomial-ratio inequalities; and 101 exact MGF identities. The line-tail
comparison for sizes 0 through 100 additionally uses ordinary floating-point
exp and is therefore only a numerical sanity check.

Static scans found no missing local imports, local import cycles, or code
tokens for sorry, admit, custom axiom, native_decide, sorryAx, unsafe, or
implemented_by. All five copied helper hashes matched their provenance
record. Original mathematical modules and the pinned dependency manifest
are unchanged from the 05:19 package. Only the new RealScope module, import
root, verification target list, and documentation have changed.

## Primary references

- Jiaxi Nie, [Block Designs with Large Transversal–Block Intersections](https://arxiv.org/html/2609.07736v1), Problem 1.1 and Theorem 1.2.
- Campos–Samotij, [Towards an optimal hypergraph container lemma](https://arxiv.org/html/2408.06617v2), Theorem A and Section 3.

The project uses a fixed-K specialization with affine geometry and a coarse
disjoint-trace packing. It does not claim Nie's stronger logarithmic lower
bound or its size constant 0.6. The constant 0.4 is already sufficient to
negate each original uniform-bound assertion.
