# JSP539 / Erdős 664: exact block designs

**UNCOMPILED source. No Lean or Lake build has been run on this project.**

This project gives proof bodies for the two original formulations of Erdős
664: the family with pairwise intersections at most one, and the stronger
requirement that every distinct point pair lies in exactly one block. The
answer is negative. The construction works for every proposed bound K,
with arbitrarily large finite ground sets; it is not one finite example.

The fixed size constant is 2/5. Every block has more than (2/5)√n elements,
yet every transversal meets some block in more than K elements. The
exact-pair construction implies the original partial-design result and its
explicit two-fifths variant. Existing public Lean already covers the latter
partial-design results; the intended additional contribution is exact
pair coverage. The pinned official catalog displays “Eligible to claim: No”.
The additional original scope has not been accepted by the organizer as a
new eligible claim. No worldwide firstness or prize acceptance is asserted.

## Revision at 07:30 UTC

The original mathematical modules are byte-for-byte unchanged. The added
`RealScope.lean` makes the ceiling conversion for arbitrary real-valued
intersection bounds explicit. `Verify.lean` includes the three new endpoints.
An independent mathematical/source review and reproducible finite sanity
checks are included in `audit/`. These checks do not establish compilation or
kernel verification; the whole source remains **UNCOMPILED**.

## Mathematical route

The route specializes Jiaxi Nie's September 2026 random-restriction proof
to a fixed K. Set k=K+2 and choose a sufficiently large prime q. Construct
the affine plane on ZMod q × ZMod q. A finite hypergraph-container algorithm
covers all k-arcs by a family of containers, each of size at most 2kq. The
logarithm of the number of containers is o(q), with K fixed.

Retain each point with probability one half. A short-trace packing proves
that a particular container's retained points meet every line with
probability at most exp(-cₖq), where cₖ=2^(-4k)/(16k). The union bound includes
the entire container family. An independently proved finite MGF calculation
bounds the probability that any one line retains at most 2q/5 points by
exp(-q/200). The sum over all q(q+1) lines also tends to zero. Consequently
one retained point set avoids both bad-event families simultaneously.

All ambient lines remain as blocks through their traces. Every pair of
retained points still has its unique line; the trace size bound prevents
duplicate blocks. A transversal with all block intersections at most K
would be a k-arc inside one of the excluded containers, a contradiction.

The full probability/counting calculation is in `PROBABILITY_BUDGET.txt`.
This project does not attempt Nie's stronger logarithmic intersection lower
bound; arbitrary K already settles every original question here.

## Source organization

- `AffinePlane`, `ChunkPartition`, `GroundHypergraph`, `LineChunks`,
  `ShortTraces`: actual finite geometry, chunks, degrees, and disjoint traces
- `ContainerPotential`, `ContainerAlgorithm`, `ContainerCore`,
  `ContainerCounting`, `ContainerShrink`: finite algorithm and its proof,
  fingerprint reconstruction, family count, and shrinking
- `ArcContainerStep`, `ArcContainerIteration`, `ArcContainerGrowth`: actual
  arc families, complete finite tree, and subexponential family count
- `FiniteProbability`, `DisjointPacking`, `UniformBits`, `FairBitTail`,
  `ContainerProbability`, `ProbabilityBudget`: one common fair-bit space,
  finite sums, independence on disjoint coordinates, both full union bounds
- `RandomRestriction`: unconditional construction, arbitrary K and minimum n
- `FiniteDesignTransport`, `OriginalScope`: genuine finite reindexing and
  original statements on families `Fin m → Finset (Fin n)`

See `SCOPE_MAP.md` for exact final theorem names. Source bodies contain no
declared extra axioms, `sorry`, `admit`, or `native_decide`. This statement is
a static source observation, not a kernel-checked axioms report.

## Reproduction on the user's Codex

The exact pins are:

- Lean `leanprover/lean4:v4.35.0-rc3`
- Mathlib `2a885768dae569d938bb9ff3474da6a8753bb90a`
- Transitive dependency commits: `lake-manifest.json`

From the extracted project root, use the included toolchain and manifest:

```sh
lake exe cache get
lake build
lake env lean Verify.lean
```

Do not update to moving branches while checking this handoff. The manifest
was copied from the same pinned Mathlib dependency closure and renamed for
this package. It has not been exercised by Lake in this project. Record any
API/elaboration repairs and the eventual build and expanded-axiom outputs.
No successful build, proof acceptance, or verified absence of extra axioms
is claimed by this handoff.

## Sources, permissions, and priority

`SOURCES.md` lists original mathematical sources and the selection boundary.
`THIRD_PARTY_PROVENANCE.json` records URLs, exact commits, Git blob IDs,
upstream SHA256, local SHA256, and transformations for every copied helper.
Only five individually Apache-2.0-licensed container helper files are copied.
The independent construction and new proof modules are Apache-2.0 as well.
No unlicensed whole-project proof file or full paper is included.

The selected problem was checked against all states of official PRs, their
comments and referenced cross-repository sources, before source construction.
The dated selection evidence is a separate Library artifact. A closed PR,
license question, fork-only repository, or different toolchain does not
invalidate an earlier mathematical formalization. Public priority can change
and was only assessed within a bounded search. No public repository,
submission, external contact, or authorship claim has been made here.
