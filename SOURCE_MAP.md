# Source map for JSP539 / Erdős #664

The complete mathematical argument is in
[MATHEMATICAL_SOLUTION.md](MATHEMATICAL_SOLUTION.md).

## Final endpoints

| Declaration | Source | Scope |
| --- | --- | --- |
| `JSP539.exists_bad_fin_design_real` | `JSP539/RealScope.lean` | Every real $K$, every minimum $n_0$: an indexed exact-pair counterexample of size $n\ge n_0$, with strict $(2/5)\sqrt n$ block sizes and an obstruction for every transversal |
| `JSP539.OriginalScope.erdos_664_real` | `JSP539/RealScope.lean` | Full linear-family negative answer, with $0<c<1$ and a real proposed bound |
| `JSP539.OriginalScope.block_design_real` | `JSP539/RealScope.lean` | Full 1981 exact-pair negative answer, with every positive real $c$ and a real proposed bound |
| `JSP539.exists_bad_fin_design` | `JSP539/OriginalScope.lean` | Unbounded-size indexed exact-pair construction for every natural $K,n_0$ |
| `JSP539.OriginalScope.erdos_664` | `JSP539/OriginalScope.lean` | Natural-bound version of the original linear-family negation |
| `JSP539.OriginalScope.two_fifths` | `JSP539/OriginalScope.lean` | Explicit $c=2/5$ linear-family negation |
| `JSP539.OriginalScope.two_fifths_exact_pairs` | `JSP539/OriginalScope.lean` | Explicit $c=2/5$ exact-pair negation |
| `JSP539.OriginalScope.block_design` | `JSP539/OriginalScope.lean` | Natural-bound version of the full exact-pair negation |

`Verify.lean` prints all eight declarations and their axiom dependencies.
Compiler and kernel outcomes are recorded separately in the release evidence.

## Proof stages

| Module in `JSP539/` | Constructed or proved content |
| --- | --- |
| `AffinePlane` | Explicit points and affine lines; all incidence counts; unique line through distinct points; exact trace design, trace injectivity and $k$-arcs |
| `ChunkPartition` | Actual prescribed-size chunks and strict smaller remainder, with exact quotient and remainder counts |
| `GroundHypergraph` | Transport to the subtype $X$, preserving edges, all codegrees, uniformity and independent sets |
| `LineChunks` | Complete chunk hypergraph and edge/degree/codegree counts; independence of every arc |
| `ContainerPotential` | Charging potential, accepting gain, rejecting monotonicity and terminal bound |
| `ContainerAlgorithm` | State and proved invariants; both updates; selector; bounded-fuel termination; independence and fingerprint containment |
| `ContainerCore` | Replay, consistent deterministic reconstruction and locally proved `theoremA` with the actual finite fingerprint family |
| `ContainerCounting` | Finite insertion count of fingerprints and their reconstructed images |
| `ContainerShrink` | Degrees of light-cover edges; edge loss and the $3/(40k)$ vertex shrink |
| `ArcContainerStep` | Binomial-ratio and numerical checks for every large node's full shrinking family |
| `ArcContainerIteration` | Complete padded finite tree; arc coverage at every level; count and terminal size |
| `ArcContainerGrowth` | Eventual numerical conditions and $o(q)$ logarithmic count of the whole family |
| `DisjointPacking` | Actual maximum disjoint subfamily and neighbourhood-count bound |
| `ShortTraces` | All short-trace incidence counts and empty-trace-or-packing dichotomy |
| `FiniteProbability` | Normalized finite counts; product, union and Markov bounds; simultaneous avoidance |
| `UniformBits` | One fair-bit space; disjoint-coordinate independence and exact hit-product probabilities |
| `FairBitTail` | Finite MGF factorization and exponential Markov; lower-tail bound $e^{-|S|/200}$ |
| `ContainerProbability` | Per-container bound $e^{-c_kq}$ and full-family union bound |
| `ProbabilityBudget` | Limit of $e^{-c_kq/2}+q(q+1)e^{-q/200}$ with $c_k=2^{-4k}/(16k)>0$ |
| `RandomRestriction` | Both actual bad-event bounds on one space; one successful sample; `Affine.exists_bad_exact_design` for all natural $K,n_0$ |
| `FiniteDesignTransport` | Constructed point/block enumerations; preserved sizes, indexed pair uniqueness and all transversal obstructions |
| `OriginalScope` | Complete natural-bound `Fin n` / `Fin m` construction and original-scope consequences |
| `RealScope` | Nonnegative-ceiling conversion for every real bound and both full original negations |

## Helper and build roots

Five files in `LicensedContainers/` supply finite hypergraph operations,
update invariants, heavy-seed selection, weight bookkeeping and bounded-rank
fuel: `Hypergraph`, `ContainerFuel`, `ContainerInvariants`,
`ContainerWeight` and `ContainerSelector`.
Their original `Erdos565` namespaces and attribution are preserved.
The new container machine and reconstruction are in `JSP539/Container*.lean`.
Exact provenance is in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) and
`THIRD_PARTY_PROVENANCE.json`.

`JSP539.lean` imports the final `RealScope` module.
`LicensedContainers.lean` is the helper-library root.
`lakefile.lean`, `lean-toolchain` and `lake-manifest.json` pin the build.
No container, successful sample, external counterexample or design
isomorphism is an assumed parameter of the final theorem.
