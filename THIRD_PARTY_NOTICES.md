# Attribution and third-party notices

## Mathematical sources

- Paul Erdős, *On the combinatorial problems which I would most like to see
  solved*, Combinatorica (1981), 25–42. The exact pairwise-balanced question
  is in the [author's paper archive](https://www.renyi.hu/~p_erdos/1981-16.pdf).
- Noga Alon, [*A remark on a problem of Erdős*](https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf),
  for the earlier negative answer under the at-most-one intersection
  hypothesis.
- Jiaxi Nie, [*Block Designs with Large Transversal–Block Intersections*,
  arXiv:2609.07736v1](https://arxiv.org/html/2609.07736v1), for the mathematical
  exact-design resolution. This implementation specializes the random
  restriction to a fixed proposed bound, uses an affine plane and a finite
  disjoint-trace argument, and takes the strict size constant $2/5$.
- Marcelo Campos and Wojciech Samotij,
  [*Towards an optimal hypergraph container lemma*,
  arXiv:2408.06617](https://arxiv.org/abs/2408.06617), Theorem A and Section 3,
  for the finite algorithm, seed selection and charging method.
  Its machine, reconstruction, counting and shrinking conclusions have
  local proof bodies.

The mathematical results are credited to their authors. Paper full texts
and figures are not redistributed in the proof repository.
The new formalization and original-scope adapters are implemented by the
JSP539 formalization contributors, with AI assistance. The software headers
retain the source attribution.

## Five Apache-2.0 helper files

The helpers come from
[`plby/lean-proofs`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos565)
at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
Every upstream file below contains an explicit Apache License, Version 2.0
header and **Copyright 2026 The Lean-Proofs Authors**.
Those notices and the original `Erdos565` namespaces are retained.

| Local path | Pinned upstream file | Git blob |
| --- | --- | --- |
| `LicensedContainers/Hypergraph.lean` | [Hypergraph.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos565/Hypergraph.lean) | `87aa8f4ef12fcc6b9192470474352f7238eb7a2a` |
| `LicensedContainers/ContainerFuel.lean` | [ContainerFuel.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos565/ContainerFuel.lean) | `31af944e4a5d05c5e6cbf5ab66896f44b67ed5bc` |
| `LicensedContainers/ContainerInvariants.lean` | [ContainerInvariants.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos565/ContainerInvariants.lean) | `85d221b7590e996245e284c98221ef2927ec121d` |
| `LicensedContainers/ContainerWeight.lean` | [ContainerWeight.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos565/ContainerWeight.lean) | `c8493745d441d3904fab31095e888a46d10ca86f` |
| `LicensedContainers/ContainerSelector.lean` | [ContainerSelector.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos565/ContainerSelector.lean) | `fa911c3c7dd1c01000031a0984275f3b1e2cfa0a` |

The input package redirects the upstream `ErdosProblems.Erdos565` import
prefix to `LicensedContainers`.
`ContainerWeight.lean` replaces the unused upstream `FiniteAnalysis`
import with `Mathlib`; no source from that module is included.
Mathematical bodies were retained in this input adaptation.
Subsequent compatibility repairs, if present in the selected release,
are described in its source repair record.

`THIRD_PARTY_PROVENANCE.json` preserves upstream URLs, Git blobs,
upstream SHA256 values, input adaptation SHA256 values and transformations.
The release verification record binds final hashes to compiled sources.

The full Apache License, Version 2.0 is in `LICENSE`.
New `JSP539` sources also carry Apache-2.0 notices.
Mathlib and its pinned dependencies are obtained through Lake and retain
their own license and attribution files.
