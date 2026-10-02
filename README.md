# JSP539 / Erdős #664: exact-pair design formalization

The source constructs a counterexample for **every real proposed
transversal–block intersection bound**, with arbitrarily large finite
ground sets. Every distinct point pair is contained in exactly one indexed
block, every block has size strictly larger than $(2/5)\sqrt n$, and every
transversal has an intersection larger than the proposed bound.

The endpoint is `JSP539.exists_bad_fin_design_real`.
`JSP539.OriginalScope.block_design_real` and
`JSP539.OriginalScope.erdos_664_real` give the original exact-design and
linear-family negative answers. Natural-bound and explicit two-fifths
endpoints are also included.

The route follows Jiaxi Nie's
[2026 exact-design result](https://arxiv.org/html/2609.07736v1), using an
affine plane, a locally proved finite container algorithm, disjoint-trace
packing and a directly proved exponential tail.
All container and line-size events use the same fair-bit sample space.
Every affine line is retained as a trace block. Injectivity and indexed
exact-pair coverage are proved before finite reindexing.

- [Complete mathematical proof](MATHEMATICAL_SOLUTION.md)
- [Definitions, proof stages and final theorem map](SOURCE_MAP.md)
- [Source attribution](THIRD_PARTY_NOTICES.md)
- `Verify.lean`: expanded endpoint statements and axiom dependencies
- `verification/`: actual build and kernel records included with the release

## Reproduce with the pinned environment

The input pins are Lean `leanprover/lean4:v4.35.0-rc3` and Mathlib commit
`2a885768dae569d938bb9ff3474da6a8753bb90a`.
Transitive dependency commits are in `lake-manifest.json`.

With Elan installed, run from the repository root:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc3
lake exe cache get
lake build LicensedContainers JSP539
lake env lean Verify.lean
lake env leanchecker --verbose JSP539.RealScope
```

The cache command obtains Mathlib artifacts for the pinned closure.
The build compiles the source libraries. `Verify.lean` checks the eight
final declarations. The kernel-replay command checks the final
`RealScope` module.
Release verification records identify the commands actually run, natural
exit codes, source hashes, toolchain versions and axiom output.

## Attribution

Nie is credited for the exact-design mathematical resolution.
Campos and Samotij are credited for the container algorithm and charging
argument adapted here. Alon is credited for the earlier linear-family result.
This project's contribution is the Lean implementation and its complete
original-scope adapters, with AI assistance.

Five finite container helper files are adapted from individually
Apache-2.0-licensed `plby/lean-proofs` files, preserving their attribution.
The new sources carry Apache-2.0 notices. The full license is in `LICENSE`;
exact helper provenance and modifications are in
`THIRD_PARTY_PROVENANCE.json` and `THIRD_PARTY_NOTICES.md`.

## Executed verification

The complete pinned two-library build, all eleven actual axiom reports, and all three declaring-module kernel replays passed. The public-copy reproduction completed 25 processes with natural exit 0 and unchanged proof inputs. See [VERIFICATION.md](VERIFICATION.md) and [complete run evidence](verification/publication_reproduction/).

Submitted Lean implementation, integration, compiler repairs and verification: **peilinliu66-dev**, with ChatGPT/Codex assistance. Mathematical sources and reused finite-container helpers are credited separately in the source map and notices.
