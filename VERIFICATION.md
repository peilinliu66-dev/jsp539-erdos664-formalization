# Executed pinned verification

On 2 October 2026 the complete `JSP539` and `LicensedContainers` libraries built successfully (3172 Lake jobs). The public project contains 30 local library/root modules. The reproduction ran 25 processes, all with natural exit 0, and all active source hashes remained unchanged. All nine dependency checkouts matched their locked revisions and had clean source workspaces; versions were retained.

The eight supplied endpoint reports and three literal-statement reports use only dependencies from `propext`, `Classical.choice`, and `Quot.sound`. Actual complete outputs and process metadata are in [publication_reproduction](verification/publication_reproduction/); the exact dependencies are also recorded in [publication-summary.json](verification/publication-summary.json).

Official `leanchecker --verbose` replayed the actual declaring modules `JSP539.RandomRestriction`, `JSP539.OriginalScope` and `JSP539.RealScope`. Each exited naturally with code 0 and emitted its actual replay marker. Replay uses the pinned imported environment.

The literal [original-statement audit](VerifyOriginalStatement.lean) covers every real `K`, every minimum size `n0`, strict block sizes above `2/5 * sqrt(n)`, exactly one indexed block per distinct pair, pairwise block intersections at most one, and every hitting set having a block intersection strictly larger than `K`. It also checks the two original proposed uniform real-bound formulations. No supplied container, probability or counterexample hypothesis appears in these conclusions.

## Reproduce

With Python 3.10+ and Elan:

```text
elan toolchain install leanprover/lean4:v4.35.0-rc3
python verify_project.py --cache
```

The optional cache command retrieves the official complete Mathlib cache at the fixed revision. A new checkout builds its local sources. The recorded publication run reused the exact pinned dependency and candidate caches; `lake --rehash` checked source inputs and rebuilt changed status-comment copies.

```text
elan run leanprover/lean4:v4.35.0-rc3 lake --rehash build JSP539 LicensedContainers
elan run leanprover/lean4:v4.35.0-rc3 lake env lean Verify.lean
elan run leanprover/lean4:v4.35.0-rc3 lake env lean VerifyOriginalStatement.lean
elan run leanprover/lean4:v4.35.0-rc3 lake env leanchecker --verbose JSP539.RandomRestriction
elan run leanprover/lean4:v4.35.0-rc3 lake env leanchecker --verbose JSP539.OriginalScope
elan run leanprover/lean4:v4.35.0-rc3 lake env leanchecker --verbose JSP539.RealScope
```

## Source and contribution evidence

[accepted-proof-inputs.json](verification/accepted-proof-inputs.json) binds all 35 active proof/build/lock inputs to the checked bytes. Actual compiler repairs changed 20 original Lean files (+114/-65 lines); full raw logs and repair snapshots are preserved under [audit_logs](verification/audit_logs/). The public copy updates 17 historical status comments with executable proof code unchanged, and this exact copy was reverified.

The complete [mathematical argument](MATHEMATICAL_SOLUTION.md) and [source map](SOURCE_MAP.md) describe the proof and its correspondence. The five reused finite-container helpers retain their explicit Apache 2.0 notices and are credited in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) and [THIRD_PARTY_PROVENANCE.json](THIRD_PARTY_PROVENANCE.json). Historical supplied source-status documents are preserved under `verification/supplied_handoff_documents/`.
