# JSP539 full build and axiom audit

Status: PASSED. This report is derived from actual natural compiler exits and unchanged source snapshots, for the user-selected REAL_BOUNDS_0730 source package.

The full `lake build JSP539 LicensedContainers` completed 3172 jobs. All 30 local library modules appear as **Built** in that full build; this is not inferred from dependency replay. All 31 local modules, including the separate `Verify.lean` entrypoint, also have accepted direct compile receipts.

The independent `lake env lean Verify.lean` check exited naturally with code 0 and printed 8 axiom dependency reports. Every reported set is exactly `propext`, `Classical.choice`, and `Quot.sound` after universe annotations are normalized.

| Check | Accepted log |
|---|---|
| Whole library build | `verification/build/full_build_01.log` |
| Final theorem printing and axioms | `verification/build/verify_final_01.log` |

The 34 final proof/build inputs comprise 32 Lean files (including `lakefile.lean`) and the toolchain and manifest files. Their SHA256 snapshot is `24571c3194e580c0e88d8fb936310a47ed6eae30414cf2e8d34201ce46a61661`. All 46 preserved original package members match the received package's saved hashes. OriginalScope, RealScope, JSP539 root, Verify, and all three version/configuration files remain byte-identical to that selected package.

Repairs changed 20 Lean files, adding 114 lines and removing 65 lines; the complete original-to-final patch is `FINAL_SOURCE_REPAIRS.patch`. Required-module imports, API names, casts, product normalization, and explicit elaboration arguments account for the repairs. Source comments inherited from the original uncompiled package describe its initial execution status; the accepted logs record the later compilation.

Lean remains 4.35.0-rc3, release commit 470d5ce1400764999581fd26d5d72b00d990b0f4; Mathlib remains 2a885768dae569d938bb9ff3474da6a8753bb90a. Fresh Git checks confirm all nine dependency HEAD revisions match the manifest and every dependency worktree is clean. The project uses its own build directory and reuses dependency binaries from the same exact pins.

Initial simultaneous full-Mathlib imports failed while reading PellMatiyasevic private data. The exact-pin official cache command and the isolated Pell import both exited 0. Required-module imports resolved the full-import resource/read problem; these diagnostics do not establish a missing mathematical proof or unavailable dependency source.

No `sorry`, `admit`, `native_decide`, or new `axiom` token occurs in the final Lean source outside comments and string literals. Actual final axiom reports provide the proof-dependency check. The arbitrary real K, arbitrary minimum ground size, and exact distinct-pair uniqueness endpoints are retained in the unchanged final scope modules.

Direct compile output olean hashes are historical artifacts of those accepted commands; this report binds current source inputs rather than demanding binary identity after the later full build. An additional independent kernel replay, if performed, is recorded separately by the main audit.

| Final theorem | Axiom set |
|---|---|
| `JSP539.exists_bad_fin_design` | `propext, Classical.choice, Quot.sound` |
| `JSP539.OriginalScope.erdos_664` | `propext, Classical.choice, Quot.sound` |
| `JSP539.OriginalScope.two_fifths` | `propext, Classical.choice, Quot.sound` |
| `JSP539.OriginalScope.two_fifths_exact_pairs` | `propext, Classical.choice, Quot.sound` |
| `JSP539.OriginalScope.block_design` | `propext, Classical.choice, Quot.sound` |
| `JSP539.exists_bad_fin_design_real` | `propext, Classical.choice, Quot.sound` |
| `JSP539.OriginalScope.erdos_664_real` | `propext, Classical.choice, Quot.sound` |
| `JSP539.OriginalScope.block_design_real` | `propext, Classical.choice, Quot.sound` |
