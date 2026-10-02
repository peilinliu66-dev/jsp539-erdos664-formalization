# JSP539 prebuild readiness

Prepared without invoking Lean, Lake, dependency download, or changing any
candidate file. All 46 files match the user-selected 0730 archive; its SHA256
is `168c87fc14b7c0511e12cf79f35163190c0e342a875d006117e62478daadaaf9`.

`READY.json` records all source hashes, nested-comment-aware import topology,
31 local modules (including roots and `Verify`), and the eight actual axiom
targets already in the package. The only external import is `Mathlib`.
No executable `sorry`, `admit`, `native_decide`, or `axiom` tokens were found.
This is preparation evidence, not compilation evidence.

The supplied Lean 4.35.0-rc3 and nine dependency commits exactly match both
JSP865 and JSP896. Read-only `git rev-parse HEAD` and `git status --porcelain`
checks establish exact, clean dependency trees in both existing projects.

## Authorized start gate

Wait for Root's explicit instruction that JSP896 has been submitted and JSP539
actual compilation may begin. Do not start any compiler or dependency fetch
before that instruction.

## Build procedure after the gate

1. Recheck the chosen archive, all original candidate hashes, nine dependency
   heads, clean status, and actual Lean version.
2. Create only JSP539's `.lake` and an independent `.lake/build`. Link its
   `.lake/packages` to the proven exact dependency cache from JSP865. Do not
   share or copy previous project oleans for JSP539 source modules.
3. Adapt the previous durable runner for `lakefile.lean` (JSP539 uses Lean
   configuration, unlike the earlier TOML packages). Save initial hash map,
   module order, actual version output, and dependency receipt.
4. Compile all local modules in the saved topological order with natural exit
   status, full raw logs, and before/after source snapshots. Fix actual Lean
   diagnostics only, recording original/repaired bytes, diff, and reason. Save
   hash-verified source checkpoints after every repair group.
5. Run `lake build JSP539 LicensedContainers`; run `lake env lean Verify.lean`
   for the eight actual axiom reports and expanded statements. Preserve every
   real K, every minimum n0, exact pair multiplicity one, strict block-size
   bound, and unbounded transversal obstruction.
6. Coordinate Root's additional literal-statement wrapper and kernel replay.
   Record their natural status and actual source hashes before a final seal.

Keep the five individually Apache-2.0-licensed helper notices and namespace.
Do not add admissions, mathematical axioms, external assumption interfaces,
or restrict the original quantifiers. Do not change versions without an
explicit version-adjustment record. The package's finite Python checks and
prose do not substitute for actual compilation.
