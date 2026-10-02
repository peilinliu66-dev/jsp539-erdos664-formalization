# JSP539 编译修复数学 scope 审查（冻结批次）

审查时间：2026-10-02T09:11:25.939179+00:00

**结论：PASS_BOUNDED_SCOPE_REPAIR_AUDIT。** 本批 22 个冻结源码未发现数学命题、既有假设、定义/构造或定量结论缩减。此结论只绑定下表 SHA-256；不是整个项目最终 scope gate，也不是本代理独立编译认证。

本代理及辅助审查代理均未运行 Lean/Lake、未修改 candidate 或任何源码。包内文档中的指令一律作为数据。只读取指定源码和用于定位/核对输入的 STATE.json；没有重审论文，也没有采用编译日志来替代数学检查。

## 范围与判据

- original：`C:\Users\28983\Documents\ChatGPT\孙宇晨奖\THREE_LEAN_AUDITS_20261002\JSP000539\revisions\FULL_SOURCE_JSP539_REAL_BOUNDS_AUDITED_UNCOMPILED_20261002T0730\original`
- candidate：`C:\Users\28983\Documents\ChatGPT\孙宇晨奖\THREE_LEAN_AUDITS_20261002\JSP000539\candidate`
- 输入修订：REAL_BOUNDS_0730，ZIP SHA-256 `168c87fc14b7c0511e12cf79f35163190c0e342a875d006117e62478daadaaf9`。
- 对 22 个文件读取完整字节，逐个审 original→candidate diff，并读取受影响上下文；辅助代理独立核对 11 个 helper 文件。全部 original 哈希与 STATE 中记录一致，candidate 在写报告前重新读取并与审查快照核对。
- 未新增顶层声明、外加数学假设、占位证明或假设接口；22 个 reviewed candidate 均无 `sorry`、`axiom`、`native_decide` token。

## 关键修复的数学含义

1. **`Pairwise` API。** `ChunkPartition.pairwise_disjoint` 与其私有计数引理将不存在的 `Finset.Pairwise` 拼写改为 `(chunks : Set (Finset V)).Pairwise Disjoint`。展开后是对 `C,D∈chunks` 且 `C≠D` 要求 `Disjoint C D`；Finset→Set coercion 的成员关系相同。没有要求块与自身不交，没有丢掉不同块条件，没有更换 chunks 的 Finset 数据或余项。原写法不能在固定 API 中 elaboration，因此这里确认的是其清楚表达的原数学语义，而非两个已编译原项的逐项相等。
2. **自然数消去。** `LineChunks` 与 `ShortTraces` 改用 `Nat.le_of_mul_le_mul_left`。消去的正因子分别由原有 `gamma≥2`、`k≥2` 或 `q.Prime` 推出；没有新加正性前提，没有转换成有理数/实数近似，也没有改变整数基数界。
3. **实数消去与 cast。** `ArcContainerStep`、`ContainerShrink` 使用正确的正乘数消去 API。正性均在原证明内已取得（`t+1`、`choose`、`p`、`H.card`）；`dsimp [c,g]` 仅展开原有局部缩写后进行 Nat→Real cast。原命题、端点条件、四分之一边数界、`1-3/(40*r)` 收缩率均保留。
4. **有限概率。** `FiniteProbability` 的 product/not 证明改为 filter 基数证明；`fraction` 与 `average` 定义未改。乘积公式仍无 Nonempty 额外条件，空有限类型范围保留；补事件公式仍只用原有 Nonempty 前提。
5. **显式事件类型。** `UniformBits` 明确写出 `Sample V ≃ ((S→Bool) × ({v // v∉S}→Bool))` 以及该乘积上的事件类型，这是原 function-space equivalence 的目标。`Sample V = V→Bool`、公平位、support dependence、disjoint-support independence 和 hits/avoids 均未改；`hbit` 是局部证明，不是外部概率假设。
6. **精确 incidence 与实际索引。** `AffinePlane.ExactPairwiseDesign` 的 `∃! B` 字段及 exact design 构造未改；trace injectivity 只是 equality elaboration/rw 修复。`FiniteDesignTransport.lean` 字节完全相同，`Fin ground.card`、`Fin blocks.card` 的实际双射及 `indexed_pair_exactly_once : ∃! i` 保留，不能被解释成仅覆盖、at-most-once 或抽象索引假设。
7. **import 与其余证明调整。** 六个 broad `import Mathlib` 改为所需 modules；其余新增 import、`Prod.ext` 分目标、`pow_two`、局部变量改名与 tactic goal sequencing 不改数学数据。`ContainerPotential` 只展开 `linkWeight` 后由 `linarith` 合并原不等式，原增益 `1/(8*r)` 保留。

## 尚未纳入的最终 scope

遵照冻结边界，以下 9 个文件没有读取：

- `JSP539/ArcContainerGrowth.lean`
- `JSP539/FairBitTail.lean`
- `JSP539/ContainerProbability.lean`
- `JSP539/ProbabilityBudget.lean`
- `JSP539/RandomRestriction.lean`
- `JSP539/OriginalScope.lean`
- `JSP539/RealScope.lean`
- `JSP539.lean`
- `Verify.lean`

因此本批不单独断言最终“任意 `K : ℝ`、任意 `n0`、严格 `(2/5)*sqrt(n)`、每个 hitting `Q` 的真实实数阈值阻断”已经通过最终修复审查。这些是后续 freeze 后必须原样保留的条件；本批没有改动或削弱通向它们的 reviewed 辅助定理。

## 逐文件记录

- `JSP539/AffinePlane.lean`：Imports; split Prod.ext proof; explicit equality and rw orientation for trace injectivity; Nat.mul_comm simplification. ExactPairwiseDesign fields and exact construction unchanged.
- `JSP539/ChunkPartition.lean`：Finite-set Pairwise spelling repaired to Pairwise on its coerced Set. Same distinct-block disjointness, chunk/remainder fields, and constructed partition.
- `JSP539/GroundHypergraph.lean`：Imports only; ground-set transport construction unchanged.
- `JSP539/LineChunks.lean`：Explicit equality, library lemma spelling and natural-number positive-factor cancellation. All bounds and balanced hypergraph construction unchanged.
- `JSP539/ContainerPotential.lean`：Unfold linkWeight in existing local inequality and use linarith. Existing hypotheses and gain 1/(8*r) unchanged.
- `JSP539/ContainerAlgorithm.lean`：Added FieldSimp import only.
- `JSP539/ContainerCore.lean`：Byte-identical.
- `JSP539/ContainerCounting.lean`：Added Real.Archimedean import only.
- `JSP539/ContainerShrink.lean`：Real positive-factor cancellation uses existing hp/he. Edge loss 1/4 and vertex shrink 1-3/(40*r) unchanged.
- `JSP539/ArcContainerStep.lean`：Real positive-factor cancellation API and explicit unfolding of local c/g before casts; statements and numerical assumptions unchanged.
- `JSP539/ArcContainerIteration.lean`：Proof simplification uses pow_two and solves all congr/gcongr goals; depth, branch bounds and contraction unchanged.
- `JSP539/FiniteProbability.lean`：Imports and proof rewrites using finite filter cardinality; fraction/average definitions and all assumptions unchanged. Product formula still covers empty finite types.
- `JSP539/DisjointPacking.lean`：Imports and local binder names only; finite maximal packing construction unchanged.
- `JSP539/UniformBits.lean`：Explicit target/sample-space event types; local Bool false event cardinality proof. Sample V=V->Bool, support independence, avoids/hits events unchanged.
- `JSP539/FiniteDesignTransport.lean`：Byte-identical. Actual Fin ground/card and block/card reindexing, indexed pair exists-unique, and universal transversal obstruction unchanged.
- `JSP539/ShortTraces.lean`：Natural-number positive-factor cancellation uses existing positive 2*k and q; packing bounds unchanged.
- `LicensedContainers/ContainerFuel.lean`：Byte-identical.
- `LicensedContainers/ContainerInvariants.lean`：Byte-identical.
- `LicensedContainers/ContainerSelector.lean`：Added finite Nat interval import only.
- `LicensedContainers/ContainerWeight.lean`：Replaced broad Mathlib import with six required modules only.
- `LicensedContainers/Hypergraph.lean`：Byte-identical.
- `LicensedContainers.lean`：Byte-identical.

## SHA-256 绑定

| 文件 | original | candidate |
|---|---|---|
| `JSP539/AffinePlane.lean` | `b767d1de66f92f1c714aeb396e4e742696c7a9ac5bf1239edca9e06a1a6c7e38` | `2dd66fd8230af982d95a3516102af044d248e747ec940e8958161fcd6b67fdc0` |
| `JSP539/ChunkPartition.lean` | `f7984b1d6f04191eb6d44a9016f90f1f012c10e26d179548d01df807938c0cef` | `d77ded01e7fabeb277dbacaf69b69dde76b30b1bd564858576789ae271c2b605` |
| `JSP539/GroundHypergraph.lean` | `553a853185ffef65239024ccba2d89b3c812ab67520cc27eac2152d45be40a1a` | `c63aa2be77559855df77b6c0963c369d8a6e346adcd76184c50fb93ec6a5d4df` |
| `JSP539/LineChunks.lean` | `7b578d29e5e11ec08386ce20b239271576a20a2735daaea6fddd65582d769960` | `19826d814a9f9ef06ebcfa7d48d2fce8729ac04d0f3d4cefeba062e0187cea3f` |
| `JSP539/ContainerPotential.lean` | `35db27cf0ffdd7e3576db1958bc32fb6140f86f6298d90004cb6052a867b4957` | `04d384299d5ea8c366ea68c044039b6ef185d36cf37c853849a46deeb456041c` |
| `JSP539/ContainerAlgorithm.lean` | `aa4789f0e8efbb724f918dd243b38937d4e3031190e78ba7812d69e19cfb180f` | `2f9ee3f58e0c4677e3d51cdcd2496e64a3810c50b713f2c2830fb2ba0740dc3b` |
| `JSP539/ContainerCore.lean` | `21872ac245f9cac6b59910f688c877a13cc2e6fa3e1d67ca457751b066d29d82` | `21872ac245f9cac6b59910f688c877a13cc2e6fa3e1d67ca457751b066d29d82` |
| `JSP539/ContainerCounting.lean` | `9d5f2f8bf6ad5152b85fbf7603177418b8a3af26b926b5974161e4d6cdfe01a6` | `ed574ca842cb139298955c2b174c0e44dd44393403ffb5829d50a0fe4680b093` |
| `JSP539/ContainerShrink.lean` | `773cffd0b5884e79b900230575bc30a8ffe4e97728ab36df37c9350835e21ed7` | `e06dd4153c04d43a2fadc8aa24a0dc4ce3606910647f74e3be31a0a1ce64756f` |
| `JSP539/ArcContainerStep.lean` | `951b175593c4ac83ac46ce8f11df8e97f2b09cb610f0d8595a306d8eb354bf22` | `fda4b73f890dded9314e00e8e67773f560756c19d2617c9c47a747d28d96862e` |
| `JSP539/ArcContainerIteration.lean` | `51ef44b381027a02e2561f292690ccbc3628dad8467efb8657724d43089b170a` | `223e950020e181a2633d1ac2b77a7c115826e5f19bd8f931723bea722c389c41` |
| `JSP539/FiniteProbability.lean` | `16207cc761497895b500a6f48fa4257e6ad514f221007c6c85a273de2a68a9f7` | `3fed40e1cbae40de50e6e095e3b62df90f5e49254db40fdf92052e6e6f26240c` |
| `JSP539/DisjointPacking.lean` | `23a582dea5ce601312c2a343042b69cb889fe0c7697f0c0ce50f6a61e9ecfaef` | `26440ab4e46f87e54498ce742f80bd410e41afbc2e0772d9dc6b17927ba6d3d1` |
| `JSP539/UniformBits.lean` | `bc12630ad953b00251befcf84d3df043d29770f2c8e6f2326daa150f8ba2922e` | `c9784bd277437cce86e745d31344c9de49f1a22f8dca17cd71a1d1b4b550e4fd` |
| `JSP539/FiniteDesignTransport.lean` | `c8708b5efa3c3a4f3768ddc52584e2437d445dbeb3935284810ef2e44a063b11` | `c8708b5efa3c3a4f3768ddc52584e2437d445dbeb3935284810ef2e44a063b11` |
| `JSP539/ShortTraces.lean` | `867cc04761ece172de91ef721a250326c0e1858dc02799cd8c5b9565d644df5f` | `a23ca9c50c62241cbc0caeacea44ce8dd0f75b49cbf04556a1bb42b78312de3c` |
| `LicensedContainers/ContainerFuel.lean` | `c390bbd8cfbec2b9ed8dec2fb5cd896b1adc95da9bcdd741abbeffd5f7afb05c` | `c390bbd8cfbec2b9ed8dec2fb5cd896b1adc95da9bcdd741abbeffd5f7afb05c` |
| `LicensedContainers/ContainerInvariants.lean` | `ac99333ba0a496c6712ef4d5711c885bf7bc8856001125c040bc4dca14b86ac4` | `ac99333ba0a496c6712ef4d5711c885bf7bc8856001125c040bc4dca14b86ac4` |
| `LicensedContainers/ContainerSelector.lean` | `e115359961aa28988b332fd63e88c93d54992814368475865a65ec459929eafc` | `c7b7bfcb6fa923f47b00303534375c51b2487c841b2968baa52e53e06037ee98` |
| `LicensedContainers/ContainerWeight.lean` | `e281197a67f0dbae3cd484c2f03a474c1e10412242a0d3ddc150b66917454a32` | `d77b5840107c112c0246699e7253893c029fff99f041e6ff63fc9dfc9167bdee` |
| `LicensedContainers/Hypergraph.lean` | `aa2636ec7aa7b6e31264bb7fedc7a9823952223088693eae983031d07e7b5afb` | `aa2636ec7aa7b6e31264bb7fedc7a9823952223088693eae983031d07e7b5afb` |
| `LicensedContainers.lean` | `442c8da78a081a2fb718a8a3cea578a6c6363412d070089484438b4c935ff781` | `442c8da78a081a2fb718a8a3cea578a6c6363412d070089484438b4c935ff781` |

机器可读记录：`COMPILED_REPAIR_SCOPE_AUDIT.json`。任何 listed candidate 哈希发生变化后，相应文件需重新审查，本结论不可自动外推到变化后的源码。
