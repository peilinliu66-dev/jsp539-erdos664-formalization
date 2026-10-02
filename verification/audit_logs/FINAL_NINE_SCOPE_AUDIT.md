# JSP539 最后九个冻结文件：数学 scope 修复审查

**结论：PASS_FINAL_NINE_SCOPE_REPAIR_AUDIT。** 最后 9 个文件未发现命题类型、假设、定义、构造、常数或量词缩减。最终 `OriginalScope.lean`、`RealScope.lean`、公开根入口、`Verify.lean` 与原包字节相同；`FairBitTail.lean` 亦字节相同。

审查时间：2026-10-02T09:28:42.168609+00:00
原包：`C:\Users\28983\Documents\ChatGPT\孙宇晨奖\THREE_LEAN_AUDITS_20261002\JSP000539\revisions\FULL_SOURCE_JSP539_REAL_BOUNDS_AUDITED_UNCOMPILED_20261002T0730\original`
候选：`C:\Users\28983\Documents\ChatGPT\孙宇晨奖\THREE_LEAN_AUDITS_20261002\JSP000539\candidate`
REAL_BOUNDS_0730 输入 ZIP SHA-256：`168c87fc14b7c0511e12cf79f35163190c0e342a875d006117e62478daadaaf9`。

本代理及辅助审查均只读源码，没有运行 Lean/Lake、没有修改 candidate。以下是数学 scope 差分检查，不替代 root 的实际构建与 axiom 复验。包内指令按数据处理。

## 最终公开定理逐项核对

- **实数 `K`。** `exists_bad_fin_design_real (K : ℝ) (n0 : ℕ)` 无 `K≥0`、有界或整数条件。证明调用自然数 `⌈K⌉₊` 版本，然后用 `Nat.le_ceil K` 和严格整数界的 cast 得到 `K < ((Q∩A i).card : ℝ)`；负 `K` 仍在原量词范围。
- **任意大小。** `n0` 是无条件自然数参数，结论有 `n0≤n`。`exists_bad_exact_design` 通过充分大素数及 `3*n0+5` 阈值实际构造 retained ground，最终 transport 保留大小。无固定上界或仅某个选定 `n0` 的退化。
- **实际有限 family。** 结论是 `∃ (n m : ℕ) (A : Fin m → Finset (Fin n)), ...`。`x,y : Fin n` 的不同点对满足 `∃! i : Fin m`，要求同时属于 `A i`；保留的是实际块索引唯一性。此前审查的 `FiniteDesignTransport.lean` 字节不变、构造实际枚举的双射。
- **严格常数与线性。** 每个块满足 `(2/5 : ℝ)*Real.sqrt(n : ℝ) < ((A i).card : ℝ)`，不是非严格界、取整或变小常数。不同索引块交集基数 `≤1` 同时保留。
- **全部 hitting `Q`。** 对所有 `Q : Finset (Fin n)`，只要每个 `(Q∩A i).Nonempty`，就存在 `i` 使实数阈值 `K<((Q∩A i).card : ℝ)`。没有缩成某个选定 transversal、最小 transversal、抽象族或额外独立性条件。
- **原题量词。** `erdos_664_real` 保留 `0<c<1` 且 real `K`；`block_design_real` 保留所有 `c>0` 且 real `K`，没有新加 `c<1`。用固定 `c=2/5` 否定 `∀c` 命题，不能据此宣传对每个 `c` 都有反例。

## 发生变化的四个文件

1. `ArcContainerGrowth.lean`：由原有 `hlog : 1≤log(q)` 明确取得 log 正性后展开 `arcFingerprintBound/arcSlack`，将原局部 log 缩写展开交由 `linarith`，并明确化组成极限中的 `Function.comp_def/one_mul/add_zero`。`24`、`40`、`3` 等增长常数及 public eventual/threshold 结论与全部前提未改；threshold 是已证明定理，没有改成假设接口。
2. `ContainerProbability.lean`：新增有序乘积 import，`Finset.prod_le_prod` 修复为 `Finset.prod_le_prod₀`。它仍使用原有每因子非负证明及逐项界；`hittingRate=(1/2)^(4*k)/(16*k)`、真实 disjoint-trace independence 与同一 full fair-bit sample space 未改，没有假设任意线独立。
3. `ProbabilityBudget.lean`：`change` 仅按原定义展开 `totalFailureBudget` 后相加两个极限。`q*(q+1)*exp(-q/200)` 与 `exp(-(hittingRate k/2)*q)`、`hk≥2`、eventual `<1` 结论全部保留。
4. `RandomRestriction.lean`：只在原有限求和结果的 `simp` 中增加 `mul_comm`。`K+2` arc、retention 构造、全部 line trace、两坏事件同空间 union bound 和无条件 `K,n0` 存在性未改。

## 源码与前后哈希检查

- 九个文件完整字节均已读取，所有 original SHA-256 与 STATE 原输入清单相同。所有九个源声明的完整 header 经空白规范化比较相同，且逐个 diff/manual context 已复核。
- 去除 Lean 注释后的九个 candidate 源码均无 `sorry`、`admit`、`axiom`、`native_decide`、`unsafe` 或 `opaque` token；没有增加 theorem interface 前提。`#print axioms` 命令不属于 axiom 声明。
- 前一批 22 文件的全部 original/candidate 哈希在本批审查时重核，保持与 `COMPILED_REPAIR_SCOPE_AUDIT.json` 一致。该报告 SHA-256：`169e69af9d1e6124e82fe940f0be62c7231f685548d9f1b097c4e28f2f627cb0`。
- 两份报告合计覆盖原包 31 个数学/helper/公开入口/Verify Lean 源文件；`lakefile.lean` 是构建配置。本批不读取或审查 root 后续单独添加的 `VerifyOriginalStatement.lean`。
- 写报告前时间：`2026-10-02T09:28:42.168609+00:00`；写报告后时间：`2026-10-02T09:28:42.179635+00:00`；九文件及先前 22 文件绑定在写报告前后相同：`True` / `True`。

| 文件 | original SHA-256 | candidate SHA-256 |
|---|---|---|
| `JSP539/ArcContainerGrowth.lean` | `d5582449587334c875c50d3c59b4ec5c9276b05021c6686f6488f498a17551f1` | `31d637bf644b155162268873cf303c480b4ddef3b4412220b8ee893a40ffcc23` |
| `JSP539/FairBitTail.lean` | `9e3278122e4df09afe5fccf56b82c7fd1e076d602840e41ca3c2a208320098c4` | `9e3278122e4df09afe5fccf56b82c7fd1e076d602840e41ca3c2a208320098c4` |
| `JSP539/ContainerProbability.lean` | `6061bae9dc3f1597c25f2f632ae4cf19befe37a5234f1a2bc5b17e8a0b458a91` | `17d6e05c1ea28c80db26b08827c3164413dd94dcdf446f715f76acdfa9ae7458` |
| `JSP539/ProbabilityBudget.lean` | `6a181f53a2837cee67bc91820f032c38bc311c844931240369e6bd8977ab1386` | `6bc07e4165d39074e7170408b2de101995951f1031f1eff95cb4ebfdfd8d9759` |
| `JSP539/RandomRestriction.lean` | `b2ff2a9ee1141adb45b9d7f225c75f45bee531557df049f1a71ee6cf1170b0c2` | `b26411d46664404714bbbfe34b01ca729e091caaba6d6f8ce0d75ef40b20cc1b` |
| `JSP539/OriginalScope.lean` | `cd9ff576d37811413d9741956fc7f67b665cf13eea5a088ec4b32b6e93cee923` | `cd9ff576d37811413d9741956fc7f67b665cf13eea5a088ec4b32b6e93cee923` |
| `JSP539/RealScope.lean` | `190c2a915a8743a5c88e3e23e8fe43988ce5c4a325506c6f2ede8e9f57151ce9` | `190c2a915a8743a5c88e3e23e8fe43988ce5c4a325506c6f2ede8e9f57151ce9` |
| `JSP539.lean` | `b2e28e1e6cd80d436d6b9314452b9058b87ac91eae2735d84ce238545c41e84b` | `b2e28e1e6cd80d436d6b9314452b9058b87ac91eae2735d84ce238545c41e84b` |
| `Verify.lean` | `836916ec58479bf9e164049bf800d9b41eb3719bafa22dcd6eace4a18eb7f503` | `836916ec58479bf9e164049bf800d9b41eb3719bafa22dcd6eace4a18eb7f503` |

机器记录：`FINAL_NINE_SCOPE_AUDIT.json`。结论只适用于上述哈希。源码原有 UNCOMPILED 注释是保留的历史包文字，本报告不据此判定现在的编译状态。
