# JSP539：英文完整数学说明独立复核

状态：DOCUMENTATION_MATHEMATICAL_REVIEW_PASSED。日期：2026-10-02。

对象：publication_drafts/docs539/MATHEMATICAL_SOLUTION.md。
最终文稿 SHA256：5d49973fd9483aafbcfdf72b0e63c6fcdda5d8537140333e2c18dcc266b0ff1d。

已完整读取初稿及复核全部后续修改。当前说明与 REAL_BOUNDS_0730 源码数学构造一致，未发现数学错误、缺失步骤或原题量词范围缺失。本次只读审稿；没有修改文稿或 candidate，没有运行 Lean/Lake。

## 实际复核范围

1. §1：任意实数 K、任意自然数最低地集规模 n₀ 后才选择反例，反例同时具备严格 two-fifths 根号块大小、按索引点对唯一覆盖、线性交集和对所有 transversal 的交点严格 >K。原正命题的否定只需固定 c=2/5 的反例；exact-design 正命题允许全部正 c，没有误加 c<1。
2. §2–3：真实 affine plane 的 q² 点、q(q+1) 条线、unique line 与 incidence；γ=floor(|X|/(2q)) 的上下界；构造出的 chunks 数、k-uniform hypergraph 无重边、实际 ground subtype、每层 codegree、falling-factorial 比值和 p=1/(γ(log q)³) 的全部有限条件。
3. §4：finite stopping test、heavy seed 存在、最低层及极大 seed、独立输入的 accept/reject 维护、lower-rank low-link 不变式、below-rank potential 的 half charging、增量 1/(8r)、实际 fingerprint 基数 ≤8r²Φ、严格 generated-upset 增长与有限 fuel、终态 light cover、指纹重放确定输出。
4. §5：oversized cover edges degree 为 0；全 cover 边求和 e(H[C])≤e(H)/4；Δ₁ 正确转换为至少 3|X|/(40k) 顶点损失；实际全 child family 与全层 biUnion 计数；M、B、D 与 source 一致；终止 self-child、有限树覆盖全部 arcs、family logarithm 的 oₖ(q) 结论并实际解除 largeness 前提。
5. §6：整个 family 在随机 restriction 之前确定；一个完整 fair-bit space；固定容器全部 short lines 与真实 disjoint packing；只对坐标 disjoint events 主张精确独立；cₖ=2^(−4k)/(16k)；union 包含全部容器。对全部 q(q+1) 条线的 finite MGF/Markov 界以及 exponent −3q/550≤−q/200 正确。两个坏事件族在同一样本空间求和，没有不合法 conditioning 或额外 independence 假设。
6. §7：所有 line traces 保留，q≥5 和 strict >2q/5 保证至少 3 点；不同线没有 duplicate trace，point-pair unique line 转为 unique block。n≤q² 给出 strict >two-fifths √n；q≥3n₀+5 用一条 trace 给出 n≥n₀。所有 bounded-intersection transversal 都成为 k=K+2 arc 并触发已排除的容器事件。真实 finite point/block 双射保持所有候选 Q、cardinality 和 block-index uniqueness。
7. §8：自然数 ceiling 对每个实数 K（包含负数）满足 K≤⌈K⌉₊，给出实数严格交点界并完整否定原断言。文稿没有把 Nie 的较强 logarithmic rate 当成本实现端点。

## 已落实的三项小幅文字精确化

初稿 SHA256 为 72837bf3c939b6405b23b8dc941f51492ce34a921061bb4aaa70c08f1f375dc7。初读没有发现实质数学错误。审稿提出三个精确性调整，文稿作者已修改且本次回读确认：

- §1 把 integers n,m 改为 natural numbers，与 Fin n / Fin m 的实际类型一致。
- §4 charging 明确限定为被 Φ 计入的 deleted old edges；half-weight bound 只对 below-rank potential 使用。
- §5 输出 display 明确写出对每个 family 容器 C 的 size bound，消除 display 中自由 C 的歧义。

这些修改没有改变构造、常数或最终范围。本文结论绑定开头的最终 SHA256。

## 边界

本次文稿审查建立的是数学说明与实际源码路线的一致性，不建立源码已通过 Lean 编译、展开公理输出或内核重放。完整工程编译应独立完成；选定公开版本若修改数学路线、常数、定义或端点前提，应复核相应变化并刷新文稿哈希。
