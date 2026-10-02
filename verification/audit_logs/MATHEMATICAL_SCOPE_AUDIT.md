# JSP539 / Erdős 664：独立数学与源码范围审查

审查日期：2026-10-02。标签：SOURCE_MATHEMATICAL_SCOPE_PASS_PENDING_COMPILATION。

结论：对选定的 REAL_BOUNDS_0730 版本，未发现致命数学缺口、原题范围缩减，或把容器、抽样成功、设计同构、最后反例作为未证明接口输入的情况。已完整读取 32 个 Lean 文件，包括 23 个本题证明模块、5 个复用 helper、两份 import root、Verify.lean 与 lakefile.lean。核心数学构造和全部范围适配具有相互闭合的实际源码证明体。

**此结论是独立的数学和源码审查，不是 Lean 编译成功、公理检查输出或内核重放结论。本次没有运行 Lean/Lake，没有修改 candidate。** 包内先前的 audit/INDEPENDENT_REVIEW.md 仅作为待核对材料；没有以它的判断或有限 Python 试验代替本次审查。

选定输入 ZIP SHA256：168c87fc14b7c0511e12cf79f35163190c0e342a875d006117e62478daadaaf9。
实际读取源码的逐文件 SHA256、行数、原包比对和本地 import 图见 mathematical_scope_read_snapshot.json。本次快照的 32 个文件均与选定原包字节相同。

## 最终命题和量词

exists_bad_fin_design_real 明确证明：对每个实数 K 和每个自然数 n₀，存在自然数 n,m 及索引族 A:Fin m→Finset(Fin n)，满足：

1. n≥n₀。
2. 每个块的基数严格 >(2/5)√n。
3. 每两个不同点恰好属于一个**块索引**：∀x≠y，∃!i，x,y∈Aᵢ。
4. 不同块索引的交集基数至多 1。
5. 对每个命中全部块的 Q⊆Fin n，存在 i 使 K<|Q∩Aᵢ|，右侧基数转换为实数。

不存在“只证明每对点至多一次”的替代。实际设计先在有限域平面中构造，再把点和块分别重标为 Fin n 与 Fin m，唯一性落实到索引。

OriginalScope.erdos_664_real 否定线性族原题的“∀实数 c∈(0,1)，存在实数 K，对所有 n,m,A 存在命中全部块且每块交点至多 K 的 Q”。OriginalScope.block_design_real 否定 exact-pair 原题的同型断言，其中 c>0 没有上界限制。两者在固定 c=2/5 处构造反例即足够否定全称原命题。它们没有声称对每个正 c 都给出反例；这不是原否定命题所需的量词。所构造规模为任意大的某些 n，不是每个指定 n；原题的统一上界已由该范围完整否定。

自然数版本五个端点与新增三个实数端点均在 Verify.lean 中列出；相关 expanded statement 与 axioms 输出尚待实际执行。

## 实际有限几何及分块

AffinePlane.lean 的点为 ZMod q×ZMod q，其中 q 为素数；直线为 Option(ZMod q)×ZMod q。垂直线与斜率线均有显式参数化。实际证明了点数 q²、线数 q(q+1)、每线 q 点、每点 q+1 线、不同点存在唯一连线、不同线至多交一点；这些不是抽象 incidence 假设。

ChunkPartition.lean 对任何正整数 γ 用有限集强归纳构造 γ 元互不相交块及大小 <γ 的余项，给出真实覆盖和基数恒等式。在 X⊆AG(2,q)、|X|>2kq 时，取

\[
\gamma=\left\lfloor\frac{|X|}{2q}\right\rfloor,\qquad
k\le\gamma,\qquad2\gamma q\le|X|\le3\gamma q,
\]

其中 k≥2。各条线与 X 的交集实际分块，所有块的 k 元子集构成真正有限 k 一致超图 H。同线块互不相交；异线块交集至多一点，所以不重复 k 边，也不重复 γ 块。实际基数和 codegree 估计为

\[
e(H)\ge q^2\binom\gamma k,\qquad
\Delta_1(H)\le(q+1)\binom{\gamma-1}{k-1},\qquad
\Delta_t(H)\le\binom{\gamma-t}{k-t}\quad(2\le t\le k).
\]

GroundHypergraph.lean 把这个超图重标到 X 的 subtype，保留边数、uniformity、所有 degree 和 independent-set 性质；容器定理的宇宙基数因此是 |X|，没有误用整个平面的 q²。所有 k arc 都在此实际超图中独立。

## 容器存在没有作为假设

已完整读五个 LicensedContainers helper 及 ContainerPotential、ContainerAlgorithm、ContainerCore、ContainerCounting、ContainerShrink。另有独立容器分支复核，记录于 CONTAINER_SCOPE_REVIEW.md。

非终止状态的停止条件确为 wₚ(H>1)≤p|C(H)|。若失败，有限加权 incidence 计数产生 heavy singleton seed，再由最小可用层与最大 seed 基数选出 canonical choice。选择只依赖当前状态，不依赖输入 independent set。

每一步按 seed 是否包含于输入集合进行接受或拒绝，更新为 (H\F↑)∪F。实际维护 antichain、rank bound、非空边、输入独立性及 low-link 不变式。接受 replacement 为该层的 seed link；拒绝 replacement 为 seed 本身。二者都包含旧 upset 之外的边，故 generated upset 严格增长。其大小至多 2^|V|，所以固定 fuel 2^|V|+1 足以终止。

low-link 每层界为 1/(2k)，有限层和给出每个非空 replacement seed 的旧 strict-link weight 至多 1/2。删除旧边可逐个计入 replacement seed 的 strict supersets，得到被删 weight 至多插入 weight 的一半。接受 choice 的 weight 至少 1/(4k)，故 below-rank potential 增量至少 1/(8k)。接受的 seed 大小至多 k，据此维护实际 union fingerprint 的不变式 |S|≤8k²Φ。

终止时 singleton 部分 weight 恰为 p 乘 forbidden vertices 数，非 singleton 部分由停止条件控制，故 Φ≤p|V|，最终 |S|≤8k²p|V|。

接受过的 seed 都在最终 fingerprint 中，拒绝 seed 从未成为输入的子集。沿相同确定选择逐轮重放，证明以最终 fingerprint 作为输入得到同一最终状态。容器是实际 fingerprint family 的确定 image，而不是另外自由选择的集合。image 数量由有限 insertion recursion 控制为

\[
(|V|+1)^{\lfloor8k^2p|V|\rfloor+1}.
\]

最终 light cover 的每条边大小至少 2，cover 真正覆盖 H[C]，并满足 ∑p^|E|≤p|C|。Theorem A 的输入只含有限 uniformity、正 rank 和 0<p≤1/(8k²)，没有 consistency 或 container existence 参数。

## 实际缩小与全树数量

令 L=(log q)³、p=1/(γL)。ArcStepLarge 的有限条件 log q≥1、L≥8k、q≥12k^k L^(k−1) 保证 p≤1/(8k²)。独立证明的 falling-factorial 比较

\[
\binom{\gamma-t}{k-t}\gamma^t
\le k^t\binom\gamma k
\]

配合实际 degree 与 |X|≤3γq，给出

\[
\Delta_1(H)\le\frac{10k\,e(H)}{|X|},\qquad
\deg_H(E)\le\frac{e(H)}{4|X|}p^{|E|-1}
\quad(2\le|E|\le k).
\]

cover 中比 k 更大的边有 degree 0；没有忽略它们或对它们错误使用低阶 codegree。对所有 cover 边求和得到 e(H[C])≤e(H)/4。删除顶点最多删除 Δ₁(H) 条边，所以至少删除 3|X|/(40k) 个顶点。

每个非终止节点实际构造全部 child containers，终止节点用唯一 self-child 填充。设

\[
M=\left\lfloor\frac{24k^2q}{(\log q)^3}\right\rfloor,\qquad
B=(q^2+1)^{M+1},\qquad
D=\lceil40k\log q\rceil+1.
\]

每层为上一层所有 child family 的有限 union。归纳保证全部 arcs 始终被覆盖、计数至多 B^D、全部叶大小至多 2kq。衰减系数 1−3/(40k) 为非负；深度 D 足以使未终止节点的衰减界降至 q，因此无需假定树最终停下。

源码实际控制 full-family logarithm 为

\[
\log|\mathcal C|\le3(40k+2)
\left(\frac{24k^2q}{\log q}+(\log q)^2\right)=o_k(q).
\]

取 k 固定并令 q→∞，所有有限 local conditions 及任意正 ε 的 |C|≤exp(εq) 由 scalar limits 自行解除。最终阈值 theorem 没有容器 family 输入。

## 同一概率空间的完整两类坏事件

全程使用一个非空有限样本空间 Point q→Bool，每个函数均匀取样；fraction 与 average 都是实际 finite sums 除以样本数。没有引入未定义的随机对象、外部浓缩定理或任意线间独立假设。

固定容器 |C|≤2kq。incidence 计数给出至少 q²/2 条 short lines，其 trace 与 C 的交集大小 <4k。若存在空 trace，命中全部线的事件为空。否则从实际有限 powerset 中选择最大互不相交 trace 族，其 closed-neighbourhood 大小至多 4k(q+1)，给出 m≥q/(16k)。

对这个**坐标支持互不相交**的 trace 族，完整 function-space 双射和 finite products 证明精确独立性。每个 trace 未被保留点命中的概率至少 a=2^(−4k)，所以

\[
\Pr(C\cap R\text{ hits all lines})
\le(1-a)^m\le e^{-c_kq},\qquad c_k=\frac{a}{16k}>0.
\]

对整个实际 family 求 union bound，并选 ε=cₖ/2，得到第一类坏事件概率至多 exp(−cₖq/2)。这个 union 没有只取某个代表容器。

同一样本空间中，单条线 retained count 的有限 MGF 被直接展开为

\[
\mathbb E e^{-tX}=\left(\frac{1+e^{-t}}2\right)^q.
\]

取 t=log(11/10)，moment 为 (21/22)^q。由 log(11/10)≤1/10、log(21/22)≤−1/22 和 finite Markov，得

\[
\Pr(X\le2q/5)\le
\exp((-1/22+1/25)q)=e^{-3q/550}\le e^{-q/200}.
\]

对所有 q(q+1) 条线求 union bound。总坏事件界 exp(−cₖq/2)+q(q+1)exp(−q/200)→0，保证存在同一个 R 同时避免两类坏事件。无需两类坏事件互相独立，也没有把第一类概率条件化到 line-size 好事件后继续沿用原界。

## 精确设计、原题与实数界的闭合

对自然数 K，先固定 k=K+2，再选一个素数 q 超过容器和概率的所有阈值，并令 q≥3n₀+5。任意大素数由实际 Mathlib theorem 调用取得。

每条 trace 满足 |R∩ℓ|>2q/5。由 q≥5，其基数严格 >2，因此至少 3；不同线不能产生重复 trace。所有原直线保留为 blocks，未删除空块、单点块或随机选取部分 incidence。任意保留点对仍有唯一 ambient line，故恰好同属一个 trace block。

取 n=|R|≤q²，有 |R∩ℓ|>(2/5)q≥(2/5)√|R|。选择一条实际直线即可给出 |R|≥|R∩ℓ|>(2/5)q≥(2/5)(3n₀+5)>n₀，所以最低地集规模被真实构造解除。

若一个 transversal Q⊆R 对每块交点至多 K，则 Q 是 k arc，属于某个完整 family 容器 C。因为 Q 命中所有 trace 且 Q⊆C∩R，C∩R 也命中全部线，直接违反选择 R 时排除的容器坏事件。因此所有 transversal 都在某块出现交点 >K。

Finset.equivFin 对真实点集和真实块集分别给出双射。cardinality、hitting、intersection cardinality 保持，块双射使唯一 block set 转成唯一 block index。原题的候选 Q⊆Fin n 全部经该双射 lift 回实际地集；没有只对某种编码或特殊 transversal 证明。

对实数 K，选自然数 K′=⌈K⌉₊，满足 K≤K′，包括负 K。自然数构造给出 K′<|Q∩Aᵢ|，转为实数后得 K<|Q∩Aᵢ|。这一步已在 RealScope.lean 实际源码中完成。

## 静态发现、边界和后续验证

自主去除嵌套 block comments、line comments 与字符串后的扫描，未发现 sorry、admit、新增 axiom、sorryAx、native_decide、unsafe、implemented_by 或 extern 代码 token；本地 imports 完整且无 cycle，普通括号均平衡。

曾对 ArcContainerGrowth.eventually_ArcStepLarge 中 hratio 的三个末尾右括号产生视觉怀疑，已逐括号复数并撤回：它们分别关闭 denominator cast、numerator 外层组、function 外层组；不需要删改。此项已与容器分支审查者交叉确认，候选字节不变。

这些词法观察不能代替实际编译；API、elaboration、tactic 或模块可见性错误仍由实际 build 判定。后续需要保持最终声明及所有条件含义，完成全 library build，执行 eight expanded endpoint statements 及实际传递公理输出，并对最终模块运行 Lean kernel replay。数学修复若改变了上述核心输入或证明路线，应重新审查对应分支。

没有把包内 finite Python assertions 当作无限范围的证明，也没有声称此数学/source 检查建立了公众优先权、官方奖项资格或审稿接受。这些分别由查新证据与官方审核判定，不属于本报告的编译结论。
