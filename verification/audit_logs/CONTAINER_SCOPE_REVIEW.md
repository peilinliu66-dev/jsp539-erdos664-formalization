# JSP539 容器构造独立源码数学审查

状态：`SOURCE_MATHEMATICAL_REVIEW_PASSED_COMPILATION_PENDING`。

对象是用户指定的新版 `FULL_SOURCE_JSP539_REAL_BOUNDS_AUDITED_UNCOMPILED_20261002T0730.zip` 解压后的 candidate。此审查逐项读取五个 LicensedContainers helper，以及十个容器、收缩、迭代、概率模块的完整源码；补读 GroundHypergraph、ShortTraces、ProbabilityBudget 三个衔接模块。实际读取文件及 SHA256 见 `container_scope_read_snapshot.json`。

本审查没有运行 Lean、Lake 或内核重放，也没有修改 candidate。结论是有限数学构造与量词衔接目前未发现实质缺口，不能作为已经通过 Lean 编译的声明。源码中已有证明项仍须由编译审计验证。

## 1. 有限对象及覆盖方向

`Hypergraph V = Finset (Finset V)`，不允许重复边。`restrict H X` 保留包含于 X 的原边；`degree H S` 数包含 S 的原边；`link H S` 对每个包含 S 的原边删除 S。固定 S 的删除在包含 S 的边上单射，所以 link 的基数与 degree 一致，不会通过合并不同边丢失权重。

`C.Covers H` 的方向是“每条 H 边包含某条 C 边”。`upClosure H` 列出含 H 边的全部顶点子集。更新 `(H \\ F.upClosure) ∪ F` 只删除包含新边的旧边。每条被删除边的上闭包仍被一条新边覆盖，因此旧上闭包包含于新上闭包。若 F 至少有一条边在旧上闭包之外，包含严格，成为终止秩。

antichain 更新分别处理旧旧、旧新、新旧、新新四种方向，确实需要并使用每条新边在旧上闭包之外这一条件；不是仅凭“新边不属于 H”替代这一条件。接受和拒绝两种更新均分别证明该条件。

## 2. selector 的条件来自证明

停止条件是 `w_p(H.aboveOne) ≤ p |C(H)|`，其中 C(H) 为没有被 singleton 边禁止的顶点。若停止条件失败，按各层加权 singleton-link 的 incidence 双计数得到某个可用顶点 v，使各层 link 权重和大于 1。活跃层数至多 r+1，所以有一层 link 权重大于 1/(r+1)，进而至少为 1/(4r)。antichain 保证当前不可用顶点不在活跃层边内，因此双计数没有错误地把 singleton 禁止顶点计入。

`exists_choice_of_candidate` 从这个实际候选出发，先对层号取 Nat.find，再在有限种子集合中取最大基数。于是最低层条件和种子包含极大条件都由最优化证明，不作为外部公理或用户输入。

被选择种子非空、不属于当前 H、真包含于某条当前层边，故其基数严格小于层号。被选择种子本身、接受时的每条 link 边均是 antichain 某条旧边的真子集，因而在旧上闭包之外。由此得到结构不变式与严格秩增长。

`Choice` 和 `State` 虽保存命题字段，但后续使用的是构造出的具体值：initial 证明全部 State 字段；choice 从 `exists_choice_of_not_stop` 产生；accept/reject 各自证明全部新 State 字段。最终 theoremA 只接收有限类型、r>0、r-uniform H、p>0、p≤1/(8r²)，不要求给定容器、selector oracle、charging 结论或任何省略的数学接口。

## 3. low-link 与 charging 条件全部落实

低 link 不变式约束层号 a<r、非空种子 L、|L|<a：`w_p(link(H_a,L)) ≤ 1/(2r)`。初始 r-uniform H 的所有较低层为空，故初始条件成立。

接受时插入层的秩为 u=a−|L|，且 u<a≤r。旧 u 层 link 由最低活跃层性质小于 1/(4r)；插入 link 内的非空种子 K 可合成更大的 L∪K，原极大种子性质给出新 link 小于 1/(4r)。两个量之和小于 1/(2r)，其余层只会删除旧边，因此不变式保持。

拒绝时插入单边 {L}，秩 u=|L|<a≤r。旧 u 层 link 同样小于 1/(4r)。新单边的任何较低 link 权重为 p 的至少一次幂，使用 0≤p≤1 得到至多 p；参数范围 p≤1/(8r²) 又蕴含 p≤1/(4r)。因此拒绝也保持全部 low-link 条件。

势函数是秩严格低于 r 的旧边 p 权重。对每个非空插入边 L，把其 strict-link 按秩 0,…,r−1 分层，每层权重≤1/(2r)，合计≤1/2。按包含关系把删除的旧边覆盖到各插入边的 strict supersets；精确恒等式为 `p^|L| w_p(strictLink(H,L)) = w_p(strictSupersets(H,L))`。允许同一旧边重复计数时方向是上界，故删除权重≤插入权重的一半。

插入边均为非空、秩<r、在旧上闭包之外；保留边与插入边不重合。这些是 update_potential_gain 的全部前提，接受及拒绝调用处均显式给出。接受插入 link 的权重≥1/(4r)，所以势至少增加 1/(8r)，而 fingerprint 增加至多 r 个顶点；乘上 8r² 足以支付增加的基数。拒绝不增加 fingerprint 且势不减。初始 fingerprint=∅、势≥0，因此预算不变式覆盖任意有限运行。

终态非空边分解为 singleton 层和大小至少二的层。singleton 权重恰为 p×禁止顶点数，停止条件给出其余权重≤p×可用顶点数，合计≤p|V|。由此 fingerprint 基数≤8r²p|V|。

## 4. 终止、重建与全部容器计数

秩为 generated up-set 的基数，始终≤2^|V|。每个非停止步骤严格增加秩，所以固定 fuel 2^|V|+1 保证停止；无需假设状态类型有限，也不靠“无限过程最终停止”接口。

selector 只依赖当前有限 family，不依赖独立集 I。若 final fingerprint⊆J⊆I，那么每次接受查询的 seed 都包含于 final fingerprint，从而也包含于 J；每次拒绝查询在 J⊆I 下仍被拒绝。归纳得到逐步重放相同完整 State。特别地，以 final fingerprint 再运行，重建完全相同的输出 family，证明不同 I 产生同一 fingerprint 时输出一致。

fingerprints 是全部独立输入输出的有限 image，containerMap 为从指纹重放所得可用顶点集。独立输入始终独立于更新 family，所以包含于该可用顶点集。旧上闭包单调增长，加上终态无空边，保证终态非 singleton 边覆盖 H restrict C，singleton 边不能出现在 C 内。这些给出了 theoremA 的三个输出条件。

`fingerprintBall m` 通过实际逐次插入顶点递归构造；包含基数≤m 的所有集合。有限 union/image 计数得到基数≤(|V|+1)^(m+1)。所有实际 fingerprints 均进入 floor(B) 半径集合，因此全部容器 image 的计数≤(|V|+1)^(floor(B)+1)。没有把全部家族缩成一个代表容器。

## 5. 收缩定量条件及 affine arc 调用

light cover F 的每条边大小≥2。若某边大小超过 uniform rank r，其原超图 degree=0；否则使用实际 codegree bound。覆盖的边数≤各覆盖边 degree 和，乘 p 后化为 p 权重之和；结合 light cover 总权重≤p|C| 以及 |C|≤|V|，得到 |H restrict C|≤|H|/4。

每条限制后丢失的原边包含至少一个被删除顶点，所以 |H|≤|H restrict C|+∑deleted degree(v)。单点 degree bound 10r|H|/|V| 迫使删除顶点至少 3|V|/(40r)，故 |C|≤(1−3/(40r))|V|。H 非空和正秩给出顶点总数正，所有除法与取消因子所需正性均有前提。

ArcContainerStep 使用实际 `BalancedGroundHypergraph`，其构造由 LineChunks 提供；这里没有要求用户提供该结构或其 degree 估计。选择 g=chunkSize(X)、L=log(q)^3、p=1/(gL)，实际 ground type 大小=|X|。前提 |X|>2kq、k≥2 得到 g≥k、|X|≤3gq；数值条件 L≥8k 确保 p≤1/(8k²)。

单点 degree≤(q+1) choose(g−1,k−1)、边数≥q² choose(g,k)，经 falling-factorial 比值给出≤10k|H|/|X|。t≥2 codegree≤choose(g−t,k−t)，经比值给出 degree×g^t≤k^t choose(g,k)。`12 k^k L^(k−1) ≤ q` 蕴含全部 t≤k 需要的 `12 k^t L^(t−1) ≤ q`，因此所有 higher-codegree 条件同时满足。顶点子类型的 image 单射，所以传回 affine points 时容器基数、包含关系不变。

容器子节点上界为 `(q²+1)^(floor(24k²q/L)+1)`；这里用 |X|≤3gq 消去 ambient X，得到统一分支上界。终止节点保留 self-child，非终止节点应用 proved shrinking_family。整层为全部节点孩子的 biUnion，保持所有 arc 的覆盖；全部容器数≤branch^n；每个未终止节点基数≤(1−3/(40k))^n q²。深度 ceil(40k log q)+1 足以压到≤q，因此所有末层容器≤2kq。

最终 family 数的 log 上界是 `3(40k+2)(24k²q/log(q)+log(q)²)`，除以 q 对固定 k 趋于 0。ArcStepLarge 的全部数值条件均由 log 趋向无穷和 log 固定幂/q→0 推出 eventually；`eventually_arc_container_family` 最终前提只有 k≥2、ε>0、q 足够大且为素数，不把 ArcStepLarge 留为缺失证明的外部假设。

## 6. fixed-container 概率衔接

ContainerProbability 定义唯一实验为每个实际 affine point 的 fair bit。容器 C 若漏掉一条线，则 hits-all 概率为零。否则 ShortTraces 中至少 q²/2 条短线，trace 大小≤4k，每个实际 trace 点最多属于 q+1 条 trace。有限最大 disjoint packing 通过 neighbourhood 覆盖计数产生 I，使 q≤16k|I|；该 I 的存在与计数有证明。

只对 I 内两两不交的实际 trace 调用 UniformBits 的 finite independence 恒等式，所得因子为 `1−2^(−|trace|)`，每因子≤exp(−2^(−4k))。因此任何形状的 C（只要求 |C|≤2kq）的命中所有线概率≤exp(−hittingRate(k)q)，hittingRate(k)=2^(−4k)/(16k)>0。全家族通过实际有限 union bound 计数；大小≤exp(hittingRate(k)q/2) 时坏事件总概率≤exp(−hittingRate(k)q/2)。没有断言任意相交 affine lines 彼此独立。

ProbabilityBudget 把上述坏事件概率和 q(q+1)exp(−q/200) 相加，固定 k 下趋于零。是否进一步得到每对点恰好一次的设计和 arbitrary real K，属于上游总体审查，不能仅凭本文件容器部分独立认定；本次看到的容器链条没有削弱 exact-design 目标的替代接口。

## 7. 编译阶段边界

对 ArcContainerGrowth 的 hratio lambda 最初产生过“多余右括号”的读法疑虑。逐层复数后，三个结束括号分别关闭 cast、先前开启的分式表达式组和 lambda，括号实际匹配；该疑虑已经撤回，不应据此删改源码。固定 k 的常数倍 log(q)^(3(k−1))/q 极限也与源码的实际表达式一致。

本结论只绑定 JSON 中的实际 SHA256；本次源码数学审查没有给出已确认的解析错误。编译修复如改变数学定义、定理前提、selector 或不等式，而不仅是语法/API，则应重新审查相应改变。
