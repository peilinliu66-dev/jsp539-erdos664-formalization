# JSP539 英文完整说明：容器部分数学对照审查

结论：`SOURCE_NOTE_MATHEMATICAL_ALIGNMENT_PASSED_COMPILATION_PENDING`。

只读审查对象是 `publication_drafts/docs539/MATHEMATICAL_SOLUTION.md`。首版全文 484 行已完整阅读，随后复核负责人通知的三处精确性修订；当前版本 487 行，SHA256 为 `5d49973fd9483aafbcfdf72b0e63c6fcdda5d8537140333e2c18dcc266b0ff1d`。重点复核第 3–6 节与 candidate 的实际有限容器构造。本次没有修改英文稿或 candidate，没有调用 Lean 或 Lake。

对照上次完整读取的五个 LicensedContainers helper、十个委派容器模块和三个支撑模块，当前 18 份源码 SHA256 全部一致。源码读取依据为 `container_scope_read_snapshot.json`；本稿审查依据另存 `container_note_review.json`。此次结论只涉及说明与源码的数学内容相符，不替代编译、最终公理依赖或原题查新审计。

未发现需要修订的真实数学问题。以下环节与实际源码吻合：

1. 第 3 节的 ground 是实际顶点子类型 X，大小 N=|X|，不是全 affine plane 的 q²。边数、单点和高阶 codegree 的式子与 LineChunks 接口及 ArcContainerStep 的实际调用一致。gamma≥k≥2 保证 falling-factorial 分母与 choose(gamma,k) 正。q≥12k^kL^(k−1)、k,L≥1 同时控制所有 t≤k 的 codegrees。
2. 第 4 节 Stop、1/(4r) heavy threshold、最小层和包含极大种子对应 ContainerSelector 的有限存在证明。初始和两种更新实际构造 State 的全部命题字段；文稿未把这些字段作为未证外部接口。
3. LowLinks 只约束 b<r 和非空 proper seed。接受插入秩 u=a−|T|，拒绝插入秩 u=|T|，两者都严格小于 a。最小层控制旧 u 层 link，种子极大性控制接受新 link，p≤1 控制拒绝单边 proper link。这正是源码在插入层证明两个 threshold 相加≤1/(2r) 的分支，其他层仅删除。
4. charging 恒等式的左边是 below-rank 边的 strict supersets，不包括与插入边相等的旧边。插入边在旧 up-set 之外的证明给出无重合；strict-link 的 r 层总上界为 1/2。删除边可能重复被覆盖，但这提供所需的上界方向。故势增益半个插入权重、accept gain 1/(8r)、预算因子 8r² 均正确。
5. 非终止更新严格增加有限 generated up-set 基数，fuel 2^N+1 的终止推导成立。终态 singleton 精确权重加 Stop 给出 pN 的总权重上界，再给出 8r²pN 指纹大小。
6. 重放论证用到了 final fingerprint⊆I；每个接受 seed 属于最终指纹，每个原拒绝 seed 不包含于 I，因此也不包含于最终指纹。family-dependent selector 保证同状态有同查询，归纳重建的是完整 State，而不仅是大小估计。由所有实际指纹的 image 得到所有独立集的实际容器家族。
7. light cover 的边都至少二元；大于原 uniform rank 的覆盖边 degree 为零，其余 degree 可用 codegree bound。乘 p 后求和、用 light weight 和 |C|≤N，得到 e(H[C])≤e/4。再由 deleted vertices 的 degree 上界推出删除量≥3N/(40k)。全部正性因子来自非空 uniform chunk hypergraph 和 k≥2。
8. 节点 child family 上界 B 包含所有指纹；finite insertion recursion 的额外 +1 与源码一致。树层是全部孩子的 biUnion，terminal 节点保留 self-child。未达阈值的分支持续收缩，达到阈值的分支保持小；深度 D 后所有容器均≤2kq。B^d 是全家族上界，文稿没有只计一条分支。
9. log family bound 的显示常数和 q/log(q)、log(q)² 两项与 ArcContainerGrowth 一致。除 q 后的极限为零，ArcStepLarge 的全部 finite 条件对固定 k eventually 成立。最终 ε 家族结论未把数值 largeness 条件留作未证数学前提。
10. 第 6 节短 trace 和 disjoint packing 的常数链正确：短线至少 q²/2、每条 trace≤4k、点重数≤q+1、closed-neighbourhood≤4k(q+1)，故 packing 大小≥q²/(8k(q+1))≥q/(16k)。文稿只对两两不交 trace 的点坐标事件使用独立性；所有容器用实际有限 union bound 计数，与 ContainerProbability 的 hittingRate=2^(−4k)/(16k) 完全相符。

最终三处措辞修订均正确对应源码：n,m 明确为自然数；charging 明确只指势函数计入的被删除旧边；最终家族显示式明确对每个 C∈家族约束大小。这三处加强了精确性，未改变数学证明链条。本次没有提出实质数学改稿请求。先前源码审查中的 hratio 括号读法疑虑已撤回；它也不影响这份英文说明的数学论证。
