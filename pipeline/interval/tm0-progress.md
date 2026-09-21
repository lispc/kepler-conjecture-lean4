# TM0 进度笔记（一元 Taylor 模型 pilot）

> 运行记录。每个可验证子步骤一段：做了什么 / 验证命令与结果 / 下一步。
> 工作树 `/home/scroll/repos/kepler-g4e`（分支 wip/g4-emit）。

## 0. 理解与计划（2026-09-21）

任务：按 `pipeline/interval/taylor-model-design.md` §4 第一行实施 TM0。

已读：设计文档全文、`Expr.lean`（IExpr/eval/evalReal/checkPos_sound:364）、
`CertG.lean`（BBTreeG/covers_point:57/bb_soundG:118/exGExpr:135）、`Basic.lean`
（Dyadic/DInterval 算术）、`Sqrt.lean`（`Dyadic.sqrtI d s` 契约：s² ≤ m·2^(e%2)
< (s+1)² → [⟨s,e/2⟩,⟨s+1,e/2⟩]，`sqrtI_sound`/`sqrtI_cases`/`sqrtI_nonneg`）、
`Div.lean`（`DInterval.recip I out` + `recip_sound` : J.mem (1/y)；`div` 同形）、
`Cert.lean`（`DInterval.mid` + `toReal_mid`、`boxMem`、`boxSub`）、
`CertBool.lean`（splitOKB/coversB 模式）。

**关键设计偏差（记录在此，理由如下）**：设计 §3.1 的 T1 路线
（`taylor_mean_remainder_bound` + Diff2OnBox + Hessian 界）在 TM0 被
**纯代数合成路线**取代。理由：§1.2 的 `Valid` 语义本身就是 ∃a（存在斜率
aᵢ ∈ dfBᵢ）形式——这个形式下 +−× 与 sqrt 的 Valid 保持性是**纯代数恒等式
+ 区间算术**，逐节点直接构造见证 a，完全不需要 ContDiff/导数机制。n=1 的
T1 虽然不需要 g'' 展开引理，但仍要求 |f''| 的盒上界（= 符号二阶导 AST，
本质是 TM1 的 deriv_sound 机器）。代数路线对**一般 n** 同样成立（Valid 的
∃a 形式无维数依赖），等于顺带把 TM1 的 T1/g'' 债也化解了——留给 TM1 的
只剩 div/trans 节点的合成规则。sqrt 的余项用初等恒等式
`√s − √t = (s−t)/(√s+√t)` 推得 `|1/(√s+√t) − 1/(2√t)| ≤ |s−t|/(8c^{3/2})`
（c = 公共下界 > 0），无需 g''。`taylor_mean_remainder_bound` 实测存在于
Mathlib v4.32.2（Taylor.lean:390，签名 `{f : ℝ → E} (hab : a ≤ b)
(hf : ContDiffOn ℝ (n+1) f (Icc a b)) (hx) (hC) : ‖f x − taylorWithinEval …‖
≤ C*(x−a)^(n+1)/n!`），本里程碑未使用。

**另一个实测记录**：验收例 2 的"裸区间二分永不收敛"对一元 +−× 真命题
不成立——`x²` 在正盒上的区间求值是**精确的**（端点单调），`x²−2` 在 √2
上方任何 dyadic 盒的 lo = a²−2 是精确 dyadic，裸区间立即闭合。TM 的真正
收益是定量（叶数），定性差距在一元 +−×sqrt 不存在。验收 2 按字面执行：
x²−2 在 √2 邻域、TM 树深度 ≤ 2 内核闭合；裸区间对照如实记录。

**exGExpr 的 div 节点**：evalTM（TM0）不支持 div；`x/4` 改写为
`x·⟨1,−2⟩`（除以 2² = 乘 dyadic 逆元，语义相同），记为 `exGExprTM`，
验收 1 用它配 taylorLeaf 闭合 √x − x/4（同一实函数）。

### 架构（落地形状）

- 新文件 `lean/Kepler/Interval/CertTM.lean`（import Cert → Expr）：
  - `SqrtTMP`（每个 sqrt 节点的证书：slo/shi/sc 三个 mantissa + o1/o2 两个
    recip 粒度）；`evalTM` 用 `List SqrtTMP` 按遍历顺序消耗（state-passing）。
  - `TaylorM n`（y w fB dfB err，一般 n）；`TaylorM.Valid`（§1.2 原文）。
  - 组合子：`neg/add/sub/mul`（纯 DInterval 算术）、`sqrt`（Option，消费
    一个 SqrtTMP：c := fB.lo − W 要求 isPos；√fB.lo/√fB.hi/√c 三张 sqrtI
    证书；J := recip [2√fB.lo, 2√fB.hi]（斜率 1/(2√f(y)) 的包围）；K :=
    recip (point 8·c·√c.lo)（Mg'' = 1/(8c^{3/2}) 上界）；err' =
    err·J.hi + W²·K.hi；dfB'ᵢ = dfBᵢ·J；fB' = [Jl.lo, Jh.hi]）。
  - `W0 := Σᵢ |dfBᵢ|.abs.hi·wᵢ`（foldl on List.finRange），`W := dmax
    (W0+err) 0`（振幅界）。
  - `evalTM`（中心 y := boxCenter = mid，w := dmax(y−lo, hi−y)；const/var/
    neg/add/sub/mul/sqrt 四族 + 基例；abs/ite/div/trans → none）。
  - 定理链：`valid_const/var/neg/add/sub/mul/sqrt`（独立引理）→
    `evalTM_sound`（归纳 + M.y = boxCenter ∧ M.w = boxW 不变式）→
    `loBound`（fB.lo + Σᵢ (dfBᵢ·[loᵢ−yᵢ, hiᵢ−yᵢ]).lo − err）+
    `loBound_sound` → `checkPosTM`（wf && evalTM && loBound.isPos）→
    `checkPosTM_sound`（与 checkPos_sound 同形）。
- `CertG.lean`：BBTreeG 加构造器 `taylorLeaf box ps (hcert : checkPosTM e box
  ps = true)`；`covers_point` 结论一般化为
  `∃ box el, el.evalReal = e.evalReal ∧ boxMem box ρ ∧ ∀ σ, boxMem box σ →
  0 < el.evalReal σ`（leaf 走 checkPos_sound，taylorLeaf 走
  checkPosTM_sound）；bb_soundG 适配。外部使用点只有
  coversB_sound/bb_soundG/.leaf/.node（Cases/* 61970 处 grep 确认无
  BBTreeG.covers_point 直接调用），加构造器安全。
- 验收例放 CertG.lean 尾部（exGExprTM + 单 taylorLeaf 树根闭合 [1,2]；
  x²−2 例：盒 [2897/2048, 3/2]，深度 1 两叶 taylorLeaf）。

### 下一步

写 CertTM.lean 骨架（定义 + sorry 占位）→ 编译过 → 逐引理填证明 →
CertG 构造器 → 两例 + #print axioms → lake build。

## 1. CertTM.lean 编译通过（2026-09-21）

做了：写出完整 `lean/Kepler/Interval/CertTM.lean`（~990 行）：SqrtTMP、
TaylorM（y/w/fB/dfB/err）、Valid（§1.2 原文）、组合子 neg/add/sub/mul/sqrt、
W0/W/loBound、evalTM（`Option.bind`/`map` 风格 + `List.head?` 消费 sqrt
证书）、定理链 valid_const/var/neg/add/sub/mul/sqrt → evalTM_sound →
loBound_sound → checkPosTM → checkPosTM_sound。

验证：`lake env lean Kepler/Interval/CertTM.lean` —— **零错误零警告零 sorry**
（grep sorry 只剩文件头注释）。~6s。

落地中改的要点（与计划偏差，都不影响语义层）：
- `Finset.sum_univ_def` 在此 Mathlib 里不存在（只有 prod 版）——自证桥引理
  `sum_finRange_map`（`List.ofFn_eq_map` + `List.sum_ofFn`）。
- `evalTM`/`TaylorM.sqrt` 的证明解构用 `Option.bind_eq_some_iff` /
  `Option.map_eq_some_iff`（match 解构在证明里被臂绑定遮蔽坑过一次，
  bind 风格干净利落）。
- `valid_add`/`valid_mul` 实测**不需要** `Mf.w = Mg.w`（只有 y 要一致，
  w 各自内部自洽即可）——假设保留但标 `_hw`。
- `Valid` 的 conjunct 1（y ∈ box）实际用于 err ≥ 0 / dfB.abs.hi ≥ 0 的
  语义侧条件（ρ := y 代入），不是装饰。
- sqrt 余项完全初等：`sqrt_sub_eq`（差商恒等式）+ `sqrt_slope_diff`
  （|1/(√s+√t) − 1/(2√t)| ≤ |s−t|/(8c√c)，纯代数 + Real.sqrt 单调性）。

下一步：CertG.lean 加 taylorLeaf 构造器 + covers_point 一般化 +
bb_soundG 适配；两个验收例 + #print axioms；lake build。

## 2. CertG 整合 + 验收例（完成，2026-09-21）

做了：
- `CertG.lean`：`import Kepler.Interval.CertTM`；`BBTreeG` 新增构造器
  `taylorLeaf box ps (hcert : checkPosTM e box ps = true)`；
  `covers`/`coversB`/`coversB_sound` 加分支；`covers_point` 结论一般化为
  `∃ box el, el.evalReal = e.evalReal ∧ boxMem box ρ ∧ ∀ σ, boxMem box σ →
  0 < el.evalReal σ`（leaf 走 `checkPos_sound`，taylorLeaf 走
  `checkPosTM_sound`）；`bb_soundG` 适配（签名不变）。
  兼容性：全库无文件对 BBTreeG 做模式匹配（Cases/* 只用
  `.leaf`/`.node`/`coversB_sound`/`bb_soundG`，签名全不变；FillParams 只在
  注释提及）。Cases/* 未重建（归其他 runner 的活儿；接口未变）。
- 验收例 1（sqrt pilot）：`exGExprTM = √x − x·⟨1,−2⟩`（div→mul dyadic 逆元，
  `exGExprTM_same` 证语义相同）；单叶 `taylorLeaf` 在根盒 `[1,2]` 闭合
  （对照：裸区间版 `exGTree` 要 2 叶）。证书 `[⟨2,2,2,−3,−2⟩]`。
  end-to-end：`exGTM_end_to_end : 0 < √x − x/4` on [1,2]。
- 验收例 2（x²−2 在 √2 邻域）：根盒 `[2897/2048, 3/2]`（2897/2048 是 2¹¹
  分母下 √2 上方最近 dyadic）；`exTM2Root_fails`：根盒 checkPosTM = false
  （y²−2−2yw−w² < 0，O(w²) 余项吞掉 9.5e-4 余量）；深度 1 树两叶闭合
  （`exTM2L_cert`/`exTM2R_cert`）；end-to-end `exTM2_end_to_end :
  0 < x*x − 2`。诚实对照 `exTM2Root_bare`：裸区间在根盒即闭合（x·x 在正盒
  上求值精确）——设计文档"裸区间永不收敛"对此例不成立，已记录于 §0。
- 旧的 exGTree/exG_end_to_end 保留未动（双路径并存）。

验证（全部 lake env lean / lake build，wrapper PATH）：
- `lake env lean Kepler/Interval/CertG.lean`：零错误；`#print axioms` 输出：
  - `exGTM_end_to_end`: [propext, Classical.choice, Quot.sound]
  - `exTM2_end_to_end`: [propext, Classical.choice, Quot.sound]
  均无 sorryAx ✓（验收 3 通过）
- `lake build Kepler.Interval.CertG Kepler.Interval.CertGD`：✔ 8666 jobs
  全绿（验收 4 通过；CertGD 回归无恙）
- `grep sorry` CertG/CertTM：无

验收 1✓（taylorLeaf 闭合 sqrt pilot）、2✓（x²−2 深度 1 < 2-3 层上限，
根盒 TM 失败→二分一层收敛）、3✓、4✓。

下一步：commit（CertTM.lean 新增 + CertG.lean 修改 + 本笔记）。
