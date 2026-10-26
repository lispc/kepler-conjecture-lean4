# 侦察报告 — LA1 `LocalFan` 编码保真与 foundation 桩可证性（la1-localfan-scout）

- 基线: `aff2188a58577ca5c2336a0f8902f9a6a756314b`（BASE_COMMIT.txt）
- 只读侦察；机器探针 = `lake env lean`（/tmp，秒级，用现成 olean）；零 .lean 改动。
- 探针与输出: 本目录 `probeB.lean` / `probeE.lean` / `PROBE_OUTPUT.txt`（lake env lean 自然退出 0）。
- 标记约定: **【原文】** = 源码字面；**【推断】** = 据证据推断、未逐条实测。

## 0. 结论速览

1. **问1**：LA1 `LocalFan`（LocalAuto1.lean:157）把 HOL `local_fan` 的 dart 集从
   `darts_of_hyp = ord_pairs ∪ self_pairs`（含孤立点自环）**弱化**为 `dart1OfFan`
   （纯边对）。HOL `local_fan` 内部可证每顶点度数恰 2（local_lemmas.hl:1967）；
   LA1 编码拿不到，`V \ ⋃₀E` 的 junk 孤立顶点合法。忠实镜像 `dartOfFan`
   **已在树内**（Fan.lean:90）但未被 `hypermapOfFan`（Fan.lean:1169）采用；
   LA1:152-156 docstring 自认 "residual HYP-layer bookkeeping is tracked by
   downstream obligations"。LA4 `localFan_p4` 同病（LA36:592 `hyp_p4` 的 FAN
   支 = `hypermapOfFan`）；忠实世界 = LA2/LA3 `localFan_p2/p3` + AzimBridge
   （`dartsOfHyp_p3`，`exists_hypHyp_of_fan`）。
2. **问2**：受害面 = LA7:1073-1128 九桩 + LA7 FAN_PERIMETER 族 4 枚 + BGMIFTE
   （LA7:1691）+ 跨文件 8 枚（LA14×3、LA35×2、LA36:805、LA37×2）。
   **已落地传染 = 零**（w5b 闭合的两枚免疫；其余消费点全部仍是 sorry）。
3. **问3**：机器反例链**闭合**（模一个非机器环节）：
   - ε junk-collapse **可证**——本 toolchain 的 `Classical.epsilon` 空谓词分支
     值 = `choice h`（与谓词无关，Init/Classical.lean:96-110
     `strongIndefiniteDescription`），两枚空谓词的 rhoNode1 相等（probeB 探针）。
   - `LocalFan` + 两个无边顶点 ⇒ `RHO_NODE1_INJECTIVE` 见证对机器成立
     （LHS 真、RHS 假）；n=1 的 `ITER_IVS_RHO_IDD` 双点夹逼机器成立。
   - 唯一非机器环节：含两个孤立顶点的 `LocalFan` **实例存在性**——由基础
     fan 存在性（树内 `CKQOWSA`/`ESTD_fan7` 已证）+ 无边顶点的开稠密
     genericity（fan7 要求孤立点射线避开全部边锥；`affGe {0} ∅ = {0}`，
     ContraFan `affGe_0_empty`）**【推断】**。
4. **问4**：推荐 **(a) SF 加前提** `hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E`；
   (b) wedge-相交引理路线有「证不出」真实风险（HOL 不走此路：HOL 从
   self-pairs + dih2k 计数内部消孤立点；凸世界 junk 可满足性未被排除）；
   (c) 定义级修复 blast radius 16 文件不推荐；(d) 迁移 p2 世界被 LA7
   import 死角阻塞。
5. **问5**：LA1:121 `Generic` 用 `affGt`，HOL `generic`（localization.hl:103）
   用 `aff_ge` —— 前提变弱 = **危险方向**（结论变强，有假风险），
   波及 scsGeneric → 8 文件；LA2:273 `circular_p2` 用 `affGe`，HOL
   `circular`（:107）用 `aff_gt` —— 同向危险，波及 KCHMAMG（LA5:5018）。
   LA1:117 `Circular`（affGt ✓ 忠实）与 LA2:268 `generic_p2`（affGe ✓ 忠实）
   无病。机器佐证：`affGt ⊆ affGe` + `0 ∈ affGe\affGt`（probeE）。
6. **W6a 裁决：需先修陈述，不可原样开填**。LA7:1073-1128 块在当前弱编码下
   7 枚不可证 + 2 枚（RHO_NODE1_INJECTIVE、ITER_IVS_RHO_IDD 型）机器反例可闭
   （模实例存在性）。SF-2（加 hedge）拍板后 W6a 即可以新陈述开工，走
   `localFan_p3.of_LocalFan_noIso`（AzimBridge:953，已真）+ LA5 p2-kit；
   SF 不批则需改道（见 §4）。

## 1. 问1 —— 编码逐字段对照

### 1.1 HOL 原文（localization.hl）

- **【原文】** :40-44：
  `ord_pairs E = {a,b | {a,b} IN E}`；
  `self_pairs E V = {(v,v) | v IN V /\ EE v E = {}}`；
  `darts_of_hyp E V = ord_pairs E UNION self_pairs E V`。
- **【原文】** :58 `HYP (x,V,E) = (darts_of_hyp E V, ee_of_hyp, nn_of_hyp, ff_of_hyp)`。
- **【原文】** :66-70 `local_fan (V,E,FF) <=> let H = hypermap (HYP (vec 0,V,E)) in
  FAN (vec 0,V,E) /\ (?x. x IN dart H /\ FF = face H x) /\ dih2k H (CARD FF)`。
- **【原文】** :92 `convex_local_fan`、:103 `generic`（`aff_ge`）、:107 `circular`
  （`aff_gt`）、:115/:117 `rho_node1`/`ivs_rho_node1`（Hilbert @）、:119
  `interior_angle1`、:122 `sol_local`。
- HOL 侧「无孤立点」不是前提而是**定理**：local_lemmas.hl:1967
  `local_fan ∧ v ∈ V ⇒ CARD (EE v E) = 2`（度数恰 2）；:289 `¬(FF = {x})`；
  :267 `¬(V = {v})`；:442 `¬(V={v1,v2} ∧ {v1,v2} ∈ E)`；:1796
  `darts_of_hyp E V = FF ∪ {v,w | w,v IN FF}`。
  机理【推断】：孤立点自环 dart (v,v) 是 faceMap 不动点，与 `dih2k` 的
  card=2·k、`dart = face ∪ node_map''face`、orders 三条不相容。

### 1.2 LA1/Fan 侧现状

- **【原文】** LocalAuto1.lean:157-161 `LocalFan V E FF := ∃ hfan : FAN 0 V E,
  ∃ x ∈ (hypermapOfFan 0 V E hfan).darts, FF = orbitMap ...faceMap x ∧
  Dih2k ... FF.ncard`。
- **【原文】** Fan.lean:1169 `hypermapOfFan`：`darts := hD.toFinset`，
  `hD = finite_dart1_fan hfan`；Fan.lean:86 `dart1OfFan V E = {d | {d.1,d.2} ∈ E}`
  ——**只有边对，无孤立点自环**。
- **【原文】** Fan.lean:90 `dartOfFan V E = {d | d.1 = d.2 ∧ d.1 ∈ V ∧
  setOfEdge d.1 V E = ∅} ∪ dart1OfFan V E` —— HOL `darts_of_hyp` 的忠实镜像
  **已在树内**；Fan.lean:1082 `dartOfFan_eq_dart1_of_surrounded`（FAN + 每点
  度数 > 1 ⇒ 相等）说明作者清楚两者关系，但 `hypermapOfFan` 仍取 `dart1OfFan`。
- **【原文】** LA1:149-156 docstring 自认："on a fan the HYP kit's
  isolated-vertex self_pairs are absent … the residual HYP-layer bookkeeping
  is tracked by downstream obligations" —— 弱化是**有意的**，但下游义务
  至今无人接。
- **【原文】** FAN（Fan.lean:56）= `⋃₀E ⊆ V ∧ Graph E ∧ fan1 ∧ fan2 ∧ fan6 ∧
  fan7`：`⋃₀E ⊆ V` 允许 V 严格更大；fan7（边×孤立单点 case）要求
  `affGe{0} e ∩ affGe{0} {z} = affGe{0} ∅ = {0}`（ContraFan `affGe_0_empty`
  已证），即孤立点射线须避开全部边锥——**可满足但非平凡**（见 §3 实例讨论）。
- **【原文】** LocalAuto36.lean:592 `hyp_p4_of_fan_p36`：FAN 下 `hyp_p4 x V E =
  hypermapOfFan x V E hfan`；:601/:615 `localFan_p4 ↔ LocalFan` 双向已证
  —— **LA4 `_p4` 世界不解决孤立点问题**。
- **【原文】** 忠实世界存在且已架桥：AzimBridge（LA3 `_p3` HYP 层，
  `dartsOfHyp_p3 = ordPairs_p3 ∪ selfPairs_p3`）、LA2 `localFan_p2`、
  AzimBridge:859 `hno_of_no_isolated`（hedge ⇒ `dartsOfHyp_p3 = dart1OfFan`）、
  AzimBridge:941/:953/:959 `localFan_p3.of_LocalFan(_noIso)` / `localFan_p2.of_…
  （已真）。p2 世界内部已证「顶点在边上」：LA5:186 `LOCAL_FAN_RHO_NODE_PROS`
  （经 WRGCVDR_BIJ 级联转真）、LA5:875 `LOCAL_FAN_CHARACTER_OF_RHO_NODE`
  （`rhoNode1_p2 FF v ≠ v ∧ (v, rhoNode1_p2 FF v) ∈ ordPairs_p2 E ∧ ¬Collinear`）。

### 1.3 差异清单（LA1 锚 + HOL 锚）

| # | 差异 | LA1/Lean 锚 | HOL 锚 | 后果 |
|---|---|---|---|---|
| D1 | dart 集缺孤立点自环 | LA1:157 + Fan.lean:1169/:86 | localization.hl:40-44/:66 | junk 孤立顶点合法入 V；本报告全部下游 |
| D2 | `Generic` 用 affGt | LA1:121-122 | localization.hl:103（aff_ge） | 前提严格弱（B 级，见 §5） |
| D3 | `Circular` 用 affGt | LA1:117-118 | localization.hl:107（aff_gt） | **忠实，无病** |
| D4 | `_p4` 假 HYP 分支 | LA36:592 | （LA4 侧 dite 的 junk 支） | `_p4` 世界同 D1 |

（`rhoNode1`/`ivsRhoNode1`/`interiorAngle1`/`solLocal`/`wedgeInFanGe`/`azimInFan`
/`Dih2k`/`HasOrders` 各字段逐条对读忠实；问题只在 dart 底座与 `Generic`。）

## 2. 问2 —— 桩清单与受害面

前提形状：所有条目 hypothesis = LA1 弱编码（`LocalFan`/`ConvexLocalFan`）。
判定用语：**疑似假** = 给定含孤立点实例即机器反例（见 §3）；**需新前提** =
在弱编码下无证明路径（junk 分支不受任何约束），加 hedge 后恢复 HOL 可证性；
**免疫** = 陈述只触及 FF/边，或前提未使用。

### 2.1 LA7:1073-1128 块（9 枚，全 sorry）

| 定理（LA7 行 / HOL polar_fan.hl 行） | 判定 | 依据 |
|---|---|---|
| `RHO_NODE1_INJECTIVE`（:1073 / :318） | **疑似假（机器反例，§3 probeC）** | 2 无边顶点 ⇒ junk 相等 ∧ 顶点不等；HOL 证明经 `IVS_RHO_IDD`（MESON，:318-323） |
| `IVS_RHO_NODE1_IN_V`（:1079 / :325） | 需新前提 | junk ∈ V 无约束 |
| `LOCAL_FAN_ITER_IVS_RHO_NODE_IN_V`（:1084 / :330） | 需新前提 | 同上（迭代级联 junk） |
| `LOCAL_FAN_ORBIT_MAP_EXPLICIT`（:1090 / :336） | **疑似假** | junk 源点 ⇢ 真点的 ∃i 双向夹逼（§3 论证，probeC 同款手法） |
| `LOCAL_FAN_ORBIT_MAP_EXPLICIT_IVS`（:1096 / :360） | **疑似假** | 对偶同上 |
| `ITER_IVS_RHO_IDD`（:1102 / :381） | **疑似假（机器反例，§3 probeD）** | n=1 双点夹逼：空支 junk 共享强推 v1=v2；非空支 ε 返回真前驱 ≠ v1,v2 |
| `ITER_RHO_IVS_IDD`（:1108 / :392） | **疑似假** | 对偶同上 |
| `LOFA_IMP_ITER_IVS_RHO_NODE_ID`（:1114 / :402） | **疑似假** | n = V.ncard：空支双点夹逼；非空支真前驱轨道永不回到孤立点 |
| `GENERIC_LOCAL_FAN_AZIM_POS`（:1120 / :408） | 需新前提 | 前提 hia 对 junk v 不可满足式实例化；结论经 junk azim；凸世界 junk 可满足性未排除（§4b） |

### 2.2 LA7 其他（全 sorry）

- `FAN_PERIMETER_INVARIANT`（:1741）、`FAN_PERIMETER_INVARIANT_CARD_V`（:1749）、
  `FAN_PERIMETER`（:1757）、`WSEWPCH`（:1764）：需新前提——rhs/orbit 走
  `(rhoNode1 FF)^[i] v` over V，junk v 断轨。
- `BGMIFTE`（:1691，本体 sorry）：**结论 1/3**（`ConvexLocalFan V' E' FF'` +
  `V'.ncard = V.ncard`）疑似假/需新前提（junk v 的 `cross3 v (rhoNode1 FF v)`
  可产出坏极扇顶点；w5b 已标）；结论 2 外部锚阻塞（CIZMRRH/KCHMAMG）与本题
  无关；结论 4/5 的逐点形 kit（`p7w2_half_polar_arc`）**天然免疫**，但其装配
  清单第 (ii) 项 = `IVS_RHO_IDD` 逐点形（本表第 6 行），被本问题阻塞。
- 已闭合免疫件（w5b）：`LOCAL_FAN_NOT_EMPTY_FF`（:1211）、
  `LOCAL_FAN_NOT_CARD_FF_GE_2`（:1219）——只用 FF-orbit 内部事实 ✓。

### 2.3 跨文件（全 sorry，无已落地传染）

| 文件:行 | 定理形状 | 判定 |
|---|---|---|
| LA14:696 | `interiorAngle1 0 FF v = azimInFan (v, rhoNode1 FF v) E` | 需新前提（junk v 无 (v,ρv)∈FF） |
| LA14:704 / :715 | deformation ρ/ivs 等变 | 需新前提（image-FF 侧 junk 断链） |
| LA21:789 / :795 | `_h : LocalFan` 未使用，rfl 件 | 免疫 |
| LA25:182 等 | `_hlf` 未使用 | 免疫 |
| LA26:1205 | `ConvexLocalFan + Circular → solLocal E FF = 2π` | FF-事实形状，倾向无病【推断】 |
| LA31:872-936 | `LocalFan + Generic` + `(v,w1) ∈ FF` 件 | FF/dart 逐点形状，倾向无病【推断】 |
| LA35:1157 / :1171 | slice 面计数（face (v,ρv) 拆 FF） | 需新前提（证明需 V-orbit 覆盖 FF） |
| LA36:805 | `CARD_SLICE_EQ` 型 | 需新前提（同上） |
| LA37:214 | 边有二端点（Graph E） | 无病 |
| LA37:222 | `EDGE_IN_LOCAL_FAN_DET_RHO_NODE` | 需新前提 |
| LA37:398 | `{p \| ∃ v ∈ V, p = {v, rhoNode1 FF v}} = E` | **疑似假（最干净）**：孤立 v1 ⇒ `{v1, junk} ∈ LHS` 且无条件 `∉ E`，连 junk 碰撞都不需要 |
| LA36:601/:615/:646 | `LocalFan ↔ localFan_p4` 传输 | 免疫（纯传输） |

**传染裁决：已落库件零传染。** 全部受害者仍是 `sorry` 桩；SF 改陈述不碰任何
已证链。唯一陈述级消费已冻结进定义：`BBsV39`（LA1:413-417）第 4 合取用
`ConvexLocalFan (range vv) …`——定义不会"假"，但弱编码使 SCS 基本集类比 HOL
宽，`scs` 层保真度依赖 SF-B1 同步修复。

## 3. 问3 —— 机器反例试验（探针全绿，输出见 PROBE_OUTPUT.txt）

### 3.1 ε junk-collapse（关键新机器事实）

**【原文】** Lean v4.32.2 `Init/Classical.lean:96-110`：
```
strongIndefiniteDescription p h :=
  dite (∃x, p x) (fun hp => ⟨indefiniteDescription _ hp|.val, …⟩)
                 (fun hp => ⟨choice h, fun h => absurd h hp⟩)   -- 空分支值 = choice h（与 p 无关！）
epsilon p = (strongIndefiniteDescription p h).val
```
wsewpch-w5b DELIVERY 曾担心「ε 值不可控」；实测恰相反——**空谓词的 ε 值全部
等于同一个 `choice h`**，collapse 是定理：

```lean
-- probeB.lean (lake env lean, 0 error)
theorem probe_epsilon_collapse {α : Type} [Nonempty α] {p q : α → Prop}
    (hp : ∀ x, ¬ p x) (hq : ∀ x, ¬ q x) : Classical.epsilon p = Classical.epsilon q := by
  unfold Classical.epsilon Classical.strongIndefiniteDescription
  have h1 : ¬ (∃ x, p x) := by rintro ⟨x, hx⟩; exact hp x hx
  have h2 : ¬ (∃ x, q x) := by rintro ⟨x, hx⟩; exact hq x hx
  rw [dif_neg h1, dif_neg h2]
```

### 3.2 反例链四件（probeB.lean，全 0 error）

1. `probe_ff_subset_dart1`：`LocalFan V E FF → FF ⊆ dart1OfFan V E`
   （镜像 LA7 w5b 已证件的内核步：`orbitMap_subset_of_permutesOn` +
   coe 传输）。
2. `probe_predFF_empty`：无边顶点 v ⇒ `∀ w, (v,w) ∉ FF` ⇒ `rhoNode1 FF v` 是
   纯 junk。
3. `probe_RNI_witness`：`LocalFan` + `v1 ≠ v2` 均无边 ⇒
   `rhoNode1 FF v1 = rhoNode1 FF v2 ∧ rhoNode1 FF v2 = rhoNode1 FF v1 ∧
   v1 ≠ v2` —— `RHO_NODE1_INJECTIVE` 在 (v1,v2) 处双条件 LHS 真、RHS 假。
4. `probe_ITER_IVS_fail`：同一前提下 `¬(ivsRhoNode1 FF (rhoNode1 FF v1) = v1 ∧
   ivsRhoNode1 FF (rhoNode1 FF v2) = v2)`（n=1 的 `ITER_IVS_RHO_IDD` 双点
   夹逼：非空支 ε 给真前驱、其首分量 ≠ v1,v2；空支两边 collapse 到同一
   junk 强推 v1 = v2）。

复现：
```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean
lake env lean /tmp/la1-localfan-scout/probeB.lean   # 0 error
lake env lean /tmp/la1-localfan-scout/probeE.lean   # 0 error（见 §5）
```

### 3.3 唯一非机器环节：实例存在性【推断】

需要：`LocalFan V E FF` 且 V 含两个无边点。数学论证：
- 底座：真实 k-fan（如树内已证的 `CKQOWSA`：packing + annulus ⇒
  `FAN 0 V (ESTD V)`）加 `LocalFan` 的 dih2k 面结构（HOL 世界标准对象；
  树内无现成 `LocalFan` 实例，亦无任何已证 `LocalFan`-结论定理——见 §2.3）。
- 加孤立点 z：fan1/2/6 不受影响；fan7 的新 case 归结为
  `affGe{0} e ∩ ray(z) = {0}`（`affGe_0_empty` = {0}；`affGe {0} {z}` = 闭
  射线）——开稠密 genericity 条件（有限个薄锥不盖 ℝ³），可满足。
- dih2k 部分与 V 无关：`setOfEdge v V E` 的 `w ∈ V` 分量被 `⋃₀E ⊆ V` 吸收，
  `sigmaFan`/`fFanPair`/darts 全部不动，`LocalFan (insert z V) E FF` 沿
  同一见证成立。
结论：**SF 证据链闭合到「模一个标准 genericity 论证」**；即便实例存在性
最终不被单独机器验证，§2 的全部条目仍因「junk 分支无任何证明路径」而
不可原样填证——SF 的修复动作不变。

## 4. 问4 —— 修复路线对比

### (a) SF 加前提 `hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E`（推荐）

- 陈述变更清单：§2.1 九桩 + §2.2 FAN_PERIMETER 族 + BGMIFTE（结论 1/3 的
  证明输入）+ §2.3 表中「需新前提/疑似假」条目。hedge 前提下
  `localFan_p3.of_LocalFan_noIso`（AzimBridge:953，已真）一键桥入 p2/p3
  忠实世界，LA5 p2-kit（`LOCAL_FAN_RHO_NODE_PROS`/`LOCAL_FAN_CHARACTER_OF_
  RHO_NODE`/`WRGCVDR_BIJ` 等）直接可用——**修复=陈述对齐 + 现成管道**。
- 影响面：所有受害桩均为 sorry、零已证消费者 ⇒ 无涟漪；BGMIFTE 也未闭合。
  方向安全：前提变强 ⇒ 结论变弱 ⇒ 已有真件保持真。
- 与 HOL 等价性：HOL 侧这些引理的前提是 `local_fan`（内部含无孤立点），
  LA1 弱编码 + hedge 恰好 = HOL 前提类（local_lemmas.hl:1967 证明度数=2，
  hedge 是它的弱化形式，足够喂 AzimBridge 桥）。

### (b) 不动陈述、证 wedge-相交排除引理（不推荐）

- 只覆盖 ConvexLocalFan 前提的 2 处（LA7:1120、BGMIFTE 结论 1/3）；
  其余 7+9 枚 LocalFan 桩完全无援。
- HOL **不走此路**：HOL 的无孤立点来自 self-pairs + dih2k 计数
  （local_lemmas.hl:1967），与 wedge 无关。
- 实质性风险：凸世界中 junk 孤立点可能仍可满足——junk 须 ∈
  `⋂_{x∈FF} wedgeInFanGe x E` 且射线避开全部边锥；单面/窄扇构型下 ⋂wedge
  有内点，两个条件可同时满足【推断】——即该引理**可能根本是假的**。
  先花 ~100 行去证一个可疑命题不划算；如要走此路必须先做独立 mini-侦察。

### (c) 定义级修复（备选，不推荐本轮）

把 LA1 `LocalFan` 改量化到忠实 dart 底座（`dartOfFan` 已在 Fan.lean:90，
或直接挂 `localFan_p3`/`exists_hypHyp_of_fan`）。最忠实（逐字 HOL），
但 blast radius = 全部 16 个 LocalFan/ConvexLocalFan 消费文件的定义语义 +
`BBsV39` SCS 层，且 LA1 无法 import LA2（依赖方向）需搬定义。留作
「未来合并 LocalFan 孪生定义」大项的一部分。

### (d) 迁移 p2 世界（被阻塞）

LA7 不能 import 任何闭包含 LA2 的模块（`LOCAL_FAN_ORBIT_MAP_EXPLICIT`
同名冲突 LA2:1488 vs LA7:1090，w5b §8 已勘定）——除非 SF 同时处理改名，
本路线在 LA7 文件内不可行。注意：**改名与加前提可以打包成同一枚 SF**。

**传染核查结论**：无需抢救件。已落库且真证的 LocalFan 消费件
（w5b 两枚、LA36 传输、AzimBridge 桥、LA21/LA25 未用前提件）在两种
编码下同真。

## 5. 问5 —— B 级：`Generic`/`affGt` 与 LA2 `circular_p2`

### 5.1 LA1 `Generic`（LA1:121-122）

- **【原文】** HOL localization.hl:103：`generic V E <=> ∀ v w u. {v,w} ∈ E ∧
  u ∈ V ==> aff_ge {vec 0} {v,w} INTER aff_lt {vec 0} {u} = {}`。
- **【原文】** LA1:121：`∀ v w u, {v,w} ∈ E → u ∈ V → affGt {0} {v,w} ∩
  affLt {0} {u} = ∅` —— `affGt` 应为 `affGe`。
- 语义：`affGt ⊆ affGe`（严格：`0 ∈ affGe{0}{v}\affGt{0}{v}`，v ≠ 0，
  probeE 机器证）。前提类变大 ⇒ **消费定理前提偏弱 ⇒ 结论偏强 ⇒ 有假风险**
  （与「无害变弱」相反的危险方向）。
- 影响面：LA7 `BGMIFTE`/`GENERIC_LOCAL_FAN_AZIM_POS` 前提；LA14:732/774/785；
  LA31:872-936；`scsGeneric`（LA1:792 = `Generic (range v) (range edges)`）→
  LA18/22/23/25/26/27/29/33 全链 SCS 件（现均 pending）；`BBsV39`/`MMsV39`
  定义层。修复（affGt→affGe）使前提变强 = 安全方向，已证件不受影响。
- 另一动机：LA1 内 `Generic ↔ ¬Circular` 变成逐字否定（两边 affGt），
  而 HOL 是 `generic`(aff_ge) vs `circular`(aff_gt) 的**非对称对**
  （circular ⇒ ¬generic，反向不成立）——移植时被「对偶化」了，丢掉开/闭
  结构。
- **SF 草稿**：LA1:121 两处 `affGt`→`affGe`（仅 Generic 行；LA1:118 Circular
  行的 affGt 忠实勿动）。零已证消费者，无涟漪。

### 5.2 LA2 `circular_p2`（LA2:273）

- **【原文】** LA2:268 `generic_p2` 用 `affGe` ✓ 忠实；LA2:273 `circular_p2`
  用 `affGe` ✗（HOL :107 用 `aff_gt`）。镜像误差成立：w5b 判断正确。
- 后果：`circular_p2`（affGe 形）比 HOL `circular` 前提类大 ⇒ 消费者
  `KCHMAMG`（LA5:5018，sorry，BGMIFTE 结论 2 的外部锚之一）结论偏强有假
  风险；且 `circular_p2 ↔ ¬generic_p2` 恰好互否，再次丢失 HOL 的非对称
  开/闭结构。
- 消费点清单：LA6:473 `CVLF_COLLINEAR_CIRCULAR_LUNAR`（by_cases 平凡件，
  语义不变）；LA5:5018 `KCHMAMG`；`lunar_p2`（LA2:277 = `¬circular_p2 ∧ …`）
  定义内部一致，随 SF 同步收紧（lunar 前提变强 = 其消费者前提变强 = 安全）。
- **SF 草稿**：LA2:273 `affGe`→`affGt`（circular_p2 一处）；连带核查通过：
  LA6:473 平凡、KCHMAMG 安全向、lunar_p2 内部一致。

## 6. 给 W6a 的裁决（LA7:1073-1128 波）

**裁决：需先修陈述；按现陈述不可开填。**

- 按现陈述：7 枚不可证（junk 分支无证明路径）+ 至少 4 枚疑似假（§2.1 机器
  反例模实例存在性）+ LA37:398 无条件假——任何填证尝试都会产出假证或死循环。
- SF-2（加 hedge）拍板后：**可开**。施工路径 = 陈述替换（机械）→
  `localFan_p3.of_LocalFan_noIso`（AzimBridge:953 已真）桥入忠实世界 →
  消费 LA5 p2-kit + LA5 orbit engine（playbook §5.4：`la5_orbit_period`/
  `la5_iterate_mod` 已就位）→ HOL polar_fan.hl:318-430 逐条移植。
  ⚠ 同一 SF 建议附带处理 LA2:1488/LA7:1090 同名问题，否则 LA7 仍不能
  import 忠实世界，只能同文件重建 kit（可行但费）。
- SF 不批的退路：W6a 改道 p2 世界（放掉 LA7 文件内闭合的目标）或先攻
  wedge 引理（§4b 风险自负）。**不推荐无裁决开填。**

## 7. 地图信息（给后续波次）

- `Classical.epsilon` 空分支 junk 共享（`choice h`）是本 toolchain 的通用
  junk-审计事实：凡「ε 进几何构造」的桩，两个 junk-源可证相等——
  一句话反例模板已沉淀在 probeB.lean。
- `affGe {0} ∅ = {0}`（ContraFan `affGe_0_empty`）、`affGe {0} {v}` = 闭
  射线（`affGe_0_1_char`）——fan7 单点 case 与孤立点可满足性讨论的基石。
- `dartOfFan`（Fan.lean:90）+ `dartOfFan_eq_dart1_of_surrounded`（:1082）：
  定义级修复（§4c）的原料已备。
- `Exists_hypHyp_of_fan`（AzimBridge:578 附近）：任意 FAN 的忠实 HYP 超图
  构造器——若走 §4c/§4d，这是入口。
- 探针方法论：`unfold Classical.epsilon Classical.strongIndefiniteDescription`
  + `rw [dif_neg h1, dif_neg h2]` 两步才可 collapse（只 unfold epsilon 不够，
  dite 在内层 def 里）；probeB 亦给出 ε 侧 `epsilon_spec` 的 defeq-转写手法
  （`have hs' : (ivsRhoNode1 …, …) ∈ FF := hs`）。
