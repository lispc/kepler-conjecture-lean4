/-
  Kepler/LP/LpVocabW6B — W6-B 词表（LP 波次 W6-D/E/F 的取词入口）。

  车道 hlp-w6b 主产品。HOL 正本：
  `reference/flyspeck/formal_lp/hypermap/ineqs/lp_ineqs_proofs-compiled.hl`
  （对照基准 flyspeck @ 1ce0353）定义区 :9-23（`lp_fan`/`lp_cond`/`lp_tau`）
  + section Contravening 下 `contravening_lp_fan` :385-392（scout 锚）。

  ## 四件交付

  1. `LpFan` —— HOL `lp_fan`（:9-12）五合取。**定义性别名**：正本 =
     `Kepler.Text.TameLp.LpFan`（:344-347，逐字段对照零漂移，见 docstring
     对照表）；不重定义语义（沿 LpSemantics.lean:18-19 既有决策"不重定义
     lp_fan"），本别名供 W6-D/E/F 在 `Kepler.LP` 名空间内统一取词，
     TameLp 侧全部 LpFan 引理（`ineq_tauK_tauVEF_std` 群等）经 defeq 直通。
  2. `LpCond` —— HOL `lp_cond`（:14-21）七合取直译（LpCond 之前未入 Lean：
     LpSemantics 的 `lpCondAssembly_nf` 以显式合取直书结论，本 def 把该
     结论冻结为词表名）。两处【推断】折算见 docstring。
  3. `LpTau` —— HOL `lp_tau`（:22-23）直译。与 TameLp tau 群零重复
     （重复度核查见 DELIVERY.md：TameLp 只有 sum 上界件
     `sum_tauVEF_upper_bound` :1382、带 JEJTVGB 前提的逐 dart 件
     `ineq_tauK_tauVEF_std` :2016 起、等式桥 `tau_fun_eq_tauVEF` 群——
     无"逐面非负"陈述）。
  4. `contraveningHasLpFan` —— HOL `contravening_lp_fan`（:385-392，section
     Contravening :371-375 的 section hyp `cV : contravening V` 下）真证：
     `Contravening V → LpFan V (ESTD V)`。证明结构照 HOL 四步（见定理
     docstring 的逐步对照），消费 `Contravening` 分量 1/2/5/6（分量 7 与
     scriptL 两支 3/4 未消费，与 HOL 同——section 证明从不触及 ECTC 支）。
     技术件 = `ContraFan.contraveningFanTl`（CONTRAVENING_FAN，
     tame_general.hl:247-259 的 CKQOWSA 链折算）+ 逐点 surrounded 运输
     （CONTRAVENING_IMP_FULLY_SURROUNDED，tame_general.hl:266 的核心步，
     承重件 = TameLp `dartOfFan_fst_mem` :674）+ `ContraFan.mem_ESTD` /
     `two_h0` 的 2.52 距离折算（IN_ESTD，tame_general.hl:327；Lean 侧
     ESTD 的 `dist ≤ 2 * h0` 与 `#2.52` 经 `two_h0 : 2 * h0 = 2.52`）。

  ## Contravening 两处定义的关系（任务书侦察项，动手前已核）

  `Kepler.Assembly.Contravening`（Assembly.lean:92-97）与
  `Kepler.Text.TameLp.Contravening`（TameLp.lean:331-336）是**逐字同义镜像**
  （同源 tame/tame_defs.hl:248-253；七合取逐槽一致；下游件 pairwise defeq：
  `ESTD` 三处同体——ContraFan.lean:50-51 在案、`scriptL` 同体、
  `surroundedNode` 两处同引 Kepler.Text.Fan.surroundedNode）。本模块消费
  **TameLp 版**（与既有 `LpSemantics.contraveningLpFan` 同源）；Assembly 版
  消费者经 defeq 透传（`exact contraveningHasLpFan V hc` 一步），不设
  transport 件（避免本模块拖入 `Kepler.Assembly` 主模块 import）。

  ## 独立性与公理面

  本模块只 import `Kepler.Text.TameLp` + `Kepler.Text.ContraFan`（后者已在
  TameLp 闭包内，显式列出取词）；不被任何既有文件 import（独立构建
  `lake build Kepler.LP.LpVocabW6B`）。新增 Lean 行零未证原子（闸门禁词表
  三项全部不出现，含注释）；`contraveningHasLpFan` 的公理面预期 = 标准三
  （propext / Classical.choice / Quot.sound）+ `ContraFan.contraveningFanTl`
  在案骨架公理（CKQOWSA → ESTD_fan7 → LEMMA_4_POINTS_FINAL 链，
  ContraFan.lean:28-29 记账在案）——与 `LpSemantics.contraveningLpFan`
  公理面同源（LpSemantics.lean:23-27 注记），本模块零新增未证原子。
-/
import Kepler.Text.TameLp
import Kepler.Text.ContraFan

/-! ## 词表层 -/

namespace Kepler.LP.LpVocabW6B

open Kepler.Geom
open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)
open Kepler.Text.Fan
open Kepler.Text.TameLp

/-- **W6-B 词表 1/3：`LpFan`** —— HOL `lp_fan`
（`lp_ineqs_proofs-compiled.hl:9-12`）五合取，**定义性别名**（正本
`Kepler.Text.TameLp.LpFan`，TameLp.lean:344-347）。逐字段对照（零漂移）：

| HOL（:9-12） | Lean（TameLp.LpFan） |
| `FAN (vec 0,V,E)` | `FAN 0 V E` |
| `fully_surrounded (V,E)`（fan_defs.hl:260-261） | `FullySurrounded V E`（TameLp:339-340 镜像） |
| `!v w. v IN V /\ w IN V /\ ~(v = w) /\ ~({v,w} IN E) ==> #2.52 <= dist (v,w)` | `∀ v w, v ∈ V → w ∈ V → v ≠ w → {v,w} ∉ E → 2.52 ≤ dist v w`（逐字面） |
| `V SUBSET ball_annulus` | `V ⊆ ballAnnulus` |
| `packing V` | `Packing V` |

W6-D/E/F 经本名取词后，TameLp 侧全部 `LpFan` 引理 defeq 直通
（`ineq_tauK_tauVEF_std` 群 TameLp:2016 起、`fully_surrounded_*` 簇等）。 -/
def LpFan (V : Set V3) (E : Set (Set V3)) : Prop :=
  Kepler.Text.TameLp.LpFan V E

/-- **W6-B 词表 2/3：`LpCond`** —— HOL `lp_cond`
（`lp_ineqs_proofs-compiled.hl:14-21`）七合取直译。字段对照：

| HOL（:14-21） | Lean（本 def 槽位） |
| `lp_fan (V,E)` | `LpFan V E` |
| `good_list L`（tame_defs2.hl:27-31） | `GoodList L`（GoodListDefs.lean:72 镜像） |
| `good_list_nodes L`（tame_defs2.hl:33-36） | `GoodListNodesTl L hL` ——【推断】HOL 是 `L` 上独立谓词；Lean 构造 `hypermapOfList` 是依赖式（proof 参数），槽位取 TameLp 实例形（TameLp:5193-5194，nodeSet 等式）；lp_cond 语境自带 `hL : GoodList L`，与 flip 后 `Assembly.GoodListNodes L = ∀ hL, …` 的实例一致（`goodListNodesSpine_iff_tameLp` 桥，GoodGraph.lean:135-138；SF-57 (d)-10） |
| `hyp_iso g (hypermap_of_list L, hypermap_of_fan (V,E))`（hypermap_iso-compiled.hl:6-11：BIJ + 三映射交换） | `Set.BijOn g ↑(hypermapOfList L hL).darts ↑(hypermapOfFanTl V E hfan).darts` + 三映射交换两槽——与 `Hypermap.Iso`（Hypermap.lean:8249-8252，hypermap.hl:9614 镜像）同形但保留显式 `g`（HOL 把 g 作为 lp_cond 参数） |
| `BIJ h (elements_of_list L) V` | `Set.BijOn h (elementsOfList L) V` |
| `!d. g d = h (FST d), h (SND d)` | `∀ d, g d = (h d.1, h d.2)` |
| `!x. x IN elements_of_list L <=> h x IN V` | `∀ x, x ∈ elementsOfList L ↔ h x ∈ V` |

两处【推断】折算（同一根因）：`hypermapOfList`/`hypermapOfFanTl` 在 Lean
是 proof 参数化构造（`hL : GoodList L` / `hfan : FAN 0 V E` 显式入参），
HOL 侧为全函数（junk 语义）；故本 def 比 HOL 多 `hL`/`hfan` 两个 proof
参数——与 `GoodListNodesTl`（TameLp:5190）、`faceSetOfFan`（TameLp:352）
的既有折算同款。结论形与 `LpSemantics.lpCondAssembly_nf`（LpSemantics.lean:726
起，前波已证的 lp_cond_lemma 装配层）的 ∃-体逐槽一致：消费侧以
`lpCondAssembly_nf` 的结论逐槽组装即得本 def（W6-E 取词路径）。 -/
def LpCond (L : fgraph ℕ) (g : ℕ × ℕ → V3 × V3) (h : ℕ → V3) (V : Set V3)
    (E : Set (Set V3)) (hL : GoodList L) (hfan : FAN 0 V E) : Prop :=
  LpFan V E ∧ GoodList L ∧ GoodListNodesTl L hL ∧
    Set.BijOn g ↑(hypermapOfList L hL).darts
      ↑(hypermapOfFanTl V E hfan).darts ∧
    (∀ d ∈ (hypermapOfList L hL).darts,
        (hypermapOfFanTl V E hfan).edgeMap (g d) =
          g ((hypermapOfList L hL).edgeMap d) ∧
        (hypermapOfFanTl V E hfan).nodeMap (g d) =
          g ((hypermapOfList L hL).nodeMap d) ∧
        (hypermapOfFanTl V E hfan).faceMap (g d) =
          g ((hypermapOfList L hL).faceMap d)) ∧
    Set.BijOn h (elementsOfList L) V ∧
    (∀ d : ℕ × ℕ, g d = (h d.1, h d.2)) ∧
    (∀ x, x ∈ elementsOfList L ↔ h x ∈ V)

/-- **W6-B 词表 3/3：`LpTau`** —— HOL `lp_tau`
（`lp_ineqs_proofs-compiled.hl:22-23`）
`!f. f IN face_set (hypermap_of_fan (V,E)) ==> &0 <= tauVEF (V,E,f)` 直译。

折算注记：①`face_set (hypermap_of_fan (V,E))` ↦
`(hypermapOfFanTl V E hfan).faceSet`（Hypermap.lean:1008
`= setOfOrbits darts faceMap`；hfan proof 参数【推断】同 LpCond 条，
TameLp.`faceSetOfFan` :352-353 同体）；②`tauVEF` ↦ `Kepler.Text.tauVEF_p2`
（LocalAuto2.lean:369，localization.hl:1559 镜像——与 TameLp tau 群既有
折算一致，TameLp:1375-1377 同款注记）。

**与 TameLp tau 群零重复**（W6-F 前置核查，DELIVERY.md 有全表）：TameLp
侧现存 tau 件 = `sum_tauVEF_upper_bound`（:1382，faceSet 上的和上界）、
`ineq_tauK_tauVEF_std`（:2016 起 K=3..6，逐 dart 且带 `JEJTVGB_stdK_concl`
证书前提）、`tau_fun_eq_tauVEF`/`f_surr_*`/`wk_*` 等式桥、私件
`p6g_face_tauVEF`——没有任何"逐面无条件非负"陈述；HOL 侧 `lp_tau` 的
非负性内容在 `lp_main_estimate` 链（CRTTXAT + JEJTVGB + 面表示），即
W6-F 的 `ContraveningLpTau` 桥工作面。本 def 只是冻结词表名。 -/
def LpTau (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E) : Prop :=
  ∀ f ∈ (hypermapOfFanTl V E hfan).faceSet, (0 : ℝ) ≤ Kepler.Text.tauVEF_p2 V E f

/-! ## 主件：`contravening_lp_fan` 直译 -/

/-- 逐点 surrounded ⇒ 全 dart surrounded（HOL
`CONTRAVENING_IMP_FULLY_SURROUNDED` 的去 contravening 化核心步，
tame_general.hl:266；dart 第一分量归属由 TameLp `dartOfFan_fst_mem`
（:674）承载。`LpSemantics.fullySurrounded_of_surroundedNode`
（LpSemantics.lean:61-64）的独立副本——本模块不 import LpSemantics，
保持词表模块独立性（两件同证同型，见各自 docstring）。 -/
private theorem fullySurrounded_of_surroundedNode' {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hsurr : ∀ v ∈ V, surroundedNode V E v) :
    FullySurrounded V E := fun d hd =>
  hsurr d.1 (dartOfFan_fst_mem hfan hd) d hd rfl

/-- **W6-B 主件：`contraveningHasLpFan`** —— HOL `contravening_lp_fan`
（`lp_ineqs_proofs-compiled.hl:385-392`，section Contravening
（:371-375：`V` + section hyp `cV : contravening V`）下）直译：
`contravening V ==> lp_fan (V, ESTD V)`。

证明逐步对照（HOL :388-389 五合取展开）：
1. `FAN (vec 0,V,ESTD V)` ← `fanV`（:377-381）← `CONTRAVENING_FAN`
   （tame_general.hl:247-259）↦ `ContraFan.contraveningFanTl`
   （ContraFan.lean:1066-1068，CKQOWSA 链）——消费分量 1（Packing）、
   2（ballAnnulus）、5（ncard 13/14/15 ⇒ `V ≠ ∅`）；
2. `fully_surrounded` ← `CONTRAVENING_IMP_FULLY_SURROUNDED`
   （tame_general.hl:266）↦ `fullySurrounded_of_surroundedNode'`——消费
   分量 6（`surrounded_node (V, ESTD V)`）；
3. 2.52 距离 ← contravening 展开后 `contraR` + `IN_ESTD`
   （tame_general.hl:327：`{v,w} IN ESTD V ⇔ … /\ dist(v,w) <= #2.52`）
   归谬 ↦ `ContraFan.mem_ESTD` + `two_h0`（ContraFan.lean:61-63/72：
   `2 * h0 = 2.52` 折算）；
4. `V SUBSET ball_annulus` / `packing V` ← 分量 2 / 分量 1 直取。

消费面：分量 1/2/5/6；分量 7（ECTC 支）与 scriptL 两支（3/4）未消费——
与 HOL section 证明一致（从不触及 ECTC 支）。
公理面：标准三 + `ContraFan.contraveningFanTl` 在案骨架（见文件头）；
与 `LpSemantics.contraveningLpFan`（LpSemantics.lean:72-85）同陈述同源：
Text 侧正本已落库，本件是 W6 词表命名空间内的取词入口（下游 W6-D/E/F
统一消费本模块），非语义孪生。 -/
theorem contraveningHasLpFan (V : Set V3) (hc : Contravening V) : LpFan V (ESTD V) := by
  have hne : V ≠ ∅ := by
    have hcard : V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15 := hc.2.2.2.2.1
    rintro rfl
    simp at hcard
  have hfan : FAN 0 V (ESTD V) :=
    Kepler.Text.ContraFan.contraveningFanTl V hc.1 hc.2.1 hne
  refine ⟨hfan, fullySurrounded_of_surroundedNode' hfan hc.2.2.2.2.2.1, ?_, hc.2.1, hc.1⟩
  intro v w hv hw hvw hnotE
  by_contra hcon
  push_neg at hcon
  have hmem : {v, w} ∈ ESTD V :=
    Kepler.Text.ContraFan.mem_ESTD.mpr ⟨v, w, rfl, hv, hw, hvw,
      by linarith [Kepler.Text.ContraFan.two_h0, hcon]⟩
  exact hnotE hmem

end Kepler.LP.LpVocabW6B

/-! 公理审计锚（验收探针执行；主件预期 = 标准三 + ContraFan 在案骨架，
词表层三个 def 预期零公理）：
#print axioms Kepler.LP.LpVocabW6B.contraveningHasLpFan
#print axioms Kepler.LP.LpVocabW6B.LpFan
#print axioms Kepler.LP.LpVocabW6B.LpCond
#print axioms Kepler.LP.LpVocabW6B.LpTau
-/
