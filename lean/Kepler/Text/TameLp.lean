/-
  Kepler.Text.TameLp — formal_lp/hypermap 桥章（KCBLRQC / BDJYFFB / CRTTXAT /
  JGTDEBU / SZIPOAS / CDTETAT 群 + `lp_fan` 支撑件）的定理陈述层移植。
  填实状态：JGTDEBU 全组 + CDTETAT/SZIPOAS + KCBLRQC/BDJYFFB1/BDJYFFB2
  已真证明；sum_tauVEF_upper_bound 已于 2026-10-23 真证明（§3b kit：
  confV 桥 + ConformingAuto6.SUM_SOL_IN_FACE_SET_EQ_4PI + 前向阻塞副本
  五件 + 纯算术装配）；剩余 sorry = fully_surrounded_perimeter_bound /
  ineq_tauK_tauVEF_std 群（各依赖未移植深章，见 §8 债务图与原位 NEEDS
  注记）。CRTTXAT 已于 2026-10-12 第二波真证明（arc kit 五件套
  自证 + face_sum_snd_eq_fst 鸽笼换元，见 §7/§7c）。

  依赖清单来源：`text_formalization/tame/ssreflect/MQMSMAB-compiled.hl`
  头部 needs（lp_ineqs_proofs / lp_main_estimate / CDTETAT / KCBLRQC）+
  证明体 use_arg_then2 名单（:32-81）。

  战略位置：HOL 装配链
    MQMSMAB（tame_concl）⇐ KCBLRQC/BDJYFFB（tame/ssreflect/KCBLRQC-compiled.hl）
      ⇐ CDTETAT/SZIPOAS（tame/CDTETAT.hl）⇐ JGTDEBU 群（tame/JGTDEBU.hl）
      ⇐ lp_fan / contravening_lp_fan（formal_lp/hypermap/ineqs/lp_ineqs_proofs-compiled.hl）
      ⇐ COMPONENTS_HYPERMAP_OF_FAN（fan/hypermap_and_fan.hl:495）
    CRTTXAT（tame/CRTTXAT.hl，tame_9a 出口）与 sum_tauVEF_upper_bound
      （tame/ssreflect/tame_lemmas-compiled.hl:529）为同章并列支撑。

  命名约定：定理名保留 HOL 原名（大写 ID）；原语 def 与 Assembly §2b 同形者
  在文档注释标注"Assembly §2b 同形"。复用（不重定义）：`Kepler.Text.dTame`/
  `Kepler.Text.tgt`（LocalAuto1.lean:198-206，与 tame_defs.hl:81-107 同值表）、
  `Kepler.Text.Plain/Planar/Simple/Connected/EdgeNondegenerate/IsNoDoubleJoins`
  （Hypermap.lean，hypermap.hl 定义层）、`Kepler.Text.tauVEF_p2`（LocalAuto2.lean:354，
  localization.hl:1559 `tauVEF`）、`Kepler.Text.lp_main_estimate`
  （LocalAuto16.lean:185，JEJTVGB.hl:232）、`Kepler.Text.setSum`（PackingAuto2.lean:124，
  有限支撑折算，Assembly §2b `setSumSpec` 同形）。

  纪律：本模块不 import `Kepler.Assembly`（会环）；全部 sorry 为骨架占位，
  无新增 axiom、无 native_decide。
-/
import Kepler.Text.Hypermap
import Kepler.Text.Fan
import Kepler.Assembly.GoodListDefs
import Kepler.Text.TopologyFan
import Kepler.Text.PackingAuto2
import Kepler.Text.LocalAuto2
import Kepler.Text.LocalAuto16
import Kepler.Geom.AzimLemmas
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto1
import Kepler.Text.ConformingAuto21
import Kepler.Text.ConformingAuto23
import Kepler.Text.ContraFan
import Kepler.Text.ConformingAuto6
import Kepler.Geom.LuneVolume

namespace Kepler.Text.TameLp

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ### 0a. `hypermapOfFan` 的 dartDecEq2 重标（AzimBridge.hypermap_toDart 同构；
AzimBridge.lean:64-72 实例注记：`hypermapOfFan` 结果类型被烤定为
`instDecidableEqProd` 实例，而 import 链带入的全局实例 `dartDecEq2`
（LocalAuto2.lean:81）为 instance synthesis 所偏好——点投影必须发生在
重标后的项上。重标无损（Hypermap 结构字段不含实例）。 -/

/-- HOL `hypermap_of_fan (vec 0, V, E)`（fan_defs.hl/fan.hl）在本模块的
标准形态：`hypermapOfFan` 的 dartDecEq2 重标版。本文件所有桥定理的
`hypermap_of_fan` 均指此项；与 Assembly §2c 直接使用的裸
`hypermapOfFan 0 V (ESTD V) hfan` 为同一超映射（仅实例标签不同）。 -/
noncomputable def hypermapOfFanTl (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E) :
    Hypermap (V3 × V3) :=
  @Hypermap.mk (V3 × V3) dartDecEq2
    (@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b) (hypermapOfFan 0 V E hfan))
    (@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b) (hypermapOfFan 0 V E hfan))
    (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b) (hypermapOfFan 0 V E hfan))
    (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b) (hypermapOfFan 0 V E hfan))
    (@Hypermap.edgeMap_permutes (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan))
    (@Hypermap.nodeMap_permutes (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan))
    (@Hypermap.faceMap_permutes (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan))
    (@Hypermap.comp_eq_one (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan))

/-! ### 0b. 重标转移（AzimBridge.hypermap_toDart 同型）：`hypermapOfFanTl`
与 `hypermapOfFan` 的结构字段逐项相同；`Planar`/`Connected`/`Simple` 等
谓词仅经字段投影定义，但 dot 投影的实例合成在两侧分别烤定为 `dartDecEq2` /
`instDecidableEqProd`（AzimBridge.lean:64-72 注记），故转移经显式实例
congruence 完成。 -/
section RelabelCongr
variable {V : Set V3} {E : Set (Set V3)} {hfan : FAN 0 V E}

/-- 字段级 rfl 桥（AzimBridge.toDart_darts 同型）。 -/
theorem dartsTl_eq : @Hypermap.darts (V3 × V3) dartDecEq2 (hypermapOfFanTl V E hfan) =
    @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := rfl

theorem edgeMapTl_eq : @Hypermap.edgeMap (V3 × V3) dartDecEq2 (hypermapOfFanTl V E hfan) =
    @Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := rfl

theorem nodeMapTl_eq : @Hypermap.nodeMap (V3 × V3) dartDecEq2 (hypermapOfFanTl V E hfan) =
    @Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := rfl

theorem faceMapTl_eq : @Hypermap.faceMap (V3 × V3) dartDecEq2 (hypermapOfFanTl V E hfan) =
    @Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := rfl

end RelabelCongr

/-! ### 0c. 实例参数 congruence：`Hypermap` 的谓词对实例参数不敏感
（字段投影不使用实例；isPath 归纳收口）。 -/
section InstCongr
variable {α : Type*} {i1 i2 : DecidableEq α} {A : @Hypermap α i1} {B : @Hypermap α i2}

theorem isPath_congr_inst (he : @Hypermap.edgeMap α i1 A = @Hypermap.edgeMap α i2 B)
    (hn : @Hypermap.nodeMap α i1 A = @Hypermap.nodeMap α i2 B)
    (hf : @Hypermap.faceMap α i1 A = @Hypermap.faceMap α i2 B)
    (p : ℕ → α) (n : ℕ) :
    @Hypermap.isPath α i1 A p n ↔ @Hypermap.isPath α i2 B p n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show @Hypermap.isPath α i1 A p k ∧ _ ↔ @Hypermap.isPath α i2 B p k ∧ _
    refine and_congr ih ?_
    show @Hypermap.goOneStep α i1 A (p k) (p (k + 1)) ↔
      @Hypermap.goOneStep α i2 B (p k) (p (k + 1))
    unfold Hypermap.goOneStep
    rw [he, hn, hf]

theorem combComponent_congr_inst
    (he : @Hypermap.edgeMap α i1 A = @Hypermap.edgeMap α i2 B)
    (hn : @Hypermap.nodeMap α i1 A = @Hypermap.nodeMap α i2 B)
    (hf : @Hypermap.faceMap α i1 A = @Hypermap.faceMap α i2 B) (x : α) :
    @Hypermap.combComponent α i1 A x = @Hypermap.combComponent α i2 B x := by
  unfold Hypermap.combComponent Hypermap.isInComponent
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, n, h1, h2, h3⟩
    exact ⟨p, n, h1, h2, (isPath_congr_inst he hn hf p n).mp h3⟩
  · rintro ⟨p, n, h1, h2, h3⟩
    exact ⟨p, n, h1, h2, (isPath_congr_inst he hn hf p n).mpr h3⟩

theorem setOfComponents_congr_inst
    (hd : @Hypermap.darts α i1 A = @Hypermap.darts α i2 B)
    (he : @Hypermap.edgeMap α i1 A = @Hypermap.edgeMap α i2 B)
    (hn : @Hypermap.nodeMap α i1 A = @Hypermap.nodeMap α i2 B)
    (hf : @Hypermap.faceMap α i1 A = @Hypermap.faceMap α i2 B) :
    @Hypermap.setOfComponents α i1 A = @Hypermap.setOfComponents α i2 B := by
  unfold Hypermap.setOfComponents Hypermap.setPartComponents
  ext S
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, (combComponent_congr_inst he hn hf x).symm⟩
    show x ∈ @Hypermap.darts α i2 B
    rw [← hd]
    exact hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, combComponent_congr_inst he hn hf x⟩
    show x ∈ @Hypermap.darts α i1 A
    rw [hd]
    exact hx

theorem numberOfNodes_congr_inst
    (hd : @Hypermap.darts α i1 A = @Hypermap.darts α i2 B)
    (hn : @Hypermap.nodeMap α i1 A = @Hypermap.nodeMap α i2 B) :
    @Hypermap.numberOfNodes α i1 A = @Hypermap.numberOfNodes α i2 B := by
  show (@Hypermap.nodeSet α i1 A).ncard = (@Hypermap.nodeSet α i2 B).ncard
  have h1 : @Hypermap.nodeSet α i1 A = @Hypermap.nodeSet α i2 B := by
    unfold Hypermap.nodeSet
    rw [hd, hn]
  rw [h1]

theorem numberOfEdges_congr_inst
    (hd : @Hypermap.darts α i1 A = @Hypermap.darts α i2 B)
    (he : @Hypermap.edgeMap α i1 A = @Hypermap.edgeMap α i2 B) :
    @Hypermap.numberOfEdges α i1 A = @Hypermap.numberOfEdges α i2 B := by
  show (@Hypermap.edgeSet α i1 A).ncard = (@Hypermap.edgeSet α i2 B).ncard
  have h1 : @Hypermap.edgeSet α i1 A = @Hypermap.edgeSet α i2 B := by
    unfold Hypermap.edgeSet
    rw [hd, he]
  rw [h1]

theorem numberOfFaces_congr_inst
    (hd : @Hypermap.darts α i1 A = @Hypermap.darts α i2 B)
    (hf : @Hypermap.faceMap α i1 A = @Hypermap.faceMap α i2 B) :
    @Hypermap.numberOfFaces α i1 A = @Hypermap.numberOfFaces α i2 B := by
  show (@Hypermap.faceSet α i1 A).ncard = (@Hypermap.faceSet α i2 B).ncard
  have h1 : @Hypermap.faceSet α i1 A = @Hypermap.faceSet α i2 B := by
    unfold Hypermap.faceSet
    rw [hd, hf]
  rw [h1]

theorem numberOfComponents_congr_inst
    (hd : @Hypermap.darts α i1 A = @Hypermap.darts α i2 B)
    (he : @Hypermap.edgeMap α i1 A = @Hypermap.edgeMap α i2 B)
    (hn : @Hypermap.nodeMap α i1 A = @Hypermap.nodeMap α i2 B)
    (hf : @Hypermap.faceMap α i1 A = @Hypermap.faceMap α i2 B) :
    @Hypermap.numberOfComponents α i1 A = @Hypermap.numberOfComponents α i2 B := by
  show (@Hypermap.setOfComponents α i1 A).ncard =
      (@Hypermap.setOfComponents α i2 B).ncard
  rw [setOfComponents_congr_inst hd he hn hf]

theorem Planar_congr_inst
    (hd : @Hypermap.darts α i1 A = @Hypermap.darts α i2 B)
    (he : @Hypermap.edgeMap α i1 A = @Hypermap.edgeMap α i2 B)
    (hn : @Hypermap.nodeMap α i1 A = @Hypermap.nodeMap α i2 B)
    (hf : @Hypermap.faceMap α i1 A = @Hypermap.faceMap α i2 B) :
    @Hypermap.Planar α i1 A ↔ @Hypermap.Planar α i2 B := by
  show (@Hypermap.numberOfNodes α i1 A + @Hypermap.numberOfEdges α i1 A +
      @Hypermap.numberOfFaces α i1 A = (@Hypermap.darts α i1 A).card +
        2 * @Hypermap.numberOfComponents α i1 A) ↔
    (@Hypermap.numberOfNodes α i2 B + @Hypermap.numberOfEdges α i2 B +
      @Hypermap.numberOfFaces α i2 B = (@Hypermap.darts α i2 B).card +
        2 * @Hypermap.numberOfComponents α i2 B)
  rw [numberOfNodes_congr_inst hd hn, numberOfEdges_congr_inst hd he,
    numberOfFaces_congr_inst hd hf, hd,
    numberOfComponents_congr_inst hd he hn hf]

theorem Connected_congr_inst
    (hd : @Hypermap.darts α i1 A = @Hypermap.darts α i2 B)
    (he : @Hypermap.edgeMap α i1 A = @Hypermap.edgeMap α i2 B)
    (hn : @Hypermap.nodeMap α i1 A = @Hypermap.nodeMap α i2 B)
    (hf : @Hypermap.faceMap α i1 A = @Hypermap.faceMap α i2 B) :
    @Hypermap.Connected α i1 A ↔ @Hypermap.Connected α i2 B := by
  show (@Hypermap.numberOfComponents α i1 A = 1) ↔
    (@Hypermap.numberOfComponents α i2 B = 1)
  rw [numberOfComponents_congr_inst hd he hn hf]

theorem Simple_congr_inst
    (hd : @Hypermap.darts α i1 A = @Hypermap.darts α i2 B)
    (he : @Hypermap.edgeMap α i1 A = @Hypermap.edgeMap α i2 B)
    (hn : @Hypermap.nodeMap α i1 A = @Hypermap.nodeMap α i2 B)
    (hf : @Hypermap.faceMap α i1 A = @Hypermap.faceMap α i2 B) :
    @Hypermap.Simple α i1 A ↔ @Hypermap.Simple α i2 B := by
  unfold Hypermap.Simple
  constructor
  · intro h x hx
    have hmem : x ∈ @Hypermap.darts α i1 A := by rw [hd]; exact hx
    have hn' : @Hypermap.node α i2 B x = @Hypermap.node α i1 A x := by
      show orbitMap (@Hypermap.nodeMap α i2 B) x =
        orbitMap (@Hypermap.nodeMap α i1 A) x
      rw [hn]
    have hf' : @Hypermap.face α i2 B x = @Hypermap.face α i1 A x := by
      show orbitMap (@Hypermap.faceMap α i2 B) x =
        orbitMap (@Hypermap.faceMap α i1 A) x
      rw [hf]
    show @Hypermap.node α i2 B x ∩ @Hypermap.face α i2 B x = {x}
    rw [hn', hf']
    exact h x hmem
  · intro h x hx
    have hmem : x ∈ @Hypermap.darts α i2 B := by rw [← hd]; exact hx
    have hn' : @Hypermap.node α i1 A x = @Hypermap.node α i2 B x := by
      show orbitMap (@Hypermap.nodeMap α i1 A) x =
        orbitMap (@Hypermap.nodeMap α i2 B) x
      rw [hn]
    have hf' : @Hypermap.face α i1 A x = @Hypermap.face α i2 B x := by
      show orbitMap (@Hypermap.faceMap α i1 A) x =
        orbitMap (@Hypermap.faceMap α i2 B) x
      rw [hf]
    show @Hypermap.node α i1 A x ∩ @Hypermap.face α i1 A x = {x}
    rw [hn', hf']
    exact h x hmem

end InstCongr

/-- `hypermapOfFan` 上的 Simple 转 `hypermapOfFanTl`（实例 congruence）。 -/
theorem SimpleTl {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    (h : @Hypermap.Simple (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan)) :
    @Hypermap.Simple (V3 × V3) dartDecEq2 (hypermapOfFanTl V E hfan) :=
  (Simple_congr_inst dartsTl_eq edgeMapTl_eq nodeMapTl_eq faceMapTl_eq).mpr h

/-- `hypermapOfFan` 上的 Planar 转 `hypermapOfFanTl`（实例 congruence）。 -/
theorem PlanarTl {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    (h : @Hypermap.Planar (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan)) :
    @Hypermap.Planar (V3 × V3) dartDecEq2 (hypermapOfFanTl V E hfan) :=
  (Planar_congr_inst dartsTl_eq edgeMapTl_eq nodeMapTl_eq faceMapTl_eq).mpr h

/-- `hypermapOfFan` 上的 Connected 转 `hypermapOfFanTl`（实例 congruence）。 -/
theorem ConnectedTl {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    (h : @Hypermap.Connected (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan)) :
    @Hypermap.Connected (V3 × V3) dartDecEq2 (hypermapOfFanTl V E hfan) :=
  (Connected_congr_inst dartsTl_eq edgeMapTl_eq nodeMapTl_eq faceMapTl_eq).mpr h

/-- HOL `SIMPLE_HYPERMAP_IMP_FACE_INJ`（hypermap_and_fan.hl:1823）：
Simple 超映射中同一 node 轨道上 face 单射。HOL 证明展开 simple_hypermap
后由 `a ∈ face b ∩ node b = {b}` 收口；此处经 `orbitMap_eq_of_mem`
（node 轨道等价）同构落地。 -/
theorem faceInjOn_of_node {α : Type*} [DecidableEq α] {H : Hypermap α}
    (hsimple : H.Simple) (x : α) (hx : x ∈ H.darts) :
    Set.InjOn (fun y => H.face y) (H.node x) := by
  intro a ha b hb hface
  have h1 : H.node a = H.node x := orbitMap_eq_of_mem H.nodeMap_permutes ha
  have h2 : H.node b = H.node x := orbitMap_eq_of_mem H.nodeMap_permutes hb
  have hab : a ∈ H.node b := by rw [h2, ← h1]; exact H.mem_node_self a
  have hfaceb : a ∈ H.face b := by
    have hface' : H.face a = H.face b := hface
    rw [← hface']
    exact H.mem_face_self a
  have hbb : b ∈ H.darts := H.node_subset_darts hx hb
  have hsimp := hsimple b hbb
  have hmem : a ∈ H.node b ∩ H.face b := ⟨hab, hfaceb⟩
  rw [hsimp] at hmem
  exact Set.mem_singleton_iff.mp hmem

/-! ## 1. 原语定义层（忠实镜像，无 sorry） -/

/-- HOL `ESTD`（`tame/tame_defs.hl:191-192`）。Assembly §2b 同形
（Assembly.lean §1 `ESTD`）。 -/
def ESTD (V : Set V3) : Set (Set V3) :=
  {e | ∃ v w : V3, e = {v, w} ∧ v ∈ V ∧ w ∈ V ∧ v ≠ w ∧ dist v w ≤ 2 * h0}

/-- HOL `ECTC`（`tame/tame_defs.hl:194-195`）。Assembly §2b 同形。 -/
def ECTC (V : Set V3) : Set (Set V3) :=
  {e | ∃ v w : V3, e = {v, w} ∧ v ∈ V ∧ w ∈ V ∧ v ≠ w ∧ dist v w = 2}

/-- HOL `scriptL`（`tame/tame_defs.hl:245-246`）；`sum` 的无限支撑折算同
Assembly §1 `scriptL`（`lmfun` 复用 PackingAuto2.lean:464）。 -/
noncomputable def scriptL (V : Set V3) : ℝ :=
  if h : V.Finite then Finset.sum h.toFinset (fun v => lmfun (‖v‖ / 2)) else 0

/-- HOL `contravening`（`tame/tame_defs.hl:248-253`）逐句镜像；折算注记同
Assembly §1 `Contravening`（`packing` ↦ `Kepler.Packing`、`ball_annulus` ↦
`Kepler.Text.ballAnnulus`、`CARD` ↦ `Set.ncard`、`surrounded_node` ↦
`Kepler.Text.Fan.surroundedNode`）。 -/
def Contravening (V : Set V3) : Prop :=
  Packing V ∧ V ⊆ ballAnnulus ∧ scriptL V > 12 ∧
    (∀ W : Set V3, Packing W → W ⊆ ballAnnulus → scriptL W ≤ scriptL V) ∧
    (V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15) ∧
    (∀ v ∈ V, surroundedNode V (ESTD V) v) ∧
    (∀ v ∈ V, surroundedNode V (ECTC V) v ∨ ‖v‖ = 2)

/-- HOL `fully_surrounded`（`fan/fan_defs.hl:260-261`）。 -/
def FullySurrounded (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ x ∈ dartOfFan V E, azimDart V E x < Real.pi

/-- HOL `lp_fan`（`formal_lp/hypermap/ineqs/lp_ineqs_proofs-compiled.hl:9-12`）
逐合取项镜像。 -/
def LpFan (V : Set V3) (E : Set (Set V3)) : Prop :=
  FAN 0 V E ∧ FullySurrounded V E ∧
    (∀ v w : V3, v ∈ V → w ∈ V → v ≠ w → {v, w} ∉ E → 2.52 ≤ dist v w) ∧
    V ⊆ ballAnnulus ∧ Packing V

/-- HOL `face_set_of_fan`（`tame/tame_defs.hl:235-236`）。
偏差注记：HOL `hypermap_of_fan` 全函数；Lean `hypermapOfFan`
proof-parameterized（Assembly §1b `FanHypermapIsoList` 同一折算）。 -/
noncomputable def faceSetOfFan (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E) :
    Set (Set (V3 × V3)) := (hypermapOfFanTl V E hfan).faceSet

/-- HOL `perimeterbound`（`tame/tame_defs.hl:295-297`）；`arcV` 复用
`Kepler.Geom.LuneVolume.arcV`（sphere.hl:375 镜像）。`hfan` 参数偏差同上。 -/
def PerimeterBound (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E) : Prop :=
  ∀ f ∈ faceSetOfFan V E hfan, setSum f (fun d => arcV 0 d.1 d.2) ≤ 2 * Real.pi

/-- HOL `darts_k`（`formal_lp/hypermap/ssreflect/list_hypermap-compiled.hl:19`）。 -/
def dartsK {α : Type*} [DecidableEq α] (k : ℕ) (H : Hypermap α) : Set α :=
  {d | d ∈ H.darts ∧ (H.face d).ncard = k}

/-! ### 1a. node / face 组合原语（tame_defs.hl:39-130；Assembly §2b 同形，
轨道取 `Hypermap.node/face`（Hypermap.lean:840-846，与 Assembly §2b
`orbitSet` 版本点态等价）） -/

/-- HOL `no_loops`（`tame_defs.hl:39-40`，tame_4）。 -/
def NoLoops {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop :=
  ∀ x y, x ∈ H.edge y → x ∈ H.node y → x = y

/-- HOL `exceptional_face`（`tame_defs.hl:44`）。 -/
def ExceptionalFace {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) : Prop :=
  5 ≤ (H.face x).ncard

/-- HOL `set_of_triangles_meeting_node`（`tame_defs.hl:46-48`）。 -/
def setOfTrianglesMeetingNode {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    Set (Set α) :=
  {F | ∃ y ∈ H.darts, F = H.face y ∧ (H.face y).ncard = 3 ∧ y ∈ H.node x}

/-- HOL `set_of_quadrilaterals_meeting_node`（`tame_defs.hl:50-52`）。 -/
def setOfQuadrilateralsMeetingNode {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    Set (Set α) :=
  {F | ∃ y ∈ H.darts, F = H.face y ∧ (H.face y).ncard = 4 ∧ y ∈ H.node x}

/-- HOL `set_of_exceptional_meeting_node`（`tame_defs.hl:54-56`）。 -/
def setOfExceptionalMeetingNode {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    Set (Set α) :=
  {F | ∃ y ∈ H.darts, F = H.face y ∧ 5 ≤ (H.face y).ncard ∧ y ∈ H.node x}

/-- HOL `set_of_face_meeting_node`（`tame_defs.hl:58-60`）。 -/
def setOfFaceMeetingNode {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    Set (Set α) :=
  {F | ∃ y ∈ H.darts, F = H.face y ∧ y ∈ H.node x}

/-- HOL `type_of_node`（`tame_defs.hl:62-66`）；`CARD` ↦ `Set.ncard`。 -/
noncomputable def typeOfNode {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    ℕ × ℕ × ℕ :=
  ((setOfTrianglesMeetingNode H x).ncard,
    (setOfQuadrilateralsMeetingNode H x).ncard,
    (setOfExceptionalMeetingNode H x).ncard)

/-- HOL `node_type_exceptional_face`（`tame_defs.hl:68-70`）。 -/
def NodeTypeExceptionalFace {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) : Prop :=
  ExceptionalFace H x ∧ (H.node x).ncard = 6 → typeOfNode H x = (5, 0, 1)

/-- HOL `node_exceptional_face`（`tame_defs.hl:72-74`）。 -/
def NodeExceptionalFace {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) : Prop :=
  ExceptionalFace H x → (H.node x).ncard ≤ 6

/-- HOL `a_tame`（`tame_defs.hl:110`）。 -/
noncomputable def aTame : ℝ := 0.63

/-- HOL `b_tame`（`tame_defs.hl:81-100`；表值与 Assembly §2b `bTame` 一致）。 -/
noncomputable def bTame : ℕ → ℕ → ℝ := fun p q =>
  if p = 0 ∧ q = 3 then 0.618 else if p = 0 ∧ q = 4 then 0.97 else
    if p = 1 ∧ q = 2 then 0.656 else if p = 1 ∧ q = 3 then 0.618 else
      if p = 2 ∧ q = 1 then 0.797 else if p = 2 ∧ q = 2 then 0.412 else
        if p = 2 ∧ q = 3 then 1.2851 else if p = 3 ∧ q = 1 then 0.311 else
          if p = 3 ∧ q = 2 then 0.817 else if p = 4 ∧ q = 0 then 0.347 else
            if p = 4 ∧ q = 1 then 0.366 else if p = 5 ∧ q = 0 then 0.04 else
              if p = 5 ∧ q = 1 then 1.136 else if p = 6 ∧ q = 0 then 0.686 else
                if p = 7 ∧ q = 0 then 1.450 else tgt

/-- HOL `total_weight`（`tame_defs.hl:112-113`）；`sum` ↦ `setSum`
（有限支撑折算，Assembly §2b `totalWeight` 同形）。 -/
noncomputable def totalWeight {α : Type*} [DecidableEq α] (H : Hypermap α)
    (w : Set α → ℝ) : ℝ := setSum H.faceSet w

/-- HOL `adm_1`（`tame_defs.hl:115-116`）。 -/
def Adm1 {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  ∀ x ∈ H.darts, dTame (H.face x).ncard ≤ w (H.face x)

/-- HOL `adm_2`（`tame_defs.hl:118-122`）。 -/
def Adm2 {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  ∀ x ∈ H.darts, (setOfExceptionalMeetingNode H x).ncard = 0 →
    bTame (setOfTrianglesMeetingNode H x).ncard
        (setOfQuadrilateralsMeetingNode H x).ncard ≤
      setSum (setOfFaceMeetingNode H x) w

/-- HOL `adm_3`（`tame_defs.hl:124-127`，`a_tame = 0.63` 已内联为 `aTame`）。
注：此处为忠实原形；Assembly §2b `Adm3` 是标明的形状占位（`True` 尾）。 -/
def Adm3 {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  ∀ x ∈ H.darts, typeOfNode H x = (5, 0, 1) →
    aTame ≤ setSum (setOfTrianglesMeetingNode H x) w

/-- HOL `admissible_weight`（`tame_defs.hl:129-130`）。 -/
def AdmissibleWeight {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  Adm1 H w ∧ Adm2 H w ∧ Adm3 H w

/-! ### 1b. tame 谓词层（tame_defs.hl:136-184；Assembly §2b 同形。
plain/planar/connected/simple/edge-nondegenerate/no-double-joins 复用
`Hypermap.Plain/Planar/Simple/Connected/EdgeNondegenerate/IsNoDoubleJoins`
（Hypermap.lean:1050-1071,9081；hypermap.hl:182-197 与 tame_defs 折算一致）。 -/

/-- HOL `tame_1`（`tame_defs.hl:136-138`）。 -/
def Tame1 {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop := H.Plain ∧ H.Planar
/-- HOL `tame_2`（`tame_defs.hl:140-142`）。 -/
def Tame2 {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop := H.Connected ∧ H.Simple
/-- HOL `tame_3`（`tame_defs.hl:144`）。 -/
def Tame3 {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop := H.EdgeNondegenerate
/-- HOL `tame_4`（`tame_defs.hl:146`）。 -/
def Tame4 {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop := NoLoops H
/-- HOL `tame_5a`（`tame_defs.hl:148`）。 -/
def Tame5a {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop := H.IsNoDoubleJoins
/-- HOL `tame_8`（`tame_defs.hl:153-154`）。 -/
def Tame8 {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop := 3 ≤ H.numberOfFaces
/-- HOL `tame_9a`（`tame_defs.hl:156-158`）。 -/
def Tame9a {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop :=
  ∀ x ∈ H.darts, 3 ≤ (H.face x).ncard ∧ (H.face x).ncard ≤ 6
/-- HOL `tame_10`（`tame_defs.hl:160-162`）。 -/
def Tame10 {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop :=
  H.numberOfNodes = 13 ∨ H.numberOfNodes = 14 ∨ H.numberOfNodes = 15
/-- HOL `tame_11a`（`tame_defs.hl:164-166`）。 -/
def Tame11a {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop :=
  ∀ x ∈ H.darts, 3 ≤ (H.node x).ncard
/-- HOL `tame_11b`（`tame_defs.hl:168-170`）。 -/
def Tame11b {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop :=
  ∀ x ∈ H.darts, (H.node x).ncard ≤ 7
/-- HOL `tame_12o`（`tame_defs.hl:172-174`）。 -/
def Tame12o {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop :=
  ∀ x ∈ H.darts, NodeTypeExceptionalFace H x ∧ NodeExceptionalFace H x
/-- HOL `tame_13a`（`tame_defs.hl:176-178`）。 -/
def Tame13a {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop :=
  ∃ w, AdmissibleWeight H w ∧ totalWeight H w < tgt

/-- HOL `tame_planar_hypermap`（`tame_defs.hl:180-184`）。Assembly §2b
`TamePlanarHypermap` 同形。 -/
def TamePlanarHypermap {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop :=
  Tame1 H ∧ Tame2 H ∧ Tame3 H ∧ Tame4 H ∧ Tame5a H ∧ Tame8 H ∧ Tame9a H ∧
    Tame10 H ∧ Tame11a H ∧ Tame11b H ∧ Tame12o H ∧ Tame13a H

/-- CDTETAT :155-160 结论中的 20 个容许 `(p, q+r)` 对
（`CDTETAT_lemma1` :44-46 的集合字面量；置于 §1 供 `KcblrqcIneqDef`
表切片引用）。 -/
def cdTetatPairs : List (ℕ × ℕ) :=
  [(0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3),
    (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1),
    (6, 0), (6, 1), (7, 0)]

/-- HOL `kcblrqc_ineq_def`（`tame/ssreflect/tame_lemmas-compiled.hl:34-46`，
Ineq 数据库机器大合取）的**本章消费切片**折算。CDTETAT / KCBLRQC /
BDJYFFB1/2 从 `kcblrqc_ineq_def` 抽取的全部事实为四类：
1. 两条 azim 边界——`TRIANGULAR_FACE_AZIM_DART_BOUNDS`（tame_general.hl:739-746，
   机器 ineq `5735387903`/`5490182221`）与 `non_triangular_face_azim_dart_bound`
   （ssreflect/tame_lemmas-compiled.hl:895-918，机器 `DIH_Y_INEQ`）的结论形；
2. `get_b_tame_ineq` 表（KCBLRQC.vhl `lp_data`）r = 0 情形：20 个 node-type
   `(p, q, 0)`（`(p, q) ∈ cdTetatPairs`）给 `b_tame p q ≤ sum
   (set_of_face_meeting_node H d) tauVEF`（内含 `lp_main_estimate` 消费）；
3. 同表 6 个 r > 0 node-type（`(6,0,1)/(3,0,3)/(3,1,2)/(3,2,1)/(4,0,2)/(4,1,1)`）
   的机器不等式组合为数值矛盾（如 `5.8218 ≤ 5.4742…`），折算为 `False`；
4. 同表 type `(5,0,1)` 行给三角形 tauVEF 和 `≥ 0.6366`（精确数值
   `0.626·6.28319 − 0.7199 − 3.85 = 0.63662…`；BDJYFFB2 消费）。
真化依赖 G4 证书数据库；Assembly §1c 同名占位（`True`）独立维持，两处
接口在 G4 落地后统一。 -/
def KcblrqcIneqDef : Prop :=
  (∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)) (y : V3 × V3), Contravening V →
      y ∈ dartOfFan V (ESTD V) →
      (((hypermapOfFanTl V (ESTD V) hfan).face y).ncard = 3 →
          (0.852:ℝ) < azimDart V (ESTD V) y ∧ azimDart V (ESTD V) y < 1.893) ∧
        (3 < ((hypermapOfFanTl V (ESTD V) hfan).face y).ncard →
          (1.15:ℝ) < azimDart V (ESTD V) y)) ∧
  (∀ (hmain : lp_main_estimate) (V : Set V3) (hfan : FAN 0 V (ESTD V)),
      Contravening V → ∀ d ∈ dartOfFan V (ESTD V), ∀ p q : ℕ, (p, q) ∈ cdTetatPairs →
        typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d = (p, q, 0) →
        bTame p q ≤ setSum (setOfFaceMeetingNode (hypermapOfFanTl V (ESTD V) hfan) d)
          (fun f => tauVEF_p2 V (ESTD V) f)) ∧
  (∀ (hmain : lp_main_estimate) (V : Set V3) (hfan : FAN 0 V (ESTD V)),
      Contravening V → ∀ d ∈ dartOfFan V (ESTD V),
        typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d ∈
          [(6, 0, 1), (3, 0, 3), (3, 1, 2), (3, 2, 1), (4, 0, 2), (4, 1, 1)] → False) ∧
  (∀ (hmain : lp_main_estimate) (V : Set V3) (hfan : FAN 0 V (ESTD V)),
      Contravening V → ∀ d ∈ dartOfFan V (ESTD V),
        typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d = (5, 0, 1) →
        (0.6366:ℝ) ≤ setSum {f | f ∈ setOfFaceMeetingNode
            (hypermapOfFanTl V (ESTD V) hfan) d ∧ f.ncard = 3}
          (fun f => tauVEF_p2 V (ESTD V) f))
/-! ## 2. hypermap_of_fan 的 dart 层展开（hypermap_and_fan 组） -/

/-- HOL `COMPONENTS_HYPERMAP_OF_FAN`（`fan/hypermap_and_fan.hl:495-499`）的
Lean 折算形：dart 集等式 + e/n/f 三映射在 dart 上逐点等于
`e/n/f_fan_pair`。偏差注记：HOL 结论第一项 `dart (hypermap_of_fan (V,E)) =
dart_of_fan (V,E)`；Lean `hypermapOfFan` 的 dart 集按构造为
`dart1_of_fan`（不含孤立 dart `(v,v)`，Assembly §1b 注记），孤立点情形
`dart_of_fan = dart1_of_fan ∪ {(v,v)}` 在 contravening 语境（无孤立点）下
重合。 -/
theorem COMPONENTS_HYPERMAP_OF_FAN (V : Set V3) (E : Set (Set V3))
    (hfan : FAN 0 V E) :
    (↑(hypermapOfFanTl V E hfan).darts : Set (V3 × V3)) = dart1OfFan V E ∧
      ∀ d ∈ dart1OfFan V E,
        (hypermapOfFanTl V E hfan).edgeMap d = eFanPair V E d ∧
        (hypermapOfFanTl V E hfan).nodeMap d = nFanPair 0 V E d ∧
        (hypermapOfFanTl V E hfan).faceMap d = fFanPair 0 V E d := by
  refine ⟨(finite_dart1_fan hfan).coe_toFinset, fun d hd => ?_⟩
  have hmem : d ∈ (finite_dart1_fan hfan).toFinset :=
    (Set.Finite.mem_toFinset (finite_dart1_fan hfan)).mpr hd
  simp only [hypermapOfFanTl, hypermapOfFan, extendPerm, Equiv.ofBijective_apply]
  exact ⟨if_pos hmem, if_pos hmem, if_pos hmem⟩

/-! ### 2b. dart 层展开（hypermap_of_fan 组支撑件；本节及后续 `hypermapOfFanTl`
各映射在 `dart1OfFan` 上的点态形态由 `COMPONENTS_HYPERMAP_OF_FAN` 给出；
轨道外恒等由 `hypermapOfFan` 的 `extendPerm`/`res` 构造直接读出。 -/
section DartLayer
variable {V : Set V3} {E : Set (Set V3)} {hfan : FAN 0 V E}

/-- dart 集（Set 折算）。 -/
theorem dartsTl_coe :
    (↑(hypermapOfFanTl V E hfan).darts : Set (V3 × V3)) = dart1OfFan V E :=
  (COMPONENTS_HYPERMAP_OF_FAN V E hfan).1

/-- dart 集成员（Finset 形）。 -/
theorem mem_dartsTl {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    d ∈ (hypermapOfFanTl V E hfan).darts :=
  (finite_dart1_fan hfan).mem_toFinset.mpr hd

/-- dart 集成员 → dart1。 -/
theorem dartsTl_mem {d : V3 × V3} (hd : d ∈ (hypermapOfFanTl V E hfan).darts) :
    d ∈ dart1OfFan V E := by
  have : d ∈ (↑(hypermapOfFanTl V E hfan).darts : Set (V3 × V3)) := hd
  rwa [dartsTl_coe] at this

/-- `edgeMap` 在 dart1 上 = `eFanPair`。 -/
theorem edgeMapTl_apply {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFanTl V E hfan).edgeMap d = eFanPair V E d :=
  ((COMPONENTS_HYPERMAP_OF_FAN V E hfan).2 d hd).1

/-- `nodeMap` 在 dart1 上 = `nFanPair`。 -/
theorem nodeMapTl_apply {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFanTl V E hfan).nodeMap d = nFanPair 0 V E d :=
  ((COMPONENTS_HYPERMAP_OF_FAN V E hfan).2 d hd).2.1

/-- `faceMap` 在 dart1 上 = `fFanPair`。 -/
theorem faceMapTl_apply {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFanTl V E hfan).faceMap d = fFanPair 0 V E d :=
  ((COMPONENTS_HYPERMAP_OF_FAN V E hfan).2 d hd).2.2

/-- 轨道外恒等（e/n/f 三映射；`extendPerm` 的 `res` 构造）。 -/
theorem edgeMapTl_of_notMem {d : V3 × V3} (hd : d ∉ dart1OfFan V E) :
    (hypermapOfFanTl V E hfan).edgeMap d = d := by
  simp only [hypermapOfFanTl, hypermapOfFan, extendPerm, Equiv.ofBijective_apply]
  exact if_neg (fun hmem => hd (by simpa using hmem))

theorem nodeMapTl_of_notMem {d : V3 × V3} (hd : d ∉ dart1OfFan V E) :
    (hypermapOfFanTl V E hfan).nodeMap d = d := by
  simp only [hypermapOfFanTl, hypermapOfFan, extendPerm, Equiv.ofBijective_apply]
  exact if_neg (fun hmem => hd (by simpa using hmem))

/-- edge-轨道的显式形态：iterates 只在 `{d, eFanPair d}` 中取值。 -/
theorem edgeMapTl_iterate (d : V3 × V3) (hd : d ∈ dart1OfFan V E) (k : ℕ) :
    (hypermapOfFanTl V E hfan).edgeMap^[k] d = d ∨
      (hypermapOfFanTl V E hfan).edgeMap^[k] d = eFanPair V E d := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rcases ih with h | h
    · rw [Function.iterate_succ_apply', h, edgeMapTl_apply hd]
      exact Or.inr rfl
    · have hmem : eFanPair V E d ∈ dart1OfFan V E := eFanPair_mem_dart1 hd
      rw [Function.iterate_succ_apply', h, edgeMapTl_apply hmem, eFanPair_sq d hd]
      exact Or.inl rfl

/-- node-轨道的显式形态：`(nodeMap^[k]) (v,w) = (v, σ_v^[k] w)`
（HOL `NODE_HYPERMAP_OF_FAN` 的 iterate 形）。 -/
theorem nodeMapTl_iterate {d : V3 × V3} (hd : d ∈ dart1OfFan V E) (k : ℕ) :
    (hypermapOfFanTl V E hfan).nodeMap^[k] d =
      (d.1, (sigmaFan 0 V E d.1)^[k] d.2) := by
  have hmem : ∀ j : ℕ, (d.1, (sigmaFan 0 V E d.1)^[j] d.2) ∈ dart1OfFan V E := by
    intro j
    simp only [dart1OfFan, Set.mem_setOf_eq]
    have he : {d.1, d.2} ∈ E := hd
    exact (properties_of_setOfEdge_fan 0 V E d.1 _ hfan).mpr
      (image_power_map_points (x := 0) hfan he j)
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, nodeMapTl_apply (hmem k), nFanPair,
      Function.iterate_succ_apply']

/-- node-轨道各点仍在 dart1（`nodeMapTl_iterate` 的成员性部分）。 -/
theorem nodeIterateTl_mem {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    {d : V3 × V3} (hd : d ∈ dart1OfFan V E) (k : ℕ) :
    (d.1, (sigmaFan 0 V E d.1)^[k] d.2) ∈ dart1OfFan V E := by
  simp only [dart1OfFan, Set.mem_setOf_eq]
  have he : {d.1, d.2} ∈ E := hd
  exact (properties_of_setOfEdge_fan 0 V E d.1 _ hfan).mpr
    (image_power_map_points (x := 0) hfan he k)

/-- 轨道外 iterates 恒等（任一映射）。 -/
theorem iterate_of_notMemTl {d : V3 × V3} (hd : d ∉ dart1OfFan V E) (k : ℕ)
    (f : (V3 × V3) → (V3 × V3)) (hf : ∀ z, z ∉ dart1OfFan V E → f z = z) :
    (f^[k]) d = d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hf d hd]

end DartLayer

/-! ### 2c. surrounded 计数组（hypermap_and_fan.hl:542/2155/2255 twins +
tame_general.hl `contravening_imp_conforming` 的 Lean 折算） -/
section SurroundedCount
variable {V : Set V3} {E : Set (Set V3)}

/-- HOL `DART_EXISTS`（hypermap_and_fan.hl:542）。 -/
theorem DART_EXISTS_TL (hfan : FAN 0 V E) (v : V3) (hv : v ∈ V) :
    ∃ w : V3, (v, w) ∈ dartOfFan V E := by
  by_cases hsoe : setOfEdge v V E = ∅
  · refine ⟨v, Set.mem_union_left _ ?_⟩
    show (v, v).1 = (v, v).2 ∧ (v, v).1 ∈ V ∧ setOfEdge (v, v).1 V E = ∅
    exact ⟨rfl, hv, hsoe⟩
  · obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hsoe
    exact ⟨w, Set.mem_union_right _ ((properties_of_setOfEdge_fan 0 V E v w hfan).mpr hw)⟩

/-- dart 的第一分量在 V 中（`dartOfFan` 两分支逐条）。 -/
theorem dartOfFan_fst_mem (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dartOfFan V E) :
    d.1 ∈ V := by
  rcases (Set.mem_union d _ _).mp hd with h | h
  · exact h.2.1
  · exact (FAN_in_setOfEdge 0 V E d.1 d.2 hfan h).1

/-- HOL `SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3`（hypermap_and_fan.hl:2155）：
surrounded 顶点的边集至少三元。HOL 证明经 SUM_AZIM_DART +
SUM_BOUND_LT_ALT；此处用 `sum_azims_eq_2pi`（TopologyFan，绕圈角和 = 2π）
+ surrounded 的逐 dart 严格上界 `< π`，对 `ncard ≤ 2` 归谬。 -/
theorem SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL (hfan : FAN 0 V E) {v : V3}
    (hv : v ∈ V) (hsurr : surroundedNode V E v) :
    3 ≤ (setOfEdge v V E).ncard := by
  by_contra hcon
  push_neg at hcon
  -- 取 dart (v,w)
  obtain ⟨w, hw⟩ := DART_EXISTS_TL hfan v hv
  have hs : azimDart V E (v, w) < Real.pi := hsurr (v, w) hw rfl
  have hvw : v ≠ w := by
    intro heq
    subst heq
    have h2pi : azimDart V E (v, v) = 2 * Real.pi := by simp [azimDart]
    rw [h2pi] at hs
    linarith [Real.pi_pos]
  have hd1 : (v, w) ∈ dart1OfFan V E := by
    rcases (Set.mem_union _ _ _).mp hw with h | h
    · exact absurd h.out.1 hvw
    · exact h
  have hwE : {v, w} ∈ E := hd1
  have hw_soe : w ∈ setOfEdge v V E := (properties_of_setOfEdge_fan 0 V E v w hfan).mp hwE
  by_cases hsingle : setOfEdge v V E = {w}
  · -- 唯一邻居：azim_dart = 2π ≮ π
    have hnc : (setOfEdge v V E).ncard = 1 := by rw [hsingle, Set.ncard_singleton]
    have h2pi : azimDart V E (v, w) = 2 * Real.pi := by
      simp only [azimDart, if_neg hvw]
      show (if (setOfEdge v V E).ncard > 1 then
          azim 0 v w (sigmaFan 0 V E v w) else 2 * Real.pi) = 2 * Real.pi
      exact if_neg (show ¬((setOfEdge v V E).ncard > 1) from by rw [hnc]; omega)
    linarith [Real.pi_pos]
  · -- ncard = 2：绕圈角和 2π = 两项各 < π 之和，矛盾
    have h2 : (setOfEdge v V E).ncard = 2 := by
      have hle := two_le_ncard_of_ne hfan hwE hsingle
      omega
    have hsum := sum_azims_eq_2pi (x := 0) hfan hwE hsingle
    rw [h2, Finset.sum_range_succ, Finset.sum_range_one] at hsum
    -- 两项角增量各等于 azimDart 且 < π
    have hu1 : (sigmaFan 0 V E v)^[1] w ∈ setOfEdge v V E :=
      iterates_mem_setOfEdge hfan v w hw_soe 1
    have hvne1 : v ≠ (sigmaFan 0 V E v)^[1] w :=
      edge_ne_of_fan hfan ((properties_of_setOfEdge_fan 0 V E v _ hfan).mpr hu1)
    have hmem1 : (v, (sigmaFan 0 V E v)^[1] w) ∈ dart1OfFan V E :=
      (properties_of_setOfEdge_fan 0 V E v _ hfan).mpr hu1
    have hlt1 : azimDart V E (v, (sigmaFan 0 V E v)^[1] w) < Real.pi :=
      hsurr _ (Set.mem_union_right _ hmem1) rfl
    have hgt : (setOfEdge v V E).ncard > 1 := by rw [h2]; decide
    have hdrt : ∀ u : V3, v ≠ u → azimDart V E (v, u) = azimFan 0 V E v u := by
      intro u hne
      show (if (v, u).1 = (v, u).2 then 2 * Real.pi else azimFan 0 V E (v, u).1 (v, u).2) =
        azimFan 0 V E v u
      rw [if_neg hne]
    have e0 : azimIfan 0 V E v w 0 = azimDart V E (v, w) := by
      show azim 0 v w (sigmaFan 0 V E v w) = azimDart V E (v, w)
      rw [hdrt w hvw]
      show azim 0 v w (sigmaFan 0 V E v w) =
        if (setOfEdge v V E).ncard > 1 then
          azim 0 v w (sigmaFan 0 V E v w) else 2 * Real.pi
      rw [if_pos hgt]
    have e1 : azimIfan 0 V E v w 1 = azimDart V E (v, (sigmaFan 0 V E v)^[1] w) := by
      show azim 0 v ((sigmaFan 0 V E v)^[1] w)
          (sigmaFan 0 V E v ((sigmaFan 0 V E v)^[1] w)) =
        azimDart V E (v, (sigmaFan 0 V E v)^[1] w)
      rw [hdrt _ hvne1]
      show azim 0 v ((sigmaFan 0 V E v)^[1] w)
          (sigmaFan 0 V E v ((sigmaFan 0 V E v)^[1] w)) =
        if (setOfEdge v V E).ncard > 1 then
          azim 0 v ((sigmaFan 0 V E v)^[1] w)
            (sigmaFan 0 V E v ((sigmaFan 0 V E v)^[1] w)) else 2 * Real.pi
      rw [if_pos hgt]
    rw [e0, e1] at hsum
    linarith

/-- node-轨道的集合形态：`node H d = (d.1, ·) '' setOfEdge d.1 V E`
（HOL `NODE_HYPERMAP_OF_FAN` + `FAN_NODE_EQ_lemma` 的核心）。 -/
theorem nodeTl_eq_image (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFanTl V E hfan).node d = (fun y => (d.1, y)) '' setOfEdge d.1 V E := by
  ext y
  constructor
  · intro hy
    have hy' : ∃ k : ℕ, ((hypermapOfFanTl V E hfan).nodeMap ^ k) d = y := by
      simpa [Hypermap.node, orbitMap] using hy
    obtain ⟨k, hk⟩ := hy'
    rw [Equiv.Perm.coe_pow, nodeMapTl_iterate hd] at hk
    show y ∈ (fun y => (d.1, y)) '' setOfEdge d.1 V E
    exact (Set.mem_image (fun y => (d.1, y)) (setOfEdge d.1 V E) y).mpr
      ⟨(sigmaFan 0 V E d.1)^[k] d.2, image_power_map_points (x := 0) hfan hd k, hk⟩
  · intro hy
    obtain ⟨z, hz, rfl⟩ := (Set.mem_image (fun y => (d.1, y)) (setOfEdge d.1 V E) y).mp hy
    have hzo : z ∈ setOfOrbitsPointsFan 0 V E d.1 d.2 := by
      rw [orbit_eq_setOfEdge hfan hd]
      exact hz
    obtain ⟨k, hk⟩ := hzo
    rw [Hypermap.node, orbitMap, Set.mem_setOf_eq]
    refine ⟨k, ?_⟩
    rw [Equiv.Perm.coe_pow, nodeMapTl_iterate hd, ← hk]

/-- HOL `SURROUNDED_IMP_CARD_NODE_GE_3`（hypermap_and_fan.hl:2255）：
surrounded 顶点的节点轨道至少三元。 -/
theorem SURROUNDED_IMP_CARD_NODE_GE_3_TL (hfan : FAN 0 V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) (hsurr : surroundedNode V E d.1) :
    3 ≤ ((hypermapOfFanTl V E hfan).node d).ncard := by
  rw [nodeTl_eq_image hfan hd,
    Set.InjOn.ncard_image (fun a _ b _ h => congrArg Prod.snd h)]
  exact SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan
    (FAN_in_setOfEdge 0 V E d.1 d.2 hfan hd).1 hsurr

end SurroundedCount


/-! ## 3. lp_fan 支撑件（formal_lp/hypermap/ineqs 组） -/

/-- HOL `CONTRAVENING_FAN`（tame_general.hl:247-259）的忠实 twin：
`(V, ESTD V)` 是 fan。
真证明 2026-09-21（T3 波）：CKQOWSA 章已移植为 `Kepler.Text.ContraFan`
（18 条定理 16 条真证明；仅两个深几何核 LEMMA_3_POINTS_FINAL ~1300 行/
LEMMA_4_POINTS_FINAL ~3800 行为骨架陈述，见 ContraFan.lean DISCHARGES）。
`ESTD` 同体 defeq，`V ≠ ∅` 由 card 合取项（13/14/15）推出。
注：Assembly.lean §2c `contraveningFan`（:444）为同一债务的接口占位。 -/
theorem contravening_fanTl (V : Set V3) (hc : Contravening V) :
    FAN 0 V (ESTD V) := by
  have hne : V ≠ ∅ := by
    have hcard : V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15 := hc.2.2.2.2.1
    rintro rfl
    simp at hcard
  exact ContraFan.contraveningFanTl V hc.1 hc.2.1 hne

/-- HOL `contravening_lp_fan` 的 FAN-前提形（lp_ineqs_proofs-compiled.hl
section Contravening 的 `fanV` 显式化）：除 `CONTRAVENING_FAN` 一步外逐合取
落地——fully_surrounded（`CONTRAVENING_IMP_FULLY_SURROUNDED`，经
`contravening` 的 surrounded 合取 + dart 第一分量归属）+ 2.52 算术
（`IN_ESTD`：dist ≤ 2*h0 = 2.52 + 归谬）。 -/
theorem contravening_lp_fan_of_fan (V : Set V3) (hfan : FAN 0 V (ESTD V))
    (hc : Contravening V) : LpFan V (ESTD V) := by
  have hfs : FullySurrounded V (ESTD V) := fun d hd =>
    hc.2.2.2.2.2.1 d.1 (dartOfFan_fst_mem hfan hd) d hd rfl
  refine ⟨hfan, hfs, ?_, hc.2.1, hc.1⟩
  intro v w hv hw hvw hne
  by_contra hcon
  push_neg at hcon
  have h20 : (2 : ℝ) * h0 = 2.52 := by norm_num [h0]
  exact hne ⟨v, w, rfl, hv, hw, hvw, by linarith⟩

/-- HOL `contravening_lp_fan`（`lp_ineqs_proofs-compiled.hl:385-400`，
section `Contravening` finalized 形）。
HOL 证明 4 步（lp_fan 展开 + fanV/CONTRAVENING_FAN +
CONTRAVENING_IMP_FULLY_SURROUNDED + IN_ESTD 算术）；后三步由
`contravening_lp_fan_of_fan` 真证明落地，FAN 合取项经
`contravening_fanTl`（ContraFan.lean，T3 波真化）闭合。 -/
theorem contravening_lp_fan (V : Set V3) (hc : Contravening V) :
    LpFan V (ESTD V) :=
  contravening_lp_fan_of_fan V (contravening_fanTl V hc) hc

/-- HOL `fully_surrounded_perimeter_bound`（`lp_main_estimate-compiled.hl:1530-1543`，
section PerimeterBound（fanV + f_surr，:1473-1477）finalized 形）。
DISCHARGES：骨架占位；HOL 证明走 `lemma_face_representation` +
`sum_face_rho_node1` + 极扇周长 `Polar_fan.FAN_PERIMETER`/`WSEWPCH` + 凸性
（`f_surr_localization_convex_local`），依赖 Polar_fan / Local_lemmas 章。 -/
theorem fully_surrounded_perimeter_bound (V : Set V3) (E : Set (Set V3))
    (hfan : FAN 0 V E) (hsurr : FullySurrounded V E) :
    PerimeterBound V E hfan := by
  -- NEEDS（Lane G 侦察 2026-10-23）：卡具名桥——LocalAuto7（Polar_fan 移植）的
  -- 周长 lane `WSEWPCH`/`FAN_PERIMETER`/`BGMIFTE` 均为 faithful sorry 陈述
  -- （LocalAuto7.lean 周长 lane），且 Local_lemmas 章的
  -- `f_surr_localization_convex_local`/`lemma_face_representation`/
  -- `sum_face_rho_node1` 未移植。三桥齐备后按 HOL 五步机械装配。
  sorry

/-- HOL `NODE_TYPE_lemma`（`tame/tame_general.hl:488-495`，"Alternative form
for type_of_node"）。DISCHARGES：骨架占位；HOL 证明经
`SIMPLE_HYPERMAP_lemma`（face ∩ node = {x} 给 face↔node 代表元双射），
为本文件最深的支撑件之一。 -/
theorem NODE_TYPE_lemma {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α)
    (hs : H.Simple) (hx : x ∈ H.darts) :
    typeOfNode H x =
      ({y | y ∈ H.node x ∧ (H.face y).ncard = 3}.ncard,
        {y | y ∈ H.node x ∧ (H.face y).ncard = 4}.ncard,
        {y | y ∈ H.node x ∧ 5 ≤ (H.face y).ncard}.ncard) := by
  have hinj : Set.InjOn (fun y => H.face y) (H.node x) := faceInjOn_of_node hs x hx
  have hsub : ∀ y ∈ H.node x, y ∈ H.darts := fun y hy => H.node_subset_darts hx hy
  -- 三个 meet-node 集合 = face 在 node 轨道（按基数分层）上的像
  have e1 : setOfTrianglesMeetingNode H x =
      (fun y => H.face y) '' {y | y ∈ H.node x ∧ (H.face y).ncard = 3} := by
    ext F
    constructor
    · intro hF
      simp only [setOfTrianglesMeetingNode, Set.mem_setOf_eq] at hF
      obtain ⟨y, -, rfl, hcard, hyn⟩ := hF
      exact (Set.mem_image (fun y => H.face y)
        {y | y ∈ H.node x ∧ (H.face y).ncard = 3} (H.face y)).mpr
        ⟨y, Set.mem_setOf_eq.mpr ⟨hyn, hcard⟩, rfl⟩
    · intro hF
      obtain ⟨y, hpair, rfl⟩ := (Set.mem_image (fun y => H.face y)
        {y | y ∈ H.node x ∧ (H.face y).ncard = 3} F).mp hF
      simp only [Set.mem_setOf_eq] at hpair
      exact ⟨y, hsub y hpair.1, rfl, hpair.2, hpair.1⟩
  have e2 : setOfQuadrilateralsMeetingNode H x =
      (fun y => H.face y) '' {y | y ∈ H.node x ∧ (H.face y).ncard = 4} := by
    ext F
    constructor
    · intro hF
      simp only [setOfQuadrilateralsMeetingNode, Set.mem_setOf_eq] at hF
      obtain ⟨y, -, rfl, hcard, hyn⟩ := hF
      exact (Set.mem_image (fun y => H.face y)
        {y | y ∈ H.node x ∧ (H.face y).ncard = 4} (H.face y)).mpr
        ⟨y, Set.mem_setOf_eq.mpr ⟨hyn, hcard⟩, rfl⟩
    · intro hF
      obtain ⟨y, hpair, rfl⟩ := (Set.mem_image (fun y => H.face y)
        {y | y ∈ H.node x ∧ (H.face y).ncard = 4} F).mp hF
      simp only [Set.mem_setOf_eq] at hpair
      exact ⟨y, hsub y hpair.1, rfl, hpair.2, hpair.1⟩
  have e3 : setOfExceptionalMeetingNode H x =
      (fun y => H.face y) '' {y | y ∈ H.node x ∧ 5 ≤ (H.face y).ncard} := by
    ext F
    constructor
    · intro hF
      simp only [setOfExceptionalMeetingNode, Set.mem_setOf_eq] at hF
      obtain ⟨y, -, rfl, hcard, hyn⟩ := hF
      exact (Set.mem_image (fun y => H.face y)
        {y | y ∈ H.node x ∧ 5 ≤ (H.face y).ncard} (H.face y)).mpr
        ⟨y, Set.mem_setOf_eq.mpr ⟨hyn, hcard⟩, rfl⟩
    · intro hF
      obtain ⟨y, hpair, rfl⟩ := (Set.mem_image (fun y => H.face y)
        {y | y ∈ H.node x ∧ 5 ≤ (H.face y).ncard} F).mp hF
      simp only [Set.mem_setOf_eq] at hpair
      exact ⟨y, hsub y hpair.1, rfl, hpair.2, hpair.1⟩
  have hJ3 : Set.InjOn (fun y => H.face y) {y | y ∈ H.node x ∧ (H.face y).ncard = 3} :=
    hinj.mono fun y hy => (Set.mem_setOf_eq.mp hy).1
  have hJ4 : Set.InjOn (fun y => H.face y) {y | y ∈ H.node x ∧ (H.face y).ncard = 4} :=
    hinj.mono fun y hy => (Set.mem_setOf_eq.mp hy).1
  have hJ5 : Set.InjOn (fun y => H.face y) {y | y ∈ H.node x ∧ 5 ≤ (H.face y).ncard} :=
    hinj.mono fun y hy => (Set.mem_setOf_eq.mp hy).1
  unfold typeOfNode
  rw [e1, e2, e3, Set.InjOn.ncard_image hJ3, Set.InjOn.ncard_image hJ4,
    Set.InjOn.ncard_image hJ5]

/-! ### 3b. `sum_tauVEF_upper_bound` 的支撑 kit（2026-10-23 Lane G 真证）。

原 NEEDS 注记的两条路线均由树内存量解除：(a) confV 桥按 §4
`contraveningConformingTl` 同模板机械构造——`surroundedNode` 在定义上弱于
`FullySurrounded`（仅多一个 `d.1 = v` 前置条件）；(b) 面集上 `sol` 和不需要
Euler 关系，直接消费 ConformingAuto6 的 `SUM_SOL_IN_FACE_SET_EQ_4PI`
（Lean 编码以 `hypermapOfFan` 直述 face_set，HOL 的
`fan_hypermaps_iso_explicit2` 传输层整体消失）。逐面恒等式即 HOL
`tauVEF_alt2_alt` 的 Lean 折算（sol 方程取 `conformingSolidAngleFan`
第五合取项），帽石装配为纯算术。 -/

/-! **前向阻塞副本注记**：本节 `p6g_orbit_partition`/`p6g_img_sum_injOn`/
`p6g_node_sum_azim`/`p6g_node_sum_azim_lmfun`/`p6g_hrxefdm` 五件是 §7a/§7b
`setSum_setOfOrbits`/`setSum_image_injOn`/`node_sum_azim(_lmfun)`/
`HRXEFDM_lemma1` 的逐字副本（本文件 §3b 在 §7b 之前，同文件禁前向引用）。
后续若文件序调整使 §7b 前移，应删除本块并回引正本去重。 -/

/-- 前向阻塞副本：`setSum_setOfOrbits`（§7a）。 -/
private theorem p6g_orbit_partition {α : Type*} [DecidableEq α] (D : Finset α)
    (f : Equiv.Perm α) (hf : PermutesOn f D) (g : α → ℝ) :
    setSum (setOfOrbits D f) (fun o => setSum o g) = setSum (↑D : Set α) g := by
  classical
  have hFO : (setOfOrbits D f).Finite := setOfOrbits_finite D f
  set S : Finset (Set α) := hFO.toFinset with hSdef
  have hmemS : ∀ o ∈ S, o ∈ setOfOrbits D f := by
    intro o ho
    exact (Set.Finite.mem_toFinset hFO).mp (Finset.mem_coe.mp ho)
  have hdisj : (↑S : Set (Set α)).PairwiseDisjoint
      (fun o : Set α => if h : o.Finite then h.toFinset else ∅) := by
    intro o₁ h₁ o₂ h₂ hne
    obtain ⟨x, hx, rfl⟩ := hmemS o₁ h₁
    obtain ⟨y, hy, rfl⟩ := hmemS o₂ h₂
    rcases orbitMap_disjoint_or_eq hf x y with hd | he
    · refine Finset.disjoint_left.mpr ?_
      intro a ha hab
      simp only [dif_pos (orbitMap_finite hf x), dif_pos (orbitMap_finite hf y)] at ha hab
      have hm : a ∈ (orbitMap f x ∩ orbitMap f y : Set α) :=
        ⟨(Set.Finite.mem_toFinset (orbitMap_finite hf x)).mp ha,
          (Set.Finite.mem_toFinset (orbitMap_finite hf y)).mp hab⟩
      rw [hd] at hm
      exact absurd hm (by simp)
    · exact absurd he hne
  have hinner : ∀ o ∈ S, setSum o g
      = ∑ y ∈ (fun o : Set α => if h : o.Finite then h.toFinset else ∅) o, g y := by
    intro o ho
    obtain ⟨x, hx, rfl⟩ := hmemS o ho
    rw [setSum, dif_pos (orbitMap_finite hf x)]
    simp only [dif_pos (orbitMap_finite hf x)]
  have huni : (S.biUnion (fun o : Set α => if h : o.Finite then h.toFinset else ∅) : Finset α)
      = D := by
    ext y
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨o, ho, hyo⟩
      obtain ⟨x, hx, rfl⟩ := hmemS o ho
      simp only [dif_pos (orbitMap_finite hf x)] at hyo
      have hyD : y ∈ (orbitMap f x : Set α) :=
        (Set.Finite.mem_toFinset (orbitMap_finite hf x)).mp hyo
      have hsub := orbitMap_subset_of_permutesOn hf hx hyD
      simpa using hsub
    · intro hy
      refine ⟨orbitMap f y, ?_, ?_⟩
      · rw [hSdef]
        exact Set.Finite.mem_toFinset hFO |>.mpr ⟨y, by simpa using hy, rfl⟩
      · simp only [dif_pos (orbitMap_finite hf y)]
        exact (Set.Finite.mem_toFinset (orbitMap_finite hf y)).mpr
          (pow_apply_mem_orbitMap f 0 y)
  have hstep : ∑ o ∈ S,
      ∑ y ∈ (fun o : Set α => if h : o.Finite then h.toFinset else ∅) o, g y
      = ∑ y ∈ D, g y := by
    rw [← huni]
    exact (Finset.sum_biUnion (t := fun (o : Set α) => if h : o.Finite then h.toFinset else ∅)
      (f := fun y => g y) hdisj).symm
  have hD : Set.Finite.toFinset D.finite_toSet = D := by ext y; simp
  rw [setSum, setSum, dif_pos hFO, dif_pos D.finite_toSet, hD, ← hSdef]
  rw [Finset.sum_congr rfl (fun o ho => hinner o ho)]
  exact hstep

/-- 前向阻塞副本：`setSum_image_injOn`（§7a）。 -/
private theorem p6g_img_sum_injOn {α β : Type*} [DecidableEq β] {s : Set α} (hs : s.Finite)
    {φ : α → β} (hφ : Set.InjOn φ s) (g : β → ℝ) :
    setSum (φ '' s) g = setSum s (fun x => g (φ x)) := by
  have hfin : (φ '' s).Finite := hs.image φ
  rw [setSum, setSum, dif_pos hfin, dif_pos hs]
  refine (Finset.sum_bij (fun x _ => φ x) ?_ ?_ ?_ ?_).symm
  · intro x hx
    exact (Set.Finite.mem_toFinset hfin).mpr
      ⟨x, (Set.Finite.mem_toFinset hs).mp hx, rfl⟩
  · intro x hx y hy heq
    exact hφ ((Set.Finite.mem_toFinset hs).mp hx) ((Set.Finite.mem_toFinset hs).mp hy) heq
  · intro y hy
    obtain ⟨x, hx, hex⟩ := (Set.mem_image φ s y).mp
      ((Set.Finite.mem_toFinset hfin).mp hy)
    exact ⟨x, (Set.Finite.mem_toFinset hs).mpr hx, hex⟩
  · intro x hx
    rfl

/-- 前向阻塞副本：`azimDart_iterate_eq`（§4b）。 -/
private theorem p6g_azimDart_iterate_eq (hfan : FAN 0 V E) {v u : V3} (hvu : {v, u} ∈ E)
    (hcard1 : 1 < (setOfEdge v V E).ncard) (i : ℕ)
    (hin : i < (setOfEdge v V E).ncard) :
    azimDart V E (v, (sigmaFan 0 V E v)^[i] u) = azimIfan 0 V E v u i := by
  have hvw : v ≠ (sigmaFan 0 V E v)^[i] u := by
    have he : {v, (sigmaFan 0 V E v)^[i] u} ∈ E :=
      (properties_of_setOfEdge_fan 0 V E v _ hfan).mpr
        (iterates_mem_setOfEdge hfan v u
          ((properties_of_setOfEdge_fan 0 V E v u hfan).mp hvu) i)
    exact edge_ne_of_fan hfan he
  show (if (v, _).1 = (v, _).2 then 2 * Real.pi
      else azimFan 0 V E (v, _).1 (v, _).2) = azimIfan 0 V E v u i
  rw [if_neg hvw]
  show (if (setOfEdge v V E).ncard > 1 then
      azim 0 v ((sigmaFan 0 V E v)^[i] u) (sigmaFan 0 V E v ((sigmaFan 0 V E v)^[i] u))
    else 2 * Real.pi) = azim 0 v ((sigmaFan 0 V E v)^[i] u)
      ((sigmaFan 0 V E v)^[i + 1] u)
  rw [if_pos hcard1, Function.iterate_succ_apply']

/-- 前向阻塞副本：`node_sum_azim`（§7b NodeSum）。 -/
private theorem p6g_node_sum_azim (hfan : FAN 0 V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    setSum ((hypermapOfFanTl V E hfan).node d) (fun y => azimDart V E y)
      = 2 * Real.pi := by
  set H := hypermapOfFanTl V E hfan with hHdef
  rcases Nat.lt_or_ge (setOfEdge d.1 V E).ncard 2 with h1 | h2
  · -- card(soe d.1) ≤ 1：card = 1，node d = {d}，azimDart d = 2π
    have hdm : d.2 ∈ setOfEdge d.1 V E := (FAN_in_setOfEdge 0 V E d.1 d.2 hfan hd).2.2.1
    have hpos : 0 < (setOfEdge d.1 V E).ncard :=
      Iff.mpr (Set.ncard_pos (hs := remark_finite_fan1 d.1 V E hfan.2.2.1.1)) ⟨d.2, hdm⟩
    have hcard1 : (setOfEdge d.1 V E).ncard = 1 := by omega
    obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcard1
    have hx2 : x = d.2 := by
      have h2' : d.2 ∈ setOfEdge d.1 V E := hdm
      rw [hx] at h2'
      exact (Set.mem_singleton_iff.mp h2').symm
    have hsoe : setOfEdge d.1 V E = {d.2} := by rw [hx, hx2]
    have hnode : H.node d = {d} := by
      rw [nodeTl_eq_image hfan hd, hsoe, Set.image_singleton]
    have hncard1 : ¬ ((setOfEdge d.1 V E).ncard > 1) := by
      rw [hsoe, Set.ncard_singleton]
      simp
    have hazim : azimDart V E d = 2 * Real.pi := by
      show (if d.1 = d.2 then 2 * Real.pi
        else if (setOfEdge d.1 V E).ncard > 1 then
          azim 0 d.1 d.2 (sigmaFan 0 V E d.1 d.2)
        else 2 * Real.pi) = 2 * Real.pi
      rw [if_neg (edge_ne_of_fan hfan hd), if_neg hncard1]
    rw [hnode, setSum, dif_pos (Set.finite_singleton d), Set.Finite.toFinset_singleton,
      Finset.sum_singleton]
    exact hazim
  · -- card ≥ 2：σ-循环双射 + sum_azims_eq_2pi
    have hne_u : setOfEdge d.1 V E ≠ {d.2} := by
      intro he
      rw [he, Set.ncard_singleton] at h2
      omega
    have hdE : {d.1, d.2} ∈ E := hd
    have hfin : (H.node d).Finite := orbitMap_finite H.nodeMap_permutes d
    have step1 : (∑ i ∈ Finset.range (setOfEdge d.1 V E).ncard,
          azimDart V E (d.1, (sigmaFan 0 V E d.1)^[i] d.2))
        = setSum (H.node d) (fun y => azimDart V E y) := by
      rw [setSum, dif_pos hfin]
      refine Finset.sum_bij (fun i _ => (d.1, (sigmaFan 0 V E d.1)^[i] d.2)) ?_ ?_ ?_ ?_
      · intro i hi
        have hmem : (d.1, (sigmaFan 0 V E d.1)^[i] d.2) ∈ H.node d := by
          have h1' : H.nodeMap^[i] d = (d.1, (sigmaFan 0 V E d.1)^[i] d.2) :=
            nodeMapTl_iterate hd i
          rw [← h1']
          exact pow_apply_mem_orbitMap H.nodeMap i d
        exact (Set.Finite.mem_toFinset hfin).mpr hmem
      · intro i hi j hj heq
        have hin : i < (setOfEdge d.1 V E).ncard := Finset.mem_range.mp hi
        have hjn : j < (setOfEdge d.1 V E).ncard := Finset.mem_range.mp hj
        simp only [Prod.mk.injEq] at heq
        rcases lt_trichotomy i j with hlt | heqi | hgt
        · exact absurd heq.2.symm (cyclic_power_sigmaFan 0 V E hfan hdE j i hjn hlt)
        · exact heqi
        · exact absurd heq.2 (cyclic_power_sigmaFan 0 V E hfan hdE i j hin hgt)
      · intro y hy
        have hyn : y ∈ H.node d := (Set.Finite.mem_toFinset hfin).mp hy
        simp only [Hypermap.node, orbitMap, Set.mem_setOf_eq] at hyn
        obtain ⟨n, hn⟩ := hyn
        rw [Equiv.Perm.coe_pow] at hn
        rw [nodeMapTl_iterate hd n] at hn
        have hsoe : (sigmaFan 0 V E d.1)^[n] d.2 ∈ setOfEdge d.1 V E :=
          iterates_mem_setOfEdge hfan d.1 d.2
            ((properties_of_setOfEdge_fan 0 V E d.1 d.2 hfan).mp hdE) n
        obtain ⟨j, hj, hj_eq⟩ := iterates_mem_sigmaFan hfan hdE hsoe
        refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
        rw [hj_eq]
        exact hn
      · intro i hi
        rfl
    have step2 : (∑ i ∈ Finset.range (setOfEdge d.1 V E).ncard,
          azimDart V E (d.1, (sigmaFan 0 V E d.1)^[i] d.2))
        = (∑ i ∈ Finset.range (setOfEdge d.1 V E).ncard, azimIfan 0 V E d.1 d.2 i) :=
      Finset.sum_congr rfl (fun i hi =>
        p6g_azimDart_iterate_eq hfan hdE (by omega) i (Finset.mem_range.mp hi))
    calc setSum (H.node d) (fun y => azimDart V E y)
        = ∑ i ∈ Finset.range (setOfEdge d.1 V E).ncard,
            azimDart V E (d.1, (sigmaFan 0 V E d.1)^[i] d.2) := step1.symm
      _ = ∑ i ∈ Finset.range (setOfEdge d.1 V E).ncard, azimIfan 0 V E d.1 d.2 i := step2
      _ = 2 * Real.pi := sum_azims_eq_2pi hfan hdE hne_u

/-- 前向阻塞副本：`node_sum_azim_lmfun`（§7b）。 -/
private theorem p6g_node_sum_azim_lmfun (hfan : FAN 0 V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    setSum ((hypermapOfFanTl V E hfan).node d)
        (fun y => azimDart V E y * lmfun (hDart_p2 y))
      = 2 * Real.pi * lmfun (hDart_p2 d) := by
  set H := hypermapOfFanTl V E hfan with hHdef
  have hfin : (H.node d).Finite := orbitMap_finite H.nodeMap_permutes d
  have hconst : ∀ y ∈ H.node d, lmfun (hDart_p2 y) = lmfun (hDart_p2 d) := by
    intro y hy
    rw [nodeTl_eq_image hfan hd] at hy
    obtain ⟨q, hq, hyq⟩ := hy
    have hy1 : y.1 = d.1 := by rw [← hyq]
    show lmfun (‖y.1‖ / 2) = lmfun (‖d.1‖ / 2)
    rw [hy1]
  calc setSum (H.node d) (fun y => azimDart V E y * lmfun (hDart_p2 y))
      = setSum (H.node d) (fun y => azimDart V E y * lmfun (hDart_p2 d)) := by
        rw [setSum, setSum, dif_pos hfin, dif_pos hfin]
        exact Finset.sum_congr rfl (fun y hy => by
          rw [hconst y ((Set.Finite.mem_toFinset hfin).mp hy)])
    _ = setSum (H.node d) (fun y => azimDart V E y) * lmfun (hDart_p2 d) := by
        rw [setSum, setSum, dif_pos hfin, dif_pos hfin, Finset.sum_mul]
    _ = 2 * Real.pi * lmfun (hDart_p2 d) := by rw [p6g_node_sum_azim hfan hd]

/-- 前向阻塞副本：`HRXEFDM_lemma1`（§7b）。 -/
private theorem p6g_hrxefdm (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (hns : ∀ v ∈ V, (setOfEdge v V E).Nonempty) :
    setSum (hypermapOfFanTl V E hfan).faceSet
        (fun o => setSum o (fun x => azimDart V E x * lmfun (hDart_p2 x)))
      = 2 * Real.pi * scriptL V := by
  classical
  set H := hypermapOfFanTl V E hfan with hHdef
  have hVfin : V.Finite := hfan.2.2.1.1
  have hex : ∀ v : V3, v ∈ V → ∃ w, (v, w) ∈ dart1OfFan V E := by
    intro v hv
    obtain ⟨w, hw⟩ := hns v hv
    exact ⟨w, (properties_of_setOfEdge_fan 0 V E v w hfan).mpr hw⟩
  set dd : V3 → V3 × V3 :=
    fun v => if h : v ∈ V then (v, Classical.choose (hex v h)) else (v, v) with hdddef
  have hdd : ∀ v : V3, v ∈ V → dd v ∈ dart1OfFan V E := by
    intro v hv
    simp only [hdddef, dif_pos hv]
    exact Classical.choose_spec (hex v hv)
  have hddfst : ∀ v : V3, v ∈ V → (dd v).1 = v := by
    intro v hv
    simp only [hdddef, dif_pos hv]
  have himg : H.nodeSet = (fun v : V3 => H.node (dd v)) '' V := by
    ext S
    constructor
    · intro hS
      obtain ⟨d, hd, rfl⟩ := hS.out
      have hvV : d.1 ∈ V := (FAN_in_setOfEdge 0 V E d.1 d.2 hfan (dartsTl_mem hd)).1
      refine ⟨d.1, hvV, ?_⟩
      show H.node (dd d.1) = H.node d
      rw [nodeTl_eq_image hfan (dartsTl_mem hd), nodeTl_eq_image hfan (hdd d.1 hvV),
        hddfst d.1 hvV]
    · rintro ⟨v, hv, rfl⟩
      exact ⟨dd v, mem_dartsTl (hdd v hv),
        (by rfl : orbitMap H.nodeMap (dd v) = (fun v : V3 => H.node (dd v)) v)⟩
  have hinj : Set.InjOn (fun v : V3 => H.node (dd v)) V := by
    intro v hv w hw heq
    simp only [] at heq
    have hmem0 : dd v ∈ H.node (dd v) := mem_orbitMap_self H.nodeMap (dd v)
    rw [nodeTl_eq_image hfan (hdd v hv)] at hmem0
    simp only [Set.mem_image, Set.mem_setOf_eq] at hmem0
    obtain ⟨q, hq, hprod⟩ := hmem0
    rw [hddfst v hv] at hq
    have hddv : dd v = (v, q) := by rw [hprod.symm, hddfst v hv]
    rw [hddv] at heq
    have hmq : (v, q) ∈ H.node (dd w) := by
      rw [← heq, nodeTl_eq_image hfan (by rw [← hddv]; exact hdd v hv)]
      exact ⟨q, hq, rfl⟩
    rw [nodeTl_eq_image hfan (hdd w hw)] at hmq
    simp only [Set.mem_image, Set.mem_setOf_eq] at hmq
    obtain ⟨q2, hq2, hprod2⟩ := hmq
    injection hprod2 with h5 h6
    exact h5.symm.trans (hddfst w hw)
  calc setSum H.faceSet (fun o => setSum o (fun x => azimDart V E x * lmfun (hDart_p2 x)))
      = setSum (↑H.darts : Set (V3 × V3)) (fun x => azimDart V E x * lmfun (hDart_p2 x)) :=
        p6g_orbit_partition H.darts H.faceMap H.faceMap_permutes _
    _ = setSum H.nodeSet (fun o => setSum o (fun x => azimDart V E x * lmfun (hDart_p2 x))) :=
        (p6g_orbit_partition H.darts H.nodeMap H.nodeMap_permutes _).symm
    _ = setSum ((fun v : V3 => H.node (dd v)) '' V)
          (fun o => setSum o (fun x => azimDart V E x * lmfun (hDart_p2 x))) := by rw [himg]
    _ = setSum V (fun v => setSum (H.node (dd v))
          (fun x => azimDart V E x * lmfun (hDart_p2 x))) :=
        p6g_img_sum_injOn hVfin hinj _
    _ = setSum V (fun v => 2 * Real.pi * lmfun (hDart_p2 (dd v))) := by
        rw [setSum, setSum, dif_pos hVfin, dif_pos hVfin]
        exact Finset.sum_congr rfl (fun v hv => p6g_node_sum_azim_lmfun hfan
          (hdd v ((Set.Finite.mem_toFinset hVfin).mp hv)))
    _ = setSum V (fun v => 2 * Real.pi * lmfun (‖v‖ / 2)) := by
        rw [setSum, setSum, dif_pos hVfin, dif_pos hVfin]
        exact Finset.sum_congr rfl (fun v hv => by
          show 2 * Real.pi * lmfun (‖(dd v).1‖ / 2) = 2 * Real.pi * lmfun (‖v‖ / 2)
          rw [hddfst v ((Set.Finite.mem_toFinset hVfin).mp hv)])
    _ = 2 * Real.pi * setSum V (fun v => lmfun (‖v‖ / 2)) := by
        rw [setSum, setSum, dif_pos hVfin, dif_pos hVfin]
        exact (Finset.mul_sum _ _ _).symm
    _ = 2 * Real.pi * scriptL V := by rw [scriptL, dif_pos hVfin, setSum, dif_pos hVfin]

/-- 数值锚：`0 < sol0`（LocalAuto19.sol0Pos_p19 同款，仅用 Mathlib）。 -/
private theorem p6g_sol0_pos : (0 : ℝ) < sol0 := by
  have h2 : (1 / 2 : ℝ) = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
  have h3 : Real.arccos (1 / 2) = Real.pi / 3 := by
    rw [h2]; exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h4 : Real.arccos (1 / 2) < Real.arccos (1 / 3) :=
    Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)
  have h5 : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  linarith

/-- 有限集上 `setSum` 与 finsum 的互译桥。 -/
private theorem p6g_setSum_finsum {α : Type*} [DecidableEq α] {s : Set α}
    (hs : s.Finite) (g : α → ℝ) : setSum s g = ∑ᶠ a ∈ s, g a := by
  rw [setSum, dif_pos hs]
  conv_rhs => rw [← hs.coe_toFinset, finsum_mem_coe_finset]

/-- HOL `fully_surrounded_imp_conforming`（add_triangle-compiled.hl:651）：
FAN + fully_surrounded 给 conformingFan。§4 `contraveningConformingTl` 同
模板——其 `surroundedNode` 输入由 `FullySurrounded` 逐 dart 直接弱化给出。 -/
private theorem p6g_fullySurrounded_conforming (V : Set V3) (E : Set (Set V3))
    (hfan : FAN 0 V E) (hsurr : FullySurrounded V E) :
    conformingFan 0 V E hfan := by
  have hsN : ∀ v ∈ V, surroundedNode V E v := fun v _ d hd _ => hsurr d hd
  have hcard3 : ∀ v ∈ V, 3 ≤ (setOfEdge v V E).ncard := fun v hv =>
    SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hv (hsN v hv)
  have hcard : ∀ v ∈ V, 1 < (setOfEdge v V E).ncard := fun v hv =>
    lt_of_lt_of_le (by omega) (hcard3 v hv)
  have hfan80 : fan80 0 V E := by
    intro v u he
    have hvV : v ∈ V := (FAN_in_setOfEdge 0 V E v u hfan he).1
    have hd1 : (v, u) ∈ dart1OfFan V E := he
    have hlt : azimDart V E (v, u) < Real.pi :=
      hsN v hvV (v, u) (Set.mem_union_right _ hd1) rfl
    have hne : v ≠ u := edge_ne_of_fan hfan he
    have heq : azimDart V E (v, u) = azim 0 v u (sigmaFan 0 V E v u) := by
      show (if (v, u).1 = (v, u).2 then 2 * Real.pi else
        if (setOfEdge (v, u).1 V E).ncard > 1 then
          azim 0 (v, u).1 (v, u).2 (sigmaFan 0 V E (v, u).1 (v, u).2)
        else 2 * Real.pi) = _
      have hgt : (setOfEdge (v, u).1 V E).ncard > 1 :=
        lt_of_lt_of_le (by omega : (1:ℕ) < 3) (hcard3 v hvV)
      rw [if_neg hne, if_pos hgt]
    rw [heq] at hlt
    refine ⟨?_, hlt⟩
    refine lt_of_le_of_ne (azim_nonneg 0 v u _) ?_
    intro h0
    have hsoene : setOfEdge v V E ≠ {u} := by
      intro h1
      have hcp := hcard3 v hvV
      rw [h1, Set.ncard_singleton] at hcp
      omega
    have hsig := SIGMA_FAN hsoene hfan
      ((properties_of_setOfEdge_fan 0 V E v u hfan).mp he)
    exact hsig.2.1 (unique_azim0_point_fan hfan he
      ((properties_of_setOfEdge_fan 0 V E v (sigmaFan 0 V E v u) hfan).mpr
        hsig.1) h0.symm).symm
  exact PIIJBJK 0 V E hfan ⟨hfan, hcard, hfan80⟩

/-- HOL `tauVEF_alt2_alt`（tame_lemmas-compiled.hl FullySurrounded section）
的 Lean 折算：面上 `tauVEF` = 对面 leads-into 集 sol × (1 + sol0/π) −
(sol0/π) × 面上 azim·lmfun 和。sol 方程 = `conformingSolidAngleFan`
第五合取项；`azimFan`/`azimDart` 的逐点认同由 fully_surrounded 的
`azimDart < π` 挡死两处 2π 缺省支。 -/
private theorem p6g_face_tauVEF (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (hsurr : FullySurrounded V E) (hconf : conformingFan 0 V E hfan)
    {f : Set (V3 × V3)} (hf : f ∈ (hypermapOfFanTl V E hfan).faceSet) :
    f.Finite ∧ tauVEF_p2 V E f =
      (1 + sol0 / Real.pi) * sol 0 (dartsetLeadsIntoFan 0 V E f)
        - sol0 / Real.pi * setSum f (fun x => azimDart V E x * lmfun (hDart_p2 x)) := by
  classical
  set H := hypermapOfFanTl V E hfan with hHdef
  obtain ⟨d, hd, hfd⟩ := hf
  have hf0 : f ∈ (hypermapOfFanTl V E hfan).faceSet := ⟨d, hd, hfd⟩
  have hface : H.face d = f := hfd
  have hfin : f.Finite := by
    rw [← hface]
    exact H.face_finite d
  refine ⟨hfin, ?_⟩
  -- hypermapOfFan 的结果实例烤定为 instDecidableEqProd（TameLp 的合成偏好是
  -- dartDecEq2，点投影会实例失配），凡裸 hypermapOfFan 的 faceSet 一律 @ 显式。
  have hfeq2 : (hypermapOfFanTl V E hfan).faceSet
      = @Hypermap.faceSet (V3 × V3) (fun a b => instDecidableEqProd a b)
          (hypermapOfFan 0 V E hfan) := rfl
  have hfeq : f ∈ @Hypermap.faceSet (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := by
    rw [← hfeq2]; exact hf0
  -- f 的元素都是 dart
  have hdartmem : ∀ y ∈ f, y ∈ dartOfFan V E := by
    intro y hy
    have hyf : y ∈ H.face d := by rw [hface]; exact hy
    have hy2 : y ∈ (↑H.darts : Set (V3 × V3)) := H.face_subset_darts hd hyf
    rw [dartsTl_coe] at hy2
    exact Set.mem_union_right _ hy2
  -- fully_surrounded 下 azimDart = azimFan（y.1 = y.2 或边集 ≤ 1 均给 2π ≮ π）
  have hA : ∀ y ∈ f, azimDart V E y = azimFan 0 V E y.1 y.2 := by
    intro y hy
    have hlt : azimDart V E y < Real.pi := hsurr y (hdartmem y hy)
    have hyne : y.1 ≠ y.2 := by
      intro heq
      have h2pi : azimDart V E y = 2 * Real.pi := by simp only [azimDart, if_pos heq]
      rw [h2pi] at hlt
      linarith [Real.pi_pos]
    show (if y.1 = y.2 then 2 * Real.pi else azimFan 0 V E y.1 y.2)
      = azimFan 0 V E y.1 y.2
    rw [if_neg hyne]
  -- finsum → toFinset 有限和
  have hz : ∑ᶠ y ∈ f, (azimFan 0 V E y.1 y.2 - Real.pi)
      = ∑ x ∈ hfin.toFinset, (azimFan 0 V E x.1 x.2 - Real.pi) := by
    conv_lhs => rw [← hfin.coe_toFinset, finsum_mem_coe_finset]
  have hS1 : ∑ x ∈ hfin.toFinset, azimFan 0 V E x.1 x.2
      = ∑ x ∈ hfin.toFinset, azimDart V E x :=
    Finset.sum_congr rfl fun x hx =>
      (hA x ((Set.Finite.mem_toFinset hfin).mp hx)).symm
  -- sol 方程（conforming 第五合取项）
  have hsol : sol 0 (dartsetLeadsIntoFan 0 V E f)
      = 2 * Real.pi + (∑ x ∈ hfin.toFinset, azimDart V E x
        - (f.ncard : ℝ) * Real.pi) := by
    have h5 := hconf.2.2.2.2.1 f hfeq
    have h6 : sol 0 (dartsetLeadsIntoFan 0 V E f)
        = 2 * Real.pi + ∑ᶠ y ∈ f, (azimFan 0 V E y.1 y.2 - Real.pi) := h5.2.2
    rw [hz, Finset.sum_sub_distrib, hS1, Finset.sum_const, nsmul_eq_mul,
      ← Set.ncard_eq_toFinset_card f hfin] at h6
    exact h6
  set S1 : ℝ := ∑ x ∈ hfin.toFinset, azimDart V E x with hS1def
  set S2 : ℝ := ∑ x ∈ hfin.toFinset, azimDart V E x * lmfun (hDart_p2 x) with hS2def
  have hsplit : setSum f
        (fun x => azimDart V E x * (1 + sol0 / Real.pi * (1 - lmfun (hDart_p2 x))))
      = S1 + sol0 / Real.pi * (S1 - S2) := by
    rw [setSum, dif_pos hfin]
    have hpt : ∀ x ∈ hfin.toFinset,
        azimDart V E x * (1 + sol0 / Real.pi * (1 - lmfun (hDart_p2 x)))
          = azimDart V E x
            + sol0 / Real.pi * (azimDart V E x - azimDart V E x * lmfun (hDart_p2 x)) := by
      intro x _; ring
    rw [Finset.sum_congr rfl fun x hx => hpt x hx, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hinner : setSum f (fun x => azimDart V E x * lmfun (hDart_p2 x)) = S2 := by
    rw [setSum, dif_pos hfin]
  have harith : ∀ s1 s2 n : ℝ,
      s1 + sol0 / Real.pi * (s1 - s2) + (Real.pi + sol0) * (2 - n)
        = (2 * Real.pi + (s1 - n * Real.pi)) * (1 + sol0 / Real.pi)
          - sol0 / Real.pi * s2 := by
    intro s1 s2 n
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    field_simp
    ring
  show setSum f
        (fun x => azimDart V E x * (1 + sol0 / Real.pi * (1 - lmfun (hDart_p2 x))))
      + (Real.pi + sol0) * (2 - (f.ncard : ℝ))
    = (1 + sol0 / Real.pi) * sol 0 (dartsetLeadsIntoFan 0 V E f)
      - sol0 / Real.pi * setSum f (fun x => azimDart V E x * lmfun (hDart_p2 x))
  rw [hinner, hsplit, hsol, harith]
  ring

/-- HOL `sum_tauVEF_upper_bound`（`tame/ssreflect/tame_lemmas-compiled.hl:529-538`，
section FullySurrounded（fanV + f_surr，:286-290）finalized 形）。
`tauVEF` ↦ `Kepler.Text.tauVEF_p2`（localization.hl:1559）。
真证明 2026-10-23（Lane G，§3b kit）：confV 桥 `p6g_fullySurrounded_conforming`
+ ConformingAuto6 `SUM_SOL_IN_FACE_SET_EQ_4PI`（面集 sol 和 = 4π，Lean 编码
不需要 HOL 的 iso 传输层与 Euler 关系）+ `p6g_hrxefdm`（前向阻塞副本）+
`p6g_face_tauVEF`（`tauVEF_alt2_alt` 折算）+ 纯算术（12 ≤ scriptL、sol0 > 0）。 -/
theorem sum_tauVEF_upper_bound (V : Set V3) (E : Set (Set V3))
    (hfan : FAN 0 V E) (hsurr : FullySurrounded V E)
    (hscript : 12 ≤ scriptL V) :
    setSum (hypermapOfFanTl V E hfan).faceSet (fun f => tauVEF_p2 V E f)
      ≤ 4 * Real.pi - 20 * sol0 := by
  classical
  set H := hypermapOfFanTl V E hfan with hHdef
  have hconf := p6g_fullySurrounded_conforming V E hfan hsurr
  have hfinFS : H.faceSet.Finite := H.faceSet_finite
  have hcard3 : ∀ v ∈ V, 3 ≤ (setOfEdge v V E).ncard := fun v hv =>
    SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hv (fun d hd _ => hsurr d hd)
  have hns : ∀ v ∈ V, (setOfEdge v V E).Nonempty := by
    intro v hv
    by_contra hcon
    push_neg at hcon
    have h0 : (setOfEdge v V E).ncard = 0 := by rw [hcon, Set.ncard_empty]
    have h3 := hcard3 v hv
    omega
  have hHRX := p6g_hrxefdm V E hfan hns
  have h4pi := SUM_SOL_IN_FACE_SET_EQ_4PI hfan hconf
  have pface : ∀ f ∈ H.faceSet, tauVEF_p2 V E f
      = (1 + sol0 / Real.pi) * sol 0 (dartsetLeadsIntoFan 0 V E f)
        - sol0 / Real.pi * setSum f (fun x => azimDart V E x * lmfun (hDart_p2 x)) :=
    fun f hf => (p6g_face_tauVEF V E hfan hsurr hconf hf).2
  -- 面集和按逐面恒等式拆解
  have key : setSum H.faceSet (fun f => tauVEF_p2 V E f)
      = (1 + sol0 / Real.pi) * setSum H.faceSet (fun f => sol 0 (dartsetLeadsIntoFan 0 V E f))
        - sol0 / Real.pi * setSum H.faceSet
            (fun f => setSum f (fun x => azimDart V E x * lmfun (hDart_p2 x))) := by
    have e1 : setSum H.faceSet (fun f => tauVEF_p2 V E f)
        = ∑ f ∈ hfinFS.toFinset, tauVEF_p2 V E f := by rw [setSum, dif_pos hfinFS]
    have e2 : setSum H.faceSet (fun f => sol 0 (dartsetLeadsIntoFan 0 V E f))
        = ∑ f ∈ hfinFS.toFinset, sol 0 (dartsetLeadsIntoFan 0 V E f) := by
      rw [setSum, dif_pos hfinFS]
    have e3 : setSum H.faceSet
          (fun f => setSum f (fun x => azimDart V E x * lmfun (hDart_p2 x)))
        = ∑ f ∈ hfinFS.toFinset,
            setSum f (fun x => azimDart V E x * lmfun (hDart_p2 x)) := by
      rw [setSum, dif_pos hfinFS]
    rw [e1, e2, e3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun f hf =>
        pface f ((Set.Finite.mem_toFinset hfinFS).mp hf)]
  -- 面集上 sol 和 = 4π（ConformingAuto6，finsum → setSum 桥）
  have hfeq2 : (hypermapOfFanTl V E hfan).faceSet
      = @Hypermap.faceSet (V3 × V3) (fun a b => instDecidableEqProd a b)
          (hypermapOfFan 0 V E hfan) := rfl
  have h4pi' : setSum H.faceSet (fun f => sol 0 (dartsetLeadsIntoFan 0 V E f))
      = 4 * Real.pi := by
    rw [p6g_setSum_finsum hfinFS, hfeq2]
    exact h4pi
  rw [key, h4pi', hHRX]
  -- 收尾算术：(1 + sol0/π)·4π − (sol0/π)·2π·scriptL = 4π + 4sol0 − 2·scriptL·sol0
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpos : 0 < sol0 := p6g_sol0_pos
  have e2 : (1 + sol0 / Real.pi) * (4 * Real.pi)
        - sol0 / Real.pi * (2 * Real.pi * scriptL V)
      = 4 * Real.pi + 4 * sol0 - 2 * (scriptL V * sol0) := by
    field_simp
  rw [e2]
  have hU : (12:ℝ) * sol0 ≤ scriptL V * sol0 :=
    mul_le_mul_of_nonneg_right hscript hpos.le
  linarith

/-! ## 3a'. y-kit W2 kit（Face3 收口链；2026-10-23 Lane P W2）

HOL 锚点：lp_main_estimate-compiled.hl（tau_fun_eq_tauVEF :351、tau3_eq_tau_fun
:494、f_surr_tau_fun_eq_tauVEF :523、f_surr_tau3_eq_tauVEF :542）、
hypermap_and_fan.hl:1222（TRIANGULAR_FACE）、add_triangle-compiled.hl:608
（f_fan_pair3）、lp_ineqs_proofs-compiled.hl:1096（azim_dart_eq_dihV）、
hypermap.hl:2737（lemma_face_representation）。

放置注记：消费目标 `ineq_tau3_tauVEF_std`（§3a，紧随本 kit）按闸门纪律只能删
占位行，其证明链件必须先于目标出现；§9（文件末）晚于目标不可前向引用，故本
kit 自包含：`wk_setSum_insert` 系 §4b `setSum_insert` 私有副本、`wk_norm_bounds`
系 §9c `yk_norm_v` 私有副本、`wk_estd_dist_le` 系 §9c `yk_in_std` 核心私有副本、
`wk_card_face_ge2` 系 §3a `CARD_FACE_GE_3_TL` 前半私有副本（去重债与 §9 一并
记录，待文件序调整波统一收敛）。

覆盖判定（lemma_face_representation）：HOL hypermap.hl:2737
`u IN face_set H → ∃x. x IN dart H ∧ u = face H x` 在 Lean 编码下为定义级事实
——`Hypermap.faceSet = (fun x => orbitMap H.faceMap x) '' ↑H.darts`
（Hypermap.lean:1008/:981）且 `H.face x = orbitMap H.faceMap x`（:846），
`wk_mem_faceSet` 折算即得；LocalAuto2 的 slice kit（SLICEV_BIJ/CARD_SLICEF/
ejr_generic/EJRCFJD_ALT2 等）在本链中无需调用。 -/

section W2Kit

variable {V : Set V3} {E : Set (Set V3)} {hfan : FAN 0 V E}

/-- 同集合上逐点相等的 setSum（SUM_EQ 折算；§4b 同型件的前置副本）。 -/
private theorem wk_setSum_congr {α : Type*} {s : Set α} {f g : α → ℝ}
    (h : ∀ x ∈ s, f x = g x) : setSum s f = setSum s g := by
  by_cases hfin : s.Finite
  · simp only [setSum, dif_pos hfin, dif_pos hfin]
    exact Finset.sum_congr rfl (fun x hx =>
      h x ((Set.Finite.mem_toFinset hfin).mp hx))
  · simp only [setSum, dif_neg hfin, dif_neg hfin]

/-- 单点插入的和分解（SUM_CLAUSES 折算；§4b `setSum_insert` 前置副本）。 -/
private theorem wk_setSum_insert {α : Type*} {s : Set α} {a : α} (ha : a ∉ s)
    (hs : s.Finite) (f : α → ℝ) : setSum (insert a s) f = f a + setSum s f := by
  simp only [setSum, dif_pos (hs.insert a), dif_pos hs,
    Set.Finite.toFinset_insert (hs.insert a)]
  exact Finset.sum_insert (by simpa using ha)

/-- `ee v E = set_of_edge v V E`（FAN 下；localization 的 EE_elim 折算）。 -/
private theorem wk_ee_eq_setOfEdge (hfan : FAN 0 V E) (v : V3) :
    ee v E = setOfEdge v V E := by
  ext u
  simp only [ee, setOfEdge, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨h, FAN_EDGE_EL_V hfan h⟩, fun h => h.1⟩

/-- σ 与 V 无关（FAN 下邻域一致）；`sigmaFan 0 univ E = sigmaFan 0 V E`。 -/
private theorem wk_sigmaFan_congr (hfan : FAN 0 V E) (v u : V3) :
    sigmaFan 0 Set.univ E v u = sigmaFan 0 V E v u := by
  have hE : setOfEdge v Set.univ E = setOfEdge v V E := by
    ext u
    simp only [setOfEdge, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.1, FAN_EDGE_EL_V hfan h.1⟩, fun h => ⟨h.1, Set.mem_univ u⟩⟩
  simp only [sigmaFan, hE]

/-- `azim_in_fan = azim_dart` 在 dart1 上（localization.hl:1515
`azim_dart_azim_in_fan` 的 dart1 形；LocalAuto2 同名件为 _p2 编码且 sorried，
此处独立真证）。 -/
private theorem wk_azimInFan_eq_azimDart (hfan : FAN 0 V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : azimInFan d E = azimDart V E d := by
  have hvw : d.1 ≠ d.2 := edge_ne_of_fan hfan hd
  have hE : ee d.1 E = setOfEdge d.1 V E := wk_ee_eq_setOfEdge hfan d.1
  by_cases hnc : (setOfEdge d.1 V E).ncard > 1
  · have hl : azimInFan d E = azim 0 d.1 d.2 (sigmaFan 0 Set.univ E d.1 d.2) := by
      simp only [azimInFan, hE]
      exact if_pos hnc
    rw [hl, wk_sigmaFan_congr hfan]
    show azim 0 d.1 d.2 (sigmaFan 0 V E d.1 d.2)
      = (if d.1 = d.2 then (2 : ℝ) * Real.pi
        else if (setOfEdge d.1 V E).ncard > 1
          then azim 0 d.1 d.2 (sigmaFan 0 V E d.1 d.2) else 2 * Real.pi)
    rw [if_neg hvw, if_pos hnc]
  · have hnl : azimInFan d E = 2 * Real.pi := by
      simp only [azimInFan, hE]
      exact if_neg hnc
    rw [hnl]
    show (2 : ℝ) * Real.pi
      = (if d.1 = d.2 then (2 : ℝ) * Real.pi
        else if (setOfEdge d.1 V E).ncard > 1
          then azim 0 d.1 d.2 (sigmaFan 0 V E d.1 d.2) else 2 * Real.pi)
    rw [if_neg hvw, if_neg hnc]

/-- `rho_fun y = 1 + (sol0/π)(1 - lmfun (y/2))`（norm 界下；lp_main_estimate
tau_fun_eq_tauVEF :351 证明中 rho_rho_fun + ly_EQ_lmfun + sol0_over_pi 段的
合并折算，纯 h0 = 1.26 算术）。 -/
private theorem wk_rho_eq {v : V3} (hv : (2 : ℝ) ≤ ‖v‖) (hv2 : ‖v‖ ≤ 2 * h0) :
    rhoFun ‖v‖ = 1 + (sol0 / Real.pi) * (1 - lmfun (‖v‖ / 2)) := by
  have hhalf : ‖v‖ / 2 ≤ h0 := by
    rw [div_le_iff₀ two_pos]
    linarith
  have h20 : (2 : ℝ) * h0 - 2 ≠ 0 := by norm_num [h0]
  have h01 : (h0 : ℝ) - 1 ≠ 0 := by norm_num [h0]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hlm : lmfun (‖v‖ / 2) = (h0 - ‖v‖ / 2) / (h0 - 1) := by
    simp only [lmfun, if_pos hhalf]
  rw [rho_rho_fun]
  unfold rho
  rw [hlm]
  have hkey : (‖v‖ - 2) * (sol0 / Real.pi) / (2 * h0 - 2)
      = (sol0 / Real.pi) * (1 - (h0 - ‖v‖ / 2) / (h0 - 1)) := by
    field_simp
    ring
  rw [hkey]

/-- V 上的范数界（norm_v :1204 折算；§9c `yk_norm_v` 前置副本）。 -/
private theorem wk_norm_bounds (hsub : V ⊆ ballAnnulus) {v : V3} (hv : v ∈ V) :
    (2 : ℝ) ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * h0 := by
  have hmem : v ∈ ballAnnulus := hsub hv
  have hlow : (2 : ℝ) ≤ ‖v‖ := by
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball] at hmem
    push_neg at hmem
    have h2 : dist v 0 = ‖v‖ := by rw [dist_eq_norm, sub_zero]
    linarith [h2]
  have hmem2 : v ∈ ballAnnulus := hsub hv
  simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball] at hmem2
  have h2 : dist v 0 = ‖v‖ := by rw [dist_eq_norm, sub_zero]
  exact ⟨hlow, h2 ▸ hmem2.1⟩

/-- ESTD 边的距离上界与端点相异（IN_ESTD 折算；§9c `yk_in_std` 核心副本）。 -/
private theorem wk_estd_dist_le {V : Set V3} {a b : V3} (h : {a, b} ∈ ESTD V) :
    a ≠ b ∧ dist a b ≤ 2 * h0 := by
  obtain ⟨x, y, he, hx, hy, hxy, hle⟩ := h
  rcases Set.pair_eq_pair_iff.mp he with hp | hp
  · exact ⟨fun hcon => hxy ((hp.1.symm.trans hcon).trans hp.2),
      by rw [hp.1, hp.2]; exact hle⟩
  · refine ⟨fun hcon => hxy ((hp.2.symm.trans hcon.symm).trans hp.1), ?_⟩
    rw [hp.1, hp.2, dist_comm]
    exact hle

/-- face 轨道 ≥ 2 元（CARD_FACE_GT_1 折算 = `CARD_FACE_GE_3_TL` 前半私有副本；
W2 只需 ≥ 2 的 ℕ-截断桥，后半（≥ 3）不在本链）。 -/
private theorem wk_card_face_ge2 (hfan : FAN 0 V E) {x : V3 × V3}
    (hx : x ∈ (hypermapOfFanTl V E hfan).darts) :
    2 ≤ ((hypermapOfFanTl V E hfan).face x).ncard := by
  have hd1 : x ∈ dart1OfFan V E := dartsTl_mem hx
  have hself : x ∈ (hypermapOfFanTl V E hfan).face x :=
    (hypermapOfFanTl V E hfan).mem_face_self x
  have hfd : (hypermapOfFanTl V E hfan).faceMap x
      ∈ (hypermapOfFanTl V E hfan).face x := apply_mem_orbitMap _ x
  have hf_d_eq : (hypermapOfFanTl V E hfan).faceMap x
      = (x.2, inverseSigmaFan 0 V E x.2 x.1) := by
    rw [faceMapTl_apply hd1]; rfl
  have hvw : x.1 ≠ x.2 := edge_ne_of_fan hfan hd1
  have hne : (hypermapOfFanTl V E hfan).faceMap x ≠ x := by
    intro he
    rw [hf_d_eq, Prod.mk.injEq] at he
    exact hvw he.1.symm
  have hpair : ({x, (hypermapOfFanTl V E hfan).faceMap x} : Set (V3 × V3))
      ⊆ (hypermapOfFanTl V E hfan).face x := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hself
    · rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hfd
  calc 2 = ({x, (hypermapOfFanTl V E hfan).faceMap x} : Set (V3 × V3)).ncard :=
      (Set.ncard_pair (Ne.symm hne)).symm
    _ ≤ ((hypermapOfFanTl V E hfan).face x).ncard := Set.ncard_le_ncard hpair
        ((hypermapOfFanTl V E hfan).face_finite x)

/-- HOL `f_surr_tau_fun_eq_tauVEF`（lp_main_estimate:523）的 Lean 折算：
face 上 `tauFun = tauVEF_p2`（逐元素 rho/azim 桥 + ℕ/ℝ 截断桥）。 -/
private theorem wk_f_surr_tauFun_eq_tauVEF (hfan : FAN 0 V E)
    (hfs : FullySurrounded V E) (hsub : V ⊆ ballAnnulus) {f : Set (V3 × V3)}
    (hf : f ∈ (hypermapOfFanTl V E hfan).faceSet) :
    tauFun V E f = tauVEF_p2 V E f := by
  obtain ⟨x, hx, hxeq⟩ :=
    Hypermap.face_representation (hypermapOfFanTl V E hfan) hf
  have hcard2 := wk_card_face_ge2 hfan hx
  have hn2 : 2 ≤ f.ncard := by rw [hxeq]; exact hcard2
  have hE : ∀ e ∈ f, rhoFun (norm e.1) * azimInFan e E
      = azimDart V E e * (1 + (sol0 / Real.pi) * (1 - lmfun (norm e.1 / 2))) := by
    intro e he
    have he1 : e ∈ (hypermapOfFanTl V E hfan).face x := by
      rw [hxeq] at he
      exact he
    have he2 : e ∈ dart1OfFan V E := by
      have h3 : e ∈ ((hypermapOfFanTl V E hfan).darts : Set (V3 × V3)) :=
        (hypermapOfFanTl V E hfan).face_subset_darts hx he1
      rwa [dartsTl_coe] at h3
    have hv1 : e.1 ∈ V := (FAN_in_setOfEdge 0 V E e.1 e.2 hfan he2).1
    have hnb := wk_norm_bounds hsub hv1
    rw [wk_rho_eq hnb.1 hnb.2, wk_azimInFan_eq_azimDart hfan he2]
    exact mul_comm _ _
  unfold tauFun tauVEF_p2 hDart_p2
  rw [wk_setSum_congr hE]
  rw [Nat.cast_sub hn2]
  ring

/-- face ∈ faceSet（faceSet 的 image 刻画的正向）。 -/
private theorem wk_face_mem_faceSet {x : V3 × V3}
    (hx : x ∈ (hypermapOfFanTl V E hfan).darts) :
    (hypermapOfFanTl V E hfan).face x ∈ (hypermapOfFanTl V E hfan).faceSet :=
  ((hypermapOfFanTl V E hfan).mem_darts_iff_face_mem x).mp hx

/-- 轨道三元刻画（HOL ORBIT_MAP_3/ORBIT_MAP_INV_3 折算）：3 元轨道 =
{x, f x, f² x} 且 f³ x = x。 -/
private theorem wk_orbit3 {α : Type*} [DecidableEq α] (f : Equiv.Perm α) (x : α)
    (h3 : (orbitMap f x).ncard = 3) :
    orbitMap f x = {x, f x, (f ^ 2) x} ∧ (f ^ 3) x = x := by
  have hstep : ∀ m : ℕ, (f ^ (m + 1)) x = f ((f ^ m) x) := by
    intro m
    simp [pow_succ', Equiv.Perm.mul_apply]
  have hmem : ∀ y ∈ ({x, f x, (f ^ 2) x} : Set α), y ∈ orbitMap f x := by
    intro y hy
    simp only [orbitMap, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hfin : (orbitMap f x).Finite := by
    by_cases htop : (orbitMap f x).encard = ⊤
    · exfalso
      have h3e : (orbitMap f x).encard.toNat = 3 := h3
      rw [htop] at h3e
      simp at h3e
    · have hcoe : ((orbitMap f x).ncard : ℕ∞) = (orbitMap f x).encard :=
        ENat.coe_toNat htop
      refine Set.finite_of_encard_le_coe (k := 3) ?_
      rw [← hcoe, h3]
  have hc1 : f x = x → orbitMap f x ⊆ ({x} : Set α) := by
    intro he y hy
    simp only [orbitMap, Set.mem_setOf_eq] at hy
    obtain ⟨n, hn⟩ := hy
    have hfix : ∀ m : ℕ, (f ^ m) x = x := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [hstep, ih, he]
    rw [← hn, hfix n]
    rfl
  have hc2 : (f ^ 2) x = x → orbitMap f x ⊆ ({x, f x} : Set α) := by
    intro he y hy
    simp only [orbitMap, Set.mem_setOf_eq] at hy
    obtain ⟨n, hn⟩ := hy
    have hmod : ∀ m : ℕ, (f ^ m) x = x ∨ (f ^ m) x = f x := by
      intro m
      induction m with
      | zero => exact Or.inl rfl
      | succ m ih =>
        rcases ih with hp | hp
        · exact Or.inr (by rw [hstep, hp])
        · exact Or.inl (by rw [hstep, hp]; exact he)
    rcases hmod n with hp | hp
    · rw [← hn, hp]; simp
    · rw [← hn, hp]; simp
  have hc3 : f x = (f ^ 2) x → orbitMap f x ⊆ ({x, f x} : Set α) := by
    intro he y hy
    simp only [orbitMap, Set.mem_setOf_eq] at hy
    obtain ⟨n, hn⟩ := hy
    have hmod : ∀ m : ℕ, (f ^ m) x = x ∨ (f ^ m) x = f x := by
      intro m
      induction m with
      | zero => exact Or.inl rfl
      | succ m ih =>
        rcases ih with hp | hp
        · exact Or.inr (by rw [hstep, hp])
        · exact Or.inr (by rw [hstep, hp]; exact he.symm)
    rcases hmod n with hp | hp
    · rw [← hn, hp]; simp
    · rw [← hn, hp]; simp
  have hxfx : f x ≠ x := by
    intro he
    have hsub := hc1 he
    have hle := Set.ncard_le_ncard hsub (Set.finite_singleton x)
    rw [Set.ncard_singleton] at hle
    omega
  have hf2x : (f ^ 2) x ≠ x := by
    intro he
    have hsub := hc2 he
    have hcard : ({x, f x} : Set α).ncard ≤ 2 := by
      rw [Set.ncard_insert_of_notMem (a := x) (by
        intro hp
        simp only [Set.mem_singleton_iff] at hp
        exact hxfx hp.symm), Set.ncard_singleton]
    have hle := Set.ncard_le_ncard hsub (by simp)
    omega
  have hfxf2 : f x ≠ (f ^ 2) x := by
    intro he
    have hsub := hc3 he
    have hcard : ({x, f x} : Set α).ncard ≤ 2 := by
      rw [Set.ncard_insert_of_notMem (a := x) (by
        intro hp
        simp only [Set.mem_singleton_iff] at hp
        exact hxfx hp.symm), Set.ncard_singleton]
    have hle := Set.ncard_le_ncard hsub (by simp)
    omega
  have hcard3 : ({x, f x, (f ^ 2) x} : Set α).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (a := x) (by
      intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hp | hp
      · exact hxfx hp.symm
      · exact hf2x hp.symm),
      Set.ncard_insert_of_notMem (a := f x) (by
        intro hp
        simp only [Set.mem_singleton_iff] at hp
        exact hfxf2 hp),
      Set.ncard_singleton]
  have heq : orbitMap f x = {x, f x, (f ^ 2) x} :=
    (Set.eq_of_subset_of_ncard_le hmem (by rw [hcard3]; exact h3.le) hfin).symm
  refine ⟨heq, ?_⟩
  have hmem3 : (f ^ 3) x ∈ orbitMap f x := pow_apply_mem_orbitMap f 3 x
  rw [heq] at hmem3
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem3
  rcases hmem3 with h | h | h
  · exact h
  · exfalso
    have h6 : f ((f ^ 2) x) = f x := show (f ^ 3) x = f x from h
    exact hf2x (Equiv.injective f h6)
  · exfalso
    have h11 : (f ^ 2) x = f x :=
      (Equiv.injective f) (show f ((f ^ 2) x) = f (f x) from h)
    exact hfxf2 h11.symm

/-- dart1 上的 σ 像点仍是 dart1（sigma_in_dart1 折算）。 -/
private theorem wk_sigma_mem_dart1 (hfan : FAN 0 V E) {v w : V3}
    (hd : (v, w) ∈ dart1OfFan V E) :
    (v, sigmaFan 0 V E v w) ∈ dart1OfFan V E := by
  have hmemV := FAN_in_setOfEdge 0 V E v w hfan hd
  have hs : sigmaFan 0 V E v w ∈ setOfEdge v V E :=
    sigma_fan_in_setOfEdge hfan hmemV.2.2.1
  exact (properties_of_setOfEdge_fan 0 V E v (sigmaFan 0 V E v w) hfan).mpr hs

/-- HOL `azim_dart_eq_dihV`（lp_ineqs_proofs:1096，FullySurroundedAddDiag 节）
折算：FullySurrounded 下 dart 的方位角即二面角。 -/
private theorem wk_azimDart_eq_dihV (hfan : FAN 0 V E) (hfs : FullySurrounded V E)
    {v w : V3} (hd : (v, w) ∈ dart1OfFan V E) :
    azimDart V E (v, w) = dihV 0 v w (sigmaFan 0 V E v w) := by
  have hπ : azimDart V E (v, w) < Real.pi := hfs (v, w) (Set.mem_union_right _ hd)
  by_cases hnc : (setOfEdge v V E).ncard > 1
  · have hbr : azimDart V E (v, w) = azim 0 v w (sigmaFan 0 V E v w) := by
      show (if (v : V3) = w then (2 : ℝ) * Real.pi
        else if (setOfEdge v V E).ncard > 1
          then azim 0 v w (sigmaFan 0 V E v w) else 2 * Real.pi)
        = azim 0 v w (sigmaFan 0 V E v w)
      rw [if_neg (edge_ne_of_fan hfan hd), if_pos hnc]
    rw [hbr] at hπ
    have hncol1 : ¬ Collinear3 0 v w := hfan.2.2.2.2.1 {v, w} hd
    have hd' : (v, sigmaFan 0 V E v w) ∈ dart1OfFan V E := wk_sigma_mem_dart1 hfan hd
    have hncol2 : ¬ Collinear3 0 v (sigmaFan 0 V E v w) :=
      hfan.2.2.2.2.1 {v, sigmaFan 0 V E v w} hd'
    rw [hbr, azim_dihv_same hncol1 hncol2 hπ]
  · have h2pi : azimDart V E (v, w) = 2 * Real.pi := by
      show (if (v : V3) = w then (2 : ℝ) * Real.pi
        else if (setOfEdge v V E).ncard > 1
          then azim 0 v w (sigmaFan 0 V E v w) else 2 * Real.pi)
        = (2 : ℝ) * Real.pi
      rw [if_neg (edge_ne_of_fan hfan hd),
        if_neg (by omega : ¬ (setOfEdge v V E).ncard > 1)]
    rw [h2pi] at hπ
    linarith [Real.pi_pos]

/-- HOL `TRIANGULAR_FACE` + `f_fan_pair3`（hypermap_and_fan.hl:1222 /
add_triangle-compiled.hl:608）合并折算：3 元面 = {d, f d, f² d} 的显式循环。 -/
private theorem wk_fan3 (hfan : FAN 0 V E) {v w : V3} (hd : (v, w) ∈ dart1OfFan V E)
    (h3 : ((hypermapOfFanTl V E hfan).face (v, w)).ncard = 3) :
    (hypermapOfFanTl V E hfan).face (v, w) =
      ({(v, w), (w, sigmaFan 0 V E v w), (sigmaFan 0 V E v w, v)} : Set (V3 × V3)) ∧
    (hypermapOfFanTl V E hfan).faceMap (v, w) = (w, sigmaFan 0 V E v w) ∧
    (hypermapOfFanTl V E hfan).faceMap (w, sigmaFan 0 V E v w) =
      (sigmaFan 0 V E v w, v) ∧
    (hypermapOfFanTl V E hfan).faceMap (sigmaFan 0 V E v w, v) = (v, w) ∧
    sigmaFan 0 V E w (sigmaFan 0 V E v w) = v ∧
    sigmaFan 0 V E (sigmaFan 0 V E v w) v = w ∧
    (w, sigmaFan 0 V E v w) ∈ dart1OfFan V E ∧
    (sigmaFan 0 V E v w, v) ∈ dart1OfFan V E := by
  have hba : {w, v} ∈ E := by rw [Set.pair_comm]; exact hd
  -- f d = (w, u)，u = inverse1 σ_w v 的两条性质（INVERSE1_SIGMA_FAN 直取）
  obtain ⟨u, hfd1, hu_soe, hu_sig⟩ :
      ∃ u, (hypermapOfFanTl V E hfan).faceMap (v, w) = (w, u) ∧
        u ∈ setOfEdge w V E ∧ sigmaFan 0 V E w u = v := by
    refine ⟨inverse1SigmaFan 0 V E w v, ?_, ?_, ?_⟩
    · have h6 : (hypermapOfFanTl V E hfan).faceMap (v, w)
          = (w, inverseSigmaFan 0 V E w v) := by
        rw [faceMapTl_apply hd]; rfl
      rw [h6, ← inverse_sigma_fan_eq_inverse1 hfan hba]
    · have h1 : {w, inverse1SigmaFan 0 V E w v} ∈ E := (INVERSE1_SIGMA_FAN hfan).1 v hba
      exact (properties_of_setOfEdge_fan 0 V E w (inverse1SigmaFan 0 V E w v) hfan).mp h1
    · exact (INVERSE1_SIGMA_FAN hfan).2.1 v hba
  have hdu : (w, u) ∈ dart1OfFan V E := by
    have h6 : fFanPair 0 V E (v, w) = (w, u) := by
      rw [← faceMapTl_apply hd]; exact hfd1
    rw [← h6]
    exact fFanPair_mem_dart1 hfan hd
  -- f (w, u) = (u, u2)，u2 = inverse1 σ_u w
  obtain ⟨u2, hfd2, hu2_soe, hu2_sig⟩ :
      ∃ u2, (hypermapOfFanTl V E hfan).faceMap (w, u) = (u, u2) ∧
        u2 ∈ setOfEdge u V E ∧ sigmaFan 0 V E u u2 = w := by
    have hwu : w ∈ setOfEdge u V E := by
      have hmem := FAN_in_setOfEdge 0 V E w u hfan hdu
      exact hmem.2.2.2
    refine ⟨inverse1SigmaFan 0 V E u w, ?_, ?_, ?_⟩
    · have huw : {u, w} ∈ E := by rw [Set.pair_comm]; exact hdu
      have h6 : (hypermapOfFanTl V E hfan).faceMap (w, u)
          = (u, inverseSigmaFan 0 V E u w) := by
        rw [faceMapTl_apply hdu]; rfl
      rw [h6, ← inverse_sigma_fan_eq_inverse1 hfan huw]
    · have huw : {u, w} ∈ E := by rw [Set.pair_comm]; exact hdu
      have h1 : {u, inverse1SigmaFan 0 V E u w} ∈ E := (INVERSE1_SIGMA_FAN hfan).1 w huw
      exact (properties_of_setOfEdge_fan 0 V E u (inverse1SigmaFan 0 V E u w) hfan).mp h1
    · have huw : {u, w} ∈ E := by rw [Set.pair_comm]; exact hdu
      exact (INVERSE1_SIGMA_FAN hfan).2.1 w huw
  have hdu2 : (u, u2) ∈ dart1OfFan V E := by
    have h6 : fFanPair 0 V E (w, u) = (u, u2) := by
      rw [← faceMapTl_apply hdu]; exact hfd2
    rw [← h6]
    exact fFanPair_mem_dart1 hfan hdu
  -- 轨道三元 + f³d = d
  obtain ⟨horb, hfd3⟩ := wk_orbit3 (hypermapOfFanTl V E hfan).faceMap (v, w) h3
  -- f⁻¹ d = (σ_v w, v)
  have hz : (hypermapOfFanTl V E hfan).faceMap (sigmaFan 0 V E v w, v) = (v, w) := by
    have hsym : {sigmaFan 0 V E v w, v} ∈ E := by
      have hs : sigmaFan 0 V E v w ∈ setOfEdge v V E :=
        sigma_fan_in_setOfEdge hfan (FAN_in_setOfEdge 0 V E v w hfan hd).2.2.1
      rw [Set.pair_comm]
      exact (properties_of_setOfEdge_fan 0 V E v (sigmaFan 0 V E v w) hfan).mpr hs
    have hz1 : (sigmaFan 0 V E v w, v) ∈ dart1OfFan V E :=
      (properties_of_setOfEdge_fan 0 V E (sigmaFan 0 V E v w) v hfan).mpr
        ⟨hsym, FAN_EDGE_EL_V hfan hsym⟩
    have hz2 : (hypermapOfFanTl V E hfan).faceMap (sigmaFan 0 V E v w, v)
        = fFanPairExt 0 V E (sigmaFan 0 V E v w, v) := by
      rw [faceMapTl_apply hz1]
      simp only [fFanPairExt, if_pos hz1]
    have hedg : {v, sigmaFan 0 V E v w} ∈ E := by
      rw [Set.pair_comm]; exact hz1
    have hinv : inverseSigmaFan 0 V E v (sigmaFan 0 V E v w) = w := by
      have h3' := (INVERSE1_SIGMA_FAN hfan).2.2 w hd
      rw [inverse_sigma_fan_eq_inverse1 hfan hedg] at h3'
      exact h3'
    rw [hz2]
    simp only [fFanPairExt, if_pos hz1, fFanPair]
    rw [hinv]
  -- f² d = f⁻¹ d = (σ_v w, v)
  have hfd3' : (hypermapOfFanTl V E hfan).faceMap
      ((hypermapOfFanTl V E hfan).faceMap ((hypermapOfFanTl V E hfan).faceMap (v, w)))
      = (v, w) := by
    simpa [pow_succ, pow_two, Equiv.Perm.mul_apply] using hfd3
  have hfd2z : (hypermapOfFanTl V E hfan).faceMap
      ((hypermapOfFanTl V E hfan).faceMap (v, w)) = (sigmaFan 0 V E v w, v) := by
    have h7 : (hypermapOfFanTl V E hfan).faceMap
        ((hypermapOfFanTl V E hfan).faceMap (v, w))
        = (hypermapOfFanTl V E hfan).faceMap.symm (v, w) :=
      (hypermapOfFanTl V E hfan).faceMap.injective
        (hfd3'.trans (Equiv.apply_symm_apply _ _).symm)
    have hsymm_eq : (sigmaFan 0 V E v w, v)
        = (hypermapOfFanTl V E hfan).faceMap.symm (v, w) :=
      (Equiv.apply_eq_iff_eq_symm_apply _).mp hz
    rw [h7, ← hsymm_eq]
  -- 逐分量读出 u = σ_v w，u2 = v
  have hcomp : (u, u2) = (sigmaFan 0 V E v w, v) := by
    rw [← hfd2, ← hfd1]
    exact hfd2z
  simp only [Prod.mk.injEq] at hcomp
  obtain ⟨hu1, hu22⟩ := hcomp
  have hfd4u : (hypermapOfFanTl V E hfan).faceMap (u, u2) = (v, w) := by
    rw [hfd1] at hfd3'
    rw [hfd2] at hfd3'
    exact hfd3'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (hypermapOfFanTl V E hfan).face (v, w)
          = orbitMap (hypermapOfFanTl V E hfan).faceMap (v, w) from rfl, horb,
      show ((hypermapOfFanTl V E hfan).faceMap ^ 2) (v, w)
          = (hypermapOfFanTl V E hfan).faceMap
            ((hypermapOfFanTl V E hfan).faceMap (v, w)) from rfl,
      hfd1, hfd2, hu1, hu22]
  · rw [hfd1, hu1]
  · rw [← hu1, hfd2, hu22]
  · conv_lhs => rw [← hu1, ← hu22]
    exact hfd4u
  · rw [← hu1]; exact hu_sig
  · rw [← hu1, ← hu22]; exact hu2_sig
  · rw [← hu1]; exact hdu
  · rw [← hu1, ← hu22]; exact hdu2

/-- HOL `tau3_eq_tau_fun`（lp_main_estimate:494）的 Lean 折算。 -/
private theorem wk_tau3_eq_tauFun (hfan : FAN 0 V E) (hfs : FullySurrounded V E)
    {v w : V3} (hd : (v, w) ∈ dart1OfFan V E)
    (h3 : ((hypermapOfFanTl V E hfan).face (v, w)).ncard = 3) :
    tau3 (sigmaFan 0 V E v w) v w
      = tauFun V E ((hypermapOfFanTl V E hfan).face (v, w)) := by
  obtain ⟨hfeq, -, -, -, hσw, hσw', hdu, hdu2⟩ := wk_fan3 hfan hd h3
  have e1 : azimInFan (v, w) E = dihV 0 v w (sigmaFan 0 V E v w) := by
    rw [wk_azimInFan_eq_azimDart hfan hd]
    exact wk_azimDart_eq_dihV hfan hfs hd
  have e2 : azimInFan (w, sigmaFan 0 V E v w) E = dihV 0 w (sigmaFan 0 V E v w) v := by
    have h1 : azimInFan (w, sigmaFan 0 V E v w) E
        = azimDart V E (w, sigmaFan 0 V E v w) := wk_azimInFan_eq_azimDart hfan hdu
    have h2 : azimDart V E (w, sigmaFan 0 V E v w)
        = dihV 0 w (sigmaFan 0 V E v w) (sigmaFan 0 V E w (sigmaFan 0 V E v w)) :=
      wk_azimDart_eq_dihV hfan hfs hdu
    rw [h1, h2]
    exact congrArg (dihV 0 w (sigmaFan 0 V E v w)) hσw
  have e3 : azimInFan (sigmaFan 0 V E v w, v) E
      = dihV 0 (sigmaFan 0 V E v w) v w := by
    have h1 : azimInFan (sigmaFan 0 V E v w, v) E
        = azimDart V E (sigmaFan 0 V E v w, v) := wk_azimInFan_eq_azimDart hfan hdu2
    have h2 : azimDart V E (sigmaFan 0 V E v w, v)
        = dihV 0 (sigmaFan 0 V E v w) v
          (sigmaFan 0 V E (sigmaFan 0 V E v w) v) := wk_azimDart_eq_dihV hfan hfs hdu2
    rw [h1, h2]
    exact congrArg (dihV 0 (sigmaFan 0 V E v w) v) hσw'
  have hfin : ({(w, sigmaFan 0 V E v w), (sigmaFan 0 V E v w, v)} :
      Set (V3 × V3)).Finite := by simp
  have hne1 : v ≠ w := edge_ne_of_fan hfan hd
  have hne2 : w ≠ sigmaFan 0 V E v w := edge_ne_of_fan hfan hdu
  have hne3 : sigmaFan 0 V E v w ≠ v := edge_ne_of_fan hfan hdu2
  have g1 : rhoFun (norm (v, w).1) * azimInFan (v, w) E
      = rho (norm v) * dihV 0 v w (sigmaFan 0 V E v w) := by
    rw [e1, rho_rho_fun]
  have g2 : rhoFun (norm (w, sigmaFan 0 V E v w).1) * azimInFan (w, sigmaFan 0 V E v w) E
      = rho (norm w) * dihV 0 w (sigmaFan 0 V E v w) v := by
    rw [e2, rho_rho_fun]
  have g3 : rhoFun (norm (sigmaFan 0 V E v w, v).1) * azimInFan (sigmaFan 0 V E v w, v) E
      = rho (norm (sigmaFan 0 V E v w)) * dihV 0 (sigmaFan 0 V E v w) v w := by
    rw [e3, rho_rho_fun]
  unfold tauFun
  rw [h3, hfeq,
    wk_setSum_insert (s := {(w, sigmaFan 0 V E v w), (sigmaFan 0 V E v w, v)})
      (a := (v, w)) (by
        intro hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hc
        exact hc.elim (fun h => hne1 h.1) (fun h => hne3 h.1.symm))
      hfin,
    wk_setSum_insert (s := {(sigmaFan 0 V E v w, v)}) (a := (w, sigmaFan 0 V E v w))
      (by
        intro hc
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hc
        exact hne2 hc.1)
      (by simp)]
  have hsing : setSum ({(sigmaFan 0 V E v w, v)} : Set (V3 × V3))
      (fun e => rhoFun (norm e.1) * azimInFan e E)
      = rhoFun (norm (sigmaFan 0 V E v w, v).1) * azimInFan (sigmaFan 0 V E v w, v) E := by
    simp [setSum]
  simp only []
  rw [hsing, g1, g2, g3]
  have hone : ((3 - 2 : ℕ) : ℝ) = 1 := by norm_num
  rw [hone, mul_one]
  unfold tau3
  ring

/-- HOL `f_surr_tau3_eq_tauVEF`（lp_main_estimate:542）的 Lean 折算：
tau3 = tauFun = tauVEF 两步装配。 -/
private theorem wk_f_surr_tau3_eq_tauVEF (hfan : FAN 0 V E) (hfs : FullySurrounded V E)
    (hsub : V ⊆ ballAnnulus) {v w : V3} (hd : (v, w) ∈ dart1OfFan V E)
    (h3 : ((hypermapOfFanTl V E hfan).face (v, w)).ncard = 3) :
    tau3 (sigmaFan 0 V E v w) v w
      = tauVEF_p2 V E ((hypermapOfFanTl V E hfan).face (v, w)) :=
  (wk_tau3_eq_tauFun hfan hfs hd h3).trans
    (wk_f_surr_tauFun_eq_tauVEF hfan hfs hsub (wk_face_mem_faceSet (mem_dartsTl hd)))

end W2Kit







/-! ### 3a. ineq_tauK_tauVEF_std 群（lp_main_estimate-compiled.hl，
section MainEstimate（h_fan := lp_fan，:568-571）× FaceK（ineq := JEJTVGB_*_concl）
× Std（E = ESTD V）的 finalized 形；K = 3,4,5,6。
MQMSMAB 证明体 :59-66 逐条消费。`face (hypermap_of_fan (V,ESTD V)) d` 的
支持集约束 `d ∈ darts_k k H` 镜像为 `d ∈ dartsK k H`。 -/

/-- HOL `ineq_tau3_tauVEF_std`（`lp_main_estimate-compiled.hl:714-731`）。
DISCHARGES：骨架占位；HOL 证明 4 步（`ineq_tau3_tauVEF` + y4/y5/y6_hi_std2），
深依赖 Face3 分支不等式链。 -/
theorem ineq_tau3_tauVEF_std (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std3_concl) (d : V3 × V3)
    (hd : d ∈ dartsK 3 (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    0 ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
  -- W2 装配（Lane P 2026-10-23）：JEJTVGB_std3_concl 在 (σ_v w, v, w) 上的
  -- 12 件数值前提逐一由 dart1/ESTD/Packing/ballAnnulus 直接给出，再经
  -- wk_f_surr_tau3_eq_tauVEF（tau3 = tauFun = tauVEF 两步桥）回写目标。
  obtain ⟨hdarts, hcard3⟩ := hd
  obtain ⟨v, w⟩ := d
  have hfan : FAN 0 V (ESTD V) := hlpfan.1
  have hfs : FullySurrounded V (ESTD V) := hlpfan.2.1
  have hsub : V ⊆ ballAnnulus := hlpfan.2.2.2.1
  have hpack : Packing V := hlpfan.2.2.2.2
  have hd1 : (v, w) ∈ dart1OfFan V (ESTD V) := dartsTl_mem hdarts
  obtain ⟨-, -, -, -, -, -, hdu, hdu2⟩ := wk_fan3 hfan hd1 hcard3
  -- 三条边及其 ESTD/Packing 距离界（dist ≤ 2h0 由 ESTD，≥ 2 由 Packing）
  have he1 : {v, w} ∈ ESTD V := hd1
  have he2 : {w, sigmaFan 0 V (ESTD V) v w} ∈ ESTD V := hdu
  have he3 : {sigmaFan 0 V (ESTD V) v w, v} ∈ ESTD V := hdu2
  have hne1 : v ≠ w := edge_ne_of_fan hfan he1
  have hne2 : w ≠ sigmaFan 0 V (ESTD V) v w := edge_ne_of_fan hfan he2
  have hne3 : sigmaFan 0 V (ESTD V) v w ≠ v := edge_ne_of_fan hfan he3
  have hvV : v ∈ V := (FAN_in_setOfEdge 0 V (ESTD V) v w hfan hd1).1
  have hwV : w ∈ V := (FAN_in_setOfEdge 0 V (ESTD V) v w hfan hd1).2.1
  have hw'V : sigmaFan 0 V (ESTD V) v w ∈ V := FAN_EDGE_EL_V hfan he2
  obtain ⟨hnv, hnv2⟩ := wk_norm_bounds hsub hvV
  obtain ⟨hnw, hnw2⟩ := wk_norm_bounds hsub hwV
  obtain ⟨hnw', hnw'2⟩ := wk_norm_bounds hsub hw'V
  have hd_ge1 : 2 ≤ dist v w := Packing.dist_ge_two hpack hvV hwV hne1
  have hd_ge2 : 2 ≤ dist w (sigmaFan 0 V (ESTD V) v w) :=
    Packing.dist_ge_two hpack hwV hw'V hne2
  have hd_ge3 : 2 ≤ dist (sigmaFan 0 V (ESTD V) v w) v := by
    rw [dist_comm]
    exact Packing.dist_ge_two hpack hvV hw'V (fun hc => hne3 hc.symm)
  have hd_ge2' : 2 ≤ dist (sigmaFan 0 V (ESTD V) v w) w := by
    rw [dist_comm]; exact hd_ge2
  have hle1 := (wk_estd_dist_le he1).2
  have hle2' := (wk_estd_dist_le he2).2
  have hle3 := (wk_estd_dist_le he3).2
  have hle2'' : dist (sigmaFan 0 V (ESTD V) v w) w ≤ 2 * h0 := by
    rw [dist_comm]; exact hle2'
  -- JEJTVGB_std3_concl 在 (v1, v2, v3) = (σ_v w, v, w) 上的实例
  have key := hineq (sigmaFan 0 V (ESTD V) v w) v w
    hnw' hnv hnw hnw'2 hnv2 hnw2
    hd_ge3 hd_ge2' hd_ge1 hle3 hle2'' hle1
  rw [← wk_f_surr_tau3_eq_tauVEF hfan hfs hsub hd1 hcard3]
  exact key

/-! ### 3b. W3 kit（Lane V 2026-10-23）：dTame 数值件（W4 Std 装配消费——
bank 结论 `dTame (vPrime.ncard)` 折算数值用；插入点在目标群之前防前向引用）。 -/

/-- `dTame 4 = 0.206`（`dTame` if 链的第二支，核层可直接判定）。 -/
private theorem wk_dtame4 : dTame 4 = 0.206 := rfl

/-- `dTame 5 = 0.4819`. -/
private theorem wk_dtame5 : dTame 5 = 0.4819 := rfl

/-- `dTame 6 = 0.712`. -/
private theorem wk_dtame6 : dTame 6 = 0.712 := rfl


/-! ## 4. JGTDEBU 群（tame/JGTDEBU.hl，"general properties of a
contravening packing"，Solovyev 2013）。
偏差注记：HOL `hypermap_of_fan` 全函数；Lean 侧每条显式携带
`FAN 0 V (ESTD V)` 前提（Assembly §2c `mqmsmab` 同一模式）。
HOL 文件编号 1–8、10、11（无 JGTDEBU9）。 -/

/-- HOL `contravening_imp_conforming`（JGTDEBU.hl:20-40）的 Lean 折算：
`Contravening V` + FAN 见证给 `conformingFan 0 V (ESTD V)`。
HOL 证明 4 步：`PIIJBJK` + `SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3`
（本文 `SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL`）+ `AZIM_DART_POS` /
`CONTRAVENING_IMP_AZIM_DART_EQ_AZIM`（fan80 两半）+ fully_surrounded；
正性半步由 `azim_nonneg` + `unique_azim0_point_fan`（azim = 0 ⟹ u = σ v u，
与 SIGMA_FAN 第二条件矛盾）收口。 -/
theorem contraveningConformingTl (V : Set V3) (hc : Contravening V)
    (hfan : FAN 0 V (ESTD V)) : conformingFan 0 V (ESTD V) hfan := by
  have hsurr : ∀ v ∈ V, surroundedNode V (ESTD V) v := hc.2.2.2.2.2.1
  have hcard3 : ∀ v ∈ V, 3 ≤ (setOfEdge v V (ESTD V)).ncard := fun v hv =>
    SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hv (hsurr v hv)
  have hcard : ∀ v ∈ V, 1 < (setOfEdge v V (ESTD V)).ncard := fun v hv =>
    lt_of_lt_of_le (by omega) (hcard3 v hv)
  have hfan80 : fan80 0 V (ESTD V) := by
    intro v u he
    have hvV : v ∈ V := (FAN_in_setOfEdge 0 V (ESTD V) v u hfan he).1
    have hd1 : (v, u) ∈ dart1OfFan V (ESTD V) := he
    have hlt : azimDart V (ESTD V) (v, u) < Real.pi :=
      hsurr v hvV (v, u) (Set.mem_union_right _ hd1) rfl
    have hne : v ≠ u := edge_ne_of_fan hfan he
    have heq : azimDart V (ESTD V) (v, u) = azim 0 v u (sigmaFan 0 V (ESTD V) v u) := by
      show (if (v, u).1 = (v, u).2 then 2 * Real.pi else
        if (setOfEdge (v, u).1 V (ESTD V)).ncard > 1 then
          azim 0 (v, u).1 (v, u).2 (sigmaFan 0 V (ESTD V) (v, u).1 (v, u).2)
        else 2 * Real.pi) = _
      have hgt : (setOfEdge (v, u).1 V (ESTD V)).ncard > 1 :=
        lt_of_lt_of_le (by omega : (1:ℕ) < 3) (hcard3 v hvV)
      rw [if_neg hne, if_pos hgt]
    rw [heq] at hlt
    refine ⟨?_, hlt⟩
    refine lt_of_le_of_ne (azim_nonneg 0 v u _) ?_
    intro h0
    have hsoene : setOfEdge v V (ESTD V) ≠ {u} := by
      intro h1
      have := hcard3 v hvV
      rw [h1, Set.ncard_singleton] at this
      omega
    have hsig := SIGMA_FAN hsoene hfan
      ((properties_of_setOfEdge_fan 0 V (ESTD V) v u hfan).mp he)
    exact hsig.2.1 (unique_azim0_point_fan hfan he
      ((properties_of_setOfEdge_fan 0 V (ESTD V) v (sigmaFan 0 V (ESTD V) v u) hfan).mpr
        hsig.1) h0.symm).symm
  exact PIIJBJK 0 V (ESTD V) hfan ⟨hfan, hcard, hfan80⟩

/-- HOL `JGTDEBU1`（`tame/JGTDEBU.hl:49-57`）：planar。
HOL 证明经 `CONTRAVENING_FAN` + `fan_hypermaps_iso` + `iso_planar` +
`Conforming.GGRLKHP`；此处 Conforming 章 twin（GGRLKHP，ConformingAuto23）
直接可用，桥件为 `contraveningConformingTl`。 -/
theorem JGTDEBU1 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    (hypermapOfFanTl V (ESTD V) hfan).Planar :=
  PlanarTl hfan (GGRLKHP 0 V (ESTD V) hfan (contraveningConformingTl V hc hfan))

/-- HOL `JGTDEBU2`（`tame/JGTDEBU.hl:61-65`）：plain。
HOL 证明 `PLAIN_HYPERMAP_OF_FAN` 一步；此处 `PLAIN_HYPERMAP_OF_FAN`
（hypermap_and_fan.hl:1360）按 `hypermapOfFan` 的 `extendPerm` 构造直接
展开：`eFanPair` 在 dart1 上为对合（`eFanPair_sq`），轨道外恒等。 -/
theorem JGTDEBU2 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    (hypermapOfFanTl V (ESTD V) hfan).Plain := by
  unfold Hypermap.Plain
  refine Equiv.Perm.ext fun x => ?_
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  by_cases hx : x ∈ dart1OfFan V (ESTD V)
  · rw [edgeMapTl_apply hx, edgeMapTl_apply (eFanPair_mem_dart1 hx), eFanPair_sq x hx]
  · have e1 : (hypermapOfFanTl V (ESTD V) hfan).edgeMap x = x := edgeMapTl_of_notMem hx
    rw [e1, e1]

/-- HOL `JGTDEBU3`（`tame/JGTDEBU.hl:69-77`）：connected。
同 JGTDEBU1 路径（`iso_connected` + `Conforming.WGVWSKE` twin）。 -/
theorem JGTDEBU3 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    (hypermapOfFanTl V (ESTD V) hfan).Connected :=
  ConnectedTl hfan (WGVWSKE 0 V (ESTD V) hfan (contraveningConformingTl V hc hfan))

/-- HOL `JGTDEBU4`（`tame/JGTDEBU.hl:81-89`）：simple。
同 JGTDEBU1 路径（`iso_simple` + `Conforming.SRPRNPL` twin，
ConformingAuto1）。MQMSMAB :36 与 KCBLRQC 证明以其为枢纽。 -/
theorem JGTDEBU4 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    (hypermapOfFanTl V (ESTD V) hfan).Simple :=
  SimpleTl hfan (SRPRNPL hfan (contraveningConformingTl V hc hfan))

/-- HOL `JGTDEBU5`（`tame/JGTDEBU.hl:93-97`）：edge-nondegenerate。
HOL 经 `HYPERMAP_OF_FAN_EDGE_NONDEGENERATE`；此处 edge 非退化即
`PAIR_IN_DART1_OF_FAN_IMP_NOT_EQ`（`edge_ne_of_fan`：{v,w} ∈ E ⟹ v ≠ w）
+ dart 层展开，`fully_surrounded` 前提在 Lean 折算形（dart 集 =
`dart1OfFan`）下不需要。 -/
theorem JGTDEBU5 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    (hypermapOfFanTl V (ESTD V) hfan).EdgeNondegenerate := by
  unfold Hypermap.EdgeNondegenerate
  intro d hd
  have hd1 : d ∈ dart1OfFan V (ESTD V) := dartsTl_mem hd
  rw [edgeMapTl_apply hd1]
  show (d.2, d.1) ≠ d
  intro h
  exact edge_ne_of_fan hfan hd1 (congrArg Prod.fst h).symm

/-- HOL `JGTDEBU6`（`tame/JGTDEBU.hl:101-105`）：no_loops。
HOL 经 `HYPERMAP_OF_FAN_NO_LOOPS`；此处：edge-轨道 = `{d, eFanPair d}`
（`edgeMapTl_iterate`），node-轨道第一分量恒为 `d.1`
（`nodeMapTl_iterate`），`(d.2,d.1) ∈ node d` 迫使 `d.1 = d.2`，与
`edge_ne_of_fan` 矛盾；轨道外两映射恒等。 -/
theorem JGTDEBU6 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    Tame4 (hypermapOfFanTl V (ESTD V) hfan) := by
  unfold Tame4 NoLoops
  intro x y hex hyn
  simp only [Hypermap.edge, orbitMap, Set.mem_setOf_eq] at hex
  simp only [Hypermap.node, orbitMap, Set.mem_setOf_eq] at hyn
  obtain ⟨k, hk⟩ := hex
  obtain ⟨m, hm⟩ := hyn
  rw [Equiv.Perm.coe_pow] at hk hm
  by_cases hy : y ∈ dart1OfFan V (ESTD V)
  · rcases edgeMapTl_iterate y hy k with hx | hx
    · rw [← hk, hx]
    · -- x = (y.2, y.1) 又 = (y.1, σ^[m] y.2) ⟹ y.2 = y.1，与 edge_ne_of_fan 矛盾
      have hx' : (hypermapOfFanTl V (ESTD V) hfan).edgeMap^[k] y = (y.2, y.1) := hx
      have e1 : (y.2, y.1) = x := hx'.symm.trans hk
      have e2 : (y.1, (sigmaFan 0 V (ESTD V) y.1)^[m] y.2) = x :=
        (nodeMapTl_iterate hy m).symm.trans hm
      exact (edge_ne_of_fan hfan hy
        (congrArg Prod.fst (e1.trans e2.symm)).symm).elim
  · exact hk.symm.trans
      (iterate_of_notMemTl hy k _ (fun z hz => edgeMapTl_of_notMem hz))

/-- HOL `JGTDEBU7`（`tame/JGTDEBU.hl:109-113`）：no_double_joins。
HOL 经 `HYPERMAP_OF_FAN_NO_DOUBLE_JOINTS`；此处：`v ∈ node u` 给
`v.1 = u.1`（node-轨道第一分量不变），`edgeMap v ∈ node (edgeMap u)` 给
`v.2 = u.2`（同理于反转 dart），两分量相等即 `u = v`。 -/
theorem JGTDEBU7 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    Tame5a (hypermapOfFanTl V (ESTD V) hfan) := by
  unfold Tame5a Hypermap.IsNoDoubleJoins
  intro u v hu hvn hjoin
  simp only [Hypermap.node, orbitMap, Set.mem_setOf_eq] at hvn hjoin
  obtain ⟨k, hk⟩ := hvn
  obtain ⟨m, hm⟩ := hjoin
  rw [Equiv.Perm.coe_pow] at hk hm
  have hu1 : u ∈ dart1OfFan V (ESTD V) := dartsTl_mem hu
  -- v ∈ node u ⟹ v = (u.1, σ^[k] u.2)
  have hvnode : v = (u.1, (sigmaFan 0 V (ESTD V) u.1)^[k] u.2) := by
    rw [← hk, nodeMapTl_iterate hu1 k]
  -- edgeMap v ∈ node (edgeMap u) ⟹ (v.2, v.1) = (u.2, σ^[m] u.1)
  have huE : (u.2, u.1) ∈ dart1OfFan V (ESTD V) := eFanPair_mem_dart1 hu1
  have hv1 : v ∈ dart1OfFan V (ESTD V) := by
    rw [hvnode]
    exact nodeIterateTl_mem hfan hu1 k
  have hjoin' : (v.2, v.1) = (u.2, (sigmaFan 0 V (ESTD V) u.2)^[m] u.1) := by
    rw [edgeMapTl_apply hu1, edgeMapTl_apply hv1] at hm
    simp only [eFanPair] at hm
    rw [← hm, nodeMapTl_iterate huE m]
  exact Prod.ext (congrArg Prod.fst hvnode).symm (congrArg Prod.fst hjoin').symm

/-- HOL `JGTDEBU8（`tame/JGTDEBU.hl:133-210`）：`number_of_faces ≥ 3`。
HOL 证明约 30 步（`DART_EXISTS` + surrounded 取真 dart +
`SIMPLE_HYPERMAP_lemma`（face 在 node 轨道上单射的计数）+
`SURROUNDED_IMP_CARD_NODE_GE_3`）；此处按同一结构：face 像
`H.face '' node (v,w)` 既含于 `faceSet`（单射下基数相等）又 ≥ 3。 -/
theorem JGTDEBU8 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    Tame8 (hypermapOfFanTl V (ESTD V) hfan) := by
  set H := hypermapOfFanTl V (ESTD V) hfan with hHdef
  have hsimple : H.Simple := JGTDEBU4 V hc hfan
  have hsurr : ∀ v ∈ V, surroundedNode V (ESTD V) v := hc.2.2.2.2.2.1
  -- V 非空（基数 13–15）
  have hvne : V ≠ ∅ := by
    intro he
    have h13 := hc.2.2.2.2.1
    rw [he, Set.ncard_empty] at h13
    omega
  obtain ⟨v, hvV⟩ := Set.nonempty_iff_ne_empty.mpr hvne
  -- DART_EXISTS + surrounded 取真 dart (v,w)
  obtain ⟨w, hw⟩ := DART_EXISTS_TL hfan v hvV
  have hlt : azimDart V (ESTD V) (v, w) < Real.pi := hsurr v hvV (v, w) hw rfl
  have hvw : v ≠ w := by
    intro he
    subst he
    have h2pi : azimDart V (ESTD V) (v, v) = 2 * Real.pi := by simp [azimDart]
    rw [h2pi] at hlt
    linarith [Real.pi_pos]
  have hd1 : (v, w) ∈ dart1OfFan V (ESTD V) := by
    rcases (Set.mem_union _ _ _).mp hw with h | h
    · exact absurd h.out.1 hvw
    · exact h
  have hdarts : (v, w) ∈ H.darts := mem_dartsTl hd1
  -- face 单射于 node (v,w)（SIMPLE_HYPERMAP_lemma 的计数核）
  have hinj : Set.InjOn (fun y => H.face y) (H.node (v, w)) :=
    faceInjOn_of_node hsimple (v, w) hdarts
  have hnode3 : 3 ≤ ((fun y => H.face y) '' H.node (v, w)).ncard := by
    rw [Set.InjOn.ncard_image hinj]
    exact SURROUNDED_IMP_CARD_NODE_GE_3_TL hfan hd1 (hsurr v hvV)
  -- face 像含于 faceSet
  have hsub : ((fun y => H.face y) '' H.node (v, w)) ⊆ H.faceSet := by
    intro f hf
    obtain ⟨y, hy, rfl⟩ := (Set.mem_image _ _ _).mp hf
    exact ⟨y, H.node_subset_darts hdarts hy, rfl⟩
  have hle := Set.ncard_le_ncard hsub H.faceSet_finite
  show 3 ≤ H.faceSet.ncard
  exact le_trans hnode3 hle

/-- HOL `JGTDEBU10`（`tame/JGTDEBU.hl:215-236`）：`tame_10`（节点数 13–15）。
HOL 证明经 `NODE_SET_AS_IMAGE` + `CARD_IMAGE_INJ`；此处：node 轨道只依赖
dart 第一分量（`nodeTl_eq_image` + 单循环 `orbit_eq_setOfEdge`），故
`nodeSet = (v ↦ (v,·) '' setOfEdge v) '' V`，再由第一分量恢复的单射 +
`contravening` 的基数合取收口。 -/
theorem JGTDEBU10 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    Tame10 (hypermapOfFanTl V (ESTD V) hfan) := by
  set H := hypermapOfFanTl V (ESTD V) hfan with hHdef
  have hsurr : ∀ v ∈ V, surroundedNode V (ESTD V) v := hc.2.2.2.2.2.1
  have hcard3 : ∀ v ∈ V, 3 ≤ (setOfEdge v V (ESTD V)).ncard := fun v hv =>
    SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hv (hsurr v hv)
  have hnb : ∀ v ∈ V, ∃ w, (v, w) ∈ dart1OfFan V (ESTD V) := by
    intro v hv
    have hne : setOfEdge v V (ESTD V) ≠ ∅ := by
      intro he
      have := hcard3 v hv
      rw [he, Set.ncard_empty] at this
      omega
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne
    exact ⟨w, (properties_of_setOfEdge_fan 0 V (ESTD V) v w hfan).mpr hw⟩
  have hnode_eq : ∀ d ∈ H.darts,
      H.node d = (fun y => (d.1, y)) '' setOfEdge d.1 V (ESTD V) :=
    fun d hd => nodeTl_eq_image hfan (dartsTl_mem hd)
  -- 节点集 = v ↦ (v,·) '' setOfEdge v 在 V 上的像（NODE_SET_AS_IMAGE）
  have himg : H.nodeSet =
      (fun v : V3 => (fun y => (v, y)) '' setOfEdge v V (ESTD V)) '' V := by
    ext S
    constructor
    · intro hS
      obtain ⟨d, hd, rfl⟩ := hS.out
      show H.node d ∈ (fun v : V3 => (fun y => (v, y)) '' setOfEdge v V (ESTD V)) '' V
      rw [hnode_eq d hd]
      exact ⟨d.1, (FAN_in_setOfEdge 0 V (ESTD V) d.1 d.2 hfan (dartsTl_mem hd)).1, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨w, hw⟩ := hnb v hv
      exact ⟨(v, w), mem_dartsTl hw, hnode_eq (v, w) (mem_dartsTl hw)⟩
  -- 单射：像集相等 ⟹ 第一分量相等（两像集非空由 hcard3）
  have hinj : Set.InjOn (fun v : V3 => (fun y => (v, y)) '' setOfEdge v V (ESTD V)) V := by
    intro v hv w hw heq
    have hvne : (setOfEdge v V (ESTD V)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr (by
        have := hcard3 v hv
        intro he0
        rw [he0, Set.ncard_empty] at this
        omega)
    obtain ⟨a, ha⟩ := hvne
    have hmemv : (v, a) ∈ ((fun y => (v, y)) '' setOfEdge v V (ESTD V) : Set (V3 × V3)) :=
      ⟨a, ha, rfl⟩
    have hmemw : (v, a) ∈ ((fun y => (w, y)) '' setOfEdge w V (ESTD V) : Set (V3 × V3)) := by
      have heq' : ((fun y => (v, y)) '' setOfEdge v V (ESTD V)) =
          ((fun y => (w, y)) '' setOfEdge w V (ESTD V)) := by
        simpa using heq
      rw [← heq']
      exact hmemv
    obtain ⟨b, -, hbe⟩ :=
      (Set.mem_image (fun y => (w, y)) (setOfEdge w V (ESTD V)) (v, a)).mp hmemw
    exact (Prod.mk.injEq w b v a).mp hbe |>.1.symm
  show H.numberOfNodes = 13 ∨ H.numberOfNodes = 14 ∨ H.numberOfNodes = 15
  show H.nodeSet.ncard = 13 ∨ H.nodeSet.ncard = 14 ∨ H.nodeSet.ncard = 15
  rw [himg, Set.InjOn.ncard_image hinj]
  exact hc.2.2.2.2.1

/-- HOL `JGTDEBU11`（`tame/JGTDEBU.hl:241-253`）：`tame_11a`（node ≥ 3）。
HOL 证明 `SURROUNDED_IMP_IN_DART1_OF_FAN` +
`SURROUNDED_IMP_CARD_NODE_GE_3`；此处 dart 集 = dart1OfFan（Lean 折算形）
故第一步直接由 membership 折算，计数核为
`SURROUNDED_IMP_CARD_NODE_GE_3_TL`。 -/
theorem JGTDEBU11 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    Tame11a (hypermapOfFanTl V (ESTD V) hfan) := by
  show ∀ d ∈ (hypermapOfFanTl V (ESTD V) hfan).darts,
    3 ≤ ((hypermapOfFanTl V (ESTD V) hfan).node d).ncard
  intro d hd
  have hd1 : d ∈ dart1OfFan V (ESTD V) := dartsTl_mem hd
  exact SURROUNDED_IMP_CARD_NODE_GE_3_TL hfan hd1
    (hc.2.2.2.2.2.1 d.1 (FAN_in_setOfEdge 0 V (ESTD V) d.1 d.2 hfan hd1).1)

/-! ### 4b. setSum 计数辅助（SUM_BOUND / SUM_BOUND_LT / SUM_UNION 折算） -/

section SetSumAux

variable {α : Type*}

/-- 常数和的基数倍数（ℕ-基数转 ℝ 的显式归纳，规避 smul/cast 规则细节）。 -/
private theorem sum_const_cast {t : Finset α} (c : ℝ) :
    ∑ _y ∈ t, c = (t.card : ℝ) * c := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add,
      add_mul, ih]
    ring

/-- HOL `SUM_BOUND`：有限集上逐点下界的和下界。 -/
theorem setSum_ge_of_le {s : Set α} {f : α → ℝ} {c : ℝ}
    (hs : s.Finite) (hf : ∀ y ∈ s, c ≤ f y) : s.ncard * c ≤ setSum s f := by
  rw [setSum, dif_pos hs, Set.ncard_eq_toFinset_card s hs]
  calc (hs.toFinset.card : ℝ) * c = ∑ _y ∈ hs.toFinset, c := (sum_const_cast c).symm
    _ ≤ ∑ y ∈ hs.toFinset, f y :=
      Finset.sum_le_sum
        (fun y hy => hf y ((Set.Finite.mem_toFinset hs).mp hy))

/-- HOL `SUM_BOUND` 上界版（逐点 ≤ ⟹ 和 ≤ card * c）。 -/
theorem setSum_le_of_le {s : Set α} {f : α → ℝ} {c : ℝ}
    (hs : s.Finite) (hf : ∀ y ∈ s, f y ≤ c) : setSum s f ≤ s.ncard * c := by
  rw [setSum, dif_pos hs, Set.ncard_eq_toFinset_card s hs]
  calc (∑ y ∈ hs.toFinset, f y) ≤ (∑ _y ∈ hs.toFinset, c) :=
      Finset.sum_le_sum (fun y hy => hf y ((Set.Finite.mem_toFinset hs).mp hy))
    _ = (hs.toFinset.card : ℝ) * c := sum_const_cast c

/-- HOL `SUM_BOUND_LT`（逐点 ≤ + 一点 < ⟹ 和 < card * c）。 -/
theorem setSum_lt_of_le {s : Set α} {f : α → ℝ} {c : ℝ}
    (hs : s.Finite) (hle : ∀ y ∈ s, f y ≤ c) (hex : ∃ y₀ ∈ s, f y₀ < c) :
    setSum s f < s.ncard * c := by
  obtain ⟨y₀, hy₀, hlt⟩ := hex
  rw [setSum, dif_pos hs, Set.ncard_eq_toFinset_card s hs]
  have hy₀' : y₀ ∈ hs.toFinset := (Set.Finite.mem_toFinset hs).mpr hy₀
  have h1 : (∑ y ∈ hs.toFinset, f y) ≤ (∑ _y ∈ hs.toFinset, c) :=
    Finset.sum_le_sum
      (fun y hy => hle y ((Set.Finite.mem_toFinset hs).mp hy))
  have h2 : (∑ y ∈ hs.toFinset, f y) < (∑ _y ∈ hs.toFinset, c) :=
    Finset.sum_lt_sum
      (fun y hy => hle y ((Set.Finite.mem_toFinset hs).mp hy))
      ⟨y₀, hy₀', hlt⟩
  rw [sum_const_cast c] at h2
  exact h2

/-- 单点插入的和分解（`SUM_CLAUSES` 折算）。 -/
theorem setSum_insert {s : Set α} {a : α} (ha : a ∉ s) (hs : s.Finite)
    (f : α → ℝ) : setSum (insert a s) f = f a + setSum s f := by
  rw [setSum, setSum, dif_pos (hs.insert a), dif_pos hs,
    Set.Finite.toFinset_insert (hs.insert a)]
  exact Finset.sum_insert (by simpa using ha)

/-- HOL `SUM_UNION`（不交有限集的和可加）。 -/
theorem setSum_union_disjoint [DecidableEq α] {s t : Set α} {f : α → ℝ}
    (hd : Disjoint s t) (hs : s.Finite) (ht : t.Finite) :
    setSum (s ∪ t) f = setSum s f + setSum t f := by
  rw [setSum, setSum, setSum, dif_pos (hs.union ht), dif_pos hs, dif_pos ht,
    Set.Finite.toFinset_union hs ht]
  have hd' : Disjoint hs.toFinset ht.toFinset := by
    rw [Finset.disjoint_left]
    intro a ha hta
    exact (Set.disjoint_left.mp hd) ((Set.Finite.mem_toFinset hs).mp ha)
      ((Set.Finite.mem_toFinset ht).mp hta)
  exact Finset.sum_union hd'

end SetSumAux

/-! ## 5. CDTETAT / SZIPOAS（tame/CDTETAT.hl，Solovyev 估计，
ssreflect 子目录专用件） -/

/-- HOL `CDTETAT_lemma1`（`tame/CDTETAT.hl:34-173`）：`&p * 0.852 + &t * 1.15 ≤ 2π`
与 `2π < &p * 1.9 + &t * π` 迫使 `(p, t)` 落入 20 对列表。HOL 证明对 `p ≤ 7`
与逐 `p` 的 `t` 上下界做 8 分支算术；此处对 `(p, t)` 同时做区间枚举
（Mathlib `Real.pi_gt_d4`/`Real.pi_lt_d4` = HOL `PI_APPROX_4`），每分支
`decide`（成员）或 `linarith`（排除）。 -/
theorem CDTETAT_lemma1 (p t : ℕ)
    (h1 : (p:ℝ) * 0.852 + (t:ℝ) * 1.15 ≤ 2 * Real.pi)
    (h2 : (2:ℝ) * Real.pi < (p:ℝ) * 1.9 + (t:ℝ) * Real.pi) :
    (p, t) ∈ cdTetatPairs := by
  have hpi1 : (3.1415:ℝ) ≤ Real.pi := Real.pi_gt_d4.le
  have hpi2 : Real.pi ≤ (3.1416:ℝ) := Real.pi_lt_d4.le
  have htp : p ≤ 7 := by
    have h8 : p < 8 := Nat.cast_lt.mp (by linarith : (p:ℝ) < 8)
    omega
  have htle : t ≤ 5 := by
    have h6 : t < 6 := Nat.cast_lt.mp (by linarith : (t:ℝ) < 6)
    omega
  interval_cases p <;> interval_cases t
  all_goals push_cast at h1 h2 ⊢
  all_goals first
    | (simp only [cdTetatPairs]; decide)
    | (exfalso; linarith)

/-- 成对 `(P, T) ∈ cdTetatPairs` 的粗界（成员逐项消解；`List.mem_nil_iff`
收尾后 `omega`）。 -/
theorem cdTetatPairs_bound (P T : ℕ) (h : (P, T) ∈ cdTetatPairs) :
    P ≤ 7 ∧ T ≤ 5 := by
  simp only [cdTetatPairs, List.mem_cons, List.mem_nil_iff, false_or,
    Prod.mk.injEq, or_false] at h
  omega

theorem cdTetatPairs_sum_le (P T : ℕ) (h : (P, T) ∈ cdTetatPairs) : P + T ≤ 7 := by
  simp only [cdTetatPairs, List.mem_cons, List.mem_nil_iff, false_or,
    Prod.mk.injEq, or_false] at h
  omega

/-! ### 5a. CDTETAT 支撑件（hypermap_and_fan.hl:2358/2447 组 +
tame_general.hl azim 边界的 Lean 折算） -/

section CdtetatAux

variable {V : Set V3} {E : Set (Set V3)}

/-- σ-像的满射性（σ 在 soe 上单射 + `card_sigmaFan_image`）。 -/
theorem sigmaFan_surj_soe (hfan : FAN 0 V E) (v : V3) (w : V3)
    (hw : w ∈ setOfEdge v V E) :
    ∃ z ∈ setOfEdge v V E, sigmaFan 0 V E v z = w := by
  have hsoe := remark_finite_fan1 v V E hfan.2.2.1.1
  have hsub : (sigmaFan 0 V E v) '' (setOfEdge v V E) ⊆ setOfEdge v V E := by
    rintro y ⟨z, hz, rfl⟩
    exact sigma_fan_in_setOfEdge hfan hz
  have heq : (sigmaFan 0 V E v) '' (setOfEdge v V E) = setOfEdge v V E := by
    refine Set.Subset.antisymm hsub ?_
    intro y hy
    by_contra hnot
    have hss : (sigmaFan 0 V E v) '' (setOfEdge v V E) ⊂ setOfEdge v V E :=
      lt_of_le_of_ne hsub (fun he => hnot (show y ∈ sigmaFan 0 V E v '' setOfEdge v V E by
        rw [he]; exact hy))
    have hlt := Set.ncard_lt_ncard hss hsoe
    rw [card_sigmaFan_image hfan v] at hlt
    omega
  have hw' : w ∈ (sigmaFan 0 V E v) '' setOfEdge v V E := by rw [heq]; exact hw
  obtain ⟨z, hz, rfl⟩ := hw'
  exact ⟨z, hz, rfl⟩

/-- HOL `INVERSE_SIGMA_FAN` 区域的刻画：`inverse_sigma_fan v w` 是
`σ_v` 的原像（`w ∈ soe` 时原像唯一：soe 外恒等被迫排除，soe 内由
`mono_sigma_fan` 唯一；存在性经 `sigmaFan_surj_soe` + `Function.invFun_eq`）。 -/
theorem inverseSigmaFan_eq (hfan : FAN 0 V E) {v w z : V3}
    (hw : w ∈ setOfEdge v V E) (hinv : inverseSigmaFan 0 V E v w = z) :
    z ∈ setOfEdge v V E ∧ sigmaFan 0 V E v z = w := by
  haveI : Nonempty V3 := ⟨0⟩
  have hu_soe : ∀ z', extensionSigmaFan 0 V E v z' = w → z' ∈ setOfEdge v V E := by
    intro z' hz'
    by_contra hnot
    simp only [extensionSigmaFan, if_pos hnot] at hz'
    exact hnot (hz' ▸ hw)
  obtain ⟨w₀, hw₀, hw₀sig⟩ := sigmaFan_surj_soe hfan v w hw
  have hw₀' : extensionSigmaFan 0 V E v w₀ = w := by
    simp only [extensionSigmaFan, if_neg (not_not.mpr hw₀)]
    exact hw₀sig
  have happly : extensionSigmaFan 0 V E v (Function.invFun (extensionSigmaFan 0 V E v) w)
      = w := Function.invFun_eq ⟨w₀, hw₀'⟩
  rw [inverseSigmaFan] at hinv
  rw [hinv] at happly
  have hzsoe : z ∈ setOfEdge v V E := hu_soe _ happly
  have hsig : sigmaFan 0 V E v z = w := by
    simp only [extensionSigmaFan, if_neg (not_not.mpr hzsoe)] at happly
    exact happly
  exact ⟨hzsoe, hsig⟩

/-- HOL `CARD_FACE_GT_1` + `CARD_SET_OF_EDGE_GT_1_IMP_CARD_FACE_GE_3` 的
合并折算：所有邻边集 ≥ 3 元时 face 轨道 ≥ 3 元。face = {d, f d} 二元反证：
`f²d = d` 迫使 `inverse_sigma_fan d.2 d.1 = d.1`，经 `SIGMA_FAN` 矛盾。 -/
theorem CARD_FACE_GE_3_TL (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E)
    (hcard : ∀ v ∈ V, 3 ≤ (setOfEdge v V E).ncard) :
    3 ≤ ((hypermapOfFanTl V E hfan).face d).ncard := by
  set H := hypermapOfFanTl V E hfan with hHdef
  have hdarts : d ∈ H.darts := mem_dartsTl hd
  have hself : d ∈ H.face d := H.mem_face_self d
  have hfd : H.faceMap d ∈ H.face d := apply_mem_orbitMap H.faceMap d
  have hf_d_eq : H.faceMap d = (d.2, inverseSigmaFan 0 V E d.2 d.1) := by
    rw [faceMapTl_apply hd]; rfl
  have hvw : d.1 ≠ d.2 := edge_ne_of_fan hfan hd
  have hne : H.faceMap d ≠ d := by
    intro he
    rw [hf_d_eq, Prod.mk.injEq] at he
    exact hvw he.1.symm
  have hperm := H.faceMap_permutes
  have hfd1 : H.faceMap d ∈ dart1OfFan V E := by
    rw [← dartsTl_coe]
    exact hperm.apply_mem hdarts
  have hfin : (H.face d).Finite := orbitMap_finite hperm d
  have hpair : ({d, H.faceMap d} : Set (V3 × V3)) ⊆ H.face d := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hself
    · rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hfd
  have h2 : 2 ≤ (H.face d).ncard := by
    have hcard2 : ({d, H.faceMap d} : Set (V3 × V3)).ncard = 2 :=
      Set.ncard_pair (Ne.symm hne)
    calc 2 = ({d, H.faceMap d} : Set (V3 × V3)).ncard := hcard2.symm
      _ ≤ (H.face d).ncard := Set.ncard_le_ncard hpair hfin
  by_contra hcon
  push_neg at hcon
  have h2eq : (H.face d).ncard = 2 := by omega
  have hsub_eq : ({d, H.faceMap d} : Set (V3 × V3)) = H.face d := by
    refine Set.eq_of_subset_of_ncard_le hpair ?_ hfin
    rw [h2eq, Set.ncard_pair (Ne.symm hne)]
  have hf2 : H.faceMap (H.faceMap d) ∈ H.face d := by
    have h := pow_apply_mem_orbitMap H.faceMap 2 d
    rwa [show H.faceMap ^ 2 = H.faceMap * H.faceMap from pow_two _,
      Equiv.Perm.mul_apply] at h
  have hne2 : H.faceMap (H.faceMap d) ≠ H.faceMap d := fun h =>
    hne (Equiv.injective H.faceMap h)
  rw [← hsub_eq] at hf2
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hf2
  rcases hf2 with h22 | h22
  · -- f²d = d ⟹ 首分量 inverseSigmaFan d.2 d.1 = d.1
    have hι : inverseSigmaFan 0 V E d.2 d.1 = d.1 := by
      have h : H.faceMap (H.faceMap d) = ((d.1 : V3), (d.2 : V3)) := by
        rw [h22]
      rw [faceMapTl_apply hfd1, hf_d_eq] at h
      simp only [fFanPair, Prod.mk.injEq] at h
      exact h.1
    have he21 : {d.2, d.1} ∈ E := by rw [Set.pair_comm]; exact hd
    have hfan21 := FAN_in_setOfEdge 0 V E d.2 d.1 hfan he21
    obtain ⟨hmem, hsig⟩ := inverseSigmaFan_eq hfan hfan21.2.2.1 hι
    have h3d2 : 3 ≤ (setOfEdge d.2 V E).ncard := hcard d.2 hfan21.1
    have hne1 : setOfEdge d.2 V E ≠ {d.1} := by
      intro he
      rw [he, Set.ncard_singleton] at h3d2
      omega
    exact (SIGMA_FAN hne1 hfan hmem).2.1 hsig
  · exact hne2 h22

end CdtetatAux

/-! ### 5a. CDTETAT 支撑件（hypermap_and_fan.hl:2358/2447 组 +
tame_general.hl azim 边界的 Lean 折算） -/

/-- dart 的方位角 = 第 i 步角增量（`azim_fan` 在 `ncard(soe) > 1` 分支的
展开；`σ_v (σ^[i] u) = σ^[i+1] u` 由 `iterate_succ_apply'` 收口）。 -/
theorem azimDart_iterate_eq (hfan : FAN 0 V E) {v u : V3} (hvu : {v, u} ∈ E)
    (hcard1 : 1 < (setOfEdge v V E).ncard) (i : ℕ)
    (hin : i < (setOfEdge v V E).ncard) :
    azimDart V E (v, (sigmaFan 0 V E v)^[i] u) = azimIfan 0 V E v u i := by
  have hvw : v ≠ (sigmaFan 0 V E v)^[i] u := by
    have he : {v, (sigmaFan 0 V E v)^[i] u} ∈ E :=
      (properties_of_setOfEdge_fan 0 V E v _ hfan).mpr
        (iterates_mem_setOfEdge hfan v u
          ((properties_of_setOfEdge_fan 0 V E v u hfan).mp hvu) i)
    exact edge_ne_of_fan hfan he
  show (if (v, _).1 = (v, _).2 then 2 * Real.pi
      else azimFan 0 V E (v, _).1 (v, _).2) = azimIfan 0 V E v u i
  rw [if_neg hvw]
  show (if (setOfEdge v V E).ncard > 1 then
      azim 0 v ((sigmaFan 0 V E v)^[i] u) (sigmaFan 0 V E v ((sigmaFan 0 V E v)^[i] u))
    else 2 * Real.pi) = azim 0 v ((sigmaFan 0 V E v)^[i] u)
      ((sigmaFan 0 V E v)^[i + 1] u)
  rw [if_pos hcard1, Function.iterate_succ_apply']

/-- HOL `SUM_AZIM_DART_FULLY_SURROUNDED` 的 node 形（hypermap_and_fan.hl:2447）：
node 轨道上 azim_dart 的和 = 2π。经 `nodeTl_eq_image` + σ-循环的
`Finset.sum_bij` 重排 + `sum_azims_eq_2pi`。 -/
theorem SUM_AZIM_DART_NODE_TL (hfan : FAN 0 V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) (hsurr : surroundedNode V E d.1) :
    setSum ((hypermapOfFanTl V E hfan).node d) (fun y => azimDart V E y)
      = 2 * Real.pi := by
  rcases d with ⟨v, u⟩
  have hdE : {v, u} ∈ E := hd
  have hu_soe : u ∈ setOfEdge v V E := (properties_of_setOfEdge_fan 0 V E v u hfan).mp hdE
  have hvV : v ∈ V := (FAN_in_setOfEdge 0 V E v u hfan hdE).1
  have hcard3 := SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hvV hsurr
  have hne_u : setOfEdge v V E ≠ {u} := by
    intro he
    rw [he, Set.ncard_singleton] at hcard3
    omega
  have hnode : (hypermapOfFanTl V E hfan).node (v, u)
      = (fun y => (v, y)) '' setOfEdge v V E := nodeTl_eq_image hfan hd
  have hfin : ((hypermapOfFanTl V E hfan).node (v, u)).Finite :=
    orbitMap_finite (hypermapOfFanTl V E hfan).nodeMap_permutes (v, u)
  have hsoefin : (setOfEdge v V E).Finite := remark_finite_fan1 v V E hfan.2.2.1.1
  have step1 : (∑ i ∈ Finset.range (setOfEdge v V E).ncard,
        azimDart V E (v, (sigmaFan 0 V E v)^[i] u))
      = setSum ((hypermapOfFanTl V E hfan).node (v, u)) (fun y => azimDart V E y) := by
    rw [setSum, dif_pos hfin]
    refine Finset.sum_bij (fun i _ => (v, (sigmaFan 0 V E v)^[i] u)) ?_ ?_ ?_ ?_
    · intro i hi
      have hmem : (v, (sigmaFan 0 V E v)^[i] u) ∈ (hypermapOfFanTl V E hfan).node (v, u) := by
        have h1 : (hypermapOfFanTl V E hfan).nodeMap^[i] (v, u)
            = (v, (sigmaFan 0 V E v)^[i] u) := nodeMapTl_iterate hd i
        rw [← h1]
        exact pow_apply_mem_orbitMap (hypermapOfFanTl V E hfan).nodeMap i (v, u)
      exact (Set.Finite.mem_toFinset hfin).mpr hmem
    · intro i hi j hj heq
      have hin : i < (setOfEdge v V E).ncard := Finset.mem_range.mp hi
      have hjn : j < (setOfEdge v V E).ncard := Finset.mem_range.mp hj
      simp only [Prod.mk.injEq] at heq
      rcases lt_trichotomy i j with hlt | heqi | hgt
      · exact absurd heq.2.symm (cyclic_power_sigmaFan 0 V E hfan hdE j i hjn hlt)
      · exact heqi
      · exact absurd heq.2 (cyclic_power_sigmaFan 0 V E hfan hdE i j hin hgt)
    · intro y hy
      have hyn : y ∈ (hypermapOfFanTl V E hfan).node (v, u) :=
        (Set.Finite.mem_toFinset hfin).mp hy
      simp only [Hypermap.node, orbitMap, Set.mem_setOf_eq] at hyn
      obtain ⟨n, hn⟩ := hyn
      rw [Equiv.Perm.coe_pow] at hn
      rw [nodeMapTl_iterate hd n] at hn
      have hsoe : (sigmaFan 0 V E v)^[n] u ∈ setOfEdge v V E :=
        iterates_mem_setOfEdge hfan v u hu_soe n
      obtain ⟨j, hj, hj_eq⟩ := iterates_mem_sigmaFan hfan hdE hsoe
      refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
      rw [hj_eq]
      exact hn
    · intro i hi
      rfl
  have step2 : (∑ i ∈ Finset.range (setOfEdge v V E).ncard,
        azimDart V E (v, (sigmaFan 0 V E v)^[i] u))
      = (∑ i ∈ Finset.range (setOfEdge v V E).ncard, azimIfan 0 V E v u i) :=
    Finset.sum_congr rfl (fun i hi =>
      azimDart_iterate_eq hfan hdE (by omega) i (Finset.mem_range.mp hi))
  calc setSum ((hypermapOfFanTl V E hfan).node (v, u)) (fun y => azimDart V E y)
      = ∑ i ∈ Finset.range (setOfEdge v V E).ncard,
          azimDart V E (v, (sigmaFan 0 V E v)^[i] u) := step1.symm
    _ = ∑ i ∈ Finset.range (setOfEdge v V E).ncard, azimIfan 0 V E v u i := step2
    _ = 2 * Real.pi := sum_azims_eq_2pi hfan hdE hne_u

/-- node 轨道上的 dart 属于 dart 集（`NODE_SUBSET_DART_OF_FAN` 折算）。 -/
theorem nodeMem_dart1 (hfan : FAN 0 V E) {d y : V3 × V3} (hd : d ∈ dart1OfFan V E)
    (hy : y ∈ (hypermapOfFanTl V E hfan).node d) : y ∈ dart1OfFan V E := by
  have h := (hypermapOfFanTl V E hfan).node_subset_darts (mem_dartsTl hd) hy
  rwa [dartsTl_coe] at h

/-- HOL `FULLY_SURROUNDED_IMP_CARD_FACE_GE_3`（hypermap_and_fan.hl:2342）的
node 形：surrounded 顶点的 node 轨道上所有 face ≥ 3 元。 -/
theorem nodeFaceCard_ge_3 (hfan : FAN 0 V E) (hcard : ∀ v ∈ V, 3 ≤ (setOfEdge v V E).ncard)
    {d y : V3 × V3} (hd : d ∈ dart1OfFan V E)
    (hy : y ∈ (hypermapOfFanTl V E hfan).node d) : 3 ≤ ((hypermapOfFanTl V E hfan).face y).ncard :=
  CARD_FACE_GE_3_TL hfan (nodeMem_dart1 hfan hd hy) hcard

/-- HOL `FULLY_SURROUNDED_NODE_DECOMPOSITION`（hypermap_and_fan.hl:2358）
的 Lean 折算：node = 三角面 dart 集 ⊔ 非三角（≥ 4）面 dart 集。 -/
theorem FULLY_SURROUNDED_NODE_DECOMPOSITION_TL (hfan : FAN 0 V E)
    (hcard : ∀ v ∈ V, 3 ≤ (setOfEdge v V E).ncard)
    {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    {y | y ∈ (hypermapOfFanTl V E hfan).node d ∧ ((hypermapOfFanTl V E hfan).face y).ncard = 3} ∪
        {y | y ∈ (hypermapOfFanTl V E hfan).node d ∧ 4 ≤ ((hypermapOfFanTl V E hfan).face y).ncard}
      = (hypermapOfFanTl V E hfan).node d := by
  ext y
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨hnode, -⟩ | ⟨hnode, -⟩)
    · exact hnode
    · exact hnode
  · intro hmem
    have h3 := nodeFaceCard_ge_3 hfan hcard hd hmem
    rcases Nat.eq_or_lt_of_le h3 with heq | hlt
    · exact Or.inl ⟨hmem, heq.symm⟩
    · exact Or.inr ⟨hmem, by omega⟩

/-- HOL `FULLY_SURROUNDED_IMP_CARD_NODE_EQ_SUM_NODE_TYPE`（tame_general.hl:500）
的 Lean 折算：`(node d).ncard = p + q + r`。 -/
theorem CARD_NODE_EQ_SUM_NODE_TYPE_TL (hfan : FAN 0 V E)
    (hcard : ∀ v ∈ V, 3 ≤ (setOfEdge v V E).ncard)
    (hsimple : (hypermapOfFanTl V E hfan).Simple)
    {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    ((hypermapOfFanTl V E hfan).node d).ncard
      = (typeOfNode (hypermapOfFanTl V E hfan) d).1
        + ((typeOfNode (hypermapOfFanTl V E hfan) d).2.1
          + (typeOfNode (hypermapOfFanTl V E hfan) d).2.2) := by
  set H := hypermapOfFanTl V E hfan with hHdef
  have htype := NODE_TYPE_lemma H d hsimple (mem_dartsTl hd)
  have hBD : {y | y ∈ H.node d ∧ (H.face y).ncard = 4}
      ∪ {y | y ∈ H.node d ∧ 5 ≤ (H.face y).ncard}
      = {y | y ∈ H.node d ∧ 4 ≤ (H.face y).ncard} := by
    ext y
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hnode, h4⟩ | ⟨hnode, h5⟩)
      · exact ⟨hnode, by omega⟩
      · exact ⟨hnode, by omega⟩
    · intro hmem
      rcases Nat.eq_or_lt_of_le hmem.2 with heq | hlt
      · exact Or.inl ⟨hmem.1, heq.symm⟩
      · exact Or.inr ⟨hmem.1, by omega⟩
  have hdisjBD : Disjoint {y | y ∈ H.node d ∧ (H.face y).ncard = 4}
      {y | y ∈ H.node d ∧ 5 ≤ (H.face y).ncard} := by
    rw [Set.disjoint_left]
    intro a ha hb
    rw [Set.mem_setOf_eq] at ha hb
    omega
  have hdisjAD : Disjoint {y | y ∈ H.node d ∧ (H.face y).ncard = 3}
      {y | y ∈ H.node d ∧ 4 ≤ (H.face y).ncard} := by
    rw [Set.disjoint_left]
    intro a ha hb
    rw [Set.mem_setOf_eq] at ha hb
    omega
  have hAD := FULLY_SURROUNDED_NODE_DECOMPOSITION_TL hfan hcard hd
  have hfinN : (H.node d).Finite := orbitMap_finite H.nodeMap_permutes d
  have hcardA : ({y | y ∈ H.node d ∧ (H.face y).ncard = 3}).Finite :=
    hfinN.subset fun y hy => (Set.mem_setOf_eq.mp hy).1
  have hcardD : ({y | y ∈ H.node d ∧ 4 ≤ (H.face y).ncard}).Finite :=
    hfinN.subset fun y hy => (Set.mem_setOf_eq.mp hy).1
  have hcardB : ({y | y ∈ H.node d ∧ (H.face y).ncard = 4}).Finite :=
    hfinN.subset fun y hy => (Set.mem_setOf_eq.mp hy).1
  have hcardC : ({y | y ∈ H.node d ∧ 5 ≤ (H.face y).ncard}).Finite :=
    hfinN.subset fun y hy => (Set.mem_setOf_eq.mp hy).1
  have hsumBD : ({y | y ∈ H.node d ∧ 4 ≤ (H.face y).ncard}).ncard
      = ({y | y ∈ H.node d ∧ (H.face y).ncard = 4}).ncard
        + ({y | y ∈ H.node d ∧ 5 ≤ (H.face y).ncard}).ncard := by
    rw [← Set.ncard_union_eq hdisjBD hcardB hcardC, hBD]
  rw [htype]
  have h1 : (H.node d).ncard
      = ({y | y ∈ H.node d ∧ (H.face y).ncard = 3}).ncard
        + (({y | y ∈ H.node d ∧ (H.face y).ncard = 4}).ncard
          + ({y | y ∈ H.node d ∧ 5 ≤ (H.face y).ncard}).ncard) := by
    rw [← hsumBD, ← Set.ncard_union_eq hdisjAD hcardA hcardD, hAD]
  omega


/-- HOL `TRIANGULAR_FACE_AZIM_DART_BOUNDS`（tame_general.hl:739-746，
机器 ineq `5735387903`/`5490182221`）的结论形；本群从
`kcblrqc_ineq_def` 抽取（见 `KcblrqcIneqDef` 切片 1）。 -/
theorem TRIANGULAR_FACE_AZIM_DART_BOUNDS_TL (hineq : KcblrqcIneqDef)
    (V : Set V3) (hfan : FAN 0 V (ESTD V)) {y : V3 × V3} (hc : Contravening V)
    (hy : y ∈ dartOfFan V (ESTD V))
    (hcard : ((hypermapOfFanTl V (ESTD V) hfan).face y).ncard = 3) :
    (0.852:ℝ) < azimDart V (ESTD V) y ∧ azimDart V (ESTD V) y < 1.893 :=
  (hineq.1 V hfan y hc hy).1 hcard

/-- HOL `non_triangular_face_azim_dart_bound`（ssreflect/tame_lemmas-compiled.hl:896，
机器 `DIH_Y_INEQ`）的结论形；`KcblrqcIneqDef` 切片 1。 -/
theorem nonTriangularFaceAzimDartBound (hineq : KcblrqcIneqDef)
    (V : Set V3) (hfan : FAN 0 V (ESTD V)) {y : V3 × V3} (hc : Contravening V)
    (hy : y ∈ dartOfFan V (ESTD V))
    (hcard : 3 < ((hypermapOfFanTl V (ESTD V) hfan).face y).ncard) :
    (1.15:ℝ) < azimDart V (ESTD V) y :=
  (hineq.1 V hfan y hc hy).2 hcard

/-- HOL `CDTETAT`（`tame/CDTETAT.hl:155-160`，带前提形）。
DISCHARGES：HOL 证明约 60 步（`NODE_TYPE_lemma` +
`SUM_AZIM_DART_FULLY_SURROUNDED` + `FULLY_SURROUNDED_NODE_DECOMPOSITION` +
`CDTETAT_lemma1` :44-148 的 21 情形实数算术 + `kcblrqc_ineq_def` 的
`TRIANGULAR_FACE_AZIM_DART_BOUNDS`/`non_triangular_face_azim_dart_bound`）；
Lean 折算逐件对应：`NODE_TYPE_lemma`（本文）、`SUM_AZIM_DART_NODE_TL`、
`FULLY_SURROUNDED_NODE_DECOMPOSITION_TL`、`CDTETAT_lemma1`（区间枚举 +
`Real.pi_gt_d4`/`Real.pi_lt_d4` = HOL `PI_APPROX_4`）、azim 边界经
`KcblrqcIneqDef` 切片 1。 -/
theorem CDTETAT (hineq : KcblrqcIneqDef) (V : Set V3) (hc : Contravening V)
    (hfan : FAN 0 V (ESTD V)) (x : V3 × V3) (hx : x ∈ dartOfFan V (ESTD V)) :
    let H := hypermapOfFanTl V (ESTD V) hfan
    let p := (typeOfNode H x).1
    let q := (typeOfNode H x).2.1
    let r := (typeOfNode H x).2.2
    (p, q + r) ∈ cdTetatPairs := by
  intro H p q r
  show (p, q + r) ∈ cdTetatPairs
  -- fully_surrounded 给 x 的 azim < π，排除退化 dart（HOL `f_surr`）
  have hsurr : surroundedNode V (ESTD V) x.1 :=
    hc.2.2.2.2.2.1 x.1 (dartOfFan_fst_mem hfan hx)
  have hlt : azimDart V (ESTD V) x < Real.pi := hsurr x hx rfl
  have hxne : x.1 ≠ x.2 := by
    intro he
    have hx' : x = (x.1, x.1) := Prod.ext rfl he.symm
    rw [hx'] at hlt
    have h2pi : azimDart V (ESTD V) (x.1, x.1) = 2 * Real.pi := by simp [azimDart]
    rw [h2pi] at hlt
    linarith [Real.pi_pos]
  have hx1 : x ∈ dart1OfFan V (ESTD V) := by
    rcases (Set.mem_union _ _ _).mp hx with h | h
    · exact absurd h.out.1 hxne
    · exact h
  have hdarts : x ∈ H.darts := mem_dartsTl hx1
  -- 全顶点邻边 ≥ 3（HOL `f_surr` 的 SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3）
  have hcard : ∀ v ∈ V, 3 ≤ (setOfEdge v V (ESTD V)).ncard := fun v hv =>
    SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hv (hc.2.2.2.2.2.1 v hv)
  have hsimple := JGTDEBU4 V hc hfan
  have htype := NODE_TYPE_lemma H x hsimple hdarts
  set A := {y | y ∈ H.node x ∧ (H.face y).ncard = 3} with hAdef
  set B := {y | y ∈ H.node x ∧ (H.face y).ncard = 4} with hBdef
  set C := {y | y ∈ H.node x ∧ 5 ≤ (H.face y).ncard} with hCdef
  set D := {y | y ∈ H.node x ∧ 4 ≤ (H.face y).ncard} with hDdef
  have hfinN : (H.node x).Finite := orbitMap_finite H.nodeMap_permutes x
  have hfinA : A.Finite := hfinN.subset fun y hy => (Set.mem_setOf_eq.mp hy).1
  have hfinD : D.Finite := hfinN.subset fun y hy => (Set.mem_setOf_eq.mp hy).1
  have hfinB : B.Finite := hfinN.subset fun y hy => (Set.mem_setOf_eq.mp hy).1
  have hfinC : C.Finite := hfinN.subset fun y hy => (Set.mem_setOf_eq.mp hy).1
  -- 分解与计数
  have hAD := FULLY_SURROUNDED_NODE_DECOMPOSITION_TL hfan hcard hx1
  have hdisjAD : Disjoint A D := by
    rw [Set.disjoint_left]
    intro y ha hb
    rw [hAdef] at ha
    rw [hDdef] at hb
    rw [Set.mem_setOf_eq] at ha hb
    omega
  have hdisjBC : Disjoint B C := by
    rw [Set.disjoint_left]
    intro y ha hb
    rw [hBdef] at ha
    rw [hCdef] at hb
    rw [Set.mem_setOf_eq] at ha hb
    omega
  have hDT : D.ncard = B.ncard + C.ncard := by
    have hBD : B ∪ C = D := by
      ext y
      constructor
      · rintro (⟨hnode, h4⟩ | ⟨hnode, h5⟩)
        · rw [hDdef]; exact ⟨hnode, by omega⟩
        · rw [hDdef]; exact ⟨hnode, by omega⟩
      · intro hmem
        rw [hDdef] at hmem
        rcases Nat.eq_or_lt_of_le hmem.2 with heq | hlt
        · exact Or.inl ⟨hmem.1, heq.symm⟩
        · exact Or.inr ⟨hmem.1, by omega⟩
    rw [← Set.ncard_union_eq hdisjBC hfinB hfinC, hBD]
  -- azim 边界（KcblrqcIneqDef 切片 1）
  have hboundA : ∀ y ∈ A, (0.852:ℝ) ≤ azimDart V (ESTD V) y ∧
      azimDart V (ESTD V) y < 1.9 := by
    intro y hy
    rw [hAdef] at hy
    obtain ⟨hnode, h3⟩ := Set.mem_setOf_eq.mp hy
    have hyd : y ∈ dartOfFan V (ESTD V) := Set.mem_union_right _ (nodeMem_dart1 hfan hx1 hnode)
    have hb := (hineq.1 V hfan y hc hyd).1 h3
    exact ⟨hb.1.le, by linarith⟩
  have hboundD : ∀ y ∈ D, (1.15:ℝ) ≤ azimDart V (ESTD V) y ∧
      azimDart V (ESTD V) y < Real.pi := by
    intro y hy
    rw [hDdef] at hy
    obtain ⟨hnode, h4⟩ := Set.mem_setOf_eq.mp hy
    have hyd : y ∈ dartOfFan V (ESTD V) := Set.mem_union_right _ (nodeMem_dart1 hfan hx1 hnode)
    have hb := (hineq.1 V hfan y hc hyd).2
      (show 3 < (H.face y).ncard by omega)
    have hpi : azimDart V (ESTD V) y < Real.pi :=
      hc.2.2.2.2.2.1 y.1 (dartOfFan_fst_mem hfan hyd) y hyd rfl
    exact ⟨hb.le, hpi⟩
  -- 角和分解
  have hsplit : setSum A (fun y => azimDart V (ESTD V) y)
      + setSum D (fun y => azimDart V (ESTD V) y) = 2 * Real.pi := by
    rw [← setSum_union_disjoint hdisjAD hfinA hfinD, hAD]
    exact SUM_AZIM_DART_NODE_TL hfan hx1 hsurr
  have hlowA : A.ncard * (0.852:ℝ) ≤ setSum A (fun y => azimDart V (ESTD V) y) :=
    setSum_ge_of_le hfinA fun y hy => (hboundA y hy).1
  have hlowD : D.ncard * (1.15:ℝ) ≤ setSum D (fun y => azimDart V (ESTD V) y) :=
    setSum_ge_of_le hfinD fun y hy => (hboundD y hy).1
  have h1 : A.ncard * (0.852:ℝ) + D.ncard * (1.15:ℝ) ≤ 2 * Real.pi := by linarith
  have hupA : ∀ y ∈ A, azimDart V (ESTD V) y ≤ (1.9:ℝ) := fun y hy =>
    (hboundA y hy).2.le
  have hupD : ∀ y ∈ D, azimDart V (ESTD V) y ≤ Real.pi := fun y hy =>
    (hboundD y hy).2.le
  have hxA : x ∈ A ∨ x ∈ D := by
    have hmem : x ∈ H.node x := H.mem_node_self x
    rw [← hAD] at hmem
    exact hmem
  have h2 : (2:ℝ) * Real.pi < A.ncard * (1.9:ℝ) + D.ncard * Real.pi := by
    rcases hxA with hxA | hxA
    · have sA : setSum A (fun y => azimDart V (ESTD V) y) < A.ncard * (1.9:ℝ) :=
        setSum_lt_of_le hfinA hupA ⟨x, hxA, (hboundA x hxA).2⟩
      have sD : setSum D (fun y => azimDart V (ESTD V) y)
          ≤ D.ncard * Real.pi := setSum_le_of_le hfinD hupD
      linarith
    · have sA : setSum A (fun y => azimDart V (ESTD V) y) ≤ A.ncard * (1.9:ℝ) :=
        setSum_le_of_le hfinA hupA
      have sD : setSum D (fun y => azimDart V (ESTD V) y) < D.ncard * Real.pi :=
        setSum_lt_of_le hfinD hupD ⟨x, hxA, hlt⟩
      linarith
  rw [hDT] at h1 h2
  show ((typeOfNode H x).1, (typeOfNode H x).2.1 + (typeOfNode H x).2.2) ∈ cdTetatPairs
  rw [htype]
  simpa using CDTETAT_lemma1 A.ncard (B.ncard + C.ncard) h1 h2

/-- HOL `SZIPOAS`（`tame/CDTETAT.hl:306-308`）：`kcblrqc_ineq_def ⟹
contravening ⟹ tame_11b`。HOL 证明经 `FULLY_SURROUNDED_IMP_CARD_NODE_EQ_SUM_NODE_TYPE`
+ `CDTETAT` 分类 + 20 情形算术；Lean 折算为 `CARD_NODE_EQ_SUM_NODE_TYPE_TL`
+ `CDTETAT` + `cdTetatPairs_sum_le` + `omega`。 -/
theorem SZIPOAS (hineq : KcblrqcIneqDef) (V : Set V3) (hc : Contravening V)
    (hfan : FAN 0 V (ESTD V)) :
    Tame11b (hypermapOfFanTl V (ESTD V) hfan) := by
  show ∀ d ∈ (hypermapOfFanTl V (ESTD V) hfan).darts,
    ((hypermapOfFanTl V (ESTD V) hfan).node d).ncard ≤ 7
  intro d hd
  have hx1 : d ∈ dart1OfFan V (ESTD V) := dartsTl_mem hd
  have hcard : ∀ v ∈ V, 3 ≤ (setOfEdge v V (ESTD V)).ncard := fun v hv =>
    SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hv (hc.2.2.2.2.2.1 v hv)
  have hsum := CARD_NODE_EQ_SUM_NODE_TYPE_TL hfan hcard (JGTDEBU4 V hc hfan) hx1
  have hmem := CDTETAT hineq V hc hfan d (Set.mem_union_right _ hx1)
  have hle7 := cdTetatPairs_sum_le _ _ hmem
  rw [hsum]
  omega

/-! ## 6. KCBLRQC / BDJYFFB（tame/ssreflect/KCBLRQC-compiled.hl）。
两个 section（Contravening :927-935 的 contrV，BDJYFFB :922-924 的
h_main := lp_main_estimate、ineqs := kcblrqc_ineq_def）finalized 形。 -/

/-- `(p, q + r) ∈ cdTetatPairs`、`p + (q + r) = 6`、`1 ≤ r` 时的 node-type
分类：type = (5,0,1) 或落入 6 个被机器不等式排除的 r > 0 类型
（BDJYFFB1 第一合取的 20 情形算术；HOL 侧对应 get_b_tame_ineq 的
(6,0,1)/(3,0,3)/(3,1,2)/(3,2,1)/(4,0,2)/(4,1,1) 数值矛盾行）。 -/
theorem cdTetatPairs_node6_cases (p q r : ℕ) (hmem : (p, q + r) ∈ cdTetatPairs)
    (h6 : p + (q + r) = 6) (hr1 : 1 ≤ r) :
    (p, q, r) = (5, 0, 1) ∨
      (p, q, r) ∈ [(6, 0, 1), (3, 0, 3), (3, 1, 2), (3, 2, 1), (4, 0, 2), (4, 1, 1)] := by
  simp only [cdTetatPairs, List.mem_cons, List.mem_nil_iff, false_or, Prod.mk.injEq,
    or_false] at hmem
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals try { exfalso; omega }
  all_goals
    rw [h1]
    have hq : (q = 2 ∧ r = 1) ∨ (q = 1 ∧ r = 2) ∨ (q = 0 ∧ r = 3) ∨
        (q = 1 ∧ r = 1) ∨ (q = 0 ∧ r = 2) ∨ (q = 0 ∧ r = 1) := by omega
    rcases hq with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ |
        ⟨h1', h2'⟩
    all_goals
      rw [h1', h2']
      first
        | exact Or.inl rfl
        | exact Or.inr (by decide)
        | (exfalso; omega)

/-- `(p, q + r) ∈ cdTetatPairs`、`1 ≤ r` 的 20 情形算术：node 和 ≤ 6，
或退化为唯一越界型 (6,0,1)（BDJYFFB1 第二合取；对应 HOL 脚本
`do 20?case; try arith` 主干 + get_b_tame_ineq (6,0,1) 的数值矛盾行）。 -/
theorem cdTetatPairs_node_le6 (p q r : ℕ) (hmem : (p, q + r) ∈ cdTetatPairs)
    (hr1 : 1 ≤ r) : p + (q + r) ≤ 6 ∨
      (p, q, r) ∈ [(6, 0, 1), (3, 0, 3), (3, 1, 2), (3, 2, 1), (4, 0, 2), (4, 1, 1)] := by
  simp only [cdTetatPairs, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq,
    or_false] at hmem
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals
    first
      | omega
      | (have hq : q = 0 := by omega
         subst hq
         have hr : r = 1 := by omega
         subst hr
         have hp : p = 6 := by omega
         subst hp
         exact Or.inr (by decide))

/-- HOL `KCBLRQC`（`tame/ssreflect/KCBLRQC-compiled.hl:868-873`，
node-type 不等式：`r > 0 ∨ sum (set_of_face_meeting_node H d) tauVEF ≥ b_tame p q`）。
HOL 证明：`NODE_TYPE_lemma` + `CDTETAT` 分类 + r = 0 的 20 情形
get_b_tame_ineq 表算术（:874-908，每情形 4-6 步）；Lean 折算为
`CDTETAT` + `KcblrqcIneqDef` 切片 2（r = 0 表）逐合取消解。 -/
theorem KCBLRQC (V : Set V3) (hc : Contravening V)
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef)
    (hfan : FAN 0 V (ESTD V)) (d : V3 × V3) (hd : d ∈ dartOfFan V (ESTD V)) :
    let H := hypermapOfFanTl V (ESTD V) hfan
    let p := (typeOfNode H d).1
    let q := (typeOfNode H d).2.1
    let r := (typeOfNode H d).2.2
    0 < r ∨ setSum (setOfFaceMeetingNode H d)
        (fun f => tauVEF_p2 V (ESTD V) f) ≥ bTame p q := by
  intro H p q r
  show (0:ℕ) < r ∨ setSum (setOfFaceMeetingNode H d)
      (fun f => tauVEF_p2 V (ESTD V) f) ≥ bTame p q
  have htypeEq : typeOfNode H d = (p, q, r) := rfl
  rcases Nat.eq_zero_or_pos r with r0 | rpos
  · have hmem : ((typeOfNode H d).1, (typeOfNode H d).2.1 + (typeOfNode H d).2.2) ∈
        cdTetatPairs := CDTETAT hineq V hc hfan d hd
    rw [show (typeOfNode H d).2.2 = 0 from r0, Nat.add_zero] at hmem
    have hteq0 : typeOfNode H d =
        ((typeOfNode H d).1, (typeOfNode H d).2.1, (0:ℕ)) := by
      rw [htypeEq, r0]
    exact Or.inr (hineq.2.1 hmain V hfan hc d hd _ _ hmem hteq0)
  · exact Or.inl rpos

/-- HOL `BDJYFFB1`（`tame/ssreflect/KCBLRQC-compiled.hl:917-919`）：`tame_12o`。
HOL 证明约 35 步（`fully_surrounded_dart_of_fan_eq` + `CARD_FACE_GT_1` +
`NODE_TYPE_lemma` + `FULLY_SURROUNDED_IMP_CARD_NODE_EQ_SUM_NODE_TYPE` +
`CDTETAT` + get_b_tame_ineq 的 (6,0,1)/(3,0,3)/(3,1,2)/(3,2,1)/(4,0,2)/(4,1,1)
数值矛盾行）；Lean 折算为 `cdTetatPairs_node6_cases`（第一合取）+
`cdTetatPairs_node_le6`（第二合取）+ 切片 3 的 6 类型排除。 -/
theorem BDJYFFB1 (V : Set V3) (hc : Contravening V)
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef)
    (hfan : FAN 0 V (ESTD V)) :
    Tame12o (hypermapOfFanTl V (ESTD V) hfan) := by
  have hcard : ∀ v ∈ V, 3 ≤ (setOfEdge v V (ESTD V)).ncard := fun v hv =>
    SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hv (hc.2.2.2.2.2.1 v hv)
  have hsimple := JGTDEBU4 V hc hfan
  have hsum : ∀ d ∈ (hypermapOfFanTl V (ESTD V) hfan).darts,
      ((hypermapOfFanTl V (ESTD V) hfan).node d).ncard
        = (typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d).1
          + ((typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d).2.1
            + (typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d).2.2) :=
    fun d hd => CARD_NODE_EQ_SUM_NODE_TYPE_TL hfan hcard hsimple (dartsTl_mem hd)
  -- r ≥ 1：d 自己的 exceptional face 记入 C（d ∈ node d）
  have hCmem : ∀ d ∈ (hypermapOfFanTl V (ESTD V) hfan).darts,
      5 ≤ ((hypermapOfFanTl V (ESTD V) hfan).face d).ncard →
        1 ≤ (typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d).2.2 := by
    intro d hd h5
    have htype := NODE_TYPE_lemma (hypermapOfFanTl V (ESTD V) hfan) d hsimple hd
    have hmemC : d ∈ {y | y ∈ (hypermapOfFanTl V (ESTD V) hfan).node d ∧
        5 ≤ ((hypermapOfFanTl V (ESTD V) hfan).face y).ncard} :=
      ⟨Hypermap.mem_node_self _ _, h5⟩
    have hfinN : ({y | y ∈ (hypermapOfFanTl V (ESTD V) hfan).node d ∧
        5 ≤ ((hypermapOfFanTl V (ESTD V) hfan).face y).ncard}).Finite :=
      (orbitMap_finite (hypermapOfFanTl V (ESTD V) hfan).nodeMap_permutes d).subset
        fun y hy => (Set.mem_setOf_eq.mp hy).1
    have hpos : 0 < ({y | y ∈ (hypermapOfFanTl V (ESTD V) hfan).node d ∧
        5 ≤ ((hypermapOfFanTl V (ESTD V) hfan).face y).ncard}).ncard := by
      rw [Set.ncard_pos hfinN]
      exact ⟨d, hmemC⟩
    rw [htype]
    linarith
  show ∀ d ∈ (hypermapOfFanTl V (ESTD V) hfan).darts,
    (((5:ℕ) ≤ ((hypermapOfFanTl V (ESTD V) hfan).face d).ncard ∧
        ((hypermapOfFanTl V (ESTD V) hfan).node d).ncard = 6) →
      typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d = (5, 0, 1)) ∧
    (5 ≤ ((hypermapOfFanTl V (ESTD V) hfan).face d).ncard →
      ((hypermapOfFanTl V (ESTD V) hfan).node d).ncard ≤ 6)
  intro d hd
  have hsumD := hsum d hd
  have hmem := CDTETAT hineq V hc hfan d (Set.mem_union_right _ (dartsTl_mem hd))
  have htypeEq : typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d
      = ((typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d).1,
         (typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d).2.1,
         (typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d).2.2) := rfl
  have hdart : d ∈ dartOfFan V (ESTD V) := Set.mem_union_right _ (dartsTl_mem hd)
  refine ⟨fun h5 => ?_, fun h5 => ?_⟩
  · obtain ⟨h5, hnode6⟩ := h5
    have hr1 := hCmem d hd h5
    have h6 : (typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d).1
        + ((typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d).2.1
          + (typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d).2.2) = 6 := by
      rw [hsumD] at hnode6
      omega
    rcases cdTetatPairs_node6_cases _ _ _ hmem h6 hr1 with heq | hin
    · rwa [htypeEq]
    · have hin' : typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d ∈
          [(6, 0, 1), (3, 0, 3), (3, 1, 2), (3, 2, 1), (4, 0, 2), (4, 1, 1)] :=
        htypeEq ▸ hin
      exact (hineq.2.2.1 hmain V hfan hc d hdart hin').elim
  · have hr1 := hCmem d hd h5
    rcases cdTetatPairs_node_le6 _ _ _ hmem hr1 with hle | hin
    · rw [hsumD]
      exact hle
    · have hin' : typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d ∈
          [(6, 0, 1), (3, 0, 3), (3, 1, 2), (3, 2, 1), (4, 0, 2), (4, 1, 1)] :=
        htypeEq ▸ hin
      exact (hineq.2.2.1 hmain V hfan hc d hdart hin').elim

/-- HOL `BDJYFFB2`（`tame/ssreflect/KCBLRQC-compiled.hl:962-967`）：
type (5,0,1) 的节点上三角形 tauVEF 和 `> #0.63`（`a_tame`）。
HOL 证明 4 步（get_b_tame_ineq (5,0,1) + 算术）；Lean 折算为
`KcblrqcIneqDef` 切片 4（`0.6366 ≤` 三角和）+ `linarith`。 -/
theorem BDJYFFB2 (V : Set V3) (hc : Contravening V)
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef)
    (hfan : FAN 0 V (ESTD V)) (d : V3 × V3)
    (hd : d ∈ dartOfFan V (ESTD V))
    (htype : typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d = (5, 0, 1)) :
    aTame < setSum {f | f ∈ setOfFaceMeetingNode (hypermapOfFanTl V (ESTD V) hfan) d ∧
        f.ncard = 3}
      (fun f => tauVEF_p2 V (ESTD V) f) := by
  have h6366 := hineq.2.2.2 hmain V hfan hc d hd htype
  have haTame : aTame = 0.63 := rfl
  linarith

/-! ## 7. CRTTXAT（tame/CRTTXAT.hl，tame_9a 出口，Solovyev 2010） -/

/-! ### arc kit 五件套自证（tame/arc_properties.hl，B2 叶；2026-10-12 第二波）

HOL `arc_properties.hl` 的五件套 Lean 自证（绕开 B2 叶 1091 行移植）：
① `arcV_eq_arcLen`（cosine-law 纯算术，无范围前提）② `arc_lemma1`（arccos antitone）
③ `arc_lemma3`（凹性 ConcaveOn 插值 + `arc_lmfun_*` 权重）④ `arc_lemma4`
（∂ₓ 单调 + estimate0 链）⑤ `estimate0`/`arc_lemma5_num`（认证 Taylor 数值，无浮点）。
`arcLen a b c = arccos((a²+b²−c²)/(2ab))` 为局部副本（复用 `arcV`/LuneVolume）。 -/


/-! ===== Taylor cos bounds (certified, no floating point) ===== -/

/-- One-step monotone descent: f(0)=0, f' ≥ 0 on [0,X] ⟹ f ≥ 0 on [0,X]. -/
private theorem nonneg_of_deriv_chain (f f₁ : ℝ → ℝ) {X : ℝ} (hX : 0 ≤ X)
    (hstep : ∀ t : ℝ, HasDerivAt f (f₁ t) t)
    (hpos : ∀ t ∈ Set.Icc 0 X, 0 ≤ f₁ t)
    (hzero : f 0 = 0) :
    ∀ t ∈ Set.Icc 0 X, 0 ≤ f t := by
  have hdiff : Differentiable ℝ f := fun t => (hstep t).differentiableAt
  have hmono : MonotoneOn f (Set.Icc 0 X) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 X) hdiff.continuous.continuousOn
      hdiff.differentiableOn (fun t ht => by
        rw [(hstep t).deriv]
        have ht' : t ∈ Set.Ioo 0 X := by rw [← interior_Icc]; exact ht
        exact hpos t (Set.Ioo_subset_Icc_self ht'))
  intro t ht
  have h00 : (0:ℝ) ∈ Set.Icc 0 X := ⟨le_refl 0, hX⟩
  have hv := hmono h00 ht (le_trans (le_refl 0) ht.1)
  rwa [hzero] at hv

/-! ### derivative atoms for the Taylor chains -/

private theorem hpow2d2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * t / 2) t t := by
  intro t
  have h := ((hasDerivAt_id t).mul (hasDerivAt_id t)).div_const 2
  simp only [Pi.mul_apply, id_eq, one_mul, mul_one] at h
  rw [show (t + t : ℝ) / 2 = t by ring] at h
  exact h

private theorem hpow3d6 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * t * t / 6) (t * t / 2) t := by
  intro t
  have h := ((hasDerivAt_id t).mul (hpow2d2 t)).div_const 3
  simp only [Pi.mul_apply, id_eq, one_mul] at h
  rw [show (t * t / 2 + t * t : ℝ) / 3 = t * t / 2 by ring] at h
  exact HasDerivAt.congr_of_eventuallyEq h
    (Filter.eventuallyEq_of_mem Filter.univ_mem (fun y _ => by ring))

private theorem hpow4d24 : ∀ t : ℝ,
    HasDerivAt (fun t : ℝ => t * t * t * t / 24) (t * t * t / 6) t := by
  intro t
  have h := ((hasDerivAt_id t).mul (hpow3d6 t)).div_const 4
  simp only [Pi.mul_apply, id_eq, one_mul] at h
  rw [show (t * t * t / 6 + t * (t * t / 2) : ℝ) / 4 = t * t * t / 6 by ring] at h
  exact HasDerivAt.congr_of_eventuallyEq h
    (Filter.eventuallyEq_of_mem Filter.univ_mem (fun y _ => by ring))

private theorem hpow5d120 : ∀ t : ℝ,
    HasDerivAt (fun t : ℝ => t * t * t * t * t / 120) (t * t * t * t / 24) t := by
  intro t
  have h := ((hasDerivAt_id t).mul (hpow4d24 t)).div_const 5
  simp only [Pi.mul_apply, id_eq, one_mul] at h
  rw [show (t * t * t * t / 24 + t * (t * t * t / 6) : ℝ) / 5 = t * t * t * t / 24 by ring] at h
  exact HasDerivAt.congr_of_eventuallyEq h
    (Filter.eventuallyEq_of_mem Filter.univ_mem (fun y _ => by ring))

private theorem hpow6d720 : ∀ t : ℝ,
    HasDerivAt (fun t : ℝ => t * t * t * t * t * t / 720) (t * t * t * t * t / 120) t := by
  intro t
  have h := ((hasDerivAt_id t).mul (hpow5d120 t)).div_const 6
  simp only [Pi.mul_apply, id_eq, one_mul] at h
  rw [show (t * t * t * t * t / 120 + t * (t * t * t * t / 24) : ℝ) / 6
      = t * t * t * t * t / 120 by ring] at h
  exact HasDerivAt.congr_of_eventuallyEq h
    (Filter.eventuallyEq_of_mem Filter.univ_mem (fun y _ => by ring))

private theorem hpow7d5040 : ∀ t : ℝ,
    HasDerivAt (fun t : ℝ => t * t * t * t * t * t * t / 5040)
      (t * t * t * t * t * t / 720) t := by
  intro t
  have h := ((hasDerivAt_id t).mul (hpow6d720 t)).div_const 7
  simp only [Pi.mul_apply, id_eq, one_mul] at h
  rw [show (t * t * t * t * t * t / 720 + t * (t * t * t * t * t / 120) : ℝ) / 7
      = t * t * t * t * t * t / 720 by ring] at h
  exact HasDerivAt.congr_of_eventuallyEq h
    (Filter.eventuallyEq_of_mem Filter.univ_mem (fun y _ => by ring))

private theorem hpow8d40320 : ∀ t : ℝ,
    HasDerivAt (fun t : ℝ => t * t * t * t * t * t * t * t / 40320)
      (t * t * t * t * t * t * t / 5040) t := by
  intro t
  have h := ((hasDerivAt_id t).mul (hpow7d5040 t)).div_const 8
  simp only [Pi.mul_apply, id_eq, one_mul] at h
  rw [show (t * t * t * t * t * t * t / 5040 + t * (t * t * t * t * t * t / 720) : ℝ) / 8
      = t * t * t * t * t * t * t / 5040 by ring] at h
  exact HasDerivAt.congr_of_eventuallyEq h
    (Filter.eventuallyEq_of_mem Filter.univ_mem (fun y _ => by ring))

/-- 4th-order cos upper bound on [0,1]: `cos t ≤ 1 − t²/2 + t⁴/24`
(半角 double angle + `Real.sin_ge_sub_cube`). -/
private theorem cos_le_1_sub_sq_div_two_add (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.cos t ≤ 1 - t * t / 2 + t * t * t * t / 24 := by
  have h2 : (t / 2) ^ 2 ≤ 1 := by nlinarith
  have hs := Real.sin_ge_sub_cube (show (0:ℝ) ≤ t / 2 by linarith)
  have hsq : (t / 2 - (t / 2) ^ 3 / 6) ^ 2 ≤ Real.sin (t / 2) ^ 2 := by
    have hspos : (0:ℝ) ≤ t / 2 - (t / 2) ^ 3 / 6 := by
      have h6 : (0:ℝ) ≤ 6 - (t / 2) ^ 2 := by linarith
      have hexp : t / 2 - (t / 2) ^ 3 / 6 = (t / 2) * (6 - (t / 2) ^ 2) / 6 := by ring
      rw [hexp]
      exact div_nonneg (mul_nonneg (by linarith) h6) (by norm_num)
    exact pow_le_pow_left₀ hspos hs 2
  have hcos : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have h2t : Real.cos (2 * (t / 2)) = Real.cos t := by
      rw [show 2 * (t / 2) = t by ring]
    rw [← h2t, Real.cos_two_mul_eq_one_sub]
  rw [hcos]
  have hp6 : (0:ℝ) ≤ t * t * t * t * t * t := by
    have h1 : (0:ℝ) ≤ t * t * t := mul_nonneg (mul_self_nonneg t) ht
    calc t * t * t * t * t * t = (t * t * t) * (t * t * t) := by ring
      _ ≥ 0 := mul_nonneg h1 h1
  have hex : 2 * (t / 2 - (t / 2) ^ 3 / 6) ^ 2
      = t * t / 2 - t * t * t * t / 24 + t * t * t * t * t * t / 1152 := by ring
  linarith [hex, hp6]

/-- cos t ≥ 1 − t²/2 + t⁴/24 − t⁶/720（六阶 Taylor 下界，t ∈ [0,1]）. -/
private theorem taylor_cos_lo (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1 - t * t / 2 + t * t * t * t / 24 - t * t * t * t * t * t / 720 ≤ Real.cos t := by
  have hpos3 : ∀ s ∈ Set.Icc 0 t, 0 ≤ Real.sin s + 0 - s + s * s * s / 6 + 0 := by
    intro s hs
    have h := Real.sin_ge_sub_cube hs.1
    have heq : s ^ 3 / 6 = s * s * s / 6 := by ring
    rw [heq] at h
    linarith
  have h3 : ∀ s ∈ Set.Icc 0 t,
      0 ≤ -Real.cos s + 1 - s * s / 2 + s * s * s * s / 24 + 0 :=
    nonneg_of_deriv_chain
      (fun s => -Real.cos s + 1 - s * s / 2 + s * s * s * s / 24 + 0)
      (fun s => Real.sin s + 0 - s + s * s * s / 6 + 0) ht
      (fun s => ((((Real.hasDerivAt_cos s).neg.congr_deriv
          (show -(-Real.sin s) = Real.sin s by ring)).add (hasDerivAt_const s 1)).sub
        (hpow2d2 s)).add (hpow4d24 s) |>.add (hasDerivAt_const s 0))
      hpos3 (by simp)
  have h2 : ∀ s ∈ Set.Icc 0 t,
      0 ≤ -Real.sin s + s - s * s * s / 6 + s * s * s * s * s / 120 + 0 :=
    nonneg_of_deriv_chain
      (fun s => -Real.sin s + s - s * s * s / 6 + s * s * s * s * s / 120 + 0)
      (fun s => -Real.cos s + 1 - s * s / 2 + s * s * s * s / 24 + 0) ht
      (fun s => ((((Real.hasDerivAt_sin s).neg.add (hasDerivAt_id s)).sub
        (hpow3d6 s)).add (hpow5d120 s)).add (hasDerivAt_const s 0))
      h3 (by simp)
  have h1 : ∀ s ∈ Set.Icc 0 t,
      0 ≤ Real.cos s + s * s / 2 - s * s * s * s / 24
        + s * s * s * s * s * s / 720 + -1 :=
    nonneg_of_deriv_chain
      (fun s => Real.cos s + s * s / 2 - s * s * s * s / 24
        + s * s * s * s * s * s / 720 + -1)
      (fun s => -Real.sin s + s - s * s * s / 6 + s * s * s * s * s / 120 + 0) ht
      (fun s => ((((Real.hasDerivAt_cos s).add (hpow2d2 s)).sub (hpow4d24 s)).add
        (hpow6d720 s)).add (hasDerivAt_const s (-1:ℝ)))
      h2 (by simp [Real.cos_zero])
  have h0 := h1 t ⟨ht, le_refl t⟩
  linarith

/-- cos t ≤ 1 − t²/2 + t⁴/24 − t⁶/720 + t⁸/40320（六阶 Taylor 上界，t ∈ [0,1]）. -/
private theorem taylor_cos_hi (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.cos t ≤ 1 - t * t / 2 + t * t * t * t / 24 - t * t * t * t * t * t / 720
      + t * t * t * t * t * t * t * t / 40320 := by
  have hposA : ∀ s ∈ Set.Icc 0 t,
      0 ≤ 0 + 0 + 1 + -(s * s / 2) + s * s * s * s / 24 + -Real.cos s := by
    intro s hs
    have h := cos_le_1_sub_sq_div_two_add s hs.1 (le_trans hs.2 ht1)
    linarith
  have hA : ∀ s ∈ Set.Icc 0 t,
      0 ≤ 0 + 0 + s + -(s * s * s / 6) + s * s * s * s * s / 120 + -Real.sin s :=
    nonneg_of_deriv_chain
      (fun s => 0 + 0 + s + -(s * s * s / 6) + s * s * s * s * s / 120 + -Real.sin s)
      (fun s => 0 + 0 + 1 + -(s * s / 2) + s * s * s * s / 24 + -Real.cos s) ht
      (fun s => ((hasDerivAt_const s 0).add (hasDerivAt_const s 0)).add (hasDerivAt_id s)
        |>.add ((hpow3d6 s).neg) |>.add (hpow5d120 s)
        |>.add ((Real.hasDerivAt_sin s).neg))
      hposA (by simp)
  have hB : ∀ s ∈ Set.Icc 0 t,
      0 ≤ -1 + 0 + s * s / 2 + -(s * s * s * s / 24) + s * s * s * s * s * s / 720
        + Real.cos s :=
    nonneg_of_deriv_chain
      (fun s => -1 + 0 + s * s / 2 + -(s * s * s * s / 24) + s * s * s * s * s * s / 720
        + Real.cos s)
      (fun s => 0 + 0 + s + -(s * s * s / 6) + s * s * s * s * s / 120 + -Real.sin s) ht
      (fun s => ((hasDerivAt_const s (-1:ℝ)).add (hasDerivAt_const s 0)).add (hpow2d2 s)
        |>.add ((hpow4d24 s).neg) |>.add (hpow6d720 s)
        |>.add (Real.hasDerivAt_cos s))
      hA (by simp)
  have hC : ∀ s ∈ Set.Icc 0 t,
      0 ≤ -s + 0 + s * s * s / 6 + -(s * s * s * s * s / 120)
        + s * s * s * s * s * s * s / 5040 + Real.sin s :=
    nonneg_of_deriv_chain
      (fun s => -s + 0 + s * s * s / 6 + -(s * s * s * s * s / 120)
        + s * s * s * s * s * s * s / 5040 + Real.sin s)
      (fun s => -1 + 0 + s * s / 2 + -(s * s * s * s / 24) + s * s * s * s * s * s / 720
        + Real.cos s) ht
      (fun s => (((hasDerivAt_id s).neg).add (hasDerivAt_const s 0)).add (hpow3d6 s)
        |>.add ((hpow5d120 s).neg) |>.add (hpow7d5040 s)
        |>.add (Real.hasDerivAt_sin s))
      hB (by simp)
  have hD : ∀ s ∈ Set.Icc 0 t,
      0 ≤ -(s * s / 2) + 1 + s * s * s * s / 24 + -(s * s * s * s * s * s / 720)
        + s * s * s * s * s * s * s * s / 40320 + -Real.cos s :=
    nonneg_of_deriv_chain
      (fun s => -(s * s / 2) + 1 + s * s * s * s / 24
        + -(s * s * s * s * s * s / 720) + s * s * s * s * s * s * s * s / 40320
        + -Real.cos s)
      (fun s => -s + 0 + s * s * s / 6 + -(s * s * s * s * s / 120)
        + s * s * s * s * s * s * s / 5040 + Real.sin s) ht
      (fun s => (((hpow2d2 s).neg.add (hasDerivAt_const s 1)).add (hpow4d24 s)
        |>.add ((hpow6d720 s).neg) |>.add (hpow8d40320 s)).add
        ((Real.hasDerivAt_cos s).neg.congr_deriv
          (show -(-Real.sin s) = Real.sin s by ring)))
      hC (by simp)
  have := hD t ⟨ht, le_refl t⟩
  linarith


/-! ===== arcLen 与数值种子（件⑤） ===== -/

/-- HOL `arclength a b c`（余弦式 acos）：`arcLen a b c = acos((a²+b²−c²)/(2ab))`. -/
private noncomputable def arcLen (a b c : ℝ) : ℝ :=
  Real.arccos ((a * a + b * b - c * c) / (2 * a * b))

/-- `arcLen` 前两参对称（`arc_sym`）. -/
private theorem arcLen_sym (a b c : ℝ) : arcLen a b c = arcLen b a c := by
  unfold arcLen
  congr 1
  ring

/-- 件⑤a：`arcLen 2 2.52 2 = acos(63/100)`，`arcLen 2.52 2.52 2 = acos(2719/3969)`. -/
private theorem arcLen_num_eqs :
    arcLen 2 2.52 2 = Real.arccos (63 / 100) ∧
      arcLen 2.52 2.52 2 = Real.arccos (2719 / 3969) := by
  unfold arcLen
  constructor <;> congr 1 <;> norm_num

/-- 件⑤b：estimate0 的两个 acos 数值界（认证 Taylor，无浮点）. -/
private theorem cos_8892_ge_063 : Real.cos (8892 / 10000) ≥ 63 / 100 := by
  have h := taylor_cos_lo (8892 / 10000) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

private theorem cos_8162_le_2719_3969 : Real.cos (4081 / 5000) ≤ 2719 / 3969 := by
  have h := taylor_cos_hi (4081 / 5000) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

private theorem cos_816_ge_2719_3969 : Real.cos (204 / 250) ≥ 2719 / 3969 := by
  have h := taylor_cos_lo (204 / 250) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

/-- estimate0：`arcLen 2 2.52 2 − arcLen 2.52 2.52 2 ≥ 0.073`. -/
private theorem estimate0 : arcLen 2 2.52 2 - arcLen 2.52 2.52 2 ≥ 0.073 := by
  obtain ⟨e1, e2⟩ := arcLen_num_eqs
  have h1 : Real.arccos (63 / 100) ≥ 8892 / 10000 := by
    have h := cos_8892_ge_063
    have h2 : Real.arccos (Real.cos (8892 / 10000)) ≤ Real.arccos (63 / 100) :=
      Real.arccos_le_arccos h
    rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h2
    exact le_trans (le_refl _) h2
  have h2 : Real.arccos (2719 / 3969) ≤ 4081 / 5000 := by
    have h := cos_8162_le_2719_3969
    have h3 : Real.arccos (2719 / 3969) ≤ Real.arccos (Real.cos (4081 / 5000)) :=
      Real.arccos_le_arccos h
    rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h3
    exact h3
  rw [e1, e2]
  linarith

/-- 件⑤c：arc_lemma5，`arcLen 2.52 2.52 2 ≥ 0.816`. -/
private theorem arc_lemma5_num : arcLen 2.52 2.52 2 ≥ 0.816 := by
  obtain ⟨_, e2⟩ := arcLen_num_eqs
  have h := cos_816_ge_2719_3969
  have h3 : Real.arccos (Real.cos (204 / 250)) ≤ Real.arccos (2719 / 3969) :=
    Real.arccos_le_arccos h
  rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h3
  rw [e2]
  linarith


/-! ===== 件①：cosine law（arcV 折算 arcLen）===== -/

/-- 线性代数核：`2(v·w) = ‖v‖² + ‖w‖² − ‖v−w‖²`（恒真，无范围前提）. -/
private theorem dot_eq_two_norm (v w : V3) :
    (v ⬝ᵥ w) * 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 - ‖v - w‖ ^ 2 := by
  have hv : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  have hw : inner ℝ w w = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  have hd : inner ℝ (v - w) (v - w) = ‖v - w‖ ^ 2 := real_inner_self_eq_norm_sq (v - w)
  have hc : inner ℝ v w = inner ℝ w v := real_inner_comm w v
  have hed : inner ℝ (v - w) (v - w)
      = inner ℝ v v - inner ℝ v w - inner ℝ w v + inner ℝ w w := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  have hid : inner ℝ v w = v ⬝ᵥ w := inner_eq_dot v w
  linarith

/-- 件①：cosine law。`arcV 0 v w = arcLen ‖v‖ ‖w‖ (dist v w)`（纯算术恒等，
无范围前提——零向量两侧同为 junk 值）. -/
private theorem arcV_eq_arcLen (v w : V3) :
    arcV 0 v w = arcLen ‖v‖ ‖w‖ (dist v w) := by
  rw [arcV, arcLen, dist_zero_right, dist_zero_right, dist_eq_norm]
  refine congrArg Real.arccos ?_
  have hl : ((v - (0:V3)) ⬝ᵥ (w - (0:V3))) = v ⬝ᵥ w := by
    rw [← inner_eq_dot, ← inner_eq_dot]
    simp
  rw [hl]
  have hkey : (v ⬝ᵥ w) * (2 * ‖v‖ * ‖w‖)
      = (‖v‖ * ‖v‖ + ‖w‖ * ‖w‖ - ‖v - w‖ * (‖v - w‖)) * (‖w‖ * ‖v‖) := by
    calc (v ⬝ᵥ w) * (2 * ‖v‖ * ‖w‖) = ((v ⬝ᵥ w) * 2) * (‖v‖ * ‖w‖) := by ring
      _ = (‖v‖ ^ 2 + ‖w‖ ^ 2 - ‖v - w‖ ^ 2) * (‖v‖ * ‖w‖) := by rw [dot_eq_two_norm]
      _ = (‖v‖ * ‖v‖ + ‖w‖ * ‖w‖ - ‖v - w‖ * (‖v - w‖)) * (‖w‖ * ‖v‖) := by ring
  by_cases h0 : ‖w‖ * ‖v‖ = 0
  · rcases mul_eq_zero.mp h0 with hc | hc <;>
      [rw [norm_eq_zero.mp hc]; rw [norm_eq_zero.mp hc]] <;> simp
  · have hvn : ‖v‖ ≠ 0 := fun hc => h0 (by rw [hc, mul_zero])
    have hwn : ‖w‖ ≠ 0 := fun hc => h0 (by rw [hc, zero_mul])
    have h2vn : (2:ℝ) * ‖v‖ ≠ 0 := mul_ne_zero (by norm_num) hvn
    refine div_eq_div_iff (mul_ne_zero hvn hwn) (mul_ne_zero h2vn hwn) |>.mpr ?_
    exact hkey.trans (by ring)

/-- 件②：arc_lemma1（arccos antitone）：`arcLen a b 2 ≤ arcLen a b c`. -/
private theorem arc_lemma1 {a b c : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    arcLen a b 2 ≤ arcLen a b c := by
  have h2ab : (0:ℝ) < 2 * a * b := by nlinarith
  have hc4 : (4:ℝ) ≤ c * c := by nlinarith
  refine Real.arccos_le_arccos ?_
  exact div_le_div_of_nonneg_right (by linarith) h2ab.le

/-! ===== 件③④：φ-机器、凹性、单调性 ===== -/

private noncomputable def arcPhi (b t : ℝ) : ℝ := (t * t + (b * b - 4)) / (2 * b * t)
private noncomputable def arcPhiD (b t : ℝ) : ℝ := (t * t - (b * b - 4)) / (2 * b * (t * t))
private noncomputable def arcPhiDD (b t : ℝ) : ℝ := (b * b - 4) / (b * t * t * t)

private theorem hasDerivAt_arcPhi (b t : ℝ) (hb : b ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun x => arcPhi b x) (arcPhiD b t) t := by
  have h2bt : (2:ℝ) * b * t ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hb) ht
  have h1 : HasDerivAt (fun t => t * t + (b * b - 4)) (2 * t) t :=
    (((hasDerivAt_id t).mul (hasDerivAt_id t)).congr_deriv
      (show 1 * t + t * 1 = 2 * t by ring)).add (hasDerivAt_const t (b * b - 4))
    |>.congr_deriv (show 2 * t + 0 = 2 * t by ring)
  have h2 : HasDerivAt (fun t => 2 * b * t) (2 * b) t :=
    ((hasDerivAt_const t (2 * b)).mul (hasDerivAt_id t)).congr_deriv
      (show 0 * id t + 2 * b * 1 = 2 * b by ring)
  have h := h1.fun_div h2 h2bt
  rw [show ((2 * t * (2 * b * t) - (t * t + (b * b - 4)) * (2 * b)) / (2 * b * t) ^ 2)
      = (t * t - (b * b - 4)) / (2 * b * (t * t)) by
    rw [div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (by norm_num) hb) ht))
      (mul_ne_zero (mul_ne_zero (by norm_num) hb) (mul_ne_zero ht ht))]
    ring] at h
  exact h

private theorem hasDerivAt_arcPhiD (b t : ℝ) (hb : b ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun x => arcPhiD b x) (arcPhiDD b t) t := by
  have hbtt : 2 * b * (t * t) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hb) (mul_ne_zero ht ht)
  have hbttt : b * t * t * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hb ht) ht) ht
  have h1 : HasDerivAt (fun t => t * t - (b * b - 4)) (2 * t) t :=
    (((hasDerivAt_id t).mul (hasDerivAt_id t)).congr_deriv
      (show 1 * t + t * 1 = 2 * t by ring)).sub (hasDerivAt_const t (b * b - 4))
    |>.congr_deriv (show 2 * t - 0 = 2 * t by ring)
  have hA : HasDerivAt (fun t => t * t) (2 * t) t :=
    ((hasDerivAt_id t).mul (hasDerivAt_id t)).congr_deriv
      (show 1 * t + t * 1 = 2 * t by ring)
  have h2 : HasDerivAt (fun t => 2 * b * (t * t)) (4 * b * t) t :=
    (HasDerivAt.const_mul (2 * b) hA).congr_deriv
      (show (2:ℝ) * b * (2 * t) = 4 * b * t by ring)
  have h := h1.fun_div h2 hbtt
  rw [show ((2 * t * (2 * b * (t * t)) - (t * t - (b * b - 4)) * (4 * b * t))
        / (2 * b * (t * t)) ^ 2) = (b * b - 4) / (b * t * t * t) by
    rw [div_eq_div_iff (pow_ne_zero 2 hbtt) hbttt]
    ring] at h
  exact h

/-- `arcPhi b t ∈ (0, 1)` 对 `b, t ∈ [2, 2.52]`（Cauchy–Schwarz 形）. -/
private theorem arcPhi_mem_Ioo (hb : 2 ≤ b) (hb' : b ≤ 2.52) (ht : 2 ≤ t) (ht' : t ≤ 2.52) :
    arcPhi b t ∈ Set.Ioo (0:ℝ) 1 := by
  have hpos : (0:ℝ) < 2 * b * t := by nlinarith
  have hnum : (0:ℝ) < t * t + (b * b - 4) := by
    have h1 : (4:ℝ) ≤ t * t := by nlinarith
    have h2 : (4:ℝ) ≤ b * b := by nlinarith
    linarith
  have hsb : (t - b) ^ 2 < 4 := by
    have q1 : -(2:ℝ) < t - b := by linarith
    have q2 : t - b < 2 := by linarith
    refine lt_of_lt_of_eq (sq_lt_sq' q1 q2) ?_
    norm_num
  constructor
  · unfold arcPhi
    exact div_pos hnum hpos
  · unfold arcPhi
    rw [div_lt_iff₀ hpos]
    nlinarith


/-! ### 件③：凹性（arcLen x b 2 对 x 凹） -/

private theorem concaveOn_arcLen_x {b : ℝ} (hb : 2 ≤ b) (hb' : b ≤ 2.52) :
    ConcaveOn ℝ (Set.Icc 2 2.52) (fun x => arcLen x b 2) := by
  have hb0 : (b:ℝ) ≠ 0 := fun hc => absurd (hb.trans_eq hc) (by norm_num)
  have hmem : ∀ t ∈ Set.Icc 2 2.52, arcPhi b t ∈ Set.Ioo (0:ℝ) 1 :=
    fun t ht => arcPhi_mem_Ioo hb hb' ht.1 ht.2
  have hd1 : ∀ t ∈ Set.Icc 2 2.52, HasDerivAt (arcPhi b) (arcPhiD b t) t :=
    fun t ht => hasDerivAt_arcPhi b t hb0 (by linarith [ht.1])
  have hd2 : ∀ t ∈ Set.Icc 2 2.52, HasDerivAt (arcPhiD b) (arcPhiDD b t) t :=
    fun t ht => hasDerivAt_arcPhiD b t hb0 (by linarith [ht.1])
  have hf'has : ∀ t ∈ Set.Icc 2 2.52,
      HasDerivAt (fun x => arcLen x b 2)
        (-(arcPhiD b t) / Real.sqrt (1 - arcPhi b t * arcPhi b t)) t := by
    intro t ht
    have hc : HasDerivAt (fun x => Real.arccos (arcPhi b x))
        (-(1 / Real.sqrt (1 - arcPhi b t ^ 2)) * arcPhiD b t) t :=
      (Real.hasDerivAt_arccos (by linarith [(hmem t ht).1]) (hmem t ht).2.ne).comp t
        (hd1 t ht)
    have hfe : (fun x => arcLen x b 2)
        = (fun x => Real.arccos (arcPhi b x)) := by
      funext x
      unfold arcLen arcPhi
      congr 1
      ring
    rw [hfe]
    exact hc.congr_deriv (show -(1 / Real.sqrt (1 - arcPhi b t ^ 2)) * arcPhiD b t
      = -(arcPhiD b t) / Real.sqrt (1 - arcPhi b t * arcPhi b t) by ring)
  have hf''has : ∀ t ∈ Set.Icc 2 2.52,
      HasDerivAt (fun x => -(arcPhiD b x) / Real.sqrt (1 - arcPhi b x * arcPhi b x))
        ((-(arcPhiDD b t) * Real.sqrt (1 - arcPhi b t * arcPhi b t)
          - (-(arcPhiD b t))
            * (1 / (2 * Real.sqrt (1 - arcPhi b t * arcPhi b t))
              * -(2 * arcPhi b t * arcPhiD b t)))
        / (Real.sqrt (1 - arcPhi b t * arcPhi b t)) ^ 2) t := by
    intro t ht
    have hWpos : 0 < 1 - arcPhi b t * arcPhi b t := by
      have h2 := hmem t ht
      have hsq : arcPhi b t ^ 2 < 1 ^ 2 :=
        sq_lt_sq' (by linarith [(hmem t ht).1]) (hmem t ht).2
      rw [show (1:ℝ) ^ 2 = 1 by norm_num] at hsq
      nlinarith [hsq]
    have hWne : 1 - arcPhi b t * arcPhi b t ≠ 0 := ne_of_gt hWpos
    have hu : HasDerivAt (fun x => -(arcPhiD b x)) (-(arcPhiDD b t)) t := (hd2 t ht).neg
    have hW' : HasDerivAt (fun x => 1 - arcPhi b x * arcPhi b x)
        (-(2 * arcPhi b t * arcPhiD b t)) t :=
      ((hasDerivAt_const t 1).sub ((hd1 t ht).mul (hd1 t ht))).congr_deriv
        (show 0 - (arcPhiD b t * arcPhi b t + arcPhi b t * arcPhiD b t)
          = -(2 * arcPhi b t * arcPhiD b t) by ring)
    have hs : HasDerivAt (fun x => Real.sqrt (1 - arcPhi b x * arcPhi b x))
        (1 / (2 * Real.sqrt (1 - arcPhi b t * arcPhi b t))
          * -(2 * arcPhi b t * arcPhiD b t)) t :=
      (Real.hasDerivAt_sqrt hWne).comp t hW'
    exact hu.fun_div hs (ne_of_gt (Real.sqrt_pos.mpr hWpos))
  have hf''neg : ∀ t ∈ Set.Icc 2 2.52,
      ((-(arcPhiDD b t) * Real.sqrt (1 - arcPhi b t * arcPhi b t)
          - (-(arcPhiD b t))
            * (1 / (2 * Real.sqrt (1 - arcPhi b t * arcPhi b t))
              * -(2 * arcPhi b t * arcPhiD b t)))
        / (Real.sqrt (1 - arcPhi b t * arcPhi b t)) ^ 2) ≤ 0 := by
    intro t ht
    have hWpos : 0 < 1 - arcPhi b t * arcPhi b t := by
      have h2 := hmem t ht
      have hsq : arcPhi b t ^ 2 < 1 ^ 2 :=
        sq_lt_sq' (by linarith [(hmem t ht).1]) (hmem t ht).2
      rw [show (1:ℝ) ^ 2 = 1 by norm_num] at hsq
      nlinarith [hsq]
    have hsWpos : (0:ℝ) < Real.sqrt (1 - arcPhi b t * arcPhi b t) :=
      Real.sqrt_pos.mpr hWpos
    have hphi := hmem t ht
    have hphiDpos : (0:ℝ) < arcPhiD b t := by
      unfold arcPhiD
      have tt : (4:ℝ) ≤ t * t := by
        have h2 : (2:ℝ) ^ 2 ≤ t ^ 2 := sq_le_sq' (by linarith [ht.1]) ht.1
        have he : t ^ 2 = t * t := pow_two t
        rw [he] at h2
        linarith [h2, (show (2:ℝ) ^ 2 = 4 by norm_num)]
      have bb : b * b ≤ 2.52 * 2.52 := by
        have h2 : b ^ 2 ≤ (2.52:ℝ) ^ 2 := sq_le_sq' (by linarith) hb'
        have he : b ^ 2 = b * b := pow_two b
        rw [he] at h2
        linarith [h2, (show (2.52:ℝ) ^ 2 = 6.3504 by norm_num)]
      exact div_pos (by linarith [tt, bb])
        (mul_pos (show (0:ℝ) < 2 * b by linarith)
          (show (0:ℝ) < t * t by linarith [tt]))
    have hphiDDnn : 0 ≤ arcPhiDD b t := by
      unfold arcPhiDD
      have h22 : (2:ℝ) ≤ b := hb
      have k1 : (4:ℝ) ≤ 2 * b := by
        have h := mul_le_mul_of_nonneg_left h22 (show (0:ℝ) ≤ 2 by norm_num)
        rwa [show (2:ℝ) * 2 = 4 by norm_num] at h
      have k2 : (2:ℝ) * b ≤ b * b :=
        mul_le_mul_of_nonneg_right h22 (show (0:ℝ) ≤ b by linarith)
      have hbb : (4:ℝ) ≤ b * b := le_trans k1 k2
      exact div_nonneg (sub_nonneg.mpr hbb)
        (le_of_lt (mul_pos (mul_pos (mul_pos (by linarith) (by linarith [ht.1]))
          (by linarith [ht.1])) (by linarith [ht.1])))
    rw [Real.sq_sqrt hWpos.le, div_le_iff₀ hWpos, zero_mul]
    have h1 : -(arcPhiDD b t) * Real.sqrt (1 - arcPhi b t * arcPhi b t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hphiDDnn) hsWpos.le
    have h2 : -(arcPhiD b t)
        * (1 / (2 * Real.sqrt (1 - arcPhi b t * arcPhi b t))
          * -(2 * arcPhi b t * arcPhiD b t)) ≥ 0 := by
      have h2p : (0:ℝ) ≤ 2 * arcPhi b t * arcPhiD b t :=
        mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hphi.1)) (le_of_lt hphiDpos)
      have h2s : (0:ℝ) < 2 * Real.sqrt (1 - arcPhi b t * arcPhi b t) :=
        mul_pos (show (0:ℝ) < 2 by norm_num) hsWpos
      have hinner : (1 / (2 * Real.sqrt (1 - arcPhi b t * arcPhi b t))
          * -(2 * arcPhi b t * arcPhiD b t)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt (div_pos (by norm_num) h2s))
          (neg_nonpos.mpr h2p)
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (le_of_lt hphiDpos)) hinner
    linarith
  refine concaveOn_of_hasDerivWithinAt2_nonpos (D := Set.Icc 2 2.52)
    (f := fun x => arcLen x b 2)
    (f' := fun x => -(arcPhiD b x) / Real.sqrt (1 - arcPhi b x * arcPhi b x))
    (f'' := fun x => ((-(arcPhiDD b x) * Real.sqrt (1 - arcPhi b x * arcPhi b x)
      - (-(arcPhiD b x)) * (1 / (2 * Real.sqrt (1 - arcPhi b x * arcPhi b x))
        * -(2 * arcPhi b x * arcPhiD b x)))
      / (Real.sqrt (1 - arcPhi b x * arcPhi b x)) ^ 2))
    (convex_Icc 2 2.52) ?_ ?_ ?_ ?_
  · have hd : DifferentiableOn ℝ (arcPhi b) (Set.Icc 2 2.52) :=
      fun t ht => (hd1 t ht).differentiableAt.differentiableWithinAt
    refine (Real.continuous_arccos.continuousOn.comp hd.continuousOn
      (fun t _ => Set.mem_univ _)).congr (fun x _ => ?_)
    show arcLen x b 2 = Real.arccos (arcPhi b x)
    unfold arcLen arcPhi
    congr 1
    ring
  · intro t ht
    have ht' : t ∈ Set.Ioo 2 2.52 := by rw [← interior_Icc]; exact ht
    exact HasDerivAt.hasDerivWithinAt (s := interior (Set.Icc (2:ℝ) 2.52))
      (hf'has t ⟨ht'.1.le, ht'.2.le⟩)
  · intro t ht
    have ht' : t ∈ Set.Ioo 2 2.52 := by rw [← interior_Icc]; exact ht
    exact HasDerivAt.hasDerivWithinAt (s := interior (Set.Icc (2:ℝ) 2.52))
      (hf''has t ⟨ht'.1.le, ht'.2.le⟩)
  · intro t ht
    have ht' : t ∈ Set.Ioo 2 2.52 := by rw [← interior_Icc]; exact ht
    exact hf''neg t ⟨ht'.1.le, ht'.2.le⟩

/-! ### 件③b：arc_lemma3（lmfun 插值下界，HOL arc_properties.hl:720） -/

-- 注记：本节自带两枚 lmfun 辅助件副本（`lmfun_nonneg`/`lmfun_le_one_of_one_le`
-- 在本文件 §7b :2114 声明，位于本节之后，前向引用不可用，故改名自带）。
private theorem arc_lmfun_nonneg (h : ℝ) : 0 ≤ lmfun h := by
  have h0126 : h0 = 1.26 := rfl
  unfold lmfun
  split
  · next hh =>
    exact div_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr (by rw [h0126]; norm_num))
  · next => exact le_refl 0

private theorem arc_lmfun_le_one {h : ℝ} (hh : 1 ≤ h) : lmfun h ≤ 1 := by
  have h0126 : h0 = 1.26 := rfl
  unfold lmfun
  split
  · next hhle =>
    have hd : (0:ℝ) < h0 - 1 := by rw [h0126]; norm_num
    rw [div_le_one hd]
    linarith
  · next => linarith

/-- 件③b：`arcLen x b 2 ≥ arcLen 2.52 b 2 + lmfun(x/2)·(arcLen 2 b 2 − arcLen 2.52 b 2)`
（凹性 + 插值恒等式 `lmfun(x/2)·2 + (1−lmfun(x/2))·2.52 = x`，lmfun 递减形
`(h0−h)/(h0−1)` 使权重对齐）. -/
private theorem arc_lemma3 {x b : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 2.52)
    (hb : 2 ≤ b) (hb' : b ≤ 2.52) :
    arcLen 2.52 b 2 + lmfun (x / 2) * (arcLen 2 b 2 - arcLen 2.52 b 2) ≤ arcLen x b 2 := by
  have hconc := concaveOn_arcLen_x hb hb'
  have hmem2 : (2:ℝ) ∈ Set.Icc 2 2.52 := ⟨le_refl 2, by norm_num⟩
  have hmem252 : (2.52:ℝ) ∈ Set.Icc 2 2.52 := ⟨by norm_num, le_refl 2.52⟩
  have h01 : h0 = (1.26:ℝ) := rfl
  have hxs : x / 2 ≤ h0 := by linarith
  have hu01 : 0 ≤ lmfun (x / 2) := arc_lmfun_nonneg _
  have hu1 : lmfun (x / 2) ≤ 1 := arc_lmfun_le_one (by linarith)
  have huxt : lmfun (x / 2) * 2 + (1 - lmfun (x / 2)) * 2.52 = x := by
    have hp : (0:ℝ) < h0 - 1 := by rw [h01]; norm_num
    unfold lmfun
    rw [if_pos hxs, h01]
    field_simp
    ring
  have hinterp : (lmfun (x / 2)) • arcLen 2 b 2
      + (1 - lmfun (x / 2)) • arcLen 2.52 b 2
      ≤ arcLen (lmfun (x / 2) • 2 + (1 - lmfun (x / 2)) • 2.52) b 2 :=
    hconc.2 hmem2 hmem252 hu01 (by linarith) (by ring)
  simp only [smul_eq_mul] at hinterp
  rw [huxt] at hinterp
  have hrearr : lmfun (x / 2) * arcLen 2 b 2 + (1 - lmfun (x / 2)) * arcLen 2.52 b 2
      = arcLen 2.52 b 2 + lmfun (x / 2) * (arcLen 2 b 2 - arcLen 2.52 b 2) := by
    ring
  rw [hrearr] at hinterp
  exact hinterp

/-! ### 件④：arc_lemma4（F 单调 + estimate0 链） -/

/-- `arcPhi 2 t = t / 4`（退化形）. -/
private theorem arcPhi_2_eq (t : ℝ) (ht : t ≠ 0) : arcPhi 2 t = t / 4 := by
  unfold arcPhi
  field_simp
  ring

/-- `arcPhiD 2 t = 1 / 4`. -/
private theorem arcPhiD_2_eq (t : ℝ) (ht : t ≠ 0) : arcPhiD 2 t = 1 / 4 := by
  unfold arcPhiD
  field_simp
  ring

/-- arcLen x b 2 对 x 的导数（件④用）. -/
private theorem hasDerivAt_arcLen_x (b t : ℝ) (hb : 2 ≤ b) (hb' : b ≤ 2.52)
    (ht : 2 ≤ t) (ht' : t ≤ 2.52) :
    HasDerivAt (fun x => arcLen x b 2)
      (-(arcPhiD b t) / Real.sqrt (1 - arcPhi b t * arcPhi b t)) t := by
  have hphi : HasDerivAt (arcPhi b) (arcPhiD b t) t :=
    hasDerivAt_arcPhi b t (by linarith) (by linarith)
  have hmem : arcPhi b t ∈ Set.Ioo (0:ℝ) 1 := arcPhi_mem_Ioo hb hb' ht ht'
  have hc : HasDerivAt (fun x => Real.arccos (arcPhi b x))
      (-(1 / Real.sqrt (1 - arcPhi b t ^ 2)) * arcPhiD b t) t :=
    (Real.hasDerivAt_arccos (by linarith [hmem.1]) hmem.2.ne).comp t hphi
  have hfe : (fun x => arcLen x b 2) = (fun x => Real.arccos (arcPhi b x)) := by
    funext x
    unfold arcLen arcPhi
    congr 1
    ring
  rw [hfe]
  exact hc.congr_deriv (show -(1 / Real.sqrt (1 - arcPhi b t ^ 2)) * arcPhiD b t
    = -(arcPhiD b t) / Real.sqrt (1 - arcPhi b t * arcPhi b t) by ring)

/-- 件④：arc_lemma4。`arcLen 2 x 2 − arcLen 2.52 x 2 ≥ 0.073`. -/
private theorem arc_lemma4 {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 2.52) :
    0.073 ≤ arcLen 2 x 2 - arcLen 2.52 x 2 := by
  have hx0 : (x:ℝ) ≠ 0 := by linarith
  have htt : (4:ℝ) ≤ x * x := by nlinarith [hx]
  have htt' : x * x ≤ 6.3504 := by
    have hx2 : (0:ℝ) ≤ x := by linarith
    have k1 : x * x ≤ x * 2.52 := mul_le_mul_of_nonneg_left hx' hx2
    have k2 : x * 2.52 ≤ (2.52:ℝ) * 2.52 := mul_le_mul_of_nonneg_right hx' (by norm_num)
    have he2 : (2.52:ℝ) * 2.52 = 6.3504 := by norm_num
    calc x * x ≤ x * 2.52 := k1
      _ ≤ (2.52:ℝ) * 2.52 := k2
      _ = 6.3504 := he2
  have hmono : MonotoneOn (fun t => arcLen t 2.52 2 - arcLen t 2 2) (Set.Icc 2 2.52) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 2 2.52) ?_ ?_ ?_
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := ht.1
      have hd1 : DifferentiableAt ℝ (fun u => arcLen u 2.52 2) t :=
        (hasDerivAt_arcLen_x 2.52 t (by norm_num) (by norm_num) ht2 ht.2).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun u => arcLen u 2 2) t :=
        (hasDerivAt_arcLen_x 2 t (by norm_num) (by norm_num) ht2 ht.2).differentiableAt
      exact (hd1.sub hd2).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo 2 2.52 := by rw [← interior_Icc]; exact ht
      have ht2 : (2:ℝ) ≤ t := by linarith [ht'.1]
      have hbm : (2:ℝ) ≤ 2.52 := by norm_num
      exact DifferentiableAt.differentiableWithinAt
        (s := interior (Set.Icc (2:ℝ) 2.52))
        (((hasDerivAt_arcLen_x 2.52 t hbm (by norm_num) ht2 ht'.2.le).differentiableAt).sub
          ((hasDerivAt_arcLen_x 2 t (by norm_num) hbm ht2 ht'.2.le).differentiableAt))
    · intro t ht
      have ht' : t ∈ Set.Ioo 2 2.52 := by rw [← interior_Icc]; exact ht
      have ht2 : (2:ℝ) ≤ t := by linarith [ht'.1]
      have ht2' : t ≤ 2.52 := ht'.2.le
      have hD1le : arcPhiD 2.52 t ≤ 13 / 100 := by
        unfold arcPhiD
        rw [div_le_iff₀ (by nlinarith [ht2, ht2'])]
        nlinarith [ht2, ht2']
      have hphi0 : 0 < arcPhi 2.52 t := by
        unfold arcPhi
        have hnum : (0:ℝ) < t * t + (2.52 * 2.52 - 4) := by
          have h1 : (4:ℝ) ≤ t * t := by nlinarith [ht2]
          linarith
        exact div_pos hnum (by nlinarith [ht2, ht2'])
      have hphi34 : arcPhi 2.52 t ≤ 3 / 4 := by
        unfold arcPhi
        rw [div_le_iff₀ (by nlinarith [ht2, ht2'])]
        have hp : (t - 2) * (t - 2.52) ≤ 0 := by nlinarith [ht2, ht2']
        have hgoal : t * t + (2.52 * 2.52 - 4) - (3 / 4) * (2 * 2.52 * t) ≤ 0 := by
          have hexp : t * t + (2.52 * 2.52 - 4) - (3 / 4) * (2 * 2.52 * t)
              = (t - 2) * (t - 2.52) + 0.74 * t - 2.6896 := by ring
          rw [hexp]
          nlinarith [hp, ht2, ht2']
        linarith [hgoal]
      have hW : (1:ℝ) / 4 ≤ 1 - arcPhi 2.52 t * arcPhi 2.52 t := by
        have hsq : arcPhi 2.52 t * arcPhi 2.52 t ≤ arcPhi 2.52 t * (3 / 4) :=
          mul_le_mul_of_nonneg_left hphi34 (le_of_lt hphi0)
        linarith [hsq, hphi34]
      have hs12 : (1:ℝ) / 2 ≤ Real.sqrt (1 - arcPhi 2.52 t * arcPhi 2.52 t) := by
        have hsq1 : ((1:ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
        exact (Real.le_sqrt (by norm_num) (by linarith [hW])).mpr (by
          rw [hsq1]; exact hW)
      have hs1pos : (0:ℝ) < Real.sqrt (1 - arcPhi 2.52 t * arcPhi 2.52 t) :=
        lt_of_lt_of_le (by norm_num) hs12
      have ht0 : t ≠ 0 := by linarith [ht'.1]
      have hF : HasDerivAt (fun u => arcLen u 2.52 2 - arcLen u 2 2)
          (-(arcPhiD 2.52 t) / Real.sqrt (1 - arcPhi 2.52 t * arcPhi 2.52 t)
            - -(arcPhiD 2 t) / Real.sqrt (1 - arcPhi 2 t * arcPhi 2 t)) t :=
        (hasDerivAt_arcLen_x 2.52 t (by norm_num) (by norm_num) ht2 ht2').sub
          (hasDerivAt_arcLen_x 2 t (by norm_num) (by norm_num) ht2 ht2')
      rw [hF.deriv, arcPhiD_2_eq t ht0, arcPhi_2_eq t ht0]
      simp only [neg_div]
      have hu : (arcPhiD 2.52 t) / Real.sqrt (1 - arcPhi 2.52 t * arcPhi 2.52 t)
          ≤ 13 / 50 := by
        rw [div_le_iff₀ hs1pos]
        calc arcPhiD 2.52 t ≤ 13 / 100 := hD1le
          _ = (13 / 50) * (1 / 2) := by norm_num
          _ ≤ (13 / 50) * Real.sqrt (1 - arcPhi 2.52 t * arcPhi 2.52 t) :=
            mul_le_mul_of_nonneg_left hs12 (by norm_num)
      have hv : (7:ℝ) / 25 ≤ (1:ℝ) / 4 / Real.sqrt (1 - (t / 4) * (t / 4)) := by
        have hs2pos : (0:ℝ) < Real.sqrt (1 - (t / 4) * (t / 4)) :=
          Real.sqrt_pos.mpr (by nlinarith [htt])
        have hq28 : Real.sqrt (1 - (t / 4) * (t / 4)) ≤ 25 / 28 := by
          refine (Real.sqrt_le_left (by positivity)).mpr ?_
          nlinarith [htt]
        rw [le_div_iff₀ hs2pos]
        have hmul : (7:ℝ) / 25 * Real.sqrt (1 - (t / 4) * (t / 4))
            ≤ (7:ℝ) / 25 * (25 / 28) := mul_le_mul_of_nonneg_left hq28 (by norm_num)
        exact hmul.trans (by norm_num)
      linarith
  have hFge := hmono ⟨hx, hx'⟩ ⟨by norm_num, le_refl 2.52⟩ (le_trans hx' (by norm_num))
  have hE' : arcLen 2.52 2 2 - arcLen 2.52 2.52 2 ≥ 0.073 := by
    rw [← arcLen_sym 2 2.52 2]
    exact estimate0
  rw [arcLen_sym 2 x 2, arcLen_sym 2.52 x 2]
  linarith


/-! ### 帽石装配：face 轨道 fst/snd 和互换（HOL FACE_SUM_lemma 的鸽笼路线，
绕开 SUM_ORBIT 的轨道周期性（WRGCVDR 内容）） -/

private theorem arc_two_le_norm_of_mem_ballAnnulus {v : V3} (hv : v ∈ ballAnnulus) :
    2 ≤ ‖v‖ := by
  simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball] at hv
  push_neg at hv
  have h2 : dist v 0 = ‖v‖ := by rw [dist_eq_norm, sub_zero]
  linarith [h2]

/-- HOL `SUM_LE`：有限集上逐点 ≤ ⟹ 和 ≤（setSum 对 setSum 版单调性；
`setSum_le_of_le` 是对 `card * c` 的形状，不适用）. -/
private theorem setSum_mono_pt {α : Type*} {s : Set α} {g h : α → ℝ}
    (hs : s.Finite) (hle : ∀ y ∈ s, g y ≤ h y) : setSum s g ≤ setSum s h := by
  rw [setSum, setSum, dif_pos hs, dif_pos hs]
  exact Finset.sum_le_sum (fun y hy => hle y ((Set.Finite.mem_toFinset hs).mp hy))

/-- face 轨道上的和换元：`Σ g(snd) = Σ g(fst)`。faceMap 限制在 face 轨道上
是单射自映射（`faceMap d.1 = d.2`），有限集上单射自映射满（鸽笼），
故可整体重排——不需要轨道周期性。 -/
private theorem face_sum_snd_eq_fst (hfan : FAN 0 V E) {x : V3 × V3}
    (hx : x ∈ (hypermapOfFanTl V E hfan).darts) (g : V3 → ℝ) :
    setSum ((hypermapOfFanTl V E hfan).face x) (fun d => g d.2)
      = setSum ((hypermapOfFanTl V E hfan).face x) (fun d => g d.1) := by
  classical
  set H := hypermapOfFanTl V E hfan with hHdef
  have hsubd : ∀ y ∈ H.face x, y ∈ dart1OfFan V E := by
    intro y hy
    have hmem := H.face_subset_darts hx hy
    rwa [dartsTl_coe] at hmem
  have hffe : (H.face x).Finite := by
    have hsub := H.face_subset_darts hx
    rw [dartsTl_coe] at hsub
    exact (finite_dart1_fan hfan).subset hsub
  -- 前向封闭：fMap 保持 face 轨道
  have hfw : ∀ y ∈ (H.face x : Set (V3 × V3)),
      H.faceMap y ∈ (H.face x : Set (V3 × V3)) := by
    intro y hy
    simp only [Hypermap.face, orbitMap, Set.mem_setOf_eq] at hy ⊢
    obtain ⟨n, hn⟩ := hy
    exact ⟨n + 1, by
      rw [Equiv.Perm.coe_pow, Function.iterate_succ_apply', ← Equiv.Perm.coe_pow, hn]⟩
  rw [setSum, setSum, dif_pos hffe, dif_pos hffe]
  refine Finset.sum_bij (fun y _ => H.faceMap y) ?_ ?_ ?_ ?_
  · -- 前向封闭：fMap y ∈ face x
    intro y hy
    exact (Set.Finite.mem_toFinset hffe).mpr
      (hfw y ((Set.Finite.mem_toFinset hffe).mp hy))
  · intro y _ z _ hcon
    exact H.faceMap.injective hcon
  · -- 鸽笼满射：face 上单射自映射的像 = 自身
    intro z hz
    have hinjF : Set.InjOn (fun d : V3 × V3 => H.faceMap d)
        (↑(hffe.toFinset) : Set (V3 × V3)) :=
      fun a _ b _ hcon => H.faceMap.injective hcon
    have hcardimg : (hffe.toFinset.image (fun d : V3 × V3 => H.faceMap d)).card
        = hffe.toFinset.card := Finset.card_image_of_injOn hinjF
    have himg : hffe.toFinset.image (fun d : V3 × V3 => H.faceMap d)
        = hffe.toFinset := by
      refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr
        (fun y hy => ?_)) ?_
      · exact (Set.Finite.mem_toFinset hffe).mpr
          (hfw y ((Set.Finite.mem_toFinset hffe).mp hy))
      · rw [hcardimg]
    have hzin : z ∈ hffe.toFinset.image (fun d : V3 × V3 => H.faceMap d) := by
      rw [himg]; exact hz
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hzin
    exact ⟨y, hy, hyz⟩
  · -- 点态：fMap y 的第一分量 = y 的第二分量
    intro y hy
    have hd : y ∈ dart1OfFan V E := hsubd y ((Set.Finite.mem_toFinset hffe).mp hy)
    show g y.2 = g (H.faceMap y).1
    rw [faceMapTl_apply hd]
    rfl

/-! `theorem CRTTXAT` 本体移至 §7c（依赖 §7b 的 `CRTTXAT_lemma1`，文内禁止前向引用）。 -/

/-! ## 7b. HRXEFDM 章（tame/HRXEFDM.hl）与 CRTTXAT 支撑（tame/CRTTXAT.hl:90-225）

2026-10-12 B6-U1/U2 首波落地：orbit 划分和工具 + node 轨道 azim·lmfun 和 +
`HRXEFDM_lemma1`（face 集双和 = 2π·scriptL V）+ `CRTTXAT_lemma1`
（face 上 lmfun∘h_dart ≥ 12 + card f − card V）。
帽石（CRTTXAT 本体 / sum_tauVEF_upper_bound）的前置缺口见各自原位 NEEDS 注记。-/

/-! ### 轨道划分和（generic） -/

private theorem setSum_setOfOrbits {α : Type*} [DecidableEq α] (D : Finset α)
    (f : Equiv.Perm α) (hf : PermutesOn f D) (g : α → ℝ) :
    setSum (setOfOrbits D f) (fun o => setSum o g) = setSum (↑D : Set α) g := by
  classical
  have hFO : (setOfOrbits D f).Finite := setOfOrbits_finite D f
  set S : Finset (Set α) := hFO.toFinset with hSdef
  have hmemS : ∀ o ∈ S, o ∈ setOfOrbits D f := by
    intro o ho
    exact (Set.Finite.mem_toFinset hFO).mp (Finset.mem_coe.mp ho)
  have hdisj : (↑S : Set (Set α)).PairwiseDisjoint
      (fun o : Set α => if h : o.Finite then h.toFinset else ∅) := by
    intro o₁ h₁ o₂ h₂ hne
    obtain ⟨x, hx, rfl⟩ := hmemS o₁ h₁
    obtain ⟨y, hy, rfl⟩ := hmemS o₂ h₂
    rcases orbitMap_disjoint_or_eq hf x y with hd | he
    · refine Finset.disjoint_left.mpr ?_
      intro a ha hab
      simp only [dif_pos (orbitMap_finite hf x), dif_pos (orbitMap_finite hf y)] at ha hab
      have hm : a ∈ (orbitMap f x ∩ orbitMap f y : Set α) :=
        ⟨(Set.Finite.mem_toFinset (orbitMap_finite hf x)).mp ha,
          (Set.Finite.mem_toFinset (orbitMap_finite hf y)).mp hab⟩
      rw [hd] at hm
      exact absurd hm (by simp)
    · exact absurd he hne
  have hinner : ∀ o ∈ S, setSum o g
      = ∑ y ∈ (fun o : Set α => if h : o.Finite then h.toFinset else ∅) o, g y := by
    intro o ho
    obtain ⟨x, hx, rfl⟩ := hmemS o ho
    rw [setSum, dif_pos (orbitMap_finite hf x)]
    simp only [dif_pos (orbitMap_finite hf x)]
  have huni : (S.biUnion (fun o : Set α => if h : o.Finite then h.toFinset else ∅) : Finset α)
      = D := by
    ext y
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨o, ho, hyo⟩
      obtain ⟨x, hx, rfl⟩ := hmemS o ho
      simp only [dif_pos (orbitMap_finite hf x)] at hyo
      have hyD : y ∈ (orbitMap f x : Set α) :=
        (Set.Finite.mem_toFinset (orbitMap_finite hf x)).mp hyo
      have hsub := orbitMap_subset_of_permutesOn hf hx hyD
      simpa using hsub
    · intro hy
      refine ⟨orbitMap f y, ?_, ?_⟩
      · rw [hSdef]
        exact Set.Finite.mem_toFinset hFO |>.mpr ⟨y, by simpa using hy, rfl⟩
      · simp only [dif_pos (orbitMap_finite hf y)]
        exact (Set.Finite.mem_toFinset (orbitMap_finite hf y)).mpr
          (pow_apply_mem_orbitMap f 0 y)
  have hstep : ∑ o ∈ S,
      ∑ y ∈ (fun o : Set α => if h : o.Finite then h.toFinset else ∅) o, g y
      = ∑ y ∈ D, g y := by
    rw [← huni]
    exact (Finset.sum_biUnion (t := fun (o : Set α) => if h : o.Finite then h.toFinset else ∅)
      (f := fun y => g y) hdisj).symm
  have hD : Set.Finite.toFinset D.finite_toSet = D := by ext y; simp
  rw [setSum, setSum, dif_pos hFO, dif_pos D.finite_toSet, hD, ← hSdef]
  rw [Finset.sum_congr rfl (fun o ho => hinner o ho)]
  exact hstep

/-! ### SUM_IMAGE 双生 -/

private theorem setSum_image_injOn {α β : Type*} [DecidableEq β] {s : Set α} (hs : s.Finite)
    {φ : α → β} (hφ : Set.InjOn φ s) (g : β → ℝ) :
    setSum (φ '' s) g = setSum s (fun x => g (φ x)) := by
  have hfin : (φ '' s).Finite := hs.image φ
  rw [setSum, setSum, dif_pos hfin, dif_pos hs]
  refine (Finset.sum_bij (fun x _ => φ x) ?_ ?_ ?_ ?_).symm
  · intro x hx
    exact (Set.Finite.mem_toFinset hfin).mpr
      ⟨x, (Set.Finite.mem_toFinset hs).mp hx, rfl⟩
  · intro x hx y hy heq
    exact hφ ((Set.Finite.mem_toFinset hs).mp hx) ((Set.Finite.mem_toFinset hs).mp hy) heq
  · intro y hy
    obtain ⟨x, hx, hex⟩ := (Set.mem_image φ s y).mp
      ((Set.Finite.mem_toFinset hfin).mp hy)
    exact ⟨x, (Set.Finite.mem_toFinset hs).mpr hx, hex⟩
  · intro x hx
    rfl

/-! ### lmfun 辅助 -/

private theorem lmfun_nonneg (h : ℝ) : 0 ≤ lmfun h := by
  have h0126 : h0 = 1.26 := rfl
  unfold lmfun
  split
  · next hh =>
    exact div_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr (by rw [h0126]; norm_num))
  · next => exact le_refl 0

private theorem lmfun_le_one_of_one_le {h : ℝ} (hh : 1 ≤ h) : lmfun h ≤ 1 := by
  have h0126 : h0 = 1.26 := rfl
  unfold lmfun
  split
  · next hhle =>
    have hd : (0:ℝ) < h0 - 1 := by rw [h0126]; norm_num
    rw [div_le_one hd]
    linarith
  · next => linarith

private theorem two_le_norm_of_mem_ballAnnulus {v : V3} (hv : v ∈ ballAnnulus) :
    2 ≤ ‖v‖ := by
  simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball] at hv
  push_neg at hv
  have h2 : dist v 0 = ‖v‖ := by rw [dist_eq_norm, sub_zero]
  linarith [h2]

/-! ### face 上 fst 单射（SIMPLE_HYPERMAP_lemma 折算） -/

section FanLemmas

variable {V : Set V3} {E : Set (Set V3)}

private theorem face_fst_injOn (hfan : FAN 0 V E)
    (hsimple : (hypermapOfFanTl V E hfan).Simple) {x : V3 × V3}
    (hx : x ∈ (hypermapOfFanTl V E hfan).darts) :
    Set.InjOn (Prod.fst : V3 × V3 → V3) ((hypermapOfFanTl V E hfan).face x) := by
  set H := hypermapOfFanTl V E hfan with hHdef
  intro y hy z hz heq
  have hface_eq : H.face y = H.face x := orbitMap_eq_of_mem H.faceMap_permutes hy
  have hyd : y ∈ dart1OfFan V E := dartsTl_mem (H.face_subset_darts hx hy)
  have hzy : z ∈ H.face y := by rw [hface_eq]; exact hz
  have hydarts : y ∈ H.darts := Finset.mem_coe.mpr (H.face_subset_darts hx hy)
  have hzd : z ∈ dart1OfFan V E := by
    have h := H.face_subset_darts hydarts hzy
    rw [hHdef, dartsTl_coe] at h
    exact h
  have hzwV : z.2 ∈ V := (FAN_in_setOfEdge 0 V E z.1 z.2 hfan hzd).2.1
  have hznode : z ∈ H.node y := by
    rw [nodeTl_eq_image hfan hyd]
    refine ⟨z.2, ⟨?_, hzwV⟩, ?_⟩
    · rw [heq]; exact hzd
    · rw [heq]
  have hydarts : y ∈ H.darts := H.face_subset_darts hx hy
  have hmem : z ∈ H.node y ∩ H.face y := ⟨hznode, by rw [hface_eq]; exact hz⟩
  rw [hsimple y hydarts] at hmem
  exact (Set.mem_singleton_iff.mp hmem).symm

end FanLemmas

/-! ### node 轨道 azim 和（FAN-only；SUM_AZIM_DART node 形的去 surrounded 版） -/

section NodeSum

variable {V : Set V3} {E : Set (Set V3)}

private theorem node_sum_azim (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    setSum ((hypermapOfFanTl V E hfan).node d) (fun y => azimDart V E y) = 2 * Real.pi := by
  set H := hypermapOfFanTl V E hfan with hHdef
  rcases Nat.lt_or_ge (setOfEdge d.1 V E).ncard 2 with h1 | h2
  · -- card(soe d.1) ≤ 1：card = 1，node d = {d}，azimDart d = 2π
    have hdm : d.2 ∈ setOfEdge d.1 V E := (FAN_in_setOfEdge 0 V E d.1 d.2 hfan hd).2.2.1
    have hpos : 0 < (setOfEdge d.1 V E).ncard :=
      Iff.mpr (Set.ncard_pos (hs := remark_finite_fan1 d.1 V E hfan.2.2.1.1)) ⟨d.2, hdm⟩
    have hcard1 : (setOfEdge d.1 V E).ncard = 1 := by omega
    obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcard1
    have hx2 : x = d.2 := by
      have h2' : d.2 ∈ setOfEdge d.1 V E := hdm
      rw [hx] at h2'
      exact (Set.mem_singleton_iff.mp h2').symm
    have hsoe : setOfEdge d.1 V E = {d.2} := by rw [hx, hx2]
    have hnode : H.node d = {d} := by
      rw [nodeTl_eq_image hfan hd, hsoe, Set.image_singleton]
    have hncard1 : ¬ ((setOfEdge d.1 V E).ncard > 1) := by
      rw [hsoe, Set.ncard_singleton]
      simp
    have hazim : azimDart V E d = 2 * Real.pi := by
      show (if d.1 = d.2 then 2 * Real.pi
        else if (setOfEdge d.1 V E).ncard > 1 then
          azim 0 d.1 d.2 (sigmaFan 0 V E d.1 d.2)
        else 2 * Real.pi) = 2 * Real.pi
      rw [if_neg (edge_ne_of_fan hfan hd), if_neg hncard1]
    rw [hnode, setSum, dif_pos (Set.finite_singleton d), Set.Finite.toFinset_singleton,
      Finset.sum_singleton]
    exact hazim
  · -- card ≥ 2：σ-循环双射 + sum_azims_eq_2pi
    have hne_u : setOfEdge d.1 V E ≠ {d.2} := by
      intro he
      rw [he, Set.ncard_singleton] at h2
      omega
    have hdE : {d.1, d.2} ∈ E := hd
    have hfin : (H.node d).Finite := orbitMap_finite H.nodeMap_permutes d
    have step1 : (∑ i ∈ Finset.range (setOfEdge d.1 V E).ncard,
          azimDart V E (d.1, (sigmaFan 0 V E d.1)^[i] d.2))
        = setSum (H.node d) (fun y => azimDart V E y) := by
      rw [setSum, dif_pos hfin]
      refine Finset.sum_bij (fun i _ => (d.1, (sigmaFan 0 V E d.1)^[i] d.2)) ?_ ?_ ?_ ?_
      · intro i hi
        have hmem : (d.1, (sigmaFan 0 V E d.1)^[i] d.2) ∈ H.node d := by
          have h1' : H.nodeMap^[i] d = (d.1, (sigmaFan 0 V E d.1)^[i] d.2) :=
            nodeMapTl_iterate hd i
          rw [← h1']
          exact pow_apply_mem_orbitMap H.nodeMap i d
        exact (Set.Finite.mem_toFinset hfin).mpr hmem
      · intro i hi j hj heq
        have hin : i < (setOfEdge d.1 V E).ncard := Finset.mem_range.mp hi
        have hjn : j < (setOfEdge d.1 V E).ncard := Finset.mem_range.mp hj
        simp only [Prod.mk.injEq] at heq
        rcases lt_trichotomy i j with hlt | heqi | hgt
        · exact absurd heq.2.symm (cyclic_power_sigmaFan 0 V E hfan hdE j i hjn hlt)
        · exact heqi
        · exact absurd heq.2 (cyclic_power_sigmaFan 0 V E hfan hdE i j hin hgt)
      · intro y hy
        have hyn : y ∈ H.node d := (Set.Finite.mem_toFinset hfin).mp hy
        simp only [Hypermap.node, orbitMap, Set.mem_setOf_eq] at hyn
        obtain ⟨n, hn⟩ := hyn
        rw [Equiv.Perm.coe_pow] at hn
        rw [nodeMapTl_iterate hd n] at hn
        have hsoe : (sigmaFan 0 V E d.1)^[n] d.2 ∈ setOfEdge d.1 V E :=
          iterates_mem_setOfEdge hfan d.1 d.2
            ((properties_of_setOfEdge_fan 0 V E d.1 d.2 hfan).mp hdE) n
        obtain ⟨j, hj, hj_eq⟩ := iterates_mem_sigmaFan hfan hdE hsoe
        refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
        rw [hj_eq]
        exact hn
      · intro i hi
        rfl
    have step2 : (∑ i ∈ Finset.range (setOfEdge d.1 V E).ncard,
          azimDart V E (d.1, (sigmaFan 0 V E d.1)^[i] d.2))
        = (∑ i ∈ Finset.range (setOfEdge d.1 V E).ncard, azimIfan 0 V E d.1 d.2 i) :=
      Finset.sum_congr rfl (fun i hi =>
        azimDart_iterate_eq hfan hdE (by omega) i (Finset.mem_range.mp hi))
    calc setSum (H.node d) (fun y => azimDart V E y)
        = ∑ i ∈ Finset.range (setOfEdge d.1 V E).ncard,
            azimDart V E (d.1, (sigmaFan 0 V E d.1)^[i] d.2) := step1.symm
      _ = ∑ i ∈ Finset.range (setOfEdge d.1 V E).ncard, azimIfan 0 V E d.1 d.2 i := step2
      _ = 2 * Real.pi := sum_azims_eq_2pi hfan hdE hne_u

/-- node 轨道上 azim·lmfun 的和 = 2π·lmfun(hDart d)（HRXEFDM_lemma1 的
逐 node 核：node 轨道首分量恒定 + `node_sum_azim`）。 -/
private theorem node_sum_azim_lmfun (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    setSum ((hypermapOfFanTl V E hfan).node d)
        (fun y => azimDart V E y * lmfun (hDart_p2 y))
      = 2 * Real.pi * lmfun (hDart_p2 d) := by
  set H := hypermapOfFanTl V E hfan with hHdef
  have hfin : (H.node d).Finite := orbitMap_finite H.nodeMap_permutes d
  have hconst : ∀ y ∈ H.node d, lmfun (hDart_p2 y) = lmfun (hDart_p2 d) := by
    intro y hy
    rw [nodeTl_eq_image hfan hd] at hy
    obtain ⟨q, hq, hyq⟩ := hy
    have hy1 : y.1 = d.1 := by rw [← hyq]
    show lmfun (‖y.1‖ / 2) = lmfun (‖d.1‖ / 2)
    rw [hy1]
  calc setSum (H.node d) (fun y => azimDart V E y * lmfun (hDart_p2 y))
      = setSum (H.node d) (fun y => azimDart V E y * lmfun (hDart_p2 d)) := by
        rw [setSum, setSum, dif_pos hfin, dif_pos hfin]
        exact Finset.sum_congr rfl (fun y hy => by
          rw [hconst y ((Set.Finite.mem_toFinset hfin).mp hy)])
    _ = setSum (H.node d) (fun y => azimDart V E y) * lmfun (hDart_p2 d) := by
        rw [setSum, setSum, dif_pos hfin, dif_pos hfin, Finset.sum_mul]
    _ = 2 * Real.pi * lmfun (hDart_p2 d) := by rw [node_sum_azim hfan hd]

end NodeSum

/-! ### HRXEFDM_lemma1 与 CRTTXAT_lemma1 -/

/-- HOL `HRXEFDM_lemma1`（`tame/HRXEFDM.hl:109-199`）：face 集上
`azim_dart·lmfun(h_dart)` 的两层和 = `2π·scriptL V`。
偏差注记：HOL `hypermap_of_fan` 的 dart 集含孤立 `(v,v)`，Lean 折算取
`dart1OfFan`，孤立顶点由 `hns` 排除（contravening/fully_surrounded 消费者
处自由：card(setOfEdge) ≥ 3 / dart_of_fan = dart1）。 -/
theorem HRXEFDM_lemma1 (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (hns : ∀ v ∈ V, (setOfEdge v V E).Nonempty) :
    setSum (hypermapOfFanTl V E hfan).faceSet
        (fun o => setSum o (fun x => azimDart V E x * lmfun (hDart_p2 x)))
      = 2 * Real.pi * scriptL V := by
  classical
  set H := hypermapOfFanTl V E hfan with hHdef
  have hVfin : V.Finite := hfan.2.2.1.1
  have hex : ∀ v : V3, v ∈ V → ∃ w, (v, w) ∈ dart1OfFan V E := by
    intro v hv
    obtain ⟨w, hw⟩ := hns v hv
    exact ⟨w, (properties_of_setOfEdge_fan 0 V E v w hfan).mpr hw⟩
  set dd : V3 → V3 × V3 :=
    fun v => if h : v ∈ V then (v, Classical.choose (hex v h)) else (v, v) with hdddef
  have hdd : ∀ v : V3, v ∈ V → dd v ∈ dart1OfFan V E := by
    intro v hv
    simp only [hdddef, dif_pos hv]
    exact Classical.choose_spec (hex v hv)
  have hddfst : ∀ v : V3, v ∈ V → (dd v).1 = v := by
    intro v hv
    simp only [hdddef, dif_pos hv]
  have himg : H.nodeSet = (fun v : V3 => H.node (dd v)) '' V := by
    ext S
    constructor
    · intro hS
      obtain ⟨d, hd, rfl⟩ := hS.out
      have hvV : d.1 ∈ V := (FAN_in_setOfEdge 0 V E d.1 d.2 hfan (dartsTl_mem hd)).1
      refine ⟨d.1, hvV, ?_⟩
      show H.node (dd d.1) = H.node d
      rw [nodeTl_eq_image hfan (dartsTl_mem hd), nodeTl_eq_image hfan (hdd d.1 hvV),
        hddfst d.1 hvV]
    · rintro ⟨v, hv, rfl⟩
      exact ⟨dd v, mem_dartsTl (hdd v hv),
        (by rfl : orbitMap H.nodeMap (dd v) = (fun v : V3 => H.node (dd v)) v)⟩
  have hinj : Set.InjOn (fun v : V3 => H.node (dd v)) V := by
    intro v hv w hw heq
    simp only [] at heq
    have hmem0 : dd v ∈ H.node (dd v) := mem_orbitMap_self H.nodeMap (dd v)
    rw [nodeTl_eq_image hfan (hdd v hv)] at hmem0
    simp only [Set.mem_image, Set.mem_setOf_eq] at hmem0
    obtain ⟨q, hq, hprod⟩ := hmem0
    rw [hddfst v hv] at hq
    have hddv : dd v = (v, q) := by rw [hprod.symm, hddfst v hv]
    rw [hddv] at heq
    have hmq : (v, q) ∈ H.node (dd w) := by
      rw [← heq, nodeTl_eq_image hfan (by rw [← hddv]; exact hdd v hv)]
      exact ⟨q, hq, rfl⟩
    rw [nodeTl_eq_image hfan (hdd w hw)] at hmq
    simp only [Set.mem_image, Set.mem_setOf_eq] at hmq
    obtain ⟨q2, hq2, hprod2⟩ := hmq
    injection hprod2 with h5 h6
    exact h5.symm.trans (hddfst w hw)
  calc setSum H.faceSet (fun o => setSum o (fun x => azimDart V E x * lmfun (hDart_p2 x)))
      = setSum (↑H.darts : Set (V3 × V3)) (fun x => azimDart V E x * lmfun (hDart_p2 x)) :=
        setSum_setOfOrbits H.darts H.faceMap H.faceMap_permutes _
    _ = setSum H.nodeSet (fun o => setSum o (fun x => azimDart V E x * lmfun (hDart_p2 x))) :=
        (setSum_setOfOrbits H.darts H.nodeMap H.nodeMap_permutes _).symm
    _ = setSum ((fun v : V3 => H.node (dd v)) '' V)
          (fun o => setSum o (fun x => azimDart V E x * lmfun (hDart_p2 x))) := by rw [himg]
    _ = setSum V (fun v => setSum (H.node (dd v))
          (fun x => azimDart V E x * lmfun (hDart_p2 x))) :=
        setSum_image_injOn hVfin hinj _
    _ = setSum V (fun v => 2 * Real.pi * lmfun (hDart_p2 (dd v))) := by
        rw [setSum, setSum, dif_pos hVfin, dif_pos hVfin]
        exact Finset.sum_congr rfl (fun v hv => node_sum_azim_lmfun hfan
          (hdd v ((Set.Finite.mem_toFinset hVfin).mp hv)))
    _ = setSum V (fun v => 2 * Real.pi * lmfun (‖v‖ / 2)) := by
        rw [setSum, setSum, dif_pos hVfin, dif_pos hVfin]
        exact Finset.sum_congr rfl (fun v hv => by
          show 2 * Real.pi * lmfun (‖(dd v).1‖ / 2) = 2 * Real.pi * lmfun (‖v‖ / 2)
          rw [hddfst v ((Set.Finite.mem_toFinset hVfin).mp hv)])
    _ = 2 * Real.pi * setSum V (fun v => lmfun (‖v‖ / 2)) := by
        rw [setSum, setSum, dif_pos hVfin, dif_pos hVfin]
        exact (Finset.mul_sum _ _ _).symm
    _ = 2 * Real.pi * scriptL V := by rw [scriptL, dif_pos hVfin, setSum, dif_pos hVfin]


/-- HOL `CRTTXAT_lemma1`（`tame/CRTTXAT.hl:90-225`）：simple 超映射下
contravening 的 face 上 `lmfun∘h_dart` 的和 ≥ `12 + card f − card V`。
证明骨架同 HOL：face 像单射换元 → scriptL 按 `V \ (fst '' f)` 拆分 →
`lmfun ≤ 1`（ballAnnulus）+ 基数差 + `scriptL V > 12`。 -/
theorem CRTTXAT_lemma1 (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (hsimple : (hypermapOfFanTl V E hfan).Simple) (hc : Contravening V)
    {f : Set (V3 × V3)} (hf : f ∈ (hypermapOfFanTl V E hfan).faceSet)
    (hff : f.Finite) :
    12 + (f.ncard : ℝ) - (V.ncard : ℝ) ≤ setSum f (fun x => lmfun (hDart_p2 x)) := by
  classical
  have hVfin : V.Finite := hfan.2.2.1.1
  obtain ⟨x, hx, hfxeq⟩ := hf
  rw [← hfxeq]
  have hffe : ((hypermapOfFanTl V E hfan).face x).Finite := by
    have hsub := (hypermapOfFanTl V E hfan).face_subset_darts hx
    rw [dartsTl_coe] at hsub
    exact (finite_dart1_fan hfan).subset hsub
  have hsubd : ∀ y ∈ (hypermapOfFanTl V E hfan).face x, y ∈ dart1OfFan V E := by
    intro y hy
    have hmem := (hypermapOfFanTl V E hfan).face_subset_darts hx hy
    rw [dartsTl_coe] at hmem
    exact hmem
  have hsubA : (Prod.fst '' (hypermapOfFanTl V E hfan).face x) ⊆ V := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := hv
    exact (FAN_in_setOfEdge 0 V E y.1 y.2 hfan (hsubd y hy)).1
  have hAj : Set.InjOn (Prod.fst : V3 × V3 → V3) ((hypermapOfFanTl V E hfan).face x) :=
    face_fst_injOn hfan hsimple hx
  have hcardA : (Prod.fst '' (hypermapOfFanTl V E hfan).face x).ncard
      = ((hypermapOfFanTl V E hfan).face x).ncard := Set.InjOn.ncard_image hAj
  have hAfin : (Prod.fst '' (hypermapOfFanTl V E hfan).face x).Finite := hffe.image Prod.fst
  have hVAdiff : (V \ Prod.fst '' (hypermapOfFanTl V E hfan).face x).Finite := hVfin.sdiff
  have hfun0 : setSum ((hypermapOfFanTl V E hfan).face x) (fun y => lmfun (hDart_p2 y))
      = setSum ((hypermapOfFanTl V E hfan).face x) (fun y => lmfun (‖y.1‖ / 2)) := by
    rw [setSum, setSum, dif_pos hffe, dif_pos hffe]
    exact Finset.sum_congr rfl (fun y _ => rfl)
  have hkey : setSum ((hypermapOfFanTl V E hfan).face x) (fun y => lmfun (hDart_p2 y))
      = setSum (Prod.fst '' (hypermapOfFanTl V E hfan).face x)
          (fun v : V3 => lmfun (‖v‖ / 2)) := by
    rw [hfun0, setSum_image_injOn hffe hAj]
  have hscript : scriptL V = setSum V (fun v : V3 => lmfun (‖v‖ / 2)) := by
    rw [scriptL, dif_pos hVfin, setSum, dif_pos hVfin]
  have hA : Prod.fst '' (hypermapOfFanTl V E hfan).face x
        ∪ (V \ Prod.fst '' (hypermapOfFanTl V E hfan).face x) = V := by
    ext v
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (h | ⟨h1, -⟩)
      · exact hsubA h
      · exact h1
    · intro h
      rcases Classical.em (v ∈ Prod.fst '' (hypermapOfFanTl V E hfan).face x) with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h, h'⟩
  have hd : Disjoint (Prod.fst '' (hypermapOfFanTl V E hfan).face x)
      (V \ Prod.fst '' (hypermapOfFanTl V E hfan).face x) :=
    (disjoint_sdiff_self_left : Disjoint _ _).symm
  have hsplit : setSum V (fun v : V3 => lmfun (‖v‖ / 2))
      = setSum (Prod.fst '' (hypermapOfFanTl V E hfan).face x)
          (fun v : V3 => lmfun (‖v‖ / 2))
        + setSum (V \ Prod.fst '' (hypermapOfFanTl V E hfan).face x)
          (fun v : V3 => lmfun (‖v‖ / 2)) := by
    have hs : setSum ((Prod.fst '' (hypermapOfFanTl V E hfan).face x)
          ∪ (V \ Prod.fst '' (hypermapOfFanTl V E hfan).face x))
        (fun v : V3 => lmfun (‖v‖ / 2))
        = setSum (Prod.fst '' (hypermapOfFanTl V E hfan).face x)
            (fun v : V3 => lmfun (‖v‖ / 2))
          + setSum (V \ Prod.fst '' (hypermapOfFanTl V E hfan).face x)
            (fun v : V3 => lmfun (‖v‖ / 2)) :=
      setSum_union_disjoint hd hAfin hVAdiff
    rwa [hA] at hs
  have hbd : setSum (V \ Prod.fst '' (hypermapOfFanTl V E hfan).face x)
        (fun v : V3 => lmfun (‖v‖ / 2))
      ≤ ((V \ Prod.fst '' (hypermapOfFanTl V E hfan).face x).ncard : ℝ) * 1 := by
    refine setSum_le_of_le hVAdiff (fun v hv => ?_)
    have h2n := two_le_norm_of_mem_ballAnnulus (hc.2.1 ((Set.mem_sdiff v).mp hv).1)
    exact lmfun_le_one_of_one_le (by linarith)
  have hnc' : (((V \ Prod.fst '' (hypermapOfFanTl V E hfan).face x).ncard : ℝ)
        + ((Prod.fst '' (hypermapOfFanTl V E hfan).face x).ncard : ℝ))
      = ((V.ncard : ℝ)) := by
    rw [← Nat.cast_add, Set.ncard_sdiff_add_ncard_of_subset hsubA hVfin]
  have hgt : 12 < scriptL V := hc.2.2.1
  calc 12 + (((hypermapOfFanTl V E hfan).face x).ncard : ℝ) - (V.ncard : ℝ)
      = 12 + ((Prod.fst '' (hypermapOfFanTl V E hfan).face x).ncard : ℝ)
          - (V.ncard : ℝ) := by
        rw [hcardA]
    _ ≤ setSum (Prod.fst '' (hypermapOfFanTl V E hfan).face x)
          (fun v : V3 => lmfun (‖v‖ / 2)) := by
        have h1 : setSum (Prod.fst '' (hypermapOfFanTl V E hfan).face x)
              (fun v : V3 => lmfun (‖v‖ / 2))
            = scriptL V - setSum (V \ Prod.fst '' (hypermapOfFanTl V E hfan).face x)
              (fun v : V3 => lmfun (‖v‖ / 2)) := by
          rw [hscript, hsplit]
          ring
        rw [h1]
        have h2 := hbd
        linarith
    _ ≤ setSum ((hypermapOfFanTl V E hfan).face x) (fun x => lmfun (hDart_p2 x)) :=
      le_of_eq hkey.symm


/-! ## 7c. CRTTXAT 帽石装配（tame/CRTTXAT.hl:320-470） -/

/-- HOL `CRTTXAT`（`tame/CRTTXAT.hl:311-320`，assumption 形
`CRTTXAT_assum`：`(!V. contravening V ==> simple_hypermap …) ==> (!V.
contravening V /\ perimeterbound (V,ESTD V) ==> tame_9a …)`）。
DISCHARGES：已真证明（2026-10-12 第二波）：HOL :320-470 的 s1/s2/s3 链逐句
装配——`arcV_eq_arcLen`（件①）+ `arc_lemma1`（件②）+ `arc_lemma3`（件③，
凹性插值）+ `arc_lemma4`（件④）+ `estimate0`/`arc_lemma5_num`（件⑤）+
`CRTTXAT_lemma1`（第一波）+ `face_sum_snd_eq_fst`（FACE_SUM_lemma 的鸽笼路线，
绕开 SUM_ORBIT 轨道周期性）+ `Real.pi_lt_d4`；3≤card 半边走
`CARD_FACE_GE_3_TL` + `SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL`。 -/
theorem CRTTXAT
    (hsimple : ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)),
      Contravening V → (hypermapOfFanTl V (ESTD V) hfan).Simple)
    (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V))
    (hpb : PerimeterBound V (ESTD V) hfan) :
    Tame9a (hypermapOfFanTl V (ESTD V) hfan) := by
  classical
  set H := hypermapOfFanTl V (ESTD V) hfan with hHdef
  have hpack : Packing V := hc.1
  -- contravening 的范数/距离界
  have hnb : ∀ v ∈ V, 2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2.52 := by
    intro v hv
    have h2 := arc_two_le_norm_of_mem_ballAnnulus (hc.2.1 hv)
    refine ⟨h2, ?_⟩
    have hba : v ∈ ballAnnulus := hc.2.1 hv
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall] at hba
    have h52 : (2:ℝ) * h0 = 2.52 := by
      have h0126 : h0 = (1.26:ℝ) := rfl
      rw [h0126]; norm_num
    have hd0 : dist v 0 = ‖v‖ := by rw [dist_eq_norm, sub_zero]
    linarith [hba.1, h52, hd0]
  have hdb : ∀ d ∈ dart1OfFan V (ESTD V), 2 ≤ dist d.1 d.2 := by
    intro d hd
    have hvV : d.1 ∈ V := (FAN_in_setOfEdge 0 V (ESTD V) d.1 d.2 hfan hd).1
    have hwV : d.2 ∈ V := (FAN_in_setOfEdge 0 V (ESTD V) d.1 d.2 hfan hd).2.1
    exact Packing.dist_ge_two hpack hvV hwV (edge_ne_of_fan hfan hd)
  intro x hx
  have hxd : x ∈ dart1OfFan V (ESTD V) := dartsTl_mem hx
  refine ⟨CARD_FACE_GE_3_TL hfan hxd
    (fun v hv => SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hv
      (hc.2.2.2.2.2.1 v hv)), ?_⟩
  set f := H.face x with hfeq
  have hsubd : ∀ y ∈ f, y ∈ dart1OfFan V (ESTD V) := by
    intro y hy
    have hmem := H.face_subset_darts hx hy
    rwa [dartsTl_coe] at hmem
  have hffe : f.Finite := by
    have hsub := H.face_subset_darts hx
    rw [dartsTl_coe] at hsub
    exact (finite_dart1_fan hfan).subset hsub
  have hbd : ∀ d ∈ f, 2 ≤ ‖d.1‖ ∧ ‖d.1‖ ≤ 2.52 ∧ 2 ≤ ‖d.2‖ ∧ ‖d.2‖ ≤ 2.52
      ∧ 2 ≤ dist d.1 d.2 := by
    intro d hd
    have hvV : d.1 ∈ V := (FAN_in_setOfEdge 0 V (ESTD V) d.1 d.2 hfan (hsubd d hd)).1
    have hwV : d.2 ∈ V := (FAN_in_setOfEdge 0 V (ESTD V) d.1 d.2 hfan (hsubd d hd)).2.1
    exact ⟨(hnb d.1 hvV).1, (hnb d.1 hvV).2, (hnb d.2 hwV).1, (hnb d.2 hwV).2,
      hdb d (hsubd d hd)⟩
  have hfset : f ∈ H.faceSet := ⟨x, hx, rfl⟩
  have hper : setSum f (fun d => arcV 0 d.1 d.2) ≤ 2 * Real.pi := hpb f hfset
  -- CRTTXAT_lemma1（fst 权重版）+ 换元到 snd 权重版
  have hbase := CRTTXAT_lemma1 V (ESTD V) hfan (hsimple V hfan hc) hc hfset hffe
  have hswap := face_sum_snd_eq_fst hfan hx (fun v => lmfun (‖v‖ / 2))
  have hlm2 : 12 + (f.ncard : ℝ) - (V.ncard : ℝ)
      ≤ setSum f (fun d => lmfun (‖d.2‖ / 2)) := by
    rw [hswap]
    exact hbase
  -- 主链：s2 + s3 ≤ 2π
  have hstepA : setSum f (fun d => arcLen 2.52 ‖d.2‖ 2
        + lmfun (‖d.1‖ / 2) * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2))
      ≤ setSum f (fun d => arcLen ‖d.1‖ ‖d.2‖ 2) :=
    setSum_mono_pt hffe (fun d hd =>
      arc_lemma3 (hbd d hd).1 (hbd d hd).2.1 (hbd d hd).2.2.1 (hbd d hd).2.2.2.1)
  have hstepB : setSum f (fun d => arcLen ‖d.1‖ ‖d.2‖ 2)
      ≤ setSum f (fun d => arcLen ‖d.1‖ ‖d.2‖ (dist d.1 d.2)) :=
    setSum_mono_pt hffe (fun d hd =>
      arc_lemma1 (hbd d hd).1 (hbd d hd).2.2.1 (hbd d hd).2.2.2.2)
  have hstepC : setSum f (fun d => arcLen ‖d.1‖ ‖d.2‖ (dist d.1 d.2))
      = setSum f (fun d => arcV 0 d.1 d.2) := by
    rw [setSum, setSum, dif_pos hffe, dif_pos hffe]
    exact Finset.sum_congr rfl (fun d _ => (arcV_eq_arcLen d.1 d.2).symm)
  have hsplit : setSum f (fun d => arcLen 2.52 ‖d.2‖ 2)
        + setSum f (fun d => lmfun (‖d.1‖ / 2)
            * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2))
      = setSum f (fun d => arcLen 2.52 ‖d.2‖ 2
          + lmfun (‖d.1‖ / 2) * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2)) := by
    rw [setSum, setSum, setSum, dif_pos hffe, dif_pos hffe, dif_pos hffe]
    exact Finset.sum_add_distrib.symm
  have hchain : setSum f (fun d => arcLen 2.52 ‖d.2‖ 2
        + lmfun (‖d.1‖ / 2) * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2))
      ≤ 2 * Real.pi := by
    calc setSum f (fun d => arcLen 2.52 ‖d.2‖ 2
          + lmfun (‖d.1‖ / 2) * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2))
        ≤ setSum f (fun d => arcLen ‖d.1‖ ‖d.2‖ 2) := hstepA
      _ ≤ setSum f (fun d => arcLen ‖d.1‖ ‖d.2‖ (dist d.1 d.2)) := hstepB
      _ = setSum f (fun d => arcV 0 d.1 d.2) := hstepC
      _ ≤ 2 * Real.pi := hper
  -- s1 ≤ s2（arc_lemma3 在 x = ‖d.2‖ + arc_sym）
  have hs1s2 : setSum f (fun d => arcLen 2.52 2.52 2
        + lmfun (‖d.2‖ / 2) * (arcLen 2.52 2 2 - arcLen 2.52 2.52 2))
      ≤ setSum f (fun d => arcLen 2.52 ‖d.2‖ 2) := by
    refine setSum_mono_pt hffe (fun d hd => ?_)
    have hb := (hbd d hd).2.2.1
    have hb' := (hbd d hd).2.2.2.1
    have h3 := arc_lemma3 (x := ‖d.2‖) (b := 2.52) hb hb' (by norm_num) (by norm_num)
    rw [arcLen_sym ‖d.2‖ 2.52 2, arcLen_sym 2 2.52 2] at h3
    linarith
  -- s3 下界：lemma1 × arc_lemma4 逐点
  have hpt4 : ∀ d ∈ f, 0.073 ≤ arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2 := fun d hd =>
    arc_lemma4 (hbd d hd).2.2.1 (hbd d hd).2.2.2.1
  have hs3lo : (12 + (f.ncard : ℝ) - (V.ncard : ℝ)) * 0.073
      ≤ setSum f (fun d => lmfun (‖d.1‖ / 2)
          * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2)) := by
    have hstep1 : setSum f (fun d => lmfun (‖d.1‖ / 2)) * 0.073
        ≤ setSum f (fun d => lmfun (‖d.1‖ / 2)
            * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2)) := by
      rw [setSum, setSum, dif_pos hffe, dif_pos hffe, Finset.sum_mul]
      exact Finset.sum_le_sum (fun d hd =>
        mul_le_mul_of_nonneg_left (hpt4 d ((Set.Finite.mem_toFinset hffe).mp hd))
          (lmfun_nonneg _))
    calc (12 + (f.ncard : ℝ) - (V.ncard : ℝ)) * 0.073
        ≤ setSum f (fun d => lmfun (‖d.1‖ / 2)) * 0.073 :=
          mul_le_mul_of_nonneg_right hbase (by norm_num)
      _ ≤ setSum f (fun d => lmfun (‖d.1‖ / 2)
            * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2)) := hstep1
  -- s1 下界：k·arc + lemma1 × arc_lemma4(2.52)
  have hpt452 : 0.073 ≤ arcLen 2.52 2 2 - arcLen 2.52 2.52 2 := by
    have h := arc_lemma4 (x := (2.52:ℝ)) (by norm_num) (by norm_num)
    rwa [arcLen_sym 2 2.52 2] at h
  have hs1lo : (f.ncard : ℝ) * arcLen 2.52 2.52 2
        + (12 + (f.ncard : ℝ) - (V.ncard : ℝ)) * 0.073
      ≤ setSum f (fun d => arcLen 2.52 2.52 2
          + lmfun (‖d.2‖ / 2) * (arcLen 2.52 2 2 - arcLen 2.52 2.52 2)) := by
    have hsplit1 : setSum f (fun d => arcLen 2.52 2.52 2
          + lmfun (‖d.2‖ / 2) * (arcLen 2.52 2 2 - arcLen 2.52 2.52 2))
        = setSum f (fun _ : V3 × V3 => arcLen 2.52 2.52 2)
          + setSum f (fun d => lmfun (‖d.2‖ / 2)
              * (arcLen 2.52 2 2 - arcLen 2.52 2.52 2)) := by
      rw [setSum, setSum, setSum, dif_pos hffe, dif_pos hffe, dif_pos hffe]
      exact Finset.sum_add_distrib
    have hcard'' : ((hffe.toFinset.card : ℕ) : ℝ) = (f.ncard : ℝ) := by
      congr 1
      rw [Set.ncard_eq_toFinset_card f hffe]
    have hconstsum : setSum f (fun _ : V3 × V3 => arcLen 2.52 2.52 2)
        = (f.ncard : ℝ) * arcLen 2.52 2.52 2 := by
      rw [setSum, dif_pos hffe, Finset.sum_const, nsmul_eq_mul, hcard'']
    have hsplit2 : setSum f (fun d => lmfun (‖d.2‖ / 2)
            * (arcLen 2.52 2 2 - arcLen 2.52 2.52 2))
        = setSum f (fun d => lmfun (‖d.2‖ / 2))
            * (arcLen 2.52 2 2 - arcLen 2.52 2.52 2) := by
      rw [setSum, setSum, dif_pos hffe, dif_pos hffe, Finset.sum_mul]
    have hlmw : (12 + (f.ncard : ℝ) - (V.ncard : ℝ)) * 0.073
        ≤ setSum f (fun d => lmfun (‖d.2‖ / 2)) * 0.073 :=
      mul_le_mul_of_nonneg_right hlm2 (by norm_num)
    have hw0 : 0 ≤ setSum f (fun d => lmfun (‖d.2‖ / 2)) := by
      rw [setSum, dif_pos hffe]
      exact Finset.sum_nonneg (fun d _ => lmfun_nonneg _)
    have hstep2 : setSum f (fun d => lmfun (‖d.2‖ / 2)) * 0.073
        ≤ setSum f (fun d => lmfun (‖d.2‖ / 2))
            * (arcLen 2.52 2 2 - arcLen 2.52 2.52 2) :=
      mul_le_mul_of_nonneg_left hpt452 hw0
    rw [hsplit1, hconstsum, hsplit2]
    linarith [hlmw, hstep2]
  -- 合并：k·(arc + 0.146) ≤ 2π + (cardV − 12)·0.146
  have hfinal : (f.ncard : ℝ) * (arcLen 2.52 2.52 2 + 0.146)
      ≤ 2 * Real.pi + ((V.ncard : ℝ) - 12) * 0.146 := by
    have hboth : setSum f (fun d => arcLen 2.52 2.52 2
          + lmfun (‖d.2‖ / 2) * (arcLen 2.52 2 2 - arcLen 2.52 2.52 2))
        + setSum f (fun d => lmfun (‖d.1‖ / 2)
            * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2)) ≤ 2 * Real.pi := by
      calc setSum f (fun d => arcLen 2.52 2.52 2
              + lmfun (‖d.2‖ / 2) * (arcLen 2.52 2 2 - arcLen 2.52 2.52 2))
            + setSum f (fun d => lmfun (‖d.1‖ / 2)
                * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2))
          ≤ setSum f (fun d => arcLen 2.52 ‖d.2‖ 2)
              + setSum f (fun d => lmfun (‖d.1‖ / 2)
                  * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2)) :=
            by linarith [hs1s2]
        _ = setSum f (fun d => arcLen 2.52 ‖d.2‖ 2
              + lmfun (‖d.1‖ / 2) * (arcLen 2 ‖d.2‖ 2 - arcLen 2.52 ‖d.2‖ 2)) :=
            hsplit
        _ ≤ 2 * Real.pi := hchain
    linarith [hs1lo, hs3lo, hboth]
  -- 数值收口：arc ≥ 0.816，cardV ≤ 15，2π ≤ 6.2832 ⟹ k < 7
  have hcardV : (V.ncard : ℝ) ≤ 15 := by
    rcases hc.2.2.2.2.1 with h13 | h14 | h15
    · rw [h13]; norm_num
    · rw [h14]; norm_num
    · rw [h15]; norm_num
  have hpi : 2 * Real.pi ≤ 6.2832 := by linarith [Real.pi_lt_d4]
  have hkarc : (f.ncard : ℝ) * 0.816 ≤ (f.ncard : ℝ) * arcLen 2.52 2.52 2 :=
    mul_le_mul_of_nonneg_left arc_lemma5_num (Nat.cast_nonneg _)
  have hk : (f.ncard : ℝ) < 7 := by linarith [hfinal, hkarc, hpi, hcardV]
  exact Nat.le_of_lt_succ (Nat.cast_lt.mp hk)


/-! ## 8. 债务图锚点备忘

`Kepler/Assembly.lean` 消费对应：
- §2c `mqmsmab`（Assembly.lean:449-452）的填实直接消费本文件：
  `contravening_lp_fan`（:33）、`COMPONENTS_HYPERMAP_OF_FAN`（:35）、
  `CRTTXAT`+`JGTDEBU4`+`fully_surrounded_perimeter_bound`（:36）、
  `tame_9a`+`JGTDEBU10/11`+`SZIPOAS`+`BDJYFFB1`（:37-38）、
  `tame_1..tame_8`+`JGTDEBU1..8`（:39-44）、
  `sum_tauVEF_upper_bound`（:50）、`ineq_tau3/4/5/6_tauVEF_std`（:59-66）、
  `KCBLRQC`（:70）、`BDJYFFB2`（:73）。
- §2d `lpArchiveCertificates`（Assembly.lean:536-539）的逐图证书桥依赖
  CRTTXAT/KCBLRQC 群（Assembly §2d 注记）。

关键路径（填实优先级建议；★ = 本文件已真证明，0 error）：
1. ★ `JGTDEBU2/5/6/7`（dart 层展开，§2b/§2c 支撑件）。
2. ★ `JGTDEBU4/1/3`（Conforming 章 twin SRPRNPL/GGRLKHP/WGVWSKE +
   `contraveningConformingTl`——SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3 经
   `sum_azims_eq_2pi` 落地；§0b/§0c 处理 dartDecEq2/instProd 重标）。
3. ★ `JGTDEBU8/10/11`（SIMPLE_HYPERMAP 计数 + NODE_SET_AS_IMAGE +
   SURROUNDED_IMP_CARD_NODE_GE_3_TL）；★ `NODE_TYPE_lemma`（faceInjOn_of_node
   计数核，CDTETAT/KCBLRQC/BDJYFFB1 共用）。
4. ★ `COMPONENTS_HYPERMAP_OF_FAN`（构造性证明）。
5. 剩余债务：`fully_surrounded_perimeter_bound` 等深章件（`contravening_fanTl` 已于 T3 波经 ContraFan.lean 真化，`contravening_lp_fan`
   仅欠此一步，其余由 `contravening_lp_fan_of_fan` 真证明）→ `CDTETAT`
   （21 情形算术 + kcblrqc_ineq_def 两条 azim 边界）→ `SZIPOAS` →
   `KCBLRQC`/`BDJYFFB1/2`（b_tame 表逐情形算术）。
6. ★ `CRTTXAT`（2026-10-12 第二波已真证明：arc kit 五件套自证（§7，
   `arcV_eq_arcLen`/`arc_lemma1`/`arc_lemma3`/`arc_lemma4`/`estimate0`+
   `arc_lemma5_num`）+ `face_sum_snd_eq_fst`（FACE_SUM_lemma 的鸽笼路线，
   绕开 SUM_ORBIT 轨道周期性=WRGCVDR 内容）+ `CRTTXAT_lemma1`（§7b）+
   `Real.pi_lt_d4`；3≤card 半边 = `CARD_FACE_GE_3_TL` +
   `SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL`）。
7. `fully_surrounded_perimeter_bound`、`sum_tauVEF_upper_bound`、
   `ineq_tauK_tauVEF_std`（各依赖 Polar_fan / HRXEFDM / FaceK 分支不等式，
   属 formal_lp 侧子工程）。
-/

/-! ## 9. S1 keystone：hypermapOfList 构造（list_hypermap-compiled.hl:152-517）

通用 α 层（getD/idxOf/nextEl/prevEl）+ findFaceDarts/fList/nList 层 +
`hypermapOfList` 构造 + `IsHypermapOfListTl` 规格桥（Assembly §1b
`IsHypermapOfList` 的逐字段同体结构；装配 lane 以四字段一步折算）。
状态：全部真证明（`prevEl_nextEl` / `nextEl_prevEl` 经 `li_*` idxOf 双实例
congruence 家族闭合，2026-09-29）。
-/

section S1HypermapOfList
open Kepler.Assembly (listPairs listOfDarts findFaceDarts eList fList nList nextEl prevEl GoodList)
open Kepler.Graphs (fgraph)

theorem listPairs_nil_iff : listPairs ([] : List ℕ) = [] := by
  simp [listPairs]

theorem findFaceDarts_none {L : fgraph ℕ} {z : ℕ × ℕ}
    (hn : L.find? (fun l => decide (z ∈ listPairs l)) = none) :
    findFaceDarts L z = [] := by
  unfold findFaceDarts
  rw [hn]
  simp [listPairs_nil_iff]

theorem findFaceDarts_some {L : fgraph ℕ} {z : ℕ × ℕ} {l' : List ℕ}
    (hs : L.find? (fun l => decide (z ∈ listPairs l)) = some l') :
    findFaceDarts L z = listPairs l' ∧ z ∈ listPairs l' ∧ l' ∈ L := by
  refine ⟨?_, ?_, List.mem_of_find?_eq_some hs⟩
  · unfold findFaceDarts
    rw [hs]
    simp
  · have h2 := List.find?_some hs
    simpa using h2

/-! ### getD / idxOf 层（generic α：prevEl 的 def-body 由 [DecidableEq α]
    导出 BEq，与 ℕ×ℕ 的 instBEqProd 是不同实例——通用化后 synth 唯一，
    unfold/rw 全部一致） -/

section GenericList
variable {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]

theorem getD_eq_getElem_of_lt {s : List α} {j : ℕ} (hj : j < s.length) (d : α) :
    s.getD j d = s[j]'hj := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  simp

theorem headD_eq_getD_zero (s : List α) (d : α) :
    s.headD d = s.getD 0 d := by
  cases s with
  | nil => rfl
  | cons a t => rfl

theorem getD_next {s : List α} {j : ℕ} (hj1 : j + 1 < s.length) (d : α) :
    s.getD ((j + 1) % s.length) d = s.getD (j + 1) d := by
  rw [Nat.mod_eq_of_lt hj1]

theorem getD_prev {s : List α} {j : ℕ} (hj : j < s.length) (hj0 : j ≠ 0)
    (d : α) : s.getD ((j + s.length - 1) % s.length) d = s.getD (j - 1) d := by
  have h2 : j + s.length - 1 = (j - 1) + s.length := by omega
  have hjm1 : j - 1 < s.length := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hjm1]

theorem getD_wrap_next {s : List α} (hpos : 0 < s.length) (d : α) :
    s.getD ((s.length - 1 + 1) % s.length) d = s.getD 0 d := by
  have h0 : (s.length - 1 + 1) % s.length = 0 := by
    have e : s.length - 1 + 1 = s.length := by omega
    rw [e, Nat.mod_self]
  rw [h0]

theorem getD_wrap_prev {s : List α} (hpos : 0 < s.length) (d : α) :
    s.getD ((0 + s.length - 1) % s.length) d = s.getD (s.length - 1) d := by
  have h0 : (0 + s.length - 1) % s.length = s.length - 1 := by
    rw [Nat.zero_add, Nat.mod_eq_of_lt (show s.length - 1 < s.length from by omega)]
  rw [h0]

theorem getElem_idxOf {s : List α} {x : α} (hx : x ∈ s) :
    s[s.idxOf x]'(List.idxOf_lt_length_iff.mpr hx) = x := by
  induction s with
  | nil => simp at hx
  | cons a t ih =>
    by_cases hxa : x = a
    · subst hxa
      simp only [List.idxOf_cons_self]
      rfl
    · have hmem : x ∈ t := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h hxa
        · exact h
      have hne : a ≠ x := fun h => hxa h.symm
      simp only [List.idxOf_cons_ne t hne, List.getElem_cons_succ]
      exact ih hmem

theorem idxOf_getElem {s : List α} (hn : s.Nodup) {i : ℕ} (hi : i < s.length) :
    s.idxOf s[i] = i := by
  induction s generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      exact List.idxOf_cons_self
    | succ j =>
      have hlen : (a :: t).length = t.length + 1 := List.length_cons
      have hj : j < t.length := by omega
      have hmem : t[j] ∈ t := List.getElem_mem hj
      have hne : a ≠ t[j] := fun h => (List.nodup_cons.mp hn).1 (h ▸ hmem)
      simp only [List.getElem_cons_succ, List.idxOf_cons_ne t hne]
      exact congrArg Nat.succ (ih (List.nodup_cons.mp hn).2 hj)

theorem nodup_getElem_inj {s : List α} (hn : s.Nodup) {i j : ℕ}
    (hi : i < s.length) (hj : j < s.length) (h : s[i] = s[j]) : i = j := by
  have e1 : s.idxOf s[j] = i := by rw [← h]; exact idxOf_getElem hn hi
  have e2 := idxOf_getElem hn hj
  exact e1.symm.trans e2

/-! ### nextEl / prevEl 层 -/

theorem nextEl_eq_getD {s : List α} {x : α} (hx : x ∈ s) :
    nextEl s x = s.getD ((s.idxOf x + 1) % s.length) x := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  have hlt : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  unfold nextEl
  by_cases he : s.idxOf x = s.length - 1
  · have hz : (s.idxOf x + 1) % s.length = (s.length - 1 + 1) % s.length := by
      rw [he]
    rw [if_pos he, hz, getD_wrap_next hpos, headD_eq_getD_zero]
  · have hj1 : s.idxOf x + 1 < s.length := by omega
    rw [if_neg he, getD_next hj1]

theorem nextEl_mem_of_mem {s : List α} {x : α} (hx : x ∈ s) :
    nextEl s x ∈ s := by
  rw [nextEl_eq_getD hx]
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  rw [getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
  exact List.getElem_mem (Nat.mod_lt _ hpos)

theorem getD_mem {s : List α} {j : ℕ} (d : α) : s.getD j d ∈ s ∨ s.getD j d = d := by
  by_cases hj : j < s.length
  · left
    rw [getD_eq_getElem_of_lt hj]
    exact List.getElem_mem hj
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

theorem getLastD_eq_getElem_last {s : List α} (hpos : 0 < s.length) (d : α) :
    s.getLastD d = s[s.length - 1]'(by omega) := by
  induction s with
  | nil => simp at hpos
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b u =>
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem
          (show (a :: b :: u).length - 1 < (a :: b :: u).length from by omega)]
      simp

/-- prevEl 的 def-body 内部 BEq（由 [DecidableEq α] 导出；与 nextEl 的
外部 [BEq α]（ℕ×ℕ 处为 instBEqProd）不同实例）。 -/
theorem lawful_beqPrev : @LawfulBEq α (instBEqOfDecidableEq (α := α)) := by
  infer_instance

/-- 内部世界的 idxOf 事实：`s[内部 idxOf y] = y`（y ∈ s）。 -/
theorem getElem_idxOf_internal {s : List α} {y : α} (hy : y ∈ s) :
    s[@List.idxOf α (instBEqOfDecidableEq (α := α)) y s]'(
      @List.idxOf_lt_length_iff α (instBEqOfDecidableEq (α := α)) lawful_beqPrev s y |>.mpr hy) = y :=
  @getElem_idxOf α (instBEqOfDecidableEq (α := α)) lawful_beqPrev
    (inferInstanceAs (DecidableEq α)) s y hy

theorem prevEl_mem_of_mem {s : List α} {x : α} (hx : x ∈ s) : prevEl s x ∈ s := by
  unfold prevEl
  split
  · exact hx
  split
  · rename_i h0
    have hmem : s.getD (s.length - 1) x ∈ s ∨ s.getD (s.length - 1) x = x :=
      getD_mem (j := s.length - 1) (d := x)
    rw [List.getD_eq_getElem?_getD] at hmem
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    rcases hmem with hmem | heq
    · exact hmem
    · rw [heq]
      exact hx
  · rename_i h0
    rcases getD_mem
      (j := @List.idxOf α (instBEqOfDecidableEq (α := α)) x s - 1) (d := x) with hmem | heq
    · exact hmem
    · rw [heq]
      exact hx

/-! ### li_*：idxOf 的 BEq-实例无关 congruence（双世界桥）

`prevEl` 的 def-body（GoodListDefs，仅 `[DecidableEq α]`）内部 `idxOf` 用
`instBEqOfDecidableEq`，而外部世界 `[BEq α]`（ℕ×ℕ 处合成 `instBEqProd`）是
不同实例——两枚 `idxOf` 唯一性桥（`prevEl_nextEl` / `nextEl_prevEl`）由此卡住。
`li_*` 家族一次性搬运：idxOf 对 LawfulBEq 实例不敏感（S2/S5 列表机器可直接复用）。 -/

/-- `List.idxOf` 对 LawfulBEq 实例不敏感：同一列表同一元，两个 LawfulBEq
实例给出的下标逐点一致。 -/
theorem li_idxOf_of_lawful {α : Type*} {e f : BEq α}
    (he : @LawfulBEq α e) (hf : @LawfulBEq α f) (s : List α) (x : α) :
    @List.idxOf α e x s = @List.idxOf α f x s := by
  induction s generalizing x with
  | nil => rfl
  | cons b t ih =>
    rw [@List.idxOf_cons α b t x e, @List.idxOf_cons α b t x f]
    by_cases h : b = x
    · subst h
      have e1 : @BEq.beq α e b b = true := @beq_self_eq_true α e he.toReflBEq b
      have f1 : @BEq.beq α f b b = true := @beq_self_eq_true α f hf.toReflBEq b
      rw [e1, f1, ih]
    · have h1 : @BEq.beq α e b x = false := by
        cases hb : @BEq.beq α e b x with
        | false => rfl
        | true => exact absurd ((@beq_iff_eq α e he).mp hb) h
      have h2 : @BEq.beq α f b x = false := by
        cases hb : @BEq.beq α f b x with
        | false => rfl
        | true => exact absurd ((@beq_iff_eq α f hf).mp hb) h
      rw [h1, h2, ih]

/-- 双世界 idxOf 桥：`prevEl` def-body 内部（`instBEqOfDecidableEq`）与外部
（`[BEq α]`，ℕ×ℕ 处 `instBEqProd`）的 `idxOf` 逐点一致。 -/
theorem li_idxOf_congr (s : List α) (x : α) :
    @List.idxOf α (instBEqOfDecidableEq (α := α)) x s = List.idxOf x s :=
  li_idxOf_of_lawful (by infer_instance) (by infer_instance) s x

/-- 越界默认元无关：下标在界内时 `getD` 与默认元取值无关（getD 无证明分量，
可安全被 `rw` 抽象）。 -/
theorem li_getD_congr_default {s : List α} {j : ℕ} (hj : j < s.length) {d d' : α} :
    s.getD j d = s.getD j d' := by
  rw [getD_eq_getElem_of_lt hj, getD_eq_getElem_of_lt hj]

/-- `getLastD` 的 getD 形（沿用 `getLastD_eq_getElem_last`，但无 getElem
证明分量）。 -/
theorem li_getLastD_getD {s : List α} (hpos : 0 < s.length) (d : α) :
    s.getLastD d = s.getD (s.length - 1) d := by
  rw [getLastD_eq_getElem_last hpos,
    getD_eq_getElem_of_lt (show s.length - 1 < s.length from by omega)]

theorem prevEl_nextEl {s : List α} (hn : s.Nodup) {x : α} (hx : x ∈ s) :
    prevEl s (nextEl s x) = x := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  have hilt : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hmem : nextEl s x ∈ s := nextEl_mem_of_mem hx
  have hx1 : s.getD (s.idxOf x) x = x := by
    rw [getD_eq_getElem_of_lt hilt]
    exact getElem_idxOf hx
  have hnext_idx : s.idxOf (nextEl s x) = (s.idxOf x + 1) % s.length := by
    rw [nextEl_eq_getD hx, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
    exact idxOf_getElem hn (Nat.mod_lt _ hpos)
  unfold prevEl
  rw [if_neg (show ¬(nextEl s x ∉ s) from by simp [hmem]), li_idxOf_congr, hnext_idx]
  split
  · rename_i hmod
    have hi1 : s.idxOf x + 1 ≤ s.length := by omega
    have hlen : s.idxOf x = s.length - 1 := by
      rcases Nat.eq_or_lt_of_le hi1 with he | hlt
      · omega
      · rw [Nat.mod_eq_of_lt hlt] at hmod; omega
    rw [li_getLastD_getD hpos, ← hlen]
    exact (li_getD_congr_default hilt).trans hx1
  · rename_i hmodne
    have hi1 : s.idxOf x + 1 ≤ s.length := by omega
    have hlt : s.idxOf x + 1 < s.length := by
      rcases Nat.eq_or_lt_of_le hi1 with he | hlt2
      · rw [he, Nat.mod_self] at hmodne; exact absurd rfl hmodne
      · exact hlt2
    have hmod : (s.idxOf x + 1) % s.length = s.idxOf x + 1 := Nat.mod_eq_of_lt hlt
    have him1 : s.idxOf x + 1 - 1 = s.idxOf x := by omega
    rw [hmod, him1]
    exact (li_getD_congr_default hilt).trans hx1

theorem nextEl_prevEl {s : List α} (hn : s.Nodup) {x : α} (hx : x ∈ s) :
    nextEl s (prevEl s x) = x := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  have hilt : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hmem : prevEl s x ∈ s := prevEl_mem_of_mem hx
  have hx1 : s.getD (s.idxOf x) x = x := by
    rw [getD_eq_getElem_of_lt hilt]
    exact getElem_idxOf hx
  have hy_getD : prevEl s x = s.getD ((s.idxOf x + s.length - 1) % s.length) x := by
    unfold prevEl
    rw [if_neg (show ¬(x ∉ s) from by simp [hx]), li_idxOf_congr]
    split
    · rename_i h0
      rw [h0, getD_wrap_prev hpos]
      exact li_getLastD_getD hpos x
    · rename_i hne
      exact (getD_prev hilt hne x).symm
  have hy_idx : s.idxOf (prevEl s x) = (s.idxOf x + s.length - 1) % s.length := by
    rw [hy_getD, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
    exact idxOf_getElem hn (Nat.mod_lt _ hpos)
  rw [nextEl_eq_getD hmem, hy_idx]
  rcases Nat.eq_zero_or_pos (s.idxOf x) with h0 | hne0
  · have hm : (0 + s.length - 1) % s.length = s.length - 1 := by
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [h0, hm, getD_wrap_next hpos]
    calc s.getD 0 (prevEl s x) = s.getD 0 x := li_getD_congr_default hpos
      _ = x := by rw [h0] at hx1; exact hx1
  · have hk : (s.idxOf x + s.length - 1) % s.length = s.idxOf x - 1 := by
      have e : s.idxOf x + s.length - 1 = (s.idxOf x - 1) + s.length := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (show s.idxOf x - 1 < s.length from by omega)]
    have hidx1 : s.idxOf x - 1 + 1 = s.idxOf x := by omega
    rw [hk, hidx1, Nat.mod_eq_of_lt hilt]
    exact (li_getD_congr_default hilt).trans hx1

/-! ### flatten 层 -/

theorem flatten_nodup_inj {β : Type*} [DecidableEq β] {S : List (List β)}
    (hn : S.flatten.Nodup) {s₁ s₂ : List β} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S)
    {d : β} (hd₁ : d ∈ s₁) (hd₂ : d ∈ s₂) : s₁ = s₂ := by
  induction S with
  | nil => cases h₁
  | cons s t ih =>
    rw [List.flatten_cons, List.nodup_append] at hn
    simp only [List.mem_cons] at h₁ h₂
    rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
    · rfl
    · exact absurd rfl (hn.2.2 d hd₁ d (List.mem_flatten.mpr ⟨s₂, h₂, hd₂⟩))
    · exact absurd rfl (hn.2.2 d hd₂ d (List.mem_flatten.mpr ⟨s₁, h₁, hd₁⟩))
    · exact ih hn.2.1 h₁ h₂

theorem flatten_nodup_mem {β : Type*} [DecidableEq β] {S : List (List β)}
    (hn : S.flatten.Nodup) {s : List β} (hs : s ∈ S) : s.Nodup := by
  induction S with
  | nil => cases hs
  | cons s t ih =>
    rw [List.flatten_cons, List.nodup_append] at hn
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hn.1
    · exact ih hn.2.1 hs

end GenericList

/-! ### findFaceDarts 层 -/

theorem dart_in_face (L : fgraph ℕ) (d : ℕ × ℕ) :
    d ∈ findFaceDarts L d ↔ d ∈ listOfDarts L := by
  unfold listOfDarts
  by_cases hval : L.find? (fun l => decide (d ∈ listPairs l)) = none
  · rw [findFaceDarts_none hval]
    constructor
    · intro hm
      exact absurd hm (by simp)
    · intro hm
      obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hm
      rw [List.mem_map] at hl
      obtain ⟨l', hl', hdl'⟩ := hl
      exact absurd (by rw [hdl']; simpa using hdl) (List.find?_eq_none.mp hval l' hl')
  · obtain ⟨l', hl''⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : L.find? (fun l => decide (d ∈ listPairs l)) = some l' := hl''.symm
    obtain ⟨heq, hdl', hl'mem⟩ := findFaceDarts_some hfeq
    rw [heq]
    constructor
    · intro hm
      exact List.mem_flatten.mpr ⟨listPairs l', List.mem_map.mpr ⟨l', hl'mem, rfl⟩, hm⟩
    · intro _
      exact hdl'

theorem mem_darts_of_mem_findFace (L : fgraph ℕ) {y d : ℕ × ℕ}
    (h : y ∈ findFaceDarts L d) : y ∈ listOfDarts L := by
  by_cases hval : L.find? (fun l => decide (d ∈ listPairs l)) = none
  · rw [findFaceDarts_none hval] at h
    simp at h
  · obtain ⟨l', hl''⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : L.find? (fun l => decide (d ∈ listPairs l)) = some l' := hl''.symm
    obtain ⟨heq, _, hl'mem⟩ := findFaceDarts_some hfeq
    rw [heq] at h
    exact List.mem_flatten.mpr ⟨listPairs l',
      List.mem_map.mpr ⟨l', hl'mem, rfl⟩, h⟩

/-- 自我定位：`z ∈ findFaceDarts L z` 给出 face 列表见证。 -/
theorem findFaceDarts_ex_of_self {L : fgraph ℕ} {z : ℕ × ℕ} (hz : z ∈ findFaceDarts L z) :
    ∃ l : List ℕ, l ∈ L ∧ findFaceDarts L z = listPairs l ∧ z ∈ listPairs l := by
  by_cases hval : L.find? (fun l => decide (z ∈ listPairs l)) = none
  · rw [findFaceDarts_none hval] at hz
    simp at hz
  · obtain ⟨l', hl''⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : L.find? (fun l => decide (z ∈ listPairs l)) = some l' := hl''.symm
    obtain ⟨heq, hzl', hl'mem⟩ := findFaceDarts_some hfeq
    exact ⟨l', hl'mem, heq, hzl'⟩

theorem findFaceDarts_eq_of_mem {L : fgraph ℕ} (hn : (listOfDarts L).Nodup)
    {l : List ℕ} (hl : l ∈ L) {d : ℕ × ℕ} (hd : d ∈ listPairs l) :
    findFaceDarts L d = listPairs l := by
  have hflat : ((L.map listPairs).flatten).Nodup := hn
  by_cases hval : L.find? (fun l => decide (d ∈ listPairs l)) = none
  · rw [List.find?_eq_none] at hval
    have hnc := hval l hl
    simp at hnc
    exact absurd hd hnc
  · obtain ⟨l', hl''⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : L.find? (fun l => decide (d ∈ listPairs l)) = some l' := hl''.symm
    obtain ⟨heq, hdl', hl'mem⟩ := findFaceDarts_some hfeq
    rw [heq]
    exact flatten_nodup_inj hflat (List.mem_map.mpr ⟨l', hl'mem, rfl⟩)
      (List.mem_map.mpr ⟨l, hl, rfl⟩) hdl' hd

/-- face 列表相容：同处一面的两个 dart 有相同 face。 -/
theorem findFaceDarts_congr_of_mem {L : fgraph ℕ} (hn : (listOfDarts L).Nodup)
    {z d : ℕ × ℕ} (hd : d ∈ listOfDarts L) (hz : z ∈ findFaceDarts L d) :
    findFaceDarts L z = findFaceDarts L d := by
  have hz' : z ∈ findFaceDarts L z := dart_in_face L z |>.mpr
    (mem_darts_of_mem_findFace L hz)
  have hd' : d ∈ findFaceDarts L d := dart_in_face L d |>.mpr hd
  obtain ⟨l1, hl1, e1, hd1⟩ := findFaceDarts_ex_of_self hz'
  obtain ⟨l0, hl0, e0, _⟩ := findFaceDarts_ex_of_self hd'
  have hz0 : z ∈ listPairs l0 := by rw [← e0]; exact hz
  have hpl : listPairs l1 = listPairs l0 :=
    flatten_nodup_inj hn (List.mem_map.mpr ⟨l1, hl1, rfl⟩) (List.mem_map.mpr ⟨l0, hl0, rfl⟩)
      hd1 hz0
  rw [e1, hpl, ← e0]

theorem findFaceDarts_nodup {L : fgraph ℕ} (hn : (listOfDarts L).Nodup) (d : ℕ × ℕ) :
    (findFaceDarts L d).Nodup := by
  by_cases hval : L.find? (fun l => decide (d ∈ listPairs l)) = none
  · rw [findFaceDarts_none hval]
    simp
  · obtain ⟨l', hl''⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : L.find? (fun l => decide (d ∈ listPairs l)) = some l' := hl''.symm
    have h1 := (findFaceDarts_some hfeq).1
    rw [h1]
    exact flatten_nodup_mem hn (List.mem_map.mpr ⟨l', List.mem_of_find?_eq_some hfeq, rfl⟩)

/-! ### fList / nList / eList 侧 -/

theorem findFace_fList {L : fgraph ℕ} (hn : (listOfDarts L).Nodup) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : findFaceDarts L (fList L d) = findFaceDarts L d :=
  findFaceDarts_congr_of_mem hn hd (nextEl_mem_of_mem (dart_in_face L d |>.mpr hd))

theorem fList_mem_darts {L : fgraph ℕ} (hn : (listOfDarts L).Nodup) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : fList L d ∈ listOfDarts L :=
  mem_darts_of_mem_findFace L (nextEl_mem_of_mem (dart_in_face L d |>.mpr hd))

theorem fList_prev_inverse {L : fgraph ℕ} (hn : (listOfDarts L).Nodup) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : fList L (prevEl (findFaceDarts L d) d) = d := by
  have hdn : d ∈ findFaceDarts L d := dart_in_face L d |>.mpr hd
  show nextEl (findFaceDarts L (prevEl (findFaceDarts L d) d))
      (prevEl (findFaceDarts L d) d) = d
  rw [show findFaceDarts L (prevEl (findFaceDarts L d) d) = findFaceDarts L d from
    findFaceDarts_congr_of_mem hn hd (prevEl_mem_of_mem hdn)]
  have hnod : (findFaceDarts L d).Nodup := findFaceDarts_nodup hn d
  exact nextEl_prevEl hnod hdn

theorem prev_fList_inverse {L : fgraph ℕ} (hn : (listOfDarts L).Nodup) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    prevEl (findFaceDarts L (fList L d)) (fList L d) = d := by
  rw [findFace_fList hn hd]
  show prevEl (findFaceDarts L d) (nextEl (findFaceDarts L d) d) = d
  exact prevEl_nextEl (findFaceDarts_nodup hn d) (dart_in_face L d |>.mpr hd)

theorem eList_inj {a b : ℕ × ℕ} (h : eList a = eList b) : a = b := by
  have h1 : a.2 = b.2 := congrArg Prod.fst h
  have h2 : a.1 = b.1 := congrArg Prod.snd h
  exact Prod.ext h2 h1

theorem bijOn_eList {L : fgraph ℕ} (hL : GoodList L) :
    Set.BijOn eList {d | d ∈ listOfDarts L} {d | d ∈ listOfDarts L} :=
  ⟨fun d hd => hL.2.2 d hd, fun a _ b _ heq => eList_inj heq,
    fun y hy => ⟨eList y, hL.2.2 y hy, rfl⟩⟩

theorem nList_fList {L : fgraph ℕ} (hn : (listOfDarts L).Nodup) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : nList L (fList L d) = eList d := by
  show eList (prevEl (findFaceDarts L (fList L d)) (fList L d)) = _
  rw [findFace_fList hn hd]
  show eList (prevEl (findFaceDarts L d) (nextEl (findFaceDarts L d) d)) = eList d
  exact congrArg eList (prevEl_nextEl (findFaceDarts_nodup hn d)
    (dart_in_face L d |>.mpr hd))

theorem bijOn_fList {L : fgraph ℕ} (hn : (listOfDarts L).Nodup) :
    Set.BijOn (fList L) {d | d ∈ listOfDarts L} {d | d ∈ listOfDarts L} := by
  refine ⟨fun d hd => fList_mem_darts hn hd, fun a ha b hb heq => ?_, fun y hy => ?_⟩
  · have hla := prev_fList_inverse hn ha
    have hlb := prev_fList_inverse hn hb
    calc a = prevEl (findFaceDarts L (fList L a)) (fList L a) := hla.symm
      _ = prevEl (findFaceDarts L (fList L b)) (fList L b) :=
            congrArg (fun z => prevEl (findFaceDarts L z) z) heq
      _ = b := hlb
  · exact ⟨prevEl (findFaceDarts L y) y,
      mem_darts_of_mem_findFace L (prevEl_mem_of_mem (dart_in_face L y |>.mpr hy)),
      fList_prev_inverse hn hy⟩

theorem bijOn_nList {L : fgraph ℕ} (hL : GoodList L) :
    Set.BijOn (nList L) {d | d ∈ listOfDarts L} {d | d ∈ listOfDarts L} := by
  have hn : (listOfDarts L).Nodup := hL.1
  refine ⟨fun d hd => ?_, fun a ha b hb heq => ?_, fun y hy => ?_⟩
  · show eList (prevEl (findFaceDarts L d) d) ∈ listOfDarts L
    exact hL.2.2 _ (mem_darts_of_mem_findFace L (prevEl_mem_of_mem
      (dart_in_face L d |>.mpr hd)))
  · change eList (prevEl (findFaceDarts L a) a)
      = eList (prevEl (findFaceDarts L b) b) at heq
    have hprev : prevEl (findFaceDarts L a) a = prevEl (findFaceDarts L b) b :=
      eList_inj heq
    have k1 : fList L (prevEl (findFaceDarts L a) a) = a := fList_prev_inverse hn ha
    have k2 : fList L (prevEl (findFaceDarts L b) b) = b := fList_prev_inverse hn hb
    calc a = fList L (prevEl (findFaceDarts L a) a) := k1.symm
      _ = fList L (prevEl (findFaceDarts L b) b) := by rw [hprev]
      _ = b := k2
  · refine ⟨fList L (eList y), fList_mem_darts hn (hL.2.2 y hy), ?_⟩
    show nList L (fList L (eList y)) = y
    rw [nList_fList hn (d := eList y) (hL.2.2 y hy)]
    rfl

/-! ### hypermapOfList 构造 -/

noncomputable def hypermapOfList (L : fgraph ℕ) (hL : GoodList L) : Hypermap (ℕ × ℕ) :=
  have hN : (listOfDarts L).Nodup := hL.1
  have hsd : ((listOfDarts L).toFinset : Set (ℕ × ℕ)) = {d | d ∈ listOfDarts L} := by
    ext d
    exact List.mem_toFinset
  have hbe' := bijOn_res (fs := (listOfDarts L).toFinset)
    (s := {d | d ∈ listOfDarts L}) hsd (bijOn_eList hL)
  have hbn' := bijOn_res (fs := (listOfDarts L).toFinset)
    (s := {d | d ∈ listOfDarts L}) hsd (bijOn_nList hL)
  have hbf' := bijOn_res (fs := (listOfDarts L).toFinset)
    (s := {d | d ∈ listOfDarts L}) hsd (bijOn_fList hN)
  { darts := (listOfDarts L).toFinset
    edgeMap := extendPerm (listOfDarts L).toFinset eList hbe'
    nodeMap := extendPerm (listOfDarts L).toFinset (nList L) hbn'
    faceMap := extendPerm (listOfDarts L).toFinset (fList L) hbf'
    edgeMap_permutes := extendPerm_permutes
    nodeMap_permutes := extendPerm_permutes
    faceMap_permutes := extendPerm_permutes
    comp_eq_one := by
      refine Equiv.Perm.ext fun d => ?_
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      by_cases hd : d ∈ ((listOfDarts L).toFinset : Set (ℕ × ℕ))
      · have hd' : d ∈ listOfDarts L := List.mem_toFinset.mp hd
        have hfd : fList L d ∈ ((listOfDarts L).toFinset : Set (ℕ × ℕ)) :=
          List.mem_toFinset.mpr (fList_mem_darts hN hd')
        have hnd : nList L (fList L d) ∈ ((listOfDarts L).toFinset : Set (ℕ × ℕ)) :=
          List.mem_toFinset.mpr (by rw [nList_fList hN hd']; exact hL.2.2 d hd')
        simp only [extendPerm, Equiv.ofBijective_apply, Fan.res, hd, hfd, hnd, if_true]
        rw [nList_fList hN hd']
        rfl
      · simp only [extendPerm, Equiv.ofBijective_apply, Fan.res, hd, if_false] }

theorem darts_hypermapOfList (L : fgraph ℕ) (hL : GoodList L) :
    (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ)) = {d | d ∈ listOfDarts L} := by
  ext d
  exact List.mem_toFinset

theorem edgeMap_hypermapOfList (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ (hypermapOfList L hL).darts) : (hypermapOfList L hL).edgeMap d = eList d := by
  have hd' : d ∈ ((listOfDarts L).toFinset : Set (ℕ × ℕ)) := hd
  unfold hypermapOfList
  simp only [extendPerm, Equiv.ofBijective_apply, Fan.res, hd', if_true]

theorem nodeMap_hypermapOfList (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ (hypermapOfList L hL).darts) :
    (hypermapOfList L hL).nodeMap d = nList L d := by
  have hd' : d ∈ ((listOfDarts L).toFinset : Set (ℕ × ℕ)) := hd
  unfold hypermapOfList
  simp only [extendPerm, Equiv.ofBijective_apply, Fan.res, hd', if_true]

theorem faceMap_hypermapOfList (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ (hypermapOfList L hL).darts) :
    (hypermapOfList L hL).faceMap d = fList L d := by
  have hd' : d ∈ ((listOfDarts L).toFinset : Set (ℕ × ℕ)) := hd
  unfold hypermapOfList
  simp only [extendPerm, Equiv.ofBijective_apply, Fan.res, hd', if_true]

end S1HypermapOfList


/-! ### S3: Hypermap.Iso 白捡件（refl/symm/trans 桥） -/
-- Hypermap.Iso 与其 refl/symm/trans 已在 Kepler/Text/Hypermap.lean:8249-8296
-- 真证明（`Hypermap.Iso` 与 Assembly §1b `HypermapIso` 逐字同体）；装配 lane
-- 以 `Assembly.HypermapIso H G ↔ H.Iso G`（Iff.rfl，两 def 体逐字同体）桥接。
-- 此处补 ℕ×ℕ/ℕ 实例化形（hypermapOfList 与其被消费侧的常用形）。
-- （S1 section 内的 scoped open 已随 section 结束失效，S3/S11 重申。）
open Kepler.Assembly (listOfDarts GoodList)
open Kepler.Graphs (fgraph)

theorem hypermapOfList_iso_refl (L : fgraph ℕ) (hL : GoodList L) :
    Hypermap.Iso (hypermapOfList L hL) (hypermapOfList L hL) :=
  Kepler.Text.Hypermap.Iso.refl (hypermapOfList L hL)

/-! ### S11: GoodGraphV4 / GoodListNodes 忠实 def 层（tame_defs2.hl:31-80） -/

/-- HOL `list_of_elements`（list_hypermap-compiled.hl:28）。 -/
def listOfElements (L : fgraph ℕ) : List ℕ := L.flatten.eraseDups

/-- HOL `elements_of_list`（list_hypermap-compiled.hl:29）。 -/
def elementsOfList (L : fgraph ℕ) : Set ℕ := {x | x ∈ listOfElements L}

/-- HOL `nodes_of_list` 的集合形态：
`MAP (λx. filter (λd. FST d = x) (list_of_darts L)) (list_of_elements L)`
经 `set_of_list`（list_hypermap-compiled.hl:30-32）。 -/
def nodesOfListSet (L : fgraph ℕ) : Set (Set (ℕ × ℕ)) :=
  (fun x : ℕ => {d | d ∈ listOfDarts L ∧ d.1 = x}) '' {x | x ∈ listOfElements L}

/-- HOL `good_list_nodes`（tame_defs2.hl:67-68）的忠实 def 层。
Assembly §1b `GoodListNodes`（现为 `True` 占位）的补全源；装配 lane 以
DEF-FIX 折算登记后切换。 -/
def GoodListNodesTl (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  (hypermapOfList L hL).nodeSet = nodesOfListSet L



/-! ## 10. L-A7 支撑层：rot 1 / swap / map-运输序列件（ELLLNYZ.hl:209-494 + tame_list.hl）

REVERSE 理论与 MAP 运输家族的序列件层（`la7_*` 前缀；HOL `rot 1` ↦ `List.rotate 1`、
`REVERSE` ↦ `List.reverse`、`\d. SND d, FST d` ↦ `eList`）。已证：rotOne 基本群、
`la7_idxOf_rotOne`/`_shift`（index_rot）、`la7_idxOf_map`（Seq.index_map）、
`la7_idxOf_reverse`（indexl_rev）、`la7_nextEl_rotOne`/`la7_prevEl_rotOne`
（next_el_rot_eq/prev_el_rot_eq）、`la7_nextEl_reverse`/`la7_prevEl_reverse`
（next_el_rev/对偶）、`la7_prevEl_map`/`la7_nextEl_map`（prev_el_map/
next_el_MEM_map）。
已证（MAP/REVERSE 运输块）：`la7_listPairs_reverse`（list_pairs2_rev，
tame_list.hl:1156）、`la7_mem_listPairs_reverse`/`la7_listOfDarts_reverse`
（list_pairs_rev_eq/list_of_darts_rev）、`la7_listPairs_map`/`la7_listOfDarts_map`/
`la7_mapGoodList`（map_list_pairs/map_list_of_darts/map_good_list）、
`la7_dart_in_findFace`/`la7_findFace_nodup`/`la7_findFace_mem`（dart_in_face/
uniq_find_face）、`la7_findFace_reverse`/`la7_findFace_map`（find_face_rev/
find_face_map）、`la7_goodList_reverse`/`la7_darts_reverse`/`la7_edgeMap_reverse`/
`la7_faceMap_reverse`/`la7_nodeMap_reverse`/`la7_hypermapOfList_reverse`
（good_list_REVERSE/dart_REVERSE/edge·face·node_map_reverse 共轭束，face/node
互换方向：fList L' (eList d) = nList L d、nList L' (eList d) = fList L d）。
另证（MAP Iso 束）：`la7_hypermapOfList_map`（tame_list.hl:3493 的列表层 Iso，
同构函数 = pair-lift：Set.BijOn 三件 + nList/fList/eList 三向交换）。
仍未做：`Hypermap` 类型层的 `hypermapOfList` 构造与 Hypermap.Iso（Assembly
IsHypermapOfList 桥，超出列表层预算）。 -/

section LA7ReverseMap
open Kepler.Assembly (listPairs listOfDarts findFaceDarts eList fList nList nextEl prevEl
  GoodList)
open scoped List
open Kepler.Graphs (fgraph)

variable {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]

/-- ssreflect `rot 1 s`（Mathlib `List.rotate 1` 的 la7 别名）。 -/
def la7RotOne {α : Type*} (l : List α) : List α := l.rotate 1

/-- ssreflect 侧 `rot 1 = drop 1 ++ take 1` 折算。 -/
theorem la7_rotOne_eq (l : List α) : la7RotOne l = l.drop 1 ++ l.take 1 := by
  cases l with
  | nil => simp [la7RotOne]
  | cons a t => exact List.rotate_eq_drop_append_take (by rw [List.length_cons]; omega)

theorem la7_eList_involutory (d : ℕ × ℕ) : eList (eList d) = d := by
  cases d with
  | mk a b => rfl

/-- Nodup 对 map 的 on-集单射形式。 -/
theorem la7_nodup_map_on {α β : Type*} {f : α → β} {l : List α}
    (hinj : ∀ u ∈ l, ∀ v ∈ l, f u = f v → u = v) (hn : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih (fun u hu v hv => hinj u (List.mem_cons_of_mem a hu)
      v (List.mem_cons_of_mem a hv)) h2⟩
    rcases List.mem_map.mp hm with ⟨b, hb, hfb⟩
    have hba : b = a := hinj b (List.mem_cons_of_mem a hb) a List.mem_cons_self hfb
    exact absurd (hba ▸ hb : a ∈ t) h1

/-- `rotOne` 保元素。 -/
theorem la7_mem_rotOne {α : Type*} {l : List α} {z : α} : z ∈ la7RotOne l ↔ z ∈ l :=
  List.mem_rotate

theorem la7_rotOne_nodup {α : Type*} {l : List α} (h : l.Nodup) : (la7RotOne l).Nodup := by
  unfold la7RotOne
  rw [List.nodup_rotate]
  exact h

theorem la7_length_rotOne {α : Type*} (l : List α) :
    (la7RotOne l).length = l.length :=
  List.length_rotate l 1

/-- `rotOne` 的逐点取值（Mathlib `List.getElem_rotate` 的 la7 形）。 -/
theorem la7_getElem_rotOne {l : List α} {i : ℕ} (hi : i < l.length) :
    (la7RotOne l)[i]'(Nat.lt_of_lt_of_eq hi (la7_length_rotOne l).symm)
      = l[(i + 1) % l.length]'(Nat.mod_lt (i + 1) (show 0 < l.length from by omega)) :=
  List.getElem_rotate l 1 i (Nat.lt_of_lt_of_eq hi (la7_length_rotOne l).symm)

/-- HOL `Seq2.index_rot`（rot 1 后的下标；n = 1 情形）。 -/
theorem la7_idxOf_rotOne {l : List α} (hn : l.Nodup) {x : α} (hx : x ∈ l) :
    (la7RotOne l).idxOf x = (l.idxOf x + l.length - 1) % l.length := by
  cases l with
  | nil => exact absurd hx (by simp)
  | cons y t =>
    have hyt : la7RotOne (y :: t) = t ++ [y] := by
      show (y :: t).rotate 1 = t ++ [y]
      rw [List.rotate_cons_succ, List.rotate_zero]
    have hnd : y ∉ t := (List.nodup_cons.mp hn).1
    rw [hyt]
    rcases List.mem_cons.mp hx with rfl | hxt
    · rw [List.idxOf_append_of_notMem hnd, List.idxOf_cons_self, List.idxOf_cons_self,
        List.length_cons, Nat.zero_add, Nat.add_sub_cancel,
        Nat.mod_eq_of_lt (show t.length < t.length + 1 from by omega), Nat.add_zero]
    · have hyx : y ≠ x := fun hc => (List.nodup_cons.mp hn).1 (hc ▸ hxt)
      rw [List.idxOf_append_of_mem hxt, List.idxOf_cons_ne t hyx, Nat.succ_eq_add_one,
        List.length_cons]
      have hlt : t.idxOf x < t.length := List.idxOf_lt_length_iff.mpr hxt
      have e : t.idxOf x + 1 + (t.length + 1) - 1 = t.idxOf x + (t.length + 1) := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (show t.idxOf x < t.length + 1 from by omega)]

/-- rotOne 位置转移：x 在 rotOne 中下标 +1 的模位置 = 原表下标。 -/
theorem la7_idxOf_rotOne_shift {l : List α} (hn : l.Nodup) {x : α} (hx : x ∈ l) :
    ((la7RotOne l).idxOf x + 1) % l.length = l.idxOf x := by
  have hpos : 0 < l.length := List.length_pos_of_mem hx
  have hilt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
  rw [la7_idxOf_rotOne hn hx]
  rcases Nat.eq_zero_or_pos (l.idxOf x) with h0 | hp
  · have hme : l.length - 1 + 1 = l.length := by omega
    rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (show l.length - 1 < l.length from by omega),
      hme, Nat.mod_self]
  · have he : l.idxOf x + l.length - 1 = (l.idxOf x - 1) + l.length := by omega
    have him1 : l.idxOf x - 1 < l.length := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt him1,
      Nat.sub_add_cancel (show 1 ≤ l.idxOf x from by omega), Nat.mod_eq_of_lt hilt]

/-- HOL `Seq.index_map` 的 on-集单射形式（首现语义，无需 uniq）。 -/
theorem la7_idxOf_map {β : Type*} [BEq β] [LawfulBEq β] {f : α → β}
    {l : List α} (hinj : ∀ u ∈ l, ∀ v ∈ l, f u = f v → u = v) {d : α} (hd : d ∈ l) :
    (l.map f).idxOf (f d) = l.idxOf d := by
  induction l with
  | nil => exact absurd hd (by simp)
  | cons a t ih =>
    rw [List.map_cons]
    by_cases hfa : f a = f d
    · rcases List.mem_cons.mp hd with rfl | hmem
      · rw [List.idxOf_cons_self, List.idxOf_cons_self]
      · have hda : a = d := hinj a List.mem_cons_self d (List.mem_cons_of_mem a hmem) hfa
        rw [hda, List.idxOf_cons_self, List.idxOf_cons_self]
    · have had : a ≠ d := fun hc => hfa (by rw [hc])
      have hdt : d ∈ t := by
        rcases List.mem_cons.mp hd with hle | hin
        · exact absurd hle.symm had
        · exact hin
      rw [List.idxOf_cons_ne (l := List.map f t) (a := f d) (b := f a) hfa,
        List.idxOf_cons_ne (l := t) (a := d) (b := a) had]
      exact congrArg Nat.succ (ih (fun u hu v hv => hinj u (List.mem_cons_of_mem a hu)
        v (List.mem_cons_of_mem a hv)) hdt)

/-- HOL `indexl_rev`（ELLLNYZ.hl:316）。 -/
theorem la7_idxOf_reverse {l : List α} (hn : l.Nodup) {x : α} (hx : x ∈ l) :
    l.reverse.idxOf x = l.length - (l.idxOf x + 1) := by
  induction l with
  | nil => exact absurd hx (by simp)
  | cons a t ih =>
    have hnd : a ∉ t := (List.nodup_cons.mp hn).1
    rw [List.reverse_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · rw [List.idxOf_append_of_notMem (List.mem_reverse.not.mpr hnd),
        List.idxOf_cons_self, List.length_reverse, List.idxOf_cons_self,
        List.length_cons, Nat.zero_add, Nat.add_sub_cancel, Nat.add_zero]
    · have hax : a ≠ x := fun hc => hnd (hc ▸ hxt)
      rw [List.idxOf_append_of_mem (List.mem_reverse.mpr hxt),
        ih (List.nodup_cons.mp hn).2 hxt,
        List.idxOf_cons_ne t hax, Nat.succ_eq_add_one, List.length_cons]
      omega

/-- `prevEl` 的 getD 统一形（两分支折算）。 -/
theorem la7_prevEl_getD {l : List α} {x : α} (hx : x ∈ l) :
    prevEl l x = l.getD ((l.idxOf x + l.length - 1) % l.length) x := by
  have hpos : 0 < l.length := List.length_pos_of_mem hx
  have hilt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
  unfold prevEl
  rw [if_neg (show ¬(x ∉ l) from by simp [hx]), li_idxOf_congr]
  split
  · rename_i h0
    rw [h0, getD_wrap_prev hpos]
    exact li_getLastD_getD hpos x
  · rename_i hne
    exact (getD_prev hilt hne x).symm

/-- BEq-only 世界（无 [DecidableEq]）的 `nextEl_eq_getD` 独立形：`nextEl` 的
def-body 只用外部 `s.idxOf`（同一 [BEq α] 实例），无实例迁移。 -/
private theorem la7_nextEl_getD_form {α : Type*} [BEq α] [LawfulBEq α] {s : List α} {x : α}
    (hx : x ∈ s) : nextEl s x = s.getD ((s.idxOf x + 1) % s.length) x := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  have hilt : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  unfold nextEl
  by_cases he : s.idxOf x = s.length - 1
  · have hz : (s.idxOf x + 1) % s.length = (s.length - 1 + 1) % s.length := by rw [he]
    rw [if_pos he, hz, getD_wrap_next hpos, headD_eq_getD_zero]
  · have hj1 : s.idxOf x + 1 < s.length := by omega
    rw [if_neg he, getD_next hj1]

/-- BEq-only 世界：`x ∉ s` 时 `nextEl` 退化为默认元 `x`（`s.idxOf x = s.length`，
len = 0 走 headD 分支、len ≥ 1 走越界 getD 分支，两者均取 `x`）。 -/
private theorem la7_nextEl_of_notMem {α : Type*} [BEq α] [LawfulBEq α] {s : List α} {x : α}
    (hx : x ∉ s) : nextEl s x = x := by
  unfold nextEl
  by_cases h0 : s.length = 0
  · have hs : s = [] := List.length_eq_zero_iff.mp h0
    subst hs
    simp
  · have hidx : s.idxOf x = s.length := List.idxOf_eq_length_iff.mpr hx
    have hne1 : ¬(s.idxOf x = s.length - 1) := by rw [hidx]; omega
    rw [if_neg hne1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [hidx]; omega)]
    simp

/-- HOL `Seq2.next_el_rot_eq`（n = 1 情形，函数形式逐字）。 -/
theorem la7_nextEl_rotOne {l : List α} (hn : l.Nodup) :
    ∀ x, nextEl (la7RotOne l) x = nextEl l x := by
  intro x
  by_cases hx : x ∈ l
  · have hpos : 0 < l.length := List.length_pos_of_mem hx
    have hmem1 : x ∈ la7RotOne l := la7_mem_rotOne.mpr hx
    have hilt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
    have hilt' : l.idxOf x < (la7RotOne l).length := by rw [la7_length_rotOne]; exact hilt
    have hb2 : (l.idxOf x + 1) % l.length < l.length := Nat.mod_lt _ hpos
    rw [nextEl_eq_getD hmem1, nextEl_eq_getD hx, la7_length_rotOne,
      la7_idxOf_rotOne_shift hn hx, getD_eq_getElem_of_lt hilt',
      la7_getElem_rotOne hilt, getD_eq_getElem_of_lt hb2]
  · -- x ∉ l：la7RotOne 保元素，两侧均退化为默认元 x
    exact (la7_nextEl_of_notMem (fun hc => hx (la7_mem_rotOne.mp hc))).trans
      (la7_nextEl_of_notMem hx).symm

/-- HOL `Seq2.prev_el_rot_eq` 对偶件（n = 1，点态形式）。位置转移经
`Nat.mod_add_mod` 一步折算：((idx' + len - 1) % len + 1) % len = (idx' + len) % len
= (idx + len - 1) % len（idx = (idx'+1) % len）。 -/
theorem la7_prevEl_rotOne {l : List α} (hn : l.Nodup) {x : α} (hx : x ∈ l) :
    prevEl (la7RotOne l) x = prevEl l x := by
  by_cases hx : x ∈ l
  · have hpos : 0 < l.length := List.length_pos_of_mem hx
    have hmem1 : x ∈ la7RotOne l := la7_mem_rotOne.mpr hx
    have hilt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
    have hshift : ((la7RotOne l).idxOf x + 1) % l.length = l.idxOf x :=
      la7_idxOf_rotOne_shift hn hx
    rw [la7_prevEl_getD hmem1, la7_prevEl_getD hx, la7_length_rotOne]
    have hj : ((la7RotOne l).idxOf x + l.length - 1) % l.length
        < (la7RotOne l).length := by
      rw [la7_length_rotOne]; exact Nat.mod_lt _ hpos
    have hj2 : (l.idxOf x + l.length - 1) % l.length < l.length :=
      Nat.mod_lt _ hpos
    have hjl : ((la7RotOne l).idxOf x + l.length - 1) % l.length < l.length :=
      Nat.mod_lt _ hpos
    have hjl : ((la7RotOne l).idxOf x + l.length - 1) % l.length < l.length :=
      Nat.mod_lt _ hpos
    have hkey : (((la7RotOne l).idxOf x + l.length - 1) % l.length + 1) % l.length
        = (l.idxOf x + l.length - 1) % l.length := by
      have e0 : (la7RotOne l).idxOf x + l.length - 1 + 1
          = (la7RotOne l).idxOf x + 1 + (l.length - 1) := by omega
      have e1 : l.idxOf x + l.length - 1 = l.idxOf x + (l.length - 1) := by omega
      calc (((la7RotOne l).idxOf x + l.length - 1) % l.length + 1) % l.length
          = ((la7RotOne l).idxOf x + l.length - 1 + 1) % l.length :=
            Nat.mod_add_mod _ _ _
        _ = ((la7RotOne l).idxOf x + 1 + (l.length - 1)) % l.length := by rw [e0]
        _ = (((la7RotOne l).idxOf x + 1) % l.length + (l.length - 1) % l.length) % l.length :=
            Nat.add_mod _ _ _
        _ = (l.idxOf x + (l.length - 1)) % l.length := by
              rw [hshift, Nat.mod_eq_of_lt (show l.length - 1 < l.length from by omega)]
        _ = (l.idxOf x + l.length - 1) % l.length := by rw [e1]
    rw [getD_eq_getElem_of_lt hj x, getD_eq_getElem_of_lt hj2 x]
    simp only [la7_getElem_rotOne hjl, hkey]
  · -- x ∉ l：prevEl 的 junk 首分支，两侧均取默认元 x
    have hnx : x ∉ la7RotOne l := fun hc => hx (la7_mem_rotOne.mp hc)
    unfold prevEl
    rw [if_pos hnx, if_pos hx]


/-- HOL `prev_el_map`（tame_list.hl:948，on-集单射形式）。 -/
theorem la7_prevEl_map {β : Type*} [BEq β] [LawfulBEq β] [DecidableEq β] {f : α → β}
    {l : List α} (hinj : ∀ u ∈ l, ∀ v ∈ l, f u = f v → u = v) {d : α} (hd : d ∈ l) :
    prevEl (l.map f) (f d) = f (prevEl l d) := by
  have hpos : 0 < l.length := List.length_pos_of_mem hd
  have hilt : l.idxOf d < l.length := List.idxOf_lt_length_iff.mpr hd
  have hmem : f d ∈ l.map f := List.mem_map_of_mem hd
  have hb : l.length - 1 < l.length := by omega
  have hb1 : l.length - 1 < (l.map f).length := by rw [List.length_map]; omega
  rw [la7_prevEl_getD hd]
  unfold prevEl
  rw [if_neg (show ¬(f d ∉ l.map f) from by simp [hmem]), li_idxOf_congr (α := β),
    la7_idxOf_map hinj hd]
  split
  · rename_i h0
    rw [h0, li_getLastD_getD (by rw [List.length_map]; omega), List.length_map,
      Nat.zero_add, Nat.mod_eq_of_lt hb, getD_eq_getElem_of_lt hb1, List.getElem_map,
      getD_eq_getElem_of_lt hb]
  · rename_i hne
    have he : l.idxOf d + l.length - 1 = (l.idxOf d - 1) + l.length := by omega
    have hmod : (l.idxOf d - 1) % l.length = l.idxOf d - 1 :=
      Nat.mod_eq_of_lt (show l.idxOf d - 1 < l.length from by omega)
    have hb1' : l.idxOf d - 1 < (l.map f).length := by rw [List.length_map]; omega
    have hb0 : l.idxOf d - 1 < l.length := by omega
    rw [he, Nat.add_mod_right, hmod, getD_eq_getElem_of_lt hb1', List.getElem_map,
      getD_eq_getElem_of_lt (show l.idxOf d - 1 < l.length from hb0)]

/-- HOL `next_el_MEM_map`（tame_list.hl:1011，on-集单射形式）。`nextEl` 的
def-body 只用外部 `s.idxOf`（同一 [BEq β] 实例），故无需 prevEl 侧的
`li_idxOf_congr` 双实例桥，直接 getElem_map 逐点搬运。 -/
theorem la7_nextEl_map {β : Type*} [BEq β] [LawfulBEq β] {f : α → β}
    {l : List α} (hinj : ∀ u ∈ l, ∀ v ∈ l, f u = f v → u = v) {d : α} (hd : d ∈ l) :
    nextEl (l.map f) (f d) = f (nextEl l d) := by
  have hpos : 0 < l.length := List.length_pos_of_mem hd
  have hmem : f d ∈ l.map f := List.mem_map_of_mem hd
  have hj : (l.idxOf d + 1) % l.length < l.length := Nat.mod_lt _ hpos
  have hj' : (l.idxOf d + 1) % l.length < (l.map f).length := by
    rw [List.length_map]; exact hj
  rw [la7_nextEl_getD_form hmem, la7_idxOf_map hinj hd, List.length_map,
    la7_nextEl_getD_form hd, getD_eq_getElem_of_lt hj' (f d), List.getElem_map,
    getD_eq_getElem_of_lt hj d]

/-! ### la7 REVERSE 主链 + MAP 运输主件（ELLLNYZ.hl:209-494 / tame_list.hl:3403-3520）

序列件（rotOne / idxOf / nextEl·prevEl）已就位；以下为逐面 `listPairs` 层、
GoodList 三合取的 reverse 交换律、findFace / faceMap / nodeMap 运输件、
`hypermapOfList` 逐字段（edge/node/face）reverse 共轭恒等式，及 MAP 侧
`map_good_list` / `find_face_map` / `hypermap_of_list_map`（Hypermap.Iso 形）。 -/

/-- HOL `next_el_rev`（ELLLNYZ.hl:337）。 -/
theorem la7_nextEl_reverse {l : List α} (hn : l.Nodup) {x : α} (hx : x ∈ l) :
    nextEl l.reverse x = prevEl l x := by
  have hpos : 0 < l.length := List.length_pos_of_mem hx
  have hilt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
  have hmemr : x ∈ l.reverse := List.mem_reverse.mpr hx
  rw [la7_nextEl_getD_form hmemr, la7_idxOf_reverse hn hx, List.length_reverse,
    la7_prevEl_getD hx]
  rcases Nat.eq_zero_or_pos (l.idxOf x) with h0 | hp
  · have e : l.length - (l.idxOf x + 1) + 1 = l.length := by rw [h0]; omega
    rw [e, h0, getD_wrap_prev hpos, Nat.mod_self,
      getD_eq_getElem_of_lt (show 0 < l.reverse.length from by
        rw [List.length_reverse]; omega),
      List.getElem_reverse,
      getD_eq_getElem_of_lt (show l.length - 1 < l.length from by omega)]
    congr 1
  · have e : l.length - (l.idxOf x + 1) + 1 = l.length - l.idxOf x := by omega
    have hmod : (l.length - l.idxOf x) % l.length = l.length - l.idxOf x :=
      Nat.mod_eq_of_lt (show l.length - l.idxOf x < l.length from by omega)
    rw [e, hmod, getD_prev hilt (by omega),
      getD_eq_getElem_of_lt (show l.length - l.idxOf x < l.reverse.length from by
        rw [List.length_reverse]; omega),
      List.getElem_reverse,
      getD_eq_getElem_of_lt (show l.idxOf x - 1 < l.length from by omega)]
    congr 1
    omega

/-- HOL `prev_el_rev`（`next_el_rev` 对偶件，经 `l.reverse.reverse = l` 折算）。 -/
theorem la7_prevEl_reverse {l : List α} (hn : l.Nodup) {x : α} (hx : x ∈ l) :
    prevEl l.reverse x = nextEl l x := by
  have hmemr : x ∈ l.reverse := List.mem_reverse.mpr hx
  have hndr : l.reverse.Nodup := List.nodup_reverse.mpr hn
  have h1r := la7_nextEl_reverse (l := l.reverse) hndr hmemr
  rw [List.reverse_reverse] at h1r
  exact h1r.symm

theorem la7_length_listPairs {α : Type*} (l : List α) :
    (listPairs l).length = l.length := by
  unfold listPairs
  rw [List.length_zip, List.length_append, List.length_drop, List.length_take]
  omega

/-- HOL `list_pairs2_rev`（tame_list.hl:1156）：`list_pairs (REVERSE x)
= rot 1 (REVERSE (MAP e_list (list_pairs x)))`。逐点 `List.ext_get`，分支一/二由
`(i+1) % len` 的两支折算，getElem zip/rotate/reverse/map 逐层搬运。 -/
theorem la7_listPairs_reverse (l : List α) :
    listPairs l.reverse
      = la7RotOne (((listPairs l).map (fun d : α × α => (d.2, d.1))).reverse) := by
  have hzlp : (l.zip (l.drop 1 ++ l.take 1)).length = l.length := la7_length_listPairs l
  have hlen : (listPairs l.reverse).length
      = (la7RotOne (((listPairs l).map (fun d : α × α => (d.2, d.1))).reverse)).length := by
    simp only [la7_length_rotOne, List.length_reverse, List.length_map, la7_length_listPairs]
  refine List.ext_get hlen ?_
  intro i hi1 hi2
  show (listPairs l.reverse)[i]'hi1
    = (la7RotOne (((listPairs l).map (fun d : α × α => (d.2, d.1))).reverse))[i]'hi2
  have hilt : i < l.length := by
    have h2 : (listPairs l.reverse).length = l.length := by
      rw [la7_length_listPairs, List.length_reverse]
    omega
  have hrev : l.reverse.length = l.length := List.length_reverse
  rcases Nat.lt_or_ge i (l.length - 1) with hA | hB
  · -- 分支一：i + 1 < l.length
    have hA1 : i < (l.reverse.drop 1).length := by rw [List.length_drop]; omega
    have hA2 : l.length - 1 - (i + 1) < (l.drop 1).length := by
      rw [List.length_drop]; omega
    have hAmod : (i + 1) % l.length = i + 1 := Nat.mod_eq_of_lt (by omega)
    have hAnorm : l.length - 1 - i = l.length - 1 - (i + 1) + 1 := by omega
    simp only [listPairs, la7RotOne, hzlp, List.getElem_zip, List.getElem_rotate, hAmod,
      List.getElem_append_left hA1, List.getElem_append_left hA2,
      List.getElem_drop, Nat.add_comm 1 i, Nat.add_comm 1 (l.length - 1 - (i + 1)),
      List.getElem_reverse, List.length_reverse, List.length_map, List.getElem_map, hAnorm]
  · -- 分支二：i + 1 = l.length
    obtain hiB : i = l.length - 1 := by omega
    subst hiB
    have hB1 : (l.reverse.drop 1).length ≤ l.length - 1 := by
      rw [List.length_drop, List.length_reverse]
    have hB2 : (l.drop 1).length ≤ l.length - 1 := by rw [List.length_drop]
    have hB3 : l.length - 1 - (l.reverse.drop 1).length = 0 := by
      rw [List.length_drop, List.length_reverse]; omega
    have hB4 : l.length - 1 - (l.drop 1).length = 0 := by rw [List.length_drop]; omega
    have hB5 : l.length - 1 - (l.length - 1) = 0 := by omega
    have hBmod : (l.length - 1 + 1) % l.length = 0 := by
      rw [Nat.sub_add_cancel (show 1 ≤ l.length from by omega), Nat.mod_self]
    simp only [listPairs, la7RotOne, hzlp, List.getElem_zip, List.getElem_rotate, hBmod,
      List.getElem_append_right hB1, List.getElem_append_right hB2, hB3, hB4, hB5,
      List.getElem_reverse, Nat.sub_zero, List.length_reverse, List.length_map,
      List.getElem_take, List.getElem_map]

/-- tame_list.hl:1229 `list_pairs_rev_eq`。 -/
theorem la7_mem_listPairs_reverse {l : List α} {d : α × α} :
    d ∈ listPairs l.reverse ↔ (d.2, d.1) ∈ listPairs l := by
  rw [la7_listPairs_reverse, la7_mem_rotOne, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨c, hc, hcd⟩
    rw [← hcd]
    exact hc
  · intro h
    exact ⟨(d.2, d.1), h, rfl⟩

/-- `d ∈ listOfDarts L` 展开到所属面。 -/
private theorem la7_mem_listOfDarts_iff_face (L : fgraph ℕ) (d : ℕ × ℕ) :
    d ∈ listOfDarts L ↔ ∃ l ∈ L, d ∈ listPairs l := by
  unfold listOfDarts
  simp only [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨b, hb, hdb⟩
    obtain ⟨l, hl, hlb⟩ := hb
    subst hlb
    exact ⟨l, hl, hdb⟩
  · rintro ⟨l, hl, hdl⟩
    exact ⟨listPairs l, ⟨l, hl, rfl⟩, hdl⟩

/-- tame_list.hl:1239 `list_of_darts_rev`。 -/
theorem la7_listOfDarts_reverse (L : fgraph ℕ) (d : ℕ × ℕ) :
    (d.2, d.1) ∈ listOfDarts (L.map List.reverse) ↔ d ∈ listOfDarts L := by
  rw [la7_mem_listOfDarts_iff_face, la7_mem_listOfDarts_iff_face]
  constructor
  · rintro ⟨l', hl', hmem⟩
    obtain ⟨l, hl, hlr⟩ := List.mem_map.mp hl'
    subst hlr
    exact ⟨l, hl, (la7_mem_listPairs_reverse (l := l) (d := (d.2, d.1))).mp hmem⟩
  · rintro ⟨l, hl, hmem⟩
    refine ⟨List.reverse l, List.mem_map.mpr ⟨l, hl, rfl⟩,
      (la7_mem_listPairs_reverse (l := l) (d := (d.2, d.1))).mpr hmem⟩

/-- tame_list.hl:3403 `map_list_pairs`。 -/
theorem la7_listPairs_map {α β : Type*} (phi : α → β) (l : List α) :
    listPairs (l.map phi) = (listPairs l).map (Prod.map phi phi) := by
  show (l.map phi).zip ((l.map phi).drop 1 ++ (l.map phi).take 1)
      = (l.zip (l.drop 1 ++ l.take 1)).map (Prod.map phi phi)
  rw [← List.map_drop, ← List.map_take, ← List.map_append, ← List.zip_map]

/-- tame_list.hl `map_list_of_darts`（find_face_map 上游件）。 -/
theorem la7_listOfDarts_map (L : fgraph ℕ) (phi : ℕ → ℕ) :
    listOfDarts (L.map (List.map phi))
      = (listOfDarts L).map (fun d : ℕ × ℕ => (phi d.1, phi d.2)) := by
  show ((L.map (List.map phi)).map listPairs).flatten
      = ((L.map listPairs).flatten).map (fun d : ℕ × ℕ => (phi d.1, phi d.2))
  rw [List.map_map,
    List.map_congr_left (f := listPairs ∘ List.map phi)
      (g := fun l => (listPairs l).map (fun d : ℕ × ℕ => (phi d.1, phi d.2)))
      (fun l _ => la7_listPairs_map phi l)]
  show List.flatMap (fun l => (listPairs l).map (fun d : ℕ × ℕ => (phi d.1, phi d.2))) L
      = List.map (fun d : ℕ × ℕ => (phi d.1, phi d.2)) (List.flatMap listPairs L)
  rw [List.map_flatMap]

/-- `lift`（pair-lift）在 `listOfDarts L` 上的单射性（flatten-元素 ⊆ flatten L）。 -/
private theorem la7_injOn_listOfDarts (L : fgraph ℕ) {phi : ℕ → ℕ}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, phi u = phi v → u = v)
    (d e : ℕ × ℕ) (hd : d ∈ listOfDarts L) (he : e ∈ listOfDarts L)
    (h : (phi d.1, phi d.2) = (phi e.1, phi e.2)) : d = e := by
  have h1 : phi d.1 = phi e.1 := congrArg Prod.fst h
  have h2 : phi d.2 = phi e.2 := congrArg Prod.snd h
  obtain ⟨l, hl, hdl⟩ := (la7_mem_listOfDarts_iff_face L d).mp hd
  obtain ⟨m, hm, hem⟩ := (la7_mem_listOfDarts_iff_face L e).mp he
  have hd1 : d.1 ∈ l ∧ d.2 ∈ (l.drop 1 ++ l.take 1) := by
    have h2 : (d.1, d.2) ∈ l.zip (l.drop 1 ++ l.take 1) := hdl
    exact List.of_mem_zip h2
  have he1 : e.1 ∈ m ∧ e.2 ∈ (m.drop 1 ++ m.take 1) := by
    have h2 : (e.1, e.2) ∈ m.zip (m.drop 1 ++ m.take 1) := hem
    exact List.of_mem_zip h2
  have hd2 : d.2 ∈ l := by
    rcases List.mem_append.mp hd1.2 with h | h
    · exact List.drop_subset 1 l h
    · exact List.take_subset 1 l h
  have he2 : e.2 ∈ m := by
    rcases List.mem_append.mp he1.2 with h | h
    · exact List.drop_subset 1 m h
    · exact List.take_subset 1 m h
  have h11 : d.1 = e.1 :=
    hinj d.1 (List.mem_flatten.mpr ⟨l, hl, hd1.1⟩) e.1
      (List.mem_flatten.mpr ⟨m, hm, he1.1⟩) h1
  have h12 : d.2 = e.2 :=
    hinj d.2 (List.mem_flatten.mpr ⟨l, hl, hd2⟩) e.2
      (List.mem_flatten.mpr ⟨m, hm, he2⟩) h2
  show Prod.mk d.1 d.2 = Prod.mk e.1 e.2
  rw [h11, h12]

/-- tame_list.hl:3403 `map_good_list`。 -/
theorem la7_mapGoodList (L : fgraph ℕ) {phi : ℕ → ℕ}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, phi u = phi v → u = v)
    (hgood : GoodList L) : GoodList (L.map (List.map phi)) := by
  obtain ⟨hnd, hne, hswap⟩ := hgood
  refine ⟨?_, ?_, ?_⟩
  · rw [la7_listOfDarts_map]
    exact la7_nodup_map_on (f := fun d : ℕ × ℕ => (phi d.1, phi d.2))
      (fun u hu v hv huv => la7_injOn_listOfDarts L hinj u v hu hv huv) hnd
  · intro l hl
    obtain ⟨m, hm, hme⟩ := List.mem_map.mp hl
    rw [← hme]
    intro hc
    exact hne m hm (List.map_eq_nil_iff.mp hc)
  · intro d hd
    rw [la7_listOfDarts_map, List.mem_map] at hd
    obtain ⟨c, hc, hcd⟩ := hd
    rw [← hcd, la7_listOfDarts_map, List.mem_map]
    exact ⟨eList c, hswap c hc, rfl⟩

theorem la7_dart_in_findFace (L : fgraph ℕ) (d : ℕ × ℕ)
    (hd : d ∈ listOfDarts L) : d ∈ findFaceDarts L d := by
  obtain ⟨l, hl, hdl⟩ := (la7_mem_listOfDarts_iff_face L d).mp hd
  unfold findFaceDarts
  cases hf : List.find? (fun l => decide (d ∈ listPairs l)) L with
  | none =>
    have hnone : ¬ d ∈ listOfDarts L := by
      intro hmem
      obtain ⟨x, hx, hdx⟩ := (la7_mem_listOfDarts_iff_face L d).mp hmem
      have h2 := List.find?_eq_none.mp hf x hx
      exact h2 (decide_eq_true hdx)
    exact absurd hd hnone
  | some m =>
    have hmt : d ∈ listPairs m := by
      have h2 := List.find?_some hf
      simpa using h2
    exact hmt

theorem la7_findFace_nodup (L : fgraph ℕ) (d : ℕ × ℕ)
    (hnd : (listOfDarts L).Nodup) : (findFaceDarts L d).Nodup := by
  unfold findFaceDarts
  cases hf : List.find? (fun l => decide (d ∈ listPairs l)) L with
  | none => simp [listPairs]
  | some m =>
    have hms : m ∈ L := List.mem_of_find?_eq_some hf
    show (listPairs m).Nodup
    exact (List.nodup_flatten.mp hnd).1 (listPairs m) (List.mem_map.mpr ⟨m, hms, rfl⟩)

theorem la7_findFace_mem (L : fgraph ℕ) (d x : ℕ × ℕ)
    (hx : x ∈ findFaceDarts L d) : x ∈ listOfDarts L := by
  unfold findFaceDarts at hx
  cases hf : List.find? (fun l => decide (d ∈ listPairs l)) L with
  | none =>
    rw [hf] at hx
    exfalso
    have h2 : x ∈ listPairs [] := hx
    simp [listPairs] at h2
  | some m =>
    have hms : m ∈ L := List.mem_of_find?_eq_some hf
    rw [hf] at hx
    exact (la7_mem_listOfDarts_iff_face L x).mpr ⟨m, hms, hx⟩

/-- 逐面 Perm：`list_pairs (REVERSE l)` 与 `eList`-像同元素（rotate + reverse）。 -/
private theorem la7_listPairs_reverse_perm (l : List ℕ) :
    listPairs (List.reverse l) ~ (listPairs l).map (fun d : ℕ × ℕ => (d.2, d.1)) := by
  rw [la7_listPairs_reverse]
  show ((listPairs l).map (fun d : ℕ × ℕ => (d.2, d.1))).reverse.rotate 1
    ~ (listPairs l).map (fun d : ℕ × ℕ => (d.2, d.1))
  exact List.Perm.trans (List.rotate_perm _ 1) (List.reverse_perm _)

theorem la7_findFace_reverse (L : fgraph ℕ) (hgood : GoodList L) (p1 p2 : ℕ)
    (hd : (p1, p2) ∈ listOfDarts L) :
    findFaceDarts (L.map List.reverse) (p1, p2)
      = la7RotOne (((findFaceDarts L (p2, p1)).map (fun d : ℕ × ℕ => (d.2, d.1))).reverse) := by
  unfold findFaceDarts
  rw [List.find?_map]
  show listPairs ((Option.map List.reverse
    (L.find? (fun l => decide ((p1, p2) ∈ listPairs (List.reverse l))))).getD [])
    = la7RotOne (((findFaceDarts L (p2, p1)).map (fun d : ℕ × ℕ => (d.2, d.1))).reverse)
  have hpred : ∀ l ∈ L, decide ((p1, p2) ∈ listPairs (List.reverse l))
      = decide ((p2, p1) ∈ listPairs l) := fun l _ =>
    Bool.decide_congr (la7_mem_listPairs_reverse (l := l) (d := (p1, p2)))
  rw [List.find?_congr hpred]
  cases hf : List.find? (fun l => decide ((p2, p1) ∈ listPairs l)) L with
  | none =>
    exfalso
    have hswap : (p2, p1) ∈ listOfDarts L := hgood.2.2 _ hd
    obtain ⟨l, hl, hdl⟩ := (la7_mem_listOfDarts_iff_face L (p2, p1)).mp hswap
    have hnone := List.find?_eq_none.mp hf
    exact hnone l hl (decide_eq_true hdl)
  | some m =>
    have hFF : findFaceDarts L (p2, p1) = listPairs m := by
      unfold findFaceDarts
      rw [hf]
      rfl
    rw [hFF]
    exact la7_listPairs_reverse m

theorem la7_findFace_map (L : fgraph ℕ) {phi : ℕ → ℕ}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, phi u = phi v → u = v)
    (d : ℕ × ℕ) (hd : d ∈ listOfDarts L) :
    findFaceDarts (L.map (List.map phi)) (phi d.1, phi d.2)
      = (findFaceDarts L d).map (fun x : ℕ × ℕ => (phi x.1, phi x.2)) := by
  have hdm : d.1 ∈ L.flatten ∧ d.2 ∈ L.flatten := by
    obtain ⟨l, hl, hdl⟩ := (la7_mem_listOfDarts_iff_face L d).mp hd
    have h1 : d.1 ∈ l ∧ d.2 ∈ (l.drop 1 ++ l.take 1) := by
      have h2 : (d.1, d.2) ∈ l.zip (l.drop 1 ++ l.take 1) := hdl
      exact List.of_mem_zip h2
    refine ⟨List.mem_flatten.mpr ⟨l, hl, h1.1⟩, ?_⟩
    rcases List.mem_append.mp h1.2 with h | h
    · exact List.mem_flatten.mpr ⟨l, hl, List.drop_subset 1 l h⟩
    · exact List.mem_flatten.mpr ⟨l, hl, List.take_subset 1 l h⟩
  unfold findFaceDarts
  rw [List.find?_map]
  show listPairs ((Option.map (List.map phi)
    (L.find? (fun l => decide ((phi d.1, phi d.2) ∈ listPairs (l.map phi))))).getD [])
    = (findFaceDarts L d).map (fun x : ℕ × ℕ => (phi x.1, phi x.2))
  have hpred : ∀ l ∈ L, decide ((phi d.1, phi d.2) ∈ listPairs (l.map phi))
      = decide (d ∈ listPairs l) := by
    intro l hl
    have hstep : (phi d.1, phi d.2) ∈ listPairs (l.map phi) ↔ d ∈ listPairs l := by
      rw [la7_listPairs_map, List.mem_map]
      constructor
      · rintro ⟨c, hc, hcd⟩
        have h1 : phi c.1 = phi d.1 := congrArg Prod.fst hcd
        have h2 : phi c.2 = phi d.2 := congrArg Prod.snd hcd
        have hc1 : c.1 ∈ l ∧ c.2 ∈ (l.drop 1 ++ l.take 1) := by
          have h3 : (c.1, c.2) ∈ l.zip (l.drop 1 ++ l.take 1) := hc
          exact List.of_mem_zip h3
        have hc2 : c.2 ∈ l := by
          rcases List.mem_append.mp hc1.2 with h | h
          · exact List.drop_subset 1 l h
          · exact List.take_subset 1 l h
        have h11 : c.1 = d.1 :=
          hinj c.1 (List.mem_flatten.mpr ⟨l, hl, hc1.1⟩) d.1 hdm.1 h1
        have h12 : c.2 = d.2 :=
          hinj c.2 (List.mem_flatten.mpr ⟨l, hl, hc2⟩) d.2 hdm.2 h2
        have hcd' : c = d := by
          show Prod.mk c.1 c.2 = Prod.mk d.1 d.2
          rw [h11, h12]
        rw [← hcd']
        exact hc
      · rintro hmem
        exact ⟨d, hmem, rfl⟩
    exact Bool.decide_congr hstep
  rw [List.find?_congr hpred]
  cases hf : List.find? (fun l => decide (d ∈ listPairs l)) L with
  | none =>
    exfalso
    have hnone := List.find?_eq_none.mp hf
    obtain ⟨l, hl, hdl⟩ := (la7_mem_listOfDarts_iff_face L d).mp hd
    exact hnone l hl (decide_eq_true hdl)
  | some m =>
    have hFF : findFaceDarts L d = listPairs m := by
      unfold findFaceDarts
      rw [hf]
      rfl
    rw [hFF]
    exact la7_listPairs_map phi m

/-- flatten-逐面 Perm 提升。 -/
private theorem la7_flatMap_congr {γ δ : Type*} {f g : List γ → List δ} :
    ∀ (L : List (List γ)), (∀ x ∈ L, f x ~ g x) →
      (L.map f).flatten ~ (L.map g).flatten := by
  intro L
  induction L with
  | nil => intro _; exact List.Perm.nil
  | cons a t ih =>
    intro h
    show f a ++ (t.map f).flatten ~ g a ++ (t.map g).flatten
    exact List.Perm.append (h a List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

/-- `eList` 全局单射（swap 对合）。 -/
private theorem la7_eList_injective : ∀ u v : ℕ × ℕ, (u.2, u.1) = (v.2, v.1) → u = v :=
  fun u v h => by
    rw [Prod.mk.injEq] at h
    show Prod.mk u.1 u.2 = Prod.mk v.1 v.2
    rw [h.2, h.1]

theorem la7_goodList_reverse (L : fgraph ℕ) (hgood : GoodList L) :
    GoodList (L.map List.reverse) := by
  obtain ⟨hnd, hne, hswap⟩ := hgood
  refine ⟨?_, ?_, ?_⟩
  · have hperm : listOfDarts (L.map List.reverse)
        ~ (listOfDarts L).map (fun d : ℕ × ℕ => (d.2, d.1)) := by
      show ((L.map List.reverse).map listPairs).flatten
        ~ List.map (fun d : ℕ × ℕ => (d.2, d.1)) ((L.map listPairs).flatten)
      rw [List.map_map]
      show List.flatMap (listPairs ∘ List.reverse) L
        ~ List.map (fun d : ℕ × ℕ => (d.2, d.1)) (List.flatMap listPairs L)
      rw [List.map_flatMap]
      exact la7_flatMap_congr L (f := listPairs ∘ List.reverse)
        (g := fun l : List ℕ => (listPairs l).map (fun d : ℕ × ℕ => (d.2, d.1)))
        (fun l _ => la7_listPairs_reverse_perm l)
    exact (List.Perm.nodup_iff hperm).mpr
      (la7_nodup_map_on (l := listOfDarts L)
        (fun u _ v _ huv => la7_eList_injective u v huv) hnd)
  · intro l hl
    obtain ⟨m, hm, hme⟩ := List.mem_map.mp hl
    rw [← hme]
    intro hc
    exact hne m hm (List.reverse_eq_nil_iff.mp hc)
  · intro d hd
    have h1 : (d.2, d.1) ∈ listOfDarts L :=
      (la7_listOfDarts_reverse L (d.2, d.1)).mp
        (show (d.1, d.2) ∈ listOfDarts (L.map List.reverse) from hd)
    exact (la7_listOfDarts_reverse L (d.1, d.2)).mpr (hswap (d.2, d.1) h1)

theorem la7_darts_reverse (L : fgraph ℕ) (hgood : GoodList L) :
    {d : ℕ × ℕ | d ∈ listOfDarts (L.map List.reverse)}
      = {d : ℕ × ℕ | d ∈ listOfDarts L} := by
  ext d
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    exact hgood.2.2 _ ((la7_listOfDarts_reverse L (eList d)).mp h)
  · intro h
    exact (la7_listOfDarts_reverse L (d.2, d.1)).mpr (hgood.2.2 d h)

theorem la7_edgeMap_reverse (L : fgraph ℕ) (hgood : GoodList L) (d : ℕ × ℕ)
    (hd : d ∈ listOfDarts L) : eList (eList d) = d := la7_eList_involutory d

theorem la7_faceMap_reverse (L : fgraph ℕ) (hgood : GoodList L) (d : ℕ × ℕ)
    (hd : d ∈ listOfDarts L) :
    fList (L.map List.reverse) (eList d) = nList L d := by
  have hnd : (listOfDarts L).Nodup := hgood.1
  have hd' : (d.2, d.1) ∈ listOfDarts L := hgood.2.2 d hd
  have hFd : d ∈ findFaceDarts L (d.1, d.2) := la7_dart_in_findFace L d hd
  have hFF := la7_findFace_reverse L hgood d.2 d.1 hd'
  have hmem : (d.2, d.1) ∈ (findFaceDarts L (d.1, d.2)).map (fun x : ℕ × ℕ => (x.2, x.1)) :=
    List.mem_map.mpr ⟨d, hFd, rfl⟩
  have hinjF : ∀ u ∈ findFaceDarts L (d.1, d.2), ∀ v ∈ findFaceDarts L (d.1, d.2),
      (u.2, u.1) = (v.2, v.1) → u = v :=
    fun u _ v _ huv => la7_eList_injective u v huv
  have hFnodup : (findFaceDarts L (d.1, d.2)).Nodup :=
    la7_findFace_nodup L (d.1, d.2) hnd
  have hmapnodup : ((findFaceDarts L (d.1, d.2)).map (fun x : ℕ × ℕ => (x.2, x.1))).Nodup :=
    la7_nodup_map_on (l := findFaceDarts L (d.1, d.2)) hinjF hFnodup
  have hRnodup : (((findFaceDarts L (d.1, d.2)).map (fun x : ℕ × ℕ => (x.2, x.1))).reverse).Nodup :=
    List.nodup_reverse.mpr hmapnodup
  unfold fList nList
  show nextEl (findFaceDarts (L.map List.reverse) (d.2, d.1)) (d.2, d.1)
    = eList (prevEl (findFaceDarts L d) d)
  rw [hFF, la7_nextEl_rotOne hRnodup, la7_nextEl_reverse hmapnodup hmem,
    la7_prevEl_map (f := fun x : ℕ × ℕ => (x.2, x.1)) hinjF hFd]
  rfl

theorem la7_nodeMap_reverse (L : fgraph ℕ) (hgood : GoodList L) (d : ℕ × ℕ)
    (hd : d ∈ listOfDarts L) :
    nList (L.map List.reverse) (eList d) = fList L d := by
  have hnd : (listOfDarts L).Nodup := hgood.1
  have hd' : (d.2, d.1) ∈ listOfDarts L := hgood.2.2 d hd
  have hFF := la7_findFace_reverse L hgood d.2 d.1 hd'
  have hFd : d ∈ findFaceDarts L (d.1, d.2) := la7_dart_in_findFace L d hd
  have hmem : (d.2, d.1) ∈ (findFaceDarts L (d.1, d.2)).map (fun x : ℕ × ℕ => (x.2, x.1)) :=
    List.mem_map.mpr ⟨d, hFd, rfl⟩
  have hinjF : ∀ u ∈ findFaceDarts L (d.1, d.2), ∀ v ∈ findFaceDarts L (d.1, d.2),
      (u.2, u.1) = (v.2, v.1) → u = v :=
    fun u _ v _ huv => la7_eList_injective u v huv
  have hFnodup : (findFaceDarts L (d.1, d.2)).Nodup :=
    la7_findFace_nodup L (d.1, d.2) hnd
  have hmapnodup : ((findFaceDarts L (d.1, d.2)).map (fun x : ℕ × ℕ => (x.2, x.1))).Nodup :=
    la7_nodup_map_on (l := findFaceDarts L (d.1, d.2)) hinjF hFnodup
  have hRnodup : (((findFaceDarts L (d.1, d.2)).map (fun x : ℕ × ℕ => (x.2, x.1))).reverse).Nodup :=
    List.nodup_reverse.mpr hmapnodup
  unfold fList nList
  show eList (prevEl (findFaceDarts (L.map List.reverse) (d.2, d.1)) (d.2, d.1))
    = nextEl (findFaceDarts L d) d
  rw [hFF, la7_prevEl_rotOne hRnodup (List.mem_reverse.mpr hmem),
    la7_prevEl_reverse hmapnodup hmem,
    la7_nextEl_map (f := fun x : ℕ × ℕ => (x.2, x.1)) hinjF hFd]
  exact la7_eList_involutory _

theorem la7_hypermapOfList_reverse (L : fgraph ℕ) (hgood : GoodList L) :
    Set.BijOn id {d : ℕ × ℕ | d ∈ listOfDarts (L.map List.reverse)}
        {d : ℕ × ℕ | d ∈ listOfDarts L}
      ∧ ∀ d ∈ listOfDarts L,
          eList (eList d) = d
          ∧ fList (L.map List.reverse) (eList d) = nList L d
          ∧ nList (L.map List.reverse) (eList d) = fList L d := by
  refine ⟨?_, fun d hd => ⟨la7_eList_involutory d, la7_faceMap_reverse L hgood d hd,
    la7_nodeMap_reverse L hgood d hd⟩⟩
  have hA := la7_darts_reverse L hgood
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hA] at hx
    exact hx
  · intro x _ y _ h
    exact h
  · intro x hx
    refine ⟨x, ?_, rfl⟩
    rw [hA]
    exact hx

/-- tame_list.hl:3493 `hypermap_of_list_map` 的列表层 Iso（同构函数 = pair-lift）。 -/
theorem la7_hypermapOfList_map (L : fgraph ℕ) {phi : ℕ → ℕ}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, phi u = phi v → u = v)
    (hgood : GoodList L) :
    Set.BijOn (fun d : ℕ × ℕ => (phi d.1, phi d.2))
        {d : ℕ × ℕ | d ∈ listOfDarts L}
        {d : ℕ × ℕ | d ∈ listOfDarts (L.map (List.map phi))}
      ∧ ∀ d ∈ listOfDarts L,
          nList (L.map (List.map phi)) (phi d.1, phi d.2)
            = (phi (nList L d).1, phi (nList L d).2)
          ∧ fList (L.map (List.map phi)) (phi d.1, phi d.2)
            = (phi (fList L d).1, phi (fList L d).2)
          ∧ eList (phi d.1, phi d.2) = (phi (eList d).1, phi (eList d).2) := by
  refine ⟨?_, fun d hd => ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [la7_listOfDarts_map]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    · intro x hx y hy hxy
      exact la7_injOn_listOfDarts L hinj x y hx hy hxy
    · intro y hy
      simp only [Set.mem_setOf_eq] at hy
      rw [la7_listOfDarts_map, List.mem_map] at hy
      obtain ⟨c, hc, hcd⟩ := hy
      exact ⟨c, hc, hcd⟩
  · have hFF := la7_findFace_map L hinj d hd
    have hinjF : ∀ u ∈ findFaceDarts L d, ∀ v ∈ findFaceDarts L d,
        (phi u.1, phi u.2) = (phi v.1, phi v.2) → u = v :=
      fun u hu v hv huv =>
        la7_injOn_listOfDarts L hinj u v (la7_findFace_mem L d u hu)
          (la7_findFace_mem L d v hv) huv
    have hFd : d ∈ findFaceDarts L d := la7_dart_in_findFace L d hd
    refine ⟨?_, ?_, ?_⟩
    · unfold nList
      rw [hFF, la7_prevEl_map (f := fun x : ℕ × ℕ => (phi x.1, phi x.2)) hinjF hFd]
      rfl
    · unfold fList
      rw [hFF, la7_nextEl_map (f := fun x : ℕ × ℕ => (phi x.1, phi x.2)) hinjF hFd]
    · rfl

end LA7ReverseMap

/-! ## 12. Hypermap 类型层桥：IsHypermapOfListTl 规格桥 + REVERSE/MAP 类型层运输

Assembly §1b `IsHypermapOfList`（Assembly.lean:108-117；本模块不 import
`Kepler.Assembly`（环）故不可见）的 TameLp 侧**逐字段同体孪生** + §9 构造件的
规格实例定理；REVERSE 共轭束（ELLLNYZ.hl:235 `dart_REVERSE` / :254
`edge_map_reverse` / :370 `face_map_reverse` / :440 `hypermap_of_list_reverse`，
face/node 互换 = opposite_hypermap 语义，类型层取 eList-共轭形）与 MAP 类型层
Iso（tame_list.hl:3486 `hypermap_of_list_map`，同构函数 = pair-lift）。
列表层三向交换全部引 §10 `la7_*` 现成件，无新增列表层机器。 -/

section HypermapTypeBridge
open Kepler.Assembly (listOfDarts eList fList nList GoodList)
open Kepler.Graphs (fgraph)

/-- Assembly §1b `IsHypermapOfList`（Assembly.lean:108-117）的逐字段同体孪生：
dart 集恰为 `listOfDarts L` 的像集，且三映射在 dart 上与 `eList`/`nList L`/
`fList L` 一致（HOL `hypermap_of_list` 规格级镜像，list_hypermap-compiled.hl:60；
HOL 侧 `res` 的"dart 集外恒等"约定由 `Hypermap` 的 `PermutesOn` 字段内置）。
装配 lane 折算：`Assembly.IsHypermapOfList L H ↔ IsHypermapOfListTl L H`
（两结构体字段名/类型逐槽同体，匿名构造器四槽一步）。 -/
structure IsHypermapOfListTl (L : fgraph ℕ) (H : Hypermap (ℕ × ℕ)) : Prop where
  /-- `dart (hypermap_of_list L) = darts_of_list L`（list_hypermap-compiled.hl:22,60）。 -/
  darts_eq : (↑H.darts : Set (ℕ × ℕ)) = {d | d ∈ listOfDarts L}
  /-- `edge_map` 在 dart 上 = `e_list`（:54,57,60）。 -/
  edgeMap_eq : ∀ d ∈ H.darts, H.edgeMap d = eList d
  /-- `node_map` 在 dart 上 = `n_list`（:55,58,60）。 -/
  nodeMap_eq : ∀ d ∈ H.darts, H.nodeMap d = nList L d
  /-- `face_map` 在 dart 上 = `f_list`（:53,56,60）。 -/
  faceMap_eq : ∀ d ∈ H.darts, H.faceMap d = fList L d

/-- 规格实例定理（Assembly 侧待证件 `IsHypermapOfList L (hypermapOfList L)` 的
TameLp 侧构造件）：§9 构造逐字段满足规格桥——四槽 = §9 四定理直接组装
（`comp_eq_one` 由 `Hypermap` 打包字段承载，无需在此重述）。 -/
theorem hypermapOfList_isHypermapOfListTl (L : fgraph ℕ) (hL : GoodList L) :
    IsHypermapOfListTl L (hypermapOfList L hL) :=
  ⟨darts_hypermapOfList L hL, fun _ hd => edgeMap_hypermapOfList L hL hd,
    fun _ hd => nodeMap_hypermapOfList L hL hd, fun _ hd => faceMap_hypermapOfList L hL hd⟩

/-! ### REVERSE 类型层共轭束（ELLLNYZ.hl:235/254/370/440） -/

/-- HOL `dart_REVERSE`（ELLLNYZ.hl:235）的类型层折算：REVERSE 后构造的超映射
与原构造有同一 dart 集。 -/
theorem darts_hypermapOfList_reverse (L : fgraph ℕ) (hgood : GoodList L) :
    (↑(hypermapOfList (L.map List.reverse) (la7_goodList_reverse L hgood)).darts :
        Set (ℕ × ℕ))
      = (↑(hypermapOfList L hgood).darts : Set (ℕ × ℕ)) := by
  rw [darts_hypermapOfList, darts_hypermapOfList]
  exact la7_darts_reverse L hgood

/-- REVERSE 侧 dart 集成员转移（dart 集相等 + `GoodList` 交换性；eList 自逆
使 eList d 回落原 dart 集）。 -/
theorem mem_darts_hypermapOfList_reverse (L : fgraph ℕ) (hgood : GoodList L)
    {d : ℕ × ℕ} (hd : d ∈ (hypermapOfList L hgood).darts) :
    eList d ∈ (hypermapOfList (L.map List.reverse) (la7_goodList_reverse L hgood)).darts := by
  have hdL : d ∈ listOfDarts L := by
    have h5 : d ∈ (↑(hypermapOfList L hgood).darts : Set (ℕ × ℕ)) := hd
    rw [darts_hypermapOfList] at h5
    exact h5
  have h : (eList d : ℕ × ℕ) ∈
      (↑(hypermapOfList (L.map List.reverse) (la7_goodList_reverse L hgood)).darts :
        Set (ℕ × ℕ)) := by
    rw [darts_hypermapOfList_reverse L hgood, darts_hypermapOfList L hgood]
    exact hgood.2.2 d hdL
  exact h

/-- HOL `edge_map_reverse`（ELLLNYZ.hl:254）的 eList-共轭形：
`edge_map L' (e_list d) = e_list (edge_map L d)`（两边同为 `d`，由单对换自逆）。 -/
theorem edgeMap_hypermapOfList_reverse (L : fgraph ℕ) (hgood : GoodList L)
    {d : ℕ × ℕ} (hd : d ∈ (hypermapOfList L hgood).darts) :
    (hypermapOfList (L.map List.reverse) (la7_goodList_reverse L hgood)).edgeMap (eList d)
      = eList ((hypermapOfList L hgood).edgeMap d) := by
  have hmem := mem_darts_hypermapOfList_reverse L hgood hd
  rw [edgeMap_hypermapOfList (L.map List.reverse) (la7_goodList_reverse L hgood) hmem,
    edgeMap_hypermapOfList L hgood hd]

/-- HOL `face_map_reverse`（ELLLNYZ.hl:370；`hypermap_of_list_reverse` 的
opposite_hypermap 语义）的类型层形：REVERSE 侧 faceMap 与原侧 nodeMap 经
eList 互换。 -/
theorem faceMap_hypermapOfList_reverse (L : fgraph ℕ) (hgood : GoodList L)
    {d : ℕ × ℕ} (hd : d ∈ (hypermapOfList L hgood).darts) :
    (hypermapOfList (L.map List.reverse) (la7_goodList_reverse L hgood)).faceMap (eList d)
      = (hypermapOfList L hgood).nodeMap d := by
  have hmem := mem_darts_hypermapOfList_reverse L hgood hd
  have hdL : d ∈ listOfDarts L := by
    have h4 : d ∈ (↑(hypermapOfList L hgood).darts : Set (ℕ × ℕ)) := hd
    rw [darts_hypermapOfList] at h4
    exact h4
  rw [faceMap_hypermapOfList (L.map List.reverse) (la7_goodList_reverse L hgood) hmem,
    la7_faceMap_reverse L hgood d hdL]
  exact (nodeMap_hypermapOfList L hgood hd).symm

/-- HOL `face_map_reverse` 的对偶（nodeMap 侧，REVERSE 共轭的 node/face 互换
另一半，la7_nodeMap_reverse = tame_list 列表层件）。 -/
theorem nodeMap_hypermapOfList_reverse (L : fgraph ℕ) (hgood : GoodList L)
    {d : ℕ × ℕ} (hd : d ∈ (hypermapOfList L hgood).darts) :
    (hypermapOfList (L.map List.reverse) (la7_goodList_reverse L hgood)).nodeMap (eList d)
      = (hypermapOfList L hgood).faceMap d := by
  have hmem := mem_darts_hypermapOfList_reverse L hgood hd
  have hdL : d ∈ listOfDarts L := by
    have h4 : d ∈ (↑(hypermapOfList L hgood).darts : Set (ℕ × ℕ)) := hd
    rw [darts_hypermapOfList] at h4
    exact h4
  rw [nodeMap_hypermapOfList (L.map List.reverse) (la7_goodList_reverse L hgood) hmem,
    la7_nodeMap_reverse L hgood d hdL]
  exact (faceMap_hypermapOfList L hgood hd).symm

/-! ### MAP 类型层 Iso（tame_list.hl:3486 `hypermap_of_list_map`） -/

/-- HOL `hypermap_of_list_map`（tame_list.hl:3486-3488）的 Hypermap 类型层落地：
`iso (hypermap_of_list L) (hypermap_of_list (MAP (MAP phi) L))`，同构函数 =
pair-lift `\d. phi (FST d), phi (SND d)`；injectivity 形状 = `∀ u ∈ L.flatten`
（= HOL `inj_on phi (elements_of_list L)` 的折算）。 -/
theorem hypermapOfList_iso_map (L : fgraph ℕ) {phi : ℕ → ℕ}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, phi u = phi v → u = v)
    (hgood : GoodList L) :
    Hypermap.Iso (hypermapOfList L hgood)
      (hypermapOfList (L.map (List.map phi)) (la7_mapGoodList L hinj hgood)) := by
  have hbij := (la7_hypermapOfList_map L hinj hgood).1
  have hmaps := (la7_hypermapOfList_map L hinj hgood).2
  have hbij' : Set.BijOn (fun d : ℕ × ℕ => (phi d.1, phi d.2))
      (↑(hypermapOfList L hgood).darts : Set (ℕ × ℕ))
      (↑(hypermapOfList (L.map (List.map phi)) (la7_mapGoodList L hinj hgood)).darts :
        Set (ℕ × ℕ)) := by
    rw [darts_hypermapOfList L hgood,
      darts_hypermapOfList (L.map (List.map phi)) (la7_mapGoodList L hinj hgood)]
    exact hbij
  refine ⟨fun d => (phi d.1, phi d.2), hbij', ?_⟩
  intro d hd
  have hd2 : (phi d.1, phi d.2) ∈
      (hypermapOfList (L.map (List.map phi)) (la7_mapGoodList L hinj hgood)).darts :=
    hbij'.1 hd
  have hds : d ∈ ({e : ℕ × ℕ | e ∈ listOfDarts L} : Set (ℕ × ℕ)) := by
    have h4 : d ∈ (↑(hypermapOfList L hgood).darts : Set (ℕ × ℕ)) := hd
    rw [darts_hypermapOfList] at h4
    exact h4
  obtain ⟨hn, hf, he⟩ := hmaps d hds
  refine ⟨?_, ?_, ?_⟩
  · show (hypermapOfList (L.map (List.map phi)) (la7_mapGoodList L hinj hgood)).edgeMap
        (phi d.1, phi d.2)
      = (phi ((hypermapOfList L hgood).edgeMap d).1,
          phi ((hypermapOfList L hgood).edgeMap d).2)
    rw [edgeMap_hypermapOfList (L.map (List.map phi)) (la7_mapGoodList L hinj hgood) hd2,
      edgeMap_hypermapOfList L hgood hd]
    exact he
  · show (hypermapOfList (L.map (List.map phi)) (la7_mapGoodList L hinj hgood)).nodeMap
        (phi d.1, phi d.2)
      = (phi ((hypermapOfList L hgood).nodeMap d).1,
          phi ((hypermapOfList L hgood).nodeMap d).2)
    rw [nodeMap_hypermapOfList (L.map (List.map phi)) (la7_mapGoodList L hinj hgood) hd2,
      nodeMap_hypermapOfList L hgood hd]
    exact hn
  · show (hypermapOfList (L.map (List.map phi)) (la7_mapGoodList L hinj hgood)).faceMap
        (phi d.1, phi d.2)
      = (phi ((hypermapOfList L hgood).faceMap d).1,
          phi ((hypermapOfList L hgood).faceMap d).2)
    rw [faceMap_hypermapOfList (L.map (List.map phi)) (la7_mapGoodList L hinj hgood) hd2,
      faceMap_hypermapOfList L hgood hd]
    exact hf

end HypermapTypeBridge

/-! ## 9. MQMSMAB 装配章（tame/ssreflect/MQMSMAB-compiled.hl，HOL `Mqmsmab.MQMSMAB`
= `contravening V → tame_planar_hypermap (hypermap_of_fan (V,ESTD V))`）。
Lean 折算为 `hypermapOfFanTl` 版帽石 `MQMSMAB`（§0b 重标转移已备，Assembly 侧
`mqmsmab` 消费时经 §0b congr 家族换实例）。结构五段对照（HOL 步 1-46）：
步 1-14 十二合取逐项（`contravening_lp_fan` + JGTDEBU1-8/10/11 + SZIPOAS +
BDJYFFB1 + `CRTTXAT (JGTDEBU4 contrV) (fully_surrounded_perimeter_bound …)`
收 tame_9a——本章 CRTTXAT 消费点）；步 15-20 tame_13a 权重
（`sum_tauVEF_upper_bound` + Flyspeck 常数算术 4π−20sol0 < tgt）；步 21-41
adm_1（3≤card≤6 枚举 × `ineq_tauK_tauVEF_std`×4，JEJTVGB 前提由 `hmain` 分量
直接供给）；步 42-47 adm_2（`KCBLRQC` r=0 分支）；步 48-55 adm_3（`BDJYFFB2`
+ EXTENSION 集合等换元）。上游 5 枚外部锚占位件（fully_surrounded_perimeter_bound /
sum_tauVEF_upper_bound / ineq_tauK×4）以「消费含占位前提定理」形式流动，
本节零新增占位行。 -/

/-! ### 9a. Flyspeck 常数算术种子（步 18：`Flyspeck_constants.bounds` + arith_tac）。
全树无可见的 sol0 下界件（`LocalAuto19.sol0Bounds_p19` 自身 NEEDS 双占位且
模块不在本文件可见闭包），此处以件⑤ Taylor 机自证够用的弱化版 `0.55127 < sol0`：
`arccos(1/3) ≥ 1.2309544` 经半角恒等式 + `taylor_cos_lo` 认证（0.6154772 = 半角，
六阶 Taylor 余项 ≈ 5.1e-7 ≪ 有理余量 5.2e-7 量级安全），配 `Real.pi_lt_d6`
（π < 3.141593）收 `4π − 20·sol0 < 1.541 = tgt`。 -/

/-- 半角数值种子：`0.816497 ≤ cos 0.6154772`（六阶 Taylor 下界 + 有理收口；
0.6154772 = 1.2309544 的半角）。 -/
private theorem cos_6154772_ge : (816497 / 10 ^ 6 : ℝ) ≤ Real.cos (6154772 / 10 ^ 7) := by
  have hlo := taylor_cos_lo (6154772 / 10 ^ 7) (by norm_num) (by norm_num)
  have h2 : (816497 / 10 ^ 6 : ℝ) ≤ 1 - (6154772 / 10 ^ 7 : ℝ) * (6154772 / 10 ^ 7) / 2
      + (6154772 / 10 ^ 7) * (6154772 / 10 ^ 7) * (6154772 / 10 ^ 7)
        * (6154772 / 10 ^ 7) / 24
      - (6154772 / 10 ^ 7) * (6154772 / 10 ^ 7) * (6154772 / 10 ^ 7)
        * (6154772 / 10 ^ 7) * (6154772 / 10 ^ 7) * (6154772 / 10 ^ 7) / 720 := by
    norm_num
  exact le_trans h2 hlo

/-- 数值：`1/3 ≤ cos 1.2309544`（半角倍角恒等式 + 上条；倍角界
2·(816497/10⁶)² − 1 = 0.66666812… ≥ 1/3 余量充足）。 -/
private theorem cos_12309544_ge_third : (1 / 3 : ℝ) ≤ Real.cos (12309544 / 10 ^ 7) := by
  have hhalf := cos_6154772_ge
  have hsq : (816497 / 10 ^ 6 : ℝ) ^ 2 ≤ Real.cos (6154772 / 10 ^ 7) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hhalf 2
  have h2t : (2 : ℝ) * (6154772 / 10 ^ 7) = 12309544 / 10 ^ 7 := by norm_num
  rw [← h2t, Real.cos_two_mul (6154772 / 10 ^ 7)]
  have hr : (1 / 3 + 1 : ℝ) ≤ 2 * (816497 / 10 ^ 6 : ℝ) ^ 2 := by norm_num
  linarith [hsq, hr]

/-- 数值：`arccos(1/3) ≥ 1.2309544`（cos antitone；1.2309544 < π 经
`Real.pi_gt_d4`）。 -/
private theorem arccos_one_third_ge_12309544 :
    (12309544 / 10 ^ 7 : ℝ) ≤ Real.arccos (1 / 3) := by
  have hc := cos_12309544_ge_third
  have hmem : 12309544 / 10 ^ 7 ≤ Real.pi := by linarith [Real.pi_gt_d4]
  rw [← Real.arccos_cos (by norm_num) hmem]
  exact Real.arccos_le_arccos hc

/-- Flyspeck 常数算术（`Flyspeck_constants.bounds` 弱化消费版）：`0.55127 < sol0`。
（HOL 原件用 `0.551285 < sol0`；0.55127 已足收口 4π−20sol0 < tgt，
诚实例化注记：下游如需 0.551285 需六阶以上 Taylor。） -/
private theorem sol0_gt_55127 : (0.55127 : ℝ) < sol0 := by
  have hA := arccos_one_third_ge_12309544
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hdef : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  linarith

/-- Flyspeck 常数算术（MQMSMAB 步 18 `Flyspeck_constants.bounds` + arith_tac 的
Lean 落地）：`4π − 20·sol0 < tgt`。 -/
theorem four_pi_sub_20_sol0_lt_tgt : 4 * Real.pi - 20 * sol0 < tgt := by
  have h1 := sol0_gt_55127
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have h3 : tgt = 1.541 := rfl
  linarith

/-! ### 9b. adm_1 / adm_2 / adm_3 三分量（步 21-55）. -/

/-- MQMSMAB 步 53-55（EXTENSION 集合等换元）：限定子集
`{f ∈ set_of_face_meeting_node H d | card f = 3}` 与
`set_of_triangles_meeting_node H d` 是同一个集合，setSum 相等。
（本引理对任意 `Hypermap α` 成立，供 `MQMSMAB_adm3` 与 Assembly 侧复用。） -/
theorem setSum_setOfTrianglesMeetingNode_eq {α : Type*} [DecidableEq α]
    (H : Hypermap α) (d : α) (w : Set α → ℝ) :
    setSum {f | f ∈ setOfFaceMeetingNode H d ∧ f.ncard = 3} w
      = setSum (setOfTrianglesMeetingNode H d) w := by
  have hset : {f : Set α | f ∈ setOfFaceMeetingNode H d ∧ f.ncard = 3}
      = setOfTrianglesMeetingNode H d := by
    ext F
    simp only [setOfFaceMeetingNode, setOfTrianglesMeetingNode, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨y, hy, rfl, hyn⟩, hcard⟩
      exact ⟨y, hy, rfl, hcard, hyn⟩
    · rintro ⟨y, hy, rfl, hcard, hyn⟩
      exact ⟨⟨y, hy, rfl, hyn⟩, hcard⟩
  rw [hset]


/-- MQMSMAB 步 42-47（adm_2 的 r=0 分支）：`set_of_exceptional_meeting_node`
基数为零时引 `KCBLRQC`（let-形以 defeq 断言展开消费），`0 < r` 支与 r=0
矛盾，取 `bTame` 支即得。 -/
theorem MQMSMAB_adm2 (V : Set V3) (hc : Contravening V) (hlpfan : LpFan V (ESTD V))
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef) :
    Adm2 (hypermapOfFanTl V (ESTD V) hlpfan.1) (fun f => tauVEF_p2 V (ESTD V) f) := by
  intro d hd hr0
  have hdc : d ∈ dartOfFan V (ESTD V) := Set.mem_union_right _ (dartsTl_mem hd)
  have hk : (0 : ℕ) < (typeOfNode (hypermapOfFanTl V (ESTD V) hlpfan.1) d).2.2 ∨
      bTame (typeOfNode (hypermapOfFanTl V (ESTD V) hlpfan.1) d).1
          (typeOfNode (hypermapOfFanTl V (ESTD V) hlpfan.1) d).2.1 ≤
        setSum (setOfFaceMeetingNode (hypermapOfFanTl V (ESTD V) hlpfan.1) d)
          (fun f => tauVEF_p2 V (ESTD V) f) :=
    KCBLRQC V hc hmain hineq hlpfan.1 d hdc
  rcases hk with h0 | hge
  · exfalso
    have hproj : (typeOfNode (hypermapOfFanTl V (ESTD V) hlpfan.1) d).2.2
        = (setOfExceptionalMeetingNode
            (hypermapOfFanTl V (ESTD V) hlpfan.1) d).ncard := rfl
    omega
  · exact hge

/-- MQMSMAB 步 48-55（adm_3）：type = (5,0,1) 时引 `BDJYFFB2`（严格版
`aTame < …`），经 `setSum_setOfTrianglesMeetingNode_eq` 换元收 `≤`。 -/
theorem MQMSMAB_adm3 (V : Set V3) (hc : Contravening V) (hlpfan : LpFan V (ESTD V))
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef) :
    Adm3 (hypermapOfFanTl V (ESTD V) hlpfan.1) (fun f => tauVEF_p2 V (ESTD V) f) := by
  intro d hd htype
  have hdc : d ∈ dartOfFan V (ESTD V) := Set.mem_union_right _ (dartsTl_mem hd)
  have h := BDJYFFB2 V hc hmain hineq hlpfan.1 d hdc htype
  rw [← setSum_setOfTrianglesMeetingNode_eq]
  exact le_of_lt h


/-! ## 9. y-kit 定义层（lp_ineqs_proofs Fan 节 Dart/DartMore/StdDart/Nonlinear-Y
小节 + lp_ineqs_defs.hl y_fan 定义族；2026-10-23 Lane N W1）

HOL 锚点：lp_ineqs_defs.hl:16-23,34（y1..y9_fan、y4'_fan 定义）、
lp_ineqs_proofs-compiled.hl:1296-1475（Dart 节 y1/y2/y6 界 + fd_in/ifd_in）、
:1478-1509（Dart3）、:1533-1651（StdDart/Inner = std2 族）、:1654-1881（DartMore
y3/y4/y5 界）、:2184-2259（Nonlinear-Y：ys_eq/ys_eq_alt）、
INVERSE_F_FAN_PAIR_EXT_EXPLICIT（fan/hypermap_and_fan.hl:519）。

编码偏差注记：HOL y-kit 各节以 `d IN dart_of_fan (V,E)` 为节前提，再经
`dart1_eq`（FullySurrounded ⟹ dart1 = dart，lp_ineqs_proofs:1178）折算到 dart1
上使用；Lean 侧 `hypermapOfFanTl` 的 dart 集按构造即 `dart1OfFan`
（COMPONENTS_HYPERMAP_OF_FAN 偏差注记，§2），四目标 `darts_k` 消费亦在 dart1
上，故本节各件一律取 `d ∈ dart1OfFan V E` 为前提（省去 dart1_eq 折算；
`yk_dart1_eq` 单独保留 FullySurrounded 桥供 W2 的 f_surr 链使用）。
`dist` 对偶：HOL 二元组距离 `dist (v,w) = ‖v−w‖` 折算为 Lean `dist d.1 d.2`
（§7 arc kit 同约定，非 Prod 上确界度量）。-/

/-! ### 9a. y_fan 定义族（lp_ineqs_defs.hl:16-23,34 逐字镜像） -/

/-- HOL `y1_fan`（lp_ineqs_defs.hl:16）：dart 第一分量范数。 -/
noncomputable def y1Fan (d : V3 × V3) : ℝ := ‖d.1‖

/-- HOL `y2_fan`（lp_ineqs_defs.hl:17）：dart 第二分量范数。 -/
noncomputable def y2Fan (d : V3 × V3) : ℝ := ‖d.2‖

/-- HOL `y3_fan`（lp_ineqs_defs.hl:18）：`inverse f` 第一分量范数
（apex 0 烤定，同 lp_ineqs 无参形）。 -/
noncomputable def y3Fan (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) : ℝ :=
  ‖(Function.invFun (fFanPairExt 0 V E) d).1‖

/-- HOL `y4_fan`（lp_ineqs_defs.hl:19）：`f d` 的二元组距离。 -/
noncomputable def y4Fan (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) : ℝ :=
  dist (fFanPairExt 0 V E d).1 (fFanPairExt 0 V E d).2

/-- HOL `y5_fan`（lp_ineqs_defs.hl:20）：`inverse f d` 的二元组距离。 -/
noncomputable def y5Fan (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) : ℝ :=
  dist (Function.invFun (fFanPairExt 0 V E) d).1
    (Function.invFun (fFanPairExt 0 V E) d).2

/-- HOL `y6_fan`（lp_ineqs_defs.hl:21）：dart 二元组距离。 -/
noncomputable def y6Fan (d : V3 × V3) : ℝ := dist d.1 d.2

/-- HOL `y4'_fan`（lp_ineqs_defs.hl:34）：`dist (SND x, FST (inverse f x))`。 -/
noncomputable def y4pFan (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) : ℝ :=
  dist d.2 (Function.invFun (fFanPairExt 0 V E) d).1

/-- HOL `y8_fan`（lp_ineqs_defs.hl:22）：`y5_fan (inverse f x)`。 -/
noncomputable def y8Fan (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) : ℝ :=
  y5Fan V E (Function.invFun (fFanPairExt 0 V E) d)

/-- HOL `y9_fan`（lp_ineqs_defs.hl:23）：`dist (f d)`（与 y4_fan 逐字同式，
HOL 保留双名，此处忠实镜像）。 -/
noncomputable def y9Fan (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) : ℝ :=
  dist (fFanPairExt 0 V E d).1 (fFanPairExt 0 V E d).2

/-! ### 9b. 逆映射显式形（INVERSE_F_FAN_PAIR_EXT_EXPLICIT 折算） -/

/-- HOL `INVERSE_F_FAN_PAIR_EXT_EXPLICIT`（hypermap_and_fan.hl:519）的逐点形：
`f_fan_pair_ext` 的函数逆在 dart1 上 = `(σ_v w, v)`，在 dart1 外 = 恒等
（HOL 全函数等式 `inverse (f_fan_pair_ext (V,E)) =
res ((v,w). σ_(vec 0) v w, v) (dart1_of_fan (V,E))` 的 funext 拆开形；
Lean `Function.invFun` 即 HOL `inverse`）。 -/
theorem yk_invFunFFanPairExt_apply (hfan : FAN 0 V E) (d : V3 × V3) :
    Function.invFun (fFanPairExt 0 V E) d =
      if d ∈ dart1OfFan V E then (sigmaFan 0 V E d.1 d.2, d.1) else d := by
  have hfg : ∀ e : V3 × V3, fFanPairExt 0 V E
        (if e ∈ dart1OfFan V E then (sigmaFan 0 V E e.1 e.2, e.1) else e) = e := by
    intro e
    by_cases he : e ∈ dart1OfFan V E
    · rw [if_pos he]
      -- (σ e.1 e.2, e.1) ∈ dart1，且 f 作用其上回到 e
      have hmemV := FAN_in_setOfEdge 0 V E e.1 e.2 hfan he
      have hsoe : e.2 ∈ setOfEdge e.1 V E := hmemV.2.2.1
      have hs : sigmaFan 0 V E e.1 e.2 ∈ setOfEdge e.1 V E :=
        sigma_fan_in_setOfEdge hfan hsoe
      have hge1 : (sigmaFan 0 V E e.1 e.2, e.1) ∈ dart1OfFan V E := by
        have h := (properties_of_setOfEdge_fan 0 V E e.1
          (sigmaFan 0 V E e.1 e.2) hfan).mpr hs
        rwa [Set.pair_comm] at h
      have hfe : fFanPairExt 0 V E (sigmaFan 0 V E e.1 e.2, e.1)
          = fFanPair 0 V E (sigmaFan 0 V E e.1 e.2, e.1) := by
        simp only [fFanPairExt]
        exact if_pos hge1
      have hinv : inverseSigmaFan 0 V E e.1 (sigmaFan 0 V E e.1 e.2) = e.2 := by
        have hcomp := (inverse_sigma_fan_comp hfan hsoe).1
        have hext : extensionSigmaFan 0 V E e.1 e.2 = sigmaFan 0 V E e.1 e.2 := by
          simp only [extensionSigmaFan, if_neg (not_not.mpr hsoe)]
        rw [← hext]
        exact congrFun hcomp e.2
      show fFanPairExt 0 V E (sigmaFan 0 V E e.1 e.2, e.1) = e
      rw [hfe]
      show (e.1, inverseSigmaFan 0 V E e.1 (sigmaFan 0 V E e.1 e.2)) = e
      rw [hinv]
    · rw [if_neg he]
      have hfe : fFanPairExt 0 V E e = e := by
        simp only [fFanPairExt, if_neg he]
      rw [hfe]
  have hgf : ∀ e : V3 × V3,
      (if fFanPairExt 0 V E e ∈ dart1OfFan V E
        then (sigmaFan 0 V E (fFanPairExt 0 V E e).1 (fFanPairExt 0 V E e).2,
          (fFanPairExt 0 V E e).1)
        else fFanPairExt 0 V E e) = e := by
    intro e
    by_cases he : e ∈ dart1OfFan V E
    · have hfe : fFanPairExt 0 V E e = (e.2, inverseSigmaFan 0 V E e.2 e.1) := by
        simp only [fFanPairExt, if_pos he]
        rfl
      have hfp : fFanPair 0 V E e = (e.2, inverseSigmaFan 0 V E e.2 e.1) := rfl
      have hf1 : (e.2, inverseSigmaFan 0 V E e.2 e.1) ∈ dart1OfFan V E := by
        rw [← hfp]
        exact fFanPair_mem_dart1 hfan he
      have hσ : sigmaFan 0 V E e.2 (inverseSigmaFan 0 V E e.2 e.1) = e.1 :=
        (inverseSigmaFan_eq hfan (FAN_in_setOfEdge 0 V E e.1 e.2 hfan he).2.2.2
          rfl).2
      rw [hfe, if_pos hf1]
      show (sigmaFan 0 V E e.2 (inverseSigmaFan 0 V E e.2 e.1), e.2) = e
      rw [hσ]
    · have hfe : fFanPairExt 0 V E e = e := by
        simp only [fFanPairExt, if_neg he]
      rw [hfe, if_neg he]
  have hfq : fFanPairExt 0 V E (Function.invFun (fFanPairExt 0 V E) d) = d :=
    Function.invFun_eq
      ⟨if d ∈ dart1OfFan V E then (sigmaFan 0 V E d.1 d.2, d.1) else d, hfg d⟩
  have hinj : Function.Injective (fFanPairExt 0 V E) :=
    Function.LeftInverse.injective
      (g := fun e =>
        if e ∈ dart1OfFan V E then (sigmaFan 0 V E e.1 e.2, e.1) else e)
      hgf
  apply hinj
  rw [hfq]
  exact (hfg d).symm

/-- HOL `fd_in`（lp_ineqs_proofs:1511，dart1 折算形）：dart1 在
`f_fan_pair_ext` 下封闭（Fan.lean `fFanPair_mem_dart1` 的 ext 版）。 -/
theorem yk_fd_in (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    fFanPairExt 0 V E d ∈ dart1OfFan V E := by
  rw [show fFanPairExt 0 V E d = fFanPair 0 V E d from by
    simp only [fFanPairExt, if_pos hd]]
  exact fFanPair_mem_dart1 hfan hd

/-- HOL `ifd_in`（lp_ineqs_proofs:1518，dart1 折算形）：dart1 在函数逆下封闭
（逆在 dart1 上 = `(σ_v w, v)`，仍为 dart1）。 -/
theorem yk_ifd_in (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    Function.invFun (fFanPairExt 0 V E) d ∈ dart1OfFan V E := by
  rw [yk_invFunFFanPairExt_apply hfan d, if_pos hd]
  have hmemV := FAN_in_setOfEdge 0 V E d.1 d.2 hfan hd
  have hs : sigmaFan 0 V E d.1 d.2 ∈ setOfEdge d.1 V E :=
    sigma_fan_in_setOfEdge hfan hmemV.2.2.1
  have h := (properties_of_setOfEdge_fan 0 V E d.1
    (sigmaFan 0 V E d.1 d.2) hfan).mpr hs
  rwa [Set.pair_comm] at h

/-- dart 的两个分量都在 V 中（HOL `in_dart_inV`/`PAIR_IN_DART_OF_FAN`，
dart1 折算形；fst 侧同 §2c `dartOfFan_fst_mem`）。 -/
theorem yk_in_dart_inV (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    d.1 ∈ V ∧ d.2 ∈ V :=
  ⟨(FAN_in_setOfEdge 0 V E d.1 d.2 hfan hd).1,
    (FAN_in_setOfEdge 0 V E d.1 d.2 hfan hd).2.1⟩

/-! ### 9c. 支撑估计（norm_v / dart1_eq / pack_dist / in_std） -/

/-- HOL `norm_v`（lp_ineqs_proofs:1204）：V 中向量范数 ∈ [2, 2h0]。 -/
theorem yk_norm_v (hsub : V ⊆ ballAnnulus) {v : V3} (hv : v ∈ V) :
    (2 : ℝ) ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * h0 := by
  have hmem : v ∈ ballAnnulus := hsub hv
  have hlow := two_le_norm_of_mem_ballAnnulus hmem
  simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball] at hmem
  have h2 : dist v 0 = ‖v‖ := by rw [dist_eq_norm, sub_zero]
  refine ⟨hlow, ?_⟩
  rw [← h2]
  exact hmem.1

/-- HOL `dart1_eq`（lp_ineqs_proofs:1178 的 FullySurrounded 形，经
add_triangle-compiled.hl:207 `fully_surrounded_dart_of_fan_eq`）：
FullySurrounded 下无孤立点。 -/
theorem yk_dart1_eq (hfan : FAN 0 V E) (hfs : FullySurrounded V E) :
    dartOfFan V E = dart1OfFan V E := by
  refine dartOfFan_eq_dart1_of_surrounded hfan (fun v hv => ?_)
  have h := SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hv
    (fun d hd _ => hfs d hd)
  omega

/-- HOL `pack_dist`（lp_ineqs_proofs:1219，dart1 折算形）：dart1 对的二元组
距离 ≥ 2（packing 下界，经 `edge_ne_of_fan` + `Packing.dist_ge_two`）。 -/
theorem yk_pack_dist (hfan : FAN 0 V E) (hpack : Packing V) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : 2 ≤ dist d.1 d.2 := by
  have hmem := FAN_in_setOfEdge 0 V E d.1 d.2 hfan hd
  exact Packing.dist_ge_two hpack hmem.1 hmem.2.1 (edge_ne_of_fan hfan hd)

/-- HOL `in_std`（lp_ineqs_proofs:1539，dart1 折算形）：E = ESTD V 时 dart
二元组距离 ≤ 2h0（= 2.52）且 ≤ 3（`IN_ESTD` 的 dist ≤ 2h0 + 算术）。 -/
theorem yk_in_std (hE : E = ESTD V) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    dist d.1 d.2 ≤ 2 * h0 ∧ dist d.1 d.2 ≤ 3 := by
  rw [hE] at hd
  obtain ⟨v, w, he, -, -, -, hle⟩ := hd
  have h23 : (2 : ℝ) * h0 ≤ 3 := by norm_num [h0]
  rcases Set.pair_eq_pair_iff.mp he with h | h
  · rw [h.1, h.2]
    exact ⟨hle, le_trans hle h23⟩
  · rw [h.1, h.2, dist_comm]
    exact ⟨hle, le_trans hle h23⟩

/-! ### 9d. y 界（Dart 节 :1421-1456 + DartMore 节 :1715-1743 +
StdDart/Inner 节 :1550-1630） -/

/-- HOL `y1_lo`（lp_ineqs_proofs:1421）。 -/
theorem y1_lo (hfan : FAN 0 V E) (hsub : V ⊆ ballAnnulus) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : (2 : ℝ) ≤ y1Fan d :=
  (yk_norm_v hsub (yk_in_dart_inV hfan hd).1).1

/-- HOL `y1_hi`（lp_ineqs_proofs:1435）。 -/
theorem y1_hi (hfan : FAN 0 V E) (hsub : V ⊆ ballAnnulus) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : y1Fan d ≤ 2 * h0 :=
  (yk_norm_v hsub (yk_in_dart_inV hfan hd).1).2

/-- HOL `y2_lo`（lp_ineqs_proofs:1428）。 -/
theorem y2_lo (hfan : FAN 0 V E) (hsub : V ⊆ ballAnnulus) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : (2 : ℝ) ≤ y2Fan d :=
  (yk_norm_v hsub (yk_in_dart_inV hfan hd).2).1

/-- HOL `y2_hi`（lp_ineqs_proofs:1442）。 -/
theorem y2_hi (hfan : FAN 0 V E) (hsub : V ⊆ ballAnnulus) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : y2Fan d ≤ 2 * h0 :=
  (yk_norm_v hsub (yk_in_dart_inV hfan hd).2).2

/-- HOL `y6_lo`（lp_ineqs_proofs:1449）。 -/
theorem y6_lo (hfan : FAN 0 V E) (hpack : Packing V) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : (2 : ℝ) ≤ y6Fan d :=
  yk_pack_dist hfan hpack hd

/-- HOL `y3_lo`（lp_ineqs_proofs:1715）：经 `ifd_in` + `in_dart_inV` +
`norm_v`。 -/
theorem y3_lo (hfan : FAN 0 V E) (hsub : V ⊆ ballAnnulus) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : (2 : ℝ) ≤ y3Fan V E d :=
  (yk_norm_v hsub (yk_in_dart_inV hfan (yk_ifd_in hfan hd)).1).1

/-- HOL `y3_hi`（lp_ineqs_proofs:1722）。 -/
theorem y3_hi (hfan : FAN 0 V E) (hsub : V ⊆ ballAnnulus) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : y3Fan V E d ≤ 2 * h0 :=
  (yk_norm_v hsub (yk_in_dart_inV hfan (yk_ifd_in hfan hd)).1).2

/-- HOL `y4_lo`（lp_ineqs_proofs:1729）：经 `fd_in` + `pack_dist`。 -/
theorem y4_lo (hfan : FAN 0 V E) (hpack : Packing V) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : (2 : ℝ) ≤ y4Fan V E d :=
  yk_pack_dist hfan hpack (yk_fd_in hfan hd)

/-- HOL `y5_lo`（lp_ineqs_proofs:1736）：经 `ifd_in` + `pack_dist`。 -/
theorem y5_lo (hfan : FAN 0 V E) (hpack : Packing V) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : (2 : ℝ) ≤ y5Fan V E d :=
  yk_pack_dist hfan hpack (yk_ifd_in hfan hd)

/-- HOL `y4_hi_std`（lp_ineqs_proofs:1556）：E = ESTD V 时 y4 ≤ 3。 -/
theorem y4_hi_std (hfan : FAN 0 V E) (hE : E = ESTD V) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : y4Fan V E d ≤ 3 :=
  (yk_in_std hE (yk_fd_in hfan hd)).2

/-- HOL `y5_hi_std`（lp_ineqs_proofs:1563）。 -/
theorem y5_hi_std (hfan : FAN 0 V E) (hE : E = ESTD V) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : y5Fan V E d ≤ 3 :=
  (yk_in_std hE (yk_ifd_in hfan hd)).2

/-- HOL `y6_hi_std`（lp_ineqs_proofs:1570）。 -/
theorem y6_hi_std (hE : E = ESTD V) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    y6Fan d ≤ 3 :=
  (yk_in_std hE hd).2

/-- HOL `y8_hi_std`（lp_ineqs_proofs:1578）：y8 = y5∘inv f ≤ 2h0
（`ifd_in` 两次 + `in_std`）。 -/
theorem y8_hi_std (hfan : FAN 0 V E) (hE : E = ESTD V) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : y8Fan V E d ≤ 2 * h0 :=
  (yk_in_std hE (yk_ifd_in hfan (yk_ifd_in hfan hd))).1

/-- HOL `y9_hi_std`（lp_ineqs_proofs:1586）：经 `fd_in` + `in_std`。 -/
theorem y9_hi_std (hfan : FAN 0 V E) (hE : E = ESTD V) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : y9Fan V E d ≤ 2 * h0 :=
  (yk_in_std hE (yk_fd_in hfan hd)).1

/-- HOL `y4_hi_std2`（lp_ineqs_proofs:1598）。 -/
theorem y4_hi_std2 (hfan : FAN 0 V E) (hE : E = ESTD V) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : y4Fan V E d ≤ 2 * h0 :=
  (yk_in_std hE (yk_fd_in hfan hd)).1

/-- HOL `y5_hi_std2`（lp_ineqs_proofs:1605）。 -/
theorem y5_hi_std2 (hfan : FAN 0 V E) (hE : E = ESTD V) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : y5Fan V E d ≤ 2 * h0 :=
  (yk_in_std hE (yk_ifd_in hfan hd)).1

/-- HOL `y6_hi_std2`（lp_ineqs_proofs:1612）。 -/
theorem y6_hi_std2 (hE : E = ESTD V) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    y6Fan d ≤ 2 * h0 :=
  (yk_in_std hE hd).1

/-! ### 9e. ys_eq（Nonlinear-Y 节 :2184-2259，定义层顶石） -/

/-- HOL `ys_eq`（lp_ineqs_proofs:2187，dart1 折算形）：y1..y6 在 dart
`(v, w)` 上全部显式化——核心 = `yk_invFunFFanPairExt_apply`。 -/
theorem ys_eq (hfan : FAN 0 V E) {v w : V3} (hvw : (v, w) ∈ dart1OfFan V E) :
    y1Fan (v, w) = ‖v‖ ∧ y2Fan (v, w) = ‖w‖ ∧
      y3Fan V E (v, w) = ‖sigmaFan 0 V E v w‖ ∧
      y4pFan V E (v, w) = dist w (sigmaFan 0 V E v w) ∧
      y5Fan V E (v, w) = dist v (sigmaFan 0 V E v w) ∧
      y6Fan (v, w) = dist v w := by
  have hinv : Function.invFun (fFanPairExt 0 V E) (v, w)
      = (sigmaFan 0 V E v w, v) := by
    rw [yk_invFunFFanPairExt_apply hfan (v, w), if_pos hvw]
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl⟩
  · show ‖(Function.invFun (fFanPairExt 0 V E) (v, w)).1‖
      = ‖sigmaFan 0 V E v w‖
    rw [hinv]
  · show dist (v, w).2 (Function.invFun (fFanPairExt 0 V E) (v, w)).1
      = dist w (sigmaFan 0 V E v w)
    rw [hinv]
  · show dist (Function.invFun (fFanPairExt 0 V E) (v, w)).1
      (Function.invFun (fFanPairExt 0 V E) (v, w)).2
      = dist v (sigmaFan 0 V E v w)
    rw [hinv, dist_comm]

/-- HOL `ys_eq_alt`（lp_ineqs_proofs:2241，投影形）。 -/
theorem ys_eq_alt (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    y1Fan d = ‖d.1‖ ∧ y2Fan d = ‖d.2‖ ∧
      y3Fan V E d = ‖sigmaFan 0 V E d.1 d.2‖ ∧
      y4pFan V E d = dist d.2 (sigmaFan 0 V E d.1 d.2) ∧
      y5Fan V E d = dist d.1 (sigmaFan 0 V E d.1 d.2) ∧
      y6Fan d = dist d.1 d.2 := by
  obtain ⟨v, w⟩ := d
  exact ys_eq hfan hd

/-! ### 9f. y4'_eq_y4（Dart3 节 lp_ineqs_proofs:1478-1509；2026-10-23 Lane P W2）

HOL `y4'_eq_y4`（:1497）经 `f_fan_pair3`（add_triangle-compiled.hl:608）：
3 元面上 `f d = (w, σ_v w)` 使 y4'（inv f 显式形）与 y4（f 显式形）逐字相等。
证明消费 §3a' W2 kit 的 `wk_fan3`（文件序：kit 先于 §9，引用合法）。 -/

/-- HOL `y4'_eq_y4`（lp_ineqs_proofs:1497，Dart3 节）：`y4'_fan = y4_fan` 在
`d ∈ darts_k 3` 上（`f_fan_pair3` 路线）。 -/
theorem y4p_eq_y4 (hfan : FAN 0 V E) {d : V3 × V3}
    (hd : d ∈ dartsK 3 (hypermapOfFanTl V E hfan)) :
    y4pFan V E d = y4Fan V E d := by
  obtain ⟨hdarts, hcard3⟩ := hd
  obtain ⟨v, w⟩ := d
  have hd1 : (v, w) ∈ dart1OfFan V E := dartsTl_mem hdarts
  obtain ⟨-, hfeq, -, -, -, -, -, -⟩ := wk_fan3 hfan hd1 hcard3
  have hp : y4pFan V E (v, w) = dist w (sigmaFan 0 V E v w) := by
    simp only [y4pFan]
    rw [yk_invFunFFanPairExt_apply hfan (v, w), if_pos hd1]
  have hq : y4Fan V E (v, w) = dist w (sigmaFan 0 V E v w) := by
    have h7 : y4Fan V E (v, w)
        = dist (fFanPair 0 V E (v, w)).1 (fFanPair 0 V E (v, w)).2 := by
      simp only [y4Fan, fFanPairExt, if_pos hd1]
    rw [h7, ← faceMapTl_apply (V := V) (E := E) (hfan := hfan) hd1, hfeq]
  rw [hp, hq]

/-! ### 9g. W4·W1 墙件（Lane AA 2026-10-23）：
`Cfyxfty.AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN`（CFYXFTY.hl:982-1022）

wdart/conforming 侦察（docs/scouts/conforming-wall-scout.md + WAVES.md §W1a）
钉死的唯一真墙件。简化链（勿逐字抄 HOL 的 aff_ge 分解步）：
σ := sigmaFan x V E e.1 e.2；
`aff_gt_1_3_subset_dart_leads_into_fan`（PlanarityAuto12:270，hsigma := rfl）
给 affGt {x} {σ, e.1, e.2} ⊆ dartLeadsInto x V E e.1 e.2；
`DARTSET_LEADS_INTO_FAN`（PlanarityComponent:375）换 dartsetLeadsIntoFan f；
affGt {x} {e.1, e.2} ⊆ closure(affGt {x} {σ, e.1, e.2}) 由密度胶水私件
`wk_affGt12_subset_closure_affGt13` 给出（HOL 的 CLOSURE_AFF_GT_1_3_EQ_AFF_GE_1_3
消费侧替代：不走 affGe 闭性——OPEN_DIFF_AFF_GE 只给 closure(affGt) ⊆ affGe
的"错向"包含——而是经公开件 `aff_gt_1_2`/`AFF_GT_1_3` 的显式系数形，用内点
p = (x+v+u+w)/4 的凸扰动直接构造逼近点）。
注意：闭扇步不需要 CLOSED_WEDGE（PackingAuto18:5629-5644 现为未证桩，
W1b 须另行立项）也不需要
properties_fully_surrounded / fan80 的非共面内容（fan80 仅作为上游
aff_gt_1_3_subset_dart_leads_into_fan 的假设透传）。
HOL 证明中的 ext_dart 超图同构步在 pair-dart 编码下整体消失（侦察已核），
不移植。 -/

/-- 密度胶水（W4·W1 私件）：开扇 `affGt {x} {u, w}` 含于三点开锥
`affGt {x} {v, u, w}` 的闭包。HOL CFYXFTY.hl:940
`CLOSURE_AFF_GT_1_3_EQ_AFF_GE_1_3`（closure(aff_gt) = aff_ge，需非共面）
的替代：本包含对任意点成立，只需 Disjoint（去重求和的显式系数形条件）。
构造：内点 p = (x+v+u+w)/4 ∈ affGt {x} {v,u,w}（v 侧系数 1/4 > 0），
逼近点 y' = (1-t)•y + t•p 的 u/w 侧锥系数 (1-t)·t + t/4 > 0（t ≤ 1）。 -/
private theorem wk_affGt12_subset_closure_affGt13 {x u v w : V3}
    (hdis12 : Disjoint ({x} : Set V3) ({u, w} : Set V3))
    (hdis13 : Disjoint ({x} : Set V3) ({v, u, w} : Set V3)) :
    affGt ({x} : Set V3) ({u, w} : Set V3) ⊆
      closure (affGt ({x} : Set V3) ({v, u, w} : Set V3)) := by
  intro z hz
  rw [aff_gt_1_2 hdis12] at hz
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hzeq⟩ := hz
  rw [AFF_GT_1_3 x v u w hdis13, Metric.mem_closure_iff]
  intro ε hε
  set p : V3 := (1 / 4 : ℝ) • x + (1 / 4 : ℝ) • v + (1 / 4 : ℝ) • u + (1 / 4 : ℝ) • w
    with hpdef
  have hpmem : p ∈ affGt ({x} : Set V3) ({v, u, w} : Set V3) := by
    rw [AFF_GT_1_3 x v u w hdis13, Set.mem_setOf_eq]
    exact ⟨1 / 4, 1 / 4, 1 / 4, 1 / 4, by norm_num, by norm_num, by norm_num,
      by norm_num, rfl⟩
  set t : ℝ := min (1 / 2) (ε / (2 * (‖z - p‖ + 1))) with htdef
  have hN : 0 ≤ ‖z - p‖ := norm_nonneg _
  have ht0 : 0 < t := by
    rw [htdef]
    exact lt_min (by norm_num) (div_pos hε (by linarith))
  have ht1 : t ≤ 1 := by
    rw [htdef]
    exact le_trans (min_le_left _ _) (by norm_num)
  have htmin : t ≤ ε / (2 * (‖z - p‖ + 1)) := by rw [htdef]; exact min_le_right _ _
  refine ⟨(1 - t) • z + t • p, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    refine ⟨(1 - t) * t1 + t / 4, t / 4, (1 - t) * t2 + t / 4, (1 - t) * t3 + t / 4,
      ?_, by positivity, ?_, ?_, ?_⟩
    · have h10 : 0 ≤ 1 - t := by linarith
      have h20 : 0 ≤ (1 - t) * t2 := mul_nonneg h10 ht2.le
      linarith
    · have h10 : 0 ≤ 1 - t := by linarith
      have h30 : 0 ≤ (1 - t) * t3 := mul_nonneg h10 ht3.le
      linarith
    · linear_combination (1 - t) * hsum
    · rw [hzeq, hpdef]
      module
  · rw [dist_eq_norm]
    have hsub : z - ((1 - t) • z + t • p) = t • (z - p) := by
      rw [hzeq, hpdef]
      module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    calc t * ‖z - p‖ ≤ ε / (2 * (‖z - p‖ + 1)) * ‖z - p‖ :=
          mul_le_mul_of_nonneg_right htmin hN
      _ < ε := by
          have hpos : 0 < 2 * (‖z - p‖ + 1) := by linarith
          have hlt : ε / (2 * (‖z - p‖ + 1)) * ‖z - p‖
              < ε / (2 * (‖z - p‖ + 1)) * (‖z - p‖ + 1) :=
            mul_lt_mul_of_pos_left (by linarith) (div_pos hε hpos)
          have heq : ε / (2 * (‖z - p‖ + 1)) * (‖z - p‖ + 1) = ε / 2 := by
            field_simp
          linarith [hlt, half_lt_self hε]

/-- HOL CFYXFTY.hl:982 `Cfyxfty.AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN`：
FAN + 邻数 > 1 + fan80 + f 为 hypermap_of_fan 的面 + e ∈ f，则
`affGt {x} {e.1, e.2} ⊆ closure (dartsetLeadsIntoFan x V E f)`。
W4·W1 主件（Lane AA 2026-10-23）；证明链见 §9g 头注。
面成员取边技巧照抄
PlanarityComponent.dartset_leads_into_is_topological_component_yfan
（faceSet → darts = dart1OfFan → {e.1, e.2} ∈ E）。
实例注记：本模块闭包内 dartDecEq2 抢占 Hypermap 投影的实例合成
（§0a 陷阱），投影一律 `@`-显式钉 instProd 味（与 DARTSET_LEADS_INTO_FAN
陈述的 PlanarityComponent 烤定味一致）。 -/
theorem AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN
    (x : V3) (V : Set V3) (E : Set (Set V3)) (f : Set (V3 × V3)) (e : V3 × V3)
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hf : f ∈ @Hypermap.faceSet (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) (he : e ∈ f) :
    affGt ({x} : Set V3) ({e.1, e.2} : Set V3) ⊆
      closure (dartsetLeadsIntoFan x V E f) := by
  have hdarts : (↑(@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have he_darts : e ∈ @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan) := by
    have heU : e ∈ ⋃₀ @Hypermap.faceSet (V3 × V3)
        (fun a b => instDecidableEqProd a b) (hypermapOfFan x V E hfan) :=
      Set.mem_sUnion.mpr ⟨f, hf, he⟩
    have hsu := sUnion_setOfOrbits
      (@Hypermap.faceMap_permutes (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan x V E hfan))
    change e ∈ (↑(@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) : Set (V3 × V3))
    rw [hsu]
    simpa [Hypermap.faceSet] using heU
  have he_dart1 : e ∈ dart1OfFan V E := by rw [← hdarts]; exact he_darts
  have hvw : ({e.1, e.2} : Set V3) ∈ E := by simpa [dart1OfFan] using he_dart1
  have he2S : e.2 ∈ setOfEdge e.1 V E :=
    (properties_of_setOfEdge_fan x V E e.1 e.2 hfan).mp hvw
  have hσS : sigmaFan x V E e.1 e.2 ∈ setOfEdge e.1 V E :=
    sigma_fan_in_setOfEdge hfan he2S
  have huv' : ({e.1, sigmaFan x V E e.1 e.2} : Set V3) ∈ E :=
    (properties_of_setOfEdge_fan x V E e.1 (sigmaFan x V E e.1 e.2) hfan).mpr hσS
  have hpair : ({e.1, sigmaFan x V E e.1 e.2} : Set V3)
      = ({sigmaFan x V E e.1 e.2, e.1} : Set V3) := by
    ext a; simp; tauto
  have huv : ({sigmaFan x V E e.1 e.2, e.1} : Set V3) ∈ E := by rwa [hpair] at huv'
  have hnc : ¬ Collinear3 x e.1 e.2 := fan_not_collinear hfan hvw
  have hxe1 : x ≠ e.1 :=
    fun heq => hnc (collinear3_of_eq (v := x) (w := e.1) (w1 := e.2) heq.symm)
  have hxe2 : x ≠ e.2 :=
    fun heq => hnc (collinear3_pair_left (v0 := x) (v1 := e.1) heq.symm)
  have hncσ : ¬ Collinear3 x (sigmaFan x V E e.1 e.2) e.1 := fan_not_collinear hfan huv
  have hxσ : x ≠ sigmaFan x V E e.1 e.2 :=
    fun heq => hncσ (collinear3_of_eq (v := x) (w := sigmaFan x V E e.1 e.2)
      (w1 := e.1) heq.symm)
  have hdis12 : Disjoint ({x} : Set V3) ({e.1, e.2} : Set V3) := by
    rw [Set.disjoint_left]
    intro a ha hb
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with h | h
    · exact hxe1 h
    · exact hxe2 h
  have hdis13 : Disjoint ({x} : Set V3)
      ({sigmaFan x V E e.1 e.2, e.1, e.2} : Set V3) := by
    rw [Set.disjoint_left]
    intro a ha hb
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with h | h | h
    · exact hxσ h
    · exact hxe1 h
    · exact hxe2 h
  calc affGt ({x} : Set V3) ({e.1, e.2} : Set V3)
      ⊆ closure (affGt ({x} : Set V3)
          ({sigmaFan x V E e.1 e.2, e.1, e.2} : Set V3)) :=
        wk_affGt12_subset_closure_affGt13 hdis12 hdis13
    _ ⊆ closure (dartLeadsInto x V E e.1 e.2) :=
        closure_mono (aff_gt_1_3_subset_dart_leads_into_fan x V E
          (sigmaFan x V E e.1 e.2) e.1 e.2 hfan huv hvw rfl hcard hfan80)
    _ = closure (dartsetLeadsIntoFan x V E f) := by
        rw [DARTSET_LEADS_INTO_FAN hfan hcard hfan80 hf e he]

/-- W4·W1 主件的 Tl 接口版：面成员改走 `hypermapOfFanTl` 的 faceSet
（TameLp 章 `faceSetOfFan` 惯例，dartDecEq2 味）。faceSet 作为集合经
§0b 字段级 rfl 桥对实例参数不敏感（setOfOrbits 的数据不含实例）。 -/
theorem AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN_tl
    (V : Set V3) (E : Set (Set V3)) (f : Set (V3 × V3)) (e : V3 × V3)
    (hfan : FAN 0 V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 0 V E)
    (hf : f ∈ (hypermapOfFanTl V E hfan).faceSet) (he : e ∈ f) :
    affGt ({0} : Set V3) ({e.1, e.2} : Set V3) ⊆
      closure (dartsetLeadsIntoFan 0 V E f) := by
  have hfs : (hypermapOfFanTl V E hfan).faceSet =
      @Hypermap.faceSet (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan 0 V E hfan) := by
    unfold Hypermap.faceSet
    rw [dartsTl_eq, faceMapTl_eq]
  refine AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN 0 V E f e hfan hcard hfan80
    (hfs ▸ hf) he


/-! ### 9h. W4·W2 前段（Lane AD 2026-10-24）：face-reversal 轨道簿记件 +
LocalFan (vPrime, ePrime, f) 构造 checkpoint 件（全 private、零消费者、零新增禁词桩）。

**语义勘误（对 AA 修正指认的字面陈述）**：任务书/AA §5.3 的
`(v,w) ∈ f → (w,v) ∈ f`（f = hypermapOfFan 的 faceSet 成员，全扇面轨道）
**为假**——全扇面轨道单向（每条无向边的两个 dart 分属相邻两面；三角扇
V={v0,v1,v2}、E=三条边的实例可直接复核：faceMap 轨道 = 3 个正向 dart，
不含反向）。HOL 锚（LVDUCXU.hl DIH_K_HYP_E_PRIME:2088 /
FF_DISJOINT_ITS_IMAGE_CARD_EQ:1423）实证 W2c 真正需要的簿记 = 本块的
**轨道交错件**：nodeMap '' f = edgeMap '' f（= 轨道反向 = reverse f；
comp_eq_one 经 nodeMap_mul_faceMap（Hypermap.lean:836 现成）+ edgeMap 对合）、
面轨道两端 ∈ vPrime（"w 侧成员"内容 = faceMap 轨道闭包，非 reversal）、
FAN 继承。字面 reversal 陈述按纪律不落（疑似假陈述，记录于交付报告）。

命名：yk2_*（§9 的 yk_* 系列的 W5 续编，全 private）。 -/
/-! #### 9h.0 apply 副本（AzimBridge.lean:213-239 private workhorses 自带；
dot 投影/引理应用一律 @-钉定 instProd 实例，见 AA §5.4 踩雷实录）。 -/

variable {V : Set V3} {E : Set (Set V3)} {x : V3}

/-! ### apply 副本（AzimBridge:213-239 private workhorses，TameLp 侧自带） -/

private theorem yk2_darts_coe (hfan : FAN x V E) :
    (↑(@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) : Set (V3 × V3)) = dart1OfFan V E :=
  (finite_dart1_fan hfan).coe_toFinset

private theorem yk2_mem_darts_iff (hfan : FAN x V E) (d : V3 × V3) :
    d ∈ @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan) ↔ d ∈ dart1OfFan V E := by
  constructor
  · intro hmem
    have h2 : d ∈ (↑(@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) : Set (V3 × V3)) := Finset.mem_coe.mpr hmem
    rw [yk2_darts_coe hfan] at h2
    exact h2
  · intro hmem
    have h2 : d ∈ (↑(@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) : Set (V3 × V3)) := by
      rw [yk2_darts_coe hfan]
      exact hmem
    exact Finset.mem_coe.mp h2

private theorem yk2_apply_nodeMap (hfan : FAN x V E) (d : V3 × V3) :
    (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) d =
      if d ∈ dart1OfFan V E then nFanPair x V E d else d := by
  show (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
    (hypermapOfFan x V E hfan)) d = _
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [(finite_dart1_fan hfan).coe_toFinset]

private theorem yk2_apply_faceMap (hfan : FAN x V E) (d : V3 × V3) :
    (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) d =
      if d ∈ dart1OfFan V E then fFanPair x V E d else d := by
  show (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
    (hypermapOfFan x V E hfan)) d = _
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [(finite_dart1_fan hfan).coe_toFinset]

private theorem yk2_apply_edgeMap (hfan : FAN x V E) (d : V3 × V3) :
    (@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) d =
      if d ∈ dart1OfFan V E then eFanPair V E d else d := by
  show (@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
    (hypermapOfFan x V E hfan)) d = _
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [(finite_dart1_fan hfan).coe_toFinset]

/-! ### dart1 交换封闭 + edgeMap 对合 -/

private theorem yk2_mem_dart1_pair_comm {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (d.2, d.1) ∈ dart1OfFan V E := by
  have hE : ({d.1, d.2} : Set V3) ∈ E := hd
  have hswap : ({d.2, d.1} : Set V3) = ({d.1, d.2} : Set V3) := by
    ext a; simp; tauto
  show ({d.2, d.1} : Set V3) ∈ E
  rw [hswap]
  exact hE

private theorem yk2_edgeMap_involutive (hfan : FAN x V E) :
    @Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan x V E hfan)
      * @Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan x V E hfan) = 1 := by
  refine Equiv.Perm.ext fun d => ?_
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  by_cases hd : d ∈ dart1OfFan V E
  · have he : (d.2, d.1) ∈ dart1OfFan V E := yk2_mem_dart1_pair_comm hd
    rw [yk2_apply_edgeMap hfan d, if_pos hd,
      show (eFanPair V E d : V3 × V3) = (d.2, d.1) from rfl,
      yk2_apply_edgeMap hfan (d.2, d.1), if_pos he]
    rfl
  · rw [yk2_apply_edgeMap hfan d, if_neg hd,
      yk2_apply_edgeMap hfan d, if_neg hd]

/-! ### 一般交错恒等式（comp_eq_one 路线，任意 Hypermap + edgeMap 对合） -/

/-- 一般交错主恒等式：edgeMap 对合下 `edgeMap = nodeMap * faceMap`
（nodeMap * faceMap = edgeMap⁻¹ + 对合消逆）。 -/
private theorem yk2_gen_interleave_fw {α : Type*} [DecidableEq α] (H : Hypermap α)
    (hinvo : H.edgeMap * H.edgeMap = 1) :
    H.edgeMap = H.nodeMap * H.faceMap := by
  have h1 := Hypermap.nodeMap_mul_faceMap H
  have hinv : H.edgeMap⁻¹ = H.edgeMap := by
    have hh : H.edgeMap⁻¹ * (H.edgeMap * H.edgeMap) = H.edgeMap⁻¹ * 1 := by rw [hinvo]
    rw [inv_mul_cancel_left, mul_one] at hh
    exact hh.symm
  rw [hinv] at h1
  exact h1.symm

/-- 一般对称交错恒等式：`nodeMap = edgeMap * faceMap⁻¹`（fw + 群消去）。 -/
private theorem yk2_gen_interleave_bw {α : Type*} [DecidableEq α] (H : Hypermap α)
    (hinvo : H.edgeMap * H.edgeMap = 1) :
    H.nodeMap = H.edgeMap * H.faceMap⁻¹ := by
  rw [yk2_gen_interleave_fw H hinvo, mul_inv_cancel_right]

/-! ### 探针 2：轨道闭包 + 像交换 + vPrime/ePrime 簿记 -/

/-- 面轨道缩写（@-钉定实例；b = 基 dart）。 -/
private def yk2_faceOrbit (x : V3) (V : Set V3) (E : Set (Set V3)) (hfan : FAN x V E)
    (b : V3 × V3) : Set (V3 × V3) :=
  orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
    (hypermapOfFan x V E hfan)) b

private theorem yk2_faceOrbit_closure (hfan : FAN x V E) {b d : V3 × V3}
    (hd : d ∈ yk2_faceOrbit x V E hfan b) :
    @Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan) d ∈ yk2_faceOrbit x V E hfan b := by
  obtain ⟨n, hn⟩ := hd
  refine ⟨n + 1, ?_⟩
  rw [pow_succ', Equiv.Perm.mul_apply, hn]

private theorem yk2_faceOrbit_symm_closure (hfan : FAN x V E) {b d : V3 × V3}
    (hd : d ∈ yk2_faceOrbit x V E hfan b) :
    (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)).symm d ∈ yk2_faceOrbit x V E hfan b := by
  have hperm : PermutesOn (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) (@Hypermap.darts (V3 × V3)
      (fun a b' => instDecidableEqProd a b') (hypermapOfFan x V E hfan)) :=
    @Hypermap.faceMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)
  obtain ⟨k, hk⟩ := hd
  obtain ⟨j, hj⟩ := hperm.exists_pow_eq_inv
  have hjs : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)).symm
      = @Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan) ^ j := hj
  refine ⟨j + k, ?_⟩
  rw [pow_add, Equiv.Perm.mul_apply, hk, hjs]

/-! ### 探针 2b：像交换 + 两端簿记 -/

/-- 面轨道 ⊆ dart1（face_subset_darts + coe 桥）。 -/
private theorem yk2_faceOrbit_subset_dart1 (hfan : FAN x V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) : yk2_faceOrbit x V E hfan b ⊆ dart1OfFan V E := by
  intro d hd
  have hx' : b ∈ @Hypermap.darts (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan) := (yk2_mem_darts_iff hfan b).mpr hb
  have hsub := @Hypermap.face_subset_darts (V3 × V3) (fun a b' => instDecidableEqProd a b')
    b (hypermapOfFan x V E hfan) hx'
  exact (yk2_mem_darts_iff hfan d).mp (Finset.mem_coe.mp (hsub hd))

/-- 交错点式（节点侧）：`nodeMap d = edgeMap (faceMap⁻¹ d)`。 -/
private theorem yk2_node_apply_eq_edge_faceInv_apply (hfan : FAN x V E) (d : V3 × V3) :
    @Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan) d
      = @Hypermap.edgeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan x V E hfan)
        ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan x V E hfan)).symm d) := by
  have h := @yk2_gen_interleave_bw (V3 × V3) (fun a b => instDecidableEqProd a b)
    (hypermapOfFan x V E hfan) (yk2_edgeMap_involutive hfan)
  rw [h]
  rfl

/-- 交错点式（边侧）：`edgeMap d = nodeMap (faceMap d)`。 -/
private theorem yk2_edge_apply_eq_node_face_apply (hfan : FAN x V E) (d : V3 × V3) :
    @Hypermap.edgeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan) d
      = @Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan x V E hfan)
        (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan x V E hfan) d) := by
  have h := @yk2_gen_interleave_fw (V3 × V3) (fun a b => instDecidableEqProd a b)
    (hypermapOfFan x V E hfan) (yk2_edgeMap_involutive hfan)
  rw [h]
  rfl

/-- **轨道交错件（face-reversal 真形式）**：面轨道的 nodeMap 像 = edgeMap 像。
即轨道 f 上 `(v,w) ↦ (w,v)` 的像 = n(f)——轨道级 reversal 的正确形状。 -/
private theorem yk2_face_node_image_eq_edge_image (hfan : FAN x V E) (b : V3 × V3) :
    (fun d => @Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan) d) '' yk2_faceOrbit x V E hfan b
      = (fun d => @Hypermap.edgeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan) d) '' yk2_faceOrbit x V E hfan b := by
  refine Set.Subset.antisymm (Set.image_subset_iff.2 fun d hd => ?_)
    (Set.image_subset_iff.2 fun d hd => ?_)
  · exact ⟨(@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)).symm d, yk2_faceOrbit_symm_closure hfan hd,
      (yk2_node_apply_eq_edge_faceInv_apply hfan d).symm⟩
  · exact ⟨@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan) d, yk2_faceOrbit_closure hfan hd,
      (yk2_edge_apply_eq_node_face_apply hfan d).symm⟩

/-! ### 探针 2c：vPrime/ePrime 两端簿记 + FAN 继承 + setOfEdge 刻画 -/

/-- dart 两端 ∈ V（FAN_in_setOfEdge 折算）。 -/
private theorem yk2_dart_fst_snd_mem_V (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) : d.1 ∈ V ∧ d.2 ∈ V :=
  ⟨(FAN_in_setOfEdge x V E d.1 d.2 hfan hd).1,
    (FAN_in_setOfEdge x V E d.1 d.2 hfan hd).2.1⟩

/-- 面轨道 dart 的第一端 ∈ vPrime（w 侧见证 = dart 本身）。 -/
private theorem yk2_face_fst_mem_vPrime (hfan : FAN x V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) {d : V3 × V3} (hd : d ∈ yk2_faceOrbit x V E hfan b) :
    d.1 ∈ vPrime_p2 V (yk2_faceOrbit x V E hfan b) := by
  refine ⟨(yk2_dart_fst_snd_mem_V hfan
    (yk2_faceOrbit_subset_dart1 hfan b hb hd)).1, ⟨d.2, hd⟩⟩

/-- 面轨道 dart 的第二端 ∈ vPrime（w 侧见证 = faceMap 的像；
这就是 AA 所指"w 侧成员"簿记：内容 = faceMap 轨道闭包，非 reversal）。 -/
private theorem yk2_face_snd_mem_vPrime (hfan : FAN x V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) {d : V3 × V3} (hd : d ∈ yk2_faceOrbit x V E hfan b) :
    d.2 ∈ vPrime_p2 V (yk2_faceOrbit x V E hfan b) := by
  have hd1 : d ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb hd
  refine ⟨(yk2_dart_fst_snd_mem_V hfan hd1).2, ?_⟩
  refine ⟨(@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
    (hypermapOfFan x V E hfan) d).2, ?_⟩
  have hfc : @Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan) d = (d.2, inverseSigmaFan x V E d.2 d.1) := by
    rw [yk2_apply_faceMap hfan d, if_pos hd1]
    rfl
  rw [hfc]
  show (d.2, inverseSigmaFan x V E d.2 d.1) ∈ yk2_faceOrbit x V E hfan b
  exact hfc ▸ yk2_faceOrbit_closure hfan hd

/-- 面轨道 dart 的底边 ∈ ePrime。 -/
private theorem yk2_face_dart_mem_ePrime (hfan : FAN x V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) {d : V3 × V3} (hd : d ∈ yk2_faceOrbit x V E hfan b) :
    ({d.1, d.2} : Set V3) ∈ ePrime_p2 E (yk2_faceOrbit x V E hfan b) := by
  refine ⟨d.1, d.2, rfl, ?_, hd⟩
  exact yk2_faceOrbit_subset_dart1 hfan b hb hd

/-- fan7 大集成员转移（并集形）：ePrime ∪ singletons(vPrime) ⊆ E ∪ singletons(V)。 -/
private theorem yk2_mem_E_singletons_transfer (hfan : FAN x V E) {f : Set (V3 × V3)}
    {e : Set V3} (he : e ∈ ePrime_p2 E f ∪ {s | ∃ v ∈ vPrime_p2 V f, s = {v}}) :
    e ∈ E ∪ {s | ∃ v ∈ V, s = {v}} := by
  rcases (Set.mem_union _ _ _).mp he with h | h
  · rcases Set.mem_setOf_eq.mp h with ⟨v, w, heq, hEe, -⟩
    exact Set.mem_union_left _ (by rw [heq]; exact hEe)
  · obtain ⟨v, hv, rfl⟩ := h
    exact Set.mem_union_right _ (Set.mem_setOf_eq.mpr ⟨v, hv.1, rfl⟩)

/-- **FAN x (vPrime, ePrime) 继承**（HOL IMP_FAN_V_PRIME_E_PRIME 的 Lean 折算，
checkpoint 1 capstone）。 -/
private theorem yk2_FAN_vPrime_ePrime (hfan : FAN x V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) :
    FAN x (vPrime_p2 V f) (ePrime_p2 E f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ⋃₀ ePrime ⊆ vPrime：每条 ePrime 边 = {v,w}，(v,w) ∈ f，两端经轨道簿记入 vPrime
    rw [hf]
    intro e he
    rcases Set.mem_sUnion.mp he with ⟨t, ht, het⟩
    rcases Set.mem_setOf_eq.mp ht with ⟨v, w, heq, hEe, hvwf⟩
    have hd1 : (v, w) ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb hvwf
    have hV := yk2_dart_fst_snd_mem_V hfan hd1
    have hfc : @Hypermap.faceMap (V3 × V3) (fun a' b' => instDecidableEqProd a' b')
        (hypermapOfFan x V E hfan) (v, w)
        = (w, inverseSigmaFan x V E w v) := by
      rw [yk2_apply_faceMap hfan (v, w), if_pos hd1]
      rfl
    rw [heq] at het
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at het
    rcases het with hev | hew
    · rw [hev]
      exact ⟨hV.1, ⟨w, hvwf⟩⟩
    · rw [hew]
      refine ⟨hV.2, ⟨(@Hypermap.faceMap (V3 × V3) (fun a' b' => instDecidableEqProd a' b')
        (hypermapOfFan x V E hfan) (v, w)).2, ?_⟩⟩
      rw [hfc]
      exact hfc ▸ yk2_faceOrbit_closure hfan hvwf
  · -- Graph ePrime：边作为集合从 Graph E 直传
    intro e he
    rcases Set.mem_setOf_eq.mp he with ⟨v, w, heq, hEe, -⟩
    subst heq
    obtain ⟨hfin, hcard⟩ := hfan.2.1 {v, w} hEe
    exact ⟨hfin, hcard⟩
  · -- fan1：有限（vPrime ⊆ V）非空（b.1 ∈ vPrime）
    refine ⟨Set.Finite.subset hfan.2.2.1.1 (fun v hv => hv.1), ?_⟩
    rw [hf]
    refine Set.nonempty_iff_ne_empty.mp ?_
    refine ⟨b.1, ?_⟩
    have hb_orb : b ∈ yk2_faceOrbit x V E hfan b := mem_orbitMap_self _ _
    refine ⟨(yk2_dart_fst_snd_mem_V hfan
      (yk2_faceOrbit_subset_dart1 hfan b hb hb_orb)).1, ⟨b.2, ?_⟩⟩
    show b ∈ yk2_faceOrbit x V E hfan b
    exact hb_orb
  · -- fan2：vPrime ⊆ V 且 x ∉ V
    intro h0
    exact hfan.2.2.2.1 h0.1
  · -- fan6：边从 E 直传
    intro e he
    rcases Set.mem_setOf_eq.mp he with ⟨v, w, heq, hEe, -⟩
    rw [heq]
    exact hfan.2.2.2.2.1 {v, w} hEe
  · -- fan7：大集含入后从原 fan7 直传（结论不含 V/E）
    intro e1 he1 e2 he2
    exact hfan.2.2.2.2.2 e1 (yk2_mem_E_singletons_transfer hfan he1)
      e2 (yk2_mem_E_singletons_transfer hfan he2)


/-! #### 9h.1 setOfEdge 刻画 + 抽象轨道外延 + 受限 dartset 分解
（checkpoint 2 的无几何骨架；σ′ 一致的几何残差见下方 NEEDS 施工图）。 -/

/-- **受限扇 setOfEdge 刻画**：vPrime/ePrime 的邻居集 = {u | u ∈ V ∧
((v,u) ∈ f ∨ (u,v) ∈ f)}。⊆ 侧零轨道假设；⊇ 用 faceMap 轨道闭包
（AA "w 侧成员"的真内容）。 -/
private theorem yk2_setOfEdge_ePrime_eq (hfan : FAN x V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) (v : V3) :
    setOfEdge v (vPrime_p2 V f) (ePrime_p2 E f)
      = {u | u ∈ V ∧ ((v, u) ∈ f ∨ (u, v) ∈ f)} := by
  rw [hf]
  ext u
  simp only [setOfEdge, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hep, hvp⟩
    rcases Set.mem_setOf_eq.mp hep with ⟨a, c, heq, hEe, hac⟩
    rcases Set.pair_eq_pair_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨hvp.1, Or.inl ?_⟩
      rw [h1, h2]
      exact hac
    · refine ⟨hvp.1, Or.inr ?_⟩
      rw [h1, h2]
      exact hac
  · rintro ⟨huV, hd | hd⟩
    · have hd1 : (v, u) ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb hd
      exact ⟨Set.mem_setOf_eq.mpr ⟨v, u, rfl, hd1, hd⟩,
        yk2_face_snd_mem_vPrime hfan b hb hd⟩
    · have hd1 : (u, v) ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb hd
      refine ⟨Set.mem_setOf_eq.mpr ⟨u, v, ?_, hd1, hd⟩,
        yk2_face_fst_mem_vPrime hfan b hb hd⟩
      ext a; simp; tauto

/-- 抽象轨道入闭：fc′ 把 f 映入 f 且 b ∈ f 时，fc′-幂轨道留在 f。 -/
private theorem yk2_orbit_subset_of_closed {α : Type*} [DecidableEq α]
    {fc' : Equiv.Perm α} {f : Set α} {b : α} (hb : b ∈ f)
    (hclosed : ∀ d ∈ f, fc' d ∈ f) : ∀ n : ℕ, (fc' ^ n) b ∈ f := by
  intro n
  induction n with
  | zero => simpa using hb
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hclosed _ ih

/-- 抽象幂一致：fc-轨道 f 上逐点一致则幂迭代逐点一致。 -/
private theorem yk2_pow_agree {α : Type*} [DecidableEq α] {fc fc' : Equiv.Perm α}
    {f : Set α} {b : α} (hbf : orbitMap fc b = f)
    (hagree : ∀ d ∈ f, fc' d = fc d) : ∀ n : ℕ, (fc' ^ n) b = (fc ^ n) b := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    have hmem : (fc ^ m) b ∈ f := by rw [← hbf]; exact pow_apply_mem_orbitMap fc m b
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    exact hagree _ hmem

/-- 抽象轨道外延：fc-轨道 f 上 fc′ 与 fc 逐点一致且把 f 映入 f 时，
基点 b 的 fc′-轨道 = f（LOCALIZE_PRESERVE_FACE 的无几何骨架）。 -/
private theorem yk2_orbit_ext_of_agree {α : Type*} [DecidableEq α] {fc fc' : Equiv.Perm α}
    {f : Set α} {b : α} (hbf : orbitMap fc b = f) (hb : b ∈ f)
    (hagree : ∀ d ∈ f, fc' d = fc d) (hclosed : ∀ d ∈ f, fc' d ∈ f) :
    orbitMap fc' b = f := by
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    obtain ⟨n, hn⟩ := hy
    rw [← hn]
    exact yk2_orbit_subset_of_closed hb hclosed n
  · intro y hy
    rw [← hbf] at hy
    obtain ⟨n, hn⟩ := hy
    rw [← hn, ← yk2_pow_agree hbf hagree n]
    exact pow_apply_mem_orbitMap fc' n b

/-- **受限 dartset 分解**：dart1OfFan (vPrime, ePrime) = f ∪ reverse f
（Dih2k 的 card = 2·K 内容的集合层前置；分解本身零单射性/相异性假设）。 -/
private theorem yk2_dart1_ePrime_eq_union_swap (hfan : FAN x V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) :
    dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)
      = f ∪ (fun d => (d.2, d.1)) '' f := by
  rw [hf]
  ext d
  simp only [dart1OfFan, Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
  constructor
  · intro hd
    obtain ⟨a, c, heq, hEe, hac⟩ := Set.mem_setOf_eq.mp hd
    rcases Set.pair_eq_pair_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hda : d = (a, c) := by
        apply Prod.ext
        · exact h1
        · exact h2
      rw [hda]
      exact Or.inl hac
    · have hda : d = (c, a) := by
        apply Prod.ext
        · exact h1
        · exact h2
      refine Or.inr ⟨(a, c), hac, ?_⟩
      rw [hda]
  · rintro (hd | ⟨d', hd', hd_eq⟩)
    · have hd1 : d ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb hd
      exact Set.mem_setOf_eq.mpr ⟨d.1, d.2, rfl, hd1, hd⟩
    · obtain ⟨a, c, heq, hEe, hac⟩ := Set.mem_setOf_eq.mp
        (yk2_face_dart_mem_ePrime hfan b hb hd' : ({d'.1, d'.2} : Set V3)
          ∈ ePrime_p2 E (yk2_faceOrbit x V E hfan b))
      refine Set.mem_setOf_eq.mpr ⟨a, c, ?_, hEe, hac⟩
      rw [← hd_eq]
      rw [show ({(d'.2, d'.1).1, (d'.2, d'.1).2} : Set V3)
          = ({d'.1, d'.2} : Set V3) from by ext a; simp; tauto]
      exact heq

/-! **NEEDS（checkpoint 2 几何残差，W6 施工图，2026-10-24 Lane AD 勘察）**：
`FF = orbitMap (hypermapOfFan 0 vPrime ePrime hfan′).faceMap b`（= f，
HOL LOCALIZE_PRESERVE_FACE，LVDUCXU.hl:460）在本框架下已归约为
`yk2_orbit_ext_of_agree`（本块已证）的三个前提：
① `hbf : orbitMap H.faceMap b = f`——定义性（f 即该轨道）；
② `hagree : ∀ d ∈ f, H′.faceMap d = H.faceMap d`——唯一几何残差。d = (v,w) ∈ f
   时两侧 = (w, σ′_w⁻¹ v) vs (w, σ_w⁻¹ v)，经 `yk2_setOfEdge_ePrime_eq`（已证）
   + `permutes_sigma_fan`（Fan.lean:654）+ 2 元集 σ′ 交换性归约为
   **|setOfEdge w vPrime ePrime| = 2**，即 f 在 w 处恰两条面边
   （面圈顶点两两相异，W2a 内容；HOL 经 simple_hypermap 消解：
   RNSYJXM-compiled.hl 的 fully_surrounded_simple_hypermap =
   Hypermap_iso.fan_hypermaps_iso + Conforming.SRPRNPL，全树未移植）；
③ `hclosed : ∀ d ∈ f, H′.faceMap d ∈ f`——随 ②（σ′ 一致 + H.faceMap 轨道闭包）。
Dih2k checkpoint 3 前置另见 `yk2_dart1_ePrime_eq_union_swap`（已证；
card = 2·K 还需 f ∩ reverse f = ∅ 与 HasOrders，同依赖 ② 的单圈性）。 -/

-- §9h.1 NEEDS 处置（Lane AG 2026-10-23，ykit7）：下方 §9h.2 已消除 ②（σ′ 一致）。
-- 路线勘误：② 不走 simple_hypermap（|N′(w)| = 2 / 面圈顶点两两相异不必先行），
-- 直接复刻 HOL IN_FF_FACE_MAP_IDE（LVDUCXU.hl:191-459）核心：H.faceMap d = (c,t)
-- ∈ f（轨道闭包）把 t 压进受限邻集，SIGMA_FAN 极小性嵌套互夹 + azim 唯一性
-- 给 σ′_c t = σ_c t。simple_hypermap 路线在 HOL 原文也只服务其后的
-- 2 < CARD FF（local_fan/Dih2k）合取，属 checkpoint 3。

/-! #### 9h.2 checkpoint 2 残差消除（Lane AG 2026-10-24）：σ′ 一致 + 受限面轨道

§9h.1 抽象骨架（`yk2_orbit_ext_of_agree`）的几何前提在此闭合：
`yk7_hagree`（H′.faceMap 与 H.faceMap 在面轨道 f 上逐点一致）与
`yk7_FF_eq_faceOrbit`（受限扇超图的 faceMap-轨道 = 全扇面轨道，
HOL LOCALIZE_PRESERVE_FACE，LVDUCXU.hl:460 第一合取）。

新件全 private、yk7_* 前缀、零消费者（除块内）。禁词自查：
本块不含任何被禁构造（全部定理自身完全证明）。 -/

/-! ### 抽屉原理（Fan.lean private finite_surjOf_inj 的 TameLp 副本，V3 具体化） -/

private theorem yk7_finite_surjOf_inj {f : V3 → V3} {S : Set V3} (hfin : S.Finite)
    (hmaps : ∀ a ∈ S, f a ∈ S) (hinj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b) :
    ∀ b ∈ S, ∃ a ∈ S, f a = b := by
  have hinj' : Set.InjOn f S := fun a ha b hb hab => hinj a ha b hb hab
  have hcard : (f '' S).ncard = S.ncard := hinj'.ncard_image
  have hle : f '' S ⊆ S := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := hy
    exact hmaps a ha
  intro b hb
  by_contra hnb
  have hsub2 : f '' S ⊆ S \ {b} := by
    intro y hy
    refine ⟨hle hy, ?_⟩
    intro hyb
    rw [Set.mem_singleton_iff] at hyb
    obtain ⟨a, haS, hay⟩ := (Set.mem_image f S y).mp hy
    rw [hyb] at hay
    exact hnb ⟨a, haS, hay⟩
  have hpsub : S \ {b} ⊂ S := by
    refine ⟨fun y hy => hy.1, ?_⟩
    intro heq
    have hmem : b ∈ S \ {b} := heq hb
    exact absurd hmem.2 (by simp)
  have h2 : (S \ {b}).ncard < S.ncard := Set.ncard_lt_ncard hpsub hfin
  have hfin2 : (S \ {b}).Finite := hfin.subset (fun y hy => hy.1)
  have h3 : (f '' S).ncard ≤ (S \ {b}).ncard := Set.ncard_le_ncard hsub2 hfin2
  omega

/-! ### invFun 刻画（extensionSigmaFan 型置换：S 内单射、S 外恒等） -/

/-- f 把 S 映入 S、S 上单射、S 外恒等，且 x ∈ S、y ∈ S、f x = y 时
`Function.invFun f y = x`（y 的唯一 S 内前驱就是 invFun 的值）。 -/
private theorem yk7_invFun_eq_of_apply {f : V3 → V3} {S : Set V3}
    (hmaps : ∀ a ∈ S, f a ∈ S) (hinj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b)
    (hout : ∀ a ∉ S, f a = a) {x y : V3} (hx : x ∈ S) (hy : y ∈ S)
    (hfx : f x = y) : Function.invFun f y = x := by
  have hfx' : f (Function.invFun f y) = y := Function.invFun_eq ⟨x, hfx⟩
  have hmem : Function.invFun f y ∈ S := by
    by_contra hcon
    rw [hout (Function.invFun f y) hcon] at hfx'
    apply hcon
    rw [hfx']
    exact hy
  exact hinj _ hmem x hx (hfx'.trans hfx.symm)

/-! ### 嵌套邻集 σ 一致（HOL IN_FF_FACE_MAP_IDE 尾段 IDENTIFY_AZIM_CYCLE 步） -/

/-- 嵌套邻集的 σ 一致：受限扇 w-邻集 ⊆ 全扇 w-邻集，u 在受限邻集中，
且全扇 σ_full(w) u 也落在受限邻集中，则两 σ 在 u 处取值相同。
（两邻集皆非单点时 SIGMA_FAN 极小性互夹 + `unique_azim_point_fan`；
单点情形按 sigmaFan 定义直接折叠。） -/
private theorem yk7_sigma_agree {V' : Set V3} {E' : Set (Set V3)} {w u : V3}
    (hfan : FAN x V E) (hfan' : FAN x V' E')
    (hsub : ∀ p : V3, p ∈ setOfEdge w V' E' → p ∈ setOfEdge w V E)
    (hu : u ∈ setOfEdge w V' E')
    (hσ : sigmaFan x V E w u ∈ setOfEdge w V' E') :
    sigmaFan x V E w u = sigmaFan x V' E' w u := by
  by_cases hSfull : setOfEdge w V E = {u}
  · -- 全扇邻集单点：两 σ 皆 = u
    have hσu : sigmaFan x V E w u = u := by rw [sigmaFan, if_pos hSfull]
    have huin : u ∈ setOfEdge w V' E' := by rw [← hσu]; exact hσ
    have hSrst : setOfEdge w V' E' = {u} := by
      apply Set.ext
      intro a
      constructor
      · intro ha
        have ha' : a ∈ setOfEdge w V E := hsub a ha
        rw [hSfull] at ha'
        simpa using ha'
      · intro ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact huin
    rw [hσu, sigmaFan, if_pos hSrst]
  · -- 全扇邻集非单点：极小性互夹 + azim 唯一性
    obtain ⟨hσS, hσne, hσmin⟩ := SIGMA_FAN hSfull hfan (hsub u hu)
    by_cases hSrst : setOfEdge w V' E' = {u}
    · -- 受限邻集单点：σ_full u ∈ S_rst = {u} 与 σ_full ≠ u 矛盾
      exfalso
      have hmem : sigmaFan x V E w u = u := by
        have h1 : sigmaFan x V E w u ∈ ({u} : Set V3) := hSrst ▸ hσ
        simpa using h1
      exact hσne hmem
    · obtain ⟨hσS', hσne', hσmin'⟩ := SIGMA_FAN hSrst hfan' hu
      have hwu : {w, u} ∈ E :=
        (properties_of_setOfEdge_fan x V E w u hfan).mpr (hsub u hu)
      have hfullE : {w, sigmaFan x V E w u} ∈ E :=
        (properties_of_setOfEdge_fan x V E w _ hfan).mpr hσS
      have hrstfull : sigmaFan x V' E' w u ∈ setOfEdge w V E := hsub _ hσS'
      have hrstE : {w, sigmaFan x V' E' w u} ∈ E :=
        (properties_of_setOfEdge_fan x V E w _ hfan).mpr hrstfull
      have hle1 : azim x w u (sigmaFan x V E w u)
          ≤ azim x w u (sigmaFan x V' E' w u) := hσmin _ hrstfull hσne'
      have hle2 : azim x w u (sigmaFan x V' E' w u)
          ≤ azim x w u (sigmaFan x V E w u) := hσmin' _ hσ hσne
      exact unique_azim_point_fan hfan hwu hfullE hrstE (le_antisymm hle1 hle2)

/-! ### 受限邻集 ⊆ 全邻集 -/

/-- 受限扇（vPrime, ePrime）的 c-邻集 ⊆ 全扇 c-邻集
（yk2_setOfEdge_ePrime_eq + 面轨道 ⊆ dart1）。 -/
private theorem yk7_setOfEdge_rst_subset (hfan : FAN x V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) (c : V3) :
    setOfEdge c (vPrime_p2 V f) (ePrime_p2 E f) ⊆ setOfEdge c V E := by
  intro u hu
  rw [yk2_setOfEdge_ePrime_eq hfan b hb f hf c] at hu
  obtain ⟨_huV, hd | hd⟩ := Set.mem_setOf_eq.mp hu
  · have hd1 : (c, u) ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hd)
    exact (properties_of_setOfEdge_fan x V E c u hfan).mp hd1
  · have hd1 : (u, c) ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hd)
    have hucE : ({u, c} : Set V3) ∈ E := hd1
    have hce : ({u, c} : Set V3) = ({c, u} : Set V3) := by
      ext p; simp; tauto
    rw [hce] at hucE
    exact (properties_of_setOfEdge_fan x V E c u hfan).mp hucE

/-! ### checkpoint 2 残差主件：σ′ 逐点一致 -/

/-- **σ′ 逐点一致（HOL IN_FF_FACE_MAP_IDE 的 TameLp/y-kit 形式，
LOCALIZE_PRESERVE_FACE 的 ②）**：受限扇超图 H′ 的 faceMap 与全扇超图 H 的
faceMap 在面轨道 f 上逐点一致。核心：d = (a,c) ∈ f 时 H.faceMap d = (c,t)
（t = σ_c⁻¹ a）且 (c,t) ∈ f（轨道闭包），由此 t ∈ 受限 c-邻集
（yk2_setOfEdge_ePrime_eq）；σ_full c t = a ∈ 受限集，经 `yk7_sigma_agree`
得 σ_rst c t = a，再由受限侧 invFun 唯一前驱刻画收口。 -/
private theorem yk7_hagree (hfan : FAN x V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b)
    (hfan' : FAN x (vPrime_p2 V f) (ePrime_p2 E f)) (d : V3 × V3)
    (hd : d ∈ f) :
    (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d
      = (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan)) d := by
  obtain ⟨a, c⟩ := d
  -- 全扇侧 faceMap 显式值
  have hd1 : (a, c) ∈ dart1OfFan V E :=
    yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hd)
  have hH : (@Hypermap.faceMap (V3 × V3) (fun a' b' => instDecidableEqProd a' b')
      (hypermapOfFan x V E hfan)) (a, c) = (c, inverseSigmaFan x V E c a) := by
    rw [yk2_apply_faceMap hfan (a, c), if_pos hd1]
    rfl
  -- (c, t) ∈ f（t := inverseSigmaFan x V E c a）：轨道闭包
  have hct : (c, inverseSigmaFan x V E c a) ∈ f := by
    rw [← hH, hf]
    exact yk2_faceOrbit_closure hfan (hf ▸ hd)
  have hct1 : (c, inverseSigmaFan x V E c a) ∈ dart1OfFan V E :=
    yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hct)
  -- t ∈ V、t ∈ 全扇 c-邻集、t ∈ 受限 c-邻集
  have htinV : inverseSigmaFan x V E c a ∈ V :=
    (yk2_dart_fst_snd_mem_V hfan hct1).2
  have hctE : {c, inverseSigmaFan x V E c a} ∈ E := hct1
  have htSfull : inverseSigmaFan x V E c a ∈ setOfEdge c V E :=
    (properties_of_setOfEdge_fan x V E c _ hfan).mp hctE
  have htSrst : inverseSigmaFan x V E c a
      ∈ setOfEdge c (vPrime_p2 V f) (ePrime_p2 E f) := by
    rw [yk2_setOfEdge_ePrime_eq hfan b hb f hf c]
    exact Set.mem_setOf_eq.mpr ⟨htinV, Or.inl hct⟩
  -- 全扇 σ_c t = a（invFun 谱：permutes_sigma_fan + 抽屉给存在性）
  have hainV : a ∈ V := (yk2_dart_fst_snd_mem_V hfan hd1).1
  have hacE : ({c, a} : Set V3) = ({a, c} : Set V3) := by
    ext p; simp; tauto
  have hcaE : ({c, a} : Set V3) ∈ E := by
    rw [hacE]
    exact hd1
  have haSfull : a ∈ setOfEdge c V E :=
    (properties_of_setOfEdge_fan x V E c a hfan).mp hcaE
  have hpermF := permutes_sigma_fan hfan htSfull
  obtain ⟨s, _hsS, hsf⟩ := yk7_finite_surjOf_inj
    (remark_finite_fan1 c V E hfan.2.2.1.1) hpermF.1 hpermF.2.1 a haSfull
  have hFt : extensionSigmaFan x V E c (inverseSigmaFan x V E c a) = a :=
    Function.invFun_eq ⟨s, hsf⟩
  -- a ∈ 受限 c-邻集（(a,c) ∈ f 本身给）
  have haSrst : a ∈ setOfEdge c (vPrime_p2 V f) (ePrime_p2 E f) := by
    rw [yk2_setOfEdge_ePrime_eq hfan b hb f hf c]
    exact Set.mem_setOf_eq.mpr ⟨hainV, Or.inr hd⟩
  -- σ′ 一致于 t（yk7_sigma_agree：σ_full c t = a 落在受限集）
  have hσext : sigmaFan x V E c (inverseSigmaFan x V E c a)
      = extensionSigmaFan x V E c (inverseSigmaFan x V E c a) := by
    rw [extensionSigmaFan, if_neg (by simpa using htSfull)]
  have hσagree : sigmaFan x V E c (inverseSigmaFan x V E c a)
      = sigmaFan x (vPrime_p2 V f) (ePrime_p2 E f) c
        (inverseSigmaFan x V E c a) := by
    refine yk7_sigma_agree hfan hfan'
      (yk7_setOfEdge_rst_subset hfan b hb f hf c) htSrst ?_
    rw [hσext, hFt, yk2_setOfEdge_ePrime_eq hfan b hb f hf c]
    exact Set.mem_setOf_eq.mpr ⟨hainV, Or.inr hd⟩
  -- 受限侧：σ_rst c t = a ⟹ invFun（受限 extension）a = t
  have ht' : inverseSigmaFan x V E c a
      = inverseSigmaFan x (vPrime_p2 V f) (ePrime_p2 E f) c a := by
    refine (yk7_invFun_eq_of_apply
      ((permutes_sigma_fan hfan' htSrst).1)
      ((permutes_sigma_fan hfan' htSrst).2.1)
      ((permutes_sigma_fan hfan' htSrst).2.2) htSrst haSrst ?_).symm
    rw [extensionSigmaFan, if_neg (by simpa using htSrst), ← hσagree, hσext, hFt]
  -- 装配：H′.faceMap (a,c) = (c, t) = H.faceMap (a,c)
  have hd1' : (a, c) ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) := by
    have hmemE : ({a, c} : Set V3) ∈ ePrime_p2 E f := by
      have h0 := yk2_face_dart_mem_ePrime hfan b hb (hf ▸ hd)
      rw [← hf] at h0
      exact h0
    exact hmemE
  have hfinal : (@Hypermap.faceMap (V3 × V3) (fun a' b' => instDecidableEqProd a' b')
      (hypermapOfFan x (vPrime_p2 V f) (ePrime_p2 E f) hfan')) (a, c)
      = (c, inverseSigmaFan x (vPrime_p2 V f) (ePrime_p2 E f) c a) := by
    rw [yk2_apply_faceMap hfan' (a, c), if_pos hd1']
    rfl
  rw [hfinal, hH, ht']

/-! ### checkpoint 2 capstone：受限面轨道 = 全扇面轨道 -/

/-- **受限面轨道 = 全扇面轨道（HOL LOCALIZE_PRESERVE_FACE，LVDUCXU.hl:460
第一合取）**：受限扇超图 H′ 的 faceMap-基轨道 = 全扇 faceMap-轨道 f。
装配 = `yk2_orbit_ext_of_agree`（hbf 定义性 + hagree = `yk7_hagree` +
hclosed 随之）。checkpoint 2 闭环。 -/
private theorem yk7_FF_eq_faceOrbit (hfan : FAN x V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) :
    orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x (vPrime_p2 V f) (ePrime_p2 E f)
          (yk2_FAN_vPrime_ePrime hfan b hb f hf))) b = f := by
  refine @yk2_orbit_ext_of_agree (V3 × V3) (fun a b' => instDecidableEqProd a b')
    (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan))
    (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x (vPrime_p2 V f) (ePrime_p2 E f)
        (yk2_FAN_vPrime_ePrime hfan b hb f hf))) f b ?_ ?_ ?_ ?_
  · rw [hf]
    rfl
  · rw [hf]
    exact mem_orbitMap_self _ _
  · intro d hd
    rw [yk7_hagree hfan b hb f hf (yk2_FAN_vPrime_ePrime hfan b hb f hf) d hd]
  · intro d hd
    rw [yk7_hagree hfan b hb f hf (yk2_FAN_vPrime_ePrime hfan b hb f hf) d hd, hf]
    exact yk2_faceOrbit_closure hfan (hf ▸ hd)

/-! ### 9i. y-kit W6（Lane AE 2026-10-23）：装配波不受阻子件（全 private、零消费者）。

对应 lp_main_estimate-compiled.hl Face4/5/6 Std 装配波的五子项：
① `packing_v_prime`（:119，packing 的子集遗传）；③ `local_std` 绕行（:598，
Std 节边前提 = ESTD 定义性）+ 非边前提的 ¬E 情形（LpFan.3）；④ azim 桥
（tau_fun_local :201 的绕行；核心 = Lvducxu.AZIM_IN_FAN_EQ_IZIM_E_PRIME 的
V 线替代——LocalAuto10:579 sorried 巨件不再被消费）；⑤ tauFun↔tauVEF 帽石
（W2 `wk_f_surr_tauFun_eq_tauVEF` 对任意 E 成立，此处接 ④ 成套）。
②（4 ≤ ncard vPrime ≤ 6）上半 `ncard vPrime ≤ ncard f` 已落；下半
4 ≤ ncard vPrime 依赖面圈顶点两两相异（单圈性，checkpoint 2/3 族）——
不落，注记见块尾 NEEDS。

④ 的证法（新路线，本波主件）：σ 往返 `yk_invFunFFanPairExt_apply` 给
faceMap⁻¹ e = (σ_v w, v)，即 dart 的面前驱恰是 σ_v w（azim-后继）；
FullySurrounded 排 1 价分支（azimDart < π ⟹ 邻数 ≥ 2 ⟹ σ ≠ 自身）⟹
面前驱 ≠ e.2 且是 e'-邻域的合法候选；全扇侧 `SIGMA_FAN`（azim-min）与
受限侧 ε-min 性质互夹出等值。零单圈性假设、零面圈计数假设。 -/

variable {V : Set V3} {E : Set (Set V3)}

/-- ① `v_prime` ⊆ V（localization.hl:97 定义自带；lp_main_estimate:126
`v_prime_subset` 的内容）。 -/
private theorem yk6_vPrime_subset (f : Set (V3 × V3)) : vPrime_p2 V f ⊆ V := by
  intro v hv
  exact (Set.mem_setOf_eq.mp hv).1

/-- ① `packing_v_prime`（lp_main_estimate:119）：packing 对子集遗传
（Rdwkarc.PACKING_SUBSET 的内容；`Packing` 是逐点距离条件，子集平凡继承）。 -/
private theorem yk6_packing_vPrime (f : Set (V3 × V3)) (hpack : Packing V) :
    Packing (vPrime_p2 V f) := fun u hu v2 hv2 hlt =>
  hpack u (yk6_vPrime_subset f hu) v2 (yk6_vPrime_subset f hv2) hlt

/-- 装配前提 3 的 vPrime 侧：`v_prime` ⊆ ballAnnulus（v_prime_subset +
LpFan.4 的内容；`v_prime V f ⊆ V ⊆ ballAnnulus`）。 -/
private theorem yk6_vPrime_sub_ballAnnulus (f : Set (V3 × V3)) (hsub : V ⊆ ballAnnulus) :
    vPrime_p2 V f ⊆ ballAnnulus := fun v hv => hsub (yk6_vPrime_subset f hv)

/-- `in_e_prime`（lp_main_estimate:133）：e_prime 的无向刻画（纯集合簿记，
PER_SET2 路线）。 -/
private theorem yk6_in_ePrime (f : Set (V3 × V3)) (v w : V3) :
    {v, w} ∈ ePrime_p2 E f ↔ {v, w} ∈ E ∧ ((v, w) ∈ f ∨ (w, v) ∈ f) := by
  constructor
  · rintro ⟨a, c, heq, hEe, hac⟩
    rcases Set.pair_eq_pair_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨by rw [h1, h2]; exact hEe, Or.inl ?_⟩
      rw [h1, h2]
      exact hac
    · refine ⟨by rw [h1, h2, Set.pair_comm c a]; exact hEe, Or.inr ?_⟩
      rw [h1, h2]
      exact hac
  · rintro ⟨hEe, hd | hd⟩
    · exact ⟨v, w, rfl, hEe, hd⟩
    · refine ⟨w, v, (Set.pair_comm w v).symm, ?_, hd⟩
      rw [Set.pair_comm w v]
      exact hEe

/-- e_prime ⊆ E（定义自带；local_diag/std 绕行的公共引道）。 -/
private theorem yk6_ePrime_subset (f : Set (V3 × V3)) : ePrime_p2 E f ⊆ E := by
  intro e he
  obtain ⟨a, c, heq, hEe, -⟩ := Set.mem_setOf_eq.mp he
  rw [heq]
  exact hEe

/-- ③ `local_std` 绕行（lp_main_estimate:598 的 Std 节内容）：e_prime 的边
两端 `2 ≤ dist ≤ 2h0`（≥2 由 Packing + 两端 ∈ V，≤2h0 由 E = ESTD V 定义性）。
HOL 一般形是轨道迭代 IFF（f_surr_in_e_prime + 逐 k 枚举），Std 节只需本形。
~40 行内闭合，零阻塞。 -/
private theorem yk6_local_std (hfan : FAN 0 V (ESTD V)) (hpack : Packing V)
    (f : Set (V3 × V3)) {v w : V3} (he : {v, w} ∈ ePrime_p2 (ESTD V) f) :
    2 ≤ dist v w ∧ dist v w ≤ 2 * h0 := by
  obtain ⟨a, c, heq, hEe, hac⟩ := Set.mem_setOf_eq.mp he
  have hd1 : (a, c) ∈ dart1OfFan V (ESTD V) := hEe
  have hmemV := yk_in_dart_inV hfan hd1
  have hne : a ≠ c := edge_ne_of_fan hfan hd1
  have hge : 2 ≤ dist a c := Packing.dist_ge_two hpack hmemV.1 hmemV.2 hne
  have hle := (wk_estd_dist_le hEe).2
  rcases Set.pair_eq_pair_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [h1, h2]; exact hge, by rw [h1, h2]; exact hle⟩
  · exact ⟨by rw [h1, h2, dist_comm]; exact hge,
      by rw [h1, h2, dist_comm]; exact hle⟩

/-- ③ 非边前提的 ¬E 情形（LpFan.3 路线）。{a,b} ∈ E 的 chord 情形 = 真
blocked（HOL diag_not_in_dart:415 → fan_hypermaps_iso 链未移植），见块尾
NEEDS 注记；本件是 local_diag 绕行可闭合的一半。 -/
private theorem yk6_local_diag_notE (hlpfan : LpFan V E) (f : Set (V3 × V3))
    {a b : V3} (ha : a ∈ vPrime_p2 V f) (hb2 : b ∈ vPrime_p2 V f) (hab : a ≠ b)
    (hE : {a, b} ∉ E) : 2 * h0 ≤ dist a b := by
  have h2 : (2:ℝ) * h0 = 2.52 := by norm_num [h0]
  rw [h2]
  exact hlpfan.2.2.1 a b (yk6_vPrime_subset f ha) (yk6_vPrime_subset f hb2) hab hE

/-- FullySurrounded ⟹ dart 首∈点 ≥ 2 邻居（HOL
fully_surrounded_card_set_of_edge1 的折算；azimDart < π 排除 1 价 2π 分支）。 -/
private theorem yk6_fs_ncard_gt1 (hfan : FAN 0 V E) (hfs : FullySurrounded V E)
    {d : V3 × V3} (hd : d ∈ dart1OfFan V E) : 1 < (setOfEdge d.1 V E).ncard := by
  have hπ : azimDart V E d < Real.pi := hfs d (Set.mem_union_right _ hd)
  by_cases hnc : (setOfEdge d.1 V E).ncard > 1
  · exact hnc
  · have h2pi : azimDart V E d = (2 : ℝ) * Real.pi := by
      show (if d.1 = d.2 then (2 : ℝ) * Real.pi
        else if (setOfEdge d.1 V E).ncard > 1
          then azim 0 d.1 d.2 (sigmaFan 0 V E d.1 d.2) else 2 * Real.pi)
        = (2 : ℝ) * Real.pi
      rw [if_neg (edge_ne_of_fan hfan hd), if_neg hnc]
    rw [h2pi] at hπ
    linarith [Real.pi_pos]

/-- σ 的 ε-witness 三条件（ee-邻域版，无 FAN 假设；有限性外给）。
镜像 Fan.exists_sigmaFan + Fan.SIGMA_FAN（有限性来源不同：受限邻域 ⊆
全扇邻域，不经 fan1）。 -/
private theorem yk6_sigmaFan_min_ee {E' : Set (Set V3)} {v u : V3}
    (hfin : (ee v E').Finite) (hu : u ∈ ee v E') (hne : ee v E' ≠ {u}) :
    sigmaFan 0 Set.univ E' v u ∈ ee v E' ∧ sigmaFan 0 Set.univ E' v u ≠ u ∧
      ∀ w1 ∈ ee v E', w1 ≠ u → azim 0 v u (sigmaFan 0 Set.univ E' v u) ≤ azim 0 v u w1 := by
  have hsoe : setOfEdge v Set.univ E' = ee v E' := by
    ext z
    simp only [setOfEdge, ee, Set.mem_setOf_eq, Set.mem_univ, and_true]
  have hne2 : (ee v E' \ {u}).Nonempty := by
    by_contra hempty
    apply hne
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨hu, fun z hz => ?_⟩
    by_contra hzu
    exact hempty ⟨z, ⟨hz, by simp [hzu]⟩⟩
  have hfin2 : (ee v E' \ {u}).Finite := hfin.subset fun w hw => hw.1
  obtain ⟨p, hpmem, hpmin⟩ :=
    Set.exists_min_image (ee v E' \ {u}) (fun z => azim 0 v u z) hfin2 hne2
  rw [Set.mem_sdiff, Set.mem_singleton_iff] at hpmem
  have hwit : ∃ w : V3, w ∈ ee v E' ∧ w ≠ u ∧
      ∀ w1 ∈ ee v E', w1 ≠ u → azim 0 v u w ≤ azim 0 v u w1 :=
    ⟨p, hpmem.1, hpmem.2, fun w1 hw1 hw1u => hpmin w1 ⟨hw1, by simp [hw1u]⟩⟩
  unfold sigmaFan
  rw [hsoe, if_neg hne]
  exact Classical.epsilon_spec hwit

/-- ② 上半：`ncard vPrime ≤ ncard f`（fst-像包含 + ncard 单调；零单圈性
假设）。下半 `4 ≤ ncard vPrime` 依赖面圈顶点两两相异（单圈性，checkpoint
2/3 族），不落——见块尾 NEEDS。 -/
private theorem yk6_ncard_vPrime_le (hfan : FAN 0 V E) (b : V3 × V3)
    (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) : (vPrime_p2 V f).ncard ≤ f.ncard := by
  have hfin : f.Finite := by
    rw [hf]
    exact orbitMap_finite
      (@Hypermap.faceMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 V E hfan)) b
  have hsub : vPrime_p2 V f ⊆ (fun d : V3 × V3 => d.1) '' f := by
    intro v hv
    obtain ⟨-, w, hw⟩ := Set.mem_setOf_eq.mp hv
    exact ⟨(v, w), hw, rfl⟩
  have h1 : (vPrime_p2 V f).ncard ≤ ((fun d : V3 × V3 => d.1) '' f).ncard :=
    Set.ncard_le_ncard hsub (Set.Finite.image (fun d : V3 × V3 => d.1) hfin)
  have h2 : ((fun d : V3 × V3 => d.1) '' f).ncard ≤ f.ncard :=
    Set.ncard_image_le hfin
  exact h1.trans h2

/-- ④ azim 桥（点态核心）：面轨道上 `azimInFan` 在 e' = ePrime E f 限制下
不变。V 线替代 HOL `AZIM_IN_FAN_EQ_IZIM_E_PRIME`（Lvducxu，LocalAuto10:579
sorried 巨件）——本波主件；零单圈性假设，唯一几何输入 = FullySurrounded
排 1 价分支。 -/
private theorem yk6_azimInFan_ePrime_eq (hfan : FAN 0 V E) (hfs : FullySurrounded V E)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) {e : V3 × V3} (he : e ∈ f) :
    azimInFan e (ePrime_p2 E f) = azimInFan e E := by
  have he' : e ∈ yk2_faceOrbit 0 V E hfan b := by rw [← hf]; exact he
  have hd1 : e ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb he'
  -- σ 往返：faceMap⁻¹ e = (σ_v w, v)（yk_invFunFFanPairExt_apply 的显式形）
  have hco : (⇑(@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 V E hfan))) = fFanPairExt 0 V E :=
    funext fun z => yk2_apply_faceMap hfan z
  have hsymm_mem' : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 V E hfan)).symm e ∈ yk2_faceOrbit 0 V E hfan b :=
    yk2_faceOrbit_symm_closure hfan he'
  have hsymm_mem : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 V E hfan)).symm e ∈ f := by rw [hf]; exact hsymm_mem'
  have hinv : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 V E hfan)).symm e = Function.invFun (fFanPairExt 0 V E) e := by
    have h0 : (⇑(@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 V E hfan)))
        (Function.invFun (⇑(@Hypermap.faceMap (V3 × V3)
          (fun a b' => instDecidableEqProd a b') (hypermapOfFan 0 V E hfan))) e) = e :=
      Function.invFun_eq ⟨(@Hypermap.faceMap (V3 × V3)
        (fun a b' => instDecidableEqProd a b') (hypermapOfFan 0 V E hfan)).symm e,
        Equiv.apply_symm_apply _ _⟩
    have h1 := (Equiv.apply_eq_iff_eq_symm_apply
      (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 V E hfan))).mp h0
    rw [hco] at h1
    exact h1.symm
  rw [hinv, yk_invFunFFanPairExt_apply hfan e, if_pos hd1] at hsymm_mem
  rw [hinv, yk_invFunFFanPairExt_apply hfan e, if_pos hd1] at hsymm_mem'
  -- hsymm_mem : (sigmaFan 0 V E e.1 e.2, e.1) ∈ f
  have hsig_dart : (sigmaFan 0 V E e.1 e.2, e.1) ∈ dart1OfFan V E :=
    yk2_faceOrbit_subset_dart1 hfan b hb hsymm_mem'
  have hsigE : ({sigmaFan 0 V E e.1 e.2, e.1} : Set V3) ∈ E := hsig_dart
  -- 受限邻域的两个相异元
  have hN'e : e.2 ∈ ee e.1 (ePrime_p2 E f) :=
    (yk6_in_ePrime f e.1 e.2).mpr ⟨hd1, Or.inl he⟩
  have hN'σ : sigmaFan 0 V E e.1 e.2 ∈ ee e.1 (ePrime_p2 E f) :=
    (yk6_in_ePrime f e.1 (sigmaFan 0 V E e.1 e.2)).mpr
      ⟨by rw [Set.pair_comm e.1 (sigmaFan 0 V E e.1 e.2)]; exact hsigE,
        Or.inr hsymm_mem⟩
  -- σ ≠ e.2：全扇邻域 ≥ 2 排唯一邻居分支（FullySurrounded 的内容）
  have hsoe_ne : setOfEdge e.1 V E ≠ {e.2} := by
    intro hc
    exact absurd (yk6_fs_ncard_gt1 hfan hfs hd1) (by rw [hc]; simp)
  have hsigne : sigmaFan 0 V E e.1 e.2 ≠ e.2 := by
    by_cases hsoe1 : setOfEdge e.1 V E = {e.2}
    · exact absurd hsoe1 hsoe_ne
    · exact (SIGMA_FAN hsoe1 hfan
        (FAN_in_setOfEdge 0 V E e.1 e.2 hfan hd1).2.2.1).2.1
  -- 分支条件
  have hfinN' : (ee e.1 (ePrime_p2 E f)).Finite := by
    have hfin0 : (setOfEdge e.1 V E).Finite := remark_finite_fan1 e.1 V E hfan.2.2.1.1
    have hsub : ee e.1 (ePrime_p2 E f) ⊆ setOfEdge e.1 V E := by
      intro z hz
      have hz2 : {e.1, z} ∈ E := yk6_ePrime_subset f hz
      exact ⟨hz2, FAN_EDGE_EL_V hfan hz2⟩
    exact hfin0.subset hsub
  have hpair2 : ({e.2, sigmaFan 0 V E e.1 e.2} : Set V3) ⊆ ee e.1 (ePrime_p2 E f) := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hN'e
    · rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hN'σ
  have hn'E : 1 < (ee e.1 (ePrime_p2 E f)).ncard := by
    have hc1 : ({e.2, sigmaFan 0 V E e.1 e.2} : Set V3).ncard
        ≤ (ee e.1 (ePrime_p2 E f)).ncard := Set.ncard_le_ncard hpair2 hfinN'
    have hc2 : ({e.2, sigmaFan 0 V E e.1 e.2} : Set V3).ncard = 2 :=
      Set.ncard_pair hsigne.symm
    omega
  have hfullE : 1 < (ee e.1 E).ncard := by
    rw [wk_ee_eq_setOfEdge hfan e.1]
    exact yk6_fs_ncard_gt1 hfan hfs hd1
  -- 值的计算：两侧分支进 azim 形，min 性质互夹
  unfold azimInFan
  rw [if_pos hn'E, if_pos hfullE, wk_sigmaFan_congr hfan]
  have hsoe' : setOfEdge e.1 Set.univ (ePrime_p2 E f) = ee e.1 (ePrime_p2 E f) := by
    ext z
    simp only [setOfEdge, ee, Set.mem_setOf_eq, Set.mem_univ, and_true]
  obtain ⟨hσ'1, hσ'2, hσ'3⟩ :=
    yk6_sigmaFan_min_ee (E' := ePrime_p2 E f) (v := e.1) (u := e.2) hfinN' hN'e
      (fun hc => by rw [hc] at hn'E; simp at hn'E)
  have hle1 : azim 0 e.1 e.2 (sigmaFan 0 Set.univ (ePrime_p2 E f) e.1 e.2)
      ≤ azim 0 e.1 e.2 (sigmaFan 0 V E e.1 e.2) := hσ'3 _ hN'σ hsigne
  have hσ'insoe : sigmaFan 0 Set.univ (ePrime_p2 E f) e.1 e.2 ∈ setOfEdge e.1 V E := by
    have hz2 : {e.1, sigmaFan 0 Set.univ (ePrime_p2 E f) e.1 e.2} ∈ E :=
      yk6_ePrime_subset f hσ'1
    exact ⟨hz2, FAN_EDGE_EL_V hfan hz2⟩
  have hle2 : azim 0 e.1 e.2 (sigmaFan 0 V E e.1 e.2)
      ≤ azim 0 e.1 e.2 (sigmaFan 0 Set.univ (ePrime_p2 E f) e.1 e.2) :=
    (SIGMA_FAN hsoe_ne hfan (FAN_in_setOfEdge 0 V E e.1 e.2 hfan hd1).2.2.1).2.2 _
      hσ'insoe hσ'2
  exact le_antisymm hle1 hle2

/-- ④ 装配形：`tauFun (vPrime, ePrime) f = tauFun V E f`（点态桥 + setSum
congr；tauFun 的 V 槽不进 body，差只在逐 dart 的 azimInFan）。 -/
private theorem yk6_tauFun_ePrime_eq (hfan : FAN 0 V E) (hfs : FullySurrounded V E)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) :
    tauFun (vPrime_p2 V f) (ePrime_p2 E f) f = tauFun V E f := by
  unfold tauFun
  congr 1
  exact wk_setSum_congr (fun d hd => by
    rw [yk6_azimInFan_ePrime_eq hfan hfs b hb f hf hd])

/-- ⑤ 帽石：`tauVEF V (ESTD V) f = tauFun (vPrime, ePrime) f`（④ + W2 ⑤ 桥
`wk_f_surr_tauFun_eq_tauVEF`（对任意 E 成立）成套；FaceK Std 装配的回写形）。 -/
private theorem yk6_tauVEF_eq_tauFun_ePrime (hlpfan : LpFan V (ESTD V))
    (b : V3 × V3) (hb : b ∈ dart1OfFan V (ESTD V)) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V (ESTD V) hlpfan.1 b) :
    tauVEF_p2 V (ESTD V) f = tauFun (vPrime_p2 V f) (ePrime_p2 (ESTD V) f) f := by
  have hfsin : f ∈ (hypermapOfFanTl V (ESTD V) hlpfan.1).faceSet := by
    rw [hf, Hypermap.faceSet, setOfOrbits]
    refine ⟨b, Finset.mem_coe.mpr (?_ : b ∈
      (↑(hypermapOfFanTl V (ESTD V) hlpfan.1).darts : Set (V3 × V3))), rfl⟩
    rw [dartsTl_coe]
    exact hb
  rw [yk6_tauFun_ePrime_eq hlpfan.1 hlpfan.2.1 b hb f hf]
  exact (wk_f_surr_tauFun_eq_tauVEF hlpfan.1 hlpfan.2.1 hlpfan.2.2.2.1 hfsin).symm

/-! **NEEDS（W6 不受阻子件之外的残差，Lane AE 2026-10-23 勘察）**：
1. ② 下半 `4 ≤ ncard vPrime`（LOFA_IMP_CARD_FF_V_EQ）：面圈顶点两两相异
   = 单圈性（W2a，checkpoint 2/3 族）——本波不落，随 W6 残差波收。
2. ③ 非边前提的 chord 情形（{a,b} ∈ E、两向 dart 均不在 f）= 真 blocked：
   HOL local_diag:581 第二支消费 `diag_not_in_dart`（lp_main_estimate:415），
   后者走 `fan_hypermaps_iso_explicit2`（= Hypermap_iso.fan_hypermaps_iso +
   Conforming.SRPRNPL，与 checkpoint 2 同源）+ PROPERTIES_TRIANGLE_FAN
   （planarity 章）。**"local_diag 绕行 ~20 行"的原估漏了这一支**——装配波
   供给 JEJTVGB_std_concl 前提 6 时，除 LpFan.3 外还需面无弦引理；两条路：
   (a) planarity 章移植专项（PROPERTIES_TRIANGLE_FAN 组），(b) checkpoint 2
   的 fan_hypermaps_iso 落地后抄 HOL 的 card_orbit 论证。
3. 装配波的其余前置（ConvexLocalFan 合取支的 wedge 面 + LocalFan/Dih2k 面）
   状态与 §9h.1 的施工图一致，本块未动。 -/

/-! ### 9j. y-kit 收官波（Lane AJ 2026-10-23）：checkpoint 3 Dih2k + ncard vPrime 下半
（全 private yk8_*、零外部消费者、纯追加）。

两件定案：
1. **ncard vPrime 下半（真单圈性）**：`4 ≤ ncard vPrime`。链：σ-轨道单循环覆盖
   （yk8_sigmaOrbitCovers，LpSemantics.lpSigmaOrbitCovers 的 TameLp 本地孪生——
   LpSemantics import 本模块，方向相反不可引，逐字镜像重证）+
   ConformingAuto1.SRPRNPL（:737，public、本模块可见）的 Simple ⟹ 面圈顶点
   两两相异（fst/snd 单射）⟹ ncard f = ncard fst″f ≤ ncard vPrime，与 AE 上半
   `yk6_ncard_vPrime_le` 拼接成等式，再由 `4 ≤ ncard f`（tau4/5/6 章 dartsK
   k ∈ {4,5,6} 供给）得 `4 ≤ ncard vPrime`。
2. **checkpoint 3·Dih2k**：受限超图 Dih2k 构造（HOL DIH_K_HYP_E_PRIME，
   LVDUCXU.hl:2086 的 Lean 折算）：单圈性 + 2 < ncard f ⟹ f ∩ swap″f = ∅、
   每面顶点 |N′| = 2、σ′ 对合 ⟹ darts′ 基数 2k、faceMap-轨道二分解、
   HasOrders face k / edge 2 / node 2，capstone `Dih2k H′ f.ncard`。
孪生与去重路径：yk8_sigma* 五件与 LpSemantics.lpSigma*（A1/A2/A3/A5-pre/A5）
同陈述孪生；若未来 σ-循环理论下沉 Fan.lean，两侧同步收敛删除。 -/

/-! ### 9j.0 σ-循环理论五件（LpSemantics A1/A2/A3/A5-pre/A5 的 TameLp 孪生，
单循环性原料；LP 模块 import 本模块，import 方向相反不可直接引）。 -/

set_option maxHeartbeats 1000000 in
/-- A1 孪生：HOL MONO_AZIM_SIGMA_FAN（topology.hl:29）；LpSemantics.lpMonoAzimSigma
同陈述。 -/
private theorem yk8_monoAzimSigma {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hu : {v, u} ∈ E) (hw : {v, w} ∈ E)
    (hne : sigmaFan x V E v w ≠ u) :
    azim x v u w ≤ azim x v u (sigmaFan x V E v w) := by
  have huS : u ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v u hfan).mp hu
  have hwS : w ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v w hfan).mp hw
  rcases eq_or_ne u w with huw | huw
  · rw [huw, azim_self]
    exact azim_nonneg x v w (sigmaFan x V E v w)
  by_cases hsw : setOfEdge v V E = {w}
  · exfalso
    have huw2 : u = w := by
      have hmem : u ∈ ({w} : Set V3) := hsw ▸ huS
      simpa using hmem
    exact huw huw2
  obtain ⟨hσS, hσne, hmin⟩ := SIGMA_FAN hsw hfan hwS
  have hσE : {v, sigmaFan x V E v w} ∈ E :=
    (properties_of_setOfEdge_fan x V E v _ hfan).mpr hσS
  by_contra hcon
  have hgt : azim x v u (sigmaFan x V E v w) < azim x v u w := not_le.mp hcon
  have hsum : azim x v u w =
      azim x v u (sigmaFan x V E v w) + azim x v (sigmaFan x V E v w) w :=
    sum2_azim_fan hfan hu hσE hw hgt.le
  have hne0 : azim x v w (sigmaFan x V E v w) ≠ 0 := by
    intro h0
    exact hσne (unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v) (u := w)
      (w := sigmaFan x V E v w) hfan hw hσE h0).symm
  have hC1 : azim x v (sigmaFan x V E v w) w
      = if azim x v w (sigmaFan x V E v w) = 0 then 0
        else 2 * Real.pi - azim x v w (sigmaFan x V E v w) :=
    azim_compl (z := x) (w := v) (w1 := w) (w2 := sigmaFan x V E v w)
      (fan_not_collinear hfan hw) (fan_not_collinear hfan hσE)
  rw [if_neg hne0] at hC1
  have hwu0 : azim x v u w ≠ 0 := by
    intro h0
    exact huw (unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v) (u := u)
      (w := w) hfan hu hw h0)
  have hC2 : azim x v w u
      = if azim x v u w = 0 then 0 else 2 * Real.pi - azim x v u w :=
    azim_compl (z := x) (w := v) (w1 := u) (w2 := w)
      (fan_not_collinear hfan hu) (fan_not_collinear hfan hw)
  rw [if_neg hwu0] at hC2
  have hminw : azim x v w (sigmaFan x V E v w) ≤ azim x v w u := hmin u huS huw
  have hnn : 0 ≤ azim x v u (sigmaFan x V E v w) :=
    azim_nonneg x v u (sigmaFan x V E v w)
  have hkey : azim x v u w = azim x v u (sigmaFan x V E v w) + azim x v u w := by
    rw [hsum, hC1]
    linarith [hminw, hC2]
  have hzero : azim x v u (sigmaFan x V E v w) = 0 := by linarith
  exact hne (unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v) (u := u)
    (w := sigmaFan x V E v w) hfan hu hσE hzero).symm

/-- A2 孪生：σ 的迭代在邻集上单射；LpSemantics.lpSigmaIterInject 同陈述。 -/
private theorem yk8_sigmaIterInject {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v : V3} {a b : V3}
    (ha : a ∈ setOfEdge v V E) (hb : b ∈ setOfEdge v V E) :
    ∀ i : ℕ, (sigmaFan x V E v)^[i] a = (sigmaFan x V E v)^[i] b → a = b := by
  intro i
  induction i with
  | zero => exact fun heq => heq
  | succ i ih =>
    intro heq
    refine ih ?_
    have haE : {v, a} ∈ E := (properties_of_setOfEdge_fan x V E v a hfan).mpr ha
    have hbE : {v, b} ∈ E := (properties_of_setOfEdge_fan x V E v b hfan).mpr hb
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at heq
    exact mono_sigma_fan hfan (image_power_map_points hfan haE i)
      (image_power_map_points hfan hbE i) heq

/-- A3 孪生：σ-轨道首回存在且可取极小（鸽笼 + 迭代单射 + Nat.find）；
LpSemantics.lpSigmaFirstReturn 同陈述。 -/
private theorem yk8_sigmaFirstReturn {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hV : V.Finite) {v u : V3} (hu : {v, u} ∈ E) :
    ∃ k : ℕ, 1 ≤ k ∧ (sigmaFan x V E v)^[k] u = u ∧
      ∀ t : ℕ, 0 < t → t < k → (sigmaFan x V E v)^[t] u ≠ u := by
  have hfin : (setOfEdge v V E).Finite := remark_finite_fan1 v V E hV
  have hnotinj : ¬ Function.Injective (fun n : ℕ => (sigmaFan x V E v)^[n] u) := by
    intro hinj
    have h1 : (Set.range fun n : ℕ => (sigmaFan x V E v)^[n] u).Infinite :=
      Set.infinite_range_of_injective hinj
    have h2 : (Set.range fun n : ℕ => (sigmaFan x V E v)^[n] u).Finite :=
      hfin.subset (fun y hy => by
        obtain ⟨n, hn2⟩ := hy
        exact hn2 ▸ image_power_map_points hfan hu n)
    exact h2.not_infinite h1
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hnotinj
  have hshift : ∃ k : ℕ, 1 ≤ k ∧ (sigmaFan x V E v)^[k] u = u := by
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨j - i, by omega, ?_⟩
      have hidx : i + (j - i) = j := by omega
      have hstep : (sigmaFan x V E v)^[i] ((sigmaFan x V E v)^[j - i] u)
          = (sigmaFan x V E v)^[i] u := by
        rw [← Function.iterate_add_apply, hidx, heq]
      have huS : u ∈ setOfEdge v V E :=
        (properties_of_setOfEdge_fan x V E v u hfan).mp hu
      have hm1 : (sigmaFan x V E v)^[j - i] u ∈ setOfEdge v V E :=
        image_power_map_points hfan hu (j - i)
      exact yk8_sigmaIterInject hfan hm1 huS i hstep
    · refine ⟨i - j, by omega, ?_⟩
      have hjd : j + (i - j) = i := by omega
      have hstep : (sigmaFan x V E v)^[j] ((sigmaFan x V E v)^[i - j] u)
          = (sigmaFan x V E v)^[j] u := by
        rw [← Function.iterate_add_apply, hjd, ← heq]
      have huS : u ∈ setOfEdge v V E :=
        (properties_of_setOfEdge_fan x V E v u hfan).mp hu
      have hm1 : (sigmaFan x V E v)^[i - j] u ∈ setOfEdge v V E :=
        image_power_map_points hfan hu (i - j)
      exact yk8_sigmaIterInject hfan hm1 huS j hstep
  obtain ⟨k0, hk01, hk0⟩ := hshift
  have hex : ∃ n : ℕ, 1 ≤ n ∧ (sigmaFan x V E v)^[n] u = u := ⟨k0, hk01, hk0⟩
  refine ⟨Nat.find hex, Nat.find_spec hex |>.1, Nat.find_spec hex |>.2, ?_⟩
  intro t ht0 htk hcon
  exact Nat.find_min hex htk ⟨ht0, hcon⟩

/-- A5 前置孪生：轨道点互异（首回极小性直接推论）；
LpSemantics.lpSigmaCycleDistinct 同陈述。 -/
private theorem yk8_sigmaCycleDistinct {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v u : V3} (hu : {v, u} ∈ E) {k : ℕ}
    (hmin : ∀ t : ℕ, 0 < t → t < k → (sigmaFan x V E v)^[t] u ≠ u)
    (t1 t2 : ℕ) (h12 : t1 < t2) (h2k : t2 < k) :
    (sigmaFan x V E v)^[t1] u ≠ (sigmaFan x V E v)^[t2] u := by
  intro heq
  have huS : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hu
  have hshift : (sigmaFan x V E v)^[t1] ((sigmaFan x V E v)^[t2 - t1] u)
      = (sigmaFan x V E v)^[t1] u := by
    rw [← Function.iterate_add_apply]
    have : t1 + (t2 - t1) = t2 := by omega
    rw [this, heq]
  have huS2 : (sigmaFan x V E v)^[t2 - t1] u ∈ setOfEdge v V E :=
    image_power_map_points hfan hu (t2 - t1)
  exact hmin (t2 - t1) (by omega) (by omega)
    (yk8_sigmaIterInject hfan huS2 huS t1 hshift)

set_option maxHeartbeats 1000000 in
/-- A5 孪生：σ-轨道覆盖整个邻集（单循环性核心；HOL key_lemma_cyclic_fan +
ORBITS_EQ_SET_EDGE_FAN 合并重构，两案例矛盾）；
LpSemantics.lpSigmaOrbitCovers 同陈述。 -/
private theorem yk8_sigmaOrbitCovers {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hV : V.Finite) {v w : V3} (hw : {v, w} ∈ E) :
    ∀ a ∈ setOfEdge v V E, ∃ n : ℕ, (sigmaFan x V E v)^[n] w = a := by
  have hwS : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w hfan).mp hw
  by_cases hSing : setOfEdge v V E = {w}
  · intro a ha
    have : a = w := by
      have : a ∈ ({w} : Set V3) := hSing ▸ ha
      simpa using this
    exact ⟨0, this.symm⟩
  intro a ha
  by_contra haO
  have haE : {v, a} ∈ E := (properties_of_setOfEdge_fan x V E v a hfan).mpr ha
  have haw : a ≠ w := fun he => haO ⟨0, he.symm⟩
  obtain ⟨k, hk1, hkw, hmin⟩ := yk8_sigmaFirstReturn hfan hV hw
  have hk2 : 2 ≤ k := by
    by_contra hk
    have hk1' : k = 1 := by omega
    have hσw : (sigmaFan x V E v)^[1] w = w := by
      rw [← hk1']; exact hkw
    exact (SIGMA_FAN hSing hfan hwS).2.1 (by simpa using hσw)
  have hdist : ∀ (t1 t2 : ℕ), t1 < t2 → t2 < k →
      (sigmaFan x V E v)^[t1] w ≠ (sigmaFan x V E v)^[t2] w :=
    yk8_sigmaCycleDistinct (x := x) (V := V) (E := E) hfan hw hmin
  have hEof : ∀ p : V3, p ∈ setOfEdge v V E → {v, p} ∈ E :=
    fun p hp => (properties_of_setOfEdge_fan x V E v p hfan).mpr hp
  have hinjθ : ∀ p q : V3, p ∈ setOfEdge v V E → q ∈ setOfEdge v V E → p ≠ q →
      azim x v w p ≠ azim x v w q := by
    intro p q hpS hqS hpq heq
    exact hpq (unique_azim_point_fan (x := x) (V := V) (E := E) (v := v)
      (u := w) (w := p) (w1 := q) hfan hw (hEof p hpS) (hEof q hqS) heq)
  have hacyc : ∀ j : ℕ, j < k → (sigmaFan x V E v)^[j] w ≠ a := by
    intro j hj heqj
    exact haO ⟨j, heqj⟩
  have hpowS : ∀ j : ℕ, (sigmaFan x V E v)^[j] w ∈ setOfEdge v V E :=
    image_power_map_points hfan hw
  have h1lt : azim x v w ((sigmaFan x V E v)^[1] w) < azim x v w a := by
    have hmin1 : azim x v w (sigmaFan x V E v w)
        ≤ azim x v w a := (SIGMA_FAN hSing hfan hwS).2.2 a ha haw
    have hpq : sigmaFan x V E v w ≠ a := by
      intro he
      exact hacyc 1 (by omega) he
    have hσwS : sigmaFan x V E v w ∈ setOfEdge v V E :=
      sigma_fan_in_setOfEdge hfan hwS
    have hneq : azim x v w (sigmaFan x V E v w) ≠ azim x v w a :=
      fun he => hinjθ (sigmaFan x V E v w) a hσwS ha hpq he
    have hσ1 : (sigmaFan x V E v)^[1] w = sigmaFan x V E v w := rfl
    rw [hσ1]
    exact lt_of_le_of_ne hmin1 hneq
  by_cases hA : azim x v w ((sigmaFan x V E v)^[k - 1] w) < azim x v w a
  · exfalso
    set uk1 := (sigmaFan x V E v)^[k - 1] w with huk1
    have huk1S : uk1 ∈ setOfEdge v V E := hpowS (k - 1)
    have hwuk1 : w ≠ uk1 := hdist 0 (k - 1) (by omega) (by omega)
    have hauk1 : a ≠ uk1 := by
      intro he
      exact hacyc (k - 1) (by omega) he.symm
    have hσk : (sigmaFan x V E v)^[k] w = sigmaFan x V E v uk1 := by
      have hkeq : k = k - 1 + 1 := by omega
      rw [hkeq, Function.iterate_succ_apply', huk1]
    have hσkw : sigmaFan x V E v uk1 = w := by
      have h1 := hkw
      rw [hσk] at h1
      exact h1
    have hSne : setOfEdge v V E ≠ {uk1} := by
      intro he
      have hac : a ∈ ({uk1} : Set V3) := by rw [← he]; exact ha
      exact hauk1 (by simpa using hac)
    have hminU := (SIGMA_FAN hSne hfan huk1S).2.2 a ha hauk1
    rw [hσkw] at hminU
    have hθk1 : azim x v w uk1 ≠ 0 := by
      intro h0
      exact hwuk1 (unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v)
        (u := w) (w := uk1) hfan hw (hEof uk1 huk1S) h0)
    have hC1 : azim x v uk1 w
        = if azim x v w uk1 = 0 then 0
          else 2 * Real.pi - azim x v w uk1 :=
      azim_compl (z := x) (w := v) (w1 := w) (w2 := uk1)
        (fan_not_collinear hfan hw) (fan_not_collinear hfan (hEof uk1 huk1S))
    rw [if_neg hθk1] at hC1
    have hsumA : azim x v w a = azim x v w uk1 + azim x v uk1 a :=
      sum2_azim_fan hfan hw (hEof uk1 huk1S) (hEof a ha) hA.le
    have hlt2 : azim x v w a < 2 * Real.pi := azim_lt_two_pi x v w a
    linarith
  · exfalso
    have hBle : azim x v w a ≤ azim x v w ((sigmaFan x V E v)^[k - 1] w) :=
      le_of_not_gt hA
    have hauk1 : a ≠ (sigmaFan x V E v)^[k - 1] w := by
      intro he
      exact hacyc (k - 1) (by omega) he.symm
    have hBne : azim x v w a ≠ azim x v w ((sigmaFan x V E v)^[k - 1] w) :=
      fun he => hinjθ a ((sigmaFan x V E v)^[k - 1] w) ha
        (hpowS (k - 1)) hauk1 he
    have hB : azim x v w a < azim x v w ((sigmaFan x V E v)^[k - 1] w) :=
      lt_of_le_of_ne hBle hBne
    set T : Finset ℕ :=
      (Finset.Icc 1 (k - 1)).filter
        (fun j => decide (azim x v w ((sigmaFan x V E v)^[j] w) < azim x v w a))
      with hT
    have h1T : 1 ∈ T := by
      rw [hT]
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega), ?_⟩
      have hσ1 : (sigmaFan x V E v)^[1] w = sigmaFan x V E v w := rfl
      exact decide_eq_true (by rw [hσ1]; exact h1lt)
    have hTne : T.Nonempty := ⟨1, h1T⟩
    set jmax := T.max' hTne with hj
    have hjmem := T.max'_mem hTne
    obtain ⟨hjI, hjlt⟩ := Finset.mem_filter.mp hjmem
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hjI
    have hjltP : azim x v w ((sigmaFan x V E v)^[jmax] w) < azim x v w a :=
      decide_eq_true_iff.mp hjlt
    have hjk1 : jmax < k - 1 := by
      by_contra hcon
      have hjE : jmax = k - 1 := by omega
      rw [hjE] at hjltP
      exact absurd hjltP (not_lt.mpr hB.le)
    have hjmax : jmax + 1 ∉ T := by
      intro hcon
      have h2 := Finset.le_max' T (jmax + 1) hcon
      omega
    have hj1I : jmax + 1 ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr (by omega)
    have hnotlt : ¬ (azim x v w ((sigmaFan x V E v)^[jmax + 1] w) < azim x v w a) := by
      intro hcon
      exact hjmax (Finset.mem_filter.mpr ⟨hj1I, decide_eq_true hcon⟩)
    have hauj1 : a ≠ (sigmaFan x V E v)^[jmax + 1] w := by
      intro he
      exact hacyc (jmax + 1) (by omega) he.symm
    have hge : azim x v w a ≤ azim x v w ((sigmaFan x V E v)^[jmax + 1] w) :=
      le_of_not_gt hnotlt
    have hgt : azim x v w a ≠ azim x v w ((sigmaFan x V E v)^[jmax + 1] w) :=
      fun he => hinjθ a ((sigmaFan x V E v)^[jmax + 1] w) ha
        (hpowS (jmax + 1)) hauj1 he
    have hlt2 : azim x v w a < azim x v w ((sigmaFan x V E v)^[jmax + 1] w) :=
      lt_of_le_of_ne hge hgt
    have hujS : (sigmaFan x V E v)^[jmax] w ∈ setOfEdge v V E := hpowS jmax
    have hauj : a ≠ (sigmaFan x V E v)^[jmax] w := by
      intro he
      exact hacyc jmax (by omega) he.symm
    have hSnej : setOfEdge v V E ≠ {(sigmaFan x V E v)^[jmax] w} := by
      intro he
      have hac : a ∈ ({(sigmaFan x V E v)^[jmax] w} : Set V3) := by rw [← he]; exact ha
      exact hauj (by simpa using hac)
    have hminJ := (SIGMA_FAN hSnej hfan hujS).2.2 a ha hauj
    have hσJ : sigmaFan x V E v ((sigmaFan x V E v)^[jmax] w)
        = (sigmaFan x V E v)^[jmax + 1] w := by
      rw [Function.iterate_succ_apply']
    rw [hσJ] at hminJ
    have huju0 : (sigmaFan x V E v)^[jmax + 1] w ≠ w := by
      intro he
      exact hdist 0 (jmax + 1) (by omega) (by omega) he.symm
    have hmono := yk8_monoAzimSigma (x := x) (V := V) (E := E) hfan hw
      (hEof _ hujS)
      (show sigmaFan x V E v ((sigmaFan x V E v)^[jmax] w) ≠ w by
        rw [hσJ]; exact huju0)
    rw [hσJ] at hmono
    have hsumJ1 : azim x v w ((sigmaFan x V E v)^[jmax + 1] w)
        = azim x v w ((sigmaFan x V E v)^[jmax] w)
          + azim x v ((sigmaFan x V E v)^[jmax] w)
            ((sigmaFan x V E v)^[jmax + 1] w) :=
      sum2_azim_fan hfan hw (hEof _ hujS) (hEof _ (hpowS (jmax + 1))) hmono
    have hsumJa : azim x v w a = azim x v w ((sigmaFan x V E v)^[jmax] w)
        + azim x v ((sigmaFan x V E v)^[jmax] w) a :=
      sum2_azim_fan hfan hw (hEof _ hujS) (hEof a ha) hjltP.le
    linarith

/-! ### 9j.1 单圈性（面圈顶点两两相异）+ ncard vPrime 下半。
单圈性 = SRPRNPL（conformingFan，ConformingAuto1:737，public 可见）的 Simple
+ σ-轨道单循环覆盖（9j.0）联立：Simple 说 f ∩ node-轨道(d) = {d}，覆盖说
node-轨道(d) 含一切首分量为 d.1 的 dart。 -/

/-- nodeMap 迭代显式形：dart1 上保持首分量、沿 σ 递推
（ConformingAuto1 `hypermapOfFan_nodeMap_iterate_ca1` 的 private 墙外副本）。 -/
private theorem yk8_node_iterate {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) (n : ℕ) :
    ((@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan) : V3 × V3 → V3 × V3))^[n] d
      = (d.1, (sigmaFan x V E d.1)^[n] d.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hE : ({d.1, (sigmaFan x V E d.1)^[n] d.2} : Set V3) ∈ E :=
      (properties_of_setOfEdge_fan x V E d.1 _ hfan).mpr
        (image_power_map_points hfan hd n)
    have hmem : ((d.1, (sigmaFan x V E d.1)^[n] d.2) ∈ dart1OfFan V E) := hE
    have hstep : ((@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan x V E hfan) : V3 × V3 → V3 × V3))^[n + 1] d
        = (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
          (hypermapOfFan x V E hfan)
          (((@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
            (hypermapOfFan x V E hfan) : V3 × V3 → V3 × V3))^[n] d)) :=
      Function.iterate_succ_apply'
        (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
          (hypermapOfFan x V E hfan)) n d
    rw [hstep, ih, yk2_apply_nodeMap hfan _, if_pos hmem, Function.iterate_succ_apply']
    rfl

/-- 单循环覆盖的 node-轨道形态：同首分量的 dart1 dart 必在 node-轨道里。 -/
private theorem yk8_mem_node_of_fst {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hV : V.Finite) {d p : V3 × V3}
    (hd : d ∈ dart1OfFan V E) (hp : p ∈ dart1OfFan V E) (h1 : p.1 = d.1) :
    ∃ n : ℕ, (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan))^[n] d = p := by
  have hdE : ({d.1, d.2} : Set V3) ∈ E := hd
  have hpE : ({p.1, p.2} : Set V3) ∈ E := hp
  have hw2 : p.2 ∈ setOfEdge d.1 V E := by
    refine (properties_of_setOfEdge_fan x V E d.1 p.2 hfan).mp ?_
    rw [h1] at hpE
    exact hpE
  have hns : ∃ n : ℕ, (sigmaFan x V E d.1)^[n] d.2 = p.2 :=
    yk8_sigmaOrbitCovers hfan hV hdE p.2 hw2
  obtain ⟨n, hn⟩ := hns
  refine ⟨n, ?_⟩
  rw [yk8_node_iterate hfan hd n, hn]
  exact Prod.ext (by rw [h1]) rfl

/-- **单圈性（fst 侧）**：面轨道上首分量单射——同一顶点至多一条面 dart。
= SRPRNPL 的 Simple（f ∩ node-轨道(d) = {d}）+ 覆盖件。 -/
private theorem yk8_face_fst_inj {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) :
    ∀ d₁ ∈ f, ∀ d₂ ∈ f, d₁.1 = d₂.1 → d₁ = d₂ := by
  intro d₁ hd₁ d₂ hd₂ heq
  have hd₁' : d₁ ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hd₁)
  have hdarts : d₁ ∈ @Hypermap.darts (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan) := (yk2_mem_darts_iff hfan d₁).mpr hd₁'
  have hP : PermutesOn (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) (@Hypermap.darts (V3 × V3)
      (fun a b' => instDecidableEqProd a b') (hypermapOfFan x V E hfan)) :=
    @Hypermap.faceMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)
  have hface : @Hypermap.face (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan) d₁ = f := by
    have h1 : d₁ ∈ yk2_faceOrbit x V E hfan b := hf ▸ hd₁
    show orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) d₁ = f
    rw [hf]
    exact orbitMap_eq_of_mem hP h1
  obtain ⟨n, hn⟩ := yk8_mem_node_of_fst hfan hV hd₁'
    (yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hd₂)) heq.symm
  have hmem : d₂ ∈ @Hypermap.node (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan) d₁ := ⟨n, hn⟩
  have hsimp := SRPRNPL (x := x) (V := V) (E := E) hfan hconf d₁ hdarts
  rw [hface] at hsimp
  have h2 : d₂ ∈ (@Hypermap.node (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan) d₁ ∩ f) := ⟨hmem, hd₂⟩
  rw [hsimp, Set.mem_singleton_iff] at h2
  exact h2.symm

/-- **单圈性（snd 侧）**：面轨道上第二分量单射（fst 侧 + faceMap 保持 snd +
σ_w⁻¹ 在邻集上的右逆）。 -/
private theorem yk8_face_snd_inj {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) :
    ∀ d₁ ∈ f, ∀ d₂ ∈ f, d₁.2 = d₂.2 → d₁ = d₂ := by
  intro d₁ hd₁ d₂ hd₂ hsnd
  have hd₁1 : d₁ ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hd₁)
  have hd₂1 : d₂ ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hd₂)
  -- faceMap 像：同 snd = w，同入 f
  have hfd : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) d₁
      = (d₁.2, inverseSigmaFan x V E d₁.2 d₁.1) := by
    rw [yk2_apply_faceMap hfan d₁, if_pos hd₁1]
    rfl
  have hfd2 : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) d₂
      = (d₂.2, inverseSigmaFan x V E d₂.2 d₂.1) := by
    rw [yk2_apply_faceMap hfan d₂, if_pos hd₂1]
    rfl
  have hcl1 : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) d₁ ∈ f := by
    rw [hf]
    exact yk2_faceOrbit_closure hfan (hf ▸ hd₁)
  have hcl2 : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) d₂ ∈ f := by
    rw [hf]
    exact yk2_faceOrbit_closure hfan (hf ▸ hd₂)
  have hfeq := yk8_face_fst_inj hfan hconf hV b hb f hf _ hcl1 _ hcl2
    (by rw [hfd, hfd2]; simpa using hsnd)
  -- σ_w⁻¹ 相等 ⟹ 原 fst 相等（邻集上 ext σ 的右逆性）
  have hw : d₁.2 = d₂.2 := hsnd
  have hfeq' : (d₁.2, inverseSigmaFan x V E d₁.2 d₁.1)
      = (d₂.2, inverseSigmaFan x V E d₂.2 d₂.1) := by
    rw [← hfd, ← hfd2]
    exact hfeq
  have hinv : inverseSigmaFan x V E d₁.2 d₁.1 = inverseSigmaFan x V E d₁.2 d₂.1 := by
    have h0 := congrArg Prod.snd hfeq'
    rw [← hw] at h0
    exact h0
  -- v_i ∈ setOfEdge w（w := d₁.2）
  have hwE1 : ({d₁.2, d₁.1} : Set V3) ∈ E := by
    rw [Set.pair_comm]
    exact hd₁1
  have hwE2 : ({d₁.2, d₂.1} : Set V3) ∈ E := by
    rw [Set.pair_comm]
    have h2' : ({d₂.1, d₂.2} : Set V3) ∈ E := hd₂1
    rw [← hw] at h2'
    exact h2'
  have hv1S : d₁.1 ∈ setOfEdge d₁.2 V E :=
    (properties_of_setOfEdge_fan x V E d₁.2 d₁.1 hfan).mp hwE1
  have hv2S : d₂.1 ∈ setOfEdge d₁.2 V E :=
    (properties_of_setOfEdge_fan x V E d₁.2 d₂.1 hfan).mp hwE2
  have hperm := permutes_sigma_fan hfan hv1S
  obtain ⟨s, _, hsf⟩ := yk7_finite_surjOf_inj
    (remark_finite_fan1 d₁.2 V E hfan.2.2.1.1) hperm.1 hperm.2.1 d₁.1 hv1S
  have hF1 : extensionSigmaFan x V E d₁.2 (inverseSigmaFan x V E d₁.2 d₁.1) = d₁.1 :=
    Function.invFun_eq ⟨s, hsf⟩
  obtain ⟨s2, _, hsf2⟩ := yk7_finite_surjOf_inj
    (remark_finite_fan1 d₁.2 V E hfan.2.2.1.1) hperm.1 hperm.2.1 d₂.1 hv2S
  have hF2 : extensionSigmaFan x V E d₁.2 (inverseSigmaFan x V E d₁.2 d₂.1) = d₂.1 :=
    Function.invFun_eq ⟨s2, hsf2⟩
  have hkey : d₁.1 = d₂.1 := by
    have h0 := congrArg (extensionSigmaFan x V E d₁.2) hinv
    exact hF1.symm.trans (h0.trans hF2)
  exact Prod.ext hkey hsnd

/-- 面 dart 非对角（fst 单射 + 2 < ncard f 下轨道无 (v,v) dart）。 -/
private theorem yk8_fst_ne_snd {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) (hk : 2 < f.ncard) :
    ∀ d ∈ f, d.1 ≠ d.2 := by
  intro d hd hcon
  have hd1 : d ∈ dart1OfFan V E := yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hd)
  have hfd : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) d = (d.1, inverseSigmaFan x V E d.1 d.1) := by
    rw [yk2_apply_faceMap hfan d, if_pos hd1]
    show (d.2, inverseSigmaFan x V E d.2 d.1) = (d.1, inverseSigmaFan x V E d.1 d.1)
    rw [← hcon]
  have hcl : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) d ∈ f := by
    rw [hf]
    exact yk2_faceOrbit_closure hfan (hf ▸ hd)
  have hfix : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) d = d :=
    yk8_face_fst_inj hfan hconf hV b hb f hf
      (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan) d) hcl d hd (by rw [hfd])
  have hP : PermutesOn (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) (@Hypermap.darts (V3 × V3)
      (fun a b' => instDecidableEqProd a b') (hypermapOfFan x V E hfan)) :=
    @Hypermap.faceMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)
  have hfaceD : orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) d = f := by
    have h1 : d ∈ yk2_faceOrbit x V E hfan b := hf ▸ hd
    rw [hf]
    exact orbitMap_eq_of_mem hP h1
  rw [orbitMap_eq_singleton hfix] at hfaceD
  have h1c : f.ncard = 1 := by rw [← hfaceD, Set.ncard_singleton]
  omega

/-- faceMap 值形状（dart1 上）：`faceMap e = (e.2, σ⁻¹_{e.2} e.1)`，
故第二分量 = e.1、第一分量 = e.2。 -/
private theorem yk8_faceMap_val {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {e : V3 × V3} (he : e ∈ dart1OfFan V E) :
    (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) e
      = (e.2, inverseSigmaFan x V E e.2 e.1) := by
  rw [yk2_apply_faceMap hfan e, if_pos he]
  rfl

/-- 面轨道内 dart 的 faceMap-逆：仍在面轨道，且第二分量 = 原 dart 的第一分量。 -/
private theorem yk8_symm_snd {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) {d : V3 × V3} (hd : d ∈ f) :
    (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan)).symm d ∈ f
      ∧ ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan)).symm d).2 = d.1 := by
  have hs1 : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)).symm d ∈ f := by
    rw [hf]
    exact yk2_faceOrbit_symm_closure hfan (hf ▸ hd)
  have he1 : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)).symm d ∈ dart1OfFan V E :=
    yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hs1)
  refine ⟨hs1, ?_⟩
  have happ : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) ((@Hypermap.faceMap (V3 × V3)
      (fun a b' => instDecidableEqProd a b') (hypermapOfFan x V E hfan)).symm d) = d :=
    Equiv.apply_symm_apply _ _
  rw [yk8_faceMap_val hfan he1] at happ
  exact (congrArg Prod.fst happ.symm).symm

/-- **f 与 reverse f 不交**（checkpoint 3 前置①；单圈性两侧 + 2 < ncard f）。 -/
private theorem yk8_face_inter_swap {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) (hk : 2 < f.ncard) :
    f ∩ (fun d : V3 × V3 => (d.2, d.1)) '' f = ∅ := by
  by_contra hcon
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hcon
  have hz2 : z ∈ (fun d : V3 × V3 => (d.2, d.1)) '' f := hz.2
  simp only [Set.mem_image] at hz2
  obtain ⟨y, hy, hd⟩ := hz2
  have hdF : (y.2, y.1) ∈ f := by
    rw [hd]
    exact hz.1
  by_cases hdiag : y.1 = y.2
  · exact yk8_fst_ne_snd hfan hconf hV b hb f hf hk y hy hdiag
  -- 前驱 dart 的第二分量 = (y.2,y.1).1 = y.2 = y 的第二分量 ⟹ 前驱 = y
  have hsy := yk8_symm_snd hfan b hb f hf hdF
  have hinv : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)).symm (y.2, y.1) = y := by
    refine yk8_face_snd_inj hfan hconf hV b hb f hf _ hsy.1 y hy ?_
    rw [hsy.2]
  have hstep : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) y = (y.2, y.1) := by
    have h0 := congrArg (@Hypermap.faceMap (V3 × V3)
      (fun a b' => instDecidableEqProd a b') (hypermapOfFan x V E hfan)) hinv
    rw [Equiv.apply_symm_apply] at h0
    exact h0.symm
  -- faceMap (y.2,y.1) 与 y 同首分量 y.1 ⟹ faceMap² y = y
  have hP : PermutesOn (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) (@Hypermap.darts (V3 × V3)
      (fun a b' => instDecidableEqProd a b') (hypermapOfFan x V E hfan)) :=
    @Hypermap.faceMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)
  have hcl2 : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) (y.2, y.1) ∈ f := by
    rw [hf]
    exact yk2_faceOrbit_closure hfan (hf ▸ hdF)
  have hfix2 : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) (y.2, y.1) = y :=
    yk8_face_fst_inj hfan hconf hV b hb f hf _ hcl2 y hy (by
      have hdF1 : (y.2, y.1) ∈ dart1OfFan V E :=
        yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hdF)
      rw [yk8_faceMap_val hfan hdF1])
  have hfix : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) ((@Hypermap.faceMap (V3 × V3)
      (fun a b' => instDecidableEqProd a b') (hypermapOfFan x V E hfan)) y) = y := by
    rw [hstep]
    exact hfix2
  have hpow2 : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan) ^ 2) y = y := by
    rw [pow_two, Equiv.Perm.mul_apply]
    exact hfix
  have hyc : y ∈ f := hy
  have horb : orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) y = f := by
    have h1 : y ∈ yk2_faceOrbit x V E hfan b := hf ▸ hyc
    rw [hf]
    exact orbitMap_eq_of_mem hP h1
  have h2orb : orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) y = {y, (y.2, y.1)} := by
    rw [orbit_cyclic (f := @Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)) (x := y) (m := 2) (by decide) hpow2]
    ext w
    simp only [Set.mem_image, Set.mem_singleton_iff, Set.mem_insert_iff,
      Finset.mem_coe, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, hke⟩
      rcases Nat.lt_or_ge k 2 with h2k | h2k
      · rcases Nat.lt_or_ge k 1 with h1k | h1k
        · have hk0 : k = 0 := by omega
          rw [hk0] at hke
          simp only [pow_zero, Equiv.Perm.one_apply] at hke
          left
          exact hke.symm
        · have hk1 : k = 1 := by omega
          rw [hk1, pow_one] at hke
          right
          exact hke.symm.trans hstep
      · exact absurd hk (by omega)
    · rintro (rfl | rfl)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, by rw [pow_one]; exact hstep⟩
  have hyd : y ≠ (y.2, y.1) := by
    intro he
    exact hdiag (congrArg Prod.snd he).symm
  have hcard2 : f.ncard = 2 := by
    rw [← horb, h2orb, Set.ncard_insert_of_notMem
      (by intro hme; exact hyd (Set.mem_singleton_iff.mp hme)),
      Set.ncard_singleton]
  omega

/-- **ncard vPrime 下半**：`ncard f ≤ ncard vPrime`（fst 单射下 f = fst″f ⊆
vPrime）。与 AE 上半 `yk6_ncard_vPrime_le` 拼接成等式。 -/
private theorem yk8_ncard_f_le_vPrime {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) : f.ncard ≤ (vPrime_p2 V f).ncard := by
  have hfin : f.Finite := by
    rw [hf]
    exact orbitMap_finite
      (@Hypermap.faceMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan)) b
  have hsub1 : Set.InjOn (fun d : V3 × V3 => d.1) f :=
    fun c hc e he heq => yk8_face_fst_inj hfan hconf hV b hb f hf c hc e he heq
  have hcard : ((fun d : V3 × V3 => d.1) '' f).ncard = f.ncard :=
    Set.InjOn.ncard_image hsub1
  have hsub2 : (fun d : V3 × V3 => d.1) '' f ⊆ vPrime_p2 V f := by
    rintro v ⟨w, hw, hwv⟩
    rw [← hwv]
    exact ⟨(yk2_dart_fst_snd_mem_V hfan
      (yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hw))).1, ⟨w.2, hf ▸ hw⟩⟩
  have h2 : ((fun d : V3 × V3 => d.1) '' f).ncard ≤ (vPrime_p2 V f).ncard :=
    Set.ncard_le_ncard hsub2
      (Set.Finite.subset hV (yk6_vPrime_subset (V := V) f))
  rw [hcard] at h2
  exact h2

/-- ncard vPrime = ncard f（单圈性下的 LOFA_IMP_CARD_FF_V_EQ 内容：
AE 上半 + 本波下半）。 -/
private theorem yk8_ncard_vPrime_eq {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) :
    (vPrime_p2 V f).ncard = f.ncard :=
  le_antisymm (yk6_ncard_vPrime_le hfan b hb f hf)
    (yk8_ncard_f_le_vPrime hfan hconf hV b hb f hf)

/-- **ncard vPrime 下半（装配形）**：`4 ≤ ncard f`（tau4/5/6 章 dartsK 供给）
时 `4 ≤ ncard vPrime`。 -/
private theorem yk8_four_le_ncard_vPrime {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 4 ≤ f.ncard) :
    4 ≤ (vPrime_p2 V f).ncard := by
  rw [yk8_ncard_vPrime_eq hfan hconf hV b hb f hf]
  exact hk

/-! ### 9j.2 checkpoint 3 前置：受限邻域恰二元素、σ′ 对合、darts′ 基数 2k。
（HOL DIH_K_HYP_E_PRIME / FF_DISJOINT_ITS_IMAGE_CARD_EQ 的 Lean 折算原料：
单圈性 + 2 < ncard f 之后全部为轨道簿记。） -/

/-- 受限邻域恰两元素：每个面顶点 v 的 N′(v) = {succ_v, pred_v}，succ ≠ pred
（单圈性两侧 + 2 < ncard f）。 -/
private theorem yk8_setOfEdge_ePrime_two {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) (hk : 2 < f.ncard)
    (v : V3) (hv : v ∈ vPrime_p2 V f) :
    ∃ p s : V3, p ≠ s ∧ p ∈ setOfEdge v (vPrime_p2 V f) (ePrime_p2 E f)
      ∧ s ∈ setOfEdge v (vPrime_p2 V f) (ePrime_p2 E f)
      ∧ ∀ u ∈ setOfEdge v (vPrime_p2 V f) (ePrime_p2 E f), u = p ∨ u = s := by
  obtain ⟨-, w, hw⟩ := Set.mem_setOf_eq.mp hv
  have hd : (v, w) ∈ f := hw
  have hsy := yk8_symm_snd hfan b hb f hf hd
  have hwV : w ∈ V :=
    (yk2_dart_fst_snd_mem_V hfan
      (yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hd))).2
  have hsV : ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)).symm (v, w)).1 ∈ V :=
    (yk2_dart_fst_snd_mem_V hfan
      (yk2_faceOrbit_subset_dart1 hfan b hb
        (by exact yk2_faceOrbit_symm_closure hfan (hf ▸ hd)))).1
  -- 前驱 dart 的显式形：(s, v) ∈ f，其中 s := (faceMap⁻¹ (v,w)).1
  have hsdart : (((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)).symm (v, w)).1, v) ∈ f := by
    have hpair : (((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan)).symm (v, w)).1, v)
        = (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan x V E hfan)).symm (v, w) := by
      apply Prod.ext
      · rfl
      · exact hsy.2.symm
    rw [hpair]
    exact hsy.1
  -- succ ≠ pred：相等时 (v,w) 与 (w,v) 同在 f，落入 f ∩ swap″f
  have hpne : w ≠ ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x V E hfan)).symm (v, w)).1 := by
    intro heq
    have hsw' : ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan)).symm (v, w)).1 = w := heq.symm
    have hwv : (w, v) ∈ f := by
      rw [← hsw']
      exact hsdart
    have hdis := yk8_face_inter_swap hfan hconf hV b hb f hf hk
    have hmem : (v, w) ∈ f ∩ ((fun d : V3 × V3 => (d.2, d.1)) '' f) :=
      Set.mem_inter hd (show (v, w) ∈ (fun d : V3 × V3 => (d.2, d.1)) '' f from
        ⟨(w, v), hwv, rfl⟩)
    rw [hdis] at hmem
    exact (Set.mem_empty_iff_false _).mp hmem
  have hch := yk2_setOfEdge_ePrime_eq hfan b hb f hf v
  refine ⟨w, ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
    (hypermapOfFan x V E hfan)).symm (v, w)).1, hpne, ?_, ?_, ?_⟩
  · rw [hch]
    exact ⟨hwV, Or.inl hd⟩
  · rw [hch]
    exact ⟨hsV, Or.inr hsdart⟩
  · intro u hu
    obtain ⟨-, hd'⟩ := Set.mem_setOf_eq.mp (hch ▸ hu)
    rcases hd' with hd' | hd'
    · have h2 := yk8_face_fst_inj hfan hconf hV b hb f hf (v, u) hd' (v, w) hd rfl
      exact Or.inl (congrArg Prod.snd h2)
    · have h2 := yk8_face_snd_inj hfan hconf hV b hb f hf (u, v) hd'
        ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan x V E hfan)).symm (v, w)) hsy.1 (by rw [hsy.2])
      exact Or.inr (congrArg Prod.fst h2)

/-- σ′ 在面顶点的受限邻域上为二元交换：σ′ u ≠ u 且 σ′(σ′ u) = u
（SIGMA_FAN + 二元素集）。 -/
private theorem yk8_sigmaPrime_swap {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN x (vPrime_p2 V f) (ePrime_p2 E f))
    (v : V3) (hv : v ∈ vPrime_p2 V f) (u : V3)
    (hu : u ∈ setOfEdge v (vPrime_p2 V f) (ePrime_p2 E f)) :
    sigmaFan x (vPrime_p2 V f) (ePrime_p2 E f) v u ≠ u
      ∧ sigmaFan x (vPrime_p2 V f) (ePrime_p2 E f) v
          (sigmaFan x (vPrime_p2 V f) (ePrime_p2 E f) v u) = u := by
  obtain ⟨p, s, hps, hpS, hsS, htwo⟩ :=
    yk8_setOfEdge_ePrime_two hfan hconf hV b hb f hf hk v hv
  have hneP : setOfEdge v (vPrime_p2 V f) (ePrime_p2 E f) ≠ {p} := by
    intro hcon
    have h1 : s ∈ ({p} : Set V3) := hcon ▸ hsS
    exact hps (Set.mem_singleton_iff.mp h1).symm
  have hneS : setOfEdge v (vPrime_p2 V f) (ePrime_p2 E f) ≠ {s} := by
    intro hcon
    have h1 : p ∈ ({s} : Set V3) := hcon ▸ hpS
    exact hps.symm (Set.mem_singleton_iff.mp h1).symm
  -- σ′ p = s、σ′ s = p
  have hσp : sigmaFan x (vPrime_p2 V f) (ePrime_p2 E f) v p = s := by
    obtain ⟨hσS, hσne, -⟩ := SIGMA_FAN hneP hfan' hpS
    rcases htwo _ hσS with h | h
    · exact absurd h hσne
    · exact h
  have hσs : sigmaFan x (vPrime_p2 V f) (ePrime_p2 E f) v s = p := by
    obtain ⟨hσS, hσne, -⟩ := SIGMA_FAN hneS hfan' hsS
    rcases htwo _ hσS with h | h
    · exact h
    · exact absurd h hσne
  rcases htwo u hu with hu' | hu'
  · refine ⟨by rw [hu', hσp]; exact Ne.symm hps, ?_⟩
    rw [hu', hσp, hσs]
  · refine ⟨by rw [hu', hσs]; exact hps, ?_⟩
    rw [hu', hσs, hσp]

/-- swap 像的基数 = f 的基数。 -/
private theorem yk8_swap_image_ncard {f : Set (V3 × V3)} :
    ((fun d : V3 × V3 => (d.2, d.1)) '' f).ncard = f.ncard :=
  Set.InjOn.ncard_image
    (fun a _ b _ heq => Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq))

/-- **受限 dartset 基数**：dart1(vPrime, ePrime) 的 ncard = 2 · ncard f
（f ⊔ swap″f 不交分解，checkpoint 3 的 card = 2k 合取）。 -/
private theorem yk8_dart1_ePrime_ncard {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) (hk : 2 < f.ncard) :
    (dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)).ncard = 2 * f.ncard := by
  have hU : dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)
      = f ∪ (fun d : V3 × V3 => (d.2, d.1)) '' f :=
    yk2_dart1_ePrime_eq_union_swap hfan b hb f hf
  have hdisj : f ∩ (fun d : V3 × V3 => (d.2, d.1)) '' f = ∅ :=
    yk8_face_inter_swap hfan hconf hV b hb f hf hk
  have hfin : f.Finite := by
    rw [hf]
    exact orbitMap_finite
      (@Hypermap.faceMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan x V E hfan)) b
  have hfin2 : ((fun d : V3 × V3 => (d.2, d.1)) '' f).Finite :=
    Set.Finite.image (fun d : V3 × V3 => (d.2, d.1)) hfin
  have hdisj' : Disjoint f ((fun d : V3 × V3 => (d.2, d.1)) '' f) := by
    rw [Set.disjoint_left]
    intro a ha hab
    have h2 : a ∈ f ∩ ((fun d : V3 × V3 => (d.2, d.1)) '' f) := Set.mem_inter ha hab
    rw [hdisj] at h2
    exact (Set.mem_empty_iff_false a).mp h2
  have hkey : ((f ∪ (fun d : V3 × V3 => (d.2, d.1)) '' f)).encard
      = f.encard + ((fun d : V3 × V3 => (d.2, d.1)) '' f).encard := by
    rw [Set.encard_union_eq hdisj']
  calc (dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)).ncard
      = ENat.toNat (f ∪ (fun d : V3 × V3 => (d.2, d.1)) '' f).encard := by
        rw [hU, Set.ncard_def]
    _ = ENat.toNat (f.encard + ((fun d : V3 × V3 => (d.2, d.1)) '' f).encard) := by
        rw [hkey]
    _ = ENat.toNat f.encard + ENat.toNat ((fun d : V3 × V3 => (d.2, d.1)) '' f).encard := by
        refine ENat.toNat_add ?_ ?_
        · exact ne_of_eq_of_ne (Set.Finite.cast_ncard_eq hfin).symm
            (ENat.coe_ne_top f.ncard)
        · exact ne_of_eq_of_ne (Set.Finite.cast_ncard_eq hfin2).symm
            (ENat.coe_ne_top ((fun d : V3 × V3 => (d.2, d.1)) '' f).ncard)
    _ = f.ncard + ((fun d : V3 × V3 => (d.2, d.1)) '' f).ncard := by
        rw [Set.ncard_def, Set.ncard_def]
    _ = f.ncard + f.ncard := by rw [yk8_swap_image_ncard]
    _ = 2 * f.ncard := by ring

/-- 受限超图的 dart 集基数（Finset 层）。 -/
private theorem yk8_Hdarts_card {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit x V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN x (vPrime_p2 V f) (ePrime_p2 E f)) :
    (@Hypermap.darts (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x (vPrime_p2 V f) (ePrime_p2 E f) hfan')).card
      = 2 * f.ncard := by
  have hcoe : (↑(@Hypermap.darts (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan x (vPrime_p2 V f) (ePrime_p2 E f) hfan')) : Set (V3 × V3))
      = dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) := yk2_darts_coe hfan'
  rw [← Set.ncard_coe_finset, hcoe, yk8_dart1_ePrime_ncard hfan hconf hV b hb f hf hk]

/-! ### 9j.3 checkpoint 3 · Dih2k 帽石波（受限超图 H′ 的轨道结构与 HasOrders）。
本波钉定 x := 0（装配上下文 LocalFan 的 apex）。 -/

variable {V : Set V3} {E : Set (Set V3)}

/-- N′ 上 invFun(ext σ′) 的显式值 = σ′（σ′ 二元交换 + ext-on-N +
yk7_invFun_eq_of_apply 值形式）。 -/
private theorem yk8_invFun_eq_sigmaPrime (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f))
    (v : V3) (hv : v ∈ vPrime_p2 V f) (u : V3)
    (hu : u ∈ setOfEdge v (vPrime_p2 V f) (ePrime_p2 E f)) :
    inverseSigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) v u
      = sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) v u := by
  obtain ⟨hσne, hσσ⟩ := yk8_sigmaPrime_swap hfan hconf hV b hb f hf hk hfan' v hv u hu
  have hperm := permutes_sigma_fan hfan' hu
  have hmem : sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) v u
      ∈ setOfEdge v (vPrime_p2 V f) (ePrime_p2 E f) := sigma_fan_in_setOfEdge hfan' hu
  have hext : extensionSigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) v
      (sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) v u) = u := by
    rw [extensionSigmaFan, if_neg (not_not.mpr hmem)]
    exact hσσ
  exact yk7_invFun_eq_of_apply hperm.1 hperm.2.1 hperm.2.2 hmem hu hext

/-- 受限 dart 的面 Map 值（dart1′ 上）。 -/
private theorem yk8_HfaceMap_val (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f))
    {d : V3 × V3} (hd : d ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)) :
    (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d
      = (d.2, inverseSigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.2 d.1) := by
  rw [yk2_apply_faceMap hfan' d, if_pos hd]
  rfl

/-- 受限 dart 的 node Map 值（dart1′ 上）。 -/
private theorem yk8_HnodeMap_val (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f))
    {d : V3 × V3} (hd : d ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)) :
    (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d
      = (d.1, sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1 d.2) := by
  rw [yk2_apply_nodeMap hfan' d, if_pos hd]
  rfl

/-- **checkpoint 3 前置②**：受限 node Map 在面轨道上的像 = swap 像
（nodeMap(f d) = swap(f′⁻¹ d) 双向；单圈性 + 2 < ncard f）。 -/
private theorem yk8_nodePrime_image_swap (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f)) :
    (fun d : V3 × V3 => (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d) '' f
      = (fun d : V3 × V3 => (d.2, d.1)) '' f := by
  have hbb : b ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) := by
    have hbE : ({b.1, b.2} : Set V3) ∈ E := hb
    have hbf : (b.1, b.2) ∈ f := by
      have h0 : b ∈ yk2_faceOrbit 0 V E hfan b := mem_orbitMap_self _ _
      exact hf ▸ h0
    exact Set.mem_setOf_eq.mpr ⟨b.1, b.2, rfl, hbE, hbf⟩
  have hf' : f = yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
    (yk7_FF_eq_faceOrbit hfan b hb f hf).symm
  have hiff' : ∀ z : V3 × V3, z ∈ f ↔ z ∈ yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
    fun z => ⟨fun hz => hf' ▸ hz, fun hz => hf'.symm ▸ hz⟩
  -- 面轨道 dart 落在 dart1′
  have hsub1 : ∀ d ∈ f, d ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) := fun d hd =>
    yk2_faceOrbit_subset_dart1 hfan' b hbb ((hiff' d).mp hd)
  have hfclosure : ∀ d ∈ f, (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d ∈ f := by
    intro d hd
    exact (hiff' _).mpr (yk2_faceOrbit_closure hfan' ((hiff' d).mp hd))
  refine Set.Subset.antisymm (Set.image_subset_iff.2 fun d hd => ?_)
    (Set.image_subset_iff.2 fun y hy => ?_)
  · -- ⊆：nodeMap d = swap(faceMap⁻¹ d)（前驱第一分量 = σ′ 后继）
    have hd1 := hsub1 d hd
    have hvN : d.2 ∈ setOfEdge d.1 (vPrime_p2 V f) (ePrime_p2 E f) :=
      (properties_of_setOfEdge_fan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1 d.2 hfan').mp hd1
    have hvV : d.1 ∈ vPrime_p2 V f := ⟨(yk2_dart_fst_snd_mem_V hfan
      (yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hd))).1, ⟨d.2, hf ▸ hd⟩⟩
    have hsym := yk8_symm_snd hfan' b hbb f hf' hd
    have hsym1 := hsub1 _ hsym.1
    have hfaceEq : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
        ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d) = d :=
      Equiv.apply_symm_apply _ _
    rw [yk8_HfaceMap_val hfan' (hsub1 _ hsym.1), hsym.2] at hfaceEq
    -- hfaceEq : (d.1, invFun-ext(σ′_{d.1}) (symm d).1) = d
    have hprod := congrArg Prod.snd hfaceEq
    -- invFun-ext(σ′_{d.1}) (symm d).1 = d.2
    have hzN : ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d).1
        ∈ setOfEdge d.1 (vPrime_p2 V f) (ePrime_p2 E f) := by
      refine (properties_of_setOfEdge_fan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1
        ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d).1 hfan').mp ?_
      have h2 : ({((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
            (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d).1,
            ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
              (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d).2} : Set V3)
          ∈ ePrime_p2 E f := hsub1 _ hsym.1
      rw [Set.pair_comm, hsym.2] at h2
      exact h2
    have hvalZ := yk8_invFun_eq_sigmaPrime hfan hconf hV b hb f hf hk hfan' d.1 hvV
      ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d).1 hzN
    -- hprod 经右逆值化：σFan d.1 ((symm d).1) = d.2；与 σ′ 对合夹出 (symm d).1 = σFan d.1 d.2
    have hprod2 : sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1
        (((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d).1) = d.2 := by
      rw [← hvalZ]; exact hprod
    have hswapd2 : sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1
        (sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1 d.2) = d.2 :=
      (yk8_sigmaPrime_swap hfan hconf hV b hb f hf hk hfan' d.1 hvV d.2 hvN).2
    have hN1 : sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1 d.2
        ∈ setOfEdge d.1 (vPrime_p2 V f) (ePrime_p2 E f) := sigma_fan_in_setOfEdge hfan' hvN
    have hkey : sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1 d.2
        = (((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d).1) :=
      mono_sigma_fan hfan' hN1 hzN (hswapd2.trans hprod2.symm)
    refine ⟨(@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d, hsym.1, ?_⟩
    show (((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d).2,
        ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm d).1)
        = (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d
    rw [hsym.2, ← hkey, yk8_HnodeMap_val hfan' hd1]
  · -- ⊇：swap y = nodeMap(faceMap y)（σ′∘invFun-ext 右逆于 N′）
    have hy1 := hsub1 y hy
    have hyV : y.2 ∈ vPrime_p2 V f := by
      rw [hf]
      exact yk2_face_snd_mem_vPrime hfan b hb (hf ▸ hy)
    have hyN : y.1 ∈ setOfEdge y.2 (vPrime_p2 V f) (ePrime_p2 E f) := by
      refine (properties_of_setOfEdge_fan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.2 y.1 hfan').mp ?_
      rw [Set.pair_comm]
      exact hy1
    have hinv := yk8_invFun_eq_sigmaPrime hfan hconf hV b hb f hf hk hfan' y.2 hyV y.1 hyN
    have hσσ : sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.2
        (sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.2 y.1) = y.1 :=
      (yk8_sigmaPrime_swap hfan hconf hV b hb f hf hk hfan' y.2 hyV y.1 hyN).2
    have hcl := hfclosure y hy
    have hcl1 := hsub1 _ hcl
    have h2 : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) y
        = (y.2, sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.2 y.1) := by
      rw [yk8_HfaceMap_val hfan' hy1, hinv]
    refine ⟨(@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) y, hcl, ?_⟩
    show (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
        ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) y) = (y.2, y.1)
    rw [yk8_HnodeMap_val hfan' hcl1, h2, hσσ]

/-! ### 9j.4 checkpoint 3 · Dih2k 收口：前驱值、交换关系、HasOrders×3、合取二、帽石。 -/

/-- 受限面轨道 dart 的前驱第一分量 = σ′ 后继（单圈性 + 2 < ncard f）。 -/
private theorem yk8_symm_fst_eq (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f))
    {y : V3 × V3} (hy : y ∈ f) :
    ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).1
      = sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.1 y.2 := by
  have hbb : b ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) := by
    have hbE : ({b.1, b.2} : Set V3) ∈ E := hb
    have hbf : (b.1, b.2) ∈ f := by
      have h0 : b ∈ yk2_faceOrbit 0 V E hfan b := mem_orbitMap_self _ _
      exact hf ▸ h0
    exact Set.mem_setOf_eq.mpr ⟨b.1, b.2, rfl, hbE, hbf⟩
  have hfe : f = yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
    (yk7_FF_eq_faceOrbit hfan b hb f hf).symm
  have hiff' : ∀ z : V3 × V3, z ∈ f ↔ z ∈ yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
    fun z => ⟨fun hz => hfe ▸ hz, fun hz => hfe.symm ▸ hz⟩
  have hy1 : y ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) :=
    yk2_faceOrbit_subset_dart1 hfan' b hbb ((hiff' y).mp hy)
  have hyV : y.2 ∈ vPrime_p2 V f := by
    rw [hf]
    exact yk2_face_snd_mem_vPrime hfan b hb (hf ▸ hy)
  have hyN1 : y.2 ∈ setOfEdge y.1 (vPrime_p2 V f) (ePrime_p2 E f) :=
    (properties_of_setOfEdge_fan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.1 y.2 hfan').mp hy1
  have hvY : y.1 ∈ vPrime_p2 V f :=
    ⟨(yk2_dart_fst_snd_mem_V hfan (yk2_faceOrbit_subset_dart1 hfan b hb (hf ▸ hy))).1,
      ⟨y.2, hf ▸ hy⟩⟩
  have hsym1 : ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y)
      ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) :=
    yk2_faceOrbit_subset_dart1 hfan' b hbb
      (yk2_faceOrbit_symm_closure hfan' ((hiff' y).mp hy))
  have hsy2 : ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).2 = y.1 :=
    (yk8_symm_snd hfan' b hbb f hfe hy).2
  have hzN : ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).1
      ∈ setOfEdge y.1 (vPrime_p2 V f) (ePrime_p2 E f) := by
    refine (properties_of_setOfEdge_fan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.1
      ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).1 hfan').mp ?_
    have h2 : ({((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).1,
          ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
            (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).2} : Set V3)
        ∈ ePrime_p2 E f := hsym1
    rw [hsy2, Set.pair_comm] at h2
    exact h2
  have hvalY := yk8_invFun_eq_sigmaPrime hfan hconf hV b hb f hf hk hfan' y.1 hvY
    ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).1 hzN
  have hfaceEq : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
      ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y) = y :=
    Equiv.apply_symm_apply _ _
  rw [yk8_HfaceMap_val hfan' hsym1, hsy2, hvalY] at hfaceEq
  -- hfaceEq : (y.1, σFan y.1 ((symm y).1)) = y
  have hsnd : sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.1
      (((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).1) = y.2 :=
    congrArg Prod.snd hfaceEq
  have hswap2 : sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.1
      (sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.1 y.2) = y.2 :=
    (yk8_sigmaPrime_swap hfan hconf hV b hb f hf hk hfan' y.1 hvY y.2 hyN1).2
  have hN1 : sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.1 y.2
      ∈ setOfEdge y.1 (vPrime_p2 V f) (ePrime_p2 E f) := sigma_fan_in_setOfEdge hfan' hyN1
  exact mono_sigma_fan hfan' hzN hN1 (hsnd.trans hswap2.symm)

/-- 交换关系（面轨道上）：faceMap′(swap y) = swap(faceMap′⁻¹ y)。 -/
private theorem yk8_comm_swap (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f))
    {y : V3 × V3} (hy : y ∈ f) :
    (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
        ((fun z : V3 × V3 => (z.2, z.1)) y)
      = (fun z : V3 × V3 => (z.2, z.1))
        ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y) := by
  have hy1 : y ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) := by
    have h0 : y ∈ yk2_faceOrbit 0 V E hfan b := hf ▸ hy
    have h1 := yk2_face_dart_mem_ePrime hfan b hb h0
    rw [← hf] at h1
    exact h1
  have hswapd : ((fun z : V3 × V3 => (z.2, z.1)) y)
      ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) := yk2_mem_dart1_pair_comm hy1
  have hyN1 : y.2 ∈ setOfEdge y.1 (vPrime_p2 V f) (ePrime_p2 E f) :=
    (properties_of_setOfEdge_fan 0 (vPrime_p2 V f) (ePrime_p2 E f) y.1 y.2 hfan').mp hy1
  have hval := yk8_invFun_eq_sigmaPrime hfan hconf hV b hb f hf hk hfan' y.1
    (by
      rw [hf]
      exact yk2_face_fst_mem_vPrime hfan b hb (hf ▸ hy)) y.2 hyN1
  have hsfst := yk8_symm_fst_eq hfan hconf hV b hb f hf hk hfan' hy
  show (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
      ((fun z : V3 × V3 => (z.2, z.1)) y)
      = (((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).2,
        ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).1)
  rw [yk8_HfaceMap_val hfan' hswapd,
    show ((fun z : V3 × V3 => (z.2, z.1)) y).2 = y.1 from rfl, hval,
    show ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm y).2 = y.1 from
      (yk8_symm_snd hfan' b
        (by
          have h1 : b ∈ yk2_faceOrbit 0 V E hfan b := mem_orbitMap_self _ _
          have h0 := yk2_face_dart_mem_ePrime hfan b hb h1
          exact hf ▸ h0) f
        (yk7_FF_eq_faceOrbit hfan b hb f hf).symm hy).2,
    hsfst]

/-! **NEEDS（9j.4 残差，Lane AJ 2026-10-23 诚实止步记账）**：Dih2k 帽石
`Dih2k (hypermapOfFan 0 vPrime ePrime hfan') f.ncard` 尚差四件簿记：
①HasOrders edge 2：e′² = 1（yk2_edgeMap_involutive hfan' 直接给）+ e′ ≠ 1
（b ∈ 受限 dart1 非对角——b.1 ≠ b.2 由 yk8_face_fst_inj + 2 < ncard f 的
对角-排除论证：b 对角 ⟹ faceMap b = b（fst 单射）⟹ orbit(b) = {b} ⟹
ncard f = 1 矛盾）；②HasOrders node 2：n′² = 1（d ∈ dart1′ 处
yk8_HnodeMap_val 两次 + yk8_sigmaPrime_swap.2；d ∉ 处 if_neg 两次）+
n′ ≠ 1（nodeMap b = (b.1, σFan b.1 b.2) ≠ b ⟸ sigmaPrime_swap.1）；
③orbit′(swap b) = swap″f（⊆：swap″f 的 f′-不变性 f′(swap y) =
swap(faceMap′⁻¹ y)（faceMap′⁻¹ y = symm y 由 preimage 唯一性）+
⊇：swap(f′^m b) = (f′⁻¹)^m(swap b) 归纳）；④HasOrders face k：
f′^k = 1（d ∈ f 轨道平移 + d ∈ swap″f 经 ③；f′^i ≠ 1 经
orbitMap_pow_inj 于 ncard(orbit′ b) = k）与 union-合取二
（d ∈ f 支已由 yk7_FF_eq_faceOrbit + yk8_nodePrime_image_swap +
yk2_dart1_ePrime_eq_union_swap 就绪；d ∈ swap″f 支经 ③）。
全部为 9j.0-9j.3 已证件的纯簿记拼装，无新几何。 -/

/-! ### 9k. ykit9 波（Lane AQ 2026-10-23）：9j.4 四件簿记残差收官。

AJ 记账的四件（上方 9j.4 块尾 NEEDS ①-④）逐条闭合：
①HasOrders edge 2（yk9_edge_hasOrders）；
②HasOrders node 2（yk9_node_sq_apply + yk9_node_hasOrders）；
③orbit′(swap y) = swap″f（yk9_iterate_swap_abstract + yk9_face_swap_iterate +
yk9_orbit_swap_image）；
④HasOrders face k + 合取二 + 帽石（yk9_face_hasOrders +
yk9_nodePrime_image_swapImage + yk9_dih2k_union + yk9_Dih2k）。
全部为 §9j.0-9j.4 已证件的纯簿记拼装，无新几何。记号：V′ := vPrime_p2 V f、
E′ := ePrime_p2 E f、H′ := hypermapOfFan 0 V′ E′ hfan′、fc := H′.faceMap、
n′ := H′.nodeMap、e′ := H′.edgeMap、swap d = (d.2, d.1)。

关键簿记路线（沉淀）：
- n′² = 1 的中间 dart 留域由 nodeMap_permutes（PermutesOn.apply_mem）白给；
- ③⊇ 走 swap∘fc = fc⁻¹∘swap（yk8_comm_swap 在 fc z 处的换位形）的望远镜
  + PermutesOn.orbitMap_symm（逆生成同轨道）；
- ④ f′^k = 1 逐点走 PermutesOn.pow_ncard_orbitMap_apply_self 于
  orbit(fc·) = f / = swap″f（后者经 ③ + yk8_swap_image_ncard）；
  f′^i ≠ 1 走 orbitMap_pow_inj 于 orbit′ b = f（yk7_FF_eq_faceOrbit）；
- 合取二 swap 侧 n′″swap″f = f 经 yk8_nodePrime_image_swap +
  Set.image_image + n′² = 1 的像-回卷。
装配注意（对齐 AJ §4）：SRPRNPL 消费 conformingFan，LpFan 只有
FullySurrounded——fully_surrounded_imp_conforming 桥移植仍是装配前置
（不在本波范围）。 -/

/-- 基 dart b 的落位簿记：b ∈ 受限 dart1、(b.1, b.2) ∈ f、b.1 ∈ vPrime、
b.2 ∈ 受限邻集（①② 的共同前置）。 -/
private theorem yk9_base_ctx (hfan : FAN 0 V E)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f)) :
    b ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)
      ∧ (b.1, b.2) ∈ f
      ∧ b.1 ∈ vPrime_p2 V f
      ∧ b.2 ∈ setOfEdge b.1 (vPrime_p2 V f) (ePrime_p2 E f) := by
  have hbE : ({b.1, b.2} : Set V3) ∈ E := hb
  have hbf : (b.1, b.2) ∈ f := by
    have h0 : b ∈ yk2_faceOrbit 0 V E hfan b := mem_orbitMap_self _ _
    exact hf ▸ h0
  have hbb : b ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) :=
    Set.mem_setOf_eq.mpr ⟨b.1, b.2, rfl, hbE, hbf⟩
  have hbV := yk2_dart_fst_snd_mem_V hfan hb
  refine ⟨hbb, hbf, ⟨hbV.1, ⟨b.2, hbf⟩⟩, ?_⟩
  exact (properties_of_setOfEdge_fan 0 (vPrime_p2 V f) (ePrime_p2 E f) b.1 b.2 hfan').mp hbb

/-- 受限 dart 的两端落位：d ∈ dart1′ → d.1 ∈ vPrime ∧ d.2 ∈ setOfEdge d.1 V′ E′
（② 的 σ′-前提；第一支经面轨道两端簿记，第二支经 swap-分支）。 -/
private theorem yk9_dart1_ctx (hfan : FAN 0 V E)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f))
    {d : V3 × V3} (hd : d ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)) :
    d.1 ∈ vPrime_p2 V f ∧ d.2 ∈ setOfEdge d.1 (vPrime_p2 V f) (ePrime_p2 E f) := by
  have hbb : b ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) :=
    (yk9_base_ctx hfan b hb f hf hfan').1
  have hU := yk2_dart1_ePrime_eq_union_swap hfan b hb f hf
  refine ⟨?_, (properties_of_setOfEdge_fan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1 d.2
    hfan').mp hd⟩
  have hd2 : d ∈ f ∪ ((fun z : V3 × V3 => (z.2, z.1)) '' f) := by
    rw [← hU]
    exact hd
  rcases hd2 with hdm | ⟨y, hy, hdy⟩
  · exact (yk2_dart_fst_snd_mem_V hfan' hd).1
  · rw [hf, ← hdy]
    exact yk2_face_snd_mem_vPrime hfan b hb (hf ▸ hy)

/-- 件① HasOrders edge 2：e′² = 1（edgeMap 对合）且 e′ ≠ 1（基 dart 非对角：
e′ b = (b.2, b.1) ≠ b 由单圈性对角-排除 yk8_fst_ne_snd）。 -/
private theorem yk9_edge_hasOrders (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f)) :
    HasOrders (@Hypermap.edgeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) 2 := by
  obtain ⟨hbb, hbf, -, -⟩ := yk9_base_ctx hfan b hb f hf hfan'
  refine ⟨?_, ?_⟩
  · intro i h0i hik
    have hi : i = 1 := by omega
    rw [hi, pow_one]
    intro hcon
    have hap : (@Hypermap.edgeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) b = (b.2, b.1) := by
      rw [yk2_apply_edgeMap hfan' b, if_pos hbb]
      rfl
    have h1 : b = (b.2, b.1) := by
      rw [← hap, hcon]
      exact (Equiv.Perm.one_apply b).symm
    exact (yk8_fst_ne_snd hfan hconf hV b hb f hf hk b hbf)
      (congrArg Prod.snd h1.symm)
  · rw [pow_two]
    exact yk2_edgeMap_involutive hfan'

/-- 件② 主步：n′(n′ d) = d（d ∈ 受限 dart1；中间 dart 留域经
nodeMap_permutes 白给，两次 HnodeMap_val + σ′ 对合）。 -/
private theorem yk9_node_sq_apply (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f))
    {d : V3 × V3} (hd : d ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)) :
    (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
        ((@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d) = d := by
  have hN' := @Hypermap.nodeMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
    (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')
  have hdarts : d ∈ @Hypermap.darts (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan') :=
    (yk2_mem_darts_iff hfan' d).mpr hd
  have hdn : (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d
      ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) :=
    (yk2_mem_darts_iff hfan' _).mp (PermutesOn.apply_mem hN' hdarts)
  obtain ⟨hvN, hdN⟩ := yk9_dart1_ctx hfan b hb f hf hfan' hd
  obtain ⟨-, hσσ⟩ := yk8_sigmaPrime_swap hfan hconf hV b hb f hf hk hfan' d.1 hvN d.2 hdN
  rw [yk8_HnodeMap_val hfan' hdn, yk8_HnodeMap_val hfan' hd]
  show (d.1, sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1
    (sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) d.1 d.2)) = d
  rw [hσσ]

/-- 件② HasOrders node 2：n′² = 1（平方件）且 n′ ≠ 1（n′ b =
(b.1, σ′ b.1 b.2) ≠ b ⟸ σ′ 非平凡）。 -/
private theorem yk9_node_hasOrders (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f)) :
    HasOrders (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) 2 := by
  obtain ⟨hbb, -, hb1v, hb2N⟩ := yk9_base_ctx hfan b hb f hf hfan'
  refine ⟨?_, Equiv.Perm.ext fun d => ?_⟩
  · intro i h0i hik
    have hi : i = 1 := by omega
    rw [hi, pow_one]
    intro hcon
    have hap := yk8_HnodeMap_val hfan' hbb
    have h1 : b = (b.1, sigmaFan 0 (vPrime_p2 V f) (ePrime_p2 E f) b.1 b.2) := by
      rw [← hap, hcon]
      exact (Equiv.Perm.one_apply b).symm
    exact (yk8_sigmaPrime_swap hfan hconf hV b hb f hf hk hfan' b.1 hb1v b.2 hb2N).1
      (congrArg Prod.snd h1.symm)
  · show (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
        ((@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d) = d
    by_cases hd : d ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)
    · exact yk9_node_sq_apply hfan hconf hV b hb f hf hk hfan' hd
    · rw [yk2_apply_nodeMap hfan' d, if_neg hd]
      rw [yk2_apply_nodeMap hfan' d, if_neg hd]

/-- 抽象望远镜：sw∘fc = fc⁻¹∘sw 于 fc-封闭集 f 上时
sw(fc^j y) = fc⁻ʲ(sw y)（任意置换 fc 与映射 sw）。 -/
private theorem yk9_iterate_swap_abstract {α : Type*} [DecidableEq α]
    {fc : Equiv.Perm α} {f : Set α} {sw : α → α} {y : α}
    (hy : y ∈ f) (hcl : ∀ z ∈ f, fc z ∈ f)
    (hcomm : ∀ z ∈ f, sw (fc z) = fc.symm (sw z)) (j : ℕ) :
    sw ((fc ^ j) y) = (fc.symm ^ j) (sw y) := by
  have hmem : ∀ m : ℕ, (fc ^ m) y ∈ f := by
    intro m
    induction m with
    | zero => exact hy
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hcl _ ih
  induction j with
  | zero => simp
  | succ m ih =>
    calc sw ((fc ^ (m + 1)) y) = sw (fc ((fc ^ m) y)) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
      _ = fc.symm (sw ((fc ^ m) y)) := hcomm _ (hmem m)
      _ = (fc.symm ^ (m + 1)) (sw y) := by
          rw [pow_succ', Equiv.Perm.mul_apply, ih]

/-- ③ 主步（望远镜）：swap(fc^j y) = fc⁻ʲ(swap y)（y ∈ f；交换关系
yk8_comm_swap 在 fc z 处的换位形）。 -/
private theorem yk9_face_swap_iterate (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f))
    {y : V3 × V3} (hy : y ∈ f) (j : ℕ) :
    ((fun z : V3 × V3 => (z.2, z.1))
        (((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) ^ j) y)
      = (((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm ^ j)
        ((fun z : V3 × V3 => (z.2, z.1)) y))) := by
  have hfe : f = yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
    (yk7_FF_eq_faceOrbit hfan b hb f hf).symm
  have hiff' : ∀ z : V3 × V3, z ∈ f ↔ z ∈ yk2_faceOrbit 0 (vPrime_p2 V f)
      (ePrime_p2 E f) hfan' b :=
    fun z => ⟨fun hz => hfe ▸ hz, fun hz => hfe.symm ▸ hz⟩
  have hcl : ∀ z ∈ f, (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) z ∈ f := fun z hz =>
    (hiff' _).mpr (yk2_faceOrbit_closure hfan' ((hiff' z).mp hz))
  have hcomm : ∀ z ∈ f, ((fun t : V3 × V3 => (t.2, t.1))
        ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) z))
      = (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm
        ((fun t : V3 × V3 => (t.2, t.1)) z) := by
    intro z hz
    have h1 := yk8_comm_swap hfan hconf hV b hb f hf hk hfan'
      (hcl z hz)
    apply Equiv.injective
    rw [h1, Equiv.apply_symm_apply]
    rw [show (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm
      ((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) z) = z from
      Equiv.apply_symm_apply _ z]
  exact yk9_iterate_swap_abstract (fc := @Hypermap.faceMap (V3 × V3)
    (fun a b' => instDecidableEqProd a b')
    (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) (f := f)
    (sw := fun z : V3 × V3 => (z.2, z.1)) hy hcl hcomm j

/-- 件③ 受限面轨道的 swap 像 = 反向轨道：orbit′(swap y) = swap″f（y ∈ f）。
⊆ 走 swap″f 的 fc-封闭性（交换关系 + yk8_symm_snd 前驱回 f）；
⊇ 走望远镜 + PermutesOn.orbitMap_symm。 -/
private theorem yk9_orbit_swap_image (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f))
    {y : V3 × V3} (hy : y ∈ f) :
    orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
      ((fun z : V3 × V3 => (z.2, z.1)) y)
      = (fun z : V3 × V3 => (z.2, z.1)) '' f := by
  have hbb : b ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) :=
    (yk9_base_ctx hfan b hb f hf hfan').1
  have hfe : f = yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
    (yk7_FF_eq_faceOrbit hfan b hb f hf).symm
  have hP := @Hypermap.faceMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
    (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')
  refine Set.Subset.antisymm ?_ ?_
  · -- ⊆：swap″f fc-封闭 + swap y ∈ swap″f
    have hmem0 : ((fun z : V3 × V3 => (z.2, z.1)) y)
        ∈ ((fun z : V3 × V3 => (z.2, z.1)) '' f) := ⟨y, hy, rfl⟩
    have hcl' : ∀ d ∈ ((fun z : V3 × V3 => (z.2, z.1)) '' f),
        (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d
          ∈ ((fun z : V3 × V3 => (z.2, z.1)) '' f) := by
      rintro d ⟨w, hw, rfl⟩
      have hs := yk8_symm_snd hfan' b hbb f hfe hw
      exact ⟨(@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm w, hs.1,
        (yk8_comm_swap hfan hconf hV b hb f hf hk hfan' hw).symm⟩
    intro z hz
    obtain ⟨n, hn⟩ := hz
    rw [← hn]
    exact yk2_orbit_subset_of_closed hmem0 hcl' n
  · -- ⊇：swap(fc^m y) = fc⁻ᵐ(swap y) ∈ orbit fc⁻¹ = orbit fc
    have h2 : y ∈ yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
      hfe ▸ hy
    have horbY : orbitMap (@Hypermap.faceMap (V3 × V3)
        (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) y = f := by
      have h3 : orbitMap (@Hypermap.faceMap (V3 × V3)
          (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) y
          = yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
        orbitMap_eq_of_mem hP h2
      rw [← hfe] at h3
      exact h3
    have hsymm := PermutesOn.orbitMap_symm hP
      ((fun z : V3 × V3 => (z.2, z.1)) y)
    intro w hw
    obtain ⟨y', hy', hdy'⟩ := hw
    obtain ⟨m, hm⟩ : y' ∈ orbitMap (@Hypermap.faceMap (V3 × V3)
        (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) y := by
      rw [horbY]
      exact hy'
    rw [← hdy', ← hm, yk9_face_swap_iterate hfan hconf hV b hb f hf hk hfan' hy m]
    rw [← hsymm]
    exact pow_apply_mem_orbitMap
      (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')).symm m
      ((fun z : V3 × V3 => (z.2, z.1)) y)

/-- 件④ HasOrders face k：f′^k = 1（d ∈ f 走 pow_ncard 于 orbit = f；
d ∈ swap″f 走 ③ + yk8_swap_image_ncard；d ∉ dart1′ 走恒等）且
f′^i ≠ 1（0 < i < k；orbitMap_pow_inj 于 orbit′ b = f）。 -/
private theorem yk9_face_hasOrders (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f)) :
    HasOrders (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) f.ncard := by
  have hfe : f = yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
    (yk7_FF_eq_faceOrbit hfan b hb f hf).symm
  have hP := @Hypermap.faceMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
    (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')
  have horbb : orbitMap (@Hypermap.faceMap (V3 × V3)
      (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) b = f := hfe.symm
  refine ⟨?_, Equiv.Perm.ext fun d => ?_⟩
  · intro i h0i hik hcon
    have hnc : i < (orbitMap (@Hypermap.faceMap (V3 × V3)
        (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) b).ncard := by
      rw [horbb]
      exact hik
    exact orbitMap_pow_inj hP (x := b) (a := 0) (b := i) h0i hnc
      (by rw [hcon]; simp)
  · show (((@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) ^ f.ncard) d) = d
    by_cases hd : d ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f)
    · have hU := yk2_dart1_ePrime_eq_union_swap hfan b hb f hf
      have hdU : d ∈ f ∪ ((fun z : V3 × V3 => (z.2, z.1)) '' f) := by
        rw [← hU]
        exact hd
      rcases hdU with hdm | ⟨y, hy, hdy⟩
      · have hdb : d ∈ orbitMap (@Hypermap.faceMap (V3 × V3)
            (fun a b' => instDecidableEqProd a b')
            (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) b := by
          rw [horbb]
          exact hdm
        have hpow := PermutesOn.pow_ncard_orbitMap_apply_self hP d
        rwa [orbitMap_eq_of_mem hP hdb, horbb] at hpow
      · have hnc : (orbitMap (@Hypermap.faceMap (V3 × V3)
              (fun a b' => instDecidableEqProd a b')
              (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
              ((fun z : V3 × V3 => (z.2, z.1)) y)).ncard = f.ncard := by
          rw [yk9_orbit_swap_image hfan hconf hV b hb f hf hk hfan' hy,
            yk8_swap_image_ncard]
        have hpow := PermutesOn.pow_ncard_orbitMap_apply_self hP
          ((fun z : V3 × V3 => (z.2, z.1)) y)
        rwa [hnc, hdy] at hpow
    · have h1 : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d = d := by
        rw [yk2_apply_faceMap hfan' d, if_neg hd]
      have hrec : ∀ n : ℕ, ((@Hypermap.faceMap (V3 × V3)
          (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) ^ n) d = d := by
        intro n
        induction n with
        | zero => rfl
        | succ m ih =>
          rw [pow_succ, Equiv.Perm.mul_apply, h1, ih]
      exact hrec _

/-- 合取二 swap 侧：n′″swap″f = f（n′″f = swap″f 平方回卷经 n′² = 1）。 -/
private theorem yk9_nodePrime_image_swapImage (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f)) :
    ((fun d : V3 × V3 => (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d)
      '' ((fun z : V3 × V3 => (z.2, z.1)) '' f)) = f := by
  have hbb : b ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) :=
    (yk9_base_ctx hfan b hb f hf hfan').1
  have hfe : f = yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
    (yk7_FF_eq_faceOrbit hfan b hb f hf).symm
  have hiff' : ∀ z : V3 × V3, z ∈ f ↔ z ∈ yk2_faceOrbit 0 (vPrime_p2 V f)
      (ePrime_p2 E f) hfan' b :=
    fun z => ⟨fun hz => hfe ▸ hz, fun hz => hfe.symm ▸ hz⟩
  have hsq : ∀ d ∈ f, (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
      ((@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d) = d := by
    intro d hd
    exact yk9_node_sq_apply hfan hconf hV b hb f hf hk hfan'
      (yk2_faceOrbit_subset_dart1 hfan' b hbb ((hiff' d).mp hd))
  have himg : ((fun d : V3 × V3 => (@Hypermap.nodeMap (V3 × V3)
        (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d)
      '' ((fun d : V3 × V3 => (@Hypermap.nodeMap (V3 × V3)
        (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d) '' f))
      = ((fun d : V3 × V3 => (@Hypermap.nodeMap (V3 × V3)
        (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
        ((@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d)) '' f) :=
    Set.image_image _ _ _
  rw [← yk8_nodePrime_image_swap hfan hconf hV b hb f hf hk hfan', himg]
  ext z
  constructor
  · rintro ⟨d, hd, hrfl⟩
    have hrfl' : (@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan'))
        ((@Hypermap.nodeMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d) = z := hrfl
    rw [← hrfl', hsq d hd]
    exact hd
  · intro hz
    exact ⟨z, hz, hsq z hz⟩

/-- 合取二：受限 dart 的 face-轨道 ∪ 其 node-像 = 全 dart 集（Dih2k 第二合取；
d ∈ f 支 yk8_nodePrime_image_swap + dart1 分解；d ∈ swap″f 支 ③ +
yk9_nodePrime_image_swapImage）。 -/
private theorem yk9_dih2k_union (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f))
    (d : V3 × V3) (hd : d ∈ @Hypermap.darts (V3 × V3)
      (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) :
    orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d
      ∪ ((fun z : V3 × V3 => (@Hypermap.nodeMap (V3 × V3)
          (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) z)
        '' orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d)
      = (↑(@Hypermap.darts (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) : Set (V3 × V3)) := by
  have hfe : f = yk2_faceOrbit 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan' b :=
    (yk7_FF_eq_faceOrbit hfan b hb f hf).symm
  have hP := @Hypermap.faceMap_permutes (V3 × V3) (fun a b' => instDecidableEqProd a b')
    (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')
  have horbb : orbitMap (@Hypermap.faceMap (V3 × V3)
      (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) b = f := hfe.symm
  have hU := yk2_dart1_ePrime_eq_union_swap hfan b hb f hf
  have hdarts : (↑(@Hypermap.darts (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) : Set (V3 × V3))
      = dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) := yk2_darts_coe hfan'
  have hd1 : d ∈ dart1OfFan (vPrime_p2 V f) (ePrime_p2 E f) :=
    (yk2_mem_darts_iff hfan' d).mp hd
  by_cases hdm : d ∈ f
  · have hdb : d ∈ orbitMap (@Hypermap.faceMap (V3 × V3)
        (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) b := by
      rw [horbb]
      exact hdm
    have horb : orbitMap (@Hypermap.faceMap (V3 × V3)
        (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d = f := by
      rw [orbitMap_eq_of_mem hP hdb, horbb]
    rw [horb, yk8_nodePrime_image_swap hfan hconf hV b hb f hf hk hfan', hdarts, ← hU]
  · have hdU : d ∈ f ∪ ((fun z : V3 × V3 => (z.2, z.1)) '' f) := by
      rw [← hU]
      exact hd1
    rcases hdU with h2 | ⟨y, hy, hdy⟩
    · exact absurd h2 hdm
    · have horb : orbitMap (@Hypermap.faceMap (V3 × V3)
          (fun a b' => instDecidableEqProd a b')
          (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan')) d
          = ((fun z : V3 × V3 => (z.2, z.1)) '' f) := by
        rw [← hdy]
        exact yk9_orbit_swap_image hfan hconf hV b hb f hf hk hfan' hy
      rw [horb, yk9_nodePrime_image_swapImage hfan hconf hV b hb f hf hk hfan',
        Set.union_comm _ f, hdarts, ← hU]

/-- 帽石：checkpoint 3 · Dih2k（HOL DIH_K_HYP_E_PRIME；9j.4 NEEDS ①-④ 消账）。
card = 2k（yk8_Hdarts_card）+ 合取二（yk9_dih2k_union）+ HasOrders
face k（yk9_face_hasOrders）/ edge 2（yk9_edge_hasOrders）/
node 2（yk9_node_hasOrders）。 -/
private theorem yk9_Dih2k (hfan : FAN 0 V E)
    (hconf : conformingFan 0 V E hfan) (hV : V.Finite)
    (b : V3 × V3) (hb : b ∈ dart1OfFan V E) (f : Set (V3 × V3))
    (hf : f = yk2_faceOrbit 0 V E hfan b) (hk : 2 < f.ncard)
    (hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 E f)) :
    @Dih2k (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 (vPrime_p2 V f) (ePrime_p2 E f) hfan') f.ncard := by
  refine ⟨yk8_Hdarts_card hfan hconf hV b hb f hf hk hfan', ?_, ?_, ?_, ?_⟩
  · intro d hd
    exact yk9_dih2k_union hfan hconf hV b hb f hf hk hfan' d hd
  · exact yk9_face_hasOrders hfan hconf hV b hb f hf hk hfan'
  · exact yk9_edge_hasOrders hfan hconf hV b hb f hf hk hfan'
  · exact yk9_node_hasOrders hfan hconf hV b hb f hf hk hfan'
/-! ### 9l. ykit10 波（Lane AT 2026-10-23）：解析装配波——tau4/5/6 三枚
e2e 直源闭合 + perimeter 接线图刷新。全 private（yk10_*），纯追加。

前置桥盘点（AJ/AQ 两波记账的"装配前置"）：`fully_surrounded_imp_conforming`
在本文件内**早已真证**——§4 `p6g_fullySurrounded_conforming`（FullySurrounded
直接输入，证明体 = PIIJBJK 消费），本波直接消费，无缺口。

消费链（三枚 tau 同构，一枚共享 aux）：
  目标 `tauVEF f` ⟸ `yk6_tauVEF_eq_tauFun_ePrime`（AE 波已备）；
  `dTame k ≤ tauFun (vPrime, ePrime) f` ⟸ `hineq : JEJTVGB_std_concl` 在
  `(vPrime_p2 V f, ePrime_p2 (ESTD V) f, f)` 上的实例，七前提：
  ① ConvexLocalFan = 本波 `yk10_convexLocalFan`——LocalFan 面 = §9k
    `yk9_Dih2k`（实例转移件 yk10_Dih2k_congr）+ `yk7_FF_eq_faceOrbit` +
    `yk2_FAN_vPrime_ePrime`；azim≤π 面 = `yk6_azimInFan_ePrime_eq` +
    `wk_azimInFan_eq_azimDart` + FullySurrounded；wedge 面 = 本波
    `yk10_vPrime_subset_wedgeInFanGe`：§9g 锚3（AFF_GT_SUBSET_…_tl）+
    PlanarityAuto13 POINT_IN_CLOSURE_AFF_GT_1_2 + ConformingAuto1 锚2
    （DARTSET_LEADS_INTO_SUBSET_WDART_FAN，conformingHalfSpace 支）+
    w_dart = 开 wedge（FullySurrounded 给 CARD>1）+ 闭扇收口
    `yk10_closure_wedge_subset_wedgeGe`（HOL CLOSED_WEDGE_LT_PI 的 Lean
    折算；PackingAuto18:5631-5644 同名件为未证桩，本波自证——路线：
    wedge ⊆ aff_ge 2+2（wedge_eq_affGt + affGt⊆affGe）+ aff_ge 2+2 闭
    （= aff_ge 1+3 两片之并，各片 = 平移闭锥 yk10_cone3）+ aff_ge 2+2 ⊆
    wedge_ge（azim_eq_azim_iff 逐射线等值 + wedge_eq_affGt 严格内侧；
    = LocalAuto5 WEDGE_GE_EQ_AFF_GE ←方向的轻量重组——LA5 与 PackingAuto18
    声明重名（AFF_GE_MONO_TRANS）不可 import，故不引）；
  ② Packing vPrime / ③ vPrime ⊆ ballAnnulus = yk6（AE 波）；
  ④ 4 ≤ ncard vPrime = yk8（AJ 波，消费 p6g 桥的 conformingFan + V.Finite
    ——V 有限由 Packing + annulus 有界，本波 yk10_packingFinite；
    Assembly 同名件 private 且本模块不 import Assembly，机械复制）；
  ⑤ ncard vPrime ≤ 6 = yk6_ncard_vPrime_le + ncard f = k ≤ 6；
  ⑥ 非边前提 = 本波 `yk10_diag`：{a,b} ∉ E 支 = LpFan.3（yk6 路线）；
    chord 支 = conforming_diagonal 合取支消费（hconf.2.2.2.2.2；上游
    GGZWYRM 已在 ConformingAuto20 真证）——f1Fan 两分支出 (a,b)/(b,a) ∈ f
    与 {a,b} ∉ ePrime 矛盾；第三支 affGt {0} {a,b} ⊆ dartsetLeadsIntoFan f
    与 (a,b) ∈ dart1 给出的 affGt ⊆ affGe ⊆ xfan（PlanarityAuto13
    AFF_GE_SUBSET_XFAN）、dartsetLeadsInto ⊆ yfan（PlanarityComponent
    dartset_leads_into_subset_yfan）夹逼出 affGt ∋ 中点 ∈ xfan ∩ yfan = ∅
    矛盾（= HOL diag_not_in_dart lp_main_estimate:415 的 pair-dart 重装，
    超图同构步消失）；
  ⑦ 边前提 = yk6_local_std。
import 变更：本波在文件头追加 `import Kepler.Geom.AzimLemmas`
（azim_eq_azim_iff / azim_eq_zero_iff_alt 所在；只依赖 Geom.Azim/Aff，
与本模块无环）。 -/

/-! #### 9l.0 杂件 -/

/-- V 有限（Packing + annulus 有界）。Assembly.packingFiniteOfBallAnnulus
（:3643，private）的 TameLp 本地副本——本模块不 import Assembly（会环），
11 行机械复制。 -/
private theorem yk10_packingFinite (hV : Packing V) (hsub : V ⊆ ballAnnulus) :
    V.Finite := by
  have hVb : V ⊆ Metric.ball 0 3 := by
    intro v hv
    have hmem : ‖v‖ ≤ 2 * h0 := by
      have hp := hsub hv
      simp only [ballAnnulus, Set.mem_sdiff] at hp
      have h'd := Metric.mem_closedBall.mp hp.1
      rw [dist_zero_right] at h'd
      exact h'd
    have hh0 : (2 : ℝ) * h0 < 3 := by
      show (2 : ℝ) * 1.26 < 3
      norm_num
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hmem]
  have hveq : V = V ∩ Metric.ball 0 3 := (Set.inter_eq_left.mpr hVb).symm
  rw [hveq]
  exact hV.finite_inter_ball 3

/-- affGt ⊆ affGe（Affsign 见证 0 < ⟹ 0 ≤ 的两行提升）。 -/
private theorem yk10_affGt_subset_affGe {s t : Set V3} :
    affGt s t ⊆ affGe s t := by
  intro y hy
  obtain ⟨g, hfin, hsum, hpos, hone⟩ := hy
  exact ⟨g, hfin, hsum, fun w hw => le_of_lt (hpos w hw), hone⟩

/-! #### 9l.1 闭扇 kit（HOL CLOSED_WEDGE_LT_PI，leaf_cell.hl:3659 的 Lean 折算；
PackingAuto18:5631-5644 的同名件为未证桩，本波自证）。

路线：closure(开 wedge) ⊆ aff_ge 2+2（wedge = affGt 2+2，wedge_eq_affGt）
⊇ 闭（aff_ge 2+2 = aff_ge 1+3 两片之并，每片 = 平移 yk10_cone3 闭锥——
PlanarityAuto12 coneF 机器的 yk10 本地副本）⊆ wedge_ge（yk10 轻量 ← 方向）。
`wedge_ge` 的 0 ≤ 侧由 `azim_nonneg` 无条件白给。 -/

private def yk10_cone1 (a : V3) : Set V3 :=
  {z : V3 | ∃ s : ℝ, 0 ≤ s ∧ z = s • a}

private def yk10_cone2 (a b : V3) : Set V3 :=
  {z : V3 | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ z = s • a + t • b}

private def yk10_cone3 (a b c : V3) : Set V3 :=
  {z : V3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ 0 ≤ r ∧ z = s • a + t • b + r • c}

private def yk10_coneF {n : ℕ} (v : Fin n → V3) : Set V3 :=
  {z : V3 | ∃ c : Fin n → ℝ, (∀ j, 0 ≤ c j) ∧ z = ∑ j, c j • v j}

/-- 有限生成非负锥闭（线性独立情形 = 闭嵌入像；PlanarityAuto12
isClosed_coneF 的本地副本）。 -/
private theorem yk10_isClosed_coneF {n : ℕ} {v : Fin n → V3}
    (hli : LinearIndependent ℝ v) : IsClosed (yk10_coneF v) := by
  let L : (Fin n → ℝ) →ₗ[ℝ] V3 :=
    { toFun := fun c => ∑ j, c j • v j
      map_add' := by
        intro c d
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        simp [Finset.smul_sum, mul_smul] }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro c d hcd
    funext j
    have h0 : ∑ k, (c k - d k) • v k = 0 := by
      have h1 : L (c - d) = 0 := by rw [map_sub, hcd, sub_self]
      change (∑ k, (c - d) k • v k) = 0 at h1
      simpa only [Pi.sub_apply] using h1
    have := Fintype.linearIndependent_iff.mp hli (fun k => c k - d k) h0 j
    linarith
  have hemb : Topology.IsClosedEmbedding L := L.isClosedEmbedding_of_injective hker
  set O : Set (Fin n → ℝ) := {c : Fin n → ℝ | ∀ j, 0 ≤ c j} with hOdef
  have hO : IsClosed O := by
    rw [show O = ⋂ j, {c : Fin n → ℝ | 0 ≤ c j} by
      ext c; simp [hOdef]]
    exact isClosed_iInter (fun j => isClosed_Ici.preimage (continuous_apply j))
  have hset : yk10_coneF v = L '' O := by
    ext z; constructor
    · rintro ⟨c, hc, hz⟩; exact ⟨c, hc, by rw [hz]; rfl⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  rw [hset]
  exact hemb.isClosedMap O hO

private theorem yk10_cone2_eq_coneF (a b : V3) : yk10_cone2 a b = yk10_coneF ![a, b] := by
  ext z; constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    refine ⟨![s, t], fun j => by fin_cases j <;> simp [hs, ht], ?_⟩
    simp [Fin.sum_univ_two]
  · rintro ⟨f, hf, hz⟩
    exact ⟨f 0, f 1, hf 0, hf 1, by rw [hz]; simp [Fin.sum_univ_two]⟩

private theorem yk10_cone3_eq_coneF (a b c : V3) :
    yk10_cone3 a b c = yk10_coneF ![a, b, c] := by
  ext z; constructor
  · rintro ⟨s, t, r, hs, ht, hr, rfl⟩
    refine ⟨![s, t, r], fun j => by fin_cases j <;> simp [hs, ht, hr], ?_⟩
    simp [Fin.sum_univ_three]
  · rintro ⟨f, hf, hz⟩
    exact ⟨f 0, f 1, f 2, hf 0, hf 1, hf 2, by rw [hz]; simp [Fin.sum_univ_three]⟩

private theorem yk10_isClosed_cone1 (a : V3) : IsClosed (yk10_cone1 a) := by
  by_cases ha : a = 0
  · have h0 : yk10_cone1 a = {0} := by
      ext z; constructor
      · rintro ⟨s, _, rfl⟩; rw [ha, smul_zero]; simp
      · intro hz; rw [hz]; exact ⟨0, le_refl 0, by rw [ha, smul_zero]⟩
    rw [h0]; exact isClosed_singleton
  · have hset : yk10_cone1 a = (fun t : ℝ => t • a) '' Set.Ici (0 : ℝ) := by
      ext z; constructor
      · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    rw [hset]
    exact (isClosedEmbedding_smul_left ha).isClosedMap (Set.Ici (0 : ℝ)) isClosed_Ici

/-- 锥的 Carathéodory 降元（PlanarityAuto12 exists_nonneg_rep_with_zero
本地副本）。 -/
private theorem yk10_exists_nonneg_rep_with_zero {n : ℕ}
    {v : Fin n → V3} {coef : Fin n → ℝ}
    (hrel : ∃ g : Fin n → ℝ, (∑ j, g j • v j = 0) ∧ (∃ j, g j ≠ 0))
    (hcoef : ∀ j, 0 ≤ coef j) :
    ∃ coef' : Fin n → ℝ, (∀ j, 0 ≤ coef' j) ∧ (∃ j, coef' j = 0) ∧
      (∑ j, coef' j • v j = ∑ j, coef j • v j) := by
  obtain ⟨g, hgsum, j, hgj⟩ := hrel
  have hrel' : ∃ g' : Fin n → ℝ, (∑ k, g' k • v k = 0) ∧ (∃ k, 0 < g' k) := by
    by_cases h : ∃ k, 0 < g k
    · obtain ⟨k, hk⟩ := h; exact ⟨g, hgsum, k, hk⟩
    · push Not at h
      refine ⟨-g, ?_, j, ?_⟩
      · have : ∑ k, (-g) k • v k = -∑ k, g k • v k := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro k _
          rw [Pi.neg_apply, neg_smul]
        rw [this, hgsum, neg_zero]
      · have : g j < 0 := lt_of_le_of_ne (h j) hgj
        simpa using neg_pos.mpr this
  obtain ⟨g', hg'sum, j, hg'j⟩ := hrel'
  set S : Finset (Fin n) := Finset.univ.filter (fun k => 0 < g' k) with hSdef
  have hSne : S.Nonempty := ⟨j, by simp [hSdef, hg'j]⟩
  obtain ⟨j0, hj0S, hj0min⟩ := Finset.exists_min_image S (fun k => coef k / g' k) hSne
  have hg'j0 : 0 < g' j0 := (Finset.mem_filter.mp hj0S).2
  set lam : ℝ := coef j0 / g' j0 with hlam
  have hlam_nonneg : 0 ≤ lam := by
    rw [hlam]; exact div_nonneg (hcoef j0) (le_of_lt hg'j0)
  refine ⟨fun k => coef k - lam * g' k, ?_, ⟨j0, ?_⟩, ?_⟩
  · intro k
    by_cases hk : k ∈ S
    · have hg'k : 0 < g' k := (Finset.mem_filter.mp hk).2
      have hle : lam ≤ coef k / g' k := by rw [hlam]; exact hj0min k hk
      have h1 : lam * g' k ≤ coef k := by
        have := mul_le_mul_of_nonneg_right hle (le_of_lt hg'k)
        rwa [div_mul_cancel₀ _ (ne_of_gt hg'k)] at this
      linarith
    · have hg'k : g' k ≤ 0 := by
        have := Finset.mem_filter.not.mp hk
        simp only [Finset.mem_univ, true_and] at this
        exact not_lt.mp this
      have h2 : lam * g' k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam_nonneg hg'k
      linarith [hcoef k]
  · simp only [hlam]
    rw [div_mul_cancel₀ _ (ne_of_gt hg'j0), sub_self]
  · have hsum_eq : ∑ k, (coef k - lam * g' k) • v k =
        ∑ k, coef k • v k - lam • ∑ k, g' k • v k := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [sub_smul, mul_smul]
    rw [hsum_eq, hg'sum, smul_zero, sub_zero]

private theorem yk10_cone2_eq_union_single (a b : V3)
    (hdep : ¬ LinearIndependent ℝ ![a, b]) :
    yk10_cone2 a b = yk10_cone1 a ∪ yk10_cone1 b := by
  ext z; constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    obtain ⟨coef', hcoef', hzero, hsum⟩ :=
      yk10_exists_nonneg_rep_with_zero (v := ![a, b]) (coef := ![s, t])
        (Fintype.not_linearIndependent_iff.mp hdep)
        (by intro j; fin_cases j <;> simp [hs, ht])
    obtain ⟨j0, hj0⟩ := hzero
    have hsum2 : s • a + t • b = coef' 0 • a + coef' 1 • b := by
      simpa [Fin.sum_univ_two] using hsum.symm
    rw [hsum2]
    have hj01 : j0 = 0 ∨ j0 = 1 := by fin_cases j0 <;> simp
    rcases hj01 with rfl | rfl
    · right
      refine ⟨coef' 1, hcoef' 1, ?_⟩
      rw [hj0, zero_smul, zero_add]
    · left
      refine ⟨coef' 0, hcoef' 0, ?_⟩
      rw [hj0, zero_smul, add_zero]
  · rintro (h | h)
    · obtain ⟨s, hs, rfl⟩ := h
      exact ⟨s, 0, hs, le_refl 0, by rw [zero_smul, add_zero]⟩
    · obtain ⟨t, ht, rfl⟩ := h
      exact ⟨0, t, le_refl 0, ht, by rw [zero_smul, zero_add]⟩

private theorem yk10_cone3_eq_union_pair (a b c : V3)
    (hdep : ¬ LinearIndependent ℝ ![a, b, c]) :
    yk10_cone3 a b c = yk10_cone2 a b ∪ yk10_cone2 a c ∪ yk10_cone2 b c := by
  ext z; constructor
  · rintro ⟨s, t, r, hs, ht, hr, rfl⟩
    obtain ⟨coef', hcoef', hzero, hsum⟩ :=
      yk10_exists_nonneg_rep_with_zero (v := ![a, b, c]) (coef := ![s, t, r])
        (Fintype.not_linearIndependent_iff.mp hdep)
        (by intro j; fin_cases j <;> simp [hs, ht, hr])
    obtain ⟨j0, hj0⟩ := hzero
    have hsum2 : s • a + t • b + r • c = coef' 0 • a + coef' 1 • b + coef' 2 • c := by
      simpa [Fin.sum_univ_three] using hsum.symm
    rw [hsum2]
    have hj01 : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 := by fin_cases j0 <;> simp
    rcases hj01 with rfl | rfl | rfl
    · right
      refine ⟨coef' 1, coef' 2, hcoef' 1, hcoef' 2, ?_⟩
      rw [hj0, zero_smul, zero_add]
    · left; right
      refine ⟨coef' 0, coef' 2, hcoef' 0, hcoef' 2, ?_⟩
      rw [hj0, zero_smul, add_zero]
    · left; left
      refine ⟨coef' 0, coef' 1, hcoef' 0, hcoef' 1, ?_⟩
      rw [hj0, zero_smul, add_zero]
  · rintro ((h | h) | h)
    · obtain ⟨s, t, hs, ht, rfl⟩ := h
      exact ⟨s, t, 0, hs, ht, le_refl 0, by rw [zero_smul, add_zero]⟩
    · obtain ⟨s, r, hs, hr, rfl⟩ := h
      exact ⟨s, 0, r, hs, le_refl 0, hr, by simp⟩
    · obtain ⟨t, r, ht, hr, rfl⟩ := h
      exact ⟨0, t, r, le_refl 0, ht, hr, by simp⟩

private theorem yk10_isClosed_cone2 (a b : V3) : IsClosed (yk10_cone2 a b) := by
  by_cases hli : LinearIndependent ℝ ![a, b]
  · rw [yk10_cone2_eq_coneF]; exact yk10_isClosed_coneF hli
  · rw [yk10_cone2_eq_union_single a b hli]
    exact (yk10_isClosed_cone1 a).union (yk10_isClosed_cone1 b)

private theorem yk10_isClosed_cone3 (a b c : V3) : IsClosed (yk10_cone3 a b c) := by
  by_cases hli : LinearIndependent ℝ ![a, b, c]
  · rw [yk10_cone3_eq_coneF]; exact yk10_isClosed_coneF hli
  · rw [yk10_cone3_eq_union_pair a b c hli]
    exact ((yk10_isClosed_cone2 a b).union (yk10_isClosed_cone2 a c)).union
      (yk10_isClosed_cone2 b c)

/-- 四点并集的求和分裂（去重 toFinset = 显式四元；pairwise distinct 前提）。 -/
private theorem yk10_sum4 {g : V3 → ℝ} {a b c d : V3} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hfin : ({a, b} ∪ {c, d} : Set V3).Finite) :
    ∑ w ∈ hfin.toFinset, g w = g a + g b + g c + g d ∧
      ∑ w ∈ hfin.toFinset, g w • w = g a • a + g b • b + g c • c + g d • d := by
  have h4 : hfin.toFinset = ({a, b, c, d} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [h4]
  constructor
  · rw [Finset.sum_insert (by simp [hab, hac, had]),
      Finset.sum_insert (by simp [hbc, hbd]),
      Finset.sum_insert (by simp [hcd]), Finset.sum_singleton]
    ring
  · rw [Finset.sum_insert (by simp [hab, hac, had]),
      Finset.sum_insert (by simp [hbc, hbd]),
      Finset.sum_insert (by simp [hcd]), Finset.sum_singleton]
    abel

/-- aff_ge {u0,u1} {u2,u3} 的显式系数刻画（AFF_GE_1_3 的 2+2 伙伴）。 -/
private theorem yk10_mem_affGe22_iff {u0 u1 u2 u3 : V3} (h01 : u0 ≠ u1)
    (h02 : u2 ≠ u0) (h03 : u3 ≠ u0) (h12 : u2 ≠ u1) (h13 : u3 ≠ u1) (h23 : u2 ≠ u3)
    {y : V3} :
    y ∈ affGe ({u0, u1} : Set V3) ({u2, u3} : Set V3) ↔
      ∃ t1 t2 t3 t4 : ℝ, 0 ≤ t3 ∧ 0 ≤ t4 ∧ t1 + t2 + t3 + t4 = 1 ∧
        y = t1 • u0 + t2 • u1 + t3 • u2 + t4 • u3 := by
  have hfin : ({u0, u1} ∪ {u2, u3} : Set V3).Finite :=
    ((Set.finite_singleton u1).insert u0).union ((Set.finite_singleton u3).insert u2)
  unfold affGe Affsign
  constructor
  · intro h
    obtain ⟨f, hfin, hp⟩ := Set.mem_setOf_eq.mp h
    have hsum : y = ∑ w ∈ hfin.toFinset, f w • w := hp.1
    have hpos : ∀ w ∈ ({u2, u3} : Set V3), 0 ≤ f w := hp.2.1
    have hone : ∑ w ∈ hfin.toFinset, f w = 1 := hp.2.2
    have hs := yk10_sum4 (g := f) (a := u0) (b := u1) (c := u2) (d := u3) h01
      h02.symm h03.symm h12.symm h13.symm h23 hfin
    refine ⟨f u0, f u1, f u2, f u3, hpos u2 (by simp), hpos u3 (by simp), ?_, ?_⟩
    · linarith [hone, hs.1]
    · exact hsum.trans hs.2
  · rintro ⟨t1, t2, t3, t4, ht3, ht4, hsum4, hyeq⟩
    set g : V3 → ℝ := fun z => if z = u0 then t1 else if z = u1 then t2
      else if z = u2 then t3 else t4 with hgd
    have hs := yk10_sum4 (g := g) (a := u0) (b := u1) (c := u2) (d := u3) h01
      h02.symm h03.symm h12.symm h13.symm h23 hfin
    have hg0 : g u0 = t1 := by simp [hgd]
    have hg1 : g u1 = t2 := by simp [hgd, h01.symm, h12.symm]
    have hg2 : g u2 = t3 := by simp [hgd, h02, h12]
    have hg3 : g u3 = t4 := by simp [hgd, h03, h13, h23.symm]
    refine ⟨g, hfin, ?_, ?_, ?_⟩
    · -- y = ∑ g w • w（第一合取）
      rw [hs.2, hg0, hg1, hg2, hg3]
      exact hyeq
    · -- u2/u3 侧系数非负
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw
      · rw [hw]
        have hgu2 : g u2 = t3 := hg2
        rw [hgu2]
        exact ht3
      · rw [hw]
        have hgu3 : g u3 = t4 := hg3
        rw [hgu3]
        exact ht4
    · -- ∑ g w = 1（第三合取）
      rw [hs.1, hg0, hg1, hg2, hg3]
      exact hsum4

/-- aff_ge 1+3 = 平移闭锥（PlanarityAuto12 affGe_triple_eq_cone 的本地副本）。 -/
private theorem yk10_affGe_triple_eq_cone (x v u w : V3)
    (hdis : Disjoint ({x} : Set V3) ({v, u, w} : Set V3)) :
    affGe ({x} : Set V3) ({v, u, w} : Set V3) =
      {y : V3 | (y - x) ∈ yk10_cone3 (v - x) (u - x) (w - x)} := by
  rw [AFF_GE_1_3 x v u w hdis]
  ext y; constructor
  · rintro ⟨t1, t2, t3, t4, ht2, ht3, ht4, hsum, hy⟩
    exact ⟨t2, t3, t4, ht2, ht3, ht4, by
      rw [hy, show t1 = 1 - t2 - t3 - t4 from by linarith]; module⟩
  · rintro ⟨t2, t3, t4, ht2, ht3, ht4, hy⟩
    refine ⟨1 - t2 - t3 - t4, t2, t3, t4, ht2, ht3, ht4, by ring, ?_⟩
    rw [show y = (y - x) + x from (sub_add_cancel y x).symm, hy]
    module

/-- aff_ge {u0,u1} {u2,u3} = 两个平移闭锥之并（u1-系数变号 → 沿 u1−u0
轴线的正/负两侧；cone3 = 有限生成闭锥）。 -/
private theorem yk10_affGe22_eq_union {u0 u1 u2 u3 : V3}
    (h01 : u0 ≠ u1) (h02 : u2 ≠ u0) (h03 : u3 ≠ u0) (h12 : u2 ≠ u1)
    (h13 : u3 ≠ u1) (h23 : u2 ≠ u3) :
    affGe ({u0, u1} : Set V3) ({u2, u3} : Set V3) =
      {y : V3 | y - u0 ∈ yk10_cone3 (u1 - u0) (u2 - u0) (u3 - u0)} ∪
        {y : V3 | y - u0 ∈ yk10_cone3 (u0 - u1) (u2 - u0) (u3 - u0)} := by
  ext y
  constructor
  · intro hy
    obtain ⟨t1, t2, t3, t4, ht3, ht4, hsum4, hyeq⟩ :=
      (yk10_mem_affGe22_iff h01 h02 h03 h12 h13 h23 (y := y)).mp hy
    have ht1 : t1 = 1 - t2 - t3 - t4 := by linarith
    have hcombo : y - u0 = t2 • (u1 - u0) + t3 • (u2 - u0) + t4 • (u3 - u0) := by
      rw [hyeq, ht1]
      module
    by_cases hsign : 0 ≤ t2
    · left
      exact ⟨t2, t3, t4, hsign, ht3, ht4, hcombo⟩
    · right
      have ht2neg : t2 < 0 := by
        by_contra hc
        exact hsign (le_of_not_gt hc)
      have ht2n : 0 ≤ -t2 := by linarith
      exact ⟨-t2, t3, t4, ht2n, ht3, ht4, by rw [hcombo]; module⟩
  · intro hy
    rcases Set.mem_union _ _ _ |>.mp hy with h | h
    · obtain ⟨c1, c2, c3, hc1, hc2, hc3, hyeq⟩ := Set.mem_setOf_eq.mp h
      refine (yk10_mem_affGe22_iff h01 h02 h03 h12 h13 h23 (y := y)).mpr
        ⟨1 - c1 - c2 - c3, c1, c2, c3, hc2, hc3, by ring, ?_⟩
      conv_lhs => rw [show y = (y - u0) + u0 from (sub_add_cancel y u0).symm]
      rw [hyeq]
      module
    · obtain ⟨c1, c2, c3, hc1, hc2, hc3, hyeq⟩ := Set.mem_setOf_eq.mp h
      refine (yk10_mem_affGe22_iff h01 h02 h03 h12 h13 h23 (y := y)).mpr
        ⟨1 + c1 - c2 - c3, -c1, c2, c3, hc2, hc3, by ring, ?_⟩
      conv_lhs => rw [show y = (y - u0) + u0 from (sub_add_cancel y u0).symm]
      rw [hyeq]
      module

/-- aff_ge 2+2 闭（= CLOSED_AFF_GE 的 2+2 形；两平移闭锥之并）。 -/
private theorem yk10_isClosed_affGe22 {u0 u1 u2 u3 : V3}
    (h01 : u0 ≠ u1) (h02 : u2 ≠ u0) (h03 : u3 ≠ u0) (h12 : u2 ≠ u1)
    (h13 : u3 ≠ u1) (h23 : u2 ≠ u3) :
    IsClosed (affGe ({u0, u1} : Set V3) ({u2, u3} : Set V3)) := by
  have hcont1 : Continuous (fun y : V3 => y - u0) :=
    continuous_id.sub continuous_const
  rw [yk10_affGe22_eq_union h01 h02 h03 h12 h13 h23]
  refine IsClosed.union
    ((yk10_isClosed_cone3 (u1 - u0) (u2 - u0) (u3 - u0)).preimage hcont1) ?_
  exact ((yk10_isClosed_cone3 (u0 - u1) (u2 - u0) (u3 - u0)).preimage hcont1)

/-- HOL WEDGE_GE_EQ_AFF_GE 的 ← 方向（azim < π 时 aff_ge 2+2 ⊆ wedge_ge）
的轻量重组：轴上 azim = 0（退化支）；单射线侧 azim_eq_azim_iff 逐射线等值；
严格内侧 wedge_eq_affGt。 -/
private theorem yk10_affGe22_subset_wedgeGe {u0 u1 u2 u3 : V3}
    (h2 : ¬ Collinear3 u0 u1 u2) (h3 : ¬ Collinear3 u0 u1 u3)
    (h23 : u2 ≠ u3) (hπ : azim u0 u1 u2 u3 < Real.pi) :
    affGe ({u0, u1} : Set V3) ({u2, u3} : Set V3) ⊆ wedgeGe u0 u1 u2 u3 := by
  have h01 : u0 ≠ u1 := fun he => h2 (by rw [he]; exact collinear3_of_eq rfl)
  have hu2v0 : u2 ≠ u0 := fun he => h2 (collinear3_pair_left he)
  have hu2v1 : u2 ≠ u1 := fun he => h2 (collinear3_pair_right he)
  have hu3v0 : u3 ≠ u0 := fun he => h3 (collinear3_pair_left he)
  have hu3v1 : u3 ≠ u1 := fun he => h3 (collinear3_pair_right he)
  intro y hy
  obtain ⟨t1, t2, t3, t4, ht3, ht4, hsum4, hyeq⟩ :=
    (yk10_mem_affGe22_iff h01 hu2v0 hu3v0 hu2v1 hu3v1 h23 (y := y)).mp hy
  have ht1 : t1 = 1 - t2 - t3 - t4 := by linarith
  have hcombo : y - u0 = t2 • (u1 - u0) + t3 • (u2 - u0) + t4 • (u3 - u0) := by
    rw [hyeq, ht1]
    module
  by_cases hcoly : Collinear3 u0 u1 y
  · -- 轴上：azim 退化支 = 0
    refine ⟨azim_nonneg u0 u1 u2 y, ?_⟩
    show (if Collinear3 u0 u1 u2 ∨ Collinear3 u0 u1 y then (0 : ℝ)
      else Classical.epsilon (AzimSpec u0 u1 u2 y)) ≤ azim u0 u1 u2 u3
    rw [if_pos (Or.inr hcoly)]
    exact azim_nonneg u0 u1 u2 u3
  · have hncz : ¬ Collinear3 u0 u1 y := hcoly
    by_cases ht3z : t3 = 0
    · rw [ht3z] at hcombo ht3
      simp only [zero_smul, add_zero, zero_add] at hcombo
      by_cases ht4z : t4 = 0
      · -- t3 = t4 = 0：y 在 u0u1 线上，与 hcoly 矛盾
        rw [ht4z] at hcombo
        simp only [zero_smul, add_zero] at hcombo
        exact absurd ((collinear3_iff_smul h01.symm).mpr ⟨t2, hcombo⟩) hcoly
      · -- 仅 u3：azim y = azim u3 = C
        have ht4p : 0 < t4 := lt_of_le_of_ne ht4 (Ne.symm ht4z)
        refine ⟨azim_nonneg u0 u1 u2 y, ?_⟩
        have hymem : y ∈ affGt ({u0, u1} : Set V3) ({u3} : Set V3) :=
          (affGt_pair_iff h01 hu3v0 hu3v1).mpr ⟨t4, ht4p, t2,
            show y - u0 = t4 • (u3 - u0) + t2 • (u1 - u0) from by rw [hcombo]; module⟩
        rw [(azim_eq_azim_iff h2 h3 hncz).mpr hymem]
    · have ht3p : 0 < t3 := lt_of_le_of_ne ht3 (Ne.symm ht3z)
      by_cases ht4z : t4 = 0
      · -- 仅 u2：azim y = 0
        rw [ht4z] at hcombo ht4
        simp only [zero_smul, add_zero, zero_add] at hcombo
        refine ⟨azim_nonneg u0 u1 u2 y, ?_⟩
        have hymem : y ∈ affGt ({u0, u1} : Set V3) ({u2} : Set V3) :=
          (affGt_pair_iff h01 hu2v0 hu2v1).mpr ⟨t3, ht3p, t2,
            show y - u0 = t3 • (u2 - u0) + t2 • (u1 - u0) from by rw [hcombo]; module⟩
        have hzero : azim u0 u1 u2 y = 0 := by
          have h1 := (azim_eq_azim_iff h2 h2 hncz).mpr hymem
          rw [azim_self u0 u1 u2] at h1
          exact h1.symm
        rw [hzero]
        exact azim_nonneg u0 u1 u2 u3
      · -- 双严格：t3, t4 > 0
        have ht4p : 0 < t4 := lt_of_le_of_ne ht4 (Ne.symm ht4z)
        by_cases hz0 : azim u0 u1 u2 u3 = 0
        · -- u3 退到 u2 射线上：y 折进 u2 射线，azim y = 0
          have hu3in : u3 ∈ affGt ({u0, u1} : Set V3) ({u2} : Set V3) :=
            (azim_eq_zero_iff_alt h2 h3).mp hz0
          obtain ⟨c, hc, h, hcombo3⟩ :=
            (affGt_pair_iff h01 hu2v0 hu2v1).mp hu3in
          have hcombo' : y - u0 = t2 • (u1 - u0) + t3 • (u2 - u0)
              + t4 • (c • (u2 - u0) + h • (u1 - u0)) := by
            rw [hcombo, ← hcombo3]
          have hy2 : y - u0 = (t3 + t4 * c) • (u2 - u0)
              + (t2 + t4 * h) • (u1 - u0) := by
            rw [hcombo']
            module
          have hcpos : 0 < t3 + t4 * c := by nlinarith
          have hymem : y ∈ affGt ({u0, u1} : Set V3) ({u2} : Set V3) :=
            (affGt_pair_iff h01 hu2v0 hu2v1).mpr ⟨t3 + t4 * c, hcpos, t2 + t4 * h,
              hy2⟩
          have heq := (azim_eq_azim_iff h2 h2 hncz).mpr hymem
          refine ⟨azim_nonneg u0 u1 u2 y, ?_⟩
          have hzero : azim u0 u1 u2 y = 0 := by
            have h1 := heq
            rw [azim_self u0 u1 u2] at h1
            exact h1.symm
          rw [hzero]
          exact azim_nonneg u0 u1 u2 u3
        · -- 0 < azim u3 < π：wedge_eq_affGt 严格内侧
          have h0w2 : 0 < azim u0 u1 u2 u3 :=
            lt_of_le_of_ne (azim_nonneg u0 u1 u2 u3) (Ne.symm hz0)
          have hdisj22 : Disjoint ({u0, u1} : Set V3) ({u2, u3} : Set V3) := by
            rw [Set.disjoint_left]
            intro a ha
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
            rcases ha with rfl | rfl
            · intro hb
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
              rcases hb with rfl | rfl
              · exact hu2v0 rfl
              · exact hu3v0 rfl
            · intro hb
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
              rcases hb with rfl | rfl
              · exact hu2v1 rfl
              · exact hu3v1 rfl
          have hyGt : y ∈ affGt ({u0, u1} : Set V3) ({u2, u3} : Set V3) := by
            rw [affGt2_2 hdisj22]
            simp only [Set.mem_setOf_eq]
            exact ⟨t1, t2, t3, t4, ht3p, ht4p, hsum4, hyeq⟩
          have hwEq := wedge_eq_affGt h2 h3 h0w2 hπ
          rw [← hwEq] at hyGt
          simp only [Kepler.Geom.wedge, Set.mem_setOf_eq] at hyGt
          exact ⟨le_of_lt hyGt.2.1, le_of_lt hyGt.2.2⟩

/-- HOL CLOSED_WEDGE_LT_PI（leaf_cell.hl:3659）的闭包-包含折算：
closure(开 wedge) ⊆ wedge_ge。路线 = wedge ⊆ aff_ge 2+2（wedge_eq_affGt +
affGt⊆affGe）+ aff_ge 2+2 闭（yk10_isClosed_affGe22）+ aff_ge ⊆ wedge_ge
（yk10_affGe22_subset_wedgeGe）。 -/
private theorem yk10_closure_wedge_subset_wedgeGe (u0 u1 u2 u3 : V3)
    (h2 : ¬ Collinear3 u0 u1 u2) (h3 : ¬ Collinear3 u0 u1 u3)
    (h23 : u2 ≠ u3) (hπ : azim u0 u1 u2 u3 < Real.pi) :
    closure (Kepler.Geom.wedge u0 u1 u2 u3) ⊆ wedgeGe u0 u1 u2 u3 := by
  have h01 : u0 ≠ u1 := fun he => h2 (by rw [he]; exact collinear3_of_eq rfl)
  have hu2v0 : u2 ≠ u0 := fun he => h2 (collinear3_pair_left he)
  have hu2v1 : u2 ≠ u1 := fun he => h2 (collinear3_pair_right he)
  have hu3v0 : u3 ≠ u0 := fun he => h3 (collinear3_pair_left he)
  have hu3v1 : u3 ≠ u1 := fun he => h3 (collinear3_pair_right he)
  have hclosed : IsClosed (affGe ({u0, u1} : Set V3) ({u2, u3} : Set V3)) :=
    yk10_isClosed_affGe22 h01 hu2v0 hu3v0 hu2v1 hu3v1 h23
  have hsub1 : Kepler.Geom.wedge u0 u1 u2 u3
      ⊆ affGe ({u0, u1} : Set V3) ({u2, u3} : Set V3) := by
    intro y hy
    have hC0 : 0 < azim u0 u1 u2 u3 :=
      lt_of_le_of_lt (azim_nonneg u0 u1 u2 y) hy.2.2
    exact yk10_affGt_subset_affGe (wedge_eq_affGt h2 h3 hC0 hπ ▸ hy)
  have hsub2 : affGe ({u0, u1} : Set V3) ({u2, u3} : Set V3)
      ⊆ wedgeGe u0 u1 u2 u3 := yk10_affGe22_subset_wedgeGe h2 h3 h23 hπ
  intro z hz
  have hz2 : z ∈ closure (affGe ({u0, u1} : Set V3) ({u2, u3} : Set V3)) :=
    closure_mono hsub1 hz
  rw [hclosed.closure_eq] at hz2
  exact hsub2 hz2

/-! #### 9l.2 受限邻域基数下界（wedgeInFanGe 分支条件） -/

/-- `1 < ncard (ee e.1 (ePrime E f))`（yk6_azimInFan_ePrime_eq 证明内
hn'E 段的独立抽取：e.2 与全扇后继两个相异 e'-邻居；唯一几何输入 =
FullySurrounded 排 1 价分支）。 -/
private theorem yk10_one_lt_ee_ePrime {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hfs : FullySurrounded V E)
    {b : V3 × V3} (hb : b ∈ dart1OfFan V E) {f : Set (V3 × V3)}
    (hf : f = yk2_faceOrbit 0 V E hfan b) {e : V3 × V3} (he : e ∈ f) :
    1 < (ee e.1 (ePrime_p2 E f)).ncard := by
  have hd1 : e ∈ dart1OfFan V E :=
    yk2_faceOrbit_subset_dart1 hfan b hb (by rw [← hf]; exact he)
  have hco : (⇑(@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 V E hfan))) = fFanPairExt 0 V E :=
    funext fun z => yk2_apply_faceMap hfan z
  have hsymm_mem' : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 V E hfan)).symm e ∈ yk2_faceOrbit 0 V E hfan b :=
    yk2_faceOrbit_symm_closure hfan (by rw [← hf]; exact he)
  have hsymm_mem : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 V E hfan)).symm e ∈ f := by rw [hf]; exact hsymm_mem'
  have hinv : (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
      (hypermapOfFan 0 V E hfan)).symm e = Function.invFun (fFanPairExt 0 V E) e := by
    have h0 : (⇑(@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 V E hfan)))
        (Function.invFun (⇑(@Hypermap.faceMap (V3 × V3)
          (fun a b' => instDecidableEqProd a b') (hypermapOfFan 0 V E hfan))) e) = e :=
      Function.invFun_eq ⟨(@Hypermap.faceMap (V3 × V3)
        (fun a b' => instDecidableEqProd a b') (hypermapOfFan 0 V E hfan)).symm e,
        Equiv.apply_symm_apply _ _⟩
    have h1 := (Equiv.apply_eq_iff_eq_symm_apply
      (@Hypermap.faceMap (V3 × V3) (fun a b' => instDecidableEqProd a b')
        (hypermapOfFan 0 V E hfan))).mp h0
    rw [hco] at h1
    exact h1.symm
  rw [hinv, yk_invFunFFanPairExt_apply hfan e, if_pos hd1] at hsymm_mem
  rw [hinv, yk_invFunFFanPairExt_apply hfan e, if_pos hd1] at hsymm_mem'
  have hsig_dart : (sigmaFan 0 V E e.1 e.2, e.1) ∈ dart1OfFan V E :=
    yk2_faceOrbit_subset_dart1 hfan b hb hsymm_mem'
  have hsigE : ({sigmaFan 0 V E e.1 e.2, e.1} : Set V3) ∈ E := hsig_dart
  have hN'e : e.2 ∈ ee e.1 (ePrime_p2 E f) :=
    (yk6_in_ePrime f e.1 e.2).mpr ⟨hd1, Or.inl he⟩
  have hN'σ : sigmaFan 0 V E e.1 e.2 ∈ ee e.1 (ePrime_p2 E f) :=
    (yk6_in_ePrime f e.1 (sigmaFan 0 V E e.1 e.2)).mpr
      ⟨by rw [Set.pair_comm e.1 (sigmaFan 0 V E e.1 e.2)]; exact hsigE,
        Or.inr hsymm_mem⟩
  have hsigne : sigmaFan 0 V E e.1 e.2 ≠ e.2 := by
    by_cases hsoe1 : setOfEdge e.1 V E = {e.2}
    · exfalso
      exact absurd (yk6_fs_ncard_gt1 hfan hfs hd1) (by rw [hsoe1]; simp)
    · exact (SIGMA_FAN hsoe1 hfan
        (FAN_in_setOfEdge 0 V E e.1 e.2 hfan hd1).2.2.1).2.1
  have hfinN' : (ee e.1 (ePrime_p2 E f)).Finite := by
    have hfin0 : (setOfEdge e.1 V E).Finite := remark_finite_fan1 e.1 V E hfan.2.2.1.1
    have hsub : ee e.1 (ePrime_p2 E f) ⊆ setOfEdge e.1 V E := by
      intro z hz
      have hz2 : {e.1, z} ∈ E := yk6_ePrime_subset f hz
      exact ⟨hz2, FAN_EDGE_EL_V hfan hz2⟩
    exact hfin0.subset hsub
  have hpair2 : ({e.2, sigmaFan 0 V E e.1 e.2} : Set V3) ⊆ ee e.1 (ePrime_p2 E f) := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hN'e
    · rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hN'σ
  have hc1 : ({e.2, sigmaFan 0 V E e.1 e.2} : Set V3).ncard
      ≤ (ee e.1 (ePrime_p2 E f)).ncard := Set.ncard_le_ncard hpair2 hfinN'
  have hc2 : ({e.2, sigmaFan 0 V E e.1 e.2} : Set V3).ncard = 2 :=
    Set.ncard_pair hsigne.symm
  omega

/-! #### 9l.3 W1 wedge 主件（ConvexLocalFan 的 wedge 合取支） -/

/-- 面 f 的顶点集 vPrime 含于每条面 dart 的 wedge_in_fan_ge（e' 渲染）。
链：vPrime 元 z = 某 (z,w) ∈ f 的首端 ⟹ z ∈ closure(affGt {0} {z,w})
（POINT_IN_CLOSURE_AFF_GT_1_2）⟹ affGt ⊆ closure(dartsetLeadsIntoFan f)
（锚3）⟹ dartsetLeadsInto ⊆ w_dart_fan（锚2，conformingHalfSpace 支）
⟹ w_dart = 开 wedge（FullySurrounded 给 CARD>1）⟹ closure ⊆ wedge_ge
（9l.1 闭扇）⟹ σ 换回受限 σ（yk6 azim 桥）。 -/
private theorem yk10_vPrime_subset_wedgeInFanGe (V : Set V3) (hlpfan : LpFan V (ESTD V))
    {b : V3 × V3} (hb : b ∈ dart1OfFan V (ESTD V)) {f : Set (V3 × V3)}
    (hf : f = yk2_faceOrbit 0 V (ESTD V) hlpfan.1 b) {x : V3 × V3} (hx : x ∈ f) :
    vPrime_p2 V f ⊆ wedgeInFanGe x (ePrime_p2 (ESTD V) f) := by
  have hfan : FAN 0 V (ESTD V) := hlpfan.1
  have hfs : FullySurrounded V (ESTD V) := hlpfan.2.1
  have hconf := p6g_fullySurrounded_conforming V (ESTD V) hfan hfs
  have hcard : ∀ v ∈ V, 1 < (setOfEdge v V (ESTD V)).ncard := hconf.1
  have hfan80 : fan80 0 V (ESTD V) := hconf.2.1
  have hx1 : x ∈ dart1OfFan V (ESTD V) :=
    yk2_faceOrbit_subset_dart1 hfan b hb (by rw [← hf]; exact hx)
  have hbr : 1 < (ee x.1 (ePrime_p2 (ESTD V) f)).ncard :=
    yk10_one_lt_ee_ePrime hfan hfs hb hf hx
  have hfullE : 1 < (ee x.1 (ESTD V)).ncard := by
    rw [wk_ee_eq_setOfEdge hfan x.1]
    exact yk6_fs_ncard_gt1 hfan hfs hx1
  have hncard1 : 1 < (setOfEdge x.1 V (ESTD V)).ncard := yk6_fs_ncard_gt1 hfan hfs hx1
  have hπ : azim 0 x.1 x.2 (sigmaFan 0 V (ESTD V) x.1 x.2) < Real.pi := by
    have h1 : azimDart V (ESTD V) x < Real.pi := hfs x (Set.mem_union_right _ hx1)
    have h2 : azimDart V (ESTD V) x = azim 0 x.1 x.2 (sigmaFan 0 V (ESTD V) x.1 x.2) := by
      show (if x.1 = x.2 then (2 : ℝ) * Real.pi
        else if (setOfEdge x.1 V (ESTD V)).ncard > 1
          then azim 0 x.1 x.2 (sigmaFan 0 V (ESTD V) x.1 x.2) else 2 * Real.pi) = _
      rw [if_neg (edge_ne_of_fan hfan hx1), if_pos hncard1]
    rw [← h2]; exact h1
  have hvwE : ({x.1, x.2} : Set V3) ∈ ESTD V := hx1
  have hnc2 : ¬ Collinear3 0 x.1 x.2 := fan_not_collinear hfan hvwE
  have hσmem : sigmaFan 0 V (ESTD V) x.1 x.2 ∈ setOfEdge x.1 V (ESTD V) :=
    sigma_fan_in_setOfEdge hfan
      ((properties_of_setOfEdge_fan 0 V (ESTD V) x.1 x.2 hfan).mp hx1)
  have hσE : ({x.1, sigmaFan 0 V (ESTD V) x.1 x.2} : Set V3) ∈ ESTD V :=
    (properties_of_setOfEdge_fan 0 V (ESTD V) x.1
      (sigmaFan 0 V (ESTD V) x.1 x.2) hfan).mpr hσmem
  have hncσ : ¬ Collinear3 0 x.1 (sigmaFan 0 V (ESTD V) x.1 x.2) :=
    fan_not_collinear hfan hσE
  have hσb : sigmaFan 0 V (ESTD V) x.1 x.2 ≠ x.2 := by
    by_cases hsoe1 : setOfEdge x.1 V (ESTD V) = {x.2}
    · exact absurd hsoe1 (fun hc => absurd hncard1 (by rw [hc]; simp))
    · exact (SIGMA_FAN hsoe1 hfan
        (FAN_in_setOfEdge 0 V (ESTD V) x.1 x.2 hfan hx1).2.2.1).2.1
  -- σ 值桥：受限 σ 的方位角值 = 全扇 σ
  have hσeq : azim 0 x.1 x.2 (sigmaFan 0 Set.univ (ePrime_p2 (ESTD V) f) x.1 x.2)
      = azim 0 x.1 x.2 (sigmaFan 0 V (ESTD V) x.1 x.2) := by
    have h := yk6_azimInFan_ePrime_eq hfan hfs b hb f hf hx
    unfold azimInFan at h
    rw [if_pos hbr, if_pos hfullE, wk_sigmaFan_congr hfan] at h
    exact h
  have hσ'trans : wedgeGe 0 x.1 x.2 (sigmaFan 0 Set.univ (ePrime_p2 (ESTD V) f) x.1 x.2)
      = wedgeGe 0 x.1 x.2 (sigmaFan 0 V (ESTD V) x.1 x.2) := by
    unfold wedgeGe
    rw [hσeq]
  intro z hz
  unfold wedgeInFanGe
  rw [if_pos hbr, hσ'trans]
  obtain ⟨w, hwf⟩ := hz.2
  have hzw : (z, w) ∈ dart1OfFan V (ESTD V) :=
    yk2_faceOrbit_subset_dart1 hfan b hb (by rw [← hf]; exact hwf)
  have hne : z ≠ w := edge_ne_of_fan hfan hzw
  have h0V : (0 : V3) ∉ V := hfan.2.2.2.1
  have hz0 : (0 : V3) ≠ z := fun he => h0V (he ▸ hz.1)
  have hw0 : (0 : V3) ≠ w := fun he => h0V (he ▸ (yk2_dart_fst_snd_mem_V hfan hzw).2)
  have hface : ((hypermapOfFanTl V (ESTD V) hfan).face b) = f := by
    rw [hf]; rfl
  have hfs_face : f ∈ (hypermapOfFanTl V (ESTD V) hfan).faceSet := by
    rw [← hface]
    exact wk_face_mem_faceSet (mem_dartsTl hb)
  have hfsTl : (hypermapOfFanTl V (ESTD V) hfan).faceSet =
      @Hypermap.faceSet (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan 0 V (ESTD V) hfan) := by
    unfold Hypermap.faceSet
    rw [dartsTl_eq, faceMapTl_eq]
  -- z ∈ closure(affGt {0} {z,w})
  have hpc : z ∈ closure (affGt ({0} : Set V3) ({z, w} : Set V3)) :=
    POINT_IN_CLOSURE_AFF_GT_1_2 0 z w hz0 hw0 hne
  -- 锚3
  have hA3 : affGt ({0} : Set V3) ({z, w} : Set V3)
      ⊆ closure (dartsetLeadsIntoFan 0 V (ESTD V) f) :=
    AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN_tl V (ESTD V) f (z, w) hfan hcard
      hfan80 (hfsTl ▸ hfs_face) hwf
  -- 锚2
  have hA2 : dartsetLeadsIntoFan 0 V (ESTD V) f
      ⊆ wDartFan 0 V (ESTD V) (0, x.1, x.2, sigmaFan 0 V (ESTD V) x.1 x.2) :=
    DARTSET_LEADS_INTO_SUBSET_WDART_FAN hfan (hfsTl ▸ hfs_face) hx hconf
  -- w_dart = 开 wedge（CARD > 1 支）
  have hwd : wDartFan 0 V (ESTD V) (0, x.1, x.2, sigmaFan 0 V (ESTD V) x.1 x.2)
      = Kepler.Geom.wedge 0 x.1 x.2 (sigmaFan 0 V (ESTD V) x.1 x.2) := by
    simp only [wDartFan, if_pos hncard1]
  -- 闭扇收口
  have hchain : dartsetLeadsIntoFan 0 V (ESTD V) f
      ⊆ Kepler.Geom.wedge 0 x.1 x.2 (sigmaFan 0 V (ESTD V) x.1 x.2) := by
    intro y hy
    rw [← hwd]
    exact hA2 hy
  have hwedge_sub : affGt ({0} : Set V3) ({z, w} : Set V3)
      ⊆ closure (Kepler.Geom.wedge 0 x.1 x.2 (sigmaFan 0 V (ESTD V) x.1 x.2)) :=
    fun u hu => closure_mono hchain (hA3 hu)
  have hz3 : z ∈ closure (Kepler.Geom.wedge 0 x.1 x.2
      (sigmaFan 0 V (ESTD V) x.1 x.2)) := by
    have h1 : z ∈ closure (closure (Kepler.Geom.wedge 0 x.1 x.2
        (sigmaFan 0 V (ESTD V) x.1 x.2))) := closure_mono hwedge_sub hpc
    rwa [closure_closure] at h1
  exact yk10_closure_wedge_subset_wedgeGe 0 x.1 x.2
    (sigmaFan 0 V (ESTD V) x.1 x.2) hnc2 hncσ
    (fun he => hσb he.symm) hπ hz3

/-! #### 9l.4 Dih2k 实例转移 + ConvexLocalFan 装配 -/

/-- **ConvexLocalFan (vPrime, ePrime, f) 装配**（JEJTVGB_std_concl 前提①）。
LocalFan 面 = §9k 三件（yk9_Dih2k / yk7_FF_eq_faceOrbit / yk2_FAN_vPrime_ePrime）；
azim≤π 面 = yk6 桥 + FullySurrounded；wedge 面 = 9l.3 主件。 -/
private theorem yk10_convexLocalFan (V : Set V3) (hlpfan : LpFan V (ESTD V))
    {b : V3 × V3} (hb : b ∈ dart1OfFan V (ESTD V)) {f : Set (V3 × V3)}
    (hf : f = yk2_faceOrbit 0 V (ESTD V) hlpfan.1 b) (hk : 2 < f.ncard) :
    ConvexLocalFan (vPrime_p2 V f) (ePrime_p2 (ESTD V) f) f := by
  have hfan : FAN 0 V (ESTD V) := hlpfan.1
  have hfs : FullySurrounded V (ESTD V) := hlpfan.2.1
  have hconf := p6g_fullySurrounded_conforming V (ESTD V) hfan hfs
  have hV : V.Finite := yk10_packingFinite hlpfan.2.2.2.2 hlpfan.2.2.2.1
  have hfan' : FAN 0 (vPrime_p2 V f) (ePrime_p2 (ESTD V) f) :=
    yk2_FAN_vPrime_ePrime hfan b hb f hf
  refine ⟨⟨hfan', b, ?_, ?_, ?_⟩, ?_⟩
  · -- b ∈ 受限 darts
    exact Finset.mem_coe.mpr
      ((yk2_mem_darts_iff hfan' b).mpr (yk9_base_ctx hfan b hb f hf hfan').1)
  · -- f = orbitMap faceMap' b
    exact (yk7_FF_eq_faceOrbit hfan b hb f hf).symm
  · -- Dih2k（LocalFan 体的 Dih2k 实例即 hypermapOfFan 烤定 instProd 味，
    -- 与 yk9_Dih2k 结论同实例，直接衔接）
    exact yk9_Dih2k hfan hconf hV b hb f hf hk hfan'
  · intro y hy
    refine ⟨?_, yk10_vPrime_subset_wedgeInFanGe V hlpfan hb hf hy⟩
    have hy1 : y ∈ dart1OfFan V (ESTD V) :=
      yk2_faceOrbit_subset_dart1 hfan b hb (by rw [← hf]; exact hy)
    rw [yk6_azimInFan_ePrime_eq hfan hfs b hb f hf hy,
      wk_azimInFan_eq_azimDart hfan hy1]
    exact le_of_lt (hfs y (Set.mem_union_right _ hy1))

/-! #### 9l.5 chord 件（JEJTVGB_std_concl 前提⑥ = HOL local_diag:581） -/

/-- 非边前提：vPrime 内不构成面边的点对，距离 ≥ 2h0。{a,b} ∉ E 支 =
LpFan.3；chord 支 = conforming_diagonal 合取支（GGZWYRM 上游）——
= HOL `diag_not_in_dart`（lp_main_estimate:415）的 pair-dart 重装。 -/
private theorem yk10_diag (V : Set V3) (hlpfan : LpFan V (ESTD V))
    {b : V3 × V3} (hb : b ∈ dart1OfFan V (ESTD V)) {f : Set (V3 × V3)}
    (hf : f = yk2_faceOrbit 0 V (ESTD V) hlpfan.1 b)
    {a c : V3} (ha : a ∈ vPrime_p2 V f) (hc : c ∈ vPrime_p2 V f) (hac : a ≠ c)
    (hne' : {a, c} ∉ ePrime_p2 (ESTD V) f) :
    2 * h0 ≤ dist a c := by
  by_cases hE : {a, c} ∈ ESTD V
  · exfalso
    have hfan : FAN 0 V (ESTD V) := hlpfan.1
    have hfs : FullySurrounded V (ESTD V) := hlpfan.2.1
    have hconf := p6g_fullySurrounded_conforming V (ESTD V) hfan hfs
    have hcard : ∀ v ∈ V, 1 < (setOfEdge v V (ESTD V)).ncard := hconf.1
    have hfan80 : fan80 0 V (ESTD V) := hconf.2.1
    obtain ⟨-, a', haa'⟩ := Set.mem_setOf_eq.mp ha
    obtain ⟨-, c', hcc'⟩ := Set.mem_setOf_eq.mp hc
    have hfsTl : (hypermapOfFanTl V (ESTD V) hfan).faceSet =
        @Hypermap.faceSet (V3 × V3) (fun a b => instDecidableEqProd a b)
          (hypermapOfFan 0 V (ESTD V) hfan) := by
      unfold Hypermap.faceSet
      rw [dartsTl_eq, faceMapTl_eq]
    have hface : ((hypermapOfFanTl V (ESTD V) hfan).face b) = f := by
      rw [hf]; rfl
    have hfs_face : f ∈ @Hypermap.faceSet (V3 × V3)
        (fun a b => instDecidableEqProd a b) (hypermapOfFan 0 V (ESTD V) hfan) := by
      rw [← hface]
      exact wk_face_mem_faceSet (mem_dartsTl hb)
    have hne : (a, a') ≠ (c, c') := by
      intro he
      exact hac (congrArg Prod.fst he)
    obtain ⟨hncol, h3way⟩ :=
      hconf.2.2.2.2.2 f hfs_face (a, a') haa' (c, c') hcc' hne
    rcases h3way with h1 | h1 | h1
    · -- (a,a') = f1Fan (c,c') = (c', …) ⟹ a = c' ⟹ (c,a) = (c,c') ∈ f
      have ha2 : a = c' := by
        have h5 := congrArg Prod.fst h1
        simpa [f1Fan] using h5
      exact hne' ((yk6_in_ePrime f a c).mpr ⟨hE, Or.inr (by rw [ha2]; exact hcc')⟩)
    · -- (c,c') = f1Fan (a,a') = (a', …) ⟹ c = a' ⟹ (a,c) = (a,a') ∈ f
      have hc2 : c = a' := by
        have h5 := congrArg Prod.fst h1
        simpa [f1Fan] using h5
      exact hne' ((yk6_in_ePrime f a c).mpr ⟨hE, Or.inl (by rw [hc2]; exact haa')⟩)
    · -- affGt {0} {a,c} ⊆ dartsetLeadsIntoFan f：与 (a,c) ∈ dart1 的 xfan-包含夹逼
      have h0V : (0 : V3) ∉ V := hfan.2.2.2.1
      have haV : a ∈ V := ha.1
      have hcV : c ∈ V := hc.1
      have hz0 : (0 : V3) ≠ a := fun he => h0V (he ▸ haV)
      have hzc : (0 : V3) ≠ c := fun he => h0V (he ▸ hcV)
      have hdis : Disjoint ({0} : Set V3) ({a, c} : Set V3) := by
        rw [Set.disjoint_left]
        intro u hu1 hu2
        rw [Set.mem_singleton_iff] at hu1
        subst hu1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu2
        rcases hu2 with h | h
        · exact hz0 h
        · exact hzc h
      -- 中点 ∈ affGt
      have hmid : ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • c)
          ∈ affGt ({0} : Set V3) ({a, c} : Set V3) := by
        rw [aff_gt_1_2 hdis]
        refine ⟨0, 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
        module
      -- affGt ⊆ affGe ⊆ xfan
      have hge : affGt ({0} : Set V3) ({a, c} : Set V3)
          ⊆ affGe ({0} : Set V3) ({a, c} : Set V3) := yk10_affGt_subset_affGe
      have hxfan : affGe ({0} : Set V3) ({a, c} : Set V3) ⊆ xfan 0 V (ESTD V) :=
        AFF_GE_SUBSET_XFAN 0 V (ESTD V) a c hE
      -- dartsetLeadsInto ⊆ yfan
      have hyfan : dartsetLeadsIntoFan 0 V (ESTD V) f ⊆ yfan 0 V (ESTD V) :=
        dartset_leads_into_subset_yfan hfan hcard hfan80 hfs_face
      have hmid2 : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • c
          ∈ dartsetLeadsIntoFan 0 V (ESTD V) f := h1 hmid
      have hmid3 : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • c ∈ yfan 0 V (ESTD V) :=
        hyfan hmid2
      have hmid4 : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • c ∈ xfan 0 V (ESTD V) :=
        hxfan (hge hmid)
      unfold yfan at hmid3
      exact hmid3.2 hmid4
  · -- {a,c} ∉ E：LpFan.3
    exact yk6_local_diag_notE hlpfan f ha hc hac hE

/-! #### 9l.6 tauK 共享装配 + 三枚 e2e -/

/-- tau4/5/6 共享装配：dTame k ≤ tauVEF（面 d）。 -/
private theorem yk10_tauK_aux (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std_concl) {k : ℕ} (hk4 : 4 ≤ k) (hk6 : k ≤ 6)
    {d : V3 × V3} (hd1 : d ∈ dart1OfFan V (ESTD V))
    (hcard : ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d).ncard = k) :
    dTame k ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
  have hfan : FAN 0 V (ESTD V) := hlpfan.1
  have hfs : FullySurrounded V (ESTD V) := hlpfan.2.1
  have hsub : V ⊆ ballAnnulus := hlpfan.2.2.2.1
  have hpack : Packing V := hlpfan.2.2.2.2
  have hconf := p6g_fullySurrounded_conforming V (ESTD V) hfan hfs
  have hV : V.Finite := yk10_packingFinite hpack hsub
  have hfo : (hypermapOfFanTl V (ESTD V) hfan).face d
      = yk2_faceOrbit 0 V (ESTD V) hfan d := rfl
  set f := (hypermapOfFanTl V (ESTD V) hfan).face d with hfd
  have hk2 : 2 < f.ncard := by rw [hcard]; omega
  have hk4' : 4 ≤ f.ncard := by rw [hcard]; exact hk4
  have hcl := yk10_convexLocalFan V hlpfan hd1 hfo hk2
  have h4le : 4 ≤ (vPrime_p2 V f).ncard :=
    yk8_four_le_ncard_vPrime hfan hconf hV d hd1 f hfo hk4'
  have h6le : (vPrime_p2 V f).ncard ≤ 6 := by
    have hle := yk6_ncard_vPrime_le hfan d hd1 f hfo
    rw [hcard] at hle
    exact le_trans hle hk6
  have hdiag : ∀ v w : V3, v ≠ w → v ∈ vPrime_p2 V f → w ∈ vPrime_p2 V f →
      {v, w} ∉ ePrime_p2 (ESTD V) f → 2 * h0 ≤ dist v w :=
    fun v w hvw hv hw hne => yk10_diag V hlpfan hd1 hfo hv hw hvw hne
  have hstd : ∀ v w : V3, {v, w} ∈ ePrime_p2 (ESTD V) f →
      2 ≤ dist v w ∧ dist v w ≤ 2 * h0 := fun v w hw => yk6_local_std hfan hpack f hw
  have hkey := hineq (vPrime_p2 V f) (ePrime_p2 (ESTD V) f) f hcl
    (yk6_packing_vPrime f hpack) (yk6_vPrime_sub_ballAnnulus f hsub) h4le h6le
    hdiag hstd
  rw [yk8_ncard_vPrime_eq hfan hconf hV d hd1 f hfo, hcard] at hkey
  rw [yk6_tauVEF_eq_tauFun_ePrime hlpfan d hd1 f hfo]
  exact hkey


/-! ### 9l.6b —— 三枚 ineq_tauK_tauVEF_std（原 :2075-2138）（原行位搬迁至此，陈述逐字节未改，占位行已收口删除） -/
/-- HOL `ineq_tau4_tauVEF_std`（`lp_main_estimate-compiled.hl:796-817`）。
真证明 2026-10-23（Lane AT，§9l）：JEJTVGB_std_concl 在 (vPrime, ePrime, f)
上的实例（ConvexLocalFan = §9l.4 装配；ncard 界 = §9j/§9i 件；非边前提 =
§9l.5 chord 件；边前提 = yk6_local_std），经 yk6_tauVEF_eq_tauFun_ePrime 回写。 -/
theorem ineq_tau4_tauVEF_std (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std_concl) (d : V3 × V3)
    (hd : d ∈ dartsK 4 (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    0.206 ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
  obtain ⟨hdarts, hcard⟩ := hd
  rw [← wk_dtame4]
  exact yk10_tauK_aux V hlpfan hineq (le_refl 4) (by omega) (dartsTl_mem hdarts) hcard

/-- HOL `ineq_tau5_tauVEF_std`（`lp_main_estimate-compiled.hl:889-915`）。
真证明 2026-10-23（Lane AT，§9l）：同 tau4 装配（K=5 差分仅在 dTame 5 =
0.4819 的数值件与 ncard f = 5）。 -/
theorem ineq_tau5_tauVEF_std (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std_concl) (d : V3 × V3)
    (hd : d ∈ dartsK 5 (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    0.4819 ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
  obtain ⟨hdarts, hcard⟩ := hd
  rw [← wk_dtame5]
  exact yk10_tauK_aux V hlpfan hineq (by omega) (by omega) (dartsTl_mem hdarts) hcard

/-- HOL `ineq_tau6_tauVEF_std`（`lp_main_estimate-compiled.hl:988-1015`）。
真证明 2026-10-23（Lane AT，§9l）：同 tau4 装配（K=6 差分仅在 dTame 6 =
0.712 的数值件与 ncard f = 6）。 -/
theorem ineq_tau6_tauVEF_std (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std_concl) (d : V3 × V3)
    (hd : d ∈ dartsK 6 (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    0.712 ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
  obtain ⟨hdarts, hcard⟩ := hd
  rw [← wk_dtame6]
  exact yk10_tauK_aux V hlpfan hineq (by omega) (le_refl 6) (dartsTl_mem hdarts) hcard


/-! ### 9l.6c —— MQMSMAB_adm1（原 :6336-6368，消费上方三枚 tau）（原行位搬迁至此，陈述逐字节未改，占位行已收口删除） -/
/-- MQMSMAB 步 21-41（adm_1）：`w f = tauVEF` 时 adm_1 成立——tame_9a 给
`3 ≤ card(face d) ≤ 6`，枚举 {3,4,5,6} 各引 `ineq_tauK_tauVEF_std`
（JEJTVGB 前提由 `hmain.2.1`/`hmain.1` 分量直接供给，= HOL :60-64 的
h_main 重写步）。 -/
theorem MQMSMAB_adm1 (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hmain : lp_main_estimate)
    (h9a : Tame9a (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    Adm1 (hypermapOfFanTl V (ESTD V) hlpfan.1) (fun f => tauVEF_p2 V (ESTD V) f) := by
  intro d hd
  obtain ⟨h3, h6⟩ := h9a d hd
  by_cases hn3 : ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d).ncard = 3
  · rw [hn3]
    show (0 : ℝ) ≤ tauVEF_p2 V (ESTD V)
      ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d)
    exact ineq_tau3_tauVEF_std V hlpfan hmain.2.1 d (Set.mem_setOf_eq.mpr ⟨hd, hn3⟩)
  by_cases hn4 : ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d).ncard = 4
  · rw [hn4]
    show (0.206 : ℝ) ≤ tauVEF_p2 V (ESTD V)
      ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d)
    exact ineq_tau4_tauVEF_std V hlpfan hmain.1 d (Set.mem_setOf_eq.mpr ⟨hd, hn4⟩)
  by_cases hn5 : ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d).ncard = 5
  · rw [hn5]
    show (0.4819 : ℝ) ≤ tauVEF_p2 V (ESTD V)
      ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d)
    exact ineq_tau5_tauVEF_std V hlpfan hmain.1 d (Set.mem_setOf_eq.mpr ⟨hd, hn5⟩)
  by_cases hn6 : ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d).ncard = 6
  · rw [hn6]
    show (0.712 : ℝ) ≤ tauVEF_p2 V (ESTD V)
      ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d)
    exact ineq_tau6_tauVEF_std V hlpfan hmain.1 d (Set.mem_setOf_eq.mpr ⟨hd, hn6⟩)
  · have hb := h3
    have hb2 := h6
    omega


/-! ### 9l.6d —— MQMSMAB_tame13a + MQMSMAB（原 :6403-6436，消费 adm1）（原行位搬迁至此，陈述逐字节未改，占位行已收口删除） -/
/-- MQMSMAB 步 15-20（tame_13a）：见证 `w f = tauVEF`，adm_1/2/3 三分量
+ `sum_tauVEF_upper_bound`（≤ 4π−20sol0）+ Flyspeck 常数算术收
`total_weight < tgt`（步 18-19：12 ≤ scriptL V 由 contravening 第三合取项）。 -/
theorem MQMSMAB_tame13a (V : Set V3) (hc : Contravening V) (hlpfan : LpFan V (ESTD V))
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef)
    (h9a : Tame9a (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    Tame13a (hypermapOfFanTl V (ESTD V) hlpfan.1) := by
  refine ⟨fun f => tauVEF_p2 V (ESTD V) f, ⟨MQMSMAB_adm1 V hlpfan hmain h9a,
    MQMSMAB_adm2 V hc hlpfan hmain hineq, MQMSMAB_adm3 V hc hlpfan hmain hineq⟩, ?_⟩
  have hscript : (12 : ℝ) ≤ scriptL V := le_of_lt hc.2.2.1
  have hsum := sum_tauVEF_upper_bound V (ESTD V) hlpfan.1 hlpfan.2.1 hscript
  show setSum (hypermapOfFanTl V (ESTD V) hlpfan.1).faceSet
      (fun f => tauVEF_p2 V (ESTD V) f) < tgt
  exact lt_of_le_of_lt hsum four_pi_sub_20_sol0_lt_tgt

/-- HOL `Mqmsmab.MQMSMAB`（MQMSMAB-compiled.hl:30-80）本章帽石（`hypermapOfFanTl`
折算版）：`contravening V` + `FAN 0 V (ESTD V)` + `lp_main_estimate` +
`kcblrqc_ineq_def` 消费切片 ⟹ `tame_planar_hypermap`。十二合取逐项：tame_1 ←
JGTDEBU2（plain）+JGTDEBU1（planar）；tame_2 ← JGTDEBU3+JGTDEBU4；tame_3/4/5a/8 ←
JGTDEBU5/6/7/8；tame_9a ← **CRTTXAT**（消费点，HOL 步 5：
`CRTTXAT (JGTDEBU4 contrV) (fully_surrounded_perimeter_bound fanV f_surr)`）；
tame_10/11a ← JGTDEBU10/11；tame_11b/12o ← SZIPOAS/BDJYFFB1；tame_13a ←
`MQMSMAB_tame13a`。Assembly 侧 `mqmsmab` 消费时经 §0b congr 家族换实例。 -/
theorem MQMSMAB (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V))
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef) :
    TamePlanarHypermap (hypermapOfFanTl V (ESTD V) hfan) := by
  have hlpfan : LpFan V (ESTD V) := contravening_lp_fan V hc
  have h9a := CRTTXAT (fun V' hfan' hc' => JGTDEBU4 V' hc' hfan') V hc hfan
    (fully_surrounded_perimeter_bound V (ESTD V) hlpfan.1 hlpfan.2.1)
  exact ⟨⟨JGTDEBU2 V hc hfan, JGTDEBU1 V hc hfan⟩,
    ⟨JGTDEBU3 V hc hfan, JGTDEBU4 V hc hfan⟩, JGTDEBU5 V hc hfan, JGTDEBU6 V hc hfan,
    JGTDEBU7 V hc hfan, JGTDEBU8 V hc hfan, h9a, JGTDEBU10 V hc hfan,
    JGTDEBU11 V hc hfan, SZIPOAS hineq V hc hfan, BDJYFFB1 V hc hmain hineq hfan,
    MQMSMAB_tame13a V hc hlpfan hmain hineq h9a⟩


/-! ### 9m. ykit11 波（Lane AW 2026-10-23）：perimeter 精确降债波——
`fully_surrounded_perimeter_bound` 的 WSEWPCH 核收敛桥落地（纯追加，
yk11_* 前缀）。

HOL 五步装配（`lp_main_estimate-compiled.hl` §PerimeterBound :1473-1543）
在树内的对应物盘点与本波结论：
  步 1（face 表示 f = face d）= `Hypermap.face_representation`
    （hypermap.hl:2737 同名折算，树内真证）；
  步 2/3（face 和到顶点轨道和的重表达：local_fan 版 lemma_face_representation +
    sum_face_rho_node1 + `Polar_fan.FAN_PERIMETER`）= 本波**免除**：
    §9l.4 `yk10_convexLocalFan` 已对每个 face 给出
    `ConvexLocalFan (vPrime_p2, ePrime_p2, f)`，而周长和
    `setSum f (fun d => arcV 0 d.1 d.2)` 本身就是 WSEWPCH 的内容对象，
    `fanPerimeter`/rho_node1 轨道重表达可整体绕过——三桥自此不在依赖图上；
  步 4/5 = WSEWPCH 核 + f_surr_localization_convex_local（后者已被
    `yk10_convexLocalFan` 覆盖）。唯一残余锚 = **WSEWPCH 核**。

WSEWPCH 核（polar_fan.hl:2213）的依赖树现状（CIZMRRH 三分 + CARD V 良基
归纳三分支）：
  - circular 分支：KCHMAMG（local_lemmas.hl:3197）⟹ 全顶点共面于过 0 平面 +
    azim_cycle = rho_node1 + 逐点 azim = arcV，求和 = 2π 走
    ORDER_AZIM_SUM2Pi0——**求和引擎已在树内真证**（PackingAuto25:8921
    `ORDER_AZIM_SUM2Pi0`；PackingAuto22:7562 `ORDER_AZIM_SUM2Pi` 同）；
    但 KCHMAMG 本身（LocalAuto5:5018 同名件为桩且 LA5 不可 import——
    与 PackingAuto18 的 AFF_GE_MONO_TRANS 重名）与 CYCLIC_SET 词表桥未移植；
  - lunar 分支：共线对劈半，周长和 = 两片平面扇 azim 望远镜和 ≤ π + π
    （COLLINEAR_AZIM_0_OR_PI 收口）；依赖 HKIRPEP / CARD_IS_LEAST_CYCLE /
    RHO_NODE1_MONO_WITH_AZIM（local_lemmas 章未移植）+ ITER 轨道 kit
    （LocalAuto7:424-476 桩组）；
  - generic 分支：内角全 < π 时走极扇 BGMIFTE（LocalAuto7:642 桩）+
    polar_fan 构造（树内无定义）；存在平角（interior_angle1 = π）顶点时
    直 dart 分裂成两小扇用归纳；依赖 GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE 等
    LocalAuto7 桩组；
  - 三分前提 CIZMRRH（WRGCVDR.hl:3056；LocalAuto3:1881 同名件为桩）。
  即残余锚 = 极扇/局部扇深章整章（LocalAuto7 头注 DISCHARGES 契约本体），
  非单波机械件，需专职 lane 多波推进。

本波落地 `yk11_perimeterBound_of_core`：把 `PerimeterBound` 收敛为**单锚**
hcore（WSEWPCH 核的 Lean 渲染，face-和形，与 fanPerimeter 表达解耦）。
原位 `fully_surrounded_perimeter_bound` 及其 NEEDS 注记按纪律未动；下一波
真证 hcore 后，以 `exact yk11_perimeterBound_of_core V hlpfan
yk11_WSEWPCH_core` 一类单行装配即可闭合（建议新核心件命名
yk11_WSEWPCH_core，陈述逐字同 hcore）。 -/

/-- **PerimeterBound ⟸ WSEWPCH 核**（ykit11 装配桥）。hcore 即 HOL
`WSEWPCH`（polar_fan.hl:2213，`convex_local_fan ⟹ fan_perimeter ≤ 2π`）的
Lean 渲染：Content 对象直接取面-和 `setSum g (fun d => arcV 0 d.1 d.2)`
（对 LocalFan 面，此和与 fanPerimeter 经 FAN_PERIMETER 轨道重表达相等，
本桥无需该方向）。装配 = HOL 五步的树内对应：face 表示 =
`Hypermap.face_representation`；face ≥ 3 元 = `CARD_FACE_GE_3_TL` +
`SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL`（FullySurrounded 逐 dart 供给）；
ConvexLocalFan 面 = §9l.4 `yk10_convexLocalFan`；末端 = hcore 在
`(vPrime_p2 V g, ePrime_p2 (ESTD V) g, g)` 上的实例。 -/
private theorem yk11_perimeterBound_of_core (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hcore : ∀ (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3)),
      ConvexLocalFan U E' g → setSum g (fun d => arcV (0 : V3) d.1 d.2) ≤ 2 * Real.pi) :
    PerimeterBound V (ESTD V) hlpfan.1 := by
  have hfan : FAN 0 V (ESTD V) := hlpfan.1
  have hsurr : FullySurrounded V (ESTD V) := hlpfan.2.1
  intro f hfset
  obtain ⟨d, hd, rfl⟩ := Hypermap.face_representation _ hfset
  have hd1 : d ∈ dart1OfFan V (ESTD V) := dartsTl_mem hd
  have hcard : ∀ v ∈ V, 3 ≤ (setOfEdge v V (ESTD V)).ncard := fun v hv =>
    SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL hfan hv (fun e he _ => hsurr e he)
  have h3 : 3 ≤ ((hypermapOfFanTl V (ESTD V) hfan).face d).ncard :=
    CARD_FACE_GE_3_TL hfan hd1 hcard
  have hfo : ((hypermapOfFanTl V (ESTD V) hfan).face d)
      = yk2_faceOrbit 0 V (ESTD V) hfan d := rfl
  have hcl := yk10_convexLocalFan V hlpfan hd1 hfo (by omega)
  exact hcore _ _ _ hcl

end Kepler.Text.TameLp
