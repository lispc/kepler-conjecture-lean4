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

/-- HOL `ineq_tau4_tauVEF_std`（`lp_main_estimate-compiled.hl:796-817`）。
DISCHARGES：骨架占位（同上群）。 -/
theorem ineq_tau4_tauVEF_std (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std_concl) (d : V3 × V3)
    (hd : d ∈ dartsK 4 (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    0.206 ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
  -- NEEDS（Lane G 侦察 2026-10-23）：同 tau3 卡 y-kit 章 + Face4 节
  -- `f_surr_tau_fun_eq_tauVEF`/`tau_fun_local`/`f_surr_localization_convex_local`
  -- （Local_lemmas 未移植）。
  sorry

/-- HOL `ineq_tau5_tauVEF_std`（`lp_main_estimate-compiled.hl:889-915`）。
DISCHARGES：骨架占位（同上群）。 -/
theorem ineq_tau5_tauVEF_std (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std_concl) (d : V3 × V3)
    (hd : d ∈ dartsK 5 (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    0.4819 ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
  -- NEEDS（Lane G 侦察 2026-10-23）：同 tau4，卡 y-kit 章 + Face5 节桥。
  sorry

/-- HOL `ineq_tau6_tauVEF_std`（`lp_main_estimate-compiled.hl:988-1015`）。
DISCHARGES：骨架占位（同上群）。 -/
theorem ineq_tau6_tauVEF_std (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std_concl) (d : V3 × V3)
    (hd : d ∈ dartsK 6 (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    0.712 ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
  -- NEEDS（Lane G 侦察 2026-10-23）：同 tau4，卡 y-kit 章 + Face6 节桥。
  sorry

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

end Kepler.Text.TameLp
