/-
  Kepler.Text.TameLp — formal_lp/hypermap 桥章（KCBLRQC / BDJYFFB / CRTTXAT /
  JGTDEBU / SZIPOAS / CDTETAT 群 + `lp_fan` 支撑件）的定理陈述层移植。
  骨架模式：证明体 `sorry` + DISCHARGES 注明；供主定理债务图
  （Kepler/Assembly.lean §2c `mqmsmab`、§2d `lpArchiveCertificates`）落锚。

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
import Kepler.Text.TopologyFan
import Kepler.Text.PackingAuto2
import Kepler.Text.LocalAuto2
import Kepler.Text.LocalAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto1
import Kepler.Text.ConformingAuto21
import Kepler.Text.ConformingAuto23
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

/-- HOL `kcblrqc_ineq_def`（`tame/ssreflect/tame_lemmas-compiled.hl:34-46`）：
HOL 本体是对 Ineq 数据库按 flypaper ID 过滤后的不等式大合取
（`KCBLRQC`、`3287695934`、`6988401556`、`3862621143 side` 等机器生成项），
不具可手抄公式形态。骨架期折算为占位 `True`（Assembly §1c `KcblrqcIneqDef`
同形折算；真化依赖 G4 证书数据库）。 -/
def KcblrqcIneqDef : Prop := True

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
DISCHARGES：骨架占位；HOL 证明经 `Ckqowsa.CKQOWSA`（CKQOWSA 章：
ESTD_fan0/fan1/fan2/fan6 + fan7_2/fan7_3 的 aff_ge 交分配律锥几何核心，
约 600 行），该章未移植。注：Assembly.lean §2c `contraveningFan`（:444）
为同一债务的接口占位。 -/
theorem contravening_fanTl (V : Set V3) (hc : Contravening V) :
    FAN 0 V (ESTD V) := by
  sorry

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
`contravening_fanTl`（CKQOWSA 章，未移植）记欠。 -/
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

/-- HOL `sum_tauVEF_upper_bound`（`tame/ssreflect/tame_lemmas-compiled.hl:529-538`，
section FullySurrounded（fanV + f_surr，:286-290）finalized 形）。
`tauVEF` ↦ `Kepler.Text.tauVEF_p2`（localization.hl:1559）。
DISCHARGES：骨架占位；HOL 证明经 `tauVEF_alt2_alt` 改写 + `fully_surrounded_sum_sol`
+ `HRXEFDM_lemma1`，约 9 步。 -/
theorem sum_tauVEF_upper_bound (V : Set V3) (E : Set (Set V3))
    (hfan : FAN 0 V E) (hsurr : FullySurrounded V E)
    (hscript : 12 ≤ scriptL V) :
    setSum (hypermapOfFanTl V E hfan).faceSet (fun f => tauVEF_p2 V E f)
      ≤ 4 * Real.pi - 20 * sol0 := by
  sorry

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
  sorry

/-- HOL `ineq_tau4_tauVEF_std`（`lp_main_estimate-compiled.hl:796-817`）。
DISCHARGES：骨架占位（同上群）。 -/
theorem ineq_tau4_tauVEF_std (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std_concl) (d : V3 × V3)
    (hd : d ∈ dartsK 4 (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    0.206 ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
  sorry

/-- HOL `ineq_tau5_tauVEF_std`（`lp_main_estimate-compiled.hl:889-915`）。
DISCHARGES：骨架占位（同上群）。 -/
theorem ineq_tau5_tauVEF_std (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std_concl) (d : V3 × V3)
    (hd : d ∈ dartsK 5 (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    0.4819 ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
  sorry

/-- HOL `ineq_tau6_tauVEF_std`（`lp_main_estimate-compiled.hl:988-1015`）。
DISCHARGES：骨架占位（同上群）。 -/
theorem ineq_tau6_tauVEF_std (V : Set V3) (hlpfan : LpFan V (ESTD V))
    (hineq : JEJTVGB_std_concl) (d : V3 × V3)
    (hd : d ∈ dartsK 6 (hypermapOfFanTl V (ESTD V) hlpfan.1)) :
    0.712 ≤ tauVEF_p2 V (ESTD V) ((hypermapOfFanTl V (ESTD V) hlpfan.1).face d) := by
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

/-! ## 5. CDTETAT / SZIPOAS（tame/CDTETAT.hl，Solovyev 估计，
ssreflect 子目录专用件） -/

/-- CDTETAT :155-160 结论中的 20 个容许 `(p, q+r)` 对
（`CDTETAT_lemma1` :44-46 的集合字面量）。 -/
def cdTetatPairs : List (ℕ × ℕ) :=
  [(0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3),
    (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1),
    (6, 0), (6, 1), (7, 0)]

/-- HOL `CDTETAT`（`tame/CDTETAT.hl:155-160`，带前提形）。
DISCHARGES：骨架占位；HOL 证明约 60 步（`NODE_TYPE_lemma` +
`SUM_AZIM_DART_FULLY_SURROUNDED` + `FULLY_SURROUNDED_NODE_DECOMPOSITION` +
`CDTETAT_lemma1` :44-148 的 21 情形实数算术 + `kcblrqc_ineq_def` 的
`TRIANGULAR_FACE_AZIM_DART_BOUNDS`/`non_triangular_face_azim_dart_bound`）。 -/
theorem CDTETAT (hineq : KcblrqcIneqDef) (V : Set V3) (hc : Contravening V)
    (hfan : FAN 0 V (ESTD V)) (x : V3 × V3) (hx : x ∈ dartOfFan V (ESTD V)) :
    let H := hypermapOfFanTl V (ESTD V) hfan
    let p := (typeOfNode H x).1
    let q := (typeOfNode H x).2.1
    let r := (typeOfNode H x).2.2
    (p, q + r) ∈ cdTetatPairs := by
  sorry

/-- HOL `SZIPOAS`（`tame/CDTETAT.hl:306-308`）：`kcblrqc_ineq_def ⟹
contravening ⟹ tame_11b`。
DISCHARGES：骨架占位；HOL 证明经 `FULLY_SURROUNDED_IMP_CARD_NODE_EQ_SUM_NODE_TYPE`
+ `CDTETAT` 分类 + 20 情形算术。 -/
theorem SZIPOAS (hineq : KcblrqcIneqDef) (V : Set V3) (hc : Contravening V)
    (hfan : FAN 0 V (ESTD V)) :
    Tame11b (hypermapOfFanTl V (ESTD V) hfan) := by
  sorry

/-! ## 6. KCBLRQC / BDJYFFB（tame/ssreflect/KCBLRQC-compiled.hl）。
两个 section（Contravening :927-935 的 contrV，BDJYFFB :922-924 的
h_main := lp_main_estimate、ineqs := kcblrqc_ineq_def）finalized 形。 -/

/-- HOL `KCBLRQC`（`tame/ssreflect/KCBLRQC-compiled.hl:868-873`，
node-type 不等式：`r > 0 ∨ sum (set_of_face_meeting_node H d) tauVEF ≥ b_tame p q`）。
DISCHARGES：骨架占位；HOL 证明 21 情形 b_tame 表算术（get_b_tame_ineq 驱动，
:874-908，每情形 4-6 步），入口为 `NODE_TYPE_lemma` + `CDTETAT`。规模粗评：
证明体 ~40 行 tactic + `get_b_tame_ineq` 表。 -/
theorem KCBLRQC (V : Set V3) (hc : Contravening V)
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef)
    (hfan : FAN 0 V (ESTD V)) (d : V3 × V3) (hd : d ∈ dartOfFan V (ESTD V)) :
    let H := hypermapOfFanTl V (ESTD V) hfan
    let p := (typeOfNode H d).1
    let q := (typeOfNode H d).2.1
    let r := (typeOfNode H d).2.2
    0 < r ∨ setSum (setOfFaceMeetingNode H d)
        (fun f => tauVEF_p2 V (ESTD V) f) ≥ bTame p q := by
  sorry

/-- HOL `BDJYFFB1`（`tame/ssreflect/KCBLRQC-compiled.hl:917-919`）：`tame_12o`。
DISCHARGES：骨架占位；HOL 证明约 35 步（`fully_surrounded_dart_of_fan_eq` +
`CARD_FACE_GT_1` + `NODE_TYPE_lemma` +
`FULLY_SURROUNDED_IMP_CARD_NODE_EQ_SUM_NODE_TYPE` + `CDTETAT` +
get_b_tame_ineq 的 (6,0,1)/(3,0,3)/(3,1,2)/(3,2,1)/(4,0,2)/(4,1,1) 情形）。 -/
theorem BDJYFFB1 (V : Set V3) (hc : Contravening V)
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef)
    (hfan : FAN 0 V (ESTD V)) :
    Tame12o (hypermapOfFanTl V (ESTD V) hfan) := by
  sorry

/-- HOL `BDJYFFB2`（`tame/ssreflect/KCBLRQC-compiled.hl:962-967`）：
type (5,0,1) 的节点上三角形 tauVEF 和 `> #0.63`（`a_tame`）。
DISCHARGES：骨架占位；HOL 证明 4 步（get_b_tame_ineq (5,0,1) + 算术）。 -/
theorem BDJYFFB2 (V : Set V3) (hc : Contravening V)
    (hmain : lp_main_estimate) (hineq : KcblrqcIneqDef)
    (hfan : FAN 0 V (ESTD V)) (d : V3 × V3)
    (hd : d ∈ dartOfFan V (ESTD V))
    (htype : typeOfNode (hypermapOfFanTl V (ESTD V) hfan) d = (5, 0, 1)) :
    aTame < setSum {f | f ∈ setOfFaceMeetingNode (hypermapOfFanTl V (ESTD V) hfan) d ∧
        f.ncard = 3}
      (fun f => tauVEF_p2 V (ESTD V) f) := by
  sorry

/-! ## 7. CRTTXAT（tame/CRTTXAT.hl，tame_9a 出口，Solovyev 2010） -/

/-- HOL `CRTTXAT`（`tame/CRTTXAT.hl:311-320`，assumption 形
`CRTTXAT_assum`：`(!V. contravening V ==> simple_hypermap …) ==> (!V.
contravening V /\ perimeterbound (V,ESTD V) ==> tame_9a …)`）。
DISCHARGES：骨架占位；HOL 证明本体 :320-470（`CRTTXAT_lemma1/2/1'` +
`arc_properties` 章 + `per` 周长和的轨道求和），规模 >250 行 tactic，
为桥章最重单件。 -/
theorem CRTTXAT
    (hsimple : ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)),
      Contravening V → (hypermapOfFanTl V (ESTD V) hfan).Simple)
    (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V))
    (hpb : PerimeterBound V (ESTD V) hfan) :
    Tame9a (hypermapOfFanTl V (ESTD V) hfan) := by
  sorry

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
5. 剩余债务：`contravening_fanTl`（CKQOWSA 章，未移植；`contravening_lp_fan`
   仅欠此一步，其余由 `contravening_lp_fan_of_fan` 真证明）→ `CDTETAT`
   （21 情形算术 + kcblrqc_ineq_def 两条 azim 边界）→ `SZIPOAS` →
   `KCBLRQC`/`BDJYFFB1/2`（b_tame 表逐情形算术）。
6. `CRTTXAT`（最重，依赖 arc_properties / per 周长和移植，独立子工程）。
7. `fully_surrounded_perimeter_bound`、`sum_tauVEF_upper_bound`、
   `ineq_tauK_tauVEF_std`（各依赖 Polar_fan / HRXEFDM / FaceK 分支不等式，
   属 formal_lp 侧子工程）。
-/

end Kepler.Text.TameLp
