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
import Kepler.Text.PackingAuto2
import Kepler.Text.LocalAuto2
import Kepler.Text.LocalAuto16
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

/-! ## 3. lp_fan 支撑件（formal_lp/hypermap/ineqs 组） -/

/-- HOL `contravening_lp_fan`（`lp_ineqs_proofs-compiled.hl:385-400`，
section `Contravening` finalized 形）。
DISCHARGES：骨架占位；HOL 证明 4 步（lp_fan 展开 + contravening 逐合取 +
contraR/IN_ESTD 算术）。 -/
theorem contravening_lp_fan (V : Set V3) (hc : Contravening V) :
    LpFan V (ESTD V) := by
  sorry

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
  sorry

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

/-- HOL `JGTDEBU1`（`tame/JGTDEBU.hl:49-57`）：planar。
DISCHARGES：骨架占位；HOL 证明经 `CONTRAVENING_FAN` + `fan_hypermaps_iso`
+ `iso_planar` + `Conforming.GGRLKHP`（消耗 Conforming 章）。 -/
theorem JGTDEBU1 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    (hypermapOfFanTl V (ESTD V) hfan).Planar := by
  sorry

/-- HOL `JGTDEBU2`（`tame/JGTDEBU.hl:61-65`）：plain。
DISCHARGES：骨架占位；HOL 证明 `PLAIN_HYPERMAP_OF_FAN` 一步。 -/
theorem JGTDEBU2 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    (hypermapOfFanTl V (ESTD V) hfan).Plain := by
  sorry

/-- HOL `JGTDEBU3`（`tame/JGTDEBU.hl:69-77`）：connected。
DISCHARGES：骨架占位；同 JGTDEBU1 路径（`iso_connected` + `Conforming.WGVWSKE`）。 -/
theorem JGTDEBU3 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    (hypermapOfFanTl V (ESTD V) hfan).Connected := by
  sorry

/-- HOL `JGTDEBU4`（`tame/JGTDEBU.hl:81-89`）：simple。
DISCHARGES：骨架占位；同 JGTDEBU1 路径（`iso_simple` + `Conforming.SRPRNPL`）。
MQMSMAB :36 与 KCBLRQC 证明以其为枢纽。 -/
theorem JGTDEBU4 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    (hypermapOfFanTl V (ESTD V) hfan).Simple := by
  sorry

/-- HOL `JGTDEBU5`（`tame/JGTDEBU.hl:93-97`）：edge-nondegenerate。
DISCHARGES：骨架占位；`HYPERMAP_OF_FAN_EDGE_NONDEGENERATE` + fully_surrounded。 -/
theorem JGTDEBU5 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    (hypermapOfFanTl V (ESTD V) hfan).EdgeNondegenerate := by
  sorry

/-- HOL `JGTDEBU6`（`tame/JGTDEBU.hl:101-105`）：no_loops。
DISCHARGES：骨架占位；`HYPERMAP_OF_FAN_NO_LOOPS` 一步。 -/
theorem JGTDEBU6 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    Tame4 (hypermapOfFanTl V (ESTD V) hfan) := by
  sorry

/-- HOL `JGTDEBU7`（`tame/JGTDEBU.hl:109-113`）：no_double_joins。
DISCHARGES：骨架占位；`HYPERMAP_OF_FAN_NO_DOUBLE_JOINTS` 一步。 -/
theorem JGTDEBU7 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    Tame5a (hypermapOfFanTl V (ESTD V) hfan) := by
  sorry

/-- HOL `JGTDEBU8`（`tame/JGTDEBU.hl:133-210`）：`number_of_faces ≥ 3`。
DISCHARGES：骨架占位；HOL 证明约 30 步（`DART_EXISTS` +
`SURROUNDED_IMP_IN_DART1_OF_FAN` + `SIMPLE_HYPERMAP_lemma` 计数 + 
`SURROUNDED_IMP_CARD_NODE_GE_3`）。 -/
theorem JGTDEBU8 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    Tame8 (hypermapOfFanTl V (ESTD V) hfan) := by
  sorry

/-- HOL `JGTDEBU10`（`tame/JGTDEBU.hl:215-236`）：`tame_10`（节点数 13–15）。
DISCHARGES：骨架占位；HOL 证明经 `NODE_SET_AS_IMAGE` + `CARD_IMAGE_INJ`。 -/
theorem JGTDEBU10 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    Tame10 (hypermapOfFanTl V (ESTD V) hfan) := by
  sorry

/-- HOL `JGTDEBU11`（`tame/JGTDEBU.hl:241-253`）：`tame_11a`（node ≥ 3）。
DISCHARGES：骨架占位；`SURROUNDED_IMP_IN_DART1_OF_FAN` +
`SURROUNDED_IMP_CARD_NODE_GE_3`。 -/
theorem JGTDEBU11 (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V)) :
    Tame11a (hypermapOfFanTl V (ESTD V) hfan) := by
  sorry

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

关键路径（填实优先级建议）：
1. `JGTDEBU2/5/6/7`（一步定理，最先清偿）→ `JGTDEBU4`（Conforming.SRPRNPL
   依赖）→ `JGTDEBU1/3`（iso_planar/iso_connected，需 Conforming 章 GGRLKHP/
   WGVWSKE）→ `JGTDEBU8/10/11`。
2. `NODE_TYPE_lemma`（SIMPLE_HYPERMAP_lemma 计数核心，CDTETAT/KCBLRQC/BDJYFFB1
   共用）。
3. `COMPONENTS_HYPERMAP_OF_FAN`（本文件已给出 Lean 折算形的构造性证明）。
4. `CDTETAT`（21 情形算术 + kcblrqc_ineq_def 的两条 azim 边界）→ `SZIPOAS`。
5. `KCBLRQC`/`BDJYFFB1/2`（b_tame 表逐情形算术，可由 `decide`/`norm_num`
   批量消解，但前提是 1/2/4 到位）。
6. `CRTTXAT`（最重，依赖 arc_properties / per 周长和移植，独立子工程）。
7. `fully_surrounded_perimeter_bound`、`sum_tauVEF_upper_bound`、
   `ineq_tauK_tauVEF_std`（各依赖 Polar_fan / HRXEFDM / FaceK 分支不等式，
   属 formal_lp 侧子工程）。
-/

end Kepler.Text.TameLp
