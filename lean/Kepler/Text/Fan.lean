/-
Kepler.Text.Fan — Flyspeck fan 章定义层（`fan/fan_defs.hl`，304 行）

源：`reference/flyspeck/text_formalization/fan/fan_defs.hl`（经
`general/sphere.hl` 与 HOL Light `Multivariate/flyspeck.ml` 取 azim/wedge/
aff_ge 词汇，见 `Kepler/Geom/Azim.lean` 与 `Kepler/Geom/Aff.lean`）。

移植注记：
- dart 为二元组 `V3 × V3`（HOL fan 章约定；4 元组对应物 `iFan`/
  `extendedDart`/`contractedDart` 一并移植）。
- `hypermapOfFan` 与 `conforming_bijection` **暂缓**：我们的 `Hypermap`
  结构携带 `Equiv.Perm` 与 `PermutesOn` 证明，而 e/n/f_fan 的置换性是
  fan.hl 的定理（后续块）；届时以证明参数化的 def 落地（同 `IsMarked`
  的 hnf 提参模式）。
- `yfan_deprecated`（HOL 注释认定有误）与被注释掉的 `cw_dart_fan` 不移植。
- 选择算子 `@` ↔ `Classical.epsilon`；HOL `CARD s > 1` 的有限性前提由
  `Set.ncard` 的无限集取 0 约定蕴含。
-/

import Kepler.Geom.Azim
import Kepler.Geom.Aff
import Mathlib.Topology.Connected.Basic

open Classical

namespace Kepler.Text.Fan

open Kepler.Geom

variable {x y v u w : V3} {V : Set V3} {E : Set (Set V3)}

/-! ## fan 公理（fan_defs.hl:36–52） -/

/-- HOL `graph E`：每条边恰含两点（HAS_SIZE 2 的显式有限版）。 -/
def Graph (E : Set (Set V3)) : Prop :=
  ∀ e ∈ E, ∃ h : e.Finite, h.toFinset.card = 2

/-- HOL `fan1`：基数非平凡（有限非空）。 -/
def fan1 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop := V.Finite ∧ V ≠ ∅

/-- HOL `fan2`：原点不在顶点集。 -/
def fan2 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop := x ∉ V

/-- HOL `fan6`：无平行边（任一边与原点不共线）。 -/
def fan6 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ e ∈ E, ¬ Collinear ℝ (insert x e)

/-- HOL `fan7`：相交性（aff_ge 半空间在边上的分配律）。 -/
def fan7 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
    affGe {x} e1 ∩ affGe {x} e2 = affGe {x} (e1 ∩ e2)

/-- HOL `FAN(x,V,E)`。 -/
def FAN (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  (⋃₀ E) ⊆ V ∧ Graph E ∧ fan1 x V E ∧ fan2 x V E ∧ fan6 x V E ∧ fan7 x V E

/-! ## 邻边与 σ 映射（fan_defs.hl:55–85） -/

/-- HOL `set_of_edge v V E`：`v` 的邻居集。 -/
def setOfEdge (v : V3) (V : Set V3) (E : Set (Set V3)) : Set V3 :=
  {w | {v, w} ∈ E ∧ w ∈ V}

/-- HOL `sigma_fan x V E v u`：`u` 之后的下一邻居（方位角最小者；唯一
邻居时回自身）。 -/
noncomputable def sigmaFan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3) :
    V3 :=
  if setOfEdge v V E = {u} then u
  else Classical.epsilon (fun w => w ∈ setOfEdge v V E ∧ w ≠ u ∧
    ∀ w1 ∈ setOfEdge v V E, w1 ≠ u → azim x v u w ≤ azim x v u w1)

/-- HOL `extension_sigma_fan`：邻居集外恒等。 -/
noncomputable def extensionSigmaFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u : V3) : V3 :=
  if u ∉ setOfEdge v V E then u else sigmaFan x V E v u

/-- HOL `inverse_sigma_fan`（函数逆；HOL `inverse` ↔ `Function.invFun`）。 -/
noncomputable def inverseSigmaFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v : V3) : V3 → V3 :=
  Function.invFun (extensionSigmaFan x V E v)

/-! ## fan 的 dart（fan_defs.hl:88–128） -/

/-- HOL `dart1_of_fan (V,E)`：真 dart（有边的对）。 -/
def dart1OfFan (V : Set V3) (E : Set (Set V3)) : Set (V3 × V3) :=
  {d | {d.1, d.2} ∈ E}

/-- HOL `dart_of_fan (V,E)`：dart 集（孤立点补 (v,v)）。 -/
def dartOfFan (V : Set V3) (E : Set (Set V3)) : Set (V3 × V3) :=
  {d | d.1 = d.2 ∧ d.1 ∈ V ∧ setOfEdge d.1 V E = ∅} ∪ dart1OfFan V E

/-- HOL `i_fan`：4 元组对应物（(x,v,w,w) ↦ (x,v,w,σ w)）。 -/
noncomputable def iFan (x : V3) (V : Set V3) (E : Set (Set V3)) :
    V3 × V3 × V3 × V3 → V3 × V3 × V3 × V3 :=
  fun p => (p.1, p.2.1, p.2.2.1, sigmaFan x V E p.2.1 p.2.2.2)

/-- HOL `extended_dart (V,E) (v,w)`。 -/
noncomputable def extendedDart (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 × V3 × V3 :=
  iFan 0 V E (0, d.1, d.2, d.2)

/-- HOL `contracted_dart`。 -/
def contractedDart (p : V3 × V3 × V3 × V3) : V3 × V3 := (p.2.1, p.2.2.1)

/-! ## e/n/f 映射（fan_defs.hl:131–150） -/

/-- HOL `e_fan_pair (V,E) (v,w) = (w,v)`。 -/
def eFanPair (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) : V3 × V3 :=
  (d.2, d.1)

/-- HOL `n_fan_pair (V,E) (v,w) = (v, σ_v w)`（原点取 `vec 0`）。 -/
noncomputable def nFanPair (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  (d.1, sigmaFan 0 V E d.1 d.2)

/-- HOL `f_fan_pair (V,E) (v,w) = (w, σ⁻¹_ w v)`。 -/
noncomputable def fFanPair (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  (d.2, inverseSigmaFan 0 V E d.2 d.1)

/-- HOL `res f s`（sphere.hl:503）：集合外恒等的限制。 -/
noncomputable def res {α : Type*} (f : α → α) (s : Set α) : α → α :=
  fun a => if a ∈ s then f a else a

/-- HOL `e_fan_pair_ext`（= `res (e_fan_pair) (dart1_of_fan)`，见
`eFanPairExt_eq`）。 -/
noncomputable def eFanPairExt (V : Set V3) (E : Set (Set V3)) :
    V3 × V3 → V3 × V3 :=
  fun d => if d ∈ dart1OfFan V E then eFanPair V E d else d

/-- HOL `n_fan_pair_ext`。 -/
noncomputable def nFanPairExt (V : Set V3) (E : Set (Set V3)) : V3 × V3 → V3 × V3 :=
  fun d => if d ∈ dart1OfFan V E then nFanPair V E d else d

/-- HOL `f_fan_pair_ext`。 -/
noncomputable def fFanPairExt (V : Set V3) (E : Set (Set V3)) : V3 × V3 → V3 × V3 :=
  fun d => if d ∈ dart1OfFan V E then fFanPair V E d else d

theorem eFanPairExt_eq (V : Set V3) (E : Set (Set V3)) :
    eFanPairExt V E = res (eFanPair V E) (dart1OfFan V E) := rfl

theorem nFanPairExt_eq (V : Set V3) (E : Set (Set V3)) :
    nFanPairExt V E = res (nFanPair V E) (dart1OfFan V E) := rfl

theorem fFanPairExt_eq (V : Set V3) (E : Set (Set V3)) :
    fFanPairExt V E = res (fFanPair V E) (dart1OfFan V E) := rfl

/-! ## x/y 区域与楔形（fan_defs.hl:155–234） -/

/-- HOL `xfan (x,V,E)`：被边锥覆盖的区域。 -/
def xfan (x : V3) (V : Set V3) (E : Set (Set V3)) : Set V3 :=
  {v | ∃ e ∈ E, v ∈ affGe {x} e}

/-- HOL `yfan (x,V,E)` = 全空间 \\ xfan。 -/
def yfan (x : V3) (V : Set V3) (E : Set (Set V3)) : Set V3 :=
  Set.univ \ xfan x V E

/-- HOL `w_dart_fan x V E (y,v,w,w1)`。 -/
def wDartFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (p : V3 × V3 × V3 × V3) : Set V3 :=
  if (setOfEdge p.2.1 V E).ncard > 1 then
    wedge x p.2.1 p.2.2.1 (sigmaFan x V E p.2.1 p.2.2.1)
  else if setOfEdge p.2.1 V E = {p.2.2.1} then
    Set.univ \ affGe {x, p.2.1} {p.2.2.1}
  else if setOfEdge p.2.1 V E = ∅ then
    Set.univ \ (affineSpan ℝ ({x, p.2.1} : Set V3) : Set V3)
  else ∅

/-- HOL `cwedge v0 v1 w1 w2`。 -/
def cwedge (v0 v1 w1 w2 : V3) : Set V3 :=
  {y | 0 ≤ azim v0 v1 w1 y ∧ azim v0 v1 w1 y ≤ azim v0 v1 w1 w2}

/-- HOL `azim_fan x V E v w`。 -/
noncomputable def azimFan (x : V3) (V : Set V3) (E : Set (Set V3)) (v w : V3) :
    ℝ :=
  if (setOfEdge v V E).ncard > 1 then azim x v w (sigmaFan x V E v w)
  else 2 * Real.pi

/-- HOL `azim_dart (V,E) (v,w)`。 -/
noncomputable def azimDart (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) : ℝ :=
  if d.1 = d.2 then 2 * Real.pi else azimFan 0 V E d.1 d.2

/-- HOL `rcone_fan x v h`：半角锥。 -/
def rconeFan (x v : V3) (h : ℝ) : Set V3 :=
  {b | ((b - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) >
    dist b x * dist v x * h}

/-- HOL `rw_dart_fan x V E (y,v,w,w1) h`。 -/
def rwDartFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (p : V3 × V3 × V3 × V3) (h : ℝ) : Set V3 :=
  wDartFan x V E p ∩ rconeFan x p.2.1 h

/-! ## 拓扑分量与引导（fan_defs.hl:244–275） -/

/-- HOL `topological_component_yfan (x,V,E)`。 -/
def topologicalComponentYfan (x : V3) (V : Set V3) (E : Set (Set V3)) :
    Set (Set V3) :=
  {connectedComponentIn (yfan x V E) b | b ∈ yfan x V E}

/-- HOL `dart_leads_into1 (x,V,E) (v,u)`。 -/
noncomputable def dartLeadsInto1 (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u : V3) : Set V3 :=
  Classical.epsilon (fun s => s ∈ topologicalComponentYfan x V E ∧
    ∃ eps < 1, rwDartFan x V E (x, v, u, sigmaFan x V E v u) eps ⊆ s)

/-- HOL `dartset_leads_into (x,V,E) ds`。 -/
noncomputable def dartsetLeadsInto (x : V3) (V : Set V3) (E : Set (Set V3))
    (ds : Set (V3 × V3)) : Set V3 :=
  Classical.epsilon (fun s => ∀ b ∈ ds, s = dartLeadsInto1 x V E b.1 b.2)

/-- HOL `surrounded_node (V,E) v`。 -/
def surroundedNode (V : Set V3) (E : Set (Set V3)) (v : V3) : Prop :=
  ∀ d ∈ dartOfFan V E, d.1 = v → azimDart V E d < Real.pi

/-- HOL `fully_surrounded (V,E)`。 -/
def fullySurrounded (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ d ∈ dartOfFan V E, azimDart V E d < Real.pi

/-- HOL `fan81`。 -/
def fan81 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ v u : V3, {v, u} ∈ E → azimFan x V E v u < Real.pi

/-- HOL `fan80`。 -/
def fan80 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ v u : V3, {v, u} ∈ E →
    0 < azim x v u (sigmaFan x V E v u) ∧ azim x v u (sigmaFan x V E v u) < Real.pi


/-! ## fan_misc.hl（155 行）的可独立部分

其余三引理（`INVERSE_SIGMA_FAN`、`EXTENSION_SIGMA_FAN_INJECTIVE`、
`INVERSE_SIGMA_FAN_EQ_INVERSE1_SIGMA_FAN`）依赖 fan.hl 的
`permutes_sigma_fan`/`INVERSE1_SIGMA_FAN`（σ-置换理论，进而依赖
flyspeck.ml 的 azim 基础引理层 AZIM_REFL/AZIM_SYMM 等）——排入 F3。 -/

/-- HOL fan_misc `inverse1_sigma_fan`（ε-形式的三条件逆）。 -/
noncomputable def inverse1SigmaFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v : V3) : V3 → V3 :=
  Classical.epsilon (fun g => (∀ w : V3, {v, w} ∈ E → {v, g w} ∈ E) ∧
    (∀ w : V3, {v, w} ∈ E → sigmaFan x V E v (g w) = w) ∧
    (∀ w : V3, {v, w} ∈ E → g (sigmaFan x V E v w) = w))

/-- HOL fan_misc `EXTENSION_SIGMA_FAN_EQ_RES`。 -/
theorem extensionSigmaFan_eq_res (x : V3) (V : Set V3) (E : Set (Set V3))
    (v : V3) :
    extensionSigmaFan x V E v = res (sigmaFan x V E v) (setOfEdge v V E) := by
  funext u
  unfold extensionSigmaFan res
  by_cases hu : u ∈ setOfEdge v V E <;> simp [hu]

/-- HOL fan_misc `IN_SET_OF_EDGE`。 -/
theorem in_setOfEdge (V : Set V3) (E : Set (Set V3)) (v w : V3)
    (hsub : ⋃₀ E ⊆ V) (hd : (v, w) ∈ dart1OfFan V E) :
    v ∈ V ∧ w ∈ V ∧ w ∈ setOfEdge v V E ∧ v ∈ setOfEdge w V E := by
  have he : {v, w} ∈ E := hd
  have hv : v ∈ V := hsub (Set.mem_sUnion.mpr ⟨{v, w}, he, by simp⟩)
  have hw : w ∈ V := hsub (Set.mem_sUnion.mpr ⟨{v, w}, he, by simp⟩)
  have he' : {w, v} ∈ E := by
    have h2 : ({w, v} : Set V3) = ({v, w} : Set V3) := by
      apply Set.ext; intro a; simp; tauto
    rw [h2]; exact he
  exact ⟨hv, hw, ⟨he, hw⟩, ⟨he', hv⟩⟩

/-- HOL fan_misc `FAN_IN_SET_OF_EDGE`。 -/
theorem FAN_in_setOfEdge (x : V3) (V : Set V3) (E : Set (Set V3)) (v w : V3)
    (hfan : FAN x V E) (he : {v, w} ∈ E) :
    v ∈ V ∧ w ∈ V ∧ w ∈ setOfEdge v V E ∧ v ∈ setOfEdge w V E :=
  in_setOfEdge V E v w hfan.1 he


/-! ## σ-链起步：SIGMA_FAN spec 与集隶属（fan.hl:324/330/552/565） -/

/-- HOL fan.hl:324 `remark_finite_fan1`。 -/
theorem remark_finite_fan1 (v : V3) (V : Set V3) (E : Set (Set V3))
    (hV : V.Finite) : (setOfEdge v V E).Finite :=
  hV.subset (fun w hw => hw.2)

/-- HOL fan.hl:330 `properties_of_set_of_edge`。 -/
theorem properties_of_setOfEdge (v : V3) (V : Set V3) (E : Set (Set V3)) (u : V3)
    (hsub : ⋃₀ E ⊆ V) : ({v, u} ∈ E ↔ u ∈ setOfEdge v V E) := by
  constructor
  · intro he
    refine ⟨he, ?_⟩
    exact hsub (Set.mem_sUnion.mpr ⟨{v, u}, he, by simp⟩)
  · intro h
    exact h.1

/-- HOL fan.hl `exists_sigma_fan`（最小方位角见证的存在性）。 -/
theorem exists_sigmaFan (hne : setOfEdge v V E ≠ {u}) (hfan : FAN x V E)
    (hu : u ∈ setOfEdge v V E) :
    ∃ w : V3, w ∈ setOfEdge v V E ∧ w ≠ u ∧
      ∀ w1 ∈ setOfEdge v V E, w1 ≠ u → azim x v u w ≤ azim x v u w1 := by
  obtain ⟨hsub, -, ⟨hV, -⟩, -⟩ := hfan
  have hfin := remark_finite_fan1 v V E hV
  -- setOfEdge \ {u} 非空
  have hne2 : (setOfEdge v V E \ {u}).Nonempty := by
    by_contra hempty
    apply hne
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨hu, ?_⟩
    intro w hw
    by_contra hwu
    exact hempty ⟨w, ⟨hw, by simp [hwu]⟩⟩
  -- 有限非空实值集存在最小元
  have hfin2 : (setOfEdge v V E \ {u}).Finite :=
    hfin.subset (fun w hw => hw.1)
  obtain ⟨w, hwmem, hwmin⟩ :=
    Set.exists_min_image (setOfEdge v V E \ {u}) (fun w => azim x v u w) hfin2 hne2
  rw [Set.mem_sdiff, Set.mem_singleton_iff] at hwmem
  exact ⟨w, hwmem.1, hwmem.2, fun w1 hw1 hw1u => hwmin w1 ⟨hw1, by simp [hw1u]⟩⟩


/-- HOL fan.hl:552 `SIGMA_FAN`（σ 的 ε-witness 三条件）。 -/
theorem SIGMA_FAN (hne : setOfEdge v V E ≠ {u}) (hfan : FAN x V E)
    (hu : u ∈ setOfEdge v V E) :
    sigmaFan x V E v u ∈ setOfEdge v V E ∧ sigmaFan x V E v u ≠ u ∧
      ∀ w1 ∈ setOfEdge v V E, w1 ≠ u → azim x v u (sigmaFan x V E v u) ≤ azim x v u w1 := by
  unfold sigmaFan
  rw [if_neg hne]
  exact Classical.epsilon_spec (exists_sigmaFan hne hfan hu)

/-- HOL fan.hl:565 `sigma_fan_in_set_of_edge`。 -/
theorem sigma_fan_in_setOfEdge (hfan : FAN x V E) (hu : u ∈ setOfEdge v V E) :
    sigmaFan x V E v u ∈ setOfEdge v V E := by
  by_cases h : setOfEdge v V E = {u}
  · rw [sigmaFan, if_pos h, h]
    exact Set.mem_singleton u
  · exact (SIGMA_FAN h hfan hu).1

/-- HOL fan.hl:337 `properties_of_set_of_edge_fan`。 -/
theorem properties_of_setOfEdge_fan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (hfan : FAN x V E) : {v, u} ∈ E ↔ u ∈ setOfEdge v V E :=
  properties_of_setOfEdge v V E u hfan.1

end Kepler.Text.Fan

/- 计划（F3）：azim 基础引理层（flyspeck.ml 的 AZIM_REFL/AZIM_SYMM 等）→
fan.hl 的 sigma_fan_in_set_of_edge/permutes_sigma_fan/INVERSE1_SIGMA_FAN →
fan_misc 剩余三引理；随后 hypermapOfFan（证明参数化）与
conforming_bijection（需 Hypermap.faceSet）。 -/
