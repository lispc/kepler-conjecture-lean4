/-
LocalAuto7W16b: W16b — 切片↔`vPrime` 桥链（HOL `COMPATIBLE_BW_TWO_LEMMAS` 的 Lean 移植）。

## 目标与用途

`EJRCFJD_ALT2`（LA2:1589，未证桩）合取 1–2 需要
`vPrime_p2 V fv = slicev_p2 E FF v w`（及 `ePrime`/`fv` 同款）。HOL 走
`COMPATIBLE_BW_TWO_LEMMAS`（Nkezbfc.hl:1413，238 行）→ `...2`（:1651，34 行）。
本件按 HOL 逐段移植，**p2 词汇、正序形**（`fv = HS.face …`；LA9 的 `_p9` 桩是反序，不改）。

## 件表

* `p16b_order_iff`：`(∀ m < n, ρ^[m] v ≠ w) ↔ n ≤ order ρ v w`（HOL `ORDER`/`UNIQUE_ORDER` 的最小性）；
* `p16b_vPrime_eq`：`vPrime_p2 V fv = slicev_p2 E FF v w`（吃 `POINTS_IN_HAFL_CIRCLE` 的截断形）；
* `p16b_fv_eq`：`fv = slicef_p2 E FF v w`（`DETERMINE_FV2` + 切片分解）；
* `p16b_ePrime_eq`：`ePrime_p2 (E ∪ {{v,w}}) fv = slicee_p2 E FF v w`；
* **`p16b_compatible`**（公开）：HOL `COMPATIBLE_BW_TWO_LEMMAS` 的三合取；
* **`p16b_compatible2`**（公开）：HOL `COMPATIBLE_BW_TWO_LEMMAS2`（`(v,w)` 与 `(w,v)` 双边）。

依赖全部在库且 std3（本批机器复核）：`PROVE_THE_SLICE_ASSUMPTION` / `POINTS_IN_HAFL_CIRCLE` /
`DETERMINE_FV2` / `LOCAL_FAN_ORBIT_MAP_V` / `ORDER_p9` / `UNIQUE_ORDER_p9` / `CVX_LO_IMP_LO`。
W16 / W13A–F / LA2 / LA6 / LA9 零改动；无新增 import。
-/
import Kepler.Text.LocalAuto7W16

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## 1. 序的最小性（HOL `ORDER` / `UNIQUE_ORDER`） -/

/-- **`(∀ m < n, ρ^[m] v ≠ w) ↔ n ≤ order ρ v w`**：`order` 是首次命中 `w` 的迭代数，
故「前 `n` 步都不命中」等价于 `n` 不超过它。 -/
theorem p16b_order_iff {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v w : V3} (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w) :
    ∀ n : ℕ, (∀ m, m < n → (rhoNode1_p2 FF)^[m] v ≠ w) ↔
      n ≤ order_p2 (rhoNode1_p2 FF) v w := by
  -- 轨道覆盖 `V`：`w` 必在某步被命中
  have hmem : w ∈ orbitF_p2 (rhoNode1_p2 FF) v := by
    rw [LOCAL_FAN_ORBIT_MAP_V h hv]
    exact hw
  obtain ⟨n0, hn0⟩ := hmem
  have hex : ∃ k, (rhoNode1_p2 FF)^[k] v = w := ⟨n0, hn0⟩
  have hspec := ORDER_p9 (rhoNode1_p2 FF) v w (Nat.find hex) (Nat.find_spec hex)
    (fun i _ hi => Nat.find_min hex hi)
  intro n
  constructor
  · intro hn
    by_contra hlt
    exact hn _ (Nat.lt_of_not_le hlt) hspec.1
  · intro hn m hm
    by_contra heq
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at heq
      exact hvw (by simpa using heq)
    · exact hspec.2 m h0 (Nat.lt_of_lt_of_le hm hn) heq

/-! ## 2. `vPrime` 侧（HOL `COMPATIBLE_BW_TWO_LEMMAS` 合取 1） -/

/-- **`vPrime_p2 V fv = slicev_p2 E FF v w`**：`POINTS_IN_HAFL_CIRCLE` 把 `vPrime` 写成
「到 `w` 为止（不含）的轨道」，`p16b_order_iff` 再把该条件换成 `n ≤ order`。 -/
theorem p16b_vPrime_eq {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} {fv : Set (V3 × V3)}
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} → ¬Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    vPrime_p2 V fv = slicev_p2 E FF v w := by
  rw [POINTS_IN_HAFL_CIRCLE h hv hw hvw hcol hsub HS hHS hfv]
  ext z
  simp only [Set.mem_setOf_eq, slicev_p2]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, (p16b_order_iff h hv hw hvw n).mp hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, (p16b_order_iff h hv hw hvw n).mpr hn, rfl⟩


/-! ## 3. `fv` 侧（HOL `COMPATIBLE_BW_TWO_LEMMAS` 合取 3） -/

/-- **`fv = slicef_p2 E FF v w`**：`POINT_PRESENTED_IN_RHOND1` 给有界最小命中 `n`
（`n = order`，由 `UNIQUE_ORDER_p9`），`DETERMINE_FV2` 把 `fv` 写成「`(w,v)` + 前 `n` 条边」，
再与 `slicef_p2` 的「`u ∈ slicev` 且 `u ≠ w`」逐点对齐（`m ≤ n` 且 `ρ^[m] v ≠ w` ⟺ `m < n`）。 -/
theorem p16b_fv_eq {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} {fv : Set (V3 × V3)}
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} → ¬Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    fv = slicef_p2 E FF v w := by
  obtain ⟨n, hnlt, hnw, hnmin⟩ := POINT_PRESENTED_IN_RHOND1 h hv hw
  have hord : order_p2 (rhoNode1_p2 FF) v w = n :=
    UNIQUE_ORDER_p9 (rhoNode1_p2 FF) v w n hnw (fun i _ hi => hnmin i hi) hvw
  have hslice : slicef_p2 E FF v w
      = insert (w, v)
          {p : V3 × V3 | ∃ m, m < n ∧ p = ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v)} := by
    rw [slicef_p2, slicev_p2, hord]
    ext p
    constructor
    · rintro (⟨u, ⟨m, hm, rfl⟩, hune, rfl⟩ | rfl)
      · refine Set.mem_insert_of_mem _ ⟨m, ?_, ?_⟩
        · by_contra hge
          exact hune (le_antisymm hm (Nat.le_of_not_lt hge) ▸ hnw)
        · rw [Function.iterate_succ_apply']
      · exact Set.mem_insert _ _
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact Or.inr rfl
      · refine Or.inl ⟨(rhoNode1_p2 FF)^[m] v, ⟨m, Nat.le_of_lt hm, rfl⟩, hnmin m hm, ?_⟩
        rw [Function.iterate_succ_apply']
  rw [hslice, DETERMINE_FV2 h hv hw hvw hcol hsub HS hHS hfv hnlt hnw]

/-! ## 4. `ePrime` 侧（HOL `COMPATIBLE_BW_TWO_LEMMAS` 合取 2） -/

/-- **`ePrime_p2 (E ∪ {{v,w}}) fv = slicee_p2 E FF v w`**：`fv = slicef_p2` 之后，
`ePrime` 的元素就是「切片内 dart 的边」加合并边 `{w,v}`；切片内 `u ∈ V` ⇒
`{u, ρu} ∈ E`（`LOCAL_RHO_NODE_PAIR_E`），故两边逐点相同。 -/
theorem p16b_ePrime_eq {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} {fv : Set (V3 × V3)}
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} → ¬Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p2 E FF v w := by
  have hfv' : fv = slicef_p2 E FF v w := p16b_fv_eq h hv hw hvw hcol hsub HS hHS hfv
  rw [hfv']
  ext e
  constructor
  · rintro ⟨a, b, rfl, -, hab⟩
    rcases hab with ⟨u, hu, hune, hpair⟩ | hpair
    · have ha : a = u := congrArg Prod.fst hpair
      have hb : b = rhoNode1_p2 FF u := congrArg Prod.snd hpair
      rw [ha, hb]
      exact Or.inl ⟨u, hu, hune, rfl⟩
    · have ha : a = w := congrArg Prod.fst hpair
      have hb : b = v := congrArg Prod.snd hpair
      rw [ha, hb]
      exact Or.inr rfl
  · rintro (⟨u, hu, hune, rfl⟩ | rfl)
    · have huV : u ∈ V := by
        obtain ⟨m, -, rfl⟩ := hu
        exact LOCAL_FAN_ORBIT_MAP_VITER h hv m
      exact ⟨u, rhoNode1_p2 FF u, rfl, Or.inl (LOCAL_RHO_NODE_PAIR_E h huV),
        Or.inl ⟨u, hu, hune, rfl⟩⟩
    · exact ⟨w, v, rfl, Or.inr (by simp [Set.pair_comm]), Or.inr rfl⟩

/-! ## 5. 两公开件：HOL `COMPATIBLE_BW_TWO_LEMMAS` / `...2` -/

/-- **HOL `COMPATIBLE_BW_TWO_LEMMAS`（p2 词汇、正序形）**：`(v,w)` 侧的三合取。 -/
theorem p16b_compatible {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} {fv : Set (V3 × V3)}
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} → ¬Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    vPrime_p2 V fv = slicev_p2 E FF v w ∧
      ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p2 E FF v w ∧
      fv = slicef_p2 E FF v w :=
  ⟨p16b_vPrime_eq h hv hw hvw hcol hsub HS hHS hfv,
   p16b_ePrime_eq h hv hw hvw hcol hsub HS hHS hfv,
   p16b_fv_eq h hv hw hvw hcol hsub HS hHS hfv⟩

/-- **HOL `COMPATIBLE_BW_TWO_LEMMAS2`（双边）**：`(v,w)` 与 `(w,v)` 两侧各三合取
（HOL 的 `INSERT_COMM` 在 `E ∪ {{w,v}} = E ∪ {{v,w}}` 处）。 -/
theorem p16b_compatible2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} {fv fw : Set (V3 × V3)}
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} → ¬Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    (vPrime_p2 V fv = slicev_p2 E FF v w ∧
        ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p2 E FF v w ∧
        fv = slicef_p2 E FF v w) ∧
      (vPrime_p2 V fw = slicev_p2 E FF w v ∧
        ePrime_p2 (E ∪ {{w, v}}) fw = slicee_p2 E FF w v ∧
        fw = slicef_p2 E FF w v) := by
  have hcol' : ∀ z t : V3, z ∈ ({w, v} : Set V3) → t ∈ V \ {z} →
      ¬Collinear ℝ ({0, z, t} : Set V3) := by
    intro z t hz
    rw [show ({w, v} : Set V3) = {v, w} from Set.pair_comm w v] at hz
    exact hcol z t hz
  have hE : E ∪ {{w, v}} = E ∪ {{v, w}} := by rw [Set.pair_comm w v]
  have hsub' : ∀ x ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 x E := by
    intro x hx
    rw [Set.pair_comm w v]
    exact hsub x hx
  have hHS' : IsHyp_p2 0 V (E ∪ {{w, v}}) HS := hE.symm ▸ hHS
  exact ⟨p16b_compatible h hv hw hvw hcol hsub HS hHS hfv,
    hE ▸ p16b_compatible h hw hv (Ne.symm hvw) hcol' hsub' HS hHS' hfw⟩

/-- **p9 反序形的换序桥**：LA9 的 `COMPATIBLE_BW_TWO_LEMMAS_p9` 桩用
`HS.face (v, ρv) = fv`（反序），本件的 `p16b_compatible` 用正序 `fv = HS.face (v, ρv)`。
此处给一行换序形，落库对表时直接可用（**不改 p9 桩**）。 -/
theorem p16b_compatible_p9form {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} {fv : Set (V3 × V3)}
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} → ¬Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : HS.face (v, rhoNode1_p2 FF v) = fv) :
    vPrime_p2 V fv = slicev_p2 E FF v w ∧
      ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p2 E FF v w ∧
      fv = slicef_p2 E FF v w :=
  p16b_compatible h hv hw hvw hcol hsub HS hHS hfv.symm

/-- **LA9 `COMPATIBLE_BW_TWO_LEMMAS_p9` 桩（`LocalAuto9.lean:3200`，未证）的陈述，已证**：
把 `p16b_compatible_p9form` 接到 p9 词汇上。p9 桩**没有** `hcol` 前提，但
`PROVE_THE_SLICE_ASSUMPTION`（LA6，std3）恰好从 `hcl/hv/hw/hvw/hsub` 给出它
⇒ 该桩的**内容**在此完全闭合（`_p2`/`_p9` 切片定义 rfl 级相等）。
LA9 不能 import 本文件，故以新名在下游给出；退休时一行对齐。 -/
theorem p16b_compatible_p9 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} {fv : Set (V3 × V3)}
    (h : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : HS.face (v, rhoNode1_p2 FF v) = fv) :
    vPrime_p2 V fv = slicev_p9 E FF v w ∧
      ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p9 E FF v w ∧
      fv = slicef_p9 E FF v w :=
  p16b_compatible_p9form (CVX_LO_IMP_LO h) hv hw hvw
    (fun z t hz ht => PROVE_THE_SLICE_ASSUMPTION h hv hw hvw hsub z t hz ht) hsub HS hHS hfv

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p16b_order_iff
#print axioms Kepler.Text.p16b_vPrime_eq
#print axioms Kepler.Text.p16b_fv_eq
#print axioms Kepler.Text.p16b_ePrime_eq
#print axioms Kepler.Text.p16b_compatible
#print axioms Kepler.Text.p16b_compatible2
#print axioms Kepler.Text.p16b_compatible_p9form
#print axioms Kepler.Text.p16b_compatible_p9

end Kepler.Text
