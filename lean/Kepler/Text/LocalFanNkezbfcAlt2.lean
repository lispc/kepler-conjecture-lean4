/-
Kepler/Text/LocalFanNkezbfcAlt2.lean — wave B: `EJRCFJD_ALT2` 真证。

目标（HOL `localization.hl:1367-1501`；树内陈述 `LocalAuto2.lean:1589-1605`）：
在 `convexLocalFan_p2 V E FF`、`v,w ∈ V`、对角线非共线、切片弦条件下，
两片切片扇仍是凸局部扇，且 tau 不减、sol 可加、顶点数严格下降、generic 保持。

## 与既有件的关系（全部机器核实，见文件末尾探针）

* `EJRCFJD`（`LocalAuto6.lean:6763`，std3）给出 HS 形结论：两片
  `convexLocalFan_p2 (vPrime …) (ePrime …) fv/fw` + 以 `vPrime` 为索引的角度和恒等式。
* 切片恒等式（`vPrime=slicev`、`ePrime=slicee`、`fv=slicef`）由
  `DETERMINE_FV2`（LA6:5867，std3）＋ `order_p2` 最小性给出；**不消费** LA2 的
  `COMPATIBLE_BW_TWO_LEMMAS2_ALT`（该件在库内是未完成声明）。
* `CARD_SLICEV` / `CARD_SLICEF` 由 `CARD_V_TWO_HAFL_CIRCLE`（LA6:5683，std3）＋
  `LOFA_IMP_BIJ_FF_V`（LA5:7030，std3）＋ `LOFA_IMP_CARD_FF_V_EQ` 重推；
  **不消费** LA2 的 `CARD_SLICEV` / `CARD_SLICEF` / `ejr_generic`。
* generic 保持按 HOL `localization.hl:1074-1170` 的路线在本文件内重证。

## 不许 import LA14

import 面：`Kepler.Text.LocalAuto6`（`EJRCFJD` 家族、`PROVE_SLICING_FAN`、切片 kit）
+ `Kepler.Text.LocalAuto9`（`SOL_LOFA_EQ_SUM_INANGLE_p9`、`CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_p9`）。
两条 import 均不经过 `LocalAuto14`。
-/
import Kepler.Text.LocalAuto6
import Kepler.Text.LocalAuto9
import Kepler.Text.LocalAuto37

set_option maxHeartbeats 4000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## `setSum` 重索引小工具 -/

private theorem pB_setSum_congr {α : Type*} {s : Set α} {f g : α → ℝ}
    (h : ∀ x ∈ s, f x = g x) : setSum s f = setSum s g := by
  unfold setSum
  by_cases hs : s.Finite
  · simp only [dif_pos hs]
    exact Finset.sum_congr rfl fun x hx => h x ((Set.Finite.mem_toFinset hs).mp hx)
  · simp only [dif_neg hs]

private theorem pB_setSum_reindex {α β : Type*} {A : Set α} {B : Set β}
    (hA : A.Finite) (hB : B.Finite) (ab : α → β) (g : β → ℝ)
    (h : Set.BijOn ab A B) : setSum A (fun x => g (ab x)) = setSum B g := by
  classical
  rw [setSum, dif_pos hA, setSum, dif_pos hB]
  have hinj : ∀ x ∈ hA.toFinset, ∀ y ∈ hA.toFinset, ab x = ab y → x = y :=
    fun x hx y hy he => h.injOn (hA.mem_toFinset.mp hx) (hA.mem_toFinset.mp hy) he
  have himg : hA.toFinset.image ab = hB.toFinset := by
    ext y
    simp only [Finset.mem_image, hA.mem_toFinset, hB.mem_toFinset]
    exact ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ h.mapsTo hx, fun hy => by
      obtain ⟨x, hx, hxy⟩ := h.surjOn hy
      exact ⟨x, hx, hxy⟩⟩
  rw [← himg, Finset.sum_image]
  intro x hx y hy hxy
  exact hinj x hx y hy hxy

/-! ## `order_p2` 的闭式：`order ρ v w = n`（`w = ρ^[n] v` 且最小） -/

private theorem pB_order_eq {v w : V3} {n : ℕ}
    (hvw : v ≠ w) (hnw : (rhoNode1_p2 FF)^[n] v = w)
    (hnmin : ∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w)) :
    order_p2 (rhoNode1_p2 FF) v w = n := by
  classical
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hp
    · rw [h0, Function.iterate_zero, id] at hnw
      exact absurd hnw hvw
    · exact hp
  have hprop : (rhoNode1_p2 FF)^[n] v = w ∧
      ∀ i : ℕ, 0 < i → i < n → ¬((rhoNode1_p2 FF)^[i] v = w) :=
    ⟨hnw, fun i _ hi => hnmin i hi⟩
  have hspec := Classical.epsilon_spec (p := fun k : ℕ =>
    (rhoNode1_p2 FF)^[k] v = w ∧
      ∀ i : ℕ, 0 < i → i < k → ¬((rhoNode1_p2 FF)^[i] v = w)) ⟨n, hprop⟩
  obtain ⟨hk1, hk2⟩ := hspec
  rcases lt_trichotomy (order_p2 (rhoNode1_p2 FF) v w) n with hlt | heq | hgt
  · exact absurd hk1 (hnmin _ hlt)
  · exact heq
  · exact absurd hnw (hk2 n hnpos hgt)

/-! ## 切片顶点集：`slicev` 的迭代形 -/

private theorem pB_slicev_eq {v w : V3} {n : ℕ}
    (hvw : v ≠ w) (hnw : (rhoNode1_p2 FF)^[n] v = w)
    (hnmin : ∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w)) :
    slicev_p2 E FF v w =
      {u : V3 | ∃ k : ℕ, k < n + 1 ∧ u = (rhoNode1_p2 FF)^[k] v} := by
  unfold slicev_p2
  rw [pB_order_eq (FF := FF) (v := v) (w := w) (n := n) hvw hnw hnmin]
  ext u
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by omega, rfl⟩

private theorem pB_slicev_image {v w : V3} {n : ℕ}
    (hvw : v ≠ w) (hnw : (rhoNode1_p2 FF)^[n] v = w)
    (hnmin : ∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w)) :
    slicev_p2 E FF v w =
      (fun k : ℕ => (rhoNode1_p2 FF)^[k] v) '' {k : ℕ | k < n + 1} := by
  rw [pB_slicev_eq (FF := FF) (v := v) (w := w) (n := n) hvw hnw hnmin]
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_image]
  exact ⟨fun ⟨k, hk, hu⟩ => ⟨k, hk, hu.symm⟩, fun ⟨k, hk, hu⟩ => ⟨k, hk, hu.symm⟩⟩

end Kepler.Text

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## 切片面：`fv = slicef` -/

private theorem pB_face_eq_slicef
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    {fv : Set (V3 × V3)} (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    {n : ℕ} (hnlt : n < V.ncard) (hnw : (rhoNode1_p2 FF)^[n] v = w)
    (hnmin : ∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w)) :
    fv = slicef_p2 E FF v w := by
  have hFV2 := DETERMINE_FV2 h hv hw hvw hcol hsub HS hHS hfv hnlt hnw
  unfold slicef_p2
  rw [hFV2]
  ext p
  constructor
  · intro hp
    rcases Set.mem_insert_iff.mp hp with hpw | hpS
    · exact Or.inr hpw
    · rw [Set.mem_setOf_eq] at hpS
      obtain ⟨m, hm, hpm⟩ := hpS
      refine Or.inl ⟨(rhoNode1_p2 FF)^[m] v, ?_, ?_, ?_⟩
      · rw [pB_slicev_eq (FF := FF) (v := v) (w := w) (n := n) hvw hnw hnmin]
        exact ⟨m, by omega, rfl⟩
      · intro hcon
        exact hnmin m hm hcon
      · rw [hpm, Function.iterate_succ_apply']
  · rintro (⟨u, hu, huw, hpu⟩ | hpw)
    · rw [pB_slicev_eq (FF := FF) (v := v) (w := w) (n := n) hvw hnw hnmin] at hu
      obtain ⟨m, hm, hum⟩ := hu
      have hmlt : m < n := by
        rcases lt_or_eq_of_le (by omega : m ≤ n) with hmn | hmn
        · exact hmn
        · exfalso
          apply huw
          rw [hum, hmn, hnw]
      rw [Set.mem_insert_iff]
      right
      rw [Set.mem_setOf_eq]
      refine ⟨m, hmlt, ?_⟩
      rw [hpu, hum, Function.iterate_succ_apply']
    · exact Set.mem_insert_iff.mpr (Or.inl hpw)

/-! ## `vPrime V fv = slicev` -/

private theorem pB_vprime_eq_slicev
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hvw : v ≠ w)
    (hnw : (rhoNode1_p2 FF)^[n] v = w)
    (hnmin : ∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w))
    {fv : Set (V3 × V3)} (hfv : fv = slicef_p2 E FF v w) :
    vPrime_p2 V fv = slicev_p2 E FF v w := by
  rw [hfv]
  unfold vPrime_p2
  ext z
  constructor
  · rintro ⟨-, y, hy⟩
    unfold slicef_p2 at hy
    rw [Set.mem_union] at hy
    rcases hy with ⟨u, hu, huw, huy⟩ | hyw
    · have hzu : z = u := (Prod.ext_iff.mp huy).1
      rw [hzu]
      exact hu
    · have hzw : z = w := (Prod.ext_iff.mp hyw).1
      rw [hzw,
        pB_slicev_eq (FF := FF) (v := v) (w := w) (n := n) hvw hnw hnmin]
      exact ⟨n, by omega, hnw.symm⟩
  · intro hz
    have hzV : z ∈ V := by
      rw [pB_slicev_eq (FF := FF) (v := v) (w := w) (n := n) hvw hnw hnmin] at hz
      obtain ⟨k, -, rfl⟩ := hz
      exact LOCAL_FAN_ITER_RHO_NODE_IN_V h hv k
    refine ⟨hzV, ?_⟩
    rw [pB_slicev_eq (FF := FF) (v := v) (w := w) (n := n) hvw hnw hnmin] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    by_cases hkn : k = n
    · refine ⟨v, ?_⟩
      unfold slicef_p2
      rw [Set.mem_union]
      right
      rw [hkn, hnw]
      rfl
    · have hklt : k < n := by omega
      refine ⟨(rhoNode1_p2 FF)^[k + 1] v, ?_⟩
      unfold slicef_p2
      rw [Set.mem_union]
      left
      refine ⟨(rhoNode1_p2 FF)^[k] v, ?_, ?_, ?_⟩
      · rw [pB_slicev_eq (FF := FF) (v := v) (w := w) (n := n) hvw hnw hnmin]
        exact ⟨k, by omega, rfl⟩
      · intro hcon
        exact hnmin k hklt hcon
      · rw [Function.iterate_succ_apply']

/-! ## `ePrime (E ∪ {{v,w}}) fv = slicee` -/

private theorem pB_eprime_eq_slicee
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hvw : v ≠ w)
    (hnw : (rhoNode1_p2 FF)^[n] v = w)
    (hnmin : ∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w))
    {fv : Set (V3 × V3)} (hfv : fv = slicef_p2 E FF v w) :
    ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p2 E FF v w := by
  rw [hfv]
  unfold ePrime_p2 slicee_p2
  ext e
  constructor
  · rintro ⟨a, b, heq, -, hdart⟩
    unfold slicef_p2 at hdart
    rw [Set.mem_union] at hdart
    rcases hdart with ⟨u, hu, huw, huy⟩ | hyw
    · have hab : (a, b) = (u, rhoNode1_p2 FF u) := huy
      have ha : a = u := (Prod.ext_iff.mp hab).1
      have hb : b = rhoNode1_p2 FF u := (Prod.ext_iff.mp hab).2
      rw [Set.mem_union]
      left
      refine ⟨u, hu, huw, ?_⟩
      rw [heq, ha, hb]
    · have hab : (a, b) = (w, v) := hyw
      have ha : a = w := (Prod.ext_iff.mp hab).1
      have hb : b = v := (Prod.ext_iff.mp hab).2
      rw [Set.mem_union]
      right
      rw [heq, ha, hb]
      simp
  · rintro (⟨u, hu, huw, heq⟩ | heq)
    · refine ⟨u, rhoNode1_p2 FF u, heq, ?_, ?_⟩
      · rw [Set.mem_union]
        left
        have huV : u ∈ V := by
          rw [pB_slicev_eq (FF := FF) (v := v) (w := w) (n := n) hvw hnw hnmin] at hu
          obtain ⟨k, -, rfl⟩ := hu
          exact LOCAL_FAN_ITER_RHO_NODE_IN_V h hv k
        have hdart : (u, rhoNode1_p2 FF u) ∈ FF :=
          (LOCAL_FAN_RHO_NODE_PROS h).1 u huV
        exact LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hdart
      · unfold slicef_p2
        rw [Set.mem_union]
        left
        exact ⟨u, hu, huw, rfl⟩
    · refine ⟨w, v, ?_, ?_, ?_⟩
      · simpa using heq
      · rw [Set.mem_union]
        right
        simp [Set.pair_comm]
      · unfold slicef_p2
        rw [Set.mem_union]
        right
        rfl

end Kepler.Text

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## 切片基数 -/

private theorem pB_card_slicev (h : localFan_p2 V E FF) (hv : v ∈ V) (hvw : v ≠ w)
    {n : ℕ} (hnw : (rhoNode1_p2 FF)^[n] v = w)
    (hnmin : ∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w))
    (hnlt : n < V.ncard) :
    (slicev_p2 E FF v w).ncard = n + 1 := by
  rw [pB_slicev_image (FF := FF) (v := v) (w := w) (n := n) hvw hnw hnmin]
  rw [Set.InjOn.ncard_image]
  · rw [show {k : ℕ | k < n + 1} = Set.Iio (n + 1) from rfl, Set.ncard_Iio_nat]
  · intro a ha b hb hab
    have ha1 : a < n + 1 := ha
    have hb1 : b < n + 1 := hb
    exact LT_CARD_MONO_LOFA h hv a b ⟨by omega, by omega, hab⟩

private theorem pB_card_slicev_sum (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w) {n n' : ℕ} (hnw : (rhoNode1_p2 FF)^[n] v = w)
    (hn'w : (rhoNode1_p2 FF)^[n'] w = v)
    (hnmin : ∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w))
    (hn'min : ∀ m : ℕ, m < n' → ¬((rhoNode1_p2 FF)^[m] w = v))
    (hnlt : n < V.ncard) (hn'lt : n' < V.ncard) :
    (slicev_p2 E FF v w).ncard + (slicev_p2 E FF w v).ncard = V.ncard + 2 := by
  have h1 : (slicev_p2 E FF v w).ncard = n + 1 :=
    pB_card_slicev h hv hvw hnw hnmin hnlt
  have h2 : (slicev_p2 E FF w v).ncard = n' + 1 :=
    pB_card_slicev h hw (Ne.symm hvw) hn'w hn'min hn'lt
  have hsum := CARD_V_TWO_HAFL_CIRCLE h hv hw hvw n n' hnw hn'w hnlt hn'lt
  omega

end Kepler.Text

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## 加权 azim 和分裂（`ejr_sum` 的 Lean 替代，从 `SUM_INTERIOR_AGL_LEMMA` 推导） -/

end Kepler.Text

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

private theorem pB_FF_finite (h : localFan_p2 V E FF) : FF.Finite := by
  obtain ⟨HS0, -, -, -, -, -, ⟨x0, hx0, hFF0⟩, -⟩ := h
  rw [hFF0]
  exact HS0.darts.finite_toSet.subset (HS0.face_subset_darts hx0)

private theorem pB_face_finite (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hv : v ∈ V) (h : localFan_p2 V E FF) {fv : Set (V3 × V3)}
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) : fv.Finite := by
  have hdart : (v, rhoNode1_p2 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS h).1 v hv
  have he : ({v, rhoNode1_p2 FF v} : Set V3) ∈ E := LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hdart
  have hbase : (v, rhoNode1_p2 FF v) ∈ HS.darts := by
    refine Finset.mem_coe.mp ?_
    rw [hHS.1]
    exact Set.mem_union_left _ (Set.mem_setOf_eq.mpr (Set.mem_union_left _ he))
  rw [hfv]
  exact HS.darts.finite_toSet.subset (HS.face_subset_darts hbase)

/-- `setSum V g = Σ_{i < |V|} g (ρ^[i] v)`（rho 轨道是 `V` 的枚举）。 -/
private theorem pB_setSum_V_orbit (h : localFan_p2 V E FF) (hv : v ∈ V) (g : V3 → ℝ) :
    setSum V g = setSum {i : ℕ | i < V.ncard} (fun i => g ((rhoNode1_p2 FF)^[i] v)) := by
  have hVfin : V.Finite := LOCAL_FAN_FINITE_V h
  have hr := pB_setSum_reindex (A := {i : ℕ | i < V.ncard}) (B := V)
    (Set.finite_Iio V.ncard) hVfin (fun i => (rhoNode1_p2 FF)^[i] v) g
    ⟨fun i _ => LOCAL_FAN_ITER_RHO_NODE_IN_V h hv i,
     fun a ha b hb hab => LT_CARD_MONO_LOFA h hv a b ⟨ha, hb, hab⟩,
     fun u hu => by
       have hmem : u ∈ {(rhoNode1_p2 FF)^[n] v | n < V.ncard} := by
         rw [LOFA_IMP_LT_CARD_SET_V h hv]; exact hu
       obtain ⟨i, hi, hiu⟩ := hmem
       exact ⟨i, hi, hiu⟩⟩
  exact hr.symm

/-- `Σ_{u ∈ B} g u = Σ_{i < |V|, ρ^[i]v ∈ B} g (ρ^[i] v)`（`B ⊆ V`）。 -/
private theorem pB_setSum_orbit_subset (h : localFan_p2 V E FF) (hv : v ∈ V)
    {B : Set V3} (hBV : B ⊆ V) (g : V3 → ℝ) :
    setSum B g = setSum {i : ℕ | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ B}
      (fun i => g ((rhoNode1_p2 FF)^[i] v)) := by
  have hVfin : V.Finite := LOCAL_FAN_FINITE_V h
  have hr := pB_setSum_reindex (A := {i : ℕ | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ B})
    (B := B) (Set.Finite.subset (Set.finite_Iio V.ncard) (fun i hi => hi.1))
    (hVfin.subset hBV) (fun i => (rhoNode1_p2 FF)^[i] v) g
    ⟨fun i hi => hi.2,
     fun a ha b hb hab => LT_CARD_MONO_LOFA h hv a b ⟨ha.1, hb.1, hab⟩,
     fun u hu => by
       have huV : u ∈ V := hBV hu
       have hmem : u ∈ {(rhoNode1_p2 FF)^[n] v | n < V.ncard} := by
         rw [LOFA_IMP_LT_CARD_SET_V h hv]; exact huV
       obtain ⟨i, hi, hiu⟩ := hmem
       exact ⟨i, ⟨hi, hiu ▸ hu⟩, hiu⟩⟩
  exact hr.symm

/-- `Σ_{d ∈ fv} g d.1 * azim d E' = Σ_{u ∈ vPrime fv} g u * interiorAngle1 fv u`。 -/
private theorem pB_setSum_face_fst {E' : Set (Set V3)}
    (hclv : convexLocalFan_p2 (vPrime_p2 V fv) (ePrime_p2 E' fv) fv)
    (hfin : fv.Finite) (g : V3 → ℝ) :
    setSum (vPrime_p2 V fv) (fun u => g u * interiorAngle1_p2 0 fv u) =
      setSum fv (fun e => g e.1 * azimInFan_p2 e (ePrime_p2 E' fv)) := by
  have hbij := LOFA_IMP_BIJ_FF_V hclv.1
  have hBfin : (vPrime_p2 V fv).Finite := by
    rw [← hbij.image_eq]; exact hfin.image Prod.fst
  have hr := pB_setSum_reindex (A := fv) (B := vPrime_p2 V fv) hfin hBfin
    Prod.fst (fun u => g u * interiorAngle1_p2 0 fv u) hbij
  have hcongr : setSum fv (fun x => g x.1 * interiorAngle1_p2 0 fv x.1)
      = setSum fv (fun e => g e.1 * azimInFan_p2 e (ePrime_p2 E' fv)) := by
    refine pB_setSum_congr (s := fv)
      (f := fun x => g x.1 * interiorAngle1_p2 0 fv x.1)
      (g := fun e => g e.1 * azimInFan_p2 e (ePrime_p2 E' fv)) (fun e he => ?_)
    have hd : e.1 ∈ vPrime_p2 V fv := hbij.1 he
    have hdart : e = (e.1, rhoNode1_p2 fv e.1) := (LOCAL_FAN_RHO_NODE_PROS hclv.1).2 e he
    have haz : azimInFan_p2 e (ePrime_p2 E' fv)
        = azimInFan_p2 (e.1, rhoNode1_p2 fv e.1) (ePrime_p2 E' fv) := by rw [hdart]
    have hangle := CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_p9 hclv e.1 hd
    rw [haz, ← hangle]
  exact hr.symm.trans hcongr

/-- FF 面 → vPrime/ePrime 形式（`ejr_sum` 的入口）。 -/
private theorem pB_setSum_FF_fst (h : localFan_p2 V E FF) (hcl : convexLocalFan_p2 V E FF)
    (g : V3 → ℝ) :
    setSum FF (fun e => g e.1 * azimInFan_p2 e E) =
      setSum V (fun u => g u * interiorAngle1_p2 0 FF u) := by
  have hr := pB_setSum_reindex (A := FF) (B := V) (pB_FF_finite h)
    (LOCAL_FAN_FINITE_V h) Prod.fst (fun u => g u * interiorAngle1_p2 0 FF u)
    (LOFA_IMP_BIJ_FF_V h)
  have hcongr : setSum FF (fun e => g e.1 * azimInFan_p2 e E)
      = setSum FF (fun x => g x.1 * interiorAngle1_p2 0 FF x.1) := by
    refine pB_setSum_congr (s := FF)
      (f := fun e => g e.1 * azimInFan_p2 e E)
      (g := fun x => g x.1 * interiorAngle1_p2 0 FF x.1) (fun e he => ?_)
    have hd : e.1 ∈ V := (LOFA_IMP_BIJ_FF_V h).1 he
    have hdart : e = (e.1, rhoNode1_p2 FF e.1) := (LOCAL_FAN_RHO_NODE_PROS h).2 e he
    have haz : azimInFan_p2 e E = azimInFan_p2 (e.1, rhoNode1_p2 FF e.1) E := by rw [hdart]
    have hangle := CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_p9 hcl e.1 hd
    rw [haz, ← hangle]
  exact hcongr.trans hr

/-- 加权 azim 和分裂（`ejr_sum` 的 Lean 替代）。 -/
private theorem pB_sum_azim
    (h : localFan_p2 V E FF) (hcl : convexLocalFan_p2 V E FF)
    (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    {fv fw : Set (V3 × V3)}
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w))
    (hclv : convexLocalFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv)
    (hclw : convexLocalFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw)
    (hfinv : fv.Finite) (hfinw : fw.Finite)
    (g : V3 → ℝ) :
    setSum FF (fun e => g e.1 * azimInFan_p2 e E) =
      setSum fv (fun e => g e.1 * azimInFan_p2 e (ePrime_p2 (E ∪ {{v, w}}) fv)) +
        setSum fw (fun e => g e.1 * azimInFan_p2 e (ePrime_p2 (E ∪ {{w, v}}) fw)) := by
  obtain ⟨-, -, hangle⟩ := EJRCFJD hcl hv hw hvw hsub HS hHS hfv hfw
  have h3 := hangle (fun i => g ((rhoNode1_p2 FF)^[i] v))
  have h4v := pB_setSum_orbit_subset h hv (V_PRIME_SUBSET_V V fv)
    (fun u => g u * interiorAngle1_p2 0 fv u)
  have h4w := pB_setSum_orbit_subset h hv (V_PRIME_SUBSET_V V fw)
    (fun u => g u * interiorAngle1_p2 0 fw u)
  have h5v := pB_setSum_face_fst (E' := E ∪ {{v, w}}) hclv hfinv g
  have h5w := pB_setSum_face_fst (E' := E ∪ {{w, v}}) hclw hfinw g
  rw [pB_setSum_FF_fst h hcl g, pB_setSum_V_orbit h hv
    (fun u => g u * interiorAngle1_p2 0 FF u), h3, ← h4v, ← h4w, ← h5v, ← h5w]

end Kepler.Text

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- `Collinear3` 后两位互换。 -/
private theorem pB_collinear3_swap {a b c : V3} (h : Collinear3 a b c) : Collinear3 a c b := by
  have hset : ({a, b, c} : Set V3) = {a, c, b} := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  simpa [Collinear3, hset] using h

/-- `affLt {0}{u}` 的点与 `0,u` 共线（`Affsign` 系数和 = 1 即直线参数化）。 -/
private theorem pB_affLt_collinear {u y : V3} (hu : u ≠ 0)
    (hy : y ∈ affLt ({0} : Set V3) {u}) : Collinear3 0 u y := by
  have hspan : y ∈ (affineSpan ℝ ({0, u} : Set V3) : Set V3) :=
    AFF_LT_SUBSET_AFF11_p37 (by simpa using hu.symm) hy
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hspan
  refine (collinear3_iff_smul hu).mpr ⟨r, ?_⟩
  rw [← hr, AffineMap.lineMap_apply]
  simp

/-- generic 从 `(V,E)` 传到切片扇 `(slicev, slicee)`（HOL `ejr_generic`）。 -/
private theorem pB_generic_slice
    (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (hg : generic_p2 V E) :
    generic_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) := by
  have h : localFan_p2 V E FF := hcl.1
  have hfan : FAN 0 V E := (CVLF_LF_F hcl).2
  intro a b u hab hu
  have huV : u ∈ V := by
    unfold slicev_p2 at hu
    obtain ⟨k, -, rfl⟩ := hu
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V h hv k
  have hu0 : u ≠ 0 := fun hh => hfan.2.2.2.1 (hh ▸ huV)
  have hv0 : v ≠ 0 := fun hh => hfan.2.2.2.1 (hh ▸ hv)
  have hw0 : w ≠ 0 := fun hh => hfan.2.2.2.1 (hh ▸ hw)
  unfold slicee_p2 at hab
  rw [Set.mem_union] at hab
  rcases hab with ⟨u', hu', hu'w, heq⟩ | hchord
  · have hu'V : u' ∈ V := by
      unfold slicev_p2 at hu'
      obtain ⟨k, -, rfl⟩ := hu'
      exact LOCAL_FAN_ITER_RHO_NODE_IN_V h hv k
    have hpred : ({u', rhoNode1_p2 FF u'} : Set V3) ∈ E :=
      LOCAL_FAN_IN_FF_IN_ORD_PAIRS h ((LOCAL_FAN_RHO_NODE_PROS h).1 u' hu'V)
    rw [heq]
    exact hg u' (rhoNode1_p2 FF u') u hpred huV
  · have habw : ({a, b} : Set V3) = {w, v} := by simpa using hchord
    rw [habw]
    have hwVv : w ∈ V \ ({v} : Set V3) := by
      rw [Set.mem_sdiff]; exact ⟨hw, by simpa using hvw.symm⟩
    have hnc : ¬ Collinear3 (0 : V3) v w :=
      hcol v w (Set.mem_insert _ _) hwVv
    have hnc' : ¬ Collinear3 (0 : V3) w v := fun h => hnc (pB_collinear3_swap h)
    have hdecomp := aff_ge_eq_aff_gt_union_aff_ge (x := (0 : V3)) (v := w) (w := v) hnc'
    have h1 : affGt ({0} : Set V3) {v, w} ∩ affLt ({0} : Set V3) {u} = ∅ := by
      have hdart : (u, rhoNode1_p2 FF u) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS h).1 u huV
      have hwedge := hsub (u, rhoNode1_p2 FF u) hdart
      have hcard : 1 < (EE_p2 u E).ncard := by
        rw [LOFA_CARD_EE_V_1 h huV]; norm_num
      unfold wedgeInFanGt_p2 at hwedge
      rw [if_pos hcard] at hwedge
      refine Set.eq_empty_iff_forall_notMem.mpr (fun y hy => ?_)
      exact (hwedge hy.1).1 (pB_affLt_collinear hu0 hy.2)
    have h2 : affGe ({0} : Set V3) {v} ∩ affLt ({0} : Set V3) {u} = ∅ := by
      by_cases huv : u = v
      · subst huv; exact aff_ge_INTER_aff_lt hu0
      · by_contra hne
        have hc := (AFF_GE_INTER_AFF_LT_IMP_NOT_EQ_COL (u := u) (v := v) hv0 hu0 hne).2
        have huVv : u ∈ V \ ({v} : Set V3) := by
          rw [Set.mem_sdiff]; exact ⟨huV, huv⟩
        exact hcol v u (Set.mem_insert _ _) huVv (pB_collinear3_swap hc)
    have h3 : affGe ({0} : Set V3) {w} ∩ affLt ({0} : Set V3) {u} = ∅ := by
      by_cases huw : u = w
      · subst huw; exact aff_ge_INTER_aff_lt hu0
      · by_contra hne
        have hc := (AFF_GE_INTER_AFF_LT_IMP_NOT_EQ_COL (u := u) (v := w) hw0 hu0 hne).2
        have huVw : u ∈ V \ ({w} : Set V3) := by
          rw [Set.mem_sdiff]; exact ⟨huV, huw⟩
        exact hcol w u (Set.mem_insert_of_mem _ (Set.mem_singleton _)) huVw
          (pB_collinear3_swap hc)
    have h1' : affGt ({0} : Set V3) {w, v} ∩ affLt ({0} : Set V3) {u} = ∅ := by
      simpa [Set.pair_comm w v] using h1
    rw [hdecomp, Set.union_inter_distrib_right, Set.union_inter_distrib_right, h1', h3, h2]
    simp

end Kepler.Text

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- `setSum` 的逐项减常数。 -/
private theorem pB_setSum_sub_const {α : Type*} {s : Set α} (hs : s.Finite)
    (f : α → ℝ) (c : ℝ) : setSum s (fun e => f e - c) = setSum s f - c * s.ncard := by
  rw [setSum, dif_pos hs, setSum, dif_pos hs, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Set.ncard_eq_toFinset_card s hs, mul_comm]

/-- `v ∈ affGt {0}{v}`（`v ≠ 0`）。 -/
private theorem pB_mem_affGt_self {v : V3} (_hv : v ≠ 0) :
    v ∈ affGt ({0} : Set V3) {v} := by
  have hfin : (({0} : Set V3) ∪ {v}).Finite :=
    (Set.finite_singleton 0).union (Set.finite_singleton v)
  have hset : hfin.toFinset = ({0, v} : Finset V3) := by
    ext q
    simp only [Set.Finite.mem_toFinset, Set.mem_union,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  unfold affGt Affsign
  refine ⟨fun w => if w = v then 1 else 0, hfin, ?_, ?_, ?_⟩
  · rw [hset]
    simp
  · intro w hw
    have hwv : w = v := by simpa using hw
    simp [hwv]
  · rw [hset]
    simp

/-- **wave B 目标**：`EJRCFJD_ALT2`（HOL `localization.hl:1367-1501`）真证。 -/
theorem pB_EJRCFJD_ALT2
    (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
      ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) :
    convexLocalFan_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) (slicef_p2 E FF v w) ∧
      convexLocalFan_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v) (slicef_p2 E FF w v) ∧
      tauFun_p2 V E FF ≥
        tauFun_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) (slicef_p2 E FF v w) +
          tauFun_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v) (slicef_p2 E FF w v) ∧
      solLocal_p2 E FF =
        solLocal_p2 (slicee_p2 E FF v w) (slicef_p2 E FF v w) +
          solLocal_p2 (slicee_p2 E FF w v) (slicef_p2 E FF w v) ∧
      (slicev_p2 E FF v w).ncard < V.ncard ∧ (slicev_p2 E FF w v).ncard < V.ncard ∧
      (generic_p2 V E → generic_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) ∧
        generic_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v)) := by
  classical
  have h : localFan_p2 V E FF := hcl.1
  have hcol' : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3) := by
    intro z t hz ht
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at ht
    exact hcol z t hz ht.1 (Ne.symm ht.2)
  have hvw : v ≠ w := by
    intro hwv
    have hdart : (v, rhoNode1_p2 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS h).1 v hv
    have hwedge := hsub (v, rhoNode1_p2 FF v) hdart
    have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
    have hv0 : v ≠ 0 := fun hh => h0V (hh ▸ hv)
    have hcard : 1 < (EE_p2 v E).ncard := by
      rw [LOFA_CARD_EE_V_1 h hv]; norm_num
    have hmem : v ∈ wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E := by
      apply hwedge
      rw [show ({v, w} : Set V3) = {v} from by rw [hwv]; simp]
      exact pB_mem_affGt_self hv0
    unfold wedgeInFanGt_p2 at hmem
    rw [if_pos hcard] at hmem
    exact hmem.1 (by
      have hcol3 : Collinear3 0 v v := collinear3_pair_right rfl
      exact hcol3)
  have hfanAug : FAN 0 V (E ∪ {{v, w}}) := PROVE_SLICING_FAN h hv hw hvw hcol' hsub
  obtain ⟨HS, hHS⟩ : ∃ HS : Hypermap (V3 × V3), IsHyp_p2 0 V (E ∪ {{v, w}}) HS := by
    obtain ⟨H, hd, he, hn, hf⟩ := HYP_LEMMA (x := (0 : V3)) hfanAug
    exact ⟨H, hd, he, hn, hf⟩
  let fv : Set (V3 × V3) := HS.face (v, rhoNode1_p2 FF v)
  let fw : Set (V3 × V3) := HS.face (w, rhoNode1_p2 FF w)
  obtain ⟨hclv, hclw, hangle⟩ := EJRCFJD (fv := fv) (fw := fw) hcl hv hw hvw hsub HS hHS rfl rfl
  obtain ⟨n, hnlt, hnw, hnmin⟩ := POINT_PRESENTED_IN_RHOND1 h hv hw
  obtain ⟨n', hn'lt, hn'w, hn'min⟩ := POINT_PRESENTED_IN_RHOND1 h hw hv
  have hsf : fv = slicef_p2 E FF v w := pB_face_eq_slicef (fv := fv) h hv hw hvw hcol' hsub HS hHS rfl hnlt hnw hnmin
  have hHSw : IsHyp_p2 0 V (E ∪ {{w, v}}) HS := by
    rw [show (E ∪ {{w, v}}) = (E ∪ {{v, w}}) from by rw [Set.pair_comm]]
    exact hHS
  have hsf' : fw = slicef_p2 E FF w v :=
    pB_face_eq_slicef (fv := fw) h hw hv (Ne.symm hvw) (by
      intro z t hz ht
      rw [show ({w, v} : Set V3) = {v, w} from Set.pair_comm w v] at hz
      exact hcol' z t hz ht) (by
      intro x hx
      rw [show ({w, v} : Set V3) = {v, w} from Set.pair_comm w v]
      exact hsub x hx) HS hHSw rfl hn'lt hn'w hn'min
  have hvp : vPrime_p2 V fv = slicev_p2 E FF v w := pB_vprime_eq_slicev (fv := fv) h hv hvw hnw hnmin hsf
  have hwp : vPrime_p2 V fw = slicev_p2 E FF w v :=
    pB_vprime_eq_slicev (fv := fw) h hw (Ne.symm hvw) hn'w hn'min hsf'
  have hep : ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p2 E FF v w :=
    pB_eprime_eq_slicee (fv := fv) h hv hvw hnw hnmin hsf
  have hep' : ePrime_p2 (E ∪ {{w, v}}) fw = slicee_p2 E FF w v :=
    pB_eprime_eq_slicee (fv := fw) h hw (Ne.symm hvw) hn'w hn'min hsf'
  have hfinv : fv.Finite := pB_face_finite (fv := fv) hHS hv h rfl
  have hfinw : fw.Finite := pB_face_finite (fv := fw) hHSw hw h rfl
  have hcardsum := pB_card_slicev_sum h hv hw hvw hnw hn'w hnmin hn'min hnlt hn'lt
  have hfvc : fv.ncard = (slicev_p2 E FF v w).ncard := by
    have hbij := LOFA_IMP_BIJ_FF_V hclv.1
    rw [← hvp, ← hbij.image_eq, Set.InjOn.ncard_image hbij.injOn]
  have hfwc : fw.ncard = (slicev_p2 E FF w v).ncard := by
    have hbij := LOFA_IMP_BIJ_FF_V hclw.1
    rw [← hwp, ← hbij.image_eq, Set.InjOn.ncard_image hbij.injOn]
  have hfacecard : fv.ncard + fw.ncard = FF.ncard + 2 := by
    rw [hfvc, hfwc, LOFA_IMP_CARD_FF_V_EQ h]; exact hcardsum
  have hltv : (slicev_p2 E FF v w).ncard < V.ncard := by
    have h3 : 3 ≤ (slicev_p2 E FF w v).ncard := by
      rw [← hwp]; exact CARD_VERTEX_GE_3_LOCAL_FAN_p9 hclw
    omega
  have hltw : (slicev_p2 E FF w v).ncard < V.ncard := by
    have h3 : 3 ≤ (slicev_p2 E FF v w).ncard := by
      rw [← hvp]; exact CARD_VERTEX_GE_3_LOCAL_FAN_p9 hclv
    omega
  have htau : tauFun_p2 V E FF ≥
      tauFun_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) (slicef_p2 E FF v w) +
        tauFun_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v) (slicef_p2 E FF w v) := by
    have hsumR := pB_sum_azim (fv := fv) (fw := fw) h hcl hv hw hvw hsub HS hHS rfl rfl hclv hclw hfinv hfinw
      (fun u : V3 => rhoFun_p2 ‖u‖)
    have hsumR' : setSum FF (fun e => rhoFun_p2 ‖e.1‖ * azimInFan_p2 e E)
        = setSum (slicef_p2 E FF v w)
            (fun e => rhoFun_p2 ‖e.1‖ * azimInFan_p2 e (slicee_p2 E FF v w)) +
          setSum (slicef_p2 E FF w v)
            (fun e => rhoFun_p2 ‖e.1‖ * azimInFan_p2 e (slicee_p2 E FF w v)) := by
      rw [hsumR]
      rw [hep, hsf, hep', hsf']
    unfold tauFun_p2
    rw [hsumR']
    have hcardR : ((FF.ncard - 2 : ℕ) : ℝ) =
        (((slicef_p2 E FF v w).ncard - 2 : ℕ) : ℝ) +
          (((slicef_p2 E FF w v).ncard - 2 : ℕ) : ℝ) := by
      rw [← hsf, ← hsf']
      have h2v : 2 ≤ fv.ncard := by omega
      have h2w : 2 ≤ fw.ncard := by omega
      have hnat : FF.ncard - 2 = (fv.ncard - 2) + (fw.ncard - 2) := by omega
      rw [hnat]; push_cast; ring
    rw [hcardR]; ring_nf; linarith
  have hsol : solLocal_p2 E FF =
      solLocal_p2 (slicee_p2 E FF v w) (slicef_p2 E FF v w) +
        solLocal_p2 (slicee_p2 E FF w v) (slicef_p2 E FF w v) := by
    have hsum1 := pB_sum_azim (fv := fv) (fw := fw) h hcl hv hw hvw hsub HS hHS rfl rfl hclv hclw hfinv hfinw
      (fun _ => (1 : ℝ))
    have hsum1' : setSum FF (fun e => azimInFan_p2 e E)
        = setSum (slicef_p2 E FF v w) (fun e => azimInFan_p2 e (slicee_p2 E FF v w)) +
          setSum (slicef_p2 E FF w v) (fun e => azimInFan_p2 e (slicee_p2 E FF w v)) := by
      have h1 := hsum1
      simp only [one_mul] at h1
      rw [h1]
      rw [hep, hsf, hep', hsf']
    unfold solLocal_p2
    rw [← hsf, ← hep, ← hsf', ← hep']
    rw [pB_setSum_sub_const (pB_FF_finite h) _ Real.pi,
      pB_setSum_sub_const hfinv _ Real.pi, pB_setSum_sub_const hfinw _ Real.pi]
    have h1 := hsum1
    simp only [one_mul] at h1
    rw [h1]
    have hcast : (FF.ncard : ℝ) = (fv.ncard : ℝ) + (fw.ncard : ℝ) - 2 := by
      have h' : (fv.ncard : ℝ) + (fw.ncard : ℝ) = (FF.ncard : ℝ) + 2 := by
        exact_mod_cast hfacecard
      linarith
    rw [hcast]
    ring
  refine ⟨?_, ?_, htau, hsol, hltv, hltw, ?_⟩
  · rw [← hvp, ← hep, ← hsf]; exact hclv
  · rw [← hwp, ← hep', ← hsf']; exact hclw
  · intro hg
    exact ⟨pB_generic_slice hcl hv hw hvw hcol' hsub hg,
      pB_generic_slice hcl hw hv (Ne.symm hvw) (by
        intro z t hz ht
        rw [show ({w, v} : Set V3) = {v, w} from Set.pair_comm w v] at hz
        exact hcol' z t hz ht) (by
        intro x hx
        rw [show ({w, v} : Set V3) = {v, w} from Set.pair_comm w v]
        exact hsub x hx) hg⟩

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pB_EJRCFJD_ALT2
#print axioms Kepler.Text.pB_face_eq_slicef
#print axioms Kepler.Text.pB_sum_azim
#print axioms Kepler.Text.pB_generic_slice
