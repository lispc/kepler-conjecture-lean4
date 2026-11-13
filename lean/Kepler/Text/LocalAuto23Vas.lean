/-
LocalAuto23Vas — the VASYYAU / JOTSWIX cluster, moved verbatim out of
`LocalAuto23` (Section A, donor lines 427-646 at HEAD 815775f6).

DEF-FIX charter: `docs/def-fix-charters/vas-cluster-move/README.md`
(user-approved 2026-11-13, 21:14; V3 execution).

Why a new sink module: `LocalAuto23` cannot import `LocalAuto21` or
`LocalAuto22` (both of them import `LocalAuto23`, so a back-edge would
create an import cycle), yet the VASYYAU giants (`NEHXMWH` / `BZQNDMN` /
`JOTSWIX` / `LEMMA_PWE1..4`) need the azim/deform kit of `LocalAuto21`
(`azim_assumption_reduction_p21` / `MMs_minimize_tau_fun_p21` /
`WNWSHJT_ALT_p21`) and `LocalAuto22` (`INTERIOR_ANGLE1_AZIM_p22`). This
module is a DAG sink: it imports only upstream modules and nothing imports
it yet, so the R3 deadlock is lifted without touching any existing
statement.

Content discipline: the 14 declarations below are pasted byte-for-byte
from the donor block (2 proved + 12 `sorry`); no statement, proof body,
or `sorry` was edited. The donor keeps its Section 0 substrate, the
`taum`/`LFLACKU`/`JEJTVGB` kit and Section B unchanged.
└──
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto21
import Kepler.Text.LocalAuto22
import Kepler.Text.LocalAuto23
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-- HOL `MOD_4_CASES` (JOTSWIX.hl:454). -/
theorem MOD_4_CASES_p23 (j p : ℕ) (hj : j < 4) :
    j = (p + 0) % 4 ∨ j = (p + 1) % 4 ∨ j = (p + 2) % 4 ∨ j = (p + 3) % 4 := by
  omega

/-- HOL `ab4_assumption_reduction` (JOTSWIX.hl:476): a k=4 deformation
fixing all but `v p` propagates the a/b endpoint bounds. NEEDS: the full
HOL proof (JOTSWIX.hl:487-668). -/
theorem ab4_assumption_reduction_p23 (s : ScsV39) (p : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s v)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j < dist (v i) (v j) ∧ 4 * h0 < s.b i j)
    (hdef : Deformation f (Set.range v) (-e) e) (he : 0 < e)
    (hfix : ∀ w t, w ≠ v p → f w t = w)
    (hdist : ∀ t, |t| < e → dist (v (p + 3)) (f (v p) t) = dist (v (p + 3)) (v p))
    (hab : s.a p (p + 1) < dist (v p) (v (p + 1)) ∧
      dist (v p) (v (p + 1)) < s.b p (p + 1)) :
    (∀ i j, ∃ e1 : ℝ, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
        ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t))) ∧
    (∀ i j, ∃ e2 : ℝ, 0 < e2 ∧ (dist (v i) (v j) = s.b i j →
        ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j)) := by
  -- ── substrate: periodicity + injectivity of `v` on one period ──
  have hinj : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j := BBs_inj_p21 s v 4 hs hk hBB
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpb, -, hsym, hch, ha0, -, -, -, -, -, -⟩ := hs
  obtain ⟨hann, hperv, hdistBB, -⟩ := hBB
  have hperv4 : Periodic v 4 := hk ▸ hperv
  have hpa4 : Periodic2 s.a 4 := hk ▸ hpa
  have hpb4 : Periodic2 s.b 4 := hk ▸ hpb
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  have hAred : ∀ i j : ℕ, s.a i j = s.a (i % 4) (j % 4) := fun i j => periodic2_MOD_p21 h4 hpa4
  have hBred : ∀ i j : ℕ, s.b i j = s.b (i % 4) (j % 4) := fun i j => periodic2_MOD_p21 h4 hpb4
  have hvred : ∀ i : ℕ, v (i % 4) = v i := fun i => periodic_mod_eq_p23 hperv4 i
  have hAcong : ∀ i j k l : ℕ, i % 4 = k % 4 → j % 4 = l % 4 → s.a i j = s.a k l := by
    intro i j k l hi hj
    rw [hAred i j, hAred k l, hi, hj]
  have hBcong : ∀ i j k l : ℕ, i % 4 = k % 4 → j % 4 = l % 4 → s.b i j = s.b k l := by
    intro i j k l hi hj
    rw [hBred i j, hBred k l, hi, hj]
  have hmodv : ∀ i : ℕ, v i = v p → i % 4 = p % 4 := by
    intro i hi
    exact hinj (i % 4) (p % 4) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      (by rw [hvred i, hvred p]; exact hi)
  have hne_vp : ∀ i : ℕ, i % 4 ≠ p % 4 → v i ≠ v p :=
    fun i hne hc => hne (hmodv i hc)
  -- every vertex of the annulus has norm ≤ `2 * h0`
  have hnorm : ∀ i : ℕ, ‖v i‖ ≤ 2 * h0 := by
    intro i
    have hx : v i ∈ ballAnnulus := hann (Set.mem_range_self i)
    unfold ballAnnulus at hx
    have h1 : dist (v i) 0 ≤ 2 * h0 := Metric.mem_closedBall.mp hx.1
    rwa [dist_eq_norm, sub_zero] at h1
  have htri : dist (v p) (v (p + 2)) ≤ 4 * h0 := by
    have h1 : dist (v p) (v (p + 2)) ≤ dist (v p) 0 + dist 0 (v (p + 2)) :=
      dist_triangle (v p) 0 (v (p + 2))
    have h2 : dist (v p) 0 = ‖v p‖ := by rw [dist_eq_norm, sub_zero]
    have h3 : dist 0 (v (p + 2)) = ‖v (p + 2)‖ := by rw [dist_eq_norm, zero_sub, norm_neg]
    rw [h2, h3] at h1
    linarith [hnorm p, hnorm (p + 2)]
  have hdiag2 : scsDiag 4 p (p + 2) := by
    unfold scsDiag
    exact ⟨by intro hc; omega, by intro hc; omega, by intro hc; omega⟩
  -- ── row lemma at `p`, `a` side (HOL `scs_a_v39` block) ──
  have hrowA : ∀ j : ℕ, j < 4 → ∃ e1 : ℝ, 0 < e1 ∧ (s.a p j = dist (v p) (v j) →
      ∀ t : ℝ, |t| < e1 → s.a p j ≤ dist (f (v p) t) (f (v j) t)) := by
    intro j hj
    rcases MOD_4_CASES_p23 j p hj with h | h | h | h
    · -- `j ≡ p`: both slots coincide, `s.a p p = 0` and the distance is `0`
      refine ⟨1, by norm_num, fun _ t _ => ?_⟩
      have hjeq : j % 4 = p % 4 := by rw [h, Nat.mod_mod]; omega
      have hjv : v j = v p := by rw [← hvred j, hjeq]; exact hvred p
      have hz : s.a p j = s.a p p := hAcong p j p p rfl hjeq
      rw [hz, ha0 p, hjv, dist_self]
    · -- `j ≡ p + 1`: `hab.1` makes the `a` hypothesis impossible
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 1) % 4 := by rw [h, Nat.mod_mod]
      have ha : s.a p j = s.a p (p + 1) := hAcong p j p (p + 1) rfl hjmod
      have hjv : v j = v (p + 1) := by rw [h]; exact hvred (p + 1)
      have he1 : s.a p (p + 1) = dist (v p) (v (p + 1)) := by
        rw [← ha, ← hjv]; exact hhyp
      exact absurd he1 (ne_of_lt hab.1)
    · -- `j ≡ p + 2`: the (p,p+2) diagonal, `hdg` makes it impossible
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 2) % 4 := by rw [h, Nat.mod_mod]
      have ha : s.a p j = s.a p (p + 2) := hAcong p j p (p + 2) rfl hjmod
      have hjv : v j = v (p + 2) := by rw [h]; exact hvred (p + 2)
      have he1 : s.a p (p + 2) = dist (v p) (v (p + 2)) := by
        rw [← ha, ← hjv]; exact hhyp
      exact absurd he1 (ne_of_lt (hdg p (p + 2) hdiag2).1)
    · -- `j ≡ p + 3`: the one deformed slot; the `hdist` invariance closes it
      refine ⟨e, he, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 3) % 4 := by rw [h, Nat.mod_mod]
      have ha : s.a p j = s.a p (p + 3) := hAcong p j p (p + 3) rfl hjmod
      have hjv : v j = v (p + 3) := by rw [h]; exact hvred (p + 3)
      have hne3 : v (p + 3) ≠ v p := hne_vp (p + 3) (by omega)
      rw [ha, hjv, hfix (v (p + 3)) t hne3]
      have hd3 : dist (f (v p) t) (v (p + 3)) = dist (v p) (v (p + 3)) :=
        (dist_comm _ _).trans ((hdist t ht).trans (dist_comm _ _))
      rw [hd3]
      exact (hdistBB p (p + 3)).1
  -- ── row lemma at `p`, `b` side (HOL `now the b end` block) ──
  have hrowB : ∀ j : ℕ, j < 4 → ∃ e2 : ℝ, 0 < e2 ∧ (dist (v p) (v j) = s.b p j →
      ∀ t : ℝ, |t| < e2 → dist (f (v p) t) (f (v j) t) ≤ s.b p j) := by
    intro j hj
    rcases MOD_4_CASES_p23 j p hj with h | h | h | h
    · -- `j ≡ p`: both slots coincide; `0 ≤ s.b p p` from the `a ≤ b` chain
      refine ⟨1, by norm_num, fun _ t _ => ?_⟩
      have hjeq : j % 4 = p % 4 := by rw [h, Nat.mod_mod]; omega
      have hjv : v j = v p := by rw [← hvred j, hjeq]; exact hvred p
      have hz : s.a p j = s.a p p := hAcong p j p p rfl hjeq
      have hle : s.a p j ≤ s.b p j :=
        (hch p j).1.trans ((hch p j).2.1.trans (hch p j).2.2)
      rw [hz, ha0 p] at hle
      rw [hjv, dist_self]
      exact hle
    · -- `j ≡ p + 1`: `hab.2` makes the `b` hypothesis impossible
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 1) % 4 := by rw [h, Nat.mod_mod]
      have hb : s.b p j = s.b p (p + 1) := hBcong p j p (p + 1) rfl hjmod
      have hjv : v j = v (p + 1) := by rw [h]; exact hvred (p + 1)
      have he1 : dist (v p) (v (p + 1)) = s.b p (p + 1) := by
        rw [← hb, ← hjv]; exact hhyp
      exact absurd he1 (ne_of_lt hab.2)
    · -- `j ≡ p + 2`: the diagonal is shorter than `4 * h0 < s.b p (p+2)`
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 2) % 4 := by rw [h, Nat.mod_mod]
      have hb : s.b p j = s.b p (p + 2) := hBcong p j p (p + 2) rfl hjmod
      have hjv : v j = v (p + 2) := by rw [h]; exact hvred (p + 2)
      have he1 : dist (v p) (v (p + 2)) = s.b p (p + 2) := by
        rw [← hb, ← hjv]; exact hhyp
      exact absurd he1 (ne_of_lt (lt_of_le_of_lt htri (hdg p (p + 2) hdiag2).2))
    · -- `j ≡ p + 3`: same invariance as the `a` side
      refine ⟨e, he, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 3) % 4 := by rw [h, Nat.mod_mod]
      have hb : s.b p j = s.b p (p + 3) := hBcong p j p (p + 3) rfl hjmod
      have hjv : v j = v (p + 3) := by rw [h]; exact hvred (p + 3)
      have hne3 : v (p + 3) ≠ v p := hne_vp (p + 3) (by omega)
      rw [hb, hjv, hfix (v (p + 3)) t hne3]
      have hd3 : dist (f (v p) t) (v (p + 3)) = dist (v p) (v (p + 3)) :=
        (dist_comm _ _).trans ((hdist t ht).trans (dist_comm _ _))
      rw [hd3]
      exact (hdistBB p (p + 3)).2
  -- ── lift the row lemmas off the `% 4`-class of `j` ──
  have hArow : ∀ j : ℕ, ∃ e1 : ℝ, 0 < e1 ∧ (s.a p j = dist (v p) (v j) →
      ∀ t : ℝ, |t| < e1 → s.a p j ≤ dist (f (v p) t) (f (v j) t)) := by
    intro j
    obtain ⟨e1, he1, hall⟩ := hrowA (j % 4) (Nat.mod_lt _ (by norm_num))
    refine ⟨e1, he1, fun hhyp t ht => ?_⟩
    have hap : s.a p (j % 4) = s.a p j := hAcong p (j % 4) p j rfl (by omega)
    have hvj : v (j % 4) = v j := hvred j
    rw [← hap, ← hvj] at hhyp ⊢
    exact hall hhyp t ht
  have hBrow : ∀ j : ℕ, ∃ e2 : ℝ, 0 < e2 ∧ (dist (v p) (v j) = s.b p j →
      ∀ t : ℝ, |t| < e2 → dist (f (v p) t) (f (v j) t) ≤ s.b p j) := by
    intro j
    obtain ⟨e2, he2, hall⟩ := hrowB (j % 4) (Nat.mod_lt _ (by norm_num))
    refine ⟨e2, he2, fun hhyp t ht => ?_⟩
    have hbp : s.b p (j % 4) = s.b p j := hBcong p (j % 4) p j rfl (by omega)
    have hvj : v (j % 4) = v j := hvred j
    rw [← hbp, ← hvj] at hhyp ⊢
    exact hall hhyp t ht
  -- ── assemble: HOL's four-way `MOD_4_CASES` split on `(i,j)` ──
  refine ⟨?_, ?_⟩
  · intro i j
    by_cases hA : i % 4 = p % 4
    · -- `i` sits on the deformed vertex: transport the row lemma at `p`
      obtain ⟨e1, he1, hall⟩ := hArow j
      refine ⟨e1, he1, fun hhyp t ht => ?_⟩
      have hvi : v i = v p := by rw [← hvred i, hA]; exact hvred p
      have haij : s.a i j = s.a p j := hAcong i j p j hA rfl
      rw [haij, hvi] at hhyp ⊢
      exact hall hhyp t ht
    · by_cases hB : j % 4 = p % 4
      · -- `j` sits on the deformed vertex: row lemma at `p` with `DIST_SYM`
        obtain ⟨e1, he1, hall⟩ := hArow i
        refine ⟨e1, he1, fun hhyp t ht => ?_⟩
        have hvj : v j = v p := by rw [← hvred j, hB]; exact hvred p
        have haij : s.a i j = s.a p i := (hAcong i j i p rfl hB).trans (hsym i p).1
        have hdi : dist (v i) (v j) = dist (v p) (v i) := by rw [hvj, dist_comm]
        have hdf : dist (f (v i) t) (f (v j) t) = dist (f (v p) t) (f (v i) t) := by
          rw [hvj, dist_comm]
        rw [haij, hdi] at hhyp
        rw [haij, hdf]
        exact hall hhyp t ht
      · -- neither slot is deformed: `f` fixes both, `BBsV39` gives the bound
        refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
        have hfi : f (v i) t = v i := hfix _ t (hne_vp i hA)
        have hfj : f (v j) t = v j := hfix _ t (hne_vp j hB)
        rw [hfi, hfj]
        exact (hdistBB i j).1
  · intro i j
    by_cases hA : i % 4 = p % 4
    · obtain ⟨e2, he2, hall⟩ := hBrow j
      refine ⟨e2, he2, fun hhyp t ht => ?_⟩
      have hvi : v i = v p := by rw [← hvred i, hA]; exact hvred p
      have hbij : s.b i j = s.b p j := hBcong i j p j hA rfl
      rw [hbij, hvi] at hhyp ⊢
      exact hall hhyp t ht
    · by_cases hB : j % 4 = p % 4
      · obtain ⟨e2, he2, hall⟩ := hBrow i
        refine ⟨e2, he2, fun hhyp t ht => ?_⟩
        have hvj : v j = v p := by rw [← hvred j, hB]; exact hvred p
        have hbij : s.b i j = s.b p i := (hBcong i j i p rfl hB).trans (hsym i p).2.2.2.1
        have hdi : dist (v i) (v j) = dist (v p) (v i) := by rw [hvj, dist_comm]
        have hdf : dist (f (v i) t) (f (v j) t) = dist (f (v p) t) (f (v i) t) := by
          rw [hvj, dist_comm]
        rw [hbij, hdi] at hhyp
        rw [hbij, hdf]
        exact hall hhyp t ht
      · refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
        have hfi : f (v i) t = v i := hfix _ t (hne_vp i hA)
        have hfj : f (v j) t = v j := hfix _ t (hne_vp j hB)
        rw [hfi, hfj]
        exact (hdistBB i j).2

/-- HOL `PERIODIC_INJ_MOD` (JOTSWIX.hl:668). -/
theorem PERIODIC_INJ_MOD_p23 {α : Sort u} (v : ℕ → α) (k : ℕ) (hk : k ≠ 0)
    (hp : Periodic v k) (hinj : ∀ i j, i < k → j < k → v i = v j → i = j)
    (i j : ℕ) : (v i = v j ↔ i % k = j % k) := by
  constructor
  · intro hij
    apply hinj _ _ (Nat.mod_lt _ (by omega : 0 < k)) (Nat.mod_lt _ (by omega : 0 < k))
    rw [periodic_mod_eq_p23 hp i, periodic_mod_eq_p23 hp j, hij]
  · intro hmod
    rw [← periodic_mod_eq_p23 hp i, ← periodic_mod_eq_p23 hp j, hmod]

/-- Shared row assembly for the `ab4_assumption_reduction` family: two
one-row endpoint lemmas at a single vertex `q` (both sides, `j < 4`) are
lifted to all index pairs.  This is the `periodic2_mod_reduce` +
`MOD_4_CASES` assembly of HOL `ab4_assumption_reduction` (JOTSWIX.hl:487-668),
parameterised over the moved vertex `q` so that the
`ab4_assumption_reduction2` (`q = p`) and `_sym` (`q = p+1`) twins share it. -/
private theorem ab4_assemble_row_p23 (s : ScsV39) (q : ℕ) (f : V3 → ℝ → V3) (v : ℕ → V3)
    (hpa4 : Periodic2 s.a 4) (hpb4 : Periodic2 s.b 4)
    (hvred : ∀ i : ℕ, v (i % 4) = v i)
    (hsym : ∀ i j, s.a i j = s.a j i ∧ s.am i j = s.am j i ∧
      s.bm i j = s.bm j i ∧ s.b i j = s.b j i ∧ s.J i j = s.J j i)
    (hBBd : ∀ i j, s.a i j ≤ dist (v i) (v j) ∧ dist (v i) (v j) ≤ s.b i j)
    (hne : ∀ i j : ℕ, i % 4 ≠ j % 4 → v i ≠ v j)
    (hfix : ∀ w t, w ≠ v q → f w t = w)
    (hrowA : ∀ j : ℕ, j < 4 → ∃ e1 : ℝ, 0 < e1 ∧ (s.a q j = dist (v q) (v j) →
      ∀ t : ℝ, |t| < e1 → s.a q j ≤ dist (f (v q) t) (f (v j) t)))
    (hrowB : ∀ j : ℕ, j < 4 → ∃ e2 : ℝ, 0 < e2 ∧ (dist (v q) (v j) = s.b q j →
      ∀ t : ℝ, |t| < e2 → dist (f (v q) t) (f (v j) t) ≤ s.b q j)) :
    (∀ i j, ∃ e1 : ℝ, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
        ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t))) ∧
    (∀ i j, ∃ e2 : ℝ, 0 < e2 ∧ (dist (v i) (v j) = s.b i j →
        ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j)) := by
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  have hAred : ∀ i j : ℕ, s.a i j = s.a (i % 4) (j % 4) := fun i j => periodic2_MOD_p21 h4 hpa4
  have hBred : ∀ i j : ℕ, s.b i j = s.b (i % 4) (j % 4) := fun i j => periodic2_MOD_p21 h4 hpb4
  have hAcong : ∀ i j k l : ℕ, i % 4 = k % 4 → j % 4 = l % 4 → s.a i j = s.a k l := by
    intro i j k l hi hj
    rw [hAred i j, hAred k l, hi, hj]
  have hBcong : ∀ i j k l : ℕ, i % 4 = k % 4 → j % 4 = l % 4 → s.b i j = s.b k l := by
    intro i j k l hi hj
    rw [hBred i j, hBred k l, hi, hj]
  -- ── lift the row lemmas off the `% 4`-class of `j` ──
  have hArow : ∀ j : ℕ, ∃ e1 : ℝ, 0 < e1 ∧ (s.a q j = dist (v q) (v j) →
      ∀ t : ℝ, |t| < e1 → s.a q j ≤ dist (f (v q) t) (f (v j) t)) := by
    intro j
    obtain ⟨e1, he1, hall⟩ := hrowA (j % 4) (Nat.mod_lt _ (by norm_num))
    refine ⟨e1, he1, fun hhyp t ht => ?_⟩
    have hap : s.a q (j % 4) = s.a q j := hAcong q (j % 4) q j rfl (by omega)
    have hvj : v (j % 4) = v j := hvred j
    rw [← hap, ← hvj] at hhyp ⊢
    exact hall hhyp t ht
  have hBrow : ∀ j : ℕ, ∃ e2 : ℝ, 0 < e2 ∧ (dist (v q) (v j) = s.b q j →
      ∀ t : ℝ, |t| < e2 → dist (f (v q) t) (f (v j) t) ≤ s.b q j) := by
    intro j
    obtain ⟨e2, he2, hall⟩ := hrowB (j % 4) (Nat.mod_lt _ (by norm_num))
    refine ⟨e2, he2, fun hhyp t ht => ?_⟩
    have hbp : s.b q (j % 4) = s.b q j := hBcong q (j % 4) q j rfl (by omega)
    have hvj : v (j % 4) = v j := hvred j
    rw [← hbp, ← hvj] at hhyp ⊢
    exact hall hhyp t ht
  -- ── assemble: HOL's four-way `MOD_4_CASES` split on `(i,j)` ──
  refine ⟨?_, ?_⟩
  · intro i j
    by_cases hA : i % 4 = q % 4
    · -- `i` sits on the deformed vertex: transport the row lemma at `q`
      obtain ⟨e1, he1, hall⟩ := hArow j
      refine ⟨e1, he1, fun hhyp t ht => ?_⟩
      have hvi : v i = v q := by rw [← hvred i, hA]; exact hvred q
      have haij : s.a i j = s.a q j := hAcong i j q j hA rfl
      rw [haij, hvi] at hhyp ⊢
      exact hall hhyp t ht
    · by_cases hB : j % 4 = q % 4
      · -- `j` sits on the deformed vertex: row lemma at `q` with `DIST_SYM`
        obtain ⟨e1, he1, hall⟩ := hArow i
        refine ⟨e1, he1, fun hhyp t ht => ?_⟩
        have hvj : v j = v q := by rw [← hvred j, hB]; exact hvred q
        have haij : s.a i j = s.a q i := (hAcong i j i q rfl hB).trans (hsym i q).1
        have hdi : dist (v i) (v j) = dist (v q) (v i) := by rw [hvj, dist_comm]
        have hdf : dist (f (v i) t) (f (v j) t) = dist (f (v q) t) (f (v i) t) := by
          rw [hvj, dist_comm]
        rw [haij, hdi] at hhyp
        rw [haij, hdf]
        exact hall hhyp t ht
      · -- neither slot is deformed: `f` fixes both, `BBsV39` gives the bound
        refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
        have hfi : f (v i) t = v i := hfix _ t (hne i q hA)
        have hfj : f (v j) t = v j := hfix _ t (hne j q hB)
        rw [hfi, hfj]
        exact (hBBd i j).1
  · intro i j
    by_cases hA : i % 4 = q % 4
    · obtain ⟨e2, he2, hall⟩ := hBrow j
      refine ⟨e2, he2, fun hhyp t ht => ?_⟩
      have hvi : v i = v q := by rw [← hvred i, hA]; exact hvred q
      have hbij : s.b i j = s.b q j := hBcong i j q j hA rfl
      rw [hbij, hvi] at hhyp ⊢
      exact hall hhyp t ht
    · by_cases hB : j % 4 = q % 4
      · obtain ⟨e2, he2, hall⟩ := hBrow i
        refine ⟨e2, he2, fun hhyp t ht => ?_⟩
        have hvj : v j = v q := by rw [← hvred j, hB]; exact hvred q
        have hbij : s.b i j = s.b q i := (hBcong i j i q rfl hB).trans (hsym i q).2.2.2.1
        have hdi : dist (v i) (v j) = dist (v q) (v i) := by rw [hvj, dist_comm]
        have hdf : dist (f (v i) t) (f (v j) t) = dist (f (v q) t) (f (v i) t) := by
          rw [hvj, dist_comm]
        rw [hbij, hdi] at hhyp
        rw [hbij, hdf]
        exact hall hhyp t ht
      · refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
        have hfi : f (v i) t = v i := hfix _ t (hne i q hA)
        have hfj : f (v j) t = v j := hfix _ t (hne j q hB)
        rw [hfi, hfj]
        exact (hBBd i j).2

/-- HOL `ab4_assumption_reduction2` (JOTSWIX.hl:693): same propagation,
with the upper-bound side assumed only along the deformed edge. NEEDS:
the full HOL proof (JOTSWIX.hl:700-900). -/
theorem ab4_assumption_reduction2_p23 (s : ScsV39) (p : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s v)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j < dist (v i) (v j) ∧ 4 * h0 < s.b i j)
    (hdef : Deformation f (Set.range v) (-e) e) (he : 0 < e)
    (hfix : ∀ w t, w ≠ v p → f w t = w)
    (hdist : ∀ t, |t| < e → dist (v (p + 3)) (f (v p) t) = dist (v (p + 3)) (v p))
    (hab : s.a p (p + 1) < dist (v p) (v (p + 1)))
    (hb3 : ∃ e3 : ℝ, 0 < e3 ∧ ∀ t, |t| < e3 →
      dist (f (v p) t) (v (p + 1)) ≤ s.b p (p + 1)) :
    (∀ i j, ∃ e1 : ℝ, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
        ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t))) ∧
    (∀ i j, ∃ e2 : ℝ, 0 < e2 ∧ (dist (v i) (v j) = s.b i j →
        ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j)) := by
  have hinj : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j := BBs_inj_p21 s v 4 hs hk hBB
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpb, -, hsym, hch, ha0, -, -, -, -, -, -⟩ := hs
  obtain ⟨hann, hperv, hdistBB, -⟩ := hBB
  have hperv4 : Periodic v 4 := hk ▸ hperv
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  have hpa4 : Periodic2 s.a 4 := hk ▸ hpa
  have hpb4 : Periodic2 s.b 4 := hk ▸ hpb
  have hvred : ∀ i : ℕ, v (i % 4) = v i := fun i => periodic_mod_eq_p23 hperv4 i
  have hAred : ∀ i j : ℕ, s.a i j = s.a (i % 4) (j % 4) := fun i j => periodic2_MOD_p21 h4 hpa4
  have hBred : ∀ i j : ℕ, s.b i j = s.b (i % 4) (j % 4) := fun i j => periodic2_MOD_p21 h4 hpb4
  have hAcong : ∀ i j k l : ℕ, i % 4 = k % 4 → j % 4 = l % 4 → s.a i j = s.a k l := by
    intro i j k l hi hj
    rw [hAred i j, hAred k l, hi, hj]
  have hBcong : ∀ i j k l : ℕ, i % 4 = k % 4 → j % 4 = l % 4 → s.b i j = s.b k l := by
    intro i j k l hi hj
    rw [hBred i j, hBred k l, hi, hj]
  have hmodv : ∀ i j : ℕ, v i = v j → i % 4 = j % 4 := by
    intro i j hij
    exact hinj (i % 4) (j % 4) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      (by rw [hvred i, hvred j]; exact hij)
  have hne : ∀ i j : ℕ, i % 4 ≠ j % 4 → v i ≠ v j :=
    fun i j hnc hc => hnc (hmodv i j hc)
  -- every vertex of the annulus has norm ≤ `2 * h0`
  have hnorm : ∀ i : ℕ, ‖v i‖ ≤ 2 * h0 := by
    intro i
    have hx : v i ∈ ballAnnulus := hann (Set.mem_range_self i)
    unfold ballAnnulus at hx
    have h1 : dist (v i) 0 ≤ 2 * h0 := Metric.mem_closedBall.mp hx.1
    rwa [dist_eq_norm, sub_zero] at h1
  have htri : dist (v p) (v (p + 2)) ≤ 4 * h0 := by
    have h1 : dist (v p) (v (p + 2)) ≤ dist (v p) 0 + dist 0 (v (p + 2)) :=
      dist_triangle (v p) 0 (v (p + 2))
    have h2 : dist (v p) 0 = ‖v p‖ := by rw [dist_eq_norm, sub_zero]
    have h3 : dist 0 (v (p + 2)) = ‖v (p + 2)‖ := by rw [dist_eq_norm, zero_sub, norm_neg]
    rw [h2, h3] at h1
    linarith [hnorm p, hnorm (p + 2)]
  have hdiag2 : scsDiag 4 p (p + 2) := by
    unfold scsDiag
    exact ⟨by intro hc; omega, by intro hc; omega, by intro hc; omega⟩
  have hrowA : ∀ j : ℕ, j < 4 → ∃ e1 : ℝ, 0 < e1 ∧ (s.a p j = dist (v p) (v j) →
      ∀ t : ℝ, |t| < e1 → s.a p j ≤ dist (f (v p) t) (f (v j) t)) := by
    intro j hj
    rcases MOD_4_CASES_p23 j p hj with h | h | h | h
    · -- `j ≡ p`: both slots coincide, `s.a p p = 0` and the distance is `0`
      refine ⟨1, by norm_num, fun _ t _ => ?_⟩
      have hjeq : j % 4 = p % 4 := by rw [h, Nat.mod_mod]; omega
      have hjv : v j = v p := by rw [← hvred j, hjeq]; exact hvred p
      have hz : s.a p j = s.a p p := hAcong p j p p rfl hjeq
      rw [hz, ha0 p, hjv, dist_self]
    · -- `j ≡ p + 1`: `hab` makes the `a` hypothesis impossible
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 1) % 4 := by rw [h, Nat.mod_mod]
      have ha : s.a p j = s.a p (p + 1) := hAcong p j p (p + 1) rfl hjmod
      have hjv : v j = v (p + 1) := by rw [h]; exact hvred (p + 1)
      have he1 : s.a p (p + 1) = dist (v p) (v (p + 1)) := by
        rw [← ha, ← hjv]; exact hhyp
      exact absurd he1 (ne_of_lt hab)
    · -- `j ≡ p + 2`: the (p,p+2) diagonal, `hdg` makes it impossible
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 2) % 4 := by rw [h, Nat.mod_mod]
      have ha : s.a p j = s.a p (p + 2) := hAcong p j p (p + 2) rfl hjmod
      have hjv : v j = v (p + 2) := by rw [h]; exact hvred (p + 2)
      have he1 : s.a p (p + 2) = dist (v p) (v (p + 2)) := by
        rw [← ha, ← hjv]; exact hhyp
      exact absurd he1 (ne_of_lt (hdg p (p + 2) hdiag2).1)
    · -- `j ≡ p + 3`: the one deformed slot; the `hdist` invariance closes it
      refine ⟨e, he, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 3) % 4 := by rw [h, Nat.mod_mod]
      have ha : s.a p j = s.a p (p + 3) := hAcong p j p (p + 3) rfl hjmod
      have hjv : v j = v (p + 3) := by rw [h]; exact hvred (p + 3)
      rw [ha, hjv, hfix (v (p + 3)) t (hne (p + 3) p (by omega))]
      have hd3 : dist (f (v p) t) (v (p + 3)) = dist (v p) (v (p + 3)) :=
        (dist_comm _ _).trans ((hdist t ht).trans (dist_comm _ _))
      rw [hd3]
      exact (hdistBB p (p + 3)).1
  have hrowB : ∀ j : ℕ, j < 4 → ∃ e2 : ℝ, 0 < e2 ∧ (dist (v p) (v j) = s.b p j →
      ∀ t : ℝ, |t| < e2 → dist (f (v p) t) (f (v j) t) ≤ s.b p j) := by
    intro j hj
    rcases MOD_4_CASES_p23 j p hj with h | h | h | h
    · -- `j ≡ p`: both slots coincide; `0 ≤ s.b p p` from the `a ≤ b` chain
      refine ⟨1, by norm_num, fun _ t _ => ?_⟩
      have hjeq : j % 4 = p % 4 := by rw [h, Nat.mod_mod]; omega
      have hjv : v j = v p := by rw [← hvred j, hjeq]; exact hvred p
      have hz : s.a p j = s.a p p := hAcong p j p p rfl hjeq
      have hle : s.a p j ≤ s.b p j :=
        (hch p j).1.trans ((hch p j).2.1.trans (hch p j).2.2)
      rw [hz, ha0 p] at hle
      rw [hjv, dist_self]
      exact hle
    · -- `j ≡ p + 1`: the `hb3` bound along the deformed edge (`f` fixes `v (p+1)`)
      obtain ⟨e3, he3, hb3all⟩ := hb3
      refine ⟨e3, he3, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 1) % 4 := by rw [h, Nat.mod_mod]
      have hb : s.b p j = s.b p (p + 1) := hBcong p j p (p + 1) rfl hjmod
      have hjv : v j = v (p + 1) := by rw [h]; exact hvred (p + 1)
      have hfix1 : f (v (p + 1)) t = v (p + 1) := hfix _ t (hne (p + 1) p (by omega))
      rw [hb, hjv, hfix1]
      exact hb3all t ht
    · -- `j ≡ p + 2`: the diagonal is shorter than `4 * h0 < s.b p (p+2)`
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 2) % 4 := by rw [h, Nat.mod_mod]
      have hb : s.b p j = s.b p (p + 2) := hBcong p j p (p + 2) rfl hjmod
      have hjv : v j = v (p + 2) := by rw [h]; exact hvred (p + 2)
      have he1 : dist (v p) (v (p + 2)) = s.b p (p + 2) := by
        rw [← hb, ← hjv]; exact hhyp
      exact absurd he1 (ne_of_lt (lt_of_le_of_lt htri (hdg p (p + 2) hdiag2).2))
    · -- `j ≡ p + 3`: same invariance as the `a` side
      refine ⟨e, he, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 3) % 4 := by rw [h, Nat.mod_mod]
      have hb : s.b p j = s.b p (p + 3) := hBcong p j p (p + 3) rfl hjmod
      have hjv : v j = v (p + 3) := by rw [h]; exact hvred (p + 3)
      rw [hb, hjv, hfix (v (p + 3)) t (hne (p + 3) p (by omega))]
      have hd3 : dist (f (v p) t) (v (p + 3)) = dist (v p) (v (p + 3)) :=
        (dist_comm _ _).trans ((hdist t ht).trans (dist_comm _ _))
      rw [hd3]
      exact (hdistBB p (p + 3)).2
  exact ab4_assemble_row_p23 s p f v hpa4 hpb4 hvred hsym hdistBB hne hfix hrowA hrowB

/-- HOL `ab4_assumption_reduction_sym` (JOTSWIX.hl:900): the `_sym`
twin, moving the fixed vertex to `v (p+1)`. NEEDS: the full HOL proof
(JOTSWIX.hl:908-1084). -/
theorem ab4_assumption_reduction_sym_p23 (s : ScsV39) (p : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s v)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j < dist (v i) (v j) ∧ 4 * h0 < s.b i j)
    (hdef : Deformation f (Set.range v) (-e) e) (he : 0 < e)
    (hfix : ∀ w t, w ≠ v (p + 1) → f w t = w)
    (hdist : ∀ t, |t| < e → dist (f (v (p + 1)) t) (v (p + 2)) =
      dist (v (p + 1)) (v (p + 2)))
    (hab : s.a p (p + 1) < dist (v p) (v (p + 1)) ∧
      dist (v p) (v (p + 1)) < s.b p (p + 1)) :
    (∀ i j, ∃ e1 : ℝ, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
        ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t))) ∧
    (∀ i j, ∃ e2 : ℝ, 0 < e2 ∧ (dist (v i) (v j) = s.b i j →
        ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j)) := by
  have hinj : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j := BBs_inj_p21 s v 4 hs hk hBB
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpb, -, hsym, hch, ha0, -, -, -, -, -, -⟩ := hs
  obtain ⟨hann, hperv, hdistBB, -⟩ := hBB
  have hperv4 : Periodic v 4 := hk ▸ hperv
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  have hpa4 : Periodic2 s.a 4 := hk ▸ hpa
  have hpb4 : Periodic2 s.b 4 := hk ▸ hpb
  have hvred : ∀ i : ℕ, v (i % 4) = v i := fun i => periodic_mod_eq_p23 hperv4 i
  have hAred : ∀ i j : ℕ, s.a i j = s.a (i % 4) (j % 4) := fun i j => periodic2_MOD_p21 h4 hpa4
  have hBred : ∀ i j : ℕ, s.b i j = s.b (i % 4) (j % 4) := fun i j => periodic2_MOD_p21 h4 hpb4
  have hAcong : ∀ i j k l : ℕ, i % 4 = k % 4 → j % 4 = l % 4 → s.a i j = s.a k l := by
    intro i j k l hi hj
    rw [hAred i j, hAred k l, hi, hj]
  have hBcong : ∀ i j k l : ℕ, i % 4 = k % 4 → j % 4 = l % 4 → s.b i j = s.b k l := by
    intro i j k l hi hj
    rw [hBred i j, hBred k l, hi, hj]
  have hmodv : ∀ i j : ℕ, v i = v j → i % 4 = j % 4 := by
    intro i j hij
    exact hinj (i % 4) (j % 4) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      (by rw [hvred i, hvred j]; exact hij)
  have hne : ∀ i j : ℕ, i % 4 ≠ j % 4 → v i ≠ v j :=
    fun i j hnc hc => hnc (hmodv i j hc)
  -- every vertex of the annulus has norm ≤ `2 * h0`
  have hnorm : ∀ i : ℕ, ‖v i‖ ≤ 2 * h0 := by
    intro i
    have hx : v i ∈ ballAnnulus := hann (Set.mem_range_self i)
    unfold ballAnnulus at hx
    have h1 : dist (v i) 0 ≤ 2 * h0 := Metric.mem_closedBall.mp hx.1
    rwa [dist_eq_norm, sub_zero] at h1
  have htri : dist (v (p + 1)) (v (p + 3)) ≤ 4 * h0 := by
    have h1 : dist (v (p + 1)) (v (p + 3)) ≤
        dist (v (p + 1)) 0 + dist 0 (v (p + 3)) :=
      dist_triangle (v (p + 1)) 0 (v (p + 3))
    have h2 : dist (v (p + 1)) 0 = ‖v (p + 1)‖ := by rw [dist_eq_norm, sub_zero]
    have h3 : dist 0 (v (p + 3)) = ‖v (p + 3)‖ := by rw [dist_eq_norm, zero_sub, norm_neg]
    rw [h2, h3] at h1
    linarith [hnorm (p + 1), hnorm (p + 3)]
  have hdiag2 : scsDiag 4 (p + 1) (p + 3) := by
    unfold scsDiag
    exact ⟨by intro hc; omega, by intro hc; omega, by intro hc; omega⟩
  have hrowA : ∀ j : ℕ, j < 4 → ∃ e1 : ℝ, 0 < e1 ∧ (s.a (p + 1) j = dist (v (p + 1)) (v j) →
      ∀ t : ℝ, |t| < e1 → s.a (p + 1) j ≤ dist (f (v (p + 1)) t) (f (v j) t)) := by
    intro j hj
    rcases MOD_4_CASES_p23 j (p + 1) hj with h | h | h | h
    · -- `j ≡ p + 1`: both slots coincide, `s.a (p+1) (p+1) = 0`, distance `0`
      refine ⟨1, by norm_num, fun _ t _ => ?_⟩
      have hjeq : j % 4 = (p + 1) % 4 := by rw [h, Nat.mod_mod]
      have hjv : v j = v (p + 1) := by rw [← hvred j, hjeq]; exact hvred (p + 1)
      have hz : s.a (p + 1) j = s.a (p + 1) (p + 1) :=
        hAcong (p + 1) j (p + 1) (p + 1) rfl hjeq
      rw [hz, ha0 (p + 1), hjv, dist_self]
    · -- `j ≡ p + 2`: the `hdist` invariance at the deformed vertex
      refine ⟨e, he, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 2) % 4 := by rw [h, Nat.mod_mod]
      have ha : s.a (p + 1) j = s.a (p + 1) (p + 2) :=
        hAcong (p + 1) j (p + 1) (p + 2) rfl hjmod
      have hjv : v j = v (p + 2) := by rw [← hvred j, hjmod]; exact hvred (p + 2)
      have he1 : s.a (p + 1) (p + 2) = dist (v (p + 1)) (v (p + 2)) := by
        rw [← ha, ← hjv]; exact hhyp
      rw [ha, hjv, hfix (v (p + 2)) t (hne (p + 2) (p + 1) (by omega))]
      rw [hdist t ht]
      exact le_of_eq he1
    · -- `j ≡ p + 3`: the (p+1,p+3) diagonal, `hdg` makes it impossible
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 3) % 4 := by rw [h, Nat.mod_mod]
      have ha : s.a (p + 1) j = s.a (p + 1) (p + 3) :=
        hAcong (p + 1) j (p + 1) (p + 3) rfl hjmod
      have hjv : v j = v (p + 3) := by rw [← hvred j, hjmod]; exact hvred (p + 3)
      have he1 : s.a (p + 1) (p + 3) = dist (v (p + 1)) (v (p + 3)) := by
        rw [← ha, ← hjv]; exact hhyp
      exact absurd he1 (ne_of_lt (hdg (p + 1) (p + 3) hdiag2).1)
    · -- `j ≡ p` (wrap-around): `hab.1` makes the `a` hypothesis impossible
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = p % 4 := by rw [h, Nat.mod_mod]; omega
      have ha : s.a (p + 1) j = s.a p (p + 1) := by
        have h1 : s.a (p + 1) j = s.a (p + 1) p :=
          hAcong (p + 1) j (p + 1) p rfl hjmod
        exact h1.trans (hsym p (p + 1)).1.symm
      have hjv : v j = v p := by rw [← hvred j, hjmod]; exact hvred p
      have he1 : s.a p (p + 1) = dist (v p) (v (p + 1)) := by
        rw [← ha, ← hjv, dist_comm]
        exact hhyp
      exact absurd he1 (ne_of_lt hab.1)
  have hrowB : ∀ j : ℕ, j < 4 → ∃ e2 : ℝ, 0 < e2 ∧
      (dist (v (p + 1)) (v j) = s.b (p + 1) j →
      ∀ t : ℝ, |t| < e2 → dist (f (v (p + 1)) t) (f (v j) t) ≤ s.b (p + 1) j) := by
    intro j hj
    rcases MOD_4_CASES_p23 j (p + 1) hj with h | h | h | h
    · -- `j ≡ p + 1`: both slots coincide; `0 ≤ s.b (p+1) (p+1)` via `a ≤ b`
      refine ⟨1, by norm_num, fun _ t _ => ?_⟩
      have hjeq : j % 4 = (p + 1) % 4 := by rw [h, Nat.mod_mod]
      have hjv : v j = v (p + 1) := by rw [← hvred j, hjeq]; exact hvred (p + 1)
      have hz : s.a (p + 1) j = s.a (p + 1) (p + 1) :=
        hAcong (p + 1) j (p + 1) (p + 1) rfl hjeq
      have hle : s.a (p + 1) j ≤ s.b (p + 1) j :=
        (hch (p + 1) j).1.trans ((hch (p + 1) j).2.1.trans (hch (p + 1) j).2.2)
      rw [hz, ha0 (p + 1)] at hle
      rw [hjv, dist_self]
      exact hle
    · -- `j ≡ p + 2`: the `hdist` invariance at the deformed vertex
      refine ⟨e, he, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 2) % 4 := by rw [h, Nat.mod_mod]
      have hb : s.b (p + 1) j = s.b (p + 1) (p + 2) :=
        hBcong (p + 1) j (p + 1) (p + 2) rfl hjmod
      have hjv : v j = v (p + 2) := by rw [← hvred j, hjmod]; exact hvred (p + 2)
      have he1 : dist (v (p + 1)) (v (p + 2)) = s.b (p + 1) (p + 2) := by
        rw [← hb, ← hjv]; exact hhyp
      rw [hb, hjv, hfix (v (p + 2)) t (hne (p + 2) (p + 1) (by omega))]
      rw [hdist t ht]
      exact le_of_eq he1
    · -- `j ≡ p + 3`: the diagonal is shorter than `4 * h0 < s.b (p+1) (p+3)`
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = (p + 3) % 4 := by rw [h, Nat.mod_mod]
      have hb : s.b (p + 1) j = s.b (p + 1) (p + 3) :=
        hBcong (p + 1) j (p + 1) (p + 3) rfl hjmod
      have hjv : v j = v (p + 3) := by rw [← hvred j, hjmod]; exact hvred (p + 3)
      have he1 : dist (v (p + 1)) (v (p + 3)) = s.b (p + 1) (p + 3) := by
        rw [← hb, ← hjv]; exact hhyp
      exact absurd he1 (ne_of_lt (lt_of_le_of_lt htri (hdg (p + 1) (p + 3) hdiag2).2))
    · -- `j ≡ p` (wrap-around): `hab.2` makes the `b` hypothesis impossible
      refine ⟨1, by norm_num, fun hhyp t ht => ?_⟩
      have hjmod : j % 4 = p % 4 := by rw [h, Nat.mod_mod]; omega
      have hb : s.b (p + 1) j = s.b p (p + 1) := by
        have h1 : s.b (p + 1) j = s.b (p + 1) p :=
          hBcong (p + 1) j (p + 1) p rfl hjmod
        exact h1.trans (hsym p (p + 1)).2.2.2.1.symm
      have hjv : v j = v p := by rw [← hvred j, hjmod]; exact hvred p
      have he1 : dist (v p) (v (p + 1)) = s.b p (p + 1) := by
        rw [← hb, ← hjv, dist_comm]
        exact hhyp
      exact absurd he1 (ne_of_lt hab.2)
  exact ab4_assemble_row_p23 s (p + 1) f v hpa4 hpb4 hvred hsym hdistBB hne hfix hrowA hrowB

/-- HOL `deform_azim_sum` (JOTSWIX.hl:1084): a deformation of a 4-point
fan preserving one azimuth summand preserves the summed azimuth, off a
collinearity set. NEEDS: `CONTINUOUS_PRESERVE_COLLINEAR`
(Local_lemmas1) + the real-continuity of `f` from `Deformation`. -/
theorem deform_azim_sum_p23 (v1 v2 v3 v4 : V3) (f : V3 → ℝ → V3) (e : ℝ)
    (hdef : Deformation f {v1, v2, v3, v4} (-e) e)
    (ha4 : 0 < azim 0 v1 v2 v4) (ha4' : azim 0 v1 v2 v4 < Real.pi)
    (hc2 : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hc3 : ¬ Collinear ℝ ({0, v1, v3} : Set V3))
    (hc4 : ¬ Collinear ℝ ({0, v1, v4} : Set V3))
    (hsum : azim 0 v1 v2 v3 + azim 0 v1 v3 v4 = azim 0 v1 v2 v4)
    (hcase : ((∀ t, azim 0 (f v1 t) (f v2 t) (f v3 t) = azim 0 v1 v2 v3) ∧
        0 < azim 0 v1 v3 v4 ∧ azim 0 v1 v3 v4 < Real.pi) ∨
      ((∀ t, azim 0 (f v1 t) (f v3 t) (f v4 t) = azim 0 v1 v3 v4) ∧
        0 < azim 0 v1 v2 v3 ∧ azim 0 v1 v2 v3 < Real.pi)) :
    ∃ e1 : ℝ, 0 < e1 ∧ ∀ t, |t| < e1 →
      ¬ Collinear ℝ ({0, f v1 t, f v2 t} : Set V3) ∧
      ¬ Collinear ℝ ({0, f v1 t, f v3 t} : Set V3) ∧
      ¬ Collinear ℝ ({0, f v1 t, f v4 t} : Set V3) ∧
      azim 0 (f v1 t) (f v2 t) (f v3 t) + azim 0 (f v1 t) (f v3 t) (f v4 t) =
        azim 0 (f v1 t) (f v2 t) (f v4 t) := by
  -- ── substrate: `Deformation` gives continuity and normalisation at `0` ──
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-e) e := hdef.1
  have hcont : ∀ v ∈ ({v1, v2, v3, v4} : Set V3), ∀ r ∈ Set.Ioo (-e) e,
      ContinuousAt (f v) r := hdef.2.1
  have hfix0 : ∀ v ∈ ({v1, v2, v3, v4} : Set V3), f v 0 = v := hdef.2.2
  have hv1 : v1 ∈ ({v1, v2, v3, v4} : Set V3) := by simp
  have hv2 : v2 ∈ ({v1, v2, v3, v4} : Set V3) := by simp
  have hv3 : v3 ∈ ({v1, v2, v3, v4} : Set V3) := by simp
  have hv4 : v4 ∈ ({v1, v2, v3, v4} : Set V3) := by simp
  have hct1 : ContinuousAt (f v1) 0 := hcont v1 hv1 0 h0mem
  have hct2 : ContinuousAt (f v2) 0 := hcont v2 hv2 0 h0mem
  have hct3 : ContinuousAt (f v3) 0 := hcont v3 hv3 0 h0mem
  have hct4 : ContinuousAt (f v4) 0 := hcont v4 hv4 0 h0mem
  have hf1 : f v1 0 = v1 := hfix0 v1 hv1
  have hf2 : f v2 0 = v2 := hfix0 v2 hv2
  have hf3 : f v3 0 = v3 := hfix0 v3 hv3
  have hf4 : f v4 0 = v4 := hfix0 v4 hv4
  -- ── HOL: three `CONTINUOUS_PRESERVE_COLLINEAR` epsilons ──
  have hnc12 : ¬ Collinear3 (0 : V3) (f v1 0) (f v2 0) := by
    show ¬ Collinear ℝ ({0, f v1 0, f v2 0} : Set V3)
    rw [hf1, hf2]
    exact hc2
  have hnc13 : ¬ Collinear3 (0 : V3) (f v1 0) (f v3 0) := by
    show ¬ Collinear ℝ ({0, f v1 0, f v3 0} : Set V3)
    rw [hf1, hf3]
    exact hc3
  have hnc14 : ¬ Collinear3 (0 : V3) (f v1 0) (f v4 0) := by
    show ¬ Collinear ℝ ({0, f v1 0, f v4 0} : Set V3)
    rw [hf1, hf4]
    exact hc4
  obtain ⟨e12, he12, h12⟩ :=
    CONTINUOUS_PRESERVE_COLLINEAR (0 : V3) (f v1) (f v2) 0 hct1 hct2 hnc12
  obtain ⟨e13, he13, h13⟩ :=
    CONTINUOUS_PRESERVE_COLLINEAR (0 : V3) (f v1) (f v3) 0 hct1 hct3 hnc13
  obtain ⟨e14, he14, h14⟩ :=
    CONTINUOUS_PRESERVE_COLLINEAR (0 : V3) (f v1) (f v4) 0 hct1 hct4 hnc14
  -- ── HOL: the two `WNWSHJT_ALT` branches inside `hcase`, giving some `e`
  --    with `azim(123) + azim(134) < 2π` on `|t| < e` ──
  have hsub4 : ({v4, v1, v3} : Set V3) ⊆ ({v1, v2, v3, v4} : Set V3) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp
  have hsub3 : ({v3, v1, v2} : Set V3) ⊆ ({v1, v2, v3, v4} : Set V3) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp
  have hsumeps : ∃ es : ℝ, 0 < es ∧ ∀ t, |t| < es →
      azim 0 (f v1 t) (f v2 t) (f v3 t) + azim 0 (f v1 t) (f v3 t) (f v4 t) <
        2 * Real.pi := by
    rcases hcase with ⟨h123, h134pos, _⟩ | ⟨h134, h123pos, _⟩
    · -- left disjunct: freeze `azim 123`, open `azim 134` with `c = π - azim 123`
      have hdef4 : Deformation f ({v4, v1, v3} : Set V3) (-e) e :=
        deformation_subset_p14 f {v4, v1, v3} {v1, v2, v3, v4} (-e) e hsub4 hdef
      have hlt : azim 0 v1 v3 v4 < Real.pi - azim 0 v1 v2 v3 := by linarith
      obtain ⟨es, hes, hprop⟩ := WNWSHJT_ALT_p21 v4 v1 v3 f (-e) e
        (Real.pi - azim 0 v1 v2 v3) hdef4 hc3 hc4 h134pos hlt
      refine ⟨es, hes, fun t ht => ?_⟩
      have hp := hprop t ht
      have h123t := h123 t
      linarith [hp.1, hp.2, Real.pi_pos]
    · -- right disjunct: freeze `azim 134`, open `azim 123` with `c = π - azim 134`
      have hdef3 : Deformation f ({v3, v1, v2} : Set V3) (-e) e :=
        deformation_subset_p14 f {v3, v1, v2} {v1, v2, v3, v4} (-e) e hsub3 hdef
      have hlt : azim 0 v1 v2 v3 < Real.pi - azim 0 v1 v3 v4 := by linarith
      obtain ⟨es, hes, hprop⟩ := WNWSHJT_ALT_p21 v3 v1 v2 f (-e) e
        (Real.pi - azim 0 v1 v3 v4) hdef3 hc2 hc3 h123pos hlt
      refine ⟨es, hes, fun t ht => ?_⟩
      have hp := hprop t ht
      have h134t := h134 t
      linarith [hp.1, hp.2, Real.pi_pos]
  -- ── HOL: `epsilon_triple` twice, then the final window ──
  obtain ⟨es, hes, hsumall⟩ := hsumeps
  obtain ⟨eA, heA, hA2, hA3, hA4⟩ := epsilon_triple_p21 e12 e13 e14 he12 he13 he14
  obtain ⟨eB, heB, hBeA, hBes⟩ := epsilon_pair_p21 eA es heA hes
  refine ⟨eB, heB, fun t ht => ?_⟩
  have htA : |t| < eA := hBeA t ht
  have ht12 : |t| < e12 := hA2 t htA
  have ht13 : |t| < e13 := hA3 t htA
  have ht14 : |t| < e14 := hA4 t htA
  have hts : |t| < es := hBes t ht
  have hnc2t : ¬ Collinear3 (0 : V3) (f v1 t) (f v2 t) :=
    h12 t (by rwa [zero_sub, abs_neg])
  have hnc3t : ¬ Collinear3 (0 : V3) (f v1 t) (f v3 t) :=
    h13 t (by rwa [zero_sub, abs_neg])
  have hnc4t : ¬ Collinear3 (0 : V3) (f v1 t) (f v4 t) :=
    h14 t (by rwa [zero_sub, abs_neg])
  have hsum_t := hsumall t hts
  have hxv : f v1 t ≠ 0 := fun hzero =>
    hnc2t (collinear3_of_eq (v := (0 : V3)) (w := f v1 t) (w1 := f v2 t) hzero)
  exact ⟨hnc2t, hnc3t, hnc4t,
    (sum3_azim_fan (x := (0 : V3)) (v := f v1 t) (u := f v2 t) (w1 := f v3 t)
      (w2 := f v4 t) hxv hnc2t hnc3t hnc4t hsum_t).symm⟩

/-- HOL `NEHXMWH` (JOTSWIX.hl:1171): the quad endpoint lemma for the
`(p+2)`-opposite interior angles. NEEDS: `BBprime2_v39`/`BBs_v39`
descent and the terminal registry entry `5541487347`. -/
theorem NEHXMWH_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (FF : Set (V3 × V3)) (v : ℕ → V3) (p : ℕ)
    (hFF : (fun i : ℕ => (v i, v (i + 1))) '' Set.univ = FF)
    (hs : isScsV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s) (hb : scsBasicV39 s)
    (hg : scsGeneric v)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hang : ∀ i, i % 4 ≠ (p + 2) % 4 → interiorAngle1 0 FF (v i) < Real.pi) :
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∨
      dist (v p) (v (p + 1)) = s.b p (p + 1) := by
  -- ═══ A. substrate: `BBs_v39` from `MMs_v39`, fan data, azimuth forms ═══
  have hs' : isScsV39 s := hs
  obtain ⟨-, hk3le, -, -, -, -, -, hpa, -, -, hpbP, -, hsym, hch, hdiag0, hdiag, -, hbc, -, -, -⟩ := hs
  have hk4pos : 0 < (4 : ℕ) := by norm_num
  have hvBBp : v ∈ BBprimeV39 s := by
    have h2 : v ∈ BBprime2V39 s := by
      have h1 := hMM
      simp only [MMsV39, Set.mem_setOf_eq] at h1
      exact h1.1
    have h3 := h2
    simp only [BBprime2V39, Set.mem_setOf_eq] at h3
    exact h3.1
  obtain ⟨hBBs, hvmin, hvneg⟩ := by
    have h3 := hvBBp
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3
  have hBBs' : BBsV39 s v := hBBs
  obtain ⟨hann, hpervS, hbnd, hconv0⟩ := hBBs
  have hperv : Periodic v 4 := by rw [← hk]; exact hpervS
  have hmod : ∀ i : ℕ, v (i % 4) = v i := fun i => periodic_mod_eq_p23 hperv i
  have hinj : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j :=
    BBs_inj_p21 s v 4 hs' hk hBBs'
  have hmodv : ∀ i : ℕ, v i = v p → i % 4 = p % 4 := by
    intro i hi
    exact hinj (i % 4) (p % 4) (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos)
      (by rw [hmod i, hmod p]; exact hi)
  have hne_vp : ∀ i : ℕ, i % 4 ≠ p % 4 → v i ≠ v p :=
    fun i h hc => h (hmodv i hc)
  have hFFr : Set.range (fun i : ℕ => (v i, v (i + 1))) = FF := by
    simpa only [Set.image_univ] using hFF
  have hconv : ConvexLocalFan (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3))
      (Set.range fun i => (v i, v (i + 1))) := by
    rcases hconv0 with hle | hcl
    · omega
    · exact hcl
  have hlf := hconv.1
  have hvmem : ∀ i : ℕ, v i ∈ Set.range v := fun i => Set.mem_range_self i
  have hazim : ∀ i : ℕ, interiorAngle1 0 FF (v i) = azim 0 (v i) (v (i + 1)) (v (i + 3)) := by
    intro i
    have h1 := INTERIOR_ANGLE1_AZIM_p22 s v i hs' hBBs' (show 3 < s.k by omega) FF hFFr.symm
    rw [hk] at h1
    exact h1.symm
  have hpos : ∀ i : ℕ, 0 < azim 0 (v i) (v (i + 1)) (v (i + 3)) := by
    intro i
    have h1 := LOCAL_FAN_AZIM_POS_p22 s v i hconv hs' hBBs'
    rw [hk] at h1
    exact h1
  have hnc : ∀ i j : ℕ, i % 4 ≠ j % 4 → ¬ Collinear ℝ ({0, v i, v j} : Set V3) := by
    intro i j hij
    have hne : v i ≠ v j := by
      intro he
      exact hij (hinj (i % 4) (j % 4) (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos)
        (by rw [hmod i, hmod j]; exact he))
    have hgen : Generic (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)) := by
      simpa only [scsGeneric] using hg
    exact PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 _ _ _ _ _ hlf (hvmem i) (hvmem j) hne hgen
  have hpp2 : p % 4 ≠ (p + 2) % 4 := by omega
  have ha013_lt : azim 0 (v p) (v (p + 1)) (v (p + 3)) < Real.pi := by
    have h1 := hang p hpp2
    rwa [hazim p] at h1
  have ha013_pos : 0 < azim 0 (v p) (v (p + 1)) (v (p + 3)) := hpos p
  have hnc_pp1 : ¬ Collinear ℝ ({0, v p, v (p + 1)} : Set V3) := hnc p (p + 1) (by omega)
  have hnc_pp3 : ¬ Collinear ℝ ({0, v p, v (p + 3)} : Set V3) := hnc p (p + 3) (by omega)
  obtain ⟨⟨h132, h132'⟩, ⟨h301, h301'⟩⟩ :=
    g482w3_azim_cycle (x := v p) (y := v (p + 1)) (z := v (p + 3))
      hnc_pp1 hnc_pp3 ha013_pos ha013_lt
  have hncop : ¬ Coplanar ({0, v p, v (p + 1), v (p + 3)} : Set V3) := by
    intro hc
    rcases (AZIM_COND_FOR_COPLANAR (0 : V3) (v p) (v (p + 1)) (v (p + 3))).mpr hc with h0 | hpi
    · linarith
    · linarith
  -- ═══ B. the edge deformation at `v p` (HOL `deform_simplex_edge_exists`) ═══
  have hncop4 : ¬ Coplanar ({0, v (p + 3), v p, v (p + 1)} : Set V3) := by
    intro hc
    apply hncop
    have hset : ({0, v (p + 3), v p, v (p + 1)} : Set V3) = {0, v p, v (p + 1), v (p + 3)} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [hset] at hc
  have hcross : (v p).ofLp ⬝ᵥ (cross3 (v (p + 1)) (v (p + 3))).ofLp > 0 := by
    have h := (azim_lt_pi_cross_p14 (v (p + 1)) (v (p + 3)) (v p)).mp ⟨h132, h132'⟩
    rwa [dotProduct_comm] at h
  obtain ⟨f, hf⟩ := deform_simplex_edge_exists_p21 (Set.range v) (fun _ => 0) (fun t => t)
    (v (p + 3)) (v p) (v (p + 1)) 1
  obtain ⟨e', he'pos, hdef, hfix, hdistf⟩ := hf hncop4 hcross (by norm_num)
    (by fun_prop) (by fun_prop) (by simp) (by simp)
  have hdist1 : ∀ t : ℝ, |t| < e' →
      dist (v (p + 3)) (f (v p) t) = dist (v (p + 3)) (v p) := by
    intro t ht
    have h := (hdistf t ht).1
    rwa [add_zero] at h
  have hdist2 : ∀ t : ℝ, |t| < e' →
      dist (v (p + 1)) (f (v p) t) = dist (v (p + 1)) (v p) + t :=
    fun t ht => (hdistf t ht).2.1
  have hnormf : ∀ (i : ℕ) (t : ℝ), |t| < e' → ‖f (v i) t‖ = ‖v i‖ := by
    intro i t ht
    by_cases hi : v i = v p
    · rw [hi]; exact (hdistf t ht).2.2
    · rw [hfix _ t hi]
  have hdiag4 : ∀ i j, scsDiag 4 i j → s.a i j < dist (v i) (v j) ∧ 4 * h0 < s.b i j := by
    intro i j hd
    obtain ⟨h1, h2, h3⟩ := hdg i j hd
    exact ⟨lt_of_le_of_lt h1 h2, h3⟩
  -- ═══ C. assume the strict interior case, derive `hab` ═══
  by_contra hcon
  push_neg at hcon
  obtain ⟨hneA, hneB⟩ := hcon
  have hab : s.a p (p + 1) < dist (v p) (v (p + 1)) ∧
      dist (v p) (v (p + 1)) < s.b p (p + 1) :=
    ⟨lt_of_le_of_ne (hbnd p (p + 1)).1 (Ne.symm hneA),
      lt_of_le_of_ne (hbnd p (p + 1)).2 hneB⟩
  obtain ⟨ha_ab, hb_ab⟩ :=
    ab4_assumption_reduction_p23 s p f v e' hs' hk hBBs' hdiag4 hdef he'pos hfix hdist1 hab
  -- ═══ D. the flat-angle skolem for `deformation_BBs_ALT` ═══
  have hsucc : ∀ {i j : ℕ}, v i = v j → v (i + 1) = v (j + 1) := by
    intro i j hij
    have h1 : i % 4 = j % 4 :=
      hinj _ _ (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos) (by rw [hmod i, hmod j]; exact hij)
    have h2 : (i + 1) % 4 = (j + 1) % 4 := by omega
    rw [← hmod (i + 1), ← hmod (j + 1), h2]
  have hadd3 : ∀ {i j : ℕ}, v i = v j → v (i + 3) = v (j + 3) := by
    intro i j hij
    have h1 : i % 4 = j % 4 :=
      hinj _ _ (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos) (by rw [hmod i, hmod j]; exact hij)
    have h2 : (i + 3) % 4 = (j + 3) % 4 := by omega
    rw [← hmod (i + 3), ← hmod (j + 3), h2]
  have hazPi : ∀ i : ℕ, ∃ e0 : ℝ, 0 < e0 ∧
      (azim 0 (v i) (v (i + 1)) (v (i + (4 - 1))) = Real.pi →
        ∀ t : ℝ, |t| < e0 →
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (4 - 1))) t) ≤ Real.pi) := by
    intro i
    by_cases hi : v i = v (p + 2)
    · have h1 : v (i + 1) = v (p + 3) := hsucc hi
      have h3 : v (i + (4 - 1)) = v (p + 1) := by
        have h := hadd3 hi
        rw [show p + 2 + 3 = (p + 1) + 4 by omega, hperv (p + 1)] at h
        exact h
      have hne2 : v (p + 2) ≠ v p := hne_vp (p + 2) (by omega)
      have hne3 : v (p + 3) ≠ v p := hne_vp (p + 3) (by omega)
      have hne1 : v (p + 1) ≠ v p := hne_vp (p + 1) (by omega)
      refine ⟨1, by norm_num, fun hpi t _ => ?_⟩
      rw [hi, h1, h3] at hpi ⊢
      rw [hfix _ t hne2, hfix _ t hne3, hfix _ t hne1]
      exact le_of_eq hpi
    · have hmodne : i % 4 ≠ (p + 2) % 4 := by
        intro hc
        exact hi (by rw [← hmod i, ← hmod (p + 2), hc])
      have hlt : azim 0 (v i) (v (i + 1)) (v (i + 3)) < Real.pi := by
        have h1 := hang i hmodne
        rwa [hazim i] at h1
      refine ⟨1, by norm_num, fun hpi _ _ => ?_⟩
      exact absurd hpi (ne_of_lt hlt)
  obtain ⟨eBB, heBB, hBBdef⟩ :=
    deformation_BBs_ALT_p21 s 4 f v e' hs' hk (by norm_num) hBBs' hg he'pos hdef hazPi hnormf
      ha_ab hb_ab
  -- ═══ E. the two azimuth sums (`vv_split_azim_generic` + `deform_azim_sum`) ═══
  have hdef4 : Deformation f ({v (p + 3), v p, v (p + 1), v (p + 2)} : Set V3) (-e') e' := by
    refine deformation_subset_p14 f _ (Set.range v) (-e') e' ?_ hdef
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Set.mem_range_self _
  have hsum1 : azim 0 (v (p + 3)) (v p) (v (p + 2)) =
      azim 0 (v (p + 3)) (v p) (v (p + 1)) + azim 0 (v (p + 3)) (v (p + 1)) (v (p + 2)) := by
    have hnc1 : ¬ Collinear ℝ ({0, v (p + 3), v (p + 1)} : Set V3) :=
      hnc (p + 3) (p + 1) (by omega)
    have hnc2 : ¬ Collinear ℝ ({0, v (p + 3), v ((p + 3) + (4 - 1))} : Set V3) := by
      have e : v ((p + 3) + (4 - 1)) = v (p + 2) := by
        rw [show (p + 3) + (4 - 1) = (p + 2) + 4 by omega, hperv (p + 2)]
      rw [e]; exact hnc (p + 3) (p + 2) (by omega)
    have hnc3 : ¬ Collinear ℝ ({0, v (p + 3), v ((p + 3) + 1)} : Set V3) := by
      have e : v ((p + 3) + 1) = v p := by
        rw [show (p + 3) + 1 = p + 4 by omega, hperv p]
      rw [e]; exact hnc (p + 3) p (by omega)
    have hinj' : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j := hinj
    have h := vv_split_azim_alt_p21 (vv := v) (k := 4) (i := p + 3) (j := p + 1)
      hperv (by norm_num) hnc1 hnc2 hnc3 hconv hinj'
    have e2 : v (p + 3 + 4 - 1) = v (p + 2) := by
      rw [show p + 3 + 4 - 1 = (p + 2) + 4 by omega, hperv (p + 2)]
    have e3 : v (p + 3 + 1) = v p := by
      rw [show p + 3 + 1 = p + 4 by omega, hperv p]
    rw [e2, e3] at h
    exact h
  have hApos1 : 0 < azim 0 (v (p + 3)) (v p) (v (p + 2)) := by
    have h := LOCAL_FAN_AZIM_POS_p22 s v (p + 3) hconv hs' hBBs'
    rwa [hk, show (p + 3) + 1 = p + 4 by omega, hperv p,
      show (p + 3) + (4 - 1) = p + 6 by omega, show p + 6 = (p + 2) + 4 by omega,
      hperv (p + 2)] at h
  have hA'1 : azim 0 (v (p + 3)) (v p) (v (p + 2)) < Real.pi := by
    have h := hang (p + 3) (by omega : (p + 3) % 4 ≠ (p + 2) % 4)
    rw [hazim (p + 3)] at h
    rwa [show p + 3 + 1 = p + 4 by omega, hperv p,
      show p + 3 + 3 = p + 6 by omega, show p + 6 = (p + 2) + 4 by omega, hperv (p + 2)] at h
  have hcase1 : ((∀ t : ℝ, azim 0 (f (v (p + 3)) t) (f (v p) t) (f (v (p + 1)) t) =
        azim 0 (v (p + 3)) (v p) (v (p + 1))) ∧
      0 < azim 0 (v (p + 3)) (v (p + 1)) (v (p + 2)) ∧
        azim 0 (v (p + 3)) (v (p + 1)) (v (p + 2)) < Real.pi) ∨
      ((∀ t : ℝ, azim 0 (f (v (p + 3)) t) (f (v (p + 1)) t) (f (v (p + 2)) t) =
        azim 0 (v (p + 3)) (v (p + 1)) (v (p + 2))) ∧
      0 < azim 0 (v (p + 3)) (v p) (v (p + 1)) ∧
        azim 0 (v (p + 3)) (v p) (v (p + 1)) < Real.pi) := by
    refine Or.inr ⟨?_, h301, h301'⟩
    intro t
    rw [hfix _ t (hne_vp (p + 3) (by omega)), hfix _ t (hne_vp (p + 1) (by omega)),
      hfix _ t (hne_vp (p + 2) (by omega))]
  obtain ⟨eA, heA, hAall⟩ := deform_azim_sum_p23 (v (p + 3)) (v p) (v (p + 1)) (v (p + 2))
    f e' hdef4 hApos1 hA'1 (hnc (p + 3) p (by omega)) (hnc (p + 3) (p + 1) (by omega))
      (hnc (p + 3) (p + 2) (by omega)) hsum1.symm hcase1
  -- second sum: `v (p+1), v (p+2), v (p+3), v p`
  have hdef4' : Deformation f ({v (p + 1), v (p + 2), v (p + 3), v p} : Set V3) (-e') e' := by
    refine deformation_subset_p14 f _ (Set.range v) (-e') e' ?_ hdef
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Set.mem_range_self _
  have hsum2 : azim 0 (v (p + 1)) (v (p + 2)) (v p) =
      azim 0 (v (p + 1)) (v (p + 2)) (v (p + 3)) + azim 0 (v (p + 1)) (v (p + 3)) (v p) := by
    have hnc1 : ¬ Collinear ℝ ({0, v (p + 1), v (p + 3)} : Set V3) :=
      hnc (p + 1) (p + 3) (by omega)
    have hnc2 : ¬ Collinear ℝ ({0, v (p + 1), v ((p + 1) + (4 - 1))} : Set V3) := by
      have e : v ((p + 1) + (4 - 1)) = v p := by
        rw [show (p + 1) + (4 - 1) = p + 4 by omega, hperv p]
      rw [e]; exact hnc (p + 1) p (by omega)
    have hnc3 : ¬ Collinear ℝ ({0, v (p + 1), v ((p + 1) + 1)} : Set V3) := by
      have e : v ((p + 1) + 1) = v (p + 2) := by
        rw [show (p + 1) + 1 = p + 2 by omega]
      rw [e]; exact hnc (p + 1) (p + 2) (by omega)
    have hinj' : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j := hinj
    have h := vv_split_azim_alt_p21 (vv := v) (k := 4) (i := p + 1) (j := p + 3)
      hperv (by norm_num) hnc1 hnc2 hnc3 hconv hinj'
    have e2 : v (p + 1 + 4 - 1) = v p := by
      rw [show p + 1 + 4 - 1 = p + 4 by omega, hperv p]
    rw [e2] at h
    exact h
  have hApos2 : 0 < azim 0 (v (p + 1)) (v (p + 2)) (v p) := by
    have h := LOCAL_FAN_AZIM_POS_p22 s v (p + 1) hconv hs' hBBs'
    rwa [hk, show (p + 1) + 1 = p + 2 by omega,
      show (p + 1) + (4 - 1) = p + 4 by omega, hperv p] at h
  have hA'2 : azim 0 (v (p + 1)) (v (p + 2)) (v p) < Real.pi := by
    have h := hang (p + 1) (by omega : (p + 1) % 4 ≠ (p + 2) % 4)
    rw [hazim (p + 1)] at h
    rwa [show p + 1 + 1 = p + 2 by omega, show p + 1 + 3 = p + 4 by omega, hperv p] at h
  have hcase2 : ((∀ t : ℝ, azim 0 (f (v (p + 1)) t) (f (v (p + 2)) t) (f (v (p + 3)) t) =
        azim 0 (v (p + 1)) (v (p + 2)) (v (p + 3))) ∧
      0 < azim 0 (v (p + 1)) (v (p + 3)) (v p) ∧
        azim 0 (v (p + 1)) (v (p + 3)) (v p) < Real.pi) ∨
      ((∀ t : ℝ, azim 0 (f (v (p + 1)) t) (f (v (p + 3)) t) (f (v p) t) =
        azim 0 (v (p + 1)) (v (p + 3)) (v p)) ∧
      0 < azim 0 (v (p + 1)) (v (p + 2)) (v (p + 3)) ∧
        azim 0 (v (p + 1)) (v (p + 2)) (v (p + 3)) < Real.pi) := by
    refine Or.inl ⟨?_, h132, h132'⟩
    intro t
    rw [hfix _ t (hne_vp (p + 1) (by omega)), hfix _ t (hne_vp (p + 2) (by omega)),
      hfix _ t (hne_vp (p + 3) (by omega))]
  obtain ⟨eB, heB, hBall⟩ := deform_azim_sum_p23 (v (p + 1)) (v (p + 2)) (v (p + 3)) (v p)
    f e' hdef4' hApos2 hA'2 (hnc (p + 1) (p + 2) (by omega)) (hnc (p + 1) (p + 3) (by omega))
      (hnc (p + 1) p (by omega)) hsum2.symm hcase2
  -- ═══ F. nonplanarity stays open along the deformation ═══
  have hcont0 : ContinuousAt (fun t => f (v p) t) 0 :=
    hdef.2.1 (v p) (Set.mem_range_self p) 0 hdef.1
  obtain ⟨eNP, heNP, hNPall⟩ := NONPLANAR_OPEN_p14 (fun _ => (0 : V3)) (fun t => f (v p) t)
    (fun _ => v (p + 1)) (fun _ => v (p + 3)) 0
    (by
      have hset : ({0, f (v p) 0, v (p + 1), v (p + 3)} : Set V3) =
          {0, v p, v (p + 1), v (p + 3)} := by
        rw [hdef.2.2 (v p) (Set.mem_range_self p)]
      rwa [hset])
    continuousAt_const hcont0 continuousAt_const continuousAt_const
  have hNP : ∀ t : ℝ, |t| < eNP →
      ¬ Coplanar ({0, f (v p) t, v (p + 1), v (p + 3)} : Set V3) := by
    intro t ht
    exact hNPall t (by rwa [zero_sub, abs_neg])
  -- ═══ G. combine the epsilons ═══
  have hdef3 : Deformation f ({v (p + 3), v p, v (p + 1)} : Set V3) (-e') e' := by
    refine deformation_subset_p14 f _ (Set.range v) (-e') e' ?_ hdef
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact Set.mem_range_self _
  have hncF1 : ¬ Collinear ℝ ({0, f (v p) 0, f (v (p + 1)) 0} : Set V3) := by
    rw [hfix (v (p + 1)) 0 (hne_vp (p + 1) (by omega)),
      hdef.2.2 (v p) (Set.mem_range_self p)]
    exact hnc_pp1
  have hncF3 : ¬ Collinear ℝ ({0, f (v p) 0, f (v (p + 3)) 0} : Set V3) := by
    rw [hfix (v (p + 3)) 0 (hne_vp (p + 3) (by omega)),
      hdef.2.2 (v p) (Set.mem_range_self p)]
    exact hnc_pp3
  obtain ⟨eW, heW, hWall⟩ := WNWSHJT_p14 (v (p + 3)) (v p) (v (p + 1)) f (-e') e'
    hdef3 hncF1 hncF3 ha013_pos ha013_lt
  obtain ⟨e1, he1, h1e', h1eBB, h1eA⟩ := epsilon_triple_p21 e' eBB eA he'pos heBB heA
  obtain ⟨e2, he2, h2e1, h2eB, h2eNP⟩ := epsilon_triple_p21 e1 eB eNP he1 heB heNP
  obtain ⟨e3', he3', h3'e2, h3'eW⟩ := epsilon_pair_p21 e2 eW he2 heW
  obtain ⟨e7, he7, h7e3, h71⟩ := epsilon_pair_p21 e3' 1 he3' (by norm_num)
  have h7e' : ∀ t : ℝ, |t| < e7 → |t| < e' :=
    fun t ht => h1e' t (h2e1 t (h3'e2 t (h7e3 t ht)))
  have h7eBB : ∀ t : ℝ, |t| < e7 → |t| < eBB :=
    fun t ht => h1eBB t (h2e1 t (h3'e2 t (h7e3 t ht)))
  have h7eA : ∀ t : ℝ, |t| < e7 → |t| < eA :=
    fun t ht => h1eA t (h2e1 t (h3'e2 t (h7e3 t ht)))
  have h7eB : ∀ t : ℝ, |t| < e7 → |t| < eB :=
    fun t ht => h2eB t (h3'e2 t (h7e3 t ht))
  have h7eNP : ∀ t : ℝ, |t| < e7 → |t| < eNP :=
    fun t ht => h2eNP t (h3'e2 t (h7e3 t ht))
  have h7eW : ∀ t : ℝ, |t| < e7 → |t| < eW := fun t ht => h3'eW t (h7e3 t ht)
  -- ═══ H. norms and the `LEMMA_1834976363` box ═══
  have hnorm_lo : ∀ i : ℕ, 2 ≤ ‖v i‖ := by
    intro i
    have h := hann (Set.mem_range_self i)
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at h
    linarith [h.1, h.2]
  have hnorm_hi : ∀ i : ℕ, ‖v i‖ ≤ 2 * h0 := by
    intro i
    have h := hann (Set.mem_range_self i)
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at h
    linarith [h.1, h.2]
  set y1 : ℝ := ‖v (p + 3)‖ with hy1def
  set y2 : ℝ := ‖v p‖ with hy2def
  set y3 : ℝ := ‖v (p + 1)‖ with hy3def
  set y4 : ℝ := dist (v p) (v (p + 1)) with hy4def
  set y5 : ℝ := dist (v (p + 1)) (v (p + 3)) with hy5def
  set y6 : ℝ := dist (v p) (v (p + 3)) with hy6def
  have hy1lo : 2 ≤ y1 := by rw [hy1def]; exact hnorm_lo _
  have hy1hi : y1 ≤ 2 * h0 := by rw [hy1def]; exact hnorm_hi _
  have hy2lo : 2 ≤ y2 := by rw [hy2def]; exact hnorm_lo _
  have hy2hi : y2 ≤ 2 * h0 := by rw [hy2def]; exact hnorm_hi _
  have hy3lo : 2 ≤ y3 := by rw [hy3def]; exact hnorm_lo _
  have hy3hi : y3 ≤ 2 * h0 := by rw [hy3def]; exact hnorm_hi _
  have hy4lo : 2 ≤ y4 := by
    rw [hy4def]
    exact scs_lb_2_p22 s v p (p + 1) hs' hBBs' (by rw [hk]; omega)
  have hy5lo : 2 ≤ y5 := by
    rw [hy5def]
    exact scs_lb_2_p22 s v (p + 1) (p + 3) hs' hBBs' (by rw [hk]; omega)
  have hy6lo : 2 ≤ y6 := by
    rw [hy6def]
    exact scs_lb_2_p22 s v p (p + 3) hs' hBBs' (by rw [hk]; omega)
  have hy4le : y4 ≤ Real.sqrt 15.53 := by
    rw [hy4def]
    have h1 : dist (v p) (v (p + 1)) ≤ s.b p (p + 1) := (hbnd p (p + 1)).2
    have h2 : s.b p (p + 1) ≤ cstab := hbc p (by omega)
    have h3 : cstab ≤ Real.sqrt 15.53 := by
      have hc : cstab = (3.01 : ℝ) := rfl
      have hsq : (Real.sqrt 15.53) ^ 2 = 15.53 := Real.sq_sqrt (by norm_num)
      have hnn : (0 : ℝ) ≤ Real.sqrt 15.53 := Real.sqrt_nonneg _
      rw [hc]
      nlinarith
    linarith
  have hsqrt4 : Real.sqrt 15.53 < 4 := by
    have h : Real.sqrt 15.53 < Real.sqrt 16 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show Real.sqrt 16 = 4 from by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hx4 : (2 / h0) ^ 2 ≤ xrr y2 y3 y4 ∧ xrr y2 y3 y4 ≤ 15.53 := by
    constructor
    · exact xrr_simple_lower_bound_p22 y2 y3 y4 2 hy2lo hy2hi hy3lo hy3hi (by norm_num) hy4lo
    · have h := xrr_simple_upper_bound_p22 y2 y3 y4 (Real.sqrt 15.53)
        hy2lo hy2hi hy3lo hy3hi hy4lo hy4le hsqrt4
      rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15.53)] at h
  have hx5 : (2 / h0) ^ 2 ≤ xrr y1 y3 y5 :=
    xrr_simple_lower_bound_p22 y1 y3 y5 2 hy1lo hy1hi hy3lo hy3hi (by norm_num) hy5lo
  have hx6 : (2 / h0) ^ 2 ≤ xrr y1 y2 y6 :=
    xrr_simple_lower_bound_p22 y1 y2 y6 2 hy1lo hy1hi hy2lo hy2hi (by norm_num) hy6lo
  have hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6) := by
    have h := g482w3_upsX_pos_of_not_col (a := (0 : V3)) (b := v (p + 3)) (c := v p)
      (hnc (p + 3) p (by omega))
    have e1 : dist (0 : V3) (v (p + 3)) = y1 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy1def]
    have e2 : dist (0 : V3) (v p) = y2 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy2def]
    have e4 : dist (v (p + 3)) (v p) = y6 := by rw [dist_comm (v (p + 3)) (v p), ← hy6def]
    rw [e1, e2, e4] at h
    exact h
  have hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5) := by
    have h := g482w3_upsX_pos_of_not_col (a := (0 : V3)) (b := v (p + 3)) (c := v (p + 1))
      (hnc (p + 3) (p + 1) (by omega))
    have e1 : dist (0 : V3) (v (p + 3)) = y1 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy1def]
    have e2 : dist (0 : V3) (v (p + 1)) = y3 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy3def]
    have e4 : dist (v (p + 3)) (v (p + 1)) = y5 := by
      rw [dist_comm (v (p + 3)) (v (p + 1)), ← hy5def]
    rw [e1, e2, e4] at h
    exact h
  have hsub : Set.Ioo (y4 - e7) (y4 + e7) ⊆
      {y : ℝ | 0 < deltaY y1 y2 y3 y y5 y6 ∧ 0 < y ∧
        0 < upsX (y2 * y2) (y3 * y3) (y * y)} := by
    intro y hy
    have ht : |y - y4| < e7 := by
      rw [abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    have hyt : y = y4 + (y - y4) := by ring
    have hNPt : ¬ Coplanar ({0, f (v p) (y - y4), v (p + 1), v (p + 3)} : Set V3) :=
      hNP _ (h7eNP _ ht)
    refine ⟨?_, ?_, ?_⟩
    · have hncop' : ¬ Coplanar ({0, v (p + 3), f (v p) (y - y4), v (p + 1)} : Set V3) := by
        intro hc
        apply hNPt
        have hset : ({0, v (p + 3), f (v p) (y - y4), v (p + 1)} : Set V3) =
            {0, f (v p) (y - y4), v (p + 1), v (p + 3)} := by
          ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rwa [hset] at hc
      have hd := g482w3_deltaY_pos (u0 := (0 : V3)) (u1 := v (p + 3))
        (u2 := f (v p) (y - y4)) (u3 := v (p + 1)) hncop'
      have e1 : dist (0 : V3) (v (p + 3)) = y1 := by
        rw [dist_eq_norm, zero_sub, norm_neg, hy1def]
      have e2 : dist (0 : V3) (f (v p) (y - y4)) = y2 := by
        rw [dist_eq_norm, zero_sub, norm_neg, hnormf p (y - y4) (h7e' _ ht), ← hy2def]
      have e3 : dist (0 : V3) (v (p + 1)) = y3 := by
        rw [dist_eq_norm, zero_sub, norm_neg, hy3def]
      have e4 : dist (f (v p) (y - y4)) (v (p + 1)) = y := by
        rw [dist_comm, hdist2 _ (h7e' _ ht)]
        rw [show dist (v (p + 1)) (v p) = y4 from by rw [dist_comm, ← hy4def]]
        ring
      have e5 : dist (v (p + 3)) (v (p + 1)) = y5 := by
        rw [dist_comm (v (p + 3)) (v (p + 1)), ← hy5def]
      have e6 : dist (v (p + 3)) (f (v p) (y - y4)) = y6 := by
        rw [hdist1 _ (h7e' _ ht), dist_comm (v (p + 3)) (v p), ← hy6def]
      rw [e1, e2, e3, e4, e5, e6] at hd
      exact hd
    · have hgt : -(1 : ℝ) < y - y4 := (abs_lt.mp (h71 _ ht)).1
      linarith
    · have hnc' : ¬ Collinear3 (0 : V3) (f (v p) (y - y4)) (v (p + 1)) :=
        (notcoplanar_imp_notcollinear_fan (x := (0 : V3)) (v := f (v p) (y - y4))
          (u := v (p + 1)) (w := v (p + 3)) hNPt).2.1
      have h := g482w3_upsX_pos_of_not_col (a := (0 : V3)) (b := f (v p) (y - y4))
        (c := v (p + 1)) hnc'
      have e1 : dist (0 : V3) (f (v p) (y - y4)) = y2 := by
        rw [dist_eq_norm, zero_sub, norm_neg, hnormf p (y - y4) (h7e' _ ht), ← hy2def]
      have e2 : dist (0 : V3) (v (p + 1)) = y3 := by
        rw [dist_eq_norm, zero_sub, norm_neg, hy3def]
      have e3 : dist (f (v p) (y - y4)) (v (p + 1)) = y := by
        rw [dist_comm, hdist2 _ (h7e' _ ht)]
        rw [show dist (v (p + 1)) (v p) = y4 from by rw [dist_comm, ← hy4def]]
        ring
      rw [e1, e2, e3] at h
      exact h
  obtain ⟨y4', hy4'mem, hy4'lt⟩ := LEMMA_1834976363_p22 h y1 y2 y3 y4 y5 y6 (y4 - e7) (y4 + e7)
    ⟨hy1lo, hy1hi⟩ ⟨hy2lo, hy2hi⟩ ⟨hy3lo, hy3hi⟩ hx4 hx5 hx6
    ⟨by linarith, by linarith⟩ hsub (by linarith) (by linarith) hu6 hu5
  -- ═══ I. minimality at the deformed configuration ═══
  set t : ℝ := y4' - y4 with htdef
  have htabs : |t| < e7 := by
    rw [htdef, abs_lt]
    constructor <;> linarith [hy4'mem.1, hy4'mem.2]
  have hy4'eq : y4' = y4 + t := by rw [htdef]; ring
  have hw : BBsV39 s (fun i => f (v i) t) := hBBdef t (h7eBB t htabs)
  have hmin := MMs_minimize_tau_fun_p21 s 4 v (fun i => f (v i) t) hs' hb hk (by norm_num)
    hvBBp hw
  -- ═══ J. expand the two `rhoFun * azim` sums (HOL `periodic_sum` block) ═══
  have hsum4 : ∀ (g : ℕ → ℝ), periodic g 4 → setSum {i : ℕ | i < 4} g =
      g p + g (p + 1) + g (p + 2) + g (p + 3) := by
    intro g hg4
    have hfin : ({i : ℕ | i < 4} : Set ℕ).Finite := Set.finite_lt_nat 4
    have hset : setSum {i : ℕ | i < 4} g = ∑ x ∈ Finset.range 4, g x := by
      rw [setSum, dif_pos hfin]
      congr 1
      ext x; simp
    rw [hset, ← periodic_sum hg4 (by norm_num) p]
    have hI : Finset.Icc p (4 - 1 + p) = ({p, p + 1, p + 2, p + 3} : Finset ℕ) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hI]
    rw [Finset.sum_insert (by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; omega)]
    rw [Finset.sum_insert (by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; omega)]
    rw [Finset.sum_insert (by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; omega)]
    rw [Finset.sum_singleton]
    ring
  have hpergv : periodic (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))) 4 := by
    intro i
    show rhoFun ‖v (i + 4)‖ * azim 0 (v (i + 4)) (v (i + 4 + 1)) (v (i + 4 + 3)) =
      rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))
    rw [show i + 4 + 1 = (i + 1) + 4 by omega, show i + 4 + 3 = (i + 3) + 4 by omega,
      hperv i, hperv (i + 1), hperv (i + 3)]
  have hpergw : periodic (fun i => rhoFun ‖f (v i) t‖ *
      azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) 4 := by
    intro i
    show rhoFun ‖f (v (i + 4)) t‖ * azim 0 (f (v (i + 4)) t) (f (v (i + 4 + 1)) t)
        (f (v (i + 4 + 3)) t) =
      rhoFun ‖f (v i) t‖ * azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)
    rw [show i + 4 + 1 = (i + 1) + 4 by omega, show i + 4 + 3 = (i + 3) + 4 by omega,
      hperv i, hperv (i + 1), hperv (i + 3)]
  have hSv := hsum4 (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))) hpergv
  have hSw := hsum4 (fun i => rhoFun ‖f (v i) t‖ *
    azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) hpergw
  have hmin' : setSum {i : ℕ | i < 4} (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3)))
      ≤ setSum {i : ℕ | i < 4} (fun i => rhoFun ‖f (v i) t‖ *
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) := by
    simpa only using hmin
  -- ═══ K. name the azimuth atoms ═══
  set A013 : ℝ := azim 0 (v p) (v (p + 1)) (v (p + 3)) with hA013
  set A120 : ℝ := azim 0 (v (p + 1)) (v (p + 2)) (v p) with hA120
  set B301 : ℝ := azim 0 (v (p + 3)) (v p) (v (p + 2)) with hB301
  set A312 : ℝ := azim 0 (v (p + 3)) (v (p + 1)) (v (p + 2)) with hA312
  set A231 : ℝ := azim 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) with hA231
  set A301 : ℝ := azim 0 (v (p + 3)) (v p) (v (p + 1)) with hA301
  set A123 : ℝ := azim 0 (v (p + 1)) (v (p + 2)) (v (p + 3)) with hA123
  set D : ℝ := azim 0 (v (p + 1)) (v (p + 3)) (v p) with hD
  set F013 : ℝ := azim 0 (f (v p) t) (v (p + 1)) (v (p + 3)) with hF013
  set F120 : ℝ := azim 0 (v (p + 1)) (v (p + 2)) (f (v p) t) with hF120
  set F301 : ℝ := azim 0 (v (p + 3)) (f (v p) t) (v (p + 2)) with hF301
  set G301 : ℝ := azim 0 (v (p + 3)) (f (v p) t) (v (p + 1)) with hG301
  set D' : ℝ := azim 0 (v (p + 1)) (v (p + 3)) (f (v p) t) with hD'
  have hgv_exp : setSum {i : ℕ | i < 4}
      (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))) =
      rhoFun y2 * A013 + rhoFun y3 * A120 + rhoFun y1 * B301 +
        rhoFun ‖v (p + 2)‖ * A231 := by
    rw [hSv]
    rw [show p + 1 + 3 = p + 4 by omega, hperv p, show p + 2 + 3 = (p + 1) + 4 by omega,
      hperv (p + 1), show p + 3 + 3 = p + 6 by omega, show p + 6 = (p + 2) + 4 by omega,
      hperv (p + 2),
      ← hy1def, ← hy2def, ← hy3def, ← hA120, ← hB301, ← hA231]
    ring
  have hgw_exp : setSum {i : ℕ | i < 4} (fun i => rhoFun ‖f (v i) t‖ *
      azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) =
      rhoFun y2 * F013 + rhoFun y3 * F120 + rhoFun y1 * F301 +
        rhoFun ‖v (p + 2)‖ * A231 := by
    rw [hSw]
    rw [show p + 1 + 1 = p + 2 by omega, show p + 1 + 3 = p + 4 by omega,
      show p + 3 + 1 = p + 4 by omega, show p + 3 + 3 = p + 6 by omega,
      show p + 6 = (p + 2) + 4 by omega, show p + 2 + 3 = (p + 1) + 4 by omega,
      hperv p, hperv (p + 1), hperv (p + 2),
      hfix (v (p + 1)) t (hne_vp (p + 1) (by omega)),
      hfix (v (p + 2)) t (hne_vp (p + 2) (by omega)),
      hfix (v (p + 3)) t (hne_vp (p + 3) (by omega)),
      hnormf p t (h7e' t htabs), ← hy1def, ← hy2def, ← hy3def,
      ← hF013, ← hF120, ← hF301, ← hA231]
    ring
  -- ═══ L. the strict-drop contradiction ═══
  have hcmp : rhoFun y2 * A013 + rhoFun y3 * A120 + rhoFun y1 * B301
      ≤ rhoFun y2 * F013 + rhoFun y3 * F120 + rhoFun y1 * F301 := by
    have h := hmin'
    rw [hgv_exp, hgw_exp] at h
    linarith
  have hA120_split : A120 = A123 + D := hsum2
  have hF120_split : F120 = A123 + D' := by
    have hsumB := (hBall t (h7eB t htabs)).2.2.2
    rw [hfix (v (p + 1)) t (hne_vp (p + 1) (by omega)),
      hfix (v (p + 2)) t (hne_vp (p + 2) (by omega)),
      hfix (v (p + 3)) t (hne_vp (p + 3) (by omega))] at hsumB
    exact hsumB.symm
  have hB301_split : B301 = A301 + A312 := hsum1
  have hF301_split : F301 = G301 + A312 := by
    have hsumA := (hAall t (h7eA t htabs)).2.2.2
    rw [hfix (v (p + 3)) t (hne_vp (p + 3) (by omega)),
      hfix (v (p + 1)) t (hne_vp (p + 1) (by omega)),
      hfix (v (p + 2)) t (hne_vp (p + 2) (by omega))] at hsumA
    exact hsumA.symm
  have hWC : azim 0 (f (v p) t) (v (p + 1)) (v (p + 3)) < Real.pi := by
    have h := hWall t (h7eW t htabs)
    rwa [hfix (v (p + 1)) t (hne_vp (p + 1) (by omega)),
      hfix (v (p + 3)) t (hne_vp (p + 3) (by omega))] at h
  have hGle : azim 0 (v (p + 3)) (f (v p) t) (v (p + 1)) ≤ Real.pi := by
    have hnc1 : ¬ Collinear ℝ ({0, f (v p) t, v (p + 1)} : Set V3) :=
      (notcoplanar_imp_notcollinear_fan (x := (0 : V3)) (v := f (v p) t)
        (u := v (p + 1)) (w := v (p + 3)) (hNP t (h7eNP t htabs))).2.1
    have hnc2 : ¬ Collinear ℝ ({0, f (v p) t, v (p + 3)} : Set V3) :=
      (notcoplanar_imp_notcollinear_fan (x := (0 : V3)) (v := f (v p) t)
        (u := v (p + 1)) (w := v (p + 3)) (hNP t (h7eNP t htabs))).2.2
    have hposW : 0 < azim 0 (f (v p) t) (v (p + 1)) (v (p + 3)) := by
      have h := LOCAL_FAN_AZIM_POS_p22 s (fun i => f (v i) t) p
        (by
          rcases hw.2.2.2 with hle | hcl
          · omega
          · exact hcl)
        hs' hw
      rw [hk] at h
      simp only [Nat.reduceSub] at h
      rwa [hfix (v (p + 1)) t (hne_vp (p + 1) (by omega)),
        hfix (v (p + 3)) t (hne_vp (p + 3) (by omega))] at h
    exact le_of_lt (g482w3_azim_cycle (x := f (v p) t) (y := v (p + 1)) (z := v (p + 3))
      hnc1 hnc2 hposW hWC).2.2
  have htau_base : taum y1 y2 y3 y4 y5 y6 =
      rho y2 * A013 + rho y3 * D + rho y1 * A301 - (Real.pi + sol0) := by
    rw [g482w3_taum_cyc y1 y2 y3 y4 y5 y6,
      ← tau3_taum_nonplanar_p21 (v p) (v (p + 1)) (v (p + 3)) hncop,
      tau3_azim_p21 (v p) (v (p + 1)) (v (p + 3)) hncop (le_of_lt ha013_lt)]
  have hd4 : dist (f (v p) t) (v (p + 1)) = y4' := by
    rw [dist_comm, hdist2 _ (h7e' _ htabs)]
    rw [show dist (v (p + 1)) (v p) = y4 from by rw [dist_comm, ← hy4def], ← hy4'eq]
  have htaum_congr : taum y1 y2 y3 y4' y5 y6 =
      taum ‖f (v p) t‖ ‖v (p + 1)‖ ‖v (p + 3)‖ (dist (v (p + 1)) (v (p + 3)))
        (dist (f (v p) t) (v (p + 3))) (dist (f (v p) t) (v (p + 1))) := by
    rw [g482w3_taum_cyc y1 y2 y3 y4' y5 y6]
    rw [hy2def, hnormf p t (h7e' t htabs), hy3def, hy1def, hy5def, hy6def,
      dist_comm (v p) (v (p + 3)), ← hdist1 _ (h7e' _ htabs),
      dist_comm (v (p + 3)) (f (v p) t), ← hd4]
  have htau_def : taum y1 y2 y3 y4' y5 y6 =
      rho y2 * F013 + rho y3 * D' + rho y1 * G301 - (Real.pi + sol0) := by
    rw [htaum_congr,
      ← tau3_taum_nonplanar_p21 (f (v p) t) (v (p + 1)) (v (p + 3))
        (hNP t (h7eNP t htabs)),
      tau3_azim_p21 (f (v p) t) (v (p + 1)) (v (p + 3)) (hNP t (h7eNP t htabs))
        (le_of_lt hWC)]
    rw [hnormf p t (h7e' t htabs), ← hy1def, ← hy2def, ← hy3def, ← hF013, ← hD', ← hG301]
  have hcmp_rho : rho y2 * A013 + rho y3 * A120 + rho y1 * B301
      ≤ rho y2 * F013 + rho y3 * F120 + rho y1 * F301 := by
    simpa only [rho_rho_fun] using hcmp
  have hstep : rho y2 * A013 + rho y3 * D + rho y1 * A301
      ≤ rho y2 * F013 + rho y3 * D' + rho y1 * G301 := by
    have h := hcmp_rho
    rw [hA120_split, hF120_split, hB301_split, hF301_split] at h
    linarith [h]
  have hmain : taum y1 y2 y3 y4 y5 y6 ≤ taum y1 y2 y3 y4' y5 y6 := by
    rw [htau_base, htau_def]
    linarith [hstep]
  linarith [hy4'lt]

set_option maxHeartbeats 6000000 in
/-- HOL `BZQNDMN` (JOTSWIX.hl:1679): the `NEHXMWH` twin for the
`(p+3)`-opposite interior angles. NEEDS: same kit as `NEHXMWH_p23`. -/
theorem BZQNDMN_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (FF : Set (V3 × V3)) (v : ℕ → V3) (p : ℕ)
    (hFF : (fun i : ℕ => (v i, v (i + 1))) '' Set.univ = FF)
    (hs : isScsV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s) (hb : scsBasicV39 s)
    (hg : scsGeneric v)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hang : ∀ i, i % 4 ≠ (p + 3) % 4 → interiorAngle1 0 FF (v i) < Real.pi) :
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∨
      dist (v p) (v (p + 1)) = s.b p (p + 1) := by
  -- ═══ A. substrate: `BBs_v39` from `MMs_v39`, fan data, azimuth forms ═══
  have hs' : isScsV39 s := hs
  obtain ⟨-, hk3le, -, -, -, -, -, hpa, -, -, hpbP, -, hsym, hch, hdiag0, hdiag, -, hbc, -, -, -⟩ := hs
  have hk4pos : 0 < (4 : ℕ) := by norm_num
  have hvBBp : v ∈ BBprimeV39 s := by
    have h2 : v ∈ BBprime2V39 s := by
      have h1 := hMM
      simp only [MMsV39, Set.mem_setOf_eq] at h1
      exact h1.1
    have h3 := h2
    simp only [BBprime2V39, Set.mem_setOf_eq] at h3
    exact h3.1
  obtain ⟨hBBs, hvmin, hvneg⟩ := by
    have h3 := hvBBp
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3
  have hBBs' : BBsV39 s v := hBBs
  obtain ⟨hann, hpervS, hbnd, hconv0⟩ := hBBs
  have hperv : Periodic v 4 := by rw [← hk]; exact hpervS
  have hmod : ∀ i : ℕ, v (i % 4) = v i := fun i => periodic_mod_eq_p23 hperv i
  have hinj : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j :=
    BBs_inj_p21 s v 4 hs' hk hBBs'
  have hmodv1 : ∀ i : ℕ, v i = v (p + 1) → i % 4 = (p + 1) % 4 := by
    intro i hi
    exact hinj (i % 4) ((p + 1) % 4) (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos)
      (by rw [hmod i, hmod (p + 1)]; exact hi)
  have hne_vp1 : ∀ i : ℕ, i % 4 ≠ (p + 1) % 4 → v i ≠ v (p + 1) :=
    fun i h hc => h (hmodv1 i hc)
  have hFFr : Set.range (fun i : ℕ => (v i, v (i + 1))) = FF := by
    simpa only [Set.image_univ] using hFF
  have hconv : ConvexLocalFan (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3))
      (Set.range fun i => (v i, v (i + 1))) := by
    rcases hconv0 with hle | hcl
    · omega
    · exact hcl
  have hlf := hconv.1
  have hvmem : ∀ i : ℕ, v i ∈ Set.range v := fun i => Set.mem_range_self i
  have hazim : ∀ i : ℕ, interiorAngle1 0 FF (v i) = azim 0 (v i) (v (i + 1)) (v (i + 3)) := by
    intro i
    have h1 := INTERIOR_ANGLE1_AZIM_p22 s v i hs' hBBs' (show 3 < s.k by omega) FF hFFr.symm
    rw [hk] at h1
    exact h1.symm
  have hpos : ∀ i : ℕ, 0 < azim 0 (v i) (v (i + 1)) (v (i + 3)) := by
    intro i
    have h1 := LOCAL_FAN_AZIM_POS_p22 s v i hconv hs' hBBs'
    rw [hk] at h1
    exact h1
  have hnc : ∀ i j : ℕ, i % 4 ≠ j % 4 → ¬ Collinear ℝ ({0, v i, v j} : Set V3) := by
    intro i j hij
    have hne : v i ≠ v j := by
      intro he
      exact hij (hinj (i % 4) (j % 4) (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos)
        (by rw [hmod i, hmod j]; exact he))
    have hgen : Generic (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)) := by
      simpa only [scsGeneric] using hg
    exact PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 _ _ _ _ _ hlf (hvmem i) (hvmem j) hne hgen
  -- ═══ B. the azimuths at `p`, `p+1`, `p+2` and the coplanarity of the quad ═══
  have hpp3 : p % 4 ≠ (p + 3) % 4 := by omega
  have ha013_lt : azim 0 (v p) (v (p + 1)) (v (p + 3)) < Real.pi := by
    have h1 := hang p hpp3
    rwa [hazim p] at h1
  have ha013_pos : 0 < azim 0 (v p) (v (p + 1)) (v (p + 3)) := hpos p
  have hB_lt : azim 0 (v (p + 1)) (v (p + 2)) (v p) < Real.pi := by
    have h1 := hang (p + 1) (by omega : (p + 1) % 4 ≠ (p + 3) % 4)
    rw [hazim (p + 1)] at h1
    rwa [show (p + 1) + 1 = p + 2 by omega, show (p + 1) + 3 = p + 4 by omega,
      hperv p] at h1
  have hB_pos : 0 < azim 0 (v (p + 1)) (v (p + 2)) (v p) := by
    have h := hpos (p + 1)
    rwa [show (p + 1) + 1 = p + 2 by omega, show (p + 1) + 3 = p + 4 by omega,
      hperv p] at h
  have hC_pos : 0 < azim 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) := by
    have h := hpos (p + 2)
    rwa [show (p + 2) + 1 = p + 3 by omega, show (p + 2) + 3 = p + 5 by omega,
      show p + 5 = (p + 1) + 4 by omega, hperv (p + 1)] at h
  have hC_lt : azim 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) < Real.pi := by
    have h1 := hang (p + 2) (by omega : (p + 2) % 4 ≠ (p + 3) % 4)
    rw [hazim (p + 2)] at h1
    rwa [show (p + 2) + 1 = p + 3 by omega, show (p + 2) + 3 = p + 5 by omega,
      show p + 5 = (p + 1) + 4 by omega, hperv (p + 1)] at h1
  have hnc_pp1 : ¬ Collinear ℝ ({0, v p, v (p + 1)} : Set V3) := hnc p (p + 1) (by omega)
  have hnc_pp2 : ¬ Collinear ℝ ({0, v p, v (p + 2)} : Set V3) := hnc p (p + 2) (by omega)
  have hnc_pp3 : ¬ Collinear ℝ ({0, v p, v (p + 3)} : Set V3) := hnc p (p + 3) (by omega)
  have hB_cycle := g482w3_azim_cycle (x := v (p + 1)) (y := v (p + 2)) (z := v p)
    (hnc (p + 1) (p + 2) (by omega)) (hnc (p + 1) p (by omega)) hB_pos hB_lt
  have hA201_pos : 0 < azim 0 (v (p + 2)) (v p) (v (p + 1)) := hB_cycle.1.1
  have hA201_lt : azim 0 (v (p + 2)) (v p) (v (p + 1)) < Real.pi := hB_cycle.1.2
  have hA012_pos : 0 < azim 0 (v p) (v (p + 1)) (v (p + 2)) := hB_cycle.2.1
  have hA012_lt : azim 0 (v p) (v (p + 1)) (v (p + 2)) < Real.pi := hB_cycle.2.2
  have hncop : ¬ Coplanar ({0, v p, v (p + 1), v (p + 2)} : Set V3) := by
    intro hc
    have hc' : Coplanar ({0, v (p + 1), v (p + 2), v p} : Set V3) := by
      rw [show ({0, v (p + 1), v (p + 2), v p} : Set V3) =
        {0, v p, v (p + 1), v (p + 2)} from by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
      exact hc
    rcases (AZIM_COND_FOR_COPLANAR (0 : V3) (v (p + 1)) (v (p + 2)) (v p)).mpr hc' with h0 | hpi
    · linarith
    · linarith
  -- ═══ C. the edge deformation at `v (p+1)` (HOL `deform_simplex_edge_exists`) ═══
  have hcross : (v (p + 1)) ⬝ᵥ cross3 (v (p + 2)) (v p) > 0 := by
    have h := (azim_lt_pi_cross_p14 (v (p + 1)) (v (p + 2)) (v p)).mp ⟨hB_pos, hB_lt⟩
    rw [show cross3 (v (p + 1)) (v (p + 2)) ⬝ᵥ v p
          = (v (p + 1)) ⬝ᵥ cross3 (v (p + 2)) (v p) from by
        rw [show cross3 (v (p + 1)) (v (p + 2)) ⬝ᵥ v p
              = cross3 (v (p + 2)) (v p) ⬝ᵥ v (p + 1) from by
            simpa only [cross3] using g482w3_cross_det_cyc (v (p + 1)) (v (p + 2)) (v p),
          dotProduct_comm]] at h
    exact h
  obtain ⟨f, hf⟩ := deform_simplex_edge_exists_p21 (Set.range v) (fun t => t) (fun _ => 0)
    (v p) (v (p + 1)) (v (p + 2)) 1
  obtain ⟨e', he'pos, hdef, hfix, hdistf⟩ := hf hncop hcross (by norm_num)
    (by fun_prop) (by fun_prop) (by simp) (by simp)
  have hdist1 : ∀ t : ℝ, |t| < e' →
      dist (v p) (f (v (p + 1)) t) = dist (v p) (v (p + 1)) + t :=
    fun t ht => (hdistf t ht).1
  have hdist2 : ∀ t : ℝ, |t| < e' →
      dist (v (p + 2)) (f (v (p + 1)) t) = dist (v (p + 2)) (v (p + 1)) :=
    fun t ht => by simpa using (hdistf t ht).2.1
  have hnormf : ∀ (i : ℕ) (t : ℝ), |t| < e' → ‖f (v i) t‖ = ‖v i‖ := by
    intro i t ht
    by_cases hi : v i = v (p + 1)
    · rw [hi]; exact (hdistf t ht).2.2
    · rw [hfix _ t hi]
  have hdiag4 : ∀ i j, scsDiag 4 i j → s.a i j < dist (v i) (v j) ∧ 4 * h0 < s.b i j := by
    intro i j hd
    obtain ⟨h1, h2, h3⟩ := hdg i j hd
    exact ⟨lt_of_le_of_lt h1 h2, h3⟩
  -- ═══ D. assume the strict interior case, derive `hab` ═══
  by_contra hcon
  push_neg at hcon
  obtain ⟨hneA, hneB⟩ := hcon
  have hab : s.a p (p + 1) < dist (v p) (v (p + 1)) ∧
      dist (v p) (v (p + 1)) < s.b p (p + 1) :=
    ⟨lt_of_le_of_ne (hbnd p (p + 1)).1 (Ne.symm hneA),
      lt_of_le_of_ne (hbnd p (p + 1)).2 hneB⟩
  have hdistsym : ∀ t : ℝ, |t| < e' →
      dist (f (v (p + 1)) t) (v (p + 2)) = dist (v (p + 1)) (v (p + 2)) := by
    intro t ht
    rw [dist_comm (f (v (p + 1)) t) (v (p + 2)), dist_comm (v (p + 1)) (v (p + 2))]
    exact hdist2 t ht
  obtain ⟨ha_ab, hb_ab⟩ :=
    ab4_assumption_reduction_sym_p23 s p f v e' hs' hk hBBs' hdiag4 hdef he'pos hfix
      hdistsym hab
  -- ═══ E. the flat-angle skolem for `deformation_BBs_ALT` ═══
  have hsucc : ∀ {i j : ℕ}, v i = v j → v (i + 1) = v (j + 1) := by
    intro i j hij
    have h1 : i % 4 = j % 4 :=
      hinj _ _ (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos) (by rw [hmod i, hmod j]; exact hij)
    have h2 : (i + 1) % 4 = (j + 1) % 4 := by omega
    rw [← hmod (i + 1), ← hmod (j + 1), h2]
  have hadd3 : ∀ {i j : ℕ}, v i = v j → v (i + 3) = v (j + 3) := by
    intro i j hij
    have h1 : i % 4 = j % 4 :=
      hinj _ _ (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos) (by rw [hmod i, hmod j]; exact hij)
    have h2 : (i + 3) % 4 = (j + 3) % 4 := by omega
    rw [← hmod (i + 3), ← hmod (j + 3), h2]
  have hazPi : ∀ i : ℕ, ∃ e0 : ℝ, 0 < e0 ∧
      (azim 0 (v i) (v (i + 1)) (v (i + (4 - 1))) = Real.pi →
        ∀ t : ℝ, |t| < e0 →
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (4 - 1))) t) ≤ Real.pi) := by
    intro i
    by_cases hi : v i = v (p + 3)
    · have h1 : v (i + 1) = v p := by
        have h := hsucc hi
        rw [show p + 3 + 1 = p + 4 by omega, hperv p] at h
        exact h
      have h3 : v (i + (4 - 1)) = v (p + 2) := by
        have h := hadd3 hi
        rw [show p + 3 + 3 = (p + 2) + 4 by omega, hperv (p + 2)] at h
        exact h
      have hne3 : v (p + 3) ≠ v (p + 1) := hne_vp1 (p + 3) (by omega)
      have hne0 : v p ≠ v (p + 1) := hne_vp1 p (by omega)
      have hne2 : v (p + 2) ≠ v (p + 1) := hne_vp1 (p + 2) (by omega)
      refine ⟨1, by norm_num, fun hpi t _ => ?_⟩
      rw [hi, h1, h3] at hpi ⊢
      rw [hfix _ t hne3, hfix _ t hne0, hfix _ t hne2]
      exact le_of_eq hpi
    · have hmodne : i % 4 ≠ (p + 3) % 4 := by
        intro hc
        exact hi (by rw [← hmod i, ← hmod (p + 3), hc])
      have hlt : azim 0 (v i) (v (i + 1)) (v (i + 3)) < Real.pi := by
        have h1 := hang i hmodne
        rwa [hazim i] at h1
      refine ⟨1, by norm_num, fun hpi _ _ => ?_⟩
      exact absurd hpi (ne_of_lt hlt)
  obtain ⟨eBB, heBB, hBBdef⟩ :=
    deformation_BBs_ALT_p21 s 4 f v e' hs' hk (by norm_num) hBBs' hg he'pos hdef hazPi hnormf
      ha_ab hb_ab
  -- ═══ F. the first azimuth sum (quad `p, p+1, p+2, p+3`) ═══
  have hdef4 : Deformation f ({v p, v (p + 1), v (p + 2), v (p + 3)} : Set V3) (-e') e' := by
    refine deformation_subset_p14 f _ (Set.range v) (-e') e' ?_ hdef
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Set.mem_range_self _
  have hsum1 : azim 0 (v p) (v (p + 1)) (v (p + 3)) =
      azim 0 (v p) (v (p + 1)) (v (p + 2)) + azim 0 (v p) (v (p + 2)) (v (p + 3)) := by
    have hnc1 : ¬ Collinear ℝ ({0, v p, v (p + 2)} : Set V3) := hnc_pp2
    have hnc2 : ¬ Collinear ℝ ({0, v p, v (p + 4 - 1)} : Set V3) := by
      have e : v (p + 4 - 1) = v (p + 3) := by
        rw [show p + 4 - 1 = p + 3 by omega]
      rw [e]; exact hnc_pp3
    have hnc3 : ¬ Collinear ℝ ({0, v p, v (p + 1)} : Set V3) := hnc_pp1
    have hinj' : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j := hinj
    have h := vv_split_azim_alt_p21 (vv := v) (k := 4) (i := p) (j := p + 2)
      hperv (by norm_num) hnc1 hnc2 hnc3 hconv hinj'
    rw [show p + 4 - 1 = p + 3 by omega] at h
    exact h
  have hcase1 : ((∀ t : ℝ, azim 0 (f (v p) t) (f (v (p + 1)) t) (f (v (p + 2)) t) =
        azim 0 (v p) (v (p + 1)) (v (p + 2))) ∧
      0 < azim 0 (v p) (v (p + 2)) (v (p + 3)) ∧
        azim 0 (v p) (v (p + 2)) (v (p + 3)) < Real.pi) ∨
      ((∀ t : ℝ, azim 0 (f (v p) t) (f (v (p + 2)) t) (f (v (p + 3)) t) =
        azim 0 (v p) (v (p + 2)) (v (p + 3))) ∧
      0 < azim 0 (v p) (v (p + 1)) (v (p + 2)) ∧
        azim 0 (v p) (v (p + 1)) (v (p + 2)) < Real.pi) := by
    refine Or.inr ⟨?_, hA012_pos, hA012_lt⟩
    intro t
    rw [hfix (v p) t (hne_vp1 p (by omega)),
      hfix (v (p + 2)) t (hne_vp1 (p + 2) (by omega)),
      hfix (v (p + 3)) t (hne_vp1 (p + 3) (by omega))]
  obtain ⟨eA, heA, hAall⟩ := deform_azim_sum_p23 (v p) (v (p + 1)) (v (p + 2)) (v (p + 3))
    f e' hdef4 ha013_pos ha013_lt hnc_pp1 hnc_pp2 hnc_pp3 hsum1.symm hcase1
  -- ═══ G. the second azimuth sum (quad `p+2, p+3, p, p+1`) ═══
  have hdef4' : Deformation f ({v (p + 2), v (p + 3), v p, v (p + 1)} : Set V3) (-e') e' := by
    refine deformation_subset_p14 f _ (Set.range v) (-e') e' ?_ hdef
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Set.mem_range_self _
  have hsum2 : azim 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) =
      azim 0 (v (p + 2)) (v (p + 3)) (v p) + azim 0 (v (p + 2)) (v p) (v (p + 1)) := by
    have hnc1 : ¬ Collinear ℝ ({0, v (p + 2), v p} : Set V3) :=
      hnc (p + 2) p (by omega)
    have hnc2 : ¬ Collinear ℝ ({0, v (p + 2), v ((p + 2) + (4 - 1))} : Set V3) := by
      have e : v ((p + 2) + (4 - 1)) = v (p + 1) := by
        rw [show (p + 2) + (4 - 1) = (p + 1) + 4 by omega, hperv (p + 1)]
      rw [e]; exact hnc (p + 2) (p + 1) (by omega)
    have hnc3 : ¬ Collinear ℝ ({0, v (p + 2), v (p + 3)} : Set V3) :=
      hnc (p + 2) (p + 3) (by omega)
    have hinj' : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j := hinj
    have h := vv_split_azim_alt_p21 (vv := v) (k := 4) (i := p + 2) (j := p)
      hperv (by norm_num) hnc1 hnc2 hnc3 hconv hinj'
    rw [show (p + 2) + 4 - 1 = p + 5 by omega, show p + 5 = (p + 1) + 4 by omega,
      hperv (p + 1)] at h
    exact h
  have hcase2 : ((∀ t : ℝ, azim 0 (f (v (p + 2)) t) (f (v (p + 3)) t) (f (v p) t) =
        azim 0 (v (p + 2)) (v (p + 3)) (v p)) ∧
      0 < azim 0 (v (p + 2)) (v p) (v (p + 1)) ∧
        azim 0 (v (p + 2)) (v p) (v (p + 1)) < Real.pi) ∨
      ((∀ t : ℝ, azim 0 (f (v (p + 2)) t) (f (v p) t) (f (v (p + 1)) t) =
        azim 0 (v (p + 2)) (v p) (v (p + 1))) ∧
      0 < azim 0 (v (p + 2)) (v (p + 3)) (v p) ∧
        azim 0 (v (p + 2)) (v (p + 3)) (v p) < Real.pi) := by
    refine Or.inl ⟨?_, hA201_pos, hA201_lt⟩
    intro t
    rw [hfix (v (p + 2)) t (hne_vp1 (p + 2) (by omega)),
      hfix (v (p + 3)) t (hne_vp1 (p + 3) (by omega)),
      hfix (v p) t (hne_vp1 p (by omega))]
  obtain ⟨eB, heB, hBall⟩ := deform_azim_sum_p23 (v (p + 2)) (v (p + 3)) (v p) (v (p + 1))
    f e' hdef4' hC_pos hC_lt (hnc (p + 2) (p + 3) (by omega)) (hnc (p + 2) p (by omega))
      (hnc (p + 2) (p + 1) (by omega)) hsum2.symm hcase2
  -- ═══ H. nonplanarity stays open along the deformation ═══
  have hcont0 : ContinuousAt (fun t => f (v (p + 1)) t) 0 :=
    hdef.2.1 (v (p + 1)) (Set.mem_range_self (p + 1)) 0 hdef.1
  obtain ⟨eNP, heNP, hNPall⟩ := NONPLANAR_OPEN_p14 (fun _ => (0 : V3)) (fun _ => v p)
    (fun t => f (v (p + 1)) t) (fun _ => v (p + 2)) 0
    (by
      have hset : ({0, v p, f (v (p + 1)) 0, v (p + 2)} : Set V3) =
          {0, v p, v (p + 1), v (p + 2)} := by
        rw [hdef.2.2 (v (p + 1)) (Set.mem_range_self (p + 1))]
      rwa [hset])
    continuousAt_const continuousAt_const hcont0 continuousAt_const
  have hNP : ∀ t : ℝ, |t| < eNP →
      ¬ Coplanar ({0, v p, f (v (p + 1)) t, v (p + 2)} : Set V3) := by
    intro t ht
    exact hNPall t (by rwa [zero_sub, abs_neg])
  -- ═══ I. combine the epsilons ═══
  have hdef3 : Deformation f ({v p, v (p + 1), v (p + 2)} : Set V3) (-e') e' := by
    refine deformation_subset_p14 f _ (Set.range v) (-e') e' ?_ hdef
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact Set.mem_range_self _
  have hncF1 : ¬ Collinear ℝ ({0, f (v (p + 1)) 0, f (v (p + 2)) 0} : Set V3) := by
    rw [hfix (v (p + 2)) 0 (hne_vp1 (p + 2) (by omega)),
      hdef.2.2 (v (p + 1)) (Set.mem_range_self (p + 1))]
    exact hnc (p + 1) (p + 2) (by omega)
  have hncF3 : ¬ Collinear ℝ ({0, f (v (p + 1)) 0, f (v p) 0} : Set V3) := by
    rw [hfix (v p) 0 (hne_vp1 p (by omega)),
      hdef.2.2 (v (p + 1)) (Set.mem_range_self (p + 1))]
    exact hnc (p + 1) p (by omega)
  obtain ⟨eW, heW, hWall⟩ := WNWSHJT_p14 (v p) (v (p + 1)) (v (p + 2)) f (-e') e'
    hdef3 hncF1 hncF3 hB_pos hB_lt
  obtain ⟨e1, he1, h1e', h1eBB, h1eA⟩ := epsilon_triple_p21 e' eBB eA he'pos heBB heA
  obtain ⟨e2, he2, h2e1, h2eB, h2eNP⟩ := epsilon_triple_p21 e1 eB eNP he1 heB heNP
  obtain ⟨e3', he3', h3'e2, h3'eW⟩ := epsilon_pair_p21 e2 eW he2 heW
  obtain ⟨e7, he7, h7e3, h71⟩ := epsilon_pair_p21 e3' 1 he3' (by norm_num)
  have h7e' : ∀ t : ℝ, |t| < e7 → |t| < e' :=
    fun t ht => h1e' t (h2e1 t (h3'e2 t (h7e3 t ht)))
  have h7eBB : ∀ t : ℝ, |t| < e7 → |t| < eBB :=
    fun t ht => h1eBB t (h2e1 t (h3'e2 t (h7e3 t ht)))
  have h7eA : ∀ t : ℝ, |t| < e7 → |t| < eA :=
    fun t ht => h1eA t (h2e1 t (h3'e2 t (h7e3 t ht)))
  have h7eB : ∀ t : ℝ, |t| < e7 → |t| < eB :=
    fun t ht => h2eB t (h3'e2 t (h7e3 t ht))
  have h7eNP : ∀ t : ℝ, |t| < e7 → |t| < eNP :=
    fun t ht => h2eNP t (h3'e2 t (h7e3 t ht))
  have h7eW : ∀ t : ℝ, |t| < e7 → |t| < eW := fun t ht => h3'eW t (h7e3 t ht)
  -- ═══ J. norms and the `LEMMA_1834976363` box ═══
  have hnorm_lo : ∀ i : ℕ, 2 ≤ ‖v i‖ := by
    intro i
    have h := hann (Set.mem_range_self i)
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at h
    linarith [h.1, h.2]
  have hnorm_hi : ∀ i : ℕ, ‖v i‖ ≤ 2 * h0 := by
    intro i
    have h := hann (Set.mem_range_self i)
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at h
    linarith [h.1, h.2]
  set y1 : ℝ := ‖v (p + 2)‖ with hy1def
  set y2 : ℝ := ‖v p‖ with hy2def
  set y3 : ℝ := ‖v (p + 1)‖ with hy3def
  set y4 : ℝ := dist (v p) (v (p + 1)) with hy4def
  set y5 : ℝ := dist (v (p + 2)) (v (p + 1)) with hy5def
  set y6 : ℝ := dist (v (p + 2)) (v p) with hy6def
  have hy1lo : 2 ≤ y1 := by rw [hy1def]; exact hnorm_lo _
  have hy1hi : y1 ≤ 2 * h0 := by rw [hy1def]; exact hnorm_hi _
  have hy2lo : 2 ≤ y2 := by rw [hy2def]; exact hnorm_lo _
  have hy2hi : y2 ≤ 2 * h0 := by rw [hy2def]; exact hnorm_hi _
  have hy3lo : 2 ≤ y3 := by rw [hy3def]; exact hnorm_lo _
  have hy3hi : y3 ≤ 2 * h0 := by rw [hy3def]; exact hnorm_hi _
  have hy4lo : 2 ≤ y4 := by
    rw [hy4def]
    exact scs_lb_2_p22 s v p (p + 1) hs' hBBs' (by rw [hk]; omega)
  have hy5lo : 2 ≤ y5 := by
    rw [hy5def]
    exact scs_lb_2_p22 s v (p + 2) (p + 1) hs' hBBs' (by rw [hk]; omega)
  have hy6lo : 2 ≤ y6 := by
    rw [hy6def]
    exact scs_lb_2_p22 s v (p + 2) p hs' hBBs' (by rw [hk]; omega)
  have hy4le : y4 ≤ Real.sqrt 15.53 := by
    rw [hy4def]
    have h1 : dist (v p) (v (p + 1)) ≤ s.b p (p + 1) := (hbnd p (p + 1)).2
    have h2 : s.b p (p + 1) ≤ cstab := hbc p (by omega)
    have h3 : cstab ≤ Real.sqrt 15.53 := by
      have hc : cstab = (3.01 : ℝ) := rfl
      have hsq : (Real.sqrt 15.53) ^ 2 = 15.53 := Real.sq_sqrt (by norm_num)
      have hnn : (0 : ℝ) ≤ Real.sqrt 15.53 := Real.sqrt_nonneg _
      rw [hc]
      nlinarith
    linarith
  have hsqrt4 : Real.sqrt 15.53 < 4 := by
    have h : Real.sqrt 15.53 < Real.sqrt 16 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show Real.sqrt 16 = 4 from by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hx4 : (2 / h0) ^ 2 ≤ xrr y2 y3 y4 ∧ xrr y2 y3 y4 ≤ 15.53 := by
    constructor
    · exact xrr_simple_lower_bound_p22 y2 y3 y4 2 hy2lo hy2hi hy3lo hy3hi (by norm_num) hy4lo
    · have h := xrr_simple_upper_bound_p22 y2 y3 y4 (Real.sqrt 15.53)
        hy2lo hy2hi hy3lo hy3hi hy4lo hy4le hsqrt4
      rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15.53)] at h
  have hx5 : (2 / h0) ^ 2 ≤ xrr y1 y3 y5 :=
    xrr_simple_lower_bound_p22 y1 y3 y5 2 hy1lo hy1hi hy3lo hy3hi (by norm_num) hy5lo
  have hx6 : (2 / h0) ^ 2 ≤ xrr y1 y2 y6 :=
    xrr_simple_lower_bound_p22 y1 y2 y6 2 hy1lo hy1hi hy2lo hy2hi (by norm_num) hy6lo
  have hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6) := by
    have h := g482w3_upsX_pos_of_not_col (a := (0 : V3)) (b := v (p + 2)) (c := v p)
      (hnc (p + 2) p (by omega))
    have e1 : dist (0 : V3) (v (p + 2)) = y1 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy1def]
    have e2 : dist (0 : V3) (v p) = y2 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy2def]
    have e4 : dist (v (p + 2)) (v p) = y6 := by rw [hy6def]
    rw [e1, e2, e4] at h
    exact h
  have hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5) := by
    have h := g482w3_upsX_pos_of_not_col (a := (0 : V3)) (b := v (p + 2)) (c := v (p + 1))
      (hnc (p + 2) (p + 1) (by omega))
    have e1 : dist (0 : V3) (v (p + 2)) = y1 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy1def]
    have e2 : dist (0 : V3) (v (p + 1)) = y3 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy3def]
    have e4 : dist (v (p + 2)) (v (p + 1)) = y5 := by rw [hy5def]
    rw [e1, e2, e4] at h
    exact h
  have hsub : Set.Ioo (y4 - e7) (y4 + e7) ⊆
      {y : ℝ | 0 < deltaY y1 y2 y3 y y5 y6 ∧ 0 < y ∧
        0 < upsX (y2 * y2) (y3 * y3) (y * y)} := by
    intro y hy
    have ht : |y - y4| < e7 := by
      rw [abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    have hNPt : ¬ Coplanar ({0, v p, f (v (p + 1)) (y - y4), v (p + 2)} : Set V3) :=
      hNP _ (h7eNP _ ht)
    refine ⟨?_, ?_, ?_⟩
    · have hncop' : ¬ Coplanar ({0, v (p + 2), v p, f (v (p + 1)) (y - y4)} : Set V3) := by
        intro hc
        apply hNPt
        have hset : ({0, v (p + 2), v p, f (v (p + 1)) (y - y4)} : Set V3) =
            {0, v p, f (v (p + 1)) (y - y4), v (p + 2)} := by
          ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rwa [hset] at hc
      have hd := g482w3_deltaY_pos (u0 := (0 : V3)) (u1 := v (p + 2)) (u2 := v p)
        (u3 := f (v (p + 1)) (y - y4)) hncop'
      have e1 : dist (0 : V3) (v (p + 2)) = y1 := by
        rw [dist_eq_norm, zero_sub, norm_neg]
      have e2 : dist (0 : V3) (v p) = y2 := by
        rw [dist_eq_norm, zero_sub, norm_neg]
      have e3 : dist (0 : V3) (f (v (p + 1)) (y - y4)) = y3 := by
        rw [dist_eq_norm, zero_sub, norm_neg, hnormf (p + 1) (y - y4) (h7e' _ ht)]
      have e4 : dist (v p) (f (v (p + 1)) (y - y4)) = y := by
        rw [hdist1 _ (h7e' _ ht)]
        ring
      have e5 : dist (v (p + 2)) (f (v (p + 1)) (y - y4)) = y5 := by
        exact hdist2 _ (h7e' _ ht)
      have e6 : dist (v (p + 2)) (v p) = y6 := hy6def.symm
      rw [e1, e2, e3, e4, e5, e6] at hd
      exact hd
    · have hgt : -(1 : ℝ) < y - y4 := (abs_lt.mp (h71 _ ht)).1
      linarith
    · have hnc' : ¬ Collinear3 (0 : V3) (v p) (f (v (p + 1)) (y - y4)) :=
        (notcoplanar_imp_notcollinear_fan (x := (0 : V3)) (v := v p)
          (u := f (v (p + 1)) (y - y4)) (w := v (p + 2)) hNPt).2.1
      have h := g482w3_upsX_pos_of_not_col (a := (0 : V3)) (b := v p)
        (c := f (v (p + 1)) (y - y4)) hnc'
      have e1 : dist (0 : V3) (v p) = y2 := by
        rw [dist_eq_norm, zero_sub, norm_neg]
      have e2 : dist (0 : V3) (f (v (p + 1)) (y - y4)) = y3 := by
        rw [dist_eq_norm, zero_sub, norm_neg, hnormf (p + 1) (y - y4) (h7e' _ ht)]
      have e3 : dist (v p) (f (v (p + 1)) (y - y4)) = y := by
        rw [hdist1 _ (h7e' _ ht)]
        ring
      rw [e1, e2, e3] at h
      exact h
  obtain ⟨y4', hy4'mem, hy4'lt⟩ := LEMMA_1834976363_p22 h y1 y2 y3 y4 y5 y6 (y4 - e7) (y4 + e7)
    ⟨hy1lo, hy1hi⟩ ⟨hy2lo, hy2hi⟩ ⟨hy3lo, hy3hi⟩ hx4 hx5 hx6
    ⟨by linarith, by linarith⟩ hsub (by linarith) (by linarith) hu6 hu5
  -- ═══ K. minimality at the deformed configuration ═══
  set t : ℝ := y4' - y4 with htdef
  have htabs : |t| < e7 := by
    rw [htdef, abs_lt]
    constructor <;> linarith [hy4'mem.1, hy4'mem.2]
  have hy4'eq : y4' = y4 + t := by rw [htdef]; ring
  have hw : BBsV39 s (fun i => f (v i) t) := hBBdef t (h7eBB t htabs)
  have hmin := MMs_minimize_tau_fun_p21 s 4 v (fun i => f (v i) t) hs' hb hk (by norm_num)
    hvBBp hw
  -- ═══ L. expand the two `rhoFun * azim` sums (HOL `periodic_sum` block) ═══
  have hsum4 : ∀ (g : ℕ → ℝ), periodic g 4 → setSum {i : ℕ | i < 4} g =
      g p + g (p + 1) + g (p + 2) + g (p + 3) := by
    intro g hg4
    have hfin : ({i : ℕ | i < 4} : Set ℕ).Finite := Set.finite_lt_nat 4
    have hset : setSum {i : ℕ | i < 4} g = ∑ x ∈ Finset.range 4, g x := by
      rw [setSum, dif_pos hfin]
      congr 1
      ext x; simp
    rw [hset, ← periodic_sum hg4 (by norm_num) p]
    have hI : Finset.Icc p (4 - 1 + p) = ({p, p + 1, p + 2, p + 3} : Finset ℕ) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hI]
    rw [Finset.sum_insert (by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; omega)]
    rw [Finset.sum_insert (by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; omega)]
    rw [Finset.sum_insert (by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; omega)]
    rw [Finset.sum_singleton]
    ring
  have hpergv : periodic (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))) 4 := by
    intro i
    show rhoFun ‖v (i + 4)‖ * azim 0 (v (i + 4)) (v (i + 4 + 1)) (v (i + 4 + 3)) =
      rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))
    rw [show i + 4 + 1 = (i + 1) + 4 by omega, show i + 4 + 3 = (i + 3) + 4 by omega,
      hperv i, hperv (i + 1), hperv (i + 3)]
  have hpergw : periodic (fun i => rhoFun ‖f (v i) t‖ *
      azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) 4 := by
    intro i
    show rhoFun ‖f (v (i + 4)) t‖ * azim 0 (f (v (i + 4)) t) (f (v (i + 4 + 1)) t)
        (f (v (i + 4 + 3)) t) =
      rhoFun ‖f (v i) t‖ * azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)
    rw [show i + 4 + 1 = (i + 1) + 4 by omega, show i + 4 + 3 = (i + 3) + 4 by omega,
      hperv i, hperv (i + 1), hperv (i + 3)]
  have hSv := hsum4 (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))) hpergv
  have hSw := hsum4 (fun i => rhoFun ‖f (v i) t‖ *
    azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) hpergw
  have hmin' : setSum {i : ℕ | i < 4} (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3)))
      ≤ setSum {i : ℕ | i < 4} (fun i => rhoFun ‖f (v i) t‖ *
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) := by
    simpa only using hmin
  -- ═══ M. name the azimuth atoms ═══
  set A012 : ℝ := azim 0 (v p) (v (p + 1)) (v (p + 2)) with hA012
  set A013 : ℝ := azim 0 (v p) (v (p + 1)) (v (p + 3)) with hA013
  set A023 : ℝ := azim 0 (v p) (v (p + 2)) (v (p + 3)) with hA023
  set A120 : ℝ := azim 0 (v (p + 1)) (v (p + 2)) (v p) with hA120
  set A230 : ℝ := azim 0 (v (p + 2)) (v (p + 3)) (v p) with hA230
  set A201 : ℝ := azim 0 (v (p + 2)) (v p) (v (p + 1)) with hA201
  set E231 : ℝ := azim 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) with hE231
  set B302 : ℝ := azim 0 (v (p + 3)) (v p) (v (p + 2)) with hB302
  set F012 : ℝ := azim 0 (v p) (f (v (p + 1)) t) (v (p + 2)) with hF012
  set F013 : ℝ := azim 0 (v p) (f (v (p + 1)) t) (v (p + 3)) with hF013
  set F120 : ℝ := azim 0 (f (v (p + 1)) t) (v (p + 2)) (v p) with hF120
  set F201 : ℝ := azim 0 (v (p + 2)) (v p) (f (v (p + 1)) t) with hF201
  set F230 : ℝ := azim 0 (v (p + 2)) (v (p + 3)) (f (v (p + 1)) t) with hF230
  have hgv_exp : setSum {i : ℕ | i < 4}
      (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))) =
      rhoFun y2 * A013 + rhoFun y3 * A120 + rhoFun y1 * E231 +
        rhoFun ‖v (p + 3)‖ * B302 := by
    rw [hSv]
    rw [show p + 1 + 3 = p + 4 by omega,
      show p + 2 + 3 = p + 5 by omega, show p + 5 = (p + 1) + 4 by omega,
      show p + 3 + 1 = p + 4 by omega,
      show p + 3 + 3 = p + 6 by omega, show p + 6 = (p + 2) + 4 by omega,
      hperv p, hperv (p + 1), hperv (p + 2),
      ← hy1def, ← hy2def, ← hy3def,
      ← hA120, ← hB302, ← hE231]
  have hgw_exp : setSum {i : ℕ | i < 4} (fun i => rhoFun ‖f (v i) t‖ *
      azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) =
      rhoFun y2 * F013 + rhoFun y3 * F120 + rhoFun y1 * F230 +
        rhoFun ‖v (p + 3)‖ * B302 := by
    rw [hSw]
    rw [show p + 1 + 3 = p + 4 by omega,
      show p + 2 + 3 = p + 5 by omega, show p + 5 = (p + 1) + 4 by omega,
      show p + 3 + 1 = p + 4 by omega,
      show p + 3 + 3 = p + 6 by omega, show p + 6 = (p + 2) + 4 by omega,
      hperv p, hperv (p + 1), hperv (p + 2),
      hfix (v p) t (hne_vp1 p (by omega)),
      hfix (v (p + 2)) t (hne_vp1 (p + 2) (by omega)),
      hfix (v (p + 3)) t (hne_vp1 (p + 3) (by omega)),
      hnormf (p + 1) t (h7e' t htabs), ← hy1def, ← hy2def, ← hy3def,
      ← hF013, ← hF120, ← hF230, ← hB302]
  -- ═══ N. the strict-drop contradiction ═══
  have hcmp : rhoFun y2 * A013 + rhoFun y3 * A120 + rhoFun y1 * E231
      ≤ rhoFun y2 * F013 + rhoFun y3 * F120 + rhoFun y1 * F230 := by
    have h := hmin'
    rw [hgv_exp, hgw_exp] at h
    linarith
  have hA013_split : A013 = A012 + A023 := hsum1
  have hE231_split : E231 = A230 + A201 := hsum2
  have hF013_split : F013 = F012 + A023 := by
    have hsumA := (hAall t (h7eA t htabs)).2.2.2
    rw [hfix (v p) t (hne_vp1 p (by omega)),
      hfix (v (p + 2)) t (hne_vp1 (p + 2) (by omega)),
      hfix (v (p + 3)) t (hne_vp1 (p + 3) (by omega))] at hsumA
    exact hsumA.symm
  have hF230_split : F230 = A230 + F201 := by
    have hsumB := (hBall t (h7eB t htabs)).2.2.2
    rw [hfix (v (p + 2)) t (hne_vp1 (p + 2) (by omega)),
      hfix (v (p + 3)) t (hne_vp1 (p + 3) (by omega)),
      hfix (v p) t (hne_vp1 p (by omega))] at hsumB
    exact hsumB.symm
  have hWC : azim 0 (f (v (p + 1)) t) (v (p + 2)) (v p) < Real.pi := by
    have h := hWall t (h7eW t htabs)
    rwa [hfix (v (p + 2)) t (hne_vp1 (p + 2) (by omega)),
      hfix (v p) t (hne_vp1 p (by omega))] at h
  have hd4 : dist (f (v (p + 1)) t) (v p) = y4' := by
    rw [dist_comm, hdist1 _ (h7e' _ htabs), ← hy4'eq]
  have hbase : taum y1 y2 y3 y4 y5 y6 =
      taum ‖v p‖ ‖v (p + 1)‖ ‖v (p + 2)‖ (dist (v (p + 1)) (v (p + 2)))
        (dist (v p) (v (p + 2))) (dist (v p) (v (p + 1))) := by
    rw [g482w3_taum_cyc y1 y2 y3 y4 y5 y6]
    rw [hy2def, hy3def, hy1def]
    rw [hy5def, dist_comm (v (p + 2)) (v (p + 1))]
    rw [hy6def, dist_comm (v (p + 2)) (v p)]
  have htau_base : taum y1 y2 y3 y4 y5 y6 =
      rho y2 * A012 + rho y3 * A120 + rho y1 * A201 - (Real.pi + sol0) := by
    rw [hbase, ← tau3_taum_nonplanar_p21 (v p) (v (p + 1)) (v (p + 2)) hncop,
      tau3_azim_p21 (v p) (v (p + 1)) (v (p + 2)) hncop (le_of_lt hA012_lt),
      hy2def, hy3def, hy1def, hA012, hA120, hA201]
  have htaum_congr : taum y1 y2 y3 y4' y5 y6 =
      taum ‖f (v (p + 1)) t‖ ‖v (p + 2)‖ ‖v p‖
        (dist (v (p + 2)) (v p)) (dist (f (v (p + 1)) t) (v p))
        (dist (f (v (p + 1)) t) (v (p + 2))) := by
    have h1 : y3 = ‖f (v (p + 1)) t‖ := by
      rw [hy3def]
      exact (hnormf (p + 1) t (h7e' t htabs)).symm
    have h6 : y5 = dist (f (v (p + 1)) t) (v (p + 2)) := by
      rw [hy5def]
      rw [show dist (v (p + 2)) (v (p + 1)) = dist (v (p + 2)) (f (v (p + 1)) t) from
        (hdist2 _ (h7e' _ htabs)).symm]
      exact dist_comm _ _
    rw [g482w3_taum_cyc y1 y2 y3 y4' y5 y6, g482w3_taum_cyc y2 y3 y1 y5 y6 y4',
      h1, hy1def, hy2def, hy6def, ← hd4, h6]
  have hNP' : ¬ Coplanar ({0, f (v (p + 1)) t, v (p + 2), v p} : Set V3) := by
    intro hc
    apply hNP t (h7eNP t htabs)
    rwa [show ({0, v p, f (v (p + 1)) t, v (p + 2)} : Set V3) =
      {0, f (v (p + 1)) t, v (p + 2), v p} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have htau_def : taum y1 y2 y3 y4' y5 y6 =
      rho y3 * F120 + rho y1 * F201 + rho y2 * F012 - (Real.pi + sol0) := by
    rw [htaum_congr,
      ← tau3_taum_nonplanar_p21 (f (v (p + 1)) t) (v (p + 2)) (v p) hNP',
      tau3_azim_p21 (f (v (p + 1)) t) (v (p + 2)) (v p) hNP' (le_of_lt hWC),
      hnormf (p + 1) t (h7e' t htabs), hy3def, hy1def, hy2def, hF120, hF201, hF012]
  have hcmp_rho : rho y2 * A013 + rho y3 * A120 + rho y1 * E231
      ≤ rho y2 * F013 + rho y3 * F120 + rho y1 * F230 := by
    simpa only [rho_rho_fun] using hcmp
  have hstep : rho y2 * A012 + rho y3 * A120 + rho y1 * A201
      ≤ rho y2 * F012 + rho y3 * F120 + rho y1 * F201 := by
    have h := hcmp_rho
    rw [hA013_split, hE231_split, hF013_split, hF230_split] at h
    linarith [h]
  have hmain : taum y1 y2 y3 y4 y5 y6 ≤ taum y1 y2 y3 y4' y5 y6 := by
    rw [htau_base, htau_def]
    linarith [hstep]
  linarith [hy4'lt]

set_option maxHeartbeats 6000000 in
/-- HOL `JOTSWIX` (JOTSWIX.hl:2204): the master quad lemma — under the
xrr bound at least one of the two edges of the quad is under `cstab`.
NEEDS: `NEHXMWH_p23` + the `xrr` registry bounds. -/
theorem JOTSWIX_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (FF : Set (V3 × V3)) (v : ℕ → V3) (p : ℕ)
    (hFF : (fun i : ℕ => (v i, v (i + 1))) '' Set.univ = FF)
    (hs : isScsV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s) (hb : scsBasicV39 s)
    (hg : scsGeneric v) (hsa : s.a p (p + 1) < cstab)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hang : ∀ i, i % 4 ≠ (p + 2) % 4 → interiorAngle1 0 FF (v i) < Real.pi)
    (hxrr : xrr (norm (v (p + 3))) (norm (v (p + 1)))
      (dist (v (p + 3)) (v (p + 1))) ≤ 15.53) :
    dist (v p) (v (p + 1)) < cstab ∨ dist (v p) (v (p + 3)) < cstab := by
  -- ═══ A. substrate: `BBs_v39` from `MMs_v39`, fan data, azimuth forms ═══
  have hs' : isScsV39 s := hs
  obtain ⟨-, hk3le, -, -, -, -, -, hpa, -, -, hpbP, -, hsym, hch, hdiag0, hdiag, -, hbc, -, -, -⟩ := hs
  have hk4pos : 0 < (4 : ℕ) := by norm_num
  have hvBBp : v ∈ BBprimeV39 s := by
    have h2 : v ∈ BBprime2V39 s := by
      have h1 := hMM
      simp only [MMsV39, Set.mem_setOf_eq] at h1
      exact h1.1
    have h3 := h2
    simp only [BBprime2V39, Set.mem_setOf_eq] at h3
    exact h3.1
  obtain ⟨hBBs, hvmin, hvneg⟩ := by
    have h3 := hvBBp
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3
  have hBBs' : BBsV39 s v := hBBs
  obtain ⟨hann, hpervS, hbnd, hconv0⟩ := hBBs
  have hperv : Periodic v 4 := by rw [← hk]; exact hpervS
  have hmod : ∀ i : ℕ, v (i % 4) = v i := fun i => periodic_mod_eq_p23 hperv i
  have hinj : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j :=
    BBs_inj_p21 s v 4 hs' hk hBBs'
  have hmodv : ∀ i : ℕ, v i = v p → i % 4 = p % 4 := by
    intro i hi
    exact hinj (i % 4) (p % 4) (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos)
      (by rw [hmod i, hmod p]; exact hi)
  have hne_vp : ∀ i : ℕ, i % 4 ≠ p % 4 → v i ≠ v p :=
    fun i h hc => h (hmodv i hc)
  have hFFr : Set.range (fun i : ℕ => (v i, v (i + 1))) = FF := by
    simpa only [Set.image_univ] using hFF
  have hconv : ConvexLocalFan (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3))
      (Set.range fun i => (v i, v (i + 1))) := by
    rcases hconv0 with hle | hcl
    · omega
    · exact hcl
  have hlf := hconv.1
  have hvmem : ∀ i : ℕ, v i ∈ Set.range v := fun i => Set.mem_range_self i
  have hazim : ∀ i : ℕ, interiorAngle1 0 FF (v i) = azim 0 (v i) (v (i + 1)) (v (i + 3)) := by
    intro i
    have h1 := INTERIOR_ANGLE1_AZIM_p22 s v i hs' hBBs' (show 3 < s.k by omega) FF hFFr.symm
    rw [hk] at h1
    exact h1.symm
  have hpos : ∀ i : ℕ, 0 < azim 0 (v i) (v (i + 1)) (v (i + 3)) := by
    intro i
    have h1 := LOCAL_FAN_AZIM_POS_p22 s v i hconv hs' hBBs'
    rw [hk] at h1
    exact h1
  have hnc : ∀ i j : ℕ, i % 4 ≠ j % 4 → ¬ Collinear ℝ ({0, v i, v j} : Set V3) := by
    intro i j hij
    have hne : v i ≠ v j := by
      intro he
      exact hij (hinj (i % 4) (j % 4) (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos)
        (by rw [hmod i, hmod j]; exact he))
    have hgen : Generic (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)) := by
      simpa only [scsGeneric] using hg
    exact PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 _ _ _ _ _ hlf (hvmem i) (hvmem j) hne hgen
  -- ═══ B. the azimuths at `p`, `p+1`, `p+3` and the coplanarity of the quad ═══
  have hpp2 : p % 4 ≠ (p + 2) % 4 := by omega
  have ha013_lt : azim 0 (v p) (v (p + 1)) (v (p + 3)) < Real.pi := by
    have h1 := hang p hpp2
    rwa [hazim p] at h1
  have ha013_pos : 0 < azim 0 (v p) (v (p + 1)) (v (p + 3)) := hpos p
  have hnc_pp1 : ¬ Collinear ℝ ({0, v p, v (p + 1)} : Set V3) := hnc p (p + 1) (by omega)
  have hnc_pp3 : ¬ Collinear ℝ ({0, v p, v (p + 3)} : Set V3) := hnc p (p + 3) (by omega)
  obtain ⟨⟨h132, h132'⟩, ⟨h301, h301'⟩⟩ :=
    g482w3_azim_cycle (x := v p) (y := v (p + 1)) (z := v (p + 3))
      hnc_pp1 hnc_pp3 ha013_pos ha013_lt
  have hncop : ¬ Coplanar ({0, v p, v (p + 1), v (p + 3)} : Set V3) := by
    intro hc
    rcases (AZIM_COND_FOR_COPLANAR (0 : V3) (v p) (v (p + 1)) (v (p + 3))).mpr hc with h0 | hpi
    · linarith
    · linarith
  -- ═══ C. assume both quad edges are `≥ cstab` and derive the boundary form ═══
  by_contra hcon
  push_neg at hcon
  obtain ⟨hge1, hge3⟩ := hcon
  -- the `(p,p+1)` edge is pinned at the upper bound `s.b p (p+1)`, i.e. at `cstab`
  have hbdd1 : dist (v p) (v (p + 1)) ≤ s.b p (p + 1) := (hbnd p (p + 1)).2
  have hbc1 : s.b p (p + 1) ≤ cstab := hbc p (by omega)
  have hdistB : dist (v p) (v (p + 1)) = s.b p (p + 1) := by linarith
  have hdistC : dist (v p) (v (p + 1)) = cstab := by linarith
  -- the `(p,p+3)` edge lies in `[cstab, s.b p (p+3)]`
  have hbper4 : Periodic2 s.b 4 := hk ▸ hpbP
  have hBred : ∀ i j : ℕ, s.b i j = s.b (i % 4) (j % 4) :=
    fun i j => periodic2_MOD_p21 (by norm_num) hbper4
  have hbdd3 : dist (v p) (v (p + 3)) ≤ s.b (p + 3) p := by
    have h := (hbnd (p + 3) ((p + 3) + 1)).2
    have hv : v ((p + 3) + 1) = v p := by
      rw [show (p + 3) + 1 = p + 4 by omega, hperv p]
    have hb : s.b (p + 3) ((p + 3) + 1) = s.b (p + 3) p := by
      rw [hBred (p + 3) ((p + 3) + 1), hBred (p + 3) p,
        show ((p + 3) + 1) % 4 = p % 4 by omega]
    rw [hv, hb] at h
    rwa [dist_comm] at h
  have hb3c : s.b (p + 3) p ≤ cstab := by
    have h := hbc (p + 3) (by omega)
    have hb : s.b (p + 3) ((p + 3) + 1) = s.b (p + 3) p := by
      rw [hBred (p + 3) ((p + 3) + 1), hBred (p + 3) p,
        show ((p + 3) + 1) % 4 = p % 4 by omega]
    rwa [hb] at h
  -- ═══ D. the edge deformation at `v p` (HOL `deform_simplex_edge_exists`) ═══
  have hncop4 : ¬ Coplanar ({0, v (p + 3), v p, v (p + 1)} : Set V3) := by
    intro hc
    apply hncop
    have hset : ({0, v (p + 3), v p, v (p + 1)} : Set V3) = {0, v p, v (p + 1), v (p + 3)} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [hset] at hc
  have hcross : (v p).ofLp ⬝ᵥ (cross3 (v (p + 1)) (v (p + 3))).ofLp > 0 := by
    have h := (azim_lt_pi_cross_p14 (v (p + 1)) (v (p + 3)) (v p)).mp ⟨h132, h132'⟩
    rwa [dotProduct_comm] at h
  obtain ⟨f, hf⟩ := deform_simplex_edge_exists_p21 (Set.range v) (fun _ => 0) (fun t => -|t|)
    (v (p + 3)) (v p) (v (p + 1)) 1
  obtain ⟨e', he'pos, hdef, hfix, hdistf⟩ := hf hncop4 hcross (by norm_num)
    (by fun_prop) (continuous_abs.neg.continuousOn) (by simp) (by simp)
  have hdist1 : ∀ t : ℝ, |t| < e' →
      dist (v (p + 3)) (f (v p) t) = dist (v (p + 3)) (v p) := by
    intro t ht
    have h := (hdistf t ht).1
    rwa [add_zero] at h
  have hdist2 : ∀ t : ℝ, |t| < e' →
      dist (v (p + 1)) (f (v p) t) = dist (v (p + 1)) (v p) - |t| := by
    intro t ht
    have h := (hdistf t ht).2.1
    rwa [show dist (v (p + 1)) (v p) + (-|t|) = dist (v (p + 1)) (v p) - |t| from by ring] at h
  have hnormf : ∀ (i : ℕ) (t : ℝ), |t| < e' → ‖f (v i) t‖ = ‖v i‖ := by
    intro i t ht
    by_cases hi : v i = v p
    · rw [hi]; exact (hdistf t ht).2.2
    · rw [hfix _ t hi]
  have hdiag4 : ∀ i j, scsDiag 4 i j → s.a i j < dist (v i) (v j) ∧ 4 * h0 < s.b i j := by
    intro i j hd
    obtain ⟨h1, h2, h3⟩ := hdg i j hd
    exact ⟨lt_of_le_of_lt h1 h2, h3⟩
  -- ═══ E. `ab4_assumption_reduction2`: the deformed configuration stays in `BBs` ═══
  have hab : s.a p (p + 1) < dist (v p) (v (p + 1)) := lt_of_lt_of_le hsa hge1
  have hb3 : ∃ e3 : ℝ, 0 < e3 ∧ ∀ t, |t| < e3 →
      dist (f (v p) t) (v (p + 1)) ≤ s.b p (p + 1) := by
    refine ⟨e', he'pos, fun t ht => ?_⟩
    have h := hdist2 t ht
    rw [dist_comm (f (v p) t) (v (p + 1))]
    have h4 : dist (v (p + 1)) (v p) = dist (v p) (v (p + 1)) := dist_comm _ _
    nlinarith [abs_nonneg t, hdistB]
  obtain ⟨ha_ab, hb_ab⟩ :=
    ab4_assumption_reduction2_p23 s p f v e' hs' hk hBBs' hdiag4 hdef he'pos hfix hdist1 hab hb3
  -- ═══ F. the flat-angle skolem for `deformation_BBs_ALT` ═══
  have hsucc : ∀ {i j : ℕ}, v i = v j → v (i + 1) = v (j + 1) := by
    intro i j hij
    have h1 : i % 4 = j % 4 :=
      hinj _ _ (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos) (by rw [hmod i, hmod j]; exact hij)
    have h2 : (i + 1) % 4 = (j + 1) % 4 := by omega
    rw [← hmod (i + 1), ← hmod (j + 1), h2]
  have hadd3 : ∀ {i j : ℕ}, v i = v j → v (i + 3) = v (j + 3) := by
    intro i j hij
    have h1 : i % 4 = j % 4 :=
      hinj _ _ (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos) (by rw [hmod i, hmod j]; exact hij)
    have h2 : (i + 3) % 4 = (j + 3) % 4 := by omega
    rw [← hmod (i + 3), ← hmod (j + 3), h2]
  have hazPi : ∀ i : ℕ, ∃ e0 : ℝ, 0 < e0 ∧
      (azim 0 (v i) (v (i + 1)) (v (i + (4 - 1))) = Real.pi →
        ∀ t : ℝ, |t| < e0 →
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (4 - 1))) t) ≤ Real.pi) := by
    intro i
    by_cases hi : v i = v (p + 2)
    · have h1 : v (i + 1) = v (p + 3) := hsucc hi
      have h3 : v (i + (4 - 1)) = v (p + 1) := by
        have h := hadd3 hi
        rw [show p + 2 + 3 = (p + 1) + 4 by omega, hperv (p + 1)] at h
        exact h
      have hne2 : v (p + 2) ≠ v p := hne_vp (p + 2) (by omega)
      have hne3 : v (p + 3) ≠ v p := hne_vp (p + 3) (by omega)
      have hne1 : v (p + 1) ≠ v p := hne_vp (p + 1) (by omega)
      refine ⟨1, by norm_num, fun hpi t _ => ?_⟩
      rw [hi, h1, h3] at hpi ⊢
      rw [hfix _ t hne2, hfix _ t hne3, hfix _ t hne1]
      exact le_of_eq hpi
    · have hmodne : i % 4 ≠ (p + 2) % 4 := by
        intro hc
        exact hi (by rw [← hmod i, ← hmod (p + 2), hc])
      have hlt : azim 0 (v i) (v (i + 1)) (v (i + 3)) < Real.pi := by
        have h1 := hang i hmodne
        rwa [hazim i] at h1
      refine ⟨1, by norm_num, fun hpi _ _ => ?_⟩
      exact absurd hpi (ne_of_lt hlt)
  obtain ⟨eBB, heBB, hBBdef⟩ :=
    deformation_BBs_ALT_p21 s 4 f v e' hs' hk (by norm_num) hBBs' hg he'pos hdef hazPi hnormf
      ha_ab hb_ab
  -- ═══ G. the two azimuth sums (`vv_split_azim_generic` + `deform_azim_sum`) ═══
  have hdef4 : Deformation f ({v (p + 3), v p, v (p + 1), v (p + 2)} : Set V3) (-e') e' := by
    refine deformation_subset_p14 f _ (Set.range v) (-e') e' ?_ hdef
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Set.mem_range_self _
  have hsum1 : azim 0 (v (p + 3)) (v p) (v (p + 2)) =
      azim 0 (v (p + 3)) (v p) (v (p + 1)) + azim 0 (v (p + 3)) (v (p + 1)) (v (p + 2)) := by
    have hnc1 : ¬ Collinear ℝ ({0, v (p + 3), v (p + 1)} : Set V3) :=
      hnc (p + 3) (p + 1) (by omega)
    have hnc2 : ¬ Collinear ℝ ({0, v (p + 3), v ((p + 3) + (4 - 1))} : Set V3) := by
      have e : v ((p + 3) + (4 - 1)) = v (p + 2) := by
        rw [show (p + 3) + (4 - 1) = (p + 2) + 4 by omega, hperv (p + 2)]
      rw [e]; exact hnc (p + 3) (p + 2) (by omega)
    have hnc3 : ¬ Collinear ℝ ({0, v (p + 3), v ((p + 3) + 1)} : Set V3) := by
      have e : v ((p + 3) + 1) = v p := by
        rw [show (p + 3) + 1 = p + 4 by omega, hperv p]
      rw [e]; exact hnc (p + 3) p (by omega)
    have hinj' : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j := hinj
    have h := vv_split_azim_alt_p21 (vv := v) (k := 4) (i := p + 3) (j := p + 1)
      hperv (by norm_num) hnc1 hnc2 hnc3 hconv hinj'
    have e2 : v (p + 3 + 4 - 1) = v (p + 2) := by
      rw [show p + 3 + 4 - 1 = (p + 2) + 4 by omega, hperv (p + 2)]
    have e3 : v (p + 3 + 1) = v p := by
      rw [show p + 3 + 1 = p + 4 by omega, hperv p]
    rw [e2, e3] at h
    exact h
  have hApos1 : 0 < azim 0 (v (p + 3)) (v p) (v (p + 2)) := by
    have h := LOCAL_FAN_AZIM_POS_p22 s v (p + 3) hconv hs' hBBs'
    rwa [hk, show (p + 3) + 1 = p + 4 by omega, hperv p,
      show (p + 3) + (4 - 1) = p + 6 by omega, show p + 6 = (p + 2) + 4 by omega,
      hperv (p + 2)] at h
  have hA'1 : azim 0 (v (p + 3)) (v p) (v (p + 2)) < Real.pi := by
    have h := hang (p + 3) (by omega : (p + 3) % 4 ≠ (p + 2) % 4)
    rw [hazim (p + 3)] at h
    rwa [show p + 3 + 1 = p + 4 by omega, hperv p,
      show p + 3 + 3 = p + 6 by omega, show p + 6 = (p + 2) + 4 by omega, hperv (p + 2)] at h
  have hcase1 : ((∀ t : ℝ, azim 0 (f (v (p + 3)) t) (f (v p) t) (f (v (p + 1)) t) =
        azim 0 (v (p + 3)) (v p) (v (p + 1))) ∧
      0 < azim 0 (v (p + 3)) (v (p + 1)) (v (p + 2)) ∧
        azim 0 (v (p + 3)) (v (p + 1)) (v (p + 2)) < Real.pi) ∨
      ((∀ t : ℝ, azim 0 (f (v (p + 3)) t) (f (v (p + 1)) t) (f (v (p + 2)) t) =
        azim 0 (v (p + 3)) (v (p + 1)) (v (p + 2))) ∧
      0 < azim 0 (v (p + 3)) (v p) (v (p + 1)) ∧
        azim 0 (v (p + 3)) (v p) (v (p + 1)) < Real.pi) := by
    refine Or.inr ⟨?_, h301, h301'⟩
    intro t
    rw [hfix _ t (hne_vp (p + 3) (by omega)), hfix _ t (hne_vp (p + 1) (by omega)),
      hfix _ t (hne_vp (p + 2) (by omega))]
  obtain ⟨eA, heA, hAall⟩ := deform_azim_sum_p23 (v (p + 3)) (v p) (v (p + 1)) (v (p + 2))
    f e' hdef4 hApos1 hA'1 (hnc (p + 3) p (by omega)) (hnc (p + 3) (p + 1) (by omega))
      (hnc (p + 3) (p + 2) (by omega)) hsum1.symm hcase1
  -- second sum: `v (p+1), v (p+2), v (p+3), v p`
  have hdef4' : Deformation f ({v (p + 1), v (p + 2), v (p + 3), v p} : Set V3) (-e') e' := by
    refine deformation_subset_p14 f _ (Set.range v) (-e') e' ?_ hdef
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Set.mem_range_self _
  have hsum2 : azim 0 (v (p + 1)) (v (p + 2)) (v p) =
      azim 0 (v (p + 1)) (v (p + 2)) (v (p + 3)) + azim 0 (v (p + 1)) (v (p + 3)) (v p) := by
    have hnc1 : ¬ Collinear ℝ ({0, v (p + 1), v (p + 3)} : Set V3) :=
      hnc (p + 1) (p + 3) (by omega)
    have hnc2 : ¬ Collinear ℝ ({0, v (p + 1), v ((p + 1) + (4 - 1))} : Set V3) := by
      have e : v ((p + 1) + (4 - 1)) = v p := by
        rw [show (p + 1) + (4 - 1) = p + 4 by omega, hperv p]
      rw [e]; exact hnc (p + 1) p (by omega)
    have hnc3 : ¬ Collinear ℝ ({0, v (p + 1), v ((p + 1) + 1)} : Set V3) := by
      have e : v ((p + 1) + 1) = v (p + 2) := by
        rw [show (p + 1) + 1 = p + 2 by omega]
      rw [e]; exact hnc (p + 1) (p + 2) (by omega)
    have hinj' : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j := hinj
    have h := vv_split_azim_alt_p21 (vv := v) (k := 4) (i := p + 1) (j := p + 3)
      hperv (by norm_num) hnc1 hnc2 hnc3 hconv hinj'
    have e2 : v (p + 1 + 4 - 1) = v p := by
      rw [show p + 1 + 4 - 1 = p + 4 by omega, hperv p]
    rw [e2] at h
    exact h
  have hApos2 : 0 < azim 0 (v (p + 1)) (v (p + 2)) (v p) := by
    have h := LOCAL_FAN_AZIM_POS_p22 s v (p + 1) hconv hs' hBBs'
    rwa [hk, show (p + 1) + 1 = p + 2 by omega,
      show (p + 1) + (4 - 1) = p + 4 by omega, hperv p] at h
  have hA'2 : azim 0 (v (p + 1)) (v (p + 2)) (v p) < Real.pi := by
    have h := hang (p + 1) (by omega : (p + 1) % 4 ≠ (p + 2) % 4)
    rw [hazim (p + 1)] at h
    rwa [show p + 1 + 1 = p + 2 by omega, show p + 1 + 3 = p + 4 by omega, hperv p] at h
  have hcase2 : ((∀ t : ℝ, azim 0 (f (v (p + 1)) t) (f (v (p + 2)) t) (f (v (p + 3)) t) =
        azim 0 (v (p + 1)) (v (p + 2)) (v (p + 3))) ∧
      0 < azim 0 (v (p + 1)) (v (p + 3)) (v p) ∧
        azim 0 (v (p + 1)) (v (p + 3)) (v p) < Real.pi) ∨
      ((∀ t : ℝ, azim 0 (f (v (p + 1)) t) (f (v (p + 3)) t) (f (v p) t) =
        azim 0 (v (p + 1)) (v (p + 3)) (v p)) ∧
      0 < azim 0 (v (p + 1)) (v (p + 2)) (v (p + 3)) ∧
        azim 0 (v (p + 1)) (v (p + 2)) (v (p + 3)) < Real.pi) := by
    refine Or.inl ⟨?_, h132, h132'⟩
    intro t
    rw [hfix _ t (hne_vp (p + 1) (by omega)), hfix _ t (hne_vp (p + 2) (by omega)),
      hfix _ t (hne_vp (p + 3) (by omega))]
  obtain ⟨eB, heB, hBall⟩ := deform_azim_sum_p23 (v (p + 1)) (v (p + 2)) (v (p + 3)) (v p)
    f e' hdef4' hApos2 hA'2 (hnc (p + 1) (p + 2) (by omega)) (hnc (p + 1) (p + 3) (by omega))
      (hnc (p + 1) p (by omega)) hsum2.symm hcase2
  -- ═══ H. nonplanarity stays open along the deformation ═══
  have hcont0 : ContinuousAt (fun t => f (v p) t) 0 :=
    hdef.2.1 (v p) (Set.mem_range_self p) 0 hdef.1
  obtain ⟨eNP, heNP, hNPall⟩ := NONPLANAR_OPEN_p14 (fun _ => (0 : V3)) (fun t => f (v p) t)
    (fun _ => v (p + 1)) (fun _ => v (p + 3)) 0
    (by
      have hset : ({0, f (v p) 0, v (p + 1), v (p + 3)} : Set V3) =
          {0, v p, v (p + 1), v (p + 3)} := by
        rw [hdef.2.2 (v p) (Set.mem_range_self p)]
      rwa [hset])
    continuousAt_const hcont0 continuousAt_const continuousAt_const
  have hNP : ∀ t : ℝ, |t| < eNP →
      ¬ Coplanar ({0, f (v p) t, v (p + 1), v (p + 3)} : Set V3) := by
    intro t ht
    exact hNPall t (by rwa [zero_sub, abs_neg])
  -- ═══ I. combine the epsilons ═══
  have hdef3 : Deformation f ({v (p + 3), v p, v (p + 1)} : Set V3) (-e') e' := by
    refine deformation_subset_p14 f _ (Set.range v) (-e') e' ?_ hdef
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact Set.mem_range_self _
  have hncF1 : ¬ Collinear ℝ ({0, f (v p) 0, f (v (p + 1)) 0} : Set V3) := by
    rw [hfix (v (p + 1)) 0 (hne_vp (p + 1) (by omega)),
      hdef.2.2 (v p) (Set.mem_range_self p)]
    exact hnc_pp1
  have hncF3 : ¬ Collinear ℝ ({0, f (v p) 0, f (v (p + 3)) 0} : Set V3) := by
    rw [hfix (v (p + 3)) 0 (hne_vp (p + 3) (by omega)),
      hdef.2.2 (v p) (Set.mem_range_self p)]
    exact hnc_pp3
  obtain ⟨eW, heW, hWall⟩ := WNWSHJT_p14 (v (p + 3)) (v p) (v (p + 1)) f (-e') e'
    hdef3 hncF1 hncF3 ha013_pos ha013_lt
  obtain ⟨e1, he1, h1e', h1eBB, h1eA⟩ := epsilon_triple_p21 e' eBB eA he'pos heBB heA
  obtain ⟨e2, he2, h2e1, h2eB, h2eNP⟩ := epsilon_triple_p21 e1 eB eNP he1 heB heNP
  obtain ⟨e3', he3', h3'e2, h3'eW⟩ := epsilon_pair_p21 e2 eW he2 heW
  obtain ⟨e7, he7, h7e3, h71⟩ := epsilon_pair_p21 e3' 1 he3' (by norm_num)
  have h7e' : ∀ t : ℝ, |t| < e7 → |t| < e' :=
    fun t ht => h1e' t (h2e1 t (h3'e2 t (h7e3 t ht)))
  have h7eBB : ∀ t : ℝ, |t| < e7 → |t| < eBB :=
    fun t ht => h1eBB t (h2e1 t (h3'e2 t (h7e3 t ht)))
  have h7eA : ∀ t : ℝ, |t| < e7 → |t| < eA :=
    fun t ht => h1eA t (h2e1 t (h3'e2 t (h7e3 t ht)))
  have h7eB : ∀ t : ℝ, |t| < e7 → |t| < eB :=
    fun t ht => h2eB t (h3'e2 t (h7e3 t ht))
  have h7eNP : ∀ t : ℝ, |t| < e7 → |t| < eNP :=
    fun t ht => h2eNP t (h3'e2 t (h7e3 t ht))
  have h7eW : ∀ t : ℝ, |t| < e7 → |t| < eW := fun t ht => h3'eW t (h7e3 t ht)
  -- ═══ J. norms and the `y`-box (`LEMMA_6843920790` brackets) ═══
  have hnorm_lo : ∀ i : ℕ, 2 ≤ ‖v i‖ := by
    intro i
    have h := hann (Set.mem_range_self i)
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at h
    linarith [h.1, h.2]
  have hnorm_hi : ∀ i : ℕ, ‖v i‖ ≤ 2 * h0 := by
    intro i
    have h := hann (Set.mem_range_self i)
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at h
    linarith [h.1, h.2]
  set y1 : ℝ := ‖v (p + 3)‖ with hy1def
  set y2 : ℝ := ‖v p‖ with hy2def
  set y3 : ℝ := ‖v (p + 1)‖ with hy3def
  set y4 : ℝ := dist (v p) (v (p + 1)) with hy4def
  set y5 : ℝ := dist (v (p + 1)) (v (p + 3)) with hy5def
  set y6 : ℝ := dist (v p) (v (p + 3)) with hy6def
  have hy1lo : 2 ≤ y1 := by rw [hy1def]; exact hnorm_lo _
  have hy1hi : y1 ≤ 2 * h0 := by rw [hy1def]; exact hnorm_hi _
  have hy2lo : 2 ≤ y2 := by rw [hy2def]; exact hnorm_lo _
  have hy2hi : y2 ≤ 2 * h0 := by rw [hy2def]; exact hnorm_hi _
  have hy3lo : 2 ≤ y3 := by rw [hy3def]; exact hnorm_lo _
  have hy3hi : y3 ≤ 2 * h0 := by rw [hy3def]; exact hnorm_hi _
  have hy4lo : 2 ≤ y4 := by
    rw [hy4def]
    exact scs_lb_2_p22 s v p (p + 1) hs' hBBs' (by rw [hk]; omega)
  have hy4hi : y4 ≤ 3.01 := by
    have h2 : s.b p (p + 1) ≤ (3.01 : ℝ) := by
      have h := hbc1
      rwa [show cstab = (3.01 : ℝ) from rfl] at h
    exact le_trans hbdd1 h2
  have hy5lo : 2 ≤ y5 := by
    rw [hy5def]
    exact scs_lb_2_p22 s v (p + 1) (p + 3) hs' hBBs' (by rw [hk]; omega)
  have hy5gt : 3 ≤ y5 := by
    rw [hy5def]
    have hd : scsDiag 4 (p + 1) (p + 3) := by
      unfold scsDiag
      exact ⟨by intro hc; omega, by intro hc; omega, by intro hc; omega⟩
    have h := (hdg (p + 1) (p + 3) hd).2.1
    rw [show cstab = (3.01 : ℝ) from rfl] at h
    linarith
  have hy6lo : 2 ≤ y6 := by
    rw [hy6def]
    exact scs_lb_2_p22 s v p (p + 3) hs' hBBs' (by rw [hk]; omega)
  have hy6ge : 3 ≤ y6 := by
    rw [hy6def]
    rw [show cstab = (3.01 : ℝ) from rfl] at hge1 hge3
    linarith [hge3]
  have hy6le : y6 ≤ Real.sqrt 15.53 := by
    rw [hy6def]
    have h1 : dist (v p) (v (p + 3)) ≤ cstab := by linarith [hbdd3, hb3c]
    have h2 : cstab ≤ Real.sqrt 15.53 := by
      have hc : cstab = (3.01 : ℝ) := rfl
      have hsq : (Real.sqrt 15.53) ^ 2 = 15.53 := Real.sq_sqrt (by norm_num)
      have hnn : (0 : ℝ) ≤ Real.sqrt 15.53 := Real.sqrt_nonneg _
      rw [hc]
      nlinarith
    linarith
  have hsqrt4 : Real.sqrt 15.53 < 4 := by
    have h : Real.sqrt 15.53 < Real.sqrt 16 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show Real.sqrt 16 = 4 from by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hx4lo : (2 / h0) ^ 2 ≤ xrr y2 y3 y4 :=
    xrr_simple_lower_bound_p22 y2 y3 y4 2 hy2lo hy2hi hy3lo hy3hi (by norm_num) hy4lo
  have hx4hi : xrr y2 y3 y4 ≤ (3.01 : ℝ) ^ 2 := by
    have h := xrr_simple_upper_bound_p22 y2 y3 y4 3.01 hy2lo hy2hi hy3lo hy3hi hy4lo hy4hi
      (by norm_num)
    rwa [show ((3.01 : ℝ) ^ 2) = 3.01 ^ 2 from rfl] at h
  have hx5lo3 : ((3 : ℝ) / h0) ^ 2 ≤ xrr y1 y3 y5 :=
    xrr_simple_lower_bound_p22 y1 y3 y5 3 hy1lo hy1hi hy3lo hy3hi (by norm_num) hy5gt
  have hx5lo : ((2.38 : ℝ)) ^ 2 ≤ xrr y1 y3 y5 := by
    have hc : ((2.38 : ℝ)) ^ 2 ≤ ((3 : ℝ) / h0) ^ 2 := by
      rw [h0_eq_p22]
      norm_num
    linarith
  have hx5hi : xrr y1 y3 y5 ≤ 15.53 := by
    have h := hxrr
    rw [hy1def, hy3def, hy5def, dist_comm (v (p + 1)) (v (p + 3))]
    exact h
  have hx6lo3 : ((3 : ℝ) / h0) ^ 2 ≤ xrr y1 y2 y6 :=
    xrr_simple_lower_bound_p22 y1 y2 y6 3 hy1lo hy1hi hy2lo hy2hi (by norm_num) hy6ge
  have hx6lo : ((2.38 : ℝ)) ^ 2 ≤ xrr y1 y2 y6 := by
    have hc : ((2.38 : ℝ)) ^ 2 ≤ ((3 : ℝ) / h0) ^ 2 := by
      rw [h0_eq_p22]
      norm_num
    linarith
  have hx6hi : xrr y1 y2 y6 ≤ 15.53 := by
    have h := xrr_simple_upper_bound_p22 y1 y2 y6 (Real.sqrt 15.53)
      hy1lo hy1hi hy2lo hy2hi hy6lo hy6le hsqrt4
    rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15.53)] at h
  have hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6) := by
    have h := g482w3_upsX_pos_of_not_col (a := (0 : V3)) (b := v (p + 3)) (c := v p)
      (hnc (p + 3) p (by omega))
    have e1 : dist (0 : V3) (v (p + 3)) = y1 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy1def]
    have e2 : dist (0 : V3) (v p) = y2 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy2def]
    have e4 : dist (v (p + 3)) (v p) = y6 := by rw [dist_comm (v (p + 3)) (v p), ← hy6def]
    rw [e1, e2, e4] at h
    exact h
  have hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5) := by
    have h := g482w3_upsX_pos_of_not_col (a := (0 : V3)) (b := v (p + 3)) (c := v (p + 1))
      (hnc (p + 3) (p + 1) (by omega))
    have e1 : dist (0 : V3) (v (p + 3)) = y1 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy1def]
    have e2 : dist (0 : V3) (v (p + 1)) = y3 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy3def]
    have e4 : dist (v (p + 3)) (v (p + 1)) = y5 := by
      rw [dist_comm (v (p + 3)) (v (p + 1)), ← hy5def]
    rw [e1, e2, e4] at h
    exact h
  -- ═══ K. `LEMMA_6843920790`: `taum` is strictly increasing near `y4` ═══
  have hd4pos : 0 < deltaY y1 y2 y3 y4 y5 y6 := by
    have hd := g482w3_deltaY_pos (u0 := (0 : V3)) (u1 := v (p + 3)) (u2 := v p)
      (u3 := v (p + 1)) hncop4
    have e1 : dist (0 : V3) (v (p + 3)) = y1 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy1def]
    have e2 : dist (0 : V3) (v p) = y2 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy2def]
    have e3 : dist (0 : V3) (v (p + 1)) = y3 := by
      rw [dist_eq_norm, zero_sub, norm_neg, hy3def]
    have e4 : dist (v p) (v (p + 1)) = y4 := hy4def.symm
    have e5 : dist (v (p + 3)) (v (p + 1)) = y5 := by
      rw [dist_comm (v (p + 3)) (v (p + 1)), ← hy5def]
    have e6 : dist (v (p + 3)) (v p) = y6 := by
      rw [dist_comm (v (p + 3)) (v p), ← hy6def]
    rw [e1, e2, e3, e4, e5, e6] at hd
    exact hd
  obtain ⟨a, b, hy4ab, hmono⟩ := LEMMA_6843920790_p22 h y1 y2 y3 y4 y5 y6
    ⟨hy1lo, hy1hi⟩ ⟨hy2lo, hy2hi⟩ ⟨hy3lo, hy3hi⟩ ⟨hy4lo, hy4hi⟩
    ⟨hy5gt, hx5hi⟩ ⟨hy6ge, hx6hi⟩ hd4pos
  -- a ball around `y4` inside the (open) monotonicity interval
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_Ioo y4 hy4ab
  have hball' : ∀ q : ℝ, |q - y4| < ρ → q ∈ Set.Ioo a b := by
    intro q hq
    exact hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hq)
  obtain ⟨e8, he8, h8e7, h8ρ⟩ := epsilon_pair_p21 e7 ρ he7 hρ
  obtain ⟨t, ht8, htneg⟩ : ∃ t : ℝ, |t| < e8 ∧ t < 0 :=
    ⟨-e8 / 2, by rw [abs_lt]; constructor <;> linarith, by linarith⟩
  have htabs : |t| < e7 := h8e7 t ht8
  have hy4'lt : taum y1 y2 y3 (y4 + t) y5 y6 < taum y1 y2 y3 y4 y5 y6 := by
    have htρ : |(y4 + t) - y4| < ρ := by
      rw [show y4 + t - y4 = t by ring]
      exact h8ρ t ht8
    exact hmono (y4 + t) y4 (hball' _ htρ) hy4ab (by linarith)
  -- ═══ L. minimality at the deformed configuration ═══
  set y4' : ℝ := y4 + t with hy4'def
  have hy4'eq : y4' = y4 + t := hy4'def
  have habs7 : |t| = -t := abs_of_neg htneg
  have hw : BBsV39 s (fun i => f (v i) t) := hBBdef t (h7eBB t htabs)
  have hmin := MMs_minimize_tau_fun_p21 s 4 v (fun i => f (v i) t) hs' hb hk (by norm_num)
    hvBBp hw
  -- ═══ M. expand the two `rhoFun * azim` sums (HOL `periodic_sum` block) ═══
  have hsum4 : ∀ (g : ℕ → ℝ), periodic g 4 → setSum {i : ℕ | i < 4} g =
      g p + g (p + 1) + g (p + 2) + g (p + 3) := by
    intro g hg4
    have hfin : ({i : ℕ | i < 4} : Set ℕ).Finite := Set.finite_lt_nat 4
    have hset : setSum {i : ℕ | i < 4} g = ∑ x ∈ Finset.range 4, g x := by
      rw [setSum, dif_pos hfin]
      congr 1
      ext x; simp
    rw [hset, ← periodic_sum hg4 (by norm_num) p]
    have hI : Finset.Icc p (4 - 1 + p) = ({p, p + 1, p + 2, p + 3} : Finset ℕ) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hI]
    rw [Finset.sum_insert (by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; omega)]
    rw [Finset.sum_insert (by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; omega)]
    rw [Finset.sum_insert (by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; omega)]
    rw [Finset.sum_singleton]
    ring
  have hpergv : periodic (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))) 4 := by
    intro i
    show rhoFun ‖v (i + 4)‖ * azim 0 (v (i + 4)) (v (i + 4 + 1)) (v (i + 4 + 3)) =
      rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))
    rw [show i + 4 + 1 = (i + 1) + 4 by omega, show i + 4 + 3 = (i + 3) + 4 by omega,
      hperv i, hperv (i + 1), hperv (i + 3)]
  have hpergw : periodic (fun i => rhoFun ‖f (v i) t‖ *
      azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) 4 := by
    intro i
    show rhoFun ‖f (v (i + 4)) t‖ * azim 0 (f (v (i + 4)) t) (f (v (i + 4 + 1)) t)
        (f (v (i + 4 + 3)) t) =
      rhoFun ‖f (v i) t‖ * azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)
    rw [show i + 4 + 1 = (i + 1) + 4 by omega, show i + 4 + 3 = (i + 3) + 4 by omega,
      hperv i, hperv (i + 1), hperv (i + 3)]
  have hSv := hsum4 (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))) hpergv
  have hSw := hsum4 (fun i => rhoFun ‖f (v i) t‖ *
    azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) hpergw
  have hmin' : setSum {i : ℕ | i < 4} (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3)))
      ≤ setSum {i : ℕ | i < 4} (fun i => rhoFun ‖f (v i) t‖ *
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) := by
    simpa only using hmin
  -- ═══ N. name the azimuth atoms ═══
  set A013 : ℝ := azim 0 (v p) (v (p + 1)) (v (p + 3)) with hA013
  set A120 : ℝ := azim 0 (v (p + 1)) (v (p + 2)) (v p) with hA120
  set B301 : ℝ := azim 0 (v (p + 3)) (v p) (v (p + 2)) with hB301
  set A312 : ℝ := azim 0 (v (p + 3)) (v (p + 1)) (v (p + 2)) with hA312
  set A231 : ℝ := azim 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) with hA231
  set A301 : ℝ := azim 0 (v (p + 3)) (v p) (v (p + 1)) with hA301
  set A123 : ℝ := azim 0 (v (p + 1)) (v (p + 2)) (v (p + 3)) with hA123
  set D : ℝ := azim 0 (v (p + 1)) (v (p + 3)) (v p) with hD
  set F013 : ℝ := azim 0 (f (v p) t) (v (p + 1)) (v (p + 3)) with hF013
  set F120 : ℝ := azim 0 (v (p + 1)) (v (p + 2)) (f (v p) t) with hF120
  set F301 : ℝ := azim 0 (v (p + 3)) (f (v p) t) (v (p + 2)) with hF301
  set G301 : ℝ := azim 0 (v (p + 3)) (f (v p) t) (v (p + 1)) with hG301
  set D' : ℝ := azim 0 (v (p + 1)) (v (p + 3)) (f (v p) t) with hD'
  have hgv_exp : setSum {i : ℕ | i < 4}
      (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + 3))) =
      rhoFun y2 * A013 + rhoFun y3 * A120 + rhoFun y1 * B301 +
        rhoFun ‖v (p + 2)‖ * A231 := by
    rw [hSv]
    rw [show p + 1 + 3 = p + 4 by omega, hperv p, show p + 2 + 3 = (p + 1) + 4 by omega,
      hperv (p + 1), show p + 3 + 3 = p + 6 by omega, show p + 6 = (p + 2) + 4 by omega,
      hperv (p + 2),
      ← hy1def, ← hy2def, ← hy3def, ← hA120, ← hB301, ← hA231]
    ring
  have hgw_exp : setSum {i : ℕ | i < 4} (fun i => rhoFun ‖f (v i) t‖ *
      azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 3)) t)) =
      rhoFun y2 * F013 + rhoFun y3 * F120 + rhoFun y1 * F301 +
        rhoFun ‖v (p + 2)‖ * A231 := by
    rw [hSw]
    rw [show p + 1 + 1 = p + 2 by omega, show p + 1 + 3 = p + 4 by omega,
      show p + 3 + 1 = p + 4 by omega, show p + 3 + 3 = p + 6 by omega,
      show p + 6 = (p + 2) + 4 by omega, show p + 2 + 3 = (p + 1) + 4 by omega,
      hperv p, hperv (p + 1), hperv (p + 2),
      hfix (v (p + 1)) t (hne_vp (p + 1) (by omega)),
      hfix (v (p + 2)) t (hne_vp (p + 2) (by omega)),
      hfix (v (p + 3)) t (hne_vp (p + 3) (by omega)),
      hnormf p t (h7e' t htabs), ← hy1def, ← hy2def, ← hy3def,
      ← hF013, ← hF120, ← hF301, ← hA231]
    ring
  -- ═══ O. the strict-drop contradiction ═══
  have hcmp : rhoFun y2 * A013 + rhoFun y3 * A120 + rhoFun y1 * B301
      ≤ rhoFun y2 * F013 + rhoFun y3 * F120 + rhoFun y1 * F301 := by
    have h := hmin'
    rw [hgv_exp, hgw_exp] at h
    linarith
  have hA120_split : A120 = A123 + D := hsum2
  have hF120_split : F120 = A123 + D' := by
    have hsumB := (hBall t (h7eB t htabs)).2.2.2
    rw [hfix (v (p + 1)) t (hne_vp (p + 1) (by omega)),
      hfix (v (p + 2)) t (hne_vp (p + 2) (by omega)),
      hfix (v (p + 3)) t (hne_vp (p + 3) (by omega))] at hsumB
    exact hsumB.symm
  have hB301_split : B301 = A301 + A312 := hsum1
  have hF301_split : F301 = G301 + A312 := by
    have hsumA := (hAall t (h7eA t htabs)).2.2.2
    rw [hfix (v (p + 3)) t (hne_vp (p + 3) (by omega)),
      hfix (v (p + 1)) t (hne_vp (p + 1) (by omega)),
      hfix (v (p + 2)) t (hne_vp (p + 2) (by omega))] at hsumA
    exact hsumA.symm
  have hWC : azim 0 (f (v p) t) (v (p + 1)) (v (p + 3)) < Real.pi := by
    have h := hWall t (h7eW t htabs)
    rwa [hfix (v (p + 1)) t (hne_vp (p + 1) (by omega)),
      hfix (v (p + 3)) t (hne_vp (p + 3) (by omega))] at h
  have hGle : azim 0 (v (p + 3)) (f (v p) t) (v (p + 1)) ≤ Real.pi := by
    have hnc1 : ¬ Collinear ℝ ({0, f (v p) t, v (p + 1)} : Set V3) :=
      (notcoplanar_imp_notcollinear_fan (x := (0 : V3)) (v := f (v p) t)
        (u := v (p + 1)) (w := v (p + 3)) (hNP t (h7eNP t htabs))).2.1
    have hnc2 : ¬ Collinear ℝ ({0, f (v p) t, v (p + 3)} : Set V3) :=
      (notcoplanar_imp_notcollinear_fan (x := (0 : V3)) (v := f (v p) t)
        (u := v (p + 1)) (w := v (p + 3)) (hNP t (h7eNP t htabs))).2.2
    have hposW : 0 < azim 0 (f (v p) t) (v (p + 1)) (v (p + 3)) := by
      have h := LOCAL_FAN_AZIM_POS_p22 s (fun i => f (v i) t) p
        (by
          rcases hw.2.2.2 with hle | hcl
          · omega
          · exact hcl)
        hs' hw
      rw [hk] at h
      simp only [Nat.reduceSub] at h
      rwa [hfix (v (p + 1)) t (hne_vp (p + 1) (by omega)),
        hfix (v (p + 3)) t (hne_vp (p + 3) (by omega))] at h
    exact le_of_lt (g482w3_azim_cycle (x := f (v p) t) (y := v (p + 1)) (z := v (p + 3))
      hnc1 hnc2 hposW hWC).2.2
  have htau_base : taum y1 y2 y3 y4 y5 y6 =
      rho y2 * A013 + rho y3 * D + rho y1 * A301 - (Real.pi + sol0) := by
    rw [g482w3_taum_cyc y1 y2 y3 y4 y5 y6,
      ← tau3_taum_nonplanar_p21 (v p) (v (p + 1)) (v (p + 3)) hncop,
      tau3_azim_p21 (v p) (v (p + 1)) (v (p + 3)) hncop (le_of_lt ha013_lt)]
  have hd4 : dist (f (v p) t) (v (p + 1)) = y4' := by
    rw [dist_comm, hdist2 _ (h7e' _ htabs),
      show dist (v (p + 1)) (v p) = y4 from by rw [dist_comm, ← hy4def]]
    rw [habs7]
    linarith [hy4'eq]
  have htaum_congr : taum y1 y2 y3 y4' y5 y6 =
      taum ‖f (v p) t‖ ‖v (p + 1)‖ ‖v (p + 3)‖ (dist (v (p + 1)) (v (p + 3)))
        (dist (f (v p) t) (v (p + 3))) (dist (f (v p) t) (v (p + 1))) := by
    rw [g482w3_taum_cyc y1 y2 y3 y4' y5 y6]
    rw [hy2def, hnormf p t (h7e' t htabs), hy3def, hy1def, hy5def, hy6def,
      dist_comm (v p) (v (p + 3)), ← hdist1 _ (h7e' _ htabs),
      dist_comm (v (p + 3)) (f (v p) t), ← hd4]
  have htau_def : taum y1 y2 y3 y4' y5 y6 =
      rho y2 * F013 + rho y3 * D' + rho y1 * G301 - (Real.pi + sol0) := by
    rw [htaum_congr,
      ← tau3_taum_nonplanar_p21 (f (v p) t) (v (p + 1)) (v (p + 3))
        (hNP t (h7eNP t htabs)),
      tau3_azim_p21 (f (v p) t) (v (p + 1)) (v (p + 3)) (hNP t (h7eNP t htabs))
        (le_of_lt hWC)]
    rw [hnormf p t (h7e' t htabs), ← hy1def, ← hy2def, ← hy3def, ← hF013, ← hD', ← hG301]
  have hcmp_rho : rho y2 * A013 + rho y3 * A120 + rho y1 * B301
      ≤ rho y2 * F013 + rho y3 * F120 + rho y1 * F301 := by
    simpa only [rho_rho_fun] using hcmp
  have hstep : rho y2 * A013 + rho y3 * D + rho y1 * A301
      ≤ rho y2 * F013 + rho y3 * D' + rho y1 * G301 := by
    have h := hcmp_rho
    rw [hA120_split, hF120_split, hB301_split, hF301_split] at h
    linarith [h]
  have hmain : taum y1 y2 y3 y4 y5 y6 ≤ taum y1 y2 y3 y4' y5 y6 := by
    rw [htau_base, htau_def]
    linarith [hstep]
  linarith [hy4'lt]


/-- `delta4Y < 0` + `deltaY > 0` + `0 < y1` gives the obtuse dihedral
(HOL `Ocbicby.delta4_y_imp_obtuse`; the LA22 twin is unproved, so this is
the atn2-sign proof of the same statement). -/
private theorem vas10_obtuse_of_delta4 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (h4 : delta4Y y1 y2 y3 y4 y5 y6 < 0) :
    Real.pi / 2 < dihY y1 y2 y3 y4 y5 y6 := by
  have hy : 0 < y1 * y1 := mul_pos hy1 hy1
  have hsqrt : 0 < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) := by
    rw [Real.sqrt_pos]
    nlinarith
  have h := (ea1_atn2_pos (Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6))
    (-(delta4Y y1 y2 y3 y4 y5 y6)) hsqrt).mpr (by linarith)
  have e : dihY y1 y2 y3 y4 y5 y6 =
      Real.pi / 2 + atn2 (Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6))
        (-(delta4Y y1 y2 y3 y4 y5 y6)) := rfl
  rw [e]
  linarith

/-- `dihY` is invariant under the (2 3)(5 6) leg swap (HOL
`Nonlinear_lemma.dih_y_sym`; public twin `dihY_sym23P25` lives in
`PackingAuto25`, outside this module's closure). -/
private theorem vas10_dihY_swap23 (a b c d e g : ℝ) :
    dihY a b c d e g = dihY a c b d g e := by
  have hD2 : ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      deltaX x1 x2 x3 x4 x5 x6 = deltaX x1 x3 x2 x4 x6 x5 := by
    intro x1 x2 x3 x4 x5 x6; unfold deltaX; ring
  have hD4 : ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      deltaX4 x1 x2 x3 x4 x5 x6 = deltaX4 x1 x3 x2 x4 x6 x5 := by
    intro x1 x2 x3 x4 x5 x6; unfold deltaX4; ring
  show dihXf (a * a) (b * b) (c * c) (d * d) (e * e) (g * g)
      = dihXf (a * a) (c * c) (b * b) (d * d) (g * g) (e * e)
  unfold dihXf
  rw [hD2 (a * a) (b * b) (c * c) (d * d) (e * e) (g * g),
    hD4 (a * a) (b * b) (c * c) (d * d) (e * e) (g * g)]

-- PROVED 2026-11-14 (lane `vaspwe1-w10`): case split on the `(p,p+2)`
-- diagonal; long case via the registry `6184614449` + the atn2 sign form of
-- `delta4_y_imp_obtuse` + the `DIHV_EQ_DIH_Y` bridge; short case refuted by
-- the two registry boxes `1348932091`/`5557288534` along `dih_y_mono`.
/-- HOL `LEMMA_PWE1` (JOTSWIX.hl:2706). NEEDS: the terminal registry
inequalities + `tau_fun`-`dih` kit (giant). -/
theorem LEMMA_PWE1_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ)
    (hs : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hab : ∀ i, s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0 ∨
      s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)
    (hg : scsGeneric v)
    (hns1 : ¬ scsIsStr s v (p + 1)) (hns3 : ¬ scsIsStr s v (p + 3))
    (hs1 : scsIsStr s v p) (hn : norm (v p) = 2)
    (ha01 : s.a p (p + 1) = 2) (ha31 : s.a (p + 3) p = 2)
    (hd : dist (v (p + 1)) (v (p + 2)) ≤ 2 * h0) :
    Real.pi / 2 < dihV 0 (v (p + 1)) (v (p + 2)) (v p) := by
  have h134d := h "1348932091 delta" (by simp [mainNonlinearTerminalV11Ids_t11])
  have h134 := h "1348932091" (by simp [mainNonlinearTerminalV11Ids_t11])
  have h555d := h "5557288534 delta" (by simp [mainNonlinearTerminalV11Ids_t11])
  have h555 := h "5557288534" (by simp [mainNonlinearTerminalV11Ids_t11])
  have h618 := h "6184614449" (by simp [mainNonlinearTerminalV11Ids_t11])
  -- ═══ A. substrate from `MMs_v39` ═══
  have hs' : isScsV39 s := hs
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpbP, -, hsym, -, -, hdiag, -, hbc, -, -, -⟩ := hs
  have hk4pos : 0 < (4 : ℕ) := by norm_num
  have hBBs : BBsV39 s v := by
    have h1 := hMM
    simp only [MMsV39, Set.mem_setOf_eq, BBprime2V39, BBprimeV39,
      Set.mem_setOf_eq] at h1
    exact h1.1.1.1
  have hBBs' : BBsV39 s v := hBBs
  obtain ⟨hann, hpervS, hbnd, hconv0⟩ := hBBs
  have hperv : Periodic v 4 := hk ▸ hpervS
  have hmod : ∀ i : ℕ, v (i % 4) = v i := fun i => periodic_mod_eq_p23 hperv i
  have hinj : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j :=
    BBs_inj_p21 s v 4 hs' hk hBBs'
  have hconv : ConvexLocalFan (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3))
      (Set.range fun i => (v i, v (i + 1))) := by
    rcases hconv0 with hle | hcl
    · omega
    · exact hcl
  have hgen : Generic (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)) := hg
  have hann' : ∀ i : ℕ, 2 ≤ ‖v i‖ ∧ ‖v i‖ ≤ 2 * h0 := by
    intro i
    have h := hann (Set.mem_range_self i)
    simp only [ballAnnulus, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at h
    exact ⟨h.2, h.1⟩
  have hpos : ∀ i : ℕ, 0 < azim 0 (v i) (v (i + 1)) (v (i + 3)) := by
    intro i
    have h1 := LOCAL_FAN_AZIM_POS_p22 s v i hconv hs' hBBs'
    rw [hk] at h1
    simpa using h1
  have hnc : ∀ i j : ℕ, i % 4 ≠ j % 4 → ¬ Collinear ℝ ({0, v i, v j} : Set V3) := by
    intro i j hij
    have hne : v i ≠ v j := by
      intro he
      exact hij (hinj (i % 4) (j % 4) (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos)
        (by rw [hmod i, hmod j]; exact he))
    exact PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 _ _ _ _ _ hconv.1 (Set.mem_range_self i)
      (Set.mem_range_self j) hne hgen
  have hlb : ∀ i j : ℕ, i % 4 ≠ j % 4 → 2 ≤ dist (v i) (v j) := by
    intro i j hij
    have h1 : s.a (i % 4) (j % 4) ≤ dist (v (i % 4)) (v (j % 4)) :=
      (hbnd (i % 4) (j % 4)).1
    have h2 : 2 ≤ s.a (i % 4) (j % 4) :=
      hdiag _ _ ⟨by rw [hk]; exact Nat.mod_lt _ hk4pos,
        by rw [hk]; exact Nat.mod_lt _ hk4pos, hij⟩
    rw [hmod i, hmod j] at h1
    linarith
  -- ═══ B. constants and the two edge upper bounds ═══
  have h2h0 : 2 * h0 = 2.52 := by unfold h0; norm_num
  have hcstab : cstab = 3.01 := rfl
  have hb01 : s.b p (p + 1) = 2 * h0 := by
    rcases hab p with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · exfalso
      rw [ha01] at h1
      unfold h0 at h1
      norm_num at h1
  have hBred : ∀ i j : ℕ, s.b i j = s.b (i % 4) (j % 4) :=
    fun i j => periodic2_MOD_p21 (by norm_num) (hk ▸ hpbP)
  have hAred : ∀ i j : ℕ, s.a i j = s.a (i % 4) (j % 4) :=
    fun i j => periodic2_MOD_p21 (by norm_num) (hk ▸ hpa)
  have hb31 : s.b (p + 3) p = 2 * h0 := by
    have hb : s.b (p + 3) ((p + 3) + 1) = s.b (p + 3) p := by
      rw [hBred (p + 3) ((p + 3) + 1), hBred (p + 3) p,
        show ((p + 3) + 1) % 4 = p % 4 by omega]
    have ha : s.a (p + 3) ((p + 3) + 1) = s.a (p + 3) p := by
      rw [hAred (p + 3) ((p + 3) + 1), hAred (p + 3) p,
        show ((p + 3) + 1) % 4 = p % 4 by omega]
    rcases hab (p + 3) with ⟨-, h1⟩ | ⟨h1, -⟩
    · rwa [hb] at h1
    · exfalso
      rw [ha, ha31] at h1
      unfold h0 at h1
      norm_num at h1
  have hd_pp1_le : dist (v p) (v (p + 1)) ≤ 2 * h0 := by
    have h1 := (hbnd p (p + 1)).2
    rwa [hb01] at h1
  have hd_p3p_le : dist (v (p + 3)) (v p) ≤ 2 * h0 := by
    have h1 := (hbnd (p + 3) p).2
    rwa [hb31] at h1
  -- ═══ C. the two non-coplanar quads at the non-straight vertices ═══
  have hncol_p1 : ¬ Coplanar ({0, v (p + 1), v (p + 2), v p} : Set V3) := by
    intro hc
    have hpos1 : 0 < azim 0 (v (p + 1)) (v (p + 2)) (v p) := by
      have h1 := hpos (p + 1)
      rwa [show (p + 1) + (4 - 1) = p + 4 by omega, hperv p] at h1
    rcases (AZIM_COND_FOR_COPLANAR (0 : V3) (v (p + 1)) (v (p + 2)) (v p)).mpr hc
      with h0' | hpi
    · linarith
    · refine hns1 ?_
      unfold scsIsStr
      rw [hk, show (p + 1) + (4 - 1) = p + 4 by omega, hperv p]
      exact hpi
  have hncol_p3 : ¬ Coplanar ({0, v (p + 3), v p, v (p + 2)} : Set V3) := by
    intro hc
    have hpos3 : 0 < azim 0 (v (p + 3)) (v p) (v (p + 2)) := by
      have h1 := hpos (p + 3)
      rwa [show (p + 3) + 1 = p + 4 by omega, hperv p,
        show (p + 3) + (4 - 1) = (p + 2) + 4 by omega, hperv (p + 2)] at h1
    rcases (AZIM_COND_FOR_COPLANAR (0 : V3) (v (p + 3)) (v p) (v (p + 2))).mpr hc
      with h0' | hpi
    · linarith
    · refine hns3 ?_
      unfold scsIsStr
      rw [hk, show (p + 3) + 1 = p + 4 by omega, hperv p,
        show (p + 3) + (4 - 1) = (p + 2) + 4 by omega, hperv (p + 2)]
      exact hpi
  have hncopA : ¬ Coplanar ({0, v p, v (p + 1), v (p + 2)} : Set V3) := by
    intro hc
    exact hncol_p1 (by
      have hset : ({0, v p, v (p + 1), v (p + 2)} : Set V3) = {0, v (p + 1), v (p + 2), v p} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset] at hc)
  have hncopB : ¬ Coplanar ({0, v p, v (p + 3), v (p + 2)} : Set V3) := by
    intro hc
    exact hncol_p3 (by
      have hset : ({0, v p, v (p + 3), v (p + 2)} : Set V3) = {0, v (p + 3), v p, v (p + 2)} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]; tauto
      rwa [hset] at hc)
  -- ═══ D. the `(p,p+2)` diagonal is long ═══
  by_cases hlong : (3.3 : ℝ) ≤ dist (v p) (v (p + 2))
  · -- ═══ D1. long diagonal: registry `6184614449` + atn2 sign + bridge ═══
    have hdelta4neg : delta4Y (‖v (p + 1)‖) (‖v (p + 2)‖) (‖v p‖)
        (dist (v (p + 2)) (v p)) (dist (v (p + 1)) (v p))
        (dist (v (p + 1)) (v (p + 2))) < 0 := by
      have h1 : (2 : ℝ) ≤ ‖v (p + 1)‖ ∧ ‖v (p + 1)‖ ≤ 2 * h0 := hann' (p + 1)
      have h2 : (2 : ℝ) ≤ ‖v (p + 2)‖ ∧ ‖v (p + 2)‖ ≤ 2 * h0 := hann' (p + 2)
      have h3 : (2 : ℝ) ≤ ‖v p‖ ∧ ‖v p‖ ≤ 2 * h0 := by
        refine ⟨?_, ?_⟩
        · rw [hn]
        · rw [hn]; linarith [h2h0]
      have h4 : (3.3 : ℝ) ≤ dist (v (p + 2)) (v p) ∧
          dist (v (p + 2)) (v p) ≤ 4 * h0 := by
        refine ⟨by rw [dist_comm]; exact hlong, ?_⟩
        have ht := dist_triangle (v (p + 2)) (0 : V3) (v p)
        rw [dist_zero_right, dist_zero_left] at ht
        linarith [(hann' (p + 2)).2, (hann' p).2]
      have h5 : (2 : ℝ) ≤ dist (v (p + 1)) (v p) ∧
          dist (v (p + 1)) (v p) ≤ 2 * h0 :=
        ⟨by rw [dist_comm]; exact hlb p (p + 1) (by omega),
          by rw [dist_comm]; exact hd_pp1_le⟩
      have h6 : (2 : ℝ) ≤ dist (v (p + 1)) (v (p + 2)) ∧
          dist (v (p + 1)) (v (p + 2)) ≤ 2 * h0 :=
        ⟨hlb (p + 1) (p + 2) (by omega), hd⟩
      exact h618 _ _ _ _ _ _ h1.1 h1.2 h2.1 h2.2 h3.1 h3.2 h4.1 h4.2 h5.1 h5.2 h6.1 h6.2
    have hdeltapos : 0 < deltaY (‖v (p + 1)‖) (‖v (p + 2)‖) (‖v p‖)
        (dist (v (p + 2)) (v p)) (dist (v (p + 1)) (v p))
        (dist (v (p + 1)) (v (p + 2))) := by
      simpa only [dist_zero_left] using
        g482w3_deltaY_pos (u0 := (0 : V3)) (u1 := v (p + 1)) (u2 := v (p + 2))
          (u3 := v p) hncol_p1
    have hdih : Real.pi / 2 < dihY (‖v (p + 1)‖) (‖v (p + 2)‖) (‖v p‖)
        (dist (v (p + 2)) (v p)) (dist (v (p + 1)) (v p))
        (dist (v (p + 1)) (v (p + 2))) :=
      vas10_obtuse_of_delta4 _ _ _ _ _ _ (by linarith [(hann' (p + 1)).1])
        hdeltapos hdelta4neg
    rw [DIHV_EQ_DIH_Y_4PT_B (0 : V3) (v (p + 1)) (v (p + 2)) (v p)
      (hnc (p + 1) (p + 2) (by omega)) (hnc (p + 1) p (by omega))]
    rw [dist_zero_left, dist_zero_left, dist_zero_left]
    exact hdih
  · -- ═══ D2. short diagonal: the two registry boxes contradict `scs_is_str` ═══
    have hsd : dist (v p) (v (p + 2)) < 3.3 := not_le.mp hlong
    have hspace : (2 : ℝ) ≤ ‖v p‖ ∧ ‖v p‖ ≤ 2 := by
      rw [hn]; norm_num
    have hspace12 : (2 : ℝ) ≤ ‖v (p + 1)‖ ∧ ‖v (p + 1)‖ ≤ 2.52 := by
      have h1 := hann' (p + 1); rw [← h2h0]; exact h1
    have hspace2 : (2 : ℝ) ≤ ‖v (p + 2)‖ ∧ ‖v (p + 2)‖ ≤ 2.52 := by
      have h1 := hann' (p + 2); rw [← h2h0]; exact h1
    have hspace3 : (2 : ℝ) ≤ ‖v (p + 3)‖ ∧ ‖v (p + 3)‖ ≤ 2.52 := by
      have h1 := hann' (p + 3); rw [← h2h0]; exact h1
    have hspace4 : (2.52 : ℝ) ≤ 2 * h0 ∧ 2 * h0 ≤ 2.52 := by
      rw [h2h0]; norm_num
    have hspace5 : (3.01 : ℝ) ≤ dist (v p) (v (p + 2)) ∧
        dist (v p) (v (p + 2)) ≤ 3.3 := by
      refine ⟨?_, le_of_lt hsd⟩
      have h1 := (hdg p (p + 2) (by unfold scsDiag; omega)).2.1
      rw [hcstab] at h1
      linarith
    have hspace6 : (2 : ℝ) ≤ dist (v p) (v (p + 1)) ∧
        dist (v p) (v (p + 1)) ≤ 2.52 := by
      refine ⟨hlb p (p + 1) (by omega), ?_⟩
      rw [← h2h0]; exact hd_pp1_le
    have hspace4' : (3.01 : ℝ) ≤ cstab ∧ cstab ≤ 3.01 := by
      rw [hcstab]; norm_num
    have hspace6' : (2 : ℝ) ≤ dist (v p) (v (p + 3)) ∧
        dist (v p) (v (p + 3)) ≤ 2.52 := by
      refine ⟨hlb p (p + 3) (by omega), ?_⟩
      rw [dist_comm, ← h2h0]; exact hd_p3p_le
    -- the `A` box: `y4 = 2*h0` registry, then `dih_y_mono` down to the true edge
    have hdelta2h0 : 0 < deltaY (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖) (2 * h0)
        (dist (v p) (v (p + 2))) (dist (v p) (v (p + 1))) :=
      h134d _ _ _ _ _ _ hspace.1 hspace.2 hspace12.1 hspace12.2 hspace2.1 hspace2.2
        hspace4.1 hspace4.2 hspace5.1 hspace5.2 hspace6.1 hspace6.2
    have hdih2h0 : dihY (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖) (2 * h0)
        (dist (v p) (v (p + 2))) (dist (v p) (v (p + 1))) < 1.4 :=
      h134 _ _ _ _ _ _ hspace.1 hspace.2 hspace12.1 hspace12.2 hspace2.1 hspace2.2
        hspace4.1 hspace4.2 hspace5.1 hspace5.2 hspace6.1 hspace6.2
    have hApos : 0 < deltaY (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖)
        (dist (v (p + 1)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 1))) := by
      simpa only [dist_zero_left] using
        g482w3_deltaY_pos (u0 := (0 : V3)) (u1 := v p) (u2 := v (p + 1))
          (u3 := v (p + 2)) hncopA
    have hA_bound : dihY (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖)
        (dist (v (p + 1)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 1))) < 1.4 := by
      have hmono := dih_y_mono_p22 (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖)
        (dist (v (p + 1)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 1))) (2 * h0)
        hd (by rw [hn]; norm_num)
        (by linarith [hlb (p + 1) (p + 2) (by omega : (p + 1) % 4 ≠ (p + 2) % 4)])
        hApos (le_of_lt hdelta2h0)
      linarith
    -- the `B` box: `y4 = cstab` registry at the (p+3) vertex
    have hdeltaC : 0 < deltaY (‖v p‖) (‖v (p + 3)‖) (‖v (p + 2)‖) cstab
        (dist (v p) (v (p + 2))) (dist (v p) (v (p + 3))) :=
      h555d _ _ _ _ _ _ hspace.1 hspace.2 hspace3.1 hspace3.2 hspace2.1 hspace2.2
        hspace4'.1 hspace4'.2 hspace5.1 hspace5.2 hspace6'.1 hspace6'.2
    have hdihC : dihY (‖v p‖) (‖v (p + 3)‖) (‖v (p + 2)‖) cstab
        (dist (v p) (v (p + 2))) (dist (v p) (v (p + 3))) < 1.7 :=
      h555 _ _ _ _ _ _ hspace.1 hspace.2 hspace3.1 hspace3.2 hspace2.1 hspace2.2
        hspace4'.1 hspace4'.2 hspace5.1 hspace5.2 hspace6'.1 hspace6'.2
    have hBpos : 0 < deltaY (‖v p‖) (‖v (p + 3)‖) (‖v (p + 2)‖)
        (dist (v (p + 3)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 3))) := by
      simpa only [dist_zero_left] using
        g482w3_deltaY_pos (u0 := (0 : V3)) (u1 := v p) (u2 := v (p + 3))
          (u3 := v (p + 2)) hncopB
    have hle4 : dist (v (p + 3)) (v (p + 2)) ≤ cstab := by
      have h1 := (hbnd (p + 2) (p + 3)).2
      rw [dist_comm]
      exact le_trans h1 (hbc (p + 2) (by omega))
    have hB_bound : dihY (‖v p‖) (‖v (p + 3)‖) (‖v (p + 2)‖)
        (dist (v (p + 3)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 3))) < 1.7 := by
      have hmono := dih_y_mono_p22 (‖v p‖) (‖v (p + 3)‖) (‖v (p + 2)‖)
        (dist (v (p + 3)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 3))) cstab hle4 (by rw [hn]; norm_num)
        (by linarith [hlb (p + 3) (p + 2) (by omega : (p + 3) % 4 ≠ (p + 2) % 4)])
        hBpos (le_of_lt hdeltaC)
      linarith
    -- the azimuth split at `v p` and the two `azim = dihV` conversions
    have hs1' : azim 0 (v p) (v (p + 1)) (v (p + 3)) = Real.pi := by
      have h1 := hs1
      unfold scsIsStr at h1
      rwa [hk] at h1
    have hsplit := vv_split_azim_generic_p22 v 4 p 2 3 hperv (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hgen hconv
      (fun a b hab' => hinj a b hab'.1 hab'.2.1 hab'.2.2)
    have hAle : azim 0 (v p) (v (p + 1)) (v (p + 2)) ≤ Real.pi := by
      have hnn := azim_nonneg (0 : V3) (v p) (v (p + 2)) (v (p + 3))
      linarith
    have hBle : azim 0 (v p) (v (p + 2)) (v (p + 3)) ≤ Real.pi := by
      have hnn := azim_nonneg (0 : V3) (v p) (v (p + 1)) (v (p + 2))
      linarith
    have hDihA := AZIM_DIHV_SAME_STRONG (v := (0 : V3)) (w := v p)
      (v1 := v (p + 1)) (v2 := v (p + 2))
      (hnc p (p + 1) (by omega)) (hnc p (p + 2) (by omega)) hAle
    have hDihB := AZIM_DIHV_SAME_STRONG (v := (0 : V3)) (w := v p)
      (v1 := v (p + 2)) (v2 := v (p + 3))
      (hnc p (p + 2) (by omega)) (hnc p (p + 3) (by omega)) hBle
    have hsum : Real.pi = dihY (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖)
        (dist (v (p + 1)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 1)))
        + dihY (‖v p‖) (‖v (p + 2)‖) (‖v (p + 3)‖)
          (dist (v (p + 2)) (v (p + 3))) (dist (v p) (v (p + 3)))
          (dist (v p) (v (p + 2))) := by
      have h1 : Real.pi = azim 0 (v p) (v (p + 1)) (v (p + 2))
          + azim 0 (v p) (v (p + 2)) (v (p + 3)) := by
        rw [← hsplit]; exact hs1'.symm
      rw [hDihA, hDihB] at h1
      have e1 := DIHV_EQ_DIH_Y_4PT_B (0 : V3) (v p) (v (p + 1)) (v (p + 2))
        (hnc p (p + 1) (by omega)) (hnc p (p + 2) (by omega))
      have e2 := DIHV_EQ_DIH_Y_4PT_B (0 : V3) (v p) (v (p + 2)) (v (p + 3))
        (hnc p (p + 2) (by omega)) (hnc p (p + 3) (by omega))
      rw [e1, e2] at h1
      simpa only [dist_zero_left] using h1
    have hB'' : dihY (‖v p‖) (‖v (p + 2)‖) (‖v (p + 3)‖)
        (dist (v (p + 2)) (v (p + 3))) (dist (v p) (v (p + 3)))
        (dist (v p) (v (p + 2))) < 1.7 := by
      have h1 := vas10_dihY_swap23 (‖v p‖) (‖v (p + 2)‖) (‖v (p + 3)‖)
        (dist (v (p + 2)) (v (p + 3))) (dist (v p) (v (p + 3)))
        (dist (v p) (v (p + 2)))
      rw [h1, dist_comm (v (p + 2)) (v (p + 3))]
      exact hB_bound
    exfalso
    linarith [Real.pi_gt_d2]

-- PROVED 2026-11-14 (lane `vaspwe2-w11`): the `PWE1` mirror across the
-- `(p+2),(p+3)` edge; same two-branch skeleton, roles of the two registry
-- boxes swapped (`5557288534`/cstab now at the `(p+1)` vertex, `1348932091`/
-- `2*h0` at the `(p+3)` vertex) — see DELIVERY for the HOL line mapping.
/-- HOL `LEMMA_PWE2` (JOTSWIX.hl:2994): the `PWE1` mirror across the
`(p+2),(p+3)` edge. NEEDS: same kit as `LEMMA_PWE1_p23`. -/
theorem LEMMA_PWE2_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ)
    (hs : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hab : ∀ i, s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0 ∨
      s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)
    (hg : scsGeneric v)
    (hns1 : ¬ scsIsStr s v (p + 1)) (hns3 : ¬ scsIsStr s v (p + 3))
    (hs1 : scsIsStr s v p) (hn : norm (v p) = 2)
    (ha01 : s.a p (p + 1) = 2) (ha31 : s.a (p + 3) p = 2)
    (hd : dist (v (p + 2)) (v (p + 3)) ≤ 2 * h0) :
    Real.pi / 2 < dihV 0 (v (p + 3)) (v p) (v (p + 2)) := by
  have h134d := h "1348932091 delta" (by simp [mainNonlinearTerminalV11Ids_t11])
  have h134 := h "1348932091" (by simp [mainNonlinearTerminalV11Ids_t11])
  have h555d := h "5557288534 delta" (by simp [mainNonlinearTerminalV11Ids_t11])
  have h555 := h "5557288534" (by simp [mainNonlinearTerminalV11Ids_t11])
  have h618 := h "6184614449" (by simp [mainNonlinearTerminalV11Ids_t11])
  -- ═══ A. substrate from `MMs_v39` ═══
  have hs' : isScsV39 s := hs
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpbP, -, hsym, -, -, hdiag, -, hbc, -, -, -⟩ := hs
  have hk4pos : 0 < (4 : ℕ) := by norm_num
  have hBBs : BBsV39 s v := by
    have h1 := hMM
    simp only [MMsV39, Set.mem_setOf_eq, BBprime2V39, BBprimeV39,
      Set.mem_setOf_eq] at h1
    exact h1.1.1.1
  have hBBs' : BBsV39 s v := hBBs
  obtain ⟨hann, hpervS, hbnd, hconv0⟩ := hBBs
  have hperv : Periodic v 4 := hk ▸ hpervS
  have hmod : ∀ i : ℕ, v (i % 4) = v i := fun i => periodic_mod_eq_p23 hperv i
  have hinj : ∀ i j : ℕ, i < 4 → j < 4 → v i = v j → i = j :=
    BBs_inj_p21 s v 4 hs' hk hBBs'
  have hconv : ConvexLocalFan (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3))
      (Set.range fun i => (v i, v (i + 1))) := by
    rcases hconv0 with hle | hcl
    · omega
    · exact hcl
  have hgen : Generic (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)) := hg
  have hann' : ∀ i : ℕ, 2 ≤ ‖v i‖ ∧ ‖v i‖ ≤ 2 * h0 := by
    intro i
    have h := hann (Set.mem_range_self i)
    simp only [ballAnnulus, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at h
    exact ⟨h.2, h.1⟩
  have hpos : ∀ i : ℕ, 0 < azim 0 (v i) (v (i + 1)) (v (i + 3)) := by
    intro i
    have h1 := LOCAL_FAN_AZIM_POS_p22 s v i hconv hs' hBBs'
    rw [hk] at h1
    simpa using h1
  have hnc : ∀ i j : ℕ, i % 4 ≠ j % 4 → ¬ Collinear ℝ ({0, v i, v j} : Set V3) := by
    intro i j hij
    have hne : v i ≠ v j := by
      intro he
      exact hij (hinj (i % 4) (j % 4) (Nat.mod_lt _ hk4pos) (Nat.mod_lt _ hk4pos)
        (by rw [hmod i, hmod j]; exact he))
    exact PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 _ _ _ _ _ hconv.1 (Set.mem_range_self i)
      (Set.mem_range_self j) hne hgen
  have hlb : ∀ i j : ℕ, i % 4 ≠ j % 4 → 2 ≤ dist (v i) (v j) := by
    intro i j hij
    have h1 : s.a (i % 4) (j % 4) ≤ dist (v (i % 4)) (v (j % 4)) :=
      (hbnd (i % 4) (j % 4)).1
    have h2 : 2 ≤ s.a (i % 4) (j % 4) :=
      hdiag _ _ ⟨by rw [hk]; exact Nat.mod_lt _ hk4pos,
        by rw [hk]; exact Nat.mod_lt _ hk4pos, hij⟩
    rw [hmod i, hmod j] at h1
    linarith
  -- ═══ B. constants and the two edge upper bounds ═══
  have h2h0 : 2 * h0 = 2.52 := by unfold h0; norm_num
  have hcstab : cstab = 3.01 := rfl
  have hb01 : s.b p (p + 1) = 2 * h0 := by
    rcases hab p with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · exfalso
      rw [ha01] at h1
      unfold h0 at h1
      norm_num at h1
  have hBred : ∀ i j : ℕ, s.b i j = s.b (i % 4) (j % 4) :=
    fun i j => periodic2_MOD_p21 (by norm_num) (hk ▸ hpbP)
  have hAred : ∀ i j : ℕ, s.a i j = s.a (i % 4) (j % 4) :=
    fun i j => periodic2_MOD_p21 (by norm_num) (hk ▸ hpa)
  have hb31 : s.b (p + 3) p = 2 * h0 := by
    have hb : s.b (p + 3) ((p + 3) + 1) = s.b (p + 3) p := by
      rw [hBred (p + 3) ((p + 3) + 1), hBred (p + 3) p,
        show ((p + 3) + 1) % 4 = p % 4 by omega]
    have ha : s.a (p + 3) ((p + 3) + 1) = s.a (p + 3) p := by
      rw [hAred (p + 3) ((p + 3) + 1), hAred (p + 3) p,
        show ((p + 3) + 1) % 4 = p % 4 by omega]
    rcases hab (p + 3) with ⟨-, h1⟩ | ⟨h1, -⟩
    · rwa [hb] at h1
    · exfalso
      rw [ha, ha31] at h1
      unfold h0 at h1
      norm_num at h1
  have hd_pp1_le : dist (v p) (v (p + 1)) ≤ 2 * h0 := by
    have h1 := (hbnd p (p + 1)).2
    rwa [hb01] at h1
  have hd_p3p_le : dist (v (p + 3)) (v p) ≤ 2 * h0 := by
    have h1 := (hbnd (p + 3) p).2
    rwa [hb31] at h1
  -- the mirror edge `(p+1),(p+2)` is a *consecutive* edge, hence `≤ cstab`
  have hd12_le : dist (v (p + 1)) (v (p + 2)) ≤ cstab := by
    have h1 := (hbnd (p + 1) (p + 2)).2
    have h2 := hbc (p + 1) (by omega : 3 < s.k)
    exact le_trans h1 h2
  -- ═══ C. the two non-coplanar quads at the non-straight vertices ═══
  have hncol_p1 : ¬ Coplanar ({0, v (p + 1), v (p + 2), v p} : Set V3) := by
    intro hc
    have hpos1 : 0 < azim 0 (v (p + 1)) (v (p + 2)) (v p) := by
      have h1 := hpos (p + 1)
      rwa [show (p + 1) + (4 - 1) = p + 4 by omega, hperv p] at h1
    rcases (AZIM_COND_FOR_COPLANAR (0 : V3) (v (p + 1)) (v (p + 2)) (v p)).mpr hc
      with h0' | hpi
    · linarith
    · refine hns1 ?_
      unfold scsIsStr
      rw [hk, show (p + 1) + (4 - 1) = p + 4 by omega, hperv p]
      exact hpi
  have hncol_p3 : ¬ Coplanar ({0, v (p + 3), v p, v (p + 2)} : Set V3) := by
    intro hc
    have hpos3 : 0 < azim 0 (v (p + 3)) (v p) (v (p + 2)) := by
      have h1 := hpos (p + 3)
      rwa [show (p + 3) + 1 = p + 4 by omega, hperv p,
        show (p + 3) + (4 - 1) = (p + 2) + 4 by omega, hperv (p + 2)] at h1
    rcases (AZIM_COND_FOR_COPLANAR (0 : V3) (v (p + 3)) (v p) (v (p + 2))).mpr hc
      with h0' | hpi
    · linarith
    · refine hns3 ?_
      unfold scsIsStr
      rw [hk, show (p + 3) + 1 = p + 4 by omega, hperv p,
        show (p + 3) + (4 - 1) = (p + 2) + 4 by omega, hperv (p + 2)]
      exact hpi
  have hncopA : ¬ Coplanar ({0, v p, v (p + 1), v (p + 2)} : Set V3) := by
    intro hc
    exact hncol_p1 (by
      have hset : ({0, v p, v (p + 1), v (p + 2)} : Set V3) = {0, v (p + 1), v (p + 2), v p} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset] at hc)
  have hncopB : ¬ Coplanar ({0, v p, v (p + 3), v (p + 2)} : Set V3) := by
    intro hc
    exact hncol_p3 (by
      have hset : ({0, v p, v (p + 3), v (p + 2)} : Set V3) = {0, v (p + 3), v p, v (p + 2)} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset] at hc)
  -- the long-diagonal branch needs the quad in the `(u1,u2,u3) = (p+3,p+2,p)` order
  have hncol_p3b : ¬ Coplanar ({0, v (p + 3), v (p + 2), v p} : Set V3) := by
    intro hc
    exact hncol_p3 (by
      have hset : ({0, v (p + 3), v (p + 2), v p} : Set V3) = {0, v (p + 3), v p, v (p + 2)} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset] at hc)
  -- ═══ D. the `(p,p+2)` diagonal is long ═══
  by_cases hlong : (3.3 : ℝ) ≤ dist (v p) (v (p + 2))
  · -- ═══ D1. long diagonal: registry `6184614449` at the (p+3) vertex ═══
    have hdelta4neg : delta4Y (‖v (p + 3)‖) (‖v (p + 2)‖) (‖v p‖)
        (dist (v (p + 2)) (v p)) (dist (v (p + 3)) (v p))
        (dist (v (p + 3)) (v (p + 2))) < 0 := by
      have h1 : (2 : ℝ) ≤ ‖v (p + 3)‖ ∧ ‖v (p + 3)‖ ≤ 2 * h0 := hann' (p + 3)
      have h2 : (2 : ℝ) ≤ ‖v (p + 2)‖ ∧ ‖v (p + 2)‖ ≤ 2 * h0 := hann' (p + 2)
      have h3 : (2 : ℝ) ≤ ‖v p‖ ∧ ‖v p‖ ≤ 2 * h0 := by
        refine ⟨?_, ?_⟩
        · rw [hn]
        · rw [hn]; linarith [h2h0]
      have h4 : (3.3 : ℝ) ≤ dist (v (p + 2)) (v p) ∧
          dist (v (p + 2)) (v p) ≤ 4 * h0 := by
        refine ⟨by rw [dist_comm]; exact hlong, ?_⟩
        have ht := dist_triangle (v (p + 2)) (0 : V3) (v p)
        rw [dist_zero_right, dist_zero_left] at ht
        linarith [(hann' (p + 2)).2, (hann' p).2]
      have h5 : (2 : ℝ) ≤ dist (v (p + 3)) (v p) ∧
          dist (v (p + 3)) (v p) ≤ 2 * h0 :=
        ⟨hlb (p + 3) p (by omega), hd_p3p_le⟩
      have h6 : (2 : ℝ) ≤ dist (v (p + 3)) (v (p + 2)) ∧
          dist (v (p + 3)) (v (p + 2)) ≤ 2 * h0 :=
        ⟨hlb (p + 3) (p + 2) (by omega), by rw [dist_comm]; exact hd⟩
      exact h618 _ _ _ _ _ _ h1.1 h1.2 h2.1 h2.2 h3.1 h3.2 h4.1 h4.2 h5.1 h5.2 h6.1 h6.2
    have hdeltapos : 0 < deltaY (‖v (p + 3)‖) (‖v (p + 2)‖) (‖v p‖)
        (dist (v (p + 2)) (v p)) (dist (v (p + 3)) (v p))
        (dist (v (p + 3)) (v (p + 2))) := by
      simpa only [dist_zero_left] using
        g482w3_deltaY_pos (u0 := (0 : V3)) (u1 := v (p + 3)) (u2 := v (p + 2))
          (u3 := v p) hncol_p3b
    have hdih : Real.pi / 2 < dihY (‖v (p + 3)‖) (‖v (p + 2)‖) (‖v p‖)
        (dist (v (p + 2)) (v p)) (dist (v (p + 3)) (v p))
        (dist (v (p + 3)) (v (p + 2))) :=
      vas10_obtuse_of_delta4 _ _ _ _ _ _ (by linarith [(hann' (p + 3)).1])
        hdeltapos hdelta4neg
    rw [DIHV_EQ_DIH_Y_4PT_B (0 : V3) (v (p + 3)) (v p) (v (p + 2))
      (hnc (p + 3) p (by omega)) (hnc (p + 3) (p + 2) (by omega))]
    rw [dist_zero_left, dist_zero_left, dist_zero_left]
    rw [vas10_dihY_swap23 (‖v (p + 3)‖) (‖v p‖) (‖v (p + 2)‖)
      (dist (v p) (v (p + 2))) (dist (v (p + 3)) (v (p + 2)))
      (dist (v (p + 3)) (v p))]
    rw [dist_comm (v p) (v (p + 2))]
    exact hdih
  · -- ═══ D2. short diagonal: the two registry boxes contradict `scs_is_str` ═══
    have hsd : dist (v p) (v (p + 2)) < 3.3 := not_le.mp hlong
    have hspace : (2 : ℝ) ≤ ‖v p‖ ∧ ‖v p‖ ≤ 2 := by
      rw [hn]; norm_num
    have hspace12 : (2 : ℝ) ≤ ‖v (p + 1)‖ ∧ ‖v (p + 1)‖ ≤ 2.52 := by
      have h1 := hann' (p + 1); rw [← h2h0]; exact h1
    have hspace2 : (2 : ℝ) ≤ ‖v (p + 2)‖ ∧ ‖v (p + 2)‖ ≤ 2.52 := by
      have h1 := hann' (p + 2); rw [← h2h0]; exact h1
    have hspace3 : (2 : ℝ) ≤ ‖v (p + 3)‖ ∧ ‖v (p + 3)‖ ≤ 2.52 := by
      have h1 := hann' (p + 3); rw [← h2h0]; exact h1
    have hspace4 : (2.52 : ℝ) ≤ 2 * h0 ∧ 2 * h0 ≤ 2.52 := by
      rw [h2h0]; norm_num
    have hspace5 : (3.01 : ℝ) ≤ dist (v p) (v (p + 2)) ∧
        dist (v p) (v (p + 2)) ≤ 3.3 := by
      refine ⟨?_, le_of_lt hsd⟩
      have h1 := (hdg p (p + 2) (by unfold scsDiag; omega)).2.1
      rw [hcstab] at h1
      linarith
    have hspace6 : (2 : ℝ) ≤ dist (v p) (v (p + 1)) ∧
        dist (v p) (v (p + 1)) ≤ 2.52 := by
      refine ⟨hlb p (p + 1) (by omega), ?_⟩
      rw [← h2h0]; exact hd_pp1_le
    have hspace4' : (3.01 : ℝ) ≤ cstab ∧ cstab ≤ 3.01 := by
      rw [hcstab]; norm_num
    have hspace6' : (2 : ℝ) ≤ dist (v p) (v (p + 3)) ∧
        dist (v p) (v (p + 3)) ≤ 2.52 := by
      refine ⟨hlb p (p + 3) (by omega), ?_⟩
      rw [dist_comm, ← h2h0]; exact hd_p3p_le
    -- the `A` box: `y4 = cstab` registry at the `(p+1)` vertex (mirror of PWE1's B)
    have hdeltaC : 0 < deltaY (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖) cstab
        (dist (v p) (v (p + 2))) (dist (v p) (v (p + 1))) :=
      h555d _ _ _ _ _ _ hspace.1 hspace.2 hspace12.1 hspace12.2 hspace2.1 hspace2.2
        hspace4'.1 hspace4'.2 hspace5.1 hspace5.2 hspace6.1 hspace6.2
    have hdihC : dihY (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖) cstab
        (dist (v p) (v (p + 2))) (dist (v p) (v (p + 1))) < 1.7 :=
      h555 _ _ _ _ _ _ hspace.1 hspace.2 hspace12.1 hspace12.2 hspace2.1 hspace2.2
        hspace4'.1 hspace4'.2 hspace5.1 hspace5.2 hspace6.1 hspace6.2
    have hApos : 0 < deltaY (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖)
        (dist (v (p + 1)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 1))) := by
      simpa only [dist_zero_left] using
        g482w3_deltaY_pos (u0 := (0 : V3)) (u1 := v p) (u2 := v (p + 1))
          (u3 := v (p + 2)) hncopA
    have hA_bound : dihY (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖)
        (dist (v (p + 1)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 1))) < 1.7 := by
      have hmono := dih_y_mono_p22 (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖)
        (dist (v (p + 1)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 1))) cstab
        hd12_le (by rw [hn]; norm_num)
        (by linarith [hlb (p + 1) (p + 2) (by omega : (p + 1) % 4 ≠ (p + 2) % 4)])
        hApos (le_of_lt hdeltaC)
      linarith
    -- the `B` box: `y4 = 2*h0` registry at the `(p+3)` vertex (mirror of PWE1's A)
    have hdelta2h0 : 0 < deltaY (‖v p‖) (‖v (p + 3)‖) (‖v (p + 2)‖) (2 * h0)
        (dist (v p) (v (p + 2))) (dist (v p) (v (p + 3))) :=
      h134d _ _ _ _ _ _ hspace.1 hspace.2 hspace3.1 hspace3.2 hspace2.1 hspace2.2
        hspace4.1 hspace4.2 hspace5.1 hspace5.2 hspace6'.1 hspace6'.2
    have hdih2h0 : dihY (‖v p‖) (‖v (p + 3)‖) (‖v (p + 2)‖) (2 * h0)
        (dist (v p) (v (p + 2))) (dist (v p) (v (p + 3))) < 1.4 :=
      h134 _ _ _ _ _ _ hspace.1 hspace.2 hspace3.1 hspace3.2 hspace2.1 hspace2.2
        hspace4.1 hspace4.2 hspace5.1 hspace5.2 hspace6'.1 hspace6'.2
    have hBpos : 0 < deltaY (‖v p‖) (‖v (p + 3)‖) (‖v (p + 2)‖)
        (dist (v (p + 3)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 3))) := by
      simpa only [dist_zero_left] using
        g482w3_deltaY_pos (u0 := (0 : V3)) (u1 := v p) (u2 := v (p + 3))
          (u3 := v (p + 2)) hncopB
    have hB_bound : dihY (‖v p‖) (‖v (p + 3)‖) (‖v (p + 2)‖)
        (dist (v (p + 3)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 3))) < 1.4 := by
      have hmono := dih_y_mono_p22 (‖v p‖) (‖v (p + 3)‖) (‖v (p + 2)‖)
        (dist (v (p + 3)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 3))) (2 * h0)
        (by rw [dist_comm]; exact hd) (by rw [hn]; norm_num)
        (by linarith [hlb (p + 3) (p + 2) (by omega : (p + 3) % 4 ≠ (p + 2) % 4)])
        hBpos (le_of_lt hdelta2h0)
      linarith
    -- the azimuth split at `v p` and the two `azim = dihV` conversions
    have hs1' : azim 0 (v p) (v (p + 1)) (v (p + 3)) = Real.pi := by
      have h1 := hs1
      unfold scsIsStr at h1
      rwa [hk] at h1
    have hsplit := vv_split_azim_generic_p22 v 4 p 2 3 hperv (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hgen hconv
      (fun a b hab' => hinj a b hab'.1 hab'.2.1 hab'.2.2)
    have hAle : azim 0 (v p) (v (p + 1)) (v (p + 2)) ≤ Real.pi := by
      have hnn := azim_nonneg (0 : V3) (v p) (v (p + 2)) (v (p + 3))
      linarith
    have hBle : azim 0 (v p) (v (p + 2)) (v (p + 3)) ≤ Real.pi := by
      have hnn := azim_nonneg (0 : V3) (v p) (v (p + 1)) (v (p + 2))
      linarith
    have hDihA := AZIM_DIHV_SAME_STRONG (v := (0 : V3)) (w := v p)
      (v1 := v (p + 1)) (v2 := v (p + 2))
      (hnc p (p + 1) (by omega)) (hnc p (p + 2) (by omega)) hAle
    have hDihB := AZIM_DIHV_SAME_STRONG (v := (0 : V3)) (w := v p)
      (v1 := v (p + 2)) (v2 := v (p + 3))
      (hnc p (p + 2) (by omega)) (hnc p (p + 3) (by omega)) hBle
    have hsum : Real.pi = dihY (‖v p‖) (‖v (p + 1)‖) (‖v (p + 2)‖)
        (dist (v (p + 1)) (v (p + 2))) (dist (v p) (v (p + 2)))
        (dist (v p) (v (p + 1)))
        + dihY (‖v p‖) (‖v (p + 2)‖) (‖v (p + 3)‖)
          (dist (v (p + 2)) (v (p + 3))) (dist (v p) (v (p + 3)))
          (dist (v p) (v (p + 2))) := by
      have h1 : Real.pi = azim 0 (v p) (v (p + 1)) (v (p + 2))
          + azim 0 (v p) (v (p + 2)) (v (p + 3)) := by
        rw [← hsplit]; exact hs1'.symm
      rw [hDihA, hDihB] at h1
      have e1 := DIHV_EQ_DIH_Y_4PT_B (0 : V3) (v p) (v (p + 1)) (v (p + 2))
        (hnc p (p + 1) (by omega)) (hnc p (p + 2) (by omega))
      have e2 := DIHV_EQ_DIH_Y_4PT_B (0 : V3) (v p) (v (p + 2)) (v (p + 3))
        (hnc p (p + 2) (by omega)) (hnc p (p + 3) (by omega))
      rw [e1, e2] at h1
      simpa only [dist_zero_left] using h1
    have hB'' : dihY (‖v p‖) (‖v (p + 2)‖) (‖v (p + 3)‖)
        (dist (v (p + 2)) (v (p + 3))) (dist (v p) (v (p + 3)))
        (dist (v p) (v (p + 2))) < 1.4 := by
      have h1 := vas10_dihY_swap23 (‖v p‖) (‖v (p + 2)‖) (‖v (p + 3)‖)
        (dist (v (p + 2)) (v (p + 3))) (dist (v p) (v (p + 3)))
        (dist (v p) (v (p + 2)))
      rw [h1, dist_comm (v (p + 2)) (v (p + 3))]
      exact hB_bound
    exfalso
    linarith [Real.pi_gt_d2]

/-- Taylor 下界包络（V12 私有复证，PA25:15727 同款；LP 通道专用）：
`arctan t ≥ t - t³/3 + t⁵/5 - t⁷/7 + t⁹/9 - t¹¹/11`（`[0,∞)`）。
导数误差 `+u¹²/(1+u²) ≥ 0`，FTC 于 `0`。 -/
private theorem vas12_arctan_ge_taylor6 (t : ℝ) (ht : 0 ≤ t) :
    t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 - t ^ 11 / 11 ≤ Real.arctan t := by
  have h3 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 3 / 3) (u ^ 2) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 3).div_const 3
  have h5 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 5 / 5) (u ^ 4) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 5).div_const 5
  have h7 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 7 / 7) (u ^ 6) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 7).div_const 7
  have h9 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 9 / 9) (u ^ 8) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 9).div_const 9
  have h11 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 11 / 11) (u ^ 10) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 11).div_const 11
  have hpoly : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7
      + v ^ 9 / 9 - v ^ 11 / 11) (1 - u ^ 2 + u ^ 4 - u ^ 6 + u ^ 8 - u ^ 10) u := by
    intro u
    have s1 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3) (1 - u ^ 2) u :=
      (hasDerivAt_id u).sub (h3 u)
    have s2 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5)
        (1 - u ^ 2 + u ^ 4) u := s1.add (h5 u)
    have s3 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7)
        (1 - u ^ 2 + u ^ 4 - u ^ 6) u := s2.sub (h7 u)
    have s4 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7
        + v ^ 9 / 9) (1 - u ^ 2 + u ^ 4 - u ^ 6 + u ^ 8) u := s3.add (h9 u)
    exact s4.sub (h11 u)
  have hf' : deriv (fun u => Real.arctan u
      - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9 - u ^ 11 / 11))
      = fun u => u ^ 12 / (1 + u ^ 2) := by
    funext u
    have hd : HasDerivAt (fun v : ℝ => Real.arctan v
        - (v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7 + v ^ 9 / 9 - v ^ 11 / 11))
        (1 / (1 + u ^ 2) - (1 - u ^ 2 + u ^ 4 - u ^ 6 + u ^ 8 - u ^ 10)) u :=
      HasDerivAt.sub (Real.hasDerivAt_arctan u) (hpoly u)
    rw [hd.deriv]
    field_simp
    ring
  have hdiff : ∀ x ∈ uIcc (0:ℝ) t, DifferentiableAt ℝ (fun u => Real.arctan u
      - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9 - u ^ 11 / 11)) x := by
    intro x _
    exact DifferentiableAt.sub (Real.differentiableAt_arctan x) (by fun_prop)
  have hcont : Continuous (fun u : ℝ => u ^ 12 / (1 + u ^ 2)) :=
    Continuous.div (by fun_prop) (by fun_prop)
      (fun u => ne_of_gt (by positivity : (0:ℝ) < 1 + u ^ 2))
  have hftc := intervalIntegral.integral_deriv_eq_sub'
    (fun u => Real.arctan u
      - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9 - u ^ 11 / 11)) hf' hdiff
    hcont.continuousOn
  have hint : ∫ y in (0:ℝ)..t, y ^ 12 / (1 + y ^ 2)
      = Real.arctan t - (t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 - t ^ 11 / 11) := by
    have hzero : (fun u => Real.arctan u
        - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9 - u ^ 11 / 11)) (0:ℝ) = 0 := by
      simp [Real.arctan_zero]
    simpa [hzero] using hftc
  have hnonneg : (0:ℝ) ≤ ∫ y in (0:ℝ)..t, y ^ 12 / (1 + y ^ 2) :=
    intervalIntegral.integral_nonneg ht
      (fun y (hy : y ∈ Icc (0:ℝ) t) => div_nonneg (pow_nonneg hy.1 12) (by positivity))
  linarith

/-- `arctan (sqrt 3.86) < 1.1`（HOL `Flyspeck_constants.calc` 的零证书复证；V12 私有）。
补角恒等式 + `arctan z ≥ S₆(z)` 在 `z = (√3.86)⁻¹`（`z² = 50/193` 精确、
`z ≥ 508986/1000000`）处取值；数值夹逼只用 `Real.pi_lt_d6`。 -/
private theorem vas12_atan_sqrt_386_lt : Real.arctan (Real.sqrt 3.86) < 1.1 := by
  have hsq386 : Real.sqrt 3.86 * Real.sqrt 3.86 = 3.86 := Real.mul_self_sqrt (by norm_num)
  have hcomp : Real.arctan (Real.sqrt 3.86)
      = Real.pi / 2 - Real.arctan ((Real.sqrt 3.86)⁻¹) := by
    have h := Real.arctan_inv_of_pos (x := Real.sqrt 3.86) (by positivity)
    linarith
  rw [hcomp]
  set z : ℝ := (Real.sqrt 3.86)⁻¹ with hzdef
  have hz2 : z * z = 50 / 193 := by
    rw [hzdef]
    calc (Real.sqrt 3.86)⁻¹ * (Real.sqrt 3.86)⁻¹
        = (Real.sqrt 3.86 * Real.sqrt 3.86)⁻¹ := by field_simp
      _ = 50 / 193 := by rw [hsq386]; norm_num
  have hz0 : 0 ≤ z := by positivity
  have hfact : z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 + z ^ 9 / 9 - z ^ 11 / 11
      = z * (1 - (z * z) / 3 + (z * z) ^ 2 / 5 - (z * z) ^ 3 / 7
          + (z * z) ^ 4 / 9 - (z * z) ^ 5 / 11) := by ring
  have hlow := vas12_arctan_ge_taylor6 z hz0
  rw [hfact, hz2] at hlow
  have hF : (0:ℝ) < 1 - (50:ℝ) / 193 / 3 + ((50:ℝ) / 193) ^ 2 / 5
      - ((50:ℝ) / 193) ^ 3 / 7 + ((50:ℝ) / 193) ^ 4 / 9
      - ((50:ℝ) / 193) ^ 5 / 11 := by norm_num
  have hzge : (508986 / 1000000 : ℝ) ≤ z := by
    have hp : Real.sqrt 3.86 ≤ 1000000 / 508986 := by
      calc Real.sqrt 3.86 ≤ Real.sqrt ((1000000 / 508986 : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by norm_num)
        _ = 1000000 / 508986 := Real.sqrt_sq (by norm_num)
    calc (508986 / 1000000 : ℝ) = (1000000 / 508986)⁻¹ := by norm_num
      _ ≤ (Real.sqrt 3.86)⁻¹ := (inv_le_inv₀ (by norm_num) (by positivity)).2 hp
  have hL0 : (508986 / 1000000 : ℝ) * (1 - (50:ℝ) / 193 / 3 + ((50:ℝ) / 193) ^ 2 / 5
      - ((50:ℝ) / 193) ^ 3 / 7 + ((50:ℝ) / 193) ^ 4 / 9
      - ((50:ℝ) / 193) ^ 5 / 11) ≤ Real.arctan z := by
    calc (508986 / 1000000 : ℝ) * (1 - (50:ℝ) / 193 / 3 + ((50:ℝ) / 193) ^ 2 / 5
          - ((50:ℝ) / 193) ^ 3 / 7 + ((50:ℝ) / 193) ^ 4 / 9
          - ((50:ℝ) / 193) ^ 5 / 11)
        ≤ z * (1 - (50:ℝ) / 193 / 3 + ((50:ℝ) / 193) ^ 2 / 5
          - ((50:ℝ) / 193) ^ 3 / 7 + ((50:ℝ) / 193) ^ 4 / 9
          - ((50:ℝ) / 193) ^ 5 / 11) := mul_le_mul_of_nonneg_right hzge hF.le
      _ ≤ Real.arctan z := hlow
  have hC1 : (0.4707965 : ℝ) < (508986 / 1000000 : ℝ) * (1 - (50:ℝ) / 193 / 3
      + ((50:ℝ) / 193) ^ 2 / 5 - ((50:ℝ) / 193) ^ 3 / 7
      + ((50:ℝ) / 193) ^ 4 / 9 - ((50:ℝ) / 193) ^ 5 / 11) := by norm_num
  have hC2 : Real.pi / 2 - 1.1 < (0.4707965 : ℝ) := by
    have hpi := Real.pi_lt_d6
    linarith
  linarith

/-- HOL `LINDIH_11` (JOTSWIX.hl:3291): the registry box
`[(2,y1,2);(2,y2,2.52);(2,y3,2.52);(2,y4,2);(3.01,y5,3.55);(2*h0,y6,3.01)]`
forces small dihedral or negative delta.
PROVED 2026-11-14 (lane `vaslin-w12`): `deltaY < 0` closes the goal outright;
otherwise the terminal estimates `9368433105` (`0 < delta4Y`) and
`8405387449` (`4·x1Δy < 3.86·Δ₄y²`) feed `lindihpi_lt_y_small_p11`
(HOL `lindih_lt`-y at `u = atn (√3.86)`, i.e. HOL's
`Merge_ineq.lindih_lt` route with `tan2lower = 3.86`), and the numeric tail
`atn (√3.86) < 1.1` is the zero-certificate complement plus S₆ Taylor
bracket (HOL `Flyspeck_constants.calc`). -/
theorem LINDIH_11_p23 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : y1 = 2) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2.52) (hy3 : 2 ≤ y3 ∧ y3 ≤ 2.52)
    (hy4 : y4 = 2) (hy5 : 3.01 ≤ y5 ∧ y5 ≤ 3.55)
    (hy6 : 2 * h0 ≤ y6 ∧ y6 ≤ 3.01) :
    dihY y1 y2 y3 y4 y5 y6 < 1.1 ∨ deltaY y1 y2 y3 y4 y5 y6 < 0 := by
  by_cases hneg : deltaY y1 y2 y3 y4 y5 y6 < 0
  · exact Or.inr hneg
  · left
    have hdy : 0 ≤ deltaY y1 y2 y3 y4 y5 y6 := le_of_not_gt hneg
    have h936 : mainEstimate_9368433105 :=
      h "9368433105" (by simp [mainNonlinearTerminalV11Ids_t11])
    have h840 : mainEstimate_8405387449 :=
      h "8405387449" (by simp [mainNonlinearTerminalV11Ids_t11])
    have h4pos : 0 < delta4Y y1 y2 y3 y4 y5 y6 :=
      h936 y1 y2 y3 y4 y5 y6 (le_of_eq hy1.symm) (le_of_eq hy1) hy2.1 hy2.2
        hy3.1 hy3.2 (le_of_eq hy4.symm) (le_of_eq hy4) hy5.1 hy5.2 hy6.1 hy6.2
    have h840' : (4 * x1DeltaY_t11 y1 y2 y3 y4 y5 y6
          < 3.86 * delta4SquaredY_t11 y1 y2 y3 y4 y5 y6)
        ∨ deltaY y1 y2 y3 y4 y5 y6 < 0 :=
      h840 y1 y2 y3 y4 y5 y6 (le_of_eq hy1.symm) (le_of_eq hy1) hy2.1 hy2.2
        hy3.1 hy3.2 (le_of_eq hy4.symm) (le_of_eq hy4) hy5.1 hy5.2 hy6.1 hy6.2
    rcases h840' with hlt | hdneg
    · have hiff := lindihpi_lt_y_small_p11 (b := (3.86 : ℝ)) (y1 := y1) (y2 := y2)
        (y3 := y3) (y4 := y4) (y5 := y5) (y6 := y6)
        (by rw [hy1]; norm_num) (by norm_num) hdy h4pos
      have hsmall : 4 * x1DeltaY_p11 y1 y2 y3 y4 y5 y6
          < 3.86 * delta4SquaredY_p11 y1 y2 y3 y4 y5 y6 := by
        simpa only [x1DeltaY_p11, x1DeltaY_t11, delta4SquaredY_p11,
          delta4SquaredY_t11] using hlt
      exact lt_trans (hiff.mp hsmall) vas12_atan_sqrt_386_lt
    · exact absurd hdneg hneg

/-- HOL `LEMMA_PWE3` (JOTSWIX.hl:3370). NEEDS: same kit as
`LEMMA_PWE1_p23`. -/
theorem LEMMA_PWE3_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ)
    (hs : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hab : ∀ i, s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0 ∨
      s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)
    (hg : scsGeneric v)
    (hns1 : ¬ scsIsStr s v (p + 1)) (hns3 : ¬ scsIsStr s v (p + 3))
    (hs1 : scsIsStr s v p) (hn : norm (v p) = 2)
    (ha01 : s.a p (p + 1) = 2) (ha30 : s.a (p + 3) p = 2 * h0)
    (hd1 : dist (v (p + 2)) (v (p + 3)) = 2)
    (hd2 : 2 * h0 ≤ dist (v (p + 1)) (v (p + 2))) :
    Real.pi / 2 < dihV 0 (v (p + 1)) (v p) (v (p + 2)) := by
  sorry

/-- HOL `LEMMA_PWE4` (JOTSWIX.hl:3648). NEEDS: same kit as
`LEMMA_PWE1_p23`. -/
theorem LEMMA_PWE4_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ)
    (hs : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hab : ∀ i, s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0 ∨
      s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)
    (hg : scsGeneric v)
    (hns1 : ¬ scsIsStr s v (p + 1)) (hns3 : ¬ scsIsStr s v (p + 3))
    (hs1 : scsIsStr s v p) (hn : norm (v p) = 2)
    (ha30 : s.a (p + 3) p = 2) (ha01 : s.a p (p + 1) = 2 * h0)
    (hd1 : dist (v (p + 2)) (v (p + 1)) = 2)
    (hd2 : 2 * h0 ≤ dist (v (p + 3)) (v (p + 2))) :
    Real.pi / 2 < dihV 0 (v (p + 3)) (v p) (v (p + 2)) := by
  sorry

end Kepler.Text
