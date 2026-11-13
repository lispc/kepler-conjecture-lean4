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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- HOL `LINDIH_11` (JOTSWIX.hl:3291): the registry box
`[(2,y1,2);(2,y2,2.52);(2,y3,2.52);(2,y4,2);(3.01,y5,3.55);(2*h0,y6,3.01)]`
forces small dihedral or negative delta. NEEDS: the terminal Ineq
registry entry for the box (opaque). -/
theorem LINDIH_11_p23 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : y1 = 2) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2.52) (hy3 : 2 ≤ y3 ∧ y3 ≤ 2.52)
    (hy4 : y4 = 2) (hy5 : 3.01 ≤ y5 ∧ y5 ≤ 3.55)
    (hy6 : 2 * h0 ≤ y6 ∧ y6 ≤ 3.01) :
    dihY y1 y2 y3 y4 y5 y6 < 1.1 ∨ deltaY y1 y2 y3 y4 y5 y6 < 0 := by
  sorry

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
