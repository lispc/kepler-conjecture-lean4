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
  sorry

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
