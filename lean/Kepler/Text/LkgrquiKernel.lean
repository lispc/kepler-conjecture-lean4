/-
LkgrquiKernel: the upstream kernel for the LA20 slice arrows `AQICLXA_SLICE`
(hexagons.hl:1307) and `FUNOUYH_SLICE` (hexagons.hl:1474).

The engine-sunk bodies in `Kepler.Text.LocalConcl`
(`l20es_SLICE_6I1_02/03`) are `LKGRQUI_p27` instances, but LA20 cannot
import LA27 (LA27 -> LA24 -> LA20).  `LKGRQUI` really only needs the LA35
engine (`SCS_HALF_SLICE_IS_A_SCS_p35`, `SCS_SLICE_SYM_p35`, `QKNVMLB1_p35`,
`QKNVMLB3_p35`) + the SGTRNAF minimiser kernel + three small bookkeeping
lemmas; LA35 imports only LA1/LA3/LA4/LA23/PackingAuto2 (no LA12/LA20), so
this module sits strictly above LA20.

Contents: verbatim copies of LocalAuto27 Section H under `_krnl` names
(the only change is `SGTRNAF_p27` -> `SGTRNAF_krnl` and the name suffix).
-/
import Kepler.Text.SgtrnafKernel
import Kepler.Text.LocalAuto35
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-- HOL `SLICE_IS_UNADORNED` (LKGRQUI.hl:82), kernel copy. -/
theorem SLICE_IS_UNADORNED_krnl :
    ∀ s p q d' mkj, unadornedV39 (scsHalfSliceV39 s p q d' mkj) := by
  intro s p q d' mkj
  simp [unadornedV39, scsHalfSliceV39]

/-- `MMs` membership factors into the `BBs` + negative-taustar pair consumed
by SGTRNAF (BBprimeV39 components 1 and 3), kernel copy. -/
theorem mm_BBs_taustar_krnl (s : ScsV39) (vv : ℕ → V3) (h : vv ∈ MMsV39 s) :
    BBsV39 s vv ∧ taustarV39 s vv < 0 := by
  simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at h
  exact ⟨h.1.1.1, h.1.1.2.2⟩

/-- `scsDiag` is symmetric under swapping the two indices, kernel copy. -/
theorem scsDiag_symm_krnl {k i j : ℕ} (h : scsDiag k i j) : scsDiag k j i :=
  ⟨fun hc => h.1 hc.symm, fun hc => h.2.2 hc.symm, fun hc => h.2.1 hc.symm⟩

theorem LKGRQUI_krnl : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop),
    isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    scsArrowV39 {s} {s', s''} := by
  intro s s' s'' p q d' d'' mkj hscs hdiag hsl
  have hscs0 := hscs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsymrec, -, -, -, -, -, -, -, -⟩ := hscs0
  have hsl0 := hsl
  simp only [isScsSliceV39, scsSliceV39, Prod.mk.injEq] at hsl
  obtain ⟨⟨hs', hs''⟩, hd'lt, hd''lt, hdle, hbm4, hdisj, hmkj⟩ := hsl
  -- both halves conform: E1 on the slice and on its SCS_SLICE_SYM flip
  have hscs' : isScsV39 s' :=
    SCS_HALF_SLICE_IS_A_SCS_p35 s s' s'' p q hscs hdiag hsl0
  have hsym : isScsSliceV39 s s'' s' q p :=
    (SCS_SLICE_SYM_p35 s s' s'' p q hscs hdiag).mp hsl0
  have hscs'' : isScsV39 s'' :=
    SCS_HALF_SLICE_IS_A_SCS_p35 s s'' s' q p hscs (scsDiag_symm_krnl hdiag) hsym
  -- both halves adorned-free
  have hun' : unadornedV39 s' := by
    rw [hs']; exact SLICE_IS_UNADORNED_krnl s p q s'.d (s'.J 0 (s'.k - 1))
  have hun'' : unadornedV39 s'' := by
    rw [hs'']; exact SLICE_IS_UNADORNED_krnl s q p s''.d (s'.J 0 (s'.k - 1))
  refine ⟨fun t ht => ?_, ?_⟩
  · rcases Set.mem_insert_iff.mp ht with he | ht2
    · rw [he]; exact hscs'
    · rw [Set.mem_singleton_iff.mp ht2]; exact hscs''
  · rcases eq_empty_or_nonempty (MMsV39 s) with h0 | h0
    · left
      intro t ht
      rw [Set.mem_singleton_iff.mp ht]
      exact h0
    · right
      obtain ⟨vv, hvv⟩ := h0
      obtain ⟨hBB, hta⟩ := mm_BBs_taustar_krnl s vv hvv
      -- BBs transport into both halves (E2 twice) + taustar superadditivity (E3)
      have hBB1 : BBsV39 s' (fun i => vv (i % s'.k + p % s.k)) :=
        QKNVMLB1_p35 s p q s'.d (s'.J 0 (s'.k - 1)) vv hvv hbm4 hdisj hscs hd'lt
          hdiag s' hs' _ rfl
      have hbm4' : s.bm q p < 4 := by
        rw [← (hsymrec p q).2.2.1]
        exact hbm4
      have hdisj' : s.k = 4 ∨ s.bm q p ≤ cstab := by
        rw [← (hsymrec p q).2.2.1]
        exact hdisj
      have hBB2 : BBsV39 s'' (fun i => vv (i % s''.k + q % s.k)) :=
        QKNVMLB1_p35 s q p s''.d (s'.J 0 (s'.k - 1)) vv hvv hbm4' hdisj' hscs
          hd''lt (scsDiag_symm_krnl hdiag) s'' hs'' _ rfl
      have hsum := QKNVMLB3_p35 s s' s'' p q s'.d s''.d (s'.J 0 (s'.k - 1)) vv
        (fun i => vv (i % s'.k + p % s.k)) (fun i => vv (i % s''.k + q % s.k))
        hs'.symm hs''.symm rfl rfl hvv hscs hdiag hsl0 hdle
      have hneg : taustarV39 s' (fun i => vv (i % s'.k + p % s.k)) < 0 ∨
          taustarV39 s'' (fun i => vv (i % s''.k + q % s.k)) < 0 := by
        by_contra hcon
        rw [not_or] at hcon
        linarith
      rcases hneg with h1 | h2
      · refine ⟨s', Set.mem_insert s' {s''}, ?_⟩
        exact SGTRNAF_krnl s' _ hscs' hun' hBB1 h1
      · refine ⟨s'', Set.mem_insert_of_mem _ (Set.mem_singleton _), ?_⟩
        exact SGTRNAF_krnl s'' _ hscs'' hun'' hBB2 h2
