/-
VasTuaKit — VASYYAU wave 1 (lane vas-w1): the TUAPYYU chain, provable links.

HOL source: `scripts/local/VASYYAU.hl`
  * `WGDHPPI` (:100-110): at most one `scs_is_str` stratum index at k = 4.
  * `SCS_STR_CASES_4` (:427-497): `¬str p ∧ ¬str (p+1) → ¬str (p+3) ∨ ¬str (p+2)`.
  * `TUAPYYU1` (:536-639): `NEHXMWH1_concl → NEHXMWH_concl → TUAPYYU_concl`.

The LA1 registry twins (`WGDHPPI_concl`, `TUAPYYU_concl`) cannot be proved in
place (LocalAuto1 is upstream of every local-fan kit); this file carries the
downstream, proof-clean versions of the three provable links, so the next wave
can wire them into `LocalAuto25.WGDHPPI_p25` / `SCS_STR_CASES_4_p25` /
`TUAPYYU1_p25` (or a `_discharged` exit). `TUAPYYU1` keeps the two JOTSWIX
endpoint lemmas as hypotheses, so it closes independently of them.

All dependencies are standard-three at HEAD (probes in Evidence.md):
`GSXRFWM_p33`, `AURSIPD_p18`, `MMS_IMP_BBS_p28`, `BBS_IMP_CONVEX_LOCAL_FAN_p34`,
`BB_RHO_NODE_IVS_p26`, `IN_V_IMP_AZIM_LESS_PI`, `w15_clf2`,
`periodic_mod_eq_p23`, `STR_MOD_EQ_p25`, `NOT_MOD_4_CASES_p25`.
-/
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto14
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto25
import Kepler.Text.LocalAuto26
import Kepler.Text.LocalAuto33
import Kepler.Text.LocalAuto34

set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-- HOL `WGDHPPI` (VASYYAU.hl:100). Clean route: `GSXRFWM` (MMs ⇒ generic)
plus `AURSIPD` (`3 + #strata ≤ k`) at `k = 4`. -/
theorem WGDHPPI_vaskit (s : ScsV39) (v : ℕ → V3) (his : isScsV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s) :
    {i : ℕ | i < s.k ∧ scsIsStr s v i}.ncard ≤ 1 := by
  have h3 : 3 < s.k := by omega
  have hgen : scsGeneric v := GSXRFWM_p33 s v his hk hv
  have h := AURSIPD_p18 s v h3 his hgen hv
  omega

/-- HOL `SCS_STR_CASES_4` (VASYYAU.hl:427): the two-stratum exclusion at
`k = 4`, with the proved `WGDHPPI_vaskit` in place of the circular
`WGDHPPI_p25`. -/
theorem SCS_STR_CASES_4_vaskit (s : ScsV39) (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hk : s.k = 4) (hv : v ∈ MMsV39 s) (h1 : ¬scsIsStr s v p)
    (h2 : ¬scsIsStr s v (p + 1)) :
    ¬scsIsStr s v (p + 3) ∨ ¬scsIsStr s v (p + 2) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hc3, hc2⟩ := hcon
  have hW := WGDHPPI_vaskit s v his hk hv
  have hS : ({i | i < s.k ∧ scsIsStr s v i} : Set ℕ).Finite :=
    (Set.finite_Iio s.k).subset fun x hx => Set.mem_Iio.mpr hx.1
  have hme : ∀ q : ℕ, scsIsStr s v q → q % 4 ∈ {i | i < s.k ∧ scsIsStr s v i} := by
    intro q hq
    refine ⟨by omega, ?_⟩
    exact (STR_MOD_EQ_p25 s v 4 his hk hv q).mpr hq
  have m3 := hme (p + 3) hc3
  have m2 := hme (p + 2) hc2
  have hpair : ({(p + 3) % 4, (p + 2) % 4} : Set ℕ) ⊆ {i | i < s.k ∧ scsIsStr s v i} := by
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact m3
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact m2
  have hle := Set.ncard_le_ncard hpair hS
  rw [Set.ncard_pair (by omega : (p + 3) % 4 ≠ (p + 2) % 4)] at hle
  omega

/-- HOL `TUAPYYU1` (VASYYAU.hl:536): the pure interior-angle implication
`NEHXMWH1_concl → NEHXMWH_concl → TUAPYYU_concl`. This is the *provable*
core of `TUAPYYU`; the two endpoint lemmas stay as hypotheses (they are the
JOTSWIX giants). -/
theorem TUAPYYU1_vaskit : NEHXMWH1_concl_p25 → NEHXMWH_concl_p25 → TUAPYYU_concl_p25 := by
  intro hN1 hN2 h s v p his hb hk hv hdiag hval hstr1 hstr2
  let FF : Set (V3 × V3) := Set.range fun i => (v i, v (i + 1))
  have hFF : Set.range (fun i => (v i, v (i + 1))) = FF := rfl
  have hgen : scsGeneric v := GSXRFWM_p33 s v his hk hv
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hv
  have hper : Periodic v 4 := by
    have h := hBB.2.1
    rw [hk] at h
    exact h
  have hcl : ConvexLocalFan (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF :=
    BBS_IMP_CONVEX_LOCAL_FAN_p34 s 4 v (by omega) hk hBB
  have hcl2 : convexLocalFan_p2 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF := w15_clf2 hcl
  -- the rho/ivs values on the successor-dart fan
  have hbij : ∀ j, rhoNode1 FF (v j) = v (j + 1) ∧ ivsRhoNode1 FF (v j) = v (j + 3) := by
    intro j
    obtain ⟨h1, h2⟩ := BB_RHO_NODE_IVS_p26 s 4 v (v j) (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF j hk rfl rfl rfl hFF his
      (by omega) hBB
    exact ⟨h1, by rw [h2, show j + 4 - 1 = j + 3 by omega]⟩
  -- the azim bound (convex local fan)
  have hle : ∀ j, azim 0 (v j) (v (j + 1)) (v (j + 3)) ≤ Real.pi := by
    intro j
    have h0 := IN_V_IMP_AZIM_LESS_PI (V := Set.range v)
      (E := Set.range fun i => ({v i, v (i + 1)} : Set V3)) (FF := FF)
      hcl2 (v j) ⟨j, rfl⟩ (v (j + 3)) ⟨j + 3, rfl⟩
    rw [show rhoNode1_p2 FF (v j) = v (j + 1) by
      rw [show rhoNode1_p2 FF (v j) = rhoNode1 FF (v j) from rfl, (hbij j).1]] at h0
    exact h0
  -- `¬scsIsStr` gives the strict inequality at the same index
  have hstr_ne : ∀ j, ¬scsIsStr s v j →
      azim 0 (v j) (v (j + 1)) (v (j + 3)) ≠ Real.pi := by
    intro j hj he
    apply hj
    unfold scsIsStr
    rw [hk]
    simpa [show j + (4 - 1) = j + 3 by omega] using he
  have hang : ∀ j, ¬scsIsStr s v j → interiorAngle1 0 FF (v j) < Real.pi := by
    intro j hj
    have h1 := hle j
    have h2 := hstr_ne j hj
    rw [interiorAngle1, (hbij j).1, (hbij j).2]
    exact lt_of_le_of_ne h1 h2
  -- mod-4 transport of the interior angle
  have hmod : ∀ i j, i % 4 = j % 4 →
      interiorAngle1 0 FF (v i) = interiorAngle1 0 FF (v j) := by
    intro i j hij
    have hvi : v i = v j := by
      rw [← periodic_mod_eq_p23 hper i, ← periodic_mod_eq_p23 hper j, hij]
    rw [hvi]
  rcases SCS_STR_CASES_4_vaskit s v p his hk hv hstr1 hstr2 with h3 | h2
  · -- `¬str (p+3)`: apply NEHXMWH (the `p+2`-exclusion variant)
    have hang2 : ∀ i, i % 4 ≠ (p + 2) % 4 → interiorAngle1 0 FF (v i) < Real.pi := by
      intro i hi
      rcases (NOT_MOD_4_CASES_p25 i p).mp hi with h | h | h
      · rw [hmod i p h]; exact hang p hstr1
      · rw [hmod i (p + 1) h]; exact hang (p + 1) hstr2
      · rw [hmod i (p + 3) h]; exact hang (p + 3) h3
    exact hN2 h s FF v p hFF his hk hv hb hgen hdiag hang2
  · -- `¬str (p+2)`: apply NEHXMWH1 (the `p+3`-exclusion variant)
    have hang3 : ∀ i, i % 4 ≠ (p + 3) % 4 → interiorAngle1 0 FF (v i) < Real.pi := by
      intro i hi
      rcases (NOT_MOD_4_CASES_3_p25 i p).mp hi with h | h | h
      · rw [hmod i p h]; exact hang p hstr1
      · rw [hmod i (p + 1) h]; exact hang (p + 1) hstr2
      · rw [hmod i (p + 2) h]; exact hang (p + 2) h2
    exact hN1 h s FF v p hFF his hk hv hb hgen hdiag hang3

end Kepler.Text
