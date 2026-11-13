/-
VasMasterKit — VASYYAU wave 15 (lane vaswkz-w15): the downstream master kit.

HOL source: `scripts/local/VASYYAU.hl`
  * `WKZZEEH` (:720-911): the quad master.  Under
    `main_nonlinear_terminal_v11`, a `k = 4` scs realisation `MMs_v39 s v`
    whose perimeter edges take the two documented value pairs, with the
    `p`, `p+1`, `p+3` indices all non-straight (`~scs_is_str`), cannot have
    BOTH `dist(v p, v(p+3)) = cstab` and `dist(v p, v(p+1)) = cstab`.
    The proof consumes `JOTSWIX` (the quad master of `LocalAuto23Vas`) with
    the `xrr <= #15.53` diagonal hypothesis supplied by `ASSWPOW` at `p+1`,
    whose two `b`-edge premises come from
    `B_LE_2h0_2_SCS_M_4` via `{p MOD 4, (p+3) MOD 4} SUBSET scs_M s` (the
    residues land in `scs_M` because the two pinned `cstab` distances force
    the corresponding `b`-edges above `2*h0`); the interior-angle premise of
    `JOTSWIX` is the `~scs_is_str` strictness at the three residues.

This file is the DAG sink for the VASYYAU master family.  The LocalAuto1
registry twin `WKZZEEH_concl` cannot be proved in place (LocalAuto1 is
upstream of every local-fan kit); the downstream, proof-clean version
`WKZZEEH_kit` carries the statement verbatim and is consumed through the
LocalConcl `WKZZEEH` discharge.  Later VASYYAU waves add their tenants to
this same file: `TUAPYYU_kit`, `PWEIWBZ_kit`, `VASYYAU_kit`.

Statement provenance: `WKZZEEH_kit` is byte-identical to
`LocalAuto1.WKZZEEH_concl` (LocalAuto1.lean:5278) modulo the theorem name;
see the differential in `Evidence.md`.

All dependencies are standard-three at HEAD 8a9e801a (probes in
Evidence.md): `GSXRFWM_p33`, `MMS_IMP_BBS_p28`, `BBS_IMP_CONVEX_LOCAL_FAN_p34`,
`w15_clf2`, `BB_RHO_NODE_IVS_p26`, `IN_V_IMP_AZIM_LESS_PI`,
`JOTSWIX_p23`, `ASSWPOW_p25`, `B_LE_2h0_2_SCS_M_4_pair_p25`,
`xrr_sym_p22`, `periodic_mod_eq_p23`, `periodic2_suc_mod_eq_p25`,
`NOT_MOD_4_CASES_p25`.
-/
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto9
import Kepler.Text.LocalAuto14
import Kepler.Text.LocalAuto22
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto23Vas
import Kepler.Text.LocalAuto25
import Kepler.Text.LocalAuto26
import Kepler.Text.LocalAuto28
import Kepler.Text.LocalAuto33
import Kepler.Text.LocalAuto34
import Mathlib

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-- HOL `WKZZEEH` (VASYYAU.hl:720-911) — downstream kit version of the
LocalAuto1 registry twin `WKZZEEH_concl` (statement verbatim, same
`h : main_nonlinear_terminal_v11` premise and quantifier order). -/
theorem WKZZEEH_kit (h : main_nonlinear_terminal_v11) :
    ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    ¬scsIsStr s v p → ¬scsIsStr s v (p + 1) → ¬scsIsStr s v (p + 3) →
    ¬(dist (v p) (v (p + 3)) = cstab ∧ dist (v p) (v (p + 1)) = cstab) := by
  intro s v p his hbasic hk hv hdiag hval h1 h2 h3
  -- ═══ A. substrate: `BBs`, periodicity, the convex local fan, rho/ivs ═══
  let FF : Set (V3 × V3) := Set.range fun i => (v i, v (i + 1))
  have hFFr : Set.range (fun i => (v i, v (i + 1))) = FF := rfl
  have hFF : (fun i : ℕ => (v i, v (i + 1))) '' Set.univ = FF := by
    simpa only [Set.image_univ] using hFFr
  have hgen : scsGeneric v := GSXRFWM_p33 s v his hk hv
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hv
  have hper : Periodic v 4 := by
    have hb := hBB.2.1
    rw [hk] at hb
    exact hb
  have hcl : ConvexLocalFan (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF :=
    BBS_IMP_CONVEX_LOCAL_FAN_p34 s 4 v (by omega) hk hBB
  have hcl2 : convexLocalFan_p2 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF := w15_clf2 hcl
  have hbij : ∀ j, rhoNode1 FF (v j) = v (j + 1) ∧ ivsRhoNode1 FF (v j) = v (j + 3) := by
    intro j
    obtain ⟨h4, h5⟩ := BB_RHO_NODE_IVS_p26 s 4 v (v j) (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF j hk rfl rfl rfl hFFr his
      (by omega) hBB
    exact ⟨h4, by rw [h5, show j + 4 - 1 = j + 3 by omega]⟩
  -- ═══ B. the interior-angle premise of `JOTSWIX` ═══
  have hle : ∀ j, azim 0 (v j) (v (j + 1)) (v (j + 3)) ≤ Real.pi := by
    intro j
    have h0 := IN_V_IMP_AZIM_LESS_PI (V := Set.range v)
      (E := Set.range fun i => ({v i, v (i + 1)} : Set V3)) (FF := FF)
      hcl2 (v j) ⟨j, rfl⟩ (v (j + 3)) ⟨j + 3, rfl⟩
    rw [show rhoNode1_p2 FF (v j) = v (j + 1) by
      rw [show rhoNode1_p2 FF (v j) = rhoNode1 FF (v j) from rfl, (hbij j).1]] at h0
    exact h0
  have hstr_ne : ∀ j, ¬scsIsStr s v j →
      azim 0 (v j) (v (j + 1)) (v (j + 3)) ≠ Real.pi := by
    intro j hj he
    apply hj
    unfold scsIsStr
    rw [hk]
    simpa [show j + (4 - 1) = j + 3 by omega] using he
  have hangAt : ∀ j, ¬scsIsStr s v j → interiorAngle1 0 FF (v j) < Real.pi := by
    intro j hj
    have hlt := hle j
    have hne := hstr_ne j hj
    rw [interiorAngle1, (hbij j).1, (hbij j).2]
    exact lt_of_le_of_ne hlt hne
  -- mod-4 transport of the interior angle
  have hmod : ∀ i j, i % 4 = j % 4 →
      interiorAngle1 0 FF (v i) = interiorAngle1 0 FF (v j) := by
    intro i j hij
    have hvi : v i = v j := by
      rw [← periodic_mod_eq_p23 hper i, ← periodic_mod_eq_p23 hper j, hij]
    rw [hvi]
  have hang : ∀ i, i % 4 ≠ (p + 2) % 4 → interiorAngle1 0 FF (v i) < Real.pi := by
    intro i hi
    rcases (NOT_MOD_4_CASES_p25 i p).mp hi with h' | h' | h'
    · rw [hmod i p h']; exact hangAt p h1
    · rw [hmod i (p + 1) h']; exact hangAt (p + 1) h2
    · rw [hmod i (p + 3) h']; exact hangAt (p + 3) h3
  -- ═══ C. `s.a p (p+1) < cstab` from the value table ═══
  have hsa : s.a p (p + 1) < cstab := by
    rcases hval p with ⟨ha, -⟩ | ⟨ha, -⟩
    · rw [ha]; norm_num [cstab]
    · rw [ha]; norm_num [h0, cstab]
  -- ═══ D. assume both quad edges are pinned at `cstab` ═══
  intro hcon
  obtain ⟨hcon3, hcon1⟩ := hcon
  have h2h0c : 2 * h0 < cstab := by norm_num [h0, cstab]
  have hpb : Periodic2 s.b s.k := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hpb, -, -, -, -, -, -, -, -, -, -⟩ := his
    exact hpb
  have hbP : Periodic2 s.b 4 := hk ▸ hpb
  -- both residues land in `scsM`: the pinned distances exceed `2*h0`
  have hmem1 : p % 4 ∈ scsM s := by
    have hbge : cstab ≤ s.b (p % 4) ((p % 4) + 1) := by
      rw [periodic2_suc_mod_eq_p25 hbP p]
      calc (cstab : ℝ) = dist (v p) (v (p + 1)) := hcon1.symm
        _ ≤ s.b p (p + 1) := (hBB.2.2.1 p (p + 1)).2
    refine ⟨?_, Or.inl (lt_of_lt_of_le h2h0c hbge)⟩
    rw [hk]
    exact Nat.mod_lt _ (by norm_num)
  have hp4 : v (p + 4) = v p := by
    rw [← periodic_mod_eq_p23 hper (p + 4), ← periodic_mod_eq_p23 hper p]
    congr 1
    omega
  have hmem3 : (p + 3) % 4 ∈ scsM s := by
    have hbge : cstab ≤ s.b ((p + 3) % 4) (((p + 3) % 4) + 1) := by
      rw [periodic2_suc_mod_eq_p25 hbP (p + 3)]
      have hb := (hBB.2.2.1 (p + 3) (p + 4)).2
      rw [hp4] at hb
      calc (cstab : ℝ) = dist (v p) (v (p + 3)) := hcon3.symm
        _ = dist (v (p + 3)) (v p) := by rw [dist_comm]
        _ ≤ s.b (p + 3) (p + 4) := hb
    refine ⟨?_, Or.inl (lt_of_lt_of_le h2h0c hbge)⟩
    rw [hk]
    exact Nat.mod_lt _ (by norm_num)
  have hsub : {(p % 4), ((p + 3) % 4)} ⊆ scsM s := by
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hmem1
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hmem3
  -- ═══ E. the `xrr` hypothesis: `ASSWPOW` at `p+1` ═══
  have hb12 := B_LE_2h0_2_SCS_M_4_pair_p25 s his hk hsub
  have hxrr1 := ASSWPOW_p25 s v (p + 1) his hv hk hbasic hb12.1 hb12.2
  have hxrr : xrr (norm (v (p + 3))) (norm (v (p + 1)))
      (dist (v (p + 3)) (v (p + 1))) ≤ 15.53 := by
    rw [xrr_sym_p22, dist_comm]
    exact hxrr1
  -- ═══ F. `JOTSWIX` gives a strict edge, contradicting the pins ═══
  rcases JOTSWIX_p23 h s FF v p hFF his hk hv hbasic hgen hsa hdiag hang hxrr with
    hlt | hlt
  · linarith
  · linarith

end Kepler.Text
