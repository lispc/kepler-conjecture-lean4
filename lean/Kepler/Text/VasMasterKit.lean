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
import Kepler.Text.LocalAuto16
import Kepler.Text.LocalAuto18
import Kepler.Text.LocalAuto22
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto23Vas
import Kepler.Text.LocalAuto25
import Kepler.Text.LocalAuto26
import Kepler.Text.LocalAuto28
import Kepler.Text.LocalAuto33
import Kepler.Text.LocalAuto34
import Kepler.Text.VasTuaKit
import Kepler.Text.YebwjngKit
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

/-- HOL `TUAPYYU` (VASYYAU.hl:524-646) — downstream kit version of the
LocalAuto1 registry twin `TUAPYYU_concl` (statement verbatim, same
`h : main_nonlinear_terminal_v11` premise and quantifier order).  Assembly
per HOL :640-646: `TUAPYYU1` (`VasTuaKit.TUAPYYU1_vaskit`, the `(p+3)`
block → `NEHXMWH1`, the `(p+2)` block → `NEHXMWH`) fed with `BZQNDMN_p23`
(the `(p+3)` endpoint lemma) and `NEHXMWH_p23` (the `(p+2)` one). -/
theorem TUAPYYU_kit (h : main_nonlinear_terminal_v11) :
    ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    ¬scsIsStr s v p → ¬scsIsStr s v (p + 1) →
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∨
      dist (v p) (v (p + 1)) = s.b p (p + 1) := by
  have hN1 : NEHXMWH1_concl_p25 := fun h' s FF v p hFF his hk hv hbasic hgen hdiag hang =>
    BZQNDMN_p23 h' s FF v p (by simpa only [Set.image_univ] using hFF)
      his hk hv hbasic hgen hdiag hang
  have hN2 : NEHXMWH_concl_p25 := fun h' s FF v p hFF his hk hv hbasic hgen hdiag hang =>
    NEHXMWH_p23 h' s FF v p (by simpa only [Set.image_univ] using hFF)
      his hk hv hbasic hgen hdiag hang
  intro s v p his hbasic hk hv hdiag hval h1 h2
  exact TUAPYYU1_vaskit hN1 hN2 h s v p his hbasic hk hv hdiag hval h1 h2

/-- At most one straight index at `k = 4`: any two straight indices are
congruent mod `4`.  This is the `NOT_STR_IN_CASES_4` engine re-derived from
`AURSIPD_p18` because its upstream twins `WGDHPPI_concl` /
`WGDHPPI_p25` / `NOT_STR_IN_CASES_4(_1)_p25` still carry `sorryAx` at HEAD
(probe in `Evidence.md`); `AURSIPD_p18` is standard-three. -/
private theorem pweiwbz_str_uniq (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (his : isScsV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s) :
    ∀ i j : ℕ, scsIsStr s v i → scsIsStr s v j → i % 4 = j % 4 := by
  have hgen : scsGeneric v := GSXRFWM_p33 s v his hk hv
  have hcard : {i : ℕ | i < s.k ∧ scsIsStr s v i}.ncard ≤ 1 := by
    have h3 := AURSIPD_p18 s v (by rw [hk]; norm_num) his hgen hv
    rw [hk] at h3 ⊢
    omega
  have hSfin : ({i : ℕ | i < s.k ∧ scsIsStr s v i} : Set ℕ).Finite :=
    FINITE_SET_STR_p25 s.k s v
  intro i j hi hj
  by_contra hne
  have hmi : i % 4 ∈ {i : ℕ | i < s.k ∧ scsIsStr s v i} :=
    ⟨by omega, (STR_MOD_EQ_p25 s v 4 his hk hv i).mpr hi⟩
  have hmj : j % 4 ∈ {i : ℕ | i < s.k ∧ scsIsStr s v i} :=
    ⟨by omega, (STR_MOD_EQ_p25 s v 4 his hk hv j).mpr hj⟩
  have hpair : ({i % 4, j % 4} : Set ℕ) ⊆ {i : ℕ | i < s.k ∧ scsIsStr s v i} := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]; exact hmi
    · rw [Set.mem_singleton_iff.mp hx]; exact hmj
  have hle := Set.ncard_le_ncard hpair hSfin
  rw [Set.ncard_pair (show i % 4 ≠ j % 4 by omega)] at hle
  omega

/-- HOL `PWEIWBZ` (VASYYAU.hl:1126-2348), C-branch leaf
`scs_is_str s v (p+1) ∧ scs_a_v39 s (p+3) p = &2` (VASYYAU.hl:1897-1924):
under the master premises, a straight `p+1` vertex together with the minimal
`(p+3,p)` edge pins `dist(v p, v(p+1))` at `2`.

Assembly (HOL :1902-1923): `YEBWJNG` at `p+3` gives
`dist (v (p+3)) (v (p+4)) = 2` (its `~str` pair `p+3`, `p+4` comes from the
at-most-one-straight bound, derived here directly from `AURSIPD_p18` because
the `WGDHPPI` twin `WGDHPPI_concl` still carries `sorryAx`); `CQAOQLR` at
`p+3` transports the equation across the opposite diagonal to
`dist (v (p+4)) (v (p+5)) = 2`, and periodicity (`v (p+4) = v p`,
`v (p+5) = v (p+1)`) lands on the goal.  Every shifted `a`/`b` premise is a
`Periodic2` image of the `p`-indexed value table. -/
private theorem pweiwbz_C1 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (ha : s.a p (p + 1) = 2)
    (hstr1 : scsIsStr s v (p + 1)) (ha30 : s.a (p + 3) p = 2) :
    dist (v p) (v (p + 1)) = 2 := by
  -- ═══ A. substrate: generic position, BBS bounds, periodicity ═══
  have hgen : scsGeneric v := GSXRFWM_p33 s v his hk hv
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hv
  have hper : Periodic v 4 := by
    have h1 := hBB.2.1
    rw [hk] at h1
    exact h1
  have his' : isScsV39 s := his
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpb, -, -, -, -, -, -, -, -, -, -⟩ := his
  have hpa4 : Periodic2 s.a 4 := hk ▸ hpa
  have hpb4 : Periodic2 s.b 4 := hk ▸ hpb
  -- ═══ B. at most one straight index, straight from `AURSIPD` ═══
  have hns3 : ¬scsIsStr s v (p + 3) := by
    intro hc
    have e := pweiwbz_str_uniq h s v his' hk hv (p + 3) (p + 1) hc hstr1
    omega
  have hns4 : ¬scsIsStr s v (p + 4) := by
    intro hc
    have e := pweiwbz_str_uniq h s v his' hk hv (p + 4) (p + 1) hc hstr1
    omega
  -- ═══ C. the `(p+3,p)` edge value and its mod-shifts ═══
  have ha34 : s.a (p + 3) (p + 4) = 2 := ((hpa4 (p + 3) p).2).trans ha30
  have hb34 : s.b (p + 3) (p + 4) = 2 * h0 := A_EQ2_IMP_B_p25 s (p + 3) hval ha34
  have hb01 : s.b p (p + 1) = 2 * h0 := A_EQ2_IMP_B_p25 s p hval ha
  have ha45 : s.a (p + 4) (p + 5) = 2 :=
    ((hpa4 (p + 4) (p + 1)).2).trans (((hpa4 p (p + 1)).1).trans ha)
  have hb45 : s.b (p + 4) (p + 5) = 2 * h0 :=
    ((hpb4 (p + 4) (p + 1)).2).trans (((hpb4 p (p + 1)).1).trans hb01)
  -- ═══ D. strict `a < b` on the two remaining edges ═══
  have hlt : ∀ i : ℕ, s.a i (i + 1) < s.b i (i + 1) := by
    intro i
    rcases hval i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; norm_num [h0]
    · rw [h1, h2]; norm_num [h0, cstab]
  have ea56 : s.a (p + 5) (p + 6) = s.a (p + 1) (p + 2) :=
    ((hpa4 (p + 1) (p + 6)).1).trans ((hpa4 (p + 1) (p + 2)).2)
  have eb56 : s.b (p + 5) (p + 6) = s.b (p + 1) (p + 2) :=
    ((hpb4 (p + 1) (p + 6)).1).trans ((hpb4 (p + 1) (p + 2)).2)
  have ea63 : s.a (p + 6) (p + 3) = s.a (p + 2) (p + 3) :=
    (hpa4 (p + 2) (p + 3)).1
  have eb63 : s.b (p + 6) (p + 3) = s.b (p + 2) (p + 3) :=
    (hpb4 (p + 2) (p + 3)).1
  -- ═══ E. `YEBWJNG` at `p+3`: the opposite `(p+3,p)` diagonal is `2` ═══
  have hY : dist (v (p + 3)) (v (p + 4)) = 2 :=
    YEBWJNG_kit h s v (p + 3) his' hb hk hv hdiag hval hns3 hns4 ha34
  -- ═══ F. `CQAOQLR` at `p+3` transports it across the opposite edge ═══
  have hsix : (p + 3) + s.k - 1 = p + 6 := by rw [hk]; omega
  have hCQ : dist (v (p + 3)) (v (p + 4)) = 2 ↔
      dist (v (p + 4)) (v (p + 5)) = 2 :=
    CQAOQLR_p16 h s v (p + 3)
      (by rw [hk]; norm_num)
      his' hv hgen hb
      (by rw [hk]; exact hdiag)
      (by rw [hb34]; norm_num [h0])
      (by rw [hb45]; norm_num [h0])
      (by rw [ea56, eb56]; exact hlt (p + 1))
      (by rw [hsix, ea63, eb63]; exact hlt (p + 2))
      ha34 (le_of_eq hb34) ha45 (le_of_eq hb45)
  -- ═══ G. periodicity lands the shifted edge on the goal ═══
  have hstep : dist (v (p + 4)) (v (p + 5)) = 2 := hCQ.mp hY
  have hv4 : v (p + 4) = v p := hper p
  have hv5 : v (p + 5) = v (p + 1) := by
    have h1 := hper (p + 1)
    simpa only [show (p + 1) + 4 = p + 5 by omega] using h1
  simpa only [hv4, hv5] using hstep


/-! ## `PWEIWBZ`, `str p` branch (VASYYAU.hl:1161-1783)

The branch `scs_is_str s v p` and `not (scs_is_str s v (p+1))` splits on the
value table into the `a(p+3)p = 2` leaf (HOL :1308-1391) and the two
`a(p+2)(p+3)` leaves (HOL :1394-1607).  The C-prep (HOL :1173-1306) is packaged
below as `PweiwbzPrep`; `pweiwbz_B_a30eq2` is the first leaf.
-/

/-- Common facts of the `str p` C-prep (HOL `VASYYAU.hl:1173-1306`), shared by
the `a(p+3)p = 2` leaves (HOL :1308-1607).  `pweiwbz_B_a30eq2` consumes
`gen`/`bbs`/`per`/`pa4`/`pb4`/`ia`/`iaLt`/`ns2`/`diag*`/`valLt`/`b01`/`a34`/`b34`/
`bp3p`/`a45`/`b45`/`a14`/`b14`/`a56`/`b56`/`a63`/`b63`/`wk`/`nc1`-`nc4`/`az1`/`az3`;
`rho`/`angLe`/`diagP1P3` are kept for the `a30 ≠ 2` leaves (HOL :1611-1783), which
need the same rho/dihV surface with `a30` reversed. -/
private structure PweiwbzPrep (s : ScsV39) (v : ℕ → V3) (p : ℕ) : Prop where
  gen : scsGeneric v
  bbs : BBsV39 s v
  per : Periodic v 4
  pa4 : Periodic2 s.a 4
  pb4 : Periodic2 s.b 4
  rho : ∀ j : ℕ, rhoNode1 (Set.range fun i => (v i, v (i + 1))) (v j) = v (j + 1) ∧
    ivsRhoNode1 (Set.range fun i => (v i, v (i + 1))) (v j) = v (j + 3)
  ia : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) =
    interiorAngle1 0 (Set.range fun i => (v i, v (i + 1))) (v j)
  angLe : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) ≤ Real.pi
  iaLt : ∀ j : ℕ, ¬scsIsStr s v j →
    interiorAngle1 0 (Set.range fun i => (v i, v (i + 1))) (v j) < Real.pi
  ns2 : ¬scsIsStr s v (p + 2)
  ns5 : ¬scsIsStr s v (p + 5)
  diagLt : ∀ i j : ℕ, scsDiag 4 i j → s.a i j < dist (v i) (v j)
  diag3 : ∀ i j : ℕ, scsDiag 4 i j → 3 ≤ dist (v i) (v j)
  diagB : ∀ i j : ℕ, scsDiag 4 i j → 4 * h0 < s.b i j
  diagP2P : scsDiag 4 (p + 2) p
  diagP1P3 : scsDiag 4 (p + 1) (p + 3)
  valLt : ∀ i : ℕ, s.a i (i + 1) < s.b i (i + 1)
  b01 : s.b p (p + 1) = 2 * h0
  a34 : s.a (p + 3) (p + 4) = 2
  b34 : s.b (p + 3) (p + 4) = 2 * h0
  bp3p : s.b (p + 3) p = 2 * h0
  a45 : s.a (p + 4) (p + 5) = 2
  b45 : s.b (p + 4) (p + 5) = 2 * h0
  a14 : s.a (p + 1) (p + 4) = 2
  b14 : s.b (p + 1) (p + 4) = 2 * h0
  a56 : s.a (p + 5) (p + 6) = s.a (p + 1) (p + 2)
  b56 : s.b (p + 5) (p + 6) = s.b (p + 1) (p + 2)
  a63 : s.a (p + 6) (p + 3) = s.a (p + 2) (p + 3)
  b63 : s.b (p + 6) (p + 3) = s.b (p + 2) (p + 3)
  wk : ¬(dist (v (p + 2)) (v (p + 5)) = cstab ∧ dist (v (p + 2)) (v (p + 3)) = cstab)
  nc1 : ¬Collinear ℝ ({0, v (p + 1), v (p + 2)} : Set V3)
  nc2 : ¬Collinear ℝ ({0, v (p + 1), v p} : Set V3)
  nc3 : ¬Collinear ℝ ({0, v (p + 3), v p} : Set V3)
  nc4 : ¬Collinear ℝ ({0, v (p + 3), v (p + 2)} : Set V3)
  az1 : azim 0 (v (p + 1)) (v (p + 2)) (v p) = dihV 0 (v (p + 1)) (v (p + 2)) (v p)
  az3 : azim 0 (v (p + 3)) (v p) (v (p + 2)) = dihV 0 (v (p + 3)) (v p) (v (p + 2))

/-- C-prep of the `str p` branch of `PWEIWBZ` (HOL `VASYYAU.hl:1173-1306`):
packages the generic-position, fan/rho bookkeeping, the at-most-one-straight
consequences, the value-table mod-shifts at `p+3`, the diagonal bounds and the
`WKZZEEH @ p+2` no-go into `PweiwbzPrep`. -/
private theorem pweiwbz_prep (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (hns1 : ¬scsIsStr s v (p + 1)) (hns3 : ¬scsIsStr s v (p + 3)) (hs1 : scsIsStr s v p)
    (hn : norm (v p) = 2) (ha : s.a p (p + 1) = 2) (ha30 : s.a (p + 3) p = 2) :
    PweiwbzPrep s v p := by
  let FF : Set (V3 × V3) := Set.range fun i => (v i, v (i + 1))
  have hFF : Set.range (fun i => (v i, v (i + 1))) = FF := rfl
  have hgen : scsGeneric v := GSXRFWM_p33 s v his hk hv
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hv
  have hper : Periodic v 4 := by
    have h1 := hBB.2.1
    rw [hk] at h1
    exact h1
  have his' : isScsV39 s := his
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpb, -, hsym, -, -, -, -, -, -, -, -⟩ := his
  have hpa4 : Periodic2 s.a 4 := hk ▸ hpa
  have hpb4 : Periodic2 s.b 4 := hk ▸ hpb
  have hcl : ConvexLocalFan (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF :=
    BBS_IMP_CONVEX_LOCAL_FAN_p34 s 4 v (by omega) hk hBB
  have hcl2 : convexLocalFan_p2 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF := w15_clf2 hcl
  have hrho : ∀ j : ℕ, rhoNode1 FF (v j) = v (j + 1) ∧
      ivsRhoNode1 FF (v j) = v (j + 3) := by
    intro j
    obtain ⟨h1, h2⟩ := BB_RHO_NODE_IVS_p26 s 4 v (v j) (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF j hk rfl rfl rfl rfl his'
      (by omega) hBB
    exact ⟨h1, by rw [h2, show j + 4 - 1 = j + 3 by omega]⟩
  have hangLe : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) ≤ Real.pi := by
    intro j
    have h0 := IN_V_IMP_AZIM_LESS_PI (V := Set.range v)
      (E := Set.range fun i => ({v i, v (i + 1)} : Set V3)) (FF := FF)
      hcl2 (v j) ⟨j, rfl⟩ (v (j + 3)) ⟨j + 3, rfl⟩
    rw [show rhoNode1_p2 FF (v j) = v (j + 1) by
      rw [show rhoNode1_p2 FF (v j) = rhoNode1 FF (v j) from rfl, (hrho j).1]] at h0
    exact h0
  have hia : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) =
      interiorAngle1 0 FF (v j) := by
    intro j
    have h1 := INTERIOR_ANGLE1_AZIM_p22 s v j his' hBB (by rw [hk]; norm_num) FF hFF.symm
    rw [hk] at h1
    simpa only [show j + (4 - 1) = j + 3 by omega] using h1
  have hiaLt : ∀ j : ℕ, ¬scsIsStr s v j → interiorAngle1 0 FF (v j) < Real.pi := by
    intro j hj
    have hle := hangLe j
    have hne : azim 0 (v j) (v (j + 1)) (v (j + 3)) ≠ Real.pi := by
      intro he
      exact hj (by simpa only [scsIsStr, hk] using he)
    rw [← hia j]
    exact lt_of_le_of_ne hle hne
  -- at-most-one-straight consequences
  have hns2 : ¬scsIsStr s v (p + 2) := by
    intro hc
    have e := pweiwbz_str_uniq h s v his' hk hv (p + 2) p hc hs1
    omega
  have hns5 : ¬scsIsStr s v (p + 5) := by
    intro hc
    have h1 : scsIsStr s v ((p + 5) % 4) := (STR_MOD_EQ_p25 s v 4 his' hk hv (p + 5)).mpr hc
    have h2 : ¬scsIsStr s v ((p + 1) % 4) := by
      intro h3
      exact hns1 ((STR_MOD_EQ_p25 s v 4 his' hk hv (p + 1)).mp h3)
    exact h2 (by rwa [show (p + 5) % 4 = (p + 1) % 4 by omega] at h1)
  -- diagonal bounds
  have hdiagLt : ∀ i j : ℕ, scsDiag 4 i j → s.a i j < dist (v i) (v j) := by
    intro i j hd
    exact (hdiag i j hd).1.trans_lt (hdiag i j hd).2.1
  have hdiag3 : ∀ i j : ℕ, scsDiag 4 i j → 3 ≤ dist (v i) (v j) := by
    intro i j hd
    linarith [show (3 : ℝ) < cstab by norm_num [cstab], (hdiag i j hd).2.1]
  have hdiagB : ∀ i j : ℕ, scsDiag 4 i j → 4 * h0 < s.b i j :=
    fun i j hd => (hdiag i j hd).2.2
  have hdiagP2P : scsDiag 4 (p + 2) p := by
    unfold scsDiag
    refine ⟨?_, ?_, ?_⟩ <;> omega
  have hdiagP1P3 : scsDiag 4 (p + 1) (p + 3) := by
    unfold scsDiag
    refine ⟨?_, ?_, ?_⟩ <;> omega
  -- value table facts
  have hvalLt : ∀ i : ℕ, s.a i (i + 1) < s.b i (i + 1) :=
    fun i => CONDTION_A_LT_B_p25 s hval i
  have hb01 : s.b p (p + 1) = 2 * h0 := A_EQ2_IMP_B_p25 s p hval ha
  have ha34 : s.a (p + 3) (p + 4) = 2 := ((hpa4 (p + 3) p).2).trans ha30
  have hb34 : s.b (p + 3) (p + 4) = 2 * h0 := A_EQ2_IMP_B_p25 s (p + 3) hval ha34
  have hbp3p : s.b (p + 3) p = 2 * h0 := ((hpb4 (p + 3) p).2).symm.trans hb34
  have ha45 : s.a (p + 4) (p + 5) = 2 :=
    ((hpa4 (p + 4) (p + 1)).2).trans (((hpa4 p (p + 1)).1).trans ha)
  have hb45 : s.b (p + 4) (p + 5) = 2 * h0 :=
    ((hpb4 (p + 4) (p + 1)).2).trans (((hpb4 p (p + 1)).1).trans hb01)
  have ha14 : s.a (p + 1) (p + 4) = 2 :=
    ((hpa4 (p + 1) p).2).trans (((hsym (p + 1) p).1).trans ha)
  have hb14 : s.b (p + 1) (p + 4) = 2 * h0 :=
    ((hpb4 (p + 1) p).2).trans (((hsym (p + 1) p).2.2.2.1).trans hb01)
  have ha56 : s.a (p + 5) (p + 6) = s.a (p + 1) (p + 2) :=
    ((hpa4 (p + 5) (p + 2)).2).trans ((hpa4 (p + 1) (p + 2)).1)
  have hb56 : s.b (p + 5) (p + 6) = s.b (p + 1) (p + 2) :=
    ((hpb4 (p + 5) (p + 2)).2).trans ((hpb4 (p + 1) (p + 2)).1)
  have ha63 : s.a (p + 6) (p + 3) = s.a (p + 2) (p + 3) :=
    (hpa4 (p + 2) (p + 3)).1
  have hb63 : s.b (p + 6) (p + 3) = s.b (p + 2) (p + 3) :=
    (hpb4 (p + 2) (p + 3)).1
  -- the `WKZZEEH @ p+2` no-go (HOL :1301-1303)
  have hwk : ¬(dist (v (p + 2)) (v (p + 5)) = cstab ∧
      dist (v (p + 2)) (v (p + 3)) = cstab) :=
    WKZZEEH_kit h s v (p + 2) his' hb hk hv hdiag hval hns2 hns3 hns5
  -- non-collinearity at the two relevant vertices
  have hvne : ∀ i j : ℕ, v i = v j → i % 4 = j % 4 := by
    intro i j he
    have h1 := (BB_VV_FUN_EQ_p26 s v his' hBB i j).mp he
    rwa [hk] at h1
  have hnc1 : ¬Collinear ℝ ({0, v (p + 1), v (p + 2)} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF (v (p + 1)) (v (p + 2))
      hcl.1 ⟨p + 1, rfl⟩ ⟨p + 2, rfl⟩
      (fun he => by have h1 := hvne (p + 1) (p + 2) he; omega) hgen
  have hnc2 : ¬Collinear ℝ ({0, v (p + 1), v p} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF (v (p + 1)) (v p)
      hcl.1 ⟨p + 1, rfl⟩ ⟨p, rfl⟩
      (fun he => by have h1 := hvne (p + 1) p he; omega) hgen
  have hnc3 : ¬Collinear ℝ ({0, v (p + 3), v p} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF (v (p + 3)) (v p)
      hcl.1 ⟨p + 3, rfl⟩ ⟨p, rfl⟩
      (fun he => by have h1 := hvne (p + 3) p he; omega) hgen
  have hnc4 : ¬Collinear ℝ ({0, v (p + 3), v (p + 2)} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF (v (p + 3)) (v (p + 2))
      hcl.1 ⟨p + 3, rfl⟩ ⟨p + 2, rfl⟩
      (fun he => by have h1 := hvne (p + 3) (p + 2) he; omega) hgen
  -- azim/dihV bridges for the two `hcase` first disjuncts
  have hle1 : azim 0 (v (p + 1)) (v (p + 2)) (v p) ≤ Real.pi := by
    have h1 := hangLe (p + 1)
    rw [show (p + 1) + 3 = p + 4 by omega] at h1
    rw [hper p] at h1
    exact h1
  have hle3 : azim 0 (v (p + 3)) (v p) (v (p + 2)) ≤ Real.pi := by
    have h1 := hangLe (p + 3)
    rw [show (p + 3) + 1 = p + 4 by omega] at h1
    rw [show (p + 3) + 3 = p + 6 by omega] at h1
    rw [show p + 6 = (p + 2) + 4 by omega] at h1
    rw [hper (p + 2)] at h1
    rw [hper p] at h1
    exact h1
  have haz1 : azim 0 (v (p + 1)) (v (p + 2)) (v p) = dihV 0 (v (p + 1)) (v (p + 2)) (v p) :=
    AZIM_DIHV_SAME_STRONG hnc1 hnc2 hle1
  have haz3 : azim 0 (v (p + 3)) (v p) (v (p + 2)) = dihV 0 (v (p + 3)) (v p) (v (p + 2)) :=
    AZIM_DIHV_SAME_STRONG hnc3 hnc4 hle3
  exact
    { gen := hgen, bbs := hBB, per := hper, pa4 := hpa4, pb4 := hpb4, rho := hrho
      ia := hia, angLe := hangLe, iaLt := hiaLt, ns2 := hns2, ns5 := hns5
      diagLt := hdiagLt, diag3 := hdiag3, diagB := hdiagB, diagP2P := hdiagP2P
      diagP1P3 := hdiagP1P3, valLt := hvalLt, b01 := hb01, a34 := ha34, b34 := hb34
      bp3p := hbp3p, a45 := ha45, b45 := hb45, a14 := ha14, b14 := hb14, a56 := ha56
      b56 := hb56, a63 := ha63, b63 := hb63, wk := hwk, nc1 := hnc1, nc2 := hnc2
      nc3 := hnc3, nc4 := hnc4, az1 := haz1, az3 := haz3 }

/-- HOL `PWEIWBZ` (VASYYAU.hl:1126-2348), `str p` branch leaf
`s.a (p+3) p = 2` (VASYYAU.hl:1308-1391): under the master premises with
`scsIsStr s v p`, `¬scsIsStr s v (p+1)`, `¬scsIsStr s v (p+3)`,
`norm (v p) = 2` and `s.a (p+3) p = 2`, the perimeter edge `(p,p+1)` is `2`.

Assembly: split on the value table at `p+1`.  If `a(p+1)(p+2) = 2` then
`YEBWJNG @ p+1` gives `dist(v(p+1),v(p+2)) = 2` and `CQAOQLR @ p` transports it
to the goal (HOL :1281-1292).  Otherwise `a(p+1)(p+2) = 2*h0` and
`b(p+1)(p+2) = cstab`; split on `dist(v(p+1),v(p+2))`:
if it is `2*h0`, `LEMMA_PWE1 @ p` supplies the `dihV` bound that is
CJBDXXN's `hcase` first disjunct and `CJBDXXN @ p+1` lands on
`dist(v(p+1),v(p)) = 2` (HOL :1315-1360); if it is `cstab`, `WKZZEEH @ p+2`
kills the `cstab` option at `(p+2,p+3)`, `LEMMA_PWE2 @ p` supplies the
`dihV` bound at `v(p+3)`, `CUXVZOZ @ p+3` gives `dist(v(p+3),v(p+4)) = 2` and
`CQAOQLR @ p+3` transports it to the goal (HOL :1394-1607 route). -/
private theorem pweiwbz_B_a30eq2 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (hns1 : ¬scsIsStr s v (p + 1)) (hns3 : ¬scsIsStr s v (p + 3)) (hs1 : scsIsStr s v p)
    (hn : norm (v p) = 2) (ha : s.a p (p + 1) = 2) (ha30 : s.a (p + 3) p = 2) :
    dist (v p) (v (p + 1)) = 2 := by
  let FF : Set (V3 × V3) := Set.range fun i => (v i, v (i + 1))
  have hFF : Set.range (fun i => (v i, v (i + 1))) = FF := rfl
  let P := pweiwbz_prep h s v p his hb hk hv hdiag hval hns1 hns3 hs1 hn ha ha30
  have hv4 : ∀ i : ℕ, v (i + 4) = v i := P.per
  have hp4 : v (p + 4) = v p := hv4 p
  have hp5 : v (p + 5) = v (p + 1) := by
    have h1 := hv4 (p + 1)
    simpa only [show p + 1 + 4 = p + 5 by omega] using h1
  have hia : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) = interiorAngle1 0 FF (v j) := by
    intro j
    simpa only [hFF] using P.ia j
  have hiaLt : ∀ j : ℕ, ¬scsIsStr s v j → interiorAngle1 0 FF (v j) < Real.pi := by
    intro j hj
    simpa only [hFF] using P.iaLt j hj
  by_cases hA : s.a (p + 1) (p + 2) = 2
  · -- ═══ `a(p+1)(p+2) = 2`: `YEBWJNG @ p+1` + `CQAOQLR @ p` (HOL :1281-1292) ═══
    have hY : dist (v (p + 1)) (v (p + 2)) = 2 :=
      YEBWJNG_kit h s v (p + 1) his hb hk hv hdiag hval hns1 P.ns2 hA
    have hb12 : s.b (p + 1) (p + 2) = 2 * h0 := A_EQ2_IMP_B_p25 s (p + 1) hval hA
    have hif := CQAOQLR_p16 h s v p (by rw [hk]; norm_num) his hv P.gen hb
      (fun i j hd => hdiag i j (by rw [hk] at hd; exact hd))
      (by rw [P.b01]; norm_num [h0])
      (by rw [hb12]; norm_num [h0])
      (P.valLt (p + 2))
      (by
        have e : p + s.k - 1 = p + 3 := by rw [hk]; omega
        rw [e, ha30, P.bp3p]
        norm_num [h0])
      ha (le_of_eq P.b01) hA (le_of_eq hb12)
    exact hif.mpr hY
  · -- ═══ `a(p+1)(p+2) ≠ 2`, hence `a = 2*h0`, `b = cstab` ═══
    obtain ⟨ha12, hb12⟩ := A_NOT_EQ2_IMP_B_p25 s (p + 1) hval hA
    have hTU := TUAPYYU_kit h s v (p + 1) his hb hk hv hdiag hval hns1 P.ns2
    by_cases hB1 : dist (v (p + 1)) (v (p + 2)) = 2 * h0
    · -- ═══ `dist(p+1,p+2) = 2*h0`: `LEMMA_PWE1` + `CJBDXXN @ p+1` (HOL :1315-1360) ═══
      have hPWE := LEMMA_PWE1_p23 h s v p his hb hk hv hdiag hval P.gen hns1 hns3 hs1
        hn ha ha30 (le_of_eq hB1)
      have hcase1 : Real.pi / 2 < interiorAngle1 0 FF (v (p + 1)) ∨
          interiorAngle1 0 FF (v ((p + 1) + (4 - 1))) < Real.pi := Or.inl (by
        rw [← hia (p + 1)]
        rw [show (p + 1) + 3 = p + 4 by omega, hp4, P.az1]
        exact hPWE)
      have hd1 : 3 ≤ dist (v ((p + 1) + 1)) (v ((p + 1) + (4 - 1))) := by
        have h1 := P.diag3 (p + 2) p P.diagP2P
        simpa only [show (p + 1) + 1 = p + 2 by omega,
          show (p + 1) + (4 - 1) = p + 4 by omega, hp4] using h1
      have hang1 : interiorAngle1 0 FF (v (p + 1)) < Real.pi := hiaLt (p + 1) hns1
      have h2_1 : 2 ≤ dist (v ((p + 1) + 1)) (v (p + 1)) := by
        rw [show (p + 1) + 1 = p + 2 by omega, dist_comm (v (p + 2)) (v (p + 1)), hB1]
        norm_num [h0]
      have hdc1 : dist (v ((p + 1) + 1)) (v (p + 1)) ≤ cstab := by
        rw [show (p + 1) + 1 = p + 2 by omega, dist_comm (v (p + 2)) (v (p + 1)), hB1]
        norm_num [h0, cstab]
      have hCJ := CJBDXXN_p21 h s FF 4 (p + 1) v hFF.symm his hk.symm (by norm_num) hv hb
        P.gen hd1 (fun i j hdij _ => P.diagLt i j hdij) P.diagB hang1 hcase1
        P.a14 (le_of_eq P.b14) h2_1 hdc1
      have hgoal : dist (v (p + 1)) (v p) = 2 := by
        simpa only [show (p + 1) + (4 - 1) = p + 4 by omega, hp4] using hCJ
      rw [dist_comm (v p) (v (p + 1))]
      exact hgoal
    · -- ═══ `dist(p+1,p+2) = cstab`: `WKZZEEH @ p+2` + `PWE2` + `CUXVZOZ @ p+3` + `CQAOQLR @ p+3` ═══
      have hB2 : dist (v (p + 1)) (v (p + 2)) = cstab := by
        rcases hTU with he | he
        · exact absurd (by rw [show p + 1 + 1 = p + 2 by omega]; exact he.trans ha12) hB1
        · rw [show p + 1 + 1 = p + 2 by omega] at he hb12
          exact he.trans hb12
      have hwk : ¬(dist (v (p + 2)) (v (p + 1)) = cstab ∧
          dist (v (p + 2)) (v (p + 3)) = cstab) := by
        intro hcon
        apply P.wk
        refine ⟨?_, hcon.2⟩
        rw [hp5]
        exact hcon.1
      have hd23 : dist (v (p + 2)) (v (p + 3)) ≤ 2 * h0 := by
        rcases TUAPYYU_kit h s v (p + 2) his hb hk hv hdiag hval P.ns2 hns3 with he | he
        · rcases hval (p + 2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [he, h1]; norm_num [h0]
          · rw [he, h1]
        · rcases hval (p + 2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [he, h2]
          · have hc : dist (v (p + 2)) (v (p + 3)) = cstab := by rw [he, h2]
            exact absurd ⟨by rw [dist_comm]; exact hB2, hc⟩ hwk
      have hPWE2 := LEMMA_PWE2_p23 h s v p his hb hk hv hdiag hval P.gen hns1 hns3 hs1
        hn ha ha30 hd23
      have hcase3 : Real.pi / 2 < interiorAngle1 0 FF (v (p + 3)) ∨
          interiorAngle1 0 FF (v ((p + 3) + 1)) < Real.pi := Or.inl (by
        rw [← hia (p + 3)]
        rw [show (p + 3) + 1 = p + 4 by omega]
        rw [show (p + 3) + 3 = p + 6 by omega, show p + 6 = (p + 2) + 4 by omega,
          hv4 (p + 2), hp4, P.az3]
        exact hPWE2)
      have hd3 : 3 ≤ dist (v ((p + 3) + (4 - 1))) (v ((p + 3) + 1)) := by
        have h1 := P.diag3 (p + 2) p P.diagP2P
        rw [show (p + 3) + (4 - 1) = p + 6 by omega]
        rw [show (p + 3) + 1 = p + 4 by omega]
        rw [show p + 6 = (p + 2) + 4 by omega, hv4 (p + 2), hp4]
        exact h1
      have hang3 : interiorAngle1 0 FF (v (p + 3)) < Real.pi := hiaLt (p + 3) hns3
      have h2_3 : 2 ≤ dist (v ((p + 3) + (4 - 1))) (v (p + 3)) := by
        rw [show (p + 3) + (4 - 1) = p + 6 by omega,
          show p + 6 = (p + 2) + 4 by omega, hv4 (p + 2)]
        have hle := (P.bbs.2.2.1 (p + 2) (p + 3)).1
        rcases hval (p + 2) with ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [h1] at hle; linarith
        · rw [h1] at hle
          linarith [show (2 : ℝ) ≤ 2 * h0 by norm_num [h0]]
      have hdc3 : dist (v ((p + 3) + (4 - 1))) (v (p + 3)) ≤ cstab := by
        rw [show (p + 3) + (4 - 1) = p + 6 by omega,
          show p + 6 = (p + 2) + 4 by omega, hv4 (p + 2)]
        linarith [hd23, show 2 * h0 ≤ cstab by norm_num [h0, cstab]]
      have hCUX := CUXVZOZ_p21 h s FF 4 (p + 3) v hFF.symm his hk.symm (by norm_num) hv hb
        P.gen hd3 (fun i j hdij _ => P.diagLt i j hdij) P.diagB hang3 hcase3
        P.a34 (le_of_eq P.b34) h2_3 hdc3
      have hbA : 2 < s.b (p + 3) (p + 4) := by rw [P.b34]; norm_num [h0]
      have hbB : 2 < s.b (p + 4) (p + 5) := by rw [P.b45]; norm_num [h0]
      have hif := CQAOQLR_p16 h s v (p + 3) (by rw [hk]; norm_num) his hv P.gen hb
        (fun i j hd => hdiag i j (by rw [hk] at hd; exact hd))
        hbA hbB
        (by rw [P.a56, P.b56]; exact P.valLt (p + 1))
        (by
          rw [show (p + 3) + s.k - 1 = p + 6 by rw [hk]; omega, P.a63, P.b63]
          exact P.valLt (p + 2))
        P.a34 (le_of_eq P.b34) P.a45 (le_of_eq P.b45)
      have hstep : dist (v (p + 4)) (v (p + 5)) = 2 := by
        have h1 := hif.mp hCUX
        simpa only [show (p + 3) + 1 = p + 4 by omega,
          show (p + 3) + 2 = p + 5 by omega] using h1
      simpa only [hp4, hp5] using hstep

/-! ## `PWEIWBZ`, `str p` branch, `a(p+3) p ≠ 2` group (VASYYAU.hl:1611-1783)

Under `str p` the value table forces `a(p+3)p ∈ {2, 2*h0}`; the `= 2` group is
`pweiwbz_B_a30eq2` above.  This section covers the complementary
`a(p+3)p ≠ 2` group:

* HOL :1611-1699 — `A_NOT_EQ2_IMP_B @ p+3` gives `a(p+3)(p+4) = 2*h0` and
  `b(p+3)(p+4) = cstab`; `PRO_ADD_NOT_IN_SCS_M @ {p+1, p+3}` puts both
  residues in `scsM`, so `B_LE_2h0_2_SCS_M_4_1 @ p` gives
  `b(p+2)(p+3) ≤ 2*h0`, `B_LE_2h0_IMP_B @ p+2` gives `a(p+2)(p+3) = 2`, and
  `YEBWJNG @ p+2` pins `dist(v(p+2),v(p+3)) = 2`.  `TUAPYYU @ p+1`
  localises `dist(v(p+1),v(p+2))` to `{2*h0, cstab}`; in both cases
  `LEMMA_PWE3 @ p` supplies the `dihV` bound at `v(p+1)` that is CJBDXXN's
  `hcase` first disjunct, and `CJBDXXN @ p+1` lands on
  `dist(v(p+1),v p) = 2`.
* HOL :1703-1780 — the second leaf is the `b`-value label (`1 2 = cstab`)
  inside the same `TUAPYYU` split; the Lean statement carries no value label,
  so a single `rcases` covers both (V18 precedent: value labels are not part
  of the Lean statement).

The `str p` C-prep is re-derived here instead of reusing `pweiwbz_prep`:
the latter is stated with `a(p+3)p = 2` and its `a34`/`b34`/`bp3p` fields are
the `= 2` values.  Only the `a30`-independent surface is needed below. -/
private theorem pweiwbz_B_a30ne2 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (hns1 : ¬scsIsStr s v (p + 1)) (hns3 : ¬scsIsStr s v (p + 3)) (hs1 : scsIsStr s v p)
    (hn : norm (v p) = 2) (ha : s.a p (p + 1) = 2) (ha30 : s.a (p + 3) p ≠ 2) :
    dist (v p) (v (p + 1)) = 2 := by
  let FF : Set (V3 × V3) := Set.range fun i => (v i, v (i + 1))
  have hFF : Set.range (fun i => (v i, v (i + 1))) = FF := rfl
  -- ═══ A. substrate: generic position, periodicity, the local fan ═══
  have hgen : scsGeneric v := GSXRFWM_p33 s v his hk hv
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hv
  have hper : Periodic v 4 := by
    have h1 := hBB.2.1
    rw [hk] at h1
    exact h1
  have his' : isScsV39 s := his
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpb, -, hsym, -, -, -, -, -, -, -, -⟩ := his
  have hpa4 : Periodic2 s.a 4 := hk ▸ hpa
  have hpb4 : Periodic2 s.b 4 := hk ▸ hpb
  have hcl : ConvexLocalFan (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF :=
    BBS_IMP_CONVEX_LOCAL_FAN_p34 s 4 v (by omega) hk hBB
  have hcl2 : convexLocalFan_p2 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF := w15_clf2 hcl
  have hrho : ∀ j : ℕ, rhoNode1 FF (v j) = v (j + 1) ∧
      ivsRhoNode1 FF (v j) = v (j + 3) := by
    intro j
    obtain ⟨h1, h2⟩ := BB_RHO_NODE_IVS_p26 s 4 v (v j) (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF j hk rfl rfl rfl rfl his'
      (by omega) hBB
    exact ⟨h1, by rw [h2, show j + 4 - 1 = j + 3 by omega]⟩
  have hangLe : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) ≤ Real.pi := by
    intro j
    have h0 := IN_V_IMP_AZIM_LESS_PI (V := Set.range v)
      (E := Set.range fun i => ({v i, v (i + 1)} : Set V3)) (FF := FF)
      hcl2 (v j) ⟨j, rfl⟩ (v (j + 3)) ⟨j + 3, rfl⟩
    rw [show rhoNode1_p2 FF (v j) = v (j + 1) by
      rw [show rhoNode1_p2 FF (v j) = rhoNode1 FF (v j) from rfl, (hrho j).1]] at h0
    exact h0
  have hia : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) =
      interiorAngle1 0 FF (v j) := by
    intro j
    have h1 := INTERIOR_ANGLE1_AZIM_p22 s v j his' hBB (by rw [hk]; norm_num) FF hFF.symm
    rw [hk] at h1
    simpa only [show j + (4 - 1) = j + 3 by omega] using h1
  have hiaLt : ∀ j : ℕ, ¬scsIsStr s v j → interiorAngle1 0 FF (v j) < Real.pi := by
    intro j hj
    have hle := hangLe j
    have hne : azim 0 (v j) (v (j + 1)) (v (j + 3)) ≠ Real.pi := by
      intro he
      exact hj (by simpa only [scsIsStr, hk] using he)
    rw [← hia j]
    exact lt_of_le_of_ne hle hne
  -- ═══ B. at-most-one-straight consequence at `p+2` ═══
  have hns2 : ¬scsIsStr s v (p + 2) := by
    intro hc
    have e := pweiwbz_str_uniq h s v his' hk hv (p + 2) p hc hs1
    omega
  -- ═══ C. diagonal bounds ═══
  have hdiagLt : ∀ i j : ℕ, scsDiag 4 i j → s.a i j < dist (v i) (v j) := by
    intro i j hd
    exact (hdiag i j hd).1.trans_lt (hdiag i j hd).2.1
  have hdiag3 : ∀ i j : ℕ, scsDiag 4 i j → 3 ≤ dist (v i) (v j) := by
    intro i j hd
    linarith [show (3 : ℝ) < cstab by norm_num [cstab], (hdiag i j hd).2.1]
  have hdiagB : ∀ i j : ℕ, scsDiag 4 i j → 4 * h0 < s.b i j :=
    fun i j hd => (hdiag i j hd).2.2
  have hdiagP2P : scsDiag 4 (p + 2) p := by
    unfold scsDiag
    refine ⟨?_, ?_, ?_⟩ <;> omega
  -- ═══ D. value table: the `(p,p+1)` and `(p+1,p+4)` rows ═══
  have hvalLt : ∀ i : ℕ, s.a i (i + 1) < s.b i (i + 1) :=
    fun i => CONDTION_A_LT_B_p25 s hval i
  have hb01 : s.b p (p + 1) = 2 * h0 := A_EQ2_IMP_B_p25 s p hval ha
  have ha14 : s.a (p + 1) (p + 4) = 2 :=
    ((hpa4 (p + 1) p).2).trans (((hsym (p + 1) p).1).trans ha)
  have hb14 : s.b (p + 1) (p + 4) = 2 * h0 :=
    ((hpb4 (p + 1) p).2).trans (((hsym (p + 1) p).2.2.2.1).trans hb01)
  -- ═══ E. the `(p+3,p)` edge is `(2*h0, cstab)` on this branch (HOL :1614-1616) ═══
  have hne34 : s.a (p + 3) (p + 4) ≠ 2 := fun hc =>
    ha30 (((hpa4 (p + 3) p).2).symm.trans hc)
  obtain ⟨ha34, hb34⟩ := A_NOT_EQ2_IMP_B_p25 s (p + 3) hval hne34
  have ha30' : s.a (p + 3) p = 2 * h0 := ((hpa4 (p + 3) p).2).symm.trans ha34
  have hbp3p : s.b (p + 3) p = cstab := ((hpb4 (p + 3) p).2).symm.trans hb34
  -- ═══ F. non-collinearity at `v(p+1)` and the `azim = dihV` bridge ═══
  have hvne : ∀ i j : ℕ, v i = v j → i % 4 = j % 4 := by
    intro i j he
    have h1 := (BB_VV_FUN_EQ_p26 s v his' hBB i j).mp he
    rwa [hk] at h1
  have hnc1 : ¬Collinear ℝ ({0, v (p + 1), v (p + 2)} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF (v (p + 1)) (v (p + 2))
      hcl.1 ⟨p + 1, rfl⟩ ⟨p + 2, rfl⟩
      (fun he => by have h1 := hvne (p + 1) (p + 2) he; omega) hgen
  have hnc2 : ¬Collinear ℝ ({0, v (p + 1), v p} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF (v (p + 1)) (v p)
      hcl.1 ⟨p + 1, rfl⟩ ⟨p, rfl⟩
      (fun he => by have h1 := hvne (p + 1) p he; omega) hgen
  have hle1 : azim 0 (v (p + 1)) (v (p + 2)) (v p) ≤ Real.pi := by
    have h1 := hangLe (p + 1)
    rw [show (p + 1) + 3 = p + 4 by omega] at h1
    rw [hper p] at h1
    exact h1
  have haz1 : azim 0 (v (p + 1)) (v (p + 2)) (v p) =
      dihV 0 (v (p + 1)) (v (p + 2)) (v p) :=
    AZIM_DIHV_SAME_STRONG hnc1 hnc2 hle1
  -- ═══ G. the `a(p+1)(p+2)` split (HOL :1262-1292 vs. :1294 onward) ═══
  by_cases hA : s.a (p + 1) (p + 2) = 2
  · -- `a12 = 2`: `YEBWJNG @ p+1` + `CQAOQLR @ p` (HOL :1281-1292)
    have hY : dist (v (p + 1)) (v (p + 2)) = 2 :=
      YEBWJNG_kit h s v (p + 1) his' hb hk hv hdiag hval hns1 hns2 hA
    have hb12 : s.b (p + 1) (p + 2) = 2 * h0 := A_EQ2_IMP_B_p25 s (p + 1) hval hA
    have hif := CQAOQLR_p16 h s v p (by rw [hk]; norm_num) his' hv hgen hb
      (fun i j hd => hdiag i j (by rw [hk] at hd; exact hd))
      (by rw [hb01]; norm_num [h0])
      (by rw [hb12]; norm_num [h0])
      (hvalLt (p + 2))
      (by
        have e : p + s.k - 1 = p + 3 := by rw [hk]; omega
        rw [e, ha30', hbp3p]
        norm_num [h0, cstab])
      ha (le_of_eq hb01) hA (le_of_eq hb12)
    exact hif.mpr hY
  · -- ═══ H. `a12 ≠ 2`: `a12 = 2*h0`, `b12 = cstab` (HOL :1294-1306) ═══
    obtain ⟨ha12, hb12⟩ := A_NOT_EQ2_IMP_B_p25 s (p + 1) hval hA
    -- both residues land in `scsM`; `b(p+2)(p+3) ≤ 2*h0` (HOL :1617-1618)
    have hmem1 : (p + 1) % 4 ∈ scsM s :=
      PRO_ADD_NOT_IN_SCS_M_p25 s (p + 1) 4 his' hk ha12
    have hmem3 : (p + 3) % 4 ∈ scsM s :=
      PRO_ADD_NOT_IN_SCS_M_p25 s (p + 3) 4 his' hk ha34
    have hsub : {((p + 1) % 4), ((p + 3) % 4)} ⊆ scsM s := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · rw [hx]; exact hmem1
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]; exact hmem3
    have hb23le : s.b (p + 2) (p + 3) ≤ 2 * h0 :=
      B_LE_2h0_2_SCS_M_4_1_p25 s his' hk hsub
    obtain ⟨ha23, hb23⟩ := B_LE_2h0_IMP_B_p25 s (p + 2) hval hb23le
    -- `YEBWJNG @ p+2`: the `(p+2,p+3)` edge is `2` (HOL :1620-1622)
    have hY2 : dist (v (p + 2)) (v (p + 3)) = 2 :=
      YEBWJNG_kit h s v (p + 2) his' hb hk hv hdiag hval hns2 hns3 ha23
    -- `TUAPYYU @ p+1`: `dist(p+1,p+2) ∈ {a12, b12}` (HOL :1626-1628)
    have hTU := TUAPYYU_kit h s v (p + 1) his' hb hk hv hdiag hval hns1 hns2
    have hd2 : 2 * h0 ≤ dist (v (p + 1)) (v (p + 2)) := by
      rcases hTU with he | he
      · rw [he]
        exact le_of_eq ha12.symm
      · rw [he, hb12]
        norm_num [h0, cstab]
    -- `LEMMA_PWE3 @ p`: the `dihV` bound at `v(p+1)` (HOL :1631-1633)
    have hPWE := LEMMA_PWE3_p23 h s v p his' hb hk hv hdiag hval hgen hns1 hns3 hs1
      hn ha ha30' hY2 hd2
    have hPWE' : Real.pi / 2 < dihV 0 (v (p + 1)) (v (p + 2)) (v p) := by
      rw [DIHV_SYM_2]
      exact hPWE
    have hcase1 : Real.pi / 2 < interiorAngle1 0 FF (v (p + 1)) ∨
        interiorAngle1 0 FF (v ((p + 1) + (4 - 1))) < Real.pi := Or.inl (by
      rw [← hia (p + 1)]
      rw [show (p + 1) + 3 = p + 4 by omega, hper p, haz1]
      exact hPWE')
    have hd1 : 3 ≤ dist (v ((p + 1) + 1)) (v ((p + 1) + (4 - 1))) := by
      have h1 := hdiag3 (p + 2) p hdiagP2P
      simpa only [show (p + 1) + 1 = p + 2 by omega,
        show (p + 1) + (4 - 1) = p + 4 by omega, hper p] using h1
    have hang1 : interiorAngle1 0 FF (v (p + 1)) < Real.pi := hiaLt (p + 1) hns1
    have h2_1 : 2 ≤ dist (v ((p + 1) + 1)) (v (p + 1)) := by
      rcases hTU with he | he
      · rw [show (p + 1) + 1 = p + 2 by omega, dist_comm, he, ha12]
        norm_num [h0]
      · rw [show (p + 1) + 1 = p + 2 by omega, dist_comm, he, hb12]
        norm_num [h0, cstab]
    have hdc1 : dist (v ((p + 1) + 1)) (v (p + 1)) ≤ cstab := by
      rcases hTU with he | he
      · rw [show (p + 1) + 1 = p + 2 by omega, dist_comm, he, ha12]
        norm_num [h0, cstab]
      · rw [show (p + 1) + 1 = p + 2 by omega, dist_comm, he, hb12]
    -- `CJBDXXN @ p+1`: the reflected check-completeness (HOL :1636-1699 /
    -- :1706-1780); the two `TUAPYYU` labels are absorbed above
    have hCJ := CJBDXXN_p21 h s FF 4 (p + 1) v hFF.symm his' hk.symm (by norm_num) hv hb
      hgen hd1 (fun i j hdij _ => hdiagLt i j hdij) hdiagB hang1 hcase1
      ha14 (le_of_eq hb14) h2_1 hdc1
    have hgoal : dist (v (p + 1)) (v p) = 2 := by
      simpa only [show (p + 1) + (4 - 1) = p + 4 by omega, hper p] using hCJ
    rw [dist_comm (v p) (v (p + 1))]
    exact hgoal

/-! ## `PWEIWBZ`, `str (p+1)` branch (VASYYAU.hl:1784-2345)

Under `scs_is_str s v (p+1)` the master's C-branch splits on
`a(p+3)p = &2` (HOL `:1897-1924`, closed above by `pweiwbz_C1`) versus
`a(p+3)p ≠ &2` (HOL `:1928-2345`).  This section covers the `≠ 2` trunk:
`PweiwbzC2Prep` is the C-prep of HOL `:1784-1896` (generic position, `BBs`
bounds, periodicity, the local-fan rho/interior-angle surface, the
at-most-one-straight consequences, the value-table mod-shifts, the
`WKZZEEH @ p+3` no-go of HOL `:1948-1950` and `PRO_ADD_NOT_IN_SCS_M @ p+3` of
HOL `:1951`), and the `a(p+1)(p+2) = &2` group (HOL `:1955-2196`) is closed
completely:

* `pweiwbz_C_a12eq2` — HOL `:1955-2037`, the `dist(v(p+3),v(p+4)) = 2*h0`
  branch: `LEMMA_PWE2 @ p+1` gives the `dihV` bound at `v p` that is
  `CUXVZOZ @ p`'s `hcase`, and `CUXVZOZ @ p` lands on `dist(v p,v(p+1)) = 2`;
* `pweiwbz_C_a23le` — HOL `:2040-2196`, the `dist(v(p+2),v(p+3)) ≤ 2*h0`
  branch (both the `2` and the `2*h0` labels): `LEMMA_PWE1 @ p+1` gives the
  `dihV` bound at `v(p+2)` that is `CJBDXXN @ p+2`'s `hcase`,
  `CJBDXXN @ p+2` pins `dist(v(p+2),v(p+5)) = 2` and `CQAOQLR @ p`
  transports it to the goal;
* `pweiwbz_C_a12` — the dispatch: `TUAPYYU @ p+3` (HOL `:1958-1960`) splits
  the `(p+3,p+4)` label; in the `cstab` branch `WKZZEEH @ p+3` (`:1948-1950`)
  rules out `dist(v(p+2),v(p+3)) = cstab` and `TUAPYYU @ p+2`
  (`:2030-2037`) then gives the `≤ 2*h0` label consumed by
  `pweiwbz_C_a23le`.

Both leaves take the `norm (v (p+1)) = 2` label of HOL `:1881` (the
`NUXCOEAv2` side of that split; the `≠ 2` side is `IMJXPHRv2`, same
conclusion).  The `a(p+1)(p+2) ≠ &2` group (HOL `:2199-2345`) is not
covered here.
-/

/-- Common facts of the `str (p+1)` C-prep under `s.a (p+3) p ≠ 2`
(HOL `VASYYAU.hl:1784-1896` + the trunk `:1928-1953`), shared by the
`a(p+1)(p+2)`-split leaves below. -/
private structure PweiwbzC2Prep (s : ScsV39) (v : ℕ → V3) (p : ℕ) : Prop where
  gen : scsGeneric v
  bbs : BBsV39 s v
  per : Periodic v 4
  pa4 : Periodic2 s.a 4
  pb4 : Periodic2 s.b 4
  rho : ∀ j : ℕ, rhoNode1 (Set.range fun i => (v i, v (i + 1))) (v j) = v (j + 1) ∧
    ivsRhoNode1 (Set.range fun i => (v i, v (i + 1))) (v j) = v (j + 3)
  ia : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) =
    interiorAngle1 0 (Set.range fun i => (v i, v (i + 1))) (v j)
  angLe : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) ≤ Real.pi
  iaLt : ∀ j : ℕ, ¬scsIsStr s v j →
    interiorAngle1 0 (Set.range fun i => (v i, v (i + 1))) (v j) < Real.pi
  ns0 : ¬scsIsStr s v p
  ns2 : ¬scsIsStr s v (p + 2)
  ns3 : ¬scsIsStr s v (p + 3)
  ns4 : ¬scsIsStr s v (p + 4)
  ns6 : ¬scsIsStr s v (p + 6)
  diagLt : ∀ i j : ℕ, scsDiag 4 i j → s.a i j < dist (v i) (v j)
  diag3 : ∀ i j : ℕ, scsDiag 4 i j → 3 ≤ dist (v i) (v j)
  diagB : ∀ i j : ℕ, scsDiag 4 i j → 4 * h0 < s.b i j
  diagP1P3 : scsDiag 4 (p + 1) (p + 3)
  valLt : ∀ i : ℕ, s.a i (i + 1) < s.b i (i + 1)
  b01 : s.b p (p + 1) = 2 * h0
  a30 : s.a (p + 3) p = 2 * h0
  b30 : s.b (p + 3) p = cstab
  a34 : s.a (p + 3) (p + 4) = 2 * h0
  b34 : s.b (p + 3) (p + 4) = cstab
  a14 : s.a (p + 1) (p + 4) = 2
  b14 : s.b (p + 1) (p + 4) = 2 * h0
  mem3 : (p + 3) % 4 ∈ scsM s
  wk : ¬(dist (v (p + 2)) (v (p + 3)) = cstab ∧ dist (v (p + 3)) (v (p + 4)) = cstab)
  nc1 : ¬Collinear ℝ ({0, v p, v (p + 1)} : Set V3)
  nc3 : ¬Collinear ℝ ({0, v p, v (p + 3)} : Set V3)
  nc23 : ¬Collinear ℝ ({0, v (p + 2), v (p + 3)} : Set V3)
  nc21 : ¬Collinear ℝ ({0, v (p + 2), v (p + 1)} : Set V3)
  az1 : azim 0 (v p) (v (p + 1)) (v (p + 3)) = dihV 0 (v p) (v (p + 1)) (v (p + 3))
  az2 : azim 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) =
    dihV 0 (v (p + 2)) (v (p + 3)) (v (p + 1))

/-- C-prep of the `str (p+1)`, `a(p+3)p ≠ 2` trunk of `PWEIWBZ`
(HOL `VASYYAU.hl:1784-1896` and `:1928-1953`). -/
private theorem pweiwbz_Cprep2 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (ha01 : s.a p (p + 1) = 2) (hstr1 : scsIsStr s v (p + 1))
    (ha30 : s.a (p + 3) p ≠ 2) :
    PweiwbzC2Prep s v p := by
  let FF : Set (V3 × V3) := Set.range fun i => (v i, v (i + 1))
  have hFF : Set.range (fun i => (v i, v (i + 1))) = FF := rfl
  -- ═══ A. substrate: generic position, BBS bounds, periodicity ═══
  have hgen : scsGeneric v := GSXRFWM_p33 s v his hk hv
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hv
  have hper : Periodic v 4 := by
    have h1 := hBB.2.1
    rw [hk] at h1
    exact h1
  have his' : isScsV39 s := his
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpb, -, hsym, -, -, -, -, -, -, -, -⟩ := his
  have hpa4 : Periodic2 s.a 4 := hk ▸ hpa
  have hpb4 : Periodic2 s.b 4 := hk ▸ hpb
  have hcl : ConvexLocalFan (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF :=
    BBS_IMP_CONVEX_LOCAL_FAN_p34 s 4 v (by omega) hk hBB
  have hcl2 : convexLocalFan_p2 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF := w15_clf2 hcl
  have hrho : ∀ j : ℕ, rhoNode1 FF (v j) = v (j + 1) ∧
      ivsRhoNode1 FF (v j) = v (j + 3) := by
    intro j
    obtain ⟨h1, h2⟩ := BB_RHO_NODE_IVS_p26 s 4 v (v j) (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF j hk rfl rfl rfl rfl his'
      (by omega) hBB
    exact ⟨h1, by rw [h2, show j + 4 - 1 = j + 3 by omega]⟩
  have hangLe : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) ≤ Real.pi := by
    intro j
    have h0 := IN_V_IMP_AZIM_LESS_PI (V := Set.range v)
      (E := Set.range fun i => ({v i, v (i + 1)} : Set V3)) (FF := FF)
      hcl2 (v j) ⟨j, rfl⟩ (v (j + 3)) ⟨j + 3, rfl⟩
    rw [show rhoNode1_p2 FF (v j) = v (j + 1) by
      rw [show rhoNode1_p2 FF (v j) = rhoNode1 FF (v j) from rfl, (hrho j).1]] at h0
    exact h0
  have hia : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) =
      interiorAngle1 0 FF (v j) := by
    intro j
    have h1 := INTERIOR_ANGLE1_AZIM_p22 s v j his' hBB (by rw [hk]; norm_num) FF hFF.symm
    rw [hk] at h1
    simpa only [show j + (4 - 1) = j + 3 by omega] using h1
  have hiaLt : ∀ j : ℕ, ¬scsIsStr s v j → interiorAngle1 0 FF (v j) < Real.pi := by
    intro j hj
    have hle := hangLe j
    have hne : azim 0 (v j) (v (j + 1)) (v (j + 3)) ≠ Real.pi := by
      intro he
      exact hj (by simpa only [scsIsStr, hk] using he)
    rw [← hia j]
    exact lt_of_le_of_ne hle hne
  -- ═══ B. at-most-one-straight consequences (HOL :1789-1797) ═══
  have hns0 : ¬scsIsStr s v p := by
    intro hc
    have e := pweiwbz_str_uniq h s v his' hk hv p (p + 1) hc hstr1
    omega
  have hns2 : ¬scsIsStr s v (p + 2) := by
    intro hc
    have e := pweiwbz_str_uniq h s v his' hk hv (p + 2) (p + 1) hc hstr1
    omega
  have hns3 : ¬scsIsStr s v (p + 3) := by
    intro hc
    have e := pweiwbz_str_uniq h s v his' hk hv (p + 3) (p + 1) hc hstr1
    omega
  have hns4 : ¬scsIsStr s v (p + 4) := by
    intro hc
    have e := pweiwbz_str_uniq h s v his' hk hv (p + 4) (p + 1) hc hstr1
    omega
  have hns6 : ¬scsIsStr s v (p + 6) := by
    intro hc
    have e := pweiwbz_str_uniq h s v his' hk hv (p + 6) (p + 1) hc hstr1
    omega
  -- ═══ C. diagonal bounds ═══
  have hdiagLt : ∀ i j : ℕ, scsDiag 4 i j → s.a i j < dist (v i) (v j) := by
    intro i j hd
    exact (hdiag i j hd).1.trans_lt (hdiag i j hd).2.1
  have hdiag3 : ∀ i j : ℕ, scsDiag 4 i j → 3 ≤ dist (v i) (v j) := by
    intro i j hd
    linarith [show (3 : ℝ) < cstab by norm_num [cstab], (hdiag i j hd).2.1]
  have hdiagB : ∀ i j : ℕ, scsDiag 4 i j → 4 * h0 < s.b i j :=
    fun i j hd => (hdiag i j hd).2.2
  have hdiagP1P3 : scsDiag 4 (p + 1) (p + 3) := by
    unfold scsDiag
    refine ⟨?_, ?_, ?_⟩ <;> omega
  -- ═══ D. value table facts ═══
  have hvalLt : ∀ i : ℕ, s.a i (i + 1) < s.b i (i + 1) :=
    fun i => CONDTION_A_LT_B_p25 s hval i
  have hb01 : s.b p (p + 1) = 2 * h0 := A_EQ2_IMP_B_p25 s p hval ha01
  have hne34 : s.a (p + 3) (p + 4) ≠ 2 := fun hc =>
    ha30 (((hpa4 (p + 3) p).2).symm.trans hc)
  obtain ⟨ha34, hb34⟩ := A_NOT_EQ2_IMP_B_p25 s (p + 3) hval hne34
  have ha30' : s.a (p + 3) p = 2 * h0 := ((hpa4 (p + 3) p).2).symm.trans ha34
  have hb30 : s.b (p + 3) p = cstab := ((hpb4 (p + 3) p).2).symm.trans hb34
  have ha14 : s.a (p + 1) (p + 4) = 2 :=
    ((hpa4 (p + 1) p).2).trans (((hsym (p + 1) p).1).trans ha01)
  have hb14 : s.b (p + 1) (p + 4) = 2 * h0 :=
    ((hpb4 (p + 1) p).2).trans (((hsym (p + 1) p).2.2.2.1).trans hb01)
  -- ═══ E. `PRO_ADD_NOT_IN_SCS_M @ p+3` and `WKZZEEH @ p+3` (HOL :1948-1951) ═══
  have hmem3 : (p + 3) % 4 ∈ scsM s := PRO_ADD_NOT_IN_SCS_M_p25 s (p + 3) 4 his' hk ha34
  have hwk0 := WKZZEEH_kit h s v (p + 3) his' hb hk hv hdiag hval hns3 hns4 hns6
  have hwk : ¬(dist (v (p + 2)) (v (p + 3)) = cstab ∧
      dist (v (p + 3)) (v (p + 4)) = cstab) := by
    intro hcon
    exact hwk0 (by
      refine ⟨?_, hcon.2⟩
      rw [show (p + 3) + 3 = p + 6 by omega, show p + 6 = (p + 2) + 4 by omega,
        hper (p + 2), dist_comm]
      exact hcon.1)
  -- ═══ F. non-collinearity at the two `azim = dihV` bridges ═══
  have hvne : ∀ i j : ℕ, v i = v j → i % 4 = j % 4 := by
    intro i j he
    have h1 := (BB_VV_FUN_EQ_p26 s v his' hBB i j).mp he
    rwa [hk] at h1
  have hnc1 : ¬Collinear ℝ ({0, v p, v (p + 1)} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF (v p) (v (p + 1))
      hcl.1 ⟨p, rfl⟩ ⟨p + 1, rfl⟩
      (fun he => by have h1 := hvne p (p + 1) he; omega) hgen
  have hnc3 : ¬Collinear ℝ ({0, v p, v (p + 3)} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF (v p) (v (p + 3))
      hcl.1 ⟨p, rfl⟩ ⟨p + 3, rfl⟩
      (fun he => by have h1 := hvne p (p + 3) he; omega) hgen
  have hnc23 : ¬Collinear ℝ ({0, v (p + 2), v (p + 3)} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF (v (p + 2)) (v (p + 3))
      hcl.1 ⟨p + 2, rfl⟩ ⟨p + 3, rfl⟩
      (fun he => by have h1 := hvne (p + 2) (p + 3) he; omega) hgen
  have hnc21 : ¬Collinear ℝ ({0, v (p + 2), v (p + 1)} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF (v (p + 2)) (v (p + 1))
      hcl.1 ⟨p + 2, rfl⟩ ⟨p + 1, rfl⟩
      (fun he => by have h1 := hvne (p + 2) (p + 1) he; omega) hgen
  -- ═══ G. the two `azim = dihV` bridges (HOL :1821-1841 / :2009-2020) ═══
  have haz1 : azim 0 (v p) (v (p + 1)) (v (p + 3)) = dihV 0 (v p) (v (p + 1)) (v (p + 3)) :=
    AZIM_DIHV_SAME_STRONG hnc1 hnc3 (hangLe p)
  have hle2 : azim 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) ≤ Real.pi := by
    have h1 := hangLe (p + 2)
    rw [show (p + 2) + 1 = p + 3 by omega, show (p + 2) + 3 = p + 5 by omega,
      show p + 5 = (p + 1) + 4 by omega, hper (p + 1)] at h1
    exact h1
  have haz2 : azim 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) =
      dihV 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) :=
    AZIM_DIHV_SAME_STRONG hnc23 hnc21 hle2
  exact
    { gen := hgen, bbs := hBB, per := hper, pa4 := hpa4, pb4 := hpb4, rho := hrho
      ia := hia, angLe := hangLe, iaLt := hiaLt, ns0 := hns0, ns2 := hns2, ns3 := hns3
      ns4 := hns4, ns6 := hns6, diagLt := hdiagLt, diag3 := hdiag3, diagB := hdiagB
      diagP1P3 := hdiagP1P3, valLt := hvalLt, b01 := hb01, a30 := ha30', b30 := hb30
      a34 := ha34, b34 := hb34, a14 := ha14, b14 := hb14, mem3 := hmem3, wk := hwk
      nc1 := hnc1, nc3 := hnc3, nc23 := hnc23, nc21 := hnc21, az1 := haz1, az2 := haz2 }

/-- HOL `PWEIWBZ` (VASYYAU.hl:1126-2348), `str (p+1)` branch, `a(p+3)p ≠ 2` and
`a(p+1)(p+2) = &2` with the `dist(v(p+3),v(p+4)) = 2*h0` label (VASYYAU.hl:1955-2037):
`LEMMA_PWE2 @ p+1` + `CUXVZOZ @ p`. -/
private theorem pweiwbz_C_a12eq2 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (ha01 : s.a p (p + 1) = 2) (hstr1 : scsIsStr s v (p + 1))
    (hn1 : norm (v (p + 1)) = 2) (ha30 : s.a (p + 3) p ≠ 2)
    (ha12 : s.a (p + 1) (p + 2) = 2)
    (hd34 : dist (v (p + 3)) (v (p + 4)) ≤ 2 * h0) :
    dist (v p) (v (p + 1)) = 2 := by
  let FF : Set (V3 × V3) := Set.range fun i => (v i, v (i + 1))
  have hFF : Set.range (fun i => (v i, v (i + 1))) = FF := rfl
  let P := pweiwbz_Cprep2 h s v p his hb hk hv hdiag hval ha01 hstr1 ha30
  have hia : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) = interiorAngle1 0 FF (v j) := by
    intro j
    simpa only [hFF] using P.ia j
  -- ═══ A. `LEMMA_PWE2 @ p+1`: the `dihV` bound at `v p` (HOL :1967-1973) ═══
  have hPWE := LEMMA_PWE2_p23 h s v (p + 1) his hb hk hv hdiag hval P.gen
    (by simpa only [show (p + 1) + 1 = p + 2 by omega] using P.ns2)
    (by simpa only [show (p + 1) + 3 = p + 4 by omega] using P.ns4)
    hstr1 hn1
    (by simpa only [show (p + 1) + 1 = p + 2 by omega] using ha12)
    (by simpa only [show (p + 1) + 3 = p + 4 by omega] using
      (((P.pa4 p (p + 1)).1).trans ha01))
    (by simpa only [show (p + 1) + 2 = p + 3 by omega,
      show (p + 1) + 3 = p + 4 by omega] using hd34)
  have hPWE' : Real.pi / 2 < dihV 0 (v p) (v (p + 1)) (v (p + 3)) := by
    simpa only [show (p + 1) + 1 = p + 2 by omega, show (p + 1) + 2 = p + 3 by omega,
      show (p + 1) + 3 = p + 4 by omega, P.per p] using hPWE
  -- ═══ B. the `hcase` of `CUXVZOZ @ p` (HOL :2007-2020) ═══
  have hcase1 : Real.pi / 2 < interiorAngle1 0 FF (v p) ∨
      interiorAngle1 0 FF (v (p + 1)) < Real.pi := Or.inl (by
    rw [← hia p, P.az1]
    exact hPWE')
  have hang : interiorAngle1 0 FF (v p) < Real.pi := by
    simpa only [hFF] using P.iaLt p P.ns0
  -- ═══ C. the diagonal data of `CUXVZOZ @ p` ═══
  have hd : 3 ≤ dist (v (p + (4 - 1))) (v (p + 1)) := by
    rw [dist_comm]
    exact P.diag3 (p + 1) (p + 3) P.diagP1P3
  have h2 : 2 ≤ dist (v (p + 3)) (v p) := by
    have hle := (P.bbs.2.2.1 (p + 3) p).1
    rw [P.a30] at hle
    linarith [show (2 : ℝ) ≤ 2 * h0 by norm_num [h0]]
  have hdc : dist (v (p + 3)) (v p) ≤ cstab := by
    have hle := (P.bbs.2.2.1 (p + 3) p).2
    rw [P.b30] at hle
    exact hle
  -- ═══ D. `CUXVZOZ @ p` lands on the goal ═══
  exact CUXVZOZ_p21 h s FF 4 p v hFF.symm his hk.symm (by norm_num) hv hb P.gen hd
    (fun i j hdij _ => P.diagLt i j hdij) P.diagB hang hcase1 ha01 (le_of_eq P.b01) h2 hdc

/-- HOL `PWEIWBZ` (VASYYAU.hl:1126-2348), `str (p+1)` branch, `a(p+3)p ≠ 2` and
`a(p+1)(p+2) = &2` with the `dist(v(p+2),v(p+3)) ≤ 2*h0` label
(VASYYAU.hl:2040-2196, both the `2` and the `2*h0` labels):
`LEMMA_PWE1 @ p+1` + `CJBDXXN @ p+2` + `CQAOQLR @ p`. -/
private theorem pweiwbz_C_a23le (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (ha01 : s.a p (p + 1) = 2) (hstr1 : scsIsStr s v (p + 1))
    (hn1 : norm (v (p + 1)) = 2) (ha30 : s.a (p + 3) p ≠ 2)
    (ha12 : s.a (p + 1) (p + 2) = 2)
    (hd23 : dist (v (p + 2)) (v (p + 3)) ≤ 2 * h0) :
    dist (v p) (v (p + 1)) = 2 := by
  let FF : Set (V3 × V3) := Set.range fun i => (v i, v (i + 1))
  have hFF : Set.range (fun i => (v i, v (i + 1))) = FF := rfl
  let P := pweiwbz_Cprep2 h s v p his hb hk hv hdiag hval ha01 hstr1 ha30
  have his' : isScsV39 s := his
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsym, -, -, -, -, -, -, -, -⟩ := his'
  have hia : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) = interiorAngle1 0 FF (v j) := by
    intro j
    simpa only [hFF] using P.ia j
  -- ═══ A. `LEMMA_PWE1 @ p+1`: the `dihV` bound at `v(p+2)` (HOL :2043-2049) ═══
  have hPWE := LEMMA_PWE1_p23 h s v (p + 1) his hb hk hv hdiag hval P.gen
    (by simpa only [show (p + 1) + 1 = p + 2 by omega] using P.ns2)
    (by simpa only [show (p + 1) + 3 = p + 4 by omega] using P.ns4)
    hstr1 hn1
    (by simpa only [show (p + 1) + 1 = p + 2 by omega] using ha12)
    (by simpa only [show (p + 1) + 3 = p + 4 by omega] using
      (((P.pa4 p (p + 1)).1).trans ha01))
    (by simpa only [show (p + 1) + 1 = p + 2 by omega,
      show (p + 1) + 2 = p + 3 by omega] using hd23)
  have hPWE' : Real.pi / 2 < dihV 0 (v (p + 2)) (v (p + 3)) (v (p + 1)) := by
    simpa only [show (p + 1) + 1 = p + 2 by omega,
      show (p + 1) + 2 = p + 3 by omega] using hPWE
  -- ═══ B. the `hcase` of `CJBDXXN @ p+2` (HOL :2100-2106) ═══
  have hcase2 : Real.pi / 2 < interiorAngle1 0 FF (v (p + 2)) ∨
      interiorAngle1 0 FF (v (p + 5)) < Real.pi := Or.inl (by
    rw [← hia (p + 2)]
    rw [show (p + 2) + 1 = p + 3 by omega, show (p + 2) + 3 = p + 5 by omega,
      show p + 5 = (p + 1) + 4 by omega, P.per (p + 1), P.az2]
    exact hPWE')
  have hang : interiorAngle1 0 FF (v (p + 2)) < Real.pi := by
    simpa only [hFF] using P.iaLt (p + 2) P.ns2
  -- ═══ C. the diagonal/value data of `CJBDXXN @ p+2` ═══
  have hd : 3 ≤ dist (v ((p + 2) + 1)) (v ((p + 2) + (4 - 1))) := by
    rw [show (p + 2) + 1 = p + 3 by omega, show (p + 2) + (4 - 1) = p + 5 by omega,
      show p + 5 = (p + 1) + 4 by omega, P.per (p + 1), dist_comm]
    exact P.diag3 (p + 1) (p + 3) P.diagP1P3
  have ha25 : s.a (p + 2) (p + 5) = 2 :=
    ((P.pa4 (p + 2) (p + 1)).2).trans (((hsym (p + 2) (p + 1)).1).trans ha12)
  have hb25 : s.b (p + 2) (p + 5) ≤ 2 * h0 := by
    have h : s.b (p + 2) (p + 5) = 2 * h0 :=
      ((P.pb4 (p + 2) (p + 1)).2).trans
        (((hsym (p + 2) (p + 1)).2.2.2.1).trans (A_EQ2_IMP_B_p25 s (p + 1) hval ha12))
    exact le_of_eq h
  have h2 : 2 ≤ dist (v (p + 3)) (v (p + 2)) := by
    rw [dist_comm]
    have hle := (P.bbs.2.2.1 (p + 2) (p + 3)).1
    rcases hval (p + 2) with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1] at hle; linarith
    · rw [h1] at hle
      linarith [show (2 : ℝ) ≤ 2 * h0 by norm_num [h0]]
  have hdc : dist (v (p + 3)) (v (p + 2)) ≤ cstab := by
    rw [dist_comm]
    have hle := (P.bbs.2.2.1 (p + 2) (p + 3)).2
    rcases hval (p + 2) with ⟨-, h1⟩ | ⟨-, h1⟩
    · rw [h1] at hle
      linarith [show (2 : ℝ) * h0 ≤ cstab by norm_num [h0, cstab]]
    · rw [h1] at hle
      exact hle
  -- ═══ D. `CJBDXXN @ p+2`: `dist(v(p+2),v(p+5)) = 2` (HOL :2050-2067) ═══
  have hCJ := CJBDXXN_p21 h s FF 4 (p + 2) v hFF.symm his hk.symm (by norm_num) hv hb
    P.gen hd (fun i j hdij _ => P.diagLt i j hdij) P.diagB hang hcase2 ha25 hb25 h2 hdc
  have hgoal : dist (v (p + 2)) (v (p + 5)) = 2 := by
    simpa only [show (p + 2) + (4 - 1) = p + 5 by omega] using hCJ
  -- ═══ E. `CQAOQLR @ p` transports it to the goal (HOL :2109-2116) ═══
  have hif := CQAOQLR_p16 h s v p (by rw [hk]; norm_num) his hv P.gen hb
    (fun i j hdij => hdiag i j (by rw [hk] at hdij; exact hdij))
    (by rw [P.b01]; norm_num [h0])
    (by rw [A_EQ2_IMP_B_p25 s (p + 1) hval ha12]; norm_num [h0])
    (P.valLt (p + 2))
    (by
      rw [show p + s.k - 1 = p + 3 by rw [hk]; omega, P.a30, P.b30]
      norm_num [h0, cstab])
    ha01 (le_of_eq P.b01) ha12 (le_of_eq (A_EQ2_IMP_B_p25 s (p + 1) hval ha12))
  have hd12 : dist (v (p + 1)) (v (p + 2)) = 2 := by
    rw [dist_comm, ← P.per (p + 1)]
    exact hgoal
  exact hif.mpr hd12

/-- HOL `PWEIWBZ` (VASYYAU.hl:1126-2348), `str (p+1)` branch, `a(p+3)p ≠ 2`,
`a(p+1)(p+2) = &2`: the whole HOL `:1955-2116` block, i.e. the `a12 = 2`
leaf dispatched by `TUAPYYU @ p+3` (`:1958-1960`) and by
`TUAPYYU @ p+2` together with `WKZZEEH @ p+3` (`:2030-2037`):

* `dist(v(p+3),v(p+4)) = 2*h0` → `pweiwbz_C_a12eq2` (`PWE2` + `CUXVZOZ`);
* `dist(v(p+3),v(p+4)) = cstab` → `WKZZEEH @ p+3` rules out
  `dist(v(p+2),v(p+3)) = cstab` and `TUAPYYU @ p+2` then gives
  `dist(v(p+2),v(p+3)) ≤ 2*h0`, so `pweiwbz_C_a23le` applies
  (`PWE1` + `CJBDXXN` + `CQAOQLR`). -/
private theorem pweiwbz_C_a12 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (ha01 : s.a p (p + 1) = 2) (hstr1 : scsIsStr s v (p + 1))
    (hn1 : norm (v (p + 1)) = 2) (ha30 : s.a (p + 3) p ≠ 2)
    (ha12 : s.a (p + 1) (p + 2) = 2) :
    dist (v p) (v (p + 1)) = 2 := by
  let P := pweiwbz_Cprep2 h s v p his hb hk hv hdiag hval ha01 hstr1 ha30
  by_cases h34 : dist (v (p + 3)) (v (p + 4)) = cstab
  · -- ═══ `dist(p+3,p+4) = cstab`: `WKZZEEH @ p+3` + `TUAPYYU @ p+2` ═══
    have h23ne : dist (v (p + 2)) (v (p + 3)) ≠ cstab := fun hc => P.wk ⟨hc, h34⟩
    have hTU := TUAPYYU_kit h s v (p + 2) his hb hk hv hdiag hval P.ns2 P.ns3
    have hd23 : dist (v (p + 2)) (v (p + 3)) ≤ 2 * h0 := by
      rcases hTU with he | he
      · rw [show (p + 2) + 1 = p + 3 by omega] at he
        rcases hval (p + 2) with ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [he, h1]; norm_num [h0]
        · rw [he, h1]
      · rw [show (p + 2) + 1 = p + 3 by omega] at he
        rcases hval (p + 2) with ⟨-, h1⟩ | ⟨-, h1⟩
        · rw [he, h1]
        · exact absurd (he.trans h1) h23ne
    exact pweiwbz_C_a23le h s v p his hb hk hv hdiag hval ha01 hstr1 hn1 ha30 ha12 hd23
  · -- ═══ `dist(p+3,p+4) ≠ cstab`: `TUAPYYU @ p+3` puts it at `2*h0` ═══
    have hTU := TUAPYYU_kit h s v (p + 3) his hb hk hv hdiag hval P.ns3 P.ns4
    have hd34 : dist (v (p + 3)) (v (p + 4)) ≤ 2 * h0 := by
      rcases hTU with he | he
      · rw [show (p + 3) + 1 = p + 4 by omega] at he
        rw [he, P.a34]
      · rw [show (p + 3) + 1 = p + 4 by omega] at he
        exact absurd (he.trans P.b34) h34
    exact pweiwbz_C_a12eq2 h s v p his hb hk hv hdiag hval ha01 hstr1 hn1 ha30 ha12 hd34

/-- HOL `PWEIWBZ` (VASYYAU.hl:1126-2348), `str (p+1)` branch, `a(p+3)p ≠ 2` and
`a(p+1)(p+2) ≠ &2` (VASYYAU.hl:2199-2345).  Both labels of the `TUAPYYU @ p+3`
split (`dist(v(p+3),v(p+4)) = 2*h0` = `a34` and `= cstab` = `b34`, the latter
being `dist(v p,v(p+3)) = cstab` by periodicity, i.e. HOL's "CASES 0 3= cstab")
share the same prefix and are absorbed by one `rcases`:

* `A_NOT_EQ2_IMP_B @ p+1` (`:2202`) gives `a(p+1)(p+2) = 2*h0`;
* `PRO_ADD_NOT_IN_SCS_M @ p+1` (`:2203`) and the C-prep `mem3`
  (`PRO_ADD_NOT_IN_SCS_M @ p+3`) put both residues in `scsM`, so
  `B_LE_2h0_2_SCS_M_4_1 @ p` (`:2204`) gives `b(p+2)(p+3) ≤ 2*h0`,
  `B_LE_2h0_IMP_B @ p+2` (`:2205`) gives `a(p+2)(p+3) = 2`, and
  `YEBWJNG @ p+2` (`:2206`) pins `dist(v(p+2),v(p+3)) = 2`;
* `TUAPYYU @ p+3` (`:2210`) localises `dist(v(p+3),v(p+4))` to
  `{a34 = 2*h0, b34 = cstab}`; in both labels `2*h0 ≤ dist(v(p+4),v(p+3))`;
* `LEMMA_PWE4 @ p+1` (`:2216`, `ha30 = s.a (p+4) (p+1) = 2` by `a`-symmetry
  of the C-prep `a14 = s.a (p+1) (p+4) = 2`) supplies the `dihV` bound at `v p`
  that is `CUXVZOZ @ p`'s `hcase` first disjunct, and `CUXVZOZ @ p` (`:2228`)
  lands on `dist(v p,v(p+1)) = 2`. -/
private theorem pweiwbz_C_a12ne2 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (ha01 : s.a p (p + 1) = 2) (hstr1 : scsIsStr s v (p + 1))
    (hn1 : norm (v (p + 1)) = 2) (ha30 : s.a (p + 3) p ≠ 2)
    (ha12ne : s.a (p + 1) (p + 2) ≠ 2) :
    dist (v p) (v (p + 1)) = 2 := by
  let FF : Set (V3 × V3) := Set.range fun i => (v i, v (i + 1))
  have hFF : Set.range (fun i => (v i, v (i + 1))) = FF := rfl
  let P := pweiwbz_Cprep2 h s v p his hb hk hv hdiag hval ha01 hstr1 ha30
  have his' : isScsV39 s := his
  have hsym : ∀ i j : ℕ, s.a i j = s.a j i := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsym, -, -, -, -, -, -, -, -⟩ := his
    exact fun i j => (hsym i j).1
  have hia : ∀ j : ℕ, azim 0 (v j) (v (j + 1)) (v (j + 3)) = interiorAngle1 0 FF (v j) := by
    intro j
    simpa only [hFF] using P.ia j
  -- ═══ A. `a(p+1)(p+2) ≠ 2` is `2*h0`; the `(p+2,p+3)` row is `2`
  -- (HOL :2202-2208) ═══
  obtain ⟨ha12, hb12⟩ := A_NOT_EQ2_IMP_B_p25 s (p + 1) hval ha12ne
  have hmem1 : (p + 1) % 4 ∈ scsM s :=
    PRO_ADD_NOT_IN_SCS_M_p25 s (p + 1) 4 his' hk ha12
  have hsub : {((p + 1) % 4), ((p + 3) % 4)} ⊆ scsM s := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]; exact hmem1
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact P.mem3
  have hb23le : s.b (p + 2) (p + 3) ≤ 2 * h0 :=
    B_LE_2h0_2_SCS_M_4_1_p25 s his' hk hsub
  obtain ⟨ha23, hb23⟩ := B_LE_2h0_IMP_B_p25 s (p + 2) hval hb23le
  have hY2 : dist (v (p + 2)) (v (p + 3)) = 2 :=
    YEBWJNG_kit h s v (p + 2) his' hb hk hv hdiag hval P.ns2 P.ns3 ha23
  -- ═══ B. `TUAPYYU @ p+3`: both value labels give `2*h0 ≤ dist(v(p+4),v(p+3))`
  -- (HOL :2210-2214; the `b34 = cstab` label is HOL's "CASES 0 3= cstab") ═══
  have hTU := TUAPYYU_kit h s v (p + 3) his' hb hk hv hdiag hval P.ns3 P.ns4
  have hd2 : 2 * h0 ≤ dist (v (p + 4)) (v (p + 3)) := by
    rcases hTU with he | he
    · rw [show (p + 3) + 1 = p + 4 by omega] at he
      rw [dist_comm (v (p + 4)) (v (p + 3)), he, P.a34]
    · rw [show (p + 3) + 1 = p + 4 by omega] at he
      rw [dist_comm (v (p + 4)) (v (p + 3)), he, P.b34]
      norm_num [h0, cstab]
  -- ═══ C. the `(p+4,p+1)` edge is `2` (`a`-symmetry of the C-prep `a14`,
  -- HOL :2216 `CHANGE_A_SCS_MOD` + `MOD_SUC_MOD`) ═══
  have ha30' : s.a (p + 4) (p + 1) = 2 := (hsym (p + 4) (p + 1)).trans P.a14
  -- ═══ D. `LEMMA_PWE4 @ p+1`: the `dihV` bound at `v p` (HOL :2216-2226) ═══
  have hPWE := LEMMA_PWE4_p23 h s v (p + 1) his hb hk hv hdiag hval P.gen
    (by simpa only [show (p + 1) + 1 = p + 2 by omega] using P.ns2)
    (by simpa only [show (p + 1) + 3 = p + 4 by omega] using P.ns4)
    hstr1 hn1
    (by simpa only [show (p + 1) + 3 = p + 4 by omega] using ha30')
    (by simpa only [show (p + 1) + 1 = p + 2 by omega] using ha12)
    (by
      rw [show (p + 1) + 2 = p + 3 by omega, show (p + 1) + 1 = p + 2 by omega,
        dist_comm (v (p + 3)) (v (p + 2))]
      exact hY2)
    (by simpa only [show (p + 1) + 3 = p + 4 by omega,
      show (p + 1) + 2 = p + 3 by omega] using hd2)
  have hPWE' : Real.pi / 2 < dihV 0 (v p) (v (p + 1)) (v (p + 3)) := by
    simpa only [show (p + 1) + 3 = p + 4 by omega, show (p + 1) + 2 = p + 3 by omega,
      P.per p] using hPWE
  -- ═══ E. the `hcase` of `CUXVZOZ @ p` (HOL :2264-2278) ═══
  have hcase1 : Real.pi / 2 < interiorAngle1 0 FF (v p) ∨
      interiorAngle1 0 FF (v (p + 1)) < Real.pi := Or.inl (by
    rw [← hia p, P.az1]
    exact hPWE')
  have hang : interiorAngle1 0 FF (v p) < Real.pi := by
    simpa only [hFF] using P.iaLt p P.ns0
  -- ═══ F. the diagonal data of `CUXVZOZ @ p` ═══
  have hd : 3 ≤ dist (v (p + (4 - 1))) (v (p + 1)) := by
    rw [dist_comm]
    exact P.diag3 (p + 1) (p + 3) P.diagP1P3
  have h2 : 2 ≤ dist (v (p + 3)) (v p) := by
    have hle := (P.bbs.2.2.1 (p + 3) p).1
    rw [P.a30] at hle
    linarith [show (2 : ℝ) ≤ 2 * h0 by norm_num [h0]]
  have hdc : dist (v (p + 3)) (v p) ≤ cstab := by
    have hle := (P.bbs.2.2.1 (p + 3) p).2
    rw [P.b30] at hle
    exact hle
  -- ═══ G. `CUXVZOZ @ p` lands on the goal (HOL :2228-2241) ═══
  exact CUXVZOZ_p21 h s FF 4 p v hFF.symm his hk.symm (by norm_num) hv hb P.gen hd
    (fun i j hdij _ => P.diagLt i j hdij) P.diagB hang hcase1 ha01 (le_of_eq P.b01) h2 hdc

end Kepler.Text
