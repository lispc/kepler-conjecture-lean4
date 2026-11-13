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

end Kepler.Text
