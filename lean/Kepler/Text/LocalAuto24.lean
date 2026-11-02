/-
LocalAuto24: port of three appendix modules bridging the Local Fan chapter:

  - `scripts/local/WKEIDFT.hl` (834 lines, 20 declarations): the
    diagonal-stabilisation equidecomposition of the appendix. The ℤ/k
    arithmetic kit (`SUR_MOD_FUN`, `TRANS_DIAG` ×2, `scs_components`,
    `scs_inj`, `DIAG_PSORT1`/`DIAG_PSORT2`/`DIAG_PSORT`,
    `A_EQ_PSORT`, `B_EQ_PSORT`, `PROPERTY_OF_K_SCS`) is re-exported as
    `_p24` one-line twins from the PROVED `_p17` copies in
    `Kepler.Text.LocalAuto17`; `SCS_K_D_A_STAB_EQ` likewise from
    `Kepler.Text.LocalAuto20`; `WKEIDFT_concl` (the LocalAuto1 corpus
    form of HOL `WKEIDFT.hl:570/:793`) is re-exported unchanged (FILE MAP
    note: since SF-85 it carries the four guards of the verbatim v1, with
    `b1` bound explicitly; it is no longer the light appendix variant).
    The seven genuine conclusions `WKEIDFT_A`/`WKEIDFT_B` (diagonal data),
    `WKEIDFT_EQU` (prop-eq witness), `WKEIDFT_A_V2`/`WKEIDFT_B_V2`
    (stabilised, `(i+p) MOD k = p' MOD k`), `WKEIDFT_EQU_V2` and the arrow
    `WKEIDFT` are stated verbatim and `sorry`.
  - `scripts/local/OTMTOTJ.hl` (1542 lines, 47 theorems): the pentagonal
    ear-arrow chain. The four master arrows `OTMTOTJ1-4`
    (OTMTOTJ.hl:1156/1169/1500/1520) are restated verbatim in Section B6
    (skeleton restatements, 2026-09-21 — previously only the LocalAuto1
    `OTMTOTJ1-4_concl` copies existed, OTMTOTJ.hl:1156/1169/1500/1520);
    the remaining `44-4` statements are restated, with the
    mechanical `DIAG_5_EQU_PSORT`, `DIAG_EQ_ADD5` and the four
    `SET_STAB_5I1/5I2/5I3/5M1` set identities PROVED (over the PROVED
    `STAB_MOD`/`DIAG_MOD`/`SCS_*_IS_SCS` of LocalAuto20) and the rest
    `sorry` with `-- DISCHARGES:` markers.
  - `scripts/local/UXCKFPE.hl` (2648 lines, 2 defs + 20 theorems): the
    `k = 3` `tri_sy` capstone and the case-4/5/6 nonempty witnesses.
    `J1_TS` (def), `d_fun3` (def) and the 20 conclusions are stated over
    the `_p23` stable-system kit (LocalAuto23); `FINITE_J1_TS`,
    `tri_sy_explicit` and the case assembly `UXCKFPE` are PROVED, the
    rest `sorry`.

Encoding (house conventions):
- `_p24` suffix on every re-export twin (the underlying PROVED theorem is
  cited in the docstring; no re-proving).
- New (no-collision) statements keep the bare HOL names.
- `sorry` bodies carry `-- DISCHARGES:` naming the missing HOL inputs.
- No `native_decide`. `interval_cases`/`omega` for the finite-mod proofs.
- Same-wave files LocalAuto25/26 are NOT imported (19/21-22/27 unused).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto17
import Kepler.Text.LocalAuto20
import Kepler.Text.LocalAuto23
-- sweep-b24-w2: the SET_EQ diagonal-class transfer kit consumes the
-- LocalAuto12 propEqu transfer and the FanBaseKit opposite bridge
-- (both import-acyclic w.r.t. LocalAuto24).
import Kepler.Text.LocalAuto12
import Kepler.Text.FanBaseKit
-- casebank-close-w1 kit: the PROVED LA36 fan bridge
-- (`convexLocalFan_p4_of_ConvexLocalFan_p36`) + the LA36 prereq cores
-- (`inNotEmpty_core_p36` / `inB1_core_p36`); acyclic (LA36 imports LA23, no LA24).
import Kepler.Text.LocalAuto36
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section A: WKEIDFT.hl — diagonal-stabilisation equidecomposition -/

/-! ### A0. Re-export twins (PROVED in LocalAuto17/20/1) -/

/-- HOL `SUR_MOD_FUN` (WKEIDFT.hl:92). Re-export of the PROVED LocalAuto17
twin. -/
theorem SUR_MOD_FUN_p24 (k p p' : ℕ) (hk : k ≠ 0) :
    ∃ i : ℕ, (i + p) % k = p' % k :=
  SUR_MOD_FUN_p17 k p p' hk

/-- HOL `TRANS_DIAG` (WKEIDFT.hl:113, num version). Re-export of the PROVED
LocalAuto17 twin. -/
theorem TRANS_DIAG_MOD_p24 (k i p p' q q' : ℕ) (hk : k ≠ 0)
    (h1 : (i + p) % k = p' % k) (h2 : p' + q = p + q') :
    (i + q) % k = q' % k :=
  TRANS_DIAG_p17 k i p p' q q' hk h1 h2

/-- HOL `scs_components` (WKEIDFT.hl:130). Re-export of the PROVED
LocalAuto1/17 twin. -/
theorem scs_components_p24 (s : ScsV39) :
    ScsV39.mk s.k s.d s.a s.am s.bm s.b s.J s.lo s.hi s.str = s :=
  scs_components_p17 s

/-- HOL `scs_inj` (WKEIDFT.hl:146). Re-export of the PROVED LocalAuto1/17
twin. -/
theorem scs_inj_p24 (s s' : ScsV39) (h1 : scsBasicV39 s) (h1' : scsBasicV39 s')
    (hd : s.d = s'.d) (hk : s.k = s'.k) (ha : s.a = s'.a) (hb : s.b = s'.b) :
    s = s' :=
  scs_inj_p17 s s' h1 h1' hd hk ha hb

/-- HOL `DIAG_PSORT1` (WKEIDFT.hl:173). Re-export of the PROVED LocalAuto17
twin. -/
theorem DIAG_PSORT1_p24 (k i p i' j q' q : ℕ) (hk : k ≠ 0)
    (h1 : (i + p) % k = p' % k) (h2 : p' + q = p + q')
    (h3 : psort k (i', j) = psort k (p, q)) :
    psort k (i + i', i + j) = psort k (p', q') :=
  DIAG_PSORT1_p17 k i p i' j q' q hk h1 h2 h3

/-- HOL `DIAG_PSORT2` (WKEIDFT.hl:235). Re-export of the PROVED LocalAuto17
twin. -/
theorem DIAG_PSORT2_p24 (k i p i' j q' q : ℕ) (hk : k ≠ 0)
    (h1 : (i + p) % k = p' % k) (h2 : p' + q = p + q')
    (h3 : psort k (i + i', i + j) = psort k (p', q')) :
    psort k (i', j) = psort k (p, q) :=
  DIAG_PSORT2_p17 k i p i' j q' q hk h1 h2 h3

/-- HOL `DIAG_PSORT` (WKEIDFT.hl:297). Re-export of the PROVED LocalAuto17
twin. -/
theorem DIAG_PSORT_p24 (k i p i' j q' q : ℕ) (hk : k ≠ 0)
    (h1 : (i + p) % k = p' % k) (h2 : p' + q = p + q') :
    (psort k (i + i', i + j) = psort k (p', q')) ↔
      (psort k (i', j) = psort k (p, q)) :=
  DIAG_PSORT_p17 k i p i' j q' q hk h1 h2

/-- HOL `TRANS_DIAG` (WKEIDFT.hl:313, scs_diag version). Re-export of the
PROVED LocalAuto17 twin. -/
theorem TRANS_DIAG_SCS_DIAG_p24 (k i' i j : ℕ) (hk : k ≠ 0) :
    scsDiag k i' j ↔ scsDiag k (i + i') (i + j) :=
  TRANS_DIAG_SCS_p17 k i' i j hk

/-- HOL `A_EQ_PSORT` (WKEIDFT.hl:319). Re-export of the PROVED LocalAuto17
twin. -/
theorem A_EQ_PSORT_p24 (s : ScsV39) (i j p q : ℕ) (his : isScsV39 s)
    (h : psort s.k (i, j) = psort s.k (p, q)) : s.a i j = s.a p q :=
  A_EQ_PSORT_p17 s i j p q his h

/-- HOL `B_EQ_PSORT` (WKEIDFT.hl:339). Re-export of the PROVED LocalAuto17
twin. -/
theorem B_EQ_PSORT_p24 (s : ScsV39) (i j p q : ℕ) (his : isScsV39 s)
    (h : psort s.k (i, j) = psort s.k (p, q)) : s.b i j = s.b p q :=
  B_EQ_PSORT_p17 s i j p q his h

/-- HOL `PROPERTY_OF_K_SCS` (WKEIDFT.hl:358). Re-export of the PROVED
LocalAuto17 twin. -/
theorem PROPERTY_OF_K_SCS_p24 (s : ScsV39) (his : isScsV39 s) :
    s.k ≠ 0 ∧ 0 < s.k ∧ 1 < s.k ∧ 2 < s.k :=
  PROPERTY_OF_K_SCS_p17 s his

/-- HOL `SCS_K_D_A_STAB_EQ` (the local variant of hexagons.hl:1084,
appendix WKEIDFT.hl:745). Re-export of the PROVED LocalAuto20 twin. -/
theorem SCS_K_D_A_STAB_EQ_p24 (s : ScsV39) (i j : ℕ) :
    (scsStabDiagV39 s i j).d = s.d ∧ (scsStabDiagV39 s i j).k = s.k ∧
      ∀ i' j', (scsStabDiagV39 s i j).a i' j' = s.a i' j' :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- HOL `WKEIDFT_concl` (WKEIDFT.hl:793 corpus form, via LocalAuto1).
Re-export unchanged. FIDELITY fix (SF-85): the corpus guards `scsDiag s.k
p q`, `scsDiag s.k p' q'`, `3 < s.k`, `∀ i, s.b i i = b1` (with `b1 : ℝ` an
explicit binder) now ride on the delegated statement. The verbatim HOL v1
(`WKEIDFT.hl:570`) `scs_arrow {s} {s'}` statement is covered by `WKEIDFT`
below in its v2 stabilised form. -/
theorem WKEIDFT_concl_p24 : ∀ (s : ScsV39) (a b a' b' b1 : ℝ) (p q p' q' : ℕ),
    isScsV39 s → scsBasicV39 s →
    (∀ i, s.a i (i + 1) = a) → (∀ i, s.b i (i + 1) = b) → p' + q = p + q' →
    scsDiag s.k p q → scsDiag s.k p' q' → 3 < s.k →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab) →
    (∀ i j, scsDiag s.k i j → s.a i j = a') →
    (∀ i j, scsDiag s.k i j → s.b i j = b') →
    (∀ i, s.b i i = b1) →
    scsArrowV39 {scsStabDiagV39 s p q} {scsStabDiagV39 s p' q'} :=
  WKEIDFT_concl

/-! ### A1. The seven genuine conclusions (sorried) -/

/-- HOL `WKEIDFT_A` (WKEIDFT.hl:384): the `a`-entry of `s'` is the
`i`-cyclic shift of that of `s` on the diagonal data. -/
theorem WKEIDFT_A (s s' : ScsV39) (a b a' b' : ℝ) (p q p' q' : ℕ) (i : ℕ)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hbs : scsBasicV39 s)
    (hbs' : scsBasicV39 s')
    (has : ∀ i : ℕ, s.a i (i + 1) = a) (hbs1 : ∀ i : ℕ, s.b i (i + 1) = b)
    (has' : ∀ i : ℕ, s'.a i (i + 1) = a) (hbs1' : ∀ i : ℕ, s'.b i (i + 1) = b)
    (hk : s'.k = s.k) (hsum : p' + q = p + q') (hd : s.d = s'.d)
    (ha1 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p, q) →
      s.a i j = a')
    (hb1 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p, q) →
      s.b i j = b')
    (ha2 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p', q') →
      s'.a i j = a')
    (hb2 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p', q') →
      s'.b i j = b')
    (ha0 : s.a p q = s'.a p' q') (hb0 : s.b p q = s'.b p' q')
    (hpq : (i + p) % s.k = p' % s.k) :
    (fun j j' => s'.a (i + j) (i + j')) = s.a := by
  sorry
  -- DISCHARGES: PROPERTY_OF_K_SCS, DIAG_PSORT, TRANS_DIAG,
  -- A_EQ_PSORT, CHANGE_A_SCS_MOD, YRTAFYH.A (K_%k arithmetic).

/-- HOL `WKEIDFT_B` (WKEIDFT.hl:469): the `b`-entry twin of `WKEIDFT_A`. -/
theorem WKEIDFT_B (s s' : ScsV39) (a b a' b' : ℝ) (p q p' q' : ℕ) (a1 : ℝ)
    (i : ℕ)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hbs : scsBasicV39 s)
    (hbs' : scsBasicV39 s')
    (hbsa1 : ∀ i : ℕ, s.b i i = a1) (hbsa1' : ∀ i : ℕ, s'.b i i = a1)
    (has : ∀ i : ℕ, s.a i (i + 1) = a) (hbs1 : ∀ i : ℕ, s.b i (i + 1) = b)
    (has' : ∀ i : ℕ, s'.a i (i + 1) = a) (hbs1' : ∀ i : ℕ, s'.b i (i + 1) = b)
    (hk : s'.k = s.k) (hsum : p' + q = p + q') (hd : s.d = s'.d)
    (ha1 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p, q) →
      s.a i j = a')
    (hb1 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p, q) →
      s.b i j = b')
    (ha2 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p', q') →
      s'.a i j = a')
    (hb2 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p', q') →
      s'.b i j = b')
    (ha0 : s.a p q = s'.a p' q') (hb0 : s.b p q = s'.b p' q')
    (hpq : (i + p) % s.k = p' % s.k) :
    (fun j j' => s'.b (i + j) (i + j')) = s.b := by
  sorry
  -- DISCHARGES: PROPERTY_OF_K_SCS, DIAG_PSORT, TRANS_DIAG,
  -- B_EQ_PSORT, CHANGE_B_SCS_MOD, YRTAFYH.B.

/-- HOL `WKEIDFT_EQU` (WKEIDFT.hl:554): equal diagonal data give `s'` as a
`scs_prop_equ_v39` shift of `s`. -/
theorem WKEIDFT_EQU (s s' : ScsV39) (a b a' b' : ℝ) (p q p' q' : ℕ) (a1 : ℝ)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hbs : scsBasicV39 s)
    (hbs' : scsBasicV39 s')
    (hbsa1 : ∀ i : ℕ, s.b i i = a1) (hbsa1' : ∀ i : ℕ, s'.b i i = a1)
    (has : ∀ i : ℕ, s.a i (i + 1) = a) (hbs1 : ∀ i : ℕ, s.b i (i + 1) = b)
    (has' : ∀ i : ℕ, s'.a i (i + 1) = a) (hbs1' : ∀ i : ℕ, s'.b i (i + 1) = b)
    (hk : s'.k = s.k) (hsum : p' + q = p + q') (hd : s.d = s'.d)
    (ha1 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p, q) →
      s.a i j = a')
    (hb1 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p, q) →
      s.b i j = b')
    (ha2 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p', q') →
      s'.a i j = a')
    (hb2 : ∀ i j : ℕ, scsDiag s.k i j → ¬ psort s.k (i, j) = psort s.k (p', q') →
      s'.b i j = b')
    (ha0 : s.a p q = s'.a p' q') (hb0 : s.b p q = s'.b p' q') :
    ∃ i : ℕ, s' = scsPropEquV39 s i := by
  sorry
  -- DISCHARGES: WKEIDFT_A, WKEIDFT_B, YRTAFYH.EQU (scs_inj on the shifted
  -- entries).

/-- HOL `WKEIDFT_A_V2` (WKEIDFT.hl:701): the stabilised `a`-shift. -/
theorem WKEIDFT_A_V2 (s : ScsV39) (a b a' b' : ℝ) (p q p' q' : ℕ) (b1 : ℝ)
    (i : ℕ)
    (hs : isScsV39 s) (hbs : scsBasicV39 s)
    (has : ∀ i : ℕ, s.a i (i + 1) = a) (hbs1 : ∀ i : ℕ, s.b i (i + 1) = b)
    (hsum : p' + q = p + q') (hpq : scsDiag s.k p q) (hpq' : scsDiag s.k p' q')
    (hac : ∀ i j : ℕ, scsDiag s.k i j → s.a i j ≤ cstab)
    (ha1 : ∀ i j : ℕ, scsDiag s.k i j → s.a i j = a')
    (hb1 : ∀ i j : ℕ, scsDiag s.k i j → s.b i j = b')
    (hb1' : ∀ i : ℕ, s.b i i = b1)
    (hpqs : (i + p) % s.k = p' % s.k) :
    (fun j j' => (scsStabDiagV39 s p' q').a (i + j) (i + j')) =
      (scsStabDiagV39 s p q).a := by
  sorry
  -- DISCHARGES: DIAG_PSORT, TRANS_DIAG, A_EQ_PSORT, CHANGE_A_SCS_MOD,
  -- YRTAFYH on the stabilised diagonal (`a <= cstab` admits it).

/-- HOL `WKEIDFT_B_V2` (WKEIDFT.hl:620): the stabilised `b`-shift. -/
theorem WKEIDFT_B_V2 (s : ScsV39) (a b a' b' : ℝ) (p q p' q' : ℕ) (b1 : ℝ)
    (i : ℕ)
    (hs : isScsV39 s) (hbs : scsBasicV39 s)
    (has : ∀ i : ℕ, s.a i (i + 1) = a) (hbs1 : ∀ i : ℕ, s.b i (i + 1) = b)
    (hsum : p' + q = p + q') (hpq : scsDiag s.k p q) (hpq' : scsDiag s.k p' q')
    (hac : ∀ i j : ℕ, scsDiag s.k i j → s.a i j ≤ cstab)
    (ha1 : ∀ i j : ℕ, scsDiag s.k i j → s.a i j = a')
    (hb1 : ∀ i j : ℕ, scsDiag s.k i j → s.b i j = b')
    (hb1' : ∀ i : ℕ, s.b i i = b1)
    (hpqs : (i + p) % s.k = p' % s.k) :
    (fun j j' => (scsStabDiagV39 s p' q').b (i + j) (i + j')) =
      (scsStabDiagV39 s p q).b := by
  sorry
  -- DISCHARGES: DIAG_PSORT, TRANS_DIAG, B_EQ_PSORT, CHANGE_B_SCS_MOD,
  -- YRTAFYH on the stabilised diagonal.

/-- HOL `WKEIDFT_EQU_V2` (WKEIDFT.hl:769): the stabilised `scs_prop_equ_v39`
witness. -/
theorem WKEIDFT_EQU_V2 (s : ScsV39) (a b a' b' : ℝ) (p q p' q' : ℕ) (b1 : ℝ)
    (hs : isScsV39 s) (hbs : scsBasicV39 s)
    (has : ∀ i : ℕ, s.a i (i + 1) = a) (hbs1 : ∀ i : ℕ, s.b i (i + 1) = b)
    (hsum : p' + q = p + q') (hpq : scsDiag s.k p q) (hpq' : scsDiag s.k p' q')
    (hk3 : 3 < s.k)
    (hac : ∀ i j : ℕ, scsDiag s.k i j → s.a i j ≤ cstab)
    (ha1 : ∀ i j : ℕ, scsDiag s.k i j → s.a i j = a')
    (hb1 : ∀ i j : ℕ, scsDiag s.k i j → s.b i j = b')
    (hb1' : ∀ i : ℕ, s.b i i = b1) :
    ∃ i : ℕ, scsStabDiagV39 s p' q' = scsPropEquV39 (scsStabDiagV39 s p q) i := by
  sorry
  -- DISCHARGES: SUR_MOD_FUN, WKEIDFT_A_V2, WKEIDFT_B_V2, YRTAFYH,
  -- SCS_K_D_A_STAB_EQ (the shift witness), PROPERTY_OF_K_SCS.

/-- HOL `WKEIDFT` (WKEIDFT.hl:809): the stabilised arrow conclusion
`scs_arrow_v39 {stab s p q} {stab s p' q'}`. -/
theorem WKEIDFT (s : ScsV39) (a b a' b' : ℝ) (p q p' q' : ℕ) (b1 : ℝ)
    (hs : isScsV39 s) (hbs : scsBasicV39 s)
    (has : ∀ i : ℕ, s.a i (i + 1) = a) (hbs1 : ∀ i : ℕ, s.b i (i + 1) = b)
    (hsum : p' + q = p + q') (hpq : scsDiag s.k p q) (hpq' : scsDiag s.k p' q')
    (hk3 : 3 < s.k)
    (hac : ∀ i j : ℕ, scsDiag s.k i j → s.a i j ≤ cstab)
    (ha1 : ∀ i j : ℕ, scsDiag s.k i j → s.a i j = a')
    (hb1 : ∀ i j : ℕ, scsDiag s.k i j → s.b i j = b')
    (hb1' : ∀ i : ℕ, s.b i i = b1) :
    scsArrowV39 {scsStabDiagV39 s p q} {scsStabDiagV39 s p' q'} := by
  sorry
  -- DISCHARGES: WKEIDFT_EQU_V2, STAB_IS_SCS (LocalAuto17:1101, sorried),
  -- scs_inj, SCS_K_D_A_STAB_EQ, YRTAFYH.

/-! ## Section B: OTMTOTJ.hl — the pentagonal ear-arrow chain

FILE MAP: the four master arrows `OTMTOTJ1-4` (OTMTOTJ.hl:1156/1169/1500/1520)
are restated verbatim in Section B6 below (skeleton restatements, 2026-09-21;
before that only the LocalAuto1 `OTMTOTJ1-4_concl` copies existed);
the remaining `47-4` statements
are below. The mechanical `DIAG_5_EQU_PSORT`, `DIAG_EQ_ADD5` and the four
`SET_STAB_5I*` identities are PROVED (over the PROVED `PSORT_MOD`/`DIAG_MOD`/
`STAB_MOD`/`SCS_*_IS_SCS` of LocalAuto20); all `scs_arrow_v39`-conclusions
are sorried with their HOL `FZIOTEF`-discharge chains. -/

/-! ### B0. Diag vs psort bookkeeping -/

/-- HOL `DIAG_5_EQU_PSORT` (OTMTOTJ.hl:102). -/
theorem DIAG_5_EQU_PSORT (i j : ℕ) :
    (¬ i % 5 = j % 5 ∧ ¬ (i + 1) % 5 = j % 5 ∧ ¬ i % 5 = (j + 1) % 5) ↔
      psort 5 (i, j) = (0, 2) ∨ psort 5 (i, j) = (0, 3) ∨
        psort 5 (i, j) = (1, 3) ∨ psort 5 (i, j) = (1, 4) ∨
          psort 5 (i, j) = (2, 4) := by
  have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
  rw [show (i + 1) % 5 = (i % 5 + 1) % 5 from by omega,
      show (j + 1) % 5 = (j % 5 + 1) % 5 from by omega]
  simp only [psort]
  interval_cases i % 5 <;> interval_cases j % 5 <;> decide

/-- HOL `DIAG_EQ_ADD5` (OTMTOTJ.hl:955). -/
theorem DIAG_EQ_ADD5 (i j : ℕ) :
    scsDiag 5 (i % 5) (j % 5) ↔ i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5 := by
  have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
  interval_cases i % 5 <;> interval_cases j % 5 <;> simp [scsDiag] <;> omega

/-! ### B1. The bounded-pentagon implications (`BB`/`MM`), pentagons.hl:125-559 — the four `MM_5x_IMP_MM_5M2` arrows are relocated below the Section B7 kit in sweep-b24-w2 (statements byte-identical). -/

/-- HOL `BB_5I1_IS_BB_5M2` (OTMTOTJ.hl:125). -/
theorem BB_5I1_IS_BB_5M2 (v : ℕ → V3) (h : BBsV39 scs5I1 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  sorry
  -- DISCHARGES: pentagons.hl `SCS_TAC` case work on `scs_5I1`/`scs_5M2`.

/-- HOL `BB_5I2_IS_BB_5M2` (OTMTOTJ.hl:239). -/
theorem BB_5I2_IS_BB_5M2 (v : ℕ → V3) (h : BBsV39 scs5I2 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  sorry
  -- DISCHARGES: pentagons.hl `SCS_TAC` case work on `scs_5I2`/`scs_5M2`.

/-- HOL `BB_5I3_IS_BB_5M2` (OTMTOTJ.hl:354). -/
theorem BB_5I3_IS_BB_5M2 (v : ℕ → V3) (h : BBsV39 scs5I3 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  sorry
  -- DISCHARGES: pentagons.hl `SCS_TAC` case work on `scs_5I3`/`scs_5M2`.

/-- HOL `BB_5M1_IS_BB_5M2` (OTMTOTJ.hl:478). -/
theorem BB_5M1_IS_BB_5M2 (v : ℕ → V3) (h : BBsV39 scs5M1 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  sorry
  -- DISCHARGES: pentagons.hl `SCS_TAC` case work on `scs_5M1`/`scs_5M2`.

/-! ### B2. Diag-stabilisation of the pentagons keeps `MMs` (OTMTOTJ.hl:553-696) -/

/- `_p24` private kit for the B2/B5 discharges: the periodic-reduction and
`BBindex` bookkeeping (LocalAuto1 private twins, re-cloned for this file),
plus the generic `isScs`-of-stab verification (the concrete-system residue
route around the sorried `YRTAFYH`). -/

private theorem la24periodic_mul {α : Sort u} {f : ℕ → α} {k : ℕ} (h : Periodic f k) :
    ∀ n x, f (x + n * k) = f x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ m ih =>
      intro x
      have he : x + (m + 1) * k = (x + m * k) + k := by rw [Nat.succ_mul, Nat.add_assoc]
      rw [he, h]
      exact ih x

private theorem la24periodic_mod {α : Sort u} {f : ℕ → α} {k : ℕ} (h : Periodic f k)
    (x : ℕ) : f x = f (x % k) := by
  have hx := la24periodic_mul h (x / k) (x % k)
  have he : x % k + x / k * k = x := by rw [Nat.mul_comm]; exact Nat.mod_add_div x k
  rw [he] at hx
  exact hx

private theorem la24minNum_spec (S : Set ℕ) (hne : S.Nonempty) :
    minNum S ∈ S ∧ ∀ m ∈ S, minNum S ≤ m := by
  have hex : ∃ n : ℕ, n ∈ S ∧ ∀ m ∈ S, n ≤ m :=
    ⟨sInf S, Nat.sInf_mem hne, fun m hm => Nat.sInf_le hm⟩
  exact Classical.epsilon_spec hex

private theorem la24bbindexMin_le (s : ScsV39) {v : ℕ → V3} (hv : v ∈ BBprimeV39 s) :
    BBindexMinV39 s ≤ BBindexV39 s v := by
  have himg : (BBindexV39 s '' BBprimeV39 s).Nonempty := ⟨BBindexV39 s v, v, hv, rfl⟩
  exact (la24minNum_spec _ himg).2 _ ⟨v, hv, rfl⟩

private theorem la24bbindexMin_attained (s : ScsV39) (z : ℕ → V3)
    (hz : z ∈ BBprimeV39 s) : ∃ w, w ∈ BBprimeV39 s ∧ BBindexV39 s w = BBindexMinV39 s := by
  have himg : (BBindexV39 s '' BBprimeV39 s).Nonempty := ⟨BBindexV39 s z, z, hz, rfl⟩
  obtain ⟨hmin, -⟩ := la24minNum_spec _ himg
  obtain ⟨w, hw, hwval⟩ := hmin
  exact ⟨w, hw, hwval⟩

/-- `funlist_v39` tables are symmetric (psort-swap form, k = 5 shape). -/
private theorem la24funlist_symm5 (data : List ((ℕ × ℕ) × ℝ)) (dd : ℝ) (p q : ℕ) :
    funlistV39 data dd 5 p q = funlistV39 data dd 5 q p := by
  unfold funlistV39
  rw [psort_swap_p20 5 p q]
  by_cases h : p % 5 = q % 5
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- `csAdj 5 a1 a2` is constant `a2` on the psort-class of a diagonal pair
(both orientations; the hypothesis shape is `psort_eq_cases_p20`'s). -/
private theorem la24csAdj_far {a1 a2 : ℝ} {i j x y : ℕ} (hd : scsDiag 5 i j)
    (hxy : (i % 5 = x % 5 ∧ j % 5 = y % 5) ∨ (i % 5 = y % 5 ∧ j % 5 = x % 5)) :
    csAdj 5 a1 a2 x y = a2 := by
  obtain ⟨hd1, hd2, hd3⟩ := hd
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [csAdj, ← h1, ← h2]
    split
    · exfalso; omega
    split
    · exfalso; omega
    · rfl
  · simp only [csAdj, ← h1, ← h2]
    split
    · exfalso; omega
    split
    · exfalso; omega
    · rfl

/-- Generic `isScs_v39` of a diagonal stabilisation: everything except the
`a ≤ cstab` bound on the stabilised class is bookkeeping on the `isScsV39 s`
conjuncts (the edge slots of the override are untouched by
`diag_not_edge_psort_p20`, so the `scsM` card bound is literally unchanged) —
the concrete residue content is supplied per system by `hdom`. -/
private theorem la24isScs_stab (s : ScsV39) (i j : ℕ) (hd : scsDiag s.k i j)
    (hs : isScsV39 s)
    (hdom : ∀ u v, psort s.k (i, j) = psort s.k (u, v) → s.a u v ≤ cstab) :
    isScsV39 (scsStabDiagV39 s i j) := by
  have hk0 : s.k ≠ 0 := by have := hs.2.1; omega
  have hk2 : 1 < s.k := by have := hs.2.1; omega
  obtain ⟨hdd, hk1, hk6, -, -, -, -, hpa, -, -, hpb, -, hsym, hch, hdiag0, h2a, hb3,
    hbc, -, -, hcard⟩ := hs
  have hpb1 : ∀ u v, s.b (u + s.k) v = s.b u v := fun u v => (hpb u v).1
  have hpb2 : ∀ u v, s.b u (v + s.k) = s.b u v := fun u v => (hpb u v).2
  set b' : ℕ → ℕ → ℝ := fun x y =>
    if psort s.k (i, j) = psort s.k (x, y) then cstab else s.b x y with hb'def
  rw [show scsStabDiagV39 s i j = mkUnadornedV39 s.k s.d s.a b' from by
    simp only [scsStabDiagV39, mkUnadornedV39, hb'def]]
  simp only [isScsV39, mkUnadornedV39]
  have psort_add1 : ∀ u v : ℕ, psort s.k (u + s.k, v) = psort s.k (u, v) := by
    intro u v
    rw [(PSORT_MOD s.k (u + s.k) v hk0).symm, Nat.add_mod_right, PSORT_MOD s.k u v hk0]
  have psort_add2 : ∀ u v : ℕ, psort s.k (u, v + s.k) = psort s.k (u, v) := by
    intro u v
    rw [(PSORT_MOD s.k u (v + s.k) hk0).symm, Nat.add_mod_right, PSORT_MOD s.k u v hk0]
  have hb'edge : ∀ u, b' u (u + 1) = s.b u (u + 1) := by
    intro u
    simp only [hb'def]
    rw [if_neg (diag_not_edge_psort_p20 u hk2 hd)]
  have hsymB' : ∀ u v, b' u v = b' v u := by
    intro u v
    simp only [hb'def]
    by_cases hcls : psort s.k (i, j) = psort s.k (u, v)
    · rw [if_pos hcls, psort_swap_p20 s.k v u, if_pos hcls]
    · rw [if_neg hcls, psort_swap_p20 s.k v u, if_neg hcls]
      exact (hsym u v).2.2.2.1
  have hpb' : Periodic2 b' s.k := by
    intro u v
    refine ⟨?_, ?_⟩
    · show b' (u + s.k) v = b' u v
      simp only [hb'def]
      rw [psort_add1, hpb1 u v]
    · show b' u (v + s.k) = b' u v
      simp only [hb'def]
      rw [psort_add2, hpb2 u v]
  have hdomcase : ∀ u v, s.a u v ≤ b' u v := by
    intro u v
    by_cases hcls : psort s.k (i, j) = psort s.k (u, v)
    · simp only [hb'def, if_pos hcls]
      exact hdom u v hcls
    · simp only [hb'def, if_neg hcls]
      exact (hch u v).1.trans ((hch u v).2.1.trans (hch u v).2.2)
  refine ⟨hdd, hk1, hk6, periodic_empty s.k, periodic_empty s.k, periodic_empty s.k,
    periodic_empty s.k, hpa, hpa, hpb', hpb', fun _ _ => ⟨rfl, rfl⟩,
    fun u v => ⟨(hsym u v).1, (hsym u v).1, hsymB' u v, hsymB' u v, trivial⟩,
    fun u v => ⟨le_refl _, hdomcase u v, le_refl _⟩, hdiag0, h2a,
    fun u h3 => by rw [hb'edge u]; exact hb3 u h3,
    fun u h3 => by rw [hb'edge u]; exact hbc u h3,
    fun _ _ hj => False.elim hj, fun _ _ hj => False.elim hj, ?_⟩
  simp only [hb'edge]
  exact hcard

/-- The `MMs` transport along a diagonal stabilisation (LocalAuto1
`PEDSLGV1_concl` ported to the k = 5 mk-form systems): the `cstab` override
only shrinks the `b`-bound on the stabilised class (far constant `6` there),
the `J`-empty `dsv`s agree, and the class transports the required
`dist (v i) (v j) ≤ cstab`. -/
private theorem la24stab_mm (d : ℝ) (a b : ℕ → ℕ → ℝ)
    (v : ℕ → V3) (i j : ℕ) (hd : scsDiag 5 i j) (hle : dist (v i) (v j) ≤ cstab)
    (hv : v ∈ MMsV39 (mkUnadornedV39 5 d a b))
    (hfar : ∀ x y, psort 5 (i, j) = psort 5 (x, y) → b x y = 6) :
    v ∈ MMsV39 (scsStabDiagV39 (mkUnadornedV39 5 d a b) i j) := by
  have hunad : unadornedV39 (mkUnadornedV39 5 d a b) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [unadorned_MMs_concl _ hunad] at hv
  simp only [BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at hv
  obtain ⟨⟨hBBs, hmin, hneg⟩, hidx⟩ := hv
  obtain ⟨hBBr, hper0, hBBb, hBBf⟩ := hBBs
  have hper : Periodic v 5 := hper0
  set b' : ℕ → ℕ → ℝ := fun x y =>
    if psort 5 (i, j) = psort 5 (x, y) then cstab else b x y with hb'def
  have hS : scsStabDiagV39 (mkUnadornedV39 5 d a b) i j = mkUnadornedV39 5 d a b' := by
    simp only [scsStabDiagV39, mkUnadornedV39, hb'def]
  have hunadS : unadornedV39 (scsStabDiagV39 (mkUnadornedV39 5 d a b) i j) := by
    rw [hS]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [unadorned_MMs_concl _ hunadS, hS]
  have hclsdist : ∀ x y, psort 5 (i, j) = psort 5 (x, y) →
      dist (v x) (v y) ≤ cstab := by
    intro x y hcls
    obtain hc | hc := psort_eq_cases_p20 hcls
    · rw [la24periodic_mod hper x, la24periodic_mod hper y, ← hc.1, ← hc.2,
        ← la24periodic_mod hper i, ← la24periodic_mod hper j]
      exact hle
    · rw [la24periodic_mod hper x, la24periodic_mod hper y, ← hc.2, ← hc.1,
        ← la24periodic_mod hper j, ← la24periodic_mod hper i, dist_comm]
      exact hle
  have hdistle : ∀ x y, dist (v x) (v y) ≤ b' x y := by
    intro x y
    by_cases hcls : psort 5 (i, j) = psort 5 (x, y)
    · simp only [hb'def, if_pos hcls]
      exact hclsdist x y hcls
    · simp only [hb'def, if_neg hcls]
      exact (hBBb x y).2
  have hup : ∀ x y, b' x y ≤ b x y := by
    intro x y
    by_cases hcls : psort 5 (i, j) = psort 5 (x, y)
    · simp only [hb'def, if_pos hcls]
      rw [hfar x y hcls]
      norm_num [cstab]
    · simp only [hb'def, if_neg hcls]
      exact le_refl _
  have htau : ∀ w : ℕ → V3, taustarV39 (mkUnadornedV39 5 d a b') w
      = taustarV39 (mkUnadornedV39 5 d a b) w := by
    intro w
    simp only [taustarV39]
    rw [dsv_J_empty _ _ rfl, dsv_J_empty _ _ rfl]
    rfl
  have hBBsS : BBsV39 (mkUnadornedV39 5 d a b') v :=
    ⟨hBBr, hper, fun x y => ⟨(hBBb x y).1, hdistle x y⟩, hBBf⟩
  have hBBw : ∀ w, BBsV39 (mkUnadornedV39 5 d a b') w → BBsV39 (mkUnadornedV39 5 d a b) w := by
    intro w hw
    refine ⟨hw.1, hw.2.1,
      fun x y => ⟨(hw.2.2.1 x y).1, le_trans (hw.2.2.1 x y).2 (hup x y)⟩, hw.2.2.2⟩
  have hvBS : v ∈ BBprimeV39 (mkUnadornedV39 5 d a b') :=
    ⟨hBBsS, by
      intro w hw
      rw [htau v, htau w]
      exact hmin w (hBBw w hw),
      by rw [htau v]; exact hneg⟩
  have hle1 := la24bbindexMin_le _ hvBS
  obtain ⟨z, hz, hzval⟩ := la24bbindexMin_attained _ v hvBS
  have hzS : BBsV39 (mkUnadornedV39 5 d a b) z := hBBw z hz.1
  have htaueq : taustarV39 (mkUnadornedV39 5 d a b) z
      = taustarV39 (mkUnadornedV39 5 d a b) v := by
    have h1 : taustarV39 (mkUnadornedV39 5 d a b) v ≤ taustarV39 (mkUnadornedV39 5 d a b) z :=
      hmin z hzS
    have h2 : taustarV39 (mkUnadornedV39 5 d a b) z ≤ taustarV39 (mkUnadornedV39 5 d a b) v := by
      rw [← htau z, ← htau v]
      exact hz.2.1 v hBBsS
    exact le_antisymm h2 h1
  have hzprime : z ∈ BBprimeV39 (mkUnadornedV39 5 d a b) := by
    refine ⟨hzS, ?_, ?_⟩
    · intro w hw
      rw [htaueq]
      exact hmin w hw
    · rw [htaueq]
      exact hneg
  have hidxT : BBindexV39 (mkUnadornedV39 5 d a b') v
      = BBindexMinV39 (mkUnadornedV39 5 d a b') := by
    refine le_antisymm ?_ hle1
    have h1 : BBindexMinV39 (mkUnadornedV39 5 d a b) ≤ BBindexV39 (mkUnadornedV39 5 d a b) z :=
      la24bbindexMin_le _ hzprime
    rw [← hzval]
    show BBindexV39 (mkUnadornedV39 5 d a b) v ≤ BBindexV39 (mkUnadornedV39 5 d a b) z
    rw [hidx]
    exact h1
  exact ⟨hvBS, hidxT⟩

/-- HOL `SCS_5I1_STAB_DIAG` (OTMTOTJ.hl:553). Discharged: `la24stab_mm` on the
`scs_5I1` mk-form tables (`la24csAdj_far` for the far constant `6`). -/
theorem SCS_5I1_STAB_DIAG (v : ℕ → V3) (i j : ℕ) (h : v ∈ MMsV39 scs5I1)
    (hd : scsDiag 5 i j) (hle : dist (v i) (v j) ≤ cstab) :
    v ∈ MMsV39 (scsStabDiagV39 scs5I1 i j) := by
  refine la24stab_mm (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6) v i j hd hle h ?_
  intro x y hcls
  show csAdj 5 (2 * h0) 6 x y = 6
  exact la24csAdj_far hd (psort_eq_cases_p20 hcls)

/-- HOL `SCS_5I2_STAB_DIAG` (OTMTOTJ.hl:587). Discharged: as
`SCS_5I1_STAB_DIAG` on `scs_5I2` (same b-table). -/
theorem SCS_5I2_STAB_DIAG (v : ℕ → V3) (i j : ℕ) (h : v ∈ MMsV39 scs5I2)
    (hd : scsDiag 5 i j) (hle : dist (v i) (v j) ≤ cstab) :
    v ∈ MMsV39 (scsStabDiagV39 scs5I2 i j) := by
  refine la24stab_mm 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6) v i j hd hle h ?_
  intro x y hcls
  show csAdj 5 (2 * h0) 6 x y = 6
  exact la24csAdj_far hd (psort_eq_cases_p20 hcls)

/-- HOL `SCS_5I3_STAB_DIAG` (OTMTOTJ.hl:622). Discharged: `la24stab_mm` on the
`scs_5I3` funlist tables (diagonal slots all `6`; 25-cell residue sweep). -/
theorem SCS_5I3_STAB_DIAG (v : ℕ → V3) (i j : ℕ) (h : v ∈ MMsV39 scs5I3)
    (hd : scsDiag 5 i j) (hle : dist (v i) (v j) ≤ cstab) :
    v ∈ MMsV39 (scsStabDiagV39 scs5I3 i j) := by
  refine la24stab_mm 0.616
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5)
    (funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5) v i j hd hle h ?_
  have h6 : ∀ x y, psort 5 (i, j) = psort 5 (x, y) →
      funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 x y = 6 := by
    intro x y hcls
    have huv : funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 x y =
        funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 (x % 5) (y % 5) :=
      (funlist_mod_p20 _ _ _ _ _ (by omega)).symm
    rw [huv]
    have core : funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 (i % 5) (j % 5) = 6 := by
      obtain ⟨hd1, hd2, hd3⟩ := hd
      rw [← Nat.mod_add_mod i 5 1] at hd2
      rw [← Nat.mod_add_mod j 5 1] at hd3
      have hzi : i % 5 < 5 := Nat.mod_lt i (by omega)
      have hzj : j % 5 < 5 := Nat.mod_lt j (by omega)
      interval_cases i % 5 <;> interval_cases j % 5 <;>
        simp_all [funlistV39, psort, assocdV39] <;> norm_num
    rcases psort_eq_cases_p20 hcls with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2]
      exact core
    · rw [← e2, ← e1, la24funlist_symm5]
      exact core
  exact h6

/-- HOL `SCS_5M1_STAB_DIAG` (OTMTOTJ.hl:659). Discharged: as
`SCS_5I3_STAB_DIAG` on `scs_5M1`. -/
theorem SCS_5M1_STAB_DIAG (v : ℕ → V3) (i j : ℕ) (h : v ∈ MMsV39 scs5M1)
    (hd : scsDiag 5 i j) (hle : dist (v i) (v j) ≤ cstab) :
    v ∈ MMsV39 (scsStabDiagV39 scs5M1 i j) := by
  refine la24stab_mm 0.616
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5) v i j hd hle h ?_
  have h6 : ∀ x y, psort 5 (i, j) = psort 5 (x, y) →
      funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 x y = 6 := by
    intro x y hcls
    have huv : funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 x y =
        funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 (x % 5) (y % 5) :=
      (funlist_mod_p20 _ _ _ _ _ (by omega)).symm
    rw [huv]
    have core : funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 (i % 5) (j % 5) = 6 := by
      obtain ⟨hd1, hd2, hd3⟩ := hd
      rw [← Nat.mod_add_mod i 5 1] at hd2
      rw [← Nat.mod_add_mod j 5 1] at hd3
      have hzi : i % 5 < 5 := Nat.mod_lt i (by omega)
      have hzj : j % 5 < 5 := Nat.mod_lt j (by omega)
      interval_cases i % 5 <;> interval_cases j % 5 <;>
        simp_all [funlistV39, psort, assocdV39] <;> norm_num
    rcases psort_eq_cases_p20 hcls with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2]
      exact core
    · rw [← e2, ← e1, la24funlist_symm5]
      exact core
  exact h6

/- `_p24` private kit for the B3 `BERAK` discharges: the mod-5 `funlist`
invariance and the four `scs_5Ix` `a`-slot `≤ cstab` cell bounds (every
slot value — `0`, `2`, `2*h0 = 2.52`, `sqrt 8` — is `≤ cstab = 3.01`). -/

private theorem la24funlist_mod5_p24 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ)
    (i j : ℕ) :
    funlistV39 data d 5 i j = funlistV39 data d 5 (i % 5) (j % 5) := by
  unfold funlistV39
  rw [PSORT_MOD 5 i j (by norm_num), Nat.mod_mod i 5, Nat.mod_mod j 5]

/-- The `5I1` `a`-slot is `≤ cstab` at every cell (`2`/`2*h0 ≤ 3.01`). -/
private theorem la24a5I1_le_cstab_p24 (i j : ℕ) : scs5I1.a i j ≤ cstab := by
  show csAdj 5 2 (2 * h0) i j ≤ cstab
  unfold csAdj
  by_cases h1 : i % 5 = j % 5
  · rw [if_pos h1]; norm_num [cstab]
  rw [if_neg h1]
  by_cases h2 : j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5
  · rw [if_pos h2]; norm_num [cstab]
  · rw [if_neg h2]; norm_num [h0, cstab]

/-- The `5I2` `a`-slot is `≤ cstab` at every cell (`2`/`sqrt 8 ≤ cstab`). -/
private theorem la24a5I2_le_cstab_p24 (i j : ℕ) : scs5I2.a i j ≤ cstab := by
  show csAdj 5 2 (Real.sqrt 8) i j ≤ cstab
  unfold csAdj
  by_cases h1 : i % 5 = j % 5
  · rw [if_pos h1]; norm_num [cstab]
  rw [if_neg h1]
  by_cases h2 : j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5
  · rw [if_pos h2]; norm_num [cstab]
  · rw [if_neg h2]; exact sqrt8_LE_CSTAB

/-- The `5I3` `a`-slot is `≤ cstab` at every cell (all marked classes
`2*h0`, default `2`; 25-cell sweep over the mod-reduced residues). -/
private theorem la24a5I3_le_cstab_p24 (i j : ℕ) : scs5I3.a i j ≤ cstab := by
  show funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 i j ≤ cstab
  rw [la24funlist_mod5_p24 _ _ i j]
  have hzi : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hzj : j % 5 < 5 := Nat.mod_lt j (by omega)
  interval_cases i % 5 <;> interval_cases j % 5 <;>
    simp [funlistV39, psort, assocdV39] <;> norm_num [h0, cstab]

/-- The `5M1` `a`-slot: identical table to `5I3`. -/
private theorem la24a5M1_le_cstab_p24 (i j : ℕ) : scs5M1.a i j ≤ cstab := by
  show funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 i j ≤ cstab
  rw [la24funlist_mod5_p24 _ _ i j]
  have hzi : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hzj : j % 5 < 5 := Nat.mod_lt j (by omega)
  interval_cases i % 5 <;> interval_cases j % 5 <;>
    simp [funlistV39, psort, assocdV39] <;> norm_num [h0, cstab]

/-! ### B4. Diag-set identities over k = 5 (OTMTOTJ.hl:971-1153) -/

/-- `_p24` substrate: `scs_stab_diag_v39` index reduction, first coordinate
only, second already reduced mod 5 (STAB_MOD + the `k = 5` rewrite). -/
private theorem la24stab_mod_lt (s : ScsV39) (hs : isScsV39 s) (hk : s.k = 5) (a b : ℕ)
    (hb : b % 5 = b) : scsStabDiagV39 s (a % 5) b = scsStabDiagV39 s a b := by
  have h := STAB_MOD s a b hs
  rw [hk] at h
  rwa [hb] at h

/-- HOL `EXPAND_STAB_DIAG_5` (OTMTOTJ.hl:971). The five residue classes
`(i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5)` collapse onto the five
records `(i + 2, i)`, `i < 5` (port of LocalAuto20's `EXPAND_STAB_DIAG`,
k = 6 shape, over the PROVED `STAB_MOD`/`STAB_SYM` of LocalAuto20). -/
theorem EXPAND_STAB_DIAG_5 (s : ScsV39) (hs : isScsV39 s) (hk : s.k = 5) :
    {x | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      x = scsStabDiagV39 s (i % 5) (j % 5)} =
    {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 s (i + 2) i} := by
  ext x
  constructor
  · rintro ⟨i, j, hd, rfl⟩
    have hzi : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hzj : j % 5 < 5 := Nat.mod_lt j (by omega)
    rcases hd with h | h
    · refine ⟨j % 5, hzj, ?_⟩
      rw [h, la24stab_mod_lt s hs hk (j % 5 + 2) (j % 5) (Nat.mod_mod j 5)]
    · refine ⟨i % 5, hzi, ?_⟩
      rw [h, STAB_SYM, la24stab_mod_lt s hs hk (i % 5 + 2) (i % 5) (Nat.mod_mod i 5)]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i + 2, i, Or.inl ?_, ?_⟩
    · rw [Nat.mod_eq_of_lt hi]
    · have hSM := STAB_MOD s (i + 2) i hs
      rw [hk] at hSM
      exact hSM.symm

/-- HOL `EXPAND_STAB_DIAG_5I1` (OTMTOTJ.hl:997). -/
theorem EXPAND_STAB_DIAG_5I1 :
    {x | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      x = scsStabDiagV39 scs5I1 (i % 5) (j % 5)} =
    {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 scs5I1 (i + 2) i} :=
  EXPAND_STAB_DIAG_5 scs5I1 SCS_5I1_IS_SCS rfl

/-- HOL `EXPAND_STAB_DIAG_5I2` (OTMTOTJ.hl:1005). -/
theorem EXPAND_STAB_DIAG_5I2 :
    {x | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      x = scsStabDiagV39 scs5I2 (i % 5) (j % 5)} =
    {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 scs5I2 (i + 2) i} :=
  EXPAND_STAB_DIAG_5 scs5I2 SCS_5I2_IS_SCS rfl

/-- HOL `EXPAND_STAB_DIAG_5I3` (OTMTOTJ.hl:1014). -/
theorem EXPAND_STAB_DIAG_5I3 :
    {x | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      x = scsStabDiagV39 scs5I3 (i % 5) (j % 5)} =
    {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 scs5I3 (i + 2) i} :=
  EXPAND_STAB_DIAG_5 scs5I3 SCS_5I3_IS_SCS rfl

/-- HOL `EXPAND_STAB_DIAG_5M1` (OTMTOTJ.hl:1022). -/
theorem EXPAND_STAB_DIAG_5M1 :
    {x | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      x = scsStabDiagV39 scs5M1 (i % 5) (j % 5)} =
    {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 scs5M1 (i + 2) i} :=
  EXPAND_STAB_DIAG_5 scs5M1 SCS_5M1_IS_SCS rfl

/-- HOL `EQ_DIAG_STAB_5I1_02` (OTMTOTJ.hl:1034). -/
theorem EQ_DIAG_STAB_5I1_02 (i : ℕ) :
    scsArrowV39 {scsStabDiagV39 scs5I1 (i + 2) i} {scsStabDiagV39 scs5I1 0 2} := by
  sorry
  -- DISCHARGES: STAB_SYM + WKEIDFT + h0_LT_B_SCS_5I1 + h0_EQ_B_SCS_5I1 +
  -- SCS_5I1_IS_SCS + SCS_5I1_BASIC + Qknvmlb.SUC_MOD_NOT_EQ +
  -- Ocbicby.MOD_EQ_MOD_SHIFT.

/-- HOL `EQ_DIAG_STAB_5I2_02` (OTMTOTJ.hl:1060). -/
theorem EQ_DIAG_STAB_5I2_02 (i : ℕ) :
    scsArrowV39 {scsStabDiagV39 scs5I2 (i + 2) i} {scsStabDiagV39 scs5I2 0 2} := by
  sorry
  -- DISCHARGES: as `EQ_DIAG_STAB_5I1_02` on `scs_5I2`.

/-- HOL `SET_EQ_DIAG_STAB_5I1_02` (OTMTOTJ.hl:1085). -/
theorem SET_EQ_DIAG_STAB_5I1_02 :
    scsArrowV39 {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 scs5I1 (i + 2) i}
      {scsStabDiagV39 scs5I1 0 2} := by
  sorry
  -- DISCHARGES: FZIOTEF_UNION + EQ_DIAG_STAB_5I1_02.

/-- HOL `SET_EQ_DIAG_STAB_5I2_02` (OTMTOTJ.hl:1102). -/
theorem SET_EQ_DIAG_STAB_5I2_02 :
    scsArrowV39 {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 scs5I2 (i + 2) i}
      {scsStabDiagV39 scs5I2 0 2} := by
  sorry
  -- DISCHARGES: FZIOTEF_UNION + EQ_DIAG_STAB_5I2_02.

/-- HOL `SET_STAB_5I1` (OTMTOTJ.hl:1121). -/
theorem SET_STAB_5I1 :
    {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I1 i j} =
      {x | ∃ i j, scsDiag 5 (i % 5) (j % 5) ∧
        x = scsStabDiagV39 scs5I1 (i % 5) (j % 5)} := by
  ext x
  constructor
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 5 i j (by omega)).mpr hd,
      (STAB_MOD scs5I1 i j SCS_5I1_IS_SCS).symm⟩
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 5 i j (by omega)).mp hd,
      STAB_MOD scs5I1 i j SCS_5I1_IS_SCS⟩

/-- HOL `SET_STAB_5I2` (OTMTOTJ.hl:1126). -/
theorem SET_STAB_5I2 :
    {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I2 i j} =
      {x | ∃ i j, scsDiag 5 (i % 5) (j % 5) ∧
        x = scsStabDiagV39 scs5I2 (i % 5) (j % 5)} := by
  ext x
  constructor
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 5 i j (by omega)).mpr hd,
      (STAB_MOD scs5I2 i j SCS_5I2_IS_SCS).symm⟩
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 5 i j (by omega)).mp hd,
      STAB_MOD scs5I2 i j SCS_5I2_IS_SCS⟩

/-- HOL `SET_STAB_5I3` (OTMTOTJ.hl:1131). -/
theorem SET_STAB_5I3 :
    {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I3 i j} =
      {x | ∃ i j, scsDiag 5 (i % 5) (j % 5) ∧
        x = scsStabDiagV39 scs5I3 (i % 5) (j % 5)} := by
  ext x
  constructor
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 5 i j (by omega)).mpr hd,
      (STAB_MOD scs5I3 i j SCS_5I3_IS_SCS).symm⟩
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 5 i j (by omega)).mp hd,
      STAB_MOD scs5I3 i j SCS_5I3_IS_SCS⟩

/-- HOL `SET_STAB_5M1` (OTMTOTJ.hl:1136). -/
theorem SET_STAB_5M1 :
    {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5M1 i j} =
      {x | ∃ i j, scsDiag 5 (i % 5) (j % 5) ∧
        x = scsStabDiagV39 scs5M1 (i % 5) (j % 5)} := by
  ext x
  constructor
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 5 i j (by omega)).mpr hd,
      (STAB_MOD scs5M1 i j SCS_5M1_IS_SCS).symm⟩
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 5 i j (by omega)).mp hd,
      STAB_MOD scs5M1 i j SCS_5M1_IS_SCS⟩

/-! ### B4.9 (sweep-b24-w2): the private diagonal-class transfer kit

The three `SET_EQ_DIAG_STAB_*` arrows are discharged class-by-class: the
five diagonal stabilisations of a `k = 5` system are cyclic re-indexings
(`scs_prop_equ_v39`; LocalAuto12 `TRANS_MMS_SUBSET`/`YXIONXL3`) of the
`(0,2)` one — except the `5M1` `(1,3)`/`(1,4)` classes, which are reached
through the opposite re-indexing (`scs_opp_v39`; the OppKit sweep below +
FanBaseKit `MM_SCS_OPP_fb`), exactly the HOL `YXIONXL2`/`YXIONXL3` +
`PROP_OPP_DIAG_5M1_*` route of OTMTOTJ.hl:1395. -/

/-- `Periodic2` iteration (LA1-style clone for this file). -/
private theorem swb_periodic2_mul_p24 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ}
    (h : Periodic2 f k) : ∀ n x y, f (x + n * k) y = f x y ∧ f x (y + n * k) = f x y := by
  intro n
  induction n with
  | zero => intro x y; simp
  | succ m ih =>
      intro x y
      obtain ⟨ih1, ih2⟩ := ih x y
      constructor
      · have he : x + (m + 1) * k = (x + m * k) + k := by rw [Nat.succ_mul, Nat.add_assoc]
        rw [he, (h (x + m * k) y).1]
        exact ih1
      · have he : y + (m + 1) * k = (y + m * k) + k := by rw [Nat.succ_mul, Nat.add_assoc]
        rw [he, (h x (y + m * k)).2]
        exact ih2

/-- `scs_prop_equ_v39` composition. -/
private theorem swb_pe_comp_p24 (s : ScsV39) (a b : ℕ) :
    scsPropEquV39 (scsPropEquV39 s b) a = scsPropEquV39 s (a + b) := by
  obtain ⟨k, d, a₁, am, bm, b₁, J, lo, hi, str⟩ := s
  simp only [scsPropEquV39]
  congr 1 <;> (first
    | rfl
    | (funext x; simp only [Nat.add_assoc, Nat.add_left_comm])
    | (funext x y; simp only [Nat.add_assoc, Nat.add_left_comm]))

set_option maxHeartbeats 1000000 in
private theorem swb_pe_mul_p24 (s : ScsV39) (n : ℕ) (hs : isScsV39 s) :
    scsPropEquV39 s (n * s.k) = s := by
  obtain ⟨k, d, a₁, am, bm, b₁, J, lo, hi, str⟩ := s
  obtain ⟨hd, h3, h6, hplo, hphi, hpstr, -, hpa, hpam, hpbm, hpb, hpJ, -, -, -, -, -, -,
    -, -, -⟩ := hs
  simp only [scsPropEquV39]
  congr 1 <;> (first
    | rfl
    | (funext x; rw [Nat.add_comm (n * k) x]; exact la24periodic_mul hplo n x)
    | (funext x; rw [Nat.add_comm (n * k) x]; exact la24periodic_mul hphi n x)
    | (funext x; rw [Nat.add_comm (n * k) x]; exact la24periodic_mul hpstr n x)
    | (funext x y; rw [Nat.add_comm (n * k) x, Nat.add_comm (n * k) y];
        exact (swb_periodic2_mul_p24 hpa n x (y + n * k)).1.trans
          (swb_periodic2_mul_p24 hpa n x y).2)
    | (funext x y; rw [Nat.add_comm (n * k) x, Nat.add_comm (n * k) y];
        exact (swb_periodic2_mul_p24 hpam n x (y + n * k)).1.trans
          (swb_periodic2_mul_p24 hpam n x y).2)
    | (funext x y; rw [Nat.add_comm (n * k) x, Nat.add_comm (n * k) y];
        exact (swb_periodic2_mul_p24 hpbm n x (y + n * k)).1.trans
          (swb_periodic2_mul_p24 hpbm n x y).2)
    | (funext x y; rw [Nat.add_comm (n * k) x, Nat.add_comm (n * k) y];
        exact (swb_periodic2_mul_p24 hpb n x (y + n * k)).1.trans
          (swb_periodic2_mul_p24 hpb n x y).2)
    | (funext x y; rw [Nat.add_comm (n * k) x, Nat.add_comm (n * k) y];
        exact (swb_periodic2_mul_p24 hpJ n x (y + n * k)).1.trans
          (swb_periodic2_mul_p24 hpJ n x y).2))

-- The `5M1` `(1,3)` diagonal class is opposite-fixed: the stabilised
-- `(0,3)` system is the `3`-reindexed opposite of the stabilised `(1,3)` one
-- (HOL `PROP_OPP_DIAG_5M1_03`, OTMTOTJ.hl:1285; private re-proof after the
-- LA32 `PROP_OPP_DIAG_4M8_13_p32` recipe).
set_option maxHeartbeats 1000000 in
private theorem swb_prop_opp_5M1_13_p24 :
    scsStabDiagV39 scs5M1 0 3 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs5M1 1 3)) 3 := by
  rw [STAB_SYM scs5M1 0 3, STAB_SYM scs5M1 1 3]
  simp only [scsStabDiagV39, scs5M1, mkUnadornedV39, scsPropEquV39, scsOppV39, peropp2]
  rw [ScsV39.mk.injEq]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    funext j j'
    have h1 : j % 5 < 5 := Nat.mod_lt j (by omega)
    have h2 : j' % 5 < 5 := Nat.mod_lt j' (by omega)
    try rw [← funlist_mod_p20
      [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0), ((1, 3), 2 * h0),
        ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 j j' (by omega)]
    try rw [← PSORT_MOD 5 j j' (by omega)]
    try rw [← funlist_mod_p20
      [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6), ((1, 4), 6),
        ((2, 4), 6)] (2 * h0) 5 j j' (by omega)]
    rw [Nat.add_mod 3 j 5, Nat.add_mod 3 j' 5]
    interval_cases j % 5 <;> interval_cases j' % 5 <;>
      (first
        | rfl
        | simp [funlistV39, psort, assocdV39]
        | norm_num
        | norm_num [h0, cstab]
        | omega)

-- The `(1,4)` twin: the stabilised `(0,2)` system is the `3`-reindexed
-- opposite of the stabilised `(1,4)` one (HOL `PROP_OPP_DIAG_5M1_02`,
-- OTMTOTJ.hl:1323; private re-proof after the LA32 recipe).
set_option maxHeartbeats 1000000 in
private theorem swb_prop_opp_5M1_02_p24 :
    scsStabDiagV39 scs5M1 0 2 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs5M1 1 4)) 3 := by
  rw [STAB_SYM scs5M1 0 2, STAB_SYM scs5M1 1 4]
  simp only [scsStabDiagV39, scs5M1, mkUnadornedV39, scsPropEquV39, scsOppV39, peropp2]
  rw [ScsV39.mk.injEq]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    funext j j'
    have h1 : j % 5 < 5 := Nat.mod_lt j (by omega)
    have h2 : j' % 5 < 5 := Nat.mod_lt j' (by omega)
    try rw [← funlist_mod_p20
      [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0), ((1, 3), 2 * h0),
        ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 j j' (by omega)]
    try rw [← PSORT_MOD 5 j j' (by omega)]
    try rw [← funlist_mod_p20
      [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6), ((1, 4), 6),
        ((2, 4), 6)] (2 * h0) 5 j j' (by omega)]
    rw [Nat.add_mod 3 j 5, Nat.add_mod 3 j' 5]
    interval_cases j % 5 <;> interval_cases j' % 5 <;>
      (first
        | rfl
        | simp [funlistV39, psort, assocdV39]
        | norm_num
        | norm_num [h0, cstab]
        | omega)

/-- `psort` equality from unordered residue congruence (backward direction
of `la1psort_cases`). -/
private theorem swb_psort_mod_eq_p24 (k a b c d : ℕ) (hk : k ≠ 0)
    (h : (a % k = c % k ∧ b % k = d % k) ∨ (a % k = d % k ∧ b % k = c % k)) :
    psort k (a, b) = psort k (c, d) := by
  rw [← PSORT_MOD k a b hk, ← PSORT_MOD k c d hk]
  rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [psort_swap_p20 k (a % k) (b % k), e1, e2]

/-- A stabilisation depends only on the residue class of its pair. -/
private theorem swb_stab_class_p24 (s : ScsV39) (hk : s.k = 5) (hb : scsBasicV39 s)
    (i j i' j' : ℕ) (hcls : psort 5 (i, j) = psort 5 (i', j')) :
    scsStabDiagV39 s i j = scsStabDiagV39 s i' j' := by
  have he : psort s.k (i, j) = psort 5 (i, j) := by rw [hk]
  have he' : psort s.k (i', j') = psort 5 (i', j') := by rw [hk]
  have w1 : scsBasicV39 (scsStabDiagV39 s i j) :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  have w2 : scsBasicV39 (scsStabDiagV39 s i' j') :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  refine scs_inj _ _ w1 w2 rfl rfl rfl ?_
  funext x y
  show (if psort s.k (i, j) = psort s.k (x, y) then cstab else s.b x y) =
      (if psort s.k (i', j') = psort s.k (x, y) then cstab else s.b x y)
  rw [he, he', hcls]

/-- `csAdj` is residue-determined: the value at `(i % k, j % k)` equals the
value at `(i, j)`. -/
private theorem swb_csAdj_mod_p24 {k : ℕ} (a1 a2 : ℝ) (i j : ℕ) :
    csAdj k a1 a2 (i % k) (j % k) = csAdj k a1 a2 i j := by
  unfold csAdj
  simp only [Nat.mod_mod]
  rw [Nat.mod_add_mod i k 1, Nat.mod_add_mod j k 1]

/-- `csAdj 5 a1 a2` is invariant under a common index shift (its value
depends only on the residue-difference class of the pair). -/
private theorem swb_rot_csAdj_p24 (a1 a2 : ℝ) (t x y : ℕ) :
    csAdj 5 a1 a2 (x + t) (y + t) = csAdj 5 a1 a2 x y := by
  have bx : x % 5 < 5 := Nat.mod_lt x (by omega)
  have byb : y % 5 < 5 := Nat.mod_lt y (by omega)
  have bt : t % 5 < 5 := Nat.mod_lt t (by omega)
  have e1 : (x + t) % 5 = (x % 5 + t % 5) % 5 := by omega
  have e2 : (y + t) % 5 = (y % 5 + t % 5) % 5 := by omega
  have e3 : (x + t + 1) % 5 = (x % 5 + t % 5 + 1) % 5 := by omega
  have e4 : (y + t + 1) % 5 = (y % 5 + t % 5 + 1) % 5 := by omega
  have g1 : (x + 1) % 5 = (x % 5 + 1) % 5 := by omega
  have g2 : (y + 1) % 5 = (y % 5 + 1) % 5 := by omega
  unfold csAdj
  by_cases hD : x % 5 = y % 5
  · rw [if_pos (show (x + t) % 5 = (y + t) % 5 from by omega), if_pos hD]
  · rw [if_neg hD, if_neg (show (x + t) % 5 ≠ (y + t) % 5 from by omega)]
    by_cases hA : y % 5 = (x + 1) % 5 ∨ (y + 1) % 5 = x % 5
    · rcases hA with hA | hA
      · rw [if_pos (show (y + t) % 5 = (x + t + 1) % 5 ∨
          (y + t + 1) % 5 = (x + t) % 5 from Or.inl (by omega)),
          if_pos (Or.inl hA)]
      · rw [if_pos (show (y + t) % 5 = (x + t + 1) % 5 ∨
          (y + t + 1) % 5 = (x + t) % 5 from Or.inr (by omega)),
          if_pos (Or.inr hA)]
    · rw [if_neg hA,
        if_neg (show ¬((y + t) % 5 = (x + t + 1) % 5 ∨
          (y + t + 1) % 5 = (x + t) % 5) from by omega)]

/-- Cyclic-reindexing form of a diagonal stabilisation: the `(0, 2)` class
stabilisation, re-indexed by `t` (with the tables `hrot`-shift-invariant),
is the stabilisation of the shifted class. -/
private theorem swb_stab_pe_p24 (s : ScsV39) (hk : s.k = 5) (hb : scsBasicV39 s)
    (u v u' v' t : ℕ)
    (hrot : ∀ x y : ℕ, s.a (x + t) (y + t) = s.a x y ∧ s.b (x + t) (y + t) = s.b x y)
    (hcls : psort 5 (u' + t, v' + t) = psort 5 (u, v)) :
    scsPropEquV39 (scsStabDiagV39 s u v) t = scsStabDiagV39 s u' v' := by
  have hun1 : scsBasicV39 (scsPropEquV39 (scsStabDiagV39 s u v) t) :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  have hun2 : scsBasicV39 (scsStabDiagV39 s u' v') :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  refine scs_inj _ _ hun1 hun2 rfl rfl ?_ ?_
  · funext x y
    show s.a (t + x) (t + y) = s.a x y
    rw [Nat.add_comm t x, Nat.add_comm t y]
    exact (hrot x y).1
  · funext x y
    have he : psort s.k (u, v) = psort 5 (u, v) := by rw [hk]
    have he2 : psort s.k (u', v') = psort 5 (u', v') := by rw [hk]
    show (if psort s.k (u, v) = psort s.k (t + x, t + y) then cstab
        else s.b (t + x) (t + y)) =
      (if psort s.k (u', v') = psort s.k (x, y) then cstab else s.b x y)
    rw [he, he2]
    have he3 : psort s.k (t + x, t + y) = psort 5 (t + x, t + y) := by rw [hk]
    have he4 : psort s.k (x, y) = psort 5 (x, y) := by rw [hk]
    rw [he3, he4]
    have G : ∀ a b : ℕ, psort 5 (t + a, t + b) = psort 5 (u, v) ↔
        psort 5 (a, b) = psort 5 (u', v') := by
      intro a b
      constructor <;> intro hh
      · rcases psort_eq_cases_p20 hh with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact swb_psort_mod_eq_p24 5 a b u' v' (by norm_num)
            (by rcases psort_eq_cases_p20 hcls with ⟨f1, f2⟩ | ⟨f1, f2⟩
                · exact Or.inl ⟨by omega, by omega⟩
                · exact Or.inr ⟨by omega, by omega⟩)
        · exact swb_psort_mod_eq_p24 5 a b u' v' (by norm_num)
            (by rcases psort_eq_cases_p20 hcls with ⟨f1, f2⟩ | ⟨f1, f2⟩
                · exact Or.inr ⟨by omega, by omega⟩
                · exact Or.inl ⟨by omega, by omega⟩)
      · rcases psort_eq_cases_p20 hh with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact swb_psort_mod_eq_p24 5 (t + a) (t + b) u v (by norm_num)
            (by rcases psort_eq_cases_p20 hcls with ⟨f1, f2⟩ | ⟨f1, f2⟩
                · exact Or.inl ⟨by omega, by omega⟩
                · exact Or.inr ⟨by omega, by omega⟩)
        · exact swb_psort_mod_eq_p24 5 (t + a) (t + b) u v (by norm_num)
            (by rcases psort_eq_cases_p20 hcls with ⟨f1, f2⟩ | ⟨f1, f2⟩
                · exact Or.inr ⟨by omega, by omega⟩
                · exact Or.inl ⟨by omega, by omega⟩)
    by_cases hc1 : psort 5 (u, v) = psort 5 (t + x, t + y)
    · rw [if_pos hc1, if_pos (((G x y).mp hc1.symm).symm)]
    · rw [if_neg hc1,
        if_neg (fun h => hc1 (((G x y).mpr h.symm).symm)), Nat.add_comm t x,
        Nat.add_comm t y]
      exact (hrot x y).2

/-- Diagonal classes of a `k = 5` pair sit at distance two. -/
private theorem swb_diag5_pair_p24 {i j : ℕ} (hd : scsDiag 5 i j) :
    i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5 := by
  obtain ⟨hd1, hd2, hd3⟩ := hd
  have b1 : i % 5 < 5 := Nat.mod_lt i (by omega)
  have b2 : j % 5 < 5 := Nat.mod_lt j (by omega)
  have h1 : (i + 1) % 5 = (i % 5 + 1) % 5 := (Nat.mod_add_mod i 5 1).symm
  have h2 : (j + 1) % 5 = (j % 5 + 1) % 5 := (Nat.mod_add_mod j 5 1).symm
  rw [h1] at hd2
  rw [h2] at hd3
  interval_cases i % 5 <;> interval_cases j % 5 <;> omega

/-- The `dist-2` diagonal stabilisations are cyclic re-indexings of the
`(0,2)` one (tables `hrot`-shift-invariant). -/
private theorem swb_stab5_pe_p24 (s : ScsV39) (hk : s.k = 5) (hb : scsBasicV39 s)
    (i j : ℕ)
    (hrot : ∀ x y : ℕ, s.a (x + (5 - j % 5)) (y + (5 - j % 5)) = s.a x y ∧
      s.b (x + (5 - j % 5)) (y + (5 - j % 5)) = s.b x y)
    (hsum : i % 5 = (j % 5 + 2) % 5) :
    scsStabDiagV39 s i j = scsPropEquV39 (scsStabDiagV39 s 0 2) (5 - j % 5) := by
  have hzj : j % 5 < 5 := Nat.mod_lt j (by omega)
  have hcls1 : psort 5 (i, j) = psort 5 (j % 5, (j % 5 + 2) % 5) := by
    rw [← PSORT_MOD 5 i j (by norm_num), psort_swap_p20 5 (i % 5) (j % 5), hsum]
  have hstep1 : scsStabDiagV39 s i j = scsStabDiagV39 s (j % 5) ((j % 5 + 2) % 5) :=
    swb_stab_class_p24 s hk hb i j (j % 5) ((j % 5 + 2) % 5) hcls1
  rw [hstep1]
  refine (swb_stab_pe_p24 s hk hb 0 2 (j % 5) ((j % 5 + 2) % 5) (5 - j % 5) hrot ?_).symm
  rw [← PSORT_MOD 5 (j % 5 + (5 - j % 5)) ((j % 5 + 2) % 5 + (5 - j % 5)) (by norm_num),
    (by omega : (j % 5 + (5 - j % 5)) % 5 = 0),
    (by omega : ((j % 5 + 2) % 5 + (5 - j % 5)) % 5 = 2)]

/-- `MMs`-nonemptiness descends through a cyclic re-indexing. -/
private theorem swb_mms_pe_inv_p24 (s : ScsV39) (t : ℕ) (hs : isScsV39 s)
    (h : (MMsV39 (scsPropEquV39 s t)).Nonempty) : (MMsV39 s).Nonempty := by
  have hk0 : s.k ≠ 0 := by have := hs.2.1; omega
  have hpe : scsPropEquV39 (scsPropEquV39 s t) (s.k - t % s.k) = s := by
    have h1 : scsPropEquV39 (scsPropEquV39 s t) (s.k - t % s.k) =
        scsPropEquV39 s (s.k - t % s.k + t) :=
      swb_pe_comp_p24 s (s.k - t % s.k) t
    rw [h1]
    have ht : s.k - t % s.k + t = (t / s.k + 1) * s.k := by
      have hlt : t % s.k < s.k := Nat.mod_lt t (by omega)
      have hdm := Nat.div_add_mod t s.k
      have h2 : (t / s.k + 1) * s.k = s.k * (t / s.k) + s.k := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (t / s.k) s.k]
      rw [h2]
      omega
    rw [ht, swb_pe_mul_p24 s (t / s.k + 1) hs]
  obtain ⟨v, hv⟩ := h
  have h2 := TRANS_MMS_SUBSET (PROP_EQU_IS_SCS rfl hs t) hv (s.k - t % s.k)
  rw [hpe] at h2
  exact ⟨_, h2⟩

/-- Residue `φ x = k - (x % k + 1)` is below `k` for `1 ≤ k`. -/
private theorem swbopp_phi_lt {k : ℕ} (hk : 1 ≤ k) (x : ℕ) :
    k - (x % k + 1) < k := by
  have h : x % k < k := Nat.mod_lt x (by omega)
  omega

/-- Equal residues below `k` give equal indices. -/
private theorem swbopp_mod_eq {k p q : ℕ} (h : p % k = q % k) (hp : p < k)
    (hq : q < k) : p = q := by
  have h1 : p % k = p := Nat.mod_eq_of_lt hp
  have h2 : q % k = q := Nat.mod_eq_of_lt hq
  omega

/-- HOL `OPP_SUC_MOD` (YXIONXL2.hl:381): `φ` is an involution on residues. -/
private theorem swbopp_phi_inv {k : ℕ} (hk : k ≠ 0) (x : ℕ) :
    k - ((k - (x % k + 1)) % k + 1) = x % k := by
  have hlt : x % k < k := Nat.mod_lt x (by omega)
  have h1 : (k - (x % k + 1)) % k = k - (x % k + 1) :=
    Nat.mod_eq_of_lt (by have := hlt; omega)
  rw [h1]
  omega

/-- The `φ`-pair `(φ i, φ (i + 1))` is a reversed adjacent pair modulo `k`:
`φ i = (φ (i + 1) + 1) % k`. -/
private theorem swbopp_pair_adj {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    k - (i % k + 1) = (k - ((i + 1) % k + 1) + 1) % k := by
  have hi : i % k < k := Nat.mod_lt i (by omega)
  by_cases hlt : i % k + 1 < k
  · have hw1 : (i + 1) % k = i % k + 1 := by
      rw [← Nat.mod_add_mod i k 1]
      exact Nat.mod_eq_of_lt hlt
    rw [hw1]
    have hR : k - (i % k + 1 + 1) + 1 < k := by have := hi; omega
    rw [Nat.mod_eq_of_lt hR]
    omega
  · have heq : i % k + 1 = k := by omega
    have hw1 : (i + 1) % k = 0 := by
      rw [← Nat.mod_add_mod i k 1, heq, Nat.mod_self]
    rw [hw1, heq, Nat.sub_self]
    have hR : k - (0 + 1 : ℕ) + 1 = k := by omega
    rw [hR, Nat.mod_self]

/-- Orientation swap: if the `φ`-pair satisfies `φ y % k = (φ x + 1) % k`
then `x % k = (y + 1) % k` (transports the `s.J`-adjacency through the
opposite re-indexing, orientations swapped). -/
private theorem swbopp_adj_swap {k : ℕ} (hk : 1 ≤ k) {x y : ℕ}
    (h : (k - (y % k + 1)) % k = (k - (x % k + 1) + 1) % k) :
    x % k = (y + 1) % k := by
  have hx : x % k < k := Nat.mod_lt x (by omega)
  have hy : y % k < k := Nat.mod_lt y (by omega)
  have hmod : (k - (y % k + 1)) % k = k - (y % k + 1) :=
    Nat.mod_eq_of_lt (by have := hy; omega)
  rw [hmod] at h
  have hrhs : (k - (x % k + 1) + 1) % k = (k - x % k) % k := by
    have hsh : k - (x % k + 1) + 1 = k - x % k := by have := hx; omega
    rw [hsh]
  rw [hrhs] at h
  rw [(Nat.mod_add_mod y k 1).symm]
  by_cases hx0 : x % k = 0
  · have h2 : (k - x % k) % k = 0 := by rw [hx0, Nat.sub_zero, Nat.mod_self]
    rw [h2] at h
    have hyk : y % k + 1 = k := by have := h; have := hy; omega
    rw [hx0, hyk, Nat.mod_self]
  · have h2 : (k - x % k) % k = k - x % k :=
      Nat.mod_eq_of_lt (by have := hx; omega)
    rw [h2] at h
    have hxy : y % k + 1 = x % k := by
      have h3 := h; have := hy; have := hx; omega
    rw [hxy]
    exact (Nat.mod_modEq x k).symm

/-- Adjacent-pair value transport: `x % k = (y + 1) % k` makes the value
`b x y` an adjacent value `b m (m + 1)` with `m = y % k` (the HOL shape
used throughout `OPP_IS_SCS`; residue reduction via the LocalAuto12 public
`periodic2Mod1/2` kit). -/
private theorem swbopp_b_adj {k : ℕ} {b : ℕ → ℕ → ℝ}
    (hk : 1 ≤ k) (hper : Periodic2 b k) (hsymg : ∀ i j, b i j = b j i)
    {x y : ℕ} (h : x % k = (y + 1) % k) :
    b x y = b (y % k) (y % k + 1) := by
  have hk0 : k ≠ 0 := by omega
  have hylt : y % k < k := Nat.mod_lt y (by omega)
  have hyk : (y + 1) % k = (y % k + 1) % k := (Nat.mod_add_mod y k 1).symm
  rw [hyk] at h
  have hred : b (x % k) (y % k) = b x y :=
    (periodic2Mod1 hk0 hper x (y % k)).trans (periodic2Mod2 hk0 hper x y)
  rw [← hred]
  by_cases hlt : y % k + 1 < k
  · have hxk : x % k = y % k + 1 := by rw [h, Nat.mod_eq_of_lt hlt]
    rw [hxk, hsymg (y % k + 1) (y % k)]
  · have heq : y % k + 1 = k := by omega
    have hxk : x % k = 0 := by rw [h, heq, Nat.mod_self]
    rw [hxk, hsymg 0 (y % k)]
    exact (hper (y % k) 0).2.symm.trans
      (congrArg (b (y % k)) (show (0 : ℕ) + k = y % k + 1 from by rw [Nat.zero_add, heq]))

/-- Pointwise key: the `(i, i + 1)`-value of the opposite re-indexing is
the reversed adjacent value at the successor representative
`m = k - 1 - ((i + 1) % k)`. -/
private theorem swbopp_key {k : ℕ} {g : ℕ → ℕ → ℝ}
    (hk : 1 ≤ k) (hper : Periodic2 g k) (hsymg : ∀ i j, g i j = g j i) (i : ℕ) :
    g (k - (i % k + 1)) (k - ((i + 1) % k + 1))
      = g (k - 1 - ((i + 1) % k)) (k - 1 - ((i + 1) % k) + 1) := by
  have htr := swbopp_b_adj (b := g) hk hper hsymg
    (x := k - (i % k + 1)) (y := k - ((i + 1) % k + 1))
    (by rw [Nat.mod_eq_of_lt (swbopp_phi_lt hk i)]; exact swbopp_pair_adj hk i)
  rw [htr, Nat.mod_eq_of_lt (swbopp_phi_lt hk (i + 1))]
  rw [show k - ((i + 1) % k + 1) = k - 1 - ((i + 1) % k) from by
    have hw : (i + 1) % k < k := Nat.mod_lt (i + 1) (by omega)
    omega]


/-- HOL `OPP_IS_SCS` (Ocbicby.hl:2536 / YXIONXL2.hl:2536).  See the
docstring above for the discharge note. -/
private theorem swb_opp_isscs_p24 (s : ScsV39) (hs : isScsV39 s) : isScsV39 (scsOppV39 s) := by
  obtain ⟨hd, h3, hk6, hplo, hphi, hpstr, -, hpa, hpam, hpbm, hpb, hpJ, hsym,
    hch, hdiag0, hdiag, hb3, hbc, hJstruct, hJab, hcard⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  have hk1 : 1 ≤ s.k := by omega
  have hsymb : ∀ x y, s.b x y = s.b y x := fun x y => (hsym x y).2.2.2.1
  have hsymbA : ∀ x y, s.a x y = s.a y x := fun x y => (hsym x y).1
  refine ⟨hd, h3, hk6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact peropp_periodic s.lo s.k
  · exact peropp_periodic s.hi s.k
  · exact peropp_periodic s.str s.k
  · exact peropp_periodic s.str s.k
  · intro p q
    show s.a (s.k - ((p + s.k) % s.k + 1)) (s.k - (q % s.k + 1))
        = s.a (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) ∧
      s.a (s.k - (p % s.k + 1)) (s.k - ((q + s.k) % s.k + 1))
        = s.a (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    rw [Nat.add_mod_right, Nat.add_mod_right]
    exact ⟨rfl, rfl⟩
  · intro p q
    show s.am (s.k - ((p + s.k) % s.k + 1)) (s.k - (q % s.k + 1))
        = s.am (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) ∧
      s.am (s.k - (p % s.k + 1)) (s.k - ((q + s.k) % s.k + 1))
        = s.am (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    rw [Nat.add_mod_right, Nat.add_mod_right]
    exact ⟨rfl, rfl⟩
  · intro p q
    show s.bm (s.k - ((p + s.k) % s.k + 1)) (s.k - (q % s.k + 1))
        = s.bm (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) ∧
      s.bm (s.k - (p % s.k + 1)) (s.k - ((q + s.k) % s.k + 1))
        = s.bm (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    rw [Nat.add_mod_right, Nat.add_mod_right]
    exact ⟨rfl, rfl⟩
  · intro p q
    show s.b (s.k - ((p + s.k) % s.k + 1)) (s.k - (q % s.k + 1))
        = s.b (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) ∧
      s.b (s.k - (p % s.k + 1)) (s.k - ((q + s.k) % s.k + 1))
        = s.b (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    rw [Nat.add_mod_right, Nat.add_mod_right]
    exact ⟨rfl, rfl⟩
  · intro p q
    show s.J (s.k - ((p + s.k) % s.k + 1)) (s.k - (q % s.k + 1))
        = s.J (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) ∧
      s.J (s.k - (p % s.k + 1)) (s.k - ((q + s.k) % s.k + 1))
        = s.J (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    rw [Nat.add_mod_right, Nat.add_mod_right]
    exact ⟨rfl, rfl⟩
  · intro p q
    exact ⟨(hsym (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))).1,
      (hsym (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))).2.1,
      (hsym (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))).2.2.1,
      (hsym (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))).2.2.2.1,
      (hsym (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))).2.2.2.2⟩
  · intro p q
    exact hch (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
  · intro p
    exact hdiag0 (s.k - (p % s.k + 1))
  · intro p q hpq
    have hne : s.k - (p % s.k + 1) ≠ s.k - (q % s.k + 1) := by
      intro hcon
      have e1 : s.k - ((s.k - (p % s.k + 1)) % s.k + 1) = p % s.k := swbopp_phi_inv hk0 p
      have e2 : s.k - ((s.k - (q % s.k + 1)) % s.k + 1) = q % s.k := swbopp_phi_inv hk0 q
      rw [Nat.mod_eq_of_lt (swbopp_phi_lt hk1 p)] at e1
      rw [Nat.mod_eq_of_lt (swbopp_phi_lt hk1 q)] at e2
      exact hpq.2.2 (swbopp_mod_eq (k := s.k) (by rw [← e1, ← e2, hcon]) hpq.1 hpq.2.1)
    show 2 ≤ s.a (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    exact hdiag _ _ ⟨swbopp_phi_lt hk1 p, swbopp_phi_lt hk1 q, hne⟩
  · intro p hp3
    show s.b (s.k - (p % s.k + 1)) (s.k - ((p + 1) % s.k + 1)) < 4
    rw [swbopp_key hk1 hpb hsymb p]
    exact hb3 _ hp3
  · intro p hp6
    show s.b (s.k - (p % s.k + 1)) (s.k - ((p + 1) % s.k + 1)) ≤ cstab
    rw [swbopp_key hk1 hpb hsymb p]
    exact hbc _ hp6
  · intro p q hpq
    show q % s.k = (p + 1) % s.k ∨ p % s.k = (q + 1) % s.k
    have hJs : s.J (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) := hpq
    rcases hJstruct _ _ hJs with h | h
    · exact Or.inr (swbopp_adj_swap hk1 h)
    · exact Or.inl (swbopp_adj_swap hk1 h)
  · intro p q hpq
    show s.a (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) = Real.sqrt 8 ∧
      s.b (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) = cstab
    exact hJab _ _ hpq
  · -- the ncard bound: the bad set of the opposite reindexes to the bad
    -- set of `s` along the successor representative `i ↦ k - 1 - ((i+1)%k)`
    show {i | i < s.k ∧ (2 * h0 < s.b (s.k - (i % s.k + 1))
        (s.k - ((i + 1) % s.k + 1)) ∨
        2 < s.a (s.k - (i % s.k + 1)) (s.k - ((i + 1) % s.k + 1)))}.ncard + s.k ≤ 6
    have hcardT : {i | i < s.k ∧ (2 * h0 < s.b (s.k - (i % s.k + 1))
          (s.k - ((i + 1) % s.k + 1)) ∨
        2 < s.a (s.k - (i % s.k + 1)) (s.k - ((i + 1) % s.k + 1)))}.ncard
        = {j | j < s.k ∧ (2 * h0 < s.b j (j + 1) ∨ 2 < s.a j (j + 1))}.ncard := by
      refine Set.ncard_congr
        (f := fun i (_ : i ∈ (_ : Set ℕ)) => s.k - 1 - ((i + 1) % s.k)) ?_ ?_ ?_
      · rintro i ⟨hi, hbad | hbad⟩
        · have hlt : (i + 1) % s.k < s.k := Nat.mod_lt (i + 1) (by omega)
          refine ⟨by omega, ?_⟩
          rw [swbopp_key hk1 hpb hsymb i] at hbad
          exact Or.inl hbad
        · have hlt : (i + 1) % s.k < s.k := Nat.mod_lt (i + 1) (by omega)
          refine ⟨by omega, ?_⟩
          rw [swbopp_key hk1 hpa hsymbA i] at hbad
          exact Or.inr hbad
      · rintro i j hi hb hcon
        obtain ⟨hi, -⟩ := hi
        obtain ⟨hj, -⟩ := hb
        have hcon' : s.k - 1 - ((i + 1) % s.k) = s.k - 1 - ((j + 1) % s.k) := hcon
        by_cases hik : i + 1 < s.k
        · by_cases hjk : j + 1 < s.k
          · have e1 : (i + 1) % s.k = i + 1 := Nat.mod_eq_of_lt hik
            have e2 : (j + 1) % s.k = j + 1 := Nat.mod_eq_of_lt hjk
            rw [e1, e2] at hcon'
            omega
          · have e1 : (i + 1) % s.k = i + 1 := Nat.mod_eq_of_lt hik
            have hjk1 : j + 1 = s.k := by omega
            have e2 : (j + 1) % s.k = 0 := by rw [hjk1, Nat.mod_self]
            rw [e1, e2] at hcon'
            omega
        · by_cases hjk : j + 1 < s.k
          · have hjk1 : i + 1 = s.k := by omega
            have e1 : (i + 1) % s.k = 0 := by rw [hjk1, Nat.mod_self]
            have e2 : (j + 1) % s.k = j + 1 := Nat.mod_eq_of_lt hjk
            rw [e1, e2] at hcon'
            omega
          · have hik1 : i + 1 = s.k := by omega
            have hjk1 : j + 1 = s.k := by omega
            have e1 : (i + 1) % s.k = 0 := by rw [hik1, Nat.mod_self]
            have e2 : (j + 1) % s.k = 0 := by rw [hjk1, Nat.mod_self]
            rw [e1, e2] at hcon'
            omega
      · rintro j ⟨hj, hbad⟩
        set i := (2 * s.k - 2 - j) % s.k with hiv
        have hi : i < s.k := by rw [hiv]; exact Nat.mod_lt _ (by omega)
        have hi1 : (i + 1) % s.k = (2 * s.k - 1 - j) % s.k := by
          rw [hiv, Nat.mod_add_mod (2 * s.k - 2 - j) s.k 1,
            show 2 * s.k - 2 - j + 1 = 2 * s.k - 1 - j from by omega]
        have hfi : s.k - 1 - ((i + 1) % s.k) = j := by
          rw [hi1]
          by_cases hjk1 : j = s.k - 1
          · rw [hjk1, show 2 * s.k - 1 - (s.k - 1) = s.k from by omega, Nat.mod_self]
            omega
          · have hmod : (2 * s.k - 1 - j) % s.k = s.k - 1 - j := by
              have hj2 : j ≤ s.k - 2 := by omega
              rw [show 2 * s.k - 1 - j = s.k + (s.k - 1 - j) from by omega,
                Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_modEq _ _,
                Nat.mod_eq_of_lt (by omega)]
            rw [hmod]
            omega
        refine ⟨i, ⟨hi, ?_⟩, hfi⟩
        rw [swbopp_key hk1 hpb hsymb i, swbopp_key hk1 hpa hsymbA i, hfi]
        exact hbad
    rw [hcardT]
    exact hcard
  -- DISCHARGES: NEEDS Ocbicby.hl `OPP_IS_SCS` over `ScsV39`
  -- (2026-10-28, la33-ab-w1: fan-free sweep, no `sorry` upstream).

/-- HOL `SET_EQ_DIAG_STAB_5I1` (OTMTOTJ.hl:1141). -/
theorem SET_EQ_DIAG_STAB_5I1 :
    scsArrowV39 {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I1 i j}
      {scsStabDiagV39 scs5I1 0 2} := by
  have hI : scsDiag 5 0 2 := by unfold scsDiag; norm_num
  have his02 : isScsV39 (scsStabDiagV39 scs5I1 0 2) :=
    la24isScs_stab scs5I1 0 2 hI SCS_5I1_IS_SCS (fun u v _ => la24a5I1_le_cstab_p24 u v)
  have hrot : ∀ p x y : ℕ, scs5I1.a (x + (5 - p % 5)) (y + (5 - p % 5)) = scs5I1.a x y ∧
      scs5I1.b (x + (5 - p % 5)) (y + (5 - p % 5)) = scs5I1.b x y := fun p x y =>
    ⟨swb_rot_csAdj_p24 2 (2 * h0) (5 - p % 5) x y,
      swb_rot_csAdj_p24 (2 * h0) 6 (5 - p % 5) x y⟩
  refine ⟨fun s hs => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    exact his02
  · by_cases hne : (MMsV39 (scsStabDiagV39 scs5I1 0 2)).Nonempty
    · exact Or.inr ⟨scsStabDiagV39 scs5I1 0 2, Set.mem_singleton _,
        Set.nonempty_iff_ne_empty.mp hne⟩
    · have h02e : MMsV39 (scsStabDiagV39 scs5I1 0 2) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      refine Or.inl fun u hu => ?_
      obtain ⟨i, j, hd, rfl⟩ := hu
      rcases swb_diag5_pair_p24 hd with hsum | hsum
      · rw [swb_stab5_pe_p24 scs5I1 rfl SCS_5I1_BASIC i j (hrot j) hsum]
        exact Set.not_nonempty_iff_eq_empty.mp fun hne =>
          Set.not_nonempty_iff_eq_empty.mpr h02e
            (swb_mms_pe_inv_p24 _ (5 - j % 5) his02 hne)
      · rw [STAB_SYM scs5I1 i j, swb_stab5_pe_p24 scs5I1 rfl SCS_5I1_BASIC j i
          (hrot i) hsum]
        exact Set.not_nonempty_iff_eq_empty.mp fun hne =>
          Set.not_nonempty_iff_eq_empty.mpr h02e
            (swb_mms_pe_inv_p24 _ (5 - i % 5) his02 hne)
  -- DISCHARGES: SET_STAB_5I1 + DIAG_EQ_ADD5 + EXPAND_STAB_DIAG_5I1 +
  -- SET_EQ_DIAG_STAB_5I1_02 + FZIOTEF-chaining.

/-- HOL `SET_EQ_DIAG_STAB_5I2` (OTMTOTJ.hl:1148). -/
theorem SET_EQ_DIAG_STAB_5I2 :
    scsArrowV39 {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I2 i j}
      {scsStabDiagV39 scs5I2 0 2} := by
  have hI : scsDiag 5 0 2 := by unfold scsDiag; norm_num
  have his02 : isScsV39 (scsStabDiagV39 scs5I2 0 2) :=
    la24isScs_stab scs5I2 0 2 hI SCS_5I2_IS_SCS (fun u v _ => la24a5I2_le_cstab_p24 u v)
  have hrot : ∀ p x y : ℕ, scs5I2.a (x + (5 - p % 5)) (y + (5 - p % 5)) = scs5I2.a x y ∧
      scs5I2.b (x + (5 - p % 5)) (y + (5 - p % 5)) = scs5I2.b x y := fun p x y =>
    ⟨swb_rot_csAdj_p24 2 (Real.sqrt 8) (5 - p % 5) x y,
      swb_rot_csAdj_p24 (2 * h0) 6 (5 - p % 5) x y⟩
  refine ⟨fun s hs => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    exact his02
  · by_cases hne : (MMsV39 (scsStabDiagV39 scs5I2 0 2)).Nonempty
    · exact Or.inr ⟨scsStabDiagV39 scs5I2 0 2, Set.mem_singleton _,
        Set.nonempty_iff_ne_empty.mp hne⟩
    · have h02e : MMsV39 (scsStabDiagV39 scs5I2 0 2) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      refine Or.inl fun u hu => ?_
      obtain ⟨i, j, hd, rfl⟩ := hu
      rcases swb_diag5_pair_p24 hd with hsum | hsum
      · rw [swb_stab5_pe_p24 scs5I2 rfl SCS_5I2_BASIC i j (hrot j) hsum]
        exact Set.not_nonempty_iff_eq_empty.mp fun hne =>
          Set.not_nonempty_iff_eq_empty.mpr h02e
            (swb_mms_pe_inv_p24 _ (5 - j % 5) his02 hne)
      · rw [STAB_SYM scs5I2 i j, swb_stab5_pe_p24 scs5I2 rfl SCS_5I2_BASIC j i
          (hrot i) hsum]
        exact Set.not_nonempty_iff_eq_empty.mp fun hne =>
          Set.not_nonempty_iff_eq_empty.mpr h02e
            (swb_mms_pe_inv_p24 _ (5 - i % 5) his02 hne)
  -- DISCHARGES: SET_STAB_5I2 + DIAG_EQ_ADD5 + EXPAND_STAB_DIAG_5I2 +
  -- SET_EQ_DIAG_STAB_5I2_02 + FZIOTEF-chaining.

/-! ### B5. The `5M1`/`5I3` twin chain (OTMTOTJ.hl:1184-1520)

FILE MAP: the master arrows `OTMTOTJ3` (:1500) and `OTMTOTJ4` (:1520) are
restated verbatim in Section B6 below (skeleton restatements, 2026-09-21). -/

/-- HOL `BB_5I3_IS_BB_5M1` (OTMTOTJ.hl:1184). -/
theorem BB_5I3_IS_BB_5M1 : ∀ v : ℕ → V3,
    BBsV39 (scsStabDiagV39 scs5I3 2 4) v → BBsV39 (scsStabDiagV39 scs5M1 2 4) v := by
  sorry
  -- DISCHARGES: pentagons.hl `SCS_TAC` case work on the stabilised rows.
  -- HOL: `!v. v IN BBs_v39 (scs_stab_diag_v39 scs_5I3 2 4) ==>
  --   v IN BBs_v39 (scs_stab_diag_v39 scs_5M1 2 4)` (statement fixed at
  -- the `(2,4)` diag, per the SCS_TAC expansion in the source).

/-- HOL `STAB_5I3_SCS` (OTMTOTJ.hl:1199). Discharged: `la24isScs_stab` on the
proved `SCS_5I3_IS_SCS` (the stabilised class is a diagonal class, `a`-value
`2*h0 ≤ cstab` by the 25-cell sweep) + `scsBasicV39` of the mk-form stab. -/
theorem STAB_5I3_SCS (i j : ℕ) (hd : scsDiag (scs5I3.k) i j) :
    isScsV39 (scsStabDiagV39 scs5I3 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5I3 i j) := by
  refine ⟨la24isScs_stab scs5I3 i j hd SCS_5I3_IS_SCS ?_,
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩⟩
  intro u v hcls
  rw [show scs5I3.k = 5 from rfl] at hcls
  simp only [scs5I3, mkUnadornedV39]
  have key : ∀ p q : ℕ, funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 p q ≤ cstab := by
    intro p q
    have h1 : p % 5 < 5 := Nat.mod_lt p (by omega)
    have h2 : q % 5 < 5 := Nat.mod_lt q (by omega)
    rw [← funlist_mod_p20
      [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
        ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 p q (by omega)]
    interval_cases p % 5 <;> interval_cases q % 5 <;>
      simp [funlistV39, psort, assocdV39] <;> norm_num [h0, cstab]
  have huv : funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 u v =
    funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 (u % 5) (v % 5) :=
    (funlist_mod_p20 _ _ _ _ _ (by omega)).symm
  rcases psort_eq_cases_p20 hcls with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [huv, ← e1, ← e2]
    exact key (i % 5) (j % 5)
  · rw [huv, ← e2, ← e1]
    exact key (j % 5) (i % 5)

/-- HOL `STAB_5I2_SCS` (OTMTOTJ.hl:1210). Discharged: `la24isScs_stab` +
`la24csAdj_far` (the diagonal `csAdj`-slot of `scs_5I2` is `sqrt 8 ≤ cstab`). -/
theorem STAB_5I2_SCS (i j : ℕ) (hd : scsDiag (scs5I2.k) i j) :
    isScsV39 (scsStabDiagV39 scs5I2 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5I2 i j) := by
  refine ⟨la24isScs_stab scs5I2 i j hd SCS_5I2_IS_SCS ?_,
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩⟩
  intro u v hcls
  rw [show scs5I2.k = 5 from rfl] at hcls
  show csAdj 5 2 (Real.sqrt 8) u v ≤ cstab
  rw [la24csAdj_far hd (psort_eq_cases_p20 hcls)]
  exact sqrt8_LE_CSTAB

/-- HOL `STAB_5M1_SCS` (OTMTOTJ.hl:1223). Discharged: as `STAB_5I3_SCS` on
`scs_5M1`. -/
theorem STAB_5M1_SCS (i j : ℕ) (hd : scsDiag (scs5M1.k) i j) :
    isScsV39 (scsStabDiagV39 scs5M1 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5M1 i j) := by
  refine ⟨la24isScs_stab scs5M1 i j hd SCS_5M1_IS_SCS ?_,
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩⟩
  intro u v hcls
  rw [show scs5M1.k = 5 from rfl] at hcls
  simp only [scs5M1, mkUnadornedV39]
  have key : ∀ p q : ℕ, funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 p q ≤ cstab := by
    intro p q
    have h1 : p % 5 < 5 := Nat.mod_lt p (by omega)
    have h2 : q % 5 < 5 := Nat.mod_lt q (by omega)
    rw [← funlist_mod_p20
      [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
        ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 p q (by omega)]
    interval_cases p % 5 <;> interval_cases q % 5 <;>
      simp [funlistV39, psort, assocdV39] <;> norm_num [h0, cstab]
  have huv : funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 u v =
    funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 (u % 5) (v % 5) :=
    (funlist_mod_p20 _ _ _ _ _ (by omega)).symm
  rcases psort_eq_cases_p20 hcls with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [huv, ← e1, ← e2]
    exact key (i % 5) (j % 5)
  · rw [huv, ← e2, ← e1]
    exact key (j % 5) (i % 5)

/-- HOL `PROP_OPP_DIAG_5M1_03` (OTMTOTJ.hl:1285). -/
theorem PROP_OPP_DIAG_5M1_03 :
    scsStabDiagV39 scs5M1 0 3 = scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs5M1 1 3)) 3 := by
  sorry
  -- DISCHARGES: scs_inj + scs_v39_explicit + STAB_5M1_SCS + PSORT_MOD +
  -- MOD_ADD_MOD + PSORT_5_EXPLICIT (peropp/peropp2 flip).

/-- HOL `PROP_OPP_DIAG_5M1_02` (OTMTOTJ.hl:1323). -/
theorem PROP_OPP_DIAG_5M1_02 :
    scsStabDiagV39 scs5M1 0 2 = scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs5M1 1 4)) 3 := by
  sorry
  -- DISCHARGES: scs_inj + scs_v39_explicit + STAB_5M1_SCS + PSORT_MOD +
  -- MOD_ADD_MOD + PSORT_5_EXPLICIT (peropp/peropp2 flip).

/-- HOL `SET_EQ_DIAG_STAB_5M1` (OTMTOTJ.hl:1395). -/
theorem SET_EQ_DIAG_STAB_5M1 :
    scsArrowV39 {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5M1 i j}
      ({scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
        scsStabDiagV39 scs5M1 2 4} : Set ScsV39) := by
  have hI02 : scsDiag 5 0 2 := by unfold scsDiag; norm_num
  have hI03 : scsDiag 5 0 3 := by unfold scsDiag; norm_num
  have hI24 : scsDiag 5 2 4 := by unfold scsDiag; norm_num
  have hI13 : scsDiag 5 1 3 := by unfold scsDiag; norm_num
  have hI14 : scsDiag 5 1 4 := by unfold scsDiag; norm_num
  have hb5 : scsBasicV39 scs5M1 := SCS_5M1_BASIC
  have hclass : ∀ a b c d : ℕ, psort 5 (a, b) = psort 5 (c, d) →
      MMsV39 (scsStabDiagV39 scs5M1 a b) =
        MMsV39 (scsStabDiagV39 scs5M1 c d) := by
    intro a b c d hcls
    rw [swb_stab_class_p24 scs5M1 rfl hb5 a b c d hcls]
  -- the two opposite-class contradictions
  have h13 : ¬(MMsV39 (scsStabDiagV39 scs5M1 0 3)).Nonempty →
      MMsV39 (scsStabDiagV39 scs5M1 1 3) = ∅ := fun h03 =>
    Set.not_nonempty_iff_eq_empty.mp fun hne => h03 (by
      have hIS : isScsV39 (scsStabDiagV39 scs5M1 1 3) := (STAB_5M1_SCS 1 3 hI13).1
      obtain ⟨v, hv⟩ := hne
      have hmem : MMsV39 (scsOppV39 (scsStabDiagV39 scs5M1 1 3))
          (fun i => -(peropp v 5 i)) :=
        MM_SCS_OPP_fb _ v 5 rfl hIS (by norm_num) hv
      have h2 := TRANS_MMS_SUBSET (swb_opp_isscs_p24 _ hIS) hmem 3
      rw [← swb_prop_opp_5M1_13_p24] at h2
      exact ⟨_, h2⟩)
  have h14 : ¬(MMsV39 (scsStabDiagV39 scs5M1 0 2)).Nonempty →
      MMsV39 (scsStabDiagV39 scs5M1 1 4) = ∅ := fun h02 =>
    Set.not_nonempty_iff_eq_empty.mp fun hne => h02 (by
      have hIS : isScsV39 (scsStabDiagV39 scs5M1 1 4) := (STAB_5M1_SCS 1 4 hI14).1
      obtain ⟨v, hv⟩ := hne
      have hmem : MMsV39 (scsOppV39 (scsStabDiagV39 scs5M1 1 4))
          (fun i => -(peropp v 5 i)) :=
        MM_SCS_OPP_fb _ v 5 rfl hIS (by norm_num) hv
      have h2 := TRANS_MMS_SUBSET (swb_opp_isscs_p24 _ hIS) hmem 3
      rw [← swb_prop_opp_5M1_02_p24] at h2
      exact ⟨_, h2⟩)
  refine ⟨fun s hs => ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | hs
    · exact (STAB_5M1_SCS 0 2 hI02).1
    rcases hs with rfl | rfl
    · exact (STAB_5M1_SCS 0 3 hI03).1
    · exact (STAB_5M1_SCS 2 4 hI24).1
  · by_cases h02 : (MMsV39 (scsStabDiagV39 scs5M1 0 2)).Nonempty
    · exact Or.inr ⟨_, Set.mem_insert _ _, Set.nonempty_iff_ne_empty.mp h02⟩
    by_cases h03 : (MMsV39 (scsStabDiagV39 scs5M1 0 3)).Nonempty
    · exact Or.inr ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert _ _),
        Set.nonempty_iff_ne_empty.mp h03⟩
    by_cases h24 : (MMsV39 (scsStabDiagV39 scs5M1 2 4)).Nonempty
    · exact Or.inr ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_singleton _)), Set.nonempty_iff_ne_empty.mp h24⟩
    have h02e : MMsV39 (scsStabDiagV39 scs5M1 0 2) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h02
    have h03e : MMsV39 (scsStabDiagV39 scs5M1 0 3) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h03
    have h24e : MMsV39 (scsStabDiagV39 scs5M1 2 4) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h24
    refine Or.inl fun u hu => ?_
    obtain ⟨i, j, hd, rfl⟩ := hu
    have hzj : j % 5 < 5 := Nat.mod_lt j (by omega)
    rcases swb_diag5_pair_p24 hd with hsum | hsum
    · have hps : psort 5 (i, j) = psort 5 (j % 5, (j % 5 + 2) % 5) := by
        rw [← PSORT_MOD 5 i j (by norm_num), psort_swap_p20 5 (i % 5) (j % 5), hsum]
      interval_cases j % 5
      · exact (hclass i j 0 2 (by rw [hps] <;> simp [psort])).trans h02e
      · rw [hclass i j 1 3 (by rw [hps] <;> simp [psort])]
        exact h13 h03
      · exact (hclass i j 2 4 (by rw [hps] <;> simp [psort])).trans h24e
      · exact (hclass i j 0 3 (by rw [hps] <;> simp [psort])).trans h03e
      · rw [hclass i j 1 4 (by rw [hps] <;> simp [psort])]
        exact h14 h02
    · have hsym : scsStabDiagV39 scs5M1 i j = scsStabDiagV39 scs5M1 j i :=
        STAB_SYM scs5M1 i j
      have hzi : i % 5 < 5 := Nat.mod_lt i (by omega)
      have hps : psort 5 (j, i) = psort 5 (i % 5, (i % 5 + 2) % 5) := by
        rw [← PSORT_MOD 5 j i (by norm_num), psort_swap_p20 5 (j % 5) (i % 5), hsum]
      interval_cases i % 5
      · exact ((congrArg MMsV39 hsym).trans (hclass j i 0 2 (by rw [hps] <;> simp [psort]))).trans h02e
      · rw [hsym, hclass j i 1 3 (by rw [hps] <;> simp [psort])]
        exact h13 h03
      · exact ((congrArg MMsV39 hsym).trans (hclass j i 2 4 (by rw [hps] <;> simp [psort]))).trans h24e
      · exact ((congrArg MMsV39 hsym).trans (hclass j i 0 3 (by rw [hps] <;> simp [psort]))).trans h03e
      · rw [hsym, hclass j i 1 4 (by rw [hps] <;> simp [psort])]
        exact h14 h02
  -- DISCHARGES: SET_STAB_5M1 + DIAG_EQ_ADD5 + EXPAND_STAB_DIAG_5I3 +
  -- EXPAND_STAB_DIAG_5M1 + EQ_DIAG_STAB_* (the three singleton arrows,
  -- FZIOTEF-chained).

/-! ## Section C: UXCKFPE.hl — the k ≤ 6 taustar capstone (2 defs + 20
theorems)

Encoding (over the `_p23` stable-system kit of `Kepler.Text.LocalAuto23` and
the `dih2k` row kit of `Kepler.Text.LocalAuto4`):
- `real^(M,3)finite_product` with `dimindex(:M) = k` ↦ `FinVec k 3`
  (`Fin (k*3) → ℝ`); `matvec (vector[vv 1;..;vv k;vv 0])` ↦
  `flattenRow_p23 vv k`; `row i (vecmats l)` (1-based) ↦ `rowSy_p23 l (i-1)`;
- the body set `{matvec v | rows IN ball_annulus /\ CONDITION1_SY a b v /\
  CONDITION2_SY v}` ↦ `B_SY1_p4 aR bR` (LocalAuto4:883) with the k×k scs
  tables `aR i j = scs_a_v39 s ((i+1) MOD k) ((j+1) MOD k)`;
- `tri_sy (k,d,s,a,b,J,f)` ↦ the explicit-argument LocalAuto23 kit
  (`StableSyP23` / `triStable_p23`); `change_type_v2 (scs_J_v39 s) k` ↦
  `scsJSet_p23 s`; `CONDITION1_SY`/`CONDITION2_SY` ↦ the `_p4` twins;
- the HOL row-decoding hypothesis
  `(!i. vv i = if i MOD k = 0 then row k v else ...)` is carried as
  `Periodic vv k` plus `CONDITION*_SY_p4` on `cycRow_p23 vv k`.
The HOL giants (each a 100-300 line tactic block over the row/periodicity
bookkeeping) are `sorry` with DISCHARGES chains; `FINITE_J1_TS`,
`tri_sy_explicit` and the case assembly `UXCKFPE` are PROVED. -/


private theorem periodic2_left_p24 {f : ℕ → ℕ → ℝ} {n : ℕ} (hp : Periodic2 f n)
    (q i j : ℕ) : f (n * q + i) j = f i j := by
  induction q with
  | zero => simp
  | succ m ih =>
      have hrw : n * (m + 1) + i = n * m + i + n := by ring
      rw [hrw, (hp (n * m + i) j).1, ih]

private theorem periodic2_right_p24 {f : ℕ → ℕ → ℝ} {n : ℕ} (hp : Periodic2 f n)
    (i j q : ℕ) : f i (n * q + j) = f i j := by
  induction q with
  | zero => simp
  | succ m ih =>
      have hrw : n * (m + 1) + j = n * m + j + n := by ring
      rw [hrw, (hp i (n * m + j)).2, ih]

private theorem periodic2_mod_eq_p24 {f : ℕ → ℕ → ℝ} {n : ℕ} (hp : Periodic2 f n)
    (i j : ℕ) : f i j = f (i % n) (j % n) := by
  have h1 : f i j = f (n * (i / n) + i % n) j := by
    conv_lhs => rw [(Nat.div_add_mod i n).symm]
  rw [h1, periodic2_left_p24 hp]
  have h2 : f (i % n) j = f (i % n) (n * (j / n) + j % n) := by
    conv_lhs => rw [(Nat.div_add_mod j n).symm]
  rw [h2, periodic2_right_p24 hp]

private theorem table_shift_eq_p24 (f : ℕ → ℕ → ℝ) (n : ℕ) (hp : Periodic2 f n)
    (i j : ℕ) (hi : i < n) (hj : j < n) :
    f (i + 1) (j + 1) = f ((i + 1) % n) ((j + 1) % n) := by
  have e1 : f (i + 1) (j + 1) = f (n * ((i + 1) / n) + (i + 1) % n) (j + 1) := by
    conv_lhs => rw [(Nat.div_add_mod (i + 1) n).symm]
  rw [e1, periodic2_left_p24 hp]
  have e2 : f ((i + 1) % n) (j + 1)
      = f ((i + 1) % n) (n * ((j + 1) / n) + (j + 1) % n) := by
    conv_lhs => rw [(Nat.div_add_mod (j + 1) n).symm]
  rw [e2, periodic2_right_p24 hp]

/-- SF-89 feed: `isScsV39`'s adjacent-edge upper bound (the
`3 < s.k → s.b i (i + 1) ≤ cstab` conjunct of LA1 `isScsV39`, HOL is_scs_v39 appendix.hl:354) shifted onto
the `((i + 1) % k)`-indexing that the CASE_4/5/6 tables `aRk`/`bRk` use —
this is exactly the repaired `hstab` premise of `bodyClosed_p23` at
`m = k`, since `bRk s i (finNext i) = s.b ((i + 1) % k)
(((finNext i : ℕ) + 1) % k)` definitionally. -/
private theorem stabAdj_of_isScsV39 {k : ℕ} (s : ScsV39) (hs : isScsV39 s)
    (hk : s.k = k) (hk3 : 3 < s.k) (i : Fin k) :
    s.b (((i : ℕ) + 1) % k) ((((finNext i : Fin k) : ℕ) + 1) % k) ≤ cstab_p4 := by
  unfold isScsV39 at hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hperb, -, -, -, -, -, -, hup, -, -, -⟩ := hs
  subst hk
  rw [show ((finNext i : Fin s.k) : ℕ) = ((i : ℕ) + 1) % s.k from rfl, Nat.mod_add_mod,
    ← periodic2_mod_eq_p24 hperb ((i : ℕ) + 1) ((i : ℕ) + 1 + 1)]
  exact le_trans (hup ((i : ℕ) + 1) hk3) (le_of_eq rfl)

/-- SF-91 案② feed: the full `stableSystem_p23` carrier of the CASE_4/5/6
shifted tables, witnessed by the scs record itself — `IS_SCS_STABLE_SYSTEM_p23`
(LA23:762) is stated at exactly this tuple, so after `hk : s.k = k` the first
leg closes by `rwa`; the agreement legs are `rfl` on the frozen `aRk`/`bRk`
lambdas (`aR4 s i j = s.a ((i+1) % 4) ((j+1) % 4)` definitionally).  This is
the premise `continuousOn_tauFun_p23` (SF-91 案②) consumes; the W8 discharge
translates it into the `StableSyP9` record (fanchain-w7 DELIVERY §6). -/
private theorem fullStable_of_isScsV39 {k : ℕ} (s : ScsV39) (hs : isScsV39 s)
    (hk : s.k = k) (hk3 : 3 < s.k) (aR bR : Fin k → Fin k → ℝ)
    (ha : ∀ i j : Fin k, aR i j = s.a (((i : ℕ) + 1) % k) (((j : ℕ) + 1) % k))
    (hb : ∀ i j : Fin k, bR i j = s.b (((i : ℕ) + 1) % k) (((j : ℕ) + 1) % k)) :
    ∃ a b : ℕ → ℕ → ℝ, ∃ J : Set (Set ℕ),
      stableSystem_p23 k 0 (Set.Iic (k - 1)) a b J (fun i => (1 + i) % k) ∧
      (∀ i j : Fin k, a (((i : ℕ) + 1) % k) (((j : ℕ) + 1) % k) = aR i j) ∧
      (∀ i j : Fin k, b (((i : ℕ) + 1) % k) (((j : ℕ) + 1) % k) = bR i j) :=
  ⟨s.a, s.b, scsJSet_p23 s,
    by have h := IS_SCS_STABLE_SYSTEM_p23 s hs hk3; rwa [hk] at h,
    fun i j => (ha i j).symm, fun i j => (hb i j).symm⟩

/-- the k=4 shifted tables (the frozen inline lambdas). -/
private def aR4 (s : ScsV39) : Fin 4 → Fin 4 → ℝ :=
  fun i j : Fin 4 => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4)

private def bR4 (s : ScsV39) : Fin 4 → Fin 4 → ℝ :=
  fun i j : Fin 4 => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4)

/-- glue (CLEAN): BBs bounds give the shifted CONDITION1. -/
private theorem cond1_4_of_BBs (s : ScsV39) (w : ℕ → V3) (hBB : BBsV39 s w) :
    CONDITION1_SY_p4 (aR4 s) (bR4 s) (cycRow_p23 w 4) := by
  intro i j
  have h := hBB.2.2.1 (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4)
  rw [dist_eq_norm] at h
  exact ⟨h.1, h.2⟩

/-- glue (LA36 fan bridge + V/E/F): the BBs fan conjunct gives CONDITION2. -/
private theorem cond2_4_of_BBs (s : ScsV39) (w : ℕ → V3) (hs : isScsV39 s)
    (hk : s.k = 4) (hBB : BBsV39 s w) :
    CONDITION2_SY_p4 (cycRow_p23 w 4) := by
  have hVEFF := V_E_FF_IS_SCS_CASES_4_p23 s w hs hk hBB
  rcases hBB.2.2.2 with h3 | hfan
  · omega
  · show convexLocalFan_p4 (V_SY_p4 (cycRow_p23 w 4))
      (E_SY_p4 (cycRow_p23 w 4)) (F_SY_p4 (cycRow_p23 w 4))
    rw [hVEFF.1, hVEFF.2.1, hVEFF.2.2, Set.image_univ, Set.image_univ]
    exact convexLocalFan_p4_of_ConvexLocalFan_p36 hfan

/-- glue (CLEAN): the flattening of any BBs realisation lies in the body. -/
private theorem flatten_mem_B_SY1_4 (s : ScsV39) (w : ℕ → V3) (hs : isScsV39 s)
    (hk : s.k = 4) (hBB : BBsV39 s w) :
    flattenRow_p23 w 4 ∈ (B_SY1_p4 (aR4 s) (bR4 s) : Set (FinVec 4 3)) := by
  refine ⟨cycRow_p23 w 4, ?_, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact hBB.1 ⟨((i : ℕ) + 1) % 4, rfl⟩
  · exact cond1_4_of_BBs s w hBB
  · exact cond2_4_of_BBs s w hs hk hBB

/-- the k=5 shifted tables (the frozen inline lambdas). -/
private def aR5 (s : ScsV39) : Fin 5 → Fin 5 → ℝ :=
  fun i j : Fin 5 => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5)

private def bR5 (s : ScsV39) : Fin 5 → Fin 5 → ℝ :=
  fun i j : Fin 5 => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5)

/-- glue (CLEAN): BBs bounds give the shifted CONDITION1. -/
private theorem cond1_5_of_BBs (s : ScsV39) (w : ℕ → V3) (hBB : BBsV39 s w) :
    CONDITION1_SY_p4 (aR5 s) (bR5 s) (cycRow_p23 w 5) := by
  intro i j
  have h := hBB.2.2.1 (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5)
  rw [dist_eq_norm] at h
  exact ⟨h.1, h.2⟩

/-- glue (LA36 fan bridge + V/E/F): the BBs fan conjunct gives CONDITION2. -/
private theorem cond2_5_of_BBs (s : ScsV39) (w : ℕ → V3) (hs : isScsV39 s)
    (hk : s.k = 5) (hBB : BBsV39 s w) :
    CONDITION2_SY_p4 (cycRow_p23 w 5) := by
  have hVEFF := V_E_FF_IS_SCS_CASES_5_p23 s w hs hk hBB
  rcases hBB.2.2.2 with h3 | hfan
  · omega
  · show convexLocalFan_p4 (V_SY_p4 (cycRow_p23 w 5))
      (E_SY_p4 (cycRow_p23 w 5)) (F_SY_p4 (cycRow_p23 w 5))
    rw [hVEFF.1, hVEFF.2.1, hVEFF.2.2, Set.image_univ, Set.image_univ]
    exact convexLocalFan_p4_of_ConvexLocalFan_p36 hfan

/-- glue (CLEAN): the flattening of any BBs realisation lies in the body. -/
private theorem flatten_mem_B_SY1_5 (s : ScsV39) (w : ℕ → V3) (hs : isScsV39 s)
    (hk : s.k = 5) (hBB : BBsV39 s w) :
    flattenRow_p23 w 5 ∈ (B_SY1_p4 (aR5 s) (bR5 s) : Set (FinVec 5 3)) := by
  refine ⟨cycRow_p23 w 5, ?_, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact hBB.1 ⟨((i : ℕ) + 1) % 5, rfl⟩
  · exact cond1_5_of_BBs s w hBB
  · exact cond2_5_of_BBs s w hs hk hBB

/-- the k=6 shifted tables (the frozen inline lambdas). -/
private def aR6 (s : ScsV39) : Fin 6 → Fin 6 → ℝ :=
  fun i j : Fin 6 => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6)

private def bR6 (s : ScsV39) : Fin 6 → Fin 6 → ℝ :=
  fun i j : Fin 6 => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6)

/-- glue (CLEAN): BBs bounds give the shifted CONDITION1. -/
private theorem cond1_6_of_BBs (s : ScsV39) (w : ℕ → V3) (hBB : BBsV39 s w) :
    CONDITION1_SY_p4 (aR6 s) (bR6 s) (cycRow_p23 w 6) := by
  intro i j
  have h := hBB.2.2.1 (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6)
  rw [dist_eq_norm] at h
  exact ⟨h.1, h.2⟩

/-- glue (LA36 fan bridge + V/E/F): the BBs fan conjunct gives CONDITION2. -/
private theorem cond2_6_of_BBs (s : ScsV39) (w : ℕ → V3) (hs : isScsV39 s)
    (hk : s.k = 6) (hBB : BBsV39 s w) :
    CONDITION2_SY_p4 (cycRow_p23 w 6) := by
  have hVEFF := V_E_FF_IS_SCS_CASES_6_p23 s w hs hk hBB
  rcases hBB.2.2.2 with h3 | hfan
  · omega
  · show convexLocalFan_p4 (V_SY_p4 (cycRow_p23 w 6))
      (E_SY_p4 (cycRow_p23 w 6)) (F_SY_p4 (cycRow_p23 w 6))
    rw [hVEFF.1, hVEFF.2.1, hVEFF.2.2, Set.image_univ, Set.image_univ]
    exact convexLocalFan_p4_of_ConvexLocalFan_p36 hfan

/-- glue (CLEAN): the flattening of any BBs realisation lies in the body. -/
private theorem flatten_mem_B_SY1_6 (s : ScsV39) (w : ℕ → V3) (hs : isScsV39 s)
    (hk : s.k = 6) (hBB : BBsV39 s w) :
    flattenRow_p23 w 6 ∈ (B_SY1_p4 (aR6 s) (bR6 s) : Set (FinVec 6 3)) := by
  refine ⟨cycRow_p23 w 6, ?_, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact hBB.1 ⟨((i : ℕ) + 1) % 6, rfl⟩
  · exact cond1_6_of_BBs s w hBB
  · exact cond2_6_of_BBs s w hs hk hBB

/-! ### C1. The k = 4 witnesses (UXCKFPE.hl:70-543) -/

/-- HOL `NOT_EMPTY_CASE_4_IS_SCS` (UXCKFPE.hl:70). -/
theorem NOT_EMPTY_CASE_4_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s vv) :
    (B_SY1_p4
      (fun i j : Fin 4 => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
      (fun i j : Fin 4 => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))) ≠ ∅ := by

  -- FILL (la23prereq-w1 draft C; LA36 core `inNotEmpty_core_p36` + table glue;
  -- CLEAN)
  have hap : Periodic2 s.a s.k := hs.2.2.2.2.2.2.2.1
  rw [hk] at hap
  have hbp : Periodic2 s.b s.k := hs.2.2.2.2.2.2.2.2.2.2.1
  rw [hk] at hbp
  have htabA : (fun i j : Fin 4 => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      = (fun i j : Fin 4 => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4)) := by
    funext i j
    show s.a ((i : ℕ) + 1) ((j : ℕ) + 1) = _
    exact table_shift_eq_p24 s.a 4 hap (i : ℕ) (j : ℕ) i.isLt j.isLt
  have htabB : (fun i j : Fin 4 => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      = (fun i j : Fin 4 => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4)) := by
    funext i j
    show s.b ((i : ℕ) + 1) ((j : ℕ) + 1) = _
    exact table_shift_eq_p24 s.b 4 hbp (i : ℕ) (j : ℕ) i.isLt j.isLt
  show (B_SY1_p4
    (fun i j : Fin 4 => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
    (fun i j : Fin 4 => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))) ≠ ∅
  rw [← htabA, ← htabB]
  exact Set.nonempty_iff_ne_empty.mp
    ⟨flattenRow_p23 vv 4, inNotEmpty_core_p36 (k := 4) (by omega) hk hBB⟩
  -- DISCHARGES: IN_IS_SCS_CASE_4_p23 (witness `flattenRow_p23 vv 4`) over
  -- IS_SCS_IN_BALL_ANNULUS_4_p23 + the BBsV39 bound/fan conjuncts.
  -- (filled from the LA23 fill `V_E_FF_IS_SCS_CASES_4_p23` +
  -- `IS_SCS_IN_BALL_ANNULUS_4_p23` + the LA36 core `inNotEmpty_core_p36`.)

/-- HOL `IN_NOT_EMPTY_B1_SY_4_IS_SCS` (UXCKFPE.hl:208): the row-decoding
converse — the k = 4 body conditions realize `vv` in `BBsV39 s`. -/
theorem IN_NOT_EMPTY_B1_SY_4_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 4) (hper : Periodic vv 4)
    (hball : ∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun i j : Fin 4 => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
      (fun i j : Fin 4 => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
      (cycRow_p23 vv 4))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 4)) :
    BBsV39 s vv := by

  -- FILL (la23prereq-w1 draft C; LA36 core `inB1_core_p36` + table glue; CLEAN)
  have hap : Periodic2 s.a s.k := hs.2.2.2.2.2.2.2.1
  rw [hk] at hap
  have hbp : Periodic2 s.b s.k := hs.2.2.2.2.2.2.2.2.2.2.1
  rw [hk] at hbp
  have htabA : (fun i j : Fin 4 => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
      = (fun i j : Fin 4 => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1)) := by
    funext i j
    show s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4) = _
    exact (table_shift_eq_p24 s.a 4 hap (i : ℕ) (j : ℕ) i.isLt j.isLt).symm
  have htabB : (fun i j : Fin 4 => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
      = (fun i j : Fin 4 => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
    funext i j
    show s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4) = _
    exact (table_shift_eq_p24 s.b 4 hbp (i : ℕ) (j : ℕ) i.isLt j.isLt).symm
  rw [htabA, htabB] at hC1
  exact inB1_core_p36 (k := 4) (by omega) hk hper
    (fun i j => ⟨periodic2_mod_eq_p24 hap i j, periodic2_mod_eq_p24 hbp i j⟩)
    hball hC1 hC2
  -- DISCHARGES: BBsV39 conjunct walk — annulus range + the CONDITION1
  -- bounds lifted to all indices by `Periodic2 s.a/b s.k` periodicity
  -- (PERIODIC_PROPERTY) + V_E_FF_IS_SCS_CASES_4_p23 for the fan conjunct.
  -- (filled from the LA23 fill + the LA36 core `inB1_core_p36`.)

/-- HOL `XWITCCN_CASE_4_IS_SCS` (UXCKFPE.hl:432). -/
theorem XWITCCN_CASE_4_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : s.k = 4)
    (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by

  -- FILL (la24casebank-w1 probe3 assembly + casebank-close-w1
  -- kit; wiring: HDPLYGY minimizer + the five prereq fills + the TAUSTAR
  -- bridge; the only taint entering here is the two HDPLYGY-kit NEEDS
  -- pieces `continuousOn_tauFun_p23` / `bodyClosed_p23` — see CLOSE-PLAN).
  have hk3 : 3 < s.k := by omega
  have hcomp : IsCompact (B_SY1_p4 (aR4 s) (bR4 s) : Set (FinVec 4 3)) :=
    B_SY1_p4_compact_of_fan_p23 (aR4 s) (bR4 s)
      (bodyClosed_p23 (aR4 s) (bR4 s) (by norm_num : 2 < 4)
        (fun i => stabAdj_of_isScsV39 s hs hk hk3 i))
      (bodyBounded_p23 4 (aR4 s) (bR4 s))
  have hd : ContinuousOn (fun l : FinVec 4 3 =>
      dFun_p23 (scsToStableSy_p23 s hs hk3) l) (B_SY1_p4 (aR4 s) (bR4 s)) :=
    (continuous_dFun_p23 _).continuousOn
  have hfun : ContinuousOn (fun l : FinVec 4 3 =>
      tauFun (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (F_SY_p4 (vecmatsV3_p4 l))) (B_SY1_p4 (aR4 s) (bR4 s)) :=
    continuousOn_tauFun_p23 _ _ (by norm_num : 2 < 4)
      (fullStable_of_isScsV39 s hs hk hk3 _ _ (fun _ _ => rfl) (fun _ _ => rfl))
  have hcont : ContinuousOn (tauStar_p23 (scsToStableSy_p23 s hs hk3))
      (B_SY1_p4 (aR4 s) (bR4 s)) :=
    continuousOn_tauStar_p23 _ _ _ hd hfun
  have hne := NOT_EMPTY_CASE_4_IS_SCS_p24 s vv hs hk hBB
  obtain ⟨x, hx_mem, hx_min⟩ :=
    HDPLYGY_p23 (scsToStableSy_p23 s hs hk3) (aR4 s) (bR4 s) hcomp hcont hne
  unfold B_SY1_p4 at hx_mem
  obtain ⟨w, hw, hwx⟩ := hx_mem
  -- the cyclic un-flattening vv1 of the body point w (HOL ABBREV vv1)
  set vv1 : ℕ → V3 := fun i => w ⟨(i + 3) % 4, by omega⟩ with hv1
  have hp4 : Periodic vv1 4 := by
    intro i
    simp only [hv1]
    refine congrArg w (Fin.val_injective ?_)
    simp only [Fin.val_mk]
    omega
  have hcyc : cycRow_p23 vv1 4 = w := by
    funext j
    show vv1 (((j : ℕ) + 1) % 4) = w j
    have hj := j.isLt
    simp only [hv1]
    refine congrArg w (Fin.val_injective ?_)
    simp only [Fin.val_mk]
    omega
  have hflat : flattenRow_p23 vv1 4 = x := by
    funext i
    show (cycRow_p23 vv1 4 ⟨(i : ℕ) / 3, by have := i.isLt; omega⟩ :
        Fin 3 → ℝ) ⟨(i : ℕ) % 3, by omega⟩ = x i
    rw [hcyc]
    exact congrFun hwx i
  have hball : ∀ i : Fin 4, cycRow_p23 vv1 4 i ∈ ballAnnulus := by
    intro i; rw [hcyc]; exact hw.1 i
  have hC1 : CONDITION1_SY_p4 (aR4 s) (bR4 s) (cycRow_p23 vv1 4) := by
    rw [hcyc]; exact hw.2.1
  have hC2 : CONDITION2_SY_p4 (cycRow_p23 vv1 4) := by
    rw [hcyc]; exact hw.2.2
  have hBB1 : BBsV39 s vv1 :=
    IN_NOT_EMPTY_B1_SY_4_IS_SCS_p24 s vv1 hs hk hp4 hball hC1 hC2
  have hmemVV : flattenRow_p23 vv 4 ∈
      (B_SY1_p4 (aR4 s) (bR4 s) : Set (FinVec 4 3)) :=
    flatten_mem_B_SY1_4 s vv hs hk hBB
  -- negativity transfer (TAUSTAR bridge twice + minimizer)
  have hneg : taustarV39 s vv1 < 0 := by
    rw [TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4_p23 s vv1 _ hs hk hBB1 rfl, hflat]
    have hta' : tauStar_p23 (scsToStableSy_p23 s hs hk3) (flattenRow_p23 vv 4) < 0 := by
      rw [← TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4_p23 s vv _ hs hk hBB rfl]
      exact hta
    exact (hx_min _ hmemVV).trans_lt hta'
  -- the three BBprime conjuncts
  intro hempty
  have hmem : vv1 ∈ BBprimeV39 s := by
    refine ⟨hBB1, ?_, hneg⟩
    intro u hBBu
    rw [TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4_p23 s vv1 _ hs hk hBB1 rfl, hflat,
      TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4_p23 s u _ hs hk hBBu rfl]
    exact hx_min _ (flatten_mem_B_SY1_4 s u hs hk hBBu)
  rw [hempty] at hmem
  exact (Set.mem_empty_iff_false _).mp hmem
  -- DISCHARGES: IS_SCS_STABLE_SYSTEM_p23 + NOT_EMPTY_CASE_4_IS_SCS_p24 +
  -- the HDPLYGY/B_SY1 minimizer on the stable record + IN_NOT_EMPTY_B1_SY_4
  -- + TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4_p23 (negativity transfer).
  -- (FILLED, casebank-close-w1 kit: wiring = HDPLYGY minimizer
  -- (B_SY1_p4_compact_of_fan_p23 + continuousOn_tauStar_p23) on the
  -- post SF-81a+SF-C3 stable record + the five prereq fills + the filled
  -- SF-C3-fixed TAUSTAR bridge. Transitive taint: continuousOn_tauFun_p23 +
  -- bodyClosed_p23 (HDPLYGY-kit NEEDS, giant roots — see CLOSE-PLAN §M0).)

/-! ### C2. The k = 5 witnesses (UXCKFPE.hl:547-995) -/

/-- HOL `NOT_EMPTY_CASE_5_IS_SCS` (UXCKFPE.hl:547). -/
theorem NOT_EMPTY_CASE_5_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s vv) :
    (B_SY1_p4
      (fun i j : Fin 5 => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
      (fun i j : Fin 5 => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))) ≠ ∅ := by

  -- FILL (la23prereq-w1 draft C; LA36 core `inNotEmpty_core_p36` + table glue;
  -- CLEAN)
  have hap : Periodic2 s.a s.k := hs.2.2.2.2.2.2.2.1
  rw [hk] at hap
  have hbp : Periodic2 s.b s.k := hs.2.2.2.2.2.2.2.2.2.2.1
  rw [hk] at hbp
  have htabA : (fun i j : Fin 5 => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      = (fun i j : Fin 5 => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5)) := by
    funext i j
    show s.a ((i : ℕ) + 1) ((j : ℕ) + 1) = _
    exact table_shift_eq_p24 s.a 5 hap (i : ℕ) (j : ℕ) i.isLt j.isLt
  have htabB : (fun i j : Fin 5 => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      = (fun i j : Fin 5 => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5)) := by
    funext i j
    show s.b ((i : ℕ) + 1) ((j : ℕ) + 1) = _
    exact table_shift_eq_p24 s.b 5 hbp (i : ℕ) (j : ℕ) i.isLt j.isLt
  show (B_SY1_p4
    (fun i j : Fin 5 => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
    (fun i j : Fin 5 => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))) ≠ ∅
  rw [← htabA, ← htabB]
  exact Set.nonempty_iff_ne_empty.mp
    ⟨flattenRow_p23 vv 5, inNotEmpty_core_p36 (k := 5) (by omega) hk hBB⟩
  -- DISCHARGES: IN_IS_SCS_CASE_5_p23 (witness `flattenRow_p23 vv 5`).
  -- (filled from the LA23 fill `V_E_FF_IS_SCS_CASES_5_p23` +
  -- `IS_SCS_IN_BALL_ANNULUS_5_p23` + the LA36 core `inNotEmpty_core_p36`.)

/-- HOL `IN_NOT_EMPTY_B1_SY_5_IS_SCS` (UXCKFPE.hl:704). -/
theorem IN_NOT_EMPTY_B1_SY_5_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 5) (hper : Periodic vv 5)
    (hball : ∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun i j : Fin 5 => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
      (fun i j : Fin 5 => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
      (cycRow_p23 vv 5))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 5)) :
    BBsV39 s vv := by

  -- FILL (la23prereq-w1 draft C; LA36 core `inB1_core_p36` + table glue; CLEAN)
  have hap : Periodic2 s.a s.k := hs.2.2.2.2.2.2.2.1
  rw [hk] at hap
  have hbp : Periodic2 s.b s.k := hs.2.2.2.2.2.2.2.2.2.2.1
  rw [hk] at hbp
  have htabA : (fun i j : Fin 5 => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
      = (fun i j : Fin 5 => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1)) := by
    funext i j
    show s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5) = _
    exact (table_shift_eq_p24 s.a 5 hap (i : ℕ) (j : ℕ) i.isLt j.isLt).symm
  have htabB : (fun i j : Fin 5 => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
      = (fun i j : Fin 5 => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
    funext i j
    show s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5) = _
    exact (table_shift_eq_p24 s.b 5 hbp (i : ℕ) (j : ℕ) i.isLt j.isLt).symm
  rw [htabA, htabB] at hC1
  exact inB1_core_p36 (k := 5) (by omega) hk hper
    (fun i j => ⟨periodic2_mod_eq_p24 hap i j, periodic2_mod_eq_p24 hbp i j⟩)
    hball hC1 hC2
  -- DISCHARGES: as `IN_NOT_EMPTY_B1_SY_4_IS_SCS_p24` at k = 5
  -- (V_E_FF_IS_SCS_CASES_5_p23).
  -- (filled from the LA23 fill + the LA36 core `inB1_core_p36`.)

/-- HOL `XWITCCN_CASE_5_IS_SCS` (UXCKFPE.hl:889). -/
theorem XWITCCN_CASE_5_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : s.k = 5)
    (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by

  -- FILL (la24casebank-w1 probe5 assembly + casebank-close-w1
  -- kit; wiring: HDPLYGY minimizer + the five prereq fills + the TAUSTAR
  -- bridge; the only taint entering here is the two HDPLYGY-kit NEEDS
  -- pieces `continuousOn_tauFun_p23` / `bodyClosed_p23` — see CLOSE-PLAN).
  have hk3 : 3 < s.k := by omega
  have hcomp : IsCompact (B_SY1_p4 (aR5 s) (bR5 s) : Set (FinVec 5 3)) :=
    B_SY1_p4_compact_of_fan_p23 (aR5 s) (bR5 s)
      (bodyClosed_p23 (aR5 s) (bR5 s) (by norm_num : 2 < 5)
        (fun i => stabAdj_of_isScsV39 s hs hk hk3 i))
      (bodyBounded_p23 5 (aR5 s) (bR5 s))
  have hd : ContinuousOn (fun l : FinVec 5 3 =>
      dFun_p23 (scsToStableSy_p23 s hs hk3) l) (B_SY1_p4 (aR5 s) (bR5 s)) :=
    (continuous_dFun_p23 _).continuousOn
  have hfun : ContinuousOn (fun l : FinVec 5 3 =>
      tauFun (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (F_SY_p4 (vecmatsV3_p4 l))) (B_SY1_p4 (aR5 s) (bR5 s)) :=
    continuousOn_tauFun_p23 _ _ (by norm_num : 2 < 5)
      (fullStable_of_isScsV39 s hs hk hk3 _ _ (fun _ _ => rfl) (fun _ _ => rfl))
  have hcont : ContinuousOn (tauStar_p23 (scsToStableSy_p23 s hs hk3))
      (B_SY1_p4 (aR5 s) (bR5 s)) :=
    continuousOn_tauStar_p23 _ _ _ hd hfun
  have hne := NOT_EMPTY_CASE_5_IS_SCS_p24 s vv hs hk hBB
  obtain ⟨x, hx_mem, hx_min⟩ :=
    HDPLYGY_p23 (scsToStableSy_p23 s hs hk3) (aR5 s) (bR5 s) hcomp hcont hne
  unfold B_SY1_p4 at hx_mem
  obtain ⟨w, hw, hwx⟩ := hx_mem
  -- the cyclic un-flattening vv1 of the body point w (HOL ABBREV vv1)
  set vv1 : ℕ → V3 := fun i => w ⟨(i + 4) % 5, by omega⟩ with hv1
  have hp5 : Periodic vv1 5 := by
    intro i
    simp only [hv1]
    refine congrArg w (Fin.val_injective ?_)
    simp only [Fin.val_mk]
    omega
  have hcyc : cycRow_p23 vv1 5 = w := by
    funext j
    show vv1 (((j : ℕ) + 1) % 5) = w j
    have hj := j.isLt
    simp only [hv1]
    refine congrArg w (Fin.val_injective ?_)
    simp only [Fin.val_mk]
    omega
  have hflat : flattenRow_p23 vv1 5 = x := by
    funext i
    show (cycRow_p23 vv1 5 ⟨(i : ℕ) / 3, by have := i.isLt; omega⟩ :
        Fin 3 → ℝ) ⟨(i : ℕ) % 3, by omega⟩ = x i
    rw [hcyc]
    exact congrFun hwx i
  have hball : ∀ i : Fin 5, cycRow_p23 vv1 5 i ∈ ballAnnulus := by
    intro i; rw [hcyc]; exact hw.1 i
  have hC1 : CONDITION1_SY_p4 (aR5 s) (bR5 s) (cycRow_p23 vv1 5) := by
    rw [hcyc]; exact hw.2.1
  have hC2 : CONDITION2_SY_p4 (cycRow_p23 vv1 5) := by
    rw [hcyc]; exact hw.2.2
  have hBB1 : BBsV39 s vv1 :=
    IN_NOT_EMPTY_B1_SY_5_IS_SCS_p24 s vv1 hs hk hp5 hball hC1 hC2
  have hmemVV : flattenRow_p23 vv 5 ∈
      (B_SY1_p4 (aR5 s) (bR5 s) : Set (FinVec 5 3)) :=
    flatten_mem_B_SY1_5 s vv hs hk hBB
  -- negativity transfer (TAUSTAR bridge twice + minimizer)
  have hneg : taustarV39 s vv1 < 0 := by
    rw [TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_5_p23 s vv1 _ hs hk hBB1 rfl, hflat]
    have hta' : tauStar_p23 (scsToStableSy_p23 s hs hk3) (flattenRow_p23 vv 5) < 0 := by
      rw [← TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_5_p23 s vv _ hs hk hBB rfl]
      exact hta
    exact (hx_min _ hmemVV).trans_lt hta'
  -- the three BBprime conjuncts
  intro hempty
  have hmem : vv1 ∈ BBprimeV39 s := by
    refine ⟨hBB1, ?_, hneg⟩
    intro u hBBu
    rw [TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_5_p23 s vv1 _ hs hk hBB1 rfl, hflat,
      TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_5_p23 s u _ hs hk hBBu rfl]
    exact hx_min _ (flatten_mem_B_SY1_5 s u hs hk hBBu)
  rw [hempty] at hmem
  exact (Set.mem_empty_iff_false _).mp hmem
  -- DISCHARGES: as `XWITCCN_CASE_4_IS_SCS_p24` at k = 5.
  -- (FILLED, casebank-close-w1 kit: wiring = HDPLYGY minimizer
  -- (B_SY1_p4_compact_of_fan_p23 + continuousOn_tauStar_p23) on the
  -- post SF-81a+SF-C3 stable record + the five prereq fills + the filled
  -- SF-C3-fixed TAUSTAR bridge. Transitive taint: continuousOn_tauFun_p23 +
  -- bodyClosed_p23 (HDPLYGY-kit NEEDS, giant roots — see CLOSE-PLAN §M0).)

/-! ### C3. The k = 6 witnesses (UXCKFPE.hl:1003-1483) -/

/-- HOL `NOT_EMPTY_CASE_6_IS_SCS` (UXCKFPE.hl:1003). -/
theorem NOT_EMPTY_CASE_6_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 6) (hBB : BBsV39 s vv) :
    (B_SY1_p4
      (fun i j : Fin 6 => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
      (fun i j : Fin 6 => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))) ≠ ∅ := by

  -- FILL (la23prereq-w1 draft C; LA36 core `inNotEmpty_core_p36` + table glue;
  -- CLEAN)
  have hap : Periodic2 s.a s.k := hs.2.2.2.2.2.2.2.1
  rw [hk] at hap
  have hbp : Periodic2 s.b s.k := hs.2.2.2.2.2.2.2.2.2.2.1
  rw [hk] at hbp
  have htabA : (fun i j : Fin 6 => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      = (fun i j : Fin 6 => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6)) := by
    funext i j
    show s.a ((i : ℕ) + 1) ((j : ℕ) + 1) = _
    exact table_shift_eq_p24 s.a 6 hap (i : ℕ) (j : ℕ) i.isLt j.isLt
  have htabB : (fun i j : Fin 6 => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      = (fun i j : Fin 6 => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6)) := by
    funext i j
    show s.b ((i : ℕ) + 1) ((j : ℕ) + 1) = _
    exact table_shift_eq_p24 s.b 6 hbp (i : ℕ) (j : ℕ) i.isLt j.isLt
  show (B_SY1_p4
    (fun i j : Fin 6 => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
    (fun i j : Fin 6 => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))) ≠ ∅
  rw [← htabA, ← htabB]
  exact Set.nonempty_iff_ne_empty.mp
    ⟨flattenRow_p23 vv 6, inNotEmpty_core_p36 (k := 6) (by omega) hk hBB⟩
  -- DISCHARGES: IN_IS_SCS_CASE_6_p23 (witness `flattenRow_p23 vv 6`).
  -- (filled from the LA23 fill `V_E_FF_IS_SCS_CASES_6_p23` +
  -- `IS_SCS_IN_BALL_ANNULUS_6_p23` + the LA36 core `inNotEmpty_core_p36`.)

/-- HOL `IN_NOT_EMPTY_B1_SY_6_IS_SCS` (UXCKFPE.hl:1161). -/
theorem IN_NOT_EMPTY_B1_SY_6_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 6) (hper : Periodic vv 6)
    (hball : ∀ i : Fin 6, cycRow_p23 vv 6 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun i j : Fin 6 => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
      (fun i j : Fin 6 => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
      (cycRow_p23 vv 6))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 6)) :
    BBsV39 s vv := by

  -- FILL (la23prereq-w1 draft C; LA36 core `inB1_core_p36` + table glue; CLEAN)
  have hap : Periodic2 s.a s.k := hs.2.2.2.2.2.2.2.1
  rw [hk] at hap
  have hbp : Periodic2 s.b s.k := hs.2.2.2.2.2.2.2.2.2.2.1
  rw [hk] at hbp
  have htabA : (fun i j : Fin 6 => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
      = (fun i j : Fin 6 => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1)) := by
    funext i j
    show s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6) = _
    exact (table_shift_eq_p24 s.a 6 hap (i : ℕ) (j : ℕ) i.isLt j.isLt).symm
  have htabB : (fun i j : Fin 6 => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
      = (fun i j : Fin 6 => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
    funext i j
    show s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6) = _
    exact (table_shift_eq_p24 s.b 6 hbp (i : ℕ) (j : ℕ) i.isLt j.isLt).symm
  rw [htabA, htabB] at hC1
  exact inB1_core_p36 (k := 6) (by omega) hk hper
    (fun i j => ⟨periodic2_mod_eq_p24 hap i j, periodic2_mod_eq_p24 hbp i j⟩)
    hball hC1 hC2
  -- DISCHARGES: as `IN_NOT_EMPTY_B1_SY_4_IS_SCS_p24` at k = 6
  -- (V_E_FF_IS_SCS_CASES_6_p23).
  -- (filled from the LA23 fill + the LA36 core `inB1_core_p36`.)

/-- HOL `XWITCCN_CASE_6_IS_SCS` (UXCKFPE.hl:1374). -/
theorem XWITCCN_CASE_6_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : s.k = 6)
    (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by

  -- FILL (la24casebank-w1 probe5 assembly + casebank-close-w1
  -- kit; wiring: HDPLYGY minimizer + the five prereq fills + the TAUSTAR
  -- bridge; the only taint entering here is the two HDPLYGY-kit NEEDS
  -- pieces `continuousOn_tauFun_p23` / `bodyClosed_p23` — see CLOSE-PLAN).
  have hk3 : 3 < s.k := by omega
  have hcomp : IsCompact (B_SY1_p4 (aR6 s) (bR6 s) : Set (FinVec 6 3)) :=
    B_SY1_p4_compact_of_fan_p23 (aR6 s) (bR6 s)
      (bodyClosed_p23 (aR6 s) (bR6 s) (by norm_num : 2 < 6)
        (fun i => stabAdj_of_isScsV39 s hs hk hk3 i))
      (bodyBounded_p23 6 (aR6 s) (bR6 s))
  have hd : ContinuousOn (fun l : FinVec 6 3 =>
      dFun_p23 (scsToStableSy_p23 s hs hk3) l) (B_SY1_p4 (aR6 s) (bR6 s)) :=
    (continuous_dFun_p23 _).continuousOn
  have hfun : ContinuousOn (fun l : FinVec 6 3 =>
      tauFun (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (F_SY_p4 (vecmatsV3_p4 l))) (B_SY1_p4 (aR6 s) (bR6 s)) :=
    continuousOn_tauFun_p23 _ _ (by norm_num : 2 < 6)
      (fullStable_of_isScsV39 s hs hk hk3 _ _ (fun _ _ => rfl) (fun _ _ => rfl))
  have hcont : ContinuousOn (tauStar_p23 (scsToStableSy_p23 s hs hk3))
      (B_SY1_p4 (aR6 s) (bR6 s)) :=
    continuousOn_tauStar_p23 _ _ _ hd hfun
  have hne := NOT_EMPTY_CASE_6_IS_SCS_p24 s vv hs hk hBB
  obtain ⟨x, hx_mem, hx_min⟩ :=
    HDPLYGY_p23 (scsToStableSy_p23 s hs hk3) (aR6 s) (bR6 s) hcomp hcont hne
  unfold B_SY1_p4 at hx_mem
  obtain ⟨w, hw, hwx⟩ := hx_mem
  -- the cyclic un-flattening vv1 of the body point w (HOL ABBREV vv1)
  set vv1 : ℕ → V3 := fun i => w ⟨(i + 5) % 6, by omega⟩ with hv1
  have hp6 : Periodic vv1 6 := by
    intro i
    simp only [hv1]
    refine congrArg w (Fin.val_injective ?_)
    simp only [Fin.val_mk]
    omega
  have hcyc : cycRow_p23 vv1 6 = w := by
    funext j
    show vv1 (((j : ℕ) + 1) % 6) = w j
    have hj := j.isLt
    simp only [hv1]
    refine congrArg w (Fin.val_injective ?_)
    simp only [Fin.val_mk]
    omega
  have hflat : flattenRow_p23 vv1 6 = x := by
    funext i
    show (cycRow_p23 vv1 6 ⟨(i : ℕ) / 3, by have := i.isLt; omega⟩ :
        Fin 3 → ℝ) ⟨(i : ℕ) % 3, by omega⟩ = x i
    rw [hcyc]
    exact congrFun hwx i
  have hball : ∀ i : Fin 6, cycRow_p23 vv1 6 i ∈ ballAnnulus := by
    intro i; rw [hcyc]; exact hw.1 i
  have hC1 : CONDITION1_SY_p4 (aR6 s) (bR6 s) (cycRow_p23 vv1 6) := by
    rw [hcyc]; exact hw.2.1
  have hC2 : CONDITION2_SY_p4 (cycRow_p23 vv1 6) := by
    rw [hcyc]; exact hw.2.2
  have hBB1 : BBsV39 s vv1 :=
    IN_NOT_EMPTY_B1_SY_6_IS_SCS_p24 s vv1 hs hk hp6 hball hC1 hC2
  have hmemVV : flattenRow_p23 vv 6 ∈
      (B_SY1_p4 (aR6 s) (bR6 s) : Set (FinVec 6 3)) :=
    flatten_mem_B_SY1_6 s vv hs hk hBB
  -- negativity transfer (TAUSTAR bridge twice + minimizer)
  have hneg : taustarV39 s vv1 < 0 := by
    rw [TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_6_p23 s vv1 _ hs hk hBB1 rfl, hflat]
    have hta' : tauStar_p23 (scsToStableSy_p23 s hs hk3) (flattenRow_p23 vv 6) < 0 := by
      rw [← TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_6_p23 s vv _ hs hk hBB rfl]
      exact hta
    exact (hx_min _ hmemVV).trans_lt hta'
  -- the three BBprime conjuncts
  intro hempty
  have hmem : vv1 ∈ BBprimeV39 s := by
    refine ⟨hBB1, ?_, hneg⟩
    intro u hBBu
    rw [TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_6_p23 s vv1 _ hs hk hBB1 rfl, hflat,
      TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_6_p23 s u _ hs hk hBBu rfl]
    exact hx_min _ (flatten_mem_B_SY1_6 s u hs hk hBBu)
  rw [hempty] at hmem
  exact (Set.mem_empty_iff_false _).mp hmem
  -- DISCHARGES: as `XWITCCN_CASE_4_IS_SCS_p24` at k = 6.
  -- (FILLED, casebank-close-w1 kit: wiring = HDPLYGY minimizer
  -- (B_SY1_p4_compact_of_fan_p23 + continuousOn_tauStar_p23) on the
  -- post SF-81a+SF-C3 stable record + the five prereq fills + the filled
  -- SF-C3-fixed TAUSTAR bridge. Transitive taint: continuousOn_tauFun_p23 +
  -- bodyClosed_p23 (HDPLYGY-kit NEEDS, giant roots — see CLOSE-PLAN §M0).)

/-! ### C4. The k = 3 `tri_sy` capstone (UXCKFPE.hl:1488-2597)

The k = 3 body set (no `CONDITION2_SY` at k = 3, verbatim HOL): the
`CONDITION1_SY_p4` bounds on the member's own rows.

SF-80 (2026-10-28): the four body-set builders below were restated from the
lossy `{l | (V i, cycRow_p23 vv 3 i IN ballAnnulus) /\ C1 (cycRow_p23 vv 3)}`
(membership did not constrain `l`: machine-refutable at the zero matrix /
vacuous, see lane_snapshots/sfc1c2draft-w1) to the row-indexed form
`{l | (V i, rowSy_p23 l i IN ballAnnulus) /\ C1 (fun i => rowSy_p23 l i)}` —
the HOL set `{matvec v | (!i. 1<=i <= dimindex(:M) ==> row i v IN
ball_annulus) /\ CONDITION1_SY a b v}` (UXCKFPE.hl:1878/:1926) constrains
the rows of the MEMBER's matvec pre-image.  `IN_NOT_EMPTY_B1_SY_3_IS_SCS_p24`
keeps the cycRow form: its hypotheses are about the specific realisation
`v` (HOL `row i v` of the abbreviated `v = vector[vv 1; vv 2; vv 0]`), not a
set membership.  Statements only — the `sorry` bodies are untouched. -/

/-- HOL `IN_IS_SCS_CASE_3` (UXCKFPE.hl:1502): the k = 3 flattening
`matvec (vector[vv 1; vv 2; vv 0])` lies in the (CONDITION2-free) body.
SF-80: membership constrains the member's own rows, as in HOL. -/
theorem IN_IS_SCS_CASE_3_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    flattenRow_p23 vv 3 ∈
      {l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} := by
  sorry
  -- DISCHARGES: rows-in-annulus via `vecmatsV3_flattenRow_p36` (rows of the
  -- flattening ARE the cyclic row vector: `rowSy_p23 (flattenRow_p23 vv 3) i
  -- = cycRow_p23 vv 3 i`, probe-validated CLEAN in sfc1c2draft-w1
  -- probe80_fix.lean `flattenRow_mem_B3fix`) + the BBsV39 a/b bounds at the
  -- cyclic rows (no fan conjunct needed at k = 3).

/-- HOL `IN_NOT_EMPTY_B1_SY_3_IS_SCS` (UXCKFPE.hl:1701). -/
theorem IN_NOT_EMPTY_B1_SY_3_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hper : Periodic vv 3)
    (hball : ∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
      (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
      (cycRow_p23 vv 3)) :
    BBsV39 s vv := by
  sorry
  -- DISCHARGES: BBsV39 conjunct walk at k = 3 (the `k ≤ 3` fan disjunct
  -- makes CONDITION2 unnecessary, as in the HOL source).

/-- HOL `NOT_EMPTY_CASE_3_IS_SCS` (UXCKFPE.hl:1775).  SF-80: row-indexed
body set. -/
theorem NOT_EMPTY_CASE_3_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    ({l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} : Set (FinVec 3 3)) ≠ ∅ := by
  sorry
  -- DISCHARGES: IN_IS_SCS_CASE_3_p24 (witness `flattenRow_p23 vv 3`).

/-- HOL `J1_TS` (UXCKFPE.hl:1792): the k = 3 ear index set, with the
application-instantiated `f_ts s = (\i. (1+i) MOD 3)` carried as a
parameter `f` (and `J_TS s` as `J`). -/
def J1_TS_p24 (J : Set (Set ℕ)) (f : ℕ → ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ i, {i % 3, f (i % 3)} ∈ J ∧ i ∈ Set.Icc 1 3 ∧ x = (i, i % 3 + 1)}

/-- HOL `d_fun3` (UXCKFPE.hl:1797): the k = 3 ear functional, `d_ts`/ear
flag/`J_TS`/`f_ts` carried as parameters (`d`, `ear`, `J`, `f`). -/
noncomputable def dFun3_p24 (d : ℝ) (ear : Prop) (J : Set (Set ℕ)) (f : ℕ → ℕ)
    (l : FinVec 3 3) : ℝ :=
  d + (1 : ℝ) / 10 * (if ear then 1 else -1) *
    setSum (J1_TS_p24 J f)
      (fun x => cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖)

/-- HOL `FINITE_J1_TS` (UXCKFPE.hl:1801). -/
theorem FINITE_J1_TS_p24 (J : Set (Set ℕ)) (f : ℕ → ℕ) :
    (J1_TS_p24 J f).Finite := by
  refine (Set.finite_range fun i : Fin 3 =>
    ((i : ℕ) + 1, ((i : ℕ) + 1) % 3 + 1)).subset ?_
  rintro x ⟨i, -, hi, rfl⟩
  have h1 : 1 ≤ i := hi.1
  have h3 : i ≤ 3 := hi.2
  refine ⟨⟨i - 1, by omega⟩, ?_⟩
  show ((i - 1 : ℕ) + 1, (i - 1 + 1) % 3 + 1) = (i, i % 3 + 1)
  rw [show i - 1 + 1 = i from by omega]

/-- HOL `CONTINUOUS_ON_D_FUN3` (UXCKFPE.hl:1813): `d_fun3` is continuous
on the k = 3 body set (sum over the finite `J1_TS_p24` of row differences).
SF-80: row-indexed body set. -/
theorem CONTINUOUS_ON_D_FUN3_p24 (s : ScsV39) (hk : s.k = 3)
    (vv : ℕ → V3) :
    ContinuousOn
      (fun l : FinVec 3 3 =>
        dFun3_p24 s.d (isEarV39 s) (scsJSet_p23 s) (fun i => (1 + i) % s.k) l)
      {l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} := by
  sorry
  -- DISCHARGES: setSum over the 3-point FINITE_J1_TS_p24 set of
  -- `cstab - ‖rowSy_p23 l _ - rowSy_p23 l _‖` (continuous in `l`), the
  -- constant `d`/ear terms (HOL CONTINUOUS_ON_ADD/VSUM/ROW kit).

/-- HOL `tri_sy_explicit` (UXCKFPE.hl:1856): the projections of the
`tri_sy (k,d,s,a,b,J,f)` record (↦ `StableSyP23`) return its components. -/
theorem tri_sy_explicit_p24 (k : ℕ) (d : ℝ) (s : Set ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Set (Set ℕ)) (f : ℕ → ℕ) (hs : stableSystem_p23 k 0 s a b J f) :
    ({ k := k, d := d, I := s, a := a, b := b, J := J, f := f,
        stable := hs } : StableSyP23).k = k ∧
      ({ k := k, d := d, I := s, a := a, b := b, J := J, f := f,
          stable := hs } : StableSyP23).d = d ∧
      ({ k := k, d := d, I := s, a := a, b := b, J := J, f := f,
          stable := hs } : StableSyP23).a = a ∧
      ({ k := k, d := d, I := s, a := a, b := b, J := J, f := f,
          stable := hs } : StableSyP23).b = b ∧
      ({ k := k, d := d, I := s, a := a, b := b, J := J, f := f,
          stable := hs } : StableSyP23).J = J ∧
      ({ k := k, d := d, I := s, a := a, b := b, J := J, f := f,
          stable := hs } : StableSyP23).I = s ∧
      ({ k := k, d := d, I := s, a := a, b := b, J := J, f := f,
          stable := hs } : StableSyP23).f = f :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- HOL `IN_B_SY1_COLLINEAR_CASE_3_IS_SCS` (UXCKFPE.hl:1878): the rows of
any k = 3 body point form three non-collinear triples with the origin
(HOL rows `1,2,3` ↦ the `rowSy_p23 l` indices `0,1,2`).  SF-80: the body-set
membership premise is row-indexed — it constrains the member `l` itself, so
the zero-matrix instantiation is excluded (`rowSy_p23 0 i = 0 ∉
ballAnnulus`; probe80_refute_fixed.lean: the old counterexample dies). -/
theorem IN_B_SY1_COLLINEAR_CASE_3_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    ∀ l : FinVec 3 3,
      (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
        CONDITION1_SY_p4
          (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
          (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
          (fun i : Fin 3 => rowSy_p23 l i) →
      ¬ Collinear ℝ ({0, rowSy_p23 l 0, rowSy_p23 l 1} : Set V3) ∧
        ¬ Collinear ℝ ({0, rowSy_p23 l 0, rowSy_p23 l 2} : Set V3) ∧
        ¬ Collinear ℝ ({0, rowSy_p23 l 1, rowSy_p23 l 2} : Set V3) := by
  sorry
  -- DISCHARGES: the row-decoding of IN_NOT_EMPTY_B1_SY_3 (rows of a body
  -- point are a BBs realisation) + IS_SCS_NOT_COLLINEAR_BBs_CASE_3_p23.

/-- HOL `HDPLYGY_CASE_30` (UXCKFPE.hl:1926): the k = 3 minimizer of
`tau3 - d_fun3` over the (compact, nonempty) body set.  SF-80: row-indexed
body set — `hne`/`hnc` are no longer jointly contradictory, the statement
carries real minimizer content. -/
theorem HDPLYGY_CASE_30_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3)
    (hne : ({l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} : Set (FinVec 3 3)) ≠ ∅)
    (hnc : ∀ l : FinVec 3 3,
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i) →
        ¬ Collinear ℝ ({0, rowSy_p23 l 0, rowSy_p23 l 1} : Set V3) ∧
          ¬ Collinear ℝ ({0, rowSy_p23 l 0, rowSy_p23 l 2} : Set V3) ∧
          ¬ Collinear ℝ ({0, rowSy_p23 l 1, rowSy_p23 l 2} : Set V3)) :
    ∃ x : FinVec 3 3,
      (x ∈ ({l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} : Set (FinVec 3 3))) ∧
      ∀ y : FinVec 3 3,
        y ∈ ({l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} : Set (FinVec 3 3)) →
        tau3 (rowSy_p23 x 0) (rowSy_p23 x 1) (rowSy_p23 x 2) -
            dFun3_p24 s.d (isEarV39 s) (scsJSet_p23 s)
              (fun i => (1 + i) % s.k) x ≤
          tau3 (rowSy_p23 y 0) (rowSy_p23 y 1) (rowSy_p23 y 2) -
            dFun3_p24 s.d (isEarV39 s) (scsJSet_p23 s)
              (fun i => (1 + i) % s.k) y := by
  sorry
  -- DISCHARGES: TRI_STABLE_K_EQ_3 + CONTINUOUS_ATTAINS_INF +
  -- COMPACT_TRI_STABLE + CONTINUOUS_ON_D_FUN3_p24 (the HOL rho/ly/interp
  -- continuity chain for `tau3` on rows).

/-- HOL `TAUSTAR_EQ_TAU_STAR_3_IS_SCS` (UXCKFPE.hl:2126): the scs-taustar
at k = 3 is `tau3 (vv 1) (vv 2) (vv 0) - d_fun3`. -/
theorem TAUSTAR_EQ_TAU_STAR_3_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    taustarV39 s vv = tau3 (vv 1) (vv 2) (vv 0) -
      dFun3_p24 s.d (isEarV39 s) (scsJSet_p23 s)
        (fun i => (1 + i) % s.k) (flattenRow_p23 vv 3) := by
  sorry
  -- DISCHARGES: taustarV39 k ≤ 3 branch + dsv_v39 = d_fun3 (the J1_TS
  -- index shift via `Periodic2 s.J 3`, IS_SCS_TRI_STABLE_SYSTEM_p23) +
  -- the flattenRow_p23 row/entry identity on `vv 1, vv 2, vv 0`.

/-- HOL `XWITCCN_CASE_3_IS_SCS` (UXCKFPE.hl:2495). -/
theorem XWITCCN_CASE_3_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : s.k = 3)
    (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by
  sorry
  -- DISCHARGES: IS_SCS_TRI_STABLE_SYSTEM_p23 + NOT_EMPTY_CASE_3_IS_SCS_p24
  -- + IN_B_SY1_COLLINEAR_CASE_3_IS_SCS_p24 + HDPLYGY_CASE_30_p24 +
  -- IN_NOT_EMPTY_B1_SY_3_IS_SCS_p24 + TAUSTAR_EQ_TAU_STAR_3_IS_SCS_p24.

/-- HOL `UXCKFPE` (UXCKFPE.hl:2602): the k = 3..6 case assembly
(the HOL `INST_TYPE` moves become this case split; `isScsV39` gives
`3 ≤ k ≤ 6`). -/
theorem UXCKFPE_p24 (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by
  have h3 : 3 ≤ s.k := hs.2.1
  have h6 : s.k ≤ 6 := hs.2.2.1
  rcases (by omega : s.k = 3 ∨ s.k = 4 ∨ s.k = 5 ∨ s.k = 6) with hk | hk | hk | hk
  · exact XWITCCN_CASE_3_IS_SCS_p24 s vv hs hBB hk hta
  · exact XWITCCN_CASE_4_IS_SCS_p24 s vv hs hBB hk hta
  · exact XWITCCN_CASE_5_IS_SCS_p24 s vv hs hBB hk hta
  · exact XWITCCN_CASE_6_IS_SCS_p24 s vv hs hBB hk hta
/-! ## Section B7 (la24-b3masters-w3): the `5I3 → 5M1` twin chain

The Section B5 skeleton items `MM_5I3_IMP_MM_5M1`, `STAB_5I3_ARROW_STAB_5M1`
and `STAB_5I3_ARROW_STAB_5M1_DIAG` are MOVED here verbatim (statements
byte-identical to their Section B5 forms): their discharges consume
`XWITCCN_CASE_5_IS_SCS_p24` (declared in Section C2 above), so they must
textually follow it. The private `_p24` kit clones `UXCKFPE2`/`SGTRNAF`
(LA27 Section D, UXCKFPE2_p27 文体; single case-bank root
`XWITCCN_CASE_5_IS_SCS_p24`), inlines the `unadorned_MMs` conversion
(LA27 SGTRNAF_p27 文体), clones the taustar `d`-monotonicity
(`dsv_J_empty` route) and the `Ppbtydq.XWNHLMD_MM` transfer. -/

/-- `dsvV39 s v ≤ dsvV39 s' v` for the `J`-empty basic systems with
`s.d ≤ s'.d` (`SCS_BASIC_DSV_p26` clone, LA26). -/
private theorem la24dsv_le_p24 (s s' : ScsV39) (v : ℕ → V3)
    (hb : scsBasicV39 s) (hb' : scsBasicV39 s') (hds : s.d ≤ s'.d) :
    dsvV39 s v ≤ dsvV39 s' v := by
  have hJ : s.J = fun _ _ => False := funext fun i => funext fun j => hb.2 i j
  have hJ' : s'.J = fun _ _ => False := funext fun i => funext fun j => hb'.2 i j
  rw [dsv_J_empty s v hJ, dsv_J_empty s' v hJ']
  exact hds

/-- Taustar monotonicity under `d` (`SCS_BASIC_TAUSTAR_p26` clone, LA26). -/
private theorem la24taustar_mono_p24 (s s' : ScsV39) (v : ℕ → V3)
    (hb : scsBasicV39 s) (hb' : scsBasicV39 s') (hk : s.k = s'.k)
    (hds : s.d ≤ s'.d) : taustarV39 s' v ≤ taustarV39 s v := by
  have hdsv : dsvV39 s v ≤ dsvV39 s' v := la24dsv_le_p24 s s' v hb hb' hds
  unfold taustarV39
  rw [hk]
  by_cases h3 : s'.k ≤ 3
  · simp [h3]
    nlinarith
  · simp [h3]
    nlinarith

/-- A minimal `MMsV39 s` member keeps `taustarV39 s' v < 0` when
`s.d ≤ s'.d` (`TAUSTAR_LE_0_XWNHLMD_p26` clone, LA26). -/
private theorem la24taustar_lt_p24 (s s' : ScsV39) (v : ℕ → V3)
    (hb : scsBasicV39 s) (hb' : scsBasicV39 s') (hk : s.k = s'.k)
    (hv : v ∈ MMsV39 s) (hds : s.d ≤ s'.d) : taustarV39 s' v < 0 := by
  have h0 : taustarV39 s v < 0 := hv.1.1.2.2
  exact lt_of_le_of_lt (la24taustar_mono_p24 s s' v hb hb' hk hds) h0

/-- `UXCKFPE2` + `SGTRNAF` (LA27 Section D) cloned at `k = 5`:
`XWITCCN_CASE_5_IS_SCS_p24` gives `BBprimeV39 s ≠ ∅`, the index image is a
nonempty set of naturals, its least element (`BBindexMinV39`) is attained,
and the attaining witness lands in `BBprime2V39 s`; the `unadorned_MMs`
conversion (AYQJTMD.hl:161) is inlined (LA27 SGTRNAF_p27 文体). Single
case-bank root: `XWITCCN_CASE_5_IS_SCS_p24`. -/
private theorem la24sgtrnaf5_p24 (s : ScsV39) (vv : ℕ → V3) (hk : s.k = 5)
    (hs : isScsV39 s) (hu : unadornedV39 s) (hBB : BBsV39 s vv)
    (hta : taustarV39 s vv < 0) : MMsV39 s ≠ ∅ := by
  have hbp : (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ :=
    XWITCCN_CASE_5_IS_SCS_p24 s vv hs hBB hk hta
  have himage : (BBindexV39 s '' BBprimeV39 s).Nonempty := by
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hbp
    exact ⟨BBindexV39 s w, w, hw, rfl⟩
  have hmin : BBindexMinV39 s ∈ BBindexV39 s '' BBprimeV39 s ∧
      ∀ m ∈ BBindexV39 s '' BBprimeV39 s, BBindexMinV39 s ≤ m :=
    Classical.epsilon_spec (p := fun n => n ∈ BBindexV39 s '' BBprimeV39 s ∧
      ∀ m ∈ BBindexV39 s '' BBprimeV39 s, n ≤ m)
      ⟨sInf _, Nat.sInf_mem himage, fun m hm => Nat.sInf_le hm⟩
  obtain ⟨w, hwprime, hwidx⟩ := hmin.1
  obtain ⟨hlo, hhi, hstr, ham, hbm⟩ := hu
  intro hcon
  rw [Set.eq_empty_iff_forall_notMem] at hcon
  exact hcon w ⟨⟨hwprime, hwidx⟩,
    fun i hi => by rw [hstr] at hi; exact hi.elim,
    fun i hi => by rw [hlo] at hi; exact hi.elim,
    fun i hi => by rw [hhi] at hi; exact hi.elim,
    fun i j => by rw [← ham]; exact (hwprime.1.2.2.1 i j).1,
    fun i j => by rw [← hbm]; exact (hwprime.1.2.2.1 i j).2⟩

/-- `Ppbtydq.XWNHLMD_MM` clone (LA26 route): a minimal `MMsV39 s` member
transfers to `MMsV39 s' ≠ ∅` through `BBsV39 s'` when `s.d ≤ s'.d`, via
`la24taustar_lt_p24` + `la24sgtrnaf5_p24`. -/
private theorem la24xwnhlmd_mm_p24 (s s' : ScsV39) (v : ℕ → V3)
    (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hk : s.k = s'.k) (hk5 : s'.k = 5) (hv : v ∈ MMsV39 s)
    (hv' : BBsV39 s' v) (hds : s.d ≤ s'.d) : MMsV39 s' ≠ ∅ :=
  la24sgtrnaf5_p24 s' v hk5 hs' hb'.1 hv'
    (la24taustar_lt_p24 s s' v hb hb' hk hv hds)

/-- Cell table: the `5M2` `b`-bound dominates the `5I3` `b`-bound
(`sqrt 8 ≤ cstab` on the `(0, 1)` class, other classes equal). 25-cell
sweep over the mod-5 residues (LA20 `funlist_mod_p20` reduction). -/
private theorem la24cellsB_5I3_p24 :
    ∀ p q : ℕ, p < 5 → q < 5 →
      funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
          ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 p q
        ≤ funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
          ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 p q := by
  intro p q hp hq
  interval_cases p <;> interval_cases q <;>
    simp [funlistV39, psort, assocdV39, sqrt8_LE_CSTAB]

/-- `BBs` domination at an arbitrary `k = 5` diagonal class: the stab of
`scs_5I3` at `(i, j)` is dominated by the stab of `scs_5M1` at the same
class (generalisation of the proved `BB_5I3_IS_BB_5M1`, which is fixed at
`(2, 4)`; the stabilised `b`-slot is `cstab` on both sides, so the sweep
reduces to the unstabilised table comparison `la24cellsB_5I3_p24`). -/
private theorem la24bb_diag_gen_p24 (i j : ℕ) (hd : scsDiag 5 i j) (v : ℕ → V3)
    (h : BBsV39 (scsStabDiagV39 scs5I3 i j) v) :
    BBsV39 (scsStabDiagV39 scs5M1 i j) v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, h4⟩
  intro p q
  obtain ⟨hle1, hle2⟩ := h3 p q
  refine ⟨hle1, ?_⟩
  have hb3 : (scsStabDiagV39 scs5I3 i j).b p q =
      if psort 5 (i, j) = psort 5 (p, q) then cstab else scs5I3.b p q := rfl
  have hb1 : (scsStabDiagV39 scs5M1 i j).b p q =
      if psort 5 (i, j) = psort 5 (p, q) then cstab else scs5M1.b p q := rfl
  have hcell : scs5I3.b p q ≤ scs5M1.b p q := by
    show funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
        ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 p q ≤
      funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 p q
    rw [← funlist_mod_p20 _ _ 5 p q (by omega),
        ← funlist_mod_p20 _ _ 5 p q (by omega)]
    exact la24cellsB_5I3_p24 (p % 5) (q % 5) (Nat.mod_lt p (by omega))
      (Nat.mod_lt q (by omega))
  by_cases hC : psort 5 (i, j) = psort 5 (p, q)
  · rw [hb3, if_pos hC] at hle2
    rw [hb1, if_pos hC]
    exact hle2
  · rw [hb3, if_neg hC] at hle2
    rw [hb1, if_neg hC]
    exact le_trans hle2 hcell

/-- HOL `MM_5I3_IMP_MM_5M1` (OTMTOTJ.hl:1238). -/
theorem MM_5I3_IMP_MM_5M1 (v : ℕ → V3) (i j : ℕ) (hd : scsDiag 5 i j)
    (h : v ∈ MMsV39 (scsStabDiagV39 scs5I3 i j)) :
    (MMsV39 (scsStabDiagV39 scs5M1 i j) : Set (ℕ → V3)) ≠ ∅ := by
  refine la24xwnhlmd_mm_p24 (scsStabDiagV39 scs5I3 i j)
    (scsStabDiagV39 scs5M1 i j) v ((STAB_5M1_SCS i j hd).1)
    ((STAB_5I3_SCS i j hd).2) ((STAB_5M1_SCS i j hd).2) rfl
    (rfl : (scsStabDiagV39 scs5M1 i j).k = 5) h
    (la24bb_diag_gen_p24 i j hd v h.1.1.1) (le_refl _)
  -- DISCHARGES: Ppbtydq.XWNHLMD_MM + Nuxcoea.MMS_IMP_BBS + BB_5I3_IS_BB_5M1 +
  -- STAB_5I3_SCS + STAB_5M1_SCS + SCS_K_D_A_STAB_EQ.

/-- HOL `STAB_5I3_ARROW_STAB_5M1` (OTMTOTJ.hl:1251). -/
theorem STAB_5I3_ARROW_STAB_5M1 (i j : ℕ) (hd : scsDiag 5 i j) :
    scsArrowV39 {scsStabDiagV39 scs5I3 i j} {scsStabDiagV39 scs5M1 i j} := by
  refine ⟨fun s hs => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hs
    subst s
    exact (STAB_5M1_SCS i j hd).1
  · by_cases hE : ∀ s ∈ ({scsStabDiagV39 scs5I3 i j} : Set ScsV39), MMsV39 s = ∅
    · exact Or.inl hE
    · push_neg at hE
      obtain ⟨s, hs, hne⟩ := hE
      rw [Set.mem_singleton_iff] at hs
      subst s
      obtain ⟨v, hv⟩ := hne
      exact Or.inr ⟨scsStabDiagV39 scs5M1 i j, Set.mem_singleton _,
        MM_5I3_IMP_MM_5M1 v i j hd hv⟩
  -- DISCHARGES: BB_5I3_IS_BB_5M1 + STAB_5I3_SCS + STAB_5M1_SCS +
  -- MM_5I3_IMP_MM_5M1 + SCS_K_D_A_STAB_EQ.

/-- HOL `STAB_5I3_ARROW_STAB_5M1_DIAG` (OTMTOTJ.hl:1361). -/
theorem STAB_5I3_ARROW_STAB_5M1_DIAG :
    scsArrowV39 {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I3 i j}
      {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5M1 i j} := by
  refine ⟨fun s hs => ?_, ?_⟩
  · obtain ⟨i, j, hd, rfl⟩ := hs
    exact (STAB_5M1_SCS i j hd).1
  · by_cases hE : ∀ s ∈ {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I3 i j},
      MMsV39 s = ∅
    · exact Or.inl hE
    · push_neg at hE
      obtain ⟨s, ⟨i, j, hd, rfl⟩, hne⟩ := hE
      obtain ⟨v, hv⟩ := hne
      exact Or.inr ⟨scsStabDiagV39 scs5M1 i j, ⟨i, j, hd, rfl⟩,
        MM_5I3_IMP_MM_5M1 v i j hd hv⟩
  -- DISCHARGES: SET_STAB_5I3 + SET_STAB_5M1 + DIAG_EQ_ADD5 +
  -- EXPAND_STAB_DIAG_5I3 + EXPAND_STAB_DIAG_5M1 + STAB_5I3_ARROW_STAB_5M1
  -- + FZIOTEF_UNION.


/-! ## Section B6.5 (sweep-b24-w2): the `5x → 5M2` transfers and the moved
`MM`/`BERAK`/`OTMTOTJ1`/`OTMTOTJ2` blocks

The four HOL `MM_5x_IMP_MM_5M2` arrows (OTMTOTJ.hl:223/337/462/535) are
MOVED here (statements byte-identical to their Section B1 forms; 2026-11-02
SF-90 restated the conclusions to the HOL-faithful `MMs_v39 scs_5M2 ≠ {}`)
because their discharges consume the Section B7 `XWNHLMD_MM` private kit;
the Section B3 `BERAK` arrows and the Section B6 masters `OTMTOTJ1`/`OTMTOTJ2`
follow them for the same linear-dependency reason (B3 consumes the `MM`
arrows, `OTMTOTJ1`/`OTMTOTJ2` consume the `5I1`/`5I2` `BERAK`s). -/

/-! ### B2.9 (sweep-b24): the private `5x → 5M2` transfer kit

The HOL `MM_5x_IMP_MM_5M2` (OTMTOTJ.hl:223/337/462/535) concludes
`~(MMs_v39 scs_5M2 = {})`; this kit discharges exactly that content through
the Section B7 `XWNHLMD_MM` route (`la24xwnhlmd_mm_p24`): the `5M2` `b`-table
dominates the source `b`-table (only the `(0,1)` class differs,
`2*h0 ≤ cstab`), and the `cstab` diagonal hypothesis repairs the `5M2`
`a`-side; `dTame 5 = 0.4819 ≤ 0.616` transfers the negative taustar. -/

/-- The `5M2` `a`-table is the `csAdj 5 2 cstab` shape (25-cell sweep
over the mod-reduced residues). -/
private theorem swb_a5M2_csAdj_p24 (i j : ℕ) :
    scs5M2.a i j = csAdj 5 2 cstab i j := by
  have ha : scs5M2.a i j = funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab),
      ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 5 i j := rfl
  rw [ha, ← funlist_mod_p20 _ _ 5 i j (by omega), ← swb_csAdj_mod_p24]
  have hi5 : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hj5 : j % 5 < 5 := Nat.mod_lt j (by omega)
  interval_cases i % 5 <;> interval_cases j % 5 <;>
    simp [funlistV39, psort, assocdV39, csAdj]

/-- The `5M2` `b`-table dominates `csAdj 5 (2*h0) 6` (the `5I1`/`5I2`
`b`-table): 25-cell sweep over the mod-reduced residues. -/
private theorem swb_b_csAdj_le_5M2_p24 (i j : ℕ) :
    csAdj 5 (2 * h0) 6 i j ≤ scs5M2.b i j := by
  have hb : scs5M2.b i j = funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6),
      ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i j := rfl
  rw [hb, ← funlist_mod_p20 _ _ 5 i j (by omega), ← swb_csAdj_mod_p24]
  have hi5 : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hj5 : j % 5 < 5 := Nat.mod_lt j (by omega)
  interval_cases i % 5 <;> interval_cases j % 5 <;>
    simp [funlistV39, psort, assocdV39, csAdj] <;> norm_num [h0, cstab]

/-- The `5I3` `b`-table is dominated by the `5M2` `b`-table (only the
`(0,1)` class differs, `sqrt 8 ≤ cstab`; `la24cellsB_5I3_p24` sweep). -/
private theorem swb_b_5I3_le_5M2_p24 (i j : ℕ) : scs5I3.b i j ≤ scs5M2.b i j := by
  have h1 : scs5I3.b i j = funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6),
      ((0, 3), 6), ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i j := rfl
  have h2 : scs5M2.b i j = funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6),
      ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i j := rfl
  rw [h1, h2, ← funlist_mod_p20 _ _ 5 i j (by omega),
    ← funlist_mod_p20 _ _ 5 i j (by omega)]
  exact la24cellsB_5I3_p24 (i % 5) (j % 5) (Nat.mod_lt i (by omega))
    (Nat.mod_lt j (by omega))

/-- The `cstab` diagonal hypothesis transported to a diagonal `a`-slot
(residue reduction + periodicity). -/
private theorem swb_hc_diag_p24 (v : ℕ → V3) (hp : Periodic v 5)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j))
    (i j : ℕ) (h1 : ¬(i % 5 = j % 5))
    (h2 : ¬(j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5)) :
    cstab ≤ dist (v i) (v j) := by
  exact hc i j ⟨h1, fun hh => h2 (Or.inl hh.symm),
    fun hh => h2 (Or.inr hh.symm)⟩

/-- Edge-slot `2`-bound out of a `csAdj 5 2 a1`-shaped source `a`-table. -/
private theorem swb_hed_csAdj_p24 {a1 : ℝ} (v : ℕ → V3)
    (hs : ∀ i j : ℕ, csAdj 5 2 a1 i j ≤ dist (v i) (v j))
    (i j : ℕ) (h1 : ¬(i % 5 = j % 5))
    (h2 : j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5) :
    2 ≤ dist (v i) (v j) := by
  have h := hs i j
  unfold csAdj at h
  rw [if_neg h1, if_pos h2] at h
  exact h

/-- Edge-slot `2`-bound out of the `5I3` funlist `a`-table. -/
private theorem swb_hed_5I3_p24 (v : ℕ → V3)
    (hs : ∀ i j : ℕ, scs5I3.a i j ≤ dist (v i) (v j))
    (i j : ℕ) (h1 : ¬(i % 5 = j % 5))
    (h2 : j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5) :
    2 ≤ dist (v i) (v j) := by
  have h := hs i j
  have ha : scs5I3.a i j = funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0),
      ((0, 3), 2 * h0), ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5
      (i % 5) (j % 5) :=
    (funlist_mod_p20 _ _ 5 i j (by omega)).symm
  rw [ha] at h
  rw [(Nat.mod_add_mod i 5 1).symm, (Nat.mod_add_mod j 5 1).symm] at h2
  have hi5 : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hj5 : j % 5 < 5 := Nat.mod_lt j (by omega)
  interval_cases i % 5 <;> interval_cases j % 5 <;>
    first
      | exact absurd rfl h1
      | (exfalso; simp at h2; exact (h2 : False).elim)
      | (simp only [funlistV39, psort, assocdV39] at h;
          first | exact h | exact le_trans two_lt_two_h0'.le h)

/-- Edge-slot `2`-bound out of the `5M1` funlist `a`-table. -/
private theorem swb_hed_5M1_p24 (v : ℕ → V3)
    (hs : ∀ i j : ℕ, scs5M1.a i j ≤ dist (v i) (v j))
    (i j : ℕ) (h1 : ¬(i % 5 = j % 5))
    (h2 : j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5) :
    2 ≤ dist (v i) (v j) := by
  have h := hs i j
  have ha : scs5M1.a i j = funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0),
      ((0, 3), 2 * h0), ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5
      (i % 5) (j % 5) :=
    (funlist_mod_p20 _ _ 5 i j (by omega)).symm
  rw [ha] at h
  rw [(Nat.mod_add_mod i 5 1).symm, (Nat.mod_add_mod j 5 1).symm] at h2
  have hi5 : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hj5 : j % 5 < 5 := Nat.mod_lt j (by omega)
  interval_cases i % 5 <;> interval_cases j % 5 <;>
    first
      | exact absurd rfl h1
      | (exfalso; simp at h2; exact (h2 : False).elim)
      | (simp only [funlistV39, psort, assocdV39] at h;
          first | exact h | exact le_trans two_lt_two_h0'.le h)

/-- `BBsV39`-level transfer `5I1 → 5M2` (`BB_5I1_IS_BB_5M2` content,
OTMTOTJ.hl:207). -/
private theorem swb_bb_5I1_5M2_p24 (v : ℕ → V3) (h : BBsV39 scs5I1 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  obtain ⟨hr, hp, hbd, hfan⟩ := h
  refine ⟨hr, hp, fun i j => ?_, hfan⟩
  constructor
  · rw [swb_a5M2_csAdj_p24]
    unfold csAdj
    by_cases h1 : i % 5 = j % 5
    · rw [if_pos h1]; exact dist_nonneg
    rw [if_neg h1]
    by_cases h2 : j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5
    · rw [if_pos h2]
      exact swb_hed_csAdj_p24 v (fun i j => (hbd i j).1) i j h1 h2
    · rw [if_neg h2]
      exact swb_hc_diag_p24 v hp hc i j h1 h2
  · exact le_trans (hbd i j).2 (swb_b_csAdj_le_5M2_p24 i j)

/-- `BBsV39`-level transfer `5I2 → 5M2` (same `b`-table as `5I1`). -/
private theorem swb_bb_5I2_5M2_p24 (v : ℕ → V3) (h : BBsV39 scs5I2 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  obtain ⟨hr, hp, hbd, hfan⟩ := h
  refine ⟨hr, hp, fun i j => ?_, hfan⟩
  constructor
  · rw [swb_a5M2_csAdj_p24]
    unfold csAdj
    by_cases h1 : i % 5 = j % 5
    · rw [if_pos h1]; exact dist_nonneg
    rw [if_neg h1]
    by_cases h2 : j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5
    · rw [if_pos h2]
      exact swb_hed_csAdj_p24 v (fun i j => (hbd i j).1) i j h1 h2
    · rw [if_neg h2]
      exact swb_hc_diag_p24 v hp hc i j h1 h2
  · exact le_trans (hbd i j).2 (swb_b_csAdj_le_5M2_p24 i j)

/-- `BBsV39`-level transfer `5I3 → 5M2`. -/
private theorem swb_bb_5I3_5M2_p24 (v : ℕ → V3) (h : BBsV39 scs5I3 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  obtain ⟨hr, hp, hbd, hfan⟩ := h
  refine ⟨hr, hp, fun i j => ?_, hfan⟩
  constructor
  · rw [swb_a5M2_csAdj_p24]
    unfold csAdj
    by_cases h1 : i % 5 = j % 5
    · rw [if_pos h1]; exact dist_nonneg
    rw [if_neg h1]
    by_cases h2 : j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5
    · rw [if_pos h2]
      exact swb_hed_5I3_p24 v (fun i j => (hbd i j).1) i j h1 h2
    · rw [if_neg h2]
      exact swb_hc_diag_p24 v hp hc i j h1 h2
  · exact le_trans (hbd i j).2 (swb_b_5I3_le_5M2_p24 i j)

/-- `BBsV39`-level transfer `5M1 → 5M2` (identical `b`-tables). -/
private theorem swb_bb_5M1_5M2_p24 (v : ℕ → V3) (h : BBsV39 scs5M1 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  obtain ⟨hr, hp, hbd, hfan⟩ := h
  refine ⟨hr, hp, fun i j => ?_, hfan⟩
  constructor
  · rw [swb_a5M2_csAdj_p24]
    unfold csAdj
    by_cases h1 : i % 5 = j % 5
    · rw [if_pos h1]; exact dist_nonneg
    rw [if_neg h1]
    by_cases h2 : j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5
    · rw [if_pos h2]
      exact swb_hed_5M1_p24 v (fun i j => (hbd i j).1) i j h1 h2
    · rw [if_neg h2]
      exact swb_hc_diag_p24 v hp hc i j h1 h2
  · exact le_trans (hbd i j).2 (le_of_eq rfl)


/-- HOL `MM_5I1_IMP_MM_5M2` (OTMTOTJ.hl:223). -/
theorem MM_5I1_IMP_MM_5M2 (v : ℕ → V3) (h : v ∈ MMsV39 scs5I1)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    MMsV39 scs5M2 ≠ ∅ :=
  la24xwnhlmd_mm_p24 scs5I1 scs5M2 v SCS_5M2_IS_SCS SCS_5I1_BASIC SCS_5M2_BASIC
    rfl rfl h (swb_bb_5I1_5M2_p24 v h.1.1.1 hc)
    (by show dTame 5 ≤ 0.616; norm_num [dTame])
  -- DISCHARGES: `Ppbtydq.XWNHLMD_MM` route (`la24xwnhlmd_mm_p24` at the
  -- `scs5I1` instance, via the private `swb_bb_5I1_5M2_p24` `b`-domination
  -- + `hc` `a`-repair); witness is the `BBindex`-minimized `w` of
  -- `la24sgtrnaf5_p24`, not `v`. Axiom root: `XWITCCN_CASE_5_IS_SCS_p24`.
/-- HOL `MM_5I2_IMP_MM_5M2` (OTMTOTJ.hl:337). -/
theorem MM_5I2_IMP_MM_5M2 (v : ℕ → V3) (h : v ∈ MMsV39 scs5I2)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    MMsV39 scs5M2 ≠ ∅ :=
  la24xwnhlmd_mm_p24 scs5I2 scs5M2 v SCS_5M2_IS_SCS SCS_5I2_BASIC SCS_5M2_BASIC
    rfl rfl h (swb_bb_5I2_5M2_p24 v h.1.1.1 hc)
    (by simp only [scs5I2, scs5M2, mkUnadornedV39]; norm_num)
  -- DISCHARGES: as `MM_5I1_IMP_MM_5M2`, at the `scs5I2` instance.
/-- HOL `MM_5I3_IMP_MM_5M2` (OTMTOTJ.hl:462). -/
theorem MM_5I3_IMP_MM_5M2 (v : ℕ → V3) (h : v ∈ MMsV39 scs5I3)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    MMsV39 scs5M2 ≠ ∅ :=
  la24xwnhlmd_mm_p24 scs5I3 scs5M2 v SCS_5M2_IS_SCS SCS_5I3_BASIC SCS_5M2_BASIC
    rfl rfl h (swb_bb_5I3_5M2_p24 v h.1.1.1 hc)
    (by simp only [scs5I3, scs5M2, mkUnadornedV39]; norm_num)
  -- DISCHARGES: as `MM_5I1_IMP_MM_5M2`, at the `scs5I3` instance (the
  -- `b`-domination via `la24cellsB_5I3_p24`).
/-- HOL `MM_5M1_IMP_MM_5M2` (OTMTOTJ.hl:535). -/
theorem MM_5M1_IMP_MM_5M2 (v : ℕ → V3) (h : v ∈ MMsV39 scs5M1)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    MMsV39 scs5M2 ≠ ∅ :=
  la24xwnhlmd_mm_p24 scs5M1 scs5M2 v SCS_5M2_IS_SCS SCS_5M1_BASIC SCS_5M2_BASIC
    rfl rfl h (swb_bb_5M1_5M2_p24 v h.1.1.1 hc)
    (by simp only [scs5M1, scs5M2, mkUnadornedV39]; norm_num)
  -- DISCHARGES: as `MM_5I1_IMP_MM_5M2`, at the `scs5M1` instance.

/-! ### B3. The `BERAK` arrows (OTMTOTJ.hl:699-954) -/

/-- HOL `SCS_5I1_BERAK_BY_CSTAB` (OTMTOTJ.hl:699). -/
theorem SCS_5I1_BERAK_BY_CSTAB :
    scsArrowV39 {scs5I1} ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5I1 i j}) := by
  refine ⟨fun s hs => ?_, ?_⟩
  · rcases (Set.mem_union _ _ _).mp hs with hs | ⟨i, j, hd, rfl⟩
    · rw [Set.mem_singleton_iff] at hs
      subst s
      exact SCS_5M2_IS_SCS
    · have hk3 : (3 : ℕ) < scs5I1.k := by show (3 : ℕ) < 5; norm_num
      exact (YRTAFYH_concl scs5I1 i j SCS_5I1_IS_SCS SCS_5I1_BASIC hk3 hd
        (la24a5I1_le_cstab_p24 i j)).1
  · by_cases hE : ∀ s ∈ ({scs5I1} : Set ScsV39), MMsV39 s = ∅
    · exact Or.inl hE
    · push_neg at hE
      obtain ⟨s, hs, hne⟩ := hE
      rw [Set.mem_singleton_iff] at hs
      subst s
      obtain ⟨v, hv⟩ := hne
      by_cases hdiag : ∀ i j : ℕ, scsDiag 5 i j → cstab < dist (v i) (v j)
      · refine Or.inr ⟨scs5M2, Set.mem_union_left _ (Set.mem_singleton scs5M2), ?_⟩
        exact MM_5I1_IMP_MM_5M2 v hv fun i j hdij => le_of_lt (hdiag i j hdij)
      · push_neg at hdiag
        obtain ⟨i, j, hdij, hle⟩ := hdiag
        refine Or.inr ⟨scsStabDiagV39 scs5I1 i j, ?_, ?_⟩
        · simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
          exact Or.inr ⟨i, j, hdij, rfl⟩
        · intro hcon
          rw [Set.eq_empty_iff_forall_notMem] at hcon
          exact hcon v (SCS_5I1_STAB_DIAG v i j hv hdij hle)

/-- HOL `SCS_5I2_BERAK_BY_CSTAB` (OTMTOTJ.hl:761). -/
theorem SCS_5I2_BERAK_BY_CSTAB :
    scsArrowV39 {scs5I2} ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5I2 i j}) := by
  refine ⟨fun s hs => ?_, ?_⟩
  · rcases (Set.mem_union _ _ _).mp hs with hs | ⟨i, j, hd, rfl⟩
    · rw [Set.mem_singleton_iff] at hs
      subst s
      exact SCS_5M2_IS_SCS
    · have hk3 : (3 : ℕ) < scs5I2.k := by show (3 : ℕ) < 5; norm_num
      exact (YRTAFYH_concl scs5I2 i j SCS_5I2_IS_SCS SCS_5I2_BASIC hk3 hd
        (la24a5I2_le_cstab_p24 i j)).1
  · by_cases hE : ∀ s ∈ ({scs5I2} : Set ScsV39), MMsV39 s = ∅
    · exact Or.inl hE
    · push_neg at hE
      obtain ⟨s, hs, hne⟩ := hE
      rw [Set.mem_singleton_iff] at hs
      subst s
      obtain ⟨v, hv⟩ := hne
      by_cases hdiag : ∀ i j : ℕ, scsDiag 5 i j → cstab < dist (v i) (v j)
      · refine Or.inr ⟨scs5M2, Set.mem_union_left _ (Set.mem_singleton scs5M2), ?_⟩
        exact MM_5I2_IMP_MM_5M2 v hv fun i j hdij => le_of_lt (hdiag i j hdij)
      · push_neg at hdiag
        obtain ⟨i, j, hdij, hle⟩ := hdiag
        refine Or.inr ⟨scsStabDiagV39 scs5I2 i j, ?_, ?_⟩
        · simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
          exact Or.inr ⟨i, j, hdij, rfl⟩
        · intro hcon
          rw [Set.eq_empty_iff_forall_notMem] at hcon
          exact hcon v (SCS_5I2_STAB_DIAG v i j hv hdij hle)

/-- HOL `SCS_5I3_BERAK_BY_CSTAB` (OTMTOTJ.hl:826). -/
theorem SCS_5I3_BERAK_BY_CSTAB :
    scsArrowV39 {scs5I3} ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5I3 i j}) := by
  refine ⟨fun s hs => ?_, ?_⟩
  · rcases (Set.mem_union _ _ _).mp hs with hs | ⟨i, j, hd, rfl⟩
    · rw [Set.mem_singleton_iff] at hs
      subst s
      exact SCS_5M2_IS_SCS
    · have hk3 : (3 : ℕ) < scs5I3.k := by show (3 : ℕ) < 5; norm_num
      exact (YRTAFYH_concl scs5I3 i j SCS_5I3_IS_SCS SCS_5I3_BASIC hk3 hd
        (la24a5I3_le_cstab_p24 i j)).1
  · by_cases hE : ∀ s ∈ ({scs5I3} : Set ScsV39), MMsV39 s = ∅
    · exact Or.inl hE
    · push_neg at hE
      obtain ⟨s, hs, hne⟩ := hE
      rw [Set.mem_singleton_iff] at hs
      subst s
      obtain ⟨v, hv⟩ := hne
      by_cases hdiag : ∀ i j : ℕ, scsDiag 5 i j → cstab < dist (v i) (v j)
      · refine Or.inr ⟨scs5M2, Set.mem_union_left _ (Set.mem_singleton scs5M2), ?_⟩
        exact MM_5I3_IMP_MM_5M2 v hv fun i j hdij => le_of_lt (hdiag i j hdij)
      · push_neg at hdiag
        obtain ⟨i, j, hdij, hle⟩ := hdiag
        refine Or.inr ⟨scsStabDiagV39 scs5I3 i j, ?_, ?_⟩
        · simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
          exact Or.inr ⟨i, j, hdij, rfl⟩
        · intro hcon
          rw [Set.eq_empty_iff_forall_notMem] at hcon
          exact hcon v (SCS_5I3_STAB_DIAG v i j hv hdij hle)

/-- HOL `SCS_5M1_BERAK_BY_CSTAB` (OTMTOTJ.hl:890). -/
theorem SCS_5M1_BERAK_BY_CSTAB :
    scsArrowV39 {scs5M1} ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5M1 i j}) := by
  refine ⟨fun s hs => ?_, ?_⟩
  · rcases (Set.mem_union _ _ _).mp hs with hs | ⟨i, j, hd, rfl⟩
    · rw [Set.mem_singleton_iff] at hs
      subst s
      exact SCS_5M2_IS_SCS
    · have hk3 : (3 : ℕ) < scs5M1.k := by show (3 : ℕ) < 5; norm_num
      exact (YRTAFYH_concl scs5M1 i j SCS_5M1_IS_SCS SCS_5M1_BASIC hk3 hd
        (la24a5M1_le_cstab_p24 i j)).1
  · by_cases hE : ∀ s ∈ ({scs5M1} : Set ScsV39), MMsV39 s = ∅
    · exact Or.inl hE
    · push_neg at hE
      obtain ⟨s, hs, hne⟩ := hE
      rw [Set.mem_singleton_iff] at hs
      subst s
      obtain ⟨v, hv⟩ := hne
      by_cases hdiag : ∀ i j : ℕ, scsDiag 5 i j → cstab < dist (v i) (v j)
      · refine Or.inr ⟨scs5M2, Set.mem_union_left _ (Set.mem_singleton scs5M2), ?_⟩
        exact MM_5M1_IMP_MM_5M2 v hv fun i j hdij => le_of_lt (hdiag i j hdij)
      · push_neg at hdiag
        obtain ⟨i, j, hdij, hle⟩ := hdiag
        refine Or.inr ⟨scsStabDiagV39 scs5M1 i j, ?_, ?_⟩
        · simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
          exact Or.inr ⟨i, j, hdij, rfl⟩
        · intro hcon
          rw [Set.eq_empty_iff_forall_notMem] at hcon
          exact hcon v (SCS_5M1_STAB_DIAG v i j hv hdij hle)


/-! ### B6. The four master arrows (OTMTOTJ.hl:1156/1169/1500/1520)

Skeleton restatements (2026-09-21): faithful verbatim statements of the HOL
masters `OTMTOTJ1-4`, previously carried only by the LocalAuto1
`OTMTOTJ1-4_concl` registry copies (:1419-1439).  The HOL proofs compose
the Section B3/B5 arrows through the `FZIOTEF` transitivity/union kit. -/

/-- HOL `OTMTOTJ1` (OTMTOTJ.hl:1156). -/
theorem OTMTOTJ1 :
    scsArrowV39 {scs5I1} {scsStabDiagV39 scs5I1 0 2, scs5M2} := by
  have hberak : scsArrowV39 {scs5I1}
      ({x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I1 i j} ∪ {scs5M2}) := by
    rw [Set.union_comm]
    exact SCS_5I1_BERAK_BY_CSTAB
  rw [Set.insert_eq]
  exact FZIOTEF_TRANS {scs5I1}
    ({x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I1 i j} ∪ {scs5M2})
    ({scsStabDiagV39 scs5I1 0 2} ∪ {scs5M2}) hberak
    (FZIOTEF_UNION {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I1 i j}
      {scsStabDiagV39 scs5I1 0 2} {scs5M2} {scs5M2} SET_EQ_DIAG_STAB_5I1
      (FZIOTEF_REFL {scs5M2} (fun s hs => by
        rw [Set.mem_singleton_iff] at hs
        subst s
        exact SCS_5M2_IS_SCS)))

/-- HOL `OTMTOTJ2` (OTMTOTJ.hl:1169). -/
theorem OTMTOTJ2 :
    scsArrowV39 {scs5I2} {scsStabDiagV39 scs5I2 0 2, scs5M2} := by
  have hberak : scsArrowV39 {scs5I2}
      ({x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I2 i j} ∪ {scs5M2}) := by
    rw [Set.union_comm]
    exact SCS_5I2_BERAK_BY_CSTAB
  rw [Set.insert_eq]
  exact FZIOTEF_TRANS {scs5I2}
    ({x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I2 i j} ∪ {scs5M2})
    ({scsStabDiagV39 scs5I2 0 2} ∪ {scs5M2}) hberak
    (FZIOTEF_UNION {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I2 i j}
      {scsStabDiagV39 scs5I2 0 2} {scs5M2} {scs5M2} SET_EQ_DIAG_STAB_5I2
      (FZIOTEF_REFL {scs5M2} (fun s hs => by
        rw [Set.mem_singleton_iff] at hs
        subst s
        exact SCS_5M2_IS_SCS)))


/-! ## Section B8 (la24-b3masters-w3): the master arrows `OTMTOTJ3`/`OTMTOTJ4`

The Section B6 skeleton items `OTMTOTJ3` and `OTMTOTJ4` are MOVED here
verbatim (statements byte-identical to their Section B6 forms): their
discharges consume `STAB_5I3_ARROW_STAB_5M1_DIAG` (Section B7, which
`OTMTOTJ1`/`OTMTOTJ2` sit in the sweep-b24-w2 transfer section above (moved with the `BERAK` arrows they consume; statements byte-identical). -/


/-- The `scs_5M2` reflexivity twin (singleton `isScs` membership), shared by
the master arrows `OTMTOTJ1`-`OTMTOTJ4`. -/
private theorem la24arrow_refl_5M2_p24 :
    scsArrowV39 ({scs5M2} : Set ScsV39) ({scs5M2} : Set ScsV39) :=
  FZIOTEF_REFL {scs5M2} (fun s hs => by
    rw [Set.mem_singleton_iff] at hs
    subst s
    exact SCS_5M2_IS_SCS)

/-- `SET_EQ_DIAG_STAB_5M1` lifted to the `scs_5M2`-rooted union shape: the
`scs_5M2`-∪-3-diagonal-set arrow consumed by `OTMTOTJ3`/`OTMTOTJ4`. -/
private theorem la24diag3_5M1_arrow_p24 :
    scsArrowV39 ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
        x = scsStabDiagV39 scs5M1 i j})
      ({scs5M2} ∪ ({scsStabDiagV39 scs5M1 0 2} ∪ ({scsStabDiagV39 scs5M1 0 3} ∪
        {scsStabDiagV39 scs5M1 2 4} : Set ScsV39))) := by
  have hseteq : ({scsStabDiagV39 scs5M1 0 2} ∪ ({scsStabDiagV39 scs5M1 0 3} ∪
      {scsStabDiagV39 scs5M1 2 4} : Set ScsV39)) =
      {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
        scsStabDiagV39 scs5M1 2 4} := by
    rw [Set.insert_eq, Set.insert_eq]
  have hseq : scsArrowV39 {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5M1 i j}
      ({scsStabDiagV39 scs5M1 0 2} ∪ ({scsStabDiagV39 scs5M1 0 3} ∪
        {scsStabDiagV39 scs5M1 2 4} : Set ScsV39)) := by
    rw [hseteq]
    exact SET_EQ_DIAG_STAB_5M1
  exact FZIOTEF_UNION {scs5M2} {scs5M2}
    {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5M1 i j}
    ({scsStabDiagV39 scs5M1 0 2} ∪ ({scsStabDiagV39 scs5M1 0 3} ∪
      {scsStabDiagV39 scs5M1 2 4} : Set ScsV39))
    la24arrow_refl_5M2_p24 hseq

/-- The `scs_5M2`-first union form of the four-element master codomain
(pure `Set.insert_eq`/`union_comm`/`union_assoc` bookkeeping). -/
private theorem la24diag4_rotate_p24 :
    ({scs5M2} ∪ ({scsStabDiagV39 scs5M1 0 2} ∪ ({scsStabDiagV39 scs5M1 0 3} ∪
        {scsStabDiagV39 scs5M1 2 4} : Set ScsV39))) =
      {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
        scsStabDiagV39 scs5M1 2 4, scs5M2} := by
  rw [Set.insert_eq, Set.insert_eq, Set.insert_eq, Set.union_comm,
    Set.union_assoc, Set.union_assoc]

/-- `OTMTOTJ3`'s `scs_5M2`-rooted pre-chain (BERAK → twin-diag → 3-diag
set), via the two `FZIOTEF_UNION` hops over `la24arrow_refl_5M2_p24`. -/
private theorem la24otj3_chain_p24 :
    scsArrowV39 {scs5I3}
      ({scs5M2} ∪ ({scsStabDiagV39 scs5M1 0 2} ∪ ({scsStabDiagV39 scs5M1 0 3} ∪
        {scsStabDiagV39 scs5M1 2 4} : Set ScsV39))) :=
  FZIOTEF_TRANS {scs5I3} ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5I3 i j})
    ({scs5M2} ∪ ({scsStabDiagV39 scs5M1 0 2} ∪ ({scsStabDiagV39 scs5M1 0 3} ∪
      {scsStabDiagV39 scs5M1 2 4} : Set ScsV39)))
    SCS_5I3_BERAK_BY_CSTAB
    (FZIOTEF_TRANS ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
        x = scsStabDiagV39 scs5I3 i j})
      ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5M1 i j})
      ({scs5M2} ∪ ({scsStabDiagV39 scs5M1 0 2} ∪ ({scsStabDiagV39 scs5M1 0 3} ∪
        {scsStabDiagV39 scs5M1 2 4} : Set ScsV39)))
      (FZIOTEF_UNION {scs5M2} {scs5M2}
        {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I3 i j}
        {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5M1 i j}
        la24arrow_refl_5M2_p24 STAB_5I3_ARROW_STAB_5M1_DIAG)
      la24diag3_5M1_arrow_p24)

/-- `OTMTOTJ4`'s `scs_5M2`-rooted pre-chain (BERAK → 3-diag set). -/
private theorem la24otj4_chain_p24 :
    scsArrowV39 {scs5M1}
      ({scs5M2} ∪ ({scsStabDiagV39 scs5M1 0 2} ∪ ({scsStabDiagV39 scs5M1 0 3} ∪
        {scsStabDiagV39 scs5M1 2 4} : Set ScsV39))) :=
  FZIOTEF_TRANS {scs5M1} ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5M1 i j})
    ({scs5M2} ∪ ({scsStabDiagV39 scs5M1 0 2} ∪ ({scsStabDiagV39 scs5M1 0 3} ∪
      {scsStabDiagV39 scs5M1 2 4} : Set ScsV39)))
    SCS_5M1_BERAK_BY_CSTAB la24diag3_5M1_arrow_p24

/-- HOL `OTMTOTJ3` (OTMTOTJ.hl:1500). -/
theorem OTMTOTJ3 :
    scsArrowV39 {scs5I3} {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs5M2} := by
  rw [← la24diag4_rotate_p24]
  exact la24otj3_chain_p24

/-- HOL `OTMTOTJ4` (OTMTOTJ.hl:1520). -/
theorem OTMTOTJ4 :
    scsArrowV39 {scs5M1} {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs5M2} := by
  rw [← la24diag4_rotate_p24]
  exact la24otj4_chain_p24



-- sweep-b24-w2: axiom tails of the seven discharged arrows.
#print axioms Kepler.Text.MM_5I1_IMP_MM_5M2
#print axioms Kepler.Text.MM_5I2_IMP_MM_5M2
#print axioms Kepler.Text.MM_5I3_IMP_MM_5M2
#print axioms Kepler.Text.MM_5M1_IMP_MM_5M2
#print axioms Kepler.Text.SET_EQ_DIAG_STAB_5I1
#print axioms Kepler.Text.SET_EQ_DIAG_STAB_5I2
#print axioms Kepler.Text.SET_EQ_DIAG_STAB_5M1
