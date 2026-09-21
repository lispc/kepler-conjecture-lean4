/-
LocalAuto24: port of three appendix modules bridging the Local Fan chapter:

  - `scripts/local/WKEIDFT.hl` (834 lines, 20 declarations): the
    diagonal-stabilisation equidecomposition of the appendix. The ℤ/k
    arithmetic kit (`SUR_MOD_FUN`, `TRANS_DIAG` ×2, `scs_components`,
    `scs_inj`, `DIAG_PSORT1`/`DIAG_PSORT2`/`DIAG_PSORT`,
    `A_EQ_PSORT`, `B_EQ_PSORT`, `PROPERTY_OF_K_SCS`) is re-exported as
    `_p24` one-line twins from the PROVED `_p17` copies in
    `Kepler.Text.LocalAuto17`; `SCS_K_D_A_STAB_EQ` likewise from
    `Kepler.Text.LocalAuto20`; `WKEIDFT_concl` (the LocalAuto1:1384
    appendix variant of HOL `WKEIDFT.hl:570/:793`) is re-exported
    unchanged (FILE MAP note: it is a light variant, not the verbatim v1).
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

/-- HOL `WKEIDFT_concl` (appendix.hl / LocalAuto1:1384 variant). Re-export
unchanged. FILE MAP note: this is the *light* appendix variant (no
`scs_diag k p q`, no `b1`); the verbatim HOL v1 (`WKEIDFT.hl:570`)
`scs_arrow {s} {s'}` statement is covered by `WKEIDFT` below in its v2
stabilised form. -/
theorem WKEIDFT_concl_p24 : ∀ (s : ScsV39) (a b a' b' : ℝ) (p q p' q' : ℕ),
    isScsV39 s → scsBasicV39 s →
    (∀ i, s.a i (i + 1) = a) → (∀ i, s.b i (i + 1) = b) → p' + q = p + q' →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab) →
    (∀ i j, scsDiag s.k i j → s.a i j = a') →
    (∀ i j, scsDiag s.k i j → s.b i j = b') →
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

/-! ### B1. The bounded-pentagon implications (`BB`/`MM`), pentagons.hl:125-559 -/

/-- HOL `BB_5I1_IS_BB_5M2` (OTMTOTJ.hl:125). -/
theorem BB_5I1_IS_BB_5M2 (v : ℕ → V3) (h : BBsV39 scs5I1 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  sorry
  -- DISCHARGES: pentagons.hl `SCS_TAC` case work on `scs_5I1`/`scs_5M2`.

/-- HOL `MM_5I1_IMP_MM_5M2` (OTMTOTJ.hl:223). -/
theorem MM_5I1_IMP_MM_5M2 (v : ℕ → V3) (h : v ∈ MMsV39 scs5I1)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    v ∈ MMsV39 scs5M2 := by
  sorry
  -- DISCHARGES: `BB_5I1_IS_BB_5M2` + `MM` unfold.

/-- HOL `BB_5I2_IS_BB_5M2` (OTMTOTJ.hl:239). -/
theorem BB_5I2_IS_BB_5M2 (v : ℕ → V3) (h : BBsV39 scs5I2 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  sorry
  -- DISCHARGES: pentagons.hl `SCS_TAC` case work on `scs_5I2`/`scs_5M2`.

/-- HOL `MM_5I2_IMP_MM_5M2` (OTMTOTJ.hl:337). -/
theorem MM_5I2_IMP_MM_5M2 (v : ℕ → V3) (h : v ∈ MMsV39 scs5I2)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    v ∈ MMsV39 scs5M2 := by
  sorry
  -- DISCHARGES: `BB_5I2_IS_BB_5M2` + `MM` unfold.

/-- HOL `BB_5I3_IS_BB_5M2` (OTMTOTJ.hl:354). -/
theorem BB_5I3_IS_BB_5M2 (v : ℕ → V3) (h : BBsV39 scs5I3 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  sorry
  -- DISCHARGES: pentagons.hl `SCS_TAC` case work on `scs_5I3`/`scs_5M2`.

/-- HOL `MM_5I3_IMP_MM_5M2` (OTMTOTJ.hl:462). -/
theorem MM_5I3_IMP_MM_5M2 (v : ℕ → V3) (h : v ∈ MMsV39 scs5I3)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    v ∈ MMsV39 scs5M2 := by
  sorry
  -- DISCHARGES: `BB_5I3_IS_BB_5M2` + `MM` unfold.

/-- HOL `BB_5M1_IS_BB_5M2` (OTMTOTJ.hl:478). -/
theorem BB_5M1_IS_BB_5M2 (v : ℕ → V3) (h : BBsV39 scs5M1 v)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs5M2 v := by
  sorry
  -- DISCHARGES: pentagons.hl `SCS_TAC` case work on `scs_5M1`/`scs_5M2`.

/-- HOL `MM_5M1_IMP_MM_5M2` (OTMTOTJ.hl:535). -/
theorem MM_5M1_IMP_MM_5M2 (v : ℕ → V3) (h : v ∈ MMsV39 scs5M1)
    (hc : ∀ i j : ℕ, scsDiag 5 i j → cstab ≤ dist (v i) (v j)) :
    v ∈ MMsV39 scs5M2 := by
  sorry
  -- DISCHARGES: `BB_5M1_IS_BB_5M2` + `MM` unfold.

/-! ### B2. Diag-stabilisation of the pentagons keeps `MMs` (OTMTOTJ.hl:553-696) -/

/-- HOL `SCS_5I1_STAB_DIAG` (OTMTOTJ.hl:553). -/
theorem SCS_5I1_STAB_DIAG (v : ℕ → V3) (i j : ℕ) (h : v ∈ MMsV39 scs5I1)
    (hd : scsDiag 5 i j) (hle : dist (v i) (v j) ≤ cstab) :
    v ∈ MMsV39 (scsStabDiagV39 scs5I1 i j) := by
  sorry
  -- DISCHARGES: Nuxcoea.MMS_IMP_BBS, DIST_LE_IMP_A_LE, YRTAFYH,
  -- Ppbtydq.MXQTIED, STAB_BB, SCS_K_D_A_STAB_EQ, DIAG_SCS_M_EQ,
  -- DIAD_PSORT_IMP_DIAD, DIAG_5_EQU_PSORT.

/-- HOL `SCS_5I2_STAB_DIAG` (OTMTOTJ.hl:587). -/
theorem SCS_5I2_STAB_DIAG (v : ℕ → V3) (i j : ℕ) (h : v ∈ MMsV39 scs5I2)
    (hd : scsDiag 5 i j) (hle : dist (v i) (v j) ≤ cstab) :
    v ∈ MMsV39 (scsStabDiagV39 scs5I2 i j) := by
  sorry
  -- DISCHARGES: as `SCS_5I1_STAB_DIAG` on `scs_5I2`.

/-- HOL `SCS_5I3_STAB_DIAG` (OTMTOTJ.hl:622). -/
theorem SCS_5I3_STAB_DIAG (v : ℕ → V3) (i j : ℕ) (h : v ∈ MMsV39 scs5I3)
    (hd : scsDiag 5 i j) (hle : dist (v i) (v j) ≤ cstab) :
    v ∈ MMsV39 (scsStabDiagV39 scs5I3 i j) := by
  sorry
  -- DISCHARGES: as `SCS_5I1_STAB_DIAG` on `scs_5I3`.

/-- HOL `SCS_5M1_STAB_DIAG` (OTMTOTJ.hl:659). -/
theorem SCS_5M1_STAB_DIAG (v : ℕ → V3) (i j : ℕ) (h : v ∈ MMsV39 scs5M1)
    (hd : scsDiag 5 i j) (hle : dist (v i) (v j) ≤ cstab) :
    v ∈ MMsV39 (scsStabDiagV39 scs5M1 i j) := by
  sorry
  -- DISCHARGES: as `SCS_5I1_STAB_DIAG` on `scs_5M1`.

/-! ### B3. The `BERAK` arrows (OTMTOTJ.hl:699-954) -/

/-- HOL `SCS_5I1_BERAK_BY_CSTAB` (OTMTOTJ.hl:699). -/
theorem SCS_5I1_BERAK_BY_CSTAB :
    scsArrowV39 {scs5I1} ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5I1 i j}) := by
  sorry
  -- DISCHARGES: STAB_IS_SCS, MM_5I1_IMP_MM_5M2, SCS_5I1_STAB_DIAG,
  -- FZIOTEF-closure of `scs_arrow_v39`.

/-- HOL `SCS_5I2_BERAK_BY_CSTAB` (OTMTOTJ.hl:761). -/
theorem SCS_5I2_BERAK_BY_CSTAB :
    scsArrowV39 {scs5I2} ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5I2 i j}) := by
  sorry
  -- DISCHARGES: as `SCS_5I1_BERAK_BY_CSTAB` on `scs_5I2`.

/-- HOL `SCS_5I3_BERAK_BY_CSTAB` (OTMTOTJ.hl:826). -/
theorem SCS_5I3_BERAK_BY_CSTAB :
    scsArrowV39 {scs5I3} ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5I3 i j}) := by
  sorry
  -- DISCHARGES: as `SCS_5I1_BERAK_BY_CSTAB` on `scs_5I3`.

/-- HOL `SCS_5M1_BERAK_BY_CSTAB` (OTMTOTJ.hl:890). -/
theorem SCS_5M1_BERAK_BY_CSTAB :
    scsArrowV39 {scs5M1} ({scs5M2} ∪ {x | ∃ i j, scsDiag 5 i j ∧
      x = scsStabDiagV39 scs5M1 i j}) := by
  sorry
  -- DISCHARGES: as `SCS_5I1_BERAK_BY_CSTAB` on `scs_5M1`.

/-! ### B4. Diag-set identities over k = 5 (OTMTOTJ.hl:971-1153) -/

/-- HOL `EXPAND_STAB_DIAG_5` (OTMTOTJ.hl:971). -/
theorem EXPAND_STAB_DIAG_5 (s : ScsV39) (hs : isScsV39 s) (hk : s.k = 5) :
    {x | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      x = scsStabDiagV39 s (i % 5) (j % 5)} =
    {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 s (i + 2) i} := by
  sorry
  -- DISCHARGES: STAB_MOD, STAB_SYM, MOD_REFL, DIVISION, MOD_LT.

/-- HOL `EXPAND_STAB_DIAG_5I1` (OTMTOTJ.hl:997). -/
theorem EXPAND_STAB_DIAG_5I1 :
    {x | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      x = scsStabDiagV39 scs5I1 (i % 5) (j % 5)} =
    {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 scs5I1 (i + 2) i} := by
  sorry
  -- DISCHARGES: EXPAND_STAB_DIAG_5 + SCS_5I1_IS_SCS + K_SCS_5I1.

/-- HOL `EXPAND_STAB_DIAG_5I2` (OTMTOTJ.hl:1005). -/
theorem EXPAND_STAB_DIAG_5I2 :
    {x | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      x = scsStabDiagV39 scs5I2 (i % 5) (j % 5)} =
    {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 scs5I2 (i + 2) i} := by
  sorry
  -- DISCHARGES: EXPAND_STAB_DIAG_5 + SCS_5I2_IS_SCS + K_SCS_5I2.

/-- HOL `EXPAND_STAB_DIAG_5I3` (OTMTOTJ.hl:1014). -/
theorem EXPAND_STAB_DIAG_5I3 :
    {x | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      x = scsStabDiagV39 scs5I3 (i % 5) (j % 5)} =
    {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 scs5I3 (i + 2) i} := by
  sorry
  -- DISCHARGES: EXPAND_STAB_DIAG_5 + SCS_5I3_IS_SCS + K_SCS_5I3.

/-- HOL `EXPAND_STAB_DIAG_5M1` (OTMTOTJ.hl:1022). -/
theorem EXPAND_STAB_DIAG_5M1 :
    {x | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      x = scsStabDiagV39 scs5M1 (i % 5) (j % 5)} =
    {x | ∃ i, i < 5 ∧ x = scsStabDiagV39 scs5M1 (i + 2) i} := by
  sorry
  -- DISCHARGES: EXPAND_STAB_DIAG_5 + SCS_5M1_IS_SCS + K_SCS_5M1.

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

/-- HOL `SET_EQ_DIAG_STAB_5I1` (OTMTOTJ.hl:1141). -/
theorem SET_EQ_DIAG_STAB_5I1 :
    scsArrowV39 {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I1 i j}
      {scsStabDiagV39 scs5I1 0 2} := by
  sorry
  -- DISCHARGES: SET_STAB_5I1 + DIAG_EQ_ADD5 + EXPAND_STAB_DIAG_5I1 +
  -- SET_EQ_DIAG_STAB_5I1_02 + FZIOTEF-chaining.

/-- HOL `SET_EQ_DIAG_STAB_5I2` (OTMTOTJ.hl:1148). -/
theorem SET_EQ_DIAG_STAB_5I2 :
    scsArrowV39 {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I2 i j}
      {scsStabDiagV39 scs5I2 0 2} := by
  sorry
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

/-- HOL `STAB_5I3_SCS` (OTMTOTJ.hl:1199). -/
theorem STAB_5I3_SCS (i j : ℕ) (hd : scsDiag (scs5I3.k) i j) :
    isScsV39 (scsStabDiagV39 scs5I3 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5I3 i j) := by
  sorry
  -- DISCHARGES: Yrtafyh.YRTAFYH + SCS_K_D_A_STAB_EQ + SCS_5I3_IS_SCS +
  -- SCS_5I3_BASIC + K_SCS_5I3.

/-- HOL `STAB_5I2_SCS` (OTMTOTJ.hl:1210). -/
theorem STAB_5I2_SCS (i j : ℕ) (hd : scsDiag (scs5I2.k) i j) :
    isScsV39 (scsStabDiagV39 scs5I2 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5I2 i j) := by
  sorry
  -- DISCHARGES: Yrtafyh.YRTAFYH + SCS_K_D_A_STAB_EQ + SCS_5I2_IS_SCS +
  -- SCS_5I2_BASIC + K_SCS_5I2 + sqrt8_LE_CSTAB.

/-- HOL `STAB_5M1_SCS` (OTMTOTJ.hl:1223). -/
theorem STAB_5M1_SCS (i j : ℕ) (hd : scsDiag (scs5M1.k) i j) :
    isScsV39 (scsStabDiagV39 scs5M1 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5M1 i j) := by
  sorry
  -- DISCHARGES: Yrtafyh.YRTAFYH + SCS_K_D_A_STAB_EQ + SCS_5M1_IS_SCS +
  -- SCS_5M1_BASIC + K_SCS_5M1.

/-- HOL `MM_5I3_IMP_MM_5M1` (OTMTOTJ.hl:1238). -/
theorem MM_5I3_IMP_MM_5M1 (v : ℕ → V3) (i j : ℕ) (hd : scsDiag 5 i j)
    (h : v ∈ MMsV39 (scsStabDiagV39 scs5I3 i j)) :
    (MMsV39 (scsStabDiagV39 scs5M1 i j) : Set (ℕ → V3)) ≠ ∅ := by
  sorry
  -- DISCHARGES: Ppbtydq.XWNHLMD_MM + Nuxcoea.MMS_IMP_BBS + BB_5I3_IS_BB_5M1 +
  -- STAB_5I3_SCS + STAB_5M1_SCS + SCS_K_D_A_STAB_EQ.

/-- HOL `STAB_5I3_ARROW_STAB_5M1` (OTMTOTJ.hl:1251). -/
theorem STAB_5I3_ARROW_STAB_5M1 (i j : ℕ) (hd : scsDiag 5 i j) :
    scsArrowV39 {scsStabDiagV39 scs5I3 i j} {scsStabDiagV39 scs5M1 i j} := by
  sorry
  -- DISCHARGES: BB_5I3_IS_BB_5M1 + STAB_5I3_SCS + STAB_5M1_SCS +
  -- MM_5I3_IMP_MM_5M1 + SCS_K_D_A_STAB_EQ.

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

/-- HOL `STAB_5I3_ARROW_STAB_5M1_DIAG` (OTMTOTJ.hl:1361). -/
theorem STAB_5I3_ARROW_STAB_5M1_DIAG :
    scsArrowV39 {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5I3 i j}
      {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5M1 i j} := by
  sorry
  -- DISCHARGES: SET_STAB_5I3 + SET_STAB_5M1 + DIAG_EQ_ADD5 +
  -- EXPAND_STAB_DIAG_5I3 + EXPAND_STAB_DIAG_5M1 + STAB_5I3_ARROW_STAB_5M1
  -- + FZIOTEF_UNION.

/-- HOL `SET_EQ_DIAG_STAB_5M1` (OTMTOTJ.hl:1395). -/
theorem SET_EQ_DIAG_STAB_5M1 :
    scsArrowV39 {x | ∃ i j, scsDiag 5 i j ∧ x = scsStabDiagV39 scs5M1 i j}
      ({scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
        scsStabDiagV39 scs5M1 2 4} : Set ScsV39) := by
  sorry
  -- DISCHARGES: SET_STAB_5M1 + DIAG_EQ_ADD5 + EXPAND_STAB_DIAG_5I3 +
  -- EXPAND_STAB_DIAG_5M1 + EQ_DIAG_STAB_* (the three singleton arrows,
  -- FZIOTEF-chained).

/-! ### B6. The four master arrows (OTMTOTJ.hl:1156/1169/1500/1520)

Skeleton restatements (2026-09-21): faithful verbatim statements of the HOL
masters `OTMTOTJ1-4`, previously carried only by the LocalAuto1
`OTMTOTJ1-4_concl` registry copies (:1419-1439).  The HOL proofs compose
the Section B3/B5 arrows through the `FZIOTEF` transitivity/union kit. -/

/-- HOL `OTMTOTJ1` (OTMTOTJ.hl:1156). -/
theorem OTMTOTJ1 :
    scsArrowV39 {scs5I1} {scsStabDiagV39 scs5I1 0 2, scs5M2} := by
  sorry
  -- DISCHARGES: 骨架占位，忠实陈述 (OTMTOTJ.hl:1156). HOL chain:
  -- FZIOTEF_TRANS over SCS_5I1_BERAK_BY_CSTAB + SET_EQ_DIAG_STAB_5I1 +
  -- FZIOTEF_UNION + FZIOTEF_REFL + SCS_5M2_IS_SCS.

/-- HOL `OTMTOTJ2` (OTMTOTJ.hl:1169). -/
theorem OTMTOTJ2 :
    scsArrowV39 {scs5I2} {scsStabDiagV39 scs5I2 0 2, scs5M2} := by
  sorry
  -- DISCHARGES: 骨架占位，忠实陈述 (OTMTOTJ.hl:1169). HOL chain:
  -- as `OTMTOTJ1` over SCS_5I2_BERAK_BY_CSTAB + SET_EQ_DIAG_STAB_5I2.

/-- HOL `OTMTOTJ3` (OTMTOTJ.hl:1500). -/
theorem OTMTOTJ3 :
    scsArrowV39 {scs5I3} {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs5M2} := by
  sorry
  -- DISCHARGES: 骨架占位，忠实陈述 (OTMTOTJ.hl:1500). HOL chain:
  -- FZIOTEF_TRANS over SCS_5I3_BERAK_BY_CSTAB + STAB_5I3_ARROW_STAB_5M1_DIAG
  -- + SET_EQ_DIAG_STAB_5M1 + FZIOTEF_REFL + SCS_5M2_IS_SCS.

/-- HOL `OTMTOTJ4` (OTMTOTJ.hl:1520). -/
theorem OTMTOTJ4 :
    scsArrowV39 {scs5M1} {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs5M2} := by
  sorry
  -- DISCHARGES: 骨架占位，忠实陈述 (OTMTOTJ.hl:1520). HOL chain:
  -- as `OTMTOTJ1` over SCS_5M1_BERAK_BY_CSTAB + SET_EQ_DIAG_STAB_5M1.

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

/-! ### C1. The k = 4 witnesses (UXCKFPE.hl:70-543) -/

/-- HOL `NOT_EMPTY_CASE_4_IS_SCS` (UXCKFPE.hl:70). -/
theorem NOT_EMPTY_CASE_4_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s vv) :
    (B_SY1_p4
      (fun i j : Fin 4 => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
      (fun i j : Fin 4 => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))) ≠ ∅ := by
  sorry
  -- DISCHARGES: IN_IS_SCS_CASE_4_p23 (witness `flattenRow_p23 vv 4`) over
  -- IS_SCS_IN_BALL_ANNULUS_4_p23 + the BBsV39 bound/fan conjuncts.

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
  sorry
  -- DISCHARGES: BBsV39 conjunct walk — annulus range + the CONDITION1
  -- bounds lifted to all indices by `Periodic2 s.a/b s.k` periodicity
  -- (PERIODIC_PROPERTY) + V_E_FF_IS_SCS_CASES_4_p23 for the fan conjunct.

/-- HOL `XWITCCN_CASE_4_IS_SCS` (UXCKFPE.hl:432). -/
theorem XWITCCN_CASE_4_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : s.k = 4)
    (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by
  sorry
  -- DISCHARGES: IS_SCS_STABLE_SYSTEM_p23 + NOT_EMPTY_CASE_4_IS_SCS_p24 +
  -- the HDPLYGY/B_SY1 minimizer on the stable record + IN_NOT_EMPTY_B1_SY_4
  -- + TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4_p23 (negativity transfer).

/-! ### C2. The k = 5 witnesses (UXCKFPE.hl:547-995) -/

/-- HOL `NOT_EMPTY_CASE_5_IS_SCS` (UXCKFPE.hl:547). -/
theorem NOT_EMPTY_CASE_5_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s vv) :
    (B_SY1_p4
      (fun i j : Fin 5 => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
      (fun i j : Fin 5 => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))) ≠ ∅ := by
  sorry
  -- DISCHARGES: IN_IS_SCS_CASE_5_p23 (witness `flattenRow_p23 vv 5`).

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
  sorry
  -- DISCHARGES: as `IN_NOT_EMPTY_B1_SY_4_IS_SCS_p24` at k = 5
  -- (V_E_FF_IS_SCS_CASES_5_p23).

/-- HOL `XWITCCN_CASE_5_IS_SCS` (UXCKFPE.hl:889). -/
theorem XWITCCN_CASE_5_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : s.k = 5)
    (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by
  sorry
  -- DISCHARGES: as `XWITCCN_CASE_4_IS_SCS_p24` at k = 5.

/-! ### C3. The k = 6 witnesses (UXCKFPE.hl:1003-1483) -/

/-- HOL `NOT_EMPTY_CASE_6_IS_SCS` (UXCKFPE.hl:1003). -/
theorem NOT_EMPTY_CASE_6_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 6) (hBB : BBsV39 s vv) :
    (B_SY1_p4
      (fun i j : Fin 6 => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
      (fun i j : Fin 6 => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))) ≠ ∅ := by
  sorry
  -- DISCHARGES: IN_IS_SCS_CASE_6_p23 (witness `flattenRow_p23 vv 6`).

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
  sorry
  -- DISCHARGES: as `IN_NOT_EMPTY_B1_SY_4_IS_SCS_p24` at k = 6
  -- (V_E_FF_IS_SCS_CASES_6_p23).

/-- HOL `XWITCCN_CASE_6_IS_SCS` (UXCKFPE.hl:1374). -/
theorem XWITCCN_CASE_6_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : s.k = 6)
    (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by
  sorry
  -- DISCHARGES: as `XWITCCN_CASE_4_IS_SCS_p24` at k = 6.

/-! ### C4. The k = 3 `tri_sy` capstone (UXCKFPE.hl:1488-2597)

The k = 3 body set (no `CONDITION2_SY` at k = 3, verbatim HOL): the
`CONDITION1_SY_p4` bounds on the cyclic row vector `cycRow_p23 vv 3`. -/

/-- HOL `IN_IS_SCS_CASE_3` (UXCKFPE.hl:1502): the k = 3 flattening
`matvec (vector[vv 1; vv 2; vv 0])` lies in the (CONDITION2-free) body. -/
theorem IN_IS_SCS_CASE_3_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    flattenRow_p23 vv 3 ∈
      {l : FinVec 3 3 |
        (∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (cycRow_p23 vv 3)} := by
  sorry
  -- DISCHARGES: rows-in-annulus (IS_SCS_IN_BALL_ANNULUS via hBB.1) + the
  -- BBsV39 a/b bounds at the cyclic rows (no fan conjunct needed at k = 3).

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

/-- HOL `NOT_EMPTY_CASE_3_IS_SCS` (UXCKFPE.hl:1775). -/
theorem NOT_EMPTY_CASE_3_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    ({l : FinVec 3 3 |
        (∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (cycRow_p23 vv 3)} : Set (FinVec 3 3)) ≠ ∅ := by
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
on the k = 3 body set (sum over the finite `J1_TS_p24` of row differences). -/
theorem CONTINUOUS_ON_D_FUN3_p24 (s : ScsV39) (hk : s.k = 3)
    (vv : ℕ → V3) :
    ContinuousOn
      (fun l : FinVec 3 3 =>
        dFun3_p24 s.d (isEarV39 s) (scsJSet_p23 s) (fun i => (1 + i) % s.k) l)
      {l : FinVec 3 3 |
        (∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (cycRow_p23 vv 3)} := by
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
(HOL rows `1,2,3` ↦ the `rowSy_p23 l` indices `0,1,2`). -/
theorem IN_B_SY1_COLLINEAR_CASE_3_IS_SCS_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    ∀ l : FinVec 3 3,
      (∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus) ∧
        CONDITION1_SY_p4
          (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
          (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
          (cycRow_p23 vv 3) →
      ¬ Collinear ℝ ({0, rowSy_p23 l 0, rowSy_p23 l 1} : Set V3) ∧
        ¬ Collinear ℝ ({0, rowSy_p23 l 0, rowSy_p23 l 2} : Set V3) ∧
        ¬ Collinear ℝ ({0, rowSy_p23 l 1, rowSy_p23 l 2} : Set V3) := by
  sorry
  -- DISCHARGES: the row-decoding of IN_NOT_EMPTY_B1_SY_3 (rows of a body
  -- point are a BBs realisation) + IS_SCS_NOT_COLLINEAR_BBs_CASE_3_p23.

/-- HOL `HDPLYGY_CASE_30` (UXCKFPE.hl:1926): the k = 3 minimizer of
`tau3 - d_fun3` over the (compact, nonempty) body set. -/
theorem HDPLYGY_CASE_30_p24 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3)
    (hne : ({l : FinVec 3 3 |
        (∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (cycRow_p23 vv 3)} : Set (FinVec 3 3)) ≠ ∅)
    (hnc : ∀ l : FinVec 3 3,
        (∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (cycRow_p23 vv 3) →
        ¬ Collinear ℝ ({0, rowSy_p23 l 0, rowSy_p23 l 1} : Set V3) ∧
          ¬ Collinear ℝ ({0, rowSy_p23 l 0, rowSy_p23 l 2} : Set V3) ∧
          ¬ Collinear ℝ ({0, rowSy_p23 l 1, rowSy_p23 l 2} : Set V3)) :
    ∃ x : FinVec 3 3,
      (x ∈ ({l : FinVec 3 3 |
        (∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (cycRow_p23 vv 3)} : Set (FinVec 3 3))) ∧
      ∀ y : FinVec 3 3,
        y ∈ ({l : FinVec 3 3 |
        (∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (cycRow_p23 vv 3)} : Set (FinVec 3 3)) →
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