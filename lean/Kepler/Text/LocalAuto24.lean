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