/-
LocalAuto12: port of `scripts/local/YXIONXL.hl` (2610 lines, 0 defs +
39 theorems; H. L. Truong, 2012) — "remaining conclusions from appendix to
Local Fan chapter": the BB-transfer lemmas for `scs_arrow_v39`, i.e. the
invariance of the BB*/MM* tower under `transfer_v39` (dilation of the a/b
windows) and under `scs_prop_equ_v39` (cyclic re-indexing of a system).

NO overlap with YXIONXL2 (a different, parallel-owned file).

FILE MAP
  Section 0: port helpers — `Periodic`/`Periodic2` residue lemmas
    (`periodicMod` = HOL `PERIODIC_PROPERTY`), the mod-shift kit
    (`TRANS_MOD_EQ`, `TRANS_MOD_EQ_SUC`, `TRANS_ID_INDEX`), the cyclic
    `funext` kit (`shiftBy_eq`, `shiftBy1_eq`), and `setSum` monotonicity
    (HOL `SUM_SUBSET_SIMPLE`/`SUM_POS_LE`).
  Section 1: the transfer kit (TRANSFER_SUBSET_BB, DSV_LE_DSV_TRANSFER,
    TAUSTAR_LE_TAUSTAR_TRANSFER, TRANSTER_IS_UNADORNED, the `sgtrnaf_p12`
    anchor, NOT_EMPETY_MMS_TRANSFER, YXIONXL1).
  Section 2: cyclic images (TRANS_V, TRANS_FF, TRANS_E, BB_TRANS_SUBSET_BB).
  Section 3: invariance under `scs_prop_equ_v39` (PROP_EQU_IS_SCS, the
    `TRANS_SCS_*_ID` family, PRO_EQU_ID/ID1, the BBindex image/min kit,
    TRANS_MMS_SUBSET, YXIONXL3).  Each section keeps source order.

PROOF STATUS: 27 of the 39 theorems proved outright; 12 sorry'd with
per-item NEEDS notes (see below).  Of the proved ones,
NOT_EMPETY_MMS_TRANSFER and YXIONXL1 rest on the `sgtrnaf_p12` anchor.

ENCODING NOTES
  - HOL `real^3` <-> `V3` (Kepler.Geom); `IMAGE f (:num)` <-> `Set.range f`;
    `x IN (:num)` <-> `x ∈ Set.univ`; `SUC n` <-> `n + 1`; `i MOD k` <->
    `i % k`; HOL `sum S f` <-> `setSum` (PackingAuto2, 0 on infinite sets).
  - The scs_v39 lane (`ScsV39`, `isScsV39`, `unadornedV39`, `isEarV39`,
    `BBsV39`, `dsvV39`, `taustarV39`, `BBprimeV39`, `BBindexV39`,
    `BBindexMinV39`, `BBprime2V39`, `MMsV39`, `scsArrowV39`,
    `scsPropEquV39`, `transferV39`, `Periodic`, `Periodic2`, `cstab`) is the
    LocalAuto1 port of appendix.hl; `setSum`/`h0`/`ballAnnulus` are
    PackingAuto2.  NO `_p12` copies needed for the defs.
  - Source names kept verbatim, including the typos `TRANSTER_IS_UNADORNED`
    and `NOT_EMPETY_MMS_TRANSFER` (1:1 traceability).
  - `scs_prop_equ_v39 s i` is `scsPropEquV39 s i`; its `.k` field is
    definitionally `s.k`, so the HOL side conditions `scs_k_v39 s = k`
    stay as hypotheses where the source has them.
  - `PRO_EQU_ID`/`PRO_EQU_ID1` are proved componentwise from the
    `shiftBy_eq` funext kit (the HOL proofs rewrite the ten `scs_*_v39`
    tuple projections; here the projections are structure fields, so
    `ScsV39.mk` congruence replaces the `part*`/`drop*` rewriting).
  - NEEDS: HOL `SGTRNAF` (sgtrnaf.hl:166) has no importable port; carried
    as the `sgtrnaf_p12` anchor (its HOL proof consumes `unadorned_MMs` =
    the `unadorned_MMs_concl` registry item of LocalAuto1 and `UXCKFPE2`
    from uxckfpe.hl, also unported).  The chain
    NOT_EMPETY_MMS_TRANSFER -> YXIONXL1 is proved modulo that anchor.
  - The giants (PROP_EQU_IS_SCS, PRO_EQU_IS_EAR, PRO_EQU_DSV_EQ,
    PRO_EQU_TAUSTAR_EQ, the BBindex image/min kit, TRANS_MMS_SUBSET,
    YXIONXL3) are stated and sorry'd — see the per-item NEEDS notes.
    PRO_EQU_TAUSTAR_EQ additionally needs HOL `SUM_AZIM_EQ_ANGLE_LE4`
    (Hdplygy lane, unported).

DISCHARGES: nothing yet (sorry'd items keep `sorry`; DISCHARGES
convention — later waves prove them and the `sorry` disappears).  The
open needs are: SGTRNAF/UXCKFPE2 (sgtrnaf.hl, uxckfpe.hl), the ncard
bijection `j ↦ (i + j) % k` for PROP_EQU_IS_SCS/TRANS_BBINDEX_ID, the
3-cycle J-singleton transport for PRO_EQU_IS_EAR, the `SUM_EQ_GENERAL`
reindexing for PRO_EQU_DSV_EQ, and HOL `SUM_AZIM_EQ_ANGLE_LE4`
(Hdplygy lane) for PRO_EQU_TAUSTAR_EQ; YXIONXL3 then follows from
PROP_EQU_IS_SCS + TRANS_MMS_SUBSET as in HOL.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.PackingAuto2
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: helpers -/

/-- HOL `PERIODIC_PROPERTY` shape: a `k`-periodic function only depends on
the residue mod `k` (`k ≠ 0`). -/
theorem periodicMod {α : Sort u} {f : ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (hf : Periodic f k) (i : ℕ) : f (i % k) = f i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    if h : i < k then
      rw [Nat.mod_eq_of_lt h]
    else
      have hle : k ≤ i := le_of_not_gt h
      rw [Nat.mod_eq_sub_mod hle, ih (i - k) (by omega), ← hf (i - k),
        Nat.sub_add_cancel hle]

/-- First-argument residue form of `Periodic2`. -/
theorem periodic2Mod1 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (hf : Periodic2 f k) (i j : ℕ) : f (i % k) j = f i j :=
  periodicMod (f := fun x => f x j) hk (fun x => (hf x j).1) i

/-- Second-argument residue form of `Periodic2`. -/
theorem periodic2Mod2 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (hf : Periodic2 f k) (i j : ℕ) : f i (j % k) = f i j :=
  periodicMod (f := fun x => f i x) hk (fun x => (hf i x).2) j

/-- `setSum` is monotone under subsets with nonnegative summands
(HOL `SUM_SUBSET_SIMPLE` with `SUM_POS_LE`). -/
private theorem setSum_le_setSum_of_subset {α : Type*} {S T : Set α} {f : α → ℝ}
    (hsub : S ⊆ T) (hf : ∀ x ∈ T, 0 ≤ f x) (hT : T.Finite) :
    setSum S f ≤ setSum T f := by
  have hS : S.Finite := hT.subset hsub
  rw [setSum, setSum, dif_pos hS, dif_pos hT]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_iff.2 fun x hx => hT.mem_toFinset.2 (hsub (hS.mem_toFinset.1 hx)))
    (fun x hx _ => hf x (hT.mem_toFinset.1 hx))

/-- `setSum` is nonnegative when every summand is. -/
private theorem setSum_nonneg {α : Type*} {S : Set α} {f : α → ℝ}
    (hf : ∀ x ∈ S, 0 ≤ f x) (hS : S.Finite) : 0 ≤ setSum S f := by
  rw [setSum, dif_pos hS]
  exact Finset.sum_nonneg (fun x hx => hf x (hS.mem_toFinset.1 hx))

/-- HOL `TRANS_MOD_EQ` (YXIONXL.hl:950). -/
theorem TRANS_MOD_EQ {k i x : ℕ} (hk : k ≠ 0) :
    (i + (x + k - i % k) % k) % k = x % k := by
  have hlt : i % k < k := Nat.mod_lt i (by omega)
  have h1 : Nat.ModEq k (i + (x + k - i % k) % k) (i % k + (x + k - i % k) % k) :=
    (Nat.ModEq.add_right _ (Nat.mod_modEq i k)).symm
  have h2 : Nat.ModEq k (i % k + (x + k - i % k) % k) (i % k + (x + k - i % k)) :=
    Nat.ModEq.add_left _ (Nat.mod_modEq (x + k - i % k) k)
  calc (i + (x + k - i % k) % k) % k
      = (i % k + (x + k - i % k) % k) % k := h1
    _ = (i % k + (x + k - i % k)) % k := h2
    _ = (x + k) % k := by rw [show i % k + (x + k - i % k) = x + k from by omega]
    _ = x % k := Nat.add_mod_right x k

/-- HOL `TRANS_MOD_EQ_SUC` (YXIONXL.hl:964). -/
theorem TRANS_MOD_EQ_SUC {k i x : ℕ} (hk : 1 < k) :
    (i + ((x + k - i % k) % k + 1)) % k = (x + 1) % k := by
  have hk0 : k ≠ 0 := by omega
  rw [← Nat.add_assoc, Nat.add_mod (i + (x + k - i % k) % k) 1 k, Nat.add_mod x 1 k,
    TRANS_MOD_EQ hk0]

/-- HOL `TRANS_ID_INDEX` (YXIONXL.hl:1937). -/
theorem TRANS_ID_INDEX {k i j : ℕ} (hk : k ≠ 0) :
    (k - i % k + i + j) % k = j % k := by
  have hlt : i % k < k := Nat.mod_lt i (by omega)
  have hle : i % k ≤ i := Nat.mod_le i k
  have hkey : (i - i % k) % k = 0 := by
    have h := Nat.ModEq.sub_left (Nat.mod_le i k) (le_refl i) (Nat.mod_modEq i k)
    simpa [Nat.ModEq] using h
  rw [show k - i % k + i = k + (i - i % k) from by omega, Nat.add_assoc,
    Nat.add_comm k ((i - i % k) + j), Nat.add_mod_right, ← Nat.mod_add_mod, hkey,
    Nat.zero_add]

/-- HOL `TRANSTER_IS_UNADORNED` (YXIONXL.hl:314; source typo kept). -/
theorem TRANSTER_IS_UNADORNED {s t : ScsV39} (htr : transferV39 s t) :
    unadornedV39 t := htr.2.2.1

/-- HOL `scs_k_le_3` (YXIONXL.hl:2270). -/
theorem scs_k_le_3 {s : ScsV39} (hs : isScsV39 s) : 3 ≤ s.k := hs.2.1

/-- Cyclic-shift `funext` kit: if `φ j` has the same residue as `j` mod `k`,
then precomposition with `φ` fixes every `k`-`Periodic2` function. -/
private theorem shiftBy_eq {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (hper : Periodic2 f k) (φ : ℕ → ℕ) (hφ : ∀ j, φ j % k = j % k) :
    (fun j j' => f (φ j) (φ j')) = f := by
  funext j j'
  calc f (φ j) (φ j')
      = f (φ j % k) (φ j') := (periodic2Mod1 hk hper _ _).symm
    _ = f (j % k) (φ j') := by rw [hφ j]
    _ = f (j % k) (φ j' % k) := (periodic2Mod2 hk hper _ _).symm
    _ = f (j % k) (j' % k) := by rw [hφ j']
    _ = f j (j' % k) := periodic2Mod1 hk hper j (j' % k)
    _ = f j j' := periodic2Mod2 hk hper j j'

/-- One-argument `shiftBy_eq`. -/
private theorem shiftBy1_eq {α : Sort u} {f : ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (hper : Periodic f k) (φ : ℕ → ℕ) (hφ : ∀ j, φ j % k = j % k) :
    (fun j => f (φ j)) = f := by
  funext j
  calc f (φ j)
      = f (φ j % k) := (periodicMod hk hper _).symm
    _ = f (j % k) := by rw [hφ j]
    _ = f j := periodicMod hk hper j

/-! ## Section 1: transfer of the BB*/MM* tower (source order) -/

set_option linter.unusedVariables false in
/-- HOL `TRANSFER_SUBSET_BB` (YXIONXL.hl:61): `BBs_v39` realisations
transfer along `transfer_v39`. -/
theorem TRANSFER_SUBSET_BB {s t : ScsV39} {ww : ℕ → V3} (hs : isScsV39 s)
    (ht : isScsV39 t) (hk : t.k = s.k) (htr : transferV39 s t) (hBB : BBsV39 s ww) :
    BBsV39 t ww := by
  rcases Classical.em (isEarV39 s) with he | he
  · have hst : s = t := htr.1 he
    subst hst
    exact hBB
  · have ha : ∀ i j, t.a i j ≤ s.a i j := htr.2.2.2.2.2.1
    have hb : ∀ i j, s.b i j ≤ t.b i j := htr.2.2.2.2.2.2.1
    obtain ⟨hball, hper, hdist, hfan⟩ := hBB
    refine ⟨hball, ?_, fun i j => ⟨(ha i j).trans (hdist i j).1,
      (hdist i j).2.trans (hb i j)⟩, ?_⟩
    · show Periodic ww t.k
      rw [hk]; exact hper
    · rw [hk]; exact hfan

set_option linter.unusedVariables false in
/-- HOL `DSV_LE_DSV_TRANSFER` (YXIONXL.hl:106): the dsv defect decreases
along a transfer (the sign flips of `dsv_v39` are why the ear cases
matter). -/
theorem DSV_LE_DSV_TRANSFER {s t : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (ht : isScsV39 t) (hk : t.k = s.k) (htr : transferV39 s t) (hBB : BBsV39 s vv) :
    dsvV39 s vv ≤ dsvV39 t vv := by
  have hJob : ∀ i j, t.J i j → s.J i j := htr.2.2.2.2.2.2.2
  have hJab : ∀ i j, s.J i j → s.b i j = cstab := by
    unfold isScsV39 at hs
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hJab, -⟩ := hs
    exact fun i j h => (hJab i j h).2
  have hdist : ∀ i j, dist (vv i) (vv j) ≤ s.b i j := fun i j => (hBB.2.2.1 i j).2
  have hsub : {x | x < t.k ∧ t.J x (x + 1)} ⊆ {x | x < s.k ∧ s.J x (x + 1)} := by
    rintro x ⟨hx, hJ⟩
    exact ⟨hk ▸ hx, hJob x (x + 1) hJ⟩
  have hfinS : {x | x < s.k ∧ s.J x (x + 1)}.Finite :=
    (Set.finite_Iio s.k).subset fun x hx => hx.1
  have hfinT : {x | x < t.k ∧ t.J x (x + 1)}.Finite :=
    (Set.finite_Iio t.k).subset fun x hx => hx.1
  have hposS : ∀ x ∈ {x | x < s.k ∧ s.J x (x + 1)},
      0 ≤ cstab - dist (vv x) (vv (x + 1)) := by
    rintro x ⟨hx, hJ⟩
    have hb : dist (vv x) (vv (x + 1)) ≤ s.b x (x + 1) := hdist x (x + 1)
    rw [hJab x (x + 1) hJ] at hb
    linarith
  have hsum : setSum {x | x < t.k ∧ t.J x (x + 1)}
        (fun i => cstab - dist (vv i) (vv (i + 1))) ≤
      setSum {x | x < s.k ∧ s.J x (x + 1)}
        (fun i => cstab - dist (vv i) (vv (i + 1))) :=
    setSum_le_setSum_of_subset hsub (fun x hx => hposS x hx) hfinS
  have h0S : 0 ≤ setSum {x | x < s.k ∧ s.J x (x + 1)}
      (fun i => cstab - dist (vv i) (vv (i + 1))) := setSum_nonneg hposS hfinS
  have h0T : 0 ≤ setSum {x | x < t.k ∧ t.J x (x + 1)}
      (fun i => cstab - dist (vv i) (vv (i + 1))) := by
    refine setSum_nonneg (fun x hx => ?_) hfinT
    obtain ⟨hx, hJ⟩ := hx
    have hb : dist (vv x) (vv (x + 1)) ≤ s.b x (x + 1) := hdist x (x + 1)
    rw [hJab x (x + 1) (hJob x (x + 1) hJ)] at hb
    linarith
  have hsd : s.d ≤ t.d := htr.2.2.2.1
  unfold dsvV39
  rcases Classical.em (isEarV39 s) with he | he
  · rw [htr.1 he]
  · rw [if_neg he]
    rcases Classical.em (isEarV39 t) with het | het
    · rw [if_pos het]; linarith
    · rw [if_neg het]; linarith

/-- HOL `TAUSTAR_LE_TAUSTAR_TRANSFER` (YXIONXL.hl:297). -/
theorem TAUSTAR_LE_TAUSTAR_TRANSFER {s t : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (ht : isScsV39 t) (hk : t.k = s.k) (htr : transferV39 s t) (hBB : BBsV39 s vv) :
    taustarV39 t vv ≤ taustarV39 s vv := by
  have hd := DSV_LE_DSV_TRANSFER hs ht hk htr hBB
  unfold taustarV39
  by_cases hk3 : t.k ≤ 3
  · have hs3 : s.k ≤ 3 := hk ▸ hk3
    rw [if_pos hk3, if_pos hs3]; linarith
  · have hs3 : ¬ s.k ≤ 3 := fun h => hk3 (hk ▸ h)
    rw [if_neg hk3, if_neg hs3]; linarith

set_option linter.unusedVariables false in
/-- NEEDS: HOL `SGTRNAF` (sgtrnaf.hl:166): `is_scs_v39 s /\ unadorned_v39 s
/\ vv IN BBs_v39 s /\ taustar_v39 s vv < &0 ==> ~(MMs_v39 s = {})`.  No
importable port exists; the HOL proof consumes `unadorned_MMs` (the
`unadorned_MMs_concl` registry item of LocalAuto1) and `UXCKFPE2`
(uxckfpe.hl, unported), so this anchor stays `sorry` until those land. -/
theorem sgtrnaf_p12 {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hu : unadornedV39 s) (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) :
    MMsV39 s ≠ ∅ := sorry

/-- HOL `NOT_EMPETY_MMS_TRANSFER` (YXIONXL.hl:320; source typo kept).
Proved modulo the `sgtrnaf_p12` anchor. -/
theorem NOT_EMPETY_MMS_TRANSFER {s t : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (ht : isScsV39 t) (hk : t.k = s.k) (htr : transferV39 s t)
    (hM : vv ∈ MMsV39 s) : ∃ ww, ww ∈ MMsV39 t := by
  have hBB2 : vv ∈ BBprime2V39 s := hM.1
  have hBB : BBsV39 s vv := hBB2.1.1
  have hta : taustarV39 s vv < 0 := hBB2.1.2.2
  have hBBt : BBsV39 t vv := TRANSFER_SUBSET_BB hs ht hk htr hBB
  have htaT : taustarV39 t vv < 0 :=
    lt_of_le_of_lt (TAUSTAR_LE_TAUSTAR_TRANSFER hs ht hk htr hBB) hta
  exact (Set.nonempty_iff_ne_empty (s := MMsV39 t)).mpr
    (sgtrnaf_p12 ht (TRANSTER_IS_UNADORNED htr) hBBt htaT)

/-- HOL `YXIONXL1` (YXIONXL.hl:338). -/
theorem YXIONXL1 {s t : ScsV39} (hs : isScsV39 s) (htr : transferV39 s t) :
    scsArrowV39 {s} {t} := by
  refine ⟨fun u hu => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hu
    rw [hu]
    exact htr.2.1
  · by_cases hM : MMsV39 s = ∅
    · refine Or.inl fun u hu => ?_
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact hM
    · refine Or.inr ?_
      obtain ⟨vv, hvv⟩ := (Set.nonempty_iff_ne_empty (s := MMsV39 s)).mpr hM
      obtain ⟨ww, hww⟩ := NOT_EMPETY_MMS_TRANSFER hs htr.2.1
        htr.2.2.2.2.1 htr hvv
      refine ⟨t, Set.mem_singleton t, ?_⟩
      exact Set.Nonempty.ne_empty ⟨ww, hww⟩

/-! ## Section 2: cyclic images of a realisation (source order TRANS_V,
TRANS_FF, TRANS_E, BB_TRANS_SUBSET_BB) -/

/-- HOL `TRANS_V` (YXIONXL.hl:369): re-indexing by `i + x` does not change
the vertex set of a realisation. -/
theorem TRANS_V {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (i : ℕ) :
    Set.range (fun x => vv (i + x)) = Set.range vv := by
  have h3 : 3 ≤ s.k := scs_k_le_3 hs
  have hk0 : s.k ≠ 0 := by omega
  have hper := hBB.2.1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨i + x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(x + s.k - i % s.k) % s.k, ?_⟩
    show vv (i + (x + s.k - i % s.k) % s.k) = vv x
    calc vv (i + (x + s.k - i % s.k) % s.k)
        = vv ((i + (x + s.k - i % s.k) % s.k) % s.k) :=
          (periodicMod hk0 hper _).symm
      _ = vv (x % s.k) := congrArg vv (TRANS_MOD_EQ (i := i) (x := x) hk0)
      _ = vv x := periodicMod hk0 hper x

/-- Private residue-shift equality for vertices (the workhorse of the
TRANS_FF/TRANS_E reverse inclusions). -/
private theorem vvShift_eq {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (i x : ℕ) :
    vv (i + (x + s.k - i % s.k) % s.k) = vv x := by
  have h3 : 3 ≤ s.k := scs_k_le_3 hs
  have hk0 : s.k ≠ 0 := by omega
  have hper := hBB.2.1
  calc vv (i + (x + s.k - i % s.k) % s.k)
      = vv ((i + (x + s.k - i % s.k) % s.k) % s.k) := (periodicMod hk0 hper _).symm
    _ = vv (x % s.k) := congrArg vv (TRANS_MOD_EQ (i := i) (x := x) hk0)
    _ = vv x := periodicMod hk0 hper x

/-- Successor variant of `vvShift_eq` (HOL `TRANS_MOD_EQ_SUC` at work). -/
private theorem vvShiftSUC_eq {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (i x : ℕ) :
    vv (i + (x + s.k - i % s.k) % s.k + 1) = vv (x + 1) := by
  have h3 : 3 ≤ s.k := scs_k_le_3 hs
  have hlt : 1 < s.k := by omega
  have hk0 : s.k ≠ 0 := by omega
  have hper := hBB.2.1
  have hTS := TRANS_MOD_EQ_SUC (i := i) (x := x) hlt
  have hmod : i + (x + s.k - i % s.k) % s.k + 1
      = i + ((x + s.k - i % s.k) % s.k + 1) := by omega
  calc vv (i + (x + s.k - i % s.k) % s.k + 1)
      = vv ((i + (x + s.k - i % s.k) % s.k + 1) % s.k) := (periodicMod hk0 hper _).symm
    _ = vv ((i + ((x + s.k - i % s.k) % s.k + 1)) % s.k) := by rw [hmod]
    _ = vv ((x + 1) % s.k) := congrArg vv hTS
    _ = vv (x + 1) := periodicMod hk0 hper (x + 1)

/-- HOL `TRANS_FF` (YXIONXL.hl:427): re-indexing does not change the dart
set of a realisation. -/
theorem TRANS_FF {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (i : ℕ) :
    Set.range (fun x => (vv (i + x), vv (i + x + 1)))
      = Set.range (fun x => (vv x, vv (x + 1))) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨i + x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(x + s.k - i % s.k) % s.k, ?_⟩
    show (vv (i + (x + s.k - i % s.k) % s.k),
        vv (i + (x + s.k - i % s.k) % s.k + 1)) = (vv x, vv (x + 1))
    rw [vvShift_eq hs hBB i x, vvShiftSUC_eq hs hBB i x]

/-- HOL `TRANS_E` (YXIONXL.hl:496): re-indexing does not change the edge
set of a realisation. -/
theorem TRANS_E {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (i : ℕ) :
    Set.range (fun x => ({vv (i + x), vv (i + x + 1)} : Set V3))
      = Set.range (fun x => ({vv x, vv (x + 1)} : Set V3)) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨i + x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(x + s.k - i % s.k) % s.k, ?_⟩
    show {vv (i + (x + s.k - i % s.k) % s.k),
        vv (i + (x + s.k - i % s.k) % s.k + 1)} = {vv x, vv (x + 1)}
    rw [vvShift_eq hs hBB i x, vvShiftSUC_eq hs hBB i x]

/-- HOL `BB_TRANS_SUBSET_BB` (YXIONXL.hl:567): the shifted realisation
realises the cyclic re-indexing `scs_prop_equ_v39 s i`. -/
theorem BB_TRANS_SUBSET_BB {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (i : ℕ) :
    BBsV39 (scsPropEquV39 s i) (fun x => vv (i + x)) := by
  have hBBfull : BBsV39 s vv := hBB
  obtain ⟨hball, hper, hdist, hfan⟩ := hBB
  refine ⟨?_, ?_, fun j j' => hdist (i + j) (i + j'), ?_⟩
  · rintro y ⟨x, rfl⟩
    exact hball ⟨i + x, rfl⟩
  · intro y
    show vv (i + (y + s.k)) = vv (i + y)
    rw [← add_assoc]
    exact hper (i + y)
  · rcases hfan with h3 | hF
    · exact Or.inl h3
    · refine Or.inr ?_
      show ConvexLocalFan (Set.range (fun x => vv (i + x)))
        (Set.range (fun j => {vv (i + j), vv (i + j + 1)}))
        (Set.range (fun j => (vv (i + j), vv (i + j + 1))))
      rw [TRANS_V hs hBBfull i, TRANS_E hs hBBfull i, TRANS_FF hs hBBfull i]
      exact hF

/-! ## Section 3: invariance under `scs_prop_equ_v39` (source order) -/

/-- HOL `PROP_EQU_IS_SCS` (YXIONXL.hl:589).  NEEDS: the heavy conjunct is
the `is_scs_v39` ncard bound, which in HOL goes through
`CARD_IMAGE_INJ_EQ` for the bijection `j ↦ (i + j) % k` on `{0..k-1}`;
deferred (DISCHARGES). -/
theorem PROP_EQU_IS_SCS {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) : isScsV39 (scsPropEquV39 s i) := sorry

/-- HOL `PRO_EQU_IS_EAR` (YXIONXL.hl:978).  NEEDS: both directions reduce
to the 3-cycle bijection `j ↦ (i + j) % 3` on the J-singleton set plus
`TRANS_MOD_EQ` residue transport; the reverse direction also uses
`PRO_EQU_ID1`.  Deferred (DISCHARGES). -/
theorem PRO_EQU_IS_EAR {s : ScsV39} (hs : isScsV39 s) (i : ℕ) :
    isEarV39 s ↔ isEarV39 (scsPropEquV39 s i) := sorry

/-- HOL `PRO_EQU_DSV_EQ` (YXIONXL.hl:1523).  NEEDS: `PRO_EQU_IS_EAR` for
the ear sign plus a `SUM_EQ_GENERAL` reindexing `y ↦ (y + k - i % k) % k`
of the dsv sums.  Deferred (DISCHARGES). -/
theorem PRO_EQU_DSV_EQ {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (i : ℕ) :
    dsvV39 (scsPropEquV39 s i) (fun x => vv (i + x)) = dsvV39 s vv := sorry

/-- HOL `PRO_EQU_TAUSTAR_EQ` (YXIONXL.hl:1833).  NEEDS: `PRO_EQU_DSV_EQ`
plus HOL `SUM_AZIM_EQ_ANGLE_LE4` (Hdplygy lane, unported) for the tau_fun
re-indexing.  Deferred (DISCHARGES). -/
theorem PRO_EQU_TAUSTAR_EQ {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (i : ℕ) :
    taustarV39 (scsPropEquV39 s i) (fun j => vv (i + j)) = taustarV39 s vv := sorry

/-- HOL `TRANS_SCS_A_ID` (YXIONXL.hl:1961). -/
theorem TRANS_SCS_A_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) :
    (fun j j' => s.a (k - i % k + i + j) (k - i % k + i + j')) = s.a := by
  subst hk
  obtain ⟨-, h3, -, -, -, -, -, hpa, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  exact shiftBy_eq hk0 hpa (fun j => s.k - i % s.k + i + j)
    (fun j => TRANS_ID_INDEX (i := i) (j := j) hk0)

/-- HOL `TRANS_SCS_A_ID_MOD` (YXIONXL.hl:1986). -/
theorem TRANS_SCS_A_ID_MOD {s : ScsV39} {k : ℕ} (hk : s.k = k)
    (hs : isScsV39 s) (i : ℕ) :
    (fun j j' => s.a (i + (j + k - i % k) % k) (i + (j' + k - i % k) % k)) = s.a := by
  subst hk
  obtain ⟨-, h3, -, -, -, -, -, hpa, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  exact shiftBy_eq hk0 hpa (fun j => i + (j + s.k - i % s.k) % s.k)
    (fun j => TRANS_MOD_EQ (i := i) (x := j) hk0)

/-- HOL `TRANS_SCS_B_ID` (YXIONXL.hl:2014). -/
theorem TRANS_SCS_B_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) :
    (fun j j' => s.b (k - i % k + i + j) (k - i % k + i + j')) = s.b := by
  subst hk
  obtain ⟨-, h3, -, -, -, -, -, -, -, -, hpb, -, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  exact shiftBy_eq hk0 hpb (fun j => s.k - i % s.k + i + j)
    (fun j => TRANS_ID_INDEX (i := i) (j := j) hk0)

/-- HOL `TRANS_SCS_AM_ID` (YXIONXL.hl:2041). -/
theorem TRANS_SCS_AM_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) :
    (fun j j' => s.am (k - i % k + i + j) (k - i % k + i + j')) = s.am := by
  subst hk
  obtain ⟨-, h3, -, -, -, -, -, -, hpam, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  exact shiftBy_eq hk0 hpam (fun j => s.k - i % s.k + i + j)
    (fun j => TRANS_ID_INDEX (i := i) (j := j) hk0)

/-- HOL `TRANS_SCS_BM_ID` (YXIONXL.hl:2067). -/
theorem TRANS_SCS_BM_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) :
    (fun j j' => s.bm (k - i % k + i + j) (k - i % k + i + j')) = s.bm := by
  subst hk
  obtain ⟨-, h3, -, -, -, -, -, -, -, hpbm, -, -, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  exact shiftBy_eq hk0 hpbm (fun j => s.k - i % s.k + i + j)
    (fun j => TRANS_ID_INDEX (i := i) (j := j) hk0)

/-- HOL `TRANS_SCS_J_ID` (YXIONXL.hl:2096). -/
theorem TRANS_SCS_J_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) :
    (fun j j' => s.J (k - i % k + i + j) (k - i % k + i + j')) = s.J := by
  subst hk
  obtain ⟨-, h3, -, -, -, -, -, -, -, -, -, hpJ, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  exact shiftBy_eq hk0 hpJ (fun j => s.k - i % s.k + i + j)
    (fun j => TRANS_ID_INDEX (i := i) (j := j) hk0)

/-- HOL `TRANS_SCS_LO_ID` (YXIONXL.hl:2127). -/
theorem TRANS_SCS_LO_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) :
    (fun j => s.lo (k - i % k + i + j)) = s.lo := by
  subst hk
  obtain ⟨-, h3, -, hplo, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  exact shiftBy1_eq hk0 hplo (fun j => s.k - i % s.k + i + j)
    (fun j => TRANS_ID_INDEX (i := i) (j := j) hk0)

/-- HOL `TRANS_SCS_HI_ID` (YXIONXL.hl:2146). -/
theorem TRANS_SCS_HI_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) :
    (fun j => s.hi (k - i % k + i + j)) = s.hi := by
  subst hk
  obtain ⟨-, h3, -, -, hphi, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  exact shiftBy1_eq hk0 hphi (fun j => s.k - i % s.k + i + j)
    (fun j => TRANS_ID_INDEX (i := i) (j := j) hk0)

/-- HOL `TRANS_SCS_STR_ID` (YXIONXL.hl:2165). -/
theorem TRANS_SCS_STR_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) :
    (fun j => s.str (k - i % k + i + j)) = s.str := by
  subst hk
  obtain ⟨-, h3, -, -, -, hpstr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  exact shiftBy1_eq hk0 hpstr (fun j => s.k - i % s.k + i + j)
    (fun j => TRANS_ID_INDEX (i := i) (j := j) hk0)

/-- HOL `PRO_EQU_ID` (YXIONXL.hl:2185). -/
theorem PRO_EQU_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) :
    s = scsPropEquV39 (scsPropEquV39 s (k - i % k)) i := by
  subst hk
  obtain ⟨-, h3, -, hplo, hphi, hpstr, -, hpa, hpam, hpbm, hpb, hpJ,
    -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  set m := s.k - i % s.k with hmdef
  have hφ : ∀ j, (m + (i + j)) % s.k = j % s.k := fun j => by
    rw [hmdef, ← add_assoc]; exact TRANS_ID_INDEX (i := i) (j := j) hk0
  have hcomp : scsPropEquV39 (scsPropEquV39 s m) i
      = ScsV39.mk s.k s.d s.a s.am s.bm s.b s.J s.lo s.hi s.str := by
    simp only [scsPropEquV39, hmdef]
    rw [shiftBy_eq hk0 hpa (fun j => m + (i + j)) hφ,
      shiftBy_eq hk0 hpam (fun j => m + (i + j)) hφ,
      shiftBy_eq hk0 hpbm (fun j => m + (i + j)) hφ,
      shiftBy_eq hk0 hpb (fun j => m + (i + j)) hφ,
      shiftBy_eq hk0 hpJ (fun j => m + (i + j)) hφ,
      shiftBy1_eq hk0 hplo (fun j => m + (i + j)) hφ,
      shiftBy1_eq hk0 hphi (fun j => m + (i + j)) hφ,
      shiftBy1_eq hk0 hpstr (fun j => m + (i + j)) hφ]
  have e : s = ScsV39.mk s.k s.d s.a s.am s.bm s.b s.J s.lo s.hi s.str := rfl
  rw [hcomp, e]

/-- HOL `PRO_EQU_ID1` (YXIONXL.hl:2212). -/
theorem PRO_EQU_ID1 {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) :
    s = scsPropEquV39 (scsPropEquV39 s i) (k - i % k) := by
  subst hk
  obtain ⟨-, h3, -, hplo, hphi, hpstr, -, hpa, hpam, hpbm, hpb, hpJ,
    -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  set m := s.k - i % s.k with hmdef
  have hφ : ∀ j, (i + (m + j)) % s.k = j % s.k := fun j => by
    rw [← add_assoc, add_comm i m, hmdef]; exact TRANS_ID_INDEX (i := i) (j := j) hk0
  have hcomp : scsPropEquV39 (scsPropEquV39 s i) m
      = ScsV39.mk s.k s.d s.a s.am s.bm s.b s.J s.lo s.hi s.str := by
    simp only [scsPropEquV39, hmdef]
    rw [shiftBy_eq hk0 hpa (fun j => i + (m + j)) hφ,
      shiftBy_eq hk0 hpam (fun j => i + (m + j)) hφ,
      shiftBy_eq hk0 hpbm (fun j => i + (m + j)) hφ,
      shiftBy_eq hk0 hpb (fun j => i + (m + j)) hφ,
      shiftBy_eq hk0 hpJ (fun j => i + (m + j)) hφ,
      shiftBy1_eq hk0 hplo (fun j => i + (m + j)) hφ,
      shiftBy1_eq hk0 hphi (fun j => i + (m + j)) hφ,
      shiftBy1_eq hk0 hpstr (fun j => i + (m + j)) hφ]
  have e : s = ScsV39.mk s.k s.d s.a s.am s.bm s.b s.J s.lo s.hi s.str := rfl
  rw [hcomp, e]

/-- HOL `PROP_EQU_EQ_BB` (YXIONXL.hl:2241): proved here from
`BB_TRANS_SUBSET_BB` + `PRO_EQU_ID1` (the HOL proof goes through the
taustar kit instead). -/
theorem PROP_EQU_EQ_BB {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) {vv : ℕ → V3} (hse : isScsV39 (scsPropEquV39 s i))
    (hBB : BBsV39 (scsPropEquV39 s i) vv) :
    BBsV39 s (fun x => vv (k - i % k + x)) := by
  subst hk
  have h1 : BBsV39 (scsPropEquV39 (scsPropEquV39 s i) (s.k - i % s.k))
      (fun x => vv (s.k - i % s.k + x)) :=
    BB_TRANS_SUBSET_BB hse hBB (s.k - i % s.k)
  rw [← PRO_EQU_ID1 rfl hs i] at h1
  exact h1

/-- HOL `TRANS_SCS_WW_ID` (YXIONXL.hl:2251). -/
theorem TRANS_SCS_WW_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hk3 : 3 ≤ k)
    (i : ℕ) {ww : ℕ → V3} (hBB : BBsV39 (scsPropEquV39 s i) ww) :
    (fun j => ww (k - i % k + i + j)) = ww := by
  subst hk
  have hk0 : s.k ≠ 0 := by omega
  exact shiftBy1_eq hk0 hBB.2.1 (fun j => s.k - i % s.k + i + j)
    (fun j => TRANS_ID_INDEX (i := i) (j := j) hk0)

/-- HOL `TRANS_SCS_BBPRIME` (YXIONXL.hl:2275).  NEEDS:
`PRO_EQU_TAUSTAR_EQ` (for the taustar clause) plus `PROP_EQU_EQ_BB` /
`TRANS_SCS_WW_ID` for the minimality clause.  Deferred (DISCHARGES). -/
theorem TRANS_SCS_BBPRIME {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hbp : vv ∈ BBprimeV39 s) (i : ℕ) :
    (fun x => vv (i + x)) ∈ BBprimeV39 (scsPropEquV39 s i) := sorry

/-- HOL `TRANS_BBINDEX_ID` (YXIONXL.hl:2299).  NEEDS: the ncard bijection
`j ↦ (i + j) % k` (HOL `CARD_IMAGE_INJ_EQ`) between the two BBindex
counting sets.  Deferred (DISCHARGES). -/
theorem TRANS_BBINDEX_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) {vv : ℕ → V3} (hBB : BBsV39 s vv) :
    BBindexV39 (scsPropEquV39 s i) (fun x => vv (i + x)) = BBindexV39 s vv := sorry

/-- HOL `PROP_EQU_EQ_BBPRIME` (YXIONXL.hl:2487).  NEEDS:
`TRANS_SCS_BBPRIME` and `PRO_EQU_ID1`.  Deferred (DISCHARGES). -/
theorem PROP_EQU_EQ_BBPRIME {s : ScsV39} {k : ℕ} (hk : s.k = k)
    (hs : isScsV39 s) (i : ℕ) {vv : ℕ → V3}
    (hbp : vv ∈ BBprimeV39 (scsPropEquV39 s i)) :
    (fun x => vv (k - i % k + x)) ∈ BBprimeV39 s := sorry

/-- HOL `TRANS_IMAGE_BBINDEX_EQ` (YXIONXL.hl:2497).  NEEDS:
`PROP_EQU_IS_SCS`, `TRANS_SCS_BBPRIME`, `PROP_EQU_EQ_BBPRIME`,
`TRANS_BBINDEX_ID`.  Deferred (DISCHARGES). -/
theorem TRANS_IMAGE_BBINDEX_EQ {s : ScsV39} {k : ℕ} (hk : s.k = k)
    (hs : isScsV39 s) (i : ℕ) :
    BBindexV39 (scsPropEquV39 s i) '' BBprimeV39 (scsPropEquV39 s i)
      = BBindexV39 s '' BBprimeV39 s := sorry

/-- HOL `TRANS_BBINDEX_MIN_EQ` (YXIONXL.hl:2531).  NEEDS:
`TRANS_IMAGE_BBINDEX_EQ` (then the two `minNum` sets agree).  Deferred
(DISCHARGES). -/
theorem TRANS_BBINDEX_MIN_EQ {s : ScsV39} {k : ℕ} (hk : s.k = k)
    (hs : isScsV39 s) (i : ℕ) {vv : ℕ → V3} (hBB : BBsV39 s vv) :
    BBindexMinV39 (scsPropEquV39 s i) = BBindexMinV39 s := sorry

/-- HOL `TRANS_BBPRIME2_SUBSET` (YXIONXL.hl:2542).  NEEDS:
`TRANS_SCS_BBPRIME` + `TRANS_BBINDEX_MIN_EQ` + `TRANS_BBINDEX_ID`.
Deferred (DISCHARGES). -/
theorem TRANS_BBPRIME2_SUBSET {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hbp2 : vv ∈ BBprime2V39 s) (i : ℕ) :
    (fun x => vv (i + x)) ∈ BBprime2V39 (scsPropEquV39 s i) := sorry

/-- HOL `TRANS_MMS_SUBSET` (YXIONXL.hl:2559).  NEEDS:
`TRANS_BBPRIME2_SUBSET` plus the str/lo/hi/am/bm clauses of `MMs_v39`
(residue transports of the `azim`/`norm` side conditions).  Deferred
(DISCHARGES). -/
theorem TRANS_MMS_SUBSET {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hm : vv ∈ MMsV39 s) (i : ℕ) :
    (fun x => vv (i + x)) ∈ MMsV39 (scsPropEquV39 s i) := sorry

/-- HOL `YXIONXL3` (YXIONXL.hl:2573): the cyclic re-indexing is an arrow.
NEEDS: `PROP_EQU_IS_SCS` and `TRANS_MMS_SUBSET` (via the `scs_arrow_v39`
MMs clause, as in HOL).  Deferred (DISCHARGES). -/
theorem YXIONXL3 (s : ScsV39) (i : ℕ) (hs : isScsV39 s) :
    scsArrowV39 {s} {scsPropEquV39 s i} := sorry
