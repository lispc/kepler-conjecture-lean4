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

PROOF STATUS: 38 of the 39 theorems proved outright; 1 sorry'd with a
per-item NEEDS note (the `sgtrnaf_p12` anchor).  NOT_EMPETY_MMS_TRANSFER
and YXIONXL1 rest on that anchor.  The whole `scs_prop_equ_v39`
invariance chain of Section 3 is proved in-file: `PROP_EQU_IS_SCS` /
`TRANS_BBINDEX_ID` via the residue bijection `y ↦ (y + k - i % k) % k`
(`Set.InjOn.ncard_image`), `PRO_EQU_IS_EAR` via the 3-cycle transport +
`PRO_EQU_ID1`, `PRO_EQU_DSV_EQ` via a `SUM_EQ_GENERAL`-shaped setSum
re-index, `PRO_EQU_TAUSTAR_EQ` via `tau3` cyclicity (k = 3) and the
range equalities `TRANS_V`/`TRANS_E`/`TRANS_FF` (k > 3 — the HOL detour
through `SUM_AZIM_EQ_ANGLE_LE4` is unnecessary on this route), and the
BBprime/BBindex/MMs transports follow the HOL dependency order.

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
    from uxckfpe.hl, also unported; the LocalAuto27 wave items
    `unadorned_MMs_p27`/`AYQJTMD_p27` were still `sorry` at fill time).
    The chain NOT_EMPETY_MMS_TRANSFER -> YXIONXL1 is proved modulo that
    anchor.
  - The former giants of Section 3 (PROP_EQU_IS_SCS, PRO_EQU_IS_EAR,
    PRO_EQU_DSV_EQ, PRO_EQU_TAUSTAR_EQ, the BBindex image/min kit,
    TRANS_MMS_SUBSET, YXIONXL3) are now PROVED in-file — see the header
    PROOF STATUS note for the route map.

DISCHARGES: nothing yet (the `sgtrnaf_p12` anchor stays `sorry`;
DISCHARGES convention — later waves prove it and the `sorry` disappears).
All other former gaps are closed in this file.  The remaining external
need is SGTRNAF/UXCKFPE2/`unadorned_MMs` (sgtrnaf.hl, uxckfpe.hl,
AYQJTMD.hl lane).
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

/-! ### Fill kit: residue transports for `scs_prop_equ_v39` -/

/-- Both coordinates reduced to their residues (`periodic2_mod_p17`
shape; the LocalAuto17 twin is not importable from here). -/
private theorem periodic2_mod_mod {α : Sort u} {k : ℕ} {g : ℕ → ℕ → α}
    (hk : k ≠ 0) (hper : Periodic2 g k) (a b : ℕ) : g (a % k) (b % k) = g a b :=
  (periodic2Mod1 hk hper a (b % k)).trans (periodic2Mod2 hk hper a b)

/-- Successor-pair transport: the value at the shifted pair `(i + x,
i + x + 1)` is the value at the reduced pair `((i + x) % k, (i + x) % k +
1)` (no reduction of the successor). -/
private theorem periodic2_shift_pair {α : Sort u} {k : ℕ} {g : ℕ → ℕ → α}
    (hk0 : k ≠ 0) (hper : Periodic2 g k) (i x : ℕ) :
    g (i + x) (i + x + 1) = g ((i + x) % k) ((i + x) % k + 1) := by
  have h2 : (i + x + 1) % k = ((i + x) % k + 1) % k :=
    ((Nat.mod_modEq (i + x) k).add_right 1).symm
  calc g (i + x) (i + x + 1)
      = g ((i + x) % k) (i + x + 1) :=
        (periodic2Mod1 (k := k) hk0 hper (i + x) (i + x + 1)).symm
    _ = g ((i + x) % k) ((i + x + 1) % k) :=
        (periodic2Mod2 (k := k) hk0 hper ((i + x) % k) (i + x + 1)).symm
    _ = g ((i + x) % k) (((i + x) % k + 1) % k) := by rw [h2]
    _ = g ((i + x) % k) ((i + x) % k + 1) :=
        periodic2Mod2 (k := k) hk0 hper ((i + x) % k) ((i + x) % k + 1)

/-- Vertex-distance twin of `periodic2_shift_pair`. -/
private theorem dist_shift_pair {k : ℕ} {vv : ℕ → V3} (hk : k ≠ 0)
    (hper : Periodic vv k) (i x : ℕ) :
    dist (vv (i + x)) (vv (i + x + 1)) =
      dist (vv ((i + x) % k)) (vv ((i + x) % k + 1)) := by
  have h2 : (i + x + 1) % k = ((i + x) % k + 1) % k :=
    ((Nat.mod_modEq (i + x) k).add_right 1).symm
  calc dist (vv (i + x)) (vv (i + x + 1))
      = dist (vv ((i + x) % k)) (vv (i + x + 1)) :=
        congrArg (fun w => dist w (vv (i + x + 1)))
          (periodicMod hk hper (i + x)).symm
    _ = dist (vv ((i + x) % k)) (vv ((i + x + 1) % k)) :=
        congrArg (dist (vv ((i + x) % k))) (periodicMod hk hper (i + x + 1)).symm
    _ = dist (vv ((i + x) % k)) (vv (((i + x) % k + 1) % k)) :=
        congrArg (dist (vv ((i + x) % k))) (congrArg vv h2)
    _ = dist (vv ((i + x) % k)) (vv ((i + x) % k + 1)) :=
        congrArg (dist (vv ((i + x) % k))) (periodicMod hk hper ((i + x) % k + 1))

/-- Cancel the shift in residues of close neighbours. -/
private theorem mod_pair_cancel {k i x y : ℕ} (hx : x < k) (hy : y < k)
    (h : (i + x) % k = (i + y) % k) : x = y := by
  have e : Nat.ModEq k x y :=
    Nat.ModEq.add_left_cancel' i h
  have e' : x % k = y % k := e
  have hx' : x % k = x := Nat.mod_eq_of_lt hx
  have hy' : y % k = y := Nat.mod_eq_of_lt hy
  omega

/-- Unbounded form: cancel the shift at the level of residues. -/
private theorem mod_pair_cancel' {k i x y : ℕ} (h : (i + x) % k = (i + y) % k) :
    x % k = y % k :=
  Nat.ModEq.add_left_cancel' i h

/-- The `TRANS_MOD_EQ` residue in reduced form. -/
private theorem psi_key {k i y : ℕ} (hk : k ≠ 0) (hy : y < k) :
    (i + (y + k - i % k) % k) % k = y :=
  (TRANS_MOD_EQ (i := i) (x := y) hk).trans (Nat.mod_eq_of_lt hy)

/-- The reduced shift of a residue is the residue again
(`ψ ∘ φ = id` on `{0..k-1}`). -/
private theorem mod_pair_roundtrip {k i x : ℕ} (hk : k ≠ 0) (hx : x < k) :
    ((i + x) % k + (k - i % k)) % k = x := by
  have hle : i % k ≤ i := Nat.mod_le i k
  have hmlt : i % k < k := Nat.mod_lt i (by omega)
  have hid : i - i % k + i % k = i := by omega
  have hsub : (i - i % k) % k = 0 := by
    have h := Nat.ModEq.sub_left (Nat.mod_le i k) (le_refl i) (Nat.mod_modEq i k)
    simpa [Nat.ModEq] using h
  have h2 : Nat.ModEq k ((i + x) % k + (k - i % k)) ((i + x) + (k - i % k)) :=
    (Nat.mod_modEq (i + x) k).add_right _
  have h3 : (i + x) + (k - i % k) = x + k + (i - i % k) := by omega
  have h4 : Nat.ModEq k ((i + x) + (k - i % k)) x := by
    have e1 : (x + k + (i - i % k)) % k = (x + (i - i % k)) % k := by
      rw [show x + k + (i - i % k) = x + (i - i % k) + k from by omega,
        Nat.add_mod_right]
    have e2 : (x + (i - i % k)) % k = x % k := by
      rw [Nat.add_mod, hsub, Nat.add_zero]
      exact Nat.mod_modEq x k
    rw [h3]
    show (x + k + (i - i % k)) % k = x % k
    rw [e1, e2]
  have h5 : Nat.ModEq k ((i + x) % k + (k - i % k)) x := h2.trans h4
  have h5' : ((i + x) % k + (k - i % k)) % k = x % k := h5
  rwa [Nat.mod_eq_of_lt hx] at h5'

/-- `setSum` re-indexing along an injective index transport (HOL
`SUM_EQ_GENERAL` shape, `setSum` rendering). -/
private theorem setSum_image_bij {A B : Set ℕ} {f g : ℕ → ℝ} (φ : ℕ → ℕ)
    (hB : B.Finite) (hmem : ∀ x ∈ B, φ x ∈ A)
    (hinj : Set.InjOn φ B) (hsurj : ∀ y ∈ A, ∃ x ∈ B, φ x = y)
    (hfg : ∀ x ∈ B, g x = f (φ x)) : setSum A f = setSum B g := by
  have hAB : A = φ '' B := by
    refine Set.ext fun z => ?_
    simp only [Set.mem_image]
    constructor
    · intro hz
      obtain ⟨x, hx, hφ⟩ := hsurj z hz
      exact ⟨x, hx, hφ⟩
    · rintro ⟨x, hx, rfl⟩
      exact hmem x hx
  rw [hAB, setSum, setSum, dif_pos (hB.image φ), dif_pos hB,
    Set.Finite.toFinset_image φ hB (hB.image φ),
    Finset.sum_image fun x hx y hy => hinj (by simpa using hx) (by simpa using hy)]
  refine Finset.sum_congr rfl fun x hx => ?_
  exact (hfg x (hB.mem_toFinset.mp hx)).symm

/-- The dsv index-set transport of `PRO_EQU_DSV_EQ`: the sum over the
J-successor set re-indexes along `x ↦ (i + x) % k`. -/
private theorem setSum_dsv_propEq {s : ScsV39} {vv : ℕ → V3} (hk0 : s.k ≠ 0)
    (hpJ : Periodic2 s.J s.k) (hper : Periodic vv s.k) (i : ℕ) :
    setSum {y | y < s.k ∧ s.J y (y + 1)}
        (fun y => cstab - dist (vv y) (vv (y + 1))) =
      setSum {x | x < s.k ∧ s.J (i + x) (i + x + 1)}
        (fun x => cstab - dist (vv (i + x)) (vv (i + x + 1))) := by
  have hBfin : {x | x < s.k ∧ s.J (i + x) (i + x + 1)}.Finite :=
    (Set.finite_Iio s.k).subset fun x hx => hx.1
  refine setSum_image_bij (φ := fun x => (i + x) % s.k)
    (A := {y | y < s.k ∧ s.J y (y + 1)})
    (B := {x | x < s.k ∧ s.J (i + x) (i + x + 1)})
    (f := fun y => cstab - dist (vv y) (vv (y + 1)))
    (g := fun x => cstab - dist (vv (i + x)) (vv (i + x + 1)))
    hBfin ?hmem ?hinj ?hsurj ?hfg
  case hmem =>
    trace_state
    rintro x ⟨hx, hJ⟩
    exact ⟨Nat.mod_lt (i + x) (by omega), by
      rwa [← periodic2_shift_pair hk0 hpJ i x]⟩
  case hinj =>
    rintro x ⟨hx, -⟩ y ⟨hy, -⟩ hxy
    exact mod_pair_cancel hx hy hxy
  case hsurj =>
    rintro y ⟨hy, hJy⟩
    refine ⟨(y + s.k - i % s.k) % s.k, ⟨Nat.mod_lt _ (by omega), ?_⟩, psi_key hk0 hy⟩
    rw [periodic2_shift_pair hk0 hpJ i ((y + s.k - i % s.k) % s.k), psi_key hk0 hy]
    exact hJy
  case hfg =>
    intro x _
    rw [dist_shift_pair hk0 hper i x]

/-- `tau3` is cyclically invariant (pure re-association of its three
dihedral summands). -/
private theorem tau3_cycle (a b c : V3) : tau3 a b c = tau3 b c a := by
  unfold tau3
  ring

/-- HOL `PROP_EQU_IS_SCS` (YXIONXL.hl:589).  The `is_scs_v39` ncard bound
goes through the bijection `y ↦ (y + k - i % k) % k` on `{0..k-1}`
(`Set.InjOn.ncard_image` replaces HOL `CARD_IMAGE_INJ_EQ`). -/
theorem PROP_EQU_IS_SCS {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) : isScsV39 (scsPropEquV39 s i) := by
  subst hk
  obtain ⟨hd, h3, hk6, hplo, hphi, hpstr, -, hpa, hpam, hpbm, hpb, hpJ, hsym,
    hch, hdiag0, hdiag, hb3, hbc, hJstruct, hJab, hcard⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  have hlt3 : 1 < s.k := by omega
  have himod : i % s.k ≤ s.k := le_of_lt (Nat.mod_lt i (by omega))
  refine ⟨hd, h3, hk6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show s.lo (i + (j + s.k)) = s.lo (i + j)
    rw [← add_assoc, hplo (i + j)]
  · intro j
    show s.hi (i + (j + s.k)) = s.hi (i + j)
    rw [← add_assoc, hphi (i + j)]
  · intro j
    show s.str (i + (j + s.k)) = s.str (i + j)
    rw [← add_assoc, hpstr (i + j)]
  · intro j
    show s.str (i + (j + s.k)) = s.str (i + j)
    rw [← add_assoc, hpstr (i + j)]
  · intro p q
    obtain ⟨h1, h2⟩ := hpa (i + p) (i + q)
    show s.a (i + (p + s.k)) (i + q) = s.a (i + p) (i + q) ∧
      s.a (i + p) (i + (q + s.k)) = s.a (i + p) (i + q)
    rw [← add_assoc, h1, ← add_assoc, h2]
    exact ⟨rfl, rfl⟩
  · intro p q
    obtain ⟨h1, h2⟩ := hpam (i + p) (i + q)
    show s.am (i + (p + s.k)) (i + q) = s.am (i + p) (i + q) ∧
      s.am (i + p) (i + (q + s.k)) = s.am (i + p) (i + q)
    rw [← add_assoc, h1, ← add_assoc, h2]
    exact ⟨rfl, rfl⟩
  · intro p q
    obtain ⟨h1, h2⟩ := hpbm (i + p) (i + q)
    show s.bm (i + (p + s.k)) (i + q) = s.bm (i + p) (i + q) ∧
      s.bm (i + p) (i + (q + s.k)) = s.bm (i + p) (i + q)
    rw [← add_assoc, h1, ← add_assoc, h2]
    exact ⟨rfl, rfl⟩
  · intro p q
    obtain ⟨h1, h2⟩ := hpb (i + p) (i + q)
    show s.b (i + (p + s.k)) (i + q) = s.b (i + p) (i + q) ∧
      s.b (i + p) (i + (q + s.k)) = s.b (i + p) (i + q)
    rw [← add_assoc, h1, ← add_assoc, h2]
    exact ⟨rfl, rfl⟩
  · intro p q
    obtain ⟨h1, h2⟩ := hpJ (i + p) (i + q)
    show s.J (i + (p + s.k)) (i + q) = s.J (i + p) (i + q) ∧
      s.J (i + p) (i + (q + s.k)) = s.J (i + p) (i + q)
    rw [← add_assoc, h1, ← add_assoc, h2]
    exact ⟨rfl, rfl⟩
  · intro p q
    obtain ⟨s1, s2, s3, s4, s5⟩ := hsym (i + p) (i + q)
    show s.a (i + p) (i + q) = s.a (i + q) (i + p) ∧
      s.am (i + p) (i + q) = s.am (i + q) (i + p) ∧
      s.bm (i + p) (i + q) = s.bm (i + q) (i + p) ∧
      s.b (i + p) (i + q) = s.b (i + q) (i + p) ∧
      s.J (i + p) (i + q) = s.J (i + q) (i + p)
    exact ⟨s1, s2, s3, s4, s5⟩
  · intro p q
    show s.a (i + p) (i + q) ≤ s.am (i + p) (i + q) ∧
      s.am (i + p) (i + q) ≤ s.bm (i + p) (i + q) ∧
      s.bm (i + p) (i + q) ≤ s.b (i + p) (i + q)
    exact hch (i + p) (i + q)
  · intro p
    show s.a (i + p) (i + p) = 0
    exact hdiag0 (i + p)
  · intro p q hpq
    have hp : p < s.k := hpq.1
    have hq : q < s.k := hpq.2.1
    show 2 ≤ s.a (i + p) (i + q)
    rw [← periodic2_mod_mod hk0 hpa]
    refine hdiag ((i + p) % s.k) ((i + q) % s.k)
      ⟨Nat.mod_lt (i + p) (by omega), Nat.mod_lt (i + q) (by omega), ?_⟩
    intro hcon
    exact hpq.2.2 (mod_pair_cancel hp hq hcon)
  · intro p hp3
    show s.b (i + p) (i + p + 1) < 4
    rw [periodic2_shift_pair hk0 hpb i p]
    exact hb3 ((i + p) % s.k) hp3
  · intro p hp6
    show s.b (i + p) (i + p + 1) ≤ cstab
    rw [periodic2_shift_pair hk0 hpb i p]
    exact hbc ((i + p) % s.k) hp6
  · intro p q hpq
    show q % s.k = (p + 1) % s.k ∨ p % s.k = (q + 1) % s.k
    have hJs : s.J (i + p) (i + q) := hpq
    rcases hJstruct (i + p) (i + q) hJs with h | h
    · left
      exact mod_pair_cancel' h
    · right
      exact mod_pair_cancel' h
  · intro p q hpq
    show s.a (i + p) (i + q) = Real.sqrt 8 ∧ s.b (i + p) (i + q) = cstab
    exact hJab (i + p) (i + q) hpq
  · -- the ncard bound via the bijection `y ↦ (y + k - i % k) % k`
    have himod2 : i % s.k < s.k := Nat.mod_lt i (by omega)
    show {x | x < s.k ∧ (2 * h0 < s.b (i + x) (i + x + 1) ∨
          2 < s.a (i + x) (i + x + 1))}.ncard + s.k ≤ 6
    have hcardT : {x | x < s.k ∧ (2 * h0 < s.b (i + x) (i + x + 1) ∨
          2 < s.a (i + x) (i + x + 1))}.ncard =
        {y | y < s.k ∧ (2 * h0 < s.b y (y + 1) ∨ 2 < s.a y (y + 1))}.ncard := by
      refine Set.ncard_congr (f := fun a (_ : a ∈ _) => (i + a) % s.k) ?_ ?_ ?_
      · rintro a ⟨ha, ha1 | ha2⟩
        · refine ⟨Nat.mod_lt (i + a) (by omega), Set.mem_setOf.mpr (Or.inl ?_)⟩
          rw [← periodic2_shift_pair hk0 hpb i a]
          exact ha1
        · refine ⟨Nat.mod_lt (i + a) (by omega), Set.mem_setOf.mpr (Or.inr ?_)⟩
          rw [← periodic2_shift_pair hk0 hpa i a]
          exact ha2
      · rintro a b ⟨ha, -⟩ ⟨hb, -⟩ hcon
        exact mod_pair_cancel ha hb hcon
      · rintro b ⟨hb, hb1 | hb2⟩
        · refine ⟨(b + s.k - i % s.k) % s.k, Set.mem_setOf.mpr
            ⟨Nat.mod_lt _ (by omega), Or.inl ?_⟩, psi_key hk0 hb⟩
          rw [periodic2_shift_pair hk0 hpb i ((b + s.k - i % s.k) % s.k),
            psi_key hk0 hb]
          exact hb1
        · refine ⟨(b + s.k - i % s.k) % s.k, Set.mem_setOf.mpr
            ⟨Nat.mod_lt _ (by omega), Or.inr ?_⟩, psi_key hk0 hb⟩
          rw [periodic2_shift_pair hk0 hpa i ((b + s.k - i % s.k) % s.k),
            psi_key hk0 hb]
          exact hb2

    show {x | x < s.k ∧ (2 * h0 < s.b (i + x) (i + x + 1) ∨
          2 < s.a (i + x) (i + x + 1))}.ncard + s.k ≤ 6
    rw [hcardT]
    exact hcard


/-- The double shift composes back to `s` (the `PRO_EQU_ID1` shape,
needed before `PRO_EQU_ID1` itself is stated). -/
private theorem propEqu_comp_eq {s : ScsV39} (hs : isScsV39 s) (i : ℕ) :
    scsPropEquV39 (scsPropEquV39 s i) (s.k - i % s.k) = s := by
  obtain ⟨-, h3, -, hplo, hphi, hpstr, -, hpa, hpam, hpbm, hpb, hpJ,
    -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  set m := s.k - i % s.k with hmdef
  have hφ : ∀ j, (i + (m + j)) % s.k = j % s.k := fun j => by
    rw [← add_assoc, add_comm i m, hmdef]
    exact TRANS_ID_INDEX (i := i) (j := j) hk0
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

/-- Forward direction of `PRO_EQU_IS_EAR`. -/
private theorem PRO_EQU_IS_EAR_FWD {s : ScsV39} (hs : isScsV39 s) (i : ℕ)
    (h : isEarV39 s) : isEarV39 (scsPropEquV39 s i) := by
  obtain ⟨hscs, hu, hk3, hd011, hbb0, i₀, hset, ha8, hbc0, hrest⟩ := h
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpb, hpJ, -, -, -, -, -, -, -, -, -⟩ := hs
  rw [hk3] at hpa hpb hpJ
  have hk0 : (0:ℕ) < 3 := by omega
  -- the residue of the transported witness and the source witness data
  have himem : i₀ ∈ {j | j < 3 ∧ s.J j (j + 1)} := by
    rw [hset]; exact rfl
  obtain ⟨hi₀3, hJi₀⟩ := himem
  set j₀ := (i₀ + 3 - i % 3) % 3 with hj₀def
  have hj₀3 : j₀ < 3 := Nat.mod_lt _ (by omega)
  have hkey : (i + j₀) % 3 = i₀ :=
    (TRANS_MOD_EQ (k := 3) (i := i) (x := i₀) (by omega)).trans
      (Nat.mod_eq_of_lt hi₀3)
  refine ⟨PROP_EQU_IS_SCS rfl hscs i,
    ⟨by funext j; exact congrFun hu.1 (i + j),
      by funext j; exact congrFun hu.2.1 (i + j),
      by funext j; exact congrFun hu.2.2.1 (i + j),
      by funext p q; exact congrFun (congrFun hu.2.2.2.1 (i + p)) (i + q),
      by funext p q; exact congrFun (congrFun hu.2.2.2.2 (i + p)) (i + q)⟩,
    hk3, hd011, fun p => hbb0 (i + p), ⟨j₀, ?_, ?_, ?_, ?_⟩⟩
  · -- the J-singleton transports along `j ↦ (i + j) % 3`
    refine Set.ext fun j => ?_
    show j < 3 ∧ s.J (i + j) (i + j + 1) ↔ j = j₀
    constructor
    · rintro ⟨hj3, hJ⟩
      have hJ' : s.J ((i + j) % 3) ((i + j) % 3 + 1) := by
        rw [← periodic2_shift_pair (k := 3) (by omega) hpJ i j]
        exact hJ
      have hmem : (i + j) % 3 ∈ {y | y < 3 ∧ s.J y (y + 1)} :=
        ⟨Nat.mod_lt _ hk0, hJ'⟩
      rw [hset, Set.mem_singleton_iff] at hmem
      exact mod_pair_cancel hj3 hj₀3 (by rw [hmem, hkey])
    · rintro hcon
      have hj3 : j < 3 := by rw [hcon]; exact hj₀3
      refine ⟨hj3, ?_⟩
      have hJ' : s.J ((i + j) % 3) ((i + j) % 3 + 1) := by
        rw [hcon, hkey]
        exact hJi₀
      rw [periodic2_shift_pair (k := 3) (by omega) hpJ i j]
      exact hJ'
  · -- the √8 edge
    show s.a (i + j₀) (i + j₀ + 1) = Real.sqrt 8
    rw [periodic2_shift_pair (k := 3) (by omega) hpa i j₀, hkey]
    exact ha8
  · -- the cstab edge
    show s.b (i + j₀) (i + j₀ + 1) = cstab
    rw [periodic2_shift_pair (k := 3) (by omega) hpb i j₀, hkey]
    exact hbc0
  · -- the remaining edges
    intro j hjj
    obtain ⟨hj3, hjne⟩ := hjj
    refine ⟨?_, ?_⟩
    · show s.a (i + j) (i + j + 1) = 2
      rw [periodic2_shift_pair (k := 3) (by omega) hpa i j]
      refine hrest ((i + j) % 3) ⟨Nat.mod_lt _ hk0, ?_⟩ |>.1
      intro hcon
      exact hjne (mod_pair_cancel hj3 hj₀3 (by rw [hkey]; exact hcon))
    · show s.b (i + j) (i + j + 1) = 2 * h0
      rw [periodic2_shift_pair (k := 3) (by omega) hpb i j]
      refine hrest ((i + j) % 3) ⟨Nat.mod_lt _ hk0, ?_⟩ |>.2
      intro hcon
      exact hjne (mod_pair_cancel hj3 hj₀3 (by rw [hkey]; exact hcon))

/-- HOL `PRO_EQU_IS_EAR` (YXIONXL.hl:978).  The J-singleton transports
along the 3-cycle bijection `j ↦ (i + j) % 3` and the reverse direction
re-uses the forward one through `PRO_EQU_ID1`. -/
theorem PRO_EQU_IS_EAR {s : ScsV39} (hs : isScsV39 s) (i : ℕ) :
    isEarV39 s ↔ isEarV39 (scsPropEquV39 s i) := by
  constructor
  · exact PRO_EQU_IS_EAR_FWD hs i
  · intro h
    have hfwd := PRO_EQU_IS_EAR_FWD (PROP_EQU_IS_SCS rfl hs i) (s.k - i % s.k) h
    rwa [propEqu_comp_eq hs i] at hfwd

/-- HOL `PRO_EQU_DSV_EQ` (YXIONXL.hl:1523).  The ear sign transports via
`PRO_EQU_IS_EAR`; the dsv sum re-indexes along `x ↦ (i + x) % k`
(`SUM_EQ_GENERAL` shape). -/
theorem PRO_EQU_DSV_EQ {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (i : ℕ) :
    dsvV39 (scsPropEquV39 s i) (fun x => vv (i + x)) = dsvV39 s vv := by
  unfold dsvV39
  rw [← PRO_EQU_IS_EAR hs i]
  obtain ⟨-, h3, -, -, -, -, -, -, -, -, -, hpJ, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  show s.d + 0.1 * (if isEarV39 s then 1 else -1) *
    setSum {x | x < s.k ∧ s.J (i + x) (i + x + 1)}
      (fun x => cstab - dist (vv (i + x)) (vv (i + x + 1))) =
    s.d + 0.1 * (if isEarV39 s then 1 else -1) *
    setSum {y | y < s.k ∧ s.J y (y + 1)}
      (fun y => cstab - dist (vv y) (vv (y + 1)))
  rw [setSum_dsv_propEq hk0 hpJ hBB.2.1 i]

/-- HOL `PRO_EQU_TAUSTAR_EQ` (YXIONXL.hl:1833).  The `k ≤ 3` branch uses
the cyclic invariance of `tau3`; the `k > 3` branch rewrites the three
vertex/dart/edge ranges by `TRANS_V`/`TRANS_E`/`TRANS_FF` (the HOL proof
routes through `SUM_AZIM_EQ_ANGLE_LE4` instead; the range-equality route
makes that detour unnecessary). -/
theorem PRO_EQU_TAUSTAR_EQ {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (i : ℕ) :
    taustarV39 (scsPropEquV39 s i) (fun j => vv (i + j)) = taustarV39 s vv := by
  have hkt : (scsPropEquV39 s i).k = s.k := rfl
  have h3 : 3 ≤ s.k := scs_k_le_3 hs
  have hk0 : s.k ≠ 0 := by omega
  have hper : Periodic vv s.k := hBB.2.1
  simp only [taustarV39]
  rw [PRO_EQU_DSV_EQ hs hBB i, hkt]
  by_cases hk3 : s.k ≤ 3
  · have hk33 : s.k = 3 := by omega
    rw [hk33] at hper
    rw [if_pos hk3, if_pos hk3]
    show tau3 (vv (i + 0)) (vv (i + 1)) (vv (i + 2)) - dsvV39 s vv =
      tau3 (vv 0) (vv 1) (vv 2) - dsvV39 s vv
    have hmod : i % 3 < 3 := Nat.mod_lt i (by omega)
    rcases Nat.lt_or_ge (i % 3) 1 with h0 | h1
    · have h0 : i % 3 = 0 := by omega
      have hv0 : vv (i + 0) = vv 0 := by
        rw [add_zero, ← periodicMod (k := 3) (by omega) hper i, h0]
      have hv1 : vv (i + 1) = vv 1 := by
        rw [← periodicMod (k := 3) (by omega) hper (i + 1),
          show (i + 1) % 3 = 1 from by omega]
      have hv2 : vv (i + 2) = vv 2 := by
        rw [← periodicMod (k := 3) (by omega) hper (i + 2),
          show (i + 2) % 3 = 2 from by omega]
      rw [hv0, hv1, hv2]
    · rcases Nat.lt_or_ge (i % 3) 2 with h1' | h2'
      · have h1'' : i % 3 = 1 := by omega
        have hv0 : vv (i + 0) = vv 1 := by
          rw [add_zero, ← periodicMod (k := 3) (by omega) hper i, h1'']
        have hv1 : vv (i + 1) = vv 2 := by
          rw [← periodicMod (k := 3) (by omega) hper (i + 1),
            show (i + 1) % 3 = 2 from by omega]
        have hv2 : vv (i + 2) = vv 0 := by
          rw [← periodicMod (k := 3) (by omega) hper (i + 2),
            show (i + 2) % 3 = 0 from by omega]
        rw [hv0, hv1, hv2, tau3_cycle, tau3_cycle]
      · have h2'' : i % 3 = 2 := by omega
        have hv0 : vv (i + 0) = vv 2 := by
          rw [add_zero, ← periodicMod (k := 3) (by omega) hper i, h2'']
        have hv1 : vv (i + 1) = vv 0 := by
          rw [← periodicMod (k := 3) (by omega) hper (i + 1),
            show (i + 1) % 3 = 0 from by omega]
        have hv2 : vv (i + 2) = vv 1 := by
          rw [← periodicMod (k := 3) (by omega) hper (i + 2),
            show (i + 2) % 3 = 1 from by omega]
        rw [hv0, hv1, hv2, tau3_cycle]
  · rw [if_neg hk3, if_neg hk3]
    show tauFun (Set.range fun x => vv (i + x))
        (Set.range fun x => ({vv (i + x), vv (i + x + 1)} : Set V3))
        (Set.range fun x => (vv (i + x), vv (i + x + 1))) - dsvV39 s vv =
      tauFun (Set.range vv) (Set.range fun x => ({vv x, vv (x + 1)} : Set V3))
        (Set.range fun x => (vv x, vv (x + 1))) - dsvV39 s vv
    rw [TRANS_V hs hBB i, TRANS_E hs hBB i, TRANS_FF hs hBB i]

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

/-- HOL `TRANS_SCS_BBPRIME` (YXIONXL.hl:2275).  The taustar clause goes
through `PRO_EQU_TAUSTAR_EQ` (forward and, via `PRO_EQU_ID1`, backward). -/
theorem TRANS_SCS_BBPRIME {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hbp : vv ∈ BBprimeV39 s) (i : ℕ) :
    (fun x => vv (i + x)) ∈ BBprimeV39 (scsPropEquV39 s i) := by
  have hse : isScsV39 (scsPropEquV39 s i) := PROP_EQU_IS_SCS rfl hs i
  have hta : taustarV39 (scsPropEquV39 s i) (fun x => vv (i + x)) = taustarV39 s vv :=
    PRO_EQU_TAUSTAR_EQ hs hbp.1 i
  have hEq : scsPropEquV39 (scsPropEquV39 s i) (s.k - i % s.k) = s :=
    (PRO_EQU_ID1 rfl hs i).symm
  have htransport : ∀ ww : ℕ → V3, BBsV39 (scsPropEquV39 s i) ww →
      taustarV39 s (fun x => ww (s.k - i % s.k + x)) =
        taustarV39 (scsPropEquV39 s i) ww := by
    intro ww hw
    have h := PRO_EQU_TAUSTAR_EQ hse hw (s.k - i % s.k)
    rwa [hEq] at h
  refine ⟨BB_TRANS_SUBSET_BB hs hbp.1 i, ?_, ?_⟩
  · intro ww hw
    have hwBack : BBsV39 s (fun x => ww (s.k - i % s.k + x)) :=
      PROP_EQU_EQ_BB rfl hs i hse hw
    rw [hta, ← htransport ww hw]
    exact hbp.2.1 _ hwBack
  · rw [hta]
    exact hbp.2.2

/-- HOL `TRANS_BBINDEX_ID` (YXIONXL.hl:2299).  The ncard bijection
`y ↦ (y + k - i % k) % k` on `{0..k-1}` (`Set.InjOn.ncard_image` replaces
HOL `CARD_IMAGE_INJ_EQ`). -/
theorem TRANS_BBINDEX_ID {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) {vv : ℕ → V3} (hBB : BBsV39 s vv) :
    BBindexV39 (scsPropEquV39 s i) (fun x => vv (i + x)) = BBindexV39 s vv := by
  subst hk
  obtain ⟨-, h3, -, -, -, -, -, hpa, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hs
  have hk0 : s.k ≠ 0 := by omega
  have hper : Periodic vv s.k := hBB.2.1
  show {x | x < s.k ∧ (scsPropEquV39 s i).a x (x + 1) =
      dist (vv (i + x)) (vv (i + x + 1))}.ncard
    = {y | y < s.k ∧ s.a y (y + 1) = dist (vv y) (vv (y + 1))}.ncard
  refine Set.ncard_congr (f := fun a (_ : a ∈ _) => (i + a) % s.k) ?_ ?_ ?_
  · rintro y ⟨hy, hay⟩
    refine ⟨Nat.mod_lt (i + y) (by omega), Set.mem_setOf.mpr ?_⟩
    have e1 : (scsPropEquV39 s i).a y (y + 1)
        = s.a ((i + y) % s.k) (((i + y) % s.k) + 1) := by
      show s.a (i + y) (i + y + 1) = s.a ((i + y) % s.k) ((i + y) % s.k + 1)
      exact periodic2_shift_pair hk0 hpa i y
    have e2 : dist (vv (i + y)) (vv (i + y + 1))
        = dist (vv ((i + y) % s.k)) (vv (((i + y) % s.k) + 1)) :=
      dist_shift_pair hk0 hper i y
    exact e1.symm.trans (hay.trans e2)

  · rintro a b ⟨ha, -⟩ ⟨hb, -⟩ hcon
    exact mod_pair_cancel ha hb hcon
  · rintro b ⟨hb, hb2⟩
    have hEq : (scsPropEquV39 s i).a ((b + s.k - i % s.k) % s.k)
        (((b + s.k - i % s.k) % s.k) + 1)
        = dist (vv (i + (b + s.k - i % s.k) % s.k))
            (vv (i + (b + s.k - i % s.k) % s.k + 1)) := by
      show s.a (i + (b + s.k - i % s.k) % s.k)
          (i + (b + s.k - i % s.k) % s.k + 1) =
        dist (vv (i + (b + s.k - i % s.k) % s.k))
          (vv (i + (b + s.k - i % s.k) % s.k + 1))
      rw [periodic2_shift_pair hk0 hpa i ((b + s.k - i % s.k) % s.k),
        psi_key hk0 hb, dist_shift_pair hk0 hper i ((b + s.k - i % s.k) % s.k),
        psi_key hk0 hb]
      exact hb2
    exact ⟨(b + s.k - i % s.k) % s.k, Set.mem_setOf.mpr
      ⟨Nat.mod_lt _ (by omega), hEq⟩, psi_key hk0 hb⟩

/-- HOL `PROP_EQU_EQ_BBPRIME` (YXIONXL.hl:2487).  The minimality clause
transports through `BB_TRANS_SUBSET_BB` and the two taustar transports
(`PRO_EQU_TAUSTAR_EQ` at `(s, i)` and at `(t, k - i % k)` via
`PRO_EQU_ID1`). -/
theorem PROP_EQU_EQ_BBPRIME {s : ScsV39} {k : ℕ} (hk : s.k = k)
    (hs : isScsV39 s) (i : ℕ) {vv : ℕ → V3}
    (hbp : vv ∈ BBprimeV39 (scsPropEquV39 s i)) :
    (fun x => vv (k - i % k + x)) ∈ BBprimeV39 s := by
  subst hk
  have hse : isScsV39 (scsPropEquV39 s i) := PROP_EQU_IS_SCS rfl hs i
  have hEq : scsPropEquV39 (scsPropEquV39 s i) (s.k - i % s.k) = s :=
    (PRO_EQU_ID1 rfl hs i).symm
  have htransport : ∀ ww : ℕ → V3, BBsV39 (scsPropEquV39 s i) ww →
      taustarV39 s (fun x => ww (s.k - i % s.k + x)) =
        taustarV39 (scsPropEquV39 s i) ww := by
    intro ww hw
    have h := PRO_EQU_TAUSTAR_EQ hse hw (s.k - i % s.k)
    rwa [hEq] at h
  refine ⟨PROP_EQU_EQ_BB rfl hs i hse hbp.1, ?_, ?_⟩
  · intro ww hwW
    have hw' : BBsV39 (scsPropEquV39 s i) (fun x => ww (i + x)) :=
      BB_TRANS_SUBSET_BB hs hwW i
    have hstep := hbp.2.1 _ hw'
    rw [← htransport vv hbp.1, PRO_EQU_TAUSTAR_EQ hs hwW i] at hstep
    exact hstep
  · rw [htransport vv hbp.1]
    exact hbp.2.2

/-- HOL `TRANS_IMAGE_BBINDEX_EQ` (YXIONXL.hl:2497): the two BBindex
images agree, via `TRANS_SCS_BBPRIME` / `PROP_EQU_EQ_BBPRIME` and the
index transport in both directions. -/
theorem TRANS_IMAGE_BBINDEX_EQ {s : ScsV39} {k : ℕ} (hk : s.k = k)
    (hs : isScsV39 s) (i : ℕ) :
    BBindexV39 (scsPropEquV39 s i) '' BBprimeV39 (scsPropEquV39 s i)
      = BBindexV39 s '' BBprimeV39 s := by
  subst hk
  have hse : isScsV39 (scsPropEquV39 s i) := PROP_EQU_IS_SCS rfl hs i
  have hEq : scsPropEquV39 (scsPropEquV39 s i) (s.k - i % s.k) = s :=
    (PRO_EQU_ID1 rfl hs i).symm
  refine Set.ext fun n => ?_
  constructor
  · rintro ⟨vv, hvv, rfl⟩
    have h1 := TRANS_BBINDEX_ID (s := scsPropEquV39 s i) (k := s.k) rfl hse
      (s.k - i % s.k) (vv := vv) hvv.1
    rw [hEq] at h1
    exact ⟨fun x => vv (s.k - i % s.k + x), PROP_EQU_EQ_BBPRIME rfl hs i hvv,
      h1⟩
  · rintro ⟨vv, hvv, rfl⟩
    exact ⟨fun x => vv (i + x), TRANS_SCS_BBPRIME hs hvv i,
      TRANS_BBINDEX_ID rfl hs i hvv.1⟩

/-- HOL `TRANS_BBINDEX_MIN_EQ` (YXIONXL.hl:2531): the two `minNum` sets
agree by `TRANS_IMAGE_BBINDEX_EQ`. -/
theorem TRANS_BBINDEX_MIN_EQ {s : ScsV39} {k : ℕ} (hk : s.k = k)
    (hs : isScsV39 s) (i : ℕ) {vv : ℕ → V3} (hBB : BBsV39 s vv) :
    BBindexMinV39 (scsPropEquV39 s i) = BBindexMinV39 s :=
  congrArg minNum (TRANS_IMAGE_BBINDEX_EQ rfl hs i)

/-- HOL `TRANS_BBPRIME2_SUBSET` (YXIONXL.hl:2542): the BBprime2 transport,
from `TRANS_SCS_BBPRIME` + `TRANS_BBINDEX_ID` + `TRANS_BBINDEX_MIN_EQ`. -/
theorem TRANS_BBPRIME2_SUBSET {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hbp2 : vv ∈ BBprime2V39 s) (i : ℕ) :
    (fun x => vv (i + x)) ∈ BBprime2V39 (scsPropEquV39 s i) := by
  refine ⟨TRANS_SCS_BBPRIME hs hbp2.1 i, ?_⟩
  show BBindexV39 (scsPropEquV39 s i) (fun x => vv (i + x)) =
    BBindexMinV39 (scsPropEquV39 s i)
  rw [TRANS_BBINDEX_ID (vv := vv) rfl hs i hbp2.1.1]
  have h2 : BBindexV39 s vv = BBindexMinV39 (scsPropEquV39 s i) := by
    rw [hbp2.2,
      (TRANS_BBINDEX_MIN_EQ (hBB := hbp2.1.1) rfl hs i).symm]
  exact h2

/-- HOL `TRANS_MMS_SUBSET` (YXIONXL.hl:2559): the MM clauses transport
pointwise along the shift (the str clause needs only `add_assoc`). -/
theorem TRANS_MMS_SUBSET {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hm : vv ∈ MMsV39 s) (i : ℕ) :
    (fun x => vv (i + x)) ∈ MMsV39 (scsPropEquV39 s i) := by
  obtain ⟨hbb2, hstr, hlo, hhi, ham, hbm⟩ := hm
  refine ⟨TRANS_BBPRIME2_SUBSET hs hbb2 i, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    show azim 0 (vv (i + j)) (vv (i + (j + 1))) (vv (i + (j + (s.k - 1)))) =
      Real.pi
    have h := hstr (i + j) hj
    simpa only [add_assoc] using h
  · intro j hj
    show norm (vv (i + j)) = 2
    exact hlo (i + j) hj
  · intro j hj
    show norm (vv (i + j)) = 2 * h0
    exact hhi (i + j) hj
  · intro p q
    show s.am (i + p) (i + q) ≤ dist (vv (i + p)) (vv (i + q))
    exact ham (i + p) (i + q)
  · intro p q
    show dist (vv (i + p)) (vv (i + q)) ≤ s.bm (i + p) (i + q)
    exact hbm (i + p) (i + q)

/-- HOL `YXIONXL3` (YXIONXL.hl:2573): the cyclic re-indexing is an arrow,
from `PROP_EQU_IS_SCS` + `TRANS_MMS_SUBSET`. -/
theorem YXIONXL3 (s : ScsV39) (i : ℕ) (hs : isScsV39 s) :
    scsArrowV39 {s} {scsPropEquV39 s i} := by
  refine ⟨fun u hu => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hu
    rw [hu]
    exact PROP_EQU_IS_SCS rfl hs i
  · by_cases hM : MMsV39 s = ∅
    · refine Or.inl ?_
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact hM
    · obtain ⟨vv, hvv⟩ := (Set.nonempty_iff_ne_empty (s := MMsV39 s)).mpr hM
      refine Or.inr ⟨scsPropEquV39 s i, Set.mem_singleton _, ?_⟩
      have hvv' : (MMsV39 (scsPropEquV39 s i)).Nonempty :=
        ⟨fun x => vv (i + x), TRANS_MMS_SUBSET hs hvv i⟩
      exact hvv'.ne_empty
