/-
LocalAuto30 — the ninth micro-file bundle of the appendix-to-Local-Fan
wave (skeleton-first pass), porting `scripts/local/UAGHHBM.hl`
(4106 ln, 0 defs + 47 thms): the subdivision (FORK) machinery for the
appendix — `psort` periodicity/case kit, override monotonicity,
`BBs`/`BBprime`/`BBprime2`/`MMs` transfer through the two restrictions
`restriction_cs1/2_v39`, the `BBindex`/`BBindex_min` comparison kit
(cs1-branch `dist <= c`, cs2-branch `c < dist`, and the `c = am`
edge-branch), ending in the master arrow `UAGHHBM`
(`scs_arrow_v39 {s} (set_of_list (subdiv_v39 s i j c))`).

Encoding:
- HOL `real^3` <-> `V3` (Kepler.Geom); `dist(ww i, ww j)` <->
  `dist (ww i) (ww j)`; HOL `c < norm(ww i - ww j)` <->
  `c < dist (ww i) (ww j)` (same statement via `dist_eq_norm`).
- All toolkit defs live in `Kepler.Text.LocalAuto1` (`ScsV39`,
  `isScsV39`, `Periodic(2)`, `psort`, `override`, `BBsV39`,
  `BBprimeV39`, `BBprime2V39`, `BBindexV39`, `BBindexMinV39`,
  `MMsV39`, `minNum`, `restrictionCs1V39`, `restrictionCs2V39`,
  `subdivV39`, `dsvV39`, `taustarV39`, `isEarV39`, `scsArrowV39`);
  this file only adds `_p30` substrate + statements.
- Accessor projection: `scs_k_v39 s` <-> `s.k`, `scs_a_v39 s i j` <->
  `s.a i j` (also `am`, `bm`, `b`, `J`); `IMAGE f s` <-> `f '' s`;
  `set_of_list (subdiv_v39 s i j c)` <-> `{t | t ∈ subdivV39 s i j c}`;
  `SUC` <-> `(· + 1)`; `min_num` <-> `minNum`.
- HOL `Misc_defs_and_lemmas.min_least` is re-derived here from the
  epsilon definition of `minNum` (`least_exists_p30` +
  `minNum_mem_p30`/`minNum_le_p30`).
- Same-wave workers own LocalAuto28/29/31-33; nothing is imported from
  them — every shared input is an in-file `_p30` copy.
- No `native_decide`. The 40 proved items use mod/periodicity folding,
  psort case analysis, order arithmetic and set-cardinality bookkeeping
  (`Set.ncard_le_ncard`); the `c = am` edge-branch index-counting
  cancellations and the master `UAGHHBM` fork analysis remain `sorry`
  (each with a NEEDS marker).

FILE MAP
  Section 0 (`_p30` substrate): `periodic_mod_p30`, `periodic2_mod_p30`,
    `per_eq_p30`, `per2_eq_p30`, `least_exists_p30`, `minNum_mem_p30`,
    `minNum_le_p30`.
  Transfer helpers (Sections B/C/G): `comp_psort_p30`, `a_psort_p30`,
    `b_psort_p30`, `dist_psort_p30`, `not_isEar_p30`,
    `BBs_s_to_restrictionCs2_p30`, `BBs_restrictionCs2_to_s_p30`,
    `BBs_s_to_restrictionCs1_p30`, `BBs_restrictionCs1_to_s_p30`,
    `BBs_s_to_restrictionCs2_eq_p30`.

  Status: 40 of the 47 HOL theorems are fully proved; the 6 `c = am`
  edge-branch index-counting statements (Sections G tail) and the master
  `UAGHHBM_p30` carry `sorry` with NEEDS markers.

  Section A (UAGHHBM.hl:84-146): `PERIODIC_PSORT_p30` (proved),
    `CASE_PSORT_p30` (proved), `C_LE_2_IS_SCS_p30` (proved),
    `C_LT_2_IS_SCS_p30` (proved).
  Section B (150-219): `A_LE_A_OVERRIDE_p30`, `B_OVERRIDE_LE_B_p30`.
  Section C (223-494): `BB_EQ_UNION_BB_SUBDIVISION_p30`,
    `SUBDIVISION_IS_NOT_EAR_p30`, `SUBDIVISION_CS1_DSV_EQ_p30`,
    `SUBDIVISION_CS1_TAUSTAR_EQ_p30`,
    `BBPRIME_SUBSET_SUBDIVISION_UNION_p30`,
    `BBPRIME_SUBSET_BBPRIME_SUBDIVISION_UNION_p30`.
  Section D (499-1065, cs2/`c < dist`): `BBINDEX_EQ_SUBDIVISION_p30`,
    `CONDITION_BBPRIME_SUBSET_BBPRIME_SUBDIVISION_p30`,
    `BBPRIME_SUBDIVISION2_SUBSET_BBPRIME_p30`,
    `IN_BBPRIME_SUBDIVISION_p30`, `MIN_NUM_SUBSET_p30`,
    `BBINDEX_MIN_S_LE_SUBDIVISION2_p30`,
    `BBINDEX_BBPRIME_LE_SUBDIVISION2_p30`.
  Section E (1068-1342): `MIN_NUM_LE_IMAGE_p30`,
    `CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION2_p30`,
    `BBindex_min_LE_SUBDIVISION2_p30`,
    `BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION_p30`,
    `MM_IS_NOT_2EMPTY_SUBDIVISION_p30`,
    `MM_IS_NOT_1EMPTY_SUBDIVISION_p30`.
  Section F (1350-1815, cs1/`dist <= c` twins): `BBINDEX_EQ_SUBDIVISION1_p30`,
    `CONDITION_BBPRIME_SUBSET_BBPRIME_SUBDIVISION1_p30`,
    `IN_BBPRIME_SUBDIVISION1_p30`,
    `BBPRIME_SUBDIVISION2_SUBSET_BBPRIME1_p30`,
    `BBINDEX_MIN_S_LE_SUBDIVISION1_p30`,
    `BBINDEX_BBPRIME_LE_SUBDIVISION1_p30`,
    `CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION1_p30`,
    `BBindex_min_LE_SUBDIVISION1_p30`,
    `BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION1_p30`,
    `MM_IS_NOT_2EMPTY_SUBDIVISION1_p30`,
    `MM_IS_NOT_1EMPTY_SUBDIVISION1_p30`.
  Section G (1820-2496, `c = am` edge-branch):
    `BBINDEX_EQ_SUBDIVISION_C_EQ_AM_p30`,
    `CONDITION_BBPRIME_SUBSET_BBPRIME_SUBDIVISION_C_EQ_AM_p30`,
    `BBPRIME_SUBDIVISION2_SUBSET_BBPRIME_C_EQ_AM_p30`,
    `IN_BBPRIME_SUBDIVISION_C_EQ_AM_p30`,
    `BBINDEX_MIN_S_LE_SUBDIVISION2_C_EQ_AM_p30`,
    `BBINDEX_BBPRIME_LE_SUBDIVISION2_C_EQ_AM_p30`,
    `CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION2_C_EQ_AM_p30`,
    `BBindex_min_LE_SUBDIVISION2_C_EQ_AM_p30`,
    `BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION_C_EQ_AM_p30`,
    `MM_IS_NOT_2EMPTY_SUBDIVISION_C_EQ_AM_p30`.
  Section H (2501-4095): `UAGHHBM_p30`.

  DISCHARGES: every `sorry` carries a NEEDS note naming the blocking
  HOL input.
-/

import Kepler.Text.LocalAuto1
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p30` substrate -/

/-- Mod-periodicity folding for the 1D `Periodic` components
(universe-polymorphic twin of LocalAuto27 `periodic_mod_p27`). -/
theorem periodic_mod_p30 {α : Sort u} {f : ℕ → α} {n : ℕ} (hper : Periodic f n)
    (i : ℕ) : f i = f (i % n) := by
  have key : ∀ m r, f (n * m + r) = f r := by
    intro m
    induction m with
    | zero => intro r; simp
    | succ m ih =>
        intro r
        have hE : n * (m + 1) + r = n * m + r + n := by ring
        rw [hE, hper, ih]
  have hI : i = n * (i / n) + i % n := (Nat.div_add_mod i n).symm
  nth_rewrite 1 [hI]
  exact key (i / n) (i % n)

/-- Mod-periodicity folding for the `Periodic2` (matrix) components. -/
theorem periodic2_mod_p30 {α : Sort u} {f : ℕ → ℕ → α} {n : ℕ}
    (hper : Periodic2 f n) (i j : ℕ) : f i j = f (i % n) (j % n) := by
  have key1 : ∀ m r s, f (n * m + r) s = f r s := by
    intro m
    induction m with
    | zero => intro r s; simp
    | succ m ih =>
        intro r s
        have hE : n * (m + 1) + r = n * m + r + n := by ring
        rw [hE, (hper (n * m + r) s).1, ih]
  have key2 : ∀ m r s, f s (n * m + r) = f s r := by
    intro m
    induction m with
    | zero => intro r s; simp
    | succ m ih =>
        intro r s
        have hE : n * (m + 1) + r = n * m + r + n := by ring
        rw [hE, (hper s (n * m + r)).2, ih]
  have hI : i = n * (i / n) + i % n := (Nat.div_add_mod i n).symm
  have hJ : j = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
  nth_rewrite 1 [hI]
  nth_rewrite 1 [hJ]
  rw [key1 (i / n) (i % n) (n * (j / n) + j % n), key2 (j / n) (j % n) (i % n)]

/-- Residue-equal indices are indistinguishable for a `Periodic` family. -/
theorem per_eq_p30 {α : Sort u} {f : ℕ → α} {k : ℕ} (hper : Periodic f k)
    {i x : ℕ} (h : i % k = x % k) : f i = f x := by
  rw [periodic_mod_p30 hper i, periodic_mod_p30 hper x, h]

/-- Residue-equal index pairs are indistinguishable for a `Periodic2`
family. -/
theorem per2_eq_p30 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ} (hper : Periodic2 f k)
    {i j x y : ℕ} (hi : i % k = x % k) (hj : j % k = y % k) : f i j = f x y := by
  rw [periodic2_mod_p30 hper i j, periodic2_mod_p30 hper x y, hi, hj]

/-- A nonempty set of naturals has a least element (HOL
`Misc_defs_and_lemmas.min_least` existence half). -/
theorem least_exists_p30 {S : Set ℕ} (hne : S.Nonempty) :
    ∃ n, n ∈ S ∧ ∀ m ∈ S, n ≤ m := by
  obtain ⟨x, hx⟩ := hne
  have hp : ∃ n, n ∈ S := ⟨x, hx⟩
  classical
  exact ⟨Nat.find hp, Nat.find_spec hp, fun m hm => Nat.find_min' hp hm⟩

/-- `minNum S` lands in `S` when `S` is nonempty. -/
theorem minNum_mem_p30 {S : Set ℕ} (hne : S.Nonempty) : minNum S ∈ S :=
  (Classical.epsilon_spec (p := fun n => n ∈ S ∧ ∀ m ∈ S, n ≤ m)
    (least_exists_p30 hne)).1

/-- `minNum S` is a lower bound for `S` when `S` is nonempty. -/
theorem minNum_le_p30 {S : Set ℕ} (hne : S.Nonempty) {m : ℕ} (hm : m ∈ S) :
    minNum S ≤ m :=
  (Classical.epsilon_spec (p := fun n => n ∈ S ∧ ∀ m ∈ S, n ≤ m)
    (least_exists_p30 hne)).2 m hm

/-! ## Section A: psort kit (UAGHHBM.hl:84-146) -/

/-- HOL `PERIODIC_PSORT` (UAGHHBM.hl:84). -/
theorem PERIODIC_PSORT_p30 {k : ℕ} (hk : k ≠ 0) (i j : ℕ) :
    psort k (i + k, j) = psort k (i, j) ∧ psort k (i, j + k) = psort k (i, j) := by
  have h1 : (i + k) % k = i % k := Nat.add_mod_right i k
  have h2 : (j + k) % k = j % k := Nat.add_mod_right j k
  exact ⟨by simp only [psort, h1], by simp only [psort, h2]⟩

/-- HOL `CASE_PSORT` (UAGHHBM.hl:92). -/
theorem CASE_PSORT_p30 {k : ℕ} {i j i' j' : ℕ}
    (h : psort k (i, j) = psort k (i', j')) :
    (i % k = i' % k ∧ j % k = j' % k) ∨ (i % k = j' % k ∧ j % k = i' % k) := by
  unfold psort at h
  by_cases h1 : i % k ≤ j % k
  · by_cases h2 : i' % k ≤ j' % k
    · rw [if_pos h1, if_pos h2] at h
      exact Or.inl (by simpa [Prod.mk.injEq] using h)
    · rw [if_pos h1, if_neg h2] at h
      exact Or.inr (by simpa [Prod.mk.injEq] using h)
  · by_cases h2 : i' % k ≤ j' % k
    · rw [if_neg h1, if_pos h2] at h
      have h' : j % k = i' % k ∧ i % k = j' % k := by
        simpa [Prod.mk.injEq] using h
      exact Or.inr ⟨h'.2, h'.1⟩
    · rw [if_neg h1, if_neg h2] at h
      have h' : j % k = j' % k ∧ i % k = i' % k := by
        simpa [Prod.mk.injEq] using h
      exact Or.inl ⟨h'.2, h'.1⟩

/-- HOL `C_LE_2_IS_SCS` (UAGHHBM.hl:102). -/
theorem C_LE_2_IS_SCS_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (hs : isScsV39 s)
    (hij : i % s.k ≠ j % s.k) (h : s.a i j ≤ c) : 2 ≤ c := by
  obtain ⟨_, hk1, _, _, _, _, _, hpa, _, _, _, _, _, _, _, hdiag, _, _, _, _, _⟩ := hs
  have hkpos : 0 < s.k := by omega
  calc 2 ≤ s.a (i % s.k) (j % s.k) :=
      hdiag (i % s.k) (j % s.k) ⟨Nat.mod_lt i hkpos, Nat.mod_lt j hkpos, hij⟩
    _ = s.a i j := (periodic2_mod_p30 hpa i j).symm
    _ ≤ c := h

/-- HOL `C_LT_2_IS_SCS` (UAGHHBM.hl:126). -/
theorem C_LT_2_IS_SCS_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (hs : isScsV39 s)
    (hij : i % s.k ≠ j % s.k) (h : s.a i j < c) : 2 < c := by
  obtain ⟨_, hk1, _, _, _, _, _, hpa, _, _, _, _, _, _, _, hdiag, _, _, _, _, _⟩ := hs
  have hkpos : 0 < s.k := by omega
  calc 2 ≤ s.a (i % s.k) (j % s.k) :=
      hdiag (i % s.k) (j % s.k) ⟨Nat.mod_lt i hkpos, Nat.mod_lt j hkpos, hij⟩
    _ = s.a i j := (periodic2_mod_p30 hpa i j).symm
    _ < c := h

/-! ## Section B: override monotonicity (UAGHHBM.hl:150-219) -/

/-- psort-equal cells are indistinguishable for any symmetric `Periodic2`
real-valued component. -/
theorem comp_psort_p30 {k : ℕ} {f : ℕ → ℕ → ℝ} (hper : Periodic2 f k)
    (hsym : ∀ i j : ℕ, f i j = f j i) {i j x y : ℕ}
    (h : psort k (i, j) = psort k (x, y)) : f i j = f x y := by
  rw [periodic2_mod_p30 hper i j, periodic2_mod_p30 hper x y]
  rcases CASE_PSORT_p30 h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb]
  · rw [ha, hb, hsym _ _]

/-- psort-equal cells are indistinguishable for `s.a`. -/
theorem a_psort_p30 (s : ScsV39) (hs : isScsV39 s) {i j x y : ℕ}
    (h : psort s.k (i, j) = psort s.k (x, y)) : s.a i j = s.a x y := by
  obtain ⟨_, _, _, _, _, _, _, hpa, _, _, _, _, hsym, _, _, _, _, _, _, _, _⟩ := hs
  exact comp_psort_p30 hpa (fun i j => (hsym i j).1) h

/-- psort-equal cells are indistinguishable for `s.b`. -/
theorem b_psort_p30 (s : ScsV39) (hs : isScsV39 s) {i j x y : ℕ}
    (h : psort s.k (i, j) = psort s.k (x, y)) : s.b i j = s.b x y := by
  obtain ⟨_, _, _, _, _, _, _, hpa, _, _, hpb, _, hsym, _, _, _, _, _, _, _, _⟩ := hs
  exact comp_psort_p30 hpb (fun i j => (hsym i j).2.2.2.1) h

/-- HOL `A_LE_A_OVERRIDE` (UAGHHBM.hl:150). -/
theorem A_LE_A_OVERRIDE_p30 (s : ScsV39) (i j i' j' : ℕ) (c : ℝ) (hs : isScsV39 s)
    (h : s.a i j ≤ c) : s.a i' j' ≤ override s.a s.k (i, j) c i' j' := by
  unfold override
  by_cases hp : psort s.k (i, j) = psort s.k (i', j')
  · rw [if_pos hp]
    rw [(a_psort_p30 s hs hp).symm]
    exact h
  · rw [if_neg hp]

/-- HOL `B_OVERRIDE_LE_B` (UAGHHBM.hl:189). -/
theorem B_OVERRIDE_LE_B_p30 (s : ScsV39) (i j i' j' : ℕ) (c : ℝ) (hs : isScsV39 s)
    (h : c ≤ s.b i j) : override s.b s.k (i, j) c i' j' ≤ s.b i' j' := by
  unfold override
  by_cases hp : psort s.k (i, j) = psort s.k (i', j')
  · rw [if_pos hp]
    rw [(b_psort_p30 s hs hp).symm]
    exact h
  · rw [if_neg hp]

/-! ## Section C: subdivision basics (UAGHHBM.hl:223-494) -/

/-- A system with `3 < scs_k_v39` is not an ear. -/
theorem not_isEar_p30 (s : ScsV39) (hk : 3 < s.k) : ¬isEarV39 s := by
  intro h
  have h3 : s.k = 3 := h.2.2.1
  omega

/-- HOL `SUBDIVISION_IS_NOT_EAR` (UAGHHBM.hl:395). -/
theorem SUBDIVISION_IS_NOT_EAR_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (hk : 3 < s.k) :
    ¬isEarV39 s ∧ ¬isEarV39 (restrictionCs1V39 s i j c) ∧
      ¬isEarV39 (restrictionCs2V39 s i j c) := by
  refine ⟨not_isEar_p30 s hk, ?_, ?_⟩
  · intro h
    have hk1 : (restrictionCs1V39 s i j c).k = s.k := rfl
    have h3 : s.k = 3 := h.2.2.1
    omega
  · intro h
    have hk2 : (restrictionCs2V39 s i j c).k = s.k := rfl
    have h3 : s.k = 3 := h.2.2.1
    omega

/-- HOL `SUBDIVISION_CS1_DSV_EQ` (UAGHHBM.hl:405). -/
theorem SUBDIVISION_CS1_DSV_EQ_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (ww : ℕ → V3)
    (hk : 3 < s.k) :
    dsvV39 (restrictionCs1V39 s i j c) ww = dsvV39 s ww ∧
      dsvV39 (restrictionCs2V39 s i j c) ww = dsvV39 s ww := by
  have h1 := not_isEar_p30 s hk
  have h2 : ¬isEarV39 (restrictionCs1V39 s i j c) :=
    fun hh => (SUBDIVISION_IS_NOT_EAR_p30 s i j c hk).2.1 hh
  have h3 : ¬isEarV39 (restrictionCs2V39 s i j c) :=
    fun hh => (SUBDIVISION_IS_NOT_EAR_p30 s i j c hk).2.2 hh
  unfold dsvV39
  rw [if_neg h2, if_neg h1, if_neg h3]
  exact ⟨rfl, rfl⟩

/-- HOL `SUBDIVISION_CS1_TAUSTAR_EQ` (UAGHHBM.hl:417). -/
theorem SUBDIVISION_CS1_TAUSTAR_EQ_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (ww : ℕ → V3)
    (hk : 3 < s.k) :
    taustarV39 (restrictionCs1V39 s i j c) ww = taustarV39 s ww ∧
      taustarV39 (restrictionCs2V39 s i j c) ww = taustarV39 s ww := by
  have hd := SUBDIVISION_CS1_DSV_EQ_p30 s i j c ww hk
  have hk1 : (restrictionCs1V39 s i j c).k = s.k := rfl
  have hk2 : (restrictionCs2V39 s i j c).k = s.k := rfl
  have h3 : ¬((restrictionCs1V39 s i j c).k ≤ 3) := by omega
  have h4 : ¬((restrictionCs2V39 s i j c).k ≤ 3) := by omega
  have h5 : ¬(s.k ≤ 3) := by omega
  unfold taustarV39
  rw [if_neg h3, if_neg h4, if_neg h5]
  exact ⟨by rw [hd.1], by rw [hd.2]⟩

/-- psort-equal cells carry equal distances for a `Periodic` point family. -/
theorem dist_psort_p30 {ww : ℕ → V3} {k : ℕ} (hper : Periodic ww k)
    {i j x y : ℕ} (h : psort k (i, j) = psort k (x, y)) :
    dist (ww i) (ww j) = dist (ww x) (ww y) := by
  rw [periodic_mod_p30 hper i, periodic_mod_p30 hper j, periodic_mod_p30 hper x,
    periodic_mod_p30 hper y]
  rcases CASE_PSORT_p30 h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb]
  · rw [ha, hb, dist_comm]

/-- `BBs` realisations of `s` with `c < dist (ww i) (ww j)` are `BBs`
realisations of the cs2-restriction. -/
theorem BBs_s_to_restrictionCs2_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (ww : ℕ → V3)
    (hs : isScsV39 s) (hbb : BBsV39 s ww) (h1 : s.a i j ≤ c)
    (hlt : c < dist (ww i) (ww j)) : BBsV39 (restrictionCs2V39 s i j c) ww := by
  obtain ⟨hann, hper, hdist, hfan⟩ := hbb
  refine ⟨hann, hper, ?_, hfan⟩
  intro x y
  have hab := hdist x y
  refine ⟨?_, hab.2⟩
  show override s.a s.k (i, j) c x y ≤ dist (ww x) (ww y)
  unfold override
  by_cases hp : psort s.k (i, j) = psort s.k (x, y)
  · rw [if_pos hp, (dist_psort_p30 hper hp).symm]
    exact hlt.le
  · rw [if_neg hp]
    exact hab.1

/-- `BBs` realisations of the cs2-restriction are `BBs` realisations of `s`. -/
theorem BBs_restrictionCs2_to_s_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (ww : ℕ → V3)
    (hs : isScsV39 s) (h1 : s.a i j ≤ c)
    (hbb : BBsV39 (restrictionCs2V39 s i j c) ww) : BBsV39 s ww := by
  obtain ⟨hann, hper, hdist, hfan⟩ := hbb
  refine ⟨hann, hper, ?_, ?_⟩
  · intro x y
    have hab := hdist x y
    exact ⟨le_trans (A_LE_A_OVERRIDE_p30 s i j x y c hs h1) hab.1, hab.2⟩
  · exact hfan

/-- `BBs` realisations of `s` with `dist (ww i) (ww j) <= c` are `BBs`
realisations of the cs1-restriction. -/
theorem BBs_s_to_restrictionCs1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (ww : ℕ → V3)
    (hs : isScsV39 s) (hbb : BBsV39 s ww) (h2 : c ≤ s.b i j)
    (hle : dist (ww i) (ww j) ≤ c) : BBsV39 (restrictionCs1V39 s i j c) ww := by
  obtain ⟨hann, hper, hdist, hfan⟩ := hbb
  refine ⟨hann, hper, ?_, hfan⟩
  intro x y
  have hab := hdist x y
  refine ⟨hab.1, ?_⟩
  show dist (ww x) (ww y) ≤ override s.b s.k (i, j) c x y
  unfold override
  by_cases hp : psort s.k (i, j) = psort s.k (x, y)
  · rw [if_pos hp, (dist_psort_p30 hper hp).symm]
    exact hle
  · rw [if_neg hp]
    exact hab.2

/-- `BBs` realisations of the cs1-restriction are `BBs` realisations of `s`. -/
theorem BBs_restrictionCs1_to_s_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (ww : ℕ → V3)
    (hs : isScsV39 s) (h2 : c ≤ s.b i j)
    (hbb : BBsV39 (restrictionCs1V39 s i j c) ww) : BBsV39 s ww := by
  obtain ⟨hann, hper, hdist, hfan⟩ := hbb
  refine ⟨hann, hper, ?_, ?_⟩
  · intro x y
    exact ⟨(hdist x y).1,
      le_trans (hdist x y).2 (B_OVERRIDE_LE_B_p30 s i j x y c hs h2)⟩
  · exact hfan

/-- HOL `BB_EQ_UNION_BB_SUBDIVISION` (UAGHHBM.hl:223). HOL `BBs_v39 s` is
the set of `ww` with `BBsV39 s ww`. -/
theorem BB_EQ_UNION_BB_SUBDIVISION_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (hs : isScsV39 s) (h1 : s.a i j ≤ c) (h2 : c ≤ s.b i j) :
    {ww | BBsV39 s ww} = {ww | BBsV39 (restrictionCs1V39 s i j c) ww} ∪
      {ww | BBsV39 (restrictionCs2V39 s i j c) ww} := by
  ext ww
  simp only [Set.mem_setOf_eq, Set.mem_union]
  by_cases hd : dist (ww i) (ww j) ≤ c
  · constructor
    · intro hbb
      exact Or.inl (BBs_s_to_restrictionCs1_p30 s i j c ww hs hbb h2 hd)
    · intro h
      rcases h with h | h
      · exact BBs_restrictionCs1_to_s_p30 s i j c ww hs h2 h
      · exact BBs_restrictionCs2_to_s_p30 s i j c ww hs h1 h
  · have hd' : c < dist (ww i) (ww j) := not_le.mp hd
    constructor
    · intro hbb
      exact Or.inr (BBs_s_to_restrictionCs2_p30 s i j c ww hs hbb h1 hd')
    · intro h
      rcases h with h | h
      · exact BBs_restrictionCs1_to_s_p30 s i j c ww hs h2 h
      · exact BBs_restrictionCs2_to_s_p30 s i j c ww hs h1 h

/-! ## Section D: the cs2 (`c < dist`) BBindex chain (UAGHHBM.hl:499-1065) -/

/-- HOL `BBINDEX_EQ_SUBDIVISION` (UAGHHBM.hl:499). -/
theorem BBINDEX_EQ_SUBDIVISION_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (ww : ℕ → V3)
    (hs : isScsV39 s) (h1 : s.a i j ≤ c) (hbb : BBsV39 s ww)
    (hlt : c < dist (ww i) (ww j)) :
    BBindexV39 s ww = BBindexV39 (restrictionCs2V39 s i j c) ww := by
  have hper := hbb.2.1
  have iff_a : ∀ x : ℕ, (x < s.k ∧ s.a x (x + 1) = dist (ww x) (ww (x + 1)) ↔
      x < s.k ∧
        (restrictionCs2V39 s i j c).a x (x + 1) = dist (ww x) (ww (x + 1))) := by
    intro x
    have proj : (restrictionCs2V39 s i j c).a x (x + 1) =
        override s.a s.k (i, j) c x (x + 1) := rfl
    constructor
    · rintro ⟨h1x, h2x⟩
      refine ⟨h1x, ?_⟩
      rw [proj]
      unfold override
      by_cases hp : psort s.k (i, j) = psort s.k (x, x + 1)
      · rw [if_pos hp]
        exfalso
        have hdd : dist (ww i) (ww j) = dist (ww x) (ww (x + 1)) :=
          dist_psort_p30 hper hp
        have haxx : s.a x (x + 1) = s.a i j :=
          (a_psort_p30 s hs hp).symm
        rw [← hdd, haxx] at h2x
        linarith [h2x, h1, hlt]
      · rw [if_neg hp]
        exact h2x
    · rintro ⟨h1x, h2x⟩
      refine ⟨h1x, ?_⟩
      rw [proj] at h2x
      unfold override at h2x
      by_cases hp : psort s.k (i, j) = psort s.k (x, x + 1)
      · exfalso
        rw [if_pos hp] at h2x
        have hdd : dist (ww i) (ww j) = dist (ww x) (ww (x + 1)) :=
          dist_psort_p30 hper hp
        rw [← hdd] at h2x
        linarith [h2x, hlt]
      · rw [if_neg hp] at h2x
        exact h2x
  unfold BBindexV39
  congr 1
  ext x
  have hkk : (restrictionCs2V39 s i j c).k = s.k := rfl
  simp only [hkk, Set.mem_setOf_eq]
  exact iff_a x

/-- HOL `CONDITION_BBPRIME_SUBSET_BBPRIME_SUBDIVISION` (UAGHHBM.hl:643). -/
theorem CONDITION_BBPRIME_SUBSET_BBPRIME_SUBDIVISION_p30 (s : ScsV39) (i j : ℕ)
    (c : ℝ) (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hlt : c < dist (ww i) (ww j)) : BBsV39 (restrictionCs2V39 s i j c) ww :=
  BBs_s_to_restrictionCs2_p30 s i j c ww hs hbp.1 h1 hlt

/-- HOL `BBPRIME_SUBDIVISION2_SUBSET_BBPRIME` (UAGHHBM.hl:704). -/
theorem BBPRIME_SUBDIVISION2_SUBSET_BBPRIME_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hlt : c < dist (ww i) (ww j)) :
    BBprimeV39 (restrictionCs2V39 s i j c) ⊆ BBprimeV39 s := by
  have htau2 : ∀ w : ℕ → V3,
      taustarV39 (restrictionCs2V39 s i j c) w = taustarV39 s w :=
    fun w => (SUBDIVISION_CS1_TAUSTAR_EQ_p30 s i j c w hk).2
  have hbbr : BBsV39 (restrictionCs2V39 s i j c) ww :=
    BBs_s_to_restrictionCs2_p30 s i j c ww hs hbp.1 h1 hlt
  intro x hx
  have hx2' := hx.2.2
  rw [htau2 x] at hx2'
  have hx3 : taustarV39 s x < 0 := hx2'
  refine ⟨BBs_restrictionCs2_to_s_p30 s i j c x hs h1 hx.1, ?_, hx3⟩
  intro z hz
  have h1' := hx.2.1 ww hbbr
  rw [htau2 x, htau2 ww] at h1'
  have h2' := hbp.2.1 z hz
  linarith

/-- HOL `IN_BBPRIME_SUBDIVISION` (UAGHHBM.hl:754). -/
theorem IN_BBPRIME_SUBDIVISION_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (ww : ℕ → V3)
    (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c) (h2 : c ≤ s.b i j)
    (hbp : ww ∈ BBprimeV39 s) (hlt : c < dist (ww i) (ww j)) :
    ww ∈ BBprimeV39 (restrictionCs2V39 s i j c) := by
  have htau2 : ∀ w : ℕ → V3,
      taustarV39 (restrictionCs2V39 s i j c) w = taustarV39 s w :=
    fun w => (SUBDIVISION_CS1_TAUSTAR_EQ_p30 s i j c w hk).2
  refine ⟨BBs_s_to_restrictionCs2_p30 s i j c ww hs hbp.1 h1 hlt, ?_, ?_⟩
  · intro z hz
    rw [htau2 ww, htau2 z]
    exact hbp.2.1 z (BBs_restrictionCs2_to_s_p30 s i j c z hs h1 hz)
  · rw [htau2 ww]
    exact hbp.2.2

/-- HOL `MIN_NUM_SUBSET` (UAGHHBM.hl:790). -/
theorem MIN_NUM_SUBSET_p30 {X Y : Set ℕ} {a : ℕ} (hsub : X ⊆ Y) (ha : a ∈ X) :
    minNum Y ≤ minNum X := by
  have hneX : X.Nonempty := ⟨a, ha⟩
  have hneY : Y.Nonempty := ⟨a, hsub ha⟩
  exact minNum_le_p30 hneY (hsub (minNum_mem_p30 hneX))

/-- HOL `BBINDEX_MIN_S_LE_SUBDIVISION2` (UAGHHBM.hl:800). -/
theorem BBINDEX_MIN_S_LE_SUBDIVISION2_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hlt : c < dist (ww i) (ww j)) :
    BBindexMinV39 s ≤ minNum
      (BBindexV39 s '' BBprimeV39 (restrictionCs2V39 s i j c)) := by
  have hsub : BBprimeV39 (restrictionCs2V39 s i j c) ⊆ BBprimeV39 s :=
    BBPRIME_SUBDIVISION2_SUBSET_BBPRIME_p30 s i j c ww hs hk h1 h2 hbp hlt
  have himg : BBindexV39 s '' BBprimeV39 (restrictionCs2V39 s i j c) ⊆
      BBindexV39 s '' BBprimeV39 s := Set.image_mono hsub
  have hin : ww ∈ BBprimeV39 (restrictionCs2V39 s i j c) :=
    IN_BBPRIME_SUBDIVISION_p30 s i j c ww hs hk h1 h2 hbp hlt
  exact MIN_NUM_SUBSET_p30 (a := BBindexV39 s ww) himg ⟨ww, hin, rfl⟩

/-- HOL `BBINDEX_BBPRIME_LE_SUBDIVISION2` (UAGHHBM.hl:828). -/
theorem BBINDEX_BBPRIME_LE_SUBDIVISION2_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww vv : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hlt : c < dist (ww i) (ww j))
    (hbv : vv ∈ BBprimeV39 (restrictionCs2V39 s i j c)) :
    BBindexV39 s vv ≤ BBindexV39 (restrictionCs2V39 s i j c) vv := by
  have hper : Periodic vv s.k :=
    (BBs_restrictionCs2_to_s_p30 s i j c vv hs h1 hbv.1).2.1
  have hc : c ≤ dist (vv i) (vv j) := by
    have hab := hbv.1.2.2.1 i j |>.1
    have proj : (restrictionCs2V39 s i j c).a i j = c := by
      show override s.a s.k (i, j) c i j = c
      unfold override
      rw [if_pos rfl]
    rw [proj] at hab
    exact hab
  have hkk : (restrictionCs2V39 s i j c).k = s.k := rfl
  have hfin2 : {x | x < (restrictionCs2V39 s i j c).k ∧
      (restrictionCs2V39 s i j c).a x (x + 1) = dist (vv x) (vv (x + 1))}.Finite :=
    Set.Finite.subset (Set.finite_lt_nat s.k) (fun x hx => hkk ▸ hx.1)
  unfold BBindexV39
  refine Set.ncard_le_ncard (fun x hx => ⟨hx.1, ?_⟩) hfin2
  show override s.a s.k (i, j) c x (x + 1) = dist (vv x) (vv (x + 1))
  unfold override
  by_cases hp : psort s.k (i, j) = psort s.k (x, x + 1)
  · rw [if_pos hp]
    have hdd : dist (vv i) (vv j) = dist (vv x) (vv (x + 1)) :=
      dist_psort_p30 hper hp
    have haxx : s.a x (x + 1) = s.a i j :=
      (a_psort_p30 s hs hp).symm
    rw [← hdd]
    linarith [hx.2, haxx, h1, hc, hdd]
  · rw [if_neg hp]
    exact hx.2

/-! ## Section E: the cs2 minimum/emptyness chain (UAGHHBM.hl:1068-1342) -/

/-- HOL `MIN_NUM_LE_IMAGE` (UAGHHBM.hl:1068). -/
theorem MIN_NUM_LE_IMAGE_p30 {A : Type*} {S : Set A} {f g : A → ℕ} {a : A}
    (ha : a ∈ S) (h : ∀ x ∈ S, f x ≤ g x) :
    minNum (f '' S) ≤ minNum (g '' S) := by
  have hne : (g '' S).Nonempty := ⟨g a, a, ha, rfl⟩
  have hmem : minNum (g '' S) ∈ g '' S := minNum_mem_p30 hne
  obtain ⟨x, hxS, hxeq⟩ := hmem
  have hfne : (f '' S).Nonempty := ⟨f x, x, hxS, rfl⟩
  calc minNum (f '' S) ≤ f x := minNum_le_p30 hfne ⟨x, hxS, rfl⟩
    _ ≤ g x := h x hxS
    _ = minNum (g '' S) := hxeq

/-- HOL `CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION2` (UAGHHBM.hl:1108). -/
theorem CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION2_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hlt : c < dist (ww i) (ww j)) :
    minNum (BBindexV39 s '' BBprimeV39 (restrictionCs2V39 s i j c)) ≤
      minNum (BBindexV39 (restrictionCs2V39 s i j c) ''
        BBprimeV39 (restrictionCs2V39 s i j c)) := by
  have hin : ww ∈ BBprimeV39 (restrictionCs2V39 s i j c) :=
    IN_BBPRIME_SUBDIVISION_p30 s i j c ww hs hk h1 h2 hbp hlt
  exact MIN_NUM_LE_IMAGE_p30 hin fun x hx =>
    BBINDEX_BBPRIME_LE_SUBDIVISION2_p30 s i j c ww x hs hk h1 h2 hbp hlt hx

/-- HOL `BBindex_min_LE_SUBDIVISION2` (UAGHHBM.hl:1130). -/
theorem BBindex_min_LE_SUBDIVISION2_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hlt : c < dist (ww i) (ww j)) :
    BBindexMinV39 s ≤ BBindexMinV39 (restrictionCs2V39 s i j c) := by
  have hclaim := CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION2_p30 s i j c ww hs hk h1 h2
    hbp hlt
  have hmin := BBINDEX_MIN_S_LE_SUBDIVISION2_p30 s i j c ww hs hk h1 h2 hbp hlt
  have hdef : BBindexMinV39 (restrictionCs2V39 s i j c) =
      minNum (BBindexV39 (restrictionCs2V39 s i j c) ''
        BBprimeV39 (restrictionCs2V39 s i j c)) := rfl
  rw [hdef]
  exact le_trans hmin hclaim

/-- HOL `BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION` (UAGHHBM.hl:1146). -/
theorem BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hmm : ww ∈ MMsV39 s)
    (hlt : c < dist (ww i) (ww j)) :
    ww ∈ BBprime2V39 (restrictionCs2V39 s i j c) := by
  have hbp : ww ∈ BBprimeV39 s := hmm.1.1
  have hin : ww ∈ BBprimeV39 (restrictionCs2V39 s i j c) :=
    IN_BBPRIME_SUBDIVISION_p30 s i j c ww hs hk h1 h2 hbp hlt
  have heq : BBindexV39 (restrictionCs2V39 s i j c) ww = BBindexV39 s ww :=
    (BBINDEX_EQ_SUBDIVISION_p30 s i j c ww hs h1 hbp.1 hlt).symm
  have hmin2 : BBindexMinV39 s ≤ BBindexMinV39 (restrictionCs2V39 s i j c) :=
    BBindex_min_LE_SUBDIVISION2_p30 s i j c ww hs hk h1 h2 hbp hlt
  have hge : BBindexMinV39 (restrictionCs2V39 s i j c) ≤
      BBindexV39 (restrictionCs2V39 s i j c) ww := by
    have hne : (BBindexV39 (restrictionCs2V39 s i j c) ''
        BBprimeV39 (restrictionCs2V39 s i j c)).Nonempty :=
      ⟨BBindexV39 (restrictionCs2V39 s i j c) ww, ⟨ww, hin, rfl⟩⟩
    exact minNum_le_p30 hne ⟨ww, hin, rfl⟩
  refine ⟨hin, ?_⟩
  have hkey : BBindexMinV39 (restrictionCs2V39 s i j c) =
      BBindexV39 (restrictionCs2V39 s i j c) ww :=
    le_antisymm hge (by rw [heq, hmm.1.2]; exact hmin2)
  rw [hkey]

/-- HOL `MM_IS_NOT_2EMPTY_SUBDIVISION` (UAGHHBM.hl:1197). -/
theorem MM_IS_NOT_2EMPTY_SUBDIVISION_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (ham : s.am i j < c) (hmm : ww ∈ MMsV39 s)
    (hlt : c < dist (ww i) (ww j)) :
    ww ∈ MMsV39 (restrictionCs2V39 s i j c) := by
  have hper : Periodic ww s.k := hmm.1.1.1.2.1
  refine ⟨BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION_p30 s i j c ww hs hk h1 h2 hmm hlt,
    hmm.2.1, hmm.2.2.1, hmm.2.2.2.1, ?_, ?_⟩
  · intro x y
    show (if s.am i j < c then override s.am s.k (i, j) c else s.am) x y ≤
      dist (ww x) (ww y)
    rw [if_pos ham]
    unfold override
    by_cases hp : psort s.k (i, j) = psort s.k (x, y)
    · rw [if_pos hp, (dist_psort_p30 hper hp).symm]
      exact hlt.le
    · rw [if_neg hp]
      exact hmm.2.2.2.2.1 x y
  · intro x y
    exact hmm.2.2.2.2.2 x y

/-- HOL `MM_IS_NOT_1EMPTY_SUBDIVISION` (UAGHHBM.hl:1323). -/
theorem MM_IS_NOT_1EMPTY_SUBDIVISION_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hge : c ≤ s.am i j) (hmm : ww ∈ MMsV39 s)
    (hlt : c < dist (ww i) (ww j)) :
    ww ∈ MMsV39 (restrictionCs2V39 s i j c) := by
  have hper : Periodic ww s.k := hmm.1.1.1.2.1
  refine ⟨BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION_p30 s i j c ww hs hk h1 h2 hmm hlt,
    hmm.2.1, hmm.2.2.1, hmm.2.2.2.1, ?_, ?_⟩
  · intro x y
    show (if s.am i j < c then override s.am s.k (i, j) c else s.am) x y ≤
      dist (ww x) (ww y)
    rw [if_neg (not_lt.mpr hge)]
    exact hmm.2.2.2.2.1 x y
  · intro x y
    exact hmm.2.2.2.2.2 x y

/-! ## Section F: the cs1 (`dist <= c`) twins (UAGHHBM.hl:1350-1815) -/

/-- HOL `BBINDEX_EQ_SUBDIVISION1` (UAGHHBM.hl:1350). The cs1-restriction
does not touch `a` or `k`, so the two indices agree definitionally. -/
theorem BBINDEX_EQ_SUBDIVISION1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (ww : ℕ → V3)
    (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c) (h2 : c ≤ s.b i j)
    (hbb : BBsV39 s ww) (hle : dist (ww i) (ww j) ≤ c) :
    BBindexV39 s ww = BBindexV39 (restrictionCs1V39 s i j c) ww := rfl

/-- HOL `CONDITION_BBPRIME_SUBSET_BBPRIME_SUBDIVISION1` (UAGHHBM.hl:1370). -/
theorem CONDITION_BBPRIME_SUBSET_BBPRIME_SUBDIVISION1_p30 (s : ScsV39) (i j : ℕ)
    (c : ℝ) (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hle : dist (ww i) (ww j) ≤ c) : BBsV39 (restrictionCs1V39 s i j c) ww :=
  BBs_s_to_restrictionCs1_p30 s i j c ww hs hbp.1 h2 hle

/-- HOL `IN_BBPRIME_SUBDIVISION1` (UAGHHBM.hl:1435). -/
theorem IN_BBPRIME_SUBDIVISION1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (ww : ℕ → V3)
    (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c) (h2 : c ≤ s.b i j)
    (hbp : ww ∈ BBprimeV39 s) (hle : dist (ww i) (ww j) ≤ c) :
    ww ∈ BBprimeV39 (restrictionCs1V39 s i j c) := by
  have htau1 : ∀ w : ℕ → V3,
      taustarV39 (restrictionCs1V39 s i j c) w = taustarV39 s w :=
    fun w => (SUBDIVISION_CS1_TAUSTAR_EQ_p30 s i j c w hk).1
  refine ⟨BBs_s_to_restrictionCs1_p30 s i j c ww hs hbp.1 h2 hle, ?_, ?_⟩
  · intro z hz
    rw [htau1 ww, htau1 z]
    exact hbp.2.1 z (BBs_restrictionCs1_to_s_p30 s i j c z hs h2 hz)
  · rw [htau1 ww]
    exact hbp.2.2

/-- HOL `BBPRIME_SUBDIVISION2_SUBSET_BBPRIME1` (UAGHHBM.hl:1474). -/
theorem BBPRIME_SUBDIVISION2_SUBSET_BBPRIME1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hle : dist (ww i) (ww j) ≤ c) :
    BBprimeV39 (restrictionCs1V39 s i j c) ⊆ BBprimeV39 s := by
  have htau1 : ∀ w : ℕ → V3,
      taustarV39 (restrictionCs1V39 s i j c) w = taustarV39 s w :=
    fun w => (SUBDIVISION_CS1_TAUSTAR_EQ_p30 s i j c w hk).1
  have hbbr : BBsV39 (restrictionCs1V39 s i j c) ww :=
    BBs_s_to_restrictionCs1_p30 s i j c ww hs hbp.1 h2 hle
  intro x hx
  have hx2' := hx.2.2
  rw [htau1 x] at hx2'
  refine ⟨BBs_restrictionCs1_to_s_p30 s i j c x hs h2 hx.1, ?_, hx2'⟩
  intro z hz
  have h1' := hx.2.1 ww hbbr
  rw [htau1 x, htau1 ww] at h1'
  have h2' := hbp.2.1 z hz
  linarith

/-- HOL `BBINDEX_MIN_S_LE_SUBDIVISION1` (UAGHHBM.hl:1521). -/
theorem BBINDEX_MIN_S_LE_SUBDIVISION1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hle : dist (ww i) (ww j) ≤ c) :
    BBindexMinV39 s ≤ minNum
      (BBindexV39 s '' BBprimeV39 (restrictionCs1V39 s i j c)) := by
  have hsub : BBprimeV39 (restrictionCs1V39 s i j c) ⊆ BBprimeV39 s :=
    BBPRIME_SUBDIVISION2_SUBSET_BBPRIME1_p30 s i j c ww hs hk h1 h2 hbp hle
  have himg : BBindexV39 s '' BBprimeV39 (restrictionCs1V39 s i j c) ⊆
      BBindexV39 s '' BBprimeV39 s := Set.image_mono hsub
  have hin : ww ∈ BBprimeV39 (restrictionCs1V39 s i j c) :=
    IN_BBPRIME_SUBDIVISION1_p30 s i j c ww hs hk h1 h2 hbp hle
  exact MIN_NUM_SUBSET_p30 (a := BBindexV39 s ww) himg ⟨ww, hin, rfl⟩

/-- HOL `BBINDEX_BBPRIME_LE_SUBDIVISION1` (UAGHHBM.hl:1554). Again `rfl`,
since the cs1-restriction keeps `a` and `k`. -/
theorem BBINDEX_BBPRIME_LE_SUBDIVISION1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c) (h2 : c ≤ s.b i j)
    (hbp : ww ∈ BBprimeV39 s) (hle : dist (ww i) (ww j) ≤ c)
    (vv : ℕ → V3) (hbv : vv ∈ BBprimeV39 (restrictionCs1V39 s i j c)) :
    BBindexV39 s vv = BBindexV39 (restrictionCs1V39 s i j c) vv := rfl

/-- HOL `CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION1` (UAGHHBM.hl:1575). -/
theorem CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hle : dist (ww i) (ww j) ≤ c) :
    minNum (BBindexV39 s '' BBprimeV39 (restrictionCs1V39 s i j c)) ≤
      minNum (BBindexV39 (restrictionCs1V39 s i j c) ''
        BBprimeV39 (restrictionCs1V39 s i j c)) := by
  have hin : ww ∈ BBprimeV39 (restrictionCs1V39 s i j c) :=
    IN_BBPRIME_SUBDIVISION1_p30 s i j c ww hs hk h1 h2 hbp hle
  refine MIN_NUM_LE_IMAGE_p30 hin (fun x hx => ?_)
  exact (BBINDEX_BBPRIME_LE_SUBDIVISION1_p30 s i j c hs hk h1 h2 hbp hle x hx).le

/-- HOL `BBindex_min_LE_SUBDIVISION1` (UAGHHBM.hl:1598). -/
theorem BBindex_min_LE_SUBDIVISION1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hle : dist (ww i) (ww j) ≤ c) :
    BBindexMinV39 s ≤ BBindexMinV39 (restrictionCs1V39 s i j c) := by
  have hclaim := CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION1_p30 s i j c ww hs hk h1 h2
    hbp hle
  have hmin := BBINDEX_MIN_S_LE_SUBDIVISION1_p30 s i j c ww hs hk h1 h2 hbp hle
  have hdef : BBindexMinV39 (restrictionCs1V39 s i j c) =
      minNum (BBindexV39 (restrictionCs1V39 s i j c) ''
        BBprimeV39 (restrictionCs1V39 s i j c)) := rfl
  rw [hdef]
  exact le_trans hmin hclaim

/-- HOL `BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION1` (UAGHHBM.hl:1615). -/
theorem BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hmm : ww ∈ MMsV39 s)
    (hle : dist (ww i) (ww j) ≤ c) :
    ww ∈ BBprime2V39 (restrictionCs1V39 s i j c) := by
  have hbp : ww ∈ BBprimeV39 s := hmm.1.1
  have hin : ww ∈ BBprimeV39 (restrictionCs1V39 s i j c) :=
    IN_BBPRIME_SUBDIVISION1_p30 s i j c ww hs hk h1 h2 hbp hle
  have heq : BBindexV39 (restrictionCs1V39 s i j c) ww = BBindexV39 s ww := rfl
  have hmin2 : BBindexMinV39 s ≤ BBindexMinV39 (restrictionCs1V39 s i j c) :=
    BBindex_min_LE_SUBDIVISION1_p30 s i j c ww hs hk h1 h2 hbp hle
  have hge : BBindexMinV39 (restrictionCs1V39 s i j c) ≤
      BBindexV39 (restrictionCs1V39 s i j c) ww := by
    have hne : (BBindexV39 (restrictionCs1V39 s i j c) ''
        BBprimeV39 (restrictionCs1V39 s i j c)).Nonempty :=
      ⟨BBindexV39 (restrictionCs1V39 s i j c) ww, ⟨ww, hin, rfl⟩⟩
    exact minNum_le_p30 hne ⟨ww, hin, rfl⟩
  refine ⟨hin, ?_⟩
  have hkey : BBindexMinV39 (restrictionCs1V39 s i j c) =
      BBindexV39 (restrictionCs1V39 s i j c) ww :=
    le_antisymm hge (by rw [heq, hmm.1.2]; exact hmin2)
  rw [hkey]

/-- HOL `MM_IS_NOT_2EMPTY_SUBDIVISION1` (UAGHHBM.hl:1668). -/
theorem MM_IS_NOT_2EMPTY_SUBDIVISION1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbm : c < s.bm i j) (hmm : ww ∈ MMsV39 s)
    (hle : dist (ww i) (ww j) ≤ c) :
    ww ∈ MMsV39 (restrictionCs1V39 s i j c) := by
  have hper : Periodic ww s.k := hmm.1.1.1.2.1
  refine ⟨BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION1_p30 s i j c ww hs hk h1 h2 hmm hle,
    hmm.2.1, hmm.2.2.1, hmm.2.2.2.1, hmm.2.2.2.2.1, ?_⟩
  · intro x y
    show dist (ww x) (ww y) ≤
      (if c < s.bm i j then override s.bm s.k (i, j) c else s.bm) x y
    rw [if_pos hbm]
    unfold override
    by_cases hp : psort s.k (i, j) = psort s.k (x, y)
    · rw [if_pos hp, (dist_psort_p30 hper hp).symm]
      exact hle
    · rw [if_neg hp]
      exact hmm.2.2.2.2.2 x y

/-- HOL `MM_IS_NOT_1EMPTY_SUBDIVISION1` (UAGHHBM.hl:1796). -/
theorem MM_IS_NOT_1EMPTY_SUBDIVISION1_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbm : s.bm i j ≤ c) (hmm : ww ∈ MMsV39 s)
    (hle : dist (ww i) (ww j) ≤ c) :
    ww ∈ MMsV39 (restrictionCs1V39 s i j c) := by
  refine ⟨BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION1_p30 s i j c ww hs hk h1 h2 hmm hle,
    hmm.2.1, hmm.2.2.1, hmm.2.2.2.1, hmm.2.2.2.2.1, ?_⟩
  · intro x y
    show dist (ww x) (ww y) ≤
      (if c < s.bm i j then override s.bm s.k (i, j) c else s.bm) x y
    rw [if_neg (not_lt.mpr hbm)]
    exact hmm.2.2.2.2.2 x y

/-- HOL `BBPRIME_SUBSET_SUBDIVISION_UNION` (UAGHHBM.hl:432). -/
theorem BBPRIME_SUBSET_SUBDIVISION_UNION_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hlt : c < dist (ww i) (ww j)) :
    ww ∈ BBprimeV39 (restrictionCs1V39 s i j c) ∪
      BBprimeV39 (restrictionCs2V39 s i j c) :=
  Or.inr (IN_BBPRIME_SUBDIVISION_p30 s i j c ww hs hk h1 h2 hbp hlt)

/-- HOL `BBPRIME_SUBSET_BBPRIME_SUBDIVISION_UNION` (UAGHHBM.hl:485). -/
theorem BBPRIME_SUBSET_BBPRIME_SUBDIVISION_UNION_p30 (s : ScsV39) (i j : ℕ)
    (c : ℝ) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) :
    BBprimeV39 s ⊆ BBprimeV39 (restrictionCs1V39 s i j c) ∪
      BBprimeV39 (restrictionCs2V39 s i j c) := by
  intro x hx
  by_cases hd : dist (x i) (x j) ≤ c
  · exact Or.inl (IN_BBPRIME_SUBDIVISION1_p30 s i j c x hs hk h1 h2 hx hd)
  · have hd' : c < dist (x i) (x j) := not_le.mp hd
    exact Or.inr (IN_BBPRIME_SUBDIVISION_p30 s i j c x hs hk h1 h2 hx hd')

/-! ## Section G: the `c = am` edge-branch (UAGHHBM.hl:1820-2496) -/

/-- cs2-restriction transfer for the `dist (ww i) (ww j) = c` branch. -/
theorem BBs_s_to_restrictionCs2_eq_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hbb : BBsV39 s ww)
    (hdc : dist (ww i) (ww j) = c) : BBsV39 (restrictionCs2V39 s i j c) ww := by
  obtain ⟨hann, hper, hdist, hfan⟩ := hbb
  refine ⟨hann, hper, ?_, hfan⟩
  intro x y
  have hab := hdist x y
  refine ⟨?_, hab.2⟩
  show override s.a s.k (i, j) c x y ≤ dist (ww x) (ww y)
  unfold override
  by_cases hp : psort s.k (i, j) = psort s.k (x, y)
  · rw [if_pos hp, (dist_psort_p30 hper hp).symm]
    exact hdc.ge
  · rw [if_neg hp]
    exact hab.1

/-- HOL `CONDITION_BBPRIME_SUBSET_BBPRIME_SUBDIVISION_C_EQ_AM`
(UAGHHBM.hl:1930). -/
theorem CONDITION_BBPRIME_SUBSET_BBPRIME_SUBDIVISION_C_EQ_AM_p30 (s : ScsV39)
    (i j : ℕ) (c : ℝ) (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k)
    (h1 : s.a i j ≤ c) (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hdc : dist (ww i) (ww j) = c) (ham : s.am i j = c)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j) :
    BBsV39 (restrictionCs2V39 s i j c) ww :=
  BBs_s_to_restrictionCs2_eq_p30 s i j c ww hs hbp.1 hdc

/-- HOL `BBPRIME_SUBDIVISION2_SUBSET_BBPRIME_C_EQ_AM` (UAGHHBM.hl:1997). -/
theorem BBPRIME_SUBDIVISION2_SUBSET_BBPRIME_C_EQ_AM_p30 (s : ScsV39) (i j : ℕ)
    (c : ℝ) (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hdc : dist (ww i) (ww j) = c) (ham : s.am i j = c)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j) :
    BBprimeV39 (restrictionCs2V39 s i j c) ⊆ BBprimeV39 s := by
  have htau2 : ∀ w : ℕ → V3,
      taustarV39 (restrictionCs2V39 s i j c) w = taustarV39 s w :=
    fun w => (SUBDIVISION_CS1_TAUSTAR_EQ_p30 s i j c w hk).2
  have hbbr : BBsV39 (restrictionCs2V39 s i j c) ww :=
    BBs_s_to_restrictionCs2_eq_p30 s i j c ww hs hbp.1 hdc
  intro x hx
  have hx2' := hx.2.2
  rw [htau2 x] at hx2'
  refine ⟨BBs_restrictionCs2_to_s_p30 s i j c x hs h1 hx.1, ?_, hx2'⟩
  intro z hz
  have h1' := hx.2.1 ww hbbr
  rw [htau2 x, htau2 ww] at h1'
  have h2' := hbp.2.1 z hz
  linarith

/-- HOL `IN_BBPRIME_SUBDIVISION_C_EQ_AM` (UAGHHBM.hl:2049). -/
theorem IN_BBPRIME_SUBDIVISION_C_EQ_AM_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hdc : dist (ww i) (ww j) = c) (ham : s.am i j = c)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j) :
    ww ∈ BBprimeV39 (restrictionCs2V39 s i j c) := by
  have htau2 : ∀ w : ℕ → V3,
      taustarV39 (restrictionCs2V39 s i j c) w = taustarV39 s w :=
    fun w => (SUBDIVISION_CS1_TAUSTAR_EQ_p30 s i j c w hk).2
  refine ⟨BBs_s_to_restrictionCs2_eq_p30 s i j c ww hs hbp.1 hdc, ?_, ?_⟩
  · intro z hz
    rw [htau2 ww, htau2 z]
    exact hbp.2.1 z (BBs_restrictionCs2_to_s_p30 s i j c z hs h1 hz)
  · rw [htau2 ww]
    exact hbp.2.2

/-- HOL `BBINDEX_MIN_S_LE_SUBDIVISION2_C_EQ_AM` (UAGHHBM.hl:2088). -/
theorem BBINDEX_MIN_S_LE_SUBDIVISION2_C_EQ_AM_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hdc : dist (ww i) (ww j) = c) (ham : s.am i j = c)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j) :
    BBindexMinV39 s ≤ minNum
      (BBindexV39 s '' BBprimeV39 (restrictionCs2V39 s i j c)) := by
  have hsub : BBprimeV39 (restrictionCs2V39 s i j c) ⊆ BBprimeV39 s :=
    BBPRIME_SUBDIVISION2_SUBSET_BBPRIME_C_EQ_AM_p30 s i j c ww hs hk h1 h2 hbp
      hdc ham hedge
  have himg : BBindexV39 s '' BBprimeV39 (restrictionCs2V39 s i j c) ⊆
      BBindexV39 s '' BBprimeV39 s := Set.image_mono hsub
  have hin : ww ∈ BBprimeV39 (restrictionCs2V39 s i j c) :=
    IN_BBPRIME_SUBDIVISION_C_EQ_AM_p30 s i j c ww hs hk h1 h2 hbp hdc ham hedge
  exact MIN_NUM_SUBSET_p30 (a := BBindexV39 s ww) himg ⟨ww, hin, rfl⟩

/-- HOL `BBINDEX_EQ_SUBDIVISION_C_EQ_AM` (UAGHHBM.hl:1820).
NEEDS: the psort-matched-cell cancellation `IMP_SUC_MOD_EQ` counting kit
(UAGHHBM.hl:1841-1926): the cells with `psort k (i,j) = psort k (x, x+1)`
where `s.a x (x+1) ≠ c = s.am i j` drop out of both index sets, and
`CARD_IMAGE_INJ_EQ` over the residue injection closes the equality. -/
theorem BBINDEX_EQ_SUBDIVISION_C_EQ_AM_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j) (hbb : BBsV39 s ww) (hdc : dist (ww i) (ww j) = c)
    (ham : s.am i j = c) :
    BBindexV39 s ww = BBindexV39 (restrictionCs2V39 s i j c) ww := by
  sorry

/-- HOL `BBINDEX_BBPRIME_LE_SUBDIVISION2_C_EQ_AM` (UAGHHBM.hl:2120).
NEEDS: same psort-matched-cell cancellation (`CARD_SUBSET` +
`IMP_SUC_MOD_EQ`), UAGHHBM.hl:2144-2370. -/
theorem BBINDEX_BBPRIME_LE_SUBDIVISION2_C_EQ_AM_p30 (s : ScsV39) (i j : ℕ)
    (c : ℝ) (ww vv : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k)
    (h1 : s.a i j ≤ c) (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hdc : dist (ww i) (ww j) = c) (ham : s.am i j = c)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j)
    (hbv : vv ∈ BBprimeV39 (restrictionCs2V39 s i j c)) :
    BBindexV39 s vv ≤ BBindexV39 (restrictionCs2V39 s i j c) vv := by
  sorry

/-- HOL `CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION2_C_EQ_AM` (UAGHHBM.hl:2378).
NEEDS: `BBINDEX_BBPRIME_LE_SUBDIVISION2_C_EQ_AM_p30`. -/
theorem CLAIM_BBINDEX_BBPRIME_LE_SUBDIVISION2_C_EQ_AM_p30 (s : ScsV39)
    (i j : ℕ) (c : ℝ) (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k)
    (h1 : s.a i j ≤ c) (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hdc : dist (ww i) (ww j) = c) (ham : s.am i j = c)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j) :
    minNum (BBindexV39 s '' BBprimeV39 (restrictionCs2V39 s i j c)) ≤
      minNum (BBindexV39 (restrictionCs2V39 s i j c) ''
        BBprimeV39 (restrictionCs2V39 s i j c)) := by
  sorry

/-- HOL `BBindex_min_LE_SUBDIVISION2_C_EQ_AM` (UAGHHBM.hl:2403).
NEEDS: the two preceding C_EQ_AM min lemmas. -/
theorem BBindex_min_LE_SUBDIVISION2_C_EQ_AM_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hbp : ww ∈ BBprimeV39 s)
    (hdc : dist (ww i) (ww j) = c) (ham : s.am i j = c)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j) :
    BBindexMinV39 s ≤ BBindexMinV39 (restrictionCs2V39 s i j c) := by
  sorry

/-- HOL `BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION_C_EQ_AM` (UAGHHBM.hl:2422).
NEEDS: `BBINDEX_EQ_SUBDIVISION_C_EQ_AM_p30` and
`BBindex_min_LE_SUBDIVISION2_C_EQ_AM_p30`. -/
theorem BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION_C_EQ_AM_p30 (s : ScsV39) (i j : ℕ)
    (c : ℝ) (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hmm : ww ∈ MMsV39 s)
    (hdc : dist (ww i) (ww j) = c) (ham : s.am i j = c)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j) :
    ww ∈ BBprime2V39 (restrictionCs2V39 s i j c) := by
  sorry

/-- HOL `MM_IS_NOT_2EMPTY_SUBDIVISION_C_EQ_AM` (UAGHHBM.hl:2476).
NEEDS: `BBPRIME2_IS_NOT_2EMPTY_SUBDIVISION_C_EQ_AM_p30` (the am-side
matches `ham` through `override` + `psort` case analysis). -/
theorem MM_IS_NOT_2EMPTY_SUBDIVISION_C_EQ_AM_p30 (s : ScsV39) (i j : ℕ) (c : ℝ)
    (ww : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j) (hmm : ww ∈ MMsV39 s)
    (hdc : dist (ww i) (ww j) = c) (ham : s.am i j = c)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j) :
    ww ∈ MMsV39 (restrictionCs2V39 s i j c) := by
  sorry

/-! ## Section H: the master subdivision arrow (UAGHHBM.hl:2501-4095) -/

/-- HOL `UAGHHBM` (UAGHHBM.hl:2501): the forking conclusion
`scs_arrow_v39 {s} (set_of_list (subdiv_v39 s i j c))`.
NEEDS: the full fork analysis over `subdivV39`'s four cases (HOL
UAGHHBM.hl:2501-4095): `SCS_A_2`-style edge regime, the psort/override
rewrites of `is_scs_v39` for each restriction, and Sections D-G. -/
theorem UAGHHBM_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (hs : isScsV39 s)
    (hij : i % s.k ≠ j % s.k) (hJ : ¬s.J i j) (h1 : s.a i j ≤ c)
    (h2 : c ≤ s.b i j)
    (hedge : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      2 < s.a i j ∨ 2 * h0 < s.b i j) (hk : 3 < s.k)
    (hne : (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k) →
      c ≠ s.am i j) :
    scsArrowV39 {s} {t | t ∈ subdivV39 s i j c} := by
  sorry

end Kepler.Text
