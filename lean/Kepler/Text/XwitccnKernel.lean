/-
XwitccnKernel: the strictly-upstream kernel for `Kepler.Text.LocalAuto36.XWITCCN`
(the eight-system `sInitListV39` taustar-minimiser capstone).

Why a separate upstream module: `XWITCCN`'s minimal realisations are produced by
the `UXCKFPE` case bank, whose engine-sunk bodies live in `Kepler.Text.LocalAuto24`
(`HDPLYGY_CASE_30_p24`, `XWITCCN_CASE_*_IS_SCS_p24`, `UXCKFPE_p24`) and whose
`isScs` substrate `s_init_scs` lives in `Kepler.Text.LocalAuto27`.  LocalAuto24
imports LocalAuto36, so LocalAuto36 cannot import the case bank directly; this
module carries the case bank strictly above it.

Contents (all PROVED, zero `sorry`):
- a verbatim copy of LocalAuto36's Section 0.5-0.7 kit (fan p4<->registry
  bridge, `vSy/eSy/fSy_eq_range`, `inNotEmpty_core`/`inB1_core`) under the
  private namespace `X36` (declaration names unchanged inside X36);
- verbatim copies of LocalAuto24's Section C (`UXCKFPE.hl`) case bank under
  `_xw6` names (the w1 `tau3` continuity kit, `J1_TS`/`dFun3`,
  `HDPLYGY_CASE_30`, `TAUSTAR_EQ_TAU_STAR_3`, `XWITCCN_CASE_*_IS_SCS`,
  `UXCKFPE`), i.e. the same text that `SgtrnafKernel` carries as `_krnl`;
- the `sInitListV39` `isScs` substrate: `s_init_scs_xw6`, from LocalAuto27's
  `s_init_scs_p27` (with its `init7*/init8*` table identities), plus the
  LocalAuto20 `SCS_5I3_IS_SCS` / `init8` certificates reproduced over
  LocalAuto1/22/23 kit (`LocalAuto20` itself is downstream, so its small
  numeric lemmas are copied under `_xw6` names);
- `XWITCCN_xw6`, the upstream twin of LocalAuto36's `XWITCCN`.

Axiom face: standard three (`propext`, `Classical.choice`, `Quot.sound`).
`LocalAuto36.XWITCCN` delegates to `XWITCCN_xw6` by one line.
-/
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto3
import Kepler.Text.LocalAuto4
import Kepler.Text.LocalAuto8
import Kepler.Text.LocalAuto22
import Kepler.Text.LocalAuto23
import Kepler.Text.AzimBridge
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Part 1: LocalAuto36 Sections 0.5-0.7, verbatim under namespace `X36` -/

namespace X36

/-! ## Section 0: shared kit -/

/-- HOL `change_type_v3` (XWITCCN.hl:322): uncurry a curried table to the
pair-indexed `CONDITION1_SY` shape. -/
def change_type_v3 (a : ℕ → ℕ → ℝ) (p : ℕ × ℕ) : ℝ := a p.1 p.2

/-- HOL `change_type_v2` (XWITCCN.hl:326): the `J`-table as the set of
`k`-residue edges `{i MOD k, j MOD k}` with `a i j`. -/
def change_type_v2 (a : ℕ → ℕ → Prop) (k : ℕ) : Set (Set ℕ) :=
  {e | ∃ i j, a i j ∧ e = {(i : ℕ) % k, j % k}}

/-- HOL `a_pro` (the `let a_pro = ...` of the `upperbd = &6` blocks; also a
local of `sInitListV39`). -/
noncomputable def aPro (k : ℕ) (p a1 a2 : ℝ) (i j : ℕ) : ℝ :=
  if i % k = j % k then 0
  else if ({i % k, j % k} : Set ℕ) = {0, 1} then p
  else if j % k = (i + 1) % k ∨ (j + 1) % k = i % k then a1 else a2

/-- HOL `PERIODIC_PROPERTY` (XWITCCN.hl:330) — twin of the PROVED
PackingAuto3 lemma over the LocalAuto1 `Periodic`. -/
theorem PERIODIC_PROPERTY_p36 {vv : ℕ → V3} {k : ℕ} (_hk : k ≠ 0)
    (hper : Periodic vv k) (i : ℕ) : vv (i % k) = vv i :=
  periodic_mod_eq_p23 hper i

/-- `change_type_v2 s.J s.k` is the `scsJSet_p23 s` of the LocalAuto23 kit
(the residue bounds supply the `i < k ∧ j < k` side conditions). -/
theorem change_type_v2_eq {s : ScsV39} (hk : 0 < s.k) (hJp : Periodic2 s.J s.k) :
    change_type_v2 s.J s.k = scsJSet_p23 s := by
  unfold change_type_v2 scsJSet_p23
  ext e
  constructor
  · rintro ⟨i, j, hJ, rfl⟩
    refine ⟨i % s.k, j % s.k, Nat.mod_lt _ hk, Nat.mod_lt _ hk, ?_, rfl⟩
    have e1 : ∀ i j : ℕ, s.J (i % s.k) j = s.J i j := by
      intro i j
      have hp : Periodic (fun x => s.J x j) s.k := fun t => (hJp t j).1
      simpa using periodic_mod_eq_p23 hp i
    have e2 : ∀ i j : ℕ, s.J i (j % s.k) = s.J i j := by
      intro i j
      have hp : Periodic (fun x => s.J i x) s.k := fun t => (hJp i t).2
      simpa using periodic_mod_eq_p23 hp j
    have key : s.J (i % s.k) (j % s.k) = s.J i j :=
      (e1 i (j % s.k)).trans (e2 i j)
    rw [key]
    exact hJ
  · rintro ⟨i, j, hi, hj, hJ, rfl⟩
    exact ⟨i, j, hJ, by rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]⟩

/-- `csAdj` reads only residues. -/
theorem csAdj_mod_p36 (k : ℕ) (a1 a2 : ℝ) (i j : ℕ) :
    csAdj k a1 a2 i j = csAdj k a1 a2 (i % k) (j % k) := by
  simp only [csAdj, Nat.mod_mod, Nat.add_mod]

/-- `aPro` reads only residues. -/
theorem aPro_mod_p36 (k : ℕ) (p a1 a2 : ℝ) (i j : ℕ) :
    aPro k p a1 a2 i j = aPro k p a1 a2 (i % k) (j % k) := by
  simp only [aPro, Nat.mod_mod, Nat.add_mod]

/-- HOL `VECTOR_3_3` (XWITCCN.hl:1291): the rows of the k = 3 cyclic
`vector[vv 1; vv 2; vv 0]`. -/
theorem VECTOR_3_3 (vv : ℕ → V3) :
    cycRow_p23 vv 3 0 = vv 1 ∧ cycRow_p23 vv 3 1 = vv 2 ∧ cycRow_p23 vv 3 2 = vv 0 :=
  ⟨rfl, rfl, rfl⟩

/-- HOL `VECTOR_3_4` (XWITCCN.hl:2429). -/
theorem VECTOR_3_4 (vv : ℕ → V3) :
    cycRow_p23 vv 4 0 = vv 1 ∧ cycRow_p23 vv 4 1 = vv 2 ∧ cycRow_p23 vv 4 2 = vv 3 ∧
      cycRow_p23 vv 4 3 = vv 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- HOL `VECTOR_3_5` (XWITCCN.hl:3232). -/
theorem VECTOR_3_5 (vv : ℕ → V3) :
    cycRow_p23 vv 5 0 = vv 1 ∧ cycRow_p23 vv 5 1 = vv 2 ∧ cycRow_p23 vv 5 2 = vv 3 ∧
      cycRow_p23 vv 5 3 = vv 4 ∧ cycRow_p23 vv 5 4 = vv 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- HOL `VECTOR_3_6` (XWITCCN.hl:4072). -/
theorem VECTOR_3_6 (vv : ℕ → V3) :
    cycRow_p23 vv 6 0 = vv 1 ∧ cycRow_p23 vv 6 1 = vv 2 ∧ cycRow_p23 vv 6 2 = vv 3 ∧
      cycRow_p23 vv 6 3 = vv 4 ∧ cycRow_p23 vv 6 4 = vv 5 ∧ cycRow_p23 vv 6 5 = vv 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- HOL `stable_sy_explicit` (XWITCCN.hl:1271): the projections of the
`stable_sy (k,d,s,a,b,J,f)` record. The unused HOL reals dummy `d` is the
`0` of the LocalAuto23 kit. -/
theorem stable_sy_explicit {k : ℕ} {I : Set ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Set (Set ℕ)} {f : ℕ → ℕ} (hs : stableSystem_p23 k 0 I a b J f) :
    (StableSyP23.k ⟨k, 0, I, a, b, J, f, hs⟩ : ℕ) = k ∧
    (StableSyP23.d ⟨k, 0, I, a, b, J, f, hs⟩ : ℝ) = 0 ∧
    (StableSyP23.I ⟨k, 0, I, a, b, J, f, hs⟩ : Set ℕ) = I ∧
    (StableSyP23.a ⟨k, 0, I, a, b, J, f, hs⟩) = a ∧
    (StableSyP23.b ⟨k, 0, I, a, b, J, f, hs⟩) = b ∧
    (StableSyP23.J ⟨k, 0, I, a, b, J, f, hs⟩ : Set (Set ℕ)) = J ∧
    (StableSyP23.f ⟨k, 0, I, a, b, J, f, hs⟩) = f :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Mod bookkeeping: `(n % k + 1) % k = (n + 1) % k`. -/
theorem mod_add_one_mod_p36 (k n : ℕ) : (n % k + 1) % k = (n + 1) % k :=
  Nat.mod_add_mod n k 1

/-- The cyclic predecessor `r + k - 1` shifts back to `r` after one `+1 MOD k`. -/
theorem modShift_p36 (k r : ℕ) (hrk : r < k) :
    ((r + k - 1) % k + 1) % k = r % k := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    rw [show 0 + k - 1 = k - 1 by omega, Nat.mod_eq_of_lt (by omega : k - 1 < k),
      show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod]
  · rw [show r + k - 1 = r - 1 + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : r - 1 < k), show r - 1 + 1 = r by omega]

/-- The `V_SY = range vv` conjunct of `V_E_FF_CASE_k` (proved core; the
cyclic shift `i ↦ i+1` is a bijection `Fin k → Fin k` up to `Periodic`). -/
theorem vSy_eq_range_p36 {k : ℕ} (hk : 0 < k) {vv : ℕ → V3} (hper : Periodic vv k) :
    V_SY_p4 (cycRow_p23 vv k) = Set.range vv := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨i, rfl⟩
    exact ⟨(i : ℕ) + 1, (periodic_mod_eq_p23 hper ((i : ℕ) + 1)).symm⟩
  · rintro _ ⟨n, rfl⟩
    refine ⟨⟨(n % k + k - 1) % k, Nat.mod_lt _ hk⟩, ?_⟩
    show vv (((n % k + k - 1) % k + 1) % k) = vv n
    rw [modShift_p36 _ _ (Nat.mod_lt n hk), Nat.mod_mod]
    exact periodic_mod_eq_p23 hper n

/-- The cyclic index that decodes `vv n` as row `i` (and `vv (n+1)` as its
`finNext` row). -/
theorem cycRow_shift_p36 {k : ℕ} (hk : 0 < k) {vv : ℕ → V3} (hper : Periodic vv k)
    (n : ℕ) : ∃ i : Fin k, cycRow_p23 vv k i = vv n ∧
      cycRow_p23 vv k (finNext i) = vv (n + 1) := by
  have e1 : ((n % k + k - 1) % k + 1) % k = n % k := by
    rw [modShift_p36 _ _ (Nat.mod_lt n hk), Nat.mod_mod]
  have e2 : (((n % k + k - 1) % k + 1) % k + 1) % k = (n + 1) % k := by
    rw [e1]
    exact mod_add_one_mod_p36 k n
  refine ⟨⟨(n % k + k - 1) % k, Nat.mod_lt _ hk⟩, ?_, ?_⟩
  · have h1 : cycRow_p23 vv k (⟨(n % k + k - 1) % k, Nat.mod_lt _ hk⟩ : Fin k)
        = vv (((n % k + k - 1) % k + 1) % k) := rfl
    rw [h1, e1]
    exact periodic_mod_eq_p23 hper n
  · have h2 : cycRow_p23 vv k
        (finNext (⟨(n % k + k - 1) % k, Nat.mod_lt _ hk⟩ : Fin k))
        = vv ((((n % k + k - 1) % k + 1) % k + 1) % k) := rfl
    rw [h2, e2]
    exact periodic_mod_eq_p23 hper (n + 1)

/-- The `E_SY = range (fun i => {vv i, vv (i+1)})` conjunct (proved core). -/
theorem eSy_eq_range_p36 {k : ℕ} (hk : 0 < k) {vv : ℕ → V3} (hper : Periodic vv k) :
    E_SY_p4 (cycRow_p23 vv k) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨i, -, rfl⟩
    refine ⟨(i : ℕ) + 1, ?_⟩
    simp only [cycRow_p23, finNext]
    rw [periodic_mod_eq_p23 hper ((i : ℕ) + 1), mod_add_one_mod_p36,
      periodic_mod_eq_p23 hper ((i : ℕ) + 1 + 1)]
  · rintro _ ⟨n, rfl⟩
    obtain ⟨i, hi1, hi2⟩ := cycRow_shift_p36 hk hper n
    exact ⟨i, Set.mem_univ i, by simp only; rw [hi1, hi2]⟩

/-- The `F_SY = range (fun i => (vv i, vv (i+1)))` conjunct (proved core). -/
theorem fSy_eq_range_p36 {k : ℕ} (hk : 0 < k) {vv : ℕ → V3} (hper : Periodic vv k) :
    F_SY_p4 (cycRow_p23 vv k) = Set.range (fun i : ℕ => (vv i, vv (i + 1))) := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨i, -, rfl⟩
    refine ⟨(i : ℕ) + 1, ?_⟩
    simp only [cycRow_p23, finNext]
    rw [periodic_mod_eq_p23 hper ((i : ℕ) + 1), mod_add_one_mod_p36,
      periodic_mod_eq_p23 hper ((i : ℕ) + 1 + 1)]
  · rintro _ ⟨n, rfl⟩
    obtain ⟨i, hi1, hi2⟩ := cycRow_shift_p36 hk hper n
    exact ⟨i, Set.mem_univ i, by simp only; rw [hi1, hi2]⟩


/-! ## Section 0.5: shared helpers (succ-torsor kit, table symm, concrete
stable-system builders for the eight `s_init_list_v39` tables) -/

theorem succ_mod_ne_p36 {k : ℕ} (hk : 1 < k) (n : ℕ) : n % k ≠ (n + 1) % k := by
  have e1 : (n + 1) % k = (n % k + 1) % k := by simp [Nat.add_mod]
  have h1 : n % k < k := Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge (n % k + 1) k with h | h
  · rw [e1, Nat.mod_eq_of_lt (by omega : n % k + 1 < k)]
    omega
  · have hk1 : n % k + 1 = k := by omega
    rw [e1, hk1, Nat.mod_self]
    omega

theorem succModIter_p36 (k : ℕ) (hk : 0 < k) {j : ℕ} (hj : j < k) (n : ℕ) :
    (fun i => (1 + i) % k)^[n] j = (j + n) % k := by
  induction n with
  | zero =>
      show j = j % k
      exact (Nat.mod_eq_of_lt hj).symm
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, Nat.add_comm]
      exact Nat.ModEq.add_right (c := 1) (Nat.mod_modEq (j + m) k)

theorem succModIter_pos_p36 (k : ℕ) (hk : 0 < k) (j n : ℕ) (hn : 0 < n) :
    (fun i => (1 + i) % k)^[n] j = (j + n) % k := by
  induction n with
  | zero => exact absurd hn (by omega)
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst m
        show (1 + j) % k = (j + 1) % k
        rw [Nat.add_comm]
      · rw [Function.iterate_succ_apply', ih hm, Nat.add_comm 1 ((j + m) % k)]
        exact Nat.ModEq.add_right (c := 1) (Nat.mod_modEq (j + m) k)

theorem torsor_succ_mod_p36 {k : ℕ} (hk : 0 < k) :
    torsor_p23 (Set.Iic (k - 1)) k (fun i => (1 + i) % k) := by
  have hxl : ∀ x ∈ Set.Iic (k - 1), x < k := fun x hx => by
    rw [Set.mem_Iic] at hx
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxl : x < k := hxl x hx
    show (1 + x) % k ≤ k - 1
    rcases Nat.lt_or_ge (1 + x) k with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  · intro x1 hx1 x2 hx2 heq
    have h1 : x1 < k := hxl x1 hx1
    have h2 : x2 < k := hxl x2 hx2
    have hme : Nat.ModEq k (1 + x1) (1 + x2) := heq
    have hme' : Nat.ModEq k (x1 + 1) (x2 + 1) := by
      rw [Nat.add_comm x1 1, Nat.add_comm x2 1]; exact hme
    have hc : x1 % k = x2 % k := Nat.ModEq.add_right_cancel' 1 hme'
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hc
    exact hc
  · intro i x hi hik hxi
    have hxl : x < k := hxl x hxi
    rw [succModIter_p36 k hk hxl i]
    intro heq
    have h1 : (x + i) % k = x % k := by rw [heq, Nat.mod_eq_of_lt hxl]
    have hdvd : k ∣ (x + i) - x := (Nat.modEq_iff_dvd' (by omega)).mp h1.symm
    rw [Nat.add_sub_cancel_left] at hdvd
    exact absurd (Nat.eq_zero_of_dvd_of_lt hdvd (by omega)) (by omega)
  · intro x hx
    have hxlt : x < k := hxl x hx
    show (fun i => (1 + i) % k)^[k] x = x
    rw [succModIter_p36 k hk hxlt k, Nat.add_mod_right, Nat.mod_eq_of_lt hxlt]
  · rw [Nat.card_coe_set_eq, Set.ncard_Iic_nat]
    omega

theorem csAdj_symm_p36 {k : ℕ} {a1 a2 : ℝ} {i j : ℕ} :
    csAdj k a1 a2 i j = csAdj k a1 a2 j i := by
  simp only [csAdj]
  by_cases h1 : i % k = j % k
  · simp [h1]
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    by_cases h2 : (j % k = (i + 1) % k ∨ (j + 1) % k = i % k)
    · have h2' : (i % k = (j + 1) % k ∨ (i + 1) % k = j % k) := by
        rcases h2 with h | h
        · exact Or.inr h.symm
        · exact Or.inl h.symm
      rw [if_pos h2, if_pos h2']
    · have h2' : ¬ (i % k = (j + 1) % k ∨ (i + 1) % k = j % k) := by
        rintro (h | h)
        · exact h2 (Or.inr h.symm)
        · exact h2 (Or.inl h.symm)
      rw [if_neg h2, if_neg h2']

theorem aPro_symm_p36 {k : ℕ} {p a1 a2 : ℝ} {i j : ℕ} :
    aPro k p a1 a2 i j = aPro k p a1 a2 j i := by
  simp only [aPro]
  by_cases h1 : i % k = j % k
  · simp [h1]
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    by_cases h2 : ({i % k, j % k} : Set ℕ) = {0, 1}
    · have h2' : ({j % k, i % k} : Set ℕ) = {0, 1} := by
        rw [← h2]
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      rw [if_pos h2, if_pos h2']
    · have h2' : ¬ ({j % k, i % k} : Set ℕ) = {0, 1} := by
        intro he
        rw [← he] at h2
        exact h2 (by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega)
      rw [if_neg h2, if_neg h2']
      by_cases h3 : (j % k = (i + 1) % k ∨ (j + 1) % k = i % k)
      · have h3' : (i % k = (j + 1) % k ∨ (i + 1) % k = j % k) := by
          rcases h3 with h | h
          · exact Or.inr h.symm
          · exact Or.inl h.symm
        rw [if_pos h3, if_pos h3']
      · have h3' : ¬ (i % k = (j + 1) % k ∨ (i + 1) % k = j % k) := by
          rintro (h | h)
          · exact h3 (Or.inr h.symm)
          · exact h3 (Or.inl h.symm)
        rw [if_neg h3, if_neg h3']

theorem change_type_v2_mkUnadorned_p36 {k : ℕ} (d : ℝ) (a b : ℕ → ℕ → ℝ) :
    change_type_v2 (mkUnadornedV39 k d a b).J k = ∅ := by
  show change_type_v2 (fun _ _ => False) k = ∅
  ext e
  simp [change_type_v2]

/-- `scsJSet_p23` of an unadorned system is empty (`mk_unadorned_v39` has
`J = fun _ _ => False`). -/
theorem scsJSet_mkUnadorned_p36 {k : ℕ} (d : ℝ) (a b : ℕ → ℕ → ℝ) :
    scsJSet_p23 (mkUnadornedV39 k d a b) = ∅ := by
  ext e
  simp only [scsJSet_p23, Set.mem_setOf_eq, Set.mem_empty_iff_false]
  constructor
  · rintro ⟨i, j, -, -, hJ, -⟩
    exact hJ
  · intro h
    exact absurd h (by simp)

/-- HOL `stable_sy ((scs_k_v39 s),(scs_d_v39 s),(0..scs_k_v39 s - 1),
(change_type_v3 (scs_a_v39 s)),(change_type_v3 (scs_b_v39 s)),
(change_type_v2 (scs_J_v39 s) (scs_k_v39 s)),(\i. (1 + i) MOD scs_k_v39 s))`
— the record carried by the `TAUSTAR_EQ_TAU_STAR_*` hypotheses
(XWITCCN.hl:2771-2774 et seq.).

FIDELITY-FIX 2026-09-17: the HOL record's `d` slot is `scs_d_v39 s`
(XWITCCN.hl:2772), NOT `0`.  The earlier rendering via `scsToStableSy_p23`
(which fixes `d := 0`) made every `k ≥ 4` `TAUSTAR_EQ_TAU_STAR_*` false,
since `taustar_v39` subtracts `dsv_v39 = scs_d_v39 s` while
`tau_star s1` subtracted `0 ≠ d_tame k`.

SF-81 案①: the `stable` field is fed from `IS_SCS_STABLE_SYSTEM_p23` via
explicit evidence parameters — the def-body `sorry` placeholder is gone and
the taint is carried by that TRACKED M0 theorem instead. -/
noncomputable def scsToStableSyD_p36 (s : ScsV39) (hs : isScsV39 s)
    (hk : 3 < s.k) : StableSyP23 where
  k := s.k
  d := s.d
  I := Set.Iic (s.k - 1)
  a := s.a
  b := s.b
  J := scsJSet_p23 s
  f := fun i => (1 + i) % s.k
  stable := IS_SCS_STABLE_SYSTEM_p23 s hs hk

/-- `setSum` over the empty set is `0`. -/
private theorem setSum_empty_p36 {α : Type*} (f : α → ℝ) : setSum (∅ : Set α) f = 0 := by
  classical
  rw [setSum, dif_pos (Set.finite_empty : Set.Finite (∅ : Set α))]
  simp

/-- `MATVEC_VECMATS_ID` for `real^3` rows: the `flattenRow_p23` flattening
decodes back to the cyclic row vector. -/
theorem vecmatsV3_flattenRow_p36 {k : ℕ} (vv : ℕ → V3) :
    vecmatsV3_p4 (flattenRow_p23 vv k) = cycRow_p23 vv k := by
  funext j
  have h1 : flattenRow_p23 vv k
      = matvec_p4 (fun j : Fin k => (cycRow_p23 vv k j : Fin 3 → ℝ)) := by
    funext i
    simp only [flattenRow_p23, matvec_p4]
  have h2 : vecmats_p4 (flattenRow_p23 vv k) j = (cycRow_p23 vv k j : Fin 3 → ℝ) := by
    rw [h1, VECMATS_MATVEC_ID]
  show (WithLp.toLp 2 (vecmats_p4 (flattenRow_p23 vv k) j) : V3) = cycRow_p23 vv k j
  rw [h2, WithLp.toLp_ofLp]

/-- The `CONDITION2`-free k = 3 body set of the HOL case machine: HOL
`{matvec v | (!i. 1<=i /\ i <= dimindex(:M) ==> row i v IN ball_annulus) /\
CONDITION1_SY (change_type_v3 (scs_a_v39 s)) (change_type_v3 (scs_b_v39 s))
v}` — verbatim in `IN_NOT_EMPTY_CASE_3` (XWITCCN.hl:1344-1346),
`NOT_EMPTY_CASE_3` (:1383-1384), `IN_B_SY1_COLLINEAR_CASE_3` (:2033-2035)
and `HDPLYGY_CASE_3` (:2101-2116).  Unlike the `k ≥ 4` bodies (rendered by
`B_SY1_p4`), the k = 3 statements carry NO `CONDITION2_SY v` conjunct.

FIDELITY-FIX 2026-09-17: the earlier port stated the k = 3 case machine
over `B_SY1_p4`, injecting a spurious `CONDITION2_SY_p4` conjunct that
`BBsV39` cannot supply at `k = 3` (only the vacuous `s.k ≤ 3` disjunct). -/
def B_SY1_nc2_p36 {m : ℕ} (a b : Fin m → Fin m → ℝ) : Set (FinVec m 3) :=
  (fun v : Fin m → V3 =>
      fun i : Fin (m * 3) =>
        (v ⟨(i : ℕ) / 3, (Nat.div_lt_iff_lt_mul (k := 3) (by norm_num)).mpr i.isLt⟩ :
              Fin 3 → ℝ) ⟨(i : ℕ) % 3, Nat.mod_lt (i : ℕ) (by norm_num : 0 < 3)⟩)
    '' {v | (∀ i : Fin m, v i ∈ ballAnnulus) ∧ CONDITION1_SY_p4 a b v}

/-- Core of the `k ≥ 4` `TAUSTAR_EQ_TAU_STAR_*` family (XWITCCN.hl:2763 et
seq.): with `J = ∅`, `taustar_v39 = tau_fun(...) - scs_d_v39 s` and
`tau_star s1 = tau_fun(...) - d_fun s1` where `d_fun s1 = s1.d` because
`J1_SY s1 = ∅`. -/
private theorem taustar_eq_tauStar_gen_p36 {k : ℕ} (hk3 : ¬(k ≤ 3)) (s : ScsV39)
    (s1 : StableSyP23) (vv : ℕ → V3) (l : FinVec k 3)
    (hJ : s.J = fun _ _ => False) (hk : s.k = k)
    (hVEF : V_SY_p4 (cycRow_p23 vv k) = Set.range vv ∧
      E_SY_p4 (cycRow_p23 vv k) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
      F_SY_p4 (cycRow_p23 vv k) = Set.range (fun i : ℕ => (vv i, vv (i + 1))))
    (hsS : isScsV39 s) (h3k : 3 < s.k)
    (hs1 : s1 = scsToStableSyD_p36 s hsS h3k) (hl : flattenRow_p23 vv k = l) :
    taustarV39 s vv = tauStar_p23 s1 l := by
  subst hs1
  subst hl
  obtain ⟨hV, hE, hF⟩ := hVEF
  have hn3 : ¬(s.k ≤ 3) := by omega
  have hvb : vecmatsV3_p4 (flattenRow_p23 vv k) = cycRow_p23 vv k :=
    vecmatsV3_flattenRow_p36 vv
  have hJs : (scsToStableSyD_p36 s hsS h3k).J = (∅ : Set (Set ℕ)) := by
    show scsJSet_p23 s = ∅
    ext e
    simp only [scsJSet_p23, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    constructor
    · rintro ⟨i, j, -, -, hJm, -⟩
      rw [hJ] at hJm
      exact hJm
    · intro h
      exact absurd h (by simp)
  have hJ1 : J1_SY_p23 (scsToStableSyD_p36 s hsS h3k) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    simp only [J1_SY_p23, Set.mem_setOf_eq] at hx
    obtain ⟨i, hm, -, -⟩ := hx
    rw [hJs] at hm
    exact absurd hm (by simp)
  unfold taustarV39
  rw [if_neg hn3, dsv_J_empty s vv hJ]
  unfold tauStar_p23 dFun_p23
  rw [hvb, hV, hE, hF, hJ1, setSum_empty_p36, mul_zero, add_zero]
  rfl


/-! ## Section 0.6: the registry-`ConvexLocalFan` ↔ `convexLocalFan_p4`
def-bridge (AzimBridge-fuelled).  Under `Fan.FAN x V E` the LA4 `hyp_p4 x V E`
IS the instProd-baked `Fan.hypermapOfFan x V E` (`hyp_p4`'s `Hypermap (V3 × V3)`
instance, pinned in LocalAuto4, is Mathlib's `instDecidableEqProd` — LA4
does not import LocalAuto3's `dartDecEq3`), so `face_p4`/`dih2k_p4`/
`localFan_p4` are pointwise-convertible to the LA1 registry data with NO
instance clash, and the azim/wedge renderings merge through the AzimBridge
§4 FAN-conditional bridges plus the `azimCycle_p4`/`EE_p4` = `_p3` rfl-twins.
All `Hypermap` projections are written `@`-explicitly (AzimBridge §0 note):
dot-projections of instProd-typed terms would synthesize `dartDecEq3` here. -/

/-- `face_p4` is the faceMap orbit on the dart set (pure `Hypermap`
conversion at the instProd instance; `hypermap.hl` `face`). -/
theorem face_p4_eq_orbitMap_p36
    (H : @Hypermap (V3 × V3) (fun a b => instDecidableEqProd a b)) (p : V3 × V3)
    (hp : p ∈ (@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b) H :
      Finset (V3 × V3))) :
    face_p4 H p = orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b) H) p := by
  unfold face_p4 orbitMap
  ext y
  constructor
  · rintro ⟨hy, n, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨?_, n, hn⟩
    have h2 := (@Hypermap.faceMap_permutes (V3 × V3) (fun a b => instDecidableEqProd a b)
      H).pow_apply_mem n hp
    rw [← hn]
    exact Finset.mem_coe.mp h2

/-- The faceMap orbit of a dart stays in the dart set (`PermutesOn.pow_apply_mem`). -/
theorem orbit_mem_darts_p36
    (H : @Hypermap (V3 × V3) (fun a b => instDecidableEqProd a b)) (p q : V3 × V3)
    (hp : p ∈ (@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b) H :
      Finset (V3 × V3)))
    (hq : q ∈ orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b) H) p) :
    q ∈ ((@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b) H :
      Finset (V3 × V3)) : Set (V3 × V3)) := by
  simp only [orbitMap, Set.mem_setOf_eq] at hq
  obtain ⟨n, hn⟩ := hq
  have h2 := (@Hypermap.faceMap_permutes (V3 × V3) (fun a b => instDecidableEqProd a b)
    H).pow_apply_mem n hp
  rw [hn] at h2
  exact Finset.mem_coe.mp h2

/-- LA4's `dih2k_p4` and LA1's `Dih2k` are the same data at the instProd
instance (orders via AzimBridge `hasOrders_iff_hasOrders_p4`). -/
theorem dih2k_p4_iff_Dih2k_p36 (H : @Hypermap (V3 × V3) (fun a b => instDecidableEqProd a b))
    (k : ℕ) : dih2k_p4 H k ↔ @Dih2k (V3 × V3) (fun a b => instDecidableEqProd a b) H k := by
  constructor
  · rintro ⟨hcard, horb, hof, hoe, hon⟩
    refine ⟨hcard, ?_, (@hasOrders_iff_hasOrders_p4 (V3 × V3)
        (fun a b => instDecidableEqProd a b) _ _).mpr hof,
      (@hasOrders_iff_hasOrders_p4 (V3 × V3) (fun a b => instDecidableEqProd a b) _ _).mpr hoe,
      (@hasOrders_iff_hasOrders_p4 (V3 × V3) (fun a b => instDecidableEqProd a b) _ _).mpr hon⟩
    intro d hd
    have h2 : ((@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b) H :
          Finset (V3 × V3)) : Set (V3 × V3)) = face_p4 H d ∪
        (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b) H :
          V3 × V3 → V3 × V3) '' face_p4 H d := horb d hd
    rw [face_p4_eq_orbitMap_p36 H d hd] at h2
    exact h2.symm
  · rintro ⟨hcard, horb, hof, hoe, hon⟩
    refine ⟨hcard, ?_, (@hasOrders_iff_hasOrders_p4 (V3 × V3)
        (fun a b => instDecidableEqProd a b) _ _).mp hof,
      (@hasOrders_iff_hasOrders_p4 (V3 × V3) (fun a b => instDecidableEqProd a b) _ _).mp hoe,
      (@hasOrders_iff_hasOrders_p4 (V3 × V3) (fun a b => instDecidableEqProd a b) _ _).mp hon⟩
    intro p hp
    rw [face_p4_eq_orbitMap_p36 H p hp]
    exact (horb p hp).symm

/-- Under `Fan.FAN x V E` the LA4 junk-dite `hyp_p4` picks the fan hypermap. -/
theorem hyp_p4_of_fan_p36 {x : V3} {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN x V E) :
    hyp_p4 x V E = Fan.hypermapOfFan x V E hfan := by
  unfold hyp_p4
  exact dif_pos hfan

/-- Registry → `_p4`: LA1's `LocalFan` gives LA4's `localFan_p4`. -/
theorem localFan_p4_of_LocalFan_p36 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) : localFan_p4 V E FF := by
  -- α2: the trailing ψ slot is bound by NAME (a `-` pattern here makes rcases
  -- whnf-unfold `Dih2k` and mis-bind `hD`, cf. the AzimBridge §6 note).
  obtain ⟨hfan, x, hx, hFF, hD, htwo⟩ := h
  clear htwo
  have hhp := hyp_p4_of_fan_p36 hfan
  refine ⟨hfan, ⟨x, ?_, ?_⟩, ?_⟩
  · rw [hhp]; exact hx
  · rw [hhp, hFF, face_p4_eq_orbitMap_p36 (Fan.hypermapOfFan 0 V E hfan) x hx]
  · rw [hhp]
    exact (dih2k_p4_iff_Dih2k_p36 (Fan.hypermapOfFan 0 V E hfan) FF.ncard).mpr hD

/-! **α2-W2 resolution (lf-alpha-w2)**: the α2 `LocalFan` conjunct
`∀ u ∈ V, (ee u E).ncard = 2` is NOT closable from `_p4` data alone — under
`FAN`, `hyp_p4` is `hypermapOfFan` (`hyp_p4_of_fan_p36`), whose dart layer
carries no self-pairs, so isolated vertices are invisible to `localFan_p4`
(lf-alpha-w1 counterexample: triangle + isolated point satisfies every
`_p4` condition while ψ fails at the isolated point).  Solution (a) of the
w1 BLOCKER note: add the premise `V ⊆ ⋃₀ E`, which (with `FAN`'s
`⋃₀ E ⊆ V` conjunct and `Graph E`) gives the no-isolated form
`∀ v ∈ V, ∃ w, {v, w} ∈ E` and closes ψ through the AzimBridge core lemma. -/

/-- No-isolated in its natural form from `V ⊆ ⋃₀ E`: `hsub` gives an edge
through each `v ∈ V`, and `Graph E` (a `FAN` conjunct: every edge is a
2-element set) makes that edge literally `{v, w}`. -/
theorem noIsolated_of_hsub_p36 {V : Set V3} {E : Set (Set V3)}
    (hfan : Fan.FAN 0 V E) (hsub : V ⊆ ⋃₀ E) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  intro v hv
  obtain ⟨e, heE, hev⟩ := Set.mem_sUnion.mp (hsub hv)
  obtain ⟨hfin, h2⟩ := hfan.2.1 e heE
  have hw : ∃ w ∈ hfin.toFinset, w ≠ v := by
    by_contra hcon
    push_neg at hcon
    have hle : hfin.toFinset.card ≤ 1 :=
      (Finset.card_le_card (fun x hx => Finset.mem_singleton.mpr (hcon x hx))).trans
        (Finset.card_singleton v).le
    omega
  obtain ⟨w, hws, hwv⟩ := hw
  have hwe : w ∈ e := hfin.mem_toFinset.mp hws
  have hsubVW : ({v, w} : Set V3) ⊆ e := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hev
    · rw [Set.mem_singleton_iff.mp hx]; exact hwe
  have hncVW : ({v, w} : Set V3).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem (a := v) (s := {w})
      (fun hm => hwv (Set.mem_singleton_iff.mp hm).symm), Set.ncard_singleton]
  have hncE : e.ncard = 2 := by
    rw [← hfin.coe_toFinset, Set.ncard_coe_finset]
    omega
  have hEq : ({v, w} : Set V3) = e :=
    Set.eq_of_subset_of_ncard_le hsubVW (by omega) hfin
  refine ⟨w, ?_⟩
  rw [hEq]
  exact heE

/-- **W2 helper**: LA4's `localFan_p4` assembles the packaged `localFan_p3`
provided no vertex of `V` is isolated.  The witness hypermap is the HYP
hypermap of the fan (`exists_hypHyp_of_fan`), whose components are the raw
of-hyp maps by construction; the dart layer matches through
`hno_of_no_isolated` (fed by `noIsolated_of_hsub_p36`), and LA1's `Dih2k`
(at the instProd-baked `hypermapOfFan`, reached from `dih2k_p4` by
`dih2k_p4_iff_Dih2k_p36`) transports to `dih2k_p3` conjunct by conjunct —
the mirror of AzimBridge's `LocalFan.of_localFan_p3` transport. -/
theorem localFan_p3_of_localFan_p4_p36 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p4 V E FF) (hsub : V ⊆ ⋃₀ E) : localFan_p3 V E FF := by
  obtain ⟨hfan, ⟨p, hp, hFF⟩, hD⟩ := h
  have hhp := hyp_p4_of_fan_p36 hfan
  have hedge := noIsolated_of_hsub_p36 hfan hsub
  have hno := hno_of_no_isolated hedge
  obtain ⟨H, hdarts, hedgeF, hnodeF, hfaceF⟩ := exists_hypHyp_of_fan hfan
  have hDartF : @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan) = H.darts :=
    Finset.coe_injective ((dartsLA1 0 V E hfan).trans (hno.symm.trans hdarts.symm))
  have hm : p ∈ (@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan) : Finset (V3 × V3)) := by
    rw [← hhp]; exact hp
  have hcoF : (H.faceMap : V3 × V3 → V3 × V3) =
      ⇑(@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (Fan.hypermapOfFan 0 V E hfan)) := hfaceF.trans (ffOfHyp_p3_eq_faceMapLA1_fun hfan)
  have hcoN : (H.nodeMap : V3 × V3 → V3 × V3) =
      ⇑(@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (Fan.hypermapOfFan 0 V E hfan)) := hnodeF.trans (nnOfHyp_p3_eq_nodeMapLA1_fun hfan)
  have hcoE : (H.edgeMap : V3 × V3 → V3 × V3) =
      ⇑(@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (Fan.hypermapOfFan 0 V E hfan)) := hedgeF.trans (eeOfHyp_p3_eq_edgeMapLA1_fun hfan)
  rw [hhp] at hFF hD
  have heq : FF = orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan)) p := by
    rw [hFF]
    exact face_p4_eq_orbitMap_p36 (Fan.hypermapOfFan 0 V E hfan) p hm
  have hd : @Dih2k (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan) FF.ncard :=
    (dih2k_p4_iff_Dih2k_p36 (Fan.hypermapOfFan 0 V E hfan) FF.ncard).mp hD
  -- the `localFan_p3` face-orbit congruence (mirror of
  -- `LocalFan.of_localFan_p3`'s `hfaceOrb`)
  have hfaceOrb : ∀ y : V3 × V3, H.face y = orbitF_p3 (ffOfHyp_p3 0 V E) y := by
    intro y
    show orbitMap H.faceMap y = orbitF_p3 (ffOfHyp_p3 0 V E) y
    unfold orbitMap orbitF_p3
    ext z
    simp only [Equiv.Perm.coe_pow, hfaceF]
  have hpD : p ∈ (↑H.darts : Set (V3 × V3)) := by
    rw [hdarts, hno, ← dartsLA1 0 V E hfan]
    exact Finset.mem_coe.mp hm
  refine ⟨H, hdarts, hedgeF, hnodeF, hfaceF, hfan, ⟨p, Finset.mem_coe.mpr hpD, ?_⟩, ?_⟩
  · rw [heq, orbitMap_LA1faceMap_eq_orbitF hfan p]
    exact (hfaceOrb p).symm
  -- `dih2k_p3 H FF.ncard`: conjunct-by-conjunct transport of `hd`
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hDartF]; exact hd.1
  · intro d hdD
    have hdD' : d ∈ @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
        (Fan.hypermapOfFan 0 V E hfan) := by rw [hDartF]; exact hdD
    have hb := hd.2.1 d hdD'
    rw [hDartF] at hb
    show (↑H.darts : Set (V3 × V3)) = orbitMap H.faceMap d ∪
      (H.nodeMap : V3 × V3 → V3 × V3) '' orbitMap H.faceMap d
    rw [orbitMap_congr hcoF d, hcoN]
    exact hb.symm
  · rw [hcoF]; exact (hasOrders_iff_hasOrders_p4 _ _).mp hd.2.2.1
  · rw [hcoE]; exact (hasOrders_iff_hasOrders_p4 _ _).mp hd.2.2.2.1
  · rw [hcoN]; exact (hasOrders_iff_hasOrders_p4 _ _).mp hd.2.2.2.2

/-- `_p4` → registry: LA4's `localFan_p4` gives LA1's `LocalFan`.  The α2
2-regularity conjunct rides on the AzimBridge receipt `localFanEquiv_p35`
via the W2 helper above; the added premise `hsub : V ⊆ ⋃₀ E` is exactly the
no-isolated input the `_p4` dart layer cannot see (see the α2-W2 resolution
note above).  Conclusion shape frozen (lf-alpha-w1 α2); only the premise is
added. -/
theorem LocalFan_of_localFan_p4_p36 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p4 V E FF) (hsub : V ⊆ ⋃₀ E) : LocalFan V E FF :=
  localFanEquiv_p35.mpr (localFan_p3_of_localFan_p4_p36 h hsub)

/-- The `azim_in_fan` renderings merge on fan darts: `azimInFan_p4` =
`azimInFan_p3` (rfl) and the sigmaFan-vs-azimCycle bodies merge through the
AzimBridge §4 bridge. -/
theorem azimInFan_p4_eq_azimInFan_p36 {V : Set V3} {E : Set (Set V3)}
    (hfan : Fan.FAN 0 V E) {d : V3 × V3} (hd : d ∈ Fan.dart1OfFan V E) :
    azimInFan_p4 d E = azimInFan d E := by
  rw [show azimInFan_p4 d E = azimInFan_p3 d E from rfl,
    azimInFan_eq_azimInFan_p3 hfan hd]

/-- The matching `wedge_in_fan_ge` merge. -/
theorem wedgeInFanGe_p4_eq_wedgeInFanGe_p36 {V : Set V3} {E : Set (Set V3)}
    (hfan : Fan.FAN 0 V E) {d : V3 × V3} (hd : d ∈ Fan.dart1OfFan V E) :
    wedgeInFanGe_p4 d E = wedgeInFanGe d E := by
  rw [show wedgeInFanGe_p4 d E = wedgeInFanGe_p3 d E from rfl,
    wedgeInFanGe_eq_wedgeInFanGe_p3 hfan hd]

/-- **MASTER (registry → `_p4`)**: the LA1 `ConvexLocalFan` gives LA4's
`convexLocalFan_p4` verbatim (the fan conjunct of `BBsV39 s vv` yields the
`CONDITION2_SY_p4` conjunct of `B_SY1_p4`). -/
theorem convexLocalFan_p4_of_ConvexLocalFan_p36 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : ConvexLocalFan V E FF) : convexLocalFan_p4 V E FF := by
  obtain ⟨hl, haw⟩ := h
  have hlf : LocalFan V E FF := hl
  obtain ⟨hfan, x0, hx0, hFF, hD0, htwo⟩ := hl
  clear hD0 htwo
  refine ⟨localFan_p4_of_LocalFan_p36 hlf, ?_⟩
  intro x hxFF
  have hdart : x ∈ Fan.dart1OfFan V E := by
    have h1 : x ∈ orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (Fan.hypermapOfFan 0 V E hfan)) x0 := by rwa [hFF] at hxFF
    have h2 := orbit_mem_darts_p36 (Fan.hypermapOfFan 0 V E hfan) x0 x hx0 h1
    rw [dartsLA1 0 V E hfan] at h2
    exact h2
  exact ⟨by rw [azimInFan_p4_eq_azimInFan_p36 hfan hdart]; exact (haw x hxFF).1,
    by rw [wedgeInFanGe_p4_eq_wedgeInFanGe_p36 hfan hdart]; exact (haw x hxFF).2⟩

/-- **MASTER (`_p4` → registry)**: the converse direction (used by the
`IN_NOT_EMPTY_B1_SY_*` row-decoding twins to lift `CONDITION2_SY_p4` to the
`BBsV39` fan conjunct). -/
theorem ConvexLocalFan_of_convexLocalFan_p4_p36 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : convexLocalFan_p4 V E FF) (hsub : V ⊆ ⋃₀ E) :
    ConvexLocalFan V E FF := by
  obtain ⟨hl, haw⟩ := h
  have hlf : localFan_p4 V E FF := hl
  obtain ⟨hfan, ⟨p, hp, hFF⟩, hD⟩ := hl
  have hhp := hyp_p4_of_fan_p36 hfan
  have hm : p ∈ (@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan) : Finset (V3 × V3)) := by
    rw [← hhp]; exact hp
  have hFF' : FF = orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan)) p := by
    rw [hhp] at hFF
    rw [hFF, face_p4_eq_orbitMap_p36 (Fan.hypermapOfFan 0 V E hfan) p hm]
  refine ⟨LocalFan_of_localFan_p4_p36 hlf hsub, ?_⟩
  intro x hxFF
  have hdart : x ∈ Fan.dart1OfFan V E := by
    rw [hFF'] at hxFF
    have h2 := orbit_mem_darts_p36 (Fan.hypermapOfFan 0 V E hfan) p x hm hxFF
    rw [dartsLA1 0 V E hfan] at h2
    exact h2
  exact ⟨by rw [← azimInFan_p4_eq_azimInFan_p36 hfan hdart]; exact (haw x hxFF).1,
    by rw [← wedgeInFanGe_p4_eq_wedgeInFanGe_p36 hfan hdart]; exact (haw x hxFF).2⟩

/-! ## Section 0.7: the generic k ≥ 4 `B_SY1_p4` cores.  CONDITION1 needs no
table ladder at all: the `_p4` body tables are `change_type_v3 s.a (i+1, j+1)`
and the `BBsV39` a/b conjunct is exactly that bound at the periodic rows. -/

/-- Generic core of the k ≥ 4 `IN_NOT_EMPTY_CASE_*` family: `BBsV39 s vv` at
`s.k = k ≥ 4` puts the flattening of the cyclic rows in `B_SY1_p4` (the
`CONDITION2` conjunct via the Section 0.6 bridge). -/
theorem inNotEmpty_core_p36 {k : ℕ} (hk : 4 ≤ k) {s : ScsV39} {vv : ℕ → V3}
    (hksk : s.k = k) (hBB : BBsV39 s vv) :
    flattenRow_p23 vv k ∈ B_SY1_p4
      (fun (i j : Fin k) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin k) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
  have hper : Periodic vv k := by rw [← hksk]; exact hBB.2.1
  have hconv : ConvexLocalFan (Set.range vv)
      (Set.range fun i : ℕ => {vv i, vv (i + 1)})
      (Set.range fun i : ℕ => (vv i, vv (i + 1))) := by
    rcases hBB.2.2.2 with h3 | hc
    · have h3k : k ≤ 3 := hksk ▸ h3
      omega
    · exact hc
  refine ⟨cycRow_p23 vv k, ⟨?_, ?_, ?_⟩, rfl⟩
  · intro i
    show vv (((i : ℕ) + 1) % k) ∈ ballAnnulus
    rw [periodic_mod_eq_p23 hper ((i : ℕ) + 1)]
    exact hBB.1 (Set.mem_range_self ((i : ℕ) + 1))
  · intro i j
    have e1 : cycRow_p23 vv k i = vv ((i : ℕ) + 1) :=
      periodic_mod_eq_p23 hper ((i : ℕ) + 1)
    have e2 : cycRow_p23 vv k j = vv ((j : ℕ) + 1) :=
      periodic_mod_eq_p23 hper ((j : ℕ) + 1)
    have hb := hBB.2.2.1 ((i : ℕ) + 1) ((j : ℕ) + 1)
    rw [dist_eq_norm] at hb
    simp only [change_type_v3]
    rw [e1, e2]
    exact hb
  · show convexLocalFan_p4 (V_SY_p4 (cycRow_p23 vv k)) (E_SY_p4 (cycRow_p23 vv k))
      (F_SY_p4 (cycRow_p23 vv k))
    rw [vSy_eq_range_p36 (by omega) hper, eSy_eq_range_p36 (by omega) hper,
      fSy_eq_range_p36 (by omega) hper]
    exact convexLocalFan_p4_of_ConvexLocalFan_p36 hconv

/-- Generic core of the k ≥ 4 `IN_NOT_EMPTY_B1_SY_*` twins: the body
conditions on the cyclic rows decode back to `BBsV39 s vv` (the fan
conjunct via the converse Section 0.6 bridge).  `hmod` is the residue
periodicity of the value tables — in HOL discharged by `EXPAND_TAC s`
(the concrete `cs_adj`/`a_pro` ladders); here instantiate it with the
proved `SCS_A_B__EQ_MOD_k` twins. -/
theorem inB1_core_p36 {k : ℕ} (hk : 4 ≤ k) {s : ScsV39} {vv : ℕ → V3}
    (hksk : s.k = k) (hper : Periodic vv k)
    (hmod : ∀ i j : ℕ, s.a i j = s.a (i % k) (j % k) ∧ s.b i j = s.b (i % k) (j % k))
    (hball : ∀ i : Fin k, cycRow_p23 vv k i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun (i j : Fin k) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin k) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      (cycRow_p23 vv k))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv k)) :
    BBsV39 s vv := by
  -- α2-W2: the vv-world `V ⊆ ⋃₀ E` for the converse fan bridge — a periodic
  -- row puts every vertex on a cyclic edge (`k ≥ 1` suffices).  Stated in the
  -- `V_SY_p4`/`E_SY_p4` world to match the rewritten goal below.
  have hvsub : V_SY_p4 (cycRow_p23 vv k) ⊆ ⋃₀ E_SY_p4 (cycRow_p23 vv k) := by
    rw [vSy_eq_range_p36 (by omega) hper, eSy_eq_range_p36 (by omega) hper]
    rintro y ⟨n, rfl⟩
    exact Set.mem_sUnion_of_mem
      (Set.mem_insert_iff.mpr (Or.inl (periodic_mod_eq_p23 hper n).symm))
      (Set.mem_range_self (n % k))
  have hc : ConvexLocalFan (Set.range vv)
      (Set.range fun i : ℕ => {vv i, vv (i + 1)})
      (Set.range fun i : ℕ => (vv i, vv (i + 1))) := by
    rw [← vSy_eq_range_p36 (by omega) hper, ← eSy_eq_range_p36 (by omega) hper,
      ← fSy_eq_range_p36 (by omega) hper]
    exact ConvexLocalFan_of_convexLocalFan_p4_p36 hC2 hvsub
  refine ⟨?_, by rw [hksk]; exact hper, ?_, Or.inr hc⟩
  · rintro y ⟨n, rfl⟩
    have hrow : cycRow_p23 vv k ⟨(n % k + k - 1) % k, Nat.mod_lt _ (by omega)⟩
        = vv (n % k) := by
      show vv ((((n % k + k - 1) % k + 1) % k : ℕ)) = vv (n % k)
      rw [modShift_p36 k (n % k) (Nat.mod_lt n (by omega)), Nat.mod_mod]
    rw [← periodic_mod_eq_p23 hper n, ← hrow]
    exact hball _
  · intro i j
    have hik : i % k < k := Nat.mod_lt i (by omega)
    have hjk : j % k < k := Nat.mod_lt j (by omega)
    have hik' : (i % k + k - 1) % k < k := Nat.mod_lt _ (by omega)
    have hjk' : (j % k + k - 1) % k < k := Nat.mod_lt _ (by omega)
    have hi : cycRow_p23 vv k ⟨(i % k + k - 1) % k, hik'⟩ = vv (i % k) := by
      show vv ((((i % k + k - 1) % k + 1) % k : ℕ)) = vv (i % k)
      rw [modShift_p36 k (i % k) hik, Nat.mod_mod]
    have hj : cycRow_p23 vv k ⟨(j % k + k - 1) % k, hjk'⟩ = vv (j % k) := by
      show vv ((((j % k + k - 1) % k + 1) % k : ℕ)) = vv (j % k)
      rw [modShift_p36 k (j % k) hjk, Nat.mod_mod]
    have hb := hC1 ⟨(i % k + k - 1) % k, hik'⟩ ⟨(j % k + k - 1) % k, hjk'⟩
    simp only [change_type_v3] at hb
    rw [hi, hj] at hb
    have hii : ((i % k + k - 1) % k + 1) % k = i % k := by
      rw [modShift_p36 k (i % k) hik, Nat.mod_mod]
    have hjj : ((j % k + k - 1) % k + 1) % k = j % k := by
      rw [modShift_p36 k (j % k) hjk, Nat.mod_mod]
    rw [(hmod i j).1, (hmod i j).2, ← periodic_mod_eq_p23 hper i,
      ← periodic_mod_eq_p23 hper j, dist_eq_norm]
    have hb1 := hb.1
    have hb2 := hb.2
    rw [(hmod ((i % k + k - 1) % k + 1) ((j % k + k - 1) % k + 1)).1, hii, hjj] at hb1
    rw [(hmod ((i % k + k - 1) % k + 1) ((j % k + k - 1) % k + 1)).2, hii, hjj] at hb2
    exact ⟨hb1, hb2⟩




end X36

open X36

/-! ## Part 2: the `sInitListV39` `isScs` substrate (LocalAuto22 certificates,
LocalAuto20 `SCS_5I3`/`init8` proofs, LocalAuto27 `s_init_scs` table identities) -/

/-- HOL `sqrt8_LE_6_xw6` (hexagons.hl:189). -/
theorem sqrt8_LE_6_xw6 : Real.sqrt 8 ≤ 6 :=
  le_trans (Real.sqrt_le_sqrt (by norm_num : (8:ℝ) ≤ 36)) (by norm_num)

/-- HOL `sqrt8_LE_CSTAB_xw6` (hexagons.hl:194). -/
theorem sqrt8_LE_CSTAB_xw6 : Real.sqrt 8 ≤ cstab :=
  le_trans (Real.sqrt_le_sqrt (by norm_num : (8:ℝ) ≤ 9)) (by norm_num [cstab])

/-- HOL `LE_sqrt8_2_xw6` (hexagons.hl:200). -/
theorem LE_sqrt8_2_xw6 : (2 : ℝ) ≤ Real.sqrt 8 :=
  (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)

/-- HOL `LE_sqrt8_2h0_xw6` (hexagons.hl:205). -/
theorem LE_sqrt8_2h0_xw6 : 2 * h0 ≤ Real.sqrt 8 :=
  (Real.le_sqrt (by norm_num [h0]) (by norm_num)).2 (by norm_num [h0])

/-- HOL `LT_sqrt8_2h0_xw6` (hexagons.hl:211). -/
theorem LT_sqrt8_2h0_xw6 : 2 * h0 < Real.sqrt 8 :=
  Real.lt_sqrt_of_sq_lt (by norm_num [h0] : (2 * h0) ^ 2 < 8)


theorem two_lt_two_h0_p20_xw6 : (2 : ℝ) < 2 * h0 := by norm_num [h0]


/-- Numeric strict facts for the M-row edge sets. -/
theorem two_h0_lt_cstab_p20_xw6 : 2 * h0 < cstab := by norm_num [h0, cstab]

/-- `funlistV39` tables only read residues: `(i % k, j % k)` entry equals the
`(i, j)` entry (hexagons.hl `PSORT_MOD` applied to the whole table). -/
theorem funlist_mod_p20_xw6 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k i j : ℕ)
    (_hk : k ≠ 0) :
    funlistV39 data d k (i % k) (j % k) = funlistV39 data d k i j := by
  simp only [funlistV39, psort, Nat.mod_mod]

/-- `funlistV39` tables are 2-periodic in `k` (hexagons.hl `PSORT_3456_PERIODIC`). -/
theorem periodic2_funlist_p20_xw6 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k : ℕ) :
    Periodic2 (funlistV39 data d k) k := by
  intro i j
  simp [funlistV39, psort, Nat.add_mod_right]

/-- The strict `2 < 2*h0` edge fact. -/
theorem two_lt_two_h0'_xw6 : (2 : ℝ) < 2 * h0 := two_lt_two_h0_p20_xw6


/-- HOL `SCS_5I3_IS_SCS_xw6` (hexagons.hl:565). Direct `is_scs_v39` verification of
the funlist tables (the strict `2*h0 < sqrt8` edge fact enters the card bound). -/
theorem SCS_5I3_IS_SCS_xw6 : isScsV39 scs5I3 := by
  unfold isScsV39 scs5I3 mkUnadornedV39
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
        ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5) 5 :=
    periodic2_funlist_p20_xw6 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
        ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5) 5 :=
    periodic2_funlist_p20_xw6 _ _ _
  refine ⟨by norm_num, by norm_num, by norm_num, periodic_empty 5, periodic_empty 5,
    periodic_empty 5, periodic_empty 5, pa, pa, pb, pb,
    fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ hj => False.elim hj,
    fun _ _ hj => False.elim hj, ?_⟩
  · intro i j
    simp only [funlistV39, psort]
    have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
    interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39]
  · intro i j
    simp only [funlistV39, psort]
    refine ⟨le_refl _, ?_, le_refl _⟩
    have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
    interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39] <;>
      first | exact LE_sqrt8_2h0_xw6 | norm_num [h0, cstab]
  · intro i; simp [funlistV39]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39] <;>
      first | norm_num [h0, cstab] | exact LE_sqrt8_2_xw6
  · intro i hk3
    omega
  · intro i hk5
    rw [← funlist_mod_p20_xw6 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
        ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) (by omega),
      ← Nat.mod_add_mod i 5 1]
    have hz : i % 5 < 5 := Nat.mod_lt i (by omega)
    interval_cases i % 5 <;> simp [funlistV39, psort, assocdV39] <;>
      first | exact sqrt8_LE_CSTAB_xw6 | norm_num [h0, cstab]
  · have key : ∀ r : ℕ, r < 5 →
        ((2 * h0 < funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
              ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 r ((r + 1) % 5) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
              ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5
              r ((r + 1) % 5)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, two_h0_lt_cstab_p20_xw6, two_lt_two_h0'_xw6,
          LT_sqrt8_2h0_xw6] <;> norm_num [h0, cstab]
    have hS : {i | i < 5 ∧ (2 * h0 < funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6),
              ((0, 3), 6), ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5
              i (i + 1) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
              ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5
              i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← funlist_mod_p20_xw6 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
          ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) (by omega),
        ← funlist_mod_p20_xw6 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
          ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 i (i + 1)
          (by omega), ← Nat.mod_add_mod i 5 1]
      rw [key (i % 5) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    simp
    all_goals norm_num

/-- `{a, b} = {0, 1}` (a set of two naturals) iff one is `0` and the other
`1`; rewrites the `{i, j} = {0, 1}` guards of the raw `a_pro` lambdas in
`sInitListV39` into arithmetic for `simp`. -/
@[simp]
theorem init_pair_01_xw6 (a b : ℕ) : ({a, b} : Set ℕ) = {0, 1} ↔
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  constructor
  · intro h
    have ha : a = 0 ∨ a = 1 := by
      have : a ∈ ({0, 1} : Set ℕ) := by rw [← h]; simp
      simpa using this
    have hb : b = 0 ∨ b = 1 := by
      have : b ∈ ({0, 1} : Set ℕ) := by rw [← h]; simp
      simpa using this
    rcases ha with ha0 | ha1
    · rcases hb with hb0 | hb1
      · exfalso
        have : (1 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
        have hc : (1 : ℕ) = a ∨ (1 : ℕ) = b := by simpa using this
        omega
      · left; exact ⟨ha0, hb1⟩
    · rcases hb with hb0 | hb1
      · right; exact ⟨ha1, hb0⟩
      · exfalso
        have : (0 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
        have hc : (0 : ℕ) = a ∨ (0 : ℕ) = b := by simpa using this
        omega
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals ext x
    all_goals simp
    all_goals omega

/-- The sInit entry-7 a-field: the inlined `a_pro` lambda (k = 5) equals the
`funlistV39` table of `scs5I3` (its a-value `2` = the `d` default). -/
theorem init7a_xw6 :
    (fun i j =>
      if i % 5 = j % 5 then 0
      else if ({i % 5, j % 5} : Set ℕ) = {0, 1} then 2 * h0
      else if j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5 then 2 else 2 * h0) =
      funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
        ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 := by
  funext i j
  have hi : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hj : j % 5 < 5 := Nat.mod_lt j (by omega)
  rw [← Nat.mod_add_mod i 5 1]
  rw [← Nat.mod_add_mod j 5 1]
  simp only [funlistV39, psort]
  interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39]

theorem init7b_xw6 :
    (fun i j =>
      if i % 5 = j % 5 then 0
      else if ({i % 5, j % 5} : Set ℕ) = {0, 1} then Real.sqrt 8
      else if j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5 then 2 * h0 else 6) =
      funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
        ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 := by
  funext i j
  have hi : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hj : j % 5 < 5 := Nat.mod_lt j (by omega)
  rw [← Nat.mod_add_mod i 5 1]
  rw [← Nat.mod_add_mod j 5 1]
  simp only [funlistV39, psort]
  interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39]

theorem init8a_xw6 :
    (fun i j =>
      if i % 4 = j % 4 then 0
      else if ({i % 4, j % 4} : Set ℕ) = {0, 1} then 2 * h0
      else if j % 4 = (i + 1) % 4 ∨ (j + 1) % 4 = i % 4 then 2 else Real.sqrt 8) =
      funlistV39 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)] 2 4 := by
  funext i j
  have hi : i % 4 < 4 := Nat.mod_lt i (by omega)
  have hj : j % 4 < 4 := Nat.mod_lt j (by omega)
  rw [← Nat.mod_add_mod i 4 1]
  rw [← Nat.mod_add_mod j 4 1]
  simp only [funlistV39, psort]
  interval_cases i % 4 <;> interval_cases j % 4 <;> simp [assocdV39]

theorem init8b_xw6 :
    (fun i j =>
      if i % 4 = j % 4 then 0
      else if ({i % 4, j % 4} : Set ℕ) = {0, 1} then Real.sqrt 8
      else if j % 4 = (i + 1) % 4 ∨ (j + 1) % 4 = i % 4 then 2 * h0 else 6) =
      funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4 := by
  funext i j
  have hi : i % 4 < 4 := Nat.mod_lt i (by omega)
  have hj : j % 4 < 4 := Nat.mod_lt j (by omega)
  rw [← Nat.mod_add_mod i 4 1]
  rw [← Nat.mod_add_mod j 4 1]
  simp only [funlistV39, psort]
  interval_cases i % 4 <;> interval_cases j % 4 <;> simp [assocdV39]

/-- `isScsV39 scs4I3` (the sInit entry-8 system, k = 4). Built directly over
`periodic2_funlist_p20_xw6`; the mod-step arithmetic and the `√8` bounds use only
LocalAuto20 kit (`LE_sqrt8_2_xw6`, `sqrt8_LE_6_xw6`, `LE_sqrt8_2h0_xw6`, `LT_sqrt8_2h0_xw6`,
`sqrt8_LE_CSTAB_xw6`, `two_lt_two_h0'_xw6`, `two_h0_lt_cstab_p20_xw6`). -/
theorem init8_isScs_xw6 : isScsV39 scs4I3 := by
  unfold isScsV39 scs4I3 mkUnadornedV39
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8),
        ((1, 3), Real.sqrt 8)] 2 4) 4 := periodic2_funlist_p20_xw6 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)]
        (2 * h0) 4) 4 := periodic2_funlist_p20_xw6 _ _ _
  refine ⟨by norm_num, by norm_num, by norm_num, periodic_empty 4, periodic_empty 4,
    periodic_empty 4, periodic_empty 4, pa, pa, pb, pb,
    fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ hj => False.elim hj,
    fun _ _ hj => False.elim hj, ?_⟩
  · intro i j
    simp only [funlistV39, psort]
    have hz1 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hz2 : j % 4 < 4 := Nat.mod_lt j (by omega)
    interval_cases i % 4 <;> interval_cases j % 4 <;> simp [assocdV39]
  · intro i j
    simp only [funlistV39, psort]
    refine ⟨le_refl _, ?_, le_refl _⟩
    have hz1 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hz2 : j % 4 < 4 := Nat.mod_lt j (by omega)
    interval_cases i % 4 <;> interval_cases j % 4 <;> simp [assocdV39] <;>
      first | exact LE_sqrt8_2h0_xw6 | exact sqrt8_LE_6_xw6 | exact LE_sqrt8_2_xw6 | norm_num [h0, cstab]
  · intro i; simp [funlistV39]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39] <;>
      first | exact LE_sqrt8_2_xw6 | exact LE_sqrt8_2h0_xw6 | norm_num [h0, cstab]
  · intro i hk3
    omega
  · intro i hk4
    rw [← funlist_mod_p20_xw6 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)]
        (2 * h0) 4 i (i + 1) (by omega), ← Nat.mod_add_mod i 4 1]
    have hz : i % 4 < 4 := Nat.mod_lt i (by omega)
    interval_cases i % 4 <;> simp [funlistV39, psort, assocdV39] <;>
      first | exact sqrt8_LE_CSTAB_xw6 | norm_num [h0, cstab]
  · have key : ∀ r : ℕ, r < 4 →
        ((2 * h0 < funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)]
              (2 * h0) 4 r ((r + 1) % 4) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)]
              2 4 r ((r + 1) % 4)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, LT_sqrt8_2h0_xw6]
    have hS : {i | i < 4 ∧ (2 * h0 < funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6),
              ((1, 3), 6)] (2 * h0) 4 i (i + 1) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)]
              2 4 i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← funlist_mod_p20_xw6 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)]
          (2 * h0) 4 i (i + 1) (by omega),
        ← funlist_mod_p20_xw6 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)]
          2 4 i (i + 1) (by omega), ← Nat.mod_add_mod i 4 1]
      rw [key (i % 4) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    simp

/-- Every `sInitListV39` member is an `isScsV39` system: entries 1-6 are the
named `scs6I1`..`scs4I2` constants (`is_scs_*_p22`, LocalAuto22); entry 7 is
`scs5I3` (`SCS_5I3_IS_SCS_xw6`, LocalAuto20) and entry 8 is `scs4I3`
(`init8_isScs_xw6`), after the inlined `a_pro` lambdas are identified with the
`funlistV39` tables via `init7a/b_xw6`, `init8a/b_xw6`. -/
theorem s_init_scs_xw6 (s : ScsV39) (hs : s ∈ sInitListV39) : isScsV39 s := by
  simp only [sInitListV39, List.mem_cons, List.not_mem_nil] at hs
  rcases hs with he | he | he | he | he | he | he | he | he
  · rw [he]; exact is_scs_6I1_p22
  · rw [he]; exact is_scs_5I1_p22
  · rw [he]; exact is_scs_4I1_p22
  · rw [he]; exact is_scs_3I1_p22
  · rw [he]; exact is_scs_5I2_p22
  · rw [he]; exact is_scs_4I2_p22
  · rw [he]
    rw [init7a_xw6, init7b_xw6]
    exact SCS_5I3_IS_SCS_xw6
  · rw [he]
    rw [init8a_xw6, init8b_xw6]
    exact init8_isScs_xw6
  · exact absurd he (by simp)



/-! ## Part 3: LocalAuto24 Section C (`UXCKFPE.hl`) case bank, `_krnl` -> `_xw6` -/

open Kepler.Geom Set Classical

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
bookkeeping) are carried verbatim from LocalAuto24, where they are PROVED
(standard three axioms); this file changes only the declaration names
(`_p24` -> `_xw6`). -/


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
theorem NOT_EMPTY_CASE_4_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
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
theorem IN_NOT_EMPTY_B1_SY_4_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
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
theorem XWITCCN_CASE_4_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
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
        (fullStable_of_isScsV39 s hs hk hk3 _ _ (fun _ _ => rfl) (fun _ _ => rfl)))
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
  have hne := NOT_EMPTY_CASE_4_IS_SCS_xw6 s vv hs hk hBB
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
    IN_NOT_EMPTY_B1_SY_4_IS_SCS_xw6 s vv1 hs hk hp4 hball hC1 hC2
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
  -- DISCHARGES: IS_SCS_STABLE_SYSTEM_p23 + NOT_EMPTY_CASE_4_IS_SCS_xw6 +
  -- the HDPLYGY/B_SY1 minimizer on the stable record + IN_NOT_EMPTY_B1_SY_4
  -- + TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4_p23 (negativity transfer).
  -- (FILLED, casebank-close-w1 kit: wiring = HDPLYGY minimizer
  -- (B_SY1_p4_compact_of_fan_p23 + continuousOn_tauStar_p23) on the
  -- post SF-81a+SF-C3 stable record + the five prereq fills + the filled
  -- SF-C3-fixed TAUSTAR bridge. Transitive taint: continuousOn_tauFun_p23 +
  -- bodyClosed_p23 (HDPLYGY-kit NEEDS, giant roots — see CLOSE-PLAN §M0).)

/-! ### C2. The k = 5 witnesses (UXCKFPE.hl:547-995) -/

/-- HOL `NOT_EMPTY_CASE_5_IS_SCS` (UXCKFPE.hl:547). -/
theorem NOT_EMPTY_CASE_5_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
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
theorem IN_NOT_EMPTY_B1_SY_5_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
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
  -- DISCHARGES: as `IN_NOT_EMPTY_B1_SY_4_IS_SCS_xw6` at k = 5
  -- (V_E_FF_IS_SCS_CASES_5_p23).
  -- (filled from the LA23 fill + the LA36 core `inB1_core_p36`.)

/-- HOL `XWITCCN_CASE_5_IS_SCS` (UXCKFPE.hl:889). -/
theorem XWITCCN_CASE_5_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
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
        (fullStable_of_isScsV39 s hs hk hk3 _ _ (fun _ _ => rfl) (fun _ _ => rfl)))
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
  have hne := NOT_EMPTY_CASE_5_IS_SCS_xw6 s vv hs hk hBB
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
    IN_NOT_EMPTY_B1_SY_5_IS_SCS_xw6 s vv1 hs hk hp5 hball hC1 hC2
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
  -- DISCHARGES: as `XWITCCN_CASE_4_IS_SCS_xw6` at k = 5.
  -- (FILLED, casebank-close-w1 kit: wiring = HDPLYGY minimizer
  -- (B_SY1_p4_compact_of_fan_p23 + continuousOn_tauStar_p23) on the
  -- post SF-81a+SF-C3 stable record + the five prereq fills + the filled
  -- SF-C3-fixed TAUSTAR bridge. Transitive taint: continuousOn_tauFun_p23 +
  -- bodyClosed_p23 (HDPLYGY-kit NEEDS, giant roots — see CLOSE-PLAN §M0).)

/-! ### C3. The k = 6 witnesses (UXCKFPE.hl:1003-1483) -/

/-- HOL `NOT_EMPTY_CASE_6_IS_SCS` (UXCKFPE.hl:1003). -/
theorem NOT_EMPTY_CASE_6_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
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
theorem IN_NOT_EMPTY_B1_SY_6_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
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
  -- DISCHARGES: as `IN_NOT_EMPTY_B1_SY_4_IS_SCS_xw6` at k = 6
  -- (V_E_FF_IS_SCS_CASES_6_p23).
  -- (filled from the LA23 fill + the LA36 core `inB1_core_p36`.)

/-- HOL `XWITCCN_CASE_6_IS_SCS` (UXCKFPE.hl:1374). -/
theorem XWITCCN_CASE_6_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
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
        (fullStable_of_isScsV39 s hs hk hk3 _ _ (fun _ _ => rfl) (fun _ _ => rfl)))
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
  have hne := NOT_EMPTY_CASE_6_IS_SCS_xw6 s vv hs hk hBB
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
    IN_NOT_EMPTY_B1_SY_6_IS_SCS_xw6 s vv1 hs hk hp6 hball hC1 hC2
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
  -- DISCHARGES: as `XWITCCN_CASE_4_IS_SCS_xw6` at k = 6.
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
the rows of the MEMBER's matvec pre-image.  `IN_NOT_EMPTY_B1_SY_3_IS_SCS_xw6`
keeps the cycRow form: its hypotheses are about the specific realisation
`v` (HOL `row i v` of the abbreviated `v = vector[vv 1; vv 2; vv 0]`), not a
set membership.  Statements SF-80-frozen; the eight bodies below are FILLED
by lane sf80-case3-w1 (2026-11-02), with the private `w1*` kit preceding. -/

/-! #### sf80-case3-w1 kit (private): `Periodic2` mod bookkeeping, `setSum`
reindexing, the row/coordinate identities of the k = 3 flattening, the
elementary non-collinearity of k = 3 body rows, the `dihV`/`tau3`
`ContinuousAt` kit (LA9 `fw5` shape, generalized over continuous coordinate
maps), and the closedness/boundedness of the row-indexed k = 3 body set. -/

/-- `Periodic2` residue pullback, first argument. -/
private theorem w1periodic2_mod_l {α : Sort*} {f : ℕ → ℕ → α} {k : ℕ}
    (hp : Periodic2 f k) (i m : ℕ) : f i m = f (i % k) m := by
  have h1 : f i m = f (i % k + k * (i / k)) m :=
    (congrArg (fun t => f t m) (Nat.mod_add_div i k)).symm
  rw [h1]
  induction i / k with
  | zero => simp
  | succ n ih =>
      have hrw : i % k + k * (n + 1) = (i % k + k * n) + k := by ring
      rw [hrw, (hp (i % k + k * n) m).1, ih]

/-- `setSum` reindexing along an injection onto the source. -/
private theorem w1setSum_image_bij {α β : Type*} [DecidableEq α] [DecidableEq β]
    (φ : β → α) {A : Set α} {B : Set β} {f : α → ℝ} {g : β → ℝ}
    (hB : B.Finite) (hmem : ∀ x ∈ B, φ x ∈ A) (hinj : Set.InjOn φ B)
    (hsurj : ∀ y ∈ A, ∃ x ∈ B, φ x = y) (hfg : ∀ x ∈ B, g x = f (φ x)) :
    setSum A f = setSum B g := by
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

/-- the rows of the k = 3 flattening are the cyclic row vector. -/
private theorem w1rowSy_flattenRow3 (vv : ℕ → V3) (i : ℕ) (hi : i < 3) :
    rowSy_p23 (flattenRow_p23 vv 3) i = vv ((i + 1) % 3) := by
  unfold rowSy_p23
  rw [dif_pos hi, vecmatsV3_flattenRow_p23]
  rfl

/-- the `(r, c)` entry of a `FinVec 3 3` is coordinate `3 * r + c`. -/
private theorem w1coord (l : FinVec 3 3) (r : ℕ) (hr : r < 3) (c : ℕ)
    (hc : c < 3) :
    rowSy_p23 l r ⟨c, hc⟩ = l ⟨3 * r + c, by omega⟩ := by
  unfold rowSy_p23
  rw [dif_pos hr]
  show (vecmatsV3_p4 l ⟨r, hr⟩) ⟨c, hc⟩ = l ⟨3 * r + c, by omega⟩
  have hidx : l ⟨3 * r + c, by omega⟩ = vecmats_p4 l ⟨r, hr⟩ ⟨c, hc⟩ :=
    (congrArg l (Fin.ext (show r * 3 + c = 3 * r + c from by rw [Nat.mul_comm]))).symm.trans
      rfl
  rw [hidx]
  rfl

private theorem w1body3_bounded (aR bR : Fin 3 → Fin 3 → ℝ) :
    Bornology.IsBounded {l : FinVec 3 3 |
      (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
        CONDITION1_SY_p4 aR bR (fun i : Fin 3 => rowSy_p23 l i)} := by
  refine Metric.isBounded_iff.mpr ⟨4 * h0, fun p₁ hp₁ p₂ hp₂ => ?_⟩
  rw [dist_pi_le_iff (by
    have hh : h0 = 1.26 := rfl
    norm_num [hh])]
  intro k
  have hr : ((k : ℕ) / 3) < 3 := by omega
  have hc : ((k : ℕ) % 3) < 3 := by omega
  have hval : (⟨3 * ((k : ℕ) / 3) + (k : ℕ) % 3, by omega⟩ : Fin 9) = k := by
    have hk9 := k.isLt
    exact Fin.eq_of_val_eq (show 3 * ((k : ℕ) / 3) + (k : ℕ) % 3 = (k : ℕ) from by omega)
  have hrow1 : rowSy_p23 p₁ ((k : ℕ) / 3) ⟨(k : ℕ) % 3, hc⟩ = p₁ k := by
    rw [w1coord p₁ _ hr _ hc]
    exact congrArg p₁ hval
  have hrow2 : rowSy_p23 p₂ ((k : ℕ) / 3) ⟨(k : ℕ) % 3, hc⟩ = p₂ k := by
    rw [w1coord p₂ _ hr _ hc]
    exact congrArg p₂ hval
  have hb1 : ‖p₁ k‖ ≤ 2 * h0 := by
    rw [← hrow1]
    calc ‖rowSy_p23 p₁ ((k : ℕ) / 3) ⟨(k : ℕ) % 3, hc⟩‖
        ≤ ‖rowSy_p23 p₁ ((k : ℕ) / 3)‖ := PiLp.norm_apply_le _ _
      _ ≤ 2 * h0 := (ballAnnulus_norm_bounds (hp₁.1 ⟨(k : ℕ) / 3, hr⟩)).2
  have hb2 : ‖p₂ k‖ ≤ 2 * h0 := by
    rw [← hrow2]
    calc ‖rowSy_p23 p₂ ((k : ℕ) / 3) ⟨(k : ℕ) % 3, hc⟩‖
        ≤ ‖rowSy_p23 p₂ ((k : ℕ) / 3)‖ := PiLp.norm_apply_le _ _
      _ ≤ 2 * h0 := (ballAnnulus_norm_bounds (hp₂.1 ⟨(k : ℕ) / 3, hr⟩)).2
  calc dist (p₁ k) (p₂ k) = ‖p₁ k - p₂ k‖ := dist_eq_norm _ _
    _ ≤ ‖p₁ k‖ + ‖p₂ k‖ := norm_sub_le _ _
    _ ≤ 4 * h0 := by linarith

/-- the shifted `a`/`b` tables at k = 3. -/
private theorem w1ab3_of_isScs (s : ScsV39) (hs : isScsV39 s) (hk : s.k = 3) :
    (∀ i j : Fin 3, i ≠ j →
      2 ≤ s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3)) ∧
    (∀ i j : Fin 3, i ≠ j →
      s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3) < 4) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpb, -, hsymm, -, -, hage2, hb3, -, -, -, -⟩ := hs
  have hpb3 : Periodic2 s.b 3 := by
    rw [show s.k = 3 from hk] at hpb
    exact hpb
  refine ⟨fun i j hij => hage2 _ _ ⟨by omega, by omega, ?_⟩, fun i j hij => ?_⟩
  · intro hcc
    have hi3 := i.isLt
    have hj3 := j.isLt
    exact hij (Fin.val_injective (by omega))
  · have b01 : s.b 0 1 < 4 := hb3 0 hk
    have b12 : s.b 1 2 < 4 := hb3 1 hk
    have b20 : s.b 2 0 < 4 := by
      rw [← periodic2_mod_r_p23 hpb3 2 3]
      exact hb3 2 hk
    have hb4 : ∀ p q : ℕ, p < 3 → q < 3 → p ≠ q → s.b p q < 4 := by
      intro p q _ _ hpq
      rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with hp' | hp' | hp' <;>
        rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with hq' | hq' | hq'
      · exact absurd (by rw [hp', hq']) hpq
      · rw [hp', hq']; exact b01
      · rw [hp', hq', (hsymm 0 2).2.2.2.1]; exact b20
      · rw [hp', hq', (hsymm 1 0).2.2.2.1]; exact b01
      · exact absurd (by rw [hp', hq']) hpq
      · rw [hp', hq']; exact b12
      · rw [hp', hq']; exact b20
      · rw [hp', hq', (hsymm 2 1).2.2.2.1]; exact b12
      · exact absurd (by rw [hp', hq']) hpq
    exact hb4 (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3) (by omega) (by omega)
      (fun hcc => hij (Fin.val_injective (by have hi3 := i.isLt; have hj3 := j.isLt; omega)))

/-- the elementary non-collinearity of the origin and two distinct k = 3
body rows. -/
private theorem w1not_collinear3 (aR bR : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → V3)
    (h1 : ∀ i : Fin 3, v i ∈ ballAnnulus)
    (h2 : CONDITION1_SY_p4 aR bR v)
    (hb : ∀ i j : Fin 3, i ≠ j → bR i j < 4)
    (i j : Fin 3) (hij : i ≠ j) (ha : 2 ≤ aR i j) :
    ¬ Collinear ℝ ({0, v i, v j} : Set V3) := by
  intro hcol
  obtain ⟨hge_i, hle_i⟩ := ballAnnulus_norm_bounds (h1 i)
  obtain ⟨hge_j, hle_j⟩ := ballAnnulus_norm_bounds (h1 j)
  have hvi0 : v i ≠ 0 := fun hz => by
    have hn0 : ‖v i‖ = 0 := norm_eq_zero.mpr hz
    linarith
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := (0:V3)) (w := v i) (w1 := v j) hvi0).mp hcol
  have hj' : v j = c • v i := by simpa using hc
  have hnj : ‖v j‖ = |c| * ‖v i‖ := by rw [hj', norm_smul, Real.norm_eq_abs]
  have hd : ‖v i - v j‖ = |1 - c| * ‖v i‖ := by
    have hstep : v i - v j = (1 - c) • v i := by rw [hj']; module
    rw [hstep, norm_smul, Real.norm_eq_abs]
  obtain ⟨hlo, hhi⟩ := h2 i j
  have hge : (2:ℝ) ≤ ‖v i - v j‖ := le_trans ha hlo
  have hbb : bR i j < 4 := hb i j hij
  have h026 : h0 = 1.26 := rfl
  by_cases hcneg : c < 0
  · -- opposite rays: ‖p - q‖ = ‖p‖ + ‖q‖ ≥ 4 > bR i j
    have hnj' : ‖v j‖ = (-c) * ‖v i‖ := by rw [hnj, abs_of_neg hcneg]
    have hle_i := hle_i
    have hle_j := hle_j
    have hge_i := hge_i
    have hge_j := hge_j
    have hpos : (0:ℝ) < 1 - c := by linarith
    have hdd : ‖v i - v j‖ = ‖v i‖ + ‖v j‖ := by
      rw [hd, abs_of_pos hpos, hnj']; ring
    have h4 : 4 ≤ ‖v i - v j‖ := by linarith
    linarith
  · -- same line: ‖p - q‖ = |‖p‖ - ‖q‖| ≤ 2 * h0 - 2 < 2 ≤ aR i j
    have hcpos : 0 ≤ c := le_of_not_gt hcneg
    have hnj' : ‖v j‖ = c * ‖v i‖ := by rw [hnj, abs_of_nonneg hcpos]
    have hle_i := hle_i
    have hle_j := hle_j
    have hge_i := hge_i
    have hge_j := hge_j
    by_cases hc1 : (1:ℝ) ≤ c
    · have hdd : ‖v i - v j‖ = ‖v j‖ - ‖v i‖ := by
        rw [hd, abs_of_nonpos (by linarith), hnj']; ring
      linarith
    · have hdd : ‖v i - v j‖ = ‖v i‖ - ‖v j‖ := by
        rw [hd, abs_of_nonneg (by linarith), hnj']; ring
      linarith

/-- `dihV 0 · · ·` first projection vector (LA9 `fw5_proj` clone). -/
private def w1proj (u v : V3) : V3 := (u ⬝ᵥ u) • v - (v ⬝ᵥ u) • u

private theorem w1cont_dot {X : Type*} [TopologicalSpace X] {p r : X → V3}
    (hp : Continuous p) (hr : Continuous r) : Continuous (fun x => p x ⬝ᵥ r x) := by
  have h : Continuous (fun x => inner ℝ (p x) (r x)) := hp.inner hr
  simpa only [inner_eq_dot] using h

private theorem w1cont_smul {X : Type*} [TopologicalSpace X] {k : X → ℝ} {v : X → V3}
    (hk : Continuous k) (hv : Continuous v) : Continuous (fun x => k x • v x) := hk.smul hv

private theorem w1cont_sub {X : Type*} [TopologicalSpace X] {p q : X → V3}
    (hp : Continuous p) (hq : Continuous q) : Continuous (fun x => p x - q x) := hp.sub hq

private theorem w1proj_ne_zero (u v : V3)
    (huv : ¬ Collinear ℝ ({0, u, v} : Set V3)) : w1proj u v ≠ 0 := by
  have hu : u ≠ 0 := fun hu0 => huv (collinear3_of_eq hu0)
  have hnu : (‖u‖ : ℝ) ≠ 0 := fun he => hu (norm_eq_zero.mp he)
  have hu2 : u ⬝ᵥ u ≠ 0 := fun hc =>
    hnu (sq_eq_zero_iff.mp (by rw [norm_sq_eq_dot]; exact hc))
  intro hzero
  refine huv ((collinear3_iff_smul hu).mpr ⟨(v ⬝ᵥ u) / (u ⬝ᵥ u), ?_⟩)
  show v - 0 = _ • (u - 0)
  rw [sub_zero, sub_zero]
  refine smul_right_injective V3 hu2 ?_
  show (u ⬝ᵥ u) • v = (u ⬝ᵥ u) • ((v ⬝ᵥ u) / (u ⬝ᵥ u)) • u
  rw [smul_smul, mul_comm, div_mul_cancel₀ _ hu2]
  exact sub_eq_zero.mp hzero

private theorem w1dihV_eq (u v w : V3) :
    dihV 0 u v w =
      Real.arccos ((w1proj u v ⬝ᵥ w1proj u w) /
        (‖w1proj u v‖ * ‖w1proj u w‖)) := by
  unfold dihV arcV w1proj
  simp [sub_zero, dist_eq_norm]

private theorem w1continuousAt_dihV_map {X : Type*} [TopologicalSpace X] {x : X}
    {u v w : X → V3} (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (huv : ¬ Collinear ℝ ({0, u x, v x} : Set V3))
    (huw : ¬ Collinear ℝ ({0, u x, w x} : Set V3)) :
    ContinuousAt (fun t => dihV 0 (u t) (v t) (w t)) x := by
  have hne1 : ‖w1proj (u x) (v x)‖ ≠ 0 :=
    fun he => w1proj_ne_zero (u x) (v x) huv (norm_eq_zero.mp he)
  have hne2 : ‖w1proj (u x) (w x)‖ ≠ 0 :=
    fun he => w1proj_ne_zero (u x) (w x) huw (norm_eq_zero.mp he)
  have hpA : Continuous (fun t : X => w1proj (u t) (v t)) :=
    w1cont_sub (w1cont_smul (w1cont_dot hu hu) hv) (w1cont_smul (w1cont_dot hv hu) hu)
  have hpB : Continuous (fun t : X => w1proj (u t) (w t)) :=
    w1cont_sub (w1cont_smul (w1cont_dot hu hu) hw) (w1cont_smul (w1cont_dot hw hu) hu)
  have hnum : Continuous (fun t : X =>
      w1proj (u t) (v t) ⬝ᵥ w1proj (u t) (w t)) := w1cont_dot hpA hpB
  have hden : Continuous (fun t : X =>
      ‖w1proj (u t) (v t)‖ * ‖w1proj (u t) (w t)‖) := (hpA.norm).mul hpB.norm
  have hquot : ContinuousAt (fun t : X =>
      (w1proj (u t) (v t) ⬝ᵥ w1proj (u t) (w t)) /
        (‖w1proj (u t) (v t)‖ * ‖w1proj (u t) (w t)‖)) x :=
    hnum.continuousAt.div hden.continuousAt (mul_ne_zero hne1 hne2)
  have hfinal : ContinuousAt (fun t : X =>
      Real.arccos ((w1proj (u t) (v t) ⬝ᵥ w1proj (u t) (w t)) /
        (‖w1proj (u t) (v t)‖ * ‖w1proj (u t) (w t)‖))) x :=
    hquot.arccos
  exact hfinal.congr (Filter.Eventually.of_forall
    (fun t => (w1dihV_eq (u t) (v t) (w t)).symm))

private theorem w1continuousAt_tau3 {X : Type*} [TopologicalSpace X] {x : X}
    {p q r : X → V3} (hp : Continuous p) (hq : Continuous q) (hr : Continuous r)
    (hpq : ¬ Collinear ℝ ({0, p x, q x} : Set V3))
    (hpr : ¬ Collinear ℝ ({0, p x, r x} : Set V3))
    (hqr : ¬ Collinear ℝ ({0, q x, r x} : Set V3)) :
    ContinuousAt (fun t => tau3 (p t) (q t) (r t)) x := by
  have hsetqp : ({0, q x, p x} : Set V3) = {0, p x, q x} := by
    ext y
    simp only [Set.mem_insert_iff]
    tauto
  have hsetrp : ({0, r x, p x} : Set V3) = {0, p x, r x} := by
    ext y
    simp only [Set.mem_insert_iff]
    tauto
  have hsetrq : ({0, r x, q x} : Set V3) = {0, q x, r x} := by
    ext y
    simp only [Set.mem_insert_iff]
    tauto
  have hqp : ¬ Collinear ℝ ({0, q x, p x} : Set V3) := fun h =>
    hpq (by rw [← hsetqp]; exact h)
  have hrp : ¬ Collinear ℝ ({0, r x, p x} : Set V3) := fun h =>
    hpr (by rw [← hsetrp]; exact h)
  have hrq : ¬ Collinear ℝ ({0, r x, q x} : Set V3) := fun h =>
    hqr (by rw [← hsetrq]; exact h)
  have hrho : Continuous (fun y : ℝ => rho y) := by
    unfold rho
    fun_prop
  have hn1 : Continuous (fun t => ‖p t‖) := hp.norm
  have hn2 : Continuous (fun t => ‖q t‖) := hq.norm
  have hn3 : Continuous (fun t => ‖r t‖) := hr.norm
  have ht1 : ContinuousAt (fun t => rho (‖p t‖) * dihV 0 (p t) (q t) (r t)) x :=
    ((hrho.comp hn1).continuousAt).mul
      (w1continuousAt_dihV_map hp hq hr hpq hpr)
  have ht2 : ContinuousAt (fun t => rho (‖q t‖) * dihV 0 (q t) (r t) (p t)) x :=
    ((hrho.comp hn2).continuousAt).mul
      (w1continuousAt_dihV_map hq hr hp hqr hqp)
  have ht3 : ContinuousAt (fun t => rho (‖r t‖) * dihV 0 (r t) (p t) (q t)) x :=
    ((hrho.comp hn3).continuousAt).mul
      (w1continuousAt_dihV_map hr hp hq hrp hrq)
  have hsum := (ht1.add ht2).add ht3
  have hres := hsum.sub
    (show ContinuousAt (fun _ : X => (Real.pi + sol0)) x from
      continuous_const.continuousAt)
  exact hres.congr (Filter.Eventually.of_forall fun t => rfl)

/-- closedness, inline-set form. -/
private theorem w1setClosed (aR bR : Fin 3 → Fin 3 → ℝ) :
    IsClosed {l : FinVec 3 3 |
      (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
        CONDITION1_SY_p4 aR bR (fun i : Fin 3 => rowSy_p23 l i)} := by
  have h1 : IsClosed {l : FinVec 3 3 | ∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus} := by
    have hrw : {l : FinVec 3 3 | ∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus}
        = ⋂ i : Fin 3, (fun l : FinVec 3 3 => rowSy_p23 l i) ⁻¹' ballAnnulus := by
      ext l
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [hrw]
    exact isClosed_iInter fun i =>
      IsClosed.preimage (continuous_rowSy_p23 i) CLOSED_BALL_ANNULUS
  have h2 : IsClosed {l : FinVec 3 3 |
      CONDITION1_SY_p4 aR bR (fun i : Fin 3 => rowSy_p23 l i)} := by
    have hrw2 : {l : FinVec 3 3 | CONDITION1_SY_p4 aR bR (fun i : Fin 3 => rowSy_p23 l i)}
        = ⋂ (i : Fin 3) (j : Fin 3),
          (fun l : FinVec 3 3 => ‖rowSy_p23 l i - rowSy_p23 l j‖) ⁻¹'
            Set.Ici (aR i j) ∩
          (fun l : FinVec 3 3 => ‖rowSy_p23 l i - rowSy_p23 l j‖) ⁻¹'
            Set.Iic (bR i j) := by
      ext l
      simp only [CONDITION1_SY_p4, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
        Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic]
    rw [hrw2]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    have hc : Continuous (fun l : FinVec 3 3 =>
        ‖rowSy_p23 l i - rowSy_p23 l j‖) :=
      ((continuous_rowSy_p23 i).sub (continuous_rowSy_p23 j)).norm
    exact (IsClosed.preimage hc isClosed_Ici).inter
      (IsClosed.preimage hc isClosed_Iic)
  exact h1.inter h2

/-- boundedness, inline-set form. -/
private theorem w1setBounded (aR bR : Fin 3 → Fin 3 → ℝ) :
    Bornology.IsBounded {l : FinVec 3 3 |
      (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
        CONDITION1_SY_p4 aR bR (fun i : Fin 3 => rowSy_p23 l i)} :=
  w1body3_bounded aR bR

/-! ### the eight fills as test lemmas -/



/-- HOL `IN_IS_SCS_CASE_3` (UXCKFPE.hl:1502): the k = 3 flattening
`matvec (vector[vv 1; vv 2; vv 0])` lies in the (CONDITION2-free) body.
SF-80: membership constrains the member's own rows, as in HOL. -/
theorem IN_IS_SCS_CASE_3_xw6 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    flattenRow_p23 vv 3 ∈
      {l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · have hi3 := i.isLt
    rw [w1rowSy_flattenRow3 vv (i : ℕ) (by omega)]
    exact hBB.1 ⟨((i : ℕ) + 1) % 3, rfl⟩
  · have hi3 := i.isLt
    have hj3 := j.isLt
    simp only []
    have h := hBB.2.2.1 (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3)
    rw [dist_eq_norm] at h
    rw [w1rowSy_flattenRow3 vv (i : ℕ) (by omega),
      w1rowSy_flattenRow3 vv (j : ℕ) (by omega)]
    exact ⟨h.1, h.2⟩
  -- DISCHARGES: rows-in-annulus via `vecmatsV3_flattenRow_p36` (rows of the
  -- flattening ARE the cyclic row vector: `rowSy_p23 (flattenRow_p23 vv 3) i
  -- = cycRow_p23 vv 3 i`, probe-validated CLEAN in sfc1c2draft-w1
  -- probe80_fix.lean `flattenRow_mem_B3fix`) + the BBsV39 a/b bounds at the
  -- cyclic rows (no fan conjunct needed at k = 3).

set_option maxHeartbeats 1000000 in
/-- HOL `IN_NOT_EMPTY_B1_SY_3_IS_SCS` (UXCKFPE.hl:1701). -/
theorem IN_NOT_EMPTY_B1_SY_3_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hper : Periodic vv 3)
    (hball : ∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
      (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
      (cycRow_p23 vv 3)) :
    BBsV39 s vv := by
  have hk3 : s.k = 3 := hk
  obtain ⟨-, -, -, -, -, -, -, haP, -, -, hpb, -, -, -, -, -, -, -, -, -, -⟩ := hs
  rw [show s.k = 3 from hk3] at haP hpb
  have hper' : Periodic vv s.k := by
    rw [hk3]
    exact hper
  refine ⟨?_, hper', ?_, Or.inl (by omega)⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    rw [← periodic_mod_eq_p23 hper i]
    rcases Nat.lt_trichotomy (i % 3) 1 with h0 | h1r | h2
    · rw [show i % 3 = 0 from by omega]
      have h := hball ⟨2, by omega⟩
      simpa [cycRow_p23] using h
    · rw [show i % 3 = 1 from by omega]
      have h := hball ⟨0, by omega⟩
      simpa [cycRow_p23] using h
    · rw [show i % 3 = 2 from by omega]
      have h := hball ⟨1, by omega⟩
      simpa [cycRow_p23] using h
  · intro i j
    have hrai : s.a i j = s.a (i % 3) (j % 3) := by
      rw [w1periodic2_mod_l haP i j, periodic2_mod_r_p23 haP (i % 3) j]
    have hpb3 : Periodic2 s.b 3 := hpb
    have hrbi : s.b i j = s.b (i % 3) (j % 3) := by
      rw [w1periodic2_mod_l hpb3 i j, periodic2_mod_r_p23 hpb3 (i % 3) j]
    have key := hC1 ⟨(i % 3 + 2) % 3, by omega⟩ ⟨(j % 3 + 2) % 3, by omega⟩
    have hlo2 : s.a (((i % 3 + 2) % 3 + 1) % 3) (((j % 3 + 2) % 3 + 1) % 3)
        ≤ ‖vv (((i % 3 + 2) % 3 + 1) % 3) - vv (((j % 3 + 2) % 3 + 1) % 3)‖ :=
      key.1
    have hhi2 : s.b (((i % 3 + 2) % 3 + 1) % 3) (((j % 3 + 2) % 3 + 1) % 3)
        ≥ ‖vv (((i % 3 + 2) % 3 + 1) % 3) - vv (((j % 3 + 2) % 3 + 1) % 3)‖ :=
      key.2
    have e1 : ((i % 3 + 2) % 3 + 1) % 3 = i % 3 := by omega
    have e2 : ((j % 3 + 2) % 3 + 1) % 3 = j % 3 := by omega
    rw [e1] at hlo2 hhi2
    rw [e2] at hlo2 hhi2
    rw [hrai, hrbi, dist_eq_norm,
      ← periodic_mod_eq_p23 hper i, ← periodic_mod_eq_p23 hper j]
    exact ⟨hlo2, hhi2⟩
  -- DISCHARGES: BBsV39 conjunct walk at k = 3 (the `k ≤ 3` fan disjunct
  -- makes CONDITION2 unnecessary, as in the HOL source).

/-- HOL `NOT_EMPTY_CASE_3_IS_SCS` (UXCKFPE.hl:1775).  SF-80: row-indexed
body set. -/
theorem NOT_EMPTY_CASE_3_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    ({l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} : Set (FinVec 3 3)) ≠ ∅ := by
  exact Set.nonempty_iff_ne_empty.mp
    ⟨flattenRow_p23 vv 3, IN_IS_SCS_CASE_3_xw6 s vv hs hk hBB⟩
  -- DISCHARGES: IN_IS_SCS_CASE_3_xw6 (witness `flattenRow_p23 vv 3`).

/-- HOL `J1_TS` (UXCKFPE.hl:1792): the k = 3 ear index set, with the
application-instantiated `f_ts s = (\i. (1+i) MOD 3)` carried as a
parameter `f` (and `J_TS s` as `J`). -/
def J1_TS_xw6 (J : Set (Set ℕ)) (f : ℕ → ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ i, {i % 3, f (i % 3)} ∈ J ∧ i ∈ Set.Icc 1 3 ∧ x = (i, i % 3 + 1)}

/-- HOL `d_fun3` (UXCKFPE.hl:1797): the k = 3 ear functional, `d_ts`/ear
flag/`J_TS`/`f_ts` carried as parameters (`d`, `ear`, `J`, `f`). -/
noncomputable def dFun3_xw6 (d : ℝ) (ear : Prop) (J : Set (Set ℕ)) (f : ℕ → ℕ)
    (l : FinVec 3 3) : ℝ :=
  d + (1 : ℝ) / 10 * (if ear then 1 else -1) *
    setSum (J1_TS_xw6 J f)
      (fun x => cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖)

/-- HOL `FINITE_J1_TS` (UXCKFPE.hl:1801). -/
theorem FINITE_J1_TS_xw6 (J : Set (Set ℕ)) (f : ℕ → ℕ) :
    (J1_TS_xw6 J f).Finite := by
  refine (Set.finite_range fun i : Fin 3 =>
    ((i : ℕ) + 1, ((i : ℕ) + 1) % 3 + 1)).subset ?_
  rintro x ⟨i, -, hi, rfl⟩
  have h1 : 1 ≤ i := hi.1
  have h3 : i ≤ 3 := hi.2
  refine ⟨⟨i - 1, by omega⟩, ?_⟩
  show ((i - 1 : ℕ) + 1, (i - 1 + 1) % 3 + 1) = (i, i % 3 + 1)
  rw [show i - 1 + 1 = i from by omega]

/-- the `dFun3_xw6` head is continuous (mirror of `continuous_dFun_p23`). -/
private theorem w1continuous_dFun3 (s : ScsV39) :
    Continuous (fun l : FinVec 3 3 =>
      dFun3_xw6 s.d (isEarV39 s) (scsJSet_p23 s) (fun i => (1 + i) % s.k) l) := by
  have hterms : ∀ x ∈ J1_TS_xw6 (scsJSet_p23 s) (fun i : ℕ => (1 + i) % s.k),
      Continuous (fun l : FinVec 3 3 =>
        cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖) := fun x _ =>
    Continuous.sub continuous_const
      (((continuous_rowSy_p23 (x.1 - 1)).sub (continuous_rowSy_p23 (x.2 - 1))).norm)
  unfold dFun3_xw6
  refine Continuous.add continuous_const (Continuous.const_mul ?_ _)
  simp only [setSum]
  split
  · rename_i h
    exact continuous_finsetSum _ (fun x hx => hterms x (h.mem_toFinset.mp hx))
  · exact continuous_const

/-- HOL `CONTINUOUS_ON_D_FUN3` (UXCKFPE.hl:1813): `d_fun3` is continuous
on the k = 3 body set (sum over the finite `J1_TS_xw6` of row differences).
SF-80: row-indexed body set. -/
theorem CONTINUOUS_ON_D_FUN3_xw6 (s : ScsV39) (hk : s.k = 3)
    (vv : ℕ → V3) :
    ContinuousOn
      (fun l : FinVec 3 3 =>
        dFun3_xw6 s.d (isEarV39 s) (scsJSet_p23 s) (fun i => (1 + i) % s.k) l)
      {l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} := by
  exact (w1continuous_dFun3 s).continuousOn
  -- DISCHARGES: setSum over the 3-point FINITE_J1_TS_xw6 set of
  -- `cstab - ‖rowSy_p23 l _ - rowSy_p23 l _‖` (continuous in `l`), the
  -- constant `d`/ear terms (HOL CONTINUOUS_ON_ADD/VSUM/ROW kit).

/-- HOL `tri_sy_explicit` (UXCKFPE.hl:1856): the projections of the
`tri_sy (k,d,s,a,b,J,f)` record (↦ `StableSyP23`) return its components. -/
theorem tri_sy_explicit_xw6 (k : ℕ) (d : ℝ) (s : Set ℕ) (a b : ℕ → ℕ → ℝ)
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
theorem IN_B_SY1_COLLINEAR_CASE_3_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
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
  obtain ⟨haR, hbR⟩ := w1ab3_of_isScs s hs hk
  intro l hl
  have hnc := w1not_collinear3
    (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
    (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
    (fun i : Fin 3 => rowSy_p23 l i) hl.1 hl.2 hbR
  exact ⟨hnc 0 1 (by decide) (haR 0 1 (by decide)),
    hnc 0 2 (by decide) (haR 0 2 (by decide)),
    hnc 1 2 (by decide) (haR 1 2 (by decide))⟩
  -- DISCHARGES: the row-decoding of IN_NOT_EMPTY_B1_SY_3 (rows of a body
  -- point are a BBs realisation) + IS_SCS_NOT_COLLINEAR_BBs_CASE_3_p23.

/-- HOL `HDPLYGY_CASE_30` (UXCKFPE.hl:1926): the k = 3 minimizer of
`tau3 - d_fun3` over the (compact, nonempty) body set.  SF-80: row-indexed
body set — `hne`/`hnc` are no longer jointly contradictory, the statement
carries real minimizer content. -/
theorem HDPLYGY_CASE_30_xw6 (s : ScsV39) (vv : ℕ → V3)
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
            dFun3_xw6 s.d (isEarV39 s) (scsJSet_p23 s)
              (fun i => (1 + i) % s.k) x ≤
          tau3 (rowSy_p23 y 0) (rowSy_p23 y 1) (rowSy_p23 y 2) -
            dFun3_xw6 s.d (isEarV39 s) (scsJSet_p23 s)
              (fun i => (1 + i) % s.k) y := by
  obtain ⟨haR, hbR⟩ := w1ab3_of_isScs s hs hk
  have htau : ContinuousOn (fun l : FinVec 3 3 =>
      tau3 (rowSy_p23 l 0) (rowSy_p23 l 1) (rowSy_p23 l 2))
      {l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} := by
    intro l hl
    refine ContinuousAt.continuousWithinAt ?_
    have hnc' := w1not_collinear3
      (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
      (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
      (fun i : Fin 3 => rowSy_p23 l i) hl.1 hl.2 hbR
    exact w1continuousAt_tau3 (continuous_rowSy_p23 0) (continuous_rowSy_p23 1)
      (continuous_rowSy_p23 2)
      (hnc' 0 1 (by decide) (haR 0 1 (by decide)))
      (hnc' 0 2 (by decide) (haR 0 2 (by decide)))
      (hnc' 1 2 (by decide) (haR 1 2 (by decide)))
  exact hdplygy_min_core_p23
    (Metric.isCompact_of_isClosed_isBounded
      (w1setClosed
        (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
        (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3)))
      (w1setBounded
        (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
        (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))))
    (Set.nonempty_iff_ne_empty.mpr hne) (htau.sub (w1continuous_dFun3 s).continuousOn)
  -- DISCHARGES: TRI_STABLE_K_EQ_3 + CONTINUOUS_ATTAINS_INF +
  -- COMPACT_TRI_STABLE + CONTINUOUS_ON_D_FUN3_xw6 (the HOL rho/ly/interp
  -- continuity chain for `tau3` on rows).

set_option maxHeartbeats 1000000 in
/-- HOL `TAUSTAR_EQ_TAU_STAR_3_IS_SCS` (UXCKFPE.hl:2126): the scs-taustar
at k = 3 is `tau3 (vv 1) (vv 2) (vv 0) - d_fun3`. -/
theorem TAUSTAR_EQ_TAU_STAR_3_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    taustarV39 s vv = tau3 (vv 1) (vv 2) (vv 0) -
      dFun3_xw6 s.d (isEarV39 s) (scsJSet_p23 s)
        (fun i => (1 + i) % s.k) (flattenRow_p23 vv 3) := by
  have hk3 : s.k = 3 := hk
  have hper : Periodic vv 3 := hk3 ▸ hBB.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hJper, hsymm, -, -, -, -, -, -, -, -⟩ := hs
  rw [show s.k = 3 from hk3] at hJper
  unfold taustarV39
  rw [if_pos (by omega : s.k ≤ 3)]
  have hcyc : tau3 (vv 0) (vv 1) (vv 2) = tau3 (vv 1) (vv 2) (vv 0) := by
    unfold tau3
    ring
  rw [hcyc]
  have hd : dsvV39 s vv = dFun3_xw6 s.d (isEarV39 s) (scsJSet_p23 s)
      (fun i => (1 + i) % s.k) (flattenRow_p23 vv 3) := by
    unfold dsvV39 dFun3_xw6
    have h10 : (0.1:ℝ) = (1:ℝ)/10 := by norm_num
    rw [h10]
    refine congrArg (fun t => s.d + (1:ℝ)/10 * (if isEarV39 s then 1 else -1) * t) ?_
    apply w1setSum_image_bij (φ := fun x : ℕ × ℕ => x.2 - 1)
    · exact FINITE_J1_TS_xw6 _ _
    · -- hmem: every B member maps into the dsv index set
      intro x hx
      rw [show s.k = 3 from hk3] at hx
      simp only [J1_TS_xw6, Set.mem_setOf_eq] at hx
      obtain ⟨i, hedge, hicc, rfl⟩ := hx
      have h1 : 1 ≤ i := hicc.1
      have h3 : i ≤ 3 := hicc.2
      simp only [scsJSet_p23, Set.mem_setOf_eq] at hedge
      obtain ⟨a, b, ha3, hb3, hJab, hset⟩ := hedge
      have hr : i % 3 + 1 - 1 = i % 3 := by omega
      show (i % 3 + 1 - 1 : ℕ) < s.k ∧ s.J (i % 3 + 1 - 1) (i % 3 + 1 - 1 + 1)
      rw [hr]
      refine ⟨by omega, ?_⟩
      rcases Set.pair_eq_pair_iff.mp hset with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · rw [← ha', ← hb',
          show (1 + i % 3) % 3 = (i % 3 + 1) % 3 from by rw [Nat.add_comm],
          ← periodic2_mod_r_p23 hJper (i % 3) (i % 3 + 1)] at hJab
        exact hJab
      · rw [periodic2_mod_r_p23 hJper (i % 3) (i % 3 + 1),
          show (i % 3 + 1) % 3 = (1 + i % 3) % 3 from by rw [Nat.add_comm]]
        rw [← hb', ← ha'] at hJab
        exact Eq.mp (hsymm _ _).2.2.2.2 hJab
    · -- hinj: φ = x.2 - 1 is injective on B
      intro x hx y hy hxy
      rw [show s.k = 3 from hk3] at hx hy
      simp only [J1_TS_xw6, Set.mem_setOf_eq] at hx hy
      obtain ⟨i, hedge, hicc, rfl⟩ := hx
      obtain ⟨i', hedge', hicc', rfl⟩ := hy
      have h1 : 1 ≤ i := hicc.1
      have h3 : i ≤ 3 := hicc.2
      have h1' : 1 ≤ i' := hicc'.1
      have h3' : i' ≤ 3 := hicc'.2
      have hmod : i % 3 = i' % 3 := by simpa using hxy
      have hii : i = i' := by omega
      show (i, i % 3 + 1) = (i', i' % 3 + 1)
      rw [hii]
    · -- hsurj: every dsv index comes from a B member
      intro y hy
      rw [Set.mem_setOf_eq] at hy
      obtain ⟨hy3, hyJ⟩ := hy
      have hiy : ((y + 2) % 3 + 1) % 3 = y := by omega
      have hyJ' : s.J y ((y + 1) % 3) := by
        rw [← periodic2_mod_r_p23 hJper y (y + 1)]
        exact hyJ
      refine ⟨⟨(y + 2) % 3 + 1, y + 1⟩, ?_, ?_⟩
      · simp only [J1_TS_xw6, Set.mem_setOf_eq, scsJSet_p23, Set.mem_setOf_eq]
        rw [show s.k = 3 from hk3]
        refine ⟨(y + 2) % 3 + 1, ⟨y, (y + 1) % 3, by have := hk3; omega, by omega,
          hyJ', ?_⟩, ⟨by omega, by omega⟩, ?_⟩
        · rw [hiy, show (1 + y) % 3 = (y + 1) % 3 from by rw [Nat.add_comm]]
        · rw [hiy]
      · show (y + 1 - 1 : ℕ) = y
        omega
    · -- hfg: summands agree
      intro x hx
      rw [show s.k = 3 from hk3] at hx
      simp only [J1_TS_xw6, Set.mem_setOf_eq] at hx
      obtain ⟨i, hedge, hicc, rfl⟩ := hx
      have h1 : 1 ≤ i := hicc.1
      have h3 : i ≤ 3 := hicc.2
      show (cstab - ‖rowSy_p23 (flattenRow_p23 vv 3) (i - 1)
              - rowSy_p23 (flattenRow_p23 vv 3) (i % 3 + 1 - 1)‖)
          = cstab - dist (vv (i % 3)) (vv (i % 3 + 1))
      rw [w1rowSy_flattenRow3 vv (i - 1) (by omega),
        w1rowSy_flattenRow3 vv (i % 3 + 1 - 1) (by omega),
        show ((i - 1 + 1) % 3) = i % 3 from by omega,
        show ((i % 3 + 1 - 1 + 1) % 3) = (i % 3 + 1) % 3 from by omega,
        periodic_mod_eq_p23 hper (i % 3 + 1), dist_eq_norm]
  rw [hd]
  -- DISCHARGES: taustarV39 k ≤ 3 branch + dsv_v39 = d_fun3 (the J1_TS
  -- index shift via `Periodic2 s.J 3`, IS_SCS_TRI_STABLE_SYSTEM_p23) +
  -- the flattenRow_p23 row/entry identity on `vv 1, vv 2, vv 0`.

set_option maxHeartbeats 1000000 in
/-- HOL `XWITCCN_CASE_3_IS_SCS` (UXCKFPE.hl:2495). -/
theorem XWITCCN_CASE_3_IS_SCS_xw6 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : s.k = 3)
    (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by
  have hne := NOT_EMPTY_CASE_3_IS_SCS_xw6 s vv hs hk hBB
  have hnc := IN_B_SY1_COLLINEAR_CASE_3_IS_SCS_xw6 s vv hs hk hBB
  obtain ⟨x, hx_mem, hx_min⟩ := HDPLYGY_CASE_30_xw6 s vv hs hk hne hnc
  set vv1 : ℕ → V3 := fun i => rowSy_p23 x ((i + 2) % 3) with hv1
  have hper : Periodic vv1 3 := by
    intro i
    show vv1 (i + 3) = vv1 i
    simp only [hv1]
    rw [show ((i + 3) + 2) % 3 = (i + 2) % 3 from by omega]
  have hcyc : ∀ i : Fin 3, cycRow_p23 vv1 3 i = rowSy_p23 x i := by
    intro i
    have hi := i.isLt
    simp only [hv1, cycRow_p23]
    rw [show ((((i : ℕ) + 1) % 3 + 2) % 3) = ((i : ℕ) % 3) from by omega,
      Nat.mod_eq_of_lt hi]
  have hball : ∀ i : Fin 3, cycRow_p23 vv1 3 i ∈ ballAnnulus := fun i => by
    rw [hcyc i]
    exact hx_mem.1 i
  have hC1 : CONDITION1_SY_p4
      (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
      (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
      (cycRow_p23 vv1 3) := by
    have heq : cycRow_p23 vv1 3 = fun i : Fin 3 => rowSy_p23 x i := funext hcyc
    rw [heq]
    exact hx_mem.2
  have hBB1 : BBsV39 s vv1 :=
    IN_NOT_EMPTY_B1_SY_3_IS_SCS_xw6 s vv1 hs hk hper hball hC1
  have hflat : flattenRow_p23 vv1 3 = x := by
    funext i
    have hi := i.isLt
    show (cycRow_p23 vv1 3 ⟨(i : ℕ) / 3, by omega⟩ : Fin 3 → ℝ)
        ⟨(i : ℕ) % 3, by omega⟩ = x i
    rw [hcyc ⟨(i : ℕ) / 3, by omega⟩]
    have hval : (⟨3 * ((i : ℕ) / 3) + (i : ℕ) % 3, by omega⟩ : Fin 9) = i := by
      have hi9 := i.isLt
      exact Fin.eq_of_val_eq (show 3 * ((i : ℕ) / 3) + (i : ℕ) % 3 = (i : ℕ) from
        by omega)
    rw [w1coord x ((i : ℕ) / 3) (by omega) ((i : ℕ) % 3) (by omega)]
    exact congrArg x hval
  have hrowvv : ∀ i : ℕ, i < 3 →
      rowSy_p23 (flattenRow_p23 vv 3) i = vv ((i + 1) % 3) :=
    fun i hi => w1rowSy_flattenRow3 vv i hi
  have hneg : taustarV39 s vv1 < 0 := by
    rw [TAUSTAR_EQ_TAU_STAR_3_IS_SCS_xw6 s vv1 hs hk hBB1, hflat]
    have hta' : tau3 (vv 1) (vv 2) (vv 0)
        - dFun3_xw6 s.d (isEarV39 s) (scsJSet_p23 s) (fun i => (1 + i) % s.k)
            (flattenRow_p23 vv 3) < 0 := by
      rw [← TAUSTAR_EQ_TAU_STAR_3_IS_SCS_xw6 s vv hs hk hBB]
      exact hta
    have hmin := hx_min _ (IN_IS_SCS_CASE_3_xw6 s vv hs hk hBB)
    rw [hrowvv 0 (by omega), hrowvv 1 (by omega), hrowvv 2 (by omega)] at hmin
    exact hmin.trans_lt hta'
  refine fun hempty => ?_
  have hmem : vv1 ∈ (BBprimeV39 s : Set (ℕ → V3)) := by
    refine ⟨hBB1, ?_, hneg⟩
    intro u hBBu
    have hrowu : ∀ i : ℕ, i < 3 →
        rowSy_p23 (flattenRow_p23 u 3) i = u ((i + 1) % 3) :=
      fun i hi => w1rowSy_flattenRow3 u i hi
    have hmin := hx_min _ (IN_IS_SCS_CASE_3_xw6 s u hs hk hBBu)
    rw [hrowu 0 (by omega), hrowu 1 (by omega), hrowu 2 (by omega)] at hmin
    rw [TAUSTAR_EQ_TAU_STAR_3_IS_SCS_xw6 s vv1 hs hk hBB1, hflat, TAUSTAR_EQ_TAU_STAR_3_IS_SCS_xw6 s u hs hk hBBu]
    simp only [hv1]
    exact hmin
  rw [hempty] at hmem
  exact (Set.mem_empty_iff_false _).mp hmem
  -- DISCHARGES: IS_SCS_TRI_STABLE_SYSTEM_p23 + NOT_EMPTY_CASE_3_IS_SCS_xw6
  -- + IN_B_SY1_COLLINEAR_CASE_3_IS_SCS_xw6 + HDPLYGY_CASE_30_xw6 +
  -- IN_NOT_EMPTY_B1_SY_3_IS_SCS_xw6 + TAUSTAR_EQ_TAU_STAR_3_IS_SCS_xw6.

/-- HOL `UXCKFPE` (UXCKFPE.hl:2602): the k = 3..6 case assembly
(the HOL `INST_TYPE` moves become this case split; `isScsV39` gives
`3 ≤ k ≤ 6`). -/
theorem UXCKFPE_xw6 (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by
  have h3 : 3 ≤ s.k := hs.2.1
  have h6 : s.k ≤ 6 := hs.2.2.1
  rcases (by omega : s.k = 3 ∨ s.k = 4 ∨ s.k = 5 ∨ s.k = 6) with hk | hk | hk | hk
  · exact XWITCCN_CASE_3_IS_SCS_xw6 s vv hs hBB hk hta
  · exact XWITCCN_CASE_4_IS_SCS_xw6 s vv hs hBB hk hta
  · exact XWITCCN_CASE_5_IS_SCS_xw6 s vv hs hBB hk hta
  · exact XWITCCN_CASE_6_IS_SCS_xw6 s vv hs hBB hk hta

/-- HOL `UXCKFPE2` (SGTRNAF.hl:75), kernel copy (see module docstring). -/
theorem UXCKFPE2_xw6 : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprime2V39 s ≠ ∅ := by
  intro s vv hs hBB hta
  have hbp : (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := UXCKFPE_xw6 s vv hs hBB hta
  have himage : (BBindexV39 s '' BBprimeV39 s).Nonempty := by
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hbp
    exact ⟨BBindexV39 s w, w, hw, rfl⟩
  have hmin : BBindexMinV39 s ∈ BBindexV39 s '' BBprimeV39 s ∧
      ∀ m ∈ BBindexV39 s '' BBprimeV39 s, BBindexMinV39 s ≤ m :=
    Classical.epsilon_spec (p := fun n => n ∈ BBindexV39 s '' BBprimeV39 s ∧
      ∀ m ∈ BBindexV39 s '' BBprimeV39 s, n ≤ m)
      ⟨sInf _, Nat.sInf_mem himage, fun m hm => Nat.sInf_le hm⟩
  obtain ⟨w, hwprime, hwidx⟩ := hmin.1
  intro hcon
  rw [Set.eq_empty_iff_forall_notMem] at hcon
  exact hcon w ⟨hwprime, hwidx⟩

/-- HOL `SGTRNAF` (SGTRNAF.hl:166), kernel copy: the `sgtrnaf_p12` body.
The `unadorned_MMs` conversion (AYQJTMD.hl:161) is inlined. -/
theorem SGTRNAF_xw6 : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    unadornedV39 s → BBsV39 s vv → taustarV39 s vv < 0 → MMsV39 s ≠ ∅ := by
  intro s vv hs hu hBB hta
  have h2 : (BBprime2V39 s : Set (ℕ → V3)) ≠ ∅ := UXCKFPE2_xw6 s vv hs hBB hta
  obtain ⟨hlo, hhi, hstr, ham, hbm⟩ := hu
  intro hcon
  rw [Set.eq_empty_iff_forall_notMem] at hcon
  obtain ⟨w, hwprime, hwidx⟩ := Set.nonempty_iff_ne_empty.mpr h2
  exact hcon w ⟨⟨hwprime, hwidx⟩,
    fun i hi => by rw [hstr] at hi; exact hi.elim,
    fun i hi => by rw [hlo] at hi; exact hi.elim,
    fun i hi => by rw [hhi] at hi; exact hi.elim,
    fun i j => by rw [← ham]; exact (hwprime.1.2.2.1 i j).1,
    fun i j => by rw [← hbm]; exact (hwprime.1.2.2.1 i j).2⟩

/-- HOL `XWITCCN` (XWITCCN.hl:7980), upstream twin: every `sInitListV39` member
is `isScsV39` (`s_init_scs_xw6`), so the `UXCKFPE` capstone applies. -/
theorem XWITCCN_xw6 : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprimeV39 s ≠ ∅ := by
  intro s vv hs hBB hta
  exact UXCKFPE_xw6 s vv (s_init_scs_xw6 s hs) hBB hta

end Kepler.Text
