/-
LocalAuto36 — port of `scripts/local/XWITCCN.hl` (8020 ln, 2 defs + 77
theorems incl. the `INEQUALITY_A_B_TAC_*` tactic-helper family): the
CONCRETE `XWITCCN` case machine, i.e. the per-initial-system (`s_init_list_v39`)
realisations of `BBs_v39 s vv → taustar_v39 s vv < 0 → BBprime_v39 s ≠ ∅`
for the eight `k ≤ 6` systems

  3I1 = `mk_unadorned_v39 3 (d_tame 3) (cs_adj 3 2 (2*h0)) (cs_adj 3 (2*h0) 6)`
  4I1 / 5I1 / 6I1 (same shape at k = 4/5/6),
  4_3     = `mk_unadorned_v39 4 #0.467 (cs_adj 4 2 3) (cs_adj 4 (2*h0) 6)`,
  5_sqrt8 = `mk_unadorned_v39 5 #0.616 (cs_adj 5 2 sqrt8) (cs_adj 5 (2*h0) 6)`,
  4_sqrt8 = `mk_unadorned_v39 4 #0.477 (a_pro 4 (2*h0) 2 sqrt8) (a_pro 4 sqrt8 (2*h0) 6)`,
  5_pro_cs= `mk_unadorned_v39 5 #0.616 (a_pro 5 (2*h0) 2 (2*h0)) (a_pro 5 sqrt8 (2*h0) 6)`.

Sections follow source order: kit, k = 3, k = 4, k = 5, k = 6, 5_sqrt8,
5_pro_cs, 4_3, 4_sqrt8, then `XWITCCN_TYPE` / `XWITCCN`.

TACTIC-HELPER REDESIGN. HOL `let T = fun (so:term) ... -> TAC;;` bindings
(the `INEQUALITY_A_B_TAC_*` / `PROVE_*_TAC` / `PROOF_*_TAC` /
`VV_IN_BALL_ANNULUS_TAC_*` / `IN_BALL_*TAC*` families, 92 bindings / 54
distinct names after HOL shadowing) are ALL-CAPS "theorems" that carry a
tactic. They are ported as faithful HELPER LEMMAS: hypotheses = the tactic
preconditions (the `ASM`/`MRESAL` context, e.g. `BBsV39 s vv` or
`Periodic vv k`), conclusion = the tactic postcondition (the goal shape the
tactic discharges: the a/b bound conjuncts of `BBsV39`, the `V_SY`/`E_SY`/
`F_SY` image equalities of the `V_E_FF` conjunct, `ballAnnulus` membership,
witness memberships). Tactic replay is deliberately NOT attempted; where a
helper's goal shape is reconstructed from the family pattern rather than the
verbatim body, the docstring says so.

Encoding (house conventions, cf. LocalAuto24/33):
- HOL `real^3` ↔ `V3`; `vec 0` ↔ `0`; `dist` ↔ `dist`; `#0.616` etc. ↔
  exact decimal literals; `sqrt8` ↔ `Real.sqrt 8`; `h0`/`cstab`/`ballAnnulus`
  from `Kepler.Text` (PackingAuto2/LocalAuto1).
- HOL `real^(M,3)finite_product` with `dimindex(:M) = k` ↔ `FinVec k 3`
  (`Fin (k*3) → ℝ`); `matvec (vector[vv 1;..;vv k;vv 0])` ↔
  `flattenRow_p23 vv k`; `row i (vecmats l)` (1-based) ↔ `rowSy_p23 l (i-1)`;
  the row-decoding hypothesis `!i. vv i = if i MOD k = 0 then row k v ...`
  is carried as `Periodic vv k` plus conditions on `cycRow_p23 vv k`
  (LocalAuto24 rendering of the same UXCKFPE-shaped machine).
- `V_SY`/`E_SY`/`F_SY`/`CONDITION1_SY`/`CONDITION2_SY`/`B_SY1` ↔ the `_p4`
  twins (LocalAuto4); the body set `{matvec v | rows IN ball_annulus /\
  CONDITION1_SY a b v /\ CONDITION2_SY v}` ↔ `B_SY1_p4 aT bT` with the
  1-based scs tables `aT i j = change_type_v3 s.a (i+1, j+1)`.
- `stable_sy`/`tau_star`/`stable_system`/`tri_stable` ↔ `StableSyP23` /
  `tauStar_p23` / `stableSystem_p23` / `triStable_p23` (LocalAuto23 kit;
  the unused HOL reals dummy `d` is `0`); `change_type_v2 (scs_J_v39 s) k`
  is proved equal to `scsJSet_p23 s` in Section 0.
- `card`/`IMAGE vv (:num)` ↔ `Nat.card`/`Set.range vv`; `collinear` ↔
  `Collinear ℝ`.
- `sorry` bodies carry `-- DISCHARGES:` naming the missing HOL inputs.
  Same-wave files LocalAuto34/35 are NOT imported (any overlap is resolved
  at the merge by deleting twins).
- FILL LEDGER (proof-fill wave 2): 48 -> 34 sorries. Filled: the 8
  `SCS_*_IS_TRI_STABLE` (generic cs_adj/a_pro successor-table builders +
  `torsor_succ_mod_p36`; cstab = 3.01 makes every bound numeric),
  `IN_NOT_EMPTY_B1_SY_3`, `NOT_COLLINEAR_BBs_CASE_3`,
  `IN_B_SY1_COLLINEAR_CASE_3`, `TAUSTAR_EQ_TAU_STAR_3` (dTame 3 = 0 +
  `tau3_cycle_p36`). Remaining 34: `CARD_SLICE_EQ`, `HDPLYGY_CASE_3`,
  `XWITCCN_CASE_*` (8, blocked by TAUSTAR_* + the B_SY1-minimiser),
  `TAUSTAR_EQ_TAU_STAR_*` k >= 4 (7, statement doubt ①: s1.d := 0 vs
  taustarV39's dTame k), the k >= 4 `IN_NOT_EMPTY_CASE/B1_SY` twins (14,
  blocked by the registry-ConvexLocalFan vs `convexLocalFan_p4` def-bridge
  — azimCycle_p4 vs sigmaFan; see NEEDS notes), `IN_NOT_EMPTY_CASE_3`
  (statement doubt ②), `XWITCCN_TYPE`/`XWITCCN`.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto3
import Kepler.Text.LocalAuto4
import Kepler.Text.LocalAuto8
import Kepler.Text.LocalAuto23
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

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


/-! ## Section 1: the k = 3 system (XWITCCN.hl:63-2428) -/

/-- HOL `wedge_in_fan_gt` (localization.hl:79) — statement-level twin.
LocalAuto2 (`wedgeInFanGt_p2`) is NOT importable here (PackingAuto18/20
`atn2` clash); body = the LocalAuto3 rendering `wedgeInFanGt_p3` (same
shape, proved def); NEEDS dedup at merge. -/
noncomputable def wedgeInFanGt_p36 (d : V3 × V3) (E : Set (Set V3)) : Set V3 :=
  wedgeInFanGt_p3 d E

/-- HOL `slicev` (localization.hl:149) — statement-level twin of
LocalAuto2 `slicev_p2` (same import caveat); body = the LocalAuto8
rendering `slicev_p8` (same shape); NEEDS dedup at merge. -/
def slicev_p36 (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3) : Set V3 :=
  slicev_p8 E FF v w

/-- HOL `CARD_SLICE_EQ` (XWITCCN.hl:63). -/
theorem CARD_SLICE_EQ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3)
    (hfan : ConvexLocalFan V E FF) (hvw : v ≠ w) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u ∈ ({v, w} : Set V3), ∀ u1 ∈ V, u ≠ u1 → ¬Collinear ℝ {0, u, u1})
    (hwedge : ∀ e ∈ FF, affGt {0} {v, w} ⊆ wedgeInFanGt_p36 e E) :
    Nat.card V = Nat.card (slicev_p36 E FF v w) + Nat.card (slicev_p36 E FF w v) - 2 := by
  sorry
  -- DISCHARGES: HOL Localization `CARD_SLICE_EQ` proof (rhoNode1 walk split
  -- at v, w); NEEDS the slicev card kit + `ConvexLocalFan` nondegeneracy.

/-! ### Value-table/case disjunction for `cs_adj` and `a_pro` (def-order
precedence: diagonal, then `{0,1}` pair, then cyclic adjacency, then far). -/

private theorem csAdj_values_p36 {k : ℕ} {a1 a2 : ℝ} {i j : ℕ} :
    (i % k = j % k ∧ csAdj k a1 a2 i j = 0) ∨
      (i % k ≠ j % k ∧ (j % k = (i + 1) % k ∨ (j + 1) % k = i % k) ∧
        csAdj k a1 a2 i j = a1) ∨
      (i % k ≠ j % k ∧ ¬(j % k = (i + 1) % k ∨ (j + 1) % k = i % k) ∧
        csAdj k a1 a2 i j = a2) := by
  unfold csAdj
  by_cases h1 : i % k = j % k
  · exact Or.inl ⟨h1, if_pos h1⟩
  · rw [if_neg h1]
    by_cases h2 : j % k = (i + 1) % k ∨ (j + 1) % k = i % k
    · exact Or.inr (Or.inl ⟨h1, h2, if_pos h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, if_neg h2⟩)

private theorem aPro_values_p36 {k : ℕ} {p a1 a2 : ℝ} {i j : ℕ} :
    (i % k = j % k ∧ aPro k p a1 a2 i j = 0) ∨
      (i % k ≠ j % k ∧ ({i % k, j % k} : Set ℕ) = {0, 1} ∧ aPro k p a1 a2 i j = p) ∨
      (i % k ≠ j % k ∧ ({i % k, j % k} : Set ℕ) ≠ {0, 1} ∧
        (j % k = (i + 1) % k ∨ (j + 1) % k = i % k) ∧ aPro k p a1 a2 i j = a1) ∨
      (i % k ≠ j % k ∧ ({i % k, j % k} : Set ℕ) ≠ {0, 1} ∧
        ¬(j % k = (i + 1) % k ∨ (j + 1) % k = i % k) ∧ aPro k p a1 a2 i j = a2) := by
  unfold aPro
  by_cases h1 : i % k = j % k
  · exact Or.inl ⟨h1, if_pos h1⟩
  · rw [if_neg h1]
    by_cases h2 : ({i % k, j % k} : Set ℕ) = {0, 1}
    · exact Or.inr (Or.inl ⟨h1, h2, if_pos h2⟩)
    · rw [if_neg h2]
      by_cases h3 : j % k = (i + 1) % k ∨ (j + 1) % k = i % k
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, if_pos h3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, if_neg h3⟩))

private theorem csAdj_diag_p36 {k : ℕ} {a1 a2 : ℝ} (i : ℕ) :
    csAdj k a1 a2 i i = 0 := by
  unfold csAdj; exact if_pos rfl

private theorem csAdj_shift_p36 {k : ℕ} {a1 a2 : ℝ} (i j : ℕ) :
    csAdj k a1 a2 i j = csAdj k a1 a2 i (j % k) := by
  rw [csAdj_mod_p36 k a1 a2 i j, csAdj_mod_p36 k a1 a2 i (j % k),
    show (j % k) % k = j % k from Nat.mod_mod j k]

private theorem aPro_diag_p36 {k : ℕ} {p a1 a2 : ℝ} (i : ℕ) :
    aPro k p a1 a2 i i = 0 := by
  unfold aPro; exact if_pos rfl

private theorem aPro_shift_p36 {k : ℕ} {p a1 a2 : ℝ} (i j : ℕ) :
    aPro k p a1 a2 i j = aPro k p a1 a2 i (j % k) := by
  rw [aPro_mod_p36 k p a1 a2 i j, aPro_mod_p36 k p a1 a2 i (j % k),
    show (j % k) % k = j % k from Nat.mod_mod j k]

/-- `cs_adj k (2*h0) b2 i ((1+i)%k) = 2*h0`: the successor pair is never
diagonal and always cyclically adjacent. -/
private theorem csAdj_fi_p36 {k : ℕ} {b2 : ℝ} (hk : 1 < k) (i : ℕ) :
    csAdj k (2 * h0) b2 i ((1 + i) % k) = 2 * h0 := by
  have e1 : ((1 + i) % k) % k = (i + 1) % k := by
    rw [Nat.mod_mod, Nat.add_comm 1 i]
  have hne : i % k ≠ ((1 + i) % k) % k := fun he => succ_mod_ne_p36 hk i (he.trans e1)
  rcases csAdj_values_p36 (k := k) (a1 := 2 * h0) (a2 := b2) (i := i)
    (j := (1 + i) % k) with h | ⟨-, -, hv⟩ | ⟨-, hneg, -⟩
  · exact absurd h.1 hne
  · exact hv
  · exact absurd (Or.inl e1) hneg

/-- `a_pro k p' a1' a2' i ((1+i)%k)` is `p'` (the `{0,1}` band, only at
`i % k = 0`) or `a1'` (cyclic adjacency). -/
private theorem aPro_fi_p36 {k : ℕ} {p' a1' a2' : ℝ} (hk : 1 < k) (i : ℕ) :
    aPro k p' a1' a2' i ((1 + i) % k) = p' ∨
      aPro k p' a1' a2' i ((1 + i) % k) = a1' := by
  have e1 : ((1 + i) % k) % k = (i + 1) % k := by
    rw [Nat.mod_mod, Nat.add_comm 1 i]
  have hne : i % k ≠ ((1 + i) % k) % k := fun he => succ_mod_ne_p36 hk i (he.trans e1)
  rcases aPro_values_p36 (k := k) (p := p') (a1 := a1') (a2 := a2') (i := i)
    (j := (1 + i) % k) with h | ⟨-, -, hv⟩ | ⟨-, -, -, hv⟩ | ⟨-, -, hneg, -⟩
  · exact absurd h.1 hne
  · exact Or.inl hv
  · exact Or.inr hv
  · exact absurd (Or.inl e1) hneg

/-! ### Generic stable/tri-stable builders for the successor-cycling
unadorned systems on `0..k-1` (torsor from `torsor_succ_mod_p36`, `J = ∅`;
value tables are `cs_adj`/`a_pro` ladders). The `a ≤ b` conjunct is a same
pair case walk: both tables read the same case, so only the four aligned
cases occur and the others die on the case witnesses. -/

private theorem constraintSystem_succ_empty_p36 {k : ℕ} (hk3 : 3 ≤ k) (hk6 : k ≤ 6)
    (aT bT : ℕ → ℕ → ℝ)
    (hsym : ∀ i j, aT i j = aT j i ∧ bT i j = bT j i ∧ aT i j ≤ bT i j)
    (hshift : ∀ i j, aT i j = aT i (j % k) ∧ bT i j = bT i (j % k)) :
    constraintSystem_p23 k 0 (Set.Iic (k - 1)) aT bT ∅ (fun i => (1 + i) % k) := by
  refine ⟨hk3, hk6, torsor_succ_mod_p36 (k := k) (by omega), ?_, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨(hsym i j).1, (hsym i j).2.1, (hsym i j).2.2⟩
  · intro i j
    have hfk : (fun i => (1 + i) % k)^[k] j = (j + k) % k :=
      succModIter_pos_p36 k (by omega) j k (by omega)
    rw [hfk, Nat.add_mod_right]
    exact hshift i j
  · intro e he
    exact absurd he (by simp)
  · simpa using hk6

private theorem stableSystem_csAdj_succ_p36 {k : ℕ} (hk3 : 3 ≤ k) (hk6 : k ≤ 6)
    (a2 b2 : ℝ) (ha2 : 2 ≤ a2) (ha2b2 : a2 ≤ b2) :
    stableSystem_p23 k 0 (Set.Iic (k - 1)) (csAdj k 2 a2) (csAdj k (2 * h0) b2)
      ∅ (fun i => (1 + i) % k) := by
  have hk1 : (1 : ℕ) < k := by have := hk3; omega
  have hnum : (2 : ℝ) ≤ 2 * h0 := by rw [h0]; norm_num
  refine ⟨constraintSystem_succ_empty_p36 hk3 hk6 _ _ ?_ ?_, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨csAdj_symm_p36, csAdj_symm_p36, ?_⟩
    rcases csAdj_values_p36 (k := k) (a1 := 2) (a2 := a2) (i := i) (j := j) with
      h | ⟨hne, hadj, hv⟩ | ⟨hne, hneg, hv⟩
    · rcases csAdj_values_p36 (k := k) (a1 := 2 * h0) (a2 := b2) (i := i) (j := j) with
        h' | ⟨hne', -, -⟩ | ⟨hne', -, -⟩
      · rw [h.2, h'.2]
      · exact absurd h.1 hne'
      · exact absurd h.1 hne'
    · rcases csAdj_values_p36 (k := k) (a1 := 2 * h0) (a2 := b2) (i := i) (j := j) with
        h' | ⟨hne', hadj', hv'⟩ | ⟨hne', hneg', hv'⟩
      · exact absurd h'.1 hne
      · rw [hv, hv']; rw [h0]; norm_num
      · exact absurd hadj hneg'
    · rcases csAdj_values_p36 (k := k) (a1 := 2 * h0) (a2 := b2) (i := i) (j := j) with
        h' | ⟨hne', hadj', hv'⟩ | ⟨hne', hneg', hv'⟩
      · exact absurd h'.1 hne
      · exact absurd hadj' hneg
      · rw [hv, hv']; exact ha2b2
  · intro i j
    exact ⟨csAdj_shift_p36 i j, csAdj_shift_p36 i j⟩
  · intro i hi j hj hne
    have hik : i < k := by have := Set.mem_Iic.mp hi; omega
    have hjk : j < k := by have := Set.mem_Iic.mp hj; omega
    rcases csAdj_values_p36 (k := k) (a1 := 2) (a2 := a2) (i := i) (j := j) with
      h | ⟨-, -, hv⟩ | ⟨-, -, hv⟩
    · rw [Nat.mod_eq_of_lt hik, Nat.mod_eq_of_lt hjk] at h; exact absurd h.1 hne
    · rw [hv]
    · rw [hv]; exact ha2
  · intro i _
    refine ⟨csAdj_diag_p36 i, ?_⟩
    rw [csAdj_fi_p36 (k := k) (b2 := b2) hk1 i, h0, cstab]
    norm_num
  · intro i j hj
    exact absurd hj (by simp)

private theorem triStable_csAdj_succ_p36 (a2 b2 : ℝ) (ha2 : 2 ≤ a2) (ha2b2 : a2 ≤ b2) :
    triStable_p23 3 0 (Set.Iic (3 - 1)) (csAdj 3 2 a2) (csAdj 3 (2 * h0) b2)
      ∅ (fun i => (1 + i) % 3) := by
  have hk1 : (1 : ℕ) < 3 := by norm_num
  have hnum : (2 : ℝ) ≤ 2 * h0 := by rw [h0]; norm_num
  have hk36 : (3 : ℕ) ≤ 6 := by norm_num
  refine ⟨constraintSystem_succ_empty_p36 (by norm_num : (3:ℕ) ≤ 3)
    (by norm_num : (3:ℕ) ≤ 6) _ _ ?_ ?_, rfl, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨csAdj_symm_p36, csAdj_symm_p36, ?_⟩
    rcases csAdj_values_p36 (k := 3) (a1 := 2) (a2 := a2) (i := i) (j := j) with
      h | ⟨hne, hadj, hv⟩ | ⟨hne, hneg, hv⟩
    · rcases csAdj_values_p36 (k := 3) (a1 := 2 * h0) (a2 := b2) (i := i) (j := j) with
        h' | ⟨hne', -, -⟩ | ⟨hne', -, -⟩
      · rw [h.2, h'.2]
      · exact absurd h.1 hne'
      · exact absurd h.1 hne'
    · rcases csAdj_values_p36 (k := 3) (a1 := 2 * h0) (a2 := b2) (i := i) (j := j) with
        h' | ⟨hne', hadj', hv'⟩ | ⟨hne', hneg', hv'⟩
      · exact absurd h'.1 hne
      · rw [hv, hv']; rw [h0]; norm_num
      · exact absurd hadj hneg'
    · rcases csAdj_values_p36 (k := 3) (a1 := 2 * h0) (a2 := b2) (i := i) (j := j) with
        h' | ⟨hne', hadj', hv'⟩ | ⟨hne', hneg', hv'⟩
      · exact absurd h'.1 hne
      · exact absurd hadj' hneg
      · rw [hv, hv']; exact ha2b2
  · intro i j
    exact ⟨csAdj_shift_p36 i j, csAdj_shift_p36 i j⟩
  · intro i hi j hj hne
    have hik : i < 3 := by have := Set.mem_Iic.mp hi; omega
    have hjk : j < 3 := by have := Set.mem_Iic.mp hj; omega
    rcases csAdj_values_p36 (k := 3) (a1 := 2) (a2 := a2) (i := i) (j := j) with
      h | ⟨-, -, hv⟩ | ⟨-, -, hv⟩
    · rw [Nat.mod_eq_of_lt hik, Nat.mod_eq_of_lt hjk] at h; exact absurd h.1 hne
    · rw [hv]
    · rw [hv]; exact ha2
  · intro i _
    refine ⟨csAdj_diag_p36 i, ?_⟩
    rw [csAdj_fi_p36 (k := 3) (b2 := b2) hk1 i, h0]
    norm_num
  · intro i j hj
    exact absurd hj (by simp)

private theorem stableSystem_aPro_succ_p36 {k : ℕ} (hk3 : 3 ≤ k) (hk6 : k ≤ 6)
    (p a1 a2 p' a1' a2' : ℝ)
    (hge_p : 2 ≤ p) (hle_p : p ≤ p') (hge_a1 : 2 ≤ a1) (hle_a1 : a1 ≤ a1')
    (hle_a2 : a2 ≤ a2') (hbound : p' ≤ cstab ∧ a1' ≤ cstab) (hge_a2 : 2 ≤ a2) :
    stableSystem_p23 k 0 (Set.Iic (k - 1)) (aPro k p a1 a2) (aPro k p' a1' a2')
      ∅ (fun i => (1 + i) % k) := by
  have hk1 : (1 : ℕ) < k := by have := hk3; omega
  refine ⟨constraintSystem_succ_empty_p36 hk3 hk6 _ _ ?_ ?_, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨aPro_symm_p36, aPro_symm_p36, ?_⟩
    rcases aPro_values_p36 (k := k) (p := p) (a1 := a1) (a2 := a2) (i := i) (j := j) with
      h | ⟨hne, h01, hv⟩ | ⟨hne, h01, hadj, hv⟩ | ⟨hne, h01, hneg, hv⟩
    · rcases aPro_values_p36 (k := k) (p := p') (a1 := a1') (a2 := a2') (i := i)
        (j := j) with h' | ⟨hne', -, -⟩ | ⟨hne', -, -⟩ | ⟨hne', -, -⟩
      · rw [h.2, h'.2]
      · exact absurd h.1 hne'
      · exact absurd h.1 hne'
      · exact absurd h.1 hne'
    · rcases aPro_values_p36 (k := k) (p := p') (a1 := a1') (a2 := a2') (i := i)
        (j := j) with h' | ⟨hne', h01', hv'⟩ | ⟨hne', h01', hadj', hv'⟩ |
        ⟨hne', h01', hneg', hv'⟩
      · exact absurd h'.1 hne
      · rw [hv, hv']; exact hle_p
      · exact absurd h01 h01'
      · exact absurd h01 h01'
    · rcases aPro_values_p36 (k := k) (p := p') (a1 := a1') (a2 := a2') (i := i)
        (j := j) with h' | ⟨hne', h01', hv'⟩ | ⟨hne', h01', hadj', hv'⟩ |
        ⟨hne', h01', hneg', hv'⟩
      · exact absurd h'.1 hne
      · exact absurd h01' h01
      · rw [hv, hv']; exact hle_a1
      · exact absurd hadj hneg'
    · rcases aPro_values_p36 (k := k) (p := p') (a1 := a1') (a2 := a2') (i := i)
        (j := j) with h' | ⟨hne', h01', hv'⟩ | ⟨hne', h01', hadj', hv'⟩ |
        ⟨hne', h01', hneg', hv'⟩
      · exact absurd h'.1 hne
      · exact absurd h01' h01
      · exact absurd hadj' hneg
      · rw [hv, hv']; exact hle_a2
  · intro i j
    exact ⟨aPro_shift_p36 i j, aPro_shift_p36 i j⟩
  · intro i hi j hj hne
    have hik : i < k := by have := Set.mem_Iic.mp hi; omega
    have hjk : j < k := by have := Set.mem_Iic.mp hj; omega
    rcases aPro_values_p36 (k := k) (p := p) (a1 := a1) (a2 := a2) (i := i) (j := j) with
      h | ⟨-, -, hv⟩ | ⟨-, -, -, hv⟩ | ⟨-, -, -, hv⟩
    · rw [Nat.mod_eq_of_lt hik, Nat.mod_eq_of_lt hjk] at h; exact absurd h.1 hne
    · rw [hv]; exact hge_p
    · rw [hv]; exact hge_a1
    · rw [hv]; exact hge_a2
  · intro i _
    refine ⟨aPro_diag_p36 i, ?_⟩
    rcases aPro_fi_p36 (k := k) (p' := p') (a1' := a1') (a2' := a2') hk1 i with hv | hv
    · rw [hv]; exact hbound.1
    · rw [hv]; exact hbound.2
  · intro i j hj
    exact absurd hj (by simp)

theorem SCS_3_IS_TRI_STABLE (s : ScsV39)
    (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6)) :
    triStable_p23 s.k 0 (Set.Iic (s.k - 1))
      (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
      (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k) := by
  have hk : s.k = 3 := by rw [hs]; rfl
  have ha : s.a = csAdj 3 2 (2 * h0) := by rw [hs]; rfl
  have hb : s.b = csAdj 3 (2 * h0) 6 := by rw [hs]; rfl
  have hJ : change_type_v2 s.J 3 = ∅ := by
    rw [hs]; exact change_type_v2_mkUnadorned_p36 _ _ _
  rw [hk, ha, hb, hJ]
  simpa only [change_type_v3] using
    triStable_csAdj_succ_p36 (a2 := 2 * h0) (b2 := 6)
      (by rw [h0]; norm_num) (by rw [h0]; norm_num)

/-- HOL `ROW_IN_BALL_ANNULUS_3` (XWITCCN.hl:1303) as a lemma: the
`fun th -> ...` tactic proves `vv th IN ball_annulus` from `IMAGE vv (:num)
SUBSET ball_annulus`. -/
theorem ROW_IN_BALL_ANNULUS_3 (vv : ℕ → V3) (hsub : Set.range vv ⊆ ballAnnulus)
    (th : ℕ) : vv th ∈ ballAnnulus :=
  hsub (Set.mem_range_self th)

/-- HOL `INEQUALITY_A_B_SCS_TAC_30` (XWITCCN.hl:1315) as a lemma: the
a/b bound conjunct of `BBsV39 s vv` in `change_type_v3` form. -/
theorem INEQUALITY_A_B_SCS_TAC_30 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) :
    change_type_v3 s.a (i, j) ≤ dist (vv i) (vv j) ∧
      dist (vv i) (vv j) ≤ change_type_v3 s.b (i, j) :=
  hBB.2.2.1 i j

/-- HOL `INEQUALITY_A_B_SCS_TAC_3` (XWITCCN.hl:1322): the case machine
`i = 1 ∨ i = 2 ∨ i = 0` collapses to the same bound conjunct. -/
theorem INEQUALITY_A_B_SCS_TAC_3 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) :
    change_type_v3 s.a (i, j) ≤ dist (vv i) (vv j) ∧
      dist (vv i) (vv j) ≤ change_type_v3 s.b (i, j) :=
  INEQUALITY_A_B_SCS_TAC_30 s vv hBB i j

/-- HOL `IN_NOT_EMPTY_CASE_3` (XWITCCN.hl:1335). -/
theorem IN_NOT_EMPTY_CASE_3 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 3) :
    flattenRow_p23 vv 3 ∈ B_SY1_p4
      (fun (i j : Fin 3) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 3) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
  sorry
  -- DISCHARGES: BBsV39 unpack (annulus rows via ROW_IN_BALL_ANNULUS_3 /
  -- VECTOR_3_3, CONDITION1 via the cs_adj ladder, fan conjunct vacuous at
  -- k = 3) with witness `flattenRow_p23 vv 3`.
  -- NEEDS (statement doubt, cf. HANDOFF ②): the B_SY1_p4 body requires
  -- CONDITION2_SY_p4 (a convex local fan), but BBsV39 at k = 3 gives only the
  -- vacuous left fan disjunct (s.k ≤ 3); the HOL k = 3 body has no CONDITION2.
  -- Should be re-stated against a CONDITION2-free body (LA24 rendering).

/-- HOL `NOT_EMPTY_CASE_3` (XWITCCN.hl:1383). -/
theorem NOT_EMPTY_CASE_3 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 3) :
    B_SY1_p4
      (fun (i j : Fin 3) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 3) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp
    (⟨flattenRow_p23 vv 3, IN_NOT_EMPTY_CASE_3 s vv hs hBB hk⟩ :
      (B_SY1_p4
        (fun (i j : Fin 3) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
        (fun (i j : Fin 3) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))).Nonempty)

/-- HOL `SCS_A_B__EQ_MOD_3` (XWITCCN.hl:1408). -/
theorem SCS_A_B__EQ_MOD_3 (s : ScsV39)
    (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
    (i j : ℕ) :
    s.a i j = s.a (i % 3) (j % 3) ∧ s.b i j = s.b (i % 3) (j % 3) := by
  subst hs
  exact ⟨csAdj_mod_p36 3 2 (2 * h0) i j, csAdj_mod_p36 3 (2 * h0) 6 i j⟩

/-- HOL `VV_IN_BALL_ANNULUS_TAC_3` (XWITCCN.hl:1430) as a lemma. -/
theorem VV_IN_BALL_ANNULUS_TAC_3 (vv : ℕ → V3) (hsub : Set.range vv ⊆ ballAnnulus)
    (i : ℕ) : vv i ∈ ballAnnulus :=
  hsub (Set.mem_range_self i)

/-- HOL `PROVE_INEQUALITY_TAC_30` (XWITCCN.hl:1436) as a lemma: the a/b
bound conjunct of `BBsV39 s vv` (raw table form). -/
theorem PROVE_INEQUALITY_TAC_30 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  hBB.2.2.1 i j

/-- HOL `PROVE_INEQUALITY_TAC_3` (XWITCCN.hl:1460): the `j MOD 3` case
machine collapses to the same bound conjunct. -/
theorem PROVE_INEQUALITY_TAC_3 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  PROVE_INEQUALITY_TAC_30 s vv hBB i j

/-! ### Annulus-norm/collinearity kit for the k = 3 case machine (a pair of
annulus points at table distance `2..2*h0` is never collinear with `0`). -/

private theorem ballAnnulus_norm_p36 {x : V3} (hx : x ∈ ballAnnulus) :
    (2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * h0 := by
  unfold ballAnnulus at hx
  obtain ⟨hcb, hnb⟩ := hx
  have h1 : dist x (0 : V3) ≤ 2 * h0 := hcb
  have h2 : ¬ dist x (0 : V3) < 2 := fun hd => hnb (Metric.mem_ball.mpr hd)
  rw [dist_zero_right] at h1 h2
  exact ⟨le_of_not_gt h2, h1⟩

private theorem notCollinear_annulus_pair_p36 {p q : V3} (hp : p ∈ ballAnnulus)
    (hq : q ∈ ballAnnulus) (hlo : (2 : ℝ) ≤ dist p q) (hhi : dist p q ≤ 2 * h0) :
    ¬ Collinear ℝ ({0, p, q} : Set V3) := by
  intro hcol
  obtain ⟨p0, w, hw⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hcol
  obtain ⟨r0, hr0⟩ := hw 0 (by simp)
  obtain ⟨r1, hr1⟩ := hw p (by simp)
  obtain ⟨r2, hr2⟩ := hw q (by simp)
  have hp0 : p ≠ 0 := fun he => ballAnnulus_ne_0_p23 _ hp he
  simp only [vadd_eq_add] at hr0 hr1 hr2
  have hp0neg : p0 = -(r0 • w) := by
    have h := eq_neg_of_add_eq_zero_left hr0.symm
    calc p0 = -(-p0) := (neg_neg p0).symm
      _ = -(r0 • w) := by rw [h]
  have hc1 : p = (r1 - r0) • w := by rw [hr1, hp0neg]; module
  have hc2 : q = (r2 - r0) • w := by rw [hr2, hp0neg]; module
  have hc10 : r1 - r0 ≠ 0 := by
    intro he
    rw [hc1, he, zero_smul] at hp0
    exact hp0 rfl
  have hvdef : w = (r1 - r0)⁻¹ • p := by
    rw [hc1, inv_smul_smul₀ hc10]
  have hqeq : q = ((r2 - r0) / (r1 - r0)) • p := by
    rw [hc2, hvdef, smul_smul, div_eq_inv_mul, mul_comm]
  obtain ⟨hplo, hphi⟩ := ballAnnulus_norm_p36 hp
  obtain ⟨hqlo, hqhi⟩ := ballAnnulus_norm_p36 hq
  simp only [h0] at hphi hqhi hhi
  set t := (r2 - r0) / (r1 - r0) with ht
  have hnormq : ‖q‖ = |t| * ‖p‖ := by
    rw [hqeq, norm_smul, Real.norm_eq_abs]
  have hsub : p - t • p = (1 - t) • p := by module
  have hd : dist p q = |1 - t| * ‖p‖ := by
    rw [dist_eq_norm, hqeq, hsub, norm_smul, Real.norm_eq_abs]
  have habst : |t| = t ∨ |t| = -t := by
    rcases le_or_gt 0 t with h | h
    · exact Or.inl (abs_of_nonneg h)
    · exact Or.inr (abs_of_neg h)
  have habs1 : |1 - t| = 1 - t ∨ |1 - t| = t - 1 := by
    rcases le_or_gt t 1 with h | h
    · exact Or.inl (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)])
    · exact Or.inr (by rw [abs_of_neg (by linarith : (1 : ℝ) - t < 0)]; ring)
  rcases habst with h2 | h2
  · rw [h2] at hnormq
    rcases habs1 with h1 | h1
    · rw [h1] at hd
      have hsum : dist p q + ‖q‖ = ‖p‖ := by rw [hd, hnormq]; ring
      linarith
    · rw [h1] at hd
      have hsum : dist p q + ‖p‖ = ‖q‖ := by rw [hd, hnormq]; ring
      linarith
  · rw [h2] at hnormq
    rcases habs1 with h1 | h1
    · rw [h1] at hd
      have hsum : dist p q = ‖p‖ + ‖q‖ := by rw [hd, hnormq]; ring
      linarith
    · rw [h1] at hd
      have hsum : dist p q + ‖p‖ + ‖q‖ = (0 : ℝ) := by rw [hd, hnormq]; ring
      linarith

/-- `tau3` is cyclically invariant (verbatim twin of LocalAuto12's private
`tau3_cycle`, re-derived here because that lane keeps it `private`). -/
private theorem tau3_cycle_p36 (a b c : V3) : tau3 a b c = tau3 b c a := by
  unfold tau3
  ring

/-- The `B_SY1_p4` flattening map at `m = 3` (verbatim body copy of the
anonymous lambda in `LocalAuto4.B_SY1_p4`'s image). -/
private def bFlat3_p36 (v : Fin 3 → V3) : FinVec 3 3 :=
  fun i : Fin (3 * 3) =>
    (v ⟨(i : ℕ) / 3, (Nat.div_lt_iff_lt_mul (k := 3) (by norm_num)).mpr i.isLt⟩ :
          Fin 3 → ℝ) ⟨(i : ℕ) % 3, Nat.mod_lt (i : ℕ) (by norm_num : 0 < 3)⟩

private theorem rowSy_bFlat3_p36 (v : Fin 3 → V3) (i : Fin 3) :
    rowSy_p23 (bFlat3_p36 v) i = v i := by
  have hv : vecmats_p4 (bFlat3_p36 v) ⟨(i : ℕ), i.isLt⟩ = (v i : Fin 3 → ℝ) := by
    funext k
    simp only [vecmats_p4, bFlat3_p36]
    have hX : (finProdEquiv 3 3 (⟨(i : ℕ), i.isLt⟩, k) : ℕ) = (i : ℕ) * 3 + (k : ℕ) :=
      finProdEquiv_val _ _
    have hlt : (finProdEquiv 3 3 (⟨(i : ℕ), i.isLt⟩, k) : ℕ) < 3 * 3 := by rw [hX]; omega
    have hdiv : (finProdEquiv 3 3 (⟨(i : ℕ), i.isLt⟩, k) : ℕ) / 3 = (i : ℕ) := by
      rw [hX]; omega
    have hmod : (finProdEquiv 3 3 (⟨(i : ℕ), i.isLt⟩, k) : ℕ) % 3 = (k : ℕ) := by
      rw [hX]; omega
    have eA : (⟨(finProdEquiv 3 3 (⟨(i : ℕ), i.isLt⟩, k) : ℕ) / 3,
        Nat.div_lt_iff_lt_mul (k := 3) (by norm_num) |>.mpr hlt⟩ : Fin 3) = i :=
      Fin.ext hdiv
    have eB : (⟨(finProdEquiv 3 3 (⟨(i : ℕ), i.isLt⟩, k) : ℕ) % 3,
        Nat.mod_lt _ (by norm_num : (0 : ℕ) < 3)⟩ : Fin 3) = k :=
      Fin.ext hmod
    rw [eA, eB]
  rw [rowSy_p23, dif_pos i.isLt, vecmatsV3_p4, hv, WithLp.toLp_ofLp]

/-- HOL `IN_NOT_EMPTY_B1_SY_3` (XWITCCN.hl:1470): the row-decoding converse.
The HOL hypothesis `!i. vv i = if i MOD k = 0 then row 3 v else if ...`
is carried as `Periodic vv 3` plus the body conditions on `cycRow_p23 vv 3`
(LocalAuto24 rendering). -/
theorem IN_NOT_EMPTY_B1_SY_3 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
    (hk : s.k = 3) (hper : Periodic vv 3)
    (hball : ∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun (i j : Fin 3) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 3) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      (cycRow_p23 vv 3)) :
    BBsV39 s vv := by
  subst hs
  have hdisj : (mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0))
      (csAdj 3 (2 * h0) 6)).k ≤ 3 := by
    simp only [mkUnadornedV39]; exact le_refl 3
  refine ⟨?_, hper, ?_, Or.inl hdisj⟩
  · rintro _ ⟨n, rfl⟩
    rw [← periodic_mod_eq_p23 hper n]
    have hrow : cycRow_p23 vv 3 ⟨(n % 3 + 2) % 3, by omega⟩ = vv (n % 3) := by
      show vv ((((n % 3 + 2) % 3 + 1) % 3 : ℕ)) = vv (n % 3)
      rw [show (((n % 3 + 2) % 3 + 1) % 3 : ℕ) = n % 3 by omega]
    rw [← hrow]
    exact hball ⟨(n % 3 + 2) % 3, by omega⟩
  · intro i j
    have e1 : (((i % 3 + 2) % 3 + 1) % 3 : ℕ) = i % 3 := by omega
    have e2 : (((j % 3 + 2) % 3 + 1) % 3 : ℕ) = j % 3 := by omega
    have hi3 : (i % 3 + 2) % 3 < 3 := by omega
    have hj3 : (j % 3 + 2) % 3 < 3 := by omega
    obtain ⟨hc1, hc2⟩ := hC1 ⟨(i % 3 + 2) % 3, hi3⟩ ⟨(j % 3 + 2) % 3, hj3⟩
    simp only [change_type_v3] at hc1 hc2
    have hri : cycRow_p23 vv 3 ⟨(i % 3 + 2) % 3, hi3⟩ = vv (i % 3) := by
      show vv ((((i % 3 + 2) % 3 + 1) % 3 : ℕ)) = vv (i % 3)
      rw [e1]
    have hqi : cycRow_p23 vv 3 ⟨(j % 3 + 2) % 3, hj3⟩ = vv (j % 3) := by
      show vv ((((j % 3 + 2) % 3 + 1) % 3 : ℕ)) = vv (j % 3)
      rw [e2]
    rw [hri, hqi] at hc1 hc2
    rw [← periodic_mod_eq_p23 hper i, ← periodic_mod_eq_p23 hper j, dist_eq_norm]
    have hL : csAdj 3 2 (2 * h0) ((i % 3 + 2) % 3 + 1) ((j % 3 + 2) % 3 + 1)
        = csAdj 3 2 (2 * h0) (i % 3) (j % 3) := by
      rw [csAdj_mod_p36 3 2 (2 * h0), e1, e2]
    have hR : csAdj 3 (2 * h0) 6 ((i % 3 + 2) % 3 + 1) ((j % 3 + 2) % 3 + 1)
        = csAdj 3 (2 * h0) 6 (i % 3) (j % 3) := by
      rw [csAdj_mod_p36 3 (2 * h0) 6, e1, e2]
    simp only [mkUnadornedV39] at hc1 hc2
    rw [hL] at hc1
    rw [hR] at hc2
    refine ⟨?_, ?_⟩
    · simp only [mkUnadornedV39]
      rw [csAdj_mod_p36 3 2 (2 * h0) i j]
      exact hc1
    · simp only [mkUnadornedV39]
      rw [csAdj_mod_p36 3 (2 * h0) 6 i j]
      exact hc2

/-- HOL `TRI_STABLE_K_EQ_3` (XWITCCN.hl:1554). -/
theorem TRI_STABLE_K_EQ_3 {k : ℕ} {a b : ℕ → ℕ → ℝ} {J : Set (Set ℕ)}
    (ht : triStable_p23 k 0 (Set.Iic (k - 1)) a b J (fun i => (1 + i) % k)) :
    k = 3 ∧ 2 < k :=
  ⟨ht.2.1, by have := ht.2.1; omega⟩

/-- HOL `POINT_IN_BBS_IS_NOT_0_3` (XWITCCN.hl:1563). -/
theorem POINT_IN_BBS_IS_NOT_0_3 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv) :
    ¬(vv 1 = 0) ∧ ¬(vv 2 = 0) ∧ ¬(vv 0 = 0) :=
  ⟨fun h1 => ballAnnulus_ne_0_p23 _ (hBB.1 (Set.mem_range_self 1)) h1,
   fun h2 => ballAnnulus_ne_0_p23 _ (hBB.1 (Set.mem_range_self 2)) h2,
   fun h0 => ballAnnulus_ne_0_p23 _ (hBB.1 (Set.mem_range_self 0)) h0⟩

/-- HOL `NOT_COLLINEAR_BBs_CASE_3` (XWITCCN.hl:1618). -/
theorem NOT_COLLINEAR_BBs_CASE_3 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
    (hBB : BBsV39 s vv) :
    ¬Collinear ℝ {0, vv 1, vv 2} ∧ ¬Collinear ℝ {0, vv 1, vv 0} ∧
      ¬Collinear ℝ {0, vv 2, vv 0} := by
  subst hs
  have hb := hBB.2.2.1
  simp only [mkUnadornedV39, csAdj] at hb
  exact ⟨
    notCollinear_annulus_pair_p36 (hBB.1 (Set.mem_range_self 1))
      (hBB.1 (Set.mem_range_self 2)) (hb 1 2).1 (hb 1 2).2,
    notCollinear_annulus_pair_p36 (hBB.1 (Set.mem_range_self 1))
      (hBB.1 (Set.mem_range_self 0)) (hb 1 0).1 (hb 1 0).2,
    notCollinear_annulus_pair_p36 (hBB.1 (Set.mem_range_self 2))
      (hBB.1 (Set.mem_range_self 0)) (hb 2 0).1 (hb 2 0).2⟩

/-- HOL `IN_B_SY1_COLLINEAR_CASE_3` (XWITCCN.hl:2027). -/
theorem IN_B_SY1_COLLINEAR_CASE_3 (s : ScsV39)
    (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
    (hk : s.k = 3) :
    ∀ l ∈ B_SY1_p4
      (fun (i j : Fin 3) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 3) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)),
      ¬Collinear ℝ {0, rowSy_p23 l 0, rowSy_p23 l 1} ∧
      ¬Collinear ℝ {0, rowSy_p23 l 0, rowSy_p23 l 2} ∧
      ¬Collinear ℝ {0, rowSy_p23 l 1, rowSy_p23 l 2} := by
  subst hs
  intro l hl
  simp only [B_SY1_p4, Set.mem_image, Set.mem_setOf_eq] at hl
  obtain ⟨v, ⟨hvball, hvC1, -⟩, hvfl⟩ := hl
  subst hvfl
  have b0 := hvball ⟨0, by norm_num⟩
  have b1 := hvball ⟨1, by norm_num⟩
  have b2 := hvball ⟨2, by norm_num⟩
  have h01 := hvC1 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  have h02 := hvC1 ⟨0, by norm_num⟩ ⟨2, by norm_num⟩
  have h12 := hvC1 ⟨1, by norm_num⟩ ⟨2, by norm_num⟩
  simp only [change_type_v3, mkUnadornedV39, csAdj] at h01 h02 h12
  have d01 : (2 : ℝ) ≤ dist (v ⟨0, by norm_num⟩) (v ⟨1, by norm_num⟩) ∧
      dist (v ⟨0, by norm_num⟩) (v ⟨1, by norm_num⟩) ≤ 2 * h0 :=
    ⟨by rw [dist_eq_norm]; exact h01.1, by rw [dist_eq_norm]; exact h01.2⟩
  have d02 : (2 : ℝ) ≤ dist (v ⟨0, by norm_num⟩) (v ⟨2, by norm_num⟩) ∧
      dist (v ⟨0, by norm_num⟩) (v ⟨2, by norm_num⟩) ≤ 2 * h0 :=
    ⟨by rw [dist_eq_norm]; exact h02.1, by rw [dist_eq_norm]; exact h02.2⟩
  have d12 : (2 : ℝ) ≤ dist (v ⟨1, by norm_num⟩) (v ⟨2, by norm_num⟩) ∧
      dist (v ⟨1, by norm_num⟩) (v ⟨2, by norm_num⟩) ≤ 2 * h0 :=
    ⟨by rw [dist_eq_norm]; exact h12.1, by rw [dist_eq_norm]; exact h12.2⟩
  refine ⟨?_, ?_, ?_⟩
  · show ¬Collinear ℝ ({0, rowSy_p23 (bFlat3_p36 v) (0 : ℕ),
      rowSy_p23 (bFlat3_p36 v) (1 : ℕ)} : Set V3)
    rw [rowSy_bFlat3_p36 v ⟨0, by norm_num⟩, rowSy_bFlat3_p36 v ⟨1, by norm_num⟩]
    exact notCollinear_annulus_pair_p36 b0 b1 d01.1 d01.2
  · show ¬Collinear ℝ ({0, rowSy_p23 (bFlat3_p36 v) (0 : ℕ),
      rowSy_p23 (bFlat3_p36 v) (2 : ℕ)} : Set V3)
    rw [rowSy_bFlat3_p36 v ⟨0, by norm_num⟩, rowSy_bFlat3_p36 v ⟨2, by norm_num⟩]
    exact notCollinear_annulus_pair_p36 b0 b2 d02.1 d02.2
  · show ¬Collinear ℝ ({0, rowSy_p23 (bFlat3_p36 v) (1 : ℕ),
      rowSy_p23 (bFlat3_p36 v) (2 : ℕ)} : Set V3)
    rw [rowSy_bFlat3_p36 v ⟨1, by norm_num⟩, rowSy_bFlat3_p36 v ⟨2, by norm_num⟩]
    exact notCollinear_annulus_pair_p36 b1 b2 d12.1 d12.2

/-- HOL `HDPLYGY_CASE_3` (XWITCCN.hl:2098): the `B_SY1` minimiser. -/
theorem HDPLYGY_CASE_3 (k : ℕ) (a b : ℕ → ℕ → ℝ) (J : Set (Set ℕ))
    (ht : triStable_p23 k 0 (Set.Iic (k - 1)) a b J (fun i => (1 + i) % k))
    (hk : k = 3) (h2k : 2 < k)
    (hne : B_SY1_p4 (fun (i j : Fin k) => a ((i : ℕ) + 1) ((j : ℕ) + 1))
      (fun (i j : Fin k) => b ((i : ℕ) + 1) ((j : ℕ) + 1)) ≠ ∅)
    (hcol : ∀ l ∈ B_SY1_p4 (fun (i j : Fin k) => a ((i : ℕ) + 1) ((j : ℕ) + 1))
      (fun (i j : Fin k) => b ((i : ℕ) + 1) ((j : ℕ) + 1)),
      ¬Collinear ℝ {0, rowSy_p23 l 0, rowSy_p23 l 1} ∧
      ¬Collinear ℝ {0, rowSy_p23 l 0, rowSy_p23 l 2} ∧
      ¬Collinear ℝ {0, rowSy_p23 l 1, rowSy_p23 l 2}) :
    ∃ x ∈ B_SY1_p4 (fun (i j : Fin k) => a ((i : ℕ) + 1) ((j : ℕ) + 1))
      (fun (i j : Fin k) => b ((i : ℕ) + 1) ((j : ℕ) + 1)),
      ∀ y ∈ B_SY1_p4 (fun (i j : Fin k) => a ((i : ℕ) + 1) ((j : ℕ) + 1))
        (fun (i j : Fin k) => b ((i : ℕ) + 1) ((j : ℕ) + 1)),
        tau3 (rowSy_p23 x 0) (rowSy_p23 x 1) (rowSy_p23 x 2) ≤
          tau3 (rowSy_p23 y 0) (rowSy_p23 y 1) (rowSy_p23 y 2) := by
  sorry
  -- DISCHARGES: HOL HDPLYGY.hdplygy (taum existence over the tau3 rows of
  -- the finite body set); NEEDS the `tau_fun`-minimisation kit (LocalAuto8
  -- `tauStar_p8` lane, not importable here).

/-- HOL `TAUSTAR_EQ_TAU_STAR_3` (XWITCCN.hl:2283): at `k = 3` the taustar is
the plain `tau3` of rows 1, 2, 0. -/
theorem TAUSTAR_EQ_TAU_STAR_3 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
    (hBB : BBsV39 s vv) :
    taustarV39 s vv = tau3 (vv 1) (vv 2) (vv 0) := by
  have hk : s.k = 3 := by rw [hs]; rfl
  have hd : s.d = dTame 3 := by rw [hs]; rfl
  have hJ : s.J = fun _ _ => False := by rw [hs]; rfl
  unfold taustarV39
  rw [hk, if_pos (le_refl 3), dsv_J_empty s vv hJ, hd]
  have hd3 : dTame 3 = 0 := by unfold dTame; rfl
  rw [hd3, sub_zero]
  exact tau3_cycle_p36 (vv 0) (vv 1) (vv 2)

/-- HOL `XWITCCN_CASE_3` (XWITCCN.hl:2322). -/
theorem XWITCCN_CASE_3 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) (hk : s.k = 3) :
    BBprimeV39 s ≠ ∅ := by
  sorry
  -- DISCHARGES: SCS_3_IS_TRI_STABLE + TRI_STABLE_K_EQ_3 + NOT_EMPTY_CASE_3
  -- + IN_B_SY1_COLLINEAR_CASE_3 + HDPLYGY_CASE_3 (minimiser x) +
  -- IN_NOT_EMPTY_B1_SY_3 + TAUSTAR_EQ_TAU_STAR_3 (hta < 0 transfer).

/-! ## Section 2: the k = 4 system `4I1` (XWITCCN.hl:2429-3231) -/

/-- HOL `PROVE_V_SY_EQ_TAC` (XWITCCN.hl:2446) as a lemma: the `V_SY` image
equality of the `V_E_FF` conjunct at k = 4. -/
theorem PROVE_V_SY_EQ_TAC (vv : ℕ → V3) (hper : Periodic vv 4) :
    V_SY_p4 (cycRow_p23 vv 4) = Set.range vv :=
  vSy_eq_range_p36 (by norm_num) hper

/-- HOL `PROVE_E_SY_EQ_TAC` (XWITCCN.hl:2456) as a lemma: the `E_SY` image
equality at k = 4. -/
theorem PROVE_E_SY_EQ_TAC (vv : ℕ → V3) (hper : Periodic vv 4) :
    E_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) :=
  eSy_eq_range_p36 (by norm_num) hper

/-- HOL `PROVE_EQ_V_SY_TAC_4` (XWITCCN.hl:2464) as a lemma: the inverse
`range vv = V_SY` form. -/
theorem PROVE_EQ_V_SY_TAC_4 (vv : ℕ → V3) (hper : Periodic vv 4) :
    Set.range vv = V_SY_p4 (cycRow_p23 vv 4) :=
  (vSy_eq_range_p36 (by norm_num) hper).symm

/-- HOL `PROVE_F_SY_EQ_TAC` (XWITCCN.hl:2474) as a lemma: the `F_SY` image
equality at k = 4. -/
theorem PROVE_F_SY_EQ_TAC (vv : ℕ → V3) (hper : Periodic vv 4) :
    F_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => (vv i, vv (i + 1))) :=
  fSy_eq_range_p36 (by norm_num) hper

/-- HOL `PROOF_E_EQ_IMAGE_4` (XWITCCN.hl:2481) as a lemma. -/
theorem PROOF_E_EQ_IMAGE_4 (vv : ℕ → V3) (hper : Periodic vv 4) (x : Set V3)
    (hx : x ∈ E_SY_p4 (cycRow_p23 vv 4)) :
    x ∈ Set.range (fun i : ℕ => {vv i, vv (i + 1)}) := by
  rw [eSy_eq_range_p36 (by norm_num) hper] at hx
  exact hx

/-- HOL `V_E_FF_CASE_4` (XWITCCN.hl:2496): the three image equalities of the
`BBsV39` fan conjunct (proved; periodicity comes from `BBsV39` itself). -/
theorem V_E_FF_CASE_4 (s : ScsV39) (vv : ℕ → V3)
    (_hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4) :
    V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
    F_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => (vv i, vv (i + 1))) := by
  have hper : Periodic vv 4 := by rw [← hk]; exact hBB.2.1
  exact ⟨vSy_eq_range_p36 (by norm_num) hper, eSy_eq_range_p36 (by norm_num) hper,
    fSy_eq_range_p36 (by norm_num) hper⟩

/-- HOL `IN_BALL_ANNULUS_ROW_TAC_4` (XWITCCN.hl:2631) as a lemma: row `i` of
the k = 4 cyclic matrix lies in the annulus. -/
theorem IN_BALL_ANNULUS_ROW_TAC_4 (vv : ℕ → V3) (hper : Periodic vv 4)
    (hsub : Set.range vv ⊆ ballAnnulus) (i : Fin 4) :
    cycRow_p23 vv 4 i ∈ ballAnnulus := by
  have h : cycRow_p23 vv 4 i = vv ((i : ℕ) + 1) := periodic_mod_eq_p23 hper _
  rw [h]
  exact hsub (Set.mem_range_self ((i : ℕ) + 1))

/-- HOL `INEQUALITY_PROOF_TAC40` (XWITCCN.hl:2645) as a lemma: the a/b bound
conjunct (one residue case). -/
theorem INEQUALITY_PROOF_TAC40 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  hBB.2.2.1 i j

/-- HOL `INEQUALITY_PROOF_TAC4` (XWITCCN.hl:2657): the `j MOD 4` case
machine. -/
theorem INEQUALITY_PROOF_TAC4 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  INEQUALITY_PROOF_TAC40 s vv hBB i j

/-- HOL `IN_NOT_EMPTY_CASE_4` (XWITCCN.hl:2671). -/
theorem IN_NOT_EMPTY_CASE_4 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4) :
    flattenRow_p23 vv 4 ∈ B_SY1_p4
      (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
  sorry
  -- DISCHARGES: BBsV39 unpack — annulus rows via IN_BALL_ANNULUS_ROW_TAC_4 /
  -- VECTOR_3_4, CONDITION1 via the cs_adj ladder, CONDITION2 via
  -- V_E_FF_CASE_4 (fan conjunct of BBsV39).
  -- NEEDS (family blocker for all k ≥ 4 IN_NOT_EMPTY_CASE/B1_SY twins): the
  -- registry `ConvexLocalFan` (LA1: sigmaFan/ee/wedgeGe vocabulary) vs the
  -- `_p4` `convexLocalFan_p4` (LA4: azimCycle_p4/EE_p4/wedgeGe_p4) def-bridge:
  -- azimCycle_p4 (EE_p4 v E) 0 v u = sigmaFan 0 Set.univ E v u (fan-hypothetic),
  -- wedgeGe_p4 = wedgeGe, EE_p4 = ee, plus localFan_p4 → LocalFan(=True).

/-- HOL `NOT_EMPTY_CASE_4` (XWITCCN.hl:2737). -/
theorem NOT_EMPTY_CASE_4 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4) :
    B_SY1_p4
      (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp
    (⟨flattenRow_p23 vv 4, IN_NOT_EMPTY_CASE_4 s vv hs hBB hk⟩ :
      (B_SY1_p4
        (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
        (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))).Nonempty)

/-- HOL `TAUSTAR_EQ_TAU_STAR_4` (XWITCCN.hl:2763). The HOL record equation
`stable_sy (k,d,0..k-1, change_type_v3 (scs_a_v39 s), ..., (\i. (1+i) MOD k)) = s1`
is carried as `s1 = scsToStableSy_p23 s` (the change_type bookkeeping
collapses to the kit fields, cf. `change_type_v2_eq`). -/
theorem TAUSTAR_EQ_TAU_STAR_4 (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
    (l : FinVec 4 3)
    (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4)
    (hs1 : s1 = scsToStableSy_p23 s) (hl : flattenRow_p23 vv 4 = l) :
    taustarV39 s vv = tauStar_p23 s1 l := by
  sorry
  -- DISCHARGES: taustarV39 `k > 3` branch (tauFun over V/E/F from
  -- V_E_FF_CASE_4) + dFun J-empty (mkUnadornedV39) + stable_sy_explicit.
  -- NEEDS (statement doubt, cf. HANDOFF ①): as ported, s1 = scsToStableSy_p23 s
  -- carries d = 0, so tauStar_p23 s1 l = tauFun(...) - 0, while taustarV39 s vv
  -- = tauFun(...) - dTame k (≠ 0 for k ≥ 4). The HOL source fixes
  -- s1.d := scs_d_v39 s; the Lean statement needs s1.d := dTame k before it is
  -- provable. Statement left untouched here; same for all k ≥ 4 TAUSTAR twins.

/-- HOL `VV_IN_BALL_ANNULUS_TAC_4` (XWITCCN.hl:2836) as a lemma. -/
theorem VV_IN_BALL_ANNULUS_TAC_4 (vv : ℕ → V3) (hsub : Set.range vv ⊆ ballAnnulus)
    (i : ℕ) : vv i ∈ ballAnnulus :=
  hsub (Set.mem_range_self i)

/-- HOL `SCS_A_B__EQ_MOD_4` (XWITCCN.hl:2848). -/
theorem SCS_A_B__EQ_MOD_4 (s : ScsV39)
    (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
    (i j : ℕ) :
    s.a i j = s.a (i % 4) (j % 4) ∧ s.b i j = s.b (i % 4) (j % 4) := by
  subst hs
  exact ⟨csAdj_mod_p36 4 2 (2 * h0) i j, csAdj_mod_p36 4 (2 * h0) 6 i j⟩

/-- HOL `PROVE_INEQUALITY_TAC_40` (XWITCCN.hl:2868) as a lemma. -/
theorem PROVE_INEQUALITY_TAC_40 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  hBB.2.2.1 i j

/-- HOL `PROVE_INEQUALITY_TAC_4` (XWITCCN.hl:2893): the `j MOD 4` case
machine. -/
theorem PROVE_INEQUALITY_TAC_4 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  PROVE_INEQUALITY_TAC_40 s vv hBB i j

/-- HOL `V_SY_EQ_IMAGE_VV_TAC4` (XWITCCN.hl:2905) as a lemma: `V_SY`
membership by witness (the `fun th -> EXISTS_TAC th` tactic). -/
theorem V_SY_EQ_IMAGE_VV_TAC4 (vv : ℕ → V3) (hper : Periodic vv 4) (x : V3)
    (hx : x ∈ Set.range vv) : x ∈ V_SY_p4 (cycRow_p23 vv 4) := by
  rw [vSy_eq_range_p36 (by norm_num) hper]
  exact hx

/-- HOL `PROVE_E_SY_EQ_MOD_TAC_4` (XWITCCN.hl:2913) as a lemma: edge
membership by witness index. -/
theorem PROVE_E_SY_EQ_MOD_TAC_4 (vv : ℕ → V3) (hper : Periodic vv 4) (i : ℕ) :
    {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 4) := by
  obtain ⟨j, hj1, hj2⟩ := cycRow_shift_p36 (by norm_num) hper i
  exact ⟨j, Set.mem_univ j, by simp only; rw [hj1, hj2]⟩

/-- HOL `PROVE_E_SY_EQ_IMAGE_VV_4` (XWITCCN.hl:2921) as a lemma. -/
theorem PROVE_E_SY_EQ_IMAGE_VV_4 (vv : ℕ → V3) (hper : Periodic vv 4) (x : Set V3)
    (hx : x ∈ Set.range (fun i : ℕ => {vv i, vv (i + 1)})) :
    x ∈ E_SY_p4 (cycRow_p23 vv 4) := by
  rw [eSy_eq_range_p36 (by norm_num) hper]
  exact hx

/-- HOL `PROOF_E_EQ_TAC_4` (XWITCCN.hl:2933) as a lemma: edge membership by
witness (`fun th -> EXISTS_TAC th`). -/
theorem PROOF_E_EQ_TAC_4 (vv : ℕ → V3) (hper : Periodic vv 4) (i : ℕ) :
    {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 4) :=
  PROVE_E_SY_EQ_MOD_TAC_4 vv hper i

/-- HOL `IN_NOT_EMPTY_B1_SY_4` (XWITCCN.hl:2941): row-decoding converse. -/
theorem IN_NOT_EMPTY_B1_SY_4 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
    (hk : s.k = 4) (hper : Periodic vv 4)
    (hball : ∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      (cycRow_p23 vv 4))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 4)) :
    BBsV39 s vv := by
  sorry
  -- DISCHARGES: BBsV39 conjunct walk — annulus range lifted by periodicity,
  -- the cs_adj bound ladder, fan conjunct via V_E_FF_CASE_4 + CONDITION2_SY_p4.

/-- HOL `XWITCCN_CASE_4` (XWITCCN.hl:3118). -/
theorem XWITCCN_CASE_4 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) (hk : s.k = 4) :
    BBprimeV39 s ≠ ∅ := by
  sorry
  -- DISCHARGES: IS_SCS_STABLE_SYSTEM_p23 (hs, k = 4) + NOT_EMPTY_CASE_4 +
  -- IN_B_SY1_COLLINEAR-style row kit + HDPLYGY minimiser + IN_NOT_EMPTY_B1_SY_4
  -- + TAUSTAR_EQ_TAU_STAR_4 (hta < 0 transfer).

/-! ## Section 3: the k = 5 system `5I1` (XWITCCN.hl:3232-4071) -/

/-- HOL `EQUALITY_V_SY_TAC_5` (XWITCCN.hl:3247) as a lemma. -/
theorem EQUALITY_V_SY_TAC_5 (vv : ℕ → V3) (hper : Periodic vv 5) :
    V_SY_p4 (cycRow_p23 vv 5) = Set.range vv :=
  vSy_eq_range_p36 (by norm_num) hper

/-- HOL `PROVE_V_SY_EQ_5_TAC` (XWITCCN.hl:3258) as a lemma. -/
theorem PROVE_V_SY_EQ_5_TAC (vv : ℕ → V3) (hper : Periodic vv 5) :
    V_SY_p4 (cycRow_p23 vv 5) = Set.range vv :=
  vSy_eq_range_p36 (by norm_num) hper

/-- HOL `PROVE_E_SY_EQ_5_TAC` (XWITCCN.hl:3266) as a lemma. -/
theorem PROVE_E_SY_EQ_5_TAC (vv : ℕ → V3) (hper : Periodic vv 5) :
    E_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) :=
  eSy_eq_range_p36 (by norm_num) hper

/-- HOL `PROVE_E_SY_EQ_INV_5_TAC` (XWITCCN.hl:3290, shadowing the :3279
copy) as a lemma: the inverse `range = E_SY` form. -/
theorem PROVE_E_SY_EQ_INV_5_TAC (vv : ℕ → V3) (hper : Periodic vv 5) :
    Set.range (fun i : ℕ => {vv i, vv (i + 1)}) = E_SY_p4 (cycRow_p23 vv 5) :=
  (eSy_eq_range_p36 (by norm_num) hper).symm

/-- HOL `V_E_FF_CASE_5` (XWITCCN.hl:3306) — proved. -/
theorem V_E_FF_CASE_5 (s : ScsV39) (vv : ℕ → V3)
    (_hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5) :
    V_SY_p4 (cycRow_p23 vv 5) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
    F_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => (vv i, vv (i + 1))) := by
  have hper : Periodic vv 5 := by rw [← hk]; exact hBB.2.1
  exact ⟨vSy_eq_range_p36 (by norm_num) hper, eSy_eq_range_p36 (by norm_num) hper,
    fSy_eq_range_p36 (by norm_num) hper⟩

/-- HOL `IN_BALL_ANNUUS_TAC_5` (XWITCCN.hl:3434) as a lemma. -/
theorem IN_BALL_ANNUUS_TAC_5 (vv : ℕ → V3) (hper : Periodic vv 5)
    (hsub : Set.range vv ⊆ ballAnnulus) (i : Fin 5) :
    cycRow_p23 vv 5 i ∈ ballAnnulus := by
  have h : cycRow_p23 vv 5 i = vv ((i : ℕ) + 1) := periodic_mod_eq_p23 hper _
  rw [h]
  exact hsub (Set.mem_range_self ((i : ℕ) + 1))

/-- HOL `INEQUALITY_A_B_TAC_50` (XWITCCN.hl:3448) as a lemma. -/
theorem INEQUALITY_A_B_TAC_50 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  hBB.2.2.1 i j

/-- HOL `INEQUALITY_A_B_TAC_5` (XWITCCN.hl:3461): the `j MOD 5` case
machine. -/
theorem INEQUALITY_A_B_TAC_5 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  INEQUALITY_A_B_TAC_50 s vv hBB i j

/-- HOL `IN_NOT_EMPTY_CASE_5` (XWITCCN.hl:3476). -/
theorem IN_NOT_EMPTY_CASE_5 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5) :
    flattenRow_p23 vv 5 ∈ B_SY1_p4
      (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
  sorry
  -- DISCHARGES: BBsV39 unpack — annulus rows via IN_BALL_ANNUUS_TAC_5 /
  -- VECTOR_3_5, CONDITION1 via the cs_adj ladder, CONDITION2 via
  -- V_E_FF_CASE_5.

/-- HOL `NOT_EMPTY_CASE_5` (XWITCCN.hl:3543). -/
theorem NOT_EMPTY_CASE_5 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5) :
    B_SY1_p4
      (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp
    (⟨flattenRow_p23 vv 5, IN_NOT_EMPTY_CASE_5 s vv hs hBB hk⟩ :
      (B_SY1_p4
        (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
        (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))).Nonempty)

/-- HOL `TAUSTAR_EQ_TAU_STAR_5` (XWITCCN.hl:3577). -/
theorem TAUSTAR_EQ_TAU_STAR_5 (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
    (l : FinVec 5 3)
    (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5)
    (hs1 : s1 = scsToStableSy_p23 s) (hl : flattenRow_p23 vv 5 = l) :
    taustarV39 s vv = tauStar_p23 s1 l := by
  sorry
  -- DISCHARGES: as TAUSTAR_EQ_TAU_STAR_4 at k = 5.

/-- HOL `VV_IN_BALL_ANNULUS_TAC_5` (XWITCCN.hl:3654) as a lemma. -/
theorem VV_IN_BALL_ANNULUS_TAC_5 (vv : ℕ → V3) (hsub : Set.range vv ⊆ ballAnnulus)
    (i : ℕ) : vv i ∈ ballAnnulus :=
  hsub (Set.mem_range_self i)

/-- HOL `SCS_A_B__EQ_MOD_5` (XWITCCN.hl:3636). -/
theorem SCS_A_B__EQ_MOD_5 (s : ScsV39)
    (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
    (i j : ℕ) :
    s.a i j = s.a (i % 5) (j % 5) ∧ s.b i j = s.b (i % 5) (j % 5) := by
  subst hs
  exact ⟨csAdj_mod_p36 5 2 (2 * h0) i j, csAdj_mod_p36 5 (2 * h0) 6 i j⟩

/-- HOL `PROVE_INEQUALITY_TAC_50` (XWITCCN.hl:3661) as a lemma. -/
theorem PROVE_INEQUALITY_TAC_50 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  hBB.2.2.1 i j

/-- HOL `PROVE_INEQUALITY_TAC_5` (XWITCCN.hl:3689): the `j MOD 5` case
machine. -/
theorem PROVE_INEQUALITY_TAC_5 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  PROVE_INEQUALITY_TAC_50 s vv hBB i j

/-- HOL `V_SY_EQ_IMAGE_VV_TAC5` (XWITCCN.hl:3703) as a lemma. -/
theorem V_SY_EQ_IMAGE_VV_TAC5 (vv : ℕ → V3) (hper : Periodic vv 5) (x : V3)
    (hx : x ∈ Set.range vv) : x ∈ V_SY_p4 (cycRow_p23 vv 5) := by
  rw [vSy_eq_range_p36 (by norm_num) hper]
  exact hx

/-- HOL `PROVE_E_SY_EQ_MOD_TAC_5` (XWITCCN.hl:3713) as a lemma. -/
theorem PROVE_E_SY_EQ_MOD_TAC_5 (vv : ℕ → V3) (hper : Periodic vv 5) (i : ℕ) :
    {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 5) := by
  obtain ⟨j, hj1, hj2⟩ := cycRow_shift_p36 (by norm_num) hper i
  exact ⟨j, Set.mem_univ j, by simp only; rw [hj1, hj2]⟩

/-- HOL `PROOF_E_EQ_TAC_5` (XWITCCN.hl:3725) as a lemma. -/
theorem PROOF_E_EQ_TAC_5 (vv : ℕ → V3) (hper : Periodic vv 5) (i : ℕ) :
    {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 5) :=
  PROVE_E_SY_EQ_MOD_TAC_5 vv hper i

/-- HOL `PROVE_E_SY_EQ_IMAGE_VV_5` (XWITCCN.hl:3734) as a lemma. -/
theorem PROVE_E_SY_EQ_IMAGE_VV_5 (vv : ℕ → V3) (hper : Periodic vv 5) (x : Set V3)
    (hx : x ∈ Set.range (fun i : ℕ => {vv i, vv (i + 1)})) :
    x ∈ E_SY_p4 (cycRow_p23 vv 5) := by
  rw [eSy_eq_range_p36 (by norm_num) hper]
  exact hx

/-- HOL `IN_NOT_EMPTY_B1_SY_5` (XWITCCN.hl:3750): row-decoding converse. -/
theorem IN_NOT_EMPTY_B1_SY_5 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
    (hk : s.k = 5) (hper : Periodic vv 5)
    (hball : ∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      (cycRow_p23 vv 5))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 5)) :
    BBsV39 s vv := by
  sorry
  -- DISCHARGES: as IN_NOT_EMPTY_B1_SY_4 at k = 5 (fan conjunct via
  -- V_E_FF_CASE_5).

/-- HOL `XWITCCN_CASE_5` (XWITCCN.hl:3954). -/
theorem XWITCCN_CASE_5 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) (hk : s.k = 5) :
    BBprimeV39 s ≠ ∅ := by
  sorry
  -- DISCHARGES: as XWITCCN_CASE_4 at k = 5.

/-! ## Section 3.5: the remaining `IS_TRI_STABLE` statements (source lines
471-1270, grouped; each is the k-wise twin of `SCS_3_IS_TRI_STABLE`) -/

/- Numeric yardsticks of the eight concrete tables (h0 = 1.26, cstab = 3.01). -/
private theorem two_le_2h0_p36 : (2 : ℝ) ≤ 2 * h0 := by rw [h0]; norm_num
private theorem twoh0_le_cstab_p36 : 2 * h0 ≤ cstab := by rw [h0, cstab]; norm_num
private theorem twoh0_le_six_p36 : 2 * h0 ≤ 6 := by rw [h0]; norm_num
private theorem two_le_sqrt8_p36 : (2 : ℝ) ≤ Real.sqrt 8 :=
  (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
private theorem sqrt8_le_six_p36 : Real.sqrt 8 ≤ 6 :=
  (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
private theorem sqrt8_le_cstab_p36 : Real.sqrt 8 ≤ cstab := by
  rw [cstab]; exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
private theorem twoh0_le_sqrt8_p36 : 2 * h0 ≤ Real.sqrt 8 := by
  rw [h0]; exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)

/-- HOL `SCS_4_IS_TRI_STABLE` (XWITCCN.hl:471): `4I1` is `stable_system`. -/
theorem SCS_4_IS_TRI_STABLE (s : ScsV39)
    (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6)) :
    stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
      (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
      (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k) := by
  have hk : s.k = 4 := by rw [hs]; rfl
  have ha : s.a = csAdj 4 2 (2 * h0) := by rw [hs]; rfl
  have hb : s.b = csAdj 4 (2 * h0) 6 := by rw [hs]; rfl
  have hJ : change_type_v2 s.J 4 = ∅ := by
    rw [hs]; exact change_type_v2_mkUnadorned_p36 _ _ _
  rw [hk, ha, hb, hJ]
  simpa only [change_type_v3] using
    stableSystem_csAdj_succ_p36 (k := 4) (by norm_num) (by norm_num) (2 * h0) 6
      two_le_2h0_p36 (by rw [h0]; norm_num)

/-- HOL `SCS_5_IS_TRI_STABLE` (XWITCCN.hl:577). -/
theorem SCS_5_IS_TRI_STABLE (s : ScsV39)
    (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6)) :
    stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
      (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
      (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k) := by
  have hk : s.k = 5 := by rw [hs]; rfl
  have ha : s.a = csAdj 5 2 (2 * h0) := by rw [hs]; rfl
  have hb : s.b = csAdj 5 (2 * h0) 6 := by rw [hs]; rfl
  have hJ : change_type_v2 s.J 5 = ∅ := by
    rw [hs]; exact change_type_v2_mkUnadorned_p36 _ _ _
  rw [hk, ha, hb, hJ]
  simpa only [change_type_v3] using
    stableSystem_csAdj_succ_p36 (k := 5) (by norm_num) (by norm_num) (2 * h0) 6
      two_le_2h0_p36 (by rw [h0]; norm_num)

/-- HOL `SCS_6_IS_TRI_STABLE` (XWITCCN.hl:685). -/
theorem SCS_6_IS_TRI_STABLE (s : ScsV39)
    (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6)) :
    stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
      (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
      (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k) := by
  have hk : s.k = 6 := by rw [hs]; rfl
  have ha : s.a = csAdj 6 2 (2 * h0) := by rw [hs]; rfl
  have hb : s.b = csAdj 6 (2 * h0) 6 := by rw [hs]; rfl
  have hJ : change_type_v2 s.J 6 = ∅ := by
    rw [hs]; exact change_type_v2_mkUnadorned_p36 _ _ _
  rw [hk, ha, hb, hJ]
  simpa only [change_type_v3] using
    stableSystem_csAdj_succ_p36 (k := 6) (by norm_num) (by norm_num) (2 * h0) 6
      two_le_2h0_p36 (by rw [h0]; norm_num)

/-- HOL `SCS_4_3_IS_TRI_STABLE` (XWITCCN.hl:797): the `4_3` system. -/
theorem SCS_4_3_IS_TRI_STABLE (s : ScsV39)
    (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6)) :
    stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
      (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
      (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k) := by
  have hk : s.k = 4 := by rw [hs]; rfl
  have ha : s.a = csAdj 4 2 3 := by rw [hs]; rfl
  have hb : s.b = csAdj 4 (2 * h0) 6 := by rw [hs]; rfl
  have hJ : change_type_v2 s.J 4 = ∅ := by
    rw [hs]; exact change_type_v2_mkUnadorned_p36 _ _ _
  rw [hk, ha, hb, hJ]
  simpa only [change_type_v3] using
    stableSystem_csAdj_succ_p36 (k := 4) (by norm_num) (by norm_num) 3 6
      (by norm_num) (by norm_num)

/-- HOL `SCS_5_sqrt8_IS_TRI_STABLE` (XWITCCN.hl:905): the `5_sqrt8` system. -/
theorem SCS_5_sqrt8_IS_TRI_STABLE (s : ScsV39)
    (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6)) :
    stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
      (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
      (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k) := by
  have hk : s.k = 5 := by rw [hs]; rfl
  have ha : s.a = csAdj 5 2 (Real.sqrt 8) := by rw [hs]; rfl
  have hb : s.b = csAdj 5 (2 * h0) 6 := by rw [hs]; rfl
  have hJ : change_type_v2 s.J 5 = ∅ := by
    rw [hs]; exact change_type_v2_mkUnadorned_p36 _ _ _
  rw [hk, ha, hb, hJ]
  simpa only [change_type_v3] using
    stableSystem_csAdj_succ_p36 (k := 5) (by norm_num) (by norm_num) (Real.sqrt 8) 6
      two_le_sqrt8_p36 sqrt8_le_six_p36

/-- HOL `SCS_4_sqrt8_IS_TRI_STABLE` (XWITCCN.hl:1024): the `4_sqrt8` system
(`a_pro` tables). -/
theorem SCS_4_sqrt8_IS_TRI_STABLE (s : ScsV39)
    (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
      (aPro 4 (Real.sqrt 8) (2 * h0) 6)) :
    stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
      (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
      (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k) := by
  have hk : s.k = 4 := by rw [hs]; rfl
  have ha : s.a = aPro 4 (2 * h0) 2 (Real.sqrt 8) := by rw [hs]; rfl
  have hb : s.b = aPro 4 (Real.sqrt 8) (2 * h0) 6 := by rw [hs]; rfl
  have hJ : change_type_v2 s.J 4 = ∅ := by
    rw [hs]; exact change_type_v2_mkUnadorned_p36 _ _ _
  rw [hk, ha, hb, hJ]
  simpa only [change_type_v3] using
    stableSystem_aPro_succ_p36 (k := 4) (by norm_num) (by norm_num) (2 * h0) 2
      (Real.sqrt 8) (Real.sqrt 8) (2 * h0) 6
      two_le_2h0_p36 twoh0_le_sqrt8_p36 le_rfl two_le_2h0_p36 sqrt8_le_six_p36
      ⟨sqrt8_le_cstab_p36, twoh0_le_cstab_p36⟩ two_le_sqrt8_p36

/-- HOL `SCS_5_pro_cs_IS_TRI_STABLE` (XWITCCN.hl:1147): the `5_pro_cs`
system (`a_pro` tables). -/
theorem SCS_5_pro_cs_IS_TRI_STABLE (s : ScsV39)
    (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
      (aPro 5 (Real.sqrt 8) (2 * h0) 6)) :
    stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
      (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
      (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k) := by
  have hk : s.k = 5 := by rw [hs]; rfl
  have ha : s.a = aPro 5 (2 * h0) 2 (2 * h0) := by rw [hs]; rfl
  have hb : s.b = aPro 5 (Real.sqrt 8) (2 * h0) 6 := by rw [hs]; rfl
  have hJ : change_type_v2 s.J 5 = ∅ := by
    rw [hs]; exact change_type_v2_mkUnadorned_p36 _ _ _
  rw [hk, ha, hb, hJ]
  simpa only [change_type_v3] using
    stableSystem_aPro_succ_p36 (k := 5) (by norm_num) (by norm_num) (2 * h0) 2
      (2 * h0) (Real.sqrt 8) (2 * h0) 6
      two_le_2h0_p36 twoh0_le_sqrt8_p36 le_rfl two_le_2h0_p36 twoh0_le_six_p36
      ⟨sqrt8_le_cstab_p36, twoh0_le_cstab_p36⟩ two_le_2h0_p36

/-! ## Section 3.6: the `4_sqrt8`-tail tactic helpers (source lines
7176-7261; new names only — the shadowed copies of `VV_IN_BALL_ANNULUS_TAC_4`,
`PROVE_INEQUALITY_TAC_40/4`, `V_SY_EQ_IMAGE_VV_TAC4`, `PROVE_E_SY_EQ_MOD_TAC_4`,
`PROVE_E_SY_EQ_IMAGE_VV_4`, `PROOF_E_EQ_TAC_4`, `PROVE_V_SY_EQ_TAC`,
`PROVE_E_SY_EQ_TAC` are the lemmas above) -/

/-- HOL `EQ_V_SY_TAC_4` (XWITCCN.hl:7222) as a lemma. -/
theorem EQ_V_SY_TAC_4 (vv : ℕ → V3) (hper : Periodic vv 4) :
    Set.range vv = V_SY_p4 (cycRow_p23 vv 4) :=
  (vSy_eq_range_p36 (by norm_num) hper).symm

/-- HOL `PROVE_E_SY_INV_TAC_4` (XWITCCN.hl:7252) as a lemma: the inverse
`range = E_SY` form at k = 4. -/
theorem PROVE_E_SY_INV_TAC_4 (vv : ℕ → V3) (hper : Periodic vv 4) :
    Set.range (fun i : ℕ => {vv i, vv (i + 1)}) = E_SY_p4 (cycRow_p23 vv 4) :=
  (eSy_eq_range_p36 (by norm_num) hper).symm

/-- HOL `IN_BALL_ANNULUS_TAC_4` (XWITCCN.hl:7176) as a lemma. -/
theorem IN_BALL_ANNULUS_TAC_4 (vv : ℕ → V3) (hper : Periodic vv 4)
    (hsub : Set.range vv ⊆ ballAnnulus) (i : Fin 4) :
    cycRow_p23 vv 4 i ∈ ballAnnulus :=
  IN_BALL_ANNULUS_ROW_TAC_4 vv hper hsub i

/-- HOL `INEQUALITY_A_B_TAC_40` (XWITCCN.hl:7195) as a lemma (the shadowed
copies for `4I1` / `4_3` / `4_sqrt8` collapse to this one lemma). -/
theorem INEQUALITY_A_B_TAC_40 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  hBB.2.2.1 i j

/-- HOL `INEQUALITY_A_B_TAC_4` (XWITCCN.hl:7209): the `j MOD 4` case
machine (shadowed copies likewise collapsed). -/
theorem INEQUALITY_A_B_TAC_4 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  INEQUALITY_A_B_TAC_40 s vv hBB i j

/-! ## Section 4: the k = 6 system `6I1` (XWITCCN.hl:4072-4972) -/

/-- HOL `EQUALITY_V_SY_TAC_6` (XWITCCN.hl:4125) as a lemma. -/
theorem EQUALITY_V_SY_TAC_6 (vv : ℕ → V3) (hper : Periodic vv 6) :
    V_SY_p4 (cycRow_p23 vv 6) = Set.range vv :=
  vSy_eq_range_p36 (by norm_num) hper

/-- HOL `PROVE_V_SY_EQ_6_TAC` (XWITCCN.hl:4136) as a lemma. -/
theorem PROVE_V_SY_EQ_6_TAC (vv : ℕ → V3) (hper : Periodic vv 6) :
    V_SY_p4 (cycRow_p23 vv 6) = Set.range vv :=
  vSy_eq_range_p36 (by norm_num) hper

/-- HOL `PROVE_E_SY_EQ_6_TAC` (XWITCCN.hl:4146) as a lemma. -/
theorem PROVE_E_SY_EQ_6_TAC (vv : ℕ → V3) (hper : Periodic vv 6) :
    E_SY_p4 (cycRow_p23 vv 6) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) :=
  eSy_eq_range_p36 (by norm_num) hper

/-- HOL `PROVE_E_SY_EQ_INV_6_TAC` (XWITCCN.hl:4160) as a lemma. -/
theorem PROVE_E_SY_EQ_INV_6_TAC (vv : ℕ → V3) (hper : Periodic vv 6) :
    Set.range (fun i : ℕ => {vv i, vv (i + 1)}) = E_SY_p4 (cycRow_p23 vv 6) :=
  (eSy_eq_range_p36 (by norm_num) hper).symm

/-- HOL `V_E_FF_CASE_6` (XWITCCN.hl:4173) — proved. -/
theorem V_E_FF_CASE_6 (s : ScsV39) (vv : ℕ → V3)
    (_hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 6) :
    V_SY_p4 (cycRow_p23 vv 6) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 6) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
    F_SY_p4 (cycRow_p23 vv 6) = Set.range (fun i : ℕ => (vv i, vv (i + 1))) := by
  have hper : Periodic vv 6 := by rw [← hk]; exact hBB.2.1
  exact ⟨vSy_eq_range_p36 (by norm_num) hper, eSy_eq_range_p36 (by norm_num) hper,
    fSy_eq_range_p36 (by norm_num) hper⟩

/-- HOL `IN_BALL_ANNUUS_TAC_6` (XWITCCN.hl:4086) as a lemma. -/
theorem IN_BALL_ANNUUS_TAC_6 (vv : ℕ → V3) (hper : Periodic vv 6)
    (hsub : Set.range vv ⊆ ballAnnulus) (i : Fin 6) :
    cycRow_p23 vv 6 i ∈ ballAnnulus := by
  have h : cycRow_p23 vv 6 i = vv ((i : ℕ) + 1) := periodic_mod_eq_p23 hper _
  rw [h]
  exact hsub (Set.mem_range_self ((i : ℕ) + 1))

/-- HOL `INEQUALITY_A_B_TAC_60` (XWITCCN.hl:4099) as a lemma. -/
theorem INEQUALITY_A_B_TAC_60 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  hBB.2.2.1 i j

/-- HOL `INEQUALITY_A_B_TAC_6` (XWITCCN.hl:4112): the `j MOD 6` case
machine. -/
theorem INEQUALITY_A_B_TAC_6 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  INEQUALITY_A_B_TAC_60 s vv hBB i j

/-- HOL `IN_NOT_EMPTY_CASE_6` (XWITCCN.hl:4309). -/
theorem IN_NOT_EMPTY_CASE_6 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 6) :
    flattenRow_p23 vv 6 ∈ B_SY1_p4
      (fun (i j : Fin 6) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 6) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
  sorry
  -- DISCHARGES: BBsV39 unpack — annulus rows, cs_adj ladder, CONDITION2 via
  -- V_E_FF_CASE_6.

/-- HOL `NOT_EMPTY_CASE_6` (XWITCCN.hl:4378). -/
theorem NOT_EMPTY_CASE_6 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 6) :
    B_SY1_p4
      (fun (i j : Fin 6) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 6) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp
    (⟨flattenRow_p23 vv 6, IN_NOT_EMPTY_CASE_6 s vv hs hBB hk⟩ :
      (B_SY1_p4
        (fun (i j : Fin 6) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
        (fun (i j : Fin 6) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))).Nonempty)

/-- HOL `TAUSTAR_EQ_TAU_STAR_6` (XWITCCN.hl:4402). -/
theorem TAUSTAR_EQ_TAU_STAR_6 (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
    (l : FinVec 6 3)
    (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 6)
    (hs1 : s1 = scsToStableSy_p23 s) (hl : flattenRow_p23 vv 6 = l) :
    taustarV39 s vv = tauStar_p23 s1 l := by
  sorry
  -- DISCHARGES: as TAUSTAR_EQ_TAU_STAR_4 at k = 6.

/-- HOL `VV_IN_BALL_ANNULUS_TAC_6` (XWITCCN.hl:4495) as a lemma. -/
theorem VV_IN_BALL_ANNULUS_TAC_6 (vv : ℕ → V3) (hsub : Set.range vv ⊆ ballAnnulus)
    (i : ℕ) : vv i ∈ ballAnnulus :=
  hsub (Set.mem_range_self i)

/-- HOL `SCS_A_B__EQ_MOD_6` (XWITCCN.hl:4476). -/
theorem SCS_A_B__EQ_MOD_6 (s : ScsV39)
    (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
    (i j : ℕ) :
    s.a i j = s.a (i % 6) (j % 6) ∧ s.b i j = s.b (i % 6) (j % 6) := by
  subst hs
  exact ⟨csAdj_mod_p36 6 2 (2 * h0) i j, csAdj_mod_p36 6 (2 * h0) 6 i j⟩

/-- HOL `PROVE_INEQUALITY_TAC_60` (XWITCCN.hl:4505) as a lemma. -/
theorem PROVE_INEQUALITY_TAC_60 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  hBB.2.2.1 i j

/-- HOL `PROVE_INEQUALITY_TAC_6` (XWITCCN.hl:4536): the `j MOD 6` case
machine. -/
theorem PROVE_INEQUALITY_TAC_6 (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (i j : ℕ) : s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j :=
  PROVE_INEQUALITY_TAC_60 s vv hBB i j

/-- HOL `V_SY_EQ_IMAGE_VV_TAC6` (XWITCCN.hl:4552) as a lemma. -/
theorem V_SY_EQ_IMAGE_VV_TAC6 (vv : ℕ → V3) (hper : Periodic vv 6) (x : V3)
    (hx : x ∈ Set.range vv) : x ∈ V_SY_p4 (cycRow_p23 vv 6) := by
  rw [vSy_eq_range_p36 (by norm_num) hper]
  exact hx

/-- HOL `PROVE_E_SY_EQ_MOD_TAC_6` (XWITCCN.hl:4568) as a lemma. -/
theorem PROVE_E_SY_EQ_MOD_TAC_6 (vv : ℕ → V3) (hper : Periodic vv 6) (i : ℕ) :
    {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 6) := by
  obtain ⟨j, hj1, hj2⟩ := cycRow_shift_p36 (by norm_num) hper i
  exact ⟨j, Set.mem_univ j, by simp only; rw [hj1, hj2]⟩

/-- HOL `PROOF_E_EQ_TAC_6` (XWITCCN.hl:4583) as a lemma. -/
theorem PROOF_E_EQ_TAC_6 (vv : ℕ → V3) (hper : Periodic vv 6) (i : ℕ) :
    {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 6) :=
  PROVE_E_SY_EQ_MOD_TAC_6 vv hper i

/-- HOL `PROVE_E_SY_EQ_IMAGE_VV_6` (XWITCCN.hl:4598) as a lemma. -/
theorem PROVE_E_SY_EQ_IMAGE_VV_6 (vv : ℕ → V3) (hper : Periodic vv 6) (x : Set V3)
    (hx : x ∈ Set.range (fun i : ℕ => {vv i, vv (i + 1)})) :
    x ∈ E_SY_p4 (cycRow_p23 vv 6) := by
  rw [eSy_eq_range_p36 (by norm_num) hper]
  exact hx

/-- HOL `IN_NOT_EMPTY_B1_SY_6` (XWITCCN.hl:4618): row-decoding converse. -/
theorem IN_NOT_EMPTY_B1_SY_6 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
    (hk : s.k = 6) (hper : Periodic vv 6)
    (hball : ∀ i : Fin 6, cycRow_p23 vv 6 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun (i j : Fin 6) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 6) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      (cycRow_p23 vv 6))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 6)) :
    BBsV39 s vv := by
  sorry
  -- DISCHARGES: as IN_NOT_EMPTY_B1_SY_4 at k = 6.

/-- HOL `XWITCCN_CASE_6` (XWITCCN.hl:4826). -/
theorem XWITCCN_CASE_6 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) (hk : s.k = 6) :
    BBprimeV39 s ≠ ∅ := by
  sorry
  -- DISCHARGES: as XWITCCN_CASE_4 at k = 6.

/-! ## Section 5: the `5_sqrt8` system (XWITCCN.hl:4973-5670) -/

/-- HOL `V_E_FF_CASE_5_sqrt8` (XWITCCN.hl:4973) — proved. -/
theorem V_E_FF_CASE_5_sqrt8 (s : ScsV39) (vv : ℕ → V3)
    (_hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5) :
    V_SY_p4 (cycRow_p23 vv 5) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
    F_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => (vv i, vv (i + 1))) := by
  have hper : Periodic vv 5 := by rw [← hk]; exact hBB.2.1
  exact ⟨vSy_eq_range_p36 (by norm_num) hper, eSy_eq_range_p36 (by norm_num) hper,
    fSy_eq_range_p36 (by norm_num) hper⟩

/-- HOL `IN_NOT_EMPTY_CASE_5_sqrt8` (XWITCCN.hl:5102). -/
theorem IN_NOT_EMPTY_CASE_5_sqrt8 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5) :
    flattenRow_p23 vv 5 ∈ B_SY1_p4
      (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
  sorry
  -- DISCHARGES: as IN_NOT_EMPTY_CASE_5 over the `5_sqrt8` bound ladder.

/-- HOL `NOT_EMPTY_CASE_5_sqrt8` (XWITCCN.hl:5181). -/
theorem NOT_EMPTY_CASE_5_sqrt8 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5) :
    B_SY1_p4
      (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp
    (⟨flattenRow_p23 vv 5, IN_NOT_EMPTY_CASE_5_sqrt8 s vv hs hBB hk⟩ :
      (B_SY1_p4
        (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
        (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))).Nonempty)

/-- HOL `TAUSTAR_EQ_TAU_STAR_5_sqrt8` (XWITCCN.hl:5205). -/
theorem TAUSTAR_EQ_TAU_STAR_5_sqrt8 (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
    (l : FinVec 5 3)
    (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5)
    (hs1 : s1 = scsToStableSy_p23 s) (hl : flattenRow_p23 vv 5 = l) :
    taustarV39 s vv = tauStar_p23 s1 l := by
  sorry
  -- DISCHARGES: as TAUSTAR_EQ_TAU_STAR_5 over the `5_sqrt8` system.

/-- HOL `SCS_A_B__EQ_MOD_5_sqrt8` (XWITCCN.hl:5267). -/
theorem SCS_A_B__EQ_MOD_5_sqrt8 (s : ScsV39)
    (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
    (i j : ℕ) :
    s.a i j = s.a (i % 5) (j % 5) ∧ s.b i j = s.b (i % 5) (j % 5) := by
  subst hs
  exact ⟨csAdj_mod_p36 5 2 (Real.sqrt 8) i j, csAdj_mod_p36 5 (2 * h0) 6 i j⟩

/-- HOL `IN_NOT_EMPTY_B1_SY_5_sqrt8` (XWITCCN.hl:5381): row-decoding
converse. -/
theorem IN_NOT_EMPTY_B1_SY_5_sqrt8 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
    (hk : s.k = 5) (hper : Periodic vv 5)
    (hball : ∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      (cycRow_p23 vv 5))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 5)) :
    BBsV39 s vv := by
  sorry
  -- DISCHARGES: as IN_NOT_EMPTY_B1_SY_5 over the `5_sqrt8` system.

/-- HOL `XWITCCN_CASE_5_sqrt8` (XWITCCN.hl:5549). -/
theorem XWITCCN_CASE_5_sqrt8 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) (hk : s.k = 5) :
    BBprimeV39 s ≠ ∅ := by
  sorry
  -- DISCHARGES: as XWITCCN_CASE_5 over the `5_sqrt8` system.

/-! ## Section 6: the `5_pro_cs` system (XWITCCN.hl:5671-6450) -/

/-- HOL `V_E_FF_CASE_5_pro_cs` (XWITCCN.hl:5764) — proved. -/
theorem V_E_FF_CASE_5_pro_cs (s : ScsV39) (vv : ℕ → V3)
    (_hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
      (aPro 5 (Real.sqrt 8) (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5) :
    V_SY_p4 (cycRow_p23 vv 5) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
    F_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => (vv i, vv (i + 1))) := by
  have hper : Periodic vv 5 := by rw [← hk]; exact hBB.2.1
  exact ⟨vSy_eq_range_p36 (by norm_num) hper, eSy_eq_range_p36 (by norm_num) hper,
    fSy_eq_range_p36 (by norm_num) hper⟩

/-- HOL `IN_NOT_EMPTY_CASE_5_pro_cs` (XWITCCN.hl:5893). -/
theorem IN_NOT_EMPTY_CASE_5_pro_cs (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
      (aPro 5 (Real.sqrt 8) (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5) :
    flattenRow_p23 vv 5 ∈ B_SY1_p4
      (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
  sorry
  -- DISCHARGES: as IN_NOT_EMPTY_CASE_5 over the `a_pro 5` bound ladder.

/-- HOL `NOT_EMPTY_CASE_5_pro_cs` (XWITCCN.hl:5968). -/
theorem NOT_EMPTY_CASE_5_pro_cs (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
      (aPro 5 (Real.sqrt 8) (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5) :
    B_SY1_p4
      (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp
    (⟨flattenRow_p23 vv 5, IN_NOT_EMPTY_CASE_5_pro_cs s vv hs hBB hk⟩ :
      (B_SY1_p4
        (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
        (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))).Nonempty)

/-- HOL `TAUSTAR_EQ_TAU_STAR_5_pro_cs` (XWITCCN.hl:5992). -/
theorem TAUSTAR_EQ_TAU_STAR_5_pro_cs (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
    (l : FinVec 5 3)
    (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
      (aPro 5 (Real.sqrt 8) (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 5)
    (hs1 : s1 = scsToStableSy_p23 s) (hl : flattenRow_p23 vv 5 = l) :
    taustarV39 s vv = tauStar_p23 s1 l := by
  sorry
  -- DISCHARGES: as TAUSTAR_EQ_TAU_STAR_5 over the `5_pro_cs` system.

/-- HOL `SCS_A_B__EQ_MOD_5_pro_cs` (XWITCCN.hl:6053). -/
theorem SCS_A_B__EQ_MOD_5_pro_cs (s : ScsV39)
    (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
      (aPro 5 (Real.sqrt 8) (2 * h0) 6))
    (i j : ℕ) :
    s.a i j = s.a (i % 5) (j % 5) ∧ s.b i j = s.b (i % 5) (j % 5) := by
  subst hs
  exact ⟨aPro_mod_p36 5 (2 * h0) 2 (2 * h0) i j,
    aPro_mod_p36 5 (Real.sqrt 8) (2 * h0) 6 i j⟩

/-- HOL `IN_NOT_EMPTY_B1_SY_5_pro_cs` (XWITCCN.hl:6167): row-decoding
converse. -/
theorem IN_NOT_EMPTY_B1_SY_5_pro_cs (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
      (aPro 5 (Real.sqrt 8) (2 * h0) 6))
    (hk : s.k = 5) (hper : Periodic vv 5)
    (hball : ∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      (cycRow_p23 vv 5))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 5)) :
    BBsV39 s vv := by
  sorry
  -- DISCHARGES: as IN_NOT_EMPTY_B1_SY_5 over the `5_pro_cs` system.

/-- HOL `XWITCCN_CASE_5_pro_cs` (XWITCCN.hl:6338). -/
theorem XWITCCN_CASE_5_pro_cs (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
      (aPro 5 (Real.sqrt 8) (2 * h0) 6))
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) (hk : s.k = 5) :
    BBprimeV39 s ≠ ∅ := by
  sorry
  -- DISCHARGES: as XWITCCN_CASE_5 over the `5_pro_cs` system.

/-! ## Section 7: the `4_3` system (XWITCCN.hl:6451-7175) -/

/-- HOL `V_E_FF_CASE_4_3` (XWITCCN.hl:6451) — proved. -/
theorem V_E_FF_CASE_4_3 (s : ScsV39) (vv : ℕ → V3)
    (_hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4) :
    V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
    F_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => (vv i, vv (i + 1))) := by
  have hper : Periodic vv 4 := by rw [← hk]; exact hBB.2.1
  exact ⟨vSy_eq_range_p36 (by norm_num) hper, eSy_eq_range_p36 (by norm_num) hper,
    fSy_eq_range_p36 (by norm_num) hper⟩

/-- HOL `IN_NOT_EMPTY_CASE_4_3` (XWITCCN.hl:6584). -/
theorem IN_NOT_EMPTY_CASE_4_3 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4) :
    flattenRow_p23 vv 4 ∈ B_SY1_p4
      (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
  sorry
  -- DISCHARGES: as IN_NOT_EMPTY_CASE_4 over the `cs_adj 4 2 3` ladder.

/-- HOL `NOT_EMPTY_CASE_4_3` (XWITCCN.hl:6664). -/
theorem NOT_EMPTY_CASE_4_3 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4) :
    B_SY1_p4
      (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp
    (⟨flattenRow_p23 vv 4, IN_NOT_EMPTY_CASE_4_3 s vv hs hBB hk⟩ :
      (B_SY1_p4
        (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
        (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))).Nonempty)

/-- HOL `TAUSTAR_EQ_TAU_STAR_4_3` (XWITCCN.hl:6688). -/
theorem TAUSTAR_EQ_TAU_STAR_4_3 (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
    (l : FinVec 4 3)
    (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4)
    (hs1 : s1 = scsToStableSy_p23 s) (hl : flattenRow_p23 vv 4 = l) :
    taustarV39 s vv = tauStar_p23 s1 l := by
  sorry
  -- DISCHARGES: as TAUSTAR_EQ_TAU_STAR_4 over the `4_3` system.

/-- HOL `SCS_A_B__EQ_MOD_4_3` (XWITCCN.hl:6773). -/
theorem SCS_A_B__EQ_MOD_4_3 (s : ScsV39)
    (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
    (i j : ℕ) :
    s.a i j = s.a (i % 4) (j % 4) ∧ s.b i j = s.b (i % 4) (j % 4) := by
  subst hs
  exact ⟨csAdj_mod_p36 4 2 3 i j, csAdj_mod_p36 4 (2 * h0) 6 i j⟩

/-- HOL `IN_NOT_EMPTY_B1_SY_4_3` (XWITCCN.hl:6866): row-decoding converse. -/
theorem IN_NOT_EMPTY_B1_SY_4_3 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
    (hk : s.k = 4) (hper : Periodic vv 4)
    (hball : ∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      (cycRow_p23 vv 4))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 4)) :
    BBsV39 s vv := by
  sorry
  -- DISCHARGES: as IN_NOT_EMPTY_B1_SY_4 over the `4_3` system.

/-- HOL `XWITCCN_CASE_4_3` (XWITCCN.hl:7045). -/
theorem XWITCCN_CASE_4_3 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) (hk : s.k = 4) :
    BBprimeV39 s ≠ ∅ := by
  sorry
  -- DISCHARGES: as XWITCCN_CASE_4 over the `4_3` system.

/-! ## Section 8: the `4_sqrt8` system (XWITCCN.hl:7262-7940) -/

/-- HOL `V_E_FF_CASE_4_sqrt8` (XWITCCN.hl:7262) — proved. -/
theorem V_E_FF_CASE_4_sqrt8 (s : ScsV39) (vv : ℕ → V3)
    (_hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
      (aPro 4 (Real.sqrt 8) (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4) :
    V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
    F_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => (vv i, vv (i + 1))) := by
  have hper : Periodic vv 4 := by rw [← hk]; exact hBB.2.1
  exact ⟨vSy_eq_range_p36 (by norm_num) hper, eSy_eq_range_p36 (by norm_num) hper,
    fSy_eq_range_p36 (by norm_num) hper⟩

/-- HOL `IN_NOT_EMPTY_CASE_4_sqrt8` (XWITCCN.hl:7387). -/
theorem IN_NOT_EMPTY_CASE_4_sqrt8 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
      (aPro 4 (Real.sqrt 8) (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4) :
    flattenRow_p23 vv 4 ∈ B_SY1_p4
      (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) := by
  sorry
  -- DISCHARGES: as IN_NOT_EMPTY_CASE_4 over the `a_pro 4` bound ladder.

/-- HOL `NOT_EMPTY_CASE_4_sqrt8` (XWITCCN.hl:7461). -/
theorem NOT_EMPTY_CASE_4_sqrt8 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
      (aPro 4 (Real.sqrt 8) (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4) :
    B_SY1_p4
      (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp
    (⟨flattenRow_p23 vv 4, IN_NOT_EMPTY_CASE_4_sqrt8 s vv hs hBB hk⟩ :
      (B_SY1_p4
        (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
        (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))).Nonempty)

/-- HOL `TAUSTAR_EQ_TAU_STAR_4_sqrt8` (XWITCCN.hl:7485). -/
theorem TAUSTAR_EQ_TAU_STAR_4_sqrt8 (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
    (l : FinVec 4 3)
    (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
      (aPro 4 (Real.sqrt 8) (2 * h0) 6))
    (hBB : BBsV39 s vv) (hk : s.k = 4)
    (hs1 : s1 = scsToStableSy_p23 s) (hl : flattenRow_p23 vv 4 = l) :
    taustarV39 s vv = tauStar_p23 s1 l := by
  sorry
  -- DISCHARGES: as TAUSTAR_EQ_TAU_STAR_4 over the `4_sqrt8` system.

/-- HOL `SCS_A_B__EQ_MOD_4_sqrt8` (XWITCCN.hl:7557). -/
theorem SCS_A_B__EQ_MOD_4_sqrt8 (s : ScsV39)
    (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
      (aPro 4 (Real.sqrt 8) (2 * h0) 6))
    (i j : ℕ) :
    s.a i j = s.a (i % 4) (j % 4) ∧ s.b i j = s.b (i % 4) (j % 4) := by
  subst hs
  exact ⟨aPro_mod_p36 4 (2 * h0) 2 (Real.sqrt 8) i j,
    aPro_mod_p36 4 (Real.sqrt 8) (2 * h0) 6 i j⟩

/-- HOL `IN_NOT_EMPTY_B1_SY_4_sqrt8` (XWITCCN.hl:7650): row-decoding
converse. -/
theorem IN_NOT_EMPTY_B1_SY_4_sqrt8 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
      (aPro 4 (Real.sqrt 8) (2 * h0) 6))
    (hk : s.k = 4) (hper : Periodic vv 4)
    (hball : ∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus)
    (hC1 : CONDITION1_SY_p4
      (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
      (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
      (cycRow_p23 vv 4))
    (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 4)) :
    BBsV39 s vv := by
  sorry
  -- DISCHARGES: as IN_NOT_EMPTY_B1_SY_4 over the `4_sqrt8` system.

/-- HOL `XWITCCN_CASE_4_sqrt8` (XWITCCN.hl:7827). -/
theorem XWITCCN_CASE_4_sqrt8 (s : ScsV39) (vv : ℕ → V3)
    (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
      (aPro 4 (Real.sqrt 8) (2 * h0) 6))
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) (hk : s.k = 4) :
    BBprimeV39 s ≠ ∅ := by
  sorry
  -- DISCHARGES: as XWITCCN_CASE_4 over the `4_sqrt8` system.

/-! ## Section 9: the master conclusions (XWITCCN.hl:7941-8020) -/

/-- HOL `XWITCCN_TYPE` (XWITCCN.hl:7941): `XWITCCN` relativised to an index
type `M` with `scs_k_v39 s = dimindex(:M)`; the `k` is explicit here. -/
theorem XWITCCN_TYPE (k : ℕ) (s : ScsV39) (vv : ℕ → V3)
    (hmem : s ∈ sInitListV39) (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0)
    (hk : s.k = k) : BBprimeV39 s ≠ ∅ := by
  sorry
  -- DISCHARGES: XWITCCN_CASE_3 / _4 / _5 / _6 / _4_3 / _4_sqrt8 / _5_sqrt8 /
  -- _5_pro_cs, assembled by the explicit `s_init_list_v39` eight-element
  -- case split (LENGTH_s_init_list, LocalAuto1).

/-- HOL `XWITCCN` (XWITCCN.hl:7980): the master conclusion. Twin of the
`XWITCCN_concl` statement of LocalAuto1 (that lane is `sorry`; here the
`INST_TYPE` instantiations `k = 3, 2+2, 2+3, 3+3` are carried explicitly). -/
theorem XWITCCN : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprimeV39 s ≠ ∅ := by
  sorry
  -- DISCHARGES: XWITCCN_TYPE at k ∈ {3, 4, 5, 6}.
