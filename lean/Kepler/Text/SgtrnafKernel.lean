/-
SgtrnafKernel: the upstream kernel for the `sgtrnaf_p12` anchor
(`Kepler.Text.LocalAuto12`) — the HOL `SGTRNAF` conclusion, i.e. the
existence of a minimal `BBs` realisation (`BBprimeV39 s ≠ ∅`) whenever
`taustar_v39 s vv < 0`.

Why a separate upstream module: the original HOL proof consumes `UXCKFPE2`
(UXCKFPE.hl), whose engine-sunk body lives in `Kepler.Text.LocalAuto24` and
whose downstream twin `SGTRNAF_p27` lives in `Kepler.Text.LocalAuto27`. Both
are import-cyclic for LocalAuto12 (LA27 -> LA24 -> LA20 -> LA12) and for
LocalAuto20 (LA24 -> LA20). This module re-proves the same content strictly
above LA12/LA20: it imports `LocalAuto23` (the stable-system/minimiser kit)
and `LocalAuto36` (the generic k >= 4 `B_SY1` cores), neither of which
imports LA12 or LA20, and carries verbatim copies of LocalAuto24's Section C
(UXCKFPE.hl case lemmas for k = 3..6) under `_krnl` names.

The copied bodies are the PROVED, standard-three-axiom case bank of
LocalAuto24 (measured `#print axioms`: propext, Classical.choice,
Quot.sound for `XWITCCN_CASE_*_IS_SCS_p24`/`UXCKFPE_p24`); only
the declaration names are changed (`_p24` -> `_krnl`) so that a module
importing both this file and LocalAuto24 (e.g. LocalConcl through LA20)
stays collision-free. Statements are byte-identical to the LA24 originals.

Consumers:
- `Kepler.Text.LocalAuto12.sgtrnaf_p12` = `SGTRNAF_krnl` (statement frozen);
- `Kepler.Text.LkgrquiKernel` (LKGRQUI copy) uses `SGTRNAF_krnl`.
-/
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto36
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

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
(`_p24` -> `_krnl`). -/


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
theorem NOT_EMPTY_CASE_4_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
theorem IN_NOT_EMPTY_B1_SY_4_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
theorem XWITCCN_CASE_4_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
  have hne := NOT_EMPTY_CASE_4_IS_SCS_krnl s vv hs hk hBB
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
    IN_NOT_EMPTY_B1_SY_4_IS_SCS_krnl s vv1 hs hk hp4 hball hC1 hC2
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
  -- DISCHARGES: IS_SCS_STABLE_SYSTEM_p23 + NOT_EMPTY_CASE_4_IS_SCS_krnl +
  -- the HDPLYGY/B_SY1 minimizer on the stable record + IN_NOT_EMPTY_B1_SY_4
  -- + TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4_p23 (negativity transfer).
  -- (FILLED, casebank-close-w1 kit: wiring = HDPLYGY minimizer
  -- (B_SY1_p4_compact_of_fan_p23 + continuousOn_tauStar_p23) on the
  -- post SF-81a+SF-C3 stable record + the five prereq fills + the filled
  -- SF-C3-fixed TAUSTAR bridge. Transitive taint: continuousOn_tauFun_p23 +
  -- bodyClosed_p23 (HDPLYGY-kit NEEDS, giant roots — see CLOSE-PLAN §M0).)

/-! ### C2. The k = 5 witnesses (UXCKFPE.hl:547-995) -/

/-- HOL `NOT_EMPTY_CASE_5_IS_SCS` (UXCKFPE.hl:547). -/
theorem NOT_EMPTY_CASE_5_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
theorem IN_NOT_EMPTY_B1_SY_5_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
  -- DISCHARGES: as `IN_NOT_EMPTY_B1_SY_4_IS_SCS_krnl` at k = 5
  -- (V_E_FF_IS_SCS_CASES_5_p23).
  -- (filled from the LA23 fill + the LA36 core `inB1_core_p36`.)

/-- HOL `XWITCCN_CASE_5_IS_SCS` (UXCKFPE.hl:889). -/
theorem XWITCCN_CASE_5_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
  have hne := NOT_EMPTY_CASE_5_IS_SCS_krnl s vv hs hk hBB
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
    IN_NOT_EMPTY_B1_SY_5_IS_SCS_krnl s vv1 hs hk hp5 hball hC1 hC2
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
  -- DISCHARGES: as `XWITCCN_CASE_4_IS_SCS_krnl` at k = 5.
  -- (FILLED, casebank-close-w1 kit: wiring = HDPLYGY minimizer
  -- (B_SY1_p4_compact_of_fan_p23 + continuousOn_tauStar_p23) on the
  -- post SF-81a+SF-C3 stable record + the five prereq fills + the filled
  -- SF-C3-fixed TAUSTAR bridge. Transitive taint: continuousOn_tauFun_p23 +
  -- bodyClosed_p23 (HDPLYGY-kit NEEDS, giant roots — see CLOSE-PLAN §M0).)

/-! ### C3. The k = 6 witnesses (UXCKFPE.hl:1003-1483) -/

/-- HOL `NOT_EMPTY_CASE_6_IS_SCS` (UXCKFPE.hl:1003). -/
theorem NOT_EMPTY_CASE_6_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
theorem IN_NOT_EMPTY_B1_SY_6_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
  -- DISCHARGES: as `IN_NOT_EMPTY_B1_SY_4_IS_SCS_krnl` at k = 6
  -- (V_E_FF_IS_SCS_CASES_6_p23).
  -- (filled from the LA23 fill + the LA36 core `inB1_core_p36`.)

/-- HOL `XWITCCN_CASE_6_IS_SCS` (UXCKFPE.hl:1374). -/
theorem XWITCCN_CASE_6_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
  have hne := NOT_EMPTY_CASE_6_IS_SCS_krnl s vv hs hk hBB
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
    IN_NOT_EMPTY_B1_SY_6_IS_SCS_krnl s vv1 hs hk hp6 hball hC1 hC2
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
  -- DISCHARGES: as `XWITCCN_CASE_4_IS_SCS_krnl` at k = 6.
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
the rows of the MEMBER's matvec pre-image.  `IN_NOT_EMPTY_B1_SY_3_IS_SCS_krnl`
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
theorem IN_IS_SCS_CASE_3_krnl (s : ScsV39) (vv : ℕ → V3)
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
theorem IN_NOT_EMPTY_B1_SY_3_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
theorem NOT_EMPTY_CASE_3_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    ({l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} : Set (FinVec 3 3)) ≠ ∅ := by
  exact Set.nonempty_iff_ne_empty.mp
    ⟨flattenRow_p23 vv 3, IN_IS_SCS_CASE_3_krnl s vv hs hk hBB⟩
  -- DISCHARGES: IN_IS_SCS_CASE_3_krnl (witness `flattenRow_p23 vv 3`).

/-- HOL `J1_TS` (UXCKFPE.hl:1792): the k = 3 ear index set, with the
application-instantiated `f_ts s = (\i. (1+i) MOD 3)` carried as a
parameter `f` (and `J_TS s` as `J`). -/
def J1_TS_krnl (J : Set (Set ℕ)) (f : ℕ → ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ i, {i % 3, f (i % 3)} ∈ J ∧ i ∈ Set.Icc 1 3 ∧ x = (i, i % 3 + 1)}

/-- HOL `d_fun3` (UXCKFPE.hl:1797): the k = 3 ear functional, `d_ts`/ear
flag/`J_TS`/`f_ts` carried as parameters (`d`, `ear`, `J`, `f`). -/
noncomputable def dFun3_krnl (d : ℝ) (ear : Prop) (J : Set (Set ℕ)) (f : ℕ → ℕ)
    (l : FinVec 3 3) : ℝ :=
  d + (1 : ℝ) / 10 * (if ear then 1 else -1) *
    setSum (J1_TS_krnl J f)
      (fun x => cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖)

/-- HOL `FINITE_J1_TS` (UXCKFPE.hl:1801). -/
theorem FINITE_J1_TS_krnl (J : Set (Set ℕ)) (f : ℕ → ℕ) :
    (J1_TS_krnl J f).Finite := by
  refine (Set.finite_range fun i : Fin 3 =>
    ((i : ℕ) + 1, ((i : ℕ) + 1) % 3 + 1)).subset ?_
  rintro x ⟨i, -, hi, rfl⟩
  have h1 : 1 ≤ i := hi.1
  have h3 : i ≤ 3 := hi.2
  refine ⟨⟨i - 1, by omega⟩, ?_⟩
  show ((i - 1 : ℕ) + 1, (i - 1 + 1) % 3 + 1) = (i, i % 3 + 1)
  rw [show i - 1 + 1 = i from by omega]

/-- the `dFun3_krnl` head is continuous (mirror of `continuous_dFun_p23`). -/
private theorem w1continuous_dFun3 (s : ScsV39) :
    Continuous (fun l : FinVec 3 3 =>
      dFun3_krnl s.d (isEarV39 s) (scsJSet_p23 s) (fun i => (1 + i) % s.k) l) := by
  have hterms : ∀ x ∈ J1_TS_krnl (scsJSet_p23 s) (fun i : ℕ => (1 + i) % s.k),
      Continuous (fun l : FinVec 3 3 =>
        cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖) := fun x _ =>
    Continuous.sub continuous_const
      (((continuous_rowSy_p23 (x.1 - 1)).sub (continuous_rowSy_p23 (x.2 - 1))).norm)
  unfold dFun3_krnl
  refine Continuous.add continuous_const (Continuous.const_mul ?_ _)
  simp only [setSum]
  split
  · rename_i h
    exact continuous_finsetSum _ (fun x hx => hterms x (h.mem_toFinset.mp hx))
  · exact continuous_const

/-- HOL `CONTINUOUS_ON_D_FUN3` (UXCKFPE.hl:1813): `d_fun3` is continuous
on the k = 3 body set (sum over the finite `J1_TS_krnl` of row differences).
SF-80: row-indexed body set. -/
theorem CONTINUOUS_ON_D_FUN3_krnl (s : ScsV39) (hk : s.k = 3)
    (vv : ℕ → V3) :
    ContinuousOn
      (fun l : FinVec 3 3 =>
        dFun3_krnl s.d (isEarV39 s) (scsJSet_p23 s) (fun i => (1 + i) % s.k) l)
      {l : FinVec 3 3 |
        (∀ i : Fin 3, rowSy_p23 l i ∈ ballAnnulus) ∧
          CONDITION1_SY_p4
            (fun i j : Fin 3 => s.a (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i j : Fin 3 => s.b (((i : ℕ) + 1) % 3) (((j : ℕ) + 1) % 3))
            (fun i : Fin 3 => rowSy_p23 l i)} := by
  exact (w1continuous_dFun3 s).continuousOn
  -- DISCHARGES: setSum over the 3-point FINITE_J1_TS_krnl set of
  -- `cstab - ‖rowSy_p23 l _ - rowSy_p23 l _‖` (continuous in `l`), the
  -- constant `d`/ear terms (HOL CONTINUOUS_ON_ADD/VSUM/ROW kit).

/-- HOL `tri_sy_explicit` (UXCKFPE.hl:1856): the projections of the
`tri_sy (k,d,s,a,b,J,f)` record (↦ `StableSyP23`) return its components. -/
theorem tri_sy_explicit_krnl (k : ℕ) (d : ℝ) (s : Set ℕ) (a b : ℕ → ℕ → ℝ)
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
theorem IN_B_SY1_COLLINEAR_CASE_3_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
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
theorem HDPLYGY_CASE_30_krnl (s : ScsV39) (vv : ℕ → V3)
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
            dFun3_krnl s.d (isEarV39 s) (scsJSet_p23 s)
              (fun i => (1 + i) % s.k) x ≤
          tau3 (rowSy_p23 y 0) (rowSy_p23 y 1) (rowSy_p23 y 2) -
            dFun3_krnl s.d (isEarV39 s) (scsJSet_p23 s)
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
  -- COMPACT_TRI_STABLE + CONTINUOUS_ON_D_FUN3_krnl (the HOL rho/ly/interp
  -- continuity chain for `tau3` on rows).

set_option maxHeartbeats 1000000 in
/-- HOL `TAUSTAR_EQ_TAU_STAR_3_IS_SCS` (UXCKFPE.hl:2126): the scs-taustar
at k = 3 is `tau3 (vv 1) (vv 2) (vv 0) - d_fun3`. -/
theorem TAUSTAR_EQ_TAU_STAR_3_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    taustarV39 s vv = tau3 (vv 1) (vv 2) (vv 0) -
      dFun3_krnl s.d (isEarV39 s) (scsJSet_p23 s)
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
  have hd : dsvV39 s vv = dFun3_krnl s.d (isEarV39 s) (scsJSet_p23 s)
      (fun i => (1 + i) % s.k) (flattenRow_p23 vv 3) := by
    unfold dsvV39 dFun3_krnl
    have h10 : (0.1:ℝ) = (1:ℝ)/10 := by norm_num
    rw [h10]
    refine congrArg (fun t => s.d + (1:ℝ)/10 * (if isEarV39 s then 1 else -1) * t) ?_
    apply w1setSum_image_bij (φ := fun x : ℕ × ℕ => x.2 - 1)
    · exact FINITE_J1_TS_krnl _ _
    · -- hmem: every B member maps into the dsv index set
      intro x hx
      rw [show s.k = 3 from hk3] at hx
      simp only [J1_TS_krnl, Set.mem_setOf_eq] at hx
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
      simp only [J1_TS_krnl, Set.mem_setOf_eq] at hx hy
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
      · simp only [J1_TS_krnl, Set.mem_setOf_eq, scsJSet_p23, Set.mem_setOf_eq]
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
      simp only [J1_TS_krnl, Set.mem_setOf_eq] at hx
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
theorem XWITCCN_CASE_3_IS_SCS_krnl (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : s.k = 3)
    (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by
  have hne := NOT_EMPTY_CASE_3_IS_SCS_krnl s vv hs hk hBB
  have hnc := IN_B_SY1_COLLINEAR_CASE_3_IS_SCS_krnl s vv hs hk hBB
  obtain ⟨x, hx_mem, hx_min⟩ := HDPLYGY_CASE_30_krnl s vv hs hk hne hnc
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
    IN_NOT_EMPTY_B1_SY_3_IS_SCS_krnl s vv1 hs hk hper hball hC1
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
    rw [TAUSTAR_EQ_TAU_STAR_3_IS_SCS_krnl s vv1 hs hk hBB1, hflat]
    have hta' : tau3 (vv 1) (vv 2) (vv 0)
        - dFun3_krnl s.d (isEarV39 s) (scsJSet_p23 s) (fun i => (1 + i) % s.k)
            (flattenRow_p23 vv 3) < 0 := by
      rw [← TAUSTAR_EQ_TAU_STAR_3_IS_SCS_krnl s vv hs hk hBB]
      exact hta
    have hmin := hx_min _ (IN_IS_SCS_CASE_3_krnl s vv hs hk hBB)
    rw [hrowvv 0 (by omega), hrowvv 1 (by omega), hrowvv 2 (by omega)] at hmin
    exact hmin.trans_lt hta'
  refine fun hempty => ?_
  have hmem : vv1 ∈ (BBprimeV39 s : Set (ℕ → V3)) := by
    refine ⟨hBB1, ?_, hneg⟩
    intro u hBBu
    have hrowu : ∀ i : ℕ, i < 3 →
        rowSy_p23 (flattenRow_p23 u 3) i = u ((i + 1) % 3) :=
      fun i hi => w1rowSy_flattenRow3 u i hi
    have hmin := hx_min _ (IN_IS_SCS_CASE_3_krnl s u hs hk hBBu)
    rw [hrowu 0 (by omega), hrowu 1 (by omega), hrowu 2 (by omega)] at hmin
    rw [TAUSTAR_EQ_TAU_STAR_3_IS_SCS_krnl s vv1 hs hk hBB1, hflat, TAUSTAR_EQ_TAU_STAR_3_IS_SCS_krnl s u hs hk hBBu]
    simp only [hv1]
    exact hmin
  rw [hempty] at hmem
  exact (Set.mem_empty_iff_false _).mp hmem
  -- DISCHARGES: IS_SCS_TRI_STABLE_SYSTEM_p23 + NOT_EMPTY_CASE_3_IS_SCS_krnl
  -- + IN_B_SY1_COLLINEAR_CASE_3_IS_SCS_krnl + HDPLYGY_CASE_30_krnl +
  -- IN_NOT_EMPTY_B1_SY_3_IS_SCS_krnl + TAUSTAR_EQ_TAU_STAR_3_IS_SCS_krnl.

/-- HOL `UXCKFPE` (UXCKFPE.hl:2602): the k = 3..6 case assembly
(the HOL `INST_TYPE` moves become this case split; `isScsV39` gives
`3 ≤ k ≤ 6`). -/
theorem UXCKFPE_krnl (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) :
    (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := by
  have h3 : 3 ≤ s.k := hs.2.1
  have h6 : s.k ≤ 6 := hs.2.2.1
  rcases (by omega : s.k = 3 ∨ s.k = 4 ∨ s.k = 5 ∨ s.k = 6) with hk | hk | hk | hk
  · exact XWITCCN_CASE_3_IS_SCS_krnl s vv hs hBB hk hta
  · exact XWITCCN_CASE_4_IS_SCS_krnl s vv hs hBB hk hta
  · exact XWITCCN_CASE_5_IS_SCS_krnl s vv hs hBB hk hta
  · exact XWITCCN_CASE_6_IS_SCS_krnl s vv hs hBB hk hta

/-- HOL `UXCKFPE2` (SGTRNAF.hl:75), kernel copy (see module docstring). -/
theorem UXCKFPE2_krnl : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprime2V39 s ≠ ∅ := by
  intro s vv hs hBB hta
  have hbp : (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := UXCKFPE_krnl s vv hs hBB hta
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
theorem SGTRNAF_krnl : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    unadornedV39 s → BBsV39 s vv → taustarV39 s vv < 0 → MMsV39 s ≠ ∅ := by
  intro s vv hs hu hBB hta
  have h2 : (BBprime2V39 s : Set (ℕ → V3)) ≠ ∅ := UXCKFPE2_krnl s vv hs hBB hta
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
