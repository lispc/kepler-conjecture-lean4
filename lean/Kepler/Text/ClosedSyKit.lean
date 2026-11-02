/-
ClosedSyKit — the `SY` carrier kit, twinned verbatim from LocalAuto18's
carrier definition section (LA18:145-233: `torsor_p18`, `constraintSystem_p18`,
`stableSystem_p18`, `rowV3_p18`, `CONDITION2_SY_p18`, `BSY1body_p18`,
`POWER_MOD_FUN_p18` (LA18:210), `SYset_p18` (LA18:232)) with the suffix
`_p18` → `_cs`, plus the giant goal `CLOSED_SY_cs` (verbatim twin of
`CLOSED_SY_p18`, LA18:238) and the G-B1 row-rendering bridge
`bcw2b_bodyClosed_of_SYset_cs` (bodyclosed-w2 code, `p18` names → `cs`).

WHY A TWIN MODULE (bodyclosed-w2b): LA23 cannot import LA18 — the existing
edges LA18 → LocalAuto27 → LA24/LA25/LA35 → LA23 close a cycle (probed in
bodyclosed-w2, cycleprobe3).  The carrier kit therefore moves upstream of
LA23 into a module whose imports are drawn only from
{LocalAuto1, SphereKit, LocalAuto4, Mathlib} — a set disjoint from the
LA18/LA23/LA24/LA27 cycle corridor, so LA23 may consume it and (also)
LA18 may consume it back with zero new cycles (ClosedSyKit's closure is
contained in LA18's pre-LA27 closure; python BFS check in the lane
evidence).

`CLOSED_SY_cs` is the debt root of the bodyClosed campaign (W3-W7 giant
replay): every consumer — LA23 `bodyClosed_p23` via G-B2 + G-B1, and LA18
`CLOSED_SY_p18` via the definitional twin bridge — now hangs its
`sorryAx` on this single declaration.  HOL source: CLOSED_SY,
WJSCPRO.hl:63-3174 (SF-89b / bodyclosed-recon route B).

The only unfinished declaration in this file is `CLOSED_SY_cs` (the single
`CLOSED_SY` axiom-gap marker); every other declaration is fully proved.
-/
import Kepler.Text.LocalAuto1
import Kepler.Text.SphereKit
import Kepler.Text.LocalAuto4
import Mathlib

namespace Kepler.Text

open Kepler.Geom Set

/-- HOL `torsor` (dih2k.hl:48), `Finset ℕ` instance. Verbatim twin of
`torsor_p18` (LocalAuto18:147) / `torsor_p9`. NEEDS: merge. -/
def torsor_cs (s : Finset ℕ) (k : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ x ∈ s, f x ∈ s) ∧ (∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂) ∧
    (∀ i x, 0 < i → i < k → x ∈ s → f^[i] x ≠ x) ∧
    (∀ x ∈ s, f^[k] x = x) ∧ s.card = k

/-- HOL `constraint_system` (dih2k.hl:52) with `d : ℝ`. Verbatim twin of
`constraintSystem_p18` (LocalAuto18:154) / `constraintSystem_p9`. NEEDS:
merge. -/
def constraintSystem_cs (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  3 ≤ k ∧ k ≤ 6 ∧ torsor_cs s k f ∧
    (∀ i j, a i j = a j i ∧ b i j = b j i ∧ a i j ≤ b i j) ∧
    (∀ i j, a i j = a i (f^[k] j) ∧ b i j = b i (f^[k] j)) ∧
    J ⊆ s.image (fun i => {i, f i}) ∧
    J.card + k ≤ 6

/-- HOL `stable_system` (dih2k.hl:61) with `d : ℝ`. Verbatim twin of
`stableSystem_p18` (LocalAuto18:164) / `stableSystem_p9`. NEEDS: merge. -/
def stableSystem_cs (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  constraintSystem_cs k d s a b J f ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 ≤ a i j) ∧
    (∀ i ∈ s, a i i = 0 ∧ b i (f i) ≤ cstab_p4) ∧
    (∀ i j, {i, j} ∈ J → a i j = Real.sqrt 8 ∧ b i j = cstab_p4)

/-- HOL `row i (vecmats l)`: the `i`-th row (1-based, junk value `0`
off-range) as a `V3`. Verbatim twin of `rowV3_p18` (LocalAuto18:173) /
`rowV3_p9`. NEEDS: merge. -/
def rowV3_cs {m : ℕ} (l : FinVec m 3) (i : ℕ) : V3 :=
  if h : 1 ≤ i ∧ i ≤ m then vecmatsV3_p4 l ⟨i - 1, by omega⟩ else 0

/-- HOL `CONDITION2_SY` (dih2k.hl:88) at `ℕ` index type. Verbatim twin of
`CONDITION2_SY_p18` (LocalAuto18:178) / `CONDITION2_SY_p9`. NEEDS: merge. -/
def CONDITION2_SY_cs (k : ℕ) (l : FinVec k 3) : Prop :=
  convexLocalFan_p4 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
    (F_SY_p4 (vecmatsV3_p4 l))

/-- The `B_SY1` body-set: HOL `{matvec v | rows v in ball_annulus ∧
CONDITION1_SY a b v}` (k = dimindex(:M)). Verbatim twin of `BSY1body_p18`
(LocalAuto18:185) / `BSY1body_p9`. NEEDS: merge. -/
def BSY1body_cs (k : ℕ) (a b : ℕ → ℕ → ℝ) : Set (FinVec k 3) :=
  {l | (∀ j : Fin k, vecmatsV3_p4 l j ∈ ballAnnulus) ∧
    ∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k →
      a i j ≤ ‖rowV3_cs l i - rowV3_cs l j‖ ∧
        ‖rowV3_cs l i - rowV3_cs l j‖ ≤ b i j}

/-! ## Section A: WJSCPRO (Wjscpro.hl) -/

/-- HOL `POWER_MOD_FUN` (WJSCPRO.hl:42): the successor-mod cycle,
iterated `n` times, advances by `n`. Verbatim twin of `POWER_MOD_FUN_p18`
(LocalAuto18:210, proof copied verbatim). -/
theorem POWER_MOD_FUN_cs (n i k : ℕ) (_hn : 1 ≤ n) (_hk : 1 < k) :
    (fun j => (1 + j) % k)^[n] i = (n + i) % k := by
  obtain ⟨m, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have key : ∀ p i, (fun j => (1 + j) % k)^[p + 1] i = (p + 1 + i) % k := by
    intro p
    induction p with
    | zero => intro i; rfl
    | succ p ih =>
      intro i
      rw [Function.iterate_succ', Function.comp_apply, ih]
      have hstep : ∀ x : ℕ, (1 + x % k) % k = (1 + x) % k := fun x => by
        rw [Nat.add_comm 1 (x % k), Nat.mod_add_mod, Nat.add_comm x 1]
      rw [hstep]
      congr 1
      omega
  exact key m i

/-- The `WJSCPRO` space: HOL `{matvec v | !i. row i v IN ball_annulus /\
CONDITION1_SY a b v /\ CONDITION2_SY v}` at ambient size `k`, rendered as
the `BSY1body_cs` rows/CONDITION1 body intersected with `CONDITION2_SY_cs`
(since `vecmats ∘ matvec = id`, the members agree with the HOL matrix
image). Verbatim twin of `SYset_p18` (LocalAuto18:232). -/
def SYset_cs (k : ℕ) (a b : ℕ → ℕ → ℝ) : Set (FinVec k 3) :=
  {l | l ∈ BSY1body_cs k a b ∧ CONDITION2_SY_cs k l}

/-- HOL `CLOSED_SY` (WJSCPRO.hl:63). Giant (the HOL proof spans
WJSCPRO.hl:63-3174, threading sequential limits through the rows,
`CONDITION1_SY` and the fan-convexity clause `CONDITION2_SY`).

bodyClosed 战役 W3–W7 目标；HOL CLOSED_SY WJSCPRO.hl:63-3174；
SF-89b/bodyclosed-recon 路线 B 债根（bodyclosed-w2b 起为唯一债根：LA23
`bodyClosed_p23` 经 G-B2 + G-B1 消费本件，LA18 `CLOSED_SY_p18` 经定义层孪生
桥重定向到本件）。

Statement verbatim twin of `CLOSED_SY_p18` (LocalAuto18:238). -/
theorem CLOSED_SY_cs {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (_hsys : stableSystem_cs k d s a b J f) (_hk1 : 1 < k) (_hk2 : 2 < k) :
    IsClosed (SYset_cs k a b) := by
  sorry
  -- DISCHARGES: the `BSY1body_cs` factor is closed exactly as in
  -- LocalAuto9's `CLOSED_TRI_SY_p9` (proved there; blocked here only by
  -- that theorem's `triStable_p9` hypothesis, so the intersection
  -- argument must be redone locally); the `CONDITION2_SY_cs` factor
  -- needs the limit argument on `V_SY`/`E_SY`/`F_SY`
  -- (HOL: CLOSED_SY's SKOLEM/sequential-lims part).

/-! ## Section A′: bodyclosed-w2 G-B1 bridge, redirected to `_cs`

The row-space locus of `bodyClosed_p23` is the preimage of `SYset_cs`
under the canonical LA4 flattening `matvec_p4 (fun j => (v j : Fin 3 → ℝ))`,
shifted by the SF-89b agreement legs.  Code copied from bodyclosed-w2's
`bcw2_bodyClosed_of_SYset` (LA18 block) with the `p18` names redirected to
the `_cs` twins. -/

/-- bcw2b: `rowV3_cs` at `p.val + 1` is the `p`-th row (LA23 `fw8_row_fin`
shape, private there). -/
private theorem bcw2b_row_fin_cs {m : ℕ} (l : FinVec m 3) (p : Fin m) :
    rowV3_cs l (p.val + 1) = vecmatsV3_p4 l p := by
  unfold rowV3_cs
  rw [dif_pos (by exact ⟨by omega, by have := p.isLt; omega⟩)]
  refine congrArg (vecmatsV3_p4 l) (Fin.eq_of_val_eq ?_)
  show (p.val + 1 - 1 : ℕ) = p.val
  omega

/-- bcw2b: `rowV3_cs` at a 1-based ℕ index in `1..m` (LA23 `fw8_row_nat`
shape, private there). -/
private theorem bcw2b_row_nat_cs {m : ℕ} (l : FinVec m 3) (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
    rowV3_cs l i = vecmatsV3_p4 l ⟨i - 1, by omega⟩ := by
  unfold rowV3_cs
  rw [dif_pos ⟨hi, him⟩]

/-- G-B1 (bodyclosed-w2, `cs` redirect): row-space rendering of `SYset_cs`.
The canonical LA4 flattening `matvec_p4 (fun j => (v j : Fin 3 → ℝ))` pulls
the carrier back to the `Fin m → V3` locus of `bodyClosed_p23`: that locus
is the preimage of `SYset_cs` under the flattening, shifted by the SF-89b
agreement legs (`A (p+1) (q+1) = aR p q` etc.). -/
theorem bcw2b_bodyClosed_of_SYset_cs {m : ℕ} (aR bR : Fin m → Fin m → ℝ)
    (A B : ℕ → ℕ → ℝ)
    (hA : ∀ p q : Fin m, A ((p : ℕ) + 1) ((q : ℕ) + 1) = aR p q)
    (hB : ∀ p q : Fin m, B ((p : ℕ) + 1) ((q : ℕ) + 1) = bR p q)
    (h : IsClosed (SYset_cs m A B)) :
    IsClosed {v : Fin m → V3 | (∀ i, v i ∈ ballAnnulus) ∧
      CONDITION1_SY_p4 aR bR v ∧ CONDITION2_SY_p4 v} := by
  have hrows : ∀ (v : Fin m → V3) (j : Fin m),
      vecmatsV3_p4 (matvec_p4 (fun j : Fin m => (v j : Fin 3 → ℝ))) j = v j := by
    intro v j
    show (WithLp.toLp 2 (vecmats_p4 (matvec_p4 (fun j : Fin m => (v j : Fin 3 → ℝ))) j) : V3)
        = v j
    rw [VECMATS_MATVEC_ID]
  have hcont : Continuous (fun v : Fin m → V3 =>
      matvec_p4 (fun j : Fin m => (v j : Fin 3 → ℝ))) := by
    show Continuous fun (v : Fin m → V3) (i : Fin (m * 3)) =>
      (v ⟨(i : ℕ) / 3, (Nat.div_lt_iff_lt_mul (k := 3) (by norm_num)).mpr i.isLt⟩ :
            Fin 3 → ℝ) ⟨(i : ℕ) % 3, Nat.mod_lt (i : ℕ) (by norm_num : 0 < 3)⟩
    fun_prop
  have hset : {v : Fin m → V3 | (∀ i, v i ∈ ballAnnulus) ∧
      CONDITION1_SY_p4 aR bR v ∧ CONDITION2_SY_p4 v}
      = (fun v : Fin m → V3 =>
          matvec_p4 (fun j : Fin m => (v j : Fin 3 → ℝ))) ⁻¹' (SYset_cs m A B) := by
    ext v
    have hrv : vecmatsV3_p4 (matvec_p4 (fun j : Fin m => (v j : Fin 3 → ℝ))) = v :=
      funext (hrows v)
    constructor
    · rintro ⟨hann, hc1, hc2⟩
      refine Set.mem_preimage.mp ⟨⟨?_, ?_⟩, ?_⟩
      · intro j
        rw [hrows v j]
        exact hann j
      · intro i j hi him hj hjm
        have hA' := hA ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
        have hB' := hB ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
        rw [show (i - 1 : ℕ) + 1 = i by omega, show (j - 1 : ℕ) + 1 = j by omega] at hA' hB'
        obtain ⟨hc11, hc12⟩ := hc1 ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
        rw [bcw2b_row_nat_cs _ _ hi him, bcw2b_row_nat_cs _ _ hj hjm, hrv, hA', hB']
        exact ⟨hc11, hc12⟩
      · show convexLocalFan_p4
          (V_SY_p4 (vecmatsV3_p4 (matvec_p4 (fun j : Fin m => (v j : Fin 3 → ℝ)))))
          (E_SY_p4 (vecmatsV3_p4 (matvec_p4 (fun j : Fin m => (v j : Fin 3 → ℝ)))))
          (F_SY_p4 (vecmatsV3_p4 (matvec_p4 (fun j : Fin m => (v j : Fin 3 → ℝ)))))
        rw [hrv]
        exact hc2
    · rintro ⟨⟨hann, hc1⟩, hc2⟩
      refine ⟨fun i => ?_, ?_, ?_⟩
      · rw [← hrows v i]
        exact hann i
      · intro p q
        have h1 := hc1 ((p : ℕ) + 1) ((q : ℕ) + 1) (by omega)
          (by have := p.isLt; omega) (by omega) (by have := q.isLt; omega)
        rw [bcw2b_row_fin_cs, bcw2b_row_fin_cs, hrv, hA p q, hB p q] at h1
        exact h1
      · show convexLocalFan_p4 (V_SY_p4 v) (E_SY_p4 v) (F_SY_p4 v)
        rw [← hrv]
        exact hc2
  exact hset ▸ IsClosed.preimage hcont h

/-! ## Section W3 (bodyclosed-w3): the S-A-SF kit for the `CLOSED_SY_cs`
giant replay (WJSCPRO.hl:63-460)

All pieces are fully proved; the giant `CLOSED_SY_cs` itself stays `sorry`.
Layout (HOL segment → piece):

- S-B/S-D factor closedness + sequential sandwiches (Mathlib `Tendsto` kit,
  HOL `LIM_NORM_LBOUND`/`LIM_NORM_UBOUND` + `COMPACT_BALL_ANNULUS`+SKOLEM):
  `w3cs_BSY1body_closed`, `w3cs_tendsto_row_diff`, `w3cs_seq_row_sandwich`,
  `w3cs_seq_row_annulus`.
- S-A skeleton: `closedSy_cs_of_limitTransfer` — `IsClosed (SYset_cs k a b)`
  from the CONDITION2 transfer obligation `hC2`; W7 = instantiation
  (SKOLEM/sequential-lims absorbed by `mem_closure_iff_seq_limit`).
- S-B clause-① sandwich and S-C adjacency at the limit point, with the HOL
  ℕ-index wrap bookkeeping (`POWER_MOD_FUN`/`MOD_MULT` stations at
  WJSCPRO:218/:290) absorbed by `POWER_MOD_FUN_cs`:
  `w3cs_two_le_row_of_BSY1body`, `w3cs_row_adj_cstab`, Fin-level twin
  `w3cs_two_le_next_fin`.  Both take the G-B2-supplied pinned shape
  `s = Finset.Iic (k - 1)`, `f = fun j => (1 + j) % k` as explicit
  hypotheses; under the frozen `CLOSED_SY_cs` premises (arbitrary `s f`)
  the sandwich is not derivable — see the bodyclosed-w3 DELIVERY interface
  contract (SF-89c decision point).
- S-E row distinctness (WJSCPRO:331-348): `w3cs_row_ne_next_nat`,
  `w3cs_row_ne_next_fin`.
- S-F `FAN` clauses at the limit point (WJSCPRO:349-460):
  `w3cs_sUnion_E_SY_sub_V`, `w3cs_fan1_E_SY`, `w3cs_fan2_E_SY`,
  `w3cs_Graph_E_SY`, `w3cs_fan6_of_sandwich` / `w3cs_fan6_E_SY`
  (`NONPARALLEL_BALL_ANNULUS` on the sandwich, exactly HOL :418), and the
  assembler `w3cs_FAN_of_clauses` (fan7 left to W4). -/

section W3Kit

/-- Service: the `j`-th row of the flattening is continuous (twin of LA9
`continuous_vecmatsV3_p4`, proof copied verbatim). -/
theorem w3cs_continuous_vecmatsV3 {m : ℕ} (j : Fin m) :
    Continuous (fun l : FinVec m 3 => vecmatsV3_p4 l j) := by
  unfold vecmatsV3_p4 vecmats_p4
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun _ => continuous_apply _)

/-- Service: `rowV3_cs` is continuous (twin of LA9 `continuous_rowV3_p9`). -/
theorem w3cs_continuous_rowV3 {m : ℕ} (i : ℕ) :
    Continuous (fun l : FinVec m 3 => rowV3_cs l i) := by
  unfold rowV3_cs
  split_ifs with h
  · exact w3cs_continuous_vecmatsV3 ⟨i - 1, by omega⟩
  · exact continuous_const

/-- W3 S-B/S-D: the `BSY1body_cs` factor is closed — annulus rows (closed
preimage) plus the CONDITION1 double bound (`isClosed_iInter`/preimage
route, LA9 `CLOSED_TRI_SY_p9` verbatim-adapted).  No stability input, like
the LA9 precedent's zero-consumed `_h`. -/
theorem w3cs_BSY1body_closed {k : ℕ} (a b : ℕ → ℕ → ℝ) :
    IsClosed (BSY1body_cs k a b) := by
  have hrows : IsClosed {l : FinVec k 3 | ∀ j : Fin k,
      vecmatsV3_p4 l j ∈ ballAnnulus} := by
    have hset : {l : FinVec k 3 | ∀ j : Fin k, vecmatsV3_p4 l j ∈ ballAnnulus}
        = {l : FinVec k 3 | ∀ j : Fin k,
            vecmats_p4 l j ∈
              ((WithLp.toLp (p := 2) (V := Fin 3 → ℝ)) ⁻¹' ballAnnulus :
                Set (Fin 3 → ℝ))} := rfl
    rw [hset]
    exact CLOSED_MATVEC _ (fun j =>
      (CLOSED_BALL_ANNULUS).preimage
        (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)))
  have hcond : IsClosed {l : FinVec k 3 | ∀ i j : ℕ, 1 ≤ i → i ≤ k →
      1 ≤ j → j ≤ k →
      a i j ≤ ‖rowV3_cs l i - rowV3_cs l j‖ ∧
        ‖rowV3_cs l i - rowV3_cs l j‖ ≤ b i j} := by
    have hset : {l : FinVec k 3 | ∀ i j : ℕ, 1 ≤ i → i ≤ k →
        1 ≤ j → j ≤ k →
        a i j ≤ ‖rowV3_cs l i - rowV3_cs l j‖ ∧
          ‖rowV3_cs l i - rowV3_cs l j‖ ≤ b i j}
        = ⋂ (p : ℕ × ℕ),
            {l : FinVec k 3 | (1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧ p.2 ≤ k) →
              (a p.1 p.2 ≤ ‖rowV3_cs l p.1 - rowV3_cs l p.2‖ ∧
                ‖rowV3_cs l p.1 - rowV3_cs l p.2‖ ≤ b p.1 p.2)} := by
      ext l
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h p hp => h p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2,
        fun h i j hi hj hjk hl => h (i, j) ⟨hi, hj, hjk, hl⟩⟩
    rw [hset]
    refine isClosed_iInter fun p => ?_
    by_cases hb : 1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧ p.2 ≤ k
    · have heq : {l : FinVec k 3 | (1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧ p.2 ≤ k) →
          (a p.1 p.2 ≤ ‖rowV3_cs l p.1 - rowV3_cs l p.2‖ ∧
            ‖rowV3_cs l p.1 - rowV3_cs l p.2‖ ≤ b p.1 p.2)}
          = {l : FinVec k 3 | a p.1 p.2 ≤ ‖rowV3_cs l p.1 - rowV3_cs l p.2‖ ∧
            ‖rowV3_cs l p.1 - rowV3_cs l p.2‖ ≤ b p.1 p.2} := by
        ext l
        simp [hb]
      rw [heq]
      exact isClosed_Icc.preimage
        (((w3cs_continuous_rowV3 p.1).sub (w3cs_continuous_rowV3 p.2)).norm)
    · have heq : {l : FinVec k 3 | (1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧ p.2 ≤ k) →
          (a p.1 p.2 ≤ ‖rowV3_cs l p.1 - rowV3_cs l p.2‖ ∧
            ‖rowV3_cs l p.1 - rowV3_cs l p.2‖ ≤ b p.1 p.2)} = Set.univ := by
        ext l
        simp [hb]
      rw [heq]
      exact isClosed_univ
  have hEq : BSY1body_cs k a b =
      {l : FinVec k 3 | ∀ j : Fin k, vecmatsV3_p4 l j ∈ ballAnnulus} ∩
        {l : FinVec k 3 | ∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k →
          a i j ≤ ‖rowV3_cs l i - rowV3_cs l j‖ ∧
            ‖rowV3_cs l i - rowV3_cs l j‖ ≤ b i j} := by
    ext l
    simp only [BSY1body_cs, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [hEq]
  exact hrows.inter hcond

/-- W3 S-A: row differences converge along a convergent sequence of
flattenings (the two HOL row-limit sub-goals, WJSCPRO:85/:133, in Lean
rendering: continuity of `rowV3_cs` along the sequence). -/
theorem w3cs_tendsto_row_diff {k : ℕ} {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (hu : Filter.Tendsto u Filter.atTop (nhds L)) (p q : ℕ) :
    Filter.Tendsto (fun n => rowV3_cs (u n) p - rowV3_cs (u n) q)
      Filter.atTop (nhds (rowV3_cs L p - rowV3_cs L q)) :=
  (((w3cs_continuous_rowV3 p).tendsto L).comp hu).sub
    (((w3cs_continuous_rowV3 q).tendsto L).comp hu)

/-- W3 S-B (sequential `LIM_NORM` form): the CONDITION1 double bound
passes to the limit (`le_of_tendsto` twice on the row-difference
sequence; HOL WJSCPRO:180/:187). -/
theorem w3cs_seq_row_sandwich {k : ℕ} {a b : ℕ → ℕ → ℝ}
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (hu : Filter.Tendsto u Filter.atTop (nhds L))
    (humem : ∀ n, u n ∈ BSY1body_cs k a b) {p q : ℕ}
    (hp : 1 ≤ p) (hpk : p ≤ k) (hq : 1 ≤ q) (hqk : q ≤ k) :
    a p q ≤ ‖rowV3_cs L p - rowV3_cs L q‖ ∧
      ‖rowV3_cs L p - rowV3_cs L q‖ ≤ b p q := by
  have htn : Filter.Tendsto
      (fun n => ‖rowV3_cs (u n) p - rowV3_cs (u n) q‖) Filter.atTop
      (nhds ‖rowV3_cs L p - rowV3_cs L q‖) :=
    (w3cs_tendsto_row_diff hu p q).norm
  have hbnd : ∀ n, a p q ≤ ‖rowV3_cs (u n) p - rowV3_cs (u n) q‖ ∧
      ‖rowV3_cs (u n) p - rowV3_cs (u n) q‖ ≤ b p q :=
    fun n => (humem n).2 p q hp hpk hq hqk
  exact ⟨ge_of_tendsto htn (Filter.Eventually.of_forall fun n => (hbnd n).1),
    le_of_tendsto htn (Filter.Eventually.of_forall fun n => (hbnd n).2)⟩

/-- W3 S-D: every row of the limit point stays in the ball annulus
(`CLOSED_BALL_ANNULUS` + row continuity; HOL COMPACT_BALL_ANNULUS+SKOLEM,
WJSCPRO:317-330). -/
theorem w3cs_seq_row_annulus {k : ℕ} {a b : ℕ → ℕ → ℝ}
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (hu : Filter.Tendsto u Filter.atTop (nhds L))
    (humem : ∀ n, u n ∈ BSY1body_cs k a b) (j : Fin k) :
    vecmatsV3_p4 L j ∈ ballAnnulus :=
  (CLOSED_BALL_ANNULUS).mem_of_tendsto
    ((w3cs_continuous_vecmatsV3 j).tendsto L |>.comp hu)
    (Filter.Eventually.of_forall fun n => (humem n).1 j)

/-- W3 S-A skeleton (the giant's closedness core): `SYset_cs k a b` is
closed once the CONDITION2 transfer obligation `hC2` — the S-G-SL content
(limit-point fan-convexity) — is supplied.  W7 instantiates `hC2` from
`stableSystem_cs`; the `BSY1body_cs` leg is discharged here via
`w3cs_BSY1body_closed` (S-B/S-D). -/
theorem closedSy_cs_of_limitTransfer {k : ℕ} {a b : ℕ → ℕ → ℝ}
    (hC2 : ∀ (u : ℕ → FinVec k 3) (L : FinVec k 3), (∀ n, u n ∈ SYset_cs k a b) →
      Filter.Tendsto u Filter.atTop (nhds L) → L ∈ BSY1body_cs k a b →
      CONDITION2_SY_cs k L) :
    IsClosed (SYset_cs k a b) := by
  refine isClosed_of_closure_subset fun L hL => ?_
  rw [mem_closure_iff_seq_limit] at hL
  obtain ⟨u, humem, huto⟩ := hL
  have hLb : L ∈ BSY1body_cs k a b :=
    (w3cs_BSY1body_closed a b).mem_of_tendsto huto
      (Filter.Eventually.of_forall fun n => (humem n).1)
  exact ⟨hLb, hC2 u L humem huto hLb⟩

/-- W3 S-B, clause ① at the limit point (HOL WJSCPRO:186-255): every pair
of distinct 1-based rows of the limit point is 2-separated.  The ℕ-index
wrap bookkeeping is exactly HOL's `POWER_MOD_FUN`/`MOD_MULT` stations
(:218): the pair `(p, 0)` stands in for `(p, k)` and `(1, 0)` for `(k, 1)`
via the periodicity clause of `constraintSystem_cs` and
`POWER_MOD_FUN_cs` (`f^[k] x = x % k`).  `hs`/`hf` are the G-B2-supplied
pinned shape (`s = 0..k-1`, successor `f`); under the frozen
`CLOSED_SY_cs` premises they are additional obligations — see the
bodyclosed-w3 DELIVERY interface contract (SF-89c decision point). -/
theorem w3cs_two_le_row_of_BSY1body {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k) (hk1 : 1 < k)
    (L : FinVec k 3) (hL : L ∈ BSY1body_cs k a b)
    {p q : ℕ} (hp : 1 ≤ p) (hpk : p ≤ k) (hq : 1 ≤ q) (hqk : q ≤ k)
    (hpq : p ≠ q) : (2:ℝ) ≤ ‖rowV3_cs L p - rowV3_cs L q‖ := by
  obtain ⟨⟨_, _, _, hsym, hper, _, _⟩, hcl1, _, _⟩ := hsys
  subst hs
  subst hf
  have hpow : ∀ x : ℕ, (fun j => (1 + j) % k)^[k] x = x % k := by
    intro x
    rw [POWER_MOD_FUN_cs k x k (le_of_lt hk1) hk1, Nat.add_mod_left]
  have h0s : (0:ℕ) ∈ Finset.Iic (k - 1) := Finset.mem_Iic.mpr (Nat.zero_le _)
  have hsmem : ∀ x : ℕ, 1 ≤ x → x ≤ k - 1 → x ∈ Finset.Iic (k - 1) :=
    fun x _ hx => Finset.mem_Iic.mpr hx
  rcases Nat.lt_or_ge p k with hplt | hpge
  · rcases Nat.lt_or_ge q k with hqlt | hqge
    · exact (hcl1 p (hsmem p hp (by omega)) q (hsmem q hq (by omega))
        (by omega)).trans (hL.2 p q hp hpk hq hqk).1
    · -- q = k: a p k = a p (f^[k] k) = a p 0 ≥ 2 (clause ① at (p, 0))
      have hq2 : q = k := le_antisymm hqk hqge
      have hper1 : a p k = a p 0 := by
        have h := (hper p k).1
        rw [hpow k, Nat.mod_self] at h
        exact h
      have h2 : (2:ℝ) ≤ a p 0 :=
        hcl1 p (hsmem p hp (by omega)) 0 h0s (by omega)
      have h3 : (2:ℝ) ≤ a p q := by
        rw [hq2]; exact hper1 ▸ h2
      exact h3.trans (hL.2 p q hp hpk hq hqk).1
  · have hp2 : p = k := le_antisymm hpk hpge
    rcases Nat.lt_or_ge q k with hqlt | hqge
    · -- p = k: a k q = a q k = a q 0 ≥ 2 (clause ① at (q, 0))
      have hper1 : a q k = a q 0 := by
        have h := (hper q k).1
        rw [hpow k, Nat.mod_self] at h
        exact h
      have h2 : (2:ℝ) ≤ a q 0 :=
        hcl1 q (hsmem q hq (by omega)) 0 h0s (by omega)
      have h3 : (2:ℝ) ≤ a p q := by
        rw [hp2, ← (hsym q k).1]; exact hper1 ▸ h2
      exact h3.trans (hL.2 p q hp hpk hq hqk).1
    · -- p = q = k contradicts p ≠ q
      have hq2 : q = k := le_antisymm hqk hqge
      omega

/-- W3 S-C, adjacency upper bound at the limit point (HOL WJSCPRO:256-315
with the :290 wrap station): the chord between 1-based row `p` and its
cyclic successor row `p % k + 1` is at most `cstab_p4` — clause ②
`b p (f p) ≤ cstab` transported through the periodicity clause and
`POWER_MOD_FUN_cs`.  Pinned shape as in
`w3cs_two_le_row_of_BSY1body`. -/
theorem w3cs_row_adj_cstab {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k) (hk1 : 1 < k)
    (L : FinVec k 3) (hL : L ∈ BSY1body_cs k a b)
    {p : ℕ} (hp : 1 ≤ p) (hpk : p ≤ k) :
    ‖rowV3_cs L p - rowV3_cs L (p % k + 1)‖ ≤ cstab_p4 := by
  obtain ⟨⟨_, _, _, hsym, hper, _, _⟩, _, hcl2, _⟩ := hsys
  subst hs
  subst hf
  have hpow : ∀ x : ℕ, (fun j => (1 + j) % k)^[k] x = x % k := by
    intro x
    rw [POWER_MOD_FUN_cs k x k (le_of_lt hk1) hk1, Nat.add_mod_left]
  have h0s : (0:ℕ) ∈ Finset.Iic (k - 1) := Finset.mem_Iic.mpr (Nat.zero_le _)
  have hsmem : ∀ x : ℕ, 1 ≤ x → x ≤ k - 1 → x ∈ Finset.Iic (k - 1) :=
    fun x _ hx => Finset.mem_Iic.mpr hx
  have hmod : p % k + 1 ≤ k := by
    have := Nat.mod_lt p (by omega : (0:ℕ) < k)
    omega
  have hle := (hL.2 p (p % k + 1) hp hpk (by omega) hmod).2
  rcases Nat.lt_or_ge p k with hplt | hpge
  · rw [Nat.mod_eq_of_lt hplt] at hle ⊢
    rcases Nat.lt_or_ge (p + 1) k with hplt2 | hpge2
    · -- clause ② at p ∈ s, f p = (1 + p) % k = p + 1
      have hb2 : b p ((1 + p) % k) ≤ cstab_p4 :=
        (hcl2 p (hsmem p hp (by omega))).2
      rw [Nat.mod_eq_of_lt (show (1:ℕ) + p < k by omega),
        Nat.add_comm 1 p] at hb2
      exact hle.trans hb2
    · -- p + 1 = k: b p k = b p (f^[k] k) = b p 0 = b p (f p) ≤ cstab
      have hpk2 : p + 1 = k := le_antisymm (by omega) hpge2
      have hb2 : b p ((1 + p) % k) ≤ cstab_p4 :=
        (hcl2 p (hsmem p hp (by omega))).2
      rw [Nat.add_comm 1 p, hpk2, Nat.mod_self k] at hb2
      have hper1 : b p k = b p 0 := by
        have h := (hper p k).2
        rw [hpow k, Nat.mod_self] at h
        exact h
      have hb3 : b p (p + 1) ≤ cstab_p4 := by
        rw [hpk2]
        have hb5 : b p k ≤ cstab_p4 := by rw [hper1]; exact hb2
        exact hb5
      exact hle.trans hb3
  · -- p = k: the chord is (k, 1); b k 1 = b 1 k = b 1 0 = b 0 1 ≤ cstab
    have hp2 : p = k := le_antisymm hpk hpge
    rw [hp2] at hle ⊢
    have hkk : k % k = 0 := Nat.mod_self k
    rw [hkk] at hle ⊢
    rw [Nat.zero_add] at hle ⊢
    have hcl21 : b 0 1 ≤ cstab_p4 := by
      have h : b 0 ((1 + 0) % k) ≤ cstab_p4 := (hcl2 0 h0s).2
      rw [Nat.add_zero, Nat.mod_eq_of_lt hk1] at h
      exact h
    have hper1 : b 1 k = b 1 0 := by
      have h := (hper 1 k).2
      rw [hpow k, Nat.mod_self] at h
      exact h
    have hbkk : b k 1 = b 0 1 := by
      rw [(hsym k 1).2.1]
      exact hper1.trans (hsym 1 0).2.1
    have hbk2 : b k 1 ≤ cstab_p4 := by
      rw [hbkk]; exact hcl21
    exact hle.trans hbk2

/-- W3 S-B, Fin-level corollary: the consecutive-row chord sandwich lower
half at `Fin k` indices — the `fan6`/`VEC0_BALL_ANNULUS` input at the
limit point (W4 consumes it verbatim). -/
theorem w3cs_two_le_next_fin {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k) (hk2 : 2 < k)
    (L : FinVec k 3) (hL : L ∈ BSY1body_cs k a b) (i : Fin k) :
    (2:ℝ) ≤ ‖vecmatsV3_p4 L i - vecmatsV3_p4 L (finNext i)‖ := by
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  have hp : (1:ℕ) ≤ i.val + 1 := by omega
  have hpk : i.val + 1 ≤ k := by have := i.isLt; omega
  have hq : (1:ℕ) ≤ (finNext i).val + 1 := by omega
  have hqk : (finNext i).val + 1 ≤ k := by
    have := Nat.mod_lt (i.val + 1) (by omega : (0:ℕ) < k)
    omega
  have hne : i.val + 1 ≠ (finNext i).val + 1 := by
    show i.val + 1 ≠ (i.val + 1) % k + 1
    rcases Nat.lt_or_ge (i.val + 1) k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have he : i.val + 1 = k := le_antisymm (by have := i.isLt; omega) hge
      rw [he, Nat.mod_self]; omega
  rw [← bcw2b_row_fin_cs, ← bcw2b_row_fin_cs]
  exact w3cs_two_le_row_of_BSY1body hsys hs hf hk1 L hL hp hpk hq hqk hne

/-- W3 S-E (HOL WJSCPRO:331-348), ℕ row level: row `p` and its cyclic
successor row differ — equality would give chord 0 against the 2-separation
of `w3cs_two_le_row_of_BSY1body`. -/
theorem w3cs_row_ne_next_nat {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k) (hk2 : 2 < k)
    (L : FinVec k 3) (hL : L ∈ BSY1body_cs k a b)
    {p : ℕ} (hp : 1 ≤ p) (hpk : p ≤ k) :
    rowV3_cs L p ≠ rowV3_cs L (p % k + 1) := by
  intro heq
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  have hq1 : (1:ℕ) ≤ p % k + 1 := by omega
  have hmod : p % k + 1 ≤ k := by
    have := Nat.mod_lt p (by omega : (0:ℕ) < k)
    omega
  have hne : p ≠ p % k + 1 := by
    rcases Nat.lt_or_ge p k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have he : p = k := le_antisymm hpk hge
      rw [he, Nat.mod_self]; omega
  have h2 := w3cs_two_le_row_of_BSY1body hsys hs hf hk1 L hL hp hpk
    hq1 hmod hne
  rw [heq, sub_self, norm_zero] at h2
  linarith

/-- W3 S-E, Fin level (the `Graph` input): consecutive `E_SY` rows differ. -/
theorem w3cs_row_ne_next_fin {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k) (hk2 : 2 < k)
    (L : FinVec k 3) (hL : L ∈ BSY1body_cs k a b) (i : Fin k) :
    vecmatsV3_p4 L i ≠ vecmatsV3_p4 L (finNext i) := by
  have hp : (1:ℕ) ≤ i.val + 1 := by omega
  have hpk : i.val + 1 ≤ k := by have := i.isLt; omega
  intro heq
  rw [← bcw2b_row_fin_cs, ← bcw2b_row_fin_cs] at heq
  refine w3cs_row_ne_next_nat hsys hs hf hk2 L hL hp hpk ?_
  show rowV3_cs L (i.val + 1) = rowV3_cs L ((finNext i).val + 1)
  exact heq

/-- W3 S-F, clause 1: `E_SY` edges sit inside the `V_SY` row range
(unconditional). -/
theorem w3cs_sUnion_E_SY_sub_V {k : ℕ} (L : FinVec k 3) :
    (⋃₀ E_SY_p4 (vecmatsV3_p4 L)) ⊆ V_SY_p4 (vecmatsV3_p4 L) := by
  rintro x ⟨e, he, hx⟩
  simp only [E_SY_p4, Set.mem_image, Set.mem_univ, true_and] at he
  obtain ⟨i, rfl⟩ := he
  simp at hx
  rcases hx with rfl | rfl
  · exact ⟨i, rfl⟩
  · exact ⟨finNext i, rfl⟩

/-- W3 S-F, `fan1` clause: the `V_SY` row range is finite and nonempty
(unconditional, `k ≥ 1`). -/
theorem w3cs_fan1_E_SY {k : ℕ} (L : FinVec k 3) (hk : 0 < k) :
    Fan.fan1 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L)) := by
  refine ⟨Set.finite_range _, fun hcon => ?_⟩
  have hm : vecmatsV3_p4 L ⟨0, hk⟩ ∈ V_SY_p4 (vecmatsV3_p4 L) :=
    Set.mem_range_self _
  rw [hcon] at hm
  simp at hm

/-- W3 S-F, `fan2` clause: the origin is not a row (rows lie in the ball
annulus, whose norm floor is 2). -/
theorem w3cs_fan2_E_SY {k : ℕ} {a b : ℕ → ℕ → ℝ} (L : FinVec k 3)
    (hL : L ∈ BSY1body_cs k a b) :
    Fan.fan2 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L)) := by
  intro hmem
  obtain ⟨j, hj⟩ := Set.mem_range.mp hmem
  have hm := hL.1 j
  rw [hj] at hm
  obtain ⟨hb1, _⟩ := ballAnnulus_norm_bounds hm
  have h0 : ‖(0:V3)‖ = (0:ℝ) := norm_zero
  linarith

/-- W3 S-F, `Graph` clause: every `E_SY` edge has exactly two elements
(consecutive rows differ, S-E). -/
theorem w3cs_Graph_E_SY {k : ℕ} (L : FinVec k 3)
    (hd : ∀ i : Fin k, vecmatsV3_p4 L i ≠ vecmatsV3_p4 L (finNext i)) :
    Fan.Graph (E_SY_p4 (vecmatsV3_p4 L)) := by
  intro e he
  simp only [E_SY_p4, Set.mem_image, Set.mem_univ, true_and] at he
  obtain ⟨i, rfl⟩ := he
  have fin : ({vecmatsV3_p4 L i, vecmatsV3_p4 L (finNext i)} : Set V3).Finite :=
    Set.finite_insert.mpr (Set.finite_singleton _)
  refine ⟨fin, ?_⟩
  have hc : fin.toFinset = {vecmatsV3_p4 L i, vecmatsV3_p4 L (finNext i)} := by
    ext x
    simp
  rw [hc, Finset.card_insert_of_notMem (by simp [hd i])]
  simp

/-- W3 S-F, `fan6` core: no `E_SY` edge is collinear with the origin
(`NONPARALLEL_BALL_ANNULUS` on the sandwich double bound, exactly HOL
WJSCPRO:418). -/
theorem w3cs_fan6_of_sandwich {k : ℕ} (L : FinVec k 3)
    (hann : ∀ j : Fin k, vecmatsV3_p4 L j ∈ ballAnnulus)
    (h2 : ∀ i : Fin k, (2:ℝ) ≤ ‖vecmatsV3_p4 L i - vecmatsV3_p4 L (finNext i)‖)
    (hup : ∀ i : Fin k,
      ‖vecmatsV3_p4 L i - vecmatsV3_p4 L (finNext i)‖ ≤ cstab_p4) :
    Fan.fan6 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L)) := by
  intro e he
  simp only [E_SY_p4, Set.mem_image, Set.mem_univ, true_and] at he
  obtain ⟨i, rfl⟩ := he
  intro hc
  exact NONPARALLEL_BALL_ANNULUS (hann i) (hann (finNext i)) (h2 i) (hup i) hc

/-- W3 S-F, `fan6` at the limit point (pinned shape): the S-B sandwich
(`w3cs_two_le_next_fin`) and the S-C adjacency
(`w3cs_row_adj_cstab` via `bcw2b_row_fin_cs`) feed
`NONPARALLEL_BALL_ANNULUS`. -/
theorem w3cs_fan6_E_SY {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k) (hk2 : 2 < k)
    (L : FinVec k 3) (hL : L ∈ BSY1body_cs k a b) :
    Fan.fan6 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L)) := by
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  refine w3cs_fan6_of_sandwich L (fun j => hL.1 j)
    (w3cs_two_le_next_fin hsys hs hf hk2 L hL) (fun i => ?_)
  have hp : (1:ℕ) ≤ i.val + 1 := by omega
  have hpk : i.val + 1 ≤ k := by have := i.isLt; omega
  rw [← bcw2b_row_fin_cs, ← bcw2b_row_fin_cs]
  exact w3cs_row_adj_cstab hsys hs hf hk1 L hL hp hpk

/-- W3 S-F capstone: the exact `FAN 0 V E` assembly order for the limit
point — W4 supplies `fan7` (S-G) and consumes this assembler verbatim. -/
theorem w3cs_FAN_of_clauses {k : ℕ} (L : FinVec k 3)
    (hU : (⋃₀ E_SY_p4 (vecmatsV3_p4 L)) ⊆ V_SY_p4 (vecmatsV3_p4 L))
    (hG : Fan.Graph (E_SY_p4 (vecmatsV3_p4 L)))
    (hf1 : Fan.fan1 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L)))
    (hf2 : Fan.fan2 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L)))
    (hf6 : Fan.fan6 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L)))
    (hf7 : Fan.fan7 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L))) :
    Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L)) :=
  ⟨hU, hG, hf1, hf2, hf6, hf7⟩

end W3Kit

end Kepler.Text
