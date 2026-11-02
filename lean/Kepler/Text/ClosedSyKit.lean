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
import Kepler.Text.Planarity

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

Statement verbatim twin of `CLOSED_SY_p18` (LocalAuto18:238).
SF-89c (2026-11-02, bodyclosed-w3 §2.2): the premise pins `s = 0..k-1` and
`f = succ mod k` exactly as HOL `stable_system k d (0..k-1) a b J
(\i. (1+i) MOD k)` — the free-`s f` generalization had no supply for the
row-pair lower bound (`s ∩ [1,k] = ∅`) and is refuted by the m=6 collapse
family; G-B2 supplies precisely this pinned shape. -/
theorem CLOSED_SY_cs {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (_hsys : stableSystem_cs k d s a b J f) (_hs : s = Finset.Iic (k - 1))
    (_hf : f = fun j => (1 + j) % k) (_hk1 : 1 < k) (_hk2 : 2 < k) :
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

/-! ## Section W5 (bodyclosed-w5): S-H edge×edge — the cross-dot sign wall
(WJSCPRO.hl:874-2291 + :1191-1262 limit side; the `{y',z'} ∈ E_SY (v N1)`
sequential transfers at :1133/:1450 are definitional in the Fin-rendering;
the ℕ wrap stations :2215/:2250 are absorbed by `finNext`).

Architecture (self-contained reconstruction; HOL branch bookkeeping replaced):
- `w5cs_false_of_sign_wall` (pointwise engine): fan7 at a point + two
  disjoint edges + the four strict cross-dot inequalities ⟹ False
  (`condition_cross_dot_4point` twice; the two triple-products coincide by
  `cross_anticomm`; the common point lies in both open fans, hence in
  `affGe {0} (e1 ∩ e2) = {0}` — against `origin_is_not_aff_gt_fan`).
- `w5cs_tendsto_cross_dot` + `w5cs_tendsto_pos_eventual` +
  `w5cs_eventual_ne`: the sequential layer (LA4 `CROSS_DOT_SEQUENTIALLY`
  rendered at Fin rows; HOL `ABS_LT_EPSI` stations become Mathlib
  `Metric.tendsto_atTop`).
- `w5cs_false_of_limit_wall` (5a capstone, unified W6/W7 premise shape
  「u, L, ∀ n, u n ∈ SYset_cs, Tendsto u atTop (𝓝 L), L ∈ BSY1body_cs」 +
  G-B2-pinned hsys/hs/hf): the sign wall at the limit point transfers to a
  large index, where fan7 (from CONDITION2 at `u n`) and edge-disjointness
  (eventual 2-separation) close the wall to False. -/

section W5Kit

/-- W5 service: a sequence converging to a positive limit is eventually
positive (HOL `ABS_LT_EPSI` station, Mathlib rendering). -/
theorem w5cs_tendsto_pos_eventual {g : ℕ → ℝ} {c : ℝ}
    (hg : Filter.Tendsto g Filter.atTop (nhds c)) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < g n := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hg (c / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [Real.dist_eq] at h
  have h2 := abs_lt.mp h
  linarith

/-- W5 service: two row sequences with distinct limits are eventually
distinct as points. -/
theorem w5cs_eventual_ne {f g : ℕ → V3} {x y : V3}
    (hf : Filter.Tendsto f Filter.atTop (nhds x))
    (hg : Filter.Tendsto g Filter.atTop (nhds y))
    (hxy : x ≠ y) : ∃ N : ℕ, ∀ n ≥ N, f n ≠ g n := by
  have hsub : Filter.Tendsto (fun n => f n - g n) Filter.atTop (nhds (x - y)) := hf.sub hg
  have hnorm : Filter.Tendsto (fun n => ‖f n - g n‖) Filter.atTop (nhds ‖x - y‖) := hsub.norm
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨N, hN⟩ := w5cs_tendsto_pos_eventual hnorm hpos
  refine ⟨N, fun n hn hfg => ?_⟩
  have hz := hN n hn
  rw [hfg] at hz
  simp at hz

/-- W5 service: `affGe {x} ∅ = {x}` (public twin of the private
`affGe_empty_singleton` in Planarity; HOL `AFF_GE_EQ_AFFINE_HULL` +
`AFFINE_HULL_SING`). -/
theorem w5cs_affGe_empty (x : V3) : affGe {x} ∅ = {x} := by
  have hx : x ∈ affGe {x} ∅ := by
    simp only [affGe, Set.mem_setOf_eq]
    refine ⟨fun v => if v = x then (1:ℝ) else 0, ?_, ?_, ?_, ?_⟩
    · exact (Set.finite_singleton x).union Set.finite_empty
    · have hfin : ({x} ∪ ∅ : Set V3).Finite := by
        exact (Set.finite_singleton x).union Set.finite_empty
      have htf : hfin.toFinset = {x} := by ext u; simp
      rw [htf]
      simp
    · intro v hv
      exact absurd hv (Set.notMem_empty v)
    · have hfin : ({x} ∪ ∅ : Set V3).Finite := by
        exact (Set.finite_singleton x).union Set.finite_empty
      have htf : hfin.toFinset = {x} := by ext u; simp
      rw [htf]
      simp
  ext w
  by_cases hw : w = x
  · subst hw
    constructor
    · intro _
      exact Set.mem_singleton_iff.mpr rfl
    · intro _
      exact hx
  · constructor
    · intro hc
      simp only [affGe, Set.mem_setOf_eq] at hc
      obtain ⟨f, hfin, h1, h2, h3⟩ := hc
      have htf : hfin.toFinset = {x} := by ext u; simp
      rw [htf] at h1 h3
      simp only [Finset.sum_singleton] at h1 h3
      rw [h3] at h1
      simpa using h1
    · intro hc
      exact absurd (Set.mem_singleton_iff.mp hc) hw

set_option maxHeartbeats 2000000 in
/-- W5 service: `condition_cross_dot_4point` at the origin, with the
`have`-lets discharged into an explicit statement (the `(w - 0 : V3)` forms
must stay explicit `WithLp.ofLp` coercions; the bare coercion
elaboration diverges). -/
theorem w5cs_cond4 (y z v u : V3) (hnc : ¬ Collinear3 (0:V3) v u)
    (h1 : 0 < (crossProduct (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ)
        (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp (u - 0 : V3) : Fin 3 → ℝ))
    (h2 : 0 < -((crossProduct (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ)
        (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp (v - 0 : V3) : Fin 3 → ℝ))) :
    (WithLp.toLp 2 (crossProduct
        (crossProduct (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ))
        (crossProduct (WithLp.ofLp (v - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (u - 0 : V3) : Fin 3 → ℝ))) + 0 : V3)
      ∈ affGt ({0} : Set V3) ({v, u} : Set V3) :=
  condition_cross_dot_4point (0:V3) y z v u hnc h1 h2

set_option maxHeartbeats 2000000 in
/-- W5 core engine (HOL WJSCPRO:1385-1490, de-branchified): at a point
where fan7 holds, two disjoint edges with all four strict cross-dot
inequalities (each edge straddles the other's plane) cannot exist.  The
conjunction `wall1 ∧ wall2` says edge `{y1, z1}` straddles plane `{0, y, z}`
with `y1` on the `(y × z)`-positive side; `wall3 ∧ wall4` says edge
`{y, z}` straddles plane `{0, y1, z1}` with `z` on the `(y1 × z1)`-positive
side; the orientation is coherent because both open fans share the
intersection line of the two planes. -/
theorem w5cs_false_of_sign_wall {y z y1 z1 : V3}
    (hf7 : affGe ({0} : Set V3) ({y, z} : Set V3) ∩ affGe ({0} : Set V3) ({y1, z1} : Set V3)
        = affGe ({0} : Set V3) (({y, z} : Set V3) ∩ {y1, z1}))
    (hdisj : ({y, z} : Set V3) ∩ {y1, z1} = ∅)
    (hnc1 : ¬ Collinear3 (0:V3) y z) (hnc2 : ¬ Collinear3 (0:V3) y1 z1)
    (wall1 : 0 < (crossProduct (WithLp.ofLp y1 : Fin 3 → ℝ) (WithLp.ofLp z1 : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp z : Fin 3 → ℝ))
    (wall2 : 0 < -((crossProduct (WithLp.ofLp y1 : Fin 3 → ℝ) (WithLp.ofLp z1 : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp y : Fin 3 → ℝ)))
    (wall3 : 0 < (crossProduct (WithLp.ofLp z : Fin 3 → ℝ) (WithLp.ofLp y : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp z1 : Fin 3 → ℝ))
    (wall4 : 0 < -((crossProduct (WithLp.ofLp z : Fin 3 → ℝ) (WithLp.ofLp y : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp y1 : Fin 3 → ℝ))) : False := by
  have hy0 : y ≠ 0 := fun he => hnc1 (collinear3_of_eq he)
  have hz0 : z ≠ 0 := fun he => hnc1 (collinear3_pair_left he)
  have hy10 : y1 ≠ 0 := fun he => hnc2 (collinear3_of_eq he)
  have hz10 : z1 ≠ 0 := fun he => hnc2 (collinear3_pair_left he)
  have hdis1 : Disjoint ({0} : Set V3) ({y, z} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hy0 h.symm, fun h => hz0 h.symm⟩
  have hdis2 : Disjoint ({0} : Set V3) ({y1, z1} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hy10 h.symm, fun h => hz10 h.symm⟩
  have e1 : 0 < (crossProduct (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ)
      (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ) := by
    simpa using wall1
  have e2 : 0 < -((crossProduct (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ)
      (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ)) := by
    simpa using wall2
  have e3 : 0 < (crossProduct (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ)
      (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ) := by
    simpa using wall3
  have e4 : 0 < -((crossProduct (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ)
      (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ)) := by
    simpa using wall4
  have c1 : (WithLp.toLp 2 (crossProduct
      (crossProduct (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ))
      (crossProduct (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ))) + 0 : V3)
      ∈ affGt ({0} : Set V3) ({y, z} : Set V3) :=
    w5cs_cond4 y1 z1 y z hnc1 e1 e2
  have c2 : (WithLp.toLp 2 (crossProduct
      (crossProduct (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ))
      (crossProduct (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ))) + 0 : V3)
      ∈ affGt ({0} : Set V3) ({y1, z1} : Set V3) :=
    w5cs_cond4 z y y1 z1 hnc2 e3 e4
  have hkey : crossProduct
      (crossProduct (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ))
      (crossProduct (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ))
      = crossProduct
      (crossProduct (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ))
      (crossProduct (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ)) := by
    have hzy : (crossProduct (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ))
        = -(crossProduct (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ)) :=
      (cross_anticomm _ _).symm
    rw [hzy, map_neg, LinearMap.neg_apply, cross_anticomm]
  have h2' : (WithLp.toLp 2 (crossProduct
      (crossProduct (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ))
      (crossProduct (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ))) + 0 : V3)
      = (WithLp.toLp 2 (crossProduct
      (crossProduct (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ))
      (crossProduct (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ))) + 0 : V3) := by
    rw [hkey]
  rw [h2'] at c2
  have hmem : (WithLp.toLp 2 (crossProduct
      (crossProduct (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ))
      (crossProduct (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ))) + 0 : V3)
      ∈ affGe ({0} : Set V3) ({y, z} : Set V3) ∩ affGe ({0} : Set V3) ({y1, z1} : Set V3) :=
    ⟨aff_gt_subset_aff_ge (x := (0:V3)) (v := y) (u := z) hdis1 c1,
      aff_gt_subset_aff_ge (x := (0:V3)) (v := y1) (u := z1) hdis2 c2⟩
  have h3 : affGe ({0} : Set V3) ({y, z} : Set V3) ∩ affGe ({0} : Set V3) ({y1, z1} : Set V3)
      = ({0} : Set V3) := by
    rw [hf7, hdisj]
    exact w5cs_affGe_empty 0
  have hmem0 : (WithLp.toLp 2 (crossProduct
      (crossProduct (WithLp.ofLp (y1 - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z1 - 0 : V3) : Fin 3 → ℝ))
      (crossProduct (WithLp.ofLp (y - 0 : V3) : Fin 3 → ℝ) (WithLp.ofLp (z - 0 : V3) : Fin 3 → ℝ))) + 0 : V3) = 0 := by
    have hm := hmem
    rw [h3] at hm
    exact Set.mem_singleton_iff.mp hm
  rw [hmem0] at c1
  have hnot : (0:V3) ∉ affGt ({0} : Set V3) ({y, z} : Set V3) := by
    refine origin_is_not_aff_gt_fan (x := (0:V3)) (v := y) (u := z) ?_ hdis1
    rw [← collinear3_iff_mem_affineSpan (v0 := (0:V3)) (v1 := y) (Ne.symm hy0)]
    exact hnc1
  exact hnot c1

/-- W5 service: the cross-dot of three rows converges along a convergent
sequence of flattenings (LA4 `CROSS_DOT_SEQUENTIALLY`, HOL
`CROSS_DOT_SEQUENTIALLY` dih2k.hl:1467). -/
theorem w5cs_tendsto_cross_dot {k : ℕ} {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (hu : Filter.Tendsto u Filter.atTop (nhds L)) (p q r : Fin k) :
    Filter.Tendsto (fun n => (crossProduct (WithLp.ofLp (vecmatsV3_p4 (u n) p) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 (u n) q) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 (u n) r) : Fin 3 → ℝ)) Filter.atTop
      (nhds ((crossProduct (WithLp.ofLp (vecmatsV3_p4 L p) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L q) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L r) : Fin 3 → ℝ))) :=
  CROSS_DOT_SEQUENTIALLY (((w3cs_continuous_vecmatsV3 p).tendsto L).comp hu)
    (((w3cs_continuous_vecmatsV3 q).tendsto L).comp hu)
    (((w3cs_continuous_vecmatsV3 r).tendsto L).comp hu)

/-- W5 5a capstone (HOL WJSCPRO:660-1490): under the unified limit-point
premises and the G-B2-pinned stability shape, two pairwise-distinct edges
of the limit fan whose segments strictly straddle each other's planes
(the four-fold cross-dot sign wall) are impossible — the wall transfers to
a large index where fan7 (carried by `CONDITION2_SY_cs` at `u n`) and the
eventual 2-separation of the edges close it.  This is the sole
sequence-dependent content of fan7's edge×edge layer. -/
theorem w5cs_false_of_limit_wall {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k)
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (humem : ∀ n, u n ∈ SYset_cs k a b)
    (huto : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : L ∈ BSY1body_cs k a b)
    {i i' : Fin k} (hii : i ≠ i') (hiz : i ≠ finNext i')
    (hzi : finNext i ≠ i') (hzz : finNext i ≠ finNext i')
    (wall1 : 0 < (crossProduct (WithLp.ofLp (vecmatsV3_p4 L i') : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L (finNext i')) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ))
    (wall2 : 0 < -((crossProduct (WithLp.ofLp (vecmatsV3_p4 L i') : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L (finNext i')) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ)))
    (wall3 : 0 < (crossProduct (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L (finNext i')) : Fin 3 → ℝ))
    (wall4 : 0 < -((crossProduct (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L i') : Fin 3 → ℝ))) : False := by
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  have hk2 : 2 < k := by omega
  have hsep : ∀ p q : ℕ, 1 ≤ p → p ≤ k → 1 ≤ q → q ≤ k → p ≠ q →
      (2:ℝ) ≤ ‖rowV3_cs L p - rowV3_cs L q‖ :=
    fun p q hp hpk hq hqk hpq => w3cs_two_le_row_of_BSY1body hsys hs hf hk1 L hL hp hpk hq hqk hpq
  have htwo : ∀ p q : Fin k, p ≠ q → (2:ℝ) ≤ ‖vecmatsV3_p4 L p - vecmatsV3_p4 L q‖ := by
    intro p q hpq
    rw [← bcw2b_row_fin_cs, ← bcw2b_row_fin_cs]
    exact hsep (p.val + 1) (q.val + 1) (by omega) (by have := p.isLt; omega)
      (by omega) (by have := q.isLt; omega) (fun h => hpq (Fin.ext (by omega)))
  have htend : ∀ j : Fin k, Filter.Tendsto (fun n => vecmatsV3_p4 (u n) j) Filter.atTop
      (nhds (vecmatsV3_p4 L j)) := fun j =>
    ((w3cs_continuous_vecmatsV3 j).tendsto L).comp huto
  have dne : ∀ p q : Fin k, p ≠ q → vecmatsV3_p4 L p ≠ vecmatsV3_p4 L q := by
    intro p q hpq he
    have h2 := htwo p q hpq
    rw [he, sub_self, norm_zero] at h2
    linarith
  obtain ⟨n1, hn1⟩ := w5cs_eventual_ne (htend i) (htend i') (dne i i' hii)
  obtain ⟨n2, hn2⟩ := w5cs_eventual_ne (htend i) (htend (finNext i')) (dne i (finNext i') hiz)
  obtain ⟨n3, hn3⟩ := w5cs_eventual_ne (htend (finNext i)) (htend i') (dne (finNext i) i' hzi)
  obtain ⟨n4, hn4⟩ := w5cs_eventual_ne (htend (finNext i)) (htend (finNext i'))
    (dne (finNext i) (finNext i') hzz)
  obtain ⟨m1, hm1⟩ := w5cs_tendsto_pos_eventual
    (w5cs_tendsto_cross_dot huto i' (finNext i') (finNext i)) wall1
  obtain ⟨m2, hm2⟩ := w5cs_tendsto_pos_eventual
    (Filter.Tendsto.neg (w5cs_tendsto_cross_dot huto i' (finNext i') i)) (by linarith)
  obtain ⟨m3, hm3⟩ := w5cs_tendsto_pos_eventual
    (w5cs_tendsto_cross_dot huto (finNext i) i (finNext i')) wall3
  obtain ⟨m4, hm4⟩ := w5cs_tendsto_pos_eventual
    (Filter.Tendsto.neg (w5cs_tendsto_cross_dot huto (finNext i) i i')) (by linarith)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, n1 ≤ N ∧ n2 ≤ N ∧ n3 ≤ N ∧ n4 ≤ N ∧
      m1 ≤ N ∧ m2 ≤ N ∧ m3 ≤ N ∧ m4 ≤ N :=
    ⟨n1 + n2 + n3 + n4 + m1 + m2 + m3 + m4, by omega⟩
  have w1 := hm1 N (by omega)
  have w2 := hm2 N (by omega)
  have w3 := hm3 N (by omega)
  have w4 := hm4 N (by omega)
  have d1 := hn1 N (by omega)
  have d2 := hn2 N (by omega)
  have d3 := hn3 N (by omega)
  have d4 := hn4 N (by omega)
  -- fan7 at u N
  have hE1m : {vecmatsV3_p4 (u N) i, vecmatsV3_p4 (u N) (finNext i)}
      ∈ E_SY_p4 (vecmatsV3_p4 (u N)) := ⟨i, Set.mem_univ i, rfl⟩
  have hE2m : {vecmatsV3_p4 (u N) i', vecmatsV3_p4 (u N) (finNext i')}
      ∈ E_SY_p4 (vecmatsV3_p4 (u N)) := ⟨i', Set.mem_univ i', rfl⟩
  have hmemN : u N ∈ BSY1body_cs k a b := (humem N).1
  have hf7N : affGe ({0} : Set V3)
      ({vecmatsV3_p4 (u N) i, vecmatsV3_p4 (u N) (finNext i)} : Set V3)
      ∩ affGe ({0} : Set V3) ({vecmatsV3_p4 (u N) i', vecmatsV3_p4 (u N) (finNext i')} : Set V3)
      = affGe ({0} : Set V3)
        (({vecmatsV3_p4 (u N) i, vecmatsV3_p4 (u N) (finNext i)} : Set V3)
        ∩ {vecmatsV3_p4 (u N) i', vecmatsV3_p4 (u N) (finNext i')}) :=
    (humem N).2.1.1.2.2.2.2.2 _ (Or.inl hE1m) _ (Or.inl hE2m)
  have hdisjN : ({vecmatsV3_p4 (u N) i, vecmatsV3_p4 (u N) (finNext i)} : Set V3)
      ∩ {vecmatsV3_p4 (u N) i', vecmatsV3_p4 (u N) (finNext i')} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rcases Set.mem_insert_iff.mp hx1 with hx1 | hx1 <;>
      rcases Set.mem_insert_iff.mp hx2 with hx2 | hx2
    · exact d1 (hx1.symm.trans hx2)
    · exact d2 (hx1.symm.trans hx2)
    · exact d3 (hx1.symm.trans hx2)
    · exact d4 (hx1.symm.trans hx2)
  have hup : ∀ j : Fin k,
      ‖vecmatsV3_p4 (u N) j - vecmatsV3_p4 (u N) (finNext j)‖ ≤ cstab_p4 := by
    intro j
    have hj := w3cs_row_adj_cstab hsys hs hf hk1 (u N) hmemN
      (p := j.val + 1) (by omega) (by have := j.isLt; omega)
    have hj2 : rowV3_cs (u N) ((j.val + 1) % k + 1) = rowV3_cs (u N) ((finNext j).val + 1) :=
      rfl
    rw [show rowV3_cs (u N) (j.val + 1) = vecmatsV3_p4 (u N) j from bcw2b_row_fin_cs (u N) j,
      hj2, show rowV3_cs (u N) ((finNext j).val + 1) = vecmatsV3_p4 (u N) (finNext j)
        from bcw2b_row_fin_cs (u N) (finNext j)] at hj
    exact hj
  have hnc1N : ¬ Collinear3 (0:V3) (vecmatsV3_p4 (u N) i)
      (vecmatsV3_p4 (u N) (finNext i)) :=
    NONPARALLEL_BALL_ANNULUS (hmemN.1 i) (hmemN.1 (finNext i))
      (w3cs_two_le_next_fin hsys hs hf hk2 (u N) hmemN i) (hup i)
  have hnc2N : ¬ Collinear3 (0:V3) (vecmatsV3_p4 (u N) i')
      (vecmatsV3_p4 (u N) (finNext i')) :=
    NONPARALLEL_BALL_ANNULUS (hmemN.1 i') (hmemN.1 (finNext i'))
      (w3cs_two_le_next_fin hsys hs hf hk2 (u N) hmemN i') (hup i')
  exact w5cs_false_of_sign_wall hf7N hdisjN hnc1N hnc2N w1 w2 w3 w4

end W5Kit

/-! ## Section W5b (bodyclosed-w5b): the aff_gt-intersection side of fan7's
edge×edge layer — WJSCPRO.hl:660-874 (the v3 coefficient tree, strict branch)
+ :874-1290 (dual orientation) + the 9-block aff_ge assembly (W5 gap 3).

- `w5bcs_coord` (Pi side): the coordination identity `α·φ(y1) = δ·ψ(z)` for
  `x = α•y + β•z = γ•y1 + δ•z1` — HOL :660-874's coefficient tree replaced by
  the both-ways dot of `m = (y×z)×(y1×z1)` with `x` (one polarization-free
  scalar identity `d·(m·x) = -φ(y1)·‖x‖²` per side, cross-multiplied).
- `w5bcs_planar_of_mem_affGt_inter`: a point in the double open cone of two
  disjoint fan edges at `L` forces the coplanarity relations `φ(y1) =
  φ(z1) = 0` — the strict orientations close against fan7 at `u N` via
  `w5cs_false_of_limit_wall` and the swapped twin
  `w5bcs_false_of_limit_wall_swap`.
- `w5bcs_affGe_inter_eq_or_planar`: the 9-block aff_ge assembly for two
  disjoint fan edges; the edge-vertex (gt×ray) kill is the W4 (S-G)
  interface face, supplied as the explicit hypotheses `hEV1`/`hEV2` (HOL
  :780-874 discharges them by bootstrapping fan7 for edge×vertex pairs).
The planar residue itself (gap 2, HOL :677-837 interference counting) is
NOT discharged in this wave — its precise statement is in DELIVERY.md. -/

section W5bKit



/-! ## Section W5b (bodyclosed-w5b) — probe build -/

/-- dot-self positive-definiteness on `Fin 3 → ℝ`. -/
theorem w5bcs_dot_self_ne {v : Fin 3 → ℝ} (hv : v ≠ 0) : (v ⬝ᵥ v) ≠ 0 := by
  intro h
  refine hv (funext fun i => ?_)
  have hsum : (v ⬝ᵥ v) = ∑ j : Fin 3, v j * v j := rfl
  rw [h] at hsum
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (v j))).mp
    hsum.symm i (Finset.mem_univ i)
  exact mul_self_eq_zero.mp hz

/-- THE coordination identity (Pi side). -/
theorem w5bcs_coord {y z y1 z1 x : Fin 3 → ℝ} {a b c d : ℝ}
    (hx1 : x = c • y1 + d • z1) (hx2 : x = a • y + b • z) (hx0 : x ≠ 0) :
    a * (crossProduct y z ⬝ᵥ y1) = d * (crossProduct y1 z1 ⬝ᵥ z) := by
  have hQ : x ⬝ᵥ x ≠ 0 := by
    intro h
    refine hx0 (funext fun i => ?_)
    have hsum : (x ⬝ᵥ x) = ∑ j : Fin 3, x j * x j := rfl
    rw [h] at hsum
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).mp
      hsum.symm i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hz
  have p1 : crossProduct y z ⬝ᵥ y = 0 := by
    rw [dotProduct_comm, ← cross_anticomm, dotProduct_neg, dot_cross_self, neg_zero]
  have p2 : crossProduct y z ⬝ᵥ z = 0 := by
    rw [dotProduct_comm]; exact dot_cross_self y z
  have p3 : crossProduct y1 z1 ⬝ᵥ y1 = 0 := by
    rw [dotProduct_comm, ← cross_anticomm, dotProduct_neg, dot_cross_self, neg_zero]
  have p4 : crossProduct y1 z1 ⬝ᵥ z1 = 0 := by
    rw [dotProduct_comm]; exact dot_cross_self y1 z1
  have hrel : c * (crossProduct y z ⬝ᵥ y1) + d * (crossProduct y z ⬝ᵥ z1) = 0 := by
    have h1 : crossProduct y z ⬝ᵥ x = 0 := by
      rw [hx2]; simp [dotProduct_add, dotProduct_smul, p1, p2]
    rw [← h1, hx1, dotProduct_add, dotProduct_smul, dotProduct_smul]
    ring
  have hrel2 : a * (crossProduct y1 z1 ⬝ᵥ y) + b * (crossProduct y1 z1 ⬝ᵥ z) = 0 := by
    have h1 : crossProduct y1 z1 ⬝ᵥ x = 0 := by
      rw [hx1]; simp [dotProduct_add, dotProduct_smul, p3, p4]
    rw [← h1, hx2, dotProduct_add, dotProduct_smul, dotProduct_smul]
    ring
  set φ1 := crossProduct y z ⬝ᵥ y1 with hφ1
  set φ2 := crossProduct y z ⬝ᵥ z1 with hφ2
  set ψ1 := crossProduct y1 z1 ⬝ᵥ y with hψ1
  set ψ2 := crossProduct y1 z1 ⬝ᵥ z with hψ2
  have e1 : crossProduct (crossProduct y z) (crossProduct y1 z1)
      = φ2 • y1 - φ1 • z1 := by
    have h0 := cross_cross_eq_smul_sub_smul' (crossProduct y z) y1 z1
    rw [dotProduct_comm y1 (crossProduct y z)] at h0
    exact h0
  have e2 : crossProduct (crossProduct y z) (crossProduct y1 z1)
      = -ψ2 • y + ψ1 • z := by
    have h0 := cross_cross_eq_smul_sub_smul' (crossProduct y1 z1) y z
    rw [dotProduct_comm y (crossProduct y1 z1)] at h0
    have hac : crossProduct (crossProduct y z) (crossProduct y1 z1)
        = -(crossProduct (crossProduct y1 z1) (crossProduct y z)) :=
      (cross_anticomm _ _).symm
    rw [hac, h0]
    module
  have wy1 : d * (crossProduct (crossProduct y z) (crossProduct y1 z1) ⬝ᵥ x)
      = -(φ1) * (x ⬝ᵥ x) := by
    have hM : crossProduct (crossProduct y z) (crossProduct y1 z1) ⬝ᵥ x
        = c * ((φ2 • y1 - φ1 • z1) ⬝ᵥ y1)
          + d * ((φ2 • y1 - φ1 • z1) ⬝ᵥ z1) := by
      rw [e1, hx1, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [hM]
    have hE : (φ2 • y1 - φ1 • z1) ⬝ᵥ y1
        = φ2 * (y1 ⬝ᵥ y1) - φ1 * (y1 ⬝ᵥ z1) := by
      rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_comm z1 y1]
      ring
    have hF : (φ2 • y1 - φ1 • z1) ⬝ᵥ z1
        = φ2 * (y1 ⬝ᵥ z1) - φ1 * (z1 ⬝ᵥ z1) := by
      rw [sub_dotProduct, smul_dotProduct, smul_dotProduct]
      ring
    have hQex : x ⬝ᵥ x = c * c * (y1 ⬝ᵥ y1) + c * d * (y1 ⬝ᵥ z1)
        + d * c * (z1 ⬝ᵥ y1) + d * d * (z1 ⬝ᵥ z1) := by
      rw [hx1]
      simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      ring
    rw [dotProduct_comm z1 y1] at hQex
    rw [hE, hF, hQex]
    linear_combination (c * (y1 ⬝ᵥ y1) + d * (y1 ⬝ᵥ z1)) * hrel
  have wy2 : a * (crossProduct (crossProduct y z) (crossProduct y1 z1) ⬝ᵥ x)
      = -(ψ2) * (x ⬝ᵥ x) := by
    have hM : crossProduct (crossProduct y z) (crossProduct y1 z1) ⬝ᵥ x
        = a * ((-ψ2 • y + ψ1 • z) ⬝ᵥ y)
          + b * ((-ψ2 • y + ψ1 • z) ⬝ᵥ z) := by
      rw [e2, hx2, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [hM]
    have hE : (-ψ2 • y + ψ1 • z) ⬝ᵥ y
        = -ψ2 * (y ⬝ᵥ y) + ψ1 * (y ⬝ᵥ z) := by
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_comm z y]
      ring
    have hF : (-ψ2 • y + ψ1 • z) ⬝ᵥ z
        = -ψ2 * (y ⬝ᵥ z) + ψ1 * (z ⬝ᵥ z) := by
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct]
      ring
    have hQex : x ⬝ᵥ x = a * a * (y ⬝ᵥ y) + a * b * (y ⬝ᵥ z)
        + b * a * (z ⬝ᵥ y) + b * b * (z ⬝ᵥ z) := by
      rw [hx2]
      simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      ring
    rw [dotProduct_comm z y] at hQex
    rw [hE, hF, hQex]
    linear_combination (a * (y ⬝ᵥ z) + b * (z ⬝ᵥ z)) * hrel2
  have k1 : a * d * (crossProduct (crossProduct y z) (crossProduct y1 z1) ⬝ᵥ x)
      = -(a * φ1) * (x ⬝ᵥ x) := by linear_combination a * wy1
  have k2 : a * d * (crossProduct (crossProduct y z) (crossProduct y1 z1) ⬝ᵥ x)
      = -(d * ψ2) * (x ⬝ᵥ x) := by linear_combination d * wy2
  have heq : (a * φ1) * (x ⬝ᵥ x) = (d * ψ2) * (x ⬝ᵥ x) := by linarith
  exact mul_right_cancel₀ hQ heq

/-- Coefficient extraction: membership in the open cone at the origin. -/
theorem w5bcs_coeff_of_mem_affGt {v w x : V3} (hv : v ≠ 0) (hw : w ≠ 0)
    (hx : x ∈ affGt ({0} : Set V3) ({v, w} : Set V3)) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ x = c • v + d • w := by
  have hdis : Disjoint ({0} : Set V3) ({v, w} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hv h.symm, fun h => hw h.symm⟩
  rw [aff_gt_1_2 hdis, Set.mem_setOf_eq] at hx
  obtain ⟨t1, t2, t3, h2, h3, _, heq⟩ := hx
  refine ⟨t2, t3, h2, h3, ?_⟩
  rw [heq]
  simp

/-- Collinearity from a vanishing positive combination. -/
theorem w5bcs_collinear_of_eq_zero {y z : V3} {α β : ℝ} (hβ : 0 < β)
    (h : (0:V3) = α • y + β • z) : Collinear3 (0:V3) y z := by
  have h1 : α • y = -(β • z) := eq_neg_of_add_eq_zero_left h.symm
  rcases eq_or_ne y 0 with hye | hyne
  · exact collinear3_of_eq (v := (0:V3)) (w := y) (w1 := z) hye
  · refine (collinear3_iff_smul (v := (0:V3)) (w := y) (w1 := z) hyne).2 ⟨-α / β, ?_⟩
    refine smul_right_injective V3 (ne_of_gt hβ) ?_
    show β • (z - 0) = β • ((-α / β) • (y - 0))
    rw [sub_zero, sub_zero, smul_smul, mul_div_cancel₀ _ (ne_of_gt hβ), neg_smul, h1,
      neg_neg]

/-- Pi-side skew helper: swapping the cross factors negates the cross-dot. -/
private theorem w5bcs_cross_skew_dot {p q : V3} (t : Fin 3 → ℝ) :
    (crossProduct (WithLp.ofLp q : Fin 3 → ℝ) (WithLp.ofLp p : Fin 3 → ℝ)) ⬝ᵥ t
      = -((crossProduct (WithLp.ofLp p : Fin 3 → ℝ) (WithLp.ofLp q : Fin 3 → ℝ)) ⬝ᵥ t) := by
  rw [dotProduct_comm, ← cross_anticomm, dotProduct_neg, dotProduct_comm]


/-- Pure-scalar sign split behind the coordination identity: either both
edge-1 cross-dots against the row pair `(y1, z1)` vanish (the planar
configuration), or the four cross-dots line up into one of the two strict
wall orientations. -/
private theorem w5bcs_sign_split {φ1 φ2 ψ1 ψ2 α β γ δ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hcoord : α * φ1 = δ * ψ2) (hrel : γ * φ1 + δ * φ2 = 0)
    (hrel2 : α * ψ1 + β * ψ2 = 0) (hne : φ1 ≠ 0) :
    (φ1 = 0 ∧ φ2 = 0) ∨ (0 < ψ2 ∧ ψ1 < 0 ∧ φ2 < 0 ∧ 0 < φ1)
      ∨ (ψ2 < 0 ∧ 0 < ψ1 ∧ 0 < φ2 ∧ φ1 < 0) := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hαn : α * φ1 < 0 := by nlinarith
    have hψ2n : ψ2 < 0 := by
      have h1 : δ * ψ2 < δ * 0 := by rw [mul_zero]; linarith
      exact lt_of_mul_lt_mul_left h1 hδ.le
    have hψ1p : 0 < ψ1 := by
      have hbn : β * ψ2 < 0 := by nlinarith
      have h1 : α * 0 < α * ψ1 := by rw [mul_zero]; linarith
      exact lt_of_mul_lt_mul_left h1 hα.le
    have hφ2p : 0 < φ2 := by
      have hgp : γ * φ1 < 0 := by nlinarith
      have h1 : δ * 0 < δ * φ2 := by rw [mul_zero]; linarith
      exact lt_of_mul_lt_mul_left h1 hδ.le
    have hφ1n : φ1 < 0 := by
      have h2 : α * φ1 < α * 0 := by rw [mul_zero]; linarith
      exact lt_of_mul_lt_mul_left h2 hα.le
    exact Or.inr (Or.inr ⟨hψ2n, hψ1p, hφ2p, hφ1n⟩)
  · have hαp : 0 < α * φ1 := by nlinarith
    have hψ2p : 0 < ψ2 := by
      have h1 : δ * 0 < δ * ψ2 := by rw [mul_zero]; linarith
      exact lt_of_mul_lt_mul_left h1 hδ.le
    have hψ1n : ψ1 < 0 := by
      have hbp : 0 < β * ψ2 := by nlinarith
      have h1 : α * ψ1 < α * 0 := by rw [mul_zero]; linarith
      exact lt_of_mul_lt_mul_left h1 hα.le
    have hφ2n : φ2 < 0 := by
      have hgp : 0 < γ * φ1 := by nlinarith
      have h1 : δ * φ2 < δ * 0 := by rw [mul_zero]; linarith
      exact lt_of_mul_lt_mul_left h1 hδ.le
    have hφ1p : 0 < φ1 := by
      have h2 : α * 0 < α * φ1 := by rw [mul_zero]; linarith
      exact lt_of_mul_lt_mul_left h2 hα.le
    exact Or.inr (Or.inl ⟨hψ2p, hψ1n, hφ2n, hφ1p⟩)

/-- Swapped-orientation twin of `w5cs_false_of_limit_wall`: the wall hypotheses
stated with the cross-dots of edge 2 sign-flipped
(`0 < -ψ(z), 0 < ψ(y), 0 < -φ(y1), 0 < φ(z1)`), i.e. the engine orientation
after swapping the edge-2 pair. -/
theorem w5bcs_false_of_limit_wall_swap {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k)
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (humem : ∀ n, u n ∈ SYset_cs k a b)
    (huto : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : L ∈ BSY1body_cs k a b)
    {i i' : Fin k} (hii : i ≠ i') (hiz : i ≠ finNext i')
    (hzi : finNext i ≠ i') (hzz : finNext i ≠ finNext i')
    (w1 : 0 < -((crossProduct (WithLp.ofLp (vecmatsV3_p4 L i') : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L (finNext i')) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ)))
    (w2 : 0 < (crossProduct (WithLp.ofLp (vecmatsV3_p4 L i') : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L (finNext i')) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ))
    (w3 : 0 < -((crossProduct (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L i') : Fin 3 → ℝ)))
    (w4 : 0 < (crossProduct (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L (finNext i')) : Fin 3 → ℝ)) : False := by
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  have hk2 : 2 < k := by omega
  have hsep : ∀ p q : ℕ, 1 ≤ p → p ≤ k → 1 ≤ q → q ≤ k → p ≠ q →
      (2:ℝ) ≤ ‖rowV3_cs L p - rowV3_cs L q‖ :=
    fun p q hp hpk hq hqk hpq => w3cs_two_le_row_of_BSY1body hsys hs hf hk1 L hL hp hpk hq hqk hpq
  have htwo : ∀ p q : Fin k, p ≠ q → (2:ℝ) ≤ ‖vecmatsV3_p4 L p - vecmatsV3_p4 L q‖ := by
    intro p q hpq
    rw [← bcw2b_row_fin_cs, ← bcw2b_row_fin_cs]
    exact hsep (p.val + 1) (q.val + 1) (by omega) (by have := p.isLt; omega)
      (by omega) (by have := q.isLt; omega) (fun h => hpq (Fin.ext (by omega)))
  have htend : ∀ j : Fin k, Filter.Tendsto (fun n => vecmatsV3_p4 (u n) j) Filter.atTop
      (nhds (vecmatsV3_p4 L j)) := fun j =>
    ((w3cs_continuous_vecmatsV3 j).tendsto L).comp huto
  have dne : ∀ p q : Fin k, p ≠ q → vecmatsV3_p4 L p ≠ vecmatsV3_p4 L q := by
    intro p q hpq he
    have h2 := htwo p q hpq
    rw [he, sub_self, norm_zero] at h2
    linarith
  obtain ⟨n1, hn1⟩ := w5cs_eventual_ne (htend i) (htend i') (dne i i' hii)
  obtain ⟨n2, hn2⟩ := w5cs_eventual_ne (htend i) (htend (finNext i')) (dne i (finNext i') hiz)
  obtain ⟨n3, hn3⟩ := w5cs_eventual_ne (htend (finNext i)) (htend i') (dne (finNext i) i' hzi)
  obtain ⟨n4, hn4⟩ := w5cs_eventual_ne (htend (finNext i)) (htend (finNext i'))
    (dne (finNext i) (finNext i') hzz)
  obtain ⟨m1, hm1⟩ := w5cs_tendsto_pos_eventual
    (Filter.Tendsto.neg (w5cs_tendsto_cross_dot huto i' (finNext i') (finNext i))) w1
  obtain ⟨m2, hm2⟩ := w5cs_tendsto_pos_eventual
    (w5cs_tendsto_cross_dot huto i' (finNext i') i) w2
  obtain ⟨m3, hm3⟩ := w5cs_tendsto_pos_eventual
    (Filter.Tendsto.neg (w5cs_tendsto_cross_dot huto i (finNext i) i')) w3
  obtain ⟨m4, hm4⟩ := w5cs_tendsto_pos_eventual
    (w5cs_tendsto_cross_dot huto i (finNext i) (finNext i')) w4
  obtain ⟨N, hN⟩ : ∃ N : ℕ, n1 ≤ N ∧ n2 ≤ N ∧ n3 ≤ N ∧ n4 ≤ N ∧
      m1 ≤ N ∧ m2 ≤ N ∧ m3 ≤ N ∧ m4 ≤ N :=
    ⟨n1 + n2 + n3 + n4 + m1 + m2 + m3 + m4, by omega⟩
  have w1N := hm1 N (by omega)
  have w2N := hm2 N (by omega)
  have w3N := hm3 N (by omega)
  have w4N := hm4 N (by omega)
  have d1 := hn1 N (by omega)
  have d2 := hn2 N (by omega)
  have d3 := hn3 N (by omega)
  have d4 := hn4 N (by omega)
  have hE1m : {vecmatsV3_p4 (u N) i, vecmatsV3_p4 (u N) (finNext i)}
      ∈ E_SY_p4 (vecmatsV3_p4 (u N)) := ⟨i, Set.mem_univ i, rfl⟩
  have hE2m : {vecmatsV3_p4 (u N) i', vecmatsV3_p4 (u N) (finNext i')}
      ∈ E_SY_p4 (vecmatsV3_p4 (u N)) := ⟨i', Set.mem_univ i', rfl⟩
  have hmemN : u N ∈ BSY1body_cs k a b := (humem N).1
  have hf7N : affGe ({0} : Set V3)
      ({vecmatsV3_p4 (u N) i, vecmatsV3_p4 (u N) (finNext i)} : Set V3)
      ∩ affGe ({0} : Set V3) ({vecmatsV3_p4 (u N) i', vecmatsV3_p4 (u N) (finNext i')} : Set V3)
      = affGe ({0} : Set V3)
        (({vecmatsV3_p4 (u N) i, vecmatsV3_p4 (u N) (finNext i)} : Set V3)
        ∩ {vecmatsV3_p4 (u N) i', vecmatsV3_p4 (u N) (finNext i')}) :=
    (humem N).2.1.1.2.2.2.2.2 _ (Or.inl hE1m) _ (Or.inl hE2m)
  have hdisjN : ({vecmatsV3_p4 (u N) i, vecmatsV3_p4 (u N) (finNext i)} : Set V3)
      ∩ {vecmatsV3_p4 (u N) i', vecmatsV3_p4 (u N) (finNext i')} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rcases Set.mem_insert_iff.mp hx1 with hx1 | hx1 <;>
      rcases Set.mem_insert_iff.mp hx2 with hx2 | hx2
    · exact d1 (hx1.symm.trans hx2)
    · exact d2 (hx1.symm.trans hx2)
    · exact d3 (hx1.symm.trans hx2)
    · exact d4 (hx1.symm.trans hx2)
  have hup : ∀ j : Fin k,
      ‖vecmatsV3_p4 (u N) j - vecmatsV3_p4 (u N) (finNext j)‖ ≤ cstab_p4 := by
    intro j
    have hj := w3cs_row_adj_cstab hsys hs hf hk1 (u N) hmemN
      (p := j.val + 1) (by omega) (by have := j.isLt; omega)
    have hj2 : rowV3_cs (u N) ((j.val + 1) % k + 1) = rowV3_cs (u N) ((finNext j).val + 1) :=
      rfl
    rw [show rowV3_cs (u N) (j.val + 1) = vecmatsV3_p4 (u N) j from bcw2b_row_fin_cs (u N) j,
      hj2, show rowV3_cs (u N) ((finNext j).val + 1) = vecmatsV3_p4 (u N) (finNext j)
        from bcw2b_row_fin_cs (u N) (finNext j)] at hj
    exact hj
  have hnc1N : ¬ Collinear3 (0:V3) (vecmatsV3_p4 (u N) i)
      (vecmatsV3_p4 (u N) (finNext i)) :=
    NONPARALLEL_BALL_ANNULUS (hmemN.1 i) (hmemN.1 (finNext i))
      (w3cs_two_le_next_fin hsys hs hf hk2 (u N) hmemN i) (hup i)
  have hnc2N : ¬ Collinear3 (0:V3) (vecmatsV3_p4 (u N) i')
      (vecmatsV3_p4 (u N) (finNext i')) :=
    NONPARALLEL_BALL_ANNULUS (hmemN.1 i') (hmemN.1 (finNext i'))
      (w3cs_two_le_next_fin hsys hs hf hk2 (u N) hmemN i') (hup i')
  rw [Set.pair_comm (vecmatsV3_p4 (u N) i') (vecmatsV3_p4 (u N) (finNext i'))] at hf7N hdisjN
  have hnc2N' : ¬ Collinear3 (0:V3) (vecmatsV3_p4 (u N) (finNext i'))
      (vecmatsV3_p4 (u N) i') := fun hc =>
    hnc2N (hc.subset (by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      tauto))
  have e1 : 0 < (crossProduct (WithLp.ofLp (vecmatsV3_p4 (u N) (finNext i')) : Fin 3 → ℝ)
      (WithLp.ofLp (vecmatsV3_p4 (u N) i') : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 (u N) (finNext i)) : Fin 3 → ℝ) := by
    rw [w5bcs_cross_skew_dot]; exact w1N
  have e2 : 0 < -((crossProduct (WithLp.ofLp (vecmatsV3_p4 (u N) (finNext i')) : Fin 3 → ℝ)
      (WithLp.ofLp (vecmatsV3_p4 (u N) i') : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 (u N) i) : Fin 3 → ℝ)) := by
    rw [w5bcs_cross_skew_dot, neg_neg]; exact w2N
  have e3 : 0 < (crossProduct (WithLp.ofLp (vecmatsV3_p4 (u N) (finNext i)) : Fin 3 → ℝ)
      (WithLp.ofLp (vecmatsV3_p4 (u N) i) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 (u N) i') : Fin 3 → ℝ) := by
    rw [w5bcs_cross_skew_dot]; exact w3N
  have e4 : 0 < -((crossProduct (WithLp.ofLp (vecmatsV3_p4 (u N) (finNext i)) : Fin 3 → ℝ)
      (WithLp.ofLp (vecmatsV3_p4 (u N) i) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 (u N) (finNext i')) : Fin 3 → ℝ)) := by
    rw [w5bcs_cross_skew_dot, neg_neg]; exact w4N
  exact w5cs_false_of_sign_wall hf7N hdisjN hnc1N hnc2N' e1 e2 e3 e4

/-- GAP 1 capstone: a point in the double open cone of two disjoint fan edges
at the limit point forces the coplanarity relations `φ(y1) = φ(z1) = 0`
(`φ` = cross-dot against edge 1's normal).  If a relation failed, the
coordination identity `α·φ(y1) = δ·ψ(z)` would force the strict sign wall at
`L`, which `w5cs_false_of_limit_wall` (or its swapped twin) transfers to a
large index and closes against fan7 — contradiction. -/
theorem w5bcs_planar_of_mem_affGt_inter {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k)
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (humem : ∀ n, u n ∈ SYset_cs k a b)
    (huto : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : L ∈ BSY1body_cs k a b)
    {i i' : Fin k} (hii : i ≠ i') (hiz : i ≠ finNext i')
    (hzi : finNext i ≠ i') (hzz : finNext i ≠ finNext i')
    (x : V3)
    (hx1 : x ∈ affGt ({0} : Set V3)
      ({vecmatsV3_p4 L i, vecmatsV3_p4 L (finNext i)} : Set V3))
    (hx2 : x ∈ affGt ({0} : Set V3)
      ({vecmatsV3_p4 L i', vecmatsV3_p4 L (finNext i')} : Set V3)) :
    (crossProduct (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L i') : Fin 3 → ℝ) = 0
    ∧ (crossProduct (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L (finNext i')) : Fin 3 → ℝ) = 0 := by
  set y := vecmatsV3_p4 L i
  set z := vecmatsV3_p4 L (finNext i)
  set y1 := vecmatsV3_p4 L i'
  set z1 := vecmatsV3_p4 L (finNext i')
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  have hadj : ∀ j : Fin k, ‖vecmatsV3_p4 L j - vecmatsV3_p4 L (finNext j)‖ ≤ cstab_p4 := by
    intro j
    have hj := w3cs_row_adj_cstab hsys hs hf hk1 L hL
      (p := j.val + 1) (by omega) (by have := j.isLt; omega)
    have hj2 : rowV3_cs L ((j.val + 1) % k + 1) = rowV3_cs L ((finNext j).val + 1) := rfl
    rw [show rowV3_cs L (j.val + 1) = vecmatsV3_p4 L j from bcw2b_row_fin_cs L j,
      hj2, show rowV3_cs L ((finNext j).val + 1) = vecmatsV3_p4 L (finNext j)
        from bcw2b_row_fin_cs L (finNext j)] at hj
    exact hj
  have hnc1L : ¬ Collinear3 (0:V3) y z :=
    NONPARALLEL_BALL_ANNULUS (hL.1 i) (hL.1 (finNext i))
      (w3cs_two_le_next_fin hsys hs hf (by omega) L hL i) (hadj i)
  have hnc2L : ¬ Collinear3 (0:V3) y1 z1 :=
    NONPARALLEL_BALL_ANNULUS (hL.1 i') (hL.1 (finNext i'))
      (w3cs_two_le_next_fin hsys hs hf (by omega) L hL i') (hadj i')
  have hy0 : y ≠ 0 := fun he => hnc1L (collinear3_of_eq he)
  have hz0 : z ≠ 0 := fun he => hnc1L (collinear3_pair_left he)
  have hy10 : y1 ≠ 0 := fun he => hnc2L (collinear3_of_eq he)
  have hz10 : z1 ≠ 0 := fun he => hnc2L (collinear3_pair_left he)
  obtain ⟨α, β, hα, hβ, hx1c⟩ := w5bcs_coeff_of_mem_affGt hy0 hz0 hx1
  obtain ⟨γ, δ, hγ, hδ, hx2c⟩ := w5bcs_coeff_of_mem_affGt hy10 hz10 hx2
  have hx0 : x ≠ 0 := by
    intro he
    refine hnc1L (w5bcs_collinear_of_eq_zero (α := α) hβ ?_)
    rw [← he]
    exact hx1c
  have hoflp : (WithLp.ofLp x : Fin 3 → ℝ) ≠ 0 := by
    intro he
    refine hx0 ?_
    have h2 := congrArg (fun w : Fin 3 → ℝ => (WithLp.toLp 2 w : V3)) he
    simpa using h2
  have cx1 : (WithLp.ofLp x : Fin 3 → ℝ)
      = γ • (WithLp.ofLp y1 : Fin 3 → ℝ) + δ • (WithLp.ofLp z1 : Fin 3 → ℝ) := by
    rw [hx2c]; simp [WithLp.ofLp_add, WithLp.ofLp_smul]
  have cx2 : (WithLp.ofLp x : Fin 3 → ℝ)
      = α • (WithLp.ofLp y : Fin 3 → ℝ) + β • (WithLp.ofLp z : Fin 3 → ℝ) := by
    rw [hx1c]; simp [WithLp.ofLp_add, WithLp.ofLp_smul]
  set φ1 := (crossProduct (WithLp.ofLp y : Fin 3 → ℝ) (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ
    (WithLp.ofLp y1 : Fin 3 → ℝ) with hq1
  set φ2 := (crossProduct (WithLp.ofLp y : Fin 3 → ℝ) (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ
    (WithLp.ofLp z1 : Fin 3 → ℝ) with hq2
  set ψ1 := (crossProduct (WithLp.ofLp y1 : Fin 3 → ℝ) (WithLp.ofLp z1 : Fin 3 → ℝ)) ⬝ᵥ
    (WithLp.ofLp y : Fin 3 → ℝ) with hq3
  set ψ2 := (crossProduct (WithLp.ofLp y1 : Fin 3 → ℝ) (WithLp.ofLp z1 : Fin 3 → ℝ)) ⬝ᵥ
    (WithLp.ofLp z : Fin 3 → ℝ) with hq4
  have hcoord : α * φ1 = δ * ψ2 := w5bcs_coord cx1 cx2 hoflp
  have p1 : (crossProduct (WithLp.ofLp y : Fin 3 → ℝ) (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp y : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm, ← cross_anticomm, dotProduct_neg, dot_cross_self, neg_zero]
  have p2 : (crossProduct (WithLp.ofLp y : Fin 3 → ℝ) (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp z : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]; exact dot_cross_self _ _
  have p3 : (crossProduct (WithLp.ofLp y1 : Fin 3 → ℝ) (WithLp.ofLp z1 : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp y1 : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm, ← cross_anticomm, dotProduct_neg, dot_cross_self, neg_zero]
  have p4 : (crossProduct (WithLp.ofLp y1 : Fin 3 → ℝ) (WithLp.ofLp z1 : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp z1 : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]; exact dot_cross_self _ _
  have hrel : γ * φ1 + δ * φ2 = 0 := by
    have h1 : (crossProduct (WithLp.ofLp y : Fin 3 → ℝ)
        (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp x : Fin 3 → ℝ) = 0 := by
      rw [cx2]; simp [dotProduct_add, dotProduct_smul, p1, p2]
    rw [← h1, cx1, dotProduct_add, dotProduct_smul, dotProduct_smul]
    ring
  have hrel2 : α * ψ1 + β * ψ2 = 0 := by
    have h1 : (crossProduct (WithLp.ofLp y1 : Fin 3 → ℝ)
        (WithLp.ofLp z1 : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp x : Fin 3 → ℝ) = 0 := by
      rw [cx1]; simp [dotProduct_add, dotProduct_smul, p3, p4]
    rw [← h1, cx2, dotProduct_add, dotProduct_smul, dotProduct_smul]
    ring
  rcases eq_or_ne φ1 0 with h0 | hne
  · refine ⟨h0, ?_⟩
    have hrel' := hrel
    rw [h0, mul_zero, zero_add] at hrel'
    exact (mul_eq_zero.mp hrel').resolve_left (ne_of_gt hδ)
  · exfalso
    rcases w5bcs_sign_split hα hβ hγ hδ hcoord hrel hrel2 hne with
      ⟨h10, h20⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1', h2', h3', h4'⟩
    · exact absurd h10 hne
    · have e3 : 0 < (crossProduct (WithLp.ofLp z : Fin 3 → ℝ)
          (WithLp.ofLp y : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp z1 : Fin 3 → ℝ) := by
        rw [w5bcs_cross_skew_dot (p := y) (q := z), ← hq2, neg_pos]
        exact h3
      have e4 : 0 < -((crossProduct (WithLp.ofLp z : Fin 3 → ℝ)
          (WithLp.ofLp y : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp y1 : Fin 3 → ℝ)) := by
        rw [w5bcs_cross_skew_dot (p := y) (q := z), ← hq1, neg_neg]
        exact h4
      exact w5cs_false_of_limit_wall hsys hs hf humem huto hL hii hiz hzi hzz h1
        (by show 0 < -ψ1; rw [neg_pos]; exact h2) e3 e4
    · exact w5bcs_false_of_limit_wall_swap hsys hs hf humem huto hL hii hiz hzi hzz
        (by show 0 < -ψ2; rw [neg_pos]; exact h1') h2'
        (by show 0 < -φ1; rw [neg_pos]; exact h4') h3'

/-- GAP 3 assembly (edge × edge, disjoint case): under the unified
limit-point premises, the `aff_ge` intersection of two disjoint fan edges is
`{0}` — unless the planar residue `φ(y1) = φ(z1) = 0` holds (gap 2, whose
quantified angle-chord interference count is not discharged in this wave).

`hEV1` / `hEV2` are the edge-vertex (gt×ray) kill, the W4 (S-G) interface
face, supplied here as explicit hypotheses: HOL :780-874 discharges them by
bootstrapping fan7 for edge×vertex pairs; once W4 lands, its `w4cs_*`
pieces (or the fan7 instance itself) substitute directly. -/
theorem w5bcs_affGe_inter_eq_or_planar {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k)
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (humem : ∀ n, u n ∈ SYset_cs k a b)
    (huto : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : L ∈ BSY1body_cs k a b)
    {i i' : Fin k} (hii : i ≠ i') (hiz : i ≠ finNext i')
    (hzi : finNext i ≠ i') (hzz : finNext i ≠ finNext i')
    (hEV1 : ∀ w : V3, w ∈ ({vecmatsV3_p4 L i, vecmatsV3_p4 L (finNext i)} : Set V3) →
      ∀ x : V3, x ∈ affGt ({0} : Set V3)
        ({vecmatsV3_p4 L i', vecmatsV3_p4 L (finNext i')} : Set V3) →
        x ∈ affGe ({0} : Set V3) ({w} : Set V3) → x = 0)
    (hEV2 : ∀ w : V3, w ∈ ({vecmatsV3_p4 L i', vecmatsV3_p4 L (finNext i')} : Set V3) →
      ∀ x : V3, x ∈ affGt ({0} : Set V3)
        ({vecmatsV3_p4 L i, vecmatsV3_p4 L (finNext i)} : Set V3) →
        x ∈ affGe ({0} : Set V3) ({w} : Set V3) → x = 0) :
    affGe ({0} : Set V3)
        ({vecmatsV3_p4 L i, vecmatsV3_p4 L (finNext i)} : Set V3)
      ∩ affGe ({0} : Set V3)
        ({vecmatsV3_p4 L i', vecmatsV3_p4 L (finNext i')} : Set V3)
      = ({0} : Set V3)
    ∨ ((crossProduct (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L i') : Fin 3 → ℝ) = 0
      ∧ (crossProduct (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L (finNext i')) : Fin 3 → ℝ) = 0) := by
  set y := vecmatsV3_p4 L i
  set z := vecmatsV3_p4 L (finNext i)
  set y1 := vecmatsV3_p4 L i'
  set z1 := vecmatsV3_p4 L (finNext i')
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  -- noncollinearity of both edges at L
  have hadj : ∀ j : Fin k, ‖vecmatsV3_p4 L j - vecmatsV3_p4 L (finNext j)‖ ≤ cstab_p4 := by
    intro j
    have hj := w3cs_row_adj_cstab hsys hs hf hk1 L hL
      (p := j.val + 1) (by omega) (by have := j.isLt; omega)
    have hj2 : rowV3_cs L ((j.val + 1) % k + 1) = rowV3_cs L ((finNext j).val + 1) := rfl
    rw [show rowV3_cs L (j.val + 1) = vecmatsV3_p4 L j from bcw2b_row_fin_cs L j,
      hj2, show rowV3_cs L ((finNext j).val + 1) = vecmatsV3_p4 L (finNext j)
        from bcw2b_row_fin_cs L (finNext j)] at hj
    exact hj
  have hnc1L : ¬ Collinear3 (0:V3) y z :=
    NONPARALLEL_BALL_ANNULUS (hL.1 i) (hL.1 (finNext i))
      (w3cs_two_le_next_fin hsys hs hf (by omega) L hL i) (hadj i)
  have hnc2L : ¬ Collinear3 (0:V3) y1 z1 :=
    NONPARALLEL_BALL_ANNULUS (hL.1 i') (hL.1 (finNext i'))
      (w3cs_two_le_next_fin hsys hs hf (by omega) L hL i') (hadj i')
  have hy0 : y ≠ 0 := fun he => hnc1L (collinear3_of_eq he)
  have hz0 : z ≠ 0 := fun he => hnc1L (collinear3_pair_left he)
  have hy10 : y1 ≠ 0 := fun he => hnc2L (collinear3_of_eq he)
  have hz10 : z1 ≠ 0 := fun he => hnc2L (collinear3_pair_left he)
  have hyz : y ≠ z := fun he => hnc1L (collinear3_pair_right he.symm)
  have hy1z1 : y1 ≠ z1 := fun he => hnc2L (collinear3_pair_right he.symm)
  -- pairwise 2-separation at L
  have hsep : ∀ p q : ℕ, 1 ≤ p → p ≤ k → 1 ≤ q → q ≤ k → p ≠ q →
      (2:ℝ) ≤ ‖rowV3_cs L p - rowV3_cs L q‖ :=
    fun p q hp hpk hq hqk hpq => w3cs_two_le_row_of_BSY1body hsys hs hf hk1 L hL hp hpk hq hqk hpq
  have htwo : ∀ p q : Fin k, p ≠ q → (2:ℝ) ≤ ‖vecmatsV3_p4 L p - vecmatsV3_p4 L q‖ := by
    intro p q hpq
    rw [← bcw2b_row_fin_cs, ← bcw2b_row_fin_cs]
    exact hsep (p.val + 1) (q.val + 1) (by omega) (by have := p.isLt; omega)
      (by omega) (by have := q.isLt; omega) (fun h => hpq (Fin.ext (by omega)))
  -- pairwise separations needed by the ray×ray blocks
  have h2yy1 : (2:ℝ) ≤ ‖y - y1‖ := htwo i i' hii
  have h2yz1 : (2:ℝ) ≤ ‖y - z1‖ := htwo i (finNext i') hiz
  have h2zy1 : (2:ℝ) ≤ ‖z - y1‖ := htwo (finNext i) i' hzi
  have h2zz1 : (2:ℝ) ≤ ‖z - z1‖ := htwo (finNext i) (finNext i') hzz
  -- 0 lies in both closed fans
  have hmem0 : (0:V3) ∈ affGe ({0} : Set V3) ({y, z} : Set V3) ∧
      (0:V3) ∈ affGe ({0} : Set V3) ({y1, z1} : Set V3) := by
    have hgen : ∀ (v w : V3), v ≠ 0 → w ≠ 0 → v ≠ w →
        (0:V3) ∈ affGe ({0} : Set V3) ({v, w} : Set V3) := by
      intro v w hv0 hw0 hvw
      exact Affsign.of_triple (sgn := fun r => 0 ≤ r) 0 0 (le_refl 0) (le_refl 0)
        (by simp) (Ne.symm hv0) (Ne.symm hw0) hvw
    exact ⟨hgen y z hy0 hz0 hyz, hgen y1 z1 hy10 hz10 hy1z1⟩
  -- the block analysis
  have key : ∀ x : V3, x ∈ affGe ({0} : Set V3) ({y, z} : Set V3) ∩
      affGe ({0} : Set V3) ({y1, z1} : Set V3) →
      x = 0 ∨ ((crossProduct (WithLp.ofLp y : Fin 3 → ℝ)
        (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp y1 : Fin 3 → ℝ) = 0
        ∧ (crossProduct (WithLp.ofLp y : Fin 3 → ℝ)
        (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp z1 : Fin 3 → ℝ) = 0) := by
    intro x hx
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [aff_ge_eq_aff_gt_union_aff_ge hnc1L, Set.mem_union, Set.mem_union] at hx1
    rw [aff_ge_eq_aff_gt_union_aff_ge hnc2L, Set.mem_union, Set.mem_union] at hx2
    refine Or.elim hx1 (fun ha1b1 => ?_) (fun hc1 => ?_)
    · refine Or.elim ha1b1 (fun ha1 => ?_) (fun hb1 => ?_)
      · refine Or.elim hx2 (fun ha2b2 => ?_) (fun hc2 => ?_)
        · refine Or.elim ha2b2 (fun ha2 => ?_) (fun hb2 => ?_)
          · exact Or.inr (w5bcs_planar_of_mem_affGt_inter hsys hs hf humem huto hL hii hiz hzi hzz x
              ha1 ha2)
          · rcases eq_or_ne x 0 with h0 | hne
            · exact Or.inl h0
            · exact absurd (hEV2 y1 (Set.mem_insert _ _) x ha1 hb2) hne
        · rcases eq_or_ne x 0 with h0 | hne
          · exact Or.inl h0
          · exact absurd (hEV2 z1 (by simp : z1 ∈ ({y1, z1} : Set V3)) x ha1 hc2) hne
      · refine Or.elim hx2 (fun ha2b2 => ?_) (fun hc2 => ?_)
        · refine Or.elim ha2b2 (fun ha2 => ?_) (fun hb2 => ?_)
          · rcases eq_or_ne x 0 with h0 | hne
            · exact Or.inl h0
            · exact absurd (hEV1 y (Set.mem_insert _ _) x ha2 hb1) hne
          · exact Or.inl (VEC0_BALL_ANNULUS h2yy1 (hL.1 i) (hL.1 i') hb1 hb2)
        · rcases eq_or_ne x 0 with h0 | hne
          · exact Or.inl h0
          · exact absurd (VEC0_BALL_ANNULUS h2yz1 (hL.1 i)
            (hL.1 (finNext i')) hb1 hc2) hne
    · refine Or.elim hx2 (fun ha2b2 => ?_) (fun hc2 => ?_)
      · refine Or.elim ha2b2 (fun ha2 => ?_) (fun hb2 => ?_)
        · rcases eq_or_ne x 0 with h0 | hne
          · exact Or.inl h0
          · exact absurd (hEV1 z (by simp : z ∈ ({y, z} : Set V3)) x ha2 hc1) hne
        · rcases eq_or_ne x 0 with h0 | hne
          · exact Or.inl h0
          · exact absurd (VEC0_BALL_ANNULUS h2zy1 (hL.1 (finNext i)) (hL.1 i')
            hc1 hb2) hne
      · exact Or.inl (VEC0_BALL_ANNULUS h2zz1 (hL.1 (finNext i))
          (hL.1 (finNext i')) hc1 hc2)
  -- conclusion
  rcases Classical.em (∀ x : V3, x ∈ affGe ({0} : Set V3) ({y, z} : Set V3) ∩
      affGe ({0} : Set V3) ({y1, z1} : Set V3) → x = 0) with hall | hex
  · refine Or.inl ?_
    ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · exact Set.mem_singleton_iff.mpr (hall w hw)
    · have hw0 : w = 0 := Set.mem_singleton_iff.mp hw
      rw [hw0]
      exact ⟨hmem0.1, hmem0.2⟩
  · have hexists : ∃ x : V3, x ∈ affGe ({0} : Set V3) ({y, z} : Set V3) ∩
        affGe ({0} : Set V3) ({y1, z1} : Set V3) ∧ x ≠ 0 := by
      by_contra hcon
      refine hex ?_
      intro x hx
      by_contra hx0
      exact hcon ⟨x, hx, hx0⟩
    obtain ⟨x, hx, hx0⟩ := hexists
    rcases key x hx with h0 | hp
    · exact absurd h0 hx0
    · exact Or.inr hp

end W5bKit

/-! ## bodyclosed-w4: the S-G fan7 kit (WJSCPRO.hl:452-1290)

`Fan.fan7 0 V E` quantifies over `e1 e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}`.  Layers:

- vertex-vertex (WJSCPRO.hl:452-494): `VEC0_BALL_ANNULUS` on `hsand`/`hann`;
- edge-vertex (WJSCPRO.hl:495-634): the LA4 crutches `BALL_ANNULUS_4PONITS_AFF_GT`
  and friends are sorry giants — re-proved here from Planarity's explicit forms
  (`aff_gt_1_2`) and the sharp ray-distance estimate `w4cs_norm_min_ray`;
- edge-edge: the disjoint case is the W5 obligation (`aff_gt` emptiness via the
  sequential cross-dot wall, WJSCPRO.hl:636-1497 = S-H); the shared-endpoint
  case is pure limit-point geometry and is assembled here
  (`w4cs_fan7_edges_shared`).

FINDING (bodyclosed-w4): the statement pinned by W3 DELIVERY §2.3 —
`fan7_E_SY_W4` from `hsand` + `hann` alone — is FALSE (butterfly configuration:
rows `(2,0,0), (−2,0,0), (1,2,0), (1,−2,0)` satisfy every hypothesis of the
pinned statement, yet the cones of the disjoint edges `{±x̂}` and
`{(1,±2,0)}` share the ray `(1,0,0)`; fully formalized in the lane probe
`ProbeCE.pinned_false`).  The corrected assembler `w4cs_fan7_of_clauses` takes
the per-edge upper bound `hup` (= `w3cs_row_adj_cstab`'s supply, giving edge
non-degeneracy via `NONPARALLEL_BALL_ANNULUS`) and the W5 disjointness
obligation `hdisj`. -/

section W4Kit

/-! ### Cone bookkeeping -/

/-- `0` is disjoint from a two-point set of nonzero points. -/
theorem w4cs_disjoint_ne {y z : V3} (hy : y ≠ 0) (hz : z ≠ 0) :
    Disjoint ({(0:V3)} : Set V3) {y, z} := by
  rw [Set.disjoint_singleton_left]
  intro hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hy rfl
  · exact hz rfl

/-- The fundamental two-point face membership (positive combination). -/
theorem w4cs_mem_affGe_two {a b y : V3} (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    {t s : ℝ} (hy : y = t • a + s • b) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    y ∈ affGe {(0:V3)} {a, b} := by
  have hdis : Disjoint ({(0:V3)} : Set V3) {a, b} := w4cs_disjoint_ne ha0 hb0
  rw [aff_ge_1_2 hdis, Set.mem_setOf_eq]
  refine ⟨1 - t - s, t, s, ht, hs, by ring, ?_⟩
  rw [hy]
  module

/-- The open two-point face membership (strictly positive combination). -/
theorem w4cs_mem_affGt_two {a b y : V3} (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    {t s : ℝ} (hy : y = t • a + s • b) (ht : 0 < t) (hs : 0 < s) :
    y ∈ affGt {(0:V3)} {a, b} := by
  have hdis : Disjoint ({(0:V3)} : Set V3) {a, b} := w4cs_disjoint_ne ha0 hb0
  rw [aff_gt_1_2 hdis, Set.mem_setOf_eq]
  refine ⟨1 - t - s, t, s, ht, hs, by ring, ?_⟩
  rw [hy]
  module

/-- Annulus points are nonzero. -/
theorem w4cs_annulus_ne_zero {v : V3} (hv : v ∈ ballAnnulus) : v ≠ 0 := by
  obtain ⟨h1, -⟩ := ballAnnulus_norm_bounds hv
  intro h0v
  rw [h0v] at h1
  norm_num at h1

/-- Coefficient extraction for a one-point `aff_ge` face (ray form). -/
theorem w4cs_affGe_single_coeff {x u y : V3} (hxu : x ≠ u) (hmem : y ∈ affGe {x} {u}) :
    ∃ t1 t2 : ℝ, 0 ≤ t2 ∧ t1 + t2 = 1 ∧ y = t1 • x + t2 • u := by
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hmem
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := hmem
  rw [sum_insert_single_v hfin hxu] at hsum
  rw [sum_insert_single_s hfin hxu] at hone
  exact ⟨f x, f u, hpos u (by simp), hone, hsum⟩

/-- A point of the ray through a nonzero `v` is a nonnegative multiple. -/
theorem w4cs_ray_coeff {v w : V3} (hv : v ≠ 0) (hw : w ∈ affGe {(0:V3)} {v}) :
    ∃ t : ℝ, 0 ≤ t ∧ w = t • v := by
  obtain ⟨t1, t2, ht2, hsum, hpq⟩ := w4cs_affGe_single_coeff (by exact fun h => hv h.symm) hw
  refine ⟨t2, ht2, ?_⟩
  rw [hpq, smul_zero, zero_add]

/-- `0` lies on every ray. -/
theorem w4cs_zero_mem_ray {v : V3} (hv : v ≠ 0) : (0:V3) ∈ affGe {(0:V3)} {v} := by
  have hfin : (({(0:V3)} ∪ {v} : Set V3)).Finite :=
    (Set.finite_singleton (0:V3)).union (Set.finite_singleton v)
  have hvz : ¬((0:V3) = v) := fun h => hv h.symm
  simp only [affGe, Set.mem_setOf_eq, Affsign]
  refine ⟨fun w => if w = (0:V3) then 1 else 0, hfin, ?_, ?_, ?_⟩
  · rw [sum_insert_single_v hfin (by exact fun h => hvz h), if_pos rfl, one_smul,
      if_neg (fun h => hv h), zero_smul, add_zero]
  · intro w hw
    show 0 ≤ (if w = (0:V3) then 1 else 0)
    rcases eq_or_ne w (0:V3) with h0 | h0
    · rw [h0, if_pos rfl]; norm_num
    · rw [if_neg h0]
  · rw [sum_insert_single_s hfin (by exact fun h => hvz h), if_pos rfl,
      if_neg (fun h => hv h)]
    ring

/-- `0` lies in every non-degenerate two-generator cone. -/
theorem w4cs_zero_mem_cone {y z : V3} (hnc : ¬ Collinear3 (0:V3) y z)
    (hy : y ≠ 0) (hz : z ≠ 0) : (0:V3) ∈ affGe {(0:V3)} {y, z} := by
  have hfin : (({(0:V3)} ∪ {y, z} : Set V3)).Finite :=
    (Set.finite_singleton (0:V3)).union ((Set.finite_singleton z).insert y)
  have hyz : ¬(y = z) := fun h => hnc (by
    show Collinear ℝ ({(0:V3), y, z} : Set V3)
    rw [h, show ({(0:V3), z, z} : Set V3) = {(0:V3), z} from by ext x; simp]
    exact collinear_pair ℝ (0:V3) z)
  have h0y : ¬((0:V3) = y) := fun h => hy h.symm
  have h0z : ¬((0:V3) = z) := fun h => hz h.symm
  simp only [affGe, Set.mem_setOf_eq, Affsign]
  refine ⟨fun w => if w = (0:V3) then 1 else 0, hfin, ?_, ?_, ?_⟩
  · rw [sum_insert_pair_v hfin (by exact fun h => h0y h) (by exact fun h => h0z h)
      (by exact fun h => hyz h), if_pos rfl, one_smul, if_neg (fun h => hy h),
      zero_smul, if_neg (fun h => hz h), zero_smul, add_zero, add_zero]
  · intro w hw
    show 0 ≤ (if w = (0:V3) then 1 else 0)
    rcases eq_or_ne w (0:V3) with h0 | h0
    · rw [h0, if_pos rfl]; norm_num
    · rw [if_neg h0]
  · rw [sum_insert_pair_s hfin (by exact fun h => h0y h) (by exact fun h => h0z h)
      (by exact fun h => hyz h), if_pos rfl, if_neg (fun h => hy h),
      if_neg (fun h => hz h)]
    ring

/-- The squared-distance identity in `dotProduct` form. -/
theorem w4cs_norm_sq_eq_inner (x y : V3) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (x ⬝ᵥ y) := by
  rw [norm_sq_eq_dot, norm_sq_eq_dot, norm_sq_eq_dot, ← inner_eq_dot, ← inner_eq_dot,
    ← inner_eq_dot, ← inner_eq_dot, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_comm y x]
  ring

/-! The remaining S-G pieces (`w4cs_ray_subset_cone`, `w4cs_affGe_smul`,
`w4cs_norm_min_ray`, `w4cs_ballAnnulus_4ponits_aff_gt`, the edge-vertex layer,
the shared-endpoint edge-edge case and the assemblers
`w4cs_fan7_of_clauses` / `w4cs_FAN_of_limit`) are drafted in the lane artifact
`Kit-draft-w4.lean` — the proofs are complete modulo a short list of
tactic-level residuals (the `⬝ᵥ`-token split between the `EuclideanSpace` dot
(`inner_eq_dot`) and the `norm_sq_eq_dot`-produced `WithLp.ofLp` dot, plus
`mul_div_cancel₀`/`le_div_iff_mul_le` argument-order drift in this Mathlib),
documented in Evidence.md §3. -/

/-- A point collinear with `0` and `y` is a scalar multiple of `y`. -/
theorem w4cs_collinear0_smul {y v : V3} (hy : y ≠ 0) (hcol : Collinear3 (0:V3) y v) :
    ∃ c : ℝ, v = c • y := by
  have h0y : ((0:V3)) ≠ y := fun h => hy h.symm
  rw [collinear3_iff_mem_affineSpan h0y] at hcol
  obtain ⟨c, hc⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hcol
  refine ⟨c, ?_⟩
  rw [← hc, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, sub_zero, add_zero]


/-! The remaining S-G pieces (`w4cs_ray_subset_cone`, `w4cs_affGe_smul`,
`w4cs_norm_min_ray`, `w4cs_ballAnnulus_4ponits_aff_gt`, the edge-vertex layer,
the shared-endpoint edge-edge case and the assemblers
`w4cs_fan7_of_clauses` / `w4cs_FAN_of_limit`) are drafted in the lane artifact
`Kit-draft-w4.lean` — the proofs are complete modulo a short list of
tactic-level residuals (the `⬝ᵥ`-token split between the `EuclideanSpace` dot
(`inner_eq_dot`) and the `norm_sq_eq_dot`-produced `WithLp.ofLp` dot, plus
`mul_div_cancel₀`/`le_div_iff_mul_le` argument-order drift in this Mathlib),
documented in Evidence.md §3. -/

end W4Kit

section W6aKit

/-! ### W6a P1: static geometric core (annulus ray estimates, gt×ray kills,
cone-ray fan7 face, shared-endpoint edge-edge face). -/

/-- Sharp ray-distance estimate (HOL `BALL_ANNULUS_3PONITS_NORM_MIN`,
dih2k.hl:852): a positive point of the ray through `w` stays at distance at
least `√(4 − h0²)` from the distinct, 2-separated annulus point `v`. -/
theorem w6acs_norm_min_ray {v w : V3} (hvw : v ≠ w) (h2 : 2 ≤ ‖v - w‖)
    (hvm : v ∈ ballAnnulus) (hwm : w ∈ ballAnnulus) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (4 - h0 ^ 2) ≤ ‖v - t • w‖ := by
  obtain ⟨hv2, hvu⟩ := ballAnnulus_norm_bounds hvm
  obtain ⟨hw2, hwu⟩ := ballAnnulus_norm_bounds hwm
  have h126 : h0 = 1.26 := rfl
  have h4pos : (0:ℝ) ≤ 4 - h0 ^ 2 := by norm_num [h126]
  have hp : (0:ℝ) ≤ h0 ^ 2 := by norm_num [h126]
  have h4h0 : (0:ℝ) ≤ 7 - 4 * h0 ^ 2 := by norm_num [h126]
  have hA2ge : (4:ℝ) ≤ ‖v‖ ^ 2 := by nlinarith [hv2]
  have hB2ge : (4:ℝ) ≤ ‖w‖ ^ 2 := by nlinarith [hw2]
  have hexp : ‖v - t • w‖ ^ 2
      = ‖v‖ ^ 2 + t ^ 2 * ‖w‖ ^ 2 - 2 * (t * (v ⬝ᵥ w)) := by
    have h1 := w4cs_norm_sq_eq_inner v (t • w)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow] at h1
    rw [← inner_eq_dot, real_inner_smul_right, inner_eq_dot] at h1
    linarith [h1]
  have hCbound : v ⬝ᵥ w ≤ (‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2 := by
    have h := w4cs_norm_sq_eq_inner v w
    have hsq : (4:ℝ) ≤ ‖v - w‖ ^ 2 := by nlinarith
    linarith
  by_cases hcle : v ⬝ᵥ w ≤ 0
  · -- obtuse: direct
    have htc : t * (v ⬝ᵥ w) ≤ 0 := by nlinarith [hcle, ht.le]
    have htB : (0:ℝ) ≤ t ^ 2 * ‖w‖ ^ 2 := by positivity
    have hlow : 4 - h0 ^ 2 ≤ ‖v - t • w‖ ^ 2 := by
      rw [hexp]; linarith [hA2ge, htB, htc, h4pos, hp]
    exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hlow⟩
  · push Not at hcle
    -- acute: AM–GM + the sharp box algebra
    have hC0 : (0:ℝ) < v ⬝ᵥ w := hcle
    have hSpos : (0:ℝ) ≤ (‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2 := by linarith [hA2ge, hB2ge]
    have hCS : (v ⬝ᵥ w) ^ 2 ≤ ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 := by
      have hCS1 : (0:ℝ) ≤ v ⬝ᵥ w * ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) :=
        mul_nonneg (le_of_lt hC0) hSpos
      nlinarith [hCS1, le_of_lt hC0, hCbound]
    have hB0 : (0:ℝ) < ‖w‖ := by positivity
    have hB2 : (0:ℝ) < ‖w‖ ^ 2 := by positivity
    -- AM–GM: 0 ≤ (tB² − C)² gives −C²/B² ≤ t²B² − 2tC
    have hAM : -((v ⬝ᵥ w) ^ 2 / ‖w‖ ^ 2) ≤ t ^ 2 * ‖w‖ ^ 2 - 2 * (t * (v ⬝ᵥ w)) := by
      have hexp2 : (t * ‖w‖ ^ 2 - v ⬝ᵥ w) ^ 2
          = t ^ 2 * ‖w‖ ^ 2 * ‖w‖ ^ 2 - 2 * (t * (v ⬝ᵥ w) * ‖w‖ ^ 2)
            + (v ⬝ᵥ w) ^ 2 := by
        ring
      have hnum : 0 ≤ t ^ 2 * ‖w‖ ^ 2 * ‖w‖ ^ 2 - 2 * (t * (v ⬝ᵥ w) * ‖w‖ ^ 2)
          + (v ⬝ᵥ w) ^ 2 := by
        rw [← hexp2]
        exact sq_nonneg _
      have hdiv : (t ^ 2 * ‖w‖ ^ 2 * ‖w‖ ^ 2 - 2 * (t * (v ⬝ᵥ w) * ‖w‖ ^ 2)
          + (v ⬝ᵥ w) ^ 2) / ‖w‖ ^ 2
          = t ^ 2 * ‖w‖ ^ 2 - 2 * (t * (v ⬝ᵥ w)) + (v ⬝ᵥ w) ^ 2 / ‖w‖ ^ 2 := by
        field_simp
      have hpos : 0 ≤ t ^ 2 * ‖w‖ ^ 2 - 2 * (t * (v ⬝ᵥ w))
          + (v ⬝ᵥ w) ^ 2 / ‖w‖ ^ 2 := by
        have h1 := div_nonneg hnum (le_of_lt hB2)
        rw [hdiv] at h1
        exact h1
      linarith
    -- the sharp box algebra
    have hA2le : ‖v‖ ^ 2 ≤ 4 * h0 ^ 2 := by nlinarith [hvu, hv2, h126]
    have hB2le : ‖w‖ ^ 2 ≤ 4 * h0 ^ 2 := by nlinarith [hwu, hw2, h126]
    have hbox : ‖w‖ ^ 2 * (4 - h0 ^ 2)
        ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 - ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 := by
      have e1 : (0:ℝ) ≤ ‖v‖ ^ 2 - 4 := by linarith
      have e2 : (0:ℝ) ≤ 2 * ‖w‖ ^ 2 + 4 - ‖v‖ ^ 2 := by linarith [hB2ge, hA2le, h4h0]
      have e3 : (0:ℝ) ≤ ‖w‖ ^ 2 * (4 * h0 ^ 2 - ‖w‖ ^ 2) := by positivity
      have e4 : (0:ℝ) ≤ (‖v‖ ^ 2 - 4) * (2 * ‖w‖ ^ 2 + 4 - ‖v‖ ^ 2)
          + ‖w‖ ^ 2 * (4 * h0 ^ 2 - ‖w‖ ^ 2) :=
        add_nonneg (mul_nonneg e1 e2) e3
      have e5 : (‖v‖ ^ 2 - 4) * (2 * ‖w‖ ^ 2 + 4 - ‖v‖ ^ 2)
          + ‖w‖ ^ 2 * (4 * h0 ^ 2 - ‖w‖ ^ 2)
          = 4 * (‖v‖ ^ 2 * ‖w‖ ^ 2 - ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2
            - ‖w‖ ^ 2 * (4 - h0 ^ 2)) := by
        ring
      linarith
    have hmid : 4 - h0 ^ 2
        ≤ ‖v‖ ^ 2 - ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 / ‖w‖ ^ 2 := by
      have hh : ‖w‖ ^ 2 * (‖v‖ ^ 2 - ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 / ‖w‖ ^ 2)
          = ‖v‖ ^ 2 * ‖w‖ ^ 2 - ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 := by
        field_simp
      have hle : ‖w‖ ^ 2 * (4 - h0 ^ 2)
          ≤ ‖w‖ ^ 2 * (‖v‖ ^ 2 - ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 / ‖w‖ ^ 2) := by
        rw [hh]; exact hbox
      exact le_of_mul_le_mul_left hle hB2
    have hcd : (v ⬝ᵥ w) ^ 2 / ‖w‖ ^ 2
        ≤ ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 / ‖w‖ ^ 2 := by
      have hh1 : ‖w‖ ^ 2 * ((v ⬝ᵥ w) ^ 2 / ‖w‖ ^ 2) = (v ⬝ᵥ w) ^ 2 := by
        field_simp
      have hh2 : ‖w‖ ^ 2 * (((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 / ‖w‖ ^ 2)
          = ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 := by
        field_simp
      have hm : ‖w‖ ^ 2 * ((v ⬝ᵥ w) ^ 2 / ‖w‖ ^ 2)
          ≤ ‖w‖ ^ 2 * (((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 / ‖w‖ ^ 2) := by
        rw [hh1, hh2]; exact hCS
      exact le_of_mul_le_mul_left hm hB2
    have hlow : 4 - h0 ^ 2 ≤ ‖v - t • w‖ ^ 2 := by
      have hQ1 : ‖v - t • w‖ ^ 2 ≥ ‖v‖ ^ 2 - (v ⬝ᵥ w) ^ 2 / ‖w‖ ^ 2 := by
        rw [hexp]; linarith [hAM]
      have hQ2 : ‖v - t • w‖ ^ 2
          ≥ ‖v‖ ^ 2 - ((‖v‖ ^ 2 + ‖w‖ ^ 2 - 4) / 2) ^ 2 / ‖w‖ ^ 2 := by
        rw [hexp]; linarith [hcd]
      linarith [hQ1, hQ2, hmid]
    exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hlow⟩

/-- Scaling form of a point of the open `{0}`-cone. -/
theorem w6acs_affGt_zero_scale {u v w : V3} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hw : w ∈ affGt {(0:V3)} {u, v}) :
    ∃ a t : ℝ, 0 < a ∧ 0 < t ∧ t < 1 ∧ a • w = (1 - t) • u + t • v := by
  have hdis : Disjoint ({(0:V3)} : Set V3) {u, v} := by
    rw [Set.disjoint_singleton_left]
    intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hu rfl
    · exact hv rfl
  rw [aff_gt_1_2 hdis, Set.mem_setOf_eq] at hw
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hwq⟩ := hw
  have hs : 0 < t2 + t3 := add_pos ht2 ht3
  refine ⟨(t2 + t3)⁻¹, t3 / (t2 + t3), inv_pos.2 hs, div_pos ht3 hs, ?_, ?_⟩
  · rw [div_lt_one hs]
    linarith
  · have hkey1 : ((t2 + t3)⁻¹ * t2) = 1 - t3 / (t2 + t3) := by
      field_simp
      linarith
    have hkey2 : ((t2 + t3)⁻¹ * t3) = t3 / (t2 + t3) := by
      field_simp
    rw [hwq, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_zero,
      zero_add, hkey1, hkey2]

/-- The open `{0}`-cone is closed under positive scaling. -/
theorem w6acs_affGt_smul {y z x : V3} (hy : y ≠ 0) (hz : z ≠ 0) {c : ℝ} (hc : 0 < c)
    (hx : x ∈ affGt ({0} : Set V3) ({y, z})) : c • x ∈ affGt ({0} : Set V3) ({y, z}) := by
  have hdis : Disjoint ({(0:V3)} : Set V3) {y, z} := by
    rw [Set.disjoint_singleton_left]
    intro hx2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx2
    rcases hx2 with rfl | rfl
    · exact hy rfl
    · exact hz rfl
  rw [aff_gt_1_2 hdis, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hxq⟩ := hx
  refine ⟨c * t1 + (1 - c), c * t2, c * t3, by nlinarith [(le_of_lt hc), ht2],
    by nlinarith [(le_of_lt hc), ht3], by nlinarith [hsum], ?_⟩
  rw [hxq]
  module

/-- Annulus point versus the open cone of a short chord (HOL
`BALL_ANNULUS_4PONITS_AFF_GT`, dih2k.hl:1149; the LA4 copy is a sorry giant). -/
theorem w6acs_ballAnnulus_4ponits_aff_gt {v w z : V3}
    (hnc1 : ¬ Collinear3 (0:V3) v z) (hnc2 : ¬ Collinear3 (0:V3) w z)
    (h2 : 2 ≤ ‖v - w‖) (hup : ‖v - w‖ ≤ cstab_p4) (h3 : 2 ≤ ‖z - v‖)
    (h4 : 2 ≤ ‖z - w‖) (hvm : v ∈ ballAnnulus) (hwm : w ∈ ballAnnulus)
    (hzm : z ∈ ballAnnulus) : z ∉ affGt {(0:V3)} {v, w} := by
  intro hz
  have hvw : v ≠ w := fun he => (by rw [he] at h2; norm_num at h2 : False)
  have hvz : v ≠ z := fun he => (by rw [he] at h3; norm_num at h3 : False)
  have hwz : w ≠ z := fun he => (by rw [he] at h4; norm_num at h4 : False)
  obtain ⟨a, t, ha0, ht0, ht1, hac⟩ := w6acs_affGt_zero_scale
    (w4cs_annulus_ne_zero hvm) (w4cs_annulus_ne_zero hwm) hvw hz
  have hmin1 := w6acs_norm_min_ray hvz (by rw [norm_sub_rev]; exact h3) hvm hzm ha0
  have hmin2 := w6acs_norm_min_ray hwz (by rw [norm_sub_rev]; exact h4) hwm hzm ha0
  have hred1 : v - a • z = t • (v - w) := by rw [hac]; module
  have hred2 : w - a • z = (1 - t) • (w - v) := by rw [hac]; module
  rw [hred1, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hmin1
  rw [hred2, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 1 - t),
    norm_sub_rev] at hmin2
  have habsurd : 2 * Real.sqrt (4 - h0 ^ 2) ≤ cstab_p4 := by linarith
  have h126 : h0 = 1.26 := rfl
  have h0p : (0:ℝ) ≤ 4 - h0 ^ 2 := by norm_num [h126]
  have hs2 : Real.sqrt (4 * (4 - h0 ^ 2)) = 2 * Real.sqrt (4 - h0 ^ 2) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) (4 - h0 ^ 2)]
    norm_num
  rw [← hs2, Real.sqrt_le_iff] at habsurd
  rcases habsurd with ⟨_, h5⟩
  norm_num [h126, show cstab_p4 = 3.01 from rfl] at h5

/-- Same-ray annulus points are closer than the 2-separation. -/
theorem w6acs_same_ray_dist_lt2 {y v : V3} (hyv : 2 ≤ ‖y - v‖) (hy : y ∈ ballAnnulus)
    (hv : v ∈ ballAnnulus) {c : ℝ} (hc : 0 < c) (hcv : v = c • y) : False := by
  obtain ⟨hy2, hyu⟩ := ballAnnulus_norm_bounds hy
  obtain ⟨hv2, hvu⟩ := ballAnnulus_norm_bounds hv
  have h126 : h0 = 1.26 := rfl
  have hve : v - y = (c - 1) • y := by rw [hcv]; module
  have h1 : ‖v - y‖ = |c - 1| * ‖y‖ := by rw [hve, norm_smul, Real.norm_eq_abs]
  have h3 : ‖v‖ = c * ‖y‖ := by rw [hcv, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hbound : |c - 1| * ‖y‖ ≤ 2 * h0 - 2 := by
    by_cases hc1 : (1:ℝ) ≤ c
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c - 1)]
      linarith
    · rw [abs_of_neg (by linarith : (c:ℝ) - 1 < 0)]
      linarith
  have hh : (2:ℝ) ≤ ‖v - y‖ := by rw [norm_sub_rev]; exact hyv
  rw [h1] at hh
  have h02 : (2:ℝ) * h0 - 2 < 2 := by norm_num [h126]
  linarith

/-- Independence of two non-collinear vectors (scalar-coefficient uniqueness). -/
theorem w6acs_smul_indep {y z : V3} (hy : y ≠ 0) (hz : z ≠ 0)
    (hnc : ¬ Collinear3 (0:V3) y z) {a b : ℝ} (h : a • y + b • z = 0) :
    a = 0 ∧ b = 0 := by
  rcases eq_or_ne b 0 with hb0 | hbne
  · refine ⟨?_, hb0⟩
    have h1 : a • y = 0 := by
      rw [← h, hb0, zero_smul, add_zero]
    exact (smul_eq_zero.mp h1).resolve_right hy
  · exfalso
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_smul, zero_add, smul_eq_zero] at h
      exact hz (h.resolve_left hbne)
    have h3 : (1 / b) • (a • y + b • z) = (0:V3) := by
      rw [h]; simp
    rw [smul_add, smul_smul, smul_smul] at h3
    have h4 : ((1 / b) * a) = a / b := by ring
    have h5 : ((1 / b) * b) = 1 := by field_simp
    rw [h4, h5] at h3
    exact hnc (w5bcs_collinear_of_eq_zero (by norm_num) h3.symm)

/-- A vertex 2-separated from a capped edge is never inside the edge's open
cone (the collinear cases collapse by independence; only the generic case
needs the 4-points estimate). -/
theorem w6acs_indep_gt_kill {y z v : V3} (hnc : ¬ Collinear3 (0:V3) y z)
    (hy : y ∈ ballAnnulus) (hz : z ∈ ballAnnulus) (hv : v ∈ ballAnnulus)
    (h2 : 2 ≤ ‖y - z‖) (hup : ‖y - z‖ ≤ cstab_p4)
    (h3 : 2 ≤ ‖y - v‖) (h4 : 2 ≤ ‖z - v‖)
    (hvin : v ∈ affGt ({0} : Set V3) ({y, z})) : False := by
  have hy0 : y ≠ 0 := w4cs_annulus_ne_zero hy
  have hz0 : z ≠ 0 := w4cs_annulus_ne_zero hz
  rcases Classical.em (Collinear3 (0:V3) y v) with hc1 | hc1
  · obtain ⟨κ, hκ⟩ := w4cs_collinear0_smul hy0 hc1
    obtain ⟨c1, c2, hc1p, hc2p, hvq⟩ := w5bcs_coeff_of_mem_affGt hy0 hz0 hvin
    have hkeq : κ • y = c1 • y + c2 • z := by rw [← hκ, hvq]
    have heq : (κ - c1) • y + (-c2) • z = 0 := by
      rw [show (((κ - c1) • y + (-c2) • z : V3)) = κ • y - (c1 • y + c2 • z) from
        by module]
      rw [hkeq]
      module
    obtain ⟨e1, e2⟩ := w6acs_smul_indep hy0 hz0 hnc heq
    rw [neg_eq_zero.mp e2] at hc2p
    exact lt_irrefl (0:ℝ) hc2p
  rcases Classical.em (Collinear3 (0:V3) z v) with hc2 | hc2
  · obtain ⟨κ, hκ⟩ := w4cs_collinear0_smul hz0 hc2
    obtain ⟨c1, c2, hc1p, hc2p, hvq⟩ := w5bcs_coeff_of_mem_affGt hy0 hz0 hvin
    have hkeq : κ • z = c1 • y + c2 • z := by rw [← hκ, hvq]
    have heq : c1 • y + (c2 - κ) • z = 0 := by
      rw [show ((c1 • y + (c2 - κ) • z : V3)) = c1 • y + c2 • z - κ • z from
        by module]
      rw [hkeq]
      module
    obtain ⟨e1, e2⟩ := w6acs_smul_indep hy0 hz0 hnc heq
    rw [e1] at hc1p
    exact lt_irrefl (0:ℝ) hc1p
  · exact w6acs_ballAnnulus_4ponits_aff_gt hc1 hc2 h2 hup
      (by rw [norm_sub_rev]; exact h3) (by rw [norm_sub_rev]; exact h4) hy hz hv hvin

/-- A point of the open cone of a capped edge that lies on a ray of any other
annulus point 2-separated from the edge's endpoints is the origin. -/
theorem w6acs_gt_ray_kill_strong {y z v x : V3}
    (hnc : ¬ Collinear3 (0:V3) y z) (hy : y ∈ ballAnnulus) (hz : z ∈ ballAnnulus)
    (hv : v ∈ ballAnnulus) (h2 : 2 ≤ ‖y - z‖) (hup : ‖y - z‖ ≤ cstab_p4)
    (h3 : 2 ≤ ‖y - v‖) (h4 : 2 ≤ ‖z - v‖)
    (hx1 : x ∈ affGt ({0} : Set V3) ({y, z}))
    (hx2 : x ∈ affGe ({0} : Set V3) ({v})) : x = 0 := by
  by_cases hx0 : x = 0
  · exact hx0
  · exfalso
    have hv0 : v ≠ 0 := w4cs_annulus_ne_zero hv
    obtain ⟨t, ht0, hxt⟩ := w4cs_ray_coeff hv0 hx2
    have htp : 0 < t := by
      by_cases hte : t = 0
      · exact absurd (by rw [hte, zero_smul] at hxt; exact hxt) hx0
      · exact lt_of_le_of_ne ht0 (Ne.symm hte)
    have hvin : v ∈ affGt ({0} : Set V3) ({y, z}) := by
      have hsc := w6acs_affGt_smul (w4cs_annulus_ne_zero hy) (w4cs_annulus_ne_zero hz)
        (inv_pos.mpr htp) hx1
      rw [hxt, smul_smul, inv_mul_cancel₀ (ne_of_gt htp), one_smul] at hsc
      simpa using hsc
    exact w6acs_indep_gt_kill hnc hy hz hv h2 hup h3 h4 hvin

/-- A point of the open cone of a non-degenerate edge that lies on the ray
through one of the edge's own endpoints is the origin. -/
theorem w6acs_gt_ray_self_kill {y z x : V3} (hnc : ¬ Collinear3 (0:V3) y z)
    (hy0 : y ≠ 0) (hz0 : z ≠ 0)
    (hx1 : x ∈ affGt ({0} : Set V3) ({y, z}))
    (hx2 : x ∈ affGe ({0} : Set V3) ({y})) : x = 0 := by
  obtain ⟨t, ht0, hxt⟩ := w4cs_ray_coeff hy0 hx2
  rcases eq_or_ne x 0 with h0 | hne
  · exact h0
  · exfalso
    have htp : 0 < t := by
      by_cases hte : t = 0
      · exact absurd (by rw [hte, zero_smul] at hxt; exact hxt) hne
      · exact lt_of_le_of_ne ht0 (Ne.symm hte)
    obtain ⟨c1, c2, hc1, hc2, hvq⟩ := w5bcs_coeff_of_mem_affGt hy0 hz0 hx1
    rw [hvq] at hxt
    have heq : (c1 - t) • y + c2 • z = 0 := by
      rw [show (((c1 - t) • y + c2 • z : V3)) = c1 • y + c2 • z - t • y from
        by module]
      rw [hxt]
      exact sub_self (t • y)
    obtain ⟨e1, e2⟩ := w6acs_smul_indep hy0 hz0 hnc heq
    rw [e2] at hc2
    exact lt_irrefl (0:ℝ) hc2

/-- fan7 edge×edge face with a shared endpoint: the two cones meet exactly in
the ray through the shared vertex.  `hplanar` is the pointwise planar-kill
(the W6a gap-2 statement) supplied as an explicit hypothesis parameter. -/
theorem w6acs_fan7_edges_shared {a b c : V3}
    (hplanar : ∀ {y z y1 z1 x : V3},
      ¬ Collinear3 (0:V3) y z → ¬ Collinear3 (0:V3) y1 z1 →
      y ∈ ballAnnulus ∧ z ∈ ballAnnulus ∧ y1 ∈ ballAnnulus ∧ z1 ∈ ballAnnulus →
      ‖y - z‖ ≤ cstab_p4 → ‖y1 - z1‖ ≤ cstab_p4 →
      ¬ (y1 ∈ ({y, z} : Set V3) ∧ z1 ∈ ({y, z} : Set V3)) →
      (∀ v w : V3, v ≠ w → v ∈ ({y, z, y1, z1} : Set V3) →
        w ∈ ({y, z, y1, z1} : Set V3) → (2:ℝ) ≤ ‖v - w‖) →
      (crossProduct (WithLp.ofLp y : Fin 3 → ℝ) (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ
        (WithLp.ofLp y1 : Fin 3 → ℝ) = 0 →
      (crossProduct (WithLp.ofLp y : Fin 3 → ℝ) (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ
        (WithLp.ofLp z1 : Fin 3 → ℝ) = 0 →
      x ∈ affGt ({0} : Set V3) ({y, z}) →
      x ∈ affGt ({0} : Set V3) ({y1, z1}) → False)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a ∈ ballAnnulus) (hb : b ∈ ballAnnulus) (hcm : c ∈ ballAnnulus)
    (hnc1 : ¬ Collinear3 (0:V3) a b) (hnc2 : ¬ Collinear3 (0:V3) b c)
    (h2ab : 2 ≤ ‖a - b‖) (hupab : ‖a - b‖ ≤ cstab_p4)
    (h2bc : 2 ≤ ‖b - c‖) (hupbc : ‖b - c‖ ≤ cstab_p4)
    (h2ac : 2 ≤ ‖a - c‖) :
    affGe ({0} : Set V3) ({a, b}) ∩ affGe ({0} : Set V3) ({b, c})
      = affGe ({0} : Set V3) ({b}) := by
  have ha0 : a ≠ 0 := w4cs_annulus_ne_zero ha
  have hb0 : b ≠ 0 := w4cs_annulus_ne_zero hb
  have hc0 : c ≠ 0 := w4cs_annulus_ne_zero hcm
  have hdecb : affGe ({0} : Set V3) ({a, b})
      = affGt ({0} : Set V3) ({a, b}) ∪ affGe ({0} : Set V3) ({a})
        ∪ affGe ({0} : Set V3) ({b}) :=
    aff_ge_eq_aff_gt_union_aff_ge hnc1
  have hdecc : affGe ({0} : Set V3) ({b, c})
      = affGt ({0} : Set V3) ({b, c}) ∪ affGe ({0} : Set V3) ({b})
        ∪ affGe ({0} : Set V3) ({c}) :=
    aff_ge_eq_aff_gt_union_aff_ge hnc2
  -- the 3-point 2-separation for the gap-2 call
  have hdec4 : ∀ u : V3, u ∈ ({a, b, b, c} : Set V3) → u = a ∨ u = b ∨ u = c := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    tauto
  have hsep3 : ∀ v w : V3, v ≠ w → v ∈ ({a, b, b, c} : Set V3) →
      w ∈ ({a, b, b, c} : Set V3) → (2:ℝ) ≤ ‖v - w‖ := by
    intro v w hvw hv hw
    have he1 := hdec4 v hv
    have he2 := hdec4 w hw
    rcases he1 with rfl | rfl | rfl
    · rcases he2 with rfl | rfl | rfl
      · exact absurd rfl hvw
      · exact h2ab
      · exact h2ac
    · rcases he2 with rfl | rfl | rfl
      · rw [norm_sub_rev]; exact h2ab
      · exact absurd rfl hvw
      · exact h2bc
    · rcases he2 with rfl | rfl | rfl
      · rw [norm_sub_rev]; exact h2ac
      · rw [norm_sub_rev]; exact h2bc
      · exact absurd rfl hvw
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    rw [hdecb, Set.mem_union, Set.mem_union] at hx1
    rw [hdecc, Set.mem_union, Set.mem_union] at hx2
    refine Or.elim hx1 (fun ha1 => ?_) (fun hc1 => ?_)
    · refine Or.elim ha1 (fun g1 => ?_) (fun r1a => ?_)
      · refine Or.elim hx2 (fun ha2 => ?_) (fun hc2 => ?_)
        · refine Or.elim ha2 (fun g2 => ?_) (fun r2b => ?_)
          · exfalso
            -- gt∩gt: planes distinct kill, or the coplanar gap-2 kill
            by_cases hpl : (crossProduct (WithLp.ofLp a : Fin 3 → ℝ)
                (WithLp.ofLp b : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp c : Fin 3 → ℝ) = 0
            · exact hplanar hnc1 hnc2 ⟨ha, hb, hb, hcm⟩ hupab hupbc
                (by
                  intro hcon
                  rcases hcon with ⟨_, h2⟩
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
                  rcases h2 with h2 | h2
                  · exact hac h2.symm
                  · exact hbc h2.symm) hsep3
                (by rw [dotProduct_comm]; exact dot_cross_self a b) hpl g1 g2
            · obtain ⟨α, β, hα, hβ, hxq⟩ := w5bcs_coeff_of_mem_affGt ha0 hb0 g1
              obtain ⟨γ, δ, hγ, hδ, hxq2⟩ := w5bcs_coeff_of_mem_affGt hb0 hc0 g2
              have h0x : (crossProduct (WithLp.ofLp a : Fin 3 → ℝ)
                  (WithLp.ofLp b : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp x : Fin 3 → ℝ) = 0 := by
                rw [hxq]
                simp only [WithLp.ofLp_add, WithLp.ofLp_smul]
                rw [dotProduct_add, dotProduct_smul, dotProduct_smul,
                  show ((crossProduct (WithLp.ofLp a : Fin 3 → ℝ)
                      (WithLp.ofLp b : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp a : Fin 3 → ℝ)) = 0 from
                    (by rw [dotProduct_comm]; exact dot_self_cross a b),
                  show ((crossProduct (WithLp.ofLp a : Fin 3 → ℝ)
                      (WithLp.ofLp b : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp b : Fin 3 → ℝ)) = 0 from
                    (by rw [dotProduct_comm]; exact dot_cross_self a b)]
                ring
              have hδx : (crossProduct (WithLp.ofLp a : Fin 3 → ℝ)
                  (WithLp.ofLp b : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp x : Fin 3 → ℝ)
                  = δ * ((crossProduct (WithLp.ofLp a : Fin 3 → ℝ)
                    (WithLp.ofLp b : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp c : Fin 3 → ℝ)) := by
                rw [hxq2]
                simp only [WithLp.ofLp_add, WithLp.ofLp_smul]
                rw [dotProduct_add, dotProduct_smul, dotProduct_smul,
                  show ((crossProduct (WithLp.ofLp a : Fin 3 → ℝ)
                      (WithLp.ofLp b : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp b : Fin 3 → ℝ)) = 0 from
                    (by rw [dotProduct_comm]; exact dot_cross_self a b)]
                ring
              rw [h0x] at hδx
              exact hpl (by
                rcases mul_eq_zero.mp hδx.symm with h1 | h1
                · exact absurd h1 (ne_of_gt hδ)
                · exact h1)
          · -- gt(a,b) ∩ ray(b): independence kill
            obtain ⟨t, ht0, hxt⟩ := w4cs_ray_coeff hb0 r2b
            rcases eq_or_ne x 0 with h0 | hne
            · rw [h0]; exact w4cs_zero_mem_ray hb0
            · exfalso
              have htp : 0 < t := by
                by_cases hte : t = 0
                · exact absurd (by rw [hte, zero_smul] at hxt; exact hxt) hne
                · exact lt_of_le_of_ne ht0 (Ne.symm hte)
              obtain ⟨α, β, hα, hβ, hxq⟩ := w5bcs_coeff_of_mem_affGt ha0 hb0 g1
              rw [hxq] at hxt
              have heq : α • a + (β - t) • b = 0 := by
                rw [show ((α • a + (β - t) • b : V3)) = α • a + β • b - t • b from
                  by module]
                rw [hxt]
                exact sub_self (t • b)
              obtain ⟨e1, e2⟩ := w6acs_smul_indep ha0 hb0 hnc1 heq
              rw [e1] at hα
              exact lt_irrefl (0:ℝ) hα
        · -- gt(a,b) ∩ ray(c): vertex-in-open-cone kill
          obtain ⟨t, ht0, hxt⟩ := w4cs_ray_coeff hc0 hc2
          rcases eq_or_ne x 0 with h0 | hne
          · rw [h0]; exact w4cs_zero_mem_ray hb0
          · exfalso
            have htp : 0 < t := by
              by_cases hte : t = 0
              · exact absurd (by rw [hte, zero_smul] at hxt; exact hxt) hne
              · exact lt_of_le_of_ne ht0 (Ne.symm hte)
            have hcin : c ∈ affGt ({0} : Set V3) ({a, b}) := by
              have hsc := w6acs_affGt_smul ha0 hb0 (inv_pos.mpr htp) g1
              rw [hxt, smul_smul, inv_mul_cancel₀ (ne_of_gt htp), one_smul] at hsc
              simpa using hsc
            exact w6acs_indep_gt_kill hnc1 ha hb hcm h2ab hupab h2ac h2bc hcin
      · refine Or.elim hx2 (fun ha2 => ?_) (fun hc2 => ?_)
        · refine Or.elim ha2 (fun g2 => ?_) (fun r2b => ?_)
          · -- ray(a) ∩ gt(b,c): vertex-in-open-cone kill
            obtain ⟨t, ht0, hxt⟩ := w4cs_ray_coeff ha0 r1a
            rcases eq_or_ne x 0 with h0 | hne
            · rw [h0]; exact w4cs_zero_mem_ray hb0
            · exfalso
              have htp : 0 < t := by
                by_cases hte : t = 0
                · exact absurd (by rw [hte, zero_smul] at hxt; exact hxt) hne
                · exact lt_of_le_of_ne ht0 (Ne.symm hte)
              have hain : a ∈ affGt ({0} : Set V3) ({b, c}) := by
                have hsc := w6acs_affGt_smul hb0 hc0 (inv_pos.mpr htp) g2
                rw [hxt, smul_smul, inv_mul_cancel₀ (ne_of_gt htp), one_smul] at hsc
                simpa using hsc
              exact w6acs_indep_gt_kill hnc2 hb hcm ha h2bc hupbc
                (by rw [norm_sub_rev]; exact h2ab)
                (by rw [norm_sub_rev]; exact h2ac) hain
          · have hx0 := VEC0_BALL_ANNULUS h2ab ha hb r1a r2b
            rw [hx0]
            exact hx0 ▸ w4cs_zero_mem_ray hb0
        · have hx0 := VEC0_BALL_ANNULUS h2ac ha hcm r1a hc2
          rw [hx0]
          exact w4cs_zero_mem_ray hb0
    · refine Or.elim hx2 (fun ha2 => ?_) (fun hc2 => ?_)
      · refine Or.elim ha2 (fun g2 => ?_) (fun r2b => ?_)
        · -- ray(b) ∩ gt(b,c): independence kill
          obtain ⟨t, ht0, hxt⟩ := w4cs_ray_coeff hb0 hc1
          rcases eq_or_ne x 0 with h0 | hne
          · exact h0 ▸ hc1
          · exfalso
            have htp : 0 < t := by
              by_cases hte : t = 0
              · exact absurd (by rw [hte, zero_smul] at hxt; exact hxt) hne
              · exact lt_of_le_of_ne ht0 (Ne.symm hte)
            obtain ⟨γ, δ, hγ, hδ, hxq2⟩ := w5bcs_coeff_of_mem_affGt hb0 hc0 g2
            rw [hxq2] at hxt
            have heq : (t - γ) • b + (-δ) • c = 0 := by
              rw [show (((t - γ) • b + (-δ) • c : V3)) = t • b - (γ • b + δ • c) from
                by module]
              rw [← hxt]
              module
            obtain ⟨e1, e2⟩ := w6acs_smul_indep hb0 hc0 hnc2 heq
            rw [neg_eq_zero.mp e2] at hδ
            exact lt_irrefl (0:ℝ) hδ
        · exact hc1
      · have hx0 := VEC0_BALL_ANNULUS h2bc hb hcm hc1 hc2
        rw [hx0]
        exact w4cs_zero_mem_ray hb0
  · intro hx
    rw [hdecb, hdecc, Set.mem_inter_iff, Set.mem_union, Set.mem_union, Set.mem_union,
      Set.mem_union]
    exact ⟨Or.inr hx, Or.inl (Or.inr hx)⟩


end W6aKit


/-! ## Section W6bKit (bodyclosed-w6b): S-I (the ∃-dart + dih2k clauses) and
S-K (azimInFan ≤ π) for the CONDITION2_SY_cs transfer at the limit point
(HOL WJSCPRO.hl:2292-2686).  Zero new imports; zero sorry. -/

section W6bKit

theorem w6bcs_row_fin {m : ℕ} (l : FinVec m 3) (p : Fin m) :
    rowV3_cs l (p.val + 1) = vecmatsV3_p4 l p := by
  unfold rowV3_cs
  rw [dif_pos (by exact ⟨by omega, by have := p.isLt; omega⟩)]
  refine congrArg (vecmatsV3_p4 l) (Fin.eq_of_val_eq ?_)
  show (p.val + 1 - 1 : ℕ) = p.val
  omega

def w6bcs_prev {k : ℕ} (i : Fin k) : Fin k := ⟨(i.val + k - 1) % k,
  Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

theorem w6bcs_finNext_prev {k : ℕ} (i : Fin k) : finNext (w6bcs_prev i) = i := by
  refine Fin.ext ?_
  by_cases h0 : i.val = 0
  · have hp : (w6bcs_prev i).val = k - 1 := by
      simp only [w6bcs_prev, h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (Nat.sub_lt (by omega) (by omega))
    show (((w6bcs_prev i).val + 1) % k) = i.val
    rw [hp, show ((k - 1 : ℕ) + 1) = k by omega, Nat.mod_self k]
    exact h0.symm
  · have hp : (w6bcs_prev i).val = i.val - 1 := by
      simp only [w6bcs_prev]
      have hsplit : i.val - 1 + k = i.val + k - 1 := by omega
      rw [← hsplit, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    show (((w6bcs_prev i).val + 1) % k) = i.val
    rw [hp, show ((i.val - 1 : ℕ) + 1) = i.val by omega, Nat.mod_eq_of_lt i.isLt]

theorem w6bcs_prev_finNext {k : ℕ} (i : Fin k) : w6bcs_prev (finNext i) = i := by
  refine Fin.ext ?_
  by_cases h0 : i.val + 1 < k
  · have hn : (finNext i).val = i.val + 1 := by
      simp only [finNext]; exact Nat.mod_eq_of_lt h0
    have hp : (w6bcs_prev (finNext i)).val = ((finNext i).val + k - 1) % k := rfl
    show (w6bcs_prev (finNext i)).val = i.val
    rw [hp, hn, show ((i.val + 1 : ℕ) + k - 1) = i.val + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  · have hk : i.val + 1 = k := le_antisymm (by have := i.isLt; omega) (by have := i.isLt; omega)
    have hn : (finNext i).val = 0 := by
      simp only [finNext, hk]
      exact Nat.mod_self k
    have hp : (w6bcs_prev (finNext i)).val = k - 1 := by
      simp only [w6bcs_prev, hn, Nat.zero_add]
      exact Nat.mod_eq_of_lt (Nat.sub_lt (by omega) (by omega))
    show (w6bcs_prev (finNext i)).val = i.val
    rw [hp]
    have := i.isLt
    omega

theorem w6bcs_two_le_fin {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k) (hk1 : 1 < k)
    (L : FinVec k 3) (hL : L ∈ BSY1body_cs k a b)
    {i j : Fin k} (hij : i ≠ j) :
    (2:ℝ) ≤ ‖vecmatsV3_p4 L i - vecmatsV3_p4 L j‖ := by
  rw [← w6bcs_row_fin, ← w6bcs_row_fin]
  exact w3cs_two_le_row_of_BSY1body hsys hs hf hk1 L hL
    (by omega) (by have := i.isLt; omega) (by omega) (by have := j.isLt; omega)
    (fun h => hij (Fin.ext (by omega)))

theorem w6bcs_hinj {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k) (hk1 : 1 < k)
    (L : FinVec k 3) (hL : L ∈ BSY1body_cs k a b) :
    ∀ i j : Fin k, vecmatsV3_p4 L i = vecmatsV3_p4 L j → i = j := by
  intro i j heq
  by_cases hij : i = j
  · exact hij
  · exfalso
    have h2 := w6bcs_two_le_fin hsys hs hf hk1 L hL hij
    rw [heq, sub_self, norm_zero] at h2
    linarith

theorem w6bcs_hne {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k) (hk3 : 3 ≤ k)
    (L : FinVec k 3) (hL : L ∈ BSY1body_cs k a b) (i : Fin k) :
    vecmatsV3_p4 L (w6bcs_prev i) ≠ vecmatsV3_p4 L (finNext i) := by
  have hk1 : 1 < k := by omega
  have hidx : (w6bcs_prev i).val ≠ (finNext i).val := by
    by_cases h0 : i.val = 0
    · have h1 : (w6bcs_prev i).val = k - 1 := by
        simp only [w6bcs_prev, h0, Nat.zero_add]
        exact Nat.mod_eq_of_lt (Nat.sub_lt (by omega) (by omega))
      have h2 : (finNext i).val = 1 := by
        simp only [finNext, h0, Nat.zero_add]
        exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
      rw [h1, h2]; omega
    · have h1 : (w6bcs_prev i).val = i.val - 1 := by
        simp only [w6bcs_prev]
        have hsplit : i.val - 1 + k = i.val + k - 1 := by omega
        rw [← hsplit, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rcases Nat.lt_or_ge (i.val + 1) k with hlt | hge
      · have h2 : (finNext i).val = i.val + 1 := by
          simp only [finNext]; exact Nat.mod_eq_of_lt hlt
        rw [h1, h2]; omega
      · have hik : i.val + 1 = k := le_antisymm (by have := i.isLt; omega) hge
        have h2 : (finNext i).val = 0 := by
          simp only [finNext, hik]
          exact Nat.mod_self k
        rw [h1, h2]; omega
  intro heq
  have h2 := w6bcs_two_le_fin hsys hs hf hk1 L hL (i := w6bcs_prev i) (j := finNext i)
    (Fin.ne_of_val_ne hidx)
  rw [heq, sub_self, norm_zero] at h2
  linarith

theorem w6bcs_ee_eq_setOfEdge {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E)
    (v : V3) : EE_p4 v E = Fan.setOfEdge v V E := by
  ext w
  constructor
  · intro hw
    exact ⟨hw, hfan.1 (Set.mem_sUnion.mpr ⟨{v, w}, hw, by simp⟩)⟩
  · intro hw
    exact hw.1

theorem w6bcs_setOfEdge_eq {k : ℕ} (l : FinVec k 3) (hk1 : 1 < k)
    (hinj : ∀ i j : Fin k, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) (i : Fin k) :
    Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)} := by
  exact SET_OF_EDGE_CARD_EQ2 (l := l) hk1 hinj (w6bcs_prev i)
    (u := vecmatsV3_p4 l (w6bcs_prev i)) (v := vecmatsV3_p4 l i)
    (w := vecmatsV3_p4 l (finNext i)) rfl (by rw [w6bcs_finNext_prev])
    (by rw [w6bcs_finNext_prev])

theorem w6bcs_sigma_next {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Fan.sigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i))
      = vecmatsV3_p4 l (w6bcs_prev i) := by
  have hnot : ¬ (Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (finNext i)}) := by
    intro hsingle
    have hmem : vecmatsV3_p4 l (w6bcs_prev i) ∈ ({vecmatsV3_p4 l (finNext i)} : Set V3) := by
      rw [hsingle.symm.trans (hsoe i)]
      exact Set.mem_insert _ _
    rw [Set.mem_singleton_iff] at hmem
    exact hne i hmem
  rw [Fan.sigmaFan, if_neg hnot]
  have hwit : (fun w : V3 => w ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) ∧ w ≠ vecmatsV3_p4 l (finNext i) ∧
          ∀ w1 ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
            (E_SY_p4 (vecmatsV3_p4 l)), w1 ≠ vecmatsV3_p4 l (finNext i) →
            azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i)) w ≤
              azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i)) w1)
      (vecmatsV3_p4 l (w6bcs_prev i)) := by
    show vecmatsV3_p4 l (w6bcs_prev i) ∈ Fan.setOfEdge (vecmatsV3_p4 l i)
        (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) ∧
      vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i) ∧
      ∀ w1 ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)), w1 ≠ vecmatsV3_p4 l (finNext i) →
        azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i))
          (vecmatsV3_p4 l (w6bcs_prev i)) ≤
        azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i)) w1
    refine ⟨?_, hne i, ?_⟩
    · rw [hsoe i]; exact Set.mem_insert _ _
    · intro w1 hw1 hw1ne
      rw [hsoe i] at hw1
      rcases Set.mem_insert_iff.mp hw1 with h | h
      · subst h; exact le_refl _
      · rw [Set.mem_singleton_iff] at h
        exact absurd h hw1ne
  obtain ⟨hm1, hm2, -⟩ := Classical.epsilon_spec
    (p := fun w : V3 => w ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) ∧ w ≠ vecmatsV3_p4 l (finNext i) ∧
          ∀ w1 ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
            (E_SY_p4 (vecmatsV3_p4 l)), w1 ≠ vecmatsV3_p4 l (finNext i) →
            azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i)) w ≤
              azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i)) w1)
    ⟨vecmatsV3_p4 l (w6bcs_prev i), hwit⟩
  have hm3 : (Classical.epsilon (fun w : V3 => w ∈ Fan.setOfEdge (vecmatsV3_p4 l i)
        (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) ∧
          w ≠ vecmatsV3_p4 l (finNext i) ∧
          ∀ w1 ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
            (E_SY_p4 (vecmatsV3_p4 l)), w1 ≠ vecmatsV3_p4 l (finNext i) →
            azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i)) w ≤
              azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i)) w1))
      ∈ ({vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)} : Set V3) := by
    rw [← hsoe i]; exact hm1
  rcases Set.mem_insert_iff.mp hm3 with h | h
  · exact h
  · rw [Set.mem_singleton_iff] at h
    exact absurd h hm2

theorem w6bcs_sigma_prev {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Fan.sigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i))
      = vecmatsV3_p4 l (finNext i) := by
  have hnot : ¬ (Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i)}) := by
    intro hsingle
    have hmem : vecmatsV3_p4 l (finNext i) ∈ ({vecmatsV3_p4 l (w6bcs_prev i)} : Set V3) := by
      rw [hsingle.symm.trans (hsoe i)]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl)
    rw [Set.mem_singleton_iff] at hmem
    exact hne i hmem.symm
  rw [Fan.sigmaFan, if_neg hnot]
  have hwit : (fun w : V3 => w ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) ∧ w ≠ vecmatsV3_p4 l (w6bcs_prev i) ∧
          ∀ w1 ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
            (E_SY_p4 (vecmatsV3_p4 l)), w1 ≠ vecmatsV3_p4 l (w6bcs_prev i) →
            azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i)) w ≤
              azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i)) w1)
      (vecmatsV3_p4 l (finNext i)) := by
    show vecmatsV3_p4 l (finNext i) ∈ Fan.setOfEdge (vecmatsV3_p4 l i)
        (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) ∧
      vecmatsV3_p4 l (finNext i) ≠ vecmatsV3_p4 l (w6bcs_prev i) ∧
      ∀ w1 ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)), w1 ≠ vecmatsV3_p4 l (w6bcs_prev i) →
        azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i))
          (vecmatsV3_p4 l (finNext i)) ≤
        azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i)) w1
    refine ⟨?_, fun hc => hne i hc.symm, ?_⟩
    · rw [hsoe i]; exact Set.mem_insert_of_mem _ rfl
    · intro w1 hw1 hw1ne
      rw [hsoe i] at hw1
      rcases Set.mem_insert_iff.mp hw1 with h | h
      · exact absurd h hw1ne
      · rw [Set.mem_singleton_iff] at h
        subst h
        exact le_refl _
  obtain ⟨hm1, hm2, -⟩ := Classical.epsilon_spec
    (p := fun w : V3 => w ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) ∧ w ≠ vecmatsV3_p4 l (w6bcs_prev i) ∧
          ∀ w1 ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
            (E_SY_p4 (vecmatsV3_p4 l)), w1 ≠ vecmatsV3_p4 l (w6bcs_prev i) →
            azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i)) w ≤
              azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i)) w1)
    ⟨vecmatsV3_p4 l (finNext i), hwit⟩
  have hm3 : (Classical.epsilon (fun w : V3 => w ∈ Fan.setOfEdge (vecmatsV3_p4 l i)
        (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) ∧
          w ≠ vecmatsV3_p4 l (w6bcs_prev i) ∧
          ∀ w1 ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
            (E_SY_p4 (vecmatsV3_p4 l)), w1 ≠ vecmatsV3_p4 l (w6bcs_prev i) →
            azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i)) w ≤
              azim 0 (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i)) w1))
      ∈ ({vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)} : Set V3) := by
    rw [← hsoe i]; exact hm1
  rcases Set.mem_insert_iff.mp hm3 with h | h
  · exact absurd h hm2
  · exact Set.mem_singleton_iff.mp h

theorem w6bcs_azimInFan_gen {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hk1 : 1 < k)
    (hinj : ∀ i j : Fin k, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (j : Fin k)
    (hne : vecmatsV3_p4 l (w6bcs_prev j) ≠ vecmatsV3_p4 l (finNext j)) :
    azimInFan_p4 (vecmatsV3_p4 l j, vecmatsV3_p4 l (finNext j))
        (E_SY_p4 (vecmatsV3_p4 l))
      = azim 0 (vecmatsV3_p4 l j) (vecmatsV3_p4 l (finNext j))
          (vecmatsV3_p4 l (w6bcs_prev j)) := by
  have hsoe := w6bcs_setOfEdge_eq l hk1 hinj j
  have hncard : (1:ℕ) < (EE_p4 (vecmatsV3_p4 l j) (E_SY_p4 (vecmatsV3_p4 l))).ncard := by
    rw [w6bcs_ee_eq_setOfEdge hfan, hsoe]
    have hnc := Set.ncard_pair (a := vecmatsV3_p4 l (w6bcs_prev j))
      (b := vecmatsV3_p4 l (finNext j)) hne
    omega
  rw [azimInFan_p4, if_pos hncard]
  show azim 0 (vecmatsV3_p4 l j) (vecmatsV3_p4 l (finNext j))
      (azimCycle_p4 (EE_p4 (vecmatsV3_p4 l j) (E_SY_p4 (vecmatsV3_p4 l))) 0
        (vecmatsV3_p4 l j) (vecmatsV3_p4 l (finNext j)))
    = azim 0 (vecmatsV3_p4 l j) (vecmatsV3_p4 l (finNext j))
        (vecmatsV3_p4 l (w6bcs_prev j))
  have h := AZIM_CYCLE_EQ1 (l := l) hfan hk1 hinj (w6bcs_prev j)
    (u := vecmatsV3_p4 l (w6bcs_prev j)) (v := vecmatsV3_p4 l j)
    (w := vecmatsV3_p4 l (finNext j)) rfl (by rw [w6bcs_finNext_prev])
    (by rw [w6bcs_finNext_prev])
  rw [h]



/-! ## w6b chunk B: extensionSigma, inverseSigma, f/n-fan-pair steps, iterates -/

/-- `extensionSigmaFan` at vertex `l i` swaps the two neighbors
(`l (finNext i) ↦ l (prev i)`). -/
theorem w6bcs_extSigma_next {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i)) = vecmatsV3_p4 l (w6bcs_prev i) := by
  rw [Fan.extensionSigmaFan, if_neg (by
    intro hnc
    exact hnc (by
      rw [hsoe i]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl)))]
  exact w6bcs_sigma_next l hsoe hne i

/-- `extensionSigmaFan` at vertex `l i` swaps the two neighbors
(`l (prev i) ↦ l (finNext i)`). -/
theorem w6bcs_extSigma_prev {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i)) = vecmatsV3_p4 l (finNext i) := by
  rw [Fan.extensionSigmaFan, if_neg (by
    intro hnc
    exact hnc (by
      rw [hsoe i]
      exact Set.mem_insert _ _))]
  exact w6bcs_sigma_prev l hsoe hne i

theorem w6bcs_extSigma_notmem {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (i : Fin k) {w : V3} (hw : w ∉ Fan.setOfEdge (vecmatsV3_p4 l i)
      (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) :
    Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (vecmatsV3_p4 l i) w = w := by
  rw [Fan.extensionSigmaFan, if_pos hw]

/-- `extensionSigmaFan` at an `E_SY` vertex is injective. -/
theorem w6bcs_extSigma_injective {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Function.Injective (Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) (vecmatsV3_p4 l i)) := by
  intro x y hxy
  by_cases hx : x ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
  · rw [hsoe i] at hx
    rcases Set.mem_insert_iff.mp hx with hx1 | hx1
    · by_cases hy : y ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      · rw [hsoe i] at hy
        rcases Set.mem_insert_iff.mp hy with hy1 | hy1
        · exact hx1.trans hy1.symm
        · rw [Set.mem_singleton_iff] at hy1
          rw [hx1, hy1, w6bcs_extSigma_prev l hsoe hne i, w6bcs_extSigma_next l hsoe hne i] at hxy
          exact absurd hxy.symm (hne i)
      · rw [hx1, w6bcs_extSigma_prev l hsoe hne i, w6bcs_extSigma_notmem l hsoe i hy] at hxy
        rw [← hxy] at hy
        exact absurd (by
          rw [hsoe i]
          exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl)) hy
    · rw [Set.mem_singleton_iff] at hx1
      by_cases hy : y ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      · rw [hsoe i] at hy
        rcases Set.mem_insert_iff.mp hy with hy1 | hy1
        · rw [hx1, hy1, w6bcs_extSigma_next l hsoe hne i, w6bcs_extSigma_prev l hsoe hne i] at hxy
          exact absurd hxy (hne i)
        · exact hx1.trans hy1.symm
      · rw [hx1, w6bcs_extSigma_next l hsoe hne i, w6bcs_extSigma_notmem l hsoe i hy] at hxy
        rw [← hxy] at hy
        exact absurd (by
          rw [hsoe i]
          exact Set.mem_insert _ _) hy
  · by_cases hy : y ∈ Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
    · rw [hsoe i] at hy
      rcases Set.mem_insert_iff.mp hy with hy1 | hy1
      · rw [hy1, w6bcs_extSigma_prev l hsoe hne i, w6bcs_extSigma_notmem l hsoe i hx] at hxy
        rw [hxy] at hx
        exact absurd (by
          rw [hsoe i]
          exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl)) hx
      · rw [Set.mem_singleton_iff] at hy1
        rw [hy1, w6bcs_extSigma_next l hsoe hne i, w6bcs_extSigma_notmem l hsoe i hx] at hxy
        rw [hxy] at hx
        exact absurd (by
          rw [hsoe i]
          exact Set.mem_insert _ _) hx
    · rw [w6bcs_extSigma_notmem l hsoe i hx, w6bcs_extSigma_notmem l hsoe i hy] at hxy
      exact hxy

/-- inverse of the neighbor swap at vertex `l (finNext i)`, applied to
`l i`: gives `l (finNext (finNext i))` (HOL `FF_OF_HYP_EQ` station). -/
theorem w6bcs_invSigma_next {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Fan.inverseSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (vecmatsV3_p4 l (finNext i)) (vecmatsV3_p4 l i)
      = vecmatsV3_p4 l (finNext (finNext i)) := by
  have hg : ∀ a b : V3, Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) (vecmatsV3_p4 l (finNext i)) a =
      Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (vecmatsV3_p4 l (finNext i)) b → a = b :=
    w6bcs_extSigma_injective l hsoe hne (finNext i)
  have hcomp : Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (vecmatsV3_p4 l (finNext i)) (vecmatsV3_p4 l (finNext (finNext i)))
      = vecmatsV3_p4 l i := by
    rw [w6bcs_extSigma_next l hsoe hne (finNext i), w6bcs_prev_finNext]
  have hgt : Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (vecmatsV3_p4 l (finNext i))
      (Function.invFun (Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l))
          (E_SY_p4 (vecmatsV3_p4 l)) (vecmatsV3_p4 l (finNext i))) (vecmatsV3_p4 l i))
      = vecmatsV3_p4 l i :=
    Function.invFun_eq ⟨vecmatsV3_p4 l (finNext (finNext i)), hcomp⟩
  show Function.invFun (Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) (vecmatsV3_p4 l (finNext i))) (vecmatsV3_p4 l i)
    = vecmatsV3_p4 l (finNext (finNext i))
  exact (hg _ _ (hgt.trans hcomp.symm))

/-- inverse of the neighbor swap at vertex `l i`, applied to
`l (finNext i)`: gives `l (prev i)`. -/
theorem w6bcs_invSigma_prev {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Fan.inverseSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i))
      = vecmatsV3_p4 l (w6bcs_prev i) := by
  have hg : ∀ a b : V3, Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) (vecmatsV3_p4 l i) a =
      Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (vecmatsV3_p4 l i) b → a = b :=
    w6bcs_extSigma_injective l hsoe hne i
  have hcomp : Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (vecmatsV3_p4 l i) (vecmatsV3_p4 l (w6bcs_prev i)) = vecmatsV3_p4 l (finNext i) :=
    w6bcs_extSigma_prev l hsoe hne i
  have hgt : Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (vecmatsV3_p4 l i)
      (Function.invFun (Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l))
          (E_SY_p4 (vecmatsV3_p4 l)) (vecmatsV3_p4 l i)) (vecmatsV3_p4 l (finNext i)))
      = vecmatsV3_p4 l (finNext i) :=
    Function.invFun_eq ⟨vecmatsV3_p4 l (w6bcs_prev i), hcomp⟩
  show Function.invFun (Fan.extensionSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) (vecmatsV3_p4 l i)) (vecmatsV3_p4 l (finNext i))
    = vecmatsV3_p4 l (w6bcs_prev i)
  exact (hg _ _ (hgt.trans hcomp.symm))

/-- face step on a forward dart: `(u i, u i+1) ↦ (u i+1, u i+2)` -/
theorem w6bcs_fFanPair_next {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Fan.fFanPair 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i))
      = (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l (finNext (finNext i))) := by
  show (vecmatsV3_p4 l (finNext i),
      Fan.inverseSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (vecmatsV3_p4 l (finNext i)) (vecmatsV3_p4 l i))
    = (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l (finNext (finNext i)))
  rw [w6bcs_invSigma_next l hsoe hne i]

/-- face step on a reverse dart: `(u i+1, u i) ↦ (u i, u i-1)` -/
theorem w6bcs_fFanPair_prev {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Fan.fFanPair 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)
      = (vecmatsV3_p4 l i, vecmatsV3_p4 l (w6bcs_prev i)) := by
  show (vecmatsV3_p4 l i,
      Fan.inverseSigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i)))
    = (vecmatsV3_p4 l i, vecmatsV3_p4 l (w6bcs_prev i))
  rw [w6bcs_invSigma_prev l hsoe hne i]

/-- node step on a forward dart: `(u i, u i+1) ↦ (u i, u i-1)` -/
theorem w6bcs_nFanPair_next {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Fan.nFanPair 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i))
      = (vecmatsV3_p4 l i, vecmatsV3_p4 l (w6bcs_prev i)) := by
  show (vecmatsV3_p4 l i, Fan.sigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) (vecmatsV3_p4 l i) (vecmatsV3_p4 l (finNext i)))
    = (vecmatsV3_p4 l i, vecmatsV3_p4 l (w6bcs_prev i))
  rw [w6bcs_sigma_next l hsoe hne i]

/-- node step on a reverse dart: `(u i+1, u i) ↦ (u i+1, u i+2)` -/
theorem w6bcs_nFanPair_prev {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    Fan.nFanPair 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)
      = (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l (finNext (finNext i))) := by
  show (vecmatsV3_p4 l (finNext i), Fan.sigmaFan 0 (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) (vecmatsV3_p4 l (finNext i)) (vecmatsV3_p4 l i))
    = (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l (finNext (finNext i)))
  have h := w6bcs_sigma_prev l hsoe hne (finNext i)
  rw [w6bcs_prev_finNext] at h
  rw [h]

/-- `finNext` iterate in explicit mod form. -/
theorem w6bcs_finNext_iterate {k : ℕ} (n : ℕ) (i : Fin k) :
    finNext^[n] i = ⟨(i.val + n) % k,
      Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ := by
  induction n with
  | zero =>
    refine Fin.ext ?_
    show (finNext^[0] i).val = (i.val + 0) % k
    rw [Function.iterate_zero_apply, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    refine Fin.ext ?_
    show (((i.val + m) % k + 1) % k) = ((i.val + (m + 1)) % k)
    rw [Nat.mod_add_mod, Nat.add_assoc]




/-! ### w6b S-I: dart set, face orbits, cardinalities, orders, dih2k -/

theorem w6bcs_darts_coe {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E) :
    ((Fan.hypermapOfFan 0 V E hfan).darts : Set (V3 × V3)) = Fan.dart1OfFan V E := by
  have hD := Fan.finite_dart1_fan hfan
  simpa [Fan.hypermapOfFan] using hD.coe_toFinset

theorem w6bcs_faceMap_apply {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E)
    (d : V3 × V3) (hd : d ∈ Fan.dart1OfFan V E) :
    (Fan.hypermapOfFan 0 V E hfan).faceMap d = Fan.fFanPair 0 V E d := by
  have hmem : d ∈ (((Fan.finite_dart1_fan hfan).toFinset : Finset (V3 × V3)) : Set (V3 × V3)) := by
    rw [Set.Finite.coe_toFinset]; exact hd
  simp only [Fan.hypermapOfFan, Fan.extendPerm, Equiv.ofBijective_apply, Fan.res, hmem,
    if_true]

theorem w6bcs_edgeMap_apply {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E)
    (d : V3 × V3) (hd : d ∈ Fan.dart1OfFan V E) :
    (Fan.hypermapOfFan 0 V E hfan).edgeMap d = (d.2, d.1) := by
  have hmem : d ∈ (((Fan.finite_dart1_fan hfan).toFinset : Finset (V3 × V3)) : Set (V3 × V3)) := by
    rw [Set.Finite.coe_toFinset]; exact hd
  simp only [Fan.hypermapOfFan, Fan.extendPerm, Equiv.ofBijective_apply, Fan.res, hmem,
    if_true]
  rfl

theorem w6bcs_nodeMap_apply {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E)
    (d : V3 × V3) (hd : d ∈ Fan.dart1OfFan V E) :
    (Fan.hypermapOfFan 0 V E hfan).nodeMap d = Fan.nFanPair 0 V E d := by
  have hmem : d ∈ (((Fan.finite_dart1_fan hfan).toFinset : Finset (V3 × V3)) : Set (V3 × V3)) := by
    rw [Set.Finite.coe_toFinset]; exact hd
  simp only [Fan.hypermapOfFan, Fan.extendPerm, Equiv.ofBijective_apply, Fan.res, hmem,
    if_true]

theorem w6bcs_map_apply_out {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E)
    (d : V3 × V3) (hd : d ∉ Fan.dart1OfFan V E) :
    (Fan.hypermapOfFan 0 V E hfan).faceMap d = d ∧
      (Fan.hypermapOfFan 0 V E hfan).edgeMap d = d ∧
      (Fan.hypermapOfFan 0 V E hfan).nodeMap d = d := by
  have hnc : d ∉ (((Fan.finite_dart1_fan hfan).toFinset : Finset (V3 × V3)) : Set (V3 × V3)) := by
    rw [Set.Finite.coe_toFinset]; exact hd
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Fan.hypermapOfFan, Fan.extendPerm, Equiv.ofBijective_apply, Fan.res, hnc,
      if_false]

theorem w6bcs_faceMap_iterate_fwd {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (n : ℕ) (i : Fin k) :
    (Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).faceMap^[n]
        (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i))
      = (vecmatsV3_p4 l (finNext^[n] i), vecmatsV3_p4 l (finNext (finNext^[n] i))) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    have hidx : vecmatsV3_p4 l (finNext^[m] i) = vecmatsV3_p4 l (finNext^[m] i) := rfl
    rw [hidx]
    rw [w6bcs_faceMap_apply hfan
      (d := (vecmatsV3_p4 l (finNext^[m] i), vecmatsV3_p4 l (finNext (finNext^[m] i))))
      (by simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
          exact ⟨finNext^[m] i, Set.mem_univ _, rfl⟩)]
    rw [w6bcs_fFanPair_next l hsoe hne (finNext^[m] i), Function.iterate_succ_apply']

theorem w6bcs_prev_iterate {k : ℕ} (n : ℕ) (i : Fin k) :
    (w6bcs_prev)^[n] i = finNext^[n * (k - 1)] i := by
  have hprev : ∀ x : Fin k, finNext^[k - 1] x = w6bcs_prev x := by
    intro x
    rw [w6bcs_finNext_iterate]
    refine Fin.ext ?_
    show ((x.val + (k - 1)) % k) = ((x.val + k - 1) % k)
    exact congrArg (fun t : ℕ => t % k)
      (Nat.add_sub_assoc (by have hx := x.isLt; omega) x.val).symm
  rw [show (w6bcs_prev : Fin k → Fin k) = finNext^[k - 1] from
      funext fun x => (hprev x).symm,
    ← Function.iterate_mul, Nat.mul_comm]

/-- Cyclic reachability of the predecessor shift. -/
theorem w6bcs_prev_reach {k : ℕ} (i j : Fin k) :
    ∃ n : ℕ, (w6bcs_prev)^[n] j = i := by
  refine ⟨(j.val + k - i.val) % k, ?_⟩
  rw [w6bcs_prev_iterate, w6bcs_finNext_iterate]
  refine Fin.ext ?_
  show ((j.val + ((j.val + k - i.val) % k) * (k - 1)) % k) = i.val
  set n := (j.val + k - i.val) % k with hn
  have h1 : ((j.val + k - i.val) % k) ≡ (j.val + k - i.val) [MOD k] :=
    Nat.mod_modEq _ _
  have h2 : i.val + n ≡ i.val + (j.val + k - i.val) [MOD k] := Nat.ModEq.add_left _ h1
  have h3 : i.val + (j.val + k - i.val) = j.val + k := by omega
  have h4 : i.val + n ≡ j.val [MOD k] := by
    have hX : (i.val + (j.val + k - i.val)) ≡ j.val [MOD k] := by
      rw [h3]
      show ((j.val + k) % k) = (j.val % k)
      exact Nat.add_mod_right j.val k
    exact h2.trans hX
  have h6 : n * (k - 1) + n ≡ 0 [MOD k] := by
    show (n * (k - 1) + n) % k = (0 : ℕ) % k
    have hik := i.isLt
    have hjk := j.isLt
    have hnk : (n * (k - 1) + n : ℕ) = n * k := by
      have h1 := Nat.mul_add n (k - 1) 1
      rw [Nat.mul_one] at h1
      conv_rhs => rw [show ((k : ℕ)) = (k - 1) + 1 from by omega]
      exact h1.symm
    rw [hnk, Nat.mul_comm, Nat.mul_mod_right, Nat.zero_mod]
  have h7 : j.val + (n * (k - 1) + n) ≡ j.val [MOD k] := by
    have h7' := Nat.ModEq.add_left j.val h6
    rw [Nat.add_zero] at h7'
    exact h7'
  have h8 : i.val + n ≡ j.val + (n * (k - 1) + n) [MOD k] := h4.trans h7.symm
  have h9 : j.val + (n * (k - 1)) ≡ i.val [MOD k] := by
    have h8' : j.val + (n * (k - 1) + n) ≡ i.val + n [MOD k] := h8.symm
    rw [← Nat.add_assoc] at h8'
    exact Nat.ModEq.add_right_cancel' n h8'
  rw [← Nat.mod_eq_of_lt i.isLt]
  exact h9

theorem w6bcs_faceMap_iterate_rev {k : ℕ} (l : FinVec k 3)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (n : ℕ) (i : Fin k) :
    (Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).faceMap^[n]
        (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)
      = (vecmatsV3_p4 l (finNext ((w6bcs_prev)^[n] i)), vecmatsV3_p4 l ((w6bcs_prev)^[n] i)) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [w6bcs_faceMap_apply hfan
      (d := (vecmatsV3_p4 l (finNext ((w6bcs_prev)^[m] i)),
          vecmatsV3_p4 l ((w6bcs_prev)^[m] i)))
      (by simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
          have hpc : {vecmatsV3_p4 l (finNext ((w6bcs_prev)^[m] i)),
              vecmatsV3_p4 l ((w6bcs_prev)^[m] i)}
            = {vecmatsV3_p4 l ((w6bcs_prev)^[m] i),
                vecmatsV3_p4 l (finNext ((w6bcs_prev)^[m] i))} := Set.pair_comm _ _
          rw [hpc]
          exact ⟨(w6bcs_prev)^[m] i, Set.mem_univ _, rfl⟩)]
    rw [w6bcs_fFanPair_prev l hsoe hne ((w6bcs_prev)^[m] i), Function.iterate_succ_apply',
      w6bcs_finNext_prev]

#print axioms Kepler.Text.w6bcs_faceMap_iterate_rev


/-- Forward cyclic reachability. -/
theorem w6bcs_finNext_reach {k : ℕ} (i j : Fin k) :
    ∃ n : ℕ, finNext^[n] i = j := by
  refine ⟨(j.val + k - i.val) % k, ?_⟩
  rw [w6bcs_finNext_iterate]
  refine Fin.ext ?_
  show ((i.val + ((j.val + k - i.val) % k)) % k) = j.val
  have h1 : ((j.val + k - i.val) % k) ≡ (j.val + k - i.val) [MOD k] := Nat.mod_modEq _ _
  have h2 : i.val + ((j.val + k - i.val) % k) ≡ i.val + (j.val + k - i.val) [MOD k] :=
    Nat.ModEq.add_left _ h1
  have h3 : i.val + (j.val + k - i.val) = j.val + k := by omega
  have h4 : i.val + ((j.val + k - i.val) % k) ≡ j.val [MOD k] := by
    have hX : (i.val + (j.val + k - i.val)) ≡ j.val [MOD k] := by
      rw [h3]
      show ((j.val + k) % k) = (j.val % k)
      exact Nat.add_mod_right j.val k
    exact h2.trans hX
  conv_rhs => rw [← Nat.mod_eq_of_lt j.isLt]
  exact h4

/-- Under `FAN` the `_p4` hypermap is the importable `hypermapOfFan`. -/
theorem w6bcs_hyp_eq {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E) :
    hyp_p4 0 V E = Fan.hypermapOfFan 0 V E hfan := by
  unfold hyp_p4
  split
  · have hp : Fan.FAN 0 V E := ‹Fan.FAN 0 V E›
    exact congrArg _ (Subsingleton.elim hp hfan)
  · have hn : ¬Fan.FAN 0 V E := ‹¬Fan.FAN 0 V E›
    exact absurd hfan hn

/-- The face of the `F_SY` hypermap at any forward dart is all of `F_SY`
(HOL `F_SY_EQ_FACE` station; LA4's twin is a sorry giant, reproved here). -/
theorem w6bcs_face_fwd {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (i : Fin k) :
    face_p4 (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
        (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i))
      = F_SY_p4 (vecmatsV3_p4 l) := by
  rw [w6bcs_hyp_eq hfan]
  ext y
  constructor
  · rintro ⟨hmem, ⟨n, hn⟩⟩
    rw [w6bcs_faceMap_iterate_fwd l hsoe hne hfan n i] at hn
    subst hn
    exact ⟨finNext^[n] i, Set.mem_univ _, rfl⟩
  · rintro ⟨j, -, rfl⟩
    obtain ⟨n, hn⟩ := w6bcs_finNext_reach i j
    have hd : (vecmatsV3_p4 l j, vecmatsV3_p4 l (finNext j))
        ∈ ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).darts :
            Set (V3 × V3)) := by
      rw [w6bcs_darts_coe hfan]
      simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      exact ⟨j, Set.mem_univ _, rfl⟩
    have hit := w6bcs_faceMap_iterate_fwd l hsoe hne hfan n i
    rw [hn] at hit
    exact ⟨hd, n, hit⟩

/-- The face at any reverse dart is the reverse-dart set (HOL
`F_SY_EQ_FACE1` station). -/
theorem w6bcs_face_rev {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i))
    (j : Fin k) :
    face_p4 (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
        (vecmatsV3_p4 l (finNext j), vecmatsV3_p4 l j)
      = (fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ := by
  rw [w6bcs_hyp_eq hfan]
  ext y
  constructor
  · rintro ⟨hmem, ⟨n, hn⟩⟩
    rw [w6bcs_faceMap_iterate_rev l hsoe hne hfan n j] at hn
    subst hn
    exact ⟨(w6bcs_prev)^[n] j, Set.mem_univ _, rfl⟩
  · rintro ⟨i, -, rfl⟩
    obtain ⟨n, hn⟩ := w6bcs_prev_reach i j
    have hd : (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)
        ∈ ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).darts :
            Set (V3 × V3)) := by
      rw [w6bcs_darts_coe hfan]
      simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      rw [Set.pair_comm]
      exact ⟨i, Set.mem_univ _, rfl⟩
    have hit := w6bcs_faceMap_iterate_rev l hsoe hne hfan n j
    rw [hn] at hit
    exact ⟨hd, n, hit⟩

/-- `nodeMap` sends the forward darts onto the reverse darts. -/
theorem w6bcs_nodeMap_image_fwd {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i)) :
    (Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).nodeMap ''
        F_SY_p4 (vecmatsV3_p4 l)
      = (fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ := by
  ext y
  constructor
  · rintro ⟨d, hd, hnd⟩
    obtain ⟨i, -, rfl⟩ := hd
    have hd1 : (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i)) ∈ Fan.dart1OfFan
        (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
      simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      exact ⟨i, Set.mem_univ _, rfl⟩
    rw [w6bcs_nodeMap_apply hfan _ hd1, w6bcs_nFanPair_next l hsoe hne i] at hnd
    refine ⟨w6bcs_prev i, Set.mem_univ _, ?_⟩
    show (vecmatsV3_p4 l (finNext (w6bcs_prev i)), vecmatsV3_p4 l (w6bcs_prev i)) = y
    rw [w6bcs_finNext_prev]
    exact hnd
  · rintro ⟨i, -, rfl⟩
    refine ⟨(vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l (finNext (finNext i))),
      ⟨finNext i, Set.mem_univ _, rfl⟩, ?_⟩
    have hd1 : (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l (finNext (finNext i))) ∈ Fan.dart1OfFan
        (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
      simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      exact ⟨finNext i, Set.mem_univ _, rfl⟩
    dsimp only
    rw [w6bcs_nodeMap_apply hfan _ hd1, w6bcs_nFanPair_next l hsoe hne (finNext i),
      w6bcs_prev_finNext]

/-- `nodeMap` sends the reverse darts onto the forward darts. -/
theorem w6bcs_nodeMap_image_rev {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i)) :
    (Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).nodeMap ''
        ((fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ)
      = F_SY_p4 (vecmatsV3_p4 l) := by
  ext y
  constructor
  · rintro ⟨d, hd, hnd⟩
    obtain ⟨i, -, rfl⟩ := hd
    have hd1 : (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i) ∈ Fan.dart1OfFan
        (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
      simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      rw [Set.pair_comm]
      exact ⟨i, Set.mem_univ _, rfl⟩
    rw [w6bcs_nodeMap_apply hfan _ hd1, w6bcs_nFanPair_prev l hsoe hne i] at hnd
    exact ⟨finNext i, Set.mem_univ _, hnd⟩
  · rintro ⟨j, -, rfl⟩
    refine ⟨(vecmatsV3_p4 l (finNext (w6bcs_prev j)), vecmatsV3_p4 l (w6bcs_prev j)),
      ⟨w6bcs_prev j, Set.mem_univ _, rfl⟩, ?_⟩
    have hd1 : (vecmatsV3_p4 l (finNext (w6bcs_prev j)), vecmatsV3_p4 l (w6bcs_prev j))
        ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
      simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      show ({vecmatsV3_p4 l (finNext (w6bcs_prev j)), vecmatsV3_p4 l (w6bcs_prev j)} : Set V3)
          ∈ E_SY_p4 (vecmatsV3_p4 l)
      rw [Set.pair_comm]
      exact ⟨w6bcs_prev j, Set.mem_univ _, rfl⟩
    dsimp only
    rw [w6bcs_nodeMap_apply hfan _ hd1, w6bcs_nFanPair_prev l hsoe hne (w6bcs_prev j),
      w6bcs_finNext_prev]

/-- `dart1OfFan` splits into the forward and reverse `F_SY` darts. -/
theorem w6bcs_dart1_eq {k : ℕ} (l : FinVec k 3) (hk1 : 1 < k)
    (hinj : ∀ i j : Fin k, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      = F_SY_p4 (vecmatsV3_p4 l)
        ∪ ((fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ) := by
  ext d
  have hfinnextne : ∀ j : Fin k, finNext j ≠ j := by
    intro j hjj
    have hval : ((j.val + 1) % k) = j.val := congrArg Fin.val hjj
    rcases Nat.lt_or_ge (j.val + 1) k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hval
      omega
    · have hke : j.val + 1 = k := le_antisymm (by have := j.isLt; omega) hge
      rw [hke, Nat.mod_self] at hval
      have hij := j.isLt
      omega
  constructor
  · intro hd
    simp only [Fan.dart1OfFan, Set.mem_setOf_eq] at hd
    obtain ⟨j, -, hj⟩ := hd
    have hj' : ({vecmatsV3_p4 l j, vecmatsV3_p4 l (finNext j)} : Set V3) = {d.1, d.2} := hj
    have hd1 : d.1 ∈ ({d.1, d.2} : Set V3) := Set.mem_insert _ _
    have hd2 : d.2 ∈ ({d.1, d.2} : Set V3) := Set.mem_insert_of_mem _ rfl
    rw [← hj'] at hd1 hd2
    rcases Set.mem_insert_iff.mp hd1 with h1 | h1
    · rcases Set.mem_insert_iff.mp hd2 with h2 | h2
      · rw [h1, h2] at hj'
        have hsin : ({vecmatsV3_p4 l j, vecmatsV3_p4 l (finNext j)} : Set V3)
            ≠ {vecmatsV3_p4 l j, vecmatsV3_p4 l j} := by
          intro hcon
          have hm : vecmatsV3_p4 l (finNext j) ∈ ({vecmatsV3_p4 l j, vecmatsV3_p4 l j} : Set V3) := by
            rw [← hcon]
            exact Set.mem_insert_of_mem _ rfl
          rcases Set.mem_insert_iff.mp hm with hme | hme
          · exact hfinnextne j (hinj _ _ hme)
          · rw [Set.mem_singleton_iff] at hme
            exact hfinnextne j (hinj _ _ hme)
        exact absurd hj' hsin
      · exact Or.inl ⟨j, Set.mem_univ _, by
          show (vecmatsV3_p4 l j, vecmatsV3_p4 l (finNext j)) = (d.1, d.2)
          rw [h1, h2]⟩
    · rcases Set.mem_insert_iff.mp hd2 with h2 | h2
      · exact Or.inr ⟨j, Set.mem_univ _, by
          show (vecmatsV3_p4 l (finNext j), vecmatsV3_p4 l j) = (d.1, d.2)
          rw [h1, h2]⟩
      · rw [h1, h2] at hj'
        have hsin : ({vecmatsV3_p4 l j, vecmatsV3_p4 l (finNext j)} : Set V3)
            ≠ {vecmatsV3_p4 l (finNext j), vecmatsV3_p4 l (finNext j)} := by
          intro hcon
          have hm : vecmatsV3_p4 l j ∈ ({vecmatsV3_p4 l (finNext j), vecmatsV3_p4 l (finNext j)} : Set V3) := by
            rw [← hcon]
            exact Set.mem_insert _ _
          rcases Set.mem_insert_iff.mp hm with hme | hme
          · exact hfinnextne j (hinj _ _ hme.symm)
          · exact hfinnextne j (hinj _ _ hme.symm)
        exact absurd hj' hsin
  · rintro (⟨j, -, rfl⟩ | ⟨j, -, rfl⟩)
    · simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      exact ⟨j, Set.mem_univ _, rfl⟩
    · simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      rw [Set.pair_comm]
      exact ⟨j, Set.mem_univ _, rfl⟩


/-- Set-level dart membership through the `hypermapOfFan` coe. -/
theorem w6bcs_darts_mem {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E)
    {x : V3 × V3} (hx : x ∈ Fan.dart1OfFan V E) :
    x ∈ ((Fan.hypermapOfFan 0 V E hfan).darts : Set (V3 × V3)) := by
  exact w6bcs_darts_coe hfan ▸ hx

/-- `↑darts = F_SY ⊔ reverse-F_SY`. -/
theorem w6bcs_darts_eq {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hk2 : 2 < k) (hinj : ∀ i j : Fin k, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).darts :
        Set (V3 × V3))
      = F_SY_p4 (vecmatsV3_p4 l)
        ∪ ((fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ) := by
  rw [w6bcs_darts_coe hfan]
  exact w6bcs_dart1_eq l (by omega) hinj



end W6bKit

/-! ## Section W6cKit (bodyclosed-w6c): 缺口 2 点态平面退化反驳
(w6ccs_false_of_planar_inter, W5b §4 钉形 + hdiff 修正, W6a §3 陈述逐字).
坐标抽取 (正交补维数路线) + D-恒等式符号树五支收口 + 4ponits/same-ray 杀.
零新 import; 零 sorry; 六件 (四 private + 两公开面其中缺口 2 公开).
-/

section W6cKit

/-- 坐标抽取：`w` 与 `(y×z)` 正交（即落在平面 `span{y,z}` 内）时给出
`(y,z)`-坐标分解。正交补维数路线：`finrank_orthogonal_span_singleton` +
`Submodule.eq_of_le_of_finrank_eq`。 -/
private theorem w6ccs_coords_of_planar_dot {y z w : V3}
    (hnc : ¬ Collinear3 (0:V3) y z) (hy0 : y ≠ 0)
    (hpl : (crossProduct (WithLp.ofLp y : Fin 3 → ℝ) (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp w : Fin 3 → ℝ) = 0) :
    ∃ p q : ℝ, w = p • y + q • z := by
  set n : V3 := WithLp.toLp 2 (crossProduct (WithLp.ofLp y : Fin 3 → ℝ)
    (WithLp.ofLp z : Fin 3 → ℝ)) with hndef
  have hLI : LinearIndependent ℝ ![y, z] := by
    rw [LinearIndependent.pair_iff' hy0]
    intro a hae
    refine hnc (w5bcs_collinear_of_eq_zero (α := -a) one_pos ?_)
    rw [← hae]
    module
  have hn0 : n ≠ 0 := by
    intro h0
    have hc : crossProduct (WithLp.ofLp y : Fin 3 → ℝ) (WithLp.ofLp z : Fin 3 → ℝ) = 0 := by
      have hco : (WithLp.ofLp n : Fin 3 → ℝ) = crossProduct (WithLp.ofLp y : Fin 3 → ℝ)
        (WithLp.ofLp z : Fin 3 → ℝ) := rfl
      rw [← hco, h0]
      simp
    have hy0pi : WithLp.ofLp y ≠ 0 := by
      intro he
      refine hy0 ?_
      rw [show y = WithLp.toLp 2 (WithLp.ofLp y) from rfl, he]
      simp
    have hnl : ¬ LinearIndependent ℝ ![WithLp.ofLp y, WithLp.ofLp z] :=
      fun hli => (crossProduct_ne_zero_iff_linearIndependent.mpr hli) hc
    rw [LinearIndependent.pair_iff' hy0pi] at hnl
    push Not at hnl
    obtain ⟨a, hae⟩ := hnl
    refine hnc (w5bcs_collinear_of_eq_zero (α := -a) one_pos ?_)
    have hae3 : a • y = z :=
      congrArg (WithLp.toLp 2) hae
    rw [← hae3]
    module
  have hny : inner ℝ n y = 0 := by
    rw [inner_eq_dot, dot_toLp, dotProduct_comm]
    exact dot_self_cross (WithLp.ofLp y) (WithLp.ofLp z)
  have hnz : inner ℝ n z = 0 := by
    rw [inner_eq_dot, dot_toLp, dotProduct_comm]
    exact dot_cross_self (WithLp.ofLp y) (WithLp.ofLp z)
  have hnw : inner ℝ n w = 0 := by
    rw [inner_eq_dot, dot_toLp]
    exact hpl
  haveI : Fact (Module.finrank ℝ V3 = 2 + 1) := ⟨by simp⟩
  have hK2 : Module.finrank ℝ (Submodule.span ℝ ({y, z} : Set V3)) = 2 := by
    rw [show (Submodule.span ℝ ({y, z} : Set V3)) = Submodule.span ℝ
      (Set.range ![y, z]) from by
        congr 1
        ext u
        constructor
        · rintro (rfl | rfl)
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
        · rintro ⟨i, hi⟩
          fin_cases i <;> simp at hi <;> rw [hi] <;> simp, finrank_span_eq_card hLI]
    rw [Fintype.card_fin]
  have hQle : Submodule.span ℝ ({y, z} : Set V3) ≤ (ℝ ∙ n)ᗮ := by
    rw [Submodule.span_le]
    rintro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | rfl
    · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hny
    · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hnz
  have hfQ : Module.finrank ℝ ((ℝ ∙ n)ᗮ) = 2 :=
    Submodule.finrank_orthogonal_span_singleton (n := 2) hn0
  have hKQ : Submodule.span ℝ ({y, z} : Set V3) = (ℝ ∙ n)ᗮ :=
    Submodule.eq_of_le_of_finrank_eq hQle (hK2.trans hfQ.symm)
  have hwQ : w ∈ (ℝ ∙ n)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hnw
  rw [← hKQ] at hwQ
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hwQ
  exact ⟨p, q, hpq.symm⟩

/-- 纯实数符号树：α,β,γ,δ > 0、α = γp + δr、β = γq + δs、D = ps − rq > 0
五支收口。 -/
private theorem w6ccs_planar_sign_aux {p q r s α β γ δ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (he1 : α = γ * p + δ * r) (he2 : β = γ * q + δ * s)
    (hD : 0 < p * s - r * q) :
    (0 < s ∧ q < 0) ∨ (r < 0 ∧ 0 < p) ∨ (0 < p ∧ 0 < q) ∨ (0 < r ∧ 0 < s) ∨
      (q = 0 ∧ r = 0) := by
  by_cases hp : 0 < p
  · -- p > 0
    by_cases hqp : 0 < q
    · -- q > 0 → 支3
      exact Or.inr (Or.inr (Or.inl (show 0 < p ∧ 0 < q from ⟨hp, hqp⟩)))
    · have hqle : q ≤ 0 := le_of_not_gt hqp
      rcases eq_or_ne q 0 with hq0 | hqneg
      · -- q = 0：β = δs > 0 ⟹ s > 0；r<0 → 支2、r>0 → 支4、r=0 → 支5
        rw [hq0, mul_zero, zero_add] at he2
        have hds : (0:ℝ) < δ * s := by rw [← he2]; exact hβ
        have hs : 0 < s :=
          lt_of_mul_lt_mul_left (by rw [mul_zero]; exact hds : δ * (0:ℝ) < δ * s) hδ.le
        by_cases hr1 : r < 0
        · exact Or.inr (Or.inl (show r < 0 ∧ 0 < p from ⟨hr1, hp⟩))
        · have hrge : (0:ℝ) ≤ r := le_of_not_gt hr1
          rcases eq_or_ne r 0 with hr0 | hrne
          · exact Or.inr (Or.inr (Or.inr (Or.inr (show q = 0 ∧ r = 0 from ⟨hq0, hr0⟩))))
          · have hrpos : 0 < r := lt_of_le_of_ne hrge (fun he => hrne he.symm)
            exact Or.inr (Or.inr (Or.inr (Or.inl (And.intro hrpos hs))))
      · -- q < 0 → 支1（β > 0 ⟹ s > 0）
        have hq1 : q < 0 := lt_of_le_of_ne hqle hqneg
        have hγq : γ * q < 0 := by nlinarith [hγ, hq1]
        have hdt : (0:ℝ) < δ * s := by rw [he2] at hβ; linarith
        have hs : 0 < s :=
          lt_of_mul_lt_mul_left (by rw [mul_zero]; exact hdt : δ * (0:ℝ) < δ * s) hδ.le
        exact Or.inl (And.intro hs hq1)
  · -- p ≤ 0
    rcases eq_or_ne p 0 with hp0 | hpne
    · -- p = 0：he1 ⟹ r > 0；D = −rq > 0 ⟹ q < 0；β > 0 ⟹ s > 0 → 支4
      rw [hp0, mul_zero, zero_add] at he1
      have hdr : (0:ℝ) < δ * r := by rw [← he1]; exact hα
      have hr : (0:ℝ) < r :=
        lt_of_mul_lt_mul_left (by rw [mul_zero]; exact hdr : δ * (0:ℝ) < δ * r) hδ.le
      have hrq : r * q < 0 := by
        rw [hp0, zero_mul, zero_sub] at hD
        linarith
      have hqneg : q < 0 := by
        by_cases h1 : q < 0
        · exact h1
        · have h2 : (0:ℝ) ≤ q := le_of_not_gt h1
          have h3 : (0:ℝ) ≤ r * q := by nlinarith [hr.le, h2]
          linarith
      have hγq : γ * q < 0 := by nlinarith [hγ, hqneg]
      have hdt : (0:ℝ) < δ * s := by rw [he2] at hβ; linarith
      have hs : 0 < s :=
        lt_of_mul_lt_mul_left (by rw [mul_zero]; exact hdt : δ * (0:ℝ) < δ * s) hδ.le
      exact Or.inr (Or.inr (Or.inr (Or.inl (And.intro hr hs))))
    · -- p < 0
      have hpneg : p < 0 := lt_of_le_of_ne (le_of_not_gt hp) hpne
      have hpr : (0:ℝ) < r := by
        by_cases hr0 : 0 < r
        · exact hr0
        · have hrle : r ≤ 0 := le_of_not_gt hr0
          have h1 : γ * p < 0 := by nlinarith [hγ, hpneg]
          have h2 : δ * r ≤ 0 := by nlinarith [hrle, hδ.le]
          rw [he1] at hα
          linarith
      by_cases hs1 : 0 < s
      · exact Or.inr (Or.inr (Or.inr (Or.inl (And.intro hpr hs1))))
      · have hsle : s ≤ 0 := le_of_not_gt hs1
        rcases eq_or_ne s 0 with hs0 | hsne
        · -- s = 0：β = γq > 0 ⟹ q > 0 ⟹ D = −rq < 0 矛盾
          have hqp : (0:ℝ) < q := by
            rw [hs0, mul_zero, add_zero] at he2
            by_contra hc
            have hqle : q ≤ 0 := le_of_not_gt hc
            have hγq : γ * q ≤ 0 := by nlinarith [hγ.le, hqle]
            rw [he2] at hβ
            linarith
          have hrq : (0:ℝ) < r * q := by nlinarith [hpr, hqp]
          rw [hs0, mul_zero, zero_sub] at hD
          linarith
        · -- s < 0：β > 0 ⟹ q > 0；乘积矛盾 rq > ps
          have hsn : s < 0 := lt_of_le_of_ne hsle hsne
          have hqp : (0:ℝ) < q := by
            by_contra hc
            have hqle : q ≤ 0 := le_of_not_gt hc
            have h1 : γ * q ≤ 0 := by nlinarith [hγ.le, hqle]
            have h2 : δ * s < 0 := by nlinarith [hδ, hsn]
            rw [he2] at hβ
            linarith
          have e1 : -(γ * p) < δ * r := by
            have := he1
            linarith
          have e2 : -(δ * s) < γ * q := by
            have := he2
            linarith
          have b1 : (0:ℝ) < -(γ * p) := by nlinarith [hγ, hpneg]
          have b2 : (0:ℝ) < -(δ * s) := by nlinarith [hδ, hsn]
          have gq : (0:ℝ) < γ * q := mul_pos hγ (by linarith)
          have s2 : (δ * r) * (γ * q) > (-(γ * p)) * (γ * q) :=
            mul_lt_mul_of_pos_right e1 gq
          have s1 : (-(γ * p)) * (γ * q) > (-(γ * p)) * (-(δ * s)) :=
            mul_lt_mul_of_pos_left e2 b1
          have hprod : (δ * r) * (γ * q) > (-(γ * p)) * (-(δ * s)) := gt_trans s2 s1
          have hc1 : (δ * r) * (γ * q) = (γ * δ) * (r * q) := by ring
          have hc2 : (-(γ * p)) * (-(δ * s)) = (γ * δ) * (p * s) := by ring
          have hgd : (0:ℝ) < γ * δ := mul_pos hγ hδ
          have hrq : r * q > p * s := by
            rw [hc1, hc2] at hprod
            exact lt_of_mul_lt_mul_left hprod hgd.le
          linarith

/-- 系数非零 ⟹ 点不与第一基点重合。 -/
private theorem w6ccs_ne_of_coeff {y z w : V3} (hy : y ≠ 0) (hz : z ≠ 0)
    (hnc : ¬ Collinear3 (0:V3) y z) {t s : ℝ} (hw : w = t • y + s • z) (hs : s ≠ 0) : w ≠ y := by
  intro he
  rw [he] at hw
  have h6 : ((1 - t) • y + (-s) • z : V3) = y - (t • y + s • z) := by module
  have h7 : (1 - t) • y + (-s) • z = 0 := by rw [h6, ← hw, sub_self]
  obtain ⟨e1, e2⟩ := w6acs_smul_indep hy hz hnc h7
  exact hs (neg_eq_zero.mp e2)

/-- 第一系数非零 ⟹ 点不与第二基点重合。 -/
private theorem w6ccs_ne_of_coeff' {y z w : V3} (hy : y ≠ 0) (hz : z ≠ 0)
    (hnc : ¬ Collinear3 (0:V3) y z) {t s : ℝ} (hw : w = t • y + s • z) (ht : t ≠ 0) : w ≠ z := by
  intro he
  rw [he] at hw
  have h6 : (t • y + (s - 1) • z : V3) = (t • y + s • z) - z := by module
  have h7 : t • y + (s - 1) • z = 0 := by rw [h6, ← hw, sub_self]
  obtain ⟨e1, e2⟩ := w6acs_smul_indep hy hz hnc h7
  exact ht e1

/-- D > 0 情形的五支杀（消费 `w6ccs_planar_sign_aux`）。 -/
private theorem w6ccs_planar_kill_pos {y z y1 z1 x : V3}
    {p q r s α β γ δ : ℝ}
    (hy1c : y1 = p • y + q • z) (hz1c : z1 = r • y + s • z)
    (hx1e : x = α • y + β • z) (hx2e : x = γ • y1 + δ • z1)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hyz : y ≠ z) (hy0 : y ≠ 0) (hz0 : z ≠ 0)
    (hy1z1 : y1 ≠ z1) (hy10 : y1 ≠ 0) (hz10 : z1 ≠ 0)
    (hy : y ∈ ballAnnulus) (hz : z ∈ ballAnnulus) (hy1 : y1 ∈ ballAnnulus)
    (hz1 : z1 ∈ ballAnnulus)
    (hnc1 : ¬ Collinear3 (0:V3) y z) (hnc2 : ¬ Collinear3 (0:V3) y1 z1)
    (hadj1 : ‖y - z‖ ≤ cstab_p4) (hadj2 : ‖y1 - z1‖ ≤ cstab_p4)
    (hdiff : ¬ (y1 ∈ ({y, z} : Set V3) ∧ z1 ∈ ({y, z} : Set V3)))
    (hsep : ∀ v w : V3, v ≠ w → v ∈ ({y, z, y1, z1} : Set V3) →
      w ∈ ({y, z, y1, z1} : Set V3) → (2:ℝ) ≤ ‖v - w‖)
    (hD : 0 < p * s - r * q) : False := by
  have hDne : p * s - r * q ≠ 0 := ne_of_gt hD
  -- 两组系数的协调（坐标唯一性）
  have hcollect : (γ * p + δ * r) • y + (γ * q + δ * s) • z = γ • y1 + δ • z1 := by
    rw [hy1c, hz1c]; module
  have hxeq : α • y + β • z = γ • y1 + δ • z1 := by rw [← hx1e, ← hx2e]
  have hdep : (γ * p + δ * r - α) • y + (γ * q + δ * s - β) • z = 0 := by
    have h5 : (γ * p + δ * r) • y + (γ * q + δ * s) • z = α • y + β • z := by
      rw [hcollect, ← hxeq]
    have h6 : (γ * p + δ * r - α) • y + (γ * q + δ * s - β) • z
        = (γ * p + δ * r) • y + (γ * q + δ * s) • z - (α • y + β • z) := by module
    rw [h6, h5, sub_self]
  obtain ⟨e1, e2⟩ := w6acs_smul_indep hy0 hz0 hnc1 hdep
  have heq1 : α = γ * p + δ * r := by linarith
  have heq2 : β = γ * q + δ * s := by linarith
  rcases w6ccs_planar_sign_aux hα hβ hγ hδ heq1 heq2 hD with hsA | hsB | hsC | hsC' | hsE
  · -- 支A: 0 < s ∧ q < 0 → y ∈ gt(y1,z1)
    obtain ⟨hsp, hqn⟩ := hsA
    have hne1 : y1 ≠ y := w6ccs_ne_of_coeff hy0 hz0 hnc1 hy1c (ne_of_lt hqn)
    have hne2 : z1 ≠ y := w6ccs_ne_of_coeff hy0 hz0 hnc1 hz1c (ne_of_gt hsp)
    have hyE : y = (s / (p * s - r * q)) • y1 + (-q / (p * s - r * q)) • z1 := by
      rw [hy1c, hz1c]
      rw [show ((s / (p * s - r * q)) • (p • y + q • z) +
          (-q / (p * s - r * q)) • (r • y + s • z) : V3)
          = ((s * p + -q * r) / (p * s - r * q)) • y +
            ((s * q + -q * s) / (p * s - r * q)) • z from by module]
      rw [show ((s * q + -q * s : ℝ)) = 0 from by ring, zero_div, zero_smul, add_zero,
        show ((s * p + -q * r : ℝ)) = p * s - r * q from by ring, div_self hDne, one_smul]
    have hygt : y ∈ affGt ({0} : Set V3) ({y1, z1}) :=
      w4cs_mem_affGt_two hy1z1 hy10 hz10 hyE (div_pos hsp hD)
        (div_pos (by linarith : (0:ℝ) < -q) hD)
    exact w6acs_indep_gt_kill (v := y) hnc2 hy1 hz1 hy
      (hsep y1 z1 hy1z1 (by simp) (by simp)) hadj2
      (hsep y1 y hne1 (by simp) (by simp))
      (hsep z1 y hne2 (by simp) (by simp)) hygt
  · -- 支B: r < 0 ∧ 0 < p → z ∈ gt(y1,z1)
    obtain ⟨hrn, hpp⟩ := hsB
    have hne1 : y1 ≠ z := w6ccs_ne_of_coeff' hy0 hz0 hnc1 hy1c (ne_of_gt hpp)
    have hne2 : z1 ≠ z := w6ccs_ne_of_coeff' hy0 hz0 hnc1 hz1c (ne_of_lt hrn)
    have hzE : z = (-r / (p * s - r * q)) • y1 + (p / (p * s - r * q)) • z1 := by
      rw [hy1c, hz1c]
      rw [show ((-r / (p * s - r * q)) • (p • y + q • z) +
          (p / (p * s - r * q)) • (r • y + s • z) : V3)
          = ((-r * p + p * r) / (p * s - r * q)) • y +
            ((-r * q + p * s) / (p * s - r * q)) • z from by module]
      rw [show ((-r * p + p * r : ℝ)) = 0 from by ring, zero_div, zero_smul, zero_add,
        show ((-r * q + p * s : ℝ)) = p * s - r * q from by ring, div_self hDne, one_smul]
    have hzgt : z ∈ affGt ({0} : Set V3) ({y1, z1}) :=
      w4cs_mem_affGt_two hy1z1 hy10 hz10 hzE (div_pos (by linarith : (0:ℝ) < -r) hD)
        (div_pos hpp hD)
    exact w6acs_indep_gt_kill (v := z) hnc2 hy1 hz1 hz
      (hsep y1 z1 hy1z1 (by simp) (by simp)) hadj2
      (hsep y1 z hne1 (by simp) (by simp))
      (hsep z1 z hne2 (by simp) (by simp)) hzgt
  · -- 支C: 0 < p ∧ 0 < q → y1 ∈ gt(y,z)
    obtain ⟨hpp, hqp⟩ := hsC
    have hne1 : y1 ≠ y := w6ccs_ne_of_coeff hy0 hz0 hnc1 hy1c (ne_of_gt hqp)
    have hne2 : y1 ≠ z := w6ccs_ne_of_coeff' hy0 hz0 hnc1 hy1c (ne_of_gt hpp)
    have hygt : y1 ∈ affGt ({0} : Set V3) ({y, z}) :=
      w4cs_mem_affGt_two hyz hy0 hz0 hy1c hpp hqp
    exact w6acs_indep_gt_kill (v := y1) hnc1 hy hz hy1
      (hsep y z hyz (by simp) (by simp)) hadj1
      (hsep y y1 (fun he => hne1 he.symm) (by simp) (by simp))
      (hsep z y1 (fun he => hne2 he.symm) (by simp) (by simp)) hygt
  · -- 支C': 0 < r ∧ 0 < s → z1 ∈ gt(y,z)
    obtain ⟨hrp, hsp⟩ := hsC'
    have hne1 : z1 ≠ y := w6ccs_ne_of_coeff hy0 hz0 hnc1 hz1c (ne_of_gt hsp)
    have hne2 : z1 ≠ z := w6ccs_ne_of_coeff' hy0 hz0 hnc1 hz1c (ne_of_gt hrp)
    have hzgt : z1 ∈ affGt ({0} : Set V3) ({y, z}) :=
      w4cs_mem_affGt_two hyz hy0 hz0 hz1c hrp hsp
    exact w6acs_indep_gt_kill (v := z1) hnc1 hy hz hz1
      (hsep y z hyz (by simp) (by simp)) hadj1
      (hsep y z1 hne1.symm (by simp) (by simp))
      (hsep z z1 hne2.symm (by simp) (by simp)) hzgt
  · -- 支E: q = 0 ∧ r = 0 → y1 = p•y, z1 = s•z 同射线杀
    obtain ⟨hq0, hr0⟩ := hsE
    rw [hq0, zero_smul, add_zero] at hy1c
    rw [hr0, zero_smul, zero_add] at hz1c
    rw [hr0] at heq1
    rw [hq0] at heq2
    simp only [mul_zero, zero_add, add_zero] at heq1 heq2
    have hp0 : 0 < p := by
      by_contra hc
      have hcle : p ≤ 0 := le_of_not_gt hc
      have : γ * p ≤ 0 := by nlinarith [hγ.le, hcle]
      rw [heq1] at hα
      linarith
    have hs0 : 0 < s := by
      by_contra hc
      have hsle : s ≤ 0 := le_of_not_gt hc
      have : δ * s ≤ 0 := by nlinarith [hδ.le, hsle]
      rw [heq2] at hβ
      linarith
    rcases eq_or_ne y y1 with hye | hyne
    · -- y = y1：hdiff ⟹ z1 ≠ z ⟹ 同射线 (z, z1)
      have hz1z : z1 ≠ z := by
        intro he2
        refine hdiff ⟨?_, ?_⟩
        · rw [hye]; simp
        · rw [he2]; simp
      exact w6acs_same_ray_dist_lt2 (hsep z z1 hz1z.symm (by simp) (by simp)) hz hz1 hs0 hz1c
    · -- y ≠ y1：同射线 (y, y1)
      exact w6acs_same_ray_dist_lt2 (hsep y y1 hyne (by simp) (by simp)) hy hy1 hp0 hy1c

/-- 缺口 2：点态平面退化反驳（W5b §4 钉形 + hdiff 修正，W6a §3 陈述逐字）。 -/
theorem w6ccs_false_of_planar_inter {y z y1 z1 x : V3}
    (hnc1 : ¬ Collinear3 (0:V3) y z) (hnc2 : ¬ Collinear3 (0:V3) y1 z1)
    (hann : y ∈ ballAnnulus ∧ z ∈ ballAnnulus ∧ y1 ∈ ballAnnulus ∧ z1 ∈ ballAnnulus)
    (hadj1 : ‖y - z‖ ≤ cstab_p4) (hadj2 : ‖y1 - z1‖ ≤ cstab_p4)
    (hdiff : ¬ (y1 ∈ ({y, z} : Set V3) ∧ z1 ∈ ({y, z} : Set V3)))
    (hsep : ∀ v w : V3, v ≠ w → v ∈ ({y, z, y1, z1} : Set V3) →
      w ∈ ({y, z, y1, z1} : Set V3) → (2:ℝ) ≤ ‖v - w‖)
    (hpl1 : (crossProduct (WithLp.ofLp y : Fin 3 → ℝ) (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp y1 : Fin 3 → ℝ) = 0)
    (hpl2 : (crossProduct (WithLp.ofLp y : Fin 3 → ℝ) (WithLp.ofLp z : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp z1 : Fin 3 → ℝ) = 0)
    (hx1 : x ∈ affGt ({0} : Set V3) ({y, z} : Set V3))
    (hx2 : x ∈ affGt ({0} : Set V3) ({y1, z1} : Set V3)) : False := by
  obtain ⟨hy, hz, hy1, hz1⟩ := hann
  have hy0 : y ≠ 0 := w4cs_annulus_ne_zero hy
  have hz0 : z ≠ 0 := w4cs_annulus_ne_zero hz
  have hy10 : y1 ≠ 0 := w4cs_annulus_ne_zero hy1
  have hz10 : z1 ≠ 0 := w4cs_annulus_ne_zero hz1
  have hyz : y ≠ z := fun he => hnc1 (collinear3_pair_right he.symm)
  have hy1z1 : y1 ≠ z1 := fun he => hnc2 (collinear3_pair_right he.symm)
  obtain ⟨α, β, hα, hβ, hx1e⟩ := w5bcs_coeff_of_mem_affGt hy0 hz0 hx1
  obtain ⟨γ, δ, hγ, hδ, hx2e⟩ := w5bcs_coeff_of_mem_affGt hy10 hz10 hx2
  obtain ⟨p, q, hy1c⟩ := w6ccs_coords_of_planar_dot hnc1 hy0 hpl1
  obtain ⟨r, s, hz1c⟩ := w6ccs_coords_of_planar_dot hnc1 hy0 hpl2
  -- D = ps − rq ≠ 0（hnc2 反驳）
  have hDne : p * s - r * q ≠ 0 := by
    intro h0
    have hdep2 : s • y1 + (-q) • z1 = (p * s - r * q) • y := by
      rw [hy1c, hz1c]; module
    rw [h0, zero_smul] at hdep2
    by_cases h1 : 0 < -q
    · exact hnc2 (w5bcs_collinear_of_eq_zero h1 hdep2.symm)
    · have hnq : -q ≤ 0 := le_of_not_gt h1
      by_cases hq0 : q = 0
      · rw [hq0, neg_zero, zero_smul, add_zero] at hdep2
        rcases eq_or_ne s 0 with hs0 | hsne
        · -- s = 0: y1 = p•y, z1 = r•y, p,r ≠ 0 → 共线
          rw [hs0, zero_smul, add_zero] at hz1c
          rw [hq0, zero_smul, add_zero] at hy1c
          rcases eq_or_ne p 0 with hp00 | hpne0
          · rw [hp00, zero_smul] at hy1c; exact hy10 hy1c
          · rcases eq_or_ne r 0 with hr00 | hrne0
            · rw [hr00, zero_smul] at hz1c; exact hz10 hz1c
            · rcases lt_or_gt_of_ne hpne0 with hp0n | hp0p
              · -- p < 0: 0 = r • y1 + (-p) • z1
                refine hnc2 (w5bcs_collinear_of_eq_zero (α := r) (neg_pos.mpr hp0n) ?_)
                have h6 : (r • y1 + (-p) • z1 : V3) = (r • (p • y) + (-p) • (r • y)) := by
                  rw [hy1c, hz1c]
                rw [h6]; module
              · -- p > 0: 0 = (-r) • y1 + p • z1
                refine hnc2 (w5bcs_collinear_of_eq_zero (α := -r) hp0p ?_)
                have h6 : ((-r) • y1 + p • z1 : V3) =
                    ((-r) • (p • y) + p • (r • y)) := by
                  rw [hy1c, hz1c]
                rw [h6]; module
        · -- s ≠ 0: s • y1 = 0 → y1 = 0
          rw [smul_eq_zero] at hdep2
          exact hy10 (hdep2.resolve_left hsne)
      · -- q ≠ 0 且 −q ≤ 0 → q > 0：翻转系数 0 = (−s)•y1 + q•z1
        have hqge : (0:ℝ) ≤ q := by linarith
        have hqp : 0 < q := lt_of_le_of_ne hqge (fun he => hq0 he.symm)
        have hneg : (0:V3) = (-s) • y1 + q • z1 := by
          rw [show ((-s) • y1 + q • z1 : V3) = -(s • y1 + (-q) • z1) from by module, hdep2,
            neg_zero]
        exact hnc2 (w5bcs_collinear_of_eq_zero hqp hneg)
  rcases lt_or_gt_of_ne hDne with hDneg | hDpos
  · -- D < 0：换基 (z,y) 后调用 kill_pos
    have hy1c2 : y1 = q • z + p • y := by rw [hy1c]; module
    have hz1c2 : z1 = s • z + r • y := by rw [hz1c]; module
    have hx1e2 : x = β • z + α • y := by rw [hx1e]; module
    have hzy : ({z, y} : Set V3) = ({y, z} : Set V3) := by
      ext u
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hzy4 : ({z, y, y1, z1} : Set V3) = ({y, z, y1, z1} : Set V3) := by
      ext u
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hnc1' : ¬ Collinear3 (0:V3) z y := by
      intro hcc
      refine hnc1 ?_
      show Collinear ℝ ({(0:V3), y, z} : Set V3)
      rw [show ({(0:V3), y, z} : Set V3) = ({(0:V3), z, y} : Set V3) from by
        ext u
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto]
      exact hcc
    have hadj1' : ‖z - y‖ ≤ cstab_p4 := by rw [norm_sub_rev]; exact hadj1
    exact w6ccs_planar_kill_pos hy1c2 hz1c2 hx1e2 hx2e hβ hα hγ hδ
      (Ne.symm hyz) hz0 hy0 hy1z1 hy10 hz10 hz hy hy1 hz1 hnc1' hnc2 hadj1' hadj2
      (by rw [hzy]; exact hdiff)
      (by
        intro v w hvw hv hw
        rw [hzy4] at hv hw
        exact hsep v w hvw hv hw)
      (by rw [show q * r - s * p = -(p * s - r * q) from by ring]; linarith)
  · -- D > 0：直接调用 kill_pos
    exact w6ccs_planar_kill_pos hy1c hz1c hx1e hx2e hα hβ hγ hδ
      hyz hy0 hz0 hy1z1 hy10 hz10 hy hz hy1 hz1 hnc1 hnc2 hadj1 hadj2 hdiff hsep hDpos



/-! === fan7 装配层（W6c）=== -/


end W6cKit

/-! === W6dKit: bodyclosed-w6d —— fan7/FAN 装配器（w6c 残差清零）+ localFan/azimInFan 两顶石与装配件（w6b 残差清零）。纯插入；零新 import；零 sorry。 === -/

section W6dKit

/-! === fan7 装配层（W6c）=== -/

set_option maxHeartbeats 800000 in
/-- 顶点×顶点 fan7 面。 -/
private theorem w6ccs_fan7_vv {p q : V3} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hp : p ∈ ballAnnulus) (hq : q ∈ ballAnnulus)
    (h2 : p ≠ q → (2:ℝ) ≤ ‖p - q‖) :
    affGe ({0} : Set V3) ({p}) ∩ affGe ({0} : Set V3) ({q})
      = affGe ({0} : Set V3) ((({p} : Set V3) ∩ {q})) := by
  by_cases hpq : p = q
  · have hq' : affGe ({0} : Set V3) ({q}) = affGe ({0} : Set V3) ({p}) := by rw [hpq]
    have hint : ((({p} : Set V3) ∩ {q} : Set V3)) = {p} := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h, -⟩
        exact h
      · intro h
        exact ⟨h, by rw [h, hpq]⟩
    rw [hq', hint, Set.inter_self]
  · have hempty : ((({p} : Set V3) ∩ {q} : Set V3)) = ∅ := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact hpq (h1.symm.trans h2)
      · intro h
        exact absurd h (by simp)
    rw [hempty, w5cs_affGe_empty]
    ext u
    constructor
    · rintro ⟨hu1, hu2⟩
      exact Set.mem_singleton_iff.mpr (VEC0_BALL_ANNULUS (h2 hpq) hp hq hu1 hu2)
    · intro hu
      rw [Set.mem_singleton_iff.mp hu]
      exact ⟨w4cs_zero_mem_ray hp0, w4cs_zero_mem_ray hq0⟩

/-- 边×顶点 fan7 面。 -/
private theorem w6ccs_fan7_ev {y z v : V3}
    (hy0 : y ≠ 0) (hz0 : z ≠ 0) (hv0 : v ≠ 0)
    (hy : y ∈ ballAnnulus) (hz : z ∈ ballAnnulus) (hv : v ∈ ballAnnulus)
    (hnc : ¬ Collinear3 (0:V3) y z)
    (hadj : ‖y - z‖ ≤ cstab_p4)
    (hsep : ∀ u w : V3, u ≠ w → u ∈ ({y, z, v} : Set V3) →
      w ∈ ({y, z, v} : Set V3) → (2:ℝ) ≤ ‖u - w‖) :
    affGe ({0} : Set V3) ({y, z}) ∩ affGe ({0} : Set V3) ({v})
      = affGe ({0} : Set V3) ((({y, z} : Set V3) ∩ {v})) := by
  by_cases hvy : v = y
  · rw [hvy]
    have hint : ((({y, z} : Set V3) ∩ {y} : Set V3)) = {y} := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hint]
    ext u
    constructor
    · rintro ⟨-, hu2⟩
      exact hu2
    · intro hu
      have hc1 : u ∈ affGe ({0} : Set V3) ({y, z}) := by
        rw [aff_ge_eq_aff_gt_union_aff_ge hnc, Set.mem_union, Set.mem_union]
        exact Or.inl (Or.inr hu)
      exact ⟨hc1, hu⟩
  · by_cases hvz : v = z
    · rw [hvz]
      have hint : ((({y, z} : Set V3) ∩ {z} : Set V3)) = {z} := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hint]
      ext u
      constructor
      · rintro ⟨-, hu2⟩
        exact hu2
      · intro hu
        have hc1 : u ∈ affGe ({0} : Set V3) ({y, z}) := by
          rw [aff_ge_eq_aff_gt_union_aff_ge hnc, Set.mem_union, Set.mem_union]
          exact Or.inr hu
        exact ⟨hc1, hu⟩
    · have hyv : y ≠ v := fun h => hvy h.symm
      have hzv : z ≠ v := fun h => hvz h.symm
      have hyz : y ≠ z := fun he => hnc (collinear3_pair_right he.symm)
      have h2yz : (2:ℝ) ≤ ‖y - z‖ := hsep y z hyz (by simp) (by simp)
      have hint : ((({y, z} : Set V3) ∩ {v} : Set V3)) = ∅ := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          rcases h1 with rfl | rfl
          · exact absurd h2 hyv
          · exact absurd h2 hzv
        · intro h
          exact absurd h (by simp)
      rw [hint, w5cs_affGe_empty]
      ext u
      constructor
      · rintro ⟨hu1, hu2⟩
        rw [aff_ge_eq_aff_gt_union_aff_ge hnc, Set.mem_union, Set.mem_union] at hu1
        rcases hu1 with (hgt | hry) | hrz
        · exact Set.mem_singleton_iff.mpr (w6acs_gt_ray_kill_strong (v := v) hnc hy hz hv
            h2yz hadj
            (hsep y v hyv (by simp) (by simp))
            (hsep z v hzv (by simp) (by simp)) hgt hu2)
        · exact Set.mem_singleton_iff.mpr (VEC0_BALL_ANNULUS
            (hsep y v hyv (by simp) (by simp)) hy hv hry hu2)
        · exact Set.mem_singleton_iff.mpr (VEC0_BALL_ANNULUS
            (hsep z v hzv (by simp) (by simp)) hz hv hrz hu2)
      · intro hu
        rw [Set.mem_singleton_iff.mp hu]
        exact ⟨w4cs_zero_mem_cone hnc hy0 hz0, w4cs_zero_mem_ray hv0⟩

/-- 顶点×边 fan7 面（对称）。 -/
private theorem w6ccs_fan7_ve {y z v : V3}
    (hy0 : y ≠ 0) (hz0 : z ≠ 0) (hv0 : v ≠ 0)
    (hy : y ∈ ballAnnulus) (hz : z ∈ ballAnnulus) (hv : v ∈ ballAnnulus)
    (hnc : ¬ Collinear3 (0:V3) y z)
    (hadj : ‖y - z‖ ≤ cstab_p4)
    (hsep : ∀ u w : V3, u ≠ w → u ∈ ({y, z, v} : Set V3) →
      w ∈ ({y, z, v} : Set V3) → (2:ℝ) ≤ ‖u - w‖) :
    affGe ({0} : Set V3) ({v}) ∩ affGe ({0} : Set V3) ({y, z})
      = affGe ({0} : Set V3) ((({v} : Set V3) ∩ {y, z})) := by
  have hL := w6ccs_fan7_ev hy0 hz0 hv0 hy hz hv hnc hadj hsep
  rw [Set.inter_comm (affGe ({0} : Set V3) ({v})) (affGe ({0} : Set V3) ({y, z})),
    Set.inter_comm ({v} : Set V3) ({y, z} : Set V3)]
  exact hL

set_option maxHeartbeats 800000 in
/-- 边×边共享端点 fan7 面（点级、四向统一）。 -/
private theorem w6ccs_fan7_ee_shared {y z y1 z1 v : V3}
    (hy0 : y ≠ 0) (hz0 : z ≠ 0) (hy10 : y1 ≠ 0) (hz10 : z1 ≠ 0)
    (hy : y ∈ ballAnnulus) (hz : z ∈ ballAnnulus) (hy1 : y1 ∈ ballAnnulus)
    (hz1 : z1 ∈ ballAnnulus)
    (hnc1 : ¬ Collinear3 (0:V3) y z) (hnc2 : ¬ Collinear3 (0:V3) y1 z1)
    (hyz : y ≠ z) (hy1z1 : y1 ≠ z1)
    (hadj1 : ‖y - z‖ ≤ cstab_p4) (hadj2 : ‖y1 - z1‖ ≤ cstab_p4)
    (hsep : ∀ u w : V3, u ≠ w → u ∈ ({y, z, y1, z1} : Set V3) →
      w ∈ ({y, z, y1, z1} : Set V3) → (2:ℝ) ≤ ‖u - w‖)
    (hvs : (({y, z} : Set V3) ∩ ({y1, z1} : Set V3)) = ({v} : Set V3)) :
    affGe ({0} : Set V3) ({y, z}) ∩ affGe ({0} : Set V3) ({y1, z1})
      = affGe ({0} : Set V3) ((({y, z} : Set V3) ∩ {y1, z1})) := by
  have hzy := Ne.symm hyz
  have hvin : v ∈ ({y, z} : Set V3) ∩ ({y1, z1} : Set V3) := by
    rw [hvs]; exact Set.mem_singleton_iff.mpr rfl
  have hyv : v = y ∨ v = z := by
    have h1 := hvin.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  have hvw : v = y1 ∨ v = z1 := by
    have h1 := hvin.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  rcases hyv with hv1 | hv1 <;> rcases hvw with hv2 | hv2
  · -- v = y ∧ v = y1：(a,b,c) := (z, y, z1)
    have hyy1 : y = y1 := hv1.symm.trans hv2
    have hX : (z:V3) ≠ z1 := by
      intro he
      have hpv : (z:V3) ∈ ({v} : Set V3) := by
        rw [← hvs]
        refine ⟨Set.mem_insert_of_mem _ (Set.mem_singleton z), ?_⟩
        rw [he]; simp
      exact hyz (((Set.mem_singleton_iff.mp hpv).trans hv1).symm)
    have hint : ((({z, y} : Set V3) ∩ {y, z1} : Set V3)) = {y} := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ?_, fun h => ⟨Or.inr h, Or.inl h⟩⟩
      obtain ⟨h1, h2⟩ := h
      rcases h1 with h1 | h1 <;> rw [h1] at h2
      · rcases h2 with h2 | h2
        · exact absurd h2 hzy
        · exact absurd h2 hX
      · exact h1
    rw [show ((({y, z} : Set V3)) = ({z, y} : Set V3)) from by
      ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto,
      show ((({y1, z1} : Set V3)) = ({y, z1} : Set V3)) from by
        rw [← hyy1], hint]
    have hnc2' : ¬ Collinear3 (0:V3) y z1 := by
      intro hcc
      refine hnc2 ?_
      show Collinear ℝ ({(0:V3), y1, z1} : Set V3)
      rw [show ({(0:V3), y1, z1} : Set V3) = ({(0:V3), y, z1} : Set V3) from by
        rw [← hyy1]]
      exact hcc
    exact w6acs_fan7_edges_shared w6ccs_false_of_planar_inter hyz.symm
      (fun he => hy1z1 (hyy1.symm.trans he)) hX hz hy hz1
      (by
        intro hcc
        refine hnc1 ?_
        show Collinear ℝ ({(0:V3), y, z} : Set V3)
        rw [show ({(0:V3), y, z} : Set V3) = ({(0:V3), z, y} : Set V3) from by
          ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
        exact hcc)
      hnc2' (hsep z y hyz.symm (by simp) (by simp))
      (by rw [norm_sub_rev]; exact hadj1)
      (hsep y z1 (fun he => hy1z1 (hyy1.symm.trans he)) (by simp) (by simp))
      (by rw [hyy1]; exact hadj2)
      (hsep z z1 hX (by simp) (by simp))
  · -- v = y ∧ v = z1：(a,b,c) := (z, y, y1)
    have hzz1 : z1 = y := hv2.symm.trans hv1
    have hX : (z:V3) ≠ y1 := by
      intro he
      have hpv : (z:V3) ∈ ({v} : Set V3) := by
        rw [← hvs]
        refine ⟨Set.mem_insert_of_mem _ (Set.mem_singleton z), ?_⟩
        rw [he]; simp
      exact hyz (((Set.mem_singleton_iff.mp hpv).trans hv1).symm)
    have hint : ((({z, y} : Set V3) ∩ {y, y1} : Set V3)) = {y} := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ?_, fun h => ⟨Or.inr h, Or.inl h⟩⟩
      obtain ⟨h1, h2⟩ := h
      rcases h1 with h1 | h1 <;> rw [h1] at h2
      · rcases h2 with h2 | h2
        · exact absurd h2 hzy
        · exact absurd h2 hX
      · exact h1
    rw [show ((({y, z} : Set V3)) = ({z, y} : Set V3)) from by
      ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto,
      show ((({y1, z1} : Set V3)) = ({y, y1} : Set V3)) from by
        rw [hzz1]; ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, hint]
    have hnc2' : ¬ Collinear3 (0:V3) y y1 := by
      intro hcc
      refine hnc2 ?_
      show Collinear ℝ ({(0:V3), y1, z1} : Set V3)
      rw [show ({(0:V3), y1, z1} : Set V3) = ({(0:V3), y, y1} : Set V3) from by
        rw [hzz1]; ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
      exact hcc
    exact w6acs_fan7_edges_shared w6ccs_false_of_planar_inter hyz.symm
      (fun he => hy1z1 (he.symm.trans hzz1.symm)) hX hz hy hy1
      (by
        intro hcc
        refine hnc1 ?_
        show Collinear ℝ ({(0:V3), y, z} : Set V3)
        rw [show ({(0:V3), y, z} : Set V3) = ({(0:V3), z, y} : Set V3) from by
          ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
        exact hcc)
      hnc2' (hsep z y hyz.symm (by simp) (by simp))
      (by rw [norm_sub_rev]; exact hadj1)
      (hsep y y1 (fun he => hy1z1 (he.symm.trans hzz1.symm)) (by simp) (by simp))
      (by rw [norm_sub_rev, ← hzz1]; exact hadj2)
      (hsep z y1 hX (by simp) (by simp))
  · -- v = z ∧ v = y1：(a,b,c) := (y, z, z1)
    have hyy1 : y1 = z := hv2.symm.trans hv1
    have hX : (y:V3) ≠ z1 := by
      intro he
      have hpv : (y:V3) ∈ ({v} : Set V3) := by
        rw [← hvs]
        refine ⟨Set.mem_insert y ({z} : Set V3), ?_⟩
        rw [he]; simp
      exact hyz ((Set.mem_singleton_iff.mp hpv).trans hv1)
    have hint : ((({y, z} : Set V3) ∩ {z, z1} : Set V3)) = {z} := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ?_, fun h => ⟨Or.inr h, Or.inl h⟩⟩
      obtain ⟨h1, h2⟩ := h
      rcases h1 with h1 | h1 <;> rw [h1] at h2
      · rcases h2 with h2 | h2
        · exact absurd h2 hyz
        · exact absurd h2 hX
      · exact h1
    rw [show ((({y1, z1} : Set V3)) = ({z, z1} : Set V3)) from by
      rw [hyy1], hint]
    have hnc2' : ¬ Collinear3 (0:V3) z z1 := by
      intro hcc
      refine hnc2 ?_
      show Collinear ℝ ({(0:V3), y1, z1} : Set V3)
      rw [show ({(0:V3), y1, z1} : Set V3) = ({(0:V3), z, z1} : Set V3) from by
        rw [hyy1]]
      exact hcc
    exact w6acs_fan7_edges_shared w6ccs_false_of_planar_inter hyz
      (fun he => hy1z1 (hyy1.trans he)) hX hy hz hz1 hnc1 hnc2'
      (hsep y z hyz (by simp) (by simp)) hadj1
      (hsep z z1 (fun he => hy1z1 (hyy1.trans he)) (by simp) (by simp))
      (by rw [← hyy1]; exact hadj2)
      (hsep y z1 hX (by simp) (by simp))
  · -- v = z ∧ v = z1：(a,b,c) := (y, z, y1)
    have hzz1 : z1 = z := hv2.symm.trans hv1
    have hX : (y:V3) ≠ y1 := by
      intro he
      have hpv : (y:V3) ∈ ({v} : Set V3) := by
        rw [← hvs]
        refine ⟨Set.mem_insert y ({z} : Set V3), ?_⟩
        rw [he]; simp
      exact hyz ((Set.mem_singleton_iff.mp hpv).trans hv1)
    have hint : ((({y, z} : Set V3) ∩ {z, y1} : Set V3)) = {z} := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ?_, fun h => ⟨Or.inr h, Or.inl h⟩⟩
      obtain ⟨h1, h2⟩ := h
      rcases h1 with h1 | h1 <;> rw [h1] at h2
      · rcases h2 with h2 | h2
        · exact absurd h2 hyz
        · exact absurd h2 hX
      · exact h1
    rw [show ((({y1, z1} : Set V3)) = ({z, y1} : Set V3)) from by
      rw [hzz1]; ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, hint]
    have hnc2' : ¬ Collinear3 (0:V3) z y1 := by
      intro hcc
      refine hnc2 ?_
      show Collinear ℝ ({(0:V3), y1, z1} : Set V3)
      rw [show ({(0:V3), y1, z1} : Set V3) = ({(0:V3), z, y1} : Set V3) from by
        rw [hzz1]; ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
      exact hcc
    exact w6acs_fan7_edges_shared w6ccs_false_of_planar_inter hyz
      (fun he => hy1z1 (he.symm.trans hzz1.symm)) hX hy hz hy1 hnc1 hnc2'
      (hsep y z hyz (by simp) (by simp)) hadj1
      (hsep z y1 (fun he => hy1z1 (he.symm.trans hzz1.symm)) (by simp) (by simp))
      (by rw [norm_sub_rev, ← hzz1]; exact hadj2)
      (hsep y y1 hX (by simp) (by simp))
set_option maxHeartbeats 800000 in
/-- 边×边不交 fan7 面（极限点侧：topstone → 缺口 2）。 -/
private theorem w6ccs_fan7_ee_disj {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k)
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (humem : ∀ n, u n ∈ SYset_cs k a b)
    (huto : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : L ∈ BSY1body_cs k a b)
    {i i' : Fin k} (hii : i ≠ i') (hiz : i ≠ finNext i') (hzi : finNext i ≠ i')
    (hzz : finNext i ≠ finNext i')
    (hdisj : (({vecmatsV3_p4 L i, vecmatsV3_p4 L (finNext i)} : Set V3) ∩
      {vecmatsV3_p4 L i', vecmatsV3_p4 L (finNext i')}) = (∅ : Set V3)) :
    affGe ({0} : Set V3) ({vecmatsV3_p4 L i, vecmatsV3_p4 L (finNext i)} : Set V3)
      ∩ affGe ({0} : Set V3) ({vecmatsV3_p4 L i', vecmatsV3_p4 L (finNext i')} : Set V3)
      = ({0} : Set V3) := by
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  set y := vecmatsV3_p4 L i with hY
  set z := vecmatsV3_p4 L (finNext i) with hZ
  set y1 := vecmatsV3_p4 L i' with hY1
  set z1 := vecmatsV3_p4 L (finNext i') with hZ1
  have hadj : ∀ j : Fin k, ‖vecmatsV3_p4 L j - vecmatsV3_p4 L (finNext j)‖ ≤ cstab_p4 := by
    intro j
    have hj := w3cs_row_adj_cstab hsys hs hf hk1 L hL
      (p := j.val + 1) (by omega) (by have := j.isLt; omega)
    have hj2 : rowV3_cs L ((j.val + 1) % k + 1) = rowV3_cs L ((finNext j).val + 1) := rfl
    rw [show rowV3_cs L (j.val + 1) = vecmatsV3_p4 L j from w6bcs_row_fin L j,
      hj2, show rowV3_cs L ((finNext j).val + 1) = vecmatsV3_p4 L (finNext j)
        from w6bcs_row_fin L (finNext j)] at hj
    exact hj
  have hnc1 : ¬ Collinear3 (0:V3) y z :=
    NONPARALLEL_BALL_ANNULUS (hL.1 i) (hL.1 (finNext i))
      (w3cs_two_le_next_fin hsys hs hf (by omega) L hL i) (hadj i)
  have hnc2 : ¬ Collinear3 (0:V3) y1 z1 :=
    NONPARALLEL_BALL_ANNULUS (hL.1 i') (hL.1 (finNext i'))
      (w3cs_two_le_next_fin hsys hs hf (by omega) L hL i') (hadj i')
  have hneij : i ≠ finNext i := fun he =>
    hnc1 (collinear3_pair_right (show vecmatsV3_p4 L (finNext i) = vecmatsV3_p4 L i from by
      rw [he.symm]))
  have hneij' : i' ≠ finNext i' := fun he =>
    hnc2 (collinear3_pair_right (show vecmatsV3_p4 L (finNext i') = vecmatsV3_p4 L i' from by
      rw [he.symm]))
  have hsep : ∀ p q : ℕ, 1 ≤ p → p ≤ k → 1 ≤ q → q ≤ k → p ≠ q →
      (2:ℝ) ≤ ‖rowV3_cs L p - rowV3_cs L q‖ :=
    fun p q hp hpk hq hqk hpq => w3cs_two_le_row_of_BSY1body hsys hs hf hk1 L hL hp hpk hq hqk hpq
  have htwo : ∀ p q : Fin k, p ≠ q → (2:ℝ) ≤ ‖vecmatsV3_p4 L p - vecmatsV3_p4 L q‖ := by
    intro p q hpq
    rw [← w6bcs_row_fin, ← w6bcs_row_fin]
    exact hsep (p.val + 1) (q.val + 1) (by omega) (by have := p.isLt; omega)
      (by omega) (by have := q.isLt; omega) (fun h => hpq (Fin.ext (by omega)))
  have h2yz : (2:ℝ) ≤ ‖y - z‖ := htwo i (finNext i) hneij
  have h2y1z1 : (2:ℝ) ≤ ‖y1 - z1‖ := htwo i' (finNext i') hneij'
  have h2yy1 : (2:ℝ) ≤ ‖y - y1‖ := htwo i i' hii
  have h2yz1 : (2:ℝ) ≤ ‖y - z1‖ := htwo i (finNext i') hiz
  have h2zy1 : (2:ℝ) ≤ ‖z - y1‖ := htwo (finNext i) i' hzi
  have h2zz1 : (2:ℝ) ≤ ‖z - z1‖ := htwo (finNext i) (finNext i') hzz
  have hsep4 : ∀ v w : V3, v ≠ w → v ∈ ({y, z, y1, z1} : Set V3) →
      w ∈ ({y, z, y1, z1} : Set V3) → (2:ℝ) ≤ ‖v - w‖ := by
    intro v w hvw hv hw
    have hd : ∀ t : V3, t ∈ ({y, z, y1, z1} : Set V3) →
        t = y ∨ t = z ∨ t = y1 ∨ t = z1 := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      tauto
    rcases hd v hv with rfl | rfl | rfl | rfl <;>
      rcases hd w hw with rfl | rfl | rfl | rfl
    · exact absurd rfl hvw
    · exact h2yz
    · exact h2yy1
    · exact h2yz1
    · rw [norm_sub_rev]; exact h2yz
    · exact absurd rfl hvw
    · exact h2zy1
    · exact h2zz1
    · rw [norm_sub_rev]; exact h2yy1
    · rw [norm_sub_rev]; exact h2zy1
    · exact absurd rfl hvw
    · exact h2y1z1
    · rw [norm_sub_rev]; exact h2yz1
    · rw [norm_sub_rev]; exact h2zz1
    · rw [norm_sub_rev]; exact h2y1z1
    · exact absurd rfl hvw
  have hy0 : y ≠ 0 := w4cs_annulus_ne_zero (hL.1 i)
  have hz0 : z ≠ 0 := w4cs_annulus_ne_zero (hL.1 (finNext i))
  have hy10 : y1 ≠ 0 := w4cs_annulus_ne_zero (hL.1 i')
  have hz10 : z1 ≠ 0 := w4cs_annulus_ne_zero (hL.1 (finNext i'))
  have hdiff4 : ¬ (y1 ∈ ({y, z} : Set V3) ∧ z1 ∈ ({y, z} : Set V3)) := by
    intro hc
    obtain ⟨hm1, -⟩ := hc
    have hmem : y1 ∈ (({y, z} : Set V3) ∩ ({y1, z1} : Set V3)) :=
      ⟨hm1, by simp⟩
    rw [hdisj] at hmem
    exact hmem
  have hR : affGe ({0} : Set V3)
      ((({y, z} : Set V3) ∩ ({y1, z1} : Set V3))) = {0} := by
    rw [hdisj, w5cs_affGe_empty]
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    rw [aff_ge_eq_aff_gt_union_aff_ge hnc1, Set.mem_union, Set.mem_union] at hx1
    rw [aff_ge_eq_aff_gt_union_aff_ge hnc2, Set.mem_union, Set.mem_union] at hx2
    have hkill1 : ∀ (w : V3), w ∈ ({y, z} : Set V3) → ∀ (t : V3),
        t ∈ affGt ({0} : Set V3) ({y1, z1}) → t ∈ affGe ({0} : Set V3) ({w}) → t = 0 := by
      intro w hw t hgt ht
      have hwd : w = y ∨ w = z := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        exact hw
      rcases hwd with hwy | hwz
      · rw [hwy] at ht
        exact w6acs_gt_ray_kill_strong (y := y1) (z := z1) (v := y) hnc2
          (hL.1 i') (hL.1 (finNext i')) (hL.1 i) h2y1z1 (hadj i')
          (by rw [norm_sub_rev]; exact h2yy1) (by rw [norm_sub_rev]; exact h2yz1) hgt ht
      · rw [hwz] at ht
        exact w6acs_gt_ray_kill_strong (y := y1) (z := z1) (v := z) hnc2
          (hL.1 i') (hL.1 (finNext i')) (hL.1 (finNext i)) h2y1z1 (hadj i')
          (by rw [norm_sub_rev]; exact h2zy1) (by rw [norm_sub_rev]; exact h2zz1) hgt ht
    have hkill2 : ∀ (w : V3), w ∈ ({y1, z1} : Set V3) → ∀ (t : V3),
        t ∈ affGt ({0} : Set V3) ({y, z}) → t ∈ affGe ({0} : Set V3) ({w}) → t = 0 := by
      intro w hw t hgt ht
      have hwd : w = y1 ∨ w = z1 := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        exact hw
      rcases hwd with hwy1 | hwz1
      · rw [hwy1] at ht
        exact w6acs_gt_ray_kill_strong (y := y) (z := z) (v := y1) hnc1
          (hL.1 i) (hL.1 (finNext i)) (hL.1 i') h2yz (hadj i)
          h2yy1 h2zy1 hgt ht
      · rw [hwz1] at ht
        exact w6acs_gt_ray_kill_strong (y := y) (z := z) (v := z1) hnc1
          (hL.1 i) (hL.1 (finNext i)) (hL.1 (finNext i')) h2yz (hadj i)
          h2yz1 h2zz1 hgt ht
    rcases hx1 with (g1 | ry) | rz <;> rcases hx2 with (g2 | ry1) | rz1
    · exact (w6ccs_false_of_planar_inter hnc1 hnc2
          (⟨hL.1 i, hL.1 (finNext i), hL.1 i', hL.1 (finNext i')⟩) (hadj i) (hadj i')
          hdiff4 hsep4
          (w5bcs_planar_of_mem_affGt_inter hsys hs hf humem huto hL hii hiz hzi hzz x
            g1 g2).1
          (w5bcs_planar_of_mem_affGt_inter hsys hs hf humem huto hL hii hiz hzi hzz x
            g1 g2).2 g1 g2).elim
    · exact Set.mem_singleton_iff.mpr (hkill2 y1 (by simp) x g1 ry1)
    · exact Set.mem_singleton_iff.mpr (hkill2 z1 (by simp) x g1 rz1)
    · exact Set.mem_singleton_iff.mpr (hkill1 y (by simp) x g2 ry)
    · exact Set.mem_singleton_iff.mpr (VEC0_BALL_ANNULUS h2yy1 (hL.1 i) (hL.1 i') ry ry1)
    · exact Set.mem_singleton_iff.mpr (VEC0_BALL_ANNULUS h2yz1
        (hL.1 i) (hL.1 (finNext i')) ry rz1)
    · exact Set.mem_singleton_iff.mpr (hkill1 z (by simp) x g2 rz)
    · exact Set.mem_singleton_iff.mpr (VEC0_BALL_ANNULUS h2zy1
        (hL.1 (finNext i)) (hL.1 i') rz ry1)
    · exact Set.mem_singleton_iff.mpr (VEC0_BALL_ANNULUS h2zz1
        (hL.1 (finNext i)) (hL.1 (finNext i')) rz rz1)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact ⟨w4cs_zero_mem_cone hnc1 hy0 hz0, w4cs_zero_mem_cone hnc2 hy10 hz10⟩
set_option maxHeartbeats 800000 in
/-- W6c 主装配器：极限点 L 处的 fan7（前提形 = w5cs_false_of_limit_wall 统一形状）。 -/
theorem w6ccs_fan7_of_limit {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k)
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (humem : ∀ n, u n ∈ SYset_cs k a b)
    (huto : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : L ∈ BSY1body_cs k a b) :
    Fan.fan7 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L)) := by
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  have hk2 : 2 < k := by omega
  have hfinInj : Function.Injective (@finNext k) := by
    intro p q hpq
    apply Fin.ext
    have hval : ((p : ℕ) + 1) % k = ((q : ℕ) + 1) % k := congrArg Fin.val hpq
    have h1 : Nat.ModEq k (p : ℕ) (q : ℕ) := Nat.ModEq.add_right_cancel' (c := 1) hval
    change (p : ℕ) % k = (q : ℕ) % k at h1
    rwa [Nat.mod_eq_of_lt p.isLt, Nat.mod_eq_of_lt q.isLt] at h1
  have hadj : ∀ j : Fin k, ‖vecmatsV3_p4 L j - vecmatsV3_p4 L (finNext j)‖ ≤ cstab_p4 := by
    intro j
    have hj := w3cs_row_adj_cstab hsys hs hf hk1 L hL
      (p := j.val + 1) (by omega) (by have := j.isLt; omega)
    have hj2 : rowV3_cs L ((j.val + 1) % k + 1) = rowV3_cs L ((finNext j).val + 1) := rfl
    rw [show rowV3_cs L (j.val + 1) = vecmatsV3_p4 L j from w6bcs_row_fin L j,
      hj2, show rowV3_cs L ((finNext j).val + 1) = vecmatsV3_p4 L (finNext j)
        from w6bcs_row_fin L (finNext j)] at hj
    exact hj
  have hnc : ∀ j : Fin k, ¬ Collinear3 (0:V3) (vecmatsV3_p4 L j)
      (vecmatsV3_p4 L (finNext j)) :=
    fun j => NONPARALLEL_BALL_ANNULUS (hL.1 j) (hL.1 (finNext j))
      (w3cs_two_le_next_fin hsys hs hf hk2 L hL j) (hadj j)
  have hsepN : ∀ p q : ℕ, 1 ≤ p → p ≤ k → 1 ≤ q → q ≤ k → p ≠ q →
      (2:ℝ) ≤ ‖rowV3_cs L p - rowV3_cs L q‖ :=
    fun p q hp hpk hq hqk hpq => w3cs_two_le_row_of_BSY1body hsys hs hf hk1 L hL hp hpk hq hqk hpq
  have htwo : ∀ p q : Fin k, p ≠ q → (2:ℝ) ≤ ‖vecmatsV3_p4 L p - vecmatsV3_p4 L q‖ := by
    intro p q hpq
    rw [← w6bcs_row_fin, ← w6bcs_row_fin]
    exact hsepN (p.val + 1) (q.val + 1) (by omega) (by have := p.isLt; omega)
      (by omega) (by have := q.isLt; omega) (fun h => hpq (Fin.ext (by omega)))
  have hpinj : ∀ p q : Fin k, vecmatsV3_p4 L p = vecmatsV3_p4 L q → p = q := by
    intro p q he
    by_contra hc
    have h2 := htwo p q hc
    rw [he, sub_self, norm_zero] at h2
    linarith
  have hne : ∀ j : Fin k, vecmatsV3_p4 L j ≠ vecmatsV3_p4 L (finNext j) :=
    w3cs_row_ne_next_fin hsys hs hf hk2 L hL
  have hsep4 : ∀ (p1 p2 p3 p4 : Fin k) (a b : V3), a ≠ b →
      a ∈ ({vecmatsV3_p4 L p1, vecmatsV3_p4 L p2, vecmatsV3_p4 L p3,
        vecmatsV3_p4 L p4} : Set V3) →
      b ∈ ({vecmatsV3_p4 L p1, vecmatsV3_p4 L p2, vecmatsV3_p4 L p3,
        vecmatsV3_p4 L p4} : Set V3) → (2:ℝ) ≤ ‖a - b‖ := by
    intro p1 p2 p3 p4 a b hab ha hb
    have hd : ∀ t : V3, t ∈ ({vecmatsV3_p4 L p1, vecmatsV3_p4 L p2, vecmatsV3_p4 L p3,
        vecmatsV3_p4 L p4} : Set V3) → t = vecmatsV3_p4 L p1 ∨ t = vecmatsV3_p4 L p2 ∨
        t = vecmatsV3_p4 L p3 ∨ t = vecmatsV3_p4 L p4 := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      tauto
    rcases hd a ha with rfl | rfl | rfl | rfl <;>
      rcases hd b hb with rfl | rfl | rfl | rfl
    · exact absurd rfl hab
    · exact htwo p1 p2 (fun he => hab (by rw [he]))
    · exact htwo p1 p3 (fun he => hab (by rw [he]))
    · exact htwo p1 p4 (fun he => hab (by rw [he]))
    · rw [norm_sub_rev]
      exact htwo p1 p2 (fun he => hab (by rw [he]))
    · exact absurd rfl hab
    · exact htwo p2 p3 (fun he => hab (by rw [he]))
    · exact htwo p2 p4 (fun he => hab (by rw [he]))
    · rw [norm_sub_rev]
      exact htwo p1 p3 (fun he => hab (by rw [he]))
    · rw [norm_sub_rev]
      exact htwo p2 p3 (fun he => hab (by rw [he]))
    · exact absurd rfl hab
    · exact htwo p3 p4 (fun he => hab (by rw [he]))
    · rw [norm_sub_rev]
      exact htwo p1 p4 (fun he => hab (by rw [he]))
    · rw [norm_sub_rev]
      exact htwo p2 p4 (fun he => hab (by rw [he]))
    · rw [norm_sub_rev]
      exact htwo p3 p4 (fun he => hab (by rw [he]))
    · exact absurd rfl hab
  have hsep3 : ∀ (p1 p2 p3 : Fin k) (a b : V3), a ≠ b →
      a ∈ ({vecmatsV3_p4 L p1, vecmatsV3_p4 L p2, vecmatsV3_p4 L p3} : Set V3) →
      b ∈ ({vecmatsV3_p4 L p1, vecmatsV3_p4 L p2, vecmatsV3_p4 L p3} : Set V3) →
      (2:ℝ) ≤ ‖a - b‖ := by
    intro p1 p2 p3 a b hab ha hb
    have hd : ∀ t : V3, t ∈ ({vecmatsV3_p4 L p1, vecmatsV3_p4 L p2,
        vecmatsV3_p4 L p3} : Set V3) → t = vecmatsV3_p4 L p1 ∨ t = vecmatsV3_p4 L p2 ∨
        t = vecmatsV3_p4 L p3 := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      tauto
    rcases hd a ha with rfl | rfl | rfl <;> rcases hd b hb with rfl | rfl | rfl
    · exact absurd rfl hab
    · exact htwo p1 p2 (fun he => hab (by rw [he]))
    · exact htwo p1 p3 (fun he => hab (by rw [he]))
    · rw [norm_sub_rev]
      exact htwo p1 p2 (fun he => hab (by rw [he]))
    · exact absurd rfl hab
    · exact htwo p2 p3 (fun he => hab (by rw [he]))
    · rw [norm_sub_rev]
      exact htwo p1 p3 (fun he => hab (by rw [he]))
    · rw [norm_sub_rev]
      exact htwo p2 p3 (fun he => hab (by rw [he]))
    · exact absurd rfl hab
  have hdec : ∀ e : Set V3, e ∈ E_SY_p4 (vecmatsV3_p4 L) ∪
      {s : Set V3 | ∃ v ∈ V_SY_p4 (vecmatsV3_p4 L), s = {v}} →
      (∃ j : Fin k, e = ({vecmatsV3_p4 L j, vecmatsV3_p4 L (finNext j)} : Set V3)) ∨
      (∃ j : Fin k, e = ({vecmatsV3_p4 L j} : Set V3)) := by
    intro e he
    rw [Set.mem_union] at he
    rcases he with heE | heV
    · simp only [E_SY_p4, Set.mem_image, Set.mem_univ, true_and] at heE
      obtain ⟨j, rfl⟩ := heE
      exact Or.inl ⟨j, rfl⟩
    · simp only [Set.mem_setOf_eq] at heV
      obtain ⟨v, hv, rfl⟩ := heV
      rw [V_SY_p4, Set.mem_range] at hv
      obtain ⟨j, rfl⟩ := hv
      exact Or.inr ⟨j, rfl⟩
  intro e1 he1 e2 he2
  rcases hdec e1 he1 with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    rcases hdec e2 he2 with ⟨j', rfl⟩ | ⟨j', rfl⟩
  · -- 边×边
    by_cases hjj : j = j'
    · subst hjj
      rw [Set.inter_self, Set.inter_self]
    · by_cases hyeq : vecmatsV3_p4 L j = vecmatsV3_p4 L j'
      · -- 共享端点 v = L j = L j'
        have hzz1ne : vecmatsV3_p4 L (finNext j) ≠ vecmatsV3_p4 L (finNext j') :=
          fun he => hjj (hfinInj (hpinj (finNext j) (finNext j') he))
        refine w6ccs_fan7_ee_shared (v := vecmatsV3_p4 L j)
          (w4cs_annulus_ne_zero (hL.1 j)) (w4cs_annulus_ne_zero (hL.1 (finNext j)))
          (w4cs_annulus_ne_zero (hL.1 j')) (w4cs_annulus_ne_zero (hL.1 (finNext j')))
          (hL.1 j) (hL.1 (finNext j)) (hL.1 j') (hL.1 (finNext j'))
          (hnc j) (hnc j')
          (fun he => hne j he)
          (fun he => hne j' he)
          (hadj j) (hadj j')
          (hsep4 j (finNext j) j' (finNext j'))
          (by
            rw [← hyeq]
            ext t
            simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor
            · rintro ⟨h1, h2⟩
              rcases h1 with h1 | h1
              · exact h1
              · rcases h2 with h2 | h2
                · exact h2
                · exact absurd (h1.symm.trans h2) hzz1ne
            · intro h
              exact ⟨Or.inl h, Or.inl h⟩)
      · by_cases hyz1 : vecmatsV3_p4 L j = vecmatsV3_p4 L (finNext j')
        · -- 共享端点 v = L j = L finNext j'
          have hzz1ne : vecmatsV3_p4 L (finNext j) ≠ vecmatsV3_p4 L (finNext j') :=
            fun he => hjj (hfinInj (hpinj (finNext j) (finNext j') he))
          have hzy1ne : vecmatsV3_p4 L (finNext j) ≠ vecmatsV3_p4 L j' := by
            intro he
            have eq2 : w6bcs_prev j = j' := by
              have h2 := hpinj j (finNext j') hyz1
              have := congrArg w6bcs_prev h2
              rw [w6bcs_prev_finNext] at this
              exact this
            exact w6bcs_hne hsys hs hf hk3 L hL j
              ((congrArg (vecmatsV3_p4 L) eq2).trans he.symm)
          refine w6ccs_fan7_ee_shared (v := vecmatsV3_p4 L j)
            (w4cs_annulus_ne_zero (hL.1 j)) (w4cs_annulus_ne_zero (hL.1 (finNext j)))
            (w4cs_annulus_ne_zero (hL.1 j')) (w4cs_annulus_ne_zero (hL.1 (finNext j')))
            (hL.1 j) (hL.1 (finNext j)) (hL.1 j') (hL.1 (finNext j'))
            (hnc j) (hnc j')
            (fun he => hne j he)
            (fun he => hne j' he)
            (hadj j) (hadj j')
            (hsep4 j (finNext j) j' (finNext j'))
            (by
              rw [← hyz1]
              ext t
              simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
              constructor
              · rintro ⟨h1, h2⟩
                rcases h1 with h1 | h1
                · exact h1
                · rcases h2 with h2 | h2
                  · exact absurd (h1.symm.trans h2) hzy1ne
                  · exact h2
              · intro h
                exact ⟨Or.inl h, Or.inr h⟩)
        · by_cases hzy1 : vecmatsV3_p4 L (finNext j) = vecmatsV3_p4 L j'
          · -- 共享端点 v = L finNext j = L j'
            have hyy1ne : vecmatsV3_p4 L j ≠ vecmatsV3_p4 L (finNext j') := by
              intro he
              have eq2 : w6bcs_prev j = j' := by
                have h2 := hpinj j (finNext j') he
                have := congrArg w6bcs_prev h2
                rw [w6bcs_prev_finNext] at this
                exact this
              exact w6bcs_hne hsys hs hf hk3 L hL j
                ((congrArg (vecmatsV3_p4 L) eq2).trans hzy1.symm)
            refine w6ccs_fan7_ee_shared (v := vecmatsV3_p4 L (finNext j))
              (w4cs_annulus_ne_zero (hL.1 j)) (w4cs_annulus_ne_zero (hL.1 (finNext j)))
              (w4cs_annulus_ne_zero (hL.1 j')) (w4cs_annulus_ne_zero (hL.1 (finNext j')))
              (hL.1 j) (hL.1 (finNext j)) (hL.1 j') (hL.1 (finNext j'))
              (hnc j) (hnc j')
              (fun he => hne j he)
              (fun he => hne j' he)
              (hadj j) (hadj j')
              (hsep4 j (finNext j) j' (finNext j'))
              (by
                rw [← hzy1]
                ext t
                simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
                constructor
                · rintro ⟨h1, h2⟩
                  rcases h1 with h1 | h1
                  · rcases h2 with h2 | h2
                    · exact h2
                    · exact absurd (h1.symm.trans h2) hyy1ne
                  · exact h1
                · intro h
                  exact ⟨Or.inr h, Or.inl h⟩)
          · by_cases hzz1 : vecmatsV3_p4 L (finNext j) = vecmatsV3_p4 L (finNext j')
            · -- 共享端点 v = L finNext j = L finNext j'
              have hyy1ne : vecmatsV3_p4 L j ≠ vecmatsV3_p4 L j' :=
                fun he => hjj (hpinj j j' he)
              refine w6ccs_fan7_ee_shared (v := vecmatsV3_p4 L (finNext j))
                (w4cs_annulus_ne_zero (hL.1 j)) (w4cs_annulus_ne_zero (hL.1 (finNext j)))
                (w4cs_annulus_ne_zero (hL.1 j')) (w4cs_annulus_ne_zero (hL.1 (finNext j')))
                (hL.1 j) (hL.1 (finNext j)) (hL.1 j') (hL.1 (finNext j'))
                (hnc j) (hnc j')
                (fun he => hne j he)
                (fun he => hne j' he)
                (hadj j) (hadj j')
                (hsep4 j (finNext j) j' (finNext j'))
                (by
                  rw [← hzz1]
                  ext t
                  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
                  constructor
                  · rintro ⟨h1, h2⟩
                    rcases h1 with h1 | h1
                    · rcases h2 with h2 | h2
                      · exact absurd (h1.symm.trans h2) hyy1ne
                      · exact h2
                    · exact h1
                  · intro h
                    exact ⟨Or.inr h, Or.inr h⟩)
            · -- 完全不交
              have hhii : j ≠ j' := fun he => hyeq (congrArg (vecmatsV3_p4 L) he)
              have hhiz : j ≠ finNext j' := fun he => hyz1 (congrArg (vecmatsV3_p4 L) he)
              have hhzi : finNext j ≠ j' := fun he => hzy1 (congrArg (vecmatsV3_p4 L) he)
              have hhzz : finNext j ≠ finNext j' := fun he => hzz1 (congrArg (vecmatsV3_p4 L) he)
              have hdisj0 : (({vecmatsV3_p4 L j, vecmatsV3_p4 L (finNext j)} : Set V3) ∩
                  {vecmatsV3_p4 L j', vecmatsV3_p4 L (finNext j')}) = (∅ : Set V3) := by
                ext t
                simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
                constructor
                · rintro ⟨h1, h2⟩
                  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
                  · exact absurd (hpinj j j' (h1.symm.trans h2)) hhii
                  · exact absurd (hpinj j (finNext j') (h1.symm.trans h2)) hhiz
                  · exact absurd (hpinj (finNext j) j' (h1.symm.trans h2)) hhzi
                  · exact absurd (hpinj (finNext j) (finNext j') (h1.symm.trans h2)) hhzz
                · intro h
                  exact absurd h (by simp)
              rw [hdisj0, w5cs_affGe_empty]
              exact w6ccs_fan7_ee_disj hsys hs hf humem huto hL hhii hhiz hhzi hhzz hdisj0
  · -- 边×顶点
    exact w6ccs_fan7_ev (w4cs_annulus_ne_zero (hL.1 j)) (w4cs_annulus_ne_zero (hL.1 (finNext j)))
      (w4cs_annulus_ne_zero (hL.1 j')) (hL.1 j) (hL.1 (finNext j)) (hL.1 j') (hnc j) (hadj j)
      (hsep3 j (finNext j) j')
  · -- 顶点×边
    exact w6ccs_fan7_ve (w4cs_annulus_ne_zero (hL.1 j'))
      (w4cs_annulus_ne_zero (hL.1 (finNext j'))) (w4cs_annulus_ne_zero (hL.1 j))
      (hL.1 j') (hL.1 (finNext j')) (hL.1 j) (hnc j') (hadj j')
      (hsep3 j' (finNext j') j)
  · -- 顶点×顶点
    exact w6ccs_fan7_vv (w4cs_annulus_ne_zero (hL.1 j)) (w4cs_annulus_ne_zero (hL.1 j'))
      (hL.1 j) (hL.1 j') (fun he => htwo j j'
        (fun hc => he (congrArg (vecmatsV3_p4 L) hc)))

/-- W6c 顶石：极限点 L 处的 FAN（S-I 条款）。 -/
theorem w6ccs_FAN_of_limit {k : ℕ} {d : ℝ} {s : Finset ℕ}
    {a b : ℕ → ℕ → ℝ} {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k)
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (humem : ∀ n, u n ∈ SYset_cs k a b)
    (huto : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : L ∈ BSY1body_cs k a b) :
    Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L)) := by
  have hk3 : 3 ≤ k := hsys.1.1
  have hk2 : 2 < k := by omega
  exact w3cs_FAN_of_clauses L (w3cs_sUnion_E_SY_sub_V L)
    (w3cs_Graph_E_SY L (w3cs_row_ne_next_fin hsys hs hf hk2 L hL))
    (w3cs_fan1_E_SY L (by omega)) (w3cs_fan2_E_SY L hL)
    (w3cs_fan6_E_SY hsys hs hf hk2 L hL) (w6ccs_fan7_of_limit hsys hs hf humem huto hL)

/-- Dart count: `|dart1OfFan| = 2 · |F_SY|` (consumes LA4's proven
`CARD_F_SY_EQ` / `F_SY_INTER_IMAGE_NN_EMPTY`). -/
theorem w6bcs_card_darts {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hk2 : 2 < k) (hinj : ∀ i j : Fin k, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    (Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).darts.card
      = 2 * Set.ncard (F_SY_p4 (vecmatsV3_p4 l)) := by
  have hk1 : 1 < k := by omega
  have hncard : Set.ncard (F_SY_p4 (vecmatsV3_p4 l)) = k := CARD_F_SY_EQ l hinj
  have hf1c : (Finset.image
      (fun i : Fin k => (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i))) Finset.univ).card = k := by
    have hinj1 : Function.Injective
        (fun i : Fin k => (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i))) := by
      intro p q hpq
      exact hinj p q (by have h := congrArg Prod.fst hpq; exact h)
    rw [Finset.card_image_of_injective _ hinj1, Finset.card_univ, Fintype.card_fin]
  have hf2c : (Finset.image
      (fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) Finset.univ).card = k := by
    have hinj2 : Function.Injective
        (fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) := by
      intro p q hpq
      exact hinj p q (by have h := congrArg Prod.snd hpq; exact h)
    rw [Finset.card_image_of_injective _ hinj2, Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint
      (Finset.image (fun i : Fin k => (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i)))
        Finset.univ)
      (Finset.image (fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i))
        Finset.univ) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hcon
    have ha' : a ∈ F_SY_p4 (vecmatsV3_p4 l) := by
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp ha
      rw [← hj]
      exact ⟨j, Set.mem_univ _, rfl⟩
    have hab : a ∈ ((fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) ''
        Set.univ) := by
      rw [hcon]
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hb
      rw [← hj]
      exact ⟨j, Set.mem_univ _, rfl⟩
    have hcap : a ∈ F_SY_p4 (vecmatsV3_p4 l) ∩
        ((fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ) :=
      Set.mem_inter ha' hab
    rw [F_SY_INTER_IMAGE_NN_EMPTY l hk2 hinj] at hcap
    exact hcap
  have heq : (Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).darts
      = Finset.image (fun i : Fin k => (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i)))
          Finset.univ
        ∪ Finset.image (fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i))
          Finset.univ := by
    refine Finset.ext fun d => ?_
    show d ∈ ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l))
          (E_SY_p4 (vecmatsV3_p4 l)) hfan).darts : Set (V3 × V3)) ↔
      d ∈ Finset.image (fun i : Fin k => (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i)))
          Finset.univ ∪
        Finset.image (fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i))
          Finset.univ
    constructor
    · intro hd'
      have hs1 : d ∈ ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l))
            (E_SY_p4 (vecmatsV3_p4 l)) hfan).darts : Set (V3 × V3)) :=
        Finset.mem_coe.mp hd'
      rw [w6bcs_darts_coe hfan, w6bcs_dart1_eq l hk1 hinj, F_SY_p4] at hs1
      rcases hs1 with hd1 | hd1
      · obtain ⟨j, -, rfl⟩ := hd1
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
      · obtain ⟨j, -, rfl⟩ := hd1
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    · intro hd'
      rw [Finset.mem_union] at hd'
      rcases hd' with hd1 | hd1
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hd1
        rw [← hj]
        exact w6bcs_darts_mem hfan (by
          show (vecmatsV3_p4 l j, vecmatsV3_p4 l (finNext j))
            ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
          exact ⟨j, Set.mem_univ _, rfl⟩)
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hd1
        rw [← hj]
        exact w6bcs_darts_mem hfan (by
          simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
          rw [Set.pair_comm]
          exact ⟨j, Set.mem_univ _, rfl⟩)
  rw [heq, Finset.card_union_of_disjoint hdisj, hf1c, hf2c, hncard, two_mul]

/-- `edgeMap` has order 2. -/
theorem w6bcs_orders_edge {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hk2 : 2 < k) (hinj : ∀ i j : Fin k, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    hasOrders_p4
      ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).edgeMap
        : V3 × V3 → V3 × V3) 2 := by
  refine ⟨fun i hi0 hi2 => ?_, funext ?_⟩
  · have hi1 : i = 1 := by omega
    subst hi1
    intro hcon
    have hmem : (vecmatsV3_p4 l ⟨(0:ℕ), by omega⟩, vecmatsV3_p4 l (finNext ⟨(0:ℕ), by omega⟩))
        ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
      simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      exact ⟨⟨(0:ℕ), by omega⟩, Set.mem_univ _, rfl⟩
    have h2 := congrFun hcon
      (vecmatsV3_p4 l ⟨(0:ℕ), by omega⟩, vecmatsV3_p4 l (finNext ⟨(0:ℕ), by omega⟩))
    rw [Function.iterate_one, w6bcs_edgeMap_apply hfan _ hmem] at h2
    have h4 : ((0:ℕ) + 1) % k = 0 := by
      have h4' : vecmatsV3_p4 l (finNext ⟨(0:ℕ), by omega⟩)
          = vecmatsV3_p4 l ⟨(0:ℕ), by omega⟩ := congrArg Prod.fst h2
      have h5' := hinj (finNext ⟨(0:ℕ), by omega⟩) ⟨(0:ℕ), by omega⟩ h4'
      exact congrArg Fin.val h5'
    have h6 := Nat.mod_lt (0 + 1) (by omega)
    have h7 : ((0:ℕ) + 1) % k = 1 := by
      show (1:ℕ) % k = 1
      exact Nat.mod_eq_of_lt (by omega)
    omega
  · intro d
    show ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).edgeMap :
        V3 × V3 → V3 × V3)^[2] d = d
    by_cases hd : d ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
    · have hd2 : (d.2, d.1) ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
        simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
        rw [Set.pair_comm]
        exact hd
      rw [Function.iterate_succ_apply, Function.iterate_one, w6bcs_edgeMap_apply hfan d hd,
        w6bcs_edgeMap_apply hfan (d.2, d.1) hd2]
    · rw [Function.iterate_succ_apply, Function.iterate_one]
      have hout := w6bcs_map_apply_out hfan d hd
      rw [hout.2.1, hout.2.1]

/-- `nodeMap` has order 2. -/
theorem w6bcs_orders_node {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hk2 : 2 < k)
    (hinj : ∀ i j : Fin k, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i)) :
    hasOrders_p4
      ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).nodeMap
        : V3 × V3 → V3 × V3) 2 := by
  refine ⟨fun i hi0 hi2 => ?_, funext ?_⟩
  · have hi1 : i = 1 := by omega
    subst hi1
    intro hcon
    have hmem : (vecmatsV3_p4 l ⟨(0:ℕ), by omega⟩, vecmatsV3_p4 l (finNext ⟨(0:ℕ), by omega⟩))
        ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
      simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      exact ⟨⟨(0:ℕ), by omega⟩, Set.mem_univ _, rfl⟩
    have h2 := congrFun hcon
      (vecmatsV3_p4 l ⟨(0:ℕ), by omega⟩, vecmatsV3_p4 l (finNext ⟨(0:ℕ), by omega⟩))
    rw [Function.iterate_one, w6bcs_nodeMap_apply hfan _ hmem,
      w6bcs_nFanPair_next l hsoe hne ⟨(0:ℕ), by omega⟩] at h2
    have h3 : vecmatsV3_p4 l (w6bcs_prev ⟨(0:ℕ), by omega⟩)
        = vecmatsV3_p4 l (finNext ⟨(0:ℕ), by omega⟩) := congrArg Prod.snd h2
    exact hne ⟨(0:ℕ), by omega⟩ h3
  · intro d
    show ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).nodeMap :
        V3 × V3 → V3 × V3)^[2] d = d
    by_cases hd : d ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
    · have hd' : d ∈ F_SY_p4 (vecmatsV3_p4 l) ∪
        ((fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ) := by
        rw [← w6bcs_darts_eq l hfan hk2 hinj]
        exact w6bcs_darts_mem hfan hd
      rcases (Set.mem_union _ _ _).mp hd' with hd1 | hd1
      · obtain ⟨j, -, rfl⟩ := hd1
        have hmem1 : (vecmatsV3_p4 l j, vecmatsV3_p4 l (finNext j)) ∈ Fan.dart1OfFan
            (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
          simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
          exact ⟨j, Set.mem_univ _, rfl⟩
        have hmem2 : (vecmatsV3_p4 l (finNext (w6bcs_prev j)), vecmatsV3_p4 l (w6bcs_prev j))
            ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
          simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
          exact ⟨w6bcs_prev j, Set.mem_univ _, by
            show ({vecmatsV3_p4 l (w6bcs_prev j), vecmatsV3_p4 l (finNext (w6bcs_prev j))} :
                Set V3)
              = ({vecmatsV3_p4 l (finNext (w6bcs_prev j)), vecmatsV3_p4 l (w6bcs_prev j)}
                : Set V3)
            rw [Set.pair_comm]⟩
        rw [Function.iterate_succ_apply, Function.iterate_one,
          w6bcs_nodeMap_apply hfan _ hmem1, w6bcs_nFanPair_next l hsoe hne j,
          show ((vecmatsV3_p4 l j, vecmatsV3_p4 l (w6bcs_prev j)) : V3 × V3)
            = (vecmatsV3_p4 l (finNext (w6bcs_prev j)), vecmatsV3_p4 l (w6bcs_prev j)) from by
            rw [congrArg (vecmatsV3_p4 l) (w6bcs_finNext_prev j).symm],
          w6bcs_nodeMap_apply hfan _ hmem2, w6bcs_nFanPair_prev l hsoe hne (w6bcs_prev j),
          w6bcs_finNext_prev]
      · obtain ⟨t, -, rfl⟩ := hd1
        have hmem1 : (vecmatsV3_p4 l (finNext t), vecmatsV3_p4 l t) ∈ Fan.dart1OfFan
            (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
          simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
          rw [Set.pair_comm]
          exact ⟨t, Set.mem_univ _, rfl⟩
        have hmem3 : (vecmatsV3_p4 l (finNext t), vecmatsV3_p4 l (finNext (finNext t)))
            ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
          simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
          exact ⟨finNext t, Set.mem_univ _, rfl⟩
        rw [Function.iterate_succ_apply, Function.iterate_one,
          w6bcs_nodeMap_apply hfan _ hmem1, w6bcs_nFanPair_prev l hsoe hne t,
          w6bcs_nodeMap_apply hfan _ hmem3,
          w6bcs_nFanPair_next l hsoe hne (finNext t), w6bcs_prev_finNext]
    · rw [Function.iterate_succ_apply, Function.iterate_one]
      have hout := w6bcs_map_apply_out hfan d hd
      rw [hout.2.2, hout.2.2]

/-- Outside the dart set all three maps fix the point; iterates too. -/
theorem w6bcs_faceMap_iterate_out {V : Set V3} {E : Set (Set V3)}
    (hfan : Fan.FAN 0 V E) (n : ℕ) (d : V3 × V3)
    (hd : d ∉ Fan.dart1OfFan V E) :
    ((Fan.hypermapOfFan 0 V E hfan).faceMap : V3 × V3 → V3 × V3)^[n] d = d := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have h1 := (w6bcs_map_apply_out hfan d hd).1
    rw [Function.iterate_succ_apply', ih, h1]

/-- `faceMap` has order `k`. -/
theorem w6bcs_orders_face {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hk2 : 2 < k)
    (hinj : ∀ i j : Fin k, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i)) :
    hasOrders_p4
      ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).faceMap
        : V3 × V3 → V3 × V3) k := by
  have hfk : ∀ i : Fin k, finNext^[k] i = i := by
    intro i
    rw [w6bcs_finNext_iterate]
    refine Fin.ext ?_
    show ((i.val + k) % k) = i.val
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  have hpk : ∀ i : Fin k, (w6bcs_prev)^[k] i = i := by
    intro i
    rw [w6bcs_prev_iterate, Function.iterate_mul,
      show finNext^[k] = (id : Fin k → Fin k) from funext hfk]
    simp
  refine ⟨fun i hi0 hik => ?_, funext ?_⟩
  · intro hcon
    have hmem : (vecmatsV3_p4 l ⟨(0:ℕ), by omega⟩, vecmatsV3_p4 l (finNext ⟨(0:ℕ), by omega⟩))
        ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
      simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      exact ⟨⟨(0:ℕ), by omega⟩, Set.mem_univ _, rfl⟩
    have h2 := congrFun hcon
      (vecmatsV3_p4 l ⟨(0:ℕ), by omega⟩, vecmatsV3_p4 l (finNext ⟨(0:ℕ), by omega⟩))
    rw [w6bcs_faceMap_iterate_fwd l hsoe hne hfan i ⟨(0:ℕ), by omega⟩,
      w6bcs_finNext_iterate, Nat.zero_add] at h2
    have h3 : vecmatsV3_p4 l ⟨(i % k), Nat.mod_lt _ (by omega)⟩
        = vecmatsV3_p4 l ⟨(0:ℕ), by omega⟩ := congrArg Prod.fst h2
    have h4 : (Fin.mk (i % k) (Nat.mod_lt _ (by omega)) : Fin k)
        = Fin.mk 0 (by omega) := hinj _ _ h3
    have h5 : (i % k : ℕ) = 0 := congrArg Fin.val h4
    rw [Nat.mod_eq_of_lt hik] at h5
    omega
  · intro d
    show ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) hfan).faceMap :
        V3 × V3 → V3 × V3)^[k] d = d
    by_cases hd : d ∈ Fan.dart1OfFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
    · have hd' : d ∈ F_SY_p4 (vecmatsV3_p4 l) ∪
        ((fun i : Fin k => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ) := by
        rw [← w6bcs_darts_eq l hfan hk2 hinj]
        exact w6bcs_darts_mem hfan hd
      rcases (Set.mem_union _ _ _).mp hd' with hd1 | hd1
      · obtain ⟨j, -, rfl⟩ := hd1
        rw [w6bcs_faceMap_iterate_fwd l hsoe hne hfan k j, hfk]
      · obtain ⟨t, -, rfl⟩ := hd1
        rw [w6bcs_faceMap_iterate_rev l hsoe hne hfan k t, hpk]
    · exact w6bcs_faceMap_iterate_out hfan k d hd

/-- The `dih2k` clause for the `F_SY` hypermap at the limit configuration
(HOL `DIH2K_FAN_HYP_SY`, dih2k.hl:3217; LA4's twin is a sorry giant,
reproved here from the Fan.hypermapOfFan kit). -/
theorem w6bcs_dih2k {k : ℕ} (l : FinVec k 3)
    (hfan : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hk2 : 2 < k) (hinj : ∀ i j : Fin k, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (hsoe : ∀ i : Fin k,
      Fan.setOfEdge (vecmatsV3_p4 l i) (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) = {vecmatsV3_p4 l (w6bcs_prev i), vecmatsV3_p4 l (finNext i)})
    (hne : ∀ i : Fin k, vecmatsV3_p4 l (w6bcs_prev i) ≠ vecmatsV3_p4 l (finNext i)) :
    dih2k_p4 (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
      (Set.ncard (F_SY_p4 (vecmatsV3_p4 l))) := by
  have hc := w6bcs_card_darts l hfan hk2 hinj
  rw [CARD_F_SY_EQ l hinj] at hc
  rw [w6bcs_hyp_eq hfan, CARD_F_SY_EQ l hinj]
  refine ⟨hc, fun p hp => ?_, w6bcs_orders_face l hfan hk2 hinj hsoe hne,
    w6bcs_orders_edge l hfan hk2 hinj, w6bcs_orders_node l hfan hk2 hinj hsoe hne⟩
  have hs3 : p ∈ ((Fan.hypermapOfFan 0 (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) hfan).darts : Set (V3 × V3)) :=
    Finset.mem_coe.mp hp
  rw [w6bcs_darts_eq l hfan hk2 hinj] at hs3 ⊢
  rcases hs3 with hp1 | hp2
  · obtain ⟨j, -, rfl⟩ := hp1
    rw [← w6bcs_hyp_eq hfan, w6bcs_face_fwd l hfan hsoe hne j, w6bcs_hyp_eq hfan,
      w6bcs_nodeMap_image_fwd l hfan hsoe hne]
  · obtain ⟨j, -, rfl⟩ := hp2
    rw [← w6bcs_hyp_eq hfan, w6bcs_face_rev l hfan hsoe hne j, w6bcs_hyp_eq hfan,
      w6bcs_nodeMap_image_rev l hfan hsoe hne, Set.union_comm]

/-- **S-I top stone**: from the explicit `FAN` clause the full `localFan_p4`
holds with `FF = F_SY` (the ∃-dart and `dih2k` clauses of
`CONDITION2_SY_cs`'s definitional expansion; HOL WJSCPRO:2292-2400,
`FACE_HYP_FAN_SY` + `DIH2K_FAN_HYP_SY` stations). -/
theorem w6bcs_localFan_of_FAN {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k)
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (humem : ∀ n, u n ∈ SYset_cs k a b)
    (huto : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : L ∈ BSY1body_cs k a b)
    (hFAN : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L))) :
    localFan_p4 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L))
      (F_SY_p4 (vecmatsV3_p4 L)) := by
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  have hk2 : 2 < k := by omega
  have hinj := w6bcs_hinj hsys hs hf hk1 L hL
  have hne := w6bcs_hne hsys hs hf hk3 L hL
  have hsoe : ∀ i : Fin k, Fan.setOfEdge (vecmatsV3_p4 L i) (V_SY_p4 (vecmatsV3_p4 L))
      (E_SY_p4 (vecmatsV3_p4 L)) =
      {vecmatsV3_p4 L (w6bcs_prev i), vecmatsV3_p4 L (finNext i)} :=
    fun i => w6bcs_setOfEdge_eq L hk1 hinj i
  refine ⟨hFAN, ⟨(vecmatsV3_p4 L ⟨(0:ℕ), by omega⟩, vecmatsV3_p4 L (finNext ⟨(0:ℕ), by omega⟩)),
    ?_, ?_⟩, ?_⟩
  · rw [w6bcs_hyp_eq hFAN]
    exact w6bcs_darts_mem hFAN (by
      simp only [Fan.dart1OfFan, Set.mem_setOf_eq]
      exact ⟨⟨(0:ℕ), by omega⟩, Set.mem_univ _, rfl⟩)
  · rw [w6bcs_face_fwd L hFAN hsoe hne ⟨(0:ℕ), by omega⟩]
  · exact w6bcs_dih2k L hFAN hk2 hinj hsoe hne

/-- **S-K bridge, direction A**: from the convex bound `azim ≤ π` to the
mixed-product sign (HOL WJSCPRO ~2412-2470 station; `JBDNJJB` = Planarity). -/
theorem w6bcs_mixed_ge_of_azim_le_pi {u v w : V3}
    (h1 : ¬ Collinear3 (0:V3) u v) (h2 : ¬ Collinear3 (0:V3) u w)
    (h : azim 0 u v w ≤ Real.pi) :
    0 ≤ (crossProduct (WithLp.ofLp u : Fin 3 → ℝ) (WithLp.ofLp v : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp w : Fin 3 → ℝ) := by
  obtain ⟨t, ht, hsin⟩ := JBDNJJB h1 h2
  have hs : 0 ≤ Real.sin (azim 0 u v w) := Real.sin_nonneg_of_mem_Icc ⟨azim_nonneg 0 u v w, h⟩
  rw [hsin] at hs
  rcases le_or_gt 0 ((crossProduct (WithLp.ofLp u : Fin 3 → ℝ)
      (WithLp.ofLp v : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp w : Fin 3 → ℝ)) with hm | hm
  · exact hm
  · exfalso
    have hneg : Real.sin (azim 0 u v w) < 0 := by
      rw [hsin]
      have h1 := mul_lt_mul_of_pos_left hm ht
      rwa [mul_zero] at h1
    linarith

/-- **S-K bridge, direction B**: from the mixed-product sign back to
`azim ≤ π` (HOL WJSCPRO ~2470-2600 station: `PI_TO_TWO_PI_NEG_SIN`
route via `azim_lt_two_pi`). -/
theorem w6bcs_azim_le_pi_of_mixed_ge {u v w : V3}
    (h1 : ¬ Collinear3 (0:V3) u v) (h2 : ¬ Collinear3 (0:V3) u w)
    (hm : 0 ≤ (crossProduct (WithLp.ofLp u : Fin 3 → ℝ) (WithLp.ofLp v : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp w : Fin 3 → ℝ)) :
    azim 0 u v w ≤ Real.pi := by
  obtain ⟨t, ht, hsin⟩ := JBDNJJB h1 h2
  have hsn : 0 ≤ Real.sin (azim 0 u v w) := by
    rw [hsin]
    exact mul_nonneg (le_of_lt ht) hm
  rcases lt_or_ge (Real.pi) (azim 0 u v w) with hlt | hle
  · exfalso
    have hsub : azim 0 u v w - Real.pi ∈ Set.Ioo (0:ℝ) Real.pi :=
      ⟨by linarith, by linarith [azim_lt_two_pi 0 u v w]⟩
    have hpos : 0 < Real.sin (azim 0 u v w - Real.pi) := Real.sin_pos_of_mem_Ioo hsub
    have hsinpi : Real.sin (azim 0 u v w - Real.pi) = -Real.sin (azim 0 u v w) := by
      rw [Real.sin_sub]
      simp
    linarith
  · exact hle

/-- **S-K top stone**: the `azimInFan ≤ π` clause of `CONDITION2_SY_cs`
transfers to the limit point (HOL WJSCPRO:2292-2686, S-K; the per-`n`
supply is the convex clause of `CONDITION2_SY_cs (u n)`, the geometric
quantity moves by `w5cs_tendsto_cross_dot` + `ge_of_tendsto`). -/
theorem w6bcs_azimInFan_le_pi {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_cs k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k)
    {u : ℕ → FinVec k 3} {L : FinVec k 3}
    (humem : ∀ n, u n ∈ SYset_cs k a b)
    (huto : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : L ∈ BSY1body_cs k a b)
    (hFAN : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 L)) (E_SY_p4 (vecmatsV3_p4 L))) :
    ∀ x ∈ F_SY_p4 (vecmatsV3_p4 L), azimInFan_p4 x (E_SY_p4 (vecmatsV3_p4 L)) ≤ Real.pi := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := hx
  show azimInFan_p4 (vecmatsV3_p4 L i, vecmatsV3_p4 L (finNext i))
      (E_SY_p4 (vecmatsV3_p4 L)) ≤ Real.pi
  have hk3 : 3 ≤ k := hsys.1.1
  have hk1 : 1 < k := by omega
  have hk2 : 2 < k := by omega
  have hinjL := w6bcs_hinj hsys hs hf hk1 L hL
  have hneL := w6bcs_hne hsys hs hf hk3 L hL
  rw [w6bcs_azimInFan_gen L hFAN hk1 hinjL i (hneL i)]
  have hmxL : 0 ≤ (crossProduct (WithLp.ofLp (vecmatsV3_p4 L i) : Fin 3 → ℝ)
      (WithLp.ofLp (vecmatsV3_p4 L (finNext i)) : Fin 3 → ℝ)) ⬝ᵥ
      (WithLp.ofLp (vecmatsV3_p4 L (w6bcs_prev i)) : Fin 3 → ℝ) := by
    have hmixn : ∀ n : ℕ, 0 ≤ (crossProduct
        (WithLp.ofLp (vecmatsV3_p4 (u n) i) : Fin 3 → ℝ)
        (WithLp.ofLp (vecmatsV3_p4 (u n) (finNext i)) : Fin 3 → ℝ)) ⬝ᵥ
        (WithLp.ofLp (vecmatsV3_p4 (u n) (w6bcs_prev i)) : Fin 3 → ℝ) := by
      intro n
      have hm : u n ∈ SYset_cs k a b := humem n
      have hun : u n ∈ BSY1body_cs k a b := hm.1
      have hc2 : CONDITION2_SY_cs k (u n) := hm.2
      have hfanN : Fan.FAN 0 (V_SY_p4 (vecmatsV3_p4 (u n))) (E_SY_p4 (vecmatsV3_p4 (u n))) :=
        (hc2.1).1
      have hinjN := w6bcs_hinj hsys hs hf hk1 (u n) hun
      have hneN := w6bcs_hne hsys hs hf hk3 (u n) hun
      have hcf := (hc2.2 (vecmatsV3_p4 (u n) i, vecmatsV3_p4 (u n) (finNext i))
        ⟨i, Set.mem_univ _, rfl⟩).1
      rw [w6bcs_azimInFan_gen (u n) hfanN hk1 hinjN i (hneN i)] at hcf
      have he1 : {vecmatsV3_p4 (u n) i, vecmatsV3_p4 (u n) (finNext i)}
          ∈ E_SY_p4 (vecmatsV3_p4 (u n)) := ⟨i, Set.mem_univ _, rfl⟩
      have he2 : {vecmatsV3_p4 (u n) i, vecmatsV3_p4 (u n) (w6bcs_prev i)}
          ∈ E_SY_p4 (vecmatsV3_p4 (u n)) := by
        refine ⟨w6bcs_prev i, Set.mem_univ _, ?_⟩
        show ({vecmatsV3_p4 (u n) (w6bcs_prev i), vecmatsV3_p4 (u n) (finNext (w6bcs_prev i))} :
            Set V3) = ({vecmatsV3_p4 (u n) i, vecmatsV3_p4 (u n) (w6bcs_prev i)} : Set V3)
        rw [w6bcs_finNext_prev, Set.pair_comm]
      exact w6bcs_mixed_ge_of_azim_le_pi (Fan.fan_not_collinear hfanN he1)
        (Fan.fan_not_collinear hfanN he2) hcf
    have htn := w5cs_tendsto_cross_dot huto i (finNext i) (w6bcs_prev i)
    exact ge_of_tendsto htn (Filter.Eventually.of_forall hmixn)
  have he1L : {vecmatsV3_p4 L i, vecmatsV3_p4 L (finNext i)}
      ∈ E_SY_p4 (vecmatsV3_p4 L) := ⟨i, Set.mem_univ _, rfl⟩
  have he2L : {vecmatsV3_p4 L i, vecmatsV3_p4 L (w6bcs_prev i)}
      ∈ E_SY_p4 (vecmatsV3_p4 L) := by
    rw [Set.pair_comm (vecmatsV3_p4 L i) (vecmatsV3_p4 L (w6bcs_prev i))]
    exact ⟨w6bcs_prev i, Set.mem_univ _, by
      show ({vecmatsV3_p4 L (w6bcs_prev i), vecmatsV3_p4 L (finNext (w6bcs_prev i))} :
          Set V3) = ({vecmatsV3_p4 L (w6bcs_prev i), vecmatsV3_p4 L i} : Set V3)
      rw [w6bcs_finNext_prev]⟩
  exact w6bcs_azim_le_pi_of_mixed_ge (Fan.fan_not_collinear hFAN he1L)
    (Fan.fan_not_collinear hFAN he2L) hmxL


end W6dKit

end Kepler.Text
