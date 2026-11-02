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

end Kepler.Text
