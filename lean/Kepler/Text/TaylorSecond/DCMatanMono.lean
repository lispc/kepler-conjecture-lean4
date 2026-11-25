/-
Kepler.Text.TaylorSecond.DCMatanMono — lane `wt1-dcmatan-mono-w1`, M9
(2026-11-25).

**Why.** The M8a preflight of the D1 = 221 certificate boxes measured that the
M7 DC kit's `matan` value bracket is a whole-box interval evaluation
(`dMatan9` / `dMatanWp` / `dMatanU9` / `dMatanMir`), while the cover's T2 is
designed on layout9's **endpoint brackets + `matan` monotonicity**
(`PB(points) = I(points_hi.lo, points_lo.hi)`).  Result: 196/221 boxes had
`slackZ ≤ 0` (DC value brackets 1.1–248× wider than layout9), and 8 boxes had
a genuinely negative `matan` argument (the Dlt corner crosses zero), which the
four positive arms cannot certify (`dLoBig` is false).  The v3 Python preflight
(221/221, min slack +1.06e-5) confirms the fix: endpoint-hull values **and**
endpoint-hull gradients.  This file is the DC counterpart, K1–K4:

  * **K1** `ptLo` / `ptHi` + `dMatanMono` / `dMatanMono_mem` — the value hull
    `I(matan(hi).lo, matan(lo).hi)` from the two endpoint brackets, via the
    landed `nb12w_matan_strictAntiOn : StrictAntiOn matan (Ioi (-1))`.
  * **K2** `dc_mem_of_rat` (+ the `QInterval` bridge `dc_mem_of_qinterval`) —
    the generator-facing literal emission: a dyadic `DC` literal covers any
    exact-rational bracket.  The negative-endpoint bracket itself is the landed
    `MatanNegKit.lkB_matan_neg_pt` (`ql/qh = sqrt_br(-tI)`), **not** a new DC
    series arm; the emission template is in the §2 doc block.
  * **K3** `dMatanDNeg` / `dMatanDNeg_mem` — the derivative on the negative
    branch.  Same closed form as the landed `dMatanD`, but `dDiv` needs a
    positive denominator, so the denominator is `-2r = dMul (dInt (-2)) A` and
    the quotient is negated.
  * **K4** `dMatanDHull` / `dMatanDHull_mem` (+ the `deriv` form and the
    pos/neg/cross endpoint-arm corollaries) — the gradient hull
    `[matanD(lo), matanD(hi)]`, via the landed
    `lkB_matanD_monotoneOn : MonotoneOn matanD (Ioi (-1))`
    (`MatanDMonoNegKit`), which covers the whole `(-1, ∞)` including the
    zero crossing (no Taylor series, no continuity argument needed: the
    monotonicity is global and `matanD 0 = -1/3` is the crossing value).

**Scale discipline (found by the lane self-test, must not be dropped).**  The
arm outputs live at their own dyadic scales (`dMatanDNeg` of a k=200 point
gives k=199 here, `dMatanD` gives k=201), while the argument box sits at yet
another scale.  The work-order sketches `⟨A.k, Mhi.lo, Mlo.hi⟩` are only sound
after the operands are re-expressed at `A.k`; taking the raw mantissas at a
different scale silently shifts the bracket by a power of two (the lane's first
self-test hull was `[-0.644, -0.515]` instead of `[-1.289, -0.258]`).  Both
hull defs therefore normalise through `dRescale` (exact left shift, outward
rounding otherwise); `dRescale_mem` keeps the value bracket.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.M8Kit
import Kepler.Text.TaylorSecond.DCMatan
import Kepler.Text.TaylorSecond.DCJet
import Kepler.Text.Wt1TowerKit
import Kepler.Text.TaylorSecond.MatanDMonoNegKit
import Kepler.Text.TaylorSecond.MatanNegKit

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Kepler.Text.TaylorSecond

namespace DCMatanMono

open DCKit
open DCMatan
open Kepler.Text

/-! ## 0. Scale normalisation -/

/-- Re-express `B`'s bracket at scale `k`, preserving it: an exact left shift
when `B.k ≤ k`, outward rounding (floor on the lower, ceil on the upper end)
otherwise.  Every hull operand goes through this before its mantissas are
copied: arm outputs and argument boxes do not share a scale. -/
def dRescale (k : ℤ) (B : DC) : DC :=
  if B.k ≤ k then
    ⟨k, B.lo <<< (k - B.k), B.hi <<< (k - B.k)⟩
  else
    ⟨k, B.lo.shiftRight (B.k - k).toNat,
      -((-B.hi).shiftRight (B.k - k).toNat)⟩

theorem dRescale_mem {B : DC} {b : ℝ} (k : ℤ) (h : B.mem b) :
    ((dRescale k B).lo : ℝ) * (2:ℝ)^(-(k:ℤ)) ≤ b ∧
      b ≤ ((dRescale k B).hi : ℝ) * (2:ℝ)^(-(k:ℤ)) := by
  unfold dRescale
  split
  · next hk =>
      have hsL := shiftLeft_mul_zpow (x := B.lo) (k := B.k) (kk := k) hk
      have hsH := shiftLeft_mul_zpow (x := B.hi) (k := B.k) (kk := k) hk
      exact ⟨by rw [hsL]; exact h.1, by rw [hsH]; exact h.2⟩
  · next hk =>
      have hlt : k < B.k := by omega
      have hd : (((B.k - k).toNat : ℤ)) = B.k - k := Int.toNat_of_nonneg (by omega)
      have hpow : (2:ℝ)^((B.k - k).toNat) * (2:ℝ)^(-(B.k:ℤ)) = (2:ℝ)^(-(k:ℤ)) := by
        rw [← zpow_natCast (2:ℝ) ((B.k - k).toNat),
          ← zpow_add₀ (a := (2:ℝ)) (by norm_num), hd]
        congr 1
        ring
      have hpd : (0:ℝ) < (2:ℝ)^((B.k - k).toNat) := by positivity
      have hkpos : (0:ℝ) < (2:ℝ)^(-(B.k:ℤ)) := mem_zero_pow B.k
      have hL : (((B.lo.shiftRight (B.k - k).toNat : ℤ)) : ℝ)
          * (2:ℝ)^((B.k - k).toNat) ≤ (B.lo:ℝ) := by
        have h1 := shiftRight_cast_le_nat B.lo (B.k - k).toNat
        calc (((B.lo.shiftRight (B.k - k).toNat : ℤ)) : ℝ) * (2:ℝ)^((B.k - k).toNat)
            ≤ ((B.lo:ℝ) / (2:ℝ)^((B.k - k).toNat)) * (2:ℝ)^((B.k - k).toNat) :=
              mul_le_mul_of_nonneg_right h1 hpd.le
          _ = (B.lo:ℝ) := div_pow_mul_pow _ _
      have hH : (B.hi:ℝ) ≤ -(((((-B.hi).shiftRight (B.k - k).toNat : ℤ)) : ℝ))
          * (2:ℝ)^((B.k - k).toNat) := by
        have h1 : ((((-B.hi).shiftRight (B.k - k).toNat : ℤ)) : ℝ)
            ≤ (-(B.hi:ℝ)) / (2:ℝ)^((B.k - k).toNat) := by
          simpa using shiftRight_cast_le_nat (-B.hi) (B.k - k).toNat
        have h2 : ((((-B.hi).shiftRight (B.k - k).toNat : ℤ)) : ℝ)
            * (2:ℝ)^((B.k - k).toNat) ≤ (-B.hi:ℝ) := by
          calc ((((-B.hi).shiftRight (B.k - k).toNat : ℤ)) : ℝ)
              * (2:ℝ)^((B.k - k).toNat)
              ≤ (((-B.hi:ℝ)) / (2:ℝ)^((B.k - k).toNat))
                * (2:ℝ)^((B.k - k).toNat) :=
                mul_le_mul_of_nonneg_right h1 hpd.le
            _ = (-B.hi:ℝ) := div_pow_mul_pow _ _
        linarith
      refine ⟨?_, ?_⟩
      · calc (((B.lo.shiftRight (B.k - k).toNat : ℤ)) : ℝ) * (2:ℝ)^(-(k:ℤ))
            = ((((B.lo.shiftRight (B.k - k).toNat : ℤ)) : ℝ)
                * (2:ℝ)^((B.k - k).toNat)) * (2:ℝ)^(-(B.k:ℤ)) := by
                rw [← hpow]
                ring
          _ ≤ (B.lo:ℝ) * (2:ℝ)^(-(B.k:ℤ)) :=
              mul_le_mul_of_nonneg_right hL hkpos.le
          _ ≤ b := h.1
      · have hce : ((-((-B.hi).shiftRight (B.k - k).toNat) : ℤ) : ℝ)
            = -(((((-B.hi).shiftRight (B.k - k).toNat : ℤ)) : ℝ)) := by
          push_cast
          ring
        calc b ≤ (B.hi:ℝ) * (2:ℝ)^(-(B.k:ℤ)) := h.2
          _ ≤ (-(((((-B.hi).shiftRight (B.k - k).toNat : ℤ)) : ℝ))
                * (2:ℝ)^((B.k - k).toNat)) * (2:ℝ)^(-(B.k:ℤ)) :=
              mul_le_mul_of_nonneg_right hH hkpos.le
          _ = -(((((-B.hi).shiftRight (B.k - k).toNat : ℤ)) : ℝ))
                * ((2:ℝ)^((B.k - k).toNat) * (2:ℝ)^(-(B.k:ℤ))) := by ring
          _ = ((-((-B.hi).shiftRight (B.k - k).toNat) : ℤ) : ℝ) * (2:ℝ)^(-(k:ℤ)) := by
              rw [hpow, hce]

#print axioms dRescale_mem

/-! ## 1. Endpoints and the monotone value bracket (K1) -/

/-- The lower endpoint of `A` as a degenerate (point) interval. -/
def ptLo (A : DC) : DC := ⟨A.k, A.lo, A.lo⟩

/-- The upper endpoint of `A` as a degenerate (point) interval. -/
def ptHi (A : DC) : DC := ⟨A.k, A.hi, A.hi⟩

theorem ptLo_mem (A : DC) :
    (ptLo A).mem ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ))) := by
  rw [ptLo, DC.mem_mk]
  exact ⟨le_rfl, le_rfl⟩

theorem ptHi_mem (A : DC) :
    (ptHi A).mem ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ))) := by
  rw [ptHi, DC.mem_mk]
  exact ⟨le_rfl, le_rfl⟩

/-- **Monotone value hull.**  `matan` is strictly decreasing on `(-1, ∞)`, so
the two endpoint brackets bracket the whole box with the **reverse** edge
pairing of `dJoin`: the high endpoint's lower edge is the box lower edge, the
low endpoint's upper edge is the box upper edge — layout9's
`PB(points) = I(points_hi.lo, points_lo.hi)`.  Operands are first rescaled to
`A.k` (see §0). -/
def dMatanMono (A Mlo Mhi : DC) : DC :=
  ⟨A.k, (dRescale A.k Mhi).lo, (dRescale A.k Mlo).hi⟩

/-- Value-bracket soundness of `dMatanMono`.  The only domain condition is
`-1 < A.lo` (the domain of `nb12w_matan_strictAntiOn`); `dLoBig` is **not**
needed — that gate only belongs to the positive series arms that produce the
endpoint brackets, not to the monotone assembly. -/
theorem dMatanMono_mem {A : DC} {r : ℝ} (hA : A.mem r)
    {Mlo Mhi : DC}
    (hlo1 : -1 < (A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))
    (hMlo : Mlo.mem (matan ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))))
    (hMhi : Mhi.mem (matan ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ))))) :
    (dMatanMono A Mlo Mhi).mem (matan r) := by
  obtain ⟨hle, hhe⟩ := hA
  have hr1 : -1 < r := lt_of_lt_of_le hlo1 hle
  have hhi1 : -1 < (A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ)) := lt_of_lt_of_le hr1 hhe
  have h1 : matan r ≤ matan ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ))) :=
    nb12w_matan_strictAntiOn.antitoneOn (Set.mem_Ioi.mpr hlo1)
      (Set.mem_Ioi.mpr hr1) hle
  have h2 : matan ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ))) ≤ matan r :=
    nb12w_matan_strictAntiOn.antitoneOn (Set.mem_Ioi.mpr hr1)
      (Set.mem_Ioi.mpr hhi1) hhe
  have hMlo' := dRescale_mem A.k hMlo
  have hMhi' := dRescale_mem A.k hMhi
  show ((dRescale A.k Mhi).lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)) ≤ matan r ∧
       matan r ≤ ((dRescale A.k Mlo).hi : ℝ) * (2:ℝ)^(-(A.k:ℤ))
  exact ⟨le_trans hMhi'.1 h2, le_trans h1 hMlo'.2⟩

/-- Generator-facing form of the domain gate: the Bool test `-1 < A.lo` on the
common dyadic scale (emitted as `by rw [ev]; decide` on a literal box). -/
theorem dMatanMono_mem_gate {A : DC} {r : ℝ} (hA : A.mem r)
    {Mlo Mhi : DC}
    (hlo1 : dLoGt A (dInt (-1)) = true)
    (hMlo : Mlo.mem (matan ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))))
    (hMhi : Mhi.mem (matan ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ))))) :
    (dMatanMono A Mlo Mhi).mem (matan r) :=
  dMatanMono_mem hA (by simpa [dInt] using dLoGt_sound hlo1) hMlo hMhi

#print axioms ptLo_mem
#print axioms ptHi_mem
#print axioms dMatanMono_mem
#print axioms dMatanMono_mem_gate

/-! ## 2. Exact-rational literal emission (K2)

The negative-branch **value bracket at a rational point** is the landed
`Kepler.Text.TaylorSecond.MatanNegKit` product; no new DC series arm is
introduced.  For `tI : ℚ` with `-1 < tI < 0`, `s = -tI ∈ (0,1)`, and rational
`0 < ql ≤ qh < 1` with `ql² ≤ s ≤ qh²`, `lkB_matan_neg_pt` gives

  `matan tI ∈ [ lkB5r ql / ql ,  (lkB5r qh + qh·(qh^10/(1-qh^2))) / qh ]`,

an **exact rational** bracket whose width is dominated by
`qh^10/(1-qh^2)` (`lkB5` is the five-term `artanh`, so the tail is the
geometric-series remainder).  At `u = √s ≤ 1/4` that width is ≤ 1.02e-6; on
the 8 D1 negative slots `u ≤ √0.688 = 0.829`, i.e. the width grows to ≈0.49 —
still valid (`qh < 1`), and v3's 221/221 preflight shows it fits the T2 slack.

**`ql/qh` rule (generator, exact ℚ, no floating point).**  With `D` decimal
digits (D = 40 is ample for the 200-bit boxes),

  * `Nf = (s.numerator * 10^(2D)) // s.denominator`, `ql = isqrt(Nf) / 10^D`;
  * `Nc = ceil(s * 10^(2D))`, `qh = (isqrt(Nc) + 1) / 10^D`;

then `ql² ≤ s` and `s ≤ qh²` hold by `isqrt` bracketing, and `ql > 0`,
`qh < 1`.  (The ztg snapshot's `sqrt_br(v)` is the mpmath/20-digit variant; it
is acceptable only if its two exact-rational assertions `s*s ≤ v ≤ tt*tt` are
kept — the generator must emit the *rationals*, not floats.)

**Emission template** (`MvLo` is the `DC` literal the generator wants; one side
shown; the `hi` endpoint is identical with the positive kit's bracket):

```lean
-- inputs: tI = lo : ℚ (the dyadic endpoint as a rational), ql qh : ℚ,
--         Vlo = QInterval.mk (lkB5r ql / ql) ((lkB5r qh + qh * (qh ^ 10 / (1 - qh ^ 2))) / qh)
have hV : Vlo.mem (matan ((tI : ℚ) : ℝ)) :=
  lkB_matan_neg_pt tI ql qh Vlo
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) rfl
-- loPt = tI as a real; the emitted DC literal covers Vlo's rational ends
-- (pad one grid unit on each side: exact brackets can be narrower than 2^-k)
theorem mvLo : MvLo.mem (matan ((A.lo : ℝ) * (2 : ℝ) ^ (-(A.k : ℤ)))) :=
  dc_mem_of_qinterval (k := 207) (lo := <ceil (Vlo.lo * 2^207) - 1>)
    (hi := <floor (Vlo.hi * 2^207) + 1>) (by norm_num) (by norm_num) hV
```

`dc_mem_of_rat` is the raw form; `dc_mem_of_qinterval` is the same step from a
`QInterval`, which is the shape `lkB_matan_neg_pt` returns.  **Pad by one grid
unit on each side**: a 400-term series bracket at k = 200 can be narrower than
`2^-200`, and unpadded outward rounding then produces the empty literal
`lo = hi + 1` (measured on the lane self-test). -/

/-- Dyadic literal from exact rational endpoints:
`(lo:ℝ)·2^-k ≤ vlo`, `vhi ≤ (hi:ℝ)·2^-k`, `vlo ≤ x ≤ vhi` ⟹
`⟨k,lo,hi⟩ ∋ x`. -/
theorem dc_mem_of_rat {k lo hi : ℤ} {vlo vhi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) * (2:ℝ)^(-(k:ℤ)) ≤ (vlo : ℝ))
    (hhi : (vhi : ℝ) ≤ (hi : ℝ) * (2:ℝ)^(-(k:ℤ)))
    (hxl : (vlo : ℝ) ≤ x) (hxh : x ≤ (vhi : ℝ)) :
    (⟨k, lo, hi⟩ : DC).mem x := by
  show (lo : ℝ) * (2:ℝ)^(-(k:ℤ)) ≤ x ∧ x ≤ (hi : ℝ) * (2:ℝ)^(-(k:ℤ))
  exact ⟨le_trans hlo hxl, le_trans hxh hhi⟩

/-- `QInterval` version of `dc_mem_of_rat`: the exact-rational bracket returned
by `lkB_matan_neg_pt` (or any landed exact-rational kit) is covered by the
dyadic literal. -/
theorem dc_mem_of_qinterval {k lo hi : ℤ} {V : QInterval} {x : ℝ}
    (hlo : (lo : ℝ) * (2:ℝ)^(-(k:ℤ)) ≤ (V.lo : ℝ))
    (hhi : (V.hi : ℝ) ≤ (hi : ℝ) * (2:ℝ)^(-(k:ℤ)))
    (hV : V.mem x) : (⟨k, lo, hi⟩ : DC).mem x :=
  dc_mem_of_rat hlo hhi hV.1 hV.2

#print axioms dc_mem_of_rat
#print axioms dc_mem_of_qinterval

/-! ## 3. Negative-branch derivative (K3)

`matan_deriv_eq` (landed `DCMatan`) proves
`deriv matan r = (1/(1+r) − matan r)/(2r)` only for `r > 0`.  The same closed
form holds on the negative branch (`matan_hasDerivAt` + `matanD_of_ne` are
branch-agnostic); only the DC denominator has to change sign, because `dDiv`
demands `0 < B.lo`: with `A.hi < 0`, `dMul (dInt (-2)) A ∋ -2r > 0`, so
`dNeg (dDiv S B) ∋ S/(-2r) = S/(2r)`. -/

/-- `matan`'s derivative in the DC division form on the **negative** branch
(same shape as the landed positive `matan_deriv_eq`). -/
theorem matan_deriv_eq_neg {r : ℝ} (hr1 : -1 < r) (hr0 : r < 0) :
    deriv matan r = (1/(1+r) - matan r)/(2*r) := by
  rw [(matan_hasDerivAt hr1).deriv, matanD_of_ne (ne_of_lt hr0)]
  rw [one_div, one_div, div_eq_mul_inv]
  ring

/-- Negative-branch derivative bracket `(1/(1+r) − matan r)/(-2r)`, negated to
`(1/(1+r) − matan r)/(2r)`; the `-2r` denominator is what makes `dDiv` legal
when `A.hi < 0`. -/
def dMatanDNeg (A Mv : DC) : DC :=
  dNeg (dDiv (dSub (dInv (dAdd ONE A)) Mv) (dMul (dInt (-2)) A))

/-- Derivative soundness on a negative branch.  `hhi : A.hi < 0` is the exact
condition needed by `dDiv` (the endpoint `hi = 0` would give the denominator
`0`; it does not occur in the D1 boxes — no pure-negative or zero-endpoint
`matan` slot exists, per the M8a survey).  `hlo1` is the `-1 < lo` domain gate
of `matan_hasDerivAt`; the generator discharges it with
`dMatanDNeg_mem_gate`. -/
theorem dMatanDNeg_mem {A Mv : DC} {r : ℝ} (hA : A.mem r)
    (hMv : Mv.mem (matan r)) (hhi : A.hi < 0)
    (hlo1 : -1 < (A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))
    (hden1 : dLoBig (dAdd ONE A) = true)
    (hden2 : dLoBig (dMul (dInt (-2)) A) = true) :
    (dMatanDNeg A Mv).mem (deriv matan r) := by
  have hhiR : (A.hi : ℝ) < 0 := by exact_mod_cast hhi
  have hr0 : r < 0 := lt_of_le_of_lt hA.2 (mul_neg_of_neg_of_pos hhiR (mem_zero_pow A.k))
  have hr1 : -1 < r := lt_of_lt_of_le hlo1 hA.1
  have h1 : (0:ℤ) < (dAdd ONE A).lo := by exact_mod_cast dLoBig_sound hden1
  have h2 : (0:ℤ) < (dMul (dInt (-2)) A).lo := by exact_mod_cast dLoBig_sound hden2
  have hinv : (dInv (dAdd ONE A)).mem (1/(1+r)) := by
    have h := dInv_mem h1 (dAdd_mem ONE_mem hA)
    simpa [one_div] using h
  have hsub := dSub_mem hinv hMv
  have htwo : (dMul (dInt (-2)) A).mem ((-2 : ℝ) * r) := by
    have h := dMul_mem (dInt_mem (-2)) hA
    convert h using 1
    push_cast
    ring
  have hdiv := dDiv_mem h2 hsub htwo
  have hneg := dNeg_mem hdiv
  have hval : -(((1/(1+r)) - matan r) / ((-2:ℝ) * r)) = deriv matan r := by
    rw [matan_deriv_eq_neg hr1 hr0]
    have hrne : r ≠ 0 := ne_of_lt hr0
    field_simp
  rwa [hval] at hneg

/-- Generator-facing form of `dMatanDNeg_mem`: the `-1 < lo` gate as a Bool
test on the common dyadic scale. -/
theorem dMatanDNeg_mem_gate {A Mv : DC} {r : ℝ} (hA : A.mem r)
    (hMv : Mv.mem (matan r)) (hhi : A.hi < 0)
    (hlo1 : dLoGt A (dInt (-1)) = true)
    (hden1 : dLoBig (dAdd ONE A) = true)
    (hden2 : dLoBig (dMul (dInt (-2)) A) = true) :
    (dMatanDNeg A Mv).mem (deriv matan r) :=
  dMatanDNeg_mem hA hMv hhi (by simpa [dInt] using dLoGt_sound hlo1) hden1 hden2

#print axioms matan_deriv_eq_neg
#print axioms dMatanDNeg_mem
#print axioms dMatanDNeg_mem_gate

/-! ## 4. The monotone derivative hull (K4)

`matanD` is strictly increasing on `(-1, ∞)`: `lkB_matanD_strictMonoOn`
(`MatanDMonoNegKit:208`) is proved from `matanDD > 0` on both branches
(`lkB_matanDD_pos`) plus `matanD_hasDerivAt_zero`; its monotone form is
`lkB_matanD_monotoneOn`.  Hence the endpoint derivative brackets are the whole
box's bracket — no interval evaluation of the `1/(2r)` form across a zero
crossing (which is exactly what made v2 fail on 4 boxes: the *function* is
bounded near `0`, the interval formula is not).  A zero endpoint would need the
exact crossing value `matanD 0 = -1/3` (`matanD_zero`, and the landed
`lkB_matanD_zero_mem` for the `QInterval` literal); the D1 data has none (the
minimum lower end is `-0.688`, the point pass is all positive), so the three
arms below are the complete set for the 221 boxes. -/

/-- **Gradient hull** `[matanD(lo).lo, matanD(hi).hi]` (forward pairing, since
`matanD` is increasing).  Operands are first rescaled to `A.k`. -/
def dMatanDHull (A Glo Ghi : DC) : DC :=
  ⟨A.k, (dRescale A.k Glo).lo, (dRescale A.k Ghi).hi⟩

/-- Hull soundness in terms of `matanD` at the endpoints. -/
theorem dMatanDHull_mem {A Glo Ghi : DC} {r : ℝ} (hA : A.mem r)
    (hlo1 : -1 < (A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))
    (hGlo : Glo.mem (matanD ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))))
    (hGhi : Ghi.mem (matanD ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ))))) :
    (dMatanDHull A Glo Ghi).mem (matanD r) := by
  obtain ⟨hle, hhe⟩ := hA
  have hr1 : -1 < r := lt_of_lt_of_le hlo1 hle
  have hhi1 : -1 < (A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ)) := lt_of_lt_of_le hr1 hhe
  have h1 : matanD ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ))) ≤ matanD r :=
    lkB_matanD_monotoneOn (Set.mem_Ioi.mpr hlo1) (Set.mem_Ioi.mpr hr1) hle
  have h2 : matanD r ≤ matanD ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ))) :=
    lkB_matanD_monotoneOn (Set.mem_Ioi.mpr hr1) (Set.mem_Ioi.mpr hhi1) hhe
  have hGlo' := dRescale_mem A.k hGlo
  have hGhi' := dRescale_mem A.k hGhi
  show ((dRescale A.k Glo).lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)) ≤ matanD r ∧
       matanD r ≤ ((dRescale A.k Ghi).hi : ℝ) * (2:ℝ)^(-(A.k:ℤ))
  exact ⟨le_trans hGlo'.1 h1, le_trans h2 hGhi'.2⟩

/-- Hull soundness in the DCJet-facing `deriv matan` form: the endpoint
brackets are derivative brackets (as produced by `dMatanD_mem` /
`dMatanDNeg_mem`), and the conclusion is `deriv matan r`. -/
theorem dMatanDHull_mem_deriv {A Glo Ghi : DC} {r : ℝ} (hA : A.mem r)
    (hlo1 : -1 < (A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))
    (hGlo : Glo.mem (deriv matan ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))))
    (hGhi : Ghi.mem (deriv matan ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ))))) :
    (dMatanDHull A Glo Ghi).mem (deriv matan r) := by
  have hr1 : -1 < r := lt_of_lt_of_le hlo1 hA.1
  have hhi1 : -1 < (A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ)) := lt_of_lt_of_le hr1 hA.2
  have hGlo' : Glo.mem (matanD ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))) := by
    rwa [(matan_hasDerivAt hlo1).deriv] at hGlo
  have hGhi' : Ghi.mem (matanD ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ)))) := by
    rwa [(matan_hasDerivAt hhi1).deriv] at hGhi
  rw [(matan_hasDerivAt hr1).deriv]
  exact dMatanDHull_mem hA hlo1 hGlo' hGhi'

/-! ### Endpoint-arm corollaries (generator-facing) -/

/-- Positive box: both endpoint derivative brackets through the landed
`dMatanD` (whose gates are the three `dLoBig` Bool facts per endpoint). -/
def dMatanDHullPos (A MvLo MvHi : DC) : DC :=
  dMatanDHull A (dMatanD (ptLo A) MvLo) (dMatanD (ptHi A) MvHi)

theorem dMatanDHullPos_mem {A MvLo MvHi : DC} {r : ℝ} (hA : A.mem r)
    (hlo : 0 < A.lo)
    (hMvLo : MvLo.mem (matan ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))))
    (hMvHi : MvHi.mem (matan ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ)))))
    (hbigLo : dLoBig (ptLo A) = true)
    (hden1Lo : dLoBig (dAdd ONE (ptLo A)) = true)
    (hden2Lo : dLoBig (dMul (dInt 2) (ptLo A)) = true)
    (hbigHi : dLoBig (ptHi A) = true)
    (hden1Hi : dLoBig (dAdd ONE (ptHi A)) = true)
    (hden2Hi : dLoBig (dMul (dInt 2) (ptHi A)) = true) :
    (dMatanDHullPos A MvLo MvHi).mem (deriv matan r) := by
  have hlo1 : -1 < (A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)) := by
    have hs : (0:ℝ) < (2:ℝ)^(-(A.k:ℤ)) := mem_zero_pow A.k
    have h : (0:ℝ) < (A.lo : ℝ) := by exact_mod_cast hlo
    exact lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) (le_of_lt (mul_pos h hs))
  unfold dMatanDHullPos
  exact dMatanDHull_mem_deriv hA hlo1
    (dMatanD_mem (ptLo_mem A) hMvLo hbigLo hden1Lo hden2Lo)
    (dMatanD_mem (ptHi_mem A) hMvHi hbigHi hden1Hi hden2Hi)

/-- Negative box (`A.hi < 0`): both endpoint derivative brackets through
`dMatanDNeg`.  `A.lo < 0` follows from `A.mem r` + `A.hi < 0`; the remaining
hypotheses are the `-1 < lo` gate and the two denominator gates per endpoint. -/
def dMatanDHullNeg (A MvLo MvHi : DC) : DC :=
  dMatanDHull A (dMatanDNeg (ptLo A) MvLo) (dMatanDNeg (ptHi A) MvHi)

theorem dMatanDHullNeg_mem {A MvLo MvHi : DC} {r : ℝ} (hA : A.mem r)
    (hhi : A.hi < 0)
    (hlo1 : -1 < (A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))
    (hMvLo : MvLo.mem (matan ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))))
    (hMvHi : MvHi.mem (matan ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ)))))
    (hden1Lo : dLoBig (dAdd ONE (ptLo A)) = true)
    (hden2Lo : dLoBig (dMul (dInt (-2)) (ptLo A)) = true)
    (hden1Hi : dLoBig (dAdd ONE (ptHi A)) = true)
    (hden2Hi : dLoBig (dMul (dInt (-2)) (ptHi A)) = true) :
    (dMatanDHullNeg A MvLo MvHi).mem (deriv matan r) := by
  have hs : (0:ℝ) < (2:ℝ)^(-(A.k:ℤ)) := mem_zero_pow A.k
  have hr1 : -1 < r := lt_of_lt_of_le hlo1 hA.1
  have hhi1 : -1 < (A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ)) := lt_of_lt_of_le hr1 hA.2
  -- `A.lo ≤ A.hi < 0` at the integer level
  have hloA : A.lo < 0 := by
    have hcast : ((A.lo : ℝ)) * (2:ℝ)^(-(A.k:ℤ)) ≤ ((A.hi : ℝ)) * (2:ℝ)^(-(A.k:ℤ)) :=
      le_trans hA.1 hA.2
    have h2 : (A.lo : ℝ) ≤ (A.hi : ℝ) := le_of_mul_le_mul_right hcast hs
    exact lt_of_le_of_lt (by exact_mod_cast h2) hhi
  unfold dMatanDHullNeg
  exact dMatanDHull_mem_deriv hA hlo1
    (dMatanDNeg_mem (ptLo_mem A) hMvLo hloA hlo1 hden1Lo hden2Lo)
    (dMatanDNeg_mem (ptHi_mem A) hMvHi hhi hhi1 hden1Hi hden2Hi)

/-- Cross-zero box (`A.lo < 0 < A.hi`): the negative endpoint through
`dMatanDNeg`, the positive endpoint through the landed `dMatanD` — two
*different* branch formulas on the two ends, with no interval evaluation of
`1/(2r)` across `0`. -/
def dMatanDHullCross (A MvLo MvHi : DC) : DC :=
  dMatanDHull A (dMatanDNeg (ptLo A) MvLo) (dMatanD (ptHi A) MvHi)

theorem dMatanDHullCross_mem {A MvLo MvHi : DC} {r : ℝ} (hA : A.mem r)
    (hlo : A.lo < 0) (_hhi : 0 < A.hi)
    (hlo1 : -1 < (A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))
    (hMvLo : MvLo.mem (matan ((A.lo : ℝ) * (2:ℝ)^(-(A.k:ℤ)))))
    (hMvHi : MvHi.mem (matan ((A.hi : ℝ) * (2:ℝ)^(-(A.k:ℤ)))))
    (hden1Lo : dLoBig (dAdd ONE (ptLo A)) = true)
    (hden2Lo : dLoBig (dMul (dInt (-2)) (ptLo A)) = true)
    (hbigHi : dLoBig (ptHi A) = true)
    (hden1Hi : dLoBig (dAdd ONE (ptHi A)) = true)
    (hden2Hi : dLoBig (dMul (dInt 2) (ptHi A)) = true) :
    (dMatanDHullCross A MvLo MvHi).mem (deriv matan r) := by
  unfold dMatanDHullCross
  exact dMatanDHull_mem_deriv hA hlo1
    (dMatanDNeg_mem (ptLo_mem A) hMvLo hlo hlo1 hden1Lo hden2Lo)
    (dMatanD_mem (ptHi_mem A) hMvHi hbigHi hden1Hi hden2Hi)

#print axioms dMatanDHull_mem
#print axioms dMatanDHull_mem_deriv
#print axioms dMatanDHullPos_mem
#print axioms dMatanDHullNeg_mem
#print axioms dMatanDHullCross_mem

/-! ## 5. Self-test on an authentic D1 cross-zero slot

The box below is the **box-pass `matan` argument `GC`** of
`W1DC_15866_RRR_zero_0#0`, the minimum-`lo` cross-zero slot of the 8
true-negative D1 boxes (`lo = -6.877419729e-01`, `hi = +2.374506752e-01`,
quoted from the M8 generator's emitted `ev_GC` literal).  `MvLo`/`MvHi` are
point brackets of `matan` at its two endpoints computed with the rigorous
400-term series and padded outward by one `2^-200` grid unit (the Python
replica checks them numerically; their Lean `mem` is the K2 emission
obligation and is kept as a **hypothesis** of the two `*_mem` instantiations
below — no unproved fact is asserted).  `decide` re-evaluates the actual kit
defs (`dMatanDNeg` k=199, `dMatanD` k=201, the rescaled hull at k=200); `rfl`
checks the hull wiring. -/

/-- Authentic cross-zero `matan` argument box (D1, `W1DC_15866_RRR_zero_0#0`, `GC`). -/
def crossA : DC :=
  ⟨(200 : ℤ),
   (-1105158740950731742731130305825918071336834073903992985821718 : ℤ),
   (381568523608251561911458042015267508574945624595132244727993 : ℤ)⟩

/-- `matan` bracket at `crossA.lo` (`≈ 1.429994256`), padded by one grid unit. -/
def crossMvLo : DC :=
  ⟨(200 : ℤ),
   (2297912173322022672034225435713870464359560944224902307453491 : ℤ),
   (2297912173322022672034225435713870464359560944224902307453492 : ℤ)⟩

/-- `matan` bracket at `crossA.hi` (`≈ 0.930509790`), padded by one grid unit. -/
def crossMvHi : DC :=
  ⟨(200 : ℤ),
   (1495271582381442154045322780378531357667704041150602397697085 : ℤ),
   (1495271582381442154045322780378531357667704041150602397697086 : ℤ)⟩

theorem test_gate_lo : dLoGt crossA (dInt (-1)) = true := by decide

theorem test_neg_lit :
    (dMatanDNeg (ptLo crossA) crossMvLo).k = (199 : ℤ) ∧
    (dMatanDNeg (ptLo crossA) crossMvLo).lo =
      (-1035371709733577272762552556916809029191245169555786952336331 : ℤ) ∧
    (dMatanDNeg (ptLo crossA) crossMvLo).hi =
      (-1035371709733577272762552556916809029191245169555786952336327 : ℤ) := by
  decide

theorem test_pos_lit :
    (dMatanD (ptHi crossA) crossMvHi).k = (201 : ℤ) ∧
    (dMatanD (ptHi crossA) crossMvHi).lo =
      (-828315308940711285245692816239444689248533719633111045360593 : ℤ) ∧
    (dMatanD (ptHi crossA) crossMvHi).hi =
      (-828315308940711285245692816239444689248533719633111045360578 : ℤ) := by
  decide

/-- The hull wiring itself is definitional. -/
theorem test_hull_rfl :
    dMatanDHull crossA (dMatanDNeg (ptLo crossA) crossMvLo)
        (dMatanD (ptHi crossA) crossMvHi) =
      ⟨(200 : ℤ),
       (dRescale (200 : ℤ) (dMatanDNeg (ptLo crossA) crossMvLo)).lo,
       (dRescale (200 : ℤ) (dMatanD (ptHi crossA) crossMvHi)).hi⟩ := rfl

/-- The rescaled hull is the measured true range
`[-1.288626794, -0.257730941]` (101-point exact-rational scan of `matanD` over
the box; Python replica, `selftest_data.py`, contained). -/
theorem test_hull_lit :
    (dMatanDHull crossA (dMatanDNeg (ptLo crossA) crossMvLo)
        (dMatanD (ptHi crossA) crossMvHi)).k = (200 : ℤ) ∧
    (dMatanDHull crossA (dMatanDNeg (ptLo crossA) crossMvLo)
        (dMatanD (ptHi crossA) crossMvHi)).lo =
      (-2070743419467154545525105113833618058382490339111573904672662 : ℤ) ∧
    (dMatanDHull crossA (dMatanDNeg (ptLo crossA) crossMvLo)
        (dMatanD (ptHi crossA) crossMvHi)).hi =
      (-414157654470355642622846408119722344624266859816555522680289 : ℤ) := by
  decide

/-- `0 ∈ crossA` (the crossing point of the slot). -/
theorem crossA_mem_zero : crossA.mem 0 := by
  refine ⟨?_, ?_⟩
  · have h : ((crossA.lo : ℤ) : ℝ) < 0 := by
      have hZ : crossA.lo < 0 := by decide
      exact_mod_cast hZ
    exact le_of_lt (mul_neg_of_neg_of_pos h (mem_zero_pow crossA.k))
  · have h : (0 : ℝ) < ((crossA.hi : ℤ) : ℝ) := by
      have hZ : 0 < crossA.hi := by decide
      exact_mod_cast hZ
    exact le_of_lt (mul_pos h (mem_zero_pow crossA.k))

/-- K1 instantiated at the crossing point: the endpoint hull brackets
`matan 0 = 1` (conditional only on the two genuine endpoint brackets). -/
theorem test_mono_mem
    (hMvLo : crossMvLo.mem (matan ((crossA.lo : ℝ) * (2:ℝ)^(-(crossA.k:ℤ)))))
    (hMvHi : crossMvHi.mem (matan ((crossA.hi : ℝ) * (2:ℝ)^(-(crossA.k:ℤ))))) :
    (dMatanMono crossA crossMvLo crossMvHi).mem (matan 0) :=
  dMatanMono_mem_gate crossA_mem_zero test_gate_lo hMvLo hMvHi

/-- K4 instantiated at the crossing point: the mixed-branch derivative hull
covers `deriv matan 0 = matanD 0 = -1/3`; the six `dLoBig` gates of the two
endpoints and the branch predicates are discharged by `decide`. -/
theorem test_hull_mem
    (hMvLo : crossMvLo.mem (matan ((crossA.lo : ℝ) * (2:ℝ)^(-(crossA.k:ℤ)))))
    (hMvHi : crossMvHi.mem (matan ((crossA.hi : ℝ) * (2:ℝ)^(-(crossA.k:ℤ))))) :
    (dMatanDHullCross crossA crossMvLo crossMvHi).mem (deriv matan 0) :=
  dMatanDHullCross_mem crossA_mem_zero (by decide) (by decide)
    (by simpa [dInt] using dLoGt_sound test_gate_lo)
    hMvLo hMvHi (by decide) (by decide) (by decide) (by decide) (by decide)

/-- K1 numeric consequence at the crossing point: the value hull contains
`matan 0 = 1` (landed `lkB_matan_zero`). -/
theorem test_mono_contains_one
    (hMvLo : crossMvLo.mem (matan ((crossA.lo : ℝ) * (2:ℝ)^(-(crossA.k:ℤ)))))
    (hMvHi : crossMvHi.mem (matan ((crossA.hi : ℝ) * (2:ℝ)^(-(crossA.k:ℤ))))) :
    ((dMatanMono crossA crossMvLo crossMvHi).lo : ℝ)
        * (2:ℝ)^(-(crossA.k:ℤ)) ≤ 1 ∧
      1 ≤ ((dMatanMono crossA crossMvLo crossMvHi).hi : ℝ)
        * (2:ℝ)^(-(crossA.k:ℤ)) := by
  have h := test_mono_mem hMvLo hMvHi
  rwa [lkB_matan_zero] at h

/-- K4 numeric consequence at the crossing point: the mixed-branch hull
contains `deriv matan 0 = matanD 0 = -1/3` (landed `matanD_zero`). -/
theorem test_hull_contains_third
    (hMvLo : crossMvLo.mem (matan ((crossA.lo : ℝ) * (2:ℝ)^(-(crossA.k:ℤ)))))
    (hMvHi : crossMvHi.mem (matan ((crossA.hi : ℝ) * (2:ℝ)^(-(crossA.k:ℤ))))) :
    ((dMatanDHullCross crossA crossMvLo crossMvHi).lo : ℝ)
        * (2:ℝ)^(-(crossA.k:ℤ)) ≤ -(1/3) ∧
      -(1/3) ≤ ((dMatanDHullCross crossA crossMvLo crossMvHi).hi : ℝ)
        * (2:ℝ)^(-(crossA.k:ℤ)) := by
  have h := test_hull_mem hMvLo hMvHi
  rw [show deriv matan 0 = -(1/3) by
    rw [(matan_hasDerivAt (by norm_num : (-1:ℝ) < 0)).deriv, matanD_zero]] at h
  exact h

#print axioms test_gate_lo
#print axioms test_neg_lit
#print axioms test_pos_lit
#print axioms test_hull_rfl
#print axioms test_hull_lit
#print axioms crossA_mem_zero
#print axioms test_mono_mem
#print axioms test_hull_mem
#print axioms test_mono_contains_one
#print axioms test_hull_contains_third

end DCMatanMono
end Kepler.Text.TaylorSecond
