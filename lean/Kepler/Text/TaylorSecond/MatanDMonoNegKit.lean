/-
Kepler.Text.TaylorSecond.MatanDMonoNegKit — lane `wt1-matanD-mono-w1` (2026-11-25),
wt1 gap **G4**: the `matanD` monotonicity kit that completes the endpoint-route
negative-branch (204 fully negative leaves of 6,989) and zero-crossing (51)
assemblies of the wt1 Route B tower.

Context (`wt1-subdiv-study-w1` REPORT §0, 2026-11-25).  `wtspec.build_box`
cannot evaluate the 255 non-positive leaves at all (`assert I.lo > 0`: all six
`matan` slots are simultaneously non-positive).  The landed **slot-level**
factor-interval ops `MatanNegKit.lkB_matanD_ops_neg` /
`lkB_matanDD_ops_neg` are *sound* but pathological on those slots
(`matanDD` widths 450 … 1.8e5 against true values 0.40–0.45, independent of
the series order `N`; 0/204 closed).  The measured-successful route is the
**endpoint point brackets + monotonicity** mirror of the positive-branch
`LeafGenKit.g_mD_vf` / `g_mDD_vf` template — with it the study closed
204/204 negative leaves (margins 1.085e−2 … 4.703e−2) and 51/51 zero-crossing
leaves (7.179e−3 … 3.049e−2).  What that route still lacked on the Lean side
was `matanD` monotonicity (the mD slot and the `t = 0` endpoint); this file
supplies it, plus the point brackets and slot assemblies in the *consumer
shape* of the positive kit.

Content.
* §1 `lkB_arctan_gt_matanDD_bound`: the rational lower bound
  `s(3+5s²)/(3(1+s²)²) < arctan s` for `s > 0` (gap derivative
  `8s⁴/(3(1+s²)³) > 0`, gap `0` at `s = 0`).  It is exactly the numerator
  inequality of the positive-branch `matanDD` closed form.
* §2 `lkB_matanDD_pos`: **`0 < matanDD t` on the whole domain `(-1, ∞)`** —
  negative branch from the landed `lkB_matanDD_zero_le_of_neg` (`2/5 ≤ ·`),
  `t = 0` from `matanDD_zero`, positive branch from §1 through
  `matanDD t = (3(1+t)²·matan t − (3+5t)) / (4t²(1+t)²)`.
* §3 `lkB_matanD_strictMonoOn : StrictMonoOn matanD (Set.Ioi (-1))` — the
  **global** result, not just the negative branch: `deriv matanD = matanDD > 0`
  (§2) and continuity at `0` is the landed `matanD_hasDerivAt_zero`.  Immediate
  corollaries: `matanD t < -1/3 = matanD 0` for `t < 0`, `-1/3 < matanD t` for
  `t > 0` (the crossing values the zero-split slots need).
* §4 point brackets: `lkBMDpt` / `lkB_matanD_pt` (branch-agnostic exact-rational
  point bracket from a `matan` point bracket at the same `tI ≠ 0`, the positive
  kit's `gMD` expression evaluated on point intervals — the reciprocal sign
  side-condition is discharged by the sign of `tI`), `lkB_matanD_zero_mem`
  (the exact value `-1/3` at `t = 0`), and `lkBMDneg` / `lkBMDneg_mem` — the
  one-stop negative endpoint constructor with `lkB_matan_neg_pt`'s exact
  interface (`ql² ≤ -tI ≤ qh²` in, `matanD` point bracket out).
* §5 slot assembly: `lkB_matanD_transport` / `lkB_matanD_slot` (increasing
  shape `QInterval.mk MDl.lo MDh.hi`, covers negative, zero-crossing and
  positive slots in one statement) + `lkB_matanD_slot_neg` (the
  `TI.hi ≤ 0` specialisation) + the zero-split convenience forms
  `lkB_matanD_slot_zero_hi` / `_zero_lo` (a leaf split at `0` uses the exact
  value `-1/3`) + `lkB_matanD_slot_from_matan` (endpoint `matan` brackets →
  mD slot in one step).
* §6 `matanDD` slot re-exports in the same consumer shape: `lkBMDDslot`,
  `lkB_mDD_slot`, `lkB_matanDD_slot_neg`, `lkB_matanDD_slot_cross`.  The
  underlying monotone transport is the **landed** `lkB_matanDD_slot`
  (`AntitoneOn matanDD (Ioi (-1))` + `matanDD 0 = 2/5`); no new `matanDD`
  monotonicity content is added here, these are name/shape parity wrappers.
* §7 the negative-branch mirrors of the positive consumer template
  (`LeafGenKit.g_mD_vf` / `g_mDD_vf`, drop-in with the lemma name swapped):
  `lkB_mD_vf` / `lkB_mDD_vf`.

Route note (what the emitter must pair with this file).  Endpoint `matan`
point brackets on the negative side come from the landed `lkB_matan_neg_pt`
(exact rationals; for slots with `u = √(-tI) ≳ 0.25` that file must be
re-emitted with a larger series order `N`, per its own note — the study used
`N = 17`), on the positive side from the landed positive point kit, and at
`t = 0` from `lkB_matan_zero` / `lkB_matanD_zero_mem` / `lkBDD_zero_mem`.
`V` provenance is deliberately an argument everywhere in §4–§6, so a larger-`N`
re-emission changes nothing here.

Numerical audit (`scripts/check_numeric.py`, exact `fractions.Fraction`):
endpoint-bracket inclusion at all sampled rational points, and the full
mD/mDD slot inclusion on 9 real fully-negative and 3 real zero-crossing
`t`-slots extracted from `wt1-phaseb-data-w1/data/leaves_exact.json` (the
same slot intervals `wt1-subdiv-study-w1` used), checked on exact rational
grid points plus the irrational `u = √(-t)` points.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.MatanDDNegTransport

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Kepler.Text

/-! ## 1. The arctan bound behind positive-branch `matanDD` positivity -/

/-- **Rational lower bound for `arctan`**: `s(3+5s²)/(3(1+s²)²) < arctan s` for
`s > 0`.  The gap `f s = arctan s − s(3+5s²)/(3(1+s²)²)` vanishes at `0` and
has derivative `8s⁴/(3(1+s²)³) > 0`.  Cross-multiplied, this is exactly the
numerator inequality of the positive-branch closed form
`matanDD t = (3(1+t)²·matan t − (3+5t))/(4t²(1+t)²)` at `t = s²`. -/
theorem lkB_arctan_gt_matanDD_bound {s : ℝ} (hs : 0 < s) :
    s * (3 + 5 * s ^ 2) / (3 * (1 + s ^ 2) ^ 2) < Real.arctan s := by
  have hcont : ContinuousOn
      (fun x : ℝ => Real.arctan x - x * (3 + 5 * x ^ 2) / (3 * (1 + x ^ 2) ^ 2))
      (Set.Ici 0) := by
    refine Real.continuous_arctan.continuousOn.sub ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      positivity
  have h := strictMonoOn_of_deriv_pos (D := Set.Ici (0 : ℝ))
    (f := fun x : ℝ => Real.arctan x - x * (3 + 5 * x ^ 2) / (3 * (1 + x ^ 2) ^ 2))
    (convex_Ici 0) hcont (fun x hx => by
      have hx0 : (0 : ℝ) < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
      have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        have := hasDerivAt_pow 2 x
        simpa [pow_one, mul_comm] using this
      have hp : HasDerivAt (fun y : ℝ => 3 + 5 * y ^ 2) (10 * x) x := by
        have hc := (hasDerivAt_const x (3 : ℝ)).add (h2.const_mul 5)
        convert hc using 1 <;> first | rfl | ring
      have hnum : HasDerivAt (fun y : ℝ => y * (3 + 5 * y ^ 2))
          ((3 + 5 * x ^ 2) + x * (10 * x)) x := by
        have hm := (hasDerivAt_id x).mul hp
        convert hm using 1 <;> first | rfl | ((try simp only [id_eq]); ring)
      have hbase : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
        have hc := (hasDerivAt_const x (1 : ℝ)).add h2
        convert hc using 1 <;> first | rfl | ring
      have hden : HasDerivAt (fun y : ℝ => 3 * (1 + y ^ 2) ^ 2)
          (12 * x * (1 + x ^ 2)) x := by
        have hc := (hbase.pow 2).const_mul 3
        convert hc using 1 <;> first | rfl | ring
      have hquot : HasDerivAt
          (fun y : ℝ => y * (3 + 5 * y ^ 2) / (3 * (1 + y ^ 2) ^ 2))
          ((((3 + 5 * x ^ 2) + x * (10 * x)) * (3 * (1 + x ^ 2) ^ 2) -
            x * (3 + 5 * x ^ 2) * (12 * x * (1 + x ^ 2))) /
            (3 * (1 + x ^ 2) ^ 2) ^ 2) x :=
        hnum.div hden (by positivity)
      have hderiv := (Real.hasDerivAt_arctan x).sub hquot
      have hfun : ((Real.arctan : ℝ → ℝ) -
          (fun y : ℝ => y * (3 + 5 * y ^ 2) / (3 * (1 + y ^ 2) ^ 2))) =
          (fun y : ℝ => Real.arctan y - y * (3 + 5 * y ^ 2) / (3 * (1 + y ^ 2) ^ 2)) := by
        funext y
        rfl
      rw [hfun] at hderiv
      rw [hderiv.deriv]
      have hEq : 1 / (1 + x ^ 2) -
          ((((3 + 5 * x ^ 2) + x * (10 * x)) * (3 * (1 + x ^ 2) ^ 2) -
            x * (3 + 5 * x ^ 2) * (12 * x * (1 + x ^ 2))) /
            (3 * (1 + x ^ 2) ^ 2) ^ 2) =
          8 * x ^ 4 / (3 * (1 + x ^ 2) ^ 3) := by
        field_simp
        ring
      rw [hEq]
      positivity)
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs.le) hs
  simpa using h

/-! ## 2. `matanDD` is positive on the whole domain `(-1, ∞)` -/

/-- **`matanDD t > 0` for every `t > -1`.**  Negative branch: the landed
crossing comparison `lkB_matanDD_zero_le_of_neg` gives
`2/5 = matanDD 0 ≤ matanDD t`.  At `0`: `matanDD_zero`.  Positive branch: the
closed form `matanDD t = (3(1+t)²·matan t − (3+5t))/(4t²(1+t)²)` has positive
numerator by §1 (substituting `s = √t` into `matan t = arctan(√t)/√t`). -/
theorem lkB_matanDD_pos {t : ℝ} (ht : -1 < t) : 0 < matanDD t := by
  rcases lt_trichotomy t 0 with h | h | h
  · have hge := lkB_matanDD_zero_le_of_neg ht h
    rw [matanDD_zero] at hge
    linarith
  · subst h
    rw [matanDD_zero]
    norm_num
  · have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr h
    have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt h.le
    have hb := lkB_arctan_gt_matanDD_bound hs
    have hm : matan t = Real.arctan (Real.sqrt t) / Real.sqrt t := by
      unfold matan
      rw [if_neg (ne_of_gt h), if_pos h]
    have hstep : 3 * (1 + t) ^ 2 * matan t - (3 + 5 * t) > 0 := by
      rw [hm]
      have hpos3 : (0 : ℝ) < 3 * (1 + Real.sqrt t ^ 2) ^ 2 := by positivity
      have hmul := mul_lt_mul_of_pos_left hb hpos3
      have hcancel : 3 * (1 + Real.sqrt t ^ 2) ^ 2 *
          (Real.sqrt t * (3 + 5 * Real.sqrt t ^ 2) /
            (3 * (1 + Real.sqrt t ^ 2) ^ 2)) =
          Real.sqrt t * (3 + 5 * Real.sqrt t ^ 2) := by
        field_simp
      rw [hcancel] at hmul
      rw [hs2] at hmul
      rw [mul_comm (Real.sqrt t) (3 + 5 * t)] at hmul
      have hkey : 3 + 5 * t <
          3 * (1 + t) ^ 2 * Real.arctan (Real.sqrt t) / Real.sqrt t :=
        (lt_div_iff₀ hs).mpr hmul
      have hshape : 3 * (1 + t) ^ 2 * (Real.arctan (Real.sqrt t) / Real.sqrt t) =
          3 * (1 + t) ^ 2 * Real.arctan (Real.sqrt t) / Real.sqrt t := by
        ring
      rw [hshape]
      linarith
    have hform : matanDD t = (3 * (1 + t) ^ 2 * matan t - (3 + 5 * t)) /
        (4 * t ^ 2 * (1 + t) ^ 2) := by
      rw [matanDD_of_ne (ne_of_gt h)]
      have ht0 : t ≠ 0 := ne_of_gt h
      have h1t : (1 : ℝ) + t ≠ 0 := by linarith
      field_simp
      ring
    rw [hform]
    exact div_pos hstep (by positivity)

/-! ## 3. `matanD` is strictly increasing on `(-1, ∞)` -/

/-- **`matanD` is strictly increasing on the whole analytic domain `(-1, ∞)`**
(i.e. `matan` is strictly convex) — the monotonicity input of the mD slot
assembly, covering the fully negative, zero-crossing and positive slots alike.
Derivative `matanDD > 0` is §2; continuity at the removable-singularity point
`0` is the landed `matanD_hasDerivAt_zero`. -/
theorem lkB_matanD_strictMonoOn : StrictMonoOn matanD (Set.Ioi (-1)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi (-1)) ?_ ?_
  · intro x hx
    rw [Set.mem_Ioi] at hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact matanD_hasDerivAt_zero.continuousAt.continuousWithinAt
    · exact (matanD_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(matanD_hasDerivAt hx).deriv]
    exact lkB_matanDD_pos hx

/-- Slot-facing monotone form. -/
theorem lkB_matanD_monotoneOn : MonotoneOn matanD (Set.Ioi (-1)) :=
  lkB_matanD_strictMonoOn.monotoneOn

/-- Crossing value, negative side: `matanD t < -1/3 = matanD 0` for
`-1 < t < 0` (strict increase up to the removable-singularity value). -/
theorem lkB_matanD_lt_zero_neg {t : ℝ} (ht1 : -1 < t) (ht0 : t < 0) :
    matanD t < -(1 / 3) := by
  have h := lkB_matanD_strictMonoOn (a := t) (b := 0)
    (Set.mem_Ioi.mpr ht1) (Set.mem_Ioi.mpr (by linarith)) ht0
  rwa [matanD_zero] at h

/-- Crossing value, positive side: `-1/3 = matanD 0 < matanD t` for `0 < t`. -/
theorem lkB_matanD_gt_zero_pos {t : ℝ} (ht : 0 < t) : -(1 / 3) < matanD t := by
  have h := lkB_matanD_strictMonoOn (a := 0) (b := t)
    (Set.mem_Ioi.mpr (by linarith : (-1 : ℝ) < 0)) (Set.mem_Ioi.mpr (by linarith)) ht
  rwa [matanD_zero] at h

/-! ## 4. Point brackets (`matan` point bracket in → `matanD` point bracket out) -/

/-- Exact-rational point bracket for `matanD` at a rational `tI`, built from a
`matan` point bracket at the same `tI` through the clean form
`matanD t = (1/(2t))·(1/(1+t) − matan t)`.  Same expression as the landed
positive `gMD` (`LeafGenKit`); evaluated on point intervals the `mul`/`inv`
corners collapse, so the result is a genuine point bracket. -/
def lkBMDpt (V : QInterval) (tI : ℚ) : QInterval :=
  (((QInterval.const (1 : ℚ)).add (QInterval.const tI)).inv.sub V).mul
    (((QInterval.const (2 : ℚ)).mul (QInterval.const tI)).inv)

/-- **Branch-agnostic `matanD` point enclosure** for `-1 < tI`, `tI ≠ 0`:
a `matan` point bracket at `tI` in, the `matanD` point bracket out.  The sign
of the reciprocal corner `(2·tI)⁻¹` is discharged by `tI ≠ 0` (either
`2·tI > 0` or `2·tI < 0`), so the negative branch, the positive branch and
`t = 0` (via the exact value below) are all covered. -/
theorem lkB_matanD_pt (tI : ℚ) (V MD : QInterval) (ht1 : (-1 : ℚ) < tI) (ht0 : tI ≠ 0)
    (hV : V.mem (matan ((tI : ℚ) : ℝ))) (hMD : MD = lkBMDpt V tI) :
    MD.mem (matanD ((tI : ℚ) : ℝ)) := by
  have ht0r : ((tI : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ht0
  subst hMD
  rw [matanD_of_ne ht0r]
  have hA : ((QInterval.const (1 : ℚ)).add (QInterval.const tI)).mem
      ((1 : ℝ) + ((tI : ℚ) : ℝ)) := by
    have h := QInterval.mem_add (QInterval.mem_const (q := (1 : ℚ)))
      (QInterval.mem_const (q := tI))
    simpa using h
  have hApos : (0 : ℚ) < ((QInterval.const (1 : ℚ)).add (QInterval.const tI)).lo := by
    show (0 : ℚ) < 1 + tI
    linarith
  have hAi := QInterval.mem_inv hA (Or.inl hApos)
  have hsub := QInterval.mem_sub hAi hV
  have hB : ((QInterval.const (2 : ℚ)).mul (QInterval.const tI)).mem
      ((2 : ℝ) * ((tI : ℚ) : ℝ)) := by
    have h := QInterval.mem_mul (QInterval.mem_const (q := (2 : ℚ)))
      (QInterval.mem_const (q := tI))
    simpa using h
  have hBsign : (0 : ℚ) < ((QInterval.const (2 : ℚ)).mul (QInterval.const tI)).lo ∨
      ((QInterval.const (2 : ℚ)).mul (QInterval.const tI)).hi < 0 := by
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · right
      show max (max (2 * tI) (2 * tI)) (max (2 * tI) (2 * tI)) < 0
      simp only [max_lt_iff]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · left
      show (0 : ℚ) < min (min (2 * tI) (2 * tI)) (min (2 * tI) (2 * tI))
      simp only [lt_min_iff]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hBi := QInterval.mem_inv hB hBsign
  have hmem := QInterval.mem_mul hsub hBi
  have hveq : (1 / (2 * ((tI : ℚ) : ℝ))) *
      (1 / (1 + ((tI : ℚ) : ℝ)) - matan ((tI : ℚ) : ℝ)) =
      ((1 + ((tI : ℚ) : ℝ))⁻¹ - matan ((tI : ℚ) : ℝ)) *
        ((2 * ((tI : ℚ) : ℝ))⁻¹) := by
    simp only [one_div]
    rw [mul_comm]
  rw [hveq]
  exact hmem

/-- `matanD` at the removable singularity: the exact value `-1/3` as a point
bracket (the `t = 0` endpoint of a zero-split leaf). -/
theorem lkB_matanD_zero_mem : (QInterval.const (-(1 / 3))).mem (matanD 0) := by
  rw [matanD_zero]
  simpa using (QInterval.mem_const (q := (-(1 / 3) : ℚ)))

/-- Negative-branch `matanD` point bracket with **exact rational endpoints**:
`lkB_matan_neg_pt`'s `matan` bracket (same `ql² ≤ -tI ≤ qh²` interface) fed
through `lkBMDpt`.  This is the one-stop negative endpoint constructor for the
emitter. -/
def lkBMDneg (tI ql qh : ℚ) : QInterval :=
  lkBMDpt (QInterval.mk (lkB5r ql / ql)
    ((lkB5r qh + qh * (qh ^ 10 / (1 - qh ^ 2))) / qh)) tI

/-- Membership form of `lkBMDneg`: same hypotheses as the landed
`lkB_matan_neg_pt`. -/
theorem lkBMDneg_mem (tI ql qh : ℚ) (htm1 : -1 < tI) (ht0 : tI < 0)
    (hq0 : (0 : ℚ) < ql) (horder : ql ≤ qh) (hq1 : qh < 1)
    (hql2 : ((ql : ℚ) : ℝ) ^ 2 ≤ -((tI : ℚ) : ℝ))
    (hqh2 : -((tI : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) ^ 2) :
    (lkBMDneg tI ql qh).mem (matanD ((tI : ℚ) : ℝ)) :=
  lkB_matanD_pt tI _ _ htm1 (ne_of_lt ht0)
    (lkB_matan_neg_pt tI ql qh _ htm1 ht0 hq0 horder hq1 hql2 hqh2 rfl) rfl

/-! ## 5. mD slot assembly (endpoint point brackets + strict monotonicity) -/

/-- Increasing-function slot shape: endpoint brackets paired **in order**
(contrast `lkBMDDslot`, which is the decreasing/antitone pairing). -/
def lkBMDslot (MDl MDh : QInterval) : QInterval := QInterval.mk MDl.lo MDh.hi

/-- **Endpoint-coherent `matanD` transport, whole domain**: for
`-1 < lo ≤ t ≤ hi`, `matanD t` lies between the endpoint values in *forward*
order (the landed `lkB_matanDD_transport` is the reverse-order `matanDD`
mirror). -/
theorem lkB_matanD_transport (lo hi t : ℝ) (hm : -1 < lo) (hlt : lo ≤ t) (htu : t ≤ hi)
    (MDl MDh : QInterval) (hMDl : MDl.mem (matanD lo)) (hMDh : MDh.mem (matanD hi)) :
    (lkBMDslot MDl MDh).mem (matanD t) := by
  have htm : -1 < t := lt_of_lt_of_le hm hlt
  have hhm : -1 < hi := lt_of_lt_of_le htm htu
  have h1 : matanD lo ≤ matanD t :=
    lkB_matanD_monotoneOn (a := lo) (b := t)
      (Set.mem_Ioi.mpr hm) (Set.mem_Ioi.mpr htm) hlt
  have h2 : matanD t ≤ matanD hi :=
    lkB_matanD_monotoneOn (a := t) (b := hi)
      (Set.mem_Ioi.mpr htm) (Set.mem_Ioi.mpr hhm) htu
  rw [lkBMDslot, QInterval.mem]
  exact ⟨le_trans hMDl.1 h1, le_trans h2 hMDh.2⟩

/-- Rational-slot form of `lkB_matanD_transport`: exact-rational `t` interval
plus the two endpoint `matanD` brackets give the slot's `matanD` interval. -/
theorem lkB_matanD_slot (TI : QInterval) (MDl MDh : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (_horder : TI.lo ≤ TI.hi)
    (hMDl : MDl.mem (matanD ((TI.lo : ℚ) : ℝ)))
    (hMDh : MDh.mem (matanD ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (lkBMDslot MDl MDh).mem (matanD t) := by
  intro t h1t h2t
  exact lkB_matanD_transport _ _ t (by exact_mod_cast hm) h1t h2t MDl MDh hMDl hMDh

/-- Negative-slot specialisation (`TI.hi ≤ 0`): the shape the 204 fully
negative wt1 Route B leaves consume.  The `hz` hypothesis is documentation of
the intended face — the global monotonicity makes it unnecessary. -/
theorem lkB_matanD_slot_neg (TI : QInterval) (MDl MDh : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (horder : TI.lo ≤ TI.hi) (_hz : TI.hi ≤ 0)
    (hMDl : MDl.mem (matanD ((TI.lo : ℚ) : ℝ)))
    (hMDh : MDh.mem (matanD ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (lkBMDslot MDl MDh).mem (matanD t) :=
  lkB_matanD_slot TI MDl MDh hm horder hMDl hMDh

/-- **Endpoints-only mD slot**: the `matan` point brackets at the two slot
endpoints in, the `matanD` slot interval out (point brackets built by §4, then
§5).  This is the emitter's one-step form; `TI.hi = 0` uses the exact value
via `lkB_matanD_slot_zero_hi`. -/
theorem lkB_matanD_slot_from_matan (TI : QInterval) (Vl Vh : QInterval)
    (hm : (-1 : ℚ) < TI.lo) (horder : TI.lo ≤ TI.hi)
    (hl0 : TI.lo ≠ 0) (hh0 : TI.hi ≠ 0)
    (hVl : Vl.mem (matan ((TI.lo : ℚ) : ℝ)))
    (hVh : Vh.mem (matan ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (lkBMDslot (lkBMDpt Vl TI.lo) (lkBMDpt Vh TI.hi)).mem (matanD t) :=
  lkB_matanD_slot TI _ _ hm horder
    (lkB_matanD_pt TI.lo Vl _ hm hl0 hVl rfl)
    (lkB_matanD_pt TI.hi Vh _ (lt_of_lt_of_le hm horder) hh0 hVh rfl)

/-- Zero-split convenience: a slot `[tlo, 0]` ending at the singularity, the
upper edge being the exact value `-1/3`. -/
theorem lkB_matanD_slot_zero_hi (TI Vl : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (horder : TI.lo ≤ TI.hi) (hhi : TI.hi = 0) (hl0 : TI.lo ≠ 0)
    (hVl : Vl.mem (matan ((TI.lo : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ 0 →
      (lkBMDslot (lkBMDpt Vl TI.lo) (QInterval.const (-(1 / 3)))).mem (matanD t) := by
  have hMDl : (lkBMDpt Vl TI.lo).mem (matanD ((TI.lo : ℚ) : ℝ)) :=
    lkB_matanD_pt TI.lo Vl _ hm hl0 hVl rfl
  have hMDh : (QInterval.const (-(1 / 3))).mem (matanD ((TI.hi : ℚ) : ℝ)) := by
    rw [hhi]
    simpa using lkB_matanD_zero_mem
  have h := lkB_matanD_slot TI (lkBMDpt Vl TI.lo) (QInterval.const (-(1 / 3)))
    hm horder hMDl hMDh
  intro t h1t h2t
  exact h t h1t (by rw [hhi]; simpa using h2t)

/-- Zero-split convenience: a slot `[0, thi]` starting at the singularity,
the lower edge being the exact value `-1/3`. -/
theorem lkB_matanD_slot_zero_lo (TI Vh : QInterval) (hlo : TI.lo = 0)
    (horder : 0 ≤ TI.hi) (hh0 : TI.hi ≠ 0)
    (hVh : Vh.mem (matan ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, 0 ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (lkBMDslot (QInterval.const (-(1 / 3))) (lkBMDpt Vh TI.hi)).mem (matanD t) := by
  have hm : (-1 : ℚ) < TI.lo := by rw [hlo]; norm_num
  have hMDl : (QInterval.const (-(1 / 3))).mem (matanD ((TI.lo : ℚ) : ℝ)) := by
    rw [hlo]
    simpa using lkB_matanD_zero_mem
  have hMDh : (lkBMDpt Vh TI.hi).mem (matanD ((TI.hi : ℚ) : ℝ)) :=
    lkB_matanD_pt TI.hi Vh _ (by linarith) hh0 hVh rfl
  have h := lkB_matanD_slot TI (QInterval.const (-(1 / 3))) (lkBMDpt Vh TI.hi)
    hm (by rw [hlo]; exact horder) hMDl hMDh
  intro t h1t h2t
  exact h t (by rw [hlo]; simpa using h1t) h2t

/-! ## 6. mDD slot re-exports (same consumer shape, landed monotone transport) -/

/-- Decreasing-function slot shape (`matanDD` is antitone on `(-1, ∞)`) —
identical to the landed `LeafGenKit.gMDD`. -/
def lkBMDDslot (Dl Dh : QInterval) : QInterval := QInterval.mk Dh.lo Dl.hi

/-- `matanDD` slot assembly in the consumer shape, whole domain: endpoint
brackets in, slot interval out.  Re-export of the landed `lkB_matanDD_slot`
(`lkB_matanDD_antitoneOn`, which glues the negative branch, `matanDD 0 = 2/5`
and the positive branch) under the template name. -/
theorem lkB_mDD_slot (TI : QInterval) (Dl Dh : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (horder : TI.lo ≤ TI.hi)
    (hDl : Dl.mem (matanDD ((TI.lo : ℚ) : ℝ)))
    (hDh : Dh.mem (matanDD ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (lkBMDDslot Dl Dh).mem (matanDD t) := by
  intro t h1t h2t
  exact lkB_matanDD_slot TI hm horder Dl Dh hDl hDh t h1t h2t

/-- Negative-slot `matanDD` assembly (the 204 fully negative leaves): the
antitone direction `matanDD t ∈ [matanDD(hi).lo, matanDD(lo).hi]` comes from
the landed `AntitoneOn matanDD (Ioi (-1))`; the `hz` hypothesis documents the
face and is not needed by the global statement. -/
theorem lkB_matanDD_slot_neg (TI : QInterval) (Dl Dh : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (horder : TI.lo ≤ TI.hi) (_hz : TI.hi ≤ 0)
    (hDl : Dl.mem (matanDD ((TI.lo : ℚ) : ℝ)))
    (hDh : Dh.mem (matanDD ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (lkBMDDslot Dl Dh).mem (matanDD t) :=
  lkB_mDD_slot TI Dl Dh hm horder hDl hDh

/-- Zero-crossing `matanDD` assembly (the 51 cross-zero leaves): the negative
endpoint bracket (`Dl`, from `lkB_matan_neg_pt`) supplies the upper edge, the
positive endpoint bracket (`Dh`) the lower edge, and the crossing value
`matanDD 0 = 2/5` is supplied inside the landed `AntitoneOn` glue. -/
theorem lkB_matanDD_slot_cross (TI : QInterval) (Dl Dh : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (horder : TI.lo ≤ TI.hi) (_hzlo : TI.lo < 0) (_hzhi : (0 : ℚ) < TI.hi)
    (hDl : Dl.mem (matanDD ((TI.lo : ℚ) : ℝ)))
    (hDh : Dh.mem (matanDD ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (lkBMDDslot Dl Dh).mem (matanDD t) :=
  lkB_mDD_slot TI Dl Dh hm horder hDl hDh

/-! ## 7. Consumer shapes: negative-branch mirrors of the positive template -/

/-- **mD slot, negative/cross-zero mirror of `LeafGenKit.g_mD_vf`**: same
argument order (`TI`, endpoint brackets, order, hypotheses, slot), but the
slot is assembled from the endpoint `matanD` point brackets by monotonicity
instead of the factor-interval ops `gMD` (which are pathological here:
`lkB_matanD_ops_neg` was 0/204 on the negative leaves).  The emitter swaps the
lemma name and passes the point brackets it already builds per endpoint. -/
theorem lkB_mD_vf (TI : QInterval) (MDl MDh : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (horder : TI.lo ≤ TI.hi)
    (hMDl : MDl.mem (matanD ((TI.lo : ℚ) : ℝ)))
    (hMDh : MDh.mem (matanD ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (lkBMDslot MDl MDh).mem (matanD t) :=
  lkB_matanD_slot TI MDl MDh hm horder hMDl hMDh

/-- **mDD slot, negative/cross-zero mirror of `LeafGenKit.g_mDD_vf`**: same
argument order as the positive template (`TI`, `Dl`, `Dh`, order, hypotheses,
slot) with `-1 < TI.lo` in place of `0 < TI.lo`. -/
theorem lkB_mDD_vf (TI : QInterval) (Dl Dh : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (horder : TI.lo ≤ TI.hi)
    (hDl : Dl.mem (matanDD ((TI.lo : ℚ) : ℝ)))
    (hDh : Dh.mem (matanDD ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (lkBMDDslot Dl Dh).mem (matanDD t) :=
  lkB_mDD_slot TI Dl Dh hm horder hDl hDh

/-! ## Axiom audit (standard three only: propext / Classical.choice / Quot.sound) -/

#print axioms lkB_arctan_gt_matanDD_bound
#print axioms lkB_matanDD_pos
#print axioms lkB_matanD_strictMonoOn
#print axioms lkB_matanD_monotoneOn
#print axioms lkB_matanD_lt_zero_neg
#print axioms lkB_matanD_gt_zero_pos
#print axioms lkB_matanD_pt
#print axioms lkB_matanD_zero_mem
#print axioms lkBMDneg_mem
#print axioms lkB_matanD_transport
#print axioms lkB_matanD_slot
#print axioms lkB_matanD_slot_neg
#print axioms lkB_matanD_slot_from_matan
#print axioms lkB_matanD_slot_zero_hi
#print axioms lkB_matanD_slot_zero_lo
#print axioms lkB_mDD_slot
#print axioms lkB_matanDD_slot_neg
#print axioms lkB_matanDD_slot_cross
#print axioms lkB_mD_vf
#print axioms lkB_mDD_vf
#print axioms lkBMDpt
#print axioms lkBMDslot
#print axioms lkBMDDslot
#print axioms lkBMDneg

end Kepler.Text.TaylorSecond
