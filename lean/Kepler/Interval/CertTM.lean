/-
  Phase 5, TM0: **Taylor-model certificates** — the univariate pilot of the
  Taylor-model route (`pipeline/interval/taylor-model-design.md` §4, row TM0).

  ## What this file is

  A `TaylorM n` is a first-order Taylor model over a box: center `y`, radius
  envelope `w`, a `DInterval` enclosure `fB` of `f(y)`, per-coordinate slope
  enclosures `dfB`, and a dyadic remainder bound `err`.  The semantics
  `TaylorM.Valid` is the design doc's §1.2 verbatim (existential-slope form:
  for every `ρ` in the box there exist slopes `aᵢ ∈ dfBᵢ` with
  `|f(ρ) − f(y) − Σᵢ aᵢ·(ρᵢ − yᵢ)| ≤ err`).

  ## Design deviation (recorded in `tm0-progress.md`)

  The design's T1 route (Mathlib's `taylor_mean_remainder_bound` + a
  `Diff2OnBox` calculus) is **replaced by a purely algebraic compositional
  argument**: in the ∃-slope semantics, the validity of `+ − × √` composites
  follows from interval arithmetic and the elementary identity
  `√s − √t = (s − t)/(√s + √t)` (which gives
  `|1/(√s+√t) − 1/(2√t)| ≤ |s−t| / (8·c·√c)` for `s,t ≥ c > 0`) — no
  derivatives, no `ContDiff`, no Hessian bounds.  The route is
  dimension-free, so TM0 covers **general `n`** for the four supported node
  kinds (`const`/`var`/`neg` base cases plus `add`/`sub`/`mul`/`sqrt`);
  `abs`/`ite`/`div`/`trans` make `evalTM` return `none`.

  ## Checking layer

  Everything is kernel-computable dyadic/interval arithmetic: `checkPosTM`
  is a `Bool`, closed by `decide`; sqrt certificates (`SqrtTMP`: three
  `Dyadic.sqrtI` mantissas + two `DInterval.recip` granularities per sqrt
  node) are consumed from a list in traversal order.  The center is always
  the box midpoint, so no center data is needed.  No `sorry`, no
  `native_decide`, no new axioms.
-/
import Kepler.Interval.Cert

namespace Kepler.Interval

/-- Per-`sqrt`-node certificate bundle for `evalTM`: `slo`/`shi` are the
`Dyadic.sqrtI` mantissas for the center enclosure endpoints `fB.lo`/`fB.hi`
of the sub-model, `sc` the mantissa for `√c` where `c := fB.lo − W` is the
certified positive lower bound of the sub-expression over the box; `o1`/`o2`
are the `DInterval.recip` granularities for the slope interval
`1/(2·√f(y))` and the curvature bound `1/(8·c·√c)`. -/
structure SqrtTMP where
  slo : Int
  shi : Int
  sc : Int
  o1 : Int
  o2 : Int
  deriving Repr

/-- Per-`div`-node (reciprocal) certificate bundle for `evalTM`: `o0`/`o1`/`o2`
are the `DInterval.recip` granularities for the value enclosure `1/f(y)`, the
slope enclosure `1/f(y)²`, and the curvature bound `1/c³`.  No sqrt
certificates are needed. -/
structure InvTMP where
  o0 : Int
  o1 : Int
  o2 : Int
  deriving Repr

/-- Per-`trans`-node certificate: `o1`/`o2` are `DInterval.recip`
granularities (`ln`: slope `1/f(y)` and curvature `1/c²`; `atan`: slope
`1/(1+f(y)²)` and the exact-sup curvature endpoint value `1/(1+c²)` at the
off-band endpoint `c` (`atanCurv`); `sin`: unused).  The value
enclosure reuses the node's own `(N, out)` rung parameters via `transOn`. -/
structure TransTMP where
  o1 : Int
  o2 : Int
  deriving Repr

/-- Per-leaf TM parameters: certificate queues consumed in traversal order —
`sqrt` nodes from `sqrtCerts`, `div` nodes (reciprocal step) from
`invCerts`, `trans` nodes from `transCerts`. -/
structure TMParams where
  sqrtCerts : List SqrtTMP
  invCerts : List InvTMP
  transCerts : List TransTMP
  deriving Repr

/-- Empty parameter bundle (expressions without `sqrt`/`div`/`trans` nodes). -/
def TMParams.empty : TMParams := ⟨[], [], []⟩

/-- First-order Taylor model over a box (design doc §1.2). -/
structure TaylorM (n : ℕ) where
  /-- Center point (in the box; `evalTM` always uses the midpoint). -/
  y : Fin n → Dyadic
  /-- Cell radius envelope: `max (yᵢ − loᵢ, hiᵢ − yᵢ) ≤ wᵢ`. -/
  w : Fin n → Dyadic
  /-- Enclosure of `f(y)`. -/
  fB : DInterval
  /-- Slope enclosures (existential slopes, not derivatives). -/
  dfB : Fin n → DInterval
  /-- Remainder bound (semantically `≥ 0` whenever the model is valid). -/
  err : Dyadic

namespace Dyadic

@[simp] theorem toReal_zero : (⟨0, 0⟩ : Dyadic).toReal = 0 := by
  rw [toReal_def]; norm_num

@[simp] theorem toReal_one : (⟨1, 0⟩ : Dyadic).toReal = 1 := by
  rw [toReal_def]; norm_num

theorem toReal_two : (⟨2, 0⟩ : Dyadic).toReal = 2 := by
  rw [toReal_def]; norm_num

theorem toReal_eight : (⟨8, 0⟩ : Dyadic).toReal = 8 := by
  rw [toReal_def]; norm_num

/-- Ceiling-chop to exponent `e₀`: no-op when `e₀ ≤ d.e`; otherwise drop the
low `d.e − e₀` mantissa bits, rounding the mantissa UP (`⌈m/2^k⌉` via floored
division).  Sound one-sided relaxation for upper-bound quantities (`err`,
`W`): the value only grows.  Kernel- and VM-cheap: `Int` arithmetic only, no
bit-length computation. -/
def chopCeilTo (d : Dyadic) (e₀ : Int) : Dyadic :=
  if e₀ ≤ d.e then d
  else ⟨(d.m + 2 ^ (e₀ - d.e).toNat - 1) / 2 ^ (e₀ - d.e).toNat, e₀⟩

/-- **Soundness of `chopCeilTo`**: the chopped value dominates. -/
theorem toReal_le_chopCeilTo (d : Dyadic) (e₀ : Int) :
    d.toReal ≤ (d.chopCeilTo e₀).toReal := by
  unfold chopCeilTo
  split_ifs with hlt
  · exact le_rfl
  · have hki : 0 < e₀ - d.e := by omega
    set k := (e₀ - d.e).toNat with hkdef
    have hkZ : (k : ℤ) = e₀ - d.e := Int.toNat_of_nonneg (by omega)
    have hq : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
    have hdec := Int.mul_ediv_add_emod (d.m + 2 ^ k - 1) (2 ^ k : ℤ)
    rw [mul_comm] at hdec
    have hmod0 := Int.emod_nonneg (d.m + 2 ^ k - 1) (ne_of_gt hq)
    have hmodlt := Int.emod_lt_of_pos (d.m + 2 ^ k - 1) hq
    have h1 : d.m ≤ ((d.m + 2 ^ k - 1) / (2 ^ k : ℤ)) * (2 ^ k : ℤ) := by omega
    have h1r : (d.m : ℝ) ≤ ((((d.m + 2 ^ k - 1) / (2 ^ k : ℤ)) * (2 ^ k : ℤ) : ℤ) : ℝ) :=
      Int.cast_le.mpr h1
    have hscale : (2 : ℝ) ^ k * (2 : ℝ) ^ d.e = (2 : ℝ) ^ e₀ := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), hkZ,
        sub_add_cancel]
    show d.toReal ≤ Dyadic.toReal ⟨(d.m + 2 ^ k - 1) / 2 ^ k, e₀⟩
    rw [toReal_def, toReal_def]
    calc (d.m : ℝ) * (2 : ℝ) ^ d.e
        ≤ ((((d.m + 2 ^ k - 1) / (2 ^ k : ℤ)) * (2 ^ k : ℤ) : ℤ) : ℝ) * (2 : ℝ) ^ d.e :=
        mul_le_mul_of_nonneg_right h1r (zpow_nonneg (by norm_num) _)
      _ = (((d.m + 2 ^ k - 1) / (2 ^ k : ℤ) : ℤ) : ℝ) * (2 : ℝ) ^ e₀ := by
        push_cast
        rw [mul_assoc, hscale]

/-- `toReal` distributes over a `foldl` of `Dyadic.add`. -/
theorem toReal_foldl_add {α : Type*} (l : List α) (g : α → Dyadic) (init : Dyadic) :
    (l.foldl (fun a i => a.add (g i)) init).toReal
      = init.toReal + (l.map fun i => (g i).toReal).sum := by
  induction l generalizing init with
  | nil => simp
  | cons i l ih =>
      rw [List.foldl_cons, ih (init.add (g i)), toReal_add, List.map_cons, List.sum_cons]
      ring

/-- The lower endpoint of a successful `sqrtI` certificate is nonnegative. -/
theorem sqrtI_lo_nonneg {d : Dyadic} {s : Int} {I : DInterval}
    (h : d.sqrtI s = some I) : 0 ≤ I.lo.toReal := by
  obtain ⟨hs0, _, _, _⟩ := sqrtI_cases h
  unfold sqrtI at h
  split at h
  · next _ =>
      obtain rfl : I = ⟨⟨s, d.e / 2⟩, ⟨s + 1, d.e / 2⟩⟩ := (Option.some.inj h).symm
      show 0 ≤ Dyadic.toReal ⟨s, d.e / 2⟩
      rw [toReal_def]
      exact mul_nonneg (by exact_mod_cast hs0) (zpow_nonneg (by norm_num) _)
  · exact absurd h (by simp)

end Dyadic

/-- The curvature band threshold `5/8`: `5/8 ≥ 1/√3` (since `25/64 ≥ 1/3`),
so `2|x|/(1+x²)²` is antitone in `|x|` beyond it. -/
def atanCurvBand : Dyadic := ⟨5, -3⟩

/-- **Exact-sup curvature coefficient** for the `arctan` trans rule: a dyadic
`C` with `2|x|/(1+x²)² ≤ C` on the whole value range `[rLo, rHi]` of `f` over
the box.  When the range lies entirely off the band `[-5/8, 5/8]`, `C` is the
endpoint curvature `2c/(1+c²)²` at the endpoint `c` closest to `0` (one kernel
`DInterval.recip` at granularity `o2`, plus exact dyadic squares); otherwise
the global cap `7/8`. -/
def atanCurv (rLo rHi : Dyadic) (o2 : Int) : Dyadic :=
  if Dyadic.ble rHi (-atanCurvBand) then
    match DInterval.recip ⟨(⟨1, 0⟩ : Dyadic).add ((-rHi).mul (-rHi)),
        (⟨1, 0⟩ : Dyadic).add ((-rHi).mul (-rHi))⟩ o2 with
    | some Jc => ((⟨2, 0⟩ : Dyadic).mul (-rHi)).mul (Jc.hi.mul Jc.hi)
    | none => ⟨7, -3⟩
  else if Dyadic.ble atanCurvBand rLo then
    match DInterval.recip ⟨(⟨1, 0⟩ : Dyadic).add (rLo.mul rLo),
        (⟨1, 0⟩ : Dyadic).add (rLo.mul rLo)⟩ o2 with
    | some Jc => ((⟨2, 0⟩ : Dyadic).mul rLo).mul (Jc.hi.mul Jc.hi)
    | none => ⟨7, -3⟩
  else ⟨7, -3⟩


namespace TaylorM

/-- Model of `-f`. -/
def neg {n : ℕ} (M : TaylorM n) : TaylorM n :=
  ⟨M.y, M.w, M.fB.neg, fun i => (M.dfB i).neg, M.err⟩

/-- Model of `f + g` (same center/envelope, errors add). -/
def add {n : ℕ} (Mf Mg : TaylorM n) : TaylorM n :=
  ⟨Mf.y, Mf.w, Mf.fB.add Mg.fB, fun i => (Mf.dfB i).add (Mg.dfB i),
    Mf.err.add Mg.err⟩

/-- Model of `f − g`. -/
def sub {n : ℕ} (Mf Mg : TaylorM n) : TaylorM n :=
  Mf.add Mg.neg

/-- Linear amplitude bound `Σᵢ |dfBᵢ|.abs.hi · wᵢ` (without the remainder). -/
def W0 {n : ℕ} (M : TaylorM n) : Dyadic :=
  (List.finRange n).foldl (fun a i => a.add ((M.dfB i).abs.hi.mul (M.w i))) ⟨0, 0⟩

/-- Amplitude bound `max (W0 + err) 0`: valid models satisfy
`|f(ρ) − f(y)| ≤ W.toReal` on the box. -/
def W {n : ℕ} (M : TaylorM n) : Dyadic :=
  Dyadic.dmax (M.W0.add M.err) ⟨0, 0⟩

/-- The err-chop scale reference: twice the coarsest envelope exponent, minus
24 bits of slack (chopping is a sound upward relaxation; without it the
`W²`/`c³` remainder terms square mantissa sizes along deep chains — the
BIXPCGW-probe performance wall, `tm2-progress.md` §3). -/
def errScale {n : ℕ} (M : TaylorM n) : Int :=
  match n with
  | 0 => M.err.e
  | n + 1 =>
      ((List.finRange (n + 1)).foldl (fun a i => min a (M.w i).e)
        (M.w ⟨0, Nat.zero_lt_succ _⟩).e) * 2 - 24

/-- Model of `f · g`.  Remainder: with `r_f = f − f_y − L_f`,
`fg − f_yg_y − Σᵢ(a_fᵢ g_y + f_y a_gᵢ)uᵢ
  = L_f L_g + r_f (g_y + L_g + r_g) + r_g (f_y + L_f)`, bounded by
`W̃f·W̃g + err_f·(|gB| + W̃g + err_g) + err_g·(|fB| + W̃f)` where
`W̃ := W0`. -/
def mul {n : ℕ} (Mf Mg : TaylorM n) : TaylorM n :=
  ⟨Mf.y, Mf.w, Mf.fB.mul Mg.fB,
    fun i => ((Mf.dfB i).mul Mg.fB).add (Mf.fB.mul (Mg.dfB i)),
    ((Mf.W0.mul Mg.W0).add
      ((Mf.err.mul ((Mg.fB.abs.hi.add Mg.W0).add Mg.err)).add
        (Mg.err.mul (Mf.fB.abs.hi.add Mf.W0)))).chopCeilTo Mf.errScale⟩

/-- Model of `√f`, certificate-based.  `none` (safe failure) when the
certified lower bound `c := fB.lo − W` of `f` over the box is not positive or
any certificate check fails.  Remainder: with `q = 1/(2·√f(y))`,
`√f(ρ) − √f(y) − q·Σaᵢuᵢ
  = Δf·(1/(√f(ρ)+√f(y)) − q) + q·(Δf − Σaᵢuᵢ)`; the first term is bounded by
`W²/(8·c·√c)` (`sqrt_slope_diff`), the second by `err·q ≤ err·J.hi`. -/
def sqrt {n : ℕ} (M : TaylorM n) (p : SqrtTMP) : Option (TaylorM n) :=
  if (M.fB.lo.add (-M.W)).isPos = true then
    (Dyadic.sqrtI M.fB.lo p.slo).bind fun Jl =>
    (Dyadic.sqrtI M.fB.hi p.shi).bind fun Jh =>
    (Dyadic.sqrtI (M.fB.lo.add (-M.W)) p.sc).bind fun Jc =>
    (DInterval.recip ⟨(⟨2, 0⟩ : Dyadic).mul Jl.lo, (⟨2, 0⟩ : Dyadic).mul Jh.hi⟩
      p.o1).bind fun J =>
    (DInterval.recip
      ⟨(⟨8, 0⟩ : Dyadic).mul ((M.fB.lo.add (-M.W)).mul Jc.lo),
       (⟨8, 0⟩ : Dyadic).mul ((M.fB.lo.add (-M.W)).mul Jc.lo)⟩ p.o2).map fun K =>
    ⟨M.y, M.w, ⟨Jl.lo, Jh.hi⟩, fun i => (M.dfB i).mul J,
      ((M.err.mul J.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo M.errScale⟩
  else none

/-- Shared computation of `inv` once a positive lower bound `c` of `|f|` over
the box is certified. -/
def invCore {n : ℕ} (M : TaylorM n) (c : Dyadic) (p : InvTMP) : Option (TaylorM n) :=
  (DInterval.recip M.fB p.o0).bind fun V =>
  (DInterval.recip ⟨c.mul c, M.fB.abs.hi.mul M.fB.abs.hi⟩ p.o1).bind fun Jp =>
  (DInterval.recip ⟨c.mul (c.mul c), c.mul (c.mul c)⟩ p.o2).map fun K =>
  ⟨M.y, M.w, V, fun i => (M.dfB i).mul Jp.neg,
    ((M.err.mul Jp.abs.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo M.errScale⟩

/-- Model of `1/f`, certificate-light (granularities only).  `c` is a
certified lower bound of `|f|` over the box: `fB.lo − W` when positive, else
`−(fB.hi + W)` when positive, else `none` (safe failure).  Remainder: from
`1/s − 1/t = (t−s)/(s·t)` and `q := −1/f(y)²`,
`1/f(ρ) − 1/f(y) − q·Δf = Δf²/(f(ρ)·f(y)²)`, bounded by `W²/c³`; the
`q·(Δf − Σaᵢuᵢ)` part is bounded by `err·|q| ≤ err·Jp.abs.hi` where `Jp ∋
1/f(y)²`. -/
def inv {n : ℕ} (M : TaylorM n) (p : InvTMP) : Option (TaylorM n) :=
  let cpos := M.fB.lo.add (-M.W)
  let cneg := -(M.fB.hi.add M.W)
  if cpos.isPos = true then M.invCore cpos p
  else if cneg.isPos = true then M.invCore cneg p
  else none

/-- Model of `g ∘ f` for `g ∈ {sin, arctan, log}` (`cos` falls through to
`none` — the hybrid evaluator falls back to the zero-order model).  The value
enclosure `V` reuses the node's own rung `(N, out)` via `transOn` on the
center enclosure.  Curvature constants (design §1.3, elementary forms proved
in `sin_residual`/`log_residual`/`arctan_residual_sup`):
`sin: W²/2 + W³/4`; `ln: W²/c²` with `c := fB.lo − W > 0`;
`atan: W²·C` with `C := min(atanCurv (fB.lo−W) (fB.hi+W) p.o2) (2·(|fB|+W))`
— the exact-sup curvature coefficient over the whole value range of `f` on
the box (`atanCurv_sound`): the endpoint curvature `2c/(1+c²)²` (c the
off-band endpoint closest to 0) when the range misses `[-5/8, 5/8]`, else
the global cap `7/8` (true peak `3√3/8 ≈ 0.65`), each dominating the legacy
`2·(|fB|+W)` cap.  This is the 549 final formula (arctanK err was 98% of
root err on the 99 NEG straddle leaves, ~15× over-certified). -/
def trans {n : ℕ} (k : TKind) (M : TaylorM n) (N : ℕ) (out : Int) (p : TransTMP) :
    Option (TaylorM n) :=
  match k with
  | .sinK =>
      (transOn .sinK ⟨M.fB.lo, M.fB.hi⟩ N out).bind fun V =>
      (transOn .cosK ⟨M.fB.lo, M.fB.hi⟩ N out).map fun J =>
      ⟨M.y, M.w, V, fun i => (M.dfB i).mul J,
        ((M.err.mul J.abs.hi).add
          (((M.W.mul M.W).mul ⟨1, -1⟩).add
            ((M.W.mul (M.W.mul M.W)).mul ⟨1, -2⟩))).chopCeilTo M.errScale⟩
  | .cosK => none
  | .arctanK =>
      (transOn .arctanK ⟨M.fB.lo, M.fB.hi⟩ N out).bind fun V =>
      (DInterval.recip ⟨(⟨1, 0⟩ : Dyadic).add (M.fB.abs.lo.mul M.fB.abs.lo),
        (⟨1, 0⟩ : Dyadic).add (M.fB.abs.hi.mul M.fB.abs.hi)⟩ p.o1).map fun J =>
      ⟨M.y, M.w, V, fun i => (M.dfB i).mul J,
        ((M.err.mul J.abs.hi).add
          ((M.W.mul M.W).mul (Dyadic.dmin
            (atanCurv (M.fB.lo.add (-M.W)) (M.fB.hi.add M.W) p.o2)
            ((⟨2, 0⟩ : Dyadic).mul (M.fB.abs.hi.add M.W))))).chopCeilTo M.errScale⟩
  | .lnK =>
      if (M.fB.lo.add (-M.W)).isPos = true then
        (transOn .lnK ⟨M.fB.lo, M.fB.hi⟩ N out).bind fun V =>
        (DInterval.recip M.fB p.o1).bind fun J =>
        (DInterval.recip ⟨(M.fB.lo.add (-M.W)).mul (M.fB.lo.add (-M.W)),
          (M.fB.lo.add (-M.W)).mul (M.fB.lo.add (-M.W))⟩ p.o2).map fun K =>
        ⟨M.y, M.w, V, fun i => (M.dfB i).mul J,
          ((M.err.mul J.abs.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo M.errScale⟩
      else none

/-- Taylor lower bound over the box: `fB.lo + Σᵢ (dfBᵢ · [loᵢ−yᵢ, hiᵢ−yᵢ]).lo
− err`.  A linear polynomial is minimized coordinatewise at endpoints. -/
def loBound {n : ℕ} (M : TaylorM n) (box : Fin n → DInterval) : Dyadic :=
  ((List.finRange n).foldl
    (fun a i => a.add
      (((M.dfB i).mul ⟨(box i).lo.add (-(M.y i)), (box i).hi.add (-(M.y i))⟩).lo))
    M.fB.lo).add (-M.err)

/-- **Validity semantics** (design doc §1.2 verbatim): the center is in the
box, the envelope dominates both half-distances, `fB` contains `f(y)`, and
for every `ρ` in the box there exist slopes `aᵢ ∈ dfBᵢ` with the linear
approximation error bounded by `err`. -/
def Valid {n : ℕ} (M : TaylorM n) (box : Fin n → DInterval)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ i, (box i).mem (M.y i).toReal) ∧
  (∀ i, |(M.y i).toReal - (box i).lo.toReal| ≤ (M.w i).toReal ∧
        |(box i).hi.toReal - (M.y i).toReal| ≤ (M.w i).toReal) ∧
  (M.fB.mem (f fun i => (M.y i).toReal)) ∧
  ∀ ρ, boxMem box ρ → ∃ a : Fin n → ℝ,
    (∀ i, (M.dfB i).mem (a i)) ∧
    |f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)|
      ≤ M.err.toReal

/-- Bridge: a mapped sum over `List.finRange n` is the `Finset` sum over
`Fin n`. -/
theorem sum_finRange_map {n : ℕ} (g : Fin n → ℝ) :
    ((List.finRange n).map g).sum = ∑ i, g i := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]

/-- `W0` unfolds to the sum of per-coordinate amplitude bounds. -/
theorem W0_toReal {n : ℕ} (M : TaylorM n) :
    M.W0.toReal = ∑ i, ((M.dfB i).abs.hi.toReal * (M.w i).toReal) := by
  unfold W0
  rw [Dyadic.toReal_foldl_add, Dyadic.toReal_zero, zero_add, sum_finRange_map]
  simp [Dyadic.toReal_mul]

theorem W_nonneg {n : ℕ} (M : TaylorM n) : 0 ≤ M.W.toReal := by
  show 0 ≤ (Dyadic.dmax (M.W0.add M.err) ⟨0, 0⟩).toReal
  rw [Dyadic.toReal_dmax, Dyadic.toReal_zero]
  exact le_max_right _ _

namespace Valid

/-- The displacement `ρ − y` is dominated by the envelope. -/
theorem abs_sub_le_w {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f)
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) (i : Fin n) :
    |ρ i - (M.y i).toReal| ≤ (M.w i).toReal := by
  obtain ⟨_, hw, _, _⟩ := hV
  have h1 := abs_le.mp (hw i).1
  have h2 := abs_le.mp (hw i).2
  have h3 := (hρ i).1
  have h4 := (hρ i).2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3, h4]

theorem w_nonneg {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) (i : Fin n) :
    0 ≤ (M.w i).toReal := by
  obtain ⟨_, hw, _, _⟩ := hV
  exact le_trans (abs_nonneg _) (hw i).1

/-- The remainder bound of a valid model is nonnegative (evaluate the
remainder at `ρ = y`). -/
theorem err_nonneg {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) : 0 ≤ M.err.toReal := by
  obtain ⟨hmem, _, _, hrem⟩ := hV
  obtain ⟨a, _, hbound⟩ := hrem _ (fun i => hmem i)
  have h0 : (∑ i, a i * ((M.y i).toReal - (M.y i).toReal)) = 0 := by
    exact Finset.sum_eq_zero fun i _ => by rw [sub_self, mul_zero]
  rw [h0, sub_zero, sub_self, abs_zero] at hbound
  exact hbound

/-- Slope magnitude bound: `|aᵢ| ≤ (dfBᵢ).abs.hi` for any witnessed slope. -/
theorem dfB_abs_hi_nonneg {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) (i : Fin n) :
    0 ≤ (M.dfB i).abs.hi.toReal := by
  obtain ⟨hmem, _, _, hrem⟩ := hV
  obtain ⟨a, ha, _⟩ := hrem _ (fun i => hmem i)
  exact le_trans (abs_nonneg _) (DInterval.mem_abs (ha i)).2

theorem W0_nonneg {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) : 0 ≤ M.W0.toReal := by
  rw [W0_toReal]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hV.dfB_abs_hi_nonneg i) (hV.w_nonneg i)

/-- The linear part is bounded by `W0`. -/
theorem abs_linear_le_W0 {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f)
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) {a : Fin n → ℝ}
    (ha : ∀ i, (M.dfB i).mem (a i)) :
    |∑ i, a i * (ρ i - (M.y i).toReal)| ≤ M.W0.toReal := by
  calc |∑ i, a i * (ρ i - (M.y i).toReal)|
      ≤ ∑ i, |a i * (ρ i - (M.y i).toReal)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((M.dfB i).abs.hi.toReal * (M.w i).toReal) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (DInterval.mem_abs (ha i)).2 (hV.abs_sub_le_w hρ i)
          (abs_nonneg _) (hV.dfB_abs_hi_nonneg i)
    _ = M.W0.toReal := (W0_toReal M).symm

/-- The amplitude bound: `|f(ρ) − f(y)| ≤ W` on the box. -/
theorem abs_sub_le_W {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f)
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) {a : Fin n → ℝ}
    (ha : ∀ i, (M.dfB i).mem (a i))
    (hrem : |f ρ - f (fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)|
      ≤ M.err.toReal) :
    |f ρ - f (fun i => (M.y i).toReal)| ≤ M.W.toReal := by
  have hlin := hV.abs_linear_le_W0 hρ ha
  have hdecomp : f ρ - f (fun i => (M.y i).toReal)
      = (f ρ - f (fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal))
        + ∑ i, a i * (ρ i - (M.y i).toReal) := by ring
  have h1 : |f ρ - f (fun i => (M.y i).toReal)| ≤ M.err.toReal + M.W0.toReal := by
    rw [hdecomp]
    exact le_trans (abs_add_le _ _) (add_le_add hrem hlin)
  have h2 : M.err.toReal + M.W0.toReal ≤ M.W.toReal := by
    show M.err.toReal + M.W0.toReal ≤ (Dyadic.dmax (M.W0.add M.err) ⟨0, 0⟩).toReal
    rw [Dyadic.toReal_dmax, Dyadic.toReal_add, Dyadic.toReal_zero]
    exact le_max_of_le_left (le_of_eq (add_comm _ _))
  linarith

end Valid

end TaylorM

/-! ## Box center, envelope, and cell well-formedness -/

/-- The evaluation center: the exact dyadic midpoint of each box side. -/
def boxCenter {n : ℕ} (box : Fin n → DInterval) (i : Fin n) : Dyadic := (box i).mid

/-- The envelope: `max (mid − lo, hi − mid)` per coordinate. -/
def boxW {n : ℕ} (box : Fin n → DInterval) (i : Fin n) : Dyadic :=
  Dyadic.dmax ((boxCenter box i).add (-(box i).lo)) ((box i).hi.add (-(boxCenter box i)))

/-- Cell well-formedness: midpoint in the box, envelope dominates both
half-distances (the first two conjuncts of `TaylorM.Valid`, specialized to
the midpoint center). -/
def CellOK {n : ℕ} (box : Fin n → DInterval) : Prop :=
  ∀ i, ((box i).mem (boxCenter box i).toReal) ∧
    |(boxCenter box i).toReal - (box i).lo.toReal| ≤ (boxW box i).toReal ∧
    |(box i).hi.toReal - (boxCenter box i).toReal| ≤ (boxW box i).toReal

theorem cellOK_of_wf {n : ℕ} {box : Fin n → DInterval}
    (hwf : ∀ i, (box i).wf = true) : CellOK box := by
  intro i
  have hle := DInterval.le_toReal_of_wf (hwf i)
  have hmid := DInterval.toReal_mid (box i)
  have hc_eq : (boxCenter box i).toReal = (box i).mid.toReal := rfl
  have hW : (boxW box i).toReal
      = max ((box i).mid.toReal - (box i).lo.toReal)
        ((box i).hi.toReal - (box i).mid.toReal) := by
    show (Dyadic.dmax ((box i).mid.add (-(box i).lo)) ((box i).hi.add (-(box i).mid))).toReal = _
    rw [Dyadic.toReal_dmax, Dyadic.toReal_add, Dyadic.toReal_neg, Dyadic.toReal_add,
      Dyadic.toReal_neg, sub_eq_add_neg, sub_eq_add_neg]
  have hc : (box i).mid.toReal = ((box i).lo.toReal + (box i).hi.toReal) / 2 := by linarith
  rw [hc_eq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linarith
  · linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ (box i).mid.toReal - (box i).lo.toReal), hW]
    exact le_max_left _ _
  · rw [abs_of_nonneg (by linarith : 0 ≤ (box i).hi.toReal - (box i).mid.toReal), hW]
    exact le_max_right _ _

/-! ## Compositional validity lemmas -/

/-- The constant model used by `evalTM`. -/
def constTM {n : ℕ} (box : Fin n → DInterval) (d : Dyadic) : TaylorM n :=
  ⟨boxCenter box, boxW box, ⟨d, d⟩, fun _ => ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨0, 0⟩⟩

/-- The variable model used by `evalTM`. -/
def varTM {n : ℕ} (box : Fin n → DInterval) (k : Fin n) : TaylorM n :=
  ⟨boxCenter box, boxW box, ⟨boxCenter box k, boxCenter box k⟩,
    fun i => if i = k then ⟨⟨1, 0⟩, ⟨1, 0⟩⟩ else ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨0, 0⟩⟩

theorem valid_const {n : ℕ} {box : Fin n → DInterval} (hcell : CellOK box) (d : Dyadic) :
    (constTM box d).Valid box (fun _ => d.toReal) := by
  refine ⟨fun i => (hcell i).1, fun i => (hcell i).2, ⟨le_rfl, le_rfl⟩, ?_⟩
  intro ρ _
  refine ⟨fun _ => 0, fun i => ?_, ?_⟩
  · show (⟨⟨0, 0⟩, ⟨0, 0⟩⟩ : DInterval).mem (0 : ℝ)
    exact ⟨by simp, by simp⟩
  · have h0 : (∑ i, (0 : ℝ) * (ρ i - ((constTM box d).y i).toReal)) = 0 := by
      exact Finset.sum_eq_zero fun i _ => by rw [zero_mul]
    rw [h0]
    show |d.toReal - d.toReal - 0| ≤ (⟨0, 0⟩ : Dyadic).toReal
    rw [sub_self, sub_zero, abs_zero, Dyadic.toReal_zero]

theorem valid_var {n : ℕ} {box : Fin n → DInterval} (hcell : CellOK box) (k : Fin n) :
    (varTM box k).Valid box (fun ρ => ρ k) := by
  refine ⟨fun i => (hcell i).1, fun i => (hcell i).2, ⟨le_rfl, le_rfl⟩, ?_⟩
  intro ρ _
  refine ⟨fun i => if i = k then (1 : ℝ) else 0, fun i => ?_, ?_⟩
  · show (if i = k then (⟨⟨1, 0⟩, ⟨1, 0⟩⟩ : DInterval) else ⟨⟨0, 0⟩, ⟨0, 0⟩⟩).mem
      (if i = k then (1 : ℝ) else 0)
    by_cases h : i = k
    · rw [if_pos h, if_pos h]
      exact ⟨by simp, by simp⟩
    · rw [if_neg h, if_neg h]
      exact ⟨by simp, by simp⟩
  · have hsum : (∑ i, (if i = k then (1 : ℝ) else 0) * (ρ i - ((varTM box k).y i).toReal))
        = ρ k - (boxCenter box k).toReal := by
      have hpt : ∀ i, (if i = k then (1 : ℝ) else 0) * (ρ i - ((varTM box k).y i).toReal)
          = if i = k then (ρ i - (boxCenter box i).toReal) else 0 := by
        intro i
        by_cases h : i = k
        · subst h
          rw [if_pos rfl, if_pos rfl, one_mul]
          rfl
        · rw [if_neg h, if_neg h, zero_mul]
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_ite_eq']
      simp
    rw [hsum]
    show |ρ k - (boxCenter box k).toReal - (ρ k - (boxCenter box k).toReal)|
      ≤ (⟨0, 0⟩ : Dyadic).toReal
    rw [sub_self, abs_zero, Dyadic.toReal_zero]

theorem valid_neg {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) :
    (M.neg).Valid box (fun ρ => -f ρ) := by
  obtain ⟨hmem, hw, hfB, hrem⟩ := hV
  refine ⟨hmem, hw, DInterval.mem_neg hfB, ?_⟩
  intro ρ hρ
  obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
  refine ⟨fun i => -a i, fun i => DInterval.mem_neg (ha i), ?_⟩
  have hsum : (∑ i, -a i * (ρ i - (M.y i).toReal))
      = -(∑ i, a i * (ρ i - (M.y i).toReal)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  show |-f ρ - -f (fun i => (M.y i).toReal)
      - ∑ i, -a i * (ρ i - (M.y i).toReal)| ≤ M.err.toReal
  rw [hsum]
  have : -f ρ - -f (fun i => (M.y i).toReal) - -(∑ i, a i * (ρ i - (M.y i).toReal))
      = -(f ρ - f (fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)) := by ring
  rw [this, abs_neg]
  exact hbound

theorem valid_add {n : ℕ} {Mf Mg : TaylorM n} {box : Fin n → DInterval}
    {f g : (Fin n → ℝ) → ℝ}
    (hf : Mf.Valid box f) (hg : Mg.Valid box g)
    (hy : Mf.y = Mg.y) (_hw : Mf.w = Mg.w) :
    (Mf.add Mg).Valid box (fun ρ => f ρ + g ρ) := by
  obtain ⟨hfmem, hfw, hfB, hfrem⟩ := hf
  obtain ⟨_, _, hgB, hgrem⟩ := hg
  have hgB' : Mg.fB.mem (g fun i => (Mf.y i).toReal) := by rw [hy]; exact hgB
  refine ⟨hfmem, hfw, DInterval.mem_add hfB hgB', ?_⟩
  intro ρ hρ
  obtain ⟨af, haf, hbf⟩ := hfrem ρ hρ
  obtain ⟨ag, hag, hbg0⟩ := hgrem ρ hρ
  have hbg : |g ρ - g (fun i => (Mf.y i).toReal)
      - ∑ i, ag i * (ρ i - (Mf.y i).toReal)| ≤ Mg.err.toReal := by
    rw [hy]; exact hbg0
  refine ⟨fun i => af i + ag i, fun i => DInterval.mem_add (haf i) (hag i), ?_⟩
  have hsum : (∑ i, (af i + ag i) * (ρ i - (Mf.y i).toReal))
      = (∑ i, af i * (ρ i - (Mf.y i).toReal)) + (∑ i, ag i * (ρ i - (Mf.y i).toReal)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  show |f ρ + g ρ - (f (fun i => (Mf.y i).toReal) + g (fun i => (Mf.y i).toReal))
      - ∑ i, (af i + ag i) * (ρ i - (Mf.y i).toReal)| ≤ (Mf.add Mg).err.toReal
  rw [hsum]
  have hdecomp : f ρ + g ρ - (f (fun i => (Mf.y i).toReal) + g (fun i => (Mf.y i).toReal))
      - ((∑ i, af i * (ρ i - (Mf.y i).toReal)) + (∑ i, ag i * (ρ i - (Mf.y i).toReal)))
      = (f ρ - f (fun i => (Mf.y i).toReal) - ∑ i, af i * (ρ i - (Mf.y i).toReal))
        + (g ρ - g (fun i => (Mf.y i).toReal) - ∑ i, ag i * (ρ i - (Mf.y i).toReal)) := by ring
  rw [hdecomp]
  show _ ≤ (Mf.err.add Mg.err).toReal
  rw [Dyadic.toReal_add]
  exact le_trans (abs_add_le _ _) (add_le_add hbf hbg)

theorem valid_sub {n : ℕ} {Mf Mg : TaylorM n} {box : Fin n → DInterval}
    {f g : (Fin n → ℝ) → ℝ}
    (hf : Mf.Valid box f) (hg : Mg.Valid box g)
    (hy : Mf.y = Mg.y) (hw : Mf.w = Mg.w) :
    (Mf.sub Mg).Valid box (fun ρ => f ρ - g ρ) := by
  have h1 := valid_neg hg
  have h2 := valid_add hf h1 hy hw
  exact h2

theorem valid_mul {n : ℕ} {Mf Mg : TaylorM n} {box : Fin n → DInterval}
    {f g : (Fin n → ℝ) → ℝ}
    (hf : Mf.Valid box f) (hg : Mg.Valid box g)
    (hy : Mf.y = Mg.y) (_hw : Mf.w = Mg.w) :
    (Mf.mul Mg).Valid box (fun ρ => f ρ * g ρ) := by
  have hf0 := hf
  have hg0 := hg
  obtain ⟨hfmem, hfw, hfB, hfrem⟩ := hf
  obtain ⟨_, _, hgB, hgrem⟩ := hg
  have hgB' : Mg.fB.mem (g fun i => (Mf.y i).toReal) := by rw [hy]; exact hgB
  refine ⟨hfmem, hfw, DInterval.mem_mul hfB hgB', ?_⟩
  intro ρ hρ
  obtain ⟨af, haf, hbf⟩ := hfrem ρ hρ
  obtain ⟨ag, hag, hbg0⟩ := hgrem ρ hρ
  have hbg : |g ρ - g (fun i => (Mf.y i).toReal)
      - ∑ i, ag i * (ρ i - (Mf.y i).toReal)| ≤ Mg.err.toReal := by
    rw [hy]; exact hbg0
  refine ⟨fun i => af i * g (fun i => (Mf.y i).toReal)
      + f (fun i => (Mf.y i).toReal) * ag i, fun i => ?_, ?_⟩
  · show (((Mf.dfB i).mul Mg.fB).add (Mf.fB.mul (Mg.dfB i))).mem _
    exact DInterval.mem_add (DInterval.mem_mul (haf i) hgB') (DInterval.mem_mul hfB (hag i))
  · have hLf : |∑ i, af i * (ρ i - (Mf.y i).toReal)| ≤ Mf.W0.toReal :=
      TaylorM.Valid.abs_linear_le_W0 hf0 hρ haf
    have hLg : |∑ i, ag i * (ρ i - (Mf.y i).toReal)| ≤ Mg.W0.toReal := by
      have h := TaylorM.Valid.abs_linear_le_W0 hg0 hρ hag
      rwa [← hy] at h
    have hWf0 : 0 ≤ Mf.W0.toReal := TaylorM.Valid.W0_nonneg hf0
    have hWg0 : 0 ≤ Mg.W0.toReal := TaylorM.Valid.W0_nonneg hg0
    have hef : 0 ≤ Mf.err.toReal := TaylorM.Valid.err_nonneg hf0
    have heg : 0 ≤ Mg.err.toReal := TaylorM.Valid.err_nonneg hg0
    have hfa : |f (fun i => (Mf.y i).toReal)| ≤ Mf.fB.abs.hi.toReal :=
      (DInterval.mem_abs hfB).2
    have hga : |g (fun i => (Mf.y i).toReal)| ≤ Mg.fB.abs.hi.toReal :=
      (DInterval.mem_abs hgB').2
    have hfa0 : 0 ≤ Mf.fB.abs.hi.toReal := le_trans (abs_nonneg _) hfa
    have hga0 : 0 ≤ Mg.fB.abs.hi.toReal := le_trans (abs_nonneg _) hga
    have hsum : (∑ i, (af i * g (fun i => (Mf.y i).toReal)
          + f (fun i => (Mf.y i).toReal) * ag i) * (ρ i - (Mf.y i).toReal))
        = g (fun i => (Mf.y i).toReal) * (∑ i, af i * (ρ i - (Mf.y i).toReal))
          + f (fun i => (Mf.y i).toReal) * (∑ i, ag i * (ρ i - (Mf.y i).toReal)) := by
      have hpt : ∀ i, (af i * g (fun i => (Mf.y i).toReal)
            + f (fun i => (Mf.y i).toReal) * ag i) * (ρ i - (Mf.y i).toReal)
          = g (fun i => (Mf.y i).toReal) * (af i * (ρ i - (Mf.y i).toReal))
            + f (fun i => (Mf.y i).toReal) * (ag i * (ρ i - (Mf.y i).toReal)) :=
        fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]
    have hdecomp : f ρ * g ρ
        - f (fun i => (Mf.y i).toReal) * g (fun i => (Mf.y i).toReal)
        - (g (fun i => (Mf.y i).toReal) * (∑ i, af i * (ρ i - (Mf.y i).toReal))
          + f (fun i => (Mf.y i).toReal) * (∑ i, ag i * (ρ i - (Mf.y i).toReal)))
        = (∑ i, af i * (ρ i - (Mf.y i).toReal)) * (∑ i, ag i * (ρ i - (Mf.y i).toReal))
          + (f ρ - f (fun i => (Mf.y i).toReal) - ∑ i, af i * (ρ i - (Mf.y i).toReal))
            * (g (fun i => (Mf.y i).toReal) + (∑ i, ag i * (ρ i - (Mf.y i).toReal))
              + (g ρ - g (fun i => (Mf.y i).toReal) - ∑ i, ag i * (ρ i - (Mf.y i).toReal)))
          + (g ρ - g (fun i => (Mf.y i).toReal) - ∑ i, ag i * (ρ i - (Mf.y i).toReal))
            * (f (fun i => (Mf.y i).toReal) + ∑ i, af i * (ρ i - (Mf.y i).toReal)) := by
      ring
    show |f ρ * g ρ
        - f (fun i => ((Mf.mul Mg).y i).toReal) * g (fun i => ((Mf.mul Mg).y i).toReal)
        - ∑ i, (af i * g (fun i => (Mf.y i).toReal)
          + f (fun i => (Mf.y i).toReal) * ag i) * (ρ i - ((Mf.mul Mg).y i).toReal)|
        ≤ (Mf.mul Mg).err.toReal
    show |f ρ * g ρ
        - f (fun i => (Mf.y i).toReal) * g (fun i => (Mf.y i).toReal)
        - ∑ i, (af i * g (fun i => (Mf.y i).toReal)
          + f (fun i => (Mf.y i).toReal) * ag i) * (ρ i - (Mf.y i).toReal)|
        ≤ (Mf.mul Mg).err.toReal
    rw [hsum, hdecomp]
    have herr : ((Mf.W0.mul Mg.W0).add
          ((Mf.err.mul ((Mg.fB.abs.hi.add Mg.W0).add Mg.err)).add
            (Mg.err.mul (Mf.fB.abs.hi.add Mf.W0)))).toReal
        = Mf.W0.toReal * Mg.W0.toReal
          + (Mf.err.toReal * (Mg.fB.abs.hi.toReal + Mg.W0.toReal + Mg.err.toReal)
            + Mg.err.toReal * (Mf.fB.abs.hi.toReal + Mf.W0.toReal)) := by
      rw [Dyadic.toReal_add, Dyadic.toReal_mul, Dyadic.toReal_add, Dyadic.toReal_mul,
        Dyadic.toReal_mul, Dyadic.toReal_add, Dyadic.toReal_add, Dyadic.toReal_add]
    have hchop : ((Mf.W0.mul Mg.W0).add
          ((Mf.err.mul ((Mg.fB.abs.hi.add Mg.W0).add Mg.err)).add
            (Mg.err.mul (Mf.fB.abs.hi.add Mf.W0)))).toReal
        ≤ (Mf.mul Mg).err.toReal := by
      show _ ≤ (((Mf.W0.mul Mg.W0).add
          ((Mf.err.mul ((Mg.fB.abs.hi.add Mg.W0).add Mg.err)).add
            (Mg.err.mul (Mf.fB.abs.hi.add Mf.W0)))).chopCeilTo Mf.errScale).toReal
      exact Dyadic.toReal_le_chopCeilTo _ _
    refine le_trans ?_ hchop
    rw [herr]
    have h1 : |(∑ i, af i * (ρ i - (Mf.y i).toReal))
        * (∑ i, ag i * (ρ i - (Mf.y i).toReal))|
        ≤ Mf.W0.toReal * Mg.W0.toReal := by
      rw [abs_mul]
      exact mul_le_mul hLf hLg (abs_nonneg _) hWf0
    have h2 : |(f ρ - f (fun i => (Mf.y i).toReal) - ∑ i, af i * (ρ i - (Mf.y i).toReal))
        * (g (fun i => (Mf.y i).toReal) + (∑ i, ag i * (ρ i - (Mf.y i).toReal))
          + (g ρ - g (fun i => (Mf.y i).toReal) - ∑ i, ag i * (ρ i - (Mf.y i).toReal)))|
        ≤ Mf.err.toReal * (Mg.fB.abs.hi.toReal + Mg.W0.toReal + Mg.err.toReal) := by
      rw [abs_mul]
      have hB : |g (fun i => (Mf.y i).toReal) + (∑ i, ag i * (ρ i - (Mf.y i).toReal))
          + (g ρ - g (fun i => (Mf.y i).toReal) - ∑ i, ag i * (ρ i - (Mf.y i).toReal))|
          ≤ Mg.fB.abs.hi.toReal + Mg.W0.toReal + Mg.err.toReal := by
        calc |g (fun i => (Mf.y i).toReal) + (∑ i, ag i * (ρ i - (Mf.y i).toReal))
            + (g ρ - g (fun i => (Mf.y i).toReal) - ∑ i, ag i * (ρ i - (Mf.y i).toReal))|
            ≤ |g (fun i => (Mf.y i).toReal) + (∑ i, ag i * (ρ i - (Mf.y i).toReal))|
              + |g ρ - g (fun i => (Mf.y i).toReal) - ∑ i, ag i * (ρ i - (Mf.y i).toReal)| :=
            abs_add_le _ _
          _ ≤ (|g (fun i => (Mf.y i).toReal)| + |∑ i, ag i * (ρ i - (Mf.y i).toReal)|)
              + |g ρ - g (fun i => (Mf.y i).toReal) - ∑ i, ag i * (ρ i - (Mf.y i).toReal)| :=
            add_le_add (abs_add_le _ _) le_rfl
          _ ≤ Mg.fB.abs.hi.toReal + Mg.W0.toReal + Mg.err.toReal :=
            add_le_add (add_le_add hga hLg) hbg
      exact mul_le_mul hbf hB (abs_nonneg _) hef
    have h3 : |(g ρ - g (fun i => (Mf.y i).toReal) - ∑ i, ag i * (ρ i - (Mf.y i).toReal))
        * (f (fun i => (Mf.y i).toReal) + ∑ i, af i * (ρ i - (Mf.y i).toReal))|
        ≤ Mg.err.toReal * (Mf.fB.abs.hi.toReal + Mf.W0.toReal) := by
      rw [abs_mul]
      have hB : |f (fun i => (Mf.y i).toReal) + ∑ i, af i * (ρ i - (Mf.y i).toReal)|
          ≤ Mf.fB.abs.hi.toReal + Mf.W0.toReal :=
        le_trans (abs_add_le _ _) (add_le_add hfa hLf)
      exact mul_le_mul hbg hB (abs_nonneg _) heg
    have hfinal := le_trans (abs_add_le _ _)
      (add_le_add (le_trans (abs_add_le _ _) (add_le_add h1 h2)) h3)
    linarith

/-! ## The square-root rule (elementary, no derivatives) -/

/-- The difference identity for `√`: `(√s − √t)·(√s + √t) = s − t`. -/
theorem sqrt_sub_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Real.sqrt s - Real.sqrt t = (s - t) / (Real.sqrt s + Real.sqrt t) := by
  have hpos : 0 < Real.sqrt s + Real.sqrt t :=
    add_pos (Real.sqrt_pos.2 hs) (Real.sqrt_pos.2 ht)
  rw [eq_div_iff hpos.ne']
  ring_nf
  rw [Real.sq_sqrt hs.le, Real.sq_sqrt ht.le]

/-- Slope-difference bound for `√`: on `s, t ≥ c > 0`,
`|1/(√s+√t) − 1/(2√t)| ≤ |s − t| / (8·c·√c)`.  This is the `½·Mg''` term of
the design's sqrt composition rule, proved by pure algebra. -/
theorem sqrt_slope_diff {s t c : ℝ} (hc : 0 < c) (hs : c ≤ s) (ht : c ≤ t) :
    |1 / (Real.sqrt s + Real.sqrt t) - 1 / (2 * Real.sqrt t)|
      ≤ |s - t| / (8 * (c * Real.sqrt c)) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 (lt_of_lt_of_le hc hs)
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 (lt_of_lt_of_le hc ht)
  have hsum : 0 < Real.sqrt s + Real.sqrt t := add_pos hss hst
  have h2t : 0 < 2 * Real.sqrt t := by positivity
  have hden : 0 < (Real.sqrt s + Real.sqrt t) * (2 * Real.sqrt t) := mul_pos hsum h2t
  have hid : 1 / (Real.sqrt s + Real.sqrt t) - 1 / (2 * Real.sqrt t)
      = (Real.sqrt t - Real.sqrt s) / ((Real.sqrt s + Real.sqrt t) * (2 * Real.sqrt t)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hden]
  have hid2 : Real.sqrt t - Real.sqrt s
      = (t - s) / (Real.sqrt s + Real.sqrt t) := by
    rw [add_comm (Real.sqrt s) (Real.sqrt t)]
    exact sqrt_sub_eq (lt_of_lt_of_le hc ht) (lt_of_lt_of_le hc hs)
  rw [hid2, abs_div, abs_of_pos hsum, abs_sub_comm t s, div_div]
  -- denominator comparison
  have hb1 : 2 * Real.sqrt c ≤ Real.sqrt s + Real.sqrt t := by
    have h1 := Real.sqrt_le_sqrt hs
    have h2 := Real.sqrt_le_sqrt ht
    linarith
  have hb2 : 2 * Real.sqrt c ≤ 2 * Real.sqrt t := by
    have h2 := Real.sqrt_le_sqrt ht
    linarith
  have h8 : (2 * Real.sqrt c) * ((2 * Real.sqrt c) * (2 * Real.sqrt c))
      = 8 * (c * Real.sqrt c) := by
    have hsq : (2 * Real.sqrt c) * (2 * Real.sqrt c) = 4 * c := by
      calc (2 * Real.sqrt c) * (2 * Real.sqrt c)
          = 4 * (Real.sqrt c ^ 2) := by ring
        _ = 4 * c := by rw [Real.sq_sqrt hc.le]
    calc (2 * Real.sqrt c) * ((2 * Real.sqrt c) * (2 * Real.sqrt c))
        = (2 * Real.sqrt c) * (4 * c) := by rw [hsq]
      _ = 8 * (c * Real.sqrt c) := by ring
  have hdenge : (2 * Real.sqrt c) * ((2 * Real.sqrt c) * (2 * Real.sqrt c))
      ≤ (Real.sqrt s + Real.sqrt t) * ((Real.sqrt s + Real.sqrt t) * (2 * Real.sqrt t)) :=
    mul_le_mul hb1 (mul_le_mul hb1 hb2 (by positivity) (by positivity))
      (by positivity) (by positivity)
  have hDpos : 0 < (2 * Real.sqrt c) * ((2 * Real.sqrt c) * (2 * Real.sqrt c)) := by
    positivity
  rw [← h8]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hDpos hdenge

/-- **Validity of the sqrt rule**: if `M` models `f` and the certified
computation `M.sqrt p` succeeds, the result models `√ ∘ f` (with the same
center and envelope). -/
theorem valid_sqrt {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) (p : SqrtTMP) {M' : TaylorM n}
    (h : M.sqrt p = some M') :
    M'.Valid box (fun ρ => Real.sqrt (f ρ)) ∧ M'.y = M.y ∧ M'.w = M.w := by
  have hV0 := hV
  obtain ⟨hmem, hw, hfB, hrem⟩ := hV
  unfold TaylorM.sqrt at h
  by_cases hc : (M.fB.lo.add (-M.W)).isPos = true
  · rw [if_pos hc] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨Jl, hJl, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨Jh, hJh, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨Jc, hJc, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨J, hJ, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨K, hK, h⟩ := h
    obtain rfl : M' = ⟨M.y, M.w, ⟨Jl.lo, Jh.hi⟩, fun i => (M.dfB i).mul J,
      ((M.err.mul J.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo M.errScale⟩ :=
        h.symm
    -- basic real-valued facts
    have hcR : (M.fB.lo.add (-M.W)).toReal = M.fB.lo.toReal - M.W.toReal := by
      rw [Dyadic.toReal_add, Dyadic.toReal_neg, sub_eq_add_neg]
    have hc0 : 0 < (M.fB.lo.add (-M.W)).toReal :=
      (Dyadic.isPos_iff _).mp hc
    have hc_le : (M.fB.lo.add (-M.W)).toReal ≤ M.fB.lo.toReal := by
      have := TaylorM.W_nonneg M
      linarith
    have hfy_ge : M.fB.lo.toReal ≤ f (fun i => (M.y i).toReal) := hfB.1
    have hfy_le : f (fun i => (M.y i).toReal) ≤ M.fB.hi.toReal := hfB.2
    have hfBlo : 0 ≤ M.fB.lo.toReal := le_trans hc0.le hc_le
    have hfy_pos : 0 < f (fun i => (M.y i).toReal) := lt_of_lt_of_le hc0 (le_trans hc_le hfy_ge)
    -- sqrt certificates
    have hJl1 : Jl.lo.toReal ≤ Real.sqrt M.fB.lo.toReal := (Dyadic.sqrtI_sound hJl).1
    have hJh2 : Real.sqrt M.fB.hi.toReal ≤ Jh.hi.toReal := (Dyadic.sqrtI_sound hJh).2
    have hJc1 : Jc.lo.toReal ≤ Real.sqrt (M.fB.lo.add (-M.W)).toReal :=
      (Dyadic.sqrtI_sound hJc).1
    have hJclo : 0 ≤ Jc.lo.toReal := Dyadic.sqrtI_lo_nonneg hJc
    -- the slope interval J contains 1/(2·√f(y))
    have hJmem : J.mem (1 / (2 * Real.sqrt (f fun i => (M.y i).toReal))) := by
      have hmem2 : (⟨(⟨2, 0⟩ : Dyadic).mul Jl.lo, (⟨2, 0⟩ : Dyadic).mul Jh.hi⟩ :
          DInterval).mem (2 * Real.sqrt (f fun i => (M.y i).toReal)) := by
        constructor
        · rw [Dyadic.toReal_mul, Dyadic.toReal_two]
          exact mul_le_mul_of_nonneg_left
            (le_trans hJl1 (Real.sqrt_le_sqrt hfy_ge)) (by norm_num)
        · rw [Dyadic.toReal_mul, Dyadic.toReal_two]
          exact mul_le_mul_of_nonneg_left
            (le_trans (Real.sqrt_le_sqrt hfy_le) hJh2) (by norm_num)
      exact DInterval.recip_sound hmem2 hJ
    have hqpos : 0 < 1 / (2 * Real.sqrt (f fun i => (M.y i).toReal)) := by
      have : 0 < Real.sqrt (f fun i => (M.y i).toReal) := Real.sqrt_pos.2 hfy_pos
      positivity
    -- the curvature bound K
    have hq8val : ((⟨8, 0⟩ : Dyadic).mul ((M.fB.lo.add (-M.W)).mul Jc.lo)).toReal
        = 8 * ((M.fB.lo.add (-M.W)).toReal * Jc.lo.toReal) := by
      rw [Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_eight]
    have hq8nn : 0 ≤ ((⟨8, 0⟩ : Dyadic).mul ((M.fB.lo.add (-M.W)).mul Jc.lo)).toReal := by
      rw [hq8val]
      exact mul_nonneg (by norm_num) (mul_nonneg hc0.le hJclo)
    have hq8pos : 0 < ((⟨8, 0⟩ : Dyadic).mul ((M.fB.lo.add (-M.W)).mul Jc.lo)).toReal := by
      unfold DInterval.recip at hK
      split at hK
      · next hcond =>
          rcases hcond with hpos | hneg
          · exact (Dyadic.isPos_iff _).mp hpos
          · have hneg' : ((⟨8, 0⟩ : Dyadic).mul ((M.fB.lo.add (-M.W)).mul Jc.lo)).toReal < 0 :=
              (Dyadic.isNeg_iff _).mp hneg
            linarith
      · exact absurd hK (by simp)
    have hKbound : 1 / (8 * ((M.fB.lo.add (-M.W)).toReal
          * Real.sqrt (M.fB.lo.add (-M.W)).toReal)) ≤ K.hi.toReal := by
      have hKmem := DInterval.recip_sound
        (show (⟨(⟨8, 0⟩ : Dyadic).mul ((M.fB.lo.add (-M.W)).mul Jc.lo),
          (⟨8, 0⟩ : Dyadic).mul ((M.fB.lo.add (-M.W)).mul Jc.lo)⟩ : DInterval).mem
          ((⟨8, 0⟩ : Dyadic).mul ((M.fB.lo.add (-M.W)).mul Jc.lo)).toReal from
          ⟨le_rfl, le_rfl⟩) hK
      have hle : ((⟨8, 0⟩ : Dyadic).mul ((M.fB.lo.add (-M.W)).mul Jc.lo)).toReal
          ≤ 8 * ((M.fB.lo.add (-M.W)).toReal * Real.sqrt (M.fB.lo.add (-M.W)).toReal) := by
        rw [hq8val]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hJc1 hc0.le) (by norm_num)
      exact le_trans (one_div_le_one_div_of_le hq8pos hle) hKmem.2
    -- assemble the three conjuncts (y, w unchanged)
    refine ⟨⟨hmem, hw, ?_, ?_⟩, rfl, rfl⟩
    · show (⟨Jl.lo, Jh.hi⟩ : DInterval).mem
        (Real.sqrt (f fun i => (M.y i).toReal))
      exact ⟨le_trans hJl1 (Real.sqrt_le_sqrt hfy_ge),
        le_trans (Real.sqrt_le_sqrt hfy_le) hJh2⟩
    · intro ρ hρ
      obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
      have hW : |f ρ - f (fun i => (M.y i).toReal)| ≤ M.W.toReal :=
        TaylorM.Valid.abs_sub_le_W hV0 hρ ha hbound
      have hfρ_ge : (M.fB.lo.add (-M.W)).toReal ≤ f ρ := by
        have h1 := (abs_le.mp hW).1
        linarith
      have hfρ_pos : 0 < f ρ := lt_of_lt_of_le hc0 hfρ_ge
      refine ⟨fun i => a i * (1 / (2 * Real.sqrt (f fun i => (M.y i).toReal))),
        fun i => DInterval.mem_mul (ha i) hJmem, ?_⟩
      have herr' : ((M.err.mul J.hi).add ((M.W.mul M.W).mul K.hi)).toReal
          = M.err.toReal * J.hi.toReal + M.W.toReal ^ 2 * K.hi.toReal := by
        rw [Dyadic.toReal_add, Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul,
          pow_two]
      have hchop : ((M.err.mul J.hi).add ((M.W.mul M.W).mul K.hi)).toReal
          ≤ (⟨M.y, M.w, ⟨Jl.lo, Jh.hi⟩, fun i => (M.dfB i).mul J,
            ((M.err.mul J.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo M.errScale⟩ :
              TaylorM n).err.toReal := by
        show _ ≤ (((M.err.mul J.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo
          M.errScale).toReal
        exact Dyadic.toReal_le_chopCeilTo _ _
      refine le_trans ?_ hchop
      rw [herr']
      have hsum : (∑ i, a i * (1 / (2 * Real.sqrt (f fun i => (M.y i).toReal)))
            * (ρ i - (M.y i).toReal))
          = (1 / (2 * Real.sqrt (f fun i => (M.y i).toReal)))
            * ∑ i, a i * (ρ i - (M.y i).toReal) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hsqrt : Real.sqrt (f ρ) - Real.sqrt (f fun i => (M.y i).toReal)
          = (f ρ - f (fun i => (M.y i).toReal))
            / (Real.sqrt (f ρ) + Real.sqrt (f fun i => (M.y i).toReal)) :=
        sqrt_sub_eq hfρ_pos hfy_pos
      have hdecomp : Real.sqrt (f ρ) - Real.sqrt (f fun i => (M.y i).toReal)
          - (1 / (2 * Real.sqrt (f fun i => (M.y i).toReal)))
            * ∑ i, a i * (ρ i - (M.y i).toReal)
          = (f ρ - f (fun i => (M.y i).toReal))
              * (1 / (Real.sqrt (f ρ) + Real.sqrt (f fun i => (M.y i).toReal))
                - 1 / (2 * Real.sqrt (f fun i => (M.y i).toReal)))
            + (1 / (2 * Real.sqrt (f fun i => (M.y i).toReal)))
              * (f ρ - f (fun i => (M.y i).toReal)
                - ∑ i, a i * (ρ i - (M.y i).toReal)) := by
        rw [hsqrt]
        rw [div_eq_mul_inv]
        ring
      have hT1 : |(f ρ - f (fun i => (M.y i).toReal))
          * (1 / (Real.sqrt (f ρ) + Real.sqrt (f fun i => (M.y i).toReal))
            - 1 / (2 * Real.sqrt (f fun i => (M.y i).toReal)))|
          ≤ M.W.toReal ^ 2 * K.hi.toReal := by
        rw [abs_mul]
        have hsd := sqrt_slope_diff hc0 hfρ_ge (le_trans hc_le hfy_ge)
        have hDpos : 0 < 8 * ((M.fB.lo.add (-M.W)).toReal
            * Real.sqrt (M.fB.lo.add (-M.W)).toReal) := by
          have := Real.sqrt_pos.2 hc0
          positivity
        calc |f ρ - f (fun i => (M.y i).toReal)|
            * |1 / (Real.sqrt (f ρ) + Real.sqrt (f fun i => (M.y i).toReal))
              - 1 / (2 * Real.sqrt (f fun i => (M.y i).toReal))|
            ≤ M.W.toReal * (|f ρ - f (fun i => (M.y i).toReal)|
              / (8 * ((M.fB.lo.add (-M.W)).toReal
                * Real.sqrt (M.fB.lo.add (-M.W)).toReal))) :=
            mul_le_mul hW hsd (abs_nonneg _) (TaylorM.W_nonneg M)
          _ = (M.W.toReal * |f ρ - f (fun i => (M.y i).toReal)|)
              / (8 * ((M.fB.lo.add (-M.W)).toReal
                * Real.sqrt (M.fB.lo.add (-M.W)).toReal)) := (mul_div_assoc _ _ _).symm
          _ ≤ (M.W.toReal * M.W.toReal)
              / (8 * ((M.fB.lo.add (-M.W)).toReal
                * Real.sqrt (M.fB.lo.add (-M.W)).toReal)) := by
            rw [div_le_iff₀ hDpos, div_mul_cancel₀ _ hDpos.ne']
            exact mul_le_mul le_rfl hW (abs_nonneg _) (TaylorM.W_nonneg M)
          _ = (M.W.toReal * M.W.toReal)
              * (1 / (8 * ((M.fB.lo.add (-M.W)).toReal
                * Real.sqrt (M.fB.lo.add (-M.W)).toReal))) := (mul_one_div _ _).symm
          _ ≤ (M.W.toReal * M.W.toReal) * K.hi.toReal :=
            mul_le_mul_of_nonneg_left hKbound
              (mul_nonneg (TaylorM.W_nonneg M) (TaylorM.W_nonneg M))
          _ = M.W.toReal ^ 2 * K.hi.toReal := by rw [pow_two]
      have hT2 : |(1 / (2 * Real.sqrt (f fun i => (M.y i).toReal)))
          * (f ρ - f (fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal))|
          ≤ M.err.toReal * J.hi.toReal := by
        rw [abs_mul, abs_of_pos hqpos]
        calc (1 / (2 * Real.sqrt (f fun i => (M.y i).toReal)))
            * |f ρ - f (fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)|
            ≤ J.hi.toReal * M.err.toReal :=
            mul_le_mul hJmem.2 hbound (abs_nonneg _) (le_trans hqpos.le hJmem.2)
          _ = M.err.toReal * J.hi.toReal := mul_comm _ _
      rw [hsum, hdecomp]
      exact le_trans (abs_add_le _ _) (by linarith [hT1, hT2])
  · rw [if_neg hc] at h
    exact absurd h (by simp)

/-! ## The reciprocal/division rule (elementary, no derivatives) -/

/-- **Validity of `invCore`**: given a certified positive lower bound `c` of
`|f|` over the box, the computed model models `f⁻¹`. -/
theorem valid_invCore {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) {c : Dyadic} (p : InvTMP)
    (hc0 : 0 < c.toReal)
    (hcle : ∀ ρ, boxMem box ρ → c.toReal ≤ |f ρ|)
    {M' : TaylorM n} (h : M.invCore c p = some M') :
    M'.Valid box (fun ρ => (f ρ)⁻¹) ∧ M'.y = M.y ∧ M'.w = M.w := by
  have hV0 := hV
  obtain ⟨hmem, hw, hfB, hrem⟩ := hV
  unfold TaylorM.invCore at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨V, hVv, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨Jp, hJp, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨K, hK, h⟩ := h
  obtain rfl : M' = ⟨M.y, M.w, V, fun i => (M.dfB i).mul Jp.neg,
    ((M.err.mul Jp.abs.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo M.errScale⟩ :=
      h.symm
  have hcfy : c.toReal ≤ |f fun i => (M.y i).toReal| := hcle _ (fun i => hmem i)
  have hfyne : f (fun i => (M.y i).toReal) ≠ 0 :=
    abs_pos.mp (lt_of_lt_of_le hc0 hcfy)
  have hsq_abs' : ∀ x : ℝ, |x| * |x| = x * x := fun x => by
    rw [← pow_two, ← pow_two, sq_abs]
  have hfy2ge : c.toReal * c.toReal
      ≤ (f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal) := by
    have h := mul_le_mul hcfy hcfy hc0.le (le_trans hc0.le hcfy)
    rwa [hsq_abs'] at h
  have hfy2le : (f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal)
      ≤ M.fB.abs.hi.toReal * M.fB.abs.hi.toReal := by
    have h1 := (DInterval.mem_abs hfB).2
    have h0 : 0 ≤ M.fB.abs.hi.toReal := le_trans (abs_nonneg _) h1
    have h := mul_le_mul h1 h1 (abs_nonneg _) h0
    rwa [hsq_abs'] at h
  have hJpmem : Jp.mem (1 / ((f fun i => (M.y i).toReal)
      * (f fun i => (M.y i).toReal))) :=
    DInterval.recip_sound
      ⟨by rw [Dyadic.toReal_mul]; exact hfy2ge,
       by rw [Dyadic.toReal_mul]; exact hfy2le⟩ hJp
  have hVmem : V.mem (f fun i => (M.y i).toReal)⁻¹ := by
    have := DInterval.recip_sound hfB hVv
    rwa [one_div] at this
  have hKhi : 1 / (c.toReal * (c.toReal * c.toReal)) ≤ K.hi.toReal := by
    have hmem3 : (⟨c.mul (c.mul c), c.mul (c.mul c)⟩ : DInterval).mem
        (c.mul (c.mul c)).toReal := ⟨le_rfl, le_rfl⟩
    have h2 := (DInterval.recip_sound hmem3 hK).2
    rwa [Dyadic.toReal_mul, Dyadic.toReal_mul] at h2
  refine ⟨⟨hmem, hw, hVmem, ?_⟩, rfl, rfl⟩
  intro ρ hρ
  obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
  have hcρ := hcle ρ hρ
  have hfρne : f ρ ≠ 0 := abs_pos.mp (lt_of_lt_of_le hc0 hcρ)
  have hW := TaylorM.Valid.abs_sub_le_W hV0 hρ ha hbound
  refine ⟨fun i => a i * (-(1 / ((f fun i => (M.y i).toReal)
      * (f fun i => (M.y i).toReal)))), fun i => ?_, ?_⟩
  · show ((M.dfB i).mul Jp.neg).mem _
    exact DInterval.mem_mul (ha i) (DInterval.mem_neg hJpmem)
  · have herr' : ((M.err.mul Jp.abs.hi).add ((M.W.mul M.W).mul K.hi)).toReal
        = M.err.toReal * Jp.abs.hi.toReal + M.W.toReal ^ 2 * K.hi.toReal := by
      rw [Dyadic.toReal_add, Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul,
        pow_two]
    have hchop : ((M.err.mul Jp.abs.hi).add ((M.W.mul M.W).mul K.hi)).toReal
        ≤ (⟨M.y, M.w, V, fun i => (M.dfB i).mul Jp.neg,
          ((M.err.mul Jp.abs.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo M.errScale⟩ :
            TaylorM n).err.toReal := by
      show _ ≤ (((M.err.mul Jp.abs.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo
        M.errScale).toReal
      exact Dyadic.toReal_le_chopCeilTo _ _
    refine le_trans ?_ hchop
    rw [herr']
    have hsum : (∑ i, a i * (-(1 / ((f fun i => (M.y i).toReal)
            * (f fun i => (M.y i).toReal)))) * (ρ i - (M.y i).toReal))
        = (-(1 / ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal))))
          * ∑ i, a i * (ρ i - (M.y i).toReal) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hkey : (f ρ)⁻¹ - (f fun i => (M.y i).toReal)⁻¹
        - (-(1 / ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal))))
          * (f ρ - (f fun i => (M.y i).toReal))
        = (f ρ - (f fun i => (M.y i).toReal)) ^ 2
          / (f ρ * ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal))) := by
      field_simp
      ring
    have hdecomp : (f ρ)⁻¹ - (f fun i => (M.y i).toReal)⁻¹
        - (-(1 / ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal))))
          * ∑ i, a i * (ρ i - (M.y i).toReal)
        = ((f ρ)⁻¹ - (f fun i => (M.y i).toReal)⁻¹
            - (-(1 / ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal))))
              * (f ρ - (f fun i => (M.y i).toReal)))
          + (-(1 / ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal))))
            * (f ρ - (f fun i => (M.y i).toReal)
              - ∑ i, a i * (ρ i - (M.y i).toReal)) := by
      ring
    have hT1 : |(f ρ - (f fun i => (M.y i).toReal)) ^ 2
        / (f ρ * ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal)))|
        ≤ M.W.toReal ^ 2 * K.hi.toReal := by
      rw [abs_div, abs_of_nonneg (sq_nonneg _)]
      have hden : |f ρ * ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal))|
          = |f ρ| * ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal)) := by
        rw [abs_mul, abs_of_nonneg (mul_self_nonneg (f fun i => (M.y i).toReal))]
      rw [hden]
      have hW2 : (f ρ - (f fun i => (M.y i).toReal)) ^ 2 ≤ M.W.toReal ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hW 2
      have hdge : c.toReal * (c.toReal * c.toReal)
          ≤ |f ρ| * ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal)) :=
        mul_le_mul hcρ hfy2ge (mul_nonneg hc0.le hc0.le) (le_trans hc0.le hcρ)
      have hdpos : 0 < |f ρ| * ((f fun i => (M.y i).toReal)
          * (f fun i => (M.y i).toReal)) :=
        mul_pos (abs_pos.mpr hfρne) (mul_self_pos.mpr hfyne)
      have hc3pos : 0 < c.toReal * (c.toReal * c.toReal) :=
        mul_pos hc0 (mul_pos hc0 hc0)
      calc (f ρ - (f fun i => (M.y i).toReal)) ^ 2
            / (|f ρ| * ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal)))
          ≤ M.W.toReal ^ 2
            / (|f ρ| * ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal))) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hW2 (inv_nonneg.mpr hdpos.le)
        _ ≤ M.W.toReal ^ 2 / (c.toReal * (c.toReal * c.toReal)) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            have h1 := one_div_le_one_div_of_le hc3pos hdge
            simp only [one_div] at h1
            exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ ≤ M.W.toReal ^ 2 * K.hi.toReal := by
            rw [div_eq_mul_inv, ← one_div]
            exact mul_le_mul_of_nonneg_left hKhi (sq_nonneg _)
    have hT2 : |(-(1 / ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal))))
        * (f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal))|
        ≤ M.err.toReal * Jp.abs.hi.toReal := by
      rw [abs_mul]
      have hq : |-(1 / ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal)))|
          ≤ Jp.abs.hi.toReal := by
        rw [abs_neg]
        exact (DInterval.mem_abs hJpmem).2
      have hJ0 : 0 ≤ Jp.abs.hi.toReal := le_trans (abs_nonneg _) hq
      calc |-(1 / ((f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal)))|
          * |f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)|
          ≤ Jp.abs.hi.toReal * M.err.toReal :=
          mul_le_mul hq hbound (abs_nonneg _) hJ0
        _ = M.err.toReal * Jp.abs.hi.toReal := mul_comm _ _
    rw [hsum, hdecomp, hkey]
    exact le_trans (abs_add_le _ _) (by linarith [hT1, hT2])

/-- **Validity of the reciprocal rule**: two sign cases feeding
`valid_invCore`. -/
theorem valid_inv {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) (p : InvTMP) {M' : TaylorM n}
    (h : M.inv p = some M') :
    M'.Valid box (fun ρ => (f ρ)⁻¹) ∧ M'.y = M.y ∧ M'.w = M.w := by
  have hV0 := hV
  obtain ⟨hmem, hw, hfB, hrem⟩ := hV
  unfold TaylorM.inv at h
  by_cases hcp : (M.fB.lo.add (-M.W)).isPos = true
  · rw [if_pos hcp] at h
    refine valid_invCore hV0 p ?_ ?_ h
    · exact (Dyadic.isPos_iff _).mp hcp
    · intro ρ hρ
      obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
      have hW := TaylorM.Valid.abs_sub_le_W hV0 hρ ha hbound
      have h1 := (abs_le.mp hW).1
      have hfy1 := hfB.1
      have hc0 : 0 < (M.fB.lo.add (-M.W)).toReal := (Dyadic.isPos_iff _).mp hcp
      have h2 : (M.fB.lo.add (-M.W)).toReal = M.fB.lo.toReal - M.W.toReal := by
        rw [Dyadic.toReal_add, Dyadic.toReal_neg, sub_eq_add_neg]
      rw [h2] at hc0 ⊢
      have hge : M.fB.lo.toReal - M.W.toReal ≤ f ρ := by linarith
      rw [abs_of_nonneg (by linarith)]
      exact hge
  · by_cases hcn : (-(M.fB.hi.add M.W)).isPos = true
    · rw [if_neg hcp, if_pos hcn] at h
      refine valid_invCore hV0 p ?_ ?_ h
      · exact (Dyadic.isPos_iff _).mp hcn
      · intro ρ hρ
        obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
        have hW := TaylorM.Valid.abs_sub_le_W hV0 hρ ha hbound
        have h2b := (abs_le.mp hW).2
        have hfy2 := hfB.2
        have hc0 : 0 < (-(M.fB.hi.add M.W)).toReal := (Dyadic.isPos_iff _).mp hcn
        have h2 : (-(M.fB.hi.add M.W)).toReal = -(M.fB.hi.toReal + M.W.toReal) := by
          rw [Dyadic.toReal_neg, Dyadic.toReal_add]
        rw [h2] at hc0 ⊢
        have hle : f ρ ≤ M.fB.hi.toReal + M.W.toReal := by linarith
        rw [abs_of_nonpos (by linarith)]
        linarith
    · rw [if_neg hcp, if_neg hcn] at h
      exact absurd h (by simp)

/-- **Validity of division** (as `f · g⁻¹`). -/
theorem valid_div {n : ℕ} {Mf Mg : TaylorM n} {box : Fin n → DInterval}
    {f g : (Fin n → ℝ) → ℝ}
    (hf : Mf.Valid box f) (hg : Mg.Valid box g)
    (hy : Mf.y = Mg.y) (hw : Mf.w = Mg.w) (p : InvTMP) {Mi : TaylorM n}
    (hi : Mg.inv p = some Mi) :
    (Mf.mul Mi).Valid box (fun ρ => f ρ / g ρ) := by
  obtain ⟨hVi, hyi, hwi⟩ := valid_inv hg p hi
  have h := valid_mul hf hVi (by rw [hy, hyi]) (by rw [hw, hwi])
  convert h using 2
  rw [div_eq_mul_inv]

/-! ## The transcendental composition rules (sin / arctan / log)

Per the TM2 plan (`tm2-progress.md` §0): `sin` and `log` are proved by purely
elementary bounds (Mathlib's `one_sub_sq_div_two_le_cos` / `abs_sub_sin_le`
and the two standard `log` bounds); `arctan` uses the sanctioned MVT route
(`exists_hasDerivAt_eq_slope` + `Real.hasDerivAt_arctan`).  `cos` is left to
the hybrid fallback. -/

/-- `sin` second-order residual (elementary: angle addition +
`|cos h − 1| ≤ h²/2` and `|sin h − h| ≤ |h|³/6 ≤ |h|³/4`). -/
theorem sin_residual {s t : ℝ} :
    |Real.sin s - Real.sin t - Real.cos t * (s - t)|
      ≤ (s - t) ^ 2 / 2 + |s - t| ^ 3 / 4 := by
  have key : ∀ h : ℝ, |Real.sin (t + h) - Real.sin t - Real.cos t * h|
      ≤ h ^ 2 / 2 + |h| ^ 3 / 4 := by
    intro h
    have h1 : |Real.cos h - 1| ≤ h ^ 2 / 2 := by
      have hge := Real.one_sub_sq_div_two_le_cos (x := h)
      have hle := Real.cos_le_one h
      rw [abs_le]
      constructor <;> linarith
    have h2 : |Real.sin h - h| ≤ |h| ^ 3 / 4 := by
      have h3 := Real.abs_sub_sin_le h
      rw [abs_sub_comm (Real.sin h) h]
      refine le_trans h3 ?_
      exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) 3)
        (by norm_num) (by norm_num)
    rw [Real.sin_add]
    have hdecomp : Real.sin t * Real.cos h + Real.cos t * Real.sin h
        - Real.sin t - Real.cos t * h
        = Real.sin t * (Real.cos h - 1) + Real.cos t * (Real.sin h - h) := by
      ring
    rw [hdecomp]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul]
    have e1 : |Real.sin t| * |Real.cos h - 1| ≤ h ^ 2 / 2 := by
      have h4 := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t)
        (abs_nonneg (Real.cos h - 1))
      rw [one_mul] at h4
      exact le_trans h4 h1
    have e2 : |Real.cos t| * |Real.sin h - h| ≤ |h| ^ 3 / 4 := by
      have h4 := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t)
        (abs_nonneg (Real.sin h - h))
      rw [one_mul] at h4
      exact le_trans h4 h2
    linarith
  have h := key (s - t)
  rwa [show t + (s - t) = s by ring] at h

/-- `log` second-order residual (elementary): from `1 − 1/x ≤ log x ≤ x − 1`,
`log(s/t) − (s−t)/t ∈ [−(s−t)²/(s·t), 0]`. -/
theorem log_residual {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |Real.log s - Real.log t - (s - t) / t| ≤ (s - t) ^ 2 / (s * t) := by
  have hsd : 0 < s / t := div_pos hs ht
  have h1 := Real.log_le_sub_one_of_pos hsd
  have h2 := Real.one_sub_inv_le_log_of_pos hsd
  have h3 : Real.log s - Real.log t = Real.log (s / t) := by
    rw [Real.log_div hs.ne' ht.ne']
  rw [h3]
  have hub : Real.log (s / t) - (s - t) / t ≤ 0 := by
    have he : s / t - 1 = (s - t) / t := by field_simp
    linarith
  have hlb : -((s - t) ^ 2 / (s * t)) ≤ Real.log (s / t) - (s - t) / t := by
    have hinv : (s / t)⁻¹ = t / s := by rw [inv_div]
    rw [hinv] at h2
    have hident : (1 - t / s) - (s - t) / t = -((s - t) ^ 2 / (s * t)) := by
      field_simp
      ring
    linarith
  rw [abs_le]
  exact ⟨hlb, le_trans hub (by positivity)⟩

/-- **arctan second-order residual** (the sanctioned MVT route):
`atan s − atan t = (s−t)/(1+ξ²)` for some `ξ ∈ uIcc s t`, so the residual is
`(s−t)(t²−ξ²)/((1+ξ²)(1+t²))`, bounded by `(s−t)²·2B` when `|s|, |t| ≤ B`. -/
theorem arctan_residual {s t : ℝ} {B : ℝ} (hs : |s| ≤ B) (ht : |t| ≤ B) :
    |Real.arctan s - Real.arctan t - (s - t) / (1 + t ^ 2)|
      ≤ (s - t) ^ 2 * (2 * B) := by
  have hmvt : ∃ ξ ∈ Set.uIcc s t,
      Real.arctan s - Real.arctan t = (s - t) / (1 + ξ ^ 2) := by
    rcases lt_trichotomy s t with h | rfl | h
    · obtain ⟨ξ, hξ, hsl⟩ := exists_hasDerivAt_eq_slope (f := Real.arctan)
        (f' := fun x => 1 / (1 + x ^ 2)) h Real.continuous_arctan.continuousOn
        (fun x _ => Real.hasDerivAt_arctan x)
      refine ⟨ξ, Set.mem_uIcc.mpr (Or.inl ⟨hξ.1.le, hξ.2.le⟩), ?_⟩
      have hts : t - s ≠ 0 := sub_ne_zero.mpr h.ne'
      have h2 : Real.arctan t - Real.arctan s = (t - s) * (1 / (1 + ξ ^ 2)) := by
        rw [hsl, mul_comm]
        exact (div_mul_cancel₀ _ hts).symm
      have h3 : Real.arctan s - Real.arctan t = -(Real.arctan t - Real.arctan s) := by ring
      rw [h3, h2, div_eq_mul_inv]
      ring
    · exact ⟨s, Set.mem_uIcc.mpr (Or.inl ⟨le_rfl, le_rfl⟩), by simp⟩
    · obtain ⟨ξ, hξ, hsl⟩ := exists_hasDerivAt_eq_slope (f := Real.arctan)
        (f' := fun x => 1 / (1 + x ^ 2)) h Real.continuous_arctan.continuousOn
        (fun x _ => Real.hasDerivAt_arctan x)
      refine ⟨ξ, Set.mem_uIcc.mpr (Or.inr ⟨hξ.1.le, hξ.2.le⟩), ?_⟩
      have hts : s - t ≠ 0 := sub_ne_zero.mpr h.ne'
      have h2 : Real.arctan s - Real.arctan t = (s - t) * (1 / (1 + ξ ^ 2)) := by
        rw [hsl, mul_comm]
        exact (div_mul_cancel₀ _ hts).symm
      rw [h2, div_eq_mul_inv]
      ring
  obtain ⟨ξ, hξ, hid⟩ := hmvt
  rw [hid]
  have hξB : |ξ| ≤ B := by
    rw [Set.mem_uIcc] at hξ
    rcases hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases le_or_gt 0 ξ with hξp | hξp
      · rw [abs_of_nonneg hξp]
        exact le_trans h2 (le_trans (le_abs_self t) ht)
      · rw [abs_of_neg hξp]
        exact le_trans (neg_le_neg h1) (le_trans (neg_le_abs s) hs)
    · rcases le_or_gt 0 ξ with hξp | hξp
      · rw [abs_of_nonneg hξp]
        exact le_trans h2 (le_trans (le_abs_self s) hs)
      · rw [abs_of_neg hξp]
        exact le_trans (neg_le_neg h1) (le_trans (neg_le_abs t) ht)
  have hξt : |t - ξ| ≤ |s - t| := by
    rw [Set.mem_uIcc] at hξ
    rcases hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hst : |s - t| = t - s := by
        rw [abs_of_nonpos (sub_nonpos.mpr (le_trans h1 h2))]; ring
      rw [abs_le, hst]
      constructor <;> linarith
    · have hst : |s - t| = s - t := abs_of_nonneg (sub_nonneg.mpr (le_trans h1 h2))
      rw [abs_le, hst]
      constructor <;> linarith
  have hident : (s - t) / (1 + ξ ^ 2) - (s - t) / (1 + t ^ 2)
      = (s - t) * (t ^ 2 - ξ ^ 2) / ((1 + ξ ^ 2) * (1 + t ^ 2)) := by
    field_simp
    ring
  rw [hident, abs_div, abs_mul]
  have hden : 1 ≤ |(1 + ξ ^ 2) * (1 + t ^ 2)| := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg ξ, sq_nonneg t]
  have htξ : |t ^ 2 - ξ ^ 2| ≤ |s - t| * (B + B) := by
    have hdiff : t ^ 2 - ξ ^ 2 = (t - ξ) * (t + ξ) := by ring
    rw [hdiff, abs_mul]
    have hsum : |t + ξ| ≤ B + B := le_trans (abs_add_le t ξ) (add_le_add ht hξB)
    exact mul_le_mul hξt hsum (abs_nonneg _) (abs_nonneg _)
  calc |s - t| * |t ^ 2 - ξ ^ 2| / |(1 + ξ ^ 2) * (1 + t ^ 2)|
      ≤ |s - t| * |t ^ 2 - ξ ^ 2| / 1 :=
        div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (by norm_num) hden
    _ = |s - t| * |t ^ 2 - ξ ^ 2| := div_one _
    _ ≤ |s - t| * (|s - t| * (B + B)) := mul_le_mul_of_nonneg_left htξ (abs_nonneg _)
    _ = (s - t) ^ 2 * (2 * B) := by rw [← sq_abs]; ring

/-! ### arctan curvature: the exact-sup bound (549 final formula) -/

/-- Bracket identity driving both arctan-curvature monotonicity lemmas. -/
private theorem atan_curv_bracket (u v : ℝ) :
    v * (1 + u ^ 2) ^ 2 - u * (1 + v ^ 2) ^ 2
      = (v - u) * (1 - u * v * (2 + u ^ 2 + u * v + v ^ 2)) := by
  ring

/-- `2u/(1+u²)²` is monotone on `[0, 4/7]`: there
`uv(2+u²+uv+v²) ≤ (4/7)²(2+3(4/7)²) = 2336/2401 < 1`. -/
theorem atan_curv_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 4 / 7) :
    2 * u / (1 + u ^ 2) ^ 2 ≤ 2 * v / (1 + v ^ 2) ^ 2 := by
  have hu47 : u ≤ (4:ℝ) / 7 := huv.trans hv
  have hv0 : (0:ℝ) ≤ v := le_trans hu huv
  have huv1 : u * v ≤ (16:ℝ) / 49 := by nlinarith
  have hu2 : u ^ 2 ≤ (16:ℝ) / 49 := by nlinarith
  have hv2 : v ^ 2 ≤ (16:ℝ) / 49 := by nlinarith
  have hsum : (2:ℝ) + u ^ 2 + u * v + v ^ 2 ≤ (2:ℝ) + 3 * (16 / 49) := by linarith
  have hpos2 : (0:ℝ) ≤ 2 + u ^ 2 + u * v + v ^ 2 := by
    nlinarith [sq_nonneg u, sq_nonneg v]
  have hprod : u * v * (2 + u ^ 2 + u * v + v ^ 2) ≤ (1:ℝ) := by
    have h1 : u * v * (2 + u ^ 2 + u * v + v ^ 2)
        ≤ (16:ℝ) / 49 * (2 + u ^ 2 + u * v + v ^ 2) :=
      mul_le_mul_of_nonneg_right huv1 hpos2
    have h2 : (16:ℝ) / 49 * (2 + u ^ 2 + u * v + v ^ 2)
        ≤ (16:ℝ) / 49 * (2 + 3 * (16 / 49)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    have h3 : (16:ℝ) / 49 * (2 + 3 * (16 / 49)) ≤ 1 := by norm_num
    exact le_trans (le_trans h1 h2) h3
  have hbr : (0:ℝ) ≤ 1 - u * v * (2 + u ^ 2 + u * v + v ^ 2) := by linarith
  have hstep : u * (1 + v ^ 2) ^ 2 ≤ v * (1 + u ^ 2) ^ 2 := by
    have hid := atan_curv_bracket u v
    have h2 : (0:ℝ) ≤ v * (1 + u ^ 2) ^ 2 - u * (1 + v ^ 2) ^ 2 := by
      rw [hid]
      exact mul_nonneg (by linarith) hbr
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (2:ℝ) * u * (1 + v ^ 2) ^ 2 = 2 * (u * (1 + v ^ 2) ^ 2) := by ring
    _ ≤ 2 * (v * (1 + u ^ 2) ^ 2) := by exact mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = (2:ℝ) * v * (1 + u ^ 2) ^ 2 := by ring

/-- `2u/(1+u²)²` is antitone on `[5/8, ∞)`: there
`uv(2+u²+uv+v²) ≥ (5/8)²(2+3(5/8)²) = 5075/4096 > 1` (in particular
`5/8 ≥ 1/√3` since `(5/8)² = 25/64 ≥ 1/3`). -/
theorem atan_curv_anti {u v : ℝ} (hu : 5 / 8 ≤ u) (huv : u ≤ v) :
    2 * v / (1 + v ^ 2) ^ 2 ≤ 2 * u / (1 + u ^ 2) ^ 2 := by
  have hv58 : (5:ℝ) / 8 ≤ v := hu.trans huv
  have huv1 : (25:ℝ) / 64 ≤ u * v := by nlinarith
  have hu2 : (25:ℝ) / 64 ≤ u ^ 2 := by nlinarith
  have hv2 : (25:ℝ) / 64 ≤ v ^ 2 := by nlinarith
  have hsum : (2:ℝ) + 3 * (25 / 64) ≤ (2:ℝ) + u ^ 2 + u * v + v ^ 2 := by linarith
  have hprod : (1:ℝ) ≤ u * v * (2 + u ^ 2 + u * v + v ^ 2) := by
    have h1 : (1:ℝ) ≤ (25:ℝ) / 64 * (2 + 3 * (25 / 64)) := by norm_num
    have h2 : (25:ℝ) / 64 * (2 + 3 * (25 / 64)) ≤ u * v * (2 + 3 * (25 / 64)) :=
      mul_le_mul_of_nonneg_right huv1 (by norm_num)
    have h3 : u * v * (2 + 3 * (25 / 64)) ≤ u * v * (2 + u ^ 2 + u * v + v ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (le_trans (by norm_num) huv1)
    exact le_trans (le_trans h1 h2) h3
  have hbr : (1:ℝ) - u * v * (2 + u ^ 2 + u * v + v ^ 2) ≤ 0 := by linarith
  have hstep : v * (1 + u ^ 2) ^ 2 ≤ u * (1 + v ^ 2) ^ 2 := by
    have hid := atan_curv_bracket u v
    have h2 : v * (1 + u ^ 2) ^ 2 - u * (1 + v ^ 2) ^ 2 ≤ 0 := by
      rw [hid]
      have h3 : (0:ℝ) ≤ -(1 - u * v * (2 + u ^ 2 + u * v + v ^ 2)) := by linarith
      have h4 : (0:ℝ) ≤ (v - u) * -(1 - u * v * (2 + u ^ 2 + u * v + v ^ 2)) :=
        mul_nonneg (by linarith) h3
      linarith
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (2:ℝ) * v * (1 + u ^ 2) ^ 2 = 2 * (v * (1 + u ^ 2) ^ 2) := by ring
    _ ≤ 2 * (u * (1 + v ^ 2) ^ 2) := by exact mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = (2:ℝ) * u * (1 + v ^ 2) ^ 2 := by ring

/-- **Global cap for the arctan curvature**: `2|x|/(1+x²)² ≤ 7/8` for all
real `x` (true peak `3√3/8 ≈ 0.6495` at `|x| = 1/√3`; here: below `4/7` use
monotonicity to the endpoint `g(4/7) = 19208/29575`, above use the AM-GM
bound `(1+u²)² ≥ 4u²` giving `g ≤ 1/(2u)`). -/
theorem atan_curv_le_semi (x : ℝ) : 2 * |x| / (1 + x ^ 2) ^ 2 ≤ 7 / 8 := by
  have hxu : x ^ 2 = |x| ^ 2 := by
    have h := abs_pow x 2
    rwa [abs_of_nonneg (sq_nonneg x)] at h
  rw [hxu]
  rcases le_or_gt |x| ((4:ℝ) / 7) with hs | hb
  · have h1 := atan_curv_mono (u := |x|) (v := (4:ℝ) / 7) (abs_nonneg x) hs (by norm_num)
    calc 2 * |x| / (1 + |x| ^ 2) ^ 2
        ≤ 2 * ((4:ℝ) / 7) / (1 + ((4:ℝ) / 7) ^ 2) ^ 2 := h1
      _ ≤ (7:ℝ) / 8 := by norm_num
  · have hxbig : (0:ℝ) < 2 * |x| := by linarith
    have hAM : (2:ℝ) * |x| ≤ 1 + |x| ^ 2 := by nlinarith [sq_nonneg (|x| - 1)]
    have hden : (0:ℝ) < (1 + |x| ^ 2) ^ 2 := by positivity
    have h2 : 2 * |x| / (1 + |x| ^ 2) ^ 2 ≤ 1 / (2 * |x|) := by
      rw [div_le_div_iff₀ hden hxbig]
      nlinarith [sq_nonneg (|x| ^ 2 - 1)]
    have h3 : 1 / (2 * |x|) ≤ (7:ℝ) / 8 := by
      rw [div_le_iff₀ hxbig]
      nlinarith
    exact le_trans h2 h3

/-- Off-band endpoint bound: for `c ≤ |x|` with `c ≥ 5/8`, the arctan
curvature at `x` is at most the curvature at `c` (antitone in `|x|` beyond
`1/√3`). -/
theorem atan_curv_le_of_ge {x c : ℝ} (hc : 5 / 8 ≤ c) (hcx : c ≤ |x|) :
    2 * |x| / (1 + x ^ 2) ^ 2 ≤ 2 * c / (1 + c ^ 2) ^ 2 := by
  have hxu : x ^ 2 = |x| ^ 2 := by
    have h := abs_pow x 2
    rwa [abs_of_nonneg (sq_nonneg x)] at h
  rw [hxu]
  exact atan_curv_anti hc hcx

/-- **arctan second-order residual, exact-sup form**: if `C` bounds
`2|x|/(1+x²)²` on `[lo, hi] ∋ s, t`, then
`|atan s − atan t − (s−t)/(1+t²)| ≤ (s−t)²·C`.  Route: MVT on `atan`
(`ξ ∈ uIcc s t`) + MVT on `u ↦ 1/(1+u²)` (slope `−2u/(1+u²)²`), so the
slope-enclosure error is `|ξ−t|·|atan''(ζ)| ≤ |s−t|·C`.  This replaces the
legacy `arctan_residual` cap `(s−t)²·2B` (which dropped the `1/(1+ξ²)(1+t²)`
denominator and paid `2(|fB|+W)` for `|t+ξ|` — ~15× over-certified on the
549 straddle enclosures). -/
theorem arctan_residual_sup {s t : ℝ} {lo hi C : ℝ}
    (hs : lo ≤ s) (hs' : s ≤ hi) (ht : lo ≤ t) (ht' : t ≤ hi)
    (hC : ∀ x, lo ≤ x → x ≤ hi → 2 * |x| / (1 + x ^ 2) ^ 2 ≤ C) :
    |Real.arctan s - Real.arctan t - (s - t) / (1 + t ^ 2)|
      ≤ (s - t) ^ 2 * C := by
  have hC0 : (0:ℝ) ≤ C :=
    le_trans (div_nonneg (by nlinarith [abs_nonneg s]) (by positivity)) (hC s hs hs')
  have hinv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => 1 / (1 + y ^ 2))
      (-2 * x / (1 + x ^ 2) ^ 2) x := by
    intro x
    have h1 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const (c := (1:ℝ)) (x := x)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x :=
      (hasDerivAt_pow 2 x).congr_deriv (by ring)
    have hc : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      have h := h1.add h2
      rw [show ((fun _ : ℝ => (1:ℝ)) + (fun y : ℝ => y ^ 2))
            = (fun y : ℝ => (1:ℝ) + y ^ 2) from rfl,
          show ((0:ℝ) + 2 * x) = 2 * x from by ring] at h
      exact h
    have hfin := hc.inv (by positivity)
    rw [Pi.inv_def,
        show (-(2 * x) / (1 + x ^ 2) ^ 2) = (-2 * x / (1 + x ^ 2) ^ 2) from by ring,
        show ((fun y : ℝ => (1 + y ^ 2)⁻¹) = (fun y : ℝ => 1 / (1 + y ^ 2))) from
          funext fun y => (one_div _).symm] at hfin
    exact hfin
  have hcont : Continuous (fun y : ℝ => 1 / (1 + y ^ 2)) :=
    Continuous.div continuous_const (continuous_const.add (continuous_pow 2))
      (fun x => ne_of_gt (by positivity))
  have hmvt : ∃ ξ ∈ Set.uIcc s t,
      Real.arctan s - Real.arctan t = (s - t) / (1 + ξ ^ 2) := by
    rcases lt_trichotomy s t with hlt | rfl | hlt
    · obtain ⟨ξ, hξ, hsl⟩ := exists_hasDerivAt_eq_slope (f := Real.arctan)
        (f' := fun x => 1 / (1 + x ^ 2)) hlt Real.continuous_arctan.continuousOn
        (fun x _ => Real.hasDerivAt_arctan x)
      refine ⟨ξ, Set.mem_uIcc.mpr (Or.inl ⟨hξ.1.le, hξ.2.le⟩), ?_⟩
      have hts : t - s ≠ 0 := sub_ne_zero.mpr hlt.ne'
      have h2 : Real.arctan t - Real.arctan s = (t - s) * (1 / (1 + ξ ^ 2)) := by
        rw [hsl, mul_comm]
        exact (div_mul_cancel₀ _ hts).symm
      have h3 : Real.arctan s - Real.arctan t = -(Real.arctan t - Real.arctan s) := by ring
      rw [h3, h2, div_eq_mul_inv]
      ring
    · exact ⟨s, Set.mem_uIcc.mpr (Or.inl ⟨le_rfl, le_rfl⟩), by simp⟩
    · obtain ⟨ξ, hξ, hsl⟩ := exists_hasDerivAt_eq_slope (f := Real.arctan)
        (f' := fun x => 1 / (1 + x ^ 2)) hlt Real.continuous_arctan.continuousOn
        (fun x _ => Real.hasDerivAt_arctan x)
      refine ⟨ξ, Set.mem_uIcc.mpr (Or.inr ⟨hξ.1.le, hξ.2.le⟩), ?_⟩
      have hts : s - t ≠ 0 := sub_ne_zero.mpr hlt.ne'
      have h2 : Real.arctan s - Real.arctan t = (s - t) * (1 / (1 + ξ ^ 2)) := by
        rw [hsl, mul_comm]
        exact (div_mul_cancel₀ _ hts).symm
      rw [h2, div_eq_mul_inv]
      ring
  obtain ⟨ξ, hξ, hid⟩ := hmvt
  have hξr : lo ≤ ξ ∧ ξ ≤ hi := by
    rcases Set.mem_uIcc.mp hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans hs h1, le_trans h2 ht'⟩
    · exact ⟨le_trans ht h1, le_trans h2 hs'⟩
  have hξt : |ξ - t| ≤ |s - t| := by
    rcases Set.mem_uIcc.mp hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hst : |s - t| = t - s := by
        rw [abs_of_nonpos (sub_nonpos.mpr (le_trans h1 h2))]; ring
      rw [abs_le, hst]
      constructor <;> linarith
    · have hst : |s - t| = s - t := abs_of_nonneg (sub_nonneg.mpr (le_trans h1 h2))
      rw [abs_le, hst]
      constructor <;> linarith
  -- the residual factors through the slope difference at `ξ` vs `t`
  have hid' : Real.arctan s - Real.arctan t - (s - t) / (1 + t ^ 2)
      = (s - t) * ((1 / (1 + ξ ^ 2)) - (1 / (1 + t ^ 2))) := by
    rw [hid]
    ring
  -- the second MVT: slope difference = (ξ−t)·(atan'' ζ), ζ in range
  by_cases hξeq : ξ = t
  · subst hξeq
    rw [hid', sub_self, mul_zero, abs_zero]
    exact mul_nonneg (sq_nonneg _) hC0
  · -- the absolute value of the atan'' shape
    have hab : ∀ z : ℝ, |(-2 * z / (1 + z ^ 2) ^ 2 : ℝ)|
        = 2 * |z| / (1 + z ^ 2) ^ 2 := by
      intro z
      rw [abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_pos (by positivity : (0:ℝ) < (1 + z ^ 2) ^ 2)]
    rcases lt_or_gt_of_ne hξeq with hlt | hlt
    · -- ξ < t: slope on [ξ, t]
      obtain ⟨ζ, hζ, hsl⟩ := exists_hasDerivAt_eq_slope
        (f := fun y : ℝ => 1 / (1 + y ^ 2)) (f' := fun y => -2 * y / (1 + y ^ 2) ^ 2)
        hlt hcont.continuousOn (fun y _ => hinv y)
      have hts : t - ξ ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by linarith))
      have hstep : (t - ξ) * (-2 * ζ / (1 + ζ ^ 2) ^ 2)
          = (1 / (1 + t ^ 2)) - (1 / (1 + ξ ^ 2)) := by
        rw [mul_comm (t - ξ) (-2 * ζ / (1 + ζ ^ 2) ^ 2), hsl]
        exact div_mul_cancel₀ _ hts
      have hdif : (1 / (1 + ξ ^ 2)) - (1 / (1 + t ^ 2))
          = (ξ - t) * (-2 * ζ / (1 + ζ ^ 2) ^ 2) := by
        linear_combination hstep
      rw [hid', hdif, abs_mul, abs_mul, hab ζ]
      have h5 : |ξ - t| * (2 * |ζ| / (1 + ζ ^ 2) ^ 2) ≤ |s - t| * C :=
        mul_le_mul hξt (hC ζ (le_trans hξr.1 hζ.1.le) (le_trans hζ.2.le ht'))
          (div_nonneg (by linarith [abs_nonneg ζ]) (by positivity)) (abs_nonneg _)
      calc |s - t| * (|ξ - t| * (2 * |ζ| / (1 + ζ ^ 2) ^ 2))
          ≤ |s - t| * (|s - t| * C) := mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
        _ = (s - t) ^ 2 * C := by rw [← sq_abs]; ring
    · -- t < ξ: slope on [t, ξ]
      obtain ⟨ζ, hζ, hsl⟩ := exists_hasDerivAt_eq_slope
        (f := fun y : ℝ => 1 / (1 + y ^ 2)) (f' := fun y => -2 * y / (1 + y ^ 2) ^ 2)
        hlt hcont.continuousOn (fun y _ => hinv y)
      have hts : ξ - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by linarith))
      have hdif : (1 / (1 + ξ ^ 2)) - (1 / (1 + t ^ 2))
          = (ξ - t) * (-2 * ζ / (1 + ζ ^ 2) ^ 2) := by
        rw [mul_comm (ξ - t) (-2 * ζ / (1 + ζ ^ 2) ^ 2), hsl]
        exact (div_mul_cancel₀ _ hts).symm
      rw [hid', hdif, abs_mul, abs_mul, hab ζ]
      have h5 : |ξ - t| * (2 * |ζ| / (1 + ζ ^ 2) ^ 2) ≤ |s - t| * C :=
        mul_le_mul hξt (hC ζ (le_trans ht hζ.1.le) (le_trans hζ.2.le hξr.2))
          (div_nonneg (by linarith [abs_nonneg ζ]) (by positivity)) (abs_nonneg _)
      calc |s - t| * (|ξ - t| * (2 * |ζ| / (1 + ζ ^ 2) ^ 2))
          ≤ |s - t| * (|s - t| * C) := mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
        _ = (s - t) ^ 2 * C := by rw [← sq_abs]; ring

theorem atanCurv_seven_eighth : (⟨7, -3⟩ : Dyadic).toReal = 7 / 8 := by
  rw [Dyadic.toReal_def]; norm_num

/-- **Soundness of `atanCurv`**: the returned coefficient bounds the arctan
curvature on the whole range. -/
theorem atanCurv_sound (rLo rHi : Dyadic) (o2 : Int) :
    ∀ x : ℝ, rLo.toReal ≤ x → x ≤ rHi.toReal →
      2 * |x| / (1 + x ^ 2) ^ 2 ≤ (atanCurv rLo rHi o2).toReal := by
  have hband : (atanCurvBand).toReal = (5:ℝ) / 8 := by
    show (⟨5, -3⟩ : Dyadic).toReal = (5:ℝ) / 8
    rw [Dyadic.toReal_def]; norm_num
  intro x hlo hhi
  unfold atanCurv
  split_ifs with hneg hpos
  · -- range entirely negative: closest-to-zero endpoint is `c := -rHi`
    have hgate : rHi.toReal ≤ (-atanCurvBand).toReal := Dyadic.ble_toReal hneg
    rw [Dyadic.toReal_neg, hband] at hgate
    have hnegx : x < 0 := by linarith
    set c := (-rHi).toReal with hcdef
    have hc58 : (5:ℝ) / 8 ≤ c := by rw [hcdef, Dyadic.toReal_neg]; linarith
    have hcval : rHi.toReal = -c := by rw [hcdef, Dyadic.toReal_neg]; ring
    have hc2pos : (0:ℝ) ≤ 2 * c := by linarith
    have hwpos : (0:ℝ) ≤ 1 / (1 + c * c) :=
      div_nonneg (by norm_num) (by positivity)
    have hA2pos : (0:ℝ) ≤ 2 * c * (1 / (1 + c * c)) := by nlinarith
    cases hrec : DInterval.recip ⟨(⟨1, 0⟩ : Dyadic).add ((-rHi).mul (-rHi)),
        (⟨1, 0⟩ : Dyadic).add ((-rHi).mul (-rHi))⟩ o2 with
    | none => rw [atanCurv_seven_eighth]; exact atan_curv_le_semi x
    | some Jc =>
      have hval : Dyadic.toReal ((⟨1, 0⟩ : Dyadic).add ((-rHi).mul (-rHi)))
          = 1 + c * c := by
        rw [Dyadic.toReal_add, Dyadic.toReal_one, Dyadic.toReal_mul, ← hcdef]
      have hImem : (⟨(⟨1, 0⟩ : Dyadic).add ((-rHi).mul (-rHi)),
          (⟨1, 0⟩ : Dyadic).add ((-rHi).mul (-rHi))⟩ : DInterval).mem
          (⟨(⟨1, 0⟩ : Dyadic).add ((-rHi).mul (-rHi)),
            (⟨1, 0⟩ : Dyadic).add ((-rHi).mul (-rHi))⟩ : DInterval).lo.toReal :=
        ⟨le_rfl, le_rfl⟩
      obtain ⟨_, hJ2⟩ := DInterval.recip_sound hImem hrec
      rw [hval] at hJ2
      have hcx : c ≤ |x| := by
        rw [abs_of_neg hnegx]
        rw [hcval] at hhi
        linarith
      calc 2 * |x| / (1 + x ^ 2) ^ 2
          ≤ 2 * c / (1 + c ^ 2) ^ 2 := atan_curv_le_of_ge hc58 hcx
        _ = 2 * c * (1 / (1 + c * c)) * (1 / (1 + c * c)) := by
            field_simp
        _ ≤ 2 * c * (1 / (1 + c * c)) * Jc.hi.toReal :=
            mul_le_mul_of_nonneg_left hJ2 hA2pos
        _ ≤ 2 * c * Jc.hi.toReal * Jc.hi.toReal := by
            have hJhipos : (0:ℝ) ≤ Jc.hi.toReal := le_trans hwpos hJ2
            have inner : (1 / (1 + c * c)) * Jc.hi.toReal
                ≤ Jc.hi.toReal * Jc.hi.toReal :=
              mul_le_mul_of_nonneg_right hJ2 hJhipos
            have e1 : ((2:ℝ) * c * (1 / (1 + c * c)) * Jc.hi.toReal)
                = (2:ℝ) * c * ((1 / (1 + c * c)) * Jc.hi.toReal) := by ring
            have e2 : ((2:ℝ) * c * Jc.hi.toReal * Jc.hi.toReal)
                = (2:ℝ) * c * (Jc.hi.toReal * Jc.hi.toReal) := by ring
            rw [e1, e2]
            exact mul_le_mul_of_nonneg_left inner hc2pos
        _ = (((⟨2, 0⟩ : Dyadic).mul (-rHi)).mul (Jc.hi.mul Jc.hi)).toReal := by
            rw [Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul,
              Dyadic.toReal_two, ← hcdef]
            ring
  · -- range entirely positive: closest-to-zero endpoint is `c := rLo`
    have hgate : (atanCurvBand).toReal ≤ rLo.toReal := Dyadic.ble_toReal hpos
    rw [hband] at hgate
    set c := rLo.toReal with hcdef
    have hc58 : (5:ℝ) / 8 ≤ c := hgate
    have hc0 : (0:ℝ) ≤ c := le_trans (by norm_num) hc58
    have hc2pos : (0:ℝ) ≤ 2 * c := by linarith
    have hwpos : (0:ℝ) ≤ 1 / (1 + c * c) :=
      div_nonneg (by norm_num) (by positivity)
    have hA2pos : (0:ℝ) ≤ 2 * c * (1 / (1 + c * c)) := by nlinarith
    cases hrec : DInterval.recip ⟨(⟨1, 0⟩ : Dyadic).add (rLo.mul rLo),
        (⟨1, 0⟩ : Dyadic).add (rLo.mul rLo)⟩ o2 with
    | none => rw [atanCurv_seven_eighth]; exact atan_curv_le_semi x
    | some Jc =>
      have hval : Dyadic.toReal ((⟨1, 0⟩ : Dyadic).add (rLo.mul rLo))
          = 1 + c * c := by
        rw [Dyadic.toReal_add, Dyadic.toReal_one, Dyadic.toReal_mul, ← hcdef]
      have hImem : (⟨(⟨1, 0⟩ : Dyadic).add (rLo.mul rLo),
          (⟨1, 0⟩ : Dyadic).add (rLo.mul rLo)⟩ : DInterval).mem
          (⟨(⟨1, 0⟩ : Dyadic).add (rLo.mul rLo),
            (⟨1, 0⟩ : Dyadic).add (rLo.mul rLo)⟩ : DInterval).lo.toReal :=
        ⟨le_rfl, le_rfl⟩
      obtain ⟨_, hJ2⟩ := DInterval.recip_sound hImem hrec
      rw [hval] at hJ2
      have hcx : c ≤ |x| := by
        rw [abs_of_nonneg (by linarith)]
        exact le_trans hcdef.symm.le hlo
      calc 2 * |x| / (1 + x ^ 2) ^ 2
          ≤ 2 * c / (1 + c ^ 2) ^ 2 := atan_curv_le_of_ge hc58 hcx
        _ = 2 * c * (1 / (1 + c * c)) * (1 / (1 + c * c)) := by
            field_simp
        _ ≤ 2 * c * (1 / (1 + c * c)) * Jc.hi.toReal :=
            mul_le_mul_of_nonneg_left hJ2 hA2pos
        _ ≤ 2 * c * Jc.hi.toReal * Jc.hi.toReal := by
            have hJhipos : (0:ℝ) ≤ Jc.hi.toReal := le_trans hwpos hJ2
            have inner : (1 / (1 + c * c)) * Jc.hi.toReal
                ≤ Jc.hi.toReal * Jc.hi.toReal :=
              mul_le_mul_of_nonneg_right hJ2 hJhipos
            have e1 : ((2:ℝ) * c * (1 / (1 + c * c)) * Jc.hi.toReal)
                = (2:ℝ) * c * ((1 / (1 + c * c)) * Jc.hi.toReal) := by ring
            have e2 : ((2:ℝ) * c * Jc.hi.toReal * Jc.hi.toReal)
                = (2:ℝ) * c * (Jc.hi.toReal * Jc.hi.toReal) := by ring
            rw [e1, e2]
            exact mul_le_mul_of_nonneg_left inner hc2pos
        _ = (((⟨2, 0⟩ : Dyadic).mul rLo).mul (Jc.hi.mul Jc.hi)).toReal := by
            rw [Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul,
              Dyadic.toReal_two, ← hcdef]
            ring
  · rw [atanCurv_seven_eighth]
    exact atan_curv_le_semi x

#print axioms atan_curv_mono
#print axioms atan_curv_anti
#print axioms atan_curv_le_semi
#print axioms atan_curv_le_of_ge
#print axioms arctan_residual_sup
#print axioms atanCurv_sound

/-- `DInterval.abs` has a nonnegative lower endpoint. -/
theorem DInterval.abs_lo_nonneg (I : DInterval) : 0 ≤ I.abs.lo.toReal := by
  unfold DInterval.abs
  show Dyadic.toReal (if Dyadic.ble I.hi ⟨0, 0⟩ then -I.hi
    else if Dyadic.ble ⟨0, 0⟩ I.lo then I.lo else ⟨0, 0⟩) ≥ 0
  split_ifs with h1 h2
  · have h := Dyadic.ble_toReal h1
    rw [Dyadic.toReal_zero] at h
    rw [Dyadic.toReal_neg]
    linarith
  · have h := Dyadic.ble_toReal h2
    rw [Dyadic.toReal_zero] at h
    exact h
  · rw [Dyadic.toReal_zero]

/-- **Validity of the sin rule**. -/
theorem valid_trans_sin {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) (N : ℕ) (out : Int) (p : TransTMP)
    {M' : TaylorM n} (h : M.trans .sinK N out p = some M') :
    M'.Valid box (fun ρ => Real.sin (f ρ)) ∧ M'.y = M.y ∧ M'.w = M.w := by
  have hV0 := hV
  obtain ⟨hmem, hw, hfB, hrem⟩ := hV
  unfold TaylorM.trans at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨V, hVv, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨J, hJ, h⟩ := h
  obtain rfl : M' = ⟨M.y, M.w, V, fun i => (M.dfB i).mul J,
    ((M.err.mul J.abs.hi).add
      (((M.W.mul M.W).mul ⟨1, -1⟩).add
        ((M.W.mul (M.W.mul M.W)).mul ⟨1, -2⟩))).chopCeilTo M.errScale⟩ := h.symm
  have hJmem : J.mem (Real.cos (f fun i => (M.y i).toReal)) := IExpr.transOn_sound .cosK hfB hJ
  refine ⟨⟨hmem, hw, IExpr.transOn_sound .sinK hfB hVv, ?_⟩, rfl, rfl⟩
  intro ρ hρ
  obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
  have hW := TaylorM.Valid.abs_sub_le_W hV0 hρ ha hbound
  have hW0 := TaylorM.W_nonneg M
  refine ⟨fun i => a i * Real.cos (f fun i => (M.y i).toReal),
    fun i => DInterval.mem_mul (ha i) hJmem, ?_⟩
  have herr' : ((M.err.mul J.abs.hi).add
      (((M.W.mul M.W).mul ⟨1, -1⟩).add
        ((M.W.mul (M.W.mul M.W)).mul ⟨1, -2⟩))).toReal
      = M.err.toReal * J.abs.hi.toReal
        + (M.W.toReal ^ 2 / 2 + M.W.toReal ^ 3 / 4) := by
    rw [Dyadic.toReal_add, Dyadic.toReal_mul, Dyadic.toReal_add, Dyadic.toReal_mul,
      Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul]
    norm_num [Dyadic.toReal_def]
    ring
  have hchop : ((M.err.mul J.abs.hi).add
      (((M.W.mul M.W).mul ⟨1, -1⟩).add
        ((M.W.mul (M.W.mul M.W)).mul ⟨1, -2⟩))).toReal
      ≤ (⟨M.y, M.w, V, fun i => (M.dfB i).mul J,
        ((M.err.mul J.abs.hi).add
          (((M.W.mul M.W).mul ⟨1, -1⟩).add
            ((M.W.mul (M.W.mul M.W)).mul ⟨1, -2⟩))).chopCeilTo M.errScale⟩ :
              TaylorM n).err.toReal := by
    show _ ≤ (((M.err.mul J.abs.hi).add
        (((M.W.mul M.W).mul ⟨1, -1⟩).add
          ((M.W.mul (M.W.mul M.W)).mul ⟨1, -2⟩))).chopCeilTo M.errScale).toReal
    exact Dyadic.toReal_le_chopCeilTo _ _
  refine le_trans ?_ hchop
  rw [herr']
  have hsum : (∑ i, a i * Real.cos (f fun i => (M.y i).toReal) * (ρ i - (M.y i).toReal))
      = Real.cos (f fun i => (M.y i).toReal) * ∑ i, a i * (ρ i - (M.y i).toReal) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hdecomp : Real.sin (f ρ) - Real.sin (f fun i => (M.y i).toReal)
      - Real.cos (f fun i => (M.y i).toReal) * ∑ i, a i * (ρ i - (M.y i).toReal)
      = (Real.sin (f ρ) - Real.sin (f fun i => (M.y i).toReal)
          - Real.cos (f fun i => (M.y i).toReal) * (f ρ - (f fun i => (M.y i).toReal)))
        + Real.cos (f fun i => (M.y i).toReal)
          * (f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)) := by
    ring
  rw [hsum, hdecomp]
  have hT1 : |Real.sin (f ρ) - Real.sin (f fun i => (M.y i).toReal)
      - Real.cos (f fun i => (M.y i).toReal) * (f ρ - (f fun i => (M.y i).toReal))|
      ≤ M.W.toReal ^ 2 / 2 + M.W.toReal ^ 3 / 4 := by
    refine le_trans sin_residual ?_
    have h1' : (f ρ - (f fun i => (M.y i).toReal)) ^ 2 ≤ M.W.toReal ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hW 2
    have h2' : |f ρ - (f fun i => (M.y i).toReal)| ^ 3 ≤ M.W.toReal ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) hW 3
    gcongr
  have hT2 : |Real.cos (f fun i => (M.y i).toReal)
      * (f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal))|
      ≤ M.err.toReal * J.abs.hi.toReal := by
    rw [abs_mul]
    have hq := (DInterval.mem_abs hJmem).2
    have hJ0 : 0 ≤ J.abs.hi.toReal := le_trans (abs_nonneg _) hq
    calc |Real.cos (f fun i => (M.y i).toReal)|
        * |f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)|
        ≤ J.abs.hi.toReal * M.err.toReal :=
        mul_le_mul hq hbound (abs_nonneg _) hJ0
      _ = M.err.toReal * J.abs.hi.toReal := mul_comm _ _
  exact le_trans (abs_add_le _ _) (by linarith [hT1, hT2])

/-- **Validity of the log rule**. -/
theorem valid_trans_ln {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) (N : ℕ) (out : Int) (p : TransTMP)
    {M' : TaylorM n} (h : M.trans .lnK N out p = some M') :
    M'.Valid box (fun ρ => Real.log (f ρ)) ∧ M'.y = M.y ∧ M'.w = M.w := by
  have hV0 := hV
  obtain ⟨hmem, hw, hfB, hrem⟩ := hV
  simp only [TaylorM.trans] at h
  split at h
  · next hc =>
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨V, hVv, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨J, hJ, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨K, hK, h⟩ := h
    obtain rfl : M' = ⟨M.y, M.w, V, fun i => (M.dfB i).mul J,
      ((M.err.mul J.abs.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo M.errScale⟩ :=
        h.symm
    set cR := (M.fB.lo.add (-M.W)).toReal with hcRdef
    have hc0 : 0 < cR := (Dyadic.isPos_iff _).mp hc
    have hcR : cR = M.fB.lo.toReal - M.W.toReal := by
      rw [hcRdef, Dyadic.toReal_add, Dyadic.toReal_neg, sub_eq_add_neg]
    have hfy_pos : 0 < f (fun i => (M.y i).toReal) :=
      lt_of_lt_of_le hc0 (by rw [hcR]; have := TaylorM.W_nonneg M; linarith [hfB.1])
    have hJmem : J.mem (1 / (f fun i => (M.y i).toReal)) :=
      DInterval.recip_sound hfB hJ
    have hKhi : 1 / (cR * cR) ≤ K.hi.toReal := by
      have hmem2 : (⟨(M.fB.lo.add (-M.W)).mul (M.fB.lo.add (-M.W)),
          (M.fB.lo.add (-M.W)).mul (M.fB.lo.add (-M.W))⟩ : DInterval).mem
          ((M.fB.lo.add (-M.W)).mul (M.fB.lo.add (-M.W))).toReal := ⟨le_rfl, le_rfl⟩
      have h2 := (DInterval.recip_sound hmem2 hK).2
      rw [Dyadic.toReal_mul] at h2
      rwa [← hcRdef] at h2
    refine ⟨⟨hmem, hw, IExpr.transOn_sound .lnK hfB hVv, ?_⟩, rfl, rfl⟩
    intro ρ hρ
    obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
    have hW := TaylorM.Valid.abs_sub_le_W hV0 hρ ha hbound
    have hW0 := TaylorM.W_nonneg M
    have hfρ_pos : 0 < f ρ := by
      have h1 := (abs_le.mp hW).1
      rw [hcR] at hc0
      linarith [hfB.1]
    refine ⟨fun i => a i * (1 / (f fun i => (M.y i).toReal)),
      fun i => DInterval.mem_mul (ha i) hJmem, ?_⟩
    have herr' : ((M.err.mul J.abs.hi).add ((M.W.mul M.W).mul K.hi)).toReal
        = M.err.toReal * J.abs.hi.toReal + M.W.toReal ^ 2 * K.hi.toReal := by
      rw [Dyadic.toReal_add, Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul,
        pow_two]
    have hchop : ((M.err.mul J.abs.hi).add ((M.W.mul M.W).mul K.hi)).toReal
        ≤ (⟨M.y, M.w, V, fun i => (M.dfB i).mul J,
          ((M.err.mul J.abs.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo M.errScale⟩ :
            TaylorM n).err.toReal := by
      show _ ≤ (((M.err.mul J.abs.hi).add ((M.W.mul M.W).mul K.hi)).chopCeilTo
        M.errScale).toReal
      exact Dyadic.toReal_le_chopCeilTo _ _
    refine le_trans ?_ hchop
    rw [herr']
    have hsum : (∑ i, a i * (1 / (f fun i => (M.y i).toReal)) * (ρ i - (M.y i).toReal))
        = (1 / (f fun i => (M.y i).toReal)) * ∑ i, a i * (ρ i - (M.y i).toReal) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hdecomp : Real.log (f ρ) - Real.log (f fun i => (M.y i).toReal)
        - (1 / (f fun i => (M.y i).toReal)) * ∑ i, a i * (ρ i - (M.y i).toReal)
        = (Real.log (f ρ) - Real.log (f fun i => (M.y i).toReal)
            - (f ρ - (f fun i => (M.y i).toReal)) / (f fun i => (M.y i).toReal))
          + (1 / (f fun i => (M.y i).toReal))
            * (f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)) := by
      rw [div_eq_mul_inv]
      ring
    rw [hsum, hdecomp]
    have hT1 : |Real.log (f ρ) - Real.log (f fun i => (M.y i).toReal)
        - (f ρ - (f fun i => (M.y i).toReal)) / (f fun i => (M.y i).toReal)|
        ≤ M.W.toReal ^ 2 * K.hi.toReal := by
      have hW2 : (f ρ - (f fun i => (M.y i).toReal)) ^ 2 ≤ M.W.toReal ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hW 2
      have hdge : cR * cR ≤ f ρ * (f fun i => (M.y i).toReal) := by
        rw [hcR]
        have h1 := (abs_le.mp hW).1
        have hlo1 : M.fB.lo.toReal - M.W.toReal ≤ f ρ := by linarith [hfB.1]
        have hlo2 : M.fB.lo.toReal - M.W.toReal ≤ f (fun i => (M.y i).toReal) := by
          linarith [hfB.1]
        exact mul_le_mul hlo1 hlo2 (by linarith) (by linarith)
      have hdpos : 0 < f ρ * (f fun i => (M.y i).toReal) := mul_pos hfρ_pos hfy_pos
      have hc2pos : 0 < cR * cR := mul_pos hc0 hc0
      calc |Real.log (f ρ) - Real.log (f fun i => (M.y i).toReal)
          - (f ρ - (f fun i => (M.y i).toReal)) / (f fun i => (M.y i).toReal)|
          ≤ (f ρ - (f fun i => (M.y i).toReal)) ^ 2
            / (f ρ * (f fun i => (M.y i).toReal)) := log_residual hfρ_pos hfy_pos
        _ = (f ρ - (f fun i => (M.y i).toReal)) ^ 2
            * (1 / (f ρ * (f fun i => (M.y i).toReal))) := by
            rw [div_eq_mul_inv, one_div]
        _ ≤ M.W.toReal ^ 2 * (1 / (cR * cR)) := by
            exact mul_le_mul hW2 (one_div_le_one_div_of_le hc2pos hdge)
              (by positivity) (sq_nonneg _)
        _ ≤ M.W.toReal ^ 2 * K.hi.toReal :=
            mul_le_mul_of_nonneg_left hKhi (sq_nonneg _)
    have hT2 : |(1 / (f fun i => (M.y i).toReal))
        * (f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal))|
        ≤ M.err.toReal * J.abs.hi.toReal := by
      rw [abs_mul]
      have hq := (DInterval.mem_abs hJmem).2
      have hJ0 : 0 ≤ J.abs.hi.toReal := le_trans (abs_nonneg _) hq
      calc |1 / (f fun i => (M.y i).toReal)|
          * |f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)|
          ≤ J.abs.hi.toReal * M.err.toReal :=
          mul_le_mul hq hbound (abs_nonneg _) hJ0
        _ = M.err.toReal * J.abs.hi.toReal := mul_comm _ _
    exact le_trans (abs_add_le _ _) (by linarith [hT1, hT2])
  · exact absurd h (by simp)

/-- **Validity of the arctan rule** (exact-sup curvature bound): the err
curvature term is `W² · C` with
`C := min(atanCurv (fB.lo−W) (fB.hi+W) p.o2) (2·(|fB|+W))`, which bounds the
arctan curvature `2|x|/(1+x²)²` on the whole value range `[fB.lo−W, fB.hi+W]`
of `f` over the box (`atanCurv_sound` plus the elementary cap
`g ≤ 2|x| ≤ 2(|fB|+W)`); the residual is then `(s−t)²·C` by
`arctan_residual_sup`. -/
theorem valid_trans_atan {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) (N : ℕ) (out : Int) (p : TransTMP)
    {M' : TaylorM n} (h : M.trans .arctanK N out p = some M') :
    M'.Valid box (fun ρ => Real.arctan (f ρ)) ∧ M'.y = M.y ∧ M'.w = M.w := by
  have hV0 := hV
  obtain ⟨hmem, hw, hfB, hrem⟩ := hV
  unfold TaylorM.trans at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨V, hVv, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨J, hJ, h⟩ := h
  obtain rfl : M' = ⟨M.y, M.w, V, fun i => (M.dfB i).mul J,
    ((M.err.mul J.abs.hi).add
      ((M.W.mul M.W).mul (Dyadic.dmin
        (atanCurv (M.fB.lo.add (-M.W)) (M.fB.hi.add M.W) p.o2)
        ((⟨2, 0⟩ : Dyadic).mul (M.fB.abs.hi.add M.W))))).chopCeilTo
          M.errScale⟩ := h.symm
  set B := (M.fB.abs.hi.add M.W).toReal with hBdef
  set Cc := (Dyadic.dmin (atanCurv (M.fB.lo.add (-M.W)) (M.fB.hi.add M.W) p.o2)
      ((⟨2, 0⟩ : Dyadic).mul (M.fB.abs.hi.add M.W))).toReal with hCcdef
  have hW0 := TaylorM.W_nonneg M
  have hBnn : 0 ≤ B := by
    rw [hBdef, Dyadic.toReal_add]
    have h1 := (DInterval.mem_abs hfB).2
    have h3 : 0 ≤ M.fB.abs.hi.toReal := le_trans (abs_nonneg _) h1
    linarith
  -- `Cc` bounds the arctan curvature on the whole value range of `f`
  have hCc : ∀ x : ℝ, (M.fB.lo.add (-M.W)).toReal ≤ x →
      x ≤ (M.fB.hi.add M.W).toReal → 2 * |x| / (1 + x ^ 2) ^ 2 ≤ Cc := by
    intro x hx1 hx2
    rw [hCcdef, Dyadic.toReal_dmin]
    have h1 := atanCurv_sound (M.fB.lo.add (-M.W)) (M.fB.hi.add M.W) p.o2 x hx1 hx2
    -- the legacy cap `2·(|fB|+W)`: `g ≤ 2|x| ≤ 2B`
    have hMabs : M.fB.abs.hi.toReal
        = max (max M.fB.lo.toReal (-M.fB.lo.toReal))
            (max M.fB.hi.toReal (-M.fB.hi.toReal)) := by
      show (Dyadic.dmax (Dyadic.dmax M.fB.lo (-M.fB.lo))
          (Dyadic.dmax M.fB.hi (-M.fB.hi))).toReal = _
      rw [Dyadic.toReal_dmax, Dyadic.toReal_dmax, Dyadic.toReal_dmax,
        Dyadic.toReal_neg, Dyadic.toReal_neg]
    have hb3 : M.fB.hi.toReal ≤ M.fB.abs.hi.toReal := by
      rw [hMabs]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hb2 : -(M.fB.lo.toReal) ≤ M.fB.abs.hi.toReal := by
      rw [hMabs]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hx1' : M.fB.lo.toReal - M.W.toReal ≤ x := by
      have h := hx1
      rw [Dyadic.toReal_add, Dyadic.toReal_neg] at h
      linarith
    have hx2' : x ≤ M.fB.hi.toReal + M.W.toReal := by
      have h := hx2
      rw [Dyadic.toReal_add] at h
      linarith
    have hxB : |x| ≤ B := by
      rw [abs_le, hBdef, Dyadic.toReal_add]
      constructor <;> linarith [hb2, hb3, hx1', hx2']
    have hge : (1:ℝ) ≤ (1 + x ^ 2) ^ 2 := by nlinarith [sq_nonneg x]
    have hd1 : 2 * |x| / (1 + x ^ 2) ^ 2 ≤ 2 * |x| :=
      le_trans (div_le_div_of_nonneg_left (by linarith [abs_nonneg x])
          (by positivity) hge)
        (by rw [div_one])
    have hd2 : ((⟨2, 0⟩ : Dyadic).mul (M.fB.abs.hi.add M.W)).toReal
        = 2 * B := by
      rw [Dyadic.toReal_mul, Dyadic.toReal_two]
    exact le_min h1
      (le_trans hd1 (by rw [hd2]; exact mul_le_mul_of_nonneg_left hxB (by norm_num)))
  refine ⟨⟨hmem, hw, IExpr.transOn_sound .arctanK hfB hVv, ?_⟩, rfl, rfl⟩
  intro ρ hρ
  obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
  have hW := TaylorM.Valid.abs_sub_le_W hV0 hρ ha hbound
  -- the value range of `f` over the box
  have hrange1 : (M.fB.lo.add (-M.W)).toReal ≤ f ρ := by
    rw [Dyadic.toReal_add, Dyadic.toReal_neg]
    have := (abs_le.mp hW).1
    linarith [hfB.1]
  have hrange2 : f ρ ≤ (M.fB.hi.add M.W).toReal := by
    rw [Dyadic.toReal_add]
    have := (abs_le.mp hW).2
    linarith [hfB.2]
  have hranget1 : (M.fB.lo.add (-M.W)).toReal ≤ f (fun i => (M.y i).toReal) := by
    rw [Dyadic.toReal_add, Dyadic.toReal_neg]
    linarith [hfB.1, hW0]
  have hranget2 : f (fun i => (M.y i).toReal) ≤ (M.fB.hi.add M.W).toReal := by
    rw [Dyadic.toReal_add]
    linarith [hfB.2, hW0]
  have hJmem : J.mem (1 / (1 + (f fun i => (M.y i).toReal) ^ 2)) := by
    have hlo : 0 ≤ M.fB.abs.lo.toReal := DInterval.abs_lo_nonneg M.fB
    have h1 := DInterval.mem_abs hfB
    have hsqa : ∀ x : ℝ, |x| * |x| = x * x := fun x => by rw [← pow_two, ← pow_two, sq_abs]
    have h2 : M.fB.abs.lo.toReal * M.fB.abs.lo.toReal
        ≤ (f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal) := by
      have h := mul_le_mul h1.1 h1.1 hlo (le_trans hlo h1.1)
      rwa [hsqa] at h
    have h3 : (f fun i => (M.y i).toReal) * (f fun i => (M.y i).toReal)
        ≤ M.fB.abs.hi.toReal * M.fB.abs.hi.toReal := by
      have h0 : 0 ≤ M.fB.abs.hi.toReal := le_trans (abs_nonneg _) h1.2
      have h := mul_le_mul h1.2 h1.2 (abs_nonneg _) h0
      rwa [hsqa] at h
    exact DInterval.recip_sound
      (show (⟨(⟨1, 0⟩ : Dyadic).add (M.fB.abs.lo.mul M.fB.abs.lo),
        (⟨1, 0⟩ : Dyadic).add (M.fB.abs.hi.mul M.fB.abs.hi)⟩ : DInterval).mem
        (1 + (f fun i => (M.y i).toReal) ^ 2) from by
        rw [pow_two]
        constructor <;> rw [Dyadic.toReal_add, Dyadic.toReal_mul, Dyadic.toReal_one]
        · linarith [h2]
        · linarith [h3]) hJ
  refine ⟨fun i => a i * (1 / (1 + (f fun i => (M.y i).toReal) ^ 2)),
    fun i => DInterval.mem_mul (ha i) hJmem, ?_⟩
  have herr' : ((M.err.mul J.abs.hi).add
      ((M.W.mul M.W).mul (Dyadic.dmin
        (atanCurv (M.fB.lo.add (-M.W)) (M.fB.hi.add M.W) p.o2)
        ((⟨2, 0⟩ : Dyadic).mul (M.fB.abs.hi.add M.W))))).toReal
      = M.err.toReal * J.abs.hi.toReal + M.W.toReal ^ 2 * Cc := by
    rw [hCcdef, Dyadic.toReal_add, Dyadic.toReal_mul, Dyadic.toReal_mul,
      Dyadic.toReal_mul, Dyadic.toReal_dmin, ← pow_two]
  have hchop : ((M.err.mul J.abs.hi).add
      ((M.W.mul M.W).mul (Dyadic.dmin
        (atanCurv (M.fB.lo.add (-M.W)) (M.fB.hi.add M.W) p.o2)
        ((⟨2, 0⟩ : Dyadic).mul (M.fB.abs.hi.add M.W))))).toReal
      ≤ (⟨M.y, M.w, V, fun i => (M.dfB i).mul J,
        ((M.err.mul J.abs.hi).add
          ((M.W.mul M.W).mul (Dyadic.dmin
            (atanCurv (M.fB.lo.add (-M.W)) (M.fB.hi.add M.W) p.o2)
            ((⟨2, 0⟩ : Dyadic).mul (M.fB.abs.hi.add M.W))))).chopCeilTo
              M.errScale⟩ : TaylorM n).err.toReal := by
    show _ ≤ (((M.err.mul J.abs.hi).add
        ((M.W.mul M.W).mul (Dyadic.dmin
          (atanCurv (M.fB.lo.add (-M.W)) (M.fB.hi.add M.W) p.o2)
          ((⟨2, 0⟩ : Dyadic).mul (M.fB.abs.hi.add M.W))))).chopCeilTo
        M.errScale).toReal
    exact Dyadic.toReal_le_chopCeilTo _ _
  refine le_trans ?_ hchop
  rw [herr']
  have hsum : (∑ i, a i * (1 / (1 + (f fun i => (M.y i).toReal) ^ 2))
        * (ρ i - (M.y i).toReal))
      = (1 / (1 + (f fun i => (M.y i).toReal) ^ 2))
        * ∑ i, a i * (ρ i - (M.y i).toReal) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hdecomp : Real.arctan (f ρ) - Real.arctan (f fun i => (M.y i).toReal)
      - (1 / (1 + (f fun i => (M.y i).toReal) ^ 2))
        * ∑ i, a i * (ρ i - (M.y i).toReal)
      = (Real.arctan (f ρ) - Real.arctan (f fun i => (M.y i).toReal)
          - (f ρ - (f fun i => (M.y i).toReal))
            / (1 + (f fun i => (M.y i).toReal) ^ 2))
        + (1 / (1 + (f fun i => (M.y i).toReal) ^ 2))
          * (f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)) := by
    rw [div_eq_mul_inv]
    ring
  rw [hsum, hdecomp]
  have hCc0 : (0:ℝ) ≤ Cc := by
    have h := hCc (f (fun i => (M.y i).toReal)) hranget1 hranget2
    have hpos : (0:ℝ) ≤ 2 * |f (fun i => (M.y i).toReal)|
        / (1 + (f fun i => (M.y i).toReal) ^ 2) ^ 2 :=
      div_nonneg (by nlinarith [abs_nonneg (f fun i => (M.y i).toReal)])
        (by positivity)
    linarith
  have hT1 : |Real.arctan (f ρ) - Real.arctan (f fun i => (M.y i).toReal)
      - (f ρ - (f fun i => (M.y i).toReal)) / (1 + (f fun i => (M.y i).toReal) ^ 2)|
      ≤ M.W.toReal ^ 2 * Cc := by
    have hres := arctan_residual_sup (s := f ρ) (t := f fun i => (M.y i).toReal)
      (lo := (M.fB.lo.add (-M.W)).toReal) (hi := (M.fB.hi.add M.W).toReal) (C := Cc)
      hrange1 hrange2 hranget1 hranget2 hCc
    have hW2 : (f ρ - (f fun i => (M.y i).toReal)) ^ 2 ≤ M.W.toReal ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hW 2
    exact le_trans hres (mul_le_mul_of_nonneg_right hW2 hCc0)
  have hT2 : |(1 / (1 + (f fun i => (M.y i).toReal) ^ 2))
      * (f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal))|
      ≤ M.err.toReal * J.abs.hi.toReal := by
    rw [abs_mul]
    have hq := (DInterval.mem_abs hJmem).2
    have hJ0 : 0 ≤ J.abs.hi.toReal := le_trans (abs_nonneg _) hq
    calc |1 / (1 + (f fun i => (M.y i).toReal) ^ 2)|
        * |f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)|
        ≤ J.abs.hi.toReal * M.err.toReal :=
        mul_le_mul hq hbound (abs_nonneg _) hJ0
      _ = M.err.toReal * J.abs.hi.toReal := mul_comm _ _
  exact le_trans (abs_add_le _ _) (by linarith [hT1, hT2])

/-- **Validity of the trans dispatch**. -/
theorem valid_trans {k : TKind} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) (N : ℕ) (out : Int) (p : TransTMP)
    {M' : TaylorM n} (h : M.trans k N out p = some M') :
    M'.Valid box (fun ρ => transReal k (f ρ)) ∧ M'.y = M.y ∧ M'.w = M.w := by
  cases k with
  | sinK => exact valid_trans_sin hV N out p h
  | cosK => simp [TaylorM.trans] at h
  | arctanK => exact valid_trans_atan hV N out p h
  | lnK => exact valid_trans_ln hV N out p h

/-- Exact constant model of a closed (variable-free) subexpression with a
successful plain evaluation: the value is `ρ`-independent, so zero slopes and
zero remainder are *exact*.  This is what makes the rung-`2048` closed `trans`
constants (`arctan 1` etc.) free per leaf — the memoized `evalFillC` enclosure
is computed once per driver run. -/
def closedTM {n : ℕ} (box : Fin n → DInterval) (I : DInterval) : TaylorM n :=
  ⟨boxCenter box, boxW box, I, fun _ => ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨0, 0⟩⟩

/-- Validity of the constant model. -/
theorem valid_closed {n : ℕ} {box : Fin n → DInterval} {e : IExpr n} {I : DInterval}
    (hcell : CellOK box) (hcl : e.isClosed = true) (hI : e.eval box = some I) :
    (closedTM box I).Valid box (fun ρ => e.evalReal ρ) := by
  refine ⟨fun i => (hcell i).1, fun i => (hcell i).2,
    IExpr.eval_mem e box _ (fun i => (hcell i).1) I hI, ?_⟩
  intro ρ hρ
  refine ⟨fun _ => 0, fun i => ?_, ?_⟩
  · show (⟨⟨0, 0⟩, ⟨0, 0⟩⟩ : DInterval).mem (0 : ℝ)
    exact ⟨by simp, by simp⟩
  · have hc := IExpr.evalReal_const_of_isClosed hcl ρ (fun i => (boxCenter box i).toReal)
    have h0 : (∑ i, (0 : ℝ) * (ρ i - ((closedTM box I).y i).toReal)) = 0 := by
      exact Finset.sum_eq_zero fun i _ => by rw [zero_mul]
    rw [h0]
    show |e.evalReal ρ - e.evalReal (fun i => (boxCenter box i).toReal) - 0|
      ≤ (⟨0, 0⟩ : Dyadic).toReal
    rw [hc, sub_self, sub_zero, abs_zero, Dyadic.toReal_zero]


/-! ## Single-pass Taylor-model evaluation -/

/-- Single-pass Taylor-model evaluation (TM0: `const`/`var`/`neg`/`add`/`sub`/
`mul`/`sqrt` only; `abs`/`ite`/`div`/`trans` return `none`).  The center is
always the box midpoint; `sqrt` certificates are consumed from the list in
traversal order (each `sqrt` node takes the head bundle). -/
def evalTM {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (TaylorM n × TMParams)
  | .const d, ps => some (constTM box d, ps)
  | .var k, ps => some (varTM box k, ps)
  | .neg e, ps => (evalTM box e ps).map fun (M, ps') => (M.neg, ps')
  | .add e₁ e₂, ps =>
      (evalTM box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTM box e₂ ps₁).map fun (M₂, ps₂) => (M₁.add M₂, ps₂)
  | .sub e₁ e₂, ps =>
      (evalTM box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTM box e₂ ps₁).map fun (M₂, ps₂) => (M₁.sub M₂, ps₂)
  | .mul e₁ e₂, ps =>
      (evalTM box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTM box e₂ ps₁).map fun (M₂, ps₂) => (M₁.mul M₂, ps₂)
  | .div e₁ e₂ _, ps =>
      (evalTM box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTM box e₂ ps₁).bind fun (M₂, ps₂) =>
      ps₂.invCerts.head?.bind fun p =>
      (M₂.inv p).map fun Mi => (M₁.mul Mi, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail,
        ps₂.transCerts⟩)
  | .sqrt e _ _, ps =>
      (evalTM box e ps).bind fun (M₀, ps₀) =>
      ps₀.sqrtCerts.head?.bind fun p =>
      (M₀.sqrt p).map fun M' => (M', ⟨ps₀.sqrtCerts.tail, ps₀.invCerts,
        ps₀.transCerts⟩)
  | .trans k e N out, ps =>
      if e.isClosed then
        ((IExpr.trans k e N out).eval box).map fun I => (closedTM box I, ps)
      else
        (evalTM box e ps).bind fun (M₀, ps₀) =>
        ps₀.transCerts.head?.bind fun p =>
        (M₀.trans k N out p).map fun M' =>
          (M', ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩)
  | .abs _, _ => none
  | .ite _ _ _, _ => none

/-- **Soundness of `evalTM`**: a successful evaluation produces a valid model
of the real semantics, centered at the box midpoint with the midpoint
envelope. -/
theorem evalTM_sound {n : ℕ} {box : Fin n → DInterval} :
    ∀ (e : IExpr n) (ps ps' : TMParams) (M : TaylorM n),
      (∀ i, (box i).wf = true) →
      evalTM box e ps = some (M, ps') →
      M.Valid box (fun ρ => e.evalReal ρ) ∧ M.y = boxCenter box ∧ M.w = boxW box := by
  intro e
  induction e with
  | const d =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨valid_const (cellOK_of_wf hwf) d, rfl, rfl⟩
  | var k =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨valid_var (cellOK_of_wf hwf) k, rfl, rfl⟩
  | neg e ih =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₀, ps₀⟩, he, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
      exact ⟨valid_neg hV, hy, hw⟩
  | add e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_add hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | sub e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_sub hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | mul e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_mul hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | sqrt e s₁ s₂ ih =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₀, ps₀⟩, he, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨M', hs, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
      obtain ⟨hV', hyy, hww⟩ := valid_sqrt hV p hs
      refine ⟨hV', ?_, ?_⟩
      · show M'.y = boxCenter box
        exact hyy.trans hy
      · show M'.w = boxW box
        exact hww.trans hw
  | abs e ih =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      exact absurd h (by simp)
  | ite c t e ihc iht ihe =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      exact absurd h (by simp)
  | div e₁ e₂ out ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨Mi, hi, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_div hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂]) p hi
  | trans k e N out ih =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      by_cases hcl : e.isClosed = true
      · rw [if_pos hcl] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_closed (cellOK_of_wf hwf) hcl hI, rfl, rfl⟩
      · rw [if_neg hcl] at h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨⟨M₀, ps₀⟩, he, h⟩ := h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨p, _hp, h⟩ := h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨M', hs, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
        obtain ⟨hV', hyy, hww⟩ := valid_trans hV N out p hs
        refine ⟨hV', ?_, ?_⟩
        · show M'.y = boxCenter box
          exact hyy.trans hy
        · show M'.w = boxW box
          exact hww.trans hw

/-- Syntactic TM-safety check (design §3.2/§5.2): no `abs`/`ite`/`trans`
nodes.  Semantic safety of `div`/`sqrt` (base away from zero / positive) is
checked by the `Option`-valued rules at evaluation time — `evalTM` fails safe
(`none`). -/
def IExpr.TMSafe {n : ℕ} : IExpr n → Bool
  | .const _ => true
  | .var _ => true
  | .neg e => e.TMSafe
  | .abs _ => false
  | .ite _ _ _ => false
  | .add e₁ e₂ => e₁.TMSafe && e₂.TMSafe
  | .sub e₁ e₂ => e₁.TMSafe && e₂.TMSafe
  | .mul e₁ e₂ => e₁.TMSafe && e₂.TMSafe
  | .div e₁ e₂ _ => e₁.TMSafe && e₂.TMSafe
  | .sqrt e _ _ => e.TMSafe
  | .trans k _ _ _ => match k with
      | .sinK | .arctanK | .lnK => true
      | .cosK => false

/-! ## Hybrid evaluation: zero-order fallback for TM-unsafe nodes

For the stage-A-style measurement on real programs (which contain
`trans`/`ite`/`abs` nodes), the strict `evalTM` would return `none` on the
whole expression.  `evalTMH` falls back, per unsupported (or failed) node, to
the **trivial zero-order model**: the plain box enclosure with zero slopes
and `err = width` — valid because both `f(ρ)` and `f(y)` lie in the
enclosure.  Trans-node enclosures are rung-tight (`~2⁻⁶⁴`), so the hybrid
keeps the TM advantage on the algebraic part while degrading gracefully. -/

/-- The trivial zero-order model of any subexpression with a successful plain
interval evaluation. -/
def fallbackTM {n : ℕ} (box : Fin n → DInterval) (I : DInterval) : TaylorM n :=
  ⟨boxCenter box, boxW box, I, fun _ => ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, I.hi.add (-I.lo)⟩

/-- Validity of the zero-order fallback model. -/
theorem valid_fallback {n : ℕ} {box : Fin n → DInterval} {e : IExpr n} {I : DInterval}
    (hcell : CellOK box) (hI : e.eval box = some I) :
    (fallbackTM box I).Valid box (fun ρ => e.evalReal ρ) := by
  refine ⟨fun i => (hcell i).1, fun i => (hcell i).2, ?_, ?_⟩
  · exact IExpr.eval_mem e box _ (fun i => (hcell i).1) I hI
  · intro ρ hρ
    refine ⟨fun _ => 0, fun i => ?_, ?_⟩
    · show (⟨⟨0, 0⟩, ⟨0, 0⟩⟩ : DInterval).mem (0 : ℝ)
      exact ⟨by simp, by simp⟩
    have h1 := IExpr.eval_mem e box ρ hρ I hI
    have h2 := IExpr.eval_mem e box _ (fun i => (hcell i).1) I hI
    have h0 : (∑ i, (0 : ℝ) * (ρ i - ((fallbackTM box I).y i).toReal)) = 0 := by
      exact Finset.sum_eq_zero fun i _ => by rw [zero_mul]
    rw [h0]
    show |e.evalReal ρ - e.evalReal (fun i => (boxCenter box i).toReal) - 0|
      ≤ (I.hi.add (-I.lo)).toReal
    rw [sub_zero, Dyadic.toReal_add, Dyadic.toReal_neg, sub_eq_add_neg, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Hybrid single-pass evaluation: TM rules for `const`/`var`/`neg`/`add`/
`sub`/`mul`, TM rules with fallback for `div`/`sqrt`, and plain-fallback for
`abs`/`ite`/`trans`.  `none` only when even the plain evaluation fails. -/
def evalTMH {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (TaylorM n × TMParams)
  | .const d, ps => some (constTM box d, ps)
  | .var k, ps => some (varTM box k, ps)
  | .neg e, ps => (evalTMH box e ps).map fun (M, ps') => (M.neg, ps')
  | .add e₁ e₂, ps =>
      (evalTMH box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMH box e₂ ps₁).map fun (M₂, ps₂) => (M₁.add M₂, ps₂)
  | .sub e₁ e₂, ps =>
      (evalTMH box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMH box e₂ ps₁).map fun (M₂, ps₂) => (M₁.sub M₂, ps₂)
  | .mul e₁ e₂, ps =>
      (evalTMH box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMH box e₂ ps₁).map fun (M₂, ps₂) => (M₁.mul M₂, ps₂)
  | .div e₁ e₂ out, ps =>
      (evalTMH box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMH box e₂ ps₁).bind fun (M₂, ps₂) =>
      ps₂.invCerts.head?.bind fun p =>
      ((M₂.inv p).map fun Mi => (M₁.mul Mi, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail,
          ps₂.transCerts⟩)).orElse
        (fun _ => ((IExpr.div e₁ e₂ out).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩))
  | .sqrt e s₁ s₂, ps =>
      (evalTMH box e ps).bind fun (M₀, ps₀) =>
      ps₀.sqrtCerts.head?.bind fun p =>
      ((M₀.sqrt p).map fun M' => (M', ⟨ps₀.sqrtCerts.tail, ps₀.invCerts,
          ps₀.transCerts⟩)).orElse
        (fun _ => ((IExpr.sqrt e s₁ s₂).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩))
  | .abs e, ps => ((IExpr.abs e).eval box).map fun I => (fallbackTM box I, ps)
  | .ite c t e, ps => ((IExpr.ite c t e).eval box).map fun I => (fallbackTM box I, ps)
  | .trans k e N out, ps =>
      if e.isClosed then
        ((IExpr.trans k e N out).eval box).map fun I => (closedTM box I, ps)
      else
        (evalTMH box e ps).bind fun (M₀, ps₀) =>
        ps₀.transCerts.head?.bind fun p =>
        ((M₀.trans k N out p).map fun M' =>
            (M', ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩)).orElse
          (fun _ => ((IExpr.trans k e N out).eval box).map fun I =>
            (fallbackTM box I, ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩))

/-- **Soundness of `evalTMH`** (same conclusion as `evalTM_sound`). -/
theorem evalTMH_sound {n : ℕ} {box : Fin n → DInterval} :
    ∀ (e : IExpr n) (ps ps' : TMParams) (M : TaylorM n),
      (∀ i, (box i).wf = true) →
      evalTMH box e ps = some (M, ps') →
      M.Valid box (fun ρ => e.evalReal ρ) ∧ M.y = boxCenter box ∧ M.w = boxW box := by
  intro e
  induction e with
  | const d =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨valid_const (cellOK_of_wf hwf) d, rfl, rfl⟩
  | var k =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨valid_var (cellOK_of_wf hwf) k, rfl, rfl⟩
  | neg e ih =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₀, ps₀⟩, he, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
      exact ⟨valid_neg hV, hy, hw⟩
  | add e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_add hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | sub e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_sub hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | mul e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_mul hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | div e₁ e₂ out ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      cases hi : M₂.inv p with
      | none =>
        rw [hi] at h
        rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
      | some Mi =>
        rw [hi] at h
        rw [Option.map_some, Option.orElse_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
        refine ⟨?_, hy₁, hw₁⟩
        exact valid_div hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂]) p hi
  | sqrt e s₁ s₂ ih =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₀, ps₀⟩, he, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
      cases hs : M₀.sqrt p with
      | none =>
        rw [hs] at h
        rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
      | some M' =>
        rw [hs] at h
        rw [Option.map_some, Option.orElse_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
        obtain ⟨hV', hyy, hww⟩ := valid_sqrt hV p hs
        refine ⟨hV', ?_, ?_⟩
        · show M'.y = boxCenter box
          exact hyy.trans hy
        · show M'.w = boxW box
          exact hww.trans hw
  | abs e ih =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨I, hI, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
  | ite c t e ihc iht ihe =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨I, hI, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
  | trans k e N out ih =>
      intro ps ps' M hwf h
      simp only [evalTMH] at h
      by_cases hcl : e.isClosed = true
      · rw [if_pos hcl] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_closed (cellOK_of_wf hwf) hcl hI, rfl, rfl⟩
      · rw [if_neg hcl] at h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨⟨M₀, ps₀⟩, he, h⟩ := h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨p, _hp, h⟩ := h
        obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
        cases hs : M₀.trans k N out p with
      | none =>
        rw [hs] at h
        rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
      | some M' =>
        rw [hs] at h
        rw [Option.map_some, Option.orElse_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
        obtain ⟨hV', hyy, hww⟩ := valid_trans hV N out p hs
        refine ⟨hV', ?_, ?_⟩
        · show M'.y = boxCenter box
          exact hyy.trans hy
        · show M'.w = boxW box
          exact hww.trans hw

/-! ## M2: the kernel ite-hull rule

C-side counterpart: `pipeline/interval/bb_arb.c` (`--ite-hull`, the OP_ITE
guard-straddle path): both branch TMs are evaluated, their pointwise boxes
`[f0 − W, f0 + W]` are unioned, and the composite degrades to the constant
model `f0 = union midpoint`, `df = ddf = 0`, `err = half width`.  Soundness
is pointwise: whatever the guard selects, `f(ρ)` is one of the two branch
values, hence lies in the union.

Kernel version (this section): in the ∃-slope `TaylorM.Valid` semantics the
center value `f(y)` is only known up to the branch taken at `y`, so the
composite keeps the whole hull interval as `fB` and pays the full hull width
as `err` (the C-side bounds `|f(ρ) − f0|` while the Lean semantics bounds
`|f(ρ) − f(y)|`, so `err_lean = 2 · err_C`; both sound, the Lean composite is
wider by exactly the C-side half-width).  The **guard is never evaluated** —
hull synthesis depends only on the two branch models, so guard-straddling
leaves (the whole 549 lane) close without any guard decision, and guards
whose own interval evaluation fails (e.g. a `div` meeting zero) are fine too.
A failing *branch* (`div` past its certificates, negative radicand, …) still
fails the node, as on the C side.  C¹ note: on the 549 lane the two branches
join C¹ at the discriminant zero, so a `df`-hull composite could tighten
`err` substantially; this round ships the conservative constant version,
matching the C-side default. -/

/-- The certified pointwise value range of a model over its box:
`[fB.lo − W, fB.hi + W]`.  `Valid` puts every box value `f(ρ)` in this
range (`TaylorM.Valid.abs_sub_le_W`). -/
def TaylorM.valueRange {n : ℕ} (M : TaylorM n) : DInterval :=
  ⟨(M.fB.lo).add (-M.W), (M.fB.hi).add M.W⟩

/-- The ite-hull composite model: the constant model over the hull of the
two branch value ranges (the kernel analogue of the C-side `--ite-hull`
constant synthesis). -/
def iteHullTM {n : ℕ} (box : Fin n → DInterval) (Mt Me : TaylorM n) : TaylorM n :=
  fallbackTM box ((Mt.valueRange).hull Me.valueRange)

/-- **Validity of the ite-hull composite**: if both branch models are valid
on the box, the constant hull model is valid for the guard-selected function
`ρ ↦ if c(ρ) < 0 then ft ρ else fe ρ`.  Whatever the guard evaluates to
(when it evaluates at all), the selected branch value lies in that branch
model's value range, hence in the hull — and so do the composite's own
center value and every box value, which bounds all pairwise distances by the
hull width. -/
theorem valid_iteHull {n : ℕ} {Mt Me : TaylorM n} {box : Fin n → DInterval}
    {ft fe : (Fin n → ℝ) → ℝ} (c : IExpr n)
    (ht : Mt.Valid box ft) (he : Me.Valid box fe) (hcell : CellOK box) :
    (iteHullTM box Mt Me).Valid box
      (fun ρ => if c.evalReal ρ < 0 then ft ρ else fe ρ) := by
  have hIn : ∀ (M : TaylorM n) (f : (Fin n → ℝ) → ℝ), M.Valid box f →
      ∀ ρ, boxMem box ρ → M.valueRange.mem (f ρ) := by
    intro M f hV ρ hρ
    have hV0 := hV
    obtain ⟨_, _, hfB, hrem⟩ := hV
    obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
    have hW := TaylorM.Valid.abs_sub_le_W hV0 hρ ha hbound
    rw [abs_le] at hW
    constructor
    · show Dyadic.toReal ((M.fB.lo).add (-M.W)) ≤ f ρ
      rw [Dyadic.toReal_add, Dyadic.toReal_neg]
      linarith [hfB.1, hW.1]
    · show f ρ ≤ Dyadic.toReal ((M.fB.hi).add M.W)
      rw [Dyadic.toReal_add]
      linarith [hfB.2, hW.2]
  have hcen : boxMem box (fun i => ((iteHullTM box Mt Me).y i).toReal) :=
    fun i => (hcell i).1
  have hmemcen : ((Mt.valueRange).hull Me.valueRange).mem
      (if c.evalReal (fun i => ((iteHullTM box Mt Me).y i).toReal) < 0
        then ft (fun i => ((iteHullTM box Mt Me).y i).toReal)
        else fe (fun i => ((iteHullTM box Mt Me).y i).toReal)) := by
    by_cases hlt : c.evalReal (fun i => ((iteHullTM box Mt Me).y i).toReal) < 0
    · rw [if_pos hlt]
      exact DInterval.mem_hull_left (hIn Mt ft ht _ hcen)
    · rw [if_neg hlt]
      exact DInterval.mem_hull_right (hIn Me fe he _ hcen)
  refine ⟨fun i => (hcell i).1, fun i => (hcell i).2, hmemcen, ?_⟩
  intro ρ hρ
  refine ⟨fun _ => 0, fun i => ?_, ?_⟩
  · show (⟨⟨0, 0⟩, ⟨0, 0⟩⟩ : DInterval).mem (0 : ℝ)
    exact ⟨by simp, by simp⟩
  have hval : ((Mt.valueRange).hull Me.valueRange).mem
      (if c.evalReal ρ < 0 then ft ρ else fe ρ) := by
    by_cases hlt : c.evalReal ρ < 0
    · rw [if_pos hlt]
      exact DInterval.mem_hull_left (hIn Mt ft ht ρ hρ)
    · rw [if_neg hlt]
      exact DInterval.mem_hull_right (hIn Me fe he ρ hρ)
  have h0 : (∑ i, (0 : ℝ) * (ρ i - ((iteHullTM box Mt Me).y i).toReal)) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [zero_mul]
  rw [h0, sub_zero]
  show |(if c.evalReal ρ < 0 then ft ρ else fe ρ)
        - (if c.evalReal (fun i => ((iteHullTM box Mt Me).y i).toReal) < 0
            then ft (fun i => ((iteHullTM box Mt Me).y i).toReal)
            else fe (fun i => ((iteHullTM box Mt Me).y i).toReal))|
      ≤ (((Mt.valueRange).hull Me.valueRange).hi.add
          (-((Mt.valueRange).hull Me.valueRange).lo)).toReal
  rw [Dyadic.toReal_add, Dyadic.toReal_neg, sub_eq_add_neg, abs_le]
  constructor <;> linarith [hval.1, hval.2, hmemcen.1, hmemcen.2]

/-- M2: hull-based single-pass evaluation.  Identical to `evalTMH` except
that `ite c t e` recursively evaluates **both** branches and combines the
two models into the constant hull composite (`iteHullTM`); the guard is
never evaluated, and a failing branch fails the node (C-side `--ite-hull`
semantics).  On expressions without `ite` it coincides definitionally with
`evalTMH`. -/
def evalTMHull {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (TaylorM n × TMParams)
  | .ite _ t e, ps =>
      (evalTMHull box t ps).bind fun (Mt, ps₁) =>
      (evalTMHull box e ps₁).map fun (Me, ps₂) => (iteHullTM box Mt Me, ps₂)
  | e, ps => evalTMH box e ps

/-- **Soundness of `evalTMHull`** (same conclusion as `evalTMH_sound`): a
successful hull evaluation produces a valid model of the real semantics,
centered at the box midpoint with the midpoint envelope.  Every non-`ite`
node delegates to `evalTMH` verbatim, so only the `ite` case is new: both
branch models are valid by the induction hypotheses, and `valid_iteHull`
closes the hull composite. -/
theorem evalTMHull_sound {n : ℕ} {box : Fin n → DInterval} :
    ∀ (e : IExpr n) (ps ps' : TMParams) (M : TaylorM n),
      (∀ i, (box i).wf = true) →
      evalTMHull box e ps = some (M, ps') →
      M.Valid box (fun ρ => e.evalReal ρ) ∧ M.y = boxCenter box ∧ M.w = boxW box := by
  intro e
  induction e with
  | const d =>
      intro ps ps' M hwf h
      exact evalTMH_sound _ _ _ _ hwf h
  | var k =>
      intro ps ps' M hwf h
      exact evalTMH_sound _ _ _ _ hwf h
  | neg e _ih =>
      intro ps ps' M hwf h
      exact evalTMH_sound _ _ _ _ hwf h
  | abs e _ih =>
      intro ps ps' M hwf h
      exact evalTMH_sound _ _ _ _ hwf h
  | add e₁ e₂ _ih₁ _ih₂ =>
      intro ps ps' M hwf h
      exact evalTMH_sound _ _ _ _ hwf h
  | sub e₁ e₂ _ih₁ _ih₂ =>
      intro ps ps' M hwf h
      exact evalTMH_sound _ _ _ _ hwf h
  | mul e₁ e₂ _ih₁ _ih₂ =>
      intro ps ps' M hwf h
      exact evalTMH_sound _ _ _ _ hwf h
  | div e₁ e₂ _out _ih₁ _ih₂ =>
      intro ps ps' M hwf h
      exact evalTMH_sound _ _ _ _ hwf h
  | sqrt e _s₁ _s₂ _ih =>
      intro ps ps' M hwf h
      exact evalTMH_sound _ _ _ _ hwf h
  | trans k e N out _ih =>
      intro ps ps' M hwf h
      exact evalTMH_sound _ _ _ _ hwf h
  | ite c t e _ihc iht ihe =>
      intro ps ps' M hwf h
      simp only [evalTMHull] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨Mt, ps₁⟩, ht, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨Me, ps₂⟩, he, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hVt, _, _⟩ := iht ps ps₁ Mt hwf ht
      obtain ⟨hVe, _, _⟩ := ihe ps₁ ps₂ Me hwf he
      exact ⟨valid_iteHull c hVt hVe (cellOK_of_wf hwf), rfl, rfl⟩

/-! ## M2 pilot: `|x|`-style `ite` on a guard-straddling box -/

/-- Box `[-1, 1]`. -/
def exBoxIteHull : Fin 1 → DInterval := fun _ => ⟨⟨-1, 0⟩, ⟨1, 0⟩⟩

/-- `ite(x, −x, x)`: pointwise `|x|`.  The guard interval is `[-1, 1]`
(straddles 0), so the strict `evalTM` rejects the whole expression. -/
def exIteAbs : IExpr 1 := .ite (.var 0) (.neg (.var 0)) (.var 0)

theorem exBoxIteHull_wf : ∀ i, (exBoxIteHull i).wf = true := fun i => by
  fin_cases i; decide

/-- The strict evaluator rejects the whole expression (kernel computation). -/
theorem exIteHull_strict_none :
    evalTM exBoxIteHull exIteAbs TMParams.empty = none := rfl

/-- The hull evaluator succeeds (both branches evaluate). -/
theorem exIteHull_isSome :
    (evalTMHull exBoxIteHull exIteAbs TMParams.empty).isSome = true := by
  decide

/-- The produced model is valid for pointwise `|x|`. -/
theorem exIteHull_valid (ps ps' : TMParams) (M : TaylorM 1)
    (hE : evalTMHull exBoxIteHull exIteAbs ps = some (M, ps')) :
    M.Valid exBoxIteHull (fun ρ => if ρ 0 < 0 then -ρ 0 else ρ 0) :=
  (evalTMHull_sound exIteAbs ps ps' M exBoxIteHull_wf hE).1

/-- A guard that *fails* plain interval evaluation (divisor `[-1,1]` meets
0): the hybrid `evalTMH` still rejects the whole `ite` because the guard
must be evaluated, while the hull evaluator succeeds — hull synthesis never
touches the guard. -/
def exIteBadGuard : IExpr 1 :=
  .ite (.div (.var 0) (.var 0) (-1)) (.neg (.var 0)) (.var 0)

theorem exIteBadGuard_hybrid_none :
    (evalTMH exBoxIteHull exIteBadGuard TMParams.empty).isSome = false := by
  decide

theorem exIteBadGuard_hull_isSome :
    (evalTMHull exBoxIteHull exIteBadGuard TMParams.empty).isSome = true := by
  decide

#print axioms valid_iteHull
#print axioms evalTMHull_sound
#print axioms exIteHull_strict_none
#print axioms exIteHull_isSome
#print axioms exIteHull_valid
#print axioms exIteBadGuard_hybrid_none
#print axioms exIteBadGuard_hull_isSome

/-! ## Schema v3: the guard-decided hull evaluator (`evalTMHullD`)

Root cause ② of the 20-leaf NEG pilot: the M2 hull evaluator above never
looks at the guard and always pays the double-branch constant hull.  On
leaves where the guard is *sign-definite on the box* — strictly negative, or
nonnegative; the C-side `take_then` decision in `bb_arb.c` `eval_prog_tm`
(`OP_ITE`, `mode=="lt"`: guard interval `hi < 0 → then`, `lo ≥ 0 → else`,
guard eval failure → `TM_FAIL(1)`) — the ite function coincides with one
branch everywhere on the box, so the hull synthesis is pure width doubling
(nested `ite`s multiply it into the err) and the constant composite also
destroys the branch slopes.  `evalTMHullD` ("D" = decidable guard) evaluates
the guard *first* and:

- guard strictly negative on the box (`C.hi.isNeg`) → evaluates the `then`
  branch only, verbatim (no hull, no width doubling, slopes kept);
- guard nonnegative on the box (`C.lo.isNN`) → evaluates the `else` branch
  only, verbatim;
- guard straddles → the M2 double-branch hull composite (unchanged);
- guard evaluation fails → the node fails (C-side `TM_FAIL(1)`).

The guard itself is evaluated by *certified* plain interval evaluation
(`evalIParams`): the `IExpr.eval` semantics, except that `sqrt` mantissas are
consumed from `ps.sqrtCerts` (one `SqrtTMP` per `sqrt` node, traversal order —
549's outer guard contains a `sqrt` whose radicand interval is
leaf-dependent, so the AST's fixed `(0, 0)` slots cannot serve it), `sqrt` of
a straddling radicand clamps the lower end to `0` (`Real.sqrt` of a negative
real is `0`, matching the C-side `ball(0, M)` clamping), and a negative
radicand or a zero-crossing divisor fails the node.

Soundness: the certified guard interval contains the guard's real value at
every box point (`evalIParams_mem`), so a sign-definite interval forces the
same branch at every box point, and validity transports along that pointwise
branch selection (`valid_iteHullD`); the straddle case is `valid_iteHull`
verbatim.  Certificate layout: the guard's `sqrt` nodes consume from the
head of `sqrtCerts` *before* the selected branch(es), so the queue order
becomes guard-first per `ite` node (mirrored by `evalTMHullFill`). -/

namespace TaylorM

/-- Transport of validity along pointwise equality on the box (`Valid`
quantifies only over box points, the center included). -/
theorem Valid.congr_box {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f g : (Fin n → ℝ) → ℝ} (hV : M.Valid box f)
    (hEq : ∀ ρ, boxMem box ρ → g ρ = f ρ) : M.Valid box g := by
  obtain ⟨h1, h2, h3, h4⟩ := hV
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hEq _ h1]
    exact h3
  · intro ρ hρ
    obtain ⟨a, ha, hbound⟩ := h4 ρ hρ
    refine ⟨a, ha, ?_⟩
    rw [hEq ρ hρ, hEq _ h1]
    exact hbound

end TaylorM

/-- Certified plain-interval evaluation of a guard expression (see the
schema-v3 section header): the `IExpr.eval` semantics with certificate-carried
`sqrt` mantissas.  Consumes one `SqrtTMP` per `sqrt` node from the head of
`ps.sqrtCerts`; all other nodes consume nothing. -/
def evalIParams {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (DInterval × TMParams)
  | .const d, ps => some (⟨d, d⟩, ps)
  | .var k, ps => some (box k, ps)
  | .neg e, ps => (evalIParams box e ps).map fun (I, ps') => (I.neg, ps')
  | .abs e, ps => (evalIParams box e ps).map fun (I, ps') => (I.abs, ps')
  | .add e₁ e₂, ps =>
      (evalIParams box e₁ ps).bind fun (I₁, ps₁) =>
      (evalIParams box e₂ ps₁).map fun (I₂, ps₂) => (I₁.add I₂, ps₂)
  | .sub e₁ e₂, ps =>
      (evalIParams box e₁ ps).bind fun (I₁, ps₁) =>
      (evalIParams box e₂ ps₁).map fun (I₂, ps₂) => (I₁.sub I₂, ps₂)
  | .mul e₁ e₂, ps =>
      (evalIParams box e₁ ps).bind fun (I₁, ps₁) =>
      (evalIParams box e₂ ps₁).map fun (I₂, ps₂) => (I₁.mul I₂, ps₂)
  | .div e₁ e₂ out, ps =>
      (evalIParams box e₁ ps).bind fun (I₁, ps₁) =>
      (evalIParams box e₂ ps₁).bind fun (I₂, ps₂) =>
      (DInterval.div I₁ I₂ out).map fun I => (I, ps₂)
  | .sqrt e _ _, ps =>
      (evalIParams box e ps).bind fun (I, ps₀) =>
      ps₀.sqrtCerts.head?.bind fun t =>
      if I.hi.isNeg then none
      else
        (Dyadic.sqrtI I.hi t.shi).bind fun Jh =>
        (if I.lo.isNN then (Dyadic.sqrtI I.lo t.slo).map (fun Jl => Jl.lo)
          else some (⟨0, 0⟩ : Dyadic)).map fun L =>
          (⟨L, Jh.hi⟩, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩)
  | .trans k e N out, ps =>
      (evalIParams box e ps).bind fun (I, ps₀) =>
      (transOn k I N out).map fun J => (J, ps₀)
  | .ite c t e, ps =>
      (evalIParams box c ps).bind fun (C, ps₀) =>
      if C.hi.isNeg then evalIParams box t ps₀
      else if C.lo.isNN then evalIParams box e ps₀
      else
        (evalIParams box t ps₀).bind fun (T, ps₁) =>
        (evalIParams box e ps₁).map fun (E, ps₂) => (T.hull E, ps₂)

/-- **Soundness of `evalIParams`** (`IExpr.eval_mem` with certificate-carried
`sqrt` mantissas): every successful evaluation returns an interval containing
the real value at every assignment pointwise inside the box. -/
theorem evalIParams_mem {n : ℕ} {box : Fin n → DInterval} {ρ : Fin n → ℝ}
    (hρ : ∀ i, (box i).mem (ρ i)) :
    ∀ (e : IExpr n) (ps ps' : TMParams) (I : DInterval),
      evalIParams box e ps = some (I, ps') → I.mem (e.evalReal ρ) := by
  intro e
  induction e with
  | const d =>
      intro ps ps' I h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨le_rfl, le_rfl⟩
  | var k =>
      intro ps ps' I h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact hρ k
  | neg e ih =>
      intro ps ps' I h
      simp only [evalIParams] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨J, ps₀⟩, he, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.mem_neg (ih ps ps₀ J he)
  | abs e ih =>
      intro ps ps' I h
      simp only [evalIParams] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨J, ps₀⟩, he, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.mem_abs (ih ps ps₀ J he)
  | add e₁ e₂ ih₁ ih₂ =>
      intro ps ps' I h
      simp only [evalIParams] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨I₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨I₂, ps₂⟩, h₂, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.mem_add (ih₁ ps ps₁ I₁ h₁) (ih₂ ps₁ ps₂ I₂ h₂)
  | sub e₁ e₂ ih₁ ih₂ =>
      intro ps ps' I h
      simp only [evalIParams] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨I₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨I₂, ps₂⟩, h₂, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.mem_sub (ih₁ ps ps₁ I₁ h₁) (ih₂ ps₁ ps₂ I₂ h₂)
  | mul e₁ e₂ ih₁ ih₂ =>
      intro ps ps' I h
      simp only [evalIParams] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨I₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨I₂, ps₂⟩, h₂, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.mem_mul (ih₁ ps ps₁ I₁ h₁) (ih₂ ps₁ ps₂ I₂ h₂)
  | div e₁ e₂ out ih₁ ih₂ =>
      intro ps ps' I h
      simp only [evalIParams] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨I₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨I₂, ps₂⟩, h₂, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨K, hK, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.div_sound hK (ih₁ ps ps₁ I₁ h₁) (ih₂ ps₁ ps₂ I₂ h₂)
  | sqrt e _ _ ih =>
      intro ps ps' I h
      simp only [evalIParams] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨J, ps₀⟩, he, h⟩ := h
      dsimp only at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, h⟩ := h
      by_cases hneg : J.hi.isNeg = true
      · rw [if_pos hneg] at h; simp at h
      · rw [if_neg hneg] at h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨Jh, hh, h⟩ := h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨L, hl, hI⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
        obtain ⟨hy1, hy2⟩ := ih ps ps₀ J he
        have hhi0 : ¬ (J.hi.toReal < 0) := fun hlt0 =>
          hneg ((Dyadic.isNeg_iff J.hi).mpr hlt0)
        obtain ⟨_, hh2⟩ := Dyadic.sqrtI_sound hh
        have hJh0 : 0 ≤ Jh.hi.toReal :=
          le_trans (Real.sqrt_nonneg _) hh2
        constructor
        · show L.toReal ≤ Real.sqrt (e.evalReal ρ)
          by_cases hnn : J.lo.isNN = true
          · rw [if_pos hnn, Option.map_eq_some_iff] at hl
            obtain ⟨Jl, hJl, hL⟩ := hl
            subst hL
            obtain ⟨hl1, _⟩ := Dyadic.sqrtI_sound hJl
            exact le_trans hl1 (Real.sqrt_le_sqrt hy1)
          · rw [if_neg hnn] at hl
            obtain rfl : L = ⟨0, 0⟩ := (Option.some.inj hl).symm
            rw [Dyadic.toReal_zero]
            by_cases hx : e.evalReal ρ < 0
            · have hs : Real.sqrt (e.evalReal ρ) = 0 :=
                Real.sqrt_eq_zero_of_nonpos (by linarith)
              linarith
            · exact Real.sqrt_nonneg _
        · show Real.sqrt (e.evalReal ρ) ≤ Jh.hi.toReal
          by_cases hx : e.evalReal ρ < 0
          · have hs : Real.sqrt (e.evalReal ρ) = 0 :=
              Real.sqrt_eq_zero_of_nonpos (by linarith)
            linarith
          · exact le_trans (Real.sqrt_le_sqrt (by linarith)) hh2
  | trans k e N out ih =>
      intro ps ps' I h
      simp only [evalIParams] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨J, ps₀⟩, he, h⟩ := h
      dsimp only at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨K, hK, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact IExpr.transOn_sound k (ih ps ps₀ J he) hK
  | ite c t e ihc iht ihe =>
      intro ps ps' I h
      simp only [evalIParams] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨C, ps₀⟩, hc, h⟩ := h
      dsimp only at h
      by_cases hneg : C.hi.isNeg = true
      · rw [if_pos hneg] at h
        have hC := ihc ps ps₀ C hc
        have hlt : c.evalReal ρ < 0 :=
          lt_of_le_of_lt hC.2 ((Dyadic.isNeg_iff C.hi).mp hneg)
        show I.mem (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ)
        rw [if_pos hlt]
        exact iht ps₀ ps' I h
      · rw [if_neg hneg] at h
        by_cases hnn : C.lo.isNN = true
        · rw [if_pos hnn] at h
          have hC := ihc ps ps₀ C hc
          have hge : 0 ≤ c.evalReal ρ :=
            le_trans ((Dyadic.isNN_iff C.lo).mp hnn) hC.1
          have hnot : ¬ c.evalReal ρ < 0 := not_lt.mpr hge
          show I.mem (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ)
          rw [if_neg hnot]
          exact ihe ps₀ ps' I h
        · rw [if_neg hnn] at h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨⟨T, ps₁⟩, ht, h⟩ := h
          dsimp only at h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨E, ps₂⟩, he', hI⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
          show (T.hull E).mem
            (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ)
          by_cases hlt : c.evalReal ρ < 0
          · rw [if_pos hlt]
            exact DInterval.mem_hull_left (iht ps₀ ps₁ T ht)
          · rw [if_neg hlt]
            exact DInterval.mem_hull_right (ihe ps₁ ps₂ E he')

/-- **Guard-decided branch validity, then-side** (the `evalTMHullD` core):
if the guard's certified interval is *strictly negative* on the box, the ite
function coincides with the `then` branch at every box point, so a valid
model of the `then` branch is a valid model of the whole ite — no hull, no
width doubling. -/
theorem valid_iteHullD {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {c t e : IExpr n} {C : DInterval}
    (hV : M.Valid box (fun ρ => t.evalReal ρ))
    (hmem : ∀ ρ, boxMem box ρ → C.mem (c.evalReal ρ))
    (hneg : C.hi.isNeg = true) :
    M.Valid box (fun ρ => (IExpr.ite c t e).evalReal ρ) := by
  refine hV.congr_box fun ρ hρ => ?_
  show (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ)
    = t.evalReal ρ
  rw [if_pos (lt_of_le_of_lt (hmem ρ hρ).2 ((Dyadic.isNeg_iff C.hi).mp hneg))]

/-- **Guard-decided branch validity, else-side**: if the guard's certified
interval is *nonnegative* on the box, the ite function coincides with the
`else` branch at every box point. -/
theorem valid_iteHullD_else {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {c t e : IExpr n} {C : DInterval}
    (hV : M.Valid box (fun ρ => e.evalReal ρ))
    (hmem : ∀ ρ, boxMem box ρ → C.mem (c.evalReal ρ))
    (hnn : C.lo.isNN = true) :
    M.Valid box (fun ρ => (IExpr.ite c t e).evalReal ρ) := by
  refine hV.congr_box fun ρ hρ => ?_
  show (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ)
    = e.evalReal ρ
  rw [if_neg (not_lt.mpr
    (le_trans ((Dyadic.isNN_iff C.lo).mp hnn) (hmem ρ hρ).1))]

/-- M3/schema-v3: the guard-decided hull evaluator.  Full hybrid traversal
(same TM rules as `evalTMH` for every non-`ite` constructor) except at `ite`
nodes, where the guard is evaluated first by certified plain interval
evaluation (`evalIParams`): a sign-definite guard selects the single branch
to evaluate verbatim, a straddling guard falls back to the M2 double-branch
hull composite, and a failing guard evaluation fails the node (C-side
`TM_FAIL(1)`).  Unlike a delegation to `evalTMH` for the non-`ite`
constructors, the self-recursion threads the D treatment to *every* nested
`ite` — delegation would leave inner `ite`s on `evalTMH`'s plain-fallback
arm, whose guard evaluation fails on leaf-dependent `sqrt` radicands (the
0/20 pilot's actual kernel failure mode). -/
def evalTMHullD {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (TaylorM n × TMParams)
  | .const d, ps => some (constTM box d, ps)
  | .var k, ps => some (varTM box k, ps)
  | .neg e, ps => (evalTMHullD box e ps).map fun (M, ps') => (M.neg, ps')
  | .add e₁ e₂, ps =>
      (evalTMHullD box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD box e₂ ps₁).map fun (M₂, ps₂) => (M₁.add M₂, ps₂)
  | .sub e₁ e₂, ps =>
      (evalTMHullD box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD box e₂ ps₁).map fun (M₂, ps₂) => (M₁.sub M₂, ps₂)
  | .mul e₁ e₂, ps =>
      (evalTMHullD box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD box e₂ ps₁).map fun (M₂, ps₂) => (M₁.mul M₂, ps₂)
  | .div e₁ e₂ out, ps =>
      (evalTMHullD box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD box e₂ ps₁).bind fun (M₂, ps₂) =>
      ps₂.invCerts.head?.bind fun p =>
      ((M₂.inv p).map fun Mi => (M₁.mul Mi, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail,
          ps₂.transCerts⟩)).orElse
        (fun _ => ((IExpr.div e₁ e₂ out).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩))
  | .sqrt e s₁ s₂, ps =>
      (evalTMHullD box e ps).bind fun (M₀, ps₀) =>
      ps₀.sqrtCerts.head?.bind fun p =>
      ((M₀.sqrt p).map fun M' => (M', ⟨ps₀.sqrtCerts.tail, ps₀.invCerts,
          ps₀.transCerts⟩)).orElse
        (fun _ => ((IExpr.sqrt e s₁ s₂).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩))
  | .abs e, ps => ((IExpr.abs e).eval box).map fun I => (fallbackTM box I, ps)
  | .trans k e N out, ps =>
      if e.isClosed then
        ((IExpr.trans k e N out).eval box).map fun I => (closedTM box I, ps)
      else
        (evalTMHullD box e ps).bind fun (M₀, ps₀) =>
        ps₀.transCerts.head?.bind fun p =>
        ((M₀.trans k N out p).map fun M' =>
            (M', ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩)).orElse
          (fun _ => ((IExpr.trans k e N out).eval box).map fun I =>
            (fallbackTM box I, ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩))
  | .ite c t e, ps =>
      (evalIParams box c ps).bind fun (C, ps₀) =>
      if C.hi.isNeg then evalTMHullD box t ps₀
      else if C.lo.isNN then evalTMHullD box e ps₀
      else
        (evalTMHullD box t ps₀).bind fun (Mt, ps₁) =>
        (evalTMHullD box e ps₁).map fun (Me, ps₂) => (iteHullTM box Mt Me, ps₂)

/-- **Soundness of `evalTMHullD`** (same conclusion as `evalTMH_sound`): the
non-`ite` cases repeat `evalTMH_sound`'s arguments over the self-recursion,
and the `ite` case adds the certified-guard branch selection
(`valid_iteHullD`/`valid_iteHullD_else`) or the straddle fallback
(`valid_iteHull`). -/
theorem evalTMHullD_sound {n : ℕ} {box : Fin n → DInterval} :
    ∀ (e : IExpr n) (ps ps' : TMParams) (M : TaylorM n),
      (∀ i, (box i).wf = true) →
      evalTMHullD box e ps = some (M, ps') →
      M.Valid box (fun ρ => e.evalReal ρ) ∧ M.y = boxCenter box ∧ M.w = boxW box := by
  intro e
  induction e with
  | const d =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨valid_const (cellOK_of_wf hwf) d, rfl, rfl⟩
  | var k =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨valid_var (cellOK_of_wf hwf) k, rfl, rfl⟩
  | neg e ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₀, ps₀⟩, he, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
      exact ⟨valid_neg hV, hy, hw⟩
  | add e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_add hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | sub e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_sub hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | mul e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_mul hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | div e₁ e₂ out ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      cases hi : M₂.inv p with
      | none =>
        rw [hi] at h
        rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
      | some Mi =>
        rw [hi] at h
        rw [Option.map_some, Option.orElse_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
        refine ⟨?_, hy₁, hw₁⟩
        exact valid_div hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂]) p hi
  | sqrt e s₁ s₂ ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₀, ps₀⟩, he, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
      cases hs : M₀.sqrt p with
      | none =>
        rw [hs] at h
        rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
      | some M' =>
        rw [hs] at h
        rw [Option.map_some, Option.orElse_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
        obtain ⟨hV', hyy, hww⟩ := valid_sqrt hV p hs
        refine ⟨hV', ?_, ?_⟩
        · show M'.y = boxCenter box
          exact hyy.trans hy
        · show M'.w = boxW box
          exact hww.trans hw
  | abs e ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨I, hI, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
  | trans k e N out ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      by_cases hcl : e.isClosed = true
      · rw [if_pos hcl] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_closed (cellOK_of_wf hwf) hcl hI, rfl, rfl⟩
      · rw [if_neg hcl] at h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨⟨M₀, ps₀⟩, he, h⟩ := h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨p, _hp, h⟩ := h
        obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
        cases ht : M₀.trans k N out p with
        | none =>
          rw [ht] at h
          rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
          obtain ⟨I, hI, hfinal⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
          exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
        | some M' =>
          rw [ht] at h
          rw [Option.map_some, Option.orElse_some] at h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
          obtain ⟨hV', hyy, hww⟩ := valid_trans hV N out p ht
          refine ⟨hV', ?_, ?_⟩
          · show M'.y = boxCenter box
            exact hyy.trans hy
          · show M'.w = boxW box
            exact hww.trans hw
  | ite c t e _ihc iht ihe =>
      intro ps ps' M hwf h
      simp only [evalTMHullD] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨C, ps₀⟩, hc, h⟩ := h
      by_cases hneg : C.hi.isNeg = true
      · rw [if_pos hneg] at h
        obtain ⟨hVt, hy, hw⟩ := iht ps₀ ps' M hwf h
        refine ⟨valid_iteHullD hVt (fun ρ hρ => evalIParams_mem hρ c ps ps₀ C hc)
          hneg, hy, hw⟩
      · rw [if_neg hneg] at h
        by_cases hnn : C.lo.isNN = true
        · rw [if_pos hnn] at h
          obtain ⟨hVe, hy, hw⟩ := ihe ps₀ ps' M hwf h
          refine ⟨valid_iteHullD_else hVe
            (fun ρ hρ => evalIParams_mem hρ c ps ps₀ C hc) hnn, hy, hw⟩
        · rw [if_neg hnn] at h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨⟨Mt, ps₁⟩, ht, h⟩ := h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨Me, ps₂⟩, he, hfinal⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
          obtain ⟨hVt, _, _⟩ := iht ps₀ ps₁ Mt hwf ht
          obtain ⟨hVe, _, _⟩ := ihe ps₁ ps₂ Me hwf he
          exact ⟨valid_iteHull c hVt hVe (cellOK_of_wf hwf), rfl, rfl⟩

/-! ### Schema-v3 smoke tests: decided guard = single branch, no hull -/

/-- Box `[1/2, 1]`: the guard `x` of `exIteAbs` is nonnegative throughout. -/
def exBoxIteD : Fin 1 → DInterval := fun _ => ⟨⟨1, -1⟩, ⟨1, 0⟩⟩

theorem exBoxIteD_wf : ∀ i, (exBoxIteD i).wf = true := fun i => by
  fin_cases i; decide

/-- On the guard-decided box the D evaluator returns the else-branch model
verbatim — no hull composite, no certificate consumption. -/
theorem exIteD_single_branch :
    evalTMHullD exBoxIteD exIteAbs TMParams.empty
      = some (varTM exBoxIteD 0, TMParams.empty) := rfl

/-- The produced single-branch model is valid for pointwise `|x|`. -/
theorem exIteD_valid (ps ps' : TMParams) (M : TaylorM 1)
    (hE : evalTMHullD exBoxIteD exIteAbs ps = some (M, ps')) :
    M.Valid exBoxIteD (fun ρ => if ρ 0 < 0 then -ρ 0 else ρ 0) :=
  (evalTMHullD_sound exIteAbs ps ps' M exBoxIteD_wf hE).1

/-- Contrast: the M2 hull evaluator on the same box always pays both
branches and returns the constant hull composite. -/
theorem exIteD_hull_composite :
    evalTMHull exBoxIteD exIteAbs TMParams.empty
      = some (iteHullTM exBoxIteD (varTM exBoxIteD 0).neg (varTM exBoxIteD 0),
        TMParams.empty) := rfl

/-- A guard whose own interval evaluation fails (divisor `[-1,1]` meets 0)
fails the D node — C-side `TM_FAIL(1)` semantics — where the M2 hull
evaluator (guard never evaluated) still succeeds. -/
theorem exIteBadGuard_hullD_none :
    evalTMHullD exBoxIteHull exIteBadGuard TMParams.empty = none := rfl

#print axioms TaylorM.Valid.congr_box
#print axioms evalIParams_mem
#print axioms valid_iteHullD
#print axioms valid_iteHullD_else
#print axioms evalTMHullD_sound
#print axioms exIteD_single_branch
#print axioms exIteD_valid
#print axioms exIteD_hull_composite
#print axioms exIteBadGuard_hullD_none

/-! ## Schema v3, second cut: the df-hull ite composite (`iteHullTM2` /
`evalTMHullD2`)

Root cause ① of the 20-leaf NEG pilot: the M2 straddle composite is the
*constant* hull (`iteHullTM`), paying the full hull width `H` as `err` and
destroying the branch slopes.  On the 549 lane the two branches join C¹ at
the guard surface, so `|Δf0|` is small and a df-hull composite tightens
`err` by an order of magnitude (C-side counterpart: `bb_arb.c --ite-hull2`).

The Lean synthesis is re-derived for the ∃-slope `TaylorM.Valid` semantics,
whose anchor is the **true center value** `f(y)` (not a stored constant):
the composite keeps

- `y`, `w`: the (shared) branch center/envelope;
- `fB := (Mt.valueRange).hull Me.valueRange` — both branch center values are
  in their branch `fB ⊆ valueRange ⊆ hull`;
- `dfB i := (Mt.dfB i).hull (Me.dfB i)` — at a box point the selected
  branch's witnessed slopes lie in the component hull, so the ∃-slope clause
  transports verbatim;
- `err := max err_t err_e + jumpBound Mt.fB Me.fB` where `jumpBound` is the
  interval distance `max(|fB_t.lo − fB_e.hi|, |fB_t.hi − fB_e.lo|)`.  The
  jump term is REQUIRED by the true-value anchor: when the guard selects
  different branches at `ρ` and at the center `y`, the composite residual
  splits into the selected branch's own remainder (≤ `err_b`, witnessed by
  that branch's own slope — no hull-width term) plus the center jump
  `|ft(y) − fe(y)| ≤ jumpBound` (each branch center value lies in its `fB`).
  No continuity hypothesis is used — the jump is absorbed through the two
  δ = 0 value bounds, so the composite is sound for ANY guard behavior.
  (The C side anchors at stored constants `f0_b`, so its jump chain is
  `err_t + err_e + |f0_t − f0_e|`; the Lean `fB` enclosures give the jump
  directly, strictly tighter.)

Compared with the constant composite this replaces the full hull width
`H ≈ W_t + W_e + |Δf0|` by `≈ |Δf0| + max(err_t, err_e)` — the C¹ regime's
order-of-magnitude `err` cut.  The guard-decided single-branch arms of
`evalTMHullD` are inherited verbatim (`evalTMHullD2` differs from
`evalTMHullD` only in the straddle arm), so decided-guard leaves compute
identically; the old constructions stay referable. -/

/-- The distance between two intervals: `max(|I.lo − J.hi|, |I.hi − J.lo|)`
— the largest `|x − x'|` over `x ∈ I`, `x' ∈ J`, attained at opposite
endpoints (0 when the intervals overlap). -/
def DInterval.jumpBound (I J : DInterval) : Dyadic :=
  Dyadic.dmax
    (Dyadic.dmax (I.lo.add (-J.hi)) (J.hi.add (-I.lo)))
    (Dyadic.dmax (I.hi.add (-J.lo)) (J.lo.add (-I.hi)))

/-- `jumpBound` unfolds to the endpoint distance formula. -/
theorem DInterval.jumpBound_toReal (I J : DInterval) :
    (I.jumpBound J).toReal
      = max (max (I.lo.toReal - J.hi.toReal) (J.hi.toReal - I.lo.toReal))
          (max (I.hi.toReal - J.lo.toReal) (J.lo.toReal - I.hi.toReal)) := by
  show Dyadic.toReal (Dyadic.dmax
      (Dyadic.dmax (I.lo.add (-J.hi)) (J.hi.add (-I.lo)))
      (Dyadic.dmax (I.hi.add (-J.lo)) (J.lo.add (-I.hi)))) = _
  simp only [Dyadic.toReal_dmax, Dyadic.toReal_add, Dyadic.toReal_neg,
    sub_eq_add_neg]

/-- **Distance bound**: `jumpBound I J` dominates `|x − x'|` for `x ∈ I`,
`x' ∈ J`. -/
theorem DInterval.jumpBound_ge {I J : DInterval} {x x' : ℝ}
    (hx : I.mem x) (hx' : J.mem x') : |x - x'| ≤ (I.jumpBound J).toReal := by
  rw [DInterval.jumpBound_toReal, abs_le]
  constructor
  · have hA := le_max_right (I.lo.toReal - J.hi.toReal) (J.hi.toReal - I.lo.toReal)
    have hB := le_max_left
      (max (I.lo.toReal - J.hi.toReal) (J.hi.toReal - I.lo.toReal))
      (max (I.hi.toReal - J.lo.toReal) (J.lo.toReal - I.hi.toReal))
    linarith [hx.1, hx'.2, hA, hB]
  · have hC := le_max_left (I.hi.toReal - J.lo.toReal) (J.lo.toReal - I.hi.toReal)
    have hD := le_max_right
      (max (I.lo.toReal - J.hi.toReal) (J.hi.toReal - I.lo.toReal))
      (max (I.hi.toReal - J.lo.toReal) (J.lo.toReal - I.hi.toReal))
    linarith [hx.2, hx'.1, hC, hD]

/-- `jumpBound` is nonnegative (it dominates an absolute value). -/
theorem DInterval.jumpBound_nonneg (I J : DInterval) :
    0 ≤ (I.jumpBound J).toReal := by
  rw [DInterval.jumpBound_toReal]
  have h1 := le_max_left (I.lo.toReal - J.hi.toReal) (J.hi.toReal - I.lo.toReal)
  have h2 := le_max_right (I.lo.toReal - J.hi.toReal) (J.hi.toReal - I.lo.toReal)
  have h3 := le_max_left
    (max (I.lo.toReal - J.hi.toReal) (J.hi.toReal - I.lo.toReal))
    (max (I.hi.toReal - J.lo.toReal) (J.lo.toReal - I.hi.toReal))
  linarith

/-- Schema-v3 second cut: the df-hull ite composite (see the section
header). -/
def iteHullTM2 {n : ℕ} (Mt Me : TaylorM n) : TaylorM n :=
  ⟨Mt.y, Mt.w, (Mt.valueRange).hull Me.valueRange,
    fun i => (Mt.dfB i).hull (Me.dfB i),
    Dyadic.dmax ((Dyadic.dmax Mt.err Me.err).add
      (Mt.fB.jumpBound Me.fB)) ⟨0, 0⟩⟩

/-- **Validity of the df-hull composite**: if both branch models are valid
on the box (same center, same envelope), the composite is valid for the
guard-selected function `ρ ↦ if c(ρ) < 0 then ft ρ else fe ρ`.  Per box
point the witnessed slope is the selected branch's own (∈ the component
hull); the residual splits into that branch's remainder plus — only when
the guard selects the other branch at the center — the center jump
`|ft(y) − fe(y)| ≤ jumpBound Mt.fB Me.fB`.  No guard or continuity
hypothesis. -/
theorem valid_iteHull2 {n : ℕ} {Mt Me : TaylorM n} {box : Fin n → DInterval}
    {ft fe : (Fin n → ℝ) → ℝ} (c : IExpr n)
    (ht : Mt.Valid box ft) (he : Me.Valid box fe)
    (hy : Mt.y = Me.y) (_hw : Mt.w = Me.w) :
    (iteHullTM2 Mt Me).Valid box
      (fun ρ => if c.evalReal ρ < 0 then ft ρ else fe ρ) := by
  obtain ⟨htmem, htw, htfB, htrem⟩ := ht
  obtain ⟨_, _, hefB, herem⟩ := he
  rw [← hy] at hefB herem
  have hvr : ∀ (M : TaylorM n) (x : ℝ), M.fB.mem x → M.valueRange.mem x := by
    intro M x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hW : 0 ≤ M.W.toReal := TaylorM.W_nonneg M
    constructor
    · show Dyadic.toReal (M.fB.lo.add (-M.W)) ≤ x
      rw [Dyadic.toReal_add, Dyadic.toReal_neg]
      linarith
    · show x ≤ Dyadic.toReal (M.fB.hi.add M.W)
      rw [Dyadic.toReal_add]
      linarith
  have hjump : |ft (fun i => (Mt.y i).toReal) - fe (fun i => (Mt.y i).toReal)|
      ≤ (Mt.fB.jumpBound Me.fB).toReal := DInterval.jumpBound_ge htfB hefB
  have hjump' : |fe (fun i => (Mt.y i).toReal) - ft (fun i => (Mt.y i).toReal)|
      ≤ (Mt.fB.jumpBound Me.fB).toReal := by
    rw [abs_sub_comm]
    exact hjump
  have hJ0 : 0 ≤ (Mt.fB.jumpBound Me.fB).toReal := DInterval.jumpBound_nonneg _ _
  have herr : (iteHullTM2 Mt Me).err.toReal
      = max (max Mt.err.toReal Me.err.toReal + (Mt.fB.jumpBound Me.fB).toReal) 0 := by
    show Dyadic.toReal (Dyadic.dmax
      ((Dyadic.dmax Mt.err Me.err).add (Mt.fB.jumpBound Me.fB)) ⟨0, 0⟩) = _
    rw [Dyadic.toReal_dmax, Dyadic.toReal_add, Dyadic.toReal_dmax, Dyadic.toReal_zero]
  have hm1 : Mt.err.toReal ≤ max Mt.err.toReal Me.err.toReal := le_max_left _ _
  have hm2 : Me.err.toReal ≤ max Mt.err.toReal Me.err.toReal := le_max_right _ _
  have hm3 : max Mt.err.toReal Me.err.toReal + (Mt.fB.jumpBound Me.fB).toReal
      ≤ max (max Mt.err.toReal Me.err.toReal + (Mt.fB.jumpBound Me.fB).toReal) 0 :=
    le_max_left _ _
  refine ⟨htmem, htw, ?_, ?_⟩
  · show ((Mt.valueRange).hull Me.valueRange).mem
      (if c.evalReal (fun i => (Mt.y i).toReal) < 0
        then ft (fun i => (Mt.y i).toReal)
        else fe (fun i => (Mt.y i).toReal))
    by_cases hlt : c.evalReal (fun i => (Mt.y i).toReal) < 0
    · rw [if_pos hlt]
      exact DInterval.mem_hull_left (hvr Mt _ htfB)
    · rw [if_neg hlt]
      exact DInterval.mem_hull_right (hvr Me _ hefB)
  · intro ρ hρ
    dsimp only
    rw [show (iteHullTM2 Mt Me).y = Mt.y from rfl]
    by_cases hlt : c.evalReal ρ < 0
    · rw [if_pos hlt]
      obtain ⟨a, ha, hb⟩ := htrem ρ hρ
      refine ⟨a, fun i => DInterval.mem_hull_left (ha i), ?_⟩
      by_cases hcy : c.evalReal (fun i => (Mt.y i).toReal) < 0
      · rw [if_pos hcy]
        rw [herr]
        linarith
      · rw [if_neg hcy]
        have hsplit : ft ρ - fe (fun i => (Mt.y i).toReal)
            - ∑ i, a i * (ρ i - (Mt.y i).toReal)
            = (ft ρ - ft (fun i => (Mt.y i).toReal)
                - ∑ i, a i * (ρ i - (Mt.y i).toReal))
              + (ft (fun i => (Mt.y i).toReal)
                - fe (fun i => (Mt.y i).toReal)) := by ring
        rw [hsplit, herr]
        refine le_trans (abs_add_le _ _) ?_
        linarith
    · rw [if_neg hlt]
      obtain ⟨b, hb, hbe⟩ := herem ρ hρ
      refine ⟨b, fun i => DInterval.mem_hull_right (hb i), ?_⟩
      by_cases hcy : c.evalReal (fun i => (Mt.y i).toReal) < 0
      · rw [if_pos hcy]
        have hsplit : fe ρ - ft (fun i => (Mt.y i).toReal)
            - ∑ i, b i * (ρ i - (Mt.y i).toReal)
            = (fe ρ - fe (fun i => (Mt.y i).toReal)
                - ∑ i, b i * (ρ i - (Mt.y i).toReal))
              + (fe (fun i => (Mt.y i).toReal)
                - ft (fun i => (Mt.y i).toReal)) := by ring
        rw [hsplit, herr]
        refine le_trans (abs_add_le _ _) ?_
        linarith
      · rw [if_neg hcy]
        rw [herr]
        linarith

/-- Schema-v3 second cut: the df-hull evaluator.  Identical to
`evalTMHullD` except that the guard-straddle `ite` arm composes the two
branch models into the df-hull composite (`iteHullTM2`) instead of the
constant hull; the guard-decided single-branch arms are verbatim shared, so
decided-guard leaves compute identically. -/
def evalTMHullD2 {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (TaylorM n × TMParams)
  | .const d, ps => some (constTM box d, ps)
  | .var k, ps => some (varTM box k, ps)
  | .neg e, ps => (evalTMHullD2 box e ps).map fun (M, ps') => (M.neg, ps')
  | .add e₁ e₂, ps =>
      (evalTMHullD2 box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2 box e₂ ps₁).map fun (M₂, ps₂) => (M₁.add M₂, ps₂)
  | .sub e₁ e₂, ps =>
      (evalTMHullD2 box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2 box e₂ ps₁).map fun (M₂, ps₂) => (M₁.sub M₂, ps₂)
  | .mul e₁ e₂, ps =>
      (evalTMHullD2 box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2 box e₂ ps₁).map fun (M₂, ps₂) => (M₁.mul M₂, ps₂)
  | .div e₁ e₂ out, ps =>
      (evalTMHullD2 box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2 box e₂ ps₁).bind fun (M₂, ps₂) =>
      ps₂.invCerts.head?.bind fun p =>
      ((M₂.inv p).map fun Mi => (M₁.mul Mi, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail,
          ps₂.transCerts⟩)).orElse
        (fun _ => ((IExpr.div e₁ e₂ out).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩))
  | .sqrt e s₁ s₂, ps =>
      (evalTMHullD2 box e ps).bind fun (M₀, ps₀) =>
      ps₀.sqrtCerts.head?.bind fun p =>
      ((M₀.sqrt p).map fun M' => (M', ⟨ps₀.sqrtCerts.tail, ps₀.invCerts,
          ps₀.transCerts⟩)).orElse
        (fun _ => ((IExpr.sqrt e s₁ s₂).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩))
  | .abs e, ps => ((IExpr.abs e).eval box).map fun I => (fallbackTM box I, ps)
  | .trans k e N out, ps =>
      if e.isClosed then
        ((IExpr.trans k e N out).eval box).map fun I => (closedTM box I, ps)
      else
        (evalTMHullD2 box e ps).bind fun (M₀, ps₀) =>
        ps₀.transCerts.head?.bind fun p =>
        ((M₀.trans k N out p).map fun M' =>
            (M', ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩)).orElse
          (fun _ => ((IExpr.trans k e N out).eval box).map fun I =>
            (fallbackTM box I, ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩))
  | .ite c t e, ps =>
      (evalIParams box c ps).bind fun (C, ps₀) =>
      if C.hi.isNeg then evalTMHullD2 box t ps₀
      else if C.lo.isNN then evalTMHullD2 box e ps₀
      else
        (evalTMHullD2 box t ps₀).bind fun (Mt, ps₁) =>
        (evalTMHullD2 box e ps₁).map fun (Me, ps₂) => (iteHullTM2 Mt Me, ps₂)

/-- **Soundness of `evalTMHullD2`** (same conclusion as `evalTMHullD_sound`):
the non-`ite` cases repeat `evalTMHullD_sound`'s arguments over the
self-recursion, and the `ite` case adds the certified-guard branch selection
(`valid_iteHullD`/`valid_iteHullD_else`) or the df-hull straddle composite
(`valid_iteHull2`, with the shared center/envelope discharged from the
induction hypotheses). -/
theorem evalTMHullD2_sound {n : ℕ} {box : Fin n → DInterval} :
    ∀ (e : IExpr n) (ps ps' : TMParams) (M : TaylorM n),
      (∀ i, (box i).wf = true) →
      evalTMHullD2 box e ps = some (M, ps') →
      M.Valid box (fun ρ => e.evalReal ρ) ∧ M.y = boxCenter box ∧ M.w = boxW box := by
  intro e
  induction e with
  | const d =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨valid_const (cellOK_of_wf hwf) d, rfl, rfl⟩
  | var k =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨valid_var (cellOK_of_wf hwf) k, rfl, rfl⟩
  | neg e ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₀, ps₀⟩, he, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
      exact ⟨valid_neg hV, hy, hw⟩
  | add e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_add hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | sub e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_sub hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | mul e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_mul hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | div e₁ e₂ out ih₁ ih₂ =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      obtain ⟨hV₁, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ hwf h₂
      cases hi : M₂.inv p with
      | none =>
        rw [hi] at h
        rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
      | some Mi =>
        rw [hi] at h
        rw [Option.map_some, Option.orElse_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
        refine ⟨?_, hy₁, hw₁⟩
        exact valid_div hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂]) p hi
  | sqrt e s₁ s₂ ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₀, ps₀⟩, he, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
      cases hs : M₀.sqrt p with
      | none =>
        rw [hs] at h
        rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
      | some M' =>
        rw [hs] at h
        rw [Option.map_some, Option.orElse_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
        obtain ⟨hV', hyy, hww⟩ := valid_sqrt hV p hs
        refine ⟨hV', ?_, ?_⟩
        · show M'.y = boxCenter box
          exact hyy.trans hy
        · show M'.w = boxW box
          exact hww.trans hw
  | abs e ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨I, hI, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
  | trans k e N out ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      by_cases hcl : e.isClosed = true
      · rw [if_pos hcl] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        exact ⟨valid_closed (cellOK_of_wf hwf) hcl hI, rfl, rfl⟩
      · rw [if_neg hcl] at h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨⟨M₀, ps₀⟩, he, h⟩ := h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨p, _hp, h⟩ := h
        obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
        cases ht : M₀.trans k N out p with
        | none =>
          rw [ht] at h
          rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
          obtain ⟨I, hI, hfinal⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
          exact ⟨valid_fallback (cellOK_of_wf hwf) hI, rfl, rfl⟩
        | some M' =>
          rw [ht] at h
          rw [Option.map_some, Option.orElse_some] at h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
          obtain ⟨hV', hyy, hww⟩ := valid_trans hV N out p ht
          refine ⟨hV', ?_, ?_⟩
          · show M'.y = boxCenter box
            exact hyy.trans hy
          · show M'.w = boxW box
            exact hww.trans hw
  | ite c t e _ihc iht ihe =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨C, ps₀⟩, hc, h⟩ := h
      by_cases hneg : C.hi.isNeg = true
      · rw [if_pos hneg] at h
        obtain ⟨hVt, hyt, hwt⟩ := iht ps₀ ps' M hwf h
        refine ⟨valid_iteHullD hVt (fun ρ hρ => evalIParams_mem hρ c ps ps₀ C hc)
          hneg, hyt, hwt⟩
      · rw [if_neg hneg] at h
        by_cases hnn : C.lo.isNN = true
        · rw [if_pos hnn] at h
          obtain ⟨hVe, hye, hwe⟩ := ihe ps₀ ps' M hwf h
          refine ⟨valid_iteHullD_else hVe
            (fun ρ hρ => evalIParams_mem hρ c ps ps₀ C hc) hnn, hye, hwe⟩
        · rw [if_neg hnn] at h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨⟨Mt, ps₁⟩, ht, h⟩ := h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨Me, ps₂⟩, he, hfinal⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
          obtain ⟨hVt, hyt, hwt⟩ := iht ps₀ ps₁ Mt hwf ht
          obtain ⟨hVe, hye, hwe⟩ := ihe ps₁ ps₂ Me hwf he
          refine ⟨valid_iteHull2 c hVt hVe (hyt.trans hye.symm)
            (hwt.trans hwe.symm), hyt, hwt⟩

/-! ### Schema-v3 second-cut smoke tests: df-hull composite -/

/-- On the guard-straddling toy box the D2 evaluator returns the df-hull
composite of the two branch models. -/
theorem exIteHull2_straddle_composite :
    evalTMHullD2 exBoxIteHull exIteAbs TMParams.empty
      = some (iteHullTM2 (varTM exBoxIteHull 0).neg (varTM exBoxIteHull 0),
        TMParams.empty) := rfl

/-- The df-hull composite's err on the toy: `max(0,0) + jump([0,0],[0,0])
= 0` — vs the constant composite's full hull width `2`. -/
theorem exIteHull2_err_zero :
    (iteHullTM2 (varTM exBoxIteHull 0).neg (varTM exBoxIteHull 0)).err
      = ⟨0, 0⟩ := rfl

/-- The df-hull err dominates nothing extra but is strictly below the
constant composite's hull width. -/
theorem exIteHull2_err_tighter :
    Dyadic.ble (iteHullTM2 (varTM exBoxIteHull 0).neg (varTM exBoxIteHull 0)).err
      (iteHullTM exBoxIteHull (varTM exBoxIteHull 0).neg
        (varTM exBoxIteHull 0)).err = true := by
  decide

/-- The produced df-hull composite is valid for pointwise `|x|`. -/
theorem exIteHull2_valid (ps ps' : TMParams) (M : TaylorM 1)
    (hE : evalTMHullD2 exBoxIteHull exIteAbs ps = some (M, ps')) :
    M.Valid exBoxIteHull (fun ρ => if ρ 0 < 0 then -ρ 0 else ρ 0) :=
  (evalTMHullD2_sound exIteAbs ps ps' M exBoxIteHull_wf hE).1

/-- Decided-guard behavior is inherited verbatim (same single-branch arms,
definitional). -/
theorem exIteD2_single_branch :
    evalTMHullD2 exBoxIteD exIteAbs TMParams.empty
      = some (varTM exBoxIteD 0, TMParams.empty) := rfl

/-- A failing guard still fails the D2 node (C-side `TM_FAIL(1)`). -/
theorem exIteBadGuard_hullD2_none :
    evalTMHullD2 exBoxIteHull exIteBadGuard TMParams.empty = none := rfl

#print axioms DInterval.jumpBound_ge
#print axioms DInterval.jumpBound_nonneg
#print axioms valid_iteHull2
#print axioms evalTMHullD2_sound
#print axioms exIteHull2_straddle_composite
#print axioms exIteHull2_err_zero
#print axioms exIteHull2_err_tighter
#print axioms exIteHull2_valid
#print axioms exIteD2_single_branch
#print axioms exIteBadGuard_hullD2_none

/-! ## The checker -/

/-- **Soundness of the Taylor lower bound**: `loBound` lower-bounds `f` at
every point of the box. -/
theorem TaylorM.loBound_sound {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f)
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) :
    (M.loBound box).toReal ≤ f ρ := by
  obtain ⟨_, _, hfB, hrem⟩ := hV
  obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
  have hU : ∀ i, (⟨(box i).lo.add (-(M.y i)), (box i).hi.add (-(M.y i))⟩ : DInterval).mem
      (ρ i - (M.y i).toReal) := by
    intro i
    constructor
    · rw [Dyadic.toReal_add, Dyadic.toReal_neg]
      have h1 := (hρ i).1
      linarith
    · rw [Dyadic.toReal_add, Dyadic.toReal_neg]
      have h2 := (hρ i).2
      linarith
  have hterm : ∀ i, (((M.dfB i).mul
        ⟨(box i).lo.add (-(M.y i)), (box i).hi.add (-(M.y i))⟩).lo).toReal
      ≤ a i * (ρ i - (M.y i).toReal) :=
    fun i => (DInterval.mem_mul (ha i) (hU i)).1
  have hlo : (M.loBound box).toReal
      = M.fB.lo.toReal + ∑ i, (((M.dfB i).mul
          ⟨(box i).lo.add (-(M.y i)), (box i).hi.add (-(M.y i))⟩).lo).toReal
        - M.err.toReal := by
    unfold TaylorM.loBound
    rw [Dyadic.toReal_add, Dyadic.toReal_neg, Dyadic.toReal_foldl_add, sum_finRange_map,
      sub_eq_add_neg]
  rw [hlo]
  have h2 := (abs_le.mp hbound).1
  have hsumle : ∑ i, (((M.dfB i).mul
        ⟨(box i).lo.add (-(M.y i)), (box i).hi.add (-(M.y i))⟩).lo).toReal
      ≤ ∑ i, a i * (ρ i - (M.y i).toReal) :=
    Finset.sum_le_sum fun i _ => hterm i
  have hfy := hfB.1
  linarith

/-- The Taylor-model positivity checker: box well-formedness, successful
model evaluation, and a strictly positive Taylor lower bound. -/
def checkPosTM {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (ps : TMParams) : Bool :=
  (List.finRange n).all (fun i => (box i).wf) &&
    (match evalTM box e ps with
    | some (M, _) => (M.loBound box).isPos
    | none => false)

/-- **Core checker theorem** (same shape as `checkPos_sound`): if `checkPosTM`
passes, the expression is strictly positive at every real assignment
pointwise inside the box. -/
theorem checkPosTM_sound {n : ℕ} {e : IExpr n} {box : Fin n → DInterval}
    {ps : TMParams}
    (h : checkPosTM e box ps = true) (ρ : Fin n → ℝ) (hρ : boxMem box ρ) :
    0 < e.evalReal ρ := by
  unfold checkPosTM at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hwfB, h⟩ := h
  have hwf : ∀ i, (box i).wf = true := fun i => hwfB i (List.mem_finRange i)
  cases hE : evalTM box e ps with
  | none => rw [hE] at h; simp at h
  | some Mp =>
    obtain ⟨M, ps'⟩ := Mp
    rw [hE] at h
    have hpos := Dyadic.toReal_pos_of_isPos h
    obtain ⟨hV, _, _⟩ := evalTM_sound e ps ps' M hwf hE
    exact lt_of_lt_of_le hpos (M.loBound_sound hV hρ)

/-- The hybrid checker (same shape as `checkPosTM`). -/
def checkPosTMH {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (ps : TMParams) : Bool :=
  (List.finRange n).all (fun i => (box i).wf) &&
    (match evalTMH box e ps with
    | some (M, _) => (M.loBound box).isPos
    | none => false)

/-- **Soundness of the hybrid checker**. -/
theorem checkPosTMH_sound {n : ℕ} {e : IExpr n} {box : Fin n → DInterval}
    {ps : TMParams}
    (h : checkPosTMH e box ps = true) (ρ : Fin n → ℝ) (hρ : boxMem box ρ) :
    0 < e.evalReal ρ := by
  unfold checkPosTMH at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hwfB, h⟩ := h
  have hwf : ∀ i, (box i).wf = true := fun i => hwfB i (List.mem_finRange i)
  cases hE : evalTMH box e ps with
  | none => rw [hE] at h; simp at h
  | some Mp =>
    obtain ⟨M, ps'⟩ := Mp
    rw [hE] at h
    have hpos := Dyadic.toReal_pos_of_isPos h
    obtain ⟨hV, _, _⟩ := evalTMH_sound e ps ps' M hwf hE
    exact lt_of_lt_of_le hpos (M.loBound_sound hV hρ)

/-! ## M2b/schema-v3: the hull positivity checker (549 driver entry)

Same shape as `checkPosTMHull`, but on the guard-decided hull evaluator —
since the second cut this is `evalTMHullD2`: `ite` nodes with a guard that
is *sign-definite* on the leaf box evaluate the selected branch only — no
hull synthesis, no width doubling, slopes kept — while a guard-straddling
leaf composes the two branch models into the df-hull composite (`iteHullTM2`
: slope hull / value-range hull / `err = max err_b + jump`), replacing the
M2 constant hull whose full-width `err` was the 20-leaf pilot's straddle
NEG cause.  Either way the guard decision comes from *certified* interval
evaluation over the same leaf box, so the checker stays sound whatever the
driver believed.  The 549 lane (`C5490182221`, `bb_arb --ite-hull(2)`,
leaves with `hit: "tm"`) closes through this single entry.  The old
constant-composite behavior stays referable via `evalTMHullD` +
`evalTMHullD_sound` (M2b first cut).

**Driver-entry switch guide** (549 驱动入口切换): emit leaf certificates as

```
theorem leafK : checkPosTMHull expr boxK psK = true := by decide
```

instead of the interval `checkPos`/`checkPosTM`/`checkPosTMH` forms.  `psK`
carries per-leaf `sqrtCerts` (mantissa triples produced by the compiled-run
tracing evaluator `evalTMHullFill2` below — the node-for-node mirror of
`evalTMHullD2` — plus fixed recip granularities)
and fixed `invCerts`/`transCerts` granularities; the `IExpr` keeps dummy
`(0, 0)` sqrt slots and the atan rungs `(N, out)` as usual.
Generated by `emit_lean.py --hull` (stage A driver → params → stage B
certificate). -/

/-- The hull checker (same shape as `checkPosTMH`): box well-formedness,
successful guard-decided df-hull-model evaluation, and a strictly positive
Taylor lower bound. -/
def checkPosTMHull {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (ps : TMParams) : Bool :=
  (List.finRange n).all (fun i => (box i).wf) &&
    (match evalTMHullD2 box e ps with
    | some (M, _) => (M.loBound box).isPos
    | none => false)

/-- **Soundness of the hull checker** (`evalTMHullD2_sound` + the Taylor
lower bound lemma, the same two-line composition as `checkPosTMH_sound`). -/
theorem checkPosTMHull_sound {n : ℕ} {e : IExpr n} {box : Fin n → DInterval}
    {ps : TMParams}
    (h : checkPosTMHull e box ps = true) (ρ : Fin n → ℝ) (hρ : boxMem box ρ) :
    0 < e.evalReal ρ := by
  unfold checkPosTMHull at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hwfB, h⟩ := h
  have hwf : ∀ i, (box i).wf = true := fun i => hwfB i (List.mem_finRange i)
  cases hE : evalTMHullD2 box e ps with
  | none => rw [hE] at h; simp at h
  | some Mp =>
    obtain ⟨M, ps'⟩ := Mp
    rw [hE] at h
    have hpos := Dyadic.toReal_pos_of_isPos h
    obtain ⟨hV, _, _⟩ := evalTMHullD2_sound e ps ps' M hwf hE
    exact lt_of_lt_of_le hpos (M.loBound_sound hV hρ)

/-! ## M2b certificate production: the tracing hull evaluator

Compiled-run tooling for the certificate generator only — no proof
obligations, no kernel role (the `Tools.FillParams.evalFill` counterpart for
the TM route).  `evalTMHullFill` mirrors `evalTMHullD` node for node — same
`div`/`sqrt`/`trans` TM rules with the same fallbacks, same guard-decided
single-branch selection at `ite` nodes (guard certified by the mirror
`evalIParamsFill` below), same constant hull composite at guard-straddling
`ite` nodes — except that at `.sqrt` nodes (branch TM and in-guard interval
alike) the `Dyadic.sqrtI` mantissas are *computed* from the sub-model or
sub-interval (`Dyadic.sqrtFloor`, exact) instead of being read from
`ps.sqrtCerts`; the recip granularities still come from the template
certificate.  `evalTMHullFill2` is the same mirror for `evalTMHullD2`
(df-hull straddle composite).  Hence a PASS of the probe below predicts the
kernel `checkPosTMHull` of the leaf whose `sqrtCerts` carry the reported
mantissas: with the mantissas baked in, both evaluators visit identical
sub-models and sub-intervals, and every composite is deterministic. -/

/-- Exact floor-root mantissa of a nonnegative dyadic (a local mirror of
`Tools.FillParams`'s `Dyadic.sqrtFloor` — CertTM does not import the Tools
layer): `⌊√(d.m · 2^(d.e % 2))⌋`, so `Dyadic.sqrtI d (sqrtMantissa d)`
passes its kernel check whenever `d.m ≥ 0`.  `0` for `d.m < 0` (`sqrtI`
fails there for every certificate, matching `TaylorM.sqrt`'s positivity
gate).  Compiled runs only (`Nat.sqrt` does not kernel-reduce). -/
def sqrtMantissa (d : Dyadic) : Int :=
  if 0 ≤ d.m then Int.ofNat (Nat.sqrt (d.m * 2 ^ (d.e % 2).toNat).toNat) else 0

/-- Compiled-run mirror of `evalIParams` for the certificate generator: the
same control flow and the same `ps` threading (one `SqrtTMP` consumed per
`sqrt` node, so the kernel's queue layout matches), except that the two root
mantissas are *computed* (`sqrtMantissa`, exact) instead of read from the
consumed `SqrtTMP`, and each computed pair is reported in the triple list in
traversal order (guard first at `ite` nodes).  With the reported pairs baked
into the kernel-side `sqrtCerts`, the kernel `evalIParams` reproduces the
identical intervals and branch decisions. -/
def evalIParamsFill {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (DInterval × TMParams × List (Int × Int × Int))
  | .const d, ps => some (⟨d, d⟩, ps, [])
  | .var k, ps => some (box k, ps, [])
  | .neg e, ps =>
      (evalIParamsFill box e ps).map fun (I, ps', l) => (I.neg, ps', l)
  | .abs e, ps =>
      (evalIParamsFill box e ps).map fun (I, ps', l) => (I.abs, ps', l)
  | .add e₁ e₂, ps =>
      (evalIParamsFill box e₁ ps).bind fun (I₁, ps₁, l₁) =>
      (evalIParamsFill box e₂ ps₁).map fun (I₂, ps₂, l₂) =>
        (I₁.add I₂, ps₂, l₁ ++ l₂)
  | .sub e₁ e₂, ps =>
      (evalIParamsFill box e₁ ps).bind fun (I₁, ps₁, l₁) =>
      (evalIParamsFill box e₂ ps₁).map fun (I₂, ps₂, l₂) =>
        (I₁.sub I₂, ps₂, l₁ ++ l₂)
  | .mul e₁ e₂, ps =>
      (evalIParamsFill box e₁ ps).bind fun (I₁, ps₁, l₁) =>
      (evalIParamsFill box e₂ ps₁).map fun (I₂, ps₂, l₂) =>
        (I₁.mul I₂, ps₂, l₁ ++ l₂)
  | .div e₁ e₂ out, ps =>
      (evalIParamsFill box e₁ ps).bind fun (I₁, ps₁, l₁) =>
      (evalIParamsFill box e₂ ps₁).bind fun (I₂, ps₂, l₂) =>
      (DInterval.div I₁ I₂ out).map fun I => (I, ps₂, l₁ ++ l₂)
  | .sqrt e _ _, ps =>
      (evalIParamsFill box e ps).bind fun (I, ps₀, l) =>
      ps₀.sqrtCerts.head?.bind fun _ =>
      let slo := sqrtMantissa I.lo
      let shi := sqrtMantissa I.hi
      (if I.hi.isNeg then none
        else
          (Dyadic.sqrtI I.hi shi).bind fun Jh =>
          ((if I.lo.isNN then (Dyadic.sqrtI I.lo slo).map (fun Jl => Jl.lo)
            else some (⟨0, 0⟩ : Dyadic))).map fun L =>
            (⟨L, Jh.hi⟩, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩,
              l ++ [(slo, shi, 0)]))
  | .trans k e N out, ps =>
      (evalIParamsFill box e ps).bind fun (I, ps₀, l) =>
      (transOn k I N out).map fun J => (J, ps₀, l)
  | .ite c t e, ps =>
      (evalIParamsFill box c ps).bind fun (C, ps₀, lg) =>
      if C.hi.isNeg then
        (evalIParamsFill box t ps₀).map fun (I, ps', l) => (I, ps', lg ++ l)
      else if C.lo.isNN then
        (evalIParamsFill box e ps₀).map fun (I, ps', l) => (I, ps', lg ++ l)
      else
        (evalIParamsFill box t ps₀).bind fun (T, ps₁, l₁) =>
        (evalIParamsFill box e ps₁).map fun (E, ps₂, l₂) =>
          (T.hull E, ps₂, lg ++ l₁ ++ l₂)

/-- Tracing mirror of `evalTMHullD` collecting the per-`sqrt`-node mantissa
triples `(slo, shi, sc)` in traversal order (guard before the selected
branch(es) at `ite` nodes, node after its argument). -/
def evalTMHullFill {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (TaylorM n × TMParams × List (Int × Int × Int))
  | .const d, ps => some (constTM box d, ps, [])
  | .var k, ps => some (varTM box k, ps, [])
  | .neg e, ps =>
      (evalTMHullFill box e ps).map fun (M, ps', l) => (M.neg, ps', l)
  | .add e₁ e₂, ps =>
      (evalTMHullFill box e₁ ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill box e₂ ps₁).map fun (M₂, ps₂, l₂) =>
        (M₁.add M₂, ps₂, l₁ ++ l₂)
  | .sub e₁ e₂, ps =>
      (evalTMHullFill box e₁ ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill box e₂ ps₁).map fun (M₂, ps₂, l₂) =>
        (M₁.sub M₂, ps₂, l₁ ++ l₂)
  | .mul e₁ e₂, ps =>
      (evalTMHullFill box e₁ ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill box e₂ ps₁).map fun (M₂, ps₂, l₂) =>
        (M₁.mul M₂, ps₂, l₁ ++ l₂)
  | .div e₁ e₂ out, ps =>
      (evalTMHullFill box e₁ ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill box e₂ ps₁).bind fun (M₂, ps₂, l₂) =>
      ps₂.invCerts.head?.bind fun p =>
      ((M₂.inv p).map fun Mi =>
          (M₁.mul Mi, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩,
            l₁ ++ l₂)).orElse
        (fun _ => ((IExpr.div e₁ e₂ out).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩,
            l₁ ++ l₂))
  | .sqrt e s₁ s₂, ps =>
      (evalTMHullFill box e ps).bind fun (M₀, ps₀, l) =>
      ps₀.sqrtCerts.head?.bind fun t =>
      ((if (M₀.fB.lo.add (-M₀.W)).isPos = true then
          let slo := sqrtMantissa M₀.fB.lo
          let shi := sqrtMantissa M₀.fB.hi
          let sc := sqrtMantissa (M₀.fB.lo.add (-M₀.W))
          (M₀.sqrt ⟨slo, shi, sc, t.o1, t.o2⟩).map fun M' =>
            (M', ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩,
              l ++ [(slo, shi, sc)])
        else none).orElse
        (fun _ => ((IExpr.sqrt e s₁ s₂).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩, l)))
  | .trans k e N out, ps =>
      if e.isClosed then
        ((IExpr.trans k e N out).eval box).map fun I => (closedTM box I, ps, [])
      else
        (evalTMHullFill box e ps).bind fun (M₀, ps₀, l) =>
        ps₀.transCerts.head?.bind fun p =>
        ((M₀.trans k N out p).map fun M' =>
            (M', ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩, l)).orElse
          (fun _ => ((IExpr.trans k e N out).eval box).map fun I =>
            (fallbackTM box I,
              ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩, l))
  | .abs e, ps =>
      ((IExpr.abs e).eval box).map fun I => (fallbackTM box I, ps, [])
  | .ite c t e, ps =>
      (evalIParamsFill box c ps).bind fun (C, ps₀, lg) =>
      if C.hi.isNeg then
        (evalTMHullFill box t ps₀).map fun (M, ps', l) => (M, ps', lg ++ l)
      else if C.lo.isNN then
        (evalTMHullFill box e ps₀).map fun (M, ps', l) => (M, ps', lg ++ l)
      else
        (evalTMHullFill box t ps₀).bind fun (Mt, ps₁, l₁) =>
        (evalTMHullFill box e ps₁).map fun (Me, ps₂, l₂) =>
          (iteHullTM box Mt Me, ps₂, lg ++ l₁ ++ l₂)

/-- Tracing mirror of `evalTMHullD2` (schema-v3 second cut): identical to
`evalTMHullFill` except that the guard-straddling `ite` arm composes the
df-hull composite (`iteHullTM2`), so the probe below predicts the kernel
`checkPosTMHull` (which runs `evalTMHullD2`) leaf for leaf — including the
df-hull `err` and the smaller `W` entering `sqrt`'s `sc` mantissa on
sub-models below a straddle composite. -/
def evalTMHullFill2 {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (TaylorM n × TMParams × List (Int × Int × Int))
  | .const d, ps => some (constTM box d, ps, [])
  | .var k, ps => some (varTM box k, ps, [])
  | .neg e, ps =>
      (evalTMHullFill2 box e ps).map fun (M, ps', l) => (M.neg, ps', l)
  | .add e₁ e₂, ps =>
      (evalTMHullFill2 box e₁ ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill2 box e₂ ps₁).map fun (M₂, ps₂, l₂) =>
        (M₁.add M₂, ps₂, l₁ ++ l₂)
  | .sub e₁ e₂, ps =>
      (evalTMHullFill2 box e₁ ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill2 box e₂ ps₁).map fun (M₂, ps₂, l₂) =>
        (M₁.sub M₂, ps₂, l₁ ++ l₂)
  | .mul e₁ e₂, ps =>
      (evalTMHullFill2 box e₁ ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill2 box e₂ ps₁).map fun (M₂, ps₂, l₂) =>
        (M₁.mul M₂, ps₂, l₁ ++ l₂)
  | .div e₁ e₂ out, ps =>
      (evalTMHullFill2 box e₁ ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill2 box e₂ ps₁).bind fun (M₂, ps₂, l₂) =>
      ps₂.invCerts.head?.bind fun p =>
      ((M₂.inv p).map fun Mi =>
          (M₁.mul Mi, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩,
            l₁ ++ l₂)).orElse
        (fun _ => ((IExpr.div e₁ e₂ out).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩,
            l₁ ++ l₂))
  | .sqrt e s₁ s₂, ps =>
      (evalTMHullFill2 box e ps).bind fun (M₀, ps₀, l) =>
      ps₀.sqrtCerts.head?.bind fun t =>
      ((if (M₀.fB.lo.add (-M₀.W)).isPos = true then
          let slo := sqrtMantissa M₀.fB.lo
          let shi := sqrtMantissa M₀.fB.hi
          let sc := sqrtMantissa (M₀.fB.lo.add (-M₀.W))
          (M₀.sqrt ⟨slo, shi, sc, t.o1, t.o2⟩).map fun M' =>
            (M', ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩,
              l ++ [(slo, shi, sc)])
        else none).orElse
        (fun _ => ((IExpr.sqrt e s₁ s₂).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩, l)))
  | .trans k e N out, ps =>
      if e.isClosed then
        ((IExpr.trans k e N out).eval box).map fun I => (closedTM box I, ps, [])
      else
        (evalTMHullFill2 box e ps).bind fun (M₀, ps₀, l) =>
        ps₀.transCerts.head?.bind fun p =>
        ((M₀.trans k N out p).map fun M' =>
            (M', ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩, l)).orElse
          (fun _ => ((IExpr.trans k e N out).eval box).map fun I =>
            (fallbackTM box I,
              ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩, l))
  | .abs e, ps =>
      ((IExpr.abs e).eval box).map fun I => (fallbackTM box I, ps, [])
  | .ite c t e, ps =>
      (evalIParamsFill box c ps).bind fun (C, ps₀, lg) =>
      if C.hi.isNeg then
        (evalTMHullFill2 box t ps₀).map fun (M, ps', l) => (M, ps', lg ++ l)
      else if C.lo.isNN then
        (evalTMHullFill2 box e ps₀).map fun (M, ps', l) => (M, ps', lg ++ l)
      else
        (evalTMHullFill2 box t ps₀).bind fun (Mt, ps₁, l₁) =>
        (evalTMHullFill2 box e ps₁).map fun (Me, ps₂, l₂) =>
          (iteHullTM2 Mt Me, ps₂, lg ++ l₁ ++ l₂)

/-- One compiled-run leaf probe: PASS flag, the Taylor lower bound
(mantissa, exponent) for margin diagnostics, and the mantissa triples to
bake into the kernel-side `TMParams.sqrtCerts`.  Runs the `evalTMHullD2`
mirror, so the prediction matches the kernel `checkPosTMHull` (df-hull
straddle composite included). -/
def tmHullLeafProbe {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (ps : TMParams) : Option (Bool × Int × Int × List (Int × Int × Int)) :=
  (evalTMHullFill2 box e ps).map fun (M, _, l) =>
    let lb := M.loBound box
    (lb.isPos, lb.m, lb.e, l)

/-! ### M2b smoke test: a guard-straddling leaf closed by the hull checker -/

/-- Box `[2, 5/2]`. -/
def exBoxHullChk : Fin 1 → DInterval := fun _ => ⟨⟨2, 0⟩, ⟨5, -1⟩⟩

/-- `ite (x − 9/4, 2x, x+2)`: the guard interval `[-1/4, 1/4]` straddles 0,
so the strict `evalTM` returns `none` on the node, while both branch models
evaluate — the 549 leaf shape (algebraic branches, straddling guard) in
miniature. -/
def exIteHullChk : IExpr 1 :=
  .ite (.sub (.var 0) (.const ⟨9, -2⟩)) (.mul (.var 0) (.const ⟨2, 0⟩))
    (.add (.var 0) (.const ⟨2, 0⟩))

theorem exBoxHullChk_wf : ∀ i, (exBoxHullChk i).wf = true := fun i => by
  fin_cases i; decide

/-- The hull checker closes the straddling leaf (kernel `decide`) — under
the df-hull checker switch the composite is `iteHullTM2`, with strictly
smaller err than the M2 constant hull. -/
theorem exIteHullChk_checkPos :
    checkPosTMHull exIteHullChk exBoxHullChk TMParams.empty = true := by
  decide

/-- The D2 straddle composite is the df-hull of the two branch models
(algebraic-branch leaf shape in miniature). -/
theorem exIteHullChk_D2_composite :
    evalTMHullD2 exBoxHullChk exIteHullChk TMParams.empty
      = some (iteHullTM2 ((varTM exBoxHullChk 0).mul (constTM exBoxHullChk ⟨2, 0⟩))
          ((varTM exBoxHullChk 0).add (constTM exBoxHullChk ⟨2, 0⟩)),
        TMParams.empty) := rfl

/-- The df-hull err is strictly below the constant composite's hull width. -/
theorem exIteHullChk_err_tighter :
    Dyadic.ble (iteHullTM2 ((varTM exBoxHullChk 0).mul (constTM exBoxHullChk ⟨2, 0⟩))
        ((varTM exBoxHullChk 0).add (constTM exBoxHullChk ⟨2, 0⟩))).err
      (iteHullTM exBoxHullChk
        ((varTM exBoxHullChk 0).mul (constTM exBoxHullChk ⟨2, 0⟩))
        ((varTM exBoxHullChk 0).add (constTM exBoxHullChk ⟨2, 0⟩))).err = true := by
  decide

#print axioms checkPosTMHull_sound
#print axioms exIteHullChk_checkPos
#print axioms exIteHullChk_D2_composite
#print axioms exIteHullChk_err_tighter

/-! ## 549 加速 M5: AST 去重最小可行版 — 证书表 let 节点（`LExpr`）

剖面结论（docs/549-lane-log.md, native_decide 轮）：`C549Hull200Expr` 2,726
节点、文本重复率 574% —— 判别式多项式 ~6 份副本、`4x₀²·Δ` 根号被开方式
4 份、unit6 多项式 ~10 份；decide 21.4 s/叶 ∝ 求值体积，去重预期 3-5×。

### 设计选择（二选一的裁决）

任务书给的方案 A 是 `IExpr` 新构造子 `letD (e : IExpr n) (body : IExpr
(n+1))`（de Bruijn 换元）；方案 B 是"证书表 + 指向既有节点编号的引用"。
**取 B**，理由（爆炸半径）：

1. `IExpr` 定义在 `Expr.lean`——加构造子要动 `Expr.lean`，且 `IExpr.eval`
   /`evalReal`/`isClosed`/`eval_mem`/`evalReal_const_of_isClosed` 全部要补
   `letD` 分支（TKind 路径 `Trans.lean` 亦然），11 个既有求值器/谓词 +
   CertTM 的 6 个求值器全要动；
2. 方案 B 全部新增物 living 在本文件的一个新归纳类型 `LExpr` 里，
   **`evalTM`/`evalTMH`/`evalTMHull`/`evalTMHullD`/`evalTMHullD2`/
   `evalIParams` 及其 soundness 一行不动**——旧求值器连 `| .letD .. =>
   none` 补丁都不需要（没有新构造子可漏匹配），这是比任务书设想的
   fallback 补丁更小的处置面。

### `LExpr` 形状与语义

`LExpr n k` = 长度 `k` 的证书表 `tbl : Fin k → IExpr n` 加一个体节点：

- `.plain f`：无引用的普通子树（整体委托既有 `evalTMHullD2`，包括其
  内部 ite guard 定号/hull 机制——发射端只在含引用的路径上镜像）；
- `.ref i`：第 `i` 号表项（点wise 语义 = `(tbl i).evalReal ρ`，即
  body[ref i := tbl i] 的代入语义——任务书 letD 语义的表形式）；
- `neg/add/sub/mul/div/sqrt/trans/abs`：与 `IExpr` 同构的组合子，子可含
  引用；fallback/closed 臂经 `toIExpr`（引用代入 = 展开为普通树）复用
  既有 `valid_fallback`/`valid_closed`；
- `.ite c t e`：guard 保持普通 `IExpr n`（引用不入 guard——guard 走
  `evalIParams` 区间路径，其证书消耗次序与原树一致），分支为 `LExpr`，
  guard 定号单支/df-hull 合成与 `evalTMHullD2` 逐分支相同。

### 求值与证书次序

`evalTMHullD2L box tbl e ps` = 先 `evalLTable`（表项按下标 0..k-1 各求值
一次成模型，`.ref` 直接注入该模型——去重的本体），再 `evalTMHullD2B` 走
体节点。**发射端约定（MVP）**：只折叠不含 sqrt/div/trans/ite/abs 的
（证书免费）子树 ⇒ 表项消耗零证书，ps 队列次序与未折叠原树逐位相同
（既有叶证书 P 直接复用）；含证书子树的折叠需用 `evalTMHullFill2L`
（Fill 镜像，表项先、体后、ite guard 先）重产 params——emit 侧接入
清单见 `emit_hull_pilot.py stageb-let`。

### Soundness

`evalLTable_sound`：表项模型 = `evalTMHullD2_sound` 逐项（Valid +
y = boxCenter + w = boxW）。`evalTMHullD2B_sound`：对体结构归纳，
组合子各支逐字复用 `evalTMHullD2_sound` 对应支（ref 支 = 表项合法性
假设；fallback/closed 支经 `Valid.congr_box` + `evalReal_toIExpr`）；
ite 支 = `evalIParams_mem` + `valid_iteHullD_fn`/`_else_fn`（分支函数
自由版，本节新增）/`valid_iteHull2`。合成
`evalTMHullD2L_sound` ⇒ `checkPosTMHullL_sound`：与 `checkPosTMHull`
同构的两行（loBound 下界）。公理面：标准三公理。
-/

/-- Shared-subexpression certificate table: a sharing layer over `IExpr`
whose references resolve to a `Fin k → IExpr n` table evaluated once into
models (see the section header). -/
inductive LExpr (n k : ℕ) : Type where
  | plain (e : IExpr n) : LExpr n k
  | ref (i : Fin k) : LExpr n k
  | neg (a : LExpr n k) : LExpr n k
  | abs (a : LExpr n k) : LExpr n k
  | add (a b : LExpr n k) : LExpr n k
  | sub (a b : LExpr n k) : LExpr n k
  | mul (a b : LExpr n k) : LExpr n k
  | div (a b : LExpr n k) (out : Int) : LExpr n k
  | sqrt (a : LExpr n k) (s₁ s₂ : Int) : LExpr n k
  | trans (kk : TKind) (a : LExpr n k) (N : ℕ) (out : Int) : LExpr n k
  | ite (c : IExpr n) (t e : LExpr n k) : LExpr n k

/-- Reference substitution: the unfolded `IExpr` view of an `LExpr`
(used to reuse the `valid_fallback`/`valid_closed` fallback arms). -/
def LExpr.toIExpr {n k : ℕ} : LExpr n k → (Fin k → IExpr n) → IExpr n
  | .plain f, _ => f
  | .ref i, tbl => tbl i
  | .neg a, tbl => .neg (a.toIExpr tbl)
  | .abs a, tbl => .abs (a.toIExpr tbl)
  | .add a b, tbl => .add (a.toIExpr tbl) (b.toIExpr tbl)
  | .sub a b, tbl => .sub (a.toIExpr tbl) (b.toIExpr tbl)
  | .mul a b, tbl => .mul (a.toIExpr tbl) (b.toIExpr tbl)
  | .div a b out, tbl => .div (a.toIExpr tbl) (b.toIExpr tbl) out
  | .sqrt a s₁ s₂, tbl => .sqrt (a.toIExpr tbl) s₁ s₂
  | .trans kk a N out, tbl => .trans kk (a.toIExpr tbl) N out
  | .ite c t e, tbl => .ite c (t.toIExpr tbl) (e.toIExpr tbl)

/-- Closedness of the unfolded view, computed without materializing the
substitution (table references consult the entry directly). -/
def LExpr.isClosed {n k : ℕ} : LExpr n k → (Fin k → IExpr n) → Bool
  | .plain f, _ => f.isClosed
  | .ref i, tbl => (tbl i).isClosed
  | .neg a, tbl => a.isClosed tbl
  | .abs a, tbl => a.isClosed tbl
  | .add a b, tbl => a.isClosed tbl && b.isClosed tbl
  | .sub a b, tbl => a.isClosed tbl && b.isClosed tbl
  | .mul a b, tbl => a.isClosed tbl && b.isClosed tbl
  | .div a b _, tbl => a.isClosed tbl && b.isClosed tbl
  | .sqrt a _ _, tbl => a.isClosed tbl
  | .trans _ a _ _, tbl => a.isClosed tbl
  | .ite c t e, tbl => c.isClosed && t.isClosed tbl && e.isClosed tbl

theorem LExpr.isClosed_toIExpr {n k : ℕ} (e : LExpr n k) (tbl : Fin k → IExpr n) :
    e.isClosed tbl = (e.toIExpr tbl).isClosed := by
  induction e with
  | plain f => rfl
  | ref i => rfl
  | neg a ih => simp only [isClosed, toIExpr, IExpr.isClosed, ih]
  | abs a ih => simp only [isClosed, toIExpr, IExpr.isClosed, ih]
  | add a b iha ihb =>
      simp only [isClosed, toIExpr, IExpr.isClosed, iha, ihb, Bool.and_assoc]
  | sub a b iha ihb =>
      simp only [isClosed, toIExpr, IExpr.isClosed, iha, ihb, Bool.and_assoc]
  | mul a b iha ihb =>
      simp only [isClosed, toIExpr, IExpr.isClosed, iha, ihb, Bool.and_assoc]
  | div a b _ iha ihb =>
      simp only [isClosed, toIExpr, IExpr.isClosed, iha, ihb, Bool.and_assoc]
  | sqrt a _ _ ih => simp only [isClosed, toIExpr, IExpr.isClosed, ih]
  | trans _ a _ _ ih => simp only [isClosed, toIExpr, IExpr.isClosed, ih]
  | ite c t e iht ihe =>
      simp only [isClosed, toIExpr, IExpr.isClosed, iht, ihe, Bool.and_assoc]

/-- Pointwise real semantics: `.ref i` denotes table entry `i` — the
substitution semantics `body[ref i := tbl i]` of the task's `letD`. -/
noncomputable def LExpr.evalReal {n k : ℕ} :
    LExpr n k → (Fin k → IExpr n) → (Fin n → ℝ) → ℝ
  | .plain f, _, ρ => f.evalReal ρ
  | .ref i, tbl, ρ => (tbl i).evalReal ρ
  | .neg a, tbl, ρ => -a.evalReal tbl ρ
  | .abs a, tbl, ρ => |a.evalReal tbl ρ|
  | .add a b, tbl, ρ => a.evalReal tbl ρ + b.evalReal tbl ρ
  | .sub a b, tbl, ρ => a.evalReal tbl ρ - b.evalReal tbl ρ
  | .mul a b, tbl, ρ => a.evalReal tbl ρ * b.evalReal tbl ρ
  | .div a b _, tbl, ρ => a.evalReal tbl ρ / b.evalReal tbl ρ
  | .sqrt a _ _, tbl, ρ => Real.sqrt (a.evalReal tbl ρ)
  | .trans kk a _ _, tbl, ρ => transReal kk (a.evalReal tbl ρ)
  | .ite c t e, tbl, ρ =>
      if c.evalReal ρ < 0 then t.evalReal tbl ρ else e.evalReal tbl ρ

/-- The real semantics of an `LExpr` agrees with its unfolded view. -/
theorem LExpr.evalReal_toIExpr {n k : ℕ} (e : LExpr n k) (tbl : Fin k → IExpr n)
    (ρ : Fin n → ℝ) : e.evalReal tbl ρ = (e.toIExpr tbl).evalReal ρ := by
  induction e with
  | plain f => rfl
  | ref i => rfl
  | neg a ih => simp only [evalReal, toIExpr, IExpr.evalReal, ih]
  | abs a ih => simp only [evalReal, toIExpr, IExpr.evalReal, ih]
  | add a b iha ihb =>
      simp only [evalReal, toIExpr, IExpr.evalReal, iha, ihb]
  | sub a b iha ihb =>
      simp only [evalReal, toIExpr, IExpr.evalReal, iha, ihb]
  | mul a b iha ihb =>
      simp only [evalReal, toIExpr, IExpr.evalReal, iha, ihb]
  | div a b _ iha ihb =>
      simp only [evalReal, toIExpr, IExpr.evalReal, iha, ihb]
  | sqrt a _ _ ih => simp only [evalReal, toIExpr, IExpr.evalReal, ih]
  | trans _ a _ _ ih => simp only [evalReal, toIExpr, IExpr.evalReal, ih]
  | ite c t e iht ihe =>
      simp only [evalReal, toIExpr, IExpr.evalReal, iht, ihe]

/-- Model-table slot update. -/
def updTMEnv {n k : ℕ} (env : Fin k → TaylorM n) (i : Fin k) (M : TaylorM n) :
    Fin k → TaylorM n :=
  fun j => if j.val = i.val then M else env j

theorem updTMEnv_self {n k : ℕ} {env : Fin k → TaylorM n} {i : Fin k}
    {M : TaylorM n} : updTMEnv env i M i = M := by
  show (if i.val = i.val then M else env i) = M
  rw [if_pos rfl]

theorem updTMEnv_ne {n k : ℕ} {env : Fin k → TaylorM n} {i j : Fin k}
    (h : j.val ≠ i.val) {M : TaylorM n} : updTMEnv env i M j = env j := by
  show (if j.val = i.val then M else env j) = env j
  rw [if_neg h]

/-- Guard-decided branch validity over arbitrary branch functions (the
`LExpr` layer instantiates `ft`/`fe` with table-recursive semantics;
otherwise `valid_iteHullD` verbatim). -/
theorem valid_iteHullD_fn {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {c : IExpr n} {ft fe : (Fin n → ℝ) → ℝ} {C : DInterval}
    (hV : M.Valid box ft) (hmem : ∀ ρ, boxMem box ρ → C.mem (c.evalReal ρ))
    (hneg : C.hi.isNeg = true) :
    M.Valid box (fun ρ => if c.evalReal ρ < 0 then ft ρ else fe ρ) := by
  refine hV.congr_box fun ρ hρ => ?_
  show (if c.evalReal ρ < 0 then ft ρ else fe ρ) = ft ρ
  rw [if_pos (lt_of_le_of_lt (hmem ρ hρ).2 ((Dyadic.isNeg_iff C.hi).mp hneg))]

/-- Else-side arbitrary-function variant of `valid_iteHullD_else`. -/
theorem valid_iteHullD_else_fn {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {c : IExpr n} {ft fe : (Fin n → ℝ) → ℝ} {C : DInterval}
    (hV : M.Valid box fe) (hmem : ∀ ρ, boxMem box ρ → C.mem (c.evalReal ρ))
    (hnn : C.lo.isNN = true) :
    M.Valid box (fun ρ => if c.evalReal ρ < 0 then ft ρ else fe ρ) := by
  refine hV.congr_box fun ρ hρ => ?_
  show (if c.evalReal ρ < 0 then ft ρ else fe ρ) = fe ρ
  rw [if_neg (not_lt.mpr (le_trans ((Dyadic.isNN_iff C.lo).mp hnn) (hmem ρ hρ).1))]

/-- Table pass: entries `0..i-1` are evaluated once, in index order
(certificate-free under the MVP emit contract, so `ps` is untouched). -/
def evalLTable {n k : ℕ} (box : Fin n → DInterval) (tbl : Fin k → IExpr n) :
    ℕ → TMParams → Option ((Fin k → TaylorM n) × TMParams)
  | 0, ps => some (fun _ => fallbackTM box ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ps)
  | (i + 1), ps =>
      (evalLTable box tbl i ps).bind fun envps =>
      if h : i < k then
        (evalTMHullD2 box (tbl ⟨i, h⟩) envps.2).map
          fun Mps => (updTMEnv envps.1 ⟨i, h⟩ Mps.1, Mps.2)
      else some envps

/-- **Soundness of `evalLTable`**: every entry slot below the counter holds
a valid box-midpoint model of its table expression. -/
theorem evalLTable_sound {n k : ℕ} {box : Fin n → DInterval}
    (tbl : Fin k → IExpr n) (hwf : ∀ i, (box i).wf = true) :
    ∀ (i : ℕ) (ps : TMParams) (env : Fin k → TaylorM n) (ps' : TMParams),
      evalLTable box tbl i ps = some (env, ps') →
      ∀ (j : Fin k), (j : ℕ) < i →
        (env j).Valid box (fun ρ => (tbl j).evalReal ρ) ∧
        (env j).y = boxCenter box ∧ (env j).w = boxW box := by
  intro i
  induction i with
  | zero => intro ps env ps' h j hj; exact absurd hj (Nat.not_lt_zero j.val)
  | succ i ih =>
      intro ps env ps' h
      simp only [evalLTable] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨env₀, ps₀⟩, h₀, h⟩ := h
      by_cases hi : i < k
      · rw [dif_pos hi] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨M, ps₁⟩, hM, hfinal⟩ := h
        have hfinal' : (updTMEnv env₀ ⟨i, hi⟩ M, ps₁) = (env, ps') := hfinal
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal'
        intro j hj
        by_cases hji : j.val = i
        · have hjeq : j = ⟨i, hi⟩ := Fin.ext hji
          rw [hjeq]
          show (updTMEnv env₀ ⟨i, hi⟩ M ⟨i, hi⟩).Valid box
              (fun ρ => (tbl ⟨i, hi⟩).evalReal ρ) ∧
            (updTMEnv env₀ ⟨i, hi⟩ M ⟨i, hi⟩).y = boxCenter box ∧
              (updTMEnv env₀ ⟨i, hi⟩ M ⟨i, hi⟩).w = boxW box
          rw [updTMEnv_self]
          exact evalTMHullD2_sound _ _ _ _ hwf hM
        · have hne : j.val ≠ (⟨i, hi⟩ : Fin k).val := fun hcon => hji (by rw [hcon])
          show (updTMEnv env₀ ⟨i, hi⟩ M j).Valid box
              (fun ρ => (tbl j).evalReal ρ) ∧
            (updTMEnv env₀ ⟨i, hi⟩ M j).y = boxCenter box ∧
              (updTMEnv env₀ ⟨i, hi⟩ M j).w = boxW box
          rw [updTMEnv_ne hne]
          exact ih ps env₀ ps₀ h₀ j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hji)
      · rw [dif_neg hi] at h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
        exact fun j hj => ih ps env₀ ps₀ h₀ j (by omega)

/-- The let-table hull walker: `.plain` delegates wholesale to
`evalTMHullD2` (internal ite machinery included), `.ref` injects the
entry model, composites mirror `evalTMHullD2` verbatim (fallback/closed
arms go through the unfolded view), `ite` guards stay plain. -/
def evalTMHullD2B {n k : ℕ} (box : Fin n → DInterval)
    (tbl : Fin k → IExpr n) (env : Fin k → TaylorM n) :
    LExpr n k → TMParams → Option (TaylorM n × TMParams)
  | .plain f, ps => evalTMHullD2 box f ps
  | .ref i, ps => some (env i, ps)
  | .neg a, ps => (evalTMHullD2B box tbl env a ps).map fun (M, ps') => (M.neg, ps')
  | .abs a, ps => ((IExpr.abs (a.toIExpr tbl)).eval box).map fun I =>
      (fallbackTM box I, ps)
  | .add a b, ps =>
      (evalTMHullD2B box tbl env a ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2B box tbl env b ps₁).map fun (M₂, ps₂) => (M₁.add M₂, ps₂)
  | .sub a b, ps =>
      (evalTMHullD2B box tbl env a ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2B box tbl env b ps₁).map fun (M₂, ps₂) => (M₁.sub M₂, ps₂)
  | .mul a b, ps =>
      (evalTMHullD2B box tbl env a ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2B box tbl env b ps₁).map fun (M₂, ps₂) => (M₁.mul M₂, ps₂)
  | .div a b out, ps =>
      (evalTMHullD2B box tbl env a ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2B box tbl env b ps₁).bind fun (M₂, ps₂) =>
      ps₂.invCerts.head?.bind fun p =>
      ((M₂.inv p).map fun Mi => (M₁.mul Mi, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail,
          ps₂.transCerts⟩)).orElse
        (fun _ => ((IExpr.div (a.toIExpr tbl) (b.toIExpr tbl) out).eval box).map
          fun I => (fallbackTM box I, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail,
            ps₂.transCerts⟩))
  | .sqrt a s₁ s₂, ps =>
      (evalTMHullD2B box tbl env a ps).bind fun (M₀, ps₀) =>
      ps₀.sqrtCerts.head?.bind fun p =>
      ((M₀.sqrt p).map fun M' => (M', ⟨ps₀.sqrtCerts.tail, ps₀.invCerts,
          ps₀.transCerts⟩)).orElse
        (fun _ => ((IExpr.sqrt (a.toIExpr tbl) s₁ s₂).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩))
  | .trans kk a N out, ps =>
      if a.isClosed tbl then
        evalTMHullD2 box (LExpr.toIExpr (.trans kk a N out) tbl) ps
      else
        (evalTMHullD2B box tbl env a ps).bind fun (M₀, ps₀) =>
        ps₀.transCerts.head?.bind fun p =>
        ((M₀.trans kk N out p).map fun M' =>
            (M', ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩)).orElse
          (fun _ => ((IExpr.trans kk (a.toIExpr tbl) N out).eval box).map fun I =>
            (fallbackTM box I, ⟨ps₀.sqrtCerts, ps₀.invCerts,
              ps₀.transCerts.tail⟩))
  | .ite c t e, ps =>
      (evalIParams box c ps).bind fun (C, ps₀) =>
      if C.hi.isNeg then evalTMHullD2B box tbl env t ps₀
      else if C.lo.isNN then evalTMHullD2B box tbl env e ps₀
      else
        (evalTMHullD2B box tbl env t ps₀).bind fun (Mt, ps₁) =>
        (evalTMHullD2B box tbl env e ps₁).map fun (Me, ps₂) => (iteHullTM2 Mt Me, ps₂)

/-- **Soundness of the `evalTMHullD2B` walker**: table entries are the
`evalTMHullD2`-sound models of their entries (given by `henv`, discharged
by `evalLTable_sound` at the combined entry), and every composite case
repeats the corresponding `evalTMHullD2_sound` argument. -/
theorem evalTMHullD2B_sound {n k : ℕ} {box : Fin n → DInterval}
    {tbl : Fin k → IExpr n} {env : Fin k → TaylorM n}
    (henv : ∀ i, (env i).Valid box (fun ρ => (tbl i).evalReal ρ) ∧
      (env i).y = boxCenter box ∧ (env i).w = boxW box) :
    ∀ (e : LExpr n k) (ps ps' : TMParams) (M : TaylorM n),
      (∀ i, (box i).wf = true) →
      evalTMHullD2B box tbl env e ps = some (M, ps') →
      M.Valid box (fun ρ => e.evalReal tbl ρ) ∧ M.y = boxCenter box ∧
        M.w = boxW box := by
  intro e
  induction e with
  | plain f =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      exact evalTMHullD2_sound f ps ps' M hwf h
  | ref i =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact henv i
  | neg a ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₀, ps₀⟩, he, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
      exact ⟨valid_neg hV, hy, hw⟩
  | abs a ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨I, hI, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      refine ⟨(valid_fallback (cellOK_of_wf hwf) hI).congr_box fun ρ _ =>
        LExpr.evalReal_toIExpr _ tbl ρ, rfl, rfl⟩
  | add a b iha ihb =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := iha ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ihb ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_add hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | sub a b iha ihb =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := iha ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ihb ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_sub hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | mul a b iha ihb =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hV₁, hy₁, hw₁⟩ := iha ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ihb ps₁ ps₂ M₂ hwf h₂
      refine ⟨?_, hy₁, hw₁⟩
      exact valid_mul hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂])
  | div a b out iha ihb =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₂, ps₂⟩, h₂, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      obtain ⟨hV₁, hy₁, hw₁⟩ := iha ps ps₁ M₁ hwf h₁
      obtain ⟨hV₂, hy₂, hw₂⟩ := ihb ps₁ ps₂ M₂ hwf h₂
      cases hi : M₂.inv p with
      | none =>
        rw [hi] at h
        rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        refine ⟨(valid_fallback (cellOK_of_wf hwf) hI).congr_box fun ρ _ =>
          LExpr.evalReal_toIExpr _ tbl ρ, rfl, rfl⟩
      | some Mi =>
        rw [hi] at h
        rw [Option.map_some, Option.orElse_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
        refine ⟨?_, hy₁, hw₁⟩
        exact valid_div hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂]) p hi
  | sqrt a s₁ s₂ ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₀, ps₀⟩, he, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
      cases hs : M₀.sqrt p with
      | none =>
        rw [hs] at h
        rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        refine ⟨(valid_fallback (cellOK_of_wf hwf) hI).congr_box fun ρ _ =>
          LExpr.evalReal_toIExpr _ tbl ρ, rfl, rfl⟩
      | some M' =>
        rw [hs] at h
        rw [Option.map_some, Option.orElse_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
        obtain ⟨hV', hyy, hww⟩ := valid_sqrt hV p hs
        refine ⟨hV', ?_, ?_⟩
        · show M'.y = boxCenter box
          exact hyy.trans hy
        · show M'.w = boxW box
          exact hww.trans hw
  | trans kk a N out ih =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      by_cases hcl : a.isClosed tbl = true
      · rw [if_pos hcl] at h
        have hV' := evalTMHullD2_sound (LExpr.toIExpr (.trans kk a N out) tbl)
          ps ps' M hwf h
        refine ⟨hV'.1.congr_box fun ρ _ => LExpr.evalReal_toIExpr _ tbl ρ,
          hV'.2.1, hV'.2.2⟩
      · rw [if_neg hcl] at h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨⟨M₀, ps₀⟩, he, h⟩ := h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨p, _hp, h⟩ := h
        obtain ⟨hV, hy, hw⟩ := ih ps ps₀ M₀ hwf he
        cases ht : M₀.trans kk N out p with
        | none =>
          rw [ht] at h
          rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
          obtain ⟨I, hI, hfinal⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
          refine ⟨(valid_fallback (cellOK_of_wf hwf) hI).congr_box fun ρ _ =>
            LExpr.evalReal_toIExpr _ tbl ρ, rfl, rfl⟩
        | some M' =>
          rw [ht] at h
          rw [Option.map_some, Option.orElse_some] at h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
          obtain ⟨hV', hyy, hww⟩ := valid_trans hV N out p ht
          refine ⟨hV', ?_, ?_⟩
          · show M'.y = boxCenter box
            exact hyy.trans hy
          · show M'.w = boxW box
            exact hww.trans hw
  | ite c t e iht ihe =>
      intro ps ps' M hwf h
      simp only [evalTMHullD2B] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨C, ps₀⟩, hc, h⟩ := h
      by_cases hneg : C.hi.isNeg = true
      · rw [if_pos hneg] at h
        obtain ⟨hVt, hyt, hwt⟩ := iht ps₀ ps' M hwf h
        refine ⟨valid_iteHullD_fn hVt (fun ρ hρ => evalIParams_mem hρ c ps ps₀ C hc)
          hneg, hyt, hwt⟩
      · rw [if_neg hneg] at h
        by_cases hnn : C.lo.isNN = true
        · rw [if_pos hnn] at h
          obtain ⟨hVe, hye, hwe⟩ := ihe ps₀ ps' M hwf h
          refine ⟨valid_iteHullD_else_fn hVe
            (fun ρ hρ => evalIParams_mem hρ c ps ps₀ C hc) hnn, hye, hwe⟩
        · rw [if_neg hnn] at h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨⟨Mt, ps₁⟩, ht, h⟩ := h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨Me, ps₂⟩, he, hfinal⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
          obtain ⟨hVt, hyt, hwt⟩ := iht ps₀ ps₁ Mt hwf ht
          obtain ⟨hVe, hye, hwe⟩ := ihe ps₁ ps₂ Me hwf he
          refine ⟨valid_iteHull2 c hVt hVe (hyt.trans hye.symm)
            (hwt.trans hwe.symm), hyt, hwt⟩

/-- Combined let-table evaluator: entries once (index order), then the
body walker with model injection at `.ref`. -/
def evalTMHullD2L {n k : ℕ} (box : Fin n → DInterval) (tbl : Fin k → IExpr n)
    (e : LExpr n k) (ps : TMParams) : Option (TaylorM n × TMParams) :=
  (evalLTable box tbl k ps).bind fun (env, ps₀) =>
    evalTMHullD2B box tbl env e ps₀

/-- **Soundness of `evalTMHullD2L`** (`evalLTable_sound` discharging the
walker's table hypothesis, then `evalTMHullD2B_sound`). -/
theorem evalTMHullD2L_sound {n k : ℕ} {box : Fin n → DInterval}
    {tbl : Fin k → IExpr n} :
    ∀ (e : LExpr n k) (ps ps' : TMParams) (M : TaylorM n),
      (∀ i, (box i).wf = true) →
      evalTMHullD2L box tbl e ps = some (M, ps') →
      M.Valid box (fun ρ => e.evalReal tbl ρ) ∧ M.y = boxCenter box ∧
        M.w = boxW box := by
  intro e ps ps' M hwf h
  rw [evalTMHullD2L, Option.bind_eq_some_iff] at h
  obtain ⟨⟨env, ps₀⟩, henv, h⟩ := h
  exact evalTMHullD2B_sound
    (fun i => evalLTable_sound tbl hwf k ps env ps₀ henv i i.isLt) e ps₀ ps' M hwf h

/-- The let-table hull checker (same shape as `checkPosTMHull`). -/
def checkPosTMHullL {n k : ℕ} (tbl : Fin k → IExpr n) (e : LExpr n k)
    (box : Fin n → DInterval) (ps : TMParams) : Bool :=
  (List.finRange n).all (fun i => (box i).wf) &&
    (match evalTMHullD2L box tbl e ps with
    | some (M, _) => (M.loBound box).isPos
    | none => false)

/-- **Soundness of the let-table hull checker** (same two-line composition
as `checkPosTMHull_sound`). -/
theorem checkPosTMHullL_sound {n k : ℕ} {tbl : Fin k → IExpr n} {e : LExpr n k}
    {box : Fin n → DInterval} {ps : TMParams}
    (h : checkPosTMHullL tbl e box ps = true) (ρ : Fin n → ℝ) (hρ : boxMem box ρ) :
    0 < e.evalReal tbl ρ := by
  unfold checkPosTMHullL at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hwfB, h⟩ := h
  have hwf : ∀ i, (box i).wf = true := fun i => hwfB i (List.mem_finRange i)
  cases hE : evalTMHullD2L box tbl e ps with
  | none => rw [hE] at h; simp at h
  | some Mp =>
    obtain ⟨M, ps'⟩ := Mp
    rw [hE] at h
    have hpos := Dyadic.toReal_pos_of_isPos h
    obtain ⟨hV, _, _⟩ := evalTMHullD2L_sound e ps ps' M hwf hE
    exact lt_of_lt_of_le hpos (M.loBound_sound hV hρ)

/-! ### Certificate production: the let-table tracing mirror

`evalTMHullFill2L` mirrors `evalTMHullD2L` node for node on the Fill side
(entries first in index order, then the body, guard-first at `ite` nodes),
so a PASS of `tmHullLeafProbeL` predicts the kernel `checkPosTMHullL` of
the leaf whose `sqrtCerts` carry the reported mantissas.  Required only
when the emit side folds certificate-*consuming* subtrees; the MVP
certificate-free contract keeps the original `TMParams` valid verbatim. -/

def evalLTableFill {n k : ℕ} (box : Fin n → DInterval) (tbl : Fin k → IExpr n) :
    ℕ → TMParams → Option ((Fin k → TaylorM n) × TMParams ×
      List (Int × Int × Int))
  | 0, ps => some (fun _ => fallbackTM box ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ps, [])
  | (i + 1), ps =>
      (evalLTableFill box tbl i ps).bind fun (env, ps₀, l₀) =>
      if h : i < k then
        (evalTMHullFill2 box (tbl ⟨i, h⟩) ps₀).map
          fun (M, ps₁, l) => (updTMEnv env ⟨i, h⟩ M, ps₁, l₀ ++ l)
      else some (env, ps₀, l₀)

/-- Fill-side mirror of the `evalTMHullD2B` walker. -/
def evalTMHullFill2B {n k : ℕ} (box : Fin n → DInterval)
    (tbl : Fin k → IExpr n) (env : Fin k → TaylorM n) :
    LExpr n k → TMParams → Option (TaylorM n × TMParams ×
      List (Int × Int × Int))
  | .plain f, ps => evalTMHullFill2 box f ps
  | .ref i, ps => some (env i, ps, [])
  | .neg a, ps =>
      (evalTMHullFill2B box tbl env a ps).map fun (M, ps', l) => (M.neg, ps', l)
  | .abs a, ps =>
      ((IExpr.abs (a.toIExpr tbl)).eval box).map fun I => (fallbackTM box I, ps, [])
  | .add a b, ps =>
      (evalTMHullFill2B box tbl env a ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill2B box tbl env b ps₁).map fun (M₂, ps₂, l₂) =>
        (M₁.add M₂, ps₂, l₁ ++ l₂)
  | .sub a b, ps =>
      (evalTMHullFill2B box tbl env a ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill2B box tbl env b ps₁).map fun (M₂, ps₂, l₂) =>
        (M₁.sub M₂, ps₂, l₁ ++ l₂)
  | .mul a b, ps =>
      (evalTMHullFill2B box tbl env a ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill2B box tbl env b ps₁).map fun (M₂, ps₂, l₂) =>
        (M₁.mul M₂, ps₂, l₁ ++ l₂)
  | .div a b out, ps =>
      (evalTMHullFill2B box tbl env a ps).bind fun (M₁, ps₁, l₁) =>
      (evalTMHullFill2B box tbl env b ps₁).bind fun (M₂, ps₂, l₂) =>
      ps₂.invCerts.head?.bind fun p =>
      ((M₂.inv p).map fun Mi =>
          (M₁.mul Mi, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩,
            l₁ ++ l₂)).orElse
        (fun _ => ((IExpr.div (a.toIExpr tbl) (b.toIExpr tbl) out).eval box).map
          fun I => (fallbackTM box I,
            ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩, l₁ ++ l₂))
  | .sqrt a s₁ s₂, ps =>
      (evalTMHullFill2B box tbl env a ps).bind fun (M₀, ps₀, l) =>
      ps₀.sqrtCerts.head?.bind fun t =>
      ((if (M₀.fB.lo.add (-M₀.W)).isPos = true then
          let slo := sqrtMantissa M₀.fB.lo
          let shi := sqrtMantissa M₀.fB.hi
          let sc := sqrtMantissa (M₀.fB.lo.add (-M₀.W))
          (M₀.sqrt ⟨slo, shi, sc, t.o1, t.o2⟩).map fun M' =>
            (M', ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩,
              l ++ [(slo, shi, sc)])
        else none).orElse
        (fun _ => ((IExpr.sqrt (a.toIExpr tbl) s₁ s₂).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts,
            ps₀.transCerts⟩, l)))
  | .trans kk a N out, ps =>
      if a.isClosed tbl then
        ((IExpr.trans kk (a.toIExpr tbl) N out).eval box).map fun I =>
          (closedTM box I, ps, [])
      else
        (evalTMHullFill2B box tbl env a ps).bind fun (M₀, ps₀, l) =>
        ps₀.transCerts.head?.bind fun p =>
        ((M₀.trans kk N out p).map fun M' =>
            (M', ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩, l)).orElse
          (fun _ => ((IExpr.trans kk (a.toIExpr tbl) N out).eval box).map fun I =>
            (fallbackTM box I,
              ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩, l))
  | .ite c t e, ps =>
      (evalIParamsFill box c ps).bind fun (C, ps₀, lg) =>
      if C.hi.isNeg then
        (evalTMHullFill2B box tbl env t ps₀).map fun (M, ps', l) =>
          (M, ps', lg ++ l)
      else if C.lo.isNN then
        (evalTMHullFill2B box tbl env e ps₀).map fun (M, ps', l) =>
          (M, ps', lg ++ l)
      else
        (evalTMHullFill2B box tbl env t ps₀).bind fun (Mt, ps₁, l₁) =>
        (evalTMHullFill2B box tbl env e ps₁).map fun (Me, ps₂, l₂) =>
          (iteHullTM2 Mt Me, ps₂, lg ++ l₁ ++ l₂)

/-- Combined Fill mirror of `evalTMHullD2L`. -/
def evalTMHullFill2L {n k : ℕ} (box : Fin n → DInterval)
    (tbl : Fin k → IExpr n) (e : LExpr n k) (ps : TMParams) :
    Option (TaylorM n × TMParams × List (Int × Int × Int)) :=
  (evalLTableFill box tbl k ps).bind fun (env, ps₀, l₀) =>
    (evalTMHullFill2B box tbl env e ps₀).map fun (M, ps₁, l) =>
      (M, ps₁, l₀ ++ l)

/-- One compiled-run let-table leaf probe (same shape as
`tmHullLeafProbe`). -/
def tmHullLeafProbeL {n k : ℕ} (tbl : Fin k → IExpr n) (e : LExpr n k)
    (box : Fin n → DInterval) (ps : TMParams) :
    Option (Bool × Int × Int × List (Int × Int × Int)) :=
  (evalTMHullFill2L box tbl e ps).map fun (M, _, l) =>
    let lb := M.loBound box
    (lb.isPos, lb.m, lb.e, l)

/-! ### let-table smoke test: shared slot under a straddling guard -/

/-- Table with one shared slot (in miniature, the folded discriminant). -/
def exLTbl : Fin 1 → IExpr 1 := fun _ => .var 0

/-- `ite (x − 9/4, 2·ref0, ref0 + 2)`: both branches reference the shared
slot, the guard straddles 0 on `[2, 5/2]` — the 549 leaf shape with the
duplicated subtree folded into entry `0`. -/
def exLBody : LExpr 1 1 :=
  .ite (.sub (.var 0) (.const ⟨9, -2⟩))
    (.mul (.ref ⟨0, by decide⟩) (.plain (.const ⟨2, 0⟩)))
    (.add (.ref ⟨0, by decide⟩) (.plain (.const ⟨2, 0⟩)))

/-- The shared slot is injected as the very same model object: the walker's
`.ref` arm returns `env i` verbatim. -/
theorem exL_ref_is_env (env : Fin 1 → TaylorM 1) (ps : TMParams) :
    evalTMHullD2B exBoxHullChk exLTbl env (.ref ⟨0, by decide⟩) ps
      = some (env ⟨0, by decide⟩, ps) := rfl

/-- The let-table evaluator reproduces the unfolded composite exactly
(df-hull of the two branch models, shared-slot models included). -/
theorem exL_D2_composite :
    evalTMHullD2L exBoxHullChk exLTbl exLBody TMParams.empty
      = some (iteHullTM2 ((varTM exBoxHullChk 0).mul (constTM exBoxHullChk ⟨2, 0⟩))
          ((varTM exBoxHullChk 0).add (constTM exBoxHullChk ⟨2, 0⟩)),
        TMParams.empty) := rfl

/-- The let-table checker closes the straddling toy leaf (kernel `decide`). -/
theorem exL_checkPos :
    checkPosTMHullL exLTbl exLBody exBoxHullChk TMParams.empty = true := by
  decide

#print axioms valid_iteHullD_fn
#print axioms valid_iteHullD_else_fn
#print axioms evalTMHullD2L_sound
#print axioms checkPosTMHullL_sound
#print axioms exL_ref_is_env
#print axioms exL_D2_composite
#print axioms exL_checkPos


end Kepler.Interval
