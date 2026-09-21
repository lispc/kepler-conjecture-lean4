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

/-- Model of `f · g`.  Remainder: with `r_f = f − f_y − L_f`,
`fg − f_yg_y − Σᵢ(a_fᵢ g_y + f_y a_gᵢ)uᵢ
  = L_f L_g + r_f (g_y + L_g + r_g) + r_g (f_y + L_f)`, bounded by
`W̃f·W̃g + err_f·(|gB| + W̃g + err_g) + err_g·(|fB| + W̃f)` where
`W̃ := W0`. -/
def mul {n : ℕ} (Mf Mg : TaylorM n) : TaylorM n :=
  ⟨Mf.y, Mf.w, Mf.fB.mul Mg.fB,
    fun i => ((Mf.dfB i).mul Mg.fB).add (Mf.fB.mul (Mg.dfB i)),
    (Mf.W0.mul Mg.W0).add
      ((Mf.err.mul ((Mg.fB.abs.hi.add Mg.W0).add Mg.err)).add
        (Mg.err.mul (Mf.fB.abs.hi.add Mf.W0)))⟩

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
      (M.err.mul J.hi).add ((M.W.mul M.W).mul K.hi)⟩
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
    have herr : (Mf.mul Mg).err.toReal
        = Mf.W0.toReal * Mg.W0.toReal
          + (Mf.err.toReal * (Mg.fB.abs.hi.toReal + Mg.W0.toReal + Mg.err.toReal)
            + Mg.err.toReal * (Mf.fB.abs.hi.toReal + Mf.W0.toReal)) := by
      show (Dyadic.add (Mf.W0.mul Mg.W0)
          ((Mf.err.mul ((Mg.fB.abs.hi.add Mg.W0).add Mg.err)).add
            (Mg.err.mul (Mf.fB.abs.hi.add Mf.W0)))).toReal = _
      rw [Dyadic.toReal_add, Dyadic.toReal_mul, Dyadic.toReal_add, Dyadic.toReal_mul,
        Dyadic.toReal_mul, Dyadic.toReal_add, Dyadic.toReal_add, Dyadic.toReal_add]
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
      (M.err.mul J.hi).add ((M.W.mul M.W).mul K.hi)⟩ := h.symm
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
      have herr' : (⟨M.y, M.w, ⟨Jl.lo, Jh.hi⟩, fun i => (M.dfB i).mul J,
          (M.err.mul J.hi).add ((M.W.mul M.W).mul K.hi)⟩ : TaylorM n).err.toReal
          = M.err.toReal * J.hi.toReal + M.W.toReal ^ 2 * K.hi.toReal := by
        show (Dyadic.add (M.err.mul J.hi) ((M.W.mul M.W).mul K.hi)).toReal = _
        rw [Dyadic.toReal_add, Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul,
          pow_two]
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

/-! ## Single-pass Taylor-model evaluation -/

/-- Single-pass Taylor-model evaluation (TM0: `const`/`var`/`neg`/`add`/`sub`/
`mul`/`sqrt` only; `abs`/`ite`/`div`/`trans` return `none`).  The center is
always the box midpoint; `sqrt` certificates are consumed from the list in
traversal order (each `sqrt` node takes the head bundle). -/
def evalTM {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → List SqrtTMP → Option (TaylorM n × List SqrtTMP)
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
  | .sqrt e _ _, ps =>
      (evalTM box e ps).bind fun (M₀, ps₀) =>
      ps₀.head?.bind fun p =>
      (M₀.sqrt p).map fun M' => (M', ps₀.tail)
  | .abs _, _ => none
  | .ite _ _ _, _ => none
  | .div _ _ _, _ => none
  | .trans _ _ _ _, _ => none

/-- **Soundness of `evalTM`**: a successful evaluation produces a valid model
of the real semantics, centered at the box midpoint with the midpoint
envelope. -/
theorem evalTM_sound {n : ℕ} {box : Fin n → DInterval} :
    ∀ (e : IExpr n) (ps ps' : List SqrtTMP) (M : TaylorM n),
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
      exact absurd h (by simp)
  | trans k e N out ih =>
      intro ps ps' M hwf h
      simp only [evalTM] at h
      exact absurd h (by simp)

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
    (ps : List SqrtTMP) : Bool :=
  (List.finRange n).all (fun i => (box i).wf) &&
    (match evalTM box e ps with
    | some (M, _) => (M.loBound box).isPos
    | none => false)

/-- **Core checker theorem** (same shape as `checkPos_sound`): if `checkPosTM`
passes, the expression is strictly positive at every real assignment
pointwise inside the box. -/
theorem checkPosTM_sound {n : ℕ} {e : IExpr n} {box : Fin n → DInterval}
    {ps : List SqrtTMP}
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

end Kepler.Interval
