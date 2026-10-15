/-
  W8: the mixed restrict×bisect certificate tree — the kernel-side assembly
  for mono route A over real leaves (W6a search output + W7 chain rule).

  The W7 `checkMonoCorner` assembles a SINGLE restrict chain: every dimension
  monotone over one box, corner certificate, telescope.  The W6a search over
  real leaves (6 vars, atan/div/sqrt/ite) produces a richer object: a tree
  whose nodes alternate

  - `restrict` — a set of dimensions certified monotone over the node box
    (`derivExpr` positivity certificates, kernel `checkPosTMHull`), so `f`
    never increases when they move to their extreme faces (`sgn j = some
    true`: `lo` face, `some false`: `hi` face); the subtree certifies the
    FACE box `restrictBox box sgn` (a subset of the boundary — the interior
    is covered by the monotonicity telescope, NOT by children);
  - `split` — an exact dyadic bisection along one dimension (`splitOK`, the
    `Cert.BBTree` mechanism); both children cover the node box;

  and whose leaves are plain `checkPosTMHull` successes on their boxes.
  A flat dimension (`derivExpr` identically zero, the W6a "flat" verdict) is
  simply never restricted — its model slope is exactly zero, so keeping it
  free costs no tightness and no certificate.

  This file assembles that: `MonoTree` carries the premises in its nodes
  (kernel-checked at term construction — `by decide` fields, the `BBTree`
  pattern), and `monoTree_sound` turns a tree over a box into `0 < f` at
  every point of the box.  Supporting pieces:

  - `monoWalk_le` / `foldl_sgnDims_facePt` — the telescope over a LIST of
    dimensions (the subset of coordinates a `restrict` node actually moves;
    `checkMonoCorner`'s `monoCorner_le` walks all `n`, which forces every
    dimension signed);
  - `domOK_of_domByInterval` — the `DomOK` premise for real expressions from
    kernel-`decide`able plain interval certificates (divisors away from 0,
    radicands positive, guards sign-decided) — the real-leaf replacement of
    the W7 `domOK_of_domTrivial` route;
  - `evalReal_abs_eq_pos/neg` — the `|u| = ±u` rewrite facts backing the
    emitter's abs elimination (the BIXPCGW leaf carries var-carrying `abs`
    nodes; those strictly signed on the certified box are dropped from the
    certified expression, with the sign premises kernel-`decide` theorems
    of the shard).

  No `sorry`, no native-decide shortcut; the axiom footprint is the standard
  three Mathlib drags in.
-/
import Kepler.Interval.MonoCorner

namespace Kepler.Interval

/-! ## Face restriction and the restricted-point telescope -/

/-- Face restriction recorded by `sgn`: `some true` pins coordinate `i` to
the `lo` face, `some false` to the `hi` face, `none` leaves the coordinate
free (its side is untouched). -/
def restrictBox {n : ℕ} (box : Fin n → DInterval) (sgn : Fin n → Option Bool) :
    Fin n → DInterval :=
  fun i => match sgn i with
    | some true => ⟨(box i).lo, (box i).lo⟩
    | some false => ⟨(box i).hi, (box i).hi⟩
    | none => box i

/-- The point reached from `ρ` by moving every sgn-decided coordinate to its
certified face; free coordinates stay at `ρ`. -/
def facePt {n : ℕ} (box : Fin n → DInterval) (sgn : Fin n → Option Bool)
    (ρ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => match sgn i with
    | some true => (box i).lo.toReal
    | some false => (box i).hi.toReal
    | none => ρ i

/-- The restricted coordinates, in increasing order. -/
def sgnDims {n : ℕ} (sgn : Fin n → Option Bool) : List (Fin n) :=
  (List.finRange n).filter (fun i => Option.isSome (sgn i))

/-- The real point coordinate `j` moves to (its certified face; `0` in the
never-used free case). -/
def faceTarget {n : ℕ} (box : Fin n → DInterval) (sgn : Fin n → Option Bool)
    (j : Fin n) : ℝ :=
  match sgn j with
    | some true => (box j).lo.toReal
    | some false => (box j).hi.toReal
    | none => 0

theorem sgnDims_ne_none {n : ℕ} {sgn : Fin n → Option Bool} {j : Fin n}
    (hj : j ∈ sgnDims sgn) : sgn j ≠ none := by
  have hmem : Option.isSome (sgn j) = true := by
    simpa [sgnDims, List.mem_filter] using hj
  intro hcon
  rw [hcon] at hmem
  simp at hmem

/-- **The restricted-coordinate telescope**: if moving coordinate `j` to its
target `g j` never increases `f` at any in-box base point and any in-side
`x`, then folding the moves over any list of coordinates ends at a point
where `f` is no larger. -/
theorem monoWalk_le {n : ℕ} (f : (Fin n → ℝ) → ℝ) (box : Fin n → DInterval)
    (g : Fin n → ℝ) : ∀ (js : List (Fin n)),
    (∀ j ∈ js, ∀ σ : Fin n → ℝ, boxMem box σ → ∀ x : ℝ, (box j).mem x →
      f (Function.update σ j (g j)) ≤ f (Function.update σ j x)) →
    (∀ j ∈ js, (box j).mem (g j)) →
    ∀ ρ : Fin n → ℝ, boxMem box ρ →
    f (js.foldl (fun σ j => Function.update σ j (g j)) ρ) ≤ f ρ := by
  intro js
  induction js with
  | nil => intro _ _ ρ _; exact le_rfl
  | cons j js ih =>
      intro hstep hg ρ hρ
      have hgj : (box j).mem (g j) := hg j (List.mem_cons_self ..)
      have hσ' : boxMem box (Function.update ρ j (g j)) :=
        boxMem_update hρ j (g j) hgj
      have hstepjs : ∀ k ∈ js, ∀ σ : Fin n → ℝ, boxMem box σ → ∀ x : ℝ,
          (box k).mem x →
          f (Function.update σ k (g k)) ≤ f (Function.update σ k x) :=
        fun k hk σ hσm x hx => hstep k (List.mem_cons_of_mem _ hk) σ hσm x hx
      have hmemjs : ∀ k ∈ js, (box k).mem (g k) := fun k hk =>
        hg k (List.mem_cons_of_mem _ hk)
      refine le_trans (ih hstepjs hmemjs (Function.update ρ j (g j)) hσ') ?_
      have h := hstep j (List.mem_cons_self ..) ρ hρ (ρ j) (hρ j)
      simpa using h

/-- The fold over a list of coordinate updates reads, at coordinate `i`, the
target `g i` iff `i` occurs in the list (repeated occurrences are
idempotent — no distinctness needed). -/
theorem foldl_update_apply {n : ℕ} (js : List (Fin n)) (g : Fin n → ℝ)
    (ρ : Fin n → ℝ) (i : Fin n) :
    (js.foldl (fun σ j => Function.update σ j (g j)) ρ) i
      = if i ∈ js then g i else ρ i := by
  induction js generalizing ρ with
  | nil => simp
  | cons j js ih =>
      rw [List.foldl_cons, ih]
      by_cases hij : i = j
      · subst hij
        rw [if_pos (List.mem_cons_self ..)]
        split
        · rfl
        · simp [Function.update_self]
      · have hup : Function.update ρ j (g j) i = ρ i :=
          Function.update_of_ne hij (g j) ρ
        rw [hup]
        simp only [List.mem_cons, hij, false_or]

/-- The fold over the restricted coordinates ends exactly at `facePt`. -/
theorem foldl_sgnDims_facePt {n : ℕ} (box : Fin n → DInterval)
    (sgn : Fin n → Option Bool) (ρ : Fin n → ℝ) :
    (sgnDims sgn).foldl (fun σ j => Function.update σ j (faceTarget box sgn j)) ρ
      = facePt box sgn ρ := by
  funext i
  rw [foldl_update_apply]
  have hin : i ∈ sgnDims sgn ↔ ∃ b, sgn i = some b := by
    constructor
    · intro hmem
      cases hs : sgn i with
      | none =>
          exfalso
          simp [sgnDims, List.mem_filter, hs] at hmem
      | some b => exact ⟨b, rfl⟩
    · rintro ⟨b, hb⟩
      refine List.mem_filter.mpr ⟨List.mem_finRange i, ?_⟩
      rw [hb]
      rfl
  by_cases h : i ∈ sgnDims sgn
  · rw [if_pos h]
    obtain ⟨b, hb⟩ := hin.mp h
    cases b <;> simp [facePt, faceTarget, hb]
  · have h0 : sgn i = none := by
      by_contra hc
      refine h (hin.mpr ?_)
      match hs : sgn i with
      | none => exact absurd hs hc
      | some b => exact ⟨b, rfl⟩
    simp only [if_neg h, facePt, h0]

/-- **The per-dimension monotone step**: coordinate `j` carries a df
certificate (`sgn j = some true`: `∂ⱼf > 0` on the box; `some false`:
`∂ⱼf < 0`), so moving it to its certified face never increases `f`. -/
theorem monoStep_of_certs {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (sgn : Fin n → Option Bool) (psd : Fin n → TMParams)
    (hsafe : e.derivSafe = true) (hdom : DomOK box e)
    (hincr : ∀ j : Fin n, sgn j = some true →
      checkPosTMHull (IExpr.derivExpr e j) box (psd j) = true)
    (hdecr : ∀ j : Fin n, sgn j = some false →
      checkPosTMHull (IExpr.neg (IExpr.derivExpr e j)) box (psd j) = true)
    (j : Fin n) (hj : sgn j ≠ none)
    (σ : Fin n → ℝ) (hσ : boxMem box σ) (x : ℝ) (hx : (box j).mem x) :
    e.evalReal (Function.update σ j (faceTarget box sgn j))
      ≤ e.evalReal (Function.update σ j x) := by
  rcases hsj : sgn j with _ | b
  · exact absurd hsj hj
  · cases b with
    | true =>
        have hcert := hincr j hsj
        have hpos : ∀ ρ', boxMem box ρ' → 0 < (IExpr.derivExpr e j).evalReal ρ' :=
          fun ρ' hρ' => checkPosTMHull_sound hcert ρ' hρ'
        have hstep := slice_strict_incr e j box σ hσ hsafe hdom hpos
          (box j).lo.toReal x le_rfl hx.1 hx.2
        simpa only [faceTarget, hsj, sliceEval] using hstep
    | false =>
        have hcert := hdecr j hsj
        have hneg : ∀ ρ', boxMem box ρ' →
            (IExpr.derivExpr e j).evalReal ρ' < 0 := by
          intro ρ' hρ'
          have h1 := checkPosTMHull_sound
            (e := IExpr.neg (IExpr.derivExpr e j)) (box := box) hcert ρ' hρ'
          have h2 : IExpr.evalReal (IExpr.neg (IExpr.derivExpr e j)) ρ'
              = -((IExpr.derivExpr e j).evalReal ρ') := by
            simp only [IExpr.evalReal]
          rw [h2] at h1
          linarith
        have hstep := slice_strict_decr e j box σ hσ hsafe hdom hneg
          x (box j).hi.toReal hx.1 hx.2 le_rfl
        simpa only [faceTarget, hsj, sliceEval] using hstep

/-! ## The tree -/

/-- The mixed restrict×bisect certificate tree for the positivity of `e`.
Certificates live in the nodes; the structural covering check is `covers`
(kernel-`decide`able on a concrete tree, the `Cert.BBTree` pattern);
`monoTree_sound` lifts a covering tree to `0 < e` on its root box. -/
inductive MonoTree (n : ℕ) (e : IExpr n) : Type where
  /-- A plain kernel TM-hull certificate on `box`. -/
  | leaf (box : Fin n → DInterval) (ps : TMParams)
      (h : checkPosTMHull e box ps = true) : MonoTree n e
  /-- The restricted dimensions are monotone; the subtree certifies the face
  box `restrictBox box sgn` (the interior is covered by the telescope). -/
  | restrict (box : Fin n → DInterval) (sgn : Fin n → Option Bool)
      (psd : Fin n → TMParams)
      (hwf : ∀ j : Fin n, sgn j ≠ none → (box j).wf = true)
      (hincr : ∀ j : Fin n, sgn j = some true →
        checkPosTMHull (IExpr.derivExpr e j) box (psd j) = true)
      (hdecr : ∀ j : Fin n, sgn j = some false →
        checkPosTMHull (IExpr.neg (IExpr.derivExpr e j)) box (psd j) = true)
      (hsafe : e.derivSafe = true) (hdom : DomOK box e)
      (sub : MonoTree n e) : MonoTree n e
  /-- Exact dyadic bisection along `d`; both children cover the box. -/
  | split (box : Fin n → DInterval) (d : Fin n) (l r : MonoTree n e) :
      MonoTree n e

/-- The box of a tree node (root included). -/
def MonoTree.box {n : ℕ} {e : IExpr n} : MonoTree n e → Fin n → DInterval
  | .leaf b _ _ => b
  | .restrict b _ _ _ _ _ _ _ _ => b
  | .split b _ _ _ => b

/-- The structural covering check: the subtree of a `restrict` node certifies
exactly its face box; a `split` node's children are its exact dyadic halves;
recursively down to the leaves. -/
def MonoTree.covers {n : ℕ} {e : IExpr n} : MonoTree n e → Prop
  | .leaf _ _ _ => True
  | .restrict box sgn _ _ _ _ _ _ sub =>
      sub.covers ∧ sub.box = restrictBox box sgn
  | .split box d l r => splitOK box d l.box r.box ∧ l.covers ∧ r.covers

/-- **Soundness of the certificate tree**: every real point of the root box
sees a strictly positive value of `e`. -/
theorem monoTree_sound {n : ℕ} {e : IExpr n} (t : MonoTree n e)
    (hcov : t.covers) :
    ∀ ρ : Fin n → ℝ, boxMem t.box ρ → 0 < e.evalReal ρ := by
  induction t with
  | leaf box ps h => exact checkPosTMHull_sound h
  | restrict box sgn psd hwf hincr hdecr hsafe hdom sub ih =>
      obtain ⟨hsub, hface⟩ := hcov
      intro ρ hρ
      have hdims : ∀ j ∈ sgnDims sgn, sgn j ≠ none := fun j hj =>
        sgnDims_ne_none hj
      have hstep : ∀ j ∈ sgnDims sgn, ∀ σ : Fin n → ℝ, boxMem box σ →
          ∀ x : ℝ, (box j).mem x →
            e.evalReal (Function.update σ j (faceTarget box sgn j))
              ≤ e.evalReal (Function.update σ j x) := by
        intro j hj σ hσm x hx
        exact monoStep_of_certs e box sgn psd hsafe hdom hincr hdecr j
          (hdims j hj) σ hσm x hx
      have hgte : ∀ j ∈ sgnDims sgn,
          (box j).mem (faceTarget box sgn j) := by
        intro j hj
        have hne := hdims j hj
        cases hs : sgn j with
        | none => exact absurd hs hne
        | some b =>
            cases b with
            | true =>
                simp only [faceTarget, hs, DInterval.mem]
                exact ⟨le_rfl, Dyadic.ble_toReal (hwf j hne)⟩
            | false =>
                simp only [faceTarget, hs, DInterval.mem]
                exact ⟨Dyadic.ble_toReal (hwf j hne), le_rfl⟩
      have htele := monoWalk_le (e.evalReal) box
        (faceTarget box sgn) (sgnDims sgn) hstep hgte ρ hρ
      rw [foldl_sgnDims_facePt] at htele
      have hmem : boxMem sub.box (facePt box sgn ρ) := by
        rw [hface]
        intro i
        cases hs : sgn i with
        | none => simp only [facePt, hs, restrictBox]; exact hρ i
        | some b =>
            cases b with
            | true => simp only [facePt, hs, restrictBox]; exact ⟨le_rfl, le_rfl⟩
            | false => simp only [facePt, hs, restrictBox]; exact ⟨le_rfl, le_rfl⟩
      exact lt_of_lt_of_le (ih hsub (facePt box sgn ρ) hmem) htele
  | split box d l r ihl ihr =>
      obtain ⟨hsplit, hlcov, hrcov⟩ := hcov
      intro ρ hρ
      by_cases hcase : ρ d ≤ (box d).mid.toReal
      · have hρl : boxMem l.box ρ := by
          intro i
          by_cases hid : i = d
          · subst hid
            constructor
            · show (l.box i).lo.toReal ≤ ρ i
              rw [hsplit.2.1]
              exact (hρ i).1
            · show ρ i ≤ (l.box i).hi.toReal
              rw [hsplit.2.2.1]
              exact hcase
          · have hli : l.box i = box i := (hsplit.1 i hid).1
            rw [hli]
            exact hρ i
        exact ihl hlcov ρ hρl
      · have hρr : boxMem r.box ρ := by
          intro i
          by_cases hid : i = d
          · subst hid
            constructor
            · show (r.box i).lo.toReal ≤ ρ i
              rw [hsplit.2.2.2.1]
              exact le_of_lt (lt_of_not_ge hcase)
            · show ρ i ≤ (r.box i).hi.toReal
              rw [hsplit.2.2.2.2]
              exact (hρ i).2
          · have hri : r.box i = box i := (hsplit.1 i hid).2
            rw [hri]
            exact hρ i
        exact ihr hrcov ρ hρr

/-! ## Domain premises from plain interval certificates -/

/-- `optCert o k`: whether `o` is `some a` with `k a = true` (the `Option`-valued
interval checks of the domain facts, as a plain Bool). -/
def optCert {α : Type} : Option α → (α → Bool) → Bool
  | some a, k => k a
  | none, _ => false

theorem optCert_of_some {α : Type} {a : α} (k : α → Bool) :
    optCert (some a) k = k a := rfl

theorem optCert_of_none {α : Type} (k : α → Bool) : optCert none k = false := rfl

theorem option_none_or_some {α : Type} (o : Option α) :
    o = none ∨ ∃ a, o = some a := by
  match o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

/-- Kernel-`decide`able domain facts for a real expression: every divisor's
interval stays away from `0`, every radicand's interval is strictly
positive, every `ite` guard's interval is sign-decided (uniformly on the
box, so the selected branch is fixed). -/
def domByInterval {n : ℕ} (box : Fin n → DInterval) : IExpr n → Bool
  | .const _ => true
  | .var _ => true
  | .neg e => domByInterval box e
  | .abs e => domByInterval box e
  | .ite c t e =>
      optCert (c.eval box) (fun C => (C.hi.isNeg || C.lo.isNN)
        && domByInterval box t && domByInterval box e)
  | .add e₁ e₂ => domByInterval box e₁ && domByInterval box e₂
  | .sub e₁ e₂ => domByInterval box e₁ && domByInterval box e₂
  | .mul e₁ e₂ => domByInterval box e₁ && domByInterval box e₂
  | .div e₁ e₂ _ =>
      optCert (e₂.eval box) (fun J => (J.hi.isNeg || J.lo.isPos)
        && domByInterval box e₁ && domByInterval box e₂)
  | .sqrt e _ _ =>
      optCert (e.eval box) (fun J => J.lo.isPos && domByInterval box e)
  | .trans _ e _ _ => domByInterval box e

theorem domOK_div_of_certs {n : ℕ} (box : Fin n → DInterval) (e₁ e₂ : IExpr n)
    (out : Int) (h : domByInterval box (.div e₁ e₂ out) = true)
    (ih1 : domByInterval box e₁ = true → DomOK box e₁)
    (ih2 : domByInterval box e₂ = true → DomOK box e₂) :
    DomOK box (.div e₁ e₂ out) := by
  have h' : optCert (e₂.eval box) (fun J => (J.hi.isNeg || J.lo.isPos)
      && domByInterval box e₁ && domByInterval box e₂) = true := h
  rcases option_none_or_some (e₂.eval box) with hoo | ⟨J, hJ⟩
  · rw [hoo, optCert_of_none] at h'
    exact absurd h' (by decide)
  · rw [hJ, optCert_of_some] at h'
    obtain ⟨houter, hrec2⟩ := (Bool.and_eq_true _ _).mp h'
    obtain ⟨hcmp, hrec1⟩ := (Bool.and_eq_true _ _).mp houter
    refine .div (fun σ hσ => ?_) (ih1 hrec1) (ih2 hrec2)
    rw [Bool.or_eq_true] at hcmp
    rcases hcmp with hneg | hpos
    · exact ne_of_lt (evalReal_neg_of_hi_neg e₂ box σ hσ J hJ hneg)
    · exact ne_of_gt (evalReal_pos_of_lo_pos e₂ box σ hσ J hJ hpos)

theorem domOK_sqrt_of_certs {n : ℕ} (box : Fin n → DInterval) (e : IExpr n)
    (s₁ s₂ : Int) (h : domByInterval box (.sqrt e s₁ s₂) = true)
    (ih : domByInterval box e = true → DomOK box e) :
    DomOK box (.sqrt e s₁ s₂) := by
  have h' : optCert (e.eval box) (fun J => J.lo.isPos && domByInterval box e)
      = true := h
  rcases option_none_or_some (e.eval box) with hoo | ⟨J, hJ⟩
  · rw [hoo, optCert_of_none] at h'
    exact absurd h' (by decide)
  · rw [hJ, optCert_of_some] at h'
    obtain ⟨hpos, hrec⟩ := (Bool.and_eq_true _ _).mp h'
    refine .sqrt ?_ (ih hrec)
    intro σ hσ
    exact evalReal_pos_of_lo_pos e box σ hσ J hJ hpos

theorem domOK_ite_of_certs {n : ℕ} (box : Fin n → DInterval) (c t e : IExpr n)
    (h : domByInterval box (.ite c t e) = true)
    (iht : domByInterval box t = true → DomOK box t)
    (ihe : domByInterval box e = true → DomOK box e) :
    DomOK box (.ite c t e) := by
  have h' : optCert (c.eval box) (fun C => (C.hi.isNeg || C.lo.isNN)
      && domByInterval box t && domByInterval box e) = true := h
  rcases option_none_or_some (c.eval box) with hoo | ⟨C, hC⟩
  · rw [hoo, optCert_of_none] at h'
    exact absurd h' (by decide)
  · rw [hC, optCert_of_some] at h'
    obtain ⟨houter, he⟩ := (Bool.and_eq_true _ _).mp h'
    obtain ⟨hdec, ht⟩ := (Bool.and_eq_true _ _).mp houter
    rcases hcmp : C.hi.isNeg with _ | _
    · -- C.hi.isNeg = false: the guard is nonnegative on the box
      rw [hcmp, Bool.false_or] at hdec
      refine .ite (Or.inr fun σ hσ => ?_) (iht ht) (ihe he)
      exact evalReal_nonneg_of_lo_nn c box σ hσ C hC hdec
    · -- C.hi.isNeg = true: the guard is negative on the box
      refine .ite (Or.inl fun σ hσ => ?_) (iht ht) (ihe he)
      exact evalReal_neg_of_hi_neg c box σ hσ C hC hcmp

theorem domOK_of_domByInterval {n : ℕ} (box : Fin n → DInterval) (e : IExpr n)
    (h : domByInterval box e = true) : DomOK box e := by
  induction e with
  | const d => exact .const
  | var i => exact .var
  | neg e ih => exact .neg (ih (by simpa [domByInterval] using h))
  | abs e ih => exact .abs (ih (by simpa [domByInterval] using h))
  | ite c t e _ihc iht ihe =>
      exact domOK_ite_of_certs box c t e h iht ihe
  | add e₁ e₂ ih₁ ih₂ =>
      simp only [domByInterval, Bool.and_eq_true] at h
      exact .add (ih₁ h.1) (ih₂ h.2)
  | sub e₁ e₂ ih₁ ih₂ =>
      simp only [domByInterval, Bool.and_eq_true] at h
      exact .sub (ih₁ h.1) (ih₂ h.2)
  | mul e₁ e₂ ih₁ ih₂ =>
      simp only [domByInterval, Bool.and_eq_true] at h
      exact .mul (ih₁ h.1) (ih₂ h.2)
  | div e₁ e₂ out ih₁ ih₂ =>
      exact domOK_div_of_certs box e₁ e₂ out h ih₁ ih₂
  | sqrt e s₁ s₂ ih =>
      exact domOK_sqrt_of_certs box e s₁ s₂ h ih
  | trans k e N out ih => exact .trans (ih (by simpa [domByInterval] using h))

/-! ## abs elimination rewrite facts -/

/-- `|u| = u` at every point where `u > 0` (the emitter's abs-elimination
rewrite for a strictly positive argument). -/
theorem evalReal_abs_eq_pos {n : ℕ} (u : IExpr n) (ρ : Fin n → ℝ)
    (h : 0 < u.evalReal ρ) : (IExpr.abs u).evalReal ρ = u.evalReal ρ := by
  show |u.evalReal ρ| = u.evalReal ρ
  exact abs_of_pos h

/-- `|u| = -u` at every point where `u < 0`. -/
theorem evalReal_abs_eq_neg {n : ℕ} (u : IExpr n) (ρ : Fin n → ℝ)
    (h : u.evalReal ρ < 0) : (IExpr.abs u).evalReal ρ = -u.evalReal ρ := by
  show |u.evalReal ρ| = -u.evalReal ρ
  exact abs_of_neg h


/-! ## Compiled-run slot computation (certificate production only)

The mono-tree certificate needs real `.sqrt` mantissas in the AST (so plain
interval evaluations — the `DomOK` discharge and the closed-`trans` fast
path — succeed) and `(slo, shi, sc)` triples for the TM-visited `.sqrt`
nodes in `TMParams.sqrtCerts` (the Taylor-model route).  `slotsDeep`
synthesizes ALL mantissa pairs bottom-up from the radicand enclosures —
the exact same plain `DInterval` semantics as `IExpr.eval`, zero mirror
risk, no Taylor series (trans nodes return a dummy interval; sound for slot
computation because no `.sqrt` radicand of the guard-resolved programs
contains a `trans` node, verified search-side).  Compiled runs only
(`Nat.sqrt` does not kernel-reduce). -/

/-- The plain-interval value of the trans node, bypassed for slot
computation. -/
def slotsDeep {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → DInterval × List (Int × Int) × IExpr n
  | .const d => (⟨d, d⟩, [], .const d)
  | .var k => (box k, [], .var k)
  | .neg e =>
      let (I, l, f) := slotsDeep box e
      (I.neg, l, .neg f)
  | .abs e =>
      let (I, l, f) := slotsDeep box e
      (I.abs, l, .abs f)
  | .add e₁ e₂ =>
      let (I₁, l₁, f₁) := slotsDeep box e₁
      let (I₂, l₂, f₂) := slotsDeep box e₂
      (I₁.add I₂, l₁ ++ l₂, .add f₁ f₂)
  | .sub e₁ e₂ =>
      let (I₁, l₁, f₁) := slotsDeep box e₁
      let (I₂, l₂, f₂) := slotsDeep box e₂
      (I₁.sub I₂, l₁ ++ l₂, .sub f₁ f₂)
  | .mul e₁ e₂ =>
      let (I₁, l₁, f₁) := slotsDeep box e₁
      let (I₂, l₂, f₂) := slotsDeep box e₂
      (I₁.mul I₂, l₁ ++ l₂, .mul f₁ f₂)
  | .div e₁ e₂ out =>
      let (I₁, l₁, f₁) := slotsDeep box e₁
      let (I₂, l₂, f₂) := slotsDeep box e₂
      ((DInterval.div I₁ I₂ out).getD ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, l₁ ++ l₂,
        .div f₁ f₂ out)
  | .sqrt e _s₁ _s₂ =>
      let (I, l, f) := slotsDeep box e
      let slo := sqrtMantissa I.lo
      let shi := sqrtMantissa I.hi
      let J : DInterval :=
        match (Dyadic.sqrtI I.hi shi).map (·.hi),
            (if I.lo.isNN then (Dyadic.sqrtI I.lo slo).map (·.lo)
              else some (⟨0, 0⟩ : Dyadic)) with
        | some H, some L => ⟨L, H⟩
        | _, _ => ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
      (J, l ++ [(slo, shi)], @IExpr.sqrt n f slo shi)
  | .trans k e N out =>
      let (_, l, f) := slotsDeep box e
      (⟨⟨0, 0⟩, ⟨0, 0⟩⟩, l, .trans k f N out)
  | .ite c t e =>
      let (C, lc, fc) := slotsDeep box c
      let (T, lt, ft) := slotsDeep box t
      let (E2, le, fe) := slotsDeep box e
      let J := if C.hi.isNeg then T else if C.lo.isNN then E2 else T.hull E2
      (J, lc ++ lt ++ le, .ite fc ft fe)

end Kepler.Interval
