/-
Kepler.Text.Gamma4Wide — lane `nli-rest-b2`, part 2: the **`G4ENV-WIDE`**
two-sided envelopes (the wide-box upgrade of `Gamma4EnvAtoms`).

## Why a uniform box `[4, 7.02674064]⁶`

The work order asks for the envelope on `[2hmin,2hplus]×[2,√8]⁵` in `y`, i.e.
`x = y²` in `[(2hmin)², (2hplus)²]×[4,8]⁵`.  That box, however, **contains
degenerate tetrahedra**: at the corner `x = (4,4,8,4,4,8)` one has
`deltaX = 0`, so `A = √(4x₁Δ) = 0` and the slot partials `D_s` are unbounded
(they carry a factor `1/A`).  A two-sided `D` envelope on the literal box
therefore cannot exist.  (This is the wide-box analogue of the `gamma4-w5`
per-`D` negative result.)

The envelopes below are stated on the *uniform* box `[4,7.02674064]⁶`
(`7.02674064 = (2·hplus)²`).  On this box `Δ ≥ 96`, so `A ≥ 39.19` and all
`D_s` are finite.

**Coverage.**  Seven of the fourteen banks have every `y ≤ 2hplus`
(`QITNPEA3848804089`, `QITNPEA5814748276`, `QITNPEA6206775865`,
`QITNPEA5653753305`, `BIXPCGW9455898160`, `FHBVYXZb`, `GLFVCVK4y4crit`), so
their boxes — in every argument order used by `solY`/`vol4f` — are sub-boxes
of this one.  The other seven carry a `y4 ∈ [2hplus, √8]` (or
`[2hmin, √8]`) slot, i.e. an `x = 8` coordinate: the uniform box cannot be
extended to `[4,8]⁶` (degenerate, see above), and the correct domain is the
six "one-wide-slot" boxes `B_k = [4,7.02674064]⁵×[4,8]` (slot `k` wide), on
each of which `Δ ≥ 54.7107…` by transitivity of `Δ` under the 12-element
tetrahedral group.  Extending the atom/`D` envelopes to the `B_k` family is
the remaining envelope work (6 slots × the present atom proofs); it is **not**
in this lane.

Widths are collected in `DELIVERY.md`'s table; they are 500–5000× wider than
the narrow-box `Gamma4Env` widths, which is exactly why this envelope does
**not** recover the derivative signs (see the WBL-1 finding).

## Contents

* the monomial-relaxation pack on `δᵢ = xᵢ − 4 ∈ [0, 3.02674064]`;
* a corner-reduction kit for `deltaX` (concave in each variable, coefficient
  `−x_pair`), giving the rational lower bound `Δ ≥ 96`;
* two-sided envelopes of `Δ₄,Δ₅,Δ₁,Δ₂,Δ₃,Δ₆` (`[−54.02, 119.4]`),
  `u₁₂₆,u₁₃₅` (`[48, 175.61]`), `L` (`[−12.107, 12.107]`), `Δ`
  (`[96, 1928]`) and `A` (`[39.19, 232.9]`).

No `sorry`/`axiom`/`native_decide`; every declaration is axiom-audited.
-/
import Kepler.Text.Gamma4EnvNum

set_option maxHeartbeats 16000000

namespace Kepler.Text

/-! ## The uniform wide box -/

/-- The `G4ENV-WIDE` box in squared coordinates: `xᵢ ∈ [4, (2·hplus)²]`. -/
def g4wBox (x1 x2 x3 x4 x5 x6 : ℝ) : Prop :=
  4 ≤ x1 ∧ x1 ≤ 7.02674064 ∧ 4 ≤ x2 ∧ x2 ≤ 7.02674064 ∧
    4 ≤ x3 ∧ x3 ≤ 7.02674064 ∧ 4 ≤ x4 ∧ x4 ≤ 7.02674064 ∧
    4 ≤ x5 ∧ x5 ≤ 7.02674064 ∧ 4 ≤ x6 ∧ x6 ≤ 7.02674064

theorem g4w_corner : g4wBox 4 4 4 4 4 4 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## The monomial-relaxation pack

On `δᵢ = xᵢ − 4 ∈ [0, 3.02674064]` we have `δᵢ(3.02674064 − δⱼ) ≥ 0`, i.e.
`δᵢδⱼ ≤ 3.02674064·δᵢ`.  These 21 facts are the only nonlinear hints the
atom enclosures need. -/

private theorem g4w_pack {x1 x2 x3 x4 x5 x6 : ℝ}
    (h1 : 4 ≤ x1) (h1' : x1 ≤ 7.02674064)
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 7.02674064)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 7.02674064)
    (h4 : 4 ≤ x4) (h4' : x4 ≤ 7.02674064)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 7.02674064)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 7.02674064) :
    0 ≤ (x1 - 4) * (7.02674064 - x1) ∧
    0 ≤ (x2 - 4) * (7.02674064 - x2) ∧
    0 ≤ (x3 - 4) * (7.02674064 - x3) ∧
    0 ≤ (x4 - 4) * (7.02674064 - x4) ∧
    0 ≤ (x5 - 4) * (7.02674064 - x5) ∧
    0 ≤ (x6 - 4) * (7.02674064 - x6) ∧
    0 ≤ (x1 - 4) * (7.02674064 - x2) ∧
    0 ≤ (x1 - 4) * (7.02674064 - x3) ∧
    0 ≤ (x1 - 4) * (7.02674064 - x4) ∧
    0 ≤ (x1 - 4) * (7.02674064 - x5) ∧
    0 ≤ (x1 - 4) * (7.02674064 - x6) ∧
    0 ≤ (x2 - 4) * (7.02674064 - x3) ∧
    0 ≤ (x2 - 4) * (7.02674064 - x4) ∧
    0 ≤ (x2 - 4) * (7.02674064 - x5) ∧
    0 ≤ (x2 - 4) * (7.02674064 - x6) ∧
    0 ≤ (x3 - 4) * (7.02674064 - x4) ∧
    0 ≤ (x3 - 4) * (7.02674064 - x5) ∧
    0 ≤ (x3 - 4) * (7.02674064 - x6) ∧
    0 ≤ (x4 - 4) * (7.02674064 - x5) ∧
    0 ≤ (x4 - 4) * (7.02674064 - x6) ∧
    0 ≤ (x5 - 4) * (7.02674064 - x6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply mul_nonneg <;> linarith

/-! ## `deltaX` corner reduction (concave in each variable)

`deltaX` is quadratic in each variable with leading coefficient `−x_pair < 0`,
so the minimum over a box is attained at a corner.  `g4w_step` is the
one-variable reduction; the six instances below cover the six slots. -/

/-- One-variable concavity step: if the chord identity holds with `k ≥ 0`, the
minimum over `[a,b]` is attained at an endpoint. -/
theorem g4w_step {f : ℝ → ℝ} {a b t k : ℝ}
    (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) (hk : 0 ≤ k)
    (hid : f t - ((b - t) / (b - a) * f a + (1 - (b - t) / (b - a)) * f b)
      = k * ((t - a) * (b - t))) :
    min (f a) (f b) ≤ f t := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hnn : 0 ≤ k * ((t - a) * (b - t)) := by
    have : 0 ≤ (t - a) * (b - t) := mul_nonneg (by linarith) (by linarith)
    exact mul_nonneg hk this
  have hmin : min (f a) (f b) ≤ lam * f a + (1 - lam) * f b := by
    have hl := min_le_left (f a) (f b)
    have hr := min_le_right (f a) (f b)
    nlinarith
  linarith

private theorem g4w_concave_1 (x2 x3 x4 x5 x6 : ℝ) (hx4 : 0 < x4)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX a x2 x3 x4 x5 x6) (deltaX b x2 x3 x4 x5 x6) ≤
      deltaX t x2 x3 x4 x5 x6 := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX t x2 x3 x4 x5 x6 - (lam * deltaX a x2 x3 x4 x5 x6 + (1 - lam) * deltaX b x2 x3 x4 x5 x6)
      = x4 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX s x2 x3 x4 x5 x6) hat htb hab
    (le_of_lt hx4) hkey

private theorem g4w_concave_2 (x1 x3 x4 x5 x6 : ℝ) (hx5 : 0 < x5)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 a x3 x4 x5 x6) (deltaX x1 b x3 x4 x5 x6) ≤
      deltaX x1 t x3 x4 x5 x6 := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX x1 t x3 x4 x5 x6 - (lam * deltaX x1 a x3 x4 x5 x6 + (1 - lam) * deltaX x1 b x3 x4 x5 x6)
      = x5 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX x1 s x3 x4 x5 x6) hat htb hab
    (le_of_lt hx5) hkey

private theorem g4w_concave_3 (x1 x2 x4 x5 x6 : ℝ) (hx6 : 0 < x6)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 a x4 x5 x6) (deltaX x1 x2 b x4 x5 x6) ≤
      deltaX x1 x2 t x4 x5 x6 := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX x1 x2 t x4 x5 x6 - (lam * deltaX x1 x2 a x4 x5 x6 + (1 - lam) * deltaX x1 x2 b x4 x5 x6)
      = x6 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX x1 x2 s x4 x5 x6) hat htb hab
    (le_of_lt hx6) hkey

private theorem g4w_concave_4 (x1 x2 x3 x5 x6 : ℝ) (hx1 : 0 < x1)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 a x5 x6) (deltaX x1 x2 x3 b x5 x6) ≤
      deltaX x1 x2 x3 t x5 x6 := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX x1 x2 x3 t x5 x6 - (lam * deltaX x1 x2 x3 a x5 x6 + (1 - lam) * deltaX x1 x2 x3 b x5 x6)
      = x1 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX x1 x2 x3 s x5 x6) hat htb hab
    (le_of_lt hx1) hkey

private theorem g4w_concave_5 (x1 x2 x3 x4 x6 : ℝ) (hx2 : 0 < x2)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 x4 a x6) (deltaX x1 x2 x3 x4 b x6) ≤
      deltaX x1 x2 x3 x4 t x6 := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX x1 x2 x3 x4 t x6 - (lam * deltaX x1 x2 x3 x4 a x6 + (1 - lam) * deltaX x1 x2 x3 x4 b x6)
      = x2 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX x1 x2 x3 x4 s x6) hat htb hab
    (le_of_lt hx2) hkey

private theorem g4w_concave_6 (x1 x2 x3 x4 x5 : ℝ) (hx3 : 0 < x3)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 x4 x5 a) (deltaX x1 x2 x3 x4 x5 b) ≤
      deltaX x1 x2 x3 x4 x5 t := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX x1 x2 x3 x4 x5 t - (lam * deltaX x1 x2 x3 x4 x5 a + (1 - lam) * deltaX x1 x2 x3 x4 x5 b)
      = x3 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX x1 x2 x3 x4 x5 s) hat htb hab
    (le_of_lt hx3) hkey

/-- **`G4ENV-WIDE` `Δ` lower bound**: `96 ≤ Δ` on `[4, 7.02674064]⁶`
(the exact corner minimum is `96.109…`, at `(4,4,7.02674064,4,4,7.02674064)`). -/
theorem g4w_deltaX_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    (96:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have e1 : min (deltaX 4 x2 x3 x4 x5 x6) (deltaX 7.02674064 x2 x3 x4 x5 x6)
      ≤ deltaX x1 x2 x3 x4 x5 x6 :=
    g4w_concave_1 x2 x3 x4 x5 x6 (by linarith) 4 7.02674064 x1 h1 h1' (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (g4w_concave_2 _ _ _ _ _ (by linarith) 4 7.02674064 _
    (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (g4w_concave_3 _ _ _ _ _ (by linarith) 4 7.02674064 _
    (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (g4w_concave_4 _ _ _ _ _ (by linarith) 4 7.02674064 _
    (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (g4w_concave_5 _ _ _ _ _ (by linarith) 4 7.02674064 _
    (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (g4w_concave_6 _ _ _ _ _ (by linarith) 4 7.02674064 _
    (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX])

/-! ## The polynomial atom envelopes -/

set_option maxHeartbeats 8000000 in
/-- `Δ₄ ∈ [−54.02, 119.4]` on the wide box (termwise monomial relaxation). -/
theorem g4w_deltaX4_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    (-54.02:ℝ) ≤ deltaX4 x1 x2 x3 x4 x5 x6 ∧ deltaX4 x1 x2 x3 x4 x5 x6 ≤ 119.4 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ :=
    g4w_pack h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hexp : deltaX4 x1 x2 x3 x4 x5 x6
      = 16 + 4*(x6-4) + 4*(x5-4) + -8*(x4-4) + 4*(x3-4) + 4*(x2-4)
        + -1*(x5-4)*(x6-4) + 1*(x3-4)*(x6-4) + 1*(x2-4)*(x5-4)
        + -1*(x2-4)*(x3-4) + 1*(x1-4)*(x6-4) + 1*(x1-4)*(x5-4)
        + -2*(x1-4)*(x4-4) + 1*(x1-4)*(x3-4) + 1*(x1-4)*(x2-4)
        + -1*(x1-4)*(x1-4) := by
    unfold deltaX4; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

set_option maxHeartbeats 8000000 in
/-- `Δ₅ ∈ [−54.02, 119.4]` on the wide box. -/
theorem g4w_deltaX5_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    (-54.02:ℝ) ≤ deltaX5 x1 x2 x3 x4 x5 x6 ∧ deltaX5 x1 x2 x3 x4 x5 x6 ≤ 119.4 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ :=
    g4w_pack h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hexp : deltaX5 x1 x2 x3 x4 x5 x6
      = 16 + 4*(x6-4) + -8*(x5-4) + 4*(x4-4) + 4*(x3-4) + 4*(x1-4)
        + -1*(x4-4)*(x6-4) + 1*(x3-4)*(x6-4) + 1*(x2-4)*(x6-4)
        + -2*(x2-4)*(x5-4) + 1*(x2-4)*(x4-4) + 1*(x2-4)*(x3-4)
        + -1*(x2-4)*(x2-4) + 1*(x1-4)*(x4-4) + -1*(x1-4)*(x3-4)
        + 1*(x1-4)*(x2-4) := by
    unfold deltaX5; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

set_option maxHeartbeats 8000000 in
/-- `Δ₁ ∈ [−54.02, 119.4]` on the wide box. -/
theorem g4w_DX1_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    (-54.02:ℝ) ≤ g4dDX1 x1 x2 x3 x4 x5 x6 ∧ g4dDX1 x1 x2 x3 x4 x5 x6 ≤ 119.4 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ :=
    g4w_pack h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hexp : g4dDX1 x1 x2 x3 x4 x5 x6
      = 16 + 4*(x6-4) + 4*(x5-4) + 4*(x3-4) + 4*(x2-4) + -8*(x1-4)
        + 1*(x4-4)*(x6-4) + 1*(x4-4)*(x5-4) + -1*(x4-4)*(x4-4)
        + 1*(x3-4)*(x6-4) + -1*(x3-4)*(x5-4) + 1*(x3-4)*(x4-4)
        + -1*(x2-4)*(x6-4) + 1*(x2-4)*(x5-4) + 1*(x2-4)*(x4-4)
        + -2*(x1-4)*(x4-4) := by
    unfold g4dDX1; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

set_option maxHeartbeats 8000000 in
/-- `Δ₂ ∈ [−54.02, 119.4]` on the wide box. -/
theorem g4w_DX2_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    (-54.02:ℝ) ≤ g4dDX2 x1 x2 x3 x4 x5 x6 ∧ g4dDX2 x1 x2 x3 x4 x5 x6 ≤ 119.4 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ :=
    g4w_pack h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hexp : g4dDX2 x1 x2 x3 x4 x5 x6
      = 16 + 4*(x6-4) + 4*(x4-4) + 4*(x3-4) + -8*(x2-4) + 4*(x1-4)
        + 1*(x5-4)*(x6-4) + -1*(x5-4)*(x5-4) + 1*(x4-4)*(x5-4)
        + 1*(x3-4)*(x6-4) + 1*(x3-4)*(x5-4) + -1*(x3-4)*(x4-4)
        + -2*(x2-4)*(x5-4) + -1*(x1-4)*(x6-4) + 1*(x1-4)*(x5-4)
        + 1*(x1-4)*(x4-4) := by
    unfold g4dDX2; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

set_option maxHeartbeats 8000000 in
/-- `Δ₃ ∈ [−54.02, 119.4]` on the wide box. -/
theorem g4w_DX3_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    (-54.02:ℝ) ≤ g4dDX3 x1 x2 x3 x4 x5 x6 ∧ g4dDX3 x1 x2 x3 x4 x5 x6 ≤ 119.4 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ :=
    g4w_pack h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hexp : g4dDX3 x1 x2 x3 x4 x5 x6
      = 16 + 4*(x5-4) + 4*(x4-4) + -8*(x3-4) + 4*(x2-4) + 4*(x1-4)
        + -1*(x6-4)*(x6-4) + 1*(x5-4)*(x6-4) + 1*(x4-4)*(x6-4)
        + -2*(x3-4)*(x6-4) + 1*(x2-4)*(x6-4) + 1*(x2-4)*(x5-4)
        + -1*(x2-4)*(x4-4) + 1*(x1-4)*(x6-4) + -1*(x1-4)*(x5-4)
        + 1*(x1-4)*(x4-4) := by
    unfold g4dDX3; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

set_option maxHeartbeats 8000000 in
/-- `Δ₆ ∈ [−54.02, 119.4]` on the wide box. -/
theorem g4w_DX6_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    (-54.02:ℝ) ≤ g4dDX6 x1 x2 x3 x4 x5 x6 ∧ g4dDX6 x1 x2 x3 x4 x5 x6 ≤ 119.4 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ :=
    g4w_pack h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hexp : g4dDX6 x1 x2 x3 x4 x5 x6
      = 16 + -8*(x6-4) + 4*(x5-4) + 4*(x4-4) + 4*(x2-4) + 4*(x1-4)
        + -1*(x4-4)*(x5-4) + -2*(x3-4)*(x6-4) + 1*(x3-4)*(x5-4)
        + 1*(x3-4)*(x4-4) + -1*(x3-4)*(x3-4) + 1*(x2-4)*(x5-4)
        + 1*(x2-4)*(x3-4) + 1*(x1-4)*(x4-4) + 1*(x1-4)*(x3-4)
        + -1*(x1-4)*(x2-4) := by
    unfold g4dDX6; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

set_option maxHeartbeats 8000000 in
/-- `u₁₂₆ ∈ [48, 175.61]` on the wide box.  The lower bound is sharp (the
minimum `48` is attained at `x₁=x₂=x₆=4`): the expansion
`u₁₂₆ = 48 + 8Σδ − ½Σ(δᵢ−δⱼ)²` and `½Σ(δᵢ−δⱼ)² ≤ 2·3.02674064·Σδ < 8Σδ`
give it without dropping terms. -/
theorem g4w_u126_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    (48:ℝ) ≤ upsX x1 x2 x6 ∧ upsX x1 x2 x6 ≤ 175.61 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ :=
    g4w_pack h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hexp : upsX x1 x2 x6
      = 48 + 8*(x6-4) + 8*(x2-4) + 8*(x1-4)
        + -1*(x6-4)*(x6-4) + 2*(x2-4)*(x6-4) + -1*(x2-4)*(x2-4)
        + 2*(x1-4)*(x6-4) + 2*(x1-4)*(x2-4) + -1*(x1-4)*(x1-4) := by
    unfold upsX; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

set_option maxHeartbeats 8000000 in
/-- `u₁₃₅ ∈ [48, 175.61]` on the wide box. -/
theorem g4w_u135_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    (48:ℝ) ≤ upsX x1 x3 x5 ∧ upsX x1 x3 x5 ≤ 175.61 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ :=
    g4w_pack h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hexp : upsX x1 x3 x5
      = 48 + 8*(x5-4) + 8*(x3-4) + 8*(x1-4)
        + -1*(x5-4)*(x5-4) + 2*(x3-4)*(x5-4) + -1*(x3-4)*(x3-4)
        + 2*(x1-4)*(x5-4) + 2*(x1-4)*(x3-4) + -1*(x1-4)*(x1-4) := by
    unfold upsX; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

/-- `L = −2x₁+x₂+x₃−2x₄+x₅+x₆ ∈ [−12.107, 12.107]` on the wide box. -/
theorem g4w_L_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    (-12.107:ℝ) ≤ -2 * x1 + x2 + x3 - 2 * x4 + x5 + x6 ∧
      -2 * x1 + x2 + x3 - 2 * x4 + x5 + x6 ≤ 12.107 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  constructor <;> linarith

/-- `Δ ≤ 1928` on the wide box, through the rationalisation identity
`Δ₄² + 4x₁Δ = u₁₂₆·u₁₃₅` (drop the nonnegative square and use `x₁ ≥ 4`). -/
theorem g4w_deltaX_upper {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    deltaX x1 x2 x3 x4 x5 x6 ≤ 1928 := by
  obtain ⟨hu1lo, hu1hi⟩ := g4w_u126_bounds hb
  obtain ⟨hu3lo, hu3hi⟩ := g4w_u135_bounds hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hid := g4d_ups_delta x1 x2 x3 x4 x5 x6
  have hprod : upsX x1 x2 x6 * upsX x1 x3 x5 ≤ 175.61 * 175.61 :=
    mul_le_mul hu1hi hu3hi (by linarith [hu3lo]) (by norm_num)
  nlinarith [hid, hprod, h1]

/-- The radical `A = √(4·x₁·Δ) ∈ [39.19, 232.9]` on the wide box. -/
theorem g4w_A_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    39.19 ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ∧
      Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≤ 232.9 := by
  have hdlo : (96:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := g4w_deltaX_bounds hb
  have hdhi : deltaX x1 x2 x3 x4 x5 x6 ≤ 1928 := g4w_deltaX_upper hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [h1, hdlo]
  · rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 232.9)]
    nlinarith [h1', hdhi]

/-! ## Axiom audit (house style) -/

#print axioms g4w_corner
#print axioms g4w_step
#print axioms g4w_deltaX_bounds
#print axioms g4w_deltaX4_bounds
#print axioms g4w_deltaX5_bounds
#print axioms g4w_DX1_bounds
#print axioms g4w_DX2_bounds
#print axioms g4w_DX3_bounds
#print axioms g4w_DX6_bounds
#print axioms g4w_u126_bounds
#print axioms g4w_u135_bounds
#print axioms g4w_L_bounds
#print axioms g4w_deltaX_upper
#print axioms g4w_A_bounds

end Kepler.Text
