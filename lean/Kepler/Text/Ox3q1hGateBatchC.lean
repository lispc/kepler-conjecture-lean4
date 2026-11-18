/-
Ox3q1hGateBatch: S4 per-conjunct gates, components 120-179 (of 230; LIN = idx ≡ 0 mod 5).
Statement text VERBATIM from ox3q1hP25 (conj230_verbatim.json; PA25:94).
LIN gates: ox3q1hLin_NNN applied directly (closed).
G4 gates: two supply slots hsl/hcorner (landed chain_idxN premise shapes;
to be discharged by the S2-envelope and corner-bank lanes), plus a fully
mechanical core: hx from verbatim premises via nb17_hminus_bounds and
h0=1.26 / hplus=1.3254, hK0/hR0/feasibility by norm_num, chain application,
margin rewrite, linarith. Rebate direction: f y >= B - sum R > 0.
Data cross-check passed at emit time: premise endpoints vs BOXES_EXACT,
1104/1104 exact-Fraction equalities (0 mismatch).
Generator: scripts/emit_gate.py. No new sorry/axiom/native_decide.
-/
import Kepler.Text.Ox3q1hChainBatch6
import Kepler.Text.Ox3q1hChainBatch1
import Kepler.Text.Ox3q1hLin46
import Kepler.Text.Ox3q1hChainSplit2
import Kepler.Text.Ox3q1hChainSplitKit

open Set Filter Topology

namespace Kepler.Text

/-- Fin-6 sum as explicit addition (Mathlib Fin.sum_univ_six alias for reuse). -/
theorem sumFin6c (f : Fin 6 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_six]

/-- Component 120 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c120_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.066935) + (0.028887 + 0.014102 + (-0.021495) + (-0.021495)) * y1 + 2 * ((-0.066241) + 0.066241) * y12 + 2 * (0.066241 + (-0.066241)) * y23 + 2 * ((-0.066241) + 0.066241) * y34 + 2 * (0.066241 + (-0.066241)) * y41 + (0.582391 + (-0.472584) + 0.685308 + (-0.374549)) < 0 :=
  ox3q1hLin_120

/-- Margin function of conjunct 121 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c121_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.066935) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.028887 * (y 0) + (-0.066241) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.582391

theorem c121_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c121_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + 0.028887 * y1 + (-0.066241) * (y2 + y3 + y5 + y6) + 0.582391 :=
  rfl

/-- Component 121 gate (box 25; S4.5 split-grid chain
`chain_split_idx121`, split factors per SPLIT_PLAN route `Y4PATCH:y4`, m_min =
2; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c121_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit121 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b25lo j) (b25hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit121 i k) (gsplit121 i (k + 1)))
        (fun t => c121_mfunc (Function.update y i t) - K121 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split121 j) → B121 ≤ c121_mfunc v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + 0.028887 * y1 + (-0.066241) * (y2 + y3 + y5 + y6) + 0.582391 > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b25lo j) (b25hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b25lo, b25hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx121 c121_mfunc hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c121_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx121
  linarith [hchain, hpos]

/-- Margin function of conjunct 122 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c122_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.066935) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.014102 * (y 0) + 0.066241 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.472584)

theorem c122_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c122_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + 0.014102 * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.472584) :=
  rfl

/-- Component 122 gate (box 27; chain chain_idx122; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c122_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b27lo j) (b27hi j)) →
      ConcaveOn ℝ (Set.Icc (b27lo i) (b27hi i))
        (fun t => c122_mfunc (Function.update y i t) - K122 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb27 j) → B122 ≤ c122_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 2 + 3 / 2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + 0.014102 * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.472584) > 0 := by
  have hpos : (0 : ℝ) <
      B122 - ∑ i, R122 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R122 i = K122 i * (b27hi i - b27lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K122 0 = (0 : ℝ) := by rfl
    have t1 : K122 1 = (0 : ℝ) := by rfl
    have t2 : K122 2 = (0 : ℝ) := by rfl
    have t3 : K122 3 = (0 : ℝ) := by rfl
    have t4 : K122 4 = (0 : ℝ) := by rfl
    have t5 : K122 5 = (0 : ℝ) := by rfl
    have u0 : b27hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b27lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b27hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b27lo 1 = (2 : ℝ) := by rfl
    have u2 : b27hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b27lo 2 = (2 : ℝ) := by rfl
    have u3 : b27hi 3 = ((27897/12500) : ℝ) := by rfl
    have q3 : b27lo 3 = ((16927/8000) : ℝ) := by rfl
    have u4 : b27hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b27lo 4 = (2 : ℝ) := by rfl
    have u5 : b27hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b27lo 5 = (2 : ℝ) := by rfl
    have eb : B122 = ((57932445597151768384501/28823037615171174400000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b27lo j) (b27hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b27lo, b27hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K122 i := by
    intro i; fin_cases i <;> norm_num [K122]
  have hR0 : ∀ i, 0 ≤ R122 i := by
    intro i; fin_cases i <;> norm_num [R122, K122, b27lo, b27hi]
  have hchain := chain_idx122 c122_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c122_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 123 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c123_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.066935) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.021495) * (y 0) + (-0.066241) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.685308

theorem c123_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c123_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.021495) * y1 + (-0.066241) * (y2 + y3 + y5 + y6) + 0.685308 :=
  rfl

/-- Component 123 gate (box 28; chain chain_idx123; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c123_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b28lo j) (b28hi j)) →
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => c123_mfunc (Function.update y i t) - K123 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B123 ≤ c123_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.021495) * y1 + (-0.066241) * (y2 + y3 + y5 + y6) + 0.685308 > 0 := by
  have hpos : (0 : ℝ) <
      B123 - ∑ i, R123 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R123 i = K123 i * (b28hi i - b28lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K123 0 = (0 : ℝ) := by rfl
    have t1 : K123 1 = (0 : ℝ) := by rfl
    have t2 : K123 2 = (0 : ℝ) := by rfl
    have t3 : K123 3 = (0 : ℝ) := by rfl
    have t4 : K123 4 = (0 : ℝ) := by rfl
    have t5 : K123 5 = (0 : ℝ) := by rfl
    have u0 : b28hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b28lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b28hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b28lo 1 = (2 : ℝ) := by rfl
    have u2 : b28hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b28lo 2 = (2 : ℝ) := by rfl
    have u3 : b28hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b28lo 3 = (2 : ℝ) := by rfl
    have u4 : b28hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b28lo 4 = (2 : ℝ) := by rfl
    have u5 : b28hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b28lo 5 = (2 : ℝ) := by rfl
    have eb : B123 = ((7238830132115033097287123/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b28lo j) (b28hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b28lo, b28hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K123 i := by
    intro i; fin_cases i <;> norm_num [K123]
  have hR0 : ∀ i, 0 ≤ R123 i := by
    intro i; fin_cases i <;> norm_num [R123, K123, b28lo, b28hi]
  have hchain := chain_idx123 c123_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c123_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 124 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c124_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.066935) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.021495) * (y 0) + 0.066241 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.374549)

theorem c124_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c124_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.021495) * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.374549) :=
  rfl

/-- Component 124 gate (box 28; chain chain_idx124; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c124_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b28lo j) (b28hi j)) →
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => c124_mfunc (Function.update y i t) - K124 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B124 ≤ c124_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.021495) * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.374549) > 0 := by
  have hpos : (0 : ℝ) <
      B124 - ∑ i, R124 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R124 i = K124 i * (b28hi i - b28lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K124 0 = (0 : ℝ) := by rfl
    have t1 : K124 1 = (0 : ℝ) := by rfl
    have t2 : K124 2 = (0 : ℝ) := by rfl
    have t3 : K124 3 = (0 : ℝ) := by rfl
    have t4 : K124 4 = (0 : ℝ) := by rfl
    have t5 : K124 5 = (0 : ℝ) := by rfl
    have u0 : b28hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b28lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b28hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b28lo 1 = (2 : ℝ) := by rfl
    have u2 : b28hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b28lo 2 = (2 : ℝ) := by rfl
    have u3 : b28hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b28lo 3 = (2 : ℝ) := by rfl
    have u4 : b28hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b28lo 4 = (2 : ℝ) := by rfl
    have u5 : b28hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b28lo 5 = (2 : ℝ) := by rfl
    have eb : B124 = ((289707778743033646466769/144115188075855872000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b28lo j) (b28hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b28lo, b28hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K124 i := by
    intro i; fin_cases i <;> norm_num [K124]
  have hR0 : ∀ i, 0 ≤ R124 i := by
    intro i; fin_cases i <;> norm_num [R124, K124, b28lo, b28hi]
  have hchain := chain_idx124 c124_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c124_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 125 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c125_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (3 * h0 / 2 + 1 * hplus / 2) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.070081) + (0.043025 + (-0.014342) + (-0.014342) + (-0.014342)) * y1 + 2 * (0.06775 + (-0.06775)) * y12 + 2 * ((-0.06775) + 0.06775) * y23 + 2 * (0.06775 + (-0.06775)) * y34 + 2 * ((-0.06775) + 0.06775) * y41 + ((-0.520998) + 0.681778 + (-0.402228) + 0.681778) < 0 :=
  ox3q1hLin_125

/-- Margin function of conjunct 126 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c126_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.070081) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.043025 * (y 0) + 0.06775 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.520998)

theorem c126_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c126_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.070081) * dihY y1 y2 y3 y4 y5 y6 + 0.043025 * y1 + 0.06775 * (y2 + y3 + y5 + y6) + (-0.520998) :=
  rfl

/-- Component 126 gate (box 29; S4.5 split-grid chain
`chain_split_idx126`, split factors per SPLIT_PLAN route `Y4PATCH:y4`, m_min =
2; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c126_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit126 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b29lo j) (b29hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit126 i k) (gsplit126 i (k + 1)))
        (fun t => c126_mfunc (Function.update y i t) - K126 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split126 j) → B126 ≤ c126_mfunc v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 2 + 1 * hplus / 2) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (h0 + hplus) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.070081) * dihY y1 y2 y3 y4 y5 y6 + 0.043025 * y1 + 0.06775 * (y2 + y3 + y5 + y6) + (-0.520998) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b29lo j) (b29hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b29lo, b29hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx126 c126_mfunc hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c126_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx126
  linarith [hchain, hpos]

/-- Margin function of conjunct 127 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c127_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.070081) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.014342) * (y 0) + (-0.06775) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.681778

theorem c127_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c127_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.070081) * dihY y1 y2 y3 y4 y5 y6 + (-0.014342) * y1 + (-0.06775) * (y2 + y3 + y5 + y6) + 0.681778 :=
  rfl

/-- Component 127 gate (box 30; chain chain_idx127; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c127_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b30lo j) (b30hi j)) →
      ConcaveOn ℝ (Set.Icc (b30lo i) (b30hi i))
        (fun t => c127_mfunc (Function.update y i t) - K127 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb30 j) → B127 ≤ c127_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 2 + 1 * hplus / 2) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.070081) * dihY y1 y2 y3 y4 y5 y6 + (-0.014342) * y1 + (-0.06775) * (y2 + y3 + y5 + y6) + 0.681778 > 0 := by
  have hpos : (0 : ℝ) <
      B127 - ∑ i, R127 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R127 i = K127 i * (b30hi i - b30lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K127 0 = (0 : ℝ) := by rfl
    have t1 : K127 1 = (0 : ℝ) := by rfl
    have t2 : K127 2 = (0 : ℝ) := by rfl
    have t3 : K127 3 = (0 : ℝ) := by rfl
    have t4 : K127 4 = (0 : ℝ) := by rfl
    have t5 : K127 5 = (0 : ℝ) := by rfl
    have u0 : b30hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b30lo 0 = ((25527/10000) : ℝ) := by rfl
    have u1 : b30hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b30lo 1 = (2 : ℝ) := by rfl
    have u2 : b30hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b30lo 2 = (2 : ℝ) := by rfl
    have u3 : b30hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b30lo 3 = (2 : ℝ) := by rfl
    have u4 : b30hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b30lo 4 = (2 : ℝ) := by rfl
    have u5 : b30hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b30lo 5 = (2 : ℝ) := by rfl
    have eb : B127 = ((291772139870702040537501/720575940379279360000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b30lo j) (b30hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b30lo, b30hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K127 i := by
    intro i; fin_cases i <;> norm_num [K127]
  have hR0 : ∀ i, 0 ≤ R127 i := by
    intro i; fin_cases i <;> norm_num [R127, K127, b30lo, b30hi]
  have hchain := chain_idx127 c127_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c127_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 128 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c128_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.070081) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.014342) * (y 0) + 0.06775 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.402228)

theorem c128_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c128_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.070081) * dihY y1 y2 y3 y4 y5 y6 + (-0.014342) * y1 + 0.06775 * (y2 + y3 + y5 + y6) + (-0.402228) :=
  rfl

/-- Component 128 gate (box 30; chain chain_idx128; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c128_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b30lo j) (b30hi j)) →
      ConcaveOn ℝ (Set.Icc (b30lo i) (b30hi i))
        (fun t => c128_mfunc (Function.update y i t) - K128 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb30 j) → B128 ≤ c128_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 2 + 1 * hplus / 2) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.070081) * dihY y1 y2 y3 y4 y5 y6 + (-0.014342) * y1 + 0.06775 * (y2 + y3 + y5 + y6) + (-0.402228) > 0 := by
  have hpos : (0 : ℝ) <
      B128 - ∑ i, R128 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R128 i = K128 i * (b30hi i - b30lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K128 0 = (0 : ℝ) := by rfl
    have t1 : K128 1 = (0 : ℝ) := by rfl
    have t2 : K128 2 = (0 : ℝ) := by rfl
    have t3 : K128 3 = (0 : ℝ) := by rfl
    have t4 : K128 4 = (0 : ℝ) := by rfl
    have t5 : K128 5 = (0 : ℝ) := by rfl
    have u0 : b30hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b30lo 0 = ((25527/10000) : ℝ) := by rfl
    have u1 : b30hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b30lo 1 = (2 : ℝ) := by rfl
    have u2 : b30hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b30lo 2 = (2 : ℝ) := by rfl
    have u3 : b30hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b30lo 3 = (2 : ℝ) := by rfl
    have u4 : b30hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b30lo 4 = (2 : ℝ) := by rfl
    have u5 : b30hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b30lo 5 = (2 : ℝ) := by rfl
    have eb : B128 = ((288741571694175972094227/720575940379279360000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b30lo j) (b30hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b30lo, b30hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K128 i := by
    intro i; fin_cases i <;> norm_num [K128]
  have hR0 : ∀ i, 0 ≤ R128 i := by
    intro i; fin_cases i <;> norm_num [R128, K128, b30lo, b30hi]
  have hchain := chain_idx128 c128_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c128_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 129 gate (box 30; chain chain_idx129; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c129_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b30lo j) (b30hi j)) →
      ConcaveOn ℝ (Set.Icc (b30lo i) (b30hi i))
        (fun t => c127_mfunc (Function.update y i t) - K129 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb30 j) → B129 ≤ c127_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 2 + 1 * hplus / 2) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.070081) * dihY y1 y2 y3 y4 y5 y6 + (-0.014342) * y1 + (-0.06775) * (y2 + y3 + y5 + y6) + 0.681778 > 0 := by
  have hpos : (0 : ℝ) <
      B129 - ∑ i, R129 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R129 i = K129 i * (b30hi i - b30lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K129 0 = (0 : ℝ) := by rfl
    have t1 : K129 1 = (0 : ℝ) := by rfl
    have t2 : K129 2 = (0 : ℝ) := by rfl
    have t3 : K129 3 = (0 : ℝ) := by rfl
    have t4 : K129 4 = (0 : ℝ) := by rfl
    have t5 : K129 5 = (0 : ℝ) := by rfl
    have u0 : b30hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b30lo 0 = ((25527/10000) : ℝ) := by rfl
    have u1 : b30hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b30lo 1 = (2 : ℝ) := by rfl
    have u2 : b30hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b30lo 2 = (2 : ℝ) := by rfl
    have u3 : b30hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b30lo 3 = (2 : ℝ) := by rfl
    have u4 : b30hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b30lo 4 = (2 : ℝ) := by rfl
    have u5 : b30hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b30lo 5 = (2 : ℝ) := by rfl
    have eb : B129 = ((291772139870702040537501/720575940379279360000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b30lo j) (b30hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b30lo, b30hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K129 i := by
    intro i; fin_cases i <;> norm_num [K129]
  have hR0 : ∀ i, 0 ≤ R129 i := by
    intro i; fin_cases i <;> norm_num [R129, K129, b30lo, b30hi]
  have hchain := chain_idx129 c127_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c127_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 130 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c130_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.074623) + (0.079355 + (-0.023711) + (-0.023711) + (-0.031932)) * y1 + 2 * (0.068595 + (-0.068595)) * y12 + 2 * ((-0.068595) + 0.068595) * y23 + 2 * (0.068595 + (-0.068595)) * y34 + 2 * ((-0.068595) + 0.068595) * y41 + ((-0.608613) + 0.719631 + (-0.37789) + 0.735738) < 0 :=
  ox3q1hLin_130

/-- Margin function of conjunct 131 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c131_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.079355 * (y 0) + 0.068595 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.608613)

theorem c131_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c131_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + 0.079355 * y1 + 0.068595 * (y2 + y3 + y5 + y6) + (-0.608613) :=
  rfl

/-- Component 131 gate (box 31; chain chain_idx131; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c131_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b31lo j) (b31hi j)) →
      ConcaveOn ℝ (Set.Icc (b31lo i) (b31hi i))
        (fun t => c131_mfunc (Function.update y i t) - K131 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb31 j) → B131 ≤ c131_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (h0 + hplus) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + 0.079355 * y1 + 0.068595 * (y2 + y3 + y5 + y6) + (-0.608613) > 0 := by
  have hpos : (0 : ℝ) <
      B131 - ∑ i, R131 i := by
    rw [sumFin6c]
    have e0 : R131 0 = (0 : ℝ) := by rfl
    have e1 : R131 1 = (0 : ℝ) := by rfl
    have e2 : R131 2 = (0 : ℝ) := by rfl
    have e3 : R131 3 = ((63867881678500791/219902325555200000000) : ℝ) := by rfl
    have e4 : R131 4 = (0 : ℝ) := by rfl
    have e5 : R131 5 = (0 : ℝ) := by rfl
    have eb : B131 = ((1667201535459614533087/1441151880758558720000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b31lo j) (b31hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b31lo, b31hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K131 i := by
    intro i; fin_cases i <;> norm_num [K131]
  have hR0 : ∀ i, 0 ≤ R131 i := by
    intro i; fin_cases i <;> norm_num [R131, K131, b31lo, b31hi]
  have hchain := chain_idx131 c131_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c131_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 132 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c132_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.023711) * (y 0) + (-0.068595) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.719631

theorem c132_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c132_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.023711) * y1 + (-0.068595) * (y2 + y3 + y5 + y6) + 0.719631 :=
  rfl

/-- Component 132 gate (box 32; chain chain_idx132; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c132_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b32lo j) (b32hi j)) →
      ConcaveOn ℝ (Set.Icc (b32lo i) (b32hi i))
        (fun t => c132_mfunc (Function.update y i t) - K132 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb32 j) → B132 ≤ c132_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.023711) * y1 + (-0.068595) * (y2 + y3 + y5 + y6) + 0.719631 > 0 := by
  have hpos : (0 : ℝ) <
      B132 - ∑ i, R132 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R132 i = K132 i * (b32hi i - b32lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K132 0 = (0 : ℝ) := by rfl
    have t1 : K132 1 = (0 : ℝ) := by rfl
    have t2 : K132 2 = (0 : ℝ) := by rfl
    have t3 : K132 3 = (0 : ℝ) := by rfl
    have t4 : K132 4 = (0 : ℝ) := by rfl
    have t5 : K132 5 = (0 : ℝ) := by rfl
    have u0 : b32hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b32lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b32hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b32lo 1 = (2 : ℝ) := by rfl
    have u2 : b32hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b32lo 2 = (2 : ℝ) := by rfl
    have u3 : b32hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b32lo 3 = (2 : ℝ) := by rfl
    have u4 : b32hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b32lo 4 = (2 : ℝ) := by rfl
    have u5 : b32hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b32lo 5 = (2 : ℝ) := by rfl
    have eb : B132 = ((836140091848463825143807/720575940379279360000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b32lo j) (b32hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b32lo, b32hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K132 i := by
    intro i; fin_cases i <;> norm_num [K132]
  have hR0 : ∀ i, 0 ≤ R132 i := by
    intro i; fin_cases i <;> norm_num [R132, K132, b32lo, b32hi]
  have hchain := chain_idx132 c132_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c132_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 133 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c133_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.023711) * (y 0) + 0.068595 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.37789)

theorem c133_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c133_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.023711) * y1 + 0.068595 * (y2 + y3 + y5 + y6) + (-0.37789) :=
  rfl

/-- Component 133 gate (box 32; chain chain_idx133; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c133_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b32lo j) (b32hi j)) →
      ConcaveOn ℝ (Set.Icc (b32lo i) (b32hi i))
        (fun t => c133_mfunc (Function.update y i t) - K133 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb32 j) → B133 ≤ c133_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.023711) * y1 + 0.068595 * (y2 + y3 + y5 + y6) + (-0.37789) > 0 := by
  have hpos : (0 : ℝ) <
      B133 - ∑ i, R133 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R133 i = K133 i * (b32hi i - b32lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K133 0 = (0 : ℝ) := by rfl
    have t1 : K133 1 = (0 : ℝ) := by rfl
    have t2 : K133 2 = (0 : ℝ) := by rfl
    have t3 : K133 3 = (0 : ℝ) := by rfl
    have t4 : K133 4 = (0 : ℝ) := by rfl
    have t5 : K133 5 = (0 : ℝ) := by rfl
    have u0 : b32hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b32lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b32hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b32lo 1 = (2 : ℝ) := by rfl
    have u2 : b32hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b32lo 2 = (2 : ℝ) := by rfl
    have u3 : b32hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b32lo 3 = (2 : ℝ) := by rfl
    have u4 : b32hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b32lo 4 = (2 : ℝ) := by rfl
    have u5 : b32hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b32lo 5 = (2 : ℝ) := by rfl
    have eb : B133 = ((16737968422090828369341/14411518807585587200000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b32lo j) (b32hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b32lo, b32hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K133 i := by
    intro i; fin_cases i <;> norm_num [K133]
  have hR0 : ∀ i, 0 ≤ R133 i := by
    intro i; fin_cases i <;> norm_num [R133, K133, b32lo, b32hi]
  have hchain := chain_idx133 c133_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c133_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 134 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c134_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.031932) * (y 0) + (-0.068595) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.735738

theorem c134_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c134_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.031932) * y1 + (-0.068595) * (y2 + y3 + y5 + y6) + 0.735738 :=
  rfl

/-- Component 134 gate (box 33; chain chain_idx134; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c134_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b33lo j) (b33hi j)) →
      ConcaveOn ℝ (Set.Icc (b33lo i) (b33hi i))
        (fun t => c134_mfunc (Function.update y i t) - K134 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb33 j) → B134 ≤ c134_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 4 + 7 / 4) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.031932) * y1 + (-0.068595) * (y2 + y3 + y5 + y6) + 0.735738 > 0 := by
  have hpos : (0 : ℝ) <
      B134 - ∑ i, R134 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R134 i = K134 i * (b33hi i - b33lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K134 0 = (0 : ℝ) := by rfl
    have t1 : K134 1 = (0 : ℝ) := by rfl
    have t2 : K134 2 = (0 : ℝ) := by rfl
    have t3 : K134 3 = (0 : ℝ) := by rfl
    have t4 : K134 4 = (0 : ℝ) := by rfl
    have t5 : K134 5 = (0 : ℝ) := by rfl
    have u0 : b33hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b33lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b33hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b33lo 1 = (2 : ℝ) := by rfl
    have u2 : b33hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b33lo 2 = (2 : ℝ) := by rfl
    have u3 : b33hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b33lo 3 = ((32927/16000) : ℝ) := by rfl
    have u4 : b33hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b33lo 4 = (2 : ℝ) := by rfl
    have u5 : b33hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b33lo 5 = (2 : ℝ) := by rfl
    have eb : B134 = ((33521304402286636518959/28823037615171174400000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b33lo j) (b33hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b33lo, b33hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K134 i := by
    intro i; fin_cases i <;> norm_num [K134]
  have hR0 : ∀ i, 0 ≤ R134 i := by
    intro i; fin_cases i <;> norm_num [R134, K134, b33lo, b33hi]
  have hchain := chain_idx134 c134_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c134_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 135 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c135_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.074623) + (0.019702 + (-0.023711) + (-0.031932) + 0.035942) * y1 + 2 * ((-0.081204) + 0.081204) * y12 + 2 * (0.081204 + (-0.081204)) * y23 + 2 * ((-0.081204) + 0.081204) * y34 + 2 * (0.081204 + (-0.081204)) * y41 + (0.740105 + (-0.47876) + 0.836608 + (-0.629086)) < 0 :=
  ox3q1hLin_135

/-- Margin function of conjunct 136 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c136_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.019702 * (y 0) + (-0.081204) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.740105

theorem c136_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c136_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + 0.019702 * y1 + (-0.081204) * (y2 + y3 + y5 + y6) + 0.740105 :=
  rfl

/-- Component 136 gate (box 31; chain chain_idx136; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c136_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b31lo j) (b31hi j)) →
      ConcaveOn ℝ (Set.Icc (b31lo i) (b31hi i))
        (fun t => c136_mfunc (Function.update y i t) - K136 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb31 j) → B136 ≤ c136_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (h0 + hplus) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + 0.019702 * y1 + (-0.081204) * (y2 + y3 + y5 + y6) + 0.740105 > 0 := by
  have hpos : (0 : ℝ) <
      B136 - ∑ i, R136 i := by
    rw [sumFin6c]
    have e0 : R136 0 = (0 : ℝ) := by rfl
    have e1 : R136 1 = (0 : ℝ) := by rfl
    have e2 : R136 2 = (0 : ℝ) := by rfl
    have e3 : R136 3 = ((63867881678500791/219902325555200000000) : ℝ) := by rfl
    have e4 : R136 4 = (0 : ℝ) := by rfl
    have e5 : R136 5 = (0 : ℝ) := by rfl
    have eb : B136 = ((8339178211435741494619/7205759403792793600000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b31lo j) (b31hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b31lo, b31hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K136 i := by
    intro i; fin_cases i <;> norm_num [K136]
  have hR0 : ∀ i, 0 ≤ R136 i := by
    intro i; fin_cases i <;> norm_num [R136, K136, b31lo, b31hi]
  have hchain := chain_idx136 c136_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c136_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 137 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c137_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.023711) * (y 0) + 0.081204 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.47876)

theorem c137_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c137_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.023711) * y1 + 0.081204 * (y2 + y3 + y5 + y6) + (-0.47876) :=
  rfl

/-- Component 137 gate (box 32; chain chain_idx137; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c137_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b32lo j) (b32hi j)) →
      ConcaveOn ℝ (Set.Icc (b32lo i) (b32hi i))
        (fun t => c137_mfunc (Function.update y i t) - K137 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb32 j) → B137 ≤ c137_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.023711) * y1 + 0.081204 * (y2 + y3 + y5 + y6) + (-0.47876) > 0 := by
  have hpos : (0 : ℝ) <
      B137 - ∑ i, R137 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R137 i = K137 i * (b32hi i - b32lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K137 0 = (0 : ℝ) := by rfl
    have t1 : K137 1 = (0 : ℝ) := by rfl
    have t2 : K137 2 = (0 : ℝ) := by rfl
    have t3 : K137 3 = (0 : ℝ) := by rfl
    have t4 : K137 4 = (0 : ℝ) := by rfl
    have t5 : K137 5 = (0 : ℝ) := by rfl
    have u0 : b32hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b32lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b32hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b32lo 1 = (2 : ℝ) := by rfl
    have u2 : b32hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b32lo 2 = (2 : ℝ) := by rfl
    have u3 : b32hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b32lo 3 = (2 : ℝ) := by rfl
    have u4 : b32hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b32lo 4 = (2 : ℝ) := by rfl
    have u5 : b32hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b32lo 5 = (2 : ℝ) := by rfl
    have eb : B137 = ((16766791459705999543741/14411518807585587200000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b32lo j) (b32hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b32lo, b32hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K137 i := by
    intro i; fin_cases i <;> norm_num [K137]
  have hR0 : ∀ i, 0 ≤ R137 i := by
    intro i; fin_cases i <;> norm_num [R137, K137, b32lo, b32hi]
  have hchain := chain_idx137 c137_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c137_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 138 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c138_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.031932) * (y 0) + (-0.081204) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.836608

theorem c138_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c138_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.031932) * y1 + (-0.081204) * (y2 + y3 + y5 + y6) + 0.836608 :=
  rfl

/-- Component 138 gate (box 33; chain chain_idx138; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c138_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b33lo j) (b33hi j)) →
      ConcaveOn ℝ (Set.Icc (b33lo i) (b33hi i))
        (fun t => c138_mfunc (Function.update y i t) - K138 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb33 j) → B138 ≤ c138_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 4 + 7 / 4) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.031932) * y1 + (-0.081204) * (y2 + y3 + y5 + y6) + 0.836608 > 0 := by
  have hpos : (0 : ℝ) <
      B138 - ∑ i, R138 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R138 i = K138 i * (b33hi i - b33lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K138 0 = (0 : ℝ) := by rfl
    have t1 : K138 1 = (0 : ℝ) := by rfl
    have t2 : K138 2 = (0 : ℝ) := by rfl
    have t3 : K138 3 = (0 : ℝ) := by rfl
    have t4 : K138 4 = (0 : ℝ) := by rfl
    have t5 : K138 5 = (0 : ℝ) := by rfl
    have u0 : b33hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b33lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b33hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b33lo 1 = (2 : ℝ) := by rfl
    have u2 : b33hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b33lo 2 = (2 : ℝ) := by rfl
    have u3 : b33hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b33lo 3 = ((32927/16000) : ℝ) := by rfl
    have u4 : b33hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b33lo 4 = (2 : ℝ) := by rfl
    have u5 : b33hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b33lo 5 = (2 : ℝ) := by rfl
    have eb : B138 = ((4174175383681885475029337/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b33lo j) (b33hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b33lo, b33hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K138 i := by
    intro i; fin_cases i <;> norm_num [K138]
  have hR0 : ∀ i, 0 ≤ R138 i := by
    intro i; fin_cases i <;> norm_num [R138, K138, b33lo, b33hi]
  have hchain := chain_idx138 c138_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c138_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 139 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c139_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.035942 * (y 0) + 0.081204 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.629086)

theorem c139_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c139_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + 0.035942 * y1 + 0.081204 * (y2 + y3 + y5 + y6) + (-0.629086) :=
  rfl

/-- Component 139 gate (box 34; chain chain_idx139; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c139_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b34lo j) (b34hi j)) →
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => c139_mfunc (Function.update y i t) - K139 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B139 ≤ c139_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + 0.035942 * y1 + 0.081204 * (y2 + y3 + y5 + y6) + (-0.629086) > 0 := by
  have hpos : (0 : ℝ) <
      B139 - ∑ i, R139 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R139 i = K139 i * (b34hi i - b34lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K139 0 = (0 : ℝ) := by rfl
    have t1 : K139 1 = (0 : ℝ) := by rfl
    have t2 : K139 2 = (0 : ℝ) := by rfl
    have t3 : K139 3 = (0 : ℝ) := by rfl
    have t4 : K139 4 = (0 : ℝ) := by rfl
    have t5 : K139 5 = (0 : ℝ) := by rfl
    have u0 : b34hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b34lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b34hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b34lo 1 = (2 : ℝ) := by rfl
    have u2 : b34hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b34lo 2 = (2 : ℝ) := by rfl
    have u3 : b34hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b34lo 3 = (2 : ℝ) := by rfl
    have u4 : b34hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b34lo 4 = (2 : ℝ) := by rfl
    have u5 : b34hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b34lo 5 = (2 : ℝ) := by rfl
    have eb : B139 = ((16760450391430661885373/14411518807585587200000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b34lo j) (b34hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b34lo, b34hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K139 i := by
    intro i; fin_cases i <;> norm_num [K139]
  have hR0 : ∀ i, 0 ≤ R139 i := by
    intro i; fin_cases i <;> norm_num [R139, K139, b34lo, b34hi]
  have hchain := chain_idx139 c139_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c139_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 140 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c140_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.074623) + (0.019702 + (-0.031932) + (-0.023711) + 0.035942) * y1 + 2 * ((-0.068595) + 0.068595) * y12 + 2 * (0.068595 + (-0.068595)) * y23 + 2 * ((-0.068595) + 0.068595) * y34 + 2 * (0.068595 + (-0.068595)) * y41 + (0.639237 + (-0.361784) + 0.719631 + (-0.528217)) < 0 :=
  ox3q1hLin_140

/-- Margin function of conjunct 141 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c141_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.019702 * (y 0) + (-0.068595) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.639237

theorem c141_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c141_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + 0.019702 * y1 + (-0.068595) * (y2 + y3 + y5 + y6) + 0.639237 :=
  rfl

/-- Component 141 gate (box 31; chain chain_idx141; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c141_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b31lo j) (b31hi j)) →
      ConcaveOn ℝ (Set.Icc (b31lo i) (b31hi i))
        (fun t => c141_mfunc (Function.update y i t) - K141 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb31 j) → B141 ≤ c141_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (h0 + hplus) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + 0.019702 * y1 + (-0.068595) * (y2 + y3 + y5 + y6) + 0.639237 > 0 := by
  have hpos : (0 : ℝ) <
      B141 - ∑ i, R141 i := by
    rw [sumFin6c]
    have e0 : R141 0 = (0 : ℝ) := by rfl
    have e1 : R141 1 = (0 : ℝ) := by rfl
    have e2 : R141 2 = (0 : ℝ) := by rfl
    have e3 : R141 3 = ((63867881678500791/219902325555200000000) : ℝ) := by rfl
    have e4 : R141 4 = (0 : ℝ) := by rfl
    have e5 : R141 5 = (0 : ℝ) := by rfl
    have eb : B141 = ((8368001249050912669019/7205759403792793600000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b31lo j) (b31hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b31lo, b31hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K141 i := by
    intro i; fin_cases i <;> norm_num [K141]
  have hR0 : ∀ i, 0 ≤ R141 i := by
    intro i; fin_cases i <;> norm_num [R141, K141, b31lo, b31hi]
  have hchain := chain_idx141 c141_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c141_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 142 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c142_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.031932) * (y 0) + 0.068595 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.361784)

theorem c142_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c142_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.031932) * y1 + 0.068595 * (y2 + y3 + y5 + y6) + (-0.361784) :=
  rfl

/-- Component 142 gate (box 33; chain chain_idx142; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c142_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b33lo j) (b33hi j)) →
      ConcaveOn ℝ (Set.Icc (b33lo i) (b33hi i))
        (fun t => c142_mfunc (Function.update y i t) - K142 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb33 j) → B142 ≤ c142_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 4 + 7 / 4) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.031932) * y1 + 0.068595 * (y2 + y3 + y5 + y6) + (-0.361784) > 0 := by
  have hpos : (0 : ℝ) <
      B142 - ∑ i, R142 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R142 i = K142 i * (b33hi i - b33lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K142 0 = (0 : ℝ) := by rfl
    have t1 : K142 1 = (0 : ℝ) := by rfl
    have t2 : K142 2 = (0 : ℝ) := by rfl
    have t3 : K142 3 = (0 : ℝ) := by rfl
    have t4 : K142 4 = (0 : ℝ) := by rfl
    have t5 : K142 5 = (0 : ℝ) := by rfl
    have u0 : b33hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b33lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b33hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b33lo 1 = (2 : ℝ) := by rfl
    have u2 : b33hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b33lo 2 = (2 : ℝ) := by rfl
    have u3 : b33hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b33lo 3 = ((32927/16000) : ℝ) := by rfl
    have u4 : b33hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b33lo 4 = (2 : ℝ) := by rfl
    have u5 : b33hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b33lo 5 = (2 : ℝ) := by rfl
    have eb : B142 = ((33463658327056294170159/28823037615171174400000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b33lo j) (b33hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b33lo, b33hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K142 i := by
    intro i; fin_cases i <;> norm_num [K142]
  have hR0 : ∀ i, 0 ≤ R142 i := by
    intro i; fin_cases i <;> norm_num [R142, K142, b33lo, b33hi]
  have hchain := chain_idx142 c142_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c142_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 143 gate (box 34; chain chain_idx143; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c143_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b34lo j) (b34hi j)) →
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => c132_mfunc (Function.update y i t) - K143 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B143 ≤ c132_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + (-0.023711) * y1 + (-0.068595) * (y2 + y3 + y5 + y6) + 0.719631 > 0 := by
  have hpos : (0 : ℝ) <
      B143 - ∑ i, R143 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R143 i = K143 i * (b34hi i - b34lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K143 0 = (0 : ℝ) := by rfl
    have t1 : K143 1 = (0 : ℝ) := by rfl
    have t2 : K143 2 = (0 : ℝ) := by rfl
    have t3 : K143 3 = (0 : ℝ) := by rfl
    have t4 : K143 4 = (0 : ℝ) := by rfl
    have t5 : K143 5 = (0 : ℝ) := by rfl
    have u0 : b34hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b34lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b34hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b34lo 1 = (2 : ℝ) := by rfl
    have u2 : b34hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b34lo 2 = (2 : ℝ) := by rfl
    have u3 : b34hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b34lo 3 = (2 : ℝ) := by rfl
    have u4 : b34hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b34lo 4 = (2 : ℝ) := by rfl
    have u5 : b34hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b34lo 5 = (2 : ℝ) := by rfl
    have eb : B143 = ((836140091848463825143807/720575940379279360000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b34lo j) (b34hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b34lo, b34hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K143 i := by
    intro i; fin_cases i <;> norm_num [K143]
  have hR0 : ∀ i, 0 ≤ R143 i := by
    intro i; fin_cases i <;> norm_num [R143, K143, b34lo, b34hi]
  have hchain := chain_idx143 c132_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c132_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 144 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c144_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.074623) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.035942 * (y 0) + 0.068595 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.528217)

theorem c144_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c144_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + 0.035942 * y1 + 0.068595 * (y2 + y3 + y5 + y6) + (-0.528217) :=
  rfl

/-- Component 144 gate (box 34; chain chain_idx144; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c144_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b34lo j) (b34hi j)) →
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => c144_mfunc (Function.update y i t) - K144 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B144 ≤ c144_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.074623) * dihY y1 y2 y3 y4 y5 y6 + 0.035942 * y1 + 0.068595 * (y2 + y3 + y5 + y6) + (-0.528217) > 0 := by
  have hpos : (0 : ℝ) <
      B144 - ∑ i, R144 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R144 i = K144 i * (b34hi i - b34lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K144 0 = (0 : ℝ) := by rfl
    have t1 : K144 1 = (0 : ℝ) := by rfl
    have t2 : K144 2 = (0 : ℝ) := by rfl
    have t3 : K144 3 = (0 : ℝ) := by rfl
    have t4 : K144 4 = (0 : ℝ) := by rfl
    have t5 : K144 5 = (0 : ℝ) := by rfl
    have u0 : b34hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b34lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b34hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b34lo 1 = (2 : ℝ) := by rfl
    have u2 : b34hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b34lo 2 = (2 : ℝ) := by rfl
    have u3 : b34hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b34lo 3 = (2 : ℝ) := by rfl
    have u4 : b34hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b34lo 4 = (2 : ℝ) := by rfl
    have u5 : b34hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b34lo 5 = (2 : ℝ) := by rfl
    have eb : B144 = ((16717215835007905123773/14411518807585587200000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b34lo j) (b34hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b34lo, b34hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K144 i := by
    intro i; fin_cases i <;> norm_num [K144]
  have hR0 : ∀ i, 0 ≤ R144 i := by
    intro i; fin_cases i <;> norm_num [R144, K144, b34lo, b34hi]
  have hchain := chain_idx144 c144_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c144_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 145 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c145_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (7 * h0 / 4 + 1 * hplus / 4) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.090009) + (0.04151 + (-0.013837) + (-0.013837) + (-0.013837)) * y1 + 2 * (0.073665 + (-0.073665)) * y12 + 2 * ((-0.073665) + 0.073665) * y23 + 2 * (0.073665 + (-0.073665)) * y34 + 2 * ((-0.073665) + 0.073665) * y41 + ((-0.523458) + 0.755879 + (-0.422755) + 0.755879) < 0 :=
  ox3q1hLin_145

/-- Margin function of conjunct 146 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c146_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.090009) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.04151 * (y 0) + 0.073665 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.523458)

theorem c146_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c146_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.090009) * dihY y1 y2 y3 y4 y5 y6 + 0.04151 * y1 + 0.073665 * (y2 + y3 + y5 + y6) + (-0.523458) :=
  rfl

/-- Component 146 gate (box 35; chain chain_idx146; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c146_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b35lo j) (b35hi j)) →
      ConcaveOn ℝ (Set.Icc (b35lo i) (b35hi i))
        (fun t => c146_mfunc (Function.update y i t) - K146 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb35 j) → B146 ≤ c146_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (7 * h0 / 4 + 1 * hplus / 4) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * h0 / 2 + 3 * hplus / 2) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.090009) * dihY y1 y2 y3 y4 y5 y6 + 0.04151 * y1 + 0.073665 * (y2 + y3 + y5 + y6) + (-0.523458) > 0 := by
  have hpos : (0 : ℝ) <
      B146 - ∑ i, R146 i := by
    rw [sumFin6c]
    have e0 : R146 0 = (0 : ℝ) := by rfl
    have e1 : R146 1 = (0 : ℝ) := by rfl
    have e2 : R146 2 = (0 : ℝ) := by rfl
    have e3 : R146 3 = ((15558089533040421/219902325555200000000) : ℝ) := by rfl
    have e4 : R146 4 = (0 : ℝ) := by rfl
    have e5 : R146 5 = (0 : ℝ) := by rfl
    have eb : B146 = ((44924689928774775587397/144115188075855872000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b35lo j) (b35hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b35lo, b35hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K146 i := by
    intro i; fin_cases i <;> norm_num [K146]
  have hR0 : ∀ i, 0 ≤ R146 i := by
    intro i; fin_cases i <;> norm_num [R146, K146, b35lo, b35hi]
  have hchain := chain_idx146 c146_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c146_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 147 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c147_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.090009) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.013837) * (y 0) + (-0.073665) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.755879

theorem c147_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c147_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.090009) * dihY y1 y2 y3 y4 y5 y6 + (-0.013837) * y1 + (-0.073665) * (y2 + y3 + y5 + y6) + 0.755879 :=
  rfl

/-- Component 147 gate (box 36; chain chain_idx147; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c147_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b36lo j) (b36hi j)) →
      ConcaveOn ℝ (Set.Icc (b36lo i) (b36hi i))
        (fun t => c147_mfunc (Function.update y i t) - K147 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb36 j) → B147 ≤ c147_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (7 * h0 / 4 + 1 * hplus / 4) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.090009) * dihY y1 y2 y3 y4 y5 y6 + (-0.013837) * y1 + (-0.073665) * (y2 + y3 + y5 + y6) + 0.755879 > 0 := by
  have hpos : (0 : ℝ) <
      B147 - ∑ i, R147 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R147 i = K147 i * (b36hi i - b36lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K147 0 = (0 : ℝ) := by rfl
    have t1 : K147 1 = (0 : ℝ) := by rfl
    have t2 : K147 2 = (0 : ℝ) := by rfl
    have t3 : K147 3 = (0 : ℝ) := by rfl
    have t4 : K147 4 = (0 : ℝ) := by rfl
    have t5 : K147 5 = (0 : ℝ) := by rfl
    have u0 : b36hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b36lo 0 = ((50727/20000) : ℝ) := by rfl
    have u1 : b36hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b36lo 1 = (2 : ℝ) := by rfl
    have u2 : b36hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b36lo 2 = (2 : ℝ) := by rfl
    have u3 : b36hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b36lo 3 = (2 : ℝ) := by rfl
    have u4 : b36hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b36lo 4 = (2 : ℝ) := by rfl
    have u5 : b36hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b36lo 5 = (2 : ℝ) := by rfl
    have eb : B147 = ((13597274230923500954187/45035996273704960000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b36lo j) (b36hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b36lo, b36hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K147 i := by
    intro i; fin_cases i <;> norm_num [K147]
  have hR0 : ∀ i, 0 ≤ R147 i := by
    intro i; fin_cases i <;> norm_num [R147, K147, b36lo, b36hi]
  have hchain := chain_idx147 c147_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c147_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 148 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c148_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.090009) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.013837) * (y 0) + 0.073665 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.422755)

theorem c148_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c148_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.090009) * dihY y1 y2 y3 y4 y5 y6 + (-0.013837) * y1 + 0.073665 * (y2 + y3 + y5 + y6) + (-0.422755) :=
  rfl

/-- Component 148 gate (box 36; chain chain_idx148; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c148_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b36lo j) (b36hi j)) →
      ConcaveOn ℝ (Set.Icc (b36lo i) (b36hi i))
        (fun t => c148_mfunc (Function.update y i t) - K148 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb36 j) → B148 ≤ c148_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (7 * h0 / 4 + 1 * hplus / 4) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.090009) * dihY y1 y2 y3 y4 y5 y6 + (-0.013837) * y1 + 0.073665 * (y2 + y3 + y5 + y6) + (-0.422755) > 0 := by
  have hpos : (0 : ℝ) <
      B148 - ∑ i, R148 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R148 i = K148 i * (b36hi i - b36lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K148 0 = (0 : ℝ) := by rfl
    have t1 : K148 1 = (0 : ℝ) := by rfl
    have t2 : K148 2 = (0 : ℝ) := by rfl
    have t3 : K148 3 = (0 : ℝ) := by rfl
    have t4 : K148 4 = (0 : ℝ) := by rfl
    have t5 : K148 5 = (0 : ℝ) := by rfl
    have u0 : b36hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b36lo 0 = ((50727/20000) : ℝ) := by rfl
    have u1 : b36hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b36lo 1 = (2 : ℝ) := by rfl
    have u2 : b36hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b36lo 2 = (2 : ℝ) := by rfl
    have u3 : b36hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b36lo 3 = (2 : ℝ) := by rfl
    have u4 : b36hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b36lo 4 = (2 : ℝ) := by rfl
    have u5 : b36hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b36lo 5 = (2 : ℝ) := by rfl
    have eb : B148 = ((111900521944593733199293/360287970189639680000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b36lo j) (b36hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b36lo, b36hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K148 i := by
    intro i; fin_cases i <;> norm_num [K148]
  have hR0 : ∀ i, 0 ≤ R148 i := by
    intro i; fin_cases i <;> norm_num [R148, K148, b36lo, b36hi]
  have hchain := chain_idx148 c148_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c148_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 149 gate (box 36; chain chain_idx149; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c149_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b36lo j) (b36hi j)) →
      ConcaveOn ℝ (Set.Icc (b36lo i) (b36hi i))
        (fun t => c147_mfunc (Function.update y i t) - K149 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb36 j) → B149 ≤ c147_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (7 * h0 / 4 + 1 * hplus / 4) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.090009) * dihY y1 y2 y3 y4 y5 y6 + (-0.013837) * y1 + (-0.073665) * (y2 + y3 + y5 + y6) + 0.755879 > 0 := by
  have hpos : (0 : ℝ) <
      B149 - ∑ i, R149 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R149 i = K149 i * (b36hi i - b36lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K149 0 = (0 : ℝ) := by rfl
    have t1 : K149 1 = (0 : ℝ) := by rfl
    have t2 : K149 2 = (0 : ℝ) := by rfl
    have t3 : K149 3 = (0 : ℝ) := by rfl
    have t4 : K149 4 = (0 : ℝ) := by rfl
    have t5 : K149 5 = (0 : ℝ) := by rfl
    have u0 : b36hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b36lo 0 = ((50727/20000) : ℝ) := by rfl
    have u1 : b36hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b36lo 1 = (2 : ℝ) := by rfl
    have u2 : b36hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b36lo 2 = (2 : ℝ) := by rfl
    have u3 : b36hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b36lo 3 = (2 : ℝ) := by rfl
    have u4 : b36hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b36lo 4 = (2 : ℝ) := by rfl
    have u5 : b36hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b36lo 5 = (2 : ℝ) := by rfl
    have eb : B149 = ((13597274230923500954187/45035996273704960000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b36lo j) (b36hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b36lo, b36hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K149 i := by
    intro i; fin_cases i <;> norm_num [K149]
  have hR0 : ∀ i, 0 ≤ R149 i := by
    intro i; fin_cases i <;> norm_num [R149, K149, b36lo, b36hi]
  have hchain := chain_idx149 c147_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c147_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 150 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c150_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (7 * h0 / 4 + 1 * hplus / 4) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.17025) + (0.094709 + (-0.021455) + 0.009749 + (-0.021455)) * y1 + 2 * (0.098535 + (-0.098535)) * y12 + 2 * ((-0.098535) + 0.098535) * y23 + 2 * (0.098535 + (-0.098535)) * y34 + 2 * ((-0.098535) + 0.098535) * y41 + ((-0.692034) + 1.087114 + (-0.568591) + 1.087114) < 0 :=
  ox3q1hLin_150

/-- Margin function of conjunct 151 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c151_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.17025) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.094709 * (y 0) + 0.098535 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.692034)

theorem c151_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c151_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.17025) * dihY y1 y2 y3 y4 y5 y6 + 0.094709 * y1 + 0.098535 * (y2 + y3 + y5 + y6) + (-0.692034) :=
  rfl

/-- Component 151 gate (box 37; chain chain_idx151; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c151_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b37lo j) (b37hi j)) →
      ConcaveOn ℝ (Set.Icc (b37lo i) (b37hi i))
        (fun t => c151_mfunc (Function.update y i t) - K151 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb37 j) → B151 ≤ c151_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (7 * h0 / 4 + 1 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * h0 / 2 + 3 * hplus / 2) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.17025) * dihY y1 y2 y3 y4 y5 y6 + 0.094709 * y1 + 0.098535 * (y2 + y3 + y5 + y6) + (-0.692034) > 0 := by
  have hpos : (0 : ℝ) <
      B151 - ∑ i, R151 i := by
    rw [sumFin6c]
    have e0 : R151 0 = (0 : ℝ) := by rfl
    have e1 : R151 1 = (0 : ℝ) := by rfl
    have e2 : R151 2 = (0 : ℝ) := by rfl
    have e3 : R151 3 = ((60555602899863981/879609302220800000000) : ℝ) := by rfl
    have e4 : R151 4 = (0 : ℝ) := by rfl
    have e5 : R151 5 = (0 : ℝ) := by rfl
    have eb : B151 = ((6018825145969899828821/14411518807585587200000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b37lo j) (b37hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b37lo, b37hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K151 i := by
    intro i; fin_cases i <;> norm_num [K151]
  have hR0 : ∀ i, 0 ≤ R151 i := by
    intro i; fin_cases i <;> norm_num [R151, K151, b37lo, b37hi]
  have hchain := chain_idx151 c151_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c151_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 152 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c152_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.17025) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.021455) * (y 0) + (-0.098535) * ((y 1) + (y 2) + (y 4) + (y 5)) + 1.087114

theorem c152_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c152_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.17025) * dihY y1 y2 y3 y4 y5 y6 + (-0.021455) * y1 + (-0.098535) * (y2 + y3 + y5 + y6) + 1.087114 :=
  rfl

/-- Component 152 gate (box 38; chain chain_idx152; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c152_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b38lo j) (b38hi j)) →
      ConcaveOn ℝ (Set.Icc (b38lo i) (b38hi i))
        (fun t => c152_mfunc (Function.update y i t) - K152 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb38 j) → B152 ≤ c152_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (7 * h0 / 4 + 1 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.17025) * dihY y1 y2 y3 y4 y5 y6 + (-0.021455) * y1 + (-0.098535) * (y2 + y3 + y5 + y6) + 1.087114 > 0 := by
  have hpos : (0 : ℝ) <
      B152 - ∑ i, R152 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R152 i = K152 i * (b38hi i - b38lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K152 0 = (0 : ℝ) := by rfl
    have t1 : K152 1 = (0 : ℝ) := by rfl
    have t2 : K152 2 = (0 : ℝ) := by rfl
    have t3 : K152 3 = (0 : ℝ) := by rfl
    have t4 : K152 4 = (0 : ℝ) := by rfl
    have t5 : K152 5 = (0 : ℝ) := by rfl
    have u0 : b38hi 0 = ((50727/20000) : ℝ) := by rfl
    have q0 : b38lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b38hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b38lo 1 = (2 : ℝ) := by rfl
    have u2 : b38hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b38lo 2 = (2 : ℝ) := by rfl
    have u3 : b38hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b38lo 3 = (2 : ℝ) := by rfl
    have u4 : b38hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b38lo 4 = (2 : ℝ) := by rfl
    have u5 : b38hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b38lo 5 = (2 : ℝ) := by rfl
    have eb : B152 = ((9345042883342261834513/22517998136852480000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b38lo j) (b38hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b38lo, b38hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K152 i := by
    intro i; fin_cases i <;> norm_num [K152]
  have hR0 : ∀ i, 0 ≤ R152 i := by
    intro i; fin_cases i <;> norm_num [R152, K152, b38lo, b38hi]
  have hchain := chain_idx152 c152_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c152_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 153 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c153_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.17025) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.009749 * (y 0) + 0.098535 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.568591)

theorem c153_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c153_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.17025) * dihY y1 y2 y3 y4 y5 y6 + 0.009749 * y1 + 0.098535 * (y2 + y3 + y5 + y6) + (-0.568591) :=
  rfl

/-- Component 153 gate (box 38; chain chain_idx153; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c153_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b38lo j) (b38hi j)) →
      ConcaveOn ℝ (Set.Icc (b38lo i) (b38hi i))
        (fun t => c153_mfunc (Function.update y i t) - K153 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb38 j) → B153 ≤ c153_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (7 * h0 / 4 + 1 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.17025) * dihY y1 y2 y3 y4 y5 y6 + 0.009749 * y1 + 0.098535 * (y2 + y3 + y5 + y6) + (-0.568591) > 0 := by
  have hpos : (0 : ℝ) <
      B153 - ∑ i, R153 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R153 i = K153 i * (b38hi i - b38lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K153 0 = (0 : ℝ) := by rfl
    have t1 : K153 1 = (0 : ℝ) := by rfl
    have t2 : K153 2 = (0 : ℝ) := by rfl
    have t3 : K153 3 = (0 : ℝ) := by rfl
    have t4 : K153 4 = (0 : ℝ) := by rfl
    have t5 : K153 5 = (0 : ℝ) := by rfl
    have u0 : b38hi 0 = ((50727/20000) : ℝ) := by rfl
    have q0 : b38lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b38hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b38lo 1 = (2 : ℝ) := by rfl
    have u2 : b38hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b38lo 2 = (2 : ℝ) := by rfl
    have u3 : b38hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b38lo 3 = (2 : ℝ) := by rfl
    have u4 : b38hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b38lo 4 = (2 : ℝ) := by rfl
    have u5 : b38hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b38lo 5 = (2 : ℝ) := by rfl
    have eb : B153 = ((150056327510774085708757/360287970189639680000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b38lo j) (b38hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b38lo, b38hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K153 i := by
    intro i; fin_cases i <;> norm_num [K153]
  have hR0 : ∀ i, 0 ≤ R153 i := by
    intro i; fin_cases i <;> norm_num [R153, K153, b38lo, b38hi]
  have hchain := chain_idx153 c153_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c153_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 154 gate (box 38; chain chain_idx154; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c154_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b38lo j) (b38hi j)) →
      ConcaveOn ℝ (Set.Icc (b38lo i) (b38hi i))
        (fun t => c152_mfunc (Function.update y i t) - K154 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb38 j) → B154 ≤ c152_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (7 * h0 / 4 + 1 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.17025) * dihY y1 y2 y3 y4 y5 y6 + (-0.021455) * y1 + (-0.098535) * (y2 + y3 + y5 + y6) + 1.087114 > 0 := by
  have hpos : (0 : ℝ) <
      B154 - ∑ i, R154 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R154 i = K154 i * (b38hi i - b38lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K154 0 = (0 : ℝ) := by rfl
    have t1 : K154 1 = (0 : ℝ) := by rfl
    have t2 : K154 2 = (0 : ℝ) := by rfl
    have t3 : K154 3 = (0 : ℝ) := by rfl
    have t4 : K154 4 = (0 : ℝ) := by rfl
    have t5 : K154 5 = (0 : ℝ) := by rfl
    have u0 : b38hi 0 = ((50727/20000) : ℝ) := by rfl
    have q0 : b38lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b38hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b38lo 1 = (2 : ℝ) := by rfl
    have u2 : b38hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b38lo 2 = (2 : ℝ) := by rfl
    have u3 : b38hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b38lo 3 = (2 : ℝ) := by rfl
    have u4 : b38hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b38lo 4 = (2 : ℝ) := by rfl
    have u5 : b38hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b38lo 5 = (2 : ℝ) := by rfl
    have eb : B154 = ((9345042883342261834513/22517998136852480000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b38lo j) (b38hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b38lo, b38hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K154 i := by
    intro i; fin_cases i <;> norm_num [K154]
  have hR0 : ∀ i, 0 ≤ R154 i := by
    intro i; fin_cases i <;> norm_num [R154, K154, b38lo, b38hi]
  have hchain := chain_idx154 c152_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c152_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 155 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c155_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.172166) + (0.09973 + 0.014169 + (-0.017353) + 0.014169) * y1 + 2 * ((-0.099785) + 0.099785) * y12 + 2 * (0.099785 + (-0.099785)) * y23 + 2 * ((-0.099785) + 0.099785) * y34 + 2 * (0.099785 + (-0.099785)) * y41 + (0.882284 + (-0.586728) + 1.0903 + (-0.586728)) < 0 :=
  ox3q1hLin_155

/-- Margin function of conjunct 156 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c156_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.172166) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.09973 * (y 0) + (-0.099785) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.882284

theorem c156_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c156_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.172166) * dihY y1 y2 y3 y4 y5 y6 + 0.09973 * y1 + (-0.099785) * (y2 + y3 + y5 + y6) + 0.882284 :=
  rfl

/-- Component 156 gate (box 39; chain chain_idx156; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c156_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b39lo j) (b39hi j)) →
      ConcaveOn ℝ (Set.Icc (b39lo i) (b39hi i))
        (fun t => c156_mfunc (Function.update y i t) - K156 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb39 j) → B156 ≤ c156_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (h0 + hplus) ≤ y4 → y4 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.172166) * dihY y1 y2 y3 y4 y5 y6 + 0.09973 * y1 + (-0.099785) * (y2 + y3 + y5 + y6) + 0.882284 > 0 := by
  have hpos : (0 : ℝ) <
      B156 - ∑ i, R156 i := by
    rw [sumFin6c]
    have e0 : R156 0 = (0 : ℝ) := by rfl
    have e1 : R156 1 = (0 : ℝ) := by rfl
    have e2 : R156 2 = (0 : ℝ) := by rfl
    have e3 : R156 3 = ((61435212202024893/879609302220800000000) : ℝ) := by rfl
    have e4 : R156 4 = (0 : ℝ) := by rfl
    have e5 : R156 5 = (0 : ℝ) := by rfl
    have eb : B156 = ((1858386252607482077749/2882303761517117440000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b39lo j) (b39hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b39lo, b39hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K156 i := by
    intro i; fin_cases i <;> norm_num [K156]
  have hR0 : ∀ i, 0 ≤ R156 i := by
    intro i; fin_cases i <;> norm_num [R156, K156, b39lo, b39hi]
  have hchain := chain_idx156 c156_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c156_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 157 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c157_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.172166) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.014169 * (y 0) + 0.099785 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.586728)

theorem c157_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c157_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.172166) * dihY y1 y2 y3 y4 y5 y6 + 0.014169 * y1 + 0.099785 * (y2 + y3 + y5 + y6) + (-0.586728) :=
  rfl

/-- Component 157 gate (box 34; chain chain_idx157; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c157_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b34lo j) (b34hi j)) →
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => c157_mfunc (Function.update y i t) - K157 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B157 ≤ c157_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.172166) * dihY y1 y2 y3 y4 y5 y6 + 0.014169 * y1 + 0.099785 * (y2 + y3 + y5 + y6) + (-0.586728) > 0 := by
  have hpos : (0 : ℝ) <
      B157 - ∑ i, R157 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R157 i = K157 i * (b34hi i - b34lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K157 0 = (0 : ℝ) := by rfl
    have t1 : K157 1 = (0 : ℝ) := by rfl
    have t2 : K157 2 = (0 : ℝ) := by rfl
    have t3 : K157 3 = (0 : ℝ) := by rfl
    have t4 : K157 4 = (0 : ℝ) := by rfl
    have t5 : K157 5 = (0 : ℝ) := by rfl
    have u0 : b34hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b34lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b34hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b34lo 1 = (2 : ℝ) := by rfl
    have u2 : b34hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b34lo 2 = (2 : ℝ) := by rfl
    have u3 : b34hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b34lo 3 = (2 : ℝ) := by rfl
    have u4 : b34hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b34lo 4 = (2 : ℝ) := by rfl
    have u5 : b34hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b34lo 5 = (2 : ℝ) := by rfl
    have eb : B157 = ((2316670520307222761309/3602879701896396800000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b34lo j) (b34hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b34lo, b34hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K157 i := by
    intro i; fin_cases i <;> norm_num [K157]
  have hR0 : ∀ i, 0 ≤ R157 i := by
    intro i; fin_cases i <;> norm_num [R157, K157, b34lo, b34hi]
  have hchain := chain_idx157 c157_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c157_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 158 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c158_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.172166) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.017353) * (y 0) + (-0.099785) * ((y 1) + (y 2) + (y 4) + (y 5)) + 1.0903

theorem c158_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c158_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.172166) * dihY y1 y2 y3 y4 y5 y6 + (-0.017353) * y1 + (-0.099785) * (y2 + y3 + y5 + y6) + 1.0903 :=
  rfl

/-- Component 158 gate (box 34; chain chain_idx158; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c158_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b34lo j) (b34hi j)) →
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => c158_mfunc (Function.update y i t) - K158 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B158 ≤ c158_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.172166) * dihY y1 y2 y3 y4 y5 y6 + (-0.017353) * y1 + (-0.099785) * (y2 + y3 + y5 + y6) + 1.0903 > 0 := by
  have hpos : (0 : ℝ) <
      B158 - ∑ i, R158 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R158 i = K158 i * (b34hi i - b34lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K158 0 = (0 : ℝ) := by rfl
    have t1 : K158 1 = (0 : ℝ) := by rfl
    have t2 : K158 2 = (0 : ℝ) := by rfl
    have t3 : K158 3 = (0 : ℝ) := by rfl
    have t4 : K158 4 = (0 : ℝ) := by rfl
    have t5 : K158 5 = (0 : ℝ) := by rfl
    have u0 : b34hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b34lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b34hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b34lo 1 = (2 : ℝ) := by rfl
    have u2 : b34hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b34lo 2 = (2 : ℝ) := by rfl
    have u3 : b34hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b34lo 3 = (2 : ℝ) := by rfl
    have u4 : b34hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b34lo 4 = (2 : ℝ) := by rfl
    have u5 : b34hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b34lo 5 = (2 : ℝ) := by rfl
    have eb : B158 = ((46306031555053243689003/72057594037927936000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b34lo j) (b34hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b34lo, b34hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K158 i := by
    intro i; fin_cases i <;> norm_num [K158]
  have hR0 : ∀ i, 0 ≤ R158 i := by
    intro i; fin_cases i <;> norm_num [R158, K158, b34lo, b34hi]
  have hchain := chain_idx158 c158_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c158_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 159 gate (box 34; chain chain_idx159; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c159_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b34lo j) (b34hi j)) →
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => c157_mfunc (Function.update y i t) - K159 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B159 ≤ c157_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.172166) * dihY y1 y2 y3 y4 y5 y6 + 0.014169 * y1 + 0.099785 * (y2 + y3 + y5 + y6) + (-0.586728) > 0 := by
  have hpos : (0 : ℝ) <
      B159 - ∑ i, R159 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R159 i = K159 i * (b34hi i - b34lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K159 0 = (0 : ℝ) := by rfl
    have t1 : K159 1 = (0 : ℝ) := by rfl
    have t2 : K159 2 = (0 : ℝ) := by rfl
    have t3 : K159 3 = (0 : ℝ) := by rfl
    have t4 : K159 4 = (0 : ℝ) := by rfl
    have t5 : K159 5 = (0 : ℝ) := by rfl
    have u0 : b34hi 0 = ((25527/10000) : ℝ) := by rfl
    have q0 : b34lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b34hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b34lo 1 = (2 : ℝ) := by rfl
    have u2 : b34hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b34lo 2 = (2 : ℝ) := by rfl
    have u3 : b34hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b34lo 3 = (2 : ℝ) := by rfl
    have u4 : b34hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b34lo 4 = (2 : ℝ) := by rfl
    have u5 : b34hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b34lo 5 = (2 : ℝ) := by rfl
    have eb : B159 = ((2316670520307222761309/3602879701896396800000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b34lo j) (b34hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b34lo, b34hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K159 i := by
    intro i; fin_cases i <;> norm_num [K159]
  have hR0 : ∀ i, 0 ≤ R159 i := by
    intro i; fin_cases i <;> norm_num [R159, K159, b34lo, b34hi]
  have hchain := chain_idx159 c157_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c157_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 160 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c160_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.084789) + (0.039845 + (-0.013282) + (-0.013282) + (-0.013282)) * y1 + 2 * ((-0.071708) + (-0.071708)) * y12 + 2 * ((-0.071708) + (-0.071708)) * y23 + 2 * ((-0.071708) + 0.071708) * y34 + 2 * (0.071708 + (-0.071708)) * y41 + (0.632521 + 0.731624 + 0.731624 + (-0.415701)) < 0 :=
  ox3q1hLin_160

/-- Margin function of conjunct 161 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c161_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.084789) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.039845 * (y 0) + (-0.071708) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.632521

theorem c161_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c161_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.084789) * dihY y1 y2 y3 y4 y5 y6 + 0.039845 * y1 + (-0.071708) * (y2 + y3 + y5 + y6) + 0.632521 :=
  rfl

/-- Component 161 gate (box 40; S4.5 split-grid chain
`chain_split_idx161`, split factors per SPLIT_PLAN route `Y4PATCH:y4`, m_min =
2; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c161_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit161 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b40lo j) (b40hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit161 i k) (gsplit161 i (k + 1)))
        (fun t => c161_mfunc (Function.update y i t) - K161 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split161 j) → B161 ≤ c161_mfunc v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (h0 + hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.084789) * dihY y1 y2 y3 y4 y5 y6 + 0.039845 * y1 + (-0.071708) * (y2 + y3 + y5 + y6) + 0.632521 > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b40lo j) (b40hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b40lo, b40hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx161 c161_mfunc hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c161_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx161
  linarith [hchain, hpos]

/-- Margin function of conjunct 162 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c162_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.084789) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.013282) * (y 0) + (-0.071708) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.731624

theorem c162_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c162_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.084789) * dihY y1 y2 y3 y4 y5 y6 + (-0.013282) * y1 + (-0.071708) * (y2 + y3 + y5 + y6) + 0.731624 :=
  rfl

/-- Component 162 gate (box 28; chain chain_idx162; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c162_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b28lo j) (b28hi j)) →
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => c162_mfunc (Function.update y i t) - K162 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B162 ≤ c162_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.084789) * dihY y1 y2 y3 y4 y5 y6 + (-0.013282) * y1 + (-0.071708) * (y2 + y3 + y5 + y6) + 0.731624 > 0 := by
  have hpos : (0 : ℝ) <
      B162 - ∑ i, R162 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R162 i = K162 i * (b28hi i - b28lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K162 0 = (0 : ℝ) := by rfl
    have t1 : K162 1 = (0 : ℝ) := by rfl
    have t2 : K162 2 = (0 : ℝ) := by rfl
    have t3 : K162 3 = (0 : ℝ) := by rfl
    have t4 : K162 4 = (0 : ℝ) := by rfl
    have t5 : K162 5 = (0 : ℝ) := by rfl
    have u0 : b28hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b28lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b28hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b28lo 1 = (2 : ℝ) := by rfl
    have u2 : b28hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b28lo 2 = (2 : ℝ) := by rfl
    have u3 : b28hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b28lo 3 = (2 : ℝ) := by rfl
    have u4 : b28hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b28lo 4 = (2 : ℝ) := by rfl
    have u5 : b28hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b28lo 5 = (2 : ℝ) := by rfl
    have eb : B162 = ((1109777245112725649005449/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b28lo j) (b28hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b28lo, b28hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K162 i := by
    intro i; fin_cases i <;> norm_num [K162]
  have hR0 : ∀ i, 0 ≤ R162 i := by
    intro i; fin_cases i <;> norm_num [R162, K162, b28lo, b28hi]
  have hchain := chain_idx162 c162_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c162_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 163 gate (box 28; chain chain_idx163; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c163_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b28lo j) (b28hi j)) →
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => c162_mfunc (Function.update y i t) - K163 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B163 ≤ c162_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.084789) * dihY y1 y2 y3 y4 y5 y6 + (-0.013282) * y1 + (-0.071708) * (y2 + y3 + y5 + y6) + 0.731624 > 0 := by
  have hpos : (0 : ℝ) <
      B163 - ∑ i, R163 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R163 i = K163 i * (b28hi i - b28lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K163 0 = (0 : ℝ) := by rfl
    have t1 : K163 1 = (0 : ℝ) := by rfl
    have t2 : K163 2 = (0 : ℝ) := by rfl
    have t3 : K163 3 = (0 : ℝ) := by rfl
    have t4 : K163 4 = (0 : ℝ) := by rfl
    have t5 : K163 5 = (0 : ℝ) := by rfl
    have u0 : b28hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b28lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b28hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b28lo 1 = (2 : ℝ) := by rfl
    have u2 : b28hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b28lo 2 = (2 : ℝ) := by rfl
    have u3 : b28hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b28lo 3 = (2 : ℝ) := by rfl
    have u4 : b28hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b28lo 4 = (2 : ℝ) := by rfl
    have u5 : b28hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b28lo 5 = (2 : ℝ) := by rfl
    have eb : B163 = ((1109777245112725649005449/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b28lo j) (b28hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b28lo, b28hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K163 i := by
    intro i; fin_cases i <;> norm_num [K163]
  have hR0 : ∀ i, 0 ≤ R163 i := by
    intro i; fin_cases i <;> norm_num [R163, K163, b28lo, b28hi]
  have hchain := chain_idx163 c162_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c162_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 164 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c164_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.084789) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.013282) * (y 0) + 0.071708 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.415701)

theorem c164_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c164_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.084789) * dihY y1 y2 y3 y4 y5 y6 + (-0.013282) * y1 + 0.071708 * (y2 + y3 + y5 + y6) + (-0.415701) :=
  rfl

/-- Component 164 gate (box 28; chain chain_idx164; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c164_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b28lo j) (b28hi j)) →
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => c164_mfunc (Function.update y i t) - K164 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B164 ≤ c164_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.084789) * dihY y1 y2 y3 y4 y5 y6 + (-0.013282) * y1 + 0.071708 * (y2 + y3 + y5 + y6) + (-0.415701) > 0 := by
  have hpos : (0 : ℝ) <
      B164 - ∑ i, R164 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R164 i = K164 i * (b28hi i - b28lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K164 0 = (0 : ℝ) := by rfl
    have t1 : K164 1 = (0 : ℝ) := by rfl
    have t2 : K164 2 = (0 : ℝ) := by rfl
    have t3 : K164 3 = (0 : ℝ) := by rfl
    have t4 : K164 4 = (0 : ℝ) := by rfl
    have t5 : K164 5 = (0 : ℝ) := by rfl
    have u0 : b28hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b28lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b28hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b28lo 1 = (2 : ℝ) := by rfl
    have u2 : b28hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b28lo 2 = (2 : ℝ) := by rfl
    have u3 : b28hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b28lo 3 = (2 : ℝ) := by rfl
    have u4 : b28hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b28lo 4 = (2 : ℝ) := by rfl
    have u5 : b28hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b28lo 5 = (2 : ℝ) := by rfl
    have eb : B164 = ((225698054889908608616367/720575940379279360000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b28lo j) (b28hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b28lo, b28hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K164 i := by
    intro i; fin_cases i <;> norm_num [K164]
  have hR0 : ∀ i, 0 ≤ R164 i := by
    intro i; fin_cases i <;> norm_num [R164, K164, b28lo, b28hi]
  have hchain := chain_idx164 c164_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c164_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 165 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c165_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.065103 + ((-0.052337) + 0.23854 + (-0.073933) + (-0.11227)) * y1 + 2 * ((-0.02292) + 0.02292) * y12 + 2 * (0.02292 + (-0.02292)) * y23 + 2 * ((-0.02292) + 0.02292) * y34 + 2 * (0.02292 + (-0.02292)) * y41 + (0.191326 + (-0.867278) + 0.286871 + (-0.019974)) < 0 :=
  ox3q1hLin_165

/-- Margin function of conjunct 166 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c166_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.052337) * (y 0) + (-0.02292) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.191326

theorem c166_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c166_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.052337) * y1 + (-0.02292) * (y2 + y3 + y5 + y6) + 0.191326 :=
  rfl

/-- Component 166 gate (box 41; chain chain_idx166; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c166_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b41lo j) (b41hi j)) →
      ConcaveOn ℝ (Set.Icc (b41lo i) (b41hi i))
        (fun t => c166_mfunc (Function.update y i t) - K166 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb41 j) → B166 ≤ c166_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.052337) * y1 + (-0.02292) * (y2 + y3 + y5 + y6) + 0.191326 > 0 := by
  have hpos : (0 : ℝ) <
      B166 - ∑ i, R166 i := by
    rw [sumFin6c]
    have e0 : R166 0 = (0 : ℝ) := by rfl
    have e1 : R166 1 = (0 : ℝ) := by rfl
    have e2 : R166 2 = (0 : ℝ) := by rfl
    have e3 : R166 3 = ((3910962860003709/17592186044416000000) : ℝ) := by rfl
    have e4 : R166 4 = (0 : ℝ) := by rfl
    have e5 : R166 5 = (0 : ℝ) := by rfl
    have eb : B166 = ((78283134124333786320869/28823037615171174400000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b41lo j) (b41hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b41lo, b41hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K166 i := by
    intro i; fin_cases i <;> norm_num [K166]
  have hR0 : ∀ i, 0 ≤ R166 i := by
    intro i; fin_cases i <;> norm_num [R166, K166, b41lo, b41hi]
  have hchain := chain_idx166 c166_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c166_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 167 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c167_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.23854 * (y 0) + 0.02292 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.867278)

theorem c167_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c167_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.23854 * y1 + 0.02292 * (y2 + y3 + y5 + y6) + (-0.867278) :=
  rfl

/-- Component 167 gate (box 6; chain chain_idx167; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c167_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b6lo j) (b6hi j)) →
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => c167_mfunc (Function.update y i t) - K167 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B167 ≤ c167_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.23854 * y1 + 0.02292 * (y2 + y3 + y5 + y6) + (-0.867278) > 0 := by
  have hpos : (0 : ℝ) <
      B167 - ∑ i, R167 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R167 i = K167 i * (b6hi i - b6lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K167 0 = (0 : ℝ) := by rfl
    have t1 : K167 1 = (0 : ℝ) := by rfl
    have t2 : K167 2 = (0 : ℝ) := by rfl
    have t3 : K167 3 = (0 : ℝ) := by rfl
    have t4 : K167 4 = (0 : ℝ) := by rfl
    have t5 : K167 5 = (0 : ℝ) := by rfl
    have u0 : b6hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b6lo 0 = (63/25 : ℝ) := by rfl
    have u1 : b6hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b6lo 1 = (2 : ℝ) := by rfl
    have u2 : b6hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b6lo 2 = (2 : ℝ) := by rfl
    have u3 : b6hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : b6lo 3 = (2 : ℝ) := by rfl
    have u4 : b6hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b6lo 4 = (2 : ℝ) := by rfl
    have u5 : b6hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b6lo 5 = (2 : ℝ) := by rfl
    have eb : B167 = ((3924208341292139308301/1441151880758558720000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b6lo j) (b6hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b6lo, b6hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K167 i := by
    intro i; fin_cases i <;> norm_num [K167]
  have hR0 : ∀ i, 0 ≤ R167 i := by
    intro i; fin_cases i <;> norm_num [R167, K167, b6lo, b6hi]
  have hchain := chain_idx167 c167_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c167_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 168 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c168_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.073933) * (y 0) + (-0.02292) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.286871

theorem c168_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c168_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.073933) * y1 + (-0.02292) * (y2 + y3 + y5 + y6) + 0.286871 :=
  rfl

/-- Component 168 gate (box 6; chain chain_idx168; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c168_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b6lo j) (b6hi j)) →
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => c168_mfunc (Function.update y i t) - K168 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B168 ≤ c168_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.073933) * y1 + (-0.02292) * (y2 + y3 + y5 + y6) + 0.286871 > 0 := by
  have hpos : (0 : ℝ) <
      B168 - ∑ i, R168 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R168 i = K168 i * (b6hi i - b6lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K168 0 = (0 : ℝ) := by rfl
    have t1 : K168 1 = (0 : ℝ) := by rfl
    have t2 : K168 2 = (0 : ℝ) := by rfl
    have t3 : K168 3 = (0 : ℝ) := by rfl
    have t4 : K168 4 = (0 : ℝ) := by rfl
    have t5 : K168 5 = (0 : ℝ) := by rfl
    have u0 : b6hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b6lo 0 = (63/25 : ℝ) := by rfl
    have u1 : b6hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b6lo 1 = (2 : ℝ) := by rfl
    have u2 : b6hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b6lo 2 = (2 : ℝ) := by rfl
    have u3 : b6hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : b6lo 3 = (2 : ℝ) := by rfl
    have u4 : b6hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b6lo 4 = (2 : ℝ) := by rfl
    have u5 : b6hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b6lo 5 = (2 : ℝ) := by rfl
    have eb : B168 = ((489545085008139688213137/180143985094819840000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b6lo j) (b6hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b6lo, b6hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K168 i := by
    intro i; fin_cases i <;> norm_num [K168]
  have hR0 : ∀ i, 0 ≤ R168 i := by
    intro i; fin_cases i <;> norm_num [R168, K168, b6lo, b6hi]
  have hchain := chain_idx168 c168_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c168_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 169 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c169_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.11227) * (y 0) + 0.02292 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.019974)

theorem c169_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c169_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.11227) * y1 + 0.02292 * (y2 + y3 + y5 + y6) + (-0.019974) :=
  rfl

/-- Component 169 gate (box 7; chain chain_idx169; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c169_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b7lo j) (b7hi j)) →
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => c169_mfunc (Function.update y i t) - K169 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B169 ≤ c169_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.11227) * y1 + 0.02292 * (y2 + y3 + y5 + y6) + (-0.019974) > 0 := by
  have hpos : (0 : ℝ) <
      B169 - ∑ i, R169 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R169 i = K169 i * (b7hi i - b7lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K169 0 = (0 : ℝ) := by rfl
    have t1 : K169 1 = (0 : ℝ) := by rfl
    have t2 : K169 2 = (0 : ℝ) := by rfl
    have t3 : K169 3 = (0 : ℝ) := by rfl
    have t4 : K169 4 = (0 : ℝ) := by rfl
    have t5 : K169 5 = (0 : ℝ) := by rfl
    have u0 : b7hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b7lo 0 = (63/25 : ℝ) := by rfl
    have u1 : b7hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b7lo 1 = (2 : ℝ) := by rfl
    have u2 : b7hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b7lo 2 = (2 : ℝ) := by rfl
    have u3 : b7hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : b7lo 3 = (8927/4000 : ℝ) := by rfl
    have u4 : b7hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b7lo 4 = (2 : ℝ) := by rfl
    have u5 : b7hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b7lo 5 = (2 : ℝ) := by rfl
    have eb : B169 = ((98043888100283974166987/36028797018963968000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b7lo j) (b7hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b7lo, b7hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K169 i := by
    intro i; fin_cases i <;> norm_num [K169]
  have hR0 : ∀ i, 0 ≤ R169 i := by
    intro i; fin_cases i <;> norm_num [R169, K169, b7lo, b7hi]
  have hchain := chain_idx169 c169_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c169_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 170 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c170_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.065103 + ((-0.052337) + 0.23854 + (-0.11227) + (-0.073933)) * y1 + 2 * (0.02292 + (-0.02292)) * y12 + 2 * ((-0.02292) + 0.02292) * y23 + 2 * (0.02292 + (-0.02292)) * y34 + 2 * ((-0.02292) + 0.02292) * y41 + ((-0.17539) + (-0.500562) + (-0.019974) + 0.286871) < 0 :=
  ox3q1hLin_170

/-- Margin function of conjunct 171 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c171_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.052337) * (y 0) + 0.02292 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.17539)

theorem c171_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c171_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.052337) * y1 + 0.02292 * (y2 + y3 + y5 + y6) + (-0.17539) :=
  rfl

/-- Component 171 gate (box 41; chain chain_idx171; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c171_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b41lo j) (b41hi j)) →
      ConcaveOn ℝ (Set.Icc (b41lo i) (b41hi i))
        (fun t => c171_mfunc (Function.update y i t) - K171 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb41 j) → B171 ≤ c171_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.052337) * y1 + 0.02292 * (y2 + y3 + y5 + y6) + (-0.17539) > 0 := by
  have hpos : (0 : ℝ) <
      B171 - ∑ i, R171 i := by
    rw [sumFin6c]
    have e0 : R171 0 = (0 : ℝ) := by rfl
    have e1 : R171 1 = (0 : ℝ) := by rfl
    have e2 : R171 2 = (0 : ℝ) := by rfl
    have e3 : R171 3 = ((3910962860003709/17592186044416000000) : ℝ) := by rfl
    have e4 : R171 4 = (0 : ℝ) := by rfl
    have e5 : R171 5 = (0 : ℝ) := by rfl
    have eb : B171 = ((78398426274794471018469/28823037615171174400000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b41lo j) (b41hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b41lo, b41hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K171 i := by
    intro i; fin_cases i <;> norm_num [K171]
  have hR0 : ∀ i, 0 ≤ R171 i := by
    intro i; fin_cases i <;> norm_num [R171, K171, b41lo, b41hi]
  have hchain := chain_idx171 c171_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c171_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 172 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c172_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.23854 * (y 0) + (-0.02292) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.500562)

theorem c172_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c172_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.23854 * y1 + (-0.02292) * (y2 + y3 + y5 + y6) + (-0.500562) :=
  rfl

/-- Component 172 gate (box 6; chain chain_idx172; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c172_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b6lo j) (b6hi j)) →
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => c172_mfunc (Function.update y i t) - K172 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B172 ≤ c172_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.23854 * y1 + (-0.02292) * (y2 + y3 + y5 + y6) + (-0.500562) > 0 := by
  have hpos : (0 : ℝ) <
      B172 - ∑ i, R172 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R172 i = K172 i * (b6hi i - b6lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K172 0 = (0 : ℝ) := by rfl
    have t1 : K172 1 = (0 : ℝ) := by rfl
    have t2 : K172 2 = (0 : ℝ) := by rfl
    have t3 : K172 3 = (0 : ℝ) := by rfl
    have t4 : K172 4 = (0 : ℝ) := by rfl
    have t5 : K172 5 = (0 : ℝ) := by rfl
    have u0 : b6hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b6lo 0 = (63/25 : ℝ) := by rfl
    have u1 : b6hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b6lo 1 = (2 : ℝ) := by rfl
    have u2 : b6hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b6lo 2 = (2 : ℝ) := by rfl
    have u3 : b6hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : b6lo 3 = (2 : ℝ) := by rfl
    have u4 : b6hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b6lo 4 = (2 : ℝ) := by rfl
    have u5 : b6hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b6lo 5 = (2 : ℝ) := by rfl
    have eb : B172 = ((3918443733769105073421/1441151880758558720000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b6lo j) (b6hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b6lo, b6hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K172 i := by
    intro i; fin_cases i <;> norm_num [K172]
  have hR0 : ∀ i, 0 ≤ R172 i := by
    intro i; fin_cases i <;> norm_num [R172, K172, b6lo, b6hi]
  have hchain := chain_idx172 c172_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c172_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 173 gate (box 7; chain chain_idx173; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c173_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b7lo j) (b7hi j)) →
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => c169_mfunc (Function.update y i t) - K173 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B173 ≤ c169_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.11227) * y1 + 0.02292 * (y2 + y3 + y5 + y6) + (-0.019974) > 0 := by
  have hpos : (0 : ℝ) <
      B173 - ∑ i, R173 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R173 i = K173 i * (b7hi i - b7lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K173 0 = (0 : ℝ) := by rfl
    have t1 : K173 1 = (0 : ℝ) := by rfl
    have t2 : K173 2 = (0 : ℝ) := by rfl
    have t3 : K173 3 = (0 : ℝ) := by rfl
    have t4 : K173 4 = (0 : ℝ) := by rfl
    have t5 : K173 5 = (0 : ℝ) := by rfl
    have u0 : b7hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b7lo 0 = (63/25 : ℝ) := by rfl
    have u1 : b7hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b7lo 1 = (2 : ℝ) := by rfl
    have u2 : b7hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b7lo 2 = (2 : ℝ) := by rfl
    have u3 : b7hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : b7lo 3 = (8927/4000 : ℝ) := by rfl
    have u4 : b7hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b7lo 4 = (2 : ℝ) := by rfl
    have u5 : b7hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b7lo 5 = (2 : ℝ) := by rfl
    have eb : B173 = ((98043888100283974166987/36028797018963968000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b7lo j) (b7hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b7lo, b7hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K173 i := by
    intro i; fin_cases i <;> norm_num [K173]
  have hR0 : ∀ i, 0 ≤ R173 i := by
    intro i; fin_cases i <;> norm_num [R173, K173, b7lo, b7hi]
  have hchain := chain_idx173 c169_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c169_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 174 gate (box 8; chain chain_idx174; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c174_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b8lo j) (b8hi j)) →
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => c168_mfunc (Function.update y i t) - K174 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B174 ≤ c168_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.073933) * y1 + (-0.02292) * (y2 + y3 + y5 + y6) + 0.286871 > 0 := by
  have hpos : (0 : ℝ) <
      B174 - ∑ i, R174 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R174 i = K174 i * (b8hi i - b8lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K174 0 = (0 : ℝ) := by rfl
    have t1 : K174 1 = (0 : ℝ) := by rfl
    have t2 : K174 2 = (0 : ℝ) := by rfl
    have t3 : K174 3 = (0 : ℝ) := by rfl
    have t4 : K174 4 = (0 : ℝ) := by rfl
    have t5 : K174 5 = (0 : ℝ) := by rfl
    have u0 : b8hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b8lo 0 = (63/25 : ℝ) := by rfl
    have u1 : b8hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b8lo 1 = (2 : ℝ) := by rfl
    have u2 : b8hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b8lo 2 = (2 : ℝ) := by rfl
    have u3 : b8hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : b8lo 3 = (2 : ℝ) := by rfl
    have u4 : b8hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b8lo 4 = (2 : ℝ) := by rfl
    have u5 : b8hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b8lo 5 = (2 : ℝ) := by rfl
    have eb : B174 = ((489545085008139688213137/180143985094819840000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b8lo j) (b8hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b8lo, b8hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K174 i := by
    intro i; fin_cases i <;> norm_num [K174]
  have hR0 : ∀ i, 0 ≤ R174 i := by
    intro i; fin_cases i <;> norm_num [R174, K174, b8lo, b8hi]
  have hchain := chain_idx174 c168_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c168_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 175 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c175_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.065103 + ((-0.052337) + (-0.11227) + 0.23854 + (-0.073933)) * y1 + 2 * (0.02292 + (-0.02292)) * y12 + 2 * ((-0.02292) + 0.02292) * y23 + 2 * (0.02292 + (-0.02292)) * y34 + 2 * ((-0.02292) + 0.02292) * y41 + ((-0.175391) + 0.346743 + (-0.867278) + 0.286871) < 0 :=
  ox3q1hLin_175

/-- Margin function of conjunct 176 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c176_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.052337) * (y 0) + 0.02292 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.175391)

theorem c176_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c176_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.052337) * y1 + 0.02292 * (y2 + y3 + y5 + y6) + (-0.175391) :=
  rfl

/-- Component 176 gate (box 41; chain chain_idx176; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c176_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b41lo j) (b41hi j)) →
      ConcaveOn ℝ (Set.Icc (b41lo i) (b41hi i))
        (fun t => c176_mfunc (Function.update y i t) - K176 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb41 j) → B176 ≤ c176_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.052337) * y1 + 0.02292 * (y2 + y3 + y5 + y6) + (-0.175391) > 0 := by
  have hpos : (0 : ℝ) <
      B176 - ∑ i, R176 i := by
    rw [sumFin6c]
    have e0 : R176 0 = (0 : ℝ) := by rfl
    have e1 : R176 1 = (0 : ℝ) := by rfl
    have e2 : R176 2 = (0 : ℝ) := by rfl
    have e3 : R176 3 = ((3910962860003709/17592186044416000000) : ℝ) := by rfl
    have e4 : R176 4 = (0 : ℝ) := by rfl
    have e5 : R176 5 = (0 : ℝ) := by rfl
    have eb : B176 = ((78369603237179299844069/28823037615171174400000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b41lo j) (b41hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b41lo, b41hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K176 i := by
    intro i; fin_cases i <;> norm_num [K176]
  have hR0 : ∀ i, 0 ≤ R176 i := by
    intro i; fin_cases i <;> norm_num [R176, K176, b41lo, b41hi]
  have hchain := chain_idx176 c176_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c176_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 177 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c177_mfunc (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.11227) * (y 0) + (-0.02292) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.346743

theorem c177_mfunc_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c177_mfunc ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.11227) * y1 + (-0.02292) * (y2 + y3 + y5 + y6) + 0.346743 :=
  rfl

/-- Component 177 gate (box 7; chain chain_idx177; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c177_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b7lo j) (b7hi j)) →
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => c177_mfunc (Function.update y i t) - K177 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B177 ≤ c177_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.11227) * y1 + (-0.02292) * (y2 + y3 + y5 + y6) + 0.346743 > 0 := by
  have hpos : (0 : ℝ) <
      B177 - ∑ i, R177 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R177 i = K177 i * (b7hi i - b7lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K177 0 = (0 : ℝ) := by rfl
    have t1 : K177 1 = (0 : ℝ) := by rfl
    have t2 : K177 2 = (0 : ℝ) := by rfl
    have t3 : K177 3 = (0 : ℝ) := by rfl
    have t4 : K177 4 = (0 : ℝ) := by rfl
    have t5 : K177 5 = (0 : ℝ) := by rfl
    have u0 : b7hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b7lo 0 = (63/25 : ℝ) := by rfl
    have u1 : b7hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b7lo 1 = (2 : ℝ) := by rfl
    have u2 : b7hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b7lo 2 = (2 : ℝ) := by rfl
    have u3 : b7hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : b7lo 3 = (8927/4000 : ℝ) := by rfl
    have u4 : b7hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b7lo 4 = (2 : ℝ) := by rfl
    have u5 : b7hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b7lo 5 = (2 : ℝ) := by rfl
    have eb : B177 = ((97935801709227082262987/36028797018963968000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b7lo j) (b7hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b7lo, b7hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K177 i := by
    intro i; fin_cases i <;> norm_num [K177]
  have hR0 : ∀ i, 0 ≤ R177 i := by
    intro i; fin_cases i <;> norm_num [R177, K177, b7lo, b7hi]
  have hchain := chain_idx177 c177_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c177_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 178 gate (box 8; chain chain_idx178; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c178_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b8lo j) (b8hi j)) →
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => c167_mfunc (Function.update y i t) - K178 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B178 ≤ c167_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.23854 * y1 + 0.02292 * (y2 + y3 + y5 + y6) + (-0.867278) > 0 := by
  have hpos : (0 : ℝ) <
      B178 - ∑ i, R178 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R178 i = K178 i * (b8hi i - b8lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K178 0 = (0 : ℝ) := by rfl
    have t1 : K178 1 = (0 : ℝ) := by rfl
    have t2 : K178 2 = (0 : ℝ) := by rfl
    have t3 : K178 3 = (0 : ℝ) := by rfl
    have t4 : K178 4 = (0 : ℝ) := by rfl
    have t5 : K178 5 = (0 : ℝ) := by rfl
    have u0 : b8hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b8lo 0 = (63/25 : ℝ) := by rfl
    have u1 : b8hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b8lo 1 = (2 : ℝ) := by rfl
    have u2 : b8hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b8lo 2 = (2 : ℝ) := by rfl
    have u3 : b8hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : b8lo 3 = (2 : ℝ) := by rfl
    have u4 : b8hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b8lo 4 = (2 : ℝ) := by rfl
    have u5 : b8hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b8lo 5 = (2 : ℝ) := by rfl
    have eb : B178 = ((3924208341292139308301/1441151880758558720000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b8lo j) (b8hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b8lo, b8hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K178 i := by
    intro i; fin_cases i <;> norm_num [K178]
  have hR0 : ∀ i, 0 ≤ R178 i := by
    intro i; fin_cases i <;> norm_num [R178, K178, b8lo, b8hi]
  have hchain := chain_idx178 c167_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c167_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 179 gate (box 8; chain chain_idx179; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c179_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b8lo j) (b8hi j)) →
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => c168_mfunc (Function.update y i t) - K179 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B179 ≤ c168_mfunc v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.073933) * y1 + (-0.02292) * (y2 + y3 + y5 + y6) + 0.286871 > 0 := by
  have hpos : (0 : ℝ) <
      B179 - ∑ i, R179 i := by
    rw [sumFin6c]
    have ev : ∀ i : Fin 6, R179 i = K179 i * (b8hi i - b8lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K179 0 = (0 : ℝ) := by rfl
    have t1 : K179 1 = (0 : ℝ) := by rfl
    have t2 : K179 2 = (0 : ℝ) := by rfl
    have t3 : K179 3 = (0 : ℝ) := by rfl
    have t4 : K179 4 = (0 : ℝ) := by rfl
    have t5 : K179 5 = (0 : ℝ) := by rfl
    have u0 : b8hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b8lo 0 = (63/25 : ℝ) := by rfl
    have u1 : b8hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b8lo 1 = (2 : ℝ) := by rfl
    have u2 : b8hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b8lo 2 = (2 : ℝ) := by rfl
    have u3 : b8hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : b8lo 3 = (2 : ℝ) := by rfl
    have u4 : b8hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b8lo 4 = (2 : ℝ) := by rfl
    have u5 : b8hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b8lo 5 = (2 : ℝ) := by rfl
    have eb : B179 = ((489545085008139688213137/180143985094819840000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b8lo j) (b8hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b8lo, b8hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K179 i := by
    intro i; fin_cases i <;> norm_num [K179]
  have hR0 : ∀ i, 0 ≤ R179 i := by
    intro i; fin_cases i <;> norm_num [R179, K179, b8lo, b8hi]
  have hchain := chain_idx179 c168_mfunc hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c168_mfunc_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-! ### Axiom audit -/

#print axioms c120_gate

#print axioms c121_gate

#print axioms c122_gate

#print axioms c123_gate

#print axioms c124_gate

#print axioms c125_gate

#print axioms c126_gate

#print axioms c127_gate

#print axioms c128_gate

#print axioms c129_gate

#print axioms c130_gate

#print axioms c131_gate

#print axioms c132_gate

#print axioms c133_gate

#print axioms c134_gate

#print axioms c135_gate

#print axioms c136_gate

#print axioms c137_gate

#print axioms c138_gate

#print axioms c139_gate

#print axioms c140_gate

#print axioms c141_gate

#print axioms c142_gate

#print axioms c143_gate

#print axioms c144_gate

#print axioms c145_gate

#print axioms c146_gate

#print axioms c147_gate

#print axioms c148_gate

#print axioms c149_gate

#print axioms c150_gate

#print axioms c151_gate

#print axioms c152_gate

#print axioms c153_gate

#print axioms c154_gate

#print axioms c155_gate

#print axioms c156_gate

#print axioms c157_gate

#print axioms c158_gate

#print axioms c159_gate

#print axioms c160_gate

#print axioms c161_gate

#print axioms c162_gate

#print axioms c163_gate

#print axioms c164_gate

#print axioms c165_gate

#print axioms c166_gate

#print axioms c167_gate

#print axioms c168_gate

#print axioms c169_gate

#print axioms c170_gate

#print axioms c171_gate

#print axioms c172_gate

#print axioms c173_gate

#print axioms c174_gate

#print axioms c175_gate

#print axioms c176_gate

#print axioms c177_gate

#print axioms c178_gate

#print axioms c179_gate

end Kepler.Text
