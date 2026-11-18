/-
Ox3q1hGateBatch: S4 per-conjunct gates, components 0-59 (of 230; LIN = idx ≡ 0 mod 5).
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
import Kepler.Text.Ox3q1hChainSplit1
import Kepler.Text.Ox3q1hChainSplitKit

open Set Filter Topology

namespace Kepler.Text

/-- Fin-6 sum as explicit addition (Mathlib Fin.sum_univ_six alias for reuse). -/
theorem sumFin6a (f : Fin 6 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_six]

/-- Component 0 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c0_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.129913 + ((-0.060416) + 0.01764 + 0.045166 + 0.021777) * y1 + 2 * (0.002372 + (-0.002372)) * y12 + 2 * ((-0.002372) + 0.002372) * y23 + 2 * (0.002372 + (-0.002372)) * y34 + 2 * ((-0.002372) + 0.002372) * y41 + ((-0.113134) + (-0.198777) + (-0.306092) + (-0.259166)) < 0 :=
  ox3q1hLin_000

/-- Margin function of conjunct 1 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c1_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.060416) * (y 0) + 0.002372 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.113134)

theorem c1_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c1_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.060416) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-0.113134) :=
  rfl

/-- Component 1 gate (box 0; S4.5 split-grid chain
`chain_split_idx1`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
2; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c1_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit1 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit1 i k) (gsplit1 i (k + 1)))
        (fun t => c1_mfuna (Function.update y i t) - K1 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split1 j) → B1 ≤ c1_mfuna v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.060416) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-0.113134) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box0lo j) (box0hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box0lo, box0hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx1 c1_mfuna hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c1_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx1
  linarith [hchain, hpos]

/-- Margin function of conjunct 2 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c2_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.01764 * (y 0) + (-0.002372) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.198777)

theorem c2_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c2_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.01764 * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + (-0.198777) :=
  rfl

/-- Component 2 gate (box 1; chain chain_idx2; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c2_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box1lo j) (box1hi j)) →
      ConcaveOn ℝ (Set.Icc (box1lo i) (box1hi i))
        (fun t => c2_mfuna (Function.update y i t) - K2 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox1 j) → B2 ≤ c2_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.01764 * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + (-0.198777) > 0 := by
  have hpos : (0 : ℝ) <
      B2 - ∑ i, R2 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R2 i = K2 i * (box1hi i - box1lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K2 0 = (0 : ℝ) := by rfl
    have t1 : K2 1 = (0 : ℝ) := by rfl
    have t2 : K2 2 = (0 : ℝ) := by rfl
    have t3 : K2 3 = (0 : ℝ) := by rfl
    have t4 : K2 4 = (0 : ℝ) := by rfl
    have t5 : K2 5 = (0 : ℝ) := by rfl
    have u0 : box1hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box1lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box1hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box1lo 1 = (2 : ℝ) := by rfl
    have u2 : box1hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box1lo 2 = (2 : ℝ) := by rfl
    have u3 : box1hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : box1lo 3 = (2 : ℝ) := by rfl
    have u4 : box1hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box1lo 4 = (2 : ℝ) := by rfl
    have u5 : box1hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box1lo 5 = (2 : ℝ) := by rfl
    have eb : B2 = ((10405151898277464728772583/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box1lo j) (box1hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box1lo, box1hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K2 i := by
    intro i; fin_cases i <;> norm_num [K2]
  have hR0 : ∀ i, 0 ≤ R2 i := by
    intro i; fin_cases i <;> norm_num [R2, K2, box1lo, box1hi]
  have hchain := chain_idx2 c2_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c2_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 3 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c3_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.045166 * (y 0) + 0.002372 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.306092)

theorem c3_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c3_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.045166 * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-0.306092) :=
  rfl

/-- Component 3 gate (box 1; chain chain_idx3; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c3_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box1lo j) (box1hi j)) →
      ConcaveOn ℝ (Set.Icc (box1lo i) (box1hi i))
        (fun t => c3_mfuna (Function.update y i t) - K3 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox1 j) → B3 ≤ c3_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.045166 * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-0.306092) > 0 := by
  have hpos : (0 : ℝ) <
      B3 - ∑ i, R3 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R3 i = K3 i * (box1hi i - box1lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K3 0 = (0 : ℝ) := by rfl
    have t1 : K3 1 = (0 : ℝ) := by rfl
    have t2 : K3 2 = (0 : ℝ) := by rfl
    have t3 : K3 3 = (0 : ℝ) := by rfl
    have t4 : K3 4 = (0 : ℝ) := by rfl
    have t5 : K3 5 = (0 : ℝ) := by rfl
    have u0 : box1hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box1lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box1hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box1lo 1 = (2 : ℝ) := by rfl
    have u2 : box1hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box1lo 2 = (2 : ℝ) := by rfl
    have u3 : box1hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : box1lo 3 = (2 : ℝ) := by rfl
    have u4 : box1hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box1lo 4 = (2 : ℝ) := by rfl
    have u5 : box1hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box1lo 5 = (2 : ℝ) := by rfl
    have eb : B3 = ((416741359716083491744677/144115188075855872000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box1lo j) (box1hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box1lo, box1hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K3 i := by
    intro i; fin_cases i <;> norm_num [K3]
  have hR0 : ∀ i, 0 ≤ R3 i := by
    intro i; fin_cases i <;> norm_num [R3, K3, box1lo, box1hi]
  have hchain := chain_idx3 c3_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c3_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 4 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c4_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.021777 * (y 0) + (-0.002372) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.259166)

theorem c4_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c4_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.021777 * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + (-0.259166) :=
  rfl

/-- Component 4 gate (box 2; chain chain_idx4; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c4_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box2lo j) (box2hi j)) →
      ConcaveOn ℝ (Set.Icc (box2lo i) (box2hi i))
        (fun t => c4_mfuna (Function.update y i t) - K4 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox2 j) → B4 ≤ c4_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.021777 * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + (-0.259166) > 0 := by
  have hpos : (0 : ℝ) <
      B4 - ∑ i, R4 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R4 i = K4 i * (box2hi i - box2lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K4 0 = (0 : ℝ) := by rfl
    have t1 : K4 1 = (0 : ℝ) := by rfl
    have t2 : K4 2 = (0 : ℝ) := by rfl
    have t3 : K4 3 = (0 : ℝ) := by rfl
    have t4 : K4 4 = (0 : ℝ) := by rfl
    have t5 : K4 5 = (0 : ℝ) := by rfl
    have u0 : box2hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box2lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box2hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box2lo 1 = (2 : ℝ) := by rfl
    have u2 : box2hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box2lo 2 = (2 : ℝ) := by rfl
    have u3 : box2hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : box2lo 3 = (8927/4000 : ℝ) := by rfl
    have u4 : box2hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box2lo 4 = (2 : ℝ) := by rfl
    have u5 : box2hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box2lo 5 = (2 : ℝ) := by rfl
    have eb : B4 = ((416434827219847400616519/144115188075855872000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box2lo j) (box2hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box2lo, box2hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K4 i := by
    intro i; fin_cases i <;> norm_num [K4]
  have hR0 : ∀ i, 0 ≤ R4 i := by
    intro i; fin_cases i <;> norm_num [R4, K4, box2lo, box2hi]
  have hchain := chain_idx4 c4_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c4_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 5 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c5_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.129699 + ((-0.060316) + 0.019214 + 0.021887 + 0.019214) * y1 + 2 * (0.002264 + (-0.002264)) * y12 + 2 * ((-0.002264) + 0.002264) * y23 + 2 * (0.002264 + (-0.002264)) * y34 + 2 * ((-0.002264) + 0.002264) * y41 + ((-0.112116) + (-0.203309) + (-0.29619) + (-0.203309)) < 0 :=
  ox3q1hLin_005

/-- Margin function of conjunct 6 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c6_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.129699 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.060316) * (y 0) + 0.002264 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.112116)

theorem c6_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c6_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.129699 * dihY y1 y2 y3 y4 y5 y6 + (-0.060316) * y1 + 0.002264 * (y2 + y3 + y5 + y6) + (-0.112116) :=
  rfl

/-- Component 6 gate (box 0; S4.5 split-grid chain
`chain_split_idx6`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
2; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c6_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit6 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit6 i k) (gsplit6 i (k + 1)))
        (fun t => c6_mfuna (Function.update y i t) - K6 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split6 j) → B6 ≤ c6_mfuna v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.129699 * dihY y1 y2 y3 y4 y5 y6 + (-0.060316) * y1 + 0.002264 * (y2 + y3 + y5 + y6) + (-0.112116) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box0lo j) (box0hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box0lo, box0hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx6 c6_mfuna hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c6_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx6
  linarith [hchain, hpos]

/-- Margin function of conjunct 7 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c7_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129699 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.019214 * (y 0) + (-0.002264) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.203309)

theorem c7_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c7_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129699 * dihY y1 y2 y3 y4 y5 y6 + 0.019214 * y1 + (-0.002264) * (y2 + y3 + y5 + y6) + (-0.203309) :=
  rfl

/-- Component 7 gate (box 1; chain chain_idx7; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c7_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box1lo j) (box1hi j)) →
      ConcaveOn ℝ (Set.Icc (box1lo i) (box1hi i))
        (fun t => c7_mfuna (Function.update y i t) - K7 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox1 j) → B7 ≤ c7_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129699 * dihY y1 y2 y3 y4 y5 y6 + 0.019214 * y1 + (-0.002264) * (y2 + y3 + y5 + y6) + (-0.203309) > 0 := by
  have hpos : (0 : ℝ) <
      B7 - ∑ i, R7 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R7 i = K7 i * (box1hi i - box1lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K7 0 = (0 : ℝ) := by rfl
    have t1 : K7 1 = (0 : ℝ) := by rfl
    have t2 : K7 2 = (0 : ℝ) := by rfl
    have t3 : K7 3 = (0 : ℝ) := by rfl
    have t4 : K7 4 = (0 : ℝ) := by rfl
    have t5 : K7 5 = (0 : ℝ) := by rfl
    have u0 : box1hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box1lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box1hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box1lo 1 = (2 : ℝ) := by rfl
    have u2 : box1hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box1lo 2 = (2 : ℝ) := by rfl
    have u3 : box1hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : box1lo 3 = (2 : ℝ) := by rfl
    have u4 : box1hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box1lo 4 = (2 : ℝ) := by rfl
    have u5 : box1hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box1lo 5 = (2 : ℝ) := by rfl
    have eb : B7 = ((10402790728516950184241021/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box1lo j) (box1hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box1lo, box1hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K7 i := by
    intro i; fin_cases i <;> norm_num [K7]
  have hR0 : ∀ i, 0 ≤ R7 i := by
    intro i; fin_cases i <;> norm_num [R7, K7, box1lo, box1hi]
  have hchain := chain_idx7 c7_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c7_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 8 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c8_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129699 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.021887 * (y 0) + 0.002264 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.29619)

theorem c8_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c8_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129699 * dihY y1 y2 y3 y4 y5 y6 + 0.021887 * y1 + 0.002264 * (y2 + y3 + y5 + y6) + (-0.29619) :=
  rfl

/-- Component 8 gate (box 2; chain chain_idx8; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c8_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box2lo j) (box2hi j)) →
      ConcaveOn ℝ (Set.Icc (box2lo i) (box2hi i))
        (fun t => c8_mfuna (Function.update y i t) - K8 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox2 j) → B8 ≤ c8_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129699 * dihY y1 y2 y3 y4 y5 y6 + 0.021887 * y1 + 0.002264 * (y2 + y3 + y5 + y6) + (-0.29619) > 0 := by
  have hpos : (0 : ℝ) <
      B8 - ∑ i, R8 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R8 i = K8 i * (box2hi i - box2lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K8 0 = (0 : ℝ) := by rfl
    have t1 : K8 1 = (0 : ℝ) := by rfl
    have t2 : K8 2 = (0 : ℝ) := by rfl
    have t3 : K8 3 = (0 : ℝ) := by rfl
    have t4 : K8 4 = (0 : ℝ) := by rfl
    have t5 : K8 5 = (0 : ℝ) := by rfl
    have u0 : box2hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box2lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box2hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box2lo 1 = (2 : ℝ) := by rfl
    have u2 : box2hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box2lo 2 = (2 : ℝ) := by rfl
    have u3 : box2hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : box2lo 3 = (8927/4000 : ℝ) := by rfl
    have u4 : box2hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box2lo 4 = (2 : ℝ) := by rfl
    have u5 : box2hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box2lo 5 = (2 : ℝ) := by rfl
    have eb : B8 = ((416172938701507665516189/144115188075855872000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box2lo j) (box2hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box2lo, box2hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K8 i := by
    intro i; fin_cases i <;> norm_num [K8]
  have hR0 : ∀ i, 0 ≤ R8 i := by
    intro i; fin_cases i <;> norm_num [R8, K8, box2lo, box2hi]
  have hchain := chain_idx8 c8_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c8_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 9 gate (box 3; chain chain_idx9; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c9_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => c7_mfuna (Function.update y i t) - K9 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B9 ≤ c7_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129699 * dihY y1 y2 y3 y4 y5 y6 + 0.019214 * y1 + (-0.002264) * (y2 + y3 + y5 + y6) + (-0.203309) > 0 := by
  have hpos : (0 : ℝ) <
      B9 - ∑ i, R9 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R9 i = K9 i * (box3hi i - box3lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K9 0 = (0 : ℝ) := by rfl
    have t1 : K9 1 = (0 : ℝ) := by rfl
    have t2 : K9 2 = (0 : ℝ) := by rfl
    have t3 : K9 3 = (0 : ℝ) := by rfl
    have t4 : K9 4 = (0 : ℝ) := by rfl
    have t5 : K9 5 = (0 : ℝ) := by rfl
    have u0 : box3hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box3lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box3hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box3lo 1 = (2 : ℝ) := by rfl
    have u2 : box3hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box3lo 2 = (2 : ℝ) := by rfl
    have u3 : box3hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : box3lo 3 = (2 : ℝ) := by rfl
    have u4 : box3hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box3lo 4 = (2 : ℝ) := by rfl
    have u5 : box3hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box3lo 5 = (2 : ℝ) := by rfl
    have eb : B9 = ((10402790728516950184241021/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box3lo j) (box3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box3lo, box3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K9 i := by
    intro i; fin_cases i <;> norm_num [K9]
  have hR0 : ∀ i, 0 ≤ R9 i := by
    intro i; fin_cases i <;> norm_num [R9, K9, box3lo, box3hi]
  have hchain := chain_idx9 c7_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c7_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 10 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c10_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.129913 + ((-0.060416) + 0.021777 + 0.045166 + 0.01764) * y1 + 2 * (0.002372 + (-0.002372)) * y12 + 2 * ((-0.002372) + 0.002372) * y23 + 2 * (0.002372 + (-0.002372)) * y34 + 2 * ((-0.002372) + 0.002372) * y41 + ((-0.113134) + (-0.259166) + (-0.306092) + (-0.198777)) < 0 :=
  ox3q1hLin_010

/-- Component 11 gate (box 0; S4.5 split-grid chain
`chain_split_idx11`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
2; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c11_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit11 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit11 i k) (gsplit11 i (k + 1)))
        (fun t => c1_mfuna (Function.update y i t) - K11 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split11 j) → B11 ≤ c1_mfuna v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.060416) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-0.113134) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box0lo j) (box0hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box0lo, box0hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx11 c1_mfuna hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c1_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx11
  linarith [hchain, hpos]

/-- Component 12 gate (box 2; chain chain_idx12; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c12_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box2lo j) (box2hi j)) →
      ConcaveOn ℝ (Set.Icc (box2lo i) (box2hi i))
        (fun t => c4_mfuna (Function.update y i t) - K12 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox2 j) → B12 ≤ c4_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.021777 * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + (-0.259166) > 0 := by
  have hpos : (0 : ℝ) <
      B12 - ∑ i, R12 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R12 i = K12 i * (box2hi i - box2lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K12 0 = (0 : ℝ) := by rfl
    have t1 : K12 1 = (0 : ℝ) := by rfl
    have t2 : K12 2 = (0 : ℝ) := by rfl
    have t3 : K12 3 = (0 : ℝ) := by rfl
    have t4 : K12 4 = (0 : ℝ) := by rfl
    have t5 : K12 5 = (0 : ℝ) := by rfl
    have u0 : box2hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box2lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box2hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box2lo 1 = (2 : ℝ) := by rfl
    have u2 : box2hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box2lo 2 = (2 : ℝ) := by rfl
    have u3 : box2hi 3 = (15397/6250 : ℝ) := by rfl
    have q3 : box2lo 3 = (8927/4000 : ℝ) := by rfl
    have u4 : box2hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box2lo 4 = (2 : ℝ) := by rfl
    have u5 : box2hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box2lo 5 = (2 : ℝ) := by rfl
    have eb : B12 = ((416434827219847400616519/144115188075855872000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box2lo j) (box2hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box2lo, box2hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K12 i := by
    intro i; fin_cases i <;> norm_num [K12]
  have hR0 : ∀ i, 0 ≤ R12 i := by
    intro i; fin_cases i <;> norm_num [R12, K12, box2lo, box2hi]
  have hchain := chain_idx12 c4_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c4_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 13 gate (box 3; chain chain_idx13; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c13_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => c3_mfuna (Function.update y i t) - K13 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B13 ≤ c3_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.045166 * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-0.306092) > 0 := by
  have hpos : (0 : ℝ) <
      B13 - ∑ i, R13 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R13 i = K13 i * (box3hi i - box3lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K13 0 = (0 : ℝ) := by rfl
    have t1 : K13 1 = (0 : ℝ) := by rfl
    have t2 : K13 2 = (0 : ℝ) := by rfl
    have t3 : K13 3 = (0 : ℝ) := by rfl
    have t4 : K13 4 = (0 : ℝ) := by rfl
    have t5 : K13 5 = (0 : ℝ) := by rfl
    have u0 : box3hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box3lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box3hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box3lo 1 = (2 : ℝ) := by rfl
    have u2 : box3hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box3lo 2 = (2 : ℝ) := by rfl
    have u3 : box3hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : box3lo 3 = (2 : ℝ) := by rfl
    have u4 : box3hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box3lo 4 = (2 : ℝ) := by rfl
    have u5 : box3hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box3lo 5 = (2 : ℝ) := by rfl
    have eb : B13 = ((416741359716083491744677/144115188075855872000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box3lo j) (box3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box3lo, box3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K13 i := by
    intro i; fin_cases i <;> norm_num [K13]
  have hR0 : ∀ i, 0 ≤ R13 i := by
    intro i; fin_cases i <;> norm_num [R13, K13, box3lo, box3hi]
  have hchain := chain_idx13 c3_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c3_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 14 gate (box 3; chain chain_idx14; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c14_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => c2_mfuna (Function.update y i t) - K14 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B14 ≤ c2_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.01764 * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + (-0.198777) > 0 := by
  have hpos : (0 : ℝ) <
      B14 - ∑ i, R14 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R14 i = K14 i * (box3hi i - box3lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K14 0 = (0 : ℝ) := by rfl
    have t1 : K14 1 = (0 : ℝ) := by rfl
    have t2 : K14 2 = (0 : ℝ) := by rfl
    have t3 : K14 3 = (0 : ℝ) := by rfl
    have t4 : K14 4 = (0 : ℝ) := by rfl
    have t5 : K14 5 = (0 : ℝ) := by rfl
    have u0 : box3hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box3lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box3hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box3lo 1 = (2 : ℝ) := by rfl
    have u2 : box3hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box3lo 2 = (2 : ℝ) := by rfl
    have u3 : box3hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : box3lo 3 = (2 : ℝ) := by rfl
    have u4 : box3hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box3lo 4 = (2 : ℝ) := by rfl
    have u5 : box3hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box3lo 5 = (2 : ℝ) := by rfl
    have eb : B14 = ((10405151898277464728772583/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box3lo j) (box3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box3lo, box3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K14 i := by
    intro i; fin_cases i <;> norm_num [K14]
  have hR0 : ∀ i, 0 ≤ R14 i := by
    intro i; fin_cases i <;> norm_num [R14, K14, box3lo, box3hi]
  have hchain := chain_idx14 c2_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c2_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 15 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c15_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.114872) + (0.133539 + 0.148605 + 0.08743 + 0.148605) * y1 + 2 * ((-0.080919) + 0.080919) * y12 + 2 * (0.080919 + (-0.080919)) * y23 + 2 * ((-0.080919) + 0.080919) * y34 + 2 * (0.080919 + (-0.080919)) * y41 + (0.532524 + (-0.855148) + 0.593722 + (-0.855148)) < 0 :=
  ox3q1hLin_015

/-- Margin function of conjunct 16 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c16_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.114872) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.133539 * (y 0) + (-0.080919) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.532524

theorem c16_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c16_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.133539 * y1 + (-0.080919) * (y2 + y3 + y5 + y6) + 0.532524 :=
  rfl

/-- Component 16 gate (box 0; S4.5 split-grid chain
`chain_split_idx16`, split factors per SPLIT_PLAN route `Y4PATCH:y4`, m_min =
3; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c16_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit16 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit16 i k) (gsplit16 i (k + 1)))
        (fun t => c16_mfuna (Function.update y i t) - K16 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split16 j) → B16 ≤ c16_mfuna v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.133539 * y1 + (-0.080919) * (y2 + y3 + y5 + y6) + 0.532524 > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box0lo j) (box0hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box0lo, box0hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx16 c16_mfuna hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c16_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx16
  linarith [hchain, hpos]

/-- Margin function of conjunct 17 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c17_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.114872) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.148605 * (y 0) + 0.080919 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.855148)

theorem c17_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c17_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.148605 * y1 + 0.080919 * (y2 + y3 + y5 + y6) + (-0.855148) :=
  rfl

/-- Component 17 gate (box 3; chain chain_idx17; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c17_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => c17_mfuna (Function.update y i t) - K17 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B17 ≤ c17_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.148605 * y1 + 0.080919 * (y2 + y3 + y5 + y6) + (-0.855148) > 0 := by
  have hpos : (0 : ℝ) <
      B17 - ∑ i, R17 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R17 i = K17 i * (box3hi i - box3lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K17 0 = (0 : ℝ) := by rfl
    have t1 : K17 1 = (0 : ℝ) := by rfl
    have t2 : K17 2 = (0 : ℝ) := by rfl
    have t3 : K17 3 = (0 : ℝ) := by rfl
    have t4 : K17 4 = (0 : ℝ) := by rfl
    have t5 : K17 5 = (0 : ℝ) := by rfl
    have u0 : box3hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box3lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box3hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box3lo 1 = (2 : ℝ) := by rfl
    have u2 : box3hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box3lo 2 = (2 : ℝ) := by rfl
    have u3 : box3hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : box3lo 3 = (2 : ℝ) := by rfl
    have u4 : box3hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box3lo 4 = (2 : ℝ) := by rfl
    have u5 : box3hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box3lo 5 = (2 : ℝ) := by rfl
    have eb : B17 = ((47605760710723502227/112589990684262400000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box3lo j) (box3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box3lo, box3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K17 i := by
    intro i; fin_cases i <;> norm_num [K17]
  have hR0 : ∀ i, 0 ≤ R17 i := by
    intro i; fin_cases i <;> norm_num [R17, K17, box3lo, box3hi]
  have hchain := chain_idx17 c17_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c17_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 18 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c18_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.114872) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.08743 * (y 0) + (-0.080919) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.593722

theorem c18_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c18_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.08743 * y1 + (-0.080919) * (y2 + y3 + y5 + y6) + 0.593722 :=
  rfl

/-- Component 18 gate (box 3; chain chain_idx18; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c18_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => c18_mfuna (Function.update y i t) - K18 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B18 ≤ c18_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.08743 * y1 + (-0.080919) * (y2 + y3 + y5 + y6) + 0.593722 > 0 := by
  have hpos : (0 : ℝ) <
      B18 - ∑ i, R18 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R18 i = K18 i * (box3hi i - box3lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K18 0 = (0 : ℝ) := by rfl
    have t1 : K18 1 = (0 : ℝ) := by rfl
    have t2 : K18 2 = (0 : ℝ) := by rfl
    have t3 : K18 3 = (0 : ℝ) := by rfl
    have t4 : K18 4 = (0 : ℝ) := by rfl
    have t5 : K18 5 = (0 : ℝ) := by rfl
    have u0 : box3hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box3lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box3hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box3lo 1 = (2 : ℝ) := by rfl
    have u2 : box3hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box3lo 2 = (2 : ℝ) := by rfl
    have u3 : box3hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : box3lo 3 = (2 : ℝ) := by rfl
    have u4 : box3hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box3lo 4 = (2 : ℝ) := by rfl
    have u5 : box3hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box3lo 5 = (2 : ℝ) := by rfl
    have eb : B18 = ((23997835552978532956863/56294995342131200000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box3lo j) (box3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box3lo, box3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K18 i := by
    intro i; fin_cases i <;> norm_num [K18]
  have hR0 : ∀ i, 0 ≤ R18 i := by
    intro i; fin_cases i <;> norm_num [R18, K18, box3lo, box3hi]
  have hchain := chain_idx18 c18_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c18_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 19 gate (box 3; chain chain_idx19; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c19_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => c17_mfuna (Function.update y i t) - K19 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B19 ≤ c17_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.148605 * y1 + 0.080919 * (y2 + y3 + y5 + y6) + (-0.855148) > 0 := by
  have hpos : (0 : ℝ) <
      B19 - ∑ i, R19 i := by
    rw [sumFin6a]
    have ev : ∀ i : Fin 6, R19 i = K19 i * (box3hi i - box3lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K19 0 = (0 : ℝ) := by rfl
    have t1 : K19 1 = (0 : ℝ) := by rfl
    have t2 : K19 2 = (0 : ℝ) := by rfl
    have t3 : K19 3 = (0 : ℝ) := by rfl
    have t4 : K19 4 = (0 : ℝ) := by rfl
    have t5 : K19 5 = (0 : ℝ) := by rfl
    have u0 : box3hi 0 = (63/25 : ℝ) := by rfl
    have q0 : box3lo 0 = (4927/2000 : ℝ) := by rfl
    have u1 : box3hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : box3lo 1 = (2 : ℝ) := by rfl
    have u2 : box3hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : box3lo 2 = (2 : ℝ) := by rfl
    have u3 : box3hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : box3lo 3 = (2 : ℝ) := by rfl
    have u4 : box3hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : box3lo 4 = (2 : ℝ) := by rfl
    have u5 : box3hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : box3lo 5 = (2 : ℝ) := by rfl
    have eb : B19 = ((47605760710723502227/112589990684262400000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (box3lo j) (box3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [box3lo, box3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K19 i := by
    intro i; fin_cases i <;> norm_num [K19]
  have hR0 : ∀ i, 0 ≤ R19 i := by
    intro i; fin_cases i <;> norm_num [R19, K19, box3lo, box3hi]
  have hchain := chain_idx19 c17_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c17_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 20 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c20_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.065103 + ((-0.008732) + 0.072591 + 0.042651 + 0.055356) * y1 + 2 * ((-0.024884) + 0.024884) * y12 + 2 * (0.024884 + (-0.024884)) * y23 + 2 * ((-0.024884) + 0.024884) * y34 + 2 * (0.024884 + (-0.024884)) * y41 + (0.097156 + (-0.464803) + 0.008797 + (-0.458108)) < 0 :=
  ox3q1hLin_020

/-- Margin function of conjunct 21 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c21_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.008732) * (y 0) + (-0.024884) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.097156

theorem c21_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c21_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.008732) * y1 + (-0.024884) * (y2 + y3 + y5 + y6) + 0.097156 :=
  rfl

/-- Component 21 gate (box 4; chain chain_idx21; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c21_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b4lo j) (b4hi j)) →
      ConcaveOn ℝ (Set.Icc (b4lo i) (b4hi i))
        (fun t => c21_mfuna (Function.update y i t) - K21 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb4 j) → B21 ≤ c21_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.008732) * y1 + (-0.024884) * (y2 + y3 + y5 + y6) + 0.097156 > 0 := by
  have hpos : (0 : ℝ) <
      B21 - ∑ i, R21 i := by
    rw [sumFin6a]
    have e0 : R21 0 = (0 : ℝ) := by rfl
    have e1 : R21 1 = (0 : ℝ) := by rfl
    have e2 : R21 2 = (0 : ℝ) := by rfl
    have e3 : R21 3 = (7981354906034381/35184372088832000000 : ℝ) := by rfl
    have e4 : R21 4 = (0 : ℝ) := by rfl
    have e5 : R21 5 = (0 : ℝ) := by rfl
    have eb : B21 = ((4895826076609267045505263/1801439850948198400000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b4lo j) (b4hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b4lo, b4hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K21 i := by
    intro i; fin_cases i <;> norm_num [K21]
  have hR0 : ∀ i, 0 ≤ R21 i := by
    intro i; fin_cases i <;> norm_num [R21, K21, b4lo, b4hi]
  have hchain := chain_idx21 c21_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c21_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 22 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c22_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.072591 * (y 0) + 0.024884 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.464803)

theorem c22_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c22_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.072591 * y1 + 0.024884 * (y2 + y3 + y5 + y6) + (-0.464803) :=
  rfl

/-- Component 22 gate (box 1; chain chain_idx22; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c22_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b1lo j) (b1hi j)) →
      ConcaveOn ℝ (Set.Icc (b1lo i) (b1hi i))
        (fun t => c22_mfuna (Function.update y i t) - K22 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb1 j) → B22 ≤ c22_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.072591 * y1 + 0.024884 * (y2 + y3 + y5 + y6) + (-0.464803) > 0 := by
  have hpos : (0 : ℝ) <
      B22 - ∑ i, R22 i := by
    rw [sumFin6a]
    have e0 : R22 0 = (0 : ℝ) := by rfl
    have e1 : R22 1 = (0 : ℝ) := by rfl
    have e2 : R22 2 = (0 : ℝ) := by rfl
    have e3 : R22 3 = (0 : ℝ) := by rfl
    have e4 : R22 4 = (0 : ℝ) := by rfl
    have e5 : R22 5 = (0 : ℝ) := by rfl
    have eb : B22 = ((391755953970611721873027/144115188075855872000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b1lo j) (b1hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b1lo, b1hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K22 i := by
    intro i; fin_cases i <;> norm_num [K22]
  have hR0 : ∀ i, 0 ≤ R22 i := by
    intro i; fin_cases i <;> norm_num [R22, K22, b1lo, b1hi]
  have hchain := chain_idx22 c22_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c22_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 23 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c23_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.042651 * (y 0) + (-0.024884) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.008797

theorem c23_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c23_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.042651 * y1 + (-0.024884) * (y2 + y3 + y5 + y6) + 0.008797 :=
  rfl

/-- Component 23 gate (box 1; chain chain_idx23; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c23_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b1lo j) (b1hi j)) →
      ConcaveOn ℝ (Set.Icc (b1lo i) (b1hi i))
        (fun t => c23_mfuna (Function.update y i t) - K23 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb1 j) → B23 ≤ c23_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.042651 * y1 + (-0.024884) * (y2 + y3 + y5 + y6) + 0.008797 > 0 := by
  have hpos : (0 : ℝ) <
      B23 - ∑ i, R23 i := by
    rw [sumFin6a]
    have e0 : R23 0 = (0 : ℝ) := by rfl
    have e1 : R23 1 = (0 : ℝ) := by rfl
    have e2 : R23 2 = (0 : ℝ) := by rfl
    have e3 : R23 3 = (0 : ℝ) := by rfl
    have e4 : R23 4 = (0 : ℝ) := by rfl
    have e5 : R23 5 = (0 : ℝ) := by rfl
    have eb : B23 = ((9816462584030802937566801/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b1lo j) (b1hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b1lo, b1hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K23 i := by
    intro i; fin_cases i <;> norm_num [K23]
  have hR0 : ∀ i, 0 ≤ R23 i := by
    intro i; fin_cases i <;> norm_num [R23, K23, b1lo, b1hi]
  have hchain := chain_idx23 c23_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c23_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 24 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c24_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.055356 * (y 0) + 0.024884 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.458108)

theorem c24_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c24_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.055356 * y1 + 0.024884 * (y2 + y3 + y5 + y6) + (-0.458108) :=
  rfl

/-- Component 24 gate (box 2; chain chain_idx24; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c24_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b2lo j) (b2hi j)) →
      ConcaveOn ℝ (Set.Icc (b2lo i) (b2hi i))
        (fun t => c24_mfuna (Function.update y i t) - K24 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb2 j) → B24 ≤ c24_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.055356 * y1 + 0.024884 * (y2 + y3 + y5 + y6) + (-0.458108) > 0 := by
  have hpos : (0 : ℝ) <
      B24 - ∑ i, R24 i := by
    rw [sumFin6a]
    have e0 : R24 0 = (0 : ℝ) := by rfl
    have e1 : R24 1 = (0 : ℝ) := by rfl
    have e2 : R24 2 = (0 : ℝ) := by rfl
    have e3 : R24 3 = (0 : ℝ) := by rfl
    have e4 : R24 4 = (0 : ℝ) := by rfl
    have e5 : R24 5 = (0 : ℝ) := by rfl
    have eb : B24 = ((391525641827483180239857/144115188075855872000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b2lo j) (b2hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b2lo, b2hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K24 i := by
    intro i; fin_cases i <;> norm_num [K24]
  have hR0 : ∀ i, 0 ≤ R24 i := by
    intro i; fin_cases i <;> norm_num [R24, K24, b2lo, b2hi]
  have hchain := chain_idx24 c24_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c24_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 25 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c25_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.065103 + ((-0.029778) + 0.072591 + 0.055356 + 0.072591) * y1 + 2 * ((-0.027449) + 0.027449) * y12 + 2 * (0.027449 + (-0.027449)) * y23 + 2 * ((-0.027449) + 0.027449) * y34 + 2 * (0.027449 + (-0.027449)) * y41 + (0.170713 + (-0.485323) + (-0.039438) + (-0.485323)) < 0 :=
  ox3q1hLin_025

/-- Margin function of conjunct 26 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c26_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.029778) * (y 0) + (-0.027449) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.170713

theorem c26_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c26_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.029778) * y1 + (-0.027449) * (y2 + y3 + y5 + y6) + 0.170713 :=
  rfl

/-- Component 26 gate (box 4; chain chain_idx26; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c26_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b4lo j) (b4hi j)) →
      ConcaveOn ℝ (Set.Icc (b4lo i) (b4hi i))
        (fun t => c26_mfuna (Function.update y i t) - K26 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb4 j) → B26 ≤ c26_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.029778) * y1 + (-0.027449) * (y2 + y3 + y5 + y6) + 0.170713 > 0 := by
  have hpos : (0 : ℝ) <
      B26 - ∑ i, R26 i := by
    rw [sumFin6a]
    have e0 : R26 0 = (0 : ℝ) := by rfl
    have e1 : R26 1 = (0 : ℝ) := by rfl
    have e2 : R26 2 = (0 : ℝ) := by rfl
    have e3 : R26 3 = (7981354906034381/35184372088832000000 : ℝ) := by rfl
    have e4 : R26 4 = (0 : ℝ) := by rfl
    have e5 : R26 5 = (0 : ℝ) := by rfl
    have eb : B26 = ((4898078236710922483144943/1801439850948198400000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b4lo j) (b4hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b4lo, b4hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K26 i := by
    intro i; fin_cases i <;> norm_num [K26]
  have hR0 : ∀ i, 0 ≤ R26 i := by
    intro i; fin_cases i <;> norm_num [R26, K26, b4lo, b4hi]
  have hchain := chain_idx26 c26_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c26_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 27 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c27_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.072591 * (y 0) + 0.027449 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.485323)

theorem c27_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c27_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.072591 * y1 + 0.027449 * (y2 + y3 + y5 + y6) + (-0.485323) :=
  rfl

/-- Component 27 gate (box 1; chain chain_idx27; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c27_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b1lo j) (b1hi j)) →
      ConcaveOn ℝ (Set.Icc (b1lo i) (b1hi i))
        (fun t => c27_mfuna (Function.update y i t) - K27 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb1 j) → B27 ≤ c27_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.072591 * y1 + 0.027449 * (y2 + y3 + y5 + y6) + (-0.485323) > 0 := by
  have hpos : (0 : ℝ) <
      B27 - ∑ i, R27 i := by
    rw [sumFin6a]
    have e0 : R27 0 = (0 : ℝ) := by rfl
    have e1 : R27 1 = (0 : ℝ) := by rfl
    have e2 : R27 2 = (0 : ℝ) := by rfl
    have e3 : R27 3 = (0 : ℝ) := by rfl
    have e4 : R27 4 = (0 : ℝ) := by rfl
    have e5 : R27 5 = (0 : ℝ) := by rfl
    have eb : B27 = ((391755953970611721873027/144115188075855872000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b1lo j) (b1hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b1lo, b1hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K27 i := by
    intro i; fin_cases i <;> norm_num [K27]
  have hR0 : ∀ i, 0 ≤ R27 i := by
    intro i; fin_cases i <;> norm_num [R27, K27, b1lo, b1hi]
  have hchain := chain_idx27 c27_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c27_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 28 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c28_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.055356 * (y 0) + (-0.027449) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.039438)

theorem c28_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c28_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.055356 * y1 + (-0.027449) * (y2 + y3 + y5 + y6) + (-0.039438) :=
  rfl

/-- Component 28 gate (box 2; chain chain_idx28; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c28_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b2lo j) (b2hi j)) →
      ConcaveOn ℝ (Set.Icc (b2lo i) (b2hi i))
        (fun t => c28_mfuna (Function.update y i t) - K28 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb2 j) → B28 ≤ c28_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.055356 * y1 + (-0.027449) * (y2 + y3 + y5 + y6) + (-0.039438) > 0 := by
  have hpos : (0 : ℝ) <
      B28 - ∑ i, R28 i := by
    rw [sumFin6a]
    have e0 : R28 0 = (0 : ℝ) := by rfl
    have e1 : R28 1 = (0 : ℝ) := by rfl
    have e2 : R28 2 = (0 : ℝ) := by rfl
    have e3 : R28 3 = (0 : ℝ) := by rfl
    have e4 : R28 4 = (0 : ℝ) := by rfl
    have e5 : R28 5 = (0 : ℝ) := by rfl
    have eb : B28 = ((392390332955938315471857/144115188075855872000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b2lo j) (b2hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b2lo, b2hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K28 i := by
    intro i; fin_cases i <;> norm_num [K28]
  have hR0 : ∀ i, 0 ≤ R28 i := by
    intro i; fin_cases i <;> norm_num [R28, K28, b2lo, b2hi]
  have hchain := chain_idx28 c28_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c28_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 29 gate (box 3; chain chain_idx29; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c29_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b3lo j) (b3hi j)) →
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => c27_mfuna (Function.update y i t) - K29 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B29 ≤ c27_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.072591 * y1 + 0.027449 * (y2 + y3 + y5 + y6) + (-0.485323) > 0 := by
  have hpos : (0 : ℝ) <
      B29 - ∑ i, R29 i := by
    rw [sumFin6a]
    have e0 : R29 0 = (0 : ℝ) := by rfl
    have e1 : R29 1 = (0 : ℝ) := by rfl
    have e2 : R29 2 = (0 : ℝ) := by rfl
    have e3 : R29 3 = (0 : ℝ) := by rfl
    have e4 : R29 4 = (0 : ℝ) := by rfl
    have e5 : R29 5 = (0 : ℝ) := by rfl
    have eb : B29 = ((391755953970611721873027/144115188075855872000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b3lo j) (b3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b3lo, b3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K29 i := by
    intro i; fin_cases i <;> norm_num [K29]
  have hR0 : ∀ i, 0 ≤ R29 i := by
    intro i; fin_cases i <;> norm_num [R29, K29, b3lo, b3hi]
  have hchain := chain_idx29 c27_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c27_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 30 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c30_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.065103 + ((-0.008732) + 0.055356 + 0.072591 + 0.037947) * y1 + 2 * (0.025458 + (-0.025458)) * y12 + 2 * ((-0.025458) + 0.025458) * y23 + 2 * (0.025458 + (-0.025458)) * y34 + 2 * ((-0.025458) + 0.025458) * y41 + ((-0.30558) + (-0.055371) + (-0.469389) + 0.025236) < 0 :=
  ox3q1hLin_030

/-- Margin function of conjunct 31 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c31_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.008732) * (y 0) + 0.025458 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.30558)

theorem c31_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c31_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.008732) * y1 + 0.025458 * (y2 + y3 + y5 + y6) + (-0.30558) :=
  rfl

/-- Component 31 gate (box 4; chain chain_idx31; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c31_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b4lo j) (b4hi j)) →
      ConcaveOn ℝ (Set.Icc (b4lo i) (b4hi i))
        (fun t => c31_mfuna (Function.update y i t) - K31 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb4 j) → B31 ≤ c31_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + (-0.008732) * y1 + 0.025458 * (y2 + y3 + y5 + y6) + (-0.30558) > 0 := by
  have hpos : (0 : ℝ) <
      B31 - ∑ i, R31 i := by
    rw [sumFin6a]
    have e0 : R31 0 = (0 : ℝ) := by rfl
    have e1 : R31 1 = (0 : ℝ) := by rfl
    have e2 : R31 2 = (0 : ℝ) := by rfl
    have e3 : R31 3 = (7981354906034381/35184372088832000000 : ℝ) := by rfl
    have e4 : R31 4 = (0 : ℝ) := by rfl
    have e5 : R31 5 = (0 : ℝ) := by rfl
    have eb : B31 = ((391762464992251800366721/144115188075855872000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b4lo j) (b4hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b4lo, b4hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K31 i := by
    intro i; fin_cases i <;> norm_num [K31]
  have hR0 : ∀ i, 0 ≤ R31 i := by
    intro i; fin_cases i <;> norm_num [R31, K31, b4lo, b4hi]
  have hchain := chain_idx31 c31_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c31_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 32 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c32_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.055356 * (y 0) + (-0.025458) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.055371)

theorem c32_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c32_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.055356 * y1 + (-0.025458) * (y2 + y3 + y5 + y6) + (-0.055371) :=
  rfl

/-- Component 32 gate (box 2; chain chain_idx32; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c32_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b2lo j) (b2hi j)) →
      ConcaveOn ℝ (Set.Icc (b2lo i) (b2hi i))
        (fun t => c32_mfuna (Function.update y i t) - K32 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb2 j) → B32 ≤ c32_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.055356 * y1 + (-0.025458) * (y2 + y3 + y5 + y6) + (-0.055371) > 0 := by
  have hpos : (0 : ℝ) <
      B32 - ∑ i, R32 i := by
    rw [sumFin6a]
    have e0 : R32 0 = (0 : ℝ) := by rfl
    have e1 : R32 1 = (0 : ℝ) := by rfl
    have e2 : R32 2 = (0 : ℝ) := by rfl
    have e3 : R32 3 = (0 : ℝ) := by rfl
    have e4 : R32 4 = (0 : ℝ) := by rfl
    have e5 : R32 5 = (0 : ℝ) := by rfl
    have eb : B32 = ((391669757015559036111857/144115188075855872000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b2lo j) (b2hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b2lo, b2hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K32 i := by
    intro i; fin_cases i <;> norm_num [K32]
  have hR0 : ∀ i, 0 ≤ R32 i := by
    intro i; fin_cases i <;> norm_num [R32, K32, b2lo, b2hi]
  have hchain := chain_idx32 c32_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c32_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 33 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c33_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.072591 * (y 0) + 0.025458 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.469389)

theorem c33_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c33_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.072591 * y1 + 0.025458 * (y2 + y3 + y5 + y6) + (-0.469389) :=
  rfl

/-- Component 33 gate (box 3; chain chain_idx33; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c33_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b3lo j) (b3hi j)) →
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => c33_mfuna (Function.update y i t) - K33 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B33 ≤ c33_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.072591 * y1 + 0.025458 * (y2 + y3 + y5 + y6) + (-0.469389) > 0 := by
  have hpos : (0 : ℝ) <
      B33 - ∑ i, R33 i := by
    rw [sumFin6a]
    have e0 : R33 0 = (0 : ℝ) := by rfl
    have e1 : R33 1 = (0 : ℝ) := by rfl
    have e2 : R33 2 = (0 : ℝ) := by rfl
    have e3 : R33 3 = (0 : ℝ) := by rfl
    have e4 : R33 4 = (0 : ℝ) := by rfl
    have e5 : R33 5 = (0 : ℝ) := by rfl
    have eb : B33 = ((392620645099066857105027/144115188075855872000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b3lo j) (b3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b3lo, b3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K33 i := by
    intro i; fin_cases i <;> norm_num [K33]
  have hR0 : ∀ i, 0 ≤ R33 i := by
    intro i; fin_cases i <;> norm_num [R33, K33, b3lo, b3hi]
  have hchain := chain_idx33 c33_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c33_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 34 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c34_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.065103 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.037947 * (y 0) + (-0.025458) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.025236

theorem c34_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c34_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.037947 * y1 + (-0.025458) * (y2 + y3 + y5 + y6) + 0.025236 :=
  rfl

/-- Component 34 gate (box 3; chain chain_idx34; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c34_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b3lo j) (b3hi j)) →
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => c34_mfuna (Function.update y i t) - K34 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B34 ≤ c34_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.065103 * dihY y1 y2 y3 y4 y5 y6 + 0.037947 * y1 + (-0.025458) * (y2 + y3 + y5 + y6) + 0.025236 > 0 := by
  have hpos : (0 : ℝ) <
      B34 - ∑ i, R34 i := by
    rw [sumFin6a]
    have e0 : R34 0 = (0 : ℝ) := by rfl
    have e1 : R34 1 = (0 : ℝ) := by rfl
    have e2 : R34 2 = (0 : ℝ) := by rfl
    have e3 : R34 3 = (0 : ℝ) := by rfl
    have e4 : R34 4 = (0 : ℝ) := by rfl
    have e5 : R34 5 = (0 : ℝ) := by rfl
    have eb : B34 = ((9789929248523780961261137/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b3lo j) (b3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b3lo, b3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K34 i := by
    intro i; fin_cases i <;> norm_num [K34]
  have hR0 : ∀ i, 0 ≤ R34 i := by
    intro i; fin_cases i <;> norm_num [R34, K34, b3lo, b3hi]
  have hchain := chain_idx34 c34_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c34_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 35 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c35_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.114872) + (0.116669 + 0.08743 + 0.148605 + 0.08743) * y1 + 2 * (0.080919 + (-0.080919)) * y12 + 2 * ((-0.080919) + 0.080919) * y23 + 2 * (0.080919 + (-0.080919)) * y34 + 2 * ((-0.080919) + 0.080919) * y41 + ((-0.7251449999999999) + 0.595546 + (-0.853324) + 0.595546) < 0 :=
  ox3q1hLin_035

/-- Margin function of conjunct 36 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c36_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.114872) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.116669 * (y 0) + 0.080919 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.7251449999999999)

theorem c36_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c36_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.116669 * y1 + 0.080919 * (y2 + y3 + y5 + y6) + (-0.7251449999999999) :=
  rfl

/-- Component 36 gate (box 4; chain chain_idx36; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c36_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b4lo j) (b4hi j)) →
      ConcaveOn ℝ (Set.Icc (b4lo i) (b4hi i))
        (fun t => c36_mfuna (Function.update y i t) - K36 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb4 j) → B36 ≤ c36_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.116669 * y1 + 0.080919 * (y2 + y3 + y5 + y6) + (-0.7251449999999999) > 0 := by
  have hpos : (0 : ℝ) <
      B36 - ∑ i, R36 i := by
    rw [sumFin6a]
    have e0 : R36 0 = (0 : ℝ) := by rfl
    have e1 : R36 1 = (0 : ℝ) := by rfl
    have e2 : R36 2 = (0 : ℝ) := by rfl
    have e3 : R36 3 = (7520659533992827/35184372088832000000 : ℝ) := by rfl
    have e4 : R36 4 = (0 : ℝ) := by rfl
    have e5 : R36 5 = (0 : ℝ) := by rfl
    have eb : B36 = ((169003679070000176490327241168231/75244594461734338560000000000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b4lo j) (b4hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b4lo, b4hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K36 i := by
    intro i; fin_cases i <;> norm_num [K36]
  have hR0 : ∀ i, 0 ≤ R36 i := by
    intro i; fin_cases i <;> norm_num [R36, K36, b4lo, b4hi]
  have hchain := chain_idx36 c36_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c36_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 37 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c37_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.114872) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.08743 * (y 0) + (-0.080919) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.595546

theorem c37_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c37_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.08743 * y1 + (-0.080919) * (y2 + y3 + y5 + y6) + 0.595546 :=
  rfl

/-- Component 37 gate (box 3; chain chain_idx37; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c37_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b3lo j) (b3hi j)) →
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => c37_mfuna (Function.update y i t) - K37 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B37 ≤ c37_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.08743 * y1 + (-0.080919) * (y2 + y3 + y5 + y6) + 0.595546 > 0 := by
  have hpos : (0 : ℝ) <
      B37 - ∑ i, R37 i := by
    rw [sumFin6a]
    have e0 : R37 0 = (0 : ℝ) := by rfl
    have e1 : R37 1 = (0 : ℝ) := by rfl
    have e2 : R37 2 = (0 : ℝ) := by rfl
    have e3 : R37 3 = (0 : ℝ) := by rfl
    have e4 : R37 4 = (0 : ℝ) := by rfl
    have e5 : R37 5 = (0 : ℝ) := by rfl
    have eb : B37 = ((126679907057025841756863/56294995342131200000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b3lo j) (b3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b3lo, b3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K37 i := by
    intro i; fin_cases i <;> norm_num [K37]
  have hR0 : ∀ i, 0 ≤ R37 i := by
    intro i; fin_cases i <;> norm_num [R37, K37, b3lo, b3hi]
  have hchain := chain_idx37 c37_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c37_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 38 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c38_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.114872) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.148605 * (y 0) + 0.080919 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.853324)

theorem c38_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c38_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.148605 * y1 + 0.080919 * (y2 + y3 + y5 + y6) + (-0.853324) :=
  rfl

/-- Component 38 gate (box 3; chain chain_idx38; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c38_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b3lo j) (b3hi j)) →
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => c38_mfuna (Function.update y i t) - K38 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B38 ≤ c38_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.148605 * y1 + 0.080919 * (y2 + y3 + y5 + y6) + (-0.853324) > 0 := by
  have hpos : (0 : ℝ) <
      B38 - ∑ i, R38 i := by
    rw [sumFin6a]
    have e0 : R38 0 = (0 : ℝ) := by rfl
    have e1 : R38 1 = (0 : ℝ) := by rfl
    have e2 : R38 2 = (0 : ℝ) := by rfl
    have e3 : R38 3 = (0 : ℝ) := by rfl
    have e4 : R38 4 = (0 : ℝ) := by rfl
    have e5 : R38 5 = (0 : ℝ) := by rfl
    have eb : B38 = ((252969903718818119827/112589990684262400000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b3lo j) (b3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b3lo, b3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K38 i := by
    intro i; fin_cases i <;> norm_num [K38]
  have hR0 : ∀ i, 0 ≤ R38 i := by
    intro i; fin_cases i <;> norm_num [R38, K38, b3lo, b3hi]
  have hchain := chain_idx38 c38_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c38_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 39 gate (box 3; chain chain_idx39; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c39_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b3lo j) (b3hi j)) →
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => c37_mfuna (Function.update y i t) - K39 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B39 ≤ c37_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.114872) * dihY y1 y2 y3 y4 y5 y6 + 0.08743 * y1 + (-0.080919) * (y2 + y3 + y5 + y6) + 0.595546 > 0 := by
  have hpos : (0 : ℝ) <
      B39 - ∑ i, R39 i := by
    rw [sumFin6a]
    have e0 : R39 0 = (0 : ℝ) := by rfl
    have e1 : R39 1 = (0 : ℝ) := by rfl
    have e2 : R39 2 = (0 : ℝ) := by rfl
    have e3 : R39 3 = (0 : ℝ) := by rfl
    have e4 : R39 4 = (0 : ℝ) := by rfl
    have e5 : R39 5 = (0 : ℝ) := by rfl
    have eb : B39 = ((126679907057025841756863/56294995342131200000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b3lo j) (b3hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b3lo, b3hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K39 i := by
    intro i; fin_cases i <;> norm_num [K39]
  have hR0 : ∀ i, 0 ≤ R39 i := by
    intro i; fin_cases i <;> norm_num [R39, K39, b3lo, b3hi]
  have hchain := chain_idx39 c37_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c37_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 40 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c40_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.129913 + ((-0.09152) + 0.347659 + (-0.105208) + (-0.150931)) * y1 + 2 * (0.002372 + (-0.002372)) * y12 + 2 * ((-0.002372) + 0.002372) * y23 + 2 * (0.002372 + (-0.002372)) * y34 + 2 * ((-0.002372) + 0.002372) * y41 + ((-0.034749) + (-1.030425) + 0.072849 + 0.176057) < 0 :=
  ox3q1hLin_040

/-- Margin function of conjunct 41 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c41_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.09152) * (y 0) + 0.002372 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.034749)

theorem c41_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c41_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.09152) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-0.034749) :=
  rfl

/-- Component 41 gate (box 5; S4.5 split-grid chain
`chain_split_idx41`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
4; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c41_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit41 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b5lo j) (b5hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit41 i k) (gsplit41 i (k + 1)))
        (fun t => c41_mfuna (Function.update y i t) - b2K41 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split41 j) → b2B41 ≤ c41_mfuna v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.09152) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-0.034749) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b5lo j) (b5hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b5lo, b5hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx41 c41_mfuna hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c41_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx41
  linarith [hchain, hpos]

/-- Margin function of conjunct 42 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c42_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.347659 * (y 0) + (-0.002372) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-1.030425)

theorem c42_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c42_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.347659 * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + (-1.030425) :=
  rfl

/-- Component 42 gate (box 6; chain chain_idx42; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c42_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b6lo j) (b6hi j)) →
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => c42_mfuna (Function.update y i t) - K42 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B42 ≤ c42_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.347659 * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + (-1.030425) > 0 := by
  have hpos : (0 : ℝ) <
      B42 - ∑ i, R42 i := by
    rw [sumFin6a]
    have e0 : R42 0 = (0 : ℝ) := by rfl
    have e1 : R42 1 = (0 : ℝ) := by rfl
    have e2 : R42 2 = (0 : ℝ) := by rfl
    have e3 : R42 3 = (0 : ℝ) := by rfl
    have e4 : R42 4 = (0 : ℝ) := by rfl
    have e5 : R42 5 = (0 : ℝ) := by rfl
    have eb : B42 = ((1300659138202979573854401/450359962737049600000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
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
  have hK0 : ∀ i, 0 ≤ K42 i := by
    intro i; fin_cases i <;> norm_num [K42]
  have hR0 : ∀ i, 0 ≤ R42 i := by
    intro i; fin_cases i <;> norm_num [R42, K42, b6lo, b6hi]
  have hchain := chain_idx42 c42_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c42_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 43 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c43_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.105208) * (y 0) + 0.002372 * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.072849

theorem c43_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c43_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.105208) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + 0.072849 :=
  rfl

/-- Component 43 gate (box 6; chain chain_idx43; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c43_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b6lo j) (b6hi j)) →
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => c43_mfuna (Function.update y i t) - K43 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B43 ≤ c43_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.105208) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + 0.072849 > 0 := by
  have hpos : (0 : ℝ) <
      B43 - ∑ i, R43 i := by
    rw [sumFin6a]
    have e0 : R43 0 = (0 : ℝ) := by rfl
    have e1 : R43 1 = (0 : ℝ) := by rfl
    have e2 : R43 2 = (0 : ℝ) := by rfl
    have e3 : R43 3 = (0 : ℝ) := by rfl
    have e4 : R43 4 = (0 : ℝ) := by rfl
    have e5 : R43 5 = (0 : ℝ) := by rfl
    have eb : B43 = ((2082705277710028748963121/720575940379279360000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
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
  have hK0 : ∀ i, 0 ≤ K43 i := by
    intro i; fin_cases i <;> norm_num [K43]
  have hR0 : ∀ i, 0 ≤ R43 i := by
    intro i; fin_cases i <;> norm_num [R43, K43, b6lo, b6hi]
  have hchain := chain_idx43 c43_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c43_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 44 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c44_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.150931) * (y 0) + (-0.002372) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.176057

theorem c44_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c44_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.150931) * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + 0.176057 :=
  rfl

/-- Component 44 gate (box 7; chain chain_idx44; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c44_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b7lo j) (b7hi j)) →
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => c44_mfuna (Function.update y i t) - K44 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B44 ≤ c44_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.150931) * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + 0.176057 > 0 := by
  have hpos : (0 : ℝ) <
      B44 - ∑ i, R44 i := by
    rw [sumFin6a]
    have e0 : R44 0 = (0 : ℝ) := by rfl
    have e1 : R44 1 = (0 : ℝ) := by rfl
    have e2 : R44 2 = (0 : ℝ) := by rfl
    have e3 : R44 3 = (0 : ℝ) := by rfl
    have e4 : R44 4 = (0 : ℝ) := by rfl
    have e5 : R44 5 = (0 : ℝ) := by rfl
    have eb : B44 = ((520351686966608802787793/180143985094819840000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
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
  have hK0 : ∀ i, 0 ≤ K44 i := by
    intro i; fin_cases i <;> norm_num [K44]
  have hR0 : ∀ i, 0 ≤ R44 i := by
    intro i; fin_cases i <;> norm_num [R44, K44, b7lo, b7hi]
  have hchain := chain_idx44 c44_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c44_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 45 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c45_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.129913 + (0.340765 + (-0.094917) + (-0.150931) + (-0.094917)) * y1 + 2 * (0.002372 + (-0.002372)) * y12 + 2 * ((-0.002372) + 0.002372) * y23 + 2 * (0.002372 + (-0.002372)) * y34 + 2 * ((-0.002372) + 0.002372) * y41 + ((-1.124108) + 0.084866 + 0.138108 + 0.084866) < 0 :=
  ox3q1hLin_045

/-- Margin function of conjunct 46 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c46_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.340765 * (y 0) + 0.002372 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-1.124108)

theorem c46_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c46_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.340765 * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-1.124108) :=
  rfl

/-- Component 46 gate (box 5; S4.5 split-grid chain
`chain_split_idx46`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
4; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c46_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit46 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b5lo j) (b5hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit46 i k) (gsplit46 i (k + 1)))
        (fun t => c46_mfuna (Function.update y i t) - K46 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split46 j) → b2B46 ≤ c46_mfuna v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.340765 * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-1.124108) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b5lo j) (b5hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b5lo, b5hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx46 c46_mfuna hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c46_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx46
  linarith [hchain, hpos]

/-- Margin function of conjunct 47 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c47_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.094917) * (y 0) + (-0.002372) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.084866

theorem c47_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c47_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.094917) * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + 0.084866 :=
  rfl

/-- Component 47 gate (box 6; chain chain_idx47; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c47_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b6lo j) (b6hi j)) →
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => c47_mfuna (Function.update y i t) - K47 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B47 ≤ c47_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.094917) * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + 0.084866 > 0 := by
  have hpos : (0 : ℝ) <
      B47 - ∑ i, R47 i := by
    rw [sumFin6a]
    have e0 : R47 0 = (0 : ℝ) := by rfl
    have e1 : R47 1 = (0 : ℝ) := by rfl
    have e2 : R47 2 = (0 : ℝ) := by rfl
    have e3 : R47 3 = (0 : ℝ) := by rfl
    have e4 : R47 4 = (0 : ℝ) := by rfl
    have e5 : R47 5 = (0 : ℝ) := by rfl
    have eb : B47 = ((2599672155598563389141859/900719925474099200000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
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
  have hK0 : ∀ i, 0 ≤ K47 i := by
    intro i; fin_cases i <;> norm_num [K47]
  have hR0 : ∀ i, 0 ≤ R47 i := by
    intro i; fin_cases i <;> norm_num [R47, K47, b6lo, b6hi]
  have hchain := chain_idx47 c47_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c47_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 48 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c48_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.150931) * (y 0) + 0.002372 * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.138108

theorem c48_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c48_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.150931) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + 0.138108 :=
  rfl

/-- Component 48 gate (box 7; chain chain_idx48; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c48_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b7lo j) (b7hi j)) →
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => c48_mfuna (Function.update y i t) - K48 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B48 ≤ c48_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.150931) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + 0.138108 > 0 := by
  have hpos : (0 : ℝ) <
      B48 - ∑ i, R48 i := by
    rw [sumFin6a]
    have e0 : R48 0 = (0 : ℝ) := by rfl
    have e1 : R48 1 = (0 : ℝ) := by rfl
    have e2 : R48 2 = (0 : ℝ) := by rfl
    have e3 : R48 3 = (0 : ℝ) := by rfl
    have e4 : R48 4 = (0 : ℝ) := by rfl
    have e5 : R48 5 = (0 : ℝ) := by rfl
    have eb : B48 = ((520892118921893262307793/180143985094819840000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
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
  have hK0 : ∀ i, 0 ≤ K48 i := by
    intro i; fin_cases i <;> norm_num [K48]
  have hR0 : ∀ i, 0 ≤ R48 i := by
    intro i; fin_cases i <;> norm_num [R48, K48, b7lo, b7hi]
  have hchain := chain_idx48 c48_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c48_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 49 gate (box 8; chain chain_idx49; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c49_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b8lo j) (b8hi j)) →
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => c47_mfuna (Function.update y i t) - K49 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B49 ≤ c47_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.094917) * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + 0.084866 > 0 := by
  have hpos : (0 : ℝ) <
      B49 - ∑ i, R49 i := by
    rw [sumFin6a]
    have e0 : R49 0 = (0 : ℝ) := by rfl
    have e1 : R49 1 = (0 : ℝ) := by rfl
    have e2 : R49 2 = (0 : ℝ) := by rfl
    have e3 : R49 3 = (0 : ℝ) := by rfl
    have e4 : R49 4 = (0 : ℝ) := by rfl
    have e5 : R49 5 = (0 : ℝ) := by rfl
    have eb : B49 = ((2599672155598563389141859/900719925474099200000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
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
  have hK0 : ∀ i, 0 ≤ K49 i := by
    intro i; fin_cases i <;> norm_num [K49]
  have hR0 : ∀ i, 0 ≤ R49 i := by
    intro i; fin_cases i <;> norm_num [R49, K49, b8lo, b8hi]
  have hchain := chain_idx49 c47_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c47_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 50 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c50_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.129913 + ((-0.09152) + 0.291645 + (-0.105208) + (-0.094917)) * y1 + 2 * (0.002372 + (-0.002372)) * y12 + 2 * ((-0.002372) + 0.002372) * y23 + 2 * (0.002372 + (-0.002372)) * y34 + 2 * ((-0.002372) + 0.002372) * y41 + ((-0.034749) + (-0.939234) + 0.072849 + 0.084866) < 0 :=
  ox3q1hLin_050

/-- Component 51 gate (box 5; S4.5 split-grid chain
`chain_split_idx51`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
4; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c51_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit51 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b5lo j) (b5hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit51 i k) (gsplit51 i (k + 1)))
        (fun t => c41_mfuna (Function.update y i t) - K51 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split51 j) → B51 ≤ c41_mfuna v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.09152) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + (-0.034749) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b5lo j) (b5hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b5lo, b5hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx51 c41_mfuna hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c41_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx51
  linarith [hchain, hpos]

/-- Margin function of conjunct 52 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c52_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.129913 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.291645 * (y 0) + (-0.002372) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.939234)

theorem c52_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c52_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.291645 * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + (-0.939234) :=
  rfl

/-- Component 52 gate (box 7; chain chain_idx52; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c52_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b7lo j) (b7hi j)) →
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => c52_mfuna (Function.update y i t) - K52 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B52 ≤ c52_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (hminus + 1) ≤ y4 → y4 ≤ (2 * hminus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + 0.291645 * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + (-0.939234) > 0 := by
  have hpos : (0 : ℝ) <
      B52 - ∑ i, R52 i := by
    rw [sumFin6a]
    have e0 : R52 0 = (0 : ℝ) := by rfl
    have e1 : R52 1 = (0 : ℝ) := by rfl
    have e2 : R52 2 = (0 : ℝ) := by rfl
    have e3 : R52 3 = (0 : ℝ) := by rfl
    have e4 : R52 4 = (0 : ℝ) := by rfl
    have e5 : R52 5 = (0 : ℝ) := by rfl
    have eb : B52 = ((16654401013328868680957/5764607523034234880000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
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
  have hK0 : ∀ i, 0 ≤ K52 i := by
    intro i; fin_cases i <;> norm_num [K52]
  have hR0 : ∀ i, 0 ≤ R52 i := by
    intro i; fin_cases i <;> norm_num [R52, K52, b7lo, b7hi]
  have hchain := chain_idx52 c52_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c52_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 53 gate (box 8; chain chain_idx53; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c53_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b8lo j) (b8hi j)) →
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => c43_mfuna (Function.update y i t) - K53 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B53 ≤ c43_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.105208) * y1 + 0.002372 * (y2 + y3 + y5 + y6) + 0.072849 > 0 := by
  have hpos : (0 : ℝ) <
      B53 - ∑ i, R53 i := by
    rw [sumFin6a]
    have e0 : R53 0 = (0 : ℝ) := by rfl
    have e1 : R53 1 = (0 : ℝ) := by rfl
    have e2 : R53 2 = (0 : ℝ) := by rfl
    have e3 : R53 3 = (0 : ℝ) := by rfl
    have e4 : R53 4 = (0 : ℝ) := by rfl
    have e5 : R53 5 = (0 : ℝ) := by rfl
    have eb : B53 = ((2082705277710028748963121/720575940379279360000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
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
  have hK0 : ∀ i, 0 ≤ K53 i := by
    intro i; fin_cases i <;> norm_num [K53]
  have hR0 : ∀ i, 0 ≤ R53 i := by
    intro i; fin_cases i <;> norm_num [R53, K53, b8lo, b8hi]
  have hchain := chain_idx53 c43_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c43_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 54 gate (box 8; chain chain_idx54; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c54_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b8lo j) (b8hi j)) →
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => c47_mfuna (Function.update y i t) - K54 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B54 ≤ c47_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.129913 * dihY y1 y2 y3 y4 y5 y6 + (-0.094917) * y1 + (-0.002372) * (y2 + y3 + y5 + y6) + 0.084866 > 0 := by
  have hpos : (0 : ℝ) <
      B54 - ∑ i, R54 i := by
    rw [sumFin6a]
    have e0 : R54 0 = (0 : ℝ) := by rfl
    have e1 : R54 1 = (0 : ℝ) := by rfl
    have e2 : R54 2 = (0 : ℝ) := by rfl
    have e3 : R54 3 = (0 : ℝ) := by rfl
    have e4 : R54 4 = (0 : ℝ) := by rfl
    have e5 : R54 5 = (0 : ℝ) := by rfl
    have eb : B54 = ((2599672155598563389141859/900719925474099200000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
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
  have hK0 : ∀ i, 0 ≤ K54 i := by
    intro i; fin_cases i <;> norm_num [K54]
  have hR0 : ∀ i, 0 ≤ R54 i := by
    intro i; fin_cases i <;> norm_num [R54, K54, b8lo, b8hi]
  have hchain := chain_idx54 c47_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c47_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 55 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c55_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.128506 + (0.290371 + (-0.070878) + (-0.097658) + (-0.121835)) * y1 + 2 * (0.003287 + (-0.003287)) * y12 + 2 * ((-0.003287) + 0.003287) * y23 + 2 * (0.003287 + (-0.003287)) * y34 + 2 * ((-0.003287) + 0.003287) * y41 + ((-1.026581) + 0.033394 + 0.050047 + 0.13571) < 0 :=
  ox3q1hLin_055

/-- Margin function of conjunct 56 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c56_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.128506 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.290371 * (y 0) + 0.003287 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-1.026581)

theorem c56_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c56_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + 0.290371 * y1 + 0.003287 * (y2 + y3 + y5 + y6) + (-1.026581) :=
  rfl

/-- Component 56 gate (box 9; S4.5 split-grid chain
`chain_split_idx56`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
3; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c56_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit56 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b9lo j) (b9hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit56 i k) (gsplit56 i (k + 1)))
        (fun t => c56_mfuna (Function.update y i t) - K56 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split56 j) → B56 ≤ c56_mfuna v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + 0.290371 * y1 + 0.003287 * (y2 + y3 + y5 + y6) + (-1.026581) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b9lo j) (b9hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b9lo, b9hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx56 c56_mfuna hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c56_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx56
  linarith [hchain, hpos]

/-- Margin function of conjunct 57 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c57_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.128506 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.070878) * (y 0) + (-0.003287) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.033394

theorem c57_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c57_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.070878) * y1 + (-0.003287) * (y2 + y3 + y5 + y6) + 0.033394 :=
  rfl

/-- Component 57 gate (box 10; chain chain_idx57; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c57_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b10lo j) (b10hi j)) →
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => c57_mfuna (Function.update y i t) - K57 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B57 ≤ c57_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.070878) * y1 + (-0.003287) * (y2 + y3 + y5 + y6) + 0.033394 > 0 := by
  have hpos : (0 : ℝ) <
      B57 - ∑ i, R57 i := by
    rw [sumFin6a]
    have e0 : R57 0 = (0 : ℝ) := by rfl
    have e1 : R57 1 = (0 : ℝ) := by rfl
    have e2 : R57 2 = (0 : ℝ) := by rfl
    have e3 : R57 3 = (0 : ℝ) := by rfl
    have e4 : R57 4 = (0 : ℝ) := by rfl
    have e5 : R57 5 = (0 : ℝ) := by rfl
    have eb : B57 = ((2411278762556442976863527/450359962737049600000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b10lo j) (b10hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b10lo, b10hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K57 i := by
    intro i; fin_cases i <;> norm_num [K57]
  have hR0 : ∀ i, 0 ≤ R57 i := by
    intro i; fin_cases i <;> norm_num [R57, K57, b10lo, b10hi]
  have hchain := chain_idx57 c57_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c57_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 58 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c58_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.128506 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.097658) * (y 0) + 0.003287 * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.050047

theorem c58_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c58_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.097658) * y1 + 0.003287 * (y2 + y3 + y5 + y6) + 0.050047 :=
  rfl

/-- Component 58 gate (box 10; chain chain_idx58; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c58_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b10lo j) (b10hi j)) →
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => c58_mfuna (Function.update y i t) - K58 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B58 ≤ c58_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.097658) * y1 + 0.003287 * (y2 + y3 + y5 + y6) + 0.050047 > 0 := by
  have hpos : (0 : ℝ) <
      B58 - ∑ i, R58 i := by
    rw [sumFin6a]
    have e0 : R58 0 = (0 : ℝ) := by rfl
    have e1 : R58 1 = (0 : ℝ) := by rfl
    have e2 : R58 2 = (0 : ℝ) := by rfl
    have e3 : R58 3 = (0 : ℝ) := by rfl
    have e4 : R58 4 = (0 : ℝ) := by rfl
    have e5 : R58 5 = (0 : ℝ) := by rfl
    have eb : B58 = ((1932823063922836623361699/360287970189639680000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b10lo j) (b10hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b10lo, b10hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K58 i := by
    intro i; fin_cases i <;> norm_num [K58]
  have hR0 : ∀ i, 0 ≤ R58 i := by
    intro i; fin_cases i <;> norm_num [R58, K58, b10lo, b10hi]
  have hchain := chain_idx58 c58_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c58_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 59 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c59_mfuna (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.128506 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.121835) * (y 0) + (-0.003287) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.13571

theorem c59_mfuna_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c59_mfuna ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.121835) * y1 + (-0.003287) * (y2 + y3 + y5 + y6) + 0.13571 :=
  rfl

/-- Component 59 gate (box 11; chain chain_idx59; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c59_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b11lo j) (b11hi j)) →
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => c59_mfuna (Function.update y i t) - K59 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B59 ≤ c59_mfuna v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 2 + 3 / 2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.121835) * y1 + (-0.003287) * (y2 + y3 + y5 + y6) + 0.13571 > 0 := by
  have hpos : (0 : ℝ) <
      B59 - ∑ i, R59 i := by
    rw [sumFin6a]
    have e0 : R59 0 = (0 : ℝ) := by rfl
    have e1 : R59 1 = (0 : ℝ) := by rfl
    have e2 : R59 2 = (0 : ℝ) := by rfl
    have e3 : R59 3 = (0 : ℝ) := by rfl
    have e4 : R59 4 = (0 : ℝ) := by rfl
    have e5 : R59 5 = (0 : ℝ) := by rfl
    have eb : B59 = ((96477166132911695178113/18014398509481984000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b11lo j) (b11hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b11lo, b11hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K59 i := by
    intro i; fin_cases i <;> norm_num [K59]
  have hR0 : ∀ i, 0 ≤ R59 i := by
    intro i; fin_cases i <;> norm_num [R59, K59, b11lo, b11hi]
  have hchain := chain_idx59 c59_mfuna hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c59_mfuna_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-! ### Axiom audit -/

#print axioms c0_gate

#print axioms c1_gate

#print axioms c2_gate

#print axioms c3_gate

#print axioms c4_gate

#print axioms c5_gate

#print axioms c6_gate

#print axioms c7_gate

#print axioms c8_gate

#print axioms c9_gate

#print axioms c10_gate

#print axioms c11_gate

#print axioms c12_gate

#print axioms c13_gate

#print axioms c14_gate

#print axioms c15_gate

#print axioms c16_gate

#print axioms c17_gate

#print axioms c18_gate

#print axioms c19_gate

#print axioms c20_gate

#print axioms c21_gate

#print axioms c22_gate

#print axioms c23_gate

#print axioms c24_gate

#print axioms c25_gate

#print axioms c26_gate

#print axioms c27_gate

#print axioms c28_gate

#print axioms c29_gate

#print axioms c30_gate

#print axioms c31_gate

#print axioms c32_gate

#print axioms c33_gate

#print axioms c34_gate

#print axioms c35_gate

#print axioms c36_gate

#print axioms c37_gate

#print axioms c38_gate

#print axioms c39_gate

#print axioms c40_gate

#print axioms c41_gate

#print axioms c42_gate

#print axioms c43_gate

#print axioms c44_gate

#print axioms c45_gate

#print axioms c46_gate

#print axioms c47_gate

#print axioms c48_gate

#print axioms c49_gate

#print axioms c50_gate

#print axioms c51_gate

#print axioms c52_gate

#print axioms c53_gate

#print axioms c54_gate

#print axioms c55_gate

#print axioms c56_gate

#print axioms c57_gate

#print axioms c58_gate

#print axioms c59_gate

end Kepler.Text
