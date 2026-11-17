/-
Ox3q1hGateBatch: S4 per-conjunct gates, components 60-119 (of 230; LIN = idx ≡ 0 mod 5).
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
import Kepler.Text.Ox3q1hChainSplit1
import Kepler.Text.Ox3q1hChainSplitKit

open Set Filter Topology

namespace Kepler.Text

/-- Fin-6 sum as explicit addition (Mathlib Fin.sum_univ_six alias for reuse). -/
theorem sumFin6b (f : Fin 6 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_six]

/-- Component 60 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c60_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.128506 + (0.263591 + (-0.070878) + (-0.121835) + (-0.070878)) * y1 + 2 * (0.003287 + (-0.003287)) * y12 + 2 * ((-0.003287) + 0.003287) * y23 + 2 * (0.003287 + (-0.003287)) * y34 + 2 * ((-0.003287) + 0.003287) * y41 + ((-0.957343) + 0.033394 + 0.083125 + 0.033394) < 0 :=
  ox3q1hLin_060

/-- Margin function of conjunct 61 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c61_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.128506 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.263591 * (y 0) + 0.003287 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.957343)

theorem c61_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c61_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + 0.263591 * y1 + 0.003287 * (y2 + y3 + y5 + y6) + (-0.957343) :=
  rfl

/-- Component 61 gate (box 9; S4.5 split-grid chain
`chain_split_idx61`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
3; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c61_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit61 i →
      ConcaveOn ℝ (Set.Icc (gsplit61 i k) (gsplit61 i (k + 1)))
        (fun t => c61_mfunb (Function.update y i t) - K61 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split61 j) → B61 ≤ c61_mfunb v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + 0.263591 * y1 + 0.003287 * (y2 + y3 + y5 + y6) + (-0.957343) > 0 := by
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
  have hchain := chain_split_idx61 c61_mfunb hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c61_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx61
  linarith [hchain, hpos]

/-- Margin function of conjunct 62 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c62_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.128506 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.070878) * (y 0) + (-0.003287) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.033394

theorem c62_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c62_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.070878) * y1 + (-0.003287) * (y2 + y3 + y5 + y6) + 0.033394 :=
  rfl

/-- Component 62 gate (box 10; chain chain_idx62; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c62_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => c62_mfunb (Function.update y i t) - K62 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B62 ≤ c62_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.070878) * y1 + (-0.003287) * (y2 + y3 + y5 + y6) + 0.033394 > 0 := by
  have hpos : (0 : ℝ) <
      B62 - ∑ i, R62 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R62 i = K62 i * (b10hi i - b10lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K62 0 = (0 : ℝ) := by rfl
    have t1 : K62 1 = (0 : ℝ) := by rfl
    have t2 : K62 2 = (0 : ℝ) := by rfl
    have t3 : K62 3 = (0 : ℝ) := by rfl
    have t4 : K62 4 = (0 : ℝ) := by rfl
    have t5 : K62 5 = (0 : ℝ) := by rfl
    have u0 : b10hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b10lo 0 = (12927/5000 : ℝ) := by rfl
    have u1 : b10hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b10lo 1 = (2 : ℝ) := by rfl
    have u2 : b10hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b10lo 2 = (2 : ℝ) := by rfl
    have u3 : b10hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : b10lo 3 = (2 : ℝ) := by rfl
    have u4 : b10hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b10lo 4 = (2 : ℝ) := by rfl
    have u5 : b10hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b10lo 5 = (2 : ℝ) := by rfl
    have eb : B62 = ((2411278762556442976863527/450359962737049600000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
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
  have hK0 : ∀ i, 0 ≤ K62 i := by
    intro i; fin_cases i <;> norm_num [K62]
  have hR0 : ∀ i, 0 ≤ R62 i := by
    intro i; fin_cases i <;> norm_num [R62, K62, b10lo, b10hi]
  have hchain := chain_idx62 c62_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c62_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 63 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c63_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.128506 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.121835) * (y 0) + 0.003287 * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.083125

theorem c63_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c63_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.121835) * y1 + 0.003287 * (y2 + y3 + y5 + y6) + 0.083125 :=
  rfl

/-- Component 63 gate (box 11; chain chain_idx63; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c63_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => c63_mfunb (Function.update y i t) - K63 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B63 ≤ c63_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 2 + 3 / 2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.121835) * y1 + 0.003287 * (y2 + y3 + y5 + y6) + 0.083125 > 0 := by
  have hpos : (0 : ℝ) <
      B63 - ∑ i, R63 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R63 i = K63 i * (b11hi i - b11lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K63 0 = (0 : ℝ) := by rfl
    have t1 : K63 1 = (0 : ℝ) := by rfl
    have t2 : K63 2 = (0 : ℝ) := by rfl
    have t3 : K63 3 = (0 : ℝ) := by rfl
    have t4 : K63 4 = (0 : ℝ) := by rfl
    have t5 : K63 5 = (0 : ℝ) := by rfl
    have u0 : b11hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b11lo 0 = (12927/5000 : ℝ) := by rfl
    have u1 : b11hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b11lo 1 = (2 : ℝ) := by rfl
    have u2 : b11hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b11lo 2 = (2 : ℝ) := by rfl
    have u3 : b11hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : b11lo 3 = (16927/8000 : ℝ) := by rfl
    have u4 : b11hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b11lo 4 = (2 : ℝ) := by rfl
    have u5 : b11hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b11lo 5 = (2 : ℝ) := by rfl
    have eb : B63 = ((96603266922478069066113/18014398509481984000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
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
  have hK0 : ∀ i, 0 ≤ K63 i := by
    intro i; fin_cases i <;> norm_num [K63]
  have hR0 : ∀ i, 0 ≤ R63 i := by
    intro i; fin_cases i <;> norm_num [R63, K63, b11lo, b11hi]
  have hchain := chain_idx63 c63_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c63_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 64 gate (box 12; chain chain_idx64; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c64_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => c62_mfunb (Function.update y i t) - K64 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B64 ≤ c62_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.070878) * y1 + (-0.003287) * (y2 + y3 + y5 + y6) + 0.033394 > 0 := by
  have hpos : (0 : ℝ) <
      B64 - ∑ i, R64 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R64 i = K64 i * (b12hi i - b12lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K64 0 = (0 : ℝ) := by rfl
    have t1 : K64 1 = (0 : ℝ) := by rfl
    have t2 : K64 2 = (0 : ℝ) := by rfl
    have t3 : K64 3 = (0 : ℝ) := by rfl
    have t4 : K64 4 = (0 : ℝ) := by rfl
    have t5 : K64 5 = (0 : ℝ) := by rfl
    have u0 : b12hi 0 = ((6627/2500) : ℝ) := by rfl
    have q0 : b12lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b12hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b12lo 1 = (2 : ℝ) := by rfl
    have u2 : b12hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b12lo 2 = (2 : ℝ) := by rfl
    have u3 : b12hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b12lo 3 = (2 : ℝ) := by rfl
    have u4 : b12hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b12lo 4 = (2 : ℝ) := by rfl
    have u5 : b12hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b12lo 5 = (2 : ℝ) := by rfl
    have eb : B64 = ((2411278762556442976863527/450359962737049600000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b12lo j) (b12hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b12lo, b12hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K64 i := by
    intro i; fin_cases i <;> norm_num [K64]
  have hR0 : ∀ i, 0 ≤ R64 i := by
    intro i; fin_cases i <;> norm_num [R64, K64, b12lo, b12hi]
  have hchain := chain_idx64 c62_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c62_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 65 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c65_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.128506 + ((-0.066254) + 0.234791 + (-0.097658) + (-0.070878)) * y1 + 2 * (0.003287 + (-0.003287)) * y12 + 2 * ((-0.003287) + 0.003287) * y23 + 2 * (0.003287 + (-0.003287)) * y34 + 2 * ((-0.003287) + 0.003287) * y41 + ((-0.104563) + (-0.786309) + 0.050047 + 0.033394) < 0 :=
  ox3q1hLin_065

/-- Margin function of conjunct 66 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c66_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.128506 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.066254) * (y 0) + 0.003287 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.104563)

theorem c66_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c66_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.066254) * y1 + 0.003287 * (y2 + y3 + y5 + y6) + (-0.104563) :=
  rfl

/-- Component 66 gate (box 9; S4.5 split-grid chain
`chain_split_idx66`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
3; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c66_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit66 i →
      ConcaveOn ℝ (Set.Icc (gsplit66 i k) (gsplit66 i (k + 1)))
        (fun t => c66_mfunb (Function.update y i t) - K66 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split66 j) → B66 ≤ c66_mfunb v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.066254) * y1 + 0.003287 * (y2 + y3 + y5 + y6) + (-0.104563) > 0 := by
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
  have hchain := chain_split_idx66 c66_mfunb hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c66_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx66
  linarith [hchain, hpos]

/-- Margin function of conjunct 67 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c67_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.128506 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.234791 * (y 0) + (-0.003287) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.786309)

theorem c67_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c67_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + 0.234791 * y1 + (-0.003287) * (y2 + y3 + y5 + y6) + (-0.786309) :=
  rfl

/-- Component 67 gate (box 11; chain chain_idx67; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c67_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => c67_mfunb (Function.update y i t) - K67 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B67 ≤ c67_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 2 + 3 / 2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + 0.234791 * y1 + (-0.003287) * (y2 + y3 + y5 + y6) + (-0.786309) > 0 := by
  have hpos : (0 : ℝ) <
      B67 - ∑ i, R67 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R67 i = K67 i * (b11hi i - b11lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K67 0 = (0 : ℝ) := by rfl
    have t1 : K67 1 = (0 : ℝ) := by rfl
    have t2 : K67 2 = (0 : ℝ) := by rfl
    have t3 : K67 3 = (0 : ℝ) := by rfl
    have t4 : K67 4 = (0 : ℝ) := by rfl
    have t5 : K67 5 = (0 : ℝ) := by rfl
    have u0 : b11hi 0 = (6627/2500 : ℝ) := by rfl
    have q0 : b11lo 0 = (12927/5000 : ℝ) := by rfl
    have u1 : b11hi 1 = (15397/6250 : ℝ) := by rfl
    have q1 : b11lo 1 = (2 : ℝ) := by rfl
    have u2 : b11hi 2 = (15397/6250 : ℝ) := by rfl
    have q2 : b11lo 2 = (2 : ℝ) := by rfl
    have u3 : b11hi 3 = (27897/12500 : ℝ) := by rfl
    have q3 : b11lo 3 = (16927/8000 : ℝ) := by rfl
    have u4 : b11hi 4 = (15397/6250 : ℝ) := by rfl
    have q4 : b11lo 4 = (2 : ℝ) := by rfl
    have u5 : b11hi 5 = (15397/6250 : ℝ) := by rfl
    have q5 : b11lo 5 = (2 : ℝ) := by rfl
    have eb : B67 = ((965116392831417524879401/180143985094819840000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
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
  have hK0 : ∀ i, 0 ≤ K67 i := by
    intro i; fin_cases i <;> norm_num [K67]
  have hR0 : ∀ i, 0 ≤ R67 i := by
    intro i; fin_cases i <;> norm_num [R67, K67, b11lo, b11hi]
  have hchain := chain_idx67 c67_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c67_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 68 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c68_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.128506 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.097658) * (y 0) + 0.003287 * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.050047

theorem c68_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c68_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.097658) * y1 + 0.003287 * (y2 + y3 + y5 + y6) + 0.050047 :=
  rfl

/-- Component 68 gate (box 12; chain chain_idx68; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c68_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => c68_mfunb (Function.update y i t) - K68 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B68 ≤ c68_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.097658) * y1 + 0.003287 * (y2 + y3 + y5 + y6) + 0.050047 > 0 := by
  have hpos : (0 : ℝ) <
      B68 - ∑ i, R68 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R68 i = K68 i * (b12hi i - b12lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K68 0 = (0 : ℝ) := by rfl
    have t1 : K68 1 = (0 : ℝ) := by rfl
    have t2 : K68 2 = (0 : ℝ) := by rfl
    have t3 : K68 3 = (0 : ℝ) := by rfl
    have t4 : K68 4 = (0 : ℝ) := by rfl
    have t5 : K68 5 = (0 : ℝ) := by rfl
    have u0 : b12hi 0 = ((6627/2500) : ℝ) := by rfl
    have q0 : b12lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b12hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b12lo 1 = (2 : ℝ) := by rfl
    have u2 : b12hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b12lo 2 = (2 : ℝ) := by rfl
    have u3 : b12hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b12lo 3 = (2 : ℝ) := by rfl
    have u4 : b12hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b12lo 4 = (2 : ℝ) := by rfl
    have u5 : b12hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b12lo 5 = (2 : ℝ) := by rfl
    have eb : B68 = ((1932823063922836623361699/360287970189639680000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b12lo j) (b12hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b12lo, b12hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K68 i := by
    intro i; fin_cases i <;> norm_num [K68]
  have hR0 : ∀ i, 0 ≤ R68 i := by
    intro i; fin_cases i <;> norm_num [R68, K68, b12lo, b12hi]
  have hchain := chain_idx68 c68_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c68_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 69 gate (box 12; chain chain_idx69; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c69_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => c62_mfunb (Function.update y i t) - K69 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B69 ≤ c62_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.128506 * dihY y1 y2 y3 y4 y5 y6 + (-0.070878) * y1 + (-0.003287) * (y2 + y3 + y5 + y6) + 0.033394 > 0 := by
  have hpos : (0 : ℝ) <
      B69 - ∑ i, R69 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R69 i = K69 i * (b12hi i - b12lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K69 0 = (0 : ℝ) := by rfl
    have t1 : K69 1 = (0 : ℝ) := by rfl
    have t2 : K69 2 = (0 : ℝ) := by rfl
    have t3 : K69 3 = (0 : ℝ) := by rfl
    have t4 : K69 4 = (0 : ℝ) := by rfl
    have t5 : K69 5 = (0 : ℝ) := by rfl
    have u0 : b12hi 0 = ((6627/2500) : ℝ) := by rfl
    have q0 : b12lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b12hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b12lo 1 = (2 : ℝ) := by rfl
    have u2 : b12hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b12lo 2 = (2 : ℝ) := by rfl
    have u3 : b12hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b12lo 3 = (2 : ℝ) := by rfl
    have u4 : b12hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b12lo 4 = (2 : ℝ) := by rfl
    have u5 : b12hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b12lo 5 = (2 : ℝ) := by rfl
    have eb : B69 = ((2411278762556442976863527/450359962737049600000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b12lo j) (b12hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b12lo, b12hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K69 i := by
    intro i; fin_cases i <;> norm_num [K69]
  have hR0 : ∀ i, 0 ≤ R69 i := by
    intro i; fin_cases i <;> norm_num [R69, K69, b12lo, b12hi]
  have hchain := chain_idx69 c62_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c62_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 70 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c70_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.127166 + ((-0.07331) + 0.23984 + (-0.096981) + (-0.069548)) * y1 + 2 * (0.003788 + (-0.003788)) * y12 + 2 * ((-0.003788) + 0.003788) * y23 + 2 * (0.003788 + (-0.003788)) * y34 + 2 * ((-0.003788) + 0.003788) * y41 + ((-0.105909) + (-0.767737) + 0.04248 + 0.032155) < 0 :=
  ox3q1hLin_070

/-- Margin function of conjunct 71 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c71_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.127166 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.07331) * (y 0) + 0.003788 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.105909)

theorem c71_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c71_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.127166 * dihY y1 y2 y3 y4 y5 y6 + (-0.07331) * y1 + 0.003788 * (y2 + y3 + y5 + y6) + (-0.105909) :=
  rfl

/-- Component 71 gate (box 13; S4.5 split-grid chain
`chain_split_idx71`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
5; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c71_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit71 i →
      ConcaveOn ℝ (Set.Icc (gsplit71 i k) (gsplit71 i (k + 1)))
        (fun t => c71_mfunb (Function.update y i t) - K71 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split71 j) → B71 ≤ c71_mfunb v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (h0 + hplus) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.127166 * dihY y1 y2 y3 y4 y5 y6 + (-0.07331) * y1 + 0.003788 * (y2 + y3 + y5 + y6) + (-0.105909) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b13lo j) (b13hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b13lo, b13hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx71 c71_mfunb hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c71_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx71
  linarith [hchain, hpos]

/-- Margin function of conjunct 72 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c72_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.127166 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.23984 * (y 0) + (-0.003788) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.767737)

theorem c72_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c72_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.127166 * dihY y1 y2 y3 y4 y5 y6 + 0.23984 * y1 + (-0.003788) * (y2 + y3 + y5 + y6) + (-0.767737) :=
  rfl

/-- Component 72 gate (box 12; chain chain_idx72; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c72_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => c72_mfunb (Function.update y i t) - K72 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B72 ≤ c72_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.127166 * dihY y1 y2 y3 y4 y5 y6 + 0.23984 * y1 + (-0.003788) * (y2 + y3 + y5 + y6) + (-0.767737) > 0 := by
  have hpos : (0 : ℝ) <
      B72 - ∑ i, R72 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R72 i = K72 i * (b12hi i - b12lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K72 0 = (0 : ℝ) := by rfl
    have t1 : K72 1 = (0 : ℝ) := by rfl
    have t2 : K72 2 = (0 : ℝ) := by rfl
    have t3 : K72 3 = (0 : ℝ) := by rfl
    have t4 : K72 4 = (0 : ℝ) := by rfl
    have t5 : K72 5 = (0 : ℝ) := by rfl
    have u0 : b12hi 0 = ((6627/2500) : ℝ) := by rfl
    have q0 : b12lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b12hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b12lo 1 = (2 : ℝ) := by rfl
    have u2 : b12hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b12lo 2 = (2 : ℝ) := by rfl
    have u3 : b12hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b12lo 3 = (2 : ℝ) := by rfl
    have u4 : b12hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b12lo 4 = (2 : ℝ) := by rfl
    have u5 : b12hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b12lo 5 = (2 : ℝ) := by rfl
    have eb : B72 = ((2939589470258301474704291/1801439850948198400000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b12lo j) (b12hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b12lo, b12hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K72 i := by
    intro i; fin_cases i <;> norm_num [K72]
  have hR0 : ∀ i, 0 ≤ R72 i := by
    intro i; fin_cases i <;> norm_num [R72, K72, b12lo, b12hi]
  have hchain := chain_idx72 c72_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c72_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 73 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c73_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.127166 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.096981) * (y 0) + 0.003788 * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.04248

theorem c73_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c73_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.127166 * dihY y1 y2 y3 y4 y5 y6 + (-0.096981) * y1 + 0.003788 * (y2 + y3 + y5 + y6) + 0.04248 :=
  rfl

/-- Component 73 gate (box 12; chain chain_idx73; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c73_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => c73_mfunb (Function.update y i t) - K73 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B73 ≤ c73_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.127166 * dihY y1 y2 y3 y4 y5 y6 + (-0.096981) * y1 + 0.003788 * (y2 + y3 + y5 + y6) + 0.04248 > 0 := by
  have hpos : (0 : ℝ) <
      B73 - ∑ i, R73 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R73 i = K73 i * (b12hi i - b12lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K73 0 = (0 : ℝ) := by rfl
    have t1 : K73 1 = (0 : ℝ) := by rfl
    have t2 : K73 2 = (0 : ℝ) := by rfl
    have t3 : K73 3 = (0 : ℝ) := by rfl
    have t4 : K73 4 = (0 : ℝ) := by rfl
    have t5 : K73 5 = (0 : ℝ) := by rfl
    have u0 : b12hi 0 = ((6627/2500) : ℝ) := by rfl
    have q0 : b12lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b12hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b12lo 1 = (2 : ℝ) := by rfl
    have u2 : b12hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b12lo 2 = (2 : ℝ) := by rfl
    have u3 : b12hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b12lo 3 = (2 : ℝ) := by rfl
    have u4 : b12hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b12lo 4 = (2 : ℝ) := by rfl
    have u5 : b12hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b12lo 5 = (2 : ℝ) := by rfl
    have eb : B73 = ((591232786076284384171393/360287970189639680000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b12lo j) (b12hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b12lo, b12hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K73 i := by
    intro i; fin_cases i <;> norm_num [K73]
  have hR0 : ∀ i, 0 ≤ R73 i := by
    intro i; fin_cases i <;> norm_num [R73, K73, b12lo, b12hi]
  have hchain := chain_idx73 c73_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c73_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 74 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c74_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.127166 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.069548) * (y 0) + (-0.003788) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.032155

theorem c74_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c74_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.127166 * dihY y1 y2 y3 y4 y5 y6 + (-0.069548) * y1 + (-0.003788) * (y2 + y3 + y5 + y6) + 0.032155 :=
  rfl

/-- Component 74 gate (box 12; chain chain_idx74; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c74_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => c74_mfunb (Function.update y i t) - K74 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B74 ≤ c74_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.127166 * dihY y1 y2 y3 y4 y5 y6 + (-0.069548) * y1 + (-0.003788) * (y2 + y3 + y5 + y6) + 0.032155 > 0 := by
  have hpos : (0 : ℝ) <
      B74 - ∑ i, R74 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R74 i = K74 i * (b12hi i - b12lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K74 0 = (0 : ℝ) := by rfl
    have t1 : K74 1 = (0 : ℝ) := by rfl
    have t2 : K74 2 = (0 : ℝ) := by rfl
    have t3 : K74 3 = (0 : ℝ) := by rfl
    have t4 : K74 4 = (0 : ℝ) := by rfl
    have t5 : K74 5 = (0 : ℝ) := by rfl
    have u0 : b12hi 0 = ((6627/2500) : ℝ) := by rfl
    have q0 : b12lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b12hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b12lo 1 = (2 : ℝ) := by rfl
    have u2 : b12hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b12lo 2 = (2 : ℝ) := by rfl
    have u3 : b12hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b12lo 3 = (2 : ℝ) := by rfl
    have u4 : b12hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b12lo 4 = (2 : ℝ) := by rfl
    have u5 : b12hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b12lo 5 = (2 : ℝ) := by rfl
    have eb : B74 = ((734387772039426955678493/450359962737049600000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b12lo j) (b12hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b12lo, b12hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K74 i := by
    intro i; fin_cases i <;> norm_num [K74]
  have hR0 : ∀ i, 0 ≤ R74 i := by
    intro i; fin_cases i <;> norm_num [R74, K74, b12lo, b12hi]
  have hchain := chain_idx74 c74_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c74_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 75 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c75_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.126777 + ((-0.053069) + 0.196466 + (-0.093532) + (-0.049865)) * y1 + 2 * (0.003525 + (-0.003525)) * y12 + 2 * ((-0.003525) + 0.003525) * y23 + 2 * (0.003525 + (-0.003525)) * y34 + 2 * ((-0.003525) + 0.003525) * y41 + ((-0.142652) + (-0.667227) + 0.035622 + (-0.022307)) < 0 :=
  ox3q1hLin_075

/-- Margin function of conjunct 76 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c76_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.126777 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.053069) * (y 0) + 0.003525 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.142652)

theorem c76_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c76_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.126777 * dihY y1 y2 y3 y4 y5 y6 + (-0.053069) * y1 + 0.003525 * (y2 + y3 + y5 + y6) + (-0.142652) :=
  rfl

/-- Component 76 gate (box 14; S4.5 split-grid chain
`chain_split_idx76`, split factors per SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min =
5; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c76_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit76 i →
      ConcaveOn ℝ (Set.Icc (gsplit76 i k) (gsplit76 i (k + 1)))
        (fun t => c76_mfunb (Function.update y i t) - b3K76 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split76 j) → b3B76 ≤ c76_mfunb v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (h0 + hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.126777 * dihY y1 y2 y3 y4 y5 y6 + (-0.053069) * y1 + 0.003525 * (y2 + y3 + y5 + y6) + (-0.142652) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b14lo j) (b14hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b14lo, b14hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx76 c76_mfunb hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c76_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx76
  linarith [hchain, hpos]

/-- Margin function of conjunct 77 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c77_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.126777 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.196466 * (y 0) + (-0.003525) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.667227)

theorem c77_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c77_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.126777 * dihY y1 y2 y3 y4 y5 y6 + 0.196466 * y1 + (-0.003525) * (y2 + y3 + y5 + y6) + (-0.667227) :=
  rfl

/-- Component 77 gate (box 15; chain chain_idx77; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c77_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => c77_mfunb (Function.update y i t) - K77 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B77 ≤ c77_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.126777 * dihY y1 y2 y3 y4 y5 y6 + 0.196466 * y1 + (-0.003525) * (y2 + y3 + y5 + y6) + (-0.667227) > 0 := by
  have hpos : (0 : ℝ) <
      B77 - ∑ i, R77 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R77 i = K77 i * (b15hi i - b15lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K77 0 = (0 : ℝ) := by rfl
    have t1 : K77 1 = (0 : ℝ) := by rfl
    have t2 : K77 2 = (0 : ℝ) := by rfl
    have t3 : K77 3 = (0 : ℝ) := by rfl
    have t4 : K77 4 = (0 : ℝ) := by rfl
    have t5 : K77 5 = (0 : ℝ) := by rfl
    have u0 : b15hi 0 = ((6627/2500) : ℝ) := by rfl
    have q0 : b15lo 0 = ((26181/10000) : ℝ) := by rfl
    have u1 : b15hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b15lo 1 = (2 : ℝ) := by rfl
    have u2 : b15hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b15lo 2 = (2 : ℝ) := by rfl
    have u3 : b15hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b15lo 3 = (2 : ℝ) := by rfl
    have u4 : b15hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b15lo 4 = (2 : ℝ) := by rfl
    have u5 : b15hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b15lo 5 = (2 : ℝ) := by rfl
    have eb : B77 = ((224290941405761395729149/180143985094819840000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b15lo j) (b15hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b15lo, b15hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K77 i := by
    intro i; fin_cases i <;> norm_num [K77]
  have hR0 : ∀ i, 0 ≤ R77 i := by
    intro i; fin_cases i <;> norm_num [R77, K77, b15lo, b15hi]
  have hchain := chain_idx77 c77_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c77_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 78 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c78_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.126777 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.093532) * (y 0) + 0.003525 * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.035622

theorem c78_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c78_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.126777 * dihY y1 y2 y3 y4 y5 y6 + (-0.093532) * y1 + 0.003525 * (y2 + y3 + y5 + y6) + 0.035622 :=
  rfl

/-- Component 78 gate (box 15; chain chain_idx78; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c78_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => c78_mfunb (Function.update y i t) - K78 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B78 ≤ c78_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.126777 * dihY y1 y2 y3 y4 y5 y6 + (-0.093532) * y1 + 0.003525 * (y2 + y3 + y5 + y6) + 0.035622 > 0 := by
  have hpos : (0 : ℝ) <
      B78 - ∑ i, R78 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R78 i = K78 i * (b15hi i - b15lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K78 0 = (0 : ℝ) := by rfl
    have t1 : K78 1 = (0 : ℝ) := by rfl
    have t2 : K78 2 = (0 : ℝ) := by rfl
    have t3 : K78 3 = (0 : ℝ) := by rfl
    have t4 : K78 4 = (0 : ℝ) := by rfl
    have t5 : K78 5 = (0 : ℝ) := by rfl
    have u0 : b15hi 0 = ((6627/2500) : ℝ) := by rfl
    have q0 : b15lo 0 = ((26181/10000) : ℝ) := by rfl
    have u1 : b15hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b15lo 1 = (2 : ℝ) := by rfl
    have u2 : b15hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b15lo 2 = (2 : ℝ) := by rfl
    have u3 : b15hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b15lo 3 = (2 : ℝ) := by rfl
    have u4 : b15hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b15lo 4 = (2 : ℝ) := by rfl
    have u5 : b15hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b15lo 5 = (2 : ℝ) := by rfl
    have eb : B78 = ((902784802057526008673009/720575940379279360000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b15lo j) (b15hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b15lo, b15hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K78 i := by
    intro i; fin_cases i <;> norm_num [K78]
  have hR0 : ∀ i, 0 ≤ R78 i := by
    intro i; fin_cases i <;> norm_num [R78, K78, b15lo, b15hi]
  have hchain := chain_idx78 c78_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c78_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 79 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c79_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.126777 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.049865) * (y 0) + (-0.003525) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.022307)

theorem c79_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c79_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.126777 * dihY y1 y2 y3 y4 y5 y6 + (-0.049865) * y1 + (-0.003525) * (y2 + y3 + y5 + y6) + (-0.022307) :=
  rfl

/-- Component 79 gate (box 15; chain chain_idx79; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c79_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => c79_mfunb (Function.update y i t) - K79 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B79 ≤ c79_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.126777 * dihY y1 y2 y3 y4 y5 y6 + (-0.049865) * y1 + (-0.003525) * (y2 + y3 + y5 + y6) + (-0.022307) > 0 := by
  have hpos : (0 : ℝ) <
      B79 - ∑ i, R79 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R79 i = K79 i * (b15hi i - b15lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K79 0 = (0 : ℝ) := by rfl
    have t1 : K79 1 = (0 : ℝ) := by rfl
    have t2 : K79 2 = (0 : ℝ) := by rfl
    have t3 : K79 3 = (0 : ℝ) := by rfl
    have t4 : K79 4 = (0 : ℝ) := by rfl
    have t5 : K79 5 = (0 : ℝ) := by rfl
    have u0 : b15hi 0 = ((6627/2500) : ℝ) := by rfl
    have q0 : b15lo 0 = ((26181/10000) : ℝ) := by rfl
    have u1 : b15hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b15lo 1 = (2 : ℝ) := by rfl
    have u2 : b15hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b15lo 2 = (2 : ℝ) := by rfl
    have u3 : b15hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b15lo 3 = (2 : ℝ) := by rfl
    have u4 : b15hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b15lo 4 = (2 : ℝ) := by rfl
    have u5 : b15hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b15lo 5 = (2 : ℝ) := by rfl
    have eb : B79 = ((44885544409492759765531/36028797018963968000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b15lo j) (b15hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b15lo, b15hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K79 i := by
    intro i; fin_cases i <;> norm_num [K79]
  have hR0 : ∀ i, 0 ≤ R79 i := by
    intro i; fin_cases i <;> norm_num [R79, K79, b15lo, b15hi]
  have hchain := chain_idx79 c79_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c79_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 80 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c80_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.014413) + (-0.014413) + (-0.02241)) * y1 + 2 * (0.060747 + (-0.060747)) * y12 + 2 * ((-0.060747) + 0.060747) * y23 + 2 * (0.060747 + (-0.060747)) * y34 + 2 * ((-0.060747) + 0.060747) * y41 + ((-0.530637) + 0.594377 + (-0.377571) + 0.608509) < 0 :=
  ox3q1hLin_080

/-- Margin function of conjunct 81 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c81_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.051237 * (y 0) + 0.060747 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.530637)

theorem c81_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c81_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.530637) :=
  rfl

/-- Component 81 gate (box 16; chain chain_idx81; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c81_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b16lo i) (b16hi i))
        (fun t => c81_mfunb (Function.update y i t) - K81 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb16 j) → B81 ≤ c81_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (h0 + hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.530637) > 0 := by
  have hpos : (0 : ℝ) <
      B81 - ∑ i, R81 i := by
    rw [sumFin6b]
    have e0 : R81 0 = (0 : ℝ) := by rfl
    have e1 : R81 1 = (0 : ℝ) := by rfl
    have e2 : R81 2 = (0 : ℝ) := by rfl
    have e3 : R81 3 = ((2584402081090101/8796093022208000000) : ℝ) := by rfl
    have e4 : R81 4 = (0 : ℝ) := by rfl
    have e5 : R81 5 = (0 : ℝ) := by rfl
    have eb : B81 = ((177643353933028257987441/90071992547409920000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b16lo j) (b16hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b16lo, b16hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K81 i := by
    intro i; fin_cases i <;> norm_num [K81]
  have hR0 : ∀ i, 0 ≤ R81 i := by
    intro i; fin_cases i <;> norm_num [R81, K81, b16lo, b16hi]
  have hchain := chain_idx81 c81_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c81_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 82 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c82_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.014413) * (y 0) + (-0.060747) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.594377

theorem c82_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c82_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.594377 :=
  rfl

/-- Component 82 gate (box 17; chain chain_idx82; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c82_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => c82_mfunb (Function.update y i t) - K82 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B82 ≤ c82_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.594377 > 0 := by
  have hpos : (0 : ℝ) <
      B82 - ∑ i, R82 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R82 i = K82 i * (b17hi i - b17lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K82 0 = (0 : ℝ) := by rfl
    have t1 : K82 1 = (0 : ℝ) := by rfl
    have t2 : K82 2 = (0 : ℝ) := by rfl
    have t3 : K82 3 = (0 : ℝ) := by rfl
    have t4 : K82 4 = (0 : ℝ) := by rfl
    have t5 : K82 5 = (0 : ℝ) := by rfl
    have u0 : b17hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b17lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b17hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b17lo 1 = (2 : ℝ) := by rfl
    have u2 : b17hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b17lo 2 = (2 : ℝ) := by rfl
    have u3 : b17hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b17lo 3 = (2 : ℝ) := by rfl
    have u4 : b17hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b17lo 4 = (2 : ℝ) := by rfl
    have u5 : b17hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b17lo 5 = (2 : ℝ) := by rfl
    have eb : B82 = ((1775586001116581819034139/900719925474099200000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b17lo j) (b17hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b17lo, b17hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K82 i := by
    intro i; fin_cases i <;> norm_num [K82]
  have hR0 : ∀ i, 0 ≤ R82 i := by
    intro i; fin_cases i <;> norm_num [R82, K82, b17lo, b17hi]
  have hchain := chain_idx82 c82_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c82_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 83 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c83_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.014413) * (y 0) + 0.060747 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.377571)

theorem c83_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c83_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.377571) :=
  rfl

/-- Component 83 gate (box 17; chain chain_idx83; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c83_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => c83_mfunb (Function.update y i t) - K83 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B83 ≤ c83_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.377571) > 0 := by
  have hpos : (0 : ℝ) <
      B83 - ∑ i, R83 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R83 i = K83 i * (b17hi i - b17lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K83 0 = (0 : ℝ) := by rfl
    have t1 : K83 1 = (0 : ℝ) := by rfl
    have t2 : K83 2 = (0 : ℝ) := by rfl
    have t3 : K83 3 = (0 : ℝ) := by rfl
    have t4 : K83 4 = (0 : ℝ) := by rfl
    have t5 : K83 5 = (0 : ℝ) := by rfl
    have u0 : b17hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b17lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b17hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b17lo 1 = (2 : ℝ) := by rfl
    have u2 : b17hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b17lo 2 = (2 : ℝ) := by rfl
    have u3 : b17hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b17lo 3 = (2 : ℝ) := by rfl
    have u4 : b17hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b17lo 4 = (2 : ℝ) := by rfl
    have u5 : b17hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b17lo 5 = (2 : ℝ) := by rfl
    have eb : B83 = ((356291706314003806959607/180143985094819840000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b17lo j) (b17hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b17lo, b17hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K83 i := by
    intro i; fin_cases i <;> norm_num [K83]
  have hR0 : ∀ i, 0 ≤ R83 i := by
    intro i; fin_cases i <;> norm_num [R83, K83, b17lo, b17hi]
  have hchain := chain_idx83 c83_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c83_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 84 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c84_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.02241) * (y 0) + (-0.060747) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.608509

theorem c84_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c84_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.608509 :=
  rfl

/-- Component 84 gate (box 18; chain chain_idx84; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c84_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => c84_mfunb (Function.update y i t) - K84 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B84 ≤ c84_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 4 + 7 / 4) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.608509 > 0 := by
  have hpos : (0 : ℝ) <
      B84 - ∑ i, R84 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R84 i = K84 i * (b18hi i - b18lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K84 0 = (0 : ℝ) := by rfl
    have t1 : K84 1 = (0 : ℝ) := by rfl
    have t2 : K84 2 = (0 : ℝ) := by rfl
    have t3 : K84 3 = (0 : ℝ) := by rfl
    have t4 : K84 4 = (0 : ℝ) := by rfl
    have t5 : K84 5 = (0 : ℝ) := by rfl
    have u0 : b18hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b18lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b18hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b18lo 1 = (2 : ℝ) := by rfl
    have u2 : b18hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b18lo 2 = (2 : ℝ) := by rfl
    have u3 : b18hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b18lo 3 = ((32927/16000) : ℝ) := by rfl
    have u4 : b18hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b18lo 4 = (2 : ℝ) := by rfl
    have u5 : b18hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b18lo 5 = (2 : ℝ) := by rfl
    have eb : B84 = ((35526606265659279942811/18014398509481984000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b18lo j) (b18hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b18lo, b18hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K84 i := by
    intro i; fin_cases i <;> norm_num [K84]
  have hR0 : ∀ i, 0 ≤ R84 i := by
    intro i; fin_cases i <;> norm_num [R84, K84, b18lo, b18hi]
  have hchain := chain_idx84 c84_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c84_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 85 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c85_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.014413) + (-0.02241) + (-0.014413)) * y1 + 2 * (0.060747 + (-0.060747)) * y12 + 2 * ((-0.060747) + 0.060747) * y23 + 2 * (0.060747 + (-0.060747)) * y34 + 2 * ((-0.060747) + 0.060747) * y41 + ((-0.530636) + 0.594377 + (-0.36344) + 0.594377) < 0 :=
  ox3q1hLin_085

/-- Margin function of conjunct 86 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c86_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.051237 * (y 0) + 0.060747 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.530636)

theorem c86_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c86_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.530636) :=
  rfl

/-- Component 86 gate (box 16; chain chain_idx86; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c86_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b16lo i) (b16hi i))
        (fun t => c86_mfunb (Function.update y i t) - K86 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb16 j) → B86 ≤ c86_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (h0 + hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.530636) > 0 := by
  have hpos : (0 : ℝ) <
      B86 - ∑ i, R86 i := by
    rw [sumFin6b]
    have e0 : R86 0 = (0 : ℝ) := by rfl
    have e1 : R86 1 = (0 : ℝ) := by rfl
    have e2 : R86 2 = (0 : ℝ) := by rfl
    have e3 : R86 3 = ((2584402081090101/8796093022208000000) : ℝ) := by rfl
    have e4 : R86 4 = (0 : ℝ) := by rfl
    have e5 : R86 5 = (0 : ℝ) := by rfl
    have eb : B86 = ((177733425925575667907441/90071992547409920000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b16lo j) (b16hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b16lo, b16hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K86 i := by
    intro i; fin_cases i <;> norm_num [K86]
  have hR0 : ∀ i, 0 ≤ R86 i := by
    intro i; fin_cases i <;> norm_num [R86, K86, b16lo, b16hi]
  have hchain := chain_idx86 c86_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c86_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 87 gate (box 17; chain chain_idx87; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c87_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => c82_mfunb (Function.update y i t) - K87 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B87 ≤ c82_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.594377 > 0 := by
  have hpos : (0 : ℝ) <
      B87 - ∑ i, R87 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R87 i = K87 i * (b17hi i - b17lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K87 0 = (0 : ℝ) := by rfl
    have t1 : K87 1 = (0 : ℝ) := by rfl
    have t2 : K87 2 = (0 : ℝ) := by rfl
    have t3 : K87 3 = (0 : ℝ) := by rfl
    have t4 : K87 4 = (0 : ℝ) := by rfl
    have t5 : K87 5 = (0 : ℝ) := by rfl
    have u0 : b17hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b17lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b17hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b17lo 1 = (2 : ℝ) := by rfl
    have u2 : b17hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b17lo 2 = (2 : ℝ) := by rfl
    have u3 : b17hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b17lo 3 = (2 : ℝ) := by rfl
    have u4 : b17hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b17lo 4 = (2 : ℝ) := by rfl
    have u5 : b17hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b17lo 5 = (2 : ℝ) := by rfl
    have eb : B87 = ((1775586001116581819034139/900719925474099200000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b17lo j) (b17hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b17lo, b17hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K87 i := by
    intro i; fin_cases i <;> norm_num [K87]
  have hR0 : ∀ i, 0 ≤ R87 i := by
    intro i; fin_cases i <;> norm_num [R87, K87, b17lo, b17hi]
  have hchain := chain_idx87 c82_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c82_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 88 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c88_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.02241) * (y 0) + 0.060747 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.36344)

theorem c88_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c88_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.36344) :=
  rfl

/-- Component 88 gate (box 18; chain chain_idx88; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c88_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => c88_mfunb (Function.update y i t) - K88 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B88 ≤ c88_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 4 + 7 / 4) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.36344) > 0 := by
  have hpos : (0 : ℝ) <
      B88 - ∑ i, R88 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R88 i = K88 i * (b18hi i - b18lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K88 0 = (0 : ℝ) := by rfl
    have t1 : K88 1 = (0 : ℝ) := by rfl
    have t2 : K88 2 = (0 : ℝ) := by rfl
    have t3 : K88 3 = (0 : ℝ) := by rfl
    have t4 : K88 4 = (0 : ℝ) := by rfl
    have t5 : K88 5 = (0 : ℝ) := by rfl
    have u0 : b18hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b18lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b18hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b18lo 1 = (2 : ℝ) := by rfl
    have u2 : b18hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b18lo 2 = (2 : ℝ) := by rfl
    have u3 : b18hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b18lo 3 = ((32927/16000) : ℝ) := by rfl
    have u4 : b18hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b18lo 4 = (2 : ℝ) := by rfl
    have u5 : b18hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b18lo 5 = (2 : ℝ) := by rfl
    have eb : B88 = ((35580649461187725894811/18014398509481984000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b18lo j) (b18hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b18lo, b18hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K88 i := by
    intro i; fin_cases i <;> norm_num [K88]
  have hR0 : ∀ i, 0 ≤ R88 i := by
    intro i; fin_cases i <;> norm_num [R88, K88, b18lo, b18hi]
  have hchain := chain_idx88 c88_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c88_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 89 gate (box 19; chain chain_idx89; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c89_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => c82_mfunb (Function.update y i t) - K89 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B89 ≤ c82_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.594377 > 0 := by
  have hpos : (0 : ℝ) <
      B89 - ∑ i, R89 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R89 i = K89 i * (b19hi i - b19lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K89 0 = (0 : ℝ) := by rfl
    have t1 : K89 1 = (0 : ℝ) := by rfl
    have t2 : K89 2 = (0 : ℝ) := by rfl
    have t3 : K89 3 = (0 : ℝ) := by rfl
    have t4 : K89 4 = (0 : ℝ) := by rfl
    have t5 : K89 5 = (0 : ℝ) := by rfl
    have u0 : b19hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b19lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b19hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b19lo 1 = (2 : ℝ) := by rfl
    have u2 : b19hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b19lo 2 = (2 : ℝ) := by rfl
    have u3 : b19hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b19lo 3 = (2 : ℝ) := by rfl
    have u4 : b19hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b19lo 4 = (2 : ℝ) := by rfl
    have u5 : b19hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b19lo 5 = (2 : ℝ) := by rfl
    have eb : B89 = ((1775586001116581819034139/900719925474099200000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b19lo j) (b19hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b19lo, b19hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K89 i := by
    intro i; fin_cases i <;> norm_num [K89]
  have hR0 : ∀ i, 0 ≤ R89 i := by
    intro i; fin_cases i <;> norm_num [R89, K89, b19lo, b19hi]
  have hchain := chain_idx89 c82_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c82_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 90 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c90_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.02241) + (-0.014413) + (-0.014413)) * y1 + 2 * (0.060747 + (-0.060747)) * y12 + 2 * ((-0.060747) + 0.060747) * y23 + 2 * (0.060747 + (-0.060747)) * y34 + 2 * ((-0.060747) + 0.060747) * y41 + ((-0.530637) + 0.608509 + (-0.377571) + 0.594377) < 0 :=
  ox3q1hLin_090

/-- Component 91 gate (box 16; chain chain_idx91; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c91_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b16lo i) (b16hi i))
        (fun t => c81_mfunb (Function.update y i t) - K91 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb16 j) → B91 ≤ c81_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (h0 + hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.530637) > 0 := by
  have hpos : (0 : ℝ) <
      B91 - ∑ i, R91 i := by
    rw [sumFin6b]
    have e0 : R91 0 = (0 : ℝ) := by rfl
    have e1 : R91 1 = (0 : ℝ) := by rfl
    have e2 : R91 2 = (0 : ℝ) := by rfl
    have e3 : R91 3 = ((2584402081090101/8796093022208000000) : ℝ) := by rfl
    have e4 : R91 4 = (0 : ℝ) := by rfl
    have e5 : R91 5 = (0 : ℝ) := by rfl
    have eb : B91 = ((177643353933028257987441/90071992547409920000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b16lo j) (b16hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b16lo, b16hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K91 i := by
    intro i; fin_cases i <;> norm_num [K91]
  have hR0 : ∀ i, 0 ≤ R91 i := by
    intro i; fin_cases i <;> norm_num [R91, K91, b16lo, b16hi]
  have hchain := chain_idx91 c81_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c81_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 92 gate (box 18; chain chain_idx92; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c92_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => c84_mfunb (Function.update y i t) - K92 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B92 ≤ c84_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 4 + 7 / 4) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.608509 > 0 := by
  have hpos : (0 : ℝ) <
      B92 - ∑ i, R92 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R92 i = K92 i * (b18hi i - b18lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K92 0 = (0 : ℝ) := by rfl
    have t1 : K92 1 = (0 : ℝ) := by rfl
    have t2 : K92 2 = (0 : ℝ) := by rfl
    have t3 : K92 3 = (0 : ℝ) := by rfl
    have t4 : K92 4 = (0 : ℝ) := by rfl
    have t5 : K92 5 = (0 : ℝ) := by rfl
    have u0 : b18hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b18lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b18hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b18lo 1 = (2 : ℝ) := by rfl
    have u2 : b18hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b18lo 2 = (2 : ℝ) := by rfl
    have u3 : b18hi 3 = ((52897/25000) : ℝ) := by rfl
    have q3 : b18lo 3 = ((32927/16000) : ℝ) := by rfl
    have u4 : b18hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b18lo 4 = (2 : ℝ) := by rfl
    have u5 : b18hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b18lo 5 = (2 : ℝ) := by rfl
    have eb : B92 = ((35526606265659279942811/18014398509481984000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b18lo j) (b18hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b18lo, b18hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K92 i := by
    intro i; fin_cases i <;> norm_num [K92]
  have hR0 : ∀ i, 0 ≤ R92 i := by
    intro i; fin_cases i <;> norm_num [R92, K92, b18lo, b18hi]
  have hchain := chain_idx92 c84_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c84_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 93 gate (box 19; chain chain_idx93; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c93_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => c83_mfunb (Function.update y i t) - K93 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B93 ≤ c83_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.377571) > 0 := by
  have hpos : (0 : ℝ) <
      B93 - ∑ i, R93 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R93 i = K93 i * (b19hi i - b19lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K93 0 = (0 : ℝ) := by rfl
    have t1 : K93 1 = (0 : ℝ) := by rfl
    have t2 : K93 2 = (0 : ℝ) := by rfl
    have t3 : K93 3 = (0 : ℝ) := by rfl
    have t4 : K93 4 = (0 : ℝ) := by rfl
    have t5 : K93 5 = (0 : ℝ) := by rfl
    have u0 : b19hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b19lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b19hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b19lo 1 = (2 : ℝ) := by rfl
    have u2 : b19hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b19lo 2 = (2 : ℝ) := by rfl
    have u3 : b19hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b19lo 3 = (2 : ℝ) := by rfl
    have u4 : b19hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b19lo 4 = (2 : ℝ) := by rfl
    have u5 : b19hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b19lo 5 = (2 : ℝ) := by rfl
    have eb : B93 = ((356291706314003806959607/180143985094819840000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b19lo j) (b19hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b19lo, b19hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K93 i := by
    intro i; fin_cases i <;> norm_num [K93]
  have hR0 : ∀ i, 0 ≤ R93 i := by
    intro i; fin_cases i <;> norm_num [R93, K93, b19lo, b19hi]
  have hchain := chain_idx93 c83_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c83_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 94 gate (box 19; chain chain_idx94; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c94_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => c82_mfunb (Function.update y i t) - K94 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B94 ≤ c82_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.594377 > 0 := by
  have hpos : (0 : ℝ) <
      B94 - ∑ i, R94 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R94 i = K94 i * (b19hi i - b19lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K94 0 = (0 : ℝ) := by rfl
    have t1 : K94 1 = (0 : ℝ) := by rfl
    have t2 : K94 2 = (0 : ℝ) := by rfl
    have t3 : K94 3 = (0 : ℝ) := by rfl
    have t4 : K94 4 = (0 : ℝ) := by rfl
    have t5 : K94 5 = (0 : ℝ) := by rfl
    have u0 : b19hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b19lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b19hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b19lo 1 = (2 : ℝ) := by rfl
    have u2 : b19hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b19lo 2 = (2 : ℝ) := by rfl
    have u3 : b19hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b19lo 3 = (2 : ℝ) := by rfl
    have u4 : b19hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b19lo 4 = (2 : ℝ) := by rfl
    have u5 : b19hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b19lo 5 = (2 : ℝ) := by rfl
    have eb : B94 = ((1775586001116581819034139/900719925474099200000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b19lo j) (b19hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b19lo, b19hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K94 i := by
    intro i; fin_cases i <;> norm_num [K94]
  have hR0 : ∀ i, 0 ≤ R94 i := by
    intro i; fin_cases i <;> norm_num [R94, K94, b19lo, b19hi]
  have hchain := chain_idx94 c82_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c82_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 95 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c95_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.036939) + (0.050064 + (-0.016688) + (-0.016688) + (-0.016688)) * y1 + 2 * ((-0.057593) + 0.057593) * y12 + 2 * (0.057593 + (-0.057593)) * y23 + 2 * ((-0.057593) + (-0.057593)) * y34 + 2 * ((-0.057593) + (-0.057593)) * y41 + (0.397884 + (-0.362427) + 0.559062 + 0.559062) < 0 :=
  ox3q1hLin_095

/-- Margin function of conjunct 96 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c96_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.036939) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.050064 * (y 0) + (-0.057593) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.397884

theorem c96_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c96_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + 0.050064 * y1 + (-0.057593) * (y2 + y3 + y5 + y6) + 0.397884 :=
  rfl

/-- Component 96 gate (box 20; S4.5 split-grid chain
`chain_split_idx96`, split factors per SPLIT_PLAN route `Y4PATCH:y4`, m_min =
2; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c96_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit96 i →
      ConcaveOn ℝ (Set.Icc (gsplit96 i k) (gsplit96 i (k + 1)))
        (fun t => c96_mfunb (Function.update y i t) - K96 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split96 j) → B96 ≤ c96_mfunb v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (h0 + hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + 0.050064 * y1 + (-0.057593) * (y2 + y3 + y5 + y6) + 0.397884 > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b20lo j) (b20hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b20lo, b20hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx96 c96_mfunb hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c96_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx96
  linarith [hchain, hpos]

/-- Margin function of conjunct 97 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c97_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.036939) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.016688) * (y 0) + 0.057593 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.362427)

theorem c97_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c97_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + (-0.016688) * y1 + 0.057593 * (y2 + y3 + y5 + y6) + (-0.362427) :=
  rfl

/-- Component 97 gate (box 21; chain chain_idx97; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c97_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => c97_mfunb (Function.update y i t) - K97 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B97 ≤ c97_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + (-0.016688) * y1 + 0.057593 * (y2 + y3 + y5 + y6) + (-0.362427) > 0 := by
  have hpos : (0 : ℝ) <
      B97 - ∑ i, R97 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R97 i = K97 i * (b21hi i - b21lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K97 0 = (0 : ℝ) := by rfl
    have t1 : K97 1 = (0 : ℝ) := by rfl
    have t2 : K97 2 = (0 : ℝ) := by rfl
    have t3 : K97 3 = (0 : ℝ) := by rfl
    have t4 : K97 4 = (0 : ℝ) := by rfl
    have t5 : K97 5 = (0 : ℝ) := by rfl
    have u0 : b21hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b21lo 0 = ((10407/4000) : ℝ) := by rfl
    have u1 : b21hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b21lo 1 = (2 : ℝ) := by rfl
    have u2 : b21hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b21lo 2 = (2 : ℝ) := by rfl
    have u3 : b21hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b21lo 3 = (2 : ℝ) := by rfl
    have u4 : b21hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b21lo 4 = (2 : ℝ) := by rfl
    have u5 : b21hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b21lo 5 = (2 : ℝ) := by rfl
    have eb : B97 = ((23734450474249571838381/72057594037927936000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b21lo j) (b21hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b21lo, b21hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K97 i := by
    intro i; fin_cases i <;> norm_num [K97]
  have hR0 : ∀ i, 0 ≤ R97 i := by
    intro i; fin_cases i <;> norm_num [R97, K97, b21lo, b21hi]
  have hchain := chain_idx97 c97_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c97_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 98 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c98_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.036939) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.016688) * (y 0) + (-0.057593) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.559062

theorem c98_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c98_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + (-0.016688) * y1 + (-0.057593) * (y2 + y3 + y5 + y6) + 0.559062 :=
  rfl

/-- Component 98 gate (box 21; chain chain_idx98; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c98_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => c98_mfunb (Function.update y i t) - K98 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B98 ≤ c98_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + (-0.016688) * y1 + (-0.057593) * (y2 + y3 + y5 + y6) + 0.559062 > 0 := by
  have hpos : (0 : ℝ) <
      B98 - ∑ i, R98 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R98 i = K98 i * (b21hi i - b21lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K98 0 = (0 : ℝ) := by rfl
    have t1 : K98 1 = (0 : ℝ) := by rfl
    have t2 : K98 2 = (0 : ℝ) := by rfl
    have t3 : K98 3 = (0 : ℝ) := by rfl
    have t4 : K98 4 = (0 : ℝ) := by rfl
    have t5 : K98 5 = (0 : ℝ) := by rfl
    have u0 : b21hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b21lo 0 = ((10407/4000) : ℝ) := by rfl
    have u1 : b21hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b21lo 1 = (2 : ℝ) := by rfl
    have u2 : b21hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b21lo 2 = (2 : ℝ) := by rfl
    have u3 : b21hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b21lo 3 = (2 : ℝ) := by rfl
    have u4 : b21hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b21lo 4 = (2 : ℝ) := by rfl
    have u5 : b21hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b21lo 5 = (2 : ℝ) := by rfl
    have eb : B98 = ((295631055591770941384851/900719925474099200000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b21lo j) (b21hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b21lo, b21hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K98 i := by
    intro i; fin_cases i <;> norm_num [K98]
  have hR0 : ∀ i, 0 ≤ R98 i := by
    intro i; fin_cases i <;> norm_num [R98, K98, b21lo, b21hi]
  have hchain := chain_idx98 c98_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c98_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 99 gate (box 21; chain chain_idx99; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c99_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => c98_mfunb (Function.update y i t) - K99 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B99 ≤ c98_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + (-0.016688) * y1 + (-0.057593) * (y2 + y3 + y5 + y6) + 0.559062 > 0 := by
  have hpos : (0 : ℝ) <
      B99 - ∑ i, R99 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R99 i = K99 i * (b21hi i - b21lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K99 0 = (0 : ℝ) := by rfl
    have t1 : K99 1 = (0 : ℝ) := by rfl
    have t2 : K99 2 = (0 : ℝ) := by rfl
    have t3 : K99 3 = (0 : ℝ) := by rfl
    have t4 : K99 4 = (0 : ℝ) := by rfl
    have t5 : K99 5 = (0 : ℝ) := by rfl
    have u0 : b21hi 0 = ((26181/10000) : ℝ) := by rfl
    have q0 : b21lo 0 = ((10407/4000) : ℝ) := by rfl
    have u1 : b21hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b21lo 1 = (2 : ℝ) := by rfl
    have u2 : b21hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b21lo 2 = (2 : ℝ) := by rfl
    have u3 : b21hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b21lo 3 = (2 : ℝ) := by rfl
    have u4 : b21hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b21lo 4 = (2 : ℝ) := by rfl
    have u5 : b21hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b21lo 5 = (2 : ℝ) := by rfl
    have eb : B99 = ((295631055591770941384851/900719925474099200000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b21lo j) (b21hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b21lo, b21hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K99 i := by
    intro i; fin_cases i <;> norm_num [K99]
  have hR0 : ∀ i, 0 ≤ R99 i := by
    intro i; fin_cases i <;> norm_num [R99, K99, b21lo, b21hi]
  have hchain := chain_idx99 c98_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c98_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 100 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c100_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.049823) + (0.047052 + (-0.015684) + (-0.015684) + (-0.015684)) * y1 + 2 * ((-0.061687) + 0.061687) * y12 + 2 * (0.061687 + (-0.061687)) * y23 + 2 * ((-0.061687) + 0.061687) * y34 + 2 * (0.061687 + (-0.061687)) * y41 + (0.463622 + (-0.379191) + 0.607807 + (-0.379191)) < 0 :=
  ox3q1hLin_100

/-- Margin function of conjunct 101 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c101_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.049823) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.047052 * (y 0) + (-0.061687) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.463622

theorem c101_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c101_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.049823) * dihY y1 y2 y3 y4 y5 y6 + 0.047052 * y1 + (-0.061687) * (y2 + y3 + y5 + y6) + 0.463622 :=
  rfl

/-- Component 101 gate (box 22; chain chain_idx101; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c101_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b22lo i) (b22hi i))
        (fun t => c101_mfunb (Function.update y i t) - K101 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb22 j) → B101 ≤ c101_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (3 * h0 / 2 + 1 * hplus / 2) ≤ y4 → y4 ≤ (h0 + hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.049823) * dihY y1 y2 y3 y4 y5 y6 + 0.047052 * y1 + (-0.061687) * (y2 + y3 + y5 + y6) + 0.463622 > 0 := by
  have hpos : (0 : ℝ) <
      B101 - ∑ i, R101 i := by
    rw [sumFin6b]
    have e0 : R101 0 = (0 : ℝ) := by rfl
    have e1 : R101 1 = (0 : ℝ) := by rfl
    have e2 : R101 2 = (0 : ℝ) := by rfl
    have e3 : R101 3 = ((12748837324082229/175921860444160000000) : ℝ) := by rfl
    have e4 : R101 4 = (0 : ℝ) := by rfl
    have e5 : R101 5 = (0 : ℝ) := by rfl
    have eb : B101 = ((60425570515597217172127/144115188075855872000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b22lo j) (b22hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b22lo, b22hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K101 i := by
    intro i; fin_cases i <;> norm_num [K101]
  have hR0 : ∀ i, 0 ≤ R101 i := by
    intro i; fin_cases i <;> norm_num [R101, K101, b22lo, b22hi]
  have hchain := chain_idx101 c101_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c101_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 102 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c102_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.049823) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.015684) * (y 0) + 0.061687 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.379191)

theorem c102_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c102_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.049823) * dihY y1 y2 y3 y4 y5 y6 + (-0.015684) * y1 + 0.061687 * (y2 + y3 + y5 + y6) + (-0.379191) :=
  rfl

/-- Component 102 gate (box 23; chain chain_idx102; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c102_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => c102_mfunb (Function.update y i t) - K102 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B102 ≤ c102_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.049823) * dihY y1 y2 y3 y4 y5 y6 + (-0.015684) * y1 + 0.061687 * (y2 + y3 + y5 + y6) + (-0.379191) > 0 := by
  have hpos : (0 : ℝ) <
      B102 - ∑ i, R102 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R102 i = K102 i * (b23hi i - b23lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K102 0 = (0 : ℝ) := by rfl
    have t1 : K102 1 = (0 : ℝ) := by rfl
    have t2 : K102 2 = (0 : ℝ) := by rfl
    have t3 : K102 3 = (0 : ℝ) := by rfl
    have t4 : K102 4 = (0 : ℝ) := by rfl
    have t5 : K102 5 = (0 : ℝ) := by rfl
    have u0 : b23hi 0 = ((10407/4000) : ℝ) := by rfl
    have q0 : b23lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b23hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b23lo 1 = (2 : ℝ) := by rfl
    have u2 : b23hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b23lo 2 = (2 : ℝ) := by rfl
    have u3 : b23hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b23lo 3 = (2 : ℝ) := by rfl
    have u4 : b23hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b23lo 4 = (2 : ℝ) := by rfl
    have u5 : b23hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b23lo 5 = (2 : ℝ) := by rfl
    have eb : B102 = ((298715483867368104034829/720575940379279360000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b23lo j) (b23hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b23lo, b23hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K102 i := by
    intro i; fin_cases i <;> norm_num [K102]
  have hR0 : ∀ i, 0 ≤ R102 i := by
    intro i; fin_cases i <;> norm_num [R102, K102, b23lo, b23hi]
  have hchain := chain_idx102 c102_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c102_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 103 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c103_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.049823) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.015684) * (y 0) + (-0.061687) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.607807

theorem c103_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c103_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.049823) * dihY y1 y2 y3 y4 y5 y6 + (-0.015684) * y1 + (-0.061687) * (y2 + y3 + y5 + y6) + 0.607807 :=
  rfl

/-- Component 103 gate (box 23; chain chain_idx103; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c103_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => c103_mfunb (Function.update y i t) - K103 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B103 ≤ c103_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.049823) * dihY y1 y2 y3 y4 y5 y6 + (-0.015684) * y1 + (-0.061687) * (y2 + y3 + y5 + y6) + 0.607807 > 0 := by
  have hpos : (0 : ℝ) <
      B103 - ∑ i, R103 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R103 i = K103 i * (b23hi i - b23lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K103 0 = (0 : ℝ) := by rfl
    have t1 : K103 1 = (0 : ℝ) := by rfl
    have t2 : K103 2 = (0 : ℝ) := by rfl
    have t3 : K103 3 = (0 : ℝ) := by rfl
    have t4 : K103 4 = (0 : ℝ) := by rfl
    have t5 : K103 5 = (0 : ℝ) := by rfl
    have u0 : b23hi 0 = ((10407/4000) : ℝ) := by rfl
    have q0 : b23lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b23hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b23lo 1 = (2 : ℝ) := by rfl
    have u2 : b23hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b23lo 2 = (2 : ℝ) := by rfl
    have u3 : b23hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b23lo 3 = (2 : ℝ) := by rfl
    have u4 : b23hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b23lo 4 = (2 : ℝ) := by rfl
    have u5 : b23hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b23lo 5 = (2 : ℝ) := by rfl
    have eb : B103 = ((1508718784408980513689881/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b23lo j) (b23hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b23lo, b23hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K103 i := by
    intro i; fin_cases i <;> norm_num [K103]
  have hR0 : ∀ i, 0 ≤ R103 i := by
    intro i; fin_cases i <;> norm_num [R103, K103, b23lo, b23hi]
  have hchain := chain_idx103 c103_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c103_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 104 gate (box 23; chain chain_idx104; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c104_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => c102_mfunb (Function.update y i t) - K104 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B104 ≤ c102_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.049823) * dihY y1 y2 y3 y4 y5 y6 + (-0.015684) * y1 + 0.061687 * (y2 + y3 + y5 + y6) + (-0.379191) > 0 := by
  have hpos : (0 : ℝ) <
      B104 - ∑ i, R104 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R104 i = K104 i * (b23hi i - b23lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K104 0 = (0 : ℝ) := by rfl
    have t1 : K104 1 = (0 : ℝ) := by rfl
    have t2 : K104 2 = (0 : ℝ) := by rfl
    have t3 : K104 3 = (0 : ℝ) := by rfl
    have t4 : K104 4 = (0 : ℝ) := by rfl
    have t5 : K104 5 = (0 : ℝ) := by rfl
    have u0 : b23hi 0 = ((10407/4000) : ℝ) := by rfl
    have q0 : b23lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b23hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b23lo 1 = (2 : ℝ) := by rfl
    have u2 : b23hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b23lo 2 = (2 : ℝ) := by rfl
    have u3 : b23hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b23lo 3 = (2 : ℝ) := by rfl
    have u4 : b23hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b23lo 4 = (2 : ℝ) := by rfl
    have u5 : b23hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b23lo 5 = (2 : ℝ) := by rfl
    have eb : B104 = ((298715483867368104034829/720575940379279360000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b23lo j) (b23hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b23lo, b23hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K104 i := by
    intro i; fin_cases i <;> norm_num [K104]
  have hR0 : ∀ i, 0 ≤ R104 i := by
    intro i; fin_cases i <;> norm_num [R104, K104, b23lo, b23hi]
  have hchain := chain_idx104 c102_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c102_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 105 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c105_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.053582) + (0.049452 + (-0.013853) + (-0.020791) + (-0.013853)) * y1 + 2 * ((-0.06302) + 0.06302) * y12 + 2 * (0.06302 + (-0.06302)) * y23 + 2 * ((-0.06302) + (-0.062897)) * y34 + 2 * ((-0.062897) + (-0.06302)) * y41 + (0.475514 + (-0.389234) + 0.637132 + 0.618101) < 0 :=
  ox3q1hLin_105

/-- Margin function of conjunct 106 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c106_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.053582) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.049452 * (y 0) + (-0.06302) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.475514

theorem c106_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c106_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.053582) * dihY y1 y2 y3 y4 y5 y6 + 0.049452 * y1 + (-0.06302) * (y2 + y3 + y5 + y6) + 0.475514 :=
  rfl

/-- Component 106 gate (box 24; chain chain_idx106; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c106_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b24lo i) (b24hi i))
        (fun t => c106_mfunb (Function.update y i t) - K106 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb24 j) → B106 ≤ c106_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.053582) * dihY y1 y2 y3 y4 y5 y6 + 0.049452 * y1 + (-0.06302) * (y2 + y3 + y5 + y6) + 0.475514 > 0 := by
  have hpos : (0 : ℝ) <
      B106 - ∑ i, R106 i := by
    rw [sumFin6b]
    have e0 : R106 0 = (0 : ℝ) := by rfl
    have e1 : R106 1 = (0 : ℝ) := by rfl
    have e2 : R106 2 = (0 : ℝ) := by rfl
    have e3 : R106 3 = ((32229434589208443/439804651110400000000) : ℝ) := by rfl
    have e4 : R106 4 = (0 : ℝ) := by rfl
    have e5 : R106 5 = (0 : ℝ) := by rfl
    have eb : B106 = ((28193936750087767554951/72057594037927936000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b24lo j) (b24hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b24lo, b24hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K106 i := by
    intro i; fin_cases i <;> norm_num [K106]
  have hR0 : ∀ i, 0 ≤ R106 i := by
    intro i; fin_cases i <;> norm_num [R106, K106, b24lo, b24hi]
  have hchain := chain_idx106 c106_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c106_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 107 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c107_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.053582) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.013853) * (y 0) + 0.06302 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.389234)

theorem c107_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c107_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.053582) * dihY y1 y2 y3 y4 y5 y6 + (-0.013853) * y1 + 0.06302 * (y2 + y3 + y5 + y6) + (-0.389234) :=
  rfl

/-- Component 107 gate (box 23; chain chain_idx107; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c107_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => c107_mfunb (Function.update y i t) - K107 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B107 ≤ c107_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.053582) * dihY y1 y2 y3 y4 y5 y6 + (-0.013853) * y1 + 0.06302 * (y2 + y3 + y5 + y6) + (-0.389234) > 0 := by
  have hpos : (0 : ℝ) <
      B107 - ∑ i, R107 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R107 i = K107 i * (b23hi i - b23lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K107 0 = (0 : ℝ) := by rfl
    have t1 : K107 1 = (0 : ℝ) := by rfl
    have t2 : K107 2 = (0 : ℝ) := by rfl
    have t3 : K107 3 = (0 : ℝ) := by rfl
    have t4 : K107 4 = (0 : ℝ) := by rfl
    have t5 : K107 5 = (0 : ℝ) := by rfl
    have u0 : b23hi 0 = ((10407/4000) : ℝ) := by rfl
    have q0 : b23lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b23hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b23lo 1 = (2 : ℝ) := by rfl
    have u2 : b23hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b23lo 2 = (2 : ℝ) := by rfl
    have u3 : b23hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b23lo 3 = (2 : ℝ) := by rfl
    have u4 : b23hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b23lo 4 = (2 : ℝ) := by rfl
    have u5 : b23hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b23lo 5 = (2 : ℝ) := by rfl
    have eb : B107 = ((14320576368836929194993/36028797018963968000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b23lo j) (b23hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b23lo, b23hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K107 i := by
    intro i; fin_cases i <;> norm_num [K107]
  have hR0 : ∀ i, 0 ≤ R107 i := by
    intro i; fin_cases i <;> norm_num [R107, K107, b23lo, b23hi]
  have hchain := chain_idx107 c107_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c107_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 108 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c108_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.053582) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.020791) * (y 0) + (-0.06302) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.637132

theorem c108_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c108_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.053582) * dihY y1 y2 y3 y4 y5 y6 + (-0.020791) * y1 + (-0.06302) * (y2 + y3 + y5 + y6) + 0.637132 :=
  rfl

/-- Component 108 gate (box 23; chain chain_idx108; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c108_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => c108_mfunb (Function.update y i t) - K108 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B108 ≤ c108_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.053582) * dihY y1 y2 y3 y4 y5 y6 + (-0.020791) * y1 + (-0.06302) * (y2 + y3 + y5 + y6) + 0.637132 > 0 := by
  have hpos : (0 : ℝ) <
      B108 - ∑ i, R108 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R108 i = K108 i * (b23hi i - b23lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K108 0 = (0 : ℝ) := by rfl
    have t1 : K108 1 = (0 : ℝ) := by rfl
    have t2 : K108 2 = (0 : ℝ) := by rfl
    have t3 : K108 3 = (0 : ℝ) := by rfl
    have t4 : K108 4 = (0 : ℝ) := by rfl
    have t5 : K108 5 = (0 : ℝ) := by rfl
    have u0 : b23hi 0 = ((10407/4000) : ℝ) := by rfl
    have q0 : b23lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b23hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b23lo 1 = (2 : ℝ) := by rfl
    have u2 : b23hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b23lo 2 = (2 : ℝ) := by rfl
    have u3 : b23hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b23lo 3 = (2 : ℝ) := by rfl
    have u4 : b23hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b23lo 4 = (2 : ℝ) := by rfl
    have u5 : b23hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b23lo 5 = (2 : ℝ) := by rfl
    have eb : B108 = ((35127315796962965609979/90071992547409920000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b23lo j) (b23hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b23lo, b23hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K108 i := by
    intro i; fin_cases i <;> norm_num [K108]
  have hR0 : ∀ i, 0 ≤ R108 i := by
    intro i; fin_cases i <;> norm_num [R108, K108, b23lo, b23hi]
  have hchain := chain_idx108 c108_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c108_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 109 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c109_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.053582) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.013853) * (y 0) + (-0.062897) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.618101

theorem c109_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c109_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.053582) * dihY y1 y2 y3 y4 y5 y6 + (-0.013853) * y1 + (-0.062897) * (y2 + y3 + y5 + y6) + 0.618101 :=
  rfl

/-- Component 109 gate (box 23; chain chain_idx109; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c109_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => c109_mfunb (Function.update y i t) - K109 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B109 ≤ c109_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.053582) * dihY y1 y2 y3 y4 y5 y6 + (-0.013853) * y1 + (-0.062897) * (y2 + y3 + y5 + y6) + 0.618101 > 0 := by
  have hpos : (0 : ℝ) <
      B109 - ∑ i, R109 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R109 i = K109 i * (b23hi i - b23lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K109 0 = (0 : ℝ) := by rfl
    have t1 : K109 1 = (0 : ℝ) := by rfl
    have t2 : K109 2 = (0 : ℝ) := by rfl
    have t3 : K109 3 = (0 : ℝ) := by rfl
    have t4 : K109 4 = (0 : ℝ) := by rfl
    have t5 : K109 5 = (0 : ℝ) := by rfl
    have u0 : b23hi 0 = ((10407/4000) : ℝ) := by rfl
    have q0 : b23lo 0 = ((12927/5000) : ℝ) := by rfl
    have u1 : b23hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b23lo 1 = (2 : ℝ) := by rfl
    have u2 : b23hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b23lo 2 = (2 : ℝ) := by rfl
    have u3 : b23hi 3 = ((102897/50000) : ℝ) := by rfl
    have q3 : b23lo 3 = (2 : ℝ) := by rfl
    have u4 : b23hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b23lo 4 = (2 : ℝ) := by rfl
    have u5 : b23hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b23lo 5 = (2 : ℝ) := by rfl
    have eb : B109 = ((710744425100943783814353/1801439850948198400000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b23lo j) (b23hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b23lo, b23hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K109 i := by
    intro i; fin_cases i <;> norm_num [K109]
  have hR0 : ∀ i, 0 ≤ R109 i := by
    intro i; fin_cases i <;> norm_num [R109, K109, b23lo, b23hi]
  have hchain := chain_idx109 c109_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c109_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 110 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c110_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.066935) + (0.079693 + (-0.021495) + (-0.021495) + (-0.036704)) * y1 + 2 * (0.066241 + (-0.066241)) * y12 + 2 * ((-0.066241) + 0.066241) * y23 + 2 * (0.066241 + (-0.066241)) * y34 + 2 * ((-0.066241) + 0.066241) * y41 + ((-0.605497) + 0.685308 + (-0.374549) + 0.715304) < 0 :=
  ox3q1hLin_110

/-- Margin function of conjunct 111 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c111_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.066935) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.079693 * (y 0) + 0.066241 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.605497)

theorem c111_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c111_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + 0.079693 * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.605497) :=
  rfl

/-- Component 111 gate (box 25; S4.5 split-grid chain
`chain_split_idx111`, split factors per SPLIT_PLAN route `Y4PATCH:y4`, m_min =
2; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c111_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit111 i →
      ConcaveOn ℝ (Set.Icc (gsplit111 i k) (gsplit111 i (k + 1)))
        (fun t => c111_mfunb (Function.update y i t) - K111 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split111 j) → B111 ≤ c111_mfunb v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + 0.079693 * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.605497) > 0 := by
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
  have hchain := chain_split_idx111 c111_mfunb hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c111_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx111
  linarith [hchain, hpos]

/-- Margin function of conjunct 112 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c112_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.066935) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.021495) * (y 0) + (-0.066241) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.685308

theorem c112_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c112_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.021495) * y1 + (-0.066241) * (y2 + y3 + y5 + y6) + 0.685308 :=
  rfl

/-- Component 112 gate (box 26; chain chain_idx112; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c112_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => c112_mfunb (Function.update y i t) - K112 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B112 ≤ c112_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.021495) * y1 + (-0.066241) * (y2 + y3 + y5 + y6) + 0.685308 > 0 := by
  have hpos : (0 : ℝ) <
      B112 - ∑ i, R112 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R112 i = K112 i * (b26hi i - b26lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K112 0 = (0 : ℝ) := by rfl
    have t1 : K112 1 = (0 : ℝ) := by rfl
    have t2 : K112 2 = (0 : ℝ) := by rfl
    have t3 : K112 3 = (0 : ℝ) := by rfl
    have t4 : K112 4 = (0 : ℝ) := by rfl
    have t5 : K112 5 = (0 : ℝ) := by rfl
    have u0 : b26hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b26lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b26hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b26lo 1 = (2 : ℝ) := by rfl
    have u2 : b26hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b26lo 2 = (2 : ℝ) := by rfl
    have u3 : b26hi 3 = ((27897/12500) : ℝ) := by rfl
    have q3 : b26lo 3 = (2 : ℝ) := by rfl
    have u4 : b26hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b26lo 4 = (2 : ℝ) := by rfl
    have u5 : b26hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b26lo 5 = (2 : ℝ) := by rfl
    have eb : B112 = ((7238830132115033097287123/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b26lo j) (b26hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b26lo, b26hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K112 i := by
    intro i; fin_cases i <;> norm_num [K112]
  have hR0 : ∀ i, 0 ≤ R112 i := by
    intro i; fin_cases i <;> norm_num [R112, K112, b26lo, b26hi]
  have hchain := chain_idx112 c112_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c112_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 113 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c113_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.066935) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.021495) * (y 0) + 0.066241 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.374549)

theorem c113_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c113_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.021495) * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.374549) :=
  rfl

/-- Component 113 gate (box 26; chain chain_idx113; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c113_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => c113_mfunb (Function.update y i t) - K113 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B113 ≤ c113_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.021495) * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.374549) > 0 := by
  have hpos : (0 : ℝ) <
      B113 - ∑ i, R113 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R113 i = K113 i * (b26hi i - b26lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K113 0 = (0 : ℝ) := by rfl
    have t1 : K113 1 = (0 : ℝ) := by rfl
    have t2 : K113 2 = (0 : ℝ) := by rfl
    have t3 : K113 3 = (0 : ℝ) := by rfl
    have t4 : K113 4 = (0 : ℝ) := by rfl
    have t5 : K113 5 = (0 : ℝ) := by rfl
    have u0 : b26hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b26lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b26hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b26lo 1 = (2 : ℝ) := by rfl
    have u2 : b26hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b26lo 2 = (2 : ℝ) := by rfl
    have u3 : b26hi 3 = ((27897/12500) : ℝ) := by rfl
    have q3 : b26lo 3 = (2 : ℝ) := by rfl
    have u4 : b26hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b26lo 4 = (2 : ℝ) := by rfl
    have u5 : b26hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b26lo 5 = (2 : ℝ) := by rfl
    have eb : B113 = ((289707778743033646466769/144115188075855872000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b26lo j) (b26hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b26lo, b26hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K113 i := by
    intro i; fin_cases i <;> norm_num [K113]
  have hR0 : ∀ i, 0 ≤ R113 i := by
    intro i; fin_cases i <;> norm_num [R113, K113, b26lo, b26hi]
  have hchain := chain_idx113 c113_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c113_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 114 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c114_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.066935) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.036704) * (y 0) + (-0.066241) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.715304

theorem c114_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c114_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.036704) * y1 + (-0.066241) * (y2 + y3 + y5 + y6) + 0.715304 :=
  rfl

/-- Component 114 gate (box 27; chain chain_idx114; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c114_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b27lo i) (b27hi i))
        (fun t => c114_mfunb (Function.update y i t) - K114 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb27 j) → B114 ≤ c114_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 2 + 3 / 2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.036704) * y1 + (-0.066241) * (y2 + y3 + y5 + y6) + 0.715304 > 0 := by
  have hpos : (0 : ℝ) <
      B114 - ∑ i, R114 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R114 i = K114 i * (b27hi i - b27lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K114 0 = (0 : ℝ) := by rfl
    have t1 : K114 1 = (0 : ℝ) := by rfl
    have t2 : K114 2 = (0 : ℝ) := by rfl
    have t3 : K114 3 = (0 : ℝ) := by rfl
    have t4 : K114 4 = (0 : ℝ) := by rfl
    have t5 : K114 5 = (0 : ℝ) := by rfl
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
    have eb : B114 = ((181114808578158272291353/90071992547409920000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K114 i := by
    intro i; fin_cases i <;> norm_num [K114]
  have hR0 : ∀ i, 0 ≤ R114 i := by
    intro i; fin_cases i <;> norm_num [R114, K114, b27lo, b27hi]
  have hchain := chain_idx114 c114_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c114_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 115 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c115_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.066935) + (0.028887 + (-0.021495) + 0.014102 + (-0.021495)) * y1 + 2 * (0.066241 + (-0.066241)) * y12 + 2 * ((-0.066241) + 0.066241) * y23 + 2 * (0.066241 + (-0.066241)) * y34 + 2 * ((-0.066241) + 0.066241) * y41 + ((-0.477466) + 0.685308 + (-0.472584) + 0.685308) < 0 :=
  ox3q1hLin_115

/-- Margin function of conjunct 116 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c116_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.066935) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.028887 * (y 0) + 0.066241 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.477466)

theorem c116_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c116_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + 0.028887 * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.477466) :=
  rfl

/-- Component 116 gate (box 25; S4.5 split-grid chain
`chain_split_idx116`, split factors per SPLIT_PLAN route `Y4PATCH:y4`, m_min =
2; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c116_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit116 i →
      ConcaveOn ℝ (Set.Icc (gsplit116 i k) (gsplit116 i (k + 1)))
        (fun t => c116_mfunb (Function.update y i t) - K116 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split116 j) → B116 ≤ c116_mfunb v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * h0) ≤ y4 → y4 ≤ (2 * hplus) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + 0.028887 * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.477466) > 0 := by
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
  have hchain := chain_split_idx116 c116_mfunb hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c116_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx116
  linarith [hchain, hpos]

/-- Component 117 gate (box 26; chain chain_idx117; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c117_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => c112_mfunb (Function.update y i t) - K117 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B117 ≤ c112_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.021495) * y1 + (-0.066241) * (y2 + y3 + y5 + y6) + 0.685308 > 0 := by
  have hpos : (0 : ℝ) <
      B117 - ∑ i, R117 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R117 i = K117 i * (b26hi i - b26lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K117 0 = (0 : ℝ) := by rfl
    have t1 : K117 1 = (0 : ℝ) := by rfl
    have t2 : K117 2 = (0 : ℝ) := by rfl
    have t3 : K117 3 = (0 : ℝ) := by rfl
    have t4 : K117 4 = (0 : ℝ) := by rfl
    have t5 : K117 5 = (0 : ℝ) := by rfl
    have u0 : b26hi 0 = ((12927/5000) : ℝ) := by rfl
    have q0 : b26lo 0 = ((63/25) : ℝ) := by rfl
    have u1 : b26hi 1 = ((15397/6250) : ℝ) := by rfl
    have q1 : b26lo 1 = (2 : ℝ) := by rfl
    have u2 : b26hi 2 = ((15397/6250) : ℝ) := by rfl
    have q2 : b26lo 2 = (2 : ℝ) := by rfl
    have u3 : b26hi 3 = ((27897/12500) : ℝ) := by rfl
    have q3 : b26lo 3 = (2 : ℝ) := by rfl
    have u4 : b26hi 4 = ((15397/6250) : ℝ) := by rfl
    have q4 : b26lo 4 = (2 : ℝ) := by rfl
    have u5 : b26hi 5 = ((15397/6250) : ℝ) := by rfl
    have q5 : b26lo 5 = (2 : ℝ) := by rfl
    have eb : B117 = ((7238830132115033097287123/3602879701896396800000000000) : ℝ) := by rfl
    norm_num [ev, t0, t1, t2, t3, t4, t5, u0, q0, u1, q1, u2, q2, u3, q3, u4, q4, u5, q5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b26lo j) (b26hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b26lo, b26hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K117 i := by
    intro i; fin_cases i <;> norm_num [K117]
  have hR0 : ∀ i, 0 ≤ R117 i := by
    intro i; fin_cases i <;> norm_num [R117, K117, b26lo, b26hi]
  have hchain := chain_idx117 c112_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c112_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 118 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c118_mfunb (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.066935) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.014102 * (y 0) + 0.066241 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.472584)

theorem c118_mfunb_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c118_mfunb ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + 0.014102 * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.472584) :=
  rfl

/-- Component 118 gate (box 27; chain chain_idx118; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c118_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b27lo i) (b27hi i))
        (fun t => c118_mfunb (Function.update y i t) - K118 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb27 j) → B118 ≤ c118_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 2 + 3 / 2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + 0.014102 * y1 + 0.066241 * (y2 + y3 + y5 + y6) + (-0.472584) > 0 := by
  have hpos : (0 : ℝ) <
      B118 - ∑ i, R118 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R118 i = K118 i * (b27hi i - b27lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K118 0 = (0 : ℝ) := by rfl
    have t1 : K118 1 = (0 : ℝ) := by rfl
    have t2 : K118 2 = (0 : ℝ) := by rfl
    have t3 : K118 3 = (0 : ℝ) := by rfl
    have t4 : K118 4 = (0 : ℝ) := by rfl
    have t5 : K118 5 = (0 : ℝ) := by rfl
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
    have eb : B118 = ((57932445597151768384501/28823037615171174400000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K118 i := by
    intro i; fin_cases i <;> norm_num [K118]
  have hR0 : ∀ i, 0 ≤ R118 i := by
    intro i; fin_cases i <;> norm_num [R118, K118, b27lo, b27hi]
  have hchain := chain_idx118 c118_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c118_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 119 gate (box 28; chain chain_idx119; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c119_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => c112_mfunb (Function.update y i t) - K119 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B119 ≤ c112_mfunb v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.066935) * dihY y1 y2 y3 y4 y5 y6 + (-0.021495) * y1 + (-0.066241) * (y2 + y3 + y5 + y6) + 0.685308 > 0 := by
  have hpos : (0 : ℝ) <
      B119 - ∑ i, R119 i := by
    rw [sumFin6b]
    have ev : ∀ i : Fin 6, R119 i = K119 i * (b28hi i - b28lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K119 0 = (0 : ℝ) := by rfl
    have t1 : K119 1 = (0 : ℝ) := by rfl
    have t2 : K119 2 = (0 : ℝ) := by rfl
    have t3 : K119 3 = (0 : ℝ) := by rfl
    have t4 : K119 4 = (0 : ℝ) := by rfl
    have t5 : K119 5 = (0 : ℝ) := by rfl
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
    have eb : B119 = ((7238830132115033097287123/3602879701896396800000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K119 i := by
    intro i; fin_cases i <;> norm_num [K119]
  have hR0 : ∀ i, 0 ≤ R119 i := by
    intro i; fin_cases i <;> norm_num [R119, K119, b28lo, b28hi]
  have hchain := chain_idx119 c112_mfunb hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c112_mfunb_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-! ### Axiom audit -/

#print axioms c60_gate

#print axioms c61_gate

#print axioms c62_gate

#print axioms c63_gate

#print axioms c64_gate

#print axioms c65_gate

#print axioms c66_gate

#print axioms c67_gate

#print axioms c68_gate

#print axioms c69_gate

#print axioms c70_gate

#print axioms c71_gate

#print axioms c72_gate

#print axioms c73_gate

#print axioms c74_gate

#print axioms c75_gate

#print axioms c76_gate

#print axioms c77_gate

#print axioms c78_gate

#print axioms c79_gate

#print axioms c80_gate

#print axioms c81_gate

#print axioms c82_gate

#print axioms c83_gate

#print axioms c84_gate

#print axioms c85_gate

#print axioms c86_gate

#print axioms c87_gate

#print axioms c88_gate

#print axioms c89_gate

#print axioms c90_gate

#print axioms c91_gate

#print axioms c92_gate

#print axioms c93_gate

#print axioms c94_gate

#print axioms c95_gate

#print axioms c96_gate

#print axioms c97_gate

#print axioms c98_gate

#print axioms c99_gate

#print axioms c100_gate

#print axioms c101_gate

#print axioms c102_gate

#print axioms c103_gate

#print axioms c104_gate

#print axioms c105_gate

#print axioms c106_gate

#print axioms c107_gate

#print axioms c108_gate

#print axioms c109_gate

#print axioms c110_gate

#print axioms c111_gate

#print axioms c112_gate

#print axioms c113_gate

#print axioms c114_gate

#print axioms c115_gate

#print axioms c116_gate

#print axioms c117_gate

#print axioms c118_gate

#print axioms c119_gate

end Kepler.Text
