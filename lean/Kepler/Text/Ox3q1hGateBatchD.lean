/-
Ox3q1hGateBatch: S4 per-conjunct gates, components 180-229 (of 230; LIN = idx ≡ 0 mod 5).
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
theorem sumFin6d (f : Fin 6 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_six]

/-- Component 180 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c180_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.062681 + ((-0.026929) + (-0.06441) + 0.176245 + (-0.084906)) * y1 + 2 * (0.023742 + (-0.023742)) * y12 + 2 * ((-0.023742) + 0.023742) * y23 + 2 * (0.023742 + (-0.023742)) * y34 + 2 * ((-0.023742) + 0.023742) * y41 + ((-0.242815) + 0.273568 + (-0.72849) + 0.3039) < 0 :=
  ox3q1hLin_180

/-- Margin function of conjunct 181 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c181_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.062681 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.026929) * (y 0) + 0.023742 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.242815)

theorem c181_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c181_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.026929) * y1 + 0.023742 * (y2 + y3 + y5 + y6) + (-0.242815) :=
  rfl

/-- Component 181 gate (box 42; chain chain_idx181; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c181_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b42lo i) (b42hi i))
        (fun t => c181_mfund (Function.update y i t) - K181 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb42 j) → B181 ≤ c181_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.026929) * y1 + 0.023742 * (y2 + y3 + y5 + y6) + (-0.242815) > 0 := by
  have hpos : (0 : ℝ) <
      B181 - ∑ i, R181 i := by
    rw [sumFin6d]
    have e0 : R181 0 = (0 : ℝ) := by rfl
    have e1 : R181 1 = (0 : ℝ) := by rfl
    have e2 : R181 2 = (0 : ℝ) := by rfl
    have e3 : R181 3 = ((1526781846331711/7036874417766400000) : ℝ) := by rfl
    have e4 : R181 4 = (0 : ℝ) := by rfl
    have e5 : R181 5 = (0 : ℝ) := by rfl
    have eb : B181 = ((102347159822386772423857/22517998136852480000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b42lo j) (b42hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b42lo, b42hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K181 i := by
    intro i; fin_cases i <;> norm_num [K181]
  have hR0 : ∀ i, 0 ≤ R181 i := by
    intro i; fin_cases i <;> norm_num [R181, K181, b42lo, b42hi]
  have hchain := chain_idx181 c181_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c181_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 182 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c182_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.062681 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.06441) * (y 0) + (-0.023742) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.273568

theorem c182_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c182_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.06441) * y1 + (-0.023742) * (y2 + y3 + y5 + y6) + 0.273568 :=
  rfl

/-- Component 182 gate (box 10; chain chain_idx182; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c182_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => c182_mfund (Function.update y i t) - K182 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B182 ≤ c182_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.06441) * y1 + (-0.023742) * (y2 + y3 + y5 + y6) + 0.273568 > 0 := by
  have hpos : (0 : ℝ) <
      B182 - ∑ i, R182 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R182 i = K182 i * (b10hi i - b10lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K182 0 = (0 : ℝ) := by rfl
    have t1 : K182 1 = (0 : ℝ) := by rfl
    have t2 : K182 2 = (0 : ℝ) := by rfl
    have t3 : K182 3 = (0 : ℝ) := by rfl
    have t4 : K182 4 = (0 : ℝ) := by rfl
    have t5 : K182 5 = (0 : ℝ) := by rfl
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
    have eb : B182 = ((4090146674144735169433219/900719925474099200000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K182 i := by
    intro i; fin_cases i <;> norm_num [K182]
  have hR0 : ∀ i, 0 ≤ R182 i := by
    intro i; fin_cases i <;> norm_num [R182, K182, b10lo, b10hi]
  have hchain := chain_idx182 c182_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c182_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 183 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c183_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.062681 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.176245 * (y 0) + 0.023742 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.72849)

theorem c183_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c183_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + 0.176245 * y1 + 0.023742 * (y2 + y3 + y5 + y6) + (-0.72849) :=
  rfl

/-- Component 183 gate (box 10; chain chain_idx183; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c183_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => c183_mfund (Function.update y i t) - K183 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B183 ≤ c183_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + 0.176245 * y1 + 0.023742 * (y2 + y3 + y5 + y6) + (-0.72849) > 0 := by
  have hpos : (0 : ℝ) <
      B183 - ∑ i, R183 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R183 i = K183 i * (b10hi i - b10lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K183 0 = (0 : ℝ) := by rfl
    have t1 : K183 1 = (0 : ℝ) := by rfl
    have t2 : K183 2 = (0 : ℝ) := by rfl
    have t3 : K183 3 = (0 : ℝ) := by rfl
    have t4 : K183 4 = (0 : ℝ) := by rfl
    have t5 : K183 5 = (0 : ℝ) := by rfl
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
    have eb : B183 = ((655264855832160929357531/144115188075855872000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K183 i := by
    intro i; fin_cases i <;> norm_num [K183]
  have hR0 : ∀ i, 0 ≤ R183 i := by
    intro i; fin_cases i <;> norm_num [R183, K183, b10lo, b10hi]
  have hchain := chain_idx183 c183_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c183_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 184 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c184_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.062681 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.084906) * (y 0) + (-0.023742) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.3039

theorem c184_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c184_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.084906) * y1 + (-0.023742) * (y2 + y3 + y5 + y6) + 0.3039 :=
  rfl

/-- Component 184 gate (box 11; chain chain_idx184; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c184_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => c184_mfund (Function.update y i t) - K184 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B184 ≤ c184_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 2 + 3 / 2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.084906) * y1 + (-0.023742) * (y2 + y3 + y5 + y6) + 0.3039 > 0 := by
  have hpos : (0 : ℝ) <
      B184 - ∑ i, R184 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R184 i = K184 i * (b11hi i - b11lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K184 0 = (0 : ℝ) := by rfl
    have t1 : K184 1 = (0 : ℝ) := by rfl
    have t2 : K184 2 = (0 : ℝ) := by rfl
    have t3 : K184 3 = (0 : ℝ) := by rfl
    have t4 : K184 4 = (0 : ℝ) := by rfl
    have t5 : K184 5 = (0 : ℝ) := by rfl
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
    have eb : B184 = ((818148234235347152866593/180143985094819840000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K184 i := by
    intro i; fin_cases i <;> norm_num [K184]
  have hR0 : ∀ i, 0 ≤ R184 i := by
    intro i; fin_cases i <;> norm_num [R184, K184, b11lo, b11hi]
  have hchain := chain_idx184 c184_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c184_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 185 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c185_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.062681 + ((-0.026929) + 0.176245 + (-0.084906) + (-0.06441)) * y1 + 2 * (0.023742 + (-0.023742)) * y12 + 2 * ((-0.023742) + 0.023742) * y23 + 2 * (0.023742 + (-0.023742)) * y34 + 2 * ((-0.023742) + 0.023742) * y41 + ((-0.242815) + (-0.348621) + (-0.075969) + 0.273568) < 0 :=
  ox3q1hLin_185

/-- Component 186 gate (box 42; chain chain_idx186; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c186_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b42lo i) (b42hi i))
        (fun t => c181_mfund (Function.update y i t) - K186 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb42 j) → B186 ≤ c181_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.026929) * y1 + 0.023742 * (y2 + y3 + y5 + y6) + (-0.242815) > 0 := by
  have hpos : (0 : ℝ) <
      B186 - ∑ i, R186 i := by
    rw [sumFin6d]
    have e0 : R186 0 = (0 : ℝ) := by rfl
    have e1 : R186 1 = (0 : ℝ) := by rfl
    have e2 : R186 2 = (0 : ℝ) := by rfl
    have e3 : R186 3 = ((1526781846331711/7036874417766400000) : ℝ) := by rfl
    have e4 : R186 4 = (0 : ℝ) := by rfl
    have e5 : R186 5 = (0 : ℝ) := by rfl
    have eb : B186 = ((102347159822386772423857/22517998136852480000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b42lo j) (b42hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b42lo, b42hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K186 i := by
    intro i; fin_cases i <;> norm_num [K186]
  have hR0 : ∀ i, 0 ≤ R186 i := by
    intro i; fin_cases i <;> norm_num [R186, K186, b42lo, b42hi]
  have hchain := chain_idx186 c181_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c181_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 187 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c187_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.062681 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.176245 * (y 0) + (-0.023742) * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.348621)

theorem c187_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c187_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + 0.176245 * y1 + (-0.023742) * (y2 + y3 + y5 + y6) + (-0.348621) :=
  rfl

/-- Component 187 gate (box 10; chain chain_idx187; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c187_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => c187_mfund (Function.update y i t) - K187 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B187 ≤ c187_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + 0.176245 * y1 + (-0.023742) * (y2 + y3 + y5 + y6) + (-0.348621) > 0 := by
  have hpos : (0 : ℝ) <
      B187 - ∑ i, R187 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R187 i = K187 i * (b10hi i - b10lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K187 0 = (0 : ℝ) := by rfl
    have t1 : K187 1 = (0 : ℝ) := by rfl
    have t2 : K187 2 = (0 : ℝ) := by rfl
    have t3 : K187 3 = (0 : ℝ) := by rfl
    have t4 : K187 4 = (0 : ℝ) := by rfl
    have t5 : K187 5 = (0 : ℝ) := by rfl
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
    have eb : B187 = ((654832510267933361741531/144115188075855872000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K187 i := by
    intro i; fin_cases i <;> norm_num [K187]
  have hR0 : ∀ i, 0 ≤ R187 i := by
    intro i; fin_cases i <;> norm_num [R187, K187, b10lo, b10hi]
  have hchain := chain_idx187 c187_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c187_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 188 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c188_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.062681 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.084906) * (y 0) + 0.023742 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.075969)

theorem c188_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c188_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.084906) * y1 + 0.023742 * (y2 + y3 + y5 + y6) + (-0.075969) :=
  rfl

/-- Component 188 gate (box 11; chain chain_idx188; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c188_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => c188_mfund (Function.update y i t) - K188 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B188 ≤ c188_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 2 + 3 / 2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.084906) * y1 + 0.023742 * (y2 + y3 + y5 + y6) + (-0.075969) > 0 := by
  have hpos : (0 : ℝ) <
      B188 - ∑ i, R188 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R188 i = K188 i * (b11hi i - b11lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K188 0 = (0 : ℝ) := by rfl
    have t1 : K188 1 = (0 : ℝ) := by rfl
    have t2 : K188 2 = (0 : ℝ) := by rfl
    have t3 : K188 3 = (0 : ℝ) := by rfl
    have t4 : K188 4 = (0 : ℝ) := by rfl
    have t5 : K188 5 = (0 : ℝ) := by rfl
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
    have eb : B188 = ((818688666190631612386593/180143985094819840000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K188 i := by
    intro i; fin_cases i <;> norm_num [K188]
  have hR0 : ∀ i, 0 ≤ R188 i := by
    intro i; fin_cases i <;> norm_num [R188, K188, b11lo, b11hi]
  have hchain := chain_idx188 c188_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c188_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 189 gate (box 12; chain chain_idx189; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c189_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => c182_mfund (Function.update y i t) - K189 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B189 ≤ c182_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.06441) * y1 + (-0.023742) * (y2 + y3 + y5 + y6) + 0.273568 > 0 := by
  have hpos : (0 : ℝ) <
      B189 - ∑ i, R189 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R189 i = K189 i * (b12hi i - b12lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K189 0 = (0 : ℝ) := by rfl
    have t1 : K189 1 = (0 : ℝ) := by rfl
    have t2 : K189 2 = (0 : ℝ) := by rfl
    have t3 : K189 3 = (0 : ℝ) := by rfl
    have t4 : K189 4 = (0 : ℝ) := by rfl
    have t5 : K189 5 = (0 : ℝ) := by rfl
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
    have eb : B189 = ((4090146674144735169433219/900719925474099200000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K189 i := by
    intro i; fin_cases i <;> norm_num [K189]
  have hR0 : ∀ i, 0 ≤ R189 i := by
    intro i; fin_cases i <;> norm_num [R189, K189, b12lo, b12hi]
  have hchain := chain_idx189 c182_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c182_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 190 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c190_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.062681 + ((-0.026929) + (-0.084906) + 0.176245 + (-0.06441)) * y1 + 2 * (0.023742 + (-0.023742)) * y12 + 2 * ((-0.023742) + 0.023742) * y23 + 2 * (0.023742 + (-0.023742)) * y34 + 2 * ((-0.023742) + 0.023742) * y41 + ((-0.242815) + 0.3039 + (-0.72849) + 0.273568) < 0 :=
  ox3q1hLin_190

/-- Component 191 gate (box 42; chain chain_idx191; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c191_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b42lo i) (b42hi i))
        (fun t => c181_mfund (Function.update y i t) - K191 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb42 j) → B191 ≤ c181_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.026929) * y1 + 0.023742 * (y2 + y3 + y5 + y6) + (-0.242815) > 0 := by
  have hpos : (0 : ℝ) <
      B191 - ∑ i, R191 i := by
    rw [sumFin6d]
    have e0 : R191 0 = (0 : ℝ) := by rfl
    have e1 : R191 1 = (0 : ℝ) := by rfl
    have e2 : R191 2 = (0 : ℝ) := by rfl
    have e3 : R191 3 = ((1526781846331711/7036874417766400000) : ℝ) := by rfl
    have e4 : R191 4 = (0 : ℝ) := by rfl
    have e5 : R191 5 = (0 : ℝ) := by rfl
    have eb : B191 = ((102347159822386772423857/22517998136852480000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b42lo j) (b42hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b42lo, b42hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K191 i := by
    intro i; fin_cases i <;> norm_num [K191]
  have hR0 : ∀ i, 0 ≤ R191 i := by
    intro i; fin_cases i <;> norm_num [R191, K191, b42lo, b42hi]
  have hchain := chain_idx191 c181_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c181_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 192 gate (box 11; chain chain_idx192; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c192_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => c184_mfund (Function.update y i t) - K192 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B192 ≤ c184_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 2 + 3 / 2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.084906) * y1 + (-0.023742) * (y2 + y3 + y5 + y6) + 0.3039 > 0 := by
  have hpos : (0 : ℝ) <
      B192 - ∑ i, R192 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R192 i = K192 i * (b11hi i - b11lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K192 0 = (0 : ℝ) := by rfl
    have t1 : K192 1 = (0 : ℝ) := by rfl
    have t2 : K192 2 = (0 : ℝ) := by rfl
    have t3 : K192 3 = (0 : ℝ) := by rfl
    have t4 : K192 4 = (0 : ℝ) := by rfl
    have t5 : K192 5 = (0 : ℝ) := by rfl
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
    have eb : B192 = ((818148234235347152866593/180143985094819840000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K192 i := by
    intro i; fin_cases i <;> norm_num [K192]
  have hR0 : ∀ i, 0 ≤ R192 i := by
    intro i; fin_cases i <;> norm_num [R192, K192, b11lo, b11hi]
  have hchain := chain_idx192 c184_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c184_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 193 gate (box 12; chain chain_idx193; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c193_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => c183_mfund (Function.update y i t) - K193 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B193 ≤ c183_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + 0.176245 * y1 + 0.023742 * (y2 + y3 + y5 + y6) + (-0.72849) > 0 := by
  have hpos : (0 : ℝ) <
      B193 - ∑ i, R193 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R193 i = K193 i * (b12hi i - b12lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K193 0 = (0 : ℝ) := by rfl
    have t1 : K193 1 = (0 : ℝ) := by rfl
    have t2 : K193 2 = (0 : ℝ) := by rfl
    have t3 : K193 3 = (0 : ℝ) := by rfl
    have t4 : K193 4 = (0 : ℝ) := by rfl
    have t5 : K193 5 = (0 : ℝ) := by rfl
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
    have eb : B193 = ((655264855832160929357531/144115188075855872000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K193 i := by
    intro i; fin_cases i <;> norm_num [K193]
  have hR0 : ∀ i, 0 ≤ R193 i := by
    intro i; fin_cases i <;> norm_num [R193, K193, b12lo, b12hi]
  have hchain := chain_idx193 c183_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c183_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 194 gate (box 12; chain chain_idx194; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c194_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => c182_mfund (Function.update y i t) - K194 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B194 ≤ c182_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.062681 * dihY y1 y2 y3 y4 y5 y6 + (-0.06441) * y1 + (-0.023742) * (y2 + y3 + y5 + y6) + 0.273568 > 0 := by
  have hpos : (0 : ℝ) <
      B194 - ∑ i, R194 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R194 i = K194 i * (b12hi i - b12lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K194 0 = (0 : ℝ) := by rfl
    have t1 : K194 1 = (0 : ℝ) := by rfl
    have t2 : K194 2 = (0 : ℝ) := by rfl
    have t3 : K194 3 = (0 : ℝ) := by rfl
    have t4 : K194 4 = (0 : ℝ) := by rfl
    have t5 : K194 5 = (0 : ℝ) := by rfl
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
    have eb : B194 = ((4090146674144735169433219/900719925474099200000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K194 i := by
    intro i; fin_cases i <;> norm_num [K194]
  have hR0 : ∀ i, 0 ≤ R194 i := by
    intro i; fin_cases i <;> norm_num [R194, K194, b12lo, b12hi]
  have hchain := chain_idx194 c182_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c182_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 195 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c195_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * 0.061714 + ((-0.014502) + 0.134266 + (-0.059882) + (-0.059882)) * y1 + 2 * ((-0.02407) + 0.02407) * y12 + 2 * (0.02407 + (-0.02407)) * y23 + 2 * ((-0.02407) + (-0.02407)) * y34 + 2 * ((-0.02407) + (-0.02407)) * y41 + (0.104941 + (-0.631477) + 0.261947 + 0.261947) < 0 :=
  ox3q1hLin_195

/-- Margin function of conjunct 196 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c196_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + 0.061714 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.014502) * (y 0) + (-0.02407) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.104941

theorem c196_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c196_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.061714 * dihY y1 y2 y3 y4 y5 y6 + (-0.014502) * y1 + (-0.02407) * (y2 + y3 + y5 + y6) + 0.104941 :=
  rfl

/-- Component 196 gate (box 43; chain chain_idx196; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c196_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b43lo i) (b43hi i))
        (fun t => c196_mfund (Function.update y i t) - K196 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb43 j) → B196 ≤ c196_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + 0.061714 * dihY y1 y2 y3 y4 y5 y6 + (-0.014502) * y1 + (-0.02407) * (y2 + y3 + y5 + y6) + 0.104941 > 0 := by
  have hpos : (0 : ℝ) <
      B196 - ∑ i, R196 i := by
    rw [sumFin6d]
    have e0 : R196 0 = (0 : ℝ) := by rfl
    have e1 : R196 1 = (0 : ℝ) := by rfl
    have e2 : R196 2 = (0 : ℝ) := by rfl
    have e3 : R196 3 = ((753715220841029/3518437208883200000) : ℝ) := by rfl
    have e4 : R196 4 = (0 : ℝ) := by rfl
    have e5 : R196 5 = (0 : ℝ) := by rfl
    have eb : B196 = ((316746207853779033927209/360287970189639680000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b43lo j) (b43hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b43lo, b43hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K196 i := by
    intro i; fin_cases i <;> norm_num [K196]
  have hR0 : ∀ i, 0 ≤ R196 i := by
    intro i; fin_cases i <;> norm_num [R196, K196, b43lo, b43hi]
  have hchain := chain_idx196 c196_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c196_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 197 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c197_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.061714 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.134266 * (y 0) + 0.02407 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.631477)

theorem c197_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c197_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.061714 * dihY y1 y2 y3 y4 y5 y6 + 0.134266 * y1 + 0.02407 * (y2 + y3 + y5 + y6) + (-0.631477) :=
  rfl

/-- Component 197 gate (box 15; chain chain_idx197; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c197_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => c197_mfund (Function.update y i t) - K197 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B197 ≤ c197_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.061714 * dihY y1 y2 y3 y4 y5 y6 + 0.134266 * y1 + 0.02407 * (y2 + y3 + y5 + y6) + (-0.631477) > 0 := by
  have hpos : (0 : ℝ) <
      B197 - ∑ i, R197 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R197 i = K197 i * (b15hi i - b15lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K197 0 = (0 : ℝ) := by rfl
    have t1 : K197 1 = (0 : ℝ) := by rfl
    have t2 : K197 2 = (0 : ℝ) := by rfl
    have t3 : K197 3 = (0 : ℝ) := by rfl
    have t4 : K197 4 = (0 : ℝ) := by rfl
    have t5 : K197 5 = (0 : ℝ) := by rfl
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
    have eb : B197 = ((158925348430507312448539/180143985094819840000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K197 i := by
    intro i; fin_cases i <;> norm_num [K197]
  have hR0 : ∀ i, 0 ≤ R197 i := by
    intro i; fin_cases i <;> norm_num [R197, K197, b15lo, b15hi]
  have hchain := chain_idx197 c197_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c197_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 198 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c198_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + 0.061714 * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.059882) * (y 0) + (-0.02407) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.261947

theorem c198_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c198_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.061714 * dihY y1 y2 y3 y4 y5 y6 + (-0.059882) * y1 + (-0.02407) * (y2 + y3 + y5 + y6) + 0.261947 :=
  rfl

/-- Component 198 gate (box 15; chain chain_idx198; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c198_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => c198_mfund (Function.update y i t) - K198 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B198 ≤ c198_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.061714 * dihY y1 y2 y3 y4 y5 y6 + (-0.059882) * y1 + (-0.02407) * (y2 + y3 + y5 + y6) + 0.261947 > 0 := by
  have hpos : (0 : ℝ) <
      B198 - ∑ i, R198 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R198 i = K198 i * (b15hi i - b15lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K198 0 = (0 : ℝ) := by rfl
    have t1 : K198 1 = (0 : ℝ) := by rfl
    have t2 : K198 2 = (0 : ℝ) := by rfl
    have t3 : K198 3 = (0 : ℝ) := by rfl
    have t4 : K198 4 = (0 : ℝ) := by rfl
    have t5 : K198 5 = (0 : ℝ) := by rfl
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
    have eb : B198 = ((79728000761902369720047/90071992547409920000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K198 i := by
    intro i; fin_cases i <;> norm_num [K198]
  have hR0 : ∀ i, 0 ≤ R198 i := by
    intro i; fin_cases i <;> norm_num [R198, K198, b15lo, b15hi]
  have hchain := chain_idx198 c198_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c198_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 199 gate (box 15; chain chain_idx199; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c199_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => c198_mfund (Function.update y i t) - K199 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B199 ≤ c198_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.061714 * dihY y1 y2 y3 y4 y5 y6 + (-0.059882) * y1 + (-0.02407) * (y2 + y3 + y5 + y6) + 0.261947 > 0 := by
  have hpos : (0 : ℝ) <
      B199 - ∑ i, R199 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R199 i = K199 i * (b15hi i - b15lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K199 0 = (0 : ℝ) := by rfl
    have t1 : K199 1 = (0 : ℝ) := by rfl
    have t2 : K199 2 = (0 : ℝ) := by rfl
    have t3 : K199 3 = (0 : ℝ) := by rfl
    have t4 : K199 4 = (0 : ℝ) := by rfl
    have t5 : K199 5 = (0 : ℝ) := by rfl
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
    have eb : B199 = ((79728000761902369720047/90071992547409920000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K199 i := by
    intro i; fin_cases i <;> norm_num [K199]
  have hR0 : ∀ i, 0 ≤ R199 i := by
    intro i; fin_cases i <;> norm_num [R199, K199, b15lo, b15hi]
  have hchain := chain_idx199 c198_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c198_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 200 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c200_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.014413) + (-0.014413) + (-0.02241)) * y1 + 2 * (0.060747 + (-0.060747)) * y12 + 2 * ((-0.060747) + 0.060747) * y23 + 2 * (0.060747 + (-0.060747)) * y34 + 2 * ((-0.060747) + 0.060747) * y41 + ((-0.530637) + 0.594377 + (-0.377571) + 0.608509) < 0 :=
  ox3q1hLin_200

/-- Margin function of conjunct 201 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c201_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.051237 * (y 0) + 0.060747 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.530637)

theorem c201_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c201_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.530637) :=
  rfl

/-- Component 201 gate (box 44; chain chain_idx201; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c201_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b44lo i) (b44hi i))
        (fun t => c201_mfund (Function.update y i t) - K201 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb44 j) → B201 ≤ c201_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.530637) > 0 := by
  have hpos : (0 : ℝ) <
      B201 - ∑ i, R201 i := by
    rw [sumFin6d]
    have e0 : R201 0 = (0 : ℝ) := by rfl
    have e1 : R201 1 = (0 : ℝ) := by rfl
    have e2 : R201 2 = (0 : ℝ) := by rfl
    have e3 : R201 3 = ((7330444022387451/35184372088832000000) : ℝ) := by rfl
    have e4 : R201 4 = (0 : ℝ) := by rfl
    have e5 : R201 5 = (0 : ℝ) := by rfl
    have eb : B201 = ((177643353933028257987441/90071992547409920000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b44lo j) (b44hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b44lo, b44hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K201 i := by
    intro i; fin_cases i <;> norm_num [K201]
  have hR0 : ∀ i, 0 ≤ R201 i := by
    intro i; fin_cases i <;> norm_num [R201, K201, b44lo, b44hi]
  have hchain := chain_idx201 c201_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c201_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 202 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c202_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.014413) * (y 0) + (-0.060747) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.594377

theorem c202_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c202_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.594377 :=
  rfl

/-- Component 202 gate (box 17; chain chain_idx202; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c202_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => c202_mfund (Function.update y i t) - K202 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B202 ≤ c202_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.594377 > 0 := by
  have hpos : (0 : ℝ) <
      B202 - ∑ i, R202 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R202 i = K202 i * (b17hi i - b17lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K202 0 = (0 : ℝ) := by rfl
    have t1 : K202 1 = (0 : ℝ) := by rfl
    have t2 : K202 2 = (0 : ℝ) := by rfl
    have t3 : K202 3 = (0 : ℝ) := by rfl
    have t4 : K202 4 = (0 : ℝ) := by rfl
    have t5 : K202 5 = (0 : ℝ) := by rfl
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
    have eb : B202 = ((1775586001116581819034139/900719925474099200000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K202 i := by
    intro i; fin_cases i <;> norm_num [K202]
  have hR0 : ∀ i, 0 ≤ R202 i := by
    intro i; fin_cases i <;> norm_num [R202, K202, b17lo, b17hi]
  have hchain := chain_idx202 c202_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c202_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 203 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c203_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.014413) * (y 0) + 0.060747 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.377571)

theorem c203_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c203_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.377571) :=
  rfl

/-- Component 203 gate (box 17; chain chain_idx203; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c203_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => c203_mfund (Function.update y i t) - K203 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B203 ≤ c203_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.377571) > 0 := by
  have hpos : (0 : ℝ) <
      B203 - ∑ i, R203 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R203 i = K203 i * (b17hi i - b17lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K203 0 = (0 : ℝ) := by rfl
    have t1 : K203 1 = (0 : ℝ) := by rfl
    have t2 : K203 2 = (0 : ℝ) := by rfl
    have t3 : K203 3 = (0 : ℝ) := by rfl
    have t4 : K203 4 = (0 : ℝ) := by rfl
    have t5 : K203 5 = (0 : ℝ) := by rfl
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
    have eb : B203 = ((356291706314003806959607/180143985094819840000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K203 i := by
    intro i; fin_cases i <;> norm_num [K203]
  have hR0 : ∀ i, 0 ≤ R203 i := by
    intro i; fin_cases i <;> norm_num [R203, K203, b17lo, b17hi]
  have hchain := chain_idx203 c203_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c203_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 204 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c204_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.02241) * (y 0) + (-0.060747) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.608509

theorem c204_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c204_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.608509 :=
  rfl

/-- Component 204 gate (box 18; chain chain_idx204; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c204_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => c204_mfund (Function.update y i t) - K204 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B204 ≤ c204_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 4 + 7 / 4) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.608509 > 0 := by
  have hpos : (0 : ℝ) <
      B204 - ∑ i, R204 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R204 i = K204 i * (b18hi i - b18lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K204 0 = (0 : ℝ) := by rfl
    have t1 : K204 1 = (0 : ℝ) := by rfl
    have t2 : K204 2 = (0 : ℝ) := by rfl
    have t3 : K204 3 = (0 : ℝ) := by rfl
    have t4 : K204 4 = (0 : ℝ) := by rfl
    have t5 : K204 5 = (0 : ℝ) := by rfl
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
    have eb : B204 = ((35526606265659279942811/18014398509481984000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K204 i := by
    intro i; fin_cases i <;> norm_num [K204]
  have hR0 : ∀ i, 0 ≤ R204 i := by
    intro i; fin_cases i <;> norm_num [R204, K204, b18lo, b18hi]
  have hchain := chain_idx204 c204_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c204_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 205 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c205_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.014413) + (-0.02241) + (-0.014413)) * y1 + 2 * ((-0.073427) + 0.073427) * y12 + 2 * (0.073427 + (-0.073427)) * y23 + 2 * ((-0.073427) + 0.073427) * y34 + 2 * (0.073427 + (-0.073427)) * y41 + (0.542756 + (-0.479016) + 0.709954 + (-0.479016)) < 0 :=
  ox3q1hLin_205

/-- Margin function of conjunct 206 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c206_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.051237 * (y 0) + (-0.073427) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.542756

theorem c206_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c206_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + (-0.073427) * (y2 + y3 + y5 + y6) + 0.542756 :=
  rfl

/-- Component 206 gate (box 44; chain chain_idx206; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c206_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b44lo i) (b44hi i))
        (fun t => c206_mfund (Function.update y i t) - K206 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb44 j) → B206 ≤ c206_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + (-0.073427) * (y2 + y3 + y5 + y6) + 0.542756 > 0 := by
  have hpos : (0 : ℝ) <
      B206 - ∑ i, R206 i := by
    rw [sumFin6d]
    have e0 : R206 0 = (0 : ℝ) := by rfl
    have e1 : R206 1 = (0 : ℝ) := by rfl
    have e2 : R206 2 = (0 : ℝ) := by rfl
    have e3 : R206 3 = ((7330444022387451/35184372088832000000) : ℝ) := by rfl
    have e4 : R206 4 = (0 : ℝ) := by rfl
    have e5 : R206 5 = (0 : ℝ) := by rfl
    have eb : B206 = ((177733425925575667907441/90071992547409920000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b44lo j) (b44hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b44lo, b44hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K206 i := by
    intro i; fin_cases i <;> norm_num [K206]
  have hR0 : ∀ i, 0 ≤ R206 i := by
    intro i; fin_cases i <;> norm_num [R206, K206, b44lo, b44hi]
  have hchain := chain_idx206 c206_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c206_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 207 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c207_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.014413) * (y 0) + 0.073427 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.479016)

theorem c207_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c207_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + 0.073427 * (y2 + y3 + y5 + y6) + (-0.479016) :=
  rfl

/-- Component 207 gate (box 17; chain chain_idx207; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c207_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => c207_mfund (Function.update y i t) - K207 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B207 ≤ c207_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + 0.073427 * (y2 + y3 + y5 + y6) + (-0.479016) > 0 := by
  have hpos : (0 : ℝ) <
      B207 - ∑ i, R207 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R207 i = K207 i * (b17hi i - b17lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K207 0 = (0 : ℝ) := by rfl
    have t1 : K207 1 = (0 : ℝ) := by rfl
    have t2 : K207 2 = (0 : ℝ) := by rfl
    have t3 : K207 3 = (0 : ℝ) := by rfl
    have t4 : K207 4 = (0 : ℝ) := by rfl
    have t5 : K207 5 = (0 : ℝ) := by rfl
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
    have eb : B207 = ((355390986388529707759607/180143985094819840000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K207 i := by
    intro i; fin_cases i <;> norm_num [K207]
  have hR0 : ∀ i, 0 ≤ R207 i := by
    intro i; fin_cases i <;> norm_num [R207, K207, b17lo, b17hi]
  have hchain := chain_idx207 c207_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c207_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 208 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c208_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.02241) * (y 0) + (-0.073427) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.709954

theorem c208_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c208_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + (-0.073427) * (y2 + y3 + y5 + y6) + 0.709954 :=
  rfl

/-- Component 208 gate (box 18; chain chain_idx208; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c208_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => c208_mfund (Function.update y i t) - K208 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B208 ≤ c208_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 4 + 7 / 4) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + (-0.073427) * (y2 + y3 + y5 + y6) + 0.709954 > 0 := by
  have hpos : (0 : ℝ) <
      B208 - ∑ i, R208 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R208 i = K208 i * (b18hi i - b18lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K208 0 = (0 : ℝ) := by rfl
    have t1 : K208 1 = (0 : ℝ) := by rfl
    have t2 : K208 2 = (0 : ℝ) := by rfl
    have t3 : K208 3 = (0 : ℝ) := by rfl
    have t4 : K208 4 = (0 : ℝ) := by rfl
    have t5 : K208 5 = (0 : ℝ) := by rfl
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
    have eb : B208 = ((222367424337945947488883/112589990684262400000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K208 i := by
    intro i; fin_cases i <;> norm_num [K208]
  have hR0 : ∀ i, 0 ≤ R208 i := by
    intro i; fin_cases i <;> norm_num [R208, K208, b18lo, b18hi]
  have hchain := chain_idx208 c208_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c208_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 209 gate (box 19; chain chain_idx209; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c209_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => c207_mfund (Function.update y i t) - K209 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B209 ≤ c207_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + 0.073427 * (y2 + y3 + y5 + y6) + (-0.479016) > 0 := by
  have hpos : (0 : ℝ) <
      B209 - ∑ i, R209 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R209 i = K209 i * (b19hi i - b19lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K209 0 = (0 : ℝ) := by rfl
    have t1 : K209 1 = (0 : ℝ) := by rfl
    have t2 : K209 2 = (0 : ℝ) := by rfl
    have t3 : K209 3 = (0 : ℝ) := by rfl
    have t4 : K209 4 = (0 : ℝ) := by rfl
    have t5 : K209 5 = (0 : ℝ) := by rfl
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
    have eb : B209 = ((355390986388529707759607/180143985094819840000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K209 i := by
    intro i; fin_cases i <;> norm_num [K209]
  have hR0 : ∀ i, 0 ≤ R209 i := by
    intro i; fin_cases i <;> norm_num [R209, K209, b19lo, b19hi]
  have hchain := chain_idx209 c207_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c207_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 210 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c210_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.02241) + (-0.014413) + (-0.014413)) * y1 + 2 * ((-0.060747) + 0.060747) * y12 + 2 * (0.060747 + (-0.060747)) * y23 + 2 * ((-0.060747) + 0.060747) * y34 + 2 * (0.060747 + (-0.060747)) * y41 + (0.44131200000000004 + (-0.36344) + 0.594377 + (-0.377571)) < 0 :=
  ox3q1hLin_210

/-- Margin function of conjunct 211 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c211_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.051237 * (y 0) + (-0.060747) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.44131200000000004

theorem c211_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c211_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.44131200000000004 :=
  rfl

/-- Component 211 gate (box 44; chain chain_idx211; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c211_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b44lo i) (b44hi i))
        (fun t => c211_mfund (Function.update y i t) - K211 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb44 j) → B211 ≤ c211_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + 0.051237 * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.44131200000000004 > 0 := by
  have hpos : (0 : ℝ) <
      B211 - ∑ i, R211 i := by
    rw [sumFin6d]
    have e0 : R211 0 = (0 : ℝ) := by rfl
    have e1 : R211 1 = (0 : ℝ) := by rfl
    have e2 : R211 2 = (0 : ℝ) := by rfl
    have e3 : R211 3 = ((7330444022387451/35184372088832000000) : ℝ) := by rfl
    have e4 : R211 4 = (0 : ℝ) := by rfl
    have e5 : R211 5 = (0 : ℝ) := by rfl
    have eb : B211 = ((13857276402764814930245538781/7036874417766400000000000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b44lo j) (b44hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b44lo, b44hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K211 i := by
    intro i; fin_cases i <;> norm_num [K211]
  have hR0 : ∀ i, 0 ≤ R211 i := by
    intro i; fin_cases i <;> norm_num [R211, K211, b44lo, b44hi]
  have hchain := chain_idx211 c211_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c211_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 212 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c212_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.0469) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.02241) * (y 0) + 0.060747 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.36344)

theorem c212_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c212_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.36344) :=
  rfl

/-- Component 212 gate (box 18; chain chain_idx212; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c212_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => c212_mfund (Function.update y i t) - K212 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B212 ≤ c212_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (1 * hminus / 4 + 7 / 4) ≤ y4 → y4 ≤ (1 * hminus / 2 + 3 / 2) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.02241) * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.36344) > 0 := by
  have hpos : (0 : ℝ) <
      B212 - ∑ i, R212 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R212 i = K212 i * (b18hi i - b18lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K212 0 = (0 : ℝ) := by rfl
    have t1 : K212 1 = (0 : ℝ) := by rfl
    have t2 : K212 2 = (0 : ℝ) := by rfl
    have t3 : K212 3 = (0 : ℝ) := by rfl
    have t4 : K212 4 = (0 : ℝ) := by rfl
    have t5 : K212 5 = (0 : ℝ) := by rfl
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
    have eb : B212 = ((35580649461187725894811/18014398509481984000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K212 i := by
    intro i; fin_cases i <;> norm_num [K212]
  have hR0 : ∀ i, 0 ≤ R212 i := by
    intro i; fin_cases i <;> norm_num [R212, K212, b18lo, b18hi]
  have hchain := chain_idx212 c212_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c212_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 213 gate (box 19; chain chain_idx213; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c213_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => c202_mfund (Function.update y i t) - K213 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B213 ≤ c202_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + (-0.060747) * (y2 + y3 + y5 + y6) + 0.594377 > 0 := by
  have hpos : (0 : ℝ) <
      B213 - ∑ i, R213 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R213 i = K213 i * (b19hi i - b19lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K213 0 = (0 : ℝ) := by rfl
    have t1 : K213 1 = (0 : ℝ) := by rfl
    have t2 : K213 2 = (0 : ℝ) := by rfl
    have t3 : K213 3 = (0 : ℝ) := by rfl
    have t4 : K213 4 = (0 : ℝ) := by rfl
    have t5 : K213 5 = (0 : ℝ) := by rfl
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
    have eb : B213 = ((1775586001116581819034139/900719925474099200000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K213 i := by
    intro i; fin_cases i <;> norm_num [K213]
  have hR0 : ∀ i, 0 ≤ R213 i := by
    intro i; fin_cases i <;> norm_num [R213, K213, b19lo, b19hi]
  have hchain := chain_idx213 c202_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c202_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 214 gate (box 19; chain chain_idx214; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c214_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => c203_mfund (Function.update y i t) - K214 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B214 ≤ c203_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.0469) * dihY y1 y2 y3 y4 y5 y6 + (-0.014413) * y1 + 0.060747 * (y2 + y3 + y5 + y6) + (-0.377571) > 0 := by
  have hpos : (0 : ℝ) <
      B214 - ∑ i, R214 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R214 i = K214 i * (b19hi i - b19lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K214 0 = (0 : ℝ) := by rfl
    have t1 : K214 1 = (0 : ℝ) := by rfl
    have t2 : K214 2 = (0 : ℝ) := by rfl
    have t3 : K214 3 = (0 : ℝ) := by rfl
    have t4 : K214 4 = (0 : ℝ) := by rfl
    have t5 : K214 5 = (0 : ℝ) := by rfl
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
    have eb : B214 = ((356291706314003806959607/180143985094819840000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K214 i := by
    intro i; fin_cases i <;> norm_num [K214]
  have hR0 : ∀ i, 0 ≤ R214 i := by
    intro i; fin_cases i <;> norm_num [R214, K214, b19lo, b19hi]
  have hchain := chain_idx214 c203_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c203_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 215 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c215_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.036939) + (0.050064 + (-0.016688) + (-0.016688) + (-0.016688)) * y1 + 2 * (0.057593 + (-0.057593)) * y12 + 2 * ((-0.057593) + 0.057593) * y23 + 2 * (0.057593 + (-0.057593)) * y34 + 2 * ((-0.057593) + 0.057593) * y41 + ((-0.523604) + 0.559062 + (-0.362427) + 0.559062) < 0 :=
  ox3q1hLin_215

/-- Margin function of conjunct 216 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c216_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.036939) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.050064 * (y 0) + 0.057593 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.523604)

theorem c216_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c216_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + 0.050064 * y1 + 0.057593 * (y2 + y3 + y5 + y6) + (-0.523604) :=
  rfl

/-- Component 216 gate (box 45; S4.5 split-grid chain
`chain_split_idx216`, split factors per SPLIT_PLAN route `Y4PATCH:y4`, m_min =
2; supersedes the hfeas-slot placeholder whose unsplit feasibility is
FALSE per KREBATE). -/

theorem c216_gate
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit216 i →
      ConcaveOn ℝ (Set.Icc (gsplit216 i k) (gsplit216 i (k + 1)))
        (fun t => c216_mfund (Function.update y i t) - K216 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split216 j) → B216 ≤ c216_mfund v) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + 0.050064 * y1 + 0.057593 * (y2 + y3 + y5 + y6) + (-0.523604) > 0 := by
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b45lo j) (b45hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b45lo, b45hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hchain := chain_split_idx216 c216_mfund hslp hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c216_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  have hpos := feas_split_idx216
  linarith [hchain, hpos]

/-- Margin function of conjunct 217 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c217_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.036939) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.016688) * (y 0) + (-0.057593) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.559062

theorem c217_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c217_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + (-0.016688) * y1 + (-0.057593) * (y2 + y3 + y5 + y6) + 0.559062 :=
  rfl

/-- Component 217 gate (box 21; chain chain_idx217; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c217_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => c217_mfund (Function.update y i t) - K217 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B217 ≤ c217_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + (-0.016688) * y1 + (-0.057593) * (y2 + y3 + y5 + y6) + 0.559062 > 0 := by
  have hpos : (0 : ℝ) <
      B217 - ∑ i, R217 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R217 i = K217 i * (b21hi i - b21lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K217 0 = (0 : ℝ) := by rfl
    have t1 : K217 1 = (0 : ℝ) := by rfl
    have t2 : K217 2 = (0 : ℝ) := by rfl
    have t3 : K217 3 = (0 : ℝ) := by rfl
    have t4 : K217 4 = (0 : ℝ) := by rfl
    have t5 : K217 5 = (0 : ℝ) := by rfl
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
    have eb : B217 = ((295631055591770941384851/900719925474099200000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K217 i := by
    intro i; fin_cases i <;> norm_num [K217]
  have hR0 : ∀ i, 0 ≤ R217 i := by
    intro i; fin_cases i <;> norm_num [R217, K217, b21lo, b21hi]
  have hchain := chain_idx217 c217_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c217_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 218 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c218_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.036939) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.016688) * (y 0) + 0.057593 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.362427)

theorem c218_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c218_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + (-0.016688) * y1 + 0.057593 * (y2 + y3 + y5 + y6) + (-0.362427) :=
  rfl

/-- Component 218 gate (box 21; chain chain_idx218; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c218_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => c218_mfund (Function.update y i t) - K218 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B218 ≤ c218_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + (-0.016688) * y1 + 0.057593 * (y2 + y3 + y5 + y6) + (-0.362427) > 0 := by
  have hpos : (0 : ℝ) <
      B218 - ∑ i, R218 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R218 i = K218 i * (b21hi i - b21lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K218 0 = (0 : ℝ) := by rfl
    have t1 : K218 1 = (0 : ℝ) := by rfl
    have t2 : K218 2 = (0 : ℝ) := by rfl
    have t3 : K218 3 = (0 : ℝ) := by rfl
    have t4 : K218 4 = (0 : ℝ) := by rfl
    have t5 : K218 5 = (0 : ℝ) := by rfl
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
    have eb : B218 = ((23734450474249571838381/72057594037927936000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K218 i := by
    intro i; fin_cases i <;> norm_num [K218]
  have hR0 : ∀ i, 0 ≤ R218 i := by
    intro i; fin_cases i <;> norm_num [R218, K218, b21lo, b21hi]
  have hchain := chain_idx218 c218_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c218_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 219 gate (box 21; chain chain_idx219; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c219_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => c217_mfund (Function.update y i t) - K219 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B219 ≤ c217_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.036939) * dihY y1 y2 y3 y4 y5 y6 + (-0.016688) * y1 + (-0.057593) * (y2 + y3 + y5 + y6) + 0.559062 > 0 := by
  have hpos : (0 : ℝ) <
      B219 - ∑ i, R219 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R219 i = K219 i * (b21hi i - b21lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K219 0 = (0 : ℝ) := by rfl
    have t1 : K219 1 = (0 : ℝ) := by rfl
    have t2 : K219 2 = (0 : ℝ) := by rfl
    have t3 : K219 3 = (0 : ℝ) := by rfl
    have t4 : K219 4 = (0 : ℝ) := by rfl
    have t5 : K219 5 = (0 : ℝ) := by rfl
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
    have eb : B219 = ((295631055591770941384851/900719925474099200000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K219 i := by
    intro i; fin_cases i <;> norm_num [K219]
  have hR0 : ∀ i, 0 ≤ R219 i := by
    intro i; fin_cases i <;> norm_num [R219, K219, b21lo, b21hi]
  have hchain := chain_idx219 c217_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c217_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 220 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c220_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.177145) + (0.151334 + 0.041584 + 0.00995 + 0.041584) * y1 + 2 * ((-0.103308) + 0.103308) * y12 + 2 * (0.103308 + (-0.103308)) * y23 + 2 * ((-0.103308) + 0.103308) * y34 + 2 * (0.103308 + (-0.103308)) * y41 + (0.774954 + (-0.677721) + 1.057518 + (-0.677721)) < 0 :=
  ox3q1hLin_220

/-- Margin function of conjunct 221 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c221_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.177145) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.151334 * (y 0) + (-0.103308) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.774954

theorem c221_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c221_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.177145) * dihY y1 y2 y3 y4 y5 y6 + 0.151334 * y1 + (-0.103308) * (y2 + y3 + y5 + y6) + 0.774954 :=
  rfl

/-- Component 221 gate (box 46; chain chain_idx221; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c221_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b46lo i) (b46hi i))
        (fun t => c221_mfund (Function.update y i t) - K221 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb46 j) → B221 ≤ c221_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.177145) * dihY y1 y2 y3 y4 y5 y6 + 0.151334 * y1 + (-0.103308) * (y2 + y3 + y5 + y6) + 0.774954 > 0 := by
  have hpos : (0 : ℝ) <
      B221 - ∑ i, R221 i := by
    rw [sumFin6d]
    have e0 : R221 0 = (0 : ℝ) := by rfl
    have e1 : R221 1 = (0 : ℝ) := by rfl
    have e2 : R221 2 = (0 : ℝ) := by rfl
    have e3 : R221 3 = ((6969804208472547/35184372088832000000) : ℝ) := by rfl
    have e4 : R221 4 = (0 : ℝ) := by rfl
    have e5 : R221 5 = (0 : ℝ) := by rfl
    have eb : B221 = ((64068616357792110805867/72057594037927936000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b46lo j) (b46hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b46lo, b46hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K221 i := by
    intro i; fin_cases i <;> norm_num [K221]
  have hR0 : ∀ i, 0 ≤ R221 i := by
    intro i; fin_cases i <;> norm_num [R221, K221, b46lo, b46hi]
  have hchain := chain_idx221 c221_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c221_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 222 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c222_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.177145) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.041584 * (y 0) + 0.103308 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.677721)

theorem c222_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c222_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.177145) * dihY y1 y2 y3 y4 y5 y6 + 0.041584 * y1 + 0.103308 * (y2 + y3 + y5 + y6) + (-0.677721) :=
  rfl

/-- Component 222 gate (box 23; chain chain_idx222; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c222_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => c222_mfund (Function.update y i t) - K222 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B222 ≤ c222_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.177145) * dihY y1 y2 y3 y4 y5 y6 + 0.041584 * y1 + 0.103308 * (y2 + y3 + y5 + y6) + (-0.677721) > 0 := by
  have hpos : (0 : ℝ) <
      B222 - ∑ i, R222 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R222 i = K222 i * (b23hi i - b23lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K222 0 = (0 : ℝ) := by rfl
    have t1 : K222 1 = (0 : ℝ) := by rfl
    have t2 : K222 2 = (0 : ℝ) := by rfl
    have t3 : K222 3 = (0 : ℝ) := by rfl
    have t4 : K222 4 = (0 : ℝ) := by rfl
    have t5 : K222 5 = (0 : ℝ) := by rfl
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
    have eb : B222 = ((63491846600753696803367/72057594037927936000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K222 i := by
    intro i; fin_cases i <;> norm_num [K222]
  have hR0 : ∀ i, 0 ≤ R222 i := by
    intro i; fin_cases i <;> norm_num [R222, K222, b23lo, b23hi]
  have hchain := chain_idx222 c222_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c222_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 223 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c223_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.177145) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.00995 * (y 0) + (-0.103308) * ((y 1) + (y 2) + (y 4) + (y 5)) + 1.057518

theorem c223_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c223_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.177145) * dihY y1 y2 y3 y4 y5 y6 + 0.00995 * y1 + (-0.103308) * (y2 + y3 + y5 + y6) + 1.057518 :=
  rfl

/-- Component 223 gate (box 23; chain chain_idx223; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c223_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => c223_mfund (Function.update y i t) - K223 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B223 ≤ c223_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.177145) * dihY y1 y2 y3 y4 y5 y6 + 0.00995 * y1 + (-0.103308) * (y2 + y3 + y5 + y6) + 1.057518 > 0 := by
  have hpos : (0 : ℝ) <
      B223 - ∑ i, R223 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R223 i = K223 i * (b23hi i - b23lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K223 0 = (0 : ℝ) := by rfl
    have t1 : K223 1 = (0 : ℝ) := by rfl
    have t2 : K223 2 = (0 : ℝ) := by rfl
    have t3 : K223 3 = (0 : ℝ) := by rfl
    have t4 : K223 4 = (0 : ℝ) := by rfl
    have t5 : K223 5 = (0 : ℝ) := by rfl
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
    have eb : B223 = ((798552523678705351767281/900719925474099200000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K223 i := by
    intro i; fin_cases i <;> norm_num [K223]
  have hR0 : ∀ i, 0 ≤ R223 i := by
    intro i; fin_cases i <;> norm_num [R223, K223, b23lo, b23hi]
  have hchain := chain_idx223 c223_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c223_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 224 gate (box 23; chain chain_idx224; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c224_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => c222_mfund (Function.update y i t) - K224 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B224 ≤ c222_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (1 * hminus / 4 + 7 / 4) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.177145) * dihY y1 y2 y3 y4 y5 y6 + 0.041584 * y1 + 0.103308 * (y2 + y3 + y5 + y6) + (-0.677721) > 0 := by
  have hpos : (0 : ℝ) <
      B224 - ∑ i, R224 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R224 i = K224 i * (b23hi i - b23lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K224 0 = (0 : ℝ) := by rfl
    have t1 : K224 1 = (0 : ℝ) := by rfl
    have t2 : K224 2 = (0 : ℝ) := by rfl
    have t3 : K224 3 = (0 : ℝ) := by rfl
    have t4 : K224 4 = (0 : ℝ) := by rfl
    have t5 : K224 5 = (0 : ℝ) := by rfl
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
    have eb : B224 = ((63491846600753696803367/72057594037927936000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K224 i := by
    intro i; fin_cases i <;> norm_num [K224]
  have hR0 : ∀ i, 0 ≤ R224 i := by
    intro i; fin_cases i <;> norm_num [R224, K224, b23lo, b23hi]
  have hchain := chain_idx224 c222_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c222_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 225 gate (LINEAR; closed by Ox3q1hLin46). -/

theorem c225_gate : ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.121189) + (0.06473 + (-0.016252) + (-0.022099) + (-0.016252)) * y1 + 2 * ((-0.084657) + 0.084657) * y12 + 2 * (0.084657 + (-0.084657)) * y23 + 2 * ((-0.084657) + 0.084657) * y34 + 2 * (0.084657 + (-0.084657)) * y41 + (0.741383 + (-0.45858) + 0.911046 + (-0.45858)) < 0 :=
  ox3q1hLin_225

/-- Margin function of conjunct 226 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c226_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun / 2 + (bump ((y 0) / 2) - bump ((y 3) / 2)) + (-0.121189) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + 0.06473 * (y 0) + (-0.084657) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.741383

theorem c226_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c226_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.121189) * dihY y1 y2 y3 y4 y5 y6 + 0.06473 * y1 + (-0.084657) * (y2 + y3 + y5 + y6) + 0.741383 :=
  rfl

/-- Component 226 gate (box 47; chain chain_idx226; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c226_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b47lo i) (b47hi i))
        (fun t => c226_mfund (Function.update y i t) - K226 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb47 j) → B226 ≤ c226_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2 * hminus) ≤ y4 → y4 ≤ (2 * h0) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + (bump (y1 / 2) - bump (y4 / 2)) + (-0.121189) * dihY y1 y2 y3 y4 y5 y6 + 0.06473 * y1 + (-0.084657) * (y2 + y3 + y5 + y6) + 0.741383 > 0 := by
  have hpos : (0 : ℝ) <
      B226 - ∑ i, R226 i := by
    rw [sumFin6d]
    have e0 : R226 0 = (0 : ℝ) := by rfl
    have e1 : R226 1 = (0 : ℝ) := by rfl
    have e2 : R226 2 = (0 : ℝ) := by rfl
    have e3 : R226 3 = ((3664122499565469/17592186044416000000) : ℝ) := by rfl
    have e4 : R226 4 = (0 : ℝ) := by rfl
    have e5 : R226 5 = (0 : ℝ) := by rfl
    have eb : B226 = ((95474929009721561119337/72057594037927936000000000) : ℝ) := by rfl
    norm_num [e0, e1, e2, e3, e4, e5, eb]
  intro y1 y2 y3 y4 y5 y6 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26 : ℝ) ∧ hplus = (1.3254 : ℝ) := ⟨rfl, rfl⟩
  have hx : ∀ j : Fin 6, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (b47lo j) (b47hi j) := by
    intro j
    fin_cases j
    all_goals
      norm_num [b47lo, b47hi]
      constructor <;> linarith [hmn.1, hmn.2, hcon.1, hcon.2]
  have hK0 : ∀ i, 0 ≤ K226 i := by
    intro i; fin_cases i <;> norm_num [K226]
  have hR0 : ∀ i, 0 ≤ R226 i := by
    intro i; fin_cases i <;> norm_num [R226, K226, b47lo, b47hi]
  have hchain := chain_idx226 c226_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c226_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 227 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c227_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.121189) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.016252) * (y 0) + 0.084657 * ((y 1) + (y 2) + (y 4) + (y 5)) + (-0.45858)

theorem c227_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c227_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.121189) * dihY y1 y2 y3 y4 y5 y6 + (-0.016252) * y1 + 0.084657 * (y2 + y3 + y5 + y6) + (-0.45858) :=
  rfl

/-- Component 227 gate (box 26; chain chain_idx227; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c227_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => c227_mfund (Function.update y i t) - K227 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B227 ≤ c227_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.121189) * dihY y1 y2 y3 y4 y5 y6 + (-0.016252) * y1 + 0.084657 * (y2 + y3 + y5 + y6) + (-0.45858) > 0 := by
  have hpos : (0 : ℝ) <
      B227 - ∑ i, R227 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R227 i = K227 i * (b26hi i - b26lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K227 0 = (0 : ℝ) := by rfl
    have t1 : K227 1 = (0 : ℝ) := by rfl
    have t2 : K227 2 = (0 : ℝ) := by rfl
    have t3 : K227 3 = (0 : ℝ) := by rfl
    have t4 : K227 4 = (0 : ℝ) := by rfl
    have t5 : K227 5 = (0 : ℝ) := by rfl
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
    have eb : B227 = ((9571791836237643399681/7205759403792793600000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K227 i := by
    intro i; fin_cases i <;> norm_num [K227]
  have hR0 : ∀ i, 0 ≤ R227 i := by
    intro i; fin_cases i <;> norm_num [R227, K227, b26lo, b26hi]
  have hchain := chain_idx227 c227_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c227_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Margin function of conjunct 228 (verbatim conclusion, vectorized; shared by identical conjuncts). -/

noncomputable def c228_mfund (y : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) lmfun + (-0.121189) * dihY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) + (-0.022099) * (y 0) + (-0.084657) * ((y 1) + (y 2) + (y 4) + (y 5)) + 0.911046

theorem c228_mfund_at (y1 y2 y3 y4 y5 y6 : ℝ) :
    c228_mfund ![y1, y2, y3, y4, y5, y6] =
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.121189) * dihY y1 y2 y3 y4 y5 y6 + (-0.022099) * y1 + (-0.084657) * (y2 + y3 + y5 + y6) + 0.911046 :=
  rfl

/-- Component 228 gate (box 26; chain chain_idx228; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c228_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => c228_mfund (Function.update y i t) - K228 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B228 ≤ c228_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.121189) * dihY y1 y2 y3 y4 y5 y6 + (-0.022099) * y1 + (-0.084657) * (y2 + y3 + y5 + y6) + 0.911046 > 0 := by
  have hpos : (0 : ℝ) <
      B228 - ∑ i, R228 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R228 i = K228 i * (b26hi i - b26lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K228 0 = (0 : ℝ) := by rfl
    have t1 : K228 1 = (0 : ℝ) := by rfl
    have t2 : K228 2 = (0 : ℝ) := by rfl
    have t3 : K228 3 = (0 : ℝ) := by rfl
    have t4 : K228 4 = (0 : ℝ) := by rfl
    have t5 : K228 5 = (0 : ℝ) := by rfl
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
    have eb : B228 = ((4768951385158985762815491/3602879701896396800000000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K228 i := by
    intro i; fin_cases i <;> norm_num [K228]
  have hR0 : ∀ i, 0 ≤ R228 i := by
    intro i; fin_cases i <;> norm_num [R228, K228, b26lo, b26hi]
  have hchain := chain_idx228 c228_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c228_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-- Component 229 gate (box 26; chain chain_idx229; supply slots hsl/hcorner pending the S2-envelope and corner-bank lanes). -/

theorem c229_gate
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => c227_mfund (Function.update y i t) - K229 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B229 ≤ c227_mfund v)
    :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y2 → y2 ≤ (2 * hminus) → (2) ≤ y3 → y3 ≤ (2 * hminus) → (2) ≤ y4 → y4 ≤ (hminus + 1) → (2) ≤ y5 → y5 ≤ (2 * hminus) → (2) ≤ y6 → y6 ≤ (2 * hminus) → gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + (-0.121189) * dihY y1 y2 y3 y4 y5 y6 + (-0.016252) * y1 + 0.084657 * (y2 + y3 + y5 + y6) + (-0.45858) > 0 := by
  have hpos : (0 : ℝ) <
      B229 - ∑ i, R229 i := by
    rw [sumFin6d]
    have ev : ∀ i : Fin 6, R229 i = K229 i * (b26hi i - b26lo i) ^ 2 / 8 :=
      fun i => rfl
    have t0 : K229 0 = (0 : ℝ) := by rfl
    have t1 : K229 1 = (0 : ℝ) := by rfl
    have t2 : K229 2 = (0 : ℝ) := by rfl
    have t3 : K229 3 = (0 : ℝ) := by rfl
    have t4 : K229 4 = (0 : ℝ) := by rfl
    have t5 : K229 5 = (0 : ℝ) := by rfl
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
    have eb : B229 = ((9571791836237643399681/7205759403792793600000000) : ℝ) := by rfl
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
  have hK0 : ∀ i, 0 ≤ K229 i := by
    intro i; fin_cases i <;> norm_num [K229]
  have hR0 : ∀ i, 0 ≤ R229 i := by
    intro i; fin_cases i <;> norm_num [R229, K229, b26lo, b26hi]
  have hchain := chain_idx229 c227_mfund hsl hK0 hR0 hcorner ![y1, y2, y3, y4, y5, y6] hx
  rw [c227_mfund_at y1 y2 y3 y4 y5 y6] at hchain
  linarith [hchain, hpos]

/-! ### Axiom audit -/

#print axioms c180_gate

#print axioms c181_gate

#print axioms c182_gate

#print axioms c183_gate

#print axioms c184_gate

#print axioms c185_gate

#print axioms c186_gate

#print axioms c187_gate

#print axioms c188_gate

#print axioms c189_gate

#print axioms c190_gate

#print axioms c191_gate

#print axioms c192_gate

#print axioms c193_gate

#print axioms c194_gate

#print axioms c195_gate

#print axioms c196_gate

#print axioms c197_gate

#print axioms c198_gate

#print axioms c199_gate

#print axioms c200_gate

#print axioms c201_gate

#print axioms c202_gate

#print axioms c203_gate

#print axioms c204_gate

#print axioms c205_gate

#print axioms c206_gate

#print axioms c207_gate

#print axioms c208_gate

#print axioms c209_gate

#print axioms c210_gate

#print axioms c211_gate

#print axioms c212_gate

#print axioms c213_gate

#print axioms c214_gate

#print axioms c215_gate

#print axioms c216_gate

#print axioms c217_gate

#print axioms c218_gate

#print axioms c219_gate

#print axioms c220_gate

#print axioms c221_gate

#print axioms c222_gate

#print axioms c223_gate

#print axioms c224_gate

#print axioms c225_gate

#print axioms c226_gate

#print axioms c227_gate

#print axioms c228_gate

#print axioms c229_gate

end Kepler.Text
