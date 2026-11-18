/-
Ox3q1hChain3: the S3 first-batch chain-glue for three representative
ox3q1h GAMMA4 conjuncts (idx 41 / 46 / 76, boxes 5 / 5 / 14).

Chain (top to bottom):
  1. `exists_vertex_grid`       — grid-descent lemma (one-step ∃-rebate
     per coordinate, iterated over `Finset.univ`)
  2. `hstep_of_shifted_concave` — the one-step rebate supply from the
     shifted-concavity hypothesis
  3. `final_bound`              — corner-table bound minus `Σ K i`
  4. Three conjunct instances (idx 41 / 46 / 76) with the KENV dyadic K's
     and the CONJ_TABLE corner bounds. The rows carry the m-split
     obligation (SPLIT_PLAN m = 4 / 4 / 5) documented: the unsplit chains
     conclude `B - Σ K ≤ f x`; the positivity of the split-rebate bound
     is the grid-refinement batch's obligation.
-/
import Mathlib
import Kepler.Text.Ox3q1hConcaveKit
import Kepler.Text.Ox3q1hSliceRebate

open Set Filter Topology

namespace Kepler.Text

/-- Grid-descent: with a per-coordinate one-step rebate premise
(∃ grid candidate `c` with `f (update x i c) <= f x + K i`), every box
point is within `Σ K i` of some grid vertex. -/
theorem exists_vertex_grid {n : ℕ} {f : (Fin n → ℝ) → ℝ} {K : Fin n → ℝ}
    {lo hi : Fin n → ℝ}
    (cands : Fin n → Finset ℝ) (hne : ∀ i, (cands i).Nonempty)
    (hK : ∀ i, 0 ≤ K i)
    (hsub : ∀ (i : Fin n) (c : ℝ), c ∈ cands i → c ∈ Set.Icc (lo i) (hi i))
    (hstep : ∀ (i : Fin n) (x : Fin n → ℝ), (∀ j, x j ∈ Set.Icc (lo j) (hi j)) →
      ∃ c ∈ cands i, f (Function.update x i c) ≤ f x + K i)
    (x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (lo j) (hi j)) :
    ∃ v : Fin n → ℝ, (∀ j, v j ∈ cands j) ∧ f v ≤ f x + ∑ i, K i := by
  classical
  have key : ∀ s : Finset (Fin n), ∃ y : Fin n → ℝ,
      (∀ i ∈ s, y i ∈ cands i) ∧ (∀ j, j ∉ s → y j = x j) ∧
        f y ≤ f x + ∑ i ∈ s, K i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨x, fun j hj => absurd hj (by simp), fun j _ => rfl, by simp⟩
    | insert i s his ih =>
        obtain ⟨y, hyc, hyx, hsum⟩ := ih
        have hybox : ∀ j, y j ∈ Set.Icc (lo j) (hi j) := by
          intro j
          by_cases hj : j ∈ s
          · exact hsub j (y j) (hyc j hj)
          · rw [hyx j hj]; exact hx j
        obtain ⟨c, hc, hle⟩ := hstep i y hybox
        refine ⟨Function.update y i c, ?_, ?_, ?_⟩
        · intro j hj
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self j c y]
            exact hc
          · rw [Function.update_of_ne hji]
            exact hyc j ((Finset.mem_insert.mp hj).resolve_left hji)
        · intro j hj
          by_cases hji : j = i
          · subst hji
            exact absurd (Finset.mem_insert_self j s) hj
          · rw [Function.update_of_ne hji]
            exact hyx j (fun h => hj (Finset.mem_insert_of_mem h))
        · calc f (Function.update y i c) ≤ f y + K i := hle
            _ ≤ f x + ∑ j ∈ s, K j + K i := by linarith
            _ = f x + ∑ j ∈ insert i s, K j := by
                rw [Finset.sum_insert his]; ring
  obtain ⟨v, h1, -, h3⟩ := key Finset.univ
  exact ⟨v, fun j => h1 j (Finset.mem_univ j), h3⟩

/-- One-step rebate supply from the shifted-concavity hypothesis
(via the chord-rebate). -/
theorem hstep_of_shifted_concave {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {lo hi K : Fin n → ℝ} {i : Fin n} (hlohi : lo i ≤ hi i) (hK : 0 ≤ K i)
    (hsl : ∀ y : Fin n → ℝ, ConcaveOn ℝ (Set.Icc (lo i) (hi i))
      (fun t => f (Function.update y i t) - K i / 2 * t * t))
    {cands : Fin n → Finset ℝ}
    (hcands : ∀ j, cands j = insert (lo j) {hi j})
    (x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (lo j) (hi j)) :
    ∃ c ∈ cands i,
      f (Function.update x i c) ≤ f x + K i * (hi i - lo i) ^ 2 / 8 := by
  have hper : ∀ t ∈ Set.Icc (lo i) (hi i),
      f (Function.update x i t) ≥
        min (f (Function.update x i (lo i)))
          (f (Function.update x i (hi i))) - K i * (hi i - lo i) ^ 2 / 8 := by
    intro t ht
    exact rebate_of_concave_shifted hlohi hK (hsl x) (ht := ht)
  have hxmem : x i ∈ Set.Icc (lo i) (hi i) := hx i
  have hmin : min (f (Function.update x i (lo i))) (f (Function.update x i (hi i)))
      ≤ f x + K i * (hi i - lo i) ^ 2 / 8 := by
    have h := hper (x i) hxmem
    have hup : Function.update x i (x i) = x := by
      funext a
      by_cases h : a = i
      · subst h
        rw [Function.update_self]
      · rw [Function.update_of_ne h]
    rw [hup] at h
    linarith
  rcases min_le_iff.mp hmin with hlo | hhi
  · rw [hcands i]
    exact ⟨lo i, Finset.mem_insert_self _ _, hlo⟩
  · rw [hcands i]
    exact ⟨hi i, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hhi⟩

/-- One-step rebate supply from a BOXED shifted-concavity hypothesis
(SF 111 supply-slot form): the certificate is only demanded at points whose
every coordinate lies in the row box `[lo j, hi j]`; the step itself is
applied at the boxed point `x`. Proof identical to
`hstep_of_shifted_concave`, with `hsl` consumed at `x` via `hx`. -/
theorem hstep_of_shifted_concave_box {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {lo hi K : Fin n → ℝ} {i : Fin n} (hlohi : lo i ≤ hi i) (hK : 0 ≤ K i)
    (hsl : ∀ (i' : Fin n) (y : Fin n → ℝ),
      (∀ j, y j ∈ Set.Icc (lo j) (hi j)) →
      ConcaveOn ℝ (Set.Icc (lo i') (hi i'))
        (fun t => f (Function.update y i' t) - K i' / 2 * t * t))
    {cands : Fin n → Finset ℝ}
    (hcands : ∀ j, cands j = insert (lo j) {hi j})
    (x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (lo j) (hi j)) :
    ∃ c ∈ cands i,
      f (Function.update x i c) ≤ f x + K i * (hi i - lo i) ^ 2 / 8 := by
  have hper : ∀ t ∈ Set.Icc (lo i) (hi i),
      f (Function.update x i t) ≥
        min (f (Function.update x i (lo i)))
          (f (Function.update x i (hi i))) - K i * (hi i - lo i) ^ 2 / 8 := by
    intro t ht
    exact rebate_of_concave_shifted hlohi hK (hsl i x hx) (ht := ht)
  have hxmem : x i ∈ Set.Icc (lo i) (hi i) := hx i
  have hmin : min (f (Function.update x i (lo i))) (f (Function.update x i (hi i)))
      ≤ f x + K i * (hi i - lo i) ^ 2 / 8 := by
    have h := hper (x i) hxmem
    have hup : Function.update x i (x i) = x := by
      funext a
      by_cases h : a = i
      · subst h
        rw [Function.update_self]
      · rw [Function.update_of_ne h]
    rw [hup] at h
    linarith
  rcases min_le_iff.mp hmin with hlo | hhi
  · rw [hcands i]
    exact ⟨lo i, Finset.mem_insert_self _ _, hlo⟩
  · rw [hcands i]
    exact ⟨hi i, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hhi⟩

/-- Final assembly: the corner-table lower bound minus the total
grid rebate lower-bounds the margin at every box point. -/
theorem final_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ} {K : Fin n → ℝ}
    {lo hi : Fin n → ℝ} {B : ℝ}
    (cands : Fin n → Finset ℝ) (hne : ∀ i, (cands i).Nonempty)
    (hK : ∀ i, 0 ≤ K i)
    (hsub : ∀ (i : Fin n) (c : ℝ), c ∈ cands i → c ∈ Set.Icc (lo i) (hi i))
    (hstep : ∀ (i : Fin n) (x : Fin n → ℝ), (∀ j, x j ∈ Set.Icc (lo j) (hi j)) →
      ∃ c ∈ cands i, f (Function.update x i c) ≤ f x + K i)
    (hcorner : ∀ v : Fin n → ℝ, (∀ j, v j ∈ cands j) → B ≤ f v)
    (x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (lo j) (hi j)) :
    B - ∑ i, K i ≤ f x := by
  obtain ⟨v, hvc, hle⟩ := exists_vertex_grid cands hne hK hsub hstep x hx
  have hB := hcorner v hvc
  linarith

/-! ### Representative instances (idx 41 / 46 / 76) -/

/-- Box 5 lower corner (idx 41 / 46). -/
noncomputable def box5lo : Fin 6 → ℝ := fun _ => 63 / 25

/-- Box 5 upper corner (idx 41 / 46). -/
noncomputable def box5hi : Fin 6 → ℝ := fun _ => 6627 / 2500

/-- Box 14 lower corner (idx 76). -/
noncomputable def box14lo : Fin 6 → ℝ := fun _ => 26181 / 10000

/-- Box 14 upper corner (idx 76). -/
noncomputable def box14hi : Fin 6 → ℝ := fun _ => 6627 / 2500

/-- idx 41 / 46 per-coordinate curvature bounds (KENV). -/
noncomputable def K41 : Fin 6 → ℝ := fun _ => 949858192033 / 1099511627776

/-- idx 76 per-coordinate curvature bounds (KENV). -/
noncomputable def K76 : Fin 6 → ℝ := fun _ => 854743839921 / 1099511627776

/-- idx 41 corner-table bound (CONJ_TABLE). -/
noncomputable def B41 : ℝ := 10410645719309171611178167 / 3602879701896396800000000000

/-- idx 46 corner-table bound (CONJ_TABLE). -/
noncomputable def B46 : ℝ := 10407763415547654493738167 / 3602879701896396800000000000

/-- idx 76 corner-table bound (CONJ_TABLE). -/
noncomputable def B76 : ℝ := 902012941778731983592301 / 720575940379279360000000000

/-- idx 41 / 46 per-coordinate rebate amounts (KENV `R_i = K_i·W_i²/8`,
exact-fraction form of the emitted value). -/
noncomputable def R41 : Fin 6 → ℝ := fun i => K41 i * (box5hi i - box5lo i) ^ 2 / 8

/-- idx 76 per-coordinate rebate amounts (KENV `R_i = K_i·W_i²/8`). -/
noncomputable def R76 : Fin 6 → ℝ := fun i => K76 i * (box14hi i - box14lo i) ^ 2 / 8

/-- The unsplit two-corner grid of box 5. -/
noncomputable def cands5 : Fin 6 → Finset ℝ := fun i => insert (box5lo i) {box5hi i}

/-- The unsplit two-corner grid of box 14. -/
noncomputable def cands14 : Fin 6 → Finset ℝ := fun i => insert (box14lo i) {box14hi i}

theorem cands5_eq (i : Fin 6) : cands5 i = insert (box5lo i) {box5hi i} :=
  rfl

theorem cands14_eq (i : Fin 6) : cands14 i = insert (box14lo i) {box14hi i} :=
  rfl

theorem box5lo_le_box5hi (i : Fin 6) : box5lo i ≤ box5hi i := by
  fin_cases i
  all_goals norm_num [box5lo, box5hi]

theorem box14lo_le_box14hi (i : Fin 6) : box14lo i ≤ box14hi i := by
  fin_cases i
  all_goals norm_num [box14lo, box14hi]

theorem cands5_sub_box5 (i : Fin 6) (c : ℝ) (hc : c ∈ cands5 i) :
    c ∈ Set.Icc (box5lo i) (box5hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, box5lo_le_box5hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨box5lo_le_box5hi i, le_rfl⟩

theorem cands14_sub_box14 (i : Fin 6) (c : ℝ) (hc : c ∈ cands14 i) :
    c ∈ Set.Icc (box14lo i) (box14hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, box14lo_le_box14hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨box14lo_le_box14hi i, le_rfl⟩

theorem cands5_ne (i : Fin 6) : (cands5 i).Nonempty := ⟨box5lo i, by
  simp only [cands5]
  exact Finset.mem_insert_self _ _⟩

theorem cands14_ne (i : Fin 6) : (cands14 i).Nonempty := ⟨box14lo i, by
  simp only [cands14]
  exact Finset.mem_insert_self _ _⟩

/-- idx 41 chain: corner bound minus the unsplit grid rebate
lower-bounds the margin (box 5, KENV K's; the m = 4 split obligation
of SPLIT_PLAN shrinks `Σ R41 i` further). -/
theorem chain_idx41 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (box5lo i) (box5hi i))
        (fun t => f (Function.update y i t) - K41 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K41 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands5 j) → B41 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box5lo j) (box5hi j)) :
    B41 - ∑ i, R41 i ≤ f x :=
  final_bound (K := R41) cands5 cands5_ne
    (fun i => by
      rw [R41]
      exact div_nonneg (mul_nonneg (hK0 i) (sq_nonneg (box5hi i - box5lo i)))
        (by norm_num))
    cands5_sub_box5
    (fun i y hy => hstep_of_shifted_concave (box5lo_le_box5hi i) (hK0 i)
      (hsl i) cands5_eq y hy)
    hcorner x hx

/-- idx 46 chain (box 5, the same K's as idx 41; the m = 4 split
obligation of SPLIT_PLAN shrinks `Σ R41 i` further). -/
theorem chain_idx46 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (box5lo i) (box5hi i))
        (fun t => f (Function.update y i t) - K41 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K41 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands5 j) → B46 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box5lo j) (box5hi j)) :
    B46 - ∑ i, R41 i ≤ f x :=
  final_bound (K := R41) cands5 cands5_ne
    (fun i => by
      rw [R41]
      exact div_nonneg (mul_nonneg (hK0 i) (sq_nonneg (box5hi i - box5lo i)))
        (by norm_num))
    cands5_sub_box5
    (fun i y hy => hstep_of_shifted_concave (box5lo_le_box5hi i) (hK0 i)
      (hsl i) cands5_eq y hy)
    hcorner x hx

/-- idx 76 chain (box 14; the m = 5 split obligation of SPLIT_PLAN
shrinks `Σ R76 i` further). -/
theorem chain_idx76 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (box14lo i) (box14hi i))
        (fun t => f (Function.update y i t) - K76 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K76 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands14 j) → B76 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box14lo j) (box14hi j)) :
    B76 - ∑ i, R76 i ≤ f x :=
  final_bound (K := R76) cands14 cands14_ne
    (fun i => by
      rw [R76]
      exact div_nonneg (mul_nonneg (hK0 i) (sq_nonneg (box14hi i - box14lo i)))
        (by norm_num))
    cands14_sub_box14
    (fun i y hy => hstep_of_shifted_concave (box14lo_le_box14hi i) (hK0 i)
      (hsl i) cands14_eq y hy)
    hcorner x hx

/-! ### Axiom audit -/

#print axioms exists_vertex_grid
#print axioms hstep_of_shifted_concave
#print axioms hstep_of_shifted_concave_box
#print axioms final_bound
#print axioms chain_idx41
#print axioms chain_idx46
#print axioms chain_idx76

end Kepler.Text
