/-
Ox3q1hChainBatch1: S3 mass-production first batch (20 conjuncts, idx 1-19,
boxes 0/1/2/3). All 20 rows ALL-CONCAVE or single-axis REBATE per KENV;
the grid rebate `Σ K i = Σ R i` closes each chain at `B_i <= f x`.

Structure (five-part, per landed Chain3 062c1799):
  1. box definitions (exact fractions)
  2. K-functions (KENV dyadic) and corner bounds B_i (CONJ_TABLE)
  3. candidate grids (two-corner), sub/ne lemmas
  4. per-conjunct hsl+chain conditional theorems
All chains conclude `B_i - ∑ R_i ≤ f x` under hypotheses hsl/hK0/hcorner.
-/
import Mathlib
import Kepler.Text.Ox3q1hChain3

open Set Filter Topology

namespace Kepler.Text

/-- Box 0 lower corner. -/
noncomputable def box0lo : Fin 6 → ℝ := ![4927/2000, 2, 2, 63/25, 2, 2]

/-- Box 0 upper corner. -/
noncomputable def box0hi : Fin 6 → ℝ := ![63/25, 15397/6250, 15397/6250, 6627/2500, 15397/6250, 15397/6250]

theorem box0lo_le_box0hi (i : Fin 6) : box0lo i ≤ box0hi i := by
  fin_cases i
  all_goals norm_num [box0lo, box0hi]

/-- Box 1 lower corner. -/
noncomputable def box1lo : Fin 6 → ℝ := ![4927/2000, 2, 2, 2, 2, 2]

/-- Box 1 upper corner. -/
noncomputable def box1hi : Fin 6 → ℝ := ![63/25, 15397/6250, 15397/6250, 15397/6250, 15397/6250, 15397/6250]

theorem box1lo_le_box1hi (i : Fin 6) : box1lo i ≤ box1hi i := by
  fin_cases i
  all_goals norm_num [box1lo, box1hi]

/-- Box 2 lower corner. -/
noncomputable def box2lo : Fin 6 → ℝ := ![4927/2000, 2, 2, 8927/4000, 2, 2]

/-- Box 2 upper corner. -/
noncomputable def box2hi : Fin 6 → ℝ := ![63/25, 15397/6250, 15397/6250, 15397/6250, 15397/6250, 15397/6250]

theorem box2lo_le_box2hi (i : Fin 6) : box2lo i ≤ box2hi i := by
  fin_cases i
  all_goals norm_num [box2lo, box2hi]

/-- Box 3 lower corner. -/
noncomputable def box3lo : Fin 6 → ℝ := ![4927/2000, 2, 2, 2, 2, 2]

/-- Box 3 upper corner. -/
noncomputable def box3hi : Fin 6 → ℝ := ![63/25, 15397/6250, 15397/6250, 27897/12500, 15397/6250, 15397/6250]

theorem box3lo_le_box3hi (i : Fin 6) : box3lo i ≤ box3hi i := by
  fin_cases i
  all_goals norm_num [box3lo, box3hi]

/-- idx 1 per-coordinate curvature bounds (KENV). -/
noncomputable def K1 : Fin 6 → ℝ := ![0/1, 31204316903/1099511627776, 31204316903/1099511627776, 219710940055/274877906944, 31204316903/1099511627776, 31204316903/1099511627776]

/-- idx 1 corner-table bound (CONJ_TABLE). -/
noncomputable def B1 : ℝ := 69498556271971200695860763723/24078270227754988339200000000000

/-- idx 1 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R1 : Fin 6 → ℝ :=
  fun j => K1 j * (box0hi j - box0lo j) ^ 2 / 8

/-- idx 2 per-coordinate curvature bounds (KENV). -/
noncomputable def K2 : Fin 6 → ℝ := fun _ => 0

/-- idx 2 corner-table bound (CONJ_TABLE). -/
noncomputable def B2 : ℝ := 10405151898277464728772583/3602879701896396800000000000

/-- idx 2 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R2 : Fin 6 → ℝ :=
  fun j => K2 j * (box1hi j - box1lo j) ^ 2 / 8

/-- idx 3 per-coordinate curvature bounds (KENV). -/
noncomputable def K3 : Fin 6 → ℝ := fun _ => 0

/-- idx 3 corner-table bound (CONJ_TABLE). -/
noncomputable def B3 : ℝ := 416741359716083491744677/144115188075855872000000000

/-- idx 3 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R3 : Fin 6 → ℝ :=
  fun j => K3 j * (box1hi j - box1lo j) ^ 2 / 8

/-- idx 4 per-coordinate curvature bounds (KENV). -/
noncomputable def K4 : Fin 6 → ℝ := fun _ => 0

/-- idx 4 corner-table bound (CONJ_TABLE). -/
noncomputable def B4 : ℝ := 416434827219847400616519/144115188075855872000000000

/-- idx 4 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R4 : Fin 6 → ℝ :=
  fun j => K4 j * (box2hi j - box2lo j) ^ 2 / 8

/-- idx 6 per-coordinate curvature bounds (KENV). -/
noncomputable def K6 : Fin 6 → ℝ := ![0/1, 30961232843/1099511627776, 30961232843/1099511627776, 439180880907/549755813888, 30961232843/1099511627776, 30961232843/1099511627776]

/-- idx 6 corner-table bound (CONJ_TABLE). -/
noncomputable def B6 : ℝ := 69525408824385231231266891201/24078270227754988339200000000000

/-- idx 6 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R6 : Fin 6 → ℝ :=
  fun j => K6 j * (box0hi j - box0lo j) ^ 2 / 8

/-- idx 7 per-coordinate curvature bounds (KENV). -/
noncomputable def K7 : Fin 6 → ℝ := fun _ => 0

/-- idx 7 corner-table bound (CONJ_TABLE). -/
noncomputable def B7 : ℝ := 10402790728516950184241021/3602879701896396800000000000

/-- idx 7 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R7 : Fin 6 → ℝ :=
  fun j => K7 j * (box1hi j - box1lo j) ^ 2 / 8

/-- idx 8 per-coordinate curvature bounds (KENV). -/
noncomputable def K8 : Fin 6 → ℝ := fun _ => 0

/-- idx 8 corner-table bound (CONJ_TABLE). -/
noncomputable def B8 : ℝ := 416172938701507665516189/144115188075855872000000000

/-- idx 8 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R8 : Fin 6 → ℝ :=
  fun j => K8 j * (box2hi j - box2lo j) ^ 2 / 8

/-- idx 9 per-coordinate curvature bounds (KENV). -/
noncomputable def K9 : Fin 6 → ℝ := fun _ => 0

/-- idx 9 corner-table bound (CONJ_TABLE). -/
noncomputable def B9 : ℝ := 10402790728516950184241021/3602879701896396800000000000

/-- idx 9 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R9 : Fin 6 → ℝ :=
  fun j => K9 j * (box3hi j - box3lo j) ^ 2 / 8

/-- idx 11 per-coordinate curvature bounds (KENV). -/
noncomputable def K11 : Fin 6 → ℝ := ![0/1, 31204316903/1099511627776, 31204316903/1099511627776, 219710940055/274877906944, 31204316903/1099511627776, 31204316903/1099511627776]

/-- idx 11 corner-table bound (CONJ_TABLE). -/
noncomputable def B11 : ℝ := 69498556271971200695860763723/24078270227754988339200000000000

/-- idx 11 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R11 : Fin 6 → ℝ :=
  fun j => K11 j * (box0hi j - box0lo j) ^ 2 / 8

/-- idx 12 per-coordinate curvature bounds (KENV). -/
noncomputable def K12 : Fin 6 → ℝ := fun _ => 0

/-- idx 12 corner-table bound (CONJ_TABLE). -/
noncomputable def B12 : ℝ := 416434827219847400616519/144115188075855872000000000

/-- idx 12 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R12 : Fin 6 → ℝ :=
  fun j => K12 j * (box2hi j - box2lo j) ^ 2 / 8

/-- idx 13 per-coordinate curvature bounds (KENV). -/
noncomputable def K13 : Fin 6 → ℝ := fun _ => 0

/-- idx 13 corner-table bound (CONJ_TABLE). -/
noncomputable def B13 : ℝ := 416741359716083491744677/144115188075855872000000000

/-- idx 13 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R13 : Fin 6 → ℝ :=
  fun j => K13 j * (box3hi j - box3lo j) ^ 2 / 8

/-- idx 14 per-coordinate curvature bounds (KENV). -/
noncomputable def K14 : Fin 6 → ℝ := fun _ => 0

/-- idx 14 corner-table bound (CONJ_TABLE). -/
noncomputable def B14 : ℝ := 10405151898277464728772583/3602879701896396800000000000

/-- idx 14 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R14 : Fin 6 → ℝ :=
  fun j => K14 j * (box3hi j - box3lo j) ^ 2 / 8

/-- idx 16 per-coordinate curvature bounds (KENV). -/
noncomputable def K16 : Fin 6 → ℝ := ![0/1, 0/1, 0/1, 308077314483/549755813888, 0/1, 0/1]

/-- idx 16 corner-table bound (CONJ_TABLE). -/
noncomputable def B16 : ℝ := 823237231744048087528457779/1926261618220399067136000000000

/-- idx 16 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R16 : Fin 6 → ℝ :=
  fun j => K16 j * (box0hi j - box0lo j) ^ 2 / 8

/-- idx 17 per-coordinate curvature bounds (KENV). -/
noncomputable def K17 : Fin 6 → ℝ := fun _ => 0

/-- idx 17 corner-table bound (CONJ_TABLE). -/
noncomputable def B17 : ℝ := 47605760710723502227/112589990684262400000000

/-- idx 17 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R17 : Fin 6 → ℝ :=
  fun j => K17 j * (box3hi j - box3lo j) ^ 2 / 8

/-- idx 18 per-coordinate curvature bounds (KENV). -/
noncomputable def K18 : Fin 6 → ℝ := fun _ => 0

/-- idx 18 corner-table bound (CONJ_TABLE). -/
noncomputable def B18 : ℝ := 23997835552978532956863/56294995342131200000000000

/-- idx 18 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R18 : Fin 6 → ℝ :=
  fun j => K18 j * (box3hi j - box3lo j) ^ 2 / 8

/-- idx 19 per-coordinate curvature bounds (KENV). -/
noncomputable def K19 : Fin 6 → ℝ := fun _ => 0

/-- idx 19 corner-table bound (CONJ_TABLE). -/
noncomputable def B19 : ℝ := 47605760710723502227/112589990684262400000000

/-- idx 19 per-coordinate grid rebates R_j = K_j·W_j²/8 (KENV exact). -/
noncomputable def R19 : Fin 6 → ℝ :=
  fun j => K19 j * (box3hi j - box3lo j) ^ 2 / 8

/-- The unsplit two-corner grid of box 0. -/
noncomputable def candsbox0 : Fin 6 → Finset ℝ :=
  fun i => insert (box0lo i) {box0hi i}

theorem candsbox0_eq (i : Fin 6) : candsbox0 i = insert (box0lo i) {box0hi i} := rfl

theorem candsbox0_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsbox0 i) :
    c ∈ Set.Icc (box0lo i) (box0hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, box0lo_le_box0hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨box0lo_le_box0hi i, le_rfl⟩

theorem candsbox0_ne (i : Fin 6) : (candsbox0 i).Nonempty := ⟨box0lo i, by
  simp only [candsbox0]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 1. -/
noncomputable def candsbox1 : Fin 6 → Finset ℝ :=
  fun i => insert (box1lo i) {box1hi i}

theorem candsbox1_eq (i : Fin 6) : candsbox1 i = insert (box1lo i) {box1hi i} := rfl

theorem candsbox1_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsbox1 i) :
    c ∈ Set.Icc (box1lo i) (box1hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, box1lo_le_box1hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨box1lo_le_box1hi i, le_rfl⟩

theorem candsbox1_ne (i : Fin 6) : (candsbox1 i).Nonempty := ⟨box1lo i, by
  simp only [candsbox1]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 2. -/
noncomputable def candsbox2 : Fin 6 → Finset ℝ :=
  fun i => insert (box2lo i) {box2hi i}

theorem candsbox2_eq (i : Fin 6) : candsbox2 i = insert (box2lo i) {box2hi i} := rfl

theorem candsbox2_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsbox2 i) :
    c ∈ Set.Icc (box2lo i) (box2hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, box2lo_le_box2hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨box2lo_le_box2hi i, le_rfl⟩

theorem candsbox2_ne (i : Fin 6) : (candsbox2 i).Nonempty := ⟨box2lo i, by
  simp only [candsbox2]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 3. -/
noncomputable def candsbox3 : Fin 6 → Finset ℝ :=
  fun i => insert (box3lo i) {box3hi i}

theorem candsbox3_eq (i : Fin 6) : candsbox3 i = insert (box3lo i) {box3hi i} := rfl

theorem candsbox3_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsbox3 i) :
    c ∈ Set.Icc (box3lo i) (box3hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, box3lo_le_box3hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨box3lo_le_box3hi i, le_rfl⟩

theorem candsbox3_ne (i : Fin 6) : (candsbox3 i).Nonempty := ⟨box3lo i, by
  simp only [candsbox3]
  exact Finset.mem_insert_self _ _⟩

/-- idx 1 chain: corner bound minus the grid rebate lower-bounds the margin (box 0; REBATE coordinates per KENV). -/

theorem chain_idx1 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ConcaveOn ℝ (Set.Icc (box0lo i) (box0hi i))
        (fun t => f (Function.update y i t) - K1 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K1 i)
    (hR0 : ∀ i, 0 ≤ R1 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox0 j) → B1 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box0lo j) (box0hi j)) :
    B1 - ∑ i, R1 i ≤ f x :=
  final_bound candsbox0 candsbox0_ne hR0 candsbox0_sub
    (fun i y hy => hstep_of_shifted_concave_box (box0lo_le_box0hi i) (hK0 i)
      hsl candsbox0_eq y hy)
    hcorner x hx

/-- idx 2 chain: corner bound minus the grid rebate lower-bounds the margin (box 1; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx2 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box1lo j) (box1hi j)) →
      ConcaveOn ℝ (Set.Icc (box1lo i) (box1hi i))
        (fun t => f (Function.update y i t) - K2 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K2 i)
    (hR0 : ∀ i, 0 ≤ R2 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox1 j) → B2 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box1lo j) (box1hi j)) :
    B2 - ∑ i, R2 i ≤ f x :=
  final_bound candsbox1 candsbox1_ne hR0 candsbox1_sub
    (fun i y hy => hstep_of_shifted_concave_box (box1lo_le_box1hi i) (hK0 i)
      hsl candsbox1_eq y hy)
    hcorner x hx

/-- idx 3 chain: corner bound minus the grid rebate lower-bounds the margin (box 1; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx3 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box1lo j) (box1hi j)) →
      ConcaveOn ℝ (Set.Icc (box1lo i) (box1hi i))
        (fun t => f (Function.update y i t) - K3 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K3 i)
    (hR0 : ∀ i, 0 ≤ R3 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox1 j) → B3 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box1lo j) (box1hi j)) :
    B3 - ∑ i, R3 i ≤ f x :=
  final_bound candsbox1 candsbox1_ne hR0 candsbox1_sub
    (fun i y hy => hstep_of_shifted_concave_box (box1lo_le_box1hi i) (hK0 i)
      hsl candsbox1_eq y hy)
    hcorner x hx

/-- idx 4 chain: corner bound minus the grid rebate lower-bounds the margin (box 2; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx4 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box2lo j) (box2hi j)) →
      ConcaveOn ℝ (Set.Icc (box2lo i) (box2hi i))
        (fun t => f (Function.update y i t) - K4 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K4 i)
    (hR0 : ∀ i, 0 ≤ R4 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox2 j) → B4 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box2lo j) (box2hi j)) :
    B4 - ∑ i, R4 i ≤ f x :=
  final_bound candsbox2 candsbox2_ne hR0 candsbox2_sub
    (fun i y hy => hstep_of_shifted_concave_box (box2lo_le_box2hi i) (hK0 i)
      hsl candsbox2_eq y hy)
    hcorner x hx

/-- idx 6 chain: corner bound minus the grid rebate lower-bounds the margin (box 0; REBATE coordinates per KENV). -/

theorem chain_idx6 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ConcaveOn ℝ (Set.Icc (box0lo i) (box0hi i))
        (fun t => f (Function.update y i t) - K6 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K6 i)
    (hR0 : ∀ i, 0 ≤ R6 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox0 j) → B6 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box0lo j) (box0hi j)) :
    B6 - ∑ i, R6 i ≤ f x :=
  final_bound candsbox0 candsbox0_ne hR0 candsbox0_sub
    (fun i y hy => hstep_of_shifted_concave_box (box0lo_le_box0hi i) (hK0 i)
      hsl candsbox0_eq y hy)
    hcorner x hx

/-- idx 7 chain: corner bound minus the grid rebate lower-bounds the margin (box 1; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx7 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box1lo j) (box1hi j)) →
      ConcaveOn ℝ (Set.Icc (box1lo i) (box1hi i))
        (fun t => f (Function.update y i t) - K7 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K7 i)
    (hR0 : ∀ i, 0 ≤ R7 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox1 j) → B7 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box1lo j) (box1hi j)) :
    B7 - ∑ i, R7 i ≤ f x :=
  final_bound candsbox1 candsbox1_ne hR0 candsbox1_sub
    (fun i y hy => hstep_of_shifted_concave_box (box1lo_le_box1hi i) (hK0 i)
      hsl candsbox1_eq y hy)
    hcorner x hx

/-- idx 8 chain: corner bound minus the grid rebate lower-bounds the margin (box 2; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx8 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box2lo j) (box2hi j)) →
      ConcaveOn ℝ (Set.Icc (box2lo i) (box2hi i))
        (fun t => f (Function.update y i t) - K8 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K8 i)
    (hR0 : ∀ i, 0 ≤ R8 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox2 j) → B8 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box2lo j) (box2hi j)) :
    B8 - ∑ i, R8 i ≤ f x :=
  final_bound candsbox2 candsbox2_ne hR0 candsbox2_sub
    (fun i y hy => hstep_of_shifted_concave_box (box2lo_le_box2hi i) (hK0 i)
      hsl candsbox2_eq y hy)
    hcorner x hx

/-- idx 9 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx9 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => f (Function.update y i t) - K9 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K9 i)
    (hR0 : ∀ i, 0 ≤ R9 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B9 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box3lo j) (box3hi j)) :
    B9 - ∑ i, R9 i ≤ f x :=
  final_bound candsbox3 candsbox3_ne hR0 candsbox3_sub
    (fun i y hy => hstep_of_shifted_concave_box (box3lo_le_box3hi i) (hK0 i)
      hsl candsbox3_eq y hy)
    hcorner x hx

/-- idx 11 chain: corner bound minus the grid rebate lower-bounds the margin (box 0; REBATE coordinates per KENV). -/

theorem chain_idx11 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ConcaveOn ℝ (Set.Icc (box0lo i) (box0hi i))
        (fun t => f (Function.update y i t) - K11 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K11 i)
    (hR0 : ∀ i, 0 ≤ R11 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox0 j) → B11 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box0lo j) (box0hi j)) :
    B11 - ∑ i, R11 i ≤ f x :=
  final_bound candsbox0 candsbox0_ne hR0 candsbox0_sub
    (fun i y hy => hstep_of_shifted_concave_box (box0lo_le_box0hi i) (hK0 i)
      hsl candsbox0_eq y hy)
    hcorner x hx

/-- idx 12 chain: corner bound minus the grid rebate lower-bounds the margin (box 2; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx12 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box2lo j) (box2hi j)) →
      ConcaveOn ℝ (Set.Icc (box2lo i) (box2hi i))
        (fun t => f (Function.update y i t) - K12 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K12 i)
    (hR0 : ∀ i, 0 ≤ R12 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox2 j) → B12 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box2lo j) (box2hi j)) :
    B12 - ∑ i, R12 i ≤ f x :=
  final_bound candsbox2 candsbox2_ne hR0 candsbox2_sub
    (fun i y hy => hstep_of_shifted_concave_box (box2lo_le_box2hi i) (hK0 i)
      hsl candsbox2_eq y hy)
    hcorner x hx

/-- idx 13 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx13 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => f (Function.update y i t) - K13 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K13 i)
    (hR0 : ∀ i, 0 ≤ R13 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B13 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box3lo j) (box3hi j)) :
    B13 - ∑ i, R13 i ≤ f x :=
  final_bound candsbox3 candsbox3_ne hR0 candsbox3_sub
    (fun i y hy => hstep_of_shifted_concave_box (box3lo_le_box3hi i) (hK0 i)
      hsl candsbox3_eq y hy)
    hcorner x hx

/-- idx 14 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx14 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => f (Function.update y i t) - K14 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K14 i)
    (hR0 : ∀ i, 0 ≤ R14 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B14 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box3lo j) (box3hi j)) :
    B14 - ∑ i, R14 i ≤ f x :=
  final_bound candsbox3 candsbox3_ne hR0 candsbox3_sub
    (fun i y hy => hstep_of_shifted_concave_box (box3lo_le_box3hi i) (hK0 i)
      hsl candsbox3_eq y hy)
    hcorner x hx

/-- idx 16 chain: corner bound minus the grid rebate lower-bounds the margin (box 0; REBATE coordinates per KENV). -/

theorem chain_idx16 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ConcaveOn ℝ (Set.Icc (box0lo i) (box0hi i))
        (fun t => f (Function.update y i t) - K16 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K16 i)
    (hR0 : ∀ i, 0 ≤ R16 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox0 j) → B16 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box0lo j) (box0hi j)) :
    B16 - ∑ i, R16 i ≤ f x :=
  final_bound candsbox0 candsbox0_ne hR0 candsbox0_sub
    (fun i y hy => hstep_of_shifted_concave_box (box0lo_le_box0hi i) (hK0 i)
      hsl candsbox0_eq y hy)
    hcorner x hx

/-- idx 17 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx17 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => f (Function.update y i t) - K17 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K17 i)
    (hR0 : ∀ i, 0 ≤ R17 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B17 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box3lo j) (box3hi j)) :
    B17 - ∑ i, R17 i ≤ f x :=
  final_bound candsbox3 candsbox3_ne hR0 candsbox3_sub
    (fun i y hy => hstep_of_shifted_concave_box (box3lo_le_box3hi i) (hK0 i)
      hsl candsbox3_eq y hy)
    hcorner x hx

/-- idx 18 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx18 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => f (Function.update y i t) - K18 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K18 i)
    (hR0 : ∀ i, 0 ≤ R18 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B18 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box3lo j) (box3hi j)) :
    B18 - ∑ i, R18 i ≤ f x :=
  final_bound candsbox3 candsbox3_ne hR0 candsbox3_sub
    (fun i y hy => hstep_of_shifted_concave_box (box3lo_le_box3hi i) (hK0 i)
      hsl candsbox3_eq y hy)
    hcorner x hx

/-- idx 19 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx19 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (box3lo j) (box3hi j)) →
      ConcaveOn ℝ (Set.Icc (box3lo i) (box3hi i))
        (fun t => f (Function.update y i t) - K19 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K19 i)
    (hR0 : ∀ i, 0 ≤ R19 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsbox3 j) → B19 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box3lo j) (box3hi j)) :
    B19 - ∑ i, R19 i ≤ f x :=
  final_bound candsbox3 candsbox3_ne hR0 candsbox3_sub
    (fun i y hy => hstep_of_shifted_concave_box (box3lo_le_box3hi i) (hK0 i)
      hsl candsbox3_eq y hy)
    hcorner x hx

/-! ### Axiom audit -/


#print axioms chain_idx1

#print axioms chain_idx2

#print axioms chain_idx3

#print axioms chain_idx4

#print axioms chain_idx6

#print axioms chain_idx7

#print axioms chain_idx8

#print axioms chain_idx9

#print axioms chain_idx11

#print axioms chain_idx12

#print axioms chain_idx13

#print axioms chain_idx14

#print axioms chain_idx16

#print axioms chain_idx17

#print axioms chain_idx18

#print axioms chain_idx19

end Kepler.Text
