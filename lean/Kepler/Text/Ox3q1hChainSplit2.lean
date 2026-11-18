/-
Ox3q1hChainSplitB: S4.5 split-grid chains for the KREBATE-INFEASIBLE conjuncts 71-216 (9 rows: 71, 76, 96, 111, 116, 121, 126, 161, 216).
Per row: msplit (SPLIT_PLAN route x m_min; 1 = unsplit), equal-piece
grid cands_split (image of gsplit over range m+1), split rebates RSN =
K*(W/m)^2/8 (exact fractions, bridged against KN*wsplit^2/8 by norm_num),
feasibility feas_split (0 < B - sum RSN; replaces the FALSE hfeas), and
the split chain chain_split_idxN (piecewise hslp slot + split-grid
hcorner slot; internal bridges hstep_split_m + final_bound; rebate
direction B - sum RSN <= f x, not flipped).
Consumption: idx41 <- b2K41/b2B41; idx46 <- K46/b2B46/R46(defs only);
idx76 <- b3K76/b3B76; all split rebates RSN are NEW (the landed unsplit
R41/R46/R76 cannot give feasibility for these rows).
All numerals verbatim from corner184/*.tsv via scripts/emit_split.py;
split feasibility pre-checked positive for every row (min 2.37e-4 @ 161).
No new sorry/axiom/native_decide.
-/
import Mathlib
import Kepler.Text.Ox3q1hChainSplitKit
import Kepler.Text.Ox3q1hChainBatch6
import Kepler.Text.Ox3q1hChainBatch1

open Set Filter Topology

namespace Kepler.Text

theorem sumFin6s (f : Fin 6 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_six]

/-- Component 71 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 5; 1 = unsplit coordinate). -/

noncomputable def msplit71 : Fin 6 → ℕ := ![1, 5, 5, 5, 5, 5]

/-- Component 71 equal-piece width per coordinate. -/

noncomputable def wsplit71 (i : Fin 6) : ℝ := (b13hi i - b13lo i) / (msplit71 i : ℝ)

/-- Component 71 split grid point `k` per coordinate. -/

noncomputable def gsplit71 (i : Fin 6) (k : ℕ) : ℝ := b13lo i + (k : ℝ) * wsplit71 i

/-- Component 71 split candidate grid (image of `gsplit71` over `range m+1`). -/

noncomputable def cands_split71 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit71 i + 1)).image (gsplit71 i)

theorem msplit71_pos (i : Fin 6) : 0 < msplit71 i := by
  fin_cases i <;> norm_num [msplit71]

theorem wsplit71_pos (i : Fin 6) : 0 ≤ wsplit71 i := by
  fin_cases i <;> norm_num [wsplit71, msplit71, b13lo, b13hi]

theorem wsplit71_hhi (i : Fin 6) : b13hi i = b13lo i + (msplit71 i : ℝ) * wsplit71 i := by
  fin_cases i <;> norm_num [wsplit71, msplit71, b13lo, b13hi]

theorem cands_split71_ne (i : Fin 6) : (cands_split71 i).Nonempty := by
  refine ⟨gsplit71 i 0, ?_⟩
  simp only [cands_split71, gsplit71, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit71_pos i], rfl⟩

theorem cands_split71_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split71 i) :
    c ∈ Set.Icc (b13lo i) (b13hi i) := by
  rw [cands_split71, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit71_pos i) (msplit71_pos i) (wsplit71_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 71 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS71 : Fin 6 → ℝ := ![0, (1576252997639280653/8589934592000000000000), (1576252997639280653/8589934592000000000000), (5044009592426499/274877906944000000000), (1576252997639280653/8589934592000000000000), (1576252997639280653/8589934592000000000000)]

/-- Component 71 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS71v_def (i : Fin 6) : RS71 i = K71 i * wsplit71 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS71, K71, wsplit71, msplit71, b13lo, b13hi]

/-- Component 71 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx71 : (0 : ℝ) < B71 - ∑ i, RS71 i := by
  rw [sumFin6s]
  have e0 : RS71 0 = (0 : ℝ) := by rfl
  have e1 : RS71 1 = ((1576252997639280653/8589934592000000000000) : ℝ) := by rfl
  have e2 : RS71 2 = ((1576252997639280653/8589934592000000000000) : ℝ) := by rfl
  have e3 : RS71 3 = ((5044009592426499/274877906944000000000) : ℝ) := by rfl
  have e4 : RS71 4 = ((1576252997639280653/8589934592000000000000) : ℝ) := by rfl
  have e5 : RS71 5 = ((1576252997639280653/8589934592000000000000) : ℝ) := by rfl
  have eb : B71 = (((2950192360984928262663659/1801439850948198400000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 71 split-grid chain: piecewise shifted concavity over
the `[1, 5, 5, 5, 5, 5]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx71 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit71 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b13lo j) (b13hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit71 i k) (gsplit71 i (k + 1)))
        (fun t => f (Function.update y i t) - K71 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split71 j) → B71 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b13lo j) (b13hi j)) :
    B71 - ∑ i, RS71 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K71 i := by
    intro i; fin_cases i <;> norm_num [K71]
  have hw : ∀ i, 0 ≤ wsplit71 i := by
    intro i; fin_cases i <;> norm_num [wsplit71, msplit71, b13lo, b13hi]
  have hhh : ∀ i, b13hi i = b13lo i + (msplit71 i : ℝ) * wsplit71 i := by
    intro i; fin_cases i <;> norm_num [wsplit71, msplit71, b13lo, b13hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit71 i → gsplit71 i k ∈ cands_split71 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split71 i →
      c ∈ Set.Icc (b13lo i) (b13hi i) := by
    intro i c hc
    rw [cands_split71, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit71_pos i) (wsplit71_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b13lo j) (b13hi j)) →
      ∃ c ∈ cands_split71 i, f (Function.update y i c) ≤
        f y + K71 i * wsplit71 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m_box ⟨0, by norm_num⟩ (msplit71 ⟨0, by norm_num⟩) (by norm_num [msplit71]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨0, by norm_num⟩ y' k hk hbox) (hmem ⟨0, by norm_num⟩) y hybox
        (by rw [← wsplit71_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m_box ⟨1, by norm_num⟩ (msplit71 ⟨1, by norm_num⟩) (by norm_num [msplit71]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨1, by norm_num⟩ y' k hk hbox) (hmem ⟨1, by norm_num⟩) y hybox
        (by rw [← wsplit71_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m_box ⟨2, by norm_num⟩ (msplit71 ⟨2, by norm_num⟩) (by norm_num [msplit71]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨2, by norm_num⟩ y' k hk hbox) (hmem ⟨2, by norm_num⟩) y hybox
        (by rw [← wsplit71_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m_box ⟨3, by norm_num⟩ (msplit71 ⟨3, by norm_num⟩) (by norm_num [msplit71]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨3, by norm_num⟩ y' k hk hbox) (hmem ⟨3, by norm_num⟩) y hybox
        (by rw [← wsplit71_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m_box ⟨4, by norm_num⟩ (msplit71 ⟨4, by norm_num⟩) (by norm_num [msplit71]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨4, by norm_num⟩ y' k hk hbox) (hmem ⟨4, by norm_num⟩) y hybox
        (by rw [← wsplit71_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m_box ⟨5, by norm_num⟩ (msplit71 ⟨5, by norm_num⟩) (by norm_num [msplit71]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨5, by norm_num⟩ y' k hk hbox) (hmem ⟨5, by norm_num⟩) y hybox
        (by rw [← wsplit71_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b13lo j) (b13hi j)) →
      ∃ c ∈ cands_split71 i, f (Function.update y i c) ≤ f y + RS71 i := by
    intro i y hybox
    rw [RS71v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS71 i := by
    intro i; fin_cases i <;> norm_num [RS71]
  exact final_bound cands_split71 cands_split71_ne hR0 hsub hstep hcorner x hx

/-- Component 76 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 5; 1 = unsplit coordinate). -/

noncomputable def msplit76 : Fin 6 → ℕ := ![1, 5, 5, 5, 5, 5]

/-- Component 76 equal-piece width per coordinate. -/

noncomputable def wsplit76 (i : Fin 6) : ℝ := (b14hi i - b14lo i) / (msplit76 i : ℝ)

/-- Component 76 split grid point `k` per coordinate. -/

noncomputable def gsplit76 (i : Fin 6) (k : ℕ) : ℝ := b14lo i + (k : ℝ) * wsplit76 i

/-- Component 76 split candidate grid (image of `gsplit76` over `range m+1`). -/

noncomputable def cands_split76 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit76 i + 1)).image (gsplit76 i)

theorem msplit76_pos (i : Fin 6) : 0 < msplit76 i := by
  fin_cases i <;> norm_num [msplit76]

theorem wsplit76_pos (i : Fin 6) : 0 ≤ wsplit76 i := by
  fin_cases i <;> norm_num [wsplit76, msplit76, b14lo, b14hi]

theorem wsplit76_hhi (i : Fin 6) : b14hi i = b14lo i + (msplit76 i : ℝ) * wsplit76 i := by
  fin_cases i <;> norm_num [wsplit76, msplit76, b14lo, b14hi]

theorem cands_split76_ne (i : Fin 6) : (cands_split76 i).Nonempty := by
  refine ⟨gsplit76 i 0, ?_⟩
  simp only [cands_split76, gsplit76, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit76_pos i], rfl⟩

theorem cands_split76_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split76 i) :
    c ∈ Set.Icc (b14lo i) (b14hi i) := by
  rw [cands_split76, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit76_pos i) (msplit76_pos i) (wsplit76_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 76 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS76 : Fin 6 → ℝ := ![0, (826888578664448801/8589934592000000000000), (826888578664448801/8589934592000000000000), (91396904058912609/5497558138880000000000), (826888578664448801/8589934592000000000000), (826888578664448801/8589934592000000000000)]

/-- Component 76 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS76v_def (i : Fin 6) : RS76 i = b3K76 i * wsplit76 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS76, b3K76, wsplit76, msplit76, b14lo, b14hi]

/-- Component 76 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx76 : (0 : ℝ) < b3B76 - ∑ i, RS76 i := by
  rw [sumFin6s]
  have e0 : RS76 0 = (0 : ℝ) := by rfl
  have e1 : RS76 1 = ((826888578664448801/8589934592000000000000) : ℝ) := by rfl
  have e2 : RS76 2 = ((826888578664448801/8589934592000000000000) : ℝ) := by rfl
  have e3 : RS76 3 = ((91396904058912609/5497558138880000000000) : ℝ) := by rfl
  have e4 : RS76 4 = ((826888578664448801/8589934592000000000000) : ℝ) := by rfl
  have e5 : RS76 5 = ((826888578664448801/8589934592000000000000) : ℝ) := by rfl
  have eb : b3B76 = (((902012941778731983592301/720575940379279360000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 76 split-grid chain: piecewise shifted concavity over
the `[1, 5, 5, 5, 5, 5]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx76 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit76 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b14lo j) (b14hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit76 i k) (gsplit76 i (k + 1)))
        (fun t => f (Function.update y i t) - b3K76 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split76 j) → b3B76 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b14lo j) (b14hi j)) :
    b3B76 - ∑ i, RS76 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ b3K76 i := by
    intro i; fin_cases i <;> norm_num [b3K76]
  have hw : ∀ i, 0 ≤ wsplit76 i := by
    intro i; fin_cases i <;> norm_num [wsplit76, msplit76, b14lo, b14hi]
  have hhh : ∀ i, b14hi i = b14lo i + (msplit76 i : ℝ) * wsplit76 i := by
    intro i; fin_cases i <;> norm_num [wsplit76, msplit76, b14lo, b14hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit76 i → gsplit76 i k ∈ cands_split76 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split76 i →
      c ∈ Set.Icc (b14lo i) (b14hi i) := by
    intro i c hc
    rw [cands_split76, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit76_pos i) (wsplit76_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b14lo j) (b14hi j)) →
      ∃ c ∈ cands_split76 i, f (Function.update y i c) ≤
        f y + b3K76 i * wsplit76 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m_box ⟨0, by norm_num⟩ (msplit76 ⟨0, by norm_num⟩) (by norm_num [msplit76]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨0, by norm_num⟩ y' k hk hbox) (hmem ⟨0, by norm_num⟩) y hybox
        (by rw [← wsplit76_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m_box ⟨1, by norm_num⟩ (msplit76 ⟨1, by norm_num⟩) (by norm_num [msplit76]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨1, by norm_num⟩ y' k hk hbox) (hmem ⟨1, by norm_num⟩) y hybox
        (by rw [← wsplit76_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m_box ⟨2, by norm_num⟩ (msplit76 ⟨2, by norm_num⟩) (by norm_num [msplit76]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨2, by norm_num⟩ y' k hk hbox) (hmem ⟨2, by norm_num⟩) y hybox
        (by rw [← wsplit76_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m_box ⟨3, by norm_num⟩ (msplit76 ⟨3, by norm_num⟩) (by norm_num [msplit76]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨3, by norm_num⟩ y' k hk hbox) (hmem ⟨3, by norm_num⟩) y hybox
        (by rw [← wsplit76_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m_box ⟨4, by norm_num⟩ (msplit76 ⟨4, by norm_num⟩) (by norm_num [msplit76]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨4, by norm_num⟩ y' k hk hbox) (hmem ⟨4, by norm_num⟩) y hybox
        (by rw [← wsplit76_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m_box ⟨5, by norm_num⟩ (msplit76 ⟨5, by norm_num⟩) (by norm_num [msplit76]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨5, by norm_num⟩ y' k hk hbox) (hmem ⟨5, by norm_num⟩) y hybox
        (by rw [← wsplit76_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b14lo j) (b14hi j)) →
      ∃ c ∈ cands_split76 i, f (Function.update y i c) ≤ f y + RS76 i := by
    intro i y hybox
    rw [RS76v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS76 i := by
    intro i; fin_cases i <;> norm_num [RS76]
  exact final_bound cands_split76 cands_split76_ne hR0 hsub hstep hcorner x hx

/-- Component 96 split factors (SPLIT_PLAN route `Y4PATCH:y4`, m_min = 2; 1 = unsplit coordinate). -/

noncomputable def msplit96 : Fin 6 → ℕ := ![1, 1, 1, 2, 1, 1]

/-- Component 96 equal-piece width per coordinate. -/

noncomputable def wsplit96 (i : Fin 6) : ℝ := (b20hi i - b20lo i) / (msplit96 i : ℝ)

/-- Component 96 split grid point `k` per coordinate. -/

noncomputable def gsplit96 (i : Fin 6) (k : ℕ) : ℝ := b20lo i + (k : ℝ) * wsplit96 i

/-- Component 96 split candidate grid (image of `gsplit96` over `range m+1`). -/

noncomputable def cands_split96 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit96 i + 1)).image (gsplit96 i)

theorem msplit96_pos (i : Fin 6) : 0 < msplit96 i := by
  fin_cases i <;> norm_num [msplit96]

theorem wsplit96_pos (i : Fin 6) : 0 ≤ wsplit96 i := by
  fin_cases i <;> norm_num [wsplit96, msplit96, b20lo, b20hi]

theorem wsplit96_hhi (i : Fin 6) : b20hi i = b20lo i + (msplit96 i : ℝ) * wsplit96 i := by
  fin_cases i <;> norm_num [wsplit96, msplit96, b20lo, b20hi]

theorem cands_split96_ne (i : Fin 6) : (cands_split96 i).Nonempty := by
  refine ⟨gsplit96 i 0, ?_⟩
  simp only [cands_split96, gsplit96, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit96_pos i], rfl⟩

theorem cands_split96_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split96 i) :
    c ∈ Set.Icc (b20lo i) (b20hi i) := by
  rw [cands_split96, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit96_pos i) (msplit96_pos i) (wsplit96_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 96 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS96 : Fin 6 → ℝ := ![0, 0, 0, (16116435281519163/219902325555200000000), 0, 0]

/-- Component 96 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS96v_def (i : Fin 6) : RS96 i = K96 i * wsplit96 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS96, K96, wsplit96, msplit96, b20lo, b20hi]

/-- Component 96 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx96 : (0 : ℝ) < B96 - ∑ i, RS96 i := by
  rw [sumFin6s]
  have e0 : RS96 0 = (0 : ℝ) := by rfl
  have e1 : RS96 1 = (0 : ℝ) := by rfl
  have e2 : RS96 2 = (0 : ℝ) := by rfl
  have e3 : RS96 3 = ((16116435281519163/219902325555200000000) : ℝ) := by rfl
  have e4 : RS96 4 = (0 : ℝ) := by rfl
  have e5 : RS96 5 = (0 : ℝ) := by rfl
  have eb : B96 = (((234908646216233356851499/720575940379279360000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 96 split-grid chain: piecewise shifted concavity over
the `[1, 1, 1, 2, 1, 1]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx96 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit96 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b20lo j) (b20hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit96 i k) (gsplit96 i (k + 1)))
        (fun t => f (Function.update y i t) - K96 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split96 j) → B96 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b20lo j) (b20hi j)) :
    B96 - ∑ i, RS96 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K96 i := by
    intro i; fin_cases i <;> norm_num [K96]
  have hw : ∀ i, 0 ≤ wsplit96 i := by
    intro i; fin_cases i <;> norm_num [wsplit96, msplit96, b20lo, b20hi]
  have hhh : ∀ i, b20hi i = b20lo i + (msplit96 i : ℝ) * wsplit96 i := by
    intro i; fin_cases i <;> norm_num [wsplit96, msplit96, b20lo, b20hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit96 i → gsplit96 i k ∈ cands_split96 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split96 i →
      c ∈ Set.Icc (b20lo i) (b20hi i) := by
    intro i c hc
    rw [cands_split96, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit96_pos i) (wsplit96_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b20lo j) (b20hi j)) →
      ∃ c ∈ cands_split96 i, f (Function.update y i c) ≤
        f y + K96 i * wsplit96 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m_box ⟨0, by norm_num⟩ (msplit96 ⟨0, by norm_num⟩) (by norm_num [msplit96]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨0, by norm_num⟩ y' k hk hbox) (hmem ⟨0, by norm_num⟩) y hybox
        (by rw [← wsplit96_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m_box ⟨1, by norm_num⟩ (msplit96 ⟨1, by norm_num⟩) (by norm_num [msplit96]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨1, by norm_num⟩ y' k hk hbox) (hmem ⟨1, by norm_num⟩) y hybox
        (by rw [← wsplit96_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m_box ⟨2, by norm_num⟩ (msplit96 ⟨2, by norm_num⟩) (by norm_num [msplit96]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨2, by norm_num⟩ y' k hk hbox) (hmem ⟨2, by norm_num⟩) y hybox
        (by rw [← wsplit96_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m_box ⟨3, by norm_num⟩ (msplit96 ⟨3, by norm_num⟩) (by norm_num [msplit96]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨3, by norm_num⟩ y' k hk hbox) (hmem ⟨3, by norm_num⟩) y hybox
        (by rw [← wsplit96_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m_box ⟨4, by norm_num⟩ (msplit96 ⟨4, by norm_num⟩) (by norm_num [msplit96]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨4, by norm_num⟩ y' k hk hbox) (hmem ⟨4, by norm_num⟩) y hybox
        (by rw [← wsplit96_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m_box ⟨5, by norm_num⟩ (msplit96 ⟨5, by norm_num⟩) (by norm_num [msplit96]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨5, by norm_num⟩ y' k hk hbox) (hmem ⟨5, by norm_num⟩) y hybox
        (by rw [← wsplit96_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b20lo j) (b20hi j)) →
      ∃ c ∈ cands_split96 i, f (Function.update y i c) ≤ f y + RS96 i := by
    intro i y hybox
    rw [RS96v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS96 i := by
    intro i; fin_cases i <;> norm_num [RS96]
  exact final_bound cands_split96 cands_split96_ne hR0 hsub hstep hcorner x hx

/-- Component 111 split factors (SPLIT_PLAN route `Y4PATCH:y4`, m_min = 2; 1 = unsplit coordinate). -/

noncomputable def msplit111 : Fin 6 → ℕ := ![1, 1, 1, 2, 1, 1]

/-- Component 111 equal-piece width per coordinate. -/

noncomputable def wsplit111 (i : Fin 6) : ℝ := (b25hi i - b25lo i) / (msplit111 i : ℝ)

/-- Component 111 split grid point `k` per coordinate. -/

noncomputable def gsplit111 (i : Fin 6) (k : ℕ) : ℝ := b25lo i + (k : ℝ) * wsplit111 i

/-- Component 111 split candidate grid (image of `gsplit111` over `range m+1`). -/

noncomputable def cands_split111 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit111 i + 1)).image (gsplit111 i)

theorem msplit111_pos (i : Fin 6) : 0 < msplit111 i := by
  fin_cases i <;> norm_num [msplit111]

theorem wsplit111_pos (i : Fin 6) : 0 ≤ wsplit111 i := by
  fin_cases i <;> norm_num [wsplit111, msplit111, b25lo, b25hi]

theorem wsplit111_hhi (i : Fin 6) : b25hi i = b25lo i + (msplit111 i : ℝ) * wsplit111 i := by
  fin_cases i <;> norm_num [wsplit111, msplit111, b25lo, b25hi]

theorem cands_split111_ne (i : Fin 6) : (cands_split111 i).Nonempty := by
  refine ⟨gsplit111 i 0, ?_⟩
  simp only [cands_split111, gsplit111, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit111_pos i], rfl⟩

theorem cands_split111_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split111 i) :
    c ∈ Set.Icc (b25lo i) (b25hi i) := by
  rw [cands_split111, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit111_pos i) (msplit111_pos i) (wsplit111_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 111 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS111 : Fin 6 → ℝ := ![0, 0, 0, (8203387535366193/27487790694400000000), 0, 0]

/-- Component 111 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS111v_def (i : Fin 6) : RS111 i = K111 i * wsplit111 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS111, K111, wsplit111, msplit111, b25lo, b25hi]

/-- Component 111 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx111 : (0 : ℝ) < B111 - ∑ i, RS111 i := by
  rw [sumFin6s]
  have e0 : RS111 0 = (0 : ℝ) := by rfl
  have e1 : RS111 1 = (0 : ℝ) := by rfl
  have e2 : RS111 2 = (0 : ℝ) := by rfl
  have e3 : RS111 3 = ((8203387535366193/27487790694400000000) : ℝ) := by rfl
  have e4 : RS111 4 = (0 : ℝ) := by rfl
  have e5 : RS111 5 = (0 : ℝ) := by rfl
  have eb : B111 = (((58003536949343176040209/28823037615171174400000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 111 split-grid chain: piecewise shifted concavity over
the `[1, 1, 1, 2, 1, 1]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx111 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit111 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b25lo j) (b25hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit111 i k) (gsplit111 i (k + 1)))
        (fun t => f (Function.update y i t) - K111 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split111 j) → B111 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b25lo j) (b25hi j)) :
    B111 - ∑ i, RS111 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K111 i := by
    intro i; fin_cases i <;> norm_num [K111]
  have hw : ∀ i, 0 ≤ wsplit111 i := by
    intro i; fin_cases i <;> norm_num [wsplit111, msplit111, b25lo, b25hi]
  have hhh : ∀ i, b25hi i = b25lo i + (msplit111 i : ℝ) * wsplit111 i := by
    intro i; fin_cases i <;> norm_num [wsplit111, msplit111, b25lo, b25hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit111 i → gsplit111 i k ∈ cands_split111 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split111 i →
      c ∈ Set.Icc (b25lo i) (b25hi i) := by
    intro i c hc
    rw [cands_split111, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit111_pos i) (wsplit111_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b25lo j) (b25hi j)) →
      ∃ c ∈ cands_split111 i, f (Function.update y i c) ≤
        f y + K111 i * wsplit111 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m_box ⟨0, by norm_num⟩ (msplit111 ⟨0, by norm_num⟩) (by norm_num [msplit111]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨0, by norm_num⟩ y' k hk hbox) (hmem ⟨0, by norm_num⟩) y hybox
        (by rw [← wsplit111_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m_box ⟨1, by norm_num⟩ (msplit111 ⟨1, by norm_num⟩) (by norm_num [msplit111]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨1, by norm_num⟩ y' k hk hbox) (hmem ⟨1, by norm_num⟩) y hybox
        (by rw [← wsplit111_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m_box ⟨2, by norm_num⟩ (msplit111 ⟨2, by norm_num⟩) (by norm_num [msplit111]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨2, by norm_num⟩ y' k hk hbox) (hmem ⟨2, by norm_num⟩) y hybox
        (by rw [← wsplit111_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m_box ⟨3, by norm_num⟩ (msplit111 ⟨3, by norm_num⟩) (by norm_num [msplit111]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨3, by norm_num⟩ y' k hk hbox) (hmem ⟨3, by norm_num⟩) y hybox
        (by rw [← wsplit111_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m_box ⟨4, by norm_num⟩ (msplit111 ⟨4, by norm_num⟩) (by norm_num [msplit111]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨4, by norm_num⟩ y' k hk hbox) (hmem ⟨4, by norm_num⟩) y hybox
        (by rw [← wsplit111_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m_box ⟨5, by norm_num⟩ (msplit111 ⟨5, by norm_num⟩) (by norm_num [msplit111]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨5, by norm_num⟩ y' k hk hbox) (hmem ⟨5, by norm_num⟩) y hybox
        (by rw [← wsplit111_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b25lo j) (b25hi j)) →
      ∃ c ∈ cands_split111 i, f (Function.update y i c) ≤ f y + RS111 i := by
    intro i y hybox
    rw [RS111v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS111 i := by
    intro i; fin_cases i <;> norm_num [RS111]
  exact final_bound cands_split111 cands_split111_ne hR0 hsub hstep hcorner x hx

/-- Component 116 split factors (SPLIT_PLAN route `Y4PATCH:y4`, m_min = 2; 1 = unsplit coordinate). -/

noncomputable def msplit116 : Fin 6 → ℕ := ![1, 1, 1, 2, 1, 1]

/-- Component 116 equal-piece width per coordinate. -/

noncomputable def wsplit116 (i : Fin 6) : ℝ := (b25hi i - b25lo i) / (msplit116 i : ℝ)

/-- Component 116 split grid point `k` per coordinate. -/

noncomputable def gsplit116 (i : Fin 6) (k : ℕ) : ℝ := b25lo i + (k : ℝ) * wsplit116 i

/-- Component 116 split candidate grid (image of `gsplit116` over `range m+1`). -/

noncomputable def cands_split116 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit116 i + 1)).image (gsplit116 i)

theorem msplit116_pos (i : Fin 6) : 0 < msplit116 i := by
  fin_cases i <;> norm_num [msplit116]

theorem wsplit116_pos (i : Fin 6) : 0 ≤ wsplit116 i := by
  fin_cases i <;> norm_num [wsplit116, msplit116, b25lo, b25hi]

theorem wsplit116_hhi (i : Fin 6) : b25hi i = b25lo i + (msplit116 i : ℝ) * wsplit116 i := by
  fin_cases i <;> norm_num [wsplit116, msplit116, b25lo, b25hi]

theorem cands_split116_ne (i : Fin 6) : (cands_split116 i).Nonempty := by
  refine ⟨gsplit116 i 0, ?_⟩
  simp only [cands_split116, gsplit116, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit116_pos i], rfl⟩

theorem cands_split116_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split116 i) :
    c ∈ Set.Icc (b25lo i) (b25hi i) := by
  rw [cands_split116, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit116_pos i) (msplit116_pos i) (wsplit116_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 116 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS116 : Fin 6 → ℝ := ![0, 0, 0, (8203387535366193/27487790694400000000), 0, 0]

/-- Component 116 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS116v_def (i : Fin 6) : RS116 i = K116 i * wsplit116 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS116, K116, wsplit116, msplit116, b25lo, b25hi]

/-- Component 116 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx116 : (0 : ℝ) < B116 - ∑ i, RS116 i := by
  rw [sumFin6s]
  have e0 : RS116 0 = (0 : ℝ) := by rfl
  have e1 : RS116 1 = (0 : ℝ) := by rfl
  have e2 : RS116 2 = (0 : ℝ) := by rfl
  have e3 : RS116 3 = ((8203387535366193/27487790694400000000) : ℝ) := by rfl
  have e4 : RS116 4 = (0 : ℝ) := by rfl
  have e5 : RS116 5 = (0 : ℝ) := by rfl
  have eb : B116 = (((58000078184829355499281/28823037615171174400000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 116 split-grid chain: piecewise shifted concavity over
the `[1, 1, 1, 2, 1, 1]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx116 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit116 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b25lo j) (b25hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit116 i k) (gsplit116 i (k + 1)))
        (fun t => f (Function.update y i t) - K116 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split116 j) → B116 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b25lo j) (b25hi j)) :
    B116 - ∑ i, RS116 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K116 i := by
    intro i; fin_cases i <;> norm_num [K116]
  have hw : ∀ i, 0 ≤ wsplit116 i := by
    intro i; fin_cases i <;> norm_num [wsplit116, msplit116, b25lo, b25hi]
  have hhh : ∀ i, b25hi i = b25lo i + (msplit116 i : ℝ) * wsplit116 i := by
    intro i; fin_cases i <;> norm_num [wsplit116, msplit116, b25lo, b25hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit116 i → gsplit116 i k ∈ cands_split116 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split116 i →
      c ∈ Set.Icc (b25lo i) (b25hi i) := by
    intro i c hc
    rw [cands_split116, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit116_pos i) (wsplit116_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b25lo j) (b25hi j)) →
      ∃ c ∈ cands_split116 i, f (Function.update y i c) ≤
        f y + K116 i * wsplit116 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m_box ⟨0, by norm_num⟩ (msplit116 ⟨0, by norm_num⟩) (by norm_num [msplit116]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨0, by norm_num⟩ y' k hk hbox) (hmem ⟨0, by norm_num⟩) y hybox
        (by rw [← wsplit116_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m_box ⟨1, by norm_num⟩ (msplit116 ⟨1, by norm_num⟩) (by norm_num [msplit116]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨1, by norm_num⟩ y' k hk hbox) (hmem ⟨1, by norm_num⟩) y hybox
        (by rw [← wsplit116_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m_box ⟨2, by norm_num⟩ (msplit116 ⟨2, by norm_num⟩) (by norm_num [msplit116]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨2, by norm_num⟩ y' k hk hbox) (hmem ⟨2, by norm_num⟩) y hybox
        (by rw [← wsplit116_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m_box ⟨3, by norm_num⟩ (msplit116 ⟨3, by norm_num⟩) (by norm_num [msplit116]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨3, by norm_num⟩ y' k hk hbox) (hmem ⟨3, by norm_num⟩) y hybox
        (by rw [← wsplit116_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m_box ⟨4, by norm_num⟩ (msplit116 ⟨4, by norm_num⟩) (by norm_num [msplit116]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨4, by norm_num⟩ y' k hk hbox) (hmem ⟨4, by norm_num⟩) y hybox
        (by rw [← wsplit116_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m_box ⟨5, by norm_num⟩ (msplit116 ⟨5, by norm_num⟩) (by norm_num [msplit116]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨5, by norm_num⟩ y' k hk hbox) (hmem ⟨5, by norm_num⟩) y hybox
        (by rw [← wsplit116_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b25lo j) (b25hi j)) →
      ∃ c ∈ cands_split116 i, f (Function.update y i c) ≤ f y + RS116 i := by
    intro i y hybox
    rw [RS116v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS116 i := by
    intro i; fin_cases i <;> norm_num [RS116]
  exact final_bound cands_split116 cands_split116_ne hR0 hsub hstep hcorner x hx

/-- Component 121 split factors (SPLIT_PLAN route `Y4PATCH:y4`, m_min = 2; 1 = unsplit coordinate). -/

noncomputable def msplit121 : Fin 6 → ℕ := ![1, 1, 1, 2, 1, 1]

/-- Component 121 equal-piece width per coordinate. -/

noncomputable def wsplit121 (i : Fin 6) : ℝ := (b25hi i - b25lo i) / (msplit121 i : ℝ)

/-- Component 121 split grid point `k` per coordinate. -/

noncomputable def gsplit121 (i : Fin 6) (k : ℕ) : ℝ := b25lo i + (k : ℝ) * wsplit121 i

/-- Component 121 split candidate grid (image of `gsplit121` over `range m+1`). -/

noncomputable def cands_split121 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit121 i + 1)).image (gsplit121 i)

theorem msplit121_pos (i : Fin 6) : 0 < msplit121 i := by
  fin_cases i <;> norm_num [msplit121]

theorem wsplit121_pos (i : Fin 6) : 0 ≤ wsplit121 i := by
  fin_cases i <;> norm_num [wsplit121, msplit121, b25lo, b25hi]

theorem wsplit121_hhi (i : Fin 6) : b25hi i = b25lo i + (msplit121 i : ℝ) * wsplit121 i := by
  fin_cases i <;> norm_num [wsplit121, msplit121, b25lo, b25hi]

theorem cands_split121_ne (i : Fin 6) : (cands_split121 i).Nonempty := by
  refine ⟨gsplit121 i 0, ?_⟩
  simp only [cands_split121, gsplit121, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit121_pos i], rfl⟩

theorem cands_split121_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split121 i) :
    c ∈ Set.Icc (b25lo i) (b25hi i) := by
  rw [cands_split121, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit121_pos i) (msplit121_pos i) (wsplit121_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 121 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS121 : Fin 6 → ℝ := ![0, 0, 0, (8203387535366193/27487790694400000000), 0, 0]

/-- Component 121 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS121v_def (i : Fin 6) : RS121 i = K121 i * wsplit121 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS121, K121, wsplit121, msplit121, b25lo, b25hi]

/-- Component 121 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx121 : (0 : ℝ) < B121 - ∑ i, RS121 i := by
  rw [sumFin6s]
  have e0 : RS121 0 = (0 : ℝ) := by rfl
  have e1 : RS121 1 = (0 : ℝ) := by rfl
  have e2 : RS121 2 = (0 : ℝ) := by rfl
  have e3 : RS121 3 = ((8203387535366193/27487790694400000000) : ℝ) := by rfl
  have e4 : RS121 4 = (0 : ℝ) := by rfl
  have e5 : RS121 5 = (0 : ℝ) := by rfl
  have eb : B121 = (((58028901222444526673681/28823037615171174400000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 121 split-grid chain: piecewise shifted concavity over
the `[1, 1, 1, 2, 1, 1]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx121 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit121 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b25lo j) (b25hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit121 i k) (gsplit121 i (k + 1)))
        (fun t => f (Function.update y i t) - K121 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split121 j) → B121 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b25lo j) (b25hi j)) :
    B121 - ∑ i, RS121 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K121 i := by
    intro i; fin_cases i <;> norm_num [K121]
  have hw : ∀ i, 0 ≤ wsplit121 i := by
    intro i; fin_cases i <;> norm_num [wsplit121, msplit121, b25lo, b25hi]
  have hhh : ∀ i, b25hi i = b25lo i + (msplit121 i : ℝ) * wsplit121 i := by
    intro i; fin_cases i <;> norm_num [wsplit121, msplit121, b25lo, b25hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit121 i → gsplit121 i k ∈ cands_split121 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split121 i →
      c ∈ Set.Icc (b25lo i) (b25hi i) := by
    intro i c hc
    rw [cands_split121, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit121_pos i) (wsplit121_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b25lo j) (b25hi j)) →
      ∃ c ∈ cands_split121 i, f (Function.update y i c) ≤
        f y + K121 i * wsplit121 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m_box ⟨0, by norm_num⟩ (msplit121 ⟨0, by norm_num⟩) (by norm_num [msplit121]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨0, by norm_num⟩ y' k hk hbox) (hmem ⟨0, by norm_num⟩) y hybox
        (by rw [← wsplit121_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m_box ⟨1, by norm_num⟩ (msplit121 ⟨1, by norm_num⟩) (by norm_num [msplit121]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨1, by norm_num⟩ y' k hk hbox) (hmem ⟨1, by norm_num⟩) y hybox
        (by rw [← wsplit121_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m_box ⟨2, by norm_num⟩ (msplit121 ⟨2, by norm_num⟩) (by norm_num [msplit121]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨2, by norm_num⟩ y' k hk hbox) (hmem ⟨2, by norm_num⟩) y hybox
        (by rw [← wsplit121_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m_box ⟨3, by norm_num⟩ (msplit121 ⟨3, by norm_num⟩) (by norm_num [msplit121]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨3, by norm_num⟩ y' k hk hbox) (hmem ⟨3, by norm_num⟩) y hybox
        (by rw [← wsplit121_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m_box ⟨4, by norm_num⟩ (msplit121 ⟨4, by norm_num⟩) (by norm_num [msplit121]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨4, by norm_num⟩ y' k hk hbox) (hmem ⟨4, by norm_num⟩) y hybox
        (by rw [← wsplit121_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m_box ⟨5, by norm_num⟩ (msplit121 ⟨5, by norm_num⟩) (by norm_num [msplit121]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨5, by norm_num⟩ y' k hk hbox) (hmem ⟨5, by norm_num⟩) y hybox
        (by rw [← wsplit121_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b25lo j) (b25hi j)) →
      ∃ c ∈ cands_split121 i, f (Function.update y i c) ≤ f y + RS121 i := by
    intro i y hybox
    rw [RS121v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS121 i := by
    intro i; fin_cases i <;> norm_num [RS121]
  exact final_bound cands_split121 cands_split121_ne hR0 hsub hstep hcorner x hx

/-- Component 126 split factors (SPLIT_PLAN route `Y4PATCH:y4`, m_min = 2; 1 = unsplit coordinate). -/

noncomputable def msplit126 : Fin 6 → ℕ := ![1, 1, 1, 2, 1, 1]

/-- Component 126 equal-piece width per coordinate. -/

noncomputable def wsplit126 (i : Fin 6) : ℝ := (b29hi i - b29lo i) / (msplit126 i : ℝ)

/-- Component 126 split grid point `k` per coordinate. -/

noncomputable def gsplit126 (i : Fin 6) (k : ℕ) : ℝ := b29lo i + (k : ℝ) * wsplit126 i

/-- Component 126 split candidate grid (image of `gsplit126` over `range m+1`). -/

noncomputable def cands_split126 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit126 i + 1)).image (gsplit126 i)

theorem msplit126_pos (i : Fin 6) : 0 < msplit126 i := by
  fin_cases i <;> norm_num [msplit126]

theorem wsplit126_pos (i : Fin 6) : 0 ≤ wsplit126 i := by
  fin_cases i <;> norm_num [wsplit126, msplit126, b29lo, b29hi]

theorem wsplit126_hhi (i : Fin 6) : b29hi i = b29lo i + (msplit126 i : ℝ) * wsplit126 i := by
  fin_cases i <;> norm_num [wsplit126, msplit126, b29lo, b29hi]

theorem cands_split126_ne (i : Fin 6) : (cands_split126 i).Nonempty := by
  refine ⟨gsplit126 i 0, ?_⟩
  simp only [cands_split126, gsplit126, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit126_pos i], rfl⟩

theorem cands_split126_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split126 i) :
    c ∈ Set.Icc (b29lo i) (b29hi i) := by
  rw [cands_split126, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit126_pos i) (msplit126_pos i) (wsplit126_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 126 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS126 : Fin 6 → ℝ := ![0, 0, 0, (15793453740868587/219902325555200000000), 0, 0]

/-- Component 126 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS126v_def (i : Fin 6) : RS126 i = K126 i * wsplit126 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS126, K126, wsplit126, msplit126, b29lo, b29hi]

/-- Component 126 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx126 : (0 : ℝ) < B126 - ∑ i, RS126 i := by
  rw [sumFin6s]
  have e0 : RS126 0 = (0 : ℝ) := by rfl
  have e1 : RS126 1 = (0 : ℝ) := by rfl
  have e2 : RS126 2 = (0 : ℝ) := by rfl
  have e3 : RS126 3 = ((15793453740868587/219902325555200000000) : ℝ) := by rfl
  have e4 : RS126 4 = (0 : ℝ) := by rfl
  have e5 : RS126 5 = (0 : ℝ) := by rfl
  have eb : B126 = (((5775702846294293121687/14411518807585587200000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 126 split-grid chain: piecewise shifted concavity over
the `[1, 1, 1, 2, 1, 1]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx126 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit126 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b29lo j) (b29hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit126 i k) (gsplit126 i (k + 1)))
        (fun t => f (Function.update y i t) - K126 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split126 j) → B126 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b29lo j) (b29hi j)) :
    B126 - ∑ i, RS126 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K126 i := by
    intro i; fin_cases i <;> norm_num [K126]
  have hw : ∀ i, 0 ≤ wsplit126 i := by
    intro i; fin_cases i <;> norm_num [wsplit126, msplit126, b29lo, b29hi]
  have hhh : ∀ i, b29hi i = b29lo i + (msplit126 i : ℝ) * wsplit126 i := by
    intro i; fin_cases i <;> norm_num [wsplit126, msplit126, b29lo, b29hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit126 i → gsplit126 i k ∈ cands_split126 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split126 i →
      c ∈ Set.Icc (b29lo i) (b29hi i) := by
    intro i c hc
    rw [cands_split126, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit126_pos i) (wsplit126_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b29lo j) (b29hi j)) →
      ∃ c ∈ cands_split126 i, f (Function.update y i c) ≤
        f y + K126 i * wsplit126 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m_box ⟨0, by norm_num⟩ (msplit126 ⟨0, by norm_num⟩) (by norm_num [msplit126]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨0, by norm_num⟩ y' k hk hbox) (hmem ⟨0, by norm_num⟩) y hybox
        (by rw [← wsplit126_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m_box ⟨1, by norm_num⟩ (msplit126 ⟨1, by norm_num⟩) (by norm_num [msplit126]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨1, by norm_num⟩ y' k hk hbox) (hmem ⟨1, by norm_num⟩) y hybox
        (by rw [← wsplit126_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m_box ⟨2, by norm_num⟩ (msplit126 ⟨2, by norm_num⟩) (by norm_num [msplit126]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨2, by norm_num⟩ y' k hk hbox) (hmem ⟨2, by norm_num⟩) y hybox
        (by rw [← wsplit126_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m_box ⟨3, by norm_num⟩ (msplit126 ⟨3, by norm_num⟩) (by norm_num [msplit126]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨3, by norm_num⟩ y' k hk hbox) (hmem ⟨3, by norm_num⟩) y hybox
        (by rw [← wsplit126_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m_box ⟨4, by norm_num⟩ (msplit126 ⟨4, by norm_num⟩) (by norm_num [msplit126]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨4, by norm_num⟩ y' k hk hbox) (hmem ⟨4, by norm_num⟩) y hybox
        (by rw [← wsplit126_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m_box ⟨5, by norm_num⟩ (msplit126 ⟨5, by norm_num⟩) (by norm_num [msplit126]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨5, by norm_num⟩ y' k hk hbox) (hmem ⟨5, by norm_num⟩) y hybox
        (by rw [← wsplit126_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b29lo j) (b29hi j)) →
      ∃ c ∈ cands_split126 i, f (Function.update y i c) ≤ f y + RS126 i := by
    intro i y hybox
    rw [RS126v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS126 i := by
    intro i; fin_cases i <;> norm_num [RS126]
  exact final_bound cands_split126 cands_split126_ne hR0 hsub hstep hcorner x hx

/-- Component 161 split factors (SPLIT_PLAN route `Y4PATCH:y4`, m_min = 2; 1 = unsplit coordinate). -/

noncomputable def msplit161 : Fin 6 → ℕ := ![1, 1, 1, 2, 1, 1]

/-- Component 161 equal-piece width per coordinate. -/

noncomputable def wsplit161 (i : Fin 6) : ℝ := (b40hi i - b40lo i) / (msplit161 i : ℝ)

/-- Component 161 split grid point `k` per coordinate. -/

noncomputable def gsplit161 (i : Fin 6) (k : ℕ) : ℝ := b40lo i + (k : ℝ) * wsplit161 i

/-- Component 161 split candidate grid (image of `gsplit161` over `range m+1`). -/

noncomputable def cands_split161 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit161 i + 1)).image (gsplit161 i)

theorem msplit161_pos (i : Fin 6) : 0 < msplit161 i := by
  fin_cases i <;> norm_num [msplit161]

theorem wsplit161_pos (i : Fin 6) : 0 ≤ wsplit161 i := by
  fin_cases i <;> norm_num [wsplit161, msplit161, b40lo, b40hi]

theorem wsplit161_hhi (i : Fin 6) : b40hi i = b40lo i + (msplit161 i : ℝ) * wsplit161 i := by
  fin_cases i <;> norm_num [wsplit161, msplit161, b40lo, b40hi]

theorem cands_split161_ne (i : Fin 6) : (cands_split161 i).Nonempty := by
  refine ⟨gsplit161 i 0, ?_⟩
  simp only [cands_split161, gsplit161, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit161_pos i], rfl⟩

theorem cands_split161_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split161 i) :
    c ∈ Set.Icc (b40lo i) (b40hi i) := by
  rw [cands_split161, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit161_pos i) (msplit161_pos i) (wsplit161_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 161 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS161 : Fin 6 → ℝ := ![0, 0, 0, (65235399265574379/879609302220800000000), 0, 0]

/-- Component 161 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS161v_def (i : Fin 6) : RS161 i = K161 i * wsplit161 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS161, K161, wsplit161, msplit161, b40lo, b40hi]

/-- Component 161 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx161 : (0 : ℝ) < B161 - ∑ i, RS161 i := by
  rw [sumFin6s]
  have e0 : RS161 0 = (0 : ℝ) := by rfl
  have e1 : RS161 1 = (0 : ℝ) := by rfl
  have e2 : RS161 2 = (0 : ℝ) := by rfl
  have e3 : RS161 3 = ((65235399265574379/879609302220800000000) : ℝ) := by rfl
  have e4 : RS161 4 = (0 : ℝ) := by rfl
  have e5 : RS161 5 = (0 : ℝ) := by rfl
  have eb : B161 = (((22395744817333092846543/72057594037927936000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 161 split-grid chain: piecewise shifted concavity over
the `[1, 1, 1, 2, 1, 1]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx161 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit161 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b40lo j) (b40hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit161 i k) (gsplit161 i (k + 1)))
        (fun t => f (Function.update y i t) - K161 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split161 j) → B161 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b40lo j) (b40hi j)) :
    B161 - ∑ i, RS161 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K161 i := by
    intro i; fin_cases i <;> norm_num [K161]
  have hw : ∀ i, 0 ≤ wsplit161 i := by
    intro i; fin_cases i <;> norm_num [wsplit161, msplit161, b40lo, b40hi]
  have hhh : ∀ i, b40hi i = b40lo i + (msplit161 i : ℝ) * wsplit161 i := by
    intro i; fin_cases i <;> norm_num [wsplit161, msplit161, b40lo, b40hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit161 i → gsplit161 i k ∈ cands_split161 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split161 i →
      c ∈ Set.Icc (b40lo i) (b40hi i) := by
    intro i c hc
    rw [cands_split161, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit161_pos i) (wsplit161_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b40lo j) (b40hi j)) →
      ∃ c ∈ cands_split161 i, f (Function.update y i c) ≤
        f y + K161 i * wsplit161 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m_box ⟨0, by norm_num⟩ (msplit161 ⟨0, by norm_num⟩) (by norm_num [msplit161]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨0, by norm_num⟩ y' k hk hbox) (hmem ⟨0, by norm_num⟩) y hybox
        (by rw [← wsplit161_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m_box ⟨1, by norm_num⟩ (msplit161 ⟨1, by norm_num⟩) (by norm_num [msplit161]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨1, by norm_num⟩ y' k hk hbox) (hmem ⟨1, by norm_num⟩) y hybox
        (by rw [← wsplit161_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m_box ⟨2, by norm_num⟩ (msplit161 ⟨2, by norm_num⟩) (by norm_num [msplit161]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨2, by norm_num⟩ y' k hk hbox) (hmem ⟨2, by norm_num⟩) y hybox
        (by rw [← wsplit161_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m_box ⟨3, by norm_num⟩ (msplit161 ⟨3, by norm_num⟩) (by norm_num [msplit161]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨3, by norm_num⟩ y' k hk hbox) (hmem ⟨3, by norm_num⟩) y hybox
        (by rw [← wsplit161_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m_box ⟨4, by norm_num⟩ (msplit161 ⟨4, by norm_num⟩) (by norm_num [msplit161]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨4, by norm_num⟩ y' k hk hbox) (hmem ⟨4, by norm_num⟩) y hybox
        (by rw [← wsplit161_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m_box ⟨5, by norm_num⟩ (msplit161 ⟨5, by norm_num⟩) (by norm_num [msplit161]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨5, by norm_num⟩ y' k hk hbox) (hmem ⟨5, by norm_num⟩) y hybox
        (by rw [← wsplit161_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b40lo j) (b40hi j)) →
      ∃ c ∈ cands_split161 i, f (Function.update y i c) ≤ f y + RS161 i := by
    intro i y hybox
    rw [RS161v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS161 i := by
    intro i; fin_cases i <;> norm_num [RS161]
  exact final_bound cands_split161 cands_split161_ne hR0 hsub hstep hcorner x hx

/-- Component 216 split factors (SPLIT_PLAN route `Y4PATCH:y4`, m_min = 2; 1 = unsplit coordinate). -/

noncomputable def msplit216 : Fin 6 → ℕ := ![1, 1, 1, 2, 1, 1]

/-- Component 216 equal-piece width per coordinate. -/

noncomputable def wsplit216 (i : Fin 6) : ℝ := (b45hi i - b45lo i) / (msplit216 i : ℝ)

/-- Component 216 split grid point `k` per coordinate. -/

noncomputable def gsplit216 (i : Fin 6) (k : ℕ) : ℝ := b45lo i + (k : ℝ) * wsplit216 i

/-- Component 216 split candidate grid (image of `gsplit216` over `range m+1`). -/

noncomputable def cands_split216 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit216 i + 1)).image (gsplit216 i)

theorem msplit216_pos (i : Fin 6) : 0 < msplit216 i := by
  fin_cases i <;> norm_num [msplit216]

theorem wsplit216_pos (i : Fin 6) : 0 ≤ wsplit216 i := by
  fin_cases i <;> norm_num [wsplit216, msplit216, b45lo, b45hi]

theorem wsplit216_hhi (i : Fin 6) : b45hi i = b45lo i + (msplit216 i : ℝ) * wsplit216 i := by
  fin_cases i <;> norm_num [wsplit216, msplit216, b45lo, b45hi]

theorem cands_split216_ne (i : Fin 6) : (cands_split216 i).Nonempty := by
  refine ⟨gsplit216 i 0, ?_⟩
  simp only [cands_split216, gsplit216, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit216_pos i], rfl⟩

theorem cands_split216_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split216 i) :
    c ∈ Set.Icc (b45lo i) (b45hi i) := by
  rw [cands_split216, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit216_pos i) (msplit216_pos i) (wsplit216_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 216 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS216 : Fin 6 → ℝ := ![0, 0, 0, (730845378983509/14073748835532800000), 0, 0]

/-- Component 216 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS216v_def (i : Fin 6) : RS216 i = K216 i * wsplit216 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS216, K216, wsplit216, msplit216, b45lo, b45hi]

/-- Component 216 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx216 : (0 : ℝ) < B216 - ∑ i, RS216 i := by
  rw [sumFin6s]
  have e0 : RS216 0 = (0 : ℝ) := by rfl
  have e1 : RS216 1 = (0 : ℝ) := by rfl
  have e2 : RS216 2 = (0 : ℝ) := by rfl
  have e3 : RS216 3 = ((730845378983509/14073748835532800000) : ℝ) := by rfl
  have e4 : RS216 4 = (0 : ℝ) := by rfl
  have e5 : RS216 5 = (0 : ℝ) := by rfl
  have eb : B216 = (((234908646216233356851499/720575940379279360000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 216 split-grid chain: piecewise shifted concavity over
the `[1, 1, 1, 2, 1, 1]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx216 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit216 i →
      (∀ j : Fin 6, y j ∈ Set.Icc (b45lo j) (b45hi j)) →
      ConcaveOn ℝ (Set.Icc (gsplit216 i k) (gsplit216 i (k + 1)))
        (fun t => f (Function.update y i t) - K216 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split216 j) → B216 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b45lo j) (b45hi j)) :
    B216 - ∑ i, RS216 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K216 i := by
    intro i; fin_cases i <;> norm_num [K216]
  have hw : ∀ i, 0 ≤ wsplit216 i := by
    intro i; fin_cases i <;> norm_num [wsplit216, msplit216, b45lo, b45hi]
  have hhh : ∀ i, b45hi i = b45lo i + (msplit216 i : ℝ) * wsplit216 i := by
    intro i; fin_cases i <;> norm_num [wsplit216, msplit216, b45lo, b45hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit216 i → gsplit216 i k ∈ cands_split216 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split216 i →
      c ∈ Set.Icc (b45lo i) (b45hi i) := by
    intro i c hc
    rw [cands_split216, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit216_pos i) (wsplit216_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b45lo j) (b45hi j)) →
      ∃ c ∈ cands_split216 i, f (Function.update y i c) ≤
        f y + K216 i * wsplit216 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m_box ⟨0, by norm_num⟩ (msplit216 ⟨0, by norm_num⟩) (by norm_num [msplit216]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨0, by norm_num⟩ y' k hk hbox) (hmem ⟨0, by norm_num⟩) y hybox
        (by rw [← wsplit216_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m_box ⟨1, by norm_num⟩ (msplit216 ⟨1, by norm_num⟩) (by norm_num [msplit216]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨1, by norm_num⟩ y' k hk hbox) (hmem ⟨1, by norm_num⟩) y hybox
        (by rw [← wsplit216_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m_box ⟨2, by norm_num⟩ (msplit216 ⟨2, by norm_num⟩) (by norm_num [msplit216]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨2, by norm_num⟩ y' k hk hbox) (hmem ⟨2, by norm_num⟩) y hybox
        (by rw [← wsplit216_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m_box ⟨3, by norm_num⟩ (msplit216 ⟨3, by norm_num⟩) (by norm_num [msplit216]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨3, by norm_num⟩ y' k hk hbox) (hmem ⟨3, by norm_num⟩) y hybox
        (by rw [← wsplit216_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m_box ⟨4, by norm_num⟩ (msplit216 ⟨4, by norm_num⟩) (by norm_num [msplit216]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨4, by norm_num⟩ y' k hk hbox) (hmem ⟨4, by norm_num⟩) y hybox
        (by rw [← wsplit216_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m_box ⟨5, by norm_num⟩ (msplit216 ⟨5, by norm_num⟩) (by norm_num [msplit216]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' hbox => hslp ⟨5, by norm_num⟩ y' k hk hbox) (hmem ⟨5, by norm_num⟩) y hybox
        (by rw [← wsplit216_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b45lo j) (b45hi j)) →
      ∃ c ∈ cands_split216 i, f (Function.update y i c) ≤ f y + RS216 i := by
    intro i y hybox
    rw [RS216v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS216 i := by
    intro i; fin_cases i <;> norm_num [RS216]
  exact final_bound cands_split216 cands_split216_ne hR0 hsub hstep hcorner x hx

/-! ### Axiom audit -/

#print axioms chain_split_idx71
#print axioms feas_split_idx71

#print axioms chain_split_idx76
#print axioms feas_split_idx76

#print axioms chain_split_idx96
#print axioms feas_split_idx96

#print axioms chain_split_idx111
#print axioms feas_split_idx111

#print axioms chain_split_idx116
#print axioms feas_split_idx116

#print axioms chain_split_idx121
#print axioms feas_split_idx121

#print axioms chain_split_idx126
#print axioms feas_split_idx126

#print axioms chain_split_idx161
#print axioms feas_split_idx161

#print axioms chain_split_idx216
#print axioms feas_split_idx216

end Kepler.Text
