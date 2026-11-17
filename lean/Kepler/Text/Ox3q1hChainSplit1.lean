/-
Ox3q1hChainSplitA: S4.5 split-grid chains for the KREBATE-INFEASIBLE conjuncts 1-66 (10 rows: 1, 6, 11, 16, 41, 46, 51, 56, 61, 66).
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

/-- Component 1 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 2; 1 = unsplit coordinate). -/

noncomputable def msplit1 : Fin 6 → ℕ := ![1, 2, 2, 2, 2, 2]

/-- Component 1 equal-piece width per coordinate. -/

noncomputable def wsplit1 (i : Fin 6) : ℝ := (box0hi i - box0lo i) / (msplit1 i : ℝ)

/-- Component 1 split grid point `k` per coordinate. -/

noncomputable def gsplit1 (i : Fin 6) (k : ℕ) : ℝ := box0lo i + (k : ℝ) * wsplit1 i

/-- Component 1 split candidate grid (image of `gsplit1` over `range m+1`). -/

noncomputable def cands_split1 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit1 i + 1)).image (gsplit1 i)

theorem msplit1_pos (i : Fin 6) : 0 < msplit1 i := by
  fin_cases i <;> norm_num [msplit1]

theorem wsplit1_pos (i : Fin 6) : 0 ≤ wsplit1 i := by
  fin_cases i <;> norm_num [wsplit1, msplit1, box0lo, box0hi]

theorem wsplit1_hhi (i : Fin 6) : box0hi i = box0lo i + (msplit1 i : ℝ) * wsplit1 i := by
  fin_cases i <;> norm_num [wsplit1, msplit1, box0lo, box0hi]

theorem cands_split1_ne (i : Fin 6) : (cands_split1 i).Nonempty := by
  refine ⟨gsplit1 i 0, ?_⟩
  simp only [cands_split1, gsplit1, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit1_pos i], rfl⟩

theorem cands_split1_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split1 i) :
    c ∈ Set.Icc (box0lo i) (box0hi i) := by
  rw [cands_split1, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit1_pos i) (msplit1_pos i) (wsplit1_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 1 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS1 : Fin 6 → ℝ := ![0, (261885630878969927/1374389534720000000000), (261885630878969927/1374389534720000000000), (4698694221828219/10995116277760000000), (261885630878969927/1374389534720000000000), (261885630878969927/1374389534720000000000)]

/-- Component 1 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS1v_def (i : Fin 6) : RS1 i = K1 i * wsplit1 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS1, K1, wsplit1, msplit1, box0lo, box0hi]

/-- Component 1 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx1 : (0 : ℝ) < B1 - ∑ i, RS1 i := by
  rw [sumFin6s]
  have e0 : RS1 0 = (0 : ℝ) := by rfl
  have e1 : RS1 1 = ((261885630878969927/1374389534720000000000) : ℝ) := by rfl
  have e2 : RS1 2 = ((261885630878969927/1374389534720000000000) : ℝ) := by rfl
  have e3 : RS1 3 = ((4698694221828219/10995116277760000000) : ℝ) := by rfl
  have e4 : RS1 4 = ((261885630878969927/1374389534720000000000) : ℝ) := by rfl
  have e5 : RS1 5 = ((261885630878969927/1374389534720000000000) : ℝ) := by rfl
  have eb : B1 = (((69498556271971200695860763723/24078270227754988339200000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 1 split-grid chain: piecewise shifted concavity over
the `[1, 2, 2, 2, 2, 2]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx1 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit1 i →
      ConcaveOn ℝ (Set.Icc (gsplit1 i k) (gsplit1 i (k + 1)))
        (fun t => f (Function.update y i t) - K1 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split1 j) → B1 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box0lo j) (box0hi j)) :
    B1 - ∑ i, RS1 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K1 i := by
    intro i; fin_cases i <;> norm_num [K1]
  have hw : ∀ i, 0 ≤ wsplit1 i := by
    intro i; fin_cases i <;> norm_num [wsplit1, msplit1, box0lo, box0hi]
  have hhh : ∀ i, box0hi i = box0lo i + (msplit1 i : ℝ) * wsplit1 i := by
    intro i; fin_cases i <;> norm_num [wsplit1, msplit1, box0lo, box0hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit1 i → gsplit1 i k ∈ cands_split1 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split1 i →
      c ∈ Set.Icc (box0lo i) (box0hi i) := by
    intro i c hc
    rw [cands_split1, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit1_pos i) (wsplit1_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ∃ c ∈ cands_split1 i, f (Function.update y i c) ≤
        f y + K1 i * wsplit1 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m ⟨0, by norm_num⟩ (msplit1 ⟨0, by norm_num⟩) (by norm_num [msplit1]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' => hslp ⟨0, by norm_num⟩ y' k hk) (hmem ⟨0, by norm_num⟩) y
        (by rw [← wsplit1_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m ⟨1, by norm_num⟩ (msplit1 ⟨1, by norm_num⟩) (by norm_num [msplit1]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' => hslp ⟨1, by norm_num⟩ y' k hk) (hmem ⟨1, by norm_num⟩) y
        (by rw [← wsplit1_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m ⟨2, by norm_num⟩ (msplit1 ⟨2, by norm_num⟩) (by norm_num [msplit1]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' => hslp ⟨2, by norm_num⟩ y' k hk) (hmem ⟨2, by norm_num⟩) y
        (by rw [← wsplit1_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m ⟨3, by norm_num⟩ (msplit1 ⟨3, by norm_num⟩) (by norm_num [msplit1]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' => hslp ⟨3, by norm_num⟩ y' k hk) (hmem ⟨3, by norm_num⟩) y
        (by rw [← wsplit1_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m ⟨4, by norm_num⟩ (msplit1 ⟨4, by norm_num⟩) (by norm_num [msplit1]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' => hslp ⟨4, by norm_num⟩ y' k hk) (hmem ⟨4, by norm_num⟩) y
        (by rw [← wsplit1_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m ⟨5, by norm_num⟩ (msplit1 ⟨5, by norm_num⟩) (by norm_num [msplit1]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' => hslp ⟨5, by norm_num⟩ y' k hk) (hmem ⟨5, by norm_num⟩) y
        (by rw [← wsplit1_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ∃ c ∈ cands_split1 i, f (Function.update y i c) ≤ f y + RS1 i := by
    intro i y hybox
    rw [RS1v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS1 i := by
    intro i; fin_cases i <;> norm_num [RS1]
  exact final_bound cands_split1 cands_split1_ne hR0 hsub hstep hcorner x hx

/-- Component 6 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 2; 1 = unsplit coordinate). -/

noncomputable def msplit6 : Fin 6 → ℕ := ![1, 2, 2, 2, 2, 2]

/-- Component 6 equal-piece width per coordinate. -/

noncomputable def wsplit6 (i : Fin 6) : ℝ := (box0hi i - box0lo i) / (msplit6 i : ℝ)

/-- Component 6 split grid point `k` per coordinate. -/

noncomputable def gsplit6 (i : Fin 6) (k : ℕ) : ℝ := box0lo i + (k : ℝ) * wsplit6 i

/-- Component 6 split candidate grid (image of `gsplit6` over `range m+1`). -/

noncomputable def cands_split6 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit6 i + 1)).image (gsplit6 i)

theorem msplit6_pos (i : Fin 6) : 0 < msplit6 i := by
  fin_cases i <;> norm_num [msplit6]

theorem wsplit6_pos (i : Fin 6) : 0 ≤ wsplit6 i := by
  fin_cases i <;> norm_num [wsplit6, msplit6, box0lo, box0hi]

theorem wsplit6_hhi (i : Fin 6) : box0hi i = box0lo i + (msplit6 i : ℝ) * wsplit6 i := by
  fin_cases i <;> norm_num [wsplit6, msplit6, box0lo, box0hi]

theorem cands_split6_ne (i : Fin 6) : (cands_split6 i).Nonempty := by
  refine ⟨gsplit6 i 0, ?_⟩
  simp only [cands_split6, gsplit6, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit6_pos i], rfl⟩

theorem cands_split6_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split6 i) :
    c ∈ Set.Icc (box0lo i) (box0hi i) := by
  rw [cands_split6, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit6_pos i) (msplit6_pos i) (wsplit6_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 6 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS6 : Fin 6 → ℝ := ![0, (259845521409257387/1374389534720000000000), (259845521409257387/1374389534720000000000), (46961172414504603/109951162777600000000), (259845521409257387/1374389534720000000000), (259845521409257387/1374389534720000000000)]

/-- Component 6 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS6v_def (i : Fin 6) : RS6 i = K6 i * wsplit6 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS6, K6, wsplit6, msplit6, box0lo, box0hi]

/-- Component 6 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx6 : (0 : ℝ) < B6 - ∑ i, RS6 i := by
  rw [sumFin6s]
  have e0 : RS6 0 = (0 : ℝ) := by rfl
  have e1 : RS6 1 = ((259845521409257387/1374389534720000000000) : ℝ) := by rfl
  have e2 : RS6 2 = ((259845521409257387/1374389534720000000000) : ℝ) := by rfl
  have e3 : RS6 3 = ((46961172414504603/109951162777600000000) : ℝ) := by rfl
  have e4 : RS6 4 = ((259845521409257387/1374389534720000000000) : ℝ) := by rfl
  have e5 : RS6 5 = ((259845521409257387/1374389534720000000000) : ℝ) := by rfl
  have eb : B6 = (((69525408824385231231266891201/24078270227754988339200000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 6 split-grid chain: piecewise shifted concavity over
the `[1, 2, 2, 2, 2, 2]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx6 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit6 i →
      ConcaveOn ℝ (Set.Icc (gsplit6 i k) (gsplit6 i (k + 1)))
        (fun t => f (Function.update y i t) - K6 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split6 j) → B6 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box0lo j) (box0hi j)) :
    B6 - ∑ i, RS6 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K6 i := by
    intro i; fin_cases i <;> norm_num [K6]
  have hw : ∀ i, 0 ≤ wsplit6 i := by
    intro i; fin_cases i <;> norm_num [wsplit6, msplit6, box0lo, box0hi]
  have hhh : ∀ i, box0hi i = box0lo i + (msplit6 i : ℝ) * wsplit6 i := by
    intro i; fin_cases i <;> norm_num [wsplit6, msplit6, box0lo, box0hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit6 i → gsplit6 i k ∈ cands_split6 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split6 i →
      c ∈ Set.Icc (box0lo i) (box0hi i) := by
    intro i c hc
    rw [cands_split6, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit6_pos i) (wsplit6_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ∃ c ∈ cands_split6 i, f (Function.update y i c) ≤
        f y + K6 i * wsplit6 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m ⟨0, by norm_num⟩ (msplit6 ⟨0, by norm_num⟩) (by norm_num [msplit6]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' => hslp ⟨0, by norm_num⟩ y' k hk) (hmem ⟨0, by norm_num⟩) y
        (by rw [← wsplit6_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m ⟨1, by norm_num⟩ (msplit6 ⟨1, by norm_num⟩) (by norm_num [msplit6]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' => hslp ⟨1, by norm_num⟩ y' k hk) (hmem ⟨1, by norm_num⟩) y
        (by rw [← wsplit6_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m ⟨2, by norm_num⟩ (msplit6 ⟨2, by norm_num⟩) (by norm_num [msplit6]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' => hslp ⟨2, by norm_num⟩ y' k hk) (hmem ⟨2, by norm_num⟩) y
        (by rw [← wsplit6_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m ⟨3, by norm_num⟩ (msplit6 ⟨3, by norm_num⟩) (by norm_num [msplit6]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' => hslp ⟨3, by norm_num⟩ y' k hk) (hmem ⟨3, by norm_num⟩) y
        (by rw [← wsplit6_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m ⟨4, by norm_num⟩ (msplit6 ⟨4, by norm_num⟩) (by norm_num [msplit6]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' => hslp ⟨4, by norm_num⟩ y' k hk) (hmem ⟨4, by norm_num⟩) y
        (by rw [← wsplit6_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m ⟨5, by norm_num⟩ (msplit6 ⟨5, by norm_num⟩) (by norm_num [msplit6]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' => hslp ⟨5, by norm_num⟩ y' k hk) (hmem ⟨5, by norm_num⟩) y
        (by rw [← wsplit6_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ∃ c ∈ cands_split6 i, f (Function.update y i c) ≤ f y + RS6 i := by
    intro i y hybox
    rw [RS6v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS6 i := by
    intro i; fin_cases i <;> norm_num [RS6]
  exact final_bound cands_split6 cands_split6_ne hR0 hsub hstep hcorner x hx

/-- Component 11 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 2; 1 = unsplit coordinate). -/

noncomputable def msplit11 : Fin 6 → ℕ := ![1, 2, 2, 2, 2, 2]

/-- Component 11 equal-piece width per coordinate. -/

noncomputable def wsplit11 (i : Fin 6) : ℝ := (box0hi i - box0lo i) / (msplit11 i : ℝ)

/-- Component 11 split grid point `k` per coordinate. -/

noncomputable def gsplit11 (i : Fin 6) (k : ℕ) : ℝ := box0lo i + (k : ℝ) * wsplit11 i

/-- Component 11 split candidate grid (image of `gsplit11` over `range m+1`). -/

noncomputable def cands_split11 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit11 i + 1)).image (gsplit11 i)

theorem msplit11_pos (i : Fin 6) : 0 < msplit11 i := by
  fin_cases i <;> norm_num [msplit11]

theorem wsplit11_pos (i : Fin 6) : 0 ≤ wsplit11 i := by
  fin_cases i <;> norm_num [wsplit11, msplit11, box0lo, box0hi]

theorem wsplit11_hhi (i : Fin 6) : box0hi i = box0lo i + (msplit11 i : ℝ) * wsplit11 i := by
  fin_cases i <;> norm_num [wsplit11, msplit11, box0lo, box0hi]

theorem cands_split11_ne (i : Fin 6) : (cands_split11 i).Nonempty := by
  refine ⟨gsplit11 i 0, ?_⟩
  simp only [cands_split11, gsplit11, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit11_pos i], rfl⟩

theorem cands_split11_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split11 i) :
    c ∈ Set.Icc (box0lo i) (box0hi i) := by
  rw [cands_split11, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit11_pos i) (msplit11_pos i) (wsplit11_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 11 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS11 : Fin 6 → ℝ := ![0, (261885630878969927/1374389534720000000000), (261885630878969927/1374389534720000000000), (4698694221828219/10995116277760000000), (261885630878969927/1374389534720000000000), (261885630878969927/1374389534720000000000)]

/-- Component 11 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS11v_def (i : Fin 6) : RS11 i = K11 i * wsplit11 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS11, K11, wsplit11, msplit11, box0lo, box0hi]

/-- Component 11 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx11 : (0 : ℝ) < B11 - ∑ i, RS11 i := by
  rw [sumFin6s]
  have e0 : RS11 0 = (0 : ℝ) := by rfl
  have e1 : RS11 1 = ((261885630878969927/1374389534720000000000) : ℝ) := by rfl
  have e2 : RS11 2 = ((261885630878969927/1374389534720000000000) : ℝ) := by rfl
  have e3 : RS11 3 = ((4698694221828219/10995116277760000000) : ℝ) := by rfl
  have e4 : RS11 4 = ((261885630878969927/1374389534720000000000) : ℝ) := by rfl
  have e5 : RS11 5 = ((261885630878969927/1374389534720000000000) : ℝ) := by rfl
  have eb : B11 = (((69498556271971200695860763723/24078270227754988339200000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 11 split-grid chain: piecewise shifted concavity over
the `[1, 2, 2, 2, 2, 2]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx11 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit11 i →
      ConcaveOn ℝ (Set.Icc (gsplit11 i k) (gsplit11 i (k + 1)))
        (fun t => f (Function.update y i t) - K11 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split11 j) → B11 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box0lo j) (box0hi j)) :
    B11 - ∑ i, RS11 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K11 i := by
    intro i; fin_cases i <;> norm_num [K11]
  have hw : ∀ i, 0 ≤ wsplit11 i := by
    intro i; fin_cases i <;> norm_num [wsplit11, msplit11, box0lo, box0hi]
  have hhh : ∀ i, box0hi i = box0lo i + (msplit11 i : ℝ) * wsplit11 i := by
    intro i; fin_cases i <;> norm_num [wsplit11, msplit11, box0lo, box0hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit11 i → gsplit11 i k ∈ cands_split11 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split11 i →
      c ∈ Set.Icc (box0lo i) (box0hi i) := by
    intro i c hc
    rw [cands_split11, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit11_pos i) (wsplit11_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ∃ c ∈ cands_split11 i, f (Function.update y i c) ≤
        f y + K11 i * wsplit11 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m ⟨0, by norm_num⟩ (msplit11 ⟨0, by norm_num⟩) (by norm_num [msplit11]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' => hslp ⟨0, by norm_num⟩ y' k hk) (hmem ⟨0, by norm_num⟩) y
        (by rw [← wsplit11_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m ⟨1, by norm_num⟩ (msplit11 ⟨1, by norm_num⟩) (by norm_num [msplit11]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' => hslp ⟨1, by norm_num⟩ y' k hk) (hmem ⟨1, by norm_num⟩) y
        (by rw [← wsplit11_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m ⟨2, by norm_num⟩ (msplit11 ⟨2, by norm_num⟩) (by norm_num [msplit11]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' => hslp ⟨2, by norm_num⟩ y' k hk) (hmem ⟨2, by norm_num⟩) y
        (by rw [← wsplit11_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m ⟨3, by norm_num⟩ (msplit11 ⟨3, by norm_num⟩) (by norm_num [msplit11]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' => hslp ⟨3, by norm_num⟩ y' k hk) (hmem ⟨3, by norm_num⟩) y
        (by rw [← wsplit11_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m ⟨4, by norm_num⟩ (msplit11 ⟨4, by norm_num⟩) (by norm_num [msplit11]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' => hslp ⟨4, by norm_num⟩ y' k hk) (hmem ⟨4, by norm_num⟩) y
        (by rw [← wsplit11_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m ⟨5, by norm_num⟩ (msplit11 ⟨5, by norm_num⟩) (by norm_num [msplit11]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' => hslp ⟨5, by norm_num⟩ y' k hk) (hmem ⟨5, by norm_num⟩) y
        (by rw [← wsplit11_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ∃ c ∈ cands_split11 i, f (Function.update y i c) ≤ f y + RS11 i := by
    intro i y hybox
    rw [RS11v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS11 i := by
    intro i; fin_cases i <;> norm_num [RS11]
  exact final_bound cands_split11 cands_split11_ne hR0 hsub hstep hcorner x hx

/-- Component 16 split factors (SPLIT_PLAN route `Y4PATCH:y4`, m_min = 3; 1 = unsplit coordinate). -/

noncomputable def msplit16 : Fin 6 → ℕ := ![1, 1, 1, 3, 1, 1]

/-- Component 16 equal-piece width per coordinate. -/

noncomputable def wsplit16 (i : Fin 6) : ℝ := (box0hi i - box0lo i) / (msplit16 i : ℝ)

/-- Component 16 split grid point `k` per coordinate. -/

noncomputable def gsplit16 (i : Fin 6) (k : ℕ) : ℝ := box0lo i + (k : ℝ) * wsplit16 i

/-- Component 16 split candidate grid (image of `gsplit16` over `range m+1`). -/

noncomputable def cands_split16 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit16 i + 1)).image (gsplit16 i)

theorem msplit16_pos (i : Fin 6) : 0 < msplit16 i := by
  fin_cases i <;> norm_num [msplit16]

theorem wsplit16_pos (i : Fin 6) : 0 ≤ wsplit16 i := by
  fin_cases i <;> norm_num [wsplit16, msplit16, box0lo, box0hi]

theorem wsplit16_hhi (i : Fin 6) : box0hi i = box0lo i + (msplit16 i : ℝ) * wsplit16 i := by
  fin_cases i <;> norm_num [wsplit16, msplit16, box0lo, box0hi]

theorem cands_split16_ne (i : Fin 6) : (cands_split16 i).Nonempty := by
  refine ⟨gsplit16 i 0, ?_⟩
  simp only [cands_split16, gsplit16, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit16_pos i], rfl⟩

theorem cands_split16_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split16 i) :
    c ∈ Set.Icc (box0lo i) (box0hi i) := by
  rw [cands_split16, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit16_pos i) (msplit16_pos i) (wsplit16_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 16 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS16 : Fin 6 → ℝ := ![0, 0, 0, (3660266573372523/27487790694400000000), 0, 0]

/-- Component 16 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS16v_def (i : Fin 6) : RS16 i = K16 i * wsplit16 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS16, K16, wsplit16, msplit16, box0lo, box0hi]

/-- Component 16 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx16 : (0 : ℝ) < B16 - ∑ i, RS16 i := by
  rw [sumFin6s]
  have e0 : RS16 0 = (0 : ℝ) := by rfl
  have e1 : RS16 1 = (0 : ℝ) := by rfl
  have e2 : RS16 2 = (0 : ℝ) := by rfl
  have e3 : RS16 3 = ((3660266573372523/27487790694400000000) : ℝ) := by rfl
  have e4 : RS16 4 = (0 : ℝ) := by rfl
  have e5 : RS16 5 = (0 : ℝ) := by rfl
  have eb : B16 = (((823237231744048087528457779/1926261618220399067136000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 16 split-grid chain: piecewise shifted concavity over
the `[1, 1, 1, 3, 1, 1]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx16 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit16 i →
      ConcaveOn ℝ (Set.Icc (gsplit16 i k) (gsplit16 i (k + 1)))
        (fun t => f (Function.update y i t) - K16 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split16 j) → B16 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (box0lo j) (box0hi j)) :
    B16 - ∑ i, RS16 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K16 i := by
    intro i; fin_cases i <;> norm_num [K16]
  have hw : ∀ i, 0 ≤ wsplit16 i := by
    intro i; fin_cases i <;> norm_num [wsplit16, msplit16, box0lo, box0hi]
  have hhh : ∀ i, box0hi i = box0lo i + (msplit16 i : ℝ) * wsplit16 i := by
    intro i; fin_cases i <;> norm_num [wsplit16, msplit16, box0lo, box0hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit16 i → gsplit16 i k ∈ cands_split16 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split16 i →
      c ∈ Set.Icc (box0lo i) (box0hi i) := by
    intro i c hc
    rw [cands_split16, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit16_pos i) (wsplit16_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ∃ c ∈ cands_split16 i, f (Function.update y i c) ≤
        f y + K16 i * wsplit16 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m ⟨0, by norm_num⟩ (msplit16 ⟨0, by norm_num⟩) (by norm_num [msplit16]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' => hslp ⟨0, by norm_num⟩ y' k hk) (hmem ⟨0, by norm_num⟩) y
        (by rw [← wsplit16_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m ⟨1, by norm_num⟩ (msplit16 ⟨1, by norm_num⟩) (by norm_num [msplit16]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' => hslp ⟨1, by norm_num⟩ y' k hk) (hmem ⟨1, by norm_num⟩) y
        (by rw [← wsplit16_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m ⟨2, by norm_num⟩ (msplit16 ⟨2, by norm_num⟩) (by norm_num [msplit16]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' => hslp ⟨2, by norm_num⟩ y' k hk) (hmem ⟨2, by norm_num⟩) y
        (by rw [← wsplit16_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m ⟨3, by norm_num⟩ (msplit16 ⟨3, by norm_num⟩) (by norm_num [msplit16]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' => hslp ⟨3, by norm_num⟩ y' k hk) (hmem ⟨3, by norm_num⟩) y
        (by rw [← wsplit16_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m ⟨4, by norm_num⟩ (msplit16 ⟨4, by norm_num⟩) (by norm_num [msplit16]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' => hslp ⟨4, by norm_num⟩ y' k hk) (hmem ⟨4, by norm_num⟩) y
        (by rw [← wsplit16_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m ⟨5, by norm_num⟩ (msplit16 ⟨5, by norm_num⟩) (by norm_num [msplit16]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' => hslp ⟨5, by norm_num⟩ y' k hk) (hmem ⟨5, by norm_num⟩) y
        (by rw [← wsplit16_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (box0lo j) (box0hi j)) →
      ∃ c ∈ cands_split16 i, f (Function.update y i c) ≤ f y + RS16 i := by
    intro i y hybox
    rw [RS16v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS16 i := by
    intro i; fin_cases i <;> norm_num [RS16]
  exact final_bound cands_split16 cands_split16_ne hR0 hsub hstep hcorner x hx

/-- Component 41 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 4; 1 = unsplit coordinate). -/

noncomputable def msplit41 : Fin 6 → ℕ := ![1, 4, 4, 4, 4, 4]

/-- Component 41 equal-piece width per coordinate. -/

noncomputable def wsplit41 (i : Fin 6) : ℝ := (b5hi i - b5lo i) / (msplit41 i : ℝ)

/-- Component 41 split grid point `k` per coordinate. -/

noncomputable def gsplit41 (i : Fin 6) (k : ℕ) : ℝ := b5lo i + (k : ℝ) * wsplit41 i

/-- Component 41 split candidate grid (image of `gsplit41` over `range m+1`). -/

noncomputable def cands_split41 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit41 i + 1)).image (gsplit41 i)

theorem msplit41_pos (i : Fin 6) : 0 < msplit41 i := by
  fin_cases i <;> norm_num [msplit41]

theorem wsplit41_pos (i : Fin 6) : 0 ≤ wsplit41 i := by
  fin_cases i <;> norm_num [wsplit41, msplit41, b5lo, b5hi]

theorem wsplit41_hhi (i : Fin 6) : b5hi i = b5lo i + (msplit41 i : ℝ) * wsplit41 i := by
  fin_cases i <;> norm_num [wsplit41, msplit41, b5lo, b5hi]

theorem cands_split41_ne (i : Fin 6) : (cands_split41 i).Nonempty := by
  refine ⟨gsplit41 i 0, ?_⟩
  simp only [cands_split41, gsplit41, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit41_pos i], rfl⟩

theorem cands_split41_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split41 i) :
    c ∈ Set.Icc (b5lo i) (b5hi i) := by
  rw [cands_split41, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit41_pos i) (msplit41_pos i) (wsplit41_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 41 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS41 : Fin 6 → ℝ := ![0, (202400333824303147/687194767360000000000), (202400333824303147/687194767360000000000), (101567386615896657/879609302220800000000), (202400333824303147/687194767360000000000), (202400333824303147/687194767360000000000)]

/-- Component 41 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS41v_def (i : Fin 6) : RS41 i = b2K41 i * wsplit41 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS41, b2K41, wsplit41, msplit41, b5lo, b5hi]

/-- Component 41 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx41 : (0 : ℝ) < b2B41 - ∑ i, RS41 i := by
  rw [sumFin6s]
  have e0 : RS41 0 = (0 : ℝ) := by rfl
  have e1 : RS41 1 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have e2 : RS41 2 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have e3 : RS41 3 = ((101567386615896657/879609302220800000000) : ℝ) := by rfl
  have e4 : RS41 4 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have e5 : RS41 5 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have eb : b2B41 = (((10410645719309171611178167/3602879701896396800000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 41 split-grid chain: piecewise shifted concavity over
the `[1, 4, 4, 4, 4, 4]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx41 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit41 i →
      ConcaveOn ℝ (Set.Icc (gsplit41 i k) (gsplit41 i (k + 1)))
        (fun t => f (Function.update y i t) - b2K41 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split41 j) → b2B41 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b5lo j) (b5hi j)) :
    b2B41 - ∑ i, RS41 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ b2K41 i := by
    intro i; fin_cases i <;> norm_num [b2K41]
  have hw : ∀ i, 0 ≤ wsplit41 i := by
    intro i; fin_cases i <;> norm_num [wsplit41, msplit41, b5lo, b5hi]
  have hhh : ∀ i, b5hi i = b5lo i + (msplit41 i : ℝ) * wsplit41 i := by
    intro i; fin_cases i <;> norm_num [wsplit41, msplit41, b5lo, b5hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit41 i → gsplit41 i k ∈ cands_split41 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split41 i →
      c ∈ Set.Icc (b5lo i) (b5hi i) := by
    intro i c hc
    rw [cands_split41, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit41_pos i) (wsplit41_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b5lo j) (b5hi j)) →
      ∃ c ∈ cands_split41 i, f (Function.update y i c) ≤
        f y + b2K41 i * wsplit41 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m ⟨0, by norm_num⟩ (msplit41 ⟨0, by norm_num⟩) (by norm_num [msplit41]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' => hslp ⟨0, by norm_num⟩ y' k hk) (hmem ⟨0, by norm_num⟩) y
        (by rw [← wsplit41_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m ⟨1, by norm_num⟩ (msplit41 ⟨1, by norm_num⟩) (by norm_num [msplit41]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' => hslp ⟨1, by norm_num⟩ y' k hk) (hmem ⟨1, by norm_num⟩) y
        (by rw [← wsplit41_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m ⟨2, by norm_num⟩ (msplit41 ⟨2, by norm_num⟩) (by norm_num [msplit41]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' => hslp ⟨2, by norm_num⟩ y' k hk) (hmem ⟨2, by norm_num⟩) y
        (by rw [← wsplit41_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m ⟨3, by norm_num⟩ (msplit41 ⟨3, by norm_num⟩) (by norm_num [msplit41]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' => hslp ⟨3, by norm_num⟩ y' k hk) (hmem ⟨3, by norm_num⟩) y
        (by rw [← wsplit41_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m ⟨4, by norm_num⟩ (msplit41 ⟨4, by norm_num⟩) (by norm_num [msplit41]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' => hslp ⟨4, by norm_num⟩ y' k hk) (hmem ⟨4, by norm_num⟩) y
        (by rw [← wsplit41_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m ⟨5, by norm_num⟩ (msplit41 ⟨5, by norm_num⟩) (by norm_num [msplit41]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' => hslp ⟨5, by norm_num⟩ y' k hk) (hmem ⟨5, by norm_num⟩) y
        (by rw [← wsplit41_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b5lo j) (b5hi j)) →
      ∃ c ∈ cands_split41 i, f (Function.update y i c) ≤ f y + RS41 i := by
    intro i y hybox
    rw [RS41v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS41 i := by
    intro i; fin_cases i <;> norm_num [RS41]
  exact final_bound cands_split41 cands_split41_ne hR0 hsub hstep hcorner x hx

/-- Component 46 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 4; 1 = unsplit coordinate). -/

noncomputable def msplit46 : Fin 6 → ℕ := ![1, 4, 4, 4, 4, 4]

/-- Component 46 equal-piece width per coordinate. -/

noncomputable def wsplit46 (i : Fin 6) : ℝ := (b5hi i - b5lo i) / (msplit46 i : ℝ)

/-- Component 46 split grid point `k` per coordinate. -/

noncomputable def gsplit46 (i : Fin 6) (k : ℕ) : ℝ := b5lo i + (k : ℝ) * wsplit46 i

/-- Component 46 split candidate grid (image of `gsplit46` over `range m+1`). -/

noncomputable def cands_split46 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit46 i + 1)).image (gsplit46 i)

theorem msplit46_pos (i : Fin 6) : 0 < msplit46 i := by
  fin_cases i <;> norm_num [msplit46]

theorem wsplit46_pos (i : Fin 6) : 0 ≤ wsplit46 i := by
  fin_cases i <;> norm_num [wsplit46, msplit46, b5lo, b5hi]

theorem wsplit46_hhi (i : Fin 6) : b5hi i = b5lo i + (msplit46 i : ℝ) * wsplit46 i := by
  fin_cases i <;> norm_num [wsplit46, msplit46, b5lo, b5hi]

theorem cands_split46_ne (i : Fin 6) : (cands_split46 i).Nonempty := by
  refine ⟨gsplit46 i 0, ?_⟩
  simp only [cands_split46, gsplit46, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit46_pos i], rfl⟩

theorem cands_split46_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split46 i) :
    c ∈ Set.Icc (b5lo i) (b5hi i) := by
  rw [cands_split46, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit46_pos i) (msplit46_pos i) (wsplit46_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 46 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS46 : Fin 6 → ℝ := ![0, (202400333824303147/687194767360000000000), (202400333824303147/687194767360000000000), (101567386615896657/879609302220800000000), (202400333824303147/687194767360000000000), (202400333824303147/687194767360000000000)]

/-- Component 46 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS46v_def (i : Fin 6) : RS46 i = K46 i * wsplit46 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS46, K46, wsplit46, msplit46, b5lo, b5hi]

/-- Component 46 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx46 : (0 : ℝ) < b2B46 - ∑ i, RS46 i := by
  rw [sumFin6s]
  have e0 : RS46 0 = (0 : ℝ) := by rfl
  have e1 : RS46 1 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have e2 : RS46 2 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have e3 : RS46 3 = ((101567386615896657/879609302220800000000) : ℝ) := by rfl
  have e4 : RS46 4 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have e5 : RS46 5 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have eb : b2B46 = (((10407763415547654493738167/3602879701896396800000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 46 split-grid chain: piecewise shifted concavity over
the `[1, 4, 4, 4, 4, 4]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx46 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit46 i →
      ConcaveOn ℝ (Set.Icc (gsplit46 i k) (gsplit46 i (k + 1)))
        (fun t => f (Function.update y i t) - K46 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split46 j) → b2B46 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b5lo j) (b5hi j)) :
    b2B46 - ∑ i, RS46 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K46 i := by
    intro i; fin_cases i <;> norm_num [K46]
  have hw : ∀ i, 0 ≤ wsplit46 i := by
    intro i; fin_cases i <;> norm_num [wsplit46, msplit46, b5lo, b5hi]
  have hhh : ∀ i, b5hi i = b5lo i + (msplit46 i : ℝ) * wsplit46 i := by
    intro i; fin_cases i <;> norm_num [wsplit46, msplit46, b5lo, b5hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit46 i → gsplit46 i k ∈ cands_split46 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split46 i →
      c ∈ Set.Icc (b5lo i) (b5hi i) := by
    intro i c hc
    rw [cands_split46, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit46_pos i) (wsplit46_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b5lo j) (b5hi j)) →
      ∃ c ∈ cands_split46 i, f (Function.update y i c) ≤
        f y + K46 i * wsplit46 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m ⟨0, by norm_num⟩ (msplit46 ⟨0, by norm_num⟩) (by norm_num [msplit46]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' => hslp ⟨0, by norm_num⟩ y' k hk) (hmem ⟨0, by norm_num⟩) y
        (by rw [← wsplit46_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m ⟨1, by norm_num⟩ (msplit46 ⟨1, by norm_num⟩) (by norm_num [msplit46]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' => hslp ⟨1, by norm_num⟩ y' k hk) (hmem ⟨1, by norm_num⟩) y
        (by rw [← wsplit46_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m ⟨2, by norm_num⟩ (msplit46 ⟨2, by norm_num⟩) (by norm_num [msplit46]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' => hslp ⟨2, by norm_num⟩ y' k hk) (hmem ⟨2, by norm_num⟩) y
        (by rw [← wsplit46_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m ⟨3, by norm_num⟩ (msplit46 ⟨3, by norm_num⟩) (by norm_num [msplit46]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' => hslp ⟨3, by norm_num⟩ y' k hk) (hmem ⟨3, by norm_num⟩) y
        (by rw [← wsplit46_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m ⟨4, by norm_num⟩ (msplit46 ⟨4, by norm_num⟩) (by norm_num [msplit46]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' => hslp ⟨4, by norm_num⟩ y' k hk) (hmem ⟨4, by norm_num⟩) y
        (by rw [← wsplit46_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m ⟨5, by norm_num⟩ (msplit46 ⟨5, by norm_num⟩) (by norm_num [msplit46]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' => hslp ⟨5, by norm_num⟩ y' k hk) (hmem ⟨5, by norm_num⟩) y
        (by rw [← wsplit46_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b5lo j) (b5hi j)) →
      ∃ c ∈ cands_split46 i, f (Function.update y i c) ≤ f y + RS46 i := by
    intro i y hybox
    rw [RS46v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS46 i := by
    intro i; fin_cases i <;> norm_num [RS46]
  exact final_bound cands_split46 cands_split46_ne hR0 hsub hstep hcorner x hx

/-- Component 51 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 4; 1 = unsplit coordinate). -/

noncomputable def msplit51 : Fin 6 → ℕ := ![1, 4, 4, 4, 4, 4]

/-- Component 51 equal-piece width per coordinate. -/

noncomputable def wsplit51 (i : Fin 6) : ℝ := (b5hi i - b5lo i) / (msplit51 i : ℝ)

/-- Component 51 split grid point `k` per coordinate. -/

noncomputable def gsplit51 (i : Fin 6) (k : ℕ) : ℝ := b5lo i + (k : ℝ) * wsplit51 i

/-- Component 51 split candidate grid (image of `gsplit51` over `range m+1`). -/

noncomputable def cands_split51 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit51 i + 1)).image (gsplit51 i)

theorem msplit51_pos (i : Fin 6) : 0 < msplit51 i := by
  fin_cases i <;> norm_num [msplit51]

theorem wsplit51_pos (i : Fin 6) : 0 ≤ wsplit51 i := by
  fin_cases i <;> norm_num [wsplit51, msplit51, b5lo, b5hi]

theorem wsplit51_hhi (i : Fin 6) : b5hi i = b5lo i + (msplit51 i : ℝ) * wsplit51 i := by
  fin_cases i <;> norm_num [wsplit51, msplit51, b5lo, b5hi]

theorem cands_split51_ne (i : Fin 6) : (cands_split51 i).Nonempty := by
  refine ⟨gsplit51 i 0, ?_⟩
  simp only [cands_split51, gsplit51, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit51_pos i], rfl⟩

theorem cands_split51_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split51 i) :
    c ∈ Set.Icc (b5lo i) (b5hi i) := by
  rw [cands_split51, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit51_pos i) (msplit51_pos i) (wsplit51_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 51 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS51 : Fin 6 → ℝ := ![0, (202400333824303147/687194767360000000000), (202400333824303147/687194767360000000000), (101567386615896657/879609302220800000000), (202400333824303147/687194767360000000000), (202400333824303147/687194767360000000000)]

/-- Component 51 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS51v_def (i : Fin 6) : RS51 i = K51 i * wsplit51 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS51, K51, wsplit51, msplit51, b5lo, b5hi]

/-- Component 51 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx51 : (0 : ℝ) < B51 - ∑ i, RS51 i := by
  rw [sumFin6s]
  have e0 : RS51 0 = (0 : ℝ) := by rfl
  have e1 : RS51 1 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have e2 : RS51 2 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have e3 : RS51 3 = ((101567386615896657/879609302220800000000) : ℝ) := by rfl
  have e4 : RS51 4 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have e5 : RS51 5 = ((202400333824303147/687194767360000000000) : ℝ) := by rfl
  have eb : B51 = (((10410645719309171611178167/3602879701896396800000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 51 split-grid chain: piecewise shifted concavity over
the `[1, 4, 4, 4, 4, 4]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx51 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit51 i →
      ConcaveOn ℝ (Set.Icc (gsplit51 i k) (gsplit51 i (k + 1)))
        (fun t => f (Function.update y i t) - K51 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split51 j) → B51 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b5lo j) (b5hi j)) :
    B51 - ∑ i, RS51 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K51 i := by
    intro i; fin_cases i <;> norm_num [K51]
  have hw : ∀ i, 0 ≤ wsplit51 i := by
    intro i; fin_cases i <;> norm_num [wsplit51, msplit51, b5lo, b5hi]
  have hhh : ∀ i, b5hi i = b5lo i + (msplit51 i : ℝ) * wsplit51 i := by
    intro i; fin_cases i <;> norm_num [wsplit51, msplit51, b5lo, b5hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit51 i → gsplit51 i k ∈ cands_split51 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split51 i →
      c ∈ Set.Icc (b5lo i) (b5hi i) := by
    intro i c hc
    rw [cands_split51, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit51_pos i) (wsplit51_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b5lo j) (b5hi j)) →
      ∃ c ∈ cands_split51 i, f (Function.update y i c) ≤
        f y + K51 i * wsplit51 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m ⟨0, by norm_num⟩ (msplit51 ⟨0, by norm_num⟩) (by norm_num [msplit51]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' => hslp ⟨0, by norm_num⟩ y' k hk) (hmem ⟨0, by norm_num⟩) y
        (by rw [← wsplit51_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m ⟨1, by norm_num⟩ (msplit51 ⟨1, by norm_num⟩) (by norm_num [msplit51]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' => hslp ⟨1, by norm_num⟩ y' k hk) (hmem ⟨1, by norm_num⟩) y
        (by rw [← wsplit51_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m ⟨2, by norm_num⟩ (msplit51 ⟨2, by norm_num⟩) (by norm_num [msplit51]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' => hslp ⟨2, by norm_num⟩ y' k hk) (hmem ⟨2, by norm_num⟩) y
        (by rw [← wsplit51_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m ⟨3, by norm_num⟩ (msplit51 ⟨3, by norm_num⟩) (by norm_num [msplit51]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' => hslp ⟨3, by norm_num⟩ y' k hk) (hmem ⟨3, by norm_num⟩) y
        (by rw [← wsplit51_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m ⟨4, by norm_num⟩ (msplit51 ⟨4, by norm_num⟩) (by norm_num [msplit51]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' => hslp ⟨4, by norm_num⟩ y' k hk) (hmem ⟨4, by norm_num⟩) y
        (by rw [← wsplit51_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m ⟨5, by norm_num⟩ (msplit51 ⟨5, by norm_num⟩) (by norm_num [msplit51]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' => hslp ⟨5, by norm_num⟩ y' k hk) (hmem ⟨5, by norm_num⟩) y
        (by rw [← wsplit51_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b5lo j) (b5hi j)) →
      ∃ c ∈ cands_split51 i, f (Function.update y i c) ≤ f y + RS51 i := by
    intro i y hybox
    rw [RS51v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS51 i := by
    intro i; fin_cases i <;> norm_num [RS51]
  exact final_bound cands_split51 cands_split51_ne hR0 hsub hstep hcorner x hx

/-- Component 56 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 3; 1 = unsplit coordinate). -/

noncomputable def msplit56 : Fin 6 → ℕ := ![1, 3, 3, 3, 3, 3]

/-- Component 56 equal-piece width per coordinate. -/

noncomputable def wsplit56 (i : Fin 6) : ℝ := (b9hi i - b9lo i) / (msplit56 i : ℝ)

/-- Component 56 split grid point `k` per coordinate. -/

noncomputable def gsplit56 (i : Fin 6) (k : ℕ) : ℝ := b9lo i + (k : ℝ) * wsplit56 i

/-- Component 56 split candidate grid (image of `gsplit56` over `range m+1`). -/

noncomputable def cands_split56 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit56 i + 1)).image (gsplit56 i)

theorem msplit56_pos (i : Fin 6) : 0 < msplit56 i := by
  fin_cases i <;> norm_num [msplit56]

theorem wsplit56_pos (i : Fin 6) : 0 ≤ wsplit56 i := by
  fin_cases i <;> norm_num [wsplit56, msplit56, b9lo, b9hi]

theorem wsplit56_hhi (i : Fin 6) : b9hi i = b9lo i + (msplit56 i : ℝ) * wsplit56 i := by
  fin_cases i <;> norm_num [wsplit56, msplit56, b9lo, b9hi]

theorem cands_split56_ne (i : Fin 6) : (cands_split56 i).Nonempty := by
  refine ⟨gsplit56 i 0, ?_⟩
  simp only [cands_split56, gsplit56, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit56_pos i], rfl⟩

theorem cands_split56_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split56 i) :
    c ∈ Set.Icc (b9lo i) (b9hi i) := by
  rw [cands_split56, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit56_pos i) (msplit56_pos i) (wsplit56_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 56 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS56 : Fin 6 → ℝ := ![0, (43312014222397/83886080000000000), (43312014222397/83886080000000000), (2807476955819287/13743895347200000000), (43312014222397/83886080000000000), (43312014222397/83886080000000000)]

/-- Component 56 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS56v_def (i : Fin 6) : RS56 i = K56 i * wsplit56 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS56, K56, wsplit56, msplit56, b9lo, b9hi]

/-- Component 56 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx56 : (0 : ℝ) < B56 - ∑ i, RS56 i := by
  rw [sumFin6s]
  have e0 : RS56 0 = (0 : ℝ) := by rfl
  have e1 : RS56 1 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have e2 : RS56 2 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have e3 : RS56 3 = ((2807476955819287/13743895347200000000) : ℝ) := by rfl
  have e4 : RS56 4 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have e5 : RS56 5 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have eb : B56 = (((9662398472678640545419551/1801439850948198400000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 56 split-grid chain: piecewise shifted concavity over
the `[1, 3, 3, 3, 3, 3]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx56 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit56 i →
      ConcaveOn ℝ (Set.Icc (gsplit56 i k) (gsplit56 i (k + 1)))
        (fun t => f (Function.update y i t) - K56 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split56 j) → B56 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b9lo j) (b9hi j)) :
    B56 - ∑ i, RS56 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K56 i := by
    intro i; fin_cases i <;> norm_num [K56]
  have hw : ∀ i, 0 ≤ wsplit56 i := by
    intro i; fin_cases i <;> norm_num [wsplit56, msplit56, b9lo, b9hi]
  have hhh : ∀ i, b9hi i = b9lo i + (msplit56 i : ℝ) * wsplit56 i := by
    intro i; fin_cases i <;> norm_num [wsplit56, msplit56, b9lo, b9hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit56 i → gsplit56 i k ∈ cands_split56 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split56 i →
      c ∈ Set.Icc (b9lo i) (b9hi i) := by
    intro i c hc
    rw [cands_split56, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit56_pos i) (wsplit56_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b9lo j) (b9hi j)) →
      ∃ c ∈ cands_split56 i, f (Function.update y i c) ≤
        f y + K56 i * wsplit56 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m ⟨0, by norm_num⟩ (msplit56 ⟨0, by norm_num⟩) (by norm_num [msplit56]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' => hslp ⟨0, by norm_num⟩ y' k hk) (hmem ⟨0, by norm_num⟩) y
        (by rw [← wsplit56_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m ⟨1, by norm_num⟩ (msplit56 ⟨1, by norm_num⟩) (by norm_num [msplit56]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' => hslp ⟨1, by norm_num⟩ y' k hk) (hmem ⟨1, by norm_num⟩) y
        (by rw [← wsplit56_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m ⟨2, by norm_num⟩ (msplit56 ⟨2, by norm_num⟩) (by norm_num [msplit56]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' => hslp ⟨2, by norm_num⟩ y' k hk) (hmem ⟨2, by norm_num⟩) y
        (by rw [← wsplit56_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m ⟨3, by norm_num⟩ (msplit56 ⟨3, by norm_num⟩) (by norm_num [msplit56]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' => hslp ⟨3, by norm_num⟩ y' k hk) (hmem ⟨3, by norm_num⟩) y
        (by rw [← wsplit56_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m ⟨4, by norm_num⟩ (msplit56 ⟨4, by norm_num⟩) (by norm_num [msplit56]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' => hslp ⟨4, by norm_num⟩ y' k hk) (hmem ⟨4, by norm_num⟩) y
        (by rw [← wsplit56_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m ⟨5, by norm_num⟩ (msplit56 ⟨5, by norm_num⟩) (by norm_num [msplit56]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' => hslp ⟨5, by norm_num⟩ y' k hk) (hmem ⟨5, by norm_num⟩) y
        (by rw [← wsplit56_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b9lo j) (b9hi j)) →
      ∃ c ∈ cands_split56 i, f (Function.update y i c) ≤ f y + RS56 i := by
    intro i y hybox
    rw [RS56v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS56 i := by
    intro i; fin_cases i <;> norm_num [RS56]
  exact final_bound cands_split56 cands_split56_ne hR0 hsub hstep hcorner x hx

/-- Component 61 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 3; 1 = unsplit coordinate). -/

noncomputable def msplit61 : Fin 6 → ℕ := ![1, 3, 3, 3, 3, 3]

/-- Component 61 equal-piece width per coordinate. -/

noncomputable def wsplit61 (i : Fin 6) : ℝ := (b9hi i - b9lo i) / (msplit61 i : ℝ)

/-- Component 61 split grid point `k` per coordinate. -/

noncomputable def gsplit61 (i : Fin 6) (k : ℕ) : ℝ := b9lo i + (k : ℝ) * wsplit61 i

/-- Component 61 split candidate grid (image of `gsplit61` over `range m+1`). -/

noncomputable def cands_split61 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit61 i + 1)).image (gsplit61 i)

theorem msplit61_pos (i : Fin 6) : 0 < msplit61 i := by
  fin_cases i <;> norm_num [msplit61]

theorem wsplit61_pos (i : Fin 6) : 0 ≤ wsplit61 i := by
  fin_cases i <;> norm_num [wsplit61, msplit61, b9lo, b9hi]

theorem wsplit61_hhi (i : Fin 6) : b9hi i = b9lo i + (msplit61 i : ℝ) * wsplit61 i := by
  fin_cases i <;> norm_num [wsplit61, msplit61, b9lo, b9hi]

theorem cands_split61_ne (i : Fin 6) : (cands_split61 i).Nonempty := by
  refine ⟨gsplit61 i 0, ?_⟩
  simp only [cands_split61, gsplit61, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit61_pos i], rfl⟩

theorem cands_split61_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split61 i) :
    c ∈ Set.Icc (b9lo i) (b9hi i) := by
  rw [cands_split61, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit61_pos i) (msplit61_pos i) (wsplit61_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 61 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS61 : Fin 6 → ℝ := ![0, (43312014222397/83886080000000000), (43312014222397/83886080000000000), (2807476955819287/13743895347200000000), (43312014222397/83886080000000000), (43312014222397/83886080000000000)]

/-- Component 61 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS61v_def (i : Fin 6) : RS61 i = K61 i * wsplit61 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS61, K61, wsplit61, msplit61, b9lo, b9hi]

/-- Component 61 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx61 : (0 : ℝ) < B61 - ∑ i, RS61 i := by
  rw [sumFin6s]
  have e0 : RS61 0 = (0 : ℝ) := by rfl
  have e1 : RS61 1 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have e2 : RS61 2 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have e3 : RS61 3 = ((2807476955819287/13743895347200000000) : ℝ) := by rfl
  have e4 : RS61 4 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have e5 : RS61 5 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have eb : B61 = (((9664178295251377365438751/1801439850948198400000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 61 split-grid chain: piecewise shifted concavity over
the `[1, 3, 3, 3, 3, 3]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx61 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit61 i →
      ConcaveOn ℝ (Set.Icc (gsplit61 i k) (gsplit61 i (k + 1)))
        (fun t => f (Function.update y i t) - K61 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split61 j) → B61 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b9lo j) (b9hi j)) :
    B61 - ∑ i, RS61 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K61 i := by
    intro i; fin_cases i <;> norm_num [K61]
  have hw : ∀ i, 0 ≤ wsplit61 i := by
    intro i; fin_cases i <;> norm_num [wsplit61, msplit61, b9lo, b9hi]
  have hhh : ∀ i, b9hi i = b9lo i + (msplit61 i : ℝ) * wsplit61 i := by
    intro i; fin_cases i <;> norm_num [wsplit61, msplit61, b9lo, b9hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit61 i → gsplit61 i k ∈ cands_split61 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split61 i →
      c ∈ Set.Icc (b9lo i) (b9hi i) := by
    intro i c hc
    rw [cands_split61, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit61_pos i) (wsplit61_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b9lo j) (b9hi j)) →
      ∃ c ∈ cands_split61 i, f (Function.update y i c) ≤
        f y + K61 i * wsplit61 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m ⟨0, by norm_num⟩ (msplit61 ⟨0, by norm_num⟩) (by norm_num [msplit61]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' => hslp ⟨0, by norm_num⟩ y' k hk) (hmem ⟨0, by norm_num⟩) y
        (by rw [← wsplit61_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m ⟨1, by norm_num⟩ (msplit61 ⟨1, by norm_num⟩) (by norm_num [msplit61]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' => hslp ⟨1, by norm_num⟩ y' k hk) (hmem ⟨1, by norm_num⟩) y
        (by rw [← wsplit61_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m ⟨2, by norm_num⟩ (msplit61 ⟨2, by norm_num⟩) (by norm_num [msplit61]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' => hslp ⟨2, by norm_num⟩ y' k hk) (hmem ⟨2, by norm_num⟩) y
        (by rw [← wsplit61_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m ⟨3, by norm_num⟩ (msplit61 ⟨3, by norm_num⟩) (by norm_num [msplit61]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' => hslp ⟨3, by norm_num⟩ y' k hk) (hmem ⟨3, by norm_num⟩) y
        (by rw [← wsplit61_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m ⟨4, by norm_num⟩ (msplit61 ⟨4, by norm_num⟩) (by norm_num [msplit61]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' => hslp ⟨4, by norm_num⟩ y' k hk) (hmem ⟨4, by norm_num⟩) y
        (by rw [← wsplit61_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m ⟨5, by norm_num⟩ (msplit61 ⟨5, by norm_num⟩) (by norm_num [msplit61]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' => hslp ⟨5, by norm_num⟩ y' k hk) (hmem ⟨5, by norm_num⟩) y
        (by rw [← wsplit61_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b9lo j) (b9hi j)) →
      ∃ c ∈ cands_split61 i, f (Function.update y i c) ≤ f y + RS61 i := by
    intro i y hybox
    rw [RS61v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS61 i := by
    intro i; fin_cases i <;> norm_num [RS61]
  exact final_bound cands_split61 cands_split61_ne hR0 hsub hstep hcorner x hx

/-- Component 66 split factors (SPLIT_PLAN route `Y4PATCH:y2,y3,y4,y5,y6`, m_min = 3; 1 = unsplit coordinate). -/

noncomputable def msplit66 : Fin 6 → ℕ := ![1, 3, 3, 3, 3, 3]

/-- Component 66 equal-piece width per coordinate. -/

noncomputable def wsplit66 (i : Fin 6) : ℝ := (b9hi i - b9lo i) / (msplit66 i : ℝ)

/-- Component 66 split grid point `k` per coordinate. -/

noncomputable def gsplit66 (i : Fin 6) (k : ℕ) : ℝ := b9lo i + (k : ℝ) * wsplit66 i

/-- Component 66 split candidate grid (image of `gsplit66` over `range m+1`). -/

noncomputable def cands_split66 : Fin 6 → Finset ℝ :=
  fun i => (Finset.range (msplit66 i + 1)).image (gsplit66 i)

theorem msplit66_pos (i : Fin 6) : 0 < msplit66 i := by
  fin_cases i <;> norm_num [msplit66]

theorem wsplit66_pos (i : Fin 6) : 0 ≤ wsplit66 i := by
  fin_cases i <;> norm_num [wsplit66, msplit66, b9lo, b9hi]

theorem wsplit66_hhi (i : Fin 6) : b9hi i = b9lo i + (msplit66 i : ℝ) * wsplit66 i := by
  fin_cases i <;> norm_num [wsplit66, msplit66, b9lo, b9hi]

theorem cands_split66_ne (i : Fin 6) : (cands_split66 i).Nonempty := by
  refine ⟨gsplit66 i 0, ?_⟩
  simp only [cands_split66, gsplit66, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by linarith [msplit66_pos i], rfl⟩

theorem cands_split66_sub (i : Fin 6) (c : ℝ) (hc : c ∈ cands_split66 i) :
    c ∈ Set.Icc (b9lo i) (b9hi i) := by
  rw [cands_split66, Finset.mem_image] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  exact cands_split_sub_aux (wsplit66_pos i) (msplit66_pos i) (wsplit66_hhi i) k
      (by have hk2 := Finset.mem_range.mp hk; omega)

/-- Component 66 split rebates `K·(W/m)²/8` per coordinate (exact fractions). -/

noncomputable def RS66 : Fin 6 → ℝ := ![0, (43312014222397/83886080000000000), (43312014222397/83886080000000000), (2807476955819287/13743895347200000000), (43312014222397/83886080000000000), (43312014222397/83886080000000000)]

/-- Component 66 split-rebate bridge (norm_num validates the
exact fractions against `K·(W/m)²/8`). -/

theorem RS66v_def (i : Fin 6) : RS66 i = K66 i * wsplit66 i ^ 2 / 8 := by
  fin_cases i <;> norm_num [RS66, K66, wsplit66, msplit66, b9lo, b9hi]

/-- Component 66 split feasibility: the SPLIT rebates leave a
positive margin (replaces the false unsplit `hfeas`). -/

theorem feas_split_idx66 : (0 : ℝ) < B66 - ∑ i, RS66 i := by
  rw [sumFin6s]
  have e0 : RS66 0 = (0 : ℝ) := by rfl
  have e1 : RS66 1 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have e2 : RS66 2 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have e3 : RS66 3 = ((2807476955819287/13743895347200000000) : ℝ) := by rfl
  have e4 : RS66 4 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have e5 : RS66 5 = ((43312014222397/83886080000000000) : ℝ) := by rfl
  have eb : B66 = (((9661903076719629790859551/1801439850948198400000000000)) : ℝ) := by rfl
  norm_num [eb, e0, e1, e2, e3, e4, e5]

/-- Component 66 split-grid chain: piecewise shifted concavity over
the `[1, 3, 3, 3, 3, 3]`-split grid + split-grid corner table give the margin bound
with the SPLIT rebates (rebate direction `B − ∑ RSN ≤ f x`). -/

theorem chain_split_idx66 (f : (Fin 6 → ℝ) → ℝ)
    (hslp : ∀ (i : Fin 6) (y : Fin 6 → ℝ) (k : ℕ), k + 1 ≤ msplit66 i →
      ConcaveOn ℝ (Set.Icc (gsplit66 i k) (gsplit66 i (k + 1)))
        (fun t => f (Function.update y i t) - K66 i / 2 * t * t))
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ cands_split66 j) → B66 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b9lo j) (b9hi j)) :
    B66 - ∑ i, RS66 i ≤ f x := by
  have hK0 : ∀ i, 0 ≤ K66 i := by
    intro i; fin_cases i <;> norm_num [K66]
  have hw : ∀ i, 0 ≤ wsplit66 i := by
    intro i; fin_cases i <;> norm_num [wsplit66, msplit66, b9lo, b9hi]
  have hhh : ∀ i, b9hi i = b9lo i + (msplit66 i : ℝ) * wsplit66 i := by
    intro i; fin_cases i <;> norm_num [wsplit66, msplit66, b9lo, b9hi]
  have hmem : ∀ (i : Fin 6) (k : ℕ), k ≤ msplit66 i → gsplit66 i k ∈ cands_split66 i :=
    fun i k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ (i : Fin 6) (c : ℝ), c ∈ cands_split66 i →
      c ∈ Set.Icc (b9lo i) (b9hi i) := by
    intro i c hc
    rw [cands_split66, Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact cands_split_sub_aux (hw i) (msplit66_pos i) (wsplit66_hhi i) k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hstepK : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b9lo j) (b9hi j)) →
      ∃ c ∈ cands_split66 i, f (Function.update y i c) ≤
        f y + K66 i * wsplit66 i ^ 2 / 8 := by
    intro i y hybox
    fin_cases i
    · refine hstep_split_m ⟨0, by norm_num⟩ (msplit66 ⟨0, by norm_num⟩) (by norm_num [msplit66]) (hK0 ⟨0, by norm_num⟩) (hw ⟨0, by norm_num⟩)
        (fun k hk y' => hslp ⟨0, by norm_num⟩ y' k hk) (hmem ⟨0, by norm_num⟩) y
        (by rw [← wsplit66_hhi ⟨0, by norm_num⟩]; exact hybox ⟨0, by norm_num⟩)
    · refine hstep_split_m ⟨1, by norm_num⟩ (msplit66 ⟨1, by norm_num⟩) (by norm_num [msplit66]) (hK0 ⟨1, by norm_num⟩) (hw ⟨1, by norm_num⟩)
        (fun k hk y' => hslp ⟨1, by norm_num⟩ y' k hk) (hmem ⟨1, by norm_num⟩) y
        (by rw [← wsplit66_hhi ⟨1, by norm_num⟩]; exact hybox ⟨1, by norm_num⟩)
    · refine hstep_split_m ⟨2, by norm_num⟩ (msplit66 ⟨2, by norm_num⟩) (by norm_num [msplit66]) (hK0 ⟨2, by norm_num⟩) (hw ⟨2, by norm_num⟩)
        (fun k hk y' => hslp ⟨2, by norm_num⟩ y' k hk) (hmem ⟨2, by norm_num⟩) y
        (by rw [← wsplit66_hhi ⟨2, by norm_num⟩]; exact hybox ⟨2, by norm_num⟩)
    · refine hstep_split_m ⟨3, by norm_num⟩ (msplit66 ⟨3, by norm_num⟩) (by norm_num [msplit66]) (hK0 ⟨3, by norm_num⟩) (hw ⟨3, by norm_num⟩)
        (fun k hk y' => hslp ⟨3, by norm_num⟩ y' k hk) (hmem ⟨3, by norm_num⟩) y
        (by rw [← wsplit66_hhi ⟨3, by norm_num⟩]; exact hybox ⟨3, by norm_num⟩)
    · refine hstep_split_m ⟨4, by norm_num⟩ (msplit66 ⟨4, by norm_num⟩) (by norm_num [msplit66]) (hK0 ⟨4, by norm_num⟩) (hw ⟨4, by norm_num⟩)
        (fun k hk y' => hslp ⟨4, by norm_num⟩ y' k hk) (hmem ⟨4, by norm_num⟩) y
        (by rw [← wsplit66_hhi ⟨4, by norm_num⟩]; exact hybox ⟨4, by norm_num⟩)
    · refine hstep_split_m ⟨5, by norm_num⟩ (msplit66 ⟨5, by norm_num⟩) (by norm_num [msplit66]) (hK0 ⟨5, by norm_num⟩) (hw ⟨5, by norm_num⟩)
        (fun k hk y' => hslp ⟨5, by norm_num⟩ y' k hk) (hmem ⟨5, by norm_num⟩) y
        (by rw [← wsplit66_hhi ⟨5, by norm_num⟩]; exact hybox ⟨5, by norm_num⟩)
  have hstep : ∀ (i : Fin 6) (y : Fin 6 → ℝ), (∀ j, y j ∈ Set.Icc (b9lo j) (b9hi j)) →
      ∃ c ∈ cands_split66 i, f (Function.update y i c) ≤ f y + RS66 i := by
    intro i y hybox
    rw [RS66v_def i]
    exact hstepK i y hybox
  have hR0 : ∀ i, 0 ≤ RS66 i := by
    intro i; fin_cases i <;> norm_num [RS66]
  exact final_bound cands_split66 cands_split66_ne hR0 hsub hstep hcorner x hx

/-! ### Axiom audit -/

#print axioms chain_split_idx1
#print axioms feas_split_idx1

#print axioms chain_split_idx6
#print axioms feas_split_idx6

#print axioms chain_split_idx11
#print axioms feas_split_idx11

#print axioms chain_split_idx16
#print axioms feas_split_idx16

#print axioms chain_split_idx41
#print axioms feas_split_idx41

#print axioms chain_split_idx46
#print axioms feas_split_idx46

#print axioms chain_split_idx51
#print axioms feas_split_idx51

#print axioms chain_split_idx56
#print axioms feas_split_idx56

#print axioms chain_split_idx61
#print axioms feas_split_idx61

#print axioms chain_split_idx66
#print axioms feas_split_idx66

end Kepler.Text
