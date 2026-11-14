/-
LocalAuto19Euler — the `hE` input of the 6T1 conditional assembly
(`0 ≤ yOfX eulerAx_p19 …` on the even triple `vv 0, vv 2, vv 4`), reducing
`empty_6T1_p22`'s residue to the single numeric input `ht4nn`.

## Route (HOL `OCBICBY.hl:2860` `empty_6T1`, eulerA case `:3105-3125`)

`DIH_IMP_EULER_A_POS_p22` (LA22:286, standard three) turns
  * non-collinearity of the three even rays with the origin,
  * `dihV 0 vv0 vv2 vv4 + dihV 0 vv2 vv4 vv0 + dihV 0 vv4 vv0 vv2 < 2π`
    (the solid angle of the even cone at the origin),
  * the length box (`2 ≤ y1..y3 ≤ 2h0`, `3.01 ≤ y4..y6 ≤ 3.915`)
into `yOfX eulerA_x y1..y6 > 0`.

The non-collinearity comes from `PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14`, whose
`Generic` input is `scs_6T1_generic_p22` — hence the `taustar < 0` hypothesis
(HOL's `PROOF_BY_CONTR_TAC` shape).  **The unconditional form is false**: the
regular hexagon (radius 2, adjacent chords 2, diagonals `2√3 ∈ [3.01, 6]`) is
a `BBsV39 scs6T1` configuration whose `ConvexLocalFan` conjuncts both hold
(planar case: `azimInFan = π`, all azimuths `0`/`π`), with Euler-A `= -4`;
there `taustar > 0`.  See the lane's `RECON.md` §counterexample.

## `hsum < 2π` (new, tree-internal)

Write `t i = azim 0 (vv i) (vv (i+1)) (vv (i+5))` (the fan azimuth; `≤ π` from
`ConvexLocalFan`, `≥ 0` from `azim_nonneg`).  The fan splits
(`vv_split_azim_generic_p22`) give, for each `i`,
`t i = A i + B i + C i` with
`A i = azim 0 (vv i) (vv (i+1)) (vv (i+2))`,
`B i = azim 0 (vv i) (vv (i+2)) (vv (i+4))`,
`C i = azim 0 (vv i) (vv (i+4)) (vv (i+5))`;
`AZIM_DIHV_SAME_STRONG` identifies each with the corresponding `dihV`.
`EAR_SOL_NN_p22` on the tetrahedra `(0, vv i, vv (i+1), vv (i+2))` gives the
solid-angle lower bounds `π ≤ A i + t (i+1) + C (i+2)` (for `i = 0,2,4`).
Hence (with `h := B 0 + B 2 + B 4` the even-cone dihedral sum)
`h = (t 0 + t 2 + t 4) - (A 0+A 2+A 4) - (C 0+C 2+C 4) ≤ Σ t - 3π`.
On the other hand `tau_fun_azim` (LA38) + `dsv_unadorned` expand
`taustar < 0` into `Σ rho_i · t i < 4(π + sol0) + 0.712`, and `rho_i ≥ 1`
(annulus radius `≥ 2`) gives `Σ t < 4π + 4 sol0 + 0.712`.  With
`4 sol0 + 0.712 < π` (`g4d_sol0_bounds`: `sol0 ≤ 0.551408`) this yields
`h < π + 4 sol0 + 0.712 < 2π`.

DAG: imports `LocalAuto22` (the `scs`/`EAR_SOL_NN` kit) + `LocalAuto19`
(`eulerAx_p19`) + `Gamma4EnvNum` (the public `sol0` bracket); **not** Close/LA16.
-/
import Kepler.Text.LocalAuto22
import Kepler.Text.LocalAuto19
import Kepler.Text.Gamma4EnvNum
import Mathlib

set_option maxHeartbeats 4000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## small helpers -/

/-- Expand a `setSum` over `{i | i < 6}` into six terms. -/
private theorem he6t1_setSum_six (g : ℕ → ℝ) :
    setSum {i : ℕ | i < 6} g = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := by
  have hfin : ({i : ℕ | i < 6} : Set ℕ).Finite := Set.finite_Iio 6
  rw [setSum, dif_pos hfin]
  have hto : hfin.toFinset = Finset.range 6 := by
    ext j
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_range]
  rw [hto]
  norm_num [Finset.sum_range_succ]

/-- `4 · sol0 + 0.712 < π` (the `taustar < 0` threshold fits under `2π`). -/
private theorem he6t1_four_sol0_lt_pi : 4 * sol0 + (0.712 : ℝ) < Real.pi := by
  have h := g4d_sol0_bounds
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  linarith [h.2]

/-! ## the Euler-A nonnegativity of the even triple -/

/-- **`hE` of the 6T1 assembly** (conditional form — see the module docstring
for why `taustar < 0` cannot be dropped): the Euler-`A` of the even triple
`vv 0, vv 2, vv 4` is nonnegative. -/
theorem hE_6T1 (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs6T1 vv) (ht : taustarV39 scs6T1 vv < 0) :
    0 ≤ yOfX eulerAx_p19 ‖vv 0‖ ‖vv 2‖ ‖vv 4‖ (dist (vv 2) (vv 4))
      (dist (vv 0) (vv 4)) (dist (vv 0) (vv 2)) := by
  -- ===== 0. basic facts =====
  have hann : ∀ i : ℕ, vv i ∈ ballAnnulus := fun i => hB.1 (Set.mem_range_self i)
  have hnorm : ∀ i : ℕ, 2 ≤ ‖vv i‖ ∧ ‖vv i‖ ≤ 2 * h0 :=
    fun i => ballAnnulus_norm_bounds (hann i)
  have hper6 : Periodic vv 6 := hB.2.1
  have hedge : ∀ i : ℕ, dist (vv i) (vv (i + 1)) = 2 :=
    fun i => scs_6T1_props_p22.2.2.2 vv i hB
  have hinj : ∀ i j : ℕ, i < 6 ∧ j < 6 ∧ vv i = vv j → i = j :=
    vv_inj_lemma_p22 scs6T1 vv 6 is_scs_6T1_p22 hB rfl
  have hcf : ConvexLocalFan (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) := by
    rcases hB.2.2.2 with hk3 | hcf
    · exact absurd hk3 (by norm_num : ¬ (6 : ℕ) ≤ 3)
    · exact hcf
  have hgen' : Generic (Set.range vv) (Set.range fun n : ℕ => {vv n, vv (n + 1)}) :=
    scs_6T1_generic_p22 h vv hB ht
  have hvvne : ∀ c d : ℕ, c < 6 → d < 6 → c ≠ d → vv c ≠ vv d := by
    intro c d hc hd hcd he
    exact hcd (hinj c d ⟨hc, hd, he⟩)
  have hprop : ∀ c d : ℕ, c < 6 → d < 6 → c ≠ d → ¬ Collinear3 0 (vv c) (vv d) := by
    intro c d hc hd hcd
    exact PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range vv)
      (Set.range fun n : ℕ => {vv n, vv (n + 1)})
      (Set.range fun n : ℕ => (vv n, vv (n + 1)))
      (vv c) (vv d) hcf.1 (Set.mem_range_self _) (Set.mem_range_self _)
      (hvvne c d hc hd hcd) hgen'
  have hv6 : vv 6 = vv 0 := by simpa using hper6 0
  have hv7 : vv 7 = vv 1 := by simpa using hper6 1
  have hv8 : vv 8 = vv 2 := by simpa using hper6 2
  have hv9 : vv 9 = vv 3 := by simpa using hper6 3
  have hv10 : vv 10 = vv 4 := by simpa using hper6 4
  -- ===== 1. total azimuths ≤ π and the fan splits =====
  have hfanle : ∀ i : ℕ, i < 6 →
      azim 0 (vv i) (vv (i + 1)) (vv (i + 5)) ≤ Real.pi := by
    intro i hi
    have hmem : (vv i, vv (i + 1)) ∈ (Set.range fun n : ℕ => (vv n, vv (n + 1))) :=
      Set.mem_range_self i
    have h1 := (hcf.2 (vv i, vv (i + 1)) hmem).1
    rw [azim_in_fan_azim_p22 vv _ 6 i hper6 (by norm_num) hinj rfl,
      show i + (6 - 1) = i + 5 from rfl] at h1
    exact h1
  have hsplit1 : ∀ i : ℕ, azim 0 (vv i) (vv (i + 1)) (vv (i + 4)) =
      azim 0 (vv i) (vv (i + 1)) (vv (i + 2)) + azim 0 (vv i) (vv (i + 2)) (vv (i + 4)) :=
    fun i => vv_split_azim_generic_p22 vv 6 i 2 4 hper6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hgen' hcf hinj
  have hsplit2 : ∀ i : ℕ, azim 0 (vv i) (vv (i + 1)) (vv (i + 5)) =
      azim 0 (vv i) (vv (i + 1)) (vv (i + 4)) + azim 0 (vv i) (vv (i + 4)) (vv (i + 5)) :=
    fun i => vv_split_azim_generic_p22 vv 6 i 4 5 hper6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hgen' hcf hinj
  have hsplit : ∀ i : ℕ, azim 0 (vv i) (vv (i + 1)) (vv (i + 5)) =
      azim 0 (vv i) (vv (i + 1)) (vv (i + 2)) + azim 0 (vv i) (vv (i + 2)) (vv (i + 4))
        + azim 0 (vv i) (vv (i + 4)) (vv (i + 5)) := by
    intro i; rw [hsplit2 i, hsplit1 i]
  -- concrete (index-normalized) splits at i = 0, 2, 4
  have ht0 : azim 0 (vv 0) (vv 1) (vv 5) =
      azim 0 (vv 0) (vv 1) (vv 2) + azim 0 (vv 0) (vv 2) (vv 4)
        + azim 0 (vv 0) (vv 4) (vv 5) :=
    hsplit 0
  have ht2 : azim 0 (vv 2) (vv 3) (vv 1) =
      azim 0 (vv 2) (vv 3) (vv 4) + azim 0 (vv 2) (vv 4) (vv 0)
        + azim 0 (vv 2) (vv 0) (vv 1) := by
    have hh := hsplit 2
    rw [show 2 + 1 = 3 from rfl, show 2 + 2 = 4 from rfl, show 2 + 4 = 6 from rfl,
      show 2 + 5 = 7 from rfl] at hh
    rw [hv6, hv7] at hh
    exact hh
  have ht4 : azim 0 (vv 4) (vv 5) (vv 3) =
      azim 0 (vv 4) (vv 5) (vv 0) + azim 0 (vv 4) (vv 0) (vv 2)
        + azim 0 (vv 4) (vv 2) (vv 3) := by
    have hh := hsplit 4
    rw [show 4 + 1 = 5 from rfl, show 4 + 2 = 6 from rfl, show 4 + 4 = 8 from rfl,
      show 4 + 5 = 9 from rfl] at hh
    rw [hv6, hv8, hv9] at hh
    exact hh
  -- totals at i = 1, 3, 5 (only their `≤ π` is used, for the dihV bridges)
  have ht1le : azim 0 (vv 1) (vv 2) (vv 0) ≤ Real.pi := by
    have hh := hfanle 1 (by norm_num)
    rwa [show 1 + (6 - 1) = 6 from rfl, hv6] at hh
  have ht3le : azim 0 (vv 3) (vv 4) (vv 2) ≤ Real.pi := by
    have hh := hfanle 3 (by norm_num)
    rwa [show 3 + (6 - 1) = 8 from rfl, hv8] at hh
  have ht5le : azim 0 (vv 5) (vv 0) (vv 4) ≤ Real.pi := by
    have hh := hfanle 5 (by norm_num)
    rwa [show 5 + (6 - 1) = 10 from rfl, hv6, hv10] at hh
  -- ===== 2. piecewise ≤ π inside the three even splits =====
  have hA0le : azim 0 (vv 0) (vv 1) (vv 2) ≤ Real.pi := by
    have h1 := azim_nonneg 0 (vv 0) (vv 2) (vv 4)
    have h2 := azim_nonneg 0 (vv 0) (vv 4) (vv 5)
    have h3 := hfanle 0 (by norm_num)
    linarith [ht0]
  have hB0le : azim 0 (vv 0) (vv 2) (vv 4) ≤ Real.pi := by
    have h1 := azim_nonneg 0 (vv 0) (vv 1) (vv 2)
    have h2 := azim_nonneg 0 (vv 0) (vv 4) (vv 5)
    have h3 := hfanle 0 (by norm_num)
    linarith [ht0]
  have hC0le : azim 0 (vv 0) (vv 4) (vv 5) ≤ Real.pi := by
    have h1 := azim_nonneg 0 (vv 0) (vv 1) (vv 2)
    have h2 := azim_nonneg 0 (vv 0) (vv 2) (vv 4)
    have h3 := hfanle 0 (by norm_num)
    linarith [ht0]
  have hA2le : azim 0 (vv 2) (vv 3) (vv 4) ≤ Real.pi := by
    have h1 := azim_nonneg 0 (vv 2) (vv 4) (vv 0)
    have h2 := azim_nonneg 0 (vv 2) (vv 0) (vv 1)
    have h3 : azim 0 (vv 2) (vv 3) (vv 7) ≤ Real.pi := hfanle 2 (by norm_num)
    rw [hv7] at h3
    linarith [ht2]
  have hB2le : azim 0 (vv 2) (vv 4) (vv 0) ≤ Real.pi := by
    have h1 := azim_nonneg 0 (vv 2) (vv 3) (vv 4)
    have h2 := azim_nonneg 0 (vv 2) (vv 0) (vv 1)
    have h3 : azim 0 (vv 2) (vv 3) (vv 7) ≤ Real.pi := hfanle 2 (by norm_num)
    rw [hv7] at h3
    linarith [ht2]
  have hC2le : azim 0 (vv 2) (vv 0) (vv 1) ≤ Real.pi := by
    have h1 := azim_nonneg 0 (vv 2) (vv 3) (vv 4)
    have h2 := azim_nonneg 0 (vv 2) (vv 4) (vv 0)
    have h3 : azim 0 (vv 2) (vv 3) (vv 7) ≤ Real.pi := hfanle 2 (by norm_num)
    rw [hv7] at h3
    linarith [ht2]
  have hA4le : azim 0 (vv 4) (vv 5) (vv 0) ≤ Real.pi := by
    have h1 := azim_nonneg 0 (vv 4) (vv 0) (vv 2)
    have h2 := azim_nonneg 0 (vv 4) (vv 2) (vv 3)
    have h3 : azim 0 (vv 4) (vv 5) (vv 9) ≤ Real.pi := hfanle 4 (by norm_num)
    rw [hv9] at h3
    linarith [ht4]
  have hB4le : azim 0 (vv 4) (vv 0) (vv 2) ≤ Real.pi := by
    have h1 := azim_nonneg 0 (vv 4) (vv 5) (vv 0)
    have h2 := azim_nonneg 0 (vv 4) (vv 2) (vv 3)
    have h3 : azim 0 (vv 4) (vv 5) (vv 9) ≤ Real.pi := hfanle 4 (by norm_num)
    rw [hv9] at h3
    linarith [ht4]
  have hC4le : azim 0 (vv 4) (vv 2) (vv 3) ≤ Real.pi := by
    have h1 := azim_nonneg 0 (vv 4) (vv 5) (vv 0)
    have h2 := azim_nonneg 0 (vv 4) (vv 0) (vv 2)
    have h3 : azim 0 (vv 4) (vv 5) (vv 9) ≤ Real.pi := hfanle 4 (by norm_num)
    rw [hv9] at h3
    linarith [ht4]
  -- ===== 3. the twelve `azim = dihV` bridges =====
  have hbrA0 : azim 0 (vv 0) (vv 1) (vv 2) = dihV 0 (vv 0) (vv 1) (vv 2) :=
    AZIM_DIHV_SAME_STRONG (hprop 0 1 (by norm_num) (by norm_num) (by norm_num))
      (hprop 0 2 (by norm_num) (by norm_num) (by norm_num)) hA0le
  have hbrB0 : azim 0 (vv 0) (vv 2) (vv 4) = dihV 0 (vv 0) (vv 2) (vv 4) :=
    AZIM_DIHV_SAME_STRONG (hprop 0 2 (by norm_num) (by norm_num) (by norm_num))
      (hprop 0 4 (by norm_num) (by norm_num) (by norm_num)) hB0le
  have hbrC0 : azim 0 (vv 0) (vv 4) (vv 5) = dihV 0 (vv 0) (vv 4) (vv 5) :=
    AZIM_DIHV_SAME_STRONG (hprop 0 4 (by norm_num) (by norm_num) (by norm_num))
      (hprop 0 5 (by norm_num) (by norm_num) (by norm_num)) hC0le
  have hbrt1 : azim 0 (vv 1) (vv 2) (vv 0) = dihV 0 (vv 1) (vv 2) (vv 0) :=
    AZIM_DIHV_SAME_STRONG (hprop 1 2 (by norm_num) (by norm_num) (by norm_num))
      (hprop 1 0 (by norm_num) (by norm_num) (by norm_num)) ht1le
  have hbrA2 : azim 0 (vv 2) (vv 3) (vv 4) = dihV 0 (vv 2) (vv 3) (vv 4) :=
    AZIM_DIHV_SAME_STRONG (hprop 2 3 (by norm_num) (by norm_num) (by norm_num))
      (hprop 2 4 (by norm_num) (by norm_num) (by norm_num)) hA2le
  have hbrB2 : azim 0 (vv 2) (vv 4) (vv 0) = dihV 0 (vv 2) (vv 4) (vv 0) :=
    AZIM_DIHV_SAME_STRONG (hprop 2 4 (by norm_num) (by norm_num) (by norm_num))
      (hprop 2 0 (by norm_num) (by norm_num) (by norm_num)) hB2le
  have hbrC2 : azim 0 (vv 2) (vv 0) (vv 1) = dihV 0 (vv 2) (vv 0) (vv 1) :=
    AZIM_DIHV_SAME_STRONG (hprop 2 0 (by norm_num) (by norm_num) (by norm_num))
      (hprop 2 1 (by norm_num) (by norm_num) (by norm_num)) hC2le
  have hbrt3 : azim 0 (vv 3) (vv 4) (vv 2) = dihV 0 (vv 3) (vv 4) (vv 2) :=
    AZIM_DIHV_SAME_STRONG (hprop 3 4 (by norm_num) (by norm_num) (by norm_num))
      (hprop 3 2 (by norm_num) (by norm_num) (by norm_num)) ht3le
  have hbrA4 : azim 0 (vv 4) (vv 5) (vv 0) = dihV 0 (vv 4) (vv 5) (vv 0) :=
    AZIM_DIHV_SAME_STRONG (hprop 4 5 (by norm_num) (by norm_num) (by norm_num))
      (hprop 4 0 (by norm_num) (by norm_num) (by norm_num)) hA4le
  have hbrB4 : azim 0 (vv 4) (vv 0) (vv 2) = dihV 0 (vv 4) (vv 0) (vv 2) :=
    AZIM_DIHV_SAME_STRONG (hprop 4 0 (by norm_num) (by norm_num) (by norm_num))
      (hprop 4 2 (by norm_num) (by norm_num) (by norm_num)) hB4le
  have hbrC4 : azim 0 (vv 4) (vv 2) (vv 3) = dihV 0 (vv 4) (vv 2) (vv 3) :=
    AZIM_DIHV_SAME_STRONG (hprop 4 2 (by norm_num) (by norm_num) (by norm_num))
      (hprop 4 3 (by norm_num) (by norm_num) (by norm_num)) hC4le
  have hbrt5 : azim 0 (vv 5) (vv 0) (vv 4) = dihV 0 (vv 5) (vv 0) (vv 4) :=
    AZIM_DIHV_SAME_STRONG (hprop 5 0 (by norm_num) (by norm_num) (by norm_num))
      (hprop 5 4 (by norm_num) (by norm_num) (by norm_num)) ht5le
  -- ===== 4. length box: two-step diagonals =====
  have hdiag20 : ∀ i : ℕ, scsDiag 6 i (i + 2) := by
    intro i
    refine ⟨MOD_INJ1_ALT (by norm_num : (6 : ℕ) ≠ 0) (by norm_num : (2 : ℕ) < 6)
        (by norm_num : (2 : ℕ) ≠ 0) i,
      MOD_INJ1_ALT (by norm_num : (6 : ℕ) ≠ 0) (by norm_num : (1 : ℕ) < 6)
        (by norm_num : (1 : ℕ) ≠ 0) (i + 1),
      MOD_INJ1_ALT (by norm_num : (6 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) < 6)
        (by norm_num : (3 : ℕ) ≠ 0) i⟩
  have hd2l : ∀ i : ℕ, cstab ≤ dist (vv i) (vv (i + 2)) :=
    fun i => scs_6T1_props_p22.2.2.1 vv i (i + 2) hB (hdiag20 i)
  have h252 : (2 : ℝ) * h0 = 2.52 := by norm_num [h0]
  have h4i : ∀ i : ℕ, dist (vv i) (vv (i + 2)) ≤ 4 := by
    intro i
    have htri := dist_triangle (vv i) (vv (i + 1)) (vv (i + 2))
    rw [hedge i, hedge (i + 1)] at htri
    linarith
  have hreg : mainEstimate_6459846571 :=
    h "6459846571" (by simp [mainNonlinearTerminalV11Ids_t11])
  unfold mainEstimate_6459846571 at hreg
  have hd2u : ∀ i : ℕ, dist (vv i) (vv (i + 2)) < 3.915 := by
    intro i
    have hdpos := DELTA_Y_POS_4POINTS (0 : V3) (vv (i + 1)) (vv i) (vv (i + 2))
    rw [dist_zero_left, dist_zero_left, dist_zero_left,
      show dist (vv (i + 1)) (vv (i + 2)) = 2 from hedge (i + 1),
      show dist (vv (i + 1)) (vv i) = 2 from by rw [dist_comm]; exact hedge i] at hdpos
    have hb1 := hnorm (i + 1)
    have hb2 := hnorm i
    have hb3 := hnorm (i + 2)
    have hc2 := hd2l i
    rw [cstab_eq_p22] at hc2
    have hr := hreg ‖vv (i + 1)‖ ‖vv i‖ ‖vv (i + 2)‖ (dist (vv i) (vv (i + 2))) 2 2
      hb1.1 (by linarith [hb1.2, h252]) hb2.1 (by linarith [hb2.2, h252])
      hb3.1 (by linarith [hb3.2, h252]) (by linarith) (by linarith [h4i i])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rcases hr with hlt | hdlt
    · exact hlt
    · exact absurd hdlt (not_lt.mpr hdpos)
  -- ===== 5. the three solid-angle lower bounds (EAR_SOL_NN) =====
  -- distance facts for the `dihY` slot normalization
  have h10 : dist (vv 1) (vv 0) = 2 := by rw [dist_comm]; exact hedge 0
  have h21 : dist (vv 2) (vv 1) = 2 := by rw [dist_comm]; exact hedge 1
  have h05 : dist (vv 0) (vv 5) = 2 := by rw [dist_comm, ← hv6]; exact hedge 5
  have h54 : dist (vv 5) (vv 4) = 2 := by rw [dist_comm]; exact hedge 4
  have h32 : dist (vv 3) (vv 2) = 2 := by rw [dist_comm]; exact hedge 2
  have h43 : dist (vv 4) (vv 3) = 2 := by rw [dist_comm]; exact hedge 3
  -- S_0: tetrahedron (0, vv 1, vv 0, vv 2)
  have hK0 : Real.pi ≤ azim 0 (vv 0) (vv 1) (vv 2) + azim 0 (vv 1) (vv 2) (vv 0)
      + azim 0 (vv 2) (vv 0) (vv 1) := by
    have hd : 0 ≤ deltaY ‖vv 1‖ ‖vv 0‖ ‖vv 2‖ (dist (vv 0) (vv 2)) 2 2 := by
      have hpos := DELTA_Y_POS_4POINTS (0 : V3) (vv 1) (vv 0) (vv 2)
      rw [dist_zero_left, dist_zero_left, dist_zero_left, hedge 1, h10] at hpos
      exact hpos
    have hbase := EAR_SOL_NN_p22 h ‖vv 1‖ ‖vv 0‖ ‖vv 2‖ (dist (vv 0) (vv 2)) 2 2
      (hnorm 1) (hnorm 0) (hnorm 2) ⟨hd2l 0, le_of_lt (hd2u 0)⟩ (by norm_num)
      (by norm_num) hd
    unfold solY at hbase
    have e1 : azim 0 (vv 1) (vv 2) (vv 0) = dihY ‖vv 1‖ ‖vv 0‖ ‖vv 2‖
        (dist (vv 0) (vv 2)) 2 2 := by
      have hmain : azim 0 (vv 1) (vv 2) (vv 0) = dihY (dist (0 : V3) (vv 1))
          (dist 0 (vv 0)) (dist 0 (vv 2)) (dist (vv 0) (vv 2)) (dist (vv 1) (vv 2))
          (dist (vv 1) (vv 0)) := by
        rw [hbrt1, ← DIHV_SYM_2 0 (vv 1) (vv 0) (vv 2),
          DIHV_EQ_DIH_Y_4PT 0 (vv 1) (vv 0) (vv 2)
            (hprop 1 0 (by norm_num) (by norm_num) (by norm_num))
            (hprop 1 2 (by norm_num) (by norm_num) (by norm_num))]
      simpa only [dist_zero_left, hedge 1, h10] using hmain
    have e2 : azim 0 (vv 0) (vv 1) (vv 2) = dihY ‖vv 0‖ ‖vv 2‖ ‖vv 1‖ 2 2
        (dist (vv 0) (vv 2)) := by
      have hmain : azim 0 (vv 0) (vv 1) (vv 2) = dihY (dist (0 : V3) (vv 0))
          (dist 0 (vv 2)) (dist 0 (vv 1)) (dist (vv 2) (vv 1)) (dist (vv 0) (vv 1))
          (dist (vv 0) (vv 2)) := by
        rw [hbrA0, ← DIHV_SYM_2 0 (vv 0) (vv 2) (vv 1),
          DIHV_EQ_DIH_Y_4PT 0 (vv 0) (vv 2) (vv 1)
            (hprop 0 2 (by norm_num) (by norm_num) (by norm_num))
            (hprop 0 1 (by norm_num) (by norm_num) (by norm_num))]
      simpa only [dist_zero_left, h21, hedge 0] using hmain
    have e3 : azim 0 (vv 2) (vv 0) (vv 1) = dihY ‖vv 2‖ ‖vv 1‖ ‖vv 0‖ 2
        (dist (vv 0) (vv 2)) 2 := by
      have hmain : azim 0 (vv 2) (vv 0) (vv 1) = dihY (dist (0 : V3) (vv 2))
          (dist 0 (vv 1)) (dist 0 (vv 0)) (dist (vv 1) (vv 0)) (dist (vv 2) (vv 0))
          (dist (vv 2) (vv 1)) := by
        rw [hbrC2, ← DIHV_SYM_2 0 (vv 2) (vv 1) (vv 0),
          DIHV_EQ_DIH_Y_4PT 0 (vv 2) (vv 1) (vv 0)
            (hprop 2 1 (by norm_num) (by norm_num) (by norm_num))
            (hprop 2 0 (by norm_num) (by norm_num) (by norm_num))]
      simpa only [dist_zero_left, h10, h21, dist_comm (vv 2) (vv 0)] using hmain
    rw [← e1, ← e2, ← e3] at hbase
    linarith
  -- S_2: tetrahedron (0, vv 3, vv 2, vv 4)
  have hK2 : Real.pi ≤ azim 0 (vv 2) (vv 3) (vv 4) + azim 0 (vv 3) (vv 4) (vv 2)
      + azim 0 (vv 4) (vv 2) (vv 3) := by
    have hd : 0 ≤ deltaY ‖vv 3‖ ‖vv 2‖ ‖vv 4‖ (dist (vv 2) (vv 4)) 2 2 := by
      have hpos := DELTA_Y_POS_4POINTS (0 : V3) (vv 3) (vv 2) (vv 4)
      rw [dist_zero_left, dist_zero_left, dist_zero_left, hedge 3, h32] at hpos
      exact hpos
    have hbase := EAR_SOL_NN_p22 h ‖vv 3‖ ‖vv 2‖ ‖vv 4‖ (dist (vv 2) (vv 4)) 2 2
      (hnorm 3) (hnorm 2) (hnorm 4) ⟨hd2l 2, le_of_lt (hd2u 2)⟩ (by norm_num)
      (by norm_num) hd
    unfold solY at hbase
    have e1 : azim 0 (vv 3) (vv 4) (vv 2) = dihY ‖vv 3‖ ‖vv 2‖ ‖vv 4‖
        (dist (vv 2) (vv 4)) 2 2 := by
      have hmain : azim 0 (vv 3) (vv 4) (vv 2) = dihY (dist (0 : V3) (vv 3))
          (dist 0 (vv 2)) (dist 0 (vv 4)) (dist (vv 2) (vv 4)) (dist (vv 3) (vv 4))
          (dist (vv 3) (vv 2)) := by
        rw [hbrt3, ← DIHV_SYM_2 0 (vv 3) (vv 2) (vv 4),
          DIHV_EQ_DIH_Y_4PT 0 (vv 3) (vv 2) (vv 4)
            (hprop 3 2 (by norm_num) (by norm_num) (by norm_num))
            (hprop 3 4 (by norm_num) (by norm_num) (by norm_num))]
      simpa only [dist_zero_left, hedge 3, h32] using hmain
    have e2 : azim 0 (vv 2) (vv 3) (vv 4) = dihY ‖vv 2‖ ‖vv 4‖ ‖vv 3‖ 2 2
        (dist (vv 2) (vv 4)) := by
      have hmain : azim 0 (vv 2) (vv 3) (vv 4) = dihY (dist (0 : V3) (vv 2))
          (dist 0 (vv 4)) (dist 0 (vv 3)) (dist (vv 4) (vv 3)) (dist (vv 2) (vv 3))
          (dist (vv 2) (vv 4)) := by
        rw [hbrA2, ← DIHV_SYM_2 0 (vv 2) (vv 4) (vv 3),
          DIHV_EQ_DIH_Y_4PT 0 (vv 2) (vv 4) (vv 3)
            (hprop 2 4 (by norm_num) (by norm_num) (by norm_num))
            (hprop 2 3 (by norm_num) (by norm_num) (by norm_num))]
      simpa only [dist_zero_left, h43, hedge 2] using hmain
    have e3 : azim 0 (vv 4) (vv 2) (vv 3) = dihY ‖vv 4‖ ‖vv 3‖ ‖vv 2‖ 2
        (dist (vv 2) (vv 4)) 2 := by
      have hmain : azim 0 (vv 4) (vv 2) (vv 3) = dihY (dist (0 : V3) (vv 4))
          (dist 0 (vv 3)) (dist 0 (vv 2)) (dist (vv 3) (vv 2)) (dist (vv 4) (vv 2))
          (dist (vv 4) (vv 3)) := by
        rw [hbrC4, ← DIHV_SYM_2 0 (vv 4) (vv 3) (vv 2),
          DIHV_EQ_DIH_Y_4PT 0 (vv 4) (vv 3) (vv 2)
            (hprop 4 3 (by norm_num) (by norm_num) (by norm_num))
            (hprop 4 2 (by norm_num) (by norm_num) (by norm_num))]
      simpa only [dist_zero_left, h32, h43, dist_comm (vv 4) (vv 2)] using hmain
    rw [← e1, ← e2, ← e3] at hbase
    linarith
  -- S_4: tetrahedron (0, vv 5, vv 4, vv 0)
  have hK4 : Real.pi ≤ azim 0 (vv 4) (vv 5) (vv 0) + azim 0 (vv 5) (vv 0) (vv 4)
      + azim 0 (vv 0) (vv 4) (vv 5) := by
    have hd : 0 ≤ deltaY ‖vv 5‖ ‖vv 4‖ ‖vv 0‖ (dist (vv 0) (vv 4)) 2 2 := by
      have hpos := DELTA_Y_POS_4POINTS (0 : V3) (vv 5) (vv 4) (vv 0)
      rw [dist_zero_left, dist_zero_left, dist_zero_left, h54,
        dist_comm (vv 5) (vv 0), h05,
        show dist (vv 4) (vv 0) = dist (vv 0) (vv 4) from dist_comm _ _] at hpos
      exact hpos
    have hbase := EAR_SOL_NN_p22 h ‖vv 5‖ ‖vv 4‖ ‖vv 0‖ (dist (vv 0) (vv 4)) 2 2
      (hnorm 5) (hnorm 4) (hnorm 0)
      ⟨by rw [dist_comm, ← hv6]; exact hd2l 4,
        by rw [dist_comm, ← hv6]; exact le_of_lt (hd2u 4)⟩
      (by norm_num) (by norm_num) hd
    unfold solY at hbase
    have e1 : azim 0 (vv 5) (vv 0) (vv 4) = dihY ‖vv 5‖ ‖vv 4‖ ‖vv 0‖
        (dist (vv 0) (vv 4)) 2 2 := by
      have hmain : azim 0 (vv 5) (vv 0) (vv 4) = dihY (dist (0 : V3) (vv 5))
          (dist 0 (vv 4)) (dist 0 (vv 0)) (dist (vv 4) (vv 0)) (dist (vv 5) (vv 0))
          (dist (vv 5) (vv 4)) := by
        rw [hbrt5, ← DIHV_SYM_2 0 (vv 5) (vv 4) (vv 0),
          DIHV_EQ_DIH_Y_4PT 0 (vv 5) (vv 4) (vv 0)
            (hprop 5 4 (by norm_num) (by norm_num) (by norm_num))
            (hprop 5 0 (by norm_num) (by norm_num) (by norm_num))]
      simpa only [dist_zero_left, dist_comm (vv 5) (vv 0), h05, h54,
        show dist (vv 4) (vv 0) = dist (vv 0) (vv 4) from dist_comm _ _] using hmain
    have e2 : azim 0 (vv 4) (vv 5) (vv 0) = dihY ‖vv 4‖ ‖vv 0‖ ‖vv 5‖ 2 2
        (dist (vv 0) (vv 4)) := by
      have hmain : azim 0 (vv 4) (vv 5) (vv 0) = dihY (dist (0 : V3) (vv 4))
          (dist 0 (vv 0)) (dist 0 (vv 5)) (dist (vv 0) (vv 5)) (dist (vv 4) (vv 5))
          (dist (vv 4) (vv 0)) := by
        rw [hbrA4, ← DIHV_SYM_2 0 (vv 4) (vv 0) (vv 5),
          DIHV_EQ_DIH_Y_4PT 0 (vv 4) (vv 0) (vv 5)
            (hprop 4 0 (by norm_num) (by norm_num) (by norm_num))
            (hprop 4 5 (by norm_num) (by norm_num) (by norm_num))]
      simpa only [dist_zero_left, h05, hedge 4,
        show dist (vv 4) (vv 0) = dist (vv 0) (vv 4) from dist_comm _ _] using hmain
    have e3 : azim 0 (vv 0) (vv 4) (vv 5) = dihY ‖vv 0‖ ‖vv 5‖ ‖vv 4‖ 2
        (dist (vv 0) (vv 4)) 2 := by
      have hmain : azim 0 (vv 0) (vv 4) (vv 5) = dihY (dist (0 : V3) (vv 0))
          (dist 0 (vv 5)) (dist 0 (vv 4)) (dist (vv 5) (vv 4)) (dist (vv 0) (vv 4))
          (dist (vv 0) (vv 5)) := by
        rw [hbrC0, ← DIHV_SYM_2 0 (vv 0) (vv 5) (vv 4),
          DIHV_EQ_DIH_Y_4PT 0 (vv 0) (vv 5) (vv 4)
            (hprop 0 5 (by norm_num) (by norm_num) (by norm_num))
            (hprop 0 4 (by norm_num) (by norm_num) (by norm_num))]
      simpa only [dist_zero_left, h54, hedge 0, h05] using hmain
    rw [← e1, ← e2, ← e3] at hbase
    linarith
  -- ===== 6. taustar < 0 ⇒ Σ rho_i·t_i < 4(π+sol0) + 0.712 =====
  have htau_eq : taustarV39 scs6T1 vv =
      tauFun (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
        (Set.range fun i => (vv i, vv (i + 1))) - dsvV39 scs6T1 vv := by
    show (if scs6T1.k ≤ 3 then tau3 (vv 0) (vv 1) (vv 2) - dsvV39 scs6T1 vv
      else tauFun (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
        (Set.range fun i => (vv i, vv (i + 1))) - dsvV39 scs6T1 vv) = _
    rw [if_neg (by decide : ¬ scs6T1.k ≤ 3)]
  have hdsv : dsvV39 scs6T1 vv = 0.712 := by
    rw [show scs6T1 = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 cstab) (csAdj 6 2 6) from rfl,
      dsv_unadorned]
    norm_num [dTame]
  have htf := tau_fun_azim vv 6 hper6 (by norm_num) hinj
  have hset : setSum {i : ℕ | i < 6}
      (fun i => rhoFun ‖vv i‖ * azim 0 (vv i) (vv (i + 1)) (vv (i + 5)))
      < 4 * (Real.pi + sol0) + 0.712 := by
    have h1 : taustarV39 scs6T1 vv = setSum {i : ℕ | i < 6}
        (fun i => rhoFun ‖vv i‖ * azim 0 (vv i) (vv (i + 1)) (vv (i + 5)))
        - 4 * (Real.pi + sol0) - 0.712 := by
      rw [htau_eq, htf, hdsv]
      ring
    linarith [ht]
  have hrho : ∀ i : ℕ, i < 6 → (1 : ℝ) ≤ rhoFun ‖vv i‖ := by
    intro i hi
    have h20 : (0 : ℝ) < 2 * h0 - 2 := by norm_num [h0]
    have hpisol : 0 ≤ sol0 := le_trans (by norm_num) g4d_sol0_bounds.1
    have hy : (0 : ℝ) ≤ ‖vv i‖ - 2 := by linarith [(hnorm i).1]
    have hcoef : (0 : ℝ) ≤ (1 / (2 * h0 - 2)) * (1 / Real.pi) * sol0 := by positivity
    have hmul : 0 ≤ (1 / (2 * h0 - 2)) * (1 / Real.pi) * sol0 * (‖vv i‖ - 2) :=
      mul_nonneg hcoef hy
    unfold rhoFun
    linarith
  -- the sum of the six plain azimuths is dominated by the weighted sum
  have hle6 : setSum {i : ℕ | i < 6} (fun i => azim 0 (vv i) (vv (i + 1)) (vv (i + 5)))
      ≤ setSum {i : ℕ | i < 6}
        (fun i => rhoFun ‖vv i‖ * azim 0 (vv i) (vv (i + 1)) (vv (i + 5))) := by
    rw [he6t1_setSum_six (fun i => azim 0 (vv i) (vv (i + 1)) (vv (i + 5))),
      he6t1_setSum_six (fun i => rhoFun ‖vv i‖ * azim 0 (vv i) (vv (i + 1)) (vv (i + 5)))]
    simp only [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
      show (2 : ℕ) + 1 = 3 from rfl, show (3 : ℕ) + 1 = 4 from rfl,
      show (4 : ℕ) + 1 = 5 from rfl, show (5 : ℕ) + 1 = 6 from rfl,
      show (0 : ℕ) + 5 = 5 from rfl, show (1 : ℕ) + 5 = 6 from rfl,
      show (2 : ℕ) + 5 = 7 from rfl, show (3 : ℕ) + 5 = 8 from rfl,
      show (4 : ℕ) + 5 = 9 from rfl, show (5 : ℕ) + 5 = 10 from rfl,
      hv6, hv7, hv8, hv9, hv10]
    have hp0 : azim 0 (vv 0) (vv 1) (vv 5) ≤
        rhoFun ‖vv 0‖ * azim 0 (vv 0) (vv 1) (vv 5) := by
      have hnn := azim_nonneg 0 (vv 0) (vv 1) (vv 5)
      nlinarith [hrho 0 (by norm_num)]
    have hp1 : azim 0 (vv 1) (vv 2) (vv 0) ≤
        rhoFun ‖vv 1‖ * azim 0 (vv 1) (vv 2) (vv 0) := by
      have hnn := azim_nonneg 0 (vv 1) (vv 2) (vv 0)
      nlinarith [hrho 1 (by norm_num)]
    have hp2 : azim 0 (vv 2) (vv 3) (vv 1) ≤
        rhoFun ‖vv 2‖ * azim 0 (vv 2) (vv 3) (vv 1) := by
      have hnn := azim_nonneg 0 (vv 2) (vv 3) (vv 1)
      nlinarith [hrho 2 (by norm_num)]
    have hp3 : azim 0 (vv 3) (vv 4) (vv 2) ≤
        rhoFun ‖vv 3‖ * azim 0 (vv 3) (vv 4) (vv 2) := by
      have hnn := azim_nonneg 0 (vv 3) (vv 4) (vv 2)
      nlinarith [hrho 3 (by norm_num)]
    have hp4 : azim 0 (vv 4) (vv 5) (vv 3) ≤
        rhoFun ‖vv 4‖ * azim 0 (vv 4) (vv 5) (vv 3) := by
      have hnn := azim_nonneg 0 (vv 4) (vv 5) (vv 3)
      nlinarith [hrho 4 (by norm_num)]
    have hp5 : azim 0 (vv 5) (vv 0) (vv 4) ≤
        rhoFun ‖vv 5‖ * azim 0 (vv 5) (vv 0) (vv 4) := by
      have hnn := azim_nonneg 0 (vv 5) (vv 0) (vv 4)
      nlinarith [hrho 5 (by norm_num)]
    linarith
  -- Σ t_i < 4π + 4sol0 + 0.712 (normalized atoms)
  have hT : azim 0 (vv 0) (vv 1) (vv 5) + azim 0 (vv 1) (vv 2) (vv 0)
      + azim 0 (vv 2) (vv 3) (vv 1) + azim 0 (vv 3) (vv 4) (vv 2)
      + azim 0 (vv 4) (vv 5) (vv 3) + azim 0 (vv 5) (vv 0) (vv 4)
      < 4 * Real.pi + 4 * sol0 + 0.712 := by
    have hraw := lt_of_le_of_lt hle6 hset
    rw [he6t1_setSum_six (fun i => azim 0 (vv i) (vv (i + 1)) (vv (i + 5)))] at hraw
    simp only [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
      show (2 : ℕ) + 1 = 3 from rfl, show (3 : ℕ) + 1 = 4 from rfl,
      show (4 : ℕ) + 1 = 5 from rfl, show (5 : ℕ) + 1 = 6 from rfl,
      show (0 : ℕ) + 5 = 5 from rfl, show (1 : ℕ) + 5 = 6 from rfl,
      show (2 : ℕ) + 5 = 7 from rfl, show (3 : ℕ) + 5 = 8 from rfl,
      show (4 : ℕ) + 5 = 9 from rfl, show (5 : ℕ) + 5 = 10 from rfl,
      hv6, hv7, hv8, hv9, hv10] at hraw
    linarith
  -- ===== 7. the solid angle of the even cone is < 2π =====
  have hsum_lt : dihV 0 (vv 0) (vv 2) (vv 4) + dihV 0 (vv 2) (vv 4) (vv 0)
      + dihV 0 (vv 4) (vv 0) (vv 2) < 2 * Real.pi := by
    have hnum := he6t1_four_sol0_lt_pi
    linarith [ht0, ht2, ht4, hbrB0, hbrB2, hbrB4, hK0, hK2, hK4, hT, hnum]
  -- ===== 8. DIH_IMP_EULER_A_POS =====
  have hpos : 0 < yOfX eulerAX_p22 (dist (0 : V3) (vv 0)) (dist 0 (vv 2))
      (dist 0 (vv 4)) (dist (vv 2) (vv 4)) (dist (vv 0) (vv 4)) (dist (vv 0) (vv 2)) :=
    DIH_IMP_EULER_A_POS_p22 h 0 (vv 0) (vv 2) (vv 4)
      (hprop 0 2 (by norm_num) (by norm_num) (by norm_num))
      (hprop 2 4 (by norm_num) (by norm_num) (by norm_num))
      (hprop 0 4 (by norm_num) (by norm_num) (by norm_num))
      hsum_lt
      ⟨by rw [dist_zero_left]; exact (hnorm 0).1,
        by rw [dist_zero_left]; exact (hnorm 0).2⟩
      ⟨by rw [dist_zero_left]; exact (hnorm 2).1,
        by rw [dist_zero_left]; exact (hnorm 2).2⟩
      ⟨by rw [dist_zero_left]; exact (hnorm 4).1,
        by rw [dist_zero_left]; exact (hnorm 4).2⟩
      ⟨hd2l 2, le_of_lt (hd2u 2)⟩
      ⟨by rw [dist_comm, ← hv6]; exact hd2l 4,
        by rw [dist_comm, ← hv6]; exact le_of_lt (hd2u 4)⟩
      ⟨hd2l 0, le_of_lt (hd2u 0)⟩
  rw [dist_zero_left, dist_zero_left, dist_zero_left] at hpos
  exact le_of_lt hpos

end Kepler.Text
