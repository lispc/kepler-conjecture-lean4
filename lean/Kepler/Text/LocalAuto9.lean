/-
Kepler.Text.LocalAuto9 — Local Fan chapter, three-file bundle (skeleton pass):
`HDPLYGY.hl` (1844 ln, 14 defs + 26 thms), `NKEZBFC.hl` (2618 ln, 8 defs +
29 thms), `PCRTTID.hl` (367 ln, 9 defs + 6 thms). Persistent HOL copies:
`lean/scripts/local/{HDPLYGY,NKEZBFC,PCRTTID}.hl`.

File map
* Section 1 (HDPLYGY, Hdplygy.hl):
  - ear constants `a_ear0`/`b_ear0` (Hdplygy.hl:35-41);
  - `MOD_EQ_MOD1`/`MOD_EQ_MOD` (Hdplygy.hl:43-74, proved);
  - the `stable_sy` record lane (Hdplygy.hl:198-238): `exist_stable_system`,
    `stable_sy_tybij` (type definition), projections `k_sy..f_sy`,
    `stable_sy_lemma`, `ear_sy`, `sigma_sy`, `J1_SY`, `d_fun`, `tau_star`;
  - `EAR_STABLE_SYSTEM` (Hdplygy.hl:76-195);
  - finite/continuity/injectivity chain over `B_SY1`:
    `FINITE_J_SY`, `FINITE_J1_SY`, `CONTINUOUS_ON_ROW`, `INDEX_J1_SY`,
    `CONTINUOUS_ON_D_FUN`, `INJ_B_SY`, `INJ_ROW_B_SY`, `CHANGE_SUM_TAU_FUN`,
    `CONTINUOUS_ON_SAME_DOMAIN`, `EDGE_IN_F_SY`, `JBDNJJB3`,
    `SEQUENTIALLY_DIVH`, `COLLINEAR_B_SY`, `COLLINEAR_AZIM_CYCLE_B_SY`,
    `AZIM_EQ_DIHV_IN_B_SY`, `CONTINUOUS_ON_RHO_FUN_AND_AZIM`,
    `CONTINUOUS_ON_TAU_FUN`, `CONTINUOUS_ON_TAU_STAR`, `MINIMUM_IN_B_SY`,
    `HDPLYGY`.
* Section 2 (NKEZBFC, Nkezbfc.hl): `sol_local` (+ deprecated `sol_local_fan`),
  the local-fan inangle/solid-angle kit, the `aff_ge`/`aff_gt`/`wedge`
  coefficient kit, `order`/`slicev`/`slicee`/`slicef`, `rho_fun`/`tau_fun`,
  the two `lemma`s, `ORDER`/`UNIQUE_ORDER`, the compatible-slice pair
  `COMPATIBLE_BW_TWO_LEMMAS(2)`, `EJRCFJD_concl` and `NKEZBFC_PREP`.
* Section 3 (PCRTTID, Pcrttid.hl): the `tri_sy` record lane (`tri_stable`,
  `tri_sy_tybij`, `k_ts..f_ts`), `EAR_TRI_STABLE_SYSTEM`,
  `exist_tri_stable`, `augmented_constraint_system1`, and the
  closed/bounded/compact kit `CLOSED_TRI_SY`, `BOUNDED_TRI_SY`,
  `COMPACT_TRI_STABLE`, `PCRTTID`.

Encoding (HOL → Lean), following LocalAuto1 (`ScsV39` precedent) and
LocalAuto4 (`FinVec`/`vecmatsV3_p4` precedent):
- HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `0`; darts `V3 × V3`.
- HOL `real^(M,3)finite_product` (with `dimindex(:M) = m`) ↔ `FinVec m 3 =
  Fin (m * 3) → ℝ`; HOL 1-based `row i (vecmats l)` ↔ `rowV3_p9 l i`
  (0-based `Fin m` index `i-1`, junk value `0` off-range), the V3-valued row
  with the Euclidean norm.
- HOL `stable_sy` / `tri_sy` (`new_type_definition` over the 7-tuples
  `(k,d,s,a,b,J,f)`) ↔ the proof-carrying structures `StableSyP9`/`TriSyP9`;
  the projections `k_sy..f_sy`/`k_ts..f_ts` are the structure fields, so
  `*_tybij` and the `*_explicit` destructors are definitional (`ScsV39`
  precedent), and `stable_sy_lemma`/`tri_sy_lemma` are `s.prop`.
- HOL `num->bool` index sets ↔ `Finset ℕ`; `((num->bool)->bool)` ↔
  `Finset (Finset ℕ)`; `J1_SY`'s set comprehension ↔ the filtered image
  `Finset` (same members). HOL `constraint_system`'s polymorphic `d` is
  instantiated at `ℝ` here (`#0.11`), so `torsor_p9`/`constraintSystem_p9`/
  `stableSystem_p9` are `_p9` copies of LocalAuto4's `torsor_p4`-kit with
  `d : ℝ`. NEEDS: dedup at merge.
- `B_SY1`/`CONDITION1_SY`/`CONDITION2_SY` get `_p9` copies at `ℕ` index type
  (the `a_sy`/`b_sy` shapes of the stable_sy lane), reusing LocalAuto4's
  `V_SY_p4`/`E_SY_p4`/`F_SY_p4`/`convexLocalFan_p4`; `V_SY (vecmats l)` ↔
  `V_SY_p4 (vecmatsV3_p4 l)`.
- The localization-layer vocabulary used by all three sources (`azim_in_fan`,
  `azim_cycle`, `EE`, `rho_node1`, `ivs_rho_node1`, `interior_angle1`,
  `wedge_in_fan_gt/ge`, `convex_local_fan`, `local_fan`, `generic`,
  `v_prime`, `e_prime`, `hypermap (HYP (vec 0, V, E))`, `slicev`/`slicee`/
  `slicef`, `order`) is the importable LocalAuto2 `_p2` kit (`azimInFan_p2`,
  `azimCycle_p2`, `EE_p2`, `rhoNode1_p2`, `ivsRhoNode1_p2`,
  `interiorAngle1_p2`, `wedgeInFanGt_p2`/`wedgeInFanGe_p2`,
  `convexLocalFan_p2`, `localFan_p2`, `generic_p2`, `vPrime_p2`, `ePrime_p2`,
  `IsHyp_p2`, `slicev_p2`/`slicee_p2`/`slicef_p2`, `order_p2`). The three
  sources' OWN defs (`rho_fun`, `tau_fun`, `sol_local`, the deprecated
  `sol_local_fan`, ...) still get `_p9` copies below (verbatim bodies,
  lane convention — cf. `wedgeGe_p2` duplicating `wedgeGe`), each with a
  NEEDS-dedup marker pointing at the identical importable twin.
- The dih2k-layer SY kit (`V_SY`/`E_SY`/`F_SY`/`convex_local_fan` over
  matrices, `ball_annulus`, `cstab`) is LocalAuto4's `V_SY_p4`/`E_SY_p4`/
  `F_SY_p4`/`convexLocalFan_p4` and PackingAuto2's `ballAnnulus`;
  `cstab` ↦ `cstab_p4` in the HDPLYGY/PCRTTID sections and `cstab_p2` in the
  NKEZBFC section (same value 3.01, per-lane lineage).
- HOL `sum S f` over a set ↔ `Kepler.Text.setSum` (junk 0 on infinite sets,
  PackingAuto2 convention); sums over the `Finset` `J1_SY`/numsegs use
  `Finset.sum`. HOL `lift o f continuous_on s` ↔ `ContinuousOn f s`.
- HOL `ITER n f` ↔ `f^[n]`; `order f x y` keeps the epsilon-choice junk
  convention (verbatim `_p9` copy of LocalAuto2 `order_p2`'s body).
- HOL `(v - x) cross (w - x)` ↔ `cross3_p9` (the repo
  `WithLp.toLp 2 (crossProduct …)` idiom, as in `polarFan_p2`).
- `hypermap (HYP (vec 0, V, E))` hypotheses of the slice theorems ↦
  `IsHyp_p2 0 V E HS` (LocalAuto2); `CARD` on finite sets ↔ `Finset.card` /
  `Set.ncard` as in the sources.
- `wedge`/`aff_gt`/`aff_ge`/`aff_lt`/`azim`/`dihV`/`collinear` ↔ Kepler.Geom
  `wedge`/`affGt`/`affGe`/`affLt`/`azim`/`dihV` and Mathlib `Collinear ℝ`.
- Constants: `cstab`/`h0`/`sol0` ↦ `cstab_p2`/`cstab_p4` (LocalAuto2/4),
  `h0`/`sol0` (PackingAuto2); `#0.11` is the exact literal `11/100` rendered
  `0.11`; `ball_annulus` ↔ `ballAnnulus`.
- DISCHARGES convention: `sorry` bodies carry a `-- DISCHARGES:` marker with
  the blocking external item; mechanical proofs are discharged here.
- DEDUP (atn2-merge wave 3): NO code change here. `SphereKit` (reached via
  `LocalAuto2` → `PackingAuto20`) hosts only the sphere.hl numeric kit, so
  `torsor_p9`/`constraintSystem_p9`/`stableSystem_p9` (dih2k kit, deferred)
  and the `_p2` localization kit stay as-is (plan §3/§6); this file also
  consumes no atn2-family names. With the hub `atn2` clash resolved,
  `LocalAuto1` + `LocalAuto2` are co-importable again (dual-import probe
  verified 2026-09-18).
-/

import Kepler.Text.Polytope
import Kepler.Text.Fan
import Kepler.Text.PackingAuto2
import Kepler.Text.LocalAuto2
import Kepler.Text.LocalAuto4
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## Section 1: HDPLYGY (Hdplygy.hl) -/

/-! ### The ear constants (Hdplygy.hl:35-41) -/

/-- HOL `a_ear0 J (i,j)` (Hdplygy.hl:35); `J : (num->bool)->bool` ↦
`Finset (Finset ℕ)` (the stable_sy lane's `J_SY` shape). -/
noncomputable def aEar0_p9 (J : Finset (Finset ℕ)) (i j : ℕ) : ℝ :=
  if i % 3 = j % 3 then 0 else if {i % 3, j % 3} ∈ J then Real.sqrt 8 else 2

/-- HOL `b_ear0 J (i,j)` (Hdplygy.hl:39). -/
noncomputable def bEar0_p9 (J : Finset (Finset ℕ)) (i j : ℕ) : ℝ :=
  if i % 3 = j % 3 then 0 else if {i % 3, j % 3} ∈ J then cstab_p4 else 2 * h0

/-! ### MOD_EQ_MOD1 / MOD_EQ_MOD (Hdplygy.hl:43-74) -/

/-- HOL `MOD_EQ_MOD1` (Hdplygy.hl:43). -/
theorem MOD_EQ_MOD1_p9 {x1 x2 y n : ℕ} (_hn : n ≠ 0)
    (h : (y + x1) % n = (y + x2) % n) (_hle : x2 ≤ x1) : x1 % n = x2 % n := by
  have h' : x1 + y ≡ x2 + y [MOD n] := by
    show (x1 + y) % n = (x2 + y) % n
    rw [Nat.add_comm x1 y, Nat.add_comm x2 y]
    exact h
  exact Nat.ModEq.add_right_cancel' y h'

/-- HOL `MOD_EQ_MOD` (Hdplygy.hl:69). -/
theorem MOD_EQ_MOD_p9 {x1 x2 y n : ℕ} (hn : n ≠ 0)
    (h : (y + x1) % n = (y + x2) % n) : x1 % n = x2 % n := by
  rcases le_total x2 x1 with hle | hle
  · exact MOD_EQ_MOD1_p9 hn h hle
  · exact (MOD_EQ_MOD1_p9 hn h.symm hle).symm

/-! ### The stable-system kit (dih2k.hl:48-61; Hdplygy.hl:198-238)

`_p9` copies of LocalAuto4's `torsor_p4`/`constraintSystem_p4`/
`stableSystem_p4` with the constraint datum `d` at type `ℝ` (HDPLYGY's
`d_sy s = #0.11`). NEEDS: merge with LocalAuto4. -/

/-- HOL `torsor` (dih2k.hl:48), `Finset ℕ` instance. -/
def torsor_p9 (s : Finset ℕ) (k : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ x ∈ s, f x ∈ s) ∧ (∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂) ∧
    (∀ i x, 0 < i → i < k → x ∈ s → f^[i] x ≠ x) ∧
    (∀ x ∈ s, f^[k] x = x) ∧ s.card = k

/-- HOL `constraint_system` (dih2k.hl:52) with `d : ℝ`. -/
def constraintSystem_p9 (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  3 ≤ k ∧ k ≤ 6 ∧ torsor_p9 s k f ∧
    (∀ i j, a i j = a j i ∧ b i j = b j i ∧ a i j ≤ b i j) ∧
    (∀ i j, a i j = a i (f^[k] j) ∧ b i j = b i (f^[k] j)) ∧
    J ⊆ s.image (fun i => {i, f i}) ∧
    J.card + k ≤ 6

/-- HOL `stable_system` (dih2k.hl:61) with `d : ℝ`. -/
def stableSystem_p9 (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  constraintSystem_p9 k d s a b J f ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 ≤ a i j) ∧
    (∀ i ∈ s, a i i = 0 ∧ b i (f i) ≤ cstab_p4) ∧
    (∀ i j, {i, j} ∈ J → a i j = Real.sqrt 8 ∧ b i j = cstab_p4)

/-- The ear 3-cycle helper: three iterates of `i ↦ (1 + i) % 3` re-reduce
any natural to its residue (used for the `f POWER k` clauses of the ear
systems). -/
theorem iter3_ear_p9 (j : ℕ) : (fun i => (1 + i) % 3)^[3] j = j % 3 := by
  show (1 + (1 + (1 + j) % 3) % 3) % 3 = j % 3
  omega

/-- `a_ear0` only sees the residues: `a_ear0 J i (j % 3) = a_ear0 J i j`. -/
theorem aEar0_p9_mod (J : Finset (Finset ℕ)) (i j : ℕ) :
    aEar0_p9 J i (j % 3) = aEar0_p9 J i j := by
  unfold aEar0_p9
  have h3 : (j % 3) % 3 = j % 3 := Nat.mod_mod_of_dvd _ (Nat.dvd_refl 3)
  rw [h3]

/-! ### EAR_STABLE_SYSTEM (Hdplygy.hl:76-195) -/

/-- HOL `{{1,2}}` — the single residue-edge of the ear systems. -/
theorem earJ_mem_p9 {e : Finset ℕ}
    (h : e ∈ ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ))) :
    e = ({1, 2} : Finset ℕ) :=
  Finset.mem_singleton.mp h

/-- Numeric facts for the ear constants: `sqrt 8 ≤ cstab`, `2 ≤ 2 * h0`,
`2 * h0 ≤ cstab`, `2 ≤ sqrt 8`. -/
theorem ear_num_p9 :
    Real.sqrt 8 ≤ cstab_p4 ∧ (2:ℝ) ≤ 2 * h0 ∧ 2 * h0 ≤ cstab_p4 ∧
      (2:ℝ) ≤ Real.sqrt 8 := by
  have hc : cstab_p4 = 3.01 := rfl
  have hh : h0 = 1.26 := rfl
  refine ⟨?_, ?_, ?_, Real.le_sqrt_of_sq_le (by norm_num)⟩
  · rw [Real.sqrt_le_iff]; norm_num [hc]
  · norm_num [hh]
  · norm_num [hh, hc]

/-! ### The ear system lemmas (Hdplygy.hl:76-195) -/

/-- Ear 3-cycle on the index set `{0,1,2}`: closedness. -/
theorem ear_closed_p9 : ∀ x ∈ (Finset.Icc 0 2 : Finset ℕ), (1 + x) % 3 ∈ Finset.Icc 0 2 := by
  intro x hx
  simp only [Finset.mem_Icc] at hx ⊢
  omega

/-- Ear 3-cycle: injectivity on `{0,1,2}`. -/
theorem ear_inj_p9 : ∀ x₁ ∈ (Finset.Icc 0 2 : Finset ℕ), ∀ x₂ ∈ Finset.Icc 0 2,
    (1 + x₁) % 3 = (1 + x₂) % 3 → x₁ = x₂ := by
  intro x₁ hx₁ x₂ hx₂ hfx
  simp only [Finset.mem_Icc] at hx₁ hx₂
  omega

/-- Ear 3-cycle: no fixed points (first iterate). -/
theorem ear_nofix1_p9 : ∀ x ∈ (Finset.Icc 0 2 : Finset ℕ), (1 + x) % 3 ≠ x := by
  intro x hx
  simp only [Finset.mem_Icc] at hx
  omega

/-- Ear 3-cycle: no fixed points (second iterate). -/
theorem ear_nofix2_p9 : ∀ x ∈ (Finset.Icc 0 2 : Finset ℕ),
    (fun i => (1 + i) % 3)^[2] x ≠ x := by
  intro x hx
  simp only [Finset.mem_Icc] at hx
  show (1 + (1 + x) % 3) % 3 ≠ x
  omega

/-- Ear 3-cycle: period exactly 3 on `{0,1,2}`. -/
theorem ear_period_p9 : ∀ x ∈ (Finset.Icc 0 2 : Finset ℕ),
    (fun i => (1 + i) % 3)^[3] x = x := by
  intro x hx
  simp only [Finset.mem_Icc] at hx
  show (1 + (1 + (1 + x) % 3) % 3) % 3 = x
  omega

/-- Ear constants are symmetric with `a ≤ b`. -/
theorem ear_sym_p9 (i j : ℕ) :
    aEar0_p9 {{1, 2}} i j = aEar0_p9 {{1, 2}} j i ∧
      bEar0_p9 {{1, 2}} i j = bEar0_p9 {{1, 2}} j i ∧
      aEar0_p9 {{1, 2}} i j ≤ bEar0_p9 {{1, 2}} i j := by
  by_cases h : i % 3 = j % 3
  · simp only [aEar0_p9, bEar0_p9, h]
    norm_num
  · have h' : ¬(j % 3 = i % 3) := fun hh => h hh.symm
    by_cases hm : ({i % 3, j % 3} : Finset ℕ) ∈
        ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ))
    · have e1 := earJ_mem_p9 hm
      have e2 : ({j % 3, i % 3} : Finset ℕ) = {1, 2} := by
        ext t
        have he := Finset.ext_iff.mp e1 t
        simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
        omega
      have h2m : ({j % 3, i % 3} : Finset ℕ) ∈
          ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ)) :=
        Finset.mem_singleton.mpr e2
      simp only [aEar0_p9, bEar0_p9, if_neg h, if_neg h', if_pos hm, if_pos h2m,
        true_and]
      exact ear_num_p9.1
    · have h2n : ¬(({j % 3, i % 3} : Finset ℕ) ∈
          ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ))) := by
        intro h2m
        have e2 := earJ_mem_p9 h2m
        have e1 : ({i % 3, j % 3} : Finset ℕ) = {1, 2} := by
          ext t
          have he := Finset.ext_iff.mp e2 t
          simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
          omega
        exact hm (Finset.mem_singleton.mpr e1)
      simp only [aEar0_p9, bEar0_p9, if_neg h, if_neg h', if_neg hm, if_neg h2n,
        true_and]
      exact ear_num_p9.2.1

/-- Ear constants see residues only: `b_ear0` version. -/
theorem bEar0_p9_mod (J : Finset (Finset ℕ)) (i j : ℕ) :
    bEar0_p9 J i (j % 3) = bEar0_p9 J i j := by
  unfold bEar0_p9
  have h3 : (j % 3) % 3 = j % 3 := Nat.mod_mod_of_dvd _ (Nat.dvd_refl 3)
  rw [h3]

/-- Ear constants are 3-periodic along the cycle map. -/
theorem ear_period_ab_p9 (i j : ℕ) :
    aEar0_p9 {{1, 2}} i j = aEar0_p9 {{1, 2}} i ((fun n => (1 + n) % 3)^[3] j) ∧
      bEar0_p9 {{1, 2}} i j = bEar0_p9 {{1, 2}} i ((fun n => (1 + n) % 3)^[3] j) := by
  rw [iter3_ear_p9, aEar0_p9_mod, bEar0_p9_mod]
  exact ⟨rfl, rfl⟩

/-- The ear edge set sits under the image clause of `constraint_system`. -/
theorem ear_subset_p9 :
    ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ)) ⊆
      (Finset.Icc 0 2).image (fun i => ({i, (1 + i) % 3} : Finset ℕ)) := by
  intro e he
  rw [earJ_mem_p9 he]
  refine Finset.mem_image.mpr ⟨1, by simp [Finset.mem_Icc], ?_⟩
  decide

/-- `CARD J + k <= 6` for the ear system. -/
theorem ear_card_p9 :
    ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ)).card + 3 ≤ 6 := by simp

/-- Off-diagonal lower bounds of the ear system. -/
theorem ear_ge2_p9 : ∀ i ∈ (Finset.Icc 0 2 : Finset ℕ), ∀ j ∈ Finset.Icc 0 2,
    i ≠ j → 2 ≤ aEar0_p9 {{1, 2}} i j := by
  intro i hi j hj hij
  simp only [Finset.mem_Icc] at hi hj
  simp only [aEar0_p9]
  split_ifs with hc hm
  · exact absurd (by omega : i = j) hij
  · exact ear_num_p9.2.2.2
  · exact le_refl 2

/-- Diagonal row bounds of the ear system. -/
theorem ear_diag_p9 : ∀ i ∈ (Finset.Icc 0 2 : Finset ℕ),
    aEar0_p9 {{1, 2}} i i = 0 ∧
      bEar0_p9 {{1, 2}} i ((1 + i) % 3) ≤ cstab_p4 := by
  intro i hi
  rcases Finset.mem_Icc.mp hi with ⟨hi0, hi1⟩
  have h3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h3 with rfl | rfl | rfl
  · refine ⟨rfl, ?_⟩
    show bEar0_p9 {{1, 2}} 0 1 ≤ cstab_p4
    unfold bEar0_p9
    rw [if_neg (by decide : ¬((0:ℕ) % 3 = (1:ℕ) % 3)), if_neg (by decide)]
    exact ear_num_p9.2.2.1
  · refine ⟨rfl, ?_⟩
    show bEar0_p9 {{1, 2}} 1 2 ≤ cstab_p4
    unfold bEar0_p9
    rw [if_neg (by decide : ¬((1:ℕ) % 3 = (2:ℕ) % 3)),
      if_pos (by decide : ({1 % 3, 2 % 3} : Finset ℕ) ∈ {{1, 2}})]
  · refine ⟨rfl, ?_⟩
    show bEar0_p9 {{1, 2}} 2 0 ≤ cstab_p4
    unfold bEar0_p9
    rw [if_neg (by decide : ¬((2:ℕ) % 3 = (0:ℕ) % 3)),
      if_neg (by decide : ¬(({2 % 3, 0 % 3} : Finset ℕ) ∈ {{1, 2}}))]
    exact ear_num_p9.2.2.1

/-- The `J`-clause of the ear system. -/
theorem ear_J_p9 : ∀ i j : ℕ, ({i, j} : Finset ℕ) ∈
    ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ)) →
      aEar0_p9 {{1, 2}} i j = Real.sqrt 8 ∧ bEar0_p9 {{1, 2}} i j = cstab_p4 := by
  intro i j he
  have e := earJ_mem_p9 he
  have h1 : i ∈ ({1, 2} : Finset ℕ) := by rw [← e]; simp
  have h2 : j ∈ ({1, 2} : Finset ℕ) := by rw [← e]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact absurd e (by decide)
  · simp only [aEar0_p9, bEar0_p9,
      if_neg (show ¬((1:ℕ) % 3 = (2:ℕ) % 3) by omega),
      if_pos (show ({1 % 3, 2 % 3} : Finset ℕ) ∈
        ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ)) by decide)]
    exact ⟨trivial, trivial⟩
  · simp only [aEar0_p9, bEar0_p9,
      if_neg (show ¬((2:ℕ) % 3 = (1:ℕ) % 3) by omega),
      if_pos (show ({2 % 3, 1 % 3} : Finset ℕ) ∈
        ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ)) by decide)]
    exact ⟨trivial, trivial⟩
  · exact absurd e (by decide)

/-- HOL `EAR_STABLE_SYSTEM` (Hdplygy.hl:76): the ear triple
`stable_system 3 (#0.11) (0..2) (a_ear0 {{1,2}}) (b_ear0 {{1,2}}) {{1,2}}
(\i. (1+i) MOD 3)`. -/
theorem EAR_STABLE_SYSTEM_p9 :
    stableSystem_p9 3 0.11 (Finset.Icc 0 2)
      (aEar0_p9 {{1, 2}}) (bEar0_p9 {{1, 2}})
      {{1, 2}} (fun i => (1 + i) % 3) := by
  refine ⟨?_, ear_ge2_p9, ear_diag_p9, ear_J_p9⟩
  refine ⟨by norm_num, by norm_num, ?_, ear_sym_p9, ear_period_ab_p9,
    ear_subset_p9, ear_card_p9⟩
  refine ⟨ear_closed_p9, ear_inj_p9, ?_, ear_period_p9, ?_⟩
  · intro i x _ hi hx
    interval_cases i
    · exact ear_nofix1_p9 x hx
    · exact ear_nofix2_p9 x hx
  · simp

/-! ### rho_fun / tau_fun (dih2k.hl:44,46 = Nkezbfc.hl:1356,1359)

Ported here (section 1 needs them for `d_fun`/`tau_star`); also counted in
section 2. NEEDS: dedup with `rhoFun_p2`/`tauFun_p2` at merge. -/

/-- HOL `rho_fun` (dih2k.hl:44). -/
noncomputable def rhoFun_p9 (y : ℝ) : ℝ :=
  1 + (1 / (2 * h0 - 2)) * (1 / Real.pi) * sol0 * (y - 2)

/-- HOL `tau_fun` (dih2k.hl:46); `V` unused in the body (arity kept). -/
noncomputable def tauFun_p9 (V : Set V3) (E : Set (Set V3)) (f : Set (V3 × V3)) : ℝ :=
  setSum f (fun e => rhoFun_p9 ‖e.1‖ * azimInFan_p2 e E) -
    (Real.pi + sol0) * ((f.ncard - 2 : ℕ) : ℝ)

/-! ### The SY kit (dih2k.hl:70-122): rows, V/E/F, conditions, B_SY1 -/

/-- HOL `row i (vecmats l)`: the `i`-th row (1-based, junk value `0`
off-range) of the matrix encoded by `l`, as a `V3` vector. -/
def rowV3_p9 {m : ℕ} (l : FinVec m 3) (i : ℕ) : V3 :=
  if h : 1 ≤ i ∧ i ≤ m then vecmatsV3_p4 l ⟨i - 1, by omega⟩ else 0

theorem continuous_vecmatsV3_p4 {m : ℕ} (j : Fin m) :
    Continuous (fun l : FinVec m 3 => vecmatsV3_p4 l j) := by
  unfold vecmatsV3_p4 vecmats_p4
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun _ => continuous_apply _)

theorem continuous_rowV3_p9 {m : ℕ} (i : ℕ) :
    Continuous (fun l : FinVec m 3 => rowV3_p9 l i) := by
  unfold rowV3_p9
  split_ifs with h
  · exact continuous_vecmatsV3_p4 _
  · exact continuous_const

/-- HOL `B_SY1` (dih2k.hl:122): `{vecmats v | rows v in ball_annulus ∧
CONDITION1_SY a b v ∧ CONDITION2_SY v}`. Since `vecmats ∘ matvec = id`
(`MATVEC_VECMATS_ID`), the image set equals the set of flattenings `l`
whose matrix `vecmats l` satisfies the three clauses — that set is used
here (row conditions via `rowV3_p9`). -/
def B_SY1_p9 (m : ℕ) (a b : ℕ → ℕ → ℝ) : Set (FinVec m 3) :=
  {l | (∀ j : Fin m, vecmatsV3_p4 l j ∈ ballAnnulus) ∧
    (∀ i j : ℕ, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m →
      a i j ≤ ‖rowV3_p9 l i - rowV3_p9 l j‖ ∧
        ‖rowV3_p9 l i - rowV3_p9 l j‖ ≤ b i j) ∧
    convexLocalFan_p4 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (F_SY_p4 (vecmatsV3_p4 l))}

/-! ### The stable_sy record lane (Hdplygy.hl:198-238) -/

/-- HOL `stable_sy` (Hdplygy.hl:204): the `new_type_definition` over the
7-tuples `(k, d, s, a, b, J, f)` satisfying `stable_system`. Rendered as a
proof-carrying structure (`ScsV39` precedent); `tuple_stable_sy` is the
field tuple, so `stable_sy_tybij` and the seven `*_explicit` destructors
hold definitionally. -/
structure StableSyP9 where
  k_sy : ℕ
  d_sy : ℝ
  I_SY : Finset ℕ
  a_sy : ℕ → ℕ → ℝ
  b_sy : ℕ → ℕ → ℝ
  J_SY : Finset (Finset ℕ)
  f_sy : ℕ → ℕ
  prop : stableSystem_p9 k_sy d_sy I_SY a_sy b_sy J_SY f_sy

/-- HOL `exist_stable_system` (Hdplygy.hl:198), witnessed by the ear system. -/
theorem exist_stable_system_p9 :
    ∃ (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
      (J : Finset (Finset ℕ)), ∃ f : ℕ → ℕ, stableSystem_p9 k d s a b J f :=
  ⟨3, 0.11, Finset.Icc 0 2, aEar0_p9 {{1, 2}}, bEar0_p9 {{1, 2}},
    {{1, 2}}, fun i => (1 + i) % 3, EAR_STABLE_SYSTEM_p9⟩

/-- HOL `stable_sy_lemma` (Hdplygy.hl:224): every `stable_sy` satisfies
`stable_system` of its projections. -/
theorem stable_sy_lemma_p9 (s : StableSyP9) :
    stableSystem_p9 s.k_sy s.d_sy s.I_SY s.a_sy s.b_sy s.J_SY s.f_sy :=
  s.prop

/-- HOL `ear_sy` (Hdplygy.hl:228). -/
def ear_sy_p9 (s : StableSyP9) : Prop :=
  s.I_SY.card = 3 ∧ s.d_sy = 0.11 ∧ s.J_SY.card = 1 ∧
    s.a_sy = aEar0_p9 s.J_SY ∧ s.b_sy = bEar0_p9 s.J_SY

/-- HOL `sigma_sy` (Hdplygy.hl:232). -/
noncomputable def sigma_sy_p9 (s : StableSyP9) : ℝ :=
  if ear_sy_p9 s then 1 else -1

/-- HOL `J1_SY` (Hdplygy.hl:234): the set `{x | ∃ i, {i MOD k, f i MOD k} ∈
J ∧ i ∈ 1..k ∧ x = i, SUC (i MOD k)}`, rendered as the corresponding
filtered image `Finset` (same members; finiteness by construction). -/
def J1_SY_p9 (s : StableSyP9) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 s.k_sy).filter
      (fun i => {i % s.k_sy, s.f_sy (i % s.k_sy)} ∈ s.J_SY)).image
    (fun i => (i, i % s.k_sy + 1))

/-- HOL `d_fun` (Hdplygy.hl:236). -/
noncomputable def dFun_p9 (s : StableSyP9) {m : ℕ} (l : FinVec m 3) : ℝ :=
  s.d_sy + 0.1 * sigma_sy_p9 s *
    ∑ x ∈ J1_SY_p9 s,
      (cstab_p4 - ‖rowV3_p9 l x.1 - rowV3_p9 l x.2‖)

/-- HOL `tau_star` (Hdplygy.hl:238). -/
noncomputable def tauStar_p9 (s : StableSyP9) {m : ℕ} (l : FinVec m 3) : ℝ :=
  tauFun_p9 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (F_SY_p4 (vecmatsV3_p4 l)) - dFun_p9 s l

/-! ### HDPLYGY theorems (Hdplygy.hl:241-1841) -/

/-- HOL `FINITE_J_SY` (Hdplygy.hl:241). -/
theorem FINITE_J_SY_p9 (s : StableSyP9) : (s.J_SY : Set (Finset ℕ)).Finite :=
  s.J_SY.finite_toSet

/-- HOL `FINITE_J1_SY` (Hdplygy.hl:260). -/
theorem FINITE_J1_SY_p9 (s : StableSyP9) : (J1_SY_p9 s : Set (ℕ × ℕ)).Finite :=
  (J1_SY_p9 s).finite_toSet

/-- HOL `CONTINUOUS_ON_ROW` (Hdplygy.hl:272). -/
theorem CONTINUOUS_ON_ROW_p9 {m : ℕ} (i : ℕ) (S : Set (FinVec m 3)) :
    ContinuousOn (fun l : FinVec m 3 => rowV3_p9 l i) S :=
  (continuous_rowV3_p9 i).continuousOn

/-- HOL `INDEX_J1_SY` (Hdplygy.hl:291). -/
theorem INDEX_J1_SY_p9 (s : StableSyP9) {x : ℕ × ℕ} (hx : x ∈ J1_SY_p9 s) :
    1 ≤ x.1 ∧ x.1 ≤ s.k_sy := by
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  exact Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1

/-- HOL `CONTINUOUS_ON_D_FUN` (Hdplygy.hl:299). -/
theorem CONTINUOUS_ON_D_FUN_p9 (s : StableSyP9) (m : ℕ) :
    ContinuousOn (fun l : FinVec m 3 => dFun_p9 s l) (B_SY1_p9 m s.a_sy s.b_sy) := by
  have hc : Continuous (fun l : FinVec m 3 => dFun_p9 s l) := by
    unfold dFun_p9
    have hterms : ∀ x ∈ J1_SY_p9 s,
        Continuous (fun l : FinVec m 3 =>
          (cstab_p4 - ‖rowV3_p9 l x.1 - rowV3_p9 l x.2‖)) := fun x _ =>
      Continuous.sub continuous_const
        (((continuous_rowV3_p9 x.1).sub (continuous_rowV3_p9 x.2)).norm)
    refine Continuous.add continuous_const ?_
    refine Continuous.const_mul (continuous_finsetSum _ hterms) (0.1 * sigma_sy_p9 s)
  exact hc.continuousOn

/-- HOL `CONTINUOUS_ON_SAME_DOMAIN` (Hdplygy.hl:405). -/
theorem CONTINUOUS_ON_SAME_DOMAIN_p9 {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f g : α → β} {s : Set α} (h : ∀ x ∈ s, f x = g x)
    (hf : ContinuousOn f s) : ContinuousOn g s := by
  intro x hx
  exact (hf x hx).congr (fun y hy => (h y hy).symm) (h x hx).symm

/-- HOL `EDGE_IN_F_SY` (Hdplygy.hl:426). -/
theorem EDGE_IN_F_SY_p9 {m : ℕ} (l : FinVec m 3) (i : ℕ) (hi : 1 ≤ i ∧ i ≤ m)
    (u v : V3) (hu : u = rowV3_p9 l i) (hv : v = rowV3_p9 l (i % m + 1)) :
    (u, v) ∈ F_SY_p4 (vecmatsV3_p4 l) := by
  rw [hu, hv]
  have him : i % m < m := Nat.mod_lt _ (by omega)
  have hi2 : 1 ≤ i % m + 1 ∧ i % m + 1 ≤ m := by omega
  refine ⟨⟨i - 1, by omega⟩, Set.mem_univ _, ?_⟩
  simp only [rowV3_p9, dif_pos hi, dif_pos hi2, finNext]
  congr 1
  refine congrArg (vecmatsV3_p4 l) (Fin.ext ?_)
  have hi3 : i - 1 + 1 = i := by omega
  simp only [hi3]
  omega

/-- HOL `(u) cross (w)`: the vector cross product on `V3`
(the `polarFan_p2` idiom). -/
noncomputable def cross3_p9 (u w : V3) : V3 :=
  WithLp.toLp 2 (crossProduct ((u : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ))

/-- HOL `u dot w` on `real^3`. -/
noncomputable def dot3_p9 (u w : V3) : ℝ :=
  ((u : V3) : Fin 3 → ℝ) ⬝ᵥ ((w : V3) : Fin 3 → ℝ)

/-- HOL `JBDNJJB3` (Hdplygy.hl:437): the sine-of-azimuth / cross-dot
identity. Giant — blocked on the `e1_fan`/`e2_fan`/`e3_fan` orthonormal
frame kit (Trigonometry) not yet ported. -/
theorem JBDNJJB3_p9 (u v w : V3)
    (_h1 : ¬ Collinear ℝ ({0, u, v} : Set V3))
    (_h2 : ¬ Collinear ℝ ({0, u, w} : Set V3)) :
    Real.sin (azim 0 u v w) =
      dot3_p9 (cross3_p9 u v) w /
        (Real.sqrt (‖w‖ ^ 2 - (‖u‖⁻¹ * dot3_p9 u w) ^ 2) * ‖cross3_p9 u v‖) := by
  sorry

/-- HOL `SEQUENTIALLY_DIVH` (Hdplygy.hl:594): the dihedral angle is
sequentially continuous away from collinear triples. Giant. -/
theorem SEQUENTIALLY_DIVH_p9 (f g h : ℕ → V3) (a b c : V3)
    (hf : Filter.Tendsto f Filter.atTop (nhds a))
    (hg : Filter.Tendsto g Filter.atTop (nhds b))
    (hh : Filter.Tendsto h Filter.atTop (nhds c))
    (_hab : ¬ Collinear ℝ ({0, a, b} : Set V3))
    (_hac : ¬ Collinear ℝ ({0, a, c} : Set V3))
    (_hn : ∀ n : ℕ, ¬ Collinear ℝ ({0, f n, g n} : Set V3) ∧
      ¬ Collinear ℝ ({0, f n, h n} : Set V3)) :
    Filter.Tendsto (fun n => dihV 0 (f n) (g n) (h n)) Filter.atTop
      (nhds (dihV 0 a b c)) := by
  sorry

/-- The index hypothesis shape shared by the B_SY1 chain (HOL
`k_sy s = k /\ dimindex(:M) = k /\ I_SY s = 0..k-1 /\ f_sy s = (\i. (1+i) MOD k)`. -/
def StableSysHyp_p9 (s : StableSyP9) (m : ℕ) : Prop :=
  s.k_sy = m ∧ s.I_SY = Finset.Icc 0 (m - 1) ∧
    s.f_sy = (fun i => (1 + i) % m) ∧ 2 < m

/-- HOL `INJ_B_SY` (Hdplygy.hl:334) — needs `PROPERTIES_OF_FAN_IN_B_SY`
(WJSCPRO lane). DISCHARGES: from `PROPERTIES_OF_FAN_IN_B_SY`. -/
theorem INJ_B_SY_p9 (s : StableSyP9) {m : ℕ} (hm : StableSysHyp_p9 s m)
    (l : FinVec m 3) (hl : l ∈ B_SY1_p9 m s.a_sy s.b_sy) :
    ∀ i j : ℕ, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m →
      (rowV3_p9 l i, rowV3_p9 l (i % m + 1)) =
        (rowV3_p9 l j, rowV3_p9 l (j % m + 1)) → i = j := by
  sorry

/-- HOL `INJ_ROW_B_SY` (Hdplygy.hl:351). DISCHARGES: from
`PROPERTIES_OF_FAN_IN_B_SY` (WJSCPRO lane). -/
theorem INJ_ROW_B_SY_p9 (s : StableSyP9) {m : ℕ} (hm : StableSysHyp_p9 s m)
    (l : FinVec m 3) (hl : l ∈ B_SY1_p9 m s.a_sy s.b_sy) :
    ∀ i j : ℕ, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m →
      rowV3_p9 l i = rowV3_p9 l j → i = j := by
  sorry

/-- HOL `CHANGE_SUM_TAU_FUN` (Hdplygy.hl:370): the `F_SY`-sum of
`rho_fun * azim_in_fan` re-indexed over `1..k_sy s` by `INJ_B_SY`.
DISCHARGES: from `INJ_B_SY_p9` (proved) once `PROPERTIES_OF_FAN_IN_B_SY`
lands. -/
theorem CHANGE_SUM_TAU_FUN_p9 (s : StableSyP9) {m : ℕ}
    (hm : StableSysHyp_p9 s m) (l : FinVec m 3)
    (hl : l ∈ B_SY1_p9 m s.a_sy s.b_sy) :
    setSum (F_SY_p4 (vecmatsV3_p4 l))
        (fun e => rhoFun_p9 ‖e.1‖ * azimInFan_p2 e (E_SY_p4 (vecmatsV3_p4 l))) =
      ∑ i ∈ Finset.Icc 1 s.k_sy,
        rhoFun_p9 ‖rowV3_p9 l i‖ *
          azimInFan_p2 (rowV3_p9 l i, rowV3_p9 l (i % s.k_sy + 1))
            (E_SY_p4 (vecmatsV3_p4 l)) := by
  sorry

/-- HOL `COLLINEAR_B_SY` (Hdplygy.hl:1441). DISCHARGES: needs `remark1_fan`
(`Local_lemmas`). -/
theorem COLLINEAR_B_SY_p9 (s : StableSyP9) {m : ℕ} (hm : StableSysHyp_p9 s m)
    (l : FinVec m 3) (hl : l ∈ B_SY1_p9 m s.a_sy s.b_sy) (i : ℕ)
    (hi : 1 ≤ i ∧ i ≤ m) :
    ¬ Collinear ℝ ({0, rowV3_p9 l i, rowV3_p9 l (i % s.k_sy + 1)} : Set V3) := by
  sorry

/-- HOL `COLLINEAR_AZIM_CYCLE_B_SY` (Hdplygy.hl:1458). DISCHARGES: needs
`AZIM_CYCLE_EQ_SIGMA_FAN` + `sigma_fan_in_set_of_edge` + `remark1_fan`. -/
theorem COLLINEAR_AZIM_CYCLE_B_SY_p9 (s : StableSyP9) {m : ℕ}
    (hm : StableSysHyp_p9 s m) (l : FinVec m 3)
    (hl : l ∈ B_SY1_p9 m s.a_sy s.b_sy) (i : ℕ) (hi : 1 ≤ i ∧ i ≤ m) :
    ¬ Collinear ℝ ({0, rowV3_p9 l i,
        azimCycle_p2 (EE_p2 (rowV3_p9 l i) (E_SY_p4 (vecmatsV3_p4 l))) 0
          (rowV3_p9 l i) (rowV3_p9 l (i % s.k_sy + 1))} : Set V3) := by
  sorry

/-- HOL `AZIM_EQ_DIHV_IN_B_SY` (Hdplygy.hl:1484). DISCHARGES: needs
`LOFA_DETERMINE_AZIM_IN_FA` + `AZIM_LE_PI_EQ_DIHV` (`Local_lemmas`). -/
theorem AZIM_EQ_DIHV_IN_B_SY_p9 (s : StableSyP9) {m : ℕ}
    (hm : StableSysHyp_p9 s m) (l : FinVec m 3) (i : ℕ) (hi : 1 ≤ i ∧ i ≤ m)
    (u v w : V3) (hu : u = rowV3_p9 l i) (hv : v = rowV3_p9 l (i % s.k_sy + 1))
    (hw : w = azimCycle_p2 (EE_p2 u (E_SY_p4 (vecmatsV3_p4 l))) 0 u v)
    (hl : l ∈ B_SY1_p9 m s.a_sy s.b_sy) :
    azim 0 u v w = dihV 0 u v w := by
  sorry

/-- HOL `CONTINUOUS_ON_RHO_FUN_AND_AZIM` (Hdplygy.hl:1534) — giant
continuity of the azim_in_fan family. DISCHARGES: from the
azim_in_fan continuity kit (not yet ported). -/
theorem CONTINUOUS_ON_RHO_FUN_AND_AZIM_p9 (s : StableSyP9) {m : ℕ}
    (hm : StableSysHyp_p9 s m) :
    ContinuousOn (fun l : FinVec m 3 => ∑ i ∈ Finset.Icc 1 s.k_sy,
        rhoFun_p9 ‖rowV3_p9 l i‖ *
          azimInFan_p2 (rowV3_p9 l i, rowV3_p9 l (i % s.k_sy + 1))
            (E_SY_p4 (vecmatsV3_p4 l)))
      (B_SY1_p9 m s.a_sy s.b_sy) := by
  sorry

/-- HOL `CONTINUOUS_ON_TAU_FUN` (Hdplygy.hl:1771). DISCHARGES: from
`CONTINUOUS_ON_RHO_FUN_AND_AZIM_p9` + `CHANGE_SUM_TAU_FUN_p9` +
`CARD_F_SY_EQ`. -/
theorem CONTINUOUS_ON_TAU_FUN_p9 (s : StableSyP9) {m : ℕ}
    (hm : StableSysHyp_p9 s m) :
    ContinuousOn (fun l : FinVec m 3 => tauFun_p9 (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)))
      (B_SY1_p9 m s.a_sy s.b_sy) := by
  sorry

/-- HOL `CONTINUOUS_ON_TAU_STAR` (Hdplygy.hl:1805): `tau_star` is the
difference of the two continuous terms. -/
theorem CONTINUOUS_ON_TAU_STAR_p9 (s : StableSyP9) {m : ℕ}
    (hm : StableSysHyp_p9 s m) :
    ContinuousOn (fun l : FinVec m 3 => tauStar_p9 s l)
      (B_SY1_p9 m s.a_sy s.b_sy) :=
  (CONTINUOUS_ON_TAU_FUN_p9 s hm).sub (CONTINUOUS_ON_D_FUN_p9 s m)

/-- HOL `MINIMUM_IN_B_SY` (Hdplygy.hl:1814): `tau_star` attains its minimum
on `B_SY1` (HOL: `CONTINUOUS_ATTAINS_INF` + `WJSCPRO` compactness).
DISCHARGES: from the compactness of `B_SY1` (WJSCPRO; cf. `PCRTTID_p9`). -/
theorem MINIMUM_IN_B_SY_p9 (s : StableSyP9) {m : ℕ} (hm : StableSysHyp_p9 s m)
    (hne : (B_SY1_p9 m s.a_sy s.b_sy).Nonempty) :
    ∃ x ∈ B_SY1_p9 m s.a_sy s.b_sy, ∀ y ∈ B_SY1_p9 m s.a_sy s.b_sy,
      tauStar_p9 s x ≤ tauStar_p9 s y := by
  sorry

/-- HOL `HDPLYGY` (Hdplygy.hl:1831), the chapter conclusion. -/
theorem HDPLYGY_p9 (s : StableSyP9) {m : ℕ} (hm : StableSysHyp_p9 s m)
    (hne : (B_SY1_p9 m s.a_sy s.b_sy).Nonempty) :
    ContinuousOn (fun l : FinVec m 3 => tauStar_p9 s l)
        (B_SY1_p9 m s.a_sy s.b_sy) ∧
      ∃ x ∈ B_SY1_p9 m s.a_sy s.b_sy, ∀ y ∈ B_SY1_p9 m s.a_sy s.b_sy,
        tauStar_p9 s x ≤ tauStar_p9 s y :=
  ⟨CONTINUOUS_ON_TAU_STAR_p9 s hm, MINIMUM_IN_B_SY_p9 s hm hne⟩

/-! ## Section 2: NKEZBFC (Nkezbfc.hl) -/

/-! ### NKEZBFC definitions (Nkezbfc.hl:33-1359) -/

/-- HOL `sol_local_fan` (Nkezbfc.hl:33, deprecated 2013-02-22 in the
source — kept verbatim; `V` unused in the body). -/
noncomputable def solLocalFan_p9 (_V : Set V3) (E : Set (Set V3))
    (f : Set (V3 × V3)) : ℝ :=
  2 * Real.pi + setSum f (fun e => azimInFan_p2 e E - Real.pi)

/-- HOL `sol_local` (Nkezbfc.hl:36). NEEDS: dedup with `solLocal_p2`. -/
noncomputable def solLocal_p9 (E : Set (Set V3)) (f : Set (V3 × V3)) : ℝ :=
  2 * Real.pi + setSum f (fun e => azimInFan_p2 e E - Real.pi)

/-- HOL `order f x y` (Nkezbfc.hl:1348): least iterate hitting `y`
(epsilon choice, junk value when absent). NEEDS: dedup with `order_p2`. -/
noncomputable def order_p9 {α : Type*} (f : α → α) (x y : α) : ℕ :=
  Classical.epsilon fun n => f^[n] x = y ∧ ∀ i, 0 < i → i < n → ¬(f^[i] x = y)

/-- HOL `slicev` (Nkezbfc.hl:1349); `0 <= n` vacuous for `ℕ`.
NEEDS: dedup with `slicev_p2`. -/
def slicev_p9 (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3) : Set V3 :=
  {u | ∃ n : ℕ, n ≤ order_p9 (rhoNode1_p2 FF) v w ∧ u = (rhoNode1_p2 FF)^[n] v}

/-- HOL `slicee` (Nkezbfc.hl:1351); `DELETE w` ↦ `u ≠ w`.
NEEDS: dedup with `slicee_p2`. -/
def slicee_p9 (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3) :
    Set (Set V3) :=
  {e | ∃ u, u ∈ slicev_p9 E FF v w ∧ u ≠ w ∧ e = {u, rhoNode1_p2 FF u}} ∪
    {{w, v}}

/-- HOL `slicef` (Nkezbfc.hl:1353). NEEDS: dedup with `slicef_p2`. -/
def slicef_p9 (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3) :
    Set (V3 × V3) :=
  {f | ∃ u, u ∈ slicev_p9 E FF v w ∧ u ≠ w ∧ f = (u, rhoNode1_p2 FF u)} ∪
    {(w, v)}

/-! ### NKEZBFC theorems (Nkezbfc.hl:39-2616)

`convex_local_fan` ↦ `convexLocalFan_p2` (LocalAuto2, the localization
lineage), `azim_in_fan` ↦ `azimInFan_p2`, `interior_angle1` ↦
`interiorAngle1_p2`, `rho_node1`/`ivs_rho_node1` ↦ `rhoNode1_p2`/
`ivsRhoNode1_p2`, `generic` ↦ `generic_p2`, `wedge_in_fan_gt` ↦
`wedgeInFanGt_p2`, `wedge` ↦ `Kepler.Geom.wedge`. -/

/-- HOL `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM` (Nkezbfc.hl:39). -/
theorem CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_p9 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) :
    ∀ v ∈ V, interiorAngle1_p2 0 FF v = azimInFan_p2 (v, rhoNode1_p2 FF v) E := by
  sorry

/-- HOL `SOL_LOFA_EQ_SUM_INANGLE` (Nkezbfc.hl:75). -/
theorem SOL_LOFA_EQ_SUM_INANGLE_p9 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) :
    solLocal_p9 E FF =
      2 * Real.pi + setSum V (fun v => interiorAngle1_p2 0 FF v - Real.pi) := by
  sorry

/-- HOL `CARD_VERTEX_GE_3_LOCAL_FAN` (Nkezbfc.hl:103). -/
theorem CARD_VERTEX_GE_3_LOCAL_FAN_p9 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) : 3 ≤ V.ncard := by
  sorry

/-- HOL `REP_VERTEX_3_LOCAL_FAN` (Nkezbfc.hl:157). -/
theorem REP_VERTEX_3_LOCAL_FAN_p9 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (hcard : V.ncard = 3) (h : convexLocalFan_p2 V E FF) :
    ∃ v : V3, V = {v, rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)} ∧
      v ≠ rhoNode1_p2 FF v ∧
      rhoNode1_p2 FF v ≠ rhoNode1_p2 FF (rhoNode1_p2 FF v) ∧
      rhoNode1_p2 FF (rhoNode1_p2 FF v) ≠ v := by
  sorry

/-- HOL `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS` (Nkezbfc.hl:214). -/
theorem CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS_p9 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) :
    ∀ v ∈ V, interiorAngle1_p2 0 FF v =
      azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) := by
  sorry

/-- HOL `SOL_LOCAL_FAN_POS_CASE3` (Nkezbfc.hl:248). -/
theorem SOL_LOCAL_FAN_POS_CASE3_p9 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) (hcard : V.ncard = 3) :
    0 ≤ solLocal_p9 E FF := by
  sorry

/-- HOL `AFF_LT_1_1` (Nkezbfc.hl:360). -/
theorem AFF_LT_1_1_p9 (x w : V3) (hxw : x ≠ w) :
    affLt {x} {w} =
      {y | ∃ t1 t2 : ℝ, t2 < 0 ∧ t1 + t2 = 1 ∧ y = t1 • x + t2 • w} := by
  sorry

/-- HOL `PROPERTIES_GENERIC_LOCAL_FAN` (Nkezbfc.hl:370). -/
theorem PROPERTIES_GENERIC_LOCAL_FAN_p9 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : localFan_p2 V E FF) (hv0 : ∀ v0 ∈ V, True)
    (hg : generic_p2 V E) (v0 : V3) (hv0V : v0 ∈ V) :
    ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3) := by
  sorry

/-- HOL `AZIM_PI_WEDGE_SIN` (Nkezbfc.hl:473). -/
theorem AZIM_PI_WEDGE_SIN_p9 (u v w ww : V3) (h : azim u v w ww = Real.pi) :
    wedge u v w ww = {x | 0 < Real.sin (azim u v w x)} := by
  sorry

/-- HOL `AZIM_PI_WEDGE_CROSS_DOT` (Nkezbfc.hl:517). -/
theorem AZIM_PI_WEDGE_CROSS_DOT_p9 (u v w ww : V3) (h : azim u v w ww = Real.pi) :
    wedge u v w ww = {x | 0 < dot3_p9 (cross3_p9 (v - u) (w - u)) (x - u)} := by
  sorry

/-- HOL `AFF_GT_SUBSET_WEDGE_IMP_VERTEX` (Nkezbfc.hl:530). -/
theorem AFF_GT_SUBSET_WEDGE_IMP_VERTEX_p9 (x v w y z : V3)
    (h1 : ¬ Collinear ℝ ({x, v, w} : Set V3))
    (h2 : ¬ Collinear ℝ ({x, v, y} : Set V3))
    (h3 : ¬ Collinear ℝ ({x, v, z} : Set V3))
    (h4 : affGt {x} {v, w} ⊆ wedge x v y z) :
    w ∈ wedge x v y z := by
  sorry

/-- HOL `CONDITION_INANGLE_CROSS_DOT` (Nkezbfc.hl:548). -/
theorem CONDITION_INANGLE_CROSS_DOT_p9 (x v w y z : V3)
    (h1 : affGt {x} {v, w} ⊆ wedge x v y z)
    (h2 : ¬ Collinear ℝ ({x, v, w} : Set V3))
    (h3 : ¬ Collinear ℝ ({x, v, y} : Set V3))
    (h4 : ¬ Collinear ℝ ({x, v, z} : Set V3))
    (h5 : azim x v y z < Real.pi) :
    0 < dot3_p9 (cross3_p9 (v - x) (y - x)) (w - x) ∧
      0 < dot3_p9 (cross3_p9 (v - x) (w - x)) (z - x) := by
  sorry

/-- HOL `AFF_GE_3_1` (Nkezbfc.hl:587). -/
theorem AFF_GE_3_1_p9 (x v u w : V3) (hd : Disjoint ({x, v, u} : Set V3) {w}) :
    affGe {x, v, u} {w} =
      {y | ∃ t1 t2 t3 t4 : ℝ, 0 ≤ t4 ∧ t1 + t2 + t3 + t4 = 1 ∧
        y = t1 • x + t2 • v + t3 • u + t4 • w} := by
  sorry

/-- HOL `AFF_GE_2_2` (Nkezbfc.hl:598). -/
theorem AFF_GE_2_2_p9 (x u v w : V3) (hd : Disjoint ({x, u} : Set V3) {v, w}) :
    affGe {x, u} {v, w} =
      {y | ∃ t1 t2 t3 t4 : ℝ, 0 ≤ t3 ∧ 0 ≤ t4 ∧ t1 + t2 + t3 + t4 = 1 ∧
        y = t1 • x + t2 • u + t3 • v + t4 • w} := by
  sorry

/-- HOL `inter_aff_ge_3_1_is_aff_ge_2_2` (Nkezbfc.hl:610). -/
theorem inter_aff_ge_3_1_is_aff_ge_2_2_p9 (x v u w : V3)
    (h : ¬ Coplanar ℝ ({x, v, u, w} : Set V3)) :
    affGe {x, v, u} {w} ∩ affGe {x, u, w} {v} = affGe {x, u} {v, w} := by
  sorry

/-- HOL `aff_ge_3_1_rep_cross_dot` (Nkezbfc.hl:656). -/
theorem aff_ge_3_1_rep_cross_dot_p9 (x v u w : V3)
    (h : ¬ Coplanar ℝ ({x, v, u, w} : Set V3))
    (hd : 0 < dot3_p9 (cross3_p9 (v - x) (u - x)) (w - x)) :
    affGe {x, v, u} {w} = {y : V3 | 0 ≤ dot3_p9 (cross3_p9 (v - x) (u - x)) (y - x)} := by
  sorry

/-- HOL `PROPERTIES_AFF_GT_SUBSET_WEDGE` (Nkezbfc.hl:836). -/
theorem PROPERTIES_AFF_GT_SUBSET_WEDGE_p9 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) (v w : V3) (hv : v ∈ V)
    (hw : w ∈ V) (hvw : v ≠ w) (hg : generic_p2 V E)
    (ha : azimInFan_p2 (v, rhoNode1_p2 FF v) E < Real.pi)
    (hsub : affGt {0} {v, w} ⊆ wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E) :
    ∀ x ∈ FF, affGt {0} {v, w} ⊆ wedgeInFanGt_p2 x E := by
  sorry

/-- HOL `lemma` (Nkezbfc.hl:842). -/
theorem nkezLemma_p9 (A : Prop) : A ∨ ¬A := Classical.em A

/-- HOL `AFF_GE_SUBSET_AFF_GE_UNION` (Nkezbfc.hl:1236). -/
theorem AFF_GE_SUBSET_AFF_GE_UNION_p9 (x v u v1 : V3)
    (h1 : Disjoint ({x} : Set V3) {v, u})
    (h2 : Disjoint ({x} : Set V3) {v, v1})
    (h3 : Disjoint ({x} : Set V3) {v1, u})
    (h4 : v1 ∈ affGt {x} {v, u}) :
    affGe {x} {v, u} ⊆ affGe {x} {v, v1} ∪ affGe {x} {v1, u} := by
  sorry

/-- HOL `aff_ge_subset3_aff_ge` (Nkezbfc.hl:1298). -/
theorem aff_ge_subset3_aff_ge_p9 (x v u v1 : V3)
    (h1 : Disjoint ({x} : Set V3) {v, u})
    (h2 : Disjoint ({x} : Set V3) {v, v1})
    (h3 : v1 ∈ affGt {x} {v, u}) :
    affGe {x} {v, v1} ⊆ affGe {x} {v, u} := by
  sorry

/-- HOL `AFF_GE_EQ_AFF_GE_UNION` (Nkezbfc.hl:1326). -/
theorem AFF_GE_EQ_AFF_GE_UNION_p9 (x v u v1 : V3)
    (h1 : Disjoint ({x} : Set V3) {v, u})
    (h2 : Disjoint ({x} : Set V3) {v, v1})
    (h3 : Disjoint ({x} : Set V3) {v1, u})
    (h4 : v1 ∈ affGt {x} {v, u}) :
    affGe {x} {v, u} = affGe {x} {v, v1} ∪ affGe {x} {v1, u} := by
  sorry

/-- HOL `ORDER` (Nkezbfc.hl:1363). -/
theorem ORDER_p9 {α : Type*} (f : α → α) (x y : α) (n : ℕ)
    (h : f^[n] x = y) (hmin : ∀ i, 0 < i → i < n → ¬(f^[i] x = y)) :
    f^[order_p9 f x y] x = y ∧
      ∀ i, 0 < i → i < order_p9 f x y → ¬(f^[i] x = y) := by
  have heps := Classical.epsilon_spec
    (p := fun k => f^[k] x = y ∧ ∀ i, 0 < i → i < k → ¬(f^[i] x = y))
    ⟨n, h, hmin⟩
  exact heps

/-- HOL `UNIQUE_ORDER` (Nkezbfc.hl:1374). -/
theorem UNIQUE_ORDER_p9 {α : Type*} (f : α → α) (x y : α) (n : ℕ)
    (h : f^[n] x = y) (hmin : ∀ i, 0 < i → i < n → ¬(f^[i] x = y))
    (hxy : ¬(x = y)) : order_p9 f x y = n := by
  have heps := Classical.epsilon_spec
    (p := fun k => f^[k] x = y ∧ ∀ i, 0 < i → i < k → ¬(f^[i] x = y))
    ⟨n, h, hmin⟩
  by_contra hne
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at h
      exact False.elim (hxy h)
    · exact h0
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hval : f^[(order_p9 f x y : ℕ)] x = y := heps.1
    rcases Nat.eq_zero_or_pos (order_p9 f x y) with h0 | h0
    · rw [h0] at hval
      exact False.elim (hxy hval)
    · exact absurd hval (hmin _ h0 hlt)
  · exact absurd h (heps.2 n hn0 hgt)

/-- HOL `lemma1` (Nkezbfc.hl:1708). -/
theorem nkezLemma1_p9 (A : Prop) : ¬A ∨ A := by
  rcases Classical.em A with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- HOL `EJRCFJD_concl` (Nkezbfc.hl:1685), the antecedent of
`NKEZBFC_PREP`; carried as a proposition (statement registry, per the
`*_concl` convention). -/
def EJRCFJD_concl_p9 : Prop :=
  ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3),
    convexLocalFan_p2 V E FF → v ∈ V → w ∈ V →
      (∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3)) →
      (∀ e ∈ FF, affGt {0} {v, w} ⊆ wedgeInFanGt_p2 e E) →
        convexLocalFan_p2 (slicev_p9 E FF v w) (slicee_p9 E FF v w)
            (slicef_p9 E FF v w) ∧
          convexLocalFan_p2 (slicev_p9 E FF w v) (slicee_p9 E FF w v)
              (slicef_p9 E FF w v) ∧
            tauFun_p9 V E FF ≥
                tauFun_p9 (slicev_p9 E FF v w) (slicee_p9 E FF v w)
                  (slicef_p9 E FF v w) +
                  tauFun_p9 (slicev_p9 E FF w v) (slicee_p9 E FF w v)
                    (slicef_p9 E FF w v) ∧
              solLocal_p9 E FF =
                  solLocal_p9 (slicee_p9 E FF v w) (slicef_p9 E FF v w) +
                    solLocal_p9 (slicee_p9 E FF w v) (slicef_p9 E FF w v) ∧
                (slicev_p9 E FF v w).ncard < V.ncard ∧
                  (slicev_p9 E FF w v).ncard < V.ncard ∧
                    (generic_p2 V E →
                      generic_p2 (slicev_p9 E FF v w) (slicee_p9 E FF v w) ∧
                        generic_p2 (slicev_p9 E FF w v) (slicee_p9 E FF w v))

/-- HOL `NKEZBFC_PREP` (Nkezbfc.hl:1718): `EJRCFJD_concl` implies the
non-negativity of `sol_local` for generic convex local fans. Giant
(900-line well-founded induction on `CARD V - 3`). -/
theorem NKEZBFC_PREP_p9 (h : EJRCFJD_concl_p9) :
    ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
      convexLocalFan_p2 V E FF → generic_p2 V E → 0 ≤ solLocal_p9 E FF := by
  sorry

/-- HOL `COMPATIBLE_BW_TWO_LEMMAS` (Nkezbfc.hl:1413). -/
theorem COMPATIBLE_BW_TWO_LEMMAS_p9 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) (v w : V3) (hv : v ∈ V)
    (hw : w ∈ V) (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt {0} {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : HS.face (v, rhoNode1_p2 FF v) = fv) :
    (vPrime_p2 V fv = slicev_p9 E FF v w) ∧
      (ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p9 E FF v w) ∧
      (fv = slicef_p9 E FF v w) := by
  sorry

/-! ## Section 3: PCRTTID (Pcrttid.hl) -/

/-! ### PCRTTID definitions (Pcrttid.hl:32-182) -/

/-- HOL `tri_stable` (Pcrttid.hl:32) with `d : ℝ`. Note the strict
`b (i, f i) < 4` (vs `stable_system`'s `≤ cstab`). -/
def triStable_p9 (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  constraintSystem_p9 k d s a b J f ∧ k = 3 ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 ≤ a i j) ∧
    (∀ i ∈ s, a i i = 0 ∧ b i (f i) < 4) ∧
    (∀ i j, {i, j} ∈ J → a i j = Real.sqrt 8 ∧ b i j = cstab_p4)

/-- HOL `tri_sy` (Pcrttid.hl:156): `new_type_definition` over the 7-tuples
satisfying `tri_stable`; same proof-carrying-structure rendering as
`StableSyP9` (so `tri_sy_tybij` and the `k_ts..f_ts` destructors are
definitional). -/
structure TriSyP9 where
  k_ts : ℕ
  d_ts : ℝ
  I_TS : Finset ℕ
  a_ts : ℕ → ℕ → ℝ
  b_ts : ℕ → ℕ → ℝ
  J_TS : Finset (Finset ℕ)
  f_ts : ℕ → ℕ
  prop : triStable_p9 k_ts d_ts I_TS a_ts b_ts J_TS f_ts

/-- HOL `augmented_constraint_system1` (Pcrttid.hl:174) over a
`stable_sy` record; the dummy flags `I_lo`/`I_str` are unused in the HOL
body and carried as `Prop`. -/
def augmentedConstraintSystem1_p9 (s : StableSyP9) (_I_lo _I_str : Prop)
    (a b : ℕ → ℕ → ℝ) (m : ℕ) : Prop :=
  s.d_sy ≤ 0.9 ∧
    m = ((s.I_SY.filter (fun i => ∃ j ∈ s.I_SY,
          2 < s.a_sy i j ∨ 2 * h0 < s.b_sy i j))).card / 2 ∧
    m + s.k_sy ≤ 6 ∧
    (∀ i ∈ s.I_SY, ∀ j ∈ s.I_SY,
      s.a_sy i j ≤ a i j ∧ a i j ≤ b i j ∧ b i j ≤ s.b_sy i j)

/-! ### PCRTTID theorems (Pcrttid.hl:42-359) -/

/-- The diagonal `b < 4` clauses of the ear tri-system. -/
theorem ear_diag_lt_p9 : ∀ i ∈ (Finset.Icc 0 2 : Finset ℕ),
    aEar0_p9 {{1, 2}} i i = 0 ∧ bEar0_p9 {{1, 2}} i ((1 + i) % 3) < 4 := by
  intro i hi
  rcases Finset.mem_Icc.mp hi with ⟨hi0, hi1⟩
  have h3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h3 with rfl | rfl | rfl
  · refine ⟨rfl, ?_⟩
    show bEar0_p9 {{1, 2}} 0 1 < 4
    unfold bEar0_p9
    rw [if_neg (by decide : ¬((0:ℕ) % 3 = (1:ℕ) % 3)), if_neg (by decide)]
    have hh : h0 = 1.26 := rfl
    norm_num [hh]
  · refine ⟨rfl, ?_⟩
    show bEar0_p9 {{1, 2}} 1 2 < 4
    unfold bEar0_p9
    rw [if_neg (by decide : ¬((1:ℕ) % 3 = (2:ℕ) % 3)),
      if_pos (by decide : ({1 % 3, 2 % 3} : Finset ℕ) ∈ {{1, 2}})]
    have hc : cstab_p4 = 3.01 := rfl
    norm_num [hc]
  · refine ⟨rfl, ?_⟩
    show bEar0_p9 {{1, 2}} 2 0 < 4
    unfold bEar0_p9
    rw [if_neg (by decide : ¬((2:ℕ) % 3 = (0:ℕ) % 3)),
      if_neg (by decide : ¬(({2 % 3, 0 % 3} : Finset ℕ) ∈ {{1, 2}}))]
    have hh : h0 = 1.26 := rfl
    norm_num [hh]

/-- HOL `EAR_TRI_STABLE_SYSTEM` (Pcrttid.hl:42). -/
theorem EAR_TRI_STABLE_SYSTEM_p9 :
    triStable_p9 3 0.11 (Finset.Icc 0 2) (aEar0_p9 {{1, 2}}) (bEar0_p9 {{1, 2}})
      {{1, 2}} (fun i => (1 + i) % 3) :=
  ⟨EAR_STABLE_SYSTEM_p9.1, rfl, ear_ge2_p9, ear_diag_lt_p9, ear_J_p9⟩

/-- HOL `exist_tri_stable` (Pcrttid.hl:150). -/
theorem exist_tri_stable_p9 :
    ∃ (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
      (J : Finset (Finset ℕ)), ∃ f : ℕ → ℕ, triStable_p9 k d s a b J f :=
  ⟨3, 0.11, Finset.Icc 0 2, aEar0_p9 {{1, 2}}, bEar0_p9 {{1, 2}},
    {{1, 2}}, fun i => (1 + i) % 3, EAR_TRI_STABLE_SYSTEM_p9⟩

/-- HOL `CONDITION2_SY` (dih2k.hl:88) at `ℕ` index type. -/
def CONDITION2_SY_p9 (k : ℕ) (l : FinVec k 3) : Prop :=
  convexLocalFan_p4 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
    (F_SY_p4 (vecmatsV3_p4 l))

/-- The B_SY1 body-set: HOL `{matvec v | rows v in ball_annulus ∧
CONDITION1_SY a b v}` (k = dimindex(:M)). -/
def BSY1body_p9 (k : ℕ) (a b : ℕ → ℕ → ℝ) : Set (FinVec k 3) :=
  {l | (∀ j : Fin k, vecmatsV3_p4 l j ∈ ballAnnulus) ∧
    ∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k →
      a i j ≤ ‖rowV3_p9 l i - rowV3_p9 l j‖ ∧
        ‖rowV3_p9 l i - rowV3_p9 l j‖ ≤ b i j}

/-- HOL `CLOSED_TRI_SY` (Pcrttid.hl:184); the `k = dimindex(:M)` clause is
absorbed by taking the ambient size to be `k`. -/
theorem CLOSED_TRI_SY_p9 {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ} (_h : triStable_p9 k d s a b J f) :
    IsClosed (BSY1body_p9 k a b) := by
  have hrows : IsClosed {l : FinVec k 3 | ∀ j : Fin k,
      vecmatsV3_p4 l j ∈ ballAnnulus} := by
    have hset : {l : FinVec k 3 | ∀ j : Fin k, vecmatsV3_p4 l j ∈ ballAnnulus}
        = {l : FinVec k 3 | ∀ j : Fin k,
            vecmats_p4 l j ∈
              ((WithLp.toLp (p := 2) (V := Fin 3 → ℝ)) ⁻¹' ballAnnulus :
                Set (Fin 3 → ℝ))} := rfl
    rw [hset]
    exact CLOSED_MATVEC _ (fun j =>
      (CLOSED_BALL_ANNULUS).preimage
        (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)))
  have hcond : IsClosed {l : FinVec k 3 | ∀ i j : ℕ, 1 ≤ i → i ≤ k →
      1 ≤ j → j ≤ k →
      a i j ≤ ‖rowV3_p9 l i - rowV3_p9 l j‖ ∧
        ‖rowV3_p9 l i - rowV3_p9 l j‖ ≤ b i j} := by
    have hset : {l : FinVec k 3 | ∀ i j : ℕ, 1 ≤ i → i ≤ k →
        1 ≤ j → j ≤ k →
        a i j ≤ ‖rowV3_p9 l i - rowV3_p9 l j‖ ∧
          ‖rowV3_p9 l i - rowV3_p9 l j‖ ≤ b i j}
        = ⋂ (p : ℕ × ℕ),
            {l : FinVec k 3 | (1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧ p.2 ≤ k) →
              (a p.1 p.2 ≤ ‖rowV3_p9 l p.1 - rowV3_p9 l p.2‖ ∧
                ‖rowV3_p9 l p.1 - rowV3_p9 l p.2‖ ≤ b p.1 p.2)} := by
      ext l
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h p hp => h p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2,
        fun h i j hi hj hjk hl => h (i, j) ⟨hi, hj, hjk, hl⟩⟩
    rw [hset]
    refine isClosed_iInter fun p => ?_
    by_cases hb : 1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧ p.2 ≤ k
    · have heq : {l : FinVec k 3 | (1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧ p.2 ≤ k) →
          (a p.1 p.2 ≤ ‖rowV3_p9 l p.1 - rowV3_p9 l p.2‖ ∧
            ‖rowV3_p9 l p.1 - rowV3_p9 l p.2‖ ≤ b p.1 p.2)}
          = {l : FinVec k 3 | a p.1 p.2 ≤ ‖rowV3_p9 l p.1 - rowV3_p9 l p.2‖ ∧
            ‖rowV3_p9 l p.1 - rowV3_p9 l p.2‖ ≤ b p.1 p.2} := by
        ext l
        simp [hb]
      rw [heq]
      exact isClosed_Icc.preimage
        (((continuous_rowV3_p9 p.1).sub (continuous_rowV3_p9 p.2)).norm)
    · have heq : {l : FinVec k 3 | (1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧ p.2 ≤ k) →
          (a p.1 p.2 ≤ ‖rowV3_p9 l p.1 - rowV3_p9 l p.2‖ ∧
            ‖rowV3_p9 l p.1 - rowV3_p9 l p.2‖ ≤ b p.1 p.2)} = Set.univ := by
        ext l
        simp [hb]
      rw [heq]
      exact isClosed_univ
  have hEq : BSY1body_p9 k a b =
      {l : FinVec k 3 | ∀ j : Fin k, vecmatsV3_p4 l j ∈ ballAnnulus} ∩
        {l : FinVec k 3 | ∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k →
          a i j ≤ ‖rowV3_p9 l i - rowV3_p9 l j‖ ∧
            ‖rowV3_p9 l i - rowV3_p9 l j‖ ≤ b i j} := by
    ext l
    simp only [BSY1body_p9, Set.mem_setOf_eq, Set.mem_inter_iff, and_self]
  rw [hEq]
  exact hrows.inter hcond


/-- HOL `BOUNDED_TRI_SY` (Pcrttid.hl:315). -/
theorem BOUNDED_TRI_SY_p9 {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ} (_h : triStable_p9 k d s a b J f) :
    Bornology.IsBounded (BSY1body_p9 k a b) := by
  refine Bornology.IsBounded.subset
    (t := Metric.closedBall (0 : FinVec k 3) (2 * h0))
    (Metric.isBounded_closedBall (r := 2 * h0)) ?_
  intro l hl
  have hrows : ∀ j : Fin k, vecmatsV3_p4 l j ∈ ballAnnulus := hl.1
  have hcoord : ∀ p : Fin (k * 3), |l p| ≤ 2 * h0 := by
    intro p
    have hj : (p : ℕ) / 3 < k := Nat.div_lt_of_lt_mul (by
      rw [Nat.mul_comm 3 k]
      exact p.isLt)
    have hc3 : (p : ℕ) % 3 < 3 := Nat.mod_lt _ (by omega)
    have hpe : ((finProdEquiv k 3 ⟨⟨(p:ℕ)/3, hj⟩, ⟨(p:ℕ)%3, hc3⟩⟩ : ℕ)) = (p : ℕ) := by
      have hdm := Nat.div_add_mod ((p : ℕ)) 3
      rw [finProdEquiv_val]
      show (p:ℕ) / 3 * 3 + (p:ℕ) % 3 = (p:ℕ)
      omega
    have hfin : (finProdEquiv k 3 ⟨⟨(p:ℕ)/3, hj⟩, ⟨(p:ℕ)%3, hc3⟩⟩ : Fin (k*3)) = p :=
      Fin.ext hpe
    have hvm : vecmats_p4 l ⟨(p:ℕ)/3, hj⟩ ⟨(p:ℕ)%3, hc3⟩ = l p := by
      show l (finProdEquiv k 3 ⟨⟨(p:ℕ)/3, hj⟩, ⟨(p:ℕ)%3, hc3⟩⟩) = l p
      rw [hfin]
    have hv : vecmatsV3_p4 l ⟨(p:ℕ)/3, hj⟩ ∈ ballAnnulus := hl.1 ⟨(p:ℕ)/3, hj⟩
    have hcl : vecmatsV3_p4 l ⟨(p:ℕ)/3, hj⟩ ∈ Metric.closedBall (0 : V3) (2 * h0) :=
      Set.sdiff_subset hv
    have hvb : ‖vecmatsV3_p4 l ⟨(p:ℕ)/3, hj⟩‖ ≤ 2 * h0 := by
      simpa using Metric.mem_closedBall.mp hcl

    have hcoe : ‖((vecmatsV3_p4 l ⟨(p:ℕ)/3, hj⟩ : V3) : Fin 3 → ℝ) ⟨(p:ℕ)%3, hc3⟩‖
        ≤ ‖vecmatsV3_p4 l ⟨(p:ℕ)/3, hj⟩‖ :=
      PiLp.norm_apply_le _ _
    rw [vecmatsV3_p4, WithLp.ofLp_toLp, Real.norm_eq_abs] at hcoe
    rw [← hvm]
    exact hcoe.trans hvb
  have h2 : (0:ℝ) ≤ 2 * h0 := by norm_num [h0]
  have hnorm : ‖l‖ ≤ 2 * h0 := by
    rw [pi_norm_le_iff_of_nonneg h2]
    intro p
    simpa using hcoord p
  exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hnorm)

/-- helper re-export for the subset above -/
theorem bsy1body_rows_p9 {k : ℕ} {a b : ℕ → ℕ → ℝ} {l : FinVec k 3}
    (hl : l ∈ BSY1body_p9 k a b) : ∀ j : Fin k, vecmatsV3_p4 l j ∈ ballAnnulus :=
  hl.1

/-- HOL `COMPACT_TRI_STABLE` (Pcrttid.hl:329). -/
theorem COMPACT_TRI_STABLE_p9 {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ} (h : triStable_p9 k d s a b J f) :
    IsCompact (BSY1body_p9 k a b) :=
  Metric.isCompact_of_isClosed_isBounded (CLOSED_TRI_SY_p9 h)
    (BOUNDED_TRI_SY_p9 h)

/-- HOL `PCRTTID` (Pcrttid.hl:347): the tri-system body is compact; the
`stable_system` half (adding `CONDITION2_SY`, HOL's `WJSCPRO`) is a
giant. DISCHARGES: second conjunct from `WJSCPRO`. -/
theorem PCRTTID_p9 :
    (∀ (d : ℝ) (J : Finset (Finset ℕ)) (k : ℕ) (a b : ℕ → ℕ → ℝ),
        triStable_p9 k d (Finset.Icc 0 (k - 1)) a b J (fun i => (1 + i) % k) →
          IsCompact (BSY1body_p9 k a b)) ∧
      (∀ (d : ℝ) (J : Finset (Finset ℕ)) (k : ℕ) (a b : ℕ → ℕ → ℝ),
        stableSystem_p9 k d (Finset.Icc 0 (k - 1)) a b J (fun i => (1 + i) % k) →
          IsCompact {l : FinVec k 3 | l ∈ BSY1body_p9 k a b ∧
            CONDITION2_SY_p9 k l}) := by
  refine ⟨fun _ _ k a b h => COMPACT_TRI_STABLE_p9 h, ?_⟩
  sorry

/-- HOL `COMPATIBLE_BW_TWO_LEMMAS2` (Nkezbfc.hl:1651). -/
theorem COMPATIBLE_BW_TWO_LEMMAS2_p9 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) (v w : V3) (hv : v ∈ V)
    (hw : w ∈ V) (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt {0} {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : HS.face (v, rhoNode1_p2 FF v) = fv) (hfw : HS.face (w, rhoNode1_p2 FF w) = fw) :
    ((vPrime_p2 V fv = slicev_p9 E FF v w) ∧
      (ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p9 E FF v w) ∧
      (fv = slicef_p9 E FF v w)) ∧
      ((vPrime_p2 V fw = slicev_p9 E FF w v) ∧
        (ePrime_p2 (E ∪ {{w, v}}) fw = slicee_p9 E FF w v) ∧
        (fw = slicef_p9 E FF w v)) := by
  sorry
