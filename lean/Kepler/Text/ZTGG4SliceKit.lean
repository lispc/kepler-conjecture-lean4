/-
Kepler.Text.ZTGG4SliceKit — gamma4-only slice-corners assembly for the
four decoupled ZTGIJCF4 boxes.  The per-slice sign obligations remain explicit
arguments of consumers; this file proves only the generic reduction.
-/
import Kepler.Text.ZTGJointKit

set_option maxHeartbeats 8000000

namespace Kepler.Text

noncomputable def ztg_g4_fun (x : Fin 6 → ℝ) : ℝ :=
  gamma4fgcy (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) lmfun

theorem ztg_g4_step_of_mono_up_pair (i : Fin 6) (x : Fin 6 → ℝ)
    {lo k hi : ℝ} (hlk : lo ≤ k) (_hkh : k ≤ hi)
    (hxi : x i ∈ Set.Icc lo hi)
    (hlo : ∀ t ∈ Set.Icc lo k, ztg_g4_fun (Function.update x i lo) ≤
      ztg_g4_fun (Function.update x i t))
    (hk : ∀ t ∈ Set.Icc k hi, ztg_g4_fun (Function.update x i k) ≤
      ztg_g4_fun (Function.update x i t)) :
    ∃ c ∈ ({lo} : Finset ℝ),
      ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x := by
  have hklo : ztg_g4_fun (Function.update x i lo) ≤
      ztg_g4_fun (Function.update x i k) := hlo k ⟨hlk, le_rfl⟩
  by_cases hxi_le : x i ≤ k
  · refine ⟨lo, by simp, ?_⟩
    have h1 := hlo (x i) ⟨hxi.1, hxi_le⟩
    rwa [Function.update_eq_self i x] at h1
  · have hxk : k ≤ x i := (not_le.mp hxi_le).le
    refine ⟨lo, by simp, ?_⟩
    calc ztg_g4_fun (Function.update x i lo) ≤
          ztg_g4_fun (Function.update x i k) := hklo
      _ ≤ ztg_g4_fun (Function.update x i (x i)) := hk (x i) ⟨hxk, hxi.2⟩
      _ = ztg_g4_fun x := by rw [Function.update_eq_self i x]

theorem ztg_g4_step_of_concave_pair (i : Fin 6) (x : Fin 6 → ℝ)
    {lo k hi : ℝ} (hlk : lo ≤ k) (hkh : k ≤ hi)
    (hxi : x i ∈ Set.Icc lo hi)
    (hl : ConcaveOn ℝ (Set.Icc lo k)
      (fun t => ztg_g4_fun (Function.update x i t)))
    (hr : ConcaveOn ℝ (Set.Icc k hi)
      (fun t => ztg_g4_fun (Function.update x i t))) :
    ∃ c ∈ ({lo, k, hi} : Finset ℝ),
      ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x := by
  have hmin := Kepler.NliBanks9.min_of_piecewise_concave hlk hkh hl hr hxi
  rw [Function.update_eq_self i x] at hmin
  rcases min_cases (ztg_g4_fun (Function.update x i lo))
      (min (ztg_g4_fun (Function.update x i k))
        (ztg_g4_fun (Function.update x i hi))) with hA | hA
  · refine ⟨lo, by simp, ?_⟩
    rw [hA.1] at hmin
    exact hmin
  · rcases min_cases (ztg_g4_fun (Function.update x i k))
        (ztg_g4_fun (Function.update x i hi)) with hB | hB
    · refine ⟨k, by simp, ?_⟩
      rw [hA.1, hB.1] at hmin
      exact hmin
    · refine ⟨hi, by simp, ?_⟩
      rw [hA.1, hB.1] at hmin
      exact hmin

theorem ztg_g4_step_of_concave (i : Fin 6) (x : Fin 6 → ℝ)
    {lo hi : ℝ} (hxi : x i ∈ Set.Icc lo hi)
    (hconc : ConcaveOn ℝ (Set.Icc lo hi)
      (fun t => ztg_g4_fun (Function.update x i t))) :
    ∃ c ∈ ({lo, hi} : Finset ℝ),
      ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x := by
  have hlohi : lo ≤ hi := le_trans hxi.1 hxi.2
  have hmin := Kepler.NliBanks9.concaveOn_min_endpoints hlohi hconc hxi
  rw [Function.update_eq_self i x] at hmin
  rcases min_cases (ztg_g4_fun (Function.update x i lo))
      (ztg_g4_fun (Function.update x i hi)) with hA | hA
  · refine ⟨lo, by simp, ?_⟩
    rw [hA.1] at hmin
    exact hmin
  · refine ⟨hi, by simp, ?_⟩
    rw [hA.1] at hmin
    exact hmin

theorem ztg_boxInf_ge {n : ℕ} {cands : Fin n → Finset ℝ} (G : ℝ)
    (hne : ∀ i, (cands i).Nonempty) {f : (Fin n → ℝ) → ℝ}
    (h : ∀ s ∈ Finset.univ.pi cands, G ≤ f (fun i => s i (Finset.mem_univ i))) :
    G ≤ Kepler.NliBanks9.boxInf cands hne f := by
  unfold Kepler.NliBanks9.boxInf
  refine Finset.inf'_mem {r : ℝ | G ≤ r} ?_ _ _ _ h
  intro a ha b hb
  change G ≤ a at ha
  change G ≤ b at hb
  exact le_min ha hb

theorem ztg_g4_lower_of_slice_corners (G : ℝ)
    (lo hi : Fin 6 → ℝ) (cands : Fin 6 → Finset ℝ)
    (hne : ∀ i, (cands i).Nonempty)
    (hsub : ∀ i, ∀ c ∈ cands i, c ∈ Set.Icc (lo i) (hi i))
    (hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (lo j) (hi j)) →
      ∃ c ∈ cands i, ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x)
    (hcorner : ∀ c0 ∈ cands 0, ∀ c1 ∈ cands 1, ∀ c2 ∈ cands 2,
      ∀ c3 ∈ cands 3, ∀ c4 ∈ cands 4, ∀ c5 ∈ cands 5,
      G ≤ gamma4fgcy c0 c1 c2 c3 c4 c5 lmfun) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (lo j) (hi j)) →
      G ≤ ztg_g4_fun x := by
  have hge : ∀ s ∈ Finset.univ.pi cands,
      G ≤ ztg_g4_fun (fun i => s i (Finset.mem_univ i)) := by
    intro s hs
    have hmem := Finset.mem_pi.mp hs
    show G ≤ gamma4fgcy (s 0 _) (s 1 _) (s 2 _) (s 3 _) (s 4 _) (s 5 _) lmfun
    exact hcorner (s 0 (Finset.mem_univ 0)) (hmem 0 (Finset.mem_univ 0))
      (s 1 (Finset.mem_univ 1)) (hmem 1 (Finset.mem_univ 1))
      (s 2 (Finset.mem_univ 2)) (hmem 2 (Finset.mem_univ 2))
      (s 3 (Finset.mem_univ 3)) (hmem 3 (Finset.mem_univ 3))
      (s 4 (Finset.mem_univ 4)) (hmem 4 (Finset.mem_univ 4))
      (s 5 (Finset.mem_univ 5)) (hmem 5 (Finset.mem_univ 5))
  have h0 : G ≤ Kepler.NliBanks9.boxInf cands hne ztg_g4_fun :=
    ztg_boxInf_ge G hne hge
  intro x hx
  exact le_trans h0
    (Kepler.NliBanks9.boxInf_le_of_slice_min lo hi cands hne hsub hstep hx)

#print axioms ztg_g4_step_of_mono_up_pair
#print axioms ztg_g4_step_of_concave_pair
#print axioms ztg_g4_step_of_concave
#print axioms ztg_boxInf_ge
#print axioms ztg_g4_lower_of_slice_corners

end Kepler.Text
