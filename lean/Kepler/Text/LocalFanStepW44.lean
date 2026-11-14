/-
Kepler/Text/LocalFanStepW44.lean — wave W44：w 侧 back-run 1_2 + back union 恒等式
（HOL `NKEZBFC.hl:2346-2583` 的 Lean 移植；SF 批 `hslot_wEG` 的数学供给件）。

## 定位

v4 链的 w 侧槽（`pW5w_telescope` 的 `hprev`）在全范围 `n ∈ [2, k-1]` 上要求
**backward 1_2** `vv n ∈ affGt{0}{p, vv(n-1)}`。SCOUT 判定该全范围形假
（`ProbeB1Planar`: 它强制整条 rho 轨道落在 `span{p, vv 1}`）。
HOL 实际证明的是 **back run 内**的 backward 1_2（`:2406-2499`：EGHNAVX 第 5 合取
run cone + AZIM_EQ 链 + `decomposition_planar_by_angle_fan` + union IH +
`FAN_IN_AFF_GE_IMP_EQ`），以及由它搭起的 back union 恒等式（`:2346-2400`）。

本件 = 这两条：

* §1 私有单步件 `pW44_step12`：给定 back union 恒等式在 `j` 与 run cone，
  证 `vv (k-j-1) ∈ affGt{0}{p, vv(k-j-2)}`（HOL :2406-2499）。
* §2 `pW44_backUnion_aux`：back union 恒等式归纳（HOL :2346-2400；步内调 §1）。
* §3 对外 `pW44_backUnion`（V.ncard 形）+ `pW44_back1_2`（∀n 形）。

信任面：纯定理，无 axiom/sorry/native_decide；探针 = 标准三。
-/
import Kepler.Text.LocalFanStepW42A

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §0 共用原语 -/

/-- 轨道点互异（索引 ≤ k；`vv k = p = vv 0` 端由 0 号互异补）。 -/
private theorem pW44_vv_disj (hcl : convexLocalFan_p2 V E FF) {p : V3} (hp : p ∈ V)
    {vv : ℕ → V3} {k : ℕ} (hk : V.ncard = k)
    (hiter : ∀ m, (rhoNode1_p2 FF)^[m] p = vv m)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ k) : vv a ≠ vv b := by
  have hlf : localFan_p2 V E FF := hcl.1
  rcases Nat.lt_or_eq_of_le hb with hlt | heq
  · have h := LOFA_IMP_DIS_ELMS23 hlf hp a b hab (by omega)
    rw [hiter a, hiter b] at h
    exact Ne.symm h
  · have hbk : b = k := heq
    rw [hbk]
    have hvk : vv k = p := by
      rw [← hiter k, hk.symm]
      exact LOFA_IMP_ITER_RHO_NODE_ID hlf hp
    rw [hvk]
    intro hcon
    have h0 : (rhoNode1_p2 FF)^[a] p = (rhoNode1_p2 FF)^[0] p := by
      rw [hiter a, Function.iterate_zero_apply]
      exact hcon
    exact LOFA_IMP_DIS_ELMS23 hlf hp 0 a (by omega) (by omega) h0

/-- 轨道相邻对是边：`{vv a, vv (a+1)} ∈ E`（`a < V.ncard`）。 -/
private theorem pW44_edge_of_consec (hcl : convexLocalFan_p2 V E FF) {p : V3} (hp : p ∈ V)
    {vv : ℕ → V3} (hiter : ∀ m, (rhoNode1_p2 FF)^[m] p = vv m)
    {a : ℕ} (ha : a < V.ncard) : ({vv a, vv (a + 1)} : Set V3) ∈ E := by
  have hlf : localFan_p2 V E FF := hcl.1
  have hVV : vv a ∈ V := by
    rw [← hiter a]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp a
  have hdart : (vv a, rhoNode1_p2 FF (vv a)) ∈ FF :=
    (LOCAL_FAN_RHO_NODE_PROS hlf).1 (vv a) hVV
  have hρ : rhoNode1_p2 FF (vv a) = vv (a + 1) := by
    rw [← hiter a, ← hiter (a + 1)]
    rw [show a + 1 = Nat.succ a from rfl, Function.iterate_succ_apply']
  rw [hρ] at hdart
  have h := LOCAL_FAN_IN_FF_IN_ORD_PAIRS hlf hdart
  simpa [ordPairs_p2] using h

/-! ## §1 单步 backward 1_2（HOL `:2406-2499`） -/

/-- **单步 backward 1_2**：back union 恒等式在 `j`（`hA`）+ run cone（`hflat`，
EGHNAVX 第 5 合取，经 `pW5b_flat_mem` 供给）⇒ `vv(k-j-1) ∈ affGt{0}{p, vv(k-j-2)}`。
域 `j < k-i-2`（保证 `vv(k-j-2)` 仍在 run 内，即索引 ≥ i+1）。 -/
private theorem pW44_step12
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {k : ℕ} (hk : V.ncard = k)
    (hiter : ∀ m, (rhoNode1_p2 FF)^[m] p = vv m)
    (hcol : ∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3))
    {i j : ℕ} (hj : j < k - i - 2)
    (hA : ∀ z : V3, z ∈ affGe ({0} : Set V3) {p, vv (k - j - 1)}
        ↔ ∃ j1, j1 ≤ j ∧ z ∈ affGe ({0} : Set V3)
            {vv (k - j1 - 1), vv (k - j1)})
    (hflat : ∀ m : ℕ, i + 1 ≤ m → m < k → vv m ∈ affGt ({0, p} : Set V3) {vv (k - 1)}) :
    vv (k - j - 1) ∈ affGt ({0} : Set V3) {p, vv (k - j - 1 - 1)} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hfan : Kepler.Text.Fan.FAN 0 V E := (CVLF_LF_F hcl).2
  have hVV : ∀ m : ℕ, vv m ∈ V := fun m => by
    rw [← hiter m]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp m
  -- 非共线（generic + 互异）
  have hnc : ∀ m : ℕ, 1 ≤ m → m ≤ k - 1 → ¬ Collinear3 (0 : V3) p (vv m) := by
    intro m hm1 hm2
    have hne : vv m ≠ p := by
      intro hcon
      have h0 : (rhoNode1_p2 FF)^[m] p = (rhoNode1_p2 FF)^[0] p := by
        rw [hiter m, Function.iterate_zero_apply]
        exact hcon
      exact LOFA_IMP_DIS_ELMS23 hlf hp 0 m hm1 (by omega) h0
    have h := hcol (vv m) (hVV m) hne
    simpa only [Collinear3] using h
  have hk1 : 2 ≤ k := by omega
  have hnc_vv1 : ¬ Collinear3 (0 : V3) p (vv 1) := hnc 1 (by omega) (by omega)
  have hnc_last : ¬ Collinear3 (0 : V3) p (vv (k - 1)) := hnc (k - 1) (by omega) (by omega)
  have hnc_g : ¬ Collinear3 (0 : V3) p (vv (k - j - 1 - 1)) := by
    refine hnc (k - j - 1 - 1) ?_ ?_ <;> omega
  have hnc_ρg : ¬ Collinear3 (0 : V3) p (vv (k - j - 1)) := by
    refine hnc (k - j - 1) ?_ ?_ <;> omega
  -- run cone 两点
  have hg_run : vv (k - j - 1 - 1) ∈ affGt ({0, p} : Set V3) {vv (k - 1)} :=
    hflat (k - j - 1 - 1) (by omega) (by omega)
  have hρg_run : vv (k - j - 1) ∈ affGt ({0, p} : Set V3) {vv (k - 1)} :=
    hflat (k - j - 1) (by omega) (by omega)
  -- AZIM_EQ 链（base = vv 1，tip = vv(k-1)）
  have h1 : azim 0 p (vv 1) (vv (k - 1)) = azim 0 p (vv 1) (vv (k - j - 1)) :=
    (azim_eq_azim_iff hnc_vv1 hnc_last hnc_ρg).mpr hρg_run
  have h2 : azim 0 p (vv 1) (vv (k - 1)) = azim 0 p (vv 1) (vv (k - j - 1 - 1)) :=
    (azim_eq_azim_iff hnc_vv1 hnc_last hnc_g).mpr hg_run
  have h3 : azim 0 p (vv 1) (vv (k - j - 1)) = azim 0 p (vv 1) (vv (k - j - 1 - 1)) :=
    h1.symm.trans h2
  have h21 : vv (k - j - 1 - 1) ∈ affGt ({0, p} : Set V3) {vv (k - j - 1)} :=
    (azim_eq_azim_iff hnc_vv1 hnc_ρg hnc_g).mp h3
  have hge : vv (k - j - 1 - 1) ∈ affGe ({0, p} : Set V3) {vv (k - j - 1)} :=
    pW5b_affGt_subset_affGe h21
  -- 平面分解：desired ∨ 退化支
  have hdec := decomposition_planar_by_angle_fan (x := (0 : V3)) (v := p)
    (u := vv (k - j - 1)) (w := vv (k - j - 1 - 1)) hnc_ρg hnc_g hge
  rcases hdec with h | h
  · exact h
  · -- 退化支：g ∈ affGe{0}{p, ρg} ⇒ 沿 union 落到某个边锥 ⇒ 边锥只含端点 ⇒ 矛盾
    exfalso
    have hmem : vv (k - j - 1 - 1) ∈ affGe ({0} : Set V3) {p, vv (k - j - 1)} := h
    obtain ⟨j1, hj1, hsector⟩ := (hA (vv (k - j - 1 - 1))).mp hmem
    have hmk : k - j - 1 - 1 < k := by omega
    have ha1 : k - j1 - 1 < k := by omega
    have hedge : ({vv (k - j1 - 1), vv (k - j1)} : Set V3) ∈ E := by
      have h := pW44_edge_of_consec hcl hp hiter (a := k - j1 - 1) (by omega)
      rw [show k - j1 - 1 + 1 = k - j1 from by omega] at h
      exact h
    have hcase := FAN_IN_AFF_GE_IMP_EQ (x := (0 : V3)) (V := V) (E := E)
      hfan (hVV (k - j - 1 - 1)) hedge hsector
    rcases hcase with heq | heq
    · exact (pW44_vv_disj hcl hp hk hiter (a := k - j - 1 - 1) (b := k - j1 - 1)
        (by omega) (by omega) (by omega)) heq
    · exact (pW44_vv_disj hcl hp hk hiter (a := k - j - 1 - 1) (b := k - j1)
        (by omega) (by omega) (by omega)) heq

/-! ## §2 back union 恒等式（HOL `:2346-2400` 归纳） -/

/-- **back union 恒等式（k 形）**：`∀ j < k-i-1`，
`affGe{0}{p, vv(k-j-1)} = ⋃_{j1≤j} affGe{0}{vv(k-j1-1), vv(k-j1)}`。
归纳步的 h4 由 §1 供给（其 union 前提 = 归纳假设）。 -/
private theorem pW44_backUnion_aux
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k)
    (hiter : ∀ m, (rhoNode1_p2 FF)^[m] p = vv m)
    (hbta : ∀ m, azim 0 p (vv 1) (vv m) = bta m)
    (hcol : ∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3))
    {i : ℕ} (hi : i < k - 1) (hbilast : bta (i + 1) = bta (k - 1)) :
    ∀ j, j < k - i - 1 → ∀ z : V3,
      z ∈ affGe ({0} : Set V3) {p, vv (k - j - 1)}
        ↔ ∃ j1, j1 ≤ j ∧ z ∈ affGe ({0} : Set V3)
            {vv (k - j1 - 1), vv (k - j1)} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hVV : ∀ m : ℕ, vv m ∈ V := fun m => by
    rw [← hiter m]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp m
  have hp0 : p = vv 0 := by
    rw [← hiter 0, Function.iterate_zero_apply]
  have hvk : vv k = p := by
    rw [← hiter k, hk.symm]
    exact LOFA_IMP_ITER_RHO_NODE_ID hlf hp
  have hdisj : ∀ a b : ℕ, Disjoint ({0} : Set V3) {vv a, vv b} := by
    intro a b
    refine Set.disjoint_singleton_left.mpr ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => h0V (h ▸ hVV a), fun h => h0V (h ▸ hVV b)⟩
  -- run cone
  have hflat : ∀ m : ℕ, i + 1 ≤ m → m < k → vv m ∈ affGt ({0, p} : Set V3) {vv (k - 1)} := by
    intro m hm1 hm2
    have hvk1 : vv (k - 1) = ivsRhoNode1_p2 FF p := by
      rw [← hiter (k - 1), show k - 1 = V.ncard - 1 from by omega]
      exact ITER_CARD_MINUS1_EQ_IVS_RN1 hlf hp
    rw [hvk1]
    exact pW5b_flat_mem hcl hg hp hk hiter hbta hi hbilast hm1 hm2
  intro j
  induction j with
  | zero =>
      intro _ z
      constructor
      · intro hz
        refine ⟨0, le_refl 0, ?_⟩
        have h1 : vv (k - 0) = p := by rw [show k - 0 = k from by omega, hvk]
        rw [h1, show k - 0 - 1 = k - 1 from by omega]
        rwa [show ({vv (k - 1), p} : Set V3) = {p, vv (k - 1)} from Set.pair_comm _ _]
      · rintro ⟨j1, hj1, hz⟩
        have hj1' : j1 = 0 := by omega
        rw [hj1'] at hz
        rw [show k - 0 - 1 = k - 1 from by omega,
          show k - 0 = k from by omega, hvk,
          show ({vv (k - 1), p} : Set V3) = {p, vv (k - 1)} from Set.pair_comm _ _] at hz
        rw [show k - 0 - 1 = k - 1 from by omega]
        exact hz
  | succ j ih =>
      intro hj z
      have hj' : j < k - i - 1 := by omega
      have hIH := ih hj'
      have hidx : k - (j + 1) - 1 = k - j - 1 - 1 := by omega
      have hidx2 : k - (j + 1) = k - j - 1 := by omega
      -- §1 供给 h4（union 前提 = 归纳假设）
      have hB : vv (k - j - 1) ∈ affGt ({0} : Set V3) {p, vv (k - j - 1 - 1)} :=
        pW44_step12 hcl hg hp hk hiter hcol (by omega) hIH hflat
      -- h4 的方向与 AFF_GE_EQ 的 u/v1 对位：u = vv(k-j-2)、v1 = vv(k-j-1)
      have hdis1 : Disjoint ({0} : Set V3) {p, vv (k - j - 1 - 1)} := by
        rw [hp0]
        exact hdisj 0 (k - j - 1 - 1)
      have hdis2 : Disjoint ({0} : Set V3) {p, vv (k - j - 1)} := by
        rw [hp0]
        exact hdisj 0 (k - j - 1)
      have hdis3 : Disjoint ({0} : Set V3) {vv (k - j - 1), vv (k - j - 1 - 1)} :=
        hdisj (k - j - 1) (k - j - 1 - 1)
      have hEq := AFF_GE_EQ_AFF_GE_UNION_p9 (x := (0 : V3)) (v := p)
        (u := vv (k - j - 1 - 1)) (v1 := vv (k - j - 1)) hdis1 hdis2 hdis3 hB
      rw [hidx, hEq, Set.mem_union]
      constructor
      · rintro (hz | hz)
        · obtain ⟨j1, hj1, hz'⟩ := (hIH z).mp hz
          exact ⟨j1, by omega, hz'⟩
        · refine ⟨j + 1, le_refl _, ?_⟩
          rw [hidx, hidx2]
          rwa [show ({vv (k - j - 1 - 1), vv (k - j - 1)} : Set V3)
            = {vv (k - j - 1), vv (k - j - 1 - 1)} from Set.pair_comm _ _]
      · rintro ⟨j1, hj1, hz⟩
        rcases Nat.lt_or_ge j1 (j + 1) with hlt | hge
        · exact Or.inl ((hIH z).mpr ⟨j1, by omega, hz⟩)
        · right
          have hje : j1 = j + 1 := by omega
          rw [show ({vv (k - j - 1), vv (k - j - 1 - 1)} : Set V3)
            = {vv (k - j - 1 - 1), vv (k - j - 1)} from Set.pair_comm _ _]
          simpa [hje, hidx, hidx2] using hz

/-! ## §3 对外件 -/

/-- **`pW44_backUnion`**：back union 恒等式（`V.ncard` 形，与 `pW5w_telescope`
的结论逐字同形；`hprev` 已由 EGHNAVX 语境放电）。 -/
theorem pW44_backUnion
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k)
    (hiter : ∀ m, (rhoNode1_p2 FF)^[m] p = vv m)
    (hbta : ∀ m, azim 0 p (vv 1) (vv m) = bta m)
    (hcol : ∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3))
    {i : ℕ} (hi : i < k - 1) (hbilast : bta (i + 1) = bta (k - 1)) :
    ∀ j, j < V.ncard - i - 1 → ∀ z : V3,
      z ∈ affGe ({0} : Set V3) {p, vv (V.ncard - j - 1)}
        ↔ ∃ j1, j1 ≤ j ∧ z ∈ affGe ({0} : Set V3)
            {vv (V.ncard - j1 - 1), vv (V.ncard - j1)} := by
  intro j hj z
  have h := pW44_backUnion_aux hcl hg hp hk hiter hbta hcol hi hbilast j (by omega) z
  simpa only [hk] using h

/-- **`pW44_back1_2`**：back run 内 backward 1_2（HOL 内容的 ∀n 形）：
`i+2 ≤ n ≤ k-1 ⇒ vv n ∈ affGt{0}{p, vv(n-1)}`。 -/
theorem pW44_back1_2
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k)
    (hiter : ∀ m, (rhoNode1_p2 FF)^[m] p = vv m)
    (hbta : ∀ m, azim 0 p (vv 1) (vv m) = bta m)
    (hcol : ∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3))
    {i : ℕ} (hi : i < k - 1) (hbilast : bta (i + 1) = bta (k - 1)) :
    ∀ n : ℕ, i + 2 ≤ n → n ≤ k - 1 →
      vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)} := by
  intro n hn1 hn2
  have hjaux : k - n - 1 < k - i - 1 := by omega
  have hA := pW44_backUnion_aux hcl hg hp hk hiter hbta hcol hi hbilast
    (k - n - 1) hjaux
  have hflat : ∀ m : ℕ, i + 1 ≤ m → m < k → vv m ∈ affGt ({0, p} : Set V3) {vv (k - 1)} := by
    intro m hm1 hm2
    have hvk1 : vv (k - 1) = ivsRhoNode1_p2 FF p := by
      rw [← hiter (k - 1), show k - 1 = V.ncard - 1 from by omega]
      exact ITER_CARD_MINUS1_EQ_IVS_RN1 hcl.1 hp
    rw [hvk1]
    exact pW5b_flat_mem hcl hg hp hk hiter hbta hi hbilast hm1 hm2
  have hB := pW44_step12 hcl hg hp hk hiter hcol (j := k - n - 1) (by omega) hA hflat
  simpa only [show k - (k - n - 1) - 1 = n from by omega] using hB

end Kepler.Text

/-! ## 探针 -/

#print axioms Kepler.Text.pW44_back1_2
#print axioms Kepler.Text.pW44_backUnion
