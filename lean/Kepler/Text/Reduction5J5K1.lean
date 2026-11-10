/-
  Kepler.Text.Reduction5J5K1 — J5-2 续段：`reduction_K1`（reduction4.hl:253，170L）的**证体**。
  `reductionK1` 的结论 = `assumptionSetK10`（定义面 :3559，118 HOL 行，结论块 42 个顶层合取，
  见 Reduction3DefsAssumption:145-242），证体 = 前件表 → 结论表逐条对账。

  ┌─ 证体结构（HOL :375-:422 的对应）────────────────────────────────
  │ HOL：`DISCH_TAC; REWRITE_TAC[assumption_setK10]; REPEAT WEAKER_STRIP_TAC;
  │ FIRST_X_ASSUM_ST `is_restricted` (C INTRO_TAC [L;N;r;x;k]); ASM_REWRITE_TAC[];
  │ SIMP_TAC[]; REPEAT WEAKER_STRIP_TAC; INTRO_TAC final_assumption_mem_uniq […];
  │ ASM_SIMP_TAC[arith `~(k=0) ==> 0 < k`]; … BY(MESON_TAC[])`
  │ 即：取内层全称的 (L,N,r,x,k,uvns,vs,vs',fx,v) 与 13 条假设，用前件表的实例 H，
  │ 再用 `final_assumption_mem_uniq` 补 marked 推导事实，最后 MESON 对账 42 个结论合取。
  │ Lean 侧逐条显式对账（下表），不靠自动化。
  └────────────────────────────────────────────────────────────────

  ┌─ 结论块 42 合取 ← 来源（C 序号 = 定义面结论块顺序；k# = 前件表合取号；
  │    m# = final_assumption_mem_uniq 11 合取号；见本文件证体注释）────────
  │ C01 ← m9@k          C02 ← k15         C03 ← k16        C04 ← k10
  │ C05 ← k26（fx 换）   C06 ← k1.1        C07 ← m9@0       C08 ← k12（fx 换）
  │ C09 ← k18（tc=k）    C10 ← k19        C11 ← m9/k13/k14/k9/k18/k19/k20
  │ C12 ← k21           C13 ← k11（fx 换） C14 ← k11 集合外延 C15 ← k22
  │ C16 ← k27（fx 换）   C17 ← m11 + tc   C18 ← m11 + tc  C19 ← hprev 投影
  │ C20 ← m2 + fx       C21 ← m10 + fx   C22 ← k24 + fx  C23 ← k25
  │ C24 ← k5            C25 ← k6         C26 ← k7        C27 ← k8
  │ C28 ← m4 + fx       C29 ← k23        C30 ← m5        C31 ← m6
  │ C32 ← m3 + fx       C33 ← m7 + fx    C34 ← m8 + fx   C35 ← m9@0
  │ C36 ← k1.2          C37 ← k17        C38 ← k2 + C36  C39 ← k3 + fx
  │ C40 ← k4 + fx       C41 ← k28.1 + 三条定义方程       C42 ← k28.2 + 同上
  └────────────────────────────────────────────────────────────────

  ┌─ 为什么要 `hmu` 槽（对账差异，报编排者）─────────────────────────
  │ C01/C07/C11 的 core-Nodup、C17/C18 的 `transformCount ≠ 0 / 0 < 它`、
  │ C20/C21/C28/C32/C33/C34 的 marked 推导成员事实——
  │ 这些在 HOL 里全部由 `final_assumption_mem_uniq` 供给，而它需要**具体
  │ `marked_list`**；本定理的假设块只有抽象的 `Marked` 槽，抽象命题推不出任何
  │ 成员事实（取 `Marked := True` 即反例）。树内 K5 先例（`reductionK5` 把 HOL 证体
  │ 里的 `betwn_core0_z_y` / `marked_list_uniq_core` / `transform_count_non0` 等外部定理
  │ reify 成槽 `hbcK`/`hmuc`/`hnon0`…）与此同型：本文件把 `final_assumption_mem_uniq`
  │ 的 11 合取结论提成槽 `hmu`（槽形 = 该件在抽象槽上的逐字结论，前提用现成
  │ `reductionK4Asm`）。**偏离**：比 HOL 陈述多一条前提 `hmu`（变弱，结论不变）。
  │ 槽版落库后，`reductionK1Full`（本文件第二个定理）在 D3b 全实例化
  │ （`GoodNodesSlot`/`IsRestrictedSlot`/`MarkedSlot`）上把 `hmu` 用本车道
  │ `finalAssumptionMemUniq` 消掉，只余链惯例的 `haq`——这是主线装配要用的形。
  └────────────────────────────────────────────────────────────────

  ┌─ 对账差异记录（派单第 3 条要求）─────────────────────────────────
  │ 定义面结论块 = 42 个顶层合取（脚本按括号深度实测），前件表 = 28 个（K1Statement
  │ 头注）。两者的分组不是一一对应：结论块有 14 个合取（C01/C07/C14/C17/C18/C20/
  │ C21/C28/C32/C33/C34 + C11 的 core-Nodup 子项 + C36 的 v 侧 + C19）在前件表里没有
  │ 直接来源，必须靠 `hmu`（= mem_uniq）与假设块方程补。组数差异已在此列明，未硬凑：
  │ 前件表是 HOL 原文形，结论块是定义面逐字，两者本就不同层。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5K1Statement
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.Reduction5K5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts fList listOfDarts listPairs)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- **HOL `reduction_K1`**（reduction4.hl:253）的证体（槽版）。
`h : 前件表对一切 (L,N,r,x,k) 成立`，`hmu : final_assumption_mem_uniq 的结论`
（抽象槽上的 11 合取，槽形见下），结论 = `assumption_setK10`。 -/
theorem reductionK1 (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (h : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ),
      reductionK1Asm GoodNodesL IsRestrictedL Marked L N r x k → reductionK1Concl L N r x k)
    (hmu : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ),
      reductionK4Asm GoodNodesL IsRestrictedL Marked L N r x k →
        x ∈ listOfDarts L ∧
        x ∈ findFaceDarts L x ∧
        nextEl (findFaceDarts L x) x ∈ findFaceDarts L x ∧
        nextEl (findFaceDarts L x) x ∈ r ∧
        (∀ i, i < k → ztrans L N r x i ∈ r) ∧
        (∀ i, i < k → ytrans L N r x i ∈ r) ∧
        (∀ i, i < k → ytrans L N r x i ∈ findFaceDarts L x) ∧
        (∀ i, i < k → ztrans L N r x i ∈ findFaceDarts L x) ∧
        (∀ i, i ≤ k → (core L (rtrans L N r x i)).Nodup) ∧
        (findFaceDarts L x).Nodup ∧
        k ≠ 0) :
    Kepler.Text.Reduction3.assumptionSetK10 GoodNodesL IsRestrictedL Marked := by
  intro L N r x k uvns vs vs' fx v hblk
  obtain ⟨hL, hgn, hres, hep, hnv, hm, hnf, huvns, hvs, hvs', htc, hfx, hprev⟩ := hblk
  -- 前件表实例（H）与 mem_uniq 实例
  have hK := h L N r x k ⟨hL, hgn, hres, hep, hnv, hm, hnf, htc⟩
  rcases hK with
    ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17,
      k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28⟩
  have hmu11 := hmu L N r x k ⟨hL, hgn, hres, hm, hnf, htc⟩
  rcases hmu11 with ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩
  -- v 侧（(V) 合取）：i < k 的 prevEl 链与 (nextEl fx x).1 = v
  have hv1 : ∀ i, i < k → (prevEl (core L (rtrans L N r x i)) v, v) = x :=
    (k1 v hprev).1
  have hv2 : (nextEl (findFaceDarts L x) x).1 = v := (k1 v hprev).2
  -- `transformCount = k` 的改写件（C09/C10/C11 用）
  have hlt : ∀ i, i < transformCount L N r x → i < k := fun i hi => htc ▸ hi
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
  · -- C01
    exact m9 k (Nat.le_refl k)
  · -- C02
    exact k15
  · -- C03
    exact k16
  · -- C04
    exact k10
  · -- C05
    simpa only [hfx] using k26
  · -- C06
    exact hv1
  · -- C07
    have h0 := m9 0 (Nat.zero_le k)
    rw [rtrans_zero] at h0
    exact h0
  · -- C08
    simpa only [hfx] using k12
  · -- C09
    exact fun i hi => k18 i (hlt i hi)
  · -- C10
    exact fun i hi => k19 i (hlt i hi)
  · -- C11
    intro i hi1 hi2
    have hi2' : i < k := hlt i hi2
    have h13 := k13 i hi1 hi2'
    have h14 := k14 i hi1 hi2'
    have h9 := k9 i hi1 hi2'
    refine ⟨m9 i (Nat.le_of_lt hi2'), ?_, ?_, ?_,
      fun i' hi' => k18 i' (hlt i' hi'), fun i' hi' => k19 i' (hlt i' hi'),
      fun i' hi' => (k20 i i' hi1 hi2' (hlt i' hi')).1,
      fun i' hi' => (k20 i i' hi1 hi2' (hlt i' hi')).2⟩
    · simpa only [hfx] using h13
    · simpa only [hfx] using h14
    · simpa only [hfx] using h9
  · -- C12
    exact k21
  · -- C13
    simpa only [hfx] using k11
  · -- C14：由 C13（DIFF 等式）反推 N 侧与 betwn 侧不交
    rw [← hfx]
    intro i hin hbet
    have hd : i ∈ {z : ℕ | z ∈ (ntrans L N r x 1).flatten.map (fun d => d.1) ∧
        z ∉ N.flatten.map (fun d => d.1)} := by
      rw [k11]
      exact hbet
    exact hd.2 hin
  · -- C15
    exact k22
  · -- C16
    simpa only [hfx] using k27
  · -- C17
    rw [htc]
    exact m11
  · -- C18
    exact Nat.pos_of_ne_zero (by rw [htc]; exact m11)
  · -- C19
    exact (congrArg Prod.fst hprev).symm
  · -- C20
    simpa only [hfx] using m2
  · -- C21
    simpa only [hfx] using m10
  · -- C22
    simpa only [hfx] using k24
  · -- C23
    exact k25
  · -- C24
    simpa only [hfx] using k5
  · -- C25
    simpa only [hfx] using k6
  · -- C26
    simpa only [hfx] using k7
  · -- C27
    simpa only [hfx] using k8
  · -- C28
    simpa only [hfx] using m4
  · -- C29
    exact k23
  · -- C30
    exact m5
  · -- C31
    exact m6
  · -- C32
    simpa only [hfx] using m3
  · -- C33
    simpa only [hfx] using m7
  · -- C34
    simpa only [hfx] using m8
  · -- C35
    have h0 := m9 0 (Nat.zero_le k)
    rw [rtrans_zero] at h0
    exact h0
  · -- C36
    simpa only [hfx] using hv2
  · -- C37
    exact k17
  · -- C38：k2 换 fx 后用 (nextEl fx x).1 = v 收口
    have hv2' : (nextEl fx x).1 = v := by simpa only [hfx] using hv2
    rw [hfx] at k2
    rw [← hv2']
    exact k2
  · -- C39
    simpa only [hfx] using k3
  · -- C40
    simpa only [hfx] using k4
  · -- C41（UVNS 第一合取）
    have h28 := k28 v hprev
    dsimp only at h28
    rw [huvns, hvs, hvs'] at h28
    exact h28.1
  · -- C42（UVNS 第二合取）
    have h28 := k28 v hprev
    dsimp only at h28
    rw [huvns, hvs, hvs'] at h28
    exact h28.2

/-- `reduction_K1` 的**全实例化形**（主线装配用）：`hmu` 由本车道
`finalAssumptionMemUniq` 消掉，只余链惯例的 `haq`。 -/
theorem reductionK1Full
    (haq : ∀ (L : fgraph ℕ) (hL : GoodList L), Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (h : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ),
      reductionK1Asm Kepler.Text.Reduction3.GoodNodesSlot
        Kepler.Text.Reduction3.IsRestrictedSlot Kepler.Text.Reduction3.MarkedSlot L N r x k →
        reductionK1Concl L N r x k) :
    Kepler.Text.Reduction3.assumptionSetK10Full :=
  reductionK1 _ _ _ h
    (fun L N r x k hAsm =>
      let ⟨hL, hgn, hres, hm, hnf, htc⟩ := hAsm
      finalAssumptionMemUniq L hL (hgn hL) (hres hL) (haq L hL) k (hm hL) hnf htc)

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.reductionK1
#print axioms Kepler.Text.Reduction5.reductionK1Full
