/-
  Kepler.Text.TameSpine.JcajyduAqLeaf9W2 — AQ9 波 2：计数主证 + `aq9`（槽冻结陈述）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ ① `aq9w2_coreDart`（私件）：`v ∈ coreSpine row`（行 Nodup/非空）⇒ 行内取 dart，第一坐标 = v
  │ ② `aq9_countNtrans`（M1+M2 合体）：¬final 支的位次计数主件
  │ ③ `aq9`（M3）：final 支 = marked 合取投影；¬final 支 = ②
  └───────────────────────────────────────────────────────────────
  ┌─ DIFFERS（相对 HOL AQ9.hl；按编排者裁决的原生短路线）────────────
  │ ① **位次计数替代值级计数**（AQ9_SURVEY.md §5 的 A/B 情形论证原文）：
  │  · 记 `quotient N' = A ++ [core s2] ++ B ++ [core s1]`（A/B = N₁/N₂ 的 core 表）、
  │    `quotient N = A ++ [core r] ++ B`（W1a `aq9_rowDecomp` + `quotientListCore`）。
  │  · 情形 A（v 在旧 quotient）：旧过滤长 ≥2（marked 合取 5）且删去 `[core r]` 一位
  │    ⇒ `lenA + |X_r| + lenB ≥ 2`，`|X_r| ≤ 1`。
  │    若 `v ∉ core r`（`|X_r| = 0`）：`lenA + lenB ≥ 2`，新过滤含 A/B 全量 ⇒ 新长 ≥ 2。
  │    若 `v ∈ core r`：`coreDart` 取 `d ∈ r, d.1 = v`，`aq5_rCover` 给 `d` 落在 s1/s2 弧段
  │    ⇒ `memCore.mpr` 给 `v ∈ core s1|s2` ⇒ 该单元素过滤 = 1，新长 ≥ (lenA+lenB) + 1 ≥ 2。
  │  · 情形 B（v 不在旧 quotient）：`aq9_provenance` 右析取 + `aq9_windowFst` 给
  │    `v ∈ map fst s2 ∧ v ∈ map fst s1` ⇒ `memCore.mpr` ⇒ 两个单元素过滤各 = 1 ⇒ 新长 ≥ 2。
  │  · **同一行值出现两次也按两个位次计 2**（filter 按出现位次）⇒ 不需要行值互异
  │    （HOL ⑨⑩⑪ 三件的判等）也不需要下标提取。
  │ ② 五塔槽只在 `aqs_aqNormalList` 处实例化（aq1..aq5 全在库），取新表 NormalListSpine，
  │    供 `memCore`（part 级 ↔ FST 表）双向使用；旧表 NormalListSpine 走 marked 合取。
  │ ③ 零新数学：全部消费在库件（W1a/W1b 引擎 + parts 三件 + memCore + aq5_rCover）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf9W1b
import Kepler.Text.TameSpine.JcajyduAqLeaf1F
import Kepler.Text.TameSpine.JcajyduAqTowerE2
import Kepler.Text.TameSpine.JcajyduAqSplit1H
import Kepler.Text.TameSpine.JcajyduAqLeaf5
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1a

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-- 私件：单元素过滤（命中）长 = 1（谓词作显式变量，避开 lambda 的 rw 失配）。 -/
private theorem aq9w2_filterSingle {α : Type*} (P : α → Bool) (x : α) (h : P x = true) :
    (List.filter P [x]).length = 1 := by
  rw [List.filter_cons_of_pos h]
  simp

/-- 私件：单元素过滤（不命中）长 = 0。 -/
private theorem aq9w2_filterSingleNeg {α : Type*} (P : α → Bool) (x : α)
    (h : ¬ P x = true) : (List.filter P [x]).length = 0 := by
  rw [List.filter_cons_of_neg h]
  simp

/-- 私件：`v ∈ coreSpine row` ⇒ 行内有 dart 第一坐标 = v（parts 头提取）。 -/
private theorem aq9w2_coreDart (L : fgraph ℕ) {row : List (ℕ × ℕ)} {v : ℕ}
    (hnd : row.Nodup) (hne : row ≠ []) (hv : v ∈ coreSpine L row) :
    ∃ d ∈ row, d.1 = v := by
  have hmap : v ∈ (partsSpine L row).map (fun a => a.head!.1) := hv
  obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hmap
  have hpne : p ≠ [] := partsAllNonnil L hnd hne p hp
  exact ⟨p.head!, memPartsImp L hnd hne hp p.head! (List.head!_mem_self hpne), hpv⟩

/-- **¬final 支位次计数主件**（M1+M2）：新表 quotient 的每个顶点在 ≥2 个 quotient 行。 -/
theorem aq9_countNtrans (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) {v : ℕ}
    (hv : v ∈ (quotientListSpine L (ntransSpine L N r x 1)).flatten) :
    1 < ((quotientListSpine L (ntransSpine L N r x 1)).filter
      (fun q => decide (v ∈ q))).length := by
  have hunL : ∀ l ∈ L, l.Nodup := (simpleHypermapUniq L hL hgn).mp hm.1.1.simple
  obtain ⟨N₁, N₂, hN, _hnot, hnt⟩ := aq9_rowDecomp L hL hgn hunL hm hf
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hrsplit : r.Nodup ∧ r ≠ [] := normalListUniqNonnil hm.1.2.1 hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hra : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
    aq1_nextElYNePrevElZ L hL hgn hunL hm hf
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  -- 新表 NormalListSpine（五塔槽实例化，唯一消费处）
  have hnN' : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL (aq1 L hL) (aq2 L hL) (aq3 L hL) (aq4 L hL) (aq5 L hL) hgn hm
  -- 两行在新表中的成员性与 Nodup/非空
  have hs2memN' : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 ∈ ntransSpine L N r x 1 := by
    rw [hnt]
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_singleton_self _)))
  have hs1memN' : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 ∈ ntransSpine L N r x 1 := by
    rw [hnt]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  -- 行展开
  have hs2eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).2
      = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ [lYSpine L r x])
        ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) := by
    simp only [splitNormalListSpine]
    rw [hnextz1]
  have hs1eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1
      = (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
        ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
    rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (prevEl r (lZSpine L N r x)), hnextz1]
  -- quotient 的两侧显式分解
  have hqN : quotientListSpine L N
      = List.map (coreSpine L) N₁
        ++ ([coreSpine L r] ++ List.map (coreSpine L) N₂) := by
    rw [quotientListCore, hN]
    simp only [List.map_append, List.map_cons]
    rfl
  have hqN' : quotientListSpine L (ntransSpine L N r x 1)
      = List.map (coreSpine L) N₁
        ++ [coreSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (prevEl r (lZSpine L N r x))).2]
        ++ List.map (coreSpine L) N₂
        ++ [coreSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (prevEl r (lZSpine L N r x))).1] := by
    rw [quotientListCore, hnt]
    simp only [List.map_append, List.map_cons, List.map_nil]
  -- 过滤长公式（旧 / 新）
  have holdEq : (List.filter (fun q => decide (v ∈ q)) (quotientListSpine L N)).length
      = (List.filter (fun q => decide (v ∈ q)) (List.map (coreSpine L) N₁)).length
        + (List.filter (fun q => decide (v ∈ q)) [coreSpine L r]).length
        + (List.filter (fun q => decide (v ∈ q)) (List.map (coreSpine L) N₂)).length := by
    rw [hqN]
    simp only [List.filter_append, List.length_append]
    first | rfl | omega
  have hnewEq : (List.filter (fun q => decide (v ∈ q))
        (quotientListSpine L (ntransSpine L N r x 1))).length
      = (List.filter (fun q => decide (v ∈ q)) (List.map (coreSpine L) N₁)).length
        + (List.filter (fun q => decide (v ∈ q))
            [coreSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (prevEl r (lZSpine L N r x))).2]).length
        + (List.filter (fun q => decide (v ∈ q)) (List.map (coreSpine L) N₂)).length
        + (List.filter (fun q => decide (v ∈ q))
            [coreSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (prevEl r (lZSpine L N r x))).1]).length := by
    rw [hqN']
    simp only [List.filter_append, List.length_append]
  rcases aq9_provenance L hL hgn hunL hm hf hv with hvold | hvw
  · -- 情形 A：旧表已有该顶点
    have hold := hm.1.2.2.2.2.1.2 v hvold
    rw [holdEq] at hold
    by_cases hPr : (fun q : List ℕ => decide (v ∈ q)) (coreSpine L r) = true
    · -- v ∈ core r：覆盖取 s1/s2 的位次
      have hvr : v ∈ coreSpine L r := of_decide_eq_true hPr
      have hXr : (List.filter (fun q : List ℕ => decide (v ∈ q)) [coreSpine L r]).length
          = 1 :=
        aq9w2_filterSingle (fun q : List ℕ => decide (v ∈ q)) (coreSpine L r) hPr
      rw [hXr] at hold
      obtain ⟨d, hdr, hd1⟩ := aq9w2_coreDart L hrsplit.1 hrsplit.2 hvr
      rcases aq5_rCover hrnd hyr hzr hyne hz1r hnextz1 hra d hdr with hdf1 | hdf2
      · have hds1 : d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
          rw [hs1eq]
          exact List.mem_append_right _ hdf1
        have hcore1 : v ∈ coreSpine L (splitNormalListSpine L r
            (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (prevEl r (lZSpine L N r x))).1 :=
          (memCore L hL hnN' hs1memN' v).mpr (List.mem_map.mpr ⟨d, hds1, hd1⟩)
        have hP1 : (fun q : List ℕ => decide (v ∈ q)) (coreSpine L
            (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (prevEl r (lZSpine L N r x))).1) = true := by
          simp [hcore1]
        have hX1 : (List.filter (fun q : List ℕ => decide (v ∈ q)) [coreSpine L
            (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (prevEl r (lZSpine L N r x))).1]).length = 1 :=
          aq9w2_filterSingle (fun q : List ℕ => decide (v ∈ q)) (coreSpine L
            (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (prevEl r (lZSpine L N r x))).1) hP1
        rw [hnewEq, hX1]
        omega
      · have hds2 : d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
          rw [hs2eq]
          exact List.mem_append_left _ hdf2
        have hcore2 : v ∈ coreSpine L (splitNormalListSpine L r
            (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (prevEl r (lZSpine L N r x))).2 :=
          (memCore L hL hnN' hs2memN' v).mpr (List.mem_map.mpr ⟨d, hds2, hd1⟩)
        have hP2 : (fun q : List ℕ => decide (v ∈ q)) (coreSpine L
            (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (prevEl r (lZSpine L N r x))).2) = true := by
          simp [hcore2]
        have hX2 : (List.filter (fun q : List ℕ => decide (v ∈ q)) [coreSpine L
            (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (prevEl r (lZSpine L N r x))).2]).length = 1 :=
          aq9w2_filterSingle (fun q : List ℕ => decide (v ∈ q)) (coreSpine L
            (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (prevEl r (lZSpine L N r x))).2) hP2
        rw [hnewEq, hX2]
        omega
    · -- v ∉ core r：旧两位次全部存活
      have hXr : (List.filter (fun q : List ℕ => decide (v ∈ q)) [coreSpine L r]).length
          = 0 :=
        aq9w2_filterSingleNeg (fun q : List ℕ => decide (v ∈ q)) (coreSpine L r) hPr
      rw [hXr] at hold
      rw [hnewEq]
      omega
  · -- 情形 B：窗口顶点，s1/s2 两行各给一位次
    rcases aq9_windowFst L hL hgn hm hvw with ⟨hv2, hv1⟩
    have hcore2 : v ∈ coreSpine L (splitNormalListSpine L r
        (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).2 :=
      (memCore L hL hnN' hs2memN' v).mpr hv2
    have hcore1 : v ∈ coreSpine L (splitNormalListSpine L r
        (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1 :=
      (memCore L hL hnN' hs1memN' v).mpr hv1
    have hP2 : (fun q : List ℕ => decide (v ∈ q)) (coreSpine L
        (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).2) = true := by
      simp [hcore2]
    have hP1 : (fun q : List ℕ => decide (v ∈ q)) (coreSpine L
        (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).1) = true := by
      simp [hcore1]
    have hX2 : (List.filter (fun q : List ℕ => decide (v ∈ q)) [coreSpine L
        (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).2]).length = 1 :=
      aq9w2_filterSingle (fun q : List ℕ => decide (v ∈ q)) (coreSpine L
        (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).2) hP2
    have hX1 : (List.filter (fun q : List ℕ => decide (v ∈ q)) [coreSpine L
        (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).1]).length = 1 :=
      aq9w2_filterSingle (fun q : List ℕ => decide (v ∈ q)) (coreSpine L
        (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).1) hP1
    rw [hnewEq, hX2, hX1]
    omega

/-- **AQ9 叶主证**（HOL `AQ9_concl`，AQ9.hl:1368；槽陈述冻结于 TowerBase:284）。 -/
theorem aq9 (L : fgraph ℕ) (hL : GoodList L) : aq9Concl L hL := by
  intro N r x hgn hm v hv
  by_cases hfin : finalListSpine L r
  · rw [ntransId L N r x hfin] at hv ⊢
    exact hm.1.2.2.2.2.1.2 v hv
  · exact aq9_countNtrans L hL hgn hm hfin hv

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq9_countNtrans
#print axioms Kepler.Text.TameSpine.aq9
