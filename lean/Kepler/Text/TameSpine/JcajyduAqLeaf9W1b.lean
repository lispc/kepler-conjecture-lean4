/-
  Kepler.Text.TameSpine.JcajyduAqLeaf9W1b — AQ9 波 1b：行覆盖 + 窗口双行 + provenance
  （侦察件表 P2/P2'/P3/P4；AQ9_SURVEY.md §4–§5 的原生短路线）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ ① `aq9_rowCoverS2` : `d ∈ s2 ⇒ d ∈ r ∨ d ∈ w`
  │ ② `aq9_rowCoverS1` : `d ∈ s1 ⇒ d ∈ r ∨ d ∈ new1`
  │ ③ `aq9_windowFst`  : `v ∈ map fst w ⇒ v ∈ map fst s2 ∧ v ∈ map fst s1`
  │ ④ `aq9_provenance`（原生 CASES_CORE 等价物）：
  │    `v ∈ flatten (quotient N') ⇒ v ∈ flatten (quotient N) ∨ v ∈ map fst w`
  └───────────────────────────────────────────────────────────────
  DIFFERS（相对 HOL AQ9.hl，按编排者裁决的原生短路线）：
  - HOL ⑥ CASES_CORE（610 行）的值级核心被 ④ 替代：用 `quotientListCore`
    （quotient = map coreSpine）拆行 + ①②③ 的 dart 级覆盖 + 处旧表 `memCore.mpr`
    （旧表 NormalListSpine 由 marked 合取直取，**不需要**新表 NormalListSpine/五塔槽）；
  - ③ 的载体是 `map (fun d => d.1)`（dart 级 FST 表），不是 part 级 `coreSpine`：
    part 头由 ④ 内的 `coreDart` 提取（本地私件），避免在 ③ 里做 part 结构判定
    （HOL 该步由 mem_core 在 main 里做）；
  - 位次计数替代值级计数的数学理由见 AQ9_SURVEY.md §5（A/B 情形）与 W2 的 DIFFERS。
  零新数学：全部消费在库件（split 展开 / parts 三件 / fstNListPower / memCore）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf9W1
import Kepler.Text.TameSpine.JcajyduAqLeaf8W05
import Kepler.Text.TameSpine.JcajyduAqLeaf8W0
import Kepler.Text.TameSpine.JcajyduAqSnd
import Kepler.Text.TameSpine.TameList34
import Kepler.Text.TameSpine.TameList35

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-- **`s2` 行覆盖**（件表 ①）：`s2` 的元都在旧环 `r` 或窗口 `w` 上。 -/
theorem aq9_rowCoverS2 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) {d : ℕ × ℕ}
    (hd : d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).2) :
    d ∈ r ∨ d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) := by
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn
    ((simpleHypermapUniq L hL hgn).mp hm.1.1.simple) hm hf
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hs2eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).2
      = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ [lYSpine L r x])
        ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) := by
    simp only [splitNormalListSpine]
    rw [hnextz1]
  rw [hs2eq] at hd
  rcases List.mem_append.mp hd with h | h
  · rcases List.mem_append.mp h with h1 | h2
    · rcases List.mem_append.mp h1 with h1 | h1
      · exact Or.inl (by rw [List.mem_singleton.mp h1]; exact hzr)
      · exact Or.inl (betwnMem h1)
    · exact Or.inl (by rw [List.mem_singleton.mp h2]; exact hyr)
  · exact Or.inr h

/-- **`s1` 行覆盖**（件表 ②）：`s1` 的元都在旧环 `r` 或结点块串 `new1` 上。 -/
theorem aq9_rowCoverS1 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) {d : ℕ × ℕ}
    (hd : d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1) :
    d ∈ r ∨ d ∈ ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (ndSpine L)).flatten := by
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hy1r : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem (ytransMemRtrans L hL hgn hm hf)
  have hz1r : prevEl r (lZSpine L N r x) ∈ r :=
    prevEl_mem_of_mem (zMemRtransClean L hL hgn
      ((simpleHypermapUniq L hL hgn).mp hm.1.1.simple) hm hf)
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hs1eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1
      = (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
        ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
    rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (prevEl r (lZSpine L N r x)), hnextz1]
  rw [hs1eq] at hd
  rcases List.mem_append.mp hd with h | h
  · exact Or.inr (List.mem_reverse.mp h)
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl (by rw [List.mem_singleton.mp h]; exact hy1r)
      · exact Or.inl (betwnMem h)
    · exact Or.inl (by rw [List.mem_singleton.mp h]; exact hz1r)

/-- **窗口双行（FST 级）**（件表 ③）：窗口任一 dart 的顶点 `v = d.1`
同时落在 `s2` 的 FST 表（`d` 本身）与 `s1` 的 FST 表（`d` 的结点块头 `nList d`，
`fstNListPower` 保持第一坐标）上。 -/
theorem aq9_windowFst (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) {v : ℕ}
    (hv : v ∈ (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (fun d => d.1)) :
    v ∈ ((splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).2).map (fun d => d.1)
      ∧ v ∈ ((splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1).map (fun d => d.1) := by
  obtain ⟨d0, hdw, hd0⟩ := List.mem_map.mp hv
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hd0L : d0 ∈ listOfDarts L := mem_darts_of_mem_findFace L (betwnMem hdw)
  have hsz : 2 ≤ (L.flatten.filter (fun t => decide (t = d0.1))).length :=
    two_le_sz_of_restricted L hL hgn hm.1.1
      (List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (betwnMem hdw)))
  have hblkne : ndSpine L d0 ≠ [] := ndSpineNeNil L d0 hsz
  have hhead : (ndSpine L d0).head! = nList L d0 := aq4_ndSpineHead L hsz
  have hfst : (nList L d0).1 = d0.1 := by
    have h := fstNListPower L hL hgn hd0L 1
    simpa using h
  have hspmem : nList L d0 ∈ ndSpine L d0 := by
    rw [← hhead]
    exact List.head!_mem_self hblkne
  have hblkmem : ndSpine L d0 ∈ (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (ndSpine L) := List.mem_map.mpr ⟨d0, hdw, rfl⟩
  have hmemnew1 : nList L d0 ∈ ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (ndSpine L)).flatten :=
    List.mem_flatten.mpr ⟨ndSpine L d0, hblkmem, hspmem⟩
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
  refine ⟨?_, ?_⟩
  · rw [hs2eq]
    exact List.mem_map.mpr ⟨d0, List.mem_append_right _ hdw, hd0⟩
  · rw [hs1eq]
    refine List.mem_map.mpr ⟨nList L d0, ?_, ?_⟩
    · exact List.mem_append_left _ (List.mem_reverse.mpr hmemnew1)
    · rw [hfst]
      exact hd0

/-- 私件：`v ∈ coreSpine row` ⇒ 行内有 dart 的第一坐标 = v（parts 头提取）。 -/
private theorem aq9_coreDart (L : fgraph ℕ) {row : List (ℕ × ℕ)} {v : ℕ}
    (hnd : row.Nodup) (hne : row ≠ []) (hv : v ∈ coreSpine L row) :
    ∃ d ∈ row, d.1 = v := by
  have hmap : v ∈ (partsSpine L row).map (fun a => a.head!.1) := hv
  obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hmap
  have hpne : p ≠ [] := partsAllNonnil L hnd hne p hp
  exact ⟨p.head!, memPartsImp L hnd hne hp p.head! (List.head!_mem_self hpne), hpv⟩

/-- **provenance**（件表 ④；HOL `CASES_CORE` 的原生等价物）：
新表 quotient 的顶点要么来自旧表 quotient，要么是窗口 dart 的第一坐标。 -/
theorem aq9_provenance (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) {v : ℕ}
    (hv : v ∈ (quotientListSpine L (ntransSpine L N r x 1)).flatten) :
    v ∈ (quotientListSpine L N).flatten
      ∨ v ∈ (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (fun d => d.1) := by
  obtain ⟨N₁, N₂, hN, _hnot, hnt⟩ := aq9_rowDecomp L hL hgn hunL hm hf
  rw [quotientListCore, List.mem_flatten] at hv
  obtain ⟨row, hrow, hvrow⟩ := hv
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hrow
  -- 旧表来源 ⇒ 左支
  have holdRow : ∀ r0 ∈ N, v ∈ coreSpine L r0 → v ∈ (quotientListSpine L N).flatten := by
    intro r0 hr0N hv0
    rw [quotientListCore]
    exact List.mem_flatten.mpr
      ⟨coreSpine L r0, List.mem_map.mpr ⟨r0, hr0N, rfl⟩, hv0⟩
  rw [hnt] at hr0
  rcases List.mem_append.mp hr0 with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl (holdRow r0 (by rw [hN]; exact List.mem_append_left (r :: N₂) h) hvrow)
      · -- r0 = s2
        rw [List.mem_singleton.mp h] at hvrow
        have hs2nd : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).2.Nodup :=
          hsndClean L hL hgn hunL hm hf
        have hs2ne : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 ≠ [] := by
          intro h0
          have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
          have : lZSpine L N r x ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
            have hs2eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
                (lYSpine L r x) (prevEl r (lZSpine L N r x))).2
                = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
                    ++ [lYSpine L r x])
                  ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                      (lZSpine L N r x) := by
              simp only [splitNormalListSpine]
              rw [nextElPrevElUniq (uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1) _]
            rw [hs2eq]
            exact List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_singleton_self _)))
          rw [h0] at this
          exact List.not_mem_nil this
        obtain ⟨d, hdrow, hd1⟩ := aq9_coreDart L hs2nd hs2ne hvrow
        rcases aq9_rowCoverS2 L hL hgn hm hf hdrow with hdr | hdw
        · refine Or.inl ?_
          have hvmap : v ∈ r.map (fun d => d.1) := List.mem_map.mpr ⟨d, hdr, hd1⟩
          exact holdRow r hm.1.2.2.1 ((memCore L hL hm.1.2.1 hm.1.2.2.1 v).mpr hvmap)
        · exact Or.inr (List.mem_map.mpr ⟨d, hdw, hd1⟩)
    · exact Or.inl (holdRow r0 (by rw [hN]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h)) hvrow)
  · -- r0 = s1
    rw [List.mem_singleton.mp h] at hvrow
    have hs1nd : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1.Nodup :=
      aq1_split1Nodup L hL hgn hunL hm hf
    have hs1ne : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 ≠ [] := by
      intro h0
      have : nextEl r (lYSpine L r x) ∈ (splitNormalListSpine L r
          (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).1 := by
        have hs1eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
            = (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                  (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
              ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
                  (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
          rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (prevEl r (lZSpine L N r x)),
            nextElPrevElUniq (uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1) _]
        rw [hs1eq]
        exact List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_singleton_self _)))
      rw [h0] at this
      exact List.not_mem_nil this
    obtain ⟨d, hdrow, hd1⟩ := aq9_coreDart L hs1nd hs1ne hvrow
    rcases aq9_rowCoverS1 L hL hgn hm hf hdrow with hdr | hnew1
    · refine Or.inl ?_
      have hvmap : v ∈ r.map (fun d => d.1) := List.mem_map.mpr ⟨d, hdr, hd1⟩
      exact holdRow r hm.1.2.2.1 ((memCore L hL hm.1.2.1 hm.1.2.2.1 v).mpr hvmap)
    · -- d ∈ new1 ⇒ fst 不变 ⇒ v 是窗口 dart 的第一坐标
      obtain ⟨blk, hblkmem, hdblk⟩ := List.mem_flatten.mp hnew1
      obtain ⟨d0, hdw0, hblkeq⟩ := List.mem_map.mp hblkmem
      have hdsp : d ∈ ndSpine L d0 := hblkeq ▸ hdblk
      have hspdef : ndSpine L d0 = (List.range' 1 ((L.flatten.filter
          (fun t => decide (t = d0.1))).length - 1)).map (fun k => (nList L)^[k] d0) := rfl
      obtain ⟨i, _hi, hdi⟩ := List.mem_map.mp (hspdef ▸ hdsp)
      have hd0L : d0 ∈ listOfDarts L := mem_darts_of_mem_findFace L (betwnMem hdw0)
      have hfst : ((nList L)^[i] d0).1 = d0.1 := fstNListPower L hL hgn hd0L i
      exact Or.inr (List.mem_map.mpr ⟨d0, hdw0, by rw [← hfst, hdi]; exact hd1⟩)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq9_rowCoverS2
#print axioms Kepler.Text.TameSpine.aq9_rowCoverS1
#print axioms Kepler.Text.TameSpine.aq9_windowFst
#print axioms Kepler.Text.TameSpine.aq9_provenance
