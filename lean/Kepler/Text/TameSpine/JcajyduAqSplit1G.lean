/-
  Kepler.Text.TameSpine.JcajyduAqSplit1G — E4d-a-4：**f_last 四支本体**
  （`fLastSplit1`：`split.1` 的 `f_last` 全装配）。

  目标（工单 + 前任交接备注 DELIVERY §E4d-a-3 §2 六步清单）：
  `fLastSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
     (lYSpine L r x) (prevEl r (lZSpine L N r x))).1`

  支序（备注 §6 建议：先否证 `ra = z1`，再按 `new1` 空/非空分流）：
  ① 段1 展开/末元：`split.1 = new1.reverse ++ f1`，`getLast! split.1 = z1`
     （`split1Unfold` + `nextElPrevElUniq` + `getLast!AppendRight`）；
  ② 段3 `ra = z1` **否证**：`z1 = fList (eList y)`（loop + `nextRNotEqF`）与
     `z = fList (eList z1)`（loop + `prevRNotEqF` + `nextElPrevElUniq`）经
     `nodeMapSymmEqFList` 翻成 `nodeMap z = z1`、`nodeMap z1 = y`，故
     `y ∈ node z` 且 `node y = node z`；配 `z ∈ face y`（`faceTableSubset`）后
     由 `simpleHypermapList` 的 `node ∩ face = {y}` 塌出 `z = y`，撞
     `hqymrtx3List`（HOL 用 `FST_EQ_NEXT/PREV_ZTRANS` + `QRDYXYJ_list`；
     本文件改走 node 轨道 + Simple，同结论、零 Skolem 参、零 sorryAx——
     `qrdyxyjList` 需 `IsMarked`，其唯一供给 `markedListMarked` 吃
     `markedListIsNodeNondegenerate` 的在案债，**不可消费**）
     —— **ERRATA（2026-11-10）**：`TameList16:1109` 已真证（`967ebbb5`），
     `markedListMarked`/`markedListIsNodeNondegenerate` 现均标准三、零 sorryAx，
     「不可消费」已作废；本文件保留原路线（同结论，已落库，不回溯改写证明）。
  ③ 段2 `ra ≠ z1` × `new1 ≠ []`：`z1 ∉ new1.reverse`（`z1NotMemNew1`）+
     `f1.idxOf z1 = len−1`（`idxOfF1OfNe`）⇒ `split.1.idxOf z1 = len−1`
     ⇒ `nextEl = head!`（`nextElOfIdxLast`）⇒ `head! = LAST new1`
     （`List.head!_append` + `head!Reverse`）⇒ `lastNew1EqFList`
     （`lastWindowEqEListZ1` 供 `d1 = eList z1`）；
  ④ 段4 空窗支（`new1 = []` ⇒ `new2 = []`）：`split.1 = f1`、
     `nextEl f1 z1 = ra`（`nextElF1Z1OfNe`）；`betwnNilNextOfNodup`（面侧）
     给 `fList y = z`，两面 loop 二择一（`nextRNotEqF`/`prevRNotEqF` 排除）
     给 `ra = fList (eList y)`、`z = fList (eList z1)` ⇒ `fListInjDarts` 得
     `y = eList z1` ⇒ `ra = fList z1`。

  边界：本文件只做 split.1（`aq3Concl` 两槽装配归下一件 E4d-b）。
  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqSplit1F
import Kepler.Text.TameCorrCard

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts listPairs)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-! ## §0 小件：单元素 `getLast!` -/

/-- `[a].getLast! = a`。 -/
private theorem getLast!_singleton {α : Type*} [Inhabited α] (a : α) :
    ([a] : List α).getLast! = a := rfl

/-! ## §1 f_last 本体（四支装配） -/

/-- **AQ3 split.1 支的 `f_last`**（HOL `AQ23.hl:263-:266` 陈述 + `:269` 起证明体的 split.1 支（`:359`））：
`f_last L (split_normal_list …).1`，即新环 `r' = rtrans … 1`（= split.2）之外
`ntrans … 1` 的 split.1 成员也满足 normal_list 合取 3。 -/
theorem fLastSplit1 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    fLastSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
  -- §0 前提打包
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L _).mpr hyd
  have hzf : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L (lYSpine L r x)).Nodup := findFaceDarts_nodup hL.1 _
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  -- 两面 loop 合流（与 `ra` 无关，段3/段4 共用）
  have hny : nextEl r (lYSpine L r x) = fList L (eList (lYSpine L r x)) := by
    rcases (hloop (lYSpine L r x) hyr).2 with h1 | h1
    · exact absurd h1 (nextRNotEqF L hL hgn hunL hm hf)
    · exact h1
  have hz1e : lZSpine L N r x = fList L (eList (prevEl r (lZSpine L N r x))) := by
    rcases (hloop (prevEl r (lZSpine L N r x)) hz1r).2 with h1 | h1
    · rw [hnextz1] at h1
      exact absurd h1.symm (prevRNotEqF L hL hgn hunL hm hf)
    · rw [hnextz1] at h1
      exact h1
  -- §1 段1：展开与末元
  have hsplit : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
      = ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten.reverse
        ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
    rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (prevEl r (lZSpine L N r x)), hnextz1]
  have hget : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1.getLast!
      = prevEl r (lZSpine L N r x) := by
    rw [hsplit, getLast!AppendRight _ _ (by simp)]
    rw [getLast!AppendRight _ _ (by simp)]
    exact getLast!_singleton _
  unfold fLastSpine
  rw [hget]
  -- §2 支序：先否证 ra = z1
  by_cases hra : nextEl r (lYSpine L r x) = prevEl r (lZSpine L N r x)
  · -- 段3：ra = z1 ⇒ 矛盾（node 合流 + Simple 塌缩）
    exfalso
    have hzd : lZSpine L N r x ∈ listOfDarts L :=
      normalListListOfDarts hm.1.2.1 (lZSpine L N r x)
        (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hzr⟩)
    have hz1d : prevEl r (lZSpine L N r x) ∈ listOfDarts L := (hloop _ hz1r).1
    have hDz : lZSpine L N r x ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hzd
    have hDz1 : prevEl r (lZSpine L N r x) ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr hz1d
    have hDy : lYSpine L r x ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hyd
    -- nodeMap z = z1
    have hsymm1 : (hypermapOfList L hL).nodeMap.symm (prevEl r (lZSpine L N r x))
        = lZSpine L N r x := by
      rw [nodeMapSymmEqFList L hL hDz1]
      exact hz1e.symm
    have hnmapz : (hypermapOfList L hL).nodeMap (lZSpine L N r x)
        = prevEl r (lZSpine L N r x) := by
      have h := congrArg (hypermapOfList L hL).nodeMap hsymm1
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    -- nodeMap z1 = y
    have hsymmy : (hypermapOfList L hL).nodeMap.symm (lYSpine L r x)
        = prevEl r (lZSpine L N r x) := by
      rw [nodeMapSymmEqFList L hL hDy]
      exact hny.symm.trans hra
    have hnmaps1 : (hypermapOfList L hL).nodeMap (prevEl r (lZSpine L N r x))
        = lYSpine L r x := by
      have h := congrArg (hypermapOfList L hL).nodeMap hsymmy
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    -- y ∈ node z（nodeMap 二次幂）
    have hyn : lYSpine L r x ∈ (hypermapOfList L hL).node (lZSpine L N r x) := by
      rw [(hypermapOfList L hL).mem_node_iff (lZSpine L N r x) (lYSpine L r x)]
      refine ⟨2, ?_⟩
      rw [pow_two, Equiv.Perm.mul_apply, hnmapz, hnmaps1]
    have hnodeq : (hypermapOfList L hL).node (lZSpine L N r x)
        = (hypermapOfList L hL).node (lYSpine L r x) :=
      (hypermapOfList L hL).node_eq_of_mem hyn
    have hzn : lZSpine L N r x ∈ (hypermapOfList L hL).node (lYSpine L r x) := by
      rw [← hnodeq]
      exact (hypermapOfList L hL).mem_node_self _
    have hzf2 : lZSpine L N r x ∈ (hypermapOfList L hL).face (lYSpine L r x) :=
      Kepler.Text.TameCorrCard.faceTableSubset hL hyd hzf
    have hsimple := simpleHypermapList L hL hgn hunL
    have hinter : lZSpine L N r x ∈ (hypermapOfList L hL).node (lYSpine L r x)
        ∩ (hypermapOfList L hL).face (lYSpine L r x) := ⟨hzn, hzf2⟩
    rw [hsimple (lYSpine L r x) hDy] at hinter
    exact hyz (Set.mem_singleton_iff.mp hinter).symm
  · -- §3 ra ≠ z1：按 new1 空/非空分流
    by_cases hnew1 : ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).map (ndSpine L)).flatten = []
    · -- 段4：空窗支
      have hnil2 : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x) = [] := by
        by_contra hne
        obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
        have hdarts : d ∈ (hypermapOfList L hL).darts :=
          List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (memBetweenOfMem hd))
        have hbne : ndSpine L d ≠ [] :=
          ndSpineNeNil L d (two_le_sz_of_restricted L hL hgn hm.1.1 hdarts)
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hbne
        have hmem : e ∈ ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten :=
          List.mem_flatten.mpr ⟨ndSpine L d, List.mem_map.mpr ⟨d, hd, rfl⟩, he⟩
        rw [hnew1] at hmem
        exact List.not_mem_nil hmem
      have hsplitF1 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
          = [nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
              (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)] := by
        rw [hsplit, hnil2]
        simp
      have hflY : fList L (lYSpine L r x) = lZSpine L N r x := by
        show nextEl (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) = lZSpine L N r x
        exact betwnNilNextOfNodup hfnd hyf hzf hyz hnil2
      have hinq : lYSpine L r x = eList (prevEl r (lZSpine L N r x)) := by
        have h1 : fList L (lYSpine L r x)
            = fList L (eList (prevEl r (lZSpine L N r x))) := hflY.trans hz1e
        exact (fListInjDarts L hL hyd (hL.2.2 _ ((hloop _ hz1r).1))).mp h1
      rw [hsplitF1, nextElF1Z1OfNe hrnd hra, hny, hinq, eList_eList]
    · -- 段2：new1 ≠ []，nextEl split.1 z1 = head! split.1 = LAST new1 = fList z1
      have hneNew : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x) ≠ [] := by
        intro h0
        exact hnew1 (by rw [h0]; simp)
      have hmemN : ∀ d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x), d ∈ (hypermapOfList L hL).darts := by
        intro d hd
        exact List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (memBetweenOfMem hd))
      have hsz2 : ∀ d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x), 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length := by
        intro d hd
        exact two_le_sz_of_restricted L hL hgn hm.1.1 (hmemN d hd)
      have hzlast : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).getLast hneNew
          = eList (prevEl r (lZSpine L N r x)) :=
        lastWindowEqEListZ1 L hL hgn hunL hm hf
      have hlastNew1 : ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten.getLast!
          = fList L (prevEl r (lZSpine L N r x)) :=
        lastNew1EqFList L hL hgn hneNew hmemN hsz2 hzlast
      have hnotmem : prevEl r (lZSpine L N r x) ∉
          ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten.reverse := by
        rw [List.mem_reverse]
        exact z1NotMemNew1 L hL hgn hunL hm hf
      have hidxf1 : ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
          (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]).idxOf
            (prevEl r (lZSpine L N r x))
          = ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]).length - 1 :=
        idxOfF1OfNe hrnd hra
      have hidxSplit : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1.idxOf
            (prevEl r (lZSpine L N r x))
          = (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).1.length - 1 := by
        rw [hsplit, List.idxOf_append_of_notMem hnotmem, hidxf1, List.length_append]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hne1 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 ≠ [] := by
        rw [hsplit]
        simp
      have hrevne : ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten.reverse ≠ [] := by
        simpa using hnew1
      have hhead : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1.head!
          = fList L (prevEl r (lZSpine L N r x)) := by
        rw [hsplit, List.head!_append _ hrevne, head!Reverse, hlastNew1]
      rw [nextElOfIdxLast hne1 hidxSplit, hhead]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.fLastSplit1
