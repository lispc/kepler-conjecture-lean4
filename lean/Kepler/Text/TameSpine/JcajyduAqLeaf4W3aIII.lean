/-
  Kepler.Text.TameSpine.JcajyduAqLeaf4W3aIII — AQ4 W3a-iii：`aq4_loopS1New1` + `aq4_loopS1` 总装。

  件表：
  ① `aq4_loopS1New1`：`s1` 行在 `new1.reverse` 段全部元处的 `loopListSpine` 合取。
     内部支：Cat1（`s := new1.reverse`，`hx2 := dd ≠ new1.head!`）+ `la7_nextEl_reverse`
     归约到 `prevEl new1 dd`；`x = (nList)^i d` 三分：
       A（`2 ≤ i`）→ W3a-i `aq4_prevElNew1Interior` + `aq4_nodeMapSymmPow` / `nodeMapSymmEqFList`；
       B（`i = 1 ∧ d ≠ head w`）→ `aq4_prevElNew1BlockHead` + `aq4_prevElBetwnOfNeHead`
         + W1 `aq4_blockBoundaryStep`；
       C（`i = 1 ∧ d = head w`）⇒ `dd = new1.head!`，与内部前提矛盾（二分已排除）。
     行边界支（`dd = new1.reverse.getLast! = new1.head!`）：`nextElCatLast1` ⇒ `nextEl = nextEl r a`；
     `dd = eList a`（`HD_BETWN2` 反向 `prevEl_nextEl`）⇒ a 处环走步 + `nextRNotEqF`。
  ② `aq4_loopS1`：`s1 = new1.reverse ++ f1` 的 `loopListSpine` 总装
     （`List.mem_append` 两支：本件 ① + W3a-ii `aq4_loopS1F1`）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf4W3aII

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-- **`new1.reverse` 段的点值性质**（`s1` 行在 new1 段各元处的 `oneStep`）。 -/
theorem aq4_loopS1New1 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ dd ∈ (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).map (ndSpine L)).flatten).reverse,
      dd ∈ listOfDarts L ∧ oneStepListSpine L dd
        (nextEl ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
          ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
              (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])) dd) := by
  have hunL : ∀ l ∈ L, l.Nodup := (simpleHypermapUniq L hL hgn).mp hm.1.1.simple
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  have hyL : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hzfd : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L (lYSpine L r x)).Nodup := findFaceDarts_nodup hL.1 _
  have hyfd : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L _).mpr hyL
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hy1r : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hyr
  have hwnd : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).Nodup := uniqBetwn hfnd hyfd hzfd hyne
  have hs1eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1
      = (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
        ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
    rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (prevEl r (lZSpine L N r x)), nextElPrevElUniq hrnd _]
  have hR1nd : ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
      ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
          (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])).Nodup := by
    rw [← hs1eq]
    exact aq1_split1Nodup L hL hgn hunL hm hf
  have hRform : ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
      ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
          (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))
      = (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
        ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])) := by
    simp only [List.append_assoc]
  have hRnd' : ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
      ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
          (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))).Nodup :=
    hRform ▸ hR1nd
  have hF1ne : ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])) ≠ [] :=
    List.ne_nil_of_mem (List.mem_append_left _ (List.mem_singleton_self _))
  have hnew1nd : (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (ndSpine L)).flatten).Nodup :=
    List.nodup_reverse.mp (List.Sublist.nodup (List.sublist_append_left _ _) hR1nd)
  intro dd hd
  rw [hRform] at ⊢
  have hdnew1 : dd ∈ (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (ndSpine L)).flatten) := List.mem_reverse.mp hd
  have hwne : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x) ≠ [] := by
    intro h0
    rw [h0] at hdnew1
    simp at hdnew1
  have hsz1 : 2 ≤ (L.flatten.filter (fun t => decide (t = ((between
      (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).head!).1))).length :=
    two_le_sz_of_restricted L hL hgn hm.1.1
      (List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (betwnMem (List.head!_mem_self hwne))))
  have hnew1head : (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (ndSpine L)).flatten).head!
      = (ndSpine L ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).head!)).head! := by
    have hwcons : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).head!
        :: (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).tail
        = between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x) := List.cons_head!_tail hwne
    conv_lhs => rw [← hwcons, List.map_cons, List.flatten_cons]
    exact List.head!_append _ (ndSpineNeNil L _ hsz1)
  by_cases hb : dd = ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).map (ndSpine L)).flatten).reverse).getLast!
  · -- ① 行边界：dd = new1.head!，nextEl = F1.head! = nextEl r a
    have hrevne : ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).map (ndSpine L)).flatten).reverse) ≠ [] := by
      intro h0
      rw [h0] at hd
      exact List.not_mem_nil hd
    have hstep : nextEl (((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten).reverse)
        ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))) dd
        = nextEl r (lYSpine L r x) := by
      rw [hb]
      exact nextElCatLast1 hRnd' hrevne hF1ne
    have heqea : dd = eList (lYSpine L r x) := by
      have hddhead : dd = (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten).head! := by
        rw [hb, lastRev]
      have hnList : nList L ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).head!)
          = eList (prevEl (findFaceDarts L ((between (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (lZSpine L N r x)).head!))
            ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).head!)) := rfl
      rw [hddhead, hnew1head, aq4_ndSpineHead L hsz1, hnList]
      rw [HD_BETWN2 hyfd hzfd hyne hfnd hwne]
      rw [findFaceDarts_congr_of_mem hL.1 hyL (nextEl_mem_of_mem hyfd)]
      rw [Kepler.Text.TameLp.prevEl_nextEl hfnd hyfd]
    refine ⟨by
      rw [heqea]
      exact goodListEList hL hyL, ?_⟩
    rw [hstep, heqea]
    rcases (hloop _ hyr).2 with h | h
    · exact absurd h (nextRNotEqF L hL hgn hunL hm hf)
    · exact Or.inl h
  · -- ② 内部：Cat1 + la7 归约到 prevEl new1
    have hstep1 : nextEl (((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten).reverse)
        ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))) dd
        = nextEl ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).reverse) dd :=
      nextElCat1 (List.Sublist.nodup (List.sublist_append_left _ _) hR1nd) hd hb
    have hstep2 : nextEl ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten).reverse) dd
        = prevEl (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten) dd :=
      Kepler.Text.TameLp.la7_nextEl_reverse hnew1nd hdnew1
    rw [hstep1, hstep2]
    -- 块分解：dd = (nList)^i d，1 ≤ i ≤ sz-1
    obtain ⟨blk, hblkmem, hddblk⟩ := List.mem_flatten.mp hdnew1
    obtain ⟨d, hdw, hblkeq⟩ := List.mem_map.mp hblkmem
    have hddsp : dd ∈ ndSpine L d := hblkeq ▸ hddblk
    have hdDarts : d ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (betwnMem hdw))
    have hdL : d ∈ listOfDarts L := List.mem_toFinset.mp hdDarts
    have h2d : 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length :=
      two_le_sz_of_restricted L hL hgn hm.1.1 hdDarts
    have hspdef : ndSpine L d = (List.range' 1 ((List.filter (fun t => decide (t = d.1))
        (List.flatten L)).length - 1)).map (fun k => (nList L)^[k] d) := rfl
    obtain ⟨i, hi, hdd⟩ := List.mem_map.mp (hspdef ▸ hddsp)
    obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_range'.mp hi
    have hi1 : 1 ≤ i := by omega
    have hi2 : i ≤ (List.filter (fun t => decide (t = d.1)) (List.flatten L)).length - 1 := by
      omega
    have hddDarts : dd ∈ (hypermapOfList L hL).darts := by
      have hnode : dd ∈ (hypermapOfList L hL).node d := by
        rw [Kepler.Text.Hypermap.mem_node_iff]
        exact ⟨i, by rw [← hdd, nListPowEqNodeMapPow L hL hdL i]⟩
      exact (hypermapOfList L hL).node_subset_darts hdDarts hnode
    refine ⟨List.mem_toFinset.mp hddDarts, ?_⟩
    by_cases hi1e : i = 1
    · -- i = 1：d = head w ⇒ 矛盾（dd = new1.head!）；否则 B
      by_cases hdw1 : d = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).head!
      · exfalso
        apply hb
        have hddhead : dd = (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).head! := by
          rw [← hdd, hi1e, Function.iterate_one, hdw1, hnew1head,
            aq4_ndSpineHead L hsz1]
        rw [hddhead, lastRev]
      · -- B：块边界
        obtain ⟨P, Q, hwP⟩ := List.append_of_mem hdw
        have hP : P ≠ [] := by
          intro hP0
          apply hdw1
          rw [hwP, hP0, List.nil_append]
          rfl
        have hblkne : ∀ e ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x), 2 ≤ (L.flatten.filter (fun t => decide (t = e.1))).length :=
          fun e he => two_le_sz_of_restricted L hL hgn hm.1.1
            (List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (betwnMem he)))
        have hblkDart : ∀ e ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x), e ∈ (hypermapOfList L hL).darts :=
          fun e he => List.mem_toFinset.mpr
            (mem_darts_of_mem_findFace L (betwnMem he))
        have hprevB : prevEl (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten) ((ndSpine L d).head!)
            = (ndSpine L (prevEl (between (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (lZSpine L N r x)) d)).getLast! :=
          aq4_prevElNew1BlockHead L hL hgn hwP hP hwnd hnew1nd h2d hblkne hblkDart
        have hhead1 : nList L d = (ndSpine L d).head! := (aq4_ndSpineHead L h2d).symm
        have hprevDarts : prevEl (between (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (lZSpine L N r x)) d ∈ (hypermapOfList L hL).darts :=
          List.mem_toFinset.mpr (mem_darts_of_mem_findFace L
            (betwnMem (prevEl_mem_of_mem hdw)))
        have h2prevDarts : 2 ≤ (L.flatten.filter (fun t => decide
            (t = (prevEl (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)) d).1))).length :=
          two_le_sz_of_restricted L hL hgn hm.1.1 hprevDarts
        have hfacePrev : prevEl (findFaceDarts L d) d
            = prevEl (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                (lZSpine L N r x)) d := by
          rw [findFaceDarts_congr_of_mem hL.1 hyL (betwnMem hdw)]
          exact (aq4_prevElBetwnOfNeHead hfnd hyfd hzfd hyne hdw hdw1).symm
        rw [← hdd, hi1e, Function.iterate_one, hhead1, hprevB]
        exact aq4_blockBoundaryStep L hL hgn hdDarts h2d hprevDarts h2prevDarts hfacePrev
    · -- A：块内（2 ≤ i）
      have hi2' : 2 ≤ i := by omega
      have hprevA : prevEl (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten) ((nList L)^[i] d)
          = (nList L)^[i - 1] d :=
        aq4_prevElNew1Interior L hL hgn hdw hnew1nd hdDarts h2d hi2' hi2
      rw [← hdd] at hddDarts ⊢
      rw [hprevA]
      refine Or.inr ?_
      rw [← nodeMapSymmEqFList L hL hddDarts]
      rw [nListPowEqNodeMapPow L hL hdL (i - 1), nListPowEqNodeMapPow L hL hdL i]
      exact (aq4_nodeMapSymmPow L hL (d := d) hdDarts (i := i) (by omega)).symm

/-- **`s1` 行总装**（`new1.reverse` 段 ① + `f1` 段 W3a-ii）。 -/
theorem aq4_loopS1 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    loopListSpine L ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
      ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
          (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])) := by
  intro dd hd
  rcases List.mem_append.mp hd with h | h
  · exact aq4_loopS1New1 L hL hgn hm hf dd h
  · exact aq4_loopS1F1 L hL hgn hm hf dd h

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq4_loopS1New1
#print axioms Kepler.Text.TameSpine.aq4_loopS1
