/-
  Kepler.Text.TameSpine.JcajyduAqLeaf4W3aII — AQ4 W3a-ii：`aq4_loopS1` 装配。

  两侧分件（口径见 DELIVERY）：
  ① `aq4_loopS1F1`：`f1 = [y1] ++ a1 ++ [z1]` 四支（y1 / a1 末 / a1 内 / z1），
     照 W2 配方（Cat2 入 F1 → CatLast1/Cat1 入弧 → `HD_BETWN2`/`nextLastBetwn`/`aq10` 两件套）；
  ② `aq4_loopS1New1`：`new1.reverse` 侧 = 行边界（`x = new1.head!` ⇒ `nextEl = y1`）
     / 块内（`2 ≤ i` ⇒ W3a-i A）/ 块边界（`i = 1`、`P ≠ []` ⇒ W3a-i B + W1 `aq4_blockBoundaryStep`）；
  ③ `aq4_loopS1`：两次 `List.mem_append` 装配成 `loopListSpine`。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf4W3aI

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-- **`f1` 侧的点值性质**（`s1` 行在 `f1` 各元处的 `oneStep`）。 -/
theorem aq4_loopS1F1 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ dd ∈ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
        (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]),
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
  have hra : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
    aq1_nextElYNePrevElZ L hL hgn hunL hm hf
  have hy1r : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hyr
  have hA1nd : (between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x))).Nodup :=
    uniqBetwn hrnd hy1r hz1r hra
  have hA1nil : between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)) = []
      ↔ prevEl r (lZSpine L N r x) = nextEl r (nextEl r (lYSpine L r x)) :=
    betwnNil hrnd hra hy1r hz1r
  have hWnil : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x) = []
      ↔ lZSpine L N r x = nextEl (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) :=
    betwnNil hfnd hyne hyfd hzfd
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
  have hF1nd : ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])).Nodup :=
    List.Sublist.nodup (List.sublist_append_right _ _) hRnd'
  have hYWne : (between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) ≠ [] :=
    List.ne_nil_of_mem (List.mem_append_right _ (List.mem_singleton_self _))
  have hF1last : ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])).getLast!
      = prevEl r (lZSpine L N r x) := by
    rw [getLast!AppendRight _ _ hYWne, getLast!AppendRight _ _ (by simp)]
    rfl
  have hF1ne : ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])) ≠ [] :=
    List.ne_nil_of_mem (List.mem_append_left _ (List.mem_singleton_self _))
  have hheadF1Y : (between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]).head!
      = nextEl r (nextEl r (lYSpine L r x)) := by
    by_cases hA1 : between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)) = []
    · rw [hA1, List.nil_append, hA1nil.mp hA1]; rfl
    · rw [List.head!_append _ hA1]
      exact HD_BETWN2 hy1r hz1r hra hrnd hA1
  intro dd hdF1
  rw [hRform] at ⊢
  have hF1form : ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])
      = [nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
          (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
    simp only [List.append_assoc]
  rw [hF1form] at hdF1
  rcases List.mem_append.mp hdF1 with hdY1 | hdAZ
  · -- ① dd = y1
    obtain rfl := List.mem_singleton.mp hdY1
    refine ⟨(hloop _ hy1r).1, ?_⟩
    have hstep1 : nextEl ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
        ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])))
        (nextEl r (lYSpine L r x))
        = nextEl ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))
          (nextEl r (lYSpine L r x)) := by
      refine nextElCat2 hRnd' (List.mem_append_left _ (List.mem_singleton_self _)) ?_
      intro hcon
      rw [hF1last] at hcon
      exact hra hcon
    have hstep2 : nextEl ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
          (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))
        (nextEl r (lYSpine L r x))
        = (between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x))
            ++ [prevEl r (lZSpine L N r x)]).head! :=
      nextElCatLast1 hF1nd (by simp) hYWne
    rw [hstep1, hstep2, hheadF1Y]
    exact (hloop _ hy1r).2
  · rcases List.mem_append.mp hdAZ with hdA1 | hdZ1
    · -- ②③ dd ∈ a1
      have hxr : dd ∈ r := betwnMem hdA1
      have hA1ne : between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)) ≠ [] :=
        List.ne_nil_of_mem hdA1
      refine ⟨(hloop dd hxr).1, ?_⟩
      have hstep1 : nextEl ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
          ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
              (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))) dd
          = nextEl ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
              (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])) dd := by
        refine nextElCat2 hRnd' (List.mem_append_right _ (List.mem_append_left _ hdA1)) ?_
        intro hcon
        rw [hF1last] at hcon
        exact (notBetwn2 hrnd) (hcon ▸ hdA1)
      have hstep2 : nextEl ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])) dd
          = nextEl (between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x))
              ++ [prevEl r (lZSpine L N r x)]) dd := by
        have hz1last : (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]).getLast!
            = prevEl r (lZSpine L N r x) := by
          rw [getLast!AppendRight _ _ (by simp)]
          rfl
        refine nextElCat2 (s := [nextEl r (lYSpine L r x)])
          (t := between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])
          hF1nd (List.mem_append_left _ hdA1) ?_
        intro hcon
        rw [hz1last] at hcon
        exact (notBetwn2 hrnd) (hcon ▸ hdA1)
      rw [hstep1, hstep2]
      by_cases hdl : dd = (between r (nextEl r (lYSpine L r x))
          (prevEl r (lZSpine L N r x))).getLast!
      · have hstep3 : nextEl (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) dd
            = prevEl r (lZSpine L N r x) := by
          rw [hdl]
          exact nextElCatLast1 (List.Sublist.nodup (List.sublist_append_right _ _) hF1nd)
            hA1ne (by simp)
        rw [hstep3]
        have hdlast : (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x))).getLast hA1ne = dd := by
          rw [← getLast!EqGetLast hA1ne]; exact hdl.symm
        have hny : nextEl r dd = prevEl r (lZSpine L N r x) := by
          rw [← hdlast, nextLastBetwn hy1r hz1r hrnd hra hA1ne]
        have hone : oneStepListSpine L dd (nextEl r dd) := (hloop dd hxr).2
        rw [hny] at hone
        exact hone
      · have hstep3 : nextEl (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) dd
            = nextEl (between r (nextEl r (lYSpine L r x))
                (prevEl r (lZSpine L N r x))) dd :=
          nextElCat1 hA1nd hdA1 hdl
        rw [hstep3]
        have hlastne : (between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x))).getLast hA1ne ≠ dd := by
          intro hcon
          exact hdl (by rw [getLast!EqGetLast hA1ne]; exact hcon.symm)
        have hnextmem : nextEl r dd ∈ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) :=
          (aq10_eqMemNextElLast hra hy1r hz1r hdA1 hrnd).mpr hlastne
        rw [aq10_nextElBetwnSame hra hy1r hz1r hdA1 hnextmem hrnd]
        exact (hloop dd hxr).2
    · -- ④ dd = z1（行末）
      obtain rfl := List.mem_singleton.mp hdZ1
      refine ⟨(hloop _ hz1r).1, ?_⟩
      have hRlast : ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
          ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
              (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))).getLast!
          = prevEl r (lZSpine L N r x) := by
        rw [getLast!AppendRight _ _ hF1ne, hF1last]
      have hy1s1 : nextEl r (lYSpine L r x)
          ∈ ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
            ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
                (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))) :=
        List.mem_append_right _
          (List.mem_append_left _ (List.mem_singleton_self _))
      have hs1ne : ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
          ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
              (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))) ≠ [] :=
        List.ne_nil_of_mem hy1s1
      have hstep : nextEl ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
          ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
              (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])))
          (prevEl r (lZSpine L N r x))
          = ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
            ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
                (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))).head! := by
        have h := nextElLast hRnd' hs1ne
        rw [hRlast] at h
        exact h
      rw [hstep]
      by_cases hnew1nil : (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten).reverse = []
      · -- new1 = [] ⇒ s1 = F1，head = nextEl r y1
        have hhead : ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
            ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
                (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))).head!
            = nextEl r (lYSpine L r x) := by
          rw [hnew1nil, List.nil_append]
          exact List.head!_append _ (by simp)
        rw [hhead]
        -- 窗口空 ⇒ z = nextEl f y1 = fList y1
        have hw0 : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x) = [] := by
          by_contra hwne
          obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil _ hwne
          have hne : ndSpine L d0 ≠ [] := ndSpineNeNil L d0
            (two_le_sz_of_restricted L hL hgn hm.1.1
              (List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (betwnMem hd0))))
          have hblkmem : ndSpine L d0 ∈ (between (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (lZSpine L N r x)).map (ndSpine L) :=
            List.mem_map.mpr ⟨d0, hd0, rfl⟩
          obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ hne
          have hne1 : (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).map (ndSpine L)).flatten).reverse ≠ [] := by
            intro h0
            exact List.ne_nil_of_mem (List.mem_flatten.mpr ⟨ndSpine L d0, hblkmem, hx0⟩)
              (List.reverse_eq_nil_iff.mp h0)
          exact hne1 hnew1nil
        have hzfl : lZSpine L N r x = nextEl (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) := hWnil.mp hw0
        have hzy : lZSpine L N r x = fList L (lYSpine L r x) := by rw [hzfl]; rfl
        -- 末元 z1 的环走步：z = fList z1 ∨ z = fList (eList z1)；fList 单射 ⇒
        --   z1 = y1 或 z1 = eList y1；两种情形都由 y1 处的环走步直接收口
        have hz1L : prevEl r (lZSpine L N r x) ∈ listOfDarts L :=
          normalListListOfDarts hm.1.2.1 _
            (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hz1r⟩)
        have honez1 := (hloop _ hz1r).2
        rw [nextElPrevElUniq hrnd (lZSpine L N r x)] at honez1
        rcases honez1 with h1 | h1
        · have hz1a : prevEl r (lZSpine L N r x) = lYSpine L r x := by
            have hfe : fList L (prevEl r (lZSpine L N r x)) = fList L (lYSpine L r x) := by
              rw [← h1, hzy]
            exact (fListInjDarts L hL hz1L hyL).mp hfe
          rw [hz1a]
          exact (hloop _ hyr).2
        · have her : eList (prevEl r (lZSpine L N r x)) = lYSpine L r x := by
            have hfe : fList L (eList (prevEl r (lZSpine L N r x)))
                = fList L (lYSpine L r x) := by
              rw [← h1, hzy]
            exact (fListInjDarts L hL (goodListEList hL hz1L) hyL).mp hfe
          have hz1ea : prevEl r (lZSpine L N r x) = eList (lYSpine L r x) := by
            rw [← her, eList_eList]
          rw [hz1ea]
          rcases (hloop _ hyr).2 with h | h
          · exact Or.inr (by rw [eList_eList]; exact h)
          · exact Or.inl h
      · -- new1 ≠ []：head = new1.getLast! = fList z1
        have hhead : ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
            ++ ([nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
                (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]))).head!
            = fList L (prevEl r (lZSpine L N r x)) := by
          rw [List.head!_append _ hnew1nil]
          rw [head!Reverse]
          have hwne : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x) ≠ [] := by
            by_contra hw0
            exact hnew1nil (by
              rw [hw0]; simp)
          have hlastwin := lastWindowEqEListZ1 L hL hgn hunL hm hf (hne := hwne)
          exact lastNew1EqFList L hL hgn hwne
            (fun e he => List.mem_toFinset.mpr <| mem_darts_of_mem_findFace L (betwnMem he))
            (fun e he => two_le_sz_of_restricted L hL hgn hm.1.1
              (List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (betwnMem he))))
            hlastwin
        rw [hhead]
        refine Or.inl rfl

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq4_loopS1F1
