/-
  Kepler.Text.TameSpine.JcajyduAqLeaf4W2 — AQ4 W2：行 `s2 = f2 ++ new2` 的 `loopListSpine`。

  `s2 = ([z] ++ betwn r z y ++ [y]) ++ betwn (findFaceDarts L y) y z`，
  `y = lYSpine L r x`、`z = lZSpine L N r x`。目标 = 逐点
  `d ∈ listOfDarts L ∧ oneStepListSpine L d (nextEl s2 d)`。

  ┌─ 内部规范形 ────────────────────────────────────────────────
  │ 证明内部统一换成右结合形
  │ `R = [z] ++ (a2 ++ ([y] ++ w))`（`hRform`，`List.append_assoc`），
  │ 于是全部 `nextElCat*` 调用的 `s`/`t` 都直接对上；只在 ⑥ 临时改回
  │ 左结合形 `([z] ++ (a2 ++ [y])) ++ w`（CatLast2 需要）。

  ┌─ 六支 ──────────────────────────────────────────────────────
  │ ① d = z（行头）：a2 ≠ [] ⇒ nextEl = a2.head! = nextEl r z（`HD_BETWN2`）；
  │    a2 = [] ⇒ nextEl = y（`betwnNil` 给 `y = nextEl r z`）。
  │ ② d ∈ a2 内部：Cat2([z]→T) + Cat1(a2→[y]++w) + 弧连续
  │    （`aq10_eqMemNextElLast` + `aq10_nextElBetwnSame`，载体 r）⇒ nextEl = nextEl r d。
  │ ③ d = a2 末（a2 ≠ []）：Cat2 + CatLast1 ⇒ nextEl = y；`nextLastBetwn` 给旧环一步。
  │ ④ d = y：w = [] ⇒ `nextElLast` 给 nextEl = head R = z，而 z = fList y
  │    （`betwnNil`）；w ≠ [] ⇒ Cat2 + Cat2 + CatLast1 ⇒ nextEl = w.head! =
  │    nextEl f y（`HD_BETWN2`）⇒ `aq4_oneStepFindFace`。
  │ ⑤ d ∈ w 内部：Cat2 ×3 ⇒ nextEl = nextEl w d = nextEl f d（面弧连续）⇒
  │    `aq4_oneStepFindFace`。
  │ ⑥ d = w 末（w ≠ []）：CatLast2 ⇒ nextEl = head R = z；
  │    `lastWindowEqEListZ1` + `prevRNotEqF` + 旧环在 z1 = prevEl r z 的一步 ⇒
  │    z = fList (w.getLast!)。

  引擎：`aq4_oneStepFindFace`（W1）、`hsndClean`（行 Nodup）、`HD_BETWN2`/
  `nextLastBetwn`/`betwnNil`/`nextElLast`、`aq10_eqMemNextElLast`/`aq10_nextElBetwnSame`、
  `nextElCat1/2/Last1/Last2`、`betwnNotInRtrans`、`lastWindowEqEListZ1`、`prevRNotEqF`。
  **不含 `aq4Concl` 本体（W3）**；槽冻结；零新增定义。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf4W1

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-- **W2：行 `s2` 的 `loopListSpine`**（HOL AQ4 证体的 `SND split` 半）。 -/
theorem aq4_loopS2 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    loopListSpine L (([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x)) := by
  have hunL : ∀ l ∈ L, l.Nodup := (simpleHypermapUniq L hL hgn).mp hm.1.1.simple
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  have hyL : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hzfd : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hzL : lZSpine L N r x ∈ listOfDarts L := mem_darts_of_mem_findFace L hzfd
  have hfnd : (findFaceDarts L (lYSpine L r x)).Nodup := findFaceDarts_nodup hL.1 _
  have hyfd : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L _).mpr hyL
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  -- 行 Nodup
  have hs2eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).2
      = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x])
        ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) := by
    simp only [splitNormalListSpine]
    rw [nextElPrevElUniq hrnd _]
  have hs2nd : (([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x)).Nodup := by
    rw [← hs2eq]
    exact hsndClean L hL hgn hunL hm hf
  -- 弧/窗口事实
  have ha2nd : (between r (lZSpine L N r x) (lYSpine L r x)).Nodup :=
    uniqBetwn hrnd hzr hyr (Ne.symm hyne)
  have hyNotA2 : lYSpine L r x ∉ between r (lZSpine L N r x) (lYSpine L r x) :=
    notBetwn2 hrnd
  have hwNotR : ∀ d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x), d ∉ r :=
    fun d hd => betwnNotInRtrans L hL hgn hunL hm hf hd
  have hWnd : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).Nodup := uniqBetwn hfnd hyfd hzfd hyne
  have hA2nil : between r (lZSpine L N r x) (lYSpine L r x) = []
      ↔ lYSpine L r x = nextEl r (lZSpine L N r x) :=
    betwnNil hrnd (Ne.symm hyne) hzr hyr
  have hWnil : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x) = []
      ↔ lZSpine L N r x = nextEl (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) :=
    betwnNil hfnd hyne hyfd hzfd
  -- 规范形（右结合）
  have hRform : (([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (lZSpine L N r x))
      = [lZSpine L N r x] ++ (between r (lZSpine L N r x) (lYSpine L r x)
        ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (lZSpine L N r x))) := by
    simp only [List.append_assoc]
  have hRnd : ([lZSpine L N r x] ++ (between r (lZSpine L N r x) (lYSpine L r x)
      ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x)))).Nodup := hRform ▸ hs2nd
  have hTnd : (between r (lZSpine L N r x) (lYSpine L r x)
      ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x))).Nodup :=
    List.Sublist.nodup (List.sublist_append_right _ _) hRnd
  have hYWnd : ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (lZSpine L N r x)).Nodup :=
    List.Sublist.nodup (List.sublist_append_right _ _) hTnd
  have hYWne : ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (lZSpine L N r x)) ≠ [] :=
    List.ne_nil_of_mem (List.mem_append_left _ (List.mem_singleton_self _))
  have hTne : (between r (lZSpine L N r x) (lYSpine L r x)
      ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x))) ≠ [] :=
    List.ne_nil_of_mem (List.mem_append_right _ (List.mem_append_left _
      (List.mem_singleton_self _)))
  have hRne : ([lZSpine L N r x] ++ (between r (lZSpine L N r x) (lYSpine L r x)
      ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x)))) ≠ [] :=
    List.ne_nil_of_mem (List.mem_append_left _ (List.mem_singleton_self _))
  -- `T.getLast!` 的两支
  have hTlastW : ∀ (hw : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x) ≠ []),
      (between r (lZSpine L N r x) (lYSpine L r x)
        ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (lZSpine L N r x))).getLast!
      = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).getLast! := by
    intro hw
    rw [getLast!AppendRight _ _ hYWne, getLast!AppendRight _ _ hw]
  have hLastA2Y : ∀ (a : List (ℕ × ℕ)),
      (a ++ [lYSpine L r x]).getLast! = lYSpine L r x := by
    intro a
    rw [getLast!AppendRight _ _ (by simp)]
    rfl
  have hHeadYW : ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (lZSpine L N r x)).head! = lYSpine L r x :=
    List.head!_append _ (by simp)
  have hTlastE : ∀ (hw : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x) = []),
      (between r (lZSpine L N r x) (lYSpine L r x) ++ ([lYSpine L r x]
        ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x))).getLast! = lYSpine L r x := by
    intro hw
    rw [hw, List.append_nil, hLastA2Y]
  -- 主证明（转规范形）
  intro d hd
  rw [hRform] at hd ⊢
  rcases List.mem_append.mp hd with hdZ | hdA
  · -- ① d = z
    obtain rfl := List.mem_singleton.mp hdZ
    refine ⟨hzL, ?_⟩
    have hstep : nextEl ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
          (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
            (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))))
        (lZSpine L N r x)
        = (between r (lZSpine L N r x) (lYSpine L r x) ++ ([lYSpine L r x]
          ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x))).head! :=
      nextElCatLast1 hRnd (by simp) hTne
    rw [hstep]
    by_cases hA2 : between r (lZSpine L N r x) (lYSpine L r x) = []
    · have hth : (between r (lZSpine L N r x) (lYSpine L r x) ++ ([lYSpine L r x]
          ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x))).head! = lYSpine L r x := by
        rw [hA2, List.nil_append]
        exact hHeadYW
      rw [hth, hA2nil.mp hA2]
      exact (hloop _ hzr).2
    · have hth : (between r (lZSpine L N r x) (lYSpine L r x) ++ ([lYSpine L r x]
          ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x))).head!
          = (between r (lZSpine L N r x) (lYSpine L r x)).head! :=
        List.head!_append _ hA2
      rw [hth, HD_BETWN2 hzr hyr (Ne.symm hyne) hrnd hA2]
      exact (hloop _ hzr).2
  · rcases List.mem_append.mp hdA with hdA2 | hdYW
    · -- ②③ d ∈ a2
      have hdr : d ∈ r := betwnMem hdA2
      have hA2ne : between r (lZSpine L N r x) (lYSpine L r x) ≠ [] :=
        List.ne_nil_of_mem hdA2
      refine ⟨(hloop d hdr).1, ?_⟩
      have hTlast_ne : d ≠ (between r (lZSpine L N r x) (lYSpine L r x)
          ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (lZSpine L N r x))).getLast! := by
        by_cases hw : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x) = []
        · intro hcon
          rw [hTlastE hw] at hcon
          rw [hcon] at hdA2
          exact hyNotA2 hdA2
        · intro hcon
          rw [hTlastW hw, getLast!EqGetLast hw] at hcon
          rw [hcon] at hdr
          exact hwNotR _ (List.getLast_mem hw) hdr
      have hstep1 : nextEl ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
            (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
              (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)))) d
          = nextEl (between r (lZSpine L N r x) (lYSpine L r x)
            ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (lZSpine L N r x))) d :=
        nextElCat2 hRnd (List.mem_append_left _ hdA2) hTlast_ne
      rw [hstep1]
      by_cases hdl : d = (between r (lZSpine L N r x) (lYSpine L r x)).getLast!
      · -- ③ d = a2 末 ⇒ nextEl = y
        have hstep2 : nextEl (between r (lZSpine L N r x) (lYSpine L r x)
              ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
                (lYSpine L r x) (lZSpine L N r x))) d = lYSpine L r x := by
          rw [hdl]
          exact nextElCatLast1 hTnd hA2ne hYWne
        rw [hstep2]
        have hdlast : (between r (lZSpine L N r x) (lYSpine L r x)).getLast hA2ne
            = d := by
          rw [← getLast!EqGetLast hA2ne]; exact hdl.symm
        have hny : nextEl r d = lYSpine L r x := by
          rw [← hdlast, nextLastBetwn hzr hyr hrnd (Ne.symm hyne) hA2ne]
        have hone : oneStepListSpine L d (nextEl r d) := (hloop d hdr).2
        rw [hny] at hone
        exact hone
      · -- ② d ∈ a2 内部 ⇒ nextEl = nextEl r d
        have hstep2 : nextEl (between r (lZSpine L N r x) (lYSpine L r x)
              ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
                (lYSpine L r x) (lZSpine L N r x))) d
            = nextEl (between r (lZSpine L N r x) (lYSpine L r x)) d :=
          nextElCat1 ha2nd hdA2 hdl
        rw [hstep2]
        have hlastne : (between r (lZSpine L N r x) (lYSpine L r x)).getLast hA2ne
            ≠ d := by
          intro hcon
          exact hdl (by rw [getLast!EqGetLast hA2ne]; exact hcon.symm)
        have hnextmem : nextEl r d ∈ between r (lZSpine L N r x) (lYSpine L r x) :=
          (aq10_eqMemNextElLast (Ne.symm hyne) hzr hyr hdA2 hrnd).mpr hlastne
        rw [aq10_nextElBetwnSame (Ne.symm hyne) hzr hyr hdA2 hnextmem hrnd]
        exact (hloop d hdr).2
    · rcases List.mem_append.mp hdYW with hdY | hdW
      · -- ④ d = y
        obtain rfl := List.mem_singleton.mp hdY
        refine ⟨hyL, ?_⟩
        by_cases hw : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x) = []
        · -- w = []：y 是整行末元，nextEl = head = z
          have hRnne : (between r (lZSpine L N r x) (lYSpine L r x)
              ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
                (lYSpine L r x) (lZSpine L N r x))) ≠ [] :=
            List.ne_nil_of_mem (List.mem_append_right _ (List.mem_append_left
              (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)) (List.mem_singleton_self _)))
          have hRlast : ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
              (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
                (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)))).getLast!
              = lYSpine L r x := by
            rw [getLast!AppendRight _ _ hRnne, hTlastE hw]
          have hRhead : ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
              (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
                (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)))).head!
              = lZSpine L N r x := List.head!_append _ (by simp)
          have hstep : nextEl ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
                (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
                  (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))))
              (lYSpine L r x) = lZSpine L N r x := by
            have h1 : nextEl ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
                (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
                  (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))))
                (lYSpine L r x)
                = nextEl ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
                  (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
                    (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))))
                  (([lZSpine L N r x] ++ (between r (lZSpine L N r x)
                    (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
                      (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)))).getLast!) := by
              rw [hRlast]
            rw [h1, nextElLast hRnd hRne, hRhead]
          rw [hstep]
          refine Or.inl ?_
          rw [hWnil.mp hw]
          rfl
        · -- w ≠ []：y 是 T 内 [y] 段首，nextEl = w.head! = fList y
          have hstep1 : nextEl ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
                (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
                  (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))))
              (lYSpine L r x)
              = nextEl (between r (lZSpine L N r x) (lYSpine L r x)
                ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
                  (lYSpine L r x) (lZSpine L N r x))) (lYSpine L r x) := by
            refine nextElCat2 hRnd (List.mem_append_right _ (List.mem_append_left
              (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)) (List.mem_singleton_self _))) ?_
            intro hcon
            rw [hTlastW hw] at hcon
            exact hwNotR _ (List.getLast_mem hw) (by
              rw [show (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).getLast hw = lYSpine L r x from by
                rw [← getLast!EqGetLast hw]; exact hcon.symm]
              exact hyr)
          rw [hstep1]
          have hstep2 : nextEl (between r (lZSpine L N r x) (lYSpine L r x)
                ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
                  (lYSpine L r x) (lZSpine L N r x))) (lYSpine L r x)
              = nextEl ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
                  (lYSpine L r x) (lZSpine L N r x)) (lYSpine L r x) := by
            refine nextElCat2 hTnd (List.mem_append_left (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)) (List.mem_singleton_self _)) ?_
            intro hcon
            rw [getLast!AppendRight _ _ hw] at hcon
            exact hwNotR _ (List.getLast_mem hw) (by
              rw [show (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).getLast hw = lYSpine L r x from by
                rw [← getLast!EqGetLast hw]; exact hcon.symm]
              exact hyr)
          rw [hstep2]
          have hstep3 : nextEl ([lYSpine L r x] ++ between (findFaceDarts L
                (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)) (lYSpine L r x)
              = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).head! := nextElCatLast1 hYWnd (by simp) hw
          rw [hstep3]
          have hfw : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).head! = nextEl (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) :=
            HD_BETWN2 hyfd hzfd hyne hfnd hw
          rw [hfw]
          exact aq4_oneStepFindFace L hL hyL hyfd
      · -- ⑤⑥ d ∈ w
        have hdL : d ∈ listOfDarts L := mem_darts_of_mem_findFace L (betwnMem hdW)
        have hdfd : d ∈ findFaceDarts L (lYSpine L r x) := betwnMem hdW
        have hwne : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x) ≠ [] := List.ne_nil_of_mem hdW
        refine ⟨hdL, ?_⟩
        by_cases hdlw : d = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).getLast!
        · -- ⑥ d = w 末 ⇒ nextEl = z（临时改回左结合形）
          have hRnd2 : (([lZSpine L N r x] ++ (between r (lZSpine L N r x)
              (lYSpine L r x) ++ [lYSpine L r x])) ++ between (findFaceDarts L
                (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).Nodup := by
            simp only [List.append_assoc]
            exact hRnd
          have hF2ne : ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
              (lYSpine L r x) ++ [lYSpine L r x])) ≠ [] :=
            List.ne_nil_of_mem (List.mem_append_left _ (List.mem_singleton_self _))
          have hstep : nextEl ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
                (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
                  (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)))) d
              = lZSpine L N r x := by
            rw [show ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
                (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
                  (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))))
                = ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
                  (lYSpine L r x) ++ [lYSpine L r x])) ++ between (findFaceDarts L
                    (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) from by
              simp only [List.append_assoc]]
            rw [hdlw]
            exact (nextElCatLast2 hRnd2 hF2ne hwne).trans
              (List.head!_append _ (by simp))
          rw [hstep]
          have hz1z : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
            nextElPrevElUniq hrnd _
          have hone : oneStepListSpine L (prevEl r (lZSpine L N r x))
              (nextEl r (prevEl r (lZSpine L N r x))) := (hloop _ hz1r).2
          rw [hz1z] at hone
          have hzlast : lZSpine L N r x
              = fList L (eList (prevEl r (lZSpine L N r x))) := by
            rcases hone with h | h
            · exact absurd h.symm (prevRNotEqF L hL hgn hunL hm hf)
            · exact h
          have hlastwin : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).getLast hwne
              = eList (prevEl r (lZSpine L N r x)) :=
            lastWindowEqEListZ1 L hL hgn hunL hm hf
          refine Or.inl ?_
          rw [hdlw, getLast!EqGetLast hwne, hlastwin]
          exact hzlast
        · -- ⑤ d ∈ w 内部 ⇒ nextEl = fList d
          have hstep1 : nextEl ([lZSpine L N r x] ++ (between r (lZSpine L N r x)
                (lYSpine L r x) ++ ([lYSpine L r x] ++ between (findFaceDarts L
                  (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)))) d
              = nextEl (between r (lZSpine L N r x) (lYSpine L r x)
                ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
                  (lYSpine L r x) (lZSpine L N r x))) d := by
            refine nextElCat2 hRnd (List.mem_append_right _ (List.mem_append_right _
              hdW)) ?_
            intro hcon
            rw [hTlastW hwne] at hcon
            exact hdlw hcon
          rw [hstep1]
          have hstep2 : nextEl (between r (lZSpine L N r x) (lYSpine L r x)
                ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
                  (lYSpine L r x) (lZSpine L N r x))) d
              = nextEl ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
                  (lYSpine L r x) (lZSpine L N r x)) d := by
            refine nextElCat2 hTnd (List.mem_append_right _ hdW) ?_
            intro hcon
            rw [getLast!AppendRight _ _ hwne] at hcon
            exact hdlw hcon
          rw [hstep2]
          have hstep3 : nextEl ([lYSpine L r x] ++ between (findFaceDarts L
                (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)) d
              = nextEl (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                  (lZSpine L N r x)) d :=
            nextElCat2 hYWnd hdW hdlw
          rw [hstep3]
          have hlastne : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).getLast hwne ≠ d := by
            intro hcon
            exact hdlw (by rw [getLast!EqGetLast hwne]; exact hcon.symm)
          have hnextmem : nextEl (findFaceDarts L (lYSpine L r x)) d
              ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                (lZSpine L N r x) :=
            (aq10_eqMemNextElLast hyne hyfd hzfd hdW hfnd).mpr hlastne
          rw [aq10_nextElBetwnSame hyne hyfd hzfd hdW hnextmem hfnd]
          exact aq4_oneStepFindFace L hL hyL hdfd

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq4_loopS2
