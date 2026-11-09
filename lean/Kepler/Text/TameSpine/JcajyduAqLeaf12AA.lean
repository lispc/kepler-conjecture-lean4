/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12AA — AQ12 叶 W-F3e-iii（12AA，F 支）。

  HOL：AQ12.hl:3780-:4084 主证 `flag_list` 第二合取的 **F 支**（r' = FST split）。
  按 62 `cat_fst_split_normal_parts`，`p ∈ parts F` 二分：
  ① 窗口块支 `p = (ndSpine L d).reverse`（`d ∈ between f l'y l'z`）；
  ② f1 支 `p ∈ partsSpine L f1`（`f1 = [nextEl r l'y] ++ betwn r (nextEl r l'y) (prevEl r l'z) ++ [prevEl r l'z]`）。

  ┌─ 本件范围：**① 窗口块支**（12AA-i，HOL 3780-3869，~90 行）──────
  │ y = LAST (ndSpine d).reverse = HEAD (ndSpine d) = nList L d（decl 63）
  │ ⇒ eList y = prevEl (findFace d) d（findFace d = findFace x）
  │ ⇒ 证 prevEl (findFace x) d ∈ SND（final 行）：
  │   d ∈ SND（窗口 = SND 的 new2 尾段）；
  │   e := prevEl SND d ∈ SND（`prevEl_mem_of_mem`）；
  │   nextEl SND e = d（`nextElPrevElUniq` + `hsndClean`）；
  │   final SND 给 fList e = d；`prevEl_nextEl` ⇒ prevEl (findFace e) d = e；
  │   findFace e = findFace d（e ∈ SND ⊆ r∪face x 两支）⇒ e = prevEl (findFace d) d。
  │ ⇒ eList y = e ∈ SND ⊆ FinalDart N'（SND ∈ ntrans 1 + final SND）。
  └────────────────────────────────────────────────────────────────
  ┌─ ② f1 支（HOL 3870-4084，~215 行）→ **12AA-ii**（另发）────────
  │ 需要 HOL 的五路 case split（lp = LAST p1 / p ∈ parts r / lp = LAST f1 /
  │ lp = LAST r / y1 = z1）+ 66 两次 + FST_EQ/QRDYXYJ/nextCatBetwnSame/
  │ F_LIST_INJ/prevRNotEqF。本件**不宣称 F 支收口**。
  └────────────────────────────────────────────────────────────────

  不吃 `h4`。纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；
  主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12U
import Kepler.Text.TameSpine.JcajyduAqLeaf8W0
import Kepler.Text.TameSpine.JcajyduAqSnd
import Kepler.Text.TameSpine.JcajyduAqLeaf4W1
import Kepler.Text.TameSpine.JcajyduAqSplit1B

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList nList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face mem_darts_of_mem_findFace
  findFaceDarts_nodup nextEl_mem_of_mem prevEl_mem_of_mem prevEl_nextEl)

/-! ## §0 列表末元私件 -/

/-- `l.reverse.getLast! = l.head!`（`l ≠ []`）。 -/
private theorem aq12aa_getLast!_reverse {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.reverse.getLast! = l.head! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_reverse, List.head!_eq_head?_getD]

/-! ## §1 F 支 ①：窗口块（`p = (ndSpine d).reverse`） -/

/-- **HOL AQ12.hl:3780-:3869（F 支 · 窗口块半）**：
`p` 是窗口 `betwn f l'y l'z` 中某块 `ndSpine d` 的反序，
则 `eList (LAST p) ∈ FinalDartList (ntrans 1)`（经 final 行 SND）。 -/
theorem aq12aa_flagConjunctTwoFBlock (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hfinRtrans : finalListSpine L (rtransSpine L N r x 1))
    {p : List (ℕ × ℕ)}
    (hp : p ∈ ((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
      (fun d => (ndSpine L d).reverse)).reverse) :
    eList (p.getLast!) ∈ FinalDartListSpine L (ntransSpine L N r x 1) := by
  obtain ⟨d, hdW, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp)
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hdD : d ∈ listOfDarts L := mem_darts_of_mem_findFace L (betwnMem hdW)
  have h2d : 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length :=
    two_le_sz_of_restricted L hL hgn hm.1.1 (List.mem_toFinset.mpr hdD)
  -- LAST ((ndSpine d).reverse) = HEAD (ndSpine d) = nList d
  have hblk : ndSpine L d ≠ [] := ndSpineNeNil L d h2d
  have hlast : ((ndSpine L d).reverse).getLast! = nList L d := by
    rw [aq12aa_getLast!_reverse hblk, aq4_ndSpineHead L h2d]
  rw [hlast, aqs_eListNList]
  -- S = SND（f-split），final；d ∈ S；e = prevEl S d ∈ S
  set S := (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
    (prevEl r (lZSpine L N r x))).2 with hSdef
  have hfaceY : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hS2 : S = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) ++ between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x) := by
    rw [hSdef]
    simp only [splitNormalListSpine]
    rw [hnextz1]
  have hdSND : d ∈ S := by
    rw [hS2]
    exact List.mem_append.mpr (Or.inr hdW)
  have hSnd : S.Nodup := by
    have h := hsndClean L hL hgn hunL hm hf
    rw [hfaceY] at h
    rwa [hSdef]
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 = S := by
    rw [hSdef, hfaceY]
  have hmemS : S ∈ ntransSpine L N r x 1 := by
    rw [← hsplit_eq]
    exact sndMemRtran1 L hm.1.2.2.1 hf
  have hrtrans : rtransSpine L N r x 1 = S := by
    show ((transformListSpine L x)^[1] (N, r)).2 = _
    rw [Function.iterate_one]
    simp only [transformListSpine, if_neg hf]
    rw [hsplit_eq]
  have hfinS : finalListSpine L S := by
    rw [← hrtrans]
    exact hfinRtrans
  -- e := prevEl S d ∈ S，且 nextEl S e = d，fList e = d（final S）
  have heS : prevEl S d ∈ S := prevEl_mem_of_mem hdSND
  have hnext : nextEl S (prevEl S d) = d := nextElPrevElUniq hSnd d
  have hfl : fList L (prevEl S d) = d := by
    have h := hfinS (prevEl S d) heS
    rwa [hnext] at h
  -- e ∈ listOfDarts：S = ([z]++betwn r z y++[y]) ++ new2，两段各给
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hSsub : ∀ e ∈ S, e ∈ listOfDarts L := by
    intro e he
    rw [hS2] at he
    rcases List.mem_append.mp he with hin | hin
    · have hr : e ∈ r := by
        rcases List.mem_append.mp hin with h1 | h1
        · rcases List.mem_append.mp h1 with hz | hb
          · rw [List.mem_singleton] at hz
            rw [hz]; exact hzr
          · exact betwnMem hb
        · rw [List.mem_singleton] at h1
          rw [h1]; exact hyr
      exact normalListListOfDarts hm.1.2.1 _
        (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hr⟩)
    · exact mem_darts_of_mem_findFace L (betwnMem hin)
  have heD : prevEl S d ∈ listOfDarts L := hSsub _ heS
  -- findFace e = findFace d（fList e = d ⇒ d ∈ findFace e）
  have hnf : nextEl (findFaceDarts L (prevEl S d)) (prevEl S d) = d := by
    show fList L (prevEl S d) = d
    exact hfl
  have hdface : d ∈ findFaceDarts L (prevEl S d) := by
    have h := nextEl_mem_of_mem ((dart_in_face L (prevEl S d)).mpr heD)
    exact Eq.mp (congrArg (fun t => t ∈ findFaceDarts L (prevEl S d)) hnf) h
  have heface : findFaceDarts L (prevEl S d) = findFaceDarts L d :=
    (aq10_memFindFaceImpFacesEq hL.1 hdface).symm
  -- prevEl (findFace d) d = e
  have hprevEq : prevEl (findFaceDarts L d) d = prevEl S d := by
    have hbase : prevEl (findFaceDarts L (prevEl S d))
        (nextEl (findFaceDarts L (prevEl S d)) (prevEl S d)) = prevEl S d :=
      prevEl_nextEl (findFaceDarts_nodup hL.1 (prevEl S d))
        ((dart_in_face L (prevEl S d)).mpr heD)
    rw [hnf, heface] at hbase
    exact hbase
  -- eList y = prevEl (findFace d) d = e ∈ S ⊆ FinalDart
  rw [hprevEq]
  exact List.mem_flatten.mpr
    ⟨S, List.mem_filter.mpr ⟨hmemS, by simpa using hfinS⟩, heS⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq12aa_flagConjunctTwoFBlock
