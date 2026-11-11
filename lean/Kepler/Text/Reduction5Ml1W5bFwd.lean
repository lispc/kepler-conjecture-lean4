/-
  Kepler.Text.Reduction5Ml1W5bFwd — W5b 第一件：`r_rtrans_eq` 正向（rtr 1 ⊆ r）+ rtr1 展开
  （HOL more_lemma1.hl:1162–:1527 的 forward 方向；逆向 min_num 块冻结见 DELIVERY_ml9）。

  件目：`rtrans1Eq`（rtr 1 = [z]++(betwn r z y++[y]) ++ betwn f y z，链形）
  + `rRtransEqFwd`（d ∈ f 且 indexf 界 ⇒ d ∈ rtr 1 → d ∈ r）。
  路线（DIFFERS，比 HOL 短）：HOL 正向经 betwn_cases + KBWPBHQ2 + min_num 定位；
  本件用 rtr1 的 dart 层展开直接二分：d ∈ f2 ⊆ r，或 d ∈ betwn f y z，后者与
  `indexf w z f ≤ indexf w d f`（f-侧 betwn 索引式）矛盾。
  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction5Ml1W5a
import Kepler.Text.Reduction5Ml1W2
import Kepler.Text.Reduction5Kbwpbhq
import Kepler.Text.Reduction5J5BetweenInst
import Kepler.Text.PwssratFace
import Kepler.Text.Reduction5BetwnBase

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList eList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- `rtrans L N r x 1` 的展开（¬final 时；`split.2` 的 `f2 ++ new2` 形）：
`rtr 1 = [z] ++ (betwn r z y ++ [y]) ++ betwn f y z`。 -/
theorem rtrans1Eq (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hnf : ¬ finalList L r) (hrnd : r.Nodup)
    (hlyf : ly L r x ∈ findFaceDarts L x) :
    rtrans L N r x 1
      = ([lz L N r x] ++ (between r (lz L N r x) (ly L r x) ++ [ly L r x]))
        ++ between (findFaceDarts L x) (ly L r x) (lz L N r x) := by
  have hnextPrev0 : @nextEl Dart instBEqOfDecidableEq r (prevEl r (lz L N r x))
      = lz L N r x :=
    Kepler.Text.Reduction5.nextPrevId hrnd _
  have hnextPrev : @nextEl Dart instBEqProd r (prevEl r (lz L N r x)) = lz L N r x := by
    rw [Kepler.Text.Reduction5.nextElInstEq r (prevEl r (lz L N r x))]
    exact hnextPrev0
  have hff : findFaceDarts L (ly L r x) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 hlyf
  show ((transformList L x)^[1] (N, r)).2 = _
  rw [Function.iterate_one]
  simp only [transformList, if_neg hnf, splitNormalList, hnextPrev, hff]

/-- **W5b 正向（HOL :1242–:1468 的结论；本轮改短路线）**：
`d ∈ f` 且 `indexf w z f ≤ indexf w d f` ⇒ `d ∈ rtr 1 → d ∈ r`。 -/
theorem rRtransEqFwd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {d : Dart} (hd : d ∈ findFaceDarts L x)
    (hle : Kepler.Text.Reduction5.indexf (nextEl (findFaceDarts L x) x)
        (lz L N r x) (findFaceDarts L x)
      ≤ Kepler.Text.Reduction5.indexf (nextEl (findFaceDarts L x) x) d
          (findFaceDarts L x)) :
    d ∈ rtrans L N r x 1 → d ∈ r := by
  intro hmem
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  obtain ⟨hlyf, hzf, hltf⟩ :=
    Kepler.Text.Reduction4Idx.pplhuljV0 L hL hgn hunL hm hnf
  obtain ⟨hlyr, hzr0, -, -, -, -, -, -, -⟩ := ml1SetupMem L hL hgn hm hnf
  have hzr : lz L N r x ∈ r := by
    simpa [Kepler.Text.Reduction5.ztrans_def, Kepler.Text.Reduction5.ntrans_zero,
      Kepler.Text.Reduction5.rtrans_zero] using hzr0
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hrt := rtrans1Eq (N := N) (r := r) (x := x) L hL hnf hrnd hlyf
  rw [hrt] at hmem
  rcases List.mem_append.mp hmem with h | h
  · -- d ∈ [z] ++ betwn r z y ++ [y] ⊆ r
    rcases List.mem_append.mp h with h | h
    · rw [List.mem_singleton] at h; subst h; exact hzr
    · rcases List.mem_append.mp h with h | h
      · have h' : d ∈ @Kepler.Graphs.between Dart instBEqOfDecidableEq r
            (lz L N r x) (ly L r x) := by
          rwa [Kepler.Text.Reduction5.betweenInstEq r (lz L N r x) (ly L r x)] at h
        exact Kepler.Text.Reduction5.betwnMem h'
      · rw [List.mem_singleton] at h; subst h; exact hlyr
  · -- d ∈ betwn f y z：与 hle 相抵
    have hfnd : (findFaceDarts L x).Nodup :=
      Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
    have hne : ly L r x ≠ lz L N r x := by
      intro hzy
      rw [hzy] at hltf
      exact absurd hltf (lt_irrefl _)
    have hff2 : d ∈ @Kepler.Graphs.between Dart instBEqOfDecidableEq
        (findFaceDarts L x) (ly L r x) (lz L N r x) := by
      rwa [Kepler.Text.Reduction5.betweenInstEq (findFaceDarts L x) (ly L r x)
        (lz L N r x)] at h
    have hb := (Kepler.Text.Reduction5.indexfBetwnEq
      (s := findFaceDarts L x) (x := ly L r x) (y := d) (z := lz L N r x)
      hne hfnd hlyf hzf).mp hff2
    have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
      Kepler.Text.TameLp.nextEl_mem_of_mem
        ((Kepler.Text.TameLp.dart_in_face L x).mpr (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm))
    have hwy : Kepler.Text.Reduction5.indexf (nextEl (findFaceDarts L x) x) (ly L r x) (findFaceDarts L x)
        ≤ Kepler.Text.Reduction5.indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x) :=
      le_of_lt (lt_of_lt_of_le hltf hle)
    have hadd1 := Kepler.Text.Reduction4.indexf_add_left hwf hlyf hd hwy
    have hadd2 := Kepler.Text.Reduction4.indexf_add_left hwf hlyf hzf (le_of_lt hltf)
    omega

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.rtrans1Eq
#print axioms Kepler.Text.Reduction5.rRtransEqFwd
