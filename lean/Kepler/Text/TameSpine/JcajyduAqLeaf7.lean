/-
  Kepler.Text.TameSpine.JcajyduAqLeaf7 — AQ 塔（jcajydu J2 批 E）第 7 叶：
  AQ7 真证。

  锚：reference/flyspeck/text_formalization/tame/AQ7.hl:206 `AQ7_concl`
  = `!L N r (x:A#A). good_list L /\ good_list_nodes L /\
  marked_list L N r x ==> MEM x (rtrans L N r x 1)`
  ——marked_list 九合取之第 4 块（MEM x r'）。

  Lean 陈述（TowerBase:270 `aq7Concl`，**陈述冻结**）：
  `∀ N r x, GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    x ∈ rtransSpine L N r x 1`。

  ┌─ 证明结构（HOL :213-:275 的 Lean 对应）─────────────────────────
  │ ① final 支：`rtrans_id` 退化到 `MEM x r`（marked_list 合取 4）。
  │ ② ¬final 支：`rtrans_cat`（JcajyduRed2Trans:171 已落库）把一步
  │    rtrans 展开为
  │      (([z] ++ betwn r z y) ++ [y]) ++ betwn f y z，
  │    y = l'y、z = l'z、f = find_face y（z 与 y 均在 r 上）。
  │ ③ 对 (z, x, y) 用 `betwn_cases`（TameList3:1167）：x = z /
  │    x = y / x ∈ betwn r z y / x ∈ betwn r y z 四支；前三支直接
  │    落在 f2 段 `([z] ++ betwn r z y) ++ [y]` 内。
  │ ④ 第四支不可能（本文件 §1 `aq7_notMemBetweenYZ`，= HOL
  │    :259-:275 的 indexf 计数矛盾）。
  └────────────────────────────────────────────────────────────────

  ┌─ 上游复用（零重复造轮；三 helper 已由 AQ10-a2 批落库 26314655）──
  │ · transform 单步结构：`rtransCat`（JcajyduRed2Trans:171）；
  │ · z 侧干净件：`zMemRtransClean` / `hyneSupply`
  │   （JcajyduAqZUnlock:397/:422，标准三，零 sorryAx）；
  │ · AQ7.hl 三 helper 的 Lean 孪生（不重落，直接消费）：
  │   `aq10_indexfYtransEqLm1`（AQ7.hl:39）、`aq10_indexfConstLe`
  │   （AQ7.hl:128）、`aq10_indexfYLeZInR0`（AQ7.hl:181）；
  │ · betwn/indexf 全族：TameList3 §1/§7（betwnCases / indexfBetwn /
  │   indexfAddBetwn / indexfAddLeft / indexfAddRight / indexfPrev /
  │   indexfLtSizel）。
  │ 债：TameList16:1109 已真证（967ebbb5），本叶零消费 sorryAx 链
  │（本轮 `#print axioms` 复核，见文件尾探针）。
  └────────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.TameSpine.JcajyduAqTowerBase
import Kepler.Text.TameSpine.JcajyduAqZUnlock
import Kepler.Text.TameSpine.JcajyduAqLeaf10

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl fList GoodList findFaceDarts)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (GoodListNodesTl)

/-! ## §1 HOL AQ7.hl:255-:275 的算术核：`x ∈ betwn r y z` 不可能

HOL 原证（:255-:275）取 `betwn_cases` 的第三支后做 indexf 计数：
`indexf_betwn` 给 `0 < i y x` 且 `i y x < i y z`；
`indexf_add_betwn` 给 `i y x + i x z = i y z`（故 `0 < i x z`）；
`indexf_y_le_z_in_r_0` 给 `i w y < i w z`，`indexf_add_left` 给
`i w y + i y z = i w z`，`indexf_add_right` 给 `i w x + i x z = i w z`
（故 `i w x < i w z`）；`indexf_prev`（`next_el r x = w`）给
`i w x = sizel r - 1`，`indexf_lt_sizel` 给 `i w z < sizel r`——矛盾。 -/

/-- **AQ7 计数核**：`~final_list L r` 时 `x ∉ between r (l'y) (l'z)`
（`w = next_el (find_face x) x`）。 -/
theorem aq7_notMemBetweenYZ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    x ∉ between r (lYSpine L r x) (lZSpine L N r x) := by
  intro hbetween
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hxr := hm.1.2.2.2.1
  have hnd : r.Nodup := (normalListUniqNonnil hn hrN).1
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyne : lYSpine L r x ≠ lZSpine L N r x :=
    hyneSupply L hL hgn hunL hm hf
  have hwr : nextEl (findFaceDarts L x) x ∈ r := aq10_nextMarkMemRTrans L hL hgn hm
  -- `next_el r x = w`（marked_list 合取 6；`fList` 展开即 `next_el (find_face x)`）
  have hnext : nextEl r x = nextEl (findFaceDarts L x) x := hm.1.2.2.2.2.2.1
  -- ① `0 < i(y,x) < i(y,z)`
  have hb1 := indexfBetwn (s := r) (x := lYSpine L r x) (y := x)
    (z := lZSpine L N r x) hyne hnd hyr hzr hbetween
  -- ② `i(y,x) + i(x,z) = i(y,z)`，故 `0 < i(x,z)`
  have hb2 := indexfAddBetwn (s := r) (x := lYSpine L r x) (y := x)
    (z := lZSpine L N r x) hyne hnd hyr hbetween hzr
  have hxz : 0 < indexf x (lZSpine L N r x) r := by omega
  -- ③ `i(w,y) < i(w,z)`；`i(w,y) + i(y,z) = i(w,z)`
  have hb3 := aq10_indexfYLeZInR0 L hL hgn hm hf
  have hb4 := indexfAddLeft (s := r) (x := nextEl (findFaceDarts L x) x)
    (y := lYSpine L r x) (z := lZSpine L N r x) hwr hyr hzr (Nat.le_of_lt hb3)
  -- ④ `i(x,z) ≤ i(w,z)`，故 `i(w,x) + i(x,z) = i(w,z)`
  have hle : indexf x (lZSpine L N r x) r
      ≤ indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) r := by omega
  have hb5 := indexfAddRight (s := r) (x := nextEl (findFaceDarts L x) x)
    (y := x) (z := lZSpine L N r x) hwr hxr hzr hle
  -- ⑤ `i(w,x) = sizel r - 1`，`i(w,z) < sizel r`——矛盾
  have hb6 := indexfPrev (s := r) (x := x) (y := nextEl (findFaceDarts L x) x)
    hxr hwr hnd hnext
  have hb7 := indexfLtSizel (s := r) (x := nextEl (findFaceDarts L x) x)
    (y := lZSpine L N r x) hwr hzr
  have hpos : 0 < r.length := List.length_pos_of_mem hxr
  omega

/-! ## §2 AQ7 主证（HOL AQ7.hl:213-:275） -/

/-- **HOL `AQ7`**（AQ7.hl:213）：`good_list L ∧ good_list_nodes L ∧
marked_list L N r x ==> x ∈ rtrans L N r x 1`——marked_list 第 4 合取块。 -/
theorem aq7 (L : fgraph ℕ) (hL : GoodList L) : aq7Concl L hL := by
  intro N r x hgn hm
  by_cases hfin : finalListSpine L r
  · -- final 支：rtrans 恒等，x ∈ r 即结论
    rw [rtransId L N r x hfin]
    exact hm.1.2.2.2.1
  · -- ¬final 支：rtrans_cat 展开为 (([z] ++ betwn r z y) ++ [y]) ++ betwn f y z
    have hn := hm.1.2.1
    have hrN := hm.1.2.2.1
    have hxr := hm.1.2.2.2.1
    have hnd : r.Nodup := (normalListUniqNonnil hn hrN).1
    have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
    have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hfin
    have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hfin
    have hyne : lYSpine L r x ≠ lZSpine L N r x :=
      hyneSupply L hL hgn hunL hm hfin
    rw [rtransCat L N r x hfin hnd]
    -- 只需落在前半段 f2 = ([z] ++ betwn r z y) ++ [y]
    refine List.mem_append.mpr (Or.inl ?_)
    rcases betwnCases (s := r) (x := lZSpine L N r x) (y := x)
        (z := lYSpine L r x) hyne.symm hnd hzr hxr hyr with h | h | h | h
    · -- x = z：落在 [z]
      exact List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inl (List.mem_singleton.mpr h))))
    · -- x = y：落在 [y]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr h))
    · -- x ∈ betwn r z y：落在第二段
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
    · -- x ∈ betwn r y z：被 §1 计数核排除
      exact absurd h (aq7_notMemBetweenYZ L hL hgn hm hfin)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 `[propext, Classical.choice,
Quot.sound]` 的子集，零 sorryAx——本文件零消费 TameList16:1109 债链，
三 helper 与 z 侧两件均于 967ebbb5 / 26314655 批次转干净。） -/
#print axioms Kepler.Text.TameSpine.aq7_notMemBetweenYZ
#print axioms Kepler.Text.TameSpine.aq7
