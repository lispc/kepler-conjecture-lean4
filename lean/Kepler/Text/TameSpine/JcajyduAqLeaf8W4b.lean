/-
  JcajyduAqLeaf8W4b — AQ8 波 4b：W4 的 **f1 containment 细化**（`aq8w3z_partsSubArcRefine` 的 f1 变体）。

  HOL 锚：AQ8.hl:2512-2571 / 3011-3070（GSUBGOAL#3 的两份同形证体）。
  目标：`u ∈ parts f1`、`u` 的元素全在 `r` ⇒
  `∃ p ∈ parts L r, (∀ a ∈ u, a ∈ p) ∧ (u.head!).1 = (p.head!).1`。

  ┌─ 件（1 主 + 3 几何）──────────────────────────────────────────
  │ ① `aq8w4b_f1Nodup` / `aq8w4b_f1Nonnil` / `aq8w4b_f1SubsetR`
  │    f1 段几何（`aq8w4aF1`；`partRefineFst` 已用同证，本波公开化供 W4c）。
  │ ② `aq8w4b_partsSubArcRefineF1`  w3z 五步照搬：
  │    ① `d = HD u ∈ f1 ⊆ r` → `partsMemExists` 取 p ∋ d；
  │    ② 任意 `a ∈ u` → `partsMemExists` 取 p1 ∋ a；
  │    ③ `partsFst` ×3 ⇒ `(p1.head!).1 = (p.head!).1`；
  │    ④ r-side 单射（`hm.1.2.2.2.2.1` 的 quotient + `nodup_map_iff_inj_on`）
  │       ⇒ `p1 = p` ⇒ `a ∈ p`；
  │    ⑤ `partsFst` ×2 ⇒ 头 FST 相等。
  └────────────────────────────────────────────────────────────────
  ┌─ DIFFERS（对 w3z）────────────────────────────────────────────
  │ w3z 用 `SND ∈ ntrans 1` 直接取 `partsFst`（parts of a normal row）。
  │ f1 不是 normal list 的行 ⇒ 本波经 **12W `aq12w_catFstSplitNormalParts`**
  │ 把 `u ∈ parts f1` 提升为 `u ∈ parts FST`，再吃 `FST ∈ ntrans 1`
  │ （`aq8w2b_fstMemRtran1` + `aqs_aqNormalList` + aq1..aq5 定理）。
  └────────────────────────────────────────────────────────────────

  hF1 债务：本波 + W4a ⇒ `hF1 : uniq (map headFst (parts f1))` 只剩
  **f1-part 单射**（W4c）；containment 与 r-side 单射已齐。
  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W4a
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1a
import Kepler.Text.TameSpine.JcajyduAqLeaf1F
import Kepler.Text.TameSpine.JcajyduAqTowerE2
import Kepler.Text.TameSpine.JcajyduAqSplit1H
import Kepler.Text.TameSpine.JcajyduAqLeaf4W3b
import Kepler.Text.TameSpine.JcajyduAqLeaf5
import Kepler.Text.TameSpine.JcajyduAqLeaf8W2b
import Kepler.Text.TameSpine.JcajyduBetwnMap
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.JcajyduAqSnd

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList nList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face mem_darts_of_mem_findFace
  findFaceDarts_nodup nextEl_mem_of_mem prevEl_mem_of_mem)

/-! ## §1 f1 段几何（公开化供 W4c） -/

/-- `f1.Nodup`。 -/
theorem aq8w4b_f1Nodup (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (aq8w4aF1 L N r x).Nodup := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hY1r : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hyr
  have hZ1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hY1Z1 : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
    aq1_nextElYNePrevElZ L hL hgn hunL hm hf
  show ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
    (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]).Nodup
  exact uniqAppendBetwn hrnd hY1r hZ1r hY1Z1

/-- `f1 ≠ []`。 -/
theorem aq8w4b_f1Nonnil (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) : aq8w4aF1 L N r x ≠ [] := by
  show ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
    (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) ≠ []
  simp

/-- `f1 ⊆ r`。 -/
theorem aq8w4b_f1SubsetR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ a ∈ aq8w4aF1 L N r x, a ∈ r := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hY1r : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hyr
  have hZ1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  intro a ha
  have h : a ∈ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
    (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := ha
  rcases List.mem_append.mp h with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · rw [List.mem_singleton] at h2
      rw [h2]; exact hY1r
    · exact betwnMem h2
  · rw [List.mem_singleton] at h1
    rw [h1]; exact hZ1r

/-! ## §2 f1 containment 细化（w3z 五步） -/

/-- **f1 的 containment 细化**（w3z f1 变体）：
`u ∈ parts f1`、`u ⊆ r` ⇒ 存在包含 `u` 的 r-part `p`，且头 FST 相等。 -/
theorem aq8w4b_partsSubArcRefineF1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {u : List (ℕ × ℕ)} (hu : u ∈ partsSpine L (aq8w4aF1 L N r x))
    (hur : ∀ a ∈ u, a ∈ r) :
    ∃ p ∈ partsSpine L r, (∀ a ∈ u, a ∈ p) ∧ (u.head!).1 = (p.head!).1 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnR : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hnR hrN
  have hf1nd : (aq8w4aF1 L N r x).Nodup := aq8w4b_f1Nodup L hL hgn hm hf
  have hf1ne : aq8w4aF1 L N r x ≠ [] := aq8w4b_f1Nonnil L N r x
  -- hnN：ntrans 1 是 normal list；FST ∈ ntrans 1；u ∈ parts FST（经 12W）
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL (aq1 L hL) (aq2 L hL) (aq3 L hL) (aq4 L hL) (aq5 L hL) hgn hm
  have hfaceY : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1
  have hsplitF : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
      = (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1 := by
    rw [hfaceY]
  have hFmem : (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).1 ∈ ntransSpine L N r x 1 := by
    rw [← hsplitF]
    exact aq8w2b_fstMemRtran1 L hf
  have hpartsF : partsSpine L (splitNormalListSpine L r (findFaceDarts L x)
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
      = ((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => (ndSpine L d).reverse)).reverse
        ++ partsSpine L (aq8w4aF1 L N r x) :=
    aq12w_catFstSplitNormalParts L hL hgn hm hf
  have huF : u ∈ partsSpine L (splitNormalListSpine L r (findFaceDarts L x)
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
    rw [hpartsF]
    exact List.mem_append.mpr (Or.inr hu)
  -- r-side 单射
  have hq : (partsSpine L r).map (fun q => q.head!.1) ∈ quotientListSpine L N := by
    show _ ∈ coreListSpine (N.map (partsSpine L))
    exact List.mem_map.mpr ⟨partsSpine L r, List.mem_map.mpr ⟨r, hrN, rfl⟩, rfl⟩
  have hcoreNodup : ((partsSpine L r).map (fun q => q.head!.1)).Nodup :=
    (hm.1.2.2.2.2.1).1 _ hq
  have hinj : ∀ q ∈ partsSpine L r, ∀ q' ∈ partsSpine L r,
      (q.head!).1 = (q'.head!).1 → q = q' :=
    (List.nodup_map_iff_inj_on (uniqParts L hrnd hrne)).mp hcoreNodup
  have hune : u ≠ [] := partsAllNonnil L hf1nd hf1ne u hu
  have hup : u.head! ∈ u := List.head!_mem_self hune
  have hur' : u.head! ∈ r := hur _ hup
  obtain ⟨p, hp, hdp⟩ := partsMemExists L hrnd hur'
  refine ⟨p, hp, ?_, ?_⟩
  · -- ②③④ containment
    intro a ha
    have har : a ∈ r := hur a ha
    obtain ⟨p1, hp1, hap1⟩ := partsMemExists L hrnd har
    have hfst1 : a.1 = (p1.head!).1 := partsFst L hL hnR hrN hp1 hap1
    have hfstu : a.1 = (u.head!).1 := partsFst L hL hnN hFmem huF ha
    have hfstp : (u.head!).1 = (p.head!).1 := partsFst L hL hnR hrN hp hdp
    have heq : (p1.head!).1 = (p.head!).1 := by
      rw [← hfst1, hfstu, hfstp]
    have hpp : p1 = p := hinj p1 hp1 p hp heq
    rw [hpp] at hap1
    exact hap1
  · -- ⑤ 头 FST 相等
    exact (partsFst L hL hnN hFmem huF hup).trans (partsFst L hL hnR hrN hp hdp)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq8w4b_f1Nodup
#print axioms Kepler.Text.TameSpine.aq8w4b_f1Nonnil
#print axioms Kepler.Text.TameSpine.aq8w4b_f1SubsetR
#print axioms Kepler.Text.TameSpine.aq8w4b_partsSubArcRefineF1
