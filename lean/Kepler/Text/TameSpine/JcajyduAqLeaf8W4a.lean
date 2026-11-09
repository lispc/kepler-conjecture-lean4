/-
  JcajyduAqLeaf8W4a — AQ8 波 4a：`uniq_fst_split_normal_parts`（W4）的**归约器 + 块侧 + 交叉**
  + f1 头表。HOL 锚：AQ8.hl:2382-3340（959 行）的装配半。

  ┌─ 本波件（6 public + 2 private）───────────────────────────────
  │ ① `aq8w4a_blockHeadFst`   `headFst ((ndSpine d).reverse) = d.1`
  │ ② `aq8w4a_blockUniq`      块表 `uniq (map headFst (blocks))`
  │ ③ `aq8w4a_partRefineFst`  f1-part 的 head-FST 落到某个 r-part 的 head-FST
  │ ④ `aq8w4a_f1HeadFstSub`   f1 头表 ⊆ r 的 parts 头表
  │ ⑤ `aq8w4a_blockF1Disjoint` 块头表 ∩ f1 头表 = ∅（经 `aq8w3_betwnNotInFstRtrans`）
  │ ⑥ `aq8w4a_uniqOfF1`       **W4 归约器**：f1 头表 Nodup ⇒ W4 结论 Nodup
  └────────────────────────────────────────────────────────────────
  ┌─ 路线（DIFFERS：不再走 HOL 的 `betwn f y z = []` × `y1 = z1` 分支树）──
  │ W4 目标 = `uniq (map headFst (parts FST))`；FST 的 parts 分解直接复用
  │ **12W `aq12w_catFstSplitNormalParts`**（编排者裁定允许，无逻辑回环）：
  │   `parts FST = (blocks ndSpine.reverse).reverse ++ parts f1`
  │ ⇒ `map headFst` 用 `map_append`，`uniq` 用 `List.nodup_append` 三段：
  │   块表（本波 ②）、f1 表（**W4b/W4c 债务** `hF1`）、交叉（本波 ⑤）。
  │ 分支树只影响 `hF1` 的证明（f1-part 单射），归约器本身分支自由。
  └────────────────────────────────────────────────────────────────
  ┌─ 移位变体（W4 侦察 §5 的 count vs count−1）───────────────────
  │ **放本波**：不需要 aq8w2e 的块长变体——块侧直接用
  │ `lastNdSpine` + `fstNListPower`（`(nList^n d).1 = d.1`）得到
  │ `headFst (ndSpine d).reverse = d.1`（本波 ①），再吃 `aq8w1_uniqFstBetwnParts`。
  └────────────────────────────────────────────────────────────────

  DIFFERS：层序倒置（AQ8 W4a 依赖 AQ12 车道 12W/12V 的 FST partsCat）——已获
  编排者裁定；无逻辑回环（`aq8Concl` 不被 12* 引用）。不吃 `h4`。
  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12W
import Kepler.Text.TameSpine.JcajyduBetwnMap
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1b
import Kepler.Text.TameSpine.JcajyduAqLeaf8W3
import Kepler.Text.TameSpine.JcajyduAqLeaf8W05
import Kepler.Text.TameSpine.JcajyduAqSplit1B
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList9
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

/-! ## §0 私件：reverse 的头 = 尾；parts 头 FST ⊆ 行 FST 表 -/

/-- `l.reverse.head! = l.getLast!`。 -/
private theorem aq8w4a_head!_reverse {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.reverse.head! = l.getLast! := by
  rw [List.head!_eq_head?_getD, List.head?_reverse, List.getLast!_eq_getLast?_getD]

/-- `(parts r 的 head-FST 表) ⊆ (r 的 FST 表)`（normal row）。 -/
private theorem aq8w4a_headFstSubRow (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)}
    (hr : r ∈ N) :
    ∀ a ∈ (partsSpine L r).map (fun p => p.head!.1), a ∈ r.map Prod.fst := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hn hr
  have hpne : p ≠ [] := partsAllNonnil L hrnd hrne p hp
  have hmem : p.head! ∈ p := List.head!_mem_self hpne
  exact List.mem_map.mpr ⟨p.head!, memPartsImp L hrnd hrne hp _ hmem, rfl⟩

/-! ## §1 块侧：块头 FST = d.1，块表 Nodup -/

/-- 块（`(ndSpine d).reverse`）的头 FST = `d.1`（`lastNdSpine` + `fstNListPower`）。 -/
theorem aq8w4a_blockHeadFst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ}
    (hdW : d ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)) :
    (((ndSpine L d).reverse).head!).1 = d.1 := by
  have hdD : d ∈ listOfDarts L := mem_darts_of_mem_findFace L (betwnMem hdW)
  have h2 : 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length :=
    two_le_sz_of_restricted L hL hgn hm.1.1 (List.mem_toFinset.mpr hdD)
  have hne : ndSpine L d ≠ [] := ndSpineNeNil L d h2
  rw [aq8w4a_head!_reverse hne, lastNdSpine L d h2, fstNListPower L hL hgn hdD]

/-- 块表的 head-FST 无重（`aq8w1_uniqFstBetwnParts` 的块形）。 -/
theorem aq8w4a_blockUniq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
      (fun d => (ndSpine L d).reverse)).map (fun p => p.head!.1)).Nodup := by
  have hcongr : (((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
      (fun d => (ndSpine L d).reverse)).map (fun p => p.head!.1))
      = (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => d.1) := by
    rw [List.map_map]
    exact List.map_congr_left (fun d hd =>
      aq8w4a_blockHeadFst L hL hgn hm hf hd)
  rw [hcongr]
  have hparts : partsSpine L (between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x)) =
      (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
        (fun d => [d]) :=
    aqs_partsFBetwnPure L hL hgn hm hf
  have huniq := aq8w1_uniqFstBetwnParts L hL hgn hm hf
  rw [hparts] at huniq
  have hmap : ((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
      (fun d => [d])).map (fun p => p.head!.1)
      = (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => d.1) := by
    rw [List.map_map]
    rfl
  rwa [hmap] at huniq

/-! ## §2 f1 侧头表：part 头 FST 落到 r-part 头 FST -/

/-- `f1 = [y1] ++ betwn r y1 z1 ++ [z1]`（`y1 = nextEl r l'y`、`z1 = prevEl r l'z`）。 -/
noncomputable def aq8w4aF1 (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) : List (ℕ × ℕ) :=
  [nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
    (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]

/-- f1-part 的 head-FST 等于某个 r-part 的 head-FST（`aq8w3k_partRefineFst` 的 f1 弧变体）。 -/
theorem aq8w4a_partRefineFst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ u ∈ partsSpine L (aq8w4aF1 L N r x),
      ∃ v ∈ partsSpine L r, (u.head!).1 = (v.head!).1 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnR : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hnR hrN
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hY1r : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hyr
  have hZ1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hY1Z1 : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
    aq1_nextElYNePrevElZ L hL hgn hunL hm hf
  have hf1nd : (aq8w4aF1 L N r x).Nodup := by
    show ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]).Nodup
    exact uniqAppendBetwn hrnd hY1r hZ1r hY1Z1
  have hf1ne : aq8w4aF1 L N r x ≠ [] := by
    show ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) ≠ []
    simp
  have hf1sub : ∀ a ∈ aq8w4aF1 L N r x, a ∈ r := by
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
  intro u hu
  have hune : u ≠ [] := partsAllNonnil L hf1nd hf1ne u hu
  have hup : u.head! ∈ u := List.head!_mem_self hune
  have hmem : u.head! ∈ aq8w4aF1 L N r x := memPartsImp L hf1nd hf1ne hu _ hup
  have hur : u.head! ∈ r := hf1sub _ hmem
  obtain ⟨v, hv, hdv⟩ := partsMemExists L hrnd hur
  exact ⟨v, hv, partsFst L hL hnR hrN hv hdv⟩

/-- f1 头表 ⊆ r 的 parts 头表。 -/
theorem aq8w4a_f1HeadFstSub (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ a ∈ (partsSpine L (aq8w4aF1 L N r x)).map (fun p => p.head!.1),
      a ∈ (partsSpine L r).map (fun p => p.head!.1) := by
  intro a ha
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
  obtain ⟨v, hv, hveq⟩ := aq8w4a_partRefineFst L hL hgn hm hf u hu
  exact List.mem_map.mpr ⟨v, hv, hveq.symm⟩

/-! ## §3 交叉：块头表与 f1 头表不交 -/

/-- 块头表 ∩ f1 头表 = ∅（窗口 FST 不进 `map FST r`，`aq8w3_betwnNotInFstRtrans`）。 -/
theorem aq8w4a_blockF1Disjoint (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ a ∈ (((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
      (fun d => (ndSpine L d).reverse)).map (fun p => p.head!.1)),
      a ∉ (partsSpine L (aq8w4aF1 L N r x)).map (fun p => p.head!.1) := by
  intro a ha haF1
  obtain ⟨p, hp, hpa⟩ := List.mem_map.mp ha
  obtain ⟨d, hdW, rfl⟩ := List.mem_map.mp hp
  have hpd : (((ndSpine L d).reverse).head!).1 = d.1 :=
    aq8w4a_blockHeadFst L hL hgn hm hf hdW
  have haeq : a = d.1 := hpa.symm.trans hpd
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have haR : a ∈ r.map Prod.fst :=
    aq8w4a_headFstSubRow L hL hm.1.2.1 hm.1.2.2.1 a
      (aq8w4a_f1HeadFstSub L hL hgn hm hf a haF1)
  rw [haeq] at haR
  exact (aq8w3_betwnNotInFstRtrans L hL hgn hunL hm hf hdW) haR

/-! ## §4 W4 归约器：f1 头表 Nodup ⇒ W4 结论 -/

/-- **W4 归约器**：`uniq (map headFst (parts FST))` 归约到 f1 头表的 Nodup（W4b/W4c 债务）。
FST 的 parts 分解 = **12W `aq12w_catFstSplitNormalParts`**（DIFFERS：跨叶复用）。 -/
theorem aq8w4a_uniqOfF1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hF1 : ((partsSpine L (aq8w4aF1 L N r x)).map (fun p => p.head!.1)).Nodup) :
    ((partsSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1).map
        (fun p => p.head!.1)).Nodup := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hfaceY : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1
  have hF_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
      = (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1 := by
    rw [hfaceY]
  rw [hF_eq, aq12w_catFstSplitNormalParts L hL hgn hm hf, List.map_append,
    List.map_reverse, List.nodup_append]
  refine ⟨?_, hF1, ?_⟩
  · rw [List.nodup_reverse]
    exact aq8w4a_blockUniq L hL hgn hm hf
  · intro a ha b hb hab
    exact aq8w4a_blockF1Disjoint L hL hgn hm hf a (List.mem_reverse.mp ha) (hab ▸ hb)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq8w4a_blockHeadFst
#print axioms Kepler.Text.TameSpine.aq8w4a_blockUniq
#print axioms Kepler.Text.TameSpine.aq8w4a_partRefineFst
#print axioms Kepler.Text.TameSpine.aq8w4a_f1HeadFstSub
#print axioms Kepler.Text.TameSpine.aq8w4a_blockF1Disjoint
#print axioms Kepler.Text.TameSpine.aq8w4a_uniqOfF1
