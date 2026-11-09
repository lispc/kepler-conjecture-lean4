/-
  JcajyduAqLeaf8W4d — AQ8 W4c-iii：`hF1` f1-part 单射 + **W4 主定理收口**。

  HOL 锚：AQ8.hl:2512-2571 / 3011-3070（GSUBGOAL#4），但用探针改写的短路线：
  探针结论 = 候选杀点是 **`aq8w2a_lastPartsZ1NotCat`**（8W2aB，已落库）：
  「以 `z1` 结尾且 ⊆ p 的 f1-part ⇒ `z1 ∈ p` ⇒ 该 r-part 的 `getLast! ∉ f1`，
  与另一 f1-part 以 `p.getLast!` 结尾（∈ f1）矛盾」——**不需要 f1 绕序/last_cat**。

  ┌─ 件（3 public + 3 private）───────────────────────────────────
  │ · `aq8w4d_f1PartsInj`  `u v ∈ parts f1`、头 FST 相等 ⇒ `u = v`：
  │   W4b containment ⇒ 父 r-part 同 `p`；`u.last = v.last` 支 uniqSublistUnique；
  │   否则取 last ≠ z1 的 part `w`：
  │   - `w.last ≠ p.getLast!` ⇒ W4c-i 边界 + `nextElPartsUnlast`/`partsNextUnlast` 矛盾；
  │   - `w.last = p.getLast!` ⇒ 另一 part `z`：`z.last = z1` 时
  │     `lastPartsZ1NotCat` 秒杀；否则对 `z` 走边界矛盾。
  │ · `aq8w4d_hF1`  = `nodup_map_iff_inj_on` + `uniqParts` + 单射。
  │ · `aq8w4d_uniqFstSplitNormalParts` = **W4 主定理**（W4a 归约器 + hF1）。
  └────────────────────────────────────────────────────────────────
  陈述对表（HOL AQ8.hl:2382-3340）：
  `uniq (core L (FST (split_normal_list L r (find_face L (l'y)) (l'y) (prev_el r (l'z)))))`
  ↦ `((partsSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
  (lYSpine L r x) (prevEl r (lZSpine L N r x))).1).map (fun p => p.head!.1)).Nodup`
  （`core` ↦ `(parts …).map (FST∘HD)`，同形）。
  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W4c
import Kepler.Text.TameSpine.JcajyduAqLeaf8W2aB
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList5

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

/-! ## §0 私件 -/

/-- `(s ++ t).getLast! = t.getLast!`（`t ≠ []`）。 -/
private theorem aq8w4d_getLast!_append {α : Type*} [Inhabited α] (s : List α)
    {t : List α} (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

/-- `f1.getLast! = z1`。 -/
private theorem aq8w4d_f1Last (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) :
    (aq8w4aF1 L N r x).getLast! = prevEl r (lZSpine L N r x) := by
  have h : ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]).getLast!
      = prevEl r (lZSpine L N r x) := by
    rw [aq8w4d_getLast!_append _
      (by simp : ([prevEl r (lZSpine L N r x)] : List (ℕ × ℕ)) ≠ [])]
    simp
  show ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
    (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]).getLast! = _
  exact h

/-- 内部矛盾件：`m ⊆ p`、`m.last ≠ z1`、`m.last ≠ p.getLast!` ⇒ 矛盾。 -/
private theorem aq8w4d_interiorContra (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p m : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hm_mem : m ∈ partsSpine L (aq8w4aF1 L N r x)) (hmsub : ∀ a ∈ m, a ∈ p)
    (hZ1 : m.getLast! ≠ prevEl r (lZSpine L N r x))
    (hplast : m.getLast! ≠ p.getLast!) : False := by
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hm.1.2.1 hm.1.2.2.1
  have hf1nd : (aq8w4aF1 L N r x).Nodup := aq8w4b_f1Nodup L hL hgn hm hf
  have hf1ne : aq8w4aF1 L N r x ≠ [] := aq8w4b_f1Nonnil L N r x
  have hmne : m ≠ [] := partsAllNonnil L hf1nd hf1ne m hm_mem
  have hmlastmem : m.getLast! ∈ m := by
    rw [getLast!EqGetLast hmne]; exact List.getLast_mem hmne
  have hmlastp : m.getLast! ∈ p := hmsub _ hmlastmem
  have hbound : nextEl (aq8w4aF1 L N r x) m.getLast!
      ≠ fList L (eList m.getLast!) := by
    refine aq8w4c_f1Boundary L hL hgn hm hf hm_mem ?_
    rw [aq8w4d_f1Last L N r x]
    exact hZ1
  have hmlastf1 : m.getLast! ∈ aq8w4aF1 L N r x :=
    memPartsImp L hf1nd hf1ne hm_mem _ hmlastmem
  have hnext : nextEl (aq8w4aF1 L N r x) m.getLast! = nextEl r m.getLast! :=
    aq8w4c_f1NextElR L hL hgn hm hf hmlastf1 hZ1
  have hinterior : nextEl r m.getLast! = fList L (eList m.getLast!) :=
    (nextElPartsUnlast L hrnd hrne hp hmlastp hplast).trans
      (partsNextUnlast L hrnd hrne p hp m.getLast! hmlastp hplast)
  exact hbound (hnext.trans hinterior)

/-- 同一个 r-part 内不能有两个不同的 f1-part。 -/
private theorem aq8w4d_noTwoPartsInParent (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p u v : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hu : u ∈ partsSpine L (aq8w4aF1 L N r x))
    (hv : v ∈ partsSpine L (aq8w4aF1 L N r x))
    (husub : ∀ a ∈ u, a ∈ p) (hvsub : ∀ a ∈ v, a ∈ p) (hne : u ≠ v) : False := by
  have hf1nd : (aq8w4aF1 L N r x).Nodup := aq8w4b_f1Nodup L hL hgn hm hf
  have hf1ne : aq8w4aF1 L N r x ≠ [] := aq8w4b_f1Nonnil L N r x
  have hflat : (partsSpine L (aq8w4aF1 L N r x)).flatten.Nodup := by
    rw [partsFlatten L hf1nd hf1ne]; exact hf1nd
  have hune : u ≠ [] := partsAllNonnil L hf1nd hf1ne u hu
  have hvne : v ≠ [] := partsAllNonnil L hf1nd hf1ne v hv
  have humem : u.getLast! ∈ u := by
    rw [getLast!EqGetLast hune]; exact List.getLast_mem hune
  have hvmem : v.getLast! ∈ v := by
    rw [getLast!EqGetLast hvne]; exact List.getLast_mem hvne
  have hlastne : u.getLast! ≠ v.getLast! := by
    intro h
    exact hne (uniqSublistUnique (partsSpine L (aq8w4aF1 L N r x)) hflat u hu v hv
      ⟨u.getLast!, humem, h ▸ hvmem⟩)
  by_cases huZ1 : u.getLast! = prevEl r (lZSpine L N r x)
  · -- u 以 z1 结尾：z1 ∈ u ⊆ p；p 的 last ∉ f1（lastPartsZ1NotCat）
    have hz1p : prevEl r (lZSpine L N r x) ∈ p := husub _ (by rw [← huZ1]; exact humem)
    have hnot := aq8w2a_lastPartsZ1NotCat L hL hgn hm hf hp hz1p
    have hvZ1 : v.getLast! ≠ prevEl r (lZSpine L N r x) := by
      intro h; exact hlastne (huZ1.trans h.symm)
    by_cases hvp : v.getLast! = p.getLast!
    · apply hnot
      have h : p.getLast! ∈ ([nextEl r (lYSpine L r x)] ++ between r
          (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x))
          ++ [prevEl r (lZSpine L N r x)]) :=
        memPartsImp L hf1nd hf1ne hv _ (hvp ▸ hvmem)
      rwa [List.append_assoc] at h
    · exact aq8w4d_interiorContra L hL hgn hm hf hp hv hvsub hvZ1 hvp
  · by_cases hup : u.getLast! = p.getLast!
    · by_cases hvZ1 : v.getLast! = prevEl r (lZSpine L N r x)
      · have hz1p : prevEl r (lZSpine L N r x) ∈ p := hvsub _ (by rw [← hvZ1]; exact hvmem)
        have hnot := aq8w2a_lastPartsZ1NotCat L hL hgn hm hf hp hz1p
        apply hnot
        have h : p.getLast! ∈ ([nextEl r (lYSpine L r x)] ++ between r
            (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x))
            ++ [prevEl r (lZSpine L N r x)]) :=
          memPartsImp L hf1nd hf1ne hu _ (hup ▸ humem)
        rwa [List.append_assoc] at h
      · have hvp : v.getLast! ≠ p.getLast! := by
          intro h; exact hlastne (hup.trans h.symm)
        exact aq8w4d_interiorContra L hL hgn hm hf hp hv hvsub hvZ1 hvp
    · exact aq8w4d_interiorContra L hL hgn hm hf hp hu husub huZ1 hup

/-! ## §1 f1-part 单射 -/

/-- `u v ∈ parts f1`、头 FST 相等 ⇒ `u = v`。 -/
theorem aq8w4d_f1PartsInj (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ u ∈ partsSpine L (aq8w4aF1 L N r x),
      ∀ v ∈ partsSpine L (aq8w4aF1 L N r x), (u.head!).1 = (v.head!).1 → u = v := by
  have hf1nd : (aq8w4aF1 L N r x).Nodup := aq8w4b_f1Nodup L hL hgn hm hf
  have hf1ne : aq8w4aF1 L N r x ≠ [] := aq8w4b_f1Nonnil L N r x
  have hf1sub : ∀ a ∈ aq8w4aF1 L N r x, a ∈ r := aq8w4b_f1SubsetR L hL hgn hm hf
  have hnR : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hnR hrN
  have hq : (partsSpine L r).map (fun q => q.head!.1) ∈ quotientListSpine L N := by
    show _ ∈ coreListSpine (N.map (partsSpine L))
    exact List.mem_map.mpr ⟨partsSpine L r, List.mem_map.mpr ⟨r, hrN, rfl⟩, rfl⟩
  have hcoreNodup : ((partsSpine L r).map (fun q => q.head!.1)).Nodup :=
    (hm.1.2.2.2.2.1).1 _ hq
  have hinj : ∀ q ∈ partsSpine L r, ∀ q' ∈ partsSpine L r,
      (q.head!).1 = (q'.head!).1 → q = q' :=
    (List.nodup_map_iff_inj_on (uniqParts L hrnd hrne)).mp hcoreNodup
  intro u hu v hv heq
  by_contra hne
  have hur : ∀ a ∈ u, a ∈ r := fun a ha => hf1sub a (memPartsImp L hf1nd hf1ne hu a ha)
  have hvr : ∀ a ∈ v, a ∈ r := fun a ha => hf1sub a (memPartsImp L hf1nd hf1ne hv a ha)
  obtain ⟨pu, hpu, husub, hfu⟩ :=
    aq8w4b_partsSubArcRefineF1 L hL hgn hm hf hu hur
  obtain ⟨pv, hpv, hvsub, hfv⟩ :=
    aq8w4b_partsSubArcRefineF1 L hL hgn hm hf hv hvr
  have hpp : pu = pv := hinj pu hpu pv hpv (hfu.symm.trans (heq.trans hfv))
  have hvsub' : ∀ a ∈ v, a ∈ pu := by rw [← hpp] at hvsub; exact hvsub
  exact aq8w4d_noTwoPartsInParent L hL hgn hm hf hpu hu hv husub hvsub' hne

/-- `hF1`：f1 头表 Nodup。 -/
theorem aq8w4d_hF1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ((partsSpine L (aq8w4aF1 L N r x)).map (fun p => p.head!.1)).Nodup := by
  have hf1nd : (aq8w4aF1 L N r x).Nodup := aq8w4b_f1Nodup L hL hgn hm hf
  have hf1ne : aq8w4aF1 L N r x ≠ [] := aq8w4b_f1Nonnil L N r x
  exact (List.nodup_map_iff_inj_on (uniqParts L hf1nd hf1ne)).mpr
    (aq8w4d_f1PartsInj L hL hgn hm hf)

/-- **AQ8 W4 主定理**（HOL `uniq_fst_split_normal_parts`，AQ8.hl:2382-3340）：
`uniq (core L (FST split))`。 -/
theorem aq8w4d_uniqFstSplitNormalParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ((partsSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1).map
        (fun p => p.head!.1)).Nodup :=
  aq8w4a_uniqOfF1 L hL hgn hm hf (aq8w4d_hF1 L hL hgn hm hf)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq8w4d_f1PartsInj
#print axioms Kepler.Text.TameSpine.aq8w4d_hF1
#print axioms Kepler.Text.TameSpine.aq8w4d_uniqFstSplitNormalParts
