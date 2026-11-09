/-
  JcajyduAqLeaf8W4c — AQ8 波 4c（止损交边界）：**f1 分区边界降级**三件。

  按编排者 W4c 派单第 4 条：f1-part 单射的几何核心含 f1 与 r 列表绕序（wrap）
  的端点重合子案（HOL `last_cat`/`nextCatBetwnSame` 级），本波先落**边界降级**
  （机械可证的件），单射（W4c-ii）另发。

  ┌─ 件（3 public + 2 private）───────────────────────────────────
  │ ① `aq8w4c_f1PartLastNeF1Last`
  │    `p ∈ parts f1` 且 `p ≠ (parts f1).getLast!` ⇒ `p.getLast! ≠ f1.getLast!`
  │    （私有泛型 `aq8w4c_partLastNeFlattenLast`：Nodup 的块表里非末块的末元
  │     ≠ flatten 的末元——经 `mem_iff_append` + `nodup_append` 不交支）。
  │ ② `aq8w4c_f1Boundary`
  │    上述 p ⇒ `nextEl f1 p.getLast! ≠ fList (eList p.getLast!)`
  │    （66 `aqs_conditionLastParts` 在 r := f1 处的 `.mpr rfl`）。
  │ ③ `aq8w4c_f1NextElR`
  │    `d ∈ f1`、`d ≠ z1` ⇒ `nextEl f1 d = nextEl r d`
  │    （`nextCatBetwnSame`：f1 = `[y1] ++ (betwn r y1 z1 ++ [z1])`）。
  └────────────────────────────────────────────────────────────────
  ┌─ W4c-ii 单射缺口（本波实测的精确边界）────────────────────────
  │ 已有：W4b containment ⇒ 同父 r-part p；反设 u ≠ v ⇒ 取非末 part w：
  │ 若 `w.getLast! ≠ p.getLast!` 则 ②+`nextElPartsUnlast/partsNextUnlast` 秒矛盾；
  │ **仅剩**「w 末元 = p.getLast! 且另一 part 是 f1 末 part」子案：
  │ 需证 `Z1 = p.getLast!`（否则 p 的列表连通性与 f1 的绕序矛盾），
  │ 再 uniqSublistUnique 得 u = v。缺件 = f1 绕序/list-连通性排序引理
  │ （HOL `last_cat` 段），估 80–150；W4c-ii 另发。
  └────────────────────────────────────────────────────────────────
  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W4b
import Kepler.Text.TameSpine.JcajyduAqLeaf12T
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.JcajyduAqLeaf1F

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

/-! ## §0 私件：块表末元与 flatten 末元 -/

/-- `(s ++ t).getLast! = t.getLast!`（`t ≠ []`）。 -/
private theorem aq8w4c_getLast!_append {α : Type*} [Inhabited α] (s : List α)
    {t : List α} (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

/-- 非末块的末元 ≠ 块表 flatten 的末元（`flatten.Nodup` + 块全非空）。 -/
private theorem aq8w4c_partLastNeFlattenLast {α : Type*} [Inhabited α]
    {L : List (List α)} (hflat : L.flatten.Nodup) (hall : ∀ l ∈ L, l ≠ [])
    {l : List α} (hl : l ∈ L) (hne : l ≠ L.getLast!) :
    l.getLast! ≠ L.flatten.getLast! := by
  obtain ⟨A, B, hL⟩ := List.mem_iff_append.mp hl
  have hBne : B ≠ [] := by
    intro hB
    apply hne
    rw [hL, hB,
      aq8w4c_getLast!_append A (by simp : ([l] : List (List α)) ≠ [])]
    simp
  have hBflat : B.flatten ≠ [] := by
    obtain ⟨b, hbB⟩ := List.exists_mem_of_ne_nil B hBne
    have hbne : b ≠ [] := hall b (by
      rw [hL]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hbB)))
    have hbmem : b.head! ∈ B.flatten :=
      List.mem_flatten.mpr ⟨b, hbB, List.head!_mem_self hbne⟩
    intro h0
    rw [h0] at hbmem
    exact List.not_mem_nil hbmem
  have hlne : l ≠ [] := hall l hl
  have hllast : l.getLast! ∈ l := by
    rw [getLast!EqGetLast hlne]; exact List.getLast_mem hlne
  have hfl : L.flatten = (A.flatten ++ l) ++ B.flatten := by
    rw [hL, List.flatten_append, List.flatten_cons, ← List.append_assoc]
  have hflast : L.flatten.getLast! = B.flatten.getLast! := by
    rw [hfl, aq8w4c_getLast!_append (A.flatten ++ l) hBflat]
  intro heq
  have hmemB : l.getLast! ∈ B.flatten := by
    rw [heq, hflast, getLast!EqGetLast hBflat]
    exact List.getLast_mem hBflat
  have hdisj := (List.nodup_append.mp (hfl ▸ hflat)).2.2
  exact (hdisj _ (List.mem_append.mpr (Or.inr hllast)) _ hmemB) rfl

/-! ## §1 f1 分区边界降级 -/

/-- `p ∈ parts f1`、`p` 非末 part ⇒ `p.getLast! ≠ f1.getLast!`。 -/
theorem aq8w4c_f1PartLastNeF1Last (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L (aq8w4aF1 L N r x))
    (hne : p ≠ (partsSpine L (aq8w4aF1 L N r x)).getLast!) :
    p.getLast! ≠ (aq8w4aF1 L N r x).getLast! := by
  have hf1nd : (aq8w4aF1 L N r x).Nodup := aq8w4b_f1Nodup L hL hgn hm hf
  have hf1ne : aq8w4aF1 L N r x ≠ [] := aq8w4b_f1Nonnil L N r x
  have hflat : (partsSpine L (aq8w4aF1 L N r x)).flatten.Nodup := by
    rw [partsFlatten L hf1nd hf1ne]; exact hf1nd
  have h := aq8w4c_partLastNeFlattenLast (α := ℕ × ℕ) hflat
    (partsAllNonnil L hf1nd hf1ne) hp hne
  rwa [partsFlatten L hf1nd hf1ne] at h

/-- `p ∈ parts f1`、`p` 非末 part ⇒ 其末元是 f1 的分区边界。 -/
theorem aq8w4c_f1Boundary (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L (aq8w4aF1 L N r x))
    (hlast : p.getLast! ≠ (aq8w4aF1 L N r x).getLast!) :
    nextEl (aq8w4aF1 L N r x) p.getLast! ≠ fList L (eList p.getLast!) := by
  have hf1nd : (aq8w4aF1 L N r x).Nodup := aq8w4b_f1Nodup L hL hgn hm hf
  have hf1ne : aq8w4aF1 L N r x ≠ [] := aq8w4b_f1Nonnil L N r x
  have hpne : p ≠ [] := partsAllNonnil L hf1nd hf1ne p hp
  have hmem : p.getLast! ∈ p := by
    rw [getLast!EqGetLast hpne]; exact List.getLast_mem hpne
  exact (aqs_conditionLastParts L hf1nd hf1ne hp hmem hlast).mpr rfl

/-- `d ∈ f1`、`d ≠ z1` ⇒ `nextEl f1 d = nextEl r d`（f1 是 r 的弧段）。 -/
theorem aq8w4c_f1NextElR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ aq8w4aF1 L N r x)
    (hne : d ≠ prevEl r (lZSpine L N r x)) :
    nextEl (aq8w4aF1 L N r x) d = nextEl r d := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hY1r : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hyr
  have hZ1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hY1Z1 : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
    aq1_nextElYNePrevElZ L hL hgn hunL hm hf
  refine nextCatBetwnSame (r := r) (y := prevEl r (lZSpine L N r x))
    (z := nextEl r (lYSpine L r x)) (a := d) (s := aq8w4aF1 L N r x)
    hrnd hZ1r hY1r (Ne.symm hY1Z1) hd ?_ hne
  show ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])
    = [nextEl r (lYSpine L r x)] ++ (between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)])
  exact List.append_assoc _ _ _

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq8w4c_f1PartLastNeF1Last
#print axioms Kepler.Text.TameSpine.aq8w4c_f1Boundary
#print axioms Kepler.Text.TameSpine.aq8w4c_f1NextElR
