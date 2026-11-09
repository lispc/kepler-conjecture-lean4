/-
  Kepler.Text.TameSpine.JcajyduAqSplit1F — E4d-a-3 第一段：f_last 接线的**件层铺垫**
  （展开/末元 + `ra = z1` 支的 f1 收口 + idxOf 事实）。

  件目（8 件，全真证）：
  ① `split1Unfold`：`split.1 = new1.reverse ++ f1`（`splitNormalListSpine` 的
     局部 `nd` 与 `ndSpine` 同体，`rfl` 级）；
  ② `eList_eList`：`eList (eList d) = d`；
  ③ `head!Reverse`：`l.reverse.head! = l.getLast!`；
  ④ `getLast!AppendRight`：`(a ++ b).getLast! = b.getLast!`（b ≠ []）→ split.1 末元 = z1；
  ⑤ `z1NotMemF1Body` / ⑥ `idxOfF1OfNe`：`ra ≠ z1` 时 `z1` 居 f1 末位（idxOf = len−1）；
  ⑦ `idxOfF1OfEq`：`ra = z1` 时 `z1` 居 f1 首位（idxOf = 0）；
  ⑧ `getD_zero_eq_head!` + **`nextElF1Z1OfEq`**：`ra = z1` 支
     `nextEl f1 z1 = nextEl r z1`（`betweenSelfNeNil` + `HD_BETWN1`）。

  边界（BLOCKED，见 DELIVERY 续 §E4d-a-3）：f_last **本体**（四支装配 ~90-120）未落，
  本批按授权口径交到件层；所需原料现已全部在树（见 DELIVERY 的装配清单）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqSplit1E

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts listPairs)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-- `splitNormalListSpine` 的 `.1` 展开（局部 `nd` = `ndSpine`）：
`split.1 = new1.reverse ++ f1`。 -/
theorem split1Unfold (L : fgraph ℕ) (r f : List (ℕ × ℕ)) (ram1 ram2 : ℕ × ℕ) :
    (splitNormalListSpine L r f ram1 ram2).1
      = (((between f ram1 (nextEl r ram2)).map (ndSpine L)).flatten).reverse
        ++ ([nextEl r ram1] ++ between r (nextEl r ram1) ram2 ++ [ram2]) := by
  rfl

/-- `eList` 对合。 -/
theorem eList_eList (d : ℕ × ℕ) : eList (eList d) = d := by
  cases d with
  | mk a b => rfl

/-- `head! (l.reverse) = l.getLast!`。 -/
theorem head!Reverse {α : Type*} [Inhabited α] (l : List α) :
    l.reverse.head! = l.getLast! := by
  rw [List.head!_eq_head?_getD, List.head?_reverse, ← List.getLast!_eq_getLast?_getD]

/-- 末元拼接：`(a ++ b).getLast! = b.getLast!`（b ≠ []）。 -/
theorem getLast!AppendRight {α : Type*} [Inhabited α] (a b : List α) (hb : b ≠ []) :
    (a ++ b).getLast! = b.getLast! := by
  have h : a ++ b ≠ [] := by simp [hb]
  rw [getLast!EqGetLast h, getLast!EqGetLast hb,
    List.getLast_append_of_right_ne_nil a b hb]

/-- `ra ≠ z1` 时 `f1` 的前缀不含 `z1`。 -/
theorem z1NotMemF1Body {α : Type*} [BEq α] [LawfulBEq α] {r : List α} {ra z1 : α}
    (hnd : r.Nodup) (hra : ra ≠ z1) : z1 ∉ [ra] ++ between r ra z1 :=
  z1NotMemF1Prefix hnd hra

/-- `ra ≠ z1` 时 `z1` 居 `f1` 末位（idxOf = len−1）。 -/
theorem idxOfF1OfNe {α : Type*} [BEq α] [LawfulBEq α] {r : List α} {ra z1 : α}
    (hnd : r.Nodup) (hra : ra ≠ z1) :
    ([ra] ++ between r ra z1 ++ [z1]).idxOf z1
      = ([ra] ++ between r ra z1 ++ [z1]).length - 1 := by
  have hA : z1 ∉ [ra] ++ between r ra z1 := z1NotMemF1Body hnd hra
  have hidx : ([ra] ++ between r ra z1 ++ [z1]).idxOf z1
      = ([ra] ++ between r ra z1).length := by
    rw [List.idxOf_append_of_notMem hA]
    simp
  rw [hidx]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- `ra = z1` 时 `z1` 居 `f1` 首位（idxOf = 0）。 -/
theorem idxOfF1OfEq {α : Type*} [BEq α] [LawfulBEq α] {r : List α} {z1 : α}
    (hnd : r.Nodup) : ([z1] ++ between r z1 z1 ++ [z1]).idxOf z1 = 0 := by
  have hA : z1 ∉ between r z1 z1 := notBetwn2 hnd
  rw [show [z1] ++ between r z1 z1 ++ [z1] = z1 :: (between r z1 z1 ++ [z1]) from rfl,
    List.idxOf_cons_self]

/-- `getD 0` 与 `head!` 一致（非空）。 -/
theorem getD_zero_eq_head! {α : Type*} [Inhabited α] (l : List α) (d : α) (h : l ≠ []) :
    l.getD 0 d = l.head! := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-- **`ra = z1` 支的 `f1` 收口**：`nextEl f1 z1 = nextEl r z1`（= z）。 -/
theorem nextElF1Z1OfEq {α : Type*} [Inhabited α] [BEq α] [LawfulBEq α] [DecidableEq α]
    {r : List α} {z z1 : α} (hnd : r.Nodup) (hz1 : z1 ∈ r) (hz1z : z1 ≠ z) (hz : z ∈ r) :
    nextEl ([z1] ++ between r z1 z1 ++ [z1]) z1 = nextEl r z1 := by
  have hrne : r ≠ [z1] := by
    intro h
    have hzmem : z ∈ [z1] := h ▸ hz
    have hzeq : z = z1 := by simpa using hzmem
    exact hz1z hzeq.symm
  have hbne : between r z1 z1 ≠ [] := betweenSelfNeNil hz1 hnd hrne
  have hbpos : 0 < (between r z1 z1).length := List.length_pos_of_ne_nil hbne
  -- f1 = z1 :: (between ++ [z1])，idxOf = 0，故 nextEl 取 getD 1
  have hidx : ([z1] ++ between r z1 z1 ++ [z1]).idxOf z1 = 0 := idxOfF1OfEq hnd
  have hlen : 1 < ([z1] ++ between r z1 z1 ++ [z1]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hlhs : nextEl ([z1] ++ between r z1 z1 ++ [z1]) z1
      = ([z1] ++ between r z1 z1 ++ [z1]).getD 1 z1 := by
    unfold nextEl
    rw [hidx, if_neg (by omega)]
  rw [hlhs, show [z1] ++ between r z1 z1 ++ [z1]
      = z1 :: (between r z1 z1 ++ [z1]) from rfl, List.getD_cons_succ,
    getD_zero_eq_head! (between r z1 z1 ++ [z1]) z1 (by simp),
    List.head!_append [z1] hbne, HD_BETWN1 hz1 hnd hrne]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.split1Unfold
#print axioms Kepler.Text.TameSpine.eList_eList
#print axioms Kepler.Text.TameSpine.head!Reverse
#print axioms Kepler.Text.TameSpine.getLast!AppendRight
#print axioms Kepler.Text.TameSpine.z1NotMemF1Body
#print axioms Kepler.Text.TameSpine.idxOfF1OfNe
#print axioms Kepler.Text.TameSpine.idxOfF1OfEq
#print axioms Kepler.Text.TameSpine.getD_zero_eq_head!
#print axioms Kepler.Text.TameSpine.nextElF1Z1OfEq
