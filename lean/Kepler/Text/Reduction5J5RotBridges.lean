/-
  Kepler.Text.Reduction5J5RotBridges — J5-2 续段：reduction2 章的 rotate_to 簇与
  `newvertex_alt`（reduction2.hl:620）。

  ┌─ 归属对账（HOL Light Flyspeck）──────────────────────────────────
  │ reduction2.hl:91  `cat_eq`（8L）→ `catEq`：`a = c ∧ b = d ⇒ cat a b = cat c d`
  │ reduction2.hl:99  `rotate1_rcons`（8L）→ `rotate1Rcons`：
  │    ¬(x = []) ⇒ rotate1 x = rcons (TL x) (HD x)
  │ reduction2.hl:158 `rotate_to2`（27L）→ `rotate1RotateTo`（Dart 形）：
  │    uniq f ∧ MEM x f ∧ next_el f x = w ⇒ rotate1 (rotate_to f x) = rotate_to f w
  │ reduction2.hl:195 `rotate_to_uniq`（8L）→ `rotateToUniq`：
  │    MEM x f ∧ uniq f ⇒ uniq (rotate_to f x)
  │ reduction2.hl:620 `newvertex_alt`（37L）→ `newvertexAlt`：
  │    (let f = find_face L x; w = next_el f x; fw = rotate_to f w in
  │     uniq f ∧ MEM x f ∧ MEM x r ⇒
  │       newvertex L r x = MAP FST (filter (λd. ¬MEM d r) fw))
  │ tame_list.hl:12875 `rot_eq_nil` → `rotEqNil`：`rot n r = [] ⇔ r = []`
  └────────────────────────────────────────────────────────────────

  ┌─ 查重与复用（派单点名）────────────────────────────────────────
  │ HOL `Pwssrat.rotate_rot_indexl` = 树内 `Reduction1.rotateToEqRotate`
  │ （Reduction1W2d:51，泛型 BEq/LawfulBEq），直接消费，不重落。
  │ `hd_rotate_to`/`mem_rotate_to` = spine `hdRotateTo`/`memRotateTo`
  │ （TameList54）在库。两库 `rotateTo` 同值：`Reduction1.rotateToBridge`（rfl）。
  │ `rotate1_rcons`/`rot_eq_nil`/`catEq` 为纯列表叶件，本文件落。
  └────────────────────────────────────────────────────────────────

  ┌─ 实例与载体（R1）──────────────────────────────────────────────
  │ 链侧消费端全是 `Dart`（`newvertex L r x`、`findFaceDarts L x`），故
  │ rotate 簇按 **Dart 特化**陈述（同 Reduction3DefsNewVertex 的消费面）。
  │ 跨实例两处用既有桥：`nextElInstEq`（Reduction5Kbwpbhq:86）、
  │ `idxOfInstEq`（:80）——TameLp 的 `nextEl_eq_getD`/`idxOf_getElem` 烤
  │ `instBEqOfDecidableEq`，Dart 默认 `instBEqProd`。
  │ `rotateToEqRotate` 在 spine 词汇（`TameSpine.rotateTo`）；两库同值，
  │ `newvertexAlt` 用 `show` 做定义级换算。
  └────────────────────────────────────────────────────────────────

  ┌─ 证体 ────────────────────────────────────────────────────────────
  │ · rotateToUniq：rotateToEqRotate → `List.nodup_rotate`。
  │ · idxOfNextElDart：`nextEl_eq_getD` + `getD_eq_getElem_of_lt` +
  │   `idxOf_getElem`（HOL `Tame_list.indexl_next_el` 的内容）。
  │ · rotate1RotateTo：rotateToEqRotate ×2 + `List.rotate_rotate` +
  │   idxOfNextElDart + `List.rotate_mod`。
  │ · newvertexAlt：newvertex 展开 → `rotateTo f x = x :: tail` →
  │   filter 与 rotate1 交换（x ∈ r ⇒ 谓词 false）→ rotate1RotateTo →
  │   MAP 同余。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction3DefsNewVertex
import Kepler.Text.Reduction1W2d
import Kepler.Text.Reduction5Kbwpbhq
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)

/-- **HOL `cat_eq`**（reduction2.hl:91）：两对相等则两段拼接相等。 -/
theorem catEq {α : Type} {a b c d : List α} (h1 : a = c) (h2 : b = d) :
    a ++ b = c ++ d := by
  rw [h1, h2]

/-- **HOL `rotate1_rcons`**（reduction2.hl:99）：`rotate1 x = rcons (TL x) (HD x)`。 -/
theorem rotate1Rcons {α : Type} (l : List α) (h : l ≠ []) :
    l.rotate 1 = l.tail ++ [l.head h] := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rw [List.rotate_cons_succ, List.rotate_zero]; rfl

/-- **HOL `rot_eq_nil`**（tame_list.hl:12875）：`rot n r = [] ⇔ r = []`。 -/
theorem rotEqNil {α : Type} (l : List α) (n : ℕ) : l.rotate n = [] ↔ l = [] :=
  List.rotate_eq_nil_iff

/-- **HOL `rotate_to_uniq`**（reduction2.hl:195）：`MEM x f ∧ uniq f ⇒ uniq (rotate_to f x)`。 -/
theorem rotateToUniq {α : Type} [BEq α] [LawfulBEq α] {f : List α} {x : α}
    (hx : x ∈ f) (hnd : f.Nodup) : (Kepler.Text.TameSpine.rotateTo f x).Nodup := by
  rw [Kepler.Text.Reduction1.rotateToEqRotate hx hnd]
  exact List.nodup_rotate.mpr hnd

/-- `nextEl` 后的下标（HOL `Tame_list.indexl_next_el`；Dart 特化，跨实例用桥）。 -/
private theorem idxOfNextElDart {f : List Dart} {x : Dart}
    (hnd : f.Nodup) (hx : x ∈ f) :
    f.idxOf (Kepler.Assembly.nextEl f x) = (f.idxOf x + 1) % f.length := by
  have hpos : 0 < f.length := List.length_pos_of_mem hx
  have hw : Kepler.Assembly.nextEl f x = f[(f.idxOf x + 1) % f.length]'(Nat.mod_lt _ hpos) := by
    rw [Kepler.Text.TameLp.nextEl_eq_getD hx,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
  rw [hw]
  exact Kepler.Text.TameLp.idxOf_getElem hnd (Nat.mod_lt _ hpos)

/-- **HOL `rotate_to2`**（reduction2.hl:158，Dart 形）：转一步后再转 x 等于直接
转到 `next_el f x`。 -/
theorem rotate1RotateTo {f : List Dart} {x w : Dart}
    (hnd : f.Nodup) (hx : x ∈ f) (hw : Kepler.Assembly.nextEl f x = w) :
    (Kepler.Text.TameSpine.rotateTo f x).rotate 1 = Kepler.Text.TameSpine.rotateTo f w := by
  have hwm : w ∈ f := hw ▸ Kepler.Text.TameLp.nextEl_mem_of_mem hx
  rw [Kepler.Text.Reduction1.rotateToEqRotate hx hnd,
    Kepler.Text.Reduction1.rotateToEqRotate hwm hnd, List.rotate_rotate]
  rw [← hw, idxOfNextElDart hnd hx, List.rotate_mod]

/-- filter 与 rotate1 的交换（非空表且头元被滤掉；`newvertexAlt` 的私有支件）。 -/
private theorem filterRotateOneCons {α : Type} (p : α → Bool) (a : α) (t : List α)
    (ha : p a = false) :
    (a :: t).filter p = ((a :: t).rotate 1).filter p := by
  rw [List.rotate_cons_succ, List.rotate_zero]
  simp [ha, List.filter_append]

/-- **HOL `newvertex_alt`**（reduction2.hl:620）：`newvertex` 在 `rotate_to f w`
（w = next_el f x）上的展开形。 -/
theorem newvertexAlt (L : fgraph ℕ) (r : List Dart) (x : Dart)
    (hnd : (Kepler.Assembly.findFaceDarts L x).Nodup)
    (hx : x ∈ Kepler.Assembly.findFaceDarts L x) (hxr : x ∈ r) :
    Kepler.Text.Reduction3.newvertex L r x =
      ((Kepler.Text.Reduction3.rotateTo (Kepler.Assembly.findFaceDarts L x)
          (Kepler.Assembly.nextEl (Kepler.Assembly.findFaceDarts L x) x)).filter
        (fun d => d ∉ r)).map (fun d => d.1) := by
  show ((Kepler.Text.TameSpine.rotateTo (Kepler.Assembly.findFaceDarts L x) x).filter
      (fun d => d ∉ r)).map (fun d => d.1) =
    ((Kepler.Text.TameSpine.rotateTo (Kepler.Assembly.findFaceDarts L x)
        (Kepler.Assembly.nextEl (Kepler.Assembly.findFaceDarts L x) x)).filter
      (fun d => d ∉ r)).map (fun d => d.1)
  have hfilter : (Kepler.Text.TameSpine.rotateTo (Kepler.Assembly.findFaceDarts L x) x).filter
        (fun d => d ∉ r) =
      (Kepler.Text.TameSpine.rotateTo (Kepler.Assembly.findFaceDarts L x)
        (Kepler.Assembly.nextEl (Kepler.Assembly.findFaceDarts L x) x)).filter
        (fun d => d ∉ r) := by
    -- rotateTo f x = x :: tail（cons 结构，定义级）
    have hrot : Kepler.Text.TameSpine.rotateTo (Kepler.Assembly.findFaceDarts L x) x =
        x :: (Kepler.Text.TameSpine.rotateTo (Kepler.Assembly.findFaceDarts L x) x).tail := rfl
    conv_lhs => rw [hrot]
    rw [filterRotateOneCons (fun d => d ∉ r) x _ (by simp [hxr])]
    have hr1 : (x :: (Kepler.Text.TameSpine.rotateTo (Kepler.Assembly.findFaceDarts L x) x).tail).rotate 1 =
        Kepler.Text.TameSpine.rotateTo (Kepler.Assembly.findFaceDarts L x)
          (Kepler.Assembly.nextEl (Kepler.Assembly.findFaceDarts L x) x) := by
      rw [← hrot]
      exact rotate1RotateTo hnd hx rfl
    rw [hr1]
  rw [hfilter]

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.catEq
#print axioms Kepler.Text.Reduction5.rotate1Rcons
#print axioms Kepler.Text.Reduction5.rotEqNil
#print axioms Kepler.Text.Reduction5.rotateToUniq
#print axioms Kepler.Text.Reduction5.rotate1RotateTo
#print axioms Kepler.Text.Reduction5.newvertexAlt
