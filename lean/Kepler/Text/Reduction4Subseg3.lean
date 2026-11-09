/-
  Kepler.Text.Reduction4Subseg3 — J 战役 J1 板 B5-B（reduction4.hl 自由件第二批）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/reduction4.hl`）──
  │ :3864 `take_eq_nil`  → take_eq_nil
  │ :1509 `HD_flatten`   → HD_flatten
  │ :3916 `ifbetwn_rot`  → ifbetwn_rot
  │ :2420 `marked_x_exists` → **BLOCKED**：结论
  │   `∃ w, (prev_el (core L r) w, w) = x` 的 HOL 证体直投
  │   `More_lemma2.hl:39 FST_next_face_eq_SND` + `More_lemma2.hl:82
  │   prev_core_x`；前半本树已有等价件
  │   `Kepler.Text.MoreLemma2Island3.fListFstSnd`（:196），**后半
  │   `prev_core_x`（`prev_el (core L r) (FST (next_el (find_face L x) x))
  │   = FST x`）全树 grep 0**——不在 import 可达面，不绕桩凑证（AGENTS §2）。
  │   详见 DELIVERY §5。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与导入纪律 ──────────────────────────────────────────────
  │ `take` ↦ `List.take`；`HD` ↦ `List.head!`（批 11/12 既档）；`flatten`
  │ ↦ `List.flatten`；`rot` ↦ `List.rotate`（Mathlib，`drop ++ take`）。
  │ 环安全：新增 import 只有 `Kepler.Graphs.FaceDivisionProps1`——其
  │ Kepler.* 闭包实测仅 8 个 Graphs 模块
  │ （FaceDivision/FaceDivisionProps1/Graph/GraphProps/ListAux/
  │  ListAuxLemmas/Rotation/RotationLemmas），**零 `Kepler.Assembly`、
  │  零 `Kepler.Text.TameSpine.*`**，不破坏 Reduction5 岛纪律。
  │ 该 import 只为 `Kepler.Graphs.between_congs`（FaceDivisionProps1:1505，
  │ 已证 `pre_between` 下 `between` 对任意 `rotate n` 不变）。
  │ 零 axiom/sorry/admit/native_decide；泛型 binder 只用 `[DecidableEq α]`。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction4Subseg2
import Kepler.Graphs.FaceDivisionProps1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (between between_congs pre_between)
open Kepler.Text.Reduction5 (ifbetwn)

/-! ## §1 `take_eq_nil`（reduction4.hl:3864） -/

/-- **HOL `take_eq_nil`**（reduction4.hl:3864）：`take k r = [] ⇔ k = 0 ∨ r = []`。
Lean core 逐字同语句件 `List.take_eq_nil_iff`（Init/Data/List/TakeDrop.lean:143），
零镜像直投。 -/
theorem take_eq_nil {α : Type*} (r : List α) (k : ℕ) :
    r.take k = [] ↔ k = 0 ∨ r = [] :=
  List.take_eq_nil_iff

/-! ## §2 `HD_flatten`（reduction4.hl:1509） -/

/-- **HOL `HD_flatten`**（reduction4.hl:1509）：
`~(s = []) ∧ ~(HD s = []) ⇒ HD (flatten s) = HD (HD s)`。

路线：`HD ↦ List.head!`（本树既有约定），证体是**定义性**的——HOL 走
`Seq.flatten_cons` + `Tame_list.hd_cat`，Lean 侧 `flatten` 的 cons 支与
`headD` 的 cons 支都按构造子归约，故 `cases s; cases s.head` 后两非空支
`rfl`，两空支被前提直接排除（`h2` 在 `s = [] :: ts` 时即 `[] ≠ []`）。 -/
theorem HD_flatten {α : Type*} [Inhabited α] {s : List (List α)}
    (h1 : s ≠ []) (h2 : s.head! ≠ []) :
    s.flatten.head! = s.head!.head! := by
  cases s with
  | nil => exact absurd rfl h1
  | cons a ts =>
    cases a with
    | nil => exact absurd rfl h2
    | cons b bs => rfl

/-! ## §3 `ifbetwn_rot`（reduction4.hl:3916） -/

section IfbetwnRot

variable {α : Type*} [DecidableEq α]

/-- `between` 的旋转不变性（HOL `Reduction2.betwn_rot` 在 Lean 侧的借用件）：
`Kepler.Graphs.between_congs` 已证 `pre_between` 下 `between vs x y =
between (vs.rotate n) x y` 对**任意** `n`（其 `hstep` 对 `n` 归纳，单步走
`pre_between_rotate`），而 `pre_between` 的四元组恰是 `Nodup ∧ x ∈ s ∧
y ∈ s ∧ x ≠ y` ⇒ 直接投，无需 HOL 的 `n ≤ sizel s` / `rot_oversize` 二分
（Lean `List.rotate` 定义即 `drop n ++ take n`，oversize 自动落回原表）。 -/
private theorem between_rotate {s : List α} (hnd : s.Nodup) {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (n : ℕ) :
    between (s.rotate n) x y = between s x y :=
  (between_congs ⟨hnd, hx, hy, hxy⟩ ⟨n, rfl⟩).symm

/-- **HOL `ifbetwn_rot`**（reduction4.hl:3916）：
`uniq s ⇒ ifbetwn (rot n s) x y = ifbetwn s x y`。

路线：`ifbetwn` 展开后按守卫 `x ∈ s ∧ y ∈ s ∧ x ≠ y` 二分；守卫在旋转下
等价（`List.mem_rotate`），真支用 `between_rotate` 把 `between (s.rotate n)`
换回 `between s`，两支都只改 `if_pos`/`if_neg` 的条件形。 -/
theorem ifbetwn_rot {s : List α} (hnd : s.Nodup) (x y : α) (n : ℕ) :
    ifbetwn (s.rotate n) x y = ifbetwn s x y := by
  unfold ifbetwn
  by_cases hc : x ∈ s ∧ y ∈ s ∧ x ≠ y
  · have hc' : x ∈ s.rotate n ∧ y ∈ s.rotate n ∧ x ≠ y :=
      ⟨List.mem_rotate.mpr hc.1, List.mem_rotate.mpr hc.2.1, hc.2.2⟩
    rw [if_pos hc', if_pos hc, between_rotate hnd hc.1 hc.2.1 hc.2.2 n]
  · have hc' : ¬ (x ∈ s.rotate n ∧ y ∈ s.rotate n ∧ x ≠ y) := by
      intro h
      exact hc ⟨List.mem_rotate.mp h.1, List.mem_rotate.mp h.2.1, h.2.2⟩
    rw [if_neg hc', if_neg hc]

end IfbetwnRot

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（本文件编译即执行；预期 ≤ 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.Reduction4Idx.take_eq_nil
#print axioms Kepler.Text.Reduction4Idx.HD_flatten
#print axioms Kepler.Text.Reduction4Idx.ifbetwn_rot
