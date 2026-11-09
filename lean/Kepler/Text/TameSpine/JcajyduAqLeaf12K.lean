/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12K — AQ12 叶 W5a（F2 首波，decls 34–39）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:1509-:1657（149 HOL 行）
  · decl 34 `y_mem_split_snd`       （:1509-:1520，12 行）
  · decl 35 `next_y_mem_split_snd`  （:1521-:1533，13 行）
  · decl 36 `one_step_ytran`        （:1534-:1573，40 行）
  · decl 37 `z_mem_split_snd`       （:1574-:1596，23 行）
  · decl 38 `one_step_ztran`        （:1597-:1642，46 行）
  · decl 39 `prev_z_mem_split_snd`  （:1643-:1657，15 行）

  ┌─ 路线（定义性成员 + loop_list 投影，替代 HOL 的 transform 展开）──────
  │ 34/35/37/39 四件「split 成员」全是定义性事实（`splitNormalListSpine`
  │ 的 f1/f2 端元）：
  │   split.1 = new1.reverse ++ f1，
  │     f1 = [nextEl r y] ++ between r (nextEl r y) z1 ++ [z1]；
  │   split.2 = f2 ++ new2，
  │     f2 = [nextEl r z1] ++ between r (nextEl r z1) y ++ [y]。
  │ 于是 `nextEl r y` 与 `z1` 分别在 FST 首/尾、`y` 在 SND 尾；`z` 在 SND 头，
  │ 唯一非定义性步骤是 `nextEl r (prevEl r z) = z`（`nextElPrevElUniq`，
  │ 需 `r.Nodup`，由 marked_list 的 normal_list 合取给出）。
  │ 36/38 两件「one_step」不走 HOL 的 rtrans/ztran 全展开：marked_list 的
  │ normal_list 合取直接给 `loopListSpine L r`（逐点 `oneStepListSpine`），
  │ 配 `ytransMemRtrans` / `zMemRtransClean` 的 r-成员性即得
  │ （与 AQ4 W2 的 `oneStepListSpine` 消费同源）。
  └────────────────────────────────────────────────────────────────────

  ┌─ 消费点记账（编排者要求）─────────────────────────────────────────
  │ 本波六件是 decls 40/41（`exists_contour_snd_fst` / `_fst_snd`，W5b）
  │ 的直接前置。**W5a 零消费 F1 收口件 27/28/29**（`aqs_indexfSizelBetwnFlatten`
  │ / `aqs_memFlattenBetwnSym` / `aqs_memFlattenBetwnSymCase`）；F2 后续若用到
  │ 29 的「位置⇒归属」收口，从 40/41 起标。
  └────────────────────────────────────────────────────────────────────

  载体：`List (ℕ × ℕ)`（与 AQ12 全段一致）。
  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12J

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList prevEl_mem_of_mem)

/-! ## §0 HOL AQ12.hl:1509 `y_mem_split_snd` -/

/-- **HOL `y_mem_split_snd`**（AQ12.hl:1509-:1520）：
`y` 是 `split_normal_list L r f y z1` 的 SND 末元（f2 的 [ram1] 端）。 -/
theorem aqs_yMemSplitSnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r2 : List (ℕ × ℕ)} (hz : lZSpine L N r x = z)
    (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hr2 : (splitNormalListSpine L r f y z1).2 = r2) :
    y ∈ r2 := by
  rw [← hr2, ← hz1, ← hz, ← hy]
  simp [splitNormalListSpine]

/-! ## §1 HOL AQ12.hl:1521 `next_y_mem_split_snd` -/

/-- **HOL `next_y_mem_split_snd`**（AQ12.hl:1521-:1533）：
`next_el r y` 是 split 的 FST 首元（f1 的 [ram1'] 端）。 -/
theorem aqs_nextYMemSplitSnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r1 : List (ℕ × ℕ)} (hz : lZSpine L N r x = z)
    (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hr1 : (splitNormalListSpine L r f y z1).1 = r1) :
    nextEl r y ∈ r1 := by
  rw [← hr1, ← hz1, ← hz, ← hy]
  simp [splitNormalListSpine]

/-! ## §2 HOL AQ12.hl:1534 `one_step_ytran` -/

/-- **HOL `one_step_ytran`**（AQ12.hl:1534-:1573）：
`one_step_list L (l'y L r x) (next_el r (l'y L r x))`——marked_list 的
`loop_list r` 合取逐点给出，`y ∈ r` 由 `ytrans_mem_rtrans` 提供。 -/
theorem aqs_oneStepYtran (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    oneStepListSpine L (lYSpine L r x) (nextEl r (lYSpine L r x)) := by
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  exact (hloop (lYSpine L r x) hy).2

/-! ## §3 HOL AQ12.hl:1574 `z_mem_split_snd` -/

/-- **HOL `z_mem_split_snd`**（AQ12.hl:1574-:1596）：
`z` 是 split 的 SND 首元（f2 的 [next_el r z1] 端，z1 = prev_el r z）。 -/
theorem aqs_zMemSplitSnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r2 : List (ℕ × ℕ)} (hz : lZSpine L N r x = z)
    (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hr2 : (splitNormalListSpine L r f y z1).2 = r2) :
    z ∈ r2 := by
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  rw [← hr2, ← hz1, ← hz, ← hy]
  have hnext : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  simp [splitNormalListSpine, hnext]

/-! ## §4 HOL AQ12.hl:1597 `one_step_ztran` -/

/-- **HOL `one_step_ztran`**（AQ12.hl:1597-:1642）：
`one_step_list L (prev_el r (l'z L N r x)) (l'z L N r x)`——同 §2，配
`nextEl_prevEl` 把 `next_el r z1` 折回 `z`。 -/
theorem aqs_oneStepZtran (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    oneStepListSpine L (prevEl r (lZSpine L N r x)) (lZSpine L N r x) := by
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hz1 : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hz
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  have h := (hloop (prevEl r (lZSpine L N r x)) hz1).2
  rwa [nextElPrevElUniq hrnd] at h

/-! ## §5 HOL AQ12.hl:1643 `prev_z_mem_split_snd` -/

/-- **HOL `prev_z_mem_split_snd`**（AQ12.hl:1643-:1657）：
`z1 = prev_el r z` 是 split 的 FST 末元（f1 的 [ram2] 端）。 -/
theorem aqs_prevZMemSplitSnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r1 : List (ℕ × ℕ)} (hz : lZSpine L N r x = z)
    (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hr1 : (splitNormalListSpine L r f y z1).1 = r1) :
    z1 ∈ r1 := by
  rw [← hr1, ← hz1, ← hz, ← hy]
  simp [splitNormalListSpine]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_yMemSplitSnd
#print axioms Kepler.Text.TameSpine.aqs_nextYMemSplitSnd
#print axioms Kepler.Text.TameSpine.aqs_oneStepYtran
#print axioms Kepler.Text.TameSpine.aqs_zMemSplitSnd
#print axioms Kepler.Text.TameSpine.aqs_oneStepZtran
#print axioms Kepler.Text.TameSpine.aqs_prevZMemSplitSnd
