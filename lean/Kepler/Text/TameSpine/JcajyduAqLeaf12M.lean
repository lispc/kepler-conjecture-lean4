/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12M — AQ12 叶 W6a（F2，decls 42–44）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:1829-:1943（115 HOL 行）
  · decl 42 `one_step_e_list_w`（:1829-:1874，46 行）
  · decl 43 `one_step_e_list_x`（:1875-:1919，45 行）
  · decl 44 `w_mem_split_snd`（:1920-:1943，24 行）

  ┌─ 开工报价（件目 + 行数区间 + 依赖）────────────────────────────
  │ 3 件 / 1 文件；估 100–160 行（≤300，不拆 W6a-i/ii）。
  │ 依赖（**本波不吃 `h4` 槽**——与 W5b DIFFERS）：
  │ · decl 42/43 是**定义性事实**：`fList L d = nextEl (findFaceDarts L d) d`、
  │   `eList (eList d) = d`、`oneStepListSpine` 的第二析取即 `fList (eList x)`；
  │   HOL 两段 45/46 行的展开在 Lean 分别收为 4 行 / 1 行。
  │ · decl 44 消费**已落库的真定理** `aq7`（JcajyduAqLeaf7:121，`x ∈ rtrans 1`）
  │   与 `aq10`（JcajyduAqLeaf10G:26，`nextEl (rtrans 1) x = fList L x`）；
  │   无需 AQ4 的 loop_list 槽，故**无条件形**。
  │   （HOL 证体的 `Aq7.AQ7`/`Aq10.AQ10` 槽 = 本树这两个真定理。）
  └────────────────────────────────────────────────────────────────

  ┌─ 路线 ─────────────────────────────────────────────────────────
  │ 42：`one_step_list L (e_list x) w` 取**第二析取**
  │     `w = fList L (eList (eList x)) = fList L x`；
  │     由 `find_face x = f`、`next_el f x = w` 与 `fList` 定义直接得
  │     `w = nextEl f x = fList L x`。
  │ 43：`one_step_list L x ((f_list L)(e_list x))` 的第二析取是 **rfl**
  │     （`fList L (eList x) = fList L (eList x)`）。
  │ 44：`aq7` 给 `x ∈ rtrans 1`；`aq10` 给 `nextEl (rtrans 1) x = fList L x`；
  │     于是 `fList L x ∈ rtrans 1`（`nextEl_mem_of_mem`），再用
  │     `rtrans 1 = canonical split.2 = f-split.2 = r2` 三段落回 `r2`；
  │     `w = fList L x` 由 42 同款计算收口。
  └────────────────────────────────────────────────────────────────

  载体：`List (ℕ × ℕ)`。纪律：零 sorry/admit/native_decide/axiom 声明；
  既有文件零触碰；主仓 tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12L
import Kepler.Text.TameSpine.JcajyduAqLeaf7
import Kepler.Text.TameSpine.JcajyduAqLeaf10G

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList nextEl_mem_of_mem)

/-! ## §0 共同引理：`eList` 对合 -/

/-- `eList` 是对合：`eList (eList d) = d`（`eList d = (d.2, d.1)`）。 -/
private theorem aq12m_eListEList (d : ℕ × ℕ) : eList (eList d) = d := by
  cases d
  rfl

/-! ## §1 HOL AQ12.hl:1829 `one_step_e_list_w` -/

/-- **HOL `one_step_e_list_w`**（AQ12.hl:1829-:1874）：
`e_list x` 到 `w = next_el (find_face x) x = f_list L x` 是 one-step
（取 `one_step_list` 的第二析取：`w = f_list L (e_list (e_list x))`）。 -/
theorem aqs_oneStepEListW (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ)) (hfind : findFaceDarts L x = f)
    {w : ℕ × ℕ} (hw : nextEl f x = w) :
    oneStepListSpine L (eList x) w := by
  refine Or.inr ?_
  rw [aq12m_eListEList, fList, hfind, ← hw]

/-! ## §2 HOL AQ12.hl:1875 `one_step_e_list_x` -/

/-- **HOL `one_step_e_list_x`**（AQ12.hl:1875-:1919）：
`x` 到 `f_list L (e_list x)` 是 one-step（第二析取 **rfl**）。 -/
theorem aqs_oneStepEListX (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ)) (hfind : findFaceDarts L x = f)
    {w : ℕ × ℕ} (hw : nextEl f x = w) :
    oneStepListSpine L x (fList L (eList x)) :=
  Or.inr rfl

/-! ## §3 HOL AQ12.hl:1920 `w_mem_split_snd` -/

/-- **HOL `w_mem_split_snd`**（AQ12.hl:1920-:1943）：
`w = next_el (find_face x) x` 落在 `SND split` 行。
消费已落库真定理 `aq7`（`x ∈ rtrans 1`）与 `aq10`（`nextEl (rtrans 1) x = fList L x`）。 -/
theorem aqs_wMemSplitSnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r2 : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hr2 : (splitNormalListSpine L r f y z1).2 = r2)
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    w ∈ r2 := by
  -- canonical 面的对齐：findFace(l'y) = findFace x = f
  have hz1canon : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
    (aq10_memFindFaceImpFacesEq hL.1 hpp.1).trans hfind
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x)))
      = splitNormalListSpine L r f y z1 := by
    rw [← hfindcanon, ← hy, ← hz1canon]
  -- rtrans 1 = canonical split.2 = f-split.2 = r2
  have hr' : rtransSpine L N r x 1
      = (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
    show ((transformListSpine L x)^[1] (N, r)).2 = _
    rw [Function.iterate_one]
    simp only [transformListSpine, if_neg hf]
  have hconv : rtransSpine L N r x 1 = r2 := by
    rw [hr', hsplit_eq, hr2]
  -- aq7 + aq10 ⇒ fList x ∈ r2
  have h7 := aq7 L hL N r x hgn hm
  have h10 := aq10 L hL N r x hgn hm
  have hmem : fList L x ∈ r2 := by
    rw [← hconv, ← h10]
    exact nextEl_mem_of_mem h7
  -- w = fList x
  have hwF : w = fList L x := by
    rw [← hw, ← hfind, fList]
  rw [hwF]
  exact hmem

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_oneStepEListW
#print axioms Kepler.Text.TameSpine.aqs_oneStepEListX
#print axioms Kepler.Text.TameSpine.aqs_wMemSplitSnd
