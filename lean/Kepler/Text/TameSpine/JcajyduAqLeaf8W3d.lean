/-
  JcajyduAqLeaf8W3d — AQ8 波 3d-ii：`hsface` 判定件 A + 弱化版新定理。

  ┌─ 判定件 A 结论（机器证据 logs/probe_w3d2.log）──────────────────
  │ `hsface`（`∀ a ∈ s, a ∈ findFaceDarts L x`）的**内点**部分等价于
  │ 「`r` 的成员都在面 `x` 内」（`r ⊆ face x`）：
  │   `a ∈ r → a ∈ face x → a ∈ findFaceDarts L x`
  │ 由 `memFindFaceDartsOfMemFace`（ZUnlock:61，face ↦ findFaceDarts 桥）+
  │ `arcSubset`（W3b-i）逐字给出。故本波把该缺口**提成唯一命名前提**，
  │ 落弱化版新定理 ①（**不改已落库的 `aq8w3c_fstHdInjParts`**）。
  │ 端点无需新件：`pplhuljV0` / `markedLemmaYzInFace`（TameList18:96）
  │ 已给 `l'y`、`l'z` 均在 `findFaceDarts L x`。
  └────────────────────────────────────────────────────────────────

  ┌─ 件目（≤250，本波一件 + 判定记录）────────────────────────────
  │ ① aq8w3d_sSubFaceDarts  弱化版：`r ⊆ face x`（+ `x ∈ findFaceDarts L x`）
  │    ⇒ `∀ a ∈ s, a ∈ findFaceDarts L x`（= `hsface` 的消槽形）
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）────────────────────────────────────────────────
  │ ① `set_of_list` ↦ `findFaceDarts`；`face (hypermap_of_list L) x` ↦
  │    `(hypermapOfList L hL).face x`；`MEM`/`set` 逐字。
  │ ② 载体语境前提 `hR : ∀ a ∈ r, a ∈ face x` 为**已命名的唯一缺口**
  │    （AQ8 应用侧 = 「r 是面 x 的块」；本波未落，见 DELIVERY
  │    §AQ8W3d2-2）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3d_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3c
import Kepler.Text.TameSpine.JcajyduAqZUnlock
import Kepler.Text.TameSpine.TameList18

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-- **`hsface` 的消槽形（弱化版新定理）**：`s` 的成员进面 x 的
`findFaceDarts`，前提只有两条载体语境件：
`x ∈ findFaceDarts L x`（`dart_in_face` 供）与
`hR : ∀ a ∈ r, a ∈ face x`（「r 是面 x 的块」——**唯一缺口**，已命名）。

路径：`s ⊆ r`（W3b-i `arcSubset`）⇒ `a ∈ r` ⇒ `a ∈ face x`（`hR`）
⇒ `a ∈ findFaceDarts L x`（`memFindFaceDartsOfMemFace`，ZUnlock:61）。 -/
theorem aq8w3d_sSubFaceDarts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {s : List (ℕ × ℕ)}
    (harc : s = [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x])
    (hxd : x ∈ findFaceDarts L x)
    (hR : ∀ a ∈ r, a ∈ (hypermapOfList L hL).face x) :
    ∀ a ∈ s, a ∈ findFaceDarts L x := by
  intro a ha
  have har : a ∈ r := aq8w3b_arcSubset L hL hgn hm hf harc a ha
  exact memFindFaceDartsOfMemFace hL hxd (hR a har)

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3d_sSubFaceDarts
