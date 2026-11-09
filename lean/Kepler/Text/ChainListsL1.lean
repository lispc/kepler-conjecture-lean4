/-
  Kepler.Text.ChainLists — J 战役 DEF-FIX「链世界列表定义族」L1 步：
  `normalList` / `loopList` / `findList`（+ 两个必要辅助 `oneStepList` / `fLast`）。

  ┌─ 章程与范围（docs/def-fix-charters/chain-list-defs/CHARTER.md）──
  │ 本项**只落定义**，零陈述改动、零证明义务（除 rfl 级 findListNil）；
  │ 不动 Spine 双家（TameList5/7 的同名族保留）；L2（flagList/
  │ sFlagList/markedList）另派不并入。DF_SORRY_NET = 0。
  └────────────────────────────────────────────────────────────────

  ┌─ 逐件 HOL 锚（reference/flyspeck/text_formalization/tame/）──────
  │   one_step_list  tame_defs2.hl:81-82 → oneStepList（辅助①）
  │   f_last         tame_defs2.hl:78-79 → fLast（辅助②）
  │   loop_list      tame_defs2.hl:84-86 → loopList
  │   normal_list    tame_defs2.hl:93-100 → normalList（5 合取块逐字）
  │   find_list      formal_lp/hypermap/ssreflect/list_hypermap-compiled.hl:49-50
  │                  → findList（两方程递归）
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与 DIFFERS（交编排者知悉）──────────────────────────────
  │ ① 绑定链世界 `fgraph ℕ = List (List ℕ)` + `Dart = ℕ × ℕ`，不复用
  │    Spine 侧件（NormalListSpine 等仅作文本参考）。
  │ ② **`normal_list` 的第 5 合取含 `node (hypermap_of_list L) d`**——
  │    HOL 的 `hypermap_of_list` 对 L 全定义，树内唯一载体
  │    `TameLp.hypermapOfList L (hL : GoodList L)`（TameLp.lean:5188）
  │    吃 `GoodList L`（构造需 `(listOfDarts L).Nodup`）。故 `normalList`
  │    取显式参数 `(hL : GoodList L)`——与链侧既有先例
  │    `GoodListNodesTl L (hL : GoodList L)`（TameLp.lean:5278）同形；
  │    消费侧实例化配方 `fun L => ∀ hL, …`（D3b 三载体同款）。
  │ ③ `LAST` junk：HOL `LAST []` 为任意值（`f_last` 无前缀守卫）；Lean
  │    侧 `f_last` 落 `List.getLastD (0,0)` 确定性缺省（normalList 的
  │    `all nonnil` 合取使正常输入上 junk 支不可达；空表情形两库同属
  │    junk 语义，逐字记档不动陈述）。
  │ ④ `find_list` 的 `MEM x h` ↦ `x ∈ h`（Decidable，ℕ×ℕ 派生实例）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ imports = `Kepler.Text.Reduction5Base`（链岛：TameLp + GoodListDefs
  │ + ListAux；闭包零 Kepler.Assembly 主模块、零 TameSpine）。
  │ 零 axiom/sorry/admit/native_decide。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5Base

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.ChainLists

open Kepler.Assembly (GoodList nextEl eList fList listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart)
open Kepler.Text.TameLp (hypermapOfList)

/-! ## §A 辅助件（tame_defs2.hl:78-82）

`one_step_list`：一步移动 = 前进到 `f_list L x` 或经对径 `e_list x` 的
`f_list`。`f_last`：表 `s` 的末元满足 `next_el s (LAST s) = f_list L
(LAST s)`（即末元的 f 后继环回到表首）。 -/

/-- HOL `one_step_list`（tame_defs2.hl:81-82）。 -/
def oneStepList (L : fgraph ℕ) (x y : Dart) : Prop :=
  y = fList L x ∨ y = fList L (eList x)

/-- HOL `f_last`（tame_defs2.hl:78-79）：`next_el s (LAST s) = f_list L
(LAST s)`（junk 缺省 `(0,0)`，见文件头 DIFFERS-③）。 -/
def fLast (L : fgraph ℕ) (s : List Dart) : Prop :=
  nextEl s (s.getLastD (0, 0)) = fList L (s.getLastD (0, 0))

/-! ## §B `loop_list`（tame_defs2.hl:84-86）

`s` 的每个 dart 都在 `list_of_darts L` 中，且 `s` 上的下一步
（`next_el s x`）满足一步关系。 -/

/-- HOL `loop_list`（tame_defs2.hl:84-86）。 -/
def loopList (L : fgraph ℕ) (s : List Dart) : Prop :=
  ∀ x ∈ s, x ∈ listOfDarts L ∧ oneStepList L x (nextEl s x)

/-! ## §C `normal_list`（tame_defs2.hl:93-100，5 合取块逐字）

`uniq (flatten N)` / 各面非空 / 各面 `f_last` / 各面 `loop_list` /
每个 dart 的 `node`（hypermap 顶点轨道）落在 `flatten N` 内。 -/

/-- HOL `normal_list`（tame_defs2.hl:93-100）。`hL : GoodList L` 为树内
`hypermapOfList` 载体的显式前提（文件头 DIFFERS-②）。 -/
noncomputable def normalList (L : fgraph ℕ) (hL : GoodList L)
    (N : List (List Dart)) : Prop :=
  N.flatten.Nodup ∧
  (∀ s ∈ N, s ≠ []) ∧
  (∀ s ∈ N, fLast L s) ∧
  (∀ s ∈ N, loopList L s) ∧
  (∀ d ∈ N.flatten, (hypermapOfList L hL).node d ⊆ {x : Dart | x ∈ N.flatten})

/-! ## §D `find_list`（list_hypermap-compiled.hl:49-50）

`find_list [] x = []` / `find_list (h::t) x = if MEM x h then h else
find_list t x`（第一个包含 `x` 的面；`find_face` 即其 list_pairs 版）。 -/

/-- HOL `find_list`（list_hypermap-compiled.hl:49-50）。 -/
def findList : List (List Dart) → Dart → List Dart
  | [], _ => []
  | h :: t, x => if x ∈ h then h else findList t x

/-- 定义即引理：`findList` 空表方程（rfl 级）。 -/
theorem findListNil (x : Dart) : findList [] x = [] := rfl

end Kepler.Text.ChainLists

-- 探针（编译即执行）：签名比对 + 公理
#check @Kepler.Text.ChainLists.oneStepList
#check @Kepler.Text.ChainLists.fLast
#check @Kepler.Text.ChainLists.loopList
#check @Kepler.Text.ChainLists.normalList
#check @Kepler.Text.ChainLists.findList
#print axioms Kepler.Text.ChainLists.findListNil
