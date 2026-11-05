/-
  Kepler.Text.Reduction5Base — `Reduction5` 的定义基座（W0）。

  **来源**：HOL Light Flyspeck `text_formalization/tame/tame_defs2.hl`（`Tame_defs2`）
  与 `text_formalization/tame/tame_defs.hl`（`Tame_defs`）的逐句重落。本文件只含
  **定义**（定理层在 `Kepler/Text/Reduction5.lean`；本文件唯一带证明的声明是
  `finalList` 的 `Decidable` 实例，只为 `transformList` 的 `if` 求决）。

  **环纪律**（DECISIONS.md 2026-11-06「Reduction5 口径改口」）：
  唯一 import = `Kepler.Text.TameLp` + `Kepler.Graphs.ListAux`；两者 import 闭包
  **不含** `Kepler.Assembly`（侦察 `reduction5-scout` 判过；本车道静态复核与
  `#check` 探针见交付 `Evidence.md` E-4）。
  **绝不** import 任何 `Kepler.Text.TameSpine.*`：岛 74/75 经
  `TameList1.lean:37 import Kepler.Assembly` 传递成环，会让 Assembly 拒收整棵树。

  **类型特化**：HOL 的 `A` 在本链全部使用点均为 `num#num`（tame 归档的 dart 类型），
  且复用的 `f_list`/`e_list`/`n_list`/`find_face`/`list_pairs`/`good_list`
  （`Kepler.Assembly.GoodListDefs`，由 `TameLp` 转出）本身已特化到 `fgraph ℕ` /
  `ℕ × ℕ`。故本模块同特化：`Dart := ℕ × ℕ`；`L : fgraph ℕ = List (List ℕ)`
  （面 = **顶点**表，HOL `(A list) list`）；`N : List (List Dart)`（面 = **dart** 表，
  HOL `((A#A) list) list`）。特化只发生在类型层，定义体逐句对齐 HOL。

  **不复用**：`TameSpine` 岛内的同名件；也不复用 `Kepler.Text.minNum`
  （`LocalAuto1.lean:662`，该文件正被 SF-102 车道改写），本模块自带 `minNum`。

  **前提原语**（复用，不重定义；锚点逐一核对）：
  - `sizel` = `List.length`（`jHOLLight/Examples/seq-compiled.hl:18`）；
  - `POWER` = `f^[n]` = `Nat.iterate`（`hypermap/hypermap.hl:36`）；
  - `ITER` = 同 `POWER`（`azure/hol-light-nat/Library/iter.ml:9`）；
  - `upt i j` = `List.range' i (j - i)`（`tame_defs.hl:387`）；
  - `rcons l z` = `l ++ [z]`（`jHOLLight/Examples/seq-compiled.hl:128`）；
  - `betwn` = `Kepler.Graphs.between`（`tame_defs.hl:335` ↔ `ListAux.lean:27`）；
  - `list_pairs` = `listPairs`（`list_hypermap-compiled.hl:22`）；
  - `find_face`/`f_list`/`e_list`/`n_list` = `findFaceDarts`/`fList`/`eList`/`nList`
    （`list_hypermap-compiled.hl:53/54/55/56`）；
  - `next_el`/`prev_el` = `nextEl`/`prevEl`（`tame/ssreflect/seq2-compiled.hl:24/26`）。
-/
import Kepler.Text.TameLp
import Kepler.Graphs.ListAux

namespace Kepler.Text.Reduction5

open Kepler.Assembly
open Kepler.Graphs

/-- dart 类型：HOL `A#A` 在 tame 链的唯一实例（`num#num`）。 -/
abbrev Dart : Type := ℕ × ℕ

/-! ## 0. `min_num`（`tame_defs.hl:313`）

HOL：`min_num X = (@m. m IN X /\ (!n. n IN X ==> m <= n))`
（`@` 是 Hilbert 选择 `Classical.epsilon`）。空集上取值未定义（与 HOL 一致）。
本模块自带一份，避免依赖正被 SF 车道改写的 `LocalAuto1.lean`。 -/
noncomputable def minNum (S : Set ℕ) : ℕ :=
  Classical.epsilon (fun m => m ∈ S ∧ ∀ n ∈ S, m ≤ n)

/-! ## 1. `partition_into_atom*` / `parts` / `core` / `quotient_list`

HOL `tame_defs2.hl:108-136`。`partition_into_atom0` 是 `list_RECURSION` 上的
递归定义：把 `rev r` 扫一遍，把 `(f_list L) o e_list` 取值相同的**相邻**元素
聚成一个 atom（atom 内保持扫描序，故 atom 是原序的**逆序**片段）。
Lean 侧用结构递归逐分支镜像；HOL 的 `HD (HD acc)` 在内层为空表时是 junk
（不可达状态：每个 atom 非空），Lean 用 `headD r` 补全，可达输入上逐值一致。 -/

/-- HOL `partition_into_atom0`（`tame_defs2.hl:111-117`）。 -/
def partitionIntoAtom0 (n : Dart → Dart) : List (List Dart) → List Dart → List (List Dart)
  | acc, [] => acc
  | [], r :: rs => partitionIntoAtom0 n [[r]] rs
  | a :: acc, r :: rs =>
    if n r == a.headD r then partitionIntoAtom0 n ((r :: a) :: acc) rs
    else partitionIntoAtom0 n ([r] :: a :: acc) rs

/-- HOL `partition_into_atom0r`（`tame_defs2.hl:119-121`）。 -/
def partitionIntoAtom0r (n : Dart → Dart) (acc : List (List Dart)) (r : List Dart) :
    List (List Dart) :=
  partitionIntoAtom0 n acc r.reverse

/-- HOL `partition_into_atom`（`tame_defs2.hl:123-124`）。 -/
def partitionIntoAtom (n : Dart → Dart) (r : List Dart) : List (List Dart) :=
  partitionIntoAtom0 n [] r.reverse

/-- HOL `parts`（`tame_defs2.hl:126-127`）：`partition_into_atom ((f_list L) o e_list) r`。 -/
def parts (L : fgraph ℕ) (r : List Dart) : List (List Dart) :=
  partitionIntoAtom (fun d => fList L (eList d)) r

/-- HOL `core`（`tame_defs2.hl:129-130`）：`MAP (FST o HD) (parts L r)`。
注意值域是 **顶点** 表（`FST` 把 atom 的首 dart 投到 `A`），不是 dart 表。 -/
def core (L : fgraph ℕ) (r : List Dart) : List ℕ :=
  (parts L r).map (fun l => (l.headD (0, 0)).1)

/-- HOL `core_list`（`tame_defs2.hl:108-109`）：对每面（atom 表）取每个 atom 的首 dart 的
`FST`。`PN : (A#B) list list list` 在此链只以 `map (parts L) N` 的形态出现。 -/
def coreList (PN : List (List (List Dart))) : List (List ℕ) :=
  PN.map (fun f => f.map (fun x => (x.headD (0, 0)).1))

/-- HOL `quotient_list`（`tame_defs2.hl:134-136`）：`core_list (map (parts L) N)`。 -/
def quotientList (L : fgraph ℕ) (N : List (List Dart)) : List (List ℕ) :=
  coreList (N.map (parts L))

/-! ## 2. `final_list`（`tame_defs2.hl:138-139`）

HOL：`final_list L r <=> all (\d. f_list L d = next_el r d) r`。
`all` 展开为 `∀ d ∈ r, ...`。附带 `Decidable` 实例：`transform_list` 的
`if (final_list L r)` 需要它，且实例把判定落在 `List.all` 的 Bool 反射上。 -/
def finalList (L : fgraph ℕ) (r : List Dart) : Prop :=
  ∀ d ∈ r, fList L d = nextEl r d

instance finalListDecidable (L : fgraph ℕ) (r : List Dart) : Decidable (finalList L r) :=
  decidable_of_iff (r.all (fun d => fList L d == nextEl r d) = true) (by
    simp [finalList, List.all_eq_true, beq_iff_eq])

/-! ## 3. `l'm` / `l'y` / `l'p` / `l'z`（`tame_defs2.hl:440-453`）

`l'm L r x`：最小的 `m`，使 `(next_el r)^(m+2) x ≠ f_list L ((next_el r)^(m+1) x)`
（即 `x` 的轨道在 `next_el r` 下第一次「离开 f 后继」的步数减一）。
`l'y`：从 `x` 出发沿 `f_list L` 走 `l'm + 1` 步。
`l'p`：最小的 `p`，使 `(f_list L)^(p+1) (l'y)` 落在 `flatten N` 里。
`l'z`：`(f_list L)^(l'p+1) (l'y)`。 -/

/-- HOL `l'm`（`tame_defs2.hl:440-443`）。 -/
noncomputable def lm (L : fgraph ℕ) (r : List Dart) (x : Dart) : ℕ :=
  minNum {m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)}

/-- HOL `l'y`（`tame_defs2.hl:445-446`）：`(f_list L)^(SUC (l'm)) x`。 -/
noncomputable def ly (L : fgraph ℕ) (r : List Dart) (x : Dart) : Dart :=
  (fList L)^[Nat.succ (lm L r x)] x

/-- HOL `l'p`（`tame_defs2.hl:448-450`）。 -/
noncomputable def lp (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) : ℕ :=
  minNum {p : ℕ | (fList L)^[Nat.succ p] (ly L r x) ∈ N.flatten}

/-- HOL `l'z`（`tame_defs2.hl:452-453`）。 -/
noncomputable def lz (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) :
    Dart :=
  (fList L)^[Nat.succ (lp L N r x)] (ly L r x)

/-! ## 4. `split_normal_list`（`tame_defs2.hl:167-177`）

把 `f`（`find_face L y` 的 dart 表）在 `ram1 = y` 与 `ram2 = prev_el r z` 之间切开，
并在 `new2 = betwn f ram1 ram2'` 的每个 dart 上插入 `n_list L` 的 1..sz-1 次迭代
（`sz v` = 顶点 `v` 在 `flatten L` 里的重数）。返回 `(f1, f2)` 两个新面（dart 表）。 -/

/-- HOL `split_normal_list`（`tame_defs2.hl:167-177`）。 -/
def splitNormalList (L : fgraph ℕ) (r : List Dart) (f : List Dart) (ram1 ram2 : Dart) :
    List Dart × List Dart :=
  let ram1' := nextEl r ram1
  let ram2' := nextEl r ram2
  let sz := fun (v : ℕ) => (L.flatten.filter (fun t => t == v)).length
  let nd := fun (x : Dart) => (List.range' 1 (sz x.1 - 1)).map (fun i => (nList L)^[i] x)
  let new2 := between f ram1 ram2'
  let new1 := (new2.map nd).flatten
  let f1 := [ram1'] ++ (between r ram1' ram2 ++ [ram2])
  let f2 := [ram2'] ++ (between r ram2' ram1 ++ [ram1])
  (new1.reverse ++ f1, f2 ++ new2)

/-! ## 5. `transform_list` 与变换族（`tame_defs2.hl:458-489`）

`transform_list L x` 是一次「拆面」变换：作用在 `(N, r)`（面表 × 当前面）上，
返回 `(N', r')`；`final_list L r` 时是恒等。`ntrans`/`rtrans` 是它的 `i` 次迭代的
两个投影；`ytrans`/`ztrans`/`ftrans`/`mtrans` 是迭代后的派生量；
`transform_count` 是首次到达 `final_list` 的迭代数。 -/

/-- HOL `transform_list`（`tame_defs2.hl:458-467`）。 -/
noncomputable def transformList (L : fgraph ℕ) (x : Dart) :
    List (List Dart) × List Dart → List (List Dart) × List Dart
  | (N, r) =>
    let y := ly L r x
    let z := lz L N r x
    let ram2 := prevEl r z
    let f := findFaceDarts L y
    let split := splitNormalList L r f y ram2
    let N' := replace r [split.2] N ++ [split.1]
    if finalList L r then (N, r) else (N', split.2)

/-- HOL `ntrans`（`tame_defs2.hl:469-470`）：`FST ((transform_list L x)^i (N,r))`。 -/
noncomputable def ntrans (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (i : ℕ) : List (List Dart) :=
  ((transformList L x)^[i] (N, r)).1

/-- HOL `rtrans`（`tame_defs2.hl:472-473`）：`SND ((transform_list L x)^i (N,r))`。 -/
noncomputable def rtrans (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (i : ℕ) : List Dart :=
  ((transformList L x)^[i] (N, r)).2

/-- HOL `ytrans`（`tame_defs2.hl:475-476`）。 -/
noncomputable def ytrans (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (i : ℕ) : Dart :=
  ly L (rtrans L N r x i) x

/-- HOL `ztrans`（`tame_defs2.hl:478-479`）。 -/
noncomputable def ztrans (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (i : ℕ) : Dart :=
  lz L (ntrans L N r x i) (rtrans L N r x i) x

/-- HOL `ftrans`（`tame_defs2.hl:481-482`）：`if i = 0 then SND x else FST (ztrans … (PRE i))`。
`PRE` 截断减，Lean 用 `i - 1`（`Nat` 同截断）。 -/
noncomputable def ftrans (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (i : ℕ) : ℕ :=
  if i = 0 then x.2 else (ztrans L N r x (i - 1)).1

/-- HOL `mtrans`（`tame_defs2.hl:484-485`）。 -/
noncomputable def mtrans (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (i : ℕ) : ℕ :=
  lm L (rtrans L N r x i) x

/-- HOL `transform_count`（`tame_defs2.hl:487-489`）：
`min_num {i | final_list L (rtrans L N r x i)}`。 -/
noncomputable def transformCount (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : ℕ :=
  minNum {i : ℕ | finalList L (rtrans L N r x i)}

/-! ## 6. `ifbetwn`（`tame_defs2.hl:788-789`）

HOL：`ifbetwn s x y = if MEM x s /\ MEM y s /\ ~(x=y) then rcons (betwn s x y) y else []`。
（HOL 多态；此处同样多态，`rcons l z = l ++ [z]`。） -/
def ifbetwn [DecidableEq α] (s : List α) (x y : α) : List α :=
  if x ∈ s ∧ y ∈ s ∧ x ≠ y then between s x y ++ [y] else []

/-! ## 7. `indexf`（`tame_defs2.hl:73-76`）

HOL：`indexf x y s = if (MEM x s /\ MEM y s)
  then (indexl y s + (sizel s - indexl x s)) MOD sizel s else sizel s`。
`indexl` ↦ `List.idxOf`（不在表中时返回 `length`，与 HOL `indexl` 约定一致）。
`MOD` ↦ `%`；`s = []` 时 `MEM` 为假，走 else 分支，故不触及 `% 0`。 -/
def indexf [DecidableEq α] (x y : α) (s : List α) : ℕ :=
  if x ∈ s ∧ y ∈ s then (s.idxOf y + (s.length - s.idxOf x)) % s.length else s.length

/-! ## 8. `core_split_normal_list`（`tame_defs2.hl:770-784`）与
`r_rtrans_eq`（`tame_defs2.hl:762-768`）

两件都是 `Prop` 形态的「规格定义」（HOL `new_definition'`），W1+ 以它们为前提使用。 -/

/-- HOL `core_split_normal_list`（`tame_defs2.hl:770-784`）：`split_normal_list` 的两片
`core` 与 `core L r` 的 `betwn` 段的拼接等式（右端结合序逐字对齐 HOL 的 `cat` 嵌套）。 -/
noncomputable def coreSplitNormalList (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : Prop :=
  let y := ly L r x
  let z := lz L N r x
  let z' := prevEl r z
  let fx := findFaceDarts L x
  let split := splitNormalList L r fx y z'
  let newVs := (between fx y z).map (fun d => d.1)
  core L split.1 = newVs.reverse ++ ([y.1] ++ (between (core L r) y.1 z'.1 ++ [z'.1])) ∧
    core L split.2 = ([z'.1] ++ (between (core L r) z'.1 y.1 ++ [y.1])) ++ newVs

/-- HOL `r_rtrans_eq`（`tame_defs2.hl:762-768`）：在 `find_face L x` 上按 `indexf`
从 `w = next_el (find_face L x) x` 起算的「不早于 `l'z`」的 dart，其是否属于 `r`
与是否属于 `rtrans L N r x 1` 一致。 -/
noncomputable def rRtransEq (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : Prop :=
  let w := nextEl (findFaceDarts L x) x
  ∀ x' ∈ findFaceDarts L x,
    indexf w (lz L N r x) (findFaceDarts L x) ≤ indexf w x' (findFaceDarts L x) →
      (x' ∈ r ↔ x' ∈ rtrans L N r x 1)

end Kepler.Text.Reduction5
