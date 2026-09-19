/-
  Kepler/Assembly/GoodListDefs — `good_list` 纯定义层 + Bool 反射（P6-C）。

  从 `Kepler/Assembly.lean` §1a/§1c 下沉的**纯列表机器**（无几何依赖），
  使 archive 逐图 `native_decide` 分片（`Kepler/Assembly/GoodListShard*.lean`）
  不必 import 装配脊柱（避免把接口 sorry 拉进分片公理审计）。
  `Kepler.Assembly` 经 import 本模块对外签名不变。

  镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353）：
  - `formal_lp/hypermap/ssreflect/list_hypermap-compiled.hl`（`list_pairs` /
    `list_of_darts` / `find_face` / `e_list` / `f_list` / `n_list` / `good_list`）；
  - `tame/ssreflect/seq2-compiled.hl`（`next_el` / `prev_el`）；
  - `text_formalization/general/the_kepler_conjecture.hl:40`
    （`tame_archive_lists`）。
-/
import Kepler.Graphs
import Kepler.Graphs.ArchiveData.Tri
import Kepler.Graphs.ArchiveData.Quad
import Kepler.Graphs.ArchiveData.Pent
import Kepler.Graphs.ArchiveData.Hex

open Kepler.Graphs

namespace Kepler.Assembly

/-! ### list_hypermap 机器（`formal_lp/hypermap/ssreflect/list_hypermap-compiled.hl`） -/

/-- HOL `list_pairs`（list_hypermap-compiled.hl:19）：`list_pairs list = zip list (rot 1 list)`，
其中 ssreflect `rot n s = drop n s ++ take n s`（已内联 `n = 1`）。 -/
def listPairs (l : List α) : List (α × α) := l.zip (l.drop 1 ++ l.take 1)

/-- HOL `list_of_darts`（list_hypermap-compiled.hl:20-21）：
`foldr (λlist a. (list_pairs list) ++ a) [] L`，即 `flatten (map list_pairs L)`。 -/
def listOfDarts (L : fgraph ℕ) : List (ℕ × ℕ) := (L.map listPairs).flatten

/-- HOL `next_el`（`tame/ssreflect/seq2-compiled.hl:24-25`）逐句镜像：
`next_el s x = if (indexl x s = sizel s - 1) then (headl x s) else (nth x s (indexl x s + 1))`。
折算：`indexl` ↦ `List.idxOf`（`x ∉ s` 时 `idxOf = length`，与 HOL `indexl` 约定一致）、
`headl x s` ↦ `s.headD x`、`nth x s i` ↦ `s.getD i x`（默认元均为 `x`）。 -/
def nextEl [BEq α] (s : List α) (x : α) : α :=
  if s.idxOf x = s.length - 1 then s.headD x else s.getD (s.idxOf x + 1) x

/-- HOL `prev_el`（seq2-compiled.hl:26-27）逐句镜像：
`prev_el s x = if ~(MEM x s) then x
  else if (indexl x s = 0) then (last x s) else (nth x s (indexl x s - 1))`。 -/
def prevEl [DecidableEq α] (s : List α) (x : α) : α :=
  if x ∉ s then x else if s.idxOf x = 0 then s.getLastD x else s.getD (s.idxOf x - 1) x

/-- HOL `find_face`（list_hypermap-compiled.hl:47-48 经 `find_list`/`list_of_faces`）：
`L` 中第一个以 `d` 为 dart 的面（`list_pairs l` 含 `d`）的 **dart 列表**；无则 `[]`。 -/
def findFaceDarts (L : fgraph ℕ) (d : ℕ × ℕ) : List (ℕ × ℕ) :=
  listPairs ((L.find? fun l => decide (d ∈ listPairs l)).getD [])

/-- HOL `e_list`（list_hypermap-compiled.hl:54）：`e_list d = (SND d, FST d)`。 -/
def eList (d : ℕ × ℕ) : ℕ × ℕ := (d.2, d.1)

/-- HOL `f_list`（list_hypermap-compiled.hl:53）：`f_list L d = next_el (find_face L d) d`。 -/
def fList (L : fgraph ℕ) (d : ℕ × ℕ) : ℕ × ℕ := nextEl (findFaceDarts L d) d

/-- HOL `n_list`（list_hypermap-compiled.hl:55）：
`n_list L d = e_list (prev_el (find_face L d) d)`。 -/
def nList (L : fgraph ℕ) (d : ℕ × ℕ) : ℕ × ℕ := eList (prevEl (findFaceDarts L d) d)

/-- HOL `good_list`（list_hypermap-compiled.hl:62-65）逐句镜像：
`good_list L <=> uniq (list_of_darts L) /\ all (λl. ~(l = [])) L /\
  (!d. MEM d (list_of_darts L) ==> MEM (SND d, FST d) (list_of_darts L))`。
（`uniq` ↦ `List.Nodup`。） -/
def GoodList (L : fgraph ℕ) : Prop :=
  (listOfDarts L).Nodup ∧ (∀ l ∈ L, l ≠ []) ∧
    ∀ d ∈ listOfDarts L, (d.2, d.1) ∈ listOfDarts L

/-- HOL `ALL good_list a`（the_main_statement.hl:49 合取项，`Seq2.ALL_all` 展开）。 -/
def AllGoodList (a : List (fgraph ℕ)) : Prop := ∀ L ∈ a, GoodList L

/-- HOL `tame_archive_lists`（`archive = set_of_list tame_archive_lists`，
the_kepler_conjecture.hl:40）的 Lean 侧数据形态：Phase 2 archive 的底层清单
（`Archive` 的数据部分，RelativeCompleteness.lean:110）。 -/
def tameArchiveLists : List (fgraph ℕ) := TriData ++ QuadData ++ PentData ++ HexData

/-! ### Bool 反射层（P6-C 量产机器） -/

/-- `GoodList` 的 Bool 检查器（`GoodList` 是 `def`，TC 合成不展开它，
故不能直接在 `List.all` 里 `decide (GoodList L)`；三合取项各自的
`Decidable` 实例齐备，这里显式逐项 `decide` 后取 `&&`）。 -/
def goodListB (L : fgraph ℕ) : Bool :=
  decide ((listOfDarts L).Nodup) &&
  decide (∀ l ∈ L, l ≠ []) &&
  decide (∀ d ∈ listOfDarts L, (d.2, d.1) ∈ listOfDarts L)

/-- 反射：`goodListB L = true → GoodList L`（纯内核证明）。 -/
theorem good_of_goodListB {L : fgraph ℕ} (h : goodListB L = true) : GoodList L := by
  unfold goodListB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2, of_decide_eq_true h.2⟩

/-- 整表反射：`(l.all goodListB) = true → ∀ L ∈ l, GoodList L`（纯内核证明）。 -/
theorem good_of_all {l : List (fgraph ℕ)} (h : l.all goodListB = true) :
    ∀ L ∈ l, GoodList L :=
  fun L hL => good_of_goodListB ((List.all_eq_true.mp h) L hL)

/-- 分片组合器：`take`/`drop` 两片各自 `all goodListB`，则整表 `all goodListB`
（纯内核证明；`GoodListAll` 模块用它把分片定理串成逐类总定理）。 -/
theorem all_of_take_drop {l : List (fgraph ℕ)} {n : ℕ}
    (h1 : (l.take n).all goodListB = true) (h2 : (l.drop n).all goodListB = true) :
    l.all goodListB = true := by
  rw [← List.take_append_drop n l, List.all_append, h1, h2]
  rfl

end Kepler.Assembly
