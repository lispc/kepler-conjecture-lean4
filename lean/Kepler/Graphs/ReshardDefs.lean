/-
  Kepler/Graphs/ReshardDefs — `*_top_*` / `*_archive_pre` 内核重切的通用组合子。

  纯内核引理：`List.all` 在 `take`/`drop` 两片上都真，则整表真。
  （`Kepler.Assembly.all_of_take_drop` 的谓词泛化版；后者写死了 `goodListB`
  且作用在 `List (fgraph ℕ)` 上。）
-/
import Kepler.Graphs.Graph

namespace Kepler.Graphs

/-- 分片组合器（任意 Bool 谓词）：`take`/`drop` 两片各自 `all f`，则整表 `all f`。 -/
theorem all_of_take_drop_b {α : Type} {l : List α} {n : Nat} {f : α → Bool}
    (h1 : (l.take n).all f = true) (h2 : (l.drop n).all f = true) :
    l.all f = true := by
  rw [← List.take_append_drop n l, List.all_append, h1, h2]
  rfl

/-- 逐片链（符号版）：`l` 从 `m` 起的第一片 `n` 个元素全真，且 `l` 从 `m + n`
起的尾巴全真，则 `l` 从 `m` 起的整段全真。

与 `Kepler.Assembly.all_drop_of_split` 同构（谓词泛化）。**必须**用符号链：朴素的
`all_of_take_drop_b` 右嵌套在 k=161 时要证 `(D.drop (100*i)).drop 100 =?=
D.drop (100*(i+1))` 的大具体列表 defeq，实测 92.58 s 冲 8.03 GB 被杀。 -/
theorem all_drop_of_split_b {α : Type} {l : List α} {f : α → Bool} {m n : Nat}
    (h1 : ((l.drop m).take n).all f = true)
    (h2 : (l.drop (m + n)).all f = true) :
    (l.drop m).all f = true := by
  rw [← List.take_append_drop n (l.drop m), List.drop_drop, List.all_append, h1, h2]
  rfl

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
