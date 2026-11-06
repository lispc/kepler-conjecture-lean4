/-
  Kepler/Assembly/GoodListChain — 逐片链的**符号化**组合子（P6-C，goodList 重切）。

  背景：`GoodListAll` 早期把 `k` 个分片用 `all_of_take_drop` 右嵌套串起来，
  每一层都要证

      `(D.drop (100*i)).drop 100 =?= D.drop (100*(i+1))`

  的**大具体列表 defeq**（k=17 时 12 s / 2.4 GB 尚可；Pent 的 k=161 时实测
  92.58 s 冲到 8.03 GB 被 RSS 看门狗杀 —— `logs/GoodListAll.err`）。
  `all_drop_of_split` 把同一件事变成**符号**推理：只重写 `drop` 的组合律，
  唯一的算术是字面量 `n + m` 的计算，因此 161 层链从不展开 `PentData`。
-/
import Kepler.Assembly.GoodListDefs

namespace Kepler.Assembly

/-- 逐片链（符号版）：`l` 从 `m` 起的第一片 `n` 个元素全真，且 `l` 从
`n + m` 起的尾巴全真，则 `l` 从 `m` 起的整段全真。

纯内核：只用 `List.take_append_drop` / `List.drop_drop` / `List.all_append`。 -/
theorem all_drop_of_split {α : Type} {l : List α} {f : α → Bool} {m n : ℕ}
    (h1 : ((l.drop m).take n).all f = true)
    (h2 : (l.drop (m + n)).all f = true) :
    (l.drop m).all f = true := by
  rw [← List.take_append_drop n (l.drop m), List.drop_drop, List.all_append, h1, h2]
  rfl

#print axioms all_drop_of_split

end Kepler.Assembly
