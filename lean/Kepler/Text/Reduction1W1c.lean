/-
  Kepler.Text.Reduction1W1c — J4 Wave W1 批 3（**§7 触发批**）：
  RD-2′ 的 (a)(b) 机械面底座中**可机检的部分**。
  纪律：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
  详见 DELIVERY_W1C.md。
-/
import Kepler.Graphs.EnumeratorProps

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

/-- `!` 形与依赖式 `getElem` 在界内同值（约定 C3 三步链）。 -/
private theorem getElem!_eq_getElem {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l[i]! = l[i] := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- 单调链：`a ≤ b` 且逐点单步单调 ⇒ `xs[a]! ≤ xs[b]!`（批 2 私件同体重落）。 -/
private theorem monoChain {xs : List ℕ}
    (hmono : ∀ i, i + 1 < xs.length → xs[i]! ≤ xs[i + 1]!) :
    ∀ (n a : ℕ), a + n < xs.length → xs[a]! ≤ xs[a + n]! := by
  intro n
  induction n with
  | zero => intro a _; simp
  | succ n ih =>
    intro a hx
    have h1 : a + n < xs.length := by omega
    have h2 : a + n + 1 < xs.length := by omega
    have hstep := hmono (a + n) h2
    rw [show a + (n + 1) = a + n + 1 from by omega]
    exact le_trans (ih a h1) hstep

/-- `(xs.drop d).take k` 的第 `q` 个元素 = `xs[d+q]`（`?` 形，非依赖）。 -/
private theorem elemDropTake {xs : List ℕ} {d k q : ℕ} (hq : q < k) :
    ((xs.drop d).take k)[q]? = xs[d + q]? := by
  rw [List.getElem?_take, if_pos hq, List.getElem?_drop]

end Kepler.Text.Reduction1
