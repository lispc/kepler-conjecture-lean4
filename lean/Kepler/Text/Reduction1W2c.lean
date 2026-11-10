/-
  Kepler.Text.Reduction1W2c — J4 Wave W2 批 1c（编排者按车道冻结包
  `DELIVERY_W2C.md` §7 一步到位修法收口）：`subdivFace0_final`
  （HOL reduction1.hl:1704）。

  载体：Lean `Kepler.Graphs.subdivFace'` = HOL `subdivFace0`；
  `Kepler.Text.Reduction3.subdivFace0Alt` = HOL `subdivFace0_alt`。
  陈述：`(fun p : Face × Graph => makeFaceFinal p.1 p.2) (subdivFace0Alt g f u n vos)
        = subdivFace' g f u n vos`。

  技法（冻结包 §7）：展开两 def 后**不要整体 `simp only [def]`**（会把 if 一起消掉）；
  只定点消 `Option.some_ne_none`/`getD_some`，再 `by_cases` 同一 Bool 测试、
  `if_pos/if_neg` 同一 `h` 连打两次。
  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Graphs.FaceDivision
import Kepler.Text.Reduction3DefsSubdivAlt

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Graphs (Graph Face makeFaceFinal splitFace subdivFace')

/-- **HOL `subdivFace0_final`**（reduction1.hl:1704）：`makeFaceFinal` 与
`subdivFace0_alt` 的复合 = Graph 终点形递归 `subdivFace'`。 -/
theorem subdivFace0Final (g : Graph) (f : Face) (u n : Nat) :
    ∀ vos : List (Option Nat),
      (fun p : Face × Graph => makeFaceFinal p.1 p.2)
        (Kepler.Text.Reduction3.subdivFace0Alt g f u n vos)
        = subdivFace' g f u n vos := by
  intro vos
  induction vos generalizing g f u n with
  | nil => rfl
  | cons vo vos ih =>
    cases vo with
    | none =>
      show (fun p : Face × Graph => makeFaceFinal p.1 p.2)
          (Kepler.Text.Reduction3.subdivFace0Alt g f u n (none :: vos))
          = subdivFace' g f u n (none :: vos)
      rw [Kepler.Text.Reduction3.subdivFace0Alt, subdivFace']
      rw [if_pos rfl]
      exact ih g f u (n + 1)
    | some v =>
      show (fun p : Face × Graph => makeFaceFinal p.1 p.2)
          (Kepler.Text.Reduction3.subdivFace0Alt g f u n (some v :: vos))
          = subdivFace' g f u n (some v :: vos)
      rw [Kepler.Text.Reduction3.subdivFace0Alt, subdivFace']
      simp only [Option.some_ne_none, if_false, Option.getD_some]
      by_cases h : ((f.nextVertex u == v) && (n == 0)) = true
      · rw [if_pos h, if_pos h]
        exact ih g f v 0
      · rw [if_neg h, if_neg h]
        exact ih _ _ v 0

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.subdivFace0Final
