/-
  Kepler.Text.Reduction3Thm14b — J5-8 W2-1：`nfgtrans_mem`（reduction3.hl:4771-4813）。

  ┌─ 归属对账（HOL Light Flyspeck text_formalization/tame/reduction3.hl）──
  │ :4771 `nfgtrans_mem` → `nfgtransMem`（T14 main_induction 直接上游）：
  │   `MEM f (faces g) ⇒ MEM f' (faces g')`（`(n',f',g') = nfgtrans' … i`，
  │   `i ≤ transform_count`）。
  └────────────────────────────────────────────────────────────────

  **路线（对 i 归纳，零本体重写）**：
  · 0 支：`nfgtrans'Zero`（D2）⇒ 恒等；
  · succ 支：`nfgtransSuc`（本车道 W1，`Reduction3Thm14a`）展开一步 +
    `subdivTripleStepPaired`（T5B）⇒ `(n+p.1, f2, g')`，其中
    `(_, f2, g') = splitFace g' u v f' ws`；新面成员性 = `MEM_splitFace2`
    （HOL tame_list.hl:4750）**私有同证重落**（Thm7F 同体）。
  · HOL 的 `faces g` ↦ Lean `g.faces`；`sizel` ↦ `List.length`；
    Lean 惯例 +1 前提 `haq : AqiunppSlot L hL`（`nfgtransSuc` 需要）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm14a
import Kepler.Text.Reduction3Thm5B

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph between fgraph replace replace3 splitFace split_face)
open Kepler.Assembly (GoodList findFaceDarts)
open Kepler.Text.Reduction5
  (Dart ntrans rtrans ytrans ztrans transformCount finalList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- HOL `MEM_splitFace2`（tame_list.hl:4750；Thm7F 私有件同证重落）：
`f ∈ g.faces ⇒ f2 ∈ (SND (SND (splitFace g u v f ws))).faces`。 -/
private theorem t14b_splitFaceAddF21 (g : Graph) (u v : Nat) (f : Face) (ws : List Nat)
    (hf : f ∈ g.faces) :
    (splitFace g u v f ws).2.1 ∈ (splitFace g u v f ws).2.2.faces := by
  show (split_face f u v ws).2 ∈
    replace f [(split_face f u v ws).2] g.faces ++ [(split_face f u v ws).1]
  exact List.mem_append_left _ (replace3 hf List.mem_cons_self)

/-- **J5-8 W2-1：HOL `nfgtrans_mem`**（reduction3.hl:4771-4813）：
`(nfgtrans' (n,f,g) L N r x i).2.1 ∈ (nfgtrans' (n,f,g) L N r x i).2.2.faces`
（前提含 `f ∈ g.faces` 与 `i ≤ transform_count`）。 -/
theorem nfgtransMem (i : ℕ) (n : ℕ) (f : Face) (g : Graph) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hi : i ≤ transformCount L N r x)
    (hfg : f ∈ g.faces) :
    (nfgtrans' (n, f, g) L N r x i).2.1
      ∈ (nfgtrans' (n, f, g) L N r x i).2.2.faces := by
  induction i generalizing n f g with
  | zero =>
    rw [Kepler.Text.Reduction3.nfgtrans'Zero]
    exact hfg
  | succ i ih =>
    have hsucc := nfgtransSuc i n f g L N r x hL hgn haq hm hnf hir hi
    rw [hsucc]
    set p' := nfgtrans' (n, f, g) L N r x i with hp'
    have hIH : p'.2.1 ∈ p'.2.2.faces := by
      rw [hp']
      exact ih n f g (by omega) hfg
    rw [Kepler.Text.Reduction3.subdivTripleStepPaired]
    dsimp only
    exact t14b_splitFaceAddF21 p'.2.2 (ytrans L N r x i).1 (ztrans L N r x i).1
      p'.2.1 (List.range' p'.1
        (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length) hIH

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.nfgtransMem
