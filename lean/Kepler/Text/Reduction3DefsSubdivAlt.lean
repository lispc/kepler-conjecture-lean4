/-
  Kepler.Text.Reduction3DefsSubdivAlt — DEF-FIX 定义补批（章程
  `docs/def-fix-charters/subdivface-alt-defs/CHARTER.md`，commit 5037b1ca）。

  ┌─ 件目（纯定义 + nil 基例平凡事实）─────────────────────────────
  │   subdiv_face0_alt   tame_defs2.hl:368-381 → subdivFace0Alt
  │   subdiv_face0_alt2  tame_defs2.hl:389-397 → subdivFace0Alt2
  │   subdiv_faceFinal2  tame_defs2.hl:397-400 → subdivFaceFinal2
  │     （追加章程 `subdivface-final2-defs`；仅定义 + nil 方程）
  │ 动机：reduction3.hl:1454/:1560/:1572 三件直接引用它们，树内零命中；
  │ 本批只补定义，**不证** T5B 定理（章程 §3）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（章程 §3 折算口径）──────────────────────────────────
  │ ① `graph ↦ Graph`、`face ↦ Face`、`countVertices ↦ Graph.countVertices`、
  │    `nextVertex ↦ Face.nextVertex`；返回 `(face × graph)` ↦ `Face × Graph`。
  │ ② `upt a b ↦ List.range' a (b - a)`（截断减恒等；与 D2 `subdivFace0Beta`
  │    的 `List.range' g.countVertices n` 同折算法，`a = countVertices g`,
  │    `b = countVertices g + n`，`b - a` 截断后即 `n`）。
  │ ③ `the vo ↦ vo.getD 0`（`vo = NONE` 支已排除；同 D2 先例）。
  │ ④ `nextVertex f u = v /\ n = 0` ↦ `f.nextVertex u == v && n == 0`
  │    （Bool 条件，与 D2 `subdivFace0Beta` def 逐字同款式；beq_iff_eq 等价）。
  │ ⑤ `(f1,f2,g')` let 模式 ↦ 右结合三元组投影（`let (_, f2, g') := splitFace …`）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律（章程 §4）─────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；零既有陈述改动；
  │ 不 import `Kepler.Assembly` 伞/TameSpine；注释框行尾禁「减斜杠」。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Graphs.FaceDivision

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph makeFaceFinal splitFace)

/-- HOL `subdivFace0_alt`（tame_defs2.hl:368-381）：返回 `(f,g)` 余态的
递归分面（`subdivFace0Beta` 的 `(f,g)` 形孪生——两者返回值不同，不可互相
定义，见 D2 头注与章程 §2）。 -/
def subdivFace0Alt (g : Graph) (f : Face) (u : Nat) (n : Nat) :
    List (Option Nat) → Face × Graph
  | [] => (f, g)
  | vo :: vos =>
    if vo = none then subdivFace0Alt g f u (n + 1) vos
    else
      let v := vo.getD 0
      if f.nextVertex u == v && n == 0 then subdivFace0Alt g f v 0 vos
      else
        let ws := List.range' g.countVertices n
        let (_, f2, g') := splitFace g u v f ws
        subdivFace0Alt g' f2 v 0 vos

/-- HOL `subdivFace0_alt2`（tame_defs2.hl:389-397）：三元 `(u,v,n)` 流上的
`(f,g)` 余态递归分面（`subdivTripleStep` 的 `(f,g)` 形孪生）。 -/
def subdivFace0Alt2 (g : Graph) (f : Face) (n0 : Nat) :
    List (Nat × Nat × Nat) → Face × Graph
  | [] => (f, g)
  | uvn :: uvnos =>
    let (u, v, n) := uvn
    let ws := List.range' n0 n
    let (_, f2, g') := splitFace g u v f ws
    subdivFace0Alt2 g' f2 (n + n0) uvnos

/-- 定义即引理：`subdivFace0Alt` 的 nil 方程。 -/
theorem subdivFace0AltNil (g : Graph) (f : Face) (u n : Nat) :
    subdivFace0Alt g f u n [] = (f, g) := rfl

/-- 定义即引理：`subdivFace0Alt2` 的 nil 方程。 -/
theorem subdivFace0Alt2Nil (g : Graph) (f : Face) (n0 : Nat) :
    subdivFace0Alt2 g f n0 [] = (f, g) := rfl

/-- HOL `subdivFaceFinal2`（tame_defs2.hl:397-400）：`subdiv_face0_alt2` 后
`make_face_final` 的 `graph` 形孪生（DEF-FIX 章程
`docs/def-fix-charters/subdivface-final2-defs/CHARTER.md`）。 -/
def subdivFaceFinal2 (g : Graph) (f : Face) (uvns : List (Nat × Nat × Nat)) : Graph :=
  let p := subdivFace0Alt2 g f g.countVertices uvns
  makeFaceFinal p.1 p.2

/-- 定义即引理：`subdivFaceFinal2` 的 nil 方程（`subdivFace0Alt2 … [] = (f,g)`）。 -/
theorem subdivFaceFinal2Nil (g : Graph) (f : Face) :
    subdivFaceFinal2 g f [] = makeFaceFinal f g := rfl

end Kepler.Text.Reduction3

-- 探针（编译即执行）：签名比对 + 公理
#check @Kepler.Text.Reduction3.subdivFace0Alt
#check @Kepler.Text.Reduction3.subdivFace0Alt2
#print axioms Kepler.Text.Reduction3.subdivFace0AltNil
#print axioms Kepler.Text.Reduction3.subdivFace0Alt2Nil
#print axioms Kepler.Text.Reduction3.subdivFaceFinal2Nil
