/-
  Kepler.Text.ChainSimpleHypermap — J 战役 J1（任务 3 定义层）：
  `SimpleHypermapTl`（章程 `chain-params-defs` §4 的链层镜像）。

  ┌─ 章程与范围 ────────────────────────────────────────────────
  │ 只落定义：`SimpleHypermapTl H := H.Simple`（`Hypermap.Simple`，
  │ Hypermap.lean:1058 与 `Assembly.lean:2075 SimpleHypermap` 逐字同构：
  │ `nodeOrbit/faceOrbit = orbitSet = Set.range`，`H.node/H.face =
  │ orbitMap = {y | ∃n, ...}` —— 两者 defeq，零桥）。
  │ **禁区（章程 §4）**：不 import `Kepler.Assembly` 伞模块。
  └──────────────────────────────────────────────────────────────

  ┌─ `simple_hypermap_uniq`（tame_list.hl:9254）为何不在此片 ─────────
  │ 该 iff 的 Spine 证体（TameList14:297/244/325）依赖五件链层缺失的机器：
  │ `memHypermapOfListNode`（node 轨道 = 同 FST 类，经 GoodListNodesTl）、
  │ `faceTableSubsetFaceOrbit` / `faceOrbitSubsetFindFace`（face 轨道 ⊆
  │ find_face 表）、`listPairsUnique` / `listPairsNotUniq` /
  │ `listPairsGetElemRot`（list_pairs 逐项 + 唯一性族）——全树 rg 零命中。
  │ 实测规模 ≈150-200 行（非原估 30-50 行），待独立片。
  └──────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5Base

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.ChainSimpleHypermap

/-- **HOL `simple_hypermap`**（`hypermap.hl:186`；`Assembly.lean:2075`
`SimpleHypermap` 的链层镜像——两者定义体逐字同构，defeq 零桥）。
`Simple H ⟺ ∀ x ∈ H.darts, H.node x ∩ H.face x = {x}`。 -/
def SimpleHypermapTl {α : Type*} [DecidableEq α]
    (H : Kepler.Text.Hypermap α) : Prop :=
  H.Simple

end Kepler.Text.ChainSimpleHypermap

/-! 探针（编译即执行）：签名 + 公理。 -/
#check @Kepler.Text.ChainSimpleHypermap.SimpleHypermapTl
#print axioms Kepler.Text.ChainSimpleHypermap.SimpleHypermapTl
