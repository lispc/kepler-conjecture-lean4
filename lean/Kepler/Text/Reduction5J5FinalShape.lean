/-
  Kepler.Text.Reduction5J5FinalShape — 会师终装验证件：Assembly 删桩后的最终形状。

  ┌─ 目的（不碰 `Assembly.lean`）───────────────────────────────────
  │ ① `jcajyduFinalShape`：与 Assembly `jcajydu` stub 的 **Reduction5 侧逐字形**
  │    （`TameLp.IsHypermapOfListTl` + `H.Iso`）定理，参数化在
  │    `hU : k3UvnsMainSlot` 上，证体 = 一行
  │    `jcajyduOfK4Slots k3Sx3SlotInstance (k3UvnsOfSlots hU)`；
  │ ② `assemblyShapeBridge`：同一参数下的 **Assembly 形骨架检查**——把
  │    `IsHypermapOfListTl` 用四字段匿名构造器折成 `IsHypermapOfList` 镜像形，
  │    `H.Iso` 与 `HypermapIso` 镜像形按同体 def 直接消费。删桩时机械照抄。
  └────────────────────────────────────────────────────────────────

  ┌─ Assembly 侧原形（`Assembly.lean:192/210/2509`，本文件不 import）────
  │ `def HypermapIso {α β} [DecidableEq α] [DecidableEq β]
  │     (H : Hypermap α) (H' : Hypermap β) : Prop :=
  │   ∃ f : α → β, Set.BijOn f (↑H.darts) (↑H'.darts) ∧
  │     ∀ x ∈ H.darts, H'.edgeMap (f x) = f (H.edgeMap x) ∧
  │       H'.nodeMap (f x) = f (H.nodeMap x) ∧ H'.faceMap (f x) = f (H.faceMap x)`
  │ `structure IsHypermapOfList (L : fgraph ℕ) (H : Hypermap (ℕ × ℕ)) : Prop where
  │   darts_eq / edgeMap_eq / nodeMap_eq / faceMap_eq`（四字段同体）
  │ `theorem jcajydu … : ∃ g, PlaneGraphs g ∧ GoodGraphV4 g ∧
  │   ∃ H', IsHypermapOfList g.fgraph H' ∧ HypermapIso H H'`
  └────────────────────────────────────────────────────────────────

  镜像约定（同 `DELIVERY-nb43 §4` / `ProbeAssemblyBridge` 实证）：
  - `Assembly.HypermapIso` 与 `Hypermap.Iso` **两 def 体逐字同体 ⇒ defeq**；
    本文件镜像 `AssemblyHypermapIso` 亦逐字同体，故 `hiso` 直接落槽（`exact`）。
  - `Assembly.IsHypermapOfList` ↔ `TameLp.IsHypermapOfListTl` **四字段匿名构造器
    一步**（字段名/类型逐槽同体）；本文件镜像 `AssemblyIsHypermapOfList` 同体。
  - `Assembly.GoodGraphV4` ↔ `TameCorrList.GoodGraphV4` **defeq**（六合取同体，
    nb43 §1.3 + ProbeAssemblyBridge 实证）；本文件镜像结论直接用后者。
  - 本文件**不 import `Kepler.Assembly`**（import 闭包 = Reduction5J5UvnsSlot +
    Reduction5J5K4 + Reduction5J5HfSupply + Graphs/TameLp/TameCorrList，全部
    Assembly-free 侧），无环、无桩，删桩时无需回改本件。

  纪律：零公理、零占位证明、零反射式判定；不改既有陈述/定义；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction5J5UvnsSlot
import Kepler.Text.Reduction5J5K4
import Kepler.Text.Reduction5J5HfSupply

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList listOfDarts eList nList fList)

/-- **会师终装形**（= Assembly `jcajydu` stub 的 Reduction5 侧逐字形）：
`k3Sx3SlotInstance` + `k3UvnsOfSlots hU` 代入 K4 槽装配，一行。 -/
theorem jcajyduFinalShape (hU : Kepler.Text.Reduction5.k3UvnsMainSlot)
    {α : Type*} [DecidableEq α] (H : Kepler.Text.Hypermap α) (hres : H.IsRestricted) :
    ∃ g : Kepler.Graphs.Graph, Kepler.Graphs.PlaneGraphs g ∧
      Kepler.Text.TameCorrList.GoodGraphV4 g ∧
      ∃ H' : Kepler.Text.Hypermap (ℕ × ℕ),
        Kepler.Text.TameLp.IsHypermapOfListTl g.fgraph H' ∧ H.Iso H' :=
  jcajyduOfK4Slots k3Sx3SlotInstance (k3UvnsOfSlots hU) H hres

/-! ## Assembly 形镜像（同体 def / structure；本文件不 import `Kepler.Assembly`） -/

/-- **Assembly `HypermapIso` 的镜像**（`Assembly.lean:192`，同体）。 -/
def AssemblyHypermapIso {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H : Kepler.Text.Hypermap α) (H' : Kepler.Text.Hypermap β) : Prop :=
  ∃ f : α → β, Set.BijOn f (↑H.darts) (↑H'.darts) ∧
    ∀ x ∈ H.darts,
      H'.edgeMap (f x) = f (H.edgeMap x) ∧
      H'.nodeMap (f x) = f (H.nodeMap x) ∧
      H'.faceMap (f x) = f (H.faceMap x)

/-- **Assembly `IsHypermapOfList` 的镜像**（`Assembly.lean:210`，四字段同体）。 -/
structure AssemblyIsHypermapOfList (L : fgraph ℕ)
    (H : Kepler.Text.Hypermap (ℕ × ℕ)) : Prop where
  /-- `dart (hypermap_of_list L) = darts_of_list L`。 -/
  darts_eq : (↑H.darts : Set (ℕ × ℕ)) = {d | d ∈ listOfDarts L}
  /-- `edge_map` 在 dart 上 = `e_list`。 -/
  edgeMap_eq : ∀ d ∈ H.darts, H.edgeMap d = eList d
  /-- `node_map` 在 dart 上 = `n_list`。 -/
  nodeMap_eq : ∀ d ∈ H.darts, H.nodeMap d = nList L d
  /-- `face_map` 在 dart 上 = `f_list`。 -/
  faceMap_eq : ∀ d ∈ H.darts, H.faceMap d = fList L d

/-- **Assembly 形骨架桥**（删桩机械照抄样板）：
`IsHypermapOfListTl` 四字段匿名构造器一步 → `IsHypermapOfList` 镜像；
`H.Iso` 与 `HypermapIso` 镜像同体 ⇒ `hiso` 直落（defeq，无需转换项）。 -/
theorem assemblyShapeBridge (hU : Kepler.Text.Reduction5.k3UvnsMainSlot)
    {α : Type*} [DecidableEq α] (H : Kepler.Text.Hypermap α) (hres : H.IsRestricted) :
    ∃ g : Kepler.Graphs.Graph, Kepler.Graphs.PlaneGraphs g ∧
      Kepler.Text.TameCorrList.GoodGraphV4 g ∧
      ∃ H' : Kepler.Text.Hypermap (ℕ × ℕ),
        AssemblyIsHypermapOfList g.fgraph H' ∧ AssemblyHypermapIso H H' := by
  obtain ⟨g, hpg, hgg, H', hH', hiso⟩ := jcajyduFinalShape hU H hres
  exact ⟨g, hpg, hgg, H',
    ⟨hH'.darts_eq, hH'.edgeMap_eq, hH'.nodeMap_eq, hH'.faceMap_eq⟩, hiso⟩

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.jcajyduFinalShape
#print axioms Kepler.Text.Reduction5.AssemblyHypermapIso
#print axioms Kepler.Text.Reduction5.AssemblyIsHypermapOfList
#print axioms Kepler.Text.Reduction5.assemblyShapeBridge

/- 接口探针：`jcajyduFinalShape` 可直接替换 Assembly `jcajydu` 桩体（hU 由 U 段供）。 -/
#check fun (hU : Kepler.Text.Reduction5.k3UvnsMainSlot) =>
  Kepler.Text.Reduction5.jcajyduFinalShape hU
#check fun (hU : Kepler.Text.Reduction5.k3UvnsMainSlot) =>
  Kepler.Text.Reduction5.assemblyShapeBridge hU
