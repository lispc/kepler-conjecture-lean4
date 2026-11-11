/-
  Kepler.Text.Reduction5J5UvnsCombined — UVNS 组合件（HOL reduction4.hl:3076–3131
  `final_assumption_uvns_combined`）。

  ┌─ 本件范围（PARTIAL：陈述锁定 + 胶水绿；两上游件 FREEZE 见 DELIVERY §4）──
  │ HOL 原文四行证体：
  │   `CONJ2_TAC; INTRO_TAC final_assumption_uvns […]; ASM_REWRITE_TAC[LET_THM];
  │    BY(ASM_MESON_TAC[]); INTRO_TAC final_assumption_uvns_vs' […]; …`
  │ 即 combined = `final_assumption_uvns_vs'`（有序支，:2500–2606）∧
  │ `final_assumption_uvns`（pairs 支，:2893–3074）的拼装。
  │ 两上游件（合计 HOL ≈290 行 + ≈15 件辅助塔）树内零命中（nb52 §6 已核），
  │ 本件先把**陈述逐字锁定**并以 `*OfSlots` 槽形交付胶水（仓库惯例，
  │ 同 `finalAssumptionNewvertexPreppedOfSlots`/`reductionK5`）；
  │ 两槽的修法表见 DELIVERY-nb53 §4。
  └────────────────────────────────────────────────────────────────

  ┌─ 陈述对表（HOL :3077–3117 逐字）──────────────────────────────
  │ 前提 10：good_list / good_list_nodes / is_restricted / marked_list /
  │   ¬final_list / transform_count = k（= `reductionK3Asm` 六前提，逐字同集）
  │   + `hnNil`（K3CONJ #17，:3111–3113）+ `hnFy`（#15，:3114–3120）
  │   + `hnZx`（#14，:3121）+ `hIdxSnd`（#16，:3123–3125）。
  │ 结论：`∀ v, (prev_el (core L r) v, v) = x ⇒ let uvns/vs/vs' … in
  │   (有序支) ∧ (pairs 支)`。
  │ 渲染约定（与 `reductionK1Concl`/`reductionK3Concl` #18 同款，D1 直接搬）：
  │   `MAP the (filter isSome vs)` ↦ `vs.filterMap id`；
  │   `the (EL i vs)` ↦ `(vs.getD i none).getD 0`；`sizel` ↦ `.length`；
  │   `PRE k` ↦ `k - 1`；`SND x` ↦ `x.2`；`FST` ↦ `.1`。
  │ 槽形说明：两槽（`hVs'`/`hUvns`）的结论按 let 消除后的裸形书写
  │ （`let` 在 Lean 项层 defeq，`refine` 直接对上）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；不删改既有 def；主仓 tracked 零改动。
-/

import Kepler.Text.Reduction5J5K3
import Kepler.Text.Reduction3Defs

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)

/-- **HOL `final_assumption_uvns_combined` 的槽形**（reduction4.hl:3076–3131）：
前提 = `reductionK3Asm` 六前提 + K3CONJ 的 NEW/SND_X a/b/c 四合取；
两槽 = `final_assumption_uvns_vs'`（有序支）与 `final_assumption_uvns`
（pairs 支）的逐字结论（其前提由本件前提供给，落库后 D1 一行消槽）。 -/
theorem finalAssumptionUvnsCombinedOfSlots (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k)
    (hnNil : ∀ i : ℕ, i < k →
      between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
        ((ytrans L N r x i).1, (ztrans L N r x i).1) ∉
          listOfDarts (quotientList L N))
    (hnFy : ∀ i : ℕ, i < k →
      1 < (ftrans L N r x i ::
        ifbetwn (core L r) (ftrans L N r x i) (ytrans L N r x i).1).length →
        x.2 ∉ ifbetwn (core L r) (ftrans L N r x i) (ytrans L N r x i).1)
    (hnZx : x.2 ∉ ifbetwn (core L r) (ztrans L N r x (k - 1)).1 x.1)
    (hIdxSnd : ∀ i : ℕ, i < k →
      indexf x.2 (ytrans L N r x i).1 (core L r) <
        indexf x.2 (ztrans L N r x i).1 (core L r))
    (hVs' : ∀ v : ℕ, (prevEl (core L r) v, v) = x →
      let vs := Kepler.Text.Reduction3.destTripleFull (core L r) v
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)
      ∀ i : ℕ, i + 1 < (vs.filterMap id).length →
        indexf v ((vs.filterMap id).getD i 0) (core L r) <
          indexf v ((vs.filterMap id).getD (i + 1) 0) (core L r))
    (hUvns : ∀ v : ℕ, (prevEl (core L r) v, v) = x →
      let vs := Kepler.Text.Reduction3.destTripleFull (core L r) v
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)
      ∀ i : ℕ,
        (vs.getD i none).isSome → (vs.getD (i + 1) none).isSome →
        i + 1 < vs.length →
        ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0)
            ∈ listOfDarts (quotientList L N) →
        ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0)
            ∈ listPairs (core L r)) :
    ∀ v : ℕ, (prevEl (core L r) v, v) = x →
      (let uvns := Kepler.Text.Reduction3.coreTripleV4 L N r x
       let vs := Kepler.Text.Reduction3.destTripleFull (core L r) v uvns
       let vs' := vs.filterMap id
       (∀ i : ℕ, i + 1 < vs'.length →
          indexf v (vs'.getD i 0) (core L r) < indexf v (vs'.getD (i + 1) 0) (core L r)) ∧
        (∀ i : ℕ,
          let d : Dart := ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0);
          ((vs.getD i none).isSome ∧ (vs.getD (i + 1) none).isSome ∧
            i + 1 < vs.length ∧ d ∈ listOfDarts (quotientList L N)) →
          d ∈ listPairs (core L r))) := by
  intro v hv
  exact ⟨fun i hi => hVs' v hv i hi,
    fun i h4 => hUvns v hv i h4.1 h4.2.1 h4.2.2.1 h4.2.2.2⟩

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.Reduction5.finalAssumptionUvnsCombinedOfSlots
