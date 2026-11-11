/-
  Kepler.Text.Reduction5J5K4Lemma — D1 前置：K3 引理构造件
  `reductionK3ConclOfSlots`（HOL reduction4.hl:5404–5431 的「造 K3CONJ」段）。

  ┌─ 18 合取 × 供料矩阵（HOL reduction4.hl:5409–5430 逐行）──────────
  │ 1  INDEX 1  indexf2_final_lemmas       ← indexf2FinalLemmas（8a17dd66）
  │ 2  INDEX 2  indexf3_final_lemmas       ← indexf3FinalLemmas
  │ 3  INDEX 3  indexf4_final_lemmas       ← indexf4FinalLemmas
  │ 4  INDEX 4  indexf5_final_lemmas       ← indexf5FinalLemmas
  │ 5  INDEX 5  indexf6_final_lemmas       ← indexf6FinalLemmas
  │ 6  INDEX 6  indexf7_final_lemmas       ← indexf7FinalLemmas
  │ 7  INDEX 7  indexf8_final_lemmas       ← **槽 hF8**（J4 B3' 在飞）
  │ 8  MISC     final_reduction_mem_z0_ri ← finalReductionMemZ0Ri
  │ 9  BETWN 1  betwn_corek_z_x           ← betwnCorekZX
  │ 10 BETWN 2  n1_diff_n0                ← n1DiffN0（99294311）
  │ 11 BETWN 3  corei_reduction           ← coreiReduction（h0 ← betwnCoreReductionLemma
  │                                          + finalAssumptionsNotNextCore0I）
  │ 12 BETWN 4  not_next_core0_z_y         ← finalAssumptionsNotNextCore0ZY
  │ 13 BETWN 5  betwn_core0_z_y            ← betwnCore0ZY
  │ 14 NEW      snd_x_zx                  ← finalAssumptionNotMemSndXZx
  │ 15 SND_X a  snd_x_fy                  ← finalAssumptionNotMemSndXFy
  │ 16 SND_X b  index_snd_x               ← indexSndX（9006597b）
  │ 17 SND_X c  not_mem_yi_zi_list_of_darts ← **槽 hSx3**（缺件，见 §缺件）
  │ 18 UVNS     final_assumption_uvns_combined ← **槽 hUvns**（tame-corr U 段在飞）
  └────────────────────────────────────────────────────────────────

  **判词（派单第 2 条末句）**：HOL 的 K4 引理（hK4lemma）在本构造下**零消费**——
  其五合取（betwn_corek_z_x / betwn_core0_z_y / not_next z_y / not_next y_z@core r /
  pair ∉ list_pairs(core r)）在 Lean 侧都有各自的**直接供料件**（上表 9/12/13 与
  betwnCoreReductionLemma），无需绕经 K4 引理；故本件**不取 hK4 参数**（判词记档）。

  **缺件（派单未列）**：SND_X c 的 HOL 供料链
  `mem_list_of_darts_quotient_core`（reduction4.hl:3412）→
  `non_r_darts_trans`（:3433）→ `non_r_darts_trans_i`（:3530）→
  `list_of_darts_mem`（:3563）→ `list_of_darts_reduction` 第三合取（:3694–3708）
  在树内全部零命中（按名 + 按语句双搜）；本件以显式槽 `hSx3` 承载，不造新数学。

  纪律：零公理、零占位证明、零反射式判定；不改既有陈述/定义；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction5J5K3
import Kepler.Text.Reduction5J5K3Indexf2
import Kepler.Text.Reduction5J7W1d
import Kepler.Text.Reduction5J5K3Indexf45
import Kepler.Text.Reduction5J5K3Indexf678
import Kepler.Text.Reduction5J5K2A2Final
import Kepler.Text.TameSpine.Reduction3J5BetwnCorekZX
import Kepler.Text.Reduction5J7W4
import Kepler.Text.Reduction5J5NotNextCore
import Kepler.Text.Reduction5J5NotNextCore0I
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5
import Kepler.Text.Reduction4K4C1
import Kepler.Text.Reduction4K4C0R2d
import Kepler.Text.Reduction5J5K4IndexSndX
import Kepler.Text.Reduction5J5K4N1
import Kepler.Text.Reduction4Subseg8
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.Reduction3DefsAssumptionInst

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- **槽 ①（INDEX 8）**：J4 B3' `indexf8_final_lemmas` 结论的 ∀ 形
（HOL more_lemma2.hl:2172–2294；未落库）。 -/
def k3Indexf8Slot : Prop :=
  ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodesTl L hL →
    (hypermapOfList L hL).IsRestricted →
    ∀ {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ},
      markedList L hL N r x → ¬ finalList L r → transformCount L N r x = k →
      ∀ i : ℕ, i + 1 < k →
        (nextEl (core L (rtrans L N r x (i + 1))) (ztrans L N r x i).1 =
            (ytrans L N r x (i + 1)).1 ↔
          nextEl (core L r) (ztrans L N r x i).1 = (ytrans L N r x (i + 1)).1)

/-- **槽 ②（SND_X c）**：HOL `not_mem_yi_zi_list_of_darts`（reduction4.hl:3656–3752
第三合取）结论的 ∀ 形。供料链（见文件头）树内零命中，本槽由后续补件车道供给。 -/
def k3Sx3Slot : Prop :=
  ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodesTl L hL →
    (hypermapOfList L hL).IsRestricted →
    ∀ {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ},
      markedList L hL N r x → ¬ finalList L r → transformCount L N r x = k →
      ∀ i : ℕ, i < k →
        between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
        ((ytrans L N r x i).1, (ztrans L N r x i).1) ∉ listOfDarts (quotientList L N)

/-- **槽 ③（UVNS）**：HOL `final_assumption_uvns_combined`（reduction4.hl:3076–3131）
结论的 ∀ 形（tame-corr U 段在飞）。 -/
def k3UvnsSlot : Prop :=
  ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodesTl L hL →
    (hypermapOfList L hL).IsRestricted →
    ∀ {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ},
      markedList L hL N r x → ¬ finalList L r → transformCount L N r x = k →
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
            d ∈ listPairs (core L r)))

/-- **D1 前置：从 C 辅助件 + 三槽造出 K3 引理**（`reduction_K3Concl` 的 18 合取）。
HOL 对照：reduction4.hl:5404–5431（`reduction_K4` 证体的造 K3CONJ 段）。 -/
theorem reductionK3ConclOfSlots
    (hF8 : k3Indexf8Slot) (hSx3 : k3Sx3Slot) (hUvns : k3UvnsSlot) :
    ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ),
      reductionK3Asm Kepler.Text.Reduction3.GoodNodesSlot
        Kepler.Text.Reduction3.IsRestrictedSlot Kepler.Text.Reduction3.MarkedSlot L N r x k →
      reductionK3Concl L N r x k := by
  intro L N r x k hAsm
  unfold reductionK3Asm at hAsm
  obtain ⟨hL, hgnS, hresS, hmS, hnf, hk⟩ := hAsm
  have hgn : GoodListNodesTl L hL := hgnS hL
  have hres : (hypermapOfList L hL).IsRestricted := hresS hL
  have hm : markedList L hL N r x := hmS hL
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i
  have hk0 : 0 < k := by
    have hne0 : transformCount L N r x ≠ 0 :=
      transformCountNon0OfMarked L hL hgn haq hm hnf
    omega
  -- BETWN 3 的 h0（core L r 侧 0 实例）：betwnCoreReductionLemma ← NotNextCore0I
  have h0 : ∀ (L' : fgraph ℕ) (hL' : GoodList L') (N' : List (List Dart))
      (r' : List Dart) (x' : Dart),
      GoodListNodesTl L' hL' → (hypermapOfList L' hL').IsRestricted →
      markedList L' hL' N' r' x' → ¬ finalList L' r' →
      between (findFaceDarts L' x') (ytrans L' N' r' x' 0) (ztrans L' N' r' x' 0) = [] →
      ¬(nextEl (core L' r') (ytrans L' N' r' x' 0).1 = (ztrans L' N' r' x' 0).1) := by
    intro L' hL' N' r' x' hgn' hres' hm' hnf' hbet
    have haq' : Kepler.Text.Reduction4Idx.AqiunppSlot L' hL' :=
      fun hgn'' N'' r'' x'' hm'' i => Kepler.Text.TameSpine.aqiunpp L' hL' hgn'' N'' r'' x'' hm'' i
    have huniq : (core L' r').Nodup :=
      Kepler.Text.Reduction4Idx.markedListUniqCore L' hL' hm'
    have hne0 : transformCount L' N' r' x' ≠ 0 :=
      transformCountNon0OfMarked L' hL' hgn' haq' hm' hnf'
    have hmain := finalAssumptionsNotNextCore0I L' hL' hgn' hres' haq'
      (transformCount L' N' r' x') hm' hnf' rfl
    exact (betwnCoreReductionLemma L' N' r' x' (transformCount L' N' r' x')
      huniq hne0 hmain).1 hbet
  unfold reductionK3Concl
  exact ⟨indexf2FinalLemmas L hL hgn hres hm hk hk0,
    fun i hi => indexf3FinalLemmas L hL hgn hres haq hm hk hi,
    indexf4FinalLemmas L hL hgn hres hm hk,
    indexf5FinalLemmas L hL hgn hres hm hk,
    indexf6FinalLemmas L hL hgn hres hm hk hk0,
    indexf7FinalLemmas L hL hgn hres hm hk hk0,
    hF8 L hL hgn hres hm hnf hk,
    finalReductionMemZ0Ri L hL hgn hres haq hm hnf hk,
    fun hne => Kepler.Text.TameSpine.betwnCorekZX L hL hgn hres hm hk hk0 hne,
    n1DiffN0 L hL hgn hres hm hnf,
    Kepler.Text.Reduction4.coreiReduction h0 L hL N r x k hgn hres hm hnf hk,
    finalAssumptionsNotNextCore0ZY L hL hgn hres haq hm hnf,
    betwnCore0ZY L hL hgn hres haq hm hnf hk,
    Kepler.Text.Reduction4.finalAssumptionNotMemSndXZx L hL hgn hres haq hm hnf hk,
    Kepler.Text.Reduction4.finalAssumptionNotMemSndXFy L hL hgn hres haq hm hnf hk,
    indexSndX L hL hgn hres hm hnf hk,
    hSx3 L hL hgn hres hm hnf hk,
    hUvns L hL hgn hres hm hnf hk⟩

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.reductionK3ConclOfSlots

/- 接口探针（编译即验证 D1 可直接消费）：`reductionK3` + 本构造件 = assumptionSetK10Full。 -/
#check fun (haq : ∀ (L : Kepler.Graphs.fgraph ℕ) (hL : Kepler.Assembly.GoodList L),
      Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hF8 : Kepler.Text.Reduction5.k3Indexf8Slot)
    (hSx3 : Kepler.Text.Reduction5.k3Sx3Slot)
    (hUvns : Kepler.Text.Reduction5.k3UvnsSlot) =>
  Kepler.Text.Reduction5.reductionK3 haq
    (Kepler.Text.Reduction5.reductionK3ConclOfSlots hF8 hSx3 hUvns)
