/-
  Kepler.Text.Reduction5J5K2A3 — Lane A3：`reduction_K2` 的 K2CONCLUSION → K1CONCLUSION
  包装（HOL reduction4.hl:1276–1442）。

  ┌─ 定位 ─────────────────────────────────────────────────────────
  │ HOL `reduction_K2` 的整句形是
  │   `(!L N r x k. Asm ==> K2CONCLUSION) ==> assumption_setK10`
  │ 其证体首步即 `MATCH_MP_TAC reduction_K1`，即把
  │   K2CONCLUSION（内层全称定理）转成 K1CONCLUSION（28 合取前件表）。
  │ 树内 `reductionK1`（Reduction5J5K1）已落 `K1CONCLUSION → assumptionSetK10`；
  │ 本件补上它缺的那一段：
  │   `(∀ L N r x k, K2Asm → K2CONCLUSION) → (∀ L N r x k, K1Asm → K1CONCLUSION)`。
  │ `reductionK2Step` 是逐态版（28 槽显式装配），`reductionK2` 是 D3b
  │ 全实例化包装（同 `reductionK1Full` 口径），`reductionK2K10` 一行串到 K10。
  └────────────────────────────────────────────────────────────────

  ┌─ 28 槽 ← 来源（K1CONCLUSION 顺序；HOL K2 证体逐条对账）──────────
  │ 1  V                    ← `vFinalLemmas`（nb44）
  │ 2  INDEX 1（next_el）    ← `indexf1FinalLemmas`（nb44）
  │ 3  INDEX (PRE k)        ← K2 INDEX 1（投影）
  │ 4  INDEX (SUC i)        ← K2 INDEX 2（投影）
  │ 5  INDEX 3              ← K2 INDEX 3（投影）
  │ 6  INDEX 4              ← K2 INDEX 4（投影）
  │ 7  INDEX 5              ← K2 INDEX 5（投影）
  │ 8  INDEX 6              ← K2 INDEX 6（投影）
  │ 9  INDEX 7（i>0 形）    ← K2 INDEX 7（i ↦ i-1 换索引）
  │ 10 betwn_corek_z_x      ← K2 BETWN 1（投影）
  │ 11 n1_diff_n0           ← K2 BETWN 2（投影）
  │ 12 not_next @0（y-z）   ← K2 BETWN 3 @0 + `length = 0 ↔ = []` + `rtrans_zero`
  │ 13 not_next 通用 i>0    ← K2 BETWN 3（换 `length = 0 ↔ = []`）
  │ 14 betwn_core0_z_y      ← K2 BETWN 5（i ↦ i-1 换索引）
  │ 15 x ∈ core (rtrans k)  ← `finalAssumptionMemXCore`（在库）
  │ 16 z(PRE k) ∈ core k    ← `finalAssumptionZpreCoreK`（在库）
  │ 17 ∀u∈r, FST u ∈ core r ← `finalAssumptionMemFstCore`（在库）
  │ 18 ∀i<k, FST y_i ∈ core ← `pnxvwfs1` + `finalAssumptionMemFstCore`
  │ 19 ∀i<k, FST z_i ∈ core ← `pnxvwfs2` + `finalAssumptionMemFstCore`
  │ 20 yz_in_core           ← `finalAssumptionYzInCoreUncond`（nb48）
  │ 21 FST (prevEl z0) = FST z0 ← `finalAssumptionFstZ`（在库）
  │ 22 FST y0 ≠ FST z0      ← `finalAssumptionFstYNeqFstZ`（在库）
  │ 23 ∀i<k, y_i ≠ z_i      ← `finalAssumptionYNeZ`（在库）
  │ 24 1 ≤ |find_face|      ← `finalAssumptionSizeFindFace`（在库）
  │ 25 1 < |core r|         ← `finalAssumptionSizeCore`（在库）
  │ 26 PREPPED               ← `finalAssumptionNewvertexPrepped`（在库；三槽由
  │                            `coreSplitNormalListThm`/`rRtransEqThm`/
  │                            `rRtransEqToSpine` 现场实例化）
  │ 27 split_normal_list     ← `finalAssumptionSplitNormalList`（nb50）
  │ 28 UVNS                  ← K2 UVNS（投影）
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；既有陈述零改；主仓 tracked 零改动。
-/

import Kepler.Text.Reduction5J5K2
import Kepler.Text.Reduction5J5K1
import Kepler.Text.Reduction5J5K2Prefix
import Kepler.Text.Reduction5J5Shallow
import Kepler.Text.Reduction5J5FstNe
import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction5J5NewvertexPrepped
import Kepler.Text.Reduction5J5K2A2Final
import Kepler.Text.Reduction5J5K2A2Split
import Kepler.Text.Reduction5J5K2A2Up
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5Ml1W4
import Kepler.Text.Reduction5Ml1W5bBwd
import Kepler.Text.Reduction4Subseg9
import Kepler.Text.Reduction4Subseg4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)

/-- **K2CONCLUSION → K1CONCLUSION 逐态装配**（HOL reduction4.hl:1276–1442 证体）：
K1CONCLUSION 的 28 槽从 K2CONCLUSION 的 14 组 + K1 helper 群消费。 -/
theorem reductionK2Step (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hpre : Kepler.Text.Reduction3.elementPre L N)
    (hnvp : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k)
    (hK2 : reductionK2Concl L N r x k) :
    reductionK1Concl L N r x k := by
  unfold reductionK1Concl
  unfold reductionK2Concl at hK2
  rcases hK2 with
    ⟨hI1, hI2, hI3, hI4, hI5, hI6, hI7, _hMISC, hB1, hB2, hB3, hB4, hB5, hUVNS⟩
  -- `0 < k`（`transform_count_non0`）
  have hk0 : 0 < k := by
    have h := transformCountNon0OfMarked L hL hgn haq hm hnf
    rw [hk] at h
    exact Nat.pos_of_ne_zero h
  -- 状态 i 非 final
  have hnf_i : ∀ i, i < k → ¬ finalList L (rtrans L N r x i) := by
    intro i hi
    exact Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
  -- 28 槽
  -- 1 V
  have hV := vFinalLemmas L hL hgn hres hm hnf hk
  -- 2 INDEX 1
  have hIdx1 := indexf1FinalLemmas L hL hgn hres hm hnf
  -- 9 INDEX 7（i ↦ i-1）
  have hIdx7 : ∀ i : ℕ, 0 < i → i < k →
      (nextEl (core L (rtrans L N r x i)) (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1 ↔
        nextEl (core L r) (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1) := by
    intro i hi0 hik
    have h := hI7 (i - 1) (by omega)
    rwa [Nat.sub_add_cancel hi0] at h
  -- 12 not_next @0（y-z）
  have hNN0 : ¬ ((nextEl (core L r) (ytrans L N r x 0).1 = (ztrans L N r x 0).1) ∧
      (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length = 0) := by
    rintro ⟨hnext, hlen⟩
    have hbet : between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] :=
      List.length_eq_zero_iff.mp hlen
    exact hB3 0 hk0 hbet (by simpa [Kepler.Text.Reduction5.rtrans_zero] using hnext)
  -- 13 not_next 通用 i>0
  have hNNI : ∀ i : ℕ, 0 < i → i < k →
      ¬ ((nextEl (core L (rtrans L N r x i)) (ytrans L N r x i).1 = (ztrans L N r x i).1) ∧
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length = 0) := by
    intro i _hi0 hik
    rintro ⟨hnext, hlen⟩
    exact hB3 i hik (List.length_eq_zero_iff.mp hlen) hnext
  -- 14 betwn_core0_z_y（i ↦ i-1）
  have hB5s : ∀ i : ℕ, 0 < i → i < k →
      (ztrans L N r x (i - 1)).1 ≠ (ytrans L N r x i).1 →
      between (core L r) (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1 =
        between (core L (rtrans L N r x i)) (ztrans L N r x (i - 1)).1
          (ytrans L N r x i).1 := by
    intro i hi0 hik hne
    have hne' : (ztrans L N r x (i - 1)).1 ≠ (ytrans L N r x ((i - 1) + 1)).1 := by
      rwa [Nat.sub_add_cancel hi0]
    have h := hB5 (i - 1) (by omega) hne'
    rwa [Nat.sub_add_cancel hi0] at h
  -- 15 x.1 ∈ core (rtrans k)
  have hMemX := Kepler.Text.Reduction4Idx.finalAssumptionMemXCore L hL haq k hgn hres hnvp hm hnf hk
  -- 16 FST z(PRE k) ∈ core (rtrans k)
  have hMemZ := finalAssumptionZpreCoreK L hL hgn hres haq k hnvp hm hnf hk
  -- 17 ∀u∈r, FST u ∈ core r
  have hMemFst := Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm
  -- 18 / 19 ∀i<k, FST y_i / FST z_i ∈ core r
  have hMemY : ∀ i : ℕ, i < k → (ytrans L N r x i).1 ∈ core L r := by
    intro i hi
    exact Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm _
      (pnxvwfs1 L hL hgn haq i (hnf_i i hi) hm)
  have hMemZi : ∀ i : ℕ, i < k → (ztrans L N r x i).1 ∈ core L r := by
    intro i hi
    exact Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm _
      (pnxvwfs2 L hL hgn haq i (hnf_i i hi) hm)
  -- 20 yz_in_core
  have hYz := finalAssumptionYzInCoreUncond L hL hgn hres haq hm hnf hk hnvp hpre
  -- 21 FST (prevEl z0) = FST z0
  have hFstZ := finalAssumptionFstZ L hL hgn hres k hnvp hm hnf hk
  -- 22 FST y0 ≠ FST z0
  have hFstYZ := finalAssumptionFstYNeqFstZ L hL hgn hres k hm hnf hk
  -- 23 ∀i<k, y_i ≠ z_i
  have hYNeZ := finalAssumptionYNeZ L hL hgn hres haq k hm hnf hk
  -- 24 1 ≤ |find_face|
  have hSizeFF := finalAssumptionSizeFindFace L hL hgn hres k hnvp hm hnf hk
  -- 25 1 < |core r|
  have hSizeCore := finalAssumptionSizeCore L hL hgn hres haq k hnvp hm hnf hk
  -- 26 PREPPED（三槽现场实例化：8b 只增强、不消费）
  have hPrepped := finalAssumptionNewvertexPrepped L hL hgn hres haq hpre hnvp hm hnf hk
    (fun N' r' y hm' hnf' => coreSplitNormalListThm L hL hgn hm' hnf')
    (fun N' r' y hm' hnf' => rRtransEqThm L hL hgn hm' hnf')
    (fun N' r' y hm' hnf' =>
      rRtransEqToSpine L hL hgn hres haq hm' hnf' (rRtransEqThm L hL hgn hm' hnf'))
  -- 27 split_normal_list
  have hSplit := finalAssumptionSplitNormalList L hL hgn hres haq hm hnf hk
    (fun hb => hB3 0 hk0 hb) hB4 hB2
  exact ⟨hV, hIdx1, hI1, hI2, hI3, hI4, hI5, hI6, hIdx7,
    hB1, hB2, hNN0, hNNI, hB5s,
    hMemX, hMemZ, hMemFst, hMemY, hMemZi, hYz,
    hFstZ, hFstYZ, hYNeZ, hSizeFF, hSizeCore, hPrepped, hSplit, hUVNS⟩

/-- **HOL `reduction_K2` 的 K2CONCLUSION → K1CONCLUSION 包装**（D3b 全实例化）：
`hK2` 的类型即 K2 陈述 `∀ L N r x k, K2Asm → K2CONCLUSION`（逐字）；
结论 = K1CONCLUSION 的逐态定理，直接供 `reductionK1`/`reductionK1Full`。 -/
theorem reductionK2
    (haq : ∀ (L : fgraph ℕ) (hL : GoodList L), Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hK2 : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ),
      reductionK2Asm Kepler.Text.Reduction3.GoodNodesSlot
        Kepler.Text.Reduction3.IsRestrictedSlot Kepler.Text.Reduction3.MarkedSlot L N r x k →
        reductionK2Concl L N r x k) :
    ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ),
      reductionK1Asm Kepler.Text.Reduction3.GoodNodesSlot
        Kepler.Text.Reduction3.IsRestrictedSlot Kepler.Text.Reduction3.MarkedSlot L N r x k →
        reductionK1Concl L N r x k := by
  intro L N r x k hAsm
  unfold reductionK1Asm at hAsm
  obtain ⟨hL, hgnS, hresS, hpre, hnvp, hmS, hnf, hk⟩ := hAsm
  exact reductionK2Step L hL (hgnS hL) (hresS hL) (haq L hL) hpre hnvp (hmS hL) hnf hk
    (hK2 L N r x k ⟨hL, hgnS, hresS, hpre, hnvp, hmS, hnf, hk⟩)

/-- 一行串到 K10：`reductionK1Full` ∘ `reductionK2`。 -/
theorem reductionK2K10
    (haq : ∀ (L : fgraph ℕ) (hL : GoodList L), Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hK2 : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ),
      reductionK2Asm Kepler.Text.Reduction3.GoodNodesSlot
        Kepler.Text.Reduction3.IsRestrictedSlot Kepler.Text.Reduction3.MarkedSlot L N r x k →
        reductionK2Concl L N r x k) :
    Kepler.Text.Reduction3.assumptionSetK10Full :=
  reductionK1Full haq (reductionK2 haq hK2)

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.Reduction5.reductionK2Step
#print axioms Kepler.Text.Reduction5.reductionK2
#print axioms Kepler.Text.Reduction5.reductionK2K10
