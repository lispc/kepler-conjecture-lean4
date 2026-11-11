/-
  Kepler.Text.Reduction5J5K3 — Lane B4：`reduction_K3` 的 K3 引理 ⇒ K2 引理 ⇒ K10
  （HOL reduction4.hl:3132–3226）。

  ┌─ 定位 ─────────────────────────────────────────────────────────
  │ HOL `reduction_K3` 整句形：
  │   `(!L N r x k. K3ASM ==> K3CONJ) ==> assumption_setK10`
  │ 证体首步 `DISCH_TAC; MATCH_MP_TAC reduction_K2`，随后从 K3CONJ 造出
  │ K2CONCLUSION（INDEX 段由 `More_lemma2.indexf*_final_lemmas` 现场供给，
  │ MISC/BETWN 段由 K3CONJ 供给，UVNS 由 `final_assumption_uvns_combined` 供给）。
  │ 本件把这条链压成一次投影：
  │   `reductionK3 (haq) (hK3 : ∀ L N r x k, K3Asm → K3Concl) : assumptionSetK10Full`
  │ = `reductionK2K10 haq (fun L N r x k hAsm => K2CONCLUSION 从 hK3 逐槽重组)`。
  └────────────────────────────────────────────────────────────────

  ┌─ ERRATA（HOL 活段逐行核对；重要）──────────────────────────────
  │ HOL K3CONCLUSION（:3132–3225）**活段只有 10 个合取**：
  │   ① MISC `z0 ∈ rtrans i`（:3169）
  │   ② BETWN 1 betwn_corek_z_x（:3172-3174）
  │   ③ BETWN 2 n1_diff_n0（:3177-3178）
  │   ④ BETWN 3 not_next 通用 i（:3179-3181）
  │   ⑤ BETWN 4 not_next @0（:3182-3184）
  │   ⑥ BETWN 5 betwn_core0_z_y（:3187-3190）
  │   ⑦ NEW `SND x ∉ ifbetwn (core r) (FST z(PRE k)) (FST x)`（:3198）
  │   ⑧ SND_X a `1 < |ftrans i :: ifbetwn …| ⇒ SND x ∉ …`（:3201-3208）
  │   ⑨ SND_X b `indexf (SND x) (FST y_i) (core r) < … (FST z_i)`（:3213-3215）
  │   ⑩ SND_X c `betwn = [] ⇒ (FST y_i, FST z_i) ∉ list_of_darts (quotient_list)`（:3216-3220）
  │ **INDEX 块（:3146–3166）整段被 `//` 注释**、**UVNS 不在 K3 陈述里**——
  │ 二者在 HOL 里分别由 `More_lemma2.indexf*_final_lemmas` 与
  │ `final_assumption_uvns_combined` 在 reduction_K3 证体内现场证明。
  │ 本件按派单枚举（INDEX f2..f8 + MISC + BETWN + SND_X + UVNS）落
  │ `reductionK3Concl` = HOL 活段 10 + K2CONCLUSION 的 INDEX 7 + UVNS 1 = **18 合取**。
  │ 理由：派单签名固定为 `haq → hK3 → assumptionSetK10Full`（无 indexf8/uvns 槽），
  │ 而 `indexf8FinalLemmas` 仍为 J4 B3' 在飞（PARTIAL）、
  │ `final_assumption_uvns_combined`（HOL :3076–3131）树内零命中——两条都不在
  │ 「≤60 行补桥」范围。把 INDEX/UVNS 作为 K3 引理的槽（hK3 的结论）后，
  │ `reductionK3` 是纯重组（零重证 indexf2..f8），其生产者正是 Lane B 的
  │ 独立蓝本与 UVNS 车道。`reductionK3Concl` 比 HOL 活段强（前提更强 = 定理更弱），
  │ 但最终 K10 出口仍是 `reductionK2K10`，未削弱任何已声明结论。
  └────────────────────────────────────────────────────────────────

  ┌─ reductionK3Concl 18 合取（顺序 = K2CONCLUSION 前 13 + K3 新 4 + UVNS）──
  │ 1-7  INDEX 1-7（K2 :1289–1310，逐字）①
  │ 8    MISC（K3 :3169）
  │ 9-13 BETWN 1-5（K3 :3172–3190，逐字）
  │ 14   NEW（K3 :3198）
  │ 15-17 SND_X a/b/c（K3 :3201–3220）
  │ 18   UVNS（K2 :1336–1341，逐字）
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；不删改既有 def；主仓 tracked 零改动。
-/

import Kepler.Text.Reduction5J5K2A3
import Kepler.Text.Reduction5J5K2
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.Reduction5Base

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)

/-- **HOL `reduction_K3` 假设块**（reduction4.hl:3136–3143 活段，六前提逐字）：
`good_list / good_list_nodes / is_restricted / marked_list / ¬final_list /
transform_count = k`。HOL 的 `element_pre` / `newvertex_prepped` 两行已注释，
不携入（与 K1/K2 的八前提差两项）。 -/
def reductionK3Asm (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ) : Prop :=
  GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧
    Marked L N r x ∧ ¬ finalList L r ∧ transformCount L N r x = k

/-- **HOL `reduction_K3` 的 K3 引理结论**（18 合取）：
HOL 活段 10（MISC + BETWN 1-5 + NEW + SND_X a/b/c）
+ K2CONCLUSION 的 INDEX 1-7 与 UVNS（见文件头 ERRATA）。 -/
def reductionK3Concl (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (k : ℕ) : Prop :=
  -- INDEX 1-7（K2 :1289–1310，逐字）
  (indexf (ztrans L N r x (k - 1)).1 x.1 (core L r) =
    indexf (ztrans L N r x (k - 1)) x (findFaceDarts L x)) ∧
  (∀ i : ℕ, i + 1 < k →
    indexf (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 (core L r) =
      indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) (findFaceDarts L x)) ∧
  (∀ i : ℕ, i + 1 < k →
    indexf (ytrans L N r x 0) (ztrans L N r x i) (findFaceDarts L x) ≤
      indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) (findFaceDarts L x)) ∧
  (∀ i : ℕ, i + 1 < k →
    indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) (findFaceDarts L x) ≤
      indexf (ytrans L N r x 0) (ztrans L N r x (i + 1)) (findFaceDarts L x)) ∧
  (indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (k - 1)) (findFaceDarts L x) ≤
    indexf (nextEl (findFaceDarts L x) x) x (findFaceDarts L x)) ∧
  (indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0) (findFaceDarts L x) ≤
    indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (k - 1)) (findFaceDarts L x)) ∧
  (∀ i : ℕ, i + 1 < k →
    (nextEl (core L (rtrans L N r x (i + 1))) (ztrans L N r x i).1 =
        (ytrans L N r x (i + 1)).1 ↔
      nextEl (core L r) (ztrans L N r x i).1 = (ytrans L N r x (i + 1)).1)) ∧
  -- MISC（K3 :3169）
  (∀ i : ℕ, i < k → ztrans L N r x 0 ∈ rtrans L N r x i) ∧
  -- BETWN 1（K3 :3172–3174）
  ((ztrans L N r x (k - 1)).1 ≠ x.1 →
    between (core L (rtrans L N r x k)) (ztrans L N r x (k - 1)).1 x.1 =
      between (core L r) (ztrans L N r x (k - 1)).1 x.1) ∧
  -- BETWN 2（K3 :3177–3178）
  ({z : ℕ | z ∈ (ntrans L N r x 1).flatten.map (fun d => d.1) ∧
      z ∉ N.flatten.map (fun d => d.1)} =
    {z : ℕ | z ∈ (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).map
      (fun d => d.1)}) ∧
  -- BETWN 3（K3 :3179–3181）
  (∀ i : ℕ, i < k →
    between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
    nextEl (core L (rtrans L N r x i)) (ytrans L N r x i).1 ≠
      (ztrans L N r x i).1) ∧
  -- BETWN 4（K3 :3182–3184）
  (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
    nextEl (core L (rtrans L N r x 0)) (ztrans L N r x 0).1 ≠
      (ytrans L N r x 0).1) ∧
  -- BETWN 5（K3 :3187–3190）
  (∀ i : ℕ, i + 1 < k → (ztrans L N r x i).1 ≠ (ytrans L N r x (i + 1)).1 →
    between (core L r) (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 =
      between (core L (rtrans L N r x (i + 1))) (ztrans L N r x i).1
        (ytrans L N r x (i + 1)).1) ∧
  -- NEW（K3 :3198）
  (x.2 ∉ ifbetwn (core L r) (ztrans L N r x (k - 1)).1 x.1) ∧
  -- SND_X a（K3 :3201–3208）
  (∀ i : ℕ, i < k ∧
      1 < (ftrans L N r x i ::
        ifbetwn (core L r) (ftrans L N r x i) (ytrans L N r x i).1).length →
      x.2 ∉ ifbetwn (core L r) (ftrans L N r x i) (ytrans L N r x i).1) ∧
  -- SND_X b（K3 :3213–3215）
  (∀ i : ℕ, i < k →
    indexf x.2 (ytrans L N r x i).1 (core L r) <
      indexf x.2 (ztrans L N r x i).1 (core L r)) ∧
  -- SND_X c（K3 :3216–3220）
  (∀ i : ℕ, i < k →
    between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
    ((ytrans L N r x i).1, (ztrans L N r x i).1) ∉
      listOfDarts (quotientList L N)) ∧
  -- UVNS（K2 :1336–1341，逐字）
  (∀ v : ℕ, (Kepler.Assembly.prevEl (core L r) v, v) = x →
    (let uvns := Kepler.Text.Reduction3.coreTripleV4 L N r x
     let vs := Kepler.Text.Reduction3.destTripleFull (core L r) v uvns
     let vs' := vs.filterMap id
     (∀ i : ℕ, i + 1 < vs'.length →
        indexf v (vs'.getD i 0) (core L r) < indexf v (vs'.getD (i + 1) 0) (core L r)) ∧
      (∀ i : ℕ,
        let d : Dart := ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0);
        ((vs.getD i none).isSome ∧ (vs.getD (i + 1) none).isSome ∧
          i + 1 < vs.length ∧ d ∈ listOfDarts (quotientList L N)) →
        d ∈ listPairs (core L r))))

/-- **HOL `reduction_K3`**（reduction4.hl:3132–3226）：
从 K3 引理逐槽重组出 K2 引理（INDEX/MISC/BETWN/UVNS），
再经 `reductionK2K10` 一行收口到 `assumptionSetK10Full`。 -/
theorem reductionK3
    (haq : ∀ (L : fgraph ℕ) (hL : GoodList L), Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hK3 : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ),
      reductionK3Asm Kepler.Text.Reduction3.GoodNodesSlot
        Kepler.Text.Reduction3.IsRestrictedSlot Kepler.Text.Reduction3.MarkedSlot L N r x k →
        reductionK3Concl L N r x k) :
    Kepler.Text.Reduction3.assumptionSetK10Full :=
  reductionK2K10 haq (fun L N r x k hAsm => by
    unfold reductionK2Asm at hAsm
    obtain ⟨hL, hgnS, hresS, _hpre, _hnvp, hmS, hnf, hk⟩ := hAsm
    have hK3c := hK3 L N r x k ⟨hL, hgnS, hresS, hmS, hnf, hk⟩
    unfold reductionK3Concl at hK3c
    rcases hK3c with
      ⟨i1, i2, i3, i4, i5, i6, i7, misc, b1, b2, b3, b4, b5,
        _new, _sx1, _sx2, _sx3, uvns⟩
    unfold reductionK2Concl
    exact ⟨i1, i2, i3, i4, i5, i6, i7, misc, b1, b2, b3, b4, b5, uvns⟩)

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.Reduction5.reductionK3Asm
#print axioms Kepler.Text.Reduction5.reductionK3Concl
#print axioms Kepler.Text.Reduction5.reductionK3
