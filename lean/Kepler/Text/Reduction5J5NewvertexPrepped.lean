/-
  Kepler.Text.Reduction5J5NewvertexPrepped — J5-2 续段：`final_assumption_newvertex_prepped`
  （reduction4.hl:809-:880，75L）的显式槽骨架 + 端口。

  ┌─ 归属对账（HOL Light Flyspeck reduction4.hl:809）──────────────
  │ HOL 陈述（八前提 ⇒ 结论）：
  │   good_list L ∧ good_list_nodes L ∧ is_restricted (hypermap_of_list L) ∧
  │   element_pre L N ∧ newvertex_prepped L N r x ∧ marked_list L N r x ∧
  │   ~final_list L r ∧ transform_count L N r x = k
  │   ⇒ ∀ i. i < k ⇒
  │       iota (sizel (undup (MAP FST (flatten (ntrans L N r x i)))))
  │         (sizel (betwn (find_face L x) (ytrans L N r x i) (ztrans L N r x i))) =
  │       MAP FST (betwn (find_face L x) (ytrans L N r x i) (ztrans L N r x i))
  │ Lean 逐字对应：iota ↦ List.range'、sizel ↦ length、undup ↦ List.dedup、
  │ MAP FST ↦ List.map (fun d => d.1)、betwn ↦ between、find_face ↦ findFaceDarts。
  │ 另加 `haq : AqiunppSlot L hL`（链惯例 +1，同 `faceDiffR`/`lnrxInductionSpine`
  │ 的既有口径：状态 marked、ntrans/rtrans 桥、transform_count 桥都要它）。
  └────────────────────────────────────────────────────────────────

  ┌─ 槽表（外部事实；按派单三槽 + 一处实测勘误 + 一处实测增补）──────
  │ ① `h8b`  = 主机 8b `core_split_normal_list` 结论（tame-corr，未落库）。
  │    **勘误（机器证据）**：本端口**不消费**此槽。HOL :809 中它唯一的用途是
  │    消去 `lnrx_induction` 的 `core_split_normal_list_assumption L` 前提；
  │    树内 `lnrxInductionSpine`（Reduction3LnrxInductionSpine:101）已按
  │    「证体零消费」不携入该前提（同文件 DIFFERS②）。保留形参以与 HOL 依赖面
  │    对表、并在主机 8b 落库后可直接接线；它只使结论更强，不影响可靠性。
  │ ② `hrte` = `r_trans_eq_assumption_lemma`（reduction3.hl:173）结论的
  │    **链世界形**：`∀ N' r' y, rRtransEq L N' r' y`。端口两处消费：
  │    状态 i 的 `faceDiffR` 输入、`lnrxInductionSpine` 的 `hrreAll`。
  │ ②' `hrteS` = 同一外部事实的 **spine 世界形**（`rRtransEqSpine`）。
  │    实测增补：`lnrxInductionSpine` 的签名同时吃链形与 spine 形；树内没有
  │    `rRtransEq → rRtransEqSpine` 的无条件桥（spine 形无 marked/¬final 前提，
  │    两世界改写无前提时不可换），故必须显式携入。属槽②的第二载体。
  │ ③ `hfdr` = `face_diff_r` 结论。**本波已成定理**（Reduction5J5FaceDiffR.faceDiffR），
  │    故 `…OfSlots` 保留槽形，`finalAssumptionNewvertexPrepped` 以真定理实例化
  │    （reify-then-instantiate，同 `reductionK1`/`reductionK1Full` 惯例）。
  └────────────────────────────────────────────────────────────────

  ┌─ 端口路线（HOL :820-:880 逐段对照）──────────────────────────────
  │ ① 状态 i 非 final（`transform_count_not`）+ 状态 i marked（AqiunppSlot）；
  │ ② `lnrx_induction` 于状态 i ⇒ `newvertex_prepped` / `element_pre`
  │    （spine 结论经 `ntransEqSpine`/`rtransEqSpine` 折回链层）；
  │ ③ `rtrans_diff_r` 于状态 i + `l_expand` + `trans_add` ⇒
  │    filter (∉ rtrans i) (rtrans (1+i)) = betwn f y z（= 端口里的 A）；
  │ ④ `face_diff_r` 于状态 i ⇒ filter (∉ rtrans i) fw = A ++ C；
  │ ⑤ `newvertex_alt` 于状态 i ⇒ newvertex = MAP FST (filter (∉ rtrans i) fw)；
  │ ⑥ 长度账：|betwn| = |A| ≤ |A ++ C| = |newvertex|；
  │ ⑦ take/MAP FST 三步：take |A| (A ++ C) = A（`List.take_left`）→
  │    newvertex = range' a |newvertex|（`newvertex_prepped` 非 final 支）→
  │    `take_iota`（树内 `takeIota`，j54 落）收口。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5FaceDiffR
import Kepler.Text.Reduction5J5RotBridges
import Kepler.Text.Reduction5J5Red2Pieces
import Kepler.Text.TameSpine.Reduction3LnrxInductionSpine
import Kepler.Text.TameSpine.Reduction3ChainFinalBridge
import Kepler.Text.ChainSpineBridge
import Kepler.Text.Reduction3Thm1
import Kepler.Text.Reduction4
import Kepler.Text.Reduction4Subseg7
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- 槽③ 的具名形（= `faceDiffR` 的结论，`…OfSlots` 与包装件共用同一 Π 型）。 -/
private theorem faceDiffRSlot (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL) :
    ∀ {N' : List (List Dart)} {r' : List Dart} {x' w : Dart} {fw : List Dart},
      rRtransEq L N' r' x' → markedList L hL N' r' x' →
      nextEl (findFaceDarts L x') x' = w →
      Kepler.Text.Reduction3.rotateTo (findFaceDarts L x') w = fw →
      ¬ finalList L r' →
      fw.filter (fun d => d ∉ r') =
        (rtrans L N' r' x' 1).filter (fun d => d ∉ r') ++
          fw.filter (fun d => d ∉ rtrans L N' r' x' 1) :=
  fun hrr hm' hw' hfw' hnf' => faceDiffR L hL hgn hres haq hrr hm' hw' hfw' hnf'

/-- **HOL `final_assumption_newvertex_prepped`**（reduction4.hl:809）显式槽骨架：
槽 ①（8b，见文件头勘误：本端口不消费）/ ②（`r_trans_eq` 链形 + spine 形）/ ③
（`face_diff_r`）由外部供给，本定理只做 :820-:880 的装配。 -/
theorem finalAssumptionNewvertexPreppedOfSlots (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hpre : Kepler.Text.Reduction3.elementPre L N)
    (hnvp : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hm : markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    (h8b : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
      markedList L hL N' r' y → ¬ finalList L r' → coreSplitNormalList L N' r' y)
    (hrte : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
      markedList L hL N' r' y → ¬ finalList L r' → rRtransEq L N' r' y)
    (hrteS : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
      markedList L hL N' r' y → ¬ finalList L r' →
      Kepler.Text.TameSpine.rRtransEqSpine L N' r' y)
    (hfdr : ∀ {N' : List (List Dart)} {r' : List Dart} {x' w : Dart} {fw : List Dart},
      rRtransEq L N' r' x' → markedList L hL N' r' x' →
      nextEl (findFaceDarts L x') x' = w →
      Kepler.Text.Reduction3.rotateTo (findFaceDarts L x') w = fw →
      ¬ finalList L r' →
      fw.filter (fun d => d ∉ r') =
        (rtrans L N' r' x' 1).filter (fun d => d ∉ r') ++
          fw.filter (fun d => d ∉ rtrans L N' r' x' 1)) :
    ∀ i : ℕ, i < k →
      List.range' ((List.flatten (ntrans L N r x i)).map (fun d => d.1)).dedup.length
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length =
        (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).map
          (fun d => d.1) := by
  intro i hi
  -- ── ① 状态 i：非 final + marked ──
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hfi : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
  have hm_i : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x := haq hgn N r x hm i
  have hxr_i : x ∈ rtrans L N r x i := hm_i.2.2.2.1
  -- ── ② lnrx_induction 于状态 i（spine 结论折回链层） ──
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  have htc : Kepler.Text.TameSpine.transformCountSpine L N r x = k := by
    rw [← Kepler.Text.TameSpine.transformCountEqSpineOfAq L hL hgn haq hm hnf, hk]
  obtain ⟨hnvpSp, -⟩ :=
    Kepler.Text.TameSpine.lnrxInductionSpine L hL hgn hrte hrteS hmS hnvp hpre i (by omega)
  have hnt : ntrans L N r x i = Kepler.Text.TameSpine.ntransSpine L N r x i :=
    Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm i
  have hrt : rtrans L N r x i = Kepler.Text.TameSpine.rtransSpine L N r x i :=
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i
  have hnvp_i : Kepler.Text.Reduction3.newvertexPrepped L (ntrans L N r x i)
      (rtrans L N r x i) x := by
    rw [hnt, hrt]
    exact hnvpSp
  -- newvertex_prepped 的非 final 支 ⇒ newvertex 是连续段
  have hrange : Kepler.Text.Reduction3.newvertex L (rtrans L N r x i) x =
      List.range' ((List.flatten (ntrans L N r x i)).map (fun d => d.1)).dedup.length
        (Kepler.Text.Reduction3.newvertex L (rtrans L N r x i) x).length := by
    simp only [Kepler.Text.Reduction3.newvertexPrepped] at hnvp_i
    rcases hnvp_i with hfin | h
    · exact absurd hfin hfi
    · exact h
  -- ── ③ rtrans_diff_r 于状态 i（+ l_expand + trans_add） ──
  have hA : (rtrans L N r x (1 + i)).filter (fun d => d ∉ rtrans L N r x i) =
      between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) := by
    have h := rtransDiffR L hL hgn hm_i hfi
    rw [← (Kepler.Text.Reduction3.transAdd L N r x i 1).2.1] at h
    rw [(Kepler.Text.Reduction4Idx.l_expand L N r x i).1,
      (Kepler.Text.Reduction4Idx.l_expand L N r x i).2] at h
    exact h
  -- ── ④ face_diff_r 于状态 i ──
  have hF : (Kepler.Text.Reduction3.rotateTo (findFaceDarts L x)
        (nextEl (findFaceDarts L x) x)).filter
        (fun d => d ∉ rtrans L N r x i) =
      (rtrans L N r x (1 + i)).filter (fun d => d ∉ rtrans L N r x i) ++
        (Kepler.Text.Reduction3.rotateTo (findFaceDarts L x)
          (nextEl (findFaceDarts L x) x)).filter
          (fun d => d ∉ rtrans L N r x (1 + i)) := by
    have h := hfdr (hrte (ntrans L N r x i) (rtrans L N r x i) x hm_i hfi) hm_i rfl rfl hfi
    rw [← (Kepler.Text.Reduction3.transAdd L N r x i 1).2.1] at h
    exact h
  -- ── ⑤ newvertex_alt 于状态 i ──
  have hnd : (findFaceDarts L x).Nodup := Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hxf : x ∈ findFaceDarts L x :=
    (Kepler.Text.TameLp.dart_in_face L x).mpr
      (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm)
  have hNV : Kepler.Text.Reduction3.newvertex L (rtrans L N r x i) x =
      ((Kepler.Text.Reduction3.rotateTo (findFaceDarts L x)
        (nextEl (findFaceDarts L x) x)).filter
        (fun d => d ∉ rtrans L N r x i)).map (fun d => d.1) :=
    newvertexAlt L (rtrans L N r x i) x hnd hxf hxr_i
  -- ── ⑥ 长度账 ──
  have hlenA : (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length =
      ((rtrans L N r x (1 + i)).filter (fun d => d ∉ rtrans L N r x i)).length := by
    rw [hA]
  have hlen_le : (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length ≤
      (Kepler.Text.Reduction3.newvertex L (rtrans L N r x i) x).length := by
    rw [hlenA, hNV, List.length_map, hF, List.length_append]
    omega
  -- ── ⑦ take / MAP FST 三步 ──
  have htake : (Kepler.Text.Reduction3.newvertex L (rtrans L N r x i) x).take
        (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length =
      (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).map
        (fun d => d.1) := by
    rw [hNV, ← List.map_take, hF, hlenA]
    rw [List.take_left, hA]
  rw [hrange] at htake
  rw [takeIota (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length
    (Kepler.Text.Reduction3.newvertex L (rtrans L N r x i) x).length
    ((List.flatten (ntrans L N r x i)).map (fun d => d.1)).dedup.length hlen_le] at htake
  exact htake

/-- **HOL `final_assumption_newvertex_prepped`**（reduction4.hl:809）：槽③
（`face_diff_r`）由本波定理 `faceDiffR` 实例化；槽①②（8b / r_trans_eq 双世界形）
仍为外部事实。 -/
theorem finalAssumptionNewvertexPrepped (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hpre : Kepler.Text.Reduction3.elementPre L N)
    (hnvp : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hm : markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    (h8b : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
      markedList L hL N' r' y → ¬ finalList L r' → coreSplitNormalList L N' r' y)
    (hrte : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
      markedList L hL N' r' y → ¬ finalList L r' → rRtransEq L N' r' y)
    (hrteS : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
      markedList L hL N' r' y → ¬ finalList L r' →
      Kepler.Text.TameSpine.rRtransEqSpine L N' r' y) :
    ∀ i : ℕ, i < k →
      List.range' ((List.flatten (ntrans L N r x i)).map (fun d => d.1)).dedup.length
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length =
        (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).map
          (fun d => d.1) :=
  finalAssumptionNewvertexPreppedOfSlots L hL hgn hres haq hpre hnvp hm hnf hk
    h8b hrte hrteS (faceDiffRSlot L hL hgn hres haq)

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.finalAssumptionNewvertexPreppedOfSlots
#print axioms Kepler.Text.Reduction5.finalAssumptionNewvertexPrepped
