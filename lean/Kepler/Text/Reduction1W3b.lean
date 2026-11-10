/-
  Kepler.Text.Reduction1W3b — J4 Wave W3 首波（下）：final_list 连通对
  （HOL reduction1.hl :3122-:3210 `final_list_connected_lemma` +
  `final_list_connected`）。载体与 contour 簇件见 Reduction1W3a（同 patch）。

  跨实例记档：`nextEl` 持 `[BEq α]` 实例参。Island1 系 indexf 件
  （`memNextElIterate`/`nextElnIndexf`/`indexfN`，泛型 `[DecidableEq α]`）烤
  `instBEqOfDecidableEq`；`finalList`/`finalListPowerFn`（Dart 特化）烤
  `instBEqProd`。两实例非 defeq，经 Reduction5Kbwpbhq §0 的公开桥
  `iterateInstEq`（`nextEl` 迭代逐点等式）换装——`indexf` 自身无实例参
  （定义体内固定），陈述无歧义。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W3a
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.PwssratEngine
import Kepler.Text.Reduction4
import Kepler.Text.Reduction5Kbwpbhq
import Kepler.Text.Reduction3DefsAssumptionInst

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts fList nextEl)
open Kepler.Graphs (fgraph)
open Kepler.Text.ChainLists (normalList oneStepList)
open Kepler.Text.Reduction5 (Dart finalList indexf)

/-- **HOL `final_list_connected_lemma`**（reduction1.hl:3122-:3190）：
`MEM u r /\ MEM v r /\ MEM r N /\ final_list L r /\ normal_list L N /\
uniq r /\ indexf u v r = i /\ i < sizel r ==>
contour_list_connected_v2 L (set_of_list r) u v`——对 `i` 完全归纳
（HOL `COMPLETE_INDUCT`；Lean 取界内归纳骨架，对第二端点泛化）：
`i = 0` 支 `indexf0` + refl；`i = m+1` 支经 trans 拼两段——中点
`(f_list L)^m u`（`final_list_power_fn` + `MEM_POWER_NEXT_EL` 保成员），
前段 IH 吃 `next_eln_indexf`，后段两元证人的一步邻接吃 `final_list` +
`indexf_n`（`COM_POWER_FUNCTION` ↦ `iterate_succ_apply'`）。
载体：`set_of_list r` ↦ `{x : Dart | x ∈ r}`、`POWER` ↦ `Function.iterate`。 -/
theorem finalListConnectedLemma {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List Dart)} {r : List Dart} {u v : Dart} {i : ℕ}
    (hur : u ∈ r) (hvr : v ∈ r) (hrN : r ∈ N) (hfin : finalList L r)
    (hnl : normalList L hL N) (hun : r.Nodup)
    (hi : indexf u v r = i) (hlt : i < r.length) :
    contourListConnected L {x : Dart | x ∈ r} u v := by
  have hnlS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  have hdart : ∀ x ∈ r, x ∈ listOfDarts L := fun x hx =>
    Kepler.Text.TameSpine.normalListListOfDarts hnlS x
      (List.mem_flatten.mpr ⟨r, hrN, hx⟩)
  -- 跨实例桥：(nextEl r)^[n] u 的 instBEqProd 形 = instBEqOfDecidableEq 形
  have hinst := Kepler.Text.Reduction5.iterateInstEq r u
  have main : ∀ n : ℕ, ∀ j, j < n → ∀ w : Dart, w ∈ r →
      indexf u w r = j → j < r.length →
      contourListConnected L {x : Dart | x ∈ r} u w := by
    intro n
    induction n with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ n ihn =>
      intro j hj w hw hjW hjL
      rcases Nat.eq_zero_or_pos j with hz | hpos
      · -- i = 0 支：indexf0 ⇒ u = w，refl 直收
        rw [hz] at hjW
        have huw : u = w := Kepler.Text.Reduction4.indexf_eq_zero hur hw hjW
        rw [← huw]
        exact contourListConnectedRefl hur (hdart u hur)
      · -- i = m + 1 支：中点 (f_list L)^m u
        obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
        rw [hm] at hjW hjL
        have hmlt : m < r.length := by omega
        have hMMf : (fList L)^[m] u = (nextEl r)^[m] u :=
          Kepler.Text.Reduction4Idx.finalListPowerFn L m hfin u hur
        have hnm : (nextEl r)^[m] u ∈ r := by
          rw [hinst m]
          exact Kepler.Text.MoreLemma2Island1.memNextElIterate hur m
        have hmmr : (fList L)^[m] u ∈ r := by rw [hMMf]; exact hnm
        have hidx : indexf u ((fList L)^[m] u) r = m :=
          Kepler.Text.MoreLemma2Island1.nextElnIndexf hur hmmr hun
            ((hinst m).symm.trans hMMf.symm) hmlt
        have leg1 : contourListConnected L {x : Dart | x ∈ r} u
            ((fList L)^[m] u) :=
          ihn m (by omega) ((fList L)^[m] u) hmmr hidx hmlt
        -- 后段一步：w = f_list L ((f_list L)^m u)
        have hN : (nextEl r)^[m + 1] u = w := by
          have h0 := Kepler.Text.MoreLemma2Island1.indexfN hur hw hun
          rw [hjW] at h0
          exact (hinst (m + 1)).trans h0
        rw [Function.iterate_succ_apply'] at hN
        have hstep : oneStepList L ((fList L)^[m] u) w := by
          refine Or.inl ?_
          rw [hfin ((fList L)^[m] u) hmmr, hMMf]
          exact hN.symm
        have leg2 : contourListConnected L {x : Dart | x ∈ r}
            ((fList L)^[m] u) w :=
          contourListConnectedPair (hdart _ hmmr) (hdart _ hw) hmmr hw hstep
        exact contourListConnectedTrans leg1 leg2
  exact main (i + 1) i (Nat.lt_succ_self i) v hvr hi hlt

/-- **HOL `final_list_connected`**（reduction1.hl:3191-:3210）：
`MEM u r /\ MEM v r /\ MEM r N /\ final_list L r /\ normal_list L N ==>
contour_list_connected_v2 L (set_of_list r) u v`——lemma 实例化
（`i := indexf u v r`），`uniq r` 支 = `normal_list_uniq_nonnil`、
`i < sizel r` 支 = `indexf_lt_sizel`。 -/
theorem finalListConnected {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List Dart)} {r : List Dart} {u v : Dart}
    (hur : u ∈ r) (hvr : v ∈ r) (hrN : r ∈ N) (hfin : finalList L r)
    (hnl : normalList L hL N) :
    contourListConnected L {x : Dart | x ∈ r} u v := by
  have hnlS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  have hun : r.Nodup := (Kepler.Text.TameSpine.normalListUniqNonnil hnlS hrN).1
  exact finalListConnectedLemma hur hvr hrN hfin hnl hun rfl
    (Kepler.Text.Reduction4.indexf_lt_length_of_mem hur hvr)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.finalListConnectedLemma
#print axioms Kepler.Text.Reduction1.finalListConnected
