/-
  Kepler.Text.PwssratMemberBase — 无撞铺装波 patch1：PWSSRAT member 基座
  （next_el_rotate_to_eq → f_eq_next_el_x → l_y_rep_power → ytrans_mem_rtrans）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）────────
  │ PWSSRAT.hl:122 `next_el_rotate_to_eq` → nextElRotateToEq
  │ PWSSRAT.hl:160 `f_eq_next_el_x`       → fEqNextElX（rtrans 形）
  │ PWSSRAT.hl:263 `l_y_rep_power`        → lyNextElPow
  │ PWSSRAT.hl:275 `ytrans_mem_rtrans`    → ytransMemRtrans
  │ 本批未含（闸 HQYMRTX1_list，见 DELIVERY）：mem_ztrans_rtrans /
  │ z_not_eq_ytrans（消费 HQYMRTX1_list，其 markedTranslate hs 槽链侧
  │ 无填充物——待编排者裁）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与折算 ──────────────────────────────────────────────────
  │ `rotate_to` ↦ Reduction3.rotateTo；`split_at` ↦ Graphs.splitAt
  │ （patch_p2pre1 底座：splitAtRec 分解/sndEmptyIndexl/hdFstSplit）；
  │ `next_el` ↦ nextEl；`f_list` ↦ fList；`l'm`/`l'y` ↦
  │ Reduction5.lm/ly；`ytrans` ↦ Reduction5.ytrans；`ITER` ↦ f^[n]；
  │ `min_not_eq_imp_eq_at` ↦ MoreLemma2Aux.minNotEqImpEq（at 形已落）；
  │ `MEM_POWER_NEXT_EL` ↦ MoreLemma2Island1.memNextElIterate；
  │ AQIUNPP3 ↦ AqiunppSlot（Subseg9 槽）+ transform_list_power_rep
  │ 链侧 defs rfl 吸收（rtrans = iterate 投影）。
  │ 环安全：imports = PwssratRotateBase（patch_p2pre1 底座）+
  │ Reduction4Subseg9（AqiunppSlot）+ MoreLemma2Aux + Reduction5。
  │ 零 axiom/sorry/admit/native_decide；主仓 tracked 零改动。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.PwssratRotateBase
import Kepler.Text.Reduction4Subseg9
import Kepler.Text.MoreLemma2Aux
import Kepler.Text.Reduction5Tav2

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph splitAt splitAtRec)
open Kepler.Assembly (GoodList nextEl fList)
open Kepler.Text.Reduction3 (rotateTo)
open Kepler.Text.Reduction5 (Dart lm ly ytrans rtrans ntrans
  transformAssumptionV2)
open Kepler.Text.ChainLists (markedList normalList)
open Kepler.Text.Reduction5 (quotientList)

/-! ## §1 `next_el_rotate_to_eq`（PWSSRAT:122；rotate 件本体）

HOL：`!r. MEM x r ∧ uniq r ⇒ next_el r x = next_el (rotate_to r x) x`。
证明 = splitAtRec 分解（patch_p2pre1）+ 两支（x 末位 / 非末位）逐支 idxOf 算术。 -/

/-- 分解决策位：`x ∈ r`、Nodup ⇒ `x ∉ fst(splitAt x r)`。 -/
private theorem notMem_splitAt_fst {α : Type*} [BEq α] [LawfulBEq α] {x : α}
    {r : List α} (hmem : x ∈ r) (hnd : r.Nodup) :
    x ∉ (splitAt x r).1 := by
  obtain ⟨fst, hreq, hfst⟩ := splitAtRec_exists_append r [] hmem (by simp)
  have hfst' : (splitAtRec x [] r).1 = fst := by rw [hfst, List.nil_append]
  have hnd' : (fst ++ x :: (splitAtRec x [] r).2).Nodup := by
    rw [← hreq]
    exact hnd
  have hdis : List.Disjoint fst (x :: (splitAtRec x [] r).2) :=
    List.disjoint_of_nodup_append hnd'
  rw [show (splitAt x r).1 = fst from hfst']
  intro hc
  exact hdis hc (List.mem_cons.mpr (Or.inl rfl))

/-- `x` 的 `idxOf` 值（分解形）：`r = fst ++ x :: snd`、`x ∉ fst`
⇒ `idxOf x r = fst.length`。 -/
private theorem idxOf_splitAt_fst {α : Type*} [BEq α] [LawfulBEq α] {x : α}
    {r : List α} (hmem : x ∈ r) (hnd : r.Nodup) :
    r.idxOf x = (splitAt x r).1.length := by
  obtain ⟨fst, hreq, hfst⟩ := splitAtRec_exists_append r [] hmem (by simp)
  have hfst' : (splitAtRec x [] r).1 = fst := by rw [hfst, List.nil_append]
  have hxf : x ∉ fst := by
    have h := notMem_splitAt_fst hmem hnd
    rwa [show (splitAt x r).1 = fst from hfst'] at h
  rw [show (splitAt x r).1 = fst from hfst', hreq,
    List.idxOf_append_of_notMem hxf,
    List.idxOf_cons_eq (l := (splitAtRec x [] r).2) rfl]
  simp

/-- **HOL `next_el_rotate_to_eq`**（PWSSRAT.hl:122-:158）。 -/
theorem nextElRotateToEq {α : Type} [BEq α] [LawfulBEq α] {r : List α} {x : α}
    (hmem : x ∈ r) (hnd : r.Nodup) :
    nextEl r x = nextEl (rotateTo r x) x := by
  obtain ⟨fst, hreq, hfst⟩ := splitAtRec_exists_append r [] hmem (by simp)
  have hsplit1 : (splitAt x r).1 = fst := by
    rw [show (splitAt x r).1 = (splitAtRec x [] r).1 from rfl, hfst,
      List.nil_append]
  have hsplit2 : (splitAt x r).2 = (splitAtRec x [] r).2 := rfl
  have hxf : x ∉ fst := by
    rw [← hsplit1]
    exact notMem_splitAt_fst hmem hnd
  have hidx : r.idxOf x = fst.length := by
    rw [← hsplit1]
    exact idxOf_splitAt_fst hmem hnd
  have hlen : r.length = fst.length + 1 + (splitAtRec x [] r).2.length := by
    have h := congrArg List.length hreq
    simp [List.length_append, List.length_cons] at h
    omega
  by_cases hsnd : (splitAtRec x [] r).2 = []
  · -- x 位于末位：两侧 nextEl 都落到 r 的头部
    have hlen1 : r.length = fst.length + 1 := by
      rw [hlen, hsnd]
      simp
    have hidxlast : r.idxOf x = r.length - 1 := by
      rw [hidx, hlen1]
      omega
    rw [nextEl, if_pos hidxlast]
    -- rotateTo r x = x :: fst
    have hrot : rotateTo r x = x :: fst := by
      unfold rotateTo
      rw [hsplit1, hsplit2, hsnd, List.singleton_append]
    rw [hrot]
    have hnotlast : ¬ ((x :: fst).idxOf x = (x :: fst).length - 1) ∨
        fst = [] := by
      by_cases hf : fst = []
      · exact Or.inr hf
      · left
        intro hc
        rw [List.idxOf_cons_self] at hc
        simp at hc
        exact hf (List.length_eq_zero_iff.mp hc.symm)
    rcases hnotlast with hn | hf
    · rw [nextEl, if_neg hn, List.idxOf_cons_self, Nat.zero_add]
      -- getD 1 (x::fst) = fst.headD x；r.headD x 同
      have hgetD : (x :: fst).getD 1 x = fst.headD x := by
        cases fst with
        | nil => rfl
        | cons b bs => rfl
      rw [hgetD]
      -- r.headD x = fst.headD x（r = fst ++ [x]，fst ≠ []）
      have hf : fst ≠ [] := by
        intro hc
        exact hn (by rw [hc]; simp)
      rw [hreq, hsnd]
      cases fst with
      | nil => exact absurd rfl hf
      | cons b bs => rfl
    · -- fst = []：r = [x]，两侧同为 x
      subst hf
      rw [hreq, hsnd, List.nil_append]
      simp [nextEl]
  · -- x 非末位：两侧 nextEl 都落到 x 的后继
    have hlen2 : r.length - 1 = fst.length + (splitAtRec x [] r).2.length := by
      rw [hlen]
      have : 0 < (splitAtRec x [] r).2.length :=
        List.length_pos_iff.mpr hsnd
      omega
    have hnotlast : ¬ (r.idxOf x = r.length - 1) := by
      rw [hidx, hlen2]
      have : 0 < (splitAtRec x [] r).2.length :=
        List.length_pos_iff.mpr hsnd
      omega
    rw [nextEl, if_neg hnotlast, hidx]
    -- 左侧 getD = snd.headD
    have hleft : r.getD (fst.length + 1) x =
        (splitAtRec x [] r).2.headD x := by
      have hg := congrArg (fun s => s.getD (fst.length + 1) x) hreq
      rw [hg, List.getD_append_right (h := by omega)]
      rw [show fst.length + 1 - fst.length = 1 from by omega]
      cases h2 : (splitAtRec x [] r).2 with
      | nil => exact absurd h2 hsnd
      | cons b bs => rfl
    rw [hleft]
    -- rotateTo r x = x :: (snd ++ fst)
    have hrot : rotateTo r x = x :: ((splitAtRec x [] r).2 ++ fst) := by
      unfold rotateTo
      rw [hsplit1, hsplit2, List.cons_append]
    rw [hrot, nextEl]
    have hnotlast2 : ¬ ((x :: ((splitAtRec x [] r).2 ++ fst)).idxOf x =
        (x :: ((splitAtRec x [] r).2 ++ fst)).length - 1) := by
      intro hc
      rw [List.idxOf_cons_self] at hc
      rw [List.length_cons, List.length_append] at hc
      have hpos : 0 < (splitAtRec x [] r).2.length :=
        List.length_pos_iff.mpr hsnd
      omega
    rw [if_neg hnotlast2, List.idxOf_cons_self, Nat.zero_add]
    have hright : (x :: ((splitAtRec x [] r).2 ++ fst)).getD 1 x =
        (splitAtRec x [] r).2.headD x := by
      cases h2 : (splitAtRec x [] r).2 with
      | nil => exact absurd h2 hsnd
      | cons b bs => rfl
    rw [hright]

end Kepler.Text.Reduction4Idx

#print axioms Kepler.Text.Reduction4Idx.nextElRotateToEq
#print axioms Kepler.Text.Reduction4Idx.idxOf_splitAt_fst
