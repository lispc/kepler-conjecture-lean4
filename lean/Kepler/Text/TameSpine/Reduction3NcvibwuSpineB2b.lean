/-
  Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2b — W2-件2 Wave B2b 首件：
  `d_lM = y`（头段终点恒等式）。

  ┌─ 归属对账 ────────────────────────────────────────────────────
  │ Ncvibwu.hl:425 `NCVIBWU2` 案析的头段终点：face 轨道自 w 的第 l'm 步
  │ 即 l'y（d_lM = y）。证明 = indexfYtransEqLm（indexf w l'y f = l'm，
  │ JcajyduAqZIndexf:136）+ lYRepPower/fListPowEqNextElPow 幂链移位。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入；既有文件零触碰。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face findFaceDarts_nodup
  nextEl_mem_of_mem)

/-- nextEl 幂保成员（B1 私件同款重推导）。 -/
private theorem orbitMemB2b {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    {x : α} (hx : x ∈ s) : ∀ k : ℕ, (nextEl s)^[k] x ∈ s := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-- **头段终点恒等式**：face 轨道自 `w = nextEl f x` 的第 `l'm` 步 = `l'y`
（`(nextEl f)^[l'm] w = l'y`；NCVIBWU2 头段案析的终点锚）。 -/
theorem dLMeqY (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (nextEl (findFaceDarts L x))^[indexf (nextEl (findFaceDarts L x) x)
        (lYSpine L r x) (findFaceDarts L x)] (nextEl (findFaceDarts L x) x)
      = lYSpine L r x := by
  have hMLm := indexfYtransEqLm L hL hgn hunL hm hf
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  have hyPow : lYSpine L r x
      = (nextEl (findFaceDarts L x))^[lMSpine L r x + 1] x := by
    have h1 : lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x :=
      lYRepPower L r x hnext.symm
    have h2 := minNotEqImpEq (nextEl r) (fList L) x (lMSpine L r x) rfl
      (lMSpine L r x) (Nat.le_refl _)
    calc lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x := h1
      _ = (fList L)^[lMSpine L r x] (nextEl r x) := h2
      _ = (fList L)^[lMSpine L r x] (fList L x) := by rw [hnext]
      _ = (fList L)^[lMSpine L r x + 1] x :=
        (Function.iterate_succ_apply (fList L) (lMSpine L r x) x).symm
      _ = (nextEl (findFaceDarts L x))^[lMSpine L r x + 1] x :=
        fListPowEqNextElPow L hL x hxx (lMSpine L r x + 1)
  rw [hMLm, ← Function.iterate_succ_apply, hyPow]


/-- **UNRESOLVED #2 的机器判定——成立**：`l'm + 1 ≤ sizel r`。
证 = face 轨道 d_0..d_l'm 共 l'm+1 个互异 dart（nextElnIndexf + face Nodup）
全 ∈ r（leYInR）⇒ Finset 基数收口（免弧嵌套、免 wrap 分析）。 -/
theorem lMLtR (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lMSpine L r x + 1 ≤ r.length := by
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x := nextEl_mem_of_mem hxx
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  obtain ⟨hyf, _⟩ := markedLemmaYzInFace L hL hgn hunL hm hf
  have hMLm := indexfYtransEqLm L hL hgn hunL hm hf
  have hltf := indexfLtSizel hwf hyf
  -- hyPow：l'y = (next_el f)^[l'm+1] x（face 轨道）
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  have hyPow : lYSpine L r x
      = (nextEl (findFaceDarts L x))^[lMSpine L r x + 1] x := by
    have h1 : lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x :=
      lYRepPower L r x hnext.symm
    have h2 := minNotEqImpEq (nextEl r) (fList L) x (lMSpine L r x) rfl
      (lMSpine L r x) (Nat.le_refl _)
    calc lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x := h1
      _ = (fList L)^[lMSpine L r x] (nextEl r x) := h2
      _ = (fList L)^[lMSpine L r x] (fList L x) := by rw [hnext]
      _ = (fList L)^[lMSpine L r x + 1] x :=
        (Function.iterate_succ_apply (fList L) (lMSpine L r x) x).symm
      _ = (nextEl (findFaceDarts L x))^[lMSpine L r x + 1] x :=
        fListPowEqNextElPow L hL x hxx (lMSpine L r x + 1)
  have hjd : ∀ k ≤ lMSpine L r x, (nextEl (findFaceDarts L x))^[k + 1] x ∈ r := by
    intro k hk
    by_cases hklM : k = lMSpine L r x
    · rw [hklM, ← hyPow]
      exact ytransMemRtrans L hL hgn hm hf
    · refine leYInR L hL hgn hunL hm hf (orbitMemB2b hxx (k + 1)) ?_
      have hb : lMSpine L r x < (findFaceDarts L x).length := by
        rw [← hMLm]; exact hltf
      have hidxk := nextElnIndexf hwf (orbitMemB2b hxx (k + 1)) hfnd
        (Function.iterate_succ_apply (nextEl (findFaceDarts L x)) k x).symm
        (by omega)
      rw [hidxk]
      omega
  have hinj : ∀ j k, j ≤ lMSpine L r x → k ≤ lMSpine L r x →
      (nextEl (findFaceDarts L x))^[j + 1] x
        = (nextEl (findFaceDarts L x))^[k + 1] x → j = k := by
    intro j k hj hk heq
    have hb : lMSpine L r x < (findFaceDarts L x).length := by
      rw [← hMLm]; exact hltf
    have h1 : indexf (nextEl (findFaceDarts L x) x)
        ((nextEl (findFaceDarts L x))^[j + 1] x) (findFaceDarts L x) = j :=
      nextElnIndexf hwf (orbitMemB2b hxx (j + 1)) hfnd
        (Function.iterate_succ_apply (nextEl (findFaceDarts L x)) j x).symm
        (by omega)
    have h2 : indexf (nextEl (findFaceDarts L x) x)
        ((nextEl (findFaceDarts L x))^[k + 1] x) (findFaceDarts L x) = k :=
      nextElnIndexf hwf (orbitMemB2b hxx (k + 1)) hfnd
        (Function.iterate_succ_apply (nextEl (findFaceDarts L x)) k x).symm
        (by omega)
    rw [heq] at h1
    omega
  have hinjOn : Set.InjOn (fun k => (nextEl (findFaceDarts L x))^[k + 1] x)
      (Finset.range (lMSpine L r x + 1)) := by
    intro a ha b hb heq
    have ha' := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hb' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    exact hinj a b ha' hb' heq
  have himg : Finset.image (fun k => (nextEl (findFaceDarts L x))^[k + 1] x)
      (Finset.range (lMSpine L r x + 1)) ⊆ r.toFinset := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    exact List.mem_toFinset.mpr (hjd k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hcardimg := Finset.card_image_of_injOn hinjOn
  rw [Finset.card_range] at hcardimg
  have hcardr : r.toFinset.card ≤ r.length := by
    rw [List.toFinset_card_of_nodup hrnd]
  exact le_trans hcardimg.symm.le (le_trans (Finset.card_le_card himg) hcardr)

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.dLMeqY
#print axioms Kepler.Text.TameSpine.lMLtR
