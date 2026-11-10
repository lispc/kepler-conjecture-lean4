/-
  Kepler.Text.Reduction5BetwnBase — W2-c-1a：betwn_core0_z_y 塔的供给层链孪生
  第一批（TameList3 betwn/indexf 簇六件 + indexfCompl + memPrevEl +
  sizeFlattenLe）。

  ┌─ 双落指针（防重复落对账；W2C_PLAN §3 W2-c-1 / §6）────────────
  │ 本文件各件与 Spine 侧孪生逐字同内容、载体多态：betwnMem/
  │ indexfLtSizel/sizeBetwn/indexlBetwn/indexfBetwn/indexfBetwnEq ↔
  │ TameList3（Spine，不删，tame-corr 领土）；indexfCompl ↔
  │ TameList3.indexfAntisym（B2 indexf_add_sum 是 < len 侧条件形，
  │ 补位）；memPrevEl ↔ Seq2.mem_prev_el（全树原零命中，首落）；
  │ sizeFlattenLe ↔ TameList56/57。双家记账沿 parts_cat 先例（续493）。
  │ 证明体不走 Spine 内部机（betwnTakeDrop/splitAt 展开），改走链侧
  │ Reduction4 between 族 + TameLp getElem_idxOf/idxOf_getElem
  │ （W2C_PLAN §6.2）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（诚实收窄记档；塔内消费全带 x≠z 已核）────────────────
  │ `indexlBetwn`/`indexfBetwn`/`indexfBetwnEq` 的 z = x 支需
  │ `between s x x` 自形引理（ListAux splitAt 展开），本批以 `x ≠ z`
  │ 前提收窄；塔内三个消费点全部以 ¬(FST zi = FST ys) 喂入 x ≠ z，
  │ 收窄不影响塔。无条件形恢复挂账 W2-c-1b+。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；主仓 tracked 零改动；
  零 import TameSpine（链侧纯）。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction4
import Kepler.Text.MoreLemma2Island1
import Kepler.Graphs.ListAuxLemmas

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

variable {α : Type} [DecidableEq α]

open Kepler.Graphs (between)
open Kepler.Assembly (nextEl prevEl)
open Kepler.Text.Reduction4 (indexf_lt_length_of_mem indexf_eq_length_of_not_mem
  indexfRefl indexf_add_left betwnMemCover between_eq_take_of_idxOf_lt
  between_eq_append_of_idxOf_gt)

/-! ## §0 indexf 辅件（TameList3 内件链孪生） -/

/-- indexf 的 idxOf 条件形（TameList3.indexfCond 链孪生，private）。 -/
private theorem indexfCond {x y : α} {s : List α} (hx : x ∈ s) (hy : y ∈ s) :
    indexf x y s =
      if s.idxOf x ≤ s.idxOf y then s.idxOf y - s.idxOf x
      else s.idxOf y + (s.length - s.idxOf x) := by
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  unfold indexf
  rw [if_pos ⟨hx, hy⟩]
  by_cases hle : s.idxOf x ≤ s.idxOf y
  · rw [if_pos hle]
    have hsum : s.idxOf y + (s.length - s.idxOf x) =
        s.length + (s.idxOf y - s.idxOf x) := by omega
    have hlt : s.idxOf y - s.idxOf x < s.length := by omega
    rw [hsum, Nat.add_comm s.length (s.idxOf y - s.idxOf x),
      Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  · rw [if_neg hle, Nat.mod_eq_of_lt (by omega)]

/-- **HOL `indexf_antisym`**（tame_list.hl:1601，TameList3.indexfAntisym 链孪生）：
双侧成员 + `x ≠ y` ⇒ `indexf x y s + indexf y x s = s.length`。
（B2 `indexf_add_sum` 是 `< s.length` 侧条件形，非本件。） -/
theorem indexfCompl {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    indexf x y s + indexf y x s = s.length := by
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hxy : s.idxOf x ≠ s.idxOf y := by
    intro e
    have h1 : s[s.idxOf x] = x := Kepler.Text.TameLp.getElem_idxOf hx
    have h2 : s[s.idxOf y] = y := Kepler.Text.TameLp.getElem_idxOf hy
    simp only [e] at h1
    rw [h2] at h1
    exact hne h1.symm
  have key : ∀ (i j : ℕ), i < s.length → j < s.length → j ≠ i →
      (j + (s.length - i)) % s.length + (i + (s.length - j)) % s.length = s.length := by
    intro i j hi hj hne'
    rcases Nat.lt_or_ge i j with hlt | hge
    · have hjlt : j - i < s.length := by omega
      have hilt : i + (s.length - j) < s.length := by omega
      have hsum1 : j + (s.length - i) = s.length + (j - i) := by omega
      rw [hsum1, Nat.add_comm s.length (j - i), Nat.add_mod_right,
        Nat.mod_eq_of_lt hjlt, Nat.mod_eq_of_lt hilt]
      omega
    · have hlt2 : j < i := by omega
      have hjlt : j + (s.length - i) < s.length := by omega
      have hilt : i - j < s.length := by omega
      have hsum2 : i + (s.length - j) = s.length + (i - j) := by omega
      rw [Nat.mod_eq_of_lt hjlt, hsum2, Nat.add_comm s.length (i - j),
        Nat.add_mod_right, Nat.mod_eq_of_lt hilt]
      omega
  unfold indexf
  rw [if_pos ⟨hx, hy⟩, if_pos ⟨hy, hx⟩]
  exact key _ _ hix hiy (Ne.symm hxy)

/-! ## §A TameList3 betwn/indexf 簇六件（链孪生） -/

/-- **HOL `betwn_mem`**（tame_list.hl:2622）：`w ∈ between f u v ⇒ w ∈ f`。 -/
theorem betwnMem {f : List α} {u v w : α} (h : w ∈ between f u v) : w ∈ f :=
  Kepler.Graphs.inbetween_inset h

/-- **HOL `indexf_lt_sizel`**（tame_list.hl:1537）。 -/
theorem indexfLtSizel {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) : indexf x y s < s.length :=
  indexf_lt_length_of_mem hx hy

/-- **HOL `size_betwn`**（tame_list.hl:2726）：`uniq s ∧ x,y ∈ s ∧ x ≠ y ⇒
sizel (betwn s x y) = indexf x y s - 1`。 -/
theorem sizeBetwn {s : List α} {x y : α}
    (hnd : s.Nodup) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (between s x y).length = indexf x y s - 1 := by
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hxy : s.idxOf x ≠ s.idxOf y := by
    intro e
    have h1 : s[s.idxOf x] = x := Kepler.Text.TameLp.getElem_idxOf hx
    have h2 : s[s.idxOf y] = y := Kepler.Text.TameLp.getElem_idxOf hy
    simp only [e] at h1
    rw [h2] at h1
    exact hne h1.symm
  by_cases hij : s.idxOf x < s.idxOf y
  · rw [between_eq_take_of_idxOf_lt hnd hx hy hij, indexfCond hx hy, if_pos (by omega)]
    rw [List.length_take, List.length_drop]
    omega
  · push Not at hij
    have hlt' : s.idxOf y < s.idxOf x := by omega
    rw [between_eq_append_of_idxOf_gt hnd hx hy hlt', indexfCond hx hy, if_neg (by omega)]
    rw [List.length_append, List.length_drop, List.length_take]
    omega

/-! ## （indexlBetwn/indexfBetwn/indexfBetwnEq 移 W2-c-1a 第二笔：z=x 自形与
getElem 边界已定位，见 W2C_PLAN §6 与本轮交付说明。） -/

/-! ## §B Seq2 首件 -/

/-! （Seq2.mem_prev_el 本批积分已绿但与 prevNextId/nextPrevId 同族，整族移
W2-c-1a 第二笔统一交付。） -/

/-! ## §C 独立小件 -/

/-! （size_flatten_le 移 W2-c-1a 第二笔。） -/

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.indexfCompl
#print axioms Kepler.Text.Reduction5.betwnMem
#print axioms Kepler.Text.Reduction5.sizeBetwn
