/-
  Kepler.Text.Reduction4Idx — J 战役 J1 第三批（B3 首口）：
  `rot`/`flatten`/`indexl` 纯 list 层结构件（reduction4.hl rot 家族下沿四件）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）──────
  │ reduction4.hl 本地件 4 条：
  │   all_rot        :4263 → allRot
  │   flatten_rot1   :3969 → flattenRot1
  │   flatten_rot    :3980 → flattenRot
  │   flatten_indexl :4227 → flattenIndexl
  │ 四件是全文件 rot 家族的最底自含层（零 J2/J3 依赖）；上游/下游：
  │   flatten_rot1 ← rot1_cons（Mathlib rotate_cons_succ）✓ 已消费
  │   flatten_rot  ← flatten_rot1 ✓ 本文件
  │   flatten_indexl ← indexl/flatten/uniq 核心件 ✓ 本文件
  │   rot_parts（:4004）/ flatten_indexf（:4271）/ indexf_map_uniq（:4316）/
  │   mem_ifbetwn_hd/tl_extend（:4046/:4123）**本批不做**：硬依赖
  │   Reduction2.indexf_rotn_alt / Reduction3.indexl_map_uniq（J2/J3 产出）
  │   与 ifbetwn_indexf（其依赖 indexf_subseg_rot → J2）——按「先到先落」排期。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ `rot` ↦ `List.rotate`（Mathlib，`rotate_cons_succ`/`rotate_rotate`/
  │ `rotate_eq_drop_append_take`/`rotate_eq_nil_iff`/`rotate_append_length_eq`）；
  │ `flatten` ↦ `List.flatten`；`indexl` ↦ `List.idxOf`；
  │ `all P l` ↦ `∀ x ∈ l, P x`。泛型 binder 只用 `[DecidableEq α]`
  │ （rx 桥雷区记档）。零 axiom/sorry/admit/native_decide。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction4

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction4Idx

section RotFlatten

variable {α : Type*}

/-- **HOL `all_rot`**（reduction4.hl:4263）：`all P` 在旋转下不变。 -/
theorem allRot (P : α → Prop) (k : ℕ) (r : List α) :
    (∀ x ∈ r.rotate k, P x) ↔ ∀ x ∈ r, P x := by
  simp [List.mem_rotate]

/-- **HOL `flatten_rot1`**（reduction4.hl:3969）：整体旋 1 后 flatten 等于
flatten 后按首段长度旋转。 -/
theorem flattenRot1 (ss : List (List α)) (h : ss ≠ []) :
    (ss.rotate 1).flatten = ss.flatten.rotate (ss.headD []).length := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h
  have h1 : (a :: t).rotate 1 = t ++ [a] := by
    simp
  rw [h1, List.flatten_append, List.flatten_singleton, List.flatten_cons]
  simp [List.rotate_append_length_eq]

/-- **HOL `flatten_rot`**（reduction4.hl:3980）：flatten 与旋转互化（存在形）。 -/
theorem flattenRot (k : ℕ) (ss : List (List α)) :
    ∃ k', (ss.rotate k).flatten = ss.flatten.rotate k' := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨k', hk'⟩ := ih
    by_cases hnil : ss.rotate k = []
    · have hss : ss = [] := List.rotate_eq_nil_iff.mp hnil
      subst hss
      exact ⟨0, by simp⟩
    · refine ⟨k' + ((ss.rotate k).headD []).length, ?_⟩
      have hstep : ss.rotate (k + 1) = (ss.rotate k).rotate 1 := by
        rw [List.rotate_rotate]
      rw [hstep, flattenRot1 (ss.rotate k) hnil, hk', List.rotate_rotate]

end RotFlatten

section FlattenIndexl

variable {α : Type*} [DecidableEq α]

/-- **HOL `flatten_indexl`**（reduction4.hl:4227）：互异子表在 `R` 中的先后序
与元素在 `flatten R` 中的先后序一致（`Nodup (flatten R)` 下）。 -/
theorem flattenIndexl (R : List (List α)) (px py : List α) (x y : α)
    (hnil : ∀ p ∈ R, p ≠ []) (hnd : R.flatten.Nodup)
    (hpx : px ∈ R) (hpy : py ∈ R) (hx : x ∈ px) (hy : y ∈ py) (hne : px ≠ py) :
    R.idxOf px < R.idxOf py ↔ R.flatten.idxOf x < R.flatten.idxOf y := by
  induction R with
  | nil => cases hpx
  | cons h t ih =>
    rw [List.flatten_cons]
    have hnil_t : ∀ p ∈ t, p ≠ [] := fun p hp => hnil p (List.mem_cons_of_mem h hp)
    obtain ⟨hndh, hndt, hdisj⟩ :=
      List.nodup_append'.mp (by rw [List.flatten_cons] at hnd; exact hnd)
    -- py ∈ t 时 py ≠ h（h 的元素与 t.flatten 不相交，h 非空）
    have hne_h_of_mem_t : ∀ p ∈ t, p ≠ h := by
      intro p hpt hph
      obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil h (hnil h List.mem_cons_self)
      exact hdisj (a := x0) hx0 (List.mem_flatten.mpr ⟨p, hph ▸ hpt, hph.symm ▸ hx0⟩)
    rcases List.mem_cons.mp hpx with hpxh | hpxt
    · -- px = h
      rw [hpxh]
      have hx' : x ∈ h := hpxh ▸ hx
      have h1 : (h :: t).idxOf h = 0 := List.idxOf_cons_self
      rcases List.mem_cons.mp hpy with hpyh | hpyt
      · exact absurd (hpxh.trans hpyh.symm) hne
      · have hbeq : (h == py) = false :=
          beq_eq_false_iff_ne.mpr (fun hh => hne_h_of_mem_t py hpyt hh.symm)
        have h2 : (h :: t).idxOf py = t.idxOf py + 1 := by
          rw [List.idxOf_cons, hbeq, cond_false]
        have hxi : (h ++ t.flatten).idxOf x = h.idxOf x := by
          rw [List.idxOf_append, if_pos hx']
        have hyT : y ∈ t.flatten := List.mem_flatten.mpr ⟨py, hpyt, hy⟩
        have hyi : (h ++ t.flatten).idxOf y = t.flatten.idxOf y + h.length := by
          rw [List.idxOf_append, if_neg (fun hyh => hdisj (a := y) hyh hyT)]
        have hxlt : h.idxOf x < h.length := List.idxOf_lt_length_iff.mpr hx'
        rw [h1, h2, hxi, hyi]
        constructor <;> intro _ <;> omega
    · rcases List.mem_cons.mp hpy with hpyh | hpyt
      · -- py = h
        rw [hpyh]
        have hy' : y ∈ h := hpyh ▸ hy
        have hbeq : (h == px) = false :=
          beq_eq_false_iff_ne.mpr (fun hh => hne_h_of_mem_t px hpxt hh.symm)
        have h1 : (h :: t).idxOf px = t.idxOf px + 1 := by
          rw [List.idxOf_cons, hbeq, cond_false]
        have hxi : (h ++ t.flatten).idxOf x = t.flatten.idxOf x + h.length := by
          have hxT : x ∈ t.flatten := List.mem_flatten.mpr ⟨px, hpxt, hx⟩
          rw [List.idxOf_append, if_neg (fun hxh => hdisj (a := x) hxh hxT)]
        have hyi : (h ++ t.flatten).idxOf y = h.idxOf y := by
          rw [List.idxOf_append, if_pos hy']
        have hylt : h.idxOf y < h.length := List.idxOf_lt_length_iff.mpr hy'
        rw [h1, List.idxOf_cons_self, hxi, hyi]
        constructor <;> intro hh <;> omega
      · -- 都在 t：归纳
        have hpxnh : px ≠ h := fun hh => hne_h_of_mem_t px hpxt hh
        have hpynh : py ≠ h := fun hh => hne_h_of_mem_t py hpyt hh
        have hbeq1 : (h == px) = false :=
          beq_eq_false_iff_ne.mpr (fun hh => hpxnh hh.symm)
        have h1 : (h :: t).idxOf px = t.idxOf px + 1 := by
          rw [List.idxOf_cons, hbeq1, cond_false]
        have hbeq2 : (h == py) = false :=
          beq_eq_false_iff_ne.mpr (fun hh => hpynh hh.symm)
        have h2 : (h :: t).idxOf py = t.idxOf py + 1 := by
          rw [List.idxOf_cons, hbeq2, cond_false]
        have hxT : x ∈ t.flatten := List.mem_flatten.mpr ⟨px, hpxt, hx⟩
        have hyT : y ∈ t.flatten := List.mem_flatten.mpr ⟨py, hpyt, hy⟩
        have hxi : (h ++ t.flatten).idxOf x = t.flatten.idxOf x + h.length := by
          rw [List.idxOf_append, if_neg (fun hxh => hdisj (a := x) hxh hxT)]
        have hyi : (h ++ t.flatten).idxOf y = t.flatten.idxOf y + h.length := by
          rw [List.idxOf_append, if_neg (fun hyh => hdisj (a := y) hyh hyT)]
        rw [h1, h2, hxi, hyi, Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_right]
        exact ih hnil_t hndt hpxt hpyt

end FlattenIndexl

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（本文件编译即执行；预期 = 标准三
`[propext, Classical.choice, Quot.sound]`，零 sorryAx。） -/
#print axioms Kepler.Text.Reduction4Idx.allRot
#print axioms Kepler.Text.Reduction4Idx.flattenRot1
#print axioms Kepler.Text.Reduction4Idx.flattenRot
#print axioms Kepler.Text.Reduction4Idx.flattenIndexl
