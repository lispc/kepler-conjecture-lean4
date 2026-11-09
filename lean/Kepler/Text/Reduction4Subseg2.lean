/-
  Kepler.Text.Reduction4Subseg2 — J 战役 J1 板 B5-A 第二半（reduction4.hl 自由件 ⑤–⑥）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/reduction4.hl`）──
  │ :2671 `next_el_subseg` → nextEl_subseg
  │ :2138 `indexf_subseg`  → indexf_subseg
  │ ④ :2746 `mem_ifbetwn` 已于 `3b2f8f40` 前批落库（Reduction4.lean:621
  │   `memOfMemIfbetwn`，标准三）⇒ 本文件不重定义，只引用（见 §0 注）。
  │ 依赖载体：`nextEl` ↦ Kepler.Assembly.nextEl（GoodListDefs:44）；
  │   `indexf` ↦ Kepler.Text.Reduction5.indexf（Reduction5Base:225）；
  │   `cat` ↦ `List.append`；`EL` ↦ `List.getElem`；
  │   `uniq` ↦ `List.Nodup`；`sizel` ↦ `List.length`。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线差异（DIFFERS 记档）─────────────────────────────────────
  │ ⑤ HOL 走 `next_el_cat1`（tame_list 前缀段件）；本树无该件，改走
  │   `nextEl_eq_getD` 取模归约 + `List.idxOf_append`（t 成员必落左段）
  │   + `idxOf_getElem` 定位置。结论句逐字同形。
  │ ⑥ HOL 先证 `next_el_indexf`（indexf t[i] t[i+1] s = 1 走 next_el
  │   路线）再 `indexf_add_right`；本树无 `next_el_indexf`，改为直接
  │   展开 `indexf` 算「中段相邻步 = 1」（`indexf_adjacent`：`idxOf` 前缀
  │   位移 + 取模算术），后半仍走 `indexf_add_right`（与 HOL 同一件、
  │   同一侧条件 `1 ≤ indexf v t[i+1] s`），侧条件由 `indexf_eq_zero`
  │   + `uniqEl` + 假设 `(MEM v t → v = EL 0 t)` 反证（与 HOL :2173-:2179
  │   同路线）。结论句逐字同形。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；泛型 binder 只用
  `[DecidableEq α]`（实例烘焙纪律同 Reduction4/Reduction4Subseg）。
-/

import Kepler.Text.Reduction4Subseg

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Assembly (nextEl)
open Kepler.Text.Reduction5 (indexf)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt idxOf_getElem)
open Kepler.Text.Reduction4 (uniqEl indexf_eq_zero indexf_add_right)

/-! ## §0 前批件引用（不重定义）

④ `mem_ifbetwn`（reduction4.hl:2746）= `Kepler.Text.Reduction4.memOfMemIfbetwn`
（`3b2f8f40` 前的 B5-A 第一批落库，陈述逐字同形，零 sorry。
本文件消费侧只需 import 链；此处仅记录归属，不重复声明。） -/

/-! ## §1 ⑤ `next_el_subseg`（reduction4.hl:2671） -/

/-- **HOL `next_el_subseg`**（reduction4.hl:2671）：
`s = cat t b`、`uniq t`、`SUC i < sizel t`
⇒ `next_el s (EL i t) = EL (SUC i) t`。

路线：`nextEl_eq_getD` 把环上后继折成 `getD`，`t` 的成员必落在 `t ++ b`
左段（`List.idxOf_append` + `if_pos`），`Nodup t` 下 `idxOf` 定位置
（`idxOf_getElem`），模数 `(i+1) % (t++b).length = i+1` 由
`i+1 < t.length ≤ (t++b).length` 给出，最后 `getElem_append_left` 收口。 -/
theorem nextEl_subseg {α : Type*} [DecidableEq α] {s t b : List α} {i : ℕ}
    (hs : s = t ++ b) (hnd : t.Nodup) (hi : i + 1 < t.length) :
    nextEl s (t[i]'(by omega)) = t[i + 1]'hi := by
  subst hs
  have hi' : i < t.length := by omega
  have hmem : t[i]'(by omega) ∈ t ++ b :=
    List.mem_append_left _ (List.getElem_mem hi')
  have hidx : (t ++ b).idxOf (t[i]'(by omega)) = i := by
    rw [List.idxOf_append, if_pos (List.getElem_mem hi'), idxOf_getElem hnd hi']
  rw [nextEl_eq_getD hmem, hidx]
  have hmod : (i + 1) % (t ++ b).length = i + 1 := by
    rw [Nat.mod_eq_of_lt (show i + 1 < (t ++ b).length by
      rw [List.length_append]; omega)]
  rw [hmod, getD_eq_getElem_of_lt (show i + 1 < (t ++ b).length by
    rw [List.length_append]; omega)]
  exact List.getElem_append_left (as := t) (bs := b) (i := i + 1) (by omega)

/-! ## §2 ⑥ `indexf_subseg`（reduction4.hl:2138） -/

section IndexfSubseg

variable {α : Type*} [DecidableEq α]

/-- 三段拼接的中段取值定位置：`((a ++ t) ++ b).idxOf t[j] = a.length + j`
（`Nodup` 给出 `t` 与 `a` 的互斥，故 `idxOf` 走「不在左段」支，再落中段
内部位置 `j`）。 -/
private theorem idxOf_cat_cat {a t b : List α} (hnd : ((a ++ t) ++ b).Nodup)
    {j : ℕ} (hj : j < t.length) :
    ((a ++ t) ++ b).idxOf (t[j]'hj) = a.length + j := by
  obtain ⟨hnd_at, _, _⟩ := List.nodup_append.mp hnd
  obtain ⟨_, hnd_t, hdisj⟩ := List.nodup_append.mp hnd_at
  have hmem_t : t[j]'hj ∈ t := List.getElem_mem hj
  have hmem_at : t[j]'hj ∈ a ++ t := List.mem_append_right _ hmem_t
  have hnot_a : t[j]'hj ∉ a := fun h => hdisj _ h _ hmem_t rfl
  rw [List.idxOf_append, if_pos hmem_at, List.idxOf_append, if_neg hnot_a,
    idxOf_getElem hnd_t hj]
  omega

/-- 环内相邻一步：`indexf t[i] t[i+1] ((a++t)++b) = 1`
（`idxOf` 位置差恰为 1 ⇒ 环上距离恰 1；HOL `next_el_indexf` 在本树的
直接算术对应件）。 -/
private theorem indexf_adjacent {a t b : List α} (hnd : ((a ++ t) ++ b).Nodup)
    {i : ℕ} (hi : i + 1 < t.length) :
    indexf (t[i]'(by omega)) (t[i + 1]'hi) ((a ++ t) ++ b) = 1 := by
  have hi' : i < t.length := by omega
  have hmem_i : t[i]'(by omega) ∈ ((a ++ t) ++ b) :=
    List.mem_append_left _ (List.mem_append_right _ (List.getElem_mem hi'))
  have hmem_s : t[i + 1]'hi ∈ ((a ++ t) ++ b) :=
    List.mem_append_left _ (List.mem_append_right _ (List.getElem_mem hi))
  have hidx_i := idxOf_cat_cat hnd hi'
  have hidx_s := idxOf_cat_cat hnd hi
  have hslen : ((a ++ t) ++ b).length = a.length + t.length + b.length := by
    rw [List.length_append, List.length_append]
  unfold indexf
  rw [if_pos ⟨hmem_i, hmem_s⟩, hidx_s, hidx_i]
  have harith : a.length + (i + 1) + (((a ++ t) ++ b).length - (a.length + i)) =
      1 + ((a ++ t) ++ b).length := by
    rw [hslen]; omega
  rw [harith, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by rw [hslen]; omega)

/-- **HOL `indexf_subseg`**（reduction4.hl:2138）：
`s = cat (cat a t) b`、`(MEM v t → v = EL 0 t)`、`uniq s`、`MEM v s`、
`SUC i < sizel t` ⇒ `SUC (indexf v (EL i t) s) = indexf v (EL (SUC i) t) s`。

路线（与 HOL 同构）：取 `x = v`、`y = EL i t`、`z = EL (SUC i) t`，
`indexf_add_right` 化目标为 `indexf y z s = 1 ≤ indexf x z s`；前半由
`indexf_adjacent` 给出 `= 1`，后半 `1 ≤ indexf v z s` 即
`indexf v z s ≠ 0`，若为 0 则 `indexf_eq_zero` 得 `v = z`，由
`(MEM v t → v = EL 0 t)` 与 `uniqEl`（`EL (SUC i) t ≠ EL 0 t`）矛盾。 -/
theorem indexf_subseg {v : α} {s t a b : List α} {i : ℕ}
    (hs : s = (a ++ t) ++ b) (hnd : s.Nodup) (hi : i + 1 < t.length)
    (hv0 : v ∈ t → v = t[0]'(by omega)) (hv : v ∈ s) :
    indexf v (t[i]'(by omega)) s + 1 = indexf v (t[i + 1]'hi) s := by
  subst hs
  have hi' : i < t.length := by omega
  have hmem_i : t[i]'(by omega) ∈ ((a ++ t) ++ b) :=
    List.mem_append_left _ (List.mem_append_right _ (List.getElem_mem hi'))
  have hmem_s : t[i + 1]'hi ∈ ((a ++ t) ++ b) :=
    List.mem_append_left _ (List.mem_append_right _ (List.getElem_mem hi))
  have hnd_t : t.Nodup := by
    have h1 := (List.nodup_append.mp hnd).1
    exact (List.nodup_append.mp h1).2.1
  have h1 : indexf (t[i]'(by omega)) (t[i + 1]'hi) ((a ++ t) ++ b) = 1 :=
    indexf_adjacent hnd hi
  have hne : indexf v (t[i + 1]'hi) ((a ++ t) ++ b) ≠ 0 := by
    intro h0
    have hveq : v = t[i + 1]'hi := indexf_eq_zero hv hmem_s h0
    have hvt : v ∈ t := hveq ▸ List.getElem_mem hi
    have hvt0 : v = t[0]'(by omega) := hv0 hvt
    have heq : t[i + 1]'hi = t[0]'(by omega) := by rw [← hveq, hvt0]
    exact (uniqEl hnd_t (s := t) (i := i + 1) (j := 0) hi (by omega)
      (by omega)) heq
  have hle : indexf (t[i]'(by omega)) (t[i + 1]'hi) ((a ++ t) ++ b) ≤
      indexf v (t[i + 1]'hi) ((a ++ t) ++ b) := by
    rw [h1]; omega
  have hsum := indexf_add_right (s := (a ++ t) ++ b) (x := v)
    (y := t[i]'(by omega)) (z := t[i + 1]'hi) hv hmem_i hmem_s hle
  calc indexf v (t[i]'(by omega)) ((a ++ t) ++ b) + 1
      = indexf v (t[i]'(by omega)) ((a ++ t) ++ b) +
        indexf (t[i]'(by omega)) (t[i + 1]'hi) ((a ++ t) ++ b) := by rw [h1]
    _ = indexf v (t[i + 1]'hi) ((a ++ t) ++ b) := hsum

end IndexfSubseg

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（本文件编译即执行；预期 ≤ 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.Reduction4Idx.nextEl_subseg
#print axioms Kepler.Text.Reduction4Idx.indexf_subseg
