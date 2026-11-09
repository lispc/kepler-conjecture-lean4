/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12C — AQ12 叶 W2-i（decls 9–15）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:409-:611
  ┌──────────────────────────────────────────────────────────────┐
  │ decl 9  `next_eq_power_betwn_2list`   :409（34）               │
  │ decl 10 `indexf_eq_power_betwn_2list` :443（26）               │
  │ decl 11 `uniq_flatten_betwn`          :469（24）               │
  │ decl 12 `next_power_flatten_eq`       :493（34）               │
  │ decl 13 `sizel_le_indexf_not_mem`     :527（34）               │
  │ decl 14 `sizel_mem_le_flatten`        :561（11）               │
  │ decl 15 `indexf_HD_LAST_sizel_flatten`:572（40）               │
  └──────────────────────────────────────────────────────────────┘
  （W2-ii = decls 16–21，:612-:865，另交。）

  ┌─ 桥件（清单 §2.2 的 4 条零命中中的 3 条，本批一并落地）──────────
  │ `aqs_indexfIndexlHd`  = HOL `Ohcgkfu.indexf_indexl_hd`（OHCGKFU:28）
  │ `aqs_idxOfGetLast`    = HOL `Tame_list.indexl_LAST`（tame_list:5605）
  │ `aqs_sizel0NotNil`    = HOL `Pwssrat.sizel0_not_nil`（PWSSRAT:92）
  │ `aqs_headMem`/`aqs_getLastMem` = HOL `MEM_HD`/`MEM_LAST` 的非空形
  │ `next_el_flatten_unlast` 已在库（`nextElFlattenUnlast`，TameList9:644），不重落。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线勘误（相对清单）────────────────────────────────────────
  │ ① decl 11 `uniq_flatten_betwn`：HOL 走 `Aq1.all_uniq_flatten`（该件
  │   仍是零命中）；本树 core 有更强的 `List.nodup_flatten`（↔ 逐项 Nodup
  │   ∧ Pairwise Disjoint），故**不需要**移植 `all_uniq_flatten`，
  │   直接用它 + `uniqSublistUnique` 收口（省一件 ~25 行）。
  │ ② decl 12/15 的「walk 到 LAST」在 HOL 用 `indexl_LAST` +
  │   `indexf_indexl_hd` + `next_eln_indexf` 三件拼；Lean 同一组桥件
  │   （`aqs_idxOfGetLast`/`aqs_indexfIndexlHd`）直取。
  └────────────────────────────────────────────────────────────────

  载体折算：`HD`/`LAST` ↦ `head!`/`getLast!`（HOL total 版；各件均带
  非空前提）；`sizel` ↦ `List.length`；`flatten` ↦ `List.flatten`；
  `indexl` ↦ `List.idxOf`；`POWER n` ↦ `Function.iterate`。
  decls 9/10 保持 HOL 的泛型 α；decls 11–15 按本树 TameSpine 约定固定在
  `List (ℕ × ℕ)`（与 `nextElFlattenUnlast` 等既有件的载体一致）。

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList50
import Kepler.Text.TameSpine.JcajyduBetwnBase

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl)
open Kepler.Graphs (between)

/-! ## §0 桥件（MEM_HD / MEM_LAST / sizel0_not_nil / indexf_indexl_hd / indexl_LAST） -/

/-- `MEM_HD` 的非空形：`s ≠ [] ⇒ head! s ∈ s`。 -/
theorem aqs_headMem {α : Type*} [Inhabited α] {s : List α} (hne : s ≠ []) : s.head! ∈ s := by
  cases s with
  | nil => exact absurd rfl hne
  | cons a t => exact List.mem_cons_self

/-- `MEM_LAST` 的非空形：`s ≠ [] ⇒ getLast! s ∈ s`。 -/
theorem aqs_getLastMem {α : Type*} [Inhabited α] {s : List α} (hne : s ≠ []) :
    s.getLast! ∈ s := by
  rw [getLast!EqGetLast hne]
  exact List.getLast_mem hne

/-- **HOL `Pwssrat.sizel0_not_nil`**（PWSSRAT.hl:92）：`s ≠ [] ↔ 0 < sizel s`。 -/
theorem aqs_sizel0NotNil {α : Type*} {s : List α} : s ≠ [] ↔ 0 < s.length :=
  List.length_pos_iff.symm

/-- **HOL `Ohcgkfu.indexf_indexl_hd`**（OHCGKFU.hl:28）：
`indexf (HD s) y s = indexl y s`（头元素位置为 0）。 -/
theorem aqs_indexfIndexlHd {α : Type*} [BEq α] [LawfulBEq α] [Inhabited α] (s : List α) (y : α) :
    indexf s.head! y s = s.idxOf y := by
  cases s with
  | nil => simp [indexf]
  | cons a t =>
    rw [List.head!_cons]
    unfold indexf
    by_cases hy : y ∈ a :: t
    · rw [if_pos ⟨List.mem_cons_self, hy⟩, List.idxOf_cons_self]
      have hi : (a :: t).idxOf y < (a :: t).length := List.idxOf_lt_length_iff.mpr hy
      rw [Nat.sub_zero, Nat.add_comm, Nat.add_mod_left, Nat.mod_eq_of_lt hi]
    · rw [if_neg (fun h => hy h.2)]
      exact (List.idxOf_eq_length hy).symm

/-- **HOL `Tame_list.indexl_LAST`**（tame_list.hl:5605）：
`uniq s ∧ s ≠ [] ⇒ indexl (LAST s) s = sizel s - 1`。 -/
theorem aqs_idxOfGetLast {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] [Inhabited α]
    {s : List α} (hnd : s.Nodup) (hne : s ≠ []) :
    s.idxOf s.getLast! = s.length - 1 := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  rw [getLast!EqGetLast hne, List.getLast_eq_getElem hne]
  exact Kepler.Text.TameLp.idxOf_getElem hnd (by omega)

/-! ## §1 HOL AQ12.hl:409 `next_eq_power_betwn_2list` -/

/-- **HOL `next_eq_power_betwn_2list`**（AQ12.hl:409-:442）：
两条 Nodup 表 `s`/`r`，`z = LAST s`，且除 `z` 外表内逐点后继一致 ⇒ 从 `HD s`
起的 `n < |s|` 步迭代两边相同。HOL 的 `d = z` 支用 indexf 计数排除
（`indexf (HD s) z s = n` 与 `= |s| - 1` 在 `n+1 < |s|` 下矛盾）。 -/
theorem aqs_nextEqPowerBetwn2list {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    [Inhabited α] {s r : List α} {z : α} (hs : s.Nodup) (hr : r.Nodup) (hz : z ∈ s)
    (hlast : s.getLast! = z) (hnext : ∀ x ∈ s, x ≠ z → nextEl s x = nextEl r x) :
    ∀ n : ℕ, n < s.length → (nextEl s)^[n] s.head! = (nextEl r)^[n] s.head! := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hlt
    have hlt' : n < s.length := by omega
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hlt']
    have hne : s ≠ [] := List.ne_nil_of_mem hz
    have hhd : s.head! ∈ s := aqs_headMem hne
    have hmem : (nextEl r)^[n] s.head! ∈ s := ih hlt' ▸ memPowerNextEl hhd n
    by_cases hdz : (nextEl r)^[n] s.head! = z
    · -- `d = z`：indexf 计数矛盾（n = |s|-1 与 n+1 < |s|）
      exfalso
      have hsd : (nextEl s)^[n] s.head! = z := (ih hlt').trans hdz
      have h1 : indexf s.head! z s = n := nextElnIndexf hhd hz hs hsd hlt'
      have h2 : indexf s.head! z s = s.length - 1 := by
        rw [aqs_indexfIndexlHd, ← hlast, aqs_idxOfGetLast hs hne]
      omega
    · exact hnext _ hmem hdz

/-! ## §2 HOL AQ12.hl:443 `indexf_eq_power_betwn_2list` -/

/-- **HOL `indexf_eq_power_betwn_2list`**（AQ12.hl:443-:468）：
`MEM s ⊆ MEM r` 时 `indexf (HD s) x r = indexf (HD s) x s`——decl 9 的幂等式
给出 `(next_el r)^i (HD s) = x`（`i = indexf (HD s) x s`），再在 r 侧
`next_eln_indexf` 收口（界 `i < |s| ≤ |r|`）。 -/
theorem aqs_indexfEqPowerBetwn2list {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    [Inhabited α] {s r : List α} {z : α} (hsub : ∀ x ∈ s, x ∈ r) (hs : s.Nodup)
    (hr : r.Nodup) (hz : z ∈ s) (hlast : s.getLast! = z)
    (hnext : ∀ x ∈ s, x ≠ z → nextEl s x = nextEl r x) :
    ∀ x ∈ s, indexf s.head! x r = indexf s.head! x s := by
  intro x hx
  have hne : s ≠ [] := List.ne_nil_of_mem hz
  have hhd : s.head! ∈ s := aqs_headMem hne
  have hlt : indexf s.head! x s < s.length := indexfLtSizel hhd hx
  have hpow := aqs_nextEqPowerBetwn2list hs hr hz hlast hnext
    (indexf s.head! x s) hlt
  have hiter : (nextEl s)^[indexf s.head! x s] s.head! = x := indexfN hhd hx hs
  have hr_iter : (nextEl r)^[indexf s.head! x s] s.head! = x := by
    rw [← hpow]
    exact hiter
  have hlen : s.length ≤ r.length := (hs.subperm hsub).length_le
  have hmlt : indexf s.head! x s < r.length := lt_of_lt_of_le hlt hlen
  exact nextElnIndexf (hsub _ hhd) (hsub x hx) hr hr_iter hmlt

/-! ## §3 HOL AQ12.hl:469 `uniq_flatten_betwn` -/

/-- 通用辅件：`flat` 的每个成员都来自 `bars` 且 `bars` 逐项 Nodup 且两两不交 ⇒
`bars.flatten.Nodup`（本批 decl 11 的内核）。 -/
private theorem pairwiseDisjointOfMemNodup {α : Type*} {bars : List (List α)}
    {l : List (List α)} (hflat : bars.flatten.Nodup) (hl : l.Nodup)
    (hsub : ∀ a ∈ l, a ∈ bars) : l.Pairwise List.Disjoint := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    rw [List.pairwise_cons]
    refine ⟨fun b hb => ?_, ih hl.2 (fun x hx => hsub x (List.mem_cons_of_mem _ hx))⟩
    have hne : a ≠ b := fun h => hl.1 (h ▸ hb)
    rw [List.disjoint_left]
    intro x hx hxb
    exact hne (uniqSublistUnique bars hflat a (hsub a List.mem_cons_self) b
      (hsub b (List.mem_cons_of_mem _ hb)) ⟨x, hx, hxb⟩)

/-- **HOL `uniq_flatten_betwn`**（AQ12.hl:469-:492）：
`uniq (flatten r) ∧ y,z ∈ r ∧ y ≠ z ∧ all nonempty r ⇒ uniq (flatten (betwn r y z))`。
HOL 走 `Aq1.all_uniq_flatten`；Lean 直接用 core `List.nodup_flatten`
（逐项 Nodup + Pairwise Disjoint 两合取）。 -/
theorem aqs_uniqFlattenBetwn {α : Type*} [BEq α] [LawfulBEq α]
    {r : List (List α)} {y z : List α} (hflat : r.flatten.Nodup) (hy : y ∈ r)
    (hz : z ∈ r) (hyz : y ≠ z) (hall : ∀ l ∈ r, l ≠ []) :
    (between r y z).flatten.Nodup := by
  have hnd : r.Nodup := uniqFlatten (L := r) hflat hall
  have hbn : (between r y z).Nodup :=
    uniqBetwn (z := y) (y := z) hnd hy hz hyz
  rw [List.nodup_flatten]
  exact ⟨fun l hl => uniqFlattenUniq r hflat l (betwnMem hl),
    pairwiseDisjointOfMemNodup hflat hbn (fun l hl => betwnMem hl)⟩

/-! ## §4 HOL AQ12.hl:493 `next_power_flatten_eq` -/

/-- **HOL `next_power_flatten_eq`**（AQ12.hl:493-:526）：
`uniq (flatten r) ∧ all nonempty r ∧ v ∈ r ∧ n ≤ |v| - 1 ⇒
(next_el (flatten r))^n (HD v) = (next_el v)^n (HD v)`。
归纳步的支点：`(next_el v)^n (HD v) ≠ LAST v`（否则 indexf 计数把 n 逼成
`|v| - 1`，与 `SUC n ≤ |v| - 1` 矛盾），从而可用 `next_el_flatten_unlast`。 -/
theorem aqs_nextPowerFlattenEq {r : List (List (ℕ × ℕ))} {v : List (ℕ × ℕ)}
    (hflat : r.flatten.Nodup) (hall : ∀ l ∈ r, l ≠ []) (hv : v ∈ r) :
    ∀ n : ℕ, n ≤ v.length - 1 →
      (nextEl r.flatten)^[n] v.head! = (nextEl v)^[n] v.head! := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hle
    have hle' : n ≤ v.length - 1 := by omega
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hle']
    have hvne : v ≠ [] := hall v hv
    have hnd : v.Nodup := uniqFlattenUniq r hflat v hv
    have hd : (nextEl v)^[n] v.head! ∈ v := memPowerNextEl (aqs_headMem hvne) n
    have hdne : (nextEl v)^[n] v.head! ≠ v.getLast! := by
      intro hcon
      exfalso
      have h1 : indexf v.head! v.getLast! v = n :=
        nextElnIndexf (aqs_headMem hvne) (aqs_getLastMem hvne) hnd hcon (by omega)
      have h2 : indexf v.head! v.getLast! v = v.length - 1 := by
        rw [aqs_indexfIndexlHd, aqs_idxOfGetLast hnd hvne]
      omega
    exact nextElFlattenUnlast hflat hd hv hdne

/-! ## §5 HOL AQ12.hl:527 `sizel_le_indexf_not_mem` -/

/-- **HOL `sizel_le_indexf_not_mem`**（AQ12.hl:527-:560）：
`z ∉ v` 时 `|v| ≤ indexf (HD v) z (flatten r)`。反支（`indexf < |v|`）由
decl 12 把 `(next_el (flatten r))^i (HD v) = z` 降到 `(next_el v)^i (HD v) = z`，
与 `z ∉ v` 矛盾。 -/
theorem aqs_sizelLeIndexfNotMem {r : List (List (ℕ × ℕ))} {v : List (ℕ × ℕ)}
    {z : ℕ × ℕ} (hflat : r.flatten.Nodup) (hzv : z ∉ v) (hv : v ∈ r)
    (hall : ∀ l ∈ r, l ≠ []) (hz : z ∈ r.flatten) :
    v.length ≤ indexf v.head! z r.flatten := by
  rcases Nat.lt_or_ge (indexf v.head! z r.flatten) v.length with h | h
  · exfalso
    have hle : indexf v.head! z r.flatten ≤ v.length - 1 := by omega
    have hvne : v ≠ [] := hall v hv
    have hhmem : v.head! ∈ v := aqs_headMem hvne
    have hhmemF : v.head! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hhmem⟩
    have hstep : (nextEl r.flatten)^[indexf v.head! z r.flatten] v.head! = z :=
      indexfN hhmemF hz hflat
    have hpow := aqs_nextPowerFlattenEq hflat hall hv
      (indexf v.head! z r.flatten) hle
    have hvz : (nextEl v)^[indexf v.head! z r.flatten] v.head! = z := by
      rw [← hpow]
      exact hstep
    exact hzv (hvz ▸ memPowerNextEl hhmem _)
  · exact h

/-! ## §6 HOL AQ12.hl:561 `sizel_mem_le_flatten` -/

/-- **HOL `sizel_mem_le_flatten`**（AQ12.hl:561-:571）：`v ∈ r ⇒ |v| ≤ |flatten r|`。 -/
theorem aqs_sizelMemLeFlatten {α : Type*} {r : List (List α)} {v : List α}
    (hv : v ∈ r) : v.length ≤ r.flatten.length := by
  rw [List.length_flatten]
  induction r with
  | nil => simp at hv
  | cons a t ih =>
    rw [List.mem_cons] at hv
    rcases hv with rfl | hvt
    · simp
    · have := ih hvt
      simp only [List.map_cons, List.sum_cons]
      omega

/-! ## §7 HOL AQ12.hl:572 `indexf_HD_LAST_sizel_flatten` -/

/-- **HOL `indexf_HD_LAST_sizel_flatten`**（AQ12.hl:572-:611）：
`indexf (HD v) (LAST v) (flatten r) = |v| - 1`——从 `HD v` 沿 flatten 的后继走
`|v| - 1` 步正好到 `LAST v`（decl 12 + v 内 walk + `next_eln_indexf`）。 -/
theorem aqs_indexfHdLastSizelFlatten {r : List (List (ℕ × ℕ))} {v : List (ℕ × ℕ)}
    (hflat : r.flatten.Nodup) (hall : ∀ l ∈ r, l ≠ []) (hv : v ∈ r) :
    indexf v.head! v.getLast! r.flatten = v.length - 1 := by
  have hvne : v ≠ [] := hall v hv
  have hnd : v.Nodup := uniqFlattenUniq r hflat v hv
  have hhmem : v.head! ∈ v := aqs_headMem hvne
  have hlmem : v.getLast! ∈ v := aqs_getLastMem hvne
  have hhmemF : v.head! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hhmem⟩
  have hlmemF : v.getLast! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hlmem⟩
  have hidx : indexf v.head! v.getLast! v = v.length - 1 := by
    rw [aqs_indexfIndexlHd, aqs_idxOfGetLast hnd hvne]
  have hwalk : (nextEl v)^[v.length - 1] v.head! = v.getLast! := by
    have h := indexfN hhmem hlmem hnd
    rwa [hidx] at h
  have hval : (nextEl r.flatten)^[v.length - 1] v.head! = v.getLast! :=
    (aqs_nextPowerFlattenEq hflat hall hv (v.length - 1) (le_refl _)).trans hwalk
  have hmlt : v.length - 1 < r.flatten.length := by
    have h1 : v.length ≤ r.flatten.length := aqs_sizelMemLeFlatten hv
    have h2 : 0 < v.length := List.length_pos_of_ne_nil hvne
    omega
  exact nextElnIndexf hhmemF hlmemF hflat hval hmlt

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_headMem
#print axioms Kepler.Text.TameSpine.aqs_getLastMem
#print axioms Kepler.Text.TameSpine.aqs_sizel0NotNil
#print axioms Kepler.Text.TameSpine.aqs_indexfIndexlHd
#print axioms Kepler.Text.TameSpine.aqs_idxOfGetLast
#print axioms Kepler.Text.TameSpine.aqs_nextEqPowerBetwn2list
#print axioms Kepler.Text.TameSpine.aqs_indexfEqPowerBetwn2list
#print axioms Kepler.Text.TameSpine.aqs_uniqFlattenBetwn
#print axioms Kepler.Text.TameSpine.aqs_nextPowerFlattenEq
#print axioms Kepler.Text.TameSpine.aqs_sizelLeIndexfNotMem
#print axioms Kepler.Text.TameSpine.aqs_sizelMemLeFlatten
#print axioms Kepler.Text.TameSpine.aqs_indexfHdLastSizelFlatten
