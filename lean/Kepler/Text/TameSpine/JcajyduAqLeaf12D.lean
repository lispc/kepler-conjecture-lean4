/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12D — AQ12 叶 W2-ii（decls 16–21）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:612-:865
  ┌──────────────────────────────────────────────────────────────┐
  │ decl 16 `indexf_split_flatten`        :612（52）               │
  │ decl 17 `indexf_split_LAST_flatten`   :664（51）               │
  │ decl 18 `sizel_le_indexf_not_mem_last`:715（47）               │
  │ decl 19 `indexf_split_flatten_right`  :762（61）               │
  │ decl 20 `mem_mem_flatten`             :823（8）                │
  │ decl 21 `indexf_split_HD_flatten`     :831（35）               │
  └──────────────────────────────────────────────────────────────┘

  ┌─ 路线（HOL 的 indexf_add_left/right 链，Lean 逐条对应）──────────
  │ 记 `I_x_y_S = indexf x y S`、`H = HD v`、`L = LAST v`、`W = prev_el r v`。
  │ decl 16：`I_H_z_F = I_H_L_F + I_{HD(next v)}_z_F + 1`
  │   由 `I_H_L_F = |v|-1`（decl 15）+ `I_H_z_F ≥ |v|`（decl 13）
  │   + `indexf_add_left`（H,L,z）+ `next_el_flatten_last` 桥到下一 parts 的
  │   `HD`（`nextElFlattenLast`）+ `next_el_indexf`（相隔 1）。
  │ decl 17：目标 `I_y_z_F = I_y_L_v + I_{HD next}_z_F + 1`；
  │   `I_H_y_F = idxOf y v`（`indexf_flatten` + `indexf_indexl_hd`）、
  │   `I_H_y_v + I_y_L_v = |v|-1`（`indexf_add_left` on v）。
  │ decl 18：反支 `I_z_L_F ≤ |v|-1` 由 `indexf_add_right`（H,z,L）把
  │   `I_H_z_F` 压到 `≤ |v|-1`，与 decl 13 的 `|v| ≤ I_H_z_F` 矛盾。
  │   （HOL 在此处还挂了 `next_power_flatten_eq` 一串；实测该支直接矛盾，
  │    不需要——已在 DELIVERY 记路线勘误。）
  │ decl 19：`I_z_L_F = I_z_LW_F + I_H_L_v + 1`（prev_el 桥 + z→H 正性）。
  │ decl 21：`I_y_z_F = I_y_LW_F + I_H_z_v + 1`（decl 19 at y + indexf_flatten）。
  └────────────────────────────────────────────────────────────────

  ┌─ 复用与查重 ─────────────────────────────────────────────────
  │ · `indexf_flatten` 已在库（`indexfFlatten`）；`next_el_flatten_last`
  │   已在库（`nextElFlattenLast`）；`prev_el` 反演 `nextElPrevElUniq`
  │   已在库（JcajyduRed2Trans:94）。
  │ · `mem_mem_flatten`（decl 20）：查重后**无既有覆盖**（无 `memMemFlatten`
  │   /`memFlatten` 类声明；负探针亦无），本批按 2 行落地（`List.mem_flatten`）。
  │ · decl 15/13/16/18/19 均为本 W2 前批与批内件，链式依赖见上。
  └────────────────────────────────────────────────────────────────

  载体：全部固定 `List (List (ℕ × ℕ))`（与 W2-i、`nextElFlattenLast` 等既有件一致）。
  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12C
import Kepler.Text.TameSpine.JcajyduRed2Trans

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (between)

/-! ## §0 辅件：头元素位置为 0 / decl 20 `mem_mem_flatten` -/

/-- `idxOf` 在 `head!` 处为 0（`indexf_indexl_hd` 与 `indexf_flatten` 的桥）。 -/
theorem aqs_idxOfHead {α : Type*} [BEq α] [LawfulBEq α] [Inhabited α] (s : List α) :
    s.idxOf s.head! = 0 := by
  cases s with
  | nil => simp
  | cons a t => exact List.idxOf_cons_self

/-- **HOL `mem_mem_flatten`**（AQ12.hl:823-:830）：`y ∈ v ∧ v ∈ r ⇒ y ∈ flatten r`。
（查重：本树无既有覆盖；`List.mem_flatten` 两行落地。） -/
theorem aqs_memMemFlatten {α : Type*} {r : List (List α)} {v : List α} {y : α}
    (hy : y ∈ v) (hv : v ∈ r) : y ∈ r.flatten :=
  List.mem_flatten.mpr ⟨v, hv, hy⟩

/-! ## §1 HOL AQ12.hl:612 `indexf_split_flatten` -/

/-- **HOL `indexf_split_flatten`**（AQ12.hl:612-:663）：
`I(HD v, z, flatten r) = I(HD v, LAST v, v) + I(HD (next v), z, flatten r) + 1`。 -/
theorem aqs_indexfSplitFlatten {r : List (List (ℕ × ℕ))} {v : List (ℕ × ℕ)} {z : ℕ × ℕ}
    (hflat : r.flatten.Nodup) (hzv : z ∉ v) (hv : v ∈ r) (hall : ∀ l ∈ r, l ≠ [])
    (hz : z ∈ r.flatten) :
    indexf v.head! z r.flatten
      = indexf v.head! v.getLast! v + indexf (nextEl r v).head! z r.flatten + 1 := by
  have hvne : v ≠ [] := hall v hv
  have hnd : v.Nodup := uniqFlattenUniq r hflat v hv
  have hpos : 0 < v.length := List.length_pos_of_ne_nil hvne
  have hh : v.head! ∈ v := aqs_headMem hvne
  have hl : v.getLast! ∈ v := aqs_getLastMem hvne
  have hhF : v.head! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hh⟩
  have hlF : v.getLast! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hl⟩
  have h15 : indexf v.head! v.getLast! r.flatten = v.length - 1 :=
    aqs_indexfHdLastSizelFlatten hflat hall hv
  have h13 : v.length ≤ indexf v.head! z r.flatten :=
    aqs_sizelLeIndexfNotMem hflat hzv hv hall hz
  have hV : indexf v.head! v.getLast! v = v.length - 1 := by
    rw [aqs_indexfIndexlHd, aqs_idxOfGetLast hnd hvne]
  -- (a) HD → LAST → z（flatten 上）
  have hA : indexf v.head! v.getLast! r.flatten + indexf v.getLast! z r.flatten
      = indexf v.head! z r.flatten :=
    indexfAddLeft hhF hlF hz (by omega)
  -- (b) LAST v 的后继是下一 parts 的 HD
  have hstep : nextEl r.flatten v.getLast! = (nextEl r v).head! :=
    nextElFlattenLast hflat hall hv
  have hnextv : nextEl r v ∈ r := Kepler.Text.TameLp.nextEl_mem_of_mem hv
  have hnextne : nextEl r v ≠ [] := hall _ hnextv
  have hnextF : (nextEl r v).head! ∈ r.flatten :=
    List.mem_flatten.mpr ⟨nextEl r v, hnextv, aqs_headMem hnextne⟩
  have hlt2 : 1 < r.flatten.length := by
    have hlt := indexfLtSizel hhF hz
    omega
  have hstepIdx : indexf v.getLast! (nextEl r v).head! r.flatten = 1 :=
    nextElIndexf hlF hnextF hflat hstep hlt2
  have hpos2 : 1 ≤ indexf v.getLast! z r.flatten := by
    rcases Nat.eq_zero_or_pos (indexf v.getLast! z r.flatten) with h0 | h
    · exfalso
      have hzlast : v.getLast! = z := indexfZeroEq hlF hz h0
      exact hzv (hzlast ▸ hl)
    · exact h
  have hB : indexf v.getLast! (nextEl r v).head! r.flatten
      + indexf (nextEl r v).head! z r.flatten = indexf v.getLast! z r.flatten :=
    indexfAddLeft hlF hnextF hz (by rw [hstepIdx]; exact hpos2)
  omega

/-! ## §2 HOL AQ12.hl:715 `sizel_le_indexf_not_mem_last` -/

/-- **HOL `sizel_le_indexf_not_mem_last`**（AQ12.hl:715-:761）：
`z ∉ v` 时 `|v| ≤ I(z, LAST v, flatten r)`。反支由 `indexf_add_right`（H,z,L）
把 `I(H,z,F)` 压到 `≤ |v|-1`，与 decl 13 矛盾（比 HOL 少一串
`next_power_flatten_eq` 消费，HOL 该串在该支其实不必要）。 -/
theorem aqs_sizelLeIndexfNotMemLast {r : List (List (ℕ × ℕ))} {v : List (ℕ × ℕ)}
    {z : ℕ × ℕ} (hflat : r.flatten.Nodup) (hzv : z ∉ v) (hv : v ∈ r)
    (hall : ∀ l ∈ r, l ≠ [])
    (hz : z ∈ r.flatten) : v.length ≤ indexf z v.getLast! r.flatten := by
  have hvne : v ≠ [] := hall v hv
  have hh : v.head! ∈ v := aqs_headMem hvne
  have hl : v.getLast! ∈ v := aqs_getLastMem hvne
  have hhF : v.head! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hh⟩
  have hlF : v.getLast! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hl⟩
  have h15 : indexf v.head! v.getLast! r.flatten = v.length - 1 :=
    aqs_indexfHdLastSizelFlatten hflat hall hv
  have h13 : v.length ≤ indexf v.head! z r.flatten :=
    aqs_sizelLeIndexfNotMem hflat hzv hv hall hz
  rcases Nat.lt_or_ge (indexf z v.getLast! r.flatten) v.length with hlt | hge
  · exfalso
    have hle : indexf z v.getLast! r.flatten ≤ v.length - 1 := by omega
    have hle' : indexf z v.getLast! r.flatten
        ≤ indexf v.head! v.getLast! r.flatten := by
      rw [h15]
      exact hle
    have hA : indexf v.head! z r.flatten + indexf z v.getLast! r.flatten
        = indexf v.head! v.getLast! r.flatten :=
      indexfAddRight hhF hz hlF hle'
    omega
  · exact hge

/-! ## §3 HOL AQ12.hl:664 `indexf_split_LAST_flatten` -/

/-- **HOL `indexf_split_LAST_flatten`**（AQ12.hl:664-:714）：
`I(y, z, flatten r) = I(y, LAST v, v) + I(HD (next v), z, flatten r) + 1`
（`y ∈ v`、`z ∉ v`）。 -/
theorem aqs_indexfSplitLastFlatten {r : List (List (ℕ × ℕ))} {v : List (ℕ × ℕ)}
    {y z : ℕ × ℕ} (hflat : r.flatten.Nodup) (hy : y ∈ v) (hzv : z ∉ v)
    (hv : v ∈ r) (hall : ∀ l ∈ r, l ≠ []) (hz : z ∈ r.flatten) :
    indexf y z r.flatten
      = indexf y v.getLast! v + indexf (nextEl r v).head! z r.flatten + 1 := by
  have hvne : v ≠ [] := hall v hv
  have hnd : v.Nodup := uniqFlattenUniq r hflat v hv
  have hpos : 0 < v.length := List.length_pos_of_ne_nil hvne
  have hh : v.head! ∈ v := aqs_headMem hvne
  have hl : v.getLast! ∈ v := aqs_getLastMem hvne
  have hhF : v.head! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hh⟩
  have hyF : y ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hy⟩
  have hlF : v.getLast! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hl⟩
  have h16 : indexf v.head! z r.flatten
      = indexf v.head! v.getLast! v + indexf (nextEl r v).head! z r.flatten + 1 :=
    aqs_indexfSplitFlatten hflat hzv hv hall hz
  have h13 : v.length ≤ indexf v.head! z r.flatten :=
    aqs_sizelLeIndexfNotMem hflat hzv hv hall hz
  -- 头位置 = idxOf y v
  have hidxle : v.idxOf y ≤ v.length - 1 := by
    have := List.idxOf_lt_length_iff.mpr hy
    omega
  have hIF : indexf v.head! y r.flatten = v.idxOf y := by
    rw [← indexfFlatten hh hy (by rw [aqs_idxOfHead]; exact Nat.zero_le _) hv hflat hall,
      aqs_indexfIndexlHd]
  have hidxL : v.idxOf v.getLast! = v.length - 1 := aqs_idxOfGetLast hnd hvne
  have hV : indexf v.head! v.getLast! v = v.length - 1 := by
    rw [aqs_indexfIndexlHd, hidxL]
  -- (B) H→y→z 在 flatten 上
  have hB : indexf v.head! y r.flatten + indexf y z r.flatten
      = indexf v.head! z r.flatten :=
    indexfAddLeft hhF hyF hz (by omega)
  -- (C) H→y→LAST 在 v 上
  have hC : indexf v.head! y v + indexf y v.getLast! v = indexf v.head! v.getLast! v :=
    indexfAddLeft hh hy hl (by rw [aqs_indexfIndexlHd, hV]; exact hidxle)
  rw [aqs_indexfIndexlHd, hV] at hC
  omega

/-! ## §4 HOL AQ12.hl:762 `indexf_split_flatten_right` -/

/-- **HOL `indexf_split_flatten_right`**（AQ12.hl:762-:822）：
`I(z, LAST v, flatten r) = I(z, LAST (prev v), flatten r) + I(HD v, LAST v, v) + 1`
——反向分段（从 z 走到 LAST v 途经整段 v）。 -/
theorem aqs_indexfSplitFlattenRight {r : List (List (ℕ × ℕ))} {v : List (ℕ × ℕ)}
    {z : ℕ × ℕ} (hflat : r.flatten.Nodup) (hzv : z ∉ v) (hv : v ∈ r)
    (hall : ∀ l ∈ r, l ≠ []) (hz : z ∈ r.flatten) :
    indexf z v.getLast! r.flatten
      = indexf z (prevEl r v).getLast! r.flatten + indexf v.head! v.getLast! v + 1 := by
  have hrnd : r.Nodup := uniqFlatten hflat hall
  have hvne : v ≠ [] := hall v hv
  have hnd : v.Nodup := uniqFlattenUniq r hflat v hv
  have hpos : 0 < v.length := List.length_pos_of_ne_nil hvne
  have hh : v.head! ∈ v := aqs_headMem hvne
  have hl : v.getLast! ∈ v := aqs_getLastMem hvne
  have hhF : v.head! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hh⟩
  have hlF : v.getLast! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hl⟩
  have hzF : z ∈ r.flatten := hz
  have h18 : v.length ≤ indexf z v.getLast! r.flatten :=
    aqs_sizelLeIndexfNotMemLast hflat hzv hv hall hz
  have h15 : indexf v.head! v.getLast! r.flatten = v.length - 1 :=
    aqs_indexfHdLastSizelFlatten hflat hall hv
  have hV : indexf v.head! v.getLast! v = v.length - 1 := by
    rw [aqs_indexfIndexlHd, aqs_idxOfGetLast hnd hvne]
  -- (A) z→H→L
  have hA : indexf z v.head! r.flatten + indexf v.head! v.getLast! r.flatten
      = indexf z v.getLast! r.flatten :=
    indexfAddRight hzF hhF hlF (by rw [h15]; omega)
  -- z→H 为正（否则 z = HD v ∈ v）
  have hposA : 1 ≤ indexf z v.head! r.flatten := by
    rcases Nat.eq_zero_or_pos (indexf z v.head! r.flatten) with h0 | h
    · exfalso
      have hzh : z = v.head! := indexfZeroEq hzF hhF h0
      exact hzv (hzh ▸ hh)
    · exact h
  -- prev part 桥
  have hw : prevEl r v ∈ r := Kepler.Text.TameLp.prevEl_mem_of_mem hv
  have hwne : prevEl r v ≠ [] := hall _ hw
  have hstep : nextEl r (prevEl r v) = v := nextElPrevElUniq hrnd v
  have hstep2 : nextEl r.flatten (prevEl r v).getLast! = v.head! := by
    rw [nextElFlattenLast hflat hall hw, hstep]
  have hlw : (prevEl r v).getLast! ∈ r.flatten :=
    List.mem_flatten.mpr ⟨prevEl r v, hw, aqs_getLastMem hwne⟩
  have hlt2 : 1 < r.flatten.length := by
    have := indexfLtSizel hzF hhF
    omega
  have hstepIdx : indexf (prevEl r v).getLast! v.head! r.flatten = 1 :=
    nextElIndexf hlw hhF hflat hstep2 hlt2
  have hB : indexf z (prevEl r v).getLast! r.flatten
      + indexf (prevEl r v).getLast! v.head! r.flatten
      = indexf z v.head! r.flatten :=
    indexfAddRight hzF hlw hhF (by rw [hstepIdx]; exact hposA)
  omega

/-! ## §5 HOL AQ12.hl:831 `indexf_split_HD_flatten` -/

/-- **HOL `indexf_split_HD_flatten`**（AQ12.hl:831-:865）：
`I(y, z, flatten r) = I(y, LAST (prev v), flatten r) + I(HD v, z, v) + 1`
（`y ∉ v`、`z ∈ v`）。 -/
theorem aqs_indexfSplitHdFlatten {r : List (List (ℕ × ℕ))} {v : List (ℕ × ℕ)}
    {y z : ℕ × ℕ} (hflat : r.flatten.Nodup) (hyv : y ∉ v) (hzv : z ∈ v)
    (hv : v ∈ r) (hall : ∀ l ∈ r, l ≠ []) (hy : y ∈ r.flatten) :
    indexf y z r.flatten
      = indexf y (prevEl r v).getLast! r.flatten + indexf v.head! z v + 1 := by
  have hpos : 0 < v.length := List.length_pos_of_ne_nil (hall v hv)
  have hh : v.head! ∈ v := aqs_headMem (hall v hv)
  have hl : v.getLast! ∈ v := aqs_getLastMem (hall v hv)
  have hhF : v.head! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hh⟩
  have hzF : z ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hzv⟩
  have hlF : v.getLast! ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hl⟩
  -- decl 19 at y
  have h19 : indexf y v.getLast! r.flatten
      = indexf y (prevEl r v).getLast! r.flatten + indexf v.head! v.getLast! v + 1 :=
    aqs_indexfSplitFlattenRight hflat hyv hv hall hy
  have h15 : indexf v.head! v.getLast! r.flatten = v.length - 1 :=
    aqs_indexfHdLastSizelFlatten hflat hall hv
  have hnd : v.Nodup := uniqFlattenUniq r hflat v hv
  have hV : indexf v.head! v.getLast! v = v.length - 1 := by
    rw [aqs_indexfIndexlHd, aqs_idxOfGetLast hnd (hall v hv)]
  -- z→L 在 v 与 flatten 上同值，故 < |v|
  have hzidx : v.idxOf z ≤ v.idxOf v.getLast! := by
    have h1 : v.idxOf z ≤ v.length - 1 := by
      have := List.idxOf_lt_length_iff.mpr hzv
      omega
    have h2 : v.idxOf v.getLast! = v.length - 1 := aqs_idxOfGetLast hnd (hall v hv)
    omega
  have hzlastEq : indexf z v.getLast! v = indexf z v.getLast! r.flatten :=
    indexfFlatten hzv hl hzidx hv hflat hall
  have hzlt : indexf z v.getLast! r.flatten < v.length := by
    rw [← hzlastEq]
    exact indexfLtSizel hzv hl
  -- (B) y→z→L
  have hB : indexf y z r.flatten + indexf z v.getLast! r.flatten
      = indexf y v.getLast! r.flatten :=
    indexfAddRight hy hzF hlF (by omega)
  -- (C) H→z→L
  have hzlt' : indexf z v.getLast! r.flatten ≤ v.length - 1 := by omega
  have hC : indexf v.head! z r.flatten + indexf z v.getLast! r.flatten
      = indexf v.head! v.getLast! r.flatten :=
    indexfAddRight hhF hzF hlF (by rw [h15]; exact hzlt')
  -- (D) H→z 在 v 与 flatten 上同值
  have hD : indexf v.head! z r.flatten = indexf v.head! z v :=
    (indexfFlatten hh hzv (by rw [aqs_idxOfHead]; exact Nat.zero_le _) hv hflat hall).symm
  omega

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_idxOfHead
#print axioms Kepler.Text.TameSpine.aqs_memMemFlatten
#print axioms Kepler.Text.TameSpine.aqs_indexfSplitFlatten
#print axioms Kepler.Text.TameSpine.aqs_sizelLeIndexfNotMemLast
#print axioms Kepler.Text.TameSpine.aqs_indexfSplitLastFlatten
#print axioms Kepler.Text.TameSpine.aqs_indexfSplitFlattenRight
#print axioms Kepler.Text.TameSpine.aqs_indexfSplitHdFlatten
