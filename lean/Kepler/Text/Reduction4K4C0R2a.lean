/-
  Kepler.Text.Reduction4K4C0R2a — K4-C0 R2a
  （reduction4.hl:4046 mem_ifbetwn_hd_extend）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction4K4C0
import Kepler.Text.Reduction4IdxRot
import Kepler.Text.Reduction5J5IndexfUnlock
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.Reduction3Thm6B

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4

open Kepler.Graphs (Face Graph fgraph between)
open Kepler.Assembly (GoodList findFaceDarts nextEl prevEl)
open Kepler.Text.Reduction5
  (Dart core ntrans rtrans ytrans ztrans transformCount finalList ifbetwn indexf parts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-- 链 `indexf` 的 `indexf_hd`（Spine 件经 `indexf_eq_spine` 桥）。 -/
private theorem indexfHdChain {p : List Dart} {d : Dart} (hd : d ∈ p) :
    indexf p.head! d p = p.idxOf d := by
  rw [Kepler.Text.Reduction3.indexf_eq_spine]
  exact Kepler.Text.TameSpine.indexfHd hd

/-- 链 `indexf` 的 `indexf_rotn_alt`（旋转不变，Spine 件经桥）。 -/
private theorem indexfRotnChain {x y : Dart} {s : List Dart} {n : ℕ}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) :
    indexf x y s = indexf x y (s.rotate n) := by
  rw [Kepler.Text.Reduction3.indexf_eq_spine x y s,
    Kepler.Text.Reduction3.indexf_eq_spine x y (s.rotate n)]
  by_cases hs : s = []
  · subst hs; simp
  · rw [← List.rotate_mod (l := s) (n := n)]
    exact Kepler.Text.TameSpine.indexfRotn hx hy hnd
      (Nat.le_of_lt (Nat.mod_lt n (by simpa using List.length_pos_of_ne_nil hs)))

/-- HOL `mem_ifbetwn_hd_extend`（reduction4.hl:4046-4122）：
`p ∈ parts L r`、`x ∈ p`、`y,z ∈ r`、`FST x` 与 `FST y`/`FST z` 互异 ⇒
`y ∈ ifbetwn r x z ↔ y ∈ ifbetwn r (HD p) z`。 -/
theorem memIfbetwnHdExtend (L : fgraph ℕ) (N : List (List Dart)) (r p : List Dart)
    (x y z : Dart)
    (hL : GoodList L) (hn : normalList L hL N) (hrN : r ∈ N)
    (hp : p ∈ parts L r) (hx : x ∈ p) (hz : z ∈ r) (hy : y ∈ r)
    (hxy : x.1 ≠ y.1) (hxz : x.1 ≠ z.1) :
    y ∈ ifbetwn r x z ↔ y ∈ ifbetwn r p.head! z := by
  obtain ⟨hrnd, -, -, hpne, hpr⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hn hrN hp
  have hheadp : p.head! ∈ p := List.head!_mem_self hpne
  have hheadr : p.head! ∈ r := hpr _ hheadp
  have hxr : x ∈ r := hpr _ hx
  have hxhead : x.1 = p.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn hrN hp hx
  rw [ifbetwnIndexf hxr hy hz hrnd, ifbetwnIndexf hheadr hy hz hrnd]
  have hixy : indexf x y r ≠ 0 := fun h => hxy (by rw [indexf_eq_zero hxr hy h])
  have hihy : indexf p.head! y r ≠ 0 := by
    intro h
    have hpy : p.head! = y := indexf_eq_zero hheadr hy h
    exact hxy (hxhead.trans (congrArg Prod.fst hpy))
  have hadd : ∀ u ∈ r, u.1 ≠ p.head!.1 →
      indexf p.head! u r = indexf p.head! x r + indexf x u r := by
    intro u hu hune
    have hup : u ∉ p := fun hmem =>
      hune (by rw [Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn hrN hp hmem])
    obtain ⟨k, hk⟩ := Kepler.Text.Reduction4IdxRot.rotParts L hL hn hrN hp
    set s := r.rotate k with hs
    have hfull : p ++ s.drop p.length = s := by
      rw [hs]
      conv_lhs =>
        arg 1
        rw [← hk]
      exact List.take_append_drop p.length s
    have hsnd : s.Nodup := by
      rw [hs, List.nodup_rotate]; exact hrnd
    have hx_s : x ∈ s := by rw [hs]; exact List.mem_rotate.mpr hxr
    have hu_s : u ∈ s := by rw [hs]; exact List.mem_rotate.mpr hu
    have hhead_s : p.head! ∈ s := by rw [← hfull]; exact List.mem_append_left _ hheadp
    have hheadS : s.head! = p.head! := by
      rw [← hfull]
      cases p with
      | nil => exact absurd rfl hpne
      | cons a t => rfl
    have hixs : indexf p.head! x s = p.idxOf x := by
      rw [← hheadS, indexfHdChain hx_s]
      conv_lhs => rw [← hfull]
      rw [List.idxOf_append, if_pos hx]
    have hius : indexf p.head! u s = p.length + (s.drop p.length).idxOf u := by
      rw [← hheadS, indexfHdChain hu_s]
      conv_lhs => rw [← hfull]
      rw [List.idxOf_append, if_neg hup]
      omega
    have hle_p : p.idxOf x ≤ p.length :=
      Nat.le_of_lt (List.idxOf_lt_length_iff.mpr hx)
    have hle : indexf p.head! x s ≤ indexf p.head! u s := by
      rw [hixs, hius]; omega
    have hrotx : indexf p.head! x r = indexf p.head! x s := by
      rw [hs]
      exact indexfRotnChain hheadr hxr hrnd
    have hrotu : indexf p.head! u r = indexf p.head! u s := by
      rw [hs]
      exact indexfRotnChain hheadr hu hrnd
    have hle' : indexf p.head! x r ≤ indexf p.head! u r := by
      rw [hrotx, hrotu]; exact hle
    exact (Kepler.Text.Reduction4.indexf_add_left hheadr hxr hu hle').symm
  rw [hadd y hy (fun h => hxy (h.trans hxhead.symm).symm),
    hadd z hz (fun h => hxz (h.trans hxhead.symm).symm)]
  constructor <;> intro h <;> omega

end Kepler.Text.Reduction4

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction4.memIfbetwnHdExtend
