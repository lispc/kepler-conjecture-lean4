/-
  Kepler.Text.Reduction4K4C0R2b2 — K4-C0 R2b2
  （reduction4.hl:4123 mem_ifbetwn_tl_extend / :4425 core_betwn）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction4K4C0
import Kepler.Text.Reduction4K4C0R2a
import Kepler.Text.Reduction4K4C0R2b1
import Kepler.Text.Reduction4IdxRot
import Kepler.Text.Reduction4Subseg4
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.Reduction5J5IndexfUnlock
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList10
import Kepler.Graphs.FaceDivisionProps1

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
private theorem indexfHdChain2 {p : List Dart} {d : Dart} (hd : d ∈ p) :
    indexf p.head! d p = p.idxOf d := by
  rw [Kepler.Text.Reduction3.indexf_eq_spine]
  exact Kepler.Text.TameSpine.indexfHd hd

/-- 链 `indexf` 的旋转不变（Spine 件经桥）。 -/
private theorem indexfRotnChain2 {x y : Dart} {s : List Dart} {n : ℕ}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) :
    indexf x y s = indexf x y (s.rotate n) := by
  rw [Kepler.Text.Reduction3.indexf_eq_spine x y s,
    Kepler.Text.Reduction3.indexf_eq_spine x y (s.rotate n)]
  by_cases hs : s = []
  · subst hs; simp
  · rw [← List.rotate_mod (l := s) (n := n)]
    exact Kepler.Text.TameSpine.indexfRotn hx hy hnd
      (Nat.le_of_lt (Nat.mod_lt n (by simpa using List.length_pos_of_ne_nil hs)))

/-! ## §R2b2-1 `mem_ifbetwn_tl_extend`（reduction4.hl:4123-4348） -/

/-- HOL `mem_ifbetwn_tl_extend`（reduction4.hl:4123）：
`p ∈ parts L r`、`z ∈ p`、`x,y ∈ r`、`FST y`/`FST x` 与 `FST z` 互异 ⇒
`y ∈ ifbetwn r x z ↔ y ∈ ifbetwn r x (LAST p)`。
DIFFERS：`LAST p` ↦ `p.getLast!`（`p ∈ parts` 蕴含非空，无 junk 面）。 -/
theorem memIfbetwnTlExtend (L : fgraph ℕ) (N : List (List Dart)) (r p : List Dart)
    (x y z : Dart)
    (hL : GoodList L) (hn : normalList L hL N) (hrN : r ∈ N)
    (hp : p ∈ parts L r) (hz : z ∈ p) (hx : x ∈ r) (hy : y ∈ r)
    (hyz : y.1 ≠ z.1) (hxz : x.1 ≠ z.1) :
    y ∈ ifbetwn r x z ↔ y ∈ ifbetwn r x p.getLast! := by
  obtain ⟨hrnd, -, -, hpne, hpr⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hn hrN hp
  have hzr : z ∈ r := hpr z hz
  have hlast_mem : p.getLast! ∈ p := Kepler.Graphs.getLast!_mem hpne
  have hlastr : p.getLast! ∈ r := hpr _ hlast_mem
  -- 部分内 FST 同一
  have hzfst : z.1 = p.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn hrN hp hz
  have hlfst : p.getLast!.1 = p.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn hrN hp hlast_mem
  have hxzp : x ∉ p := fun hmem =>
    hxz (by rw [Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn hrN hp hmem, hzfst])
  have hyzp : y ∉ p := fun hmem =>
    hyz (by rw [Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn hrN hp hmem, hzfst])
  rw [ifbetwnIndexf hx hy hzr hrnd, ifbetwnIndexf hx hy hlastr hrnd]
  -- 核心：`indexf x y r ≤ indexf x z r ↔ indexf x y r ≤ indexf x (LAST p) r`
  have hcmp : indexf x y r ≤ indexf x z r ↔ indexf x y r ≤ indexf x p.getLast! r := by
    -- 旋转到 `p` 为前缀的 `r'`，再在 `p` 尾后拆出 `x` 的两侧
    obtain ⟨k, hk⟩ := Kepler.Text.Reduction4IdxRot.rotParts L hL hn hrN hp
    set r' : List Dart := r.rotate k with hr'def
    have hr'nd : r'.Nodup := by rw [hr'def]; exact List.nodup_rotate.mpr hrnd
    have htake : r'.take p.length = p := hk
    have hxr' : x ∈ r' := by rw [hr'def]; exact List.mem_rotate.mpr hx
    have hyr' : y ∈ r' := by rw [hr'def]; exact List.mem_rotate.mpr hy
    have hzr' : z ∈ r' := by rw [hr'def]; exact List.mem_rotate.mpr hzr
    have hlastr' : p.getLast! ∈ r' := by
      rw [hr'def]; exact List.mem_rotate.mpr hlastr
    set t : List Dart := r'.drop p.length with htdef
    have hr'eq : p ++ t = r' := by
      rw [htdef]
      conv_lhs => arg 1; rw [← htake]
      exact List.take_append_drop p.length r'
    have hxt : x ∈ t := by
      rcases List.mem_append.mp (hr'eq ▸ hxr') with h | h
      · exact absurd h hxzp
      · exact h
    have hyt : y ∈ t := by
      rcases List.mem_append.mp (hr'eq ▸ hyr') with h | h
      · exact absurd h hyzp
      · exact h
    have htid : t.idxOf x < t.length := List.idxOf_lt_length_iff.mpr hxt
    set u : List Dart := t.take (t.idxOf x) with hudef
    set v : List Dart := t.drop (t.idxOf x + 1) with hvdef
    have htdec : t = u ++ x :: v := by
      rw [hudef, hvdef]
      conv_lhs => rw [← List.take_append_drop (t.idxOf x) t]
      rw [List.drop_eq_getElem_cons htid, Kepler.Text.TameLp.getElem_idxOf hxt]
    -- `s = (x :: v) ++ (p ++ u)` 是 `r'` 的旋转，头元 `x`
    set A : List Dart := x :: v with hAdef
    set s : List Dart := A ++ (p ++ u) with hsdef
    have hr'dec : r' = p ++ (u ++ x :: v) := by rw [← hr'eq, htdec]
    have hrot1 : r'.rotate p.length = (u ++ x :: v) ++ p := by
      rw [hr'dec]
      exact List.rotate_append_length_eq p (u ++ x :: v)
    have hsrot : r'.rotate (p.length + u.length) = s := by
      rw [← List.rotate_rotate, hrot1, hsdef, hAdef]
      rw [show (u ++ x :: v) ++ p = u ++ ((x :: v) ++ p) by simp [List.append_assoc],
        List.rotate_append_length_eq u ((x :: v) ++ p), List.append_assoc]
    have hshead : s.head! = x := by
      rw [hsdef, hAdef]
      rfl
    have hys : y ∈ s := by
      rw [hsdef, hAdef]
      rcases List.mem_append.mp (htdec ▸ hyt) with hu | hxv
      · exact List.mem_append_right _ (List.mem_append_right _ hu)
      · rcases List.mem_cons.mp hxv with rfl | hv
        · exact List.mem_append_left _ (List.mem_cons_self ..)
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ hv)
    have hzs : z ∈ s := by
      rw [hsdef]
      exact List.mem_append_right _ (List.mem_append_left _ hz)
    have hws : p.getLast! ∈ s := by
      rw [hsdef]
      exact List.mem_append_right _ (List.mem_append_left _ hlast_mem)
    have hsnd : s.Nodup := by
      rw [← hsrot]
      exact List.nodup_rotate.mpr hr'nd
    have hdisjA : ∀ a ∈ A, ∀ b ∈ p ++ u, a ≠ b := by
      have h := hsnd
      rw [hsdef] at h
      exact (List.nodup_append.mp h).2.2
    have hzA : z ∉ A := fun hmem =>
      hdisjA z hmem z (List.mem_append_left _ hz) rfl
    have hwA : p.getLast! ∉ A := fun hmem =>
      hdisjA (p.getLast!) hmem (p.getLast!) (List.mem_append_left _ hlast_mem) rfl
    have hsz : s.idxOf z = A.length + p.idxOf z := by
      rw [hsdef, List.idxOf_append_of_notMem hzA, List.idxOf_append_of_mem hz]
    have hsw : s.idxOf (p.getLast!) = A.length + p.idxOf (p.getLast!) := by
      rw [hsdef, List.idxOf_append_of_notMem hwA, List.idxOf_append_of_mem hlast_mem]
    have hple_z : p.idxOf z < p.length := List.idxOf_lt_length_iff.mpr hz
    have hple_w : p.idxOf (p.getLast!) < p.length :=
      List.idxOf_lt_length_iff.mpr hlast_mem
    have hcmpS : s.idxOf y ≤ s.idxOf z ↔ s.idxOf y ≤ s.idxOf (p.getLast!) := by
      by_cases hyA : y ∈ A
      · have hsy : s.idxOf y = A.idxOf y := by
          rw [hsdef, List.idxOf_append_of_mem hyA]
        have hylt : A.idxOf y < A.length := List.idxOf_lt_length_iff.mpr hyA
        rw [hsz, hsw, hsy]; omega
      · have hypu : y ∈ p ++ u := by
          rcases List.mem_append.mp (hsdef ▸ hys) with h | h
          · exact absurd h hyA
          · exact h
        have hyu : y ∈ u := by
          rcases List.mem_append.mp hypu with h | h
          · exact absurd h hyzp
          · exact h
        have hsy : s.idxOf y = A.length + (p.length + u.idxOf y) := by
          rw [hsdef, List.idxOf_append_of_notMem hyA, List.idxOf_append_of_notMem hyzp]
        rw [hsz, hsw, hsy]; omega
    -- `indexf` ↔ `idxOf`（头元 `x`）
    have hidx (w : Dart) (hw : w ∈ s) : indexf x w s = s.idxOf w := by
      rw [← hshead]
      exact indexfHdChain2 hw
    have hrotEq (w : Dart) (hw : w ∈ r) : indexf x w r = indexf x w s := by
      have hw' : w ∈ r' := by rw [hr'def]; exact List.mem_rotate.mpr hw
      have h1 : indexf x w r = indexf x w r' := by
        rw [hr'def]
        exact indexfRotnChain2 hx hw hrnd
      have h2 : indexf x w r' = indexf x w s := by
        rw [← hsrot]
        exact indexfRotnChain2 hxr' hw' hr'nd
      exact h1.trans h2
    rw [hrotEq y hy, hrotEq z hzr, hrotEq (p.getLast!) hlastr,
      hidx y hys, hidx z hzs, hidx (p.getLast!) hws]
    exact hcmpS
  exact ⟨fun h => ⟨h.1, hcmp.mp h.2⟩, fun h => ⟨h.1, hcmp.mpr h.2⟩⟩

/-! ## §R2b2-2 `core_betwn`（reduction4.hl:4425-4497） -/

/-- HOL `core_betwn`（reduction4.hl:4425）：
`good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧ ¬final_list L r ∧
edge_nondegenerate ∧ u,v,w ∈ r ∧ 三个 FST 互异 ⇒
(v ∈ ifbetwn r u w ↔ FST v ∈ ifbetwn (core L r) (FST u) (FST w))`。
DIFFERS：`good_list_nodes` ↦ `GoodListNodesTl L hL`；`is_edge_nondegenerate` ↦
`(hypermapOfList L hL).EdgeNondegenerate`（两前提在 HOL 证体中同样未被消费）。 -/
theorem coreBetwn (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x u v w : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hen : (hypermapOfList L hL).EdgeNondegenerate)
    (hu : u ∈ r) (hv : v ∈ r) (hw : w ∈ r)
    (huv : u.1 ≠ v.1) (hvw : v.1 ≠ w.1) (huw : u.1 ≠ w.1) :
    v ∈ ifbetwn r u w ↔ v.1 ∈ ifbetwn (core L r) u.1 w.1 := by
  have hN : normalList L hL N := hm.2.1
  have hrN : r ∈ N := hm.2.2.1
  have hrnd : r.Nodup := (List.nodup_flatten.mp hN.1).1 r hrN
  have hrne : r ≠ [] := hN.2.1 r hrN
  obtain ⟨pu, hpu_mem, hu_pu⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hu
  obtain ⟨pv, hpv_mem, hv_pv⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hv
  obtain ⟨pw, hpw_mem, hw_pw⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hw
  have hpu_fst : u.1 = pu.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hrN hpu_mem hu_pu
  have hpv_fst : v.1 = pv.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hrN hpv_mem hv_pv
  have hpw_fst : w.1 = pw.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hrN hpw_mem hw_pw
  obtain ⟨-, -, -, hpu_ne, hprpu⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN hrN hpu_mem
  obtain ⟨-, -, -, hpw_ne, hprpw⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN hrN hpw_mem
  have hpuh_mem : pu.head! ∈ pu := List.head!_mem_self hpu_ne
  have hpuh_r : pu.head! ∈ r := hprpu _ hpuh_mem
  have hpw_last_mem : pw.getLast! ∈ pw := Kepler.Graphs.getLast!_mem hpw_ne
  have hpw_last_r : pw.getLast! ∈ r := hprpw _ hpw_last_mem
  have hpw_last_fst : pw.getLast!.1 = pw.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hrN hpw_mem hpw_last_mem
  have hpu_fst' : pu.head!.1 = u.1 := hpu_fst.symm
  have hpw_last_fst' : pw.getLast!.1 = w.1 := hpw_last_fst.trans hpw_fst.symm
  -- 两段 extend 把 `u,w` 换成 `HD pu / LAST pw`
  have hstep1 : v ∈ ifbetwn r u w ↔ v ∈ ifbetwn r pu.head! w :=
    memIfbetwnHdExtend L N r pu u v w hL hN hrN hpu_mem hu_pu hw hv huv huw
  have hstep2 : v ∈ ifbetwn r pu.head! w ↔ v ∈ ifbetwn r pu.head! pw.getLast! :=
    memIfbetwnTlExtend L N r pw pu.head! v w hL hN hrN hpw_mem hw_pw hpuh_r hv hvw
      (fun h => huw (hpu_fst.trans h))
  -- 两侧 indexf 化
  have hIr : v ∈ ifbetwn r pu.head! pw.getLast! ↔
      0 < indexf pu.head! v r ∧ indexf pu.head! v r ≤ indexf pu.head! pw.getLast! r :=
    ifbetwnIndexf hpuh_r hv hpw_last_r hrnd
  have huc : u.1 ∈ core L r := Kepler.Text.Reduction4Idx.memFstCore L hL hm hu
  have hvc : v.1 ∈ core L r := Kepler.Text.Reduction4Idx.memFstCore L hL hm hv
  have hwc : w.1 ∈ core L r := Kepler.Text.Reduction4Idx.memFstCore L hL hm hw
  have hcnd : (core L r).Nodup := Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hIc : v.1 ∈ ifbetwn (core L r) u.1 w.1 ↔
      0 < indexf u.1 v.1 (core L r) ∧
        indexf u.1 v.1 (core L r) ≤ indexf u.1 w.1 (core L r) :=
    ifbetwnIndexf huc hvc hwc hcnd
  -- 首合取：两侧均为真
  have hpos1 : 0 < indexf pu.head! v r := by
    apply Nat.pos_of_ne_zero
    intro h0
    have hEq : pu.head! = v := indexf_eq_zero hpuh_r hv h0
    exact huv (hpu_fst.trans (congrArg Prod.fst hEq))
  have hpos2 : 0 < indexf u.1 v.1 (core L r) := by
    apply Nat.pos_of_ne_zero
    intro h0
    exact huv (indexf_eq_zero huc hvc h0)
  -- 第二合取：`≤` 化 `<`（相等支被 indexf 单射排除）
  have hne_r : indexf pu.head! v r ≠ indexf pu.head! pw.getLast! r := by
    intro heq
    have hEq : v = pw.getLast! := (indexfInj hpuh_r hv hpw_last_r).mp heq
    exact hvw (by rw [hEq]; exact hpw_last_fst.trans hpw_fst.symm)
  have hne_c : indexf u.1 v.1 (core L r) ≠ indexf u.1 w.1 (core L r) := by
    intro heq
    exact hvw ((indexfInj huc hvc hwc).mp heq)
  have hlt_r : indexf pu.head! v r ≤ indexf pu.head! pw.getLast! r ↔
      indexf pu.head! v r < indexf pu.head! pw.getLast! r :=
    ⟨fun h => lt_of_le_of_ne h hne_r, fun h => h.le⟩
  have hlt_c : indexf u.1 v.1 (core L r) ≤ indexf u.1 w.1 (core L r) ↔
      indexf u.1 v.1 (core L r) < indexf u.1 w.1 (core L r) :=
    ⟨fun h => lt_of_le_of_ne h hne_c, fun h => h.le⟩
  -- `core_lt_indexf` 收口
  have hcoreLt := coreLtIndexf (L := L) (hL := hL) (N := N) (r := r) (p := pu) (x := x)
    (u := v) (v := pw.getLast!) hm hv hpw_last_r
    (fun h => huv (hpu_fst'.symm.trans h))
    (fun h => huw (hpu_fst'.symm.trans (h.trans hpw_last_fst')))
    (fun h => hvw (h.trans hpw_last_fst')) hpu_mem
  rw [hpu_fst', hpw_last_fst'] at hcoreLt
  have hiff : (indexf pu.head! v r ≤ indexf pu.head! pw.getLast! r) ↔
      (indexf u.1 v.1 (core L r) ≤ indexf u.1 w.1 (core L r)) := by
    rw [hlt_r, hlt_c]
    exact hcoreLt
  rw [hstep1, hstep2, hIr, hIc]
  exact ⟨fun h => ⟨hpos2, hiff.mp h.2⟩, fun h => ⟨hpos1, hiff.mpr h.2⟩⟩

end Kepler.Text.Reduction4

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction4.memIfbetwnTlExtend
#print axioms Kepler.Text.Reduction4.coreBetwn
