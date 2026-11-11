/-
  Kepler.Text.Reduction4K4C0R2b1 — K4-C0 R2b1
  （reduction4.hl:4271 flatten_indexf / :4316 indexf_map_uniq / :4349 core_lt_indexf）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction4Idx
import Kepler.Text.Reduction4IdxRot
import Kepler.Text.Reduction5J5IndexfUnlock
import Kepler.Text.Reduction3Thm10B
import Kepler.Text.Reduction4Subseg8
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.Reduction1W2d
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList10

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
private theorem indexfHdChain' {p : List Dart} {d : Dart} (hd : d ∈ p) :
    indexf p.head! d p = p.idxOf d := by
  rw [Kepler.Text.Reduction3.indexf_eq_spine]
  exact Kepler.Text.TameSpine.indexfHd hd

/-- 链 `indexf` 的旋转不变（Spine 件经桥）。 -/
private theorem indexfRotnChain' {x y : Dart} {s : List Dart} {n : ℕ}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) :
    indexf x y s = indexf x y (s.rotate n) := by
  rw [Kepler.Text.Reduction3.indexf_eq_spine x y s,
    Kepler.Text.Reduction3.indexf_eq_spine x y (s.rotate n)]
  by_cases hs : s = []
  · subst hs; simp
  · rw [← List.rotate_mod (l := s) (n := n)]
    exact Kepler.Text.TameSpine.indexfRotn hx hy hnd
      (Nat.le_of_lt (Nat.mod_lt n (by simpa using List.length_pos_of_ne_nil hs)))

/-- `uniq (flatten L) ∧ 全非空 ⇒ uniq L`（HOL `uniq_flatten`；TameList50 同证内联）。 -/
private theorem uniqFlattenParts {α : Type*} {L : List (List α)}
    (hun : L.flatten.Nodup) (hn : ∀ l ∈ L, l ≠ []) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    rw [List.flatten_cons] at hun
    obtain ⟨_, h2, h3⟩ := List.nodup_append.mp hun
    rw [List.nodup_cons]
    refine ⟨fun ha => ?_, ih h2 (fun x hx => hn x (List.mem_cons_of_mem _ hx))⟩
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil a (hn a (List.mem_cons_self ..))
    exact absurd rfl (h3 z hz z (List.mem_flatten.mpr ⟨a, ha, hz⟩))

/-- `core` 的 `head!` 形（`headD (0,0) ↔ head!`；Reduction5Ml1W4 同证内联）。 -/
private theorem coreMapHead' (L : fgraph ℕ) (r : List Dart) :
    core L r = (parts L r).map (fun p => p.head!.1) := by
  unfold core
  exact List.map_congr_left (fun p hp => by
    cases p with
    | nil => exact absurd rfl (Kepler.Text.MoreLemma2Island2.partsAllNonnil L r _ hp)
    | cons a t => rfl)

/-! ## §R2b1-1 `indexf_map_uniq`（reduction4.hl:4316-4348） -/

/-- HOL `indexf_map_uniq`（reduction4.hl:4316）：
`d,d' ∈ ys ∧ uniq (map f ys) ⇒ indexf (f d') (f d) (map f ys) = indexf d' d ys`。 -/
theorem indexfMapUniq {α β : Type} [DecidableEq α] [DecidableEq β]
    {ys : List α} {d d' : α} {f : α → β}
    (hd : d ∈ ys) (hd' : d' ∈ ys) (hnd : (ys.map f).Nodup) :
    indexf (f d') (f d) (ys.map f) = indexf d' d ys := by
  have hfd : f d ∈ ys.map f := List.mem_map.mpr ⟨d, hd, rfl⟩
  have hfd' : f d' ∈ ys.map f := List.mem_map.mpr ⟨d', hd', rfl⟩
  simp only [Kepler.Text.Reduction5.indexf]
  rw [if_pos ⟨hfd', hfd⟩, if_pos ⟨hd', hd⟩,
    Kepler.Text.Reduction3.t10b_indexl_map_uniq hd hnd,
    Kepler.Text.Reduction3.t10b_indexl_map_uniq hd' hnd, List.length_map]

/-! ## §R2b1-2 `flatten_indexf`（reduction4.hl:4271-4315） -/

/-- HOL `flatten_indexf`（reduction4.hl:4271）：
`all 非空 R ∧ uniq (flatten R) ∧ px,py,pz ∈ R ∧ y ∈ py ∧ z ∈ pz ∧ 三点互异 ⇒
(indexf px py R < indexf px pz R ↔
  indexf (HD px) y (flatten R) < indexf (HD px) z (flatten R))`。
DIFFERS：`HD` ↦ `head!`（前提 `px ∈ R` + 全非空保证非空，无 junk 面）。 -/
theorem flattenIndexf {R : List (List Dart)} {px py pz : List Dart} {y z : Dart}
    (hnil : ∀ p ∈ R, p ≠ []) (hnd : R.flatten.Nodup)
    (hpx : px ∈ R) (hpy : py ∈ R) (hy : y ∈ py) (hne_xy : px ≠ py)
    (hpz : pz ∈ R) (hz : z ∈ pz) (hne_xz : px ≠ pz) (hne_yz : py ≠ pz) :
    (indexf px py R < indexf px pz R ↔
      indexf px.head! y R.flatten < indexf px.head! z R.flatten) := by
  have hRnd : R.Nodup := uniqFlattenParts hnd hnil
  have hpxne : px ≠ [] := hnil px hpx
  have hRne : R ≠ [] := List.ne_nil_of_mem hpx
  -- 索引：显式 `instBEqOfDecidableEq` 世界（`indexf_rotate_to_indexl` 的烘焙实例）
  set k : ℕ := @List.idxOf (List Dart) (instBEqOfDecidableEq) px R with hk
  have hrotEq : @Kepler.Text.Reduction3.rotateTo (List Dart) (instBEqOfDecidableEq) R px
      = R.rotate k := by
    rw [hk]
    exact @Kepler.Text.Reduction1.rotateToEqRotate (List Dart) (instBEqOfDecidableEq)
      (by infer_instance) R px hpx hRnd
  have hRkne : R.rotate k ≠ [] := fun h => hRne (List.rotate_eq_nil_iff.mp h)
  -- 旋转后头元 = px（`rotate_to` 头元 rfl）
  have hRk_head : (R.rotate k).head! = px := by
    rw [← hrotEq]
    rfl
  -- 旋转后 flatten 头元 = px 头元
  have hRk_flat_head : (R.rotate k).flatten.head! = px.head! := by
    obtain ⟨a, t, hcons⟩ := List.exists_cons_of_ne_nil hRkne
    have ha : a = px := by
      have h1 : (R.rotate k).head! = a := by rw [hcons]; rfl
      exact h1.symm.trans hRk_head
    rw [hcons, List.flatten_cons, ha]
    exact List.head!_append t.flatten hpxne
  -- flattenRot 见证 + 旋转量取模
  obtain ⟨k', hflat⟩ := Kepler.Text.Reduction4Idx.flattenRot k R
  have hrotflat : R.flatten.rotate (k' % R.flatten.length) = (R.rotate k).flatten := by
    rw [List.rotate_mod (l := R.flatten) (n := k')]
    exact hflat.symm
  have hrotm : (R.flatten.rotate (k' % R.flatten.length)).head! = px.head! := by
    rw [hrotflat]
    exact hRk_flat_head
  have hpxh_mem : px.head! ∈ R.flatten :=
    List.mem_flatten.mpr ⟨px, hpx, List.head!_mem_self hpxne⟩
  have hyR : y ∈ R.flatten := List.mem_flatten.mpr ⟨py, hpy, hy⟩
  have hzR : z ∈ R.flatten := List.mem_flatten.mpr ⟨pz, hpz, hz⟩
  -- 桥：element 层的两个 indexf = 旋转后 flatten 的 idxOf
  have hbridgeY : indexf px.head! y R.flatten
      = (R.rotate k).flatten.idxOf y := by
    rw [indexfRotnChain' hpxh_mem hyR hnd (n := k' % R.flatten.length), ← hrotm,
      indexfHdChain' (List.mem_rotate.mpr hyR), hrotflat]
  have hbridgeZ : indexf px.head! z R.flatten
      = (R.rotate k).flatten.idxOf z := by
    rw [indexfRotnChain' hpxh_mem hzR hnd (n := k' % R.flatten.length), ← hrotm,
      indexfHdChain' (List.mem_rotate.mpr hzR), hrotflat]
  -- 世界桥①：`instBEqOfDecidableEq` → 文件默认（`List.instBEq ∘ instBEqProd`）
  have hbY : @List.idxOf (List Dart) (instBEqOfDecidableEq) py (R.rotate k)
      = @List.idxOf (List Dart) (@List.instBEq Dart instBEqProd) py (R.rotate k) :=
    Kepler.Text.TameLp.li_idxOf_of_lawful (by infer_instance) (by infer_instance) _ _
  have hbZ : @List.idxOf (List Dart) (instBEqOfDecidableEq) pz (R.rotate k)
      = @List.idxOf (List Dart) (@List.instBEq Dart instBEqProd) pz (R.rotate k) :=
    Kepler.Text.TameLp.li_idxOf_of_lawful (by infer_instance) (by infer_instance) _ _
  -- 左端：indexf 换成 rotate_to 的 idxOf（再换算到文件默认世界）
  have hify : indexf px py R
      = @List.idxOf (List Dart) (@List.instBEq Dart instBEqProd) py (R.rotate k) := by
    rw [Kepler.Text.Reduction5.indexfRotateToIndexl (z := py) (w := px) hpy hpx hRnd, hrotEq]
    exact hbY
  have hifz : indexf px pz R
      = @List.idxOf (List Dart) (@List.instBEq Dart instBEqProd) pz (R.rotate k) := by
    rw [Kepler.Text.Reduction5.indexfRotateToIndexl (z := pz) (w := px) hpz hpx hRnd, hrotEq]
    exact hbZ
  -- raster：flattenIndexl 在 `R.rotate k`
  have hnd' : (R.rotate k).flatten.Nodup := by
    rw [hflat]
    exact List.nodup_rotate.mpr hnd
  have hfl := Kepler.Text.Reduction4Idx.flattenIndexl (R.rotate k) py pz y z
    (fun p hp => hnil p (List.mem_rotate.mp hp)) hnd'
    (List.mem_rotate.mpr hpy) (List.mem_rotate.mpr hpz) hy hz hne_yz
  -- 世界桥②：文件默认 → `flattenIndexl` 烘焙世界（`List.instBEq ∘ instBEqOfDecidableEq`）
  have hL1 : @List.idxOf (List Dart) (@List.instBEq Dart instBEqProd) py (R.rotate k)
      = @List.idxOf (List Dart) (@List.instBEq Dart (instBEqOfDecidableEq)) py (R.rotate k) :=
    Kepler.Text.TameLp.li_idxOf_of_lawful (by infer_instance) (by infer_instance) _ _
  have hL2 : @List.idxOf (List Dart) (@List.instBEq Dart instBEqProd) pz (R.rotate k)
      = @List.idxOf (List Dart) (@List.instBEq Dart (instBEqOfDecidableEq)) pz (R.rotate k) :=
    Kepler.Text.TameLp.li_idxOf_of_lawful (by infer_instance) (by infer_instance) _ _
  have hR1 : @List.idxOf Dart instBEqProd y (R.rotate k).flatten
      = @List.idxOf Dart (instBEqOfDecidableEq) y (R.rotate k).flatten :=
    Kepler.Text.TameLp.li_idxOf_of_lawful (by infer_instance) (by infer_instance) _ _
  have hR2 : @List.idxOf Dart instBEqProd z (R.rotate k).flatten
      = @List.idxOf Dart (instBEqOfDecidableEq) z (R.rotate k).flatten :=
    Kepler.Text.TameLp.li_idxOf_of_lawful (by infer_instance) (by infer_instance) _ _
  rw [hify, hifz, hbridgeY, hbridgeZ, hL1, hL2, hR1, hR2]
  exact hfl

/-! ## §R2b1-3 `core_lt_indexf`（reduction4.hl:4349-4424） -/

/-- HOL `core_lt_indexf`（reduction4.hl:4349）：
`good_list L ∧ marked_list L N r x ∧ u,v ∈ r ∧ 三个 FST 互异 ∧ p ∈ parts L r ⇒
(indexf (HD p) u r < indexf (HD p) v r ↔
  indexf (FST (HD p)) (FST u) (core L r) <
  indexf (FST (HD p)) (FST v) (core L r))`。
DIFFERS：`HD` ↦ `head!`；`marked_list` 带 `hL` 载体（章约定）。 -/
theorem coreLtIndexf (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    {r : List Dart} {p : List Dart} {x : Dart} {u v : Dart}
    (hm : markedList L hL N r x)
    (hu : u ∈ r) (hv : v ∈ r)
    (hpu : p.head!.1 ≠ u.1) (hpv : p.head!.1 ≠ v.1) (huv : u.1 ≠ v.1)
    (hp : p ∈ parts L r) :
    (indexf p.head! u r < indexf p.head! v r ↔
      indexf p.head!.1 u.1 (core L r) < indexf p.head!.1 v.1 (core L r)) := by
  have hN : normalList L hL N := hm.2.1
  have hrN : r ∈ N := hm.2.2.1
  obtain ⟨hrnd, hrne, _, _, _⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN hrN hp
  obtain ⟨pu, hpu_mem, hu_pu⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hu
  obtain ⟨pv, hpv_mem, hv_pv⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hv
  have hpu_fst : u.1 = pu.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hrN hpu_mem hu_pu
  have hpv_fst : v.1 = pv.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hrN hpv_mem hv_pv
  have hne_p_pu : p ≠ pu := by
    intro h
    rw [← h] at hpu_fst
    exact hpu hpu_fst.symm
  have hne_p_pv : p ≠ pv := by
    intro h
    rw [← h] at hpv_fst
    exact hpv hpv_fst.symm
  have hne_pu_pv : pu ≠ pv := by
    intro h
    apply huv
    rw [h] at hpu_fst
    exact hpu_fst.trans hpv_fst.symm
  have hndP : (parts L r).flatten.Nodup := by
    rw [Kepler.Text.MoreLemma2Island2.partsFlatten L hrnd hrne]
    exact hrnd
  have hfl := flattenIndexf (R := parts L r) (px := p) (py := pu) (pz := pv)
    (y := u) (z := v)
    (Kepler.Text.MoreLemma2Island2.partsAllNonnil L r) hndP hp hpu_mem hu_pu hne_p_pu
    hpv_mem hv_pv hne_p_pv hne_pu_pv
  rw [Kepler.Text.MoreLemma2Island2.partsFlatten L hrnd hrne] at hfl
  have hndCore : (core L r).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hcore : core L r = (parts L r).map (fun q => q.head!.1) := coreMapHead' L r
  have hndMap : ((parts L r).map (fun q => q.head!.1)).Nodup := by
    rw [← hcore]
    exact hndCore
  have hmu : indexf p.head!.1 u.1 (core L r) = indexf p pu (parts L r) := by
    rw [hpu_fst, hcore]
    exact indexfMapUniq (ys := parts L r) (d := pu) (d' := p)
      (f := fun q : List Dart => q.head!.1) hpu_mem hp hndMap
  have hmv : indexf p.head!.1 v.1 (core L r) = indexf p pv (parts L r) := by
    rw [hpv_fst, hcore]
    exact indexfMapUniq (ys := parts L r) (d := pv) (d' := p)
      (f := fun q : List Dart => q.head!.1) hpv_mem hp hndMap
  rw [← hfl]
  rw [hmu, hmv]

end Kepler.Text.Reduction4

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction4.indexfMapUniq
#print axioms Kepler.Text.Reduction4.flattenIndexf
#print axioms Kepler.Text.Reduction4.coreLtIndexf
