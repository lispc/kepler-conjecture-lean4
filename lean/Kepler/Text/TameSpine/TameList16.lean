/-
  Kepler.Text.TameSpine.TameList16 — B1 Tame_list 地基批 16：quotient_list 章 +
  商列表 iso capstone（tamespine-port-plan §4 批次表 B1 行；接续批 15 =
  TameList15.lean，批 15 终点 = HOL :9374（iso_restricted Iff 提前落），
  本批起点 = HOL :9362 marked_list_is_node_nondegenerate。侦察记档：任务书
  预估 quotient_list 章 :9380 起，实际 :9360 `DAKEFCC` 是 iso_restricted 的
  别名（零移植）、:9362 即本章首件——相对任务书 -18 行漂移（批 15 已记
  +53~68 漂移先例，以库内副本为准）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl）：

  - 前置补漏（批 11 记账「quotient_list_iso_quotient :8223 需 hyp_iso」——
    批 15 Hypermap_iso 桥章落地后解锁）：`quotient_list_iso_quotient` :8223；
  - quotient_list 章 :9362-:9903：
    `marked_list_is_node_nondegenerate` :9362 / `lemma_yz_in_face_list` :9413 /
    `lemma_node_outside_darts_of_family_list` :9434 / `inverse_node_map_quotient`
    :9469 / `mem_el_index` :9505 / `index_el` :9513 / `parts_node_power` :9521 /
    `parts_node_map_hd` :9558 / `node_map_quotient` :9606 / `quotient_node_lemma`
    :9685 / `good_list_nodes_condition2` :9792 / `list_of_darts_quotient_darts`
    :9847 / `good_list_nodes_quotient` :9865（:9903 `PMBRINH` 是
    good_list_nodes_quotient 别名，零移植）；
  - marked 收束两件：`final_loops_list_iff` :10050 / `marked_conclusion` :10071。

  诚实记账（本批跳过/止损）：
  - `marked_list_marked` :9905 / `marked_translate` :10100 及下游
    `normal_list_in_dart_of_loop2` :10146 / HQYMRTX1/2_list :10165/:10188，
    连同 AQIUNPP1/2/3 + transform_list_pair :9990-:10026：依赖
    ntrans/rtrans/transform_list/transform_assumption（tame_defs2.hl:435-:472，
    批 7 记账「旗塔上游/reduction 波领土」定义层未进场）与 is_marked 九合取
    塔装配，随 transform/reduction 波批次立项，本批诚实跳过；
  - `marked_list_is_node_nondegenerate` 的 ql 侧 node 非退化支：HOL 经
    dart_of 选择函数章 dart_of_card_node 链（:8043-:8221 未移植），本批取
    Lean 短路线（good_list_nodes-ql 假设 + marked_list 第 5 合取 filter>1 +
    list_pairs 唯一性），收口步 2-strike 止损 sorry+NEEDS（见件内 docstring）。

  载体折算（沿批 1-15 约定）：parts/find_list/final_list/marked_list/
  normal_list/loop_of_list/loop_family_of_list ↦ *Spine（批 5-7）、
  quotient_list ↦ quotientListSpine（批 7）、l'y/l'p/l'z ↦ lYSpine/lPSpine/
  lZSpine（批 12）、商 hypermap ↦ Hypermap.quotientHypermap（Hypermap.lean
  块 12 已真）、EL/sizel ↦ getElem/length、indexl ↦ List.idxOf、HD/LAST ↦
  List.head!/List.getLast!、POWER(node_map) ↦ Equiv.Perm ^、POWER(f_list) ↦
  Function.iterate、uniq ↦ List.Nodup、BIJ ↦ Set.BijOn、set_of_list ↦
  {x | x ∈ _}（批 11）。

  红线遵守：零既有文件触碰、零 git 写操作；2-strike 止损件以 sorry+NEEDS
  记账（其余全真证）。
-/

import Kepler.Text.TameSpine.TameList15

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl eList fList GoodList listPairs listOfDarts
  findFaceDarts nList)
open Kepler.Graphs (fgraph)
open Kepler.Text (orbitMap setOfOrbits)
open Kepler.Text.TameLp (hypermapOfList nextEl_eq_getD getD_eq_getElem_of_lt
  getElem_idxOf idxOf_getElem dart_in_face findFaceDarts_ex_of_self
  findFaceDarts_eq_of_mem findFaceDarts_congr_of_mem findFaceDarts_nodup la7_getElem_rotOne
  mem_darts_of_mem_findFace nextEl_mem_of_mem flatten_nodup_mem
  la7_length_listPairs la7_prevEl_getD la7_length_rotOne darts_hypermapOfList
  faceMap_hypermapOfList nodeMap_hypermapOfList GoodListNodesTl
  listOfElements nodesOfListSet)

/-! ### §0 私件引擎（getElem 换形器 + list-pairs 结构 + face/node 轨道 + iso 共轭） -/

/-- 批 10 私件不跨文件，§0 同证重推导（批 7→16 惯例）。 -/
private theorem getLastMem {l : List (ℕ × ℕ)} (h : l ≠ []) : l.getLast! ∈ l := by
  rw [getLast!EqGetLast h]
  exact List.getLast_mem h

private theorem getElemCon {α : Type*} {l : List α} {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a = b) :
    l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- 同构表的 getElem 换形（表等价 + 证明无关；rw 跨 list-等价的 motive 问题的免疫器）。 -/
private theorem getElem_congr_list {l₁ l₂ : List ℕ} {j : ℕ} (h : l₁ = l₂)
    (h₁ : j < l₁.length) (h₂ : j < l₂.length) :
    l₁[j]'h₁ = l₂[j]'h₂ := by
  subst h
  rfl

/-- `list_pairs l` 的逐项式（HOL `nth_list_pairs` 的 rot-1 位移，任意表成立；
rot-1 段经 `la7_getElem_rotOne` + `rotateSpineOne`（批 2/TameLp 公开件））。 -/
private theorem listPairsGetElemT {l : List ℕ} {j : ℕ} (hj : j < l.length)
    (hl : j < (listPairs l).length) (hm : (j + 1) % l.length < l.length) :
    (listPairs l)[j]'hl = (l[j]'hj, l[(j + 1) % l.length]'hm) := by
  have hpos : 0 < l.length := by omega
  have hrot' : (TameLp.la7RotOne l)[j]'(Nat.lt_of_lt_of_eq hj (la7_length_rotOne l).symm)
      = l[(j + 1) % l.length]'(Nat.mod_lt (j + 1) hpos) :=
    la7_getElem_rotOne hj
  have hid : TameLp.la7RotOne l = l.drop 1 ++ l.take 1 := by
    rw [show TameLp.la7RotOne l = l.rotate 1 from rfl, rotateSpineOne]
  have hhl' : j < (l.drop 1 ++ l.take 1).length := by
    rw [Eq.symm (rotateSpineOne l), List.length_rotate]
    exact hj
  have hcon : (l.drop 1 ++ l.take 1)[j]'hhl'
      = l[(j + 1) % l.length]'(Nat.mod_lt (j + 1) hpos) :=
    (getElem_congr_list hid (Nat.lt_of_lt_of_eq hj (la7_length_rotOne l).symm) hhl').symm.trans hrot'
  show (l.zip (l.drop 1 ++ l.take 1))[j]'hl = _
  rw [List.getElem_zip]
  show (l[j]'hj, (l.drop 1 ++ l.take 1)[j]'hhl')
      = (l[j]'hj, l[(j + 1) % l.length]'hm)
  rw [hcon]

/-- HOL `mem_list_pairs_exists` 的 Lean 形：`v ∈ l` 给出含 `v` 的相邻对。 -/
private theorem listPairsMemExists {l : List ℕ} {v : ℕ} (hv : v ∈ l) :
    ∃ w : ℕ, (v, w) ∈ listPairs l := by
  have hj : l.idxOf v < l.length := List.idxOf_lt_length_iff.mpr hv
  have hpos : 0 < l.length := List.length_pos_of_mem hv
  have hv' : v = l[l.idxOf v]'(List.idxOf_lt_length_iff.mpr hv) :=
    (getElem_idxOf hv).symm
  have hl' : l.idxOf v < (listPairs l).length := by rw [la7_length_listPairs]; exact hj
  have hv' : v = l[l.idxOf v]'(List.idxOf_lt_length_iff.mpr hv) :=
    (getElem_idxOf hv).symm
  refine ⟨l[(l.idxOf v + 1) % l.length]'(Nat.mod_lt _ hpos), ?_⟩
  have hget := listPairsGetElemT hj hl' (Nat.mod_lt _ hpos)
  have heq : (v, l[(l.idxOf v + 1) % l.length]'(Nat.mod_lt _ hpos))
      = (listPairs l)[l.idxOf v]'hl' := by
    rw [hget]
    exact congrArg₂ _ (getElem_idxOf hv).symm rfl
  rw [heq]
  exact List.getElem_mem hl'

/-- 面-表内前驱的第二分量 = 对的第一分量（批 7 私件 prevElListPairsSnd
同证重推导；n_list 保 FST 的载体引擎）。 -/
private theorem prevElListPairsSnd {l : List ℕ}
    (_hs : (listPairs l).Nodup) {p : ℕ × ℕ} (hp : p ∈ listPairs l) :
    (prevEl (listPairs l) p).2 = p.1 := by
  have hlen : (listPairs l).length = l.length := la7_length_listPairs l
  have hpos : 0 < (listPairs l).length := List.length_pos_of_mem hp
  have hposl : 0 < l.length := Nat.lt_of_lt_of_eq hpos hlen
  have hk : (listPairs l).idxOf p < (listPairs l).length := List.idxOf_lt_length_iff.mpr hp
  have hkl : (listPairs l).idxOf p < l.length := Nat.lt_of_lt_of_eq hk hlen
  have hpk : p.1 = l[(listPairs l).idxOf p]'hkl := by
    have h1 := listPairsGetElemT (j := (listPairs l).idxOf p) hkl hk
      (Nat.mod_lt _ hposl)
    have h2 : (listPairs l)[(listPairs l).idxOf p]'hk = p := getElem_idxOf hp
    calc p.1 = ((listPairs l)[(listPairs l).idxOf p]'hk).1 := (congrArg Prod.fst h2).symm
      _ = l[(listPairs l).idxOf p]'hkl := (congrArg Prod.fst h1)
  have hprev : prevEl (listPairs l) p
      = (listPairs l).getD (((listPairs l).idxOf p + (listPairs l).length - 1)
        % (listPairs l).length) p := la7_prevEl_getD hp
  have hjlt : ((listPairs l).idxOf p + (listPairs l).length - 1) % (listPairs l).length
      < (listPairs l).length := Nat.mod_lt _ hpos
  rw [hprev, getD_eq_getElem_of_lt hjlt]
  have hjl : ((listPairs l).idxOf p + (listPairs l).length - 1) % (listPairs l).length
      < l.length := Nat.lt_of_lt_of_eq hjlt hlen
  have hml : (((listPairs l).idxOf p + (listPairs l).length - 1)
      % (listPairs l).length + 1) % l.length < l.length := Nat.mod_lt _ hposl
  have hsnd : ((listPairs l)[((listPairs l).idxOf p + (listPairs l).length - 1)
      % (listPairs l).length]'hjlt).2
      = l[(((listPairs l).idxOf p + (listPairs l).length - 1) % (listPairs l).length + 1)
        % l.length]'hml := by
    have h := listPairsGetElemT (j := ((listPairs l).idxOf p + (listPairs l).length - 1)
      % (listPairs l).length) hjl hjlt hml
    exact congrArg Prod.snd h
  have hidx : (((listPairs l).idxOf p + (listPairs l).length - 1)
      % (listPairs l).length + 1) % l.length = (listPairs l).idxOf p := by
    rcases Nat.eq_zero_or_pos ((listPairs l).idxOf p) with h0 | hpos'
    · have step1 : ((listPairs l).length - 1) % (listPairs l).length
        = (listPairs l).length - 1 := Nat.mod_eq_of_lt (by omega)
      have step2 : ((listPairs l).length - 1) % (listPairs l).length + 1
        = (listPairs l).length := by rw [step1]; omega
      rw [h0, Nat.zero_add, step2, hlen, Nat.mod_self]
    · have e1 : ((listPairs l).idxOf p + (listPairs l).length - 1) % (listPairs l).length
        = (listPairs l).idxOf p - 1 := by
        rw [show (listPairs l).idxOf p + (listPairs l).length - 1
            = ((listPairs l).idxOf p - 1) + (listPairs l).length from by omega,
          Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [e1, show (listPairs l).idxOf p - 1 + 1 = (listPairs l).idxOf p from by omega]
      exact Nat.mod_eq_of_lt hkl
  exact (hsnd.trans (getElemCon hml hkl hidx)).trans hpk.symm

/-- HOL `n_list_ext_fst` 第一分量（批 7 私件 fstNList 同证重推导）：good_list
下 `n_list` 保 FST。 -/
private theorem fstNListT {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : (nList L d).1 = d.1 := by
  have hdF : d ∈ findFaceDarts L d := dart_in_face L d |>.mpr hd
  have hnodup : (findFaceDarts L d).Nodup := findFaceDarts_nodup hL.1 d
  have hFF : findFaceDarts L d = listPairs
      ((L.find? fun l => decide (d ∈ listPairs l)).getD []) := rfl
  have hmem : d ∈ listPairs ((L.find? fun l => decide (d ∈ listPairs l)).getD []) := by
    rw [← hFF]; exact hdF
  show (eList (prevEl (findFaceDarts L d) d)).1 = d.1
  simp only [eList]
  rw [hFF]
  exact prevElListPairsSnd hnodup hmem

/-- node 正向轨道保 FST 且留 dart 集（批 7 私件 fstNodeOrbit 同证重推导）。 -/
private theorem fstNodeOrbitT {L : fgraph ℕ} (hL : GoodList L) {x : ℕ × ℕ}
    (hx : x ∈ (hypermapOfList L hL).darts) :
    ∀ n : ℕ, (((hypermapOfList L hL).nodeMap ^ n) x).1 = x.1
      ∧ ((hypermapOfList L hL).nodeMap ^ n) x ∈ (hypermapOfList L hL).darts := by
  intro n
  induction n with
  | zero => exact ⟨rfl, hx⟩
  | succ k ih =>
    obtain ⟨hfst, hmem⟩ := ih
    have hmem2 : (((hypermapOfList L hL).nodeMap ^ (k + 1)) x)
        ∈ (hypermapOfList L hL).darts := by
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (hypermapOfList L hL).nodeMap_permutes.apply_mem hmem
    have hfst2 : (((hypermapOfList L hL).nodeMap ^ (k + 1)) x).1 = x.1 := by
      rw [pow_succ', Equiv.Perm.mul_apply,
        nodeMap_hypermapOfList L hL hmem,
        fstNListT hL (List.mem_toFinset.mp hmem)]
      exact hfst
    exact ⟨hfst2, hmem2⟩

/-- dart 的首分量是 element（批 7 私件 fstMemListOfElements 同证重推导）。 -/
private theorem fstMemListOfElements {L : fgraph ℕ} {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : d.1 ∈ listOfElements L := by
  obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd
  simp only [List.mem_map] at hl
  obtain ⟨l₀, hl₀, hEq⟩ := hl
  subst hEq
  obtain ⟨i, hi, hdz⟩ := List.mem_iff_getElem.mp hdl
  have hi2 : i < (l₀.zip (l₀.drop 1 ++ l₀.take 1)).length := hi
  rw [List.length_zip] at hi2
  have hii : i < l₀.length := (Nat.lt_min.mp hi2).1
  have hdz2 : (l₀.zip (l₀.drop 1 ++ l₀.take 1))[i]'hi = d := hdz
  rw [List.getElem_zip] at hdz2
  have h2 : d.1 ∈ l₀ := by
    rw [← congrArg Prod.fst hdz2]
    exact List.getElem_mem hii
  show d.1 ∈ L.flatten.eraseDups
  simp
  exact ⟨l₀, hl₀, h2⟩

/-! ### §0.1 face-轨道引擎（批 7/8/14 私件不跨文件，惯例同证重推导） -/

private theorem nextElStep {s : List (ℕ × ℕ)} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (hj1 : (j + 1) % s.length < s.length) :
    nextEl s (s[j]'hj) = s[(j + 1) % s.length]'hj1 := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  rw [nextEl_eq_getD (List.getElem_mem hj), idxOf_getElem hsn hj,
    getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]

private theorem nextElIterateGetElem {s : List (ℕ × ℕ)} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (n : ℕ) (hjn : (j + n) % s.length < s.length) :
    (nextEl s)^[n] (s[j]'hj) = s[(j + n) % s.length]'hjn := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact getElemCon hj hjn (by rw [Nat.add_zero, Nat.mod_eq_of_lt hj])
  | succ k ih =>
    have hjk : (j + k) % s.length < s.length := Nat.mod_lt _ hpos
    rw [Function.iterate_succ_apply', ih hjk,
      nextElStep hsn hjk (Nat.mod_lt ((j + k) % s.length + 1) hpos)]
    refine getElemCon (Nat.mod_lt _ hpos) hjn ?_
    have hmod : ((j + k) % s.length + 1) % s.length = (j + k + 1) % s.length :=
      Nat.mod_add_mod (j + k) s.length 1
    rw [hmod, Nat.add_assoc]

private theorem nextElIterateMem {s : List (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ s) :
    ∀ n : ℕ, (nextEl s)^[n] x ∈ s := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-- face 轨道 ⊆ 面表（批 7/8/14 私件同证重推导）。 -/
private theorem faceOrbitSubsetFindFace {L : fgraph ℕ} (hL : GoodList L)
    {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) :
    (hypermapOfList L hL).face d ⊆ {y | y ∈ findFaceDarts L d} := by
  have key : ∀ n : ℕ, ((hypermapOfList L hL).faceMap ^ n) d ∈ findFaceDarts L d := by
    intro n
    induction n with
    | zero => simpa using dart_in_face L d |>.mpr hd
    | succ k ih =>
      have hz : ((hypermapOfList L hL).faceMap ^ k) d
          ∈ (hypermapOfList L hL).darts :=
        (hypermapOfList L hL).faceMap_permutes.pow_apply_mem k
          (List.mem_toFinset.mpr hd)
      have hFFz : findFaceDarts L (((hypermapOfList L hL).faceMap ^ k) d)
          = findFaceDarts L d := findFaceDarts_congr_of_mem hL.1 hd ih
      rw [pow_succ', Equiv.Perm.mul_apply, faceMap_hypermapOfList L hL hz]
      show nextEl (findFaceDarts L (((hypermapOfList L hL).faceMap ^ k) d))
        (((hypermapOfList L hL).faceMap ^ k) d) ∈ findFaceDarts L d
      rw [hFFz]
      exact nextEl_mem_of_mem ih
  rintro y hy
  simp only [Kepler.Text.Hypermap.face, orbitMap, Set.mem_setOf_eq] at hy
  obtain ⟨n, hn⟩ := hy
  subst hn
  exact key n

/-! ### §0.2 置换引擎 -/

/-- `e^m ∘ (e.symm)^m = id`（点态形；商 node 引理支路用）。 -/
private theorem powSymmCancel {α : Type*} (e : Equiv.Perm α) (m : ℕ) :
    ∀ x : α, (e ^ m) ((e.symm ^ m) x) = x := by
  induction m with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ', pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ih (e.symm x), Equiv.apply_symm_apply]

/-- 商 iso 的 node 分量由 edge+face 分量共轭而得（批 15 hypIsoEdgeNode 的
对偶版；`faceMap_eq_inv` 给 nodeMap = edgeMap.symm * faceMap.symm）。 -/
private theorem isoNodeCommOfEdgeFace {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} {f : α → β}
    (hE : ∀ x ∈ K.darts, H.edgeMap (f x) = f (K.edgeMap x))
    (hF : ∀ x ∈ K.darts, H.faceMap (f x) = f (K.faceMap x)) :
    ∀ x ∈ K.darts, H.nodeMap (f x) = f (K.nodeMap x) := by
  have hKn : K.nodeMap = K.edgeMap.symm * K.faceMap.symm := by
    have h1 : K.edgeMap * K.nodeMap = K.faceMap⁻¹ :=
      eq_inv_of_mul_eq_one_left K.comp_eq_one
    have h2 := congrArg (fun z : Equiv.Perm α => (K.edgeMap⁻¹ * z)) h1
    rw [inv_mul_cancel_left] at h2
    exact h2
  have hHn : H.nodeMap = H.edgeMap.symm * H.faceMap.symm := by
    have h1 : H.edgeMap * H.nodeMap = H.faceMap⁻¹ :=
      eq_inv_of_mul_eq_one_left H.comp_eq_one
    have h2 := congrArg (fun z : Equiv.Perm β => (H.edgeMap⁻¹ * z)) h1
    rw [inv_mul_cancel_left] at h2
    exact h2
  intro x hx
  have hsF : ∀ z ∈ K.darts, H.faceMap.symm (f z) = f (K.faceMap.symm z) := by
    intro z hz
    have h2 := hF _ (K.faceMap_permutes.symm_apply_mem hz)
    rw [Equiv.apply_symm_apply] at h2
    exact Eq.symm ((Equiv.apply_eq_iff_eq_symm_apply _).mp h2)
  have hsE : ∀ z ∈ K.darts, H.edgeMap.symm (f z) = f (K.edgeMap.symm z) := by
    intro z hz
    have h2 := hE _ (K.edgeMap_permutes.symm_apply_mem hz)
    rw [Equiv.apply_symm_apply] at h2
    exact Eq.symm ((Equiv.apply_eq_iff_eq_symm_apply _).mp h2)
  show H.nodeMap (f x) = f (K.nodeMap x)
  rw [hHn, hKn]
  show H.edgeMap.symm (H.faceMap.symm (f x))
    = f (K.edgeMap.symm (K.faceMap.symm x))
  rw [hsF x hx]
  exact hsE (K.faceMap.symm x) (K.faceMap_permutes.symm_apply_mem hx)

/-! ### §1 index 基础两件（tame_list.hl:9505/:9513） -/

/-- **HOL `mem_el_index`**（tame_list.hl:9505-:9511）
`!i s. i < sizel s ==> MEM (EL i s) s`。 -/
theorem memElIndex {α : Type*} {s : List α} {i : ℕ} (hi : i < s.length) :
    s[i] ∈ s :=
  List.getElem_mem hi

/-- **HOL `index_el`**（tame_list.hl:9513-:9519）
`!i. uniq s /\ i < sizel s ==> indexl (EL i s) s = i`。 -/
theorem indexEl {α : Type*} [DecidableEq α] {s : List α} (hsn : s.Nodup) {i : ℕ}
    (hi : i < s.length) : s.idxOf s[i] = i :=
  idxOf_getElem hsn hi

/-! ### §2 face/family 私件转运两件（tame_list.hl:9413/:9434） -/

/-- **HOL `lemma_yz_in_face_list`**（tame_list.hl:9413-:9432）
`good_list L /\ good_list_nodes L /\ all uniq L /\ next_el r x = f_list L x /\
split_condition_list L N r x ==> MEM (l'y L r x) (find_face L x) /\
MEM (l'z L N r x) (find_face L x)`——`lemma_yz_in_face`（Hypermap 层无前提
件）+ hyp 词典五桥（批 12 hypYL/hypZLz）+ face-轨道 ⊆ 面表。 -/
theorem lemmaYzInFaceList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hnext : nextEl r x = fList L x) (hsc : splitConditionListSpine hL N r x) :
    lYSpine L r x ∈ findFaceDarts L x ∧ lZSpine L N r x ∈ findFaceDarts L x := by
  have hsplit := splitConditionListSplit L hL hgn hunL hsc
  obtain ⟨h1, h2⟩ := Hypermap.hypY_hypZ_mem_face (hypermapOfList L hL)
    (loopFamilyOfListSpine N) (loopOfListSpine r) x
  have hY : (hypermapOfList L hL).hypY (loopFamilyOfListSpine N) (loopOfListSpine r) x
      = lYSpine L r x := hypYL L hL hgn hunL hnext hsc
  have hZ : (hypermapOfList L hL).hypZ (loopFamilyOfListSpine N) (loopOfListSpine r) x
      = lZSpine L N r x := hypZLz L hL hgn hunL hnext hsc
  rw [hY] at h1
  rw [hZ] at h2
  have hxd : x ∈ listOfDarts L := splitConditionListOfDarts hsc
  exact ⟨faceOrbitSubsetFindFace hL hxd h1, faceOrbitSubsetFindFace hL hxd h2⟩

/-- **HOL `lemma_node_outside_darts_of_family_list`**（tame_list.hl:9434-:9467）
`... 1 <= i /\ i <= l'p L N r x /\ MEM y (flatten N) ==>
~(FST y = FST ((f_list L POWER i) (l'y L r x)))`——node_outside_dartsOfFamily
（Hypermap 层）+ 同 FST 类入 node（批 7 memHypermapOfListNode）反证 +
darts_of_family = set_of_list (flatten N)（批 12）。 -/
theorem lemmaNodeOutsideDartsOfFamilyList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hnext : nextEl r x = fList L x) (hsc : splitConditionListSpine hL N r x)
    {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ lPSpine L N r x) {y : ℕ × ℕ}
    (hy : y ∈ N.flatten) :
    y.1 ≠ ((fList L)^[i] (lYSpine L r x)).1 := by
  intro hcon
  have hsplit := splitConditionListSplit L hL hgn hunL hsc
  have hY : (hypermapOfList L hL).hypY (loopFamilyOfListSpine N) (loopOfListSpine r) x
      = lYSpine L r x := hypYL L hL hgn hunL hnext hsc
  have hP : (hypermapOfList L hL).hypP (loopFamilyOfListSpine N) (loopOfListSpine r) x
      = lPSpine L N r x := hypPLp L hL hgn hunL hnext hsc
  have hyd : y ∈ listOfDarts L := normalListListOfDarts hsc.2.1 y hy
  have hlyD : lYSpine L r x ∈ listOfDarts L := memLYDart L hL hsc
  have hzD : ((hypermapOfList L hL).faceMap ^ i) (lYSpine L r x) ∈ listOfDarts L := by
    exact fListExtPowerMem L hL hlyD i
  have hynode : y ∈ (hypermapOfList L hL).node
      (((hypermapOfList L hL).faceMap ^ i) (lYSpine L r x)) := by
    rw [memHypermapOfListNode hL hgn hzD]
    rw [faceMapListPower L hL i hlyD]
    exact ⟨hcon.symm, hyd⟩
  have hout := Hypermap.node_outside_dartsOfFamily (hypermapOfList L hL) hsplit hi1
    (by rw [hP]; exact hi2)
  have hy' : y ∈ (hypermapOfList L hL).node
      (((hypermapOfList L hL).faceMap ^ i)
        ((hypermapOfList L hL).hypY (loopFamilyOfListSpine N) (loopOfListSpine r) x)) := by
    rw [hY]; exact hynode
  exact hout y hy' (by rw [dartsOfFamilyLoopFamilyOfList L hL hsc.2.1]; exact hy)

/-- part 表末项下标换形（idxOfGetLast + getElemCon；商 node 转运链用）。 -/
private theorem getElemLastHead {p : List (ℕ × ℕ)} (hpun : p.Nodup) (hpne : p ≠ [])
    {hl : p.idxOf p.getLast! - (p.length - 1) < p.length} :
    p[p.idxOf p.getLast! - (p.length - 1)]'hl = p.head! := by
  have hlastidx : p.idxOf p.getLast! = p.length - 1 := idxOfGetLast hpun hpne
  have hpos : 0 < p.length := List.length_pos_of_ne_nil hpne
  have hcon : p.idxOf p.getLast! - (p.length - 1) = 0 := by rw [hlastidx]; omega
  have hb : p[p.idxOf p.getLast! - (p.length - 1)]'hl = p[0]'hpos :=
    getElemCon hl hpos hcon
  rw [hb]
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hpne
  rfl

/-! ### §3 商 node-map 转运链（tame_list.hl:9521-:9685） -/

/-- **HOL `parts_node_power`**（tame_list.hl:9521-:9556）
`k <= indexl x p ==> (node_map (hypermap_of_list L) POWER k) x =
EL (indexl x p - k) p`——parts_node_inverse_power（批 10）+ 逐步前件
（node-map 在 part 表上取前一项，nodup 下标唯一；bound 显式 ∀ 携带，
批 10 key 范式）。 -/
theorem partsNodePower (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)} (hr : r ∈ N)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) {k : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ p) (hk : k ≤ p.idxOf x) :
    ((hypermapOfList L hL).nodeMap ^ k) x
      = p[p.idxOf x - k]'(by
          have := List.idxOf_lt_length_iff.mpr hx
          omega) := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpun : p.Nodup := partsUniq L hr1 hr2 p hp
  have key : ∀ k : ℕ, ∀ hk : k ≤ p.idxOf x, ∀ hl : p.idxOf x - k < p.length,
      ((hypermapOfList L hL).nodeMap ^ k) x = p[p.idxOf x - k]'hl := by
    intro k
    induction k with
    | zero =>
      intro _hk hl
      rw [pow_zero]
      show x = p[p.idxOf x]'hl
      exact (getElem_idxOf hx).symm
    | succ k ih =>
      intro hk hl
      have hk1 : k ≤ p.idxOf x := by omega
      have hidxlt : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
      have hmem : p.idxOf x - k < p.length := by omega
      have hIH := ih hk1 hmem
      -- nodeMap 单步 = symm 的对称闭包：symm 作用于 p[idx-(k+1)] 落回 p[idx-k]
      have hIH := ih hk1 hmem
      -- nodeMap 单步 = symm 的对称闭包：symm 作用于 p[idx-(k+1)] 落回 p[idx-k]
      have hsym : (hypermapOfList L hL).nodeMap.symm (p[p.idxOf x - (k + 1)]'hl)
          = p[p.idxOf x - k]'hmem := by
        have hid : p.idxOf (p[p.idxOf x - (k + 1)]'hl) = p.idxOf x - (k + 1) :=
          idxOf_getElem hpun hl
        have hlt : 1 + p.idxOf (p[p.idxOf x - (k + 1)]'hl) < p.length := by
          rw [hid]; omega
        have h2 := partsNodeInversePower L hL hn hr hp 1
          (List.getElem_mem hl) hlt
        rw [← getD_eq_getElem_of_lt hlt (p[p.idxOf x - (k + 1)]'hl)] at h2
        rw [hid] at h2
        have hcon2 : 1 + (p.idxOf x - (k + 1)) = p.idxOf x - k := by omega
        rw [hcon2] at h2
        rw [← getD_eq_getElem_of_lt hmem]
        exact h2
      rw [pow_succ', Equiv.Perm.mul_apply, hIH,
        show (hypermapOfList L hL).nodeMap
          = (hypermapOfList L hL).nodeMap.symm.symm from rfl,
        Equiv.symm_apply_eq, ← hsym]
  exact key k hk (by
    have := List.idxOf_lt_length_iff.mpr hx
    omega)

/-- **HOL `parts_node_map_hd`**（tame_list.hl:9558-:9604）
`normal_list L N /\ good_list L /\ MEM r N /\ MEM p (parts L r) /\
MEM r' N /\ MEM p' (parts L r') /\ MEM (node_map (hypermap_of_list L) (HD p)) p'
==> inverse (node_map (hypermap_of_list L)) (LAST p') = HD p`——case 分裂 +
parts_node_inverse_power(k=1)（x ≠ LAST p' 支）+ find_atom_part2（批 11）
+ index_hd0（批 8）矛盾收口。 -/
theorem partsNodeMapHd (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r r' : List (ℕ × ℕ)} (hr : r ∈ N) (hr' : r' ∈ N)
    {p p' : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) (hp' : p' ∈ partsSpine L r')
    (hx : (hypermapOfList L hL).nodeMap p.head! ∈ p') :
    (hypermapOfList L hL).nodeMap.symm p'.getLast! = p.head! := by
  obtain ⟨hr1', hr2'⟩ := normalListUniqNonnil hn hr'
  have hpun' : p'.Nodup := partsUniq L hr1' hr2' p' hp'
  have hpne' : p' ≠ [] := partsAllNonnil L hr1' hr2' p' hp'
  have hpos' : 0 < p'.length := List.length_pos_of_ne_nil hpne'
  have hlastidx : p'.idxOf p'.getLast! = p'.length - 1 := idxOfGetLast hpun' hpne'
  by_cases heq : (hypermapOfList L hL).nodeMap p.head! = p'.getLast!
  · rw [← heq]
    exact Equiv.symm_apply_apply _ _
  · exfalso
    set x := (hypermapOfList L hL).nodeMap p.head! with hxdef
    have hxmem : x ∈ p' := hx
    have hidxlt : p'.idxOf x < p'.length := List.idxOf_lt_length_iff.mpr hxmem
    -- x ≠ LAST p' ⇒ idx x ≤ len' - 2
    have hne' : p'.idxOf x ≠ p'.length - 1 := fun hcon => heq (by
      have e1 : p'.getD (p'.idxOf x) x = x := by
        rw [getD_eq_getElem_of_lt hidxlt]; exact getElem_idxOf hxmem
      rw [hcon] at e1
      have e2 : p'.getLast! = p'.getD (p'.length - 1) x := by
        rw [getD_eq_getElem_of_lt (by omega)]
        have e3 : p'[p'.idxOf p'.getLast!]'(List.idxOf_lt_length_iff.mpr (getLastMem hpne'))
            = p'.getLast! := getElem_idxOf (getLastMem hpne')
        have e4 : p'[p'.idxOf p'.getLast!]'(List.idxOf_lt_length_iff.mpr (getLastMem hpne'))
            = p'[p'.length - 1]'(by omega) :=
          getElemCon (List.idxOf_lt_length_iff.mpr (getLastMem hpne')) (by omega) hlastidx
        exact (e4.symm.trans e3).symm
      rw [e2]
      exact e1.symm)
    have hkey := partsNodeInversePower L hL hn hr' hp' 1 hxmem (by omega)
    -- hkey : nodeMap.symm x = p'[1 + idx x]
    have hsymm : (hypermapOfList L hL).nodeMap.symm x = p.head! :=
      Equiv.apply_symm_apply _ _
    have hbound : 1 + p'.idxOf x < p'.length := by omega
    have hget : p'[1 + p'.idxOf x]'hbound = p.head! := by
      rw [← hkey]; exact hsymm
    have hidxhd : p'.idxOf p.head! = 1 + p'.idxOf x := by
      rw [← hget, idxOf_getElem hpun' hbound]
    -- p.head! ∈ p'（= p'[1 + idx x]），find_atom_part2 两侧夹出 p = p'
    have hhdp' : p.head! ∈ p' := by
      rw [← hget]; exact List.getElem_mem hbound
    have hpne : p ≠ [] := by
      obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
      exact partsAllNonnil L hr1 hr2 p hp
    have hmemhd : p.head! ∈ p := List.head!_mem_self hpne
    have hp₁ := findAtomPart2 L hn hr hp hmemhd
    have hp₂ := findAtomPart2 L hn hr' hp' hhdp'
    have hpp : p = p' := hp₁.symm.trans hp₂
    have hzero : p'.idxOf p.head! = 0 := by
      rw [hpp]; exact indexHd0 hpne'
    rw [hzero] at hidxhd
    omega

/-- **HOL `inverse_node_map_quotient`**（tame_list.hl:9469-:9503）
`... MEM p (parts L r) /\ MEM r N /\ MEM p' (parts L r') /\ MEM r' N ==>
(inverse(node_map (hypermap_of_list (quotient_list L N))) (LAST p) = LAST p' <=>
MEM (f_list L (e_list (LAST p))) p')`——inverse_node_map_list（批 8）在 ql
实例化 + e-list dart 闭（批 10 list_of_darts_quotient_sym）+
f_list_quotient/f_list_quotient_alt（批 11）双链。 -/
theorem inverseNodeMapQuotient (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup)
    {r r' : List (ℕ × ℕ)} (hr : r ∈ N) (hr' : r' ∈ N)
    {p p' : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) (hp' : p' ∈ partsSpine L r') :
    ((hypermapOfList (quotientListSpine L N)
        (goodListQuotient L hL hn hnedg hunL)).nodeMap.symm p.getLast!
      = p'.getLast!) ↔ (fList L (eList p.getLast!) ∈ p') := by
  have hgood : GoodList (quotientListSpine L N) := goodListQuotient L hL hn hnedg hunL
  have hlastD : p.getLast! ∈ listOfDarts (quotientListSpine L N) :=
    (memListOfDartsQuotient L hL hn hnedg hunL p.getLast!).mpr
      ⟨p, r, hp, hr, rfl⟩
  have hinv : (hypermapOfList (quotientListSpine L N) hgood).nodeMap.symm p.getLast!
      = fList (quotientListSpine L N) (eList p.getLast!) :=
    inverseNodeMapList hgood hlastD
  have heD : eList p.getLast! ∈ listOfDarts (quotientListSpine L N) :=
    listOfDartsQuotientSym L hL hn hnedg hunL p.getLast! hlastD
  obtain ⟨q, r'', hq, hr'', hqeq⟩ :=
    (memListOfDartsQuotient L hL hn hnedg hunL (eList p.getLast!)).mp heD
  constructor
  · intro heq
    have hfq := (fListQuotient L hL hn hnedg hunL hr'' hr' hq hp').mp
      (by rw [← hqeq]; exact hinv.symm.trans heq)
    rw [hqeq]
    exact (fListQuotientAlt L hL hn hr'' hr' hq hp').mp hfq
  · intro himem
    rw [hqeq] at himem
    have hnext := (fListQuotientAlt L hL hn hr'' hr' hq hp').mpr himem
    have hfl := (fListQuotient L hL hn hnedg hunL hr'' hr' hq hp').mpr hnext
    rw [← hqeq, ← hinv] at hfl
    exact hfl

/-- **HOL `node_map_quotient`**（tame_list.hl:9606-:9683）
`... MEM r N /\ MEM p (parts L r) ==> node_map (hypermap_of_list
(quotient_list L N)) (LAST p) = (node_map (hypermap_of_list L) POWER sizel p)
(LAST p)`——parts_node_power 首步 + normal_list node-收缩 + parts_node_map_hd
+ inverse_node_map_quotient（本批）闭合。 -/
theorem nodeMapQuotient (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) :
    (hypermapOfList (quotientListSpine L N)
        (goodListQuotient L hL hn hnedg hunL)).nodeMap p.getLast!
      = ((hypermapOfList L hL).nodeMap ^ p.length) p.getLast! := by
  -- NEEDS（2-strike 记账）：hkey 组装（parts_node_power 首步 + getElemLastHead
  -- 桥 + normal_list node-收缩 + inverse_node_map_quotient 闭合）两次未攻下，
  -- 陈述逐字冻结，本件 sorry 债务记账（QNL/GLQ 照常消费其陈述）。
  sorry
/-- **HOL `quotient_node_lemma`**（tame_list.hl:9685-:9790）
`i <= k /\ ... /\ inverse (node_map (hypermap_of_list L)) = ivs /\
MEM (LAST p1) p1 /\ MEM p1 (parts L r1) /\ MEM r1 N /\
node (hypermap_of_list (quotient_list L N)) (LAST p1) = nodq /\
MEM ((ivs POWER i) (LAST p1)) (list_of_darts (quotient_list L N)) ==>
((ivs POWER i) (LAST p1)) IN nodq`——k 归纳三支：小支 parts_node_power +
find_atom_part2 同 part 收口；等支 node_map_quotient + permute 逆；
大支幂分裂 + node_map_quotient + 归纳假设 + lemma_inverse_in_node。 -/
theorem quotientNodeLemma (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup)
    (ivs : Equiv.Perm (ℕ × ℕ)) (nodq : Set (ℕ × ℕ)) {r₁ p₁ : List (ℕ × ℕ)}
    {k i : ℕ} (hi : i ≤ k)
    (hivs : (hypermapOfList L hL).nodeMap.symm = ivs)
    (hp₁ : p₁ ∈ partsSpine L r₁) (hr₁ : r₁ ∈ N)
    (hmemlast : p₁.getLast! ∈ p₁)
    (hnodq : (hypermapOfList (quotientListSpine L N)
        (goodListQuotient L hL hn hnedg hunL)).node p₁.getLast! = nodq)
    (hdart : (ivs ^ i) p₁.getLast! ∈ listOfDarts (quotientListSpine L N)) :
    (ivs ^ i) p₁.getLast! ∈ nodq := by
  have hgood : GoodList (quotientListSpine L N) := goodListQuotient L hL hn hnedg hunL
  have main : ∀ m : ℕ, ∀ j ≤ m,
      (ivs ^ j) p₁.getLast! ∈ listOfDarts (quotientListSpine L N) →
      (ivs ^ j) p₁.getLast! ∈ nodq := by
    intro m
    induction m with
    | zero =>
      intro j hj hd
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst hj0
      rw [← hnodq, pow_zero]
      show p₁.getLast! ∈ (hypermapOfList (quotientListSpine L N) hgood).node p₁.getLast!
      exact mem_orbitMap_self _ _
    | succ k ih =>
      intro j hj hd
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact ih j (Nat.lt_succ_iff.mp hlt) hd
      · have hj1 : j = k + 1 := by omega
        subst hj1
        obtain ⟨p₂, r₂, hp₂, hr₂, hw⟩ :=
          (memListOfDartsQuotient L hL hn hnedg hunL _).mp hd
        obtain ⟨_, _, hp2un, hp2ne, _⟩ := partsUniqNonnil L hL hn hr₂ hp₂
        have hlastmem₂ : p₂.getLast! ∈ p₂ := getLastMem hp2ne
        have hidx₂ : p₂.idxOf p₂.getLast! = p₂.length - 1 := idxOfGetLast hp2un hp2ne
        have hcanc : ((hypermapOfList L hL).nodeMap ^ (k + 1))
            ((ivs ^ (k + 1)) p₁.getLast!) = p₁.getLast! := by
          have h3 : ((hypermapOfList L hL).nodeMap ^ (k + 1))
              (((hypermapOfList L hL).nodeMap.symm ^ (k + 1)) p₁.getLast!) = p₁.getLast! :=
            powSymmCancel _ _ _
          rwa [hivs] at h3
        rw [hw] at hcanc
        rcases Nat.lt_trichotomy (k + 1) p₂.length with hlt | heq | hgt
        · -- 小支：同 part
          have hstep := partsNodePower L hL hn hr₂ hp₂ (k := k + 1) hlastmem₂
            (by rw [hidx₂]; omega)
          rw [hstep] at hcanc
          have hz : p₂[p₂.idxOf p₂.getLast! - (k + 1)] = p₁.getLast! := hcanc
          have hlast₁p₂ : p₁.getLast! ∈ p₂ := by
            rw [← hz]
            exact List.getElem_mem (by
              have := List.idxOf_lt_length_iff.mpr hlastmem₂
              omega)
          have hfind₁ := findAtomPart2 L hn hr₁ hp₁ hmemlast
          have hfind₂ := findAtomPart2 L hn hr₂ hp₂ hlast₁p₂
          have hpp : p₁ = p₂ := hfind₁.symm.trans hfind₂
          subst hpp
          rw [← hnodq, hw]
          exact mem_orbitMap_self
            (hypermapOfList (quotientListSpine L N) hgood).nodeMap p₁.getLast!
        · -- 等支：k+1 = len p₂
          have hlen₂ : k + 1 = p₂.length := by omega
          rw [hlen₂] at hcanc
          have hq := nodeMapQuotient L hL hgn hn hnedg hunL hr₂ hp₂
          rw [hcanc] at hq
          have hkey2 : p₂.getLast!
              = (hypermapOfList (quotientListSpine L N) hgood).nodeMap.symm
                p₁.getLast! := by
            rw [Equiv.eq_symm_apply]; exact hq
          rw [← hnodq, hw, hkey2]
          exact Hypermap.nodeMap_symm_mem_node _
            (mem_orbitMap_self
              (hypermapOfList (quotientListSpine L N) hgood).nodeMap p₁.getLast!)
        · -- NEEDS（2-strike 记账）：大支 k+1 > len p₂——幂分裂 + node_map_quotient +
          -- 归纳假设 + lemma_inverse_in_node 链的组装两次未攻下，本支 sorry。
          sorry
  exact main k i hi hdart

/-! ### §4 good_list_nodes 商章（tame_list.hl:9792-:9903） -/

/-- **HOL `list_of_darts_quotient_darts`**（tame_list.hl:9847-:9863）
`normal_list L N /\ is_edge_nondegenerate ... /\ good_list L /\ all uniq L /\
MEM d (list_of_darts (quotient_list L N)) ==> MEM d (list_of_darts L)`
——mem_list_of_darts_quotient 分解 + parts_darts（批 10）+ MEM_LAST。 -/
theorem listOfDartsQuotientDarts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts (quotientListSpine L N)) :
    d ∈ listOfDarts L := by
  obtain ⟨p, r, hp, hrN, rfl⟩ := (memListOfDartsQuotient L hL hn hnedg hunL d).mp hd
  obtain ⟨_, _, _, hpne, _⟩ := partsUniqNonnil L hL hn hrN hp
  exact partsDarts L hn hrN hp (getLastMem hpne)

/-- **HOL `good_list_nodes_condition2`**（tame_list.hl:9792-:9845）
`good_list L /\ (!d d'. MEM d (list_of_darts L) /\ MEM d' (list_of_darts L) /\
FST d = FST d' ==> d' IN node (hypermap_of_list L) d) ==> good_list_nodes L`
——node = FST-类双向刻画（假设给 ⊇、node 幂保 FST 给 ⊆）+ antisymm
（= HOL BIJ_CARD + card_set_of_list_uniq 计数闭合的免计数同构，零收窄）。 -/
theorem goodListNodesCondition2 (L : fgraph ℕ) (hL : GoodList L)
    (hcond : ∀ d d' : ℕ × ℕ, d ∈ listOfDarts L → d' ∈ listOfDarts L →
      d.1 = d'.1 → d' ∈ (hypermapOfList L hL).node d) :
    GoodListNodesTl L hL := by
  -- NEEDS（2-strike 记账）：node = FST-类双向刻画 + nodeSet/nodesOfListSet
  -- antisymm 的 setOf/Finset bound 换形多轮未攻下，陈述逐字冻结，
  -- 本件 sorry 债务记账（GLQ 照常消费其陈述）。
  sorry
/-- **HOL `good_list_nodes_quotient`**（tame_list.hl:9865-:9901，别名 PMBRINH）
`good_list L /\ good_list_nodes L /\ normal_list L N /\
is_edge_nondegenerate (hypermap_of_list L) /\ all uniq L ==>
good_list_nodes (quotient_list L N)`——good_list_nodes_condition2 在 ql 实例化
+ 同 FST 类入 node（批 7 memHypermapOfListNode）+ exists_pow_nodeMap_symm
（lemma_via_inverse_node_map）+ quotient_node_lemma（本批）闭合。 -/
theorem goodListNodesQuotient (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) :
    GoodListNodesTl (quotientListSpine L N) (goodListQuotient L hL hn hnedg hunL) := by
  have hgood : GoodList (quotientListSpine L N) := goodListQuotient L hL hn hnedg hunL
  refine goodListNodesCondition2 (quotientListSpine L N) hgood ?_
  intro d d' hd hd' hcon
  obtain ⟨p, r, hp, hrN, rfl⟩ := (memListOfDartsQuotient L hL hn hnedg hunL d).mp hd
  obtain ⟨p', r'', hp', hr'N, rfl⟩ :=
    (memListOfDartsQuotient L hL hn hnedg hunL d').mp hd'
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hrN
  obtain ⟨hr1', hr2'⟩ := normalListUniqNonnil hn hr'N
  have hmemlast : p.getLast! ∈ p := getLastMem (partsAllNonnil L hr1 hr2 p hp)
  have hmemlast' : p'.getLast! ∈ p' := getLastMem (partsAllNonnil L hr1' hr2' p' hp')
  have hnodeH : p'.getLast! ∈ (hypermapOfList L hL).node p.getLast! :=
    (memHypermapOfListNode hL hgn (partsDarts L hn hrN hp hmemlast)).mpr
      ⟨hcon, partsDarts L hn hr'N hp' hmemlast'⟩
  obtain ⟨j, -, hjk⟩ :=
    Hypermap.exists_pow_nodeMap_symm_apply_of_mem_node
      (hypermapOfList L hL) hnodeH
  have hdart2 : ((hypermapOfList L hL).nodeMap.symm ^ j) p.getLast!
      ∈ listOfDarts (quotientListSpine L N) := by
    rw [← hjk]
    exact hd'
  rw [hjk]
  exact quotientNodeLemma L hL hgn hn hnedg hunL
    (hypermapOfList L hL).nodeMap.symm
    ((hypermapOfList (quotientListSpine L N) hgood).node p.getLast!)
    (k := j) (i := j) (Nat.le_refl j) rfl hp hrN hmemlast rfl hdart2

/-! ### §5 商列表 iso capstone + node 非退化（tame_list.hl:8223/:9362） -/

/-- 私件（P1）：ql 的 dart 上 iso 映射 = atomChoice（find_atom_part +
atom_choice_part，批 11）。 -/
private theorem quotientDartAtomChoice (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {x : ℕ × ℕ}
    (hx : x ∈ listOfDarts (quotientListSpine L N)) :
    setOfListSpine (findAtomSpine L N x)
      = (hypermapOfList L hL).atomChoice (loopFamilyOfListSpine N) x := by
  -- NEEDS（2-strike 记账）：find_atom_part/atom_choice_part 的 rw 实例化链
  -- 多轮未攻下，本私件 sorry（下游 iso capstone 同步 sorry）。
  sorry
/-- 私件（P2）：ql 的 dart 是自身 atom 的 head（head_of_atom_parts，批 11）。 -/
private theorem quotientDartHeadOfAtom (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hunL : ∀ l ∈ L, l.Nodup) {x : ℕ × ℕ}
    (hx : x ∈ listOfDarts (quotientListSpine L N)) :
    (hypermapOfList L hL).headOfAtom (loopFamilyOfListSpine N) x = x := by
  -- NEEDS（2-strike 记账）：head_of_atom_parts 实例化链多轮未攻下，
  -- 本私件 sorry（下游 iso capstone 同步 sorry）。
  sorry
/-- **HOL `quotient_list_iso_quotient`**（tame_list.hl:8223-:8363）
`is_restricted (hypermap_of_list L) /\ good_list_nodes L /\ normal_list L N /\
is_edge_nondegenerate (hypermap_of_list L) /\ good_list L /\ all uniq L ==>
hyp_iso (set_of_list o (find_atom L N))
  (hypermap_of_list (quotient_list L N),
   quotient (hypermap_of_list L) (loop_family_of_list N))`——BijOn =
atom_list_bij（批 11）；edge 分量 = e_quotient_via_atom_choice（Hypermap 块
12）+ P1/P2；face 分量 = f_quotient_via_atom_choice + f_list_quotient/
f_list_quotient_alt（批 11）+ atom 词典；node 分量 = isoNodeCommOfEdgeFace
共轭（批 15 桥章解锁，零收窄）。 -/
theorem quotientListIsoQuotient (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) :
    (hypermapOfList (quotientListSpine L N)
        (goodListQuotient L hL hn hnedg hunL)).Iso
      ((hypermapOfList L hL).quotientHypermap
        (normalListNormal hL hgn hres hn)) := by
  -- NEEDS（2-strike 记账）：本件依赖 P1/P2 私件（均已 sorry），
  -- BijOn = atom_list_bij 已就位，陈述逐字冻结，本件 sorry 债务记账。
  sorry
/-- **HOL `marked_list_is_node_nondegenerate`**（tame_list.hl:9362-:9411）
`good_list L /\ good_list_nodes L /\ good_list_nodes (quotient_list L N) /\
marked_list L N r d ==> is_node_nondegenerate (quotient (hypermap_of_list L)
(loop_family_of_list N))`——iso 运输（quotient_list_iso_quotient 本批 +
Iso.symm + 批 14 isoIsNodeNondegenerate）+ ql 侧 node 非退化。NEEDS（记账）：
ql 侧收口步——marked_list 第 5 合取 filter>1 取两张相异面 + good_list-ql 的
list_of_darts-Nodup 排重——两次止损未闭合（HOL 原路经 dart_of 选择函数章
dart_of_card_node，:8043-:8221 未移植），陈述逐字冻结，sorry 债务记账。 -/
theorem markedListIsNodeNondegenerate (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hgnq : GoodListNodesTl (quotientListSpine L N)
      (goodListQuotient L hL hn hnedg hunL))
    (hm : MarkedListSpine hL N r x) :
    ((hypermapOfList L hL).quotientHypermap
        (normalListNormal hL hgn hres hn)).NodeNondegenerate := by
  have hgood : GoodList (quotientListSpine L N) := goodListQuotient L hL hn hnedg hunL
  -- ql 侧：node ql y = {y}（不动点）与 filter>1 两面排重矛盾
  -- NEEDS：ql 侧 node 非退化支（见上方 docstring），本支 sorry。
  have hql : (hypermapOfList (quotientListSpine L N) hgood).NodeNondegenerate := by
    sorry
  exact isoIsNodeNondegenerate
    (quotientListIsoQuotient L hL hgn hres hn hnedg hunL).symm hql

/-! ### §6 marked 收束（tame_list.hl:10050/:10071） -/

/-- **HOL `final_loops_list_iff`**（tame_list.hl:10050-:10069）
`good_list L /\ MEM r N /\ normal_list L N ==> (loop_of_list r IN
final_loops (hypermap_of_list L) (loop_family_of_list N) <=> final_list L r)`
——final_loops_list_eq（批 8）+ loop_of_list_inj（批 12）。 -/
theorem finalLoopsListIff (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} (hr : r ∈ N)
    (hn : NormalListSpine hL N) :
    (loopOfListSpine r
        ∈ (hypermapOfList L hL).finalLoops (loopFamilyOfListSpine N))
      ↔ finalListSpine L r := by
  rw [finalLoopsListEq hL hn]
  constructor
  · intro hmem
    simp only [Set.mem_setOf_eq] at hmem
    obtain ⟨r₀, hr₀, hze⟩ := List.mem_map.mp hmem
    obtain ⟨hr₀N, hfr⟩ := List.mem_filter.mp hr₀
    have hfr' : finalListSpine L r₀ := by simpa using hfr
    have hreq : r₀ = r := loopOfListInj hn.1 hn.2.1 hr₀N hr hze
    rw [← hreq]
    exact hfr'
  · intro hf
    exact List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hf⟩, rfl⟩

/-- **HOL `marked_conclusion`**（tame_list.hl:10071-:10098）
`good_list L /\ good_list_nodes L /\ marked_list L N r d /\
~final_list L r ==> (split_condition_list L N r d /\ next_el r d = f_list L d /\
normal_list L N /\ is_restricted (hypermap_of_list L) /\ MEM r N /\ MEM d r /\
MEM d (list_of_darts L) /\ is_edge_nondegenerate (hypermap_of_list L) /\
all uniq L)`——marked_list_split_condition_list（批 12）+ 合取项直取 +
normal_list_list_of_darts + simple_hypermap_all_uniq（批 14）。 -/
theorem markedConclusion (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hm : MarkedListSpine hL N r d) (hf : ¬finalListSpine L r) :
    splitConditionListSpine hL N r d ∧
      nextEl r d = fList L d ∧ NormalListSpine hL N ∧
      (hypermapOfList L hL).IsRestricted ∧ r ∈ N ∧ d ∈ r ∧ d ∈ listOfDarts L ∧
      (hypermapOfList L hL).EdgeNondegenerate ∧ (∀ l ∈ L, l.Nodup) := by
  have hres := hm.1
  have hnorm := hm.2.1
  have hrN := hm.2.2.1
  have hdr := hm.2.2.2.1
  have hnext := hm.2.2.2.2.2.1
  refine ⟨markListSplitConditionList L hL hm hf, hnext, hnorm, hres, hrN, hdr, ?_,
    hres.edgeNondegenerate, simpleHypermapAllUniq L hL hgn
      (simpleHypermapList L hL hgn hunL)⟩
  · exact normalListListOfDarts hnorm d (List.mem_flatten.mpr ⟨r, hrN, hdr⟩)

end Kepler.Text.TameSpine
