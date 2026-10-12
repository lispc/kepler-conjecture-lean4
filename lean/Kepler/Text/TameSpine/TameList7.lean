/-
  Kepler.Text.TameSpine.TameList7 — B1 Tame_list 地基批 7：node 显式刻画链专项 +
  marked_list 群（tamespine-port-plan §4 批次表 B1 行；接续批 6 = TameList6.lean，
  HOL :4191-:4620 已由批 6 落，本批从 `node_of_element` :4387 起）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:4387-:4606 + :4634-:4700 前五件）：

  - node 刻画链 :4387/:4399/:4413/:4508/:4606（`node_of_element` 的内容被
    ⊇ 向直构吸收；`MEM_hypermap_of_list_node`/`is_restricted_node_f_list`/
    `normal_list_nodes_exist`/`normal_list_normal`（别名 `EVNAPDQ`）四件全落）；
  - marked_list 群 :4634-:4672（`marked_list_restricted`/`marked_list_normal`/
    `marked_list_mem_family`/`marked_list_mem_loop`/`marked_list_loop_eq_face_map`），
    定义层 = tame_defs2.hl:108-:134 的 `core_list`/`partition_into_atom*`/`parts`/
    `core`/`quotient_list` + :126 `final_list`（`find_list` 内联于 `FindListSpine`）。

  批内分工记账（桥引不重移植）：
  - 批 6 接口直接 import：`isLoopOfList`/`loopOfListSpine_real`/`loopMapNextEl`/
    `inDartLoopOfList`/`normalListUniqNonnil`/`normalList11`/`normalListFullNode`/
    `normalListInDartOfLoop`/`uniqSublistUnique`；
  - TameLp 既有件全限定/开名桥引：`hypermapOfList` 及三映射点态件、`dart_in_face`/
    `findFaceDarts_nodup`/`fList_mem_darts`/`faceMap_hypermapOfList`/
    `nodeMap_hypermapOfList`/`getElem_idxOf`/`idxOf_getElem`/`getD_eq_getElem_of_lt`/
    `nextEl_eq_getD`/`getD_mem`/`la7_prevEl_getD`/`la7_length_listPairs`/
    `la7_getElem_rotOne`/`la7_eList_involutory`；批 5 件 `normalListListOfDarts`/
    `uniqFlattenUniq`；批 2 件 `rotateSpineOne`；
  - Hypermap 引擎件：`orbitMap`/`PermutesOn`（pow_apply_mem/apply_mem）/
    `node_representation`/`node_eq_of_mem`/`Simple`/`IsRestricted`（含
    three_le_ncard_face）；`GoodListNodesTl`/`nodesOfListSet`/`listOfElements`
    为 TameLp S11 def（本批首次给出其非平凡消费）。

  node 链路线（批 6 头注建议两路线的裁决）：
  - ⊆ 向（HOL fst_node_hypermap_of_list + fst_n_list_ext_power）：私件 `fstNList`
    （`n_list` 保 FST）+ nodeMap 幂归纳（`fstNodeOrbit`）。核心是 HOL
    `prev_el_list_pairs_general` 的链式刻画：`list_pairs l` 中一项的前驱的第二分量
    = 该项的第一分量（面表在顶点处成链），经 `prevEl` 的 getD 均匀形 + 下标模
    算术闭合；
  - ⊇ 向（同 FST 的 dart 全类入轨道）：**直构路线**——FST-类集合
    `{d | d ∈ darts ∧ d.1 = FST x}` 经 `GoodListNodesTl`（nodeSet = nodesOfListSet）
    成为 nodeSet 成员，由 `node_representation` 取其 node 证人 d₀，再由
    `node_eq_of_mem`（同轨道传递）得该类 = node x。**无需移植** list_hypermap 的
    nodes_of_list_eq/uniq_node/set_nodes_of_list 整块（批 6 头注路线②），该块
    留待其直接消费者（good_list_nodes 条件版/card 版）出现时另行立项。

  诚实记账（本批跳过件与边界）：
  - **MarkedListSpine 只镜像 HOL `marked_list`（tame_defs2.hl:550）的前 7 个
    合取块**（is_restricted / normal_list / MEM r N / MEM x r / quotient_list 的
    uniq-非退化两支 / next_el r x = f_list L x / final_list (find_list N (e_list x))）；
    末两合取块（`final_list L r ==> flag_list L N` 与
    `~final_list L r ==> s_flag_list L N r x`）依赖 flag_list→final_dart_list/
    contour_list/parts 与 s_flag_list→s_list/l'm(min_num) 的旗塔
    （tame_defs2.hl:469-:535，reduction1/2 领土），本批不落地——五件消费定理
    （HOL 证明均只投影前 7 块）结论零收窄；旗塔随 reduction 波批次定义层进场；
  - `ntrans`/`rtrans`/`transform_list`/`split_normal_list`（tame_defs2.hl:435-:472）
    同属旗塔上游，未进入本批；
  - `node_of_element`（:4387）在 Lean 载体下被 ⊇ 向直构吸收（nodesOfListSet 的
    集合形态即 filter-FST-类，见 `nodeClassInNodeSet`），不设独立定理；
  - `marked_list_normal` 的 HOL 前提 `good_list_nodes L` 在 Lean 镜像中经
    `normalListNormal` 的 hgn 参保持（全前提保留）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git 写操作。
-/

import Kepler.Text.TameSpine.TameList6

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs nextEl prevEl listOfDarts GoodList findFaceDarts
  eList fList nList)
open Kepler.Graphs (fgraph)
open Kepler.Text (PermutesOn orbitMap)
open Kepler.Text.Fan (extendPerm extendPerm_permutes bijOn_res)
open Kepler.Text.TameLp (hypermapOfList elementsOfList nodesOfListSet GoodListNodesTl
  listOfElements nList_fList faceMap_hypermapOfList nodeMap_hypermapOfList
  edgeMap_hypermapOfList fList_mem_darts dart_in_face findFaceDarts_nodup
  getElem_idxOf idxOf_getElem getD_eq_getElem_of_lt nextEl_eq_getD getD_mem
  la7_prevEl_getD la7_length_listPairs la7_getElem_rotOne la7_length_rotOne
  la7_eList_involutory nextEl_mem_of_mem getLastD_eq_getElem_last
  headD_eq_getD_zero findFaceDarts_congr_of_mem)

open scoped Classical

/-! ### §0 node 刻画链私有引擎（list_pairs 链式刻画 + FST 不变量） -/

/-- zip 形 `list_pairs` 第 j 项的第一分量 = `l[j]`。 -/
private theorem zipFstGetElem {l : List ℕ} {j : ℕ} {s : List (ℕ × ℕ)}
    (hs : s = l.zip (l.drop 1 ++ l.take 1)) (hj : j < l.length)
    (hjl : j < s.length) :
    (s[j]'hjl).1 = l[j]'hj := by
  subst hs
  rw [List.getElem_zip]

/-- zip 形 `list_pairs` 第 j 项的第二分量 = `l[(j+1) mod len]`（面表成链核心）。 -/
private theorem zipSndGetElem {l : List ℕ} {j : ℕ} {s : List (ℕ × ℕ)}
    (hs : s = l.zip (l.drop 1 ++ l.take 1)) (hj : j < l.length)
    (hjl : j < s.length) (hm : (j + 1) % l.length < l.length) :
    (s[j]'hjl).2 = l[(j + 1) % l.length]'hm := by
  subst hs
  rw [List.getElem_zip]
  have hb : j < (l.rotate 1).length := Nat.lt_of_lt_of_eq hj (la7_length_rotOne l).symm
  have hrot' : (l.rotate 1)[j]'hb = l[(j + 1) % l.length]'hm := la7_getElem_rotOne hj
  have hlenA : j < (l.drop 1 ++ l.take 1).length := by
    rw [← rotateSpineOne]; exact hb
  simp only [rotateSpineOne] at hrot'
  show ((l[j]'hj, (l.drop 1 ++ l.take 1)[j]'hlenA)).2 = _
  show (l.drop 1 ++ l.take 1)[j]'hlenA = l[(j + 1) % l.length]'hm
  exact hrot'

/-- **HOL `prev_el_list_pairs_general` 核心**：`p ∈ list_pairs l` 的面表内前驱的
第二分量 = `p` 的第一分量（`n_list` 保 FST 的载体引擎）。 -/
private theorem prevElListPairsSnd {l : List ℕ}
    (_hs : (listPairs l).Nodup) {p : ℕ × ℕ} (hp : p ∈ listPairs l) :
    (prevEl (listPairs l) p).2 = p.1 := by
  have hzip : listPairs l = l.zip (l.drop 1 ++ l.take 1) := rfl
  have hlen : (listPairs l).length = l.length := la7_length_listPairs l
  have hpos : 0 < (listPairs l).length := List.length_pos_of_mem hp
  have hposl : 0 < l.length := Nat.lt_of_lt_of_eq hpos hlen
  have hk : (listPairs l).idxOf p < (listPairs l).length := List.idxOf_lt_length_iff.mpr hp
  have hkl : (listPairs l).idxOf p < l.length := Nat.lt_of_lt_of_eq hk hlen
  have hpk : p.1 = l[(listPairs l).idxOf p]'hkl := by
    have h1 := zipFstGetElem (l := l) (s := listPairs l) hzip hkl hk
    have h2 : (listPairs l)[(listPairs l).idxOf p]'hk = p := getElem_idxOf hp
    calc p.1 = ((listPairs l)[(listPairs l).idxOf p]'hk).1 := (congrArg Prod.fst h2).symm
      _ = l[(listPairs l).idxOf p]'hkl := h1
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
  have hsnd := zipSndGetElem (l := l) (s := listPairs l) hzip hjl hjlt hml
  have hidx : (((listPairs l).idxOf p + (listPairs l).length - 1) % (listPairs l).length + 1)
      % l.length = (listPairs l).idxOf p := by
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
  have getCon : ∀ (a b : ℕ) (ha : a < l.length) (hb : b < l.length), a = b → l[a]'ha = l[b]'hb :=
    fun a b ha hb hab => by subst hab; rfl
  exact (hsnd.trans (getCon _ _ hml hkl hidx)).trans hpk.symm

/-- **HOL `n_list_ext_fst` 第一分量**：good_list 下 `n_list` 保 FST。 -/
private theorem fstNList {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
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

/-- **HOL `mem_list_of_elements` 半向**：dart 的首分量是 element。 -/
private theorem fstMemListOfElements {L : fgraph ℕ} {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : d.1 ∈ listOfElements L := by
  obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd
  simp only [List.mem_map] at hl
  obtain ⟨l₀, hl₀, hEq⟩ := hl
  subst hEq
  obtain ⟨i, hi, hdz⟩ := List.mem_iff_getElem.mp hdl
  have hi2 : i < (l₀.zip (l₀.drop 1 ++ l₀.take 1)).length := hi
  rw [List.length_zip] at hi2
  have hii : i < l₀.length := by omega
  have hdz2 : (l₀.zip (l₀.drop 1 ++ l₀.take 1))[i]'hi = d := hdz
  rw [List.getElem_zip] at hdz2
  have h1 : l₀[i]'hii = d.1 := congrArg Prod.fst hdz2
  have h2 : d.1 ∈ l₀ := by
    rw [← h1]
    exact List.getElem_mem hii
  show d.1 ∈ L.flatten.eraseDups
  simp
  exact ⟨l₀, hl₀, h2⟩

/-- FST-类集合是 nodeSet 成员（⊇ 向引擎件；HOL `node_of_element` 的载体吸收形）。 -/
private theorem nodeClassInNodeSet {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (x : ℕ × ℕ) (hx : x ∈ listOfDarts L) :
    {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = x.1}
      ∈ (hypermapOfList L hL).nodeSet := by
  rw [hgn]
  show {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = x.1}
    ∈ (fun v : ℕ => {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = v}) '' {v | v ∈ listOfElements L}
  exact Set.mem_image_of_mem _ (fstMemListOfElements hx)

/-- ⊇ 向：同 FST 的 dart 全类入 node 轨道。 -/
private theorem nodeSup {L : fgraph ℕ} (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {x y : ℕ × ℕ} (hx : x ∈ listOfDarts L) (hxy : x.1 = y.1) (hy : y ∈ listOfDarts L) :
    y ∈ (hypermapOfList L hL).node x := by
  have hC := nodeClassInNodeSet hL hgn x hx
  obtain ⟨d₀, hd₀D, hd₀E⟩ := (hypermapOfList L hL).node_representation hC
  have hyC : y ∈ {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = x.1} := by
    exact ⟨hy, hxy.symm⟩
  rw [hd₀E] at hyC
  have hnode : (hypermapOfList L hL).node d₀ = (hypermapOfList L hL).node x :=
    (hypermapOfList L hL).node_eq_of_mem (by rw [← hd₀E]; exact ⟨hx, rfl⟩)
  rwa [hnode] at hyC

/-- ⊆ 向引擎：nodeMap 幂保 FST 且留 dart 集（HOL `fst_n_list_ext_power` +
`list_ext_power_in_darts` 合体）。 -/
private theorem fstNodeOrbit {L : fgraph ℕ} (hL : GoodList L) {x : ℕ × ℕ}
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
        fstNList hL (List.mem_toFinset.mp hmem)]
      exact hfst
    exact ⟨hfst2, hmem2⟩

/-! ### §1 MEM_hypermap_of_list_node（tame_list.hl:4399-:4411） -/

/-- **HOL `MEM_hypermap_of_list_node`**
`good_list L /\ good_list_nodes L /\ MEM x (list_of_darts L) ==>
  y IN node (hypermap_of_list L) x <=> FST x = FST y /\ MEM y (list_of_darts L)`
——node 轨道的显式刻画：轨道 = 同首分量 dart 全类。
⊆ 向经 nodeMap 幂保 FST；⊇ 向经 FST-类 ∈ nodeSet + node 证人 + 同轨道传递。 -/
theorem memHypermapOfListNode {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {x y : ℕ × ℕ} (hx : x ∈ listOfDarts L) :
    y ∈ (hypermapOfList L hL).node x ↔ (x.1 = y.1 ∧ y ∈ listOfDarts L) := by
  have hxd : x ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hx
  constructor
  · intro hy
    simp only [Kepler.Text.Hypermap.node, orbitMap, Set.mem_setOf_eq] at hy
    obtain ⟨n, hn⟩ := hy
    subst hn
    obtain ⟨hfst, hmem⟩ := fstNodeOrbit hL hxd n
    exact ⟨hfst.symm, List.mem_toFinset.mp hmem⟩
  · rintro ⟨hfst, hyd⟩
    exact nodeSup hL hgn hx hfst hyd

/-! ### §2 is_restricted_node_f_list（tame_list.hl:4413-:4478） -/

/-- nodup 非空表上 `next_el` 的不动点把表长钉死为 1
（HOL `Seq2.next_el_refl` 的 ⟸ 消费半向 + `Seq2.size1`）。 -/
private theorem nextElSelfLenOne {s : List (ℕ × ℕ)} (hn : s.Nodup) {x : ℕ × ℕ}
    (hx : x ∈ s) (h : nextEl s x = x) : s.length = 1 := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  have hilt : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  rw [nextEl_eq_getD hx, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)] at h
  have hjeq : (s.idxOf x + 1) % s.length = s.idxOf x := by
    have hxa : s[s.idxOf x]'hilt = x := getElem_idxOf hx
    exact (hn.getElem_inj_iff (hi := Nat.mod_lt _ hpos) (hj := hilt)).mp
      (h.trans hxa.symm)
  rcases Nat.lt_or_ge (s.idxOf x + 1) s.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hjeq; omega
  · have h2 : (s.idxOf x + 1) % s.length = (s.idxOf x + 1 - s.length) % s.length :=
      Nat.mod_eq_sub_mod hge
    rw [h2, Nat.mod_eq_of_lt (by omega : s.idxOf x + 1 - s.length < s.length)] at hjeq
    omega

/-- face 轨道落在面表内（HOL `f_list_ext_orbit` 的 ⊆ 半向）。 -/
private theorem faceOrbitSubsetFindFace {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    (hypermapOfList L hL).face d ⊆ {y | y ∈ findFaceDarts L d} := by
  have key : ∀ n : ℕ, ((hypermapOfList L hL).faceMap ^ n) d ∈ findFaceDarts L d := by
    intro n
    induction n with
    | zero => simpa using dart_in_face L d |>.mpr hd
    | succ k ih =>
      have hz : ((hypermapOfList L hL).faceMap ^ k) d
          ∈ (hypermapOfList L hL).darts :=
        (hypermapOfList L hL).faceMap_permutes.pow_apply_mem k (List.mem_toFinset.mpr hd)
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

/-- **HOL `is_restricted_node_f_list`**
`good_list L /\ good_list_nodes L /\ is_restricted (hypermap_of_list L) /\
MEM d (list_of_darts L) ==> ~(FST (f_list L d) = FST d)`
——反证：f_list d 若同 FST 则同时落在 node/face 轨道，Simple 给 f_list d = d，
面表长 1 与受限 hypermap 的 face ≥ 3 矛盾。 -/
theorem isRestrictedNodeFList {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) : (fList L d).1 ≠ d.1 := by
  have hdD : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd
  intro hcon
  have hfdD : fList L d ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr (fList_mem_darts hL.1 hd)
  -- f_list L d ∈ node d
  have hfd : fList L d ∈ (hypermapOfList L hL).node d :=
    (@memHypermapOfListNode L hL hgn d (fList L d) hd).2
      ⟨hcon.symm, List.mem_toFinset.mp hfdD⟩
  -- f_list L d ∈ face d
  have hff : fList L d ∈ (hypermapOfList L hL).face d := by
    show fList L d ∈ orbitMap (hypermapOfList L hL).faceMap d
    exact ⟨1, by rw [pow_one]; exact faceMap_hypermapOfList L hL hdD⟩
  -- Simple 钉死 f_list L d = d
  have hsimple := hres.simple d hdD
  have hfeq : fList L d = d := by
    have hinter : fList L d ∈ (hypermapOfList L hL).node d ∩ (hypermapOfList L hL).face d :=
      ⟨hfd, hff⟩
    rw [hsimple] at hinter
    exact Set.mem_singleton_iff.mp hinter
  -- 面表长 1
  have h1 : (findFaceDarts L d).length = 1 :=
    nextElSelfLenOne (findFaceDarts_nodup hL.1 d) (dart_in_face L d |>.mpr hd) hfeq
  -- face 轨道 ⊆ 面表 = 单点 → ncard ≤ 1 < 3
  have hsub := faceOrbitSubsetFindFace hL hd
  have hlenpos : 0 < (findFaceDarts L d).length := by rw [h1]; omega
  have hset : {y | y ∈ findFaceDarts L d}
      = {(findFaceDarts L d)[0]'hlenpos} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hy
      obtain ⟨i, hi, hyi⟩ := List.mem_iff_getElem.mp hy
      have hi0 : i = 0 := by rw [h1] at hi; omega
      subst hi0
      rw [← hyi]
    · intro hy
      rw [hy]
      exact List.getElem_mem hlenpos
  have hncard : ((hypermapOfList L hL).face d).ncard ≤ 1 := by
    have hsub2 : (hypermapOfList L hL).face d
        ⊆ {(findFaceDarts L d)[0]'hlenpos} := by rw [← hset]; exact hsub
    calc ((hypermapOfList L hL).face d).ncard
        ≤ ({(findFaceDarts L d)[0]'hlenpos} : Set (ℕ × ℕ)).ncard :=
          Set.ncard_le_ncard hsub2
      _ = 1 := Set.ncard_singleton _
  have h3 := hres.three_le_ncard_face hdD
  omega

/-! ### §3 normal_list_nodes_exist（tame_list.hl:4508-:4560） -/

/-- **HOL `normal_list_nodes_exist`**
`is_restricted /\ good_list /\ good_list_nodes /\ normal_list L N /\
r IN loop_family_of_list N ==> ?y z. in_dart_of_loop y r /\ in_dart_of_loop z r /\
~(node (hypermap_of_list L) y = node (hypermap_of_list L) z)`
——取面表首末（HD/LAST），`f_last` 合取项 + is_restricted_node_f_list 给
FST(HD) ≠ FST(LAST)，再经 node 刻画分开两轨道。 -/
theorem normalListNodesExist {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N) {r : Loop (ℕ × ℕ)}
    (hr : r ∈ loopFamilyOfListSpine N) :
    ∃ y z, y ∈ r.darts ∧ z ∈ r.darts ∧
      (hypermapOfList L hL).node y ≠ (hypermapOfList L hL).node z := by
  obtain ⟨l, hl, rfl⟩ := hr
  have hune := normalListUniqNonnil h hl
  have hlne : l ≠ [] := hune.2
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil l hlne
  have hpos : 0 < l.length := List.length_pos_of_mem hx0
  have hzget : l[l.length - 1]'(by omega : l.length - 1 < l.length) = l.getLast! := by
    rw [getLast!EqGetLast hlne]
    have h1 : l.getLast hlne = l.getLastD (l.getLast hlne) := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hlne]
      simp
    rw [h1, getLastD_eq_getElem_last hpos]
  have hzidx : l.idxOf l.getLast! = l.length - 1 := by
    rw [← hzget]; exact idxOf_getElem hune.1 _
  have hzl : l.getLast! ∈ l := by
    rw [← hzget]; exact List.getElem_mem (by omega)
  have hyl : l.headD l.getLast! ∈ l := by
    have h0 : l.headD l.getLast! = l[0]'hpos := by
      rw [headD_eq_getD_zero, getD_eq_getElem_of_lt hpos]
    rw [h0]; exact List.getElem_mem hpos
  have hyd : l.headD l.getLast! ∈ listOfDarts L :=
    normalListListOfDarts h (l.headD l.getLast!) (List.mem_flatten.mpr ⟨l, hl, hyl⟩)
  have hzd : l.getLast! ∈ listOfDarts L :=
    normalListListOfDarts h l.getLast! (List.mem_flatten.mpr ⟨l, hl, hzl⟩)
  rw [loopOfListSpine_real hune.1 hune.2]
  refine ⟨l.headD l.getLast!, l.getLast!, List.mem_toFinset.mpr hyl,
    List.mem_toFinset.mpr hzl, ?_⟩
  intro hnodeeq
  have hziny : l.getLast! ∈ (hypermapOfList L hL).node (l.headD l.getLast!) := by
    rw [hnodeeq]
    exact ⟨0, by simp⟩
  obtain ⟨hfst, hzD⟩ :=
    (@memHypermapOfListNode L hL hgn (l.headD l.getLast!) l.getLast! hyd).mp hziny
  have hfLast : nextEl l l.getLast! = fList L l.getLast! := h.2.2.1 l hl
  have hnext : nextEl l l.getLast! = l.headD l.getLast! := by
    unfold nextEl
    rw [if_pos hzidx]
  have hne := isRestrictedNodeFList hL hgn hres hzd
  exact hne (by rw [← hfLast, hnext]; exact hfst)

/-! ### §4 normal_list_normal = EVNAPDQ（tame_list.hl:4606-:4632） -/

/-- **HOL `normal_list_normal`（别名 `EVNAPDQ`）**
`is_restricted /\ good_list /\ good_list_nodes /\ normal_list L N ==>
is_normal (hypermap_of_list L) (loop_family_of_list N)`
——IsNormalFamily 四合取：①isLoopOfList（批 6）+ normalListInDartOfLoop（批 6），
②normalListNodesExist（本批，node 链的心脏），③normalList11（批 6），
④normalListFullNode（批 6）。 -/
theorem normalListNormal {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N) :
    (hypermapOfList L hL).IsNormalFamily (loopFamilyOfListSpine N) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨l, hl, rfl⟩ := hr
    have hune := normalListUniqNonnil h hl
    refine ⟨isLoopOfList hL hune.1 hune.2 (h.2.2.2.1 l hl), ?_⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hune.2
    refine ⟨x, List.mem_toFinset.mpr (normalListListOfDarts h x
      (List.mem_flatten.mpr ⟨l, hl, hx⟩)), ?_⟩
    rw [loopOfListSpine_real hune.1 hune.2]
    exact List.mem_toFinset.mpr hx
  · intro r hr
    obtain ⟨y, z, hy, hz, hne⟩ := normalListNodesExist hL hgn hres h hr
    exact ⟨y, hy, z, hz, hne⟩
  · intro r hr r' hr' x hx hx'
    exact normalList11 hL h hr hr' hx hx'
  · intro r hr x y hx hy
    exact normalListFullNode hL h hr hx hy

/-! ### §5 quotient_list 定义块（tame_defs2.hl:108-:134 + :126） -/

/-- HOL `partition_into_atom0`（tame_defs2.hl:119-:122）逐句镜像：
按 `n`-像与当前原子头的相等性把（逆序）dart 串切成原子列
（HD/TL 的 junk 语义 ↦ `head!`/`tail!`，消费侧全部携带非空折算）。 -/
def partitionIntoAtom0 (n : ℕ × ℕ → ℕ × ℕ) :
    List (List (ℕ × ℕ)) → List (ℕ × ℕ) → List (List (ℕ × ℕ))
  | acc, [] => acc
  | acc, r :: rs =>
    if acc = [] then partitionIntoAtom0 n [[r]] rs
    else if n r = acc.head!.head! then
      partitionIntoAtom0 n ((r :: acc.head!) :: acc.tail) rs
    else partitionIntoAtom0 n ([r] :: acc) rs

/-- HOL `partition_into_atom0r` + `partition_into_atom`
（tame_defs2.hl:123-:125：`partition_into_atom n r = partition_into_atom0 n [] (rev r)`）。 -/
def partitionIntoAtom (n : ℕ × ℕ → ℕ × ℕ) (r : List (ℕ × ℕ)) :
    List (List (ℕ × ℕ)) := partitionIntoAtom0 n [] r.reverse

/-- HOL `parts`（tame_defs2.hl:127-:128：
`parts L r = partition_into_atom ((f_list L) o e_list) r`）。 -/
def partsSpine (L : fgraph ℕ) (r : List (ℕ × ℕ)) : List (List (ℕ × ℕ)) :=
  partitionIntoAtom (fun d => fList L (eList d)) r

/-- HOL `core`（tame_defs2.hl:130-:131：`core L r = MAP (FST o HD) (parts L r)`）。 -/
def coreSpine (L : fgraph ℕ) (r : List (ℕ × ℕ)) : List ℕ :=
  (partsSpine L r).map (fun a => a.head!.1)

/-- HOL `core_list`（tame_defs2.hl:108-:110：
`core_list PN = map (\f. map (\x. FST (HD x)) f) PN`）。 -/
def coreListSpine (PN : List (List (List (ℕ × ℕ)))) : List (List ℕ) :=
  PN.map (fun f => f.map (fun a => a.head!.1))

/-- HOL `quotient_list`（tame_defs2.hl:133-:134：
`quotient_list L N = core_list (map (parts L) N)`）。 -/
def quotientListSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) : List (List ℕ) :=
  coreListSpine (N.map (partsSpine L))

/-- HOL `final_list`（tame_defs2.hl:126：
`final_list L r <=> all (\d. f_list L d = next_el r d) r`）。 -/
def finalListSpine (L : fgraph ℕ) (r : List (ℕ × ℕ)) : Prop :=
  ∀ d ∈ r, fList L d = nextEl r d

/-- HOL `find_list`（list_hypermap-compiled.hl:44-45 经 `find_face` 同款内联：
`N` 中第一个含 `d` 的面；无则 `[]`）。 -/
def findListSpine (N : List (List (ℕ × ℕ))) (d : ℕ × ℕ) : List (ℕ × ℕ) :=
  (N.find? fun r => decide (d ∈ r)).getD []

/-- HOL `marked_list`（tame_defs2.hl:550-:570）的**前 7 合取块镜像**
（载体记账：`hypermap_of_list L` 的构造需 `GoodList L`，证人 `hL` 显式入参，
沿 NormalListSpine 约定）。

诚实记账：末两合取块（`final_list L r ==> flag_list L N` 与
`~final_list L r ==> s_flag_list L N r x`）依赖旗塔
`flag_list → final_dart_list/contour_list/parts` 与
`s_flag_list → s_list/l'm (min_num)`（tame_defs2.hl:469-:535，reduction1/2 领土），
本批不落地；本批五件消费定理的 HOL 证明均只投影前 7 块，结论零收窄，
旗塔随 reduction 波批次定义层进场补全（见模块头注）。 -/
def MarkedListSpine {L : fgraph ℕ} (hL : GoodList L)
    (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ) : Prop :=
  (hypermapOfList L hL).IsRestricted ∧
  NormalListSpine hL N ∧
  r ∈ N ∧
  x ∈ r ∧
  ((∀ q ∈ quotientListSpine L N, q.Nodup) ∧
    ∀ v ∈ (quotientListSpine L N).flatten,
      1 < ((quotientListSpine L N).filter (fun q => decide (v ∈ q))).length) ∧
  nextEl r x = fList L x ∧
  finalListSpine L (findListSpine N (eList x))

/-! ### §6 marked_list 群（tame_list.hl:4634-:4700 前五件） -/

/-- **HOL `marked_list_restricted`**（tame_list.hl:4634-:4641）
`marked_list L N r d ==> is_restricted (hypermap_of_list L)`——合取项 1 直取。 -/
theorem markListRestricted {L : fgraph ℕ} (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {x : ℕ × ℕ} (hm : MarkedListSpine hL N r x) :
    (hypermapOfList L hL).IsRestricted := hm.1

/-- **HOL `marked_list_normal`**（tame_list.hl:4643-:4651）
`good_list /\ good_list_nodes /\ marked_list L N r d ==>
is_normal (hypermap_of_list L) (loop_family_of_list N)`——经 normal_list_normal。 -/
theorem markListNormal {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {x : ℕ × ℕ} (hm : MarkedListSpine hL N r x) :
    (hypermapOfList L hL).IsNormalFamily (loopFamilyOfListSpine N) :=
  normalListNormal hL hgn hm.1 hm.2.1

/-- **HOL `marked_list_mem_family`**（tame_list.hl:4653-:4659）
`marked_list L N r d ==> loop_of_list r IN loop_family_of_list N`——合取项 3 直取。 -/
theorem markListMemFamily {L : fgraph ℕ} (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {x : ℕ × ℕ} (hm : MarkedListSpine hL N r x) :
    loopOfListSpine r ∈ loopFamilyOfListSpine N := ⟨r, hm.2.2.1, rfl⟩

/-- **HOL `marked_list_mem_loop`**（tame_list.hl:4661-:4670）
`good_list /\ good_list_nodes /\ marked_list L N r d ==>
in_dart_of_loop d (loop_of_list r)`——`in_dart_of_loop` 在 Loop 载体下定义性为
dart 集成员；`in_dart_loop_of_list`（批 6）+ `normal_list_uniq_nonnil`。 -/
theorem markListMemLoop {L : fgraph ℕ} (hL : GoodList L)
    (_hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {x : ℕ × ℕ} (hm : MarkedListSpine hL N r x) :
    x ∈ (loopOfListSpine r).darts := by
  have hune := normalListUniqNonnil hm.2.1 hm.2.2.1
  exact (inDartLoopOfList hune.1 hune.2 x).mpr hm.2.2.2.1

/-- **HOL `marked_list_loop_eq_face_map`**（tame_list.hl:4672-:4700）
`good_list /\ marked_list L N r d ==>
loop_map (loop_of_list r) d = face_map (hypermap_of_list L) d`
——`loop_map_next_el`（批 6）+ 合取项 6 + faceMap 点态件。 -/
theorem markListLoopEqFaceMap {L : fgraph ℕ} (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {x : ℕ × ℕ} (hm : MarkedListSpine hL N r x) :
    (loopOfListSpine r).map x = (hypermapOfList L hL).faceMap x := by
  have hune := normalListUniqNonnil hm.2.1 hm.2.2.1
  have hxd : x ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr (normalListListOfDarts hm.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.2.2.1, hm.2.2.2.1⟩))
  rw [loopMapNextEl hune.1 hune.2 x, hm.2.2.2.2.2.1,
    faceMap_hypermapOfList L hL hxd]

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.memHypermapOfListNode
#print axioms Kepler.Text.TameSpine.isRestrictedNodeFList
#print axioms Kepler.Text.TameSpine.normalListNodesExist
#print axioms Kepler.Text.TameSpine.normalListNormal
#print axioms Kepler.Text.TameSpine.markListRestricted
#print axioms Kepler.Text.TameSpine.markListNormal
#print axioms Kepler.Text.TameSpine.markListMemFamily
#print axioms Kepler.Text.TameSpine.markListMemLoop
#print axioms Kepler.Text.TameSpine.markListLoopEqFaceMap
-/
