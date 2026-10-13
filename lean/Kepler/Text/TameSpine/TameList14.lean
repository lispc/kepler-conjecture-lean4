/-
  Kepler.Text.TameSpine.TameList14 — B1 Tame_list 地基批 14：simple-hypermap 章
  （tamespine-port-plan §4 批次表 B1 行；接续批 13 = TameList13.lean，
  B1 链 :23-:9125 无缺口，本批起点 = HOL :9127 simple_hypermap_list）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl）——simple-hypermap 章全量 4 枚 +
  iso 章首件（任务书行号与库内副本逐字核对一致，零偏移）：

  `simple_hypermap_list` :9127 / `list_pairs_not_uniq` :9173 /
  `simple_hypermap_all_uniq` :9210 / `simple_hypermap_uniq` :9254 /
  `iso_is_node_nondegenerate` :9263。

  诚实记账（本批跳过/合并/桥引件）：
  - `simple_hypermap`（hypermap.hl:186）↦ `Hypermap.Simple`（Hypermap.lean:1058
    已真）直引，逐字同形（∀ x ∈ dart, node x ∩ face x = {x}）；
  - `all uniq L` ↦ `∀ l ∈ L, l.Nodup`、`uniq ↦ List.Nodup`（批 1-13 载体约定）；
  - `dart_of_unique`（:8101，批 12 记账的"备选 dart_of 选择函数章
    :8043-:8221"成员）不另移植：其收口步 = `list_pairs_unique`
    （tame_list.hl:4110），批 5 `listPairsUnique` 已真；本批经
    `findFaceDarts_ex_of_self`+`findFaceDarts_eq_of_mem`（TameLp，即 HOL
    find_face_alt/dart_in_face/mem_find_pair_list/find_pair_list_unique 的
    Lean 形）拼装同一论证，零收窄；
  - `MEM_hypermap_of_list_node`（tame_list.hl:4399）↦ 批 7
    `memHypermapOfListNode` 直引；
  - `face_of_list` 的 face-轨道双向刻画（⊆ 向 = 批 7/8
    `faceOrbitSubsetFindFace`，⊇ 向 = 批 8 `faceTableSubsetFaceOrbit`）
    系 private 不跨文件，§0 同证重推导（批 7→8→…→13 惯例；含 next_el
    轨道引擎 getElemCon/nextElStep/nextElIterateGetElem/nextElIterateMem）；
  - `list_pairs_not_uniq` 的 HOL Seq 层（uniq_nthP/set_nth_default/mem_nth/
    nth_list_pairs/size_list_pairs）按 getElem 折算重写：¬Nodup 经
    `List.nodup_iff_pairwise_ne`+`List.pairwise_iff_getElem` 取同值双下标
    i < j，双见证取 `(listPairs s)[i]`/`(listPairs s)[j]`，FST 相等由 zip
    逐项式（= HOL nth_list_pairs 的 rot-1 位移），相异由
    `Nodup.getElem_inj_iff`——HOL 同构零收窄；
  - `iso_is_node_nondegenerate`：HOL 经 `lemma_node_nondegenerate`
    （↔ CARD node ≥ 2）+ `hyp_iso_card_components` 绕行；Lean 侧
    `Hypermap.NodeNondegenerate`（Hypermap.lean:1073）本就是映射点态形，
    `Hypermap.Iso` 的三映射交换字段直接给出两步反证（f 与 nodeMap 共轭），
    无需 card-分量机制——陈述零收窄、证明取更短路线（记账）；
  - iso 章其余件（`iso_is_no_double_joins` :9276 / `iso_card_face` :9304 /
    `hyp_iso_restricted` :9319 起）前置 `Hypermap_iso` 桥章
    （hyp_iso_dart/hyp_iso_card_components/components_iso_image/
    hyp_iso_edge_node，hypermap_iso.hl）全树未移植，本批不动（诚实跳过）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 15 接续点：HOL :9276 起 iso 章余件——前置 = 先移植
  Hypermap_iso 桥章（`hyp_iso_dart`/`hyp_iso_card_components`/
  `hyp_iso_edge_node`/`components_iso_image`，hypermap_iso.hl；批 5 私件
  `nodeMapPowLift` 是 node-轨道共轭幂的现成引擎可作起点，face 分量同构
  补齐即可拼 `hyp_iso_card_components`），或如 iso_is_node_nondegenerate
  一般按 Lean Iso 字段逐枚找点态短路线。
-/

import Kepler.Text.TameSpine.TameList13

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList fList GoodList listPairs listOfDarts
  findFaceDarts nList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList nextEl_eq_getD getD_eq_getElem_of_lt
  getElem_idxOf idxOf_getElem dart_in_face findFaceDarts_ex_of_self
  findFaceDarts_eq_of_mem findFaceDarts_congr_of_mem findFaceDarts_nodup
  mem_darts_of_mem_findFace nextEl_mem_of_mem flatten_nodup_mem
  la7_length_listPairs darts_hypermapOfList faceMap_hypermapOfList
  GoodListNodesTl)

/-! ### §0 face-轨道私有引擎（批 7/8 私件不跨文件，惯例同证重推导） -/

/-- 同表两下标相等则取元相等（proof-irrelevant getElem 换形器；泛用版）。 -/
private theorem getElemCon {α : Type*} {l : List α} {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a = b) :
    l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- 单步轨道：nodup 表第 `j` 项的 `next_el` = 第 `(j+1) mod len` 项。 -/
private theorem nextElStep {s : List (ℕ × ℕ)} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (hj1 : (j + 1) % s.length < s.length) :
    nextEl s (s[j]'hj) = s[(j + 1) % s.length]'hj1 := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  rw [nextEl_eq_getD (List.getElem_mem hj), idxOf_getElem hsn hj,
    getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]

/-- 轨道枚举：nodup 表上 `next_el` 幂从第 `j` 项出发按 mod 下标走。 -/
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

/-- 轨道不离开表。 -/
private theorem nextElIterateMem {s : List (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ s) :
    ∀ n : ℕ, (nextEl s)^[n] x ∈ s := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-- face 轨道 ⊆ 面表（HOL `f_list_ext_orbit` 的 ⊆ 半向；批 7/8 私件同证
重推导，private 不跨文件可见）。 -/
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

/-- face 轨道 ⊇ 面表（面表 = `next_el` 面-表的循环，轨道走遍全表；批 8
私件同证重推导）。 -/
private theorem faceTableSubsetFaceOrbit {L : fgraph ℕ} (hL : GoodList L)
    {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) :
    {y | y ∈ findFaceDarts L d} ⊆ (hypermapOfList L hL).face d := by
  have hdd : d ∈ findFaceDarts L d := dart_in_face L d |>.mpr hd
  have hFFnodup : (findFaceDarts L d).Nodup := findFaceDarts_nodup hL.1 d
  have hpos : 0 < (findFaceDarts L d).length := List.length_pos_of_mem hdd
  -- faceMap 在面表上逐点 = nextEl 面表
  have hfaceTbl : ∀ z ∈ findFaceDarts L d,
      (hypermapOfList L hL).faceMap z = nextEl (findFaceDarts L d) z := by
    intro z hz
    have hzD : z ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr (mem_darts_of_mem_findFace L hz)
    rw [faceMap_hypermapOfList L hL hzD]
    show nextEl (findFaceDarts L z) z = nextEl (findFaceDarts L d) z
    rw [findFaceDarts_congr_of_mem hL.1 hd hz]
  -- 幂交换
  have hpow : ∀ n : ℕ, ((hypermapOfList L hL).faceMap ^ n) d
      = (nextEl (findFaceDarts L d))^[n] d := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, Function.iterate_zero]
      rfl
    | succ k ih =>
      have hmem := nextElIterateMem hdd k
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hfaceTbl _ hmem,
        Function.iterate_succ_apply']
  rintro y hy
  simp only [Kepler.Text.Hypermap.face, orbitMap, Set.mem_setOf_eq]
  -- 轨道走遍全表：从 d 走 (idxOf y - idxOf d) mod len 步
  have hidd : (findFaceDarts L d).idxOf d < (findFaceDarts L d).length :=
    List.idxOf_lt_length_iff.mpr hdd
  have hidy : (findFaceDarts L d).idxOf y < (findFaceDarts L d).length :=
    List.idxOf_lt_length_iff.mpr hy
  refine ⟨((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
      - (findFaceDarts L d).idxOf d) % (findFaceDarts L d).length, ?_⟩
  rw [hpow]
  have hiter := nextElIterateGetElem hFFnodup hidd
    (((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
      - (findFaceDarts L d).idxOf d) % (findFaceDarts L d).length)
    (Nat.mod_lt _ hpos)
  rw [getElem_idxOf hdd] at hiter
  rw [hiter]
  have hkey : ((findFaceDarts L d).idxOf d
        + (((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
          - (findFaceDarts L d).idxOf d) % (findFaceDarts L d).length))
      % (findFaceDarts L d).length = (findFaceDarts L d).idxOf y := by
    rw [Nat.add_comm, Nat.mod_add_mod]
    have h2 : (findFaceDarts L d).idxOf y + (findFaceDarts L d).length
        - (findFaceDarts L d).idxOf d + (findFaceDarts L d).idxOf d
        = (findFaceDarts L d).length + (findFaceDarts L d).idxOf y := by omega
    rw [h2, Nat.add_mod_left, Nat.mod_eq_of_lt hidy]
  exact Eq.trans (getElemCon _ _ hkey) (getElem_idxOf hy)

/-- `list_pairs s` 第 `k` 项 = `(s[k], s[(k+1) mod sizel s])`（HOL
`nth_list_pairs` 的 getElem 折算，rot-1 位移含末位回卷支。批 10 私件
listPairsGetElem 的泛型同证重推导，private 不跨文件可见）。 -/
private theorem listPairsGetElemRot {α : Type*} (s : List α) {k : ℕ}
    (hk : k < s.length) :
    (listPairs s)[k]'(by rw [la7_length_listPairs s]; omega)
      = (s[k]'hk,
        s[(k + 1) % s.length]'(Nat.mod_lt (k + 1)
          (Nat.lt_of_le_of_lt (Nat.zero_le k) hk))) := by
  have hpos : 0 < s.length := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hlenDr : (s.drop 1).length = s.length - 1 := List.length_drop
  have hlenTk : (List.take 1 s).length = min 1 s.length := List.length_take
  have htot : k < ((s.drop 1) ++ List.take 1 s).length := by
    rw [List.length_append, hlenDr, hlenTk]; omega
  by_cases hk1 : k + 1 < s.length
  · have hrot : ((s.drop 1) ++ List.take 1 s)[k] = (s.drop 1)[k] :=
      List.getElem_append_left (by rw [hlenDr]; omega) (h' := htot)
    have hdr : (s.drop 1)[k] = s[1 + k] :=
      List.getElem_drop (h := by rw [hlenDr]; omega)
    have hmod : (k + 1) % s.length = k + 1 := Nat.mod_eq_of_lt hk1
    show (s.zip (s.drop 1 ++ List.take 1 s))[k]'(by
      rw [List.length_zip]; omega) = _
    rw [List.getElem_zip, hrot, hdr]
    exact congrArg (Prod.mk s[k])
      (getElemCon (by omega) (Nat.mod_lt (k + 1) hpos) (by omega))
  · have jlen : k + 1 = s.length := by omega
    have hrot : ((s.drop 1) ++ List.take 1 s)[k]
        = (List.take 1 s)[k - (s.drop 1).length] :=
      List.getElem_append_right (by rw [hlenDr]; omega) (h₂ := htot)
    have h0 : k - (s.drop 1).length = 0 := by rw [hlenDr]; omega
    have htak : (List.take 1 s)[k - (s.drop 1).length] = s[0] :=
      (getElemCon (by rw [hlenTk]; omega) (by rw [hlenTk]; omega) h0).trans
        (List.getElem_take (h := by rw [hlenTk]; omega))
    show (s.zip (s.drop 1 ++ List.take 1 s))[k]'(by
      rw [List.length_zip]; omega) = _
    rw [List.getElem_zip, hrot, htak]
    exact congrArg (Prod.mk s[k])
      (getElemCon hpos (Nat.mod_lt (k + 1) hpos) (by rw [jlen, Nat.mod_self]))

/-! ### §1 simple-hypermap 章（tame_list.hl:9127-:9254） -/

/-- **HOL `simple_hypermap_list`**（tame_list.hl:9127-:9172）
`good_list L /\ good_list_nodes L /\ all uniq L ==>
simple_hypermap (hypermap_of_list L)`——Simple 双包含：⊇ 向 = 轨道零次幂
（node_refl/face_refl）；⊆ 向 = node 轨道给同 FST（批 7
memHypermapOfListNode）+ face 轨道落在面表（§0 faceOrbitSubsetFindFace）
+ 面表定位（TameLp findFaceDarts_ex_of_self/findFaceDarts_eq_of_mem）+
`listPairsUnique`（批 5，即 HOL list_pairs_unique/dart_of_unique 的收口步）。 -/
theorem simpleHypermapList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup) :
    (hypermapOfList L hL).Simple := by
  intro x hx
  have hxL : x ∈ listOfDarts L := List.mem_toFinset.mp hx
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    have hyn : y ∈ (hypermapOfList L hL).node x := hy.1
    have hyf : y ∈ (hypermapOfList L hL).face x := hy.2
    obtain ⟨hfst, hyd⟩ := (memHypermapOfListNode hL hgn hxL).mp hyn
    have hyf' : y ∈ findFaceDarts L x := faceOrbitSubsetFindFace hL hxL hyf
    obtain ⟨f, hfl, hfeq, hxf⟩ := findFaceDarts_ex_of_self
      (dart_in_face L x |>.mpr hxL)
    have hyf'' : y ∈ listPairs f := by rw [← hfeq]; exact hyf'
    exact (listPairsUnique (hunL f hfl) hxf hyf'' hfst).symm
  · intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact ⟨mem_orbitMap_self _ _, mem_orbitMap_self _ _⟩

/-- **HOL `list_pairs_not_uniq`**（tame_list.hl:9173-:9209）
`~uniq s /\ uniq (list_pairs s) ==> ?x x'. MEM x (list_pairs s) /\
MEM x' (list_pairs s) /\ ~(x = x') /\ (FST x = FST x')`——¬Nodup 经
`List.nodup_iff_pairwise_ne`+`List.pairwise_iff_getElem` 取同值双下标
i < j，双见证取 `list_pairs s` 第 i/j 项；FST 相等 = zip 逐项式
（= HOL nth_list_pairs），相异 = `Nodup.getElem_inj_iff`。 -/
theorem listPairsNotUniq {α : Type*} {s : List α}
    (hs : ¬s.Nodup) (hp : (listPairs s).Nodup) :
    ∃ x x' : α × α, x ∈ listPairs s ∧ x' ∈ listPairs s ∧ x ≠ x' ∧ x.1 = x'.1 := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem] at hs
  push_neg at hs
  obtain ⟨i, j, hi, hj, hij, heq⟩ := hs
  have hlen : (listPairs s).length = s.length := la7_length_listPairs s
  have hi' : i < (listPairs s).length := by rw [hlen]; omega
  have hj' : j < (listPairs s).length := by rw [hlen]; omega
  refine ⟨(listPairs s)[i]'hi', (listPairs s)[j]'hj', List.getElem_mem _,
    List.getElem_mem _, ?_, ?_⟩
  · intro hcon
    have hix := (hp.getElem_inj_iff (hi := hi') (hj := hj')).mp hcon
    omega
  · have hxi : ((listPairs s)[i]'hi').1 = s[i] := by
      rw [listPairsGetElemRot s hi]
    have hxj : ((listPairs s)[j]'hj').1 = s[j] := by
      rw [listPairsGetElemRot s hj]
    rw [hxi, hxj]
    exact heq

/-- **HOL `simple_hypermap_all_uniq`**（tame_list.hl:9210-:9253）
`good_list L /\ good_list_nodes L /\ simple_hypermap (hypermap_of_list L)
==> all uniq L`——反证：¬nodup l 时 `listPairsNotUniq` 给同 FST 异元
x ≠ x' ∈ list_pairs l ⊆ list_of_darts；x' ∈ node x（同 FST，批 7）∧
x' ∈ face x（find_face L x = list_pairs l，TameLp findFaceDarts_eq_of_mem
+ §0 faceTableSubsetFaceOrbit）与 Simple 的 {x} 收口矛盾（= HOL
uniq_flatten_uniq + face_of_list + MEM_hypermap_of_list_node 拼装）。 -/
theorem simpleHypermapAllUniq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hs : (hypermapOfList L hL).Simple) :
    ∀ l ∈ L, l.Nodup := by
  intro l hl
  by_contra hnl
  have hplnod : (listPairs l).Nodup :=
    flatten_nodup_mem hL.1 (List.mem_map.mpr ⟨l, hl, rfl⟩)
  obtain ⟨x, x', hxmem, hx'mem, hxx', hxfst⟩ := listPairsNotUniq hnl hplnod
  have hxdL : x ∈ listOfDarts L :=
    List.mem_flatten.mpr ⟨listPairs l, List.mem_map.mpr ⟨l, hl, rfl⟩, hxmem⟩
  have hx'dL : x' ∈ listOfDarts L :=
    List.mem_flatten.mpr ⟨listPairs l, List.mem_map.mpr ⟨l, hl, rfl⟩, hx'mem⟩
  have hsx := hs x (List.mem_toFinset.mpr hxdL)
  have hx'n : x' ∈ (hypermapOfList L hL).node x :=
    (memHypermapOfListNode hL hgn hxdL).mpr ⟨hxfst, hx'dL⟩
  have hfeq : findFaceDarts L x = listPairs l :=
    findFaceDarts_eq_of_mem hL.1 hl hxmem
  have hx'f : x' ∈ (hypermapOfList L hL).face x :=
    faceTableSubsetFaceOrbit hL hxdL (by rw [hfeq]; exact hx'mem)
  have hx'inter : x' ∈ (hypermapOfList L hL).node x ∩
      (hypermapOfList L hL).face x := ⟨hx'n, hx'f⟩
  rw [hsx] at hx'inter
  exact absurd (Set.mem_singleton_iff.mp hx'inter).symm hxx'

/-- **HOL `simple_hypermap_uniq`**（tame_list.hl:9254-:9262）
`good_list L /\ good_list_nodes L ==> (simple_hypermap (hypermap_of_list L)
<=> all uniq L)`——两向 = simple_hypermap_all_uniq + simple_hypermap_list
（HOL MESON 同构）。 -/
theorem simpleHypermapUniq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) :
    ((hypermapOfList L hL).Simple ↔ ∀ l ∈ L, l.Nodup) :=
  ⟨simpleHypermapAllUniq L hL hgn, fun hun => simpleHypermapList L hL hgn hun⟩

/-! ### §2 iso 章首件（tame_list.hl:9263-:9275） -/

/-- **HOL `iso_is_node_nondegenerate`**（tame_list.hl:9263-:9275）
`hyp_iso f (K,H) /\ is_node_nondegenerate H ==> is_node_nondegenerate K`——
`hyp_iso f (K,H)` ↦ `K.Iso H`（Hypermap.Iso 载体，f 由存在封装）；证明
不走 HOL 的 lemma_node_nondegenerate(card ≥ 2)+hyp_iso_card_components
绕行：NodeNondegenerate 本是映射点态形，Iso 三映射交换字段给出
`H.nodeMap (f x) = f (K.nodeMap x)` 两步反证（记账：更短路线，零收窄）。 -/
theorem isoIsNodeNondegenerate {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β}
    (hiso : K.Iso H) (hnn : H.NodeNondegenerate) : K.NodeNondegenerate := by
  obtain ⟨f, hbij, hmaps⟩ := hiso
  intro x hx hcon
  exact hnn (f x) (hbij.mapsTo hx) (by rw [(hmaps x hx).2.1, hcon])

end Kepler.Text.TameSpine
