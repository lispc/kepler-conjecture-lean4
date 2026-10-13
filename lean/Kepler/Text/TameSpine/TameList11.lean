/-
  Kepler.Text.TameSpine.TameList11 — B1 Tame_list 地基批 11：原子理论章全量
  （tamespine-port-plan §4 批次表 B1 行；接续批 10 = TameList10.lean，
  HOL :5580-:7514 已由批 9/10 落，本批从 atom_subset_r :7515 起）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:7515-:8043）——原子理论章 15 枚全量：

  `atom_subset_r` :7515 / `atom_eq_last` :7532 / `atom_last_inj` :7550 /
  `atom_last_surj` :7602 / `atom_last_p` :7641 / `find_atom_part` :7699 /
  `find_atom_part2` :7720 / `head_of_atom_parts` :7740 / `atom_list_bij` :7778 /
  `parts_last_inj` :7850 / `next_el_map_last` :7868 / `find_pair_list_parts`
  :7887 / `f_list_quotient` :7922 / `f_list_quotient_alt` :7976 /
  `atom_choice_part` :8012。在 :8043 自然边界收批（dart_of 选择函数章
  :8043-:8221 需 face-CARD/BIJ 桥、quotient_list_iso_quotient :8223 需 hyp_iso
  装配，留批 12）。

  诚实记账（本批跳过/合并/桥引件）：
  - Hypermap 侧原子章（hypermap.hl:7758-8118 镜像）在 Kepler.Text.Hypermap
    （:6546 起）已全真，本批零复制只直引：`atom_subset_darts`（=
    lemma_atom_sub_loop）、`atom_eq_of_mem`（= lemma_identity_atom）、
    `atom_reflect`/`atom_sym`/`IsNodeGoing.trans`、`atomsOfFamily`、
    `atomChoice_eq_atom`（= unique_atom_choice）、`headOfAtom_eq`（=
    lemma_unique_head_of_atom）；批 10 的 `isNodeGoingLast1`/`isNodeGoingLast2Lemma`
    是本章两根 list↔hypermap 接口柱；
  - `set_of_list` ↦ 新公开载体 `setOfListSpine`（`{x | x ∈ r}`，与批 6
    `dartLoopOfList` 的成员集折算一致）；
  - `find_pair_list`（list_hypermap-compiled.hl:51）↦ 新公开载体
    `findPairListSpine`；`find_face_alt`（find_face = list_pairs ∘
    find_pair_list）在本载体下是定义性 rfl（`findFaceDarts` 的 def 体）；
    `find_pair_list_unique` 由 `findFaceDarts_some` + TameLp
    `flatten_nodup_inj` + 私件 `listPairsInj`（listPairs 单射性，经
    `List.ext_get`+`getElem_zip` 首分量投影）装配；
  - `atom_list`/`find_atom`（tame_defs2.hl:682-686）↦ 新公开载体
    `atomListSpine`/`findAtomSpine`（`findListSpine` 组合，批 7 定义）；
  - `next_el_MEM_map`（tame_list.hl:1011）：TameLp 公开件 `la7_nextEl_map`
    直引（零移植，本批首次消费）；同批新直引 TameLp 件
    `findFaceDarts_eq_of_mem`（= find_pair_list_unique + find_face_alt 的
    dart 级合并件）/`findFaceDarts_some`/`flatten_nodup_inj`；
  - `f_list_quotient` 的 ← 方向比 HOL 的 MESON 收口显式两段：r = r' 经
    `uniqSublistUnique`（LAST p' 同属 r 与 r'），p'' = p' 再经 parts 内
    uniqSublistUnique；f_list 到 next_el 的换形经
    `findFaceDarts_eq_of_mem` + 批 10 `partsListPairs` + `la7_nextEl_map`
    （HOL 的 find_face/find_pair_list 归并直达）；
  - `is_restricted → is_edge_nondegenerate`（head_of_atom_parts :7750/
    atom_choice_part :8017 的 ASM_MESON[is_restricted]）经
    `Hypermap.IsRestricted.edgeNondegenerate` 合取项直取；
  - `normal_list_normal` 的 L 隐参、`inverse_node_map_list` 的 L 隐参
    （build 模式可见性，见 playbook §5.3）；
  - 批 10 私件 `getLastMem` 不跨文件，§0 同证重推导（批 7→8→9→10 惯例）。

  载体折算（沿批 1-10 约定）：
  - `parts L r` ↦ `partsSpine L r`、`quotient_list L N` ↦ `quotientListSpine L N`、
    `core L r` ↦ `coreSpine L r`（批 7）、`loop_of_list r` ↦ `loopOfListSpine r`、
    `loop_family_of_list N` ↦ `loopFamilyOfListSpine N`（批 6）、
    `find_list` ↦ `findListSpine`（批 7）、`next_el` ↦ `nextEl`（Assembly）、
    `f_list`/`e_list` ↦ `fList`/`eList`（Assembly）、`hypermap_of_list L` ↦
    `hypermapOfList L hL`（GoodList 证人显式入参）、`uniq` ↦ `List.Nodup`、
    `LAST`/`HD` ↦ `List.getLast!`/`List.head!`、`BIJ` ↦ `Set.BijOn`、
    `darts_of_list`（= set_of_list ∘ list_of_darts）↦ `{d | d ∈ listOfDarts Q}`
    成员集形。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git 写操作。
  批 12 接续点：HOL :8365 `MEM_EXTENSION`/:8373 `loop_of_list_inj` 起
  （split_condition_list/min_num 块 :8396-:8746；或先清 dart_of 选择函数章
  :8043-:8221——本批 `findPairListSpine` 引擎已就位，仍需 Hypermap 侧
  face-CARD 与 node-BIJ 桥侦察）。
-/

import Kepler.Text.TameSpine.TameList10

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList fList prevEl GoodList listPairs listOfDarts
  findFaceDarts nList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt getElem_idxOf
   idxOf_getElem nextEl_mem_of_mem
   dart_in_face findFaceDarts_ex_of_self la7_length_listPairs
   hypermapOfList nodeMap_hypermapOfList findFaceDarts_nodup fList_mem_darts
   nList_fList la7_eList_involutory mem_darts_of_mem_findFace
   la7_nextEl_map findFaceDarts_eq_of_mem findFaceDarts_some flatten_nodup_inj
   GoodListNodesTl)

/-! ### §0 定义载体与私有引擎 -/

/-- HOL `set_of_list`（Seq.set_of_list）的集合载体。 -/
def setOfListSpine (r : List (ℕ × ℕ)) : Set (ℕ × ℕ) := {x | x ∈ r}

theorem setOfListSpine_mem {r : List (ℕ × ℕ)} (x : ℕ × ℕ) :
    x ∈ setOfListSpine r ↔ x ∈ r := Iff.rfl

/-- 非空表 `getLast!` 必是成员（批 10 私件同证重推导）。 -/
private theorem getLastMem {l : List (ℕ × ℕ)} (h : l ≠ []) : l.getLast! ∈ l := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- HOL `find_pair_list`（list_hypermap-compiled.hl:51-52）。 -/
def findPairListSpine (L : List (List ℕ)) (d : ℕ × ℕ) : List ℕ :=
  (L.find? fun l => decide (d ∈ listPairs l)).getD []

/-- HOL `atom_list`（tame_defs2.hl:682-683）。 -/
def atomListSpine (L : fgraph ℕ) (r : List (ℕ × ℕ)) (d : ℕ × ℕ) : List (ℕ × ℕ) :=
  findListSpine (partsSpine L r) d

/-- HOL `find_atom`（tame_defs2.hl:685-686）。 -/
def findAtomSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (d : ℕ × ℕ) : List (ℕ × ℕ) :=
  atomListSpine L (findListSpine N d) d

private theorem listPairsMapFst (l : List ℕ) : (listPairs l).map Prod.fst = l := by
  have hlen : (listPairs l).length = l.length := la7_length_listPairs l
  refine List.ext_get ?_ (fun i h1 h2 => ?_)
  · rw [List.length_map]; exact hlen
  · have hi : i < (listPairs l).length := List.length_map (f := Prod.fst) ▸ h1
    have hi2 : i < l.length := hlen ▸ hi
    show ((l.zip (l.drop 1 ++ List.take 1 l)).map Prod.fst)[i] = l[i]
    rw [List.getElem_map, List.getElem_zip]

private theorem listPairsInj {l1 l2 : List ℕ} (h : listPairs l1 = listPairs l2) : l1 = l2 :=
  (listPairsMapFst l1).symm.trans (h ▸ listPairsMapFst l2)

private theorem findPairListSpine_unique {Q : List (List ℕ)}
    (hn : (Q.map listPairs).flatten.Nodup) {l : List ℕ} (hl : l ∈ Q)
    {d : ℕ × ℕ} (hd : d ∈ listPairs l) :
    l = findPairListSpine Q d := by
  by_cases hval : Q.find? (fun l => decide (d ∈ listPairs l)) = none
  · exfalso
    have h9 := List.find?_eq_none.mp hval l hl
    simp only [decide_eq_true_eq] at h9
    exact h9 hd
  · obtain ⟨l', hl''⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : Q.find? (fun l => decide (d ∈ listPairs l)) = some l' := hl''.symm
    obtain ⟨heq, hdl', hl'mem⟩ := findFaceDarts_some hfeq
    have hd2 : d ∈ listPairs l' := hdl'
    have h1 : d ∈ (Q.map listPairs).flatten :=
      List.mem_flatten.mpr ⟨listPairs l, List.mem_map.mpr ⟨l, hl, rfl⟩, hd⟩
    have h2 : d ∈ (Q.map listPairs).flatten :=
      List.mem_flatten.mpr ⟨listPairs l', List.mem_map.mpr ⟨l', hl'mem, rfl⟩, hd2⟩
    have heq2 : listPairs l' = listPairs l :=
      flatten_nodup_inj hn (List.mem_map.mpr ⟨l', hl'mem, rfl⟩)
        (List.mem_map.mpr ⟨l, hl, rfl⟩) hd2 hd
    rw [findPairListSpine, hfeq, Option.getD_some]
    exact (listPairsInj heq2).symm

/-- **HOL `atom_subset_r`**（tame_list.hl:7515） -/
theorem atomSubsetR (L : fgraph ℕ) {hL : GoodList L} {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)} (hr : r ∈ N)
    {d : ℕ × ℕ} (hd : d ∈ r) :
    (hypermapOfList L hL).atom (loopOfListSpine r) d ⊆ setOfListSpine r := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hsub := Hypermap.atom_subset_darts (hypermapOfList L hL) (loopOfListSpine r)
    ((inDartLoopOfList hr1 hr2 d).mpr hd)
  intro x hxm
  have hx : x ∈ (loopOfListSpine r).darts := hsub hxm
  exact (inDartLoopOfList hr1 hr2 x).mp hx

/-- **HOL `atom_eq_last`**（tame_list.hl:7532） -/
theorem atomEqLast (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ p) :
    (hypermapOfList L hL).atom (loopOfListSpine r) d
      = (hypermapOfList L hL).atom (loopOfListSpine r) p.getLast! :=
  Hypermap.atom_eq_of_mem (hypermapOfList L hL)
    (Or.inl (isNodeGoingLast2Lemma L hL hn hnedg hunL hr hp hd))

/-- **HOL `parts_last_inj`**（tame_list.hl:7850） -/
theorem partsLastInj (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)} (hr : r ∈ N)
    {p p' : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) (hp' : p' ∈ partsSpine L r)
    (hlast : p.getLast! = p'.getLast!) : p = p' := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hfl : (partsSpine L r).flatten.Nodup := by
    rw [partsFlatten L hr1 hr2]; exact hr1
  exact uniqSublistUnique (partsSpine L r) hfl p hp p' hp'
    ⟨p.getLast!, getLastMem (partsAllNonnil L hr1 hr2 p hp), hlast ▸
      getLastMem (partsAllNonnil L hr1 hr2 p' hp')⟩

/-- **HOL `atom_last_inj`**（tame_list.hl:7550） -/
theorem atomLastInj (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    {r r' : List (ℕ × ℕ)} (hr : r ∈ N) (hr' : r' ∈ N)
    {p p' : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) (hp' : p' ∈ partsSpine L r')
    (heq : (hypermapOfList L hL).atom (loopOfListSpine r) p.getLast!
      = (hypermapOfList L hL).atom (loopOfListSpine r') p'.getLast!) :
    r = r' ∧ p.getLast! = p'.getLast! := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  obtain ⟨hr1', hr2'⟩ := normalListUniqNonnil hn hr'
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hpne' : p' ≠ [] := partsAllNonnil L hr1' hr2' p' hp'
  have hmemLp : p.getLast! ∈ r :=
    (partsUniqNonnil L hL hn hr hp).2.2.2.2 p.getLast! (getLastMem hpne)
  have hmemLp' : p'.getLast! ∈ r' :=
    (partsUniqNonnil L hL hn hr' hp').2.2.2.2 p'.getLast! (getLastMem hpne')
  have hm : p'.getLast! ∈ (hypermapOfList L hL).atom (loopOfListSpine r') p'.getLast! :=
    Hypermap.atom_reflect _ _ _
  rw [heq.symm] at hm
  have hmr' : p'.getLast! ∈ r :=
    (atomSubsetR L hn hr hmemLp hm : p'.getLast! ∈ r)
  have hrr : r = r' := uniqSublistUnique N hn.1 r hr r' hr'
    ⟨p'.getLast!, hmr', hmemLp'⟩
  subst hrr
  rcases hm with hgo | hgo
  · exact ⟨rfl, ((isNodeGoingLast1 L hL hn hnedg hunL hr hp p'.getLast!).mp hgo).symm⟩
  · exact ⟨rfl, (isNodeGoingLast1 L hL hn hnedg hunL hr hp' p.getLast!).mp hgo⟩

/-- **HOL `atom_last_surj`**（tame_list.hl:7602） -/
theorem atomLastSurj (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    {a : Set (ℕ × ℕ)}
    (ha : a ∈ (hypermapOfList L hL).atomsOfFamily (loopFamilyOfListSpine N)) :
    ∃ r : List (ℕ × ℕ), ∃ p : List (ℕ × ℕ),
      p ∈ partsSpine L r ∧ r ∈ N ∧
      a = (hypermapOfList L hL).atom (loopOfListSpine r) p.getLast! := by
  obtain ⟨L', hL', x, hx, rfl⟩ := ha
  obtain ⟨r, hr, rfl⟩ := hL'
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hxr : x ∈ r := (inDartLoopOfList hr1 hr2 x).mp hx
  have hxfl : x ∈ (partsSpine L r).flatten := by
    rw [partsFlatten L hr1 hr2]; exact hxr
  obtain ⟨p, hp, hxp⟩ := List.mem_flatten.mp hxfl
  exact ⟨r, p, hp, hr, atomEqLast L hL hn hnedg hunL hr hp hxp⟩

/-- **HOL `atom_last_p`**（tame_list.hl:7641） -/
theorem atomLastP (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) :
    (hypermapOfList L hL).atom (loopOfListSpine r) p.getLast! = setOfListSpine p := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  ext x
  constructor
  · rintro (hgo | hgo)
    · exact ((isNodeGoingLast1 L hL hn hnedg hunL hr hp x).mp hgo) ▸ getLastMem hpne
    · have hmemLp : p.getLast! ∈ r :=
        (partsUniqNonnil L hL hn hr hp).2.2.2.2 p.getLast! (getLastMem hpne)
      have hxr : x ∈ r := (atomSubsetR L hn hr hmemLp (Or.inr hgo) : x ∈ r)
      have hxfl : x ∈ (partsSpine L r).flatten := by
        rw [partsFlatten L hr1 hr2]; exact hxr
      obtain ⟨p', hp'', hxp'⟩ := List.mem_flatten.mp hxfl
      have hmem' : x ∈ (hypermapOfList L hL).atom (loopOfListSpine r) p'.getLast! :=
        Or.inr (isNodeGoingLast2Lemma L hL hn hnedg hunL hr hp'' hxp')
      have heq : (hypermapOfList L hL).atom (loopOfListSpine r) p.getLast!
          = (hypermapOfList L hL).atom (loopOfListSpine r) p'.getLast! :=
        (Hypermap.atom_eq_of_mem (hypermapOfList L hL) (Or.inr hgo)).trans
          (Hypermap.atom_eq_of_mem (hypermapOfList L hL) hmem').symm
      obtain ⟨-, hlast⟩ := atomLastInj L hL hn hnedg hunL hr hr hp hp'' heq
      rw [partsLastInj L hL hn hr hp hp'' hlast]
      exact hxp'
  · intro hx
    exact Or.inr (isNodeGoingLast2Lemma L hL hn hnedg hunL hr hp hx)

/-- **HOL `find_atom_part`**（tame_list.hl:7699） -/
theorem findAtomPart (L : fgraph ℕ) {hL : GoodList L} {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)} (hr : r ∈ N)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) :
    findAtomSpine L N p.getLast! = p := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have h1 : findListSpine N p.getLast! = r :=
    findListUniq hn.1 ((partsUniqNonnil L hL hn hr hp).2.2.2.2 p.getLast!
      (getLastMem hpne)) hr
  show findListSpine (partsSpine L (findListSpine N p.getLast!)) p.getLast! = p
  rw [h1]
  have hfl : (partsSpine L r).flatten.Nodup := by
    rw [partsFlatten L hr1 hr2]; exact hr1
  exact findListUniq hfl (getLastMem hpne) hp

/-- **HOL `find_atom_part2`**（tame_list.hl:7720） -/
theorem findAtomPart2 (L : fgraph ℕ) {hL : GoodList L} {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)} (hr : r ∈ N)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) {d : ℕ × ℕ} (hd : d ∈ p) :
    findAtomSpine L N d = p := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have h1 : findListSpine N d = r :=
    findListUniq hn.1 ((partsUniqNonnil L hL hn hr hp).2.2.2.2 d hd) hr
  show findListSpine (partsSpine L (findListSpine N d)) d = p
  rw [h1]
  have hfl : (partsSpine L r).flatten.Nodup := by
    rw [partsFlatten L hr1 hr2]; exact hr1
  exact findListUniq hfl hd hp

/-- **HOL `head_of_atom_parts`**（tame_list.hl:7740） -/
theorem headOfAtomParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hunL : ∀ l ∈ L, l.Nodup)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ p) :
    (hypermapOfList L hL).headOfAtom (loopFamilyOfListSpine N) d = p.getLast! := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hnedg := hres.edgeNondegenerate
  have hnf := normalListNormal hL hgn hres hn
  have hdR : d ∈ r := (partsUniqNonnil L hL hn hr hp).2.2.2.2 d hd
  have hxD : d ∈ (loopOfListSpine r).darts := (inDartLoopOfList hr1 hr2 d).mpr hdR
  have hm0 : p.getLast! ∈ (hypermapOfList L hL).atom (loopOfListSpine r) p.getLast! :=
    Hypermap.atom_reflect _ _ _
  have hm : p.getLast! ∈ (hypermapOfList L hL).atom (loopOfListSpine r) d := by
    rw [atomEqLast L hL hn hnedg hunL hr hp hd]; exact hm0
  have hlastD : p.getLast! ∈ listOfDarts L := partsDarts L hn hr hp (getLastMem hpne)
  refine Hypermap.headOfAtom_eq (hypermapOfList L hL) hnf ⟨r, hr, rfl⟩ hxD hm ?_
  rw [loopMapNextEl hr1 hr2, inverseNodeMapList hL hlastD]
  exact normalListPartsNextLastNot L hL hn hnedg hr hp

/-- **HOL `atom_list_bij`**（tame_list.hl:7778） -/
theorem atomListBij (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup) :
    Set.BijOn (fun d : ℕ × ℕ => setOfListSpine (findAtomSpine L N d))
      {d | d ∈ listOfDarts (quotientListSpine L N)}
      ((hypermapOfList L hL).atomsOfFamily (loopFamilyOfListSpine N)) := by
  refine ⟨fun d hd => ?_, fun d1 hd1 d2 hd2 hcon => ?_, fun a ha => ?_⟩
  · obtain ⟨p, r, hp, hr, rfl⟩ := (memListOfDartsQuotient L hL hn hnedg hunL d).mp hd
    obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
    have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
    show setOfListSpine (findAtomSpine L N p.getLast!)
      ∈ (hypermapOfList L hL).atomsOfFamily (loopFamilyOfListSpine N)
    rw [findAtomPart2 L hn hr hp (getLastMem hpne)]
    exact ⟨loopOfListSpine r, ⟨r, hr, rfl⟩, p.getLast!,
      (inDartLoopOfList hr1 hr2 p.getLast!).mpr
        ((partsUniqNonnil L hL hn hr hp).2.2.2.2 p.getLast! (getLastMem hpne)),
      (atomLastP L hL hn hnedg hunL hr hp).symm⟩
  · obtain ⟨p, r, hp, hr, rfl⟩ := (memListOfDartsQuotient L hL hn hnedg hunL d1).mp hd1
    obtain ⟨p', r', hp', hr', rfl⟩ :=
      (memListOfDartsQuotient L hL hn hnedg hunL d2).mp hd2
    obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
    obtain ⟨hr1', hr2'⟩ := normalListUniqNonnil hn hr'
    have hcon' : setOfListSpine (findAtomSpine L N p.getLast!)
        = setOfListSpine (findAtomSpine L N p'.getLast!) := hcon
    rw [findAtomPart2 L hn hr hp (getLastMem (partsAllNonnil L hr1 hr2 p hp)),
      findAtomPart2 L hn hr' hp' (getLastMem (partsAllNonnil L hr1' hr2' p' hp'))] at hcon'
    have heq : (hypermapOfList L hL).atom (loopOfListSpine r) p.getLast!
        = (hypermapOfList L hL).atom (loopOfListSpine r') p'.getLast! := by
      rw [atomLastP L hL hn hnedg hunL hr hp, atomLastP L hL hn hnedg hunL hr' hp', hcon']
    obtain ⟨-, hlast⟩ := atomLastInj L hL hn hnedg hunL hr hr' hp hp' heq
    exact hlast
  · obtain ⟨r, p, hp, hr, heq⟩ := atomLastSurj L hL hn hnedg hunL ha
    refine ⟨p.getLast!,
      (memListOfDartsQuotient L hL hn hnedg hunL p.getLast!).mpr ⟨p, r, hp, hr, rfl⟩, ?_⟩
    show setOfListSpine (findAtomSpine L N p.getLast!) = a
    rw [findAtomPart L hn hr hp, heq]
    exact (atomLastP L hL hn hnedg hunL hr hp).symm

/-- **HOL `next_el_map_last`**（tame_list.hl:7868） -/
theorem nextElMapLast (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)} (hr : r ∈ N)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) :
    nextEl ((partsSpine L r).map (fun q => q.getLast!)) p.getLast!
      = (nextEl (partsSpine L r) p).getLast! :=
  la7_nextEl_map (l := partsSpine L r) (f := fun q => q.getLast!)
    (fun _u hu _v hv huv => partsLastInj L hL hn hr hu hv huv) hp

/-- **HOL `find_pair_list_parts`**（tame_list.hl:7887） -/
theorem findPairListParts (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) :
    coreSpine L r = findPairListSpine (quotientListSpine L N) p.getLast! := by
  have hQnod : (listOfDarts (quotientListSpine L N)).Nodup :=
    listOfDartsQuotientUniq L hL hn hnedg hunL
  have hmem : (partsSpine L r).map (fun a => a.head!.1) ∈ quotientListSpine L N := by
    show (partsSpine L r).map (fun a => a.head!.1) ∈ (N.map (partsSpine L)).map
      (fun f => f.map (fun a => a.head!.1))
    exact List.mem_map.mpr ⟨partsSpine L r, List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩
  have hd : p.getLast! ∈ listPairs ((partsSpine L r).map (fun q => q.head!.1)) := by
    rw [partsListPairs L hL hn hnedg hunL hr]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  exact findPairListSpine_unique hQnod hmem hd

/-- **HOL `f_list_quotient`**（tame_list.hl:7922） -/
theorem fListQuotient (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    {r r' : List (ℕ × ℕ)} (hr : r ∈ N) (hr' : r' ∈ N)
    {p p' : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) (hp' : p' ∈ partsSpine L r') :
    (fList (quotientListSpine L N) p.getLast! = p'.getLast! ↔
      nextEl (partsSpine L r) p = p') := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  obtain ⟨hr1', hr2'⟩ := normalListUniqNonnil hn hr'
  have hpne' : p' ≠ [] := partsAllNonnil L hr1' hr2' p' hp'
  have hQnod : (listOfDarts (quotientListSpine L N)).Nodup :=
    listOfDartsQuotientUniq L hL hn hnedg hunL
  have hmem : (partsSpine L r).map (fun a => a.head!.1) ∈ quotientListSpine L N := by
    show (partsSpine L r).map (fun a => a.head!.1) ∈ (N.map (partsSpine L)).map
      (fun f => f.map (fun a => a.head!.1))
    exact List.mem_map.mpr ⟨partsSpine L r, List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩
  have hd : p.getLast! ∈ listPairs ((partsSpine L r).map (fun q => q.head!.1)) := by
    rw [partsListPairs L hL hn hnedg hunL hr]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hkey : fList (quotientListSpine L N) p.getLast!
      = (nextEl (partsSpine L r) p).getLast! := by
    show nextEl (findFaceDarts (quotientListSpine L N) p.getLast!) p.getLast! = _
    rw [findFaceDarts_eq_of_mem hQnod hmem hd, partsListPairs L hL hn hnedg hunL hr]
    exact la7_nextEl_map (l := partsSpine L r) (f := fun q => q.getLast!)
      (fun u hu v hv huv => partsLastInj L hL hn hr hu hv huv) hp
  rw [hkey]
  constructor
  · intro hcon
    by_cases hmemP' : p' ∈ partsSpine L r
    · exact partsLastInj L hL hn hr (nextEl_mem_of_mem hp) hmemP' hcon
    · exfalso
      have hw : nextEl (partsSpine L r) p ∈ partsSpine L r := nextEl_mem_of_mem hp
      have hLr : p'.getLast! ∈ r := by
        have h1 : (nextEl (partsSpine L r) p).getLast! ∈ r :=
          (partsUniqNonnil L hL hn hr hw).2.2.2.2 _
            (getLastMem (partsAllNonnil L hr1 hr2 _ hw))
        rw [← hcon]; exact h1
      have hLr' : p'.getLast! ∈ r' :=
        (partsUniqNonnil L hL hn hr' hp').2.2.2.2 p'.getLast! (getLastMem hpne')
      have hrr : r = r' := uniqSublistUnique N hn.1 r hr r' hr'
        ⟨p'.getLast!, hLr, hLr'⟩
      exact hmemP' (hrr ▸ hp')
  · intro hcon
    rw [hcon]

/-- **HOL `f_list_quotient_alt`**（tame_list.hl:7976） -/
theorem fListQuotientAlt (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    {r r' : List (ℕ × ℕ)} (hr : r ∈ N) (hr' : r' ∈ N)
    {p p' : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) (hp' : p' ∈ partsSpine L r') :
    (nextEl (partsSpine L r) p = p' ↔ fList L p.getLast! ∈ p') := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  obtain ⟨hr1', hr2'⟩ := normalListUniqNonnil hn hr'
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hpne' : p' ≠ [] := partsAllNonnil L hr1' hr2' p' hp'
  have hkey : fList L p.getLast! = (nextEl (partsSpine L r) p).head! :=
    (normalListPartsNextLast L hL hn hr hp).symm.trans
      (nextElPartsLast L hr1 hr2 hp (getLastMem hpne) rfl)
  constructor
  · intro h
    rw [hkey, h]
    exact List.head!_mem_self hpne'
  · intro hcon
    rw [hkey] at hcon
    have hw : nextEl (partsSpine L r) p ∈ partsSpine L r := nextEl_mem_of_mem hp
    have hhd : (nextEl (partsSpine L r) p).head! ∈ nextEl (partsSpine L r) p :=
      List.head!_mem_self (partsAllNonnil L hr1 hr2 _ hw)
    have hfinR : (nextEl (partsSpine L r) p).head! ∈ r :=
      (partsUniqNonnil L hL hn hr hw).2.2.2.2 _ hhd
    have hfinP : (nextEl (partsSpine L r) p).head! ∈ r' :=
      (partsUniqNonnil L hL hn hr' hp').2.2.2.2 _ hcon
    have hrr : r = r' := uniqSublistUnique N hn.1 r hr r' hr'
      ⟨(nextEl (partsSpine L r) p).head!, hfinR, hfinP⟩
    subst hrr
    exact uniqSublistUnique (partsSpine L r)
      (by rw [partsFlatten L hr1 hr2]; exact hr1) _ hw p' hp'
      ⟨(nextEl (partsSpine L r) p).head!, hhd, hcon⟩

/-- **HOL `atom_choice_part`**（tame_list.hl:8012） -/
theorem atomChoicePart (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) (hunL : ∀ l ∈ L, l.Nodup)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r) :
    (hypermapOfList L hL).atomChoice (loopFamilyOfListSpine N) p.getLast!
      = setOfListSpine p := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hnf := normalListNormal hL hgn hres hn
  have hx : p.getLast! ∈ (loopOfListSpine r).darts :=
    (inDartLoopOfList hr1 hr2 p.getLast!).mpr
      ((partsUniqNonnil L hL hn hr hp).2.2.2.2 p.getLast! (getLastMem hpne))
  rw [Hypermap.atomChoice_eq_atom (hypermapOfList L hL) hnf ⟨r, hr, rfl⟩ hx,
    atomLastP L hL hn hnedg hunL hr hp]

end Kepler.Text.TameSpine
