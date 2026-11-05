/-
  Kepler.Text.TameCorrNode — `tame_correspondence_iso` 三波施工的 **W3 第五波 a**：
  **node 轨道引擎**（HOL `tame_list.hl:4399` `MEM_hypermap_of_list_node` 同型）
  + `dart_of` 两小件。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrCard`（→ TameCorrList → TameCorrFloor
  │ → TameLp + Graphs；闭包零 `Kepler.Assembly` 本体）。
  │ 环自检：`#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │ 必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 逐件对照**：
  · `MEM_hypermap_of_list_node`（tame_list.hl:4399-:4411）：
    `good_list L /\ good_list_nodes L /\ MEM x (list_of_darts L) ==>
      y IN node (hypermap_of_list L) x <=> FST x = FST y /\ MEM y (list_of_darts L)`
    ↦ `memHypermapOfListNode`（`GoodListNodesTl` 前提，`FST` ↦ `Prod.fst`）。
  · `dart_of`（tame_list.hl:8070 `new_specification`；`dart_of_find_face` :8073）
    ↦ 本模块 `dartOf f v := (v, nextEl f v)` + 成员/推进三件。
    HOL 的 `dart_of` 是规格函数（存在性由 `dart_of_exists` 给），Lean 取显式构造
    并逐条证明规格（`dartOf_mem_listOfDarts` + `findFaceDarts_dartOf`）。

  **证明路线（自证）**：
  ⊆ 向对 `nodeMap` 幂归纳；核心是 `(nList L z).1 = z.1`（z ∈ listOfDarts）——
  取 z 所在面表 `s = find_face L z = list_pairs l`，`nList z = eList (prev_el s z)`，
  用 `next_el (prev_el s z) = z` 与自证的面表链式事实
  `(next_el s y).1 = y.2`（`list_pairs` 的逐下标形态 `(l[i], l[(i+1)%len])` 给出）。
  ⊇ 向用 `GoodListNodesTl`（`nodeSet = nodesOfListSet`）把 `node x` 钉成
  「同 FST 的 dart 全类」，再做轨道传递。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrCard

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrNode

open Classical
open Kepler.Assembly (listPairs listOfDarts findFaceDarts fList nList nextEl prevEl eList GoodList)
open Kepler.Text (Hypermap orbitMap)
open Kepler.Text.TameLp (hypermapOfList faceMap_hypermapOfList nodeMap_hypermapOfList
  dart_in_face findFaceDarts_eq_of_mem findFaceDarts_congr_of_mem findFaceDarts_nodup
  mem_darts_of_mem_findFace nextEl_eq_getD nextEl_mem_of_mem prevEl_mem_of_mem
  nextEl_prevEl prevEl_nextEl getD_eq_getElem_of_lt getElem_idxOf idxOf_getElem
  findFaceDarts_ex_of_self
  la7_length_listPairs GoodListNodesTl nodesOfListSet)
open Kepler.Graphs (fgraph)

/-! ## §1 `list_pairs` 逐下标引擎（自证） -/

/-- 同表两下标相等则取元相等（proof-irrelevant `getElem` 换形器）。 -/
private theorem getElem_congr_idx {α : Type*} {l : List α} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (h : i = j) :
    l[i]'hi = l[j]'hj := by
  subst h
  rfl

/-- `drop 1 ++ take 1` 第 `i` 项的 `getElem?` 形态（无依赖证据，mod 下标）。 -/
private theorem getElem?_drop_take (l : List ℕ) {i : ℕ} (hi : i < l.length) :
    (l.drop 1 ++ l.take 1)[i]? = l[(i + 1) % l.length]? := by
  by_cases h : i < (l.drop 1).length
  · have hi1 : i + 1 < l.length := by
      rw [List.length_drop] at h
      omega
    rw [List.getElem?_append, if_pos h, List.getElem?_drop]
    rw [show 1 + i = i + 1 by omega, Nat.mod_eq_of_lt hi1]
  · have hi0 : i = l.length - 1 := by
      rw [List.length_drop] at h
      omega
    rw [List.getElem?_append, if_neg h, List.getElem?_take,
      if_pos (by rw [List.length_drop, hi0]; omega)]
    have hz : i - (l.drop 1).length = 0 := by
      rw [List.length_drop, hi0]
      omega
    have hz2 : (i + 1) % l.length = 0 := by
      rw [hi0, show l.length - 1 + 1 = l.length by omega, Nat.mod_self]
    rw [hz, hz2]

/-- `drop 1 ++ take 1` 第 `i` 项 = `l[(i+1) % len]`（getElem 形态，经 getD 换装）。 -/
private theorem getElem_drop_take {l : List ℕ} {i : ℕ}
    (hp : i < (l.drop 1 ++ l.take 1).length)
    (hq : (i + 1) % l.length < l.length) :
    (l.drop 1 ++ l.take 1)[i]'hp = l[(i + 1) % l.length]'hq := by
  have hlen : (l.drop 1 ++ l.take 1).length = l.length := by
    rw [List.length_append, List.length_drop, List.length_take]
    omega
  have hi : i < l.length := by omega
  rw [← getD_eq_getElem_of_lt hp (0 : ℕ), ← getD_eq_getElem_of_lt hq (0 : ℕ),
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, getElem?_drop_take l hi]

/-- `list_pairs` 的逐下标形态：第 `i` 项 = `(l[i], l[(i+1) % len])`。 -/
private theorem getElem_listPairs {l : List ℕ} {i : ℕ}
    (hi : i < (listPairs l).length) :
    (listPairs l)[i]'hi
      = (l[i]'(by rw [← la7_length_listPairs]; exact hi),
          l[(i + 1) % l.length]'(by
            have hlt := hi
            rw [la7_length_listPairs] at hlt
            exact Nat.mod_lt _ (by omega))) := by
  show (l.zip (l.drop 1 ++ l.take 1))[i]'hi = _
  rw [List.getElem_zip]
  refine Prod.ext ?_ ?_
  · rfl
  · exact getElem_drop_take _ _

/-- `list_pairs` 第 `i` 项的首分量 = `l[i]`。 -/
private theorem fst_getElem_listPairs {l : List ℕ} {i : ℕ}
    (hi : i < (listPairs l).length) :
    ((listPairs l)[i]'hi).1 = l[i]'(by rw [← la7_length_listPairs]; exact hi) := by
  rw [getElem_listPairs hi]

/-- `list_pairs` 第 `i` 项的次分量 = `l[(i+1) % len]`。 -/
private theorem snd_getElem_listPairs {l : List ℕ} {i : ℕ}
    (hi : i < (listPairs l).length) :
    ((listPairs l)[i]'hi).2 = l[(i + 1) % l.length]'(by
      have hlt := hi
      rw [la7_length_listPairs] at hlt
      exact Nat.mod_lt _ (by omega)) := by
  rw [getElem_listPairs hi]

/-- 面表链式事实：`(next_el s y).1 = y.2`（`s = list_pairs l` 的循环相邻性）。 -/
private theorem fst_nextEl_eq_snd {l : List ℕ} (hs : (listPairs l).Nodup) :
    ∀ y ∈ listPairs l, (nextEl (listPairs l) y).1 = y.2 := by
  intro y hy
  have hlen : (listPairs l).length = l.length := la7_length_listPairs l
  have hpos : 0 < (listPairs l).length := List.length_pos_of_mem hy
  have hj : (listPairs l).idxOf y < (listPairs l).length :=
    List.idxOf_lt_length_iff.mpr hy
  have hyy : y = (listPairs l)[(listPairs l).idxOf y]'hj := (getElem_idxOf hy).symm
  have hnext : nextEl (listPairs l) y
      = (listPairs l)[((listPairs l).idxOf y + 1) % (listPairs l).length]'
          (Nat.mod_lt _ hpos) := by
    rw [hyy, nextEl_eq_getD (List.getElem_mem hj), idxOf_getElem hs hj,
      getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
  rw [hnext, fst_getElem_listPairs]
  conv_rhs => rw [hyy]
  rw [snd_getElem_listPairs]
  exact getElem_congr_idx _ _ (by rw [hlen])

/-! ## §2 node 轨道引擎 -/

/-- `nList` 保住首分量（`FST (n_list L z) = FST z`，z ∈ listOfDarts）。 -/
theorem fst_nList_eq {L : fgraph ℕ} (hL : GoodList L) {z : ℕ × ℕ}
    (hz : z ∈ listOfDarts L) : (nList L z).1 = z.1 := by
  have hzs : z ∈ findFaceDarts L z := (dart_in_face L z).mpr hz
  have hnod : (findFaceDarts L z).Nodup := findFaceDarts_nodup hL.1 z
  obtain ⟨l, _hl, hfind, _hzl⟩ := findFaceDarts_ex_of_self hzs
  have hnod' : (listPairs l).Nodup := by rwa [hfind] at hnod
  have hchain : ∀ y ∈ findFaceDarts L z, (nextEl (findFaceDarts L z) y).1 = y.2 := by
    intro y hy
    rw [hfind] at hy ⊢
    exact fst_nextEl_eq_snd hnod' y hy
  have hy : prevEl (findFaceDarts L z) z ∈ findFaceDarts L z := prevEl_mem_of_mem hzs
  have hnext : nextEl (findFaceDarts L z) (prevEl (findFaceDarts L z) z) = z :=
    nextEl_prevEl hnod hzs
  have h1 := hchain _ hy
  rw [hnext] at h1
  show (eList (prevEl (findFaceDarts L z) z)).1 = z.1
  exact h1.symm

/-- `nList` 保持在 `listOfDarts` 内（`e_list` 的 `GoodList` 逆闭包）。 -/
theorem nList_mem_darts {L : fgraph ℕ} (hL : GoodList L) {z : ℕ × ℕ}
    (hz : z ∈ listOfDarts L) : nList L z ∈ listOfDarts L := by
  have hzs : z ∈ findFaceDarts L z := (dart_in_face L z).mpr hz
  have hprev : prevEl (findFaceDarts L z) z ∈ listOfDarts L :=
    mem_darts_of_mem_findFace L (prevEl_mem_of_mem hzs)
  show eList (prevEl (findFaceDarts L z) z) ∈ listOfDarts L
  exact hL.2.2 _ hprev

/-- `nodeMap` 幂的轨道不变量：首分量固定、成员保持在 `listOfDarts`。 -/
theorem nodeMap_pow_invariant {L : fgraph ℕ} (hL : GoodList L) {x : ℕ × ℕ}
    (hx : x ∈ listOfDarts L) (n : ℕ) :
    (((hypermapOfList L hL).nodeMap ^ n) x).1 = x.1 ∧
      ((hypermapOfList L hL).nodeMap ^ n) x ∈ listOfDarts L := by
  induction n with
  | zero => simpa using (show x.1 = x.1 ∧ x ∈ listOfDarts L from ⟨rfl, hx⟩)
  | succ k ih =>
    have hd : ((hypermapOfList L hL).nodeMap ^ k) x ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr ih.2
    rw [pow_succ', Equiv.Perm.mul_apply, nodeMap_hypermapOfList L hL hd]
    exact ⟨by rw [fst_nList_eq hL ih.2, ih.1], nList_mem_darts hL ih.2⟩

/-- `node` 轨道的 → 向：轨道元素同首分量且在 `listOfDarts` 内。 -/
theorem memNode_forward {L : fgraph ℕ} (hL : GoodList L) {x y : ℕ × ℕ}
    (hx : x ∈ listOfDarts L) (hy : y ∈ (hypermapOfList L hL).node x) :
    x.1 = y.1 ∧ y ∈ listOfDarts L := by
  simp only [Hypermap.node, orbitMap, Set.mem_setOf_eq] at hy
  obtain ⟨n, hn⟩ := hy
  subst hn
  exact ⟨(nodeMap_pow_invariant hL hx n).1.symm, (nodeMap_pow_invariant hL hx n).2⟩

/-- `node` 轨道的 ← 向：`GoodListNodesTl` 把 `node x` 钉成同 FST 的 dart 全类。 -/
theorem memNode_backward {L : fgraph ℕ} (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {x y : ℕ × ℕ} (hx : x ∈ listOfDarts L) (hfst : x.1 = y.1)
    (hyd : y ∈ listOfDarts L) : y ∈ (hypermapOfList L hL).node x := by
  have hxd : x ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hx
  have hmem : (hypermapOfList L hL).node x ∈ (hypermapOfList L hL).nodeSet :=
    ⟨x, hxd, rfl⟩
  rw [hgn] at hmem
  unfold nodesOfListSet at hmem
  rw [Set.mem_image] at hmem
  obtain ⟨v, _hv, hclass⟩ := hmem
  have hclass' : {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = v}
      = (hypermapOfList L hL).node x := hclass
  have hxnode : x ∈ (hypermapOfList L hL).node x :=
    Kepler.Text.Hypermap.mem_node_self _ x
  have hxv : x.1 = v := by
    have hxcl : x ∈ {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = v} := by
      rw [hclass']
      exact hxnode
    simp only [Set.mem_setOf_eq] at hxcl
    exact hxcl.2
  have hyv : y.1 = v := by
    rw [← hfst, hxv]
  have hycl : y ∈ {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = v} := by
    simp only [Set.mem_setOf_eq]
    exact ⟨hyd, hyv⟩
  rw [hclass'] at hycl
  exact hycl

/-- HOL `MEM_hypermap_of_list_node`（tame_list.hl:4399）：
`good_list L ∧ good_list_nodes L ∧ MEM x (list_of_darts L) ⇒
 y ∈ node (hypermap_of_list L) x ⇔ FST x = FST y ∧ MEM y (list_of_darts L)`。 -/
theorem memHypermapOfListNode {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {x y : ℕ × ℕ} (hx : x ∈ listOfDarts L) :
    y ∈ (hypermapOfList L hL).node x ↔ (x.1 = y.1 ∧ y ∈ listOfDarts L) :=
  ⟨memNode_forward hL hx, fun h => memNode_backward hL hgn hx h.1 h.2⟩

/-! ## §3 `dart_of`（`dartOf f v := (v, nextEl f v)`；HOL tame_list.hl:8070） -/

/-- HOL `dart_of` 的显式构造：面 `f` 上顶点 `v` 处的 dart。 -/
def dartOf (f : List ℕ) (v : ℕ) : ℕ × ℕ := (v, nextEl f v)

/-- `dart_of` 首分量 = 给定顶点（HOL `dart_of` 规格的 `FST d = v`）。 -/
theorem dartOf_fst (f : List ℕ) (v : ℕ) : (dartOf f v).1 = v := rfl

/-- `dart_of` 落在面表 `list_pairs f` 内（HOL `dart_of` 规格的成员半向）。 -/
theorem dartOf_mem_listPairs {f : List ℕ} {v : ℕ} (hv : v ∈ f) :
    dartOf f v ∈ listPairs f := by
  have hpos : 0 < f.length := List.length_pos_of_mem hv
  have hlt : f.idxOf v < f.length := List.idxOf_lt_length_iff.mpr hv
  have hidx : f.idxOf v < (listPairs f).length := by
    rwa [la7_length_listPairs]
  have hdart : dartOf f v
      = (f[f.idxOf v]'hlt, f[(f.idxOf v + 1) % f.length]'(Nat.mod_lt _ hpos)) := by
    unfold dartOf
    have h1 : v = f[f.idxOf v]'hlt := (getElem_idxOf hv).symm
    conv_lhs => rw [h1]
    congr 1
    rw [nextEl_eq_getD (List.getElem_mem hlt)]
    have hidx2 : f.idxOf (f[f.idxOf v]'hlt) = f.idxOf v := by
      rw [getElem_idxOf hv]
    rw [hidx2, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
  rw [hdart]
  have hmem := List.getElem_mem (l := listPairs f) (n := f.idxOf v) hidx
  rwa [getElem_listPairs hidx] at hmem

/-- `dart_of` 落在 `list_of_darts L` 内（HOL `dart_of` 规格的成员全向）。 -/
theorem dartOf_mem_listOfDarts {L : fgraph ℕ} {f : List ℕ} {v : ℕ}
    (hf : f ∈ L) (hv : v ∈ f) : dartOf f v ∈ listOfDarts L :=
  List.mem_flatten.mpr ⟨listPairs f, List.mem_map.mpr ⟨f, hf, rfl⟩,
    dartOf_mem_listPairs hv⟩

/-- HOL `dart_of_find_face`（tame_list.hl:8073）：`find_face L (dart_of L f v) = list_pairs f`。 -/
theorem findFaceDarts_dartOf {L : fgraph ℕ} (hL : GoodList L) {f : List ℕ}
    (hf : f ∈ L) {v : ℕ} (hv : v ∈ f) :
    findFaceDarts L (dartOf f v) = listPairs f :=
  findFaceDarts_eq_of_mem hL.1 hf (dartOf_mem_listPairs hv)


/-! ## §4 顺带：G1 第二件（HOL WMLNYMD.hl:107） -/

/-- `eraseDups` 无重复（本工具链无现成 nodup 引理；按长度强归纳自证）。 -/
private theorem nodup_eraseDups {α : Type*} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup := by
  suffices h : ∀ n, ∀ l : List α, l.length = n → l.eraseDups.Nodup from h l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hlen
    cases l with
    | nil => simp [List.eraseDups]
    | cons a t =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_eraseDups] at hmem
        obtain ⟨_, hp⟩ := List.mem_filter.mp hmem
        rw [beq_self_eq_true a] at hp
        simp at hp
      · have hle := List.length_filter_le (fun b : α => !(b == a)) t
        exact ih _ (by rw [← hlen]; simp only [List.length_cons]; omega) _ rfl

/-- `list_of_elements` 集合的基数 = 其长度（`eraseDups` 无重复）。 -/
private theorem ncard_elementsOfList (L : fgraph ℕ) :
    (Kepler.Text.TameLp.elementsOfList L).ncard
      = (Kepler.Text.TameLp.listOfElements L).length := by
  have hnod : (Kepler.Text.TameLp.listOfElements L).Nodup := nodup_eraseDups _
  have hset : Kepler.Text.TameLp.elementsOfList L
      = ((Kepler.Text.TameLp.listOfElements L).toFinset : Set ℕ) := by
    ext x
    simp [Kepler.Text.TameLp.elementsOfList]
  rw [hset, Set.ncard_coe_finset]
  exact List.toFinset_card_of_nodup hnod

/-- 同 FST 的 dart 全类映射在 `elements_of_list` 上单射（每个元素都有 dart 见证）。 -/
private theorem class_injOn (L : fgraph ℕ) :
    Set.InjOn (fun v : ℕ => {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = v})
      {x | x ∈ Kepler.Text.TameLp.listOfElements L} := by
  intro v1 hv1 v2 _hv2 heq
  have hmem1 : v1 ∈ L.flatten := by
    have := hv1
    simpa [Kepler.Text.TameLp.listOfElements, List.mem_eraseDups] using this
  obtain ⟨l1, hl1, hvl1⟩ := List.mem_flatten.mp hmem1
  have hdart1 : dartOf l1 v1 ∈ listOfDarts L := dartOf_mem_listOfDarts hl1 hvl1
  have hfst1 : (dartOf l1 v1).1 = v1 := dartOf_fst l1 v1
  have hcl : dartOf l1 v1 ∈ {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = v1} :=
    ⟨hdart1, hfst1⟩
  have heq' : {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = v1}
      = {d : ℕ × ℕ | d ∈ listOfDarts L ∧ d.1 = v2} := heq
  rw [heq'] at hcl
  simp only [Set.mem_setOf_eq] at hcl
  rw [hfst1] at hcl
  exact hcl.2

/-- `nodes_of_list` 集合的基数 = `list_of_elements` 长度（单射像 + 无重复）。 -/
private theorem nodesOfListSet_ncard (L : fgraph ℕ) :
    (Kepler.Text.TameLp.nodesOfListSet L).ncard
      = (Kepler.Text.TameLp.listOfElements L).length := by
  unfold Kepler.Text.TameLp.nodesOfListSet
  rw [Set.InjOn.ncard_image (class_injOn L)]
  change (Kepler.Text.TameLp.elementsOfList L).ncard
      = (Kepler.Text.TameLp.listOfElements L).length
  exact ncard_elementsOfList L

/-- HOL `tame10_correspondence`（WMLNYMD.hl:107，G1 第二件）：
`tame_10 (hypermap_of_list (fgraph g)) ∧ good_list (fgraph g) ∧
 good_list_nodes (fgraph g) ∧ vertices_set2 g = elements_of_list (fgraph g) ⇒ tame10 g`。
证体：`good_list_nodes` 把 `numberOfNodes` 换成 `nodesOfListSet` 基数，
`vertices_set2 = elements_of_list` 把 `countVertices` 换成 `listOfElements` 长度，
两侧合流后喂 `tame_10` 的 13/14/15 三支。 -/
theorem tame10Correspondence {g : Kepler.Graphs.Graph} (hL : GoodList g.fgraph)
    (hgn : GoodListNodesTl g.fgraph hL)
    (hvert : Kepler.Text.TameCorrList.verticesSet2 g
      = Kepler.Text.TameLp.elementsOfList g.fgraph)
    (h10 : Kepler.Text.TameLp.Tame10 (hypermapOfList g.fgraph hL)) :
    Kepler.Graphs.tame10 g = true := by
  have hnv : (Kepler.Text.TameCorrList.verticesSet2 g).ncard = g.countVertices := by
    have hset : Kepler.Text.TameCorrList.verticesSet2 g
        = ((g.vertices).toFinset : Set ℕ) := by
      ext x
      simp [Kepler.Text.TameCorrList.verticesSet2]
    rw [hset, Set.ncard_coe_finset]
    have hnod : g.vertices.Nodup := List.nodup_range
    rw [List.toFinset_card_of_nodup (l := g.vertices) hnod]
    simp [Kepler.Graphs.Graph.vertices]
  have hcount : g.countVertices
      = (Kepler.Text.TameLp.listOfElements g.fgraph).length := by
    rw [← hnv, hvert, ncard_elementsOfList]
  have hnodes : (hypermapOfList g.fgraph hL).numberOfNodes
      = (Kepler.Text.TameLp.listOfElements g.fgraph).length := by
    show ((hypermapOfList g.fgraph hL).nodeSet).ncard = _
    rw [hgn]
    exact nodesOfListSet_ncard g.fgraph
  have hc : g.countVertices = 13 ∨ g.countVertices = 14 ∨ g.countVertices = 15 := by
    rcases h10 with h | h | h
    · left; rw [hcount, ← hnodes]; exact h
    · right; left; rw [hcount, ← hnodes]; exact h
    · right; right; rw [hcount, ← hnodes]; exact h
  rw [Kepler.Graphs.tame10]
  exact decide_eq_true (by omega)

end Kepler.Text.TameCorrNode
