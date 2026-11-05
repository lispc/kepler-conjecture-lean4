/-
  Kepler.Text.TameCorrCard — `tame_correspondence_iso` 三波施工的 **W3 第四波（笔 1）**：
  List_hypermap 缺口三件（HOL `formal_lp/hypermap/ssreflect/list_hypermap.vhl`）：
  · `mem_face_lemma`（:596）
  · `face_of_list`（:1063，本模块拆成两向 `faceOrbitSubset`/`faceTableSubset` + 等式件）
  · `card_face_of_list`（:1081）

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrList`（→ TameCorrFloor → TameLp +
  │ Graphs，闭包零 `Kepler.Assembly` 本体）。
  │ 环自检：`#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │ 必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **证明路线（自证，未复制岛文件证体）**：
  `face (hypermapOfList L hL) d = orbitMap faceMap d`。方向 ⊆ 用
  `findFaceDarts_congr_of_mem` + `nextEl_mem_of_mem` 对幂次归纳；方向 ⊇ 把
  `faceMap` 在面表上逐步等同于 `next_el`，用 `nextEl` 的 mod-下标迭代公式
  `(next_el s)^[n] s[j] = s[(j+n) % len]` 在 `(j + len - i) % len` 步走到
  目标下标。最后 `card = length` 由 `toFinset_card_of_nodup`（面表 Nodup）给出。
  `mem_face_lemma` 走 `L.map listPairs` 的成员分解 + `findFaceDarts_eq_of_mem`
  （TameLp 已有，HOL 的 `HD f`/`uniq_face_unique` 路线在 Lean 侧更短）。

  **载体注记**：`find_face L d` ↦ `findFaceDarts L d`（dart 列表，非顶点列表）；
  `set_of_list` ↦ `{y | y ∈ _}`；`CARD` ↦ `Set.ncard`；`sizel` ↦ `List.length`。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrList

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrCard

open Classical
open Kepler.Assembly (listPairs listOfDarts findFaceDarts fList nextEl GoodList)
open Kepler.Text (Hypermap orbitMap)
open Kepler.Text.TameLp (hypermapOfList faceMap_hypermapOfList dart_in_face
  findFaceDarts_eq_of_mem findFaceDarts_congr_of_mem findFaceDarts_nodup
  mem_darts_of_mem_findFace nextEl_eq_getD nextEl_mem_of_mem
  getD_eq_getElem_of_lt getElem_idxOf idxOf_getElem la7_length_listPairs)
open Kepler.Graphs (fgraph)

/-! ## §1 列表/`next_el` 算术引擎（自证） -/

/-- 同表两下标相等则取元相等（proof-irrelevant `getElem` 换形器）。 -/
private theorem getElem_congr_idx {α : Type*} {l : List α} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (h : i = j) :
    l[i]'hi = l[j]'hj := by
  subst h
  rfl

/-- `list_pairs` 非空（HOL `list_pairs_empty` 的逆否形）。 -/
private theorem listPairs_ne_nil {α : Type*} {l : List α} (h : l ≠ []) :
    listPairs l ≠ [] := by
  intro hc
  have hlen : (listPairs l).length = l.length := la7_length_listPairs l
  rw [hc] at hlen
  have h0 : l.length = 0 := by simpa using hlen.symm
  exact h (List.length_eq_zero_iff.mp h0)

/-- nodup 表上 `next_el` 的一步：第 `j` 项走到第 `(j+1) mod len` 项。 -/
private theorem nextEl_step {s : List (ℕ × ℕ)} (hs : s.Nodup) {j : ℕ}
    (hj : j < s.length) (hj1 : (j + 1) % s.length < s.length) :
    nextEl s (s[j]'hj) = s[(j + 1) % s.length]'hj1 := by
  have hmem : s[j]'hj ∈ s := List.getElem_mem hj
  rw [nextEl_eq_getD hmem, idxOf_getElem hs hj, getD_eq_getElem_of_lt hj1]

/-- nodup 表上 `next_el` 的 `n` 步幂：下标按 `(j+n) mod len` 前进。 -/
private theorem nextEl_iterate {s : List (ℕ × ℕ)} (hs : s.Nodup) {j : ℕ}
    (hj : j < s.length) (n : ℕ) (hjn : (j + n) % s.length < s.length) :
    (nextEl s)^[n] (s[j]'hj) = s[(j + n) % s.length]'hjn := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact getElem_congr_idx hj hjn (by rw [Nat.add_zero, Nat.mod_eq_of_lt hj])
  | succ k ih =>
    have hjk : (j + k) % s.length < s.length := Nat.mod_lt _ hpos
    have hstep := nextEl_step hs hjk (Nat.mod_lt ((j + k) % s.length + 1) hpos)
    rw [Function.iterate_succ_apply', ih hjk, hstep]
    refine getElem_congr_idx (Nat.mod_lt _ hpos) hjn ?_
    rw [Nat.mod_add_mod, Nat.add_assoc]

/-- `next_el` 幂的 `idxOf` 起点形（避免在主证明里替换 `d` 时波及
`findFaceDarts L d` 内部；`conv_lhs` 只改轨道起点）。 -/
private theorem nextEl_iterate_idxOf {s : List (ℕ × ℕ)} (hs : s.Nodup) {x : ℕ × ℕ}
    (hx : x ∈ s) (n : ℕ) (h : (s.idxOf x + n) % s.length < s.length) :
    (nextEl s)^[n] x = s[(s.idxOf x + n) % s.length]'h := by
  have hxmem : x = s[s.idxOf x]'(List.idxOf_lt_length_iff.mpr hx) :=
    (getElem_idxOf hx).symm
  conv_lhs => rw [hxmem]
  exact nextEl_iterate hs (List.idxOf_lt_length_iff.mpr hx) n h

/-- `next_el` 的迭代不离开表。 -/
private theorem nextEl_iterate_mem {s : List (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ s) :
    ∀ n : ℕ, (nextEl s)^[n] x ∈ s := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-! ## §2 `face_of_list`（HOL :1063） -/

/-- `face_of_list` 的 ⊆ 半向：面轨道 ⊆ `find_face L d` 的 dart 集合。 -/
theorem faceOrbitSubset {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    (hypermapOfList L hL).face d ⊆ {y | y ∈ findFaceDarts L d} := by
  have hdd : d ∈ findFaceDarts L d := (dart_in_face L d).mpr hd
  have key : ∀ n : ℕ, ((hypermapOfList L hL).faceMap ^ n) d ∈ findFaceDarts L d := by
    intro n
    induction n with
    | zero => simpa using hdd
    | succ k ih =>
      have hzD : ((hypermapOfList L hL).faceMap ^ k) d ∈ (hypermapOfList L hL).darts :=
        (hypermapOfList L hL).faceMap_permutes.pow_apply_mem k
          (List.mem_toFinset.mpr hd)
      have hcongr : findFaceDarts L (((hypermapOfList L hL).faceMap ^ k) d)
          = findFaceDarts L d := findFaceDarts_congr_of_mem hL.1 hd ih
      rw [pow_succ', Equiv.Perm.mul_apply, faceMap_hypermapOfList L hL hzD]
      show nextEl (findFaceDarts L (((hypermapOfList L hL).faceMap ^ k) d))
        (((hypermapOfList L hL).faceMap ^ k) d) ∈ findFaceDarts L d
      rw [hcongr]
      exact nextEl_mem_of_mem ih
  intro y hy
  simp only [Hypermap.face, orbitMap, Set.mem_setOf_eq] at hy
  obtain ⟨n, hn⟩ := hy
  rw [← hn]
  exact key n

/-- `face_of_list` 的 ⊇ 半向：`find_face L d` 的每个 dart 都在面轨道上。 -/
theorem faceTableSubset {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    {y | y ∈ findFaceDarts L d} ⊆ (hypermapOfList L hL).face d := by
  have hdd : d ∈ findFaceDarts L d := (dart_in_face L d).mpr hd
  have hnod : (findFaceDarts L d).Nodup := findFaceDarts_nodup hL.1 d
  have hpos : 0 < (findFaceDarts L d).length := List.length_pos_of_mem hdd
  -- 面表上的 `faceMap` 就是 `next_el`
  have hfaceTbl : ∀ z ∈ findFaceDarts L d,
      (hypermapOfList L hL).faceMap z = nextEl (findFaceDarts L d) z := by
    intro z hz
    have hzD : z ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr (mem_darts_of_mem_findFace L hz)
    rw [faceMap_hypermapOfList L hL hzD]
    show nextEl (findFaceDarts L z) z = nextEl (findFaceDarts L d) z
    rw [findFaceDarts_congr_of_mem hL.1 hd hz]
  -- `faceMap` 幂 = `next_el` 幂
  have hpow : ∀ n : ℕ, ((hypermapOfList L hL).faceMap ^ n) d
      = (nextEl (findFaceDarts L d))^[n] d := by
    intro n
    induction n with
    | zero => rw [pow_zero, Function.iterate_zero]; rfl
    | succ k ih =>
      have hmem := nextEl_iterate_mem hdd k
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hfaceTbl _ hmem,
        Function.iterate_succ_apply']
  rintro y hy
  simp only [Hypermap.face, orbitMap, Set.mem_setOf_eq]
  have hidd : (findFaceDarts L d).idxOf d < (findFaceDarts L d).length :=
    List.idxOf_lt_length_iff.mpr hdd
  have hidy : (findFaceDarts L d).idxOf y < (findFaceDarts L d).length :=
    List.idxOf_lt_length_iff.mpr hy
  refine ⟨((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
    - (findFaceDarts L d).idxOf d) % (findFaceDarts L d).length, ?_⟩
  rw [hpow]
  rw [nextEl_iterate_idxOf hnod hdd
    (((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
      - (findFaceDarts L d).idxOf d) % (findFaceDarts L d).length)
    (Nat.mod_lt _ hpos)]
  refine (getElem_congr_idx (Nat.mod_lt _ hpos) hidy ?_).trans (getElem_idxOf hy)
  have h1 : ((findFaceDarts L d).idxOf d
      + (((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
        - (findFaceDarts L d).idxOf d) % (findFaceDarts L d).length))
      % (findFaceDarts L d).length
      = ((((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
        - (findFaceDarts L d).idxOf d)) + (findFaceDarts L d).idxOf d)
        % (findFaceDarts L d).length := by
    rw [Nat.add_comm ((findFaceDarts L d).idxOf d)]
    exact Nat.mod_add_mod _ _ _
  have h2 : ((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
      - (findFaceDarts L d).idxOf d) + (findFaceDarts L d).idxOf d
      = (findFaceDarts L d).idxOf y + (findFaceDarts L d).length := by
    omega
  rw [h1, h2, Nat.add_mod_right, Nat.mod_eq_of_lt hidy]

/-- HOL `face_of_list`（list_hypermap.vhl:1063）：
`good_list L ∧ MEM d (list_of_darts L) ⇒ face (hypermap_of_list L) d
= set_of_list (find_face L d)`。 -/
theorem faceOfList {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    (hypermapOfList L hL).face d = {y | y ∈ findFaceDarts L d} :=
  Set.Subset.antisymm (faceOrbitSubset hL hd) (faceTableSubset hL hd)

/-- HOL `mem_face_lemma`（list_hypermap.vhl:596）：
`good_list L ∧ MEM f (list_of_faces L) ⇒ ∃d. MEM d (list_of_darts L) ∧ f = find_face L d`。 -/
theorem memFaceLemma {L : fgraph ℕ} (hL : GoodList L) {f : List (ℕ × ℕ)}
    (hf : f ∈ L.map listPairs) :
    ∃ d : ℕ × ℕ, d ∈ listOfDarts L ∧ f = findFaceDarts L d := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hf
  have hlne : l ≠ [] := hL.2.1 l hl
  have hplne : listPairs l ≠ [] := listPairs_ne_nil hlne
  refine ⟨(listPairs l).head hplne, ?_, ?_⟩
  · exact List.mem_flatten.mpr ⟨listPairs l, List.mem_map.mpr ⟨l, hl, rfl⟩,
      List.head_mem hplne⟩
  · exact (findFaceDarts_eq_of_mem hL.1 hl (List.head_mem hplne)).symm

/-- HOL `card_face_of_list`（list_hypermap.vhl:1081）：
`good_list L ∧ MEM d (list_of_darts L) ⇒ CARD (face (hypermap_of_list L) d)
= sizel (find_face L d)`。 -/
theorem cardFaceOfList {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    ((hypermapOfList L hL).face d).ncard = (findFaceDarts L d).length := by
  rw [faceOfList hL hd]
  have hset : {y : ℕ × ℕ | y ∈ findFaceDarts L d}
      = ((findFaceDarts L d).toFinset : Set (ℕ × ℕ)) := by
    ext y
    simp
  rw [hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (findFaceDarts_nodup hL.1 d)]


/-! ## §4 顺带：G1 第一件（HOL WMLNYMD.hl:42） -/

/-- HOL `tame9a_correspondence`（WMLNYMD.hl:42，G1 第一件；本波顺带关闭）：
`tame_9a (hypermap_of_list (fgraph g)) ∧ good_list (fgraph g) ⇒ tame9a g`。
证体：每个图面 `f` 取 `listPairs f.vertices` 的首 dart `d`，`cardFaceOfList`
给 `CARD (face d) = sizel (find_face d) = sizel (listPairs f.vertices) =
LENGTH f.vertices`，再消费 `tame_9a`。 -/
theorem tame9aCorrespondence {g : Kepler.Graphs.Graph} (hL : GoodList g.fgraph)
    (h9 : Kepler.Text.TameLp.Tame9a (hypermapOfList g.fgraph hL)) :
    Kepler.Graphs.tame9a g = true := by
  rw [Kepler.Graphs.tame9a, List.all_eq_true]
  intro f hf
  have hl : f.vertices ∈ g.fgraph := List.mem_map.mpr ⟨f, hf, rfl⟩
  have hlne : f.vertices ≠ [] := hL.2.1 f.vertices hl
  have hplne : listPairs f.vertices ≠ [] := listPairs_ne_nil hlne
  have hdmem : (listPairs f.vertices).head hplne ∈ listPairs f.vertices :=
    List.head_mem hplne
  have hdD : (listPairs f.vertices).head hplne ∈ listOfDarts g.fgraph :=
    List.mem_flatten.mpr ⟨listPairs f.vertices,
      List.mem_map.mpr ⟨f.vertices, hl, rfl⟩, hdmem⟩
  have hdH : (listPairs f.vertices).head hplne
      ∈ (hypermapOfList g.fgraph hL).darts := List.mem_toFinset.mpr hdD
  have hcard := h9 _ hdH
  have hface : ((hypermapOfList g.fgraph hL).face
        ((listPairs f.vertices).head hplne)).ncard
      = (listPairs f.vertices).length := by
    rw [cardFaceOfList hL hdD, findFaceDarts_eq_of_mem hL.1 hl hdmem]
  have hlen : (listPairs f.vertices).length = f.vertices.length :=
    la7_length_listPairs _
  rw [hface, hlen] at hcard
  exact decide_eq_true hcard

end Kepler.Text.TameCorrCard
