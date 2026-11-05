/-
  Kepler.Text.TameCorrNodeCard — `tame_correspondence_iso` 三波施工的 **W3 第八波 a**：
  node 侧的 `dart_of` 三件（HOL `tame_list.hl:8100-:8230`）。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrG4b`（→ G4 → …，闭包零
  │ `Kepler.Assembly` 本体）。环自检：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 对照**：
  · `dart_of_node`（tame_list.hl:8199 前段）：
    `good_list L ∧ good_list_nodes L ∧ all uniq L ∧ MEM x (list_of_darts L) ∧
     FST x = v ⇒
     BIJ (λf. dart_of L f v) (set_of_list (facesAt_list L v)) (node (hypermap_of_list L) x)`
    ↦ `dartOfNode`（`all uniq L` ↦ `∀ l ∈ L, l.Nodup`）。
  · `dart_of_card_node`（tame_list.hl:8199）：
    `CARD (node (hypermap_of_list L) x) = LENGTH (facesAt_list L v)` ↦ `dartOfCardNode`。
  · `dart_of_card_face`（tame_list.hl:8083）：
    `CARD (face (hypermap_of_list L) (dart_of L f v)) = LENGTH f` ↦ `dartOfCardFace`。

  **证明路线（自证）**：
  - 本文件重落 W3-W5a 的 `list_pairs` 逐下标引擎（TameCorrNode 里是 private），
    得到「同一面表里首分量相同的 dart 唯一」：`l.Nodup` + `y ∈ list_pairs l` +
    `y.1 = v` ⇒ `y = dartOf l v`（`idxOf_getElem` + `getElem_listPairs` +
    `nextEl_eq_getD`）。
  - BIJ：maps-to 用 `memHypermapOfListNode`（node = 同 FST 类）；
    inj 用 `findFaceDarts_dartOf` 合流 + `listPairs_fst`；
    surj 用 `findFaceDarts_ex_of_self` 取面表 + 上述唯一性。
  - 卡数：BIJ ⇒ `node x = dartOf · v '' facesAt`、`InjOn.ncard_image` 归到
    `facesAtList` 的 `ncard`，再用 `uniqFacesAtList`（W3-W2）与
    `toFinset_card_of_nodup`。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrG4b

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrNodeCard

open Classical
open Kepler.Assembly (listPairs listOfDarts findFaceDarts nextEl GoodList)
open Kepler.Text (Hypermap)
open Kepler.Text.TameLp (hypermapOfList findFaceDarts_ex_of_self findFaceDarts_eq_of_mem
  dart_in_face nextEl_eq_getD getD_eq_getElem_of_lt getElem_idxOf idxOf_getElem
  la7_length_listPairs GoodListNodesTl)
open Kepler.Text.TameCorrFloor (facesAtList BIJ uniqFacesAtList)
open Kepler.Text.TameCorrNode (memHypermapOfListNode dartOf dartOf_fst
  dartOf_mem_listPairs dartOf_mem_listOfDarts findFaceDarts_dartOf)
open Kepler.Text.TameCorrCard (cardFaceOfList)
open Kepler.Text.TameCorrG4 (mem_facesAtList fst_mem_of_mem_listPairs listPairs_fst)
open Kepler.Graphs (fgraph)

/-! ## §0 `list_pairs` 逐下标引擎（本文件私有重落，供唯一性用） -/

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

/-! ## §1 唯一性：`l.Nodup` 下令 `FST = v` 的面内 dart 唯一 -/

/-- `l.Nodup` 时，面内首分量为 `v` 的 dart 就等于 `dartOf l v`。 -/
theorem dartOf_eq_of_mem_of_fst {l : List ℕ} (hl : l.Nodup) {y : ℕ × ℕ} {v : ℕ}
    (hy : y ∈ listPairs l) (hfst : y.1 = v) : y = dartOf l v := by
  have hidx : (listPairs l).idxOf y < (listPairs l).length :=
    List.idxOf_lt_length_iff.mpr hy
  have hiL : (listPairs l).idxOf y < l.length := by
    rwa [la7_length_listPairs] at hidx
  have hpos : 0 < l.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hiL
  have hyget : y = (listPairs l)[(listPairs l).idxOf y]'hidx := (getElem_idxOf hy).symm
  have hfst' : ((listPairs l)[(listPairs l).idxOf y]'hidx).1 = v := by
    rw [← hyget]
    exact hfst
  have hlv : l[(listPairs l).idxOf y]'hiL = v := by
    rw [← fst_getElem_listPairs hidx]
    exact hfst'
  have hiv : l.idxOf v = (listPairs l).idxOf y := by
    have h := idxOf_getElem hl hiL
    rwa [hlv] at h
  have hnext : nextEl l v
      = l[((listPairs l).idxOf y + 1) % l.length]'(Nat.mod_lt _ hpos) := by
    have hvmem : v ∈ l := hlv ▸ List.getElem_mem hiL
    rw [nextEl_eq_getD hvmem, hiv, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
  calc y = (listPairs l)[(listPairs l).idxOf y]'hidx := hyget
    _ = (l[(listPairs l).idxOf y]'hiL,
          l[((listPairs l).idxOf y + 1) % l.length]'(Nat.mod_lt _ hpos)) :=
        getElem_listPairs hidx
    _ = (v, nextEl l v) := by rw [hlv, ← hnext]
    _ = dartOf l v := rfl

/-! ## §2 `dart_of_node` BIJ + 两件卡数 -/

/-- HOL `dart_of_node`（tame_list.hl:8199 前段）：
`BIJ (λf. dart_of L f v) (set_of_list (facesAt_list L v)) (node (hypermap_of_list L) x)`。 -/
theorem dartOfNode {L : fgraph ℕ} (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hun : ∀ l ∈ L, l.Nodup) {x : ℕ × ℕ} (hx : x ∈ listOfDarts L) {v : ℕ}
    (hxv : x.1 = v) :
    BIJ (fun f : List ℕ => dartOf f v)
      {f : List ℕ | f ∈ facesAtList L v}
      ((hypermapOfList L hL).node x) := by
  refine ⟨?_, ?_, ?_⟩
  · -- maps-to
    intro f hf
    simp only [Set.mem_setOf_eq] at hf
    obtain ⟨hfL, hfv⟩ := mem_facesAtList.mp hf
    have hdD : dartOf f v ∈ listOfDarts L := dartOf_mem_listOfDarts hfL hfv
    have hfst : (dartOf f v).1 = v := dartOf_fst f v
    rw [memHypermapOfListNode hL hgn hx]
    exact ⟨by rw [hxv, hfst], hdD⟩
  · -- injectivity
    intro f1 hf1 f2 hf2 heq
    simp only [Set.mem_setOf_eq] at hf1 hf2
    obtain ⟨hf1L, hf1v⟩ := mem_facesAtList.mp hf1
    obtain ⟨hf2L, hf2v⟩ := mem_facesAtList.mp hf2
    have hfind1 : findFaceDarts L (dartOf f1 v) = listPairs f1 :=
      findFaceDarts_dartOf hL hf1L hf1v
    have heq' : dartOf f1 v = dartOf f2 v := heq
    have hfind2 : findFaceDarts L (dartOf f1 v) = listPairs f2 := by
      rw [heq']
      exact findFaceDarts_dartOf hL hf2L hf2v
    have hpl : listPairs f1 = listPairs f2 := by rw [← hfind1, hfind2]
    have hmap := congrArg (List.map Prod.fst) hpl
    simpa [listPairs_fst] using hmap
  · -- surjectivity
    intro y hy
    obtain ⟨hyx1, hyx2⟩ := (memHypermapOfListNode hL hgn hx).mp hy
    obtain ⟨l, hlL, _hfind, hyl⟩ :=
      findFaceDarts_ex_of_self ((dart_in_face L y).mpr hyx2)
    have hylmem : y.1 ∈ l := fst_mem_of_mem_listPairs hyl
    have hveq : v = y.1 := by rw [← hxv, hyx1]
    have hvl : v ∈ l := by
      rw [hveq]
      exact hylmem
    refine ⟨l, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      exact mem_facesAtList.mpr ⟨hlL, hvl⟩
    · have hlnd : l.Nodup := hun l hlL
      exact (dartOf_eq_of_mem_of_fst hlnd hyl (by rw [hveq])).symm

/-- HOL `dart_of_card_node`（tame_list.hl:8199）：
`CARD (node (hypermap_of_list L) x) = LENGTH (facesAt_list L v)`。 -/
theorem dartOfCardNode {L : fgraph ℕ} (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hun : ∀ l ∈ L, l.Nodup) {x : ℕ × ℕ} (hx : x ∈ listOfDarts L) {v : ℕ}
    (hxv : x.1 = v) :
    ((hypermapOfList L hL).node x).ncard = (facesAtList L v).length := by
  have hbij : BIJ (fun f : List ℕ => dartOf f v)
      {f : List ℕ | f ∈ facesAtList L v} ((hypermapOfList L hL).node x) :=
    dartOfNode hL hgn hun hx hxv
  have hT : ((hypermapOfList L hL).node x)
      = (fun f : List ℕ => dartOf f v) '' {f : List ℕ | f ∈ facesAtList L v} := by
    ext y
    constructor
    · intro hy
      obtain ⟨f, hfS, hfF⟩ := hbij.2.2 y hy
      exact ⟨f, hfS, hfF⟩
    · rintro ⟨f, hfS, hfF⟩
      rw [← hfF]
      exact hbij.1 f hfS
  have hcard : ((hypermapOfList L hL).node x).ncard
      = ({f : List ℕ | f ∈ facesAtList L v}).ncard := by
    rw [hT]
    exact Set.InjOn.ncard_image hbij.2.1
  have hnod : (facesAtList L v).Nodup := uniqFacesAtList hL v
  have hlen : ({f : List ℕ | f ∈ facesAtList L v}).ncard = (facesAtList L v).length := by
    have hset : {f : List ℕ | f ∈ facesAtList L v}
        = ((facesAtList L v).toFinset : Set (List ℕ)) := by
      ext f
      simp
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnod]
  rw [hcard, hlen]

/-- HOL `dart_of_card_face`（tame_list.hl:8083）：
`CARD (face (hypermap_of_list L) (dart_of L f v)) = LENGTH f`。 -/
theorem dartOfCardFace {L : fgraph ℕ} (hL : GoodList L) {f : List ℕ} (hf : f ∈ L)
    {v : ℕ} (hv : v ∈ f) :
    ((hypermapOfList L hL).face (dartOf f v)).ncard = f.length := by
  have hdD : dartOf f v ∈ listOfDarts L := dartOf_mem_listOfDarts hf hv
  rw [cardFaceOfList hL hdD, findFaceDarts_dartOf hL hf hv, la7_length_listPairs]

end Kepler.Text.TameCorrNodeCard
