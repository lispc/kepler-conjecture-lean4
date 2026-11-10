/-
  Kepler.Text.Reduction1W2e — J4 Wave W2 批 2（W2_SPLIT_FROZEN 的 W2-2 簇
  前 4 件 + 1 基座）：`rotate_to_map`（HOL reduction1.hl:1973）、
  `pair_fst_inj`（simple_list 的内核基座）、`simple_list`（:1895）、
  `newvertex_uniq`（:1947）、`set_of_list_newvertex`（:1782）。

  路线：
  · `rotateToMap` 走批 1d `rotateToEqRotate`（HOL `rotate_rot_indexl`）
    + `List.map_rotate`；`idxOf` 过 `map` 用 Nodup 下标单射定位
    （HOL `indexl_map` + `map_inj_in_uniq` 的 Lean 形）。
  · `pairFstInj`：`list_pairs` zip 形（批 1d `listPairsEqZip`）+ Nodup
    下标单射；HOL `simple_list` 内核（good_face_rep + dart_of_unique 两步
    合并为「首元相同则对相同」）。
  · `simpleList`：`find_face` 逐字（`findFaceDarts`）+ `pairFstInj`；
    HOL 的 `good_list`/`good_list_nodes` 前提在本形由
    `(listOfDarts L).Nodup`（= GoodList 首合取）与 `all uniq L` 吸收。
  · `newvertexUniq`：`uniq_map`+`filter_uniq`+`rot_uniq` 的 Lean 形
    （Nodup 的 pairwise 形 + `Nodup.filter` + `nodup_rotate`），
    注入性槽 = `simpleList`。
  · `setOfListNewvertex`：EXTENSION 展开 + `mem_rotate_to2` 换装。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W2d
import Kepler.Text.TameLp
import Kepler.Text.PackingAuto2

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts listPairs findFaceDarts)
open Kepler.Text.Reduction3 (newvertex)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face)
open Kepler.Text.TameSpine (rotateTo)

/-! ## §0 `map` 下的 Nodup（pairwise 注入形）-/

/-- `∀ a b ∈ l, f a = f b → a = b` ⇒ `map f l` Nodup（HOL `uniq_map` 的
pairwise 槽形；core 的 `Nodup.map` 只收全局单射，不合用）。 -/
private theorem nodupMapOn {α β : Type} {f : α → β} {l : List α}
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) (hl : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hl
    refine List.nodup_cons.mpr ⟨?_, ih (fun x hx y hy heq =>
      hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) heq) htail⟩
    rw [List.mem_map]
    rintro ⟨b, hb, hEq⟩
    have hb' : b ∈ a :: t := List.mem_cons_of_mem _ hb
    have hba : b = a := hf b hb' a List.mem_cons_self hEq
    exact hhead (by rw [← hba]; exact hb)

/-! ## §1 `rotate_to_map`（HOL reduction1.hl:1973） -/

/-- **HOL `rotate_to_map`**：`uniq f ∧ MEM x f ∧ inj_on phi (set_of_list f) ⇒
rotate_to (MAP phi f) (phi x) = MAP phi (rotate_to f x)`。 -/
theorem rotateToMap {α : Type} [BEq α] [LawfulBEq α] {f : List α} {x : α}
    {phi : α → α} (hnd : f.Nodup) (hx : x ∈ f)
    (hinj : Set.InjOn phi (Kepler.Text.setOfList f)) :
    rotateTo (f.map phi) (phi x) = (rotateTo f x).map phi := by
  have hndMap : (f.map phi).Nodup := nodupMapOn
    (fun a ha b hb heq => hinj ha hb heq) hnd
  have hi : f.idxOf x < f.length := List.idxOf_lt_length_iff.mpr hx
  have hiM : f.idxOf x < (f.map phi).length := by rw [List.length_map]; exact hi
  have hget : (f.map phi)[f.idxOf x]'hiM = phi x := by
    rw [List.getElem_map, List.getElem_idxOf hi]
  have hidxEq : (f.map phi).idxOf (phi x) = f.idxOf x := by
    have he := hndMap.idxOf_getElem (f.idxOf x) hiM
    rw [hget] at he
    exact he
  rw [rotateToEqRotate (List.mem_map.mpr ⟨x, hx, rfl⟩) hndMap, hidxEq,
    ← List.map_rotate, rotateToEqRotate hx hnd]

/-! ## §2 `pair_fst_inj`（`simple_list` 内核基座） -/

/-- Nodup 列表的 `list_pairs` 对由首元唯一决定（HOL `simple_list` 的
good_face_rep + dart_of_unique 两步合并形）。 -/
theorem pairFstInj {l : List Nat} (hnd : l.Nodup) {p q : Nat × Nat}
    (hp : p ∈ listPairs l) (hq : q ∈ listPairs l) (h : p.1 = q.1) : p = q := by
  obtain ⟨i, hi, hpe⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨j, hj, hqe⟩ := List.mem_iff_getElem.mp hq
  subst hpe
  subst hqe
  have hLL : (listPairs l).length = l.length := by
    rw [listPairsEqZip, List.length_zipWith, List.length_rotate]
    simp
  have hi' : i < l.length := by rw [hLL] at hi; exact hi
  have hj' : j < l.length := by rw [hLL] at hj; exact hj
  have hmodI : (i + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
  have hmodJ : (j + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
  -- `?`-形定位（避开依赖式下标重写）
  have hAt : ∀ (k : Nat) (hk : k < l.length) (hm : (k + 1) % l.length < l.length),
      (listPairs l)[k]? = some (l[k]'hk, l[(k + 1) % l.length]'hm) := by
    intro k hk hm
    rw [listPairsEqZip, List.getElem?_zipWith_eq_some]
    refine ⟨_, _, List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩, ?_, rfl⟩
    rw [List.getElem?_eq_some_iff]
    exact ⟨by rw [List.length_rotate]; exact hk, List.getElem_rotate l 1 k _⟩
  obtain ⟨_, hpiE⟩ := List.getElem?_eq_some_iff.mp (hAt i hi' hmodI)
  obtain ⟨_, hpjE⟩ := List.getElem?_eq_some_iff.mp (hAt j hj' hmodJ)
  rw [hpiE, hpjE] at h
  have hfirst : l[i]'hi' = l[j]'hj' := h
  have hij : i = j := by
    have e1 := hnd.idxOf_getElem i hi'
    have e2 := hnd.idxOf_getElem j hj'
    rw [hfirst] at e1
    exact e1.symm.trans e2
  rw [hpiE, hpjE]
  subst hij
  rfl

/-! ## §3 `simple_list`（HOL reduction1.hl:1895） -/

/-- **HOL `simple_list`**：`MEM x (list_of_darts L) ∧ MEM u (find_face L x) ∧
MEM v (find_face L x) ∧ FST u = FST v ∧ all uniq L ⇒ u = v`。
（HOL 的 `good_list`/`good_list_nodes` 两前提由本形的 `(listOfDarts L).Nodup`
= `GoodList` 首合取与 `all uniq L` 吸收：`find_face` 元是 `L` 某面
`list_pairs` 的对，首元单射性只消费面自身 Nodup。） -/
theorem simpleList {L : Kepler.Graphs.fgraph ℕ} {u v x : Kepler.Text.Reduction5.Dart}
    (hx : x ∈ listOfDarts L) (hu : u ∈ findFaceDarts L x)
    (hv : v ∈ findFaceDarts L x) (huv : u.1 = v.1)
    (hall : ∀ l ∈ L, l.Nodup) : u = v := by
  by_cases hval : L.find? (fun l => decide (x ∈ listPairs l)) = none
  · rw [Kepler.Text.TameLp.findFaceDarts_none hval] at hu
    exact absurd hu (by simp)
  · obtain ⟨l0, hl0⟩ := Option.ne_none_iff_exists.mp hval
    have hmem0 : l0 ∈ L := List.mem_of_find?_eq_some hl0.symm
    have hfeq : findFaceDarts L x = listPairs l0 := by
      simp only [findFaceDarts, ← hl0, Option.getD_some]
    rw [hfeq] at hu hv
    exact pairFstInj (hall l0 hmem0) hu hv huv

/-! ## §4 `newvertex_uniq`（HOL reduction1.hl:1947） -/

/-- **HOL `newvertex_uniq`**：`MEM x (list_of_darts L) ∧ good_list L ∧
good_list_nodes L ∧ all uniq L ⇒ uniq (newvertex L r x)`。 -/
theorem newvertexUniq {L : Kepler.Graphs.fgraph ℕ} {r : List Kepler.Text.Reduction5.Dart}
    {x : Kepler.Text.Reduction5.Dart}
    (hx : x ∈ listOfDarts L) (hgood : GoodList L)
    (hgn : GoodListNodesTl L hgood) (hall : ∀ l ∈ L, l.Nodup) :
    (newvertex L r x).Nodup := by
  have hnd : (findFaceDarts L x).Nodup := Kepler.Text.TameLp.findFaceDarts_nodup hgood.1 x
  have hvx : x ∈ findFaceDarts L x := dart_in_face L x |>.mpr hx
  have hrot : (rotateTo (findFaceDarts L x) x).Nodup := by
    rw [rotateToEqRotate hvx hnd]
    exact List.nodup_rotate.mpr hnd
  show (((Kepler.Text.Reduction3.rotateTo (findFaceDarts L x) x).filter
      (fun d => decide (d ∉ r))).map (fun d => d.1)).Nodup
  rw [rotateToBridge]
  refine nodupMapOn ?_ (hrot.filter (fun d => decide (d ∉ r)))
  intro a ha b hb hEq
  have ha' : a ∈ rotateTo (findFaceDarts L x) x := (List.mem_filter.mp ha).1
  have hb' : b ∈ rotateTo (findFaceDarts L x) x := (List.mem_filter.mp hb).1
  exact simpleList hx ((memRotateTo2 hvx hnd).mpr ha')
    ((memRotateTo2 hvx hnd).mpr hb') hEq hall

/-! ## §5 `set_of_list_newvertex`（HOL reduction1.hl:1782） -/

/-- **HOL `set_of_list_newvertex`**：`good_list L ∧ MEM x (list_of_darts L) ⇒
set_of_list (newvertex L r x) =
IMAGE FST {t | MEM t (find_face L x) ∧ ~MEM t r}`。 -/
theorem setOfListNewvertex {L : Kepler.Graphs.fgraph ℕ}
    {r : List Kepler.Text.Reduction5.Dart} {x : Kepler.Text.Reduction5.Dart}
    (hgood : GoodList L) (hx : x ∈ listOfDarts L) :
    Kepler.Text.setOfList (newvertex L r x) =
      Set.image (fun d : Kepler.Text.Reduction5.Dart => d.1)
        {t | t ∈ findFaceDarts L x ∧ t ∉ r} := by
  have hnd : (findFaceDarts L x).Nodup := Kepler.Text.TameLp.findFaceDarts_nodup hgood.1 x
  have hvx : x ∈ findFaceDarts L x := dart_in_face L x |>.mpr hx
  have hnv : ∀ t : ℕ,
      t ∈ newvertex L r x ↔
        t ∈ List.map (fun d : Kepler.Text.Reduction5.Dart => d.1)
          (List.filter (fun d => decide (d ∉ r))
            (Kepler.Text.Reduction3.rotateTo (findFaceDarts L x) x)) := fun _ => Iff.rfl
  ext d
  simp only [setOfList, Set.mem_image, Set.mem_setOf, hnv]
  constructor
  · intro h
    obtain ⟨s, hs, hEq⟩ := List.mem_map.mp h
    obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
    exact ⟨s, ⟨(memRotateTo2 hvx hnd).mpr hs1, by simpa using hs2⟩, hEq⟩
  · rintro ⟨s, ⟨hs1, hs2⟩, hEq⟩
    exact List.mem_map.mpr ⟨s, List.mem_filter.mpr
      ⟨(memRotateTo2 hvx hnd).mp hs1, by simpa using hs2⟩, hEq⟩

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.nodupMapOn
#print axioms Kepler.Text.Reduction1.rotateToMap
#print axioms Kepler.Text.Reduction1.pairFstInj
#print axioms Kepler.Text.Reduction1.simpleList
#print axioms Kepler.Text.Reduction1.newvertexUniq
#print axioms Kepler.Text.Reduction1.setOfListNewvertex
