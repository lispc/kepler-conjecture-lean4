/-
  Kepler.Text.MoreLemma2ChainUniqB — more_lemma2 岛 `simple_hypermap` 机器片 §2：
  face/node 轨道两件（链层重落）+ node 轨道件借用。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）──
  │ tame_list.hl:4399  `MEM_hypermap_of_list_node` → **借 `Kepler.Text.TameCorrNode:228`**
  │                     `memHypermapOfListNode`（public，闭包 168 模块 / 零 Spine）
  │ （f_list_ext_orbit ⊆ 半向）→ faceOrbitSubsetFindFace（public）
  │ （face 轨道 ⊇ 面表）        → faceTableSubsetFaceOrbit（public）
  │ 私有支撑（Spine 私件链层重落）：`getElemCon` / `nextElIterateMem` /
  │   `nextElIterateGetElem`（后者改走 `nextEl_eq_getD` 自证，免 Spine 的 `nextElStep`）
  └────────────────────────────────────────────────────────────────

  **说明**：TameList14:142 / TameList7:278 的对应件是 `private`（不可跨模块），
  故按路线 A 链层重落并**公开**（§3 要用）。本文件零 Spine import；
  唯一的非 Graphs/Text 基础依赖是 `Kepler.Text.TameCorrNode`（已核闭包零 Spine）。

  **纪律**：零 axiom/sorry/admit/native_decide。
-/

import Kepler.Text.TameCorrNode

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2ChainUniqB

open Kepler.Graphs (fgraph)
open Kepler.Assembly (listOfDarts findFaceDarts nextEl GoodList)
open Kepler.Text.TameLp (dart_in_face mem_darts_of_mem_findFace findFaceDarts_congr_of_mem
  findFaceDarts_nodup getElem_idxOf idxOf_getElem faceMap_hypermapOfList nextEl_mem_of_mem
  nextEl_eq_getD getD_eq_getElem_of_lt hypermapOfList)

/-! ## §0 私有小件 -/

/-- 同长双下标的取值一致性（proof-irrelevance 的显式形）。 -/
theorem getElemCon {α : Type*} {l : List α} {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a = b) : l[a]'ha = l[b]'hb := by
  subst hab
  rfl

/-- `next_el` 在无重表上的单步取值式：`nextEl s (s[j]) = s[(j+1) % sizel s]`。
本树自证（Spine 走私有 `nextElStep`；这里用 `nextEl_eq_getD` + `idxOf_getElem`）。 -/
theorem nextElGetElemSucc {s : List (ℕ × ℕ)} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (hj1 : (j + 1) % s.length < s.length) :
    nextEl s (s[j]'hj) = s[(j + 1) % s.length]'hj1 := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  have hmem : s[j]'hj ∈ s := List.getElem_mem hj
  rw [nextEl_eq_getD hmem, idxOf_getElem hsn hj, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]

/-- 轨道不离开表：`x ∈ s ⇒ (nextEl s)^[n] x ∈ s`。 -/
theorem nextElIterateMem {s : List (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ s) :
    ∀ n : ℕ, (nextEl s)^[n] x ∈ s := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-- 迭代取值式：`(nextEl s)^[n] (s[j]) = s[(j+n) % sizel s]`（`s` 无重）。 -/
theorem nextElIterateGetElem {s : List (ℕ × ℕ)} (hsn : s.Nodup) {j : ℕ}
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
      nextElGetElemSucc hsn hjk (Nat.mod_lt ((j + k) % s.length + 1) hpos)]
    refine getElemCon (Nat.mod_lt _ hpos) hjn ?_
    have hmod : ((j + k) % s.length + 1) % s.length = (j + k + 1) % s.length :=
      Nat.mod_add_mod (j + k) s.length 1
    rw [hmod, Nat.add_assoc]

/-! ## §1 `faceOrbitSubsetFindFace`（face 轨道 ⊆ 面表） -/

/-- **HOL `f_list_ext_orbit` 的 ⊆ 半向**（Spine 现名 `faceOrbitSubsetFindFace`，
TameList7:278 private）：`face` 轨道每点都落在 `findFaceDarts L d` 内。

证体：对幂次归纳——`faceMap` 在面表上逐点 = `nextEl 面表`（`faceMap_hypermapOfList`
+ `findFaceDarts_congr_of_mem`），`nextEl` 保面表成员（`nextEl_mem_of_mem`）。 -/
theorem faceOrbitSubsetFindFace {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
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

/-! ## §2 `faceTableSubsetFaceOrbit`（face 轨道 ⊇ 面表） -/

/-- **HOL `simple_hypermap` 机器的 ⊇ 半向**（Spine 现名 `faceTableSubsetFaceOrbit`，
TameList14:142 private）：`findFaceDarts L d` 整表落在 `face` 轨道内
（轨道从 `d` 走 `(idx y - idx d) mod len` 步即到 `y`）。

证体：把 `faceMap` 的幂换成 `nextEl` 面表的迭代（`nextElIterateMem` 保成员），
再用 `nextElIterateGetElem` 定位任意表成员。 -/
theorem faceTableSubsetFaceOrbit {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
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
  -- 幂与迭代交换
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

end Kepler.Text.MoreLemma2ChainUniqB

/-! 借用件可达性锚（import `TameCorrNode` 的实效核验；本件不重落） -/
#check @Kepler.Text.TameCorrNode.memHypermapOfListNode

/-! 公理审计锚（本文件编译即执行；预期 ≤ 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2ChainUniqB.faceOrbitSubsetFindFace
#print axioms Kepler.Text.MoreLemma2ChainUniqB.faceTableSubsetFaceOrbit
