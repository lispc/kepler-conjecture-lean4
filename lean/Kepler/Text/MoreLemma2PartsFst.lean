/-
  Kepler.Text.MoreLemma2PartsFst — J 战役 J1（M0h 件 2）：
  `parts_fst`（tame_list.hl:6687）链岛重落。

  ┌─ 归属对账 ─────────────────────────────────────────────────────
  │ 公开件：
  │   tame_list.hl:6687 `parts_fst` → partsFst
  │     （normal_list L N ∧ good_list L ∧ MEM r N ∧ MEM p (parts L r) ∧
  │      MEM x p ==> FST x = FST (HD p)）
  │   链上机器（HOL 锚）：
  │   tame_list.hl:6607 `parts_node_inverse_power` → partsNodeInversePower
  │   tame_list.hl:6860? `parts_in_node`（Spine partsInNode）→ partsInNode
  │   tame_list.hl:6722 `parts_darts` → partsDarts
  │   hypermap.hl `fst_n_list_ext_power`（symm 版）→ fstInvOrbit
  │   unlast 分量（Spine `partsNextUnlast`，tame_list.hl parts_next_last
  │     内蕴）→ partsNextUnlast
  └────────────────────────────────────────────────────────────────

  ┌─ 实现路线（比 Spine 省 partsInductLemma 机）──────────────────
  │ Spine 的 partsNextUnlast/partsNodeInversePower 走 sizeInduct +
  │ partsPure/partsCat/partsCases（TameList9 的 ≈250 行机）。本片改用
  │ **atom 内相邻链不变量**：partitionIntoAtom0 每次前插都满足
  │ `n new = a0.headD`（join 条件），故 atom 内相邻 `d1,d2` 恒有
  │ `d2 = n d1`——私有归纳谓词 `AtomChain` 维护平凡，提取得
  │ partsNextUnlast（本片 §2）。
  │ 其余分量直接复用已落库件：`inverseNodeMapList`（片 3）、
  │ `fListFstSnd`（片 3，经私有 no-uniq 版本 fListFstOfDarts——
  │ 本片重落 listPairs 半机器）、`nodeMap_symm_pow_mem_node_self` /
  │ `exists_pow_nodeMap_symm_apply_of_mem_node`（Hypermap）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；Dart/ℕ 具体载体；
  import 闭包零 TameSpine、零 Assembly 主模块。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.ChainListsL1
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2PartsFst

open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart parts partitionIntoAtom partitionIntoAtom0)
open Kepler.Text.ChainLists (normalList)
open Kepler.Text.MoreLemma2Island2 (partsFlatten partsAllNonnil)
open Kepler.Text.MoreLemma2Island3 (partsUniqNonnil inverseNodeMapList)
open Kepler.Assembly (fList eList listOfDarts listPairs findFaceDarts nextEl GoodList)
open Kepler.Text.TameLp (hypermapOfList dart_in_face findFaceDarts_ex_of_self
  la7_length_listPairs getElem_idxOf idxOf_getElem getD_eq_getElem_of_lt nextEl_eq_getD)

variable {n : Dart → Dart}

/-! ## §1 小件（getElem 运输 / 末元 machinery / listPairs FST 半边） -/

/-- 下标相等时的 getElem 运输（证明无关）。 -/
private theorem getElemCon {α : Type*} {l : List α} {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a = b) :
    l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- `list_pairs` 的逐项式（Spine listPairsGetElem TameList10:217 链岛重落）：
`(list_pairs s)[j] = (s[j], s[(j+1) % sizel s])`。 -/
private theorem listPairsGetElem {s : List ℕ} {j : ℕ} (hj : j < s.length) :
    (listPairs s)[j]'(Nat.lt_of_lt_of_eq hj (la7_length_listPairs s).symm)
      = (s[j]'hj,
        s[(j + 1) % s.length]'(Nat.mod_lt (j + 1)
          (Nat.lt_of_le_of_lt (Nat.zero_le j) hj))) := by
  have hlen : (listPairs s).length = s.length := la7_length_listPairs s
  have hpos : 0 < s.length := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  have hlenDr : (s.drop 1).length = s.length - 1 := List.length_drop
  have hlenTk : (List.take 1 s).length = min 1 s.length := List.length_take
  have htot : j < ((s.drop 1) ++ List.take 1 s).length := by
    rw [List.length_append, hlenDr, hlenTk]; omega
  show (s.zip (s.drop 1 ++ List.take 1 s))[j]'(Nat.lt_of_lt_of_eq hj (la7_length_listPairs s).symm) = _
  rw [List.getElem_zip]
  by_cases hj1 : j + 1 < s.length
  · have hrot : ((s.drop 1) ++ List.take 1 s)[j] = (s.drop 1)[j] :=
      List.getElem_append_left (by rw [hlenDr]; omega) (h' := htot)
    have hdr : (s.drop 1)[j] = s[1 + j] :=
      List.getElem_drop (h := by rw [hlenDr]; omega)
    rw [hrot, hdr]
    exact congrArg (Prod.mk s[j]) (getElemCon (by omega) (Nat.mod_lt (j + 1) hpos)
      (by rw [Nat.mod_eq_of_lt hj1]; omega))
  · have jlen : j + 1 = s.length := by omega
    have hrot : ((s.drop 1) ++ List.take 1 s)[j]
        = (List.take 1 s)[j - (s.drop 1).length] :=
      List.getElem_append_right (by rw [hlenDr]; omega) (h₂ := htot)
    have h0 : j - (s.drop 1).length = 0 := by rw [hlenDr]; omega
    have htak : (List.take 1 s)[j - (s.drop 1).length] = s[0] :=
      (getElemCon (by rw [hlenTk]; omega) (by rw [hlenTk]; omega) h0).trans
        (List.getElem_take (h := by rw [hlenTk]; omega))
    rw [hrot, htak]
    exact congrArg (Prod.mk s[j]) (getElemCon hpos (Nat.mod_lt (j + 1) hpos)
      (by rw [jlen, Nat.mod_self]))

/-- **HOL `next_el_list_pairs` 的 FST 半边**（list_hypermap-compiled.hl:316；
Spine nextElListPairsFst TameList10:274）：
`MEM (x,y) (list_pairs s) ⟹ FST (next_el (list_pairs s) (x,y)) = y`。 -/
private theorem nextElListPairsFst {s : List ℕ} {x y : ℕ}
    (h : (x, y) ∈ listPairs s) :
    (nextEl (listPairs s) (x, y)).1 = y := by
  have hlen : (listPairs s).length = s.length := la7_length_listPairs s
  have hpos : 0 < (listPairs s).length := List.length_pos_of_mem h
  have hposl : 0 < s.length := by rw [← hlen]; exact hpos
  have hi : (listPairs s).idxOf (x, y) < (listPairs s).length :=
    List.idxOf_lt_length_iff.mpr h
  have hI : (listPairs s).idxOf (x, y) < s.length := by rw [← hlen]; exact hi
  have hxy : (listPairs s)[(listPairs s).idxOf (x, y)] = (x, y) := getElem_idxOf h
  have hpair := listPairsGetElem (s := s) (j := (listPairs s).idxOf (x, y)) hI
  have hys : s[((listPairs s).idxOf (x, y) + 1) % s.length]'(Nat.mod_lt _ hposl) = y :=
    congrArg Prod.snd (hpair.symm.trans hxy)
  rw [nextEl_eq_getD h, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos),
    listPairsGetElem (j := ((listPairs s).idxOf (x, y) + 1) % (listPairs s).length)
      (Nat.lt_of_lt_of_eq (Nat.mod_lt _ hpos) (la7_length_listPairs s))]
  have hAB : ((listPairs s).idxOf (x, y) + 1) % (listPairs s).length
      = ((listPairs s).idxOf (x, y) + 1) % s.length := by rw [hlen]
  have hA : s[((listPairs s).idxOf (x, y) + 1) % (listPairs s).length]'(
      Nat.lt_of_lt_of_eq (Nat.mod_lt _ hpos) (la7_length_listPairs s)) = y :=
    (getElemCon (Nat.lt_of_lt_of_eq (Nat.mod_lt _ hpos) (la7_length_listPairs s))
      (Nat.mod_lt _ hposl) hAB).symm ▸ hys
  exact hA

/-- no-uniq 版 `FST (f_list L x) = SND x`（Spine fListFstOfDarts TameList10:299；
片 3 `fListFstSnd` 去掉 `all uniq L` 前提的分量——其证体本就不消费该前提）。 -/
private theorem fListFstOfDarts (L : fgraph ℕ) {x : Dart}
    (hx : x ∈ listOfDarts L) : (fList L x).1 = x.2 := by
  obtain ⟨l, _, hff, hxl⟩ := findFaceDarts_ex_of_self (dart_in_face L x |>.mpr hx)
  show (nextEl (findFaceDarts L x) x).1 = x.2
  rw [hff]
  exact nextElListPairsFst hxl

/-- 非空表 `getLast!` 成员。 -/
private theorem getLastMem {l : List Dart} (h : l ≠ []) : l.getLast! ∈ l := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- `l[len-1]` 与 `getLast!` 项级换形。 -/
private theorem getElemLastGetLast! {l : List Dart} (hpos : 0 < l.length) :
    l[l.length - 1]'(by omega) = l.getLast! := by
  have h1 : (l[l.length - 1]? : Option Dart).getD default = l[l.length - 1]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, h1]

/-! ## §2 atom 内相邻链不变量（替代 Spine partsInductLemma 的 unlast 分量） -/

/-- atom 内「相邻 = n 步」链（结构递归谓词）。 -/
private def AtomChain (n : Dart → Dart) : List Dart → Prop
  | [] => True
  | [_] => True
  | d1 :: d2 :: t => d2 = n d1 ∧ AtomChain n (d2 :: t)

/-- 链提取：`i+1 < a.length ⟹ a[i+1] = n a[i]`。 -/
private theorem atomChain_getElem {a : List Dart} (h : AtomChain n a) :
    ∀ (i : ℕ) (hi : i + 1 < a.length),
      a[i + 1]'hi = n (a[i]'(Nat.lt_of_succ_lt hi)) := by
  induction a with
  | nil => intro i hi; simp at hi
  | cons d1 t ih =>
    cases t with
    | nil => intro i hi; simp at hi
    | cons d2 t2 =>
      obtain ⟨h12, hrest⟩ := h
      intro i hi
      cases i with
      | zero => simpa using h12
      | succ i' => exact ih hrest i' (by simpa using hi)

/-- 链维护：partitionIntoAtom0 的每个前插分支都满足 join 条件（`n new = head`），
故 acc 全链 ⇒ 结果全链（对扫描表结构归纳）。 -/
private theorem atomChain_pia0 :
    ∀ (s : List Dart) (acc : List (List Dart)),
      (∀ a ∈ acc, AtomChain n a) →
      ∀ a ∈ partitionIntoAtom0 n acc s, AtomChain n a := by
  intro s
  induction s with
  | nil =>
    intro acc h a ha
    rw [partitionIntoAtom0] at ha
    exact h a ha
  | cons s0 rest ih =>
    intro acc h
    cases acc with
    | nil =>
      simp only [partitionIntoAtom0]
      refine ih [[s0]] ?_
      intro a ha
      rw [List.mem_singleton] at ha
      subst ha
      exact trivial
    | cons a0 acc' =>
      simp only [partitionIntoAtom0]
      split_ifs with hcond
      · refine ih ((s0 :: a0) :: acc') ?_
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · cases a0 with
          | nil => exact trivial
          | cons d t =>
            exact ⟨(beq_iff_eq.mp hcond).symm, h (d :: t) (List.mem_cons_self ..)⟩
        · exact h a (List.mem_cons_of_mem a0 ha')
      · refine ih ([s0] :: a0 :: acc') ?_
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact trivial
        · exact h a ha'

/-- **unlast 分量**（Spine partsNextUnlast TameList9:1274 / HOL
`parts_next_last` 证明内蕴；`tame_list.hl:6408` 族）：
atom 内非末元 `x` 沿 atom 的 next_el = `f_list L (e_list x)`。
链岛证体 = §2 链不变量 + `nextEl_eq_getD` 取模归约。 -/
theorem partsNextUnlast (L : fgraph ℕ) {r : List Dart} (hun : r.Nodup) (hne : r ≠ []) :
    ∀ p ∈ parts L r, ∀ x ∈ p, x ≠ p.getLast! → nextEl p x = fList L (eList x) := by
  intro p hp x hx hx2
  have hpne : p ≠ [] := partsAllNonnil L r p hp
  have hpos : 0 < p.length := List.length_pos_of_ne_nil hpne
  have hchain : AtomChain (fun d => fList L (eList d)) p := by
    unfold parts partitionIntoAtom at hp
    exact atomChain_pia0 r.reverse [] (by intro a ha; simp at ha) p hp
  have hix : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hidxlast : p.idxOf x ≠ p.length - 1 := by
    intro hc
    refine hx2 ?_
    calc x = p[p.idxOf x]'hix := (getElem_idxOf hx).symm
      _ = p[p.length - 1]'(by omega) := getElemCon hix (by omega) hc
      _ = p.getLast! := getElemLastGetLast! hpos
  have hj : p.idxOf x + 1 < p.length := by omega
  rw [nextEl_eq_getD hx, Nat.mod_eq_of_lt hj, getD_eq_getElem_of_lt hj]
  calc p[p.idxOf x + 1]
      = (fun d => fList L (eList d)) (p[p.idxOf x]) :=
        atomChain_getElem hchain (p.idxOf x) hj
    _ = (fun d => fList L (eList d)) x := by rw [getElem_idxOf hx]

/-! ## §3 parts_node_inverse_power / parts_darts / parts_in_node -/

/-- **HOL `parts_darts`**（tame_list.hl:6722
`MEM x p ∧ MEM p (parts L r) ∧ MEM r N ∧ normal_list L N → MEM x (list_of_darts L)`）。
Spine 现名 `partsDarts`（TameList10:326）。
链岛证体：`partsFlatten` 把 x 落进 r，normalList 合取 4（loopList）收口。 -/
theorem partsDarts (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N)
    {p : List Dart} (hp : p ∈ parts L r) {x : Dart} (hx : x ∈ p) :
    x ∈ listOfDarts L := by
  have hrN : r.Nodup := (List.nodup_flatten.mp hN.1).1 r hr
  have hrne : r ≠ [] := hN.2.1 r hr
  have hxr : x ∈ r := by
    rw [← partsFlatten L hrN hrne]
    exact List.mem_flatten.mpr ⟨p, hp, hx⟩
  exact (hN.2.2.2.1 r hr x hxr).1

/-- **HOL `parts_node_inverse_power`**（tame_list.hl:6607
`normal_list ∧ good_list ∧ MEM r N ∧ MEM p (parts L r) ∧ MEM x p ∧
  k + indexl x p < sizel p ==>
  ((inverse (node_map (hypermap_of_list L))) POWER k) x = EL (k + indexl x p) p`）。
Spine 现名 `partsNodeInversePower`（TameList10:351）。
链岛证体：k 归纳；步进用 `partsNextUnlast`（§2）+ `inverseNodeMapList`
（片 3）+ `nextEl_eq_getD` 幂化（nextEl p 的取模下标 = k+1+idx）。 -/
theorem partsNodeInversePower (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N) {p : List Dart}
    (hp : p ∈ parts L r) (k : ℕ) {x : Dart} (hx : x ∈ p)
    (hlen : k + p.idxOf x < p.length) :
    (((hypermapOfList L hL).nodeMap.symm ^ k) x) = p[k + p.idxOf x]'(by omega) := by
  have hrN : r.Nodup := (List.nodup_flatten.mp hN.1).1 r hr
  have hrne : r ≠ [] := hN.2.1 r hr
  have hpne : p ≠ [] := partsAllNonnil L r p hp
  have hpos : 0 < p.length := List.length_pos_of_ne_nil hpne
  have hpun : p.Nodup := (partsUniqNonnil L hL hN hr hp).2.2.1
  have key : ∀ k : ℕ, ∀ z ∈ p, ∀ hl : k + p.idxOf z < p.length,
      (((hypermapOfList L hL).nodeMap.symm ^ k) z) = p[k + p.idxOf z]'hl := by
    intro k
    induction k with
    | zero =>
      intro z hz hl
      rw [pow_zero, Equiv.Perm.one_apply]
      exact (getElem_idxOf hz).symm.trans
        (getElemCon (List.idxOf_lt_length_iff.mpr hz) hl (Nat.zero_add _).symm)
    | succ k ih =>
      intro z hz h
      have hk : k + p.idxOf z < p.length := by omega
      have hIH := ih z hz hk
      have hy : p[k + p.idxOf z]'hk ∈ p := List.getElem_mem hk
      have hidx : p.idxOf (p[k + p.idxOf z]'hk) = k + p.idxOf z :=
        idxOf_getElem hpun hk
      have hynl : p[k + p.idxOf z]'hk ≠ p.getLast! := by
        intro hc
        have hlast : p.idxOf p.getLast! = p.length - 1 := by
          have hp : p.getLast! ∈ p := getLastMem hpne
          rw [← getElemLastGetLast! hpos]
          exact idxOf_getElem hpun (by omega)
        rw [hc] at hidx
        omega
      have hD : p[k + p.idxOf z]'hk ∈ listOfDarts L :=
        partsDarts L hL hN hr hp hy
      have hstep : (((hypermapOfList L hL).nodeMap.symm ^ (k + 1)) z)
          = fList L (eList (p[k + p.idxOf z]'hk)) := by
        rw [pow_succ', Equiv.Perm.mul_apply, hIH, inverseNodeMapList L hL hD]
      have hstep2 : fList L (eList (p[k + p.idxOf z]'hk))
          = nextEl p (p[k + p.idxOf z]'hk) :=
        (partsNextUnlast L hrN hrne p hp _ hy hynl).symm
      have hnext : nextEl p (p[k + p.idxOf z]'hk) = p[k + 1 + p.idxOf z]'(by omega) := by
        rw [nextEl_eq_getD hy, hidx, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
        have him : (k + p.idxOf z + 1) % p.length = k + 1 + p.idxOf z := by
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        exact getElemCon (Nat.mod_lt _ hpos) (by omega) him
      rw [hstep, hstep2, hnext]
  exact key k x hx hlen

/-- **HOL `parts_in_node`**（Spine partsInNode TameList9? 对应 HOL
`parts_node` 族）：`x ∈ p ∈ parts ∧ normal_list ⇒ x` 在 `p.head` 的 node 轨道内。
链岛证体：`partsNodeInversePower`（k = idxOf x，起点 p.head!）+
`nodeMap_symm_pow_mem_node_self`（Hypermap）。 -/
theorem partsInNode (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N) {p : List Dart}
    (hp : p ∈ parts L r) {x : Dart} (hx : x ∈ p) :
    x ∈ (hypermapOfList L hL).node p.head! := by
  have hpne : p ≠ [] := partsAllNonnil L r p hp
  have h0 : p.idxOf p.head! = 0 := by
    cases p with
    | nil => exact absurd rfl hpne
    | cons a t =>
      rw [List.head!_cons]
      exact List.idxOf_cons_self
  have hx0 : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hpow := partsNodeInversePower L hL hN hr hp (p.idxOf x)
    (x := p.head!) (List.head!_mem_self hpne) (by omega)
  have hmem := (hypermapOfList L hL).nodeMap_symm_pow_mem_node_self p.head! (p.idxOf x)
  rw [hpow] at hmem
  have hxx : p[p.idxOf x + p.idxOf p.head!]'(by omega) = p[p.idxOf x]'hx0 := by
    refine getElemCon _ _ ?_
    rw [h0]
    omega
  rw [hxx, getElem_idxOf hx] at hmem
  exact hmem

/-! ## §4 fstInvOrbit + partsFst -/

/-- nodeMap-symm 轨道保 FST 且留 dart 集（Spine fstInvOrbit TameList10:395；
HOL `fst_n_list_ext_power` 的 symm 版）。
链岛证体：步进 = `inverseNodeMapList`（片 3）+ §1 `fListFstOfDarts` +
`nodeMap_permutes.symm_apply_mem`。 -/
private theorem fstInvOrbit (L : fgraph ℕ) (hL : GoodList L) {x : Dart}
    (hx : x ∈ (hypermapOfList L hL).darts) :
    ∀ k : ℕ, (((hypermapOfList L hL).nodeMap.symm ^ k) x).1 = x.1 ∧
      ((hypermapOfList L hL).nodeMap.symm ^ k) x ∈ (hypermapOfList L hL).darts := by
  intro k
  induction k with
  | zero => exact ⟨rfl, hx⟩
  | succ m ih =>
    obtain ⟨hfst, hmem⟩ := ih
    have hD : ((hypermapOfList L hL).nodeMap.symm ^ m) x ∈ listOfDarts L :=
      List.mem_toFinset.mp hmem
    have hED : eList (((hypermapOfList L hL).nodeMap.symm ^ m) x) ∈ listOfDarts L :=
      hL.2.2 _ hD
    have hfst2 : ((((hypermapOfList L hL).nodeMap.symm ^ (m + 1)) x).1) = x.1 := by
      rw [pow_succ', Equiv.Perm.mul_apply, inverseNodeMapList L hL hD,
        fListFstOfDarts L hED]
      exact hfst
    have hmem2 : (((hypermapOfList L hL).nodeMap.symm ^ (m + 1)) x)
        ∈ (hypermapOfList L hL).darts := by
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (hypermapOfList L hL).nodeMap_permutes.symm_apply_mem hmem
    exact ⟨hfst2, hmem2⟩

/-- **HOL `parts_fst`**（tame_list.hl:6687
`normal_list L N ∧ good_list L ∧ MEM r N ∧ MEM p (parts L r) ∧ MEM x p ==>
  FST x = FST (HD p)`）。
Spine 现名 `partsFst`（TameList10:420）。
链岛证体：`partsInNode` 给出 x 在 node 轨道 → 反演幂表示
（`exists_pow_nodeMap_symm_apply_of_mem_node`）→ `fstInvOrbit` 保 FST。 -/
theorem partsFst (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N) {p : List Dart}
    (hp : p ∈ parts L r) {x : Dart} (hx : x ∈ p) :
    x.1 = p.head!.1 := by
  have hnode := partsInNode L hL hN hr hp hx
  obtain ⟨j, _, hj'⟩ := (hypermapOfList L hL).exists_pow_nodeMap_symm_apply_of_mem_node hnode
  have hpne : p ≠ [] := partsAllNonnil L r p hp
  have hd : p.head! ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr (partsDarts L hL hN hr hp (List.head!_mem_self hpne))
  rw [hj']
  exact (fstInvOrbit L hL hd j).1

end Kepler.Text.MoreLemma2PartsFst

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2PartsFst.partsNextUnlast
#print axioms Kepler.Text.MoreLemma2PartsFst.partsDarts
#print axioms Kepler.Text.MoreLemma2PartsFst.partsNodeInversePower
#print axioms Kepler.Text.MoreLemma2PartsFst.partsInNode
#print axioms Kepler.Text.MoreLemma2PartsFst.partsFst
