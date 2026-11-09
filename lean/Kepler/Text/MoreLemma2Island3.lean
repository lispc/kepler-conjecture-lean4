/-
  Kepler.Text.MoreLemma2Island3 — J 战役 J1（片 3 第一波）：
  37 件 Island-only 重落清单 + L1 门槛件的**超级映射/parts-域**一组。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/tame_list.hl`）──
  │ 本波 4 件（HOL 行号 ↔ Spine 现名 ↔ 本文件 Lean 名）：
  │   :4933  `edge_nondeg_f_xor_ni`      edgeNondegFXorNi  (TameList8:368)  → edgeNondegFXorNi
  │   :6702  `f_list_fst_snd`            fListFstSnd       (TameList10:319) → fListFstSnd
  │   :4371  `is_restricted_e_list_nondeg` isRestrictedEListNondeg (TameList6:591) → isRestrictedEListNondeg
  │   :6572  `parts_uniq_nonnil`         partsUniqNonnil  (TameList9:1277)  → partsUniqNonnil
  │ 另含私有机器（HOL/Spine 对应）：
  │   `node_inverse_map_list`（tame_list.hl:2870 ↔ inverseNodeMapList TameList8:348）
  │   `next_el_list_pairs` FST 半边（list_hypermap-compiled.hl:316 ↔
  │   nextElListPairsFst TameList10:274）+ listPairs 逐项式/下标运输三私件
  │   （nextElListPairsFst / listPairsGetElem / getElemCon 链岛重落）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体桥（链世界已有，直接复用零重落）──────────────────────────
  │ `hypermap_of_list` ↦ `TameLp.hypermapOfList L hL`（TameLp:5188）；
  │ `edge_map`/`node_map`/`face_map` 点态桥 = `edgeMap_hypermapOfList` /
  │ `nodeMap_hypermapOfList` / `faceMap_hypermapOfList`（TameLp:5225/5240/5247）；
  │ `lemma_edge_nondegenerate` ↦ `Hypermap.edgeNondegenerate_iff`（Hypermap:8419，
  │   `EdgeNondegenerate ↔ ∀ x ∈ darts, faceMap x ≠ nodeMap.symm x`）；
  │ `is_restricted` ↦ `Hypermap.IsRestricted`（Hypermap:9645，含 EdgeNondegenerate
  │   合取块，访问子 `IsRestricted.edgeNondegenerate`:9663）；
  │ `node_inverse` 引擎 = `nList_fList`（TameLp:5144）+ `e_list` 对合；
  │ `f_list`/`e_list`/`list_of_darts`/`list_pairs` = Assembly 同名件；
  │ `normal_list` = `ChainLists.normalList L hL N`（L1 `220b7b20`）；
  │ `parts_flatten`/`parts_all_nonnil` = M0e 本车道落库件（MoreLemma2Island2）。
  └────────────────────────────────────────────────────────────────

  ┌─ 未入本波（停报，详见 DELIVERY-M0e 续报）────────────────────
  │ :6687 `parts_fst` 与 :7976 `f_list_quotient_alt`：两者都消费
  │ `parts_node_inverse_power`（tame_list.hl:6607，Spine 版 ≈80 行）——
  │ 需 nodeMap.symm 沿 atom 的 k 步枚举 + indexl_next_el + parts_next_unlast，
  │ 建议独立片 M0h；:6490 `next_el_parts_unlast` 需 next_el_cat 机器
  │ （nextElCat1/2 + flattenLastMem + findList 唯一性，≈150 行），片 3 波 2。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；泛型 binder 零实例
  （全部 Dart/ℕ 具体载体）；import 闭包零 TameSpine、零 Assembly 主模块。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.ChainListsL1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2Island3

open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart parts)
open Kepler.Text.MoreLemma2Island2 (partsFlatten partsAllNonnil)
open Kepler.Text.ChainLists (normalList)
open Kepler.Text.TameLp (hypermapOfList hypermapOfList_iso_refl
  darts_hypermapOfList edgeMap_hypermapOfList nodeMap_hypermapOfList
  faceMap_hypermapOfList findFaceDarts_ex_of_self dart_in_face
  la7_length_listPairs fList_mem_darts nList_fList
  getElem_idxOf idxOf_getElem getD_eq_getElem_of_lt nextEl_eq_getD)
open Kepler.Assembly (fList eList listOfDarts listPairs GoodList nextEl findFaceDarts)

/-! ## §1 listPairs 私有机器（next_el_list_pairs 的 FST 半边链岛重落） -/

/-- 下标相等时的 getElem 运输（证明无关；rw 跨 index-等式的免疫器）。 -/
private theorem getElemCon {α : Type*} {l : List α} {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a = b) :
    l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- `list_pairs` 的逐项式（HOL `nth_list_pairs` 的 rot-1 位移；任意表成立）：
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

/-- **HOL `next_el_list_pairs` 的 FST 半边**（list_hypermap-compiled.hl:316
`MEM (x,y) (list_pairs s) ==> FST (next_el (list_pairs s) (x,y)) = y`）。
Spine 现名 `nextElListPairsFst`（TameList10:274，私件）。
链岛证体：`next_el` 归约 getD + `listPairsGetElem` 逐项式 + 模下标运输。 -/
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

/-! ## §2 超级映射桥件 -/

/-- **HOL `node_inverse_map_list`**（tame_list.hl:2870；
Spine 现名 `inverseNodeMapList` TameList8:348）：
`d ∈ list_of_darts L ⇒ (node_map (hypermap_of_list L)).symm d = f_list L (e_list d)`。
链岛证体：`nList_fList`（node∘face = edge）+ e_list 对合 + perm 反演。 -/
theorem inverseNodeMapList (L : fgraph ℕ) (hL : GoodList L) {d : Dart}
    (hd : d ∈ listOfDarts L) :
    (hypermapOfList L hL).nodeMap.symm d = fList L (eList d) := by
  have hN : (listOfDarts L).Nodup := hL.1
  have hed : eList d ∈ listOfDarts L := hL.2.2 d hd
  have hy : fList L (eList d) ∈ listOfDarts L := fList_mem_darts hN hed
  have hyD : fList L (eList d) ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr hy
  have hstep : (hypermapOfList L hL).nodeMap (fList L (eList d)) = d := by
    rw [nodeMap_hypermapOfList L hL hyD, nList_fList hN hed]
    cases d with
    | mk a b => rfl
  conv_lhs => rw [← hstep]
  simp

/-- **HOL `edge_nondeg_f_xor_ni`**（tame_list.hl:4933
`good_list L /\ MEM x (list_of_darts L) /\
  is_edge_nondegenerate (hypermap_of_list L) ==> ~(f_list L x = f_list L (e_list x))`）。
Spine 现名 `edgeNondegFXorNi`（TameList8:368）。
链岛证体：`edgeNondegenerate_iff`（faceMap ≠ nodeMap.symm）+ §2
`inverseNodeMapList` —— 若 `f_list x = f_list (e_list x)` 则
`faceMap x = nodeMap.symm x`，与边非退化矛盾。 -/
theorem edgeNondegFXorNi (L : fgraph ℕ) (hL : GoodList L)
    (hne : (hypermapOfList L hL).EdgeNondegenerate) {x : Dart}
    (hx : x ∈ listOfDarts L) : fList L x ≠ fList L (eList x) := by
  have hxD : x ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hx
  intro hcon
  have hneq : (hypermapOfList L hL).faceMap x ≠ (hypermapOfList L hL).nodeMap.symm x :=
    ((hypermapOfList L hL).edgeNondegenerate_iff.mp hne) x hxD
  apply hneq
  rw [faceMap_hypermapOfList L hL hxD, inverseNodeMapList L hL hx]
  exact hcon

/-- **HOL `is_restricted_e_list_nondeg`**（tame_list.hl:4371
`good_list L /\ is_restricted (hypermap_of_list L) /\
  MEM d (list_of_darts L) ==> ~(e_list d = d)`）。
Spine 现名 `isRestrictedEListNondeg`（TameList6:591）。
链岛证体：`IsRestricted.edgeNondegenerate` 合取块直取 +
`edgeMap_hypermapOfList`（edge_map 点态 = e_list）。 -/
theorem isRestrictedEListNondeg (L : fgraph ℕ) (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted) {d : Dart}
    (hd : d ∈ listOfDarts L) : eList d ≠ d := by
  have hdD : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd
  have hne := hres.edgeNondegenerate d hdD
  rw [edgeMap_hypermapOfList L hL hdD] at hne
  exact hne

/-- **HOL `f_list_fst_snd`**（tame_list.hl:6702
`all uniq L /\ MEM x (list_of_darts L) ==> FST (f_list L x) = SND x`）。
Spine 现名 `fListFstSnd`（TameList10:319，经 fListFstOfDarts:299）。
链岛证体：`findFaceDarts_ex_of_self` 把 `find_face L x` 局部化为某面 `l` 的
`list_pairs l`，再收 `nextElListPairsFst`。`all uniq L` 为 HOL 原文前提
（FST 半边免 uniq；下游 SND 半版消费），逐字保留。 -/
theorem fListFstSnd (L : fgraph ℕ) (hunL : ∀ l ∈ L, l.Nodup) {x : Dart}
    (hx : x ∈ listOfDarts L) : (fList L x).1 = x.2 := by
  obtain ⟨l, _, hff, hxl⟩ := findFaceDarts_ex_of_self (dart_in_face L x |>.mpr hx)
  show (nextEl (findFaceDarts L x) x).1 = x.2
  rw [hff]
  exact nextElListPairsFst hxl

/-! ## §3 normal_list 门槛件（L1 `220b7b20` 解锁） -/

/-- **HOL `parts_uniq_nonnil`**（tame_list.hl:6572
`normal_list L N /\ MEM r N /\ MEM p (parts L r) ==>
  uniq r /\ ~(r = []) /\ uniq p /\ ~(p = []) /\ (!x. MEM x p ==> MEM x r)`）。
Spine 现名 `partsUniqNonnil`（TameList9:1277）。
链岛证体：`normal_list` 的 flatten-Nodup + all-nonnil 两合取块；
`p` 侧走 `parts_flatten` 把 `(parts L r).flatten.Nodup` 转回 `r.Nodup`，
`List.nodup_flatten` 取子表 Nodup；成员包含走 `parts_flatten` 等式。 -/
theorem partsUniqNonnil (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N) {p : List Dart}
    (hp : p ∈ parts L r) :
    r.Nodup ∧ r ≠ [] ∧ p.Nodup ∧ p ≠ [] ∧ ∀ x ∈ p, x ∈ r := by
  have hrN : r.Nodup := (List.nodup_flatten.mp hN.1).1 r hr
  have hrne : r ≠ [] := hN.2.1 r hr
  have hflat : (parts L r).flatten.Nodup := by
    rw [partsFlatten L hrN hrne]; exact hrN
  have hpN : p.Nodup := (List.nodup_flatten.mp hflat).1 p hp
  have hpne : p ≠ [] := partsAllNonnil L r p hp
  refine ⟨hrN, hrne, hpN, hpne, ?_⟩
  intro x hx
  rw [← partsFlatten L hrN hrne]
  exact List.mem_flatten.mpr ⟨p, hp, hx⟩

/-! ## §4 next_el_cat 尾巴机器 + `next_el_parts_unlast`

tame_list.hl:5580-5790 的 next_el_cat 族链岛重落（Spine TameList9:123-200/
§1/:358 同名前缀）。与 Spine 的差异：`flattenLastMem` 不走 find_list 唯一性
（findListUniq/lastFindList），改用「flatten 末元 = 最后子表末元 + Nodup 唯一」
的直接归纳（少 ~60 行且零 findList 依赖）。 -/

section NextElCatMachine

/-- 非空表 `getLast!` 必是成员（Spine getLastMem TameList10:113）。 -/
private theorem getLastMem {l : List Dart} (h : l ≠ []) : l.getLast! ∈ l := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- `l[len-1]` 与 `getLast!` 的项级换形（Spine getElemLastGetLast! TameList9:123）。 -/
private theorem getElemLastGetLast! {l : List Dart} (hpos : 0 < l.length) :
    l[l.length - 1]'(by omega) = l.getLast! := by
  have h1 : (l[l.length - 1]? : Option Dart).getD default = l[l.length - 1]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, h1]

/-- **HOL `indexl_LAST`**（tame_list.hl:5591-:5611；Spine idxOfGetLast TameList9:139）：
`uniq s ∧ s ≠ [] ⇒ indexl (LAST s) s = sizel s - 1`。 -/
private theorem idxOfGetLast {s : List Dart} (hun : s.Nodup) (hne : s ≠ []) :
    s.idxOf s.getLast! = s.length - 1 := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  have h1 : (s[s.length - 1]? : Option Dart).getD default = s[s.length - 1]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, h1,
    idxOf_getElem hun (by omega)]

/-- nodup 拼接表两段同元矛盾（Spine nodupAppendDisjoint TameList9:176）。 -/
private theorem nodupAppendDisjoint {s t : List Dart} {x : Dart}
    (hnd : (s ++ t).Nodup) (hs : x ∈ s) (ht : x ∈ t) : False :=
  (List.nodup_append.mp hnd).2.2 x hs x ht rfl

/-- **HOL `next_el_cat1`**（tame_list.hl:5613-:5646；Spine nextElCat1 TameList9:210）
`uniq s ∧ MEM x s ∧ x ≠ LAST s ==> next_el (cat s t) x = next_el s x`。 -/
private theorem nextElCat1 {s t : List Dart} (hsn : s.Nodup) {x : Dart}
    (hx : x ∈ s) (hx2 : x ≠ s.getLast!) :
    nextEl (s ++ t) x = nextEl s x := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  have hidx : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hlast : s.idxOf x ≠ s.length - 1 := by
    intro hc
    refine hx2 ?_
    have heq : s[s.idxOf x]'hidx = s[s.length - 1]'(by omega) :=
      getElemCon hidx (by omega) hc
    calc x = s[s.idxOf x]'hidx := (getElem_idxOf hx).symm
      _ = s[s.length - 1]'(by omega) := heq
      _ = s.getLast! := getElemLastGetLast! hpos
  have hj1 : s.idxOf x + 1 < s.length := by omega
  rw [nextEl_eq_getD (List.mem_append.mpr (Or.inl hx)), nextEl_eq_getD hx,
    List.idxOf_append_of_mem hx,
    Nat.mod_eq_of_lt (show s.idxOf x + 1 < (s ++ t).length from by
      rw [List.length_append]; omega),
    getD_eq_getElem_of_lt (show s.idxOf x + 1 < (s ++ t).length from by
      rw [List.length_append]; omega),
    Nat.mod_eq_of_lt hj1,
    getD_eq_getElem_of_lt hj1, List.getElem_append_left hj1]

/-- **HOL `next_el_cat2`**（tame_list.hl:5665-:5694；Spine nextElCat2 TameList9:240）
`uniq (cat s t) ∧ MEM x t ∧ x ≠ LAST t ==> next_el (cat s t) x = next_el t x`。 -/
private theorem nextElCat2 {s t : List Dart} (hnd : (s ++ t).Nodup) {x : Dart}
    (hx : x ∈ t) (hx2 : x ≠ t.getLast!) :
    nextEl (s ++ t) x = nextEl t x := by
  have htl : 0 < t.length := List.length_pos_of_mem hx
  have hsout : x ∉ s := fun hc => nodupAppendDisjoint hnd hc hx
  have hidx : t.idxOf x < t.length := List.idxOf_lt_length_iff.mpr hx
  have hj1 : t.idxOf x + 1 < t.length := by
    have hx2' : t.idxOf x ≠ t.length - 1 := by
      intro hc
      refine hx2 ?_
      have heq : t[t.idxOf x]'hidx = t[t.length - 1]'(by omega) :=
        getElemCon hidx (by omega) hc
      calc x = t[t.idxOf x]'hidx := (getElem_idxOf hx).symm
        _ = t[t.length - 1]'(by omega) := heq
        _ = t.getLast! := getElemLastGetLast! htl
    omega
  rw [nextEl_eq_getD (List.mem_append.mpr (Or.inr hx)), nextEl_eq_getD hx,
    List.idxOf_append_of_notMem hsout,
    show (s.length + t.idxOf x) + 1 = s.length + (t.idxOf x + 1) from by omega,
    Nat.mod_eq_of_lt (show s.length + (t.idxOf x + 1) < (s ++ t).length from by
      rw [List.length_append]; omega),
    getD_eq_getElem_of_lt (show s.length + (t.idxOf x + 1) < (s ++ t).length from by
      rw [List.length_append]; omega),
    Nat.mod_eq_of_lt hj1,
    getD_eq_getElem_of_lt hj1]
  exact (List.getElem_append_right
      (show s.length ≤ s.length + (t.idxOf x + 1) by omega)).trans
    (getElemCon (show s.length + (t.idxOf x + 1) - s.length < t.length by omega) hj1
      (show s.length + (t.idxOf x + 1) - s.length = t.idxOf x + 1 by omega))

/-- 拼接表末元缺省件（Spine lastCat TameList9:199）。 -/
private theorem lastCat {u v : List Dart} (hv : v ≠ []) :
    (u ++ v).getLast! = v.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_append_of_ne_nil _ hv,
    List.getLast!_eq_getLast?_getD]

/-- flatten 末元 = 末子表末元（Spine flattenLastMem TameList9:354 的链岛直证版：
不经 find_list 唯一性；对 L 归纳，cons 支用 getLast!-append 归约到 tail +
`nodup_append` 两段不交排除「x 同时在 u 与 tail.flatten」。） -/
private theorem flattenLastMem : ∀ (L : List (List Dart)), L.flatten.Nodup →
    ∀ {x : Dart} {r : List Dart}, r ∈ L → x ∈ r → x = L.flatten.getLast! →
      x = r.getLast! := by
  intro L
  induction L with
  | nil => intro _ x r hr; cases hr
  | cons u t ih =>
    intro hun x r hr hxr hx
    rw [List.flatten_cons] at hun hx
    rcases List.mem_cons.mp hr with rfl | hmem
    · by_cases ht0 : t.flatten = []
      · rw [ht0, List.append_nil] at hx
        exact hx
      · have hx' : x = t.flatten.getLast! := by rw [hx, lastCat ht0]
        have hxf : x ∈ t.flatten := by rw [hx']; exact getLastMem ht0
        exact absurd hxf (nodupAppendDisjoint hun hxr)
    · by_cases ht0 : t.flatten = []
      · have hxt : x ∈ t.flatten := List.mem_flatten.mpr ⟨r, hmem, hxr⟩
        rw [ht0] at hxt
        exact absurd hxt (by simp)
      · have hnt : t.flatten.Nodup := (List.nodup_append.mp hun).2.1
        have hx' : x = t.flatten.getLast! := by rw [hx, lastCat ht0]
        exact ih hnt hmem hxr hx'

/-- **HOL `next_el_flatten_unlast`**（tame_list.hl:5752-:5784；
Spine nextElFlattenUnlast TameList9:358）
`uniq (flatten L) ∧ MEM x r ∧ MEM r L ∧ x ≠ LAST r ==>
  next_el (flatten L) x = next_el r x`。 -/
private theorem nextElFlattenUnlast {L : List (List Dart)} {r : List Dart} {x : Dart}
    (hun : L.flatten.Nodup) (hxr : x ∈ r) (hr : r ∈ L)
    (hx2 : x ≠ r.getLast!) : nextEl L.flatten x = nextEl r x := by
  induction L with
  | nil => cases hr
  | cons u t ih =>
    rw [List.flatten_cons] at hun
    rw [List.flatten_cons]
    rcases List.mem_cons.mp hr with heq | hmem
    · rw [heq] at hxr hx2 ⊢
      have hsn : u.Nodup :=
        List.Sublist.nodup (List.sublist_append_left u t.flatten) hun
      exact nextElCat1 hsn hxr hx2
    · have hxf : x ∈ t.flatten := List.mem_flatten.mpr ⟨r, hmem, hxr⟩
      have htfne : t.flatten ≠ [] := List.ne_nil_of_mem hxf
      have hx2' : x ≠ t.flatten.getLast! := by
        intro hc
        exact hx2 (flattenLastMem t
          (List.Sublist.nodup (List.sublist_append_right u t.flatten) hun)
          hmem hxr hc)
      rw [nextElCat2 hun (List.mem_flatten.mpr ⟨r, hmem, hxr⟩) hx2']
      exact ih (List.Sublist.nodup (List.sublist_append_right u t.flatten) hun) hmem

/-- **HOL `next_el_parts_unlast`**（tame_list.hl:6490
`uniq r /\ ~(r = []) /\ MEM x p /\ MEM p (parts L r) /\ ~(x = LAST p) ==>
  next_el r x = next_el p x`）。
Spine 现名 `nextElPartsUnlast`（TameList9:1368）。
链岛证体：`parts_flatten` 把 r 换成 `(parts L r).flatten`（Nodup 保留），
再收 §4 `nextElFlattenUnlast`。 -/
theorem nextElPartsUnlast (L : fgraph ℕ) {r : List Dart} (hun : r.Nodup)
    (hne : r ≠ []) {p : List Dart} (hp : p ∈ parts L r) {x : Dart}
    (hx : x ∈ p) (hx2 : x ≠ p.getLast!) : nextEl r x = nextEl p x := by
  have hpfl : (parts L r).flatten.Nodup := by
    rw [partsFlatten L hun hne]; exact hun
  rw [← partsFlatten L hun hne]
  exact nextElFlattenUnlast hpfl hx hp hx2

end NextElCatMachine

end Kepler.Text.MoreLemma2Island3

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2Island3.inverseNodeMapList
#print axioms Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi
#print axioms Kepler.Text.MoreLemma2Island3.isRestrictedEListNondeg
#print axioms Kepler.Text.MoreLemma2Island3.fListFstSnd
#print axioms Kepler.Text.MoreLemma2Island3.partsUniqNonnil
#print axioms Kepler.Text.MoreLemma2Island3.nextElPartsUnlast
