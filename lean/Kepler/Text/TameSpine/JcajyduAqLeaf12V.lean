/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12V — AQ12 叶 W-F3c-i（decl 62 前置）。

  HOL：AQ12.hl:3236-:3496（261 行）`cat_fst_split_normal_parts` 的
  parts 分解（W-F3c-ii 装配用）。本文件落三块：
  · `aq12v_hH`：块边界判别（HOL 261 行主体；**移位重推**：块长
    `count - 1` = `ndSpine`，不是 `aq8w2d_hH` 的 `count`）；
  · `aq12v_szPos` / `aq12v_gNe` / `aq12v_gNodup`：`0 < sz` / `g ≠ []` / `g.Nodup`；
  · `aq12v_partsNew1Rev`：`aq8w2bC_partsRevFBetwnPure` 的 `sz := count-1` 实例化。

  hH 陈述与 `aq8w2bC_partsRevFBetwnPure` 的槽逐字同形（`sz := fun d => count-1`）：
  `∀ p ∈ (W.map (fun d => (range' 1 (count-1)).reverse.map (nList^i) d)).reverse,
     ∀ d ∈ p, d ≠ g.getLast! → (nextEl g d ≠ fList (eList d) ↔ d = p.getLast!)`。
  额外上下文（`hm`/`hf`/`W` 的窗口定义/`g` 定义/`hun`/`hpos`）只用于证明，不改槽。

  操作器供 `0<sz`：`two_le_sz_of_restricted`（Split1B:339，需
  `hrestr = hm.1.1 : IsRestricted` 与 `d ∈ darts`，后者由窗口 ⊆ findFace 经
  `mem_darts_of_mem_findFace` + `List.mem_toFinset` 供）。

  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W2bD
import Kepler.Text.TameSpine.JcajyduAqLeaf8W2bB
import Kepler.Text.TameSpine.JcajyduAqSplit1F
import Kepler.Text.TameCorrCard

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList nList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face mem_darts_of_mem_findFace)

/-! ## §0 块代数私件（`range' 1 k` 反序 nList 幂块） -/

private theorem aq12v_getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  rfl

private theorem aq12v_getLast!_map {α β : Type*} [Inhabited α] [Inhabited β]
    {l : List α} (f : α → β) (h : l ≠ []) : (l.map f).getLast! = f l.getLast! := by
  have hm : l.map f ≠ [] := fun h0 => h (List.map_eq_nil_iff.mp h0)
  rw [aq12v_getLast!_eq_getLast hm, List.getLast_map hm, ← aq12v_getLast!_eq_getLast h]

private theorem aq12v_getLast!_append {α : Type*} [Inhabited α] (s : List α)
    {t : List α} (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

private theorem aq12v_getLast!_reverse {α : Type*} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.reverse.getLast! = l.head! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_reverse, List.head!_eq_head?_getD]

private theorem aq12v_range'NeNil {k : ℕ} (hk : 0 < k) : List.range' 1 k ≠ [] := by
  intro h0
  have hlen : (List.range' 1 k).length = k := List.length_range'
  rw [h0] at hlen
  simp at hlen
  omega

private theorem aq12v_range'_head! {k : ℕ} (hk : 0 < k) : (List.range' 1 k).head! = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [List.range'_succ, List.head!_cons]

private theorem aq12v_range'_getLast! {k : ℕ} (hk : 0 < k) :
    (List.range' 1 k).getLast! = k := by
  have hne := aq12v_range'NeNil hk
  rw [aq12v_getLast!_eq_getLast hne, List.getLast_range' hne]
  omega

private theorem aq12v_blockAscNe (L : fgraph ℕ) {k : ℕ} (hk : 0 < k) (d : ℕ × ℕ) :
    (List.range' 1 k).map (fun i => (nList L)^[i] d) ≠ [] := by
  intro h0
  have hlen : ((List.range' 1 k).map (fun i => (nList L)^[i] d)).length = k := by
    rw [List.length_map, List.length_range']
  rw [h0] at hlen
  simp at hlen
  omega

private theorem aq12v_blockGetLast {k : ℕ} (hk : 0 < k) (f : ℕ → ℕ × ℕ) :
    ((List.range' 1 k).reverse.map f).getLast! = f 1 := by
  have hne := aq12v_range'NeNil hk
  have hmne : (List.range' 1 k).map f ≠ [] := fun h0 => hne (List.map_eq_nil_iff.mp h0)
  rw [List.map_reverse, aq12v_getLast!_reverse hmne, hdMap _ f hne,
    aq12v_range'_head! hk]

private theorem aq12v_blockHead {k : ℕ} (hk : 0 < k) (f : ℕ → ℕ × ℕ) :
    ((List.range' 1 k).reverse.map f).head! = f k := by
  rw [List.map_reverse, head!Reverse, aq12v_getLast!_map f (aq12v_range'NeNil hk),
    aq12v_range'_getLast! hk]

private theorem aq12v_withinBlockStep (L : fgraph ℕ) (w : ℕ × ℕ) {k : ℕ}
    (hnd : ((List.range' 1 k).map (fun i => (nList L)^[i] w)).Nodup)
    {j : ℕ} (h2 : 2 ≤ j) (hjk : j ≤ k) :
    nextEl ((List.range' 1 k).reverse.map (fun i => (nList L)^[i] w)) ((nList L)^[j] w)
      = (nList L)^[j - 1] w := by
  have hjmem : j ∈ List.range' 1 k :=
    (List.mem_range' (s := 1) (n := k) (step := 1) (m := j)).mpr
      ⟨j - 1, by omega, by omega⟩
  have hmem : (fun i => (nList L)^[i] w) j
      ∈ (List.range' 1 k).map (fun i => (nList L)^[i] w) :=
    List.mem_map_of_mem hjmem
  rw [List.map_reverse, Kepler.Text.TameLp.la7_nextEl_reverse hnd hmem,
    aq4_prevElMapUpt k (fun i => (nList L)^[i] w) hnd h2 hjk]

private theorem aq12v_iterateMemDarts (L : fgraph ℕ) (hL : GoodList L)
    {w : ℕ × ℕ} (hw : w ∈ listOfDarts L) (m : ℕ) :
    (nList L)^[m] w ∈ listOfDarts L := by
  induction m with
  | zero => simpa using hw
  | succ k ih => rw [Function.iterate_succ_apply']; exact nListMemDarts L hL ih

/-! ## §1 窗口计数正性（`0 < count - 1`） -/

/-- 窗口 dart 的 node 计数 ≥ 2 ⇒ `0 < count - 1`（`IsRestricted` 供
`nodeNondegenerate`；`d ∈ darts` 由窗口 ⊆ findFace 供）。 -/
theorem aq12v_szPos (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hrestr : (hypermapOfList L hL).IsRestricted)
    {W : List (ℕ × ℕ)} (hW : ∀ d ∈ W, d ∈ listOfDarts L) :
    ∀ d ∈ W, 0 < (L.flatten.filter (fun t => decide (t = d.1))).length - 1 := by
  intro d hd
  have hD : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr (hW d hd)
  have h2 := two_le_sz_of_restricted L hL hgn hrestr hD
  omega

/-! ## §2 hH（块边界三支，块长 count-1 的移位重推） -/

/-- **`aq8w2bC_partsRevFBetwnPure` 的 hH 槽**（`sz := count-1` 逐字同形）：
对块表反序的每个件、每个非 `g.getLast!` 元素，边界判别成立。
上下文供窗口几何（`W = between f y z`）与 `g` 定义；槽本身不加/减前提。 -/
theorem aq12v_hH (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (W : List (ℕ × ℕ)) (g : List (ℕ × ℕ))
    (hWdef : W = between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))
    (hgdef : g = (((W.map (fun d =>
          (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
            (fun i => (nList L)^[i] d))).flatten)).reverse)
    (hun : g.Nodup)
    (hpos : ∀ d ∈ W, 0 < (L.flatten.filter (fun t => decide (t = d.1))).length - 1) :
    ∀ p ∈ (W.map (fun d =>
            (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).reverse.map
              (fun i => (nList L)^[i] d))).reverse,
          ∀ d ∈ p, d ≠ g.getLast! →
            (nextEl g d ≠ fList L (eList d) ↔ d = p.getLast!) := by
  let K : ℕ × ℕ → ℕ := fun d => (L.flatten.filter (fun t => decide (t = d.1))).length - 1
  set Gf : ℕ × ℕ → List (ℕ × ℕ) :=
    fun d => (List.range' 1 (K d)).reverse.map (fun i => (nList L)^[i] d) with hGf
  have hW : ∀ d ∈ W, d ∈ listOfDarts L := by
    intro d hd
    rw [hWdef] at hd
    exact mem_darts_of_mem_findFace L (betwnMem hd)
  have hKpos : ∀ d ∈ W, 0 < K d := hpos
  have hblockne : ∀ x ∈ W, Gf x ≠ [] := by
    intro y hy
    exact aq8w2b_blockNonnil L (hKpos y hy) y
  have hfl : (W.map Gf).reverse.flatten = g := by
    rw [hGf]
    exact aq8w2bB_flattenEq L W K g hgdef
  intro p hp d hd hdne
  obtain ⟨w, hwW, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp)
  have hbne : Gf w ≠ [] := hblockne w hwW
  obtain ⟨W1, W2, hWsplit⟩ := List.append_of_mem hwW
  have hsplitG : (W.map Gf).reverse.flatten
      = (W2.map Gf).reverse.flatten ++ Gf w ++ (W1.map Gf).reverse.flatten := by
    rw [hWsplit]
    simp only [List.map_append, List.map_cons, List.reverse_append, List.reverse_cons,
      List.flatten_append, List.flatten_cons,
      List.singleton_append, List.append_assoc]
  have hgsplit : g = (W2.map Gf).reverse.flatten ++ Gf w
      ++ (W1.map Gf).reverse.flatten := by
    rw [← hfl]
    exact hsplitG
  have hndall : ((W2.map Gf).reverse.flatten ++ Gf w
      ++ (W1.map Gf).reverse.flatten).Nodup := by
    rw [← hgsplit]
    exact hun
  have hblocknd : ((List.range' 1 (K w)).map (fun i => (nList L)^[i] w)).Nodup := by
    have h1 : (Gf w).Sublist ((W2.map Gf).reverse.flatten ++ Gf w) :=
      List.sublist_append_right _ _
    have h2 : ((W2.map Gf).reverse.flatten ++ Gf w).Sublist ((W2.map Gf).reverse.flatten
        ++ Gf w ++ (W1.map Gf).reverse.flatten) := List.sublist_append_left _ _
    have h3 : (Gf w).Nodup := List.Sublist.nodup (h1.trans h2) hndall
    have h3' : ((List.range' 1 (K w)).reverse.map (fun i => (nList L)^[i] w)).Nodup := h3
    rw [List.map_reverse, List.nodup_reverse] at h3'
    exact h3'
  by_cases hlast : d = (Gf w).getLast!
  · -- B1：块尾（d = nList w），需**不等**
    have hblkLast : (Gf w).getLast! = (nList L)^[1] w :=
      aq12v_blockGetLast (hKpos w hwW) _
    have hdval : d = (nList L)^[1] w := hlast.trans hblkLast
    have hd1 : d = nList L w := by rw [hdval, Function.iterate_one]
    have hwD : w ∈ listOfDarts L := hW w hwW
    have hdD : d ∈ listOfDarts L := by
      rw [hd1]; exact nListMemDarts L hL hwD
    have hndEq : (hypermapOfList L hL).nodeMap w = d := by
      rw [Kepler.Text.TameLp.nodeMap_hypermapOfList L hL (List.mem_toFinset.mpr hwD)]
      exact hd1.symm
    have hsymm : (hypermapOfList L hL).nodeMap.symm d = w := by
      rw [← hndEq, Equiv.symm_apply_apply]
    have hfList : fList L (eList d) = w :=
      (nodeMapSymmEqFList L hL (d := d) (List.mem_toFinset.mpr hdD)).symm.trans hsymm
    have hW1ne : W1 ≠ [] := by
      intro hW1
      apply hdne
      rw [hlast, hgsplit, hW1, List.map_nil, List.reverse_nil, List.flatten_nil,
        List.append_nil, aq12v_getLast!_append _ hbne]
    have hBne : (W1.map Gf).reverse.flatten ≠ [] := by
      intro h0
      have h1 : W1.map Gf ≠ [] := fun hc => hW1ne (List.map_eq_nil_iff.mp hc)
      have hMne : (W1.map Gf).reverse ≠ [] := by simpa using h1
      have hmem : ((W1.map Gf).reverse).head! ∈ (W1.map Gf).reverse :=
        List.head!_mem_self hMne
      have hq : ((W1.map Gf).reverse).head! = [] :=
        (List.flatten_eq_nil_iff.mp h0) _ hmem
      obtain ⟨y, hyW1, hyq⟩ := List.mem_map.mp (List.mem_reverse.mp hmem)
      exact hblockne y (by rw [hWsplit]; exact List.mem_append.mpr (Or.inl hyW1))
        (hyq.trans hq)
    have hAblkne : (W2.map Gf).reverse.flatten ++ Gf w ≠ [] := by
      intro h0
      exact hbne (List.append_eq_nil_iff.mp h0).2
    have hstep : nextEl g d = (W1.map Gf).reverse.flatten.head! := by
      have hcat := nextElCatLast1 (s := (W2.map Gf).reverse.flatten ++ Gf w)
        (t := (W1.map Gf).reverse.flatten) hndall hAblkne hBne
      rw [← hgsplit, aq12v_getLast!_append _ hbne, ← hlast] at hcat
      exact hcat
    have hMne' : (W1.map Gf).reverse ≠ [] := by
      have h1 : W1.map Gf ≠ [] := fun hc => hW1ne (List.map_eq_nil_iff.mp hc)
      simpa using h1
    have hqhead : ((W1.map Gf).reverse).head! ∈ W1.map Gf :=
      (List.mem_reverse).mp (List.head!_mem_self hMne')
    obtain ⟨x', hx'W1, hx'eq⟩ :
        ∃ x' ∈ W1, Gf x' = ((W1.map Gf).reverse).head! := List.mem_map.mp hqhead
    have hx'W : x' ∈ W := by
      rw [hWsplit]; exact List.mem_append.mpr (Or.inl hx'W1)
    have hx'ne : Gf x' ≠ [] := hblockne x' hx'W
    -- 块首 = nList^(count-1) x' = nodeMap.symm x'（移位后的关键差异）
    have hGhead : (Gf x').head! = (hypermapOfList L hL).nodeMap.symm x' := by
      have hKx' : 0 < K x' := hKpos x' hx'W
      have hhead : (Gf x').head! = (nList L)^[K x'] x' := aq12v_blockHead hKx' _
      rw [hhead, nListPowEqNodeMapPow L hL (hW x' hx'W) (K x')]
      have hcard : K x' + 1 = ((hypermapOfList L hL).node x').ncard := by
        rw [← szEqNodeCard L hL hgn (List.mem_toFinset.mpr (hW x' hx'W))]
        have hK := hKx'
        dsimp only [K] at hK ⊢
        omega
      have hpowfull : (hypermapOfList L hL).nodeMap^[K x' + 1] x' = x' := by
        rw [hcard]
        exact Kepler.Text.Hypermap.pow_card_node_apply_self _ x'
      have hstep1 : (hypermapOfList L hL).nodeMap
          ((hypermapOfList L hL).nodeMap^[K x'] x') = x' := by
        rw [← Function.iterate_succ_apply' (hypermapOfList L hL).nodeMap (K x') x']
        exact hpowfull
      exact ((Equiv.symm_apply_eq (hypermapOfList L hL).nodeMap).mpr hstep1.symm).symm
    have hBhead : ((W1.map Gf).reverse.flatten).head! = (hypermapOfList L hL).nodeMap.symm x' := by
      rw [← List.cons_head!_tail hMne', List.flatten_cons, ← hx'eq]
      exact (List.head!_append _ hx'ne).trans hGhead
    -- d ∉ W（窗口几何）：d = nodeMap w；若 d ∈ W 则 d = w 撞 node 非退化
    have hdNotW : d ∉ W := by
      intro hdW
      have hdf : d ∈ findFaceDarts L x := by
        rw [hWdef] at hdW; exact betwnMem hdW
      have hwf : w ∈ findFaceDarts L x := by
        rw [hWdef] at hwW; exact betwnMem hwW
      have hwd : w ∈ listOfDarts L := mem_darts_of_mem_findFace L hwf
      have hdd : d ∈ listOfDarts L := mem_darts_of_mem_findFace L hdf
      have hfacew : findFaceDarts L w = findFaceDarts L x :=
        aq10_memFindFaceImpFacesEq hL.1 hwf
      have hdfw : d ∈ findFaceDarts L w := by rw [hfacew]; exact hdf
      have hdface : d ∈ (hypermapOfList L hL).face w := by
        rw [Kepler.Text.TameCorrCard.faceOfList hL hwd]
        exact hdfw
      have hdnode : d ∈ (hypermapOfList L hL).node w := by
        rw [← hndEq]
        simpa using Kepler.Text.Hypermap.pow_nodeMap_mem_node (hypermapOfList L hL) w 1
      have hsimple := simpleHypermapList L hL hgn (isRestrictedAllUniq L hL hgn hm.1.1)
      have hinter : d ∈ (hypermapOfList L hL).node w ∩ (hypermapOfList L hL).face w :=
        ⟨hdnode, hdface⟩
      rw [hsimple w (List.mem_toFinset.mpr hwd)] at hinter
      have hdw : d = w := Set.mem_singleton_iff.mp hinter
      have hndne : (hypermapOfList L hL).nodeMap w ≠ w :=
        hm.1.1.nodeNondegenerate w (List.mem_toFinset.mpr hwd)
      exact hndne (hndEq.trans hdw)
    have hx'd : x' ≠ d := fun h => hdNotW (h ▸ hx'W)
    have hwne : w ≠ (hypermapOfList L hL).nodeMap.symm x' := by
      intro hweq
      have h1 : (hypermapOfList L hL).nodeMap w = x' := by
        rw [hweq]
        simp
      exact hx'd (h1.symm.trans hndEq)
    constructor
    · intro _; exact hlast
    · intro _
      rw [hstep, hBhead, hfList]
      exact Ne.symm hwne
  · -- B2：块内非尾（d = nList^j w，2 ≤ j ≤ K w），需**相等**
    have hdmemL : d ∈ (List.range' 1 (K w)).map (fun i => (nList L)^[i] w) := by
      have h0 : d ∈ (List.range' 1 (K w)).reverse.map (fun i => (nList L)^[i] w) := hd
      rw [List.map_reverse, List.mem_reverse] at h0
      exact h0
    obtain ⟨j, hjmem, hjeq⟩ := List.mem_map.mp hdmemL
    obtain ⟨i, hik, hjeq2⟩ :=
      (List.mem_range' (s := 1) (n := K w) (step := 1) (m := j)).mp hjmem
    have hjk : j ≤ K w := by omega
    have hjne1 : j ≠ 1 := by
      intro h1
      apply hlast
      rw [← hjeq, h1]
      exact (aq12v_blockGetLast (hKpos w hwW) (fun i => (nList L)^[i] w)).symm
    have h2 : 2 ≤ j := by omega
    have hstepB : nextEl g d = (nList L)^[j - 1] w := by
      have hAblknd : ((W2.map Gf).reverse.flatten ++ Gf w).Nodup :=
        List.Sublist.nodup (List.sublist_append_left _ _) hndall
      have h1 : nextEl g d = nextEl ((W2.map Gf).reverse.flatten ++ Gf w) d := by
        have hcat := nextElCat1 (s := (W2.map Gf).reverse.flatten ++ Gf w)
          (t := (W1.map Gf).reverse.flatten) hAblknd
          (List.mem_append.mpr (Or.inr hd))
          (by rw [aq12v_getLast!_append _ hbne]; exact hlast)
        rw [← hgsplit] at hcat
        exact hcat
      have h2' : nextEl ((W2.map Gf).reverse.flatten ++ Gf w) d = nextEl (Gf w) d :=
        nextElCat2 (s := (W2.map Gf).reverse.flatten) (t := Gf w) hAblknd hd hlast
      have h3 : nextEl (Gf w) d = (nList L)^[j - 1] w := by
        rw [← hjeq]
        exact aq12v_withinBlockStep L w hblocknd h2 hjk
      exact h1.trans (h2'.trans h3)
    have hdj : d = (nList L)^[j] w := hjeq.symm
    have hnodeMapEq : (hypermapOfList L hL).nodeMap ((nList L)^[j - 1] w) = d := by
      rw [Kepler.Text.TameLp.nodeMap_hypermapOfList L hL
        (List.mem_toFinset.mpr (aq12v_iterateMemDarts L hL (hW w hwW) (j - 1)))]
      have hexp : (j - 1).succ = j := by omega
      rw [← Function.iterate_succ_apply' (nList L) (j - 1) w, hexp, hdj]
    have hsymm : (hypermapOfList L hL).nodeMap.symm d = (nList L)^[j - 1] w := by
      rw [← hnodeMapEq, Equiv.symm_apply_apply]
    have hdDarts : d ∈ (hypermapOfList L hL).darts := by
      rw [hdj]
      exact List.mem_toFinset.mpr (aq12v_iterateMemDarts L hL (hW w hwW) j)
    have hbridge : fList L (eList d) = (nList L)^[j - 1] w :=
      (nodeMapSymmEqFList L hL (d := d) hdDarts).symm.trans hsymm
    constructor
    · intro hne2
      exact absurd (hstepB.trans hbridge.symm) hne2
    · intro heq
      exact absurd heq hlast

/-! ## §3 三前置（`g ≠ []` / `g.Nodup` / `0 < sz`）与 `aq8w2bC` 实例化 -/

/-- 窗口非空 + 块非空 ⇒ `g ≠ []`。 -/
theorem aq12v_gNe (L : fgraph ℕ) {W : List (ℕ × ℕ)} {g : List (ℕ × ℕ)}
    (hWne : W ≠ []) (hpos : ∀ d ∈ W, 0 < (L.flatten.filter (fun t => decide (t = d.1))).length - 1)
    (hg : g = (((W.map (fun d =>
          (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
            (fun i => (nList L)^[i] d))).flatten)).reverse) : g ≠ [] := by
  rw [hg]
  intro h0
  have hfl0 : ((W.map (fun d =>
      (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
        (fun i => (nList L)^[i] d))).flatten) = [] :=
    List.reverse_eq_nil_iff.mp h0
  obtain ⟨d, hdW⟩ := List.exists_mem_of_ne_nil W hWne
  have hmem : ((List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
      (fun i => (nList L)^[i] d)) ∈ W.map (fun d =>
        (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
          (fun i => (nList L)^[i] d)) := List.mem_map_of_mem hdW
  exact absurd ((List.flatten_eq_nil_iff.mp hfl0) _ hmem)
    (aq12v_blockAscNe L (hpos d hdW) d)

/-- 窗口块表的反序展平无重（`split.1` 无重 + `split1Unfold` 前缀）。 -/
theorem aq12v_gNodup (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ((((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
        (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
          (fun i => (nList L)^[i] d))).flatten)).reverse.Nodup := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hsplit := aq1_split1Nodup L hL hgn hunL hm hf
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hface : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1
  have hdecomp : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
      = (((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
            (fun i => (nList L)^[i] d))).flatten).reverse
        ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
    rw [split1Unfold, hnextz1, hface]
    rfl
  rw [hdecomp] at hsplit
  exact (List.nodup_append.mp hsplit).1

/-- `aq8w2bC_partsRevFBetwnPure` 的 `sz := count-1` 实例化：
`parts L (new1.reverse) = (W.map (fun d => (ndSpine d).reverse)).reverse`。 -/
theorem aq12v_partsNew1Rev (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hWne : between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) ≠ []) :
    partsSpine L ((((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
        (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
          (fun i => (nList L)^[i] d))).flatten).reverse)
      = ((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).reverse.map
            (fun i => (nList L)^[i] d))).reverse := by
  have hW : ∀ d ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x),
      d ∈ listOfDarts L := by
    intro d hd
    exact mem_darts_of_mem_findFace L (betwnMem hd)
  have hpos := aq12v_szPos L hL hgn hm.1.1 hW
  have hun := aq12v_gNodup L hL hgn hm hf
  have hne := aq12v_gNe L hWne hpos rfl
  exact aq8w2bC_partsRevFBetwnPure L
    (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))
    (fun d => (L.flatten.filter (fun t => decide (t = d.1))).length - 1)
    ((((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
        (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
          (fun i => (nList L)^[i] d))).flatten).reverse)
    rfl hne hun hpos
    (aq12v_hH L hL hgn hm hf
      (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))
      ((((between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => (List.range' 1 ((L.flatten.filter (fun t => decide (t = d.1))).length - 1)).map
            (fun i => (nList L)^[i] d))).flatten).reverse)
      rfl rfl hun hpos)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq12v_szPos
#print axioms Kepler.Text.TameSpine.aq12v_hH
#print axioms Kepler.Text.TameSpine.aq12v_gNe
#print axioms Kepler.Text.TameSpine.aq12v_gNodup
#print axioms Kepler.Text.TameSpine.aq12v_partsNew1Rev
