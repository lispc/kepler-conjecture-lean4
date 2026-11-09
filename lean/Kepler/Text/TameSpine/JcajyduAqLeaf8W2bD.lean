/-
  JcajyduAqLeaf8W2bD — AQ8 波 2b-i-2c：`hH` 本体（`parts_rev_f_betwn_pure` 边界判别）。

  ┌─ 范围 ────────────────────────────────────────────────────────
  │ ① 私件层：`getLast!`/`head!`/`reverse`/`map`/`range'` 基本对应
  │    （本版 Lean 无 `List.head!_reverse`/`List.getLast!_append` 等名）。
  │ ② `aq8w2d_prevElFirstEqLast`：hE3 首元回卷（`i = 1`）实例——
  │    `prevEl ((range' 1 k).map f) (f 1) = f k`，定义级、不进 hE3。
  │ ③ `aq8w2d_withinBlockStep`：块内降一步（`la7_nextEl_reverse` +
  │    **AQ4 W1 已落库的 `aq4_prevElMapUpt`**，带 `hnd`）。
  │ ④ `aq8w2d_hH`：边界判别本体（B1 块尾 / B2 块内非尾）。
  │ ⑤ `aq8w2d_partsRevFBetwnPure`：hH 落库后一行代入得 `parts` 形。
  └────────────────────────────────────────────────────────────────

  ┌─ 数学内容（B1 / B2 两支，替代 HOL 的 prev_el_hd/not_hd_flatten）──
  │ 记 `G d = rev(F d)`、`F d = map (nList^i d) (range' 1 (sz d))`，
  │ `g = flatten (rev (map G W))`，块 p = G w 是 g 的连续段。
  │ B2（d ∈ p 非尾，d = f j，2 ≤ j ≤ k）：块内后继 = f (j-1)（E3），
  │    且 `nodeMap (f (j-1)) = f j` ⇒ `f (j-1) = nodeMap⁻¹ d = fList (eList d)`
  │    （`nodeMapSymmEqFList`）——**相等**。
  │ B1（d = p.getLast! = f 1 = nList w）：`g = A ++ p ++ B`，
  │    `nextEl g d = B.head!`（`nextElCatLast1`）=
  │    `(G x').head! = f' (sz x') = (nList)^[sz x'] x' = x'`
  │    （`sz = ncard node` + `pow_card_node_apply_self` 循环闭合），
  │    `x'` 是 W 中 w 的前驱；`W.Nodup` 给 `x' ≠ w`，
  │    而 `fList (eList d) = nodeMap⁻¹ (nList w) = w`——**不等**。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）─────────────────────────────────────────────
  │ ① HOL 走 `next_el_rev` + `prev_el_hd_flatten`/`prev_el_not_hd_flatten`
  │    （AQ4 helper）；本条车走 `nextElCat1/2` + `nextElCatLast1` +
  │    `List.append_of_mem`（W 处切分），结论与 hH 逐字同形。
  │ ② E3 槽已消去：块内降一步直接消费 `aq4_prevElMapUpt`（AQ4 W1 落库，
  │    带 `hnd`；`hnd` = `g.Nodup` 的块子表），零自造副本。
  │ ③ `hH` 的载体语境槽（`hL`/`hgn`/`hsz`/`hW`/`hWnd`）在 AQ8 应用侧
  │    全部可导（`hW` = `aq8w2bB_WDarts`、`hWnd` = `uniqBetwn`、
  │    `hsz` = rfl、`hL`/`hgn` = marked_list 语境），非新数学前提。
  │ ④ hE3 首元回卷（`i = 1`）单列 `aq8w2d_prevElFirstEqLast`：原
  │    `1 ≤ i` 形在 `i = 1` 假（`logs/probe_he3_counter.log`）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w2d_` 前缀，私件 `aq8w2d_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W2bC
import Kepler.Text.TameSpine.JcajyduAqSplit1B
import Kepler.Text.TameSpine.JcajyduAqLeaf4W1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §0 基本对应（本版 Lean 无对应公开名，逐条私证） -/

/-- 非空表 `getLast!` = `getLast`（W1b 私件同证重推导）。 -/
private theorem aq8w2d_getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast_eq_getElem, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by have := List.length_pos_of_ne_nil h; omega)]
  simp

/-- `head!` 的 `head?`-`getD` 形（`getLast!` 的对偶折算件）。 -/
private theorem aq8w2d_head!_eq_getD_head? {α : Type*} [Inhabited α] (l : List α) :
    l.head! = l.head?.getD default := by
  cases l with
  | nil => rfl
  | cons a t => rfl

/-- `rev` 的末元 = 原表首元（本版 Lean 无 `List.getLast!_reverse`）。 -/
private theorem aq8w2d_getLast!_reverse {α : Type*} [Inhabited α] (l : List α) :
    l.reverse.getLast! = l.head! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_reverse, ← aq8w2d_head!_eq_getD_head?]

/-- `rev` 的首元 = 原表末元（本版 Lean 无 `List.head!_reverse`）。 -/
private theorem aq8w2d_head!_reverse {α : Type*} [Inhabited α] (l : List α) :
    l.reverse.head! = l.getLast! := by
  rw [aq8w2d_head!_eq_getD_head?, List.head?_reverse, ← List.getLast!_eq_getLast?_getD]

/-- `map` 的末元（本版 Lean 无 `List.getLast!_map`）。 -/
private theorem aq8w2d_getLast!_map {α β : Type*} [Inhabited α] [Inhabited β]
    {l : List α} (f : α → β) (h : l ≠ []) : (l.map f).getLast! = f l.getLast! := by
  have hm : l.map f ≠ [] := fun h0 => h (List.map_eq_nil_iff.mp h0)
  rw [aq8w2d_getLast!_eq_getLast hm, List.getLast_map hm, ← aq8w2d_getLast!_eq_getLast h]

/-- 连接的末元（右半非空；本版 Lean 无 `List.getLast!_append`）。 -/
private theorem aq8w2d_getLast!_append {α : Type*} [Inhabited α] (s : List α)
    {t : List α} (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

/-- `range' 1 k` 非空（`0 < k`）。 -/
private theorem aq8w2d_range'NeNil {k : ℕ} (hk : 0 < k) : List.range' 1 k ≠ [] := by
  intro h0
  have hlen : (List.range' 1 k).length = k := List.length_range'
  rw [h0] at hlen
  simp at hlen
  omega

/-- `range' 1 k` 首元 = 1（`0 < k`）。 -/
private theorem aq8w2d_range'_head! {k : ℕ} (hk : 0 < k) :
    (List.range' 1 k).head! = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [List.range'_succ, List.head!_cons]

/-- `range' 1 k` 末元 = k（`0 < k`）。 -/
private theorem aq8w2d_range'_getLast! {k : ℕ} (hk : 0 < k) :
    (List.range' 1 k).getLast! = k := by
  have hne := aq8w2d_range'NeNil hk
  rw [aq8w2d_getLast!_eq_getLast hne, List.getLast_range' hne]
  omega

/-- 非空表 `getLastD` = `getLast!`。 -/
private theorem aq8w2d_getLastD_eq_getLast! {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) (a : α) : l.getLastD a = l.getLast! := by
  rw [List.getLastD_eq_getLast?, List.getLast!_eq_getLast?_getD,
    List.getLast?_eq_some_getLast h]
  rfl

/-- 块（反序 nList 幂块）的末元 = `f 1`（`0 < k`）。 -/
private theorem aq8w2d_blockGetLast {k : ℕ} (hk : 0 < k) (f : ℕ → ℕ × ℕ) :
    ((List.range' 1 k).reverse.map f).getLast! = f 1 := by
  rw [List.map_reverse, aq8w2d_getLast!_reverse,
    hdMap (List.range' 1 k) f (aq8w2d_range'NeNil hk), aq8w2d_range'_head! hk]

/-- 块（反序 nList 幂块）的首元 = `f k`（`0 < k`）。 -/
private theorem aq8w2d_blockHead {k : ℕ} (hk : 0 < k) (f : ℕ → ℕ × ℕ) :
    ((List.range' 1 k).reverse.map f).head! = f k := by
  rw [List.map_reverse, aq8w2d_head!_reverse,
    aq8w2d_getLast!_map f (aq8w2d_range'NeNil hk), aq8w2d_range'_getLast! hk]

/-! ## §1 hE3 首元回卷（`i = 1` 定义级实例，不进 hE3） -/

/-- `idxOf` 在 `prevEl` 体内所用实例是 `instBEqOfDecidableEq`（`prevEl`
只吃 `[DecidableEq α]`，体内 `idxOf` 的 `BEq` 由之合成）；按同一实例陈述，
避免默认 `instBEqProd` 与体内实例的语法不匹配。 -/
private theorem aq8w2d_idxOf_cons_self_dec (a : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    @List.idxOf (ℕ × ℕ) instBEqOfDecidableEq a (a :: l) = 0 :=
  @List.idxOf_cons_self (ℕ × ℕ) a instBEqOfDecidableEq _ l

/-- hE3 的首元回卷支：`prevEl ((range' 1 k).map f) (f 1) = f k`
（`prevEl` 在首元处回卷到末元；`idxOf (f 1) = 0` 定义级，与 `f` 单射无关）。
这是修正 hE3 之外单独需要的**定义级**事实（原 `1 ≤ i` 形在此处为假，
见 `logs/probe_he3_counter.log`）。 -/
theorem aq8w2d_prevElFirstEqLast {k : ℕ} (hk : 0 < k) (f : ℕ → ℕ × ℕ) :
    prevEl ((List.range' 1 k).map f) (f 1) = f k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hk' : 0 < n + 1 := by omega
  have hne := aq8w2d_range'NeNil hk'
  have hmne : (List.range' 1 (n + 1)).map f ≠ [] := by
    intro h0
    exact hne (List.map_eq_nil_iff.mp h0)
  have hmem : f 1 ∈ (List.range' 1 (n + 1)).map f := by
    rw [List.range'_succ]
    exact List.mem_map_of_mem List.mem_cons_self
  have hidx : @List.idxOf (ℕ × ℕ) instBEqOfDecidableEq (f 1)
      ((List.range' 1 (n + 1)).map f) = 0 := by
    rw [List.range'_succ, List.map_cons]
    exact aq8w2d_idxOf_cons_self_dec (f 1) _
  have hgd : ((List.range' 1 (n + 1)).map f).getLastD (f 1) = f (n + 1) := by
    rw [aq8w2d_getLastD_eq_getLast! hmne, aq8w2d_getLast!_map f hne,
      aq8w2d_range'_getLast! hk']
  unfold prevEl
  rw [if_neg (not_not.mpr hmem), hidx, if_pos rfl]
  exact hgd

/-! ## §2 块内降一步 + dart 幂闭包 -/

/-- 块内非尾元素的一步：`nextEl (rev (map f (range' 1 k))) (f j) = f (j-1)`
（`2 ≤ j ≤ k`，块 `map f (range' 1 k)` 无重）。消费 AQ4 W1 的
`aq4_prevElMapUpt`（带 `hnd`，零自造副本）。 -/
private theorem aq8w2d_withinBlockStep (L : fgraph ℕ) (w : ℕ × ℕ) {k : ℕ}
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

/-- 块内元素（nList 幂）均在 darts（`d ∈ listOfDarts L` 的迭代闭包）。 -/
private theorem aq8w2d_iterateMemDarts (L : fgraph ℕ) (hL : GoodList L)
    {w : ℕ × ℕ} (hw : w ∈ listOfDarts L) (m : ℕ) :
    (nList L)^[m] w ∈ listOfDarts L := by
  induction m with
  | zero => simpa using hw
  | succ k ih => rw [Function.iterate_succ_apply']; exact nListMemDarts L hL ih

/-! ## §3 `hH` 本体（块尾 B1 / 块内 B2） -/

/-- **`partsCharacterize` 的 `hH` 槽**（`parts_rev_f_betwn_pure` 边界判别）：
对块表 `prt = rev (map G W)` 的每个件 `p`、每个 `d ∈ p`（`d ≠ g.getLast!`），
`nextEl g d ≠ fList L (eList d) ↔ d = p.getLast!`。

载体语境槽（AQ8 应用侧全可导）：`hL`/`hgn`（GoodList 语境）、
`hsz`（`sz` 即面计数，定义级）、`hW`（窗口 dart 全在 darts）、
`hWnd`（窗口无重）。**无 E3 条件槽**：块内降一步吃 `aq4_prevElMapUpt`。 -/
theorem aq8w2d_hH (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (W : List (ℕ × ℕ)) (sz : ℕ × ℕ → ℕ) (g : List (ℕ × ℕ))
    (hsz : ∀ d ∈ W, sz d = (L.flatten.filter (fun t => decide (t = d.1))).length)
    (hW : ∀ d ∈ W, d ∈ listOfDarts L) (hWnd : W.Nodup)
    (hg : g = (((W.map (fun d =>
          (List.range' 1 (sz d)).map (fun i => (nList L)^[i] d))).flatten)).reverse)
    (hun : g.Nodup) (hpos : ∀ d ∈ W, 0 < sz d) :
    ∀ p ∈ (W.map (fun d =>
            (List.range' 1 (sz d)).reverse.map (fun i => (nList L)^[i] d))).reverse,
          ∀ d ∈ p, d ≠ g.getLast! →
            (nextEl g d ≠ fList L (eList d) ↔ d = p.getLast!) := by
  set Gf : ℕ × ℕ → List (ℕ × ℕ) :=
    fun d => (List.range' 1 (sz d)).reverse.map (fun i => (nList L)^[i] d) with hGf
  have hblockne : ∀ x ∈ W, Gf x ≠ [] := by
    intro x hx
    exact aq8w2b_blockNonnil L (hpos x hx) x
  have hfl : (W.map Gf).reverse.flatten = g := by
    rw [hGf]
    exact aq8w2bB_flattenEq L W sz g hg
  intro p hp d hd hdne
  obtain ⟨w, hwW, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp)
  have hbne : Gf w ≠ [] := hblockne w hwW
  -- W 在 w 处切分：W = W1 ++ w :: W2
  obtain ⟨W1, W2, hWsplit⟩ := List.append_of_mem hwW
  have hsplitG : (W.map Gf).reverse.flatten
      = (W2.map Gf).reverse.flatten ++ Gf w ++ (W1.map Gf).reverse.flatten := by
    rw [hWsplit]
    simp only [List.map_append, List.map_cons, List.reverse_append, List.reverse_cons,
      List.flatten_append, List.flatten_cons,
      List.singleton_append, List.append_assoc]
  have hgsplit : g = (W2.map Gf).reverse.flatten ++ Gf w ++ (W1.map Gf).reverse.flatten := by
    rw [← hfl]
    exact hsplitG
  have hndall : ((W2.map Gf).reverse.flatten ++ Gf w
      ++ (W1.map Gf).reverse.flatten).Nodup := by
    rw [← hgsplit]
    exact hun
  -- 块无重（g 无重的子表）
  have hblocknd : ((List.range' 1 (sz w)).map (fun i => (nList L)^[i] w)).Nodup := by
    have h1 : (Gf w).Sublist ((W2.map Gf).reverse.flatten ++ Gf w) :=
      List.sublist_append_right _ _
    have h2 : ((W2.map Gf).reverse.flatten ++ Gf w).Sublist ((W2.map Gf).reverse.flatten
        ++ Gf w ++ (W1.map Gf).reverse.flatten) := List.sublist_append_left _ _
    have h3 : (Gf w).Nodup := List.Sublist.nodup (h1.trans h2) hndall
    have h3' : ((List.range' 1 (sz w)).reverse.map (fun i => (nList L)^[i] w)).Nodup := h3
    rw [List.map_reverse, List.nodup_reverse] at h3'
    exact h3'
  by_cases hlast : d = (Gf w).getLast!
  · -- B1：块尾（d = f 1 = nList w），需**不等**
    have hblkLast : (Gf w).getLast! = (nList L)^[1] w :=
      aq8w2d_blockGetLast (hpos w hwW) _
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
    -- W1 ≠ []：否则 d = g.getLast!（撞假设）
    have hW1ne : W1 ≠ [] := by
      intro hW1
      apply hdne
      rw [hlast, hgsplit, hW1, List.map_nil, List.reverse_nil, List.flatten_nil,
        List.append_nil, aq8w2d_getLast!_append _ hbne]
    have hBne : (W1.map Gf).reverse.flatten ≠ [] := by
      intro h0
      have h1 : W1.map Gf ≠ [] := fun hc => hW1ne (List.map_eq_nil_iff.mp hc)
      have hMne : (W1.map Gf).reverse ≠ [] := by simpa using h1
      have hmem : ((W1.map Gf).reverse).head! ∈ (W1.map Gf).reverse :=
        List.head!_mem_self hMne
      have hq : ((W1.map Gf).reverse).head! = [] :=
        (List.flatten_eq_nil_iff.mp h0) _ hmem
      obtain ⟨x, hxW1, hxq⟩ := List.mem_map.mp (List.mem_reverse.mp hmem)
      exact hblockne x (by rw [hWsplit]; exact List.mem_append.mpr (Or.inl hxW1))
        (hxq.trans hq)
    -- nextEl g d = B.head!
    have hAblkne : (W2.map Gf).reverse.flatten ++ Gf w ≠ [] := by
      intro h0
      exact hbne (List.append_eq_nil_iff.mp h0).2
    have hstep : nextEl g d = (W1.map Gf).reverse.flatten.head! := by
      have hcat := nextElCatLast1 (s := (W2.map Gf).reverse.flatten ++ Gf w)
        (t := (W1.map Gf).reverse.flatten) hndall hAblkne hBne
      rw [← hgsplit, aq8w2d_getLast!_append _ hbne, ← hlast] at hcat
      exact hcat
    -- B.head! = x' 且 (G x').head! = x' = W1.getLast!，且 x' ≠ w
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
    have hGhead : (Gf x').head! = x' := by
      have hb := aq8w2d_blockHead (hpos x' hx'W) (fun i => (nList L)^[i] x')
      rw [hb]
      rw [nListPowEqNodeMapPow L hL (hW x' hx'W) (sz x'),
        (hsz x' hx'W).trans (szEqNodeCard L hL hgn
          (List.mem_toFinset.mpr (hW x' hx'W)))]
      exact Kepler.Text.Hypermap.pow_card_node_apply_self (hypermapOfList L hL) x'
    have hBhead : ((W1.map Gf).reverse.flatten).head! = x' := by
      rw [← List.cons_head!_tail hMne', List.flatten_cons, ← hx'eq]
      exact (List.head!_append _ hx'ne).trans hGhead
    have hx'neW : x' ≠ w := by
      have hnd' : (W1 ++ w :: W2).Nodup := by
        rw [← hWsplit]; exact hWnd
      exact (List.nodup_append.mp hnd').2.2 x' hx'W1 w List.mem_cons_self
    constructor
    · intro _; exact hlast
    · intro _
      rw [hstep, hBhead, hfList]
      exact hx'neW
  · -- B2：块内非尾（d = f j，2 ≤ j ≤ k），需**相等**
    have hdmemL : d ∈ (List.range' 1 (sz w)).map (fun i => (nList L)^[i] w) := by
      have h0 : d ∈ (List.range' 1 (sz w)).reverse.map (fun i => (nList L)^[i] w) := hd
      rw [List.map_reverse, List.mem_reverse] at h0
      exact h0
    obtain ⟨j, hjmem, hjeq⟩ := List.mem_map.mp hdmemL
    obtain ⟨i, hik, hjeq2⟩ :=
      (List.mem_range' (s := 1) (n := sz w) (step := 1) (m := j)).mp hjmem
    have hjk : j ≤ sz w := by omega
    have hjne1 : j ≠ 1 := by
      intro h1
      apply hlast
      rw [← hjeq, h1]
      exact (aq8w2d_blockGetLast (hpos w hwW) (fun i => (nList L)^[i] w)).symm
    have h2 : 2 ≤ j := by omega
    have hstepB : nextEl g d = (nList L)^[j - 1] w := by
      have hAblknd : ((W2.map Gf).reverse.flatten ++ Gf w).Nodup :=
        List.Sublist.nodup (List.sublist_append_left _ _) hndall
      have h1 : nextEl g d = nextEl ((W2.map Gf).reverse.flatten ++ Gf w) d := by
        have hcat := nextElCat1 (s := (W2.map Gf).reverse.flatten ++ Gf w)
          (t := (W1.map Gf).reverse.flatten) hAblknd
          (List.mem_append.mpr (Or.inr hd))
          (by rw [aq8w2d_getLast!_append _ hbne]; exact hlast)
        rw [← hgsplit] at hcat
        exact hcat
      have h2' : nextEl ((W2.map Gf).reverse.flatten ++ Gf w) d = nextEl (Gf w) d :=
        nextElCat2 (s := (W2.map Gf).reverse.flatten) (t := Gf w) hAblknd hd hlast
      have h3 : nextEl (Gf w) d = (nList L)^[j - 1] w := by
        rw [← hjeq]
        exact aq8w2d_withinBlockStep L w hblocknd h2 hjk
      exact h1.trans (h2'.trans h3)
    have hdj : d = (nList L)^[j] w := hjeq.symm
    have hnodeMapEq : (hypermapOfList L hL).nodeMap ((nList L)^[j - 1] w) = d := by
      rw [Kepler.Text.TameLp.nodeMap_hypermapOfList L hL
        (List.mem_toFinset.mpr (aq8w2d_iterateMemDarts L hL (hW w hwW) (j - 1)))]
      have hexp : (j - 1).succ = j := by omega
      rw [← Function.iterate_succ_apply' (nList L) (j - 1) w, hexp, hdj]
    have hsymm : (hypermapOfList L hL).nodeMap.symm d = (nList L)^[j - 1] w := by
      rw [← hnodeMapEq, Equiv.symm_apply_apply]
    have hdDarts : d ∈ (hypermapOfList L hL).darts := by
      rw [hdj]
      exact List.mem_toFinset.mpr (aq8w2d_iterateMemDarts L hL (hW w hwW) j)
    have hbridge : fList L (eList d) = (nList L)^[j - 1] w :=
      (nodeMapSymmEqFList L hL (d := d) hdDarts).symm.trans hsymm
    constructor
    · intro hne2
      exact absurd (hstepB.trans hbridge.symm) hne2
    · intro heq
      exact absurd heq hlast

/-! ## §4 总装：hH 落库后一行代入 -/

/-- `parts_rev_f_betwn_pure` 的载体语境形：`parts L g = prt`。
由 W2b-i-2b 的 `aq8w2bC_partsRevFBetwnPure` 与本节 `aq8w2d_hH` 一行代入
即得。**E3 槽已消去**：块内降一步直接消费 AQ4 W1 落库的
`aq4_prevElMapUpt`（带 `hnd`；`hnd` 由 `g.Nodup` 的块子表给出）。 -/
theorem aq8w2d_partsRevFBetwnPure (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (W : List (ℕ × ℕ)) (sz : ℕ × ℕ → ℕ) (g : List (ℕ × ℕ))
    (hsz : ∀ d ∈ W, sz d = (L.flatten.filter (fun t => decide (t = d.1))).length)
    (hW : ∀ d ∈ W, d ∈ listOfDarts L) (hWnd : W.Nodup)
    (hg : g = (((W.map (fun d =>
          (List.range' 1 (sz d)).map (fun i => (nList L)^[i] d))).flatten)).reverse)
    (hne : g ≠ []) (hun : g.Nodup)
    (hpos : ∀ d ∈ W, 0 < sz d) :
    partsSpine L g = (W.map (fun d =>
        (List.range' 1 (sz d)).reverse.map (fun i => (nList L)^[i] d))).reverse :=
  aq8w2bC_partsRevFBetwnPure L W sz g hg hne hun hpos
    (aq8w2d_hH L hL hgn W sz g hsz hW hWnd hg hun hpos)

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：全部 ⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w2d_prevElFirstEqLast
#print axioms Kepler.Text.TameSpine.aq8w2d_hH
#print axioms Kepler.Text.TameSpine.aq8w2d_partsRevFBetwnPure
