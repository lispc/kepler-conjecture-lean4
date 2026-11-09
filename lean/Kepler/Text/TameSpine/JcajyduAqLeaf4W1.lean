/-
  Kepler.Text.TameSpine.JcajyduAqLeaf4W1 — AQ4 叶 W1：行内走步引擎。

  AQ4 的结论（`aq4Concl`，TowerBase:248）是 `all (loop_list L) (ntrans … 1)`。
  **坍缩形态（第三种）**：旧行 `s ∈ N₁/N₂` 直接投影 `NormalListSpine` 的
  4th 合取（`hm.1.2.1.2.2.2.1 s`）；只剩两行新表
  `s2 = f2 ++ new2` 与 `s1 = new1.reverse ++ f1` 需要真证。W1 = 这两行的
  **走步引擎**（行级装配留 W2/W3）。

  ┌─ 件表（HOL 锚：AQ4.hl 的 28 个 helper，逐条对表见 DELIVERY）────
  │ ① `aq4_oneStepFindFace`（E5）：面内 one-step **rfl 级**——
  │    `fList L x` 定义即 `nextEl (findFaceDarts L x) x`（GoodListDefs:62），
  │    面等价一折。取代 HOL 的 PPLHULJ/count_node_face 长链。
  │ ② `aq4_prevElMapRange`（**E2 泛形，跨车道接口件**）：
  │    `prevEl ((range' 1 k).map f) (f i) = f (i-1)`（2 ≤ i ≤ k，
  │    需 `((range' 1 k).map f).Nodup`）。= HOL `PREV_EL_UPT`
  │    （AQ4.hl:262-306）+ `prev_el_map_upt`（:327-352）的合并形，
  │    **AQ8 的 `hE3` 可直接特化**（见 DELIVERY 逐字陈述）。
  │ ③ `aq4_prevElNdSpine`（E2 特化）：`f := fun j => (nList L)^[j] d`、
  │    `k := sz-1` 的代入；块内前驱 = 前一幂。
  │ ④ `aq4_ndSpineHead`：`(ndSpine L d).head! = nList L d`。
  │ ⑤ `aq4_nextElBlockLast`（E3a）：**块边界（nextEl 形）**——
  │    `nextEl blocks.flatten b.getLast! = Q.head!.head!`（`blocks = P ++ b :: Q`）。
  │    HOL `prev_el_hd_flatten`（:413-543，131 行）的对偶件。
  │ ⑥ `aq4_blockBoundaryStep`（E3b）：**块边界 one_step**——
  │    `oneStep (ndSpine d0).head! (ndSpine dprev).getLast!`
  │    （`dprev = prevEl (findFaceDarts L d0) d0`）。
  │ ⑦ `aq4_nListEqNodeMap` / `aq4_prevElBetwnOfNeHead`（E1）：
  │    `nList = nodeMap`（单步）；**弧 prevEl 连续**
  │    `x ∈ betwn r y z ∧ x ≠ head ⇒ prevEl (betwn) x = prevEl r x`。

  ┌─ 跨车道接口（AQ8 `hE3`，2 ≤ i 支；逐字陈述见 DELIVERY §4）────
  │ `aq4_prevElMapRange (k) (f : ℕ → ℕ × ℕ) (hnd : ((range' 1 k).map f).Nodup)
  │    (hi1 : 2 ≤ i) (hi2 : i ≤ k) : prevEl ((range' 1 k).map f) (f i) = f (i-1)`
  │ 注：**必须保留 `hnd`（单射）与 `2 ≤ i`**——转述形（无单射、1 ≤ i）不真：
  │ i=1 时 prevEl 回绕到表尾 `f k`；无单射时 `idxOf` 取首现、其余点错位。
  │ HOL `PREV_EL_UPT` 原前提正是 `(!u v. MEM u .. /\ MEM v .. /\ f u = f v ==> u = v)`
  │ + `2 <= a` + `2 <= x`（AQ4.hl:262-266）。

  ┌─ E3 内核的 Lean 形式（AQ12/AQ13 复用要点）────────────────────
  │ HOL 131 行的 `prev_el_hd_flatten`（prevEl + 拼接 + LAST_FLATTEN_2）；
  │ Lean 改走**对偶形**：`nextEl blocks.flatten (last b) = head(next block)`
  │ 由 `nextElCatLast1` 直达（E3a，纯列表，20 行，不需要 prevEl 拼接族）。
  │ E3b 再乘两个恒等式：
  │   · `(ndSpine d0).head! = nList d0 = eList (prevEl (findFaceDarts L d0) d0)`
  │     ——`nList` **定义式**；
  │   · `(ndSpine dprev).getLast! = (nList)^(sz-1) dprev = nodeMap^(sz-1) dprev
  │      = nodeMap.symm dprev = fList (eList dprev)`
  │     ——`lastNdSpine` + `nListPowEqNodeMapPow` + `pow_card_node_apply_self`
  │     （幂回绕，`Equiv.symm_apply_apply` 收）+ `nodeMapSymmEqFList`。
  │ ⇒ E3 拆成两件各 ~20/25 行，远低于 80 行止损线。

  ┌─ 与 AQ12/AQ13 的复用面 ──────────────────────────────────────
  │ ①④⑤⑥ = contour / final_dart 走步的同构件（面内 step、块边界、块头尾）；
  │ ⑦ 的弧 prevEl 连续供 parts/弧走步；② 供任何 `range'` 幂表的 prevEl。

  ┌─ DIFFERS ────────────────────────────────────────────────────
  │ 1. 全部件公开（前缀 `aq4_`）；`aq4Concl` 槽冻结不动；不含 `aq4` 本体（W3）。
  │ 2. 未落 E4（`betwn_rev`，HOL #28）/ `rev_split_at`（#27）：本批路线不需反转弧。
  │ 3. `aq4_nextElBlockLast` 用 `Q.head!.head!` 形（W3 只需 `blocks = P ++ b :: Q`）。
  │ 4. 公理面：8 件全部 ⊆ `[propext, Classical.choice, Quot.sound]`。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf5
import Kepler.Text.TameSpine.JcajyduAqLeaf10

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-! ## §1 E5：面内 one-step（`fList` 定义式 + 面等价） -/

/-- **面内 one-step**：`x` 与锚点 `y` 同面 ⇒ `oneStep x (nextEl 面 x)`。
`fList L x` 的定义即 `nextEl (findFaceDarts L x) x`，面等价一折即得。 -/
theorem aq4_oneStepFindFace (L : fgraph ℕ) (hL : GoodList L) {x y : ℕ × ℕ}
    (hy : y ∈ listOfDarts L) (hx : x ∈ findFaceDarts L y) :
    oneStepListSpine L x (nextEl (findFaceDarts L y) x) := by
  have hface : findFaceDarts L x = findFaceDarts L y :=
    findFaceDarts_congr_of_mem hL.1 hy hx
  refine Or.inl ?_
  show nextEl (findFaceDarts L y) x = fList L x
  rw [← hface]
  rfl

/-! ## §2 E2 泛形：`range'` 幂表的前驱（跨车道接口件） -/

/-- **`range'` 映射表的前驱**（HOL `PREV_EL_UPT` + `prev_el_map_upt` 的合并形）：
`((range' 1 k).map f).Nodup`、`2 ≤ i ≤ k` ⇒ `prevEl ((range' 1 k).map f) (f i) = f (i-1)`。
`idxOf` 定位（`Nodup.idxOf_getElem` + `getElem_range'`）+ `prevEl_eq_getD_idxOf`
+ 模运算（`i-1 ≥ 1` 故不回绕）。**`hnd` 与 `2 ≤ i` 都是必需的**（见文件头）。 -/
theorem aq4_prevElMapRange {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    (k : ℕ) (f : ℕ → α)
    (hnd : ((List.range' 1 k).map f).Nodup)
    {i : ℕ} (hi1 : 2 ≤ i) (hi2 : i ≤ k) :
    prevEl ((List.range' 1 k).map f) (f i) = f (i - 1) := by
  have hmem : f i ∈ (List.range' 1 k).map f := by
    rw [List.mem_map]
    exact ⟨i, by rw [List.mem_range']; exact ⟨i - 1, by omega, by omega⟩, rfl⟩
  have hlen : ((List.range' 1 k).map f).length = k := by
    rw [List.length_map, List.length_range']
  have hpos : i - 1 < ((List.range' 1 k).map f).length := by omega
  have hget : ((List.range' 1 k).map f)[i - 1]'hpos = f i := by
    rw [List.getElem_map, List.getElem_range']
    show f (1 + 1 * (i - 1)) = f i
    rw [show 1 + 1 * (i - 1) = i from by omega]
  have hidx : ((List.range' 1 k).map f).idxOf (f i) = i - 1 := by
    rw [← hget]
    exact List.Nodup.idxOf_getElem hnd (i - 1) hpos
  have hmod : (i - 1 + ((List.range' 1 k).map f).length - 1)
      % ((List.range' 1 k).map f).length = i - 2 := by
    rw [hlen]
    have he : i - 1 + k - 1 = (i - 2) + k := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hpos2 : i - 2 < ((List.range' 1 k).map f).length := by omega
  rw [prevEl_eq_getD_idxOf hmem,
    Kepler.Text.TameLp.li_idxOf_congr ((List.range' 1 k).map f) (f i),
    hidx, hmod, getD_eq_getElem_of_lt hpos2]
  rw [List.getElem_map, List.getElem_range']
  show f (1 + 1 * (i - 2)) = f (i - 1)
  rw [show 1 + 1 * (i - 2) = i - 1 from by omega]

/-- **跨车道接口别名**（AQ8 `hE3` 一行代入用；与 `aq4_prevElMapRange` 同陈述）。
注：`hnd`（映射表单射）与 `2 ≤ i` 均不可去——见 DELIVERY §4 的机器反证。 -/
theorem aq4_prevElMapUpt {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    (k : ℕ) (f : ℕ → α)
    (hnd : ((List.range' 1 k).map f).Nodup)
    {i : ℕ} (hi1 : 2 ≤ i) (hi2 : i ≤ k) :
    prevEl ((List.range' 1 k).map f) (f i) = f (i - 1) :=
  aq4_prevElMapRange k f hnd hi1 hi2

/-! ## §3 E2 特化：块内前驱 -/

/-- **块内前驱 = 前一幂**（`aq4_prevElMapRange` 在 `f := (nList)^· d`、
`k := sz-1` 处的代入；`hnd` 由 `aq1_ndSpineNodup` 供）。 -/
theorem aq4_prevElNdSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {d : ℕ × ℕ}
    (hd : d ∈ (hypermapOfList L hL).darts)
    (h2 : 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length)
    {i : ℕ} (hi1 : 2 ≤ i)
    (hi2 : i ≤ (L.flatten.filter (fun t => decide (t = d.1))).length - 1) :
    prevEl (ndSpine L d) ((nList L)^[i] d) = (nList L)^[i - 1] d := by
  have hdef : ndSpine L d
      = (List.range' 1 ((List.filter (fun t => decide (t = d.1)) (List.flatten L)).length - 1)).map
          (fun j => (nList L)^[j] d) := rfl
  have hnd : ((List.range' 1 ((List.filter (fun t => decide (t = d.1))
      (List.flatten L)).length - 1)).map (fun j => (nList L)^[j] d)).Nodup := by
    rw [← hdef]
    exact aq1_ndSpineNodup L hL hgn hd h2
  rw [hdef]
  exact aq4_prevElMapRange _ (fun j => (nList L)^[j] d) hnd hi1 hi2

/-! ## §4 块头 + E3a：块边界（nextEl 形） -/

/-- `ndSpine` 块头 = `nList L d`（`range' 1 (sz-1)` 首元为 `1`）。 -/
theorem aq4_ndSpineHead (L : fgraph ℕ) {d : ℕ × ℕ}
    (h2 : 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length) :
    (ndSpine L d).head! = nList L d := by
  obtain ⟨k, hk⟩ : ∃ k,
      (List.filter (fun t => decide (t = d.1)) (List.flatten L)).length - 1 = k + 1 :=
    ⟨(List.filter (fun t => decide (t = d.1)) (List.flatten L)).length - 2, by omega⟩
  unfold ndSpine
  rw [hk]
  rfl

/-- **块边界（nextEl 形）**：`blocks = P ++ b :: Q`、`b ≠ []`、`Q` 各块非空 ⇒
`nextEl blocks.flatten b.getLast! = Q.head!.head!`
（HOL `prev_el_hd_flatten`（AQ4.hl:413-543，131 行）的对偶件）。 -/
theorem aq4_nextElBlockLast {blocks P Q : List (List (ℕ × ℕ))} {b : List (ℕ × ℕ)}
    (hnd : blocks.flatten.Nodup) (hblocks : blocks = P ++ b :: Q)
    (hb : b ≠ []) (hQ : Q ≠ []) (hne : ∀ x ∈ Q, x ≠ []) :
    nextEl blocks.flatten b.getLast! = Q.head!.head! := by
  have hdecomp : blocks.flatten = (P.flatten ++ b) ++ Q.flatten := by
    rw [hblocks]
    simp only [List.flatten_append, List.flatten_cons]
    rw [List.append_assoc]
  have hnd' : ((P.flatten ++ b) ++ Q.flatten).Nodup := hdecomp ▸ hnd
  have hsne : P.flatten ++ b ≠ [] := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil b hb
    exact List.ne_nil_of_mem (List.mem_append_right P.flatten hx)
  have htne : Q.flatten ≠ [] := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil Q hQ
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil c (hne c hc)
    exact List.ne_nil_of_mem (List.mem_flatten.mpr ⟨c, hc, hx⟩)
  rw [hdecomp, ← getLast!AppendRight P.flatten b hb,
    nextElCatLast1 hnd' hsne htne]
  obtain ⟨c, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ
  rw [List.flatten_cons, List.head!_append _ (hne c List.mem_cons_self)]
  rfl

/-! ## §5 单步桥 + E3b：块边界 one_step -/

/-- `nList = nodeMap` 的单步形（`nListPowEqNodeMapPow` 的 k=1 读数）。 -/
theorem aq4_nListEqNodeMap (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    nList L d = (hypermapOfList L hL).nodeMap d := by
  rw [← Function.iterate_one (nList L), nListPowEqNodeMapPow L hL hd 1, pow_one]

/-- **块边界 one_step**：`dprev = prevEl (findFaceDarts L d0) d0` 时，
`(ndSpine dprev).getLast!` 是 `(ndSpine d0).head!` 的合法后继（one_step 第一支）。
内核见文件头：`nList 定义式` × `nodeMap.symm`（幂回绕 + 单射）。 -/
theorem aq4_blockBoundaryStep (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {d0 dprev : ℕ × ℕ}
    (hd0 : d0 ∈ (hypermapOfList L hL).darts)
    (h2d0 : 2 ≤ (L.flatten.filter (fun t => decide (t = d0.1))).length)
    (hdp : dprev ∈ (hypermapOfList L hL).darts)
    (h2dp : 2 ≤ (L.flatten.filter (fun t => decide (t = dprev.1))).length)
    (hprev : prevEl (findFaceDarts L d0) d0 = dprev) :
    oneStepListSpine L ((ndSpine L d0).head!) ((ndSpine L dprev).getLast!) := by
  have hdpL : dprev ∈ listOfDarts L := List.mem_toFinset.mp hdp
  -- ① 块头 = nList d0 = eList dprev（nList 定义式）
  have hx : (ndSpine L d0).head! = eList dprev := by
    rw [aq4_ndSpineHead L h2d0]
    show eList (prevEl (findFaceDarts L d0) d0) = eList dprev
    rw [hprev]
  -- ② 块尾：幂回绕到 nodeMap.symm
  have hper : ((hypermapOfList L hL).nodeMap ^
      (List.filter (fun t => decide (t = dprev.1)) (List.flatten L)).length) dprev = dprev := by
    rw [szEqNodeCard L hL hgn hdp]
    exact Kepler.Text.Hypermap.pow_card_node_apply_self _ dprev
  have hperI : (nList L)^[(List.filter (fun t => decide (t = dprev.1))
      (List.flatten L)).length] dprev = dprev := by
    rw [nListPowEqNodeMapPow L hL hdpL]
    exact hper
  have hpowSymm : (nList L)^[(List.filter (fun t => decide (t = dprev.1))
        (List.flatten L)).length - 1] dprev
      = (hypermapOfList L hL).nodeMap.symm dprev := by
    have hyl : (nList L)^[(List.filter (fun t => decide (t = dprev.1))
        (List.flatten L)).length - 1] dprev ∈ listOfDarts L := by
      rw [nListPowEqNodeMapPow L hL hdpL]
      exact List.mem_toFinset.mp
        ((hypermapOfList L hL).nodeMap_permutes.pow_apply_mem
          ((List.filter (fun t => decide (t = dprev.1)) (List.flatten L)).length - 1) hdp)
    have hsucc : (nList L) ((nList L)^[(List.filter (fun t => decide (t = dprev.1))
        (List.flatten L)).length - 1] dprev) = dprev := by
      have hs : (List.filter (fun t => decide (t = dprev.1)) (List.flatten L)).length - 1 + 1
          = (List.filter (fun t => decide (t = dprev.1)) (List.flatten L)).length := by omega
      have h := hperI
      rw [← hs] at h
      rwa [Function.iterate_succ_apply'] at h
    rw [aq4_nListEqNodeMap L hL hyl] at hsucc
    have h2' := congrArg (hypermapOfList L hL).nodeMap.symm hsucc
    rwa [Equiv.symm_apply_apply] at h2'
  have hlast : (ndSpine L dprev).getLast! = fList L (eList dprev) := by
    rw [lastNdSpine L dprev h2dp, ← nodeMapSymmEqFList L hL hdp]
    exact hpowSymm
  refine Or.inl ?_
  rw [hx, hlast]

/-! ## §6 E1：弧 `prevEl` 连续 -/

/-- **弧 `prevEl` 连续**：`x ∈ betwn r y z` 且 `x` 不是弧头 ⇒
`prevEl (betwn r y z) x = prevEl r x`。
路线：`t := prevEl r x`；`indexfAddSum` + 反证支（`indexf y t = len-1`
⇒ `t` 是 `y` 前驱 ⇒ `x = y`，撞 `notBetwn1`）得 `indexf y t = indexf y x - 1`
⇒ `t` 在弧内；`aq10_nextElBetwnSame` 给 `nextEl 弧 t = x`，唯一性收口。 -/
theorem aq4_prevElBetwnOfNeHead {r : List (ℕ × ℕ)} {y z : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    {x : ℕ × ℕ} (hx : x ∈ between r y z) (hxhead : x ≠ (between r y z).head!) :
    prevEl (between r y z) x = prevEl r x := by
  have hxr : x ∈ r := betwnMem hx
  have hwnd : (between r y z).Nodup := uniqBetwn hrnd hy hz hne
  have hrlen : 1 < r.length := sizelGt1 hy hz hne
  have hwne : between r y z ≠ [] := List.ne_nil_of_mem hx
  have hhead : (between r y z).head! = nextEl r y := HD_BETWN2 hy hz hne hrnd hwne
  have hx1 : indexf y x r ≠ 1 := by
    intro h1
    exact hxhead (by rw [hhead]; exact (indexfOne hy hxr hrnd h1).symm)
  have hxB := (indexfBetwnEq hne hrnd hy hz).mp hx
  have hx0 : 0 < indexf y x r := hxB.1
  have hx2 : 2 ≤ indexf y x r := by omega
  have hxz : indexf y x r < indexf y z r := hxB.2
  set t := prevEl r x with ht
  have htr : t ∈ r := prevEl_mem_of_mem hxr
  have hnext : nextEl r t = x := nextElPrevElUniq hrnd x
  have htx : indexf t x r = 1 := nextElIndexf htr hxr hrnd hnext hrlen
  have hidx : indexf y t r = indexf y x r - 1 := by
    rcases Nat.lt_or_ge (indexf y t r + indexf t x r) r.length with h | h
    · have := indexfAddSum hy htr hxr h
      omega
    · exfalso
      have hlt : indexf y t r < r.length := indexfLtSizel hy htr
      have hgt : indexf y t r = r.length - 1 := by omega
      have hty : indexf t y r = 1 := by
        have hanti := indexfAntisym htr hy (by
          intro hty
          rw [hty, indexfRefl hy] at hgt
          omega)
        omega
      have hyx : nextEl r t = y := indexfOne htr hy hrnd hty
      rw [hnext] at hyx
      exact notBetwn1 hrnd hz (hyx.symm ▸ hx)
  have ht0 : 0 < indexf y t r := by omega
  have htz : indexf y t r < indexf y z r := by omega
  have htw : t ∈ between r y z := (indexfBetwnEq hne hrnd hy hz).mpr ⟨ht0, htz⟩
  have hnextmem : nextEl r t ∈ between r y z := by rw [hnext]; exact hx
  have hnextw : nextEl (between r y z) t = x := by
    have hcont := aq10_nextElBetwnSame hne hy hz htw hnextmem hrnd
    rw [hcont, hnext]
  have hfin : prevEl (between r y z) x = t := by
    have h := Kepler.Text.TameLp.prevEl_nextEl hwnd htw
    rwa [hnextw] at h
  exact hfin

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq4_oneStepFindFace
#print axioms Kepler.Text.TameSpine.aq4_prevElMapRange
#print axioms Kepler.Text.TameSpine.aq4_prevElMapUpt
#print axioms Kepler.Text.TameSpine.aq4_prevElNdSpine
#print axioms Kepler.Text.TameSpine.aq4_ndSpineHead
#print axioms Kepler.Text.TameSpine.aq4_nextElBlockLast
#print axioms Kepler.Text.TameSpine.aq4_nListEqNodeMap
#print axioms Kepler.Text.TameSpine.aq4_blockBoundaryStep
#print axioms Kepler.Text.TameSpine.aq4_prevElBetwnOfNeHead
