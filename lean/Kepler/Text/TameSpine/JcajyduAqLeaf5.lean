/-
  Kepler.Text.TameSpine.JcajyduAqLeaf5 — AQ5 叶：`aq5Concl`（normal_list 合取 5，
  node 闭包）。

  目标（`JcajyduAqTowerBase.lean:255` `aq5Concl`，**陈述冻结**）：
  `∀ d ∈ (ntransSpine L N r x 1).flatten,
     (hypermapOfList L hL).node d ⊆ {d' | d' ∈ (ntransSpine L N r x 1).flatten}`
  = HOL `AQ5_concl`（AQ56.hl:129-:135）。

  ┌─ 路线（HOL 606 行 → Lean 的模型）─────────────────────────────
  │ AQ56.hl 里属 AQ5 的声明：`AQ5_concl`+`AQ5`（129-646，518 行）、
  │ `case_hd_betwn_last`（46-127，82 行，仅 AQ5 消费）、`TL_LAST`
  │ （39-44，6 行，**全文件零消费**）。AQ6 块（648-702）已落 `aq6`
  │ （TowerBase:353），本文件不重复。
  │ 三条结构性折算：
  │  (a) HOL 全程的 `replace`-filter 刻画 ↦ `aq1b_flattenNtrans1` 的切口形；
  │  (b) `case_hd_betwn_last`（head/middle/last 三分）**整件不需要**：
  │      本树 `aq1e_betwnSubset : betwn r y z ⊆ f1` 一条 set 级包含直达；
  │  (c) 窗口支的 `upt`/下标界（HOL 用 `dart_of_card_node`/`count_node_face`/
  │      `MEM_EQ_UPT` 数十行）↦ 本文件 §1 的**模周期** node 轨道分解
  │      `node x ⊆ {x} ∪ ndSpine x`（`pow_card_node_apply_self` + `mem_range'`）。
  │ 主证结构：final 支 2 行（`ntransId` + 旧 `NormalListSpine` node 闭包）；
  │ ¬final 支 = 旧表转移（§3）+ 六路成员拆分（旧 4 路 + 窗口 2 路）。

  ┌─ §1 `aq5_nodeCoverSelfNdSpine`（公开件，供 AQ12/AQ13 复用）────────
  │ `x ∈ darts ⇒ node x ⊆ {y | y = x ∨ y ∈ ndSpine L x}`。
  │ **证明梗概（模周期）**：设 `Nc := (node x).ncard`、`sz := filter 长`
  │ （`szEqNodeCard` 给 `sz = Nc`，`Set.ncard_pos` + `mem_orbitMap_self`
  │ 给 `Nc > 0`）。任取 `y ∈ node x`，`mem_node_iff` 给 `y = nodeMap^n x`：
  │   ① `hstep : (nList L)^[Nc] x = x`（`nListPowEqNodeMapPow` +
  │      `pow_card_node_apply_self`）；
  │   ② `hmult : (nList L)^[Nc * k] x = x`（对 k 归纳，`iterate_add_apply`）；
  │   ③ `hred : (nList L)^[n] x = (nList L)^[n % Nc] x`
  │      （`Nat.mod_add_div` + `iterate_add_apply` + `hmult`）；
  │   ④ `n % Nc = 0 ⇒ y = x`；否则 `r := n % Nc ∈ [1, Nc-1] = [1, sz-1]`，
  │      而 `ndSpine L x = (range' 1 (sz-1)).map (fun i => (nList L)^[i] x)`
  │      ⇒ `y = (nList L)^[r] x` 是第 `r` 个块元（`List.mem_range'` 的
  │      `∃ i < n, m = s + step*i` 形，取 i = r-1）。
  │ 若日后要 ndSpine 的**满轨道**形（含 `x` 自身），只需把 ④ 的 `r = 0`
  │ 支也塞进 `range'`（HOL 的 `upt 1 sz` 双闭形），本引理不用改。

  ┌─ §2-§3 中间件（均公开，宽前提）──────────────────────────────
  │ ② `aq5_rCover`：`r ⊆ f1 ∪ f2`（`betwnCases` 四支 + `aq1e_betwnSubset`）。
  │ ③ `aq5_oldSubNew`：`N = N₁ ++ r :: N₂` 且 `r ⊆ s2 ∪ s1` ⇒
  │    `N.flatten ⊆ ((N₁.flatten ++ s2) ++ N₂.flatten) ++ s1`（旧表 ⊆ 新表）。
  │ ④ `aq5_windowNode`：窗口两式——`new2` 的 node 闭包与
  │    `(new2.map ndSpine).flatten` 的 node 闭包都落到目标表 `Nfl`，
  │    前提仅为「窗口 dart ∈ darts / ∈ Nfl / 其 ndSpine 块 ⊆ Nfl」。

  ┌─ DIFFERS（相对 HOL 的记账）───────────────────────────────────
  │ 1. 未落 `TL_LAST`（HOL 死件，零消费）与 `case_hd_betwn_last`
  │    （被 `aq1e_betwnSubset` 取代，见路线 (b)）。
  │ 2. §1/§4 为**新公开件**（HOL 无对应；§1 是通用 node 轨道分解，
  │    §4 是窗口闭包的抽象形），陈述比 HOL 的 inline 论证更宽、零收窄。
  │ 3. 载体：`hL : GoodList L` / `hgn : GoodListNodesTl L hL` 显式入参；
  │    `aq5Concl` 槽冻结不动，主件名 `aq5`。
  │ 4. `hunL` 由 `simpleHypermapUniq` 现取（`aq5Concl` 无该槽，同 aq1/aq3）。
  │ 5. 公理面：5 件全部 ⊆ `[propext, Classical.choice, Quot.sound]`。

  ┌─ 边界 ────────────────────────────────────────────────────────
  │ 本叶自包含（import 仅 `JcajyduAqLeaf1F`）；下游 = `transformAssumptionOfAq`
  │ （TowerBase:329）第 5 槽。§1 预期被 AQ12/AQ13 的 node 结构复用。
  └──────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf1F

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem)

/-! ## §1 通用 node 轨道分解：`node x ⊆ {x} ∪ ndSpine x` -/

/-- **node 轨道分解**（新公开件，AQ12/AQ13 可复用）：`x` 是 dart 时，
`node x` 的每个元素要么是 `x` 自身，要么落在 `ndSpine L x`
（= `nList L` 的 1..sz-1 次幂；`sz = filter 长 = node 基数`）。
证明=模周期：`nodeMap^Nc x = x`（`pow_card_node_apply_self`），
把指数压到 `n % Nc`，非零支用 `mem_range'` 落块。**不需要 IsRestricted**。 -/
theorem aq5_nodeCoverSelfNdSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {x : ℕ × ℕ}
    (hx : x ∈ (hypermapOfList L hL).darts) :
    (hypermapOfList L hL).node x ⊆ {y | y = x ∨ y ∈ ndSpine L x} := by
  have hxL : x ∈ listOfDarts L := List.mem_toFinset.mp hx
  have hsz : (L.flatten.filter (fun t => decide (t = x.1))).length
      = ((hypermapOfList L hL).node x).ncard := szEqNodeCard L hL hgn hx
  have hNc : 0 < ((hypermapOfList L hL).node x).ncard := by
    show 0 < (Kepler.Text.orbitMap (hypermapOfList L hL).nodeMap x).ncard
    rw [Set.ncard_pos
      (Kepler.Text.orbitMap_finite (hypermapOfList L hL).nodeMap_permutes x)]
    exact ⟨x, Kepler.Text.mem_orbitMap_self _ x⟩
  have hstep : (nList L)^[((hypermapOfList L hL).node x).ncard] x = x := by
    rw [nListPowEqNodeMapPow L hL hxL]
    exact Kepler.Text.Hypermap.pow_card_node_apply_self _ x
  have hmult : ∀ k : ℕ,
      (nList L)^[((hypermapOfList L hL).node x).ncard * k] x = x := by
    intro k
    induction k with
    | zero => rw [Nat.mul_zero, Function.iterate_zero_apply]
    | succ k ih => rw [Nat.mul_succ, Function.iterate_add_apply, hstep, ih]
  intro y hy
  rw [Kepler.Text.Hypermap.mem_node_iff] at hy
  obtain ⟨n, rfl⟩ := hy
  have hred : (nList L)^[n] x
      = (nList L)^[n % ((hypermapOfList L hL).node x).ncard] x := by
    conv_lhs => rw [← Nat.mod_add_div n ((hypermapOfList L hL).node x).ncard]
    rw [Function.iterate_add_apply, hmult]
  rw [← nListPowEqNodeMapPow L hL hxL n, hred]
  by_cases hr : n % ((hypermapOfList L hL).node x).ncard = 0
  · exact Or.inl (by rw [hr, Function.iterate_zero_apply])
  · right
    have hpos : 0 < n % ((hypermapOfList L hL).node x).ncard := Nat.pos_of_ne_zero hr
    have hlt : n % ((hypermapOfList L hL).node x).ncard
        < ((hypermapOfList L hL).node x).ncard := Nat.mod_lt _ hNc
    rw [ndSpine, List.mem_map]
    refine ⟨n % ((hypermapOfList L hL).node x).ncard, ?_, rfl⟩
    rw [List.mem_range']
    exact ⟨n % ((hypermapOfList L hL).node x).ncard - 1, by omega, by omega⟩

/-! ## §2 `r ⊆ f1 ∪ f2`（split 的两段覆盖旧环 `r`） -/

/-- **`r` 被 split 两段覆盖**：`f1 = [y1] ++ betwn r y1 z1 ++ [z1]`、
`f2 = [z] ++ betwn r z y ++ [y]` 的并集含整个 `r`。
`betwnCases` 四支：`y`/`z` 落 `f2` 端点，`betwn r y z` 由
`aq1e_betwnSubset` 落 `f1`，`betwn r z y` 落 `f2` 中段。 -/
theorem aq5_rCover {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hne : y ≠ z)
    (hz1r : z1 ∈ r) (hnext : nextEl r z1 = z) (hra : nextEl r y ≠ z1) :
    ∀ x ∈ r, x ∈ ([nextEl r y] ++ between r (nextEl r y) z1) ++ [z1]
      ∨ x ∈ ([z] ++ between r z y) ++ [y] := by
  intro x hx
  rcases betwnCases hne hrnd hy hx hz with h | h | h | h
  · rw [h] at hx ⊢
    exact Or.inr (List.mem_append_right ([z] ++ between r z y) (List.mem_singleton_self y))
  · rw [h] at hx ⊢
    exact Or.inr (List.mem_append_left [y]
      (List.mem_append_left (between r z y) (List.mem_singleton_self z)))
  · exact Or.inl (aq1e_betwnSubset hrnd hy hz hz1r hnext hra x h)
  · exact Or.inr (List.mem_append_left [y] (List.mem_append_right [z] h))

/-! ## §3 旧表 ⊆ 新表（`N = N₁ ++ r :: N₂` 的切口形） -/

/-- **旧 flatten ⊆ 新 flatten**：`N = N₁ ++ r :: N₂` 且 `r ⊆ s2 ∪ s1` ⇒
`N.flatten ⊆ ((N₁.flatten ++ s2) ++ N₂.flatten) ++ s1`。
（`aq1b_flattenNtrans1` 的切口形的集合内核，逐层显式 `l₂`。） -/
theorem aq5_oldSubNew {N N₁ N₂ : List (List (ℕ × ℕ))} {r s1 s2 : List (ℕ × ℕ)}
    (hN : N = N₁ ++ r :: N₂) (hr : ∀ x ∈ r, x ∈ s2 ∨ x ∈ s1) :
    ∀ d ∈ N.flatten, d ∈ ((N₁.flatten ++ s2) ++ N₂.flatten) ++ s1 := by
  intro d hd
  rw [hN, List.flatten_append, List.flatten_cons] at hd
  rcases List.mem_append.mp hd with h1 | h1
  · exact List.mem_append_left s1
      (List.mem_append_left N₂.flatten (List.mem_append_left s2 h1))
  · rcases List.mem_append.mp h1 with h2 | h2
    · rcases hr d h2 with h3 | h3
      · exact List.mem_append_left s1
          (List.mem_append_left N₂.flatten (List.mem_append_right N₁.flatten h3))
      · exact List.mem_append_right (N₁.flatten ++ s2 ++ N₂.flatten) h3
    · exact List.mem_append_left s1 (List.mem_append_right (N₁.flatten ++ s2) h2)

/-! ## §4 窗口两式：`new2` 与 `(new2.map ndSpine).flatten` 的 node 闭包 -/

/-- **窗口两式**（`new2` = 面窗；`ndSpine` 块 = node 轨道减自身）：
若 `new2` 的 dart 都在 darts、都在目标表 `Nfl`，且每个 `ndSpine` 块 ⊆ `Nfl`，
则（i）`new2` 的 node 闭包、（ii）`(new2.map (ndSpine L)).flatten` 的 node
闭包都落到 `Nfl`。核心是 §1 的轨道分解：
`node d ⊆ {d} ∪ ndSpine d`（d ∈ new2）与
`d ∈ ndSpine x0 ⇒ node d = node x0`（`node_eq_of_mem` + 幂成员）。 -/
theorem aq5_windowNode (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {new2 Nfl : List (ℕ × ℕ)}
    (hsub : ∀ d ∈ new2, d ∈ (hypermapOfList L hL).darts)
    (hin : ∀ d ∈ new2, d ∈ Nfl)
    (hblk : ∀ x0 ∈ new2, ∀ y ∈ ndSpine L x0, y ∈ Nfl) :
    (∀ d ∈ new2, (hypermapOfList L hL).node d ⊆ {d' | d' ∈ Nfl}) ∧
      (∀ d ∈ (new2.map (ndSpine L)).flatten,
        (hypermapOfList L hL).node d ⊆ {d' | d' ∈ Nfl}) := by
  constructor
  · intro d hd y hy
    have hcov := aq5_nodeCoverSelfNdSpine L hL hgn (hsub d hd)
    rcases hcov hy with heq | hmem
    · exact heq ▸ hin d hd
    · exact hblk d hd y hmem
  · intro d hd y hy
    obtain ⟨blk, hblk_mem, hdblk⟩ := List.mem_flatten.mp hd
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hblk_mem
    obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hdblk
    have hx0d : x0 ∈ (hypermapOfList L hL).darts := hsub x0 hx0
    have hx0L : x0 ∈ listOfDarts L := List.mem_toFinset.mp hx0d
    have hpow : (nList L)^[i] x0 ∈ (hypermapOfList L hL).node x0 := by
      rw [nListPowEqNodeMapPow L hL hx0L]
      exact (hypermapOfList L hL).pow_nodeMap_mem_node _ i
    have hnodeq : (hypermapOfList L hL).node ((nList L)^[i] x0)
        = (hypermapOfList L hL).node x0 :=
      (Kepler.Text.Hypermap.node_eq_of_mem _ hpow).symm
    rw [hnodeq] at hy
    have hcov := aq5_nodeCoverSelfNdSpine L hL hgn hx0d
    rcases hcov hy with heq | hmem
    · exact heq ▸ hin x0 hx0
    · exact hblk x0 hx0 y hmem

/-! ## §5 `AQ5_concl` 主证 -/

/-- **HOL `AQ5_concl`**（AQ56.hl:129-:135）真证：node 闭包。
final 支 `ntransId` + 旧 `NormalListSpine` 的 node 闭包；¬final 支用
`aq1b_flattenNtrans1` 的切口形，六路成员拆分（旧 4 路 = §3 转移，
窗口 2 路 = §4 窗口两式）。 -/
theorem aq5 (L : fgraph ℕ) (hL : GoodList L) : aq5Concl L hL := by
  intro N r x hgn hm
  have hunL : ∀ l ∈ L, l.Nodup := (simpleHypermapUniq L hL hgn).mp hm.1.1.simple
  by_cases hfin : finalListSpine L r
  · rw [ntransId L N r x hfin]
    exact hm.1.2.1.2.2.2.2
  · obtain ⟨N₁, N₂, hN, _hnot, hflat⟩ :=
      aq1b_flattenNtrans1 L hL hgn hunL hm hfin
    rw [hflat]
    have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
    have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hfin
    have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hfin
    have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hfin
    have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
    have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
      nextElPrevElUniq hrnd _
    have hra : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
      aq1_nextElYNePrevElZ L hL hgn hunL hm hfin
    have hy1z : nextEl r (lYSpine L r x) ≠ lZSpine L N r x := by
      intro h
      exact aq1_nextElYNeZ L hL hgn hunL hm hfin h
    -- `s1` / `s2` 的分段展开
    have hs1eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
        = (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
          ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
              (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
      rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x)), hnextz1]
    have hs2eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2
        = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
            ++ [lYSpine L r x])
          ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x) := by
      simp only [splitNormalListSpine]
      rw [hnextz1]
    -- 旧环覆盖
    have hrcover : ∀ d ∈ r, d ∈ (splitNormalListSpine L r
          (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).2
        ∨ d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
      intro d hd
      rcases aq5_rCover hrnd hyr hzr hyne hz1r hnextz1 hra d hd with h | h
      · exact Or.inr (by rw [hs1eq]; exact List.mem_append_right _ h)
      · exact Or.inl (by rw [hs2eq]; exact List.mem_append_left _ h)
    -- 旧表 ⊆ 新表
    have hold : ∀ d ∈ N.flatten,
        d ∈ ((N₁.flatten ++ (splitNormalListSpine L r (findFaceDarts L
              (lYSpine L r x)) (lYSpine L r x) (prevEl r (lZSpine L N r x))).2)
          ++ N₂.flatten)
          ++ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 :=
      aq5_oldSubNew hN hrcover
    have holdNode : ∀ d ∈ N.flatten, (hypermapOfList L hL).node d ⊆
        {d' | d' ∈ ((N₁.flatten ++ (splitNormalListSpine L r
            (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (prevEl r (lZSpine L N r x))).2) ++ N₂.flatten)
          ++ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (prevEl r (lZSpine L N r x))).1} := by
      intro d hd
      exact fun y hy => hold y (hm.1.2.1.2.2.2.2 d hd hy)
    -- 旧表成员（四个旧侧 case 共用）
    have hN1sub : ∀ d ∈ N₁.flatten, d ∈ N.flatten := by
      intro d hd
      obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd
      exact List.mem_flatten.mpr ⟨l, by rw [hN]; exact List.mem_append_left _ hl, hdl⟩
    have hN2sub : ∀ d ∈ N₂.flatten, d ∈ N.flatten := by
      intro d hd
      obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd
      exact List.mem_flatten.mpr
        ⟨l, by rw [hN]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hl), hdl⟩
    -- 窗口两式
    have hwinSub : ∀ d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x), d ∈ (hypermapOfList L hL).darts :=
      fun d hd => List.mem_toFinset.mpr
        (mem_darts_of_mem_findFace L (memBetweenOfMem hd))
    have hwinIn : ∀ d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x), d ∈ ((N₁.flatten ++ (splitNormalListSpine L r
            (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (prevEl r (lZSpine L N r x))).2) ++ N₂.flatten)
          ++ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
      intro d hd
      have hdS2 : d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
        rw [hs2eq]
        exact List.mem_append_right ([lZSpine L N r x] ++ between r (lZSpine L N r x)
          (lYSpine L r x) ++ [lYSpine L r x]) hd
      exact List.mem_append_left _ (List.mem_append_left N₂.flatten
        (List.mem_append_right N₁.flatten hdS2))
    have hwinBlk : ∀ x0 ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x), ∀ y ∈ ndSpine L x0,
        y ∈ ((N₁.flatten ++ (splitNormalListSpine L r
            (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (prevEl r (lZSpine L N r x))).2) ++ N₂.flatten)
          ++ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
      intro x0 hx0 y hy
      have hyS1 : y ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
        rw [hs1eq]
        exact List.mem_append_left _
          (List.mem_reverse.mpr (List.mem_flatten.mpr
            ⟨ndSpine L x0, List.mem_map.mpr ⟨x0, hx0, rfl⟩, hy⟩))
      exact List.mem_append_right _ hyS1
    obtain ⟨hnew2Node, hnew1Node⟩ :=
      aq5_windowNode L hL hgn hwinSub hwinIn hwinBlk
    -- 六路成员拆分（逐层显式 l₂）
    intro d hd
    rcases List.mem_append.mp hd with hA | hA
    · rcases List.mem_append.mp hA with hB | hB
      · rcases List.mem_append.mp hB with hC | hC
        · exact holdNode d (hN1sub d hC)
        · rw [hs2eq] at hC
          rcases List.mem_append.mp hC with hD | hD
          · exact holdNode d (List.mem_flatten.mpr ⟨r, hm.1.2.2.1,
              aq1c_f2SubR hyr hzr hD⟩)
          · exact hnew2Node d hD
      · exact holdNode d (hN2sub d hB)
    · rw [hs1eq] at hA
      rcases List.mem_append.mp hA with hD | hD
      · exact hnew1Node d (List.mem_reverse.mp hD)
      · exact holdNode d (List.mem_flatten.mpr ⟨r, hm.1.2.2.1,
          memBetweenOfMem (aq1f_f1SubBetwn hrnd hyr hzr hyne hz1r hnextz1
            hy1z hra d hD)⟩)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq5_nodeCoverSelfNdSpine
#print axioms Kepler.Text.TameSpine.aq5_rCover
#print axioms Kepler.Text.TameSpine.aq5_oldSubNew
#print axioms Kepler.Text.TameSpine.aq5_windowNode
#print axioms Kepler.Text.TameSpine.aq5
