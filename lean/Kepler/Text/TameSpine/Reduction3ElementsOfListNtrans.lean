/-
  Kepler.Text.TameSpine.Reduction3ElementsOfListNtrans — W2-件1 本体：
  HOL `elements_of_list_ntrans`（reduction2.hl:1042-1136）的 Lean 移植。

  ┌─ 陈述对表（HOL → Lean）──────────────────────────────────────
  │ `r_rtrans_eq L N r x`            ↦ `rRtransEq L N r x`（Reduction5Base
  │                                    :249 def；本件携带，件1a 消费）
  │ `transform_assumption_v2 L`      ↦ （HOL 源内已注释；ta 由
  │                                    `transformAssumptionSpine_top` 在
  │                                    `aqiunpp1_top` 内联吸收）
  │ `is_restricted (hypermap_of_list L)` ↦ `hm.1.1`（MarkedListSpineFull
  │                                    合取 1，不出独立前提槽）
  │ `good_list L` / `good_list_nodes L` ↦ `hL` / `hgn`
  │ `marked_list L N r x`            ↦ `MarkedListSpineFull hL N r x`
  │                                    （TameList13:268，9 合取全量）
  │ `newvertex_prepped L N r x`      ↦ `newvertexPrepped L N r x`
  │                                    （Reduction3DefsNewVertex:78；本件
  │                                    携带，件1a 消费）
  │ 旧 quotient 前提 `elements_of_list (quotient_list L N) =
  │   0..PRE(sizel (undup (MAP FST (flatten N))))`
  │                                  ↦ `hold`（Thm13B ⑤ 折算：
  │                                    `0..PRE n ↦ {i | i ≤ n-1}`）
  │ 结论 `elements_of_list (quotient_list L (ntrans … 1)) =
  │   0..PRE(sizel (undup (MAP FST (flatten (ntrans … 1)))))`
  │                                  ↦ 目标等式（`quotient_list` 经
  │                                    ChainBridge 折算）
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（对 HOL 1042-1136 的唯一偏离；语义边界如实记档）──────
  │ HOL 证明在 1085-1089 有内部切口 ENOUGH_TO_SHOW：
  │   `?k. n ≤ k ∧ set_of_list (MAP FST (filter (¬MEM r) r')) = n..k`
  │ （r' = rtrans L N r x 1，n = sizel (undup (MAP FST (flatten N)))）。
  │ 该切口在 HOL 内由 face_diff_r（reduction2.hl:843-1040，约 200 行）
  │ + newvertex_alt（reduction2.hl:620-660，约 40 行）+ take_size_cat/
  │ take_iota 数算闭合；两件在 Lean 树内零移植（grep 实测），独立移植
  │ 估 150-250 行（件1a，见 DELIVERY_W2_ITEM1_BOUNDARY §2）。本件把
  │ 该切口原样提为显式前提 `hbridge`（与 HOL 切口同形同弱），其余全链
  │ 真证：
  │   ① final 支 `ntrans_id` 折回 N，结论即旧前提（HOL 1069-1070）；
  │   ② LEBHIRJ（LEBHIRJ.hl:102 set(fn') = set(fn) ∪ set(v)）——树内
  │      零移植，本件首次组装：`aq1b_flattenNtrans1`（flatten 切口形）
  │      + `ndSpineFstEq`（块 FST = 首 FST）+ `betwnNotInRtrans`
  │      （窗口 dart 不在 r）+ `rtransCat`（窗口 ⊆ r'）+ `aq6`
  │      （r' ∈ ntrans 1）+ TameList72 双弧覆盖（HOL 1103 一带，
  │      在 `(prevEl r z, y)` 处实例化：`next_el r (prev_el r z) = z`
  │      重写后两弧恰为 S 头段 `[z]++betwn r z y++[y]` 与 F 尾段
  │      `[y₁]++betwn r y₁ z₁++[z₁]`，零 shift 件）；
  │   ③ `quotient_list_elements` 段 = `quotientListElements` +
  │      `aqiunpp1_top`（HOL 1065-1084 的 GMATCH_SIMP + AQIUNPP1）；
  │   ④ 区间合并 + dedup 计数收口（HOL 1090-1101 的 EXTENSION/ARITH；
  │      l=0 支由区间形 {n..k} 自动吸收，无需单独反证）。
  │ `rRtransEq`/`newvertexPrepped` 为 HOL 前提，本件原样携带（其消费
  │ 点在件1a：闭合 hbridge 时使用），不参与本件证明。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；主仓 tracked 零改动（patch
  │ 交付）；车道 /tmp/aq13-survey-w2/；基线 fde99ddd（87d768e8 仅
  │ docs 增量）。既有树内陈述零改动。工具链实测：本环境 omega 在
  │ Nat.sub 出现于假设或 ↔/→ 连接词内时失灵（mini 复现记档），n-1
  │ 数算统一走 `leSubOneIff` 私件（无 omega 依赖）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduTowerConsumers
import Kepler.Text.TameSpine.TameList35
import Kepler.Text.TameSpine.TameList72
import Kepler.Text.TameSpine.JcajyduAqTowerBase
import Kepler.Text.TameSpine.JcajyduAqLeaf1
import Kepler.Text.TameSpine.JcajyduAqLeaf1B
import Kepler.Text.TameSpine.JcajyduAqSnd
import Kepler.Text.TameSpine.JcajyduAqSplit1D
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsNewVertex
import Kepler.Text.Reduction5Base

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts)
open Kepler.Text.TameLp (elementsOfList GoodListNodesTl nextEl_mem_of_mem
  prevEl_mem_of_mem hypermapOfList darts_hypermapOfList
  mem_darts_of_mem_findFace)

/-- `1 ≤ b → (a ≤ b - 1 ↔ a < b)`（本环境 omega 对假设/↔ 内的 Nat.sub
失灵，数算统一走本桥；无 omega 依赖）。 -/
private theorem leSubOneIff {a b : ℕ} (hb : 1 ≤ b) : a ≤ b - 1 ↔ a < b := by
  rcases b with _ | c
  · exact absurd hb (by simp)
  · show a ≤ c ↔ a < c + 1
    exact Nat.lt_succ_iff.symm

/-- `rtransSpine L N r x 1 = split.2`（¬final；HOL `rtrans_cat` 证明内
`transform_list`/`POWER 1` 展开的独立化——JcajyduRed2Trans.rtransCat
的 `hstep` 中间件提为公开私件）。 -/
private theorem rtransSpineEqSplit2 (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (hf : ¬finalListSpine L r) :
    rtransSpine L N r x 1 = (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
  show ((transformListSpine L x)^[1] (N, r)).2 = _
  rw [Function.iterate_one]
  simp only [transformListSpine, if_neg hf]

/-- **HOL `elements_of_list_ntrans`**（reduction2.hl:1042-1136）：
旧 quotient 顶点集为 `0..PRE(n)` 时，单步变换后新 quotient 顶点集为
`0..PRE(n')`。ta 前提已由 `aqiunpp1_top` 内联；件1a 桥件（HOL 内部
`ENOUGH_TO_SHOW` 切口，1085-1089）以 `hbridge` 显式承载，见模块头
DIFFERS 记档。 -/
theorem elementsOfListNtrans
    (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hrre : Kepler.Text.Reduction5.rRtransEq L N r x)
    (hm : MarkedListSpineFull hL N r x)
    (hnvp : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hold : elementsOfList (Kepler.Text.Reduction5.quotientList L N)
      = {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1})
    (hbridge : ∃ k : ℕ, (N.flatten.map (fun d => d.1)).dedup.length ≤ k ∧
      setOfListNatSpine
        (((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1))
        = {i : ℕ | (N.flatten.map (fun d => d.1)).dedup.length ≤ i ∧ i ≤ k}) :
    elementsOfList (Kepler.Text.Reduction5.quotientList L (ntransSpine L N r x 1))
      = {i : ℕ | i ≤ ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length
        - 1} := by
  by_cases hfin : finalListSpine L r
  · -- ① final 支：`ntrans_id` 折回 N，结论即旧前提（HOL 1069-1070）
    rw [ntransId L N r x hfin]
    exact hold
  · -- ② ¬final 支（HOL 1071-1136）
    obtain ⟨k, hnle, hint⟩ := hbridge
    -- 环境派生（hunL/r.Nodup 沿 aq1 同款；NormalListSpine 两件）
    have hunL : ∀ l ∈ L, l.Nodup := (simpleHypermapUniq L hL hgn).mp hm.1.1.simple
    have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
    have hnspN : NormalListSpine hL N := hm.1.2.1
    have hnsp' : NormalListSpine hL (ntransSpine L N r x 1) := aqiunpp1_top L hL hgn hm
    -- ③ quotient_list_elements 段（HOL 1065-1084）
    have hEs : elementsOfList (quotientListSpine L N)
        = setOfListNatSpine (N.flatten.map (fun d => d.1)) :=
      quotientListElements L hL hnspN
    have hEs' : elementsOfList (quotientListSpine L (ntransSpine L N r x 1))
        = setOfListNatSpine ((ntransSpine L N r x 1).flatten.map (fun d => d.1)) :=
      quotientListElements L hL hnsp'
    -- n ≥ 1（marked 给 x ∈ r ⊆ flatten N ⇒ fn ≠ []）
    have hn1 : 1 ≤ (N.flatten.map (fun d => d.1)).dedup.length := by
      by_contra h0
      have h0' : (N.flatten.map (fun d => d.1)).dedup.length = 0 := by omega
      have hd0 : (N.flatten.map (fun d => d.1)).dedup = [] :=
        List.length_eq_zero_iff.mp h0'
      have hfe : N.flatten.map (fun d => d.1) = [] := (List.dedup_eq_nil _).mp hd0
      have hxfn : x.1 ∈ N.flatten.map (fun d => d.1) :=
        List.mem_map.mpr ⟨x, List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩, rfl⟩
      exact absurd hxfn (by rw [hfe]; simp)
    -- 旧前提点态化：i ∈ fn ↔ i < n（fn = N.flatten.map FST）
    have hOLDp : ∀ i : ℕ, i ∈ N.flatten.map (fun d => d.1) ↔
        i < (N.flatten.map (fun d => d.1)).dedup.length := by
      intro i
      have h1 : elementsOfList (Kepler.Text.Reduction5.quotientList L N)
          = setOfListNatSpine (N.flatten.map (fun d => d.1)) := by
        rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]; exact hEs
      have h2 := hold
      rw [h1] at h2
      have hi := congrArg (fun S : Set ℕ => i ∈ S) h2
      have hraw : i ∈ N.flatten.map (fun d => d.1) ↔
          i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1 := by
        simpa [setOfListNatSpine, Set.mem_setOf_eq] using hi
      exact hraw.trans (leSubOneIff hn1)
    -- 桥件点态化：i ∈ v ↔ n ≤ i ∧ i ≤ k（v = MAP FST (filter (·∉r) r')）
    have hvIff : ∀ i : ℕ, i ∈
        ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map (fun d => d.1) ↔
        (N.flatten.map (fun d => d.1)).dedup.length ≤ i ∧ i ≤ k := by
      intro i
      have hi := congrArg (fun S : Set ℕ => i ∈ S) hint
      simpa [setOfListNatSpine, Set.mem_setOf_eq] using hi
    -- 结构量：y/z/y1/z1、r' 的 cat 形
    have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hfin
    have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hfin
    have hy1 : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hy
    have hz1 : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hz
    have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
      nextElPrevElUniq hrnd _
    have hcat : rtransSpine L N r x 1
        = ((([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x))
            ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (lZSpine L N r x)) :=
      rtransCat L N r x hfin hrnd
    -- ② LEBHIRJ（HOL 1103 一带；树内零移植，本件首次组装）
    obtain ⟨N₁, N₂, hN, hnot, hflat⟩ := aq1b_flattenNtrans1 L hL hgn hunL hm hfin
    have hNflat : N.flatten = N₁.flatten ++ (r ++ N₂.flatten) := by
      rw [hN, List.flatten_append, List.flatten_cons]
    have memfn : ∀ d ∈ N.flatten, d.1 ∈ N.flatten.map (fun d => d.1) :=
      fun d hd => List.mem_map.mpr ⟨d, hd, rfl⟩
    -- r'（= split.2）支：d ∈ r 归 fn、d ∉ r 归 v
    have sCase : ∀ d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2,
        d.1 ∈ N.flatten.map (fun d => d.1) ∨
        d.1 ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1) := by
      intro d hd
      by_cases hdr : d ∈ r
      · exact Or.inl (memfn d (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hdr⟩))
      · refine Or.inr (List.mem_map.mpr ⟨d, ?_, rfl⟩)
        rw [rtransSpineEqSplit2 L N r x hfin]
        exact List.mem_filter.mpr ⟨hd, decide_eq_true_iff.mpr hdr⟩
    -- split.1（new1）支：块段归 v（块 FST = 首 FST 且窗口 dart ∉ r）、
    -- 尾段 ⊆ r 归 fn
    have fCase : ∀ d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1,
        d.1 ∈ N.flatten.map (fun d => d.1) ∨
        d.1 ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1) := by
      intro d hd
      have hf1 := split1Unfold L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))
      rw [hnextz1] at hf1
      rw [hf1] at hd
      rcases List.mem_append.mp hd with hd | hd
      · -- 块段：d.1 = 某窗口 dart d₀ 的首点，d₀ ∈ 窗口 ⊆ r' 且 ∉ r
        rw [List.mem_reverse] at hd
        obtain ⟨blk, hblkm, hdblk⟩ := List.mem_flatten.mp hd
        obtain ⟨d₀, hd₀w, hd₀blk⟩ := List.mem_map.mp hblkm
        have hdart : d₀ ∈ (hypermapOfList L hL).darts :=
          List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (betwnMem hd₀w))
        have hfsteq : d.1 = d₀.1 :=
          ndSpineFstEq L hL hgn hdart (hd₀blk ▸ hdblk)
        have hd₀nr : d₀ ∉ r := betwnNotInRtrans L hL hgn hunL hm hfin hd₀w
        refine Or.inr ?_
        rw [hfsteq]
        refine List.mem_map.mpr ⟨d₀, List.mem_filter.mpr ⟨?_,
          decide_eq_true_iff.mpr hd₀nr⟩, rfl⟩
        rw [hcat]
        exact List.mem_append_right _ hd₀w
      · -- 尾段 ([y1] ++ between r y1 z1) ++ [z1] ⊆ r
        refine Or.inl ?_
        have hin : d ∈ r := by
          rcases List.mem_append.mp hd with hd' | hd'
          · rcases List.mem_append.mp hd' with hd' | hb
            · simp only [List.mem_cons] at hd'
              rcases hd' with rfl | hnil
              · exact hy1
              · exact absurd hnil (by simp)
            · exact betwnMem hb
          · simp only [List.mem_cons] at hd'
            rcases hd' with rfl | hnil
            · exact hz1
            · exact absurd hnil (by simp)
        exact memfn d (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hin⟩)
    -- LEBHIRJ 点态（⊆）：fn' 每元都在 fn ∪ v（四段逐一；hflat 左结合）
    have hsub : ∀ i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1),
        i ∈ N.flatten.map (fun d => d.1) ∨
        i ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1) := by
      intro i hi
      obtain ⟨d, hdf, hdi⟩ := List.mem_map.mp hi
      rw [hflat] at hdf
      rcases List.mem_append.mp hdf with hdf | hdF
      · rcases List.mem_append.mp hdf with hdf | hdc
        · rcases List.mem_append.mp hdf with hdf | hds
          · refine Or.inl ?_
            rw [← hdi, hNflat]
            exact List.mem_map.mpr ⟨d, List.mem_append_left _ hdf, rfl⟩
          · exact hdi ▸ sCase d hds
        · refine Or.inl ?_
          rw [← hdi, hNflat]
          exact List.mem_map.mpr ⟨d,
            List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hdc))), rfl⟩
      · exact hdi ▸ fCase d hdF
    -- LEBHIRJ 点态（⊇）：fn 每元经 N = N₁ ++ r :: N₂ 分解；r 弧由
    -- TameList72 双弧覆盖落进 S ∪ F（弧实例化于 (prevEl r z, y)），
    -- S/F 都是 ntrans 1 的 flatten 段（F 经 hflat、S 经 aq6）
    have hsup : ∀ i ∈ N.flatten.map (fun d => d.1),
        i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) := by
      intro i hi
      obtain ⟨d, hdf, hdi⟩ := List.mem_map.mp hi
      rw [hNflat] at hdf
      rcases List.mem_append.mp hdf with hdf | hdf
      · refine List.mem_map.mpr ⟨d, ?_, hdi⟩
        rw [hflat]
        exact List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hdf)))))
      rcases List.mem_append.mp hdf with hdf | hdf
      · -- d ∈ r：双弧覆盖
        have hdN' : d ∈ (ntransSpine L N r x 1).flatten := by
          have hcov := betwn_or_betwn_cover hrnd (prevEl r (lZSpine L N r x))
            (lYSpine L r x) hdf
          rw [hnextz1] at hcov
          have hto : d ∈ rtransSpine L N r x 1 ∨
              d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
                (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
            rcases List.mem_append.mp hcov with hcov | hcov
            · -- 弧1 = ([z] ++ between r z y) ++ [y] ⊆ S（hcat 左段）
              refine Or.inl ?_
              rw [hcat]
              exact List.mem_append_left _ hcov
            · -- 弧2 = ([y1] ++ between r y1 z1) ++ [z1] = split.1 尾段
              refine Or.inr ?_
              exact List.mem_append_right _ hcov
          rcases hto with hto | hdF
          · exact List.mem_flatten.mpr ⟨rtransSpine L N r x 1,
              aq6 L hL N r x hgn hm, hto⟩
          · rw [hflat]
            exact List.mem_append_right _ hdF
        exact List.mem_map.mpr ⟨d, hdN', hdi⟩
      · -- d ∈ N₂.flatten
        refine List.mem_map.mpr ⟨d, ?_, hdi⟩
        rw [hflat]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hdf)))
    have hsupv : ∀ i ∈
        ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1),
        i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) := by
      intro i hi
      obtain ⟨d, hdF, hdi⟩ := List.mem_map.mp hi
      refine List.mem_map.mpr ⟨d, ?_, hdi⟩
      exact List.mem_flatten.mpr ⟨rtransSpine L N r x 1, aq6 L hL N r x hgn hm,
        (List.mem_filter.mp hdF).1⟩
    -- ④ 区间合并 + dedup 计数收口（HOL 1090-1101 的 EXTENSION/ARITH）
    have hpoint : ∀ i : ℕ, i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) ↔
        i ∈ N.flatten.map (fun d => d.1) ∨
        i ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1) :=
      fun i => ⟨fun him => hsub i him, fun hv => hv.elim (hsup i) (hsupv i)⟩
    have htofin : ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).toFinset
        = Finset.range (k + 1) := by
      ext i
      simp only [List.mem_toFinset, Finset.mem_range]
      rw [hpoint i, hOLDp i, hvIff i]
      omega
    have hK : ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length
        = k + 1 := by
      calc ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length
          = ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).toFinset.card :=
            (List.card_toFinset _).symm
        _ = (Finset.range (k + 1)).card := by rw [htofin]
        _ = k + 1 := Finset.card_range _
    rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine, hEs', hK]
    ext i
    simp only [setOfListNatSpine, Set.mem_setOf_eq]
    rw [hpoint i, hOLDp i, hvIff i]
    have hkk : k + 1 - 1 = k := rfl
    rw [hkk]
    omega

#print axioms Kepler.Text.TameSpine.elementsOfListNtrans
