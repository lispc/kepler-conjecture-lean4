/-
  Kepler.Text.TameSpine.Reduction3NewvertexPrepTransform — W2-件2 Wave A：
  HOL `newvertex_prepped_transform_lemma`（reduction2.hl:1139-1271）的
  spine 岛移植：一步变换后「新顶点全集基数 = 旧基数 + 新弧长」。

  ┌─ 与 HOL 的关系（reduction2.hl:1139）─────────────────────────────
  │ HOL：elements_of_list ∧ r_rtrans_eq ∧ is_restricted ∧ good_list ∧
  │ good_list_nodes ∧ marked_list ∧ ~final_list ∧ newvertex_prepped ==>
  │   sizel (undup (MAP FST (flatten (ntrans … 1)))) =
  │   sizel (undup (MAP FST (flatten N))) +
  │   sizel (MAP FST (filter (\d. ~MEM d r) (rtrans … 1))).
  │ 本件逐字同形（spine 岛：ntransSpine/rtransSpine；hgn 显式；is_restricted
  │ 由 marked 合取 1 内联，同 件1/件1a 制式；r_rtrans_eq 照原文保留前提位
  │ ——件1a elementsOfListNtransTop 同款携带、证体零消费）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（路线换轨，均机器等价）─────────────────────────────────
  │ ① HOL 的 CARD/UNION/INTER + Aq7.AQ7 集合基数链 → Lean range' 精确形：
  │    件1a `newsSplit` + `rtransFilterEq` 给 news = b ++ rest
  │    （b := MAP FST (filter (∉r) r')）、hnvp 展开给 news = range' n |news|、
  │    `take_range'_eq` 给 **b = range' n |b|** ⇒ i ∈ b ↔ n ≤ i ≤ n+|b|-1
  │    （免 AQ7：HOL 用它证 b 与旧集不交，Lean 由 range' 表示直接得）。
  │ ② 计数收口 = 两个 ℕ-前缀集逐点相等：LEBHIRJ 点态（本文件
  │    `lebhirjPoint`，见 §1）+ hOLDp（hold 点态化）+ b 的 range 形 ⇒
  │    i ∈ fn' ↔ i < n + |b|；另一侧由件1a 主定理
  │    `elementsOfListNtransTop` + `quotientListElements` 得
  │    i ∈ fn' ↔ i ≤ |fn'.dedup| - 1；两点代入 + 0 ∈ fn' 保长 ⇒ omega。
  │ ③ LEBHIRJ 点态（HOL LEBHIRJ.hl:102 set(fn') = set(fn) ∪ set(v)）——
  │    件1/件1a 均私装，本件同款重推导为**公开件** `lebhirjPoint`
  │    （组装段与件1 :193-327 逐字同源；Wave C 直接消费）。
  │ ④ 跨文件取件：件1a 的 `newsSplit`/`rtransFilterEq`/`leYInR`/
  │    `take_range'_eq`/`setOfListNatSpine_range'` 五件本波翻公开
  │    （Visibility-only 补丁，陈述与证体逐字零改；见配套 patch 段落）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入（/tmp 岛编）；
  │ 既有文件仅五处可见性翻公开（零陈述改动）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.Reduction3HbridgeElim

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between splitAt)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (elementsOfList GoodListNodesTl nextEl_mem_of_mem
  prevEl_mem_of_mem hypermapOfList dart_in_face findFaceDarts_congr_of_mem
  mem_darts_of_mem_findFace nextEl_eq_getD getD_eq_getElem_of_lt
  findFaceDarts_nodup)

/-! ## §0 件1 私件同款重推导（跨文件不可取，同款撇号副本） -/

/-- 件1 私件 `rtransSpineEqSplit2` 的同款重推导。 -/
private theorem rtransSpineEqSplit2W (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (hf : ¬finalListSpine L r) :
    rtransSpine L N r x 1 = (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
  show ((transformListSpine L x)^[1] (N, r)).2 = _
  rw [Function.iterate_one]
  simp only [transformListSpine, if_neg hf]

/-- 件1 私件 `leSubOneIff` 的同款重推导。 -/
private theorem leSubOneIffW {a b : ℕ} (hb : 1 ≤ b) : a ≤ b - 1 ↔ a < b := by
  rcases b with _ | c
  · exact absurd hb (by simp)
  · show a ≤ c ↔ a < c + 1
    exact Nat.lt_succ_iff.symm

/-- `1 ≤ b → a ≤ b - 1 → a < b`（omega 在含 Nat.sub 假设上失灵时的替代桥）。 -/
private theorem ltOfLeSubOne {a b : ℕ} (hb : 1 ≤ b) (h : a ≤ b - 1) : a < b := by
  rcases b with _ | c
  · exact absurd hb (by simp)
  · exact Nat.lt_succ_iff.mpr h

/-- `a - 1 < b → a ≤ b`（pred 桥）。 -/
private theorem leOfPredLt {a b : ℕ} (h : a - 1 < b) : a ≤ b := by
  rcases a with _ | k
  · exact Nat.zero_le _
  · exact Nat.succ_le_of_lt h

/-! ## §1 LEBHIRJ 点态（HOL LEBHIRJ.hl:102；公开形，Wave C 直接消费） -/

/-- **HOL LEBHIRJ**（LEBHIRJ.hl:102）：变换一步后顶点全集
`set(fn') = set(fn) ∪ set(v)`，v = MAP FST (filter (∉r) r')。
组装段与件1 `elementsOfListNtrans` 证体（:193-327）逐字同源。 -/
theorem lebhirjPoint (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ i : ℕ, i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) ↔
      i ∈ N.flatten.map (fun d => d.1) ∨
      i ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
        (fun d => d.1) := by
  have hunL : ∀ l ∈ L, l.Nodup := (simpleHypermapUniq L hL hgn).mp hm.1.1.simple
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy1 : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hy
  have hz1 : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hz
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hcat : rtransSpine L N r x 1
      = ((([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x))
          ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (lZSpine L N r x)) :=
    rtransCat L N r x hf hrnd
  obtain ⟨N₁, N₂, hN, hnot, hflat⟩ := aq1b_flattenNtrans1 L hL hgn hunL hm hf
  have hNflat : N.flatten = N₁.flatten ++ (r ++ N₂.flatten) := by
    rw [hN, List.flatten_append, List.flatten_cons]
  have memfn : ∀ d ∈ N.flatten, d.1 ∈ N.flatten.map (fun d => d.1) :=
    fun d hd => List.mem_map.mpr ⟨d, hd, rfl⟩
  have sCase : ∀ d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2,
      d.1 ∈ N.flatten.map (fun d => d.1) ∨
      d.1 ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
        (fun d => d.1) := by
    intro d hd
    by_cases hdr : d ∈ r
    · exact Or.inl (memfn d (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hdr⟩))
    · refine Or.inr (List.mem_map.mpr ⟨d, ?_, rfl⟩)
      rw [rtransSpineEqSplit2W L N r x hf]
      exact List.mem_filter.mpr ⟨hd, decide_eq_true_iff.mpr hdr⟩
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
    · rw [List.mem_reverse] at hd
      obtain ⟨blk, hblkm, hdblk⟩ := List.mem_flatten.mp hd
      obtain ⟨d₀, hd₀w, hd₀blk⟩ := List.mem_map.mp hblkm
      have hdart : d₀ ∈ (hypermapOfList L hL).darts :=
        List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (betwnMem hd₀w))
      have hfsteq : d.1 = d₀.1 :=
        ndSpineFstEq L hL hgn hdart (hd₀blk ▸ hdblk)
      have hd₀nr : d₀ ∉ r := betwnNotInRtrans L hL hgn hunL hm hf hd₀w
      refine Or.inr ?_
      rw [hfsteq]
      refine List.mem_map.mpr ⟨d₀, List.mem_filter.mpr ⟨?_,
        decide_eq_true_iff.mpr hd₀nr⟩, rfl⟩
      rw [hcat]
      exact List.mem_append_right _ hd₀w
    · refine Or.inl ?_
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
    · have hdN' : d ∈ (ntransSpine L N r x 1).flatten := by
        have hcov := betwn_or_betwn_cover hrnd (prevEl r (lZSpine L N r x))
          (lYSpine L r x) hdf
        rw [hnextz1] at hcov
        have hto : d ∈ rtransSpine L N r x 1 ∨
            d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
          rcases List.mem_append.mp hcov with hcov | hcov
          · refine Or.inl ?_
            rw [hcat]
            exact List.mem_append_left _ hcov
          · refine Or.inr ?_
            exact List.mem_append_right _ hcov
        rcases hto with hto | hdF
        · exact List.mem_flatten.mpr ⟨rtransSpine L N r x 1,
            aq6 L hL N r x hgn hm, hto⟩
        · rw [hflat]
          exact List.mem_append_right _ hdF
      exact List.mem_map.mpr ⟨d, hdN', hdi⟩
    · refine List.mem_map.mpr ⟨d, ?_, hdi⟩
      rw [hflat]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hdf)))
  have hsupv : ∀ i ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
      (fun d => d.1),
      i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) := by
    intro i hi
    obtain ⟨d, hdF, hdi⟩ := List.mem_map.mp hi
    refine List.mem_map.mpr ⟨d, ?_, hdi⟩
    exact List.mem_flatten.mpr ⟨rtransSpine L N r x 1, aq6 L hL N r x hgn hm,
      (List.mem_filter.mp hdF).1⟩
  intro i
  exact ⟨fun him => hsub i him, fun hv => hv.elim (hsup i) (hsupv i)⟩

/-! ## §2 主件：newvertex_prepped_transform_lemma（reduction2.hl:1139） -/

/-- **HOL `newvertex_prepped_transform_lemma`**（reduction2.hl:1139-1271）
spine 形：`|fn'(1)| = |fn| + |b|`，b = MAP FST (filter (∉r) r')。 -/
theorem newvertexPreppedTransformLemmaSpine
    (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hrre : Kepler.Text.Reduction5.rRtransEq L N r x)
    (hm : MarkedListSpineFull hL N r x)
    (hnvp : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hf : ¬finalListSpine L r)
    (hold : elementsOfList (Kepler.Text.Reduction5.quotientList L N)
      = {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1}) :
    ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length
      = (N.flatten.map (fun d => d.1)).dedup.length
        + ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)).length) := by
  have hunL : ∀ l ∈ L, l.Nodup := (simpleHypermapUniq L hL hgn).mp hm.1.1.simple
  -- news = range' n |news|（非 final 支展开）
  have hnews : Kepler.Text.Reduction3.newvertex L r x
      = List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
          (Kepler.Text.Reduction3.newvertex L r x).length := by
    have h := hnvp
    rw [show Kepler.Text.Reduction3.newvertexPrepped L N r x =
        (finalListSpine L r ∨ Kepler.Text.Reduction3.newvertex L r x
          = List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
              (Kepler.Text.Reduction3.newvertex L r x).length) from rfl] at h
    exact h.resolve_left hf
  -- 前缀分解 + v = betwn
  obtain ⟨rest, hrest⟩ := newsSplit L hL hgn hunL hm hf
  have hbEq : ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map (fun d => d.1)
      = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (fun d => d.1) := by
    rw [rtransFilterEq L hL hgn hunL hm hf]
  have htake : List.take ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
        (fun d => d.1)).length) (Kepler.Text.Reduction3.newvertex L r x)
      = ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map (fun d => d.1) := by
    rw [hrest, ← hbEq]
    exact List.take_left
  have hlen_v : ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
      (fun d => d.1)).length) ≤ (Kepler.Text.Reduction3.newvertex L r x).length := by
    rw [hrest, ← hbEq, List.length_append]
    exact Nat.le_add_right _ _
  have hbRng : ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map (fun d => d.1)
      = List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
          ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)).length) := by
    calc ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map (fun d => d.1)
        = List.take ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)).length) (Kepler.Text.Reduction3.newvertex L r x) := htake.symm
      _ = List.take ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)).length)
            (List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
              (Kepler.Text.Reduction3.newvertex L r x).length) := by
          conv_lhs => rw [hnews]
      _ = List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
            ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
              (fun d => d.1)).length) := take_range'_eq _ _ _ hlen_v
  have hn1 : 1 ≤ (N.flatten.map (fun d => d.1)).dedup.length := by
    by_contra h0
    have h0' : (N.flatten.map (fun d => d.1)).dedup.length = 0 := by omega
    have hd0 : (N.flatten.map (fun d => d.1)).dedup = [] :=
      List.length_eq_zero_iff.mp h0'
    have hfe : N.flatten.map (fun d => d.1) = [] := (List.dedup_eq_nil _).mp hd0
    have hxfn : x.1 ∈ N.flatten.map (fun d => d.1) :=
      List.mem_map.mpr ⟨x, List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩, rfl⟩
    exact absurd hxfn (by rw [hfe]; simp)
  have hbis : ∀ i : ℕ,
      i ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map (fun d => d.1)
        ↔ ((N.flatten.map (fun d => d.1)).dedup.length ≤ i ∧
            i ≤ (N.flatten.map (fun d => d.1)).dedup.length
              + ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
                (fun d => d.1)).length) - 1) := by
    intro i
    conv_lhs => rw [hbRng]
    rw [List.mem_range']
    constructor
    · rintro ⟨j, hj, rfl⟩
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨i - (N.flatten.map (fun d => d.1)).dedup.length, ?_, ?_⟩
      · rw [Nat.sub_lt_iff_lt_add h1, Nat.add_comm]
        exact ltOfLeSubOne (Nat.le_trans hn1 (Nat.le_add_right _ _)) h2
      · rw [Nat.one_mul, Nat.add_sub_of_le h1]
  have hOLDp : ∀ i : ℕ, i ∈ N.flatten.map (fun d => d.1) ↔
      i < (N.flatten.map (fun d => d.1)).dedup.length := by
    intro i
    have hEs : elementsOfList (quotientListSpine L N)
        = setOfListNatSpine (N.flatten.map (fun d => d.1)) :=
      quotientListElements L hL hm.1.2.1
    have h1 : elementsOfList (Kepler.Text.Reduction5.quotientList L N)
        = setOfListNatSpine (N.flatten.map (fun d => d.1)) := by
      rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]; exact hEs
    have h2 := hold
    rw [h1] at h2
    have hi := congrArg (fun S : Set ℕ => i ∈ S) h2
    have hraw : i ∈ N.flatten.map (fun d => d.1) ↔
        i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1 := by
      simpa [setOfListNatSpine, Set.mem_setOf_eq] using hi
    exact hraw.trans (leSubOneIffW hn1)
  have hNEWp : ∀ i : ℕ, i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) ↔
      i ≤ ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length - 1 := by
    intro i
    have hEs' : elementsOfList (quotientListSpine L (ntransSpine L N r x 1))
        = setOfListNatSpine ((ntransSpine L N r x 1).flatten.map (fun d => d.1)) :=
      quotientListElements L hL (aqiunpp1_top L hL hgn hm)
    have h1 : elementsOfList (Kepler.Text.Reduction5.quotientList L (ntransSpine L N r x 1))
        = setOfListNatSpine ((ntransSpine L N r x 1).flatten.map (fun d => d.1)) := by
      rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]; exact hEs'
    have h2 := elementsOfListNtransTop L hL hgn hrre hm hnvp hold
    rw [h1] at h2
    have hi := congrArg (fun S : Set ℕ => i ∈ S) h2
    simpa [setOfListNatSpine, Set.mem_setOf_eq] using hi
  have hsetAll : ∀ i : ℕ, i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1)
      ↔ i < (N.flatten.map (fun d => d.1)).dedup.length
          + ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)).length) := by
    intro i
    rw [lebhirjPoint L hL hgn hm hf i, hOLDp i, hbis i]
    constructor
    · rintro (h | ⟨h1, h2⟩) <;> omega
    · intro h
      by_cases hlt : i < (N.flatten.map (fun d => d.1)).dedup.length
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, by omega⟩
  have hfnp1 : 1 ≤ ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length := by
    have h0 : 0 ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) :=
      (hsetAll 0).mpr (by omega)
    have hne : ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup ≠ [] := by
      intro hd
      have hnil : ((ntransSpine L N r x 1).flatten.map (fun d => d.1)) = [] :=
        (List.dedup_eq_nil _).mp hd
      rw [hnil] at h0
      exact absurd h0 (by simp)
    have hlen : ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length ≠ 0 := by
      intro h0'
      exact hne (List.length_eq_zero_iff.mp h0')
    exact Nat.one_le_iff_ne_zero.mpr hlen
  have hle : ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length
      ≤ (N.flatten.map (fun d => d.1)).dedup.length
        + ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1)).length) := by
    have hmem : ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length - 1
        ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) :=
      (hNEWp _).mpr le_rfl
    have hlt' := (hsetAll _).mp hmem
    exact leOfPredLt hlt'
  have hge : (N.flatten.map (fun d => d.1)).dedup.length
      + ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
        (fun d => d.1)).length) ≤ ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length := by
    have hmem : (N.flatten.map (fun d => d.1)).dedup.length
        + ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1)).length) - 1
        ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) :=
      (hsetAll _).mpr (by omega)
    have hle' := (hNEWp _).mp hmem
    have hm1 : 1 ≤ ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length := hfnp1
    have h1 : (N.flatten.map (fun d => d.1)).dedup.length
        + ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1)).length) - 1
        < ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length :=
      Nat.lt_of_le_of_lt hle' (Nat.pred_lt (Nat.pos_iff_ne_zero.mp hm1))
    exact leOfPredLt h1
  omega

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.lebhirjPoint
#print axioms Kepler.Text.TameSpine.newvertexPreppedTransformLemmaSpine
