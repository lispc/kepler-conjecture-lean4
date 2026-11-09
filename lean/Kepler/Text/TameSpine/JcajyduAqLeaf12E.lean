/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12E — AQ12 叶 W3a（decls 22–25）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:866-:986
  ┌──────────────────────────────────────────────────────────────┐
  │ decl 22 `betwn_cat_point_mem`    :866（51）                    │
  │ decl 23 `betwn_cat_point_sizel`  :917（26）                    │
  │ decl 24 `uniq_betwn_cat_point`   :943（13）                    │
  │ decl 25 `betwn_cat_point_last`   :956（31）                    │
  └──────────────────────────────────────────────────────────────┘
  W3b = decl 26 `betwn_cap_point`（:987，154）+ 后继面（另交）。

  ┌─ 三个辅件（W3a/W3b 共用，先落）──────────────────────────────
  │ `aqs_getLastAppend`  = `(l ++ l').getLast! = if l'=[] then l.getLast! else l'.getLast!`
  │ `aqs_headAppend`     = `(l ++ l').head!  = if l=[] then l'.head! else l.head!`
  │ `aqs_lastBetwnEqPrev`= HOL `Aq23.next_last_betwn` + `Seq2.prev_next_id` 的合成：
  │   `(betwn r y z).getLast! = prev_el r z`（非空支）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（HOL 的 indexf 计数，Lean 同构）────────────────────────
  │ 记 `I x y = indexf x y r`、`S = betwn r v v1`、`A = betwn r v l`、
  │ `B = betwn r l v1`、`T = (A ++ [l]) ++ B`。
  │ decl 22：`x ∈ S ↔ x ∈ A ∨ x = l ∨ x ∈ B`——`indexf_betwn_eq` 的
  │   三区间刻画（`I v x < / = / > I v l`），分割点用 `indexf_n` 的幂行走
  │   保 x = l；`I v x = I v l + I l x` 用 `indexf_add_betwn`（λ=中间点）。
  │ decl 23：`|S| = I v v1 - 1` 与 `|A| = I v l - 1`、`|B| = I l v1 - 1`
  │   （`size_betwn`）+ `I v v1 = I v l + I l v1`（`indexf_add_betwn`）。
  │ decl 24：`A/[l]/B` 三块各自 Nodup（`uniq_betwn`/`nodup_singleton`）
  │   + 两两不交（`not_betwn2` 两次 + A∩B 的 indexf 单调性矛盾）。
  │   HOL 走 `Seq.uniq_size_uniq`；Lean 直接 `List.nodup_append` 分解。
  │ decl 25：`LAST S = LAST T`。两支（`B = []` / `B ≠ []`）：
  │   `aqs_lastBetwnEqPrev` 给 `LAST S = prev_el r v1`；
  │   `aqs_getLastAppend` 把 T 的尾剖开：B 非空 ⇒ `LAST B = prev_el r v1`；
  │   B 空 ⇒ `next_el r l = v1`（`betwn_nil`）⇒ `l = prev_el r v1`。
  └────────────────────────────────────────────────────────────────

  ┌─ W1a 接驳（编排者验收点）────────────────────────────────────
  │ decl 26（W3b）才消费 `aqs_eq_last_next`。本轮已在
  │ `ProbeAQ12W3Hookup.lean` 做**类型级接驳实测**：把 capstone 的四个
  │ 前提（同成员/Nodup/逐点后继/LAST）作为变量喂给 `aqs_eq_last_next`，
  │ RC=0 ⇒ 签名接得上。W3b 的两条候选路线（HOL 的 next_el 逐支 vs
  │ `betwn_take_drop` 纯算术）另行上报。
  └────────────────────────────────────────────────────────────────

  载体：固定 `List (ℕ × ℕ)`（与 AQ12 全段及 `betwnTakeDrop` 等既有件一致）。
  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (between)

/-! ## §0 三辅件 -/

/-- `getLast!` 的拼接律：右段非空取右段，否则取左段。 -/
theorem aqs_getLastAppend (l l' : List (ℕ × ℕ)) :
    (l ++ l').getLast! = if l' = [] then l.getLast! else l'.getLast! := by
  by_cases h : l' = []
  · subst h
    simp
  · rw [if_neg h, List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD,
      List.getLast?_append, List.getLast?_eq_some_getLast h]
    simp

/-- `head!` 的拼接律：左段非空取左段，否则取右段。 -/
theorem aqs_headAppend (l l' : List (ℕ × ℕ)) :
    (l ++ l').head! = if l = [] then l'.head! else l.head! := by
  by_cases h : l = []
  · subst h
    simp
  · rw [if_neg h]
    cases l with
    | nil => exact absurd rfl h
    | cons a t => simp

/-- **HOL `next_last_betwn` + `prev_next_id` 合成**（Aq23.hl:? / Seq2:1784）：
非空 `betwn r y z` 的 LAST 是 `z` 的前驱。 -/
theorem aqs_lastBetwnEqPrev {r : List (ℕ × ℕ)} {y z : ℕ × ℕ} (hr : r.Nodup)
    (hy : y ∈ r) (hz : z ∈ r) (hyz : y ≠ z) (hne : between r y z ≠ []) :
    (between r y z).getLast! = prevEl r z := by
  have hmem : (between r y z).getLast! ∈ between r y z := aqs_getLastMem hne
  have hmemr : (between r y z).getLast! ∈ r := betwnMem hmem
  have hnext : nextEl r (between r y z).getLast! = z := by
    have h := nextLastBetwn (r := r) hy hz hr hyz hne
    rwa [← getLast!EqGetLast hne] at h
  calc (between r y z).getLast! = prevEl r (nextEl r (between r y z).getLast!) :=
        (Kepler.Text.TameLp.prevEl_nextEl hr hmemr).symm
    _ = prevEl r z := by rw [hnext]

/-! ## §1 HOL AQ12.hl:866 `betwn_cat_point_mem` -/

/-- **HOL `betwn_cat_point_mem`**（AQ12.hl:866-:916）：
`l` 在环段 `betwn r v v1` 上 ⇒ 段内成员 ⇔ `betwn r v l ++ [l] ++ betwn r l v1` 成员。 -/
theorem aqs_betwnCatPointMem {r : List (ℕ × ℕ)} {v v1 l : ℕ × ℕ} (hr : r.Nodup)
    (hl : l ∈ between r v v1) (hvne : v ≠ v1) (hv : v ∈ r) (hv1 : v1 ∈ r) :
    ∀ x, x ∈ between r v v1
      ↔ x ∈ ((between r v l ++ [l]) ++ between r l v1) := by
  have hl_r : l ∈ r := betwnMem hl
  have hlv : l ≠ v := fun h => notBetwn1 (s := r) (x := v) (z := v1) hr hv1 (h ▸ hl)
  have hlv1 : l ≠ v1 := fun h => notBetwn2 (s := r) (x := v) (z := v1) hr (h ▸ hl)
  have hlb := (indexfBetwnEq hvne hr hv hv1).mp hl
  intro x
  constructor
  · -- 正向：x ∈ S 三区间
    intro hx
    have hxr : x ∈ r := betwnMem hx
    have hxb := (indexfBetwnEq hvne hr hv hv1).mp hx
    have hvx : v ≠ x := fun h => notBetwn1 (s := r) (x := v) (z := v1) hr hv1 (h.symm ▸ hx)
    rcases lt_trichotomy (indexf v x r) (indexf v l r) with hlt | heq | hgt
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
        (Or.inl ((indexfBetwnEq hlv.symm hr hv hl_r).mpr ⟨hxb.1, hlt⟩))))
    · -- x = l（同一幂行走位置）
      have hx1 : (nextEl r)^[indexf v x r] v = x := indexfN hv hxr hr
      have hl1 : (nextEl r)^[indexf v l r] v = l := indexfN hv hl_r hr
      have hxl : x = l := by rw [← hx1, heq, hl1]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
        (Or.inr (List.mem_singleton.mpr hxl))))
    · -- x ∈ B：I v x = I v l + I l x
      refine List.mem_append.mpr (Or.inr ?_)
      have hlmem : l ∈ between r v x :=
        (indexfBetwnEq hvx hr hv hxr).mpr ⟨hlb.1, hgt⟩
      have hadd : indexf v l r + indexf l x r = indexf v x r :=
        indexfAddBetwn hvx hr hv hlmem hxr
      have hadd2 : indexf v l r + indexf l v1 r = indexf v v1 r :=
        indexfAddBetwn hvne hr hv hl hv1
      have hpos : 0 < indexf l x r := by omega
      have hlt2 : indexf l x r < indexf l v1 r := by omega
      exact (indexfBetwnEq hlv1 hr hl_r hv1).mpr ⟨hpos, hlt2⟩
  · -- 反向：T 的三块各落 S
    intro hx
    rcases List.mem_append.mp hx with hxA' | hxB
    · rcases List.mem_append.mp hxA' with hxA | hxl
      · -- x ∈ A ⊂ S
        have hb := (indexfBetwnEq hlv.symm hr hv hl_r).mp hxA
        exact (indexfBetwnEq hvne hr hv hv1).mpr ⟨hb.1, lt_trans hb.2 hlb.2⟩
      · -- x = l
        have hxl' : x = l := List.mem_singleton.mp hxl
        exact hxl' ▸ hl
    · -- x ∈ B：幂行走把 I v x 拆成 I v l + I l x
      have hb := (indexfBetwnEq hlv1 hr hl_r hv1).mp hxB
      have hxr : x ∈ r := betwnMem hxB
      have hw1 : (nextEl r)^[indexf v l r] v = l := indexfN hv hl_r hr
      have hw2 : (nextEl r)^[indexf l x r] l = x := indexfN hl_r hxr hr
      have hsum : (nextEl r)^[indexf v l r + indexf l x r] v = x := by
        rw [Nat.add_comm (indexf v l r) (indexf l x r), Function.iterate_add_apply, hw1, hw2]
      have haddL : indexf v l r + indexf l v1 r = indexf v v1 r :=
        indexfAddBetwn hvne hr hv hl hv1
      have hbound : indexf v l r + indexf l x r < r.length := by
        have := indexfLtSizel hv hv1
        omega
      have hadd : indexf v x r = indexf v l r + indexf l x r :=
        nextElnIndexf hv hxr hr hsum hbound
      exact (indexfBetwnEq hvne hr hv hv1).mpr ⟨by omega, by omega⟩

/-! ## §2 HOL AQ12.hl:917 `betwn_cat_point_sizel` -/

/-- **HOL `betwn_cat_point_sizel`**（AQ12.hl:917-:942）：
`|betwn r v v1| = |betwn r v l| + |betwn r l v1| + 1`。 -/
theorem aqs_betwnCatPointSizel {r : List (ℕ × ℕ)} {v v1 l : ℕ × ℕ} (hr : r.Nodup)
    (hl : l ∈ between r v v1) (hvne : v ≠ v1) (hv : v ∈ r) (hv1 : v1 ∈ r) :
    (between r v v1).length
      = (between r v l).length + (between r l v1).length + 1 := by
  have hl_r : l ∈ r := betwnMem hl
  have hlv : l ≠ v := fun h => notBetwn1 (s := r) (x := v) (z := v1) hr hv1 (h ▸ hl)
  have hlv1 : l ≠ v1 := fun h => notBetwn2 (s := r) (x := v) (z := v1) hr (h ▸ hl)
  have h1 : (between r v v1).length = indexf v v1 r - 1 := sizeBetwn hr hv hv1 hvne
  have h2 : (between r v l).length = indexf v l r - 1 := sizeBetwn hr hv hl_r hlv.symm
  have h3 : (between r l v1).length = indexf l v1 r - 1 := sizeBetwn hr hl_r hv1 hlv1
  have hadd : indexf v l r + indexf l v1 r = indexf v v1 r :=
    indexfAddBetwn hvne hr hv hl hv1
  have hb := (indexfBetwnEq hvne hr hv hv1).mp hl
  omega

/-! ## §3 HOL AQ12.hl:943 `uniq_betwn_cat_point` -/

/-- **HOL `uniq_betwn_cat_point`**（AQ12.hl:943-:955）：
`(betwn r v l ++ [l] ++ betwn r l v1)` 是 Nodup。HOL 走 `Seq.uniq_size_uniq`
（成员 + 长度 + 单侧 Nodup）；Lean 直接 `List.nodup_append` 三块分解。 -/
theorem aqs_uniqBetwnCatPoint {r : List (ℕ × ℕ)} {v v1 l : ℕ × ℕ} (hr : r.Nodup)
    (hl : l ∈ between r v v1) (hvne : v ≠ v1) (hv : v ∈ r) (hv1 : v1 ∈ r) :
    ((between r v l ++ [l]) ++ between r l v1).Nodup := by
  have hl_r : l ∈ r := betwnMem hl
  have hlv : l ≠ v := fun h => notBetwn1 (s := r) (x := v) (z := v1) hr hv1 (h ▸ hl)
  have hlv1 : l ≠ v1 := fun h => notBetwn2 (s := r) (x := v) (z := v1) hr (h ▸ hl)
  have hlb := (indexfBetwnEq hvne hr hv hv1).mp hl
  have hA : (between r v l).Nodup := uniqBetwn (z := v) (y := l) hr hv hl_r hlv.symm
  have hB : (between r l v1).Nodup := uniqBetwn (z := l) (y := v1) hr hl_r hv1 hlv1
  have hlA : l ∉ between r v l := notBetwn2 (s := r) (x := v) (z := l) hr
  have hlB : l ∉ between r l v1 := notBetwn1 (s := r) (x := l) (z := v1) hr hv1
  have hdisj1 : (between r v l ++ [l]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hA, List.nodup_singleton l, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    intro hab
    exact hlA (hab ▸ ha)
  rw [List.nodup_append]
  refine ⟨hdisj1, hB, ?_⟩
  intro a ha b hb
  rcases List.mem_append.mp ha with hA' | hal
  · -- a ∈ A、b ∈ B、a = b：indexf 单调性矛盾
    intro hab
    subst hab
    exfalso
    have har : a ∈ r := betwnMem hA'
    have hne_l : a ≠ l := fun h =>
      notBetwn2 (s := r) (x := v) (z := l) hr (h ▸ hA')
    have hab' := (indexfBetwnEq hlv.symm hr hv hl_r).mp hA'
    have hbb := (indexfBetwnEq hlv1 hr hl_r hv1).mp hb
    have h1 : indexf v a r + indexf a l r = indexf v l r :=
      indexfAddBetwn hlv.symm hr hv hA' hl_r
    have h2 : indexf l a r + indexf a v1 r = indexf l v1 r :=
      indexfAddBetwn hlv1 hr hl_r hb hv1
    have h3 : indexf v a r + indexf a v1 r = indexf v v1 r :=
      indexfAddBetwn hvne hr hv
        ((indexfBetwnEq hvne hr hv hv1).mpr ⟨hab'.1, lt_trans hab'.2 hlb.2⟩) hv1
    have h4 : indexf a l r + indexf l a r = r.length :=
      indexfAntisym har hl_r hne_l
    have h5 : indexf v l r + indexf l v1 r = indexf v v1 r :=
      indexfAddBetwn hvne hr hv hl hv1
    have hpos : 0 < r.length := List.length_pos_of_mem hv
    omega
  · rw [List.mem_singleton] at hal
    subst hal
    intro hab
    exact hlB (hab.symm ▸ hb)

/-! ## §4 HOL AQ12.hl:956 `betwn_cat_point_last` -/

/-- **HOL `betwn_cat_point_last`**（AQ12.hl:956-:986）：两端 LAST 相同
（`B = []` 支由 `betwn_nil` 把 `l` 认成 `v1` 的前驱）。 -/
theorem aqs_betwnCatPointLast {r : List (ℕ × ℕ)} {v v1 l : ℕ × ℕ} (hr : r.Nodup)
    (hl : l ∈ between r v v1) (hvne : v ≠ v1) (hv : v ∈ r) (hv1 : v1 ∈ r) :
    (between r v v1).getLast! = ((between r v l ++ [l]) ++ between r l v1).getLast! := by
  have hl_r : l ∈ r := betwnMem hl
  have hlv1 : l ≠ v1 := fun h => notBetwn2 (s := r) (x := v) (z := v1) hr (h ▸ hl)
  have hspos : between r v v1 ≠ [] := List.ne_nil_of_mem hl
  have hS : (between r v v1).getLast! = prevEl r v1 :=
    aqs_lastBetwnEqPrev hr hv hv1 hvne hspos
  have hT : ((between r v l ++ [l]) ++ between r l v1).getLast! = prevEl r v1 := by
    rw [aqs_getLastAppend]
    by_cases hB : between r l v1 = []
    · rw [if_pos hB, aqs_getLastAppend, if_neg (by simp : ([l] : List (ℕ × ℕ)) ≠ [])]
      have hlen : ([l] : List (ℕ × ℕ)).getLast! = l := by simp
      rw [hlen]
      have hnext : nextEl r l = v1 := ((betwnNil hr hlv1 hl_r hv1).mp hB).symm
      rw [← hnext, Kepler.Text.TameLp.prevEl_nextEl hr hl_r]
    · rw [if_neg hB]
      exact aqs_lastBetwnEqPrev hr hl_r hv1 hlv1 hB
  rw [hS, hT]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_getLastAppend
#print axioms Kepler.Text.TameSpine.aqs_headAppend
#print axioms Kepler.Text.TameSpine.aqs_lastBetwnEqPrev
#print axioms Kepler.Text.TameSpine.aqs_betwnCatPointMem
#print axioms Kepler.Text.TameSpine.aqs_betwnCatPointSizel
#print axioms Kepler.Text.TameSpine.aqs_uniqBetwnCatPoint
#print axioms Kepler.Text.TameSpine.aqs_betwnCatPointLast
