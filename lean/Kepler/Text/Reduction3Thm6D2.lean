/-
  Kepler.Text.Reduction3Thm6D2 — T6D 第二件：`size_vs`（T6 板收尾）。

  ┌─ 件目（逐件对账）─────────────────────────────────────────────
  │   size_vs  reduction3.hl:2055-2296 → §A sizeVs
  │ 陈述翻译口径：FST/SND ↦ .1/.2、find_face ↦ findFaceDarts、
  │ sizel ↦ .length、MEM ↦ ∈、uniq ↦ .Nodup、SUC n ↦ n + 1、
  │ PRE k ↦ k - 1（k > 0 由前提给出）。HOL 中被 `//` 注释掉的两行
  │ （transform_assumption_v2 L、MEM (ytrans L N r x 0) r）**不进前提**。
  │ 载体三插槽照 Reduction3DefsAssumption.lean 先例：
  │   GoodNodesL : fgraph ℕ → Prop、IsRestrictedL : fgraph ℕ → Prop、
  │   Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop。
  │ HOL 路线：dest_triple_full 展开 → size_initial_seg + size_final_seg
  │ → 对 take 前缀归纳（size_dest_triple0_cons2 走步 + indexf 链算术）
  │ → indexf_prev 收尾。链侧全部落成 take 前缀不变式。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ if 重写一律 `rw [if_pos/if_neg]`；indexf 全用 Reduction5.indexf
  │ （Spine 件经 indexf_eq_spine 桥）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm6D
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl findFaceDarts GoodList)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart core indexf finalList transformCount ytrans ztrans)
open Kepler.Text.Reduction4 (indexfRefl indexf_eq_zero indexf_add_left indexf_add_right)

/-! ## §0 私有辅助（D 文件 private 不可跨文件，复制；纯列表事实） -/

/-- `destTriple0` 的 cons 展开方程（rfl 级；T6/T6D 同体）。 -/
private theorem destTriple0_cons_eq (f : List ℕ) (s : List (Option ℕ)) (u v n : ℕ)
    (ts : List (ℕ × ℕ × ℕ)) :
    destTriple0 f s ((u, v, n) :: ts) =
      (let ns := List.replicate n (none : Option ℕ)
       if s = [] then destTriple0 f ([some u] ++ ns ++ [some v]) ts
       else
         let u0 := (s.getLastD none).getD 0
         if u0 = u then destTriple0 f (s ++ ns ++ [some v]) ts
         else if nextEl f u0 = u then
           destTriple0 f (s ++ [some u] ++ ns ++ [some v]) ts
         else
           destTriple0 f (s ++ (between f u0 u).map some ++ [some u] ++ ns
             ++ [some v]) ts) := rfl

/-- `size_betwn` 链口径（泛型；T6C/D 同名件 private，2 行现推）。 -/
private theorem sizeBetwnChain {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x y : α} (hnd : s.Nodup)
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (between s x y).length = indexf x y s - 1 := by
  rw [Kepler.Text.TameSpine.sizeBetwn hnd hx hy hne, indexf_eq_spine]

/-- 同表不同界证的 `getElem` 同值（proof irrelevance 直给）。 -/
private theorem getElem_eq_of_eq {α : Type} {l₁ l₂ : List α} (h : l₁ = l₂) (i : Nat)
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) : l₁[i]'h₁ = l₂[i]'h₂ := by
  subst h
  rfl

private theorem getLastD_append_of_ne {α : Type} (d : α) (a : List α) {b : List α}
    (h : b ≠ []) : (a ++ b).getLastD d = b.getLastD d := by
  induction a generalizing d with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.getLastD_cons, ih]
    cases b with
    | nil => exact (h rfl).elim
    | cons y ys => rw [List.getLastD_cons, List.getLastD_cons]

private theorem destTriple0NeNil (f : List ℕ) (uvns : List (ℕ × ℕ × ℕ))
    (sofar : List (Option ℕ)) (h : sofar ≠ []) :
    destTriple0 f sofar uvns ≠ [] := by
  induction uvns generalizing sofar with
  | nil =>
    rw [destTriple0Nil]
    exact h
  | cons t ts ih =>
    obtain ⟨u, v, n⟩ := t
    rw [destTriple0_cons_eq]
    dsimp only
    rw [if_neg h]
    by_cases h1 : (sofar.getLastD none).getD 0 = u
    · rw [if_pos h1]
      exact ih _ (by simp)
    · rw [if_neg h1]
      by_cases h2 : nextEl f ((sofar.getLastD none).getD 0) = u
      · rw [if_pos h2]
        exact ih _ (by simp)
      · rw [if_neg h2]
        exact ih _ (by simp)

private theorem destTriple0LastOfCons (f : List ℕ) (u v w n : ℕ)
    (uvns : List (ℕ × ℕ × ℕ)) :
    (destTriple0 f [some w] ((u, v, n) :: uvns)).getLastD none
      = (destTriple0 f [some v] uvns).getLastD none := by
  rw [destTriple0_cons_eq]
  dsimp only
  rw [if_neg (by simp : ([some w] : List (Option ℕ)) ≠ [])]
  rw [show (([some w] : List (Option ℕ)).getLastD none).getD 0 = w from rfl]
  have hcat : ∀ s : List (Option ℕ), s ≠ [] →
      (destTriple0 f (s ++ [some v]) uvns).getLastD none
        = (destTriple0 f [some v] uvns).getLastD none := by
    intro s hs
    rw [destTriple0Cat uvns f s [some v] (by simp)]
    exact getLastD_append_of_ne none s
      (destTriple0NeNil f uvns [some v] (by simp))
  by_cases h1 : w = u
  · rw [if_pos h1]
    exact hcat _ (by simp)
  · rw [if_neg h1]
    by_cases h2 : nextEl f w = u
    · rw [if_pos h2]
      exact hcat _ (by simp)
    · rw [if_neg h2]
      exact hcat _ (by simp)

private theorem getLast_eq_of_getLastD {β : Type} {l : List (Option β)} {a : β}
    (hne : l ≠ []) (h : l.getLastD none = some a) : l.getLast hne = some a := by
  have h2 : l.getLast? = some (some a) := by
    rw [List.getLastD_eq_getLast?] at h
    cases hl : l.getLast? with
    | none =>
      rw [hl] at h
      exact absurd h (by simp)
    | some z =>
      rw [hl] at h
      have hz : z = some a := by simpa using h
      rw [hz]
  rw [List.getLast?_eq_some_getLast hne] at h2
  exact Option.some.inj h2

private theorem eq_dropLast_append_of_getLastD {β : Type} {l : List (Option β)} {a : β}
    (hne : l ≠ []) (h : l.getLastD none = some a) :
    l = l.dropLast ++ [some a] := by
  conv_lhs => rw [← List.dropLast_concat_getLast hne]
  rw [getLast_eq_of_getLastD hne h]

private theorem take_one_eq {α : Type} (l : List α) (h : 0 < l.length) :
    l.take 1 = [l[0]'h] := by
  cases l with
  | nil => simp at h
  | cons a t => rfl

/-! ## §A `size_vs`（reduction3.hl:2055）

`destTripleFull` 三段账：初段 `sizeInitialSeg`、中段 `destTriple0` 前缀归纳
（`sizeDestTriple0Cons2` 走步 + `indexf_add_left` 链 + `hidxmid` 桥）、
末段 `sizeFinalSeg`；最后 `indexfPrev` 把 `indexf (next_el fx x) x fx`
化为 `fx.length - 1`。 -/

/-- HOL `size_vs`（reduction3.hl:2055；两行 `//` 注释前提不进陈述）。 -/
theorem sizeVs
    (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (L : fgraph ℕ) (N : List (List Dart)) (k : ℕ) (r : List Dart) (x : Dart)
    (fx : List Dart) (v : ℕ) (uvns : List (ℕ × ℕ × ℕ)) (vs : List (Option ℕ))
    (hgood : GoodList L) (hnodes : GoodNodesL L) (hres : IsRestrictedL L)
    (hprep : newvertexPrepped L N r x) (hmarked : Marked L N r x)
    (hnfin : ¬ finalList L r)
    (huvns : coreTripleV4 L N r x = uvns)
    (hvs : destTripleFull (core L r) v uvns = vs)
    (hk : transformCount L N r x = k)
    (hfx : findFaceDarts L x = fx)
    (hk0 : ¬ transformCount L N r x = 0)
    (hk0pos : 0 < transformCount L N r x)
    (hxprev : x.1 = prevEl (core L r) v)
    (hxmem : x ∈ fx) (hfxnd : fx.Nodup) (hfx1 : 1 ≤ fx.length)
    (hcore1 : 1 < (core L r).length)
    (hmono1 : ∀ i, i + 1 < k →
      indexf (ytrans L N r x 0) (ztrans L N r x i) fx ≤
        indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) fx)
    (hmono2 : ∀ i, i + 1 < k →
      indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) fx ≤
        indexf (ytrans L N r x 0) (ztrans L N r x (i + 1)) fx)
    (hmono3 : indexf (nextEl fx x) (ztrans L N r x (k - 1)) fx ≤
      indexf (nextEl fx x) x fx)
    (hmono4 : indexf (nextEl fx x) (ytrans L N r x 0) fx ≤
      indexf (nextEl fx x) (ztrans L N r x (k - 1)) fx)
    (hnextmem : nextEl fx x ∈ r)
    (hne0 : ∀ i, i < k → ytrans L N r x i ≠ ztrans L N r x i)
    (hzm : ∀ i, i < k → ztrans L N r x i ∈ r)
    (hym : ∀ i, i < k → ytrans L N r x i ∈ r)
    (hnextfx : nextEl fx x ∈ fx)
    (hyfx : ∀ i, i < k → ytrans L N r x i ∈ fx)
    (hzfx : ∀ i, i < k → ztrans L N r x i ∈ fx)
    (hcorend : (core L r).Nodup)
    (hnextv : (nextEl fx x).1 = v)
    (hcoreof : ∀ u ∈ r, u.1 ∈ core L r)
    (hidx0 : indexf v (ytrans L N r x 0).1 (core L r) =
      indexf (nextEl fx x) (ytrans L N r x 0) fx)
    (hidxlast : indexf (ztrans L N r x (k - 1)).1 x.1 (core L r) =
      indexf (ztrans L N r x (k - 1)) x fx)
    (hidxmid : ∀ i, i + 1 < k →
      indexf (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 (core L r) =
        indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) fx) :
    fx.length = vs.length := by
  -- 0. 基本事实
  have hlen : uvns.length = k := by rw [← huvns, coreTripleV4_length, hk]
  have hkpos : 0 < k := by rw [← hk]; exact hk0pos
  have hne : uvns ≠ [] := by
    intro h
    rw [h] at hlen
    simp only [List.length_nil] at hlen
    omega
  -- 1. 每个下标处的 uvns 项
  have hget : ∀ i (hi : i < k),
      uvns[i]'(by rw [hlen]; exact hi) =
        ((ytrans L N r x i).1, (ztrans L N r x i).1,
          (between fx (ytrans L N r x i) (ztrans L N r x i)).length) := by
    intro i hi
    have hcore := elCoreTriple L N r x i (by rw [hk]; exact hi)
    rw [hfx] at hcore
    exact (getElem_eq_of_eq huvns i (by rw [coreTripleV4_length]; rw [hk]; exact hi)
      (by rw [hlen]; exact hi)).symm.trans hcore
  -- 2. 首项与末项投影
  have hheadD : uvns.headD (0, 0, 0) = uvns[0]'(by rw [hlen]; exact hkpos) := by
    cases uvns with
    | nil => exact absurd rfl hne
    | cons a t => rfl
  have huHead : (uvns.headD (0, 0, 0)).1 = (ytrans L N r x 0).1 := by
    rw [hheadD, hget 0 hkpos]
  have hlastD : (uvns.getLastD (0, 0, 0)).2.1 = (ztrans L N r x (k - 1)).1 := by
    rw [← huvns]
    rw [lastCoreTriple L N r x (k - 1) hk0 (by rw [hk])]
  -- 3. take 前缀归纳
  have key : ∀ i, i + 1 ≤ k →
      (destTriple0 (core L r) [] (uvns.take (i + 1))).length
          = 1 + indexf (ytrans L N r x 0) (ztrans L N r x i) fx ∧
        (destTriple0 (core L r) [] (uvns.take (i + 1))).getLastD none
          = some (ztrans L N r x i).1 := by
    intro i
    induction i with
    | zero =>
      intro h1k
      simp only [Nat.zero_add]
      have h0len : 0 < uvns.length := by rw [hlen]; omega
      rw [take_one_eq uvns h0len, hget 0 hkpos]
      rw [show destTriple0 (core L r) []
            [((ytrans L N r x 0).1, (ztrans L N r x 0).1,
              (between fx (ytrans L N r x 0) (ztrans L N r x 0)).length)]
          = destTriple0 (core L r)
            ([some (ytrans L N r x 0).1]
              ++ List.replicate (between fx (ytrans L N r x 0) (ztrans L N r x 0)).length
                (none : Option ℕ)
              ++ [some (ztrans L N r x 0).1]) [] from rfl]
      rw [destTriple0Nil]
      constructor
      · have hbet : (between fx (ytrans L N r x 0) (ztrans L N r x 0)).length
            = indexf (ytrans L N r x 0) (ztrans L N r x 0) fx - 1 :=
          sizeBetwnChain hfxnd (hyfx 0 hkpos) (hzfx 0 hkpos) (hne0 0 hkpos)
        have hpos : 0 < indexf (ytrans L N r x 0) (ztrans L N r x 0) fx :=
          Nat.pos_of_ne_zero (fun hz =>
            hne0 0 hkpos (indexf_eq_zero (hyfx 0 hkpos) (hzfx 0 hkpos) hz))
        simp only [List.length_append, List.length_cons, List.length_replicate,
          List.length_nil]
        omega
      · rw [List.getLastD_concat]
    | succ i ih =>
      intro hik
      have hi1 : i + 1 ≤ k := by omega
      have hi1lt : i + 1 < k := by omega
      have hilt : i < k := by omega
      obtain ⟨hPlen, hPlast⟩ := ih hi1
      have hgeti : uvns[i + 1]'(by rw [hlen]; exact hi1lt) =
          ((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
            (between fx (ytrans L N r x (i + 1)) (ztrans L N r x (i + 1))).length) :=
        hget (i + 1) hi1lt
      have htake : uvns.take (i + 1 + 1)
          = uvns.take (i + 1) ++ [uvns[i + 1]'(by rw [hlen]; exact hi1lt)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by rw [hlen]; exact hi1lt)]
        rfl
      have hL1ne : destTriple0 (core L r) [] (uvns.take (i + 1)) ≠ [] := by
        intro h
        rw [h] at hPlen
        simp only [List.length_nil] at hPlen
        omega
      have hL1eq : destTriple0 (core L r) [] (uvns.take (i + 1))
          = (destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
            ++ [some (ztrans L N r x i).1] :=
        eq_dropLast_append_of_getLastD hL1ne hPlast
      have hdropLen : (destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast.length
          = indexf (ytrans L N r x 0) (ztrans L N r x i) fx := by
        have h := congrArg List.length hL1eq
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        omega
      have ha_ne : uvns.take (i + 1) ≠ [] := by
        intro h
        have hc := congrArg List.length h
        rw [List.length_take, hlen, Nat.min_eq_left hi1] at hc
        simp at hc
      have hsplit : destTriple0 (core L r) ([].flatten) (uvns.take (i + 1))
          = (destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
            ++ [some (ztrans L N r x i).1] := by
        show destTriple0 (core L r) [] (uvns.take (i + 1)) = _
        exact hL1eq
      have hcat2 : destTriple0 (core L r) []
            (uvns.take (i + 1) ++ [uvns[i + 1]'(by rw [hlen]; exact hi1lt)])
          = (destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
            ++ destTriple0 (core L r) [some (ztrans L N r x i).1]
              [uvns[i + 1]'(by rw [hlen]; exact hi1lt)] :=
        destTriple0Cat2 (core L r) [] (uvns.take (i + 1))
          [uvns[i + 1]'(by rw [hlen]; exact hi1lt)]
          (destTriple0 (core L r) [] (uvns.take (i + 1))).dropLast
          (ztrans L N r x i).1 ha_ne (fun h => absurd rfl h) hsplit
      rw [htake, hcat2, hgeti]
      -- 走步项长度/末元
      have hmu : (ytrans L N r x (i + 1)).1 ∈ core L r := hcoreof _ (hym (i + 1) hi1lt)
      have hmv : (ztrans L N r x (i + 1)).1 ∈ core L r := hcoreof _ (hzm (i + 1) hi1lt)
      have hmw : (ztrans L N r x i).1 ∈ core L r := hcoreof _ (hzm i hilt)
      have hDlen : (destTriple0 (core L r) [some (ztrans L N r x i).1]
          [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
            (between fx (ytrans L N r x (i + 1)) (ztrans L N r x (i + 1))).length)]).length
          = (between fx (ytrans L N r x (i + 1)) (ztrans L N r x (i + 1))).length
            + 1 + indexf (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 (core L r)
            + 1 := by
        have h := sizeDestTriple0Cons2 (core L r) (ytrans L N r x (i + 1)).1
          (ztrans L N r x (i + 1)).1 (ztrans L N r x i).1
          (between fx (ytrans L N r x (i + 1)) (ztrans L N r x (i + 1))).length
          [] hcorend hcore1 hmu hmv hmw
        rw [h]
        rfl
      have hDlast : (destTriple0 (core L r) [some (ztrans L N r x i).1]
          [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
            (between fx (ytrans L N r x (i + 1)) (ztrans L N r x (i + 1))).length)]).getLastD
            none = some (ztrans L N r x (i + 1)).1 := by
        rw [destTriple0LastOfCons]
        rfl
      have hDne : (destTriple0 (core L r) [some (ztrans L N r x i).1]
          [((ytrans L N r x (i + 1)).1, (ztrans L N r x (i + 1)).1,
            (between fx (ytrans L N r x (i + 1)) (ztrans L N r x (i + 1))).length)]) ≠ [] :=
        destTriple0NeNil (core L r) _ _ (by simp)
      have hbet : (between fx (ytrans L N r x (i + 1)) (ztrans L N r x (i + 1))).length
          = indexf (ytrans L N r x (i + 1)) (ztrans L N r x (i + 1)) fx - 1 :=
        sizeBetwnChain hfxnd (hyfx (i + 1) hi1lt) (hzfx (i + 1) hi1lt)
          (hne0 (i + 1) hi1lt)
      have hpos : 0 < indexf (ytrans L N r x (i + 1)) (ztrans L N r x (i + 1)) fx :=
        Nat.pos_of_ne_zero (fun hz =>
          hne0 (i + 1) hi1lt (indexf_eq_zero (hyfx (i + 1) hi1lt) (hzfx (i + 1) hi1lt) hz))
      have hmid : indexf (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 (core L r)
          = indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) fx := hidxmid i hi1lt
      have he1 := indexf_add_left (hyfx 0 hkpos) (hzfx i hilt) (hyfx (i + 1) hi1lt)
        (hmono1 i hi1lt)
      have he2 := indexf_add_left (hyfx 0 hkpos) (hyfx (i + 1) hi1lt) (hzfx (i + 1) hi1lt)
        (hmono2 i hi1lt)
      constructor
      · rw [List.length_append, hdropLen, hDlen, hmid]
        omega
      · rw [getLastD_append_of_ne none _ hDne, hDlast]
  -- 4. 三段装配
  have hvcore : v ∈ core L r := by
    rw [← hnextv]
    exact hcoreof _ hnextmem
  have huHeadcore : (uvns.headD (0, 0, 0)).1 ∈ core L r := by
    rw [huHead]
    exact hcoreof _ (hym 0 hkpos)
  have hvLastcore : (uvns.getLastD (0, 0, 0)).2.1 ∈ core L r := by
    rw [hlastD]
    exact hcoreof _ (hzm (k - 1) (by omega))
  have hprevcore : prevEl (core L r) v ∈ core L r :=
    Kepler.Text.TameLp.prevEl_mem_of_mem hvcore
  have hdest : destTripleFull (core L r) v uvns =
      (if v = (uvns.headD (0, 0, 0)).1 then []
        else some v :: (between (core L r) v (uvns.headD (0, 0, 0)).1).map some)
      ++ destTriple0 (core L r) [] uvns
      ++ (if (uvns.getLastD (0, 0, 0)).2.1 = prevEl (core L r) v then []
        else (between (core L r) (uvns.getLastD (0, 0, 0)).2.1
          (prevEl (core L r) v)).map some ++ [some (prevEl (core L r) v)]) := by
    simp [destTripleFull]
  have hinitA : (if v = (uvns.headD (0, 0, 0)).1 then []
        else some v :: (between (core L r) v (uvns.headD (0, 0, 0)).1).map some).length
      = indexf (nextEl fx x) (ytrans L N r x 0) fx := by
    have h0 : (if v = (uvns.headD (0, 0, 0)).1 then []
          else some v :: (between (core L r) v (uvns.headD (0, 0, 0)).1).map some).length
        = indexf v (uvns.headD (0, 0, 0)).1 (core L r) :=
      sizeInitialSeg (core L r) (uvns.headD (0, 0, 0)).1 v
        (if v = (uvns.headD (0, 0, 0)).1 then []
          else some v :: (between (core L r) v (uvns.headD (0, 0, 0)).1).map some)
        hvcore huHeadcore hcorend rfl
    rw [h0, huHead, hidx0]
  have hlastC : (if (uvns.getLastD (0, 0, 0)).2.1 = prevEl (core L r) v then []
        else (between (core L r) (uvns.getLastD (0, 0, 0)).2.1
          (prevEl (core L r) v)).map some ++ [some (prevEl (core L r) v)]).length
      = indexf (ztrans L N r x (k - 1)) x fx := by
    have h0 : (if (uvns.getLastD (0, 0, 0)).2.1 = prevEl (core L r) v then []
          else (between (core L r) (uvns.getLastD (0, 0, 0)).2.1
            (prevEl (core L r) v)).map some ++ [some (prevEl (core L r) v)]).length
        = indexf (uvns.getLastD (0, 0, 0)).2.1 (prevEl (core L r) v) (core L r) :=
      sizeFinalSeg (core L r) (uvns.getLastD (0, 0, 0)).2.1 (prevEl (core L r) v)
        (if (uvns.getLastD (0, 0, 0)).2.1 = prevEl (core L r) v then []
          else (between (core L r) (uvns.getLastD (0, 0, 0)).2.1
            (prevEl (core L r) v)).map some ++ [some (prevEl (core L r) v)])
        hvLastcore hprevcore hcorend rfl
    rw [h0, hlastD, ← hxprev, hidxlast]
  have hmidLen : (destTriple0 (core L r) [] uvns).length
      = 1 + indexf (ytrans L N r x 0) (ztrans L N r x (k - 1)) fx := by
    have htakek : uvns.take k = uvns := by
      rw [← hlen, List.take_length]
    have hk1 : (k - 1) + 1 = k := by omega
    have h := (key (k - 1) (by omega)).1
    rwa [hk1, htakek] at h
  have he1 := indexf_add_left hnextfx (hyfx 0 hkpos) (hzfx (k - 1) (by omega)) hmono4
  have he2 := indexf_add_left hnextfx (hzfx (k - 1) (by omega)) hxmem hmono3
  have he3 : indexf (nextEl fx x) x fx = fx.length - 1 := by
    rw [indexf_eq_spine]
    exact Kepler.Text.TameSpine.indexfPrev hxmem hnextfx hfxnd rfl
  rw [← hvs, hdest, List.length_append, List.length_append, hinitA, hlastC, hmidLen]
  omega

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.sizeVs
