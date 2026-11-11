/-
  Kepler.Text.Reduction5J5UvnsU2 — U2 有序支（k3UvnsSlot 第一合取）。

  本文件交付 **轨道/段内引擎**（U2 的 ① 支）：
  · `IndexfStrict`：`indexf v` 在 `l` 上逐位严格递增；
  · `indexfNextElSucc`：`nextEl s a = b` 且 `v ≠ b` 时 `indexf v a + 1 = indexf v b`
    （HOL `indexf_ifbetwn` 的步进引擎；由 `indexfCompl`/`indexfN`/`indexf_add_sum` 组合，
    对应在库 Dart 版 `TameSpine.indexfPrevSucc` 的 ℕ 重落）；
  · `indexfStrictOfSteps`：若 `l` 的每个相邻对要么是「非回卷 `nextEl` 步」、
    要么直接满足严格递增，则 `IndexfStrict` 整链成立（粘合接口）；
  · `arcIndexfStrict`：`a :: between s a b` 的轨道段内严格递增
    （`betwnOrbit` + `indexfNextElSucc`；`v ∉ between` 保证不回卷）。

  ┌─ 精确目标（U2 全句；与 MainWiring `uvnsMainOfU2` 的 `hU2` 逐字同形）─
  │ `theorem uvnsVsOrdered (L) (hL) (hgn) (hres) {N r x k}`
  │   `(hm) (hnf) (hk) {v} (hprev) :`
  │   `∀ i, i + 1 < ((destTripleFull (core L r) v (coreTripleV4 L N r x)).filterMap id).length →`
  │     `indexf v ((...).getD i 0) (core L r) <`
  │     `indexf v ((...).getD (i + 1) 0) (core L r)`
  │ 无 hnNil/hnFy/hnZx/hIdxSnd 参数——三者在本文件 §2 已落为库内件的 `v` 形
  │ （`indexfYtranLtZtranOfPrev` / `notMemIfbetwnFyOfPrev` / `notMemIfbetwnZxOfPrev`）。
  │ 喂法：对 `vs` 的相邻 Some 对建立
  │   `nextEl step ∧ v ≠ target`（`betwnOrbit` + 上述端点排除）
  │   或 `hIdxSnd`（跨 `replicate n none` 的 (y_i,z_i) 兜底），
  │ 再经 `indexfStrictOfSteps` 收口。
  └────────────────────────────────────────────────────────────────

  **U2 余下 glue（本文件未含，见 DELIVERY_U2）**：
  `vs' = filterMap id vs` 的段分解（init/mid/final + 每 triple 的
  `[some y_i] ++ ns ++ [some z_i]`）与跨 none 的 (y_i,z_i) 兜底（`hIdxSnd`），
  喂给 `indexfStrictOfSteps` 即收口。

  纪律：零公理、零占位证明、零反射式判定；不改已落库陈述/定义；主仓 tracked 零写入。
-/
import Kepler.Text.Reduction5J5UvnsFinal
import Kepler.Text.Reduction5J5UvnsMainWiring
import Kepler.Text.TameSpine.Reduction3J5IndexfPrevSucc
import Kepler.Text.Reduction5J5K4IndexSndX
import Kepler.Text.Reduction4K4C0R2d

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- `indexf v` 在 `l` 上逐位严格递增（`l` 的元素视为 `core` 的成员）。 -/
def IndexfStrict (v : ℕ) (s : List ℕ) (l : List ℕ) : Prop :=
  ∀ j, j + 1 < l.length →
    indexf v (l.getD j 0) s < indexf v (l.getD (j + 1) 0) s

/-- `nextEl` 的单步：`v ≠ b` 时 `indexf v a + 1 = indexf v b`
（Dart 版 `TameSpine.indexfPrevSucc` 的 ℕ 重落；去实例桥，`nextEl` 单实例）。 -/
theorem indexfNextElSucc {s : List ℕ} {v a b : ℕ}
    (hv : v ∈ s) (ha : a ∈ s) (hnd : s.Nodup) (hne : v ≠ b)
    (hnext : nextEl s a = b) :
    indexf v a s + 1 = indexf v b s := by
  have hb : b ∈ s := by rw [← hnext]; exact Kepler.Text.TameLp.nextEl_mem_of_mem ha
  have h1len : 1 < s.length := by
    rcases Nat.lt_or_ge 1 s.length with h | h
    · exact h
    · -- s.length ≤ 1：v, b ∈ s 且 v ≠ b 矛盾
      have hsub : s.length ≤ 1 := by omega
      have hv1 : s.length = 1 := by
        have hpos : 0 < s.length := List.length_pos_of_mem hv
        omega
      obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hv1
      simp at hv hb
      omega
  have hab1 : indexf a b s = 1 :=
    Kepler.Text.MoreLemma2Island1.nextElIndexf ha hb hnd hnext h1len
  by_cases hf1 : indexf v b s = 1
  · -- f = 1：b = nextEl v，前驱唯一性给 a = v，故 indexf v a = 0
    have hidx := Kepler.Text.MoreLemma2Island1.indexfN hv hb hnd
    rw [hf1, Function.iterate_one] at hidx
    have hinj : ∀ {x y : ℕ}, x ∈ s → y ∈ s → nextEl s x = nextEl s y → x = y := by
      intro x y hx hy hxy
      calc x = prevEl s (nextEl s x) := (Kepler.Text.TameLp.prevEl_nextEl hnd hx).symm
        _ = prevEl s (nextEl s y) := by rw [hxy]
        _ = y := Kepler.Text.TameLp.prevEl_nextEl hnd hy
    have hav : a = v := hinj ha hv (hnext.trans hidx.symm)
    have he0 : indexf v a s = 0 := by rw [hav]; exact Kepler.Text.Reduction4.indexfRefl hv
    omega
  · -- f ≠ 1 且 f ≠ 0 ⇒ f ≥ 2：互补 + 加法
    have hfne : indexf v b s ≠ 0 := by
      intro h0
      exact hne (Kepler.Text.Reduction4.indexf_eq_zero hv hb h0)
    by_cases hva : v = a
    · have hf1' : indexf v b s = 1 := by simpa [hva] using hab1
      exact absurd hf1' hf1
    · have hcompl1 : indexf v a s + indexf a v s = s.length :=
        Kepler.Text.Reduction5.indexfCompl hv ha hva
      have hcompl2 : indexf v b s + indexf b v s = s.length :=
        Kepler.Text.Reduction5.indexfCompl hv hb hne
      have hbv : indexf b v s = s.length - indexf v b s := by omega
      have hav' : indexf a v s = s.length - indexf v a s := by omega
      have hsum_lt : indexf a b s + indexf b v s < s.length := by
        rw [hab1, hbv]
        omega
      have hsum := Kepler.Text.Reduction4.indexf_add_sum ha hb hv hsum_lt
      rw [hab1, hbv, hav'] at hsum
      omega

/-- **粘合接口**：`l` 的每个相邻对要么是非回卷 `nextEl` 步、要么直接严格增，
则整链 `IndexfStrict`。 -/
theorem indexfStrictOfSteps {s : List ℕ} {v : ℕ}
    (hv : v ∈ s) (hnd : s.Nodup)
    {l : List ℕ} (hl : ∀ t ∈ l, t ∈ s)
    (hstep : ∀ j, j + 1 < l.length →
      (nextEl s (l.getD j 0) = l.getD (j + 1) 0 ∧ v ≠ l.getD (j + 1) 0) ∨
        indexf v (l.getD j 0) s < indexf v (l.getD (j + 1) 0) s) :
    IndexfStrict v s l := by
  intro j hj
  rcases hstep j hj with ⟨hnext, hne⟩ | hlt
  · have h := indexfNextElSucc hv (hl _ (by
      have hj' : j < l.length := by omega
      rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hj' 0]
      exact List.getElem_mem _)) hnd hne hnext
    omega
  · exact hlt

/-- **轨道段内严格递增**：`a :: between s a b` 的相邻项 `indexf v` 严格增，
`v ∉ between s a b`（不回卷；对应 `hnFy`/`hnZx` 的端点排除）。 -/
theorem arcIndexfStrict {s : List ℕ} {v a b : ℕ}
    (hv : v ∈ s) (ha : a ∈ s) (hb : b ∈ s) (hnd : s.Nodup)
    (hne : a ≠ b) (hvarc : v ∉ between s a b) :
    IndexfStrict v s (a :: between s a b) := by
  intro j hj
  set l : List ℕ := a :: between s a b with hl
  have hlen : j + 1 < l.length := hj
  -- 目标位置 = between[j]，源位置 = (nextEl)^[j] a
  have hsrc : l.getD j 0 = (nextEl s)^[j] a := by
    cases j with
    | zero => simp [hl]
    | succ k =>
      have hkb : k < (between s a b).length := by
        simp only [hl, List.length_cons] at hlen
        omega
      rw [hl, List.getD_cons_succ]
      rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hkb 0]
      exact Kepler.Text.TameSpine.betwnOrbit hne hnd ha hb hkb
  have hdst : l.getD (j + 1) 0 = (nextEl s)^[j + 1] a := by
    have hjb : j < (between s a b).length := by
      simp only [hl, List.length_cons] at hlen
      omega
    rw [hl, List.getD_cons_succ]
    rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hjb 0]
    exact Kepler.Text.TameSpine.betwnOrbit hne hnd ha hb hjb
  rw [hsrc, hdst]
  -- 源/目标成员
  have hsrcmem : (nextEl s)^[j] a ∈ s := by
    cases j with
    | zero => exact ha
    | succ k =>
      have hkb : k < (between s a b).length := by
        simp only [hl, List.length_cons] at hlen
        omega
      rw [show (nextEl s)^[k + 1] a = (between s a b)[k]'hkb from
        (Kepler.Text.TameSpine.betwnOrbit hne hnd ha hb hkb).symm]
      exact Kepler.Text.Reduction5.betwnMem (List.getElem_mem hkb)
  have hdstmem : (nextEl s)^[j + 1] a ∈ s := by
    have hjb : j < (between s a b).length := by
      simp only [hl, List.length_cons] at hlen
      omega
    rw [show (nextEl s)^[j + 1] a = (between s a b)[j]'hjb from
      (Kepler.Text.TameSpine.betwnOrbit hne hnd ha hb hjb).symm]
    exact Kepler.Text.Reduction5.betwnMem (List.getElem_mem hjb)
  have hne_v : v ≠ (nextEl s)^[j + 1] a := by
    intro h
    apply hvarc
    have hjb : j < (between s a b).length := by
      simp only [hl, List.length_cons] at hlen
      omega
    rw [h, ← Kepler.Text.TameSpine.betwnOrbit hne hnd ha hb hjb]
    exact List.getElem_mem hjb
  have hstep : nextEl s ((nextEl s)^[j] a) = (nextEl s)^[j + 1] a := by
    rw [Function.iterate_succ_apply']
  have h := indexfNextElSucc hv hsrcmem hnd hne_v hstep
  omega

/-! ## §2 U2 glue 的库内三件（无条件形；`v = x.2` 后直投在库定理） -/

/-- `hIdxSnd` 的 `v` 形（库内 `indexSndX`；`hprev` 给 `v = x.2`）。 -/
theorem indexfYtranLtZtranOfPrev (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    {v : ℕ} (hprev : (prevEl (core L r) v, v) = x) :
    ∀ i, i < k →
      indexf v (ytrans L N r x i).1 (core L r)
        < indexf v (ztrans L N r x i).1 (core L r) := by
  intro i hi
  have hv : v = x.2 := congrArg Prod.snd hprev
  rw [hv]
  exact indexSndX L hL hgn hres hm hnf hk i hi

/-- `hnFy` 的 `v` 形（库内 `finalAssumptionNotMemSndXFy`；端点排除）。 -/
theorem notMemIfbetwnFyOfPrev (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    {v : ℕ} (hprev : (prevEl (core L r) v, v) = x) :
    ∀ i, i < k → 1 < (ftrans L N r x i ::
        ifbetwn (core L r) (ftrans L N r x i) (ytrans L N r x i).1).length →
      v ∉ ifbetwn (core L r) (ftrans L N r x i) (ytrans L N r x i).1 := by
  intro i hi hlt
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hv : v = x.2 := congrArg Prod.snd hprev
  rw [hv]
  exact Kepler.Text.Reduction4.finalAssumptionNotMemSndXFy L hL hgn hres haq hm hnf hk i
    ⟨hi, hlt⟩

/-- `hnZx` 的 `v` 形（库内 `finalAssumptionNotMemSndXZx`；末段端点排除）。 -/
theorem notMemIfbetwnZxOfPrev (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    {v : ℕ} (hprev : (prevEl (core L r) v, v) = x) :
    v ∉ ifbetwn (core L r) (ztrans L N r x (k - 1)).1 x.1 := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hv : v = x.2 := congrArg Prod.snd hprev
  rw [hv]
  exact Kepler.Text.Reduction4.finalAssumptionNotMemSndXZx L hL hgn hres haq hm hnf hk

/-- **粘合**：两段各自 `IndexfStrict`，且段末 < 段首 ⇒ 拼接后 `IndexfStrict`。 -/
theorem IndexfStrict.append {l1 l2 : List ℕ} {v : ℕ} {s : List ℕ}
    (h1 : IndexfStrict v s l1) (h2 : IndexfStrict v s l2)
    (hj : l1 ≠ [] → l2 ≠ [] →
      indexf v (l1.getD (l1.length - 1) 0) s < indexf v (l2.getD 0 0) s) :
    IndexfStrict v s (l1 ++ l2) := by
  intro j hjlen
  rw [List.length_append] at hjlen
  by_cases hlt : j + 1 < l1.length
  · rw [List.getD_append l1 l2 0 j (by omega), List.getD_append l1 l2 0 (j + 1) hlt]
    exact h1 j hlt
  · by_cases heq : j + 1 = l1.length
    · have hjl : j < l1.length := by omega
      rw [List.getD_append l1 l2 0 j hjl,
        List.getD_append_right l1 l2 0 (j + 1) (by omega),
        show j + 1 - l1.length = 0 from by omega,
        show j = l1.length - 1 from by omega]
      refine hj (by rintro rfl; simp at hjl)
        (by intro h; rw [h] at hjlen; simp only [List.length_nil, Nat.add_zero] at hjlen; omega)
    · have hle : l1.length ≤ j := by omega
      rw [List.getD_append_right l1 l2 0 j hle,
        List.getD_append_right l1 l2 0 (j + 1) (by omega)]
      have hsucc : j + 1 - l1.length = (j - l1.length) + 1 := by omega
      simpa only [hsucc] using h2 (j - l1.length) (by omega)

/-! ## §3 `destTriple0` 段分解（U2 收口的结构 glue） -/

/-- `destTriple0` 的 cons 展开（与在库 T2/T3/T6C 私件同体）。 -/
private theorem destTriple0_cons_eq (f : List ℕ) (s : List (Option ℕ)) (u v n : ℕ)
    (ts : List (ℕ × ℕ × ℕ)) :
    Kepler.Text.Reduction3.destTriple0 f s ((u, v, n) :: ts) =
      (let ns := List.replicate n (none : Option ℕ)
       if s = [] then Kepler.Text.Reduction3.destTriple0 f ([some u] ++ ns ++ [some v]) ts
       else
         let u0 := (s.getLastD none).getD 0
         if u0 = u then Kepler.Text.Reduction3.destTriple0 f (s ++ ns ++ [some v]) ts
         else if nextEl f u0 = u then
           Kepler.Text.Reduction3.destTriple0 f (s ++ [some u] ++ ns ++ [some v]) ts
         else
           Kepler.Text.Reduction3.destTriple0 f
             (s ++ (between f u0 u).map some ++ [some u] ++ ns ++ [some v]) ts) := rfl

/-- `destTriple0` 的 append 分解：`destTriple0 f s (a++b) = destTriple0 f (destTriple0 f s a) b`。 -/
private theorem destTriple0Append (f : List ℕ) (s : List (Option ℕ))
    (a b : List (ℕ × ℕ × ℕ)) :
    Kepler.Text.Reduction3.destTriple0 f s (a ++ b)
      = Kepler.Text.Reduction3.destTriple0 f
          (Kepler.Text.Reduction3.destTriple0 f s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨u, v, n⟩ := t
    rw [List.cons_append, destTriple0_cons_eq, destTriple0_cons_eq]
    dsimp only
    by_cases hs : s = []
    · rw [hs]
      simp only [List.nil_append]
      exact ih _
    · simp only [if_neg hs]
      by_cases h1 : (s.getLastD none).getD 0 = u
      · simp only [if_pos h1]
        exact ih _
      · simp only [if_neg h1]
        by_cases h2 : nextEl f ((s.getLastD none).getD 0) = u
        · simp only [if_pos h2]
          exact ih _
        · simp only [if_neg h2]
          exact ih _

/-- `destTriple0` 单步新增段（`sofar` 之后的增量）。 -/
private def stepSeg (f : List ℕ) (s : List (Option ℕ)) (u v n : ℕ) :
    List (Option ℕ) :=
  let ns := List.replicate n (none : Option ℕ)
  if s = [] then [some u] ++ ns ++ [some v]
  else
    let u0 := (s.getLastD none).getD 0
    if u0 = u then ns ++ [some v]
    else if nextEl f u0 = u then [some u] ++ ns ++ [some v]
    else (between f u0 u).map some ++ [some u] ++ ns ++ [some v]

/-- 单段形：`destTriple0 f s [t] = s ++ stepSeg f s t.1 t.2.1 t.2.2`。 -/
private theorem destTriple0_single (f : List ℕ) (s : List (Option ℕ)) (u v n : ℕ) :
    Kepler.Text.Reduction3.destTriple0 f s [(u, v, n)] = s ++ stepSeg f s u v n := by
  rw [destTriple0_cons_eq]
  dsimp only
  simp only [Kepler.Text.Reduction3.destTriple0.eq_1]
  simp only [stepSeg]
  by_cases hs : s = []
  · subst hs
    simp
  · simp only [if_neg hs]
    by_cases h1 : (s.getLastD none).getD 0 = u
    · simp only [if_pos h1, List.append_assoc]
    · simp only [if_neg h1]
      by_cases h2 : nextEl f ((s.getLastD none).getD 0) = u
      · simp only [if_pos h2, List.append_assoc]
      · simp only [if_neg h2, List.append_assoc]

private theorem stepSeg_ne_nil (f : List ℕ) (s : List (Option ℕ)) (u v n : ℕ) :
    stepSeg f s u v n ≠ [] := by
  simp only [stepSeg]
  split
  · simp
  · split
    · simp
    · split <;> simp

private theorem getLastD_append_ne {α : Type} (d : α) (a : List α) {b : List α}
    (h : b ≠ []) : (a ++ b).getLastD d = b.getLastD d := by
  induction a generalizing d with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.getLastD_cons, ih]
    cases b with
    | nil => exact absurd rfl h
    | cons y ys => rw [List.getLastD_cons, List.getLastD_cons]

private theorem stepSeg_getLastD (f : List ℕ) (s : List (Option ℕ)) (u v n : ℕ) :
    (stepSeg f s u v n).getLastD none = some v := by
  simp only [stepSeg]
  split
  · rw [List.getLastD_concat]
  · split
    · rw [List.getLastD_concat]
    · split <;> rw [List.getLastD_concat]

private theorem stepSeg_filterMap_nil (f : List ℕ) (u v n : ℕ) :
    (stepSeg f [] u v n).filterMap id = [u, v] := by
  simp [stepSeg]

private theorem stepSeg_filterMap_last (f : List ℕ) (s : List (Option ℕ)) {u0 : ℕ}
    (hlast : s.getLastD none = some u0) (u v n : ℕ) :
    (stepSeg f s u v n).filterMap id
      = if u0 = u then [v]
        else if nextEl f u0 = u then [u, v]
        else between f u0 u ++ [u, v] := by
  by_cases hs : s = []
  · rw [hs] at hlast
    simp at hlast
  · simp only [stepSeg]
    rw [if_neg hs, hlast]
    simp only [Option.getD_some]
    split
    · simp
    · split <;> simp

/-- 尾段成员保持：`IndexfStrict` 的后缀仍 `IndexfStrict`。 -/
private theorem IndexfStrict.tail {a : ℕ} {l : List ℕ} {v : ℕ} {s : List ℕ}
    (h : IndexfStrict v s (a :: l)) : IndexfStrict v s l := by
  intro j hj
  have h1 := h (j + 1) (by simpa using hj)
  simpa only [List.getD_cons_succ] using h1

/-- 追加单点。 -/
private theorem IndexfStrict.snoc {l : List ℕ} {b : ℕ} {v : ℕ} {s : List ℕ}
    (h : IndexfStrict v s l)
    (hb : l ≠ [] → indexf v (l.getD (l.length - 1) 0) s < indexf v b s) :
    IndexfStrict v s (l ++ [b]) := by
  apply IndexfStrict.append h (l2 := [b])
  · intro j hj
    simp at hj
  · intro hl _
    have := hb hl
    simpa using this

/-- 前插单点。 -/
private theorem IndexfStrict.cons {a : ℕ} {l : List ℕ} {v : ℕ} {s : List ℕ}
    (h : indexf v a s < indexf v (l.getD 0 0) s) (hl : IndexfStrict v s l) :
    IndexfStrict v s (a :: l) := by
  have happ : (a :: l) = [a] ++ l := rfl
  rw [happ]
  apply IndexfStrict.append (l1 := [a]) (fun j hj => by simp at hj) hl
  intro _ _
  simpa using h

/-- `snoc` 末位取值。 -/
private theorem getD_snoc_last (l : List ℕ) (b : ℕ) :
    (l ++ [b]).getD ((l ++ [b]).length - 1) 0 = b := by
  rw [List.getD_append_right l [b] 0 _ (by simp)]
  have h0 : (l ++ [b]).length - 1 - l.length = 0 := by simp
  rw [h0]
  rfl

/-- **弧尾段严格增**：`between s a b ++ [b]` 的 `indexf v` 逐位严格增
（`v ∉ between s a b ++ [b]`；`betwnOrbit` 段内 + `nextLastBetwn` 末步）。 -/
theorem arcSnocIndexfStrict {s : List ℕ} {v a b : ℕ}
    (hv : v ∈ s) (ha : a ∈ s) (hb : b ∈ s) (hnd : s.Nodup)
    (hne : a ≠ b) (hvnot : v ∉ between s a b ++ [b]) :
    IndexfStrict v s (between s a b ++ [b]) := by
  have hvbet : v ∉ between s a b := fun h => hvnot (List.mem_append_left _ h)
  have hvb : v ≠ b := fun h => hvnot (by rw [h]; exact List.mem_append_right _ (by simp))
  have harc := arcIndexfStrict hv ha hb hnd hne hvbet
  have htail : IndexfStrict v s (between s a b) := IndexfStrict.tail harc
  by_cases hbet : between s a b = []
  · rw [hbet]
    intro j hj
    simp at hj
  · apply IndexfStrict.snoc htail
    intro _
    have hbetne : between s a b ≠ [] := hbet
    have hlast := Kepler.Text.Reduction5.nextLastBetwn ha hb hnd hne hbetne
    have hg : (between s a b).getD ((between s a b).length - 1) 0
        = (between s a b).getLast hbetne := by
      rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt (by
        have hpos : 0 < (between s a b).length := List.length_pos_of_ne_nil hbetne
        omega) 0]
      exact (List.getLast_eq_getElem hbetne).symm
    have hsrc : (between s a b).getD ((between s a b).length - 1) 0 ∈ s := by
      rw [hg]
      exact Kepler.Text.Reduction5.betwnMem (List.getLast_mem hbetne)
    have hstep := indexfNextElSucc hv hsrc hnd hvb (by rw [hg]; exact hlast)
    omega

/-- 非空表上 `getLastD` 与默认值无关。 -/
private theorem getLastD_default_eq {α : Type} {l : List α} (h : l ≠ []) (d e : α) :
    l.getLastD d = l.getLastD e := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  rfl

/-- 末项为 `some w` ⇒ `filterMap id` 非空。 -/
private theorem filterMap_ne_nil_of_last_some {l : List (Option ℕ)} {w : ℕ}
    (h : l.getLastD none = some w) : l.filterMap id ≠ [] := by
  induction l with
  | nil => simp at h
  | cons o os ih =>
    cases os with
    | nil =>
      have ho : o = some w := by simpa using h
      rw [ho]
      simp
    | cons o' os' =>
      have h' : (o' :: os').getLastD none = some w := by
        rw [List.getLastD_cons] at h
        rwa [← getLastD_default_eq (l := o' :: os') (by simp) none o] at h
      cases o with
      | none => simpa [List.filterMap_cons] using ih h'
      | some a =>
        rw [List.filterMap_cons]
        simp

/-- 末项为 `some w` ⇒ `filterMap id` 的末值 = `w`。 -/
private theorem filterMap_getLastD_of_last_some {l : List (Option ℕ)} {w : ℕ}
    (h : l.getLastD none = some w) : (l.filterMap id).getLastD 0 = w := by
  induction l with
  | nil => simp at h
  | cons o os ih =>
    cases os with
    | nil =>
      have ho : o = some w := by simpa using h
      rw [ho]
      simp
    | cons o' os' =>
      have h' : (o' :: os').getLastD none = some w := by
        rw [List.getLastD_cons] at h
        rwa [← getLastD_default_eq (l := o' :: os') (by simp) none o] at h
      have hne' : (o' :: os').filterMap id ≠ [] := filterMap_ne_nil_of_last_some h'
      cases o with
      | none => simpa [List.filterMap_cons] using ih h'
      | some a =>
        rw [List.filterMap_cons]
        change (a :: List.filterMap id (o' :: os')).getLastD 0 = w
        rw [List.getLastD_cons, getLastD_default_eq hne' a 0]
        exact ih h'

/-- 首项为 `some w` ⇒ `filterMap id` 首值 = `w`。 -/
private theorem filterMap_getD_zero_of_head_some {l : List (Option ℕ)} {w : ℕ}
    (h : l.headD none = some w) : (l.filterMap id).getD 0 0 = w := by
  cases l with
  | nil => simp at h
  | cons o os =>
    cases o with
    | none => simp at h
    | some a => simpa using h

/-- `getLastD` 与末位 `getD` 的桥（非空表）。 -/
private theorem getLastD_eq_getD_last {l : List ℕ} (h : l ≠ []) :
    l.getLastD 0 = l.getD (l.length - 1) 0 := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  symm
  rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt (by
    have hpos : 0 < l.length := List.length_pos_of_ne_nil h
    omega) 0, ← List.getLast_eq_getElem h]
  rfl

/-- `ifbetwn` 在端点不等时 = `between ++ [b]`。 -/
private theorem ifbetwn_eq_between_snoc {s : List ℕ} {a b : ℕ}
    (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) :
    Kepler.Text.Reduction5.ifbetwn s a b = between s a b ++ [b] := by
  unfold Kepler.Text.Reduction5.ifbetwn
  rw [if_pos ⟨ha, hb, hne⟩]

/-- **mid 段主归纳**：`destTriple0 f [] (take i)` 的 `filterMap id` 严格增，
且（`0 < i`）末项 = `some z_{i-1}`。 -/
private theorem midAux (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    {v : ℕ} (hprev : (prevEl (core L r) v, v) = x) :
    let uvns := Kepler.Text.Reduction3.coreTripleV4 L N r x
    ∀ i, i ≤ k →
      IndexfStrict v (core L r)
        ((Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).filterMap id) ∧
      (0 < i → (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).getLastD none
        = some (ztrans L N r x (i - 1)).1) := by
  intro uvns
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hk0 : 0 < k := by
    have h := transformCountNon0OfMarked L hL hgn haq hm hnf
    rw [hk] at h
    exact Nat.pos_of_ne_zero h
  have hnf_i : ∀ i, i < k → ¬ finalList L (rtrans L N r x i) := fun i hi =>
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
  have hcoreof : ∀ u ∈ r, u.1 ∈ core L r :=
    Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm
  have hym : ∀ i, i < k → (ytrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs1 L hL hgn haq i (hnf_i i hi) hm)
  have hzm : ∀ i, i < k → (ztrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs2 L hL hgn haq i (hnf_i i hi) hm)
  have hrnd : (core L r).Nodup := Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hv : v ∈ core L r := by
    have hx1 : x.1 = prevEl (core L r) v := (congrArg Prod.fst hprev).symm
    have hpre : prevEl (core L r) v ∈ core L r := by
      rw [← hx1]; exact hcoreof x hm.2.2.2.1
    have h := Kepler.Text.TameLp.nextEl_mem_of_mem hpre
    rwa [Kepler.Text.Reduction5.nextPrevId hrnd v] at h
  have hIdx : ∀ i, i < k →
      indexf v (ytrans L N r x i).1 (core L r)
        < indexf v (ztrans L N r x i).1 (core L r) :=
    indexfYtranLtZtranOfPrev L hL hgn hres hm hnf hk hprev
  have hFy := notMemIfbetwnFyOfPrev L hL hgn hres hm hnf hk hprev
  have hlen : uvns.length = k := by
    rw [Kepler.Text.Reduction3.coreTripleV4_length]
    exact hk
  have hmemft : ∀ i, i < k → ftrans L N r x i ∈ core L r := by
    intro i hi
    rw [Kepler.Text.Reduction5.ftrans]
    split
    · rename_i h0
      have hv2 : x.2 = v := (congrArg Prod.snd hprev).symm
      rwa [hv2]
    · rename_i h0
      exact hzm (i - 1) (by omega)
  have hftpos : ∀ i, 0 < i → ftrans L N r x i = (ztrans L N r x (i - 1)).1 := by
    intro i hi
    rw [Kepler.Text.Reduction5.ftrans]
    rw [if_neg (by omega)]
  have hnotmem : ∀ i, i < k → ftrans L N r x i ≠ (ytrans L N r x i).1 →
      v ∉ between (core L r) (ftrans L N r x i) (ytrans L N r x i).1 ∧
        v ≠ (ytrans L N r x i).1 := by
    intro i hi hne
    have hifb := ifbetwn_eq_between_snoc (hmemft i hi) (hym i hi) hne
    have hlenif : 1 < (ftrans L N r x i ::
        Kepler.Text.Reduction5.ifbetwn (core L r) (ftrans L N r x i)
          (ytrans L N r x i).1).length := by
      rw [hifb]
      simp
    have hnot := hFy i hi hlenif
    rw [hifb] at hnot
    refine ⟨fun h => hnot (List.mem_append_left _ h), fun h => hnot ?_⟩
    rw [h]
    exact List.mem_append_right _ (by simp)
  intro i hi
  induction i with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [Kepler.Text.Reduction3.destTriple0, IndexfStrict]
    · intro h; omega
  | succ i ih =>
    obtain ⟨IH1, IH2⟩ := ih (by omega)
    have hiK : i < k := by omega
    have hilt : i < uvns.length := by omega
    have htake : uvns.take (i + 1) = uvns.take i ++ [uvns[i]'hilt] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hilt]
      rfl
    have hget := Kepler.Text.Reduction3.elCoreTriple L N r x i (by rw [hk]; exact hiK)
    have hA : Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))
        = Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)
          ++ stepSeg (core L r)
              (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i))
              (ytrans L N r x i).1 (ztrans L N r x i).1
              (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length := by
      rw [htake, destTriple0Append, destTriple0_single, hget]
    have hfil : ((Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (i + 1))).filterMap id)
        = ((Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).filterMap id)
          ++ (stepSeg (core L r)
              (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i))
              (ytrans L N r x i).1 (ztrans L N r x i).1
              (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length).filterMap id := by
      rw [hA, List.filterMap_append]
    have hlastA : (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).getLastD none
        = if i = 0 then none else some (ztrans L N r x (i - 1)).1 := by
      by_cases hi0 : i = 0
      · subst hi0; simp [Kepler.Text.Reduction3.destTriple0]
      · rw [if_neg hi0]; exact IH2 (by omega)
    have hseg : (stepSeg (core L r)
          (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i))
          (ytrans L N r x i).1 (ztrans L N r x i).1
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length).filterMap id
        = if i = 0 then [(ytrans L N r x i).1, (ztrans L N r x i).1]
          else if (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1 then [(ztrans L N r x i).1]
          else if nextEl (core L r) (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1 then
            [(ytrans L N r x i).1, (ztrans L N r x i).1]
          else between (core L r) (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1
            ++ [(ytrans L N r x i).1, (ztrans L N r x i).1] := by
      by_cases hi0 : i = 0
      · subst hi0
        rw [if_pos rfl]
        have hA0 : Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take 0) = [] := by
          simp [Kepler.Text.Reduction3.destTriple0]
        rw [hA0]
        simpa using stepSeg_filterMap_nil (core L r) (ytrans L N r x 0).1
          (ztrans L N r x 0).1 (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length
      · rw [if_neg hi0]
        have hlast0 : (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).getLastD none
            = some (ztrans L N r x (i - 1)).1 := by
          rw [hlastA, if_neg hi0]
        rw [stepSeg_filterMap_last (core L r) _ hlast0]
    have hsegStrict : IndexfStrict v (core L r)
        ((stepSeg (core L r)
          (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i))
          (ytrans L N r x i).1 (ztrans L N r x i).1
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length).filterMap id) := by
      rw [hseg]
      by_cases hi0 : i = 0
      · subst hi0
        rw [if_pos rfl]
        have hp : indexf v (ytrans L N r x 0).1 (core L r)
            < indexf v (ztrans L N r x 0).1 (core L r) := hIdx 0 hk0
        rw [show ([(ytrans L N r x 0).1, (ztrans L N r x 0).1] : List ℕ)
            = [(ytrans L N r x 0).1] ++ [(ztrans L N r x 0).1] from rfl]
        exact IndexfStrict.cons (by simpa using hp) (by
          intro j hj; simp at hj)
      · rw [if_neg hi0]
        by_cases h1 : (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1
        · rw [if_pos h1]
          intro j hj
          simp at hj
        · rw [if_neg h1]
          by_cases h2 : nextEl (core L r) (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1
          · rw [if_pos h2]
            have hp := hIdx i hiK
            rw [show ([(ytrans L N r x i).1, (ztrans L N r x i).1] : List ℕ)
                = [(ytrans L N r x i).1] ++ [(ztrans L N r x i).1] from rfl]
            exact IndexfStrict.cons (by simpa using hp) (by
              intro j hj; simp at hj)
          · rw [if_neg h2]
            have hne : (ztrans L N r x (i - 1)).1 ≠ (ytrans L N r x i).1 := h1
            have hfti : ftrans L N r x i = (ztrans L N r x (i - 1)).1 := hftpos i (by omega)
            obtain ⟨hvbet, hvyi⟩ := hnotmem i hiK (by rw [hfti]; exact hne)
            have hvbetz : v ∉ between (core L r) (ztrans L N r x (i - 1)).1
                (ytrans L N r x i).1 := by
              rw [← hfti]; exact hvbet
            have hvnot : v ∉ between (core L r) (ztrans L N r x (i - 1)).1
                  (ytrans L N r x i).1 ++ [(ytrans L N r x i).1] := by
              intro h
              rcases List.mem_append.mp h with hb | hy
              · exact hvbetz hb
              · exact hvyi (by simpa using hy)
            have harc := arcSnocIndexfStrict hv (hzm (i - 1) (by omega)) (hym i hiK) hrnd
              hne hvnot
            have hz := getD_snoc_last (between (core L r) (ztrans L N r x (i - 1)).1
              (ytrans L N r x i).1) (ytrans L N r x i).1
            rw [show ([(ytrans L N r x i).1, (ztrans L N r x i).1] : List ℕ)
                = [(ytrans L N r x i).1] ++ [(ztrans L N r x i).1] from rfl,
              ← List.append_assoc]
            refine IndexfStrict.snoc harc ?_
            intro _
            rw [hz]
            exact hIdx i hiK
    have hjunct : ((Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).filterMap id) ≠ [] →
        (stepSeg (core L r)
          (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i))
          (ytrans L N r x i).1 (ztrans L N r x i).1
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length).filterMap id ≠ [] →
        indexf v (((Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).filterMap id).getD
              (((Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).filterMap id).length - 1) 0)
            (core L r) <
        indexf v (((stepSeg (core L r)
          (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i))
          (ytrans L N r x i).1 (ztrans L N r x i).1
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length).filterMap id).getD 0 0)
          (core L r) := by
      intro hAne hsegne
      by_cases hi0 : i = 0
      · subst hi0
        simp [Kepler.Text.Reduction3.destTriple0] at hAne
      · have hlastfil : (((Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).filterMap id).getD
            (((Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).filterMap id).length - 1) 0)
            = (ztrans L N r x (i - 1)).1 := by
          rw [← getLastD_eq_getD_last hAne]
          exact filterMap_getLastD_of_last_some (by rw [hlastA, if_neg hi0])
        rw [hlastfil]
        rw [hseg]
        rw [if_neg hi0]
        by_cases h1 : (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1
        · rw [if_pos h1]
          simpa [h1] using hIdx i hiK
        · rw [if_neg h1]
          by_cases h2 : nextEl (core L r) (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1
          · rw [if_pos h2]
            rw [show ([(ytrans L N r x i).1, (ztrans L N r x i).1] : List ℕ).getD 0 0
                = (ytrans L N r x i).1 from rfl]
            have hnft : ftrans L N r x i ≠ (ytrans L N r x i).1 := by
              rw [hftpos i (by omega)]; exact h1
            obtain ⟨-, hvyi⟩ := hnotmem i hiK hnft
            have hsrc : (ztrans L N r x (i - 1)).1 ∈ core L r := hzm (i - 1) (by omega)
            have hstep := indexfNextElSucc hv hsrc hrnd hvyi h2
            omega
          · rw [if_neg h2]
            have hne : (ztrans L N r x (i - 1)).1 ≠ (ytrans L N r x i).1 := h1
            have hfti : ftrans L N r x i = (ztrans L N r x (i - 1)).1 := hftpos i (by omega)
            obtain ⟨hvbet, hvyi⟩ := hnotmem i hiK (by rw [hfti]; exact hne)
            have hbetne : between (core L r) (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1 ≠ [] := by
              intro hbet
              exact h2 (Kepler.Text.TameSpine.aq10_betwnEqNil hbet (hzm (i - 1) (by omega))
                (hym i hiK) hne hrnd)
            have hbpos : 0 < (between (core L r) (ztrans L N r x (i - 1)).1
                (ytrans L N r x i).1).length := List.length_pos_of_ne_nil hbetne
            have hfirst : (between (core L r) (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1
                  ++ [(ytrans L N r x i).1, (ztrans L N r x i).1]).getD 0 0
                = (nextEl (core L r))^[1] (ztrans L N r x (i - 1)).1 := by
              rw [List.getD_append _ _ _ _ hbpos]
              rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hbpos 0]
              exact Kepler.Text.TameSpine.betwnOrbit hne hrnd (hzm (i - 1) (by omega))
                (hym i hiK) hbpos
            rw [hfirst, Function.iterate_one]
            have hsrc : (ztrans L N r x (i - 1)).1 ∈ core L r := hzm (i - 1) (by omega)
            have hfirstmem : (nextEl (core L r))^[1] (ztrans L N r x (i - 1)).1
                = (between (core L r) (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1)[0]'hbpos :=
              (Kepler.Text.TameSpine.betwnOrbit hne hrnd (hzm (i - 1) (by omega)) (hym i hiK)
                hbpos).symm
            have hbeq : between (core L r) (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1
                = between (core L r) (ftrans L N r x i) (ytrans L N r x i).1 := by
              rw [hfti]
            have hmem0 : (between (core L r) (ztrans L N r x (i - 1)).1
                  (ytrans L N r x i).1)[0]'hbpos
                ∈ between (core L r) (ftrans L N r x i) (ytrans L N r x i).1 := by
              rw [← hbeq]
              exact List.getElem_mem _
            have hvne : v ≠ (nextEl (core L r))^[1] (ztrans L N r x (i - 1)).1 := by
              intro h
              apply hvbet
              rw [h, hfirstmem]
              exact hmem0
            have hstep := indexfNextElSucc hv hsrc hrnd hvne (by rw [Function.iterate_one])
            rw [Function.iterate_one] at hstep
            omega
    refine ⟨?_, ?_⟩
    · rw [hfil]
      exact IndexfStrict.append IH1 hsegStrict hjunct
    · intro _
      rw [hA]
      rw [getLastD_append_ne none _ (stepSeg_ne_nil _ _ _ _ _)]
      exact stepSeg_getLastD _ _ _ _ _

/-- `headD` 的 append 展开。 -/
private theorem headD_append (l1 l2 : List ℕ) (d : ℕ) :
    (l1 ++ l2).headD d = if l1 = [] then l2.headD d else l1.headD d := by
  cases l1 <;> simp

/-- **mid 首值**：`0 < i` 时 `destTriple0 f [] (take i)` 的首项 = `some y_0`。 -/
private theorem midFirstAux (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hk : transformCount L N r x = k) :
    let uvns := Kepler.Text.Reduction3.coreTripleV4 L N r x
    ∀ i, 0 < i → i ≤ k →
      (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take i)).headD none
        = some (ytrans L N r x 0).1 := by
  intro uvns i hi hik
  have hlen : uvns.length = k := by
    rw [Kepler.Text.Reduction3.coreTripleV4_length]
    exact hk
  induction i with
  | zero => omega
  | succ j ih =>
    cases j with
    | zero =>
      have htake : uvns.take 1 = [uvns[0]'(by omega)] := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, List.take_add_one, List.getElem?_eq_getElem (by omega)]
        rfl
      have hget := Kepler.Text.Reduction3.elCoreTriple L N r x 0 (by rw [hk]; omega)
      have hA : Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take 1)
          = stepSeg (core L r) [] (ytrans L N r x 0).1 (ztrans L N r x 0).1
              (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length := by
        rw [htake, hget, destTriple0_single]
        rfl
      rw [hA]
      simp [stepSeg]
    | succ j =>
      have hi2 : 0 < j + 1 := by omega
      have htake : uvns.take (j + 1 + 1) = uvns.take (j + 1) ++ [uvns[j + 1]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
        rfl
      have hget := Kepler.Text.Reduction3.elCoreTriple L N r x (j + 1) (by rw [hk]; omega)
      have hA : Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (j + 1 + 1))
          = Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (j + 1))
            ++ stepSeg (core L r) (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (j + 1)))
                (ytrans L N r x (j + 1)).1 (ztrans L N r x (j + 1)).1
                (between (findFaceDarts L x) (ytrans L N r x (j + 1)) (ztrans L N r x (j + 1))).length := by
        rw [htake, destTriple0Append, destTriple0_single, hget]
      rw [hA]
      have hIH := ih hi2 (by omega)
      have hneA : Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (j + 1)) ≠ [] := by
        intro h
        rw [h] at hIH
        simp at hIH
      have hheadapp : (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (j + 1))
            ++ stepSeg (core L r)
              (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (j + 1)))
              (ytrans L N r x (j + 1)).1 (ztrans L N r x (j + 1)).1
              (between (findFaceDarts L x) (ytrans L N r x (j + 1))
                (ztrans L N r x (j + 1))).length).headD none
          = (Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (j + 1))).headD none := by
        cases hAd : Kepler.Text.Reduction3.destTriple0 (core L r) [] (uvns.take (j + 1)) with
        | nil =>
          rw [hAd] at hneA
          exact absurd rfl hneA
        | cons a t => rfl
      rw [hheadapp, hIH]

/-- **U2 全句**（`uvnsMainOfU2` 的 `hU2` 逐字同形）：`destTripleFull` 的
`filterMap id` 上 `indexf v` 逐位严格增。 -/
theorem uvnsVsOrdered (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    {v : ℕ} (hprev : (prevEl (core L r) v, v) = x) :
    ∀ i, i + 1 < ((Kepler.Text.Reduction3.destTripleFull (core L r) v
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)).filterMap id).length →
      indexf v (((Kepler.Text.Reduction3.destTripleFull (core L r) v
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)).filterMap id).getD i 0) (core L r) <
      indexf v (((Kepler.Text.Reduction3.destTripleFull (core L r) v
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)).filterMap id).getD (i + 1) 0)
        (core L r) := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hk0 : 0 < k := by
    have h := transformCountNon0OfMarked L hL hgn haq hm hnf
    rw [hk] at h
    exact Nat.pos_of_ne_zero h
  have hnz : transformCount L N r x ≠ 0 :=
    transformCountNon0OfMarked L hL hgn haq hm hnf
  have hnf_i : ∀ i, i < k → ¬ finalList L (rtrans L N r x i) := fun i hi =>
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
  have hcoreof : ∀ u ∈ r, u.1 ∈ core L r :=
    Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm
  have hym : ∀ i, i < k → (ytrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs1 L hL hgn haq i (hnf_i i hi) hm)
  have hzm : ∀ i, i < k → (ztrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs2 L hL hgn haq i (hnf_i i hi) hm)
  have hrnd : (core L r).Nodup := Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hx1 : x.1 = prevEl (core L r) v := (congrArg Prod.fst hprev).symm
  have hv : v ∈ core L r := by
    have hpre : prevEl (core L r) v ∈ core L r := by
      rw [← hx1]; exact hcoreof x hm.2.2.2.1
    have h := Kepler.Text.TameLp.nextEl_mem_of_mem hpre
    rwa [Kepler.Text.Reduction5.nextPrevId hrnd v] at h
  have hprevcore : prevEl (core L r) v ∈ core L r := by
    rw [← hx1]; exact hcoreof x hm.2.2.2.1
  have hZx := notMemIfbetwnZxOfPrev L hL hgn hres hm hnf hk hprev
  have hlen : (Kepler.Text.Reduction3.coreTripleV4 L N r x).length = k := by
    rw [Kepler.Text.Reduction3.coreTripleV4_length]
    exact hk
  -- head/last of uvns
  have hhead : (Kepler.Text.Reduction3.coreTripleV4 L N r x).headD (0, 0, 0) =
      ((ytrans L N r x 0).1, (ztrans L N r x 0).1,
        (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length) := by
    cases huv : Kepler.Text.Reduction3.coreTripleV4 L N r x with
    | nil => rw [huv] at hlen; simp at hlen; omega
    | cons a t =>
      have h0 := Kepler.Text.Reduction3.elCoreTriple L N r x 0 (by rw [hk]; exact hk0)
      simpa only [huv, List.headD_cons, List.getElem_cons_zero] using h0
  have hlast : (Kepler.Text.Reduction3.coreTripleV4 L N r x).getLastD (0, 0, 0) =
      ((ytrans L N r x (k - 1)).1, (ztrans L N r x (k - 1)).1,
        (between (findFaceDarts L x) (ytrans L N r x (k - 1))
          (ztrans L N r x (k - 1))).length) := by
    rw [Kepler.Text.Reduction3.lastCoreTriple L N r x (k - 1) hnz (by rw [hk])]
  set init : List (Option ℕ) :=
    if v = (ytrans L N r x 0).1 then []
    else some v :: (between (core L r) v (ytrans L N r x 0).1).map some with hinit
  set mid : List (Option ℕ) :=
    Kepler.Text.Reduction3.destTriple0 (core L r) []
      (Kepler.Text.Reduction3.coreTripleV4 L N r x) with hmid
  set final : List (Option ℕ) :=
    if (ztrans L N r x (k - 1)).1 = prevEl (core L r) v then []
    else (between (core L r) (ztrans L N r x (k - 1)).1 (prevEl (core L r) v)).map some
      ++ [some (prevEl (core L r) v)] with hfinal
  have hvs : Kepler.Text.Reduction3.destTripleFull (core L r) v
        (Kepler.Text.Reduction3.coreTripleV4 L N r x) = init ++ mid ++ final := by
    unfold Kepler.Text.Reduction3.destTripleFull
    rw [hhead, hlast]
  -- mid 件
  have hmidA := midAux L hL hgn hres hm hnf hk hprev
  obtain ⟨hMidStrict, hMidLast0⟩ := hmidA k le_rfl
  have htakek : (Kepler.Text.Reduction3.coreTripleV4 L N r x).take k
      = Kepler.Text.Reduction3.coreTripleV4 L N r x := by
    rw [← hlen, List.take_length]
  rw [htakek] at hMidStrict hMidLast0
  have hMidLast : mid.getLastD none = some (ztrans L N r x (k - 1)).1 := by
    rw [hmid]; exact hMidLast0 hk0
  have hMidNe : mid.filterMap id ≠ [] := filterMap_ne_nil_of_last_some hMidLast
  have hMidLastFil : (mid.filterMap id).getLastD 0 = (ztrans L N r x (k - 1)).1 :=
    filterMap_getLastD_of_last_some hMidLast
  have hMidFirst : (mid.filterMap id).getD 0 0 = (ytrans L N r x 0).1 := by
    have hheadm : mid.headD none = some (ytrans L N r x 0).1 := by
      rw [hmid, ← htakek]
      exact midFirstAux L hL hk k hk0 le_rfl
    exact filterMap_getD_zero_of_head_some hheadm
  -- init 严格
  have hInitStrict : IndexfStrict v (core L r) (init.filterMap id) := by
    by_cases hv0 : v = (ytrans L N r x 0).1
    · rw [hinit, if_pos hv0]; simp [IndexfStrict]
    · rw [hinit, if_neg hv0]
      have hvbet0 : v ∉ between (core L r) v (ytrans L N r x 0).1 := by
        intro hb
        have := (Kepler.Text.Reduction5.indexfBetwnEq hv0 hrnd hv (hym 0 hk0)).mp hb
        rw [Kepler.Text.Reduction4.indexfRefl hv] at this
        omega
      simpa using arcIndexfStrict hv hv (hym 0 hk0) hrnd hv0 hvbet0
  -- final 严格
  have hFinalStrict : IndexfStrict v (core L r) (final.filterMap id) := by
    by_cases hz : (ztrans L N r x (k - 1)).1 = prevEl (core L r) v
    · rw [hfinal, if_pos hz]; simp [IndexfStrict]
    · rw [hfinal, if_neg hz]
      have hvnot : v ∉ between (core L r) (ztrans L N r x (k - 1)).1 (prevEl (core L r) v)
          ++ [prevEl (core L r) v] := by
        have hifb := ifbetwn_eq_between_snoc (hzm (k - 1) (by omega)) hprevcore hz
        have hnot := hZx
        rw [hx1] at hnot
        rw [hifb] at hnot
        exact hnot
      simpa using arcSnocIndexfStrict hv (hzm (k - 1) (by omega)) hprevcore hrnd hz hvnot
  -- junction 1：init 末 → y0
  have hJ1 : init.filterMap id ≠ [] → mid.filterMap id ≠ [] →
      indexf v ((init.filterMap id).getD ((init.filterMap id).length - 1) 0) (core L r)
        < indexf v ((mid.filterMap id).getD 0 0) (core L r) := by
    intro hInitNe _
    rw [hMidFirst]
    -- init 形状
    have hv0 : v ≠ (ytrans L N r x 0).1 := by
      intro h0
      rw [hinit, if_pos h0] at hInitNe
      exact hInitNe rfl
    rw [hinit, if_neg hv0]
    -- init.filterMap = v :: between
    set arc : List ℕ := between (core L r) v (ytrans L N r x 0).1 with harc
    have hinitFil : (some v :: (between (core L r) v (ytrans L N r x 0).1).map some).filterMap id
        = v :: arc := by
      rw [harc]
      simp
    rw [hinitFil]
    by_cases hbet : arc = []
    · -- [v]
      rw [hbet]
      simp only [List.length_cons, List.length_nil, Nat.sub_self,
        List.getD_cons_zero]
      have hnext : nextEl (core L r) v = (ytrans L N r x 0).1 :=
        Kepler.Text.TameSpine.aq10_betwnEqNil (by rw [← harc]; exact hbet)
          hv (hym 0 hk0) hv0 hrnd
      have hstep := indexfNextElSucc hv hv hrnd hv0 hnext
      omega
    · -- last of v :: between = 弧末
      have hbet' : between (core L r) v (ytrans L N r x 0).1 ≠ [] := by
        rw [← harc]; exact hbet
      rw [harc]
      have hpos : 0 < (between (core L r) v (ytrans L N r x 0).1).length :=
        List.length_pos_of_ne_nil hbet'
      rw [show (v :: between (core L r) v (ytrans L N r x 0).1).length - 1
          = (between (core L r) v (ytrans L N r x 0).1).length - 1 + 1 from by
        simp only [List.length_cons]
        omega]
      rw [List.getD_cons_succ]
      have hlastarc : (between (core L r) v (ytrans L N r x 0).1).getD
            ((between (core L r) v (ytrans L N r x 0).1).length - 1) 0
          = (between (core L r) v (ytrans L N r x 0).1).getLast hbet' := by
        rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt (by omega) 0,
          ← List.getLast_eq_getElem hbet']
      rw [hlastarc]
      have hnext := Kepler.Text.Reduction5.nextLastBetwn hv (hym 0 hk0) hrnd hv0 hbet'
      have hsrc := Kepler.Text.Reduction5.betwnMem (List.getLast_mem hbet')
      have hstep := indexfNextElSucc hv hsrc hrnd hv0 hnext
      omega
  -- junction 2：z_{k-1} → final 首
  have hJ2 : (init.filterMap id ++ mid.filterMap id) ≠ [] → final.filterMap id ≠ [] →
      indexf v (((init.filterMap id ++ mid.filterMap id)).getD
          ((init.filterMap id ++ mid.filterMap id).length - 1) 0) (core L r)
        < indexf v ((final.filterMap id).getD 0 0) (core L r) := by
    intro _ hFinNe
    have hz : (ztrans L N r x (k - 1)).1 ≠ prevEl (core L r) v := by
      intro h0
      rw [hfinal, if_pos h0] at hFinNe
      exact hFinNe rfl
    -- prefix 末值 = z_{k-1}
    have hprefLast : (init.filterMap id ++ mid.filterMap id).getD
        ((init.filterMap id ++ mid.filterMap id).length - 1) 0 = (ztrans L N r x (k - 1)).1 := by
      have hmidpos : 0 < (mid.filterMap id).length := List.length_pos_of_ne_nil hMidNe
      rw [List.getD_append_right _ _ 0 _ (by
        rw [List.length_append]
        omega)]
      rw [show (init.filterMap id ++ mid.filterMap id).length - 1 - (init.filterMap id).length
          = (mid.filterMap id).length - 1 from by rw [List.length_append]; omega]
      rw [← getLastD_eq_getD_last hMidNe]
      exact hMidLastFil
    rw [hprefLast]
    rw [hfinal, if_neg hz]
    simp only [List.filterMap_append, List.filterMap_map, List.filterMap_cons, id_eq,
      Function.comp_apply, List.filterMap_some, List.filterMap_nil]
    by_cases hbet : between (core L r) (ztrans L N r x (k - 1)).1 (prevEl (core L r) v) = []
    · -- first = prevEl v
      rw [hbet]
      simp
      have hnext : nextEl (core L r) (ztrans L N r x (k - 1)).1 = prevEl (core L r) v :=
        Kepler.Text.TameSpine.aq10_betwnEqNil hbet (hzm (k - 1) (by omega))
          hprevcore hz hrnd
      have hvb : v ≠ prevEl (core L r) v := by
        intro h0
        apply hZx
        rw [hx1]
        rw [ifbetwn_eq_between_snoc (hzm (k - 1) (by omega)) hprevcore hz]
        rw [hbet]
        exact List.mem_singleton.mpr h0
      have hstep := indexfNextElSucc hv (hzm (k - 1) (by omega)) hrnd hvb hnext
      omega
    · -- first = between[0] = nextEl z
      have hbpos : 0 < (between (core L r) (ztrans L N r x (k - 1)).1
          (prevEl (core L r) v)).length := List.length_pos_of_ne_nil hbet
      rw [show (between (core L r) (ztrans L N r x (k - 1)).1 (prevEl (core L r) v)
            ++ [prevEl (core L r) v]).getD 0 0
          = (between (core L r) (ztrans L N r x (k - 1)).1 (prevEl (core L r) v)).getD 0 0
        from by rw [List.getD_append _ _ _ _ hbpos]]
      rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hbpos 0]
      have hfirst : (between (core L r) (ztrans L N r x (k - 1)).1 (prevEl (core L r) v))[0]'hbpos
          = (nextEl (core L r))^[1] (ztrans L N r x (k - 1)).1 :=
        Kepler.Text.TameSpine.betwnOrbit hz hrnd (hzm (k - 1) (by omega)) hprevcore hbpos
      rw [hfirst, Function.iterate_one]
      have hvbet : v ∉ between (core L r) (ztrans L N r x (k - 1)).1 (prevEl (core L r) v) := by
        have hifb := ifbetwn_eq_between_snoc (hzm (k - 1) (by omega)) hprevcore hz
        have hnot := hZx
        rw [hx1] at hnot
        rw [hifb] at hnot
        exact fun hb => hnot (List.mem_append_left _ hb)
      have hfirst' : nextEl (core L r) (ztrans L N r x (k - 1)).1
          = (between (core L r) (ztrans L N r x (k - 1)).1 (prevEl (core L r) v))[0]'hbpos := by
        rw [hfirst, Function.iterate_one]
      have hvne : v ≠ nextEl (core L r) (ztrans L N r x (k - 1)).1 := by
        intro h0
        apply hvbet
        have hmem' : nextEl (core L r) (ztrans L N r x (k - 1)).1
            ∈ between (core L r) (ztrans L N r x (k - 1)).1 (prevEl (core L r) v) := by
          rw [hfirst']
          exact List.getElem_mem _
        rwa [← h0] at hmem'
      have hstep := indexfNextElSucc hv (hzm (k - 1) (by omega)) hrnd hvne rfl
      omega
  -- 收口
  intro i hi
  rw [hvs] at hi ⊢
  simp only [List.filterMap_append] at hi ⊢
  exact (IndexfStrict.append (IndexfStrict.append hInitStrict hMidStrict hJ1) hFinalStrict hJ2) i hi

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.indexfNextElSucc
#print axioms Kepler.Text.Reduction5.indexfStrictOfSteps
#print axioms Kepler.Text.Reduction5.arcIndexfStrict
#print axioms Kepler.Text.Reduction5.indexfYtranLtZtranOfPrev
#print axioms Kepler.Text.Reduction5.notMemIfbetwnFyOfPrev
#print axioms Kepler.Text.Reduction5.notMemIfbetwnZxOfPrev
#print axioms Kepler.Text.Reduction5.IndexfStrict.append
#print axioms Kepler.Text.Reduction5.uvnsVsOrdered

/- 接口探针：U2 定理直接填 `uvnsMainOfU2` 的 `hU2` 槽。 -/
#check Kepler.Text.Reduction5.uvnsMainOfU2 Kepler.Text.Reduction5.uvnsVsOrdered
