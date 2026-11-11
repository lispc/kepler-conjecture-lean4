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

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.indexfNextElSucc
#print axioms Kepler.Text.Reduction5.indexfStrictOfSteps
#print axioms Kepler.Text.Reduction5.arcIndexfStrict
#print axioms Kepler.Text.Reduction5.indexfYtranLtZtranOfPrev
#print axioms Kepler.Text.Reduction5.notMemIfbetwnFyOfPrev
#print axioms Kepler.Text.Reduction5.notMemIfbetwnZxOfPrev
#print axioms Kepler.Text.Reduction5.IndexfStrict.append
