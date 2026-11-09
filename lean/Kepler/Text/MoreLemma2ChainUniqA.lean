/-
  Kepler.Text.MoreLemma2ChainUniqA — more_lemma2 岛 `simple_hypermap` 机器片 §1：
  `list_pairs` 三件（泛型 `α`，零 `parts`/`hypermap` 载体）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/tame_list.hl`）──
  │ :9155 `list_pairs_unique`     → listPairsUnique
  │ :9173 `list_pairs_not_uniq`   → listPairsNotUniq
  │ （`nth_list_pairs` 的 getElem 折算）→ listPairsGetElemRot（私有）
  │ 私有支撑：`memZipEq`、`getElemCon`（Spine 私件链岛重落）
  │ 复用不重落：`la7_length_listPairs`（TameLp:5626，public）
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；本片零 Spine import。
-/

import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2ChainUniqA

open Kepler.Assembly (listPairs)
open Kepler.Text.TameLp (la7_length_listPairs)

/-! ## §0 私有小件 -/

/-- 同长双下标的取值一致性（proof-irrelevance 的显式形）。 -/
private theorem getElemCon {α : Type*} {l : List α} {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a = b) : l[a]'ha = l[b]'hb := by
  subst hab
  rfl

/-- `d ∈ l₁.zip l₂` ⇒ 存在同下标 `i` 使 `(l₁[i], l₂[i]) = d`。 -/
private theorem memZipEq {β : Type*} {l₁ l₂ : List β} {d : β × β}
    (h : d ∈ l₁.zip l₂) :
    ∃ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length), (l₁[i]'h₁, l₂[i]'h₂) = d := by
  obtain ⟨i, hi, hd⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_zip] at hd
  have hk : i < l₁.length ∧ i < l₂.length := by
    rw [List.length_zip] at hi
    omega
  exact ⟨i, hk.1, hk.2, hd⟩

/-! ## §1 `list_pairs` 逐项式（HOL `nth_list_pairs` 的 getElem 折算） -/

/-- `list_pairs s` 第 `k` 项 = `(s[k], s[(k+1) % sizel s])`（含末位回卷支）。 -/
private theorem listPairsGetElemRot {α : Type*} (s : List α) {k : ℕ}
    (hk : k < s.length) :
    (listPairs s)[k]'(by rw [la7_length_listPairs s]; omega)
      = (s[k]'hk,
        s[(k + 1) % s.length]'(Nat.mod_lt (k + 1)
          (Nat.lt_of_le_of_lt (Nat.zero_le k) hk))) := by
  have hpos : 0 < s.length := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hlenDr : (s.drop 1).length = s.length - 1 := List.length_drop
  have hlenTk : (List.take 1 s).length = min 1 s.length := List.length_take
  have htot : k < ((s.drop 1) ++ List.take 1 s).length := by
    rw [List.length_append, hlenDr, hlenTk]
    omega
  by_cases hk1 : k + 1 < s.length
  · have hrot : ((s.drop 1) ++ List.take 1 s)[k] = (s.drop 1)[k] :=
      List.getElem_append_left (by rw [hlenDr]; omega) (h' := htot)
    have hdr : (s.drop 1)[k] = s[1 + k] :=
      List.getElem_drop (h := by rw [hlenDr]; omega)
    have hmod : (k + 1) % s.length = k + 1 := Nat.mod_eq_of_lt hk1
    show (s.zip (s.drop 1 ++ List.take 1 s))[k]'(by
      rw [List.length_zip]; omega) = _
    rw [List.getElem_zip, hrot, hdr]
    exact congrArg (Prod.mk s[k])
      (getElemCon (by omega) (Nat.mod_lt (k + 1) hpos) (by omega))
  · have jlen : k + 1 = s.length := by omega
    have hrot : ((s.drop 1) ++ List.take 1 s)[k]
        = (List.take 1 s)[k - (s.drop 1).length] :=
      List.getElem_append_right (by rw [hlenDr]; omega) (h₂ := htot)
    have h0 : k - (s.drop 1).length = 0 := by rw [hlenDr]; omega
    have htak : (List.take 1 s)[k - (s.drop 1).length] = s[0] :=
      (getElemCon (by rw [hlenTk]; omega) (by rw [hlenTk]; omega) h0).trans
        (List.getElem_take (h := by rw [hlenTk]; omega))
    show (s.zip (s.drop 1 ++ List.take 1 s))[k]'(by
      rw [List.length_zip]; omega) = _
    rw [List.getElem_zip, hrot, htak]
    exact congrArg (Prod.mk s[k])
      (getElemCon hpos (Nat.mod_lt (k + 1) hpos) (by rw [jlen, Nat.mod_self]))

/-! ## §2 `list_pairs` 同首分量唯一（HOL `list_pairs_unique`） -/

/-- **HOL `list_pairs_unique`**（tame_list.hl:9155）：
`uniq f ∧ MEM d1 (list_pairs f) ∧ MEM d2 (list_pairs f) ∧ FST d1 = FST d2
⇒ d1 = d2`。`Nodup.getElem_inj_iff` 把首分量相等翻成下标相等。 -/
theorem listPairsUnique {α : Type*} {f : List α} (hn : f.Nodup) {d1 d2 : α × α}
    (h1 : d1 ∈ listPairs f) (h2 : d2 ∈ listPairs f) (h : d1.1 = d2.1) :
    d1 = d2 := by
  obtain ⟨i, hi, _, hd1⟩ := memZipEq h1
  obtain ⟨j, hj, _, hd2⟩ := memZipEq h2
  have hf1 : f[i]'hi = d1.1 := congrArg Prod.fst hd1
  have hf2 : f[j]'hj = d2.1 := congrArg Prod.fst hd2
  have hij : i = j :=
    (hn.getElem_inj_iff (hi := hi) (hj := hj)).mp (by rw [hf1, hf2, h])
  subst hij
  rw [← hd1, ← hd2]

/-! ## §3 `list_pairs` 非唯一（HOL `list_pairs_not_uniq`） -/

/-- **HOL `list_pairs_not_uniq`**（tame_list.hl:9173）：
`¬ uniq s ∧ uniq (list_pairs s) ⇒ ∃ x x', x ∈ list_pairs s ∧ x' ∈ list_pairs s ∧
x ≠ x' ∧ FST x = FST x'`。 -/
theorem listPairsNotUniq {α : Type*} {s : List α}
    (hs : ¬s.Nodup) (hp : (listPairs s).Nodup) :
    ∃ x x' : α × α, x ∈ listPairs s ∧ x' ∈ listPairs s ∧ x ≠ x' ∧ x.1 = x'.1 := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem] at hs
  push Not at hs
  obtain ⟨i, j, hi, hj, hij, heq⟩ := hs
  have hlen : (listPairs s).length = s.length := la7_length_listPairs s
  have hi' : i < (listPairs s).length := by rw [hlen]; omega
  have hj' : j < (listPairs s).length := by rw [hlen]; omega
  refine ⟨(listPairs s)[i]'hi', (listPairs s)[j]'hj', List.getElem_mem _,
    List.getElem_mem _, ?_, ?_⟩
  · intro hcon
    have hix := (hp.getElem_inj_iff (hi := hi') (hj := hj')).mp hcon
    omega
  · have hxi : ((listPairs s)[i]'hi').1 = s[i] := by
      rw [listPairsGetElemRot s hi]
    have hxj : ((listPairs s)[j]'hj').1 = s[j] := by
      rw [listPairsGetElemRot s hj]
    rw [hxi, hxj]
    exact heq

end Kepler.Text.MoreLemma2ChainUniqA

/-! 公理审计锚（本文件编译即执行；预期 ≤ 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2ChainUniqA.listPairsUnique
#print axioms Kepler.Text.MoreLemma2ChainUniqA.listPairsNotUniq
