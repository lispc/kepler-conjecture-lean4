/-
  Kepler.Text.Reduction5Ml1W2bU — W2b-B2：`ml1S` 的 Nodup（HOL more_lemma1.hl:2226）。
  路线（ml3 实测收口）：`betwnTakeDrop` 两分支；
  · 非 wrap 支：`s = (r.drop i).take (j-i+1)`（`uniqTake ∘ uniqDrop`），
    端点等式走 `take_append_getElem` 反向 + `getElem_drop'` +
    `getElem_congr_idx`（ml2d 草稿的 `idxOf_inj` 支产生元变量，已弃）；
  · wrap 支：`s = (r.rotate i).take (r.length - i + j + 1)`
    （rotate 保 Nodup + `uniqTake`，免 disjoint；长度必须是
    `r.length - i + j + 1`，`i+j+1` 不足）。
  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction5Ml1W2bTiny
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl prevEl)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.ChainLists (markedList)

/-- **W2b-B2**：`y1 ≠ z1 ⇒ s.Nodup`（y1 = next_el r y、z1 = prev_el r z）。 -/
theorem ml1SUniq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0)) :
    (ml1S L N r x).Nodup := by
  obtain ⟨hyr, hzr, hz1r, hy1r, hyf, hzf, hy1fst, hz1fst, hzy⟩ :=
    ml1SetupMem L hL hgn hm hnf
  have hrnd : r.Nodup := Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  set i := r.idxOf (nextEl r (ly L r x)) with hi
  set j := r.idxOf (prevEl r (ztrans L N r x 0)) with hj
  have hy1i : i < r.length := List.idxOf_lt_length_iff.mpr hy1r
  have hz1i : j < r.length := List.idxOf_lt_length_iff.mpr hz1r
  have hgy1 : r[i]'hy1i = nextEl r (ly L r x) := Kepler.Text.TameLp.getElem_idxOf hy1r
  have hgz1 : r[j]'hz1i = prevEl r (ztrans L N r x 0) := Kepler.Text.TameLp.getElem_idxOf hz1r
  unfold ml1S
  rw [Kepler.Text.TameSpine.betwnTakeDrop hrnd hz1r, ← hi, ← hj]
  by_cases hlt : i < j
  · rw [if_pos hlt]
    have htake : (r.drop (i + 1)).take (j - i) =
        (r.drop (i + 1)).take (j - i - 1) ++ [prevEl r (ztrans L N r x 0)] := by
      conv_lhs => rw [show j - i = (j - i - 1) + 1 from by omega]
      rw [← List.take_append_getElem (by rw [List.length_drop]; omega)]
      congr 1
      rw [List.singleton_inj]
      rw [← List.getElem_drop' (xs := r) (i := i + 1) (j := j - i - 1) (h := by omega),
        getElem_congr_idx (show i + 1 + (j - i - 1) = j by omega), hgz1]
    have hEq : [nextEl r (ly L r x)] ++
        (((r.drop (i + 1)).take (j - (i + 1))) ++ [prevEl r (ztrans L N r x 0)])
        = (r.drop i).take (j - i + 1) := by
      rw [show j - (i + 1) = j - i - 1 from by omega, ← htake]
      have hdi : r.drop i = nextEl r (ly L r x) :: r.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hy1i]
        exact congrArg (fun a => a :: r.drop (i + 1)) hgy1
      rw [hdi, show j - i + 1 = (j - i) + 1 from by omega, List.take_succ_cons,
        List.singleton_append]
    rw [hEq]
    exact Kepler.Text.TameSpine.uniqTake (Kepler.Text.TameSpine.uniqDrop hrnd)
  · rw [if_neg hlt]
    have hji : j < i := by
      have h1 : j ≤ i := by omega
      rcases Nat.lt_or_eq_of_le h1 with h | h
      · exact h
      · exfalso
        apply hyz
        exact (List.idxOf_inj hy1r).mp (by rw [← hi, ← hj]; exact h.symm)
    have htake : r.take (j + 1) = r.take j ++ [prevEl r (ztrans L N r x 0)] := by
      rw [← List.take_append_getElem hz1i, hgz1]
    have hdrop : r.drop i = nextEl r (ly L r x) :: r.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hy1i]
      exact congrArg (fun a => a :: r.drop (i + 1)) hgy1
    have hLHS : [nextEl r (ly L r x)] ++
        (((r.drop (i + 1)) ++ r.take j) ++ [prevEl r (ztrans L N r x 0)])
        = (r.drop i) ++ r.take (j + 1) := by
      rw [List.singleton_append, List.append_assoc, ← List.cons_append, ← htake, ← hdrop]
    have hRHS : (r.rotate i).take (r.length - i + j + 1) = (r.drop i) ++ r.take (j + 1) := by
      rw [List.rotate_eq_drop_append_take (by omega : i ≤ r.length), List.take_append,
        List.take_of_length_le (by rw [List.length_drop]; omega),
        show r.length - i + j + 1 - (r.drop i).length = j + 1 from by
          rw [List.length_drop]; omega,
        List.take_take, Nat.min_eq_left (by omega : j + 1 ≤ i)]
    have hEq : [nextEl r (ly L r x)] ++
        (((r.drop (i + 1)) ++ r.take j) ++ [prevEl r (ztrans L N r x 0)])
        = (r.rotate i).take (r.length - i + j + 1) := by
      rw [hLHS, hRHS]
    rw [hEq]
    exact Kepler.Text.TameSpine.uniqTake (List.nodup_rotate.mpr hrnd)

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.ml1SUniq
