/-
  Kepler.Text.Reduction3Thm11 — J 战役 J3 T11 批（reduction3.hl:4269-4442）。

  ┌─ 件目（10 件待做 = 11 锚 − 已落 nfgtrans0；2 件 BLOCKED 不动）───────
  │   foldl_rcons              :4269 → §A foldlRcons（逐字）
  │   nfgtrans0                :4277 → 已落 DefsLayer `nfgtrans'Zero`，不重落
  │   cond_pair                :4433 → §A condPair（逐字）
  │   drop_iota                :4331 → §A dropIota（逐字）
  │   b_nfgtrans0              :4402 → §B bNfgtrans0Zero（逐字）
  │   batch_k                  :4417 → §B batchK（逐字）
  │   nfgtrans1                :4285 → §C nfgtrans1（条件槽形，见 DIFFERS）
  │   drop_core_triple         :4345 → §C dropCoreTriple（条件槽形）
  │   nfgtrans_add             :4373 → §C nfgtransAdd（条件槽形）
  │ ── BLOCKED（不动；缺前置定义/件，见 §5）──────────────────────
  │   nfgtrans_transform_count :4314 —— 需 subdivFace0Alt2 +
  │     subdivFace0_alt2_foldl_steps_alt（均未落，后件是 HOL 单件证明）
  │   b_nfgtransk              :4442 —— 需 subdivSingleStepInitialSeg /
  │     FinalSeg / Paired、subdivFace0BetaFoldlSteps、markedListElementPre、
  │     subdivFace0Alt2（均未落）+ assumptionSetK10 装配
  │   （Dangeyj/Hojodcm 两件**不缺**：memImpNotNil / ytransMemRtrans 已 #check）
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（条件槽形接口契约；J2 装配点，逐件写清）─────────────────
  │ 原则：树内 `transformCountNon0` / `transformCountAdd` / `coreTripleNonnil`
  │ 本身即条件槽形（多 `hfinal` 槽；T2/T3 先例）。HOL 的载体前提
  │ （good_list/good_list_nodes/marked_list/is_restricted）在 HOL 证明中
  │ 只经 `transform_assumption_v2` 用于产出 hfinal；该件未落（J2 门禁）。
  │ 故本文件以显式 `hfinal` 槽替代载体前提，逐字结论不变。
  │ 消除契约：**J2 `transform_assumption_v2` 落库后，在调用点由 hfinal
  │ 实例化即回到 HOL 逐字形**（无需改本文件陈述）。
  │
  │ 件：nfgtrans1（:4285）
  │   HOL 前提：good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧
  │             ¬final_list L r ∧ is_restricted (hypermap_of_list L)
  │   本件前提：hfinal : finalList L (rtrans L N r x (transformCount L N r x))
  │             + hnf : ¬ finalList L r（逐字保留）
  │   多出：hfinal；省去：载体四原子（由 hfinal 契约替代）
  │
  │ 件：drop_core_triple（:4345）
  │   HOL 前提：good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧
  │             i ≤ transform_count L N r x
  │   本件前提：hfinal + hi : i ≤ transformCount L N r x（逐字保留）
  │   多出：hfinal；省去：载体三原子
  │
  │ 件：nfgtrans_add（:4373）
  │   HOL 前提：good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧
  │             ¬final_list L r ∧ is_restricted (hypermap_of_list L) ∧
  │             i ≤ transform_count L N r x
  │   本件前提：hfinal + hi（hnf 在 HOL 证体与本件证体均未消费，不列）
  │   多出：hfinal；省去：载体四原子 + hnf（未消费）
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `t11_` 前缀；不重定义已落件。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm6D2
import Kepler.Text.Reduction3DefsLayer

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl findFaceDarts)
open Kepler.Graphs (Face Graph between fgraph)
open Kepler.Text.Reduction5 (Dart core indexf finalList ntrans rtrans transformCount
  ytrans ztrans)

/-! ## §0 私有辅助 -/

private theorem t11_take_one_eq {α : Type} (l : List α) (h : 0 < l.length) :
    l.take 1 = [l[0]'h] := by
  cases l with
  | nil => simp at h
  | cons a t => rfl

/-! ## §A 无依赖三件（foldl_rcons :4269 / drop_iota :4331 / cond_pair :4433） -/

/-- HOL `foldl_rcons`（reduction3.hl:4269）：`foldl f z (rcons ss s) =
f (foldl f z ss) s`。 -/
theorem foldlRcons {α β : Type} (f : β → α → β) (z : β) (ss : List α) (s : α) :
    List.foldl f z (ss ++ [s]) = f (List.foldl f z ss) s := by
  rw [List.foldl_append]
  rfl

/-- HOL `drop_iota`（reduction3.hl:4331）：`i <= j ==>
dropl i (iota n j) = iota (n+i) (j-i)`（`iota ↦ List.range'`，一行取自
`List.drop_range'`，step = 1）。 -/
theorem dropIota (i j n : ℕ) (h : i ≤ j) :
    (List.range' n j).drop i = List.range' (n + i) (j - i) := by
  rw [List.drop_range']
  simp

/-- HOL `cond_pair`（reduction3.hl:4433）：`(if a then (b,c) else (b',c)) =
((if a then b else b'),c)`。 -/
theorem condPair {α β : Type} (a : Prop) [Decidable a] (b b' : α) (c : β) :
    (if a then (b, c) else (b', c)) = ((if a then b else b'), c) := by
  by_cases h : a <;> simp [h]

/-! ## §B 定义展开两件（b_nfgtrans0 :4402 / batch_k :4417） -/

/-- HOL `b_nfgtrans0`（reduction3.hl:4402）：零步 `b_nfgtrans0` 是首态
（`batch0 … 0 = []` + `foldl` 空表；`fx = find_face L x`）。 -/
theorem bNfgtrans0Zero (f0 : Face) (g : Graph) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart) :
    bNfgtrans0 f0 g L N r x 0 =
      (((if (nextEl (findFaceDarts L x) x).1 = (ytrans L N r x 0).1 then none
          else some (prevEl f0.vertices (ytrans L N r x 0).1)), 0), f0, g) := by
  simp [bNfgtrans0, batch0, prebatch]

/-- HOL `batch_k`（reduction3.hl:4417）：`k = transform_count ==>
batch0 f L N r x k = dest_triple0 f [] (core_triple_v4 L N r x)`
（`dest_triple0_foldl_steps` 的 GSYM + `take` 超界即全表）。 -/
theorem batchK (f : List ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (k : ℕ)
    (hk : k = transformCount L N r x) :
    batch0 f L N r x k = destTriple0 f [] (coreTripleV4 L N r x) := by
  have htake : (coreTripleV4 L N r x).take k = coreTripleV4 L N r x := by
    rw [hk, ← coreTripleV4_length, List.take_length]
  have h := destTriple0FoldlSteps (coreTripleV4 L N r x) f [] (fun h => absurd rfl h)
  unfold batch0 prebatch
  rw [htake]
  exact h.symm

/-! ## §C nfgtrans 族三件（条件槽形；DIFFERS 见文件头） -/

/-- HOL `nfgtrans1`（reduction3.hl:4285；条件槽形）：
`nfgtrans' p L N r x 1` 展开为对首项 `core_triple_v4` 的一步
（`take1` + `transform_count_non0` + `core_triple_nonnil` + `el_core_triple`）。 -/
theorem nfgtrans1 (p : ℕ × Face × Graph) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart)
    (hfinal : finalList L (rtrans L N r x (transformCount L N r x)))
    (hnf : ¬ finalList L r) :
    nfgtrans' p L N r x 1 =
      subdivTripleStep p ((ytrans L N r x 0).1, (ztrans L N r x 0).1,
        (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length) := by
  have h0 : transformCount L N r x ≠ 0 := transformCountNon0 L N r x hfinal hnf
  have hpos : 0 < transformCount L N r x := Nat.pos_of_ne_zero h0
  have hne : coreTripleV4 L N r x ≠ [] := coreTripleNonnil L N r x hfinal hnf
  have hlen : 0 < (coreTripleV4 L N r x).length := by
    rw [coreTripleV4_length]
    exact hpos
  rw [nfgtrans']
  rw [show (coreTripleV4 L N r x).take 1 = [(coreTripleV4 L N r x)[0]'hlen]
      from t11_take_one_eq _ hlen]
  rw [List.foldl_cons, List.foldl_nil]
  rw [elCoreTriple L N r x 0 hpos]

/-- HOL `drop_core_triple`（reduction3.hl:4345；条件槽形）：
`dropl i (core_triple_v4 L N r x) = core_triple_v4 L (ntrans … i) (rtrans … i) x`
（逐下标 `el_core_triple` + `trans_add` 四联 + `transform_count_add`）。 -/
theorem dropCoreTriple (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (i : ℕ)
    (hfinal : finalList L (rtrans L N r x (transformCount L N r x)))
    (hi : i ≤ transformCount L N r x) :
    (coreTripleV4 L N r x).drop i =
      coreTripleV4 L (ntrans L N r x i) (rtrans L N r x i) x := by
  have hk' : transformCount L (ntrans L N r x i) (rtrans L N r x i) x
      = transformCount L N r x - i :=
    transformCountAdd L N r x i hfinal hi
  apply List.ext_getElem
  · rw [List.length_drop, coreTripleV4_length, coreTripleV4_length]
    exact hk'.symm
  · intro j hj1 hj2
    have hj1' : i + j < transformCount L N r x := by
      rw [List.length_drop, coreTripleV4_length] at hj1
      omega
    have hj2' : j < transformCount L (ntrans L N r x i) (rtrans L N r x i) x := by
      rw [← coreTripleV4_length]
      exact hj2
    rw [List.getElem_drop]
    rw [elCoreTriple L N r x (i + j) hj1']
    rw [elCoreTriple L (ntrans L N r x i) (rtrans L N r x i) x j hj2']
    have ht := transAdd L N r x i j
    have hy : ytrans L N r x (i + j)
        = ytrans L (ntrans L N r x i) (rtrans L N r x i) x j := by
      rw [Nat.add_comm i j]
      exact ht.2.2.1
    have hz : ztrans L N r x (i + j)
        = ztrans L (ntrans L N r x i) (rtrans L N r x i) x j := by
      rw [Nat.add_comm i j]
      exact ht.2.2.2
    simp only [hy, hz]

/-- HOL `nfgtrans_add`（reduction3.hl:4373；条件槽形）：
`nfgtrans' p L N r x (i+j) = nfgtrans' (nfgtrans' p L N r x i)
L (ntrans … i) (rtrans … i) x j`（`take_add` + `foldl_append` +
`drop_core_triple`）。 -/
theorem nfgtransAdd (p : ℕ × Face × Graph) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (i j : ℕ)
    (hfinal : finalList L (rtrans L N r x (transformCount L N r x)))
    (hi : i ≤ transformCount L N r x) :
    nfgtrans' p L N r x (i + j) =
      nfgtrans' (nfgtrans' p L N r x i) L (ntrans L N r x i) (rtrans L N r x i) x j := by
  rw [nfgtrans', nfgtrans', nfgtrans']
  rw [List.take_add, List.foldl_append, dropCoreTriple L N r x i hfinal hi]

end Kepler.Text.Reduction3

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.foldlRcons
#print axioms Kepler.Text.Reduction3.dropIota
#print axioms Kepler.Text.Reduction3.condPair
#print axioms Kepler.Text.Reduction3.bNfgtrans0Zero
#print axioms Kepler.Text.Reduction3.batchK
#print axioms Kepler.Text.Reduction3.nfgtrans1
#print axioms Kepler.Text.Reduction3.dropCoreTriple
#print axioms Kepler.Text.Reduction3.nfgtransAdd
