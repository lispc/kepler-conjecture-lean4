/-
  Kepler.Text.Reduction3Thm13 — J 战役 J3 T13 批（reduction3.hl:5146-5295）。

  ┌─ 件目（5 件中 3 件可做；2 件 BLOCKED 不动）─────────────────────
  │   batch_nonnil          :5146 → §B batchNonnil
  │   batch_nil_prebatch_nil :5179 → §B batchNilPrebatchNil
  │   the_last_last_prebatch :5202 → §B theLastLastPrebatch
  │ ── BLOCKED（T12 族未落 + subdiv 族未落，见 §末）──────────────
  │   b_nfgtrans1        :5232 —— 缺 bNfgtransSuc / subdivSingleStepNseg /
  │                              destTriple0RconsPaired
  │   b_nfgtrans_induction :5295 —— 上列全缺 + subdivSingleStepBetwn
  │                              （J2/Aq12 门禁）+ prebatchSucExplicit（在飞）
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（关键：绕开 T12 的 prebatch 显式件）─────────────────────
  │ HOL 证明 batch_nonnil 用 prebatch1 / prebatch_suc_explicit，
  │ the_last_last_prebatch 用 prebatch1 / prebatch_suc_explicit。
  │ 本文件改走**直接不变式**（同样成立、且零 T12 依赖）：
  │   ① `destTriple0Step` 的每个新增段都非空（逐分支 mem_append）；
  │   ② foldl 保持"每段非空"且 step 结果非空 ⇒ prebatch 非空当 take 非空；
  │   ③ `prebatch (i+1) = destTriple0Step (prebatch i) uvns[i]` 是**定义级**
  │      （`take_add_one` + `foldl_append`），不是 T12 的 prebatch_suc；
  │   ④ step 的末段末元 = `some v`（`getLastD_concat`）。
  │ 于是三件全部自足。HOL 前提逐字保留（本路线不消费，但陈述不动）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体口径（D3b 先例，同 T6D/T11）─────────────────────────────
  │ `good_list_nodes` / `is_restricted` / `marked_list` 三原子作 def 参数：
  │ GoodNodesL : fgraph ℕ → Prop、IsRestrictedL : fgraph ℕ → Prop、
  │ Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop；
  │ `good_list L` 为显式前提 `GoodList L`。**无 hfinal 槽**（本批三件不
  │ 消费 transform_count 非零类引理），故无 DIFFERS 语义差。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `t13_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm11

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl findFaceDarts GoodList)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart core finalList transformCount ytrans ztrans)

/-! ## §A 私有辅助（直接不变式路线） -/

/-- `destTriple0Step` 的结果非空（`getLastD` 非空 ⇒ 表非空）。 -/
private theorem t13_step_ne (f : List ℕ) (s : List (List (Option ℕ)))
    (t : ℕ × ℕ × ℕ) : destTriple0Step f s t ≠ [] := by
  intro h
  have hz := destTriple0StepLastNonnil f s t
  rw [h] at hz
  exact hz rfl

/-- `destTriple0Step` 新增的每一段都非空（四分支：单例或 `s ++ [非空段]`）。 -/
private theorem t13_step_all_ne (f : List ℕ) (s : List (List (Option ℕ)))
    (t : ℕ × ℕ × ℕ) (hall : ∀ seg ∈ s, seg ≠ []) :
    ∀ seg ∈ destTriple0Step f s t, seg ≠ [] := by
  obtain ⟨u, v, n⟩ := t
  unfold destTriple0Step
  dsimp only
  by_cases h0 : s.flatten = []
  · simp only [if_pos h0]
    intro seg hseg
    simp only [List.mem_singleton] at hseg
    subst hseg
    simp
  · simp only [if_neg h0]
    by_cases h1 : ((s.getLastD []).getLastD none).getD 0 = u
    · simp only [if_pos h1]
      intro seg hseg
      rw [List.mem_append] at hseg
      rcases hseg with hseg | hseg
      · exact hall seg hseg
      · simp only [List.mem_singleton] at hseg
        subst hseg
        simp
    · simp only [if_neg h1]
      by_cases h2 : nextEl f (((s.getLastD []).getLastD none).getD 0) = u
      · simp only [if_pos h2]
        intro seg hseg
        rw [List.mem_append] at hseg
        rcases hseg with hseg | hseg
        · exact hall seg hseg
        · simp only [List.mem_singleton] at hseg
          subst hseg
          simp
      · simp only [if_neg h2]
        intro seg hseg
        rw [List.mem_append] at hseg
        rcases hseg with hseg | hseg
        · exact hall seg hseg
        · simp only [List.mem_singleton] at hseg
          subst hseg
          simp

/-- foldl `destTriple0Step` 从每段非空的段表出发，结果每段非空。 -/
private theorem t13_foldl_all_ne (f : List ℕ) (uvns : List (ℕ × ℕ × ℕ)) :
    ∀ (s : List (List (Option ℕ))), (∀ seg ∈ s, seg ≠ []) →
      ∀ seg ∈ List.foldl (destTriple0Step f) s uvns, seg ≠ [] := by
  induction uvns with
  | nil =>
    intro s hall seg hseg
    simpa using hall seg hseg
  | cons t ts ih =>
    intro s hall
    rw [List.foldl_cons]
    exact ih _ (t13_step_all_ne f s t hall)

/-- foldl `destTriple0Step` 从非空段表出发恒非空。 -/
private theorem t13_foldl_ne_of_ne (f : List ℕ) (uvns : List (ℕ × ℕ × ℕ)) :
    ∀ (s : List (List (Option ℕ))), s ≠ [] →
      List.foldl (destTriple0Step f) s uvns ≠ [] := by
  induction uvns with
  | nil =>
    intro s hs
    simpa using hs
  | cons t ts ih =>
    intro s hs
    rw [List.foldl_cons]
    exact ih _ (t13_step_ne f s t)

/-- 非空输入 ⇒ 从空段表 foldl 的结果非空。 -/
private theorem t13_foldl_ne (f : List ℕ) (uvns : List (ℕ × ℕ × ℕ))
    (h : uvns ≠ []) : List.foldl (destTriple0Step f) [] uvns ≠ [] := by
  obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [List.foldl_cons]
  exact t13_foldl_ne_of_ne f ts _ (t13_step_ne f [] t)

/-- 单例段表的外层 `getLastD []`（定义级）。 -/
private theorem t13_outer_single (seg : List (Option ℕ)) :
    ([seg].getLastD []).getLastD none = seg.getLastD none := rfl

/-- 末段追加形的外层 `getLastD []`。 -/
private theorem t13_outer_append (s : List (List (Option ℕ))) (seg : List (Option ℕ)) :
    ((s ++ [seg]).getLastD []).getLastD none = seg.getLastD none := by
  rw [List.getLastD_concat]

/-- `destTriple0Step` 的末段末元 = `some v`（四分支都以 `[some v]` 收尾）。 -/
private theorem t13_step_last_seg (f : List ℕ) (s : List (List (Option ℕ)))
    (t : ℕ × ℕ × ℕ) :
    ((destTriple0Step f s t).getLastD []).getLastD none = some t.2.1 := by
  obtain ⟨u, v, n⟩ := t
  unfold destTriple0Step
  dsimp only
  by_cases h0 : s.flatten = []
  · rw [if_pos h0]
    rw [t13_outer_single, List.getLastD_concat]
  · rw [if_neg h0]
    by_cases h1 : ((s.getLastD []).getLastD none).getD 0 = u
    · rw [if_pos h1]
      rw [t13_outer_append, List.getLastD_concat]
    · rw [if_neg h1]
      by_cases h2 : nextEl f (((s.getLastD []).getLastD none).getD 0) = u
      · rw [if_pos h2]
        rw [t13_outer_append, List.getLastD_concat]
      · rw [if_neg h2]
        rw [t13_outer_append, List.getLastD_concat]

/-- 定义级 suc 展开：`prebatch (i+1) = step (prebatch i) uvns[i]`
（`take_add_one` + `foldl_append`；与 T12 的 `prebatch_suc` 无关）。 -/
private theorem t13_prebatch_suc (f : List ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (i : ℕ) (hi : i < transformCount L N r x) :
    prebatch f L N r x (i + 1) =
      destTriple0Step f (prebatch f L N r x i)
        ((coreTripleV4 L N r x)[i]'(by rw [coreTripleV4_length]; exact hi)) := by
  unfold prebatch
  rw [List.take_add_one,
    List.getElem?_eq_getElem (by rw [coreTripleV4_length]; exact hi),
    List.foldl_append]
  rfl

/-! ## §B T13 三件 -/

/-- HOL `batch_nonnil`（reduction3.hl:5146）：`0 < i < transform_count ==>
batch0 … i ≠ []`。直接不变式路线：`take i` 非空 ⇒ `prebatch` 非空且每段
非空 ⇒ `flatten` 非空。 -/
theorem batchNonnil
    (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (i : ℕ) (f : List ℕ) (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart)
    (hgood : GoodList L) (hnodes : GoodNodesL L) (hmarked : Marked L N r x)
    (hnfin : ¬ finalList L r) (hres : IsRestrictedL L) (huniq : f.Nodup)
    (hy : ∀ j, j < transformCount L N r x → (ytrans L N r x j).1 ∈ f)
    (hz : ∀ j, j < transformCount L N r x → (ztrans L N r x j).1 ∈ f)
    (hpos : 0 < i) (hlt : i < transformCount L N r x) :
    batch0 f L N r x i ≠ [] := by
  intro h
  unfold batch0 at h
  have htake : (coreTripleV4 L N r x).take i ≠ [] := by
    intro hz0
    have hlen := congrArg List.length hz0
    rw [List.length_take, coreTripleV4_length,
      Nat.min_eq_left (Nat.le_of_lt hlt)] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hpre : prebatch f L N r x i ≠ [] := by
    unfold prebatch
    exact t13_foldl_ne f _ htake
  have hall : ∀ seg ∈ prebatch f L N r x i, seg ≠ [] := by
    unfold prebatch
    exact t13_foldl_all_ne f _ [] (by intro seg hseg; simp at hseg)
  have hAll : ∀ seg ∈ prebatch f L N r x i, seg = [] :=
    List.flatten_eq_nil_iff.mp h
  obtain ⟨seg, hmem⟩ := List.exists_mem_of_ne_nil _ hpre
  exact hall seg hmem (hAll seg hmem)

/-- HOL `batch_nil_prebatch_nil`（reduction3.hl:5179）：
`batch0 … i = [] ⇒ prebatch … i = []`（扁平为空 ⇒ 所有段为空；
与"每段非空"矛盾）。 -/
theorem batchNilPrebatchNil
    (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (i : ℕ) (f : List ℕ) (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart)
    (hgood : GoodList L) (hnodes : GoodNodesL L) (hmarked : Marked L N r x)
    (hnfin : ¬ finalList L r) (hres : IsRestrictedL L) (huniq : f.Nodup)
    (hy : ∀ j, j < transformCount L N r x → (ytrans L N r x j).1 ∈ f)
    (hz : ∀ j, j < transformCount L N r x → (ztrans L N r x j).1 ∈ f)
    (hlt : i < transformCount L N r x) :
    batch0 f L N r x i = [] → prebatch f L N r x i = [] := by
  intro h
  unfold batch0 at h
  by_contra hne
  have hall : ∀ seg ∈ prebatch f L N r x i, seg ≠ [] := by
    unfold prebatch
    exact t13_foldl_all_ne f _ [] (by intro seg hseg; simp at hseg)
  have hAll : ∀ seg ∈ prebatch f L N r x i, seg = [] :=
    List.flatten_eq_nil_iff.mp h
  obtain ⟨seg, hmem⟩ := List.exists_mem_of_ne_nil _ hne
  exact hall seg hmem (hAll seg hmem)

/-- HOL `the_last_last_prebatch`（reduction3.hl:5202）：
`0 < i < transform_count ⇒ the (LAST (LAST (prebatch … i))) =
FST (ztrans … (PRE i))`（定义级 suc 展开 + 末段末元 = `some (ztrans i-1)`）。 -/
theorem theLastLastPrebatch
    (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (i : ℕ) (f : List ℕ) (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart)
    (hgood : GoodList L) (hnodes : GoodNodesL L) (hmarked : Marked L N r x)
    (hnfin : ¬ finalList L r) (hres : IsRestrictedL L) (huniq : f.Nodup)
    (hy : ∀ j, j < transformCount L N r x → (ytrans L N r x j).1 ∈ f)
    (hz : ∀ j, j < transformCount L N r x → (ztrans L N r x j).1 ∈ f)
    (hpos : 0 < i) (hlt : i < transformCount L N r x) :
    (((prebatch f L N r x i).getLastD []).getLastD none).getD 0
      = (ztrans L N r x (i - 1)).1 := by
  have hi1 : i - 1 < transformCount L N r x := by omega
  have hsucc : i - 1 + 1 = i := by omega
  conv_lhs => rw [← hsucc]
  rw [t13_prebatch_suc f L N r x (i - 1) hi1, t13_step_last_seg,
    elCoreTriple L N r x (i - 1) hi1]
  rfl

end Kepler.Text.Reduction3

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.batchNonnil
#print axioms Kepler.Text.Reduction3.batchNilPrebatchNil
#print axioms Kepler.Text.Reduction3.theLastLastPrebatch
