/-
  Kepler.Text.Reduction3Thm2 — J 战役 J3 定理层 T2 批 + T3 独立件预跳。

  ┌─ 批次定位与卡点（AGENTS §7：不硬啃）────────────────────────────
  │ T2 规划的 `transform_count_non0`（:796）与 `transform_count_add`
  │ （:515）经原文核对**均依赖 `reduction2.transform_assumption_v2_lemma`
  │ + KBWPBHQ.final_list_transform_count + KBWPBHQ0 + Nuxcoea.MIN_LEAST**：
  │   transform_count_non0 的 HOL 证明 = final_list_transform_count[`0`]
  │   （其前提含 transform_assumption_v2 L；终值 t=0 经 reduction2.trans0
  │   化为 final_list L r，与 ¬final 矛盾）；
  │   transform_count_add 另需 rtrans_final_prop（j2w1 落 Spine 岛，
  │   链岛不跨岛）+ Tame_list.AQIUNPP3 + Uaghhbm.MIN_NUM_SUBSET。
  │ transform_assumption_v2 的无条件形树内**未落**（j2w1 DELIVERY
  │ §1.4 缺口 A：AQ1-AQ13 章 13 文件），故两件按「前提挂槽」落
  │ **条件形**（hfinal 槽 = final_list L (rtrans … (transform_count …))，
  │ 即 final_list_transform_count 的结论；批 E 落库后一行代入即恢复原形）。
  │ `transform_count_not`（KBWPBHQ.hl:85）已由 j1w1 落
  │ `Kepler.Text.Reduction4.transformCount_not`，本批**不重复**。
  │ T3 预跳独立件（不触 marked/is_restricted 载体）：
  │   triple_data_nonnil :812 / core_triple_nonnil :833 /
  │   dest_triple0_nonnil :863 / hd_dest_triple0 :888 /
  │   last_dest_triple0 :913（末件如 2 轮内不收敛按 §7 止损回退）。
  └────────────────────────────────────────────────────────────────

  ┌─ 逐件对账 ─────────────────────────────────────────────────────
  │   min_num_translate  :291 → minNumTranslate（无条件全证）
  │   transform_count_non0 :796 → transformCountNon0（hfinal 槽）
  │   transform_count_add  :515 → transformCountAdd（hfinal 槽）
  │   （支撑）triple_data_v4 长度 = transform_count → tripleDataV4Length
  │   triple_data_nonnil   :812 → tripleDataNonnil（hfinal+¬final 形）
  │   core_triple_nonnil   :833 → coreTripleNonnil（hfinal+¬final 形）
  │   dest_triple0_nonnil  :863 → destTriple0Nonnil（无条件直证）
  │   hd_dest_triple0      :888 → hdDestTriple0（headD junk 缺省形）
  │   last_dest_triple0    :913 → lastDestTriple0（getLastD junk 缺省形）
  │ `size_core_triple`（:961）已由 D1 `coreTripleV4_length` 覆盖（勿重落）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ imports = `Kepler.Text.Reduction3Thm1`（闭包含 D1-D3b）。零 axiom/
  │ sorry/admit/native_decide。junk：`HD/LAST` ↦ headD/getLastD 固定缺省
  │ （分支守卫内缺省不出现）；`SOME/FST/SND` 折算同前批。`l'y` 全限定
  │ （Kepler.Text.ly 遮蔽雷区）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm1
import Kepler.Text.Reduction5

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl findFaceDarts)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart finalList minNum minNum_spec ntrans rtrans transformCount)

/-! ## §A `min_num_translate`（reduction3.hl:291，无条件全证）

`(?n. P n) ==> min_num {i | P i} + a = min_num {i + a | P i}`。
`minNum_spec` 的极小性/成员性双向夹逼（HOL 用 Tame_list.min_num_in/
min_num_le，Lean 侧二者即 minNum_spec 两投影）。 -/

/-- HOL `min_num_translate`（reduction3.hl:291）。 -/
theorem minNumTranslate (a : ℕ) (P : ℕ → Prop) (hne : ∃ n, P n) :
    minNum {i : ℕ | P i} + a = minNum {x : ℕ | ∃ i, P i ∧ i + a = x} := by
  have h1 : ({i : ℕ | P i} : Set ℕ).Nonempty := hne
  have h2 : ({x : ℕ | ∃ i, P i ∧ i + a = x} : Set ℕ).Nonempty := by
    obtain ⟨n, hn⟩ := hne
    exact ⟨n + a, n, hn, rfl⟩
  have hmem1 := (minNum_spec h1).1
  have hle1 := (minNum_spec h1).2
  have hmem2 := (minNum_spec h2).1
  have hle2 := (minNum_spec h2).2
  have hA : minNum {x : ℕ | ∃ i, P i ∧ i + a = x} ≤ minNum {i : ℕ | P i} + a :=
    hle2 _ ⟨minNum {i : ℕ | P i}, hmem1, rfl⟩
  obtain ⟨i0, hi0P, hi0eq⟩ := hmem2
  have hB : minNum {i : ℕ | P i} + a ≤ minNum {x : ℕ | ∃ i, P i ∧ i + a = x} := by
    calc minNum {i : ℕ | P i} + a ≤ i0 + a := Nat.add_le_add_right (hle1 i0 hi0P) a
      _ = minNum {x : ℕ | ∃ i, P i ∧ i + a = x} := hi0eq
  exact le_antisymm hB hA

/-! ## §B transform_count 条件形（hfinal 槽；批 E 落库后代入恢复原形）

`hfinal : finalList L (rtrans L N r x (transformCount L N r x))` 即
KBWPBHQ.final_list_transform_count（KBWPBHQ.hl:352）的结论——其前提
`transform_assumption_v2 L` 在树内未落（缺口 A）。两件为 reduction3.hl
:796/:515 的**条件槽形**：HOL 证明中 hfinal 之前的前提（good/
good_nodes/marked/transform_assumption_v2）只用于推出 hfinal。 -/

/-- HOL `transform_count_non0`（reduction3.hl:796）的**条件槽形**：
`hfinal` 槽（final_list_transform_count）+ `¬finalList L r` ⇒ 计数非零。
HOL 原前提 good_list/good_list_nodes/marked_list 仅经
transform_assumption_v2 用于产出 hfinal，见文件头卡点。 -/
theorem transformCountNon0 (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart)
    (hfinal : finalList L (rtrans L N r x (transformCount L N r x)))
    (hnf : ¬ finalList L r) : transformCount L N r x ≠ 0 := by
  intro h0
  rw [h0] at hfinal
  exact hnf (by simpa [rtrans] using hfinal)

/-- HOL `transform_count_add`（reduction3.hl:515）的**条件槽形**。 -/
theorem transformCountAdd (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (a : ℕ)
    (hfinal : finalList L (rtrans L N r x (transformCount L N r x)))
    (ha : a ≤ transformCount L N r x) :
    transformCount L (ntrans L N r x a) (rtrans L N r x a) x
      = transformCount L N r x - a := by
  have hT : minNum {i : ℕ | finalList L (rtrans L N r x i)}
      = transformCount L N r x := rfl
  -- 方向 1：t - a 属于变换后的集合（transAdd 把迭代对表接到 t = (t-a)+a）
  have hmem : transformCount L N r x - a ∈
      {i : ℕ | finalList L (rtrans L (ntrans L N r x a) (rtrans L N r x a) x i)} := by
    show finalList L (rtrans L (ntrans L N r x a) (rtrans L N r x a) x
      (transformCount L N r x - a))
    have h1 := (transAdd L N r x a (transformCount L N r x - a)).2.1
    rw [← h1, Nat.sub_add_cancel ha]
    exact hfinal
  have hne : ({i : ℕ | finalList L
      (rtrans L (ntrans L N r x a) (rtrans L N r x a) x i)} : Set ℕ).Nonempty :=
    ⟨_, hmem⟩
  have hspec' := minNum_spec hne
  have hle : minNum {i : ℕ | finalList L
      (rtrans L (ntrans L N r x a) (rtrans L N r x a) x i)}
      ≤ transformCount L N r x - a := hspec'.2 _ hmem
  -- 方向 2：变换后集合的极小元 + a 属于原集合
  have hneS : ({i : ℕ | finalList L (rtrans L N r x i)} : Set ℕ).Nonempty :=
    ⟨transformCount L N r x, hfinal⟩
  have hspec := minNum_spec hneS
  have h2 := (transAdd L N r x a (minNum {i : ℕ | finalList L
    (rtrans L (ntrans L N r x a) (rtrans L N r x a) x i)})).2.1
  have h3 : finalList L (rtrans L N r x (minNum {i : ℕ | finalList L
      (rtrans L (ntrans L N r x a) (rtrans L N r x a) x i)} + a)) := by
    rw [h2]
    exact hspec'.1
  have h4 : minNum {i : ℕ | finalList L (rtrans L N r x i)}
      ≤ minNum {i : ℕ | finalList L
        (rtrans L (ntrans L N r x a) (rtrans L N r x a) x i)} + a :=
    hspec.2 _ h3
  show minNum {i : ℕ | finalList L
      (rtrans L (ntrans L N r x a) (rtrans L N r x a) x i)}
      = transformCount L N r x - a
  omega

/-! ## §C triple_data / core_triple 长度与非空（:812/:833） -/

/-- 支撑件：`triple_data_v4` 的长度 = `transform_count`（HOL 由
Seq.size_iota + size_map 隐式使用；D1 的 `coreTripleV4_length` 的孪生）。 -/
theorem tripleDataV4Length (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : (tripleDataV4 L N r x).length = transformCount L N r x := by
  simp [tripleDataV4, List.length_range]

/-- HOL `triple_data_nonnil`（reduction3.hl:812）的**条件槽形**
（原前提 good/good_nodes/marked/¬final 经 transform_count_non0
化为计数非零；此处直接以 hfinal+¬final 立）。 -/
theorem tripleDataNonnil (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart)
    (hfinal : finalList L (rtrans L N r x (transformCount L N r x)))
    (hnf : ¬ finalList L r) : tripleDataV4 L N r x ≠ [] := by
  intro hempty
  have hlen := tripleDataV4Length L N r x
  rw [hempty] at hlen
  have h0 : transformCount L N r x = 0 := by simpa using hlen.symm
  exact transformCountNon0 L N r x hfinal hnf h0

/-- HOL `core_triple_nonnil`（reduction3.hl:833）的**条件槽形**。 -/
theorem coreTripleNonnil (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart)
    (hfinal : finalList L (rtrans L N r x (transformCount L N r x)))
    (hnf : ¬ finalList L r) : coreTripleV4 L N r x ≠ [] := by
  intro hempty
  have hlen := coreTripleV4_length L N r x
  rw [hempty] at hlen
  have h0 : transformCount L N r x = 0 := by simpa using hlen.symm
  exact transformCountNon0 L N r x hfinal hnf h0

/-! ## §D `dest_triple0` 端点机械（:863/:888/:913；无条件直证）

三者只依赖 D1 `destTriple0` 的定义（扁平累加器、四分支），
HOL 证明同样只做 LIST_INDUCT + flatten/hd/last 引理。 -/

/-- `destTriple0` 的 cons 展开方程（rfl 级；供 §D 证明使用）。 -/
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

/-- HOL `dest_triple0_nonnil`（reduction3.hl:863）：
`uvns ≠ [] ∨ s ≠ [] ==> dest_triple0 f s uvns ≠ []`。 -/
theorem destTriple0Nonnil (uvns : List (ℕ × ℕ × ℕ)) (f : List ℕ)
    (s : List (Option ℕ)) (h : uvns ≠ [] ∨ s ≠ []) :
    destTriple0 f s uvns ≠ [] := by
  induction uvns generalizing s with
  | nil =>
    rcases h with h | h
    · exact (h rfl).elim
    · simpa [destTriple0] using h
  | cons t ts ih =>
    obtain ⟨u, v, n⟩ := t
    rw [destTriple0_cons_eq]
    dsimp only
    by_cases h0 : s = []
    · rw [if_pos h0]
      exact ih _ (Or.inr (by simp))
    · rw [if_neg h0]
      by_cases h1 : (s.getLastD none).getD 0 = u
      · rw [if_pos h1]
        exact ih _ (Or.inr (by simp))
      · rw [if_neg h1]
        by_cases h2 : nextEl f ((s.getLastD none).getD 0) = u
        · rw [if_pos h2]
          exact ih _ (Or.inr (by simp))
        · rw [if_neg h2]
          exact ih _ (Or.inr (by simp))

/-- HOL `hd_dest_triple0`（reduction3.hl:888）：
`s ≠ [] ==> HD (dest_triple0 f s uvns) = HD s`（headD 缺省形）。 -/
theorem hdDestTriple0 (uvns : List (ℕ × ℕ × ℕ)) :
    ∀ (f : List ℕ) (s : List (Option ℕ)), s ≠ [] →
      (destTriple0 f s uvns).headD none = s.headD none := by
  induction uvns with
  | nil => intro f s _; rfl
  | cons t ts ih =>
    obtain ⟨u, v, n⟩ := t
    intro f s h
    rw [destTriple0_cons_eq]
    dsimp only
    rw [if_neg h]
    by_cases h1 : (s.getLastD none).getD 0 = u
    · rw [if_pos h1, ih f (s ++ List.replicate n none ++ [some v]) (by simp [h])]
      cases s with
      | nil => exact (h rfl).elim
      | cons a as => rfl
    · rw [if_neg h1]
      by_cases h2 : nextEl f ((s.getLastD none).getD 0) = u
      · rw [if_pos h2,
          ih f (s ++ [some u] ++ List.replicate n none ++ [some v]) (by simp [h])]
        cases s with
        | nil => exact (h rfl).elim
        | cons a as => rfl
      · rw [if_neg h2,
          ih f (s ++ (between f ((s.getLastD none).getD 0) u).map some ++ [some u]
            ++ List.replicate n none ++ [some v]) (by simp [h])]
        cases s with
        | nil => exact (h rfl).elim
        | cons a as => rfl

/-- HOL `last_dest_triple0`（reduction3.hl:913）：
`uvns ≠ [] ==> LAST (dest_triple0 f s uvns) = SOME (FST (SND (LAST uvns)))`
（getLastD 缺省形）。 -/
theorem lastDestTriple0 (uvns : List (ℕ × ℕ × ℕ)) :
    uvns ≠ [] → ∀ (f : List ℕ) (s : List (Option ℕ)),
      (destTriple0 f s uvns).getLast?
        = (uvns.getLast?).map (fun p => some p.2.1) := by
  induction uvns with
  | nil => intro h; exact absurd rfl h
  | cons t ts ih =>
    obtain ⟨u, v, n⟩ := t
    intro _ f s
    rw [destTriple0_cons_eq]
    dsimp only
    rcases hts : ts with _ | ⟨t2, ts2⟩
    · subst hts
      have hR : (([(u, v, n)] : List (ℕ × ℕ × ℕ)).getLast?).map (fun p => some p.2.1)
          = some (some v) := rfl
      rw [hR]
      repeat' split
      all_goals
        (simp only [destTriple0]
         simp [List.getLast?_append, List.getLast?_cons])
    · subst hts
      have hR : (((u, v, n) :: t2 :: ts2).getLast?).map (fun p => some p.2.1)
          = ((t2 :: ts2).getLast?).map (fun p => some p.2.1) := by
        simp [List.getLast?_cons_cons]
      rw [hR]
      repeat' split
      all_goals
        exact ih (by simp) f _

end Kepler.Text.Reduction3

-- 公理探针（编译即执行；目标标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.minNumTranslate
#print axioms Kepler.Text.Reduction3.transformCountNon0
#print axioms Kepler.Text.Reduction3.transformCountAdd
#print axioms Kepler.Text.Reduction3.tripleDataV4Length
#print axioms Kepler.Text.Reduction3.tripleDataNonnil
#print axioms Kepler.Text.Reduction3.coreTripleNonnil
#print axioms Kepler.Text.Reduction3.destTriple0Nonnil
#print axioms Kepler.Text.Reduction3.hdDestTriple0
#print axioms Kepler.Text.Reduction3.lastDestTriple0
