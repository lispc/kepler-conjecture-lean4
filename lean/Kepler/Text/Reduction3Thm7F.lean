/-
  Kepler.Text.Reduction3Thm7F — T7F 批：`subdiv_face0_alt2_finals`（reduction3.hl:456）
  + `subdiv_faceFinal2_finals`（:488）；后者消费章程新 def `subdivFaceFinal2`
  （已追加于 `Reduction3DefsSubdivAlt.lean` 同文件）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ §A subdivFace0Alt2Finals   reduction3.hl:456
  │ §B subdivFaceFinal2Finals  reduction3.hl:488
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字）───────────────────────────────────
  │ ① `finals` ↦ `Kepler.Graphs.finals`（`g.faces.filter Face.final`，
  │    定义级同 HOL）。
  │ ② `MEM f (faces g)` ↦ `f ∈ g.faces`；`~SND f` ↦ `f.final = false`。
  │ ③ 件2 结论 `SND (subdivFace0_alt2 …)` ↦ `(subdivFace0Alt2 …).2`。
  │ ④ 件3 的 `set_of_list (finals …) SUBSET set_of_list (finals g) UNION
  │    {setFinal …}` ↦ 点态 `∀ x, x ∈ finals … → x ∈ finals g ∨
  │    x = setFinal …`（`set_of_list l = {x | x ∈ l}` 定义展开，逐字等价；
  │    树内同形 `setOfList` 只在无关的 PackingAuto2，本文件不引）。
  │ ⑤ `subdiv_faceFinal2` ↦ 章程新 def `subdivFaceFinal2`
  │    （`let p := subdivFace0Alt2 … (countVertices g) …; makeFaceFinal p.1 p.2`）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线 ────────────────────────────────────────────────────────
  │ 私有弱形 `splitFaceFinals`：`~SND f ⇒
  │ finals (SND (SND (splitFace …))) = finals g`（HOL reduction1.hl:2588）。
  │ 树内仅有 `splitFace_incr_faces`（需 `pre_splitFace`，强于 HOL 前提）与
  │ `set_finals_splitFace`（成员 iff），故同证重落：私件
  │ `t7f_filterReplaceSingleton`（InvariantsC 私件同证）+ `filter_append`。
  │ 件2 对 `vs` 归纳：cons 步拆 `splitFace`；新面 `.2.1` 经
  │ `t7f_splitFaceAddF21` 入 faces、`.2.1.final = false`（rfl）续归纳；
  │ 旧面 finals 由弱形桥接（HOL 证体逐句同构）。
  │ 件3：`subdivFaceFinal2` 展开 → `finals (makeFaceFinal p.1 p.2)` →
  │ `replace5` 拆 `replace p.1 [setFinal p.1] p.2.faces`；非 setFinal 支
  │ 回 `p.2`，再经件2 回 `g`。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `t7f_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3DefsSubdivAlt
import Kepler.Graphs.ListAuxLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph finals makeFaceFinal setFinal replace replace3 replace5 splitFace split_face)

/-! ## §0 私有弱形 `splitFace_finals`（HOL reduction1.hl:2588 同证重落） -/

/-- `replace` 单点替换前后 `filter P` 不变（被换元素与新元素都不满足 `P`；
`InvariantsC` 私件 `filter_replace_singleton_of_false` 同证重落）。 -/
private theorem t7f_filterReplaceSingleton {α : Type} {P : α → Bool} [BEq α] [LawfulBEq α]
    {x y : α} {xs : List α} (hx : P x = false) (hy : P y = false) :
    (replace x [y] xs).filter P = xs.filter P := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    by_cases hzx : z = x
    · subst hzx
      have e1 : replace z [y] (z :: zs) = [y] ++ zs := by
        simp only [replace, beq_self_eq_true, ↓reduceIte]
      have e2 : [y].filter P = [] := by
        rw [List.filter_cons, if_neg (by simp [hy]), List.filter_nil]
      have e3 : (z :: zs).filter P = zs.filter P := by
        rw [List.filter_cons, if_neg (by simp [hx])]
      rw [e1, List.filter_append, e2, List.nil_append, e3]
    · have e1 : replace x [y] (z :: zs) = z :: replace x [y] zs := by
        simp only [replace, if_neg (fun h => hzx (beq_iff_eq.mp h))]
      rw [e1, List.filter_cons, List.filter_cons]
      by_cases hpz : P z = true
      · rw [if_pos hpz, if_pos hpz, ih]
      · rw [if_neg hpz, if_neg hpz, ih]

/-- HOL `Reduction1.splitFace_finals`（reduction1.hl:2588）弱形：
`~SND f ⇒ finals (SND (SND (splitFace g r v f ws))) = finals g`。
（HOL 前提只有 `~SND f`；树内 `splitFace_incr_faces` 需 `pre_splitFace`，更强。） -/
theorem splitFaceFinals (g : Graph) (u v : Nat) (f : Face) (ws : List Nat)
    (hfin : f.final = false) :
    finals (splitFace g u v f ws).2.2 = finals g := by
  have hf1 : (split_face f u v ws).1.final = false := rfl
  have hf2 : (split_face f u v ws).2.final = false := rfl
  show (replace f [(split_face f u v ws).2] g.faces ++
      [(split_face f u v ws).1]).filter Face.final = g.faces.filter Face.final
  rw [List.filter_append,
    show ([(split_face f u v ws).1].filter Face.final) = [] from by simp [hf1],
    List.append_nil]
  exact t7f_filterReplaceSingleton hfin hf2

/-- HOL `MEM_splitFace2`（tame_list.hl:4750）同证重落：
`MEM f (faces g) ⇒ MEM f2 (faces (SND (SND (splitFace …))))`。 -/
private theorem t7f_splitFaceAddF21 (g : Graph) (u v : Nat) (f : Face) (ws : List Nat)
    (hf : f ∈ g.faces) :
    (splitFace g u v f ws).2.1 ∈ (splitFace g u v f ws).2.2.faces := by
  show (split_face f u v ws).2 ∈
    replace f [(split_face f u v ws).2] g.faces ++ [(split_face f u v ws).1]
  exact List.mem_append_left _ (replace3 hf List.mem_cons_self)

/-- `splitFace` 第二面非 final（rfl；`FaceDivisionProps1.splitFace_nonFinal_face` 同体）。 -/
private theorem t7f_splitFaceNonFinal (g : Graph) (u v : Nat) (f : Face) (ws : List Nat) :
    (splitFace g u v f ws).2.1.final = false := rfl

/-! ## §A `subdiv_face0_alt2_finals`（reduction3.hl:456） -/

/-- HOL `subdivFace0_alt2_finals`（reduction3.hl:456）：
`MEM f (faces g) ∧ ~SND f ⇒ finals g = finals (SND (subdivFace0_alt2 g f n vs))`。 -/
theorem subdivFace0Alt2Finals (vs : List (Nat × Nat × Nat)) (g : Graph) (f : Face) (n : Nat)
    (hf : f ∈ g.faces) (hfin : f.final = false) :
    finals g = finals (subdivFace0Alt2 g f n vs).2 := by
  induction vs generalizing g f n with
  | nil =>
    show finals g = finals (f, g).2
    rfl
  | cons uvn vs ih =>
    obtain ⟨u, v, n'⟩ := uvn
    rw [show subdivFace0Alt2 g f n ((u, v, n') :: vs) =
        subdivFace0Alt2 (splitFace g u v f (List.range' n n')).2.2
          (splitFace g u v f (List.range' n n')).2.1 (n' + n) vs from rfl]
    exact (splitFaceFinals g u v f (List.range' n n') hfin).symm.trans
      (ih (splitFace g u v f (List.range' n n')).2.2
        (splitFace g u v f (List.range' n n')).2.1 (n' + n)
        (t7f_splitFaceAddF21 g u v f (List.range' n n') hf)
        (t7f_splitFaceNonFinal g u v f (List.range' n n')))

/-! ## §B `subdiv_faceFinal2_finals`（reduction3.hl:488） -/

/-- HOL `subdivFaceFinal2_finals`（reduction3.hl:488）：
`MEM f (faces g) ∧ ~SND f ⇒ set_of_list (finals (subdivFaceFinal2 g f vs)) ⊆
set_of_list (finals g) ∪ {setFinal (FST (subdivFace0_alt2 g f (countVertices g) vs))}`
（结论按 DIFFERS ④ 点态展开）。 -/
theorem subdivFaceFinal2Finals (vs : List (Nat × Nat × Nat)) (g : Graph) (f : Face)
    (hf : f ∈ g.faces) (hfin : f.final = false) :
    ∀ x : Face, x ∈ finals (subdivFaceFinal2 g f vs) →
      x ∈ finals g ∨ x = setFinal (subdivFace0Alt2 g f g.countVertices vs).1 := by
  intro x hx
  have hx' : x ∈ (makeFaceFinal (subdivFace0Alt2 g f g.countVertices vs).1
      (subdivFace0Alt2 g f g.countVertices vs).2).faces.filter Face.final := hx
  obtain ⟨hmem, hfind⟩ := List.mem_filter.mp hx'
  have hrep : x ∈ replace (subdivFace0Alt2 g f g.countVertices vs).1
      [setFinal (subdivFace0Alt2 g f g.countVertices vs).1]
      (subdivFace0Alt2 g f g.countVertices vs).2.faces := hmem
  rcases replace5 hrep with hx2 | hx2
  · left
    have hbridge : finals (subdivFace0Alt2 g f g.countVertices vs).2 = finals g :=
      (subdivFace0Alt2Finals vs g f g.countVertices hf hfin).symm
    rw [← hbridge]
    exact List.mem_filter.mpr ⟨hx2, hfind⟩
  · right
    rw [List.mem_singleton] at hx2
    exact hx2

end Kepler.Text.Reduction3

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.splitFaceFinals
#print axioms Kepler.Text.Reduction3.subdivFace0Alt2Finals
#print axioms Kepler.Text.Reduction3.subdivFaceFinal2Finals
