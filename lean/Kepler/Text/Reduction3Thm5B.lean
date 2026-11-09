/-
  Kepler.Text.Reduction3Thm5B — T5 自由件批（subdiv 族，reduction3.hl:1454-1770）。

  ┌─ 件目（9 件：6 自由件 + 3 由 patch A 解锁）───────────────────
  │ §A subdiv_single_step_paired   :1499 → subdivSingleStepPaired
  │    subdiv_triple_step_paired   :1548 → subdivTripleStepPaired
  │ §B subdivFace0_beta_foldl_steps     :1522 → subdivFace0BetaFoldlSteps
  │    subdivFace0_beta_foldl_steps_alt :1537 → subdivFace0BetaFoldlStepsAlt
  │ §C subdiv_single_step_nseg    :1729 → subdivSingleStepNseg
  │ §D subdivFace_subdivFace0_beta :1479 → subdivFaceSubdivFace0Beta
  │ §E subdivFace0_alt2_foldl_steps     :1560 → subdivFace0Alt2FoldlSteps
  │    subdivFace0_alt2_foldl_steps_alt :1572 → subdivFace0Alt2FoldlStepsAlt
  │ §F subdivFace0_beta_subdivFace0_alt :1454 → subdivFace0BetaSubdivFace0Alt
  │ 不做（J2/Aq12 门禁）：subdivSingleStepBetwn :1665、
  │   subdivSingleStepInitialSeg/FinalSeg :1742/:1767 及 betwn 系。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字）───────────────────────────────────
  │ ① `nextVertex f u = v /\ n = 0` ↦ Bool `f.nextVertex u == v && n == 0`
  │    （与 D2 def 逐字同款式；beq_iff_eq 等价）。
  │ ② `upt a (a+n)` ↦ `List.range' a n`；`nseq n NONE` ↦ `List.replicate n none`；
  │    `the o` ↦ `o.getD 0`；三元 let 模式 ↦ 右结合三元组投影 `.2.1/.2.2`。
  │ ③ `TL` ↦ `List.tail`；`HD vos` ↦ `vos.headD none`（配 `vos ≠ []`）；
  │    `SND(subdivFace0_beta …)` ↦ `(subdivFace0Beta …).2`（`Face × Graph`）。
  │ ④ `subdivFace` ↦ `Kepler.Graphs.subdivFace`（FaceDivision:76，
  │    `= subdivFace' g f vos.head!.get! 0 vos.tail`）。
  │ ⑤ §F 用 patch A 的 `subdivFace0Alt`（`Nat` 形定义）；本文件闭包含
  │    Mathlib，陈述仍用 `ℕ`（与 `Nat` 同一常量）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `t5b_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3DefsSubdivAlt
import Kepler.Text.Reduction3DefsLayer

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph fgraph splitFace makeFaceFinal subdivFace subdivFace')

/-! ## §A paired 两件（def 展开形） -/

/-- HOL `subdiv_single_step_paired`（reduction3.hl:1499）：
`subdivSingleStep` 的配对投影重述（Bool 条件随 D2 def 折算）。 -/
theorem subdivSingleStepPaired (p : (Option ℕ × ℕ) × Face × Graph) (vo : Option ℕ) :
    subdivSingleStep p vo =
      (if p.1.1 = none then ((vo, 0), p.2.1, p.2.2)
       else if vo = none then ((p.1.1, p.1.2 + 1), p.2.1, p.2.2)
       else
         let v := vo.getD 0
         let u := p.1.1.getD 0
         if p.2.1.nextVertex u == v && p.1.2 == 0 then ((vo, 0), p.2.1, p.2.2)
         else
           let ws := List.range' p.2.2.countVertices p.1.2
           let (_, f2, g') := splitFace p.2.2 u v p.2.1 ws
           ((vo, 0), f2, g')) := by
  obtain ⟨⟨uo, n⟩, f, g⟩ := p
  cases uo with
  | none =>
    cases vo <;> rfl
  | some u =>
    cases vo with
    | none => rfl
    | some v => rfl

/-- HOL `subdiv_triple_step_paired`（reduction3.hl:1548）：
`subdivTripleStep` 的配对投影重述（`upt n0 (n0+n)` ↦ `List.range' n0 n`）。 -/
theorem subdivTripleStepPaired (p : ℕ × Face × Graph) (uvn : ℕ × ℕ × ℕ) :
    subdivTripleStep p uvn =
      (let (u, v, n) := uvn
       let ws := List.range' p.1 n
       let (_, f2, g') := splitFace p.2.2 u v p.2.1 ws
       (n + p.1, f2, g')) := by
  obtain ⟨n0, f, g⟩ := p
  obtain ⟨u, v, n⟩ := uvn
  rfl

/-! ## §B subdivFace0_beta 的 foldl 桥（:1522/:1537） -/

/-- HOL `subdivFace0_beta_foldl_steps`（reduction3.hl:1522，GSYM 方向）：
`foldl subdivSingleStep p vos = subdivFace0Beta (p 的三分量) vos`。 -/
theorem subdivFace0BetaFoldlSteps (vos : List (Option ℕ))
    (p : (Option ℕ × ℕ) × Face × Graph) :
    List.foldl subdivSingleStep p vos =
      subdivFace0Beta p.2.2 p.2.1 p.1.1 p.1.2 vos := by
  obtain ⟨⟨uo, n⟩, f, g⟩ := p
  induction vos generalizing uo n f g with
  | nil => rfl
  | cons vo vos ih =>
    rw [List.foldl_cons]
    cases uo with
    | none =>
      change List.foldl subdivSingleStep (subdivSingleStep ((none, n), f, g) vo) vos
        = subdivFace0Beta g f vo 0 vos
      exact ih vo 0 f g
    | some u =>
      cases vo with
      | none =>
        change List.foldl subdivSingleStep (subdivSingleStep ((some u, n), f, g) none) vos
          = subdivFace0Beta g f (some u) (n + 1) vos
        exact ih (some u) (n + 1) f g
      | some v =>
        change List.foldl subdivSingleStep (subdivSingleStep ((some u, n), f, g) (some v)) vos
          = (if f.nextVertex u == v && n == 0 then subdivFace0Beta g f (some v) 0 vos
             else (let ws := List.range' g.countVertices n
                   let (_, f2, g') := splitFace g u v f ws
                   subdivFace0Beta g' f2 (some v) 0 vos))
        rw [show subdivSingleStep ((some u, n), f, g) (some v) =
            (if f.nextVertex u == v && n == 0 then ((some v, 0), f, g)
             else (let ws := List.range' g.countVertices n
                   let (_, f2, g') := splitFace g u v f ws
                   ((some v, 0), f2, g'))) from rfl]
        by_cases h : f.nextVertex u == v && n == 0
        · rw [if_pos h, if_pos h]
          exact ih (some v) 0 f g
        · rw [if_neg h, if_neg h]
          dsimp only
          exact ih (some v) 0 _ _

/-- HOL `subdivFace0_beta_foldl_steps_alt`（reduction3.hl:1537）：
`subdivFace0Beta g f u0 n vos = foldl subdivSingleStep ((u0,n),(f,g)) vos`。 -/
theorem subdivFace0BetaFoldlStepsAlt (g : Graph) (f : Face) (u0 : Option ℕ) (n : ℕ)
    (vos : List (Option ℕ)) :
    subdivFace0Beta g f u0 n vos = List.foldl subdivSingleStep ((u0, n), f, g) vos :=
  (subdivFace0BetaFoldlSteps vos ((u0, n), f, g)).symm

/-! ## §C `nseq` 段（:1729） -/

/-- HOL `subdiv_single_step_nseg`（reduction3.hl:1729）：
`foldl subdivSingleStep ((SOME u,k),f,g) (nseq n NONE) = ((SOME u,n+k),f,g)`。 -/
theorem subdivSingleStepNseg (n u k : ℕ) (f : Face) (g : Graph) :
    List.foldl subdivSingleStep ((some u, k), f, g) (List.replicate n none)
      = ((some u, n + k), f, g) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons]
    show List.foldl subdivSingleStep ((some u, k + 1), f, g) (List.replicate n none)
      = ((some u, n + 1 + k), f, g)
    rw [ih (k + 1)]
    simp only [Nat.add_comm, Nat.add_left_comm]

/-! ## §D `subdivFace_subdivFace0_beta`（:1479） -/

/-- 私有桥：`subdivFace' g f u n vos = makeFaceFinal (β).2.1 (β).2.2`，
`β = subdivFace0Beta g f (some u) n vos`（同构循环，定义级归纳）。 -/
private theorem t5b_subdivFace'_beta (g : Graph) (f : Face) (u n : ℕ) :
    ∀ vos : List (Option ℕ),
      subdivFace' g f u n vos =
        makeFaceFinal (subdivFace0Beta g f (some u) n vos).2.1
          (subdivFace0Beta g f (some u) n vos).2.2
  | [] => rfl
  | vo :: vos => by
    cases vo with
    | none =>
      change subdivFace' g f u (n + 1) vos
        = makeFaceFinal (subdivFace0Beta g f (some u) (n + 1) vos).2.1
            (subdivFace0Beta g f (some u) (n + 1) vos).2.2
      exact t5b_subdivFace'_beta g f u (n + 1) vos
    | some v =>
      rw [show subdivFace' g f u n (some v :: vos) =
          (if f.nextVertex u == v && n == 0 then subdivFace' g f v 0 vos
           else (let ws := List.range' g.countVertices n
                 let (_, f2, g') := splitFace g u v f ws
                 subdivFace' g' f2 v 0 vos)) from rfl]
      rw [show subdivFace0Beta g f (some u) n (some v :: vos) =
          (if f.nextVertex u == v && n == 0 then subdivFace0Beta g f (some v) 0 vos
           else (let ws := List.range' g.countVertices n
                 let (_, f2, g') := splitFace g u v f ws
                 subdivFace0Beta g' f2 (some v) 0 vos)) from rfl]
      by_cases h : f.nextVertex u == v && n == 0
      · rw [if_pos h, if_pos h]
        exact t5b_subdivFace'_beta g f v 0 vos
      · rw [if_neg h, if_neg h]
        dsimp only
        exact t5b_subdivFace'_beta _ _ v 0 _

/-- HOL `subdivFace_subdivFace0_beta`（reduction3.hl:1479）：
`vos ≠ []` 且 `HD vos` 为 `SOME` 时，
`subdivFace g f vos = makeFaceFinal f' g'`（`(·,f',g') = subdivFace0Beta g f NONE 0 vos`）。 -/
theorem subdivFaceSubdivFace0Beta (g : Graph) (f : Face) (vos : List (Option ℕ))
    (hne : vos ≠ []) (his : (vos.headD none).isSome = true) :
    subdivFace g f vos =
      (let uon := subdivFace0Beta g f none 0 vos
       makeFaceFinal uon.2.1 uon.2.2) := by
  obtain ⟨u, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  cases u with
  | none => simp [List.headD] at his
  | some w =>
    show subdivFace' g f w 0 rest =
      makeFaceFinal (subdivFace0Beta g f none 0 (some w :: rest)).2.1
        (subdivFace0Beta g f none 0 (some w :: rest)).2.2
    rw [t5b_subdivFace'_beta g f w 0 rest]
    rfl

/-! ## §E `subdivFace0_alt2` 的 foldl 桥（:1560/:1572，patch A 解锁） -/

/-- HOL `subdivFace0_alt2_foldl_steps`（reduction3.hl:1560，GSYM 方向）：
`SND (foldl subdivTripleStep p uvns) = subdivFace0Alt2 (p 的三分量) uvns`。 -/
theorem subdivFace0Alt2FoldlSteps (uvns : List (ℕ × ℕ × ℕ))
    (p : ℕ × Face × Graph) :
    (List.foldl subdivTripleStep p uvns).2 = subdivFace0Alt2 p.2.2 p.2.1 p.1 uvns := by
  obtain ⟨n0, f, g⟩ := p
  induction uvns generalizing n0 f g with
  | nil => rfl
  | cons uvn uvns ih =>
    obtain ⟨u, v, n⟩ := uvn
    rw [List.foldl_cons]
    rw [show subdivTripleStep (n0, f, g) (u, v, n) =
        (n + n0, (splitFace g u v f (List.range' n0 n)).2.1,
          (splitFace g u v f (List.range' n0 n)).2.2) from rfl]
    exact ih _ _ _

/-- HOL `subdivFace0_alt2_foldl_steps_alt`（reduction3.hl:1572）：
`subdivFace0Alt2 g f n uvns = SND (foldl subdivTripleStep (n,f,g) uvns)`。 -/
theorem subdivFace0Alt2FoldlStepsAlt (g : Graph) (f : Face) (n : ℕ)
    (uvns : List (ℕ × ℕ × ℕ)) :
    subdivFace0Alt2 g f n uvns = (List.foldl subdivTripleStep (n, f, g) uvns).2 :=
  (subdivFace0Alt2FoldlSteps uvns (n, f, g)).symm

/-! ## §F `subdivFace0_beta_subdivFace0_alt`（:1454，patch A 解锁） -/

/-- 私有件：`SND(subdivFace0Beta g f (SOME u) n vos) = subdivFace0Alt g f u n vos`
（两循环逐分支同构，`LIST_INDUCT` 形）。 -/
private theorem t5b_beta_alt (g : Graph) (f : Face) (u n : ℕ) :
    ∀ vos : List (Option ℕ),
      (subdivFace0Beta g f (some u) n vos).2 = subdivFace0Alt g f u n vos
  | [] => rfl
  | vo :: vos => by
    cases vo with
    | none =>
      change (subdivFace0Beta g f (some u) (n + 1) vos).2
        = subdivFace0Alt g f u (n + 1) vos
      exact t5b_beta_alt g f u (n + 1) vos
    | some v =>
      rw [show subdivFace0Beta g f (some u) n (some v :: vos) =
          (if f.nextVertex u == v && n == 0 then subdivFace0Beta g f (some v) 0 vos
           else (let ws := List.range' g.countVertices n
                 let (_, f2, g') := splitFace g u v f ws
                 subdivFace0Beta g' f2 (some v) 0 vos)) from rfl]
      rw [show subdivFace0Alt g f u n (some v :: vos) =
          (if f.nextVertex u == v && n == 0 then subdivFace0Alt g f v 0 vos
           else (let ws := List.range' g.countVertices n
                 let (_, f2, g') := splitFace g u v f ws
                 subdivFace0Alt g' f2 v 0 vos)) from rfl]
      by_cases h : f.nextVertex u == v && n == 0
      · rw [if_pos h, if_pos h]
        exact t5b_beta_alt g f v 0 vos
      · rw [if_neg h, if_neg h]
        dsimp only
        exact t5b_beta_alt _ _ v 0 _

/-- HOL `subdivFace0_beta_subdivFace0_alt`（reduction3.hl:1454）：
两合取——(a) `vos ≠ []` 且 `SOME u = HD vos` 时
`SND(subdivFace0Beta g f NONE 0 vos) = subdivFace0Alt g f u 0 (TL vos)`；
(b) `SND(subdivFace0Beta g f (SOME u) n vos) = subdivFace0Alt g f u n vos`。 -/
theorem subdivFace0BetaSubdivFace0Alt (vos : List (Option ℕ)) (g : Graph)
    (f : Face) (u n : ℕ) :
    (vos ≠ [] → vos.headD none = some u →
      (subdivFace0Beta g f none 0 vos).2 = subdivFace0Alt g f u 0 vos.tail) ∧
    ((subdivFace0Beta g f (some u) n vos).2 = subdivFace0Alt g f u n vos) := by
  have hb := t5b_beta_alt g f u n vos
  constructor
  · intro hne hhd
    obtain ⟨w, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    cases w with
    | none => simp [List.headD] at hhd
    | some w' =>
      have hwu : w' = u := by simpa using hhd
      subst hwu
      show (subdivFace0Beta g f none 0 (some w' :: rest)).2
        = subdivFace0Alt g f w' 0 rest
      rw [show subdivFace0Beta g f none 0 (some w' :: rest)
          = subdivFace0Beta g f (some w') 0 rest from rfl]
      exact t5b_beta_alt g f w' 0 rest
  · exact hb

end Kepler.Text.Reduction3

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.subdivSingleStepPaired
#print axioms Kepler.Text.Reduction3.subdivTripleStepPaired
#print axioms Kepler.Text.Reduction3.subdivFace0BetaFoldlSteps
#print axioms Kepler.Text.Reduction3.subdivFace0BetaFoldlStepsAlt
#print axioms Kepler.Text.Reduction3.subdivSingleStepNseg
#print axioms Kepler.Text.Reduction3.subdivFaceSubdivFace0Beta
#print axioms Kepler.Text.Reduction3.subdivFace0Alt2FoldlSteps
#print axioms Kepler.Text.Reduction3.subdivFace0Alt2FoldlStepsAlt
#print axioms Kepler.Text.Reduction3.subdivFace0BetaSubdivFace0Alt
