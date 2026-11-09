/-
  Kepler.Text.ChainBridgeParts — parts/quotientList 桥 + 链/Spine 定义族
  剩余组件完整 iff（`markedList ↔ MarkedListSpineFull` 的最后一块）。

  ┌─ 对象与路线（编排者 2026-11-09 排期：T3 后、T4 前）──────────────
  │ 链侧 `Reduction5.partitionIntoAtom0`（`eq_3` 方程形：
  │ `if (n r == a.headD r) = true then … else …`，Prop-ite）vs Spine 侧
  │ `TameSpine.partitionIntoAtom0`（`if acc = [] … else if n r =
  │ acc.head!.head! …`）。路线：对 `l` 归纳、泛化 `acc`、不变式
  │ 「acc 原子非空」（递归保持）；条件桥经 `beq_iff_eq` + `headD≡head!`
  │ （非空）。由此 `parts = partsSpine`、`quotientList = quotientListSpine`，
  │ 继以 `flagList`/`sFlagList`/`markedList` 完整 iff。
  │ **sFlagList 挂 sList 槽**：`lm`(minNum/epsilon) vs `lMSpine`(sInf)
  │ 在极值集空（r=[] 且 x 为 fList 不动点）时 junk 不可证等
  │ （inst 车 §12.3-2）；条件形可落，槽由消费处 `Nonempty` 供给。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ imports = ChainListsL2 + Reduction3DefsAssumptionInst +
  │ TameSpine.TameList13（闭包 Assembly-free，inst 车 §D 已核）。
  │ 零 axiom/sorry/admit/native_decide。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.ChainListsL2
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.TameSpine.TameList13

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.ChainBridge

open Kepler.Assembly (GoodList eList fList listOfDarts nextEl)
open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart coreList finalList lm parts quotientList)
open Kepler.Text.ChainLists (findList fLast loopList normalList oneStepList
  contourList finalDartList flagList sFlagList sList markedList)
open Kepler.Text.TameLp (hypermapOfList)

/-! ## §A junk/条件辅助 -/

private theorem headD_congr_ne {α : Type} {l : List α} (h : l ≠ []) (d₁ d₂ : α) :
    l.headD d₁ = l.headD d₂ := by
  cases l with
  | nil => exact (h rfl).elim
  | cons x xs => rfl

private theorem head!_eq_headD_of_ne {α : Type} [Inhabited α] {l : List α}
    (h : l ≠ []) (d : α) : l.head! = l.headD d := by
  cases l with
  | nil => exact (h rfl).elim
  | cons x xs => rfl

/-! ## §B `partitionIntoAtom0` 桥（第 1 步，方程形见 `eq_1/eq_2/eq_3`） -/

private def AtomsNE (acc : List (List Dart)) : Prop := ∀ a ∈ acc, a ≠ []

private theorem atomsNE_cons {a : List Dart} {as : List (List Dart)}
    (h : AtomsNE (a :: as)) : a ≠ [] ∧ AtomsNE as :=
  ⟨h a List.mem_cons_self, fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem partitionIntoAtom0_eq (n : Dart → Dart) :
    ∀ (acc : List (List Dart)) (l : List Dart), AtomsNE acc →
      Reduction5.partitionIntoAtom0 n acc l
        = TameSpine.partitionIntoAtom0 n acc l := by
  intro acc l
  induction l generalizing acc with
  | nil =>
    intro _
    rw [Reduction5.partitionIntoAtom0.eq_1, TameSpine.partitionIntoAtom0.eq_1]
  | cons r rs ih =>
    intro hne
    cases acc with
    | nil =>
      rw [Reduction5.partitionIntoAtom0.eq_2, TameSpine.partitionIntoAtom0.eq_2,
        if_pos rfl]
      exact ih [[r]] fun x hx => by
        rw [List.mem_singleton] at hx
        subst hx
        exact List.cons_ne_nil _ _
    | cons a as =>
      obtain ⟨ha, has⟩ := atomsNE_cons hne
      have hhead : a.headD r = a.head! :=
        (headD_congr_ne ha r (0, 0)).trans (head!_eq_headD_of_ne ha (0, 0)).symm
      have hcond : ((n r == a.headD r) = true) ↔ (n r = (a :: as).head!.head!) := by
        rw [beq_iff_eq]
        rw [show (a :: as).head! = a from rfl]
        constructor
        · intro h
          rw [h, hhead]
        · intro h
          rw [h, hhead]
      rw [Reduction5.partitionIntoAtom0.eq_3, TameSpine.partitionIntoAtom0.eq_2,
        if_neg (List.cons_ne_nil a as)]
      have ihne : AtomsNE ((r :: a) :: as) := by
        intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact List.cons_ne_nil _ _
        · exact has x hx
      have ihne2 : AtomsNE ([r] :: a :: as) := by
        intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact List.cons_ne_nil _ _
        · rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ha
          · exact has x hx
      by_cases hc0 : ((n r == a.headD r) = true)
      · rw [if_pos hc0, if_pos (hcond.mp hc0)]
        exact ih ((r :: a) :: as) ihne
      · rw [if_neg hc0, if_neg (fun hh => hc0 (hcond.mpr hh))]
        exact ih ([r] :: a :: as) ihne2

/-! ## §C `parts` / `quotientList` 桥（第 2 步） -/

theorem parts_eq_partsSpine (L : fgraph ℕ) (r : List Dart) :
    parts L r = Kepler.Text.TameSpine.partsSpine L r := by
  unfold parts Kepler.Text.TameSpine.partsSpine
    Reduction5.partitionIntoAtom Kepler.Text.TameSpine.partitionIntoAtom
  rw [partitionIntoAtom0_eq (fun d => fList L (eList d)) [] r.reverse]
  exact fun a ha => absurd ha List.not_mem_nil

theorem coreList_eq_coreListSpine (PN : List (List (List Dart))) :
    coreList PN = Kepler.Text.TameSpine.coreListSpine PN := by
  unfold coreList Kepler.Text.TameSpine.coreListSpine
  congr 1
  funext f
  congr 1
  funext x
  cases x with
  | nil => rfl
  | cons y ys => rfl

theorem quotientList_eq_quotientListSpine (L : fgraph ℕ) (N : List (List Dart)) :
    quotientList L N = Kepler.Text.TameSpine.quotientListSpine L N := by
  unfold quotientList Kepler.Text.TameSpine.quotientListSpine
  rw [show N.map (parts L) = N.map (Kepler.Text.TameSpine.partsSpine L) from
    List.map_congr_left (fun r _ => parts_eq_partsSpine L r)]
  rw [coreList_eq_coreListSpine]

/-! ## §D `flagList` / `sFlagList` 完整 iff -/

theorem flagList_iff_flagListSpine (L : fgraph ℕ) (N : List (List Dart)) :
    flagList L N ↔ Kepler.Text.TameSpine.FlagListSpine L N := by
  unfold flagList Kepler.Text.TameSpine.FlagListSpine
  rw [finalDartList_eq_finalDartListSpine L N]
  unfold contourList Kepler.Text.TameSpine.ContourListSpine oneStepList
    Kepler.Text.TameSpine.oneStepListSpine
  simp only [getElem!_eq_getD]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · intro u hu v hv
      obtain ⟨s, hcs, hne, hhd, hlst, hsub⟩ := h1 u v hu hv
      exact ⟨s, hcs, hne, by rw [head!_eq_headD_of_ne hne (0, 0)]; exact hhd,
        by rw [getLast!_eq_getLastD]; exact hlst, fun z hz => hsub hz⟩
    · intro r' p y hy hp hrN hnf
      rw [← parts_eq_partsSpine L r'] at hp
      exact h2 r' p y (hy.trans (getLast!_eq_getLastD p)) hp hrN hnf
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · intro u v hu hv
      obtain ⟨s, hcs, hne, hhd, hlst, hsub⟩ := h1 u hu v hv
      exact ⟨s, hcs, hne, (head!_eq_headD_of_ne hne (0, 0)).symm.trans hhd,
        by rw [← getLast!_eq_getLastD]; exact hlst, fun z hz => hsub z hz⟩
    · intro r' p y hy hp hrN hnf
      rw [parts_eq_partsSpine L r'] at hp
      exact h2 r' p y (hy.trans (getLast!_eq_getLastD p).symm) hp hrN hnf

theorem sFlagList_iff_sFlagListSpine (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart)
    (hs : sList L r x = Kepler.Text.TameSpine.sListSpine L r x) :
    sFlagList L N r x ↔ Kepler.Text.TameSpine.SFlagListSpine L N r x := by
  unfold sFlagList Kepler.Text.TameSpine.SFlagListSpine
  rw [finalDartList_eq_finalDartListSpine L N, hs]
  unfold contourList Kepler.Text.TameSpine.ContourListSpine oneStepList
    Kepler.Text.TameSpine.oneStepListSpine
  simp only [getElem!_eq_getD]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · intro u hu v hv
      obtain ⟨s, hcs, hne, hhd, hlst, hsub⟩ := h1 u v hu hv
      exact ⟨s, hcs, hne, by rw [head!_eq_headD_of_ne hne (0, 0)]; exact hhd,
        by rw [getLast!_eq_getLastD]; exact hlst, fun z hz => hsub hz⟩
    · intro r' p y hy hp hrN hnf hasn
      rw [← parts_eq_partsSpine L r'] at hp
      exact h2 r' p y (hy.trans (getLast!_eq_getLastD p)) hp hrN hnf hasn
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · intro u v hu hv
      obtain ⟨s, hcs, hne, hhd, hlst, hsub⟩ := h1 u hu v hv
      exact ⟨s, hcs, hne, (head!_eq_headD_of_ne hne (0, 0)).symm.trans hhd,
        by rw [← getLast!_eq_getLastD]; exact hlst, fun z hz => hsub z hz⟩
    · intro r' p y hy hp hrN hnf hasn
      rw [parts_eq_partsSpine L r'] at hp
      exact h2 r' p y (hy.trans (getLast!_eq_getLastD p).symm) hp hrN hnf hasn

/-! ## §E `markedList ↔ MarkedListSpineFull`（最后一块） -/

theorem markedListCore_iff_markedListSpine (L : fgraph ℕ) (hL : GoodList L)
    (N : List (List Dart)) (r : List Dart) (x : Dart) :
    ((hypermapOfList L hL).IsRestricted ∧ normalList L hL N ∧ r ∈ N ∧ x ∈ r ∧
      (let qs := quotientList L N
       (∀ s ∈ qs, s.Nodup) ∧ ∀ v ∈ qs.flatten,
         1 < (qs.filter (fun q => decide (v ∈ q))).length) ∧
      nextEl r x = fList L x ∧ finalList L (findList N (eList x)))
      ↔ Kepler.Text.TameSpine.MarkedListSpine hL N r x := by
  have hFin : finalList L (findList N (eList x))
      ↔ Kepler.Text.TameSpine.finalListSpine L
          (Kepler.Text.TameSpine.findListSpine N (eList x)) := by
    rw [findList_eq_findListSpine N (eList x)]
    exact finalList_iff_finalListSpine L (Kepler.Text.TameSpine.findListSpine N (eList x))
  unfold Kepler.Text.TameSpine.MarkedListSpine normalList
    Kepler.Text.TameSpine.NormalListSpine fLast Kepler.Text.TameSpine.fLastSpine
    loopList Kepler.Text.TameSpine.loopListSpine oneStepList
    Kepler.Text.TameSpine.oneStepListSpine
  simp only [getLast!_eq_getLastD]
  rw [quotientList_eq_quotientListSpine L N, hFin]

theorem markedList_iff_markedListSpineFull (L : fgraph ℕ) (hL : GoodList L)
    (N : List (List Dart)) (r : List Dart) (x : Dart)
    (hs : sList L r x = Kepler.Text.TameSpine.sListSpine L r x) :
    markedList L hL N r x ↔ Kepler.Text.TameSpine.MarkedListSpineFull hL N r x := by
  unfold markedList Kepler.Text.TameSpine.MarkedListSpineFull
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    have h7' : finalList L (findList N (eList x)) := h7
    refine ⟨(markedListCore_iff_markedListSpine L hL N r x).mp
      ⟨h1, h2, h3, h4, h5, h6, h7'⟩, ?_, ?_⟩
    · intro hf
      exact (flagList_iff_flagListSpine L N).mp
        (h8 ((finalList_iff_finalListSpine L r).mpr hf))
    · intro hf
      exact (sFlagList_iff_sFlagListSpine L N r x hs).mp
        (h9 (fun hc => hf ((finalList_iff_finalListSpine L r).mp hc)))
  · intro h
    obtain ⟨hc, h8, h9⟩ := h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      (markedListCore_iff_markedListSpine L hL N r x).mpr hc
    refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
    · intro hf
      exact (flagList_iff_flagListSpine L N).mpr
        (h8 ((finalList_iff_finalListSpine L r).mp hf))
    · intro hf
      exact (sFlagList_iff_sFlagListSpine L N r x hs).mpr
        (h9 (fun hc' => hf ((finalList_iff_finalListSpine L r).mpr hc')))

end Kepler.Text.ChainBridge

-- 探针
#print axioms Kepler.Text.ChainBridge.partitionIntoAtom0_eq
#print axioms Kepler.Text.ChainBridge.parts_eq_partsSpine
#print axioms Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine
#print axioms Kepler.Text.ChainBridge.flagList_iff_flagListSpine
#print axioms Kepler.Text.ChainBridge.sFlagList_iff_sFlagListSpine
#print axioms Kepler.Text.ChainBridge.markedListCore_iff_markedListSpine
#print axioms Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull
