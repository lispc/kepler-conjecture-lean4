/-
  Kepler.Text.Reduction1W2h — J4 Wave W2-3 第 1 件：`match_quotient_list_map`
  （HOL reduction1.hl:2073-2153）。

  陈述（HOL 的 Prop 等式 ↦ Lean `Iff`）：
  `is_edge_nondegenerate (hypermap_of_list L) ∧ all uniq L ∧ good_list L ∧
   normal_list L N ∧ (∀ x ∈ MAP FST (flatten N), f x = x) ∧
   inj_on f (elements_of_list L) ⇒
   match_quotient_list g (MAP (MAP f) L) (MAP (MAP pairF) N) ↔
   match_quotient_list g L N`。

  证体（HOL 两子目标 chase 的 Lean 形，基座全在库）：
  · iso 证人：`IsopListSpine f L L' N N' := ⟨hinj, rfl, rfl⟩`（TameList1，
    定义与 match_quotient_list_map 的 MAP 形逐字）；
  · quotient 槽：`TameList41.isopListQuotientSpine`（显式 phi 形，phi 原位复用）
    + `TameList35.quotientListElements`（quotient 顶点 ⊆ MAP FST (flatten N)
    ⇒ `hfix` 收点）⇒ `quotientList L' N' = quotientList L N`；
  · filter 槽：`TameList43.isoListFinalListEqSpine`（cons 形 iso：⟨f, hinj, rfl, rfl⟩）
    + `TameList56.finalListSndIsFst`（final 面元的 SND 也落在 MAP FST (flatten N)
    ⇒ `pairF d = d`）⇒ `filter finalList N' = filter finalList N`；
  · `Reduction3DefsAssumptionInst.finalList_iff_finalListSpine`（两形同体）+
    `ChainBridge`（Spine/chain 桥，Thm13B 同法）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W2g
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList35
import Kepler.Text.TameSpine.TameList41
import Kepler.Text.TameSpine.TameList43
import Kepler.Text.TameSpine.TameList56
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.Reduction3DefsLayer
import Kepler.Text.ChainListsL1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList)
open Kepler.Text.ChainLists (normalList)
open Kepler.Text.Reduction3 (matchQuotientList)
open Kepler.Text.Reduction5 (quotientList finalList)
open Kepler.Text.TameLp (elementsOfList)
open Kepler.Text.TameSpine (quotientListSpine)

/-! ## `match_quotient_list_map` -/

/-- **HOL `match_quotient_list_map`**（reduction1.hl:2073）：`f` 在
`MAP FST (flatten N)` 上恒等且 `inj_on f (elements_of_list L)` 时，
`match_quotient_list` 对 `(L, N)` 的 iso 运输不变。 -/
theorem matchQuotientListMap {g : Kepler.Graphs.Graph} {L : Kepler.Graphs.fgraph ℕ}
    {N : List (List (ℕ × ℕ))} {f : ℕ → ℕ}
    (hgood : GoodList L)
    (hend : (Kepler.Text.TameLp.hypermapOfList L hgood).EdgeNondegenerate)
    (hall : ∀ l ∈ L, l.Nodup)
    (hnl : normalList L hgood N)
    (hfix : ∀ x ∈ N.flatten.map (fun d => d.1), f x = x)
    (hinj : Set.InjOn f (elementsOfList L)) :
    matchQuotientList g (L.map (List.map f))
        (N.map (fun s => s.map (fun u => (f u.1, f u.2)))) ↔
      matchQuotientList g L N := by
  have hnlS : Kepler.Text.TameSpine.NormalListSpine hgood N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hgood N).mp hnl
  -- iso 证人（IsopListSpine 三槽 = inj_on + 两个 MAP 方程，`rfl` 即得）
  have hiso : Kepler.Text.TameSpine.IsopListSpine f L (L.map (List.map f)) N
      (N.map (fun s => s.map (fun u => (f u.1, f u.2)))) := ⟨hinj, rfl, rfl⟩
  -- quotient 槽：phi 原位复用 + quotient 顶点收点 ⇒ 两商表相等
  have hEl := Kepler.Text.TameSpine.quotientListElements L hgood hnlS
  have hfixQ : ∀ face ∈ quotientListSpine L N, face.map f = face := by
    intro face hface
    have h1 : face.map f = face.map id := List.map_congr_left fun v hv => by
      have hvEl : v ∈ elementsOfList (quotientListSpine L N) :=
        Set.mem_setOf.mpr (List.mem_eraseDups.mpr
          (List.mem_flatten.mpr ⟨face, hface, hv⟩))
      rw [hEl] at hvEl
      exact hfix v (Set.mem_setOf.mp hvEl)
    rw [h1, List.map_id]
  have hQmap : (quotientListSpine L N).map (List.map f) = quotientListSpine L N := by
    have h2 : (quotientListSpine L N).map (List.map f) =
        (quotientListSpine L N).map id :=
      List.map_congr_left fun face hface => hfixQ face hface
    rw [h2, List.map_id]
  have hQ : quotientList (L.map (List.map f))
      (N.map (fun s => s.map (fun u => (f u.1, f u.2)))) = quotientList L N := by
    rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine,
      Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
    have hisoQ := Kepler.Text.TameSpine.isopListQuotientSpine L hgood hnlS hend hall f hiso
    rw [hisoQ.2.1, hQmap]
  -- filter 槽：final 判定的 iso 运输 + final 面元的 pairF 恒等
  have hT : ∀ s ∈ N,
      (finalList (L.map (List.map f)) (s.map (fun d => (f d.1, f d.2))) ↔
        finalList L s) := fun s hs => by
    have hS := Kepler.Text.TameSpine.isoListFinalListEqSpine
      (L := L) (L' := L.map (List.map f)) (N := N)
      (N' := N.map (fun s => s.map (fun u => (f u.1, f u.2))))
      (r := s) (r' := s.map (fun u => (f u.1, f u.2)))
      ⟨f, hinj, rfl, rfl⟩ hnlS hs
    exact (Kepler.Text.ChainBridge.finalList_iff_finalListSpine _ _).trans
      (hS.trans (Kepler.Text.ChainBridge.finalList_iff_finalListSpine _ _).symm)
  have hFid : ∀ s ∈ N.filter (fun s => decide (finalList L s)),
      s.map (fun d => (f d.1, f d.2)) = s := by
    intro s hs
    obtain ⟨hsN, hdec⟩ := List.mem_filter.mp hs
    have hfin : finalList L s := of_decide_eq_true hdec
    have h1 : s.map (fun d => (f d.1, f d.2)) = s.map id :=
      List.map_congr_left fun d hd => by
        have hd2 : d.2 ∈ N.flatten.map Prod.fst :=
          Kepler.Text.TameSpine.finalListSndIsFst L hfin hnlS hall hsN hd
        have he1 : f d.1 = d.1 := hfix d.1
          (List.mem_map.mpr ⟨d, List.mem_flatten.mpr ⟨s, hsN, hd⟩, rfl⟩)
        have he2 : f d.2 = d.2 := hfix d.2 hd2
        simp [he1, he2]
    rw [h1, List.map_id]
  have hcongr : ∀ s ∈ N,
      ((fun s' => decide (finalList (L.map (List.map f)) s')) ∘
        fun s => s.map (fun u => (f u.1, f u.2))) s =
        (fun s => decide (finalList L s)) s :=
    fun s hs => decide_eq_decide.mpr (hT s hs)
  have hF : (N.map (fun s => s.map (fun u => (f u.1, f u.2)))).filter
      (fun s' => decide (finalList (L.map (List.map f)) s')) =
      N.filter (fun s => decide (finalList L s)) := by
    rw [List.filter_map, List.filter_congr hcongr]
    have h3 : (N.filter (fun s => decide (finalList L s))).map
        (fun s => s.map (fun u => (f u.1, f u.2))) =
        (N.filter (fun s => decide (finalList L s))).map id :=
      List.map_congr_left fun s hs => hFid s hs
    rw [h3, List.map_id]
  unfold matchQuotientList
  rw [hQ, hF]

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.matchQuotientListMap
