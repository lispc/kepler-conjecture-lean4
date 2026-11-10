/-
  Kepler.Text.Reduction1Mee2 — J4 W4 后波收口：`MEEIXJO` 主定理（HOL
  MEEIXJO.hl:325-:604，284 行）装配 + `hMee` 全称形 + 主定理积分件消槽演示。

  本文件三件：
  · `meEixjo` —— HOL `MEEIXJO`（MEEIXJO.hl:325-:604）：`marked_list` 沿
    `iso_list` 的九合取运输。九叶件（`Reduction1Mee.lean`，前一波已落）逐条
    消费；消费树见 DELIVERY_W4G §3.1 / 本文件 DELIVERY_MEE2 §2。
  · `meEixjoForall` —— `hMee` 全称形（= W4f/W4g 积分件的 `hMee` 槽逐字；
    纯 λ 包装，供消槽）。
  · `restrictedHypermapsArePlanegraphsReduction1OfAuq` —— 消槽演示：
    `restrictedHypermapsArePlanegraphsReduction1OfAuqMee`（W4g）的 `hMee` 槽
    由 `meEixjoForall` 代入，主定理无条件形差额只剩 `hAuq`（AUQTZYZ_list）。

  陈述对账：`meEixjo` 逐字对 HOL :326-:330（四前提、保原序）；主语境的 `good_list L`
  为载体证人参（HOL 在同位），`marked_list L' ...` 的 `good_list L'` 为 Lean 载体
  证人参（HOL 无此前提；由 iso 首支 + `iso_list_good_list` 可导出，Prop 证明无关；
  同 `iso_list_loop_choice` 处理）。**零省前提**。

  载体：chain 形（`markedList`/`flagList`/`sFlagList`/`parts`/`sList`/`findList`；
  `Dart := ℕ × ℕ`）；Spine 只在证体内经 ChainBridge 两形桥出现。轮廓件
  `injOnContourCondition2` 的结论是 Spine 形，chain `flagList` 首合取用
  `contourList_iff_contourListSpine` 的 `.mpr` 反用一次（交付 §3 记档）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1Mee
import Kepler.Text.Reduction1W4g
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.TameSpine.TameList4
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList7
import Kepler.Text.TameSpine.TameList8
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList36
import Kepler.Text.TameSpine.TameList40
import Kepler.Text.TameSpine.TameList41
import Kepler.Text.TameSpine.TameList42
import Kepler.Text.TameSpine.TameList43
import Kepler.Text.TameSpine.TameList44

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts listPairs eList fList nextEl)
open Kepler.Graphs (fgraph)
open Kepler.Text.ChainLists (normalList markedList flagList sFlagList sList
  contourList finalDartList findList)
open Kepler.Text.Reduction5 (Dart quotientList finalList parts)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl nextEl_mem_of_mem)
open Kepler.Text.TameSpine (NormalListSpine ContourListSpine)

/-! ## §0 私件：`getLastD` 沿 map -/

/-- `(s.map f).getLastD (0,0) = f (s.getLastD (0,0))`（`s ≠ []`）。 -/
private theorem getLastDMapAux {α β : Type} (f : α → β) (dα : α) (dβ : β)
    {s : List α} (hs : s ≠ []) : (s.map f).getLastD dβ = f (s.getLastD dα) := by
  rw [List.getLastD_eq_getLast?, List.getLast?_map, List.getLastD_eq_getLast?]
  cases hlast : s.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hlast) hs
  | some w => rfl

/-! ## §1 `MEEIXJO` 主定理（MEEIXJO.hl:325-:604） -/

/-- **HOL `MEEIXJO`**（MEEIXJO.hl:325-:604）：
`good_list L /\ good_list_nodes L /\ iso_list (L,([x]::r::N)) (L',([x']::r'::N')) /\
marked_list L N r x ==> marked_list L' N' r' x'`。
九合取逐条：①`iso_list_restricted` ②`iso_list_normal` ③`iso_list_mem_rN`
④`iso_list_mem_xr` ⑤`iso_list_quotient`+`iso_list_all_uniq`(LYNVPSU) +
`iso_list_all_size` ⑥`f_list_map`+`next_el_MEM_map`+marked_list ⑥
⑦`marked_list_x_last`+`e_list_last`+`find_list_map`+`iso_list_final_list_eq`+
`marked_final_list_ex` ⑧`inj_on_contour_condition2`+`iso_list_parts`+
`iso_list_final_dart_list` ⑨同上 +`inj_on_s_list`。 -/
theorem meEixjo {L L' : fgraph ℕ} {N N' : List (List Dart)} {r r' : List Dart}
    {x x' : Dart} (hL : GoodList L) (hL' : GoodList L')
    (hgn : GoodListNodesTl L hL)
    (hiso : Kepler.Text.TameSpine.IsoListSpine L L' ([x] :: r :: N) ([x'] :: r' :: N'))
    (hm : markedList L hL N r x) :
    markedList L' hL' N' r' x' := by
  -- 拆 iso 的 cons 形：x' = lift x、r' = map lift r、N' = map lift N
  have hisoKeep : Kepler.Text.TameSpine.IsoListSpine L L' ([x] :: r :: N) ([x'] :: r' :: N') :=
    hiso
  obtain ⟨phi, hinj, hLmap, hNmap⟩ := hiso
  have hN' : [x'] :: r' :: N' =
      [(phi x.1, phi x.2)] :: (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) ::
        (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) := by
    rw [hNmap]
    simp only [List.map_cons, List.map_nil]
  obtain ⟨hx1, h2⟩ := List.cons.inj hN'
  obtain ⟨hr1, hN1⟩ := List.cons.inj h2
  have hx' : x' = (phi x.1, phi x.2) := (List.cons.inj hx1).1
  have hr' : r' = r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) := hr1
  subst hx'
  subst hr'
  subst hN1
  subst hLmap
  -- 基础事实
  have hres : (hypermapOfList L hL).IsRestricted := hm.1
  have hend : (hypermapOfList L hL).EdgeNondegenerate := hres.edgeNondegenerate
  have hnl : normalList L hL N := hm.2.1
  have hnlS : NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  have hall : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.simpleHypermapAllUniq L hL hgn hres.simple
  have hxr : x ∈ r := hm.2.2.2.1
  have hrN : r ∈ N := hm.2.2.1
  have hrd : ∀ y ∈ r, y ∈ listOfDarts L := fun y hy =>
    Kepler.Text.TameSpine.normalListListOfDarts hnlS y (List.mem_flatten.mpr ⟨r, hrN, hy⟩)
  have hrinj : ∀ u ∈ r, ∀ w ∈ r,
      (phi u.1, phi u.2) = (phi w.1, phi w.2) → u = w :=
    fun u hu w hw h =>
      Kepler.Text.TameSpine.injOnLiftListOfDarts L hinj (hrd u hu) (hrd w hw) h
  have hlinj : ∀ u ∈ N.flatten, ∀ w ∈ N.flatten,
      (phi u.1, phi u.2) = (phi w.1, phi w.2) → u = w := by
    intro u hu w hw h
    exact Kepler.Text.TameSpine.injOnLiftListOfDarts L hinj
      (Kepler.Text.TameSpine.normalListListOfDarts hnlS u hu)
      (Kepler.Text.TameSpine.normalListListOfDarts hnlS w hw) h
  -- ① is_restricted L'
  have hiso0 : Kepler.Text.TameSpine.IsoListSpine L (L.map (List.map phi)) [] [] :=
    Kepler.Text.TameSpine.isoListNilFamily hisoKeep
  have hres' : (hypermapOfList (L.map (List.map phi)) hL').IsRestricted :=
    Kepler.Text.TameSpine.isoListRestricted hL'
      (Kepler.Text.TameSpine.isoListSpineSymNil hL hiso0) hres
  -- ② normal_list L' N'
  have hisoN : Kepler.Text.TameSpine.IsoListSpine L (L.map (List.map phi)) N
      (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) :=
    ⟨phi, hinj, rfl, rfl⟩
  have hnlS' : NormalListSpine hL'
      (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) :=
    Kepler.Text.TameSpine.isoListNormal hisoN hnlS
  have hnl' : normalList (L.map (List.map phi)) hL'
      (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine _ hL' _).mpr hnlS'
  -- ③ r' ∈ N'、④ x' ∈ r'
  have hrN' : r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) ∈
      N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) :=
    Kepler.Text.TameSpine.isoListMemRN hL' hrN hisoKeep
  have hxr' : (phi x.1, phi x.2) ∈ r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) :=
    Kepler.Text.TameSpine.isoListMemXR hL' hxr hisoKeep
  -- ⑤ quotient 两槽
  have hqiso : Kepler.Text.TameSpine.IsoListSpine
      (Kepler.Text.TameSpine.quotientListSpine L N)
      (Kepler.Text.TameSpine.quotientListSpine (L.map (List.map phi))
        (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))) [] [] :=
    Kepler.Text.TameSpine.isoListQuotientSpine L hL hnlS hend hall hisoN
  have hq5a : ∀ s ∈ quotientList (L.map (List.map phi))
      (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))), s.Nodup := by
    intro s hs
    rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine] at hs
    refine Kepler.Text.TameSpine.isoListSpineAllUniq hqiso ?_ s hs
    intro t ht
    rw [← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine] at ht
    exact hm.2.2.2.2.1.1 t ht
  have hq5b : ∀ v ∈ (quotientList (L.map (List.map phi))
        (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))).flatten,
      1 < ((quotientList (L.map (List.map phi))
        (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))).filter
        (fun r => decide (v ∈ r))).length := by
    intro v hv
    have hpre : ∀ w ∈ (Kepler.Text.TameSpine.quotientListSpine L N).flatten,
        1 < ((Kepler.Text.TameSpine.quotientListSpine L N).filter
          (fun s => decide (w ∈ s))).length := by
      intro w hw
      rw [← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine] at hw ⊢
      exact hm.2.2.2.2.1.2 w hw
    have hsp := Kepler.Text.TameSpine.isoListAllSizeSpine hqiso hpre v (by
      rw [← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
      exact hv)
    rwa [← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine] at hsp
  -- ⑥ next_el 运输
  have h6 : nextEl (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) (phi x.1, phi x.2)
      = fList (L.map (List.map phi)) (phi x.1, phi x.2) := by
    rw [Kepler.Text.TameLp.la7_nextEl_map
        (f := fun u : ℕ × ℕ => (phi u.1, phi u.2)) (l := r) hrinj hxr,
      Kepler.Text.TameSpine.fListMap (hL := hL) hinj (hrd x hxr),
      hm.2.2.2.2.2.1]
  -- ⑦ final_list (find_list N' (e_list x'))
  have hcore : Kepler.Text.TameSpine.MarkedListSpine hL N r x :=
    (Kepler.Text.ChainBridge.markedListCore_iff_markedListSpine L hL N r x).mp
      ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.1⟩
  obtain ⟨p, hpS, hlastp⟩ := Kepler.Text.TameSpine.markListXLast hL hcore hend
  have hp : p ∈ parts L r := by
    rw [Kepler.Text.ChainBridge.parts_eq_partsSpine]
    exact hpS
  have hxE : eList x ∈ N.flatten := by
    have h := eListLast hL hnl hrN hall hend hp
    rwa [hlastp] at h
  have hfind : findList (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))
      (eList (phi x.1, phi x.2))
      = (findList N (eList x)).map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) := by
    have hel : eList (phi x.1, phi x.2) = (phi (eList x).1, phi (eList x).2) := rfl
    rw [hel, Kepler.Text.ChainBridge.findList_eq_findListSpine,
      Kepler.Text.ChainBridge.findList_eq_findListSpine]
    exact Kepler.Text.TameSpine.findListMapSpine
      (f := fun u : ℕ × ℕ => (phi u.1, phi u.2)) hnlS.1 hxE hlinj
  have h7 : finalList (L.map (List.map phi))
      (findList (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))
        (eList (phi x.1, phi x.2))) := by
    rw [hfind]
    have hrNfind : findList N (eList x) ∈ N := by
      rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
      exact Kepler.Text.TameSpine.findListSpineMemN hxE
    have hiff := Kepler.Text.TameSpine.isoListFinalListEqSpine
      (hiso := (⟨phi, hinj, rfl, rfl⟩ : Kepler.Text.TameSpine.IsoListSpine L
        (L.map (List.map phi)) (findList N (eList x) :: N)
        ((findList N (eList x) :: N).map
          (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))))
      hnlS hrNfind
    exact hiff.mpr (markedFinalListEx hm)
  -- 轮廓存在块（L' 侧，Spine 形）
  have hcont' : ∀ u v, u ∈ finalDartList (L.map (List.map phi))
        (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) →
      v ∈ finalDartList (L.map (List.map phi))
        (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) →
      ∃ s : List Dart, ContourListSpine (L.map (List.map phi)) s ∧ s ≠ [] ∧
        s.headD (0, 0) = u ∧ s.getLastD (0, 0) = v ∧
        {w : Dart | w ∈ s} ⊆
          {w : Dart | w ∈ finalDartList (L.map (List.map phi))
            (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))} :=
    injOnContourCondition2 hL hnlS hisoN hm
  -- ⑧ final_list L' r' → flag_list L' N'
  have h8 : finalList (L.map (List.map phi))
      (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) →
      flagList (L.map (List.map phi))
        (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) := by
    intro hfinL'
    -- final_list L r（回运）
    have hrNfin : findList N (eList x) ∈ N := by
      rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
      exact Kepler.Text.TameSpine.findListSpineMemN hxE
    have hiffr := Kepler.Text.TameSpine.isoListFinalListEqSpine
      (hiso := (⟨phi, hinj, rfl, rfl⟩ : Kepler.Text.TameSpine.IsoListSpine L
        (L.map (List.map phi)) (r :: N)
        ((r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) ::
          (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))))))
      hnlS hrN
    have hfinL : finalList L r := hiffr.mp hfinL'
    have hflagL : flagList L N := hm.2.2.2.2.2.2.2.1 hfinL
    refine ⟨?_, ?_⟩
    · -- 首合取：Spine → chain
      intro u v hu hv
      obtain ⟨s, hcs, hsne, hhd, hlst, hsub⟩ := hcont' u v hu hv
      exact ⟨s, (Kepler.Text.ChainBridge.contourList_iff_contourListSpine
        (L.map (List.map phi)) s).mpr hcs, hsne, hhd, hlst, hsub⟩
    · -- 尾合取：非终面 r''' 的 parts 末端 e_list ∈ 终面 dart 表
      intro x'' p y hy hp hrN'' hnf''
      obtain ⟨x0, hx0N, rfl⟩ := List.mem_map.mp hrN''
      -- p = x0' .map lift
      have hpS' : p ∈ Kepler.Text.TameSpine.partsSpine (L.map (List.map phi))
          (x0.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) := by
        rw [← Kepler.Text.ChainBridge.parts_eq_partsSpine]
        exact hp
      have hfl0 : (Kepler.Text.TameSpine.partsSpine L x0).flatten = x0 := by
        rw [← Kepler.Text.ChainBridge.parts_eq_partsSpine]
        exact Kepler.Text.MoreLemma2Island2.partsFlatten L
          (Kepler.Text.TameSpine.normalListUniqNonnil hnlS hx0N).1
          (Kepler.Text.TameSpine.normalListUniqNonnil hnlS hx0N).2
      have hall0 : ∀ x ∈ x0, x ∈ listOfDarts L := fun x hxx =>
        Kepler.Text.TameSpine.normalListListOfDarts hnlS x
          (List.mem_flatten.mpr ⟨x0, hx0N, hxx⟩)
      have hparts0 := Kepler.Text.TameSpine.isoListParts L hL hnlS hend phi hinj
        hx0N hfl0 hall0
      obtain ⟨x0', hx0', rfl⟩ := List.mem_map.mp (hparts0 ▸ hpS')
      -- 非终面回运
      have hiff0 := Kepler.Text.TameSpine.isoListFinalListEqSpine
        (hiso := (⟨phi, hinj, rfl, rfl⟩ : Kepler.Text.TameSpine.IsoListSpine L
          (L.map (List.map phi)) (x0 :: N)
          ((x0 :: N).map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))))
        hnlS hx0N
      have hnf0 : ¬ finalList L x0 := fun hc => hnf'' (hiff0.mpr hc)
      -- p 非空、y = lift y0
      have hx0c : x0' ∈ parts L x0 := by
        rw [Kepler.Text.ChainBridge.parts_eq_partsSpine]
        exact hx0'
      obtain ⟨-, -, -, hpne, -⟩ := Kepler.Text.MoreLemma2Island3.partsUniqNonnil
        L hL hnl hx0N hx0c
      have hy0 : y = (phi (x0'.getLastD (0, 0)).1, phi (x0'.getLastD (0, 0)).2) := by
        rw [hy]
        exact getLastDMapAux (fun u : ℕ × ℕ => (phi u.1, phi u.2)) (0, 0) (0, 0) hpne
      rw [hy0]
      -- marked_list 第 8 合取在 (x0, x0', y0)
      have hmem : eList (x0'.getLastD (0, 0)) ∈ finalDartList L N :=
        hflagL.2 x0 x0' (x0'.getLastD (0, 0)) rfl hx0c hx0N hnf0
      have hfd : finalDartList (L.map (List.map phi))
          (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) =
          (finalDartList L N).map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) :=
        isoListFinalDartList hL hnlS ⟨hinj, rfl, rfl⟩
      rw [hfd]
      exact Kepler.Text.TameSpine.memfMap hmem
  -- ⑨ ¬final_list L' r' → s_flag_list L' N' r' x'
  have h9 : ¬ finalList (L.map (List.map phi))
      (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) →
      sFlagList (L.map (List.map phi))
        (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))
        (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) (phi x.1, phi x.2) := by
    intro hnfL'
    have hiffr := Kepler.Text.TameSpine.isoListFinalListEqSpine
      (hiso := (⟨phi, hinj, rfl, rfl⟩ : Kepler.Text.TameSpine.IsoListSpine L
        (L.map (List.map phi)) (r :: N)
        ((r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) ::
          (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))))))
      hnlS hrN
    have hnfL : ¬ finalList L r := fun hc => hnfL' (hiffr.mpr hc)
    have hsflagL : sFlagList L N r x := hm.2.2.2.2.2.2.2.2 hnfL
    -- s_list 运输
    have hsList : sList (L.map (List.map phi))
        (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) (phi x.1, phi x.2)
        = (sList L r x).map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) :=
      injOnSList hL hgn hnlS hrN hxr hinj
    refine ⟨?_, ?_⟩
    · intro u v hu hv
      obtain ⟨s, hcs, hsne, hhd, hlst, hsub⟩ := hcont' u v hu hv
      exact ⟨s, (Kepler.Text.ChainBridge.contourList_iff_contourListSpine
        (L.map (List.map phi)) s).mpr hcs, hsne, hhd, hlst, hsub⟩
    · intro x'' p y hy hp hrN'' hnf'' hys
      obtain ⟨x0, hx0N, rfl⟩ := List.mem_map.mp hrN''
      have hpS' : p ∈ Kepler.Text.TameSpine.partsSpine (L.map (List.map phi))
          (x0.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) := by
        rw [← Kepler.Text.ChainBridge.parts_eq_partsSpine]
        exact hp
      have hfl0 : (Kepler.Text.TameSpine.partsSpine L x0).flatten = x0 := by
        rw [← Kepler.Text.ChainBridge.parts_eq_partsSpine]
        exact Kepler.Text.MoreLemma2Island2.partsFlatten L
          (Kepler.Text.TameSpine.normalListUniqNonnil hnlS hx0N).1
          (Kepler.Text.TameSpine.normalListUniqNonnil hnlS hx0N).2
      have hall0 : ∀ x ∈ x0, x ∈ listOfDarts L := fun x hxx =>
        Kepler.Text.TameSpine.normalListListOfDarts hnlS x
          (List.mem_flatten.mpr ⟨x0, hx0N, hxx⟩)
      have hparts0 := Kepler.Text.TameSpine.isoListParts L hL hnlS hend phi hinj
        hx0N hfl0 hall0
      obtain ⟨x0', hx0', rfl⟩ := List.mem_map.mp (hparts0 ▸ hpS')
      have hiff0 := Kepler.Text.TameSpine.isoListFinalListEqSpine
        (hiso := (⟨phi, hinj, rfl, rfl⟩ : Kepler.Text.TameSpine.IsoListSpine L
          (L.map (List.map phi)) (x0 :: N)
          ((x0 :: N).map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))))
        hnlS hx0N
      have hnf0 : ¬ finalList L x0 := fun hc => hnf'' (hiff0.mpr hc)
      have hx0c : x0' ∈ parts L x0 := by
        rw [Kepler.Text.ChainBridge.parts_eq_partsSpine]
        exact hx0'
      obtain ⟨-, -, -, hpne, -⟩ := Kepler.Text.MoreLemma2Island3.partsUniqNonnil
        L hL hnl hx0N hx0c
      have hy0 : y = (phi (x0'.getLastD (0, 0)).1, phi (x0'.getLastD (0, 0)).2) := by
        rw [hy]
        exact getLastDMapAux (fun u : ℕ × ℕ => (phi u.1, phi u.2)) (0, 0) (0, 0) hpne
      -- y0 ∉ s_list L r x（经 s_list 运输反证）
      have hy0not : x0'.getLastD (0, 0) ∉ sList L r x := by
        intro hc
        apply hys
        rw [hy0, hsList]
        exact Kepler.Text.TameSpine.memfMap hc
      rw [hy0]
      -- marked_list 第 9 合取在 (x0, x0', y0)
      have hmem : eList (x0'.getLastD (0, 0)) ∈ sList L r x ++ finalDartList L N :=
        hsflagL.2 x0 x0' (x0'.getLastD (0, 0)) rfl hx0c hx0N hnf0 hy0not
      rw [hsList, isoListFinalDartList hL hnlS ⟨hinj, rfl, rfl⟩, ← List.map_append]
      exact Kepler.Text.TameSpine.memfMap hmem
  unfold Kepler.Text.ChainLists.markedList
  exact ⟨hres', hnl', hrN', hxr', ⟨hq5a, hq5b⟩, h6, h7, h8, h9⟩

/-! ## §2 `hMee` 全称形 -/

/-- `hMee` 全称形（= W4f/W4g 积分件的 `hMee` 槽逐字；λ 包装 `meEixjo`）。 -/
theorem meEixjoForall :
    ∀ (L : fgraph ℕ) (hL : GoodList L) (N : List (List Dart)) (r : List Dart)
      (x : Dart) (L' : fgraph ℕ) (hL' : GoodList L') (N' : List (List Dart))
      (r' : List Dart) (x' : Dart),
      GoodListNodesTl L hL →
      Kepler.Text.TameSpine.IsoListSpine L L' ([x] :: r :: N) ([x'] :: r' :: N') →
      markedList L hL N r x → markedList L' hL' N' r' x' :=
  fun L hL N r x L' hL' N' r' x' hgn hiso hm => meEixjo hL hL' hgn hiso hm

/-! ## §3 消槽演示：主定理无条件形差额只剩 `hAuq` -/

/-- `restrictedHypermapsArePlanegraphsReduction1OfAuqMee`（W4g）的 `hMee` 槽
由 §2 代入后：主定理无条件形差额只剩 `hAuq`（`AuqtzyzListSlot`）。 -/
theorem restrictedHypermapsArePlanegraphsReduction1OfAuq
    (hv7 : ∀ (L : fgraph ℕ) (hL : GoodList L) (N N' : List (List Dart))
        (g : Kepler.Graphs.Graph) (p : ℕ) (fs : List Kepler.Graphs.Face)
        (f : Kepler.Graphs.Face) (v k : ℕ) (r : List Dart) (x : Dart),
        GoodListNodesTl L hL →
        (hypermapOfList L hL).IsRestricted →
        Kepler.Text.Reduction3.newvertexPrepped L N r x →
        markedList L hL N r x →
        ¬ finalList L r →
        Kepler.Text.Reduction3.matchQuotientList g L N →
        Kepler.Graphs.Graph.final g = false →
        Kepler.Text.TameSpine.PlaneGraphPSpine p g →
        Kepler.Text.TameCorrList.GoodFacesV3 g →
        Kepler.Text.TameCorrList.VerticesSet2Eq g →
        p = (L.map List.length).foldr max 0 - 3 →
        fs = Kepler.Graphs.nonFinals g →
        f = Kepler.Graphs.minimalFace fs →
        v = Kepler.Graphs.minimalVertex g f →
        (r, x) = Kepler.Text.Reduction3.loopChoice2 g L N →
        k = Kepler.Text.Reduction5.transformCount L N r x →
        N' = Kepler.Text.Reduction5.ntrans L N r x k →
        ∃ (g' : Kepler.Graphs.Graph) (i : ℕ),
          Kepler.Text.Reduction3.matchQuotientList g' L N' ∧ 3 ≤ i ∧
            i ≤ Kepler.Graphs.maxGon p ∧ Kepler.Text.TameCorrList.GoodFacesV3 g' ∧
            Kepler.Text.TameCorrList.VerticesSet2Eq g' ∧
            g' ∈ Kepler.Graphs.generatePolygon i v f g)
    (htav2 : ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodesTl L hL →
        Kepler.Text.Reduction5.transformAssumptionV2 L)
    (hAuq : ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodesTl L hL →
      (hypermapOfList L hL).IsRestricted → AuqtzyzListSlot L hL) :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 :=
  restrictedHypermapsArePlanegraphsReduction1OfAuqMee hv7 htav2 hAuq meEixjoForall

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.meEixjo
#print axioms Kepler.Text.Reduction1.meEixjoForall
#print axioms Kepler.Text.Reduction1.restrictedHypermapsArePlanegraphsReduction1OfAuq
