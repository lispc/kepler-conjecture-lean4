/-
  Kepler.Text.Reduction1W2n — J4 Wave W2-4 末件：`UYOUIXG`（HOL
  reduction1.hl:2402-2409，W2 第二验收点）槽版 + `face_iota` 的 InjOn 导出形。

  陈述折算（HOL → Lean）：
  · `MEM f (list_of_faces L)` ↦ `f ∈ Kepler.Text.TameSpine.listOfFaces L`
    （TameList31:100 载体 `listOfFaces L = L.map listPairs`；f 是 dart 表
    `List (ℕ × ℕ)`，经 `faceRep` 折到顶点面 `f0 ∈ L`，`f.map FST = f0`——
    折算对账结论：是 `L.map listPairs` 形，不是 `f ∈ L`）；
  · `iso_list (L,[f;r]) (L',N')` ↦ `IsoListSpine L L' [f, r] N'`（∃φ 形）；
  · `normal_list L' N'` ↦ `normalList L' hL' N'`——Lean 载体持 GoodList 证人参，
    以 `∃ hL' : GoodList L'` 显式入结论（Prop 层 proof irrelevance，零收窄，
    下游零成本换证）；
  · `match_quotient_list (Seed (sizel f - 3))` ↦
    `matchQuotientList (Kepler.Graphs.Seed (f.length - 3))`（`sizel` ↦ `.length`，
    `maxGon p = p + 3`）。

  槽版记档（W2j hOb 槽同例，待消）：`hAuq` = HOL `AUQTZYZ_list`
  （AUQTZYZ_list.hl:19-24，329 行独件）结论的 Spine 形：
  `∃ r, NormalListSpine hL [f, r] ∧ Dih2kListSpine (quotientListSpine L [f, r])`。
  该件尚未落库（TameList60/61 仅落 AUQTZYZ.hl :23-:572 atom/loop 前段，
  主定理 :1859-:2624 的 765 行压尾未落，故 AUQTZYZ_list 无证可引）。
  AUQTZYZ_list 落库后一行消槽：
  `hAuq := auqtzyzListSpine hL hgn hres hall hf`（其 ANTS 恰为本件前四前提 + hf）。
  witness 机制：L' := MAP (MAP phi) L（phi 由 face_iota 供，f0 = MAP FST f 的
  idxOf 重编号）；r 取槽 r；两子句 = ①Seed 终面 dart 表 =
  `listPairs (range (maxGon (f.length-3))) = f.map phi-lift`（finalFaceSeed +
  face_iota + la7_listPairs_map）经 iso_list_final_list 运输（cons-3 实例：
  N := [f; r]，头槽再挂一个 f，`f ∈ [f; r]` 头位成立）进 N' 的 final filter；
  ②fgraph (Seed p) = quotient_list L' N'：dih2k 槽给 quotient = [w; rev w] 形 +
  final_list_core 给 w = MAP FST f = f0 + face_iota 给 f0.map phi = iota 0
  (sizel f0)，maxGon p = p + 3 对齐。
  `good_list_nodes L'`/`is_restricted (hypermap_of_list L')` 在 HOL 证体内
  为死码（SUBGOAL_THEN ASSUME 后零消费），故 `hgn` 仅入陈述保逐字、证明体
  不消费；`iso_list_good_list_nodes`/`iso_list_restricted` 不需要。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W2l
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList8
import Kepler.Text.TameSpine.TameList21
import Kepler.Text.TameSpine.TameList25
import Kepler.Text.TameSpine.TameList31
import Kepler.Text.TameSpine.TameList34
import Kepler.Text.TameSpine.TameList41
import Kepler.Text.TameSpine.TameList43
import Kepler.Text.TameSpine.TameList47
import Kepler.Text.TameSpine.TameList56
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.Reduction3DefsLayer
import Kepler.Text.ChainListsL1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts listPairs)
open Kepler.Text.ChainLists (normalList)
open Kepler.Text.Reduction3 (matchQuotientList fgraphOfGraph)
open Kepler.Text.Reduction5 (quotientList finalList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Text.TameSpine (IsopListSpine IsoListSpine NormalListSpine
  Dih2kListSpine quotientListSpine coreSpine finalListSpine listOfFaces)

/-! ## §1 `face_iota` 的 InjOn 导出形 -/

/-- **HOL `face_iota` 导出形**（reduction1.hl:2345 的重打包；冻结表槽 2）：
`faceIota`（Reduction1W2l）把 `InjOn phi (elements_of_list L)` 包在
`IsopListSpine` 首合取内，本件把该槽提到顶层，并把 L' 槽折成 mapped 形
（`L' = L.map (List.map phi)` 逐字，下游 iso 证人 `⟨phi, hinj, rfl, rfl⟩`
免拆包直取）。`iota 0 n` ↦ `List.range' 0 n`。 -/
theorem faceIotaInjOn {L : Kepler.Graphs.fgraph ℕ} {f0 : List ℕ}
    (hall : ∀ l ∈ L, l.Nodup) (hf0 : f0 ∈ L) :
    ∃ phi : ℕ → ℕ,
      Set.InjOn phi (Kepler.Text.TameLp.elementsOfList L) ∧
      IsopListSpine phi L (L.map (List.map phi)) [] [] ∧
      f0.map phi = List.range' 0 f0.length := by
  obtain ⟨phi, L', hisop, hmap⟩ := faceIota hall hf0
  exact ⟨phi, hisop.1, ⟨hisop.1, rfl, hisop.2.2⟩, hmap⟩

/-! ## §2 `UYOUIXG`（槽版） -/

/-- **HOL `UYOUIXG`**（reduction1.hl:2402-2409）槽版：
`is_restricted (hypermap_of_list L) ∧ all uniq L ∧ good_list L ∧
good_list_nodes L ∧ MEM f (list_of_faces L)`（+ AUQTZYZ_list 结论槽）
`⇒ ∃ L' N' r. iso_list (L,[f;r]) (L',N') ∧ normal_list L' N' ∧
match_quotient_list (Seed (sizel f - 3)) L' N'`。 -/
theorem uyouixgOfAuqtzyzList {L : Kepler.Graphs.fgraph ℕ} {f : List (ℕ × ℕ)}
    (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted)
    (hall : ∀ l ∈ L, l.Nodup)
    (hgn : GoodListNodesTl L hL)
    (hf : f ∈ listOfFaces L)
    (hAuq : ∃ r : List (ℕ × ℕ),
      NormalListSpine hL [f, r] ∧ Dih2kListSpine (quotientListSpine L [f, r])) :
    ∃ L' : Kepler.Graphs.fgraph ℕ, ∃ N' : List (List (ℕ × ℕ)), ∃ r : List (ℕ × ℕ),
      ∃ hL' : GoodList L',
        IsoListSpine L L' [f, r] N' ∧ normalList L' hL' N' ∧
          matchQuotientList (Kepler.Graphs.Seed (f.length - 3)) L' N' := by
  obtain ⟨r, hnlS, hdih⟩ := hAuq
  -- face_rep：f = list_pairs f0，f0 ∈ L，f.map Prod.fst = f0
  obtain ⟨f0, hlp, hf0, hmfst⟩ := Kepler.Text.TameSpine.faceRep L f hf
  have hlen : f0.length = f.length := by rw [← hmfst, List.length_map]
  -- face_iota：phi = f0 内 idxOf 重编号，f0.map phi = iota 0 (sizel f0)
  obtain ⟨phi, hinj, -, hiota⟩ := faceIotaInjOn hall hf0
  have h3 : 3 ≤ f.length := Kepler.Text.TameSpine.isRestrictedSizeFace L hL hres hf
  have hend := hres.edgeNondegenerate
  have hL'g : GoodList (L.map (List.map phi)) :=
    Kepler.Text.TameSpine.mapGoodList_injOn hinj hL
  -- final 面两前置（子句 ①② 共用）：
  -- final_list L f（HOL final_list_face 面，经 memFaceLemma 换 findFace 载体）
  obtain ⟨d, hdD, hfd⟩ := Kepler.Text.TameSpine.memFaceLemma L hL hf
  have hfinF : finalListSpine L f :=
    Kepler.Text.TameSpine.finalListFace hL (List.mem_map.mpr ⟨d, hdD, hfd.symm⟩)
  have hfNodup : f.Nodup := by
    rw [hfd]; exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 d
  have hdartsF : ∀ x ∈ f, x ∈ listOfDarts L := fun x hx =>
    Kepler.Text.TameSpine.normalListListOfDarts hnlS x
      (List.mem_flatten.mpr ⟨f, List.mem_cons.mpr (Or.inl rfl), hx⟩)
  -- iso_list_final_list 运输（cons-3 实例：N := [f; r]，头槽再挂 f，
  -- MEM f [f;r] 头位成立）
  have hfinF' : finalListSpine (L.map (List.map phi))
      (f.map (fun u => (phi u.1, phi u.2))) :=
    Kepler.Text.TameSpine.isoListFinalListSpine
      (N := [f, r]) (N' := [f, r].map (fun s => s.map (fun u => (phi u.1, phi u.2))))
      (r := f) (r' := f.map (fun u => (phi u.1, phi u.2)))
      ⟨phi, hinj, rfl, rfl⟩ hnlS (List.mem_cons.mpr (Or.inl rfl)) hfinF
  refine ⟨L.map (List.map phi),
    [f, r].map (fun s => s.map (fun u => (phi u.1, phi u.2))), r, hL'g,
    ⟨phi, hinj, rfl, rfl⟩, ?_, ?_⟩
  · -- normal_list L' N'：normal_list L [f;r]（槽）沿 iso_list_normal 运输
    exact (Kepler.Text.ChainBridge.normalList_iff_normalListSpine _ _ _).mpr
      (Kepler.Text.TameSpine.isoListNormal ⟨phi, hinj, rfl, rfl⟩ hnlS)
  · unfold matchQuotientList
    refine ⟨?_, ?_⟩
    · -- 子句 ①：Seed 终面 dart 表 ∈ N'.filter final
      intro dl hdl
      rw [finalFaceSeed] at hdl
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hdl
      subst hdl
      have hmg : Kepler.Graphs.maxGon (f.length - 3) = f0.length := by
        unfold Kepler.Graphs.maxGon; omega
      have hEq : listPairs (List.range (Kepler.Graphs.maxGon (f.length - 3))) =
          f.map (fun u => (phi u.1, phi u.2)) := by
        rw [hmg, List.range_eq_range', ← hiota,
          Kepler.Text.TameLp.la7_listPairs_map, hlp]
        rfl
      rw [hEq]
      refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨f,
        List.mem_cons.mpr (Or.inl rfl), rfl⟩, ?_⟩
      exact decide_eq_true
        ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine _ _).mpr hfinF')
    · -- 子句 ②：fgraph (Seed p) = quotient_list L' N'
      obtain ⟨w, hwn, hwe⟩ := hdih
      have h2el : quotientListSpine L [f, r] = [coreSpine L f, coreSpine L r] := by
        rw [Kepler.Text.TameSpine.quotientListCore, List.map_cons, List.map_cons,
          List.map_nil]
      rw [hwe] at h2el
      injection h2el with hw _
      subst hw
      have hcoreF : coreSpine L f = f0 := by
        rw [Kepler.Text.TameSpine.finalListCore hL hdartsF hend hfNodup hfinF]
        exact hmfst
      have hisoQ := Kepler.Text.TameSpine.isopListQuotientSpine L hL hnlS hend hall
        phi ⟨hinj, rfl, rfl⟩
      show Kepler.Text.Reduction3.fgraphOfGraph (Kepler.Graphs.Seed (f.length - 3)) =
        quotientList (L.map (List.map phi))
          ([f, r].map (fun s => s.map (fun u => (phi u.1, phi u.2))))
      rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine, hisoQ.2.1, hwe]
      have hfg : Kepler.Text.Reduction3.fgraphOfGraph
          (Kepler.Graphs.Seed (f.length - 3)) =
          [List.range (Kepler.Graphs.maxGon (f.length - 3)),
            (List.range (Kepler.Graphs.maxGon (f.length - 3))).reverse] :=
        Kepler.Text.TameSpine.fgraphSeed (f.length - 3)
      rw [hfg]
      have hmg : Kepler.Graphs.maxGon (f.length - 3) = f0.length := by
        unfold Kepler.Graphs.maxGon; omega
      rw [hmg, List.range_eq_range', ← hiota, hcoreF]
      simp [List.map_reverse]

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.faceIotaInjOn
#print axioms Kepler.Text.Reduction1.uyouixgOfAuqtzyzList
