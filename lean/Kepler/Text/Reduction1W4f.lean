/-
  Kepler.Text.Reduction1W4f — J4 Wave W4 第三波（余量）：reduction1 主定理
  `restricted_hypermaps_are_planegraphs_reduction1`（HOL reduction1.hl:4784-:4975）
  的**条件形**。

  **这是条件形，不是 HOL 主定理的无条件落点**。HOL 陈述是
  `generatePolygon_reduction_v7 /\ (!L. good_list L /\ good_list_nodes L ==>
  transform_assumption_v2 L) ==> restricted_hypermaps_are_planegraphs_v4`。
  本件在这两条 HOL 原有前提之外另带**两个槽**（故名加 `OfSlots` 后缀，
  HOL 原名留给日后的无槽形）：
  · `hne`（种子可许性）：HOL `max_finals_g_exists` 证体里用 `UYOUIXG` +
    `flag_list_seed` + 三条 `seed_*` 造种子三元组的那一段。在库的
    `maxFinalsGExists`（Reduction1W3d）已把它立为同形槽；本件把该槽对 `L`
    全称化后原样上抛，未消。
  · `hMee`（MEEIXJO）：`marked_list` 沿 `iso_list` 的运输（MEEIXJO.hl:325-:608，
    主证体 :4890 唯一消费点）。Lean 零落点，槽形 = HOL 陈述逐字
    （`good_list L /\ good_list_nodes L /\ iso_list (L,[x]::r::N)
    (L',[x']::r'::N') /\ marked_list L N r x ==> marked_list L' N' r' x'`），
    L' 侧载体证人 `hL'` 全称量化。
  早侦设想的第三槽 `hOb`（OBDATYB）本件**不需要**：`obdatybChain`
  （Reduction3ObdatybChain）已在库，证体内直接消费。

  **陈述对账**：
  · 前提一 `generatePolygon_reduction_v7`（tame_defs2.hl:732-:759）：Lean 无同名
    def，按**内联 ∀ 假设**写入（不新立 def）。十八个前提保 HOL 原序
    （`good_list L` 为载体证人参），结论六合取保原序。
  · 前提二：`transformAssumptionV2`（Reduction5Tav2）逐字。证体内确有消费
    （沿 `i` 归纳得 AQIUNPP3，供 `final_list_transform_count`/OBDATYB/
    `marked_list L (ntrans …) (rtrans …) x`），与 HOL 同。
  · 结论：`restrictedHypermapsArePlaneGraphsV4`（JcajyduShell，在库 def）。

  **证体与 HOL 的对应**（:4792-:4975 逐段）：
  `max_finals_g_exists` 取极大元 `(g, L', N')` → 若 `finalGraph g` 则
  `restricted_match_finalGraph` + `GNBEVVU` + `good_list_quotient` +
  `good_list_nodes_quotient` 收口；否则设 `(r, x) = loop_choice2 g L' N'`：
  `final_list L' r` 支由 `mem_makeFaceFinal_planeGraphP_etc` 给出 finals 更大的
  可许三元组，矛盾；非 final 支依次 `HKBGWJI` → `iso_list_newvertex_lemma`
  （`hOb` 实参 = OBDATYB）→ `iso_list_good_list_nodes` → MEEIXJO 槽 →
  `iso_list_final_list_eq` → `iso_list_loop_choice` → v7 前提 →
  `generatePolygon_mono`，而 `(g₃, L₂, ntrans …)` 的可许性由 AQIUNPP3 +
  `final_list_transform_count` + `planegraphP_trans` 供给，再次矛盾。
  HOL 在 L' 侧反复重建的 `is_restricted` 等事实，Lean 侧直接取自
  `marked_list` 的合取（同 Reduction1W4e 的处理）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W2j
import Kepler.Text.Reduction1W3d
import Kepler.Text.Reduction1W3e
import Kepler.Text.Reduction1W3f
import Kepler.Text.Reduction1W4a
import Kepler.Text.Reduction1W4c
import Kepler.Text.Reduction1W4d
import Kepler.Text.Reduction1W4e
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5J5Tav2Bridge
import Kepler.Text.Reduction5Tav2
import Kepler.Text.TameSpine.Reduction3ObdatybChain
import Kepler.Text.TameSpine.JcajyduShell
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.TameSpine.TameList1
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.TameList16
import Kepler.Text.TameSpine.TameList19
import Kepler.Text.TameSpine.TameList36
import Kepler.Text.TameSpine.TameList43
import Kepler.Text.TameSpine.TameList59

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts findFaceDarts)
open Kepler.Graphs (fgraph Graph Face finals minimalFace minimalVertex nonFinals
  next_plane generatePolygon maxGon)
open Kepler.Text.ChainLists (normalList markedList flagList)
open Kepler.Text.Reduction3 (matchQuotientList fgraphOfGraph loopChoice2
  newvertexPrepped)
open Kepler.Text.Reduction5 (Dart quotientList finalList ntrans rtrans
  transformCount transformAssumptionV2)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Text.TameSpine (NormalListSpine quotientListSpine IsoListSpine
  PlaneGraphPSpine restrictedHypermapsArePlaneGraphsV4)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq GoodListNodes)

/-- **HOL `restricted_hypermaps_are_planegraphs_reduction1`**
（reduction1.hl:4784-:4975）的**条件形**：HOL 两前提（`hv7` =
`generatePolygon_reduction_v7` 内联形、`htav2`）之外另带两槽——`hne`
（种子可许性，`max_finals_g_exists` 的在库槽对 `L` 全称化）与 `hMee`
（MEEIXJO.hl:325 陈述逐字）。两槽填掉后即 HOL 主定理的无条件形。
槽形与证体对应见文件头。 -/
theorem restrictedHypermapsArePlanegraphsReduction1OfSlots
    (hv7 : ∀ (L : fgraph ℕ) (hL : GoodList L) (N N' : List (List Dart)) (g : Graph)
        (p : ℕ) (fs : List Face) (f : Face) (v k : ℕ) (r : List Dart) (x : Dart),
        GoodListNodesTl L hL →
        (hypermapOfList L hL).IsRestricted →
        newvertexPrepped L N r x →
        markedList L hL N r x →
        ¬ finalList L r →
        matchQuotientList g L N →
        Kepler.Graphs.Graph.final g = false →
        PlaneGraphPSpine p g →
        GoodFacesV3 g →
        VerticesSet2Eq g →
        p = (L.map List.length).foldr max 0 - 3 →
        fs = nonFinals g →
        f = minimalFace fs →
        v = minimalVertex g f →
        (r, x) = loopChoice2 g L N →
        k = transformCount L N r x →
        N' = ntrans L N r x k →
        ∃ (g' : Graph) (i : ℕ), matchQuotientList g' L N' ∧ 3 ≤ i ∧ i ≤ maxGon p ∧
          GoodFacesV3 g' ∧ VerticesSet2Eq g' ∧ g' ∈ generatePolygon i v f g)
    (htav2 : ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodesTl L hL →
        transformAssumptionV2 L)
    (hne : ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodes L →
        (hypermapOfList L hL).IsRestricted →
        ∀ p : ℕ, p = (L.map List.length).foldr max 0 - 3 →
        ∃ (g : Graph) (L' : fgraph ℕ) (hL' : GoodList L') (N' : List (List Dart)),
          FinalsAdmissible L p g L' hL' N')
    (hMee : ∀ (L : fgraph ℕ) (hL : GoodList L) (N : List (List Dart)) (r : List Dart)
        (x : Dart) (L' : fgraph ℕ) (hL' : GoodList L') (N' : List (List Dart))
        (r' : List Dart) (x' : Dart),
        GoodListNodesTl L hL →
        IsoListSpine L L' ([x] :: r :: N) ([x'] :: r' :: N') →
        markedList L hL N r x → markedList L' hL' N' r' x') :
    restrictedHypermapsArePlaneGraphsV4 := by
  intro L hL hgnL hresL
  -- AQIUNPP3（tame_list.hl:10026）：前提二沿 i 归纳
  have haq : ∀ (M : fgraph ℕ) (hM : GoodList M),
      Kepler.Text.Reduction4Idx.AqiunppSlot M hM := by
    intro M hM hgnM N r x hm i
    induction i with
    | zero =>
      rw [Kepler.Text.Reduction5.ntrans_zero, Kepler.Text.Reduction5.rtrans_zero]
      exact hm
    | succ i ih =>
      rw [show i + 1 = Nat.succ i from rfl, Kepler.Text.TameSpine.tav2NtransSucc,
        Kepler.Text.TameSpine.tav2RtransSucc]
      exact htav2 M hM hgnM hM hgnM _ _ x ih
  -- max_finals_g_exists：极大元 (g, L', N')
  obtain ⟨p, hpdef⟩ : ∃ p, p = (L.map List.length).foldr max 0 - 3 := ⟨_, rfl⟩
  obtain ⟨g, L', hL', N', hadm, hmax⟩ :=
    maxFinalsGExists L hL hgnL hresL p hpdef (hne L hL hgnL hresL p hpdef)
  obtain ⟨hmq, hnl, hqu, hNne, hiso, hpg, hvs2, hgf, hflag, hq1⟩ := hadm
  -- L' 侧基础事实（iso_list_sym_nil / iso_list_good_list_nodes / iso_list_restricted）
  have hsym : IsoListSpine L' L [] [] :=
    Kepler.Text.TameSpine.isoListSpineSymNil hL hiso
  have hgn' : GoodListNodesTl L' hL' := isoListGoodListNodes hiso hL (hgnL hL) hL'
  have hres' : (hypermapOfList L' hL').IsRestricted :=
    Kepler.Text.TameSpine.isoListRestricted hL' hsym hresL
  have hend' : (hypermapOfList L' hL').EdgeNondegenerate := hres'.edgeNondegenerate
  have hall' : ∀ l ∈ L', l.Nodup :=
    Kepler.Text.TameSpine.simpleHypermapAllUniq L' hL' hgn' hres'.simple
  have hnlS' : NormalListSpine hL' N' :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L' hL' N').mp hnl
  have hfg : g.fgraph = quotientList L' N' := hmq.2
  have hung : ∀ l ∈ g.fgraph, l.Nodup := by
    rw [hfg]
    exact hqu
  have hgq : GoodList (quotientList L' N') := by
    rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
    exact Kepler.Text.TameSpine.goodListQuotient L' hL' hnlS' hend' hall'
  have hp' : (L'.map List.length).foldr max 0 - 3 = p := by
    rw [hpdef, Kepler.Text.TameSpine.isoListSize hiso]
  -- 核心：极大元必为终图
  have hfinal : Kepler.Graphs.Graph.final g = true := by
    by_contra hcon
    have hnf : Kepler.Graphs.Graph.final g = false := Bool.eq_false_iff.mpr hcon
    rcases hlc : loopChoice2 g L' N' with ⟨r, x⟩
    by_cases hfin : finalList L' r
    · -- final_list 支：makeFaceFinal 给出 finals 更大的可许三元组
      have hfin' : finalList L' (loopChoice2 g L' N').1 := by
        rw [hlc]
        exact hfin
      obtain ⟨g₂, hmq₂, hpg₂, hvs2₂, hgf₂, hlt⟩ :=
        memMakeFaceFinalPlaneGraphPEtc hL' hnf hung hnl hNne hpg hp' hmq hres' hqu
          hfin' hgn' hvs2 hgf
      have hle := hmax g₂ L' hL' N'
        ⟨hmq₂, hnl, hqu, hNne, hiso, hpg₂, hvs2₂, hgf₂, hflag, hq1⟩
      omega
    · -- 非 final 支：HKBGWJI → iso_list_newvertex_lemma → MEEIXJO → v7
      have hm : markedList L' hL' N' r x :=
        hkbgwji hL' hgn' hres' hnl hnf hfin hqu hq1 hflag hmq hlc.symm
      obtain ⟨L₂, N₂, r₂, x₂, hiso₂, hmq₂, hprep⟩ :=
        isoListNewvertexLemma hL' hend' hall' hgn' hm
          (fun d hd hdN => Kepler.Text.TameSpine.obdatybChain L' hL' hgn' (haq L' hL')
            (Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L' hL'
              (haq L' hL')) hm hd hdN)
          hmq hvs2
      have hiso₂0 : IsoListSpine L' L₂ [] [] := by
        obtain ⟨phi, hinj, hLmap, -⟩ := hiso₂
        exact ⟨phi, hinj, hLmap, rfl⟩
      have hL₂ : GoodList L₂ := Kepler.Text.TameSpine.isoListSpine_goodList hiso₂ hL'
      have hgn₂ : GoodListNodesTl L₂ hL₂ := isoListGoodListNodes hiso₂0 hL' hgn' hL₂
      have hm₂ : markedList L₂ hL₂ N₂ r₂ x₂ :=
        hMee L' hL' N' r x L₂ hL₂ N₂ r₂ x₂ hgn' hiso₂ hm
      have hres₂ : (hypermapOfList L₂ hL₂).IsRestricted := hm₂.1
      have hfin₂ : ¬ finalList L₂ r₂ := fun hc =>
        hfin ((Kepler.Text.TameSpine.isoListFinalListEqSpine
          (Kepler.Text.TameSpine.isoListCons hiso₂) hnlS' hm.2.2.1).mp hc)
      obtain ⟨-, hlc₂⟩ :=
        isoListLoopChoice hL' hL₂ hgn' hres' hnl hnf hmq hmq₂ hqu hgq hm hm₂ hiso₂
          hlc.symm
      have hp₂ : p = (L₂.map List.length).foldr max 0 - 3 := by
        rw [hpdef, Kepler.Text.TameSpine.isoListSize hiso,
          Kepler.Text.TameSpine.isoListSize hiso₂0]
      obtain ⟨g₃, i, hmq₃, hi3, hile, hgf₃, hvs2₃, hg₃⟩ :=
        hv7 L₂ hL₂ N₂ _ g p _ _ _ _ r₂ x₂ hgn₂ hres₂ hprep hm₂ hfin₂ hmq₂ hnf hpg
          hgf hvs2 hp₂ rfl rfl rfl hlc₂.symm rfl rfl
      have hlt := generatePolygonMono hnf rfl rfl hg₃
      -- (g₃, L₂, ntrans …) 的可许性：AQIUNPP3 + final_list_transform_count
      have hmk := haq L₂ hL₂ hgn₂ N₂ r₂ x₂ hm₂ (transformCount L₂ N₂ r₂ x₂)
      have hfinK : finalList L₂ (rtrans L₂ N₂ r₂ x₂ (transformCount L₂ N₂ r₂ x₂)) :=
        Kepler.Text.Reduction5.finalListTransformCount L₂ hL₂ hgn₂ (haq L₂ hL₂) hm₂ rfl
      have hpg₃ : PlaneGraphPSpine p g₃ := by
        refine planegraphPTrans hpg ?_
        have hne' : (nonFinals g).isEmpty = false := hnf
        rw [show next_plane p g =
            (if (nonFinals g).isEmpty = true then []
             else (List.range' 3 (maxGon p - 2)).flatMap fun i =>
               generatePolygon i (minimalVertex g (minimalFace (nonFinals g)))
                 (minimalFace (nonFinals g)) g) from rfl,
          if_neg (by rw [hne']; simp)]
        refine List.mem_flatMap.mpr ⟨i, ?_, hg₃⟩
        rw [List.mem_range'_1]
        refine ⟨hi3, ?_⟩
        rw [Kepler.Graphs.maxGon] at hile ⊢
        omega
      have hle := hmax g₃ L₂ hL₂ (ntrans L₂ N₂ r₂ x₂ (transformCount L₂ N₂ r₂ x₂))
        ⟨hmq₃, hmk.2.1, hmk.2.2.2.2.1.1, List.ne_nil_of_mem hmk.2.2.1,
          (Kepler.Text.TameSpine.isoListSnd hiso).mpr hiso₂0, hpg₃, hvs2₃, hgf₃,
          hmk.2.2.2.2.2.2.2.1 hfinK, hmk.2.2.2.2.1.2⟩
      omega
  -- 收口：g 即所求（restricted_match_finalGraph + GNBEVVU + 商层 good_list(_nodes)）
  obtain ⟨hg, hEq⟩ := restrictedMatchFinalGraph hL' hgn' hnl hres' hmq hfinal hNne
  have heq : g.fgraph = quotientListSpine L' N' := by
    rw [hfg, Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
  have hgnq : GoodListNodes g.fgraph := by
    have key : ∀ X : fgraph ℕ, X = quotientListSpine L' N' → GoodListNodes X := by
      intro X hX
      subst hX
      intro hX'
      exact Kepler.Text.TameSpine.goodListNodesQuotient L' hL' hgn' hnlS' hend' hall'
    exact key _ heq
  refine ⟨g, (Kepler.Text.TameSpine.planegraphPlaneGraphs g).mpr
    ⟨⟨p, hpg⟩, List.isEmpty_iff.mp hfinal⟩, ⟨hg, hgnq, hfinal, hung, hgf, hvs2⟩, hg, ?_⟩
  show (hypermapOfList L hL).Iso (hypermapOfList (fgraphOfGraph g) hg)
  rw [hEq]
  exact Kepler.Text.TameSpine.GNBEVVU hL hiso

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.restrictedHypermapsArePlanegraphsReduction1OfSlots
