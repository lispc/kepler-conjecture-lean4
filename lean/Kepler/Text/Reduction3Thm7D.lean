/-
  Kepler.Text.Reduction3Thm7D — reduction_B/C 的非 J2 支撑三件
  （`good_faces_makeFaceFinal` :2428 / `faces_at_v2_uniq` reduction2:1611 /
  `vs_nonnil` :2449）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ §A goodFacesMakeFaceFinal  reduction3.hl:2428
  │    前置 HOL 件一并落公开：facesAtMakeFaceFinal(:2409) /
  │    facesAtV2MakeFaceFinal(:2381) / facesAtMapFinal(:2414) /
  │    facesAtV2MapFinal(:2387)
  │ §B facesAtV2Uniq          reduction2.hl:1611
  │ §C vsNonnil               reduction3.hl:2449（条件槽形，DIFFERS ④）
  │ 收口后 reduction_C 的非 J2 支撑全清，只剩 reduction_C/B/A 本体（J2）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算/条件槽；语义逐字）──────────────────────────────
  │ ① `good_faces_v3` / `facesAt_v2` / `vertices_set2` 用 TameCorrList
  │    镜像（编排者裁定：镜像即 HOL 形，无需 DEF-FIX）。
  │ ② `sizel (faceListAt g)` ↦ `g.faceListAt.length`；`uniq` ↦ `.Nodup`；
  │    `MAP FST` ↦ `List.map (fun f => f.vertices)`；`replace`/`setFinal`/
  │    `makeFaceFinalFaceList` ↦ Kepler.Graphs 同名件（AFP 层）。
  │ ③ `is_restricted (hypermap_of_list L)` ↦ `(hypermapOfList L hL).IsRestricted`
  │    （hL 由 good_list 显式给出）。
  │ ④ **vs_nonnil 条件槽**：HOL 的 `good_list/good_list_nodes/marked_list/
  │    ¬final_list` 只经 TAV2 用于产出 `core_triple_nonnil` 所需 hfinal；
  │    链侧 T2 即 hfinal 条件槽 ⇒ 本件以 `hfinal : finalList L
  │    (rtrans L N r x (transformCount L N r x))` + `hnf : ¬ finalList L r`
  │    替代四载体前提，结论逐字；J2 落库后调用点实例化即回 HOL 形（T11 契约）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `t7d_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm5D
import Kepler.Text.TameCorrList
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.TameList58
import Kepler.Text.ChainBridgeParts

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)
open Kepler.Graphs (Face Graph between fgraph makeFaceFinal makeFaceFinalFaceList setFinal
  replace)
open Kepler.Text.Reduction5 (Dart core finalList quotientList rtrans transformCount)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (normalList)

/-! ## §0 私有辅助（HOL/树内私有件同证重落） -/

/-- `listPairs` 展平首投影 = 原表（`map_fst_zip`）。 -/
private theorem t7d_map_fst_listPairs {α : Type} (l : List α) :
    (listPairs l).map Prod.fst = l := by
  have hlen : l.length ≤ (l.drop 1 ++ l.take 1).length := by
    cases l with
    | nil => simp
    | cons x xs => simp
  rw [Kepler.Assembly.listPairs]
  exact List.map_fst_zip hlen

/-- `l ≠ [] ⇒ listPairs l ≠ []`（第一投影满射的逆否）。 -/
private theorem t7d_listPairs_ne_nil {α : Type} (l : List α) (h : l ≠ []) :
    listPairs l ≠ [] := by
  intro hc
  refine h (by rw [← t7d_map_fst_listPairs l, hc]; rfl)

/-- flatten 无重复 + 全非空成员 ⇒ 列表本身无重复。 -/
private theorem t7d_uniqFlatten {α : Type} {L : List (List α)}
    (hun : L.flatten.Nodup) (hn : ∀ l ∈ L, l ≠ []) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    rw [List.flatten_cons] at hun
    obtain ⟨_, h2, h3⟩ := List.nodup_append.mp hun
    rw [List.nodup_cons]
    refine ⟨?_, ih h2 (fun x hx => hn x (List.mem_cons_of_mem _ hx))⟩
    intro ha
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil a (hn a (List.mem_cons_self ..))
    exact (h3 z hz z (List.mem_flatten.mpr ⟨a, ha, hz⟩)) rfl

/-- HOL `List_hypermap.good_list_uniq`（compiled.hl:839）：`GoodList L → L.Nodup`。 -/
private theorem t7d_goodListNodup {L : fgraph ℕ} (hL : GoodList L) : L.Nodup :=
  List.Nodup.of_map listPairs
    (t7d_uniqFlatten (α := ℕ × ℕ) hL.1 (by
      intro q hq
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
      exact t7d_listPairs_ne_nil l (hL.2.1 l hl)))

/-- HOL `uniq_replace_map`（reduction3.hl:2368）：
`uniq fs ⇒ replace x [y] fs = MAP (\ p. if p = x then y else p) fs`。 -/
private theorem t7d_uniqReplaceMap {α : Type} [DecidableEq α] [BEq α]
    [LawfulBEq α] {fs : List α} {x y : α} (h : fs.Nodup) :
    replace x [y] fs = fs.map (fun p => if p = x then y else p) := by
  induction fs with
  | nil => rfl
  | cons a t ih =>
    show (if a == x then [y] ++ t else a :: replace x [y] t)
      = (a :: t).map (fun p => if p = x then y else p)
    by_cases hax : a = x
    · have hbeq : (a == x) = true := by rw [hax]; exact beq_self_eq_true x
      rw [hbeq, if_pos rfl, hax, List.map_cons, if_pos rfl]
      have hnot : x ∉ t := by
        rw [← hax]
        exact (List.nodup_cons.mp h).1
      have hmapid : t.map (fun p => if p = x then y else p) = t := by
        rw [show t.map (fun p => if p = x then y else p) = t.map id from
          List.map_congr_left (fun p hp => by
            exact if_neg (fun hpx => hnot (by rw [hpx] at hp; exact hp)))]
        rw [List.map_id]
      rw [hmapid]
      rfl
    · have hbeq : (a == x) = false := by
        rw [beq_eq_false_iff_ne]
        exact hax
      rw [hbeq, if_neg (by simp), List.map_cons, if_neg hax,
        ih (List.Nodup.of_cons h)]

/-- `x ∉ l ⇒ replace x ys l = l`。 -/
private theorem t7d_replace_of_not_mem {α : Type} [BEq α] [LawfulBEq α]
    {x : α} {ys l : List α} (h : x ∉ l) : replace x ys l = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show (if a == x then ys ++ t else a :: replace x ys t) = a :: t
    by_cases hax : a = x
    · have hbeq : (a == x) = true := by rw [hax]; exact beq_self_eq_true x
      rw [hbeq, if_pos rfl]
      exact absurd (by rw [← hax]; exact List.mem_cons_self) h
    · have hbeq : (a == x) = false := by
        rw [beq_eq_false_iff_ne]
        exact hax
      rw [hbeq, if_neg (by simp), ih (fun hx => h (List.mem_cons_of_mem a hx))]

/-- HOL `mem_fst_setFinal`（tame_list.hl:14179）的 vertices 形：
`filter (MEM v ∘ vertices)` 与 `replace f [setFinal f]` 交换
（`(setFinal f).vertices = f.vertices` 使谓词在替换处不变）。 -/
private theorem t7d_filterReplace (v : ℕ) (f : Face) (fs : List Face) :
    (replace f [setFinal f] fs).filter (fun p => decide (v ∈ p.vertices))
      = replace f [setFinal f] (fs.filter (fun p => decide (v ∈ p.vertices))) := by
  let P : Face → Bool := fun p => decide (v ∈ p.vertices)
  change (replace f [setFinal f] fs).filter P = replace f [setFinal f] (fs.filter P)
  have hPset : P (setFinal f) = P f := rfl
  induction fs with
  | nil => rfl
  | cons a t ih =>
    conv_rhs => rw [List.filter_cons]
    show (if a == f then [setFinal f] ++ t else a :: replace f [setFinal f] t).filter P
      = replace f [setFinal f]
          (if P a = true then a :: List.filter P t else List.filter P t)
    by_cases haf : a = f
    · rw [show (a == f) = true from by rw [haf]; exact beq_self_eq_true f, if_pos rfl]
      simp only [haf]
      rw [List.filter_append]
      by_cases hP : P f = true
      · simp only [if_pos hP]
        have hPf : P (setFinal f) = true := by rw [hPset]; exact hP
        rw [show List.filter P [setFinal f] = [setFinal f] from by
          rw [List.filter_cons, List.filter_nil, hPf, if_pos rfl]]
        rw [show replace f [setFinal f] (f :: List.filter P t)
            = [setFinal f] ++ List.filter P t from by
          show (if (f == f) = true then [setFinal f] ++ List.filter P t
              else f :: replace f [setFinal f] (List.filter P t)) = _
          rw [beq_self_eq_true f, if_pos rfl]]
      · have hPf : P (setFinal f) = false := by
          rw [hPset]
          cases hp : P f <;> simp_all
        simp only [if_neg hP]
        rw [show List.filter P [setFinal f] = [] from by
          rw [List.filter_cons, List.filter_nil, hPf, if_neg (by simp)]]
        rw [List.nil_append]
        rw [show replace f [setFinal f] (List.filter P t) = List.filter P t from
          t7d_replace_of_not_mem (by
            intro hm
            exact absurd (List.mem_filter.mp hm).2 hP)]
    · have hbeq : (a == f) = false := by
        rw [beq_eq_false_iff_ne]
        exact haf
      rw [hbeq, if_neg (by simp), List.filter_cons]
      by_cases hP : P a = true
      · simp only [if_pos hP]
        rw [show replace f [setFinal f] (a :: List.filter P t)
            = a :: replace f [setFinal f] (List.filter P t) from by
          show (if (a == f) = true then [setFinal f] ++ List.filter P t
              else a :: replace f [setFinal f] (List.filter P t)) = _
          rw [show (a == f) = false from hbeq, if_neg (by simp)]]
        rw [ih]
      · simp only [if_neg hP]
        exact ih

/-! ## §A `good_faces_makeFaceFinal` 及其前置（:2381/:2387/:2409/:2414/:2428） -/

/-- HOL `facesAt_makeFaceFinal`（reduction3.hl:2409）：
`v < sizel (faceListAt g) ⇒ facesAt (makeFaceFinal f g) v =
makeFaceFinalFaceList f (facesAt g v)`。 -/
theorem facesAtMakeFaceFinal (f : Face) (g : Graph) (v : ℕ)
    (hv : v < g.faceListAt.length) :
    (makeFaceFinal f g).facesAt v = makeFaceFinalFaceList f (g.facesAt v) := by
  unfold Graph.facesAt
  rw [Kepler.Text.TameSpine.faceListAtMakeFaceFinal]
  have hv' : v < (g.faceListAt.map (makeFaceFinalFaceList f)).length := by
    rwa [List.length_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv',
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]
  simp only [Option.getD_some, List.getElem_map]

/-- HOL `facesAt_v2_makeFaceFinal`（reduction3.hl:2381）：
`facesAt_v2 (makeFaceFinal f g) v = makeFaceFinalFaceList f (facesAt_v2 g v)`。 -/
theorem facesAtV2MakeFaceFinal (f : Face) (g : Graph) (v : ℕ) :
    Kepler.Text.TameCorrList.facesAtV2 (makeFaceFinal f g) v
      = makeFaceFinalFaceList f (Kepler.Text.TameCorrList.facesAtV2 g v) := by
  unfold Kepler.Text.TameCorrList.facesAtV2
  rw [Kepler.Text.TameSpine.facesMakeFaceFinal]
  exact t7d_filterReplace v f g.faces

/-- HOL `facesAt_map_final`（reduction3.hl:2414）：
`uniq (facesAt g v) ∧ v < sizel (faceListAt g) ⇒
facesAt (makeFaceFinal f g) v = MAP (\p. if p = f then setFinal f else p) (facesAt g v)`。 -/
theorem facesAtMapFinal (f : Face) (g : Graph) (v : ℕ)
    (huniq : (g.facesAt v).Nodup) (hv : v < g.faceListAt.length) :
    (makeFaceFinal f g).facesAt v
      = (g.facesAt v).map (fun p => if p = f then setFinal f else p) := by
  rw [facesAtMakeFaceFinal f g v hv]
  exact t7d_uniqReplaceMap huniq

/-- HOL `facesAt_v2_map_final`（reduction3.hl:2387）：
`uniq (facesAt_v2 g v) ⇒
facesAt_v2 (makeFaceFinal f g) v =
MAP (\p. if p = f then setFinal f else p) (facesAt_v2 g v)`。 -/
theorem facesAtV2MapFinal (f : Face) (g : Graph) (v : ℕ)
    (huniq : (Kepler.Text.TameCorrList.facesAtV2 g v).Nodup) :
    Kepler.Text.TameCorrList.facesAtV2 (makeFaceFinal f g) v
      = (Kepler.Text.TameCorrList.facesAtV2 g v).map
          (fun p => if p = f then setFinal f else p) := by
  rw [facesAtV2MakeFaceFinal]
  exact t7d_uniqReplaceMap huniq

/-- HOL `good_faces_makeFaceFinal`（reduction3.hl:2428）：
`(∀v∈vertices_set2 g, uniq (facesAt_v2 g v)) ∧
sizel (faceListAt g) = countVertices g ∧ good_faces_v3 g ⇒
good_faces_v3 (makeFaceFinal f g)`。 -/
theorem goodFacesMakeFaceFinal (f : Face) (g : Graph)
    (huniq : ∀ v ∈ Kepler.Text.TameCorrList.verticesSet2 g,
      (Kepler.Text.TameCorrList.facesAtV2 g v).Nodup)
    (hlen : g.faceListAt.length = g.countVertices)
    (hgv3 : Kepler.Text.TameCorrList.GoodFacesV3 g) :
    Kepler.Text.TameCorrList.GoodFacesV3 (makeFaceFinal f g) := by
  intro v hv
  have hvv : v ∈ (makeFaceFinal f g).vertices := hv
  rw [Kepler.Text.TameSpine.verticesSet2MakeFaceFinal] at hvv
  have hv' : v ∈ Kepler.Text.TameCorrList.verticesSet2 g := hvv
  have hndV2 := huniq v hv'
  have hperm := hgv3 v hv'
  have hndAt : (g.facesAt v).Nodup := hperm.nodup_iff.mp hndV2
  have hlt : v < g.faceListAt.length := by
    rw [hlen]
    simpa [Kepler.Graphs.Graph.vertices, List.mem_range] using hvv
  rw [facesAtV2MapFinal f g v hndV2, facesAtMapFinal f g v hndAt hlt]
  exact hperm.map _

/-! ## §B `faces_at_v2_uniq`（reduction2.hl:1611） -/

/-- HOL `faces_at_v2_uniq`（reduction2.hl:1611）：
`good_list L ∧ good_list_nodes L ∧ normal_list L N ∧
is_restricted (hypermap_of_list L) ∧ fgraph g = quotient_list L N ⇒
uniq (facesAt_v2 g v)`。 -/
theorem facesAtV2Uniq (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (N : List (List Dart)) (hn : normalList L hL N)
    (hir : (hypermapOfList L hL).IsRestricted)
    (g : Graph) (v : ℕ) (hmq : fgraphOfGraph g = quotientList L N) :
    (Kepler.Text.TameCorrList.facesAtV2 g v).Nodup := by
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hn
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hir.simple
  have hgqS : GoodList (Kepler.Text.TameSpine.quotientListSpine L N) :=
    Kepler.Text.TameSpine.goodListQuotient L hL hnS hir.edgeNondegenerate hunL
  have hgq : GoodList (quotientList L N) := by
    rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
    exact hgqS
  have hquotNodup : (quotientList L N).Nodup := t7d_goodListNodup hgq
  have hfgraph : (fgraphOfGraph g).Nodup := by rw [hmq]; exact hquotNodup
  have hfaces : g.faces.Nodup :=
    List.Nodup.of_map (fun f : Face => f.vertices)
      (by simpa [fgraphOfGraph] using hfgraph)
  unfold Kepler.Text.TameCorrList.facesAtV2
  exact List.Nodup.filter _ hfaces

/-! ## §C `vs_nonnil`（reduction3.hl:2449；条件槽形，DIFFERS ④） -/

/-- HOL `vs_nonnil`（reduction3.hl:2449；条件槽形）：
`uvns = core_triple_v4 L N r x ∧ vs = dest_triple_full f v uvns ⇒ vs ≠ []`
（HOL 的四载体前提经 TAV2 产出 hfinal；链侧以 hfinal 槽 + ¬final 替代）。 -/
theorem vsNonnil (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (f : List ℕ) (v : ℕ) (uvns : List (ℕ × ℕ × ℕ)) (vs : List (Option ℕ))
    (hfinal : finalList L (rtrans L N r x (transformCount L N r x)))
    (hnf : ¬ finalList L r)
    (huvns : uvns = coreTripleV4 L N r x)
    (hvs : vs = destTripleFull f v uvns) :
    vs ≠ [] := by
  subst hvs
  unfold destTripleFull
  dsimp only
  have hne : uvns ≠ [] := by
    rw [huvns]
    exact coreTripleNonnil L N r x hfinal hnf
  have hdt : destTriple0 f [] uvns ≠ [] :=
    destTriple0Nonnil uvns f [] (Or.inl hne)
  intro h
  rcases List.append_eq_nil_iff.mp h with ⟨h1, _⟩
  rcases List.append_eq_nil_iff.mp h1 with ⟨_, hd⟩
  exact hdt hd

end Kepler.Text.Reduction3

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.facesAtMakeFaceFinal
#print axioms Kepler.Text.Reduction3.facesAtV2MakeFaceFinal
#print axioms Kepler.Text.Reduction3.facesAtMapFinal
#print axioms Kepler.Text.Reduction3.facesAtV2MapFinal
#print axioms Kepler.Text.Reduction3.goodFacesMakeFaceFinal
#print axioms Kepler.Text.Reduction3.facesAtV2Uniq
#print axioms Kepler.Text.Reduction3.vsNonnil
