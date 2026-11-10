/-
  Kepler.Text.Reduction1W2j — J4 Wave W2-3 验收点：`iso_list_newvertex_lemma`
  （HOL reduction1.hl:2154-2336）。

  witness = 分段重编号 `f`：s1（`N.flatten.map (·.1)`）上恒等；newvertex 顶点按
  `idxOf` 顺序 ↦ `[countVertices, …]`；其余元素（`elements_of_list L` 的 DIFF 段）
  ↦ 续段。`L'/N'/r'/x'` 取 mapped 形（iso 第三槽 `rfl`）；`match_quotient_list`
  经 `matchQuotientListMap` 运输；`newvertexPrepped` 走 prepped 支
  （`mapNewvertex` 运输 + Nodup `idxOf` 枚举对齐 `range'`）。
  `oldnew_vertex_disjoint` 在本构造中零消费（像区间不交即足），故无 hOb 槽；
  HOL 前提 `transform_assumption_v2 L` 在证明体内零消费，省略。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W2g
import Kepler.Text.Reduction1W2h
import Kepler.Text.TameLp
import Kepler.Text.ChainListsL1
import Kepler.Text.ChainListsL2
import Kepler.Text.MoreLemma2a23
import Kepler.Text.Reduction3DefsLayer
import Kepler.Text.Reduction1W2f

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts listPairs findFaceDarts)
open Kepler.Text.ChainLists (normalList markedList)
open Kepler.Text.Reduction3 (newvertex matchQuotientList newvertexPrepped fgraphOfGraph)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face elementsOfList listOfElements)
open Kepler.Text.TameSpine (rotateTo)

/-- **HOL `iso_list_newvertex_lemma`**（reduction1.hl:2154，W2-3 验收点）。 -/
theorem isoListNewvertexLemma {g : Kepler.Graphs.Graph} {L : Kepler.Graphs.fgraph ℕ}
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hgood : GoodList L)
    (hend : (Kepler.Text.TameLp.hypermapOfList L hgood).EdgeNondegenerate)
    (hall : ∀ l ∈ L, l.Nodup)
    (hgn : GoodListNodesTl L hgood)
    (hm : markedList L hgood N r x)
    (hOb : ∀ d : ℕ × ℕ, d ∈ findFaceDarts L x → d ∈ N.flatten → d ∈ r)
    (hmq : matchQuotientList g L N)
    (hv2 : {v : ℕ | v ∈ g.vertices} = elementsOfList (fgraphOfGraph g)) :
    ∃ L' : Kepler.Graphs.fgraph ℕ, ∃ N' : List (List (ℕ × ℕ)),
      ∃ r' : List (ℕ × ℕ), ∃ x' : ℕ × ℕ,
        Kepler.Text.TameSpine.IsoListSpine L L' ([x] :: r :: N)
            ([x'] :: r' :: N') ∧
          matchQuotientList g L' N' ∧ newvertexPrepped L' N' r' x' := by
  have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hgood hm
  have hrN : r ∈ N := hm.2.2.1
  have hnl : normalList L hgood N := hm.2.1
  have hloop := hnl.2.2.2.1 r hrN
  have hsub : ∀ e ∈ r, e ∈ listOfDarts L := fun e he => (hloop e he).1
  set s1l : List ℕ := N.flatten.map (fun d => d.1) with hs1l
  set news : List ℕ := newvertex L r x with hnewsDef
  have hNoNew : ∀ v ∈ news, v ∉ s1l := by
    intro v hv hc
    have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hgood hm
    have hvS : v ∈ Kepler.Text.setOfList (newvertex L r x) := Set.mem_setOf.mpr hv
    rw [setOfListNewvertex hgood hx] at hvS
    obtain ⟨t, ⟨htF, htNr⟩, htEq⟩ := (Set.mem_image _ _ _).mp hvS
    obtain ⟨w, hw, hwEq⟩ := List.mem_map.mp hc
    have ht2 := findFaceDartMemFlatten hgood hgn (hm.2.1) hw
      (memFindFaceImpMemDarts htF) (htEq ▸ hwEq.symm)
    exact absurd (hOb t htF ht2) htNr
  set els : List ℕ := listOfElements L with helsDef
  have hnewsNodup : news.Nodup :=
    newvertexUniq hx hgood hgn hall
  -- f := 分段重编号
  set f : ℕ → ℕ := fun v =>
    if v ∈ s1l then v
    else if v ∈ news then g.countVertices + news.idxOf v
    else g.countVertices + news.length + els.idxOf v with hfdef
  have hltS1 : ∀ v ∈ s1l, v < g.countVertices := by
    intro v hv
    have hv1 : v ∈ Kepler.Text.setOfList s1l := Set.mem_setOf.mpr hv
    have hv2' : v ∈ Kepler.Text.setOfList (List.range' 0 g.countVertices) :=
      (verticesNormalList (g := g) hgood hnl hmq hv2).symm ▸ hv1
    have := List.mem_range'.mp hv2'
    omega
  -- InjOn f（elements_of_list L 上，三段像区间两两不交）
  have hinj : Set.InjOn f (elementsOfList L) := by
    intro a ha b hb hEq
    have hae : a ∈ els := Set.mem_setOf.mp ha
    have hbe : b ∈ els := Set.mem_setOf.mp hb
    simp only [hfdef] at hEq
    have hidxNews : ∀ v ∈ news, news.idxOf v < news.length :=
      fun v hv => List.idxOf_lt_length_iff.mpr hv
    have hoptNews : ∀ v ∈ news, news[news.idxOf v]? = some v := fun v hv =>
      List.getElem?_eq_some_iff.mpr ⟨hidxNews v hv, List.getElem_idxOf (hidxNews v hv)⟩
    have hoptEls : ∀ v ∈ els, els[els.idxOf v]? = some v := fun v hv =>
      List.getElem?_eq_some_iff.mpr ⟨List.idxOf_lt_length_iff.mpr hv,
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)⟩
    by_cases ha1 : a ∈ s1l
    · by_cases hb1 : b ∈ s1l
      · rw [if_pos ha1, if_pos hb1] at hEq; exact hEq
      · have hlt := hltS1 a ha1
        by_cases hb2 : b ∈ news
        · rw [if_pos ha1, if_neg hb1, if_pos hb2] at hEq; omega
        · rw [if_pos ha1, if_neg hb1, if_neg hb2] at hEq; omega
    · by_cases ha2 : a ∈ news
      · have hia := hidxNews a ha2
        by_cases hb1 : b ∈ s1l
        · have hlt := hltS1 b hb1
          rw [if_neg ha1, if_pos ha2, if_pos hb1] at hEq; omega
        · by_cases hb2 : b ∈ news
          · rw [if_neg ha1, if_pos ha2, if_neg hb1, if_pos hb2] at hEq
            have hidx : news.idxOf a = news.idxOf b := by omega
            have ha' := hoptNews a ha2
            rw [hidx] at ha'
            exact Option.some.inj (ha'.symm.trans (hoptNews b hb2))
          · rw [if_neg ha1, if_pos ha2, if_neg hb1, if_neg hb2] at hEq; omega
      · by_cases hb1 : b ∈ s1l
        · have hlt := hltS1 b hb1
          rw [if_neg ha1, if_neg ha2, if_pos hb1] at hEq; omega
        · by_cases hb2 : b ∈ news
          · have hib := hidxNews b hb2
            rw [if_neg ha1, if_neg ha2, if_neg hb1, if_pos hb2] at hEq; omega
          · rw [if_neg ha1, if_neg ha2, if_neg hb1, if_neg hb2] at hEq
            have hidx : els.idxOf a = els.idxOf b := by omega
            have ha' := hoptEls a hae
            rw [hidx] at ha'
            exact Option.some.inj (ha'.symm.trans (hoptEls b hbe))
  have hfix : ∀ x ∈ s1l, f x = x := fun v hv => by
    rw [hfdef]; simp only []; rw [if_pos hv]
  have hfixNews : ∀ v ∈ news, f v = g.countVertices + news.idxOf v := fun v hv => by
    rw [hfdef]; simp only []; rw [if_neg (fun hc => hNoNew v hv hc), if_pos hv]
  refine ⟨L.map (List.map f), N.map (fun s => s.map (fun u => (f u.1, f u.2))),
    r.map (fun d => (f d.1, f d.2)), (f x.1, f x.2), ⟨f, hinj, rfl, rfl⟩, ?_, ?_⟩
  · exact (matchQuotientListMap hgood hend hall hnl hfix hinj).mpr hmq
  · refine Or.inr ?_
    show newvertex (L.map (List.map f))
      (r.map (fun d => (f d.1, f d.2))) (f x.1, f x.2) =
      List.range'
        ((N.map (fun s => s.map (fun u => (f u.1, f u.2)))).flatten.map
          (fun d => d.1) |>.dedup).length
      (newvertex (L.map (List.map f))
        (r.map (fun d => (f d.1, f d.2))) (f x.1, f x.2)).length
    rw [mapNewvertex hgood hx hsub hinj]
    have hflatten : (N.map (fun s => s.map (fun u => (f u.1, f u.2)))).flatten =
        N.flatten.map (fun d => (f d.1, f d.2)) := by
      induction N with
      | nil => rfl
      | cons s t ih => simp [List.map_cons, List.flatten_cons]
    have hFST : ((N.map (fun s => s.map (fun u => (f u.1, f u.2)))).flatten).map
        (fun d => d.1) = s1l := by
      rw [hflatten, List.map_map]
      refine List.map_congr_left fun d hd => ?_
      have hd1 : d.1 ∈ s1l := List.mem_map.mpr ⟨d, hd, rfl⟩
      show f d.1 = d.1
      exact hfix d.1 hd1
    have hnEq : ((N.map (fun s => s.map (fun u => (f u.1, f u.2)))).flatten.map
        (fun d => d.1) |>.dedup).length = g.countVertices := by
      rw [hFST]
      have hsetEq : Kepler.Text.setOfList s1l = Kepler.Text.setOfList s1l.dedup := by
        ext a; simp [Kepler.Text.setOfList, List.mem_dedup]
      have h1 := cardVerticesNormalList (g := g) hgood hnl hmq hv2
      rw [hsetEq] at h1
      exact (cardSetOfListUniq (List.nodup_dedup s1l)).symm.trans h1
    have hMapEq : news.map (fun v => f v) =
        List.range' g.countVertices news.length := by
      rw [List.map_congr_left (g := fun v => g.countVertices + news.idxOf v)
        (fun v hv => hfixNews v hv)]
      refine List.ext_getElem (by simp) ?_
      intro i hi1 hi2
      have hin1 : i < news.length := by rw [List.length_map] at hi1; exact hi1
      have hIdx := hnewsNodup.idxOf_getElem i hin1
      simp [hIdx]
    rw [hnEq]
    show news.map f = List.range' g.countVertices (news.map f).length
    rw [List.length_map]
    exact hMapEq

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.isoListNewvertexLemma
