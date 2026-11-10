/-
  Kepler.Text.Reduction1W1p — J4 Wave W1 批 7b（编排者按车道冻结包
  `DELIVERY_W1O_7B.md` 收口）：`enumeration_vertex_list_lemma`
  （HOL `reduction1.hl:1163-1247`，19 前提）+ `enumeration_vertex_list`
  （`:1248-1379`，12 前提 wrapper）。**W1 验收点**。

  ┌─ 结构 ─────────────────────────────────────────────────────────
  │ §1 `noConsecutiveDuplicate`：P19 正向 → `listPairsIsNextElem` →
  │    `is_nextElem_edges_eq` → `f.nextVertex u1 = u2` 撞 witness 第三合取。
  │    （车道原判的 `mem_list_pairs_explicit` 不需要；`is_nextElem` ⇒
  │    `nextVertex` 桥走 `Face.edges` def，同 `dart_neighbors` 装配。）
  │ §2 `enumerationVertexListLemma`：Ob1（`enumerationVertexListEnumMem`）
  │    + Ob2（§3 `containsUnacceptableDuplicateEdgeExplicit`）+ Ob3
  │    （`enumerationVertexListIndexToVertex`）。
  │ §3 wrapper：补 8 条被剥前提——`HD vs' = v`（filter/map 头）、
  │    `isSome (HD vs)`、`2 ≤ |F|`（vs' 前二项相异 + idxOf 单射）、
  │    `2 ≤ |vs'|`（`filterEl` 双真位）、`indexf v LAST = |F|−1`
  │    （`nextElPrevElUniq` + `indexfPrev`）、`uniq (FST f)`、
  │    `MEM v (FST f)`、`image_hideDups vs`（`unadjAlt` + 严格单调）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W1n
import Kepler.Text.Reduction1W1o
import Kepler.Text.Reduction1W1m
import Kepler.Text.Reduction1W1g
import Kepler.Text.TameSpine.TameList54
import Kepler.Text.TameSpine.JcajyduRed2Trans

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (listOfDarts listPairs prevEl nextEl)
open Kepler.Graphs (Graph Face Vertex containsDuplicateEdge is_nextElem is_nextElem_edges_eq)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq)
open Kepler.Text.TameSpine (enumOfVertexList indexf ImageHideDups Unadj
  nextElPrevElUniq indexfPrev unadjAlt)

/-! ## §0 私件 -/

/-- `map` 的 `getElem!`（泛型版；W1m 私件跨文件不可见）。 -/
private theorem getElemBangMap {α β : Type} [Inhabited α] [Inhabited β]
    {l : List α} {g : α → β} {i : Nat} (h : i < l.length) :
    (l.map g)[i]! = g (l[i]!) := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp only [Option.map_some, Option.getD_some]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp

/-- `o` 为 some 时等于 `some (o.getD 0)`。 -/
private theorem eqSomeGetD {o : Option Nat} (h : o.isSome = true) :
    o = some (o.getD 0) := by
  cases o with
  | none => simp at h
  | some x => rfl

/-! ## §1 hnoDup 派生（P19 正向 + nextVertex 矛盾） -/

/-- **P19 ⇒ §3 的 `hnoDup`**：相邻两位 some 且 `(u1,u2)` 是 dart 时，P19 给
`(u1,u2) ∈ list_pairs F`，经 `listPairsIsNextElem` + `Face.edges` 得
`f.nextVertex u1 = u2`，撞 witness 第三合取。 -/
theorem noConsecutiveDuplicate {f : Face} {g : Graph} {vs : List (Option Nat)}
    (hnd : f.vertices.Nodup)
    (hP19 : ∀ (i : Nat) (d : Nat × Nat), i + 1 < vs.length →
      (vs[i]!).isSome = true → (vs[i + 1]!).isSome = true →
      d ∈ listOfDarts g.fgraph → d ∈ listPairs f.vertices) :
    ¬ ∃ i, i + 1 < vs.length ∧ (vs[i]!).isSome = true ∧
      (vs[i + 1]!).isSome = true ∧
      (vs[i]!.getD 0 ≠ (vs[i + 1]!.getD 0) ∧
       f.nextVertex (vs[i + 1]!.getD 0) ≠ (vs[i]!.getD 0) ∧
       f.nextVertex (vs[i]!.getD 0) ≠ (vs[i + 1]!.getD 0) ∧
       ((vs[i]!.getD 0), (vs[i + 1]!.getD 0)) ∈ listOfDarts g.fgraph) := by
  rintro ⟨i, hi, h1, h2, -, -, hne, hin⟩
  have hpairs : ((vs[i]!.getD 0), (vs[i + 1]!.getD 0)) ∈ listPairs f.vertices :=
    hP19 i _ hi h1 h2 hin
  have his : is_nextElem f.vertices (vs[i]!.getD 0) (vs[i + 1]!.getD 0) :=
    (listPairsIsNextElem f.vertices _ _).mp hpairs
  have hedge : ((vs[i]!.getD 0), (vs[i + 1]!.getD 0)) ∈ f.edges :=
    (is_nextElem_edges_eq hnd).mpr his
  simp only [Kepler.Graphs.Face.edges, Set.mem_setOf_eq] at hedge
  exact hne hedge.2

/-! ## §2 `enumeration_vertex_list_lemma`（19 前提，HOL :1163-1247） -/

/-- **HOL `enumeration_vertex_list_lemma`**：见证 `e = enum_of_VertexList F v vs`
同时满足三合取（enumerator 成员性 / 无重边 / `indexToVertexList` 回读）。 -/
theorem enumerationVertexListLemma {g : Graph} {f : Face} {v : Nat}
    {vs : List (Option Nat)} {vs' : List Nat}
    (hvs' : vs' = (vs.filter Option.isSome).map Option.get!)
    (hhd' : vs'.head! = v)
    (h3 : 3 ≤ vs.length)
    (h2f : 2 ≤ f.vertices.length)
    (hhd : vs.head! = some v)
    (hhdSome : (vs.head!).isSome = true)
    (hlastSome : (vs.getLast!).isSome = true)
    (h2vs' : 2 ≤ vs'.length)
    (hlastIdx : indexf v (vs.getLast!.getD 0) f.vertices = f.vertices.length - 1)
    (hnd : f.vertices.Nodup)
    (hvmem : v ∈ f.vertices)
    (himg : ImageHideDups vs)
    (hfm : f.vertices ∈ g.fgraph)
    (hun : ∀ l ∈ g.fgraph, l.Nodup)
    (hgf : GoodFacesV3 g)
    (hvs2 : VerticesSet2Eq g)
    (hall : ∀ t ∈ (vs.filter Option.isSome).map Option.get!, t ∈ f.vertices)
    (hmono : ∀ i, i + 1 < vs'.length →
      indexf v vs'[i]! f.vertices < indexf v vs'[i + 1]! f.vertices)
    (hP19 : ∀ (i : Nat) (d : Nat × Nat), i + 1 < vs.length →
      (vs[i]!).isSome = true → (vs[i + 1]!).isSome = true →
      d ∈ listOfDarts g.fgraph → d ∈ listPairs f.vertices) :
    ∃ e, e ∈ Kepler.Graphs.enumerator vs.length f.vertices.length ∧
      containsDuplicateEdge g f v e = false ∧
      vs = Kepler.Graphs.indexToVertexList f v e := by
  refine ⟨enumOfVertexList f.vertices v vs, ?_, ?_, ?_⟩
  · exact enumerationVertexListEnumMem hvs' h3 hhd hnd hvmem hall hmono hlastSome hlastIdx h2f
  · have hev : (enumOfVertexList f.vertices v vs).length = vs.length :=
      Kepler.Text.TameSpine.sizeEnumOfVertexList f.vertices v vs
    have hmonoE : ∀ i, i + 1 < (enumOfVertexList f.vertices v vs).length →
        (enumOfVertexList f.vertices v vs)[i]! ≤
          (enumOfVertexList f.vertices v vs)[i + 1]! := by
      intro i hi
      rw [hev] at hi
      exact enumOfVertexListMono hhd hnd hvmem hvs' hmono i hi
    exact containsUnacceptableDuplicateEdgeExplicit hmonoE rfl (by omega) hfm hun
      hnd hall hgf hvs2 hhd (noConsecutiveDuplicate hnd hP19)
  · exact (enumerationVertexListIndexToVertex hnd hvmem himg hall).symm

/-! ## §3 wrapper `enumeration_vertex_list`（12 前提，HOL :1248-1379） -/

/-- **HOL `enumeration_vertex_list`**：以 `prev_el F v = the (LAST vs)` 替代
lemma 的 8 条被剥前提（`HD vs' = v` / `isSome (HD vs)` / 两处 `2 ≤` /
`indexf v LAST = |F|−1` / `uniq F` / `MEM v F` / `image_hideDups`）。 -/
theorem enumerationVertexList {g : Graph} {f : Face} {v : Nat}
    {vs : List (Option Nat)} {vs' : List Nat}
    (hvs' : (vs.filter Option.isSome).map Option.get! = vs')
    (h3 : 3 ≤ vs.length)
    (hhd : vs.head! = some v)
    (hlastSome : (vs.getLast!).isSome = true)
    (hprev : prevEl f.vertices v = vs.getLast!.getD 0)
    (hfm : f.vertices ∈ g.fgraph)
    (hun : ∀ l ∈ g.fgraph, l.Nodup)
    (hgf : GoodFacesV3 g)
    (hvs2 : VerticesSet2Eq g)
    (hall : ∀ t ∈ (vs.filter Option.isSome).map Option.get!, t ∈ f.vertices)
    (hmono : ∀ i, i + 1 < vs'.length →
      indexf v vs'[i]! f.vertices < indexf v vs'[i + 1]! f.vertices)
    (hP19 : ∀ (i : Nat) (d : Nat × Nat), i + 1 < vs.length →
      (vs[i]!).isSome = true → (vs[i + 1]!).isSome = true →
      d ∈ listOfDarts g.fgraph → d ∈ listPairs f.vertices) :
    ∃ e, e ∈ Kepler.Graphs.enumerator vs.length f.vertices.length ∧
      containsDuplicateEdge g f v e = false ∧
      vs = Kepler.Graphs.indexToVertexList f v e := by
  have hne : vs ≠ [] := by intro hc; rw [hc] at h3; simp at h3
  have hnd : f.vertices.Nodup := hun f.vertices hfm
  have hjLt : vs.length - 1 < vs.length := by omega
  have hlastSomeE : vs[vs.length - 1]!.isSome = true := by
    rw [getElemLastEq (l := vs) (by omega : 0 < vs.length)]; exact hlastSome
  have hlastEq : vs.getLast! = some (vs.getLast!.getD 0) := eqSomeGetD hlastSome
  have hlastmem : vs.getLast! ∈ vs := by
    rw [List.getLast!_eq_getElem!, getElemBangH hjLt]
    exact List.getElem_mem hjLt
  have humem : vs.getLast!.getD 0 ∈ f.vertices := by
    refine hall _ (List.mem_map.mpr ⟨vs.getLast!, ?_, ?_⟩)
    · rw [List.mem_filter]
      exact ⟨hlastmem, by rw [hlastEq]; rfl⟩
    · rw [hlastEq]; rfl
  have hhdSome : (vs.head!).isSome = true := by rw [hhd]; rfl
  -- `HD vs' = v`
  have hhd' : vs'.head! = v := by
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.head!_cons] at hhd
    subst hhd
    rw [← hvs']
    simp
  -- `isSome (HD vs)` 之后的名字保持与 lemma 槽一致
  -- `2 ≤ |vs'|`（`filterEl` 双真位）
  have hzero : vs[0]!.isSome = true := by
    rw [← List.head!_eq_getElem!]; exact hhdSome
  have h0lt : 0 < vs.length := by omega
  have hsomeP0 : vs[0].isSome = true := by rw [← getElemBangH h0lt]; exact hzero
  have hlastSomeP : vs[vs.length - 1].isSome = true := by
    rw [← getElemBangH hjLt]; exact hlastSomeE
  obtain ⟨r, s, hrs, hsLt, -, -⟩ :=
    filterEl (f := Option.isSome) (vs := vs) (vs' := vs.filter Option.isSome)
      rfl (by omega) hjLt hsomeP0 hlastSomeP
  have h2filt : 2 ≤ (vs.filter Option.isSome).length := by omega
  have hlen : vs'.length = (vs.filter Option.isSome).length := by
    rw [← hvs', List.length_map]
  have h2vs' : 2 ≤ vs'.length := by rw [hlen]; exact h2filt
  -- `MEM v F`
  have h0lt' : 0 < vs.length := by omega
  have h0eq : vs[0]! = some v := by
    rw [← List.head!_eq_getElem!]; exact hhd
  have hheadmem : some v ∈ vs := by
    have hm0 : vs[0]! ∈ vs := by
      rw [getElemBangH h0lt']
      exact List.getElem_mem h0lt'
    exact h0eq ▸ hm0
  have hvmem : v ∈ f.vertices :=
    hall v (List.mem_map.mpr ⟨some v, by
      rw [List.mem_filter]
      exact ⟨hheadmem, rfl⟩, rfl⟩)
  -- `indexf v LAST = |F|-1`
  have hnext : nextEl f.vertices (vs.getLast!.getD 0) = v := by
    have h := nextElPrevElUniq hnd v
    rwa [hprev] at h
  have hlastIdx : indexf v (vs.getLast!.getD 0) f.vertices = f.vertices.length - 1 :=
    indexfPrev humem hvmem hnd hnext
  -- `2 ≤ |F|`（vs' 前二项相异）
  have hmemOfIdx : ∀ {j : Nat}, j < vs'.length → vs'[j]! ∈ f.vertices := by
    intro j hj
    have hjf : j < (vs.filter Option.isSome).length := by rw [← hlen]; exact hj
    rw [← hvs', getElemBangMap hjf, getElemBangH hjf]
    exact hall _ (List.mem_map.mpr ⟨_, List.getElem_mem hjf, rfl⟩)
  have ha : vs'[0]! ∈ f.vertices := hmemOfIdx (by omega)
  have hb : vs'[1]! ∈ f.vertices := hmemOfIdx (by omega)
  have hne01 : vs'[0]! ≠ vs'[1]! := by
    intro heq
    have h := hmono 0 (by omega)
    rw [heq] at h
    exact lt_irrefl _ h
  have h2f : 2 ≤ f.vertices.length := by
    have hidxne : f.vertices.idxOf vs'[0]! ≠ f.vertices.idxOf vs'[1]! := by
      intro heq
      exact hne01 ((List.idxOf_inj ha).mp heq)
    have h1 : f.vertices.idxOf vs'[0]! < f.vertices.length :=
      List.idxOf_lt_length_iff.mpr ha
    have h2 : f.vertices.idxOf vs'[1]! < f.vertices.length :=
      List.idxOf_lt_length_iff.mpr hb
    omega
  -- `image_hideDups vs`（unadjAlt + 严格单调）
  have himg : ImageHideDups vs := by
    refine Or.inr ⟨?_, hhdSome⟩
    rw [unadjAlt]
    intro i hi heq
    have hi' : i + 1 < vs'.length := by rw [hlen]; exact hi
    have hmonoI := hmono i hi'
    rw [← hvs'] at hmonoI
    rw [getElemBangMap (by omega), getElemBangMap (by omega)] at hmonoI
    have h_eq : indexf v (Option.get! ((vs.filter Option.isSome)[i]!)) f.vertices
        = indexf v (Option.get! ((vs.filter Option.isSome)[i + 1]!)) f.vertices := by
      rw [getElemBangH hi, getElemBangH (by omega)]
      exact congrArg (fun o => indexf v (Option.get! o) f.vertices) heq
    exact absurd h_eq (ne_of_lt hmonoI)
  exact enumerationVertexListLemma hvs'.symm hhd' h3 h2f hhd hhdSome hlastSome
    h2vs' hlastIdx hnd hvmem himg hfm hun hgf hvs2 hall hmono hP19

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.noConsecutiveDuplicate
#print axioms Kepler.Text.Reduction1.enumerationVertexListLemma
#print axioms Kepler.Text.Reduction1.enumerationVertexList
