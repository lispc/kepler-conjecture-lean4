/-
  Kepler.Text.Reduction3Thm10B — J 战役 T10B 批（链 4 纯列表 6 件 + 链 5 单件）。

  ┌─ 件目（reduction3.hl）────────────────────────────────────────
  │   indexl_replace     :3899 → t10b_indexl_replace
  │   not_uniq_replace    :3918 → t10b_not_uniq_replace
  │   indexl_uniq_replace :3930 → t10b_indexl_uniq_replace
  │   indexl_map_uniq     :3983 → t10b_indexl_map_uniq
  │   indexl_core         :3998 → t10b_indexl_core
  │   indexl_splitFace    :4010 → t10b_indexl_splitFace
  │   sizel_3_concl       :846  → t10b_sizel_3_concl（链 5）
  └────────────────────────────────────────────────────────────────

  ┌─ 载体/依赖（全树内已 #check 核验；见审计 §2.4）──────────────
  │ HOL `indexl y s` ↦ Lean `s.idxOf y`（参数序：表在前、元在后）；
  │ `replace x [y] s` ↦ `Kepler.Graphs.replace`；`uniq ↦ Nodup`；
  │ `fgraph g = MAP FST (faces g)` ↦ `fgraphOfGraph g = g.faces.map
  │ Face.vertices`（D2）。`fgraph_splitFace`（Reduction2）在本树为
  │ splitFace 定义级 rfl（faces = replace oldF [f2] fs ++ [f1]）。
  │ indexl_map_uniq ← `TameLp.la7_idxOf_map` + `JcajyduBetwnBase.uniqImpInj`
  │   （Aq8 换名件，故本件**非 J2**）。
  │ indexl_core ← `MoreLemma2Island1.quotientListCore`。
  │ indexl_splitFace ← splitFace 定义 + `t9_mem_replace` + 本批两件。
  │ sizel_3_concl ← `MoreLemma2a23.markedListOfDart` +
  │   `TameSpine.memFindFace` + `TameSpine.isRestrictedSizeFace`。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」；
  │ if 重写一律 `simp only [if_pos/if_neg]`；`List.idxOf_cons` 走 simp only。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm9
import Kepler.Text.Reduction3DefsLayer
import Kepler.Text.Reduction3Thm13B
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2a23
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.TameList49
import Kepler.Text.TameSpine.TameList56

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList listPairs listOfDarts findFaceDarts)
open Kepler.Graphs (Face fgraph)
open Kepler.Text.Reduction5 (Dart core quotientList)

/-! ## §0 辅助 -/

/-- `x ∈ l ⇒ y ∈ replace x [y] l`（替换把 `y` 插入首现位置）。 -/
private theorem t10b_mem_replace_insert {α : Type} [BEq α] [LawfulBEq α]
    {l : List α} {x y : α} (hx : x ∈ l) :
    y ∈ Kepler.Graphs.replace x [y] l := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons z zs ih =>
    rw [Kepler.Graphs.replace]
    by_cases hzx : z = x
    · rw [if_pos (beq_iff_eq.mpr hzx)]
      exact List.mem_append.mpr (Or.inl (List.mem_cons_self ..))
    · rw [if_neg (fun hc : (z == x) = true => hzx (beq_iff_eq.mp hc))]
      have hxzs : x ∈ zs := (List.mem_cons.mp hx).resolve_left (fun h => hzx h.symm)
      exact List.mem_cons.mpr (Or.inr (ih hxzs))

/-! ## §A `indexl_replace`（reduction3.hl:3899） -/

/-- HOL `indexl_replace`（reduction3.hl:3899）：
`(MEM y s ==> y = x) ∧ MEM x s ==> indexl y (replace x [y] s) = indexl x s`。 -/
theorem t10b_indexl_replace {α : Type} [BEq α] [LawfulBEq α]
    {s : List α} {x y : α} (hy : y ∈ s → y = x) (hx : x ∈ s) :
    (Kepler.Graphs.replace x [y] s).idxOf y = s.idxOf x := by
  induction s with
  | nil => exact absurd hx List.not_mem_nil
  | cons z zs ih =>
    rw [Kepler.Graphs.replace]
    by_cases hzx : z = x
    · rw [if_pos (beq_iff_eq.mpr hzx)]
      rw [hzx, List.singleton_append, List.idxOf_cons_self, List.idxOf_cons_self]
    · rw [if_neg (fun hc : (z == x) = true => hzx (beq_iff_eq.mp hc))]
      have hzy : z ≠ y := by
        intro hzy
        exact hzx (by rw [hzy]; exact hy (List.mem_cons.mpr (Or.inl hzy.symm)))
      have hxzs : x ∈ zs := (List.mem_cons.mp hx).resolve_left (fun h => hzx h.symm)
      have hbzy : (z == y) = false := beq_eq_false_iff_ne.mpr hzy
      have hbzx : (z == x) = false := beq_eq_false_iff_ne.mpr hzx
      simp only [List.idxOf_cons, hbzy, hbzx]
      rw [ih (fun hm => hy (List.mem_cons_of_mem z hm)) hxzs]

/-! ## §B `not_uniq_replace`（reduction3.hl:3918） -/

/-- HOL `not_uniq_replace`（reduction3.hl:3918）：
`MEM x s ∧ MEM y s ∧ x ≠ y ==> ¬ uniq (replace x [y] s)`。 -/
theorem t10b_not_uniq_replace {α : Type} [BEq α] [LawfulBEq α]
    {s : List α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    ¬ (Kepler.Graphs.replace x [y] s).Nodup := by
  induction s with
  | nil => exact absurd hx List.not_mem_nil
  | cons z zs ih =>
    rw [Kepler.Graphs.replace]
    by_cases hzx : z = x
    · rw [if_pos (beq_iff_eq.mpr hzx)]
      intro hnd
      have hyz : y ≠ z := fun h => hxy (hzx.symm.trans h.symm)
      have hyzs : y ∈ zs := (List.mem_cons.mp hy).resolve_left hyz
      exact (List.nodup_cons.mp hnd).1 hyzs
    · rw [if_neg (fun hc : (z == x) = true => hzx (beq_iff_eq.mp hc))]
      intro hnd
      obtain ⟨hznot, hnd'⟩ := List.nodup_cons.mp hnd
      have hxzs : x ∈ zs := (List.mem_cons.mp hx).resolve_left (fun h => hzx h.symm)
      rcases List.mem_cons.mp hy with hyz | hyzs
      · exact hznot (hyz ▸ t10b_mem_replace_insert hxzs)
      · exact ih hxzs hyzs hnd'

/-! ## §C `indexl_uniq_replace`（reduction3.hl:3930） -/

/-- HOL `indexl_uniq_replace`（reduction3.hl:3930）：
`uniq (replace x [y] s) ∧ MEM x s ==> indexl y (replace x [y] s) = indexl x s`。 -/
theorem t10b_indexl_uniq_replace {α : Type} [BEq α] [LawfulBEq α]
    {s : List α} {x y : α} (hnd : (Kepler.Graphs.replace x [y] s).Nodup)
    (hx : x ∈ s) :
    (Kepler.Graphs.replace x [y] s).idxOf y = s.idxOf x := by
  refine t10b_indexl_replace ?_ hx
  intro hy
  by_cases hxy : y = x
  · exact hxy
  · exact absurd hnd (t10b_not_uniq_replace hx hy (fun h => hxy h.symm))

/-! ## §D `indexl_map_uniq`（reduction3.hl:3983） -/

/-- HOL `indexl_map_uniq`（reduction3.hl:3983）：
`MEM d ys ∧ uniq (MAP f ys) ==> indexl (f d) (MAP f ys) = indexl d ys`。
Aq8 注入性已由 `uniqImpInj` 换名在树。 -/
theorem t10b_indexl_map_uniq {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] {ys : List α} {d : α} {f : α → β}
    (hd : d ∈ ys) (hnd : (ys.map f).Nodup) :
    (ys.map f).idxOf (f d) = ys.idxOf d :=
  Kepler.Text.TameLp.la7_idxOf_map
    (fun u hu v hv huv => Kepler.Text.TameSpine.uniqImpInj hnd hu hv huv) hd

/-! ## §E `indexl_core`（reduction3.hl:3998） -/

/-- HOL `indexl_core`（reduction3.hl:3998）：
`MEM r N ∧ uniq (quotient_list L N) ==>
indexl (core L r) (quotient_list L N) = indexl r N`。 -/
theorem t10b_indexl_core (L : fgraph ℕ) {N : List (List Dart)}
    {r : List Dart} (hr : r ∈ N) (hnd : (quotientList L N).Nodup) :
    (quotientList L N).idxOf (core L r) = N.idxOf r := by
  have h := t10b_indexl_map_uniq (ys := N) (d := r) (f := core L) hr
    (by rw [← Kepler.Text.MoreLemma2Island1.quotientListCore]; exact hnd)
  rw [← Kepler.Text.MoreLemma2Island1.quotientListCore] at h
  exact h

/-! ## §F `indexl_splitFace`（reduction3.hl:4010） -/

/-- HOL `indexl_splitFace`（reduction3.hl:4010）：
`uniq (fgraph g) ∧ uniq (fgraph g') ∧ MEM oldF (faces g) ==>
indexl (FST f2) (fgraph g') = indexl (FST oldF) (fgraph g)`
（`fgraph_splitFace` 在本树为 splitFace 定义级 rfl）。 -/
theorem t10b_indexl_splitFace (g : Kepler.Graphs.Graph) (ram₁ ram₂ : ℕ)
    (oldF : Face) (newVs : List ℕ)
    (hu : (fgraphOfGraph g).Nodup)
    (hu' : (fgraphOfGraph (Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.2).Nodup)
    (hm : oldF ∈ g.faces) :
    (fgraphOfGraph (Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.2).idxOf
        (Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.1.vertices
      = (fgraphOfGraph g).idxOf oldF.vertices := by
  have hfg' : fgraphOfGraph (Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.2
      = (Kepler.Graphs.replace oldF
          [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.1] g.faces
         ++ [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).1]).map
          (fun f => f.vertices) := rfl
  have hfg : fgraphOfGraph g = g.faces.map (fun f => f.vertices) := rfl
  have hfaces : g.faces.Nodup :=
    List.Nodup.of_map (fun f : Face => f.vertices) hu
  have hu'' : ((Kepler.Graphs.replace oldF
        [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.1] g.faces
      ++ [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).1]).map
        (fun f => f.vertices)).Nodup := hfg' ▸ hu'
  have hmem2 : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.1
      ∈ Kepler.Graphs.replace oldF
          [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.1] g.faces :=
    (t9_mem_replace g.faces
      (Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.1 oldF
      [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.1] hfaces hm).mpr
      (Or.inr (List.mem_singleton.mpr rfl))
  rw [hfg', hfg]
  rw [t10b_indexl_map_uniq (ys := Kepler.Graphs.replace oldF
        [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.1] g.faces
      ++ [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).1])
      (d := (Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.1)
      (f := fun f => f.vertices) (List.mem_append.mpr (Or.inl hmem2)) hu'']
  rw [List.idxOf_append, if_pos hmem2]
  rw [t10b_indexl_map_uniq hm hu]
  have hrep : (Kepler.Graphs.replace oldF
      [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF newVs).2.1] g.faces).Nodup :=
    (List.nodup_append.mp (List.Nodup.of_map (fun f : Face => f.vertices) hu'')).1
  exact t10b_indexl_uniq_replace hrep hm

/-! ## §G `sizel_3_concl`（reduction3.hl:846） -/

/-- HOL `sizel_3_concl`（reduction3.hl:846）：
`good_list L ∧ is_restricted (hypermap_of_list L) ∧ marked_list L N r x
==> 3 <= sizel (find_face L x)`。 -/
theorem t10b_sizel_3_concl (L : fgraph ℕ) (hL : GoodList L)
    (N : List (List Dart)) (r : List Dart) (x : Dart)
    (hir : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) :
    3 ≤ (findFaceDarts L x).length := by
  have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hf : findFaceDarts L x ∈ Kepler.Text.TameSpine.listOfFaces L :=
    Kepler.Text.TameSpine.memFindFace L hx
  exact Kepler.Text.TameSpine.isRestrictedSizeFace L hL hir hf

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t10b_indexl_replace
#print axioms Kepler.Text.Reduction3.t10b_not_uniq_replace
#print axioms Kepler.Text.Reduction3.t10b_indexl_uniq_replace
#print axioms Kepler.Text.Reduction3.t10b_indexl_map_uniq
#print axioms Kepler.Text.Reduction3.t10b_indexl_core
#print axioms Kepler.Text.Reduction3.t10b_indexl_splitFace
#print axioms Kepler.Text.Reduction3.t10b_sizel_3_concl
