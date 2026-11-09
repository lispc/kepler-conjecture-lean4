/-
  Kepler.Text.Reduction3Thm9B — J 战役 T9B 批（链 3 首批）。

  ┌─ 载体裁决（编排者 2026-11-09 批准）───────────────────────────
  │ `good_faces_v3` 载体 = `Kepler.Text.TameCorrList.GoodFacesV3`
  │ + 同文件 `facesAtV2`/`verticesSet2` 镜像。
  │ DIFFERS 记档：`Kepler.Text.TameCorrList.GoodFacesV3` 与
  │ `Kepler.Assembly.GoodFacesV3`（Assembly.lean:2271）**同体逐字**
  │ （均 `∀ v ∈ vertices_set2, (facesAt_v2 g v).Perm (g.facesAt v)`），
  │ 镜像用途仅为避开 Assembly 伞 import；语义同项，非新定义。
  └────────────────────────────────────────────────────────────────

  ┌─ 件目 ────────────────────────────────────────────────────────
  │   mem_flatten_facelistat :3323 → t9b_mem_flatten_facelistat ✅
  │ 其余 4 件本轮 BLOCKED（依赖两件未落大件，见文件尾 BLOCKED 清单）：
  │   mem_faceListAt_lemma :3148（语句 ~35 前提，HOL 证体 ~170 行）
  │   splitFace_props      :3339（~20 前提/~20 结论，HOL 证体 ~110 行）
  │   all_uniq_faceListAt  :3452（依赖上两件）
  │   mem_faceListAt       :3489（依赖 mem_faceListAt_lemma + splitFace_props）
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm12C
import Kepler.Text.TameCorrList

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph)

/-! ## §A `mem_flatten_facelistat`（reduction3.hl:3323） -/

/-- HOL `mem_flatten_facelistat`（reduction3.hl:3323）：
`countVertices g = sizel (faceListAt g) ∧ good_faces_v3 g ∧
MEM f (flatten (faceListAt g)) ==> MEM f (faces g)`。
index 路径：`f ∈ faceListAt[i]`（i < length = countVertices）→
`i ∈ vertices_set2 g` → `good_faces_v3` 给 `facesAt_v2 g i ≡ facesAt g i`
的 Perm → `facesAt g i` 成员 → filter 回 `faces g`。 -/
theorem t9b_mem_flatten_facelistat (g : Graph) (f : Face)
    (hc : g.countVertices = g.faceListAt.length)
    (hg : Kepler.Text.TameCorrList.GoodFacesV3 g)
    (hm : f ∈ g.faceListAt.flatten) :
    f ∈ g.faces := by
  obtain ⟨l, hl, hfl⟩ := List.mem_flatten.mp hm
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hl
  have hiC : i < g.countVertices := by rw [hc]; exact hi
  have hivs : i ∈ Kepler.Text.TameCorrList.verticesSet2 g := by
    show i ∈ g.vertices
    exact List.mem_range.mpr hiC
  have hperm : (Kepler.Text.TameCorrList.facesAtV2 g i).Perm (g.facesAt i) :=
    hg i hivs
  have hfa : g.facesAt i = g.faceListAt[i]'hi := by
    simp only [Kepler.Graphs.Graph.facesAt, List.getD_eq_getElem (hn := hi)]
  have hmem_i : f ∈ g.facesAt i := by
    rw [hfa]
    exact hfl
  have hmem_v2 : f ∈ Kepler.Text.TameCorrList.facesAtV2 g i :=
    hperm.mem_iff.mpr hmem_i
  exact (List.mem_filter.mp hmem_v2).1

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t9b_mem_flatten_facelistat

/- ── BLOCKED 清单（本轮未做，依赖/规模；无 J2）─────────────────────
   splitFace_props :3339 —— 依赖：t9b_mem_flatten_facelistat✓、
     betwnCases/betwnMem（TameList3）、Reduction4.betwnDisjoint✓、
     fgraph/verticesSet2/elementsOfList 载体展开、split_face/rev/rcons 推理。
     估 220–300 Lean 行。缺 `mem_faces_fgraph`（树内零命中，可 ~5 行补）。
   mem_faceListAt_lemma :3148 —— 依赖：splitFace 四次 replacefacesAt、
     t8b_size_replacefacesAt✓、t8_el_replacefacesAt✓、t8b_replace_perm_eq✓、
     t9_mem_replace3✓、t9_replace_filter3✓、TameCorrList.GoodFacesV3。
     估 250–350 Lean 行（语句 ~35 前提）。
   all_uniq_faceListAt :3452 —— 依赖 splitFace_props + t8b_all_uniq_faceListAt_lemma✓；估 40 行。
   mem_faceListAt :3489 —— 依赖 mem_faceListAt_lemma + splitFace_props；估 40 行。
   建议：拆 T9C（splitFace_props，单件专批）+ T9D（mem_faceListAt_lemma，
   单件专批），之后 all_uniq_faceListAt/mem_faceListAt 一锅收。
────────────────────────────────────────────────────────────────── -/
