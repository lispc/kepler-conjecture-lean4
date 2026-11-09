/-
  Kepler.Text.Reduction3Thm9C2 — J 战役 T9C2 批：`splitFace_props` 本体
  （HOL `reduction3.hl:3339`，证体 ~110 行）收口。

  ┌─ 说明（前车道 jcajydu-j3def §28.3 块计划 A–D）─────────────────
  │ 前车道已落支撑层 `Reduction3Thm9C.lean`（5 件，`faaac9f0`）：
  │   t9c_splitFace_fst_vertices / _snd_vertices / _faces /
  │   _faceListAt_length / t9c_mem_fgraph_of_mem_face。
  │ 本件按 §28.3 的块序收口本体：
  │   块 A｜graph/计数侧      → t9c2_vertices_iff_fgraph（独立件）
  │                              + 结论 ①②③
  │   块 B｜f1/f2 顶点成分    → 结论 ④⑤⑥⑦⑧⑨⑰
  │   块 C｜互斥/边界          → 结论 ⑩⑪⑫⑬⑭⑮
  │   块 D｜f1 ≠ f2（getLast?）→ 结论 ⑯
  └────────────────────────────────────────────────────────────────

  ┌─ 载体（零新定义；只 import 已落库支撑层）─────────────────────
  │ `GoodFacesV3` / `verticesSet2` / `VerticesSet2Eq`（TameCorrList 镜像）
  │ `t9b_mem_flatten_facelistat` / `betwnMem` / `betwnDisjoint` /
  │ `between_not_r1` / `between_not_r2`。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm9C
import Kepler.Text.Reduction3Thm8B

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph between Vertex)

/-! ## §0 两件顶点表成员刻画（定分叉：把 `++` 重结合歧义钉成右结合析取）

`List.mem_append` 的 `mp` 在所有定义相等的重结合处任取 split 位点，直接
`rcases` 分支顺序不可控。先把整条 `splitFace` 顶点表成员写成**固定顺序**的
四元析取，用例处 `mp` 后分支顺序即语句顺序。 -/

/-- `splitFace` 第一面顶点表的成员刻画（顺序：news / ram₁ / vs₁ / ram₂）。 -/
private theorem t9c2_mem_f1v {s news : List ℕ} {ram₁ ram₂ j : ℕ} :
    (j ∈ news.reverse ++ ([ram₁] ++ between s ram₁ ram₂ ++ [ram₂]))
      ↔ (j ∈ news ∨ j = ram₁ ∨ j ∈ between s ram₁ ram₂ ∨ j = ram₂) := by
  simp only [List.singleton_append, List.mem_append, List.mem_cons, List.mem_reverse,
    List.not_mem_nil]
  tauto

/-- `splitFace` 第二面顶点表的成员刻画（顺序：ram₂ / vs₂ / ram₁ / news）。 -/
private theorem t9c2_mem_f2v {s news : List ℕ} {ram₁ ram2 j : ℕ} :
    (j ∈ [ram2] ++ between s ram2 ram₁ ++ [ram₁] ++ news)
      ↔ (j = ram2 ∨ j ∈ between s ram2 ram₁ ∨ j = ram₁ ∨ j ∈ news) := by
  simp only [List.singleton_append, List.mem_append, List.mem_cons, List.not_mem_nil]
  tauto

/-! ## §A graph/计数侧（独立件：`i < len ↔ i ∈ flatten (fgraph g)`）

HOL 证体用 `vertices_set2 g = elements_of_list (fgraph g)` 一条 MESON；
Lean 侧把链拆成 `vertices_set2` → `vertices = range countVertices` → `countVertices = len`
→ `elementsOfList = flatten.eraseDups` → `flatten`。全程零 splitFace 依赖，单独成件。 -/

/-- HOL `splitFace_props` 结论①（`reduction3.hl:3362`），splitFace 无关的纯图侧件：
`countVertices g = |faceListAt g| ∧ vertices_set2 g = elements_of_list (fgraph g)`
⇒ `i < |faceListAt g| ↔ i ∈ flatten (fgraph g)`。 -/
theorem t9c2_vertices_iff_fgraph {g : Graph}
    (hc : g.countVertices = g.faceListAt.length)
    (hvs : Kepler.Text.TameCorrList.VerticesSet2Eq g) :
    ∀ j, j < g.faceListAt.length ↔ j ∈ g.fgraph.flatten := by
  intro j
  have h1 : j ∈ Kepler.Text.TameCorrList.verticesSet2 g ↔ j < g.faceListAt.length := by
    show j ∈ g.vertices ↔ j < g.faceListAt.length
    rw [Kepler.Graphs.Graph.vertices, List.mem_range, hc]
  have h2 : (j ∈ Kepler.Text.TameCorrList.verticesSet2 g) ↔
      j ∈ Kepler.Text.TameLp.elementsOfList g.fgraph := by
    rw [hvs]
  have h3 : (j ∈ Kepler.Text.TameLp.elementsOfList g.fgraph) ↔ j ∈ g.fgraph.flatten := by
    simp only [Kepler.Text.TameLp.elementsOfList, Kepler.Text.TameLp.listOfElements,
      List.mem_eraseDups, Set.mem_setOf_eq]
  exact h1.symm.trans (h2.trans h3)

/-! ## §B `splitFace_props` 本体（reduction3.hl:3339）

语句形态与 `t8b_all_uniq_faceListAt_lemma` 同款：`let s := splitFace …` 起手，
`dsimp only` 把 `f1`/`f2`/`g'` 落回 `splitFace` 投影，前提/结论逐条对应 HOL
（`FST f` ↦ `f.vertices`，`MEM` ↦ `∈`，`sizel` ↦ `List.length`，
`flatten (faceListAt g)` ↦ `g.faceListAt.flatten`）。 -/

/-- HOL `splitFace_props`（reduction3.hl:3339）。17 条结论与 HOL 逐槽同序。 -/
theorem t9c2_splitFace_props (g : Graph) (ram₁ ram₂ : Vertex) (oldF : Face)
    (news vs₁ vs₂ : List Vertex) :
    (let s := Kepler.Graphs.splitFace g ram₁ ram₂ oldF news
     let f₁ := s.1
     let f₂ := s.2.1
     Kepler.Text.TameCorrList.GoodFacesV3 g →
     g.countVertices = g.faceListAt.length →
     Kepler.Text.TameCorrList.VerticesSet2Eq g →
     oldF ∈ g.faces →
     f₁ ∉ g.faces →
     f₂ ∉ g.faces →
     oldF.vertices.Nodup →
     g.faces.Nodup →
     ram₁ ∈ oldF.vertices →
     ram₂ ∈ oldF.vertices →
     ram₁ ≠ ram₂ →
     between oldF.vertices ram₁ ram₂ = vs₁ →
     between oldF.vertices ram₂ ram₁ = vs₂ →
     (∀ j, j ∈ news ↔ g.faceListAt.length ≤ j ∧ j < s.2.2.faceListAt.length) →
     (∀ j, j < g.faceListAt.length ↔ j ∈ g.fgraph.flatten) ∧
       f₁ ∉ g.faceListAt.flatten ∧
       f₂ ∉ g.faceListAt.flatten ∧
       (∀ j, j < g.faceListAt.length → j ∈ f₁.vertices → j ∈ oldF.vertices) ∧
       (∀ j, j < g.faceListAt.length → j ∈ f₂.vertices → j ∈ oldF.vertices) ∧
       ram₁ ∈ f₁.vertices ∧ ram₁ ∈ f₂.vertices ∧
       ram₂ ∈ f₁.vertices ∧ ram₂ ∈ f₂.vertices ∧
       (∀ j, j ∈ vs₂ → j ∈ f₂.vertices ∧ j ∉ f₁.vertices) ∧
       (∀ j, j ∈ vs₁ → j ∈ f₁.vertices ∧ j ∉ f₂.vertices) ∧
       ram₁ < g.faceListAt.length ∧
       ram₂ < g.faceListAt.length ∧
       f₁ ≠ f₂ ∧
       (∀ j, j ∈ vs₁ → j < g.faceListAt.length) ∧
       (∀ j, j ∈ vs₂ → j < g.faceListAt.length) ∧
       (∀ j, j ∈ news → j ∈ f₁.vertices ∧ j ∈ f₂.vertices)) := by
  dsimp only
  intro hgood hc hvs hF hnf1 hnf2 hndOld hndFaces hr1 hr2 hrne hvs1 hvs2 hnews
  -- 顶点表的两条定义级方程（支撑层 rfl 件）
  have hf1v : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices
      = news.reverse ++ ([ram₁] ++ between oldF.vertices ram₁ ram₂ ++ [ram₂]) :=
    t9c_splitFace_fst_vertices g ram₁ ram₂ oldF news
  have hf2v : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices
      = [ram₂] ++ between oldF.vertices ram₂ ram₁ ++ [ram₁] ++ news :=
    t9c_splitFace_snd_vertices g ram₁ ram₂ oldF news
  -- 块 A｜graph/计数侧
  have hA1 : ∀ j, j < g.faceListAt.length ↔ j ∈ g.fgraph.flatten :=
    t9c2_vertices_iff_fgraph hc hvs
  have hA2 : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 ∉ g.faceListAt.flatten := by
    intro hm
    exact hnf1 (t9b_mem_flatten_facelistat g _ hc hgood hm)
  have hA3 : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1 ∉ g.faceListAt.flatten := by
    intro hm
    exact hnf2 (t9b_mem_flatten_facelistat g _ hc hgood hm)
  -- 块 B｜f1/f2 顶点成分
  have hB1 : ∀ j, j < g.faceListAt.length →
      j ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices → j ∈ oldF.vertices := by
    intro j hj hmem
    rw [hf1v] at hmem
    rcases (t9c2_mem_f1v (s := oldF.vertices) (news := news) (ram₁ := ram₁)
      (ram₂ := ram₂) (j := j)).mp hmem with hm | hm | hm | hm
    · -- j ∈ news：hnews 下界与 j < len 矛盾
      exact absurd ((hnews j).mp hm).1 (Nat.not_le.mpr hj)
    · -- j = ram₁
      rw [hm]
      exact hr1
    · exact Kepler.Text.TameSpine.betwnMem hm
    · -- j = ram₂
      rw [hm]
      exact hr2
  have hB2 : ∀ j, j < g.faceListAt.length →
      j ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices → j ∈ oldF.vertices := by
    intro j hj hmem
    rw [hf2v] at hmem
    rcases (t9c2_mem_f2v (s := oldF.vertices) (news := news) (ram₁ := ram₁)
      (ram2 := ram₂) (j := j)).mp hmem with hm | hm | hm | hm
    · -- j = ram₂
      rw [hm]
      exact hr2
    · exact Kepler.Text.TameSpine.betwnMem hm
    · -- j = ram₁
      rw [hm]
      exact hr1
    · -- j ∈ news：hnews 下界与 j < len 矛盾
      exact absurd ((hnews j).mp hm).1 (Nat.not_le.mpr hj)
  have hB3 : ram₁ ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices := by
    rw [hf2v]
    simp
  have hB4 : ram₂ ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices := by
    rw [hf1v]
    simp
  have hB5 : ram₂ ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices := by
    rw [hf2v]
    simp
  have hB6 : ram₁ ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices := by
    rw [hf1v]
    simp
  -- 块 C｜互斥/边界
  have hC1 : ∀ j, j ∈ vs₂ →
      j ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices ∧
        j ∉ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices := by
    intro j hj
    have hjb : j ∈ between oldF.vertices ram₂ ram₁ := by rw [← hvs2] at hj; exact hj
    have hjold : j ∈ oldF.vertices := Kepler.Text.TameSpine.betwnMem hjb
    have hjlen : j < g.faceListAt.length :=
      (hA1 j).mpr (t9c_mem_fgraph_of_mem_face hF hjold)
    constructor
    · rw [hf2v]
      simp only [List.singleton_append, List.mem_append, List.mem_cons, List.mem_singleton]
      tauto
    · intro hmem
      rw [hf1v] at hmem
      rcases (t9c2_mem_f1v (s := oldF.vertices) (news := news) (ram₁ := ram₁)
        (ram₂ := ram₂) (j := j)).mp hmem with hm | hm | hm | hm
      · exact absurd ((hnews j).mp hm).1 (Nat.not_le.mpr hjlen)
      · rw [hm] at hjb
        exact Kepler.Graphs.between_not_r2 (ram₁ := ram₂) hndOld hjb
      · exact (Kepler.Text.Reduction4.betwnDisjoint hndOld hr2 hr1
          (fun h => hrne h.symm) hjb) hm
      · rw [hm] at hjb
        exact Kepler.Graphs.between_not_r1 (ram₁ := ram₂) (ram₂ := ram₁) hndOld hjb
  have hC2 : ∀ j, j ∈ vs₁ →
      j ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices ∧
        j ∉ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices := by
    intro j hj
    have hjb : j ∈ between oldF.vertices ram₁ ram₂ := by rw [← hvs1] at hj; exact hj
    have hjold : j ∈ oldF.vertices := Kepler.Text.TameSpine.betwnMem hjb
    have hjlen : j < g.faceListAt.length :=
      (hA1 j).mpr (t9c_mem_fgraph_of_mem_face hF hjold)
    constructor
    · rw [hf1v]
      simp only [List.singleton_append, List.mem_append, List.mem_cons, List.mem_singleton]
      tauto
    · intro hmem
      rw [hf2v] at hmem
      rcases (t9c2_mem_f2v (s := oldF.vertices) (news := news) (ram₁ := ram₁)
        (ram2 := ram₂) (j := j)).mp hmem with hm | hm | hm | hm
      · -- j = ram₂
        rw [hm] at hjb
        exact Kepler.Graphs.between_not_r2 hndOld hjb
      · exact (Kepler.Text.Reduction4.betwnDisjoint hndOld hr1 hr2 hrne hjb) hm
      · -- j = ram₁
        rw [hm] at hjb
        exact Kepler.Graphs.between_not_r1 hndOld hjb
      · exact absurd ((hnews j).mp hm).1 (Nat.not_le.mpr hjlen)
  have hC3 : ram₁ < g.faceListAt.length :=
    (hA1 ram₁).mpr (t9c_mem_fgraph_of_mem_face hF hr1)
  have hC4 : ram₂ < g.faceListAt.length :=
    (hA1 ram₂).mpr (t9c_mem_fgraph_of_mem_face hF hr2)
  have hC5 : ∀ j, j ∈ vs₁ → j < g.faceListAt.length := by
    intro j hj
    have hjb : j ∈ between oldF.vertices ram₁ ram₂ := by rw [← hvs1] at hj; exact hj
    exact (hA1 j).mpr (t9c_mem_fgraph_of_mem_face hF (Kepler.Text.TameSpine.betwnMem hjb))
  have hC6 : ∀ j, j ∈ vs₂ → j < g.faceListAt.length := by
    intro j hj
    have hjb : j ∈ between oldF.vertices ram₂ ram₁ := by rw [← hvs2] at hj; exact hj
    exact (hA1 j).mpr (t9c_mem_fgraph_of_mem_face hF (Kepler.Text.TameSpine.betwnMem hjb))
  -- 块 D｜f1 ≠ f2（末元论证：getLast? 三分支）
  have hD : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 ≠
      (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1 := by
    intro heq
    have hv : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices
        = (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices :=
      congrArg Face.vertices heq
    have h1 : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices.getLast?
        = some ram₂ := by
      rw [hf1v]
      simp [List.getLast?_append, List.getLast?_cons]
    have h2 : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices.getLast?
        = some ram₂ := by
      rw [← hv]
      exact h1
    rw [hf2v] at h2
    cases news with
    | nil =>
      have h2' : some ram₁ = some ram₂ := by
        simpa [List.getLast?_append, List.getLast?_cons, List.getLast?_concat] using h2
      exact hrne (Option.some.inj h2')
    | cons n ns =>
      have hmem : ram₂ ∈ (n :: ns) := by
        apply List.mem_of_getLast?
        rw [List.getLast?_cons]
        have h3 : ([ram₂] ++ between oldF.vertices ram₂ ram₁ ++ [ram₁] ++ (n :: ns)).getLast?
            = some (ns.getLast?.getD n) := by
          simp [List.getLast?_append, List.getLast?_cons]
        rw [h3] at h2
        exact h2
      exact absurd ((hnews ram₂).mp hmem).1 (Nat.not_le.mpr hC4)
  -- 块 B 收尾｜⑰ news 同属两面
  have hB7 : ∀ j, j ∈ news →
      j ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices ∧
        j ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices := by
    intro j hj
    constructor
    · rw [hf1v]
      exact List.mem_append.mpr (Or.inl (List.mem_reverse.mpr hj))
    · rw [hf2v]
      exact List.mem_append.mpr (Or.inr hj)
  exact ⟨hA1, hA2, hA3, hB1, hB2, hB6, hB3, hB4, hB5, hC1, hC2, hC3, hC4, hD,
    hC5, hC6, hB7⟩

/-! ## §C `all_uniq_faceListAt`（reduction3.hl:3452，依赖本件 §B + T8B 支撑件）

HOL 证体即「`split_face_props` 供给 `all_uniq_faceListAt_lemma` 的 10 条前提」；
Lean 侧逐槽对接：`all uniq (faceListAt g)` ↦ `∀ l ∈ g.faceListAt, l.Nodup`
（Assembly.AllUniq 同口径）。 -/

/-- HOL `all_uniq_faceListAt`（reduction3.hl:3452）。 -/
theorem t9c2_all_uniq_faceListAt (g : Graph) (ram₁ ram₂ : Vertex) (oldF : Face)
    (news : List Vertex) :
    (let s := Kepler.Graphs.splitFace g ram₁ ram₂ oldF news
     let f₁ := s.1
     let f₂ := s.2.1
     oldF.vertices.Nodup →
     ram₁ ∈ oldF.vertices →
     ram₂ ∈ oldF.vertices →
     ram₁ ≠ ram₂ →
     Kepler.Text.TameCorrList.GoodFacesV3 g →
     g.countVertices = g.faceListAt.length →
     Kepler.Text.TameCorrList.VerticesSet2Eq g →
     oldF ∈ g.faces →
     f₁ ∉ g.faces →
     f₂ ∉ g.faces →
     g.faces.Nodup →
     (∀ j, j ∈ news ↔ g.faceListAt.length ≤ j ∧ j < s.2.2.faceListAt.length) →
     (∀ l ∈ g.faceListAt, l.Nodup) →
     ∀ l ∈ s.2.2.faceListAt, l.Nodup) := by
  dsimp only
  intro hndOld hr1 hr2 hrne hgood hc hvs hF hnf1 hnf2 hndFaces hnews hall
  obtain ⟨-, hA2, hA3, -, -, -, -, -, -, -, -, hC3, hC4, hD, -, -, -⟩ :=
    (by
      have hprops := t9c2_splitFace_props g ram₁ ram₂ oldF news
      dsimp only at hprops
      exact hprops (vs₁ := between oldF.vertices ram₁ ram₂)
        (vs₂ := between oldF.vertices ram₂ ram₁) hgood hc hvs hF hnf1 hnf2 hndOld
        hndFaces hr1 hr2 hrne rfl rfl hnews)
  have h := t8b_all_uniq_faceListAt_lemma g ram₁ ram₂ oldF news
  dsimp only at h
  exact h hA2 hA3 hndOld hr1 hC3 hC4 hr2 hD hrne hall

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t9c2_vertices_iff_fgraph
#print axioms Kepler.Text.Reduction3.t9c2_splitFace_props
#print axioms Kepler.Text.Reduction3.t9c2_all_uniq_faceListAt
