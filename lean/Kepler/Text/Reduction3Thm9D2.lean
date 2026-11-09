/-
  Kepler.Text.Reduction3Thm9D2 — J 战役 T9 收尾之二：`mem_faceListAt`
  （HOL `reduction3.hl:3489`）。

  ┌─ 证法 ────────────────────────────────────────────────────────
  │ `i < len` 支：`t9d_mem_faceListAt_lemma` 右支（左支 `len ≤ i` 已排除）。
  │ `len ≤ i` 支：先把该支化成 `h = f1 ∨ h = f2`，再由 T9C2 ⑰
  │ （`i ∈ news ⇒ i ∈ f1/f2`）把 `facesAt_v2 g' i` 的过滤值算成 `f1/f2`
  │ 的成员；反方向用 `i ∈ faces g` + `vertices_set2 = elements_of_list`
  │ 逼出 `i < countVertices = len` 与 `len ≤ i` 矛盾。
  │ 语句形态 DIFFERS 同上件（显式 f1/f2/g' + `hsplit`）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm9D

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph between Vertex)

/-! ## §2 `mem_faceListAt`（reduction3.hl:3489）

HOL 证体两步：`i < len` 支直接由 `mem_faceListAt_lemma` 的右支给出；
`len ≤ i` 支先把该支化成 `h = f1 ∨ h = f2`，再用 T9C2 ⑰（`i ∈ news ⇒ i ∈ f1/f2`）
把 `facesAt_v2 g' i` 的过滤值算成 `[f1, f2]` 的成员 —— 反方向靠
`i ∈ faces g` + `vertices_set2 = elements_of_list` 逼出 `i < countVertices = len`
与 `len ≤ i` 矛盾。 -/

/-- HOL `mem_faceListAt`（reduction3.hl:3489）。前提 13 条与 HOL 逐槽同序。 -/
theorem t9d_mem_faceListAt (g : Graph) (ram₁ ram₂ : Vertex) (oldF : Face)
    (news : List Vertex) (h : Face) (i : Vertex) (f₁ f₂ : Face) (g' : Graph)
    (hsplit : Kepler.Graphs.splitFace g ram₁ ram₂ oldF news = (f₁, f₂, g'))
    (hgood : Kepler.Text.TameCorrList.GoodFacesV3 g)
    (hc : g.countVertices = g.faceListAt.length)
    (hvs : Kepler.Text.TameCorrList.VerticesSet2Eq g)
    (hnf1 : f₁ ∉ g.faces)
    (hnf2 : f₂ ∉ g.faces)
    (hnews : ∀ j, j ∈ news ↔ g.faceListAt.length ≤ j ∧ j < g'.faceListAt.length)
    (hF : oldF ∈ g.faces)
    (hndOld : oldF.vertices.Nodup)
    (hndFaces : g.faces.Nodup)
    (hr1 : ram₁ ∈ oldF.vertices)
    (hr2 : ram₂ ∈ oldF.vertices)
    (hrne : ram₁ ≠ ram₂)
    (hi_lt : i < g'.faceListAt.length) :
    (h ∈ g'.facesAt i ↔ h ∈ Kepler.Text.TameCorrList.facesAtV2 g' i) := by
  have hf1' : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 = f₁ :=
    congrArg Prod.fst hsplit
  have hf2' : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1 = f₂ :=
    congrArg (fun p => p.2.1) hsplit
  have hg'' : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2 = g' :=
    congrArg (fun p => p.2.2) hsplit
  -- 前提换算到投影形
  have hnf1' : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 ∉ g.faces := by
    rw [hf1']; exact hnf1
  have hnf2' : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1 ∉ g.faces := by
    rw [hf2']; exact hnf2
  have hnews' : ∀ j, j ∈ news ↔ g.faceListAt.length ≤ j ∧
      j < (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.faceListAt.length := by
    intro j; rw [hg'']; exact hnews j
  -- T9C2 `splitFace_props` 的 ④–⑰
  have hprops := by
    have hp := t9c2_splitFace_props g ram₁ ram₂ oldF news
    dsimp only at hp
    exact hp (vs₁ := between oldF.vertices ram₁ ram₂) (vs₂ := between oldF.vertices ram₂ ram₁)
      hgood hc hvs hF hnf1' hnf2' hndOld hndFaces hr1 hr2 hrne rfl rfl hnews'
  obtain ⟨-, -, -, h4, h5, hr1f1, hr1f2, hr2f1, hr2f2, hvs2c, hvs1c,
    hr1len, hr2len, hfne, hvs1len, hvs2len, hB7⟩ := hprops
  -- `mem_faceListAt_lemma` 的投影形现成实例
  have hlem : ∀ (j : Vertex) (hh : Face),
      j < (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.faceListAt.length →
      (hh ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.facesAt j ↔
        (g.faceListAt.length ≤ j ∧
            (hh = (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 ∨
             hh = (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1)) ∨
        (j < g.faceListAt.length ∧
          hh ∈ Kepler.Text.TameCorrList.facesAtV2
            (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2 j)) := by
    intro j hh hj
    exact t9d_mem_faceListAt_lemma g ram₁ ram₂ oldF news _ _ hh j _ _ _ rfl hgood hc h4 h5
      hr1f1 hr1f2 hr2f1 hr2f2 hvs2c hvs1c hF hndOld hndFaces hr1 hr1len hr2len hr2
      hfne hrne rfl rfl hvs1len hvs2len hj
  -- `i < |faceListAt g'|` 的投影形
  have hi_lt' : i < (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.faceListAt.length := by
    rw [hg'']; exact hi_lt
  -- 目标换算到投影形
  rw [← hg'']
  by_cases hbig : g.faceListAt.length ≤ i
  · -- ── i ≥ len：`facesAt g' i` 与 `facesAt_v2 g' i` 都只剩 `f1/f2` ──
    have hi_news : i ∈ news := (hnews' i).mpr ⟨hbig, by rwa [hg'']⟩
    have hboth := hB7 i hi_news
    -- 左端：lemma 给出 `h = f1 ∨ h = f2`
    have hleft : h ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.facesAt i ↔
        (h = (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 ∨
         h = (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1) := by
      rw [hlem i h hi_lt']
      constructor
      · rintro (⟨-, hh⟩ | ⟨hlt, -⟩)
        · exact hh
        · exact absurd hlt (Nat.not_lt.mpr hbig)
      · rintro hh
        exact Or.inl ⟨hbig, hh⟩
    -- 右端：过滤值恰是 `f1/f2`
    have hright : h ∈ Kepler.Text.TameCorrList.facesAtV2
        (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2 i ↔
        (h = (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 ∨
         h = (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1) := by
      have hfaces : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.faces
          = Kepler.Graphs.replace oldF [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1]
              g.faces
            ++ [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1] :=
        t9c_splitFace_faces g ram₁ ram₂ oldF news
      have hP1 : (fun f : Face => decide (i ∈ f.vertices))
          (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 = true := by
        simp [show decide (i ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices)
            = true from by simp [hboth.1]]
      have hP2 : (fun f : Face => decide (i ∈ f.vertices))
          (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1 = true := by
        simp [show decide (i ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices)
            = true from by simp [hboth.2]]
      show h ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.faces.filter
          (fun f => decide (i ∈ f.vertices)) ↔ _
      rw [hfaces, List.filter_append, List.mem_append, List.mem_filter, List.mem_filter]
      constructor
      · rintro (⟨hm, hPh⟩ | ⟨hm, hPh⟩)
        · -- 老面里且含 i：逼出 i < len
          rw [t9_mem_replace3 g.faces h oldF
            [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1] hndFaces hF] at hm
          rcases hm with hm | ⟨hmf, -⟩
          · right
            exact List.mem_singleton.mp hm
          · have hlt : i < g.faceListAt.length :=
              ((t9c2_vertices_iff_fgraph hc hvs) i).mpr
                (t9c_mem_fgraph_of_mem_face hmf (of_decide_eq_true hPh))
            exact absurd (Nat.lt_of_lt_of_le hlt hbig) (Nat.lt_irrefl i)
        · left
          exact List.mem_singleton.mp hm
      · rintro (hh | hh)
        · -- h = f1：落在尾部追加段
          subst hh
          right
          exact ⟨List.mem_singleton.mpr rfl, hP1⟩
        · -- h = f2：落在 replace 段
          subst hh
          left
          exact ⟨by
            rw [t9_mem_replace3 g.faces _ oldF
              [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1] hndFaces hF]
            exact Or.inl (List.mem_singleton.mpr rfl), hP2⟩
    rw [hleft, hright]
  · -- ── i < len：`mem_faceListAt_lemma` 左支已排除 ──
    have hilt : i < g.faceListAt.length := Nat.lt_of_not_le hbig
    have hstep : (h ∈ (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.facesAt i ↔
        (g.faceListAt.length ≤ i ∧
            (h = (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 ∨
             h = (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1)) ∨
        (i < g.faceListAt.length ∧
          h ∈ Kepler.Text.TameCorrList.facesAtV2
            (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2 i)) :=
      hlem i h hi_lt'
    rw [hstep]
    constructor
    · rintro (⟨hle, -⟩ | ⟨-, hmem⟩)
      · exact absurd hle hbig
      · exact hmem
    · intro hmem
      exact Or.inr ⟨hilt, hmem⟩

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t9d_mem_faceListAt
