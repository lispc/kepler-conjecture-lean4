/-
  Kepler.Text.Reduction3Thm9D — J 战役 T9 收尾之一：`mem_faceListAt_lemma`
  （HOL `reduction3.hl:3148`，证体 ~170 行）。

  ┌─ 证法（按 i 的落区分解 `facesAt g' i` vs `facesAt_v2 g' i`）─────
  │  `faceListAt g'` = 四层 `replacefacesAt`（vs1/vs2/[ram1]/[ram2]）
  │  之后接 `replicate news.length [f1,f2]`。对 `i < |faceListAt g'|`：
  │   R1 `len ≤ i`：尾部新顶点段，两边都恰为 `[f1,f2]`；
  │   R2 `i < len ∧ i ∉ oldF.vertices`：四层替换全不触发；
  │   R3 `i = ram1` → 只被 `replacefacesAt [ram1]` 换成 `[f2,f1]`；
  │   R4 `i = ram2` → 只被 `replacefacesAt [ram2]` 换成 `[f1,f2]`；
  │   R5 `i ∈ vs1` → 只被 `replacefacesAt vs1` 换成 `[f1]`；
  │   R6 `i ∈ vs2` → 只被 `replacefacesAt vs2` 换成 `[f2]`。
  │  落区完备性用 `betwnCases`；每支用 `t9_mem_replace` 把
  │  `replace oldF N (facesAtV2 g i)` 折成 `D ∨ h ∈ N`（D = 删 oldF 的过滤表）。
  │
  │ 语句形态 DIFFERS（记档）：HOL `let (f1,f2,g') = splitFace …` 就地展开；
  │ 本件把 f1/f2/g' 提为显式参数 + 假设 `hsplit : splitFace … = (f1,f2,g')`
  │ （`let` 展开的标准形，前提/结论逐条不变；下游传 `rfl` 实例化）。
  │ 这样避免 `let`-形语句在最终 defeq 检验里对 `splitFace` 巨型定义做 whnf。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm9C2

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph between Vertex)

/-! ## §0 小助手 -/

/-- `replacefacesAt` 单层：`k < |F|` 且 `k ∉ ns` 时第 k 项不变。 -/
private theorem t9d_replacefacesAt_getD_notin (oldF : Face) (ns : List ℕ) (nl : List Face)
    (F : List (List Face)) (k : ℕ) (hnd : ns.Nodup) (hk : k < F.length) (hnot : k ∉ ns) :
    (Kepler.Graphs.replacefacesAt ns oldF nl F).getD k [] = F.getD k [] := by
  rw [t8_el_replacefacesAt ns oldF nl F k [] hnd hk]
  simp [hnot]

/-- `replacefacesAt` 单层：`k < |F|` 且 `k ∈ ns` 时第 k 项被替换。 -/
private theorem t9d_replacefacesAt_getD_in (oldF : Face) (ns : List ℕ) (nl : List Face)
    (F : List (List Face)) (k : ℕ) (hnd : ns.Nodup) (hk : k < F.length) (hin : k ∈ ns) :
    (Kepler.Graphs.replacefacesAt ns oldF nl F).getD k []
      = Kepler.Graphs.replace oldF nl (F.getD k []) := by
  rw [t8_el_replacefacesAt ns oldF nl F k [] hnd hk]
  simp [hin]

/-- `P old = false` 且 `news` 全不满足 `P` 时：`replace` 后过滤 = 原过滤。
（`t9_replace_filter3` 只覆盖 `P old = true` 的情形。） -/
private theorem t9d_filter_replace_of_false {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (P : α → Bool) (news : List α) (u old : α)
    (hnd : xs.Nodup) (hold : old ∈ xs) (hPold : P old = false)
    (hPnews : ∀ y, y ∈ news → P y = false) :
    (u ∈ (Kepler.Graphs.replace old news xs).filter P ↔ u ∈ xs.filter P) := by
  rw [List.mem_filter, List.mem_filter]
  constructor
  · rintro ⟨hm, hP⟩
    rw [t9_mem_replace3 xs u old news hnd hold] at hm
    rcases hm with hm | ⟨hm, -⟩
    · rw [hPnews u hm] at hP
      exact absurd hP (by simp)
    · exact ⟨hm, hP⟩
  · rintro ⟨hm, hP⟩
    refine ⟨?_, hP⟩
    rw [t9_mem_replace3 xs u old news hnd hold]
    refine Or.inr ⟨hm, ?_⟩
    intro hc
    rw [hc, hPold] at hP
    exact absurd hP (by simp)

/-! ## §1 `mem_faceListAt_lemma`（reduction3.hl:3148） -/

/-- HOL `mem_faceListAt_lemma`（reduction3.hl:3148）。前提 23 条与 HOL 逐槽同序
（HOL 源里两条 `~MEM f1/f2 (flatten (faceListAt g))` 被注释掉，故不入册）。 -/
theorem t9d_mem_faceListAt_lemma (g : Graph) (ram₁ ram₂ : Vertex) (oldF : Face)
    (news vs₁ vs₂ : List Vertex) (h : Face) (i : Vertex) (f₁ f₂ : Face) (g' : Graph)
    (hsplit : Kepler.Graphs.splitFace g ram₁ ram₂ oldF news = (f₁, f₂, g'))
    (hgood : Kepler.Text.TameCorrList.GoodFacesV3 g)
    (hc : g.countVertices = g.faceListAt.length)
    (h4 : ∀ k, k < g.faceListAt.length → k ∈ f₁.vertices → k ∈ oldF.vertices)
    (h5 : ∀ k, k < g.faceListAt.length → k ∈ f₂.vertices → k ∈ oldF.vertices)
    (hr1f1 : ram₁ ∈ f₁.vertices) (hr1f2 : ram₁ ∈ f₂.vertices)
    (hr2f1 : ram₂ ∈ f₁.vertices) (hr2f2 : ram₂ ∈ f₂.vertices)
    (hvs2c : ∀ k, k ∈ vs₂ → k ∈ f₂.vertices ∧ k ∉ f₁.vertices)
    (hvs1c : ∀ k, k ∈ vs₁ → k ∈ f₁.vertices ∧ k ∉ f₂.vertices)
    (hF : oldF ∈ g.faces)
    (hndOld : oldF.vertices.Nodup)
    (hndFaces : g.faces.Nodup)
    (hr1 : ram₁ ∈ oldF.vertices)
    (hr1len : ram₁ < g.faceListAt.length)
    (hr2len : ram₂ < g.faceListAt.length)
    (hr2 : ram₂ ∈ oldF.vertices)
    (hfne : f₁ ≠ f₂)
    (hrne : ram₁ ≠ ram₂)
    (hvs1 : between oldF.vertices ram₁ ram₂ = vs₁)
    (hvs2 : between oldF.vertices ram₂ ram₁ = vs₂)
    (hvs1len : ∀ k, k ∈ vs₁ → k < g.faceListAt.length)
    (hvs2len : ∀ k, k ∈ vs₂ → k < g.faceListAt.length)
    (hi_lt : i < g'.faceListAt.length) :
    (h ∈ g'.facesAt i ↔
      (g.faceListAt.length ≤ i ∧ (h = f₁ ∨ h = f₂)) ∨
      (i < g.faceListAt.length ∧ h ∈ Kepler.Text.TameCorrList.facesAtV2 g' i)) := by
  -- splitFace 三元组投影与 f₁/f₂/g' 的等式（供 hFL/hfaces 展开用）
  have hf1' : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 = f₁ :=
    congrArg Prod.fst hsplit
  have hf2' : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1 = f₂ :=
    congrArg (fun p => p.2.1) hsplit
  have hg'' : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2 = g' :=
    congrArg (fun p => p.2.2) hsplit
  set Fs0 : List (List Face) := g.faceListAt with hFs0
  set Fs1 : List (List Face) :=
    Kepler.Graphs.replacefacesAt (between oldF.vertices ram₁ ram₂) oldF [f₁] Fs0 with hFs1
  set Fs2 : List (List Face) :=
    Kepler.Graphs.replacefacesAt (between oldF.vertices ram₂ ram₁) oldF [f₂] Fs1 with hFs2
  set Fs3 : List (List Face) :=
    Kepler.Graphs.replacefacesAt [ram₁] oldF [f₂, f₁] Fs2 with hFs3
  set Fs4 : List (List Face) :=
    Kepler.Graphs.replacefacesAt [ram₂] oldF [f₁, f₂] Fs3 with hFs4
  have hL1 : Fs1.length = Fs0.length := by rw [hFs1]; exact t8_size_mapAt _ _ _
  have hL2 : Fs2.length = Fs1.length := by rw [hFs2]; exact t8_size_mapAt _ _ _
  have hL3 : Fs3.length = Fs2.length := by rw [hFs3]; exact t8_size_mapAt _ _ _
  have hL4 : Fs4.length = Fs3.length := by rw [hFs4]; exact t8_size_mapAt _ _ _
  have hFs4len : Fs4.length = g.faceListAt.length := by rw [hL4, hL3, hL2, hL1, hFs0]
  -- `faceListAt g'` 的四层 + 尾部 replicate 分解（splitFace 定义级）
  have hFL : g'.faceListAt = Fs4 ++ List.replicate news.length [f₁, f₂] := by
    rw [← hg'', hFs4, hFs3, hFs2, hFs1, hFs0, ← hf1', ← hf2']
    rfl
  -- `faces g'` 的分解（支撑层件）
  have hfaces : g'.faces = Kepler.Graphs.replace oldF [f₂] g.faces ++ [f₁] := by
    rw [← hg'', t9c_splitFace_faces g ram₁ ram₂ oldF news, ← hf1', ← hf2']
  -- `i < len` 时 `faceListAt g` 第 i 项 = `facesAt g i`，且与 `facesAt_v2 g i` 同 Perm
  have hperm : ∀ k, k < g.faceListAt.length →
      (Kepler.Text.TameCorrList.facesAtV2 g k).Perm (Fs0.getD k []) := by
    intro k hk
    have hivs : k ∈ Kepler.Text.TameCorrList.verticesSet2 g := by
      show k ∈ g.vertices
      rw [Kepler.Graphs.Graph.vertices, List.mem_range, hc]
      exact hk
    exact hgood k hivs
  -- 主分拆：R1（len ≤ i）与 R2–R6（i < len）
  by_cases hbig : g.faceListAt.length ≤ i
  · -- ── R1：新顶点段 ──
    have hget : g'.facesAt i = [f₁, f₂] := by
      show g'.faceListAt.getD i [] = [f₁, f₂]
      rw [hFL, List.getD_append_right Fs4 _ [] i (by rw [hFs4len]; exact hbig)]
      rw [List.getD_replicate]
      -- i - Fs4.length < news.length
      have h1 : i < Fs4.length + news.length := by
        rw [hFL] at hi_lt
        simpa only [List.length_append, List.length_replicate] using hi_lt
      have h2 : Fs4.length ≤ i := by rw [hFs4len]; exact hbig
      exact Nat.sub_lt_left_of_lt_add h2 h1
    rw [hget]
    constructor
    · intro hmem
      refine Or.inl ⟨hbig, ?_⟩
      simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hmem
    · intro hmem
      rcases hmem with ⟨-, hh⟩ | ⟨hlt, -⟩
      · simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hh
      · exact absurd hlt (Nat.not_lt.mpr hbig)
  · -- ── i < len：R2–R6 ──
    have hilt : i < g.faceListAt.length := Nat.lt_of_not_le hbig
    have hlt1 : i < Fs1.length := by rw [hL1, hFs0]; exact hilt
    have hlt2 : i < Fs2.length := by rw [hL2, hL1, hFs0]; exact hilt
    have hlt3 : i < Fs3.length := by rw [hL3, hL2, hL1, hFs0]; exact hilt
    -- `facesAt g' i` 的取值入口（尾段不参与）
    have hLHSget : g'.facesAt i = Fs4.getD i [] := by
      show g'.faceListAt.getD i [] = Fs4.getD i []
      rw [hFL]
      exact List.getD_append Fs4 _ [] i (by rw [hFs4len]; exact hilt)
    -- `vs` 与 `between` 的成员桥
    have hmemv1 : ∀ k, k ∈ vs₁ ↔ k ∈ between oldF.vertices ram₁ ram₂ := by
      intro k; rw [hvs1]
    have hmemv2 : ∀ k, k ∈ vs₂ ↔ k ∈ between oldF.vertices ram₂ ram₁ := by
      intro k; rw [hvs2]
    -- 目标右侧（`len ≤ i` 已排除）等价于 `h ∈ facesAtV2 g' i`
    have hsimp : ((g.faceListAt.length ≤ i ∧ (h = f₁ ∨ h = f₂)) ∨
        (i < g.faceListAt.length ∧ h ∈ Kepler.Text.TameCorrList.facesAtV2 g' i))
        ↔ h ∈ Kepler.Text.TameCorrList.facesAtV2 g' i := by
      constructor
      · intro hh
        rcases hh with ⟨hle, -⟩ | ⟨-, hmem⟩
        · exact absurd hle hbig
        · exact hmem
      · intro hmem
        exact Or.inr ⟨hilt, hmem⟩
    rw [hsimp]
    -- 右侧展开（i ∈ oldF.vertices）：`facesAtV2 g' i` = D ∨ (i∈f2 ∧ h=f2) ∨ (i∈f1 ∧ h=f1)
    have hRHStrue : i ∈ oldF.vertices →
        ∀ h', h' ∈ Kepler.Text.TameCorrList.facesAtV2 g' i
          ↔ h' ∈ Kepler.Graphs.replace oldF [] (Kepler.Text.TameCorrList.facesAtV2 g i)
            ∨ (i ∈ f₂.vertices ∧ h' = f₂) ∨ (i ∈ f₁.vertices ∧ h' = f₁) := by
      intro hiold h'
      have hRF := t9_replace_filter3 g.faces (fun f => decide (i ∈ f.vertices)) h' oldF [f₂]
        (by simpa using hiold) hndFaces hF
      have hsing1 : (h' ∈ ([f₁] : List Face).filter (fun f => decide (i ∈ f.vertices)))
          ↔ (i ∈ f₁.vertices ∧ h' = f₁) := by
        by_cases h1 : i ∈ f₁.vertices <;> simp [h1, List.mem_filter, and_comm]
      have hsing2 : (h' ∈ ([f₂] : List Face).filter (fun f => decide (i ∈ f.vertices)))
          ↔ (i ∈ f₂.vertices ∧ h' = f₂) := by
        by_cases h2 : i ∈ f₂.vertices <;> simp [h2, List.mem_filter, and_comm]
      show h' ∈ g'.faces.filter (fun f => decide (i ∈ f.vertices)) ↔ _
      rw [hfaces, List.filter_append, List.mem_append, hRF.symm, hsing1, hsing2]
      constructor
      · rintro (⟨h1 | h2⟩ | h3)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3)
      · intro hh
        rcases hh with h1 | h2 | h3
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h2)
        · exact Or.inr h3
    -- 落区
    by_cases hiold : i ∈ oldF.vertices
    · -- R3–R6：i ∈ oldF.vertices，按 betwnCases 分四支
      have hndP : (Kepler.Text.TameCorrList.facesAtV2 g i).Nodup :=
        List.Pairwise.filter _ hndFaces
      have holdP : oldF ∈ Kepler.Text.TameCorrList.facesAtV2 g i := by
        show oldF ∈ g.faces.filter (fun f => i ∈ f.vertices)
        rw [List.mem_filter]
        exact ⟨hF, by simpa using hiold⟩
      have hrep (N : List Face) : (h ∈ Kepler.Graphs.replace oldF N (Fs0.getD i [])
          ↔ h ∈ Kepler.Graphs.replace oldF N (Kepler.Text.TameCorrList.facesAtV2 g i)) :=
        t8b_replace_perm_eq (Fs0.getD i []) (Kepler.Text.TameCorrList.facesAtV2 g i) h oldF N
          (hperm i hilt).symm
      rcases Kepler.Text.TameSpine.betwnCases hrne hndOld hr1 hiold hr2 with
        hram1 | hram2 | hin1 | hin2
      · -- R3：i = ram1
        have hv1 : i ∈ f₁.vertices := hram1.symm ▸ hr1f1
        have hv2 : i ∈ f₂.vertices := hram1.symm ▸ hr1f2
        have hnram2 : i ∉ ([ram₂] : List Vertex) := by
          simp only [List.mem_singleton]; exact fun e => hrne (hram1.symm.trans e)
        have hnin2 : i ∉ between oldF.vertices ram₂ ram₁ := by
          rw [hram1]; exact Kepler.Graphs.between_not_r2 (ram₁ := ram₂) hndOld
        have hnin1 : i ∉ between oldF.vertices ram₁ ram₂ := by
          rw [hram1]; exact Kepler.Graphs.between_not_r1 (ram₁ := ram₁) (ram₂ := ram₂) hndOld
        have hregion : Fs4.getD i [] = Kepler.Graphs.replace oldF [f₂, f₁] (Fs0.getD i []) := by
          calc Fs4.getD i [] = Fs3.getD i [] := by
                rw [hFs4]
                exact t9d_replacefacesAt_getD_notin oldF [ram₂] [f₁, f₂] Fs3 i
                  (by simp) hlt3 hnram2
            _ = Kepler.Graphs.replace oldF [f₂, f₁] (Fs2.getD i []) := by
                rw [hFs3]
                exact t9d_replacefacesAt_getD_in oldF [ram₁] [f₂, f₁] Fs2 i
                  (by simp) hlt2 (by simp only [List.mem_singleton]; exact hram1)
            _ = Kepler.Graphs.replace oldF [f₂, f₁] (Fs1.getD i []) := by
                rw [hFs2, t9d_replacefacesAt_getD_notin oldF (between oldF.vertices ram₂ ram₁)
                  [f₂] Fs1 i (Kepler.Graphs.between_distinct hndOld) hlt1 hnin2]
            _ = Kepler.Graphs.replace oldF [f₂, f₁] (Fs0.getD i []) := by
                rw [hFs1, t9d_replacefacesAt_getD_notin oldF (between oldF.vertices ram₁ ram₂)
                  [f₁] Fs0 i (Kepler.Graphs.between_distinct hndOld)
                  (by rw [hFs0]; exact hilt) hnin1]
        calc (h ∈ g'.facesAt i)
            = (h ∈ Fs4.getD i []) := by rw [hLHSget]
          _ ↔ h ∈ Kepler.Graphs.replace oldF [f₂, f₁] (Fs0.getD i []) := by rw [hregion]
          _ ↔ h ∈ Kepler.Graphs.replace oldF [f₂, f₁] (Kepler.Text.TameCorrList.facesAtV2 g i) := hrep _
          _ ↔ h ∈ Kepler.Graphs.replace oldF [] (Kepler.Text.TameCorrList.facesAtV2 g i)
                ∨ h ∈ ([f₂, f₁] : List Face) :=
                t9_mem_replace _ h oldF [f₂, f₁] hndP holdP
          _ ↔ (h ∈ Kepler.Graphs.replace oldF [] (Kepler.Text.TameCorrList.facesAtV2 g i)
                ∨ (i ∈ f₂.vertices ∧ h = f₂) ∨ (i ∈ f₁.vertices ∧ h = f₁)) := by
                simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
                tauto
          _ ↔ h ∈ Kepler.Text.TameCorrList.facesAtV2 g' i :=
                (hRHStrue hiold h).symm
      · -- R4：i = ram2
        have hv1 : i ∈ f₁.vertices := hram2.symm ▸ hr2f1
        have hv2 : i ∈ f₂.vertices := hram2.symm ▸ hr2f2
        have hnram1 : i ∉ ([ram₁] : List Vertex) := by
          simp only [List.mem_singleton]
          exact fun e => hrne (hram2.symm.trans e).symm
        have hnin2 : i ∉ between oldF.vertices ram₂ ram₁ := by
          rw [hram2]
          exact Kepler.Graphs.between_not_r1 (ram₁ := ram₂) (ram₂ := ram₁) hndOld
        have hnin1 : i ∉ between oldF.vertices ram₁ ram₂ := by
          rw [hram2]; exact Kepler.Graphs.between_not_r2 (ram₁ := ram₁) (ram₂ := ram₂) hndOld
        have hregion : Fs4.getD i [] = Kepler.Graphs.replace oldF [f₁, f₂] (Fs0.getD i []) := by
          calc Fs4.getD i [] = Kepler.Graphs.replace oldF [f₁, f₂] (Fs3.getD i []) := by
                rw [hFs4]
                exact t9d_replacefacesAt_getD_in oldF [ram₂] [f₁, f₂] Fs3 i
                  (by simp) hlt3 (by simp only [List.mem_singleton]; exact hram2)
            _ = Kepler.Graphs.replace oldF [f₁, f₂] (Fs2.getD i []) := by
                rw [hFs3, t9d_replacefacesAt_getD_notin oldF [ram₁] [f₂, f₁] Fs2 i
                  (by simp) hlt2 hnram1]
            _ = Kepler.Graphs.replace oldF [f₁, f₂] (Fs1.getD i []) := by
                rw [hFs2, t9d_replacefacesAt_getD_notin oldF (between oldF.vertices ram₂ ram₁)
                  [f₂] Fs1 i (Kepler.Graphs.between_distinct hndOld) hlt1 hnin2]
            _ = Kepler.Graphs.replace oldF [f₁, f₂] (Fs0.getD i []) := by
                rw [hFs1, t9d_replacefacesAt_getD_notin oldF (between oldF.vertices ram₁ ram₂)
                  [f₁] Fs0 i (Kepler.Graphs.between_distinct hndOld)
                  (by rw [hFs0]; exact hilt) hnin1]
        calc (h ∈ g'.facesAt i)
            = (h ∈ Fs4.getD i []) := by rw [hLHSget]
          _ ↔ h ∈ Kepler.Graphs.replace oldF [f₁, f₂] (Fs0.getD i []) := by rw [hregion]
          _ ↔ h ∈ Kepler.Graphs.replace oldF [f₁, f₂] (Kepler.Text.TameCorrList.facesAtV2 g i) := hrep _
          _ ↔ h ∈ Kepler.Graphs.replace oldF [] (Kepler.Text.TameCorrList.facesAtV2 g i)
                ∨ h ∈ ([f₁, f₂] : List Face) :=
                t9_mem_replace _ h oldF [f₁, f₂] hndP holdP
          _ ↔ (h ∈ Kepler.Graphs.replace oldF [] (Kepler.Text.TameCorrList.facesAtV2 g i)
                ∨ (i ∈ f₂.vertices ∧ h = f₂) ∨ (i ∈ f₁.vertices ∧ h = f₁)) := by
                simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
                tauto
          _ ↔ h ∈ Kepler.Text.TameCorrList.facesAtV2 g' i :=
                (hRHStrue hiold h).symm
      · -- R5：i ∈ vs1
        have hin1' : i ∈ between oldF.vertices ram₁ ram₂ := hin1
        have hin2' : i ∉ between oldF.vertices ram₂ ram₁ :=
          Kepler.Text.Reduction4.betwnDisjoint hndOld hr1 hr2 hrne hin1'
        have hnram1 : i ≠ ram₁ := fun e => Kepler.Graphs.between_not_r1 hndOld (e ▸ hin1')
        have hnram2 : i ≠ ram₂ := fun e => Kepler.Graphs.between_not_r2 hndOld (e ▸ hin1')
        have hf1P : i ∈ f₁.vertices := (hvs1c i ((hmemv1 i).mpr hin1)).1
        have hf2P : i ∉ f₂.vertices := (hvs1c i ((hmemv1 i).mpr hin1)).2
        have hregion : Fs4.getD i [] = Kepler.Graphs.replace oldF [f₁] (Fs0.getD i []) := by
          calc Fs4.getD i [] = Fs3.getD i [] := by
                rw [hFs4]
                exact t9d_replacefacesAt_getD_notin oldF [ram₂] [f₁, f₂] Fs3 i
                  (by simp) hlt3 (by simp only [List.mem_singleton]; exact hnram2)
            _ = Fs2.getD i [] := by
                rw [hFs3]
                exact t9d_replacefacesAt_getD_notin oldF [ram₁] [f₂, f₁] Fs2 i
                  (by simp) hlt2 (by simp only [List.mem_singleton]; exact hnram1)
            _ = Fs1.getD i [] := by
                rw [hFs2]
                exact t9d_replacefacesAt_getD_notin oldF (between oldF.vertices ram₂ ram₁) [f₂] Fs1
                  i (Kepler.Graphs.between_distinct hndOld) hlt1 hin2'
            _ = Kepler.Graphs.replace oldF [f₁] (Fs0.getD i []) := by
                rw [hFs1]
                exact t9d_replacefacesAt_getD_in oldF (between oldF.vertices ram₁ ram₂) [f₁] Fs0
                  i (Kepler.Graphs.between_distinct hndOld) (by rw [hFs0]; exact hilt) hin1'
        calc (h ∈ g'.facesAt i)
            = (h ∈ Fs4.getD i []) := by rw [hLHSget]
          _ ↔ h ∈ Kepler.Graphs.replace oldF [f₁] (Fs0.getD i []) := by rw [hregion]
          _ ↔ h ∈ Kepler.Graphs.replace oldF [f₁] (Kepler.Text.TameCorrList.facesAtV2 g i) := hrep _
          _ ↔ h ∈ Kepler.Graphs.replace oldF [] (Kepler.Text.TameCorrList.facesAtV2 g i)
                ∨ h ∈ ([f₁] : List Face) :=
                t9_mem_replace _ h oldF [f₁] hndP holdP
          _ ↔ (h ∈ Kepler.Graphs.replace oldF [] (Kepler.Text.TameCorrList.facesAtV2 g i)
                ∨ (i ∈ f₂.vertices ∧ h = f₂) ∨ (i ∈ f₁.vertices ∧ h = f₁)) := by
                simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
                tauto
          _ ↔ h ∈ Kepler.Text.TameCorrList.facesAtV2 g' i :=
                (hRHStrue hiold h).symm
      · -- R6：i ∈ vs2
        have hin2'' : i ∈ between oldF.vertices ram₂ ram₁ := hin2
        have hin1'' : i ∉ between oldF.vertices ram₁ ram₂ :=
          Kepler.Text.Reduction4.betwnDisjoint hndOld hr2 hr1 (fun e => hrne e.symm) hin2''
        have hnram1 : i ≠ ram₁ :=
          fun e => Kepler.Graphs.between_not_r2 (ram₁ := ram₂) hndOld (e ▸ hin2'')
        have hnram2 : i ≠ ram₂ :=
          fun e => Kepler.Graphs.between_not_r1 (ram₁ := ram₂) (ram₂ := ram₁) hndOld (e ▸ hin2'')
        have hf2P : i ∈ f₂.vertices := (hvs2c i ((hmemv2 i).mpr hin2)).1
        have hf1P : i ∉ f₁.vertices := (hvs2c i ((hmemv2 i).mpr hin2)).2
        have hregion : Fs4.getD i [] = Kepler.Graphs.replace oldF [f₂] (Fs0.getD i []) := by
          calc Fs4.getD i [] = Fs3.getD i [] := by
                rw [hFs4]
                exact t9d_replacefacesAt_getD_notin oldF [ram₂] [f₁, f₂] Fs3 i
                  (by simp) hlt3 (by simp only [List.mem_singleton]; exact hnram2)
            _ = Fs2.getD i [] := by
                rw [hFs3]
                exact t9d_replacefacesAt_getD_notin oldF [ram₁] [f₂, f₁] Fs2 i
                  (by simp) hlt2 (by simp only [List.mem_singleton]; exact hnram1)
            _ = Kepler.Graphs.replace oldF [f₂] (Fs1.getD i []) := by
                rw [hFs2]
                exact t9d_replacefacesAt_getD_in oldF (between oldF.vertices ram₂ ram₁) [f₂] Fs1
                  i (Kepler.Graphs.between_distinct hndOld) hlt1 hin2''
            _ = Kepler.Graphs.replace oldF [f₂] (Fs0.getD i []) := by
                rw [hFs1, t9d_replacefacesAt_getD_notin oldF (between oldF.vertices ram₁ ram₂)
                  [f₁] Fs0 i (Kepler.Graphs.between_distinct hndOld)
                  (by rw [hFs0]; exact hilt) hin1'']
        calc (h ∈ g'.facesAt i)
            = (h ∈ Fs4.getD i []) := by rw [hLHSget]
          _ ↔ h ∈ Kepler.Graphs.replace oldF [f₂] (Fs0.getD i []) := by rw [hregion]
          _ ↔ h ∈ Kepler.Graphs.replace oldF [f₂] (Kepler.Text.TameCorrList.facesAtV2 g i) := hrep _
          _ ↔ h ∈ Kepler.Graphs.replace oldF [] (Kepler.Text.TameCorrList.facesAtV2 g i)
                ∨ h ∈ ([f₂] : List Face) :=
                t9_mem_replace _ h oldF [f₂] hndP holdP
          _ ↔ (h ∈ Kepler.Graphs.replace oldF [] (Kepler.Text.TameCorrList.facesAtV2 g i)
                ∨ (i ∈ f₂.vertices ∧ h = f₂) ∨ (i ∈ f₁.vertices ∧ h = f₁)) := by
                simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
                tauto
          _ ↔ h ∈ Kepler.Text.TameCorrList.facesAtV2 g' i :=
                (hRHStrue hiold h).symm
    · -- R2：i ∉ oldF.vertices
      have hPf1 : i ∉ f₁.vertices := fun hc => hiold (h4 i hilt hc)
      have hPf2 : i ∉ f₂.vertices := fun hc => hiold (h5 i hilt hc)
      have hregion : Fs4.getD i [] = Fs0.getD i [] := by
        calc Fs4.getD i [] = Fs3.getD i [] := by
              rw [hFs4]
              exact t9d_replacefacesAt_getD_notin oldF [ram₂] [f₁, f₂] Fs3 i
                (by simp) hlt3 (by simp only [List.mem_singleton]; exact fun e => hiold (e ▸ hr2))
          _ = Fs2.getD i [] := by
              rw [hFs3]
              exact t9d_replacefacesAt_getD_notin oldF [ram₁] [f₂, f₁] Fs2 i
                (by simp) hlt2 (by simp only [List.mem_singleton]; exact fun e => hiold (e ▸ hr1))
          _ = Fs1.getD i [] := by
              rw [hFs2]
              exact t9d_replacefacesAt_getD_notin oldF (between oldF.vertices ram₂ ram₁) [f₂] Fs1
                i (Kepler.Graphs.between_distinct hndOld) hlt1
                (fun hc => hiold (Kepler.Text.TameSpine.betwnMem hc))
          _ = Fs0.getD i [] := by
              rw [hFs1]
              exact t9d_replacefacesAt_getD_notin oldF (between oldF.vertices ram₁ ram₂) [f₁] Fs0
                i (Kepler.Graphs.between_distinct hndOld) (by rw [hFs0]; exact hilt)
                (fun hc => hiold (Kepler.Text.TameSpine.betwnMem hc))
      calc (h ∈ g'.facesAt i)
          = (h ∈ Fs4.getD i []) := by rw [hLHSget]
        _ ↔ h ∈ Fs0.getD i [] := by rw [hregion]
        _ ↔ h ∈ Kepler.Text.TameCorrList.facesAtV2 g i := (hperm i hilt).mem_iff.symm
        _ ↔ h ∈ Kepler.Text.TameCorrList.facesAtV2 g' i := by
            -- R2 右侧：`P oldF = P f1 = P f2 = false`，`facesAtV2 g' i` 退化为 `facesAtV2 g i`
            have hPold : (fun f : Face => decide (i ∈ f.vertices)) oldF = false := by
              simp [show decide (i ∈ oldF.vertices) = false from by simp [hiold]]
            have hPf1' : (fun f : Face => decide (i ∈ f.vertices)) f₁ = false := by
              simp [show decide (i ∈ f₁.vertices) = false from by simp [hPf1]]
            have hPf2' : (fun f : Face => decide (i ∈ f.vertices)) f₂ = false := by
              simp [show decide (i ∈ f₂.vertices) = false from by simp [hPf2]]
            show h ∈ g.faces.filter (fun f => decide (i ∈ f.vertices))
              ↔ h ∈ g'.faces.filter (fun f => decide (i ∈ f.vertices))
            rw [hfaces, List.filter_append,
              show ([f₁] : List Face).filter (fun f => decide (i ∈ f.vertices)) = [] by
                simp [hPf1'],
              List.append_nil]
            exact (t9d_filter_replace_of_false g.faces (fun f => decide (i ∈ f.vertices))
              [f₂] h oldF hndFaces hF hPold (by
                intro y hy
                rw [List.mem_singleton] at hy
                subst hy
                exact hPf2')).symm

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t9d_mem_faceListAt_lemma
