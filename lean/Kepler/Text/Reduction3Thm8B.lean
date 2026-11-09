/-
  Kepler.Text.Reduction3Thm8B — T8 后半段收尾三件（reduction3.hl:2824/:2875/:2987）。

  ┌─ 件目与路线 ──────────────────────────────────────────────────
  │ replace_uniq :2824 → t8b_replace_uniq（t9_mem_replace_gen 供首配语义）
  │ replace_perm_eq :2987 → t8b_replace_perm_eq。**路线勘误**：不走 HOL 的
  │   `size_induct`（长度强归纳），改走 `List.Perm` 构造子归纳
  │   （nil/cons/swap/trans）；swap 邻换支自建 2×2 情形引理（~30 行）。
  │   同 `minimalFaceCore` 先例：避免照搬原版机器。
  │ all_uniq_faceListAt_lemma :2875 → t8b_all_uniq_faceListAt_lemma。
  │   支撑：`t8b_uniq_betwn`（直接复用树内 `Kepler.Graphs.between_distinct`
  │   ——HOL `Ohcgkfu.uniq_betwn` 的更强形，无需树内零命中的自建）、
  │   `t8b_size_replacefacesAt`（= `t8_size_mapAt` 定义级实例）、
  │   `t8b_not_mem_replace`（替换结果不含 l/news 之外元素）。
  │   `all uniq` 折算：HOL `Seq.all uniq` ↦ `∀ l ∈ …, l.Nodup`
  │   （同 Assembly.AllUniq 口径；空表/全函数语义一致）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」；
  │ if 重写一律 `simp only [if_pos/if_neg]`（rw 只首匹配）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm8
import Kepler.Text.Reduction3Thm9
import Kepler.Graphs.FaceDivisionProps1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph)

/-! ## §0 辅助（私有，t8b_ 前缀） -/

/-- HOL `size_replacefacesAt`（reduction3.hl:2812 区间；Tame_list 注记件）：
`replacefacesAt` 为 `mapAt` 的定义级实例，长度保持由 `t8_size_mapAt` 直给。 -/
private theorem t8b_size_replacefacesAt (ns : List ℕ) (old : Face)
    (news : List Face) (Fs : List (List Face)) :
    (Kepler.Graphs.replacefacesAt ns old news Fs).length = Fs.length :=
  t8_size_mapAt ns (Kepler.Graphs.replace old news) Fs

/-- HOL `Ohcgkfu.uniq_betwn`（OHCGKFU.hl:98）的树内更强形（`between_distinct`：
只需 `vs.Nodup`，不需要端点成员/不交前提）。 -/
private theorem t8b_uniq_betwn {vs : List ℕ} {ram₁ ram₂ : ℕ}
    (hd : vs.Nodup) : (Kepler.Graphs.between vs ram₁ ram₂).Nodup :=
  Kepler.Graphs.between_distinct hd

/-- `x` 不在 `l` 与 `news` 中 ⇒ `x` 不在 `replace old news l` 中（无需 uniq）。 -/
private theorem t8b_not_mem_replace {α : Type} [BEq α] [LawfulBEq α]
    {l : List α} {news : List α} (old : α) {x : α}
    (hl : x ∉ l) (hn : x ∉ news) : x ∉ Kepler.Graphs.replace old news l := by
  induction l with
  | nil => simp [Kepler.Graphs.replace]
  | cons z zs ih =>
    rw [Kepler.Graphs.replace]
    by_cases hz : z = old
    · rw [if_pos (beq_iff_eq.mpr hz)]
      intro hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hn hx'
      · exact hl (List.mem_cons.mpr (Or.inr hx'))
    · rw [if_neg (fun hc : (z == old) = true => hz (beq_iff_eq.mp hc))]
      intro hx
      rcases List.mem_cons.mp hx with hx' | hx'
      · exact hl (List.mem_cons.mpr (Or.inl hx'))
      · exact ih (fun hm => hl (List.mem_cons.mpr (Or.inr hm))) hx'

/-! ## §A `replace_uniq`（reduction3.hl:2824） -/

/-- HOL `replace_uniq`（reduction3.hl:2824）：
`uniq (cat fs ys) ==> uniq (replace x ys fs)`。 -/
theorem t8b_replace_uniq {α : Type} [BEq α] [LawfulBEq α]
    (fs : List α) (x : α) (ys : List α) (h : (fs ++ ys).Nodup) :
    (Kepler.Graphs.replace x ys fs).Nodup := by
  induction fs with
  | nil => simp [Kepler.Graphs.replace]
  | cons z zs ih =>
    rw [List.cons_append] at h
    obtain ⟨hznot, hnd⟩ := List.nodup_cons.mp h
    rw [Kepler.Graphs.replace]
    by_cases hz : z = x
    · rw [if_pos (beq_iff_eq.mpr hz)]
      exact List.perm_append_comm.nodup hnd
    · rw [if_neg (fun hc : (z == x) = true => hz (beq_iff_eq.mp hc))]
      rw [List.nodup_cons]
      refine ⟨?_, ih hnd⟩
      intro hmem
      have hzs : zs.Nodup := (List.nodup_append.mp hnd).1
      rcases (t9_mem_replace_gen zs hzs z x ys).mp hmem with ⟨hzy, -⟩ | ⟨hzz, -⟩
      · exact hznot (List.mem_append.mpr (Or.inr hzy))
      · exact hznot (List.mem_append.mpr (Or.inl hzz))

/-! ## §A0 `replace` 保 Nodup（§A 的消费形） -/

/-- `replace old news l` 保 Nodup（`l ++ news` Nodup 前提下）。 -/
private theorem t8b_replace_nodup {α : Type} [BEq α] [LawfulBEq α]
    {l : List α} {news : List α} (old : α) (hl : l.Nodup) (hn : news.Nodup)
    (hdisj : ∀ x ∈ news, x ∉ l) :
    (Kepler.Graphs.replace old news l).Nodup :=
  t8b_replace_uniq l old news (by
    rw [List.nodup_append]
    exact ⟨hl, hn, fun a ha b hb hab => hdisj b hb (hab ▸ ha)⟩)

/-! ## §B `replace_perm_eq`（reduction3.hl:2987） -/

/-- 邻换支（`perms_eq` 归纳的 swap 构造子）：`y::x::l` 与 `x::y::l` 的
`replace` 成员等价。2×2 情形（y=old?、x=old?）全由 `replace` 展开收口。 -/
private theorem t8b_replace_swap {α : Type} [BEq α] [LawfulBEq α]
    (old : α) (news : List α) (x y : α) (l : List α) (u : α) :
    u ∈ Kepler.Graphs.replace old news (y :: x :: l)
      ↔ u ∈ Kepler.Graphs.replace old news (x :: y :: l) := by
  simp only [Kepler.Graphs.replace]
  by_cases hy : y = old
  · simp only [if_pos (beq_iff_eq.mpr hy)]
    by_cases hx : x = old
    · simp only [if_pos (beq_iff_eq.mpr hx)]
      rw [hy, hx]
    · simp only [if_neg (fun hc : (x == old) = true => hx (beq_iff_eq.mp hc))]
      simp only [List.mem_append, List.mem_cons]
      grind
  · simp only [if_neg (fun hc : (y == old) = true => hy (beq_iff_eq.mp hc))]
    by_cases hx : x = old
    · simp only [if_pos (beq_iff_eq.mpr hx)]
      simp only [List.mem_append, List.mem_cons]
      grind
    · simp only [if_neg (fun hc : (x == old) = true => hx (beq_iff_eq.mp hc))]
      simp only [List.mem_cons]
      grind

/-- HOL `replace_perm_eq`（reduction3.hl:2987）：
`perm_eq xs xs' ==> (MEM u (replace old news xs) <=> MEM u (replace old news xs'))`。 -/
theorem t8b_replace_perm_eq {α : Type} [BEq α] [LawfulBEq α]
    (xs xs' : List α) (u old : α) (news : List α) (h : List.Perm xs xs') :
    u ∈ Kepler.Graphs.replace old news xs
      ↔ u ∈ Kepler.Graphs.replace old news xs' := by
  induction h with
  | nil => rfl
  | cons x p ih =>
    simp only [Kepler.Graphs.replace]
    by_cases hx : x = old
    · simp only [if_pos (beq_iff_eq.mpr hx)]
      simp only [List.mem_append]
      rw [p.mem_iff]
    · simp only [if_neg (fun hc : (x == old) = true => hx (beq_iff_eq.mp hc))]
      simp only [List.mem_cons]
      rw [ih]
  | swap x y l => exact t8b_replace_swap old news x y l u
  | trans p q ih1 ih2 => exact ih1.trans ih2

/-! ## §C `all_uniq_faceListAt_lemma`（reduction3.hl:2875） -/

/-- HOL `all_uniq_faceListAt_lemma`（reduction3.hl:2875）。
`all uniq` ↦ `∀ l ∈ faceListAt, l.Nodup`（Assembly.AllUniq 同口径）。
`splitFace` 的四次 `replacefacesAt` 逐层按 `el_replacefacesAt` 展开；
索引只被至多一处替换（端点不在 between 内），叶子全部归约为
`replace oldF news (原条目)` 的 Nodup。 -/
theorem t8b_all_uniq_faceListAt_lemma (g : Graph) (ram₁ ram₂ : ℕ)
    (oldF : Face) (news : List ℕ) :
    (let s := Kepler.Graphs.splitFace g ram₁ ram₂ oldF news
     let f1 := s.1
     let f2 := s.2.1
     f1 ∉ g.faceListAt.flatten →
     f2 ∉ g.faceListAt.flatten →
     oldF.vertices.Nodup →
     ram₁ ∈ oldF.vertices →
     ram₁ < g.faceListAt.length →
     ram₂ < g.faceListAt.length →
     ram₂ ∈ oldF.vertices →
     f1 ≠ f2 →
     ram₁ ≠ ram₂ →
     (∀ l ∈ g.faceListAt, l.Nodup) →
     ∀ l ∈ s.2.2.faceListAt, l.Nodup) := by
  dsimp only
  intro h1 h2 holdnd hram1 hlt1 hlt2 hram2 hf12 hr12 hall
  set f1 : Face := (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1 with hf1
  set f2 : Face := (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1 with hf2
  have hface : (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.faceListAt
      = Kepler.Graphs.replacefacesAt [ram₂] oldF [f1, f2]
          (Kepler.Graphs.replacefacesAt [ram₁] oldF [f2, f1]
            (Kepler.Graphs.replacefacesAt
              (Kepler.Graphs.between oldF.vertices ram₂ ram₁) oldF [f2]
              (Kepler.Graphs.replacefacesAt
                (Kepler.Graphs.between oldF.vertices ram₁ ram₂) oldF [f1]
                g.faceListAt)))
          ++ List.replicate news.length [f1, f2] := by
    rw [hf1, hf2]
    rfl
  rw [hface]
  intro l hl
  rcases List.mem_append.mp hl with hl4 | hlrep
  · obtain ⟨i, hi4, rfl⟩ := List.mem_iff_getElem.mp hl4
    let A : List ℕ := Kepler.Graphs.between oldF.vertices ram₁ ram₂
    let B : List ℕ := Kepler.Graphs.between oldF.vertices ram₂ ram₁
    let Fs0 : List (List Face) := g.faceListAt
    let Fs1 : List (List Face) := Kepler.Graphs.replacefacesAt A oldF [f1] Fs0
    let Fs2 : List (List Face) := Kepler.Graphs.replacefacesAt B oldF [f2] Fs1
    let Fs3 : List (List Face) := Kepler.Graphs.replacefacesAt [ram₁] oldF [f2, f1] Fs2
    let Fs4 : List (List Face) := Kepler.Graphs.replacefacesAt [ram₂] oldF [f1, f2] Fs3
    change (Fs4[i]'hi4).Nodup
    have hA : A.Nodup := t8b_uniq_betwn holdnd
    have hB : B.Nodup := t8b_uniq_betwn holdnd
    have hlen10 : Fs1.length = Fs0.length := t8b_size_replacefacesAt A oldF [f1] Fs0
    have hlen21 : Fs2.length = Fs1.length := t8b_size_replacefacesAt B oldF [f2] Fs1
    have hlen32 : Fs3.length = Fs2.length := t8b_size_replacefacesAt [ram₁] oldF [f2, f1] Fs2
    have hlen43 : Fs4.length = Fs3.length := t8b_size_replacefacesAt [ram₂] oldF [f1, f2] Fs3
    have hi3 : i < Fs3.length := by rw [← hlen43]; exact hi4
    have hi2 : i < Fs2.length := by rw [← hlen32]; exact hi3
    have hi1 : i < Fs1.length := by rw [← hlen21]; exact hi2
    have hi0 : i < Fs0.length := by rw [← hlen10]; exact hi1
    have hFs0i : (Fs0.getD i []).Nodup := by
      rw [List.getD_eq_getElem (hn := hi0)]
      exact hall _ (List.getElem_mem hi0)
    have hmem0 : Fs0.getD i [] ∈ Fs0 := by
      rw [List.getD_eq_getElem (hn := hi0)]
      exact List.getElem_mem hi0
    have hf1n : f1 ∉ Fs0.getD i [] :=
      fun hm => h1 (List.mem_flatten.mpr ⟨_, hmem0, hm⟩)
    have hf2n : f2 ∉ Fs0.getD i [] :=
      fun hm => h2 (List.mem_flatten.mpr ⟨_, hmem0, hm⟩)
    have e4 := t8_el_replacefacesAt [ram₂] oldF [f1, f2] Fs3 i []
      (List.nodup_singleton _) hi3
    have e3 := t8_el_replacefacesAt [ram₁] oldF [f2, f1] Fs2 i []
      (List.nodup_singleton _) hi2
    have e2 := t8_el_replacefacesAt B oldF [f2] Fs1 i [] hB hi1
    have e1 := t8_el_replacefacesAt A oldF [f1] Fs0 i [] hA hi0
    have hnews12 : ([f1, f2] : List Face).Nodup := by
      rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro h; rw [List.mem_singleton] at h; exact hf12 h
      · rw [List.nodup_cons]
        exact ⟨fun h => absurd h (List.not_mem_nil), List.nodup_nil⟩
    have hnews21 : ([f2, f1] : List Face).Nodup := by
      rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro h; rw [List.mem_singleton] at h; exact hf12 h.symm
      · rw [List.nodup_cons]
        exact ⟨fun h => absurd h (List.not_mem_nil), List.nodup_nil⟩
    have rn : ∀ (news' : List Face), news'.Nodup →
        (∀ x ∈ news', x ∉ Fs0.getD i []) →
        (Kepler.Graphs.replace oldF news' (Fs0.getD i [])).Nodup :=
      fun news' hn hd => t8b_replace_nodup oldF hFs0i hn hd
    have disj12 : ∀ x ∈ ([f1, f2] : List Face), x ∉ Fs0.getD i [] := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hf1n
      · rw [List.mem_singleton] at hx; subst hx; exact hf2n
    have disj21 : ∀ x ∈ ([f2, f1] : List Face), x ∉ Fs0.getD i [] := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hf2n
      · rw [List.mem_singleton] at hx; subst hx; exact hf1n
    have disj2 : ∀ x ∈ ([f2] : List Face), x ∉ Fs0.getD i [] := by
      intro x hx
      rw [List.mem_singleton] at hx; subst hx; exact hf2n
    have disj1 : ∀ x ∈ ([f1] : List Face), x ∉ Fs0.getD i [] := by
      intro x hx
      rw [List.mem_singleton] at hx; subst hx; exact hf1n
    rw [List.getElem_eq_getD ([] : List Face), e4]
    by_cases h4 : i ∈ [ram₂]
    · -- i = ram₂：只被 [ram₂] 这一层触及
      rw [if_pos h4]
      have hi4eq : i = ram₂ := List.mem_singleton.mp h4
      have hram1A : ram₁ ∉ A := Kepler.Graphs.between_not_r1 holdnd
      have hram2A : ram₂ ∉ A := Kepler.Graphs.between_not_r2 holdnd
      have hram2B : ram₂ ∉ B := Kepler.Graphs.between_not_r1 holdnd
      rw [e3]
      rw [if_neg (fun h : i ∈ [ram₁] =>
        hr12 (by rw [List.mem_singleton] at h; exact (hi4eq ▸ h).symm))]
      rw [e2]
      rw [if_neg (fun h : i ∈ B => hram2B (hi4eq ▸ h))]
      rw [e1]
      rw [if_neg (fun h : i ∈ A => hram2A (hi4eq ▸ h))]
      exact rn [f1, f2] hnews12 disj12
    · rw [if_neg h4]
      by_cases h3 : i ∈ [ram₁]
      · -- i = ram₁：只被 [ram₁] 这一层触及
        rw [e3, if_pos h3]
        have hi3eq : i = ram₁ := List.mem_singleton.mp h3
        have hram1B : ram₁ ∉ B := Kepler.Graphs.between_not_r2 holdnd
        have hram1A : ram₁ ∉ A := Kepler.Graphs.between_not_r1 holdnd
        rw [e2]
        rw [if_neg (fun h : i ∈ B => hram1B (hi3eq ▸ h))]
        rw [e1]
        rw [if_neg (fun h : i ∈ A => hram1A (hi3eq ▸ h))]
        exact rn [f2, f1] hnews21 disj21
      · -- i 不是端点：只可能落在 A/B 或都不落
        rw [e3, if_neg h3]
        rw [e2]
        by_cases h2 : i ∈ B
        · rw [if_pos h2]
          rw [e1]
          by_cases h1' : i ∈ A
          · -- A ∧ B 双层：先 [f1] 后 [f2]
            rw [if_pos h1']
            have hinner : (Kepler.Graphs.replace oldF [f1] (Fs0.getD i [])).Nodup :=
              rn [f1] (List.nodup_singleton _) disj1
            have hf2inner : f2 ∉ Kepler.Graphs.replace oldF [f1] (Fs0.getD i []) :=
              t8b_not_mem_replace oldF hf2n (by
                intro h; rw [List.mem_singleton] at h; exact hf12 h.symm)
            exact t8b_replace_nodup oldF hinner (List.nodup_singleton _) (by
              intro x hx
              rw [List.mem_singleton] at hx; subst hx
              exact hf2inner)
          · -- 只 [f2]
            rw [if_neg h1']
            exact rn [f2] (List.nodup_singleton _) disj2
        · rw [if_neg h2]
          rw [e1]
          by_cases h1' : i ∈ A
          · -- 只 [f1]
            rw [if_pos h1']
            exact rn [f1] (List.nodup_singleton _) disj1
          · -- 原条目
            rw [if_neg h1']
            exact hFs0i
  · rw [List.mem_replicate] at hlrep
    obtain ⟨_, rfl⟩ := hlrep
    exact List.nodup_cons.mpr ⟨by simpa using hf12, List.nodup_singleton _⟩

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t8b_replace_uniq
#print axioms Kepler.Text.Reduction3.t8b_replace_perm_eq
#print axioms Kepler.Text.Reduction3.t8b_all_uniq_faceListAt_lemma
