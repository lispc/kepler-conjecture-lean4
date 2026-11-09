/-
  Kepler.Text.Reduction3Thm8 — J 战役 T8 首批（纯列表件 6/9；普查见 DELIVERY §21）。

  ┌─ 普查摘要（每件：def 就位性 / 世界匹配 / 门禁 / 状态）────────
  │ ✅ el_list_update(:2750)：HOL `list_update`（tame_defs2:194，越界恒等）
  │    ↦ **List.set**（std 同语义，非第二定义族；DIFFERS 记档：越界恒等两库一致）。
  │ ✅ el_mapAt(:2768)：树 `Kepler.Graphs.mapAt`（ListAux:61）与 HOL 同形
  │    （`if n < length` → `set n (f (get n))`）——直接用。
  │ ✅ size_mapAt(:2791)：同上。
  │ ✅ el_replacefacesAt(:2812)：树 `replacefacesAt`（FaceDivision:19）同形
  │    （`mapAt ns (replace f fs)`）。
  │ ✅ all_nseq(:2840)：`nseq` ↦ `List.replicate`（T1 已折）。
  │ ✅ facesAt_graph(:2979)：`facesAt` ↦ `faceListAt.getD i []`（EL junk 支
  │    DIFFERS：HOL 越界任意 vs getD []——在界同值）。
  │ ⚠ replace_uniq(:2824)：需 `MEM_replace`（= T9 的 :3096 件）作首配语义——
  │    归 T9 批一并落（本轮未做）。
  │ ⚠ replace_perm_eq(:2987)：`perm_eq` ↦ `List.Perm` + `size_induct`
  │    （链侧 = 长度强归纳）——归 T9（与 replace_uniq 同依赖 mem_replace）。
  │ ⚠ all_uniq_faceListAt_lemma(:2875)：splitFace✓/replacefacesAt✓/all_nseq✓
  │    但需 `Ohcgkfu.uniq_betwn`（树内零命中，可链侧 ~10 行落）+
  │    `size_replacefacesAt`（须补）——归 T8 后半段专批。
  │ 纪律：零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm6C
import Kepler.Graphs.ListAux
import Kepler.Graphs.FaceDivision

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph)

/-! ## §A `el_list_update`（reduction3.hl:2750）：`list_update ↦ List.set` -/

/-- HOL `el_list_update`（reduction3.hl:2750）：
`i < sizel xs ∧ j < sizel xs ==> EL i (list_update xs j v) =
if (i=j) then v else EL i xs`（getD junk 形，在界同值）。 -/
theorem t8_el_list_update {α : Type} (xs : List α) (i j : ℕ) (v d : α)
    (hi : i < xs.length) (hj : j < xs.length) :
    (xs.set j v).getD i d = if i = j then v else xs.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · rw [if_pos h, if_pos (h ▸ hj), if_pos h.symm]
    simp
  · rw [if_neg h, if_neg (fun e : i = j => h e.symm)]
    rw [← List.getD_eq_getElem?_getD]

/-! ## §B `el_mapAt` / `size_mapAt`（reduction3.hl:2768/:2791）

树 `mapAt` 与 HOL 同形；`uniq ns` ↦ `ns.Nodup`；归纳 ns，首配分支用
`t8_el_list_update`。 -/

/-- HOL `size_mapAt`（reduction3.hl:2791）：`sizel (mapAt ns f xs) = sizel xs`。 -/
theorem t8_size_mapAt {α : Type} (ns : List ℕ) (f : α → α) (xs : List α) :
    (Kepler.Graphs.mapAt ns f xs).length = xs.length := by
  induction ns generalizing xs with
  | nil => rfl
  | cons h t ih =>
    rw [Kepler.Graphs.mapAt]
    by_cases hh : h < xs.length
    · rw [dif_pos hh, ih, List.length_set]
    · rw [dif_neg hh, ih]

/-- HOL `el_mapAt`（reduction3.hl:2768）：
`uniq ns ∧ i < sizel xs ==> EL i (mapAt ns f xs) =
if (MEM i ns) then f (EL i xs) else (EL i xs)`（getD junk 形）。 -/
theorem t8_el_mapAt {α : Type} (ns : List ℕ) (xs : List α) (f : α → α)
    (i : ℕ) (d : α) (hnd : ns.Nodup) (hi : i < xs.length) :
    (Kepler.Graphs.mapAt ns f xs).getD i d
      = if i ∈ ns then f (xs.getD i d) else xs.getD i d := by
  induction ns generalizing xs with
  | nil => simp [Kepler.Graphs.mapAt]
  | cons h t ih =>
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    rw [Kepler.Graphs.mapAt]
    by_cases hh : h < xs.length
    · rw [dif_pos hh, List.getElem_eq_getD d]
      have hlen : i < (xs.set h (f (xs.getD h d))).length := by
        rw [List.length_set]; exact hi
      rw [ih (xs.set h (f (xs.getD h d))) hnd' hlen]
      by_cases he : i = h
      · rw [if_pos (List.mem_cons.mpr (Or.inl he))]
        rw [if_neg (by rwa [he])]
        rw [t8_el_list_update xs i h (f (xs.getD h d)) d hi hh, if_pos he]
        rw [he]
      · have hmem : i ∈ h :: t ↔ i ∈ t :=
          ⟨fun hc => (List.mem_cons.mp hc).elim (fun e => absurd e he) id,
            fun hc => List.mem_cons.mpr (Or.inr hc)⟩
        by_cases hit : i ∈ t
        · rw [if_pos hit, if_pos (hmem.mpr hit)]
          rw [t8_el_list_update xs i h (f (xs.getD h d)) d hi hh, if_neg he]
        · rw [if_neg hit, if_neg (fun hc => hit (hmem.mp hc))]
          rw [t8_el_list_update xs i h (f (xs.getD h d)) d hi hh, if_neg he]
    · rw [dif_neg hh]
      rw [ih xs hnd' hi]
      have hne : i ≠ h := by
        intro e
        apply hh
        rw [← e]
        exact hi
      have hmem : i ∈ h :: t ↔ i ∈ t :=
        ⟨fun hc => (List.mem_cons.mp hc).elim (fun e => absurd e hne) id,
          fun hc => List.mem_cons.mpr (Or.inr hc)⟩
      by_cases hit : i ∈ t
      · rw [if_pos hit, if_pos (hmem.mpr hit)]
      · rw [if_neg hit, if_neg (fun hc => hit (hmem.mp hc))]

/-! ## §C `el_replacefacesAt`（reduction3.hl:2812）：`mapAt ns (replace old news)` 直取 -/

/-- HOL `el_replacefacesAt`（reduction3.hl:2812）。 -/
theorem t8_el_replacefacesAt (ns : List ℕ) (old : Face) (news : List Face)
    (Fs : List (List Face)) (i : ℕ) (d : List Face) (hnd : ns.Nodup)
    (hi : i < Fs.length) :
    (Kepler.Graphs.replacefacesAt ns old news Fs).getD i d
      = if i ∈ ns then Kepler.Graphs.replace old news (Fs.getD i d)
        else Fs.getD i d :=
  t8_el_mapAt ns Fs (Kepler.Graphs.replace old news) i d hnd hi

/-! ## §D `all_nseq`（reduction3.hl:2840）：`nseq ↦ List.replicate` -/

/-- HOL `all_nseq`（reduction3.hl:2840）：`all P (nseq n x) <=> (P x \/ n = 0)`。 -/
theorem t8_all_nseq {α : Type} (n : ℕ) (P : α → Bool) (x : α) :
    ((List.replicate n x).all P = true) ↔ (P x = true ∨ n = 0) := by
  rw [List.all_replicate]
  cases n with
  | zero => simp
  | succ k => simp

/-! ## §E `facesAt_graph`（reduction3.hl:2979）

`facesAt (Graph fs n Fs ht) i = EL i Fs`——树内 `facesAt = faceListAt.getD i []`
（越界 junk 支 DIFFERS：HOL 任意 vs []；在界同值），本件 rfl 级。 -/

/-- HOL `facesAt_graph`（reduction3.hl:2979）的 getD junk-safe 形。 -/
theorem t8_facesAt_graph (fs : List Face) (n : ℕ) (Fs : List (List Face))
    (ht : List ℕ) (i : ℕ) :
    (Kepler.Graphs.Graph.mk fs n Fs ht).facesAt i = Fs.getD i [] := rfl

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t8_el_list_update
#print axioms Kepler.Text.Reduction3.t8_size_mapAt
#print axioms Kepler.Text.Reduction3.t8_el_mapAt
#print axioms Kepler.Text.Reduction3.t8_el_replacefacesAt
#print axioms Kepler.Text.Reduction3.t8_all_nseq
#print axioms Kepler.Text.Reduction3.t8_facesAt_graph
