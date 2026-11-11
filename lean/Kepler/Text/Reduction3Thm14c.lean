/-
  Kepler.Text.Reduction3Thm14c — J5-8 W2-2：`index_rtrans` + `core_rtrans`
  （reduction3.hl:3941-3978 / :4058-4104）。

  ┌─ 归属对账（HOL Light Flyspeck text_formalization/tame/reduction3.hl）──
  │ :3941 `index_rtrans`  → `indexRtrans`（`N.idxOf r = (ntrans 1).idxOf (rtrans 1)`）
  │ :4058 `core_rtrans`   → `coreRtrans`（splitFace 一步后 core 的 element 对应）
  └────────────────────────────────────────────────────────────────

  **路线（indexf 层直接闭合，不照抄 HOL 的 Aq7/uniq_sublist_unique 支）**：
  · `indexRtrans`：final 支两 `simp`；非 final 支 `ntrans1`（IdxSplit:114）展开 +
    `List.idxOf_append` + `t10b_indexl_replace`（T10B:75）；其 `hy : s2 ∈ N → s2 = r`
    由 `uniqSublistUnique`（MoreLemma2Naming:160）+ 状态 1 marked 合取 4 供
    （**不用 Aq7 桥**——Lean marked 直接给 `x ∈ rtrans 1`）。
  · `coreRtrans`：状态 1 的 `t10b_indexl_core`（T10B:151）+ `indexRtrans` + 状态 0 的
    `t10b_indexl_core` 三者串成 idxOf 等式；splitFace 侧 `t10b_indexl_splitFace`
    （T10B:165）；末步 `List.idxOf_inj`（显式 `y` 钉死，绕元变量）。
    `MEM_splitFace2` 私有同证重落（`replace3` 一行）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm10B
import Kepler.Text.Reduction5J5IdxSplit
import Kepler.Text.MoreLemma2Naming

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph between fgraph replace replace3 splitFace split_face)
open Kepler.Assembly (GoodList findFaceDarts prevEl)
open Kepler.Text.Reduction5
  (Dart core quotientList ntrans rtrans ly lz transformList splitNormalList
    transformCount finalList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- HOL `MEM_splitFace2`（tame_list.hl:4750；私有同证重落）：
`f ∈ g.faces ⇒ f2 ∈ (SND (SND (splitFace g u v f ws))).faces`。 -/
private theorem t14c_splitFaceAddF21 (g : Graph) (u v : Nat) (f : Face) (ws : List Nat)
    (hf : f ∈ g.faces) :
    (splitFace g u v f ws).2.1 ∈ (splitFace g u v f ws).2.2.faces := by
  show (split_face f u v ws).2 ∈
    replace f [(split_face f u v ws).2] g.faces ++ [(split_face f u v ws).1]
  exact List.mem_append_left _ (replace3 hf List.mem_cons_self)

/-- 被替换元在表中时，替入段的成员都在 `replace` 结果里
（IdxSplit `memReplaceIns` 私有件同证重落）。 -/
private theorem t14c_memReplaceIns {α : Type*} [BEq α] [LawfulBEq α] {f : α}
    {xs g : List α} {y : α} (hf : f ∈ g) (hy : y ∈ xs) :
    y ∈ Kepler.Graphs.replace f xs g := by
  induction g with
  | nil => exact absurd hf List.not_mem_nil
  | cons z zs ih =>
    rw [Kepler.Graphs.replace]
    by_cases hzf : z = f
    · rw [if_pos (by rw [hzf]; exact beq_self_eq_true f)]
      exact List.mem_append_left _ hy
    · rw [if_neg (by simpa using hzf)]
      rcases List.mem_cons.mp hf with h | h
      · exact absurd h.symm hzf
      · exact List.mem_cons_of_mem _ (ih h)

/-- **J5-8 W2-2a：HOL `index_rtrans`**（reduction3.hl:3941-3978）：
`indexl r N = indexl (rtrans 1) (ntrans 1)`。 -/
theorem indexRtrans (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) :
    N.idxOf r = (ntrans L N r x 1).idxOf (rtrans L N r x 1) := by
  by_cases hnf : finalList L r
  · have hn : ntrans L N r x 1 = N := by simp [ntrans, transformList, hnf]
    have hr : rtrans L N r x 1 = r := by simp [rtrans, transformList, hnf]
    rw [hn, hr]
  · set s := splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (Kepler.Text.Reduction5.lz L N r x)) with hs
    have hn : ntrans L N r x 1 = replace r [s.2] N ++ [s.1] := by
      rw [hs]
      exact Kepler.Text.Reduction5.ntrans1 L N r x hnf
    have hr : rtrans L N r x 1 = s.2 := by
      rw [hs]
      simp [rtrans, transformList, hnf]
    have hm1 : Kepler.Text.ChainLists.markedList L hL
        (ntrans L N r x 1) (rtrans L N r x 1) x := haq hgn N r x hm 1
    have hx_s2 : x ∈ s.2 := by
      rw [← hr]
      exact hm1.2.2.2.1
    have hs2mem : s.2 ∈ replace r [s.2] N :=
      t14c_memReplaceIns hm.2.2.1 List.mem_cons_self
    rw [hn, hr, List.idxOf_append, if_pos hs2mem]
    exact (Kepler.Text.Reduction3.t10b_indexl_replace (s := N) (x := r) (y := s.2)
      (fun hs2N => Kepler.Text.MoreLemma2Naming.uniqSublistUnique N hm.2.1.1
        s.2 hs2N r hm.2.2.1 ⟨x, hx_s2, hm.2.2.2.1⟩)
      hm.2.2.1).symm

/-- **J5-8 W2-2b：HOL `core_rtrans`**（reduction3.hl:4058-4104）：
`uniq (quotient L N) ∧ uniq (quotient L (ntrans 1)) ∧ … ∧
 fgraph g = quotient L N ∧ fgraph g' = quotient L (ntrans 1) ⇒
 core L (rtrans 1) = FST f2`（f2 = splitFace 的第二面）。 -/
theorem coreRtrans (g : Graph) (ram₁ ram₂ : ℕ) (oldF : Face) (newVs : List ℕ)
    (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (hu : (quotientList L N).Nodup)
    (hu' : (quotientList L (ntrans L N r x 1)).Nodup)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hmem : oldF ∈ g.faces) (hcore : core L r = oldF.vertices)
    (hfg : fgraphOfGraph g = quotientList L N)
    (hfg' : fgraphOfGraph (splitFace g ram₁ ram₂ oldF newVs).2.2
      = quotientList L (ntrans L N r x 1)) :
    core L (rtrans L N r x 1) = (splitFace g ram₁ ram₂ oldF newVs).2.1.vertices := by
  have hm1 : Kepler.Text.ChainLists.markedList L hL
      (ntrans L N r x 1) (rtrans L N r x 1) x := haq hgn N r x hm 1
  have hr1 : rtrans L N r x 1 ∈ ntrans L N r x 1 := hm1.2.2.1
  -- 状态 1 / 状态 0 的 indexl_core
  have h1 := Kepler.Text.Reduction3.t10b_indexl_core L hr1 hu'
  have h2 := indexRtrans L N r x hL hgn haq hm
  have h3 := Kepler.Text.Reduction3.t10b_indexl_core L hm.2.2.1 hu
  -- splitFace 侧 index 转移
  have hs := Kepler.Text.Reduction3.t10b_indexl_splitFace g ram₁ ram₂ oldF newVs
    (by rw [hfg]; exact hu) (by rw [hfg']; exact hu') hmem
  -- 两个元素都在 quotientList L (ntrans 1)
  have hmemCore : core L (rtrans L N r x 1)
      ∈ quotientList L (ntrans L N r x 1) := by
    rw [Kepler.Text.MoreLemma2Island1.quotientListCore]
    exact List.mem_map.mpr ⟨rtrans L N r x 1, hr1, rfl⟩
  have hmemF2 : (splitFace g ram₁ ram₂ oldF newVs).2.1.vertices
      ∈ quotientList L (ntrans L N r x 1) := by
    rw [← hfg']
    exact List.mem_map.mpr ⟨(splitFace g ram₁ ram₂ oldF newVs).2.1,
      t14c_splitFaceAddF21 g ram₁ ram₂ oldF newVs hmem, rfl⟩
  -- idxOf 串等式
  have hidx : (quotientList L (ntrans L N r x 1)).idxOf (core L (rtrans L N r x 1))
      = (quotientList L (ntrans L N r x 1)).idxOf
          ((splitFace g ram₁ ram₂ oldF newVs).2.1.vertices) := by
    calc (quotientList L (ntrans L N r x 1)).idxOf (core L (rtrans L N r x 1))
        = (ntrans L N r x 1).idxOf (rtrans L N r x 1) := h1
      _ = N.idxOf r := h2.symm
      _ = (quotientList L N).idxOf (core L r) := h3.symm
      _ = (quotientList L N).idxOf oldF.vertices := by rw [hcore]
      _ = (fgraphOfGraph g).idxOf oldF.vertices := by rw [hfg]
      _ = (fgraphOfGraph (splitFace g ram₁ ram₂ oldF newVs).2.2).idxOf
            ((splitFace g ram₁ ram₂ oldF newVs).2.1.vertices) := hs.symm
      _ = (quotientList L (ntrans L N r x 1)).idxOf
            ((splitFace g ram₁ ram₂ oldF newVs).2.1.vertices) := by rw [hfg']
  exact (List.idxOf_inj (y := (splitFace g ram₁ ram₂ oldF newVs).2.1.vertices)
    hmemCore).mp hidx

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.indexRtrans
#print axioms Kepler.Text.Reduction3.coreRtrans
