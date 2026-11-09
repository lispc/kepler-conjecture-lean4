/-
  Kepler.Text.Reduction3Thm12 — T12 首批（reduction3.hl 4884–5064 纯列表/装配件）。

  ┌─ T12 件表普查（16 件；每件前置声明核查 / 门禁 / 状态）─────────
  │ ✅ prebatch_batch :4910 —— `batch0` 在本树定义为 `(prebatch …).flatten`
  │    （D1 0785ce0e），故为 **rfl 级**。
  │ ✅ prebatch0 :4918 —— **已落**：D1 `prebatchZero`（同陈述，勿重定义）。
  │ ✅ marked_list_good_quotient :4884 —— 前置：TameSpine.goodListQuotient
  │    （TameList10:816）、ChainBridge.normalList_iff_normalListSpine、
  │    quotientList_eq_quotientListSpine、simpleHypermapUniq（TameList14）。
  │ ✅ marked_list_uniq_quotient :4896 —— 前置：上件 + 私有 goodListNodup
  │    （本文件重证 ~12 行；树内 `List_hypermap.good_list_uniq` 无公开形）。
  │ ✅ prebatch_suc :4927 —— 前置：takeEl（T1）/ coreTripleV4_length（D1）/
  │    elCoreTriple（T3）/ foldl_append（core）。`foldl_rcons` 本文件内联。
  │ ✅ dest_triple0_rcons_paired :4953 —— **rfl 级**（def 展开重述）。
  │ ✅ dest_triple0_step_rcons :4970 / _paired :4985 —— 分支展开（同一证明）。
  │ ✅ prebatch1 :5037 —— 前置：takeEl / coreTripleV4_length / elCoreTriple
  │    + 0 < transform_count 槽。
  │ ⏳ prebatch_suc_explicit :5064 —— 依赖本批三件已全就位；估 ~120 行，
  │    归 T12b（避免本片超预算）。
  │ ⛔ reduction_D :4578 —— 前置 `reduction_C` / `marked_list_element_pre` /
  │    `b_nfgtrans`(非0) / `b_nfgtransk` 全树**零命中** ⇒ BLOCKED。
  │ ⛔ reduction_E :4682 —— 依赖 reduction_D ⇒ BLOCKED。
  │ ⛔ nfgtrans_suc :4735 —— 前置 `nfgtrans_add` / `nfgtrans1` 零命中、
  │    `Kbwpbhq`（模块）零命中、`AQIUNPP` 仅有 Hypermap 章主定理 ≠ 本处
  │    AQ 塔件 ⇒ BLOCKED。
  │ ⛔ nfgtrans_mem :4771 —— 依赖 nfgtrans_suc ⇒ BLOCKED。
  │ ⛔ nfgtrans_fst :4814 —— 前置 def `core_split_normal_list_assumption` /
  │    `r_trans_eq_assumption` 树内零命中 + Kbwpbhq + Reduction2 支 ⇒ BLOCKED。
  │ ⛔ b_nfgtrans_suc :5000 —— 前置 def `b_nfgtrans`（非 0 版）零命中
  │    （树内只有 D2 `bNfgtrans0`）⇒ BLOCKED。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」；
  │ if 重写一律 `simp only [if_pos/if_neg]`（rw 只首匹配）；
  │ `List.Perm` 全称（`~` 为 scoped notation）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm3
import Kepler.Text.Reduction4
import Kepler.Text.ChainListsL2
import Kepler.Text.ChainBridgeParts
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.TameList50

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList listPairs nextEl findFaceDarts)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart core finalList quotientList transformCount
  ytrans ztrans)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-! ## §0 辅助（私有，t12_ 前缀） -/

/-- `listPairs` 展平首投影 = 原表（`map_fst_zip` 前提形）。 -/
private theorem t12_map_fst_listPairs (l : List ℕ) :
    (Kepler.Assembly.listPairs l).map Prod.fst = l := by
  have hlen : l.length ≤ (l.drop 1 ++ l.take 1).length := by
    cases l with
    | nil => simp
    | cons x xs => simp
  rw [Kepler.Assembly.listPairs]
  exact List.map_fst_zip hlen

/-- `l ≠ [] ⇒ listPairs l ≠ []`（`list_pairs_empty` 逆否形）。 -/
private theorem t12_listPairs_ne_nil {l : List ℕ} (h : l ≠ []) :
    Kepler.Assembly.listPairs l ≠ [] := by
  intro hc
  refine h (by rw [← t12_map_fst_listPairs l, hc]; rfl)

/-- `flatten` 无重复 + 全非空成员 ⇒ 列表本身无重复（树内私有件重证）。 -/
private theorem t12_uniqFlatten {α : Type*} {L : List (List α)}
    (hun : L.flatten.Nodup) (hn : ∀ l ∈ L, l ≠ []) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    rw [List.flatten_cons] at hun
    obtain ⟨_, h2, h3⟩ := List.nodup_append.mp hun
    rw [List.nodup_cons]
    refine ⟨?_, ih h2 (fun x hx => hn x (List.mem_cons_of_mem _ hx))⟩
    intro ha
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil a (hn a (List.mem_cons_self ..))
    exact (h3 z hz z (List.mem_flatten.mpr ⟨a, ha, hz⟩)) rfl

/-- HOL `List_hypermap.good_list_uniq`（compiled.hl:839）：`GoodList L → L.Nodup`。 -/
private theorem t12_goodListNodup {L : fgraph ℕ} (hL : GoodList L) : L.Nodup := by
  refine List.Nodup.of_map Kepler.Assembly.listPairs
    (t12_uniqFlatten (α := ℕ × ℕ) hL.1 ?_)
  intro q hq
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
  exact t12_listPairs_ne_nil (hL.2.1 l hl)

/-! ## §A `prebatch_batch`（reduction3.hl:4910） -/

/-- HOL `prebatch_batch`（reduction3.hl:4910）：
`flatten (prebatch f0 L N r x i) = batch0 f0 L N r x i`（本树 `batch0`
定义为 `(prebatch …).flatten`，故 rfl 级）。 -/
theorem t12_prebatch_batch (f0 : List ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (i : ℕ) :
    (prebatch f0 L N r x i).flatten = batch0 f0 L N r x i := rfl

/-! ## §B marked_list 两件（:4884/:4896） -/

/-- HOL `marked_list_good_quotient`（reduction3.hl:4884）：
`good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧
is_restricted (hypermap_of_list L) ⇒ good_list (quotient_list L N)`。 -/
theorem t12_marked_list_good_quotient (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (hm : markedList L hL N r x)
    (hir : (hypermapOfList L hL).IsRestricted) :
    GoodList (quotientList L N) := by
  obtain ⟨_, hmn, _⟩ := hm
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hmn
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hir.simple
  have hgq : GoodList (Kepler.Text.TameSpine.quotientListSpine L N) :=
    Kepler.Text.TameSpine.goodListQuotient L hL hnS hir.edgeNondegenerate hunL
  rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
  exact hgq

/-- HOL `marked_list_uniq_quotient`（reduction3.hl:4896）：
`… ⇒ uniq (quotient_list L N)`（`uniq ↦ List.Nodup`）。 -/
theorem t12_marked_list_uniq_quotient (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (hm : markedList L hL N r x)
    (hir : (hypermapOfList L hL).IsRestricted) :
    (quotientList L N).Nodup :=
  t12_goodListNodup (t12_marked_list_good_quotient L hL hgn N r x hm hir)

/-! ## §C `dest_triple0_rcons` 三件（:4953/:4970/:4985） -/

/-- HOL `dest_triple0_rcons_paired`（reduction3.hl:4953）：`destTriple0Rcons`
的四分支重述（对组 p，def 展开即证）。 -/
theorem t12_destTriple0RconsPaired (f : List ℕ) (s : List (List (Option ℕ)))
    (p : ℕ × ℕ × ℕ) :
    destTriple0Rcons f s p =
      (let (u, v, n) := p
       let ns := List.replicate n (none : Option ℕ)
       if s.flatten = [] then [some u] ++ ns ++ [some v]
       else
         let u0 := ((s.getLastD []).getLastD none).getD 0
         if u0 = u then ns ++ [some v]
         else if nextEl f u0 = u then [some u] ++ ns ++ [some v]
         else (between f u0 u).map some ++ [some u] ++ ns ++ [some v]) := rfl

/-- HOL `dest_triple0_step_rcons_paired`（reduction3.hl:4985）：
`destTriple0Step f s p = s ++ [destTriple0Rcons f s p]`（前提 `flatten s = [] →
s = []`；逐分支展开后 rfl 级）。 -/
theorem t12_destTriple0StepRconsPaired (f : List ℕ)
    (s : List (List (Option ℕ))) (p : ℕ × ℕ × ℕ)
    (hs : s.flatten = [] → s = []) :
    destTriple0Step f s p = s ++ [destTriple0Rcons f s p] := by
  obtain ⟨u, v, n⟩ := p
  unfold destTriple0Step destTriple0Rcons
  dsimp only
  by_cases h0 : s.flatten = []
  · rw [if_pos h0, if_pos h0, hs h0]
    rfl
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : ((s.getLastD []).getLastD none).getD 0 = u
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : nextEl f (((s.getLastD []).getLastD none).getD 0) = u
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]

/-- HOL `dest_triple0_step_rcons`（reduction3.hl:4970）：配对件的三元形。 -/
theorem t12_destTriple0StepRcons (f : List ℕ) (s : List (List (Option ℕ)))
    (u v n : ℕ) (hs : s.flatten = [] → s = []) :
    destTriple0Step f s (u, v, n) = s ++ [destTriple0Rcons f s (u, v, n)] :=
  t12_destTriple0StepRconsPaired f s (u, v, n) hs

/-! ## §D `prebatch_suc` / `prebatch1`（:4927/:5037） -/

/-- HOL `prebatch_suc`（reduction3.hl:4927）：`prebatch` 的 SUC 步 = 对
`coreTripleV4` 的第 i 项做 `destTriple0Step`（`take_el` + `foldl_rcons`）。 -/
theorem t12_prebatch_suc (f : List ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (i : ℕ) (hg : GoodList L)
    (hgn : GoodListNodesTl L hg)
    (hir : (hypermapOfList L hg).IsRestricted) (hm : markedList L hg N r x)
    (hnf : ¬ finalList L r) (hi : i < transformCount L N r x) :
    prebatch f L N r x (i + 1) =
      destTriple0Step f (prebatch f L N r x i)
        ((ytrans L N r x i).1, (ztrans L N r x i).1,
         (between (findFaceDarts L x) (ytrans L N r x i)
           (ztrans L N r x i)).length) := by
  have hi' : i < (coreTripleV4 L N r x).length := by
    rw [coreTripleV4_length]; exact hi
  unfold prebatch
  rw [takeEl (coreTripleV4 L N r x) hi', List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [elCoreTriple L N r x i hi]

/-- HOL `prebatch1`（reduction3.hl:5037）：一步 `prebatch` 的显式弧段
（`take1` + 首项 `el_core_triple` + 步进空 sofar 分支）。 -/
theorem t12_prebatch1 (f : List ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (hg : GoodList L)
    (hgn : GoodListNodesTl L hg)
    (hir : (hypermapOfList L hg).IsRestricted) (hm : markedList L hg N r x)
    (hnf : ¬ finalList L r) (hpos : 0 < transformCount L N r x) :
    prebatch f L N r x 1 =
      [[some (ytrans L N r x 0).1] ++
       List.replicate (between (findFaceDarts L x) (ytrans L N r x 0)
         (ztrans L N r x 0)).length (none : Option ℕ) ++
       [some (ztrans L N r x 0).1]] := by
  have h0len : 0 < (coreTripleV4 L N r x).length := by
    rw [coreTripleV4_length]; exact hpos
  unfold prebatch
  rw [show (coreTripleV4 L N r x).take (0 + 1) =
      [(coreTripleV4 L N r x)[0]'h0len] by
    rw [takeEl (coreTripleV4 L N r x) h0len]
    rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [elCoreTriple L N r x 0 hpos]
  simp only [destTriple0Step, List.flatten_nil, if_true]

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t12_prebatch_batch
#print axioms Kepler.Text.Reduction3.t12_marked_list_good_quotient
#print axioms Kepler.Text.Reduction3.t12_marked_list_uniq_quotient
#print axioms Kepler.Text.Reduction3.t12_destTriple0RconsPaired
#print axioms Kepler.Text.Reduction3.t12_destTriple0StepRconsPaired
#print axioms Kepler.Text.Reduction3.t12_destTriple0StepRcons
#print axioms Kepler.Text.Reduction3.t12_prebatch_suc
#print axioms Kepler.Text.Reduction3.t12_prebatch1

-- 前置声明普查（#check 即机器证据；BLOCKED 件的前置在下方注释清单）
#check @Kepler.Text.Reduction3.prebatchZero
#check @Kepler.Text.Reduction3.elCoreTriple
#check @Kepler.Text.Reduction3.takeEl
#check @Kepler.Text.TameSpine.goodListQuotient
#check @Kepler.Text.TameSpine.simpleHypermapUniq
#check @Kepler.Text.ChainBridge.normalList_iff_normalListSpine
#check @Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine
#check @Kepler.Text.Reduction4.transformCount_not
-- BLOCKED 件前置（树内零命中，grep 实证）：reduction_C / marked_list_element_pre /
-- b_nfgtrans(非0) / b_nfgtransk / nfgtrans_add / nfgtrans1 / Kbwpbhq /
-- core_split_normal_list_assumption / r_trans_eq_assumption
