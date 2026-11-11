/-
  Kepler.Text.Reduction3Thm14d — J5-8 W2-3a：reduction2 上游 A 簇三件
  （reduction2.hl:1003 / :1417 / :1508）。

  ┌─ 归属对账（HOL Light Flyspeck text_formalization/tame/reduction2.hl）──
  │ A1 :1003 `split_normal_list_split_list` → `splitNormalListSplitList`
  │ A2 :1417 `fgraph_splitFace`             → `fgraphSplitFace`（rfl 级）
  │ A3 :1508 `fgraph_quotient_list_transform_lemma` →
  │          `fgraphQuotientListTransformLemma`
  └────────────────────────────────────────────────────────────────

  **DIFFERS（逐条）**：
  · A1：HOL 的 let 定义量 y/z/z'/f/newVs 在本仓 `splitNormalList` 载体下
    全部可由 `l'y/l'z/prev_el/find_face/betwn` 展开；本件把**五个定义量
    提升为显式参数**（消费者 A3 已持同型等式），证体只消费 hsplit 合取。
    载体前提 good_list/good_list_nodes/marked/is_restricted/¬final 按 HOL 保留
    （证体零消费，装配面逐字同形）。
  · A2：HOL `MAP FST` ↦ `List.map (fun f => f.vertices)`；`fgraph` ↦
    `fgraphOfGraph`；splitFace 的 faces 字段在 `Kepler.Graphs.splitFace` 定义为
    `replace oldF [f2] fs ++ [f1]` ⇒ rfl。
  · A3：HOL 中未消费的前提（r_rtrans_eq/newvertex_prepped/vertices_set2/
    sizel newVs/rotate_to/fw/w）不携入；`ntrans 1` 的展开式（HOL 由 `ntrans1`
    现推）提升为显式前提 `hnt`；`(f1,f2) = split_normal_list …` 的 core 等式
    提升为显式前提 `hsplit`；`h ∈ faces g`、`core L r = FST h`、
    `fgraph g = quotient L N`、`fgraph g' = …` 保留。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm14c
import Kepler.Text.TameSpine.JcajyduAqLeaf8W05
import Kepler.Text.ChainBridgeParts

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

/-- `replace` 沿单射 `map` 交换（HOL `map_replace` 的单射形）：
`hinj` 在 `s` 上，`x ∈ s` ⇒ `(replace x [y] s).map f = replace (f x) [f y] (s.map f)`。 -/
private theorem t14d_mapReplace {α β : Type*} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β] (f : α → β) {s : List α} {x y : α}
    (hinj : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b) (hx : x ∈ s) :
    (replace x [y] s).map f = replace (f x) [f y] (s.map f) := by
  induction s with
  | nil => exact absurd hx List.not_mem_nil
  | cons z zs ih =>
    by_cases hzx : z = x
    · subst hzx
      simp [Kepler.Graphs.replace]
    · have hxzs : x ∈ zs := (List.mem_cons.mp hx).resolve_left (fun h => hzx h.symm)
      have hfzx : f z ≠ f x := fun h =>
        hzx (hinj z (by simp) x (List.mem_cons_of_mem z hxzs) h)
      simp only [Kepler.Graphs.replace, List.map_cons]
      rw [if_neg (by simpa using hzx), if_neg (by simpa using hfzx), List.map_cons]
      rw [ih (fun a ha b hb => hinj a (List.mem_cons_of_mem z ha)
        b (List.mem_cons_of_mem z hb)) hxzs]

/-- **W2-3a A1：HOL `split_normal_list_split_list`**（reduction2.hl:1003-1041）：
`split_face (core L r, b) (FST y) (FST z') newVs` 的两片 = `core` 侧拼接
（hsplit 合取）。 -/
theorem splitNormalListSplitList (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (b : Bool)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hnf : ¬ finalList L r)
    {y z' : Dart} {f : List Dart} {newVs : List ℕ}
    (hsplit : core L (splitNormalList L r f y z').1
        = newVs.reverse ++ ([y.1] ++ (between (core L r) y.1 z'.1 ++ [z'.1])) ∧
      core L (splitNormalList L r f y z').2
        = ([z'.1] ++ (between (core L r) z'.1 y.1 ++ [y.1])) ++ newVs) :
    split_face (Face.mk (core L r) b) y.1 z'.1 newVs
      = (Face.mk (core L (splitNormalList L r f y z').1) false,
         Face.mk (core L (splitNormalList L r f y z').2) false) := by
  obtain ⟨h1, h2⟩ := hsplit
  have hsp : split_face (Face.mk (core L r) b) y.1 z'.1 newVs
      = (Face.mk (newVs.reverse ++
            (([y.1] ++ between (core L r) y.1 z'.1) ++ [z'.1])) false,
         Face.mk (([z'.1] ++ between (core L r) z'.1 y.1 ++ [y.1]) ++ newVs) false) := rfl
  have h1' : core L (splitNormalList L r f y z').1
      = newVs.reverse ++ (([y.1] ++ between (core L r) y.1 z'.1) ++ [z'.1]) := by
    rw [h1]
    simp only [List.append_assoc]
  have h2' : core L (splitNormalList L r f y z').2
      = ([z'.1] ++ between (core L r) z'.1 y.1 ++ [y.1]) ++ newVs := by
    rw [h2]
    simp only [List.append_assoc]
  rw [hsp, h1', h2']

/-- **W2-3a A2：HOL `fgraph_splitFace`**（reduction2.hl:1417-1431）：
`fgraph (SND (SND (splitFace g u v h ws))) =
 MAP FST (replace h [f2] (faces g) ++ [f1])`（Lean 形 rfl）。 -/
theorem fgraphSplitFace (g : Graph) (u v : ℕ) (h : Face) (ws : List ℕ) :
    fgraphOfGraph (splitFace g u v h ws).2.2
      = (replace h [(split_face h u v ws).2] g.faces
          ++ [(split_face h u v ws).1]).map (fun f => f.vertices) := rfl

/-- **W2-3a A3：HOL `fgraph_quotient_list_transform_lemma`**（reduction2.hl:1508-1610）：
`fgraph g = quotient L N` 经一次 splitFace（h 换 f1/f2）后 =
`quotient L (ntrans 1)`。 -/
theorem fgraphQuotientListTransformLemma (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (g : Graph) (N' : List (List Dart))
    (h : Face) (g' : Graph) (y z' : Dart) (f : List Dart) (newVs : List ℕ)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hnf : ¬ finalList L r)
    (hfg : fgraphOfGraph g = quotientList L N)
    (hN' : ntrans L N r x 1 = N')
    (hcore : core L r = h.vertices)
    (hmem : h ∈ g.faces)
    (hstep : (splitFace g y.1 z'.1 h newVs).2.2 = g')
    (hsplit : core L (splitNormalList L r f y z').1
        = newVs.reverse ++ ([y.1] ++ (between h.vertices y.1 z'.1 ++ [z'.1])) ∧
      core L (splitNormalList L r f y z').2
        = ([z'.1] ++ (between h.vertices z'.1 y.1 ++ [y.1])) ++ newVs)
    (hnt : ntrans L N r x 1
        = replace r [(splitNormalList L r f y z').2] N
          ++ [(splitNormalList L r f y z').1]) :
    fgraphOfGraph g' = quotientList L N' := by
  -- quotient 列表外层 Nodup（good_list_uniq @ quotient_list）
  have hqnd : (quotientList L N).Nodup := by
    have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
      (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hm.2.1
    have hunL : ∀ l ∈ L, l.Nodup :=
      (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hm.1.simple
    have hGL : GoodList (Kepler.Text.TameSpine.quotientListSpine L N) :=
      Kepler.Text.TameSpine.goodListQuotient L hL hnS hm.1.edgeNondegenerate hunL
    have hGL' : GoodList (quotientList L N) := by
      rwa [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine L N]
    exact Kepler.Text.TameSpine.goodListUniq (quotientList L N) hGL'
  -- 两侧单射
  have hinjFaces : ∀ a ∈ g.faces, ∀ b ∈ g.faces, a.vertices = b.vertices → a = b := by
    have h2 : (fgraphOfGraph g).Nodup := by rw [hfg]; exact hqnd
    have hnd : (g.faces.map (fun f : Face => f.vertices)).Nodup := by
      simpa only [fgraphOfGraph] using h2
    exact fun a ha b hb he => Kepler.Text.TameSpine.uniqImpInj hnd ha hb he
  have hinjCore : ∀ a ∈ N, ∀ b ∈ N, core L a = core L b → a = b := by
    have hnd : (N.map (core L)).Nodup := by
      rw [← Kepler.Text.MoreLemma2Island1.quotientListCore]; exact hqnd
    exact fun a ha b hb he => Kepler.Text.TameSpine.uniqImpInj hnd ha hb he
  -- h 的 Face 形（h.vertices = core L r）
  have hface : Face.mk (core L r) h.isFinal = h := by
    cases h with
    | mk vs fin => exact congrArg₂ Face.mk hcore rfl
  -- A1：split_face 的两片
  have hsplitCore : core L (splitNormalList L r f y z').1
        = newVs.reverse ++ ([y.1] ++ (between (core L r) y.1 z'.1 ++ [z'.1])) ∧
      core L (splitNormalList L r f y z').2
        = ([z'.1] ++ (between (core L r) z'.1 y.1 ++ [y.1])) ++ newVs := by
    constructor
    · rw [hsplit.1, ← hcore]
    · rw [hsplit.2, ← hcore]
  have hsp := splitNormalListSplitList L N r x h.isFinal hL hgn hm hir hnf hsplitCore
  have hsp1 : (split_face h y.1 z'.1 newVs).1
      = Face.mk (core L (splitNormalList L r f y z').1) false := by
    rw [← hface]
    exact congrArg Prod.fst hsp
  have hsp2 : (split_face h y.1 z'.1 newVs).2
      = Face.mk (core L (splitNormalList L r f y z').2) false := by
    rw [← hface]
    exact congrArg Prod.snd hsp
  -- A2：fgraph g' 的替换形
  have hfg' : fgraphOfGraph g'
      = (replace h [(split_face h y.1 z'.1 newVs).2] g.faces
          ++ [(split_face h y.1 z'.1 newVs).1]).map (fun f => f.vertices) := by
    rw [← hstep]
    exact fgraphSplitFace g y.1 z'.1 h newVs
  rw [hfg', hsp1, hsp2]
  -- 两处 map_replace + 拼接
  calc (replace h [Face.mk (core L (splitNormalList L r f y z').2) false] g.faces
        ++ [Face.mk (core L (splitNormalList L r f y z').1) false]).map
          (fun f => f.vertices)
      = (replace h [Face.mk (core L (splitNormalList L r f y z').2) false]
            g.faces).map (fun f => f.vertices)
          ++ [core L (splitNormalList L r f y z').1] := by
          rw [List.map_append]; rfl
    _ = replace (core L r) [core L (splitNormalList L r f y z').2]
          (g.faces.map (fun f => f.vertices))
          ++ [core L (splitNormalList L r f y z').1] := by
          rw [t14d_mapReplace (fun f : Face => f.vertices) hinjFaces hmem, ← hcore]
    _ = replace (core L r) [core L (splitNormalList L r f y z').2]
          (N.map (core L))
          ++ [core L (splitNormalList L r f y z').1] := by
          rw [show g.faces.map (fun f : Face => f.vertices) = fgraphOfGraph g from rfl,
            hfg, Kepler.Text.MoreLemma2Island1.quotientListCore]
    _ = (replace r [(splitNormalList L r f y z').2] N).map (core L)
          ++ [core L (splitNormalList L r f y z').1] := by
          rw [t14d_mapReplace (core L) hinjCore hm.2.2.1]
    _ = ((replace r [(splitNormalList L r f y z').2] N)
          ++ [(splitNormalList L r f y z').1]).map (core L) := by
          rw [List.map_append]; rfl
    _ = quotientList L N' := by
          rw [Kepler.Text.MoreLemma2Island1.quotientListCore, ← hN', hnt]

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.splitNormalListSplitList
#print axioms Kepler.Text.Reduction3.fgraphSplitFace
#print axioms Kepler.Text.Reduction3.fgraphQuotientListTransformLemma
