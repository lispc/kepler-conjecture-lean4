/-
  Kepler.Text.Reduction3Thm12C — J 战役批：upt/REPLICATE 桥 + b_nfgtrans 族。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │   upt_iota_simple :206  → t12c_upt_iota_simple
  │   REPLICATE_nseq  :360  → t12c_REPLICATE_nseq
  │   b_nfgtrans_suc  :5000 → t12c_b_nfgtrans_suc
  │   b_nfgtrans1     :5232 → t12c_b_nfgtrans1
  └────────────────────────────────────────────────────────────────

  ┌─ 载体/判词 ───────────────────────────────────────────────────
  │ `iota m l ↦ List.range' m l`（D3b 约定）、`upt i j ↦ iota i (j-i)`
  │   ⇒ 本树 `upt a (a+b) = range' a ((a+b)-a)`；桥题按此形落。
  │ `REPLICATE = nseq`：本树 `nseq` 直接译为 `List.replicate`（D2），
  │   两载体坍缩 ⇒ 桥题退化为点态 rfl（DIFFERS 记档）。
  │ **勘误①采信**：HOL `b_nfgtrans`（reduction3.hl:138）def 的方程体
  │   = 本树 `bNfgtrans0` def（D2），无需新 def。
  │ `subdiv_single_step ↦ subdivSingleStep`（D2）；`nseg` 用
  │   `Reduction3Thm5B.subdivSingleStepNseg`（j3-t6d 落库）。
  │ `nextVertex (FST f) u = next_el (FST f) u` 在本树为 rfl
  │   （Face.nextVertex 定义即 nextEl vertices）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」；
  │ if 重写一律 `simp only [if_pos/if_neg]`。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm12B
import Kepler.Text.Reduction3Thm5B
import Kepler.Text.Reduction3Thm11

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList listPairs nextEl prevEl findFaceDarts)
open Kepler.Graphs (Face Graph between fgraph)
open Kepler.Text.Reduction5 (Dart finalList transformCount ytrans ztrans)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-! ## §A `upt_iota_simple`（reduction3.hl:206） -/

/-- HOL `upt_iota_simple`（reduction3.hl:206）：`upt a (a + b) = iota a b`。
折算：`iota m l ↦ List.range' m l`、`upt i j ↦ iota i (j - i)`。 -/
theorem t12c_upt_iota_simple (a b : ℕ) :
    List.range' a ((a + b) - a) = List.range' a b := by
  rw [show (a + b) - a = b from by omega]

/-! ## §B `REPLICATE_nseq`（reduction3.hl:360） -/

/-- HOL `REPLICATE_nseq`（reduction3.hl:360）：`REPLICATE = nseq`。
本树 `nseq` 直接译为 `List.replicate`，两载体坍缩，桥题退化为点态 rfl
（DIFFERS 记档：非陈述弱化，而是载体同一）。 -/
theorem t12c_REPLICATE_nseq {α : Type} (n : ℕ) (x : α) :
    List.replicate n x = List.replicate n x := rfl

/-! ## §C `b_nfgtrans_suc`（reduction3.hl:5000） -/

/-- HOL `b_nfgtrans_suc`（reduction3.hl:5000）：
`b_nfgtrans0 … (SUC i) = foldl subdiv_single_step (b_nfgtrans0 … i)
(dest_triple0_rcons (FST f) (prebatch (FST f) … i) (y_i,z_i,betwn_len))`
（`batch0 = flatten prebatch` 定义级 + `prebatch_suc` + 步进拆段）。 -/
theorem t12c_b_nfgtrans_suc (i : ℕ) (f : Face) (g : Graph) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart) (hg : GoodList L)
    (hgn : GoodListNodesTl L hg) (hir : (hypermapOfList L hg).IsRestricted)
    (hm : markedList L hg N r x) (hnf : ¬ finalList L r)
    (hlt : i < transformCount L N r x)
    (hpre : batch0 f.vertices L N r x i = [] →
      prebatch f.vertices L N r x i = []) :
    bNfgtrans0 f g L N r x (i + 1) =
      List.foldl subdivSingleStep (bNfgtrans0 f g L N r x i)
        (destTriple0Rcons f.vertices (prebatch f.vertices L N r x i)
          ((ytrans L N r x i).1, (ztrans L N r x i).1,
           (between (findFaceDarts L x) (ytrans L N r x i)
             (ztrans L N r x i)).length)) := by
  have hsuc := t12_prebatch_suc f.vertices L N r x i hg hgn hir hm hnf hlt
  have hpre' : (prebatch f.vertices L N r x i).flatten = [] →
      prebatch f.vertices L N r x i = [] := hpre
  have hstep := t12_destTriple0StepRconsPaired f.vertices
    (prebatch f.vertices L N r x i)
    ((ytrans L N r x i).1, (ztrans L N r x i).1,
     (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length)
    hpre'
  have hbatch : (prebatch f.vertices L N r x (i + 1)).flatten
      = (prebatch f.vertices L N r x i).flatten
        ++ destTriple0Rcons f.vertices (prebatch f.vertices L N r x i)
            ((ytrans L N r x i).1, (ztrans L N r x i).1,
             (between (findFaceDarts L x) (ytrans L N r x i)
               (ztrans L N r x i)).length) := by
    rw [hsuc, hstep, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil]
  unfold bNfgtrans0
  dsimp only
  unfold batch0
  rw [hbatch, List.foldl_append]

/-! ## §D `b_nfgtrans1`（reduction3.hl:5232） -/

/-- `subdivSingleStep` 首态 none 支：`some u` 直接置位。 -/
private theorem t12c_step_none (u k : ℕ) (f : Face) (g : Graph) :
    subdivSingleStep ((none, k), f, g) (some u) = ((some u, 0), f, g) := rfl

/-- 条件真支：`nextVertex f u = v ∧ k = 0` 时保持 `f`/`g`，只置 `some v`。 -/
private theorem t12c_step_match (u v k : ℕ) (f : Face) (g : Graph)
    (hc : ((f.nextVertex u == v) && (k == 0)) = true) :
    subdivSingleStep ((some u, k), f, g) (some v) = ((some v, 0), f, g) := by
  unfold subdivSingleStep
  dsimp only
  rw [if_pos hc]

/-- 条件假支：走 `splitFace`，`ws = range' countVertices k`。 -/
private theorem t12c_step_split (u v k : ℕ) (f : Face) (g : Graph)
    (hc : ((f.nextVertex u == v) && (k == 0)) ≠ true) :
    subdivSingleStep ((some u, k), f, g) (some v)
      = ((some v, 0),
         (Kepler.Graphs.splitFace g u v f (List.range' g.countVertices k)).2.1,
         (Kepler.Graphs.splitFace g u v f (List.range' g.countVertices k)).2.2) := by
  unfold subdivSingleStep
  dsimp only
  rw [if_neg hc]

/-- 后缀段：从 `((some u,0),f,g)` 起，过 `n` 个 none 再吃 `some v`，
落到 `((some v,0), splitFace g u v f newVs)`（条件假支 + `range' = newVs`）。 -/
private theorem t12c_suffix (u v n : ℕ) (f : Face) (g : Graph)
    (newVs : List ℕ) (hu : u ∈ f.vertices)
    (hnot : ¬ (nextEl f.vertices u = v ∧ n = 0))
    (hnewVs : List.range' g.countVertices n = newVs) :
    List.foldl subdivSingleStep
        (List.foldl subdivSingleStep ((some u, 0), f, g) (List.replicate n none))
        [some v]
      = (((some v), 0),
         (Kepler.Graphs.splitFace g u v f newVs).2.1,
         (Kepler.Graphs.splitFace g u v f newVs).2.2) := by
  rw [subdivSingleStepNseg n u 0 f g]
  rw [show n + 0 = n from Nat.add_zero n]
  simp only [List.foldl_cons, List.foldl_nil]
  have hc : ((f.nextVertex u == v) && (n == 0)) ≠ true := by
    intro hcon
    rw [Bool.and_eq_true] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hvu : f.nextVertex u = v := beq_iff_eq.mp h1
    have hn0 : n = 0 := beq_iff_eq.mp h2
    exact hnot ⟨by rw [Kepler.Text.TameSpine.nextVertexNextEl hu] at hvu; exact hvu, hn0⟩
  rw [t12c_step_split u v n f g hc, hnewVs]

/-- HOL `b_nfgtrans1`（reduction3.hl:5232）：
`b_nfgtrans0 f g L N r x 1 = ((SOME (FST (ztrans … 0)),0),
SND (splitFace g (FST (ytrans … 0)) (FST (ztrans … 0)) f newVs))`。
`iota (countVertices g) n = newVs` 折算为 `List.range' g.countVertices n = newVs`。 -/
theorem t12c_b_nfgtrans1 (f : Face) (g : Graph) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart) (newVs : List ℕ)
    (hg : GoodList L) (hgn : GoodListNodesTl L hg)
    (hir : (hypermapOfList L hg).IsRestricted) (hm : markedList L hg N r x)
    (hnf : ¬ finalList L r)
    (hnewVs : List.range' g.countVertices
        (between (findFaceDarts L x) (ytrans L N r x 0)
          (ztrans L N r x 0)).length = newVs)
    (huniq : f.vertices.Nodup)
    (hnot : ¬ (nextEl f.vertices (ytrans L N r x 0).1 = (ztrans L N r x 0).1 ∧
        (between (findFaceDarts L x) (ytrans L N r x 0)
          (ztrans L N r x 0)).length = 0))
    (hy : ∀ i, i < transformCount L N r x → (ytrans L N r x i).1 ∈ f.vertices)
    (hz : ∀ i, i < transformCount L N r x → (ztrans L N r x i).1 ∈ f.vertices)
    (hpos : 0 < transformCount L N r x) :
    bNfgtrans0 f g L N r x 1 =
      (((some (ztrans L N r x 0).1), 0),
       (Kepler.Graphs.splitFace g (ytrans L N r x 0).1
         (ztrans L N r x 0).1 f newVs).2.1,
       (Kepler.Graphs.splitFace g (ytrans L N r x 0).1
         (ztrans L N r x 0).1 f newVs).2.2) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  rw [t12c_b_nfgtrans_suc 0 f g L N r x hg hgn hir hm hnf hpos
    (fun _ => prebatchZero f.vertices L N r x)]
  rw [prebatchZero, bNfgtrans0Zero]
  unfold destTriple0Rcons
  dsimp only
  rw [List.flatten_nil, if_pos rfl]
  rw [List.foldl_append, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hu : (ytrans L N r x 0).1 ∈ f.vertices := hy 0 hpos
  by_cases hcond : (nextEl (findFaceDarts L x) x).1 = (ytrans L N r x 0).1
  · simp only [if_pos hcond]
    rw [t12c_step_none (ytrans L N r x 0).1 0 f g]
    exact t12c_suffix (ytrans L N r x 0).1 (ztrans L N r x 0).1
      (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length
      f g newVs hu hnot hnewVs
  · simp only [if_neg hcond]
    have hnext : f.nextVertex (prevEl f.vertices (ytrans L N r x 0).1)
        = (ytrans L N r x 0).1 := by
      rw [Kepler.Text.TameSpine.nextVertexNextEl
        (Kepler.Text.TameLp.prevEl_mem_of_mem hu)]
      exact Kepler.Text.TameLp.nextEl_prevEl huniq hu
    have hcond1 : ((f.nextVertex (prevEl f.vertices (ytrans L N r x 0).1)
        == (ytrans L N r x 0).1) && ((0 : ℕ) == 0)) = true := by
      rw [Bool.and_eq_true]
      exact ⟨beq_iff_eq.mpr hnext, beq_iff_eq.mpr rfl⟩
    rw [t12c_step_match (prevEl f.vertices (ytrans L N r x 0).1)
      (ytrans L N r x 0).1 0 f g hcond1]
    exact t12c_suffix (ytrans L N r x 0).1 (ztrans L N r x 0).1
      (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length
      f g newVs hu hnot hnewVs

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t12c_upt_iota_simple
#print axioms Kepler.Text.Reduction3.t12c_REPLICATE_nseq
#print axioms Kepler.Text.Reduction3.t12c_b_nfgtrans_suc
#print axioms Kepler.Text.Reduction3.t12c_b_nfgtrans1
