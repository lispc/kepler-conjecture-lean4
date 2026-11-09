/-
  Kepler.Text.Reduction3Thm7E — T7E 批：`b_nfgtrans_induction`（reduction3.hl:5295）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │   b_nfgtrans_induction  reduction3.hl:5295 → bNfgtransInduction
  │ 本件是 `b_nfgtrans0` 的 SUC 归纳步：由 i 步状态锁（末弧 = `ztrans (i-1)`）
  │ 给出 i+1 步状态 = `splitFace g' y_i z_i f' newVs`。T12B 的
  │ `t12_prebatch_suc_explicit`（20ff7dd7 落库）解除了本件的最后门禁。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字）───────────────────────────────────
  │ ① `is_restricted (hypermap_of_list L)` ↦ `(hypermapOfList L hgood).IsRestricted`
  │    （链侧 `hypermapOfList` 吃 hgood；hgood 即 `good_list L`）。
  │ ② `iota (countVertices g') n = newVs` ↦ `List.range' g'.countVertices n = newVs`
  │    （树内 iota 即 range'，无桥）。
  │ ③ `PRE i` ↦ `i - 1`；`PRE (SUC i)` ↦ `i`（`arith` 折算，HOL 证体中亦即时用）。
  │ ④ `SND (splitFace ...)` ↦ `(splitFace ...).2`（`Face × Face × Graph` 右结合，
  │    状态形 `((Option ℕ × ℕ) × Face × Graph)` 逐字同）。
  │ ⑤ `~final_list L r` ↦ `¬ finalList L r`；`finals` 不出现。
  │ ⑥ 无 hfinal 条件槽（本件不消费 TAV2/J2；纯 b_nfgtrans0 步进）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（HOL 逐句）────────────────────────────────────────────
  │ `b_nfgtrans_suc`（T12C）→ `batch_nil_prebatch_nil`（T13）消前提；
  │ `dest_triple0_rcons_paired`（T12）展开 rcons；
  │ `prebatch_batch`（rfl）+ `batch_nonnil`（T13）消首 if；
  │ `the_last_last_prebatch`（T13）把 u0 定到 `ztrans (i-1)`；
  │ 三分支（u0=y / nextEl u0=y / betwn 段）分别用
  │ `subdivSingleStepNseg`（T5B）、`subdivSingleStepBetwn`（T5C）、
  │ `nextVertexNextEl`、`prevEl_mem_of_mem`/`nextEl_prevEl` 收口；
  │ 末步 `t7e_step_split`：`next_el y ≠ z ∨ n ≠ 0`（hnot）排除免拆分并
  │ 以 `hnewVs` 对齐 `ws`。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `t7e_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm13
import Kepler.Text.Reduction3Thm12B
import Kepler.Text.Reduction3Thm12C
import Kepler.Text.Reduction3Thm5C

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts)
open Kepler.Graphs (Face Graph between fgraph splitFace)
open Kepler.Text.Reduction5 (Dart finalList transformCount ytrans ztrans)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList nextEl_prevEl prevEl_mem_of_mem)
open Kepler.Text.ChainLists (markedList)

/-! ## §0 私有步进件（末 `some` 的拆分判定） -/

/-- `some u` 且计数 `n` 时，若 `nextVertex u = v ∧ n = 0` 不成立，则
`subdivSingleStep` 走 `splitFace` 支，且 `ws` 由 `range'` 等式对齐到 `newVs`。 -/
private theorem t7e_step_split (f : Face) (g : Graph) (u v n : ℕ) (newVs : List ℕ)
    (hmem : u ∈ f.vertices)
    (hnot : ¬ (nextEl f.vertices u = v ∧ n = 0))
    (hws : List.range' g.countVertices n = newVs) :
    subdivSingleStep ((some u, n), f, g) (some v) =
      ((some v, 0), (splitFace g u v f newVs).2) := by
  unfold subdivSingleStep
  dsimp only
  by_cases hc : f.nextVertex u == v && n == 0
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
    exact absurd
      ⟨by rw [← Kepler.Text.TameSpine.nextVertexNextEl hmem]; exact beq_iff_eq.mp h1,
        beq_iff_eq.mp h2⟩
      hnot
  · rw [if_neg hc]
    rw [hws]

/-! ## §A `b_nfgtrans_induction`（reduction3.hl:5295） -/

/-- HOL `b_nfgtrans_induction`（reduction3.hl:5295）：
`good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧ ¬final_list L r ∧
is_restricted (hypermap_of_list L) ∧ uniq (FST f) ∧ uniq (FST f') ∧
¬(next_el f' y_i = z_i ∧ sizel (betwn (find_face L x) y_i z_i) = 0) ∧
(z_{i-1} ≠ y_i → betwn f z_{i-1} y_i = betwn f' z_{i-1} y_i) ∧
(next_el f' z_{i-1} = y_i ↔ next_el f z_{i-1} = y_i) ∧
四个 ∀j<k 的 MEM 前提 ∧ 0 < i ∧ i < k ∧
iota (countVertices g') (sizel (betwn …)) = newVs ∧
b_nfgtrans0 f g L N r x i = ((SOME z_{i-1},0),f',g') ⇒
b_nfgtrans0 f g L N r x (SUC i) =
((SOME z_i,0), SND (splitFace g' y_i z_i f' newVs))`。 -/
theorem bNfgtransInduction (i : ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (f : Face) (g : Graph) (newVs : List ℕ)
    (f' : Face) (g' : Graph)
    (hgood : GoodList L) (hgn : GoodListNodesTl L hgood)
    (hm : markedList L hgood N r x) (hnf : ¬ finalList L r)
    (hir : (hypermapOfList L hgood).IsRestricted)
    (hunf : f.vertices.Nodup) (hunf' : f'.vertices.Nodup)
    (hnot : ¬ (nextEl f'.vertices (ytrans L N r x i).1 = (ztrans L N r x i).1 ∧
      (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length = 0))
    (hbet : (ztrans L N r x (i - 1)).1 ≠ (ytrans L N r x i).1 →
      between f.vertices (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1 =
        between f'.vertices (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1)
    (hnextiff : nextEl f'.vertices (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1 ↔
      nextEl f.vertices (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1)
    (hyf : ∀ j, j < transformCount L N r x → (ytrans L N r x j).1 ∈ f.vertices)
    (hzf : ∀ j, j < transformCount L N r x → (ztrans L N r x j).1 ∈ f.vertices)
    (hyf' : ∀ j, j < transformCount L N r x → (ytrans L N r x j).1 ∈ f'.vertices)
    (hzf' : ∀ j, j < transformCount L N r x → (ztrans L N r x j).1 ∈ f'.vertices)
    (hpos : 0 < i) (hlt : i < transformCount L N r x)
    (hnewVs : List.range' g'.countVertices
      (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length = newVs)
    (hb : bNfgtrans0 f g L N r x i =
      ((some (ztrans L N r x (i - 1)).1, 0), f', g')) :
    bNfgtrans0 f g L N r x (i + 1) =
      ((some (ztrans L N r x i).1, 0),
        (splitFace g' (ytrans L N r x i).1 (ztrans L N r x i).1 f' newVs).2) := by
  have him1 : i - 1 < transformCount L N r x := by omega
  -- 0. 三条 T13 前提槽
  have hpre : batch0 f.vertices L N r x i = [] → prebatch f.vertices L N r x i = [] :=
    batchNilPrebatchNil (fun _ => True) (fun _ => True) (fun _ _ _ _ => True)
      i f.vertices L N r x hgood trivial trivial hnf trivial hunf hyf hzf hlt
  have hbn : batch0 f.vertices L N r x i ≠ [] :=
    batchNonnil (fun _ => True) (fun _ => True) (fun _ _ _ _ => True)
      i f.vertices L N r x hgood trivial trivial hnf trivial hunf hyf hzf hpos hlt
  have hlast : (((prebatch f.vertices L N r x i).getLastD []).getLastD none).getD 0
      = (ztrans L N r x (i - 1)).1 :=
    theLastLastPrebatch (fun _ => True) (fun _ => True) (fun _ _ _ _ => True)
      i f.vertices L N r x hgood trivial trivial hnf trivial hunf hyf hzf hpos hlt
  -- 1. suc 步 + 状态锁
  rw [t12c_b_nfgtrans_suc i f g L N r x hgood hgn hir hm hnf hlt hpre, hb]
  -- 2. rcons 展开 + 扁平空判定 + 末段末元
  rw [t12_destTriple0RconsPaired]
  dsimp only
  rw [t12_prebatch_batch, if_neg hbn, hlast]
  -- 3. 三分支
  have hyi : (ytrans L N r x i).1 ∈ f'.vertices := hyf' i hlt
  have hu0mem : (ztrans L N r x (i - 1)).1 ∈ f'.vertices := hzf' (i - 1) him1
  by_cases h1 : (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1
  · -- 支 1：u0 = y，末段 = nseq n ++ [some z]
    rw [if_pos h1, h1]
    rw [List.foldl_append, subdivSingleStepNseg]
    rw [List.foldl_cons, List.foldl_nil, Nat.add_zero]
    exact t7e_step_split f' g' _ _ _ newVs hyi hnot hnewVs
  · rw [if_neg h1]
    by_cases h2 : nextEl f.vertices (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1
    · -- 支 2：nextEl u0 = y，末段 = [some y] ++ nseq n ++ [some z]
      rw [if_pos h2]
      have hnv : f'.nextVertex (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1 := by
        rw [Kepler.Text.TameSpine.nextVertexNextEl hu0mem]
        exact hnextiff.mpr h2
      have hstep : subdivSingleStep ((some (ztrans L N r x (i - 1)).1, 0), f', g')
          (some (ytrans L N r x i).1) = ((some (ytrans L N r x i).1, 0), f', g') := by
        simp [subdivSingleStep, hnv]
      rw [List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hstep]
      rw [subdivSingleStepNseg, Nat.add_zero]
      exact t7e_step_split f' g' _ _ _ newVs hyi hnot hnewVs
    · -- 支 3：betwn 段 + [some y]（f' 侧两件由 hbet / hnextiff 转运）
      rw [if_neg h2]
      have hnextne : nextEl f'.vertices (ztrans L N r x (i - 1)).1 ≠ (ytrans L N r x i).1 :=
        fun h => h2 (hnextiff.mp h)
      rw [hbet h1]
      rw [List.foldl_append, List.foldl_append, List.foldl_append]
      rw [subdivSingleStepBetwn
        (between f'.vertices (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1)
        f' g' (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1
        hunf' rfl hu0mem hyi h1 hnextne]
      simp only [List.foldl_cons, List.foldl_nil]
      have hpv : prevEl f'.vertices (ytrans L N r x i).1 ∈ f'.vertices :=
        prevEl_mem_of_mem hyi
      have hnv : f'.nextVertex (prevEl f'.vertices (ytrans L N r x i).1)
          = (ytrans L N r x i).1 := by
        rw [Kepler.Text.TameSpine.nextVertexNextEl hpv]
        exact nextEl_prevEl hunf' hyi
      have hstep : subdivSingleStep
          ((some (prevEl f'.vertices (ytrans L N r x i).1), 0), f', g')
          (some (ytrans L N r x i).1) = ((some (ytrans L N r x i).1, 0), f', g') := by
        simp [subdivSingleStep, hnv]
      rw [hstep]
      rw [subdivSingleStepNseg, Nat.add_zero]
      exact t7e_step_split f' g' _ _ _ newVs hyi hnot hnewVs

end Kepler.Text.Reduction3

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.bNfgtransInduction
