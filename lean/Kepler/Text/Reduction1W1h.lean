/-
  Kepler.Text.Reduction1W1h — J4 Wave W1 批 5b 第二件：`duplicateEdge_next`
  （HOL `reduction1.hl:287-:317`，31 行；编排者按车道冻结包 `DELIVERY_W1H.md`
  收口，2026-11-10）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ reduction1.hl:287-:317 `duplicateEdge_next` → §3 duplicateEdgeNext
  │   （`duplicateEdge g f v w <=> v≠w ∧ w≠next_el (FST f) v
  │    ∧ v≠next_el (FST f) w ∧ MEM (v,w) (list_of_darts (fgraph g))`）。
  │ §1 私有 `nextVertexEqNextEl`：`Face.nextVertex`（nextElem 载体）
  │    与 `next_el`（seq2 载体）在 Nodup + 成员下逐点相等——本版无公开桥。
  │ §2 私有 `dldTwoIff`：`2 ≤ directedLength f v w ↔ v≠w ∧ nextEl v≠w`。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS / 路线说明 ───────────────────────────────────────────────
  │ ① `next_el (FST f) x` 在 §3 仍以 `f.nextVertex x` 呈现（冻结包约定）；
  │    §1 提供与 `nextEl f.vertices` 的双向点桥，两侧都可用。
  │ ② `duplicateEdge g f v w`（Bool）↦ `… = true`，`decide_eq_true_iff`
  │    转 Prop；Bool 合取由 decide 整体吸收（无需 Bool.and_eq_true 逐拆）。
  │ ③ `MEM (FST f) (fgraph g)`（hfm）唯一用途 = 由
  │    `VerticesSet2Eq g` 把 `v ∈ f.vertices` 提升到 `v ∈ verticesSet2 g`，
  │    以喂 `dartNeighbors` 的左侧顶点前提（HOL 同一路径）。
  │ ④ `2 ≤ directedLength` 的双向拆解走 §2（`betwnNil` 定义方程 +
  │    `2 ≤ l+1 ↔ l ≠ 0`），与车道冻结包 §4 的 `dld_two_iff` 同内容；
  │    未消费 `TameList53.directedLengthNext`（其结论是 A∧B ↔ C 形，
  │    单半 A 不可用）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W1g
import Kepler.Text.TameSpine.TameList53
import Kepler.Graphs.Plane

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (nextEl listOfDarts)
open Kepler.Graphs (Face Graph Vertex between is_nextElem is_sublist)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq verticesSet2)

/-! ## §1 `nextVertex` ↔ `next_el` 点桥（本版无公开件） -/

/-- 界内 `getElem!` 与 `getElem` 逐点相等（W1f `getElemBangH` 同款私件）。 -/
private theorem getElemBangH {α : Type} [Inhabited α] {l : List α} {i : ℕ}
    (h : i < l.length) : l[i]! = l[i]'h := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp

/-- **`nextVertex` ↔ `next_el` 点桥**：`f.nextVertex v = next_el (FST f) v`
在 `Nodup` + 成员下成立。路线：`nextElem_is_nextElem` 把 `nextElem` 侧化为
`is_nextElem`；`nextEl` 侧按 `idxOf` 末位/非末位二分构造 `is_nextElem`：
非末位 = 连续子列（`take i ++ [v, s[i+1]] ++ drop (i+2)`），
末位 = 回卷析取支（`v = getLast!` 且 `nextEl = head!`）。 -/
private theorem nextVertexEqNextEl {α : Type} [BEq α] [LawfulBEq α] [Inhabited α]
    {s : List α} {v : α} (hnd : s.Nodup) (hv : v ∈ s) :
    Kepler.Graphs.nextElem s s.head! v = nextEl s v := by
  have hmain : is_nextElem s v (nextEl s v) := by
    rcases s with _ | ⟨a, as⟩
    · exact absurd hv (by simp)
    · have hi : (a :: as).idxOf v < (a :: as).length :=
        List.idxOf_lt_length_iff.mpr hv
      have hsi : (a :: as)[(a :: as).idxOf v]'hi = v := List.getElem_idxOf hi
      by_cases hlast : (a :: as).idxOf v = (a :: as).length - 1
      · -- 末位支：nextEl = headD = head!；回卷析取
        have hnext : nextEl (a :: as) v = (a :: as).headD v := by
          unfold nextEl
          rw [if_pos hlast]
        have hgl : v = (a :: as).getLast! := by
          rw [List.getLast!_eq_getElem!, ← hlast]
          exact ((getElemBangH hi).trans hsi).symm
        have hhd : nextEl (a :: as) v = (a :: as).head! := by
          rw [hnext]
          rfl
        exact Or.inr ⟨List.cons_ne_nil a as, hgl, hhd⟩
      · -- 非末位支：连续子列
        have hlt : (a :: as).idxOf v + 1 < (a :: as).length := by
          have := hi
          omega
        have hnext : nextEl (a :: as) v = (a :: as).getD ((a :: as).idxOf v + 1) v := by
          unfold nextEl
          rw [if_neg hlast]
        have hget : (a :: as).getD ((a :: as).idxOf v + 1) v
            = (a :: as)[(a :: as).idxOf v + 1]'hlt :=
          List.getD_eq_getElem _ _ hlt
        have hd1 : (a :: as).drop ((a :: as).idxOf v)
            = (a :: as)[(a :: as).idxOf v]'hi :: (a :: as).drop ((a :: as).idxOf v + 1) :=
          List.drop_eq_getElem_cons hi
        have hd2 : (a :: as).drop ((a :: as).idxOf v + 1)
            = (a :: as)[(a :: as).idxOf v + 1]'hlt
              :: (a :: as).drop ((a :: as).idxOf v + 2) :=
          List.drop_eq_getElem_cons hlt
        refine Or.inl ⟨(a :: as).take ((a :: as).idxOf v),
          (a :: as).drop ((a :: as).idxOf v + 2), ?_⟩
        conv_lhs => rw [← List.take_append_drop ((a :: as).idxOf v) (a :: as)]
        rw [hd1, hd2, hsi, hnext, hget]
        conv_rhs => rw [List.append_assoc]
        rfl
  exact (Kepler.Graphs.nextElem_is_nextElem hnd hv).mp hmain

/-! ## §2 `directedLength` 两倍下界（HOL 冻结包 §4 同内容） -/

/-- **`2 ≤ directedLength f v w ↔ v ≠ w ∧ nextEl f.vertices v ≠ w`**。
`v = w` 支定义性归零；`v ≠ w` 支 `directedLength = |between| + 1`，
`2 ≤ l+1 ↔ l ≠ 0`，再经 `betwnNil`（`:13449` 真证件）双向翻译到
`nextEl` 等式。 -/
private theorem dldTwoIff {f : Face} {v w : Vertex}
    (hnd : f.vertices.Nodup) (hv : v ∈ f.vertices) (hw : w ∈ f.vertices) :
    2 ≤ Kepler.Graphs.directedLength f v w ↔ v ≠ w ∧ nextEl f.vertices v ≠ w := by
  by_cases hab : v = w
  · rw [hab] at *
    simp [Kepler.Graphs.directedLength]
  · have hd : Kepler.Graphs.directedLength f v w
        = (between f.vertices v w).length + 1 := by
      simp [Kepler.Graphs.directedLength, hab]
    have hbn : between f.vertices v w = [] ↔ w = nextEl f.vertices v :=
      Kepler.Text.TameSpine.betwnNil hnd hab hv hw
    constructor
    · intro h2
      refine ⟨hab, ?_⟩
      intro he
      have hnil : between f.vertices v w = [] := hbn.mpr he.symm
      rw [hd, List.length_eq_zero_iff.mpr hnil] at h2
      omega
    · rintro ⟨_, hne⟩
      have hn0 : (between f.vertices v w).length ≠ 0 := by
        intro h0
        exact hne (hbn.mp (List.length_eq_zero_iff.mp h0)).symm
      rw [hd]
      omega

/-! ## §3 `duplicateEdge_next`（reduction1.hl:287-:317） -/

/-- **HOL `duplicateEdge_next`**：`duplicateEdge g f v w` 成立当且仅当
`v ≠ w`、`w` 不是 `v` 的后继、`v` 不是 `w` 的后继、且 `(v,w)` 是图的一条 dart。
路线：`decide_eq_true_iff` 转 Prop → §2 两次（v→w / w→v）→ §1 两次
→ `dartNeighbors`（`e24bb3be`）消去 `w ∈ neighbors g v`。 -/
theorem duplicateEdgeNext {g : Graph} {f : Face} {v w : Vertex}
    (hnd : f.vertices.Nodup)                      -- uniq (FST f)
    (hv : v ∈ f.vertices)                         -- MEM v (FST f)
    (hw : w ∈ f.vertices)                         -- MEM w (FST f)
    (hfm : f.vertices ∈ g.fgraph)                 -- MEM (FST f) (fgraph g)
    (hun : ∀ l ∈ g.fgraph, l.Nodup)               -- all uniq (fgraph g)
    (hgf : GoodFacesV3 g)                         -- good_faces_v3 g
    (hvs : VerticesSet2Eq g) :                    -- vertices_set2 g = elements_of_list (fgraph g)
    (Kepler.Graphs.duplicateEdge g f v w = true ↔
      v ≠ w ∧ f.nextVertex v ≠ w ∧ f.nextVertex w ≠ v ∧
      (v, w) ∈ listOfDarts g.fgraph) := by
  -- 顶点提升：v ∈ verticesSet2 g（hfm + hvs）
  have hvfl : v ∈ g.fgraph.flatten := List.mem_flatten.mpr ⟨f.vertices, hfm, hv⟩
  have hve : v ∈ Kepler.Text.TameLp.elementsOfList g.fgraph := by
    simp only [Kepler.Text.TameLp.elementsOfList, Set.mem_setOf_eq]
    exact List.mem_eraseDups.mpr hvfl
  have hvset : v ∈ verticesSet2 g := by
    rw [hvs]
    exact hve
  -- dartNeighbors 消去 neighbors（左侧顶点前提已给）
  have hD : w ∈ Kepler.Graphs.neighbors g v ↔ (v, w) ∈ listOfDarts g.fgraph := by
    constructor
    · intro hwv
      exact (dartNeighbors hun hgf hvs).mp ⟨hvset, hwv⟩
    · intro hd
      exact ((dartNeighbors hun hgf hvs).mpr hd).2
  have hA := dldTwoIff hnd hv hw
  have hB := dldTwoIff hnd hw hv
  have hV : f.nextVertex v = nextEl f.vertices v := nextVertexEqNextEl hnd hv
  have hW : f.nextVertex w = nextEl f.vertices w := nextVertexEqNextEl hnd hw
  simp only [Kepler.Graphs.duplicateEdge, decide_eq_true_iff]
  rw [hA, hB, hD, hV, hW]
  constructor
  · rintro ⟨⟨hvne, hvn⟩, ⟨hwn, hwn'⟩, hd⟩
    exact ⟨hvne, hvn, hwn', hd⟩
  · rintro ⟨hvne, hvn, hwn, hd⟩
    exact ⟨⟨hvne, hvn⟩, ⟨⟨fun e => hvne e.symm, hwn⟩, hd⟩⟩

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三、零未证公理） -/
#print axioms Kepler.Text.Reduction1.duplicateEdgeNext
