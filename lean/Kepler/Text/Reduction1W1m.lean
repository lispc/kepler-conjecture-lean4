/-
  Kepler.Text.Reduction1W1m — J4 Wave W1 批 6 §3（编排者按车道冻结包
  `DELIVERY_W1M_S3_FROZEN.md` 收口，2026-11-10）：
  `containsUnacceptableDuplicateEdge_explicit`（HOL `reduction1.hl:1035-:1149`，115 HOL）。

  ┌─ 路线 ─────────────────────────────────────────────────────────
  │ S1 长度：`e.length = vs.length`（`sizeEnumOfVertexList`）。
  │ S2/S3：§2 `containsUnacceptableEdgeExplicit`（`96e487c1`）把目标化为
  │   `¬(2 ≤ e.length ∧ (A ∨ B))`，A = 首项对支，B = 三元组 ∃ 支。
  │ S5 ¬A：`e[0]! = indexf v v F = 0`；`vs[1]` 非 some ⇒ carried ⇒ e1 = e0；
  │   `vs[1]` some ⇒ P11 @0（配 `duplicateEdgeNext` `94c5389c`）。
  │ S6 ¬B：由 `e[i]≠e[i+1]`、`e[i+1]≠e[i+2]` 与 carried 结构反推
  │   `vs[i+1]`/`vs[i+2]` 必 some（`showDups0SucEqOfNone` 逆否），
  │   再 P11 @(i+1) + `duplicateEdgeNext`。
  └────────────────────────────────────────────────────────────────

  ┌─ ERRATA（相对冻结包，按 HOL 原文修正）───────────────────────────
  │ 冻结包 P11 代码块第二、三合取重复写成 `nextVertex u2 ≠ u1` 的两种
  │ 换向（同一命题）；HOL 原文（`:1064` 附近）是
  │ `~(u1 = next_el u2) /\ ~(u2 = next_el u1)` ⇒ 第三合取应为
  │ **`f.nextVertex u1 ≠ u2`**（包内注记「第三条方向要翻转」也如此说）。
  │ 本文件按 HOL 原文落 P11 第三合取；其余 18 前提与包逐字一致。
  └────────────────────────────────────────────────────────────────

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
  DIFFERS：`EL` ↦ `getElem!`；`the` ↦ `Option.get!`；`sizel` ↦ `List.length`；
  `uniq` ↦ `Nodup`；`N i j` 当 Prop ↦ `= true`；全程 `Nat`。
-/
import Kepler.Text.Reduction1W1l
import Kepler.Text.Reduction1W1h
import Kepler.Text.Reduction1W1e
import Kepler.Text.TameSpine.TameList4

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (nextEl listOfDarts)
open Kepler.Graphs (Face Graph Vertex containsUnacceptableEdge duplicateEdge)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq)
open Kepler.Text.TameSpine (showDups showDups0 enumOfVertexList indexf)

/-! ## §0 通用私件 -/

/-- 界内 `getElem!` 与依赖式 `getElem` 同值（W1f `getElemBangH` 同款）。 -/
private theorem getElemBangH {α : Type} [Inhabited α] {l : List α} {i : Nat}
    (h : i < l.length) : l[i]! = l[i]'h := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp

/-- `map` 的 `getElem!` 取值（`List.getElem!_map` 树内 0 命中）。 -/
private theorem getElemBangMap {α β : Type} [Inhabited α] [Inhabited β]
    {l : List α} {g : α → β} {i : Nat} (h : i < l.length) :
    (l.map g)[i]! = g (l[i]!) := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp only [Option.map_some, Option.getD_some]
  rw [getElemBangH h]

/-- `o` 为 some 时等于 `some o.getD 0`。 -/
private theorem eqSomeGetD {o : Option Nat} (h : o.isSome = true) :
    o = some (o.getD 0) := by
  cases o with
  | none => simp at h
  | some x => rfl

/-- some 元素落在 `(vs.filter isSome).map get!` 里。 -/
private theorem memFilterMapOfSome {vs : List (Option Nat)} {k u : Nat}
    (hk : k < vs.length) (h : vs[k]! = some u) :
    u ∈ (vs.filter Option.isSome).map Option.get! := by
  have hmem : some u ∈ vs := by
    have h1 : vs[k]! ∈ vs := by
      have h2 : vs[k] ∈ vs := List.getElem_mem hk
      rwa [← getElemBangH hk] at h2
    rwa [h] at h1
  exact List.mem_map.mpr ⟨some u, List.mem_filter.mpr ⟨hmem, by simp⟩, rfl⟩

/-! ## §1 `showDups0` 的 carried 结构 -/

/-- `showDups0` 首元：头为 `none` 时取携带默认 `a`。 -/
private theorem showDups0HeadNone {bs : List (Option Nat)} {a : Nat}
    (hbs : bs ≠ []) (h : bs[0]! = none) : (showDups0 a bs)[0]! = a := by
  cases bs with
  | nil => exact absurd rfl hbs
  | cons c cs =>
    cases c with
    | none => rw [showDups0, List.getElem!_cons_zero]
    | some d =>
      rw [List.getElem!_cons_zero] at h
      exact absurd h (by simp)

/-- **carried 核心**：`vs[k] = none`（`k > 0`）⇒ `showDups0 a vs` 在 `k` 与
`k-1` 两位取值相等（`none` 位携带前一值）。 -/
private theorem showDups0SucEqOfNone : ∀ (vs : List (Option Nat)) (a k : Nat),
    0 < k → k < vs.length → vs[k]! = none →
      (showDups0 a vs)[k]! = (showDups0 a vs)[k - 1]! := by
  intro vs
  induction vs with
  | nil => intro a k hk hlt; simp at hlt
  | cons b bs ih =>
    intro a k hk hlt hnone
    cases k with
    | zero => omega
    | succ k' =>
      have hnone' : bs[k']! = none := by
        have h1 : (b :: bs)[k' + 1]! = bs[k']! := List.getElem!_cons_succ
        rwa [h1] at hnone
      have hlt' : k' < bs.length := by
        simp only [List.length_cons] at hlt; omega
      have hbs : bs ≠ [] := by
        intro c; rw [c] at hlt'; simp at hlt'
      cases k' with
      | zero =>
        cases b with
        | none =>
          rw [showDups0]
          exact showDups0HeadNone hbs hnone'
        | some c =>
          rw [showDups0]
          exact showDups0HeadNone hbs hnone'
      | succ j =>
        have hih := ih a (j + 1) (by omega) (by omega) hnone'
        cases b with
        | none =>
          rw [showDups0]
          rw [List.getElem!_cons_succ, show j + 1 + 1 - 1 = j + 1 from by omega,
            List.getElem!_cons_succ]
          simpa using hih
        | some c =>
          rw [showDups0]
          rw [List.getElem!_cons_succ, show j + 1 + 1 - 1 = j + 1 from by omega,
            List.getElem!_cons_succ]
          simpa using (ih c (j + 1) (by omega) (by omega) hnone')

/-! ## §2 主定理 -/

/-- **HOL `containsUnacceptableDuplicateEdge_explicit`**（`reduction1.hl:1035-:1149`）：
`e = enumOfVertexList F v vs`、单调、无「可接受重边」对 ⇒ `containsUnacceptableEdge`
（谓词 = `duplicateEdge` 经 `nextVertices · v` 拉回）为假。P11 第三合取按 HOL
原文修正为 `f.nextVertex u1 ≠ u2`（见头注 ERRATA）。 -/
theorem containsUnacceptableDuplicateEdgeExplicit {g : Graph} {f : Face} {e : List Nat}
    {v : Nat} {vs : List (Option Nat)}
    (hmonoE : ∀ i, i + 1 < e.length → e[i]! ≤ e[i + 1]!)
    (he : e = enumOfVertexList f.vertices v vs)
    (h2vs : 2 ≤ vs.length)
    (hfm : f.vertices ∈ g.fgraph) (hun : ∀ l ∈ g.fgraph, l.Nodup) (hnd : f.vertices.Nodup)
    (hall : ∀ t ∈ (vs.filter Option.isSome).map Option.get!, t ∈ f.vertices)
    (hgf : GoodFacesV3 g) (hvs : VerticesSet2Eq g) (hhd : vs.head! = some v)
    (hnoDup : ¬ ∃ i, i + 1 < vs.length ∧ (vs[i]!).isSome = true ∧
      (vs[i + 1]!).isSome = true ∧
      (vs[i]!.getD 0 ≠ (vs[i + 1]!.getD 0) ∧
       f.nextVertex (vs[i + 1]!.getD 0) ≠ (vs[i]!.getD 0) ∧
       f.nextVertex (vs[i]!.getD 0) ≠ (vs[i + 1]!.getD 0) ∧
       ((vs[i]!.getD 0), (vs[i + 1]!.getD 0)) ∈ listOfDarts g.fgraph)) :
    (containsUnacceptableEdge
      (fun i j => duplicateEdge g f (f.nextVertices i v) (f.nextVertices j v)) e = false) := by
  -- 基本桥
  have hEmap : e = (showDups vs).map (fun u => indexf v u f.vertices) := by
    rw [he]; rfl
  have hsd : showDups vs = showDups0 v vs := by
    cases vs with
    | nil => simp at h2vs
    | cons b bs =>
      have hb : b = some v := by simpa using hhd
      subst hb
      rfl
  have heLen : e.length = vs.length := by rw [he, Kepler.Text.TameSpine.sizeEnumOfVertexList]
  have hv0 : vs[0]! = some v := by
    have h := hhd
    rwa [List.head!_eq_getElem!] at h
  have hv0some : (vs[0]!).isSome = true := by rw [hv0]; rfl
  have hv0get : vs[0]!.getD 0 = v := by rw [hv0]; rfl
  have hvmem : v ∈ f.vertices := hall v (memFilterMapOfSome (by omega) hv0)
  -- e 在 some 位的取值
  have eGetSome : ∀ {k : Nat}, k < vs.length → (vs[k]!).isSome = true →
      e[k]! = indexf v (vs[k]!.getD 0) f.vertices := by
    intro k hk hsome
    rw [hEmap, hsd]
    exact elShowDups0 vs v v f.vertices k hk hsome
  -- e 在 none 位（k>0）与 k-1 位相等
  have eGetEqOfNone : ∀ {k : Nat}, 0 < k → k < vs.length → vs[k]! = none →
      e[k]! = e[k - 1]! := by
    intro k hk0 hk hnone
    have hlen : k < (showDups vs).length := by
      rw [Kepler.Text.TameSpine.sizeShowDups]; exact hk
    have hlenPrev : k - 1 < (showDups vs).length := by
      rw [Kepler.Text.TameSpine.sizeShowDups]; omega
    rw [hEmap, getElemBangMap hlen, getElemBangMap hlenPrev, hsd]
    rw [showDups0SucEqOfNone vs v k hk0 hk hnone]
  -- §2 消解
  have hC := containsUnacceptableEdgeExplicit
    (N := fun i j => duplicateEdge g f (f.nextVertices i v) (f.nextVertices j v)) hmonoE
  -- ¬A
  have hA : ¬ (e[0]! ≠ e[1]! ∧
      (fun i j => duplicateEdge g f (f.nextVertices i v) (f.nextVertices j v))
        e[0]! e[1]! = true) := by
    rintro ⟨hne01, hN⟩
    have he0 : e[0]! = 0 := by
      rw [eGetSome (by omega) hv0some, hv0get, Kepler.Text.TameSpine.indexfRefl hvmem]
    by_cases hsome1 : (vs[1]!).isSome = true
    · -- vs[1] some：P11 @0
      have h1lt : 1 < vs.length := by omega
      have hvs1 : vs[1]! = some (vs[1]!.getD 0) := eqSomeGetD hsome1
      have he1 : e[1]! = indexf v (vs[1]!.getD 0) f.vertices := eGetSome h1lt hsome1
      have hu2mem : vs[1]!.getD 0 ∈ f.vertices :=
        hall _ (memFilterMapOfSome h1lt hvs1)
      have hu2ne : v ≠ vs[1]!.getD 0 := by
        intro hvu
        exact hne01 (by rw [he0, he1, ← hvu]; exact (Kepler.Text.TameSpine.indexfRefl hvmem).symm)
      have hN' : duplicateEdge g f v (vs[1]!.getD 0) = true := by
        have h := hN
        rw [he0, he1] at h
        dsimp only at h
        rw [Kepler.Text.TameSpine.nextVerticesZero,
          Kepler.Text.TameSpine.nextVerticesIndexf (w := vs[1]!.getD 0) hvmem hu2mem hnd] at h
        exact h
      have hd := (duplicateEdgeNext hnd hvmem hu2mem hfm hun hgf hvs).mp hN'
      exact hnoDup ⟨0, by omega, hv0some, hsome1, by
        rw [hv0get]
        exact ⟨hd.1, hd.2.2.1, hd.2.1, hd.2.2.2⟩⟩
    · -- vs[1] 非 some：carried ⇒ e1 = e0
      have hnone : vs[1]! = none := by
        cases hh : vs[1]! with
        | none => rfl
        | some x =>
          rw [hh, Option.isSome_some] at hsome1
          exact absurd rfl hsome1
      have hlt1 : 1 < vs.length := by omega
      have heq := eGetEqOfNone (k := 1) (by omega) hlt1 hnone
      have heq' : e[1]! = e[0]! := by
        rw [show (1 : Nat) - 1 = 0 from rfl] at heq
        exact heq
      exact hne01 heq'.symm
  -- ¬B
  have hB : ¬ (∃ i, i + 2 < e.length ∧ e[i]! ≠ e[i + 1]! ∧ e[i + 1]! ≠ e[i + 2]! ∧
      (fun i j => duplicateEdge g f (f.nextVertices i v) (f.nextVertices j v))
        e[i + 1]! e[i + 2]! = true) := by
    rintro ⟨i, hi2, hnei, hnei1, hNi⟩
    have hi2v : i + 2 < vs.length := by omega
    have hi1 : i + 1 < vs.length := by omega
    have hsome1 : (vs[i + 1]!).isSome = true := by
      by_cases h : (vs[i + 1]!).isSome = true
      · exact h
      · exfalso
        have hnone : vs[i + 1]! = none := by
          cases hh : vs[i + 1]! with
          | none => rfl
          | some x =>
            rw [hh, Option.isSome_some] at h
            exact absurd rfl h
        have heq := eGetEqOfNone (k := i + 1) (by omega) hi1 hnone
        rw [show i + 1 - 1 = i from by omega] at heq
        exact hnei heq.symm
    have hsome2 : (vs[i + 2]!).isSome = true := by
      by_cases h : (vs[i + 2]!).isSome = true
      · exact h
      · exfalso
        have hnone : vs[i + 2]! = none := by
          cases hh : vs[i + 2]! with
          | none => rfl
          | some x =>
            rw [hh, Option.isSome_some] at h
            exact absurd rfl h
        have heq := eGetEqOfNone (k := i + 2) (by omega) hi2v hnone
        rw [show i + 2 - 1 = i + 1 from by omega] at heq
        exact hnei1 heq.symm
    have hvs1 : vs[i + 1]! = some (vs[i + 1]!.getD 0) := eqSomeGetD hsome1
    have hvs2 : vs[i + 2]! = some (vs[i + 2]!.getD 0) := eqSomeGetD hsome2
    have he1 : e[i + 1]! = indexf v (vs[i + 1]!.getD 0) f.vertices := eGetSome hi1 hsome1
    have he2 : e[i + 2]! = indexf v (vs[i + 2]!.getD 0) f.vertices := eGetSome hi2v hsome2
    have hu1mem : vs[i + 1]!.getD 0 ∈ f.vertices :=
      hall _ (memFilterMapOfSome hi1 hvs1)
    have hu2mem : vs[i + 2]!.getD 0 ∈ f.vertices :=
      hall _ (memFilterMapOfSome hi2v hvs2)
    have hu12 : vs[i + 1]!.getD 0 ≠ vs[i + 2]!.getD 0 := by
      intro hEq
      exact hnei1 (by rw [he1, he2, hEq])
    have hNi' : duplicateEdge g f (vs[i + 1]!.getD 0) (vs[i + 2]!.getD 0) = true := by
      have h := hNi
      rw [he1, he2] at h
      dsimp only at h
      rw [Kepler.Text.TameSpine.nextVerticesIndexf (w := vs[i + 1]!.getD 0) hvmem hu1mem hnd,
        Kepler.Text.TameSpine.nextVerticesIndexf (w := vs[i + 2]!.getD 0) hvmem hu2mem hnd] at h
      exact h
    have hd := (duplicateEdgeNext (g := g) (f := f) (v := vs[i + 1]!.getD 0)
      (w := vs[i + 2]!.getD 0) hnd hu1mem hu2mem hfm hun hgf hvs).mp hNi'
    exact hnoDup ⟨i + 1, by omega, hsome1, hsome2, by
      exact ⟨hd.1, hd.2.2.1, hd.2.1, hd.2.2.2⟩⟩
  -- 合流
  have hNotOr : ¬ ((e[0]! ≠ e[1]! ∧
        (fun i j => duplicateEdge g f (f.nextVertices i v) (f.nextVertices j v))
          e[0]! e[1]! = true) ∨
      (∃ i, i + 2 < e.length ∧ e[i]! ≠ e[i + 1]! ∧ e[i + 1]! ≠ e[i + 2]! ∧
        (fun i j => duplicateEdge g f (f.nextVertices i v) (f.nextVertices j v))
          e[i + 1]! e[i + 2]! = true)) :=
    fun h => h.elim hA hB
  have hne : containsUnacceptableEdge
      (fun i j => duplicateEdge g f (f.nextVertices i v) (f.nextVertices j v)) e ≠ true := by
    intro h
    exact hNotOr (hC.mp h).2
  cases hCval : containsUnacceptableEdge
      (fun i j => duplicateEdge g f (f.nextVertices i v) (f.nextVertices j v)) e with
  | false => rfl
  | true => exact absurd hCval hne

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三、零未证公理） -/
#print axioms Kepler.Text.Reduction1.containsUnacceptableDuplicateEdgeExplicit
