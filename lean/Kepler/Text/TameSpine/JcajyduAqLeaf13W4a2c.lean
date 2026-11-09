/- JcajyduAqLeaf13W4a2c — AQ13 y=z1 支：p∈parts r / LAST r 两个定位分件。0 禁词。 -/
import Kepler.Text.TameSpine.JcajyduAqLeaf13W4a2b
import Kepler.Text.TameSpine.JcajyduAqLeaf12B

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Kepler.Text.TameSpine
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList)

private theorem aq13w4a2c_getLast!_mem {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  simp

/-- **y=z1 · p∈parts r 分件**：p、p1 同为 r 的 part 且共享 y ⇒ p1 末元 = y。
（y=z1 支「p∈parts r」子支的精确闭合件。） -/
theorem aq13w4a2c_lastOfPartOfMemParts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r p p1 : List (ℕ × ℕ)} {y : ℕ × ℕ}
    (hn : NormalListSpine hL N) (hrN : r ∈ N)
    (hp : p ∈ partsSpine L r) (hp1 : p1 ∈ partsSpine L r)
    (hyp : y ∈ p) (hyp1 : y ∈ p1) (hylast : y = p.getLast!) :
    p1.getLast! = y := by
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hn hrN
  have hflat : (partsSpine L r).flatten.Nodup := by
    rw [partsFlatten L hrnd hrne]; exact hrnd
  have heq : p = p1 :=
    uniqSublistUnique (partsSpine L r) hflat p hp p1 hp1 ⟨y, hyp, hyp1⟩
  rw [← heq]; exact hylast.symm

/-- **y=z1 · LAST p=LAST r 分件**：p1 含 r 末元 y ⇒ p1 末元 = y。
（HOL 1452-1464 的 `LAST_parts` 组合的 Lean 收口。） -/
theorem aq13w4a2c_lastOfPartOfLast (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r p1 : List (ℕ × ℕ)} {y : ℕ × ℕ}
    (hn : NormalListSpine hL N) (hrN : r ∈ N)
    (hp1 : p1 ∈ partsSpine L r) (hyp1 : y ∈ p1) (hyr : y = r.getLast!) :
    p1.getLast! = y := by
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hn hrN
  have hpartsne : partsSpine L r ≠ [] := partsNonnil L hrnd hrne
  set p2 := (partsSpine L r).getLast! with hp2
  have hp2mem : p2 ∈ partsSpine L r := aq13w4a2c_getLast!_mem hpartsne
  have hp2last : p2.getLast! = r.getLast! := aqs_lastParts L hL hn hrN rfl
  have hp2ne : p2 ≠ [] := (partsUniqNonnil L hL hn hrN hp2mem).2.2.2.1
  have hy2 : y ∈ p2 := by
    rw [hyr, ← hp2last]; exact aq13w4a2c_getLast!_mem hp2ne
  have hflat : (partsSpine L r).flatten.Nodup := by
    rw [partsFlatten L hrnd hrne]; exact hrnd
  have heq : p1 = p2 :=
    uniqSublistUnique (partsSpine L r) hflat p1 hp1 p2 hp2mem ⟨y, hyp1, hy2⟩
  rw [heq, hp2last, hyr]

#print axioms Kepler.Text.TameSpine.aq13w4a2c_lastOfPartOfMemParts
#print axioms Kepler.Text.TameSpine.aq13w4a2c_lastOfPartOfLast
