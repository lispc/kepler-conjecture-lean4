/-
  Kepler.Text.Reduction5J5UvnsChainCl — U1b：走行分类三件套（U 段第二小波）。
  `ChainCl f D l`（相邻 Some 项 ⇒ `nextEl f` 相邻 ∨ `D a b`）+ 三段保持引理。
  消费 nb56 getD 五件；`sizeBetwnChainPub` 私落（`Thm6C:55` 同名件 private）。

  纪律：零公理、零占位证明；私有重落（不改既有文件）。
-/

import Kepler.Text.Reduction5J5UvnsGetD
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.Reduction3Thm6B

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Assembly (nextEl)
open Kepler.Graphs (between)

/-- 走行分类谓词（相邻 Some 项 `nextEl f` 相邻，或落入分类谓词 `D`）。 -/
def ChainCl (f : List ℕ) (D : ℕ → ℕ → Prop) (l : List (Option ℕ)) : Prop :=
  ∀ j : ℕ, j + 1 < l.length → (l.getD j none).isSome → (l.getD (j + 1) none).isSome →
    nextEl f ((l.getD j none).getD 0) = (l.getD (j + 1) none).getD 0 ∨
      D ((l.getD j none).getD 0) ((l.getD (j + 1) none).getD 0)

/-- **① 首段**：`[some y] ++ nseq n none ++ [some z]` 的 `ChainCl`
（唯一可能相邻的 Some 对是 (y,z)，且仅当 `n = 0`）。 -/
theorem chainClBase (f : List ℕ) (D : ℕ → ℕ → Prop) (y z n : ℕ)
    (hdisj : n = 0 → D y z) :
    ChainCl f D ([some y] ++ List.replicate n (none : Option ℕ) ++ [some z]) := by
  intro j hj1 hs1 hs2
  cases j with
  | zero =>
    have h2 : ((List.replicate n (none : Option ℕ) ++ [some z]).getD 0 none).isSome = true := by
      simpa using hs2
    rw [uvnsGetDRepZV] at h2
    by_cases hn : n = 0
    · right
      simpa [hn, uvnsGetDRepZV] using hdisj hn
    · exfalso
      rw [if_neg (by omega : (0 : ℕ) ≠ n)] at h2
      simp at h2
  | succ k =>
    have h1 : ((List.replicate n (none : Option ℕ) ++ [some z]).getD k none).isSome = true := by
      simpa using hs1
    have h2 : ((List.replicate n (none : Option ℕ) ++ [some z]).getD (k + 1) none).isSome = true := by
      simpa using hs2
    rw [uvnsGetDRepZV] at h1 h2
    by_cases e1 : k = n
    · by_cases e2 : k + 1 = n
      · rw [if_pos e1] at h1
        rw [if_pos e2] at h2
        omega
      · rw [if_neg e2] at h2
        simp at h2
    · rw [if_neg e1] at h1
      simp at h1

/-- **② 纯 Nones 追加**（destTriple0 步进 case `u0 = u`）：
`pfx ++ nseq n none ++ [some z]` 的 `ChainCl`；跨越对仅当 `n = 0`，由 `D w z` 收口。
`hlastD` 是「pfx 末位取值为 w」的接口（调用方由 `getLastD` 供）。 -/
theorem chainClNsAppend (f : List ℕ) (D : ℕ → ℕ → Prop)
    (pfx : List (Option ℕ)) (w zv n : ℕ)
    (hcl : ChainCl f D pfx)
    (hlastD : ∀ j, j + 1 = pfx.length → (pfx.getD j none).getD 0 = w)
    (hdisj : n = 0 → D w zv) :
    ChainCl f D (pfx ++ (List.replicate n (none : Option ℕ) ++ [some zv])) := by
  intro j hj1 hs1 hs2
  simp only [uvnsGetDAppend (l := pfx) (m := List.replicate n (none : Option ℕ) ++ [some zv]) (j := j),
    uvnsGetDAppend (l := pfx) (m := List.replicate n (none : Option ℕ) ++ [some zv]) (j := j + 1)]
    at hs1 hs2 ⊢
  by_cases hj : j + 1 < pfx.length
  · simp only [dif_pos (by omega : j < pfx.length), dif_pos hj] at hs1 hs2 ⊢
    exact hcl j hj hs1 hs2
  · by_cases hje : j + 1 = pfx.length
    · -- 跨越对：pfx 末元 w × app 首项（仅 n=0 时 = some zv）
      simp only [dif_pos (by omega : j < pfx.length), dif_neg (by omega : ¬ j + 1 < pfx.length),
        show j + 1 - pfx.length = 0 from by omega] at hs1 hs2 ⊢
      have hw : (pfx.getD j none).getD 0 = w := hlastD j hje
      rw [uvnsGetDRepZV] at hs2
      by_cases hn : n = 0
      · right
        rw [hw]
        have hb : ((List.replicate n (none : Option ℕ) ++ [some zv]).getD 0 none).getD 0 = zv := by
          rw [uvnsGetDRepZV, if_pos hn.symm]
          rfl
        rw [hb]
        exact hdisj hn
      · exfalso
        rw [if_neg (by omega : (0 : ℕ) ≠ n)] at hs2
        simp at hs2
    · -- j ≥ pfx.length：两元都在 app 的 nseq 段
      simp only [dif_neg (by omega : ¬ j < pfx.length), dif_neg (by omega : ¬ j + 1 < pfx.length)] at hs1 hs2 ⊢
      rw [uvnsGetDRepZV] at hs1 hs2
      by_cases e1 : j - pfx.length = n
      · rw [if_pos e1] at hs1
        by_cases e2 : j + 1 - pfx.length = n
        · rw [if_pos e2] at hs2
          omega
        · rw [if_neg e2] at hs2
          simp at hs2
      · rw [if_neg e1] at hs1
        simp at hs1


/-- `|between| = indexf - 1`（私有重落；`Thm6C:55` 同名件为 private）。 -/
theorem sizeBetwnChainPub {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x y : α} (hnd : s.Nodup) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (between s x y).length = (Kepler.Text.TameSpine.indexf x y s) - 1 := by
  rw [Kepler.Text.TameSpine.sizeBetwn hnd hx hy hne]

end Kepler.Text.Reduction5

#print axioms Kepler.Text.Reduction5.ChainCl
#print axioms Kepler.Text.Reduction5.chainClBase
#print axioms Kepler.Text.Reduction5.chainClNsAppend
#print axioms Kepler.Text.Reduction5.sizeBetwnChainPub
