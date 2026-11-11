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
      simp only [uvnsGetDRepZV] at hs2
      by_cases hn : n = 0
      · right
        rw [hw]
        have hb : ((List.replicate n (none : Option ℕ) ++ [some zv]).getD 0 none).getD 0 = zv := by
          rw [uvnsGetDRepZV, if_pos hn.symm]
          rfl
        rw [hb]
        exact hdisj hn
      · exfalso
        simp only [if_neg (by omega : (0 : ℕ) ≠ n)] at hs2
        simp at hs2
    · -- j ≥ pfx.length：两元都在 app 的 nseq 段
      simp only [dif_neg (by omega : ¬ j < pfx.length), dif_neg (by omega : ¬ j + 1 < pfx.length)] at hs1 hs2 ⊢
      simp only [uvnsGetDRepZV] at hs1 hs2
      by_cases e1 : j - pfx.length = n
      · simp only [if_pos e1] at hs1
        by_cases e2 : j + 1 - pfx.length = n
        · simp only [if_pos e2] at hs2
          omega
        · simp only [if_neg e2] at hs2
          simp at hs2
      · simp only [if_neg e1] at hs1
        simp at hs1


/-- `|between| = indexf - 1`（私有重落；`Thm6C:55` 同名件为 private）。 -/
theorem sizeBetwnChainPub {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x y : α} (hnd : s.Nodup) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (between s x y).length = (Kepler.Text.TameSpine.indexf x y s) - 1 := by
  rw [Kepler.Text.TameSpine.sizeBetwn hnd hx hy hne]

/-- `(r.map some ++ rest).getD t`（`t` 界内）= `some (r.getD t 0)`。 -/
theorem uvnsGetDMapSomeApp {r : List ℕ} (rest : List (Option ℕ)) {t : ℕ}
    (ht : t < r.length) :
    (r.map some ++ rest).getD t none = some (r.getD t 0) := by
  rw [uvnsGetDAppend (l := r.map some) (m := rest) (j := t)]
  rw [dif_pos (by simpa using ht)]
  exact uvnsGetDMapSome ht

/-- `(r.map some ++ rest).getD (|r| + m) = rest.getD m`。 -/
theorem uvnsGetDMapAdd {r : List ℕ} (rest : List (Option ℕ)) (m : ℕ) :
    (r.map some ++ rest).getD (r.length + m) none = rest.getD m none := by
  rw [uvnsGetDAppend (l := r.map some) (m := rest) (j := r.length + m)]
  rw [dif_neg (by simp)]
  rw [List.length_map]
  rw [show r.length + m - r.length = m from by omega]

/-- **③ 带首 Some 的追加**（destTriple0 步进 case `nextEl u0 = u` 与弧支）：
`pfx ++ r.map some ++ [some u] ++ nseq n none ++ [some z]` 的 `ChainCl`。
三 junction 由调用方供：`r=[]` 时 `w→u`（`hfirst`）、`r≠[]` 时 `w→r 首`
（`hfirstR`）、`r 末→u`（`hlastR`）；`r` 内部相邻由 `hchain`；`u→z` 仅当
`n = 0`（`hdisj`）。 -/
theorem chainClSomeAppend (f : List ℕ) (D : ℕ → ℕ → Prop)
    (pfx : List (Option ℕ)) (w : ℕ) (r : List ℕ) (u zv n : ℕ)
    (hcl : ChainCl f D pfx)
    (hlastD : ∀ j, j + 1 = pfx.length → (pfx.getD j none).getD 0 = w)
    (hfirst : r = [] → nextEl f w = u ∨ D w u)
    (hfirstR : r ≠ [] → nextEl f w = r.getD 0 0)
    (hchain : ∀ j, j + 1 < r.length → nextEl f (r.getD j 0) = r.getD (j + 1) 0)
    (hlastR : r ≠ [] → nextEl f (r.getD (r.length - 1) 0) = u)
    (hdisj : n = 0 → D u zv) :
    ChainCl f D (pfx ++ (r.map some ++ [some u] ++
      List.replicate n (none : Option ℕ) ++ [some zv])) := by
  intro j hj1 hs1 hs2
  set rest : List (Option ℕ) := [some u] ++ List.replicate n (none : Option ℕ) ++ [some zv] with hrest
  have happ : r.map some ++ [some u] ++ List.replicate n (none : Option ℕ) ++ [some zv]
      = r.map some ++ rest := by
    rw [hrest]
    simp only [List.append_assoc]
  rw [happ] at hs1 hs2 ⊢
  simp only [uvnsGetDAppend (l := pfx) (m := r.map some ++ rest) (j := j),
    uvnsGetDAppend (l := pfx) (m := r.map some ++ rest) (j := j + 1)] at hs1 hs2 ⊢
  by_cases hj : j + 1 < pfx.length
  · simp only [dif_pos (by omega : j < pfx.length), dif_pos hj] at hs1 hs2 ⊢
    exact hcl j hj hs1 hs2
  · by_cases hje : j + 1 = pfx.length
    · -- 跨越：pfx 末 w × app 首项
      simp only [dif_pos (by omega : j < pfx.length), dif_neg (by omega : ¬ j + 1 < pfx.length),
        show j + 1 - pfx.length = 0 from by omega] at hs1 hs2 ⊢
      rw [hlastD j hje]
      cases r with
      | nil =>
        have h0 : ((List.map some [] ++ rest).getD 0 none).getD 0 = u := by
          simp [hrest]
        rcases hfirst rfl with h | h
        · left
          rw [h0]
          exact h
        · right
          rw [h0]
          exact h
      | cons a r'' =>
        have h0 : (((a :: r'').map some ++ rest).getD 0 none).getD 0
            = (a :: r'').getD 0 0 := by
          simp
        left
        rw [h0]
        exact hfirstR (by simp)
    · -- j ≥ pfx.length：t := j - pfx.length
      simp only [dif_neg (by omega : ¬ j < pfx.length),
        dif_neg (by omega : ¬ j + 1 < pfx.length)] at hs1 hs2 ⊢
      set t : ℕ := j - pfx.length with htdef
      simp only [show j + 1 - pfx.length = t + 1 from by omega] at hs2 ⊢
      by_cases ht0 : t < r.length
      · -- t 落在 r.map some 内
        simp only [uvnsGetDMapSomeApp (rest := rest) (t := t) ht0] at hs1 hs2 ⊢
        have hrne : r ≠ [] := by
          intro h
          rw [h] at ht0
          simp at ht0
        by_cases ht1 : t + 1 < r.length
        · simp only [uvnsGetDMapSomeApp (rest := rest) (t := t + 1) ht1] at hs2 ⊢
          left
          exact hchain t ht1
        · -- t 是 r 的末位：次元 = rest 首项 u
          have hte : t + 1 = r.length := by omega
          rw [show t + 1 = r.length + 0 from by omega] at hs2 ⊢
          simp only [uvnsGetDMapAdd (rest := rest) (m := 0)] at hs2 ⊢
          have hrest0 : rest.getD 0 none = some u := by
            simp [hrest]
          simp only [hrest0] at hs2 ⊢
          left
          rw [show t = r.length - 1 from by omega]
          exact hlastR hrne
      · -- t ≥ r.length
        by_cases htr : t = r.length
        · -- 首 = u（rest 首项）
          simp only [show t = r.length + 0 from by omega] at hs1 ⊢
          simp only [uvnsGetDMapAdd (rest := rest) (m := 0)] at hs1 ⊢
          have hrest0 : rest.getD 0 none = some u := by
            simp [hrest]
          simp only [hrest0] at hs1 ⊢
          simp only [show t + 1 = r.length + 1 from by omega] at hs2 ⊢
          simp only [uvnsGetDMapAdd (rest := rest) (m := 1)] at hs2 ⊢
          have hrest1 : rest.getD 1 none
              = (List.replicate n (none : Option ℕ) ++ [some zv]).getD 0 none := by
            simp [hrest]
          simp only [hrest1] at hs2 ⊢
          simp only [uvnsGetDRepZV] at hs2 ⊢
          by_cases hn : n = 0
          · right
            rw [if_pos hn.symm]
            exact hdisj hn
          · exfalso
            simp only [if_neg (by omega : (0 : ℕ) ≠ n)] at hs2
            simp at hs2
        · -- t > r.length：首在 rest 的 nseq 段（`> [some u]`），次元同段——isSome 互斥
          have hlt : r.length < t := by omega
          have ht_split : t = r.length + (t - r.length) := by omega
          rw [ht_split] at hs1
          rw [ht_split]
          simp only [uvnsGetDMapAdd (rest := rest) (m := t - r.length)] at hs1 ⊢
          have ht_split' : t + 1 = r.length + (t + 1 - r.length) := by omega
          rw [ht_split'] at hs2
          simp only [show r.length + (t - r.length) + 1 = r.length + (t + 1 - r.length) from by omega] at ⊢
          simp only [uvnsGetDMapAdd (rest := rest) (m := t + 1 - r.length)] at hs2 ⊢
          simp only [hrest] at hs1 hs2
          simp only [uvnsGetDHeadRepCons] at hs1 hs2
          simp only [if_neg (by omega : t - r.length ≠ 0)] at hs1
          simp only [uvnsGetDRepZV] at hs1
          have hk1 : t + 1 - r.length ≠ 0 := by omega
          simp only [if_neg hk1] at hs2
          simp only [show t + 1 - r.length - 1 = t - r.length from by omega] at hs2
          simp only [uvnsGetDRepZV] at hs2
          by_cases e1 : t - r.length - 1 = n
          · simp only [if_pos e1] at hs1
            by_cases e2 : t - r.length = n
            · simp only [if_pos e2] at hs2
              omega
            · simp only [if_neg e2] at hs2
              simp at hs2
          · simp only [if_neg e1] at hs1
            simp at hs1

end Kepler.Text.Reduction5

#print axioms Kepler.Text.Reduction5.ChainCl
#print axioms Kepler.Text.Reduction5.chainClBase
#print axioms Kepler.Text.Reduction5.chainClNsAppend
#print axioms Kepler.Text.Reduction5.sizeBetwnChainPub
#print axioms Kepler.Text.Reduction5.uvnsGetDMapSomeApp
#print axioms Kepler.Text.Reduction5.uvnsGetDMapAdd
#print axioms Kepler.Text.Reduction5.chainClSomeAppend
