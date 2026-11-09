/-
  JcajyduAqLeaf10F — AQ10-b1：前缀两支 `aq10_nextElPrefix`（Dart 专用）。

  x ∈ P = [z]++betwn r z y++[y] 且 x ≠ y ⇒ nextEl P x = nextEl r x。
  内部：左端点支（x=z）+ 内部支（x∈B，含 x=B.last 子支）。
  卡点/绕法见 DELIVERY §AQ10b4。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf10D
import Kepler.Text.TameSpine.JcajyduAqLeaf10C
import Kepler.Text.TameSpine.JcajyduAqZUnlock
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.JcajyduAqSnd
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList71
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl fList findFaceDarts listOfDarts GoodList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- `getLast! = getLast`（非空；仅纯等式处使用）。 -/
private theorem aq10_getLast!_eq_getLast {l : List (ℕ × ℕ)} (h : l ≠ []) :
    l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast_eq_getElem, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by have := List.length_pos_of_ne_nil h; omega)]
  simp

/-- 后缀末元：`(l ++ [y]).getLast! = y`。 -/
theorem aq10_suffixLast (l : List (ℕ × ℕ)) (y : ℕ × ℕ) :
    (l ++ [y]).getLast! = y := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_append_of_ne_nil _ (by simp)]
  simp

/-- 左端点支：`nextEl P z = nextEl r z`。 -/
private theorem aq10_nextElPAux_left (r : List (ℕ × ℕ)) (z y : ℕ × ℕ)
    (hnd : r.Nodup) (hz : z ∈ r) (hy : y ∈ r) (hzy : z ≠ y) :
    nextEl ([z] ++ between r z y ++ [y]) z = nextEl r z := by
  by_cases hB : between r z y = []
  · have hBz : nextEl r z = y := ((betwnNil hnd hzy hz hy).mp hB).symm
    have hstep := nextElCatLast1 (s := [z]) (t := [y])
      (by simp [List.nodup_cons, hzy]) (by simp) (by simp)
    rw [show ([z] : List (ℕ × ℕ)).getLast! = z from aq10_suffixLast [] z] at hstep
    rw [hB]
    show nextEl ([z] ++ [y]) z = nextEl r z
    rw [hstep, hBz]
    rfl
  · have hBne : between r z y ≠ [] := hB
    have hndP' : ([z] ++ (between r z y ++ [y])).Nodup := by
      rw [← List.append_assoc]
      exact uniqAppendBetwn hnd hz hy hzy
    have hstep := nextElCatLast1 (s := [z]) (t := between r z y ++ [y]) hndP'
      (by simp) (by simp)
    rw [show ([z] : List (ℕ × ℕ)).getLast! = z from aq10_suffixLast [] z] at hstep
    rw [show ([z] ++ (between r z y ++ [y]) : List (ℕ × ℕ)) =
        [z] ++ between r z y ++ [y] from
      (List.append_assoc [z] (between r z y) [y]).symm] at hstep
    rw [hstep]
    have hhead : (between r z y ++ [y]).head! = (between r z y).head! := by
      cases hB' : between r z y with
      | nil => exact absurd hB' hB
      | cons a t => rfl
    rw [hhead]
    exact HD_BETWN2 hz hy hzy hnd hBne

/-- 内部支（x∈B，含 x=B.last）：`nextEl P x = nextEl r x`。 -/
private theorem aq10_nextElPAux_mem (r : List (ℕ × ℕ)) {x z y : ℕ × ℕ}
    (hnd : r.Nodup) (hz : z ∈ r) (hy : y ∈ r) (hzy : z ≠ y)
    (hx : x ∈ between r z y) :
    nextEl ([z] ++ between r z y ++ [y]) x = nextEl r x := by
  have hBne : between r z y ≠ [] := List.ne_nil_of_mem hx
  have hndP : ([z] ++ between r z y ++ [y]).Nodup := uniqAppendBetwn hnd hz hy hzy
  have hndP' : ([z] ++ (between r z y ++ [y])).Nodup := by rwa [List.append_assoc] at hndP
  have hndT : (between r z y ++ [y]).Nodup :=
    List.Sublist.nodup (List.sublist_append_right [z] (between r z y ++ [y])) hndP'
  have hxT : x ∈ between r z y ++ [y] := List.mem_append.mpr (Or.inl hx)
  have hyB : y ∉ between r z y := notBetwn2 hnd
  have hxneT : x ≠ (between r z y ++ [y]).getLast! := by
    rw [show (between r z y ++ [y]).getLast! = y from aq10_suffixLast _ y]
    intro h
    exact hyB (h ▸ hx)
  have hstep := nextElCat2 (s := [z]) (t := between r z y ++ [y]) hndP' hxT hxneT
  rw [show ([z] ++ (between r z y ++ [y]) : List (ℕ × ℕ)) =
      [z] ++ between r z y ++ [y] from
    (List.append_assoc [z] (between r z y) [y]).symm] at hstep
  rw [hstep]
  by_cases hlastB : x = (between r z y).getLast!
  · rw [hlastB]
    rw [nextElCatLast1 hndT hBne (by simp)]
    have hnr : nextEl r ((between r z y).getLast!) = y := by
      rw [aq10_getLast!_eq_getLast hBne]
      exact nextLastBetwn hz hy hnd hzy hBne
    exact hnr.symm
  · have hstepB := nextElCat1 (s := between r z y) (t := [y])
      (List.Sublist.nodup (List.sublist_append_left (between r z y) [y]) hndT) hx
      (by
        intro h
        exact hlastB (by rw [h, aq10_getLast!_eq_getLast hBne]))
    have hnextmem : nextEl r x ∈ between r z y := by
      have hiff := aq10_eqMemNextElLast (f := r) (y := z) (z := y) (d := x) hzy hz hy hx hnd
      exact hiff.mpr (by
        intro hgl
        exact hlastB (by rw [← hgl, ← aq10_getLast!_eq_getLast hBne]))
    have hsame := aq10_nextElBetwnSame (f := r) (y := z) (z := y) (d := x)
      hzy hz hy hx hnextmem hnd
    rw [hstepB, hsame]

/-- **AQ10-b1 主件**：`x ∈ P = [z]++betwn r z y++[y]` 且 `x ≠ y` ⇒
`nextEl P x = nextEl r x`（Dart 专用；左端点支 + 内部支）。 -/
theorem aq10_nextElPrefix (r : List (ℕ × ℕ)) {x z y : ℕ × ℕ}
    (hnd : r.Nodup) (hz : z ∈ r) (hy : y ∈ r) (hzy : z ≠ y)
    (hxP : x ∈ [z] ++ between r z y ++ [y]) (hxy : x ≠ y) :
    nextEl ([z] ++ between r z y ++ [y]) x = nextEl r x := by
  rcases List.mem_append.mp hxP with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · rw [List.mem_singleton] at h2
      rw [h2]
      exact aq10_nextElPAux_left r z y hnd hz hy hzy
    · exact aq10_nextElPAux_mem r hnd hz hy hzy h2
  · rw [List.mem_singleton] at h1
    exact absurd h1 hxy

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq10_suffixLast
#print axioms Kepler.Text.TameSpine.aq10_nextElPrefix
