/-
  Kepler.Text.Reduction1W1j — J4 Wave W1 批 6 §4：
  `showDups0_mono`（`:478-:575`）+ `enum_of_VertexList_mono`（`:576-:625`）。
  纪律：零公理、零占位证明、零反射式判定。DIFFERS：`EL` ↦ `getElem!`；`the` ↦ `Option.get!`。
-/
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList4

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Text.TameSpine (showDups0 showDups indexf enumOfVertexList)

/-- `map` 的 `getElem!` 展开（界内；替代树内 0 命中的 `List.getElem!_map`）。 -/
private theorem getElemBangMap {l : List ℕ} {g : ℕ → ℕ} {k : ℕ} (hk : k < l.length) :
    (l.map g)[k]! = g l[k]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]
  simp

/-- `showDups0` 与 `vs` 等长（树内无公开件）。 -/
private theorem showDups0Length {l : List (Option ℕ)} (w : ℕ) :
    (showDups0 w l).length = l.length := by
  induction l generalizing w with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | none => rw [showDups0, List.length_cons, ih w, List.length_cons]
    | some c => rw [showDups0, List.length_cons, ih c, List.length_cons]

/-- **HOL `showDups0_mono`**（`reduction1.hl:478-:575`）。
归纳不变式：IH 五参 `(vs', w, 方程, hmono, hhead)`；`b = some c` 支把尾部过滤表
`vs'b` 显式化，`hmono'`/`hhead'` 由外层 `hmono` 经 `vs' = c :: vs'b` 位次平移得到。 -/
theorem showDups0Mono {f : List ℕ} {v : ℕ} (_hf : f.Nodup) (_hv : v ∈ f) :
    ∀ (vs : List (Option ℕ)) (vs' : List ℕ) (w : ℕ),
      vs' = (vs.filter Option.isSome).map Option.get! →
      (∀ i, i + 1 < vs'.length → indexf v vs'[i]! f < indexf v vs'[i + 1]! f) →
      (vs' ≠ [] → indexf v w f ≤ indexf v vs'[0]! f) →
      ∀ i, i + 1 < vs.length →
        indexf v (showDups0 w vs)[i]! f ≤ indexf v (showDups0 w vs)[i + 1]! f := by
  intro vs
  induction vs with
  | nil => intro vs' w _ _ _ i hi; exact absurd hi (by simp)
  | cons b bs ih =>
    intro vs' w hvs' hmono hhead i hi
    set vsb : List ℕ := (bs.filter Option.isSome).map Option.get! with hvsb_def
    cases i with
    | zero =>
      have hbs : bs ≠ [] := by intro hc; rw [hc] at hi; simp at hi
      cases b with
      | none =>
        rw [showDups0, List.getElem!_cons_zero, List.getElem!_cons_succ]
        cases bs with
        | nil => exact absurd rfl hbs
        | cons b' bs' =>
          cases b' with
          | none => rw [showDups0, List.getElem!_cons_zero]
          | some c =>
            rw [showDups0, List.getElem!_cons_zero]
            have hvs1 : vs' = c :: ((bs'.filter Option.isSome).map Option.get!) := by
              rw [hvs']; simp
            have hc := hhead (by rw [hvs1]; simp)
            rwa [hvs1, List.getElem!_cons_zero] at hc
      | some c =>
        rw [showDups0, List.getElem!_cons_zero, List.getElem!_cons_succ]
        cases bs with
        | nil => exact absurd rfl hbs
        | cons b' bs' =>
          cases b' with
          | none => rw [showDups0, List.getElem!_cons_zero]
          | some d =>
            rw [showDups0, List.getElem!_cons_zero]
            have hvs1 : vs' = c :: d :: ((bs'.filter Option.isSome).map Option.get!) := by
              rw [hvs']; simp
            have hm := hmono 0 (by rw [hvs1]; simp)
            rw [hvs1, List.getElem!_cons_zero, List.getElem!_cons_succ] at hm
            exact le_of_lt hm
    | succ j =>
      have hbj : j + 1 < bs.length := by
        rw [List.length_cons] at hi; omega
      cases b with
      | none =>
        rw [showDups0, List.getElem!_cons_succ, List.getElem!_cons_succ]
        have hvsb : vs' = vsb := by rw [hvs', hvsb_def]; simp
        exact ih vs' w hvsb hmono hhead j hbj
      | some c =>
        rw [showDups0, List.getElem!_cons_succ, List.getElem!_cons_succ]
        have hvsb : vs' = c :: vsb := by rw [hvs', hvsb_def]; simp
        have e1 : ∀ k, vs'[k + 1]! = vsb[k]! := by
          intro k; rw [hvsb, List.getElem!_cons_succ]
        have e2 : ∀ k, vs'[(k + 1) + 1]! = vsb[k + 1]! := by
          intro k
          rw [hvsb, List.getElem!_cons_succ]
        refine ih vsb c rfl ?_ ?_ j hbj
        · intro k hk
          have hm := hmono (k + 1) (by rw [hvsb, List.length_cons]; omega)
          rwa [e1, e2] at hm
        · intro hvsbne
          have h1 : 1 < vs'.length := by
            rw [hvsb, List.length_cons]
            have := List.length_pos_iff.mpr hvsbne
            omega
          have hm := hmono 0 h1
          rw [hvsb, List.getElem!_cons_zero, List.getElem!_cons_succ] at hm
          exact le_of_lt hm

/-- **HOL `enum_of_VertexList_mono`**（`reduction1.hl:576-:625`）。 -/
theorem enumOfVertexListMono {vs : List (Option ℕ)} {vs' : List ℕ} {f : List ℕ} {v : ℕ}
    (hhd : vs.head! = some v) (hf : f.Nodup) (hv : v ∈ f)
    (hvs' : vs' = (vs.filter Option.isSome).map Option.get!)
    (hmono : ∀ i, i + 1 < vs'.length → indexf v vs'[i]! f < indexf v vs'[i + 1]! f) :
    ∀ i, i + 1 < vs.length →
      (enumOfVertexList f v vs)[i]! ≤ (enumOfVertexList f v vs)[i + 1]! := by
  have hsd : showDups vs = showDups0 v vs := by
    cases vs with
    | nil => rw [List.head!_nil] at hhd; exact absurd hhd (by simp)
    | cons b bs =>
      have hb : b = some v := by simpa using hhd
      rw [showDups, hb]
      rfl
  have hhead : vs' ≠ [] → indexf v v f ≤ indexf v vs'[0]! f := by
    intro _
    rw [Kepler.Text.TameSpine.indexfRefl hv]
    exact Nat.zero_le _
  have hmonoD := showDups0Mono (f := f) (v := v) hf hv vs vs' v hvs' hmono hhead
  intro i hi
  have hlen : i < (showDups0 v vs).length := by rw [showDups0Length]; omega
  rw [enumOfVertexList, hsd, getElemBangMap hlen,
    getElemBangMap (by rw [showDups0Length]; omega)]
  exact hmonoD i hi

end Kepler.Text.Reduction1

/-! 公理审计锚 -/
#print axioms Kepler.Text.Reduction1.showDups0Mono
#print axioms Kepler.Text.Reduction1.enumOfVertexListMono
