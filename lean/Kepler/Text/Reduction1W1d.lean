/-
  Kepler.Text.Reduction1W1d — J4 Wave W1 批 4（**编排者按车道冻结包
  `DELIVERY_W1D_V3_FROZEN.md` 收口**，2026-11-10）：
  `showdups0_suc_is_some`（reduction1.hl:956-:1006）/ `enum_suc_is_some`
  （:1007-:1034）/ `showDups0_bound`（:676-:692）/ `enum_bound`（:738-:776）。

  ┌─ 路线说明（相对冻结包骨架的三处结构修正）─────────────────────────
  │ ① `showDups0_succ_none` 的归纳论证重写为：`vs[i+1] = none ⇒
  │    (showDups0 u vs)[i]! = (showDups0 u vs)[i+1]!`（对 vs 归纳、
  │    携带默认值 u 随 cons 头变化；首元 none 支用私件
  │    `showDups0HeadNone`）——冻结包 v3 中 `hall'`/`hnone'` 未绑定。
  │ ② `showDups0_bound` 改证**单下标 aux**（`i < |vs|` + 只对 `j ≤ i`
  │    的前缀假设）：避免冻结包 `induction … generalizing u k` 下
  │    `k = |bs|` 时递归调用需要 `k < |bs|` 失败的边界；主声明由 aux
  │    以 `i ≤ k < |vs|` 直接实例化。
  │ ③ `enumSucIsSome` / `enumBound` 的 `map` 位次取值走自建
  │    `getElemBangMap`（`List.getElem!_map` 树内 0 命中，冻结包实
  │    测已记档）；`showDups (b :: bs) = showDups0 (b.getD 0) (b :: bs)`
  │    用构造子 `rfl` 桥（`showDupsConsEq`）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
  DIFFERS：HOL `EL` ↦ `getElem!`（约定 C2）；`the (EL i vs)` ↦ `vs[i]!.getD 0`；
  `sizel` ↦ `List.length`。
-/
import Kepler.Text.TameSpine.TameList53

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Text.TameSpine (showDups0 showDups indexf enumOfVertexList)

/-! ## §0 通用私件 -/

/-- 界内 `getElem!` 与依赖式 `getElem` 同值（W1f `getElemBangH` 同款）。 -/
private theorem getElemBangH {α : Type} [Inhabited α] {l : List α} {i : ℕ}
    (h : i < l.length) : l[i]! = l[i]'h := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp

/-- `map` 的 `getElem!` 取值（`List.getElem!_map` 树内 0 命中）。 -/
private theorem getElemBangMap {α β : Type} [Inhabited α] [Inhabited β] {l : List α} {g : α → β} {i : ℕ}
    (h : i < l.length) : (l.map g)[i]! = g (l[i]!) := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp only [Option.map_some, Option.getD_some]
  rw [getElemBangH h]

/-- `showDups` 的 cons 展开（构造子 `rfl` 桥，`get!`/`getD 0` 在 ℕ 上同值）。 -/
private theorem showDupsConsEq (b : Option ℕ) (bs : List (Option ℕ)) :
    showDups (b :: bs) = showDups0 (b.getD 0) (b :: bs) := by
  cases b with
  | none => rfl
  | some c => rfl

/-! ## §1 `showdups0_suc_is_some`（reduction1.hl:956-:1006） -/

/-- `showDups0` 首元：头为 `none` 时取携带默认 `u`。 -/
private theorem showDups0HeadNone {bs : List (Option ℕ)} {u : ℕ}
    (hbs : bs ≠ []) (h : bs[0]! = none) : (showDups0 u bs)[0]! = u := by
  cases bs with
  | nil => exact absurd rfl hbs
  | cons c cs =>
    cases c with
    | none => rw [showDups0, List.getElem!_cons_zero]
    | some d =>
      rw [List.getElem!_cons_zero] at h
      exact absurd h (by simp)

/-- **关键引理**：`vs[i+1] = none ⇒ showDups0 相邻两项相等**。
对 `vs` 归纳（携带默认 `u` 随 cons 头换装）；首元支用
`showDups0HeadNone`。 -/
private theorem showDups0SucNoneEq : ∀ (vs : List (Option ℕ)) (u i : ℕ),
    i + 1 < vs.length → vs[i + 1]! = none →
      (showDups0 u vs)[i]! = (showDups0 u vs)[i + 1]! := by
  intro vs
  induction vs with
  | nil => intro u i hi; exact absurd hi (by simp)
  | cons b bs ih =>
    intro u i hi h
    cases i with
    | zero =>
      have hbs : bs ≠ [] := by
        intro c; rw [c] at hi; simp at hi
      have hb0 : bs[0]! = none := by
        have h1 : (b :: bs)[0 + 1]! = bs[0]! := List.getElem!_cons_succ
        rwa [h1] at h
      cases b with
      | none =>
        rw [showDups0, List.getElem!_cons_zero, List.getElem!_cons_succ]
        exact (showDups0HeadNone hbs hb0).symm
      | some c =>
        rw [showDups0, List.getElem!_cons_zero, List.getElem!_cons_succ]
        exact (showDups0HeadNone hbs hb0).symm
    | succ i' =>
      have hi' : i' + 1 < bs.length := by
        rw [List.length_cons] at hi; omega
      have h' : bs[i' + 1]! = none := by
        have h1 : (b :: bs)[i' + 1 + 1]! = bs[i' + 1]! := List.getElem!_cons_succ
        rwa [h1] at h
      cases b with
      | none =>
        rw [showDups0, List.getElem!_cons_succ, List.getElem!_cons_succ]
        exact ih u i' hi' h'
      | some c =>
        rw [showDups0, List.getElem!_cons_succ, List.getElem!_cons_succ]
        exact ih c i' hi' h'

/-- **HOL `showdups0_suc_is_some`**：`SUC i < sizel vs` 且
`EL i (showDups0 v0 vs) ≠ EL (SUC i) (showDups0 v0 vs)` ⇒ `isSome (EL (SUC i) vs)`
（`showDups0SucNoneEq` 的逆否）。 -/
theorem showdups0SucIsSome {vs : List (Option ℕ)} {v0 i : ℕ}
    (hi : i + 1 < vs.length)
    (hne : (showDups0 v0 vs)[i]! ≠ (showDups0 v0 vs)[i + 1]!) :
    (vs[i + 1]!).isSome := by
  by_cases hsome : (vs[i + 1]!).isSome = true
  · exact hsome
  · exfalso
    have hnone : vs[i + 1]! = none := by
      cases h : vs[i + 1]! with
      | none => rfl
      | some c =>
        rw [h, Option.isSome_some] at hsome
        exact absurd rfl hsome
    exact hne (showDups0SucNoneEq vs v0 i hi hnone)

/-! ## §2 `enum_suc_is_some`（reduction1.hl:1007-:1034） -/

/-- **HOL `enum_suc_is_some`**：`enumOfVertexList` 相邻两项不等 ⇒
`vs[i+1]` 为 `some`。路线：`enum = (showDups vs).map (indexf v · f)`；
若 `showDups` 相邻项相等则 `map` 后相等（`getElemBangMap`），撞 `hne`，
再交 §1。 -/
theorem enumSucIsSome {vs : List (Option ℕ)} {f : List ℕ} {v i : ℕ}
    (hi : i + 1 < vs.length)
    (hne : (enumOfVertexList f v vs)[i]! ≠ (enumOfVertexList f v vs)[i + 1]!) :
    (vs[i + 1]!).isSome := by
  cases vs with
  | nil => exact absurd hi (by simp)
  | cons b bs =>
    have hil : i < (showDups (b :: bs)).length := by
      rw [Kepler.Text.TameSpine.sizeShowDups]; omega
    have hmap : ∀ j, j < (showDups (b :: bs)).length →
        (enumOfVertexList f v (b :: bs))[j]!
          = indexf v ((showDups (b :: bs))[j]!) f := by
      intro j hj
      simp only [enumOfVertexList]
      exact getElemBangMap hj
    have hne' : indexf v ((showDups (b :: bs))[i]!) f
        ≠ indexf v ((showDups (b :: bs))[i + 1]!) f := by
      rw [← hmap i hil]
      rw [← hmap (i + 1) (by rw [Kepler.Text.TameSpine.sizeShowDups]; omega)]
      exact hne
    have hsd : (showDups (b :: bs))[i]! ≠ (showDups (b :: bs))[i + 1]! := by
      intro he
      exact hne' (congrArg (fun x => indexf v x f) he)
    cases b with
    | none =>
      have hsd' : (showDups0 0 (none :: bs))[i]! ≠ (showDups0 0 (none :: bs))[i + 1]! := by
        rwa [showDupsConsEq none bs] at hsd
      exact showdups0SucIsSome (v0 := 0) hi hsd'
    | some c =>
      have hsd' : (showDups0 c (some c :: bs))[i]! ≠ (showDups0 c (some c :: bs))[i + 1]! := by
        rwa [showDupsConsEq (some c) bs] at hsd
      exact showdups0SucIsSome (v0 := c) hi hsd'

/-! ## §3 `showDups0_bound`（reduction1.hl:676-:692） -/

/-- **单下标 aux**：`i < |vs|`、`indexf v u f ≤ r`、前缀 `j ≤ i` 的
some 项都在 `r` 内 ⇒ `showDups0 u vs` 第 `i` 项在 `r` 内。
对 `vs` 归纳：`i = 0` 时头 `none` 取 `hu`、头 `some c` 取 `hvs 0`；
`i = i'+1` 时递归携带的默认值随头换装。 -/
private theorem showDups0BoundAux : ∀ (vs : List (Option ℕ)) (u i : ℕ)
    (v : ℕ) (f : List ℕ) (r : ℕ),
    i < vs.length →
    indexf v u f ≤ r →
    (∀ j, j ≤ i → (vs[j]!).isSome → indexf v (vs[j]!.getD 0) f ≤ r) →
    indexf v (showDups0 u vs)[i]! f ≤ r := by
  intro vs
  induction vs with
  | nil => intro u i v f r hi hu hvs; exact absurd hi (by simp)
  | cons b bs ih =>
    intro u i v f r hi hu hvs
    cases i with
    | zero =>
      cases b with
      | none =>
        rw [showDups0, List.getElem!_cons_zero]
        exact hu
      | some c =>
        rw [showDups0, List.getElem!_cons_zero]
        have h0 : (((some c) :: bs)[0]!).isSome := by
          rw [List.getElem!_cons_zero]; rfl
        have h2 := hvs 0 (Nat.zero_le 0) h0
        simpa using h2
    | succ i' =>
      have hi' : i' < bs.length := by
        rw [List.length_cons] at hi; omega
      have hvs' : ∀ j, j ≤ i' → (bs[j]!).isSome →
          indexf v (bs[j]!.getD 0) f ≤ r := by
        intro j hj hso
        have h1 : ((b :: bs)[j + 1]!).isSome := by rwa [List.getElem!_cons_succ]
        have h2 := hvs (j + 1) (by omega) h1
        rwa [List.getElem!_cons_succ] at h2
      cases b with
      | none =>
        rw [showDups0, List.getElem!_cons_succ]
        exact ih u i' v f r hi' hu (fun j hj hso => hvs' j (by omega) hso)
      | some c =>
        have hc : indexf v c f ≤ r := by
          have h0 : (((some c) :: bs)[0]!).isSome := by
            rw [List.getElem!_cons_zero]; rfl
          have h2 := hvs 0 (Nat.zero_le (i' + 1)) h0
          simpa using h2
        rw [showDups0, List.getElem!_cons_succ]
        exact ih c i' v f r hi' hc (fun j hj hso => hvs' j (by omega) hso)

/-- **HOL `showDups0_bound`**（reduction1.hl:676-:692）。 -/
theorem showDups0Bound {vs : List (Option ℕ)} {u v : ℕ} {f : List ℕ} {r k : ℕ}
    (hk : k < vs.length)
    (hu : indexf v u f ≤ r)
    (hvs : ∀ i, i ≤ k → (vs[i]!).isSome → indexf v (vs[i]!.getD 0) f ≤ r) :
    ∀ i, i ≤ k → indexf v (showDups0 u vs)[i]! f ≤ r := by
  intro i hi
  exact showDups0BoundAux vs u i v f r (lt_of_le_of_lt hi hk) hu
    (fun j hj hso => hvs j (le_trans hj hi) hso)

/-! ## §4 `enum_bound`（reduction1.hl:738-:776） -/

/-- **HOL `enum_bound`**（reduction1.hl:738-:776）：`showDups0_bound` 的
`map` 提升形。 -/
theorem enumBound {vs : List (Option ℕ)} {f : List ℕ} {v r k : ℕ}
    (hk : k < vs.length)
    (hhd : vs ≠ [] → vs.head!.isSome)
    (hvs : ∀ i, i ≤ k → (vs[i]!).isSome → indexf v (vs[i]!.getD 0) f ≤ r) :
    ∀ i, i ≤ k → (enumOfVertexList f v vs)[i]! ≤ r := by
  have hne : vs ≠ [] := by intro c; rw [c] at hk; simp at hk
  cases vs with
  | nil => exact absurd hne (by simp)
  | cons b bs =>
    have hu : indexf v (b.getD 0) f ≤ r := by
      have h0 : ((b :: bs)[0]!).isSome := by
        have hh := hhd (List.cons_ne_nil b bs)
        rwa [List.head!_eq_getElem!] at hh
      have h2 := hvs 0 (Nat.zero_le k) h0
      simpa using h2
    intro i hi
    have hil : i < (b :: bs).length := lt_of_le_of_lt hi hk
    have hsd : showDups (b :: bs) = showDups0 (b.getD 0) (b :: bs) :=
      showDupsConsEq b bs
    have hmap : (enumOfVertexList f v (b :: bs))[i]!
        = indexf v ((showDups (b :: bs))[i]!) f := by
      simp only [enumOfVertexList]
      exact getElemBangMap (by rw [Kepler.Text.TameSpine.sizeShowDups]; exact hil)
    rw [hmap, hsd]
    exact showDups0Bound (vs := b :: bs) (u := b.getD 0) (v := v) (f := f)
      (r := r) (k := k) hk hu hvs i hi

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三、零未证公理） -/
#print axioms Kepler.Text.Reduction1.showdups0SucIsSome
#print axioms Kepler.Text.Reduction1.enumSucIsSome
#print axioms Kepler.Text.Reduction1.showDups0Bound
#print axioms Kepler.Text.Reduction1.enumBound
