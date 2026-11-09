/-
  Kepler.Text.TameSpine.JcajyduAqLeaf1C — AQ1 叶第三批（前置件）：
  互不交的**通用二分分离器** + `flatten` 分解的 Nodup/不交事实 + 两块直接分离。

  用途（HOL `AQ1` 末段的 `Seq.cat_uniq` 三次分裂）：
  `ntrans 1` 的 flatten 已由 `aq1b_flattenNtrans1` 化成
  `(N₁.flatten ++ s2) ++ N₂.flatten ++ s1`；`s1`/`s2` 的成员二分由
  `aq1b_split1Mem`/`aq1b_split2Mem` 给（∈ r 或 ∉ `flatten N`）。
  于是六对互不交里 **五对** 都归约成同一个模式（下面 `aq1c_disjOfDich`），
  只剩两个真缺口：`new1 × window`（Simple/injOrbit）与 `f1 × f2`（互补弧）。

  ┌─ 件表（`patch_leaf1c.diff`）─────────────────────────────────
  │ ① `aq1c_disjOfDich`：`A` 每元 ∈ r ∨ ∉ M、`B ⊆ M`、`B ∩ r = ∅`
  │    ⇒ `A` 与 `B` 互不交（一次覆盖五对）；
  │ ② `aq1c_flattenParts`：`N = N₁ ++ r :: N₂` + `flatten N` Nodup
  │    ⇒ `N₁/N₂` 的 flatten Nodup、二者与 `r` 不交、`N₁.flatten` 与
  │    `N₂.flatten` 不交；
  │ ③ `aq1c_f2SubR`：`f2 = [z] ++ betwn r z y ++ [y]` ⊆ r；
  │ ④ `aq1c_f1SubR`：`f1 = [ra] ++ betwn r ra z1 ++ [z1]` ⊆ r；
  │ ⑤ `aq1c_new1DisjF2`：`new1`（∉ `flatten N`）× `f2`（⊆ r ⊆ `flatten N`）；
  │ ⑥ `aq1c_f1DisjNew2`：`f1`（⊆ r）× `new2`（`betwnNotInRtrans`: ∉ r）。
  └──────────────────────────────────────────────────────────────

  ┌─ 边界（见 DELIVERY_AQ1C §2）──────────────────────────────────
  │ 剩余两缺口：`new1 × new2`（d = nodeMap^i x ∧ 窗口 → node∩face 塌缩，
  │ 引擎 = Leaf1 ④ + `injOrbit`）、`f1 × f2`（互补弧：弧恒等式
  │ `betwn r y z = [ra] ++ betwn r ra z1 ++ [z1]` + 零点不等式 ①②）；
  │ 然后 `List.nodup_append` ×3 总装。
  └──────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf1B

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts listPairs)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem)

/-! ## §1 通用二分分离器 -/

/-- **二分分离器**（AQ1 总装五对共用的唯一模式）：
若 `A` 的每个元素「∈ r 或 ∉ M」，`B ⊆ M`，且 `B` 不吃 `r`，则 `A` 与 `B` 互不交。
（五对 = `(A,B)` 取 `(s1, N₁.flatten)`/`(s2, N₁.flatten)`/`(s1, N₂.flatten)`/
`(s2, N₂.flatten)`/`(N₁.flatten, N₂.flatten)`（后者用 `∈ r` 全假）。） -/
theorem aq1c_disjOfDich {α : Type*} {A B r M : List α}
    (hA : ∀ d ∈ A, d ∈ r ∨ d ∉ M) (hB : ∀ d ∈ B, d ∈ M) (hrB : ∀ d ∈ B, d ∉ r) :
    ∀ d ∈ A, ∀ e ∈ B, d ≠ e := by
  intro d hd e he hde
  rcases hA d hd with h1 | h1
  · exact hrB e he (hde ▸ h1)
  · exact h1 (hde ▸ hB e he)

/-! ## §2 `flatten` 切口分解的 Nodup / 不交事实 -/

/-- `N = N₁ ++ r :: N₂` 且 `flatten N` Nodup ⇒ 三段各自的 Nodup 与互不交。 -/
theorem aq1c_flattenParts {N N₁ N₂ : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    (hflN : N.flatten.Nodup) (hN : N = N₁ ++ r :: N₂) :
    N₁.flatten.Nodup ∧ N₂.flatten.Nodup ∧
      (∀ d ∈ N₁.flatten, d ∉ r) ∧ (∀ d ∈ N₂.flatten, d ∉ r) ∧
      (∀ d ∈ N₁.flatten, d ∉ N₂.flatten) := by
  have h := hflN
  rw [hN, List.flatten_append, List.flatten_cons] at h
  rw [List.nodup_append] at h
  obtain ⟨hA, hB, hAB⟩ := h
  rw [List.nodup_append] at hB
  obtain ⟨hr, hC, hBC⟩ := hB
  exact ⟨hA, hC,
    fun d hd hdr => hAB d hd d (List.mem_append_left _ hdr) rfl,
    fun d hd hdr => hBC d hdr d hd rfl,
    fun d hd hd2 => hAB d hd d (List.mem_append_right _ hd2) rfl⟩

/-! ## §3 `f1`/`f2` 的 r-成员性 + 两块直接分离 -/

/-- `f2 = [z] ++ betwn r z y ++ [y]` 的成员都吃 `r`。 -/
theorem aq1c_f2SubR {r : List (ℕ × ℕ)} {y z d : ℕ × ℕ} (hy : y ∈ r) (hz : z ∈ r)
    (hd : d ∈ [z] ++ between r z y ++ [y]) : d ∈ r := by
  rcases List.mem_append.mp hd with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · rw [List.mem_singleton] at h2
      exact h2 ▸ hz
    · exact memBetweenOfMem h2
  · rw [List.mem_singleton] at h1
    exact h1 ▸ hy

/-- **`new1 × f2` 互不交**：`new1` 元素 ∉ `flatten N`（Leaf1 ⑦），`f2 ⊆ r ⊆ flatten N`。 -/
theorem aq1c_new1DisjF2 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ d ∈ ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).map (ndSpine L)).flatten,
      ∀ e ∈ [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ [lYSpine L r x], d ≠ e := by
  intro d hd e he hde
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have heN : e ∈ N.flatten :=
    List.mem_flatten.mpr ⟨r, hm.1.2.2.1, aq1c_f2SubR hyr hzr he⟩
  exact aq1_new1NotMemFlatten L hL hgn hunL hm hf d hd (hde ▸ heN)

/-- **`f1 × new2` 互不交**：`f1 ⊆ r`，`new2`（窗口）不吃 `r`（`betwnNotInRtrans`）。 -/
theorem aq1c_f1DisjNew2 (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ d ∈ [nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
        (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)],
      ∀ e ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x), d ≠ e := by
  intro d hd e he hde
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hdr : d ∈ r := by
    rcases List.mem_append.mp hd with h1 | h1
    · rcases List.mem_append.mp h1 with h2 | h2
      · rw [List.mem_singleton] at h2
        exact h2 ▸ (nextEl_mem_of_mem hyr)
      · exact memBetweenOfMem h2
    · rw [List.mem_singleton] at h1
      exact h1 ▸ hz1r
  exact betwnNotInRtrans L hL hgn hunL hm hf he (hde ▸ hdr)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq1c_disjOfDich
#print axioms Kepler.Text.TameSpine.aq1c_flattenParts
#print axioms Kepler.Text.TameSpine.aq1c_f2SubR
#print axioms Kepler.Text.TameSpine.aq1c_new1DisjF2
#print axioms Kepler.Text.TameSpine.aq1c_f1DisjNew2
