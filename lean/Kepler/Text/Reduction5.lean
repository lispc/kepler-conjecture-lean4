/-
  Kepler.Text.Reduction5 — `Reduction5` 的定理层（W0）。

  本文件只放 **W0** 的定理：`betwn_core_reduction_lemma`（`reduction5.hl:19-52`，11 行）
  及其唯一前置 `mem_list_pairs_explicit`（`list_hypermap-compiled.hl:295-303`），
  外加 `min_num` 规格件与变换族的一行级投影件（`rfl`）。定义全部在
  `Kepler/Text/Reduction5Base.lean`（唯一 import 链 `TameLp` + `Graphs.ListAux`，
  闭包不含 `Kepler.Assembly`，不含 `TameSpine`）。

  **纪律**：零占位证明、零新增公理、零反射式判定；每条定理附 HOL 逐字锚。
-/
import Kepler.Text.Reduction5Base

namespace Kepler.Text.Reduction5

open Kepler.Assembly
open Kepler.Graphs

/-! ## 1. `mem_list_pairs_explicit`（`list_hypermap-compiled.hl:295-303`）

HOL：`uniq s /\ MEM (x,y) (list_pairs s) ==> y = next_el s x`。
`list_pairs s = zip s (rot 1 s)`，`rot 1 s = drop 1 s ++ take 1 s`（本仓
`listPairs` 已内联 `n = 1`，`GoodListDefs.lean:34`）。证明走下标：`MEM` 给出
`i < sizel s` 与 `s[i] = x`、`(drop 1 s ++ take 1 s)[i] = y`；`uniq` 把 `idxOf`
钉在 `i` 上；再按 `i + 1 < sizel s` 分两支（末位取 `headD`）。 -/
theorem mem_listPairs_nextEl {l : List ℕ} (hn : l.Nodup) {a b : ℕ}
    (h : (a, b) ∈ listPairs l) : nextEl l a = b := by
  unfold listPairs at h
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem h
  rw [List.getElem_zip] at hget
  obtain ⟨ha, hb⟩ := Prod.mk.injEq .. |>.mp hget
  have hlen : i < l.length := by
    have hmin := hi; rw [List.length_zip] at hmin; omega
  have hlen' : i < (l.drop 1 ++ l.take 1).length := by
    have hmin := hi; rw [List.length_zip] at hmin; omega
  have hdrop : (l.drop 1).length = l.length - 1 := List.length_drop
  have hidx : l.idxOf a = i := by
    rw [← ha]
    simpa using List.get_idxOf hn ⟨i, hlen⟩
  have hcase1 (h1 : i + 1 < l.length) : (l.drop 1 ++ l.take 1)[i] = l[i + 1] := by
    rw [List.getElem_append (h := hlen'), dif_pos (by omega), List.getElem_drop]
    congr 1
    omega
  have hcase2 (h1 : ¬ i + 1 < l.length) : (l.drop 1 ++ l.take 1)[i] = l[0] := by
    rw [List.getElem_append (h := hlen'), dif_neg (by omega)]
    have hidx0 : i - (l.drop 1).length = 0 := by omega
    rw [List.getElem_take]
    simp only [hidx0]
  unfold nextEl
  rw [hidx]
  by_cases h1 : i + 1 < l.length
  · have hne : ¬ (i = l.length - 1) := by omega
    rw [if_neg hne, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h := h1)]
    simp only [Option.getD_some, ← hb, hcase1 h1]
  · have heq : i = l.length - 1 := by omega
    have h0 : 0 < l.length := by omega
    rw [if_pos (by omega : i = l.length - 1), List.headD_eq_getD,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h := h0)]
    simp only [Option.getD_some, ← hb, hcase2 h1]

/-! ## 1b. `min_num` 规格件（`tame_defs.hl:313`）

HOL 的 `min_num` 是「最小元」的 Hilbert 选择；W1+ 关于 `l'm`/`l'p`/`transform_count`
的推理全部以这条规格为前提（非空集上取到最小元）。 -/
theorem minNum_spec {S : Set ℕ} (hne : S.Nonempty) :
    minNum S ∈ S ∧ ∀ n ∈ S, minNum S ≤ n := by
  classical
  obtain ⟨m₀, hm₀⟩ := hne
  have hex : ∃ m : ℕ, m ∈ S := ⟨m₀, hm₀⟩
  have hmin : Nat.find hex ∈ S ∧ ∀ n ∈ S, Nat.find hex ≤ n :=
    ⟨Nat.find_spec hex, fun n hn => Nat.find_min' hex hn⟩
  exact Classical.epsilon_spec (p := fun m => m ∈ S ∧ ∀ n ∈ S, m ≤ n)
    ⟨Nat.find hex, hmin⟩

/-! ## 2. 变换族投影件（`rfl` 级）

`tame_defs2.hl:469-485` 的六个 `new_definition'` 在 Lean 里就是定义等式本身；
这里显式命名，供 W1+ 的 `simp` 集使用（也作为「定义未走样」的机器证据）。 -/

/-- HOL `ntrans`（`tame_defs2.hl:469-470`）：零次迭代取原面表。 -/
theorem ntrans_zero (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) :
    ntrans L N r x 0 = N := rfl

/-- HOL `rtrans`（`tame_defs2.hl:472-473`）：零次迭代取原面。 -/
theorem rtrans_zero (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) :
    rtrans L N r x 0 = r := rfl

/-- HOL `ytrans`（`tame_defs2.hl:475-476`）。 -/
theorem ytrans_def (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (i : ℕ) : ytrans L N r x i = ly L (rtrans L N r x i) x := rfl

/-- HOL `ztrans`（`tame_defs2.hl:478-479`）。 -/
theorem ztrans_def (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (i : ℕ) : ztrans L N r x i = lz L (ntrans L N r x i) (rtrans L N r x i) x := rfl

/-- HOL `mtrans`（`tame_defs2.hl:484-485`）。 -/
theorem mtrans_def (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (i : ℕ) : mtrans L N r x i = lm L (rtrans L N r x i) x := rfl

/-- HOL `ftrans 0 = SND x`（`tame_defs2.hl:481-482` 的 `i = 0` 分支）。 -/
theorem ftrans_zero (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) :
    ftrans L N r x 0 = x.2 := by
  simp [ftrans]

/-! ## 3. `betwn_core_reduction_lemma`（`reduction5.hl:19-52`）

HOL 陈述（逐字，`reduction5.hl:19-38`）：

```
!L N r x k.
  uniq (core L r) /\
  ~(k = 0) /\
  (!i. i < k /\
      betwn (find_face L x) (ytrans L N r x i) (ztrans L N r x i) = []
      ==> ~(next_el (core L r) (FST (ytrans L N r x i)) = FST (ztrans L N r x i))) ==>
  (betwn (find_face L x) (ytrans L N r x 0) (ztrans L N r x 0) = []
   ==> ~(next_el (core L r) (FST (ytrans L N r x 0)) = FST (ztrans L N r x 0))) /\
  (!i. i < k /\
      betwn (find_face L x) (ytrans L N r x i) (ztrans L N r x i) = []
      ==> ~MEM (FST (ytrans L N r x i),FST (ztrans L N r x i))
             (list_pairs (core L r)))
```

HOL 证明（`reduction5.hl:42-51`）只用两条逻辑步骤：
① 第一合取项 = 前提在 `i = 0` 处的实例（`0 < k` 由 `~(k = 0)` 得到）；
② 第二合取项由 `mem_list_pairs_explicit` 把 `MEM (a,b) (list_pairs (core L r))`
   换成 `b = next_el (core L r) a`，再与前提冲突。
Lean 侧逐句镜像，`uniq (core L r)` 恰好是 `mem_list_pairs_explicit` 的 `uniq` 前提。 -/
theorem betwnCoreReductionLemma (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (k : ℕ) (huniq : (core L r).Nodup) (hk : k ≠ 0)
    (hmain : ∀ i, i < k →
      between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
      nextEl (core L r) (ytrans L N r x i).1 ≠ (ztrans L N r x i).1) :
    (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
      nextEl (core L r) (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1) ∧
    (∀ i, i < k →
      between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
      ((ytrans L N r x i).1, (ztrans L N r x i).1) ∉ listPairs (core L r)) := by
  refine ⟨fun h0 => hmain 0 (Nat.pos_of_ne_zero hk) h0, ?_⟩
  intro i hi hbet hmem
  exact hmain i hi hbet (mem_listPairs_nextEl huniq hmem)

end Kepler.Text.Reduction5
