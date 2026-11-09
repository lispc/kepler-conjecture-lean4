/-
  JcajyduAqLeaf8W3ab — AQ8 波 3ab：**junction**（SND 在 y 处的 parts 分裂）。

  ┌─ 目标与依据 ──────────────────────────────────────────────────
  │ `parts L SND = parts L arc3 ++ parts L farc`，其中
  │   arc3 = [z] ++ between r z y ++ [y]、farc = between f y z（f = 面表）。
  │ `partsCat` 的断点前提由 **W3w**（`(between f y z).head! = fList L (l'y)`）
  │ + `nextElCatLast1` + `fListInjDarts`/`isRestrictedEListNondeg` 给出。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3ab_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3z
import Kepler.Text.TameSpine.JcajyduAqLeaf8W3w

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-- 连接的末元（右半非空）；本版无公开名。 -/
private theorem aq8w3ab_getLast!_append {α : Type*} [Inhabited α] (s : List α)
    {t : List α} (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

/-- **junction**：`SND = arc3 ++ farc` 且 `farc` 非空时，`parts` 恰在接缝处分裂。

`partsCat` 四前提：① 分解等式 rfl；② `arc3.getLast! = l'y`（私证 + 单点表）；
③ `arc3 ≠ []`；④ `farc ≠ []`（入参）；⑤ 断点
`nextEl SND y ≠ fList L (eList y)`——由 W3w（`farc.head! = fList L y`）+ 注入性/非退化。 -/
theorem aq8w3ab_partsSndSplit (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hsN : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x) ∈ ntransSpine L N r x 1)
    (hfarne : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x) ≠ []) :
    partsSpine L (([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x))
      = partsSpine L ([lZSpine L N r x] ++ between r (lZSpine L N r x)
          (lYSpine L r x) ++ [lYSpine L r x])
        ++ partsSpine L (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL h1 h2 h3 h4 h5 hgn hm
  obtain ⟨hndS, hneS⟩ := normalListUniqNonnil hnN hsN
  -- ② arc3.getLast! = l'y
  have hbetweenNe : (between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) ≠ [] := by
    intro h0
    have hmem : lYSpine L r x ∈ (between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) :=
      List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
    rw [h0] at hmem
    exact List.not_mem_nil hmem
  have hlast : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]).getLast! = lYSpine L r x := by
    exact (aq8w3ab_getLast!_append
      ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x))
      (t := [lYSpine L r x]) (List.cons_ne_nil _ _)).trans rfl
  -- ③ arc3 ≠ []
  have harcne : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) ≠ [] := by
    intro h0
    have hmem : lZSpine L N r x ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) :=
      List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_singleton_self _))))
    rw [h0] at hmem
    exact List.not_mem_nil hmem
  -- ⑤ 断点
  have hhead : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).head! = fList L (lYSpine L r x) :=
    aq8w3w_betwnFaceHead L hL hgn hm hf hfarne
  have hnext : nextEl (([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) ++ between
      (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))
      (lYSpine L r x)
      = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).head! := by
    have h1 : nextEl (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++ between
        (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))
        (([lZSpine L N r x] ++ between r (lZSpine L N r x)
          (lYSpine L r x) ++ [lYSpine L r x]).getLast!)
        = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).head! :=
      nextElCatLast1 hndS harcne hfarne
    rwa [hlast] at h1
  have hne : nextEl (([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) ++ between
      (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))
      (lYSpine L r x) ≠ fList L (eList (lYSpine L r x)) := by
    rw [hnext, hhead]
    intro hcon
    have hyD : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
    have heD : eList (lYSpine L r x) ∈ listOfDarts L := goodListEList hL hyD
    exact isRestrictedEListNondeg hL hm.1.1 hyD
      ((fListInjDarts L hL hyD heD).mp hcon).symm
  exact partsCat L (r := _) (u := _) (v := _) (x := lYSpine L r x)
    rfl hlast harcne hfarne hne hndS

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3ab_partsSndSplit
