/-
  Kepler.Text.Reduction3Thm14e — J5-8 W2-3b：A4 + C1
  （reduction3.hl:4105-4169 本体 / :3690-3729）。

  ┌─ 归属对账（HOL Light Flyspeck text_formalization/tame/reduction3.hl）──
  │ C1 :3690 `split_normal_list_split_face` → `splitNormalListSplitFace`
  │ A4 :4105 `fgraph_quotient_list_transform` → `fgraphQuotientListTransform`
  └────────────────────────────────────────────────────────────────

  **路线（纯接线，零本体重写）**：
  · C1 = A1（`splitNormalListSplitList`，W2-3a）实例化：
    `coreSplitNormalList` 展开 + `hmap` 改写 + `hsplitEq` 换 `(f1,f2)` +
    `FST (prev_el z) = FST z`（`hprevFst` 槽）挪 splitFace 端点。
  · A4 = A3（`fgraphQuotientListTransformLemma`，W2-3a）实例化：
    `coreSplitNormalList` 展开 + `hmap`/`hcore` 改写 ⇒ A3 的 hsplit；
    A3 的 `hnt` 由 `ntrans1`（IdxSplit）+ `find_face L y = find_face L x`
    （`findFaceDarts_congr_of_mem` 自证，ly ∈ face x 由 `ytranMeF`@0 供）给。
  · **DIFFERS**：`assumption_setK10` / `core_split_normal_list_assumption` /
    `r_trans_eq_assumption` / `newvertex_prepped` / `vertices_set2 g` /
    `find_face L x = fx` / `prev_el (core L r) v,v = x` 等 HOL 未消费前提不携入；
    `coreSplitNormalList L N r x`（逐状态槽） + `hprevFst`（HOL 从 K10 取
    `FST (prev_el r z) = FST z`）作显式前提。`ytrans 0 = ly`、`ztrans 0 = lz`
    为定义级（`ytrans = ly ∘ rtrans`、`rtrans … 0` rfl）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm14d
import Kepler.Text.Reduction5J5IdxSplit
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph between fgraph replace replace3 splitFace split_face)
open Kepler.Assembly (GoodList findFaceDarts prevEl)
open Kepler.Text.Reduction5
  (Dart core quotientList ntrans rtrans ytrans ztrans ly lz splitNormalList
    coreSplitNormalList transformCount finalList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- **W2-3b C1：HOL `split_normal_list_split_face`**（reduction3.hl:3690-3729）：
`core_split_normal_list` ⇒ `split_face (core L r, b) (FST y0) (FST z0) newVs` 的两片
= `Face (core L f1) F, Face (core L f2) F`。 -/
theorem splitNormalListSplitFace (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (v : ℕ) (f1 f2 : List Dart) (b : Bool)
    (newVs : List ℕ)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hnf : ¬ finalList L r)
    (hsplitEq : splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
        (prevEl r (ztrans L N r x 0)) = (f1, f2))
    (hprevFst : (prevEl r (ztrans L N r x 0)).1 = (ztrans L N r x 0).1)
    (hmap : (between (findFaceDarts L x) (ytrans L N r x 0)
        (ztrans L N r x 0)).map (fun d => d.1) = newVs)
    (hcs : coreSplitNormalList L N r x) :
    split_face (Face.mk (core L r) b) (ytrans L N r x 0).1
        (ztrans L N r x 0).1 newVs
      = (Face.mk (core L f1) false, Face.mk (core L f2) false) := by
  unfold Kepler.Text.Reduction5.coreSplitNormalList at hcs
  dsimp only at hcs
  -- hmap（HOL 的 ytrans/ztrans 形 ⇒ coreSplitNormalList 展开后的 ly/lz 形，定义级）
  have hmap' : (between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x)
      (Kepler.Text.Reduction5.lz L N r x)).map
      (fun d => d.1) = newVs := hmap
  rw [hmap'] at hcs
  -- A1 实例化
  have hsp := splitNormalListSplitList L N r x b hL hgn hm hir hnf
    (y := ytrans L N r x 0) (z' := prevEl r (ztrans L N r x 0))
    (f := findFaceDarts L x) (newVs := newVs) hcs
  rw [hsplitEq] at hsp
  rw [hprevFst] at hsp
  exact hsp

/-- **W2-3b A4：HOL `fgraph_quotient_list_transform`**（reduction3.hl:4105-4169）：
`fgraph g = quotient L N` 经一次 `splitFace g (FST y0) (FST z0) oldF newVs` 后
= `quotient L (ntrans 1)`。 -/
theorem fgraphQuotientListTransform (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (g : Graph) (oldF : Face) (g' : Graph)
    (newVs : List ℕ)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hnf : ¬ finalList L r)
    (hfg : fgraphOfGraph g = quotientList L N)
    (hcore : core L r = oldF.vertices)
    (hmem : oldF ∈ g.faces)
    (hstep : (splitFace g (ytrans L N r x 0).1 (ztrans L N r x 0).1
      oldF newVs).2.2 = g')
    (hprevFst : (prevEl r (ztrans L N r x 0)).1 = (ztrans L N r x 0).1)
    (hmap : (between (findFaceDarts L x) (ytrans L N r x 0)
        (ztrans L N r x 0)).map (fun d => d.1) = newVs)
    (hcs : coreSplitNormalList L N r x) :
    fgraphOfGraph g' = quotientList L (ntrans L N r x 1) := by
  -- hsplit（A3 形）：coreSplitNormalList 展开 + hmap/hcore 改写
  unfold Kepler.Text.Reduction5.coreSplitNormalList at hcs
  dsimp only at hcs
  have hmap' : (between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x)
      (Kepler.Text.Reduction5.lz L N r x)).map
      (fun d => d.1) = newVs := hmap
  rw [hmap', hcore] at hcs
  -- hstep 的 splitFace 端点是 prev_el z（A3 形）⇒ 由 hprevFst 挪回 z
  have hstep' : (splitFace g (ytrans L N r x 0).1
      (prevEl r (ztrans L N r x 0)).1 oldF newVs).2.2 = g' := by
    rw [hprevFst]
    exact hstep
  -- A3 的 hnt：ntrans1 + find_face L (ly …) = find_face L x
  have hx : x ∈ Kepler.Assembly.listOfDarts L :=
    Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hlyF : Kepler.Text.Reduction5.ly L r x ∈ findFaceDarts L x := by
    have h := Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl 0
    simpa only [Kepler.Text.Reduction5.ytrans_def, Kepler.Text.Reduction5.rtrans_zero]
      using h
  have hfindLy : findFaceDarts L (Kepler.Text.Reduction5.ly L r x)
      = findFaceDarts L x :=
    Kepler.Text.TameLp.findFaceDarts_congr_of_mem hL.1 hx hlyF
  have hnt : ntrans L N r x 1
      = replace r [(splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
          (prevEl r (ztrans L N r x 0))).2] N
        ++ [(splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
          (prevEl r (ztrans L N r x 0))).1] := by
    have h := Kepler.Text.Reduction5.ntrans1 L N r x hnf
    rw [hfindLy] at h
    exact h
  exact fgraphQuotientListTransformLemma L N r x g (ntrans L N r x 1) oldF g'
    (ytrans L N r x 0) (prevEl r (ztrans L N r x 0)) (findFaceDarts L x) newVs
    hL hgn hm hir hnf hfg rfl hcore hmem hstep' hcs hnt

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.splitNormalListSplitFace
#print axioms Kepler.Text.Reduction3.fgraphQuotientListTransform
