/-
  Kepler.Text.TameSpine.Reduction3J5PartsBetwnFinal — tame-corr nb30：J5-6
  `parts_betwn_final`（HOL betwn_corek_z_x.hl:503）。

  路线：`partsImpure`（在库，逐 atom 条件）+ `uniqBetwn` + `eqMemNextElLast`
  + `nextElBetwnSame` + `final r` + `edgeNondegFXorNi`（HOL 同构）。

  实例记账（BEq 世界第 5 例）：目标陈述的 `between` 在 Dart 上解析为
  `instBEqProd`；`eqMemNextElLast` / `nextElBetwnSame` / `betwnMem` 的
  `[DecidableEq α]` 世界解析为 `instBEqOfDecidableEq`。先用 `betweenInstEq`
  （Reduction5J5BetweenInst:42）把目标平移到 decidable 世界；`nextEl` 的
  两处隔离点用 `nextElInstEq`（Reduction5Kbwpbhq:86）双向折算。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.TameSpine.Reduction3CoreSplitNormal
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.ChainListsL2
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.Reduction5J5BetweenInst

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList eList listOfDarts)
open Kepler.Text.Reduction5 (Dart parts finalList)

/-- **HOL `parts_betwn_final`**（betwn_corek_z_x.hl:503）：
`good_list ∧ (∀x∈r, x∈darts) ∧ EdgeNondeg ∧ r.Nodup ∧ final r ∧ y,z∈r ∧ y≠z
⇒ parts L (between r y z) = (between r y z).map (fun x => [x])`。 -/
theorem partsBetwnFinal (L : fgraph ℕ) (hL : GoodList L) {r : List Dart}
    (hall : ∀ x ∈ r, x ∈ listOfDarts L)
    (hne : (Kepler.Text.TameLp.hypermapOfList L hL).EdgeNondegenerate)
    (hnd : r.Nodup) (hfin : finalList L r) {y z : Dart} (hy : y ∈ r) (hz : z ∈ r)
    (hyz : y ≠ z) :
    parts L (between r y z) = (between r y z).map (fun x => [x]) := by
  -- 目标平移到 DecidableEq 实例世界（BEq 世界第 5 例桥）
  rw [Kepler.Text.Reduction5.betweenInstEq r y z]
  set B : List Dart := @Kepler.Graphs.between Dart instBEqOfDecidableEq r y z with hB
  apply Kepler.Text.Reduction5.partsImpure
  · intro x hx
    by_cases hlast : x = B.getLastD (0, 0)
    · exact Or.inl hlast
    · refine Or.inr ?_
      have hx' : x ∈ @Kepler.Graphs.between Dart instBEqOfDecidableEq r y z := by
        rw [hB] at hx
        exact hx
      have hxne : B.getLast! ≠ x := by
        intro hc
        exact hlast (hc.symm.trans (Kepler.Text.ChainBridge.getLast!_eq_getLastD B))
      have hxne' : (@Kepler.Graphs.between Dart instBEqOfDecidableEq r y z).getLast! ≠ x :=
        hB ▸ hxne
      have hnextmem : @nextEl Dart instBEqOfDecidableEq r x
          ∈ @Kepler.Graphs.between Dart instBEqOfDecidableEq r y z :=
        (eqMemNextElLast hyz hy hz hx' hnd).mpr hxne'
      have hBsame : @nextEl Dart instBEqOfDecidableEq
            (@Kepler.Graphs.between Dart instBEqOfDecidableEq r y z) x
          = @nextEl Dart instBEqOfDecidableEq r x :=
        nextElBetwnSame hyz hy hz hx' hnextmem hnd
      have hxr : x ∈ r := Kepler.Text.Reduction5.betwnMem hx'
      have hfinx : fList L x = @nextEl Dart instBEqProd r x := hfin x hxr
      have hedge : fList L x ≠ fList L (eList x) :=
        Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL hne (hall x hxr)
      intro hcon
      rw [hB] at hcon
      exact hedge (hfinx.trans ((Kepler.Text.Reduction5.nextElInstEq r x).trans
        ((hBsame.symm).trans (((Kepler.Text.Reduction5.nextElInstEq _ x).symm).trans hcon))))
  · rw [hB]
    have h := uniqBetwn hnd hy hz hyz
    rw [Kepler.Text.Reduction5.betweenInstEq r y z] at h
    exact h

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.partsBetwnFinal
