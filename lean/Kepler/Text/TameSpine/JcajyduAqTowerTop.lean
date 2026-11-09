/-
JcajyduAqTowerTop: 塔顶装配（槽形）。

13 叶中 12 叶已真证（`aq1`–`aq12`，全标准三）；本件把 `aq13Concl` 留作**唯一显式槽**，
填掉其余 12 槽即得 `transformAssumptionSpine L hL`（= HOL `transform_assumption` 的目标形）。

AQ13 收口后一行代入：
`transformAssumptionSpine L hL := transformAssumptionSpine_of_aq13 L hL (aq13 L hL)`
（`aq13` 落地时把 `h13` 换成它，或另立 3 行文件）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf1F
import Kepler.Text.TameSpine.JcajyduAqTowerE2
import Kepler.Text.TameSpine.JcajyduAqSplit1H
import Kepler.Text.TameSpine.JcajyduAqLeaf4W3b
import Kepler.Text.TameSpine.JcajyduAqLeaf5
import Kepler.Text.TameSpine.JcajyduAqTowerBase
import Kepler.Text.TameSpine.JcajyduAqLeaf7
import Kepler.Text.TameSpine.JcajyduAqLeaf8W3ae
import Kepler.Text.TameSpine.JcajyduAqLeaf9W2
import Kepler.Text.TameSpine.JcajyduAqLeaf10G
import Kepler.Text.TameSpine.JcajyduAqLeaf11
import Kepler.Text.TameSpine.JcajyduAqLeaf12AC
import Kepler.Text.TameSpine.JcajyduAqLeaf13W4b

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)

/-- **塔顶（12/13 槽形）**：`aq13Concl` 为唯一显式槽，其余 12 叶已由真证定理填入。 -/
theorem transformAssumptionSpine_of_aq13 (L : fgraph ℕ) (hL : GoodList L)
    (h13 : aq13Concl L hL) : transformAssumptionSpine L hL :=
  transformAssumptionOfAq L hL (aq1 L hL) (aq2 L hL) (aq3 L hL) (aq4 L hL)
    (aq5 L hL) (aq6 L hL) (aq7 L hL) (aq8 L hL) (aq9 L hL) (aq10 L hL)
    (aq11 L hL) (aq12 L hL) h13


/-- **塔顶（13/13，无条件形）**：13 叶全部真证，直接给出 `transformAssumptionSpine`。 -/
theorem transformAssumptionSpine_top (L : fgraph ℕ) (hL : GoodList L) :
    transformAssumptionSpine L hL :=
  transformAssumptionSpine_of_aq13 L hL (aq13 L hL)

end Kepler.Text.TameSpine

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.TameSpine.transformAssumptionSpine_of_aq13
#print axioms Kepler.Text.TameSpine.transformAssumptionSpine_top
