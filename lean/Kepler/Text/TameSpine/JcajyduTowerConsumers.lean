/- JcajyduTowerConsumers — 塔顶无条件形消费者 alias（W1）。零新证明、零禁词。 -/
import Kepler.Text.TameSpine.TameList72
import Kepler.Text.TameSpine.JcajyduAqTowerTop

set_option autoImplicit false
set_option linter.unusedVariables false
namespace Kepler.Text.TameSpine
open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- `aqiunpp1` 无条件形（HOL `AQIUNPP1`）。 -/
theorem aqiunpp1_top (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) :
    NormalListSpine hL (ntransSpine L N r x 1) :=
  aqiunpp1 L hL (transformAssumptionSpine_top L hL) hgn hm

/-- `aqiunpp2` 无条件形（HOL `AQIUNPP2`）。 -/
theorem aqiunpp2_top (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) :
    MarkedListSpineFull hL (ntransSpine L N r x 1) (rtransSpine L N r x 1) x :=
  aqiunpp2 L hL (transformAssumptionSpine_top L hL) hgn hm

/-- `aqiunpp3` 无条件形（HOL `AQIUNPP3`）。 -/
theorem aqiunpp3_top (L : fgraph ℕ) (hL : GoodList L) (i : ℕ)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) :
    MarkedListSpineFull hL (ntransSpine L N r x i) (rtransSpine L N r x i) x :=
  aqiunpp3 L hL i (transformAssumptionSpine_top L hL) hgn hm

/-- `DANGEYJ_concl` 的无条件形（`_hta` 原为哑参数，传 top）。 -/
def DANGEYJ_concl_top (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) : Prop :=
  DANGEYJ_concl L hL (transformAssumptionSpine_top L hL) hgn

/-- `DANGEYJ` 无条件形（HOL `DANGEYJ`）。 -/
theorem DANGEYJ_top (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) : DANGEYJ_concl_top L hL hgn :=
  DANGEYJ L hL (transformAssumptionSpine_top L hL) hgn

#print axioms aqiunpp1_top
#print axioms aqiunpp2_top
#print axioms aqiunpp3_top
#print axioms DANGEYJ_concl_top
#print axioms DANGEYJ_top
#print axioms transformAssumptionSpine_top
