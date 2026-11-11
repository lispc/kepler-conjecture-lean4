/-
  Kepler.Text.Reduction5J7W2 — J5-7 W2 d_y 族（1/2）：
  · `betwnNilChain` —— HOL `Tame_list.betwn_nil`（tame_list.hl:13449）链形公开件
    （Spine 版 `TameSpine.betwnNil` 在库不重落；证体与私件 `t5c_betwn_nil` 同法：
    `sizeBetwn` + `indexfOne`/`nextElIndexf` + `indexfZeroEq` + `sizelGt1`）。
  · `memBetwnDY` —— HOL `mem_betwn_d_y`（betwn_core0_z_y.hl:666-811）见 J7W2b。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.TameSpine.TameList53
import Kepler.Text.Reduction5J7W1d
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.Reduction5TwelveT
import Kepler.Text.PwssratTail
import Kepler.Text.PwssratFace
import Kepler.Text.TameSpine.JcajyduAqLeaf12A
import Kepler.Text.TameSpine.JcajyduAqLeaf12B
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.Reduction3CoreSplitNormal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- **W2-0：链形 `betwn_nil`**（HOL `Tame_list.betwn_nil`，tame_list.hl:13449）：
`uniq f ∧ a ≠ b ∧ a ∈ f ∧ b ∈ f ⇒ (betwn f a b = [] ↔ b = nextEl f a)`。
公开链形；Spine 版 `TameSpine.betwnNil` 不重落。 -/
theorem betwnNilChain {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {f : List α} {a b : α} (hnd : f.Nodup) (hab : a ≠ b)
    (ha : a ∈ f) (hb : b ∈ f) :
    between f a b = [] ↔ b = nextEl f a := by
  have hlen2 : 1 < f.length := Kepler.Text.TameSpine.sizelGt1 ha hb hab
  have hne0 : Kepler.Text.TameSpine.indexf a b f ≠ 0 := fun h0 =>
    hab (Kepler.Text.TameSpine.indexfZeroEq ha hb h0)
  constructor
  · intro h
    have hsz := Kepler.Text.TameSpine.sizeBetwn hnd ha hb hab
    rw [h, List.length_nil] at hsz
    have hidx : Kepler.Text.TameSpine.indexf a b f = 1 := by omega
    exact (Kepler.Text.TameSpine.indexfOne ha hb hnd hidx).symm
  · intro h
    have hidx : Kepler.Text.TameSpine.indexf a b f = 1 := by
      rw [h]
      exact Kepler.Text.TameSpine.nextElIndexf ha
        (Kepler.Text.TameLp.nextEl_mem_of_mem ha) hnd rfl hlen2
    have hsz := Kepler.Text.TameSpine.sizeBetwn hnd ha hb hab
    rw [hidx] at hsz
    exact List.length_eq_zero_iff.mp (by simpa using hsz)

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.betwnNilChain
