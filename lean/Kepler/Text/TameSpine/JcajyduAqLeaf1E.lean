/-
  Kepler.Text.TameSpine.JcajyduAqLeaf1E — AQ1 叶第五批：`f1 × f2` 用的
  **弧恒等式 ⊆ 半向**（`betwn r y z ⊆ [nextEl r y] ++ betwn r (nextEl r y) z1 ++ [z1]`）。

  这是 TameList72 公开化三件的第一次实战消费：
  - `betwn_succ_subset`：`betwn r y z ⊆ [nextEl r y] ++ betwn r (nextEl r y) z`（剥首端点 y）；
  - `betwn_next_subset`：`betwn r a (nextEl r z1) ⊆ betwn r a z1 ++ [z1]`（`nextEl r z1 = z` 折后即
    `betwn r a z ⊆ betwn r a z1 ++ [z1]`，右端点前移一格）；
  - 前提 `nextEl r y ≠ z1` = Leaf1 ②（`aq1_nextElYNePrevElZ`）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf1D
import Kepler.Text.TameSpine.TameList72

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

/-- **弧恒等式的 ⊆ 半向**（`f1 × f2` 的第一步）：
`betwn r y z ⊆ [nextEl r y] ++ betwn r (nextEl r y) z1 ++ [z1]`，
其中 `z1 = prevEl r z`（使用者以 `nextElPrevElUniq` 供 `hnext`）。 -/
theorem aq1e_betwnSubset {r : List (ℕ × ℕ)} {y z z1 : ℕ × ℕ}
    (hrnd : r.Nodup) (hyr : y ∈ r) (hzr : z ∈ r) (hz1r : z1 ∈ r)
    (hnext : nextEl r z1 = z) (hra : nextEl r y ≠ z1) :
    ∀ d ∈ between r y z,
      d ∈ ([nextEl r y] ++ between r (nextEl r y) z1) ++ [z1] := by
  intro d hd
  have hsucc : d ∈ [nextEl r y] ++ between r (nextEl r y) z :=
    betwn_succ_subset hrnd hyr hzr hd
  have hnextM : nextEl r y ∈ r := nextEl_mem_of_mem hyr
  have hpeel : between r (nextEl r y) (nextEl r z1)
      ⊆ between r (nextEl r y) z1 ++ [z1] :=
    betwn_next_subset hrnd hnextM hz1r hra
  rw [hnext] at hpeel
  rcases List.mem_append.mp hsucc with h1 | h1
  · exact List.mem_append_left ([z1] : List (ℕ × ℕ))
      (List.mem_append_left (between r (nextEl r y) z1) h1)
  · rcases List.mem_append.mp (hpeel h1) with h2 | h2
    · exact List.mem_append_left ([z1] : List (ℕ × ℕ))
        (List.mem_append_right ([nextEl r y] : List (ℕ × ℕ)) h2)
    · exact List.mem_append_right ([nextEl r y] ++ between r (nextEl r y) z1) h2

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq1e_betwnSubset
