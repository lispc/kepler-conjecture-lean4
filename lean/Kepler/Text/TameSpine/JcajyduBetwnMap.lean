/-
  Kepler.Text.TameSpine.JcajyduBetwnMap — jcajydu-c2（C2=J0 波）批 J0-b₁：
  betwn_corek_z_x.hl / betwn_core0_z_y.hl 依赖闭包的**映射/分件层**
  （接续批 J0-a = JcajyduBetwnBase.lean，commit 04a8443c 落库）。
  全部为 α/泛型事实，零 `transform_assumption` 消费（AQ 塔阻塞见
  J0-a DELIVERY §1.2）。

  本批镜像对象（HOL 逐条锚）：
  - AQ12.hl:351 `map_betwn`（本批 `mapBetwn`）；
  - AQ8.hl:88 `parts_mem_exists`（本批 `partsMemExists`；`parts` ↦
    `TameList7.partsSpine`，与 J0 波 TameSpine 词汇一致）。

  载体折算（沿批 J0-a 约定）：`betwn` ↦ `Kepler.Graphs.between`、
  `uniq` ↦ `List.Nodup`、`indexl` ↦ `List.idxOf`、`MAP` ↦ `List.map`。

  红线：零 sorry、零 axiom、零 native_decide、零既有文件触碰、主仓 tracked
  零改动。
-/
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.TameList7

namespace Kepler.Text.TameSpine

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (between fgraph)
open Kepler.Text.TameLp (getElem_idxOf idxOf_getElem getD_eq_getElem_of_lt
  nextEl_mem_of_mem)

/-- **HOL `Aq12.map_betwn`**（AQ12.hl:351）：
`uniq s ∧ (∀ u v ∈ s, f u = f v → u = v) ∧ MEM y s ∧ MEM z s ∧ ~(y=z) →
MAP f (betwn s y z) = betwn (MAP f s) (f y) (f z)`。 -/
theorem mapBetwn {α β : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] [BEq β]
    [LawfulBEq β] [DecidableEq β]
    {s : List α} {f : α → β} (hnd : s.Nodup)
    (hinj : ∀ u ∈ s, ∀ v ∈ s, f u = f v → u = v)
    {y z : α} (hy : y ∈ s) (hz : z ∈ s) (_hyz : y ≠ z) :
    (between s y z).map f = between (s.map f) (f y) (f z) := by
  have hmapnd : (s.map f).Nodup := by
    refine (List.nodup_map_iff_inj_on hnd).mpr fun u hu v hv hfv => ?_
    exact hinj u (hu) v (hv) hfv
  have hmy : f y ∈ s.map f := List.mem_map_of_mem hy
  have hmz : f z ∈ s.map f := List.mem_map_of_mem hz
  have hidxm : ∀ u ∈ s, (s.map f).idxOf (f u) = s.idxOf u := by
    intro u hu
    have hmu : f u ∈ s.map f := List.mem_map_of_mem hu
    have hjlt : (s.map f).idxOf (f u) < (s.map f).length :=
      List.idxOf_lt_length_iff.mpr hmu
    have hjlts : (s.map f).idxOf (f u) < s.length := by
      have h := List.idxOf_lt_length_iff.mpr hmu
      rw [List.length_map] at h
      exact h
    have h1 : (s.map f)[(s.map f).idxOf (f u)] = f u := getElem_idxOf hmu
    rw [List.getElem_map] at h1
    have hjmem : s[(s.map f).idxOf (f u)] ∈ s := List.getElem_mem hjlts
    have heq : s[(s.map f).idxOf (f u)] = u := hinj _ hjmem _ hu h1
    have hcongr : s.idxOf u = s.idxOf (s[(s.map f).idxOf (f u)]) :=
      congrArg s.idxOf heq.symm
    rw [hcongr]
    exact (idxOf_getElem hnd hjlts).symm
  rw [betwnTakeDrop hnd hz, betwnTakeDrop hmapnd hmz,
    hidxm y hy, hidxm z hz]
  split
  · rw [List.map_take, List.map_drop]
  · rw [List.map_append, List.map_take, List.map_drop]

/-- **HOL `Aq8.parts_mem_exists`**（AQ8.hl:88）：
`uniq r ∧ MEM x r → ∃ p ∈ parts L r, MEM x p`。
（`parts` ↦ `TameList7.partsSpine`，J0 波 TameSpine 词汇。） -/
theorem partsMemExists (L : fgraph ℕ) {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hun : r.Nodup) (hx : x ∈ r) :
    ∃ p ∈ partsSpine L r, x ∈ p := by
  have hne : r ≠ [] := List.ne_nil_of_mem hx
  have hmem : x ∈ (partsSpine L r).flatten := by
    rw [partsFlatten L hun hne]; exact hx
  exact List.mem_flatten.mp hmem

end Kepler.Text.TameSpine
