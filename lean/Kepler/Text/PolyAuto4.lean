/-
Port of the HOL Light Flyspeck polyhedron theory (Packing chapter), slice 4:
skeleton pass of `scripts/polyhedron.hl` :570-:744 (batch 4 of 8+).

Source: `lean/scripts/polyhedron.hl` (persistent copy of Flyspeck book
formalization `text_formalization/packing/polyhedron.hl`, John Harrison +
Hoang Le Truong, 2010-2011).

Coverage (batch 4, theorems whose `let ... = prove` starts in :570-:744,
exactly 10):
- `CONVEX_RELATIVE_INTERIOR_FACET` (:570)
- `CONNECTED_RELATIVE_INTERIOR_FACET` (:578)
- `CONNECTED_HALF_LINE` (:586)
- `RELATIVE_SUBSET_FCHANGE` (:593)
- `AFF_GT_SUBSET_FCHANGED` (:607)
- `CONNECTED_HALF_LINE1` (:620)
- `LEMMA` (:621, inner `let` of CONNECTED_HALF_LINE1) → renamed `LEMMA_b4`
  here: HOL reuses the name `LEMMA` twice (:517 inside CONVEX_RELATIVE_INTERIOR,
  owned by concurrent batch 3; :621 ours); to avoid the collision our :621
  item is ported as `LEMMA_b4`.
- `CONNECTED_COMPONENT_OF_SUBSET` (:657)
- `CONNECTED_COMPONENT_TRANS` (:662)
- `CONNECTED_FCHANGED` (:675-:744, batch centerpiece: connectedness of the
  "fchanged" region)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs are `by sorry`, to be filled by the auto_loop harness.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  `t % v` ↔ `t • v`; `vec 0` ↔ `(0 : V3)`.
- HOL `relative_interior s` ↔ `intrinsicInterior ℝ s`. This Mathlib
  (v4.32.2) has no `relative_interior`/`rinterior`; the relative interior is
  `intrinsicInterior` (Mathlib/Analysis/Convex/Intrinsic.lean:61), with
  `mem_intrinsicInterior` (Intrinsic.lean:87) as the membership simp lemma.
- HOL `connected s` ↔ `IsConnected s`: Mathlib renamed `Connected` to
  `IsConnected` (Mathlib/Topology/Connected/Basic.lean); the task's
  "Mathlib Connected" is this `IsConnected`.
- HOL `connected_component s x y` ↔ `x ∈ connectedComponentIn s y`
  (repo precedent: Kepler/Text/PlanarityComponent.lean:31).
- HOL `bounded s` ↔ `Bornology.IsBounded s` (Mathlib/Topology/
  Bornology/Basic.lean:99; the old `Metric.Bounded` is now
  `Bornology.IsBounded`).
- `fchanged` IS a genuine `new_definition` of polyhedron.hl (:512, between
  the POLYHEDRON_FAN block and CONVEX_RELATIVE_INTERIOR, i.e. textually in
  the concurrent batch-3 lane :342-:569). No Lean file defines it yet
  (`grep -rw fchanged Kepler/` = 0 hits), and this batch's statements need
  it, so it is ported here verbatim from :512 as `Kepler.Text.fchanged`.
  Merge note: if batch 3 lands its own `fchanged`, delete one copy and
  re-point; later batches (FCHANGED_OPEN :891, FCHANGED_ONE_TO_ONE :1132,
  YFAN_SUBSET_FCHANGED :1564, ...) should import this file instead of
  redefining.
- `polyhedron`, `face_of`, `facet_of` are NOT defined in polyhedron.hl;
  they are HOL Light Multivariate definitions (flyspeck Definition 4.7/4.8,
  QLITJET/QSRHLXB). Verbatim bodies taken from the flyspeck-bundled HOL
  tree: `reference/flyspeck/azure/hol-light-nat/Multivariate/polytope1.ml`
  (`face_of` :22, `facet_of` :1506, `polyhedron` :2546). No Lean port
  exists anywhere in the repo (grep = 0 hits), so they are ported here as
  `FaceOf`/`FacetOf`/`polyhedron` (with auxiliary `affDim` for HOL
  `aff_dim`, ∅ ↦ -1). Merge note: the canonical home is probably the
  POLYHEDRON_FAN / CONVEX_RELATIVE_INTERIOR lane (batch 2/3); if those
  land identical defs, delete our copies and re-point.
- Imports: `PlanarityAuto16` + `ConformingDefs` per batch plan (the cited
  ConformingAuto-chain rides in transitively through PlanarityAuto16);
  `Mathlib` is imported explicitly for `intrinsicInterior`,
  `connectedComponentIn`, `segment` (precedent:
  Kepler/Text/PlanarityAuto16.lean imports `Mathlib`). NO other PolyAuto
  files are imported (batches 1-3 are concurrent lanes).

Difficulty scale (for the fill-in pass): zuzhuang = assembly of already
ported lemmas; liangou = coefficient/rewriting bookkeeping; fenxi =
geometric content.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Classical

/-! ## 批 4 需要的上游定义（HOL 原文逐字移植；见文件头「合并去重」说明） -/

/-- HOL `aff_dim`（HOL Light Multivariate，`polytope1.ml` 使用；
∅ ↦ -1，否则仿射包方向的维数）。`WithBot`/`ℤ` 语义按 HOL 取 `ℤ`。 -/
noncomputable def affDim (s : Set V3) : ℤ :=
  if s = ∅ then -1 else (Module.finrank ℝ (vectorSpan ℝ s) : ℤ)

/-- HOL `t face_of s`（polytope1.ml:22，flyspeck Definition 4.7 QLITJET）：
```
t SUBSET s /\ convex t /\
!a b x. a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b) ==> a IN t /\ b IN t
```
-/
def FaceOf (t s : Set V3) : Prop :=
  t ⊆ s ∧ Convex ℝ t ∧
    ∀ a b x : V3, a ∈ s → b ∈ s → x ∈ t → x ∈ segment ℝ a b → a ∈ t ∧ b ∈ t

/-- HOL `f facet_of s`（polytope1.ml:1506）：
```
f facet_of s <=> f face_of s /\ ~(f = {}) /\ aff_dim f = aff_dim s - &1
```
-/
def FacetOf (f s : Set V3) : Prop :=
  FaceOf f s ∧ f ≠ ∅ ∧ affDim f = affDim s - 1

/-- HOL `polyhedron s`（polytope1.ml:2546，flyspeck Definition 4.8 QSRHLXB）：
```
polyhedron s <=> ?f. FINITE f /\ s = INTERS f /\
  (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x <= b})
```
-/
def polyhedron (s : Set V3) : Prop :=
  ∃ F : Set (Set V3), F.Finite ∧ s = ⋂₀ F ∧
    ∀ h ∈ F, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b}

/-- HOL `fchanged`（polyhedron.hl:512，`new_definition`，逐字移植）：
```
fchanged f={v| ?v1 t. v=t% v1 /\ v1 IN (relative_interior f)/\ t> &0}
```
即 `f` 相对内部各点出发的正射线之并。 -/
def fchanged (f : Set V3) : Set V3 :=
  {v : V3 | ∃ v1 : V3, ∃ t : ℝ, v = t • v1 ∧ v1 ∈ intrinsicInterior ℝ f ∧ 0 < t}

/-! ## polyhedron.hl :570-:744（批 4 主体） -/

/-- HOL polyhedron.hl :570-:577 `CONVEX_RELATIVE_INTERIOR_FACET`

HOL 原文：
```
!p f:(real^3->bool). polyhedron p /\ f facet_of p ==> convex (relative_interior f)
```

编码说明：`polyhedron`/`facet_of`/`relative_interior` 的编码见文件头；
`f facet_of p` 经 `FacetOf` 展开后自带 `FaceOf f p`，再由面是
polyhedron（FACE_OF_POLYHEDRON_POLYHEDRON）归约到批 3 的
`CONVEX_RELATIVE_INTERIOR_FACE`（:565，并行车道）。

证明思路：`FacetOf` 展开 → `FaceOf` 得 `f` 是 polyhedron 的面 →
`FACE_OF_POLYHEDRON_POLYHEDRON` + 批 3 `CONVEX_RELATIVE_INTERIOR_FACE`；
或直接用 `f` 凸（`FaceOf.2.1`）+ 凸集相对内部仍凸（HOL
`CONVEX_RELATIVE_INTERIOR` :514，未移植，就地证）。

候选已有引理：
- `FacetOf`/`FaceOf`（本文件，定义展开即得 `Convex ℝ f`）
- `CONVEX_RELATIVE_INTERIOR_FACE`（批 3 车道，polyhedron.hl:565；缺口）
- `intrinsicInterior_nonempty`（Mathlib/Analysis/Convex/Intrinsic.lean:463）
- 缺口：凸集的 `intrinsicInterior` 凸性（HOL `CONVEX_RELATIVE_INTERIOR`
  :514 尚无 Lean 版） -/
theorem CONVEX_RELATIVE_INTERIOR_FACET {p f : Set V3}
    (hp : polyhedron p) (hf : FacetOf f p) :
    Convex ℝ (intrinsicInterior ℝ f) := by
  sorry

/-- HOL polyhedron.hl :578-:585 `CONNECTED_RELATIVE_INTERIOR_FACET`

HOL 原文：
```
!p f:(real^3->bool). polyhedron p /\ f facet_of p ==> connected (relative_interior f)
```

编码说明：`connected` ↔ `IsConnected`（Mathlib 改名，见文件头）。

证明思路：`CONVEX_RELATIVE_INTERIOR_FACET`（上一条）得凸，再
`Convex.isConnected` 需非空：`f ≠ ∅`（`FacetOf.2.1`）+ `Convex ℝ f`
（`FaceOf.2.1`）+ `intrinsicInterior_nonempty` 类结果给非空。

候选已有引理：
- `CONVEX_RELATIVE_INTERIOR_FACET`（本文件）
- `Convex.isConnected`（Mathlib/Analysis/Convex/PathConnected.lean:88）
- `intrinsicInterior_nonempty`（Mathlib/Analysis/Convex/Intrinsic.lean:463）
- `FaceOf`/`FacetOf`（本文件） -/
theorem CONNECTED_RELATIVE_INTERIOR_FACET {p f : Set V3}
    (hp : polyhedron p) (hf : FacetOf f p) :
    IsConnected (intrinsicInterior ℝ f) := by
  sorry

/-- HOL polyhedron.hl :586-:592 `CONNECTED_HALF_LINE`

HOL 原文：
```
!x:real^3 v. connected(aff_gt {x} {v})
```

编码说明：`aff_gt` ↔ `affGt`（Kepler/Geom/Aff.lean:39，`Affsign` 编码）。

证明思路：`affGt {x} {v} = {u | ∃ t > 0, u = x + t • (v - x)}`（由
`Affsign` 定义在两点并集上展开），该开射线凸（`module`/系数论证），再
`Convex.isConnected` + 非空见证 `x + (1:ℝ) • (v - x)`。

候选已有引理：
- `affGt`（Kepler/Geom/Aff.lean:39）及其 `Affsign` 展开（Aff.lean:32）
- `Convex.isConnected`（Mathlib/Analysis/Convex/PathConnected.lean:88）
- 缺口：`CONVEX_AFF_GT`（fan.hl 系，未移植；就地展开两点情形） -/
theorem CONNECTED_HALF_LINE (x v : V3) : IsConnected (affGt {x} {v}) := by
  sorry

/-- HOL polyhedron.hl :593-:606 `RELATIVE_SUBSET_FCHANGE`

HOL 原文：
```
!p x f:(real^3->bool). bounded p /\ polyhedron p /\ x IN interior p /\
f facet_of p ==> (relative_interior f) SUBSET fchanged f
```

编码说明：`bounded` ↔ `Bornology.IsBounded`；`fchanged` 见本文件定义
（polyhedron.hl:512）。注意 HOL 证明实际只用到 `fchanged` 的展开
（bounded/polyhedron/interior 假设在本条中不消耗），仍逐字保留。

证明思路：展开 `fchanged`，对 `v ∈ intrinsicInterior ℝ f` 取
`v1 = v, t = 1`：`v = 1 • v ∧ v ∈ intrinsicInterior ℝ f ∧ 0 < 1`。

候选已有引理：
- `fchanged`（本文件，polyhedron.hl:512）
- `mem_intrinsicInterior`（Mathlib/Analysis/Convex/Intrinsic.lean:87）
- `one_smul`、`zero_lt_one`（Mathlib） -/
theorem RELATIVE_SUBSET_FCHANGE {p f : Set V3} {x : V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (hx : x ∈ interior p)
    (hf : FacetOf f p) :
    intrinsicInterior ℝ f ⊆ fchanged f := by
  sorry

/-- HOL polyhedron.hl :607-:619 `AFF_GT_SUBSET_FCHANGED`

HOL 原文：
```
!p x f:(real^3->bool) y. bounded p /\ polyhedron p /\ x IN interior p /\
f facet_of p /\ y IN (relative_interior f)
==> {v| ?t. &0< t /\ v=t%y} SUBSET fchanged f
```

编码说明：`{v | ∃ t > 0, v = t • y}` 即从原点出发过 `y` 的开射线；
同上，HOL 证明只用 `fchanged` 展开 + `y IN relative_interior f`。

证明思路：展开 `fchanged`，对 `v = t • y, 0 < t` 取 `v1 = y, t`，
`y ∈ intrinsicInterior ℝ f` 由 `hy` 给出。

候选已有引理：
- `fchanged`（本文件，polyhedron.hl:512）
- `Set.mem_setOf_eq`（Mathlib） -/
theorem AFF_GT_SUBSET_FCHANGED {p f : Set V3} {x y : V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (hx : x ∈ interior p)
    (hf : FacetOf f p) (hy : y ∈ intrinsicInterior ℝ f) :
    {v : V3 | ∃ t : ℝ, 0 < t ∧ v = t • y} ⊆ fchanged f := by
  sorry

/-- HOL polyhedron.hl :620-:656 `CONNECTED_HALF_LINE1`

HOL 原文：
```
!y:real^3. connected {v| ?t. &0< t /\ v=t%y}
```
（其内含 `let LEMMA` :621-:638，本批作为独立引理 `LEMMA_b4` 移植。）

编码说明：开射线 `{v | ∃ t > 0, v = t • y}`。

证明思路：分 `y = 0` 与 `y ≠ 0`。`y = 0` 时集合是 `{0}`
（`t • 0 = 0`，任意 `t > 0` 可达），用 `isConnected_singleton`；
`y ≠ 0` 时用 `LEMMA_b4` 改写为 `affGt {0} {y}`，再
`CONNECTED_HALF_LINE`。

候选已有引理：
- `LEMMA_b4`（本文件，HOL :621）
- `CONNECTED_HALF_LINE`（本文件，HOL :586）
- `isConnected_singleton`（Mathlib/Topology/Connected/Basic.lean:73）
- `zero_smul`（Mathlib） -/
theorem CONNECTED_HALF_LINE1 (y : V3) :
    IsConnected {v : V3 | ∃ t : ℝ, 0 < t ∧ v = t • y} := by
  sorry

/-- HOL polyhedron.hl :621-:638 `LEMMA`（CONNECTED_HALF_LINE1 的内含
`let`）——**改名说明**：HOL 在 polyhedron.hl 中两次使用名字 `LEMMA`
（:517 在批 3 的 `CONVEX_RELATIVE_INTERIOR` 内，归并行批 3 所有；
:621 在本批）。为避免重名冲突，本批的 :621 引理移植为 `LEMMA_b4`。

HOL 原文：
```
!x:real^3. ~(x= vec 0)==>aff_gt {vec 0} {x}= {v| ?t. &0< t /\ v=t%x}
```

编码说明：`vec 0` ↔ `(0 : V3)`；`aff_gt` ↔ `affGt`。

证明思路：对 `u ∈ affGt {0} {x}` 由 `Affsign` 展开得
`u = f x • x + f 0 • 0` 且 `f x > 0`（`t` 取 `f x`）；反向对
`u = t • x, t > 0` 取系数 `f 0 = 0, f x = t`。两端都是
`Set.ext` + 系数重排（`module`/`simp` 收口）。

候选已有引理：
- `affGt`（Kepler/Geom/Aff.lean:39）、`Affsign`（Aff.lean:32）
- `affGt_pair_iff`（Kepler/Geom/Aff.lean:82 的同族刻画，配对情形）
- `zero_smul`、`vadd_eq_zero`/`smul_eq_zero`（Mathlib） -/
theorem LEMMA_b4 {x : V3} (hx : x ≠ 0) :
    affGt {(0 : V3)} {x} = {v : V3 | ∃ t : ℝ, 0 < t ∧ v = t • x} := by
  sorry

/-- HOL polyhedron.hl :657-:661 `CONNECTED_COMPONENT_OF_SUBSET`

HOL 原文：
```
!s t x y. s SUBSET t /\ connected_component s x y ==> connected_component t x y
```

编码说明：`connected_component s x y` ↔ `x ∈ connectedComponentIn s y`
（Kepler/Text/PlanarityComponent.lean:31 的约定）。注意
PlanarityComponent.lean:30 曾按「Mathlib 已有」跳过本条
（= `connectedComponentIn_mono`）；按批 4 任务单仍在此命名移植。

证明思路：直接 `connectedComponentIn_mono y hst h`。

候选已有引理：
- `connectedComponentIn_mono`
  （Mathlib/Topology/Connected/Basic.lean:635，签名
  `(x : α) (h : F ⊆ G) : connectedComponentIn F x ⊆ connectedComponentIn G x`） -/
theorem CONNECTED_COMPONENT_OF_SUBSET {s t : Set V3} {x y : V3}
    (hst : s ⊆ t) (h : x ∈ connectedComponentIn s y) :
    x ∈ connectedComponentIn t y := by
  sorry

/-- HOL polyhedron.hl :662-:674 `CONNECTED_COMPONENT_TRANS`

HOL 原文：
```
!s x y z:real^N. connected_component s x y /\ connected_component s y z
==> connected_component s x z
```

编码说明：分量成员编码同上；HOL 的证明走 `t ∪ u` 连通并，Lean 侧
用分量相等更短：`y ∈ cc s z` 蕴含 `cc s y = cc s z`。

证明思路：`connectedComponentIn_eq h2` 得
`connectedComponentIn s y = connectedComponentIn s z`，沿 `h1` 改写即得。

候选已有引理：
- `connectedComponentIn_eq`
  （Mathlib/Topology/Connected/Basic.lean:585，签名
  `(h : y ∈ connectedComponentIn F x) : connectedComponentIn F y = connectedComponentIn F x`）
- `mem_connectedComponentIn`（Mathlib/Topology/Connected/Basic.lean:517） -/
theorem CONNECTED_COMPONENT_TRANS {s : Set V3} {x y z : V3}
    (h1 : x ∈ connectedComponentIn s y) (h2 : y ∈ connectedComponentIn s z) :
    x ∈ connectedComponentIn s z := by
  sorry

/-- HOL polyhedron.hl :675-:744 `CONNECTED_FCHANGED`（批 4 中心定理）

HOL 原文：
```
!p x f:(real^3->bool). bounded p /\ polyhedron p /\ x IN interior p /\
f facet_of p ==> connected (fchanged f)
```

编码说明：`fchanged`（:512）展开为正射线之并；`connected` ↔
`IsConnected`；HOL 经 `CONNECTED_IFF_CONNECTED_COMPONENT` 把连通性
化归为「任两点同分量」，再沿
`t•v1 — v1 — v1' — t'•v1'` 的分量链拼接。

证明思路：设 `u, w ∈ fchanged f`，写 `u = t • v1, w = t' • v1'`，
`v1, v1' ∈ intrinsicInterior ℝ f`（`t, t' > 0`）。四个子事实：
`v1, t•v1` 同在射线 `{v | ∃ s > 0, v = s • v1}` 上（后者 `s = t`，前者
`s = 1`），同 `v1'` 侧；射线连通（`CONNECTED_HALF_LINE1`）给出分量
成员，`CONNECTED_COMPONENT_OF_SUBSET` 搬进 `fchanged f`；
`CONNECTED_RELATIVE_INTERIOR_FACET` 给 `intrinsicInterior ℝ f` 连通 →
`v1, v1'` 在其中同分量，同样搬进 `fchanged f`；最后
`CONNECTED_COMPONENT_TRANS` 两次拼链 `t•v1 → v1 → v1' → t'•v1'`。

候选已有引理：
- `CONNECTED_HALF_LINE1`、`CONNECTED_RELATIVE_INTERIOR_FACET`、
  `AFF_GT_SUBSET_FCHANGED`、`RELATIVE_SUBSET_FCHANGE`、
  `CONNECTED_COMPONENT_OF_SUBSET`、`CONNECTED_COMPONENT_TRANS`
  （均为本文件前 9 条）
- `isConnected_connectedComponentIn_iff`
  （Mathlib/Topology/Connected/Basic.lean:545，= HOL
  `CONNECTED_IFF_CONNECTED_COMPONENT` 的分量形态）
- `mem_connectedComponentIn`（Mathlib/Topology/Connected/Basic.lean:517）
- `one_smul`、`zero_lt_one`、`smul_zero`（Mathlib） -/
theorem CONNECTED_FCHANGED {p f : Set V3} {x : V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (hx : x ∈ interior p)
    (hf : FacetOf f p) :
    IsConnected (fchanged f) := by
  sorry

end Kepler.Text
