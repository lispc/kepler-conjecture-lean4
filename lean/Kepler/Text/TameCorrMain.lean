/-
  Kepler.Text.TameCorrMain — `tame_correspondence_iso` 三波施工的 **W3 第十一波 b（主定理）**：
  HOL `WMLNYMD.hl:1498`（= `WMLNYMD.tame_correspondence_iso`）。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ import = `Kepler.Text.TameCorrIso2` + `Kepler.Text.TameCorrG9`
  │ （闭包零 `Kepler.Assembly` 本体）。环自检：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **与 Assembly 陈述的同形关系**（详见 `接线清单.md`）：
  Assembly `tameCorrespondenceIso (g H H') (hgg : GoodGraphV4 g)
    (ht : TamePlanarHypermap H) (hiso : HypermapIso H H')
    (hIs : IsHypermapOfList g.fgraph H') : tame g`
  —— 本文件用 Assembly-free 孪生：`TameCorrList.GoodGraphV4`、
  `TameLp.TamePlanarHypermap`、`Hypermap.Iso`、`TameLp.IsHypermapOfListTl`。

  **装配路线**（12 槽只消费 7–12）：
  `isHypermapOfListTl_eq_canonical`（典范性，W3-W10）把 `H'` rw 成
  `hypermapOfList g.fgraph hgg.1`；取 iso 见证 `f`/`HypIso`；
  `tame9a/10/11a_iso`（W3-W10）+ `tame11b/12o/13a_iso`（W3-W11a）迁六槽；
  `tameCorrespondence1`（W3-W10）收口到 `Graphs.tame g`。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrIso2
import Kepler.Text.TameCorrG9

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrMain

open Classical
open Kepler.Text (Hypermap)
open Kepler.Text.TameLp (hypermapOfList TamePlanarHypermap IsHypermapOfListTl)
open Kepler.Text.TameCorrList (GoodGraphV4)
open Kepler.Text.TameCorrIso (HypIso isHypermapOfListTl_eq_canonical tame9aIso tame10Iso tame11aIso)
open Kepler.Text.TameCorrIso2 (tame11bIso tame12oIso tame13aIso)
open Kepler.Text.TameCorrG9 (tameCorrespondence1)
open Kepler.Graphs (Graph tame)

/-- HOL `tame_correspondence_iso`（WMLNYMD.hl:1498）：
`good_graph_v4 g ∧ tame_planar_hypermap H ∧ iso H H' ∧
 IsHypermapOfList g.fgraph H' ⇒ tame g`。
类型用 Assembly-free 孪生（`GoodGraphV4` / `TamePlanarHypermap` /
`Hypermap.Iso` / `IsHypermapOfListTl`）；只消费 `TamePlanarHypermap` 的
第 7–12 槽（`Tame9a/10/11a/11b/12o/13a`），槽 1–6 保留不消费。 -/
theorem tameCorrespondenceIso {α : Type*} [DecidableEq α] (g : Graph)
    (H : Hypermap α) (H' : Hypermap (ℕ × ℕ))
    (hgg : GoodGraphV4 g) (ht : TamePlanarHypermap H)
    (hiso : H.Iso H') (hIs : IsHypermapOfListTl g.fgraph H') :
    tame g := by
  have hEq : H' = hypermapOfList g.fgraph hgg.1 :=
    isHypermapOfListTl_eq_canonical (hL := hgg.1) hIs
  rw [hEq] at hiso
  obtain ⟨f, hbij, hcomm⟩ := hiso
  have hiso' : HypIso f H (hypermapOfList g.fgraph hgg.1) := ⟨hbij, hcomm⟩
  have h9 := tame9aIso ht.2.2.2.2.2.2.1 hiso'
  have h10 := tame10Iso ht.2.2.2.2.2.2.2.1 hiso'
  have h11a := tame11aIso ht.2.2.2.2.2.2.2.2.1 hiso'
  have h11b := tame11bIso ht.2.2.2.2.2.2.2.2.2.1 hiso'
  have h12o := tame12oIso ht.2.2.2.2.2.2.2.2.2.2.1 hiso'
  have h13 := tame13aIso ht.2.2.2.2.2.2.2.2.2.2.2 hiso'
  exact tameCorrespondence1 hgg h9 h10 h11a h11b h12o h13

end Kepler.Text.TameCorrMain
