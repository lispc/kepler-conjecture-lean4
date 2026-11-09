/-
LocalAuto7W22dM: W21 `hL` 槽接线 — `p21_fully_surrounded_perimeter_bound`（W21:66-70）的
② 前提由 perimeter 根面机器直接供给，只剩 `hfs`。

* `p22dK_isHypOn_dart`：用公开词 `hypermap_toDart`（= private `fanHyp` 的定义体）给出
  `IsHypOn_p10 0 V E`；darts 槽需 `hno`（FAN 只有 `⋃₀ E ⊆ V`，不排除孤立点，
  故不能省略该前提——`FullySurrounded` 经 `p22a_fs_has_edge` 供给）。
* `p21_hL_of_fullySurrounded`：对 `d ∈ (hypermapOfFanTl V E hfan).darts` 取
  `FF := Tl.face d`、`H1 := toDart (hypermapOfFan 0 V E)`、
  `H2 := toDart (hypermapOfFan 0 (vPrime_p3 V FF) (ePrime_p3 E FF) hfan')`，
  由 `p22dJ_convexLocalFan_p2`（p2 词面）装配 `ConvexLocalFan`；
  `hclosed` = `p22d_closedWedge`，`hsimple` = `p22d_locSimple_hypermap` + `p22dK_H1_simple`。

实例格（本文件实测）：`hypermapOfFan` = `instDecidableEqProd`；`hypermapOfFanTl` =
`dartDecEq2`；`hypermap_toDart`/本文件合成 = `dartDecEq3`。Tl ↔ toDart 的 face/darts
转换对具体项是 `rfl`（两者都 unfold 到 `hypermapOfFan` 的 `instProd` 字段），
故 W21 槽形可逐字书写；一行接 W21 的判据已在探针中编译通过。
-/
import Kepler.Text.LocalAuto7W22dK
import Kepler.Text.LocalAuto7W22dJ
import Kepler.Text.LocalAuto7W22dI
import Kepler.Text.TameLp

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- **`hypermapOfFan`（重标到 `dartDecEq3`）满足 `IsHypOn_p10`**：
`darts` 用 `toDart_darts` + `dartsLA1` + `hno`；四映射用 `AzimBridge` 的
`@`-显式桥（`fanHyp` 定义体即 `hypermap_toDart (hypermapOfFan …)`，此处不命名它）。 -/
theorem p22dK_isHypOn_dart {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    (hno : dartsOfHyp_p3 E V = dart1OfFan V E) :
    IsHypOn_p10 0 V E (hypermap_toDart (hypermapOfFan 0 V E hfan)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((@Hypermap.darts (V3 × V3) dartDecEq3
      (hypermap_toDart (hypermapOfFan 0 V E hfan))) : Set (V3 × V3)) = dartsOfHyp_p3 E V
    rw [toDart_darts]
    exact (dartsLA1 0 V E hfan).trans hno.symm
  · show ((@Hypermap.edgeMap (V3 × V3) dartDecEq3
      (hypermap_toDart (hypermapOfFan 0 V E hfan))) : V3 × V3 → V3 × V3) = eeOfHyp_p3 0 V E
    exact (eeOfHyp_p3_eq_edgeMap_fun hfan).symm
  · show ((@Hypermap.nodeMap (V3 × V3) dartDecEq3
      (hypermap_toDart (hypermapOfFan 0 V E hfan))) : V3 × V3 → V3 × V3) = nnOfHyp_p3 0 V E
    exact (nnOfHyp_p3_eq_nodeMap_fun hfan).symm
  · show ((@Hypermap.faceMap (V3 × V3) dartDecEq3
      (hypermap_toDart (hypermapOfFan 0 V E hfan))) : V3 × V3 → V3 × V3) = ffOfHyp_p3 0 V E
    exact (ffOfHyp_p3_eq_faceMap_fun hfan).symm

/-- **W21 `hL` 槽**（`LocalAuto7W21.lean:66-70` 逐字）：`FullySurrounded` + `FAN`
直接给每个面切片的 `ConvexLocalFan`（p2 词面）。 -/
theorem p21_hL_of_fullySurrounded {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hfs : FullySurrounded V E) :
    ∀ d, d ∈ (hypermapOfFanTl V E hfan).darts →
      ConvexLocalFan (vPrime_p2 V ((hypermapOfFanTl V E hfan).face d))
        (ePrime_p2 E ((hypermapOfFanTl V E hfan).face d))
        ((hypermapOfFanTl V E hfan).face d) := by
  intro d hd
  let FF := (hypermapOfFanTl V E hfan).face d
  let H1 := hypermap_toDart (hypermapOfFan 0 V E hfan)
  have hno0 : dartsOfHyp_p3 E V = dart1OfFan V E :=
    hno_of_no_isolated (fun v hv => p22a_fs_has_edge hfs v hv)
  have h1 : IsHypOn_p10 0 V E H1 := p22dK_isHypOn_dart hfan hno0
  -- `d` 从 Tl 的 darts 进入 `dartsOfHyp_p3`
  have hd1 : d ∈ @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := by
    rw [← dartsTl_eq]
    exact hd
  have hd1set : d ∈ ((@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan)) : Set (V3 × V3)) := Finset.mem_coe.mpr hd1
  have hx : d ∈ dartsOfHyp_p3 E V := by
    rw [hno0]
    rw [dartsLA1 0 V E hfan] at hd1set
    exact hd1set
  -- Tl 与 `H1` 的 face 对具体项一致（两者 faceMap 均 `rfl` 到 `hypermapOfFan`）
  have hFF : FF = H1.face d := by
    show @Hypermap.face (V3 × V3) dartDecEq2 (hypermapOfFanTl V E hfan) d =
      @Hypermap.face (V3 × V3) dartDecEq3 H1 d
    rfl
  have hxH1 : d ∈ (↑H1.darts : Set (V3 × V3)) := h1.1.symm ▸ hx
  -- 切片扇与切片 `IsHypOn`（`hno` 由 `p22c2_noSlot_slice` 供给）
  have hfan' : FAN 0 (vPrime_p3 V FF) (ePrime_p3 E FF) :=
    IMP_FAN_V_PRIME_E_PRIME hfan
      ⟨H1, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, d, hxH1, hFF⟩
  have hno2 : dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF)
      = dart1OfFan (vPrime_p3 V FF) (ePrime_p3 E FF) :=
    p22c2_noSlot_slice hfan h1 hx hFF hfs
  have h2 : IsHypOn_p10 0 (vPrime_p3 V FF) (ePrime_p3 E FF)
      (hypermap_toDart (hypermapOfFan 0 (vPrime_p3 V FF) (ePrime_p3 E FF) hfan')) :=
    p22dK_isHypOn_dart hfan' hno2
  have hcard : 2 < FF.ncard := p22c3_hcard_bridge hfan h1 hx hFF hfs
  have hsimple :
      (hypermap_toDart (hypermapOfFan 0 (vPrime_p3 V FF) (ePrime_p3 E FF) hfan')).Simple :=
    p22d_locSimple_hypermap hfan h1 hx hFF h2 (le_of_lt hcard)
      (p22dK_H1_simple hfan hfs h1)
  exact p22dJ_convexLocalFan_p2 hfan h1 hx hFF h2 hfs hsimple p22d_closedWedge

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22dK_isHypOn_dart
#print axioms Kepler.Text.p21_hL_of_fullySurrounded

end Kepler.Text
