/-
LocalAuto7W22dK: `f_surr_localization` 的**全消槽形**（`hcard`/`hsimple`/`hno` 全由已落件自动填）。

* `hcard`：`p22c3_hcard_bridge`（`p22c3_cardSetOfEdgeGt1ImpCardFaceGe3` 的桥，W22c-iii-a 第三路）。
* `hsimple`：`p22d_locSimple_hypermap`（HOL `localization_simple_hypermap`），
  其 `H1.Simple` 前件由 `p22dK_H1_simple` 供给：`FullySurrounded → conforming`（`p22a`+`p22b`）
  → `SRPRNPL`（原扇 `Simple`）→ 跨实例传输（`Simple_congr_inst`，四映射等式 + darts 等式）。
* `hno`：`p22c2_noSlot_slice`（`4232289f`）。

⇒ W22c-ii 条件形只剩 `hfs`（`FullySurrounded`，本就是 HOL 该节前提）。

实例注记：`hypermapOfFan` 结果烤定 `instDecidableEqProd`，本文件合成实例为 `dartDecEq3`；
本件对 `hypermapOfFan` 侧一律走 `@`-显式桥（`AzimBridge:187/360/386/379`），点投影只出现在
`dartDecEq3` 世界的 `H1` 上；两侧 `Simple` 由 `Simple_congr_inst`（`TameLp:232`）跨实例连接。
-/
import Kepler.Text.LocalAuto7W22dG
import Kepler.Text.LocalAuto7W22c3b
import Kepler.Text.LocalAuto7W22a
import Kepler.Text.LocalAuto7W22b
import Kepler.Text.LocalAuto7W22ciino
import Kepler.Text.ConformingAuto1
import Kepler.Text.AzimBridge

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- **原扇超映射的 `Simple`**：`FullySurrounded` + `FAN` 给 conforming（`p22a`+`p22b`），
`SRPRNPL` 给 `hypermapOfFan` 的 `Simple`，再经四条 `@`-显式映射 + darts 等式
（`Simple_congr_inst`）传到同 `(V,E)` 的 `H1`。 -/
theorem p22dK_H1_simple {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    (hfs : FullySurrounded V E) {H1 : Hypermap (V3 × V3)}
    (h1 : IsHypOn_p10 0 V E H1) : H1.Simple := by
  have hconf : conformingFan 0 V E hfan :=
    p22a_fully_surrounded_imp_conforming hfan hfs
      (p22b_fully_surrounded_imp_fan80 hfan hfs)
  have hs : @Hypermap.Simple (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := SRPRNPL hfan hconf
  have hno0 : dartsOfHyp_p3 E V = dart1OfFan V E :=
    hno_of_no_isolated (fun v hv => p22a_fs_has_edge hfs v hv)
  have hdartsSet :
      ((@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan 0 V E hfan)) : Set (V3 × V3)) =
      (↑H1.darts : Set (V3 × V3)) := by
    rw [dartsLA1 0 V E hfan, ← hno0, ← h1.1]
  have hd : @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) = H1.darts :=
    Finset.coe_injective hdartsSet
  have hnFun : (⇑(@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan))) = ⇑H1.nodeMap := by
    rw [← nnOfHyp_p3_eq_nodeMapLA1_fun hfan]
    exact h1.2.2.1.symm
  have hn : @Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) = H1.nodeMap :=
    Equiv.ext fun d => congrFun hnFun d
  have hfFun : (⇑(@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan))) = ⇑H1.faceMap := by
    rw [← ffOfHyp_p3_eq_faceMapLA1_fun hfan]
    exact h1.2.2.2.symm
  have hf : @Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) = H1.faceMap :=
    Equiv.ext fun d => congrFun hfFun d
  have heFun : (⇑(@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan))) = ⇑H1.edgeMap := by
    rw [← eeOfHyp_p3_eq_edgeMapLA1_fun hfan]
    exact h1.2.1.symm
  have he : @Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) = H1.edgeMap :=
    Equiv.ext fun d => congrFun heFun d
  exact (Simple_congr_inst hd he hn hf).mp hs

/-- **`f_surr_localization` 全消槽形**：只剩 `hfs`（HOL 该节前提）。 -/
theorem p22c2_f_surr_localization_cond_full {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x)
    {H2 : Hypermap (V3 × V3)}
    (h2 : IsHypOn_p10 0 (vPrime_p3 V FF) (ePrime_p3 E FF) H2)
    (hfs : FullySurrounded V E) :
    LocalFan (vPrime_p3 V FF) (ePrime_p3 E FF) FF ∧
    FF = H2.face x ∧
    (∀ y ∈ FF, azimDart V E y = azimDart (vPrime_p3 V FF) (ePrime_p3 E FF) y) ∧
    (∀ y ∈ FF, wedgeInFanGt_p2 y E = wedgeInFanGt_p2 y (ePrime_p3 E FF)) ∧
    (∀ y ∈ FF, wedgeInFanGe_p2 y E = wedgeInFanGe_p2 y (ePrime_p3 E FF)) := by
  have hcard : 2 < FF.ncard := p22c3_hcard_bridge hfan h1 hx hFF hfs
  have hsimple : H2.Simple :=
    p22d_locSimple_hypermap hfan h1 hx hFF h2 (le_of_lt hcard)
      (p22dK_H1_simple hfan hfs h1)
  exact p22c2_f_surr_localization_cond hfan h1 hx hFF h2 hfs hcard hsimple
    (p22c2_noSlot_slice hfan h1 hx hFF hfs)

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22dK_H1_simple
#print axioms Kepler.Text.p22c2_f_surr_localization_cond_full

end Kepler.Text
