/-
  Kepler/Text/LP/LpSemantics — LP 终端语义层 keystone 首件（LP W6-B #1）。

  两件：
  1. `fullySurrounded_of_surroundedNode`：fan 前提下逐点 surrounded ⇒ 全 dart
     surrounded（HOL `CONTRAVENING_IMP_FULLY_SURROUNDED` 的去 contravening 化
     核心步；dart 两支的 `d.1 ∈ V` 归属由 TameLp 已证 `dartOfFan_fst_mem`
     承载——孤立点支取 `.2.1`、边支经 `FAN_in_setOfEdge`）。
  2. `contraveningLpFan`：HOL `contravening_lp_fan`
     （`formal_lp/hypermap/ineqs/lp_ineqs_proofs-compiled.hl:385-400`）直译：
     `Contravening V → LpFan V (ESTD V)`，五合取逐项落地——
     FAN ← `ContraFan.contraveningFanTl`（Packing + ballAnnulus + V ≠ ∅，
     非空由 `Contravening` 的 ncard = 13/14/15 合取项排除空集）；
     FullySurrounded ← 件 1；2.52 距离 ← `ContraFan.mem_ESTD` + `two_h0`
     （dist < 2.52 ⇒ {v,w} ∈ ESTD V 与 `{v,w} ∉ ESTD V` 矛盾，HOL `IN_ESTD`
     归谬步）；ballAnnulus / Packing ← `Contravening` 对应合取项。

  `LpFan` 直接消费 `Kepler.Text.TameLp.LpFan`（HOL `lp_fan` 的逐合取镜像，
  不重定义 `lp_fan`）；`ESTD` 同理用 `Kepler.Text.TameLp.ESTD`（与
  `ContraFan.ESTD` 同体 defeq，`contraveningFanTl` / `mem_ESTD` 经默认
  透明度 unfolding 直通）。

  公理面：`fullySurrounded_of_surroundedNode` 仅标准三（propext /
  Classical.choice / Quot.sound）；`contraveningLpFan` = 标准三 + ContraFan
  在案骨架公理——全部经 `ContraFan.contraveningFanTl`（→ `CKQOWSA` →
  `ESTD_fan7` 的 fan7 相交性 → 深几何核 `LEMMA_4_POINTS_FINAL`，
  ContraFan.lean:613 在案骨架）继承；本文件零新增未证原子。
-/
import Kepler.Text.TameLp
import Kepler.Text.LP.LPSchema

namespace Kepler.Text.LP.LpSemantics

open Kepler.Geom
open Kepler.Text.Fan
open Kepler.Text.TameLp
open Classical

/-! ## 件 1：逐点 surrounded ⇒ 全 dart surrounded -/

/-- fan 前提下，`surroundedNode` 逐点成立即 `FullySurrounded`：
dart 的第一分量必在 `V` 中（`dartOfFan_fst_mem`，fan 的 `⋃₀ E ⊆ V` 两支
归属），再由该点的 surrounded 性质给出 `azimDart < π`。
（HOL `CONTRAVENING_IMP_FULLY_SURROUNDED` 的核心步。） -/
theorem fullySurrounded_of_surroundedNode {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hsurr : ∀ v ∈ V, surroundedNode V E v) :
    FullySurrounded V E := fun d hd =>
  hsurr d.1 (dartOfFan_fst_mem hfan hd) d hd rfl

/-! ## 件 2：`contravening_lp_fan` 直译 -/

/-- HOL `contravening_lp_fan`（`lp_ineqs_proofs-compiled.hl:385-400`）：
反例构型给出 LP 扇。五合取：FAN（`CONTRAVENING_FAN`，经 ContraFan 的
CKQOWSA 链）/ fully_surrounded（`CONTRAVENING_IMP_FULLY_SURROUNDED`）/
2.52 距离（`IN_ESTD` 归谬）/ ballAnnulus / Packing。 -/
theorem contraveningLpFan (V : Set V3) (hc : Contravening V) : LpFan V (ESTD V) := by
  have hne : V ≠ ∅ := by
    have hcard : V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15 := hc.2.2.2.2.1
    rintro rfl
    simp at hcard
  have hfan : FAN 0 V (ESTD V) := ContraFan.contraveningFanTl V hc.1 hc.2.1 hne
  refine ⟨hfan, fullySurrounded_of_surroundedNode hfan hc.2.2.2.2.2.1, ?_, hc.2.1, hc.1⟩
  intro v w hv hw hvw hnotE
  by_contra hcon
  push_neg at hcon
  have hmem : {v, w} ∈ ESTD V :=
    ContraFan.mem_ESTD.mpr ⟨v, w, rfl, hv, hw, hvw,
      by linarith [ContraFan.two_h0, hcon]⟩
  exact hnotE hmem

end Kepler.Text.LP.LpSemantics
