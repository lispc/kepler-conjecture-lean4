/-
LocalAuto7W22dJ: W22d-ii — `f_surr_localization_convex_local`（HOL `RNSYJXM.vhl:279-337`）
的 Lean 装配：`ConvexLocalFan (vPrime_p3 V FF) (ePrime_p3 E FF) FF`（`LocalAuto1.lean:174`）。

## 件表

| # | 件 | = HOL / 树内锚 |
|---|---|---|
| 1 | `p22dJ_wedgeSubsetWedgeGe`（private） | `Leaf_cell.WEDGE_SUBSET_WEDGE_GE`（唯一声明 PackingAuto18:8172，禁 import ⇒ 本地内联） |
| 2 | `p22dJ_vPrime_subset_wedgeInFanGe` | 六步 4–6 闭包链：`v_prime ⊆ wedge_in_fan_ge` |
| 3 | `p22dJ_convexLocalFan` | `f_surr_localization_convex_local`（p3 词面） |
| 4 | `p22dJ_convexLocalFan_p2` | W21 `hL` 槽的 p2 词面别名 |

## 槽（两条，别车道在证）

* `hclosed`：`IsClosed (wedgeGe u0 u1 u2 u3)`（非共线前提）—— HOL `CLOSED_WEDGE`
  （leaf_cell.hl:3663）的 W22d-i 真证件，落地后本文件一行代入（`closure_minimal` 第二参数）。
* `hsimple`：`H2.Simple` —— `fully_surrounded_simple_hypermap` 的 loc-simple 车道件。

## 词汇三层（目标 LA1 / 件 _p3 / noHcard _p2）

* 合取 1：`p22c2_f_surr_localization_cond_noHcard` 第一合取直投。
* 合取 2a：`azimInFan` → `_p3` → `azimDart`（`p22c_azimDart_eq_azimInFan`）→ 原扇
  `azimDart`（noHcard 第 3 合取）→ `< π`（`hfs`）。不用带 `hcard` 的 `p22d_slice_azimDart_lt_pi`。
* 合取 2b：E 侧闭包链给 `z ∈ wedgeGe 0 x.1 x.2 (σ_E)`，再用
  `azimInFan x E = azimInFan x (ePrime)`（noHcard 第 3 合取 + 双重 `_p3` 桥）换成
  `σ_{ePrime}` 的方位角，按 `wedgeInFanGe` 的 `if` 二分收口。**不需要** `_p2` 层。

零 `axiom`/`sorry`/`admit`/`native_decide`；不 import `PackingAuto18`；主仓零改动。
-/
import Kepler.Text.LocalAuto7W22c3b
import Kepler.Text.LocalAuto7W22dA
import Kepler.Text.LocalAuto7W22dE
import Kepler.Text.LocalAuto7W22dwedge

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-! ## 1. `WEDGE_SUBSET_WEDGE_GE` 本地内联（PackingAuto18 禁 import） -/

/-- HOL `Leaf_cell.WEDGE_SUBSET_WEDGE_GE`（PackingAuto18:8172 的证明体，逐字）。 -/
private theorem p22dJ_wedgeSubsetWedgeGe (u0 u1 u2 u3 : V3) :
    Kepler.Geom.wedge u0 u1 u2 u3 ⊆ wedgeGe u0 u1 u2 u3 := by
  intro y hy
  exact ⟨le_of_lt hy.2.1, le_of_lt hy.2.2⟩

/-! ## 2. 六步 4–6：`v_prime ⊆ wedge_in_fan_ge`（切片扇词面） -/

/-- **HOL `f_surr_localization_convex_local` 的 wedge 半**（`RNSYJXM.vhl:303-336`）：
`z ∈ v_prime` 取面内出边 `(z,w)`；`z ∈ closure(affGt {0} {z,w})`（`POINT_IN_CLOSURE_AFF_GT_1_2`）
⇒ `affGt ⊆ closure(dartsetLeadsIntoFan FF)`（锚 3）⇒ `⊆ wDartFan (σ_E)`（锚 2）⇒
`wDartFan = 开 wedge`（邻数 > 1）⇒ `closure ⊆ wedgeGe`（本地内联件 + `hclosed`）⇒ 换 `σ_{ePrime}`。 -/
theorem p22dJ_vPrime_subset_wedgeInFanGe {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {FF : Set (V3 × V3)} {x0 : V3 × V3} (hx : x0 ∈ dartsOfHyp_p3 E V)
    (hFF : FF = H1.face x0) (hfs : FullySurrounded V E)
    (hclosed : ∀ u0 u1 u2 u3 : V3, ¬ Collinear3 u0 u1 u2 → ¬ Collinear3 u0 u1 u3 →
      IsClosed (wedgeGe u0 u1 u2 u3))
    (hazimDart : ∀ y ∈ FF, azimDart V E y = azimDart (vPrime_p3 V FF) (ePrime_p3 E FF) y)
    {x : V3 × V3} (hxF : x ∈ FF) :
    vPrime_p3 V FF ⊆ wedgeInFanGe x (ePrime_p3 E FF) := by
  have hxH1 : x0 ∈ (↑H1.darts : Set (V3 × V3)) := h1.1.symm ▸ hx
  have hFFH1 : FF ⊆ (↑H1.darts : Set (V3 × V3)) := by
    rw [hFF]; exact p22c2_face_subset_darts H1 hxH1
  have hxFF : x0 ∈ FF := by rw [hFF]; exact H1.mem_face_self x0
  -- 面 ⊆ dart1OfFan（FullySurrounded 排自环）
  have hFFdart1 : ∀ d ∈ FF, d ∈ dart1OfFan V E :=
    fun d hd => p22c2_dartsOfHyp_subset hfs (h1.1 ▸ hFFH1 hd)
  have hx1 : x ∈ dart1OfFan V E := hFFdart1 x hxF
  have hxE : ({x.1, x.2} : Set V3) ∈ E := hx1
  have hxE2 : ({x.1, x.2} : Set V3) ∈ ePrime_p3 E FF := ⟨x.1, x.2, rfl, hxE, hxF⟩
  have hncard1 : 1 < (setOfEdge x.1 V E).ncard :=
    p22a_fs_ncard_gt1 hfan hfs x.1 (FAN_in_setOfEdge 0 V E x.1 x.2 hfan hxE).1
  have hfan' : FAN 0 (vPrime_p3 V FF) (ePrime_p3 E FF) :=
    IMP_FAN_V_PRIME_E_PRIME hfan ⟨H1, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, x0, hxH1, hFF⟩
  have hfan80 : fan80 0 V E := p22b_fully_surrounded_imp_fan80 hfan hfs
  have hconf : conformingFan 0 V E hfan :=
    p22a_fully_surrounded_imp_conforming hfan hfs hfan80
  -- `FF ∈ faceSet`（两实例标签：hypermapOfFan / hypermapOfFanTl）
  have hfaceOrb : H1.face x0 = orbitF_p3 (ffOfHyp_p3 0 V E) x0 := by
    show orbitMap H1.faceMap x0 = orbitF_p3 (ffOfHyp_p3 0 V E) x0
    unfold orbitMap orbitF_p3
    ext z
    simp only [Equiv.Perm.coe_pow, h1.2.2.2]
  have hFFface : FF = @Hypermap.face (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) x0 := by
    show FF = orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan)) x0
    rw [hFF, hfaceOrb, orbitMap_LA1faceMap_eq_orbitF hfan x0]
  have hx1' : x0 ∈ (@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan)) := by
    rw [← Finset.mem_coe, dartsLA1 0 V E hfan]
    exact hFFdart1 x0 hxFF
  have hFFmem : FF ∈ (@Hypermap.faceSet (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan)) := by
    rw [hFFface]
    exact (@Hypermap.mem_darts_iff_face_mem (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) x0).mp hx1'
  have hFFmemTl : FF ∈ (@Hypermap.faceSet (V3 × V3) dartDecEq2
      (hypermapOfFanTl V E hfan)) := by
    have hset : (@Hypermap.faceSet (V3 × V3) dartDecEq2 (hypermapOfFanTl V E hfan))
        = (@Hypermap.faceSet (V3 × V3) (fun a b => instDecidableEqProd a b)
            (hypermapOfFan 0 V E hfan)) := by
      unfold Hypermap.faceSet
      rw [dartsTl_eq, faceMapTl_eq]
    rwa [hset]
  have hnc2 : ¬ Collinear3 (0 : V3) x.1 x.2 := (p22d_dart1NotCollinear2 hfan hx1).1
  have hncσ : ¬ Collinear3 (0 : V3) x.1 (sigmaFan 0 V E x.1 x.2) :=
    (p22d_dart1NotCollinear2 hfan hx1).2
  have hwd : wDartFan 0 V E (0, x.1, x.2, sigmaFan 0 V E x.1 x.2) = Kepler.Geom.wedge 0 x.1 x.2 (sigmaFan 0 V E x.1 x.2) := by
    simp only [wDartFan, if_pos hncard1]
  have hcl : closure (Kepler.Geom.wedge 0 x.1 x.2 (sigmaFan 0 V E x.1 x.2)) ⊆
      wedgeGe 0 x.1 x.2 (sigmaFan 0 V E x.1 x.2) :=
    closure_minimal (p22dJ_wedgeSubsetWedgeGe 0 x.1 x.2 (sigmaFan 0 V E x.1 x.2))
      (hclosed 0 x.1 x.2 (sigmaFan 0 V E x.1 x.2) hnc2 hncσ)
  -- σ 换名：`azimInFan x E = azimInFan x (ePrime)` 的两侧展开形态
  have hbrE : 1 < (ee x.1 E).ncard := by
    rw [show ee x.1 E = EE_p2 x.1 E from rfl, EE_elim hfan x.1]; exact hncard1
  have hazimIn : azimInFan x E = azimInFan x (ePrime_p3 E FF) := by
    have h3 : azimInFan_p3 x E = azimInFan_p3 x (ePrime_p3 E FF) := by
      rw [← p22c_azimDart_eq_azimInFan hfan hxE, ← p22c_azimDart_eq_azimInFan hfan' hxE2]
      exact hazimDart x hxF
    rwa [azimInFan_eq_azimInFan_p3 hfan hx1, azimInFan_eq_azimInFan_p3 hfan' hxE2]
  have hσazim (hbr : 1 < (ee x.1 (ePrime_p3 E FF)).ncard) :
      azim 0 x.1 x.2 (sigmaFan 0 Set.univ (ePrime_p3 E FF) x.1 x.2)
        = azim 0 x.1 x.2 (sigmaFan 0 V E x.1 x.2) := by
    have h := hazimIn
    unfold azimInFan at h
    rw [if_pos hbrE, if_pos hbr] at h
    rw [← h, sigmaFan_univ_eq hfan.1]
  intro z hz
  obtain ⟨hzV, w, hzw⟩ := hz
  have hzwE : ({z, w} : Set V3) ∈ E := hFFdart1 (z, w) hzw
  have hwV : w ∈ V := (FAN_in_setOfEdge 0 V E z w hfan hzwE).2.1
  have hz0 : (0 : V3) ≠ z := fun he => hfan.2.2.2.1 (he ▸ hzV)
  have hw0 : (0 : V3) ≠ w := fun he => hfan.2.2.2.1 (he ▸ hwV)
  have hne : z ≠ w := edge_ne_of_fan hfan hzwE
  have hpc : z ∈ closure (affGt ({0} : Set V3) ({z, w} : Set V3)) := POINT_IN_CLOSURE_AFF_GT_1_2 0 z w hz0 hw0 hne
  have hA3 : affGt ({0} : Set V3) ({z, w} : Set V3) ⊆
      closure (dartsetLeadsIntoFan 0 V E FF) :=
    AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN_tl V E FF (z, w) hfan hconf.1 hfan80
      hFFmemTl hzw
  have hA2 : dartsetLeadsIntoFan 0 V E FF ⊆
      wDartFan 0 V E (0, x.1, x.2, sigmaFan 0 V E x.1 x.2) :=
    DARTSET_LEADS_INTO_SUBSET_WDART_FAN hfan hFFmem hxF hconf
  have hzwedge : z ∈ wedgeGe 0 x.1 x.2 (sigmaFan 0 V E x.1 x.2) := by
    have hwedgeSub : affGt ({0} : Set V3) ({z, w} : Set V3) ⊆
        closure (Kepler.Geom.wedge 0 x.1 x.2 (sigmaFan 0 V E x.1 x.2)) :=
      fun u hu => closure_mono (fun y hy => by rw [← hwd]; exact hA2 hy) (hA3 hu)
    have h1 : z ∈ closure (closure (Kepler.Geom.wedge 0 x.1 x.2 (sigmaFan 0 V E x.1 x.2))) :=
      closure_mono hwedgeSub hpc
    exact hcl (by rwa [closure_closure] at h1)
  unfold wedgeInFanGe
  by_cases hbr : 1 < (ee x.1 (ePrime_p3 E FF)).ncard
  · rw [if_pos hbr]
    exact ⟨hzwedge.1, by rw [hσazim hbr]; exact hzwedge.2⟩
  · rw [if_neg hbr]
    exact Set.mem_univ z

/-! ## 3. 装配：`ConvexLocalFan`（p3 词面） -/

/-- **HOL `f_surr_localization_convex_local`**（`RNSYJXM.vhl:279-337`）：
切片扇 `(v_prime V f, e_prime E f, f)` 凸（LA1 `ConvexLocalFan` 形）。
合取 1 = noHcard 第一合取；2a = `hfs` + noHcard 第 3 合取；2b = 件 2。 -/
theorem p22dJ_convexLocalFan {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x)
    {H2 : Hypermap (V3 × V3)}
    (h2 : IsHypOn_p10 0 (vPrime_p3 V FF) (ePrime_p3 E FF) H2)
    (hfs : FullySurrounded V E) (hsimple : H2.Simple)
    (hclosed : ∀ u0 u1 u2 u3 : V3, ¬ Collinear3 u0 u1 u2 → ¬ Collinear3 u0 u1 u3 →
      IsClosed (wedgeGe u0 u1 u2 u3)) :
    ConvexLocalFan (vPrime_p3 V FF) (ePrime_p3 E FF) FF := by
  have hno : dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF)
      = dart1OfFan (vPrime_p3 V FF) (ePrime_p3 E FF) := p22c2_noSlot_slice hfan h1 hx hFF hfs
  obtain ⟨hnc1, -, hazimDartEq, -, -⟩ :=
    p22c2_f_surr_localization_cond_noHcard hfan h1 hx hFF h2 hfs hsimple hno
  refine ⟨hnc1, ?_⟩
  intro y hy
  refine ⟨?_, ?_⟩
  · -- 合取 2a：`azimInFan y (ePrime) ≤ π`
    have hxH1 : x ∈ (↑H1.darts : Set (V3 × V3)) := h1.1.symm ▸ hx
    have hFFH1 : FF ⊆ (↑H1.darts : Set (V3 × V3)) := by
      rw [hFF]; exact p22c2_face_subset_darts H1 hxH1
    have hyE : ({y.1, y.2} : Set V3) ∈ E :=
      p22c2_dartsOfHyp_subset hfs (h1.1 ▸ hFFH1 hy)
    have hyE2 : ({y.1, y.2} : Set V3) ∈ ePrime_p3 E FF := ⟨y.1, y.2, rfl, hyE, hy⟩
    have hfan' : FAN 0 (vPrime_p3 V FF) (ePrime_p3 E FF) :=
      IMP_FAN_V_PRIME_E_PRIME hfan
        ⟨H1, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, x, hxH1, hFF⟩
    calc azimInFan y (ePrime_p3 E FF)
        = azimInFan_p3 y (ePrime_p3 E FF) := azimInFan_eq_azimInFan_p3 hfan' hyE2
      _ = azimDart (vPrime_p3 V FF) (ePrime_p3 E FF) y :=
          (p22c_azimDart_eq_azimInFan hfan' hyE2).symm
      _ = azimDart V E y := (hazimDartEq y hy).symm
      _ ≤ Real.pi := le_of_lt (hfs y (Or.inr hyE))
  · -- 合取 2b：`vPrime ⊆ wedgeInFanGe y (ePrime)`
    exact p22dJ_vPrime_subset_wedgeInFanGe hfan h1 hx hFF hfs hclosed hazimDartEq hy

/-- `p22dJ_convexLocalFan` 的 p2 词面别名（`vPrime_p2`/`ePrime_p2` 与 `_p3` 定义体逐字同）。 -/
theorem p22dJ_convexLocalFan_p2 {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x)
    {H2 : Hypermap (V3 × V3)}
    (h2 : IsHypOn_p10 0 (vPrime_p2 V FF) (ePrime_p2 E FF) H2)
    (hfs : FullySurrounded V E) (hsimple : H2.Simple)
    (hclosed : ∀ u0 u1 u2 u3 : V3, ¬ Collinear3 u0 u1 u2 → ¬ Collinear3 u0 u1 u3 →
      IsClosed (wedgeGe u0 u1 u2 u3)) :
    ConvexLocalFan (vPrime_p2 V FF) (ePrime_p2 E FF) FF :=
  p22dJ_convexLocalFan (V := V) (E := E) hfan h1 hx hFF h2 hfs hsimple hclosed

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22dJ_vPrime_subset_wedgeInFanGe
#print axioms Kepler.Text.p22dJ_convexLocalFan
#print axioms Kepler.Text.p22dJ_convexLocalFan_p2

end Kepler.Text
