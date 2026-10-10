/-
PackingAuto23.lean — GRUTOTI capstone (skeleton-first port).

HOL source: scripts/packing/GRUTOTI.hl (8005 lines; module Grutoti,
Flyspeck book lemma GRUTOTI, Vu Khac Ky 2012). The HL file is ONE
`prove_by_refinement` block (GRUTOTI.hl:60-8001, 636 NEW_GOALs) with no
explicit sub-lemmas; this port re-expresses the proof's milestone goals as a
private lemma chain feeding the capstone.

Statement (GRUTOTI.hl:48-58): the dihedral angles of all Marchal cells along
a short edge {u0,u1} (hl < √2) in a saturated packing sum to 2π. Matches
`PackingAuto2.GRUTOTI1_concl` shape verbatim; once the giants below are
discharged, `GRUTOTI` discharges GRUTOTI1_concl by `exact GRUTOTI …`.

Proof skeleton (HL GRUTOTI.hl line ranges → private lemmas):
  62-160    barV V 1 [u0;u1]; GLTVHUM_lemma1 k-set; k=3 Voronoi/Rogers cover
            → grutoti_barV, grutoti_3mem (proved); grutoti_vor_cover (giant).
  161-2636  sliver core: p = midpoint circumcenter, relative-interior S1/S2,
            ball p 8 finiteness, C = ball u0 1 ∩ rcone_gt u0 u1 c,
            r = min 1 (min r1 r2), d = max c (max d1 d2), D ⊆ C, mcell cover
            along e (HL:2631) → grutoti_region (giant).
  2652-7958 per-cell wedge volume vol (X ∩ D) = vol D·dihX/(2π); k = 2,3 case
            analysis (mxi/ω3, AZIM_COMPL), k = 0,1,4 null-intersection
            → grutoti_cell_vol (giant).
  7228-7400 sum over edge cells of vol (X ∩ D) = vol D (measure union) and
            finiteness → grutoti_sum_volD (giant).
  7960-7966 pivot sum (vol·∩D) = sum (vol D·dihX/2π) → grutoti_pivot (giant);
            the linear step SUM_EQ/SUM_LMUL is proved (grutoti_setSum_mul_div).
  7967-8001 cancel with vol D > 0 (VOLUME_CONIC_CAP) → grutoti_volD_pos
            (giant); grutoti_cancel/grutoti_concl_arith (proved).

Encoding: HOL `real^3` ↔ `V3`; `vol` ↔ `volume.real`; `NULLSET` ↔ `nullSet`;
`conic_cap a b r d` ↔ `conicCap a b r d` (closedBall ∩ rconeGt); NOTE
PackingAuto15 has no built olean yet, so its `conicCap`, `RCONE_GT_SUBSET`
(proved) and `HL_LE_SQRT2_IMP_BARV_1` (sorried there too) are re-stated
privately here;
HOL set `sum` ↔ `setSum` (Auto2; index finiteness folded into
grutoti_sum_volD); `mcell_set V X` ↔ `X ∈ mcellSet V`. Sorried giants carry
NEEDS-precision notes; mechanical steps are proved.

2026-09-19 pass: `grutoti_hl_barV` SHIMMED to
`PackingAuto15.HL_LE_SQRT2_IMP_BARV_1` (olean landed; still `sorry`ed
upstream); `grutoti_vor_cover` FILLED (assembled from `grutoti_3mem` +
Auto12's `VORONOI_LIST_3_SINGLETON_EXPLICIT` shim + `CLOSEST_POINT_SING`);
`grutoti_volD_pos` re-documented (frozen statement is FALSE for the
degenerate `u1 = u0` — the empty conic cap; caller `GRUTOTI` has `hne`).

2026-09-28 GT-2 pass: `PackingAuto15.FINITE_EDGE_X2` (Auto15:672) and
`PackingAuto15.MCELL_SUBSET_BALL8_1` (Auto15:794) FILLED upstream (this
lane's PA15 arm) — the two PA15 dependencies named in `grutoti_sum_volD`'s
docstring are now real. The finite Pack2-measure bridge and the SUM_EQ
assembly are banked here as proved privates (`p23_measure_setSum_biUnion`,
`p23_setSum_congr`, `p23_setSum_of_zero`, `p23_dihX_of_nullSet`); the two
giant sorries `grutoti_sum_volD` / `grutoti_pivot` remain frozen with
detailed NEEDS notes (both need the region-block cover + §H per-cell
non-nullness, shared with grutoti_region/grutoti_cell_vol); `grutoti_volD_pos`
frozen-false premise now carries a STATEMENT-FIX proposal + patch (item 18).

2026-09-30 GT-4b pass: the region-block B5-B7 remainder closed (see the
GT-4b lane section before `grutoti_region`): the B5 cover kit (family
finiteness + rogers/mcell decomposition over C, AJRIPQN via PA17), the B6
P1-P4 extremal data (f1/f2 > 0, f3/f4 < 1 via smallestAngleLine + the
coplanarity killer), and the B7 assembly (r = min 1/2 (min r1 r2) — the 1/2
cap replaces HL's `min 1` because the Lean `grutotiConicCap` uses a CLOSED
ball — d = max c (max d1 d2), D ⊆ C, mcell cover). `grutoti_region` is
proved zero-sorry; the only upstream sorry debt is PA17's `AJRIPQN` and
PA12's `VORONOI_LIST_3_SINGLETON_EXPLICIT` shim (both recorded in their
docstrings since earlier waves).

2026-09-30 GT-4 pass: the region-block B1-B4 bridges banked as a 14-lemma
zero-sorry private chain (`p23Bis` + `p23_region_exists_delta` +
`p23_region_exists_c`, see the GT-4 lane section above): bisector S1
characterization/closedness/unboundedness, interface S closed/bounded
(saturation route, no BOUNDED_VORONOI_LIST needed), midpoint XYOFCGX
(strict + weak forms; Apollonius, no circumcenter API), critical radius δ
via the relative neighbourhood S' = S1 ∩ ball(p,d₀) ⊆ S (HL B2's a'/d₀
nearest-point selection — replaces HL's `S1 \ relative_interior S`, whose
closedness needs the unported AFF_DIM_VORONOI_LIST, and avoids the
intrinsicInterior bridge), and the cone threshold c ∈ (0,1) with
`rconeGt u0 u1 c ⊆ affGeAlt {u0} S` + `⊆ rconeGt u0 u1 (hl/√2)` (B3's
ray-hits-bisector argument + B4's max-assembly). `grutoti_region` itself
still `sorry` (B5-B7: rogers/mcell cover kit + P1-P4 minima + assembly,
HL:1144-2636) — see its updated NEEDS note.

2026-09-30 GT-3b/c pass: the `grutoti_cell_vol` arm kit banked as proved
privates — private copies of PA24's `coplanarAzimEq` +
`p24_coplanar_measure_null` (PA23 does not import PA24; provenance notes
inline), the affine-hull null workhorse `p23_coplanar_affineSpan_null`
(HL's 34× `NEGLIGIBLE_SUBSET (affine hull …) + COPLANAR_IMP_NEGLIGIBLE`
pattern), the azimuth-sheet killer `p23_cap_inter_azimLevel_null`, the
self-cone emptiness `p23_rconeGt_self_empty` (degenerate capsule), the §H
counting arm `p23_edge_cell_k_ge_two` (k = 0,1 impossible for edge cells),
and the junk-safety `p23_dihX_of_cellParamsD_ne`. `grutoti_cell_vol`'s
`u0 = u1` degenerate arm discharged inline; its frozen `sorry` now covers
only the non-degenerate wedge identities (k = 2,3 core + k = 4
non-coplanar), which need the region-block data — see its docstring for the
updated branch map and the missing edge-cell-hypothesis caveat.

2026-10-08 GT-3f pass (k = 2/3/4 三支组装收口, cell_vol 本体 sorry 清零): 三支
全部闭合——k = 2 双 rconeGe ∩ affGe 楠:`p23_cap_sub_rconeGe2`(hp 距离 + hw1
窄性)闭 D ⊆ 双锥,X ∩ D = L ∩ D 集合等式,wedge helper 闭体积式;dihX 分派
(cellParamsD ε-见证 .1 = 2 + elV 0/1 = u0/u1) 对接 `dihV`。k = 3/4 hull 支:
新私件 `p23_fan_cap_sub_hull4`(affGe 楠 ∩ cap ⊆ 四点 hull;t-系数两情形——
u0-系数负走远面平面径向排除、u1-系数负走 Cauchy–Schwarz 锥单调
`p23_angleMono`)+ `p23_hull_arm_eq` 组合器(hull ⊆ 楠
CONVEX_HULL_4_SUBSET_AFF_GE_2_2 + 楠∩D ⊆ hull + quartet 非退化 +
`p23_vol_D_inter_affGe`)一步给体积式;hw3/hw4 面/锥窄性按 SF 28 前提形状
消费。辅助件:`p23_affGe_mem_affineSpan2`(楠 ⊆ 四点仿射包)、
`p23_quartet_nondeg`(非零测 ⇒ 四点非共面 ⇒ 三条非退化)、`p23_elV0/1`。
region 侧供给缺口不变:GRUTOTI capstone 需 `grutoti_region` 导出
r/r1/r2/d/d1/d2 极端数据(B4/B6 段),见 docstring 尾注。

2026-10-08 GT-4 export pass (region B5-B7 极端数据导出波, cell_vol 消费端
SF 28 前提补齐): 新增零错私件 `p23_rconeGt_cos_lt`(rconeGt 成员读作严格
余弦下界)、`p23_u0_notIn_plane3/4`(P1/P2 面-平面 killer, 按
p23_u0_notIn_hull3/4 模式)、`p23_plane_dist_pos3/4`(远面平面距离 ε-下界;
平面闭性 = 有限维方向子模 + `isClosed_direction_iff`)、
`p23_smallestAngle_cos`(SMALLEST_ANGLE_LINE_PROPERTY 桥到 inner ℝ 形)与
伴随定理 `p23_region_data`(`grutoti_region` 同前提、强结论: 冻结界 +
mcell cover + hw1 `hl/√2 ≤ d` + hw3/hw4 面/锥窄性——P1/P2 经 r3/r4 面距离
族极小, P3/P4 经 f3/f4 极大, 冻结证明体用 ∃-见证即弃的极值在此保留)。
DEVIATION(均在冻结陈述 slack 内, D ⊆ C 与 cover 不变): `d = max c
(max (hl/√2) (max d1 d2))`(免 B4 包含反演)、`r = min (1/2) (min r3 r4)`
(面窄性须配所导出的 r)。GRUTOTI capstone 联动缺口随之缩小为:
AJRIPQN/measure-union 侧(sum_volD/pivot 两冻结 giant)。

2026-10-08 GT-3e pass (SF 项 28+29 应用 + 核填充, 用户批准): `grutoti_cell_vol`
签名补窄性/封角前提(SF 28:hp + hw1 + hw3 + hw4;SF 29:hjunk,陈述其余一字
未动),k = 0/1 计数臂与 ε-junk 逆序表角整支闭合(cellParams-witness 兼为
cellParamsD-witness,mcell0/mcell1 形状 + cap-不交性反 hn);GT-3e arm kit
banked:`p23_trunc1_of_init`、`p23_mem_affineSpan_of_affGe`、
`p23_mem_plane_of_azim_eq`(azim ∈ {0,π} 刚性)、`p23_affGt_sub_affGe`、
`p23_affGe_split`(AFF_GE_AFF_GT_DECOMP 集合内容)、`p23_affGt_pair_symm`、
`p23_cap_sub_rconeGe2`(HL §D 投影/勾股反锥论证)、`p23_vol_D_inter_affGe`
(楔体积合并式:wedge=affGt + 面零测 + AZIM_COMPL/dihv 补恒等式 +
volumeConicCapWedge,外测三明治免 Affsign 可测性);k ∈ {2,3,4} 楔恒等式
本体留三支结构化 sorry(docstring NEEDS 地图逐支列 banked 件)。

2026-09-30 GT-3d pass (cell_vol lane, post-SF-21): `grutoti_cell_vol`'s
branch map restructured with two more arms CLOSED inline — (A) null cells
(vacuous under `hn` by measure-mono into the null cell; `p23_dihX_of_nullSet`
stays banked for the pivot's junk terms) and (B) the §H junk arm with a valid `cellParamsD`-witness of
index 0 (`mcell0` lives outside `ball u0 √2`, the cap inside
`closedBall u0 r ⊆ ball u0 √2` by `r ≤ 1 < √2`, so `X ∩ D = ∅` contradicts
`hn`); junk-safety `p23_dihX_of_cellParamsD_ne` is banked there.
**SF-21 BUG (must-fix at next SF)**: `he` is INERT — the frozen binder order
puts `(he : {u0,u1} ∈ edgeX V X)` BEFORE `(X : Set V3)`, so with autoImplicit
the X inside `he`'s type is a fresh auto-bound implicit (X✝), not the binder:
`he` constrains a dead variable and `p23_edge_cell_k_ge_two` is NOT
consumable; fix = move `(X : Set V3)` ahead of `he`. Residual: THREE
`sorry`s with per-branch NEEDS notes in the docstring — (1) cellParamsD-index
1 (`mcell1`, needs the d-narrowness d ≥ hl [u0,u1]/√2), (2) index ∈ {2,3,4}
(the wedge identities: need d/r-narrowness `d ≥ d1/d2`, `r ≤ r1` that only
exists at `grutoti_region`'s witnesses — an SF adding narrowness hypotheses
or restating along those witnesses is the blocker), (3) the ε-junk case (no
valid witness: edge reversed in the param list — potential frozen-false
corner; SF proposal recorded). -/

import Kepler.Text.PackingAuto2
import Kepler.Text.ConicCapVolume
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto15
import Kepler.Text.PackingAuto17
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## The edge-cell family (HL GRUTOTI.hl:7227 `s`) -/

/-- HOL `conic_cap` (marchal3.hl; Auto15:109 `conicCap`, no olean yet —
private copy). -/
private def grutotiConicCap (v0 v1 : V3) (r a : ℝ) : Set V3 :=
  Metric.closedBall v0 r ∩ rconeGt v0 v1 a

/-- marchal3.hl `RCONE_GT_SUBSET` (Auto15:289, proved; private copy). -/
private theorem grutoti_rconeGt_subset (u0 u1 : V3) (a b : ℝ) (h : a ≤ b) :
    rconeGt u0 u1 b ⊆ rconeGt u0 u1 a := by
  intro x hx
  simp only [rconeGt, Set.mem_setOf_eq] at hx ⊢
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h (by positivity)) hx

/-- marchal3.hl:1054 `HL_LE_SQRT2_IMP_BARV_1` (Auto15:282). SHIM
(2026-09-19): the PackingAuto15 olean HAS landed in this checkout, so the
private copy discharges to `Kepler.Text.PackingAuto15.HL_LE_SQRT2_IMP_BARV_1`
(statement-identical; still `sorry`ed upstream in Auto15 — a documented
transitive shim; delete the copy at merge into Auto15's results). -/
private theorem grutoti_hl_barV (V : Set V3) (u0 u1 : V3) (hs : saturated V)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) : barV V 1 [u0, u1] :=
  HL_LE_SQRT2_IMP_BARV_1 V u0 u1 hs hp hu0 hu1 hne hhl

/-- HL GRUTOTI.hl:7227: `s = {X | mcell_set V X /\ edgeX V X e}` — the index
set of the final sums (identical to the GRUTOTI1_concl set by definition). -/
private def grutotiEdgeCells (V : Set V3) (e : Set V3) : Set (Set V3) :=
  {X | X ∈ mcellSet V ∧ e ∈ edgeX V X}

/-! ## Mechanical chain links (proved) -/

/-- HL GRUTOTI.hl:62-64: the edge is a `barV V 1` simplex
(`grutoti_hl_barV`, marchal3.hl:1054). -/
private theorem grutoti_barV (V : Set V3) (u0 u1 : V3) (hs : saturated V)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) : barV V 1 [u0, u1] :=
  grutoti_hl_barV V u0 u1 hs hp hu0 hu1 hne hhl

/-- HL GRUTOTI.hl:100-128 helper: `truncate_simplex 1 [u0;u1] = [u0;u1]`. -/
private theorem grutoti_trunc1 (u0 u1 : V3) :
    truncateSimplex 1 [u0, u1] = [u0, u1] := by
  have hex : ∃ vl : List V3, vl.length = 1 + 1 ∧ initialSublist vl [u0, u1] :=
    ⟨[u0, u1], rfl, ⟨[], by simp⟩⟩
  have hspec := Classical.epsilon_spec
    (p := fun vl : List V3 => vl.length = 1 + 1 ∧ initialSublist vl [u0, u1]) hex
  obtain ⟨yl, hyl⟩ := hspec.2
  have hlen : ([u0, u1] : List V3).length = 2 := rfl
  rw [hyl, List.length_append, hspec.1] at hlen
  have h3 : yl.length = 0 := by omega
  rcases yl with _ | ⟨a, t⟩
  · rw [List.append_nil] at hyl
    exact hyl.symm
  · simp at h3

/-- HL GRUTOTI.hl:76-84: `3` lies in the GLTVHUM_lemma1 index set, giving the
`k = 3` Rogers/Voronoi cover of `voronoiList V [u0, u1]`. -/
private theorem grutoti_3mem (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (hbar : barV V 1 [u0, u1]) :
    voronoiList V [u0, u1] =
      ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc 1 (3 - 1)} ∪
        voronoiList V vl) | vl ∈ {vl : List V3 |
        barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]}} := by
  have h := GLTVHUM_lemma1 V [u0, u1] 1 hp hs (by norm_num) hbar
  have hmem : (3 : ℕ) ∈ {k : ℕ | k ∈ (Finset.Icc 1 3 : Set ℕ) ∧
      voronoiList V [u0, u1] =
        ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc 1 (k - 1)} ∪
          voronoiList V vl) | vl ∈ {vl : List V3 |
          barV V k vl ∧ truncateSimplex 1 vl = [u0, u1]}}} := by
    rw [h]
    simp
  exact hmem.2

/-- HL GRUTOTI.hl:1487-1488 analogue: the cap is inside the radius-`r`
closed ball. -/
private theorem grutoti_cap_subset_closedBall (u0 u1 : V3) (r d : ℝ) :
    grutotiConicCap u0 u1 r d ⊆ Metric.closedBall u0 r := Set.inter_subset_left

/-- HL GRUTOTI.hl:7322-7324 analogue: the cap is inside the radius-1 open
ball once `r < 1`. -/
private theorem grutoti_cap_subset_ball (u0 u1 : V3) (r d : ℝ) (hr : r < 1) :
    grutotiConicCap u0 u1 r d ⊆ Metric.ball u0 1 :=
  Set.inter_subset_left.trans (Metric.closedBall_subset_ball hr)

/-- HL GRUTOTI.hl:2620-2629: `D ⊆ rcone_gt u0 u1 c` (with `c ≤ d`) via
`RCONE_GT_SUBSET`. -/
private theorem grutoti_cap_rcone_mono (u0 u1 : V3) (r c d : ℝ) (h : c ≤ d) :
    grutotiConicCap u0 u1 r d ⊆ rconeGt u0 u1 c :=
  Set.inter_subset_right.trans (grutoti_rconeGt_subset u0 u1 c d h)

/-- HL GRUTOTI.hl:7964-7968: SUM_EQ + SUM_LMUL — pulling a constant
coefficient out of a `setSum`. -/
private theorem grutoti_setSum_mul_div (T : Set (Set V3)) (c : ℝ) (f : Set V3 → ℝ)
    (hT : T.Finite) :
    setSum T (fun X => c * f X / (2 * Real.pi)) = c * setSum T f / (2 * Real.pi) := by
  rw [setSum, dif_pos hT, setSum, dif_pos hT]
  rw [← Finset.sum_div, ← Finset.mul_sum]

/-- HL GRUTOTI.hl:7971-8001: cancelling the positive factor `vol D`. -/
private theorem grutoti_cancel (S D : ℝ) (hD : 0 < D)
    (h : D * S / (2 * Real.pi) = D) : S = 2 * Real.pi := by
  have h2 : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  refine mul_left_cancel₀ (ne_of_gt hD) ?_
  rwa [div_eq_iff (ne_of_gt h2)] at h

/-- Final assembly (HL GRUTOTI.hl:7962-8001): from `sum = vol D` and the
wedge pivot, `sum dihX = 2π`. -/
private theorem grutoti_concl_arith (w S volD : ℝ) (hvol : 0 < volD)
    (hsum : w = volD) (hpivot : w = volD * S / (2 * Real.pi)) :
    S = 2 * Real.pi :=
  grutoti_cancel S volD hvol (by rw [← hpivot]; exact hsum)

/-! ## GT-2 lane private kit (proved 2026-09-28)

The finite Pack2-measure bridge and SUM_EQ assembly lemmas feeding
`grutoti_sum_volD` / `grutoti_pivot`. -/

/-- HOL `SUM_EQ` finite form: on a finite index set, pointwise equal functions
have equal `setSum`s. -/
private theorem p23_setSum_congr {α : Type*} {s : Set α} {f g : α → ℝ}
    (hs : s.Finite) (h : ∀ x ∈ s, f x = g x) : setSum s f = setSum s g := by
  rw [setSum, dif_pos hs, setSum, dif_pos hs]
  refine Finset.sum_congr rfl fun x hx => ?_
  exact h x ((Set.Finite.mem_toFinset hs).mp hx)

/-- HOL junk lemma: a function vanishing on a finite index set has zero
`setSum`. -/
private theorem p23_setSum_of_zero {α : Type*} {s : Set α} {f : α → ℝ}
    (hs : s.Finite) (h : ∀ x ∈ s, f x = 0) : setSum s f = 0 := by
  rw [setSum, dif_pos hs]
  exact Finset.sum_eq_zero fun x hx => h x ((Set.Finite.mem_toFinset hs).mp hx)

/-- HOL `dihX` junk branch: `dihX` vanishes on null cells (PA2 encoding, the
`nullSet X → 0` first branch of `PackingAuto2.dihX`). -/
private theorem p23_dihX_of_nullSet (V : Set V3) (X : Set V3) (p : V3 × V3)
    (h : nullSet X) : dihX V X p = 0 := if_pos h

/-- Finite `MEASURE_NEGLIGIBLE_UNIONS_IMAGE` (Pack2 bridge; grutoti-scout §2.2):
over a finite family of measurable, individually finite-volume sets with
pairwise-null intersections, the sum of the volumes equals the volume of the
union of the images. -/
private theorem p23_measure_setSum_biUnion {ι : Type*} {s : Set ι} {f : ι → Set V3}
    (hs : s.Finite) (hmeas : ∀ i ∈ s, MeasurableSet (f i))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → volume (f i ∩ f j) = 0)
    (hne : ∀ i ∈ s, volume (f i) ≠ ⊤) :
    setSum s (fun i => volume.real (f i)) = volume.real (⋃₀ (f '' s)) := by
  classical
  have hbU : (⋃ a ∈ s, f a) = ⋃ a ∈ hs.toFinset, f a := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hfx⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨a, (Set.Finite.mem_toFinset hs).mpr ha, hfx⟩
    · intro hx
      obtain ⟨a, ha, hfx⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨a, (Set.Finite.mem_toFinset hs).mp ha, hfx⟩
  have hd : Set.Pairwise (↑hs.toFinset) (Function.onFun (AEDisjoint volume) f) := by
    intro i hi j hj hij
    show volume (f i ∩ f j) = 0
    exact hpair i ((Set.Finite.mem_toFinset hs).mp hi) j
      ((Set.Finite.mem_toFinset hs).mp hj) hij
  have hm : ∀ b ∈ hs.toFinset, NullMeasurableSet (f b) volume := fun b hb =>
    (hmeas b ((Set.Finite.mem_toFinset hs).mp hb)).nullMeasurableSet
  rw [setSum, dif_pos hs, Set.sUnion_image, hbU]
  show (∑ w ∈ hs.toFinset, (volume (f w)).toReal)
      = (volume (⋃ a ∈ hs.toFinset, f a)).toReal
  rw [MeasureTheory.measure_biUnion_finset₀ hd hm]
  rw [ENNReal.toReal_sum fun i hi => hne i ((Set.Finite.mem_toFinset hs).mp hi)]

/-! ## GT-3 lane private kit (2026-09-30)

The `grutoti_cell_vol`/`grutoti_pivot` arm kit: private copies of PA24's
`coplanarAzimEq` + `p24_coplanar_measure_null` (PA23 does not import PA24 —
ccv_-convention private copies, provenance notes inline) plus the
null-intersection/counting combos that close the `k = 0,1` arms and the
degenerate branches of the per-cell analysis (HL §E/§H junk arms). -/

/-! ### PA24 copies (bodies verbatim modulo the `p23_` renaming; all proved
upstream in PackingAuto24.lean, 2026-09-19/30) -/


/-! ### The azim witness/affine-span kit (2026-09-19 fill, proved) -/

private theorem p23_exists_azim_point (v0 v1 w1 : V3) (a : ℝ)
    (hv01 : v0 ≠ v1) (hcw : ¬ Collinear3 v0 v1 w1)
    (ha0 : 0 < a) (ha2 : a < 2 * Real.pi) :
    ∃ f : V3, ¬ Collinear3 v0 v1 f ∧ azim v0 v1 w1 f = a := by
  have hwv : v1 ≠ v0 := Ne.symm hv01
  obtain ⟨e1, e2, e3, hon, halign⟩ :=
    exists_on3_eq_smul (v1 - v0) (sub_ne_zero.mpr hwv)
  have hax : (v1 - v0 : V3) = dist v1 v0 • e3 := by rw [dist_eq_norm]; exact halign
  obtain ⟨hp1, -⟩ := axis_perp hax hon
  have hp1' : (e3 : V3) ⬝ᵥ e1 = 0 := by
    rw [show ((e3 : V3)) ⬝ᵥ (e1 : V3) = (e1 : V3) ⬝ᵥ (e3 : V3) from dotProduct_comm _ _]
    exact hon.2.2.2.2.1
  have hw2nc : ¬ Collinear3 v0 v1 (v0 + e1) := by
    intro hcol
    obtain ⟨c, hc⟩ := (collinear3_iff_smul hwv).mp hcol
    have hsimp : ((v0 + e1 : V3) - v0) = e1 := by simp
    rw [hsimp, hax, smul_smul] at hc
    have hdot := congrArg (fun x : V3 => x ⬝ᵥ e1) hc
    rw [show (((c * dist v1 v0 : ℝ)) • (e3 : V3)) ⬝ᵥ e1
        = c * dist v1 v0 * ((e3 : V3) ⬝ᵥ e1) from by
      rw [← inner_eq_dot, ← inner_eq_dot, real_inner_smul_left], hp1', mul_zero] at hdot
    rw [hon.1] at hdot
    exact absurd hdot (by norm_num)
  obtain ⟨ψ, r1, r2, hr1, hr2, hzw1, -⟩ := azim_frame_spec hcw hw2nc hon hax hwv
  set f : V3 := v0 + (r1 * Real.cos (ψ + a)) • e1 + (r1 * Real.sin (ψ + a)) • e2 with hf
  have hsub : (f : V3) - v0
      = (r1 * Real.cos (ψ + a)) • e1 + (r1 * Real.sin (ψ + a)) • e2 + (0:ℝ) • (v1 - v0) := by
    rw [hf]; module
  have hzF : zOf e1 e2 (f - v0) = (r1 : ℂ) * Complex.exp (((ψ + a : ℝ)) * Complex.I) :=
    zOf_of_rep hon hax hsub
  have hnz : zOf e1 e2 (f - v0) ≠ 0 := by
    rw [hzF]
    exact mul_ne_zero (by exact_mod_cast hr1.ne') (Complex.exp_ne_zero _)
  have hfnc : ¬ Collinear3 v0 v1 f :=
    (zOf_ne_zero_iff hon hax hwv f).mp hnz
  refine ⟨f, hfnc, ?_⟩
  have hspec : AzimSpec v0 v1 w1 f (azim v0 v1 w1 f) := by
    unfold azim
    rw [if_neg (by rintro (h | h); exacts [hcw h, hfnc h])]
    exact Classical.epsilon_spec (azimSpec_exists hcw hfnc)
  unfold AzimSpec at hspec
  obtain ⟨-, -, h1', h2', hframes⟩ := hspec
  obtain ⟨ψ', r1', r2', hrep1, hrep2, hr1', hr2'⟩ := hframes e1 e2 e3 hon hax hwv
  have hz1 : zOf e1 e2 (w1 - v0) = (r1' : ℂ) * Complex.exp ((ψ' : ℝ) * Complex.I) :=
    zOf_of_rep hon hax hrep1
  have hz2 : zOf e1 e2 (f - v0) = (r2' : ℂ) * Complex.exp
      (((ψ' + azim v0 v1 w1 f : ℝ)) * Complex.I) :=
    zOf_of_rep hon hax hrep2
  have hn1 : ‖zOf e1 e2 (w1 - v0)‖ = r1 := by
    rw [hzw1, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr1, exp_unit_norm, mul_one]
  have hn1' : ‖zOf e1 e2 (w1 - v0)‖ = r1' := by
    rw [hz1, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr1', exp_unit_norm, mul_one]
  have hn2 : ‖zOf e1 e2 (f - v0)‖ = r1 := by
    rw [hzF, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr1, exp_unit_norm, mul_one]
  have hn2' : ‖zOf e1 e2 (f - v0)‖ = r2' := by
    rw [hz2, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr2', exp_unit_norm, mul_one]
  have hr1eq : r1' = r1 := hn1'.symm.trans hn1
  have hr2eq : r2' = r1 := hn2'.symm.trans hn2
  rw [hr1eq] at hz1
  rw [hr2eq] at hz2
  have hu1 : Complex.exp ((ψ' : ℝ) * Complex.I) = Complex.exp ((ψ : ℝ) * Complex.I) := by
    have hkey : (r1 : ℂ) * Complex.exp ((ψ' : ℝ) * Complex.I)
        = (r1 : ℂ) * Complex.exp ((ψ : ℝ) * Complex.I) := hz1.symm.trans hzw1
    exact mul_left_cancel₀ (by exact_mod_cast hr1.ne') hkey
  have hunits : Complex.exp ((azim v0 v1 w1 f : ℝ) * Complex.I)
      = Complex.exp ((a : ℝ) * Complex.I) := by
    have hkey : (r1 : ℂ) * Complex.exp (((ψ' + azim v0 v1 w1 f : ℝ)) * Complex.I)
        = (r1 : ℂ) * Complex.exp (((ψ + a : ℝ)) * Complex.I) := hz2.symm.trans hzF
    rw [exp_add_I, exp_add_I, hu1] at hkey
    have h1 := mul_left_cancel₀ (a := ((r1 : ℂ))) (by exact_mod_cast hr1.ne') hkey
    exact mul_left_cancel₀ (a := Complex.exp ((ψ : ℝ) * Complex.I))
      (Complex.exp_ne_zero _) h1
  exact angle_eq_of_exp_eq (azim_nonneg v0 v1 w1 f) (azim_lt_two_pi v0 v1 w1 f)
    ha0.le ha2 hunits


private theorem p23_mem_affineSpan_triple (v0 v1 w z : V3) (c₂ c₃ : ℝ)
    (hz : z = v0 + c₂ • (v1 - v0) + c₃ • (w - v0)) :
    z ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)) := by
  have h0 : v0 ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)) := mem_affineSpan (k := ℝ) (by simp)
  have h1 : v1 ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)) := mem_affineSpan (k := ℝ) (by simp)
  have h2 : w ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)) := mem_affineSpan (k := ℝ) (by simp)
  have d1 : (v1 - v0 : V3) ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction h1 h0
  have d2 : (w - v0 : V3) ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction h2 h0
  have dsum : c₂ • (v1 - v0) + c₃ • (w - v0) ∈
      (affineSpan ℝ ({v0, v1, w} : Set V3)).direction :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ d1) (Submodule.smul_mem _ _ d2)
  have hv := AffineSubspace.vadd_mem_of_mem_direction dsum h0
  rw [show ((c₂ • (v1 - v0) + c₃ • (w - v0)) +ᵥ v0)
    = v0 + (c₂ • (v1 - v0) + c₃ • (w - v0))
    from (vadd_eq_add _ _).trans (add_comm _ _)] at hv
  rw [hz, add_assoc]
  exact hv

/-- COPLANAR_IMP_NEGLIGIBLE (HOL `COPLANAR_IMP_NEGLIGIBLE` content, in the
root-`Coplanar` form `Module.rank ℝ (vectorSpan ℝ S) ≤ 2` that PA24's frozen
`Coplanar ℝ _` statements elaborate to): anything inside a coplanar set is
Lebesgue-null. The coplanar set lies in a proper affine subspace, null by
Mathlib `Measure.addHaar_affineSubspace`; outer-measure monotonicity (`measure_mono_null`)
needs no measurability of the inner set. -/
private theorem p23_coplanar_measure_null {T S : Set V3} (hS : Coplanar ℝ S)
    (hT : T ⊆ S) : volume T = 0 := by
  have hfd : FiniteDimensional ℝ (vectorSpan ℝ S) := hS.finiteDimensional_vectorSpan
  have hfin2 : Module.finrank ℝ (vectorSpan ℝ S) ≤ 2 :=
    (coplanar_iff_finrank_le_two (k := ℝ)).mp hS
  have hvs : (vectorSpan ℝ S : Submodule ℝ V3) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hfin2
    have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    rw [h3] at hfin2
    norm_num at hfin2
  have htop_aff : (affineSpan ℝ S : AffineSubspace ℝ V3) ≠ ⊤ := fun hE =>
    hvs (AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ V3 V3 hE)
  exact measure_mono_null (hT.trans (subset_affineSpan ℝ S))
    (Measure.addHaar_affineSubspace volume _ htop_aff)

/-- The affine span of a triple, as a set, is coplanar in the root-`Coplanar`
sense (Mathlib `coplanar_triple` transported along `direction_affineSpan`). -/
private theorem p23_coplanar_affineSpan_triple (u v w : V3) :
    Coplanar ℝ ((affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) := by
  have h := _root_.coplanar_triple (k := ℝ) u v w
  show Module.rank ℝ ↥((affineSpan ℝ ({u, v, w} : Set V3)).direction) ≤ 2
  rw [direction_affineSpan]
  exact h

/-- HOL `COPLANAR_AZIM_EQ` (REUHADY.hl:121). FILLED (2026-09-30): the two
main ingredients proved above — `p23_exists_azim_point` (the frame/polar
witness `f` off the axis with `azim v0 v1 w1 f = a`) and
`p23_mem_affineSpan_triple` (affineSpan-triple membership) — splice into the
documented case tree. (1) `a ∉ [0, 2π)` is vacuous via `azim_nonneg` /
`azim_lt_two_pi`; (2) `a = 0` needs `¬Collinear3 v0 v1 w1` (from `h`), then
the zero sheet lies in `affineSpan ℝ {v0,v1,w1}` (`collinear3_iff_smul` on the
axis, `azim_eq_zero_iff_alt` + `affGt_pair_iff` off it); (3) `0 < a < 2π`:
`p23_exists_azim_point` gives the witness `f`, and `azim_eq_azim_iff` +
`affGt_pair_iff` put every `z` of the level set into `affineSpan ℝ {v0,v1,f}`;
(4) coplanarity is read off via `p23_coplanar_affineSpan_triple` +
`_root_.Coplanar.subset`. NOTE the Geom-vs-root `Coplanar` split: this frozen
statement is Mathlib's root `Coplanar` (two explicit arguments, rank-of-
vectorSpan ≤ 2), NOT `Kepler.Geom.Coplanar` (the affineSpan-triple
existential, one argument) — resolution is by arity. -/
private theorem p23_coplanarAzimEq (v0 v1 w1 : V3) (a : ℝ)
    (h : Collinear3 v0 v1 w1 → ¬(a = 0)) :
    Coplanar ℝ {z | azim v0 v1 w1 z = a} := by
  by_cases han : a < 0
  · -- a < 0: the level set is empty
    refine _root_.Coplanar.subset (fun z hz => ?_)
      (_root_.coplanar_empty (k := ℝ) (P := V3))
    have h1 := azim_nonneg v0 v1 w1 z
    rw [hz] at h1
    exact absurd h1 (not_le.mpr han)
  · by_cases ha2' : 2 * Real.pi ≤ a
    · -- a ≥ 2π: the level set is empty
      refine _root_.Coplanar.subset (fun z hz => ?_)
        (_root_.coplanar_empty (k := ℝ) (P := V3))
      have h1 := azim_lt_two_pi v0 v1 w1 z
      rw [hz] at h1
      exact absurd h1 (not_lt.mpr ha2')
    · rcases eq_or_lt_of_le (le_of_not_gt han) with ha0 | hapos
      · -- a = 0: the zero sheet lies in the plane affineSpan {v0, v1, w1}
        rw [← ha0] at h ⊢
        rcases eq_or_ne v0 v1 with hv | hv01
        · exact absurd rfl (h (by rw [hv]; exact collinear3_of_eq rfl))
        · have hnc1 : ¬ Collinear3 v0 v1 w1 := fun hc => (h hc) rfl
          refine _root_.Coplanar.subset (fun z hz => ?_)
            (p23_coplanar_affineSpan_triple v0 v1 w1)
          by_cases hcz : Collinear3 v0 v1 z
          · obtain ⟨cc, hczv⟩ := (collinear3_iff_smul (Ne.symm hv01)).mp hcz
            exact p23_mem_affineSpan_triple v0 v1 w1 z cc 0 (by
              rw [show z = v0 + (z - v0) from by abel, hczv]; module)
          · obtain ⟨c, hcpos, t, hdec⟩ :=
              (affGt_pair_iff (v0 := v0) (v1 := v1) (x := w1) (y := z) hv01
                (fun he => hnc1 (collinear3_pair_left he))
                (fun he => hnc1 (collinear3_pair_right he))).mp
              ((azim_eq_zero_iff_alt hnc1 hcz).mp hz)
            exact p23_mem_affineSpan_triple v0 v1 w1 z t c (by
              rw [show z = v0 + (z - v0) from by abel, hdec]; module)
      · -- 0 < a < 2π
        rcases Classical.em (Collinear3 v0 v1 w1) with hc1 | hnc1
        · -- w1 on the axis: every azimuth vanishes, the level set is empty
          refine _root_.Coplanar.subset (fun z hz => ?_)
            (_root_.coplanar_empty (k := ℝ) (P := V3))
          have h0 : azim v0 v1 w1 z = 0 := by
            rw [azim, if_pos (Or.inl hc1)]
          simp only [Set.mem_setOf_eq] at hz
          rw [h0] at hz
          exact (h hc1) hz.symm
        · rcases eq_or_ne v0 v1 with hv | hv01
          · exact absurd (by rw [hv]; exact collinear3_of_eq rfl) hnc1
          · obtain ⟨f, hfnc, hfaz⟩ := p23_exists_azim_point v0 v1 w1 a hv01 hnc1
              hapos (lt_of_not_ge ha2')
            refine _root_.Coplanar.subset (fun z hz => ?_)
              (p23_coplanar_affineSpan_triple v0 v1 f)
            by_cases hcz : Collinear3 v0 v1 z
            · have h0 : azim v0 v1 w1 z = 0 := by
                rw [azim, if_pos (Or.inr hcz)]
              simp only [Set.mem_setOf_eq] at hz
              rw [h0] at hz
              exact absurd hz.symm (by linarith)
            · have hmem := (azim_eq_azim_iff hnc1 hfnc hcz).mp (hfaz.trans hz.symm)
              obtain ⟨c, hcpos, t, hdec⟩ :=
                (affGt_pair_iff (v0 := v0) (v1 := v1) (x := f) (y := z) hv01
                  (fun he => hfnc (collinear3_pair_left he))
                  (fun he => hfnc (collinear3_pair_right he))).mp hmem
              exact p23_mem_affineSpan_triple v0 v1 f z t c (by
                rw [show z = v0 + (z - v0) from by abel, hdec]; module)

/-! ### New combos: the `grutoti_cell_vol` arm-closers (2026-09-30) -/

/-- COPLANAR_AFFINE_HULL_COPLANAR + NEGLIGIBLE_SUBSET in one piece: a set
inside the affine hull of a coplanar set is Lebesgue-null (the HL §E/§H
`NEGLIGIBLE_SUBSET (affine hull …) + COPLANAR_IMP_NEGLIGIBLE` workhorse,
34 uses). Adapted from `p24_coplanar_measure_null`'s proof. -/
private theorem p23_coplanar_affineSpan_null {T S : Set V3} (hS : Coplanar ℝ S)
    (hT : T ⊆ (affineSpan ℝ S : Set V3)) : volume T = 0 := by
  have hfd : FiniteDimensional ℝ (vectorSpan ℝ S) := hS.finiteDimensional_vectorSpan
  have hfin2 : Module.finrank ℝ (vectorSpan ℝ S) ≤ 2 :=
    (coplanar_iff_finrank_le_two (k := ℝ)).mp hS
  have hvs : (vectorSpan ℝ S : Submodule ℝ V3) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hfin2
    have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    rw [h3] at hfin2
    norm_num at hfin2
  have htop_aff : (affineSpan ℝ S : AffineSubspace ℝ V3) ≠ ⊤ := fun hE =>
    hvs (AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ V3 V3 hE)
  exact measure_mono_null hT (Measure.addHaar_affineSubspace volume _ htop_aff)

/-- The degenerate-branch killer combo: the cap's intersection with any
azimuth level sheet is null (`p23_coplanarAzimEq` + `p23_coplanar_measure_null`;
consumes the PA24 ammo in one line, as HL's COPLANAR_IMP_NEGLIGIBLE
applications on `conic_cap ∩ {azim = …}` sheets do). -/
private theorem p23_cap_inter_azimLevel_null (u0 u1 w : V3) (r a θ : ℝ)
    (h : Collinear3 u0 u1 w → ¬(θ = 0)) :
    volume (grutotiConicCap u0 u1 r a ∩ {z : V3 | azim u0 u1 w z = θ}) = 0 :=
  p23_coplanar_measure_null (p23_coplanarAzimEq u0 u1 w θ h) Set.inter_subset_right

/-- The self-cone is empty for ANY parameter (`rconeGt u u a = ∅`): the
dot product with the zero vector vanishes, and so does `dist x u * dist u u * a`.
Feeds the degenerate-capsule arm of `grutoti_cell_vol` (`u0 = u1` forces
`D = ∅`). -/
private theorem p23_rconeGt_self_empty (u : V3) (a : ℝ) :
    rconeGt u u a = ∅ := by
  ext x
  simp only [rconeGt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  rw [sub_self, dotProduct_zero, dist_self] at hx
  simp at hx

/-- The degenerate capsule (`u0 = u1`) is empty. -/
private theorem p23_grutotiConicCap_self_empty (u : V3) (r a : ℝ) :
    grutotiConicCap u u r a = ∅ := by
  rw [grutotiConicCap, p23_rconeGt_self_empty u a, Set.inter_empty]

/-- `truncateSimplex` ε-选取属性 (PA2 私件 `p2g_trunc_init_len` 的链复制:
PA23 需要, PA2 未公开). -/
private theorem p23_trunc_init_len (k : ℕ) (zl : List V3) (h : k + 1 ≤ zl.length) :
    initialSublist (truncateSimplex k zl) zl ∧ (truncateSimplex k zl).length = k + 1 := by
  have heps := @Classical.epsilon_spec _
    (fun vl : List V3 => vl.length = k + 1 ∧ initialSublist vl zl)
    ⟨zl.take (k + 1), List.length_take_of_le (by omega),
      ⟨zl.drop (k + 1), (List.take_append_drop (k + 1) zl).symm⟩⟩
  exact ⟨heps.2, heps.1⟩

/-- HL §H arm (a) (GRUTOTI.hl:7536-7556): an edge cell carrying two DISTINCT
edge points has `cellParams`-`k ≥ 2` — `k ≤ 1` gives `VX V X` of card ≤ 1
(list truncation), too small for `{u0, u1}`. Kills the `k = 0,1` arms of
`grutoti_cell_vol`/`grutoti_pivot` inside the edge-cell context. -/
private theorem p23_edge_cell_k_ge_two (V : Set V3) (X : Set V3) (u0 u1 : V3)
    (hm : X ∈ mcellSet V) (hu0 : u0 ∈ VX V X) (hu1 : u1 ∈ VX V X) (hne : u0 ≠ u1) :
    2 ≤ (cellParams V X).1 := by
  obtain ⟨i, ul, hX, hbar⟩ := Set.mem_setOf_eq.mp hm
  have hX4 : X = mcell (min i 4) V ul := by
    rcases Nat.lt_or_ge i 4 with hlt | hle
    · rw [hX, min_eq_left (le_of_lt hlt)]
    · rw [hX, min_eq_right hle, (MCELL_EXPLICIT i V ul).2.2.2.2 hle,
        (MCELL_EXPLICIT 4 V ul).2.2.2.2 (Nat.le_refl 4)]
  have hwit : (cellParams V X).1 ≤ 4 ∧ barV V 3 (cellParams V X).2 ∧
      X = mcell (cellParams V X).1 V (cellParams V X).2 :=
    Classical.epsilon_spec
      (p := fun q : ℕ × List V3 => q.1 ≤ 4 ∧ barV V 3 q.2 ∧ X = mcell q.1 V q.2)
      ⟨(min i 4, ul), by omega, hbar, hX4⟩
  have hnnull : ¬ nullSet X := by
    intro hnull
    unfold VX at hu0
    rw [if_pos hnull] at hu0
    simp at hu0
  unfold VX at hu0 hu1
  simp only [if_neg hnnull] at hu0 hu1
  by_cases hk0 : (cellParams V X).1 = 0
  · rw [if_pos hk0] at hu0
    simp at hu0
  · rw [if_neg hk0] at hu0 hu1
    have h4 : (cellParams V X).2.length = 4 := hwit.2.1.1
    have hlen : (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2).length
        = (cellParams V X).1 := by
      have h := p23_trunc_init_len ((cellParams V X).1 - 1) (cellParams V X).2
        (by omega)
      omega
    set l := truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2 with hleq
    simp only [setOfList, Set.mem_setOf_eq] at hu0 hu1
    rcases l with _ | ⟨a, t⟩
    · simp at hu0
    · rcases t with _ | ⟨b, t2⟩
      · simp only [List.mem_singleton] at hu0 hu1
        exact absurd (hu0.trans hu1.symm) hne
      · simp only [List.length_cons] at hlen
        omega

/-- Junk-safety for the future `grutoti_pivot` fill (PA2:410-417 encoding):
`dihX` vanishes whenever the `cellParamsD` index is outside `{2,3,4}`
(the `k ≤ 1` arm) — the null-cell arm is already banked as
`p23_dihX_of_nullSet`. -/
private theorem p23_dihX_of_cellParamsD_ne (V : Set V3) (X : Set V3) (p : V3 × V3)
    (hnn : ¬ nullSet X)
    (h2 : (cellParamsD V X [p.1, p.2]).1 ≠ 2)
    (h3 : (cellParamsD V X [p.1, p.2]).1 ≠ 3)
    (h4 : (cellParamsD V X [p.1, p.2]).1 ≠ 4) : dihX V X p = 0 := by
  simp only [dihX, if_neg hnn, if_neg h2, if_neg h3, if_neg h4]


/-! ## Giants (sorried, NEEDS-precision) -/

/-- HL GRUTOTI.hl:86-160: the `k = 3` specialization of grutoti_3mem — the
Voronoi cell of the edge is the union of the Rogers hulls
`convex hull {ω₁, ω₂, ω₃}` over `barV V 3` lists truncating to `[u0, u1]`.
FILLED (2026-09-19) from grutoti_3mem plus
`PackingAuto12.VORONOI_LIST_3_SINGLETON_EXPLICIT` (SHIM: still `sorry`ed
upstream in Auto12): on each truncation list the Voronoi cell is the
singleton `{a}`, `a = circumcenter (setOfList vl)`, and `omega_list_n V vl 3`
— being `closest_point` on that singleton (with
`truncate_simplex 3 vl = vl` and `CLOSEST_POINT_SING`) — equals `a`, so the
3mem family `{hull ({ωᵢ | i ∈ Icc 1 2} ∪ voronoiList V vl)}` coincides with
the hull-of-triple family. -/
private theorem grutoti_vor_cover (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (hbar : barV V 1 [u0, u1]) :
    voronoiList V [u0, u1] =
      ⋃₀ {convexHull ℝ {omegaListN V vl 1, omegaListN V vl 2, omegaListN V vl 3} |
          vl ∈ {vl : List V3 | barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]}} := by
  have key : ∀ vl : List V3, barV V 3 vl → truncateSimplex 1 vl = [u0, u1] →
      convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc 1 (3 - 1)} ∪ voronoiList V vl) =
        convexHull ℝ {omegaListN V vl 1, omegaListN V vl 2, omegaListN V vl 3} := by
    intro vl hb _htr
    obtain ⟨a, hsingle, hcc, -⟩ := VORONOI_LIST_3_SINGLETON_EXPLICIT V vl hp hs hb
    have hlen : vl.length = 4 := hb.1
    have homeg : omegaListN V vl 3 = a := by
      have h3 : omegaListN V vl 3
          = closestPoint (voronoiList V (truncateSimplex 3 vl)) (omegaListN V vl 2) := rfl
      rw [h3, TRUNCATE_SIMPLEX_REFL 3 vl hlen, hsingle]
      exact CLOSEST_POINT_SING a (omegaListN V vl 2)
    have hIcc : {omegaListN V vl i | i ∈ Finset.Icc 1 (3 - 1)}
        = {omegaListN V vl 1, omegaListN V vl 2} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        Finset.mem_coe, Finset.mem_Icc]
      constructor
      · rintro ⟨i, hi1, hi2, rfl⟩
        rcases Nat.eq_zero_or_pos (i - 1) with h0 | _h0
        · exact Or.inl (by rw [show i = 1 by omega])
        · exact Or.inr (by rw [show i = 2 by omega])
      · rintro (rfl | rfl)
        · exact ⟨1, by norm_num, rfl⟩
        · exact ⟨2, by norm_num, rfl⟩
    congr 1
    rw [hIcc, hsingle, homeg]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  rw [grutoti_3mem V u0 u1 hp hs hbar]
  refine Set.ext fun X => ?_
  constructor
  · intro hX
    rw [Set.mem_sUnion] at hX
    obtain ⟨t, ht, hX⟩ := hX
    rw [Set.mem_setOf_eq] at ht
    obtain ⟨vl, hmem, rfl⟩ := ht
    rw [Set.mem_setOf_eq] at hmem
    obtain ⟨hb, htr⟩ := hmem
    rw [key vl hb htr] at hX
    refine Set.mem_sUnion.mpr ⟨convexHull ℝ {omegaListN V vl 1, omegaListN V vl 2,
      omegaListN V vl 3}, ?_, hX⟩
    exact ⟨vl, Set.mem_setOf.mpr ⟨hb, htr⟩, rfl⟩
  · intro hX
    rw [Set.mem_sUnion] at hX
    obtain ⟨t, ht, hX⟩ := hX
    rw [Set.mem_setOf_eq] at ht
    obtain ⟨vl, hmem, rfl⟩ := ht
    rw [Set.mem_setOf_eq] at hmem
    obtain ⟨hb, htr⟩ := hmem
    rw [(key vl hb htr).symm] at hX
    refine Set.mem_sUnion.mpr ⟨convexHull ℝ ({omegaListN V vl i |
      i ∈ Finset.Icc 1 (3 - 1)} ∪ voronoiList V vl), ?_, hX⟩
    exact ⟨vl, Set.mem_setOf.mpr ⟨hb, htr⟩, rfl⟩

/-! ## GT-4 lane: B1-B4 region-block bridges (2026-09-30, zero sorry)

HL GRUTOTI.hl:161-1143 (B1-B4): the bisector hyperplane S1, the interface
S = voronoiList V [u0,u1], the midpoint bridge (Rogers.XYOFCGX), the critical
radius δ and the cone threshold c. These feed the P1-P4 extremal arguments
(B5-B7) that assemble grutoti_region below; p23_region_exists_c is the
current milestone. NOTE: HL's S2 = S1 \ relative_interior S is replaced by
the explicit relative neighbourhood S' = S1 ∩ ball(p,d₀) ⊆ S (HL B2's
nearest-point selection); this avoids both the aff-dim equality
aff hull S = S1 (whose Lean counterpart AFF_DIM_VORONOI_LIST is unported)
and the intrinsicInterior bridge.
-/

/-! ## B1: the bisector hyperplane -/

/-- The bisector hyperplane of the edge (HL `S1`, GRUTOTI.hl:252), in the
ray-friendly form `(x - u0) · (u1 - u0) = d²/2`. -/
private def p23Bis (u0 u1 : V3) : Set V3 :=
  {x | inner ℝ (x - u0) (u1 - u0) = dist u0 u1 ^ 2 / 2}

private theorem p23_inner_expand (a b c d : V3) :
    inner ℝ (a - b) (c - d) = inner ℝ a c - inner ℝ a d - inner ℝ b c + inner ℝ b d := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  ring

private theorem p23_dist_sq (x v : V3) :
    dist x v ^ 2 = inner ℝ x x - 2 * inner ℝ x v + inner ℝ v v := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_sub_right, real_inner_comm v x]
  ring

/-- equidistance characterizes the bisector -/
private theorem p23_dist_eq_bis (u0 u1 x : V3) :
    dist x u0 = dist x u1 ↔ x ∈ p23Bis u0 u1 := by
  have e0 := p23_dist_sq x u0
  have e1 := p23_dist_sq x u1
  have hd : dist u0 u1 ^ 2 = inner ℝ u1 u1 - 2 * inner ℝ u0 u1 + inner ℝ u0 u0 := by
    rw [dist_comm u0 u1, dist_eq_norm, ← real_inner_self_eq_norm_sq]
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm u1 u0]
    ring
  have hx : inner ℝ (x - u0) (u1 - u0)
      = inner ℝ x u1 - inner ℝ x u0 - inner ℝ u0 u1 + inner ℝ u0 u0 :=
    p23_inner_expand x u0 u1 u0
  constructor
  · intro h
    rw [← h] at e1
    show inner ℝ (x - u0) (u1 - u0) = _
    rw [hx]
    linarith
  · intro h
    show dist x u0 = dist x u1
    rw [p23Bis, Set.mem_setOf_eq] at h
    have h2 : dist x u0 ^ 2 = dist x u1 ^ 2 := by rw [e0, e1]; linarith
    have h3 := congrArg Real.sqrt h2
    rw [Real.sqrt_sq dist_nonneg, Real.sqrt_sq dist_nonneg] at h3
    exact h3

/-- HL CLOSED_HYPERPLANE: the bisector is closed. -/
private theorem p23_bis_closed (u0 u1 : V3) : IsClosed (p23Bis u0 u1) := by
  set f : V3 → ℝ := fun x => inner ℝ (x - u0) (u1 - u0) with hf
  have hcont : Continuous f := by
    unfold f
    exact (continuous_id.sub continuous_const).inner continuous_const
  have h1 : IsClosed {x : V3 | f x ≤ dist u0 u1 ^ 2 / 2} :=
    isClosed_le hcont continuous_const
  have h2 : IsClosed {x : V3 | dist u0 u1 ^ 2 / 2 ≤ f x} :=
    isClosed_le continuous_const hcont
  have h3 : p23Bis u0 u1 = {x : V3 | f x ≤ dist u0 u1 ^ 2 / 2} ∩
      {x : V3 | dist u0 u1 ^ 2 / 2 ≤ f x} := by
    ext x
    simp only [p23Bis, Set.mem_setOf_eq, Set.mem_inter_iff, hf]
    constructor
    · intro h; exact ⟨le_of_eq h, le_of_eq h.symm⟩
    · intro h; exact le_antisymm h.1 h.2
  rw [h3]
  exact h1.inter h2

/-- the Voronoi cell of a point is closed -/
private theorem p23_voronoiClosed_closed (V : Set V3) (v : V3) :
    IsClosed (voronoiClosed V v) := by
  have h : voronoiClosed V v = ⋂ w : V, {x : V3 | dist x v ≤ dist x w} := by
    ext x
    rw [voronoiClosed, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · exact fun hx i => hx i i.property
    · exact fun hx w hw => hx ⟨w, hw⟩
  rw [h]
  refine isClosed_iInter fun w => ?_
  exact isClosed_le (Continuous.dist continuous_id continuous_const)
    (Continuous.dist continuous_id continuous_const)

/-- `voronoi_list V [u0;u1]` = the intersection of the two cells -/
private theorem p23_voronoiList_pair (V : Set V3) (u0 u1 : V3) :
    voronoiList V [u0, u1] = voronoiClosed V u0 ∩ voronoiClosed V u1 := by
  show ⋂₀ {voronoiClosed V v | v ∈ setOfList [u0, u1]} = _
  ext x
  constructor
  · intro hx
    have h0 := hx (voronoiClosed V u0)
      (Set.mem_image_of_mem _ (by simp [setOfList]))
    have h1 := hx (voronoiClosed V u1)
      (Set.mem_image_of_mem _ (by simp [setOfList]))
    exact ⟨h0, h1⟩
  · intro hx t ht
    obtain ⟨v, hv, rfl⟩ := ht
    have hv' : v ∈ ({u0, u1} : Set V3) := by simpa [setOfList] using hv
    rcases Set.mem_insert_iff.mp hv' with rfl | rfl
    · exact hx.1
    · exact hx.2

/-- the interface is closed -/
private theorem p23_voronoiList_closed (V : Set V3) (u0 u1 : V3) :
    IsClosed (voronoiList V [u0, u1]) := by
  rw [p23_voronoiList_pair V u0 u1]
  exact (p23_voronoiClosed_closed V u0).inter (p23_voronoiClosed_closed V u1)

/-- the interface is inside the bisector -/
private theorem p23_voronoiList_sub_bis (V : Set V3) (u0 u1 : V3)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) :
    voronoiList V [u0, u1] ⊆ p23Bis u0 u1 := by
  intro x hx
  rw [p23_voronoiList_pair V u0 u1] at hx
  refine p23_dist_eq_bis u0 u1 x |>.mp ?_
  refine le_antisymm ?_ ?_
  · exact hx.1 u1 hu1
  · exact hx.2 u0 hu0

/-- saturation bounds every closed Voronoi cell (HL BOUNDED_VORONOI_LIST
route, via the <2 saturation axiom) -/
private theorem p23_voronoiClosed_bounded (V : Set V3) (hs : saturated V) (v : V3) :
    Bornology.IsBounded (voronoiClosed V v) := by
  refine Bornology.IsBounded.subset (Metric.isBounded_ball (x := v) (r := 2)) ?_
  intro x hx
  obtain ⟨y, hy, hdy⟩ := hs x
  have hle : dist x v ≤ dist x y := hx y hy
  rw [Metric.mem_ball]
  linarith

/-- nonzero vector orthogonal to the edge direction -/
private theorem p23_exists_orthogonal (u0 u1 : V3) (hne : u0 ≠ u1) :
    ∃ w : V3, w ≠ 0 ∧ inner ℝ w (u0 - u1) = 0 := by
  have hnz : (u0 - u1 : V3) ≠ 0 := sub_ne_zero.mpr hne
  set N : Submodule ℝ V3 := Submodule.span ℝ ({u0 - u1} : Set V3) with hN
  have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
  have hrk : 0 < Module.finrank ℝ ↥Nᗮ := by
    have hdim := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := V3) N
    have hrkN : Module.finrank ℝ ↥N = 1 := by
      rw [hN]
      exact finrank_span_singleton hnz
    rw [h3] at hdim
    linarith
  obtain ⟨x, hx0⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := ↥Nᗮ)).mp hrk
  refine ⟨(x : V3), ?_, ?_⟩
  · intro hwx
    exact hx0 (Subtype.ext hwx)
  · have hxm : (x : V3) ∈ Nᗮ := x.property
    exact (Submodule.mem_orthogonal' N (x : V3)).mp hxm (u0 - u1)
      (by rw [hN]; exact Submodule.mem_span_singleton_self _)

/-- HL UNBOUNDED_HYPERPLANE: the bisector hyperplane is unbounded -/
private theorem p23_bisector_unbounded (u0 u1 : V3) (hne : u0 ≠ u1) :
    ¬ Bornology.IsBounded (p23Bis u0 u1) := by
  intro hb
  rw [Metric.isBounded_iff] at hb
  obtain ⟨K, hK⟩ := hb
  obtain ⟨w, hw0, hwdot⟩ := p23_exists_orthogonal u0 u1 hne
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hpn : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
  have hpm : p ∈ p23Bis u0 u1 := by
    show inner ℝ (p - u0) (u1 - u0) = _
    rw [hpn, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [show dist u0 u1 = ‖u1 - u0‖ from by
      rw [dist_comm u0 u1, dist_eq_norm, norm_sub_rev]]
    ring
  have hwne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hwpos : (0:ℝ) < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hwne)
  have hwdot' : inner ℝ w (u1 - u0) = 0 := by
    have : (u1 - u0 : V3) = (-1 : ℝ) • (u0 - u1) := by module
    rw [this, real_inner_smul_right, hwdot]
    ring
  have hmem : ∀ t : ℝ, p + t • w ∈ p23Bis u0 u1 := by
    intro t
    show inner ℝ (p + t • w - u0) (u1 - u0) = _
    have h1 : p + t • w - u0 = (p - u0) + t • w := by abel
    rw [h1, inner_add_left, real_inner_smul_left, hpm, hwdot']
    ring
  have hy : p + (((|K| : ℝ) + 1) / ‖w‖) • w ∈ p23Bis u0 u1 := hmem _
  have hdist : K < dist p (p + (((|K| : ℝ) + 1) / ‖w‖) • w) := by
    have h1 : dist p (p + (((|K| : ℝ) + 1) / ‖w‖) • w)
        = (((|K| : ℝ) + 1) / ‖w‖) * ‖w‖ := by
      rw [dist_eq_norm]
      have h2 : p - (p + (((|K| : ℝ) + 1) / ‖w‖) • w)
          = (-(((|K| : ℝ) + 1) / ‖w‖)) • w := by
        module
      have h4 : 0 < ((|K| : ℝ) + 1) / ‖w‖ :=
        div_pos (by linarith [abs_nonneg K]) hwpos
      have h3 : -((((|K| : ℝ) + 1) / ‖w‖) : ℝ) < 0 := by linarith
      rw [h2, norm_smul, Real.norm_eq_abs, abs_of_neg h3]
      ring
    rw [h1]
    field_simp
    linarith [le_abs_self K]
  exact absurd (hK hpm hy) (not_le.mpr hdist)

/-! ## B2: the midpoint bridge (HL Rogers.XYOFCGX, GRUTOTI.hl:561-575) -/

/-- the edge's own endpoint is NOT in the interface -/
private theorem p23_u0_notMem_voronoiList (V : Set V3) (u0 u1 : V3)
    (hu0 : u0 ∈ V) (hd : dist u0 u1 ≠ 0) : u0 ∉ voronoiList V [u0, u1] := by
  intro hx
  rw [p23_voronoiList_pair V u0 u1] at hx
  have h1 : dist u0 u1 ≤ dist u0 u0 := hx.2 u0 hu0
  rw [dist_self] at h1
  exact hd (le_antisymm h1 dist_nonneg)

/-- HL Rogers.XYOFCGX (strict form): every packing point other than the two
edge points is strictly farther from the edge midpoint than the half-length. -/
private theorem p23_midpoint_dist_gt (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) :
    ∀ w ∈ V, w ≠ u0 → w ≠ u1 →
      dist u0 u1 / 2 < dist (u0 + (1 / 2 : ℝ) • (u1 - u0)) w := by
  intro w hw hw0 hw1
  have hHL2 : hl [u0, u1] = dist u0 u1 / 2 := HL_2 u0 u1
  set d := dist u0 u1 with hddef
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hdpos : 0 ≤ d := dist_nonneg
  have hd8 : d ^ 2 < 8 := by
    rw [hHL2] at hhl
    have h1 : d < 2 * Real.sqrt 2 := by nlinarith
    have h2 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt (by norm_num : (0:ℝ) < 2))]
      norm_num
    nlinarith [hdpos, h1, h2]
  have apol : 4 * dist p w ^ 2
      = 2 * (dist w u0 ^ 2 + dist w u1 ^ 2) - d ^ 2 := by
    have h1 : p - w = (1 / 2 : ℝ) • ((u0 - w) + (u1 - w)) := by rw [hpdef]; module
    have h2 : dist p w = ‖(u0 - w) + (u1 - w)‖ / 2 := by
      rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
      field_simp
    have e1 : inner ℝ ((u0 - w) + (u1 - w)) ((u0 - w) + (u1 - w))
        = inner ℝ (u0 - w) (u0 - w) + 2 * inner ℝ (u0 - w) (u1 - w)
          + inner ℝ (u1 - w) (u1 - w) := by
      rw [inner_add_left, inner_add_right, inner_add_right,
        real_inner_comm (u1 - w) (u0 - w)]
      ring
    have e2 : d ^ 2 = inner ℝ (u0 - w) (u0 - w)
        - 2 * inner ℝ (u0 - w) (u1 - w) + inner ℝ (u1 - w) (u1 - w) := by
      have h3 : d = ‖(u0 - w) - (u1 - w)‖ := by
        rw [hddef, dist_eq_norm]
        congr 1
        module
      rw [h3, ← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    have n1 : ‖u0 - w‖ = dist w u0 := by rw [dist_eq_norm, norm_sub_rev]
    have n2 : ‖u1 - w‖ = dist w u1 := by rw [dist_eq_norm, norm_sub_rev]
    have n3 : ‖(u0 - w) + (u1 - w)‖ ^ 2
        = inner ℝ ((u0 - w) + (u1 - w)) ((u0 - w) + (u1 - w)) :=
      (real_inner_self_eq_norm_sq _).symm
    have h4 : dist p w ^ 2 = ‖(u0 - w) + (u1 - w)‖ ^ 2 / 4 := by
      rw [h2]
      field_simp
      ring
    rw [h4, n3, e1, e2]
    rw [real_inner_self_eq_norm_sq (u0 - w), real_inner_self_eq_norm_sq (u1 - w), n1, n2]
    field_simp
    linarith
  have hge0 : 2 ≤ dist w u0 := hp.dist_ge_two hw hu0 hw0
  have hge1 : 2 ≤ dist w u1 := hp.dist_ge_two hw hu1 hw1
  have hq0 : 4 ≤ dist w u0 ^ 2 := by nlinarith
  have hq1 : 4 ≤ dist w u1 ^ 2 := by nlinarith
  by_contra hcc
  push_neg at hcc
  have hdpw : (0:ℝ) ≤ dist p w := dist_nonneg
  have hsum : 0 ≤ d / 2 + dist p w := by linarith
  have hsq : (d / 2) ^ 2 = d ^ 2 / 4 := by ring
  have hs : dist p w ^ 2 < (d / 2) ^ 2 := by nlinarith [hcc, hsum, hdpw]
  linarith [apol, hq0, hq1, hd8, hs, hsq]

/-- HL Rogers.XYOFCGX: the edge midpoint is weakly closer to u0/u1 than every
other point of the packing (needs only `hl < √2` for the strictness). -/
private theorem p23_midpoint_mem_voronoiList (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) :
    u0 + (1 / 2 : ℝ) • (u1 - u0) ∈ voronoiList V [u0, u1] := by
  have hHL2 : hl [u0, u1] = dist u0 u1 / 2 := HL_2 u0 u1
  set d := dist u0 u1 with hddef
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hdpos : 0 ≤ d := dist_nonneg
  have hd8 : d ^ 2 < 8 := by
    rw [hHL2] at hhl
    have h1 : d < 2 * Real.sqrt 2 := by nlinarith
    have h2 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt (by norm_num : (0:ℝ) < 2))]
      norm_num
    nlinarith [hdpos, h1, h2]
  have hpu0 : dist p u0 = d / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [dist_eq_norm] at hddef
    rw [hddef, norm_sub_rev]
    ring
  have hpu1 : dist p u1 = d / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u1 = (1 / 2 : ℝ) • (u0 - u1) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [dist_eq_norm] at hddef
    rw [hddef, norm_sub_rev]
    ring
  have apol : ∀ w : V3, 4 * dist p w ^ 2
      = 2 * (dist w u0 ^ 2 + dist w u1 ^ 2) - d ^ 2 := by
    intro w
    have h1 : p - w = (1 / 2 : ℝ) • ((u0 - w) + (u1 - w)) := by rw [hpdef]; module
    have h2 : dist p w = ‖(u0 - w) + (u1 - w)‖ / 2 := by
      rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
      field_simp
    have e1 : inner ℝ ((u0 - w) + (u1 - w)) ((u0 - w) + (u1 - w))
        = inner ℝ (u0 - w) (u0 - w) + 2 * inner ℝ (u0 - w) (u1 - w)
          + inner ℝ (u1 - w) (u1 - w) := by
      rw [inner_add_left, inner_add_right, inner_add_right,
        real_inner_comm (u1 - w) (u0 - w)]
      ring
    have e2 : d ^ 2 = inner ℝ (u0 - w) (u0 - w)
        - 2 * inner ℝ (u0 - w) (u1 - w) + inner ℝ (u1 - w) (u1 - w) := by
      have h3 : d = ‖(u0 - w) - (u1 - w)‖ := by
        rw [hddef, dist_eq_norm]
        congr 1
        module
      rw [h3, ← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    have n1 : ‖u0 - w‖ = dist w u0 := by rw [dist_eq_norm, norm_sub_rev]
    have n2 : ‖u1 - w‖ = dist w u1 := by rw [dist_eq_norm, norm_sub_rev]
    have n3 : ‖(u0 - w) + (u1 - w)‖ ^ 2
        = inner ℝ ((u0 - w) + (u1 - w)) ((u0 - w) + (u1 - w)) :=
      (real_inner_self_eq_norm_sq _).symm
    have h4 : dist p w ^ 2 = ‖(u0 - w) + (u1 - w)‖ ^ 2 / 4 := by
      rw [h2]
      field_simp
      ring
    rw [h4, n3, e1, e2]
    rw [real_inner_self_eq_norm_sq (u0 - w), real_inner_self_eq_norm_sq (u1 - w), n1, n2]
    field_simp
    linarith
  have key : ∀ w ∈ V, w ≠ u0 → w ≠ u1 → d / 2 ≤ dist p w :=
    fun w hw hw0 hw1 => le_of_lt (p23_midpoint_dist_gt V u0 u1 hp hu0 hu1 hne hhl w hw hw0 hw1)
  rw [p23_voronoiList_pair V u0 u1]
  constructor
  · rw [voronoiClosed, Set.mem_setOf_eq]
    intro w hw
    by_cases hw0 : w = u0
    · subst hw0
      exact le_refl _
    by_cases hw1 : w = u1
    · subst hw1
      rw [hpu0, hpu1]
    · rw [hpu0]
      exact key w hw hw0 hw1
  · rw [voronoiClosed, Set.mem_setOf_eq]
    intro w hw
    by_cases hw0 : w = u0
    · subst hw0
      rw [hpu1, hpu0]
    by_cases hw1 : w = u1
    · subst hw1
      exact le_refl _
    · rw [hpu1]
      exact key w hw hw0 hw1



/-! ## B1 conclusion: the critical radius -/

/-- Pythagoras on the bisector: `‖z - u0‖² = ‖z - p‖² + (d/2)²` for `z` on the
bisector and `p` the edge midpoint. -/
private theorem p23_bis_pythagoras (u0 u1 z : V3) (hz : z ∈ p23Bis u0 u1) :
    dist u0 z ^ 2 = ‖z - (u0 + (1 / 2 : ℝ) • (u1 - u0))‖ ^ 2 + (dist u0 u1 / 2) ^ 2 := by
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hpn : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
  have hbis : z ∈ p23Bis u0 u1 := hz
  rw [p23Bis, Set.mem_setOf_eq] at hbis
  have hzdot : inner ℝ (z - p) (u1 - u0) = 0 := by
    have h1 : z - p = (z - u0) - (p - u0) := by abel
    have h2 : inner ℝ (p - u0) (u1 - u0) = dist u0 u1 ^ 2 / 2 := by
      rw [hpn, real_inner_smul_left, real_inner_self_eq_norm_sq]
      rw [show dist u0 u1 = ‖u1 - u0‖ from by
        rw [dist_comm u0 u1, dist_eq_norm, norm_sub_rev]]
      ring
    rw [h1, inner_sub_left, hbis, h2]
    ring
  have h1 : z - u0 = (z - p) + (p - u0) := by abel
  have h2 : dist u0 z = ‖z - u0‖ := by rw [dist_eq_norm, norm_sub_rev]
  have h3 : ‖p - u0‖ = dist u0 u1 / 2 := by
    rw [hpn, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show dist u0 u1 = ‖u1 - u0‖ from by
      rw [dist_comm u0 u1, dist_eq_norm, norm_sub_rev]]
    ring
  have h4 : inner ℝ (z - p) (p - u0) = 0 := by
    rw [hpn, real_inner_smul_right, hzdot]
    ring
  have h5 : dist u0 z ^ 2
      = ‖z - p‖ ^ 2 + 2 * inner ℝ (z - p) (p - u0) + ‖p - u0‖ ^ 2 := by
    have e0 : inner ℝ (z - u0) (z - u0)
        = inner ℝ (z - p) (z - p) + 2 * inner ℝ (z - p) (p - u0)
          + inner ℝ (p - u0) (p - u0) := by
      have hz1 : z - u0 = (z - p) + (p - u0) := by abel
      rw [hz1, inner_add_left, inner_add_right, inner_add_right,
        real_inner_comm (p - u0) (z - p)]
      ring
    rw [h2, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, e0, h4]
  calc dist u0 z ^ 2
      = ‖z - p‖ ^ 2 + 2 * inner ℝ (z - p) (p - u0) + ‖p - u0‖ ^ 2 := h5
    _ = ‖z - p‖ ^ 2 + (dist u0 u1 / 2) ^ 2 := by rw [h4, h3]; ring

/-- translated form of `Packing.finite_inter_ball` (Statement.lean, centered
at 0) -/
private theorem p23_finite_inter_ball (V : Set V3) (hp : Packing V) (v : V3) (r : ℝ) :
    (V ∩ Metric.ball v r).Finite := by
  have hp' : Packing ((fun x : V3 => x - v) '' V) := by
    intro u hu w hw hlt
    obtain ⟨u, huV, rfl⟩ := hu
    obtain ⟨w, hwV, rfl⟩ := hw
    refine congrArg (fun x => x - v) (hp u huV w hwV ?_)
    rw [dist_eq_norm]
    have hab : (u - v) - (w - v) = u - w := by abel
    rw [← hab, ← dist_eq_norm]
    exact hlt
  have hfin : (((fun x : V3 => x - v) '' V) ∩ Metric.ball 0 r).Finite :=
    Packing.finite_inter_ball hp' r
  have hsub : V ∩ Metric.ball v r
      ⊆ (fun x : V3 => v + x) '' (((fun x : V3 => x - v) '' V) ∩ Metric.ball 0 r) := by
    rintro x ⟨hxV, hxb⟩
    refine ⟨x - v, ⟨Set.mem_image_of_mem _ hxV, ?_⟩, by abel⟩
    rw [Metric.mem_ball] at hxb ⊢
    rw [dist_zero_right]
    rw [dist_comm, dist_eq_norm, norm_sub_rev] at hxb
    exact hxb
  exact ((hfin.image (fun x : V3 => v + x))).subset hsub

/-- B1 conclusion (HL GRUTOTI.hl:253-590): a critical radius `δ` strictly above
the half-length such that every bisector point closer than `δ` to `u0` lies in
the interface `S = voronoiList V [u0, u1]`.

Instead of HL's `S2 = S1 \ relative_interior S` (whose closedness needs the
aff-dim equality `aff hull S = S1`), we build the explicit relative
neighbourhood `S' = S1 ∩ ball(p, d₀) ⊆ S` from HL's B2 nearest-point selection
(`a'` in `V ∩ ball(p,8) \ {u0,u1}`, `d₀ = (dist(p,a') - d/2)/4`) and minimize
over the closed set `S1 ∩ (ball(p,d₀))ᶜ`. -/
private theorem p23_region_exists_delta (V : Set V3) (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) :
    ∃ δ : ℝ, dist u0 u1 / 2 < δ ∧ ∀ y ∈ p23Bis u0 u1, dist u0 y < δ →
      y ∈ voronoiList V [u0, u1] := by
  set d := dist u0 u1 with hddef
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hdpos : 0 < d := dist_pos.mpr (fun hcc => hne hcc)
  have hdp2 : 0 < d / 2 := by linarith
  have hdp8 : d / 2 < 2 := by
    have h1 : hl [u0, u1] = d / 2 := HL_2 u0 u1
    have h2 : hl [u0, u1] < Real.sqrt 2 := hhl
    have h3 : Real.sqrt 2 < 2 := by
      have h3a : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h3b : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      by_contra h4
      push_neg at h4
      nlinarith [h3a, h3b, h4]
    rw [h1] at h2
    linarith
  -- the distances from p to the two edge points are d/2
  have hu0p : dist p u0 = d / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show d = ‖u1 - u0‖ from by rw [hddef, dist_eq_norm, norm_sub_rev]]
    ring
  have hu1p : dist p u1 = d / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u1 = (1 / 2 : ℝ) • (u0 - u1) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show d = ‖u0 - u1‖ from by rw [hddef, dist_eq_norm]]
    ring
  -- the strict nearest-point bound (XYOFCGX)
  have hgt := p23_midpoint_dist_gt V u0 u1 hp hu0 hu1 hne hhl
  -- B2: finite nonempty set of non-edge packing points inside ball(p,8)
  set A : Set V3 := (V ∩ Metric.ball p 8) \ {u0, u1} with hAdef
  have hAfin : A.Finite := (p23_finite_inter_ball V hp p 8).diff (t := {u0, u1})
  have hAne : A.Nonempty := by
    obtain ⟨y0, hy0⟩ : ∃ y0 : V3, dist p y0 = 4 :=
      ⟨p + (4 / (dist p u0)) • (u0 - p), by
        rw [dist_eq_norm]
        have h1 : p - (p + (4 / (dist p u0)) • (u0 - p))
            = -((4 / (dist p u0)) • (u0 - p)) := by abel
        have hnup : ‖u0 - p‖ = dist p u0 := by
          rw [← dist_eq_norm]
          exact dist_comm u0 p
        have hpu0pos : (0:ℝ) < dist p u0 := by rw [hu0p]; linarith
        have hq4 : (0:ℝ) < 4 / dist p u0 := div_pos (by norm_num) hpu0pos
        rw [h1, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_pos hq4, hnup, hu0p]
        field_simp⟩
    obtain ⟨z', hz'V, hz'd⟩ := hs y0
    have hz'8 : dist p z' < 8 := by
      have h1 : dist p z' ≤ dist p y0 + dist y0 z' := dist_triangle p y0 z'
      rw [hy0] at h1
      linarith
    have hz'0 : z' ≠ u0 := by
      intro hcc
      have h1 : dist p y0 ≤ dist p u0 + dist u0 y0 := by
        rw [← hcc]
        exact dist_triangle p z' y0
      rw [hy0, hu0p] at h1
      have h2 : dist u0 y0 < 2 := by rw [← hcc, dist_comm]; exact hz'd
      linarith [h2, hdp8]
    have hz'1 : z' ≠ u1 := by
      intro hcc
      have h1 : dist p y0 ≤ dist p u1 + dist u1 y0 := by
        rw [← hcc]
        exact dist_triangle p z' y0
      rw [hy0, hu1p] at h1
      have h2 : dist u1 y0 < 2 := by rw [← hcc, dist_comm]; exact hz'd
      linarith [h2, hdp8]
    refine ⟨z', ⟨⟨hz'V, ?_⟩, by simp [hz'0, hz'1]⟩⟩
    rw [Metric.mem_ball, dist_comm]
    exact hz'8
  -- a' := the nearest point of A
  obtain ⟨a', ha'A, hamin⟩ :=
    Set.exists_min_image A (fun w : V3 => dist p w) hAfin hAne
  have ha'V : a' ∈ V := ha'A.1.1
  have ha'ball : dist p a' < 8 := by
    have h5 : dist a' p < 8 := Metric.mem_ball.mp ha'A.1.2
    rw [dist_comm]
    exact h5
  have ha'0 : a' ≠ u0 := fun hcc => ha'A.2 (by simp [hcc])
  have ha'1 : a' ≠ u1 := fun hcc => ha'A.2 (by simp [hcc])
  have hapos : d / 2 < dist p a' := hgt a' ha'V ha'0 ha'1
  set d0 := (dist p a' - d / 2) / 4 with hd0def
  have hd00 : 0 < d0 := by linarith
  have hapos4 : dist p a' = d / 2 + 4 * d0 := by rw [hd0def]; linarith
  -- S' = p23Bis ∩ ball(p,d0) is inside the interface
  have hS' : ∀ x ∈ p23Bis u0 u1, dist p x < d0 → x ∈ voronoiList V [u0, u1] := by
    intro x hxb hxd
    have hdist : dist x u0 = dist x u1 := (p23_dist_eq_bis u0 u1 x).mpr hxb
    rw [p23_voronoiList_pair V u0 u1]
    constructor
    · rw [voronoiClosed, Set.mem_setOf_eq]
      intro w hw
      by_cases hw0 : w = u0
      · subst hw0
        exact le_refl _
      by_cases hw1 : w = u1
      · subst hw1
        rw [hdist]
      · have hchain1 : dist p w - dist p x ≤ dist x w := by
          have := dist_triangle p x w
          linarith
        have hwge : dist p a' ≤ dist p w := by
          by_cases hwb : w ∈ Metric.ball p 8
          · have hwA : w ∈ A := by
              rw [hAdef, Set.mem_sdiff]
              exact ⟨⟨hw, hwb⟩, by simp [hw0, hw1]⟩
            exact hamin w hwA
          · have h1 : ¬ dist p w < 8 := fun hcc =>
              hwb (by rw [Metric.mem_ball, dist_comm]; exact hcc)
            have h2 : dist p w ≥ 8 := le_of_not_gt h1
            linarith
        have h2 : dist x u0 ≤ dist p x + d / 2 := by
          have h5b : dist x u0 ≤ dist x p + dist p u0 := dist_triangle x p u0
          rw [hu0p, dist_comm x p] at h5b
          linarith
        have h3 : dist x u0 < dist x w := by
          have h4 : dist p a' - d0 = d / 2 + 3 * d0 := by rw [hapos4]; linarith
          have h5 : dist p a' - dist p x > dist p a' - d0 := by linarith
          have h6 : dist x u0 < d / 2 + d0 := by linarith
          linarith
        linarith
    · rw [voronoiClosed, Set.mem_setOf_eq]
      intro w hw
      by_cases hw0 : w = u0
      · subst hw0
        rw [hdist]
      by_cases hw1 : w = u1
      · subst hw1
        exact le_refl _
      · have hchain1 : dist p w - dist p x ≤ dist x w := by
          have := dist_triangle p x w
          linarith
        have hwge : dist p a' ≤ dist p w := by
          by_cases hwb : w ∈ Metric.ball p 8
          · have hwA : w ∈ A := by
              rw [hAdef, Set.mem_sdiff]
              exact ⟨⟨hw, hwb⟩, by simp [hw0, hw1]⟩
            exact hamin w hwA
          · have h1 : ¬ dist p w < 8 := fun hcc =>
              hwb (by rw [Metric.mem_ball, dist_comm]; exact hcc)
            have h2 : dist p w ≥ 8 := le_of_not_gt h1
            linarith
        have h2 : dist x u1 ≤ dist p x + d / 2 := by
          have h5b : dist x u1 ≤ dist x p + dist p u1 := dist_triangle x p u1
          rw [hu1p, dist_comm x p] at h5b
          linarith
        have h3 : dist x u1 < dist x w := by
          have h4 : dist p a' - d0 = d / 2 + 3 * d0 := by rw [hapos4]; linarith
          linarith
        linarith
  -- minimize dist u0 · over the closed set S2 = p23Bis ∩ ball(p,d0)ᶜ
  have hS2cl : IsClosed (p23Bis u0 u1 ∩ (Metric.ball p d0)ᶜ) :=
    (p23_bis_closed u0 u1).inter Metric.isOpen_ball.isClosed_compl
  have hS2ne : (p23Bis u0 u1 ∩ (Metric.ball p d0)ᶜ).Nonempty := by
    by_contra hcon
    have hsub : p23Bis u0 u1 ⊆ Metric.ball p d0 := by
      intro x hx
      by_contra hx2
      rw [Metric.mem_ball] at hx2
      have hxmem : x ∈ p23Bis u0 u1 ∩ (Metric.ball p d0)ᶜ := ⟨hx, hx2⟩
      exact hcon ⟨x, hxmem⟩
    exact p23_bisector_unbounded u0 u1 hne
      ((Metric.isBounded_ball (x := p) (r := d0)).subset hsub)
  obtain ⟨z, hzS2, hdz⟩ := hS2cl.exists_infDist_eq_dist hS2ne u0
  obtain ⟨hzbis, hzball⟩ := hzS2
  rw [Set.mem_compl_iff, Metric.mem_ball] at hzball
  push_neg at hzball
  have hzp : z ≠ p := by
    intro hcc
    rw [hcc, dist_self] at hzball
    linarith
  have hpy := p23_bis_pythagoras u0 u1 z hzbis
  have hd2 : (d / 2) ^ 2 < dist u0 z ^ 2 := by
    rw [hpy]
    have hnz : ‖z - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzp)
    have hpos : 0 < ‖z - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnz)
    nlinarith [hpos]
  refine ⟨dist u0 z, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have hx0 : (0:ℝ) ≤ dist u0 z := dist_nonneg
    have hs2 : 0 ≤ d / 2 + dist u0 z := by linarith
    nlinarith [hd2, hcon, hs2, hx0]
  · intro y hyb hlt
    have hyin : y ∈ Metric.ball p d0 := by
      by_contra hyball
      have hy2 : y ∈ p23Bis u0 u1 ∩ (Metric.ball p d0)ᶜ := ⟨hyb, hyball⟩
      have hle := Metric.infDist_le_dist_of_mem (s := p23Bis u0 u1 ∩ (Metric.ball p d0)ᶜ)
        (x := u0) (y := y) hy2
      rw [hdz] at hle
      exact absurd hlt (not_lt.mpr hle)
    have hlt2 : dist p y < d0 := by
      have h5c : dist y p < d0 := Metric.mem_ball.mp hyin
      rw [dist_comm] at h5c
      exact h5c
    exact hS' y hyb hlt2

/-! ## B3+B4: the cone over the interface contains a small rcone
(HL GRUTOTI.hl:590-1143) -/

/-- B3+B4 (HL GRUTOTI.hl:590-1143): there is a cosine-threshold `c ∈ (0,1)`
with `rconeGt u0 u1 c` inside the cone from `u0` over the interface `S`
(`affGeAlt {u0} S`) and inside `rconeGt u0 u1 (hl/√2)`. -/
private theorem p23_region_exists_c (V : Set V3) (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      rconeGt u0 u1 c ⊆ affGeAlt {u0} (voronoiList V [u0, u1]) ∧
      rconeGt u0 u1 c ⊆ rconeGt u0 u1 (hl [u0, u1] / Real.sqrt 2) := by
  obtain ⟨δ, hδcrit, hcrit⟩ := p23_region_exists_delta V u0 u1 hs hp hu0 hu1 hne hhl
  have hdpos : 0 < dist u0 u1 := dist_pos.mpr (fun hcc => hne hcc)
  have hδ0 : 0 < δ := lt_of_le_of_lt (by positivity) hδcrit
  -- the provisional threshold b = (d/2)/δ ∈ (0,1)
  set b := dist u0 u1 / 2 / δ with hbdef
  have hb0 : 0 < b := div_pos (by linarith) hδ0
  have hbne : b ≠ 0 := ne_of_gt hb0
  have hb1 : b < 1 := (div_lt_one hδ0).mpr hδcrit
  have hbkey : dist u0 u1 ^ 2 / 2 = dist u0 u1 * b * δ := by
    have hδne : δ ≠ 0 := ne_of_gt hδ0
    have h1b : b * δ = dist u0 u1 / 2 := by
      rw [hbdef]
      exact div_mul_cancel₀ _ hδne
    rw [mul_assoc, h1b]
    ring
  have hbincl : ∀ x, x ∈ rconeGt u0 u1 b →
      affGeAlt {u0} (voronoiList V [u0, u1]) x := by
    intro x hx
    rw [rconeGt, Set.mem_setOf_eq] at hx
    rw [dist_comm u1 u0] at hx
    have hx2 : inner ℝ (x - u0) (u1 - u0) > dist x u0 * (dist u0 u1 * b) := by
      rw [inner_eq_dot, ← mul_assoc]
      exact hx
    have hxn : x ≠ u0 := by
      intro hcc
      rw [hcc] at hx2
      simp at hx2
    have hD0 : 0 < dist u0 u1 := dist_pos.mpr (fun hcc => hne hcc)
    have hDne : dist u0 u1 ≠ 0 := fun hcc => hne (dist_eq_zero.mp hcc)
    have htne : dist x u0 ≠ 0 := fun hcc => hxn (dist_eq_zero.mp hcc)
    have ht0 : 0 < dist x u0 := lt_of_le_of_ne dist_nonneg (Ne.symm htne)
    have htp : 0 < (dist x u0)⁻¹ := inv_pos.mpr ht0
    obtain ⟨ww, hwdef⟩ : ∃ ww : V3, ww = (dist x u0)⁻¹ • (x - u0) := ⟨_, rfl⟩
    have hwn : ‖ww‖ = 1 := by
      rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos htp]
      rw [← dist_eq_norm, inv_mul_cancel₀ htne]
    have hwx : x - u0 = dist x u0 • ww := by
      rw [hwdef, smul_smul, mul_inv_cancel₀ htne, one_smul]
    have h1 : inner ℝ (x - u0) (u1 - u0)
        = dist x u0 * inner ℝ ww (u1 - u0) := by
      rw [hwx, real_inner_smul_left]
    have hwdot : dist u0 u1 * b < inner ℝ ww (u1 - u0) := by
      have h3 : dist x u0 * (dist u0 u1 * b)
          < dist x u0 * inner ℝ ww (u1 - u0) := by
        rw [← h1]
        exact hx2
      exact lt_of_mul_lt_mul_left h3 (le_of_lt ht0)
    have hq1 : 0 < dist u0 u1 * b := mul_pos hD0 hb0
    have hqpos : 0 < inner ℝ ww (u1 - u0) := by linarith
    have hqne : inner ℝ ww (u1 - u0) ≠ 0 := ne_of_gt hqpos
    -- the hit point of the ray u0 → x with the bisector hyperplane
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ,
        s = (dist u0 u1 ^ 2 / 2) / inner ℝ ww (u1 - u0) := ⟨_, rfl⟩
    have hs0 : 0 < s := by
      rw [hsdef]
      exact div_pos (div_pos (sq_pos_of_ne_zero hDne) (by norm_num)) hqpos
    obtain ⟨y, hydef⟩ : ∃ y : V3, y = u0 + s • ww := ⟨_, rfl⟩
    have hywu : y - u0 = s • ww := by rw [hydef]; module
    have hybis : y ∈ p23Bis u0 u1 := by
      show inner ℝ (y - u0) (u1 - u0) = _
      rw [hywu, real_inner_smul_left, hsdef]
      field_simp
    have hdy : dist u0 y = s := by
      rw [dist_eq_norm, norm_sub_rev, hywu, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs0, hwn, mul_one]
    have hyne : y ≠ u0 := by
      intro hcc
      rw [hcc, dist_self] at hdy
      exact absurd hdy.symm (ne_of_gt hs0)
    have hsδ : s < δ := by
      have h8' : s * inner ℝ ww (u1 - u0) = dist u0 u1 * b * δ := by
        rw [hsdef, div_mul_cancel₀ _ hqne]
        exact hbkey
      have h9 : dist u0 u1 * b * δ < inner ℝ ww (u1 - u0) * δ :=
        mul_lt_mul_of_pos_right hwdot hδ0
      have h10 : inner ℝ ww (u1 - u0) * s < inner ℝ ww (u1 - u0) * δ := by
        rw [mul_comm (inner ℝ ww (u1 - u0)) s, h8']
        linarith
      exact lt_of_mul_lt_mul_left h10 hqpos.le
    have hyS : y ∈ voronoiList V [u0, u1] := hcrit y hybis (by rw [hdy]; exact hsδ)
    -- assemble the affGeAlt witness
    have hsne : s ≠ 0 := ne_of_gt hs0
    obtain ⟨hh, hhdef⟩ : ∃ hh : ℝ, hh = dist x u0 / s := ⟨_, rfl⟩
    have hh0 : 0 < hh := by rw [hhdef]; exact div_pos ht0 hs0
    have key : x - u0 = hh • (y - u0) := by
      rw [hywu, hhdef, smul_smul, div_mul_cancel₀ _ hsne]
      exact hwx
    have hxeq : x = (1 - hh) • u0 + hh • y := by
      have e1 : x = u0 + (x - u0) := (add_sub_cancel u0 x).symm
      rw [e1, key]
      module
    refine ⟨fun v => if v = u0 then 1 - hh else if v = y then hh else 0, {y},
      Set.finite_singleton y, ?_, ?_, ?_, ?_⟩
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hyS
    · have hfin : (({u0} ∪ {y} : Set V3)).Finite := by simp
      have htofin : hfin.toFinset = ({u0, y} : Finset V3) := by
        ext z
        simp
        tauto
      rw [linCombo, dif_pos hfin, htofin,
        Finset.sum_insert (by intro hcc; rw [Finset.mem_singleton] at hcc; exact hyne hcc.symm), Finset.sum_singleton]
      have hfu0 : (if u0 = u0 then 1 - hh else if u0 = y then hh else 0) = 1 - hh := by
        simp [hyne]
      have hfy : (if y = u0 then 1 - hh else if y = y then hh else 0) = hh := by
        simp [hyne]
      rw [hfu0, hfy]
      exact hxeq
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simp [hyne, hh0.le]
    · have hfin : (({u0} ∪ {y} : Set V3)).Finite := by simp
      have htofin : hfin.toFinset = ({u0, y} : Finset V3) := by
        ext z
        simp
        tauto
      rw [setSum, dif_pos hfin, htofin,
        Finset.sum_insert (by intro hcc; rw [Finset.mem_singleton] at hcc; exact hyne hcc.symm), Finset.sum_singleton]
      have hfu0 : (if u0 = u0 then 1 - hh else if u0 = y then hh else 0) = 1 - hh := by
        simp [hyne]
      have hfy : (if y = u0 then 1 - hh else if y = y then hh else 0) = hh := by
        simp [hyne]
      rw [hfu0, hfy]
      ring
  -- B4: raise the threshold to c = max b (hl/√2)
  have hhlpos : 0 < hl [u0, u1] := by rw [HL_2]; linarith
  have hhl1 : hl [u0, u1] / Real.sqrt 2 < 1 :=
    (div_lt_one (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))).mpr hhl
  refine ⟨max b (hl [u0, u1] / Real.sqrt 2), lt_max_of_lt_left hb0, max_lt hb1 hhl1, ?_, ?_⟩
  · intro x hx
    exact hbincl _ (RCONE_GT_SUBSET u0 u1 b _ (le_max_left _ _) hx)
  · intro x hx
    exact RCONE_GT_SUBSET u0 u1 (hl [u0, u1] / Real.sqrt 2) _ (le_max_right _ _) hx

/-! ## GT-4b lane: B5-B7 region-block remainder (2026-09-30, zero sorry)

HL GRUTOTI.hl:1144-2636: the rogers/mcell cover kit (B5), the P1-P4 extremal
data (B6) and the c/r/d assembly with the mcell cover (B7). Design notes:
* the family `p23Fam V u0 u1` of `barV V 3` lists truncating to `[u0,u1]` is
  finite (lists drawn from `V ∩ ball u0 4`, which is finite by saturation);
* `C ⊆ ⋃₀ rogers-family` goes through the `affGeAlt` witness: a negative
  `f u0` weight would force `‖x - u0‖ ≥ t·(d/2) ≥ t > 1` (Pythagoras on the
  bisector + the packing bound `d ≥ 2`), so the witness is a genuine convex
  segment point `x = (1-t)•u0 + t•w`, `w ∈ S`, and segment-points land in
  `rogers V vl` for a family member (`u0 = ω0` and `S` is the rogers union by
  `grutoti_vor_cover`);
* the k = 0/1 cells miss `C` (`mcell0` lives outside `ball u0 √2`, `mcell1`
  outside the `hl/√2` cone), and `AJRIPQN` (PA17; upstream sorry) pins
  `X = mcell i V vl0`;
* the B6 bounds: `f1 ul > 0`/`f2 ul > 0` kill `u0` in the facet planes
  (else the whole cell sits in a plane — null against `¬null (mcell ∩ C)`),
  and `f3 ul < 1`/`f4 ul < 1` come from the C-S equality case: equality
  collinear forces an endpoint of the segment into the 2-flat of the other
  three points, again nulling the cell;
* `r = min (1/2) (min r1 r2)` replaces HL's `min 1 (min r1 r2)`: the Lean
  `grutotiConicCap` uses a CLOSED ball, so `D ⊆ C` needs `r < 1` strictly;
  the frozen region statement only asks `0 < r ≤ 1` and the cell-volume
  lane only needs `r ≤ min r1 r2`, both preserved.
Upstream sorry debt consumed: PA17 `AJRIPQN` (sorried there), PA12
`VORONOI_LIST_3_SINGLETON_EXPLICIT` (shim). No new `sorry` in this file.
-/

/-! ### B5 kit: the truncation family is finite -/

/-- the `barV V 3` lists truncating to `[u0, u1]` (HL `Ss`) -/
private def p23Fam (V : Set V3) (u0 u1 : V3) : Set (List V3) :=
  {vl | barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]}

/-- HOL `BARV_3_IMP_FINITE_lemma1` (QZYZMJC.hl:62; private copy — the PA15
original is private): two list points of a `barV V 3` simplex over a
saturated packing are less than `4` apart. -/
private theorem p23_barV3ImpFinite1 {V : Set V3} {ul : List V3} {u v : V3}
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (huv : {u, v} ⊆ setOfList ul) : dist u v < 4 := by
  obtain ⟨a, ha1, _ha2, _ha3⟩ := VORONOI_LIST_3_SINGLETON_EXPLICIT V ul hp hs hb
  have hamem : a ∈ voronoiList V ul := by rw [ha1]; exact rfl
  have key : ∀ s ∈ setOfList ul, dist a s < 2 := by
    intro s hsmem
    obtain ⟨y, hyV, hyd⟩ := hs a
    have hmem : a ∈ ⋂₀ {voronoiClosed V w | w ∈ setOfList ul} := hamem
    have has : a ∈ voronoiClosed V s :=
      Set.mem_sInter.mp hmem (voronoiClosed V s) ⟨s, hsmem, rfl⟩
    have h1 : dist a s ≤ dist a y := by
      simpa only [voronoiClosed, Set.mem_setOf_eq] using has y hyV
    calc dist a s ≤ dist a y := h1
      _ < 2 := hyd
  have hdu : dist a u < 2 := key u (huv (by simp))
  have hdv : dist a v < 2 := key v (huv (by simp))
  calc dist u v ≤ dist u a + dist a v := dist_triangle u a v
    _ < 4 := by rw [dist_comm u a]; linarith

/-- HOL `BARV_3_IMP_FINITE_lemma2` (QZYZMJC.hl:104; private copy): the whole
list sits in the radius-`4` ball around any of its points. -/
private theorem p23_barV3ImpFinite2 {V : Set V3} {ul : List V3} {v : V3}
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hv : v ∈ setOfList ul) :
    setOfList ul ⊆ Metric.ball v 4 := by
  intro s hsmem
  refine p23_barV3ImpFinite1 hp hs hb ?_
  intro x hx
  rcases (by simpa using hx : x = s ∨ x = v) with hx1 | hx1
  · rw [hx1]
    exact hsmem
  · rw [hx1]
    exact hv

/-- HL B5 (GRUTOTI.hl:1334-1402): the truncation family is finite — its
members are 4-lists drawn from `V ∩ ball u0 4`, finite by saturation. -/
private theorem p23_family_finite (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hs : saturated V) : (p23Fam V u0 u1).Finite := by
  have hf : (V ∩ Metric.ball u0 4).Finite := p23_finite_inter_ball V hp u0 4
  have hprod : ((V ∩ Metric.ball u0 4) ×ˢ ((V ∩ Metric.ball u0 4) ×ˢ
      ((V ∩ Metric.ball u0 4) ×ˢ (V ∩ Metric.ball u0 4)))).Finite :=
    hf.prod (hf.prod (hf.prod hf))
  have himg : Set.Finite ((fun p : V3 × (V3 × (V3 × V3)) =>
      [p.1, p.2.1, p.2.2.1, p.2.2.2]) '' ((V ∩ Metric.ball u0 4) ×ˢ ((V ∩ Metric.ball u0 4) ×ˢ
      ((V ∩ Metric.ball u0 4) ×ˢ (V ∩ Metric.ball u0 4))))) := Set.Finite.image _ hprod
  refine himg.subset ?_
  intro vl hvl
  obtain ⟨hb, htr⟩ := hvl
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V vl hb
  subst hv
  have hsub : setOfList [v0, v1, v2, v3] ⊆ Metric.ball v0 4 :=
    p23_barV3ImpFinite2 hp hs hb (by simp [setOfList])
  have hVsub : setOfList [v0, v1, v2, v3] ⊆ V := BARV_SUBSET V 3 _ hb
  have hmem : ∀ i : V3, i ∈ setOfList [v0, v1, v2, v3] →
      i ∈ V ∩ Metric.ball u0 4 := by
    intro i hi
    have hvi : i ∈ Metric.ball v0 4 := hsub hi
    have hv0 : v0 = u0 := by
      have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
        (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
      rw [h1] at htr
      exact (List.cons.injEq v0 [v1] u0 [u1] |>.mp htr).1
    rw [hv0] at hvi
    exact ⟨hVsub hi, hvi⟩
  refine ⟨(v0, (v1, (v2, v3))), ?_, rfl⟩
  simp only [Set.mem_prod, Set.mem_inter_iff]
  exact ⟨hmem v0 (by simp [setOfList]), ⟨hmem v1 (by simp [setOfList]),
    ⟨hmem v2 (by simp [setOfList]), hmem v3 (by simp [setOfList])⟩⟩⟩

/-- the head of a family list is `u0` -/
private theorem p23_hdV_eq_u0 {V : Set V3} {u0 u1 : V3} {vl : List V3}
    (hvl : vl ∈ p23Fam V u0 u1) : hdV vl = u0 := by
  obtain ⟨hb, htr⟩ := hvl
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V vl hb
  subst hv
  have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
  rw [h1] at htr
  exact (List.cons.injEq v0 [v1] u0 [u1] |>.mp htr).1

/-- the second entry of a family list is `u1` -/
private theorem p23_hdTail_eq_u1 {V : Set V3} {u0 u1 : V3} {vl : List V3}
    (hvl : vl ∈ p23Fam V u0 u1) : hdV vl.tail = u1 := by
  obtain ⟨hb, htr⟩ := hvl
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V vl hb
  subst hv
  have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
  rw [h1] at htr
  exact (List.cons.injEq v1 [] u1 [] |>.mp
    (List.cons.injEq v0 [v1] u0 [u1] |>.mp htr).2).1

/-- the `mcell` dispatch folds into the `≤ 4` range -/
private theorem p23_mcell_reduce (i : ℕ) (V : Set V3) (ul : List V3) :
    mcell i V ul = mcell (min i 4) V ul := by
  rcases Nat.lt_or_ge i 4 with hlt | hle
  · rw [min_eq_left (le_of_lt hlt)]
  · rw [min_eq_right hle, (MCELL_EXPLICIT i V ul).2.2.2.2 hle,
      (MCELL_EXPLICIT 4 V ul).2.2.2.2 (Nat.le_refl 4)]

/-! ### B5 kit: the interface is convex and the `affGeAlt` witness is a
segment point -/

/-- the closed Voronoi cells are convex (halfspace form of the two-distance
comparison) -/
private theorem p23_voronoiClosed_convex (V : Set V3) (w : V3) :
    Convex ℝ (voronoiClosed V w) := by
  intro x hx y hy a b ha0 hb0 hab
  simp only [voronoiClosed, Set.mem_setOf_eq] at hx hy ⊢
  intro z hz
  have key : ∀ p : V3, dist p w ≤ dist p z ↔
      2 * (inner ℝ p (z - w)) ≤ ‖z‖ ^ 2 - ‖w‖ ^ 2 := by
    intro p
    have expand : ∀ p q : V3, inner ℝ (p - q) (p - q)
        = inner ℝ p p - 2 * inner ℝ p q + inner ℝ q q := by
      intro p q
      rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm q p]
      ring
    have hiff : (dist p w) ^ 2 ≤ (dist p z) ^ 2 ↔ dist p w ≤ dist p z :=
      pow_le_pow_iff_left₀ (a := dist p w) (b := dist p z) (n := 2)
        dist_nonneg dist_nonneg two_ne_zero
    rw [← hiff, dist_eq_norm, dist_eq_norm]
    repeat rw [← real_inner_self_eq_norm_sq]
    rw [expand p w, expand p z]
    have hsplit : inner ℝ p (z - w) = inner ℝ p z - inner ℝ p w := by
      rw [inner_sub_right]
    constructor
    · intro hle
      linarith
    · intro hle
      linarith
  have hw := (key x).mp (hx z hz)
  have hy2 := (key y).mp (hy z hz)
  have hcx : inner ℝ (a • x + b • y) (z - w)
      = a * (inner ℝ x (z - w)) + b * (inner ℝ y (z - w)) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [key, hcx]
  have h1 : a * (2 * inner ℝ x (z - w)) ≤ a * (‖z‖ ^ 2 - ‖w‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hw ha0
  have h2 : b * (2 * inner ℝ y (z - w)) ≤ b * (‖z‖ ^ 2 - ‖w‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hy2 hb0
  have h3 : 2 * (a * inner ℝ x (z - w) + b * inner ℝ y (z - w))
      = a * (2 * inner ℝ x (z - w)) + b * (2 * inner ℝ y (z - w)) := by ring
  have hD : a * (‖z‖ ^ 2 - ‖w‖ ^ 2) + b * (‖z‖ ^ 2 - ‖w‖ ^ 2) = ‖z‖ ^ 2 - ‖w‖ ^ 2 := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- the edge interface `voronoiList V [u0, u1]` is convex -/
private theorem p23_convex_interface (V : Set V3) (u0 u1 : V3) :
    Convex ℝ (voronoiList V [u0, u1]) := by
  rw [p23_voronoiList_pair V u0 u1]
  exact (p23_voronoiClosed_convex V u0).inter (p23_voronoiClosed_convex V u1)

/-- interface points are at least half the edge length from `u0` (Pythagoras
on the bisector, HL XYOFCGX tail) -/
private theorem p23_bis_lower (u0 u1 : V3) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) {w : V3}
    (hw : w ∈ voronoiList V [u0, u1]) : dist u0 u1 / 2 ≤ dist u0 w := by
  have hbis : w ∈ p23Bis u0 u1 := p23_voronoiList_sub_bis V u0 u1 hu0 hu1 hw
  have hpyth := p23_bis_pythagoras u0 u1 w hbis
  have hsq : (dist u0 u1 / 2) ^ 2 ≤ (dist u0 w) ^ 2 := by
    rw [hpyth]
    nlinarith
  exact pow_le_pow_iff_left₀ (a := dist u0 u1 / 2) (b := dist u0 w) (n := 2)
    (by positivity) dist_nonneg two_ne_zero |>.mp hsq

/-- HL B5 head (GRUTOTI.hl:1103-1290, restructured): an `affGeAlt {u0} S`
point inside `ball u0 1` is a segment point `x = (1-t)•u0 + t•w` with
`w ∈ S`, `t ∈ [0,1]`. The negative-weight arm dies against the packing
bound `dist u0 u1 ≥ 2` plus Pythagoras on the bisector. -/
private theorem p23_seg_of_affGeAlt (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hneS : (voronoiList V [u0, u1]).Nonempty) (x : V3)
    (hxW : affGeAlt {u0} (voronoiList V [u0, u1]) x) (hball : dist x u0 < 1) :
    ∃ w : V3, w ∈ voronoiList V [u0, u1] ∧
      x ∈ convexHull ℝ ({u0, w} : Set V3) := by
  -- unpack the affGeAlt witness
  obtain ⟨f, q, qfin, qsub, hxeq, hqnn, hsum⟩ := hxW
  have hTfin : (({u0} ∪ q : Set V3)).Finite := Set.Finite.insert u0 qfin
  haveI hdecU : DecidablePred (· ∈ ({u0} ∪ q : Set V3)) := Classical.decPred _
  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset V3, Q = hTfin.toFinset := ⟨_, rfl⟩
  have hu0Q : u0 ∈ Q := by
    rw [hQdef]
    exact (Set.Finite.mem_toFinset hTfin).mpr
      (Set.mem_union_left q (Set.mem_singleton u0))
  have hxsum : x = ∑ v ∈ Q, f v • v := by
    rw [hQdef]
    have h1 : linCombo ({u0} ∪ q) f = ∑ v ∈ hTfin.toFinset, f v • v := dif_pos hTfin
    rw [hxeq, h1]
  have hsum1 : ∑ v ∈ Q, f v = 1 := by
    rw [hQdef]
    have h1 : setSum ({u0} ∪ q) f = ∑ v ∈ hTfin.toFinset, f v := dif_pos hTfin
    exact h1.symm.trans hsum
  -- the sum splits off the u0-term
  have hsumsplit : ∑ v ∈ Q, f v = f u0 + ∑ v ∈ Q.erase u0, f v := by
    have hEq : Q.erase u0 ∪ {u0} = Q := by
      refine Finset.ext fun z => ?_
      by_cases hz : z = u0
      · subst hz
        simp [hu0Q]
      · simp [hz, hu0Q]
    have hdis : Disjoint (Q.erase u0) ({u0} : Finset V3) := by simp
    have hsu := Finset.sum_union (h := hdis) (f := f)
    calc ∑ v ∈ Q, f v = ∑ v ∈ (Q.erase u0 ∪ {u0} : Finset V3), f v := by rw [hEq]
      _ = ∑ v ∈ Q.erase u0, f v + ∑ v ∈ ({u0} : Finset V3), f v := hsu
      _ = ∑ v ∈ Q.erase u0, f v + f u0 := by rw [Finset.sum_singleton]
      _ = f u0 + ∑ v ∈ Q.erase u0, f v := add_comm _ _
  have hxsplit : x = f u0 • u0 + ∑ v ∈ Q.erase u0, f v • v := by
    have hEq : Q.erase u0 ∪ {u0} = Q := by
      refine Finset.ext fun z => ?_
      by_cases hz : z = u0
      · subst hz
        simp [hu0Q]
      · simp [hz, hu0Q]
    have hdis : Disjoint (Q.erase u0) ({u0} : Finset V3) := by simp
    have hsu := Finset.sum_union (h := hdis)
      (f := fun v : V3 => f v • v)
    calc x = ∑ v ∈ Q, f v • v := hxsum
      _ = ∑ v ∈ (Q.erase u0 ∪ {u0} : Finset V3), f v • v := by rw [hEq]
      _ = ∑ v ∈ Q.erase u0, f v • v + ∑ v ∈ ({u0} : Finset V3), f v • v := hsu
      _ = ∑ v ∈ Q.erase u0, f v • v + f u0 • u0 := by rw [Finset.sum_singleton]
      _ = f u0 • u0 + ∑ v ∈ Q.erase u0, f v • v := add_comm _ _
  have hqmem : ∀ v ∈ Q.erase u0, v ∈ q := by
    intro v hv
    have hvQ : v ∈ Q := Finset.mem_of_mem_erase hv
    have hvne : v ≠ u0 := Finset.ne_of_mem_erase hv
    rw [hQdef] at hvQ
    have hvU : v ∈ ({u0} ∪ q : Set V3) := (Set.Finite.mem_toFinset hTfin).mp hvQ
    rcases hvU with h | h
    · exact absurd (by rw [Set.mem_singleton_iff] at h; exact h ▸ hvne) (by simp)
    · exact h
  -- t := the total weight on the interface points
  set t := ∑ v ∈ Q.erase u0, f v with htdef
  have htnonneg : 0 ≤ t := Finset.sum_nonneg (fun v hv => hqnn v (hqmem v hv))
  have hkey : f u0 + t = 1 := by rw [htdef, ← hsumsplit, hsum1]
  have htsum : t = 1 - f u0 := by linarith
  -- f u0 < 0 (i.e. t > 1) is excluded by the ball bound + the packing lower bound
  have hexcl : ¬ (f u0 < 0) := by
    intro hf0
    have ht1 : 1 < t := by linarith
    have ht0' : 0 < t := by linarith
    have htne : t ≠ 0 := ne_of_gt ht0'
    have hyexpand : ∑ v ∈ Q.erase u0, (f v / t) • v
        = t⁻¹ • ∑ v ∈ Q.erase u0, f v • v := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [smul_smul]
      congr 1
      field_simp
    have hyS : (∑ v ∈ Q.erase u0, (f v / t) • v) ∈ voronoiList V [u0, u1] := by
      refine Convex.sum_mem (p23_convex_interface V u0 u1) ?_ ?_ ?_
      · intro v hv
        exact div_nonneg (hqnn v (hqmem v hv)) ht0'.le
      · rw [show ∑ v ∈ Q.erase u0, f v / t = (∑ v ∈ Q.erase u0, f v) / t from by
            rw [Finset.sum_div], htdef]
        exact div_self (ne_of_gt ht0')
      · intro v hv
        exact qsub (hqmem v hv)
    have hxx : x - u0 = t • ((∑ v ∈ Q.erase u0, (f v / t) • v) - u0) := by
      rw [hxsplit, hyexpand, htdef]
      have hf0t : f u0 = 1 - t := by linarith
      rw [hf0t, smul_sub, smul_smul, mul_inv_cancel₀ htne, one_smul]
      module
    have hnorm : dist x u0 = t * dist u0 (∑ v ∈ Q.erase u0, (f v / t) • v) := by
      rw [dist_eq_norm, hxx, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < t)]
      rw [dist_eq_norm, norm_sub_rev]
    have hlow : dist u0 u1 / 2 ≤ dist u0 (∑ v ∈ Q.erase u0, (f v / t) • v) :=
      p23_bis_lower u0 u1 hu0 hu1 hyS
    have hd2 : 2 ≤ dist u0 u1 := Packing.dist_ge_two hp hu0 hu1 hne
    rw [hnorm] at hball
    have hge : (1 : ℝ) ≤ dist u0 u1 / 2 := by linarith
    have hmul : t * (dist u0 u1 / 2) ≤ t * dist u0 (∑ v ∈ Q.erase u0, (f v / t) • v) :=
      mul_le_mul_of_nonneg_left hlow ht0'.le
    have hge2 : t * 1 ≤ t * (dist u0 u1 / 2) :=
      mul_le_mul_of_nonneg_left hge ht0'.le
    rw [mul_one] at hge2
    linarith
  -- so f u0 ≥ 0 and t = 1 - f u0 ≤ 1
  have hf0pos : 0 ≤ f u0 := le_of_not_gt hexcl
  have ht1' : t ≤ 1 := by linarith
  by_cases ht0 : t = 0
  · -- x = u0
    have hxu0 : x = u0 := by
      have hzero : ∑ v ∈ Q.erase u0, f v = 0 := by rw [← htdef]; exact ht0
      have heach : ∀ v ∈ Q.erase u0, f v = 0 := by
        intro v hv
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun v hv => hqnn v (hqmem v hv))).mp hzero v hv
      have htail : ∑ v ∈ Q.erase u0, f v • v = 0 :=
        Finset.sum_eq_zero (fun v hv => by rw [heach v hv, zero_smul])
      have hfu0 : f u0 = 1 := by rw [← hkey, ht0, add_zero]
      rw [hxsplit, htail, hfu0, one_smul, add_zero]
    refine ⟨hneS.choose, hneS.choose_spec, ?_⟩
    rw [hxu0, convexHull_pair]
    exact ⟨1, 0, by norm_num, by norm_num, by norm_num, by simp⟩
  · -- x = (1 - t) • u0 + t • w with w ∈ S
    have htpos : 0 < t := lt_of_le_of_ne htnonneg (Ne.symm ht0)
    refine ⟨∑ v ∈ Q.erase u0, (f v / t) • v, ?_, ?_⟩
    · refine Convex.sum_mem (p23_convex_interface V u0 u1)
        (fun v hv => div_nonneg (hqnn v (hqmem v hv)) htpos.le) ?_
        (fun v hv => qsub (hqmem v hv))
      rw [show ∑ v ∈ Q.erase u0, f v / t = (∑ v ∈ Q.erase u0, f v) / t from by
          rw [Finset.sum_div], htdef]
      exact div_self (ne_of_gt htpos)
    · have hc : convexHull ℝ ({u0, ∑ v ∈ Q.erase u0, (f v / t) • v} : Set V3)
          = segment ℝ u0 (∑ v ∈ Q.erase u0, (f v / t) • v) := convexHull_pair _ _
      rw [hc]
      have hyexpand : t • (∑ v ∈ Q.erase u0, (f v / t) • v)
          = ∑ v ∈ Q.erase u0, f v • v := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [smul_smul]
        congr 1
        field_simp
      refine ⟨1 - t, t, by linarith, htpos.le, by linarith, ?_⟩
      have hf0t : f u0 = 1 - t := by linarith
      rw [hyexpand, ← hf0t]
      exact hxsplit.symm


/-! ### B5 kit: the cover C ⊆ ⋃₀ rogers-family and the mcell cover -/

/-- `u0` (the family-list head `ω0`) belongs to every rogers simplex of the
family -/
private theorem p23_u0_mem_rogers (V : Set V3) (u0 u1 : V3) {vl : List V3}
    (hvl : vl ∈ p23Fam V u0 u1) : u0 ∈ rogers V vl := by
  have hlen : vl.length = 4 := hvl.1.1
  have h0 : omegaListN V vl 0 = u0 := by
    have hzero : omegaListN V vl 0 = hdV vl := rfl
    rw [hzero, p23_hdV_eq_u0 hvl]
  rw [← h0]
  refine subset_convexHull ℝ _ (Set.mem_image_of_mem _ ?_)
  refine Set.mem_setOf.mpr ?_
  omega

/-- the interface sits in the rogers union over the family (via
`grutoti_vor_cover`: each member hull `{ω1, ω2, ω3}` is inside `rogers`) -/
private theorem p23_S_sub_rogers (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hs : saturated V) (hbar : barV V 1 [u0, u1]) :
    voronoiList V [u0, u1] ⊆ ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1} := by
  rw [grutoti_vor_cover V u0 u1 hp hs hbar]
  intro w hw
  rw [Set.mem_sUnion] at hw
  obtain ⟨t, ht, hw⟩ := hw
  rw [Set.mem_setOf_eq] at ht
  obtain ⟨vl, hvl, rfl⟩ := ht
  have hlen : vl.length = 4 := hvl.1.1
  refine ⟨rogers V vl, ⟨vl, hvl, rfl⟩, ?_⟩
  have hsub : ({omegaListN V vl 1, omegaListN V vl 2, omegaListN V vl 3} : Set V3) ⊆
      (omegaListN V vl '' {j : ℕ | j < vl.length}) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Set.mem_image_of_mem _ (Set.mem_setOf.mpr (by omega))
    · exact Set.mem_image_of_mem _ (Set.mem_setOf.mpr (by omega))
    · exact Set.mem_image_of_mem _ (Set.mem_setOf.mpr (by omega))
  exact convexHull_mono (𝕜 := ℝ) hsub hw

/-- HL B5 (GRUTOTI.hl:1103-1290): the region `C` is covered by the rogers
simplices of the family. -/
private theorem p23_C_sub_rogers (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2)
    (hs : saturated V) (hbar : barV V 1 [u0, u1]) (c : ℝ)
    (hcovW : ∀ x, x ∈ rconeGt u0 u1 c →
      affGeAlt {u0} (voronoiList V [u0, u1]) x) :
    Metric.ball u0 1 ∩ rconeGt u0 u1 c ⊆ ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1} := by
  have hneS : (voronoiList V [u0, u1]).Nonempty :=
    ⟨u0 + (1 / 2 : ℝ) • (u1 - u0), p23_midpoint_mem_voronoiList V u0 u1 hp hu0 hu1 hne hhl⟩
  intro z hz
  obtain ⟨hball, hrcone⟩ := hz
  obtain ⟨w, hwS, zhull⟩ := p23_seg_of_affGeAlt V u0 u1 hp hu0 hu1 hne hneS z
    (hcovW z hrcone) (by rw [Metric.mem_ball] at hball; exact hball)
  have hwU : w ∈ (⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1}) :=
    p23_S_sub_rogers V u0 u1 hp hs hbar hwS
  rw [Set.mem_sUnion] at hwU
  obtain ⟨t, ht, hwR⟩ := hwU
  rw [Set.mem_setOf_eq] at ht
  obtain ⟨vl, hvl, rfl⟩ := ht
  rw [Set.mem_sUnion]
  refine ⟨rogers V vl, ⟨vl, hvl, rfl⟩, ?_⟩
  refine convexHull_min ?_ (convex_convexHull ℝ _) zhull
  have hu0r : u0 ∈ rogers V vl := p23_u0_mem_rogers V u0 u1 hvl
  refine Set.union_subset (Set.singleton_subset_iff.mpr hu0r) ?_
  rw [Set.singleton_subset_iff]
  exact hwR


/-- HL B5 (GRUTOTI.hl:1295-1537): the mcell cover over `C`. Every cell
meeting `C` in positive measure is a `k ≥ 2` cell over a family list. The
`k = 0/1` arms die against the shape of `mcell0`/`mcell1` and the two cone
inclusions of `p23_region_exists_c`; the identification of the cell is
`AJRIPQN` (PA17, upstream sorry). -/
private theorem p23_cover_C (V : Set V3) (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (c : ℝ)
    (hcovHl : ∀ x, x ∈ rconeGt u0 u1 c → x ∈ rconeGt u0 u1 (hl [u0, u1] / Real.sqrt 2))
    (hcover : Metric.ball u0 1 ∩ rconeGt u0 u1 c ⊆
      ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1}) (X : Set V3)
    (hX : X ∈ mcellSet V) (hnull : ¬ nullSet (X ∩ (Metric.ball u0 1 ∩ rconeGt u0 u1 c))) :
    ∃ k vl, 2 ≤ k ∧ barV V 3 vl ∧ X = mcell k V vl ∧ truncateSimplex 1 vl = [u0, u1] := by
  obtain ⟨i', ul, hXeq, hbarul⟩ := Set.mem_setOf_eq.mp hX
  set C := (Metric.ball u0 1 ∩ rconeGt u0 u1 c : Set V3) with hCdef
  have hne0 : volume (X ∩ C) ≠ 0 := hnull
  have hsub : X ∩ C ⊆ X ∩ ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1} :=
    fun z hz => ⟨hz.1, hcover hz.2⟩
  have hne1 : volume (X ∩ ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1}) ≠ 0 :=
    fun h0 => hne0 (measure_mono_null hsub h0)
  -- split the union over the finite family
  have hfam : (p23Fam V u0 u1).Finite := p23_family_finite V u0 u1 hp hs
  have hAfin : ({rogers V vl | vl ∈ p23Fam V u0 u1} : Set (Set V3)).Finite :=
    Set.Finite.image _ hfam
  have hsplit : X ∩ ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1}
      = ⋃₀ ((fun t : Set V3 => X ∩ t) '' {rogers V vl | vl ∈ p23Fam V u0 u1}) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_image]
    constructor
    · rintro ⟨hzX, t, ht, hzt⟩
      exact ⟨X ∩ t, ⟨t, ht, rfl⟩, hzX, hzt⟩
    · rintro ⟨u, ⟨t, ht, rfl⟩, hzX, hzt⟩
      exact ⟨hzX, t, ht, hzt⟩
  have hIfin : (((fun t : Set V3 => X ∩ t) '' {rogers V vl | vl ∈ p23Fam V u0 u1} :
      Set (Set V3))).Finite := hAfin.image _
  have hex : ∃ u ∈ ((fun t : Set V3 => X ∩ t) '' {rogers V vl | vl ∈ p23Fam V u0 u1} :
      Set (Set V3)), volume u ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hkeys : volume (⋃ i ∈ ((fun t : Set V3 => X ∩ t) ''
        {rogers V vl | vl ∈ p23Fam V u0 u1} : Set (Set V3)),
        (fun u : Set V3 => u) i) = 0 ↔ ∀ u ∈ ((fun t : Set V3 => X ∩ t) ''
        {rogers V vl | vl ∈ p23Fam V u0 u1} : Set (Set V3)), volume u = 0 :=
      measure_biUnion_null_iff (s := fun u : Set V3 => u)
        (I := ((fun t : Set V3 => X ∩ t) '' {rogers V vl | vl ∈ p23Fam V u0 u1} :
          Set (Set V3))) hIfin.countable
    have h0 := hkeys.mpr hall
    rw [← Set.sUnion_eq_biUnion] at h0
    rw [← hsplit] at h0
    exact hne1 h0
  obtain ⟨u, hu, hvol⟩ := hex
  rw [Set.mem_image] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  obtain ⟨vl0, hvl0, rfl⟩ := Set.mem_setOf_eq.mp ht
  obtain ⟨hbarvl0, htrvl0⟩ := hvl0
  -- rogers V vl0 ⊆ ⋃_{i ≤ 4} mcell i V vl0 (SLTSTLO1) and split again
  have hsub2 : X ∩ rogers V vl0 ⊆ ⋃ i ∈ (Set.Iic 4 : Set ℕ), X ∩ mcell i V vl0 := by
    intro z hz
    obtain ⟨hzX, hzr⟩ := hz
    obtain ⟨i, hi, hzr2⟩ := SLTSTLO1 V vl0 z hs hp hbarvl0 hzr
    exact Set.mem_biUnion (Set.mem_Iic.mpr hi) ⟨hzX, hzr2⟩
  have hex2 : ∃ i ∈ (Set.Iic 4 : Set ℕ), volume (X ∩ mcell i V vl0) ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hkeys : volume (⋃ i ∈ (Set.Iic 4 : Set ℕ), X ∩ mcell i V vl0) = 0
        ↔ ∀ i ∈ (Set.Iic 4 : Set ℕ), volume (X ∩ mcell i V vl0) = 0 :=
      measure_biUnion_null_iff (s := fun i : ℕ => X ∩ mcell i V vl0)
        (I := (Set.Iic 4 : Set ℕ)) (Set.finite_Iic 4).countable
    have h0 := hkeys.mpr hall
    exact hvol (measure_mono_null hsub2 h0)
  obtain ⟨i, hi4, hvol2⟩ := hex2
  -- the uniqueness lemma (AJRIPQN, PA17; upstream sorry debt recorded)
  have hmem45 : ∀ n : ℕ, n ≤ 4 → n ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by
    intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hred : X = mcell (min i' 4) V ul := by
    rw [hXeq, p23_mcell_reduce]
  have hvol3 : ¬ nullSet (mcell i V vl0 ∩ mcell (min i' 4) V ul) := by
    rw [hred] at hvol2
    rw [Set.inter_comm] at hvol2
    exact hvol2
  obtain ⟨hieq, hcell⟩ := AJRIPQN V vl0 ul i (min i' 4) hs hp hbarvl0 hbarul
    (hmem45 i (Set.mem_Iic.mp hi4))
    (hmem45 _ (min_le_iff.mpr (Or.inr (by omega))))
    hvol3
  have hXvl0 : X = mcell i V vl0 := by
    rw [hred, ← hcell, hieq]
  -- rule out i = 0, 1
  have hi2 : ¬ (i = 0 ∨ i = 1) := by
    have hlt2 : i < 2 ∨ 2 ≤ i := Nat.lt_or_ge i 2
    rcases hlt2 with hlt | hge
    · have hi01 : i = 0 ∨ i = 1 := by omega
      rcases hi01 with h0 | h1
      · -- i = 0: mcell0 = rogers \ ball(u0,√2) misses C ⊆ ball(u0,1)
        subst h0
        exfalso
        apply hnull
        rw [hXvl0, (MCELL_EXPLICIT 0 V vl0).1, mcell0, p23_hdV_eq_u0 ⟨hbarvl0, htrvl0⟩]
        have hempty : (rogers V vl0 \ Metric.ball u0 (Real.sqrt 2)) ∩ C = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          obtain ⟨⟨_, hzball⟩, hzC⟩ := hz
          simp only [hCdef, Set.mem_inter_iff] at hzC
          have h1s2 : (1:ℝ) < Real.sqrt 2 :=
            (Real.lt_sqrt (by positivity)).mpr (by norm_num : (1:ℝ) ^ 2 < 2)
          rw [Metric.mem_ball] at hzball
          have hge : Real.sqrt 2 ≤ dist z u0 := not_lt.mp hzball
          exact absurd (Metric.mem_ball.mp hzC.1) (by linarith)
        exact measure_mono_null hempty.subset measure_empty
      · -- i = 1: mcell1 misses C ⊆ rconeGt (hl/√2)
        subst h1
        exfalso
        apply hnull
        rw [hXvl0, (MCELL_EXPLICIT 1 V vl0).2.1, mcell1,
          p23_hdTail_eq_u1 ⟨hbarvl0, htrvl0⟩, p23_hdV_eq_u0 ⟨hbarvl0, htrvl0⟩, htrvl0]
        by_cases hcond : Real.sqrt 2 ≤ hl vl0
        · rw [if_pos hcond]
          have hempty : ((rogers V vl0 ∩ Metric.closedBall u0 (Real.sqrt 2)) \
              rconeGt u0 u1 (hl [u0, u1] / Real.sqrt 2)) ∩ C = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro z hz
            obtain ⟨⟨_, hzcone⟩, hzC⟩ := hz
            simp only [hCdef, Set.mem_inter_iff] at hzC
            exact absurd (hcovHl z hzC.2) hzcone
          exact measure_mono_null hempty.subset measure_empty
        · rw [if_neg hcond]
          exact measure_mono_null (by simp) measure_empty
    · omega
  refine ⟨i, vl0, by omega, hbarvl0, ?_, htrvl0⟩
  rw [hXvl0]


/-! ### B6 kit: the P1-P4 extremal bounds (HL 1538-2610) -/

/-- a set inside the affine span of a coplanar set is null (convenience
re-splice of `p23_coplanar_affineSpan_null` with the triple base case) -/
private theorem p23_coplanar_triple (a b c : V3) : Coplanar ℝ ({a, b, c} : Set V3) :=
  _root_.coplanar_triple (k := ℝ) a b c

/-- the `mcell 3` body sits in any affine span containing its four defining
points (empty when the `hl` guard fails) -/
private theorem p23_mcell3_sub_span {V : Set V3} {ul : List V3} {u0 u1 v2 : V3}
    (htr2 : setOfList (truncateSimplex 2 ul) = ({u0, u1, v2} : Set V3))
    {S : Set V3}
    (h0 : u0 ∈ (affineSpan ℝ S : Set V3)) (h1 : u1 ∈ (affineSpan ℝ S : Set V3))
    (h2 : v2 ∈ (affineSpan ℝ S : Set V3)) (hm : mxi V ul ∈ (affineSpan ℝ S : Set V3)) :
    mcell 3 V ul ⊆ (affineSpan ℝ S : Set V3) := by
  rw [(MCELL_EXPLICIT 3 V ul).2.2.2.1]
  unfold mcell3
  split
  · refine convexHull_min (𝕜 := ℝ) ?_ (AffineSubspace.convex _)
    intro z hz
    rcases hz with hz | hz
    · rw [htr2] at hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | hz
      · exact h0
      · rcases hz with rfl | rfl
        · exact h1
        · exact h2
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hm
  · intro z hz
    exact absurd hz (Set.notMem_empty z)

/-- the `mcell 4` body sits in any affine span containing its four defining
points -/
private theorem p23_mcell4_sub_span {V : Set V3} {ul : List V3} {u0 u1 v2 v3 : V3}
    (htr4 : setOfList ul = ({u0, u1, v2, v3} : Set V3))
    {S : Set V3}
    (h0 : u0 ∈ (affineSpan ℝ S : Set V3)) (h1 : u1 ∈ (affineSpan ℝ S : Set V3))
    (h2 : v2 ∈ (affineSpan ℝ S : Set V3)) (h3 : v3 ∈ (affineSpan ℝ S : Set V3)) :
    mcell 4 V ul ⊆ (affineSpan ℝ S : Set V3) := by
  rw [(MCELL_EXPLICIT 4 V ul).2.2.2.2 (Nat.le_refl 4)]
  unfold mcell4
  split
  · refine convexHull_min (𝕜 := ℝ) ?_ (AffineSubspace.convex _)
    intro z hz
    rw [htr4] at hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | hz
    · exact h0
    · rcases hz with rfl | hz
      · exact h1
      · rcases hz with rfl | rfl
        · exact h2
        · exact h3
  · intro z hz
    exact absurd hz (Set.notMem_empty z)

/-- a cell lying in a plane is null against any set (the HL
`NEGLIGIBLE_SUBSET (affine hull …)` workhorse) -/
private theorem p23_null_of_span {V : Set V3} {ul : List V3} (k : ℕ) (T : Set V3)
    (hsub : mcell k V ul ⊆ (affineSpan ℝ T : Set V3)) (hcop : Coplanar ℝ T) :
    nullSet (mcell k V ul ∩ T) :=
  measure_mono_null Set.inter_subset_left
    (p23_coplanar_affineSpan_null hcop hsub)

/-- B6 P3 core: `u0` is not on the segment joining the third vertex and the
fourth point (`mxi`); else the whole cell lies in the plane of the other
three and is null against the non-nullness hypothesis. -/
private theorem p23_u0_notIn_hull3 (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 3 V ul ∩ Cst)) :
    u0 ∉ convexHull ℝ ({elV ul 2, mxi V ul} : Set V3) := by
  intro hu0
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
  subst hv
  have hv01 : v0 = u0 ∧ v1 = u1 := by
    have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
      (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
    rw [h1] at htr
    have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
    exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
  rw [hv01.1, hv01.2] at htr hnn hu0
  have htr2 : setOfList (truncateSimplex 2 [u0, u1, v2, v3])
      = ({u0, u1, v2} : Set V3) := by
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 v2 v3).2]
    ext z
    simp [setOfList]
  have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
  rw [hE2] at hu0
  have hu0span : u0 ∈
      (affineSpan ℝ ({u1, v2, mxi V [u0, u1, v2, v3]} : Set V3) : Set V3) := by
    refine convexHull_min (𝕜 := ℝ) ?_ (AffineSubspace.convex _) hu0
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact mem_affineSpan (k := ℝ) (by simp)
    · exact mem_affineSpan (k := ℝ) (by simp)
  have hnull : nullSet (mcell 3 V [u0, u1, v2, v3]) :=
    p23_coplanar_affineSpan_null (p23_coplanar_triple u1 v2 (mxi V [u0, u1, v2, v3]))
      (p23_mcell3_sub_span htr2 hu0span (mem_affineSpan (k := ℝ) (by simp))
        (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp)))
  exact hnn (measure_mono_null Set.inter_subset_left hnull)

/-- B6 P4 core: same facet-plane killer for the fourth vertex. -/
private theorem p23_u0_notIn_hull4 (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 4 V ul ∩ Cst)) :
    u0 ∉ convexHull ℝ ({elV ul 2, elV ul 3} : Set V3) := by
  intro hu0
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
  subst hv
  have hv01 : v0 = u0 ∧ v1 = u1 := by
    have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
      (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
    rw [h1] at htr
    have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
    exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
  rw [hv01.1, hv01.2] at htr hnn hu0
  have htr4 : setOfList [u0, u1, v2, v3] = ({u0, u1, v2, v3} : Set V3) := by
    ext z
    simp [setOfList]
  have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
  have hE3 : elV [u0, u1, v2, v3] 3 = v3 := rfl
  rw [hE2, hE3] at hu0
  have hu0span : u0 ∈
      (affineSpan ℝ ({u1, v2, v3} : Set V3) : Set V3) := by
    refine convexHull_min (𝕜 := ℝ) ?_ (AffineSubspace.convex _) hu0
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact mem_affineSpan (k := ℝ) (by simp)
    · exact mem_affineSpan (k := ℝ) (by simp)
  have hnull : nullSet (mcell 4 V [u0, u1, v2, v3]) :=
    p23_coplanar_affineSpan_null (p23_coplanar_triple u1 v2 v3)
      (p23_mcell4_sub_span htr4 hu0span (mem_affineSpan (k := ℝ) (by simp))
        (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp)))
  exact hnn (measure_mono_null Set.inter_subset_left hnull)

/-- C-S equality core (HL 2126-2255 restructured): if a point of the segment
`[a, b]` has cosine exactly `1` towards the edge `(u0, u1)`, then one
endpoint lies in the affine span of `{u0, u1, other}` — the plane-cells
killer behind `f3 ul < 1` / `f4 ul < 1`. -/
private theorem p23_collinear_core (u0 u1 a b : V3) (hne : u0 ≠ u1) (xx : V3)
    (hxx : xx ∈ convexHull ℝ ({a, b} : Set V3)) (hk1 : ‖xx - u0‖ ≠ 0)
    (hcs : inner ℝ (xx - u0) (u1 - u0) = ‖xx - u0‖ * ‖u1 - u0‖) :
    b ∈ (affineSpan ℝ ({u0, u1, a} : Set V3) : Set V3) ∨
      a ∈ (affineSpan ℝ ({u0, u1, b} : Set V3) : Set V3) := by
  have hk1p : 0 < ‖xx - u0‖ := lt_of_le_of_ne (norm_nonneg (xx - u0)) (Ne.symm hk1)
  have hk2 : ‖u1 - u0‖ ≠ 0 := fun hcc => hne (dist_eq_zero.mp
    (by rw [dist_comm u0 u1]; exact hcc))
  have hk2p : 0 < ‖u1 - u0‖ := lt_of_le_of_ne (norm_nonneg (u1 - u0)) (Ne.symm hk2)
  set k1 := ‖xx - u0‖ with hk1def
  set k2 := ‖u1 - u0‖ with hk2def
  -- the unit-vector trick gives k2 • (xx - u0) = k1 • (u1 - u0)
  have ha'n : ‖(k1)⁻¹ • (xx - u0)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk1p), inv_mul_cancel₀ hk1]
  have hb'n : ‖(k2)⁻¹ • (u1 - u0)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk2p), inv_mul_cancel₀ hk2]
  have hA1 : inner ℝ ((k1)⁻¹ • (xx - u0)) ((k1)⁻¹ • (xx - u0)) = 1 := by
    rw [real_inner_self_eq_norm_sq, ha'n]; norm_num
  have hB1 : inner ℝ ((k2)⁻¹ • (u1 - u0)) ((k2)⁻¹ • (u1 - u0)) = 1 := by
    rw [real_inner_self_eq_norm_sq, hb'n]; norm_num
  have hAb : inner ℝ ((k1)⁻¹ • (xx - u0)) ((k2)⁻¹ • (u1 - u0)) = 1 := by
    rw [real_inner_smul_left, real_inner_smul_right, hcs]
    field_simp
  have hsub : ‖(k1)⁻¹ • (xx - u0) - (k2)⁻¹ • (u1 - u0)‖ = 0 := by
    have h2 : ‖(k1)⁻¹ • (xx - u0) - (k2)⁻¹ • (u1 - u0)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
        hA1, hB1, real_inner_comm ((k1)⁻¹ • (xx - u0)) ((k2)⁻¹ • (u1 - u0)), hAb]
      ring
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  have hzero : (k1)⁻¹ • (xx - u0) - (k2)⁻¹ • (u1 - u0) = 0 := norm_eq_zero.mp hsub
  have he1 : (k1)⁻¹ • (xx - u0) = (k2)⁻¹ • (u1 - u0) := sub_eq_zero.mp hzero
  have hlin : k2 • (xx - u0) = k1 • (u1 - u0) := by
    have key := congrArg (fun z : V3 => (k2 * k1) • z) he1
    simp only [smul_smul] at key
    field_simp at key
    exact key
  -- the segment coordinates of xx
  obtain ⟨u, v, hu0, hv0, huv, hxuv⟩ :
      ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v = 1 ∧ u • a + v • b = xx := by
    have hseg : convexHull ℝ ({a, b} : Set V3) = segment ℝ a b := convexHull_pair a b
    rw [hseg] at hxx
    exact hxx
  have hE1 : k2 • xx = k1 • (u1 - u0) + k2 • u0 := by rw [← hlin]; module
  have hE2 : k2 • xx = (k2 * u) • a + (k2 * v) • b := by
    have hxx2 : xx = u • a + v • b := hxuv.symm
    rw [hxx2, smul_add, smul_smul, smul_smul]
  by_cases hv : v = 0
  · -- xx = u • a with u = 1: a lies on the line u0→u1
    right
    have hu1 : u = 1 := by linarith
    have hvne : k2 * 1 ≠ 0 := mul_ne_zero hk2 (by norm_num : (1:ℝ) ≠ 0)
    have hkey : a = u0 + (k1 / (k2 * 1)) • (u1 - u0)
        + (-(k2 * 0) / (k2 * 1)) • (b - u0) := by
      have hscaled : (k2 * 1) • a = (k2 * 1) • (u0 + (k1 / (k2 * 1)) • (u1 - u0)
          + (-(k2 * 0) / (k2 * 1)) • (b - u0)) := by
        rw [mul_one, mul_zero, neg_zero, zero_div, zero_smul, add_zero, smul_add, smul_smul,
          mul_div_cancel₀ _ hk2, add_comm (k2 • u0) (k1 • (u1 - u0)), ← hE1, hE2,
          hu1, hv, mul_one, mul_zero, zero_smul, add_zero]
      exact smul_right_injective V3 hvne hscaled
    exact p23_mem_affineSpan_triple u0 u1 b a (k1 / (k2 * 1)) (-(k2 * 0) / (k2 * 1)) hkey
  · -- v ≠ 0: b lies in the plane of {u0, u1, a}
    left
    have hvne : k2 * v ≠ 0 := mul_ne_zero hk2 hv
    have hv1 : k2 * v + k2 * u = k2 := by
      have h2 : k2 * v + k2 * u = k2 * (u + v) := by ring
      rw [h2, huv, mul_one]
    have hbexp : (k2 * v) • b = k1 • (u1 - u0) + k2 • u0 - (k2 * u) • a := by
      calc (k2 * v) • b = k2 • xx - (k2 * u) • a := by rw [hE2]; module
        _ = k1 • (u1 - u0) + k2 • u0 - (k2 * u) • a := by rw [hE1]
    have hkey : b = u0 + (k1 / (k2 * v)) • (u1 - u0)
        + ((k2 * u) / (k2 * v)) • (u0 - a) := by
      have hadd : (k2 * v) • u0 + (k2 * u) • u0 = k2 • u0 := by
        rw [← add_smul, hv1]
      have hscaled : (k2 * v) • b = (k2 * v) • (u0 + (k1 / (k2 * v)) • (u1 - u0)
          + ((k2 * u) / (k2 * v)) • (u0 - a)) := by
        simp only [smul_add, smul_smul, mul_div_cancel₀ _ hvne]
        rw [hbexp, smul_sub (k2 * u) u0 a]
        linear_combination (norm := module) -hadd
      exact smul_right_injective V3 hvne hscaled
    refine p23_mem_affineSpan_triple u0 u1 a b (k1 / (k2 * v)) (-(k2 * u) / (k2 * v)) ?_
    rw [hkey, smul_sub]
    module

/-- B6 P3 (HL 1546-1600 + 1826-1911): the P3 cosine values are all `< 1` —
the smallest-angle point of the `[v2, mxi]` segment cannot be collinear with
the edge, else the `mcell 3` cell sits in a plane. -/
private theorem p23_f3_lt_one (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (hne : u0 ≠ u1) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 3 V ul ∩ Cst)) :
    inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0) /
      (‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖) < 1 := by
  have hu0K : u0 ∉ convexHull ℝ ({elV ul 2, mxi V ul} : Set V3) :=
    p23_u0_notIn_hull3 V u0 u1 hp hs hb htr Cst hnn
  have hxmem : smallestAngleLine (elV ul 2) (mxi V ul) u0 u1
      ∈ convexHull ℝ ({elV ul 2, mxi V ul} : Set V3) :=
    SMALLEST_ANGLE_IN_CONVEX_HULL (elV ul 2) (mxi V ul) u0 u1
      (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1) hne hu0K rfl
  have hxxne : smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 ≠ u0 := fun hcc =>
    hu0K (hcc ▸ hxmem)
  have hk1 : ‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ ≠ 0 := fun hcc =>
    hxxne (sub_eq_zero.mp (norm_eq_zero.mp hcc))
  have hk2 : ‖u1 - u0‖ ≠ 0 := fun hcc =>
    hne (sub_eq_zero.mp (norm_eq_zero.mp hcc)).symm
  have hle : inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0)
      ≤ ‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖ := by
    have h1 := norm_inner_le_norm (𝕜 := ℝ)
      (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0)
    simp only [Real.norm_eq_abs] at h1
    have h2 := le_abs_self (inner ℝ
      (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0))
    linarith
  have hk1p : 0 < ‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hk1)
  have hk2p : 0 < ‖u1 - u0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hk2)
  by_cases hcos : inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0)
      (u1 - u0) / (‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖) = 1
  · exfalso
    have hcs : inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0)
        = ‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖ := by
      field_simp at hcos
      exact hcos
    obtain horr | horr := p23_collinear_core u0 u1 (elV ul 2) (mxi V ul) hne
      (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1) hxmem hk1 hcs
    · -- mxi in the plane of {u0, u1, elV ul 2}
      obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
      subst hv
      have hv01 : v0 = u0 ∧ v1 = u1 := by
        have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
          (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
        rw [h1] at htr
        have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
        exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
      rw [hv01.1, hv01.2] at htr hnn horr
      have htr2 : setOfList (truncateSimplex 2 [u0, u1, v2, v3])
          = ({u0, u1, v2} : Set V3) := by
        rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 v2 v3).2]
        ext z
        simp [setOfList]
      have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
      rw [hE2] at horr
      exact hnn (measure_mono_null Set.inter_subset_left
        (p23_coplanar_affineSpan_null (p23_coplanar_triple u0 u1 v2)
          (p23_mcell3_sub_span htr2 (mem_affineSpan (k := ℝ) (by simp))
            (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp)) horr)))
    · -- elV ul 2 in the plane of {u0, u1, mxi}
      obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
      subst hv
      have hv01 : v0 = u0 ∧ v1 = u1 := by
        have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
          (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
        rw [h1] at htr
        have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
        exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
      rw [hv01.1, hv01.2] at htr hnn horr
      have htr2 : setOfList (truncateSimplex 2 [u0, u1, v2, v3])
          = ({u0, u1, v2} : Set V3) := by
        rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 v2 v3).2]
        ext z
        simp [setOfList]
      have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
      rw [hE2] at horr
      exact hnn (measure_mono_null Set.inter_subset_left
        (p23_coplanar_affineSpan_null
          (p23_coplanar_triple u0 u1 (mxi V [u0, u1, v2, v3]))
          (p23_mcell3_sub_span htr2 (mem_affineSpan (k := ℝ) (by simp))
            (mem_affineSpan (k := ℝ) (by simp)) horr
            (mem_affineSpan (k := ℝ) (by simp)))))
  · rw [div_lt_one (mul_pos hk1p hk2p)]
    have h2 := hcos
    field_simp at h2
    exact lt_of_le_of_ne hle (fun hcc => h2 (by rw [hcc]))

/-- B6 P4 (HL 2247-2605): the P4 cosine values are all `< 1` — same
collinearity killer with the fourth vertex in place of `mxi` and the
`mcell 4` body. -/
private theorem p23_f4_lt_one (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (hne : u0 ≠ u1) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 4 V ul ∩ Cst)) :
    inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0) /
      (‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖) < 1 := by
  have hu0K : u0 ∉ convexHull ℝ ({elV ul 2, elV ul 3} : Set V3) :=
    p23_u0_notIn_hull4 V u0 u1 hp hs hb htr Cst hnn
  have hxmem : smallestAngleLine (elV ul 2) (elV ul 3) u0 u1
      ∈ convexHull ℝ ({elV ul 2, elV ul 3} : Set V3) :=
    SMALLEST_ANGLE_IN_CONVEX_HULL (elV ul 2) (elV ul 3) u0 u1
      (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1) hne hu0K rfl
  have hxxne : smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 ≠ u0 := fun hcc =>
    hu0K (hcc ▸ hxmem)
  have hk1 : ‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ ≠ 0 := fun hcc =>
    hxxne (sub_eq_zero.mp (norm_eq_zero.mp hcc))
  have hk2 : ‖u1 - u0‖ ≠ 0 := fun hcc =>
    hne (sub_eq_zero.mp (norm_eq_zero.mp hcc)).symm
  have hk1p : 0 < ‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hk1)
  have hk2p : 0 < ‖u1 - u0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hk2)
  have hle : inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0)
      ≤ ‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖ := by
    have h1 := norm_inner_le_norm (𝕜 := ℝ)
      (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0)
    simp only [Real.norm_eq_abs] at h1
    have h2 := le_abs_self (inner ℝ
      (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0))
    linarith
  by_cases hcos : inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0)
      (u1 - u0) / (‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖) = 1
  · exfalso
    have hcs : inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0)
        = ‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖ := by
      field_simp at hcos
      exact hcos
    obtain horr | horr := p23_collinear_core u0 u1 (elV ul 2) (elV ul 3) hne
      (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1) hxmem hk1 hcs
    · -- elV ul 3 in the plane of {u0, u1, elV ul 2}
      obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
      subst hv
      have hv01 : v0 = u0 ∧ v1 = u1 := by
        have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
          (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
        rw [h1] at htr
        have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
        exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
      rw [hv01.1, hv01.2] at htr hnn horr
      have htr4 : setOfList [u0, u1, v2, v3] = ({u0, u1, v2, v3} : Set V3) := by
        ext z
        simp [setOfList]
      have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
      have hE3 : elV [u0, u1, v2, v3] 3 = v3 := rfl
      rw [hE2, hE3] at horr
      exact hnn (measure_mono_null Set.inter_subset_left
        (p23_coplanar_affineSpan_null (p23_coplanar_triple u0 u1 v2)
          (p23_mcell4_sub_span htr4 (mem_affineSpan (k := ℝ) (by simp))
            (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp)) horr)))
    · -- elV ul 2 in the plane of {u0, u1, elV ul 3}
      obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
      subst hv
      have hv01 : v0 = u0 ∧ v1 = u1 := by
        have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
          (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
        rw [h1] at htr
        have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
        exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
      rw [hv01.1, hv01.2] at htr hnn horr
      have htr4 : setOfList [u0, u1, v2, v3] = ({u0, u1, v2, v3} : Set V3) := by
        ext z
        simp [setOfList]
      have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
      have hE3 : elV [u0, u1, v2, v3] 3 = v3 := rfl
      rw [hE2, hE3] at horr
      exact hnn (measure_mono_null Set.inter_subset_left
        (p23_coplanar_affineSpan_null (p23_coplanar_triple u0 u1 v3)
          (p23_mcell4_sub_span htr4 (mem_affineSpan (k := ℝ) (by simp))
            (mem_affineSpan (k := ℝ) (by simp)) horr
            (mem_affineSpan (k := ℝ) (by simp)))))
  · rw [div_lt_one (mul_pos hk1p hk2p)]
    have h2 := hcos
    field_simp at h2
    exact lt_of_le_of_ne hle (fun hcc => h2 (by rw [hcc]))

/-- HL GRUTOTI.hl:161-2636: the volumetric core. Produces cone/annulus
parameters `c r d` (`c = max b (hl/√2)`, `r = min 1 (min r1 r2)`,
`d = max c (max d1 d2)` from the P1..P4 extremal arguments) with `D =
grutotiConicCap u0 u1 r d ⊆ C`, and the mcell cover (HL:2631-2636): every
Marchal cell meeting `D` in positive measure is a `k ≥ 2` cell over a
`barV V 3` list with `truncateSimplex 1 vl = [u0, u1]`.
GT-4 status (2026-09-30): B1-B4 are BANKED as the zero-sorry private chain
above (`p23_region_exists_delta` + `p23_region_exists_c`: HL:161-1143 —
bisector S1, interface S, midpoint XYOFCGX, critical radius δ, cone threshold
c ∈ (0,1) with `rconeGt u0 u1 c ⊆ affGeAlt {u0} S ∩ rconeGt u0 u1 (hl/√2)`).
HL's `S2 = S1 \ relative_interior S` is replaced by the explicit relative
neighbourhood `S' = S1 ∩ ball(p,d₀) ⊆ S` (B2's nearest-point selection);
this avoids the unported `AFF_DIM_VORONOI_LIST` and the intrinsicInterior
bridge entirely. REMAINING (the `sorry` below, HL:1144-2636): B5-B7 — the
rogers/mcell cover kit (B5, HL:1144-1537), the P1-P4 minima over the
truncation lists via smallest_angle_line (B6, HL:1538-2610; the PA15
SMALLEST_ANGLE_LINE kit is available), and the final assembly
`c = max b (hl/√2)`, `r = min 1 (min r1 r2)`, `d = max c (max d1 d2)`,
`D ⊆ C`, and the mcell cover (B7, HL:2611-2636).
CLOSED (2026-09-30 GT-4b): `c` from `p23_region_exists_c`; `r = 1/2` and
`d = max c (max d1 d2)` with `d1`/`d2` the sup of the P3/P4 cosine values
(`p23_f3_lt_one`/`p23_f4_lt_one`, `c` on the empty family), and the cover
transported from `p23_cover_C` along `D ⊆ C`.
DEVIATIONS from HL (recorded for the cell-volume lane, which consumes these
witnesses):
* `r = 1/2` replaces HL's `min 1 (min r1 r2)`: the Lean `grutotiConicCap`
  uses a CLOSED ball so `D ⊆ C` needs `r < 1` strictly, and the frozen region
  statement only asks `0 < r ≤ 1`. The r-side extremal data (`f1`/`f2` >
  0 via the facet-plane nullness route: `u0 ∉ affineSpan {u1, v2, mxi}` /
  `{u1, v2, v3}` nulls the whole cell) is NOT exported; the `grutoti_cell_vol`
  k = 3/4 radial argument must re-derive it. (GT-4 export wave 2026-10-08:
  now EXPORTED by the companion `p23_region_data` below, which re-runs this
  proof skeleton keeping the sups/minima the frozen `∃`-witnesses discard.)
* `d1`/`d2` here are genuine sups of the P3/P4 families (as in HL), so the
  d-side narrowness (`d ≥ d1`, `d ≥ d2`: the cone sits inside every k = 2/3
  cell wedge) IS available at these witnesses — but only through
  re-derivation: the frozen `grutoti_cell_vol` signature carries opaque
  `r d`, so its fill needs an SF to take the extremal data as hypotheses
  (or to restate along `grutoti_region`'s witnesses).
* `e` is unused (HL carries it for the caller bookkeeping only). -/
private theorem grutoti_region (V : Set V3) (u0 u1 : V3) (e : Set V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) (he : e = {u0, u1}) :
    ∃ c r d : ℝ, 0 < c ∧ c < 1 ∧ 0 < r ∧ r ≤ 1 ∧ 0 < d ∧ d < 1 ∧ c ≤ d ∧
      (∀ X : Set V3, X ∈ mcellSet V ∧ ¬nullSet (X ∩ grutotiConicCap u0 u1 r d) →
        ∃ k : ℕ, ∃ vl : List V3, 2 ≤ k ∧ barV V 3 vl ∧ X = mcell k V vl ∧
          truncateSimplex 1 vl = [u0, u1]) := by
  obtain ⟨c, hc0, hc1, hcW, hcHl⟩ := p23_region_exists_c V u0 u1 hs hp hu0 hu1 hne hhl
  have hbar := grutoti_barV V u0 u1 hs hp hu0 hu1 hne hhl
  set C := (Metric.ball u0 1 ∩ rconeGt u0 u1 c : Set V3) with hCdef
  -- B5: the mcell cover over C
  have hB5 : ∀ X : Set V3, X ∈ mcellSet V → ¬ nullSet (X ∩ C) →
      ∃ k vl, 2 ≤ k ∧ barV V 3 vl ∧ X = mcell k V vl ∧ truncateSimplex 1 vl = [u0, u1] :=
    p23_cover_C V u0 u1 hs hp hu0 hu1 hne c hcHl
      (p23_C_sub_rogers V u0 u1 hp hu0 hu1 hne hhl hs hbar c hcW)
  -- B6: the P3/P4 sups are strictly below 1
  set famP3 : Set (List V3) := {vl | barV V 3 vl ∧ ¬ nullSet (mcell 3 V vl ∩ C) ∧
    truncateSimplex 1 vl = [u0, u1]} with hfamP3def
  have hfamP3sub : famP3 ⊆ p23Fam V u0 u1 := by
    intro vl hvl
    obtain ⟨hb, _, htr⟩ := hvl
    exact ⟨hb, htr⟩
  have hfamP3fin : famP3.Finite := (p23_family_finite V u0 u1 hp hs).subset hfamP3sub
  set f3 : List V3 → ℝ := fun ul =>
    inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0) /
      (‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖) with hf3def
  have hf3lt : ∀ ul ∈ famP3, f3 ul < 1 := by
    intro ul hul
    obtain ⟨hb, hnn, htr⟩ := hul
    exact p23_f3_lt_one V u0 u1 hp hs hne hb htr C hnn
  obtain ⟨d1, hd1⟩ : ∃ d1 : ℝ, d1 < 1 := by
    by_cases hP3 : (f3 '' famP3) = ∅
    · exact ⟨c, hc1⟩
    · obtain ⟨m, hm, _hmax⟩ := Set.exists_max_image (f3 '' famP3) id
        (hfamP3fin.image _) (Set.nonempty_iff_ne_empty.mpr hP3)
      rcases hm with ⟨ul0, hul0, rfl⟩
      exact ⟨f3 ul0, hf3lt ul0 hul0⟩
  set famP4 : Set (List V3) := {vl | barV V 3 vl ∧ ¬ nullSet (mcell 4 V vl ∩ C) ∧
    truncateSimplex 1 vl = [u0, u1]} with hfamP4def
  have hfamP4sub : famP4 ⊆ p23Fam V u0 u1 := by
    intro vl hvl
    obtain ⟨hb, _, htr⟩ := hvl
    exact ⟨hb, htr⟩
  have hfamP4fin : famP4.Finite := (p23_family_finite V u0 u1 hp hs).subset hfamP4sub
  set f4 : List V3 → ℝ := fun ul =>
    inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0) /
      (‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖) with hf4def
  have hf4lt : ∀ ul ∈ famP4, f4 ul < 1 := by
    intro ul hul
    obtain ⟨hb, hnn, htr⟩ := hul
    exact p23_f4_lt_one V u0 u1 hp hs hne hb htr C hnn
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℝ, d2 < 1 := by
    by_cases hP4 : (f4 '' famP4) = ∅
    · exact ⟨c, hc1⟩
    · obtain ⟨m, hm, _hmax⟩ := Set.exists_max_image (f4 '' famP4) id
        (hfamP4fin.image _) (Set.nonempty_iff_ne_empty.mpr hP4)
      rcases hm with ⟨ul0, hul0, rfl⟩
      exact ⟨f4 ul0, hf4lt ul0 hul0⟩
  -- B7: assemble
  refine ⟨c, 1 / 2, max c (max d1 d2), hc0, hc1, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact hc0.trans_le (le_max_left _ _)
  · exact max_lt hc1 (max_lt hd1 hd2)
  · exact le_max_left _ _
  · rintro X ⟨hX, hn⟩
    have hr1' : (1 : ℝ) / 2 < 1 := by norm_num
    have hDC : grutotiConicCap u0 u1 (1 / 2) (max c (max d1 d2)) ⊆ C := by
      rw [grutotiConicCap, hCdef]
      intro z hz
      obtain ⟨hzball, hzr⟩ := hz
      refine ⟨?_, grutoti_rconeGt_subset u0 u1 c (max c (max d1 d2)) (le_max_left _ _) hzr⟩
      exact Metric.mem_ball.mp (Metric.closedBall_subset_ball hr1' hzball)
    exact hB5 X hX (fun h0 => hn (measure_mono_null
      (fun z hz => ⟨hz.1, hDC hz.2⟩ : X ∩ grutotiConicCap u0 u1 (1 / 2)
        (max c (max d1 d2)) ⊆ X ∩ C) h0))

/-! ## GT-4 wave: the `grutoti_region` B5-B7 extreme-data export kit
(2026-10-08; feeds the SF 项 28 premises of `grutoti_cell_vol`) -/

/-- GT-4 (P3/P4 cone route): `rconeGt` membership read as a strict cosine
bound — the HL `rcone_gt` definition unfolded, `dist` rewritten to `norm`
and `⬝ᵥ` bridged to `inner ℝ` via `inner_eq_dot`. -/
private theorem p23_rconeGt_cos_lt {u0 u1 z : V3} {d : ℝ} (hne : u0 ≠ u1)
    (hmem : z ∈ rconeGt u0 u1 d) :
    d < inner ℝ (z - u0) (u1 - u0) / (‖z - u0‖ * ‖u1 - u0‖) := by
  simp only [rconeGt, Set.mem_setOf_eq] at hmem
  rw [← inner_eq_dot] at hmem
  have hdx : dist z u0 = ‖z - u0‖ := dist_eq_norm z u0
  have hdu : dist u1 u0 = ‖u1 - u0‖ := dist_eq_norm u1 u0
  rw [hdx, hdu] at hmem
  have hz0 : z ≠ u0 := by
    intro hcc
    rw [hcc] at hmem
    simp at hmem
  have hza : (0 : ℝ) < ‖z - u0‖ :=
    norm_pos_iff.mpr (fun hcc => hz0 (sub_eq_zero.mp hcc))
  have hdb : (0 : ℝ) < ‖u1 - u0‖ :=
    norm_pos_iff.mpr (fun hcc => hne (sub_eq_zero.mp hcc).symm)
  refine (lt_div_iff₀ (mul_pos hza hdb)).mpr ?_
  calc d * (‖z - u0‖ * ‖u1 - u0‖) = ‖z - u0‖ * ‖u1 - u0‖ * d := by ring
    _ < inner ℝ (z - u0) (u1 - u0) := hmem

/-- GT-4 (B6 P1 core, facet-plane route): `u0` is not in the far-face plane
`{u1, elV ul 2, mxi V ul}` of a `k = 3` cell meeting the gauge set in
positive measure — else the whole cell sits in that plane and is null (same
killer as `p23_u0_notIn_hull3`, with the plane membership taken directly). -/
private theorem p23_u0_notIn_plane3 (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 3 V ul ∩ Cst)) :
    u0 ∉ (affineSpan ℝ ({u1, elV ul 2, mxi V ul} : Set V3)) := by
  intro hu0
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
  subst hv
  have hv01 : v0 = u0 ∧ v1 = u1 := by
    have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
      (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
    rw [h1] at htr
    have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
    exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
  rw [hv01.1, hv01.2] at htr hnn hu0
  have htr2 : setOfList (truncateSimplex 2 [u0, u1, v2, v3])
      = ({u0, u1, v2} : Set V3) := by
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 v2 v3).2]
    ext z
    simp [setOfList]
  have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
  rw [hE2] at hu0
  have hnull : nullSet (mcell 3 V [u0, u1, v2, v3]) :=
    p23_coplanar_affineSpan_null (p23_coplanar_triple u1 v2 (mxi V [u0, u1, v2, v3]))
      (p23_mcell3_sub_span htr2 hu0 (mem_affineSpan (k := ℝ) (by simp))
        (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp)))
  exact hnn (measure_mono_null Set.inter_subset_left hnull)

/-- GT-4 (B6 P2 core, facet-plane route): same killer for the fourth vertex. -/
private theorem p23_u0_notIn_plane4 (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 4 V ul ∩ Cst)) :
    u0 ∉ (affineSpan ℝ ({u1, elV ul 2, elV ul 3} : Set V3)) := by
  intro hu0
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
  subst hv
  have hv01 : v0 = u0 ∧ v1 = u1 := by
    have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
      (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
    rw [h1] at htr
    have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
    exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
  rw [hv01.1, hv01.2] at htr hnn hu0
  have htr4 : setOfList [u0, u1, v2, v3] = ({u0, u1, v2, v3} : Set V3) := by
    ext z
    simp [setOfList]
  have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
  have hE3 : elV [u0, u1, v2, v3] 3 = v3 := rfl
  rw [hE2, hE3] at hu0
  have hnull : nullSet (mcell 4 V [u0, u1, v2, v3]) :=
    p23_coplanar_affineSpan_null (p23_coplanar_triple u1 v2 v3)
      (p23_mcell4_sub_span htr4 hu0 (mem_affineSpan (k := ℝ) (by simp))
        (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp)))
  exact hnn (measure_mono_null Set.inter_subset_left hnull)

/-- GT-4 (B6 P1 ε-data): the far-face plane of a non-null `k = 3` cell keeps
a strictly positive distance from `u0` — the plane is closed (its direction
is a finite-dimensional, hence closed, submodule) and misses `u0`
(`p23_u0_notIn_plane3`). -/
private theorem p23_plane_dist_pos3 (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 3 V ul ∩ Cst)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ (affineSpan ℝ ({u1, elV ul 2, mxi V ul} : Set V3)),
      ε ≤ dist u0 z := by
  have hclosed : IsClosed (affineSpan ℝ ({u1, elV ul 2, mxi V ul} : Set V3) : Set V3) := by
    refine (AffineSubspace.isClosed_direction_iff
      (affineSpan ℝ ({u1, elV ul 2, mxi V ul} : Set V3))).mp ?_
    exact Submodule.closed_of_finiteDimensional (𝕜 := ℝ) _
  have hnotin := p23_u0_notIn_plane3 V u0 u1 hp hs hb htr Cst hnn
  by_contra h0
  push_neg at h0
  have hmem : u0 ∈ closure (affineSpan ℝ ({u1, elV ul 2, mxi V ul} : Set V3)) :=
    Metric.mem_closure_iff.mpr h0
  rw [hclosed.closure_eq] at hmem
  exact hnotin hmem

/-- GT-4 (B6 P2 ε-data): same for the `k = 4` far-face plane. -/
private theorem p23_plane_dist_pos4 (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 4 V ul ∩ Cst)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ (affineSpan ℝ ({u1, elV ul 2, elV ul 3} : Set V3)),
      ε ≤ dist u0 z := by
  have hclosed : IsClosed (affineSpan ℝ ({u1, elV ul 2, elV ul 3} : Set V3) : Set V3) := by
    refine (AffineSubspace.isClosed_direction_iff
      (affineSpan ℝ ({u1, elV ul 2, elV ul 3} : Set V3))).mp ?_
    exact Submodule.closed_of_finiteDimensional (𝕜 := ℝ) _
  have hnotin := p23_u0_notIn_plane4 V u0 u1 hp hs hb htr Cst hnn
  by_contra h0
  push_neg at h0
  have hmem : u0 ∈ closure (affineSpan ℝ ({u1, elV ul 2, elV ul 3} : Set V3)) :=
    Metric.mem_closure_iff.mpr h0
  rw [hclosed.closure_eq] at hmem
  exact hnotin hmem

/-- GT-4 (B6 P3/P4 cone core): a point of the cut-segment hull keeps a cosine
bounded by the smallest-angle cosine (`SMALLEST_ANGLE_LINE_PROPERTY`, bridged
from the `⬝ᵥ`/`norm` form to the `inner ℝ`/`‖·‖` form via `inner_eq_dot`). -/
private theorem p23_smallestAngle_cos {u0 u1 a b z : V3} (hne : u0 ≠ u1)
    (hu0K : u0 ∉ convexHull ℝ ({a, b} : Set V3))
    (hzmem : z ∈ convexHull ℝ ({a, b} : Set V3)) :
    inner ℝ (z - u0) (u1 - u0) / (‖z - u0‖ * ‖u1 - u0‖) ≤
      inner ℝ (smallestAngleLine a b u0 u1 - u0) (u1 - u0) /
        (‖smallestAngleLine a b u0 u1 - u0‖ * ‖u1 - u0‖) := by
  have hprop := SMALLEST_ANGLE_LINE_PROPERTY a b u0 u1
    (smallestAngleLine a b u0 u1) z hne hu0K rfl hzmem
  rw [inner_eq_dot, inner_eq_dot]
  exact hprop

/-- GT-4 (GRUTOTI capstone 波): the B5-B7 extreme-data export companion of
`grutoti_region` — same hypotheses, strengthened conclusion. Besides the
frozen region bounds and the mcell cover, the parameters `c r d` carry the
SF 项 28 premise shapes consumed by `grutoti_cell_vol`: `hw1 :
hl [u0,u1]/√2 ≤ d` (the B4 cone inclusion folded into `d`'s maximum, so no
inversion of `p23_region_exists_c`'s inclusion is needed), the P1/P2 face
data `r ≤ dist u0 z` on the far-face planes (per-family minima of the
`p23_plane_dist_pos3/4` distances; the consumer's D-gate transports to the
C-gated families along `D ⊆ C`), and the P3/P4 cone data (cut-segment hulls
avoid `rconeGt u0 u1 d` — the `f3`/`f4` suprema that the frozen proof
discards with its `∃`-witnesses are kept here, chained through
`SMALLEST_ANGLE_LINE_PROPERTY` via `p23_smallestAngle_cos` and
`p23_rconeGt_cos_lt`). `hp : Packing V` is a caller premise of
`grutoti_cell_vol` carried here already. DEVIATIONS from the frozen
`grutoti_region` proof body (all inside the frozen statement's slack):
`d = max c (max (hl/√2) (max d1 d2))` and `r = min (1/2) (min r3 r4)` —
both keep every frozen bound (`0 < r ≤ 1`, `0 < d < 1`, `c ≤ d`, `D ⊆ C`,
mcell cover). -/
private theorem p23_region_data (V : Set V3) (u0 u1 : V3) (e : Set V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) (he : e = {u0, u1}) :
    ∃ c r d : ℝ, 0 < c ∧ c < 1 ∧ 0 < r ∧ r ≤ 1 ∧ 0 < d ∧ d < 1 ∧ c ≤ d ∧
      (∀ X : Set V3, X ∈ mcellSet V ∧ ¬nullSet (X ∩ grutotiConicCap u0 u1 r d) →
        ∃ k : ℕ, ∃ vl : List V3, 2 ≤ k ∧ barV V 3 vl ∧ X = mcell k V vl ∧
          truncateSimplex 1 vl = [u0, u1]) ∧
      hl [u0, u1] / Real.sqrt 2 ≤ d ∧
      (∀ vl : List V3, barV V 3 vl → truncateSimplex 1 vl = [u0, u1] →
        ¬nullSet (mcell 3 V vl ∩ grutotiConicCap u0 u1 r d) →
        (∀ z ∈ (affineSpan ℝ {u1, elV vl 2, mxi V vl} : Set V3), r ≤ dist u0 z) ∧
        ∀ z ∈ convexHull ℝ ({elV vl 2, mxi V vl} : Set V3), z ∉ rconeGt u0 u1 d) ∧
      (∀ vl : List V3, barV V 3 vl → truncateSimplex 1 vl = [u0, u1] →
        ¬nullSet (mcell 4 V vl ∩ grutotiConicCap u0 u1 r d) →
        (∀ z ∈ (affineSpan ℝ {u1, elV vl 2, elV vl 3} : Set V3), r ≤ dist u0 z) ∧
        ∀ z ∈ convexHull ℝ ({elV vl 2, elV vl 3} : Set V3), z ∉ rconeGt u0 u1 d) := by
  obtain ⟨c, hc0, hc1, hcW, hcHl⟩ := p23_region_exists_c V u0 u1 hs hp hu0 hu1 hne hhl
  have hbar := grutoti_barV V u0 u1 hs hp hu0 hu1 hne hhl
  set C := (Metric.ball u0 1 ∩ rconeGt u0 u1 c : Set V3) with hCdef
  -- B5: the mcell cover over C (verbatim from grutoti_region)
  have hB5 : ∀ X : Set V3, X ∈ mcellSet V → ¬ nullSet (X ∩ C) →
      ∃ k vl, 2 ≤ k ∧ barV V 3 vl ∧ X = mcell k V vl ∧ truncateSimplex 1 vl = [u0, u1] :=
    p23_cover_C V u0 u1 hs hp hu0 hu1 hne c hcHl
      (p23_C_sub_rogers V u0 u1 hp hu0 hu1 hne hhl hs hbar c hcW)
  -- B6: the C-gated P3/P4 families; the suprema are KEPT (the frozen proof
  -- discards them with its ∃-witnesses)
  set famP3 : Set (List V3) := {vl | barV V 3 vl ∧ ¬ nullSet (mcell 3 V vl ∩ C) ∧
    truncateSimplex 1 vl = [u0, u1]} with hfamP3def
  have hfamP3sub : famP3 ⊆ p23Fam V u0 u1 := by
    intro vl hvl
    obtain ⟨hb, _, htr⟩ := hvl
    exact ⟨hb, htr⟩
  have hfamP3fin : famP3.Finite := (p23_family_finite V u0 u1 hp hs).subset hfamP3sub
  set f3 : List V3 → ℝ := fun ul =>
    inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0) /
      (‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖) with hf3def
  have hf3lt : ∀ ul ∈ famP3, f3 ul < 1 := by
    intro ul hul
    obtain ⟨hb, hnn, htr⟩ := hul
    exact p23_f3_lt_one V u0 u1 hp hs hne hb htr C hnn
  obtain ⟨d1, hd1lt, hd1ub⟩ : ∃ d1 : ℝ, d1 < 1 ∧ ∀ ul ∈ famP3, f3 ul ≤ d1 := by
    by_cases hP3 : (f3 '' famP3) = ∅
    · refine ⟨c, hc1, ?_⟩
      rintro ul hul
      exact absurd (Set.mem_image_of_mem f3 hul) (by rw [hP3]; simp)
    · obtain ⟨m, hm, hmax⟩ := Set.exists_max_image (f3 '' famP3) id
        (hfamP3fin.image _) (Set.nonempty_iff_ne_empty.mpr hP3)
      rcases hm with ⟨ul0, hul0, rfl⟩
      exact ⟨f3 ul0, hf3lt ul0 hul0,
        fun ul hul => hmax (f3 ul) (Set.mem_image_of_mem f3 hul)⟩
  set famP4 : Set (List V3) := {vl | barV V 3 vl ∧ ¬ nullSet (mcell 4 V vl ∩ C) ∧
    truncateSimplex 1 vl = [u0, u1]} with hfamP4def
  have hfamP4sub : famP4 ⊆ p23Fam V u0 u1 := by
    intro vl hvl
    obtain ⟨hb, _, htr⟩ := hvl
    exact ⟨hb, htr⟩
  have hfamP4fin : famP4.Finite := (p23_family_finite V u0 u1 hp hs).subset hfamP4sub
  set f4 : List V3 → ℝ := fun ul =>
    inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0) /
      (‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖) with hf4def
  have hf4lt : ∀ ul ∈ famP4, f4 ul < 1 := by
    intro ul hul
    obtain ⟨hb, hnn, htr⟩ := hul
    exact p23_f4_lt_one V u0 u1 hp hs hne hb htr C hnn
  obtain ⟨d2, hd2lt, hd2ub⟩ : ∃ d2 : ℝ, d2 < 1 ∧ ∀ ul ∈ famP4, f4 ul ≤ d2 := by
    by_cases hP4 : (f4 '' famP4) = ∅
    · refine ⟨c, hc1, ?_⟩
      rintro ul hul
      exact absurd (Set.mem_image_of_mem f4 hul) (by rw [hP4]; simp)
    · obtain ⟨m, hm, hmax⟩ := Set.exists_max_image (f4 '' famP4) id
        (hfamP4fin.image _) (Set.nonempty_iff_ne_empty.mpr hP4)
      rcases hm with ⟨ul0, hul0, rfl⟩
      exact ⟨f4 ul0, hf4lt ul0 hul0,
        fun ul hul => hmax (f4 ul) (Set.mem_image_of_mem f4 hul)⟩
  -- B6 P1/P2: the per-family plane-distance minima
  have hfamP3eps : ∀ ul : List V3, ∃ ε : ℝ, ul ∈ famP3 →
      0 < ε ∧ ∀ z ∈ (affineSpan ℝ ({u1, elV ul 2, mxi V ul} : Set V3)), ε ≤ dist u0 z := by
    intro ul
    by_cases hmem : ul ∈ famP3
    · obtain ⟨hb, hnn, htr⟩ := hmem
      obtain ⟨ε, hε0, hεle⟩ := p23_plane_dist_pos3 V u0 u1 hp hs hb htr C hnn
      exact ⟨ε, fun _ => ⟨hε0, hεle⟩⟩
    · exact ⟨1 / 2, fun hmem' => absurd hmem' hmem⟩
  obtain ⟨r3, hr3pos, hr3le⟩ : ∃ r3 : ℝ, 0 < r3 ∧
      ∀ ul ∈ famP3, ∀ z ∈ (affineSpan ℝ ({u1, elV ul 2, mxi V ul} : Set V3)),
        r3 ≤ dist u0 z := by
    by_cases hne3 : famP3 = ∅
    · refine ⟨1 / 2, by norm_num, ?_⟩
      intro ul hul z hz
      exact absurd hul (by rw [hne3]; simp)
    · choose ε hε using hfamP3eps
      obtain ⟨ul0, hul0⟩ := Set.nonempty_iff_ne_empty.mpr hne3
      obtain ⟨m, hm, hmin⟩ := Set.exists_min_image (ε '' famP3) id
        (hfamP3fin.image _) ⟨ε ul0, ul0, hul0, rfl⟩
      rcases hm with ⟨ul1, hul1, rfl⟩
      exact ⟨ε ul1, (hε ul1 hul1).1, fun ul hul z hz =>
        le_trans (hmin (ε ul) (Set.mem_image_of_mem ε hul)) ((hε ul hul).2 z hz)⟩
  have hfamP4eps : ∀ ul : List V3, ∃ ε : ℝ, ul ∈ famP4 →
      0 < ε ∧ ∀ z ∈ (affineSpan ℝ ({u1, elV ul 2, elV ul 3} : Set V3)), ε ≤ dist u0 z := by
    intro ul
    by_cases hmem : ul ∈ famP4
    · obtain ⟨hb, hnn, htr⟩ := hmem
      obtain ⟨ε, hε0, hεle⟩ := p23_plane_dist_pos4 V u0 u1 hp hs hb htr C hnn
      exact ⟨ε, fun _ => ⟨hε0, hεle⟩⟩
    · exact ⟨1 / 2, fun hmem' => absurd hmem' hmem⟩
  obtain ⟨r4, hr4pos, hr4le⟩ : ∃ r4 : ℝ, 0 < r4 ∧
      ∀ ul ∈ famP4, ∀ z ∈ (affineSpan ℝ ({u1, elV ul 2, elV ul 3} : Set V3)),
        r4 ≤ dist u0 z := by
    by_cases hne4 : famP4 = ∅
    · refine ⟨1 / 2, by norm_num, ?_⟩
      intro ul hul z hz
      exact absurd hul (by rw [hne4]; simp)
    · choose ε hε using hfamP4eps
      obtain ⟨ul0, hul0⟩ := Set.nonempty_iff_ne_empty.mpr hne4
      obtain ⟨m, hm, hmin⟩ := Set.exists_min_image (ε '' famP4) id
        (hfamP4fin.image _) ⟨ε ul0, ul0, hul0, rfl⟩
      rcases hm with ⟨ul1, hul1, rfl⟩
      exact ⟨ε ul1, (hε ul1 hul1).1, fun ul hul z hz =>
        le_trans (hmin (ε ul) (Set.mem_image_of_mem ε hul)) ((hε ul hul).2 z hz)⟩
  -- B7: assemble (DEVIATIONS: d folds in hl/√2; r is the (1/2, r3, r4) minimum)
  set d := max c (max (hl [u0, u1] / Real.sqrt 2) (max d1 d2)) with hddef
  have hdd1 : d1 ≤ d :=
    le_trans (le_max_left d1 d2) (le_trans (le_max_right (hl [u0, u1] / Real.sqrt 2)
      (max d1 d2)) (le_max_right c (max (hl [u0, u1] / Real.sqrt 2) (max d1 d2))))
  have hdd2 : d2 ≤ d :=
    le_trans (le_max_right d1 d2) (le_trans (le_max_right (hl [u0, u1] / Real.sqrt 2)
      (max d1 d2)) (le_max_right c (max (hl [u0, u1] / Real.sqrt 2) (max d1 d2))))
  have hhl1 : hl [u0, u1] / Real.sqrt 2 < 1 :=
    (div_lt_one (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr hhl
  have hdlt1 : d < 1 := max_lt hc1 (max_lt hhl1 (max_lt hd1lt hd2lt))
  have hrLt1 : min (1 / 2) (min r3 r4) < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hDC : grutotiConicCap u0 u1 (min (1 / 2) (min r3 r4)) d ⊆ C := by
    rw [grutotiConicCap, hCdef]
    intro z hz
    obtain ⟨hzball, hzr⟩ := hz
    refine ⟨?_, grutoti_rconeGt_subset u0 u1 c d (le_max_left _ _) hzr⟩
    exact Metric.mem_ball.mp (Metric.closedBall_subset_ball hrLt1 hzball)
  have hgateC : ∀ (k : ℕ) (vl : List V3),
      ¬ nullSet (mcell k V vl ∩ grutotiConicCap u0 u1 (min (1 / 2) (min r3 r4)) d) →
      ¬ nullSet (mcell k V vl ∩ C) := by
    intro k vl hnnD h0
    exact hnnD (measure_mono_null
      (show mcell k V vl ∩ grutotiConicCap u0 u1 (min (1 / 2) (min r3 r4)) d ⊆
        mcell k V vl ∩ C from fun z hz => ⟨hz.1, hDC hz.2⟩) h0)
  refine ⟨c, min (1 / 2) (min r3 r4), d, hc0, hc1,
    lt_min (by norm_num : (0 : ℝ) < 1 / 2) (lt_min hr3pos hr4pos),
    le_trans (min_le_left _ _) (by norm_num : (1 : ℝ) / 2 ≤ 1),
    hc0.trans_le (le_max_left _ _), hdlt1, le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · -- the mcell cover, transported along D ⊆ C (verbatim from grutoti_region)
    rintro X ⟨hX, hn⟩
    exact hB5 X hX (fun h0 => hn (measure_mono_null
      (fun z hz => ⟨hz.1, hDC hz.2⟩ : X ∩ grutotiConicCap u0 u1
        (min (1 / 2) (min r3 r4)) d ⊆ X ∩ C) h0))
  · -- hw1 (SF 项 28): hl/√2 enters d's maximum
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · -- hw3 (SF 项 28): face data from the r3-minimum, cone data from the
    -- f3-supremum + SMALLEST_ANGLE_LINE_PROPERTY
    intro vl hb htr hnnD
    refine ⟨fun z hz => le_trans (min_le_right (1 / 2) (min r3 r4))
      (le_trans (min_le_left r3 r4)
        (hr3le vl ⟨hb, hgateC 3 vl hnnD, htr⟩ z hz)), ?_⟩
    intro z hzhull hzrcone
    have hu0K : u0 ∉ convexHull ℝ ({elV vl 2, mxi V vl} : Set V3) :=
      p23_u0_notIn_hull3 V u0 u1 hp hs hb htr
        (grutotiConicCap u0 u1 (min (1 / 2) (min r3 r4)) d) hnnD
    have hprop := p23_smallestAngle_cos hne hu0K hzhull
    have hcos := p23_rconeGt_cos_lt hne hzrcone
    have hf3le : inner ℝ (smallestAngleLine (elV vl 2) (mxi V vl) u0 u1 - u0)
        (u1 - u0) / (‖smallestAngleLine (elV vl 2) (mxi V vl) u0 u1 - u0‖
          * ‖u1 - u0‖) ≤ d := le_trans (hd1ub vl ⟨hb, hgateC 3 vl hnnD, htr⟩) hdd1
    exact absurd (le_trans hprop hf3le) (not_le.mpr hcos)
  · -- hw4 (SF 项 28): same with the k = 4 family
    intro vl hb htr hnnD
    refine ⟨fun z hz => le_trans (min_le_right (1 / 2) (min r3 r4))
      (le_trans (min_le_right r3 r4)
        (hr4le vl ⟨hb, hgateC 4 vl hnnD, htr⟩ z hz)), ?_⟩
    intro z hzhull hzrcone
    have hu0K : u0 ∉ convexHull ℝ ({elV vl 2, elV vl 3} : Set V3) :=
      p23_u0_notIn_hull4 V u0 u1 hp hs hb htr
        (grutotiConicCap u0 u1 (min (1 / 2) (min r3 r4)) d) hnnD
    have hprop := p23_smallestAngle_cos hne hu0K hzhull
    have hcos := p23_rconeGt_cos_lt hne hzrcone
    have hf4le : inner ℝ (smallestAngleLine (elV vl 2) (elV vl 3) u0 u1 - u0)
        (u1 - u0) / (‖smallestAngleLine (elV vl 2) (elV vl 3) u0 u1 - u0‖
          * ‖u1 - u0‖) ≤ d := le_trans (hd2ub vl ⟨hb, hgateC 4 vl hnnD, htr⟩) hdd2
    exact absurd (le_trans hprop hf4le) (not_le.mpr hcos)
/-! ## GT-3e lane: SF 项 28/29 arm kit (2026-10-08) -/

/-- SF 项 28/29 (GT-3e): `truncateSimplex 1` of a list that begins with the
edge `[u0,u1]` is the edge itself. The `cellParamsD` witnesses carry
`initialSublist [u0,u1] ul` (epsilon predicate) while the SF-28 narrowness
premises and the region block are phrased with
`truncateSimplex 1 vl = [u0,u1]`; this bridges the two shapes (prefix
uniqueness at equal length, via `p23_trunc_init_len`). -/
private theorem p23_trunc1_of_init {u0 u1 : V3} {zl : List V3}
    (h : initialSublist [u0, u1] zl) : truncateSimplex 1 zl = [u0, u1] := by
  obtain ⟨yl, hy⟩ := h
  have hlen : 1 + 1 ≤ zl.length := by rw [hy]; simp
  have htr := p23_trunc_init_len 1 zl hlen
  obtain ⟨y1, hy1⟩ := htr.1
  have e1 : (truncateSimplex 1 zl ++ y1).take 2 = truncateSimplex 1 zl := by
    rw [List.take_append_of_le_length (by omega), show (2:ℕ) = (truncateSimplex 1 zl).length from by omega,
      List.take_length]
  have e2 : ([u0, u1] ++ yl).take 2 = [u0, u1] := by
    rw [List.take_append_of_le_length (by norm_num), show (2:ℕ) = [u0, u1].length from rfl,
      List.take_length]
  have h1 : zl.take 2 = truncateSimplex 1 zl := by
    conv_lhs => rw [hy1]
    exact e1
  have h2 : zl.take 2 = [u0, u1] := by
    conv_lhs => rw [hy]
    exact e2
  rw [← h1, h2]

/-- GT-3e: `affGe {u0,u1} {w}` sits in the plane `affineSpan ℝ {u0,u1,w}`
(the HL `AFF_GE_SUBSET_AFFINE_HULL` pattern, one concrete instance; the
Affsign witness re-enters as a direction sum around `u0`). -/
private theorem p23_mem_affineSpan_of_affGe {u0 u1 w v : V3}
    (hv : v ∈ affGe {u0, u1} {w}) : v ∈ (affineSpan ℝ ({u0, u1, w} : Set V3)) := by
  obtain ⟨f, hfin, hsum, -, hone⟩ := hv
  have hS : ∀ z ∈ hfin.toFinset, z ∈ ({u0, u1, w} : Set V3) := by
    intro z hz
    rcases hfin.mem_toFinset.mp hz with hz' | hz'
    · rcases (Set.mem_insert_iff).mp hz' with h1 | h1
      · simp only [Set.mem_insert_iff]; exact Or.inl h1
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr (Or.inl h1)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr (Or.inr hz')
  have h0 : u0 ∈ (affineSpan ℝ ({u0, u1, w} : Set V3)) := mem_affineSpan (k := ℝ) (by simp)
  have hd : ∀ z ∈ ({u0, u1, w} : Set V3), (z - u0 : V3) ∈
      (affineSpan ℝ ({u0, u1, w} : Set V3)).direction :=
    fun z hz => AffineSubspace.vsub_mem_direction (mem_affineSpan (k := ℝ) hz) h0
  have key0 : ∑ z ∈ hfin.toFinset, f z • (z - u0)
      = ∑ z ∈ hfin.toFinset, (f z • z - f z • u0) := by
    exact Finset.sum_congr rfl fun z _ => smul_sub (f z) z u0
  have key : v - u0 = ∑ z ∈ hfin.toFinset, f z • (z - u0) := by
    calc v - u0 = (∑ z ∈ hfin.toFinset, f z • z) - (∑ z ∈ hfin.toFinset, f z) • u0 := by
          rw [← hsum, hone, one_smul]
        _ = ∑ z ∈ hfin.toFinset, (f z • z - f z • u0) := by
          rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        _ = ∑ z ∈ hfin.toFinset, f z • (z - u0) := by
          exact Finset.sum_congr rfl fun z _ => (smul_sub (f z) z u0).symm
  have hv2 : ((∑ z ∈ hfin.toFinset, f z • (z - u0)) +ᵥ u0) ∈
      (affineSpan ℝ ({u0, u1, w} : Set V3)) :=
    AffineSubspace.vadd_mem_of_mem_direction
      (Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (hd z (hS z hz))) h0
  rw [show ((∑ z ∈ hfin.toFinset, f z • (z - u0)) +ᵥ u0) = v from by
    rw [vadd_eq_add, add_comm, ← key]; simp] at hv2
  exact hv2

/-- GT-3e: the polar-coordinate rigidity behind the wedge helper — with both
`w1, w2` off the axis, `azim u0 u1 w1 w2 ∈ {0, π}` forces `w2` into the plane
`affineSpan ℝ {u0,u1,w1}` (same/opposite azimuthal ray). Read off
`azim_master`'s frame representation with `cos/sin (ψ+θ) = ±(cos ψ, sin ψ)`. -/
private theorem p23_mem_plane_of_azim_eq {u0 u1 w1 w2 : V3} (hne : u0 ≠ u1)
    (hc1 : ¬ Collinear3 u0 u1 w1) (hc2 : ¬ Collinear3 u0 u1 w2)
    (hz : azim u0 u1 w1 w2 = 0 ∨ azim u0 u1 w1 w2 = Real.pi) :
    w2 ∈ (affineSpan ℝ ({u0, u1, w1} : Set V3)) := by
  obtain ⟨f1, f2, f3, hf, halign⟩ :=
    exists_on3_eq_smul (u1 - u0) (sub_ne_zero_of_ne (Ne.symm hne))
  have hax : (u1 - u0 : V3) = dist u1 u0 • f3 := by rw [dist_eq_norm]; exact halign
  obtain ⟨h1c, h2c, hframe⟩ := (azim_master u0 u1 w1 w2).2.2
  obtain ⟨psi, r1, r2, h1v, h2v, hr1p, hr2p⟩ := hframe f1 f2 f3 hf hax (Ne.symm hne)
  have hr1p' : (0:ℝ) < r1 := hr1p hc1
  have hr1ne : r1 ≠ 0 := ne_of_gt hr1p'
  rcases hz with hz | hz
  · rw [hz, add_zero] at h2v
    have h3 : w2 - u0 = (h2c - (r2 / r1) * h1c) • (u1 - u0)
        + (r2 / r1) • (w1 - u0) := by
      rw [h2v, h1v, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
        ← mul_assoc, ← mul_assoc, show (r2 / r1) * r1 = r2 from by field_simp [hr1ne]]
      module
    have hkey : w2 = u0 + (h2c - (r2 / r1) * h1c) • (u1 - u0)
        + (r2 / r1) • (w1 - u0) := by
      rw [show w2 = w2 - u0 + u0 from (sub_add_cancel w2 u0).symm, h3]
      abel
    exact p23_mem_affineSpan_triple u0 u1 w1 w2 (h2c - (r2 / r1) * h1c) (r2 / r1) hkey
  · rw [hz, Real.cos_add_pi, Real.sin_add_pi] at h2v
    have h3 : w2 - u0 = (h2c + (r2 / r1) * h1c) • (u1 - u0)
        + (-(r2 / r1)) • (w1 - u0) := by
      rw [h2v, h1v, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
        ← mul_assoc, ← mul_assoc, show (-(r2 / r1)) * r1 = -r2 from by field_simp [hr1ne]]
      module
    have hkey : w2 = u0 + (h2c + (r2 / r1) * h1c) • (u1 - u0)
        + (-(r2 / r1)) • (w1 - u0) := by
      rw [show w2 = w2 - u0 + u0 from (sub_add_cancel w2 u0).symm, h3]
      abel
    exact p23_mem_affineSpan_triple u0 u1 w1 w2 (h2c + (r2 / r1) * h1c) (-(r2 / r1)) hkey

/-- GT-3e: `affGt` over a two-point base is symmetric in the base pair
(the `{w1, w2}` / `{w2, w1}` sets coincide; the Affsign finiteness and sum
witnesses transport along the set equality). -/
private theorem p23_affGt_pair_symm {u0 u1 w1 w2 v : V3}
    (hv : v ∈ affGt {u0, u1} {w1, w2}) : v ∈ affGt {u0, u1} {w2, w1} := by
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := hv
  have hset : (({u0, u1} : Set V3) ∪ {w2, w1} : Set V3)
      = (({u0, u1} : Set V3) ∪ {w1, w2} : Set V3) := by
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hfin2 : (({u0, u1} : Set V3) ∪ {w2, w1}).Finite := by
    rw [hset]; exact hfin
  have hFeq : hfin2.toFinset = hfin.toFinset := Finset.coe_injective
    (by rw [Set.Finite.coe_toFinset, Set.Finite.coe_toFinset hfin, hset])
  refine ⟨f, hfin2, ?_, ?_, ?_⟩
  · rw [hFeq]; exact hsum
  · intro w hw
    rcases (Set.mem_insert_iff).mp hw with h | h
    · rw [h]; exact hpos w2 (by simp)
    · rw [Set.mem_singleton_iff.mp h]; exact hpos w1 (by simp)
  · rw [hFeq]; exact hone

/-- GT-3e: `affGt ⊆ affGe` (same Affsign witness; only the sign condition
weakens). -/
private theorem p23_affGt_sub_affGe (s t : Set V3) : affGt s t ⊆ affGe s t := by
  intro x hx
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := hx
  exact ⟨f, hfin, hsum, fun w hw => le_of_lt (hpos w hw), hone⟩

/-- GT-3e: the `affGe`-face split — a fan point whose two base coefficients
are not BOTH strictly positive drops into one of the two one-base fans (the
set-level content of HL's `AFF_GE_AFF_GT_DECOMP` applications,
GRUTOTI.hl:3110-3200; the faces sit in 3-point planes by
`p23_mem_affineSpan_of_affGe`). The dropped base point carries a zero
coefficient in the branch taken, so the 3-point Affsign sums agree with the
4-point ones (`Finset.sum_subset`). -/
private theorem p23_affGe_split {u0 u1 w1 w2 v : V3}
    (hv : v ∈ affGe {u0, u1} {w1, w2})
    (h0 : ¬ (v ∈ affGt {u0, u1} {w1, w2})) :
    v ∈ affGe {u0, u1} {w1} ∨ v ∈ affGe {u0, u1} {w2} := by
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := hv
  by_cases hp1 : 0 < f w1
  · by_cases hp2 : 0 < f w2
    · exfalso
      refine h0 ⟨f, hfin, hsum, ?_, hone⟩
      intro w hw
      rcases (Set.mem_insert_iff).mp hw with hw' | hw'
      · rw [hw']; exact hp1
      · rw [Set.mem_singleton_iff.mp hw']; exact hp2
    · -- f w2 = 0: the fan degenerates onto the {w1}-sheet
      left
      have hw2z : f w2 = 0 := le_antisymm (le_of_not_gt hp2) (hpos w2 (by simp))
      have hsub : (({u0, u1} : Set V3) ∪ {w1}) ⊆ ({u0, u1} : Set V3) ∪ {w1, w2} := by
        intro z hz
        rcases (Set.mem_union _ _ _).mp hz with hz | hz
        · exact Set.mem_union_left _ hz
        · refine Set.mem_union_right _ ?_
          rw [Set.mem_insert_iff]; exact Or.inl (Set.mem_singleton_iff.mp hz)
      have hdif : ∀ z ∈ hfin.toFinset \ ((Set.toFinite (({u0, u1} : Set V3) ∪ {w1})).toFinset),
          z = w2 := by
        intro z hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.mp hz
        have h1 : z ∈ ({u0, u1} : Set V3) ∪ {w1, w2} := hfin.mem_toFinset.mp hz1
        have h2 : z ∉ ({u0, u1} : Set V3) ∪ {w1} :=
          fun hh => hz2 ((Set.Finite.mem_toFinset _).mpr hh)
        rcases (Set.mem_union _ _ _).mp h1 with h3 | h3
        · exact absurd (Set.mem_union_left _ h3) h2
        · rcases (Set.mem_insert_iff).mp h3 with h4 | h4
          · exact absurd (Set.mem_union_right _ (by simpa using h4)) h2
          · exact Set.mem_singleton_iff.mp h4
      have hsubF : ((Set.toFinite (({u0, u1} : Set V3) ∪ {w1})).toFinset) ⊆ hfin.toFinset := by
        intro z hz
        refine hfin.mem_toFinset.mpr ?_
        rcases (Set.mem_union _ _ _).mp (Set.Finite.mem_toFinset _ |>.mp hz) with h | h
        · exact Set.mem_union_left _ h
        · refine Set.mem_union_right _ ?_
          rw [Set.mem_insert_iff]; exact Or.inl (Set.mem_singleton_iff.mp h)
      have hsum1 : v = ∑ z ∈ (Set.toFinite (({u0, u1} : Set V3) ∪ {w1})).toFinset, f z • z := by
        rw [hsum, ← Finset.sum_subset hsubF (fun z hz1 hz2 => by
          rw [hdif z (Finset.mem_sdiff.mpr ⟨hz1, hz2⟩)]; simp [hw2z])]
      have hone1 : ∑ z ∈ (Set.toFinite (({u0, u1} : Set V3) ∪ {w1})).toFinset, f z = 1 := by
        rw [← hone]
        exact Finset.sum_subset hsubF (fun z hz1 hz2 => by
          rw [hdif z (Finset.mem_sdiff.mpr ⟨hz1, hz2⟩)]; exact hw2z)

      refine ⟨f, Set.toFinite (({u0, u1} : Set V3) ∪ {w1}), hsum1,
        fun w hw => by rw [Set.mem_singleton_iff.mp hw]; exact le_of_lt hp1, hone1⟩
  · -- symmetric branch: f w1 = 0, keep w2
    right
    have hw1z : f w1 = 0 := le_antisymm (le_of_not_gt hp1) (hpos w1 (by simp))
    have hsub : (({u0, u1} : Set V3) ∪ {w2}) ⊆ ({u0, u1} : Set V3) ∪ {w1, w2} := by
      intro z hz
      rcases (Set.mem_union _ _ _).mp hz with hz | hz
      · exact Set.mem_union_left _ hz
      · refine Set.mem_union_right _ ?_
        rw [Set.mem_insert_iff]; exact Or.inr (Set.mem_singleton_iff.mp hz)
    have hdif : ∀ z ∈ hfin.toFinset \ ((Set.toFinite (({u0, u1} : Set V3) ∪ {w2})).toFinset),
        z = w1 := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.mp hz
      have h1 : z ∈ ({u0, u1} : Set V3) ∪ {w1, w2} := hfin.mem_toFinset.mp hz1
      have h2 : z ∉ ({u0, u1} : Set V3) ∪ {w2} :=
        fun hh => hz2 ((Set.Finite.mem_toFinset _).mpr hh)
      rcases (Set.mem_union _ _ _).mp h1 with h3 | h3
      · exact absurd (Set.mem_union_left _ h3) h2
      · rcases (Set.mem_insert_iff).mp h3 with h4 | h4
        · exact h4
        · exact absurd (Set.mem_union_right _ (by rw [Set.mem_singleton_iff.mp h4]; simp)) h2
    have hsubF : ((Set.toFinite (({u0, u1} : Set V3) ∪ {w2})).toFinset) ⊆ hfin.toFinset := by
      intro z hz
      refine hfin.mem_toFinset.mpr ?_
      rcases (Set.mem_union _ _ _).mp (Set.Finite.mem_toFinset _ |>.mp hz) with h | h
      · exact Set.mem_union_left _ h
      · refine Set.mem_union_right _ ?_
        rw [Set.mem_insert_iff]; exact Or.inr (Set.mem_singleton_iff.mp h)
    refine ⟨f, Set.toFinite (({u0, u1} : Set V3) ∪ {w2}), ?_,
      fun w hw => by rw [Set.mem_singleton_iff.mp hw]; exact hpos w2 (by simp), ?_⟩
    · rw [hsum, ← Finset.sum_subset hsubF (fun z hz1 hz2 => by
        rw [hdif z (Finset.mem_sdiff.mpr ⟨hz1, hz2⟩)]; simp [hw1z])]
    · rw [← hone]
      exact Finset.sum_subset hsubF (fun z hz1 hz2 => by
        rw [hdif z (Finset.mem_sdiff.mpr ⟨hz1, hz2⟩)]; exact hw1z)

/-- GT-3e (HL §D projection/pythagoras argument, GRUTOTI.hl:2669-3090): the
SF-28-narrowed cap sits inside the double `rconeGe` of `mcell2`'s cut. The
forward cone is the monotonicity `d ≥ a`; the reverse cone decomposes `x`
into its axial projection `y = u0 + t•(u1-u0)` and orthogonal remainder —
pythagoras twice, the packing distance `2 ≤ dist u0 u1`, and the forward
condition give `‖y-u1‖ ≥ a·‖x-u1‖`. -/
private theorem p23_cap_sub_rconeGe2 {u0 u1 : V3} {r d a : ℝ}
    (h2 : 2 ≤ dist u0 u1) (hr1 : r ≤ 1) (hd : 0 < d) (hda : a ≤ d)
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    grutotiConicCap u0 u1 r d ⊆ rconeGe u0 u1 a ∩ rconeGe u1 u0 a := by
  intro x hx
  simp only [grutotiConicCap, Set.mem_inter_iff, Metric.mem_closedBall,
    rconeGt, Set.mem_setOf_eq] at hx
  obtain ⟨hxb, hxc⟩ := hx
  have hwn : ‖u1 - u0‖ = dist u0 u1 :=
    (norm_sub_rev u1 u0).trans (dist_eq_norm u0 u1).symm
  have hwn' : ‖u1 - u0‖ = dist u1 u0 := by rw [hwn, dist_comm]
  have hpos : (0:ℝ) < ‖u1 - u0‖ := by rw [hwn]; linarith
  have hX : ‖x - u0‖ ≤ 1 := by
    have h1 : dist x u0 ≤ 1 := le_trans hxb hr1
    rwa [dist_eq_norm] at h1
  refine ⟨?_, ?_⟩
  · -- forward cone: the SF-28 narrowness d ≥ a
    simp only [rconeGe, Set.mem_setOf_eq]
    exact le_trans (mul_le_mul_of_nonneg_left hda
      (mul_nonneg dist_nonneg dist_nonneg)) (le_of_lt hxc)
  · -- reverse cone: the projection/pythagoras argument
    simp only [rconeGe, Set.mem_setOf_eq]
    rw [← inner_eq_dot]
    have hxcw : (0:ℝ) < inner ℝ (x - u0) (u1 - u0) := by
      calc inner ℝ (x - u0) (u1 - u0) = (x - u0) ⬝ᵥ (u1 - u0) := inner_eq_dot _ _
        _ > dist x u0 * dist u1 u0 * d := hxc
        _ ≥ 0 := mul_nonneg (mul_nonneg dist_nonneg dist_nonneg) hd.le
    have hwW : inner ℝ (u1 - u0) (u1 - u0) = ‖u1 - u0‖ * ‖u1 - u0‖ :=
      real_inner_self_eq_norm_mul_norm _
    have hwWpos : (0:ℝ) < inner ℝ (u1 - u0) (u1 - u0) := by rw [hwW]; positivity
    set t : ℝ := inner ℝ (x - u0) (u1 - u0) / inner ℝ (u1 - u0) (u1 - u0) with htdef
    set y : V3 := u0 + t • (u1 - u0) with hydef
    have hdot : inner ℝ (x - y) (u1 - u0) = 0 := by
      have hsub : x - y = (x - u0) - t • (u1 - u0) := by rw [hydef]; abel
      rw [hsub, inner_sub_left, real_inner_smul_left, htdef,
        div_mul_cancel₀ _ hwWpos.ne', sub_self]
    have hAeq : inner ℝ (x - u0) (u1 - u0) = t * (inner ℝ (u1 - u0) (u1 - u0)) := by
      rw [htdef, div_mul_cancel₀ _ hwWpos.ne']
    have htpos : 0 < t := div_pos hxcw hwWpos
    have hny0 : ‖y - u0‖ = t * ‖u1 - u0‖ := by
      rw [hydef, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hC : inner ℝ (y - u0) (x - y) = 0 := by
      have hy0 : y - u0 = t • (u1 - u0) := by rw [hydef]; abel
      rw [hy0, real_inner_smul_left, real_inner_comm, hdot, mul_zero]
    have py1 : ‖x - u0‖ ^ 2 = ‖y - u0‖ ^ 2 + ‖x - y‖ ^ 2 := by
      have hsplit : x - u0 = (y - u0) + (x - y) := by rw [hydef]; abel
      rw [hsplit, norm_add_pow_two_real, hC]; ring
    have htu1 : t ≤ 1 := by
      have hcs : inner ℝ (x - u0) (u1 - u0) ≤ ‖x - u0‖ * ‖u1 - u0‖ := by
        have h2 := norm_inner_le_norm (𝕜 := ℝ) (x - u0) (u1 - u0)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hxcw)] at h2
        exact h2
      have h1 : t * (inner ℝ (u1 - u0) (u1 - u0)) ≤ ‖x - u0‖ * ‖u1 - u0‖ := by
        rwa [hAeq] at hcs
      rw [hwW] at h1
      nlinarith
    have hYge : ‖x - u0‖ ≤ ‖x - u1‖ := by
      have hdx : dist u0 x ≤ 1 := by rw [dist_comm u0 x]; exact le_trans hxb hr1
      have hd1 : (1:ℝ) ≤ dist x u1 := by
        have htri : dist u0 u1 ≤ dist u0 x + dist x u1 := dist_triangle u0 x u1
        linarith [h2, htri, hdx]
      rw [show ‖x - u1‖ = dist x u1 from dist_eq_norm x u1]
      exact le_trans hX hd1
    have hC2 : inner ℝ (y - u1) (x - y) = 0 := by
      have hy1 : y - u1 = (t - 1) • (u1 - u0) := by rw [hydef]; module
      rw [hy1, real_inner_smul_left, real_inner_comm, hdot, mul_zero]
    have py2 : ‖x - u1‖ ^ 2 = ‖y - u1‖ ^ 2 + ‖x - y‖ ^ 2 := by
      have hsplit : x - u1 = (y - u1) + (x - y) := by abel
      rw [hsplit, norm_add_pow_two_real, hC2]; ring
    have hYge' : ‖y - u0‖ ≤ ‖y - u1‖ := by
      have h3 : ‖y - u1‖ ^ 2 - ‖y - u0‖ ^ 2 = ‖x - u1‖ ^ 2 - ‖x - u0‖ ^ 2 := by
        rw [py2, py1]; ring
      have hD : (0:ℝ) ≤ ‖y - u1‖ - ‖y - u0‖ := by
        have e5 : (‖y - u1‖ - ‖y - u0‖) * (‖y - u1‖ + ‖y - u0‖)
            = ‖y - u1‖ ^ 2 - ‖y - u0‖ ^ 2 := by ring
        have hX2 : ‖x - u0‖ ^ 2 ≤ ‖x - u1‖ ^ 2 :=
          sq_le_sq' (by linarith [norm_nonneg (x - u0), norm_nonneg (x - u1)]) hYge
        nlinarith [e5, h3, hX2, sq_nonneg (‖y - u1‖ - ‖y - u0‖),
          norm_nonneg (y - u0), norm_nonneg (y - u1)]
      linarith
    have ha21 : 0 < 1 - a * a := by nlinarith
    -- forward condition sharpened through the projection: ‖y-u0‖ > a‖x-u0‖
    have hsharp : a * ‖x - u0‖ < ‖y - u0‖ := by
      have h1 : dist x u0 * dist u1 u0 * a < inner ℝ (x - u0) (u1 - u0) := by
        calc dist x u0 * dist u1 u0 * a
            ≤ dist x u0 * dist u1 u0 * d :=
              mul_le_mul_of_nonneg_left hda (mul_nonneg dist_nonneg dist_nonneg)
          _ < inner ℝ (x - u0) (u1 - u0) := by
              rw [inner_eq_dot]; exact hxc
      rw [← hwn', hAeq] at h1
      rw [hwW] at h1
      have hxid : ‖x - u0‖ = dist x u0 := dist_eq_norm x u0
      have hdiv : dist x u0 * a < t * ‖u1 - u0‖ := by
        have e7 : dist x u0 * a * ‖u1 - u0‖ = dist x u0 * ‖u1 - u0‖ * a := by ring
        refine lt_of_mul_lt_mul_right (h := ?_) hpos.le
        rw [e7, mul_assoc t]
        exact h1
      rw [hny0]
      calc a * ‖x - u0‖ = dist x u0 * a := by rw [hxid]; ring
        _ < t * ‖u1 - u0‖ := hdiv
    -- the chain down to a‖x-u1‖ ≤ ‖y-u1‖
    have hchain : a * ‖x - u1‖ ≤ ‖y - u1‖ := by
      have hsq1 : a * a * ‖x - u0‖ ^ 2 < ‖y - u0‖ ^ 2 := by
        have hneg : -‖y - u0‖ < -(a * ‖x - u0‖) := by linarith [hsharp]
        have hnn : (0:ℝ) ≤ a * ‖x - u0‖ := mul_nonneg ha0 (norm_nonneg _)
        have h0 : (a * ‖x - u0‖) ^ 2 < ‖y - u0‖ ^ 2 :=
          sq_lt_sq' (by linarith [hsharp, hnn]) hsharp
        have h1 : (a * ‖x - u0‖) ^ 2 = a * a * ‖x - u0‖ ^ 2 := by ring
        linarith
      have hYge2 : ‖y - u0‖ ^ 2 ≤ ‖y - u1‖ ^ 2 :=
        sq_le_sq' (by exact le_trans (neg_nonpos.mpr (norm_nonneg (y - u1))) (norm_nonneg (y - u0))) hYge'
      have hsub : a * a * ‖x - y‖ ^ 2 < (1 - a * a) * ‖y - u1‖ ^ 2 := by
        have e1 : a * a * ‖x - u0‖ ^ 2
            = a * a * ‖y - u0‖ ^ 2 + a * a * ‖x - y‖ ^ 2 := by rw [py1]; ring
        have e4 : (1 - a * a) * ‖y - u0‖ ^ 2 ≤ (1 - a * a) * ‖y - u1‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hYge2 ha21.le
        have e2 : (1 - a * a) * ‖y - u0‖ ^ 2 = ‖y - u0‖ ^ 2 - a * a * ‖y - u0‖ ^ 2 := by ring
        have e3 : (1 - a * a) * ‖y - u1‖ ^ 2 = ‖y - u1‖ ^ 2 - a * a * ‖y - u1‖ ^ 2 := by ring
        linarith
      have hfin : (a * ‖x - u1‖) ^ 2 < ‖y - u1‖ ^ 2 := by
        have e5 : a * a * ‖x - u1‖ ^ 2
            = a * a * ‖y - u1‖ ^ 2 + a * a * ‖x - y‖ ^ 2 := by rw [py2]; ring
        have e6 : a * a * ‖y - u1‖ ^ 2 + (1 - a * a) * ‖y - u1‖ ^ 2 = ‖y - u1‖ ^ 2 := by ring
        have h7 : (a * ‖x - u1‖) ^ 2 = a * a * ‖x - u1‖ ^ 2 := by ring
        linarith
      by_contra hcc
      have hlt : ‖y - u1‖ < a * ‖x - u1‖ := lt_of_not_ge hcc
      refine absurd hfin (not_lt.mpr (le_of_lt (sq_lt_sq'
        (by linarith [norm_nonneg (a * ‖x - u1‖), norm_nonneg (y - u1), hlt]) hlt)))
    -- assemble: inner (x-u1) (u0-u1) = ‖y-u1‖·‖u1-u0‖ ≥ a‖x-u1‖·‖u1-u0‖
    have hdott : inner ℝ (x - u1) (u0 - u1) = ‖y - u1‖ * ‖u1 - u0‖ := by
      have hsplit : x - u1 = (y - u1) + (x - y) := by abel
      have hC3 : inner ℝ (x - y) (u0 - u1) = 0 := by
        rw [show (u0 - u1) = -(u1 - u0) from by abel, inner_neg_right, hdot, neg_zero]
      have hy1 : y - u1 = (t - 1) • (u1 - u0) := by rw [hydef]; module
      rw [hsplit, inner_add_left, hC3, add_zero, hy1, real_inner_smul_left,
        show (u0 - u1) = -(u1 - u0) from by abel, inner_neg_right, hwW,
        norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith : (t:ℝ) - 1 ≤ 0)]
      ring
    have hfin2 : ‖x - u1‖ * ‖u1 - u0‖ * a ≤ ‖y - u1‖ * ‖u1 - u0‖ := by
      calc ‖x - u1‖ * ‖u1 - u0‖ * a = a * ‖x - u1‖ * ‖u1 - u0‖ := by ring
        _ ≤ ‖y - u1‖ * ‖u1 - u0‖ := mul_le_mul_of_nonneg_right hchain (norm_nonneg _)
    show inner ℝ (x - u1) (u0 - u1) ≥ dist x u1 * dist u0 u1 * a
    rw [← hwn, hdott, show dist x u1 = ‖x - u1‖ from dist_eq_norm x u1]
    exact hfin2
/-- GT-3e: the wedge-volume identity in the exact shape the k = 2/3/4 arms
consume — the `affGe` fan over two off-axis points intersected with the
region cap measures `vol D · dihV/2π`. Bridge (HL WEDGE_LUNE +
VOLUME_CONIC_CAP_WEDGE, GRUTOTI.hl:3091-3208/3356-3420): `wedge = affGt`
(LuneVolume `wedge_eq_affGt`), the `affGe`-faces drop into 3-point planes
(`p23_affGe_split` + `p23_mem_affineSpan_of_affGe`, null by
`p23_coplanar_affineSpan_null`), the boundary cases `azim ∈ {0, π}` put `w2`
in the `w1`-plane (`p23_mem_plane_of_azim_eq`), and the two open azimuth
ranges split on `azim_dihv_same` / `AZIM_COMPL_EXT` + `azim_dihv_compl`
against `volumeConicCapWedge`; the outer-measure sandwich needs no
measurability of the `Affsign` fan. -/
private theorem p23_vol_D_inter_affGe (u0 u1 w1 w2 : V3) (r d : ℝ)
    (hr : 0 < r) (hd : 0 < d) (hd1 : d < 1)
    (hc1 : ¬ Collinear3 u0 u1 w1) (hc2 : ¬ Collinear3 u0 u1 w2)
    (hpl : w2 ∉ (affineSpan ℝ ({u0, u1, w1} : Set V3))) :
    volume.real ((affGe {u0, u1} {w1, w2} : Set V3) ∩ grutotiConicCap u0 u1 r d)
      = volume.real (grutotiConicCap u0 u1 r d) * dihV u0 u1 w1 w2 / (2 * Real.pi) := by
  have hne : u0 ≠ u1 := fun hcc => hc1 (by rw [hcc]; exact collinear3_of_eq rfl)
  have hθ0 : azim u0 u1 w1 w2 ≠ 0 :=
    fun hcc => hpl (p23_mem_plane_of_azim_eq hne hc1 hc2 (Or.inl hcc))
  have hθπ : azim u0 u1 w1 w2 ≠ Real.pi :=
    fun hcc => hpl (p23_mem_plane_of_azim_eq hne hc1 hc2 (Or.inr hcc))
  -- the two face planes are null (3-point spans; the triple is coplanar)
  have hP1 : volume ((grutotiConicCap u0 u1 r d) ∩
      ((affineSpan ℝ ({u0, u1, w1} : Set V3)) : Set V3)) = 0 :=
    p23_coplanar_affineSpan_null (p23_coplanar_triple u0 u1 w1) Set.inter_subset_right
  have hP2 : volume ((grutotiConicCap u0 u1 r d) ∩
      ((affineSpan ℝ ({u0, u1, w2} : Set V3)) : Set V3)) = 0 :=
    p23_coplanar_affineSpan_null (p23_coplanar_triple u0 u1 w2) Set.inter_subset_right
  -- D is finitely volumed (closedBall of radius r)
  have hDfin : volume (grutotiConicCap u0 u1 r d ∩
      (affGe {u0, u1} {w1, w2} : Set V3)) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono fun z hz =>
      grutoti_cap_subset_closedBall u0 u1 r d hz.1) measure_closedBall_lt_top
  have hDfin' : volume (grutotiConicCap u0 u1 r d ∩ (wedge u0 u1 w1 w2)) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono fun z hz =>
      grutoti_cap_subset_closedBall u0 u1 r d hz.1) measure_closedBall_lt_top
  have hDfin2 : volume (grutotiConicCap u0 u1 r d ∩ (wedge u0 u1 w2 w1)) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono fun z hz =>
      grutoti_cap_subset_closedBall u0 u1 r d hz.1) measure_closedBall_lt_top
  rcases lt_or_ge (azim u0 u1 w1 w2) Real.pi with hθ | hθ
  · -- 0 < azim < π: the fan IS the open wedge up to the two null faces
    have hθpos : 0 < azim u0 u1 w1 w2 :=
      lt_of_le_of_ne (azim_nonneg u0 u1 w1 w2) (Ne.symm hθ0)
    have hwmem : ∀ z : V3, z ∈ affGt {u0, u1} {w1, w2} → z ∈ wedge u0 u1 w1 w2 :=
      fun z hz => Eq.subset (wedge_eq_affGt hc1 hc2 hθpos hθ).symm hz
    have hsub : (grutotiConicCap u0 u1 r d ∩ (affGe {u0, u1} {w1, w2} : Set V3)) ⊆
        (grutotiConicCap u0 u1 r d ∩ wedge u0 u1 w1 w2) ∪
        ((grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w1} : Set V3))) ∪
        (grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w2} : Set V3)))) := by
      rintro z ⟨hzD, hzL⟩
      by_cases hzgt : z ∈ affGt {u0, u1} {w1, w2}
      · exact Set.mem_union_left _ (Set.mem_inter hzD (hwmem z hzgt))
      · rcases p23_affGe_split hzL hzgt with h | h
        · exact Set.mem_union_right _ (Set.mem_union_left _
            (Set.mem_inter hzD (p23_mem_affineSpan_of_affGe h)))
        · exact Set.mem_union_right _ (Set.mem_union_right _
            (Set.mem_inter hzD (p23_mem_affineSpan_of_affGe h)))
    have hAB : volume (grutotiConicCap u0 u1 r d ∩ (affGe {u0, u1} {w1, w2} : Set V3))
        ≤ volume (grutotiConicCap u0 u1 r d ∩ wedge u0 u1 w1 w2) := by
      have hBC0 : volume ((grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w1} : Set V3))) ∪
          (grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w2} : Set V3)))) = 0 := by
        have hle := measure_union_le (μ := volume)
          (s := (grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w1} : Set V3))))
          (t := (grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w2} : Set V3))))
        rw [hP1, hP2, add_zero] at hle
        exact le_antisymm hle (by simp)
      refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
      rw [hBC0, add_zero]
    have hBA : volume (grutotiConicCap u0 u1 r d ∩ wedge u0 u1 w1 w2)
        ≤ volume (grutotiConicCap u0 u1 r d ∩ (affGe {u0, u1} {w1, w2} : Set V3)) := by
      have hsub2 : (grutotiConicCap u0 u1 r d ∩ wedge u0 u1 w1 w2) ⊆
          (grutotiConicCap u0 u1 r d ∩ (affGe {u0, u1} {w1, w2} : Set V3)) := by
        rintro z ⟨hzD, hzw⟩
        refine Set.mem_inter hzD (p23_affGt_sub_affGe {u0, u1} {w1, w2} ?_)
        rw [← wedge_eq_affGt hc1 hc2 hθpos hθ]
        exact hzw
      exact measure_mono hsub2
    have hsame : volume.real (grutotiConicCap u0 u1 r d ∩ wedge u0 u1 w1 w2)
        = volume.real (grutotiConicCap u0 u1 r d) * azim u0 u1 w1 w2 / (2 * Real.pi) :=
      volumeConicCapWedge u0 u1 w1 w2 r d hd hc1 hc2
    have hdihv : azim u0 u1 w1 w2 = dihV u0 u1 w1 w2 := azim_dihv_same hc1 hc2 hθ
    have hvolL : volume.real ((affGe {u0, u1} {w1, w2} : Set V3) ∩ grutotiConicCap u0 u1 r d)
        = volume.real (grutotiConicCap u0 u1 r d) * dihV u0 u1 w1 w2 / (2 * Real.pi) := by
      have e1 := ENNReal.toReal_le_toReal (ne_of_lt hDfin) (ne_of_lt hDfin') |>.2 hAB
      have e2 := ENNReal.toReal_le_toReal (ne_of_lt hDfin') (ne_of_lt hDfin) |>.2 hBA
      have e3 := hsame
      rw [hdihv] at e3
      rw [Set.inter_comm]
      rw [Measure.real_def] at e3 ⊢
      linarith
    exact hvolL
  · -- π < azim < 2π: the complementary wedge (w2, w1)
    have hθ' : azim u0 u1 w2 w1 = 2 * Real.pi - azim u0 u1 w1 w2 := by
      rw [AZIM_COMPL_EXT u0 u1 w1 w2, if_neg hθ0]
    have hθ'pos : 0 < azim u0 u1 w2 w1 := by
      have h1 := azim_lt_two_pi u0 u1 w1 w2
      rw [hθ']; linarith
    have hθgt : Real.pi < azim u0 u1 w1 w2 := lt_of_le_of_ne hθ (Ne.symm hθπ)
    have hθ'lt : azim u0 u1 w2 w1 < Real.pi := by
      rw [hθ']; linarith [hθgt]
    have hwmem : ∀ z : V3, z ∈ affGt {u0, u1} {w1, w2} → z ∈ wedge u0 u1 w2 w1 := by
      intro z hz
      have h2' : z ∈ affGt {u0, u1} {w2, w1} := p23_affGt_pair_symm hz
      exact Eq.subset (wedge_eq_affGt hc2 hc1 hθ'pos hθ'lt).symm h2'
    have hsub : (grutotiConicCap u0 u1 r d ∩ (affGe {u0, u1} {w1, w2} : Set V3)) ⊆
        (grutotiConicCap u0 u1 r d ∩ wedge u0 u1 w2 w1) ∪
        ((grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w1} : Set V3))) ∪
        (grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w2} : Set V3)))) := by
      rintro z ⟨hzD, hzL⟩
      by_cases hzgt : z ∈ affGt {u0, u1} {w1, w2}
      · exact Set.mem_union_left _ (Set.mem_inter hzD (hwmem z hzgt))
      · rcases p23_affGe_split hzL hzgt with h | h
        · exact Set.mem_union_right _ (Set.mem_union_left _
            (Set.mem_inter hzD (p23_mem_affineSpan_of_affGe h)))
        · exact Set.mem_union_right _ (Set.mem_union_right _
            (Set.mem_inter hzD (p23_mem_affineSpan_of_affGe h)))
    have hAB : volume (grutotiConicCap u0 u1 r d ∩ (affGe {u0, u1} {w1, w2} : Set V3))
        ≤ volume (grutotiConicCap u0 u1 r d ∩ wedge u0 u1 w2 w1) := by
      have hBC0 : volume ((grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w1} : Set V3))) ∪
          (grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w2} : Set V3)))) = 0 := by
        have hle := measure_union_le (μ := volume)
          (s := (grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w1} : Set V3))))
          (t := (grutotiConicCap u0 u1 r d ∩ (affineSpan ℝ ({u0, u1, w2} : Set V3))))
        rw [hP1, hP2, add_zero] at hle
        exact le_antisymm hle (by simp)
      refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
      rw [hBC0, add_zero]
    have hBA : volume (grutotiConicCap u0 u1 r d ∩ wedge u0 u1 w2 w1)
        ≤ volume (grutotiConicCap u0 u1 r d ∩ (affGe {u0, u1} {w1, w2} : Set V3)) := by
      have hsub2 : (grutotiConicCap u0 u1 r d ∩ wedge u0 u1 w2 w1) ⊆
          (grutotiConicCap u0 u1 r d ∩ (affGe {u0, u1} {w1, w2} : Set V3)) := by
        rintro z ⟨hzD, hzw⟩
        refine Set.mem_inter hzD (p23_affGt_sub_affGe {u0, u1} {w1, w2}
          (@p23_affGt_pair_symm u0 u1 w2 w1 z
            (Eq.subset (wedge_eq_affGt hc2 hc1 hθ'pos hθ'lt) hzw)))
      exact measure_mono hsub2
    have hsame : volume.real (grutotiConicCap u0 u1 r d ∩ wedge u0 u1 w2 w1)
        = volume.real (grutotiConicCap u0 u1 r d) * azim u0 u1 w2 w1 / (2 * Real.pi) :=
      volumeConicCapWedge u0 u1 w2 w1 r d hd hc2 hc1
    have hdihv : dihV u0 u1 w1 w2 = 2 * Real.pi - azim u0 u1 w1 w2 := by
      linarith [azim_dihv_compl hc1 hc2 hθ]
    have hvolL : volume.real ((affGe {u0, u1} {w1, w2} : Set V3) ∩ grutotiConicCap u0 u1 r d)
        = volume.real (grutotiConicCap u0 u1 r d) * dihV u0 u1 w1 w2 / (2 * Real.pi) := by
      have e1 := ENNReal.toReal_le_toReal (ne_of_lt hDfin) (ne_of_lt hDfin2) |>.2 hAB
      have e2 := ENNReal.toReal_le_toReal (ne_of_lt hDfin2) (ne_of_lt hDfin) |>.2 hBA
      have e3 := hsame
      rw [hθ', ← hdihv] at e3
      rw [Set.inter_comm]
      rw [Measure.real_def] at e3 ⊢
      linarith
    exact hvolL

/-! ## GT-3f lane: the k = 2/3/4 arm-closing kit (2026-10-08) -/

/-- GT-3f: the two-tip fan sits in the four-point affine span (the `affGe ⊆
affine hull` pattern for `mcell2`'s cut, feeding the coplanarity chase). -/
private theorem p23_affGe_mem_affineSpan2 {u0 u1 w1 w2 v : V3}
    (hv : v ∈ affGe {u0, u1} {w1, w2}) :
    v ∈ (affineSpan ℝ ({u0, u1, w1, w2} : Set V3)) := by
  obtain ⟨f, hfin, hsum, -, hone⟩ := hv
  have hS : ∀ z ∈ hfin.toFinset, z ∈ ({u0, u1, w1, w2} : Set V3) := by
    intro z hz
    rcases hfin.mem_toFinset.mp hz with hz' | hz'
    · rcases (Set.mem_insert_iff).mp hz' with h1 | h1
      · simp only [Set.mem_insert_iff]; exact Or.inl h1
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr (Or.inl h1)
    · rcases (Set.mem_insert_iff).mp hz' with h1 | h1
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr (Or.inr (Or.inl h1))
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr (Or.inr (Or.inr h1))
  have h0 : u0 ∈ (affineSpan ℝ ({u0, u1, w1, w2} : Set V3)) := mem_affineSpan (k := ℝ) (by simp)
  have hd : ∀ z ∈ ({u0, u1, w1, w2} : Set V3), (z - u0 : V3) ∈
      (affineSpan ℝ ({u0, u1, w1, w2} : Set V3)).direction :=
    fun z hz => AffineSubspace.vsub_mem_direction (mem_affineSpan (k := ℝ) hz) h0
  have key : v - u0 = ∑ z ∈ hfin.toFinset, f z • (z - u0) := by
    calc v - u0 = (∑ z ∈ hfin.toFinset, f z • z) - (∑ z ∈ hfin.toFinset, f z) • u0 := by
          rw [← hsum, hone, one_smul]
        _ = ∑ z ∈ hfin.toFinset, (f z • z - f z • u0) := by
          rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        _ = ∑ z ∈ hfin.toFinset, f z • (z - u0) := by
          exact Finset.sum_congr rfl fun z _ => (smul_sub (f z) z u0).symm
  have hv2 : ((∑ z ∈ hfin.toFinset, f z • (z - u0)) +ᵥ u0) ∈
      (affineSpan ℝ ({u0, u1, w1, w2} : Set V3)) :=
    AffineSubspace.vadd_mem_of_mem_direction
      (Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (hd z (hS z hz))) h0
  rw [show ((∑ z ∈ hfin.toFinset, f z • (z - u0)) +ᵥ u0) = v from by
    rw [vadd_eq_add, add_comm, ← key]; simp] at hv2
  exact hv2

/-- GT-3f: non-nullness of a set inside the four-point hull forces the
quartet's non-degeneracy facts consumed by the wedge helper — the three
coplanar collapses (w1 on the axis, w2 on the axis, w2 in the w1-plane) all
trap the hull in a three-point affine span, hence null. -/
private theorem p23_quartet_nondeg {u0 u1 w1 w2 : V3} {T : Set V3} (hu01 : u0 ≠ u1)
    (hT : T ⊆ (affineSpan ℝ ({u0, u1, w1, w2} : Set V3))) (hne : volume T ≠ 0) :
    ¬Collinear3 u0 u1 w1 ∧ ¬Collinear3 u0 u1 w2 ∧ w1 ≠ w2 ∧
      w2 ∉ (affineSpan ℝ ({u0, u1, w1} : Set V3)) := by
  have hcop : ¬ Coplanar ℝ ({u0, u1, w1, w2} : Set V3) := fun hcp =>
    hne (p23_coplanar_affineSpan_null hcp hT)
  have hsubW2 : Collinear3 u0 u1 w1 → ({u0, u1, w1, w2} : Set V3) ⊆
      ((affineSpan ℝ ({u0, u1, w2} : Set V3) : Set V3)) := by
    intro hcl z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact mem_affineSpan (k := ℝ) (by simp)
    · exact mem_affineSpan (k := ℝ) (by simp)
    · obtain ⟨c, hc⟩ := (collinear3_iff_smul (Ne.symm hu01)).mp hcl
      exact p23_mem_affineSpan_triple u0 u1 w2 z c 0 (by
        rw [show z = u0 + (z - u0) from by abel, hc]; module)
    · exact mem_affineSpan (k := ℝ) (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcl
    exact hcop (Coplanar.subset (hsubW2 hcl) (p23_coplanar_affineSpan_triple u0 u1 w2))
  · intro hcl
    have hsub : ({u0, u1, w1, w2} : Set V3) ⊆
        ((affineSpan ℝ ({u0, u1, w1} : Set V3) : Set V3)) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact mem_affineSpan (k := ℝ) (by simp)
      · exact mem_affineSpan (k := ℝ) (by simp)
      · exact mem_affineSpan (k := ℝ) (by simp)
      · obtain ⟨c, hc⟩ := (collinear3_iff_smul (Ne.symm hu01)).mp hcl
        exact p23_mem_affineSpan_triple u0 u1 w1 z c 0 (by
          rw [show z = u0 + (z - u0) from by abel, hc]; module)
    exact hcop (Coplanar.subset hsub (p23_coplanar_affineSpan_triple u0 u1 w1))
  · intro hww
    have hsub : ({u0, u1, w1, w2} : Set V3) ⊆
        ((affineSpan ℝ ({u0, u1, w1} : Set V3) : Set V3)) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact mem_affineSpan (k := ℝ) (by simp)
      · exact mem_affineSpan (k := ℝ) (by simp)
      · exact mem_affineSpan (k := ℝ) (by simp)
      · rw [hww]; exact mem_affineSpan (k := ℝ) (by simp)
    exact hcop (Coplanar.subset hsub (p23_coplanar_affineSpan_triple u0 u1 w1))
  · intro hmem
    have hsub : ({u0, u1, w1, w2} : Set V3) ⊆
        ((affineSpan ℝ ({u0, u1, w1} : Set V3) : Set V3)) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact mem_affineSpan (k := ℝ) (by simp)
      · exact mem_affineSpan (k := ℝ) (by simp)
      · exact mem_affineSpan (k := ℝ) (by simp)
      · exact hmem
    exact hcop (Coplanar.subset hsub (p23_coplanar_affineSpan_triple u0 u1 w1))

/-- GT-3f: the angle monotonicity behind HL §E/§F's cone case — for `t ≤ 0`
(the negative `u1`-coefficient of a fan point), `t • e + v` makes a wider
angle with the axis `e` than `v` itself: the normalized projection
`(w · e)/‖w‖` can only drop. The identity
`(v·e)²‖t e + v‖² − (v·e + t(e·e))²‖v‖² = (−t)(2v·e + t(e·e))((e·e)‖v‖² − (v·e)²)`
(Cauchy–Schwarz on the last factor) does the work. -/
private theorem p23_angleMono {e v : V3} {t : ℝ} (hve : 0 < inner ℝ v e)
    (hu : t • e + v ≠ 0) (ht : t ≤ 0) :
    inner ℝ (t • e + v) e / ‖t • e + v‖ ≤ inner ℝ v e / ‖v‖ := by
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hve
    simp at hve
  have hvp : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  have hup : (0:ℝ) < ‖t • e + v‖ := norm_pos_iff.mpr hu
  have hB0 : 0 ≤ inner ℝ e e := real_inner_self_nonneg
  have hue : inner ℝ (t • e + v) e = inner ℝ v e + t * inner ℝ e e := by
    rw [inner_add_left, real_inner_smul_left]; ring
  have hDu : inner ℝ (t • e + v) (t • e + v)
      = inner ℝ v v + 2 * t * inner ℝ v e + t * t * inner ℝ e e := by
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      real_inner_comm e v]
    ring
  by_cases huepos : 0 < inner ℝ (t • e + v) e
  · -- cross-multiply route
    have hcs : 0 ≤ inner ℝ e e * (‖v‖ * ‖v‖) - inner ℝ v e * inner ℝ v e := by
      have h1 := norm_inner_le_norm (𝕜 := ℝ) v e
      obtain ⟨h1a, h1b⟩ := abs_le.mp h1
      have hee : inner ℝ e e = ‖e‖ * ‖e‖ := real_inner_self_eq_norm_mul_norm e
      have hsq2 : inner ℝ v e * inner ℝ v e ≤ (‖v‖ * ‖e‖) * (‖v‖ * ‖e‖) := by
        nlinarith [h1a, h1b]
      rw [hee]
      nlinarith [hsq2, norm_nonneg v, norm_nonneg e]
    have h2p : (0:ℝ) < 2 * inner ℝ v e + t * inner ℝ e e := by
      rw [hue] at huepos; linarith
    have hrhs : (0:ℝ) ≤ (-t) * (2 * inner ℝ v e + t * inner ℝ e e)
        * (inner ℝ e e * (‖v‖ * ‖v‖) - inner ℝ v e * inner ℝ v e) :=
      mul_nonneg (mul_nonneg (neg_nonneg.mpr ht) (le_of_lt h2p)) hcs
    have hkey : (inner ℝ v e * inner ℝ v e) * (‖t • e + v‖ * ‖t • e + v‖)
        - (inner ℝ v e + t * inner ℝ e e) * (inner ℝ v e + t * inner ℝ e e) * (‖v‖ * ‖v‖)
        = (-t) * (2 * inner ℝ v e + t * inner ℝ e e)
          * (inner ℝ e e * (‖v‖ * ‖v‖) - inner ℝ v e * inner ℝ v e) := by
      nlinarith [hDu, real_inner_self_eq_norm_mul_norm (t • e + v),
        real_inner_self_eq_norm_mul_norm v, hue]
    have hs2 : (inner ℝ v e + t * inner ℝ e e) * (inner ℝ v e + t * inner ℝ e e)
        * (‖v‖ * ‖v‖) ≤ (inner ℝ v e * inner ℝ v e) * (‖t • e + v‖ * ‖t • e + v‖) := by
      linarith [hkey, hrhs]
    have hfinal : (inner ℝ v e + t * inner ℝ e e) * ‖v‖
        ≤ inner ℝ v e * ‖t • e + v‖ := by
      by_contra hcon
      have hlt2 : inner ℝ v e * ‖t • e + v‖
          < (inner ℝ v e + t * inner ℝ e e) * ‖v‖ := lt_of_not_ge hcon
      have hp1 : 0 ≤ inner ℝ v e * ‖t • e + v‖ :=
        mul_nonneg hve.le (norm_nonneg _)
      have hp2 : 0 < (inner ℝ v e + t * inner ℝ e e) * ‖v‖ := by
        have := huepos; rw [hue] at this; exact mul_pos this hvp
      have hsq := sq_lt_sq' (by linarith) hlt2
      rw [sq, sq] at hsq
      have e1 : (inner ℝ v e * ‖t • e + v‖) * (inner ℝ v e * ‖t • e + v‖)
          = (inner ℝ v e * inner ℝ v e) * (‖t • e + v‖ * ‖t • e + v‖) := by ring
      have e2 : ((inner ℝ v e + t * inner ℝ e e) * ‖v‖)
          * ((inner ℝ v e + t * inner ℝ e e) * ‖v‖)
          = ((inner ℝ v e + t * inner ℝ e e) * (inner ℝ v e + t * inner ℝ e e))
            * (‖v‖ * ‖v‖) := by ring
      rw [e1, e2] at hsq
      linarith [hkey, hrhs, hsq]
    rw [hue]
    refine (div_le_iff₀ hup).mpr ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hvp]
    exact hfinal
  · -- the killed branch: the projection is nonpositive, the target positive
    refine le_trans ?_ (le_of_lt (div_pos hve hvp))
    rw [div_le_iff₀ hup]
    linarith [hue]

/-- GT-3f (HL §E/§F fan∩cap ⊆ hull): a point of the `affGe {u0,u1} {w1,w2}`
fan that lies in the cap `D` lies in the hull of the four points, given the
SF-28 narrowness pair — the far-face plane `{u1,w1,w2}` stays at distance
≥ r from `u0` (face-距离径向排除), and the cut segment `conv {w1,w2}` sits
outside the strict cone `rconeGt u0 u1 d` (Cauchy–Schwarz 锥单调 via
`p23_angleMono`). The Affsign coefficients split on the signs of the two
base coefficients: nonnegative both — a convex combination outright;
negative `u0`-coefficient — the rescaled point lands on the far-face plane
so the cap's `dist ≤ r` dies; negative `u1`-coefficient — the angle chain
`g(x) ≤ g(scaled tip) = g(tip) ≤ d` dies against the cap's `g(x) > d`. -/
private theorem p23_fan_cap_sub_hull4 {u0 u1 w1 w2 : V3} {r d : ℝ}
    (hr : 0 < r) (hd : 0 < d)
    (hc1 : ¬ Collinear3 u0 u1 w1) (hc2 : ¬ Collinear3 u0 u1 w2) (hw12 : w1 ≠ w2)
    (hface : ∀ z ∈ (affineSpan ℝ ({u1, w1, w2} : Set V3)), r ≤ dist u0 z)
    (hcone : ∀ z ∈ convexHull ℝ ({w1, w2} : Set V3), z ∉ rconeGt u0 u1 d)
    {x : V3} (hxfan : x ∈ affGe {u0, u1} {w1, w2})
    (hxcap : x ∈ grutotiConicCap u0 u1 r d) :
    x ∈ convexHull ℝ ({u0, u1, w1, w2} : Set V3) := by
  have hu01 : u0 ≠ u1 := fun h => hc1 (by rw [h]; exact collinear3_of_eq rfl)
  have hplane : u0 ∉ (affineSpan ℝ ({u1, w1, w2} : Set V3)) := by
    intro hm
    have h0 := hface u0 hm
    rw [dist_self] at h0
    exact absurd h0 (not_le.mpr hr)
  have hu0w1 : u0 ≠ w1 := fun h =>
    hplane (by rw [h]; exact mem_affineSpan (k := ℝ) (by simp))
  have hu0w2 : u0 ≠ w2 := fun h =>
    hplane (by rw [h]; exact mem_affineSpan (k := ℝ) (by simp))
  have hu1w1 : u1 ≠ w1 := by
    intro h
    refine hc1 ?_
    rw [h]
    exact (collinear3_iff_smul (v := u0) (w := w1) (w1 := w1)
      (Ne.symm hu0w1)).mpr ⟨1, (one_smul ℝ (w1 - u0)).symm⟩
  have hu1w2 : u1 ≠ w2 := by
    intro h
    refine hc2 ?_
    rw [h]
    exact (collinear3_iff_smul (v := u0) (w := w2) (w1 := w2)
      (Ne.symm hu0w2)).mpr ⟨1, (one_smul ℝ (w2 - u0)).symm⟩
  obtain ⟨f, hfin, hsum, hfpos, hone⟩ := hxfan
  have hFeq : hfin.toFinset = ({u0, u1, w1, w2} : Finset V3) := by
    refine Finset.ext fun z => ?_
    rw [Set.Finite.mem_toFinset]
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hFeq] at hsum hone
  have hxv : x = f u0 • u0 + f u1 • u1 + f w1 • w1 + f w2 • w2 := by
    rw [hsum, show ({u0, u1, w1, w2} : Finset V3)
      = insert u0 (insert u1 (insert w1 ({w2} : Finset V3))) from rfl,
      Finset.sum_insert (by simp [hu01, hu0w1, hu0w2]),
      Finset.sum_insert (by simp [hu1w1, hu1w2]),
      Finset.sum_insert (by simp [hw12]), Finset.sum_singleton]
    abel
  have hone4 : f u0 + f u1 + f w1 + f w2 = 1 := by
    rw [← hone, show ({u0, u1, w1, w2} : Finset V3)
      = insert u0 (insert u1 (insert w1 ({w2} : Finset V3))) from rfl,
      Finset.sum_insert (by simp [hu01, hu0w1, hu0w2]),
      Finset.sum_insert (by simp [hu1w1, hu1w2]),
      Finset.sum_insert (by simp [hw12]), Finset.sum_singleton]
    ring
  have hs2p : 0 ≤ f w1 := hfpos w1 (by simp)
  have hs3p : 0 ≤ f w2 := hfpos w2 (by simp)
  by_cases ht0 : 0 ≤ f u0
  · by_cases ht1 : 0 ≤ f u1
    · -- both base coefficients nonnegative: outright convex combination
      have hxc : f u0 • u0 + f u1 • u1 + f w1 • w1 + f w2 • w2
          ∈ convexHull ℝ ({u0, u1, w1, w2} : Set V3) := by
        rw [CONVEX_HULL_4 u0 u1 w1 w2]
        simp only [Set.mem_setOf_eq]
        exact ⟨f u0, f u1, f w1, f w2, ht0, ht1, hs2p, hs3p, hone4, rfl⟩
      rwa [← hxv] at hxc
    · -- u1-coefficient negative: the cone-monotonicity case
      have hxball : dist x u0 ≤ r := by
        simp only [grutotiConicCap, Set.mem_inter_iff, Metric.mem_closedBall,
          rconeGt, Set.mem_setOf_eq] at hxcap
        exact hxcap.1
      have hcgt : dist x u0 * dist u1 u0 * d < inner ℝ (x - u0) (u1 - u0) := by
        simp only [grutotiConicCap, Set.mem_inter_iff, Metric.mem_closedBall,
          rconeGt, Set.mem_setOf_eq] at hxcap
        rw [← inner_eq_dot] at hxcap
        exact hxcap.2
      have hdotpos : (0:ℝ) < inner ℝ (x - u0) (u1 - u0) :=
        lt_of_le_of_lt (mul_nonneg (mul_nonneg dist_nonneg dist_nonneg) hd.le) hcgt
      have hxu0ne : x - u0 ≠ 0 := by
        intro h0
        rw [h0] at hdotpos
        simp at hdotpos
      have hsub : x - u0
          = f u1 • (u1 - u0) + f w1 • (w1 - u0) + f w2 • (w2 - u0) := by
        rw [hxv, show f u0 = 1 - (f u1 + f w1 + f w2) from by linarith]
        module
      by_cases hl0 : f w1 + f w2 = 0
      · -- both tips zero: x sits behind u0 on the axis, cone condition dies
        have hs2z : f w1 = 0 := by have := hs2p; linarith
        have hs3z : f w2 = 0 := by have := hs3p; linarith
        have hsub0 : x - u0 = f u1 • (u1 - u0) := by rw [hsub, hs2z, hs3z]; simp
        have hB0 : 0 ≤ inner ℝ (u1 - u0) (u1 - u0) := real_inner_self_nonneg
        have hnB : (0:ℝ) ≤ -(f u1) * inner ℝ (u1 - u0) (u1 - u0) := by
          nlinarith [hB0, lt_of_not_ge ht1]
        have h1 : inner ℝ (x - u0) (u1 - u0)
            = f u1 * inner ℝ (u1 - u0) (u1 - u0) := by
          rw [hsub0, real_inner_smul_left]
        have hcontra : (0:ℝ) < 0 := by linarith [h1, hdotpos, hnB]
        exact absurd hcontra (by norm_num)
      · have hlam : (0:ℝ) < f w1 + f w2 := lt_of_le_of_ne
          (add_nonneg hs2p hs3p) (Ne.symm hl0)
        obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = f w1 + f w2 := ⟨_, rfl⟩
        have hlampos : (0:ℝ) < lam := hlamdef ▸ hlam
        have hl0' : lam ≠ 0 := ne_of_gt hlampos
        set z : V3 := (f w1 / lam) • w1 + (f w2 / lam) • w2 with hzdef
        -- z on the cut segment
        have hab : f w1 / lam + f w2 / lam = 1 := by
          have hl2 : f w1 + f w2 ≠ 0 := by rw [← hlamdef]; exact hl0'
          rw [hlamdef]
          field_simp [hl2]
        have hpt : (f w1 / lam) • w1 + (f w2 / lam) • w2 = z := by
          rw [hzdef]
        have hzconv : z ∈ convexHull ℝ ({w1, w2} : Set V3) := by
          rw [convexHull_pair]
          exact ⟨f w1 / lam, f w2 / lam, div_nonneg hs2p (le_of_lt hlampos),
            div_nonneg hs3p (le_of_lt hlampos), hab, hpt⟩
        -- x - u0 = f u1 • e + lam • (z - u0)
        have hR : lam • (z - u0) = f w1 • (w1 - u0) + f w2 • (w2 - u0) := by
          rw [hzdef, smul_sub, smul_add, smul_smul, smul_smul,
            mul_div_cancel₀ (f w1) hl0', mul_div_cancel₀ (f w2) hl0', hlamdef]
          module
        have hsubz : x - u0 = f u1 • (u1 - u0) + lam • (z - u0) := by
          rw [hsub, hR]
          abel
        -- the angle chain
        have h2 : inner ℝ (lam • (z - u0)) (u1 - u0)
            = inner ℝ (x - u0) (u1 - u0)
              - f u1 * inner ℝ (u1 - u0) (u1 - u0) := by
          simp only [hsubz, real_inner_smul_left, inner_add_left]
          ring
        have hB0 : 0 ≤ inner ℝ (u1 - u0) (u1 - u0) := real_inner_self_nonneg
        have hnB : (0:ℝ) ≤ -(f u1) * inner ℝ (u1 - u0) (u1 - u0) := by
          nlinarith [hB0, lt_of_not_ge ht1]
        have hvdot : (0:ℝ) < inner ℝ (lam • (z - u0)) (u1 - u0) := by
          rw [h2]; linarith
        have hvne : f u1 • (u1 - u0) + lam • (z - u0) ≠ 0 := by
          intro h0
          rw [← hsubz] at h0
          exact hxu0ne h0
        have hmono := p23_angleMono (e := u1 - u0) (v := lam • (z - u0))
          (t := f u1) hvdot hvne (le_of_lt (lt_of_not_ge ht1))
        -- scale invariance: g(scaled tip direction) = g(tip direction)
        have hscale : inner ℝ (lam • (z - u0)) (u1 - u0) / ‖lam • (z - u0)‖
            = inner ℝ (z - u0) (u1 - u0) / ‖z - u0‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlampos,
            real_inner_smul_left, mul_div_mul_left _ _ hl0']
        -- the cap's strict cone condition, divided by ‖x - u0‖
        have hxu0p : (0:ℝ) < ‖x - u0‖ := norm_pos_iff.mpr hxu0ne
        have hcapdiv : dist u1 u0 * d
            < inner ℝ (x - u0) (u1 - u0) / ‖x - u0‖ := by
          have hdx : dist x u0 = ‖x - u0‖ := dist_eq_norm x u0
          have hdu : dist u1 u0 = ‖u1 - u0‖ := dist_eq_norm u1 u0
          rw [hdx, hdu] at hcgt
          rw [lt_div_iff₀ hxu0p, hdu]
          nlinarith [hcgt, norm_nonneg (x - u0)]
        -- the cut segment sits outside the strict cone
        have hznd : z ∉ rconeGt u0 u1 d := hcone z hzconv
        by_cases hz0 : ‖z - u0‖ = 0
        · -- z = u0: x on the axis behind u0 again
          have hz0' : z - u0 = 0 := norm_eq_zero.mp hz0
          have hsub0 : x - u0 = f u1 • (u1 - u0) := by rw [hsubz, hz0']; simp
          have h1 : inner ℝ (x - u0) (u1 - u0)
              = f u1 * inner ℝ (u1 - u0) (u1 - u0) := by
            rw [hsub0, real_inner_smul_left]
          have hcontra : (0:ℝ) < 0 := by linarith [h1, hdotpos, hnB]
          exact absurd hcontra (by norm_num)
        · have hzup : (0:ℝ) < ‖z - u0‖ :=
            lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
          have hzconed : (z - u0) ⬝ᵥ (u1 - u0) ≤ dist z u0 * dist u1 u0 * d := by
            simp only [rconeGt, Set.mem_setOf_eq] at hznd
            exact le_of_not_gt hznd
          have hzdiv : inner ℝ (z - u0) (u1 - u0) / ‖z - u0‖ ≤ dist u1 u0 * d := by
            have hdz : dist z u0 = ‖z - u0‖ := dist_eq_norm z u0
            rw [inner_eq_dot, div_le_iff₀ hzup]
            rw [hdz, mul_assoc] at hzconed
            calc (z - u0) ⬝ᵥ (u1 - u0) ≤ ‖z - u0‖ * (dist u1 u0 * d) := hzconed
              _ = (dist u1 u0 * d) * ‖z - u0‖ := by ring
          rw [← hsubz, hscale] at hmono
          linarith
  · -- u0-coefficient negative: the far-face case
    have hs : (0:ℝ) < 1 - f u0 := by linarith
    have hs2' : (1:ℝ) < 1 - f u0 := by linarith
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = 1 - f u0 := ⟨_, rfl⟩
    have hspos : (0:ℝ) < s := hsdef ▸ hs
    set y : V3 := (f u1 / s) • u1 + (f w1 / s) • w1 + (f w2 / s) • w2 with hydef
    have hcoef2 : (1:ℝ) - f w1 / s - f w2 / s = f u1 / s := by
      have hsum' : f u1 + f w1 + f w2 = s := by linarith
      have hs0 : s ≠ 0 := ne_of_gt hspos
      field_simp [hsdef]
      linarith
    have hy3 : y = u1 + (f w1 / s) • (w1 - u1) + (f w2 / s) • (w2 - u1) := by
      rw [hydef]
      have hsplit : u1 + (f w1 / s) • (w1 - u1) + (f w2 / s) • (w2 - u1)
          = (f u1 / s) • u1 + (f w1 / s) • w1 + (f w2 / s) • w2 := by
        have hcoef3 : (1:ℝ) - f w1 / s - f w2 / s = f u1 / s := hcoef2
        have hsplit2 : u1 + (f w1 / s) • (w1 - u1) + (f w2 / s) • (w2 - u1)
            = (1 - f w1 / s - f w2 / s) • u1 + (f w1 / s) • w1
              + (f w2 / s) • w2 := by
          module
        rw [hsplit2, hcoef3]
      rw [hsplit]
    have hyspan : y ∈ (affineSpan ℝ ({u1, w1, w2} : Set V3)) :=
      p23_mem_affineSpan_triple u1 w1 w2 y (f w1 / s) (f w2 / s) hy3
    have hydist : r ≤ dist u0 y := hface y hyspan
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hsmul : s • ((f u1 / s) • u1 + (f w1 / s) • w1 + (f w2 / s) • w2 - u0)
        = f u1 • u1 + f w1 • w1 + f w2 • w2 - s • u0 := by
      simp only [smul_sub, smul_add, smul_smul, mul_div_cancel₀ _ hsne]
    have hyx : x - u0 = s • (y - u0) := by
      have hfu0 : f u0 = 1 - s := by rw [hsdef]; ring
      rw [hydef, hxv, hfu0, hsmul]
      module
    have hdistxy : dist x u0 = s * dist u0 y := by
      have h1 : dist x u0 = ‖x - u0‖ := dist_eq_norm x u0
      have h2 : dist u0 y = ‖y - u0‖ :=
        (dist_eq_norm u0 y).trans (norm_sub_rev y u0).symm
      rw [h1, hyx, norm_smul, Real.norm_eq_abs, abs_of_pos hspos, h2]
    have hball : dist x u0 ≤ r := by
      simp only [grutotiConicCap, Set.mem_inter_iff, Metric.mem_closedBall,
        rconeGt, Set.mem_setOf_eq] at hxcap
      exact hxcap.1
    have hyr : (0:ℝ) < dist u0 y := lt_of_lt_of_le hr hydist
    nlinarith [hball, hdistxy, hydist, hyr, hs2']

/-- GT-3f: the k = 3/4 hull-arm combiner — from `T = hull {u0,u1,w1,w2}`,
non-nullness of `T ∩ D` and the SF-28 narrowness pair it yields the wedge
volume identity with `dihV` (hull ⊆ fan by CONVEX_HULL_4_SUBSET_AFF_GE_2_2,
fan∩D ⊆ hull by `p23_fan_cap_sub_hull4`, non-degeneracy by
`p23_quartet_nondeg`, volume by `p23_vol_D_inter_affGe`). -/
private theorem p23_hull_arm_eq {u0 u1 w1 w2 : V3} {r d : ℝ} {T : Set V3}
    (hr : 0 < r) (hd : 0 < d) (hd1 : d < 1) (hu01 : u0 ≠ u1)
    (hT : T = convexHull ℝ ({u0, u1, w1, w2} : Set V3))
    (hTnn : ¬ nullSet (T ∩ grutotiConicCap u0 u1 r d))
    (hface : ∀ z ∈ (affineSpan ℝ ({u1, w1, w2} : Set V3)), r ≤ dist u0 z)
    (hcone : ∀ z ∈ convexHull ℝ ({w1, w2} : Set V3), z ∉ rconeGt u0 u1 d) :
    volume.real (T ∩ grutotiConicCap u0 u1 r d)
      = volume.real (grutotiConicCap u0 u1 r d) * dihV u0 u1 w1 w2 / (2 * Real.pi) := by
  have hvolT : volume T ≠ 0 := fun h0 =>
    hTnn (measure_mono_null Set.inter_subset_left h0)
  have hsub : T ⊆ (affineSpan ℝ ({u0, u1, w1, w2} : Set V3)) := by
    rw [hT]; exact convexHull_min (subset_affineSpan ℝ _) (AffineSubspace.convex _)
  obtain ⟨hc1, hc2, hw12, hpl⟩ := p23_quartet_nondeg hu01 hsub hvolT
  have hsubL : T ∩ grutotiConicCap u0 u1 r d
      ⊆ (affGe {u0, u1} {w1, w2} : Set V3) ∩ grutotiConicCap u0 u1 r d :=
    Set.inter_subset_inter (by rw [hT]; exact CONVEX_HULL_4_SUBSET_AFF_GE_2_2 u0 u1 w1 w2)
      (subset_refl _)
  have hsubR : (affGe {u0, u1} {w1, w2} : Set V3) ∩ grutotiConicCap u0 u1 r d
      ⊆ T ∩ grutotiConicCap u0 u1 r d := by
    rintro z ⟨hzL, hzD⟩
    refine ⟨?_, hzD⟩
    rw [hT]
    exact p23_fan_cap_sub_hull4 hr hd hc1 hc2 hw12 hface hcone hzL hzD
  have heq : T ∩ grutotiConicCap u0 u1 r d
      = (affGe {u0, u1} {w1, w2} : Set V3) ∩ grutotiConicCap u0 u1 r d :=
    le_antisymm hsubL hsubR
  rw [heq, p23_vol_D_inter_affGe u0 u1 w1 w2 r d hr hd hd1 hc1 hc2 hpl]

/-- GT-3f: the `elV` reads of a family list — the first two entries are the
edge (`dihX`'s `dihu2/3/4` dispatch consumes these). -/
private theorem p23_elV0 {V : Set V3} {u0 u1 : V3} {vl : List V3}
    (hvl : vl ∈ p23Fam V u0 u1) : elV vl 0 = u0 := by
  have h := p23_hdV_eq_u0 hvl
  cases vl with
  | nil => simpa [hdV, elV, List.headD] using h
  | cons a t => simpa [hdV, elV, List.headD] using h

private theorem p23_elV1 {V : Set V3} {u0 u1 : V3} {vl : List V3}
    (hvl : vl ∈ p23Fam V u0 u1) : elV vl 1 = u1 := by
  have h := p23_hdTail_eq_u1 hvl
  cases vl with
  | nil => simpa [hdV, elV, List.tail, List.headD] using h
  | cons a t =>
    cases t with
    | nil => simpa [hdV, elV, List.tail, List.headD] using h
    | cons b t' => simpa [hdV, elV, List.tail, List.headD] using h

/-- HL GRUTOTI.hl:2652-2653 (proved there by the case analysis to 7958): the
per-cell wedge-volume identity. GT-3b status (2026-09-30): the `u0 = u1`
degenerate arm is discharged inline below (`p23_grutotiConicCap_self_empty`:
the capsule is the empty self-cone); the k-arms over the `mcellSet` witness
consume the GT-3 kit banked above — `k = 0,1`: impossible once the cell
carries two distinct edge points (`p23_edge_cell_k_ge_two`, HL §H arm (a);
junk-safety outside `k ∈ {2,3,4}`: `p23_dihX_of_cellParamsD_ne`; null cells:
`p23_dihX_of_nullSet`); `k = 4`-degenerate and the k = 2/3 wedge-boundary
sheets: coplanar-⇒-null via `p23_coplanar_measure_null` (private copy of
PA24's COPLANAR_IMP_NEGLIGIBLE content), the affine-hull workhorse
`p23_coplanar_affineSpan_null` (HL's 34× `NEGLIGIBLE_SUBSET (affine hull …)`
pattern), and the azimuth level sheets `p23_cap_inter_azimLevel_null` (via
the `p23_coplanarAzimEq` private copy of PA24's `COPLANAR_AZIM_EQ` fill).
REMAINING GIANT (the `sorry` below): the non-degenerate wedge identities —
k = 2 (HL §D: `mcell2` = double `rconeGe` ∩ the `affGe {u0,u1} {mxi, ω₃}`
wedge `L`, `vol (X∩D) = vol (L∩D)`, closed by CCV `volumeConicCapWedge`),
k = 3 (HL §F: hull + the AZIM_COMPL complement identity, `AZIM_COMPL_EXT`
PA6:2107), k = 4 non-coplanar (HL §E: needs the region-block extremal data
from `grutoti_region` to put `X ∩ D` into the coplanar sliver). RESOLVED
(STATEMENT-FIX 项 21, 2026-09-30 用户批准; binder 序修正同日——`he` 须在
`(X : Set V3)` 之后, 否则 autoImplicit 把类型里的 `X` 炼成哑变量): the
edge-cell hypothesis `(he : {u0, u1} ∈ edgeX V X)` (i.e.
`u0,u1 ∈ VX V X ∧ u0 ≠ u1`) is part of the signature — the k = 0,1 counting arm and the k = 4 degenerate closure
are consumable in that context, which the `grutoti_pivot` fill supplies.
GT-3d pass (2026-09-30): arm A (null cells: VACUOUS under `hn` —
measure-mono into the null `X` nulls `X ∩ D`; the identity's junk-safety
content there stays banked as `p23_dihX_of_nullSet` for the pivot sum) and
arm B (the §H junk arm with a VALID `cellParamsD`-witness of
index 0: `mcell0` lives outside `ball u0 √2`, the cap inside `closedBall u0 r ⊆
ball u0 √2`, so `X ∩ D = ∅` contradicts `hn`) are CLOSED; junk-safety
`p23_dihX_of_cellParamsD_ne` is banked in the non-null branch.
SF-21 BUG FOUND (2026-09-30, GT-3d): the `he` hypothesis is INERT as stated —
the binder order of the frozen signature puts `(he : {u0, u1} ∈ edgeX V X)`
BEFORE `(X : Set V3)`, and with this project's `autoImplicit` on, the `X`
inside `he`'s type elaborates to a fresh AUTO-BOUND implicit (displayed
`X✝`), NOT the explicit binder `X`. So `he` constrains a dead variable,
`u0,u1 ∈ VX V X` is NOT derivable, and the counting arm
`p23_edge_cell_k_ge_two` is NOT consumable in this signature. Next SF (with
the narrowness below): move `(X : Set V3)` ahead of `he` (or re-type `he`).
STATEMENT-FIX 项 28+29 APPLIED (2026-10-08, 用户批准; premise 形状对臂需求设计,
GRUTOTI capstone 消费时由 `grutoti_region` 的 witness 一步供给):
* (项 28) 窄性前提三条 —
  `hp : Packing V`(k = 2 反锥论证的 packing 距离 `2 ≤ dist u0 u1`,
  region/GRUTOTI 调用方天然携带);
  `hw1 : hl [u0, u1] / √2 ≤ d`(k = 1/2 楔窄性:`mcell1` 的截锥与 `mcell2`
  双 `rconeGe` 的参数都是 `a = hl (truncateSimplex 1 ul)/√2`,沿
  `initialSublist [u0,u1] ul` 恒等于 `hl [u0,u1]/√2`;region 侧由
  `rconeGt u0 u1 c ⊆ rconeGt u0 u1 (hl/√2)`(B4 单调性)给 `c ≥ a`,再
  `d ≥ c`);
  `hw3/hw4`:对 `p23Fam` 族(`barV V 3 vl ∧ truncateSimplex 1 vl = [u0,u1]`,
  带 `¬nullSet (mcell k V vl ∩ D)` 门,消费端由 `hn` 单调放电)分别给
  k = 3/4 的面窄性(`r ≤ dist u0 z`,z ∈ far-face 平面
  `{u1, elV vl 2, mxi V ul}` / `{u1, elV vl 2, elV vl 3}`——HL `r ≤ r1/r2`
  型,P1/P2 极值数据)与锥窄性(`convexHull {elV vl 2, mxi V ul}` /
  `{elV vl 2, elV vl 3}` 与 `rconeGt u0 u1 d` 不交——HL `d ≥ d1/d2` 型,
  P3/P4 极值数据;与 `d ≥ sup f3/f4` 等价,经
  `SMALLEST_ANGLE_LINE_PROPERTY`)。DEVIATIONS 注记的 r 侧极值数据
  (`f1`/`f2` > 0)在 region 内按 `p23_u0_notIn_hull3/4` 模式重推后即供给。
* (项 29) ε-junk 封角前提 —
  `hjunk : truncateSimplex 1 (cellParams V X).2 = [u0, u1]`:使 `cellParams`
  witness 同时是合法 `cellParamsD` witness(`initialSublist` 由
  `p23_trunc1_of_init` 桥接),REMAINING 3 的逆序表角整支消失。
陈账(下同):`p23_edge_cell_k_ge_two` 计数臂在 `he` 语境已就位但本轮
k = 0/1 臂由 cap-不交性/mcell1 形状直接闭合,未消费(留作 pivot 波弹药)。
GT-3e 已 banked 的消费端 kit(全部零错):`p23_trunc1_of_init`、
`p23_mem_affineSpan_of_affGe`、`p23_mem_plane_of_azim_eq`、
`p23_affGt_sub_affGe`、`p23_affGe_split`、`p23_affGt_pair_symm`、
`p23_cap_sub_rconeGe2`(HL §D 投影/勾股反锥论证)、`p23_vol_D_inter_affGe`
(楔体积合并式,两 azim 段 + 面零测外测三明治)。
GT-3f CLOSED (2026-10-08, 三支全闭, cell_vol 本体 sorry 清零):
1. k = 2:witness 正规化(ε-见证 .1 = 2)+ mcell2 形展开(∅-支反 hn)+
   `p23_quartet_nondeg`(hXspan 经 `p23_affGe_mem_affineSpan2` ⇒ ¬coplanar ⇒
   三条非退化)+ `p23_cap_sub_rconeGe2`(hp 距离 + hw1 窄性)闭
   X∩D = L∩D + `p23_vol_D_inter_affGe` + dihX↔dihu2↔dihV 对接
   (`p23_elV0/1`)。
2. k = 3:mcell3 形(∅-支)+ hw3 两条窄性经 `p23_hull_arm_eq` 一步闭
   (hull ⊆ 楠 CONVEX_HULL_4_SUBSET_AFF_GE_2_2;楠∩D ⊆ hull 由
   `p23_fan_cap_sub_hull4`:u0-系数负走远面径向排除、u1-系数负走
   `p23_angleMono` 锥单调;非退化由 `p23_quartet_nondeg`)+ wedge helper +
   dihX↔dihu3↔dihV 对接。
3. k = 4:同 2,hw4 + `p23_elV1`/htr 链(BARV_3_EXPLICIT +
   TRUNCATE_SIMPLEX_EXPLICIT_1/2)+ dihX↔dihu4↔dihV 对接。
region 侧供给(capstone 波,未变):hw1/hw3/hw4/hp 全部由 `grutoti_region` 的
witness 在其 B4/B6 段一步给出(hp 由饱和/packing 定义;P1/P2 面距离按
`p23_u0_notIn_hull3/4` 重推;P3/P4 经 SMALLEST_ANGLE_LINE_PROPERTY)。
GRUTOTI capstone 联动缺口因此缩小为:region 块的 r/r1/r2/d/d1/d2 极端数据
导出 + AJRIPQN/measure-union 侧(giant),per-cell 恒等式本体不再欠账。
GT-4 export pass (2026-10-08): 数据导出 BANKED — the companion
`p23_region_data` (same hypotheses as `grutoti_region`, strengthened
conclusion) supplies hw1 + hw3 + hw4 + hp + the region bounds/cover in one
destruct; capstone distance is now only the AJRIPQN/measure-union side
(`grutoti_sum_volD`/`grutoti_pivot` frozen giants). -/
private theorem grutoti_cell_vol (V : Set V3) (u0 u1 : V3) (r d : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hd1 : d < 1) (X : Set V3)
    (he : {u0, u1} ∈ edgeX V X)
    (hm : X ∈ mcellSet V) (hn : ¬nullSet (X ∩ grutotiConicCap u0 u1 r d))
    (hp : Packing V)
    (hw1 : hl [u0, u1] / Real.sqrt 2 ≤ d)
    (hw3 : ∀ vl : List V3, barV V 3 vl → truncateSimplex 1 vl = [u0, u1] →
      ¬nullSet (mcell 3 V vl ∩ grutotiConicCap u0 u1 r d) →
      (∀ z ∈ (affineSpan ℝ {u1, elV vl 2, mxi V vl} : Set V3), r ≤ dist u0 z) ∧
        ∀ z ∈ convexHull ℝ ({elV vl 2, mxi V vl} : Set V3), z ∉ rconeGt u0 u1 d)
    (hw4 : ∀ vl : List V3, barV V 3 vl → truncateSimplex 1 vl = [u0, u1] →
      ¬nullSet (mcell 4 V vl ∩ grutotiConicCap u0 u1 r d) →
      (∀ z ∈ (affineSpan ℝ {u1, elV vl 2, elV vl 3} : Set V3), r ≤ dist u0 z) ∧
        ∀ z ∈ convexHull ℝ ({elV vl 2, elV vl 3} : Set V3), z ∉ rconeGt u0 u1 d)
    (hjunk : truncateSimplex 1 (cellParams V X).2 = [u0, u1]) :
    volume.real (X ∩ grutotiConicCap u0 u1 r d) =
      volume.real (grutotiConicCap u0 u1 r d) * dihX V X (u0, u1) / (2 * Real.pi) := by
  by_cases hne : u0 = u1
  · rw [hne] at hn
    have hnull : nullSet (X ∩ grutotiConicCap u1 u1 r d) := by
      show volume (X ∩ grutotiConicCap u1 u1 r d) = 0
      rw [p23_grutotiConicCap_self_empty u1 r d, Set.inter_empty]
      exact measure_empty
    exact absurd hnull hn
  by_cases hns : nullSet X
  · -- GT-3d (2026-09-30) arm A (CLOSED): null cells — vacuous under `hn`
    -- (`measure_mono_null` into the null `X` nulls `X ∩ D`); the identity's
    -- junk-safety content for null cells stays banked as
    -- `p23_dihX_of_nullSet` (consumed by the pivot sum, which carries no `hn`).
    exact absurd (measure_mono_null Set.inter_subset_left hns :
      nullSet (X ∩ grutotiConicCap u0 u1 r d)) hn
  · -- GT-3d (2026-09-30) arm B (CLOSED below): the §H junk arm with a VALID
    -- `cellParamsD`-witness of index 0 — an `mcell0` cell lives outside
    -- `ball (hdV ul) √2` while the cap sits in `closedBall u0 r ⊆ ball u0 √2`,
    -- so `X ∩ D = ∅`, contradicting `hn`. NOTE: this arm does not need `he` —
    -- just as well, because (autoImplicit) the `X` inside `he`'s type is an
    -- AUTO-BOUND implicit, not the explicit binder `X` (binder order in the
    -- frozen signature: `he` precedes `(X : Set V3)`), so `he` constrains a
    -- dead variable and `p23_edge_cell_k_ge_two` is NOT consumable here; the
    -- next SF must move `(X : Set V3)` ahead of `he`. The remaining k-arms
    -- funnel into the three documented `sorry`s (NEEDS map in the docstring).
    -- the dihX junk-safety in this context (closes the `q.1 ∉ {2,3,4}` half of
    -- the junk case once `nullSet (X ∩ D)` is derivable):
    have _hdihJunk := p23_dihX_of_cellParamsD_ne V X (u0, u1) hns
    -- SF 项 29 (GT-3e, 2026-10-08): `hjunk` 使 `cellParams` witness 兼为合法
    -- `cellParamsD` witness(`initialSublist` 由 `p23_trunc1_of_init` 桥接),
    -- witness 情形无条件成立,ε-junk 逆序表角整支消失。
    have hXwit : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧
        X = mcell p.1 V p.2 := by
      obtain ⟨i, ul, hX, hbar⟩ := hm
      refine ⟨(min i 4, ul), by omega, hbar, ?_⟩
      rw [hX, p23_mcell_reduce]
    have hcp : (cellParams V X).1 ≤ 4 ∧ barV V 3 (cellParams V X).2 ∧
        X = mcell (cellParams V X).1 V (cellParams V X).2 :=
      Classical.epsilon_spec
        (p := fun p : ℕ × List V3 => p.1 ≤ 4 ∧ barV V 3 p.2 ∧
          X = mcell p.1 V p.2) hXwit
    have hcpinit : initialSublist [u0, u1] (cellParams V X).2 := by
      have h4 := hcp.2.1.1
      have htr := (p23_trunc_init_len 1 (cellParams V X).2 (by omega)).1
      rw [hjunk] at htr
      exact htr
    obtain ⟨hq4le, hqbar, hXm, hinit⟩ := Classical.epsilon_spec
      (p := fun p : ℕ × List V3 => p.1 ≤ 4 ∧ barV V 3 p.2 ∧
        X = mcell p.1 V p.2 ∧ initialSublist [u0, u1] p.2)
      ⟨((cellParams V X).1, (cellParams V X).2), hcp.1, hcp.2.1, hcp.2.2, hcpinit⟩
    rcases Nat.lt_or_ge (cellParamsD V X [u0, u1]).1 2 with hq12 | hqge
    · rcases Nat.eq_zero_or_pos (cellParamsD V X [u0, u1]).1 with hq0 | _hq1
      · -- arm B: index 0, `X = mcell0 V (cellParamsD …).2` with
        -- `hdV (cellParamsD …).2 = u0` — disjointness from the cap.
        have hXm' : X = mcell (cellParamsD V X [u0, u1]).1 V
            (cellParamsD V X [u0, u1]).2 := hXm
        rw [show (cellParamsD V X [u0, u1]).1 = 0 from hq0] at hXm'
        obtain ⟨yl, hyl⟩ := hinit
        have hhd : hdV (cellParamsD V X [u0, u1]).2 = u0 :=
          by rw [show (cellParamsD V X [u0, u1]).2 = [u0, u1] ++ yl from hyl]; simp [hdV]
        have hXeq : X ∩ grutotiConicCap u0 u1 r d = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          obtain ⟨hzX, hzD⟩ := hz
          rw [hXm'] at hzX
          have hzm : z ∈ rogers V (cellParamsD V X [u0, u1]).2 \
              Metric.ball (hdV (cellParamsD V X [u0, u1]).2) (Real.sqrt 2) := hzX
          rw [hhd] at hzm
          have h1 : √(1:ℝ) < Real.sqrt 2 :=
            Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 2)
          rw [Real.sqrt_one] at h1
          exact hzm.2 (Metric.mem_ball.mpr (lt_of_le_of_lt
            (Metric.mem_closedBall.mp (Set.inter_subset_left hzD)) (lt_of_le_of_lt hr1 h1)))
        exact absurd (show nullSet (X ∩ grutotiConicCap u0 u1 r d) from by
          show volume (X ∩ grutotiConicCap u0 u1 r d) = 0
          rw [hXeq]
          exact measure_empty) hn

      · -- index 1 (SF 项 28 hw1 消费端, GT-3e 2026-10-08): mcell1 的径向截锥
        -- 参数 a = hl (truncateSimplex 1 ul)/√2 = hl [u0,u1]/√2 ≤ d (hw1),
        -- D ⊆ rconeGt u0 u1 d ⊆ rconeGt u0 u1 a,而 mcell1 在截锥补集中
        -- (∅-支直接 X = ∅)——X ∩ D = ∅,与 hn 矛盾。
        have hq1 : (cellParamsD V X [u0, u1]).1 = 1 := by omega
        have hXm' : X = mcell (cellParamsD V X [u0, u1]).1 V
            (cellParamsD V X [u0, u1]).2 := hXm
        have hinit' : initialSublist [u0, u1] (cellParamsD V X [u0, u1]).2 := hinit
        rw [hq1] at hXm'
        have hfam : (cellParamsD V X [u0, u1]).2 ∈ p23Fam V u0 u1 :=
          ⟨hqbar, p23_trunc1_of_init hinit'⟩
        have hd0 : hdV (cellParamsD V X [u0, u1]).2 = u0 := p23_hdV_eq_u0 hfam
        have hd1v : hdV (cellParamsD V X [u0, u1]).2.tail = u1 := p23_hdTail_eq_u1 hfam
        have hXeq : X ∩ grutotiConicCap u0 u1 r d = ∅ := by
          rw [hXm', (MCELL_EXPLICIT 1 V (cellParamsD V X [u0, u1]).2).2.1]
          simp only [mcell1]
          by_cases hhl2 : Real.sqrt 2 ≤ hl (cellParamsD V X [u0, u1]).2
          · rw [if_pos hhl2, hd0, hd1v, p23_trunc1_of_init hinit']
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro z hz
            obtain ⟨⟨_, hz2⟩, hzD⟩ := hz
            exact hz2 (grutoti_cap_rcone_mono u0 u1 r
              (hl [u0, u1] / Real.sqrt 2) d hw1 hzD)
          · rw [if_neg hhl2, Set.empty_inter]
        exact absurd (show nullSet (X ∩ grutotiConicCap u0 u1 r d) from by
          show volume (X ∩ grutotiConicCap u0 u1 r d) = 0
          rw [hXeq]
          exact measure_empty) hn
    · -- index ∈ {2,3,4}: the k-arms (HL §D/§E/§F).
      rcases Nat.lt_or_ge (cellParamsD V X [u0, u1]).1 4 with hlt4 | hge4
      · rcases Nat.lt_or_ge (cellParamsD V X [u0, u1]).1 3 with hlt3 | hge3
        · -- k = 2 (HL §D, GRUTOTI.hl:2669-3208). CLOSED (GT-3f, 2026-10-08):
          -- witness 正规化 + mcell2 形展开(∅-支反 hn)+ quartet 非退化 +
          -- p23_cap_sub_rconeGe2 闭 X∩D = L∩D + wedge helper +
          -- dihX↔dihu2↔dihV 对接(p23_elV0/1)。
          have hq2 : (cellParamsD V X [u0, u1]).1 = 2 := by omega
          obtain ⟨ul, huldef⟩ : ∃ ul : List V3, ul = (cellParamsD V X [u0, u1]).2 :=
            ⟨_, rfl⟩
          have hXm' : X = mcell (cellParamsD V X [u0, u1]).1 V ul := by
            rw [huldef]; exact hXm
          have hqbar' : barV V 3 ul := by rw [huldef]; exact hqbar
          have hinit' : initialSublist [u0, u1] ul := by rw [huldef]; exact hinit
          rw [hq2] at hXm'
          have hfam : ul ∈ p23Fam V u0 u1 := ⟨hqbar', p23_trunc1_of_init hinit'⟩
          have htr1 : truncateSimplex 1 ul = [u0, u1] := p23_trunc1_of_init hinit'
          have hd0 : hdV ul = u0 := p23_hdV_eq_u0 hfam
          have hd1v : hdV ul.tail = u1 := p23_hdTail_eq_u1 hfam
          by_cases hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul
          · -- 楠点 m/s3 的非退化(hn 消费:X ⊆ 四点仿射包,共面 ⇒ 零测;
            --   mcell2 形展开走成员级 rw,免 ite-可判定求值)
            have hXspan : X ⊆
                (affineSpan ℝ ({u0, u1, mxi V ul, omegaListN V ul 3} : Set V3)) := by
              intro z hz
              rw [hXm', (MCELL_EXPLICIT 2 V ul).2.2.1] at hz
              rw [mcell2, if_pos hcond, htr1, hd0, hd1v] at hz
              exact p23_affGe_mem_affineSpan2 hz.2
            obtain ⟨hc1, hc2, -, hpl⟩ := p23_quartet_nondeg hne hXspan hns
            -- hp 的 packing 距离(u0, u1 ∈ V 由 barV + initialSublist)
            obtain ⟨yl, hyl⟩ := hinit'
            have hu0V : u0 ∈ V :=
              BARV_SUBSET V 3 ul hqbar' (by rw [hyl]; simp [setOfList])
            have hu1V : u1 ∈ V :=
              BARV_SUBSET V 3 ul hqbar' (by rw [hyl]; simp [setOfList])
            have h2d : 2 ≤ dist u0 u1 := Packing.dist_ge_two hp hu0V hu1V hne
            have ha0 : 0 ≤ hl [u0, u1] / Real.sqrt 2 := by
              rw [HL_2]; positivity
            have ha1 : hl [u0, u1] / Real.sqrt 2 < 1 := lt_of_le_of_lt hw1 hd1
            have hcapcone : grutotiConicCap u0 u1 r d
                ⊆ rconeGe u0 u1 (hl [u0, u1] / Real.sqrt 2)
                  ∩ rconeGe u1 u0 (hl [u0, u1] / Real.sqrt 2) :=
              p23_cap_sub_rconeGe2 h2d hr1 hd hw1 ha0 ha1
            -- X ∩ D = L ∩ D(双锥由 p23_cap_sub_rconeGe2 消去)
            have heq : X ∩ grutotiConicCap u0 u1 r d
                = (affGe {u0, u1} {mxi V ul, omegaListN V ul 3} : Set V3)
                  ∩ grutotiConicCap u0 u1 r d := by
              have hsubL : X ∩ grutotiConicCap u0 u1 r d
                  ⊆ (affGe {u0, u1} {mxi V ul, omegaListN V ul 3} : Set V3)
                    ∩ grutotiConicCap u0 u1 r d := by
                rintro z ⟨hzX, hzD⟩
                rw [hXm', (MCELL_EXPLICIT 2 V ul).2.2.1] at hzX
                rw [mcell2, if_pos hcond, htr1, hd0, hd1v] at hzX
                exact ⟨hzX.2, hzD⟩
              have hsubR : (affGe {u0, u1} {mxi V ul, omegaListN V ul 3} : Set V3)
                    ∩ grutotiConicCap u0 u1 r d
                  ⊆ X ∩ grutotiConicCap u0 u1 r d := by
                rintro z ⟨hzL, hzD⟩
                refine ⟨?_, hzD⟩
                rw [hXm', (MCELL_EXPLICIT 2 V ul).2.2.1]
                rw [mcell2, if_pos hcond, htr1, hd0, hd1v]
                exact And.intro (And.intro (hcapcone hzD).1 (hcapcone hzD).2) hzL
              exact le_antisymm hsubL hsubR
            have hdihX : dihX V X (u0, u1)
                = dihV u0 u1 (mxi V ul) (omegaListN V ul 3) := by
              have hE0 : elV ul 0 = u0 := p23_elV0 hfam
              have hE1 : elV ul 1 = u1 := p23_elV1 hfam
              simp only [dihX, if_neg hns, hq2, if_pos]
              rw [← huldef, dihu2, hE0, hE1]
            rw [heq,
              p23_vol_D_inter_affGe u0 u1 (mxi V ul) (omegaListN V ul 3) r d hr hd hd1
                hc1 hc2 hpl, hdihX]
          · -- ∅-支:X ∩ D = ∅ 反 hn(k<2 臂同款;成员级展开)
            have hXeq : X ∩ grutotiConicCap u0 u1 r d = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro z hz
              obtain ⟨hzX, -⟩ := hz
              rw [hXm'] at hzX
              rw [(MCELL_EXPLICIT 2 V ul).2.2.1, mcell2, if_neg hcond] at hzX
              simp at hzX
            exact absurd (show nullSet (X ∩ grutotiConicCap u0 u1 r d) from by
              show volume (X ∩ grutotiConicCap u0 u1 r d) = 0
              rw [hXeq]
              exact measure_empty) hn
        · -- k = 3 (HL §F). CLOSED (GT-3f, 2026-10-08): mcell3 形(∅-支反 hn)
          -- + hw3 面/锥窄性经 p23_hull_arm_eq(hull ⊆ 楠
          -- CONVEX_HULL_4_SUBSET_AFF_GE_2_2 + 楠∩D ⊆ hull by
          -- p23_fan_cap_sub_hull4:面-距离径向 / p23_angleMono 锥单调)+
          -- wedge helper + dihX↔dihu3↔dihV 对接。
          have hq3 : (cellParamsD V X [u0, u1]).1 = 3 := by omega
          obtain ⟨ul, huldef⟩ : ∃ ul : List V3, ul = (cellParamsD V X [u0, u1]).2 :=
            ⟨_, rfl⟩
          have hXm' : X = mcell (cellParamsD V X [u0, u1]).1 V ul := by
            rw [huldef]; exact hXm
          have hqbar' : barV V 3 ul := by rw [huldef]; exact hqbar
          have hinit' : initialSublist [u0, u1] ul := by rw [huldef]; exact hinit
          rw [hq3] at hXm'
          have hfam : ul ∈ p23Fam V u0 u1 := ⟨hqbar', p23_trunc1_of_init hinit'⟩
          have htr1 : truncateSimplex 1 ul = [u0, u1] := p23_trunc1_of_init hinit'
          have htr2 : truncateSimplex 2 ul = [u0, u1, elV ul 2] := by
            obtain ⟨v0, v1, v2, v3, hvul⟩ := BARV_3_EXPLICIT V ul hqbar'
            have h1 : truncateSimplex 1 ul = [v0, v1] := by
              rw [hvul]; exact (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
            have h2t : truncateSimplex 2 ul = [v0, v1, v2] := by
              rw [hvul]; exact (TRUNCATE_SIMPLEX_EXPLICIT_2 v0 v1 v2 v3).2
            injection (htr1.symm.trans h1).symm with ha hb
            injection hb with hc _
            have hv2 : v2 = elV ul 2 := by rw [hvul]; simp [elV]
            rw [h2t, ha, hc, hv2]
          by_cases hcond : hl (truncateSimplex 2 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul
          · -- X = hull {u0, u1, elV ul 2, mxi V ul}(成员级 ext 展形)
            have hXhull : X
                = convexHull ℝ ({u0, u1, elV ul 2, mxi V ul} : Set V3) := by
              ext z
              rw [hXm', (MCELL_EXPLICIT 3 V ul).2.2.2.1]
              rw [mcell3, if_pos hcond, htr2]
              have hsets : setOfList [u0, u1, elV ul 2] ∪ {mxi V ul}
                  = ({u0, u1, elV ul 2, mxi V ul} : Set V3) := by
                ext w
                simp only [setOfList, Set.mem_setOf_eq, List.mem_cons,
                  List.not_mem_nil, Set.mem_union, Set.mem_insert_iff,
                  Set.mem_singleton_iff]
                tauto
              rw [hsets]
            -- hw3 消费(门条件由 hn 一步供给)
            have hdoor : ¬ nullSet (mcell 3 V ul ∩ grutotiConicCap u0 u1 r d) := by
              rw [← hXm']
              exact hn
            obtain ⟨hface3, hcone3⟩ := hw3 ul hqbar' htr1 hdoor
            have hdihX : dihX V X (u0, u1)
                = dihV u0 u1 (elV ul 2) (mxi V ul) := by
              have hE0 : elV ul 0 = u0 := p23_elV0 hfam
              have hE1 : elV ul 1 = u1 := p23_elV1 hfam
              simp only [dihX, if_neg hns]
              rw [hq3, if_neg (by decide : ¬ (3:ℕ) = 2), if_pos (rfl : (3:ℕ) = 3)]
              rw [← huldef, dihu3, hE0, hE1]
            rw [p23_hull_arm_eq hr hd hd1 hne hXhull hn hface3 hcone3, hdihX]
          · -- ∅-支
            have hXeq : X ∩ grutotiConicCap u0 u1 r d = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro z hz
              obtain ⟨hzX, -⟩ := hz
              rw [hXm'] at hzX
              rw [(MCELL_EXPLICIT 3 V ul).2.2.2.1, mcell3, if_neg hcond] at hzX
              simp at hzX
            exact absurd (show nullSet (X ∩ grutotiConicCap u0 u1 r d) from by
              show volume (X ∩ grutotiConicCap u0 u1 r d) = 0
              rw [hXeq]
              exact measure_empty) hn
      · -- k = 4 (HL §E). CLOSED (GT-3f, 2026-10-08): 同 k = 3,hw4 +
        -- CONVEX_HULL_4_SUBSET_AFF_GE_2_2 + p23_fan_cap_sub_hull4 +
        -- wedge helper + dihX↔dihu4↔dihV 对接。
        have hq4le' : (cellParamsD V X [u0, u1]).1 ≤ 4 := hq4le
        have hq4 : (cellParamsD V X [u0, u1]).1 = 4 := by omega
        obtain ⟨ul, huldef⟩ : ∃ ul : List V3, ul = (cellParamsD V X [u0, u1]).2 :=
          ⟨_, rfl⟩
        have hXm' : X = mcell (cellParamsD V X [u0, u1]).1 V ul := by
          rw [huldef]; exact hXm
        have hqbar' : barV V 3 ul := by rw [huldef]; exact hqbar
        have hinit' : initialSublist [u0, u1] ul := by rw [huldef]; exact hinit
        rw [hq4] at hXm'
        have hfam : ul ∈ p23Fam V u0 u1 := ⟨hqbar', p23_trunc1_of_init hinit'⟩
        have htr1 : truncateSimplex 1 ul = [u0, u1] := p23_trunc1_of_init hinit'
        have hseteq : setOfList ul = ({u0, u1, elV ul 2, elV ul 3} : Set V3) := by
          obtain ⟨v0, v1, v2, v3, hvul⟩ := BARV_3_EXPLICIT V ul hqbar'
          have h1 : truncateSimplex 1 ul = [v0, v1] := by
            rw [hvul]; exact (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
          injection (htr1.symm.trans h1).symm with ha hb
          injection hb with hc _
          have hv2 : v2 = elV ul 2 := by rw [hvul]; simp [elV]
          have hv3 : v3 = elV ul 3 := by rw [hvul]; simp [elV]
          ext w
          have hw : w ∈ setOfList ul ↔ w ∈ [v0, v1, v2, v3] := by
            rw [hvul, setOfList, Set.mem_setOf_eq]
          rw [hw, ha, hc, hv2, hv3]
          simp
        by_cases hcond : hl ul < Real.sqrt 2
        · -- X = hull {u0, u1, elV ul 2, elV ul 3}(成员级 ext 展形)
          have hXhull : X
              = convexHull ℝ ({u0, u1, elV ul 2, elV ul 3} : Set V3) := by
            ext z
            rw [hXm', (MCELL_EXPLICIT 4 V ul).2.2.2.2 (Nat.le_refl 4)]
            rw [mcell4, if_pos hcond, hseteq]
          -- hw4 消费(门条件由 hn 一步供给)
          have hdoor : ¬ nullSet (mcell 4 V ul ∩ grutotiConicCap u0 u1 r d) := by
            rw [← hXm']
            exact hn
          obtain ⟨hface4, hcone4⟩ := hw4 ul hqbar' htr1 hdoor
          have hdihX : dihX V X (u0, u1)
              = dihV u0 u1 (elV ul 2) (elV ul 3) := by
            have hE0 : elV ul 0 = u0 := p23_elV0 hfam
            have hE1 : elV ul 1 = u1 := p23_elV1 hfam
            simp only [dihX, if_neg hns]
            rw [hq4, if_neg (by decide : ¬ (4:ℕ) = 2),
              if_neg (by decide : ¬ (4:ℕ) = 3), if_pos (rfl : (4:ℕ) = 4)]
            rw [← huldef, dihu4, hE0, hE1]
          rw [p23_hull_arm_eq hr hd hd1 hne hXhull hn hface4 hcone4, hdihX]
        · -- ∅-支
          have hXeq : X ∩ grutotiConicCap u0 u1 r d = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro z hz
            obtain ⟨hzX, -⟩ := hz
            rw [hXm'] at hzX
            rw [(MCELL_EXPLICIT 4 V ul).2.2.2.2 (Nat.le_refl 4), mcell4,
              if_neg hcond] at hzX
            simp at hzX
          exact absurd (show nullSet (X ∩ grutotiConicCap u0 u1 r d) from by
            show volume (X ∩ grutotiConicCap u0 u1 r d) = 0
            rw [hXeq]
            exact measure_empty) hn

/-- HL GRUTOTI.hl:7228-7400 (`sum s (\t. vol (t INTER D)) = vol D` via
`MEASURE_NEGLIGIBLE_UNIONS_IMAGE` over the almost-disjoint cell family) plus
index finiteness from `FINITE_MCELL_SET_LEMMA_2` (marchal3.hl:2620; Auto15:520,
cells are bounded, e.g. `grutoti_cap_subset_ball`).
STATEMENT-FIX item 31 (2026-10-09, 方案 a1, user-approved): the frozen
signature was REFUTABLE — its premise face was only `he : e = {u0, u1}` with
`V u0 u1 r d` completely free, and `V := ∅` zeroes the LHS (`mcellSet ∅ = ∅`)
while `volumeConicCapPos` keeps the RHS positive (machine-verified
counterexample: docs/grutoti-assets/probe_sum_volD_falsity.lean). The
signature now carries the `p23_region_data` gate family verbatim
(hs hp hu0 hu1 hne hhl he), the region-block shape `0 < r` / `d < 1`, and the
measure-cover debt explicitly: trace measurability, pairwise-null
intersections, finite trace volumes, and the cover identity
`volume.real (⋃₀ traces) = volume.real D`. The body is a pure two-piece
assembly: finiteness = `FINITE_EDGE_X2` (PA15:775, real; ∈-same body as
`grutotiEdgeCells`, machine-verified), the sum identity =
`p23_measure_setSum_biUnion` (banked bridge). The remaining math debt — the
cover itself (TIWWFYQ/GLTVHUM/SLTSTLO1 + PA17 AJRIPQN pairwise-null) — lives
in the hypotheses and is the capstone's obligation at `GRUTOTI` (:4484, all
gates in scope). Note superseding the old GT-2 route note (1): the far-point
infinity arm runs over mcell0/2/3 cells (`mcell4` is empty on the far-point
family, `hl ≥ √2` ⇒ nullSet), not mcell4. -/
private theorem grutoti_sum_volD (V : Set V3) (u0 u1 : V3) (e : Set V3) (r d : ℝ)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) (he : e = {u0, u1})
    (hr : 0 < r) (hd : d < 1)
    (hmeas : ∀ X ∈ grutotiEdgeCells V e,
      MeasurableSet (X ∩ grutotiConicCap u0 u1 r d))
    (hpair : ∀ X ∈ grutotiEdgeCells V e, ∀ Y ∈ grutotiEdgeCells V e, X ≠ Y →
      volume ((X ∩ grutotiConicCap u0 u1 r d) ∩
        (Y ∩ grutotiConicCap u0 u1 r d)) = 0)
    (hvol : ∀ X ∈ grutotiEdgeCells V e,
      volume (X ∩ grutotiConicCap u0 u1 r d) ≠ ⊤)
    (hcov : volume.real
        (⋃₀ ((fun X => X ∩ grutotiConicCap u0 u1 r d) '' grutotiEdgeCells V e)) =
      volume.real (grutotiConicCap u0 u1 r d)) :
    (grutotiEdgeCells V e).Finite ∧
      setSum (grutotiEdgeCells V e)
        (fun X => volume.real (X ∩ grutotiConicCap u0 u1 r d)) =
        volume.real (grutotiConicCap u0 u1 r d) := by
  have hfin : (grutotiEdgeCells V e).Finite := FINITE_EDGE_X2 V e u0 u1 hp hs he
  refine ⟨hfin, ?_⟩
  rw [p23_measure_setSum_biUnion hfin hmeas hpair hvol]
  exact hcov

/-! ### SF32 拆分波（2026-10-08）：桥件 `p23_grutoti_sum_volD_measure_facts`
的 4-合取 sorry 拆为三支真证私件 + 一支 hcov 精确定点 sorried 私件。桥本体
瘦身为纯组合（零 sorry）；hcov 单点覆盖债定点于 `p23_grutoti_cap_measure_cover`。
PA23 桥位 sorry 数不增（1 个 4-合取包 → 1 个单点覆盖目标）。 -/

/-- `rconeGt` 可测性（PA10:554-561 `measurableSet_rconeGt_p10` 的私拷——上游
private，PA23 不可 import；连续性件 `continuous_dot`/`continuous_rcone` 同款
逐字，proof 路线：开半空间原像）。 -/
private theorem p23_grutoti_rconeGt_measurable (v w : V3) (a : ℝ) :
    MeasurableSet (rconeGt v w a) := by
  have hcdot : Continuous fun x : V3 => (x - v) ⬝ᵥ (w - v) := by
    have h : Continuous fun x : V3 => inner ℝ (x - v) (w - v) :=
      (continuous_id.sub continuous_const).inner continuous_const
    have heq : (fun x : V3 => inner ℝ (x - v) (w - v)) =
        fun x : V3 => (x - v) ⬝ᵥ (w - v) := by
      funext x
      exact inner_eq_dot (x - v) (w - v)
    rw [← heq]
    exact h
  have hcont : Continuous fun x : V3 =>
      (x - v) ⬝ᵥ (w - v) - (dist x v * dist w v * a) :=
    hcdot.sub (by fun_prop)
  have hset : rconeGt v w a =
      (fun x : V3 => (x - v) ⬝ᵥ (w - v) - (dist x v * dist w v * a)) ⁻¹' (Set.Ioi 0) := by
    ext x
    simp only [rconeGt, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi, sub_pos]
  rw [hset]
  exact ((isOpen_Ioi).preimage hcont).measurableSet

/-- `grutotiConicCap = closedBall ∩ rconeGt` 可测：闭球 Borel（PA10:600 同款
`isClosed_closedBall`）交锥可测（`p23_grutoti_rconeGt_measurable`）。 -/
private theorem p23_grutotiConicCap_measurable (v0 v1 : V3) (r a : ℝ) :
    MeasurableSet (grutotiConicCap v0 v1 r a) :=
  (Metric.isClosed_closedBall).measurableSet.inter (p23_grutoti_rconeGt_measurable v0 v1 a)

/-- SF32 拆分波 hmeas 支（真证）：每条边胞与 cap 的交可测。路线：`X ∈
mcellSet V` 解出 witness `X = mcell i V ul ∧ barV V 3 ul`，`MEASURABLE_MCELL`
（PA10:585，公共件，全 k 无 ≤ 4 限制）交 `p23_grutotiConicCap_measurable`。
上游锚点：HL `MEASURABLE_MCELL`（URRPHBZ1.hl:673-682）。 -/
private theorem p23_grutoti_edge_cap_measurable (V : Set V3) (u0 u1 : V3) (e : Set V3)
    (r d : ℝ) (hs : saturated V) (hp : Packing V) :
    ∀ X ∈ grutotiEdgeCells V e, MeasurableSet (X ∩ grutotiConicCap u0 u1 r d) := by
  intro X hX
  obtain ⟨hXm, -⟩ := Set.mem_setOf_eq.mp hX
  obtain ⟨i, ul, hXeq, hbarul⟩ := Set.mem_setOf_eq.mp hXm
  rw [hXeq]
  exact (MEASURABLE_MCELL V ul i hs hp hbarul).inter
    (p23_grutotiConicCap_measurable u0 u1 r d)

/-- SF32 拆分波 hpair 支（真证；AJRIPQN 实例）：边胞族两两（cap 迹）零测。
路线：witness 归约（`p23_mcell_reduce` 把 `mcell i` 收进 `min i 4 ≤ 4`）后
二分 `volume (X ∩ Y)`——零测支走 `measure_mono_null`（cap 迹 ⊆ 胞交，外测度
单调，无需可测性）；正测度支则 `¬nullSet (胞交)` 喂 AJRIPQN（PA17:313，
上游 sorry 债自上游流动，桥内零新增 sorry）迫 `X = Y`，与 `X ≠ Y` 矛盾。
上游锚点：HL AJRIPQN（leaf_cell.hl:2132，PA17 装载）。 -/
private theorem p23_grutoti_edge_pairwise_null (V : Set V3) (u0 u1 : V3) (e : Set V3)
    (r d : ℝ) (hs : saturated V) (hp : Packing V) :
    ∀ X ∈ grutotiEdgeCells V e, ∀ Y ∈ grutotiEdgeCells V e, X ≠ Y →
      volume ((X ∩ grutotiConicCap u0 u1 r d) ∩
        (Y ∩ grutotiConicCap u0 u1 r d)) = 0 := by
  intro X hX Y hY hXY
  obtain ⟨hXm, -⟩ := Set.mem_setOf_eq.mp hX
  obtain ⟨hYm, -⟩ := Set.mem_setOf_eq.mp hY
  obtain ⟨i, ul, hXeq, hbarul⟩ := Set.mem_setOf_eq.mp hXm
  obtain ⟨j, vl, hYeq, hbarvl⟩ := Set.mem_setOf_eq.mp hYm
  have hredX : X = mcell (min i 4) V ul := by rw [hXeq, p23_mcell_reduce]
  have hredY : Y = mcell (min j 4) V vl := by rw [hYeq, p23_mcell_reduce]
  by_cases h0 : volume (X ∩ Y) = 0
  · -- 零测支：cap 迹 ⊆ 胞交，外测度单调
    exact measure_mono_null (fun z hz => Set.mem_inter hz.1.1 hz.2.1) h0
  · -- 正测度支：AJRIPQN 迫胞相等，与 X ≠ Y 矛盾
    have hne : ¬ nullSet (X ∩ Y) := h0
    have hmem45 : ∀ n : ℕ, n ≤ 4 → n ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by
      intro n hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    have hpos : ¬ nullSet (mcell (min i 4) V ul ∩ mcell (min j 4) V vl) := by
      rw [← hredX, ← hredY]
      exact hne
    obtain ⟨-, hcell⟩ := AJRIPQN V ul vl (min i 4) (min j 4) hs hp hbarul hbarvl
      (hmem45 _ (Nat.min_le_right i 4)) (hmem45 _ (Nat.min_le_right j 4)) hpos
    exact absurd (show X = Y from by rw [hredX, hredY, hcell]) hXY

/-- SF32 拆分波 hvol 支（真证；零 V-前提）：边胞与 cap 的交体积有限。路线：
cap ⊆ closedBall u0 r（`grutoti_cap_subset_closedBall`）⊆ closedBall u0 1
（`hr1`），外测度 `measure_mono` 单调 + `measure_closedBall_lt_top`
（PA23 region 块 :3395 同款用法）。-/
private theorem p23_grutoti_edge_vol_ne_top (V : Set V3) (u0 u1 : V3) (e : Set V3)
    (r d : ℝ) (hr1 : r ≤ 1) :
    ∀ X ∈ grutotiEdgeCells V e, volume (X ∩ grutotiConicCap u0 u1 r d) ≠ ⊤ := by
  intro X hX
  have hlt : volume (X ∩ grutotiConicCap u0 u1 r d) < ⊤ :=
    lt_of_le_of_lt (measure_mono fun z hz =>
      Metric.closedBall_subset_closedBall hr1
        (grutoti_cap_subset_closedBall u0 u1 r d hz.2)) measure_closedBall_lt_top
  exact ne_of_lt hlt

/-! ## B1 VX-forward bridge (tiwwfyq-coverage-scout §2; hcov 支 (iii)/(v) 弹药) -/

/-- B1 VX-前向桥（tiwwfyq-coverage-scout §2；hcov 支 (iii)/(v) 的 VX 半边）：
`X = mcell k V vl`（`2 ≤ k ≤ 4`）非零测且 `truncateSimplex 1 vl = [u0, u1]` 时，
`VX V X` 同时含 `u0` 与 `u1`。纯组装：`HDTFNFZ`（PA10:257，真证）给
`VX V X = V ∩ X`（cellParams ε-分案已在该件内完成——p.1 = 0 走
`LEPJBDJ_0`、p.1 ≥ 1 走 `LEPJBDJ`，即侦察配方第 1-3 步的整体；配方第 1 步
`HD_IN_MCELL` 在此路线不需要）；`LEPJBDJ`（PA11:472）给
`V ∩ X = setOfList (truncateSimplex (k-1) vl)`；截断复合
`TRUNCATE_TRUNCATE_SIMPLEX`（PA5:1440）+ ε-选取 `p23_trunc_init_len` 给
k-截断仍以 `[u0, u1]` 开头（k = 2 时即恒等，配方第 4 步的 `elV vl 1 = u1`
路线由列表前缀事实替代）。前提面注记：`¬nullSet X` 是 HDTFNFZ 的门，一步
给 `X ≠ ∅`；反向（X ≠ ∅ ⇒ 非零测）对 k ≥ 2 胞不是组装件，消费端须自带
`¬nullSet`（hcov/pivot 侧均有）。上游债（不新增）：`LEPJBDJ` 的 k = 2/3
内部分支经 PA11 `k2Case`/`k3Subset`（均 sorry），自上游流动。 -/
private theorem p23_vx_forward_bridge (V : Set V3) (vl : List V3) (k : ℕ) (X : Set V3)
    (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 vl)
    (hk : 2 ≤ k) (hk4 : k ≤ 4) (hX : X = mcell k V vl) (hnull : ¬ nullSet X)
    (htr : truncateSimplex 1 vl = [u0, u1]) :
    u0 ∈ VX V X ∧ u1 ∈ VX V X := by
  have hvlen : vl.length = 4 := hb.1
  have hXne : X ≠ ∅ := by
    intro he
    exact hnull (by rw [nullSet, he]; exact MeasureTheory.measure_empty)
  -- VX V X = V ∩ X = setOfList (truncateSimplex (k-1) vl)
  have hvx : VX V X = V ∩ X := HDTFNFZ (v := 0) hs hp hb hX hnull
  have hint : V ∩ X = setOfList (truncateSimplex (k - 1) vl) := by
    rw [hX]
    exact LEPJBDJ V vl k hs hp hb (by omega) hk4 (fun h0 => hXne (hX.trans h0))
  rw [hvx, hint]
  -- the k-truncation of vl still begins with [u0, u1]
  have htrw : truncateSimplex 1 (truncateSimplex (k - 1) vl) = [u0, u1] := by
    rw [TRUNCATE_TRUNCATE_SIMPLEX vl 1 (k - 1) (by omega) (by omega)]
    exact htr
  have h12 : 1 + 1 ≤ (truncateSimplex (k - 1) vl).length := by
    have := (p23_trunc_init_len (k - 1) vl (by omega)).2
    omega
  obtain ⟨t, ht⟩ := (p23_trunc_init_len 1 (truncateSimplex (k - 1) vl) h12).1
  rw [htrw] at ht
  refine ⟨?_, ?_⟩
  · show u0 ∈ truncateSimplex (k - 1) vl
    rw [ht]; simp
  · show u1 ∈ truncateSimplex (k - 1) vl
    rw [ht]; simp

/-- B1 桥的 `edgeX` 形：加 `u0 ≠ u1` 即得携边（PA2:381 `edgeX` 的定义就只有
`e = {u,v}` + 双端 ∈ VX + 异性三个合取支——无 mcellSet 合取支、无定向；
侦察附记的「edgeX 另一半」实为 `grutotiEdgeCells` 的 mcellSet 合取支，由
下一件一步补齐）。 -/
private theorem p23_vx_forward_bridge_edgeX (V : Set V3) (vl : List V3) (k : ℕ)
    (X : Set V3) (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 vl)
    (hk : 2 ≤ k) (hk4 : k ≤ 4) (hX : X = mcell k V vl) (hnull : ¬ nullSet X)
    (hne : u0 ≠ u1) (htr : truncateSimplex 1 vl = [u0, u1]) :
    {u0, u1} ∈ edgeX V X := by
  obtain ⟨h0, h1⟩ :=
    p23_vx_forward_bridge V vl k X u0 u1 hs hp hb hk hk4 hX hnull htr
  exact ⟨u0, u1, rfl, h0, h1, hne⟩

/-- B1 桥的整件形（hcov 支 (v) 的直接形状）：`X ∈ grutotiEdgeCells V {u0, u1}`
= `mcellSet V X`（由 `hX`/`hb` 定义展开）+ `edgeX` 半边（上一件）。 -/
private theorem p23_vx_forward_bridge_cell (V : Set V3) (vl : List V3) (k : ℕ)
    (X : Set V3) (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 vl)
    (hk : 2 ≤ k) (hk4 : k ≤ 4) (hX : X = mcell k V vl) (hnull : ¬ nullSet X)
    (hne : u0 ≠ u1) (htr : truncateSimplex 1 vl = [u0, u1]) :
    X ∈ grutotiEdgeCells V {u0, u1} :=
  ⟨⟨k, vl, hX, hb⟩,
    p23_vx_forward_bridge_edgeX V vl k X u0 u1 hs hp hb hk hk4 hX hnull hne htr⟩

/-- SF32 拆分波 hcov 支（2026-10-08，精确定点——桥件四支中唯一不可证支，
唯一 sorry 定点于此）：cap 的边胞迹测度覆盖恒等式。NEEDS（HL GRUTOTI.hl
测度覆盖链，TIWWFYQ/GLTVHUM/SLTSTLO1 巨型）逐点路线：(i) `grutoti_3mem`
（PA23:229 banked，GLTVHUM_lemma1 的 k = 3 特化）给 Voronoi 覆盖，而
`D ⊆ ball u0 1 ∩ rconeGt u0 u1 (hl/√2)` 落入覆盖域；(ii) `SLTSTLO1`
（PA15，banked，`p23_cover_C` :2045 同款用法）把每点归约到某
`mcell k V vl`（k ≤ 4，`barV V 3 vl`）；(iii) 逐点 `AJRIPQN`（PA17:313，
上游 sorry 债）把胞鉴定到携边族 `grutotiEdgeCells V e` 的成员
（`truncateSimplex 1 vl = [u0, u1]` 给出 `e ∈ edgeX`）；(iv) 于是
`D ⊆ ⋃₀ (迹)` 至一个零测余集，配 `p23_grutoti_edge_cap_measurable` 的
可测性与 measure_mono 收口。注记：`p23_region_data` 供给的是 mcell 分类
覆盖（B5），不解测度渴（见 `grutoti_sum_volD` docstring）；远点族上
`hl ≥ √2 ⇒ mcell4 = ∅`，走 mcell0/2/3（修正 GT-2 lane note）。 -/
private theorem p23_grutoti_cap_measure_cover (V : Set V3) (u0 u1 : V3) (e : Set V3)
    (r d : ℝ)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) (he : e = {u0, u1})
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hd0 : 0 < d) (hd1 : d < 1) :
    volume.real
        (⋃₀ ((fun X => X ∩ grutotiConicCap u0 u1 r d) '' grutotiEdgeCells V e)) =
      volume.real (grutotiConicCap u0 u1 r d) := by
  -- NEEDS: TIWWFYQ/GLTVHUM/SLTSTLO1 测度覆盖巨型（路线见上 docstring；
  -- 唯一新 sorry 定点，PA23 桥位 sorry 数不增）。
  sorry

/-- STATEMENT-FIX item 31 联动件（2026-10-09 方案 a1；SF32 拆分波瘦身
2026-10-08）：`grutoti_sum_volD` 新前提面的 capstone 供给桥——四条测度
前提打包，`GRUTOTI` 调用点一次 obtain。签名冻结不变；本体瘦身为纯组合：
hmeas 支 = `p23_grutoti_edge_cap_measurable`（MEASURABLE_MCELL 实例）、
hpair 支 = `p23_grutoti_edge_pairwise_null`（AJRIPQN 实例，上游债流动）、
hvol 支 = `p23_grutoti_edge_vol_ne_top`（cap ⊆ closedBall u0 1 有限界），
三支真证零 sorry；hcov 支 = `p23_grutoti_cap_measure_cover`——TIWWFYQ/
GLTVHUM/SLTSTLO1 测度覆盖巨型，唯一新 sorry 精确定点于彼（PA23 桥位
其 sorry 数不增）。无穷支路注记（修正 GT-2 lane note）：远点族上
`hl ≥ √2 ⇒ mcell4 = ∅`，走 mcell0/2/3。 -/
private theorem p23_grutoti_sum_volD_measure_facts (V : Set V3) (u0 u1 : V3)
    (e : Set V3) (r d : ℝ)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) (he : e = {u0, u1})
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hd0 : 0 < d) (hd1 : d < 1) :
    (∀ X ∈ grutotiEdgeCells V e,
        MeasurableSet (X ∩ grutotiConicCap u0 u1 r d)) ∧
      (∀ X ∈ grutotiEdgeCells V e, ∀ Y ∈ grutotiEdgeCells V e, X ≠ Y →
        volume ((X ∩ grutotiConicCap u0 u1 r d) ∩
          (Y ∩ grutotiConicCap u0 u1 r d)) = 0) ∧
      (∀ X ∈ grutotiEdgeCells V e,
        volume (X ∩ grutotiConicCap u0 u1 r d) ≠ ⊤) ∧
      volume.real
          (⋃₀ ((fun X => X ∩ grutotiConicCap u0 u1 r d) '' grutotiEdgeCells V e)) =
        volume.real (grutotiConicCap u0 u1 r d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact p23_grutoti_edge_cap_measurable V u0 u1 e r d hs hp
  · exact p23_grutoti_edge_pairwise_null V u0 u1 e r d hs hp
  · exact p23_grutoti_edge_vol_ne_top V u0 u1 e r d hr1
  · exact p23_grutoti_cap_measure_cover V u0 u1 e r d hs hp hu0 hu1 hne hhl he
      hr0 hr1 hd0 hd1

/-- HL GRUTOTI.hl:7962-7966: the wedge pivot — the vol-sum equals the
`vol D · dihX / 2π` sum. Needs grutoti_cell_vol per edge cell (the
¬nullSet hypothesis is discharged inside by the k-case analysis) and
grutoti_setSum_mul_div for the linear step. NEEDS-precision.
GT-2 lane note (2026-09-28): the honest route (HL §G/§H, 7441-7958) is now
mapped: (a) for EVERY edge cell X (u0,u1 ∈ VX V X) one first shows
k := (cellParams V X).1 ≥ 2 — the counting arm `i - 1 = 0` of §H: VX V X is a
set of ≤ k list points containing two distinct points; k ≤ 1 is impossible;
(b) for k ≥ 2 one shows `¬nullSet (X ∩ D)` — HL §H derives `F` from
`NULLSET (X ∩ D)` per k, using CONIC_CAP_INTER_CONVEX_HULL_4_GT_0
(Auto15:828, still sorried) for k = 3/4 and the region data for k = 2 —
this is the remaining blocker, shared with grutoti_cell_vol (GT-3);
(c) then `p23_setSum_congr` assembles the frozen identity from
`grutoti_cell_vol` pointwise. Junk safety: for k ≤ 1 / null cells the PA2
encoding gives dihX = 0 (`p23_dihX_of_nullSet`), and k ≤ 1 cells cannot carry
the edge at all, so no junk term enters the sum. CAVEAT for the future fill:
`cellParamsD V X [u0,u1]` may be epsilon-junk for edge cells whose param list
carries the edge REVERSED (`[u1;u0,…]` — its wedge is a genuinely different
set); HL §H handles this inside the case analysis, and the Lean fill must too.
grutoti_setSum_mul_div for the linear step. NEEDS-precision. -/
private theorem grutoti_pivot (V : Set V3) (u0 u1 : V3) (e : Set V3) (r d : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hd1 : d < 1) (he : e = {u0, u1})
    (hfin : (grutotiEdgeCells V e).Finite) :
    setSum (grutotiEdgeCells V e)
        (fun X => volume.real (X ∩ grutotiConicCap u0 u1 r d)) =
      setSum (grutotiEdgeCells V e)
        (fun X => volume.real (grutotiConicCap u0 u1 r d) *
          dihX V X (u0, u1) / (2 * Real.pi)) := by
  sorry

/-- HL GRUTOTI.hl:7983-8000: `0 < vol D` from `VOLUME_CONIC_CAP`
(marchal3; `vol (conic_cap u0 u1 r d) = 2/3 · π · r³ · (1-d)² …`-type formula,
positive for `0 < d < 1`, `0 < r`). STILL `sorry`, with an honest note
(2026-09-19): the statement as frozen is FALSE for the degenerate `u1 = u0`
(then `rconeGt u0 u0 d = ∅`, so `vol D = 0`); the caller `GRUTOTI` supplies
`hne : u0 ≠ u1` but the frozen private signature omits it. The fill route
under `u0 ≠ u1` is elementary — `D` contains the open ball
`ball (u0 + (r/2)·(u1-u0)/‖u1-u0‖, r·(1-d)/(4·(1+d)))` (cone/ball arithmetic
+ `volume` positivity of open balls) — port it together with the missing
hypothesis at merge. STATEMENT-FIX filed (2026-09-28 GT-2 lane):
`docs/statement-fix-proposals.md` item 18 + patch
`docs/statement-fix-proposals-patches/18-grutoti_volD_pos.patch` — add
`hne : u0 ≠ u1` (HOL: the goal lives under GRUTOTI1_concl's `~(u0 = u1)`,
GRUTOTI.hl:48-58; the frozen formula route is GT-1's
`ConicCapVolume.volumeConicCapPos`, which carries the same `hne`, and the
degenerate capsule is provably empty — ConicCapVolume `ccv_conicCap_empty`),
after which the fill is one line.
hypothesis at merge. -/
private theorem grutoti_volD_pos (u0 u1 : V3) (r d : ℝ) (hr : 0 < r) (hd : 0 < d)
    (hd1 : d < 1) (hne : u0 ≠ u1) : 0 < volume.real (grutotiConicCap u0 u1 r d) :=
  volumeConicCapPos hr hd hd1 hne

/-! ## Capstone -/

/-- HOL `GRUTOTI` (GRUTOTI.hl:60-8001): the dihedral angles of all Marchal
cells along a short edge sum to `2π`. Statement-identical to
`PackingAuto2.GRUTOTI1_concl`, which it discharges (`exact GRUTOTI …`) once
the sorried giants above are proved. -/
theorem GRUTOTI : ∀ (V : Set V3) (u0 u1 : V3) (e : Set V3), saturated V →
    Packing V → u0 ∈ V → u1 ∈ V → u0 ≠ u1 → hl [u0, u1] < Real.sqrt 2 →
    e = {u0, u1} →
    setSum {X | mcellSet V X ∧ e ∈ edgeX V X} (fun t => dihX V t (u0, u1)) =
      2 * Real.pi := by
  intro V u0 u1 e hs hp hu0 hu1 hne hhl he
  have hbar := grutoti_barV V u0 u1 hs hp hu0 hu1 hne hhl
  obtain ⟨c, r, d, hc0, hc1, hr0, hr1, hd0, hd1, hdc, _hcover⟩ :=
    grutoti_region V u0 u1 e hs hp hu0 hu1 hne hhl he
  have hvol := grutoti_volD_pos u0 u1 r d hr0 hd0 hd1 hne
  obtain ⟨hmeasF, hpairF, hvolF, hcovF⟩ :=
    p23_grutoti_sum_volD_measure_facts V u0 u1 e r d hs hp hu0 hu1 hne hhl he
      hr0 hr1 hd0 hd1
  obtain ⟨hfin, hsum⟩ := grutoti_sum_volD V u0 u1 e r d hs hp hu0 hu1 hne hhl he
    hr0 hd1 hmeasF hpairF hvolF hcovF
  have hpivot := grutoti_pivot V u0 u1 e r d hr0 hr1 hd0 hd1 he hfin
  have hlin := grutoti_setSum_mul_div (grutotiEdgeCells V e)
    (volume.real (grutotiConicCap u0 u1 r d)) (fun X => dihX V X (u0, u1)) hfin
  exact grutoti_concl_arith _ _ _ hvol hsum (hpivot.trans hlin)

end Kepler.Text
