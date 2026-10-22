/-
PackingAuto25: port of `scripts/packing/OXLZLEZ3.hl` (Flyspeck chapter
"packing / OXLZLEZ", T. Hales, 9038 lines; 6 `new_definition`s + 129-theorem
statement surface re-derived here — the file actually carries ~208
declarations: 6 defs + ~202 `prove_by_refinement` theorems + 2 tactic
helpers absorbed into proofs).

FILE MAP (the FINAL packing capstone)
  This is the last file of the packing chain: it proves `OXLZLEZ`,
  `!V. pack_nonlinear_non_ox3q1h /\ ox3q1h /\ packing V /\ saturated V ==>
  cell_cluster_inequality V`, i.e. the cell-cluster inequality, from the
  cc_v11 compressed-model case analysis (PackingAuto3/4: `CcV11`,
  `cc_bool_model_v11`, `cc_real_model_v11`, `GRHIDFA`).  Payload:
  (a) the leaf-ranking gadget: `s_leaf` (the set of leaves on a stem),
      `leaf_rank` (a cyclic azim-increasing parametrization of `s_leaf` by
      `0..n-1`), `gg_mcell`/`azim_mcell` (the gamma-weight and dihedral sums
      over the Marchal cells in one wedge), `cc_4` (wedge has a 4-cell);
  (b) `cc_data_v8`: the compression `cc_v11` of the geometric data of an
      edge `(u0,u1)` — the bridge object between geometry and the
      combinatorial cc_v11 model (PackingAuto3);
  (c) the wedge bookkeeping (CC_4_PROPS, CC_3_PROPS, CC_2_PROPS,
      MCELL{2,3,4}_*, EDGE_IMP_K23), the certified `real_model_*` inequality
      bank per wedge type (quarter, fhbv2, quqy, ztg4, azim1, gaz4/6/9,
      gamma_qx/8/8b/10/11, gamma10/11, pema/pemb, txq, tew, 008, cell23,
      3a/3b, gr, ox3q1h_merge), the three merged numeric inequalities
      IXPOTPA/TXQTPVC/TEWNSCJ, and the endgame: `cc_real_model_data` →
      `CELL_CLUSTER_ESTIMATE_PROPS` → `OXLZLEZ` →
      `PACKING_CHAPTER_MAIN_CONCLUSION` (via `RDWKARC` + `TSKAJXY`).

ENCODING NOTES
  - HOL `real^3` <-> `V3` (Kepler.Geom); `packing` <-> `Packing`;
    `saturated V` <-> `saturated V` (Kepler.Statement); `sum S f` <->
    `setSum` (PackingAuto2:124); `CARD` <-> `Nat.card`/`Set.ncard`.
  - `HAS_SIZE n` <-> `HasSizeP25 s n := s.Finite ∧ s.ncard = n`;
    `IMAGE f (:num) = s_leaf V ul` <-> `f '' Set.univ = s_leaf V ul`.
  - `EL i ul` <-> `elV ul i` (PackingAuto2:131, junk `0`); `SUC i` <-> `i + 1`.
  - `leaf`/`cc_ke`/`cc_cell`/`cc_uh`/`chi_msb` <-> PackingAuto18
    `leaf`/`ccKe`/`ccCell`/`ccUh`/`chiMsb`; `mcell*`, `mcell_set`, `edgeX`,
    `wedge_ge`, `gammaX`, `lmfun`, `critical_weight`, `critical_edgeX`,
    `critical_edge_y`, `beta_bump_v1`, `dihX`, `bump`, `wtcount*_y`, `radV`,
    `mxi`, `hl`, `barV`, `truncate_simplex`, `initial_sublist`, `setSum`,
    `NULLSET` <-> PackingAuto2 kit.
  - cc_v11 model: `CcV11`, `cc_*_v11`, `periodic` <-> PackingAuto3
    (`GRHIDFA_concl` is the interface consumed by `OXLZLEZ`).
  - `pack_nonlinear_non_ox3q1h`, `tsk_hyp` <-> PackingAuto21 (opaque);
    `TSKAJXY` <-> PackingAuto21:1114; `RDWKARC_concl`/`OXLZLEZ_concl` <->>
    PackingAuto2 `*_concl` (sorried conclusions).
  - real toolkit: `dih_x/dih_y/eta_y/gamma3f/delta_x/h0cut` <-> SphereKit +
    PackingAuto21 (`dihXf/dihY/eta_y/gamma3f/deltaX/h0cut`; the sphere.hl kit
    is single-sourced in `Kepler.Text.SphereKit`, atn2-merge plan §5.4 —
    the hub's duplicate defs are gone, and this file imports that module
    explicitly).  `vol4f`/`gamma4fgcy` remain as local `_p25` copies here
    (kept per plan §3; PA20's unsuffixed versions are not re-exported).
  - `_p25` opaque stand-ins (NEEDS upstream bodies):
    `ox3q1hP25` (Oxl_def.hl `ox3q1h`: the certified 4-cardinality gg-sum
      inequality of the cc_v11 real model — inside `cc_real_model_v11`'s
      `n = 4` conjunct; PackagingAuto3 has it only inline),
    2026-10-13 wave: `rad2XP25`/`rad2YP25` left this list — `rad2XP25` is
      re-pointed to the verbatim `IneqClosureDefs.rad2X` (sphere.hl:271-273),
    `beta_bumpA_yP25` (Merge_ineq.hl `beta_bumpA_y`, the y-space bump),
    `c2089/c1946` need certified interval bounds (`Flyspeck_constants.calc`).
  - `MOD_INJ1_ALT` is `MOD_INJ1_ALT_p25` here (name taken by
    PackingAuto3:445 with an equivalent statement).
-/

import Kepler.Text.Polytope
import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto3
import Kepler.Text.PackingAuto4
import Kepler.Text.PackingAuto18
import Kepler.Text.PackingAuto21
import Kepler.Text.SphereKit
import Kepler.Statement
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## Opaque / copied upstream constants (`_p25`; see header) -/

/-- HOL `ox3q1h` (Oxl_def.hl): the certified inequality bank for the
4-cardinality quarter case of the cc_v11 model.  Its content appears as the
`(cc_card_v11 cc = 4 ∧ qu-pattern) → 0 ≤ ∑ cc_gg_v11` conjunct of
`cc_real_model_v11` (PackingAuto3.lean:162); the global constant is not
ported elsewhere.  NEEDS: exact Oxl_def.hl body. -/
def ox3q1hP25 : Prop := sorry

/-- HOL `rad2_x` (sphere.hl:271-273): squared circumradius from squared edge
lengths, `rho_x / (4 * delta_x)`.  2026-10-13 wave: the former opaque stub is
re-pointed to the verbatim body `IneqClosureDefs.rad2X` (on this file's
import closure) — same shape as the MERGE-INEQ charter §2.1 `eta_y`
precedent; unlocks the `rad2_y` disjunct refutation in
`TXQTPVC_MERGED` (`rad2YP25 = yOfX rad2X` is now `rfl`). -/
noncomputable def rad2XP25 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rad2X x1 x2 x3 x4 x5 x6

/-- HOL `rad2_y` (sphere.hl:541): `y_of_x rad2_x` — rad2_x at squared
lengths.  (Only used through `radV {...}^2`, TSKAJXY2.hl:455.) -/
noncomputable def rad2YP25 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  rad2XP25 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `beta_bumpA_y` (Merge_ineq.hl): the y-space bump correction of
GG_MCELL_GENERAL.  NEEDS: exact Merge_ineq.hl body. -/
noncomputable def beta_bumpA_yP25 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := sorry

/-- HOL `vol4f` (sphere.hl:568); PackingAuto20.lean:105 verbatim. -/
noncomputable def vol4fP25 (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
      solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3) -
    (8 * mm2 / Real.pi) *
    (f (y1 / 2) * dihY y1 y2 y3 y4 y5 y6 +
      f (y2 / 2) * dihY y2 y3 y1 y5 y6 y4 +
      f (y3 / 2) * dihY y3 y1 y2 y6 y4 y5 +
      f (y4 / 2) * dihY y4 y3 y5 y1 y6 y2 +
      f (y5 / 2) * dihY y5 y1 y6 y2 y4 y3 +
      f (y6 / 2) * dihY y6 y1 y5 y3 y4 y2)

/-- HOL `gamma4fgcy` (sphere.hl:566); PackingAuto20.lean:122 verbatim. -/
noncomputable def gamma4fgcyP25 (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) : ℝ :=
  volY y1 y2 y3 y4 y5 y6 - vol4fP25 y1 y2 y3 y4 y5 y6 f

/-- HOL `HAS_SIZE n` (used ~40 times below). -/
def HasSizeP25 (s : Set V3) (n : ℕ) : Prop := s.Finite ∧ s.ncard = n

/-! ## Leaf-cell kit (`_p25` copies from PackingAuto18.lean; `chiMsb` and
`upsX` used to be verbatim twins here too and were deleted at the atn2 merge
(plan §5.4) — both now come from `Kepler.Text.SphereKit`.  The rest of the
section is PA18-lane-duplicated but not SphereKit material; `MCELL2_SUBSET_AFF_GE`
is *not* redeclared here (PA18's and PA21's statements differ, plan §6.1).) -/

/-! `leaf`（leaf_cell.hl:17）与 cc_* 块（`cc_pe_exists`/`ccPe1`/`ccPe2`/
`cc_uh_exists`/`ccUh`/`ccKe`/`ccCell`，leaf_cell.hl:1052-1142）已改为委托
`Kepler.Text.PackingAuto18`（2026-09-21 骨架化：该块在两文件 verbatim 重复，
导致 PA18 ⊕ PA25 无法共存于同一 import 环境，Assembly 脊柱需要二者）。 -/

/-! ## FILL-ROUND STATUS (2026-09-28 wave: 155 -> 144 sorries)

Filled this round (all self-contained, no unproved upstream dependencies):
`MCELL3_CONVEX_HULL`, `MCELL4_CONVEX_HULL`, `MCELL3_EXTREME_CARD`,
`MCELL4_CARD4`, `DIST_I_SUCI`, `s_leaf_collinear`, `LEAF_RANK_COLLINEAR`,
`LEAF_RANK_AZIM_INJ`, `LEAF_RANK_AZIM_NZ`, `S_LEAF_SYM`, `NOT_COPLANAR_AFF_3`
(+ private helpers `p25_collinear3_eq_dist`, `p25_take_cancel`,
`p25_truncate_take`, `p25_null_conv3`, `p25_set4_dedup`, `p25_leaf_swap`).

Remaining sorries, classified:
  - 机械未填 (defs-level, doable next round): none identified beyond the above.
  - 卡具名桥 / 上游未证引理 (named-bridge blockers):
    `GAMMAX_NO_BETA` (needs Bump-lane `MCELL_BUMP_0`: betaBumpV1 = 0 for
      k < 4 cells), `radius_le_circumradius(_all)` (needs PA2
      `OAPVION2_concl`, itself unproved: radV-circumcenter bridge),
      `S_LEAF_BOUNDED`/`S_LEAF_FINITE`/`MCELL_AVOID_LEAVES` (need the
      leaf chord bound dist <= 2 * hl, i.e. the circumradius bridge),
      `LEAF_RANK_REUHADY`/`c_4_azim_mcell_dih_y`/`real_model_sum_azim`
      (need REUHADY / GRUTOTI lanes), `cc_4_*`/`CC_4_*`/`K3_*/K4_*`/
      `NO_4CELL_IMP_K3`/`CC_CELL_*`/`LEAF_RANK4_*`/`cc_4_UL`/`CC_3_SUM_*`/
      `LEAF_RANK_BIJ`/`MCELL_WEDGE_UNIQUE`/`MCELL_IN_WEDGE`/
      `LEAF_RANKING_LEMMA`/`LEAF_RANK_PROPS`/`CELL_CLUSTER_ESTIMATE_*`/
      `OXLZLEZ`-adjacent assembly (need PA18 `cc_uh_exists`/`cc_pe_exists`
      and the wedge-uniqueness chain), `HL_IMP_BARV`/`AFF_DEP_COPLANAR`
      (need full voronoi-face dimension theory),
      `coplanar_delta_y`/`RADV_ETAY`/`ETA_Y_LEMMA(2)`——2026-10-13 四件已转真
      （coplanar_delta_y 经 PA18 `delta_delta_x`+`POS_EQ_NOT_COPLANANR`+
      `coplanar_eq_coplanar_alt` 全 rw 链；RADV_ETAY 经显式外心见证+Gram 行列式
      `p25_radv_etay_core`；ETA_Y 双件经 `hl=radV∘setOfList`+`pow` 单调）,
      `MCELL4_REPARAM` (permuted-prefix barV transfer),
      （2026-10-12 更新：`ORDER_AZIM_SUM2Pi0` 已转真——azim 链算术
      `AZIM_BASE_SHIFT_LE`+`azim_compl` 望远镜；`S_LEAF_IN_WEDGE_GE`/
      `MCELL4_LEAF2`/`MCELL4_LEAF3`/`MCELL4_FI_EL`/`MCELL4_FI`/
      `MCELL4_BARV_FI` 同波转真）,
      `MCELL{2,3}_DIHX*`/`MCELL3_DOMAIN`/`MCELL4_*`-cell-structure cluster
      (need the VX/cellParams characterization of edgeX/dihX).
  - 卡外部锚 (certified banks / external anchors, skip):
    `rad2XP25`/`ox3q1hP25`/`beta_bumpA_yP25` opaque defs; `GDRQXLGv3`,
    `EDGE_LE_2RAD`, `RAD2_Y_SQRT8`, `TSKAJXY_3`, `JSPEVYT_EXPLICIT`,
    `JSP_BOUNDS`, `leaf_CIHTIUM`, `real_model_*` bank (azim_c4, gamma_qu,
    fhv2(2), gckb, ox3q1h_merge, gamma3f-cluster, quqy(2), ztg4, azim1,
    gaz4/6/9, gamma_qx, g_qxd, gamma8/b, gamma10/11, azim2, pema/pemb,
    txq, tew, 008, cell23(2), GAMMAX_008a/b, 3a/3b, gr, cell23_008),
    `MCELL4_DOMAIN`, `real_model_azim_c4`, `CC_4_BETA_BUMP_EXPLICIT/0`,
    `critical_weight*`, `CC_2_PROPS`, `MCELL2_CRITICAL_WEIGHT1`,
    `MCELL3_CRITICAL_WEIGHT`, `MCELL3_008`, `real_model_008`,
    `gamma4fgcy_POS`, `c2089`, `c1946`, `IXPOTPA/TXQTPVC/TEWNSCJ_MERGED`,
    `CC_3_PROPS`, `WEDGE3_Y4`, `RAD_PI_IMP_WEDGE4`, `CELL_CLUSTER_N_LE_1`,
    `PACKING_CHAPTER_MAIN_CONCLUSION` (TSKAJXY assembly merge),
    `REUHADY` (PackingAuto24 lane).
  - 疑似假陈述: none found this round (GAMMAX_NO_BETA is faithful to
    OXLZLEZ3.hl:797; its proof needs the upstream MCELL_BUMP_0 lemma).

FILL-ROUND STATUS r2 (2026-09-29 wave: 144 -> 137 sorries)

Filled this round (7):
  `PACKING_CHAPTER_MAIN_CONCLUSION` (the HOL Oxlzlez assembly goes through
    VERBATIM: `RDWKARC_concl` + `OXLZLEZ` + pointwise `TSKAJXY` with the
    `hnl` bank antecedent — PA21:1407's capstone IS `TSKAJXY_statement`
    pointwise once the bank hypothesis is supplied; the "conclusion-surface
    mismatch" in the r1 note was only the antecedent),
  `GAMMAX_NO_BETA` (new import: `Kepler.Text.PackingAuto4` — `MCELL_BUMP_0`
    was closed in PA4 wave2; `betaBumpV1`/`betaBump` are body-identical),
  `S_LEAF_BOUNDED`/`S_LEAF_FINITE` (r1 said "circumradius bridge" — that
    bridge now exists: PA2 `OAPVION2_concl` closed wave2; leaf chord bound
    = 2 * radV via the circumcenter triangle, triple aff-independence via
    `s_leaf_collinear` + private `p25_not_affdep3`),
  `MCELL_AVOID_LEAVES` (HOL OXLZLEZ3.hl:1081 measure argument verbatim:
    finite leaf planes + `NULLSET_AFF_2_1`),
  `radius_le_circumradius(_all)` (same bridge; private
    `p25_affdep4_coplanar` = forward half of `AFF_DEP_COPLANAR`).
New helpers (all fully proved): `p25_not_affdep3`, `p25_mem_affSpan3`,
  `p25_affdep4_coplanar`.
Remaining blockers unchanged from the r1 lists above, except:
  - `AFF_DEP_COPLANAR` backward (Coplanar + 4 distinct -> affineDependent)
    is the ONLY open half; route: `AffineIndependent.card_le_card_of_subset_
    affineSpan` (Mathlib FiniteDimensional.lean:252) with S.toFinset card 4
    vs the Coplanar witness triple. `p25_affdep4_coplanar` is its forward
    half and is done.

FILL-ROUND STATUS r3 (2026-10-13 wave: 119 -> 116 sorries, MERGE-INEQ channel)
  - `rad2XP25` stub re-pointed to `IneqClosureDefs.rad2X` (def-faithful,
    statement unchanged; unlocks the rad2 disjunct refutation).
  - `IXPOTPA_MERGED`/`TXQTPVC_MERGED` 转真（axiom 面标准三）: 消费 PA21
    wave-2c 的 `mi_dih_gt_pi2`/`mi_lindihpi_lt_y`/`mi_lindihpi_gt_y`/
    `mi_gamma3_x_gamma3f` (merge_ineq.hl:2761/2783/2825/4101) + 本文件
    `p25_gamma23Full8X_yOfX_eq` 桥 + 数值臂 `c2089`/`c1946` + bank 投影
    `proj_bank_IXPOTPA`/`proj_bank_TXQTPVC`。
  - `TEWNSCJ_MERGED` 转真（SF-41 桥：PA3 `a_spine5`/`b_spine5` 重指向
    sphere.hl:632/634 逐字体，见其 docstring）；其余 blocker 面不变。

FILL-ROUND STATUS r4 (2026-10-13 wave: 116 -> 114, 楔形证书面/LEAF_S_LEAF 装配)
  - `MCELL4_LEAF_S_LEAF` 转真（装配级，零新增记账行）: PA18 冻结版 `CFFONNL`
    （真证，内部经规则⑤白名单流动 `pa18_ccCell_swap`/`ZWVCBMN`）以
    `X := mcell4 V ul` 二分装配——等式支经 PA17 `AJRIPQN`+`CC_KE_34`/
    `ZASUVOR`/`cc_uh_exists` 钉派单值 4，不等式支恰为其 `hne` 反得爆炸；
    楔边证书 `HDTFNFZ`+`LEPJBDJ`(k=4) 内联 + 私件 `p25m_list4_eq`/
    `p25m_card4_ne`。`S_LEAF_CARD2`/`LEAF_RANK_ONTO` 随之零在库欠件。
  - `MCELL4_DOMAIN` 转真（装配级）: `CC_4_PROPS` 十二合取全数消费，delta
    合取与 `coplanar_delta_y` 逐字同形直接实例化；记账件 `CC_4_PROPS`
    （上游 PA18 `MCELL4_EDGE_FIRST`/`STEM_EDGEX` edge-rigidity kit 未落地）
    与 `GDRQXLGv3`（radV² 桥）消费面在案，本体不动。

FILL-ROUND STATUS r5 (2026-10-13 wave: 114 -> 111, GDRQXLGv3 解析桥 + rad2 双件)
  - `GDRQXLGv3` 转真（M4 车道判词兑现：OAPVION2+代数，独立可装、不依赖
    edge-rigidity GIANT）: `¬Coplanar` 经 `p25g_affdep4_coplanar` 给
    `¬affineDependent`；Cayley–Menger 行列式 `deltaX > 0` 经 PA18
    `POS_EQ_NOT_COPLANANR`+`delta_delta_x`；Gram 矩阵（差向量内积组）行列式
    Δ>0，显式 Cramer 见证 q = (t₁•e₁+t₂•e₂+t₃•e₃)+ᵥv₀（tᵢ=nᵢ/2Δ）经
    `OAPVION3_concl` 认定 circumcenter、`OAPVION2_concl` 取
    `radV = dist q v₀`；平方后由多项式恒等式 `deltaX = 4Δ`、
    `rhoX = 4·Σgᵢ·nᵢ`（纯 ring）收口——与 `p25_radv_etay_core` 三点
    Heron 版同构，自身零债。
  - 新私件两枚（全零债）: `p25g_mem_affSpan3`/`p25g_affdep4_coplanar`
    （`p25_mem_affSpan3`/`p25_affdep4_coplanar` 的内联副本——原件定义在
    本文件后段，Lean 无前向引用；主体逐字未动）。
  - `MCELL4_DOMAIN` 对 `GDRQXLGv3` 的消费随本体升真（rad2_y 支出账，
    消费处代码一字未动）；`CC_4_PROPS` 记账仍在账（上游 edge-rigidity
    kit 未动）。本波零新增记账行。
  - `EDGE_LE_2RAD` 转真（纯代数零债）: RHUFIIB 型多项式恒等式
    `rhoX·upsX = chi_x² + 4·deltaX·x4x5x6`（chi_x = sphere.hl:142 逐字，
    纯 ring 展开）+ 面半弦 `4x5x6 − upsX = (x5+x6−x4)²`（Heron 面式纯
    ring）+ 面外接圆不等式 `x4x5x6/upsX ≤ rhoX/(4·deltaX)`（div_le_div_iff₀
    交叉相乘）——即 HOL OXLZLEZ3.hl:599 的 `4·eta_x² ≤ 4·rad2_x` 通往
    `x4 ≤ 4·rad2_x` 的代数直达线。
  - `RAD2_Y_SQRT8` 转真（零债）: `deltaY`/`rad2YP25` 定义性展开 + `(√8)² = 8`
    （`Real.mul_self_sqrt`）+ `UPS_X8_POS`（本文件真件）直接消费
    `EDGE_LE_2RAD`——WEDGE3_Y4 的 rad2 支自此就绪。
  - 本地预算: `GDRQXLGv3` 单件声明级 `set_option maxHeartbeats 25000000 in`
    （六变量 degree-4 ring 核 ×5 + field_simp ×3 超出文件级 5M；
    陈述与签名一字未动）。

FILL-ROUND STATUS r6 (2026-10-13 wave: 100 -> 97, 楔形 3-cell 面三连)
  - `NO_4CELL_IMP_K3` 装配级转真（HOL OXLZLEZ3.hl:3705 同构）: `k = 4` 反证
    经 `K4_CC_WI_ALT`/`K4_CC_WIM`（胞入楔）+ PA18 `STEM_EDGEX`（茎边入胞
    edgeX）+ `cc_uh`/`ccCell` 定义改写撞 `hno4`；`k = 3` 双胞入楔取
    `K3_CC_WI_ALT`/`K3_CC_WIM_ALT`（b-侧指标经 `F_SUC_PRE` 周期回卷）；互异
    取 PA18 `FUEIMOV_3`（首两点相等 ⟹ 共线撞 `hnc`）。债面 = PA18
    `K3/K4` 家族 + `STEM_EDGEX` + `FUEIMOV_3`（leaf_cell edge-rigidity kit，
    PA18 车道在案）。既有消费面 `p25m_cc3_wit`/`p25m_cc3_wit_b` 随本体升真。
  - `WEDGE3_Y4` 装配级转真（HOL OXLZLEZ3.hl:4388 同构；dih 支收官）:
    三分 witness——`pi ≤ azim` 与 `2√2 < d` 两枝取 `√8`（delta 支 =
    `proj_bank_FWGKMBZ`；dih 支 = 新 dih 单调 kit + `DIHV_EQ_DIH_Y_4PT_B` +
    `DIHV_LE_AZIM`；`delta_y(d) ≥ 0` 由 `DELTA_Y_POS_4POINTS_B` 无条件给出；
    rad2 支 = `RAD2_Y_SQRT8`），末枝（`azim < pi ∧ d ≤ 2√2`）取 `d` 本身，
    rad2 ≥ 2 经 `coplanar_delta_y` + `GDRQXLGv3` + `RAD_PI_IMP_WEDGE4`
    反证撞 `hno4`。债面 = `RAD_PI_IMP_WEDGE4`（本文件在案）。
  - 新 dih 单调 kit 七枚（全零债，真证）: `p25w_atn2_eq_arctan`（atn2 右半
    平面分支消解）、`p25w_delta_inv`（判别式不变量 `P² + 4x1·Δ = const`，
    纯 ring）、`p25w_dX4_sub`/`p25w_dX_mid`（仿射差 + 中点恒等式，纯
    ring）、`p25w_ratio_le`（比值比较，正分子支 `abs_le_of_sq_le_sq'`）、
    `p25w_dihXf_mono_x4`/`p25w_dihY_mono_y4`——即 HOL
    `Tame_inequalities.DIH_X_MONO_LT_4` + `dih_y_mono`（CUXVZOZ.hl:3206）的
    本文件解析版（纯代数，无微积分），可供 TSKAJXY 侧单调需求复用。
  - `CC_3_PROPS` 装配级转真（HOL OXLZLEZ3.hl:5908 同构，三十三合取全数）:
    `NO_4CELL_IMP_K3` 分派 + `WEDGE3_Y4` 收口 + `LEAF_RANK_REUHADY`
    （azim 塌缩，在案 sorried）+ 真件 `LEAF_DOMAIN`/`CC_CELL_NOT_NULLSET`/
    `ZASUVOR`/`BumpP4.MCELL_BUMP_0`（k = 3 胞 bump 归零）+ `cc_uh_exists`
    见证。债面 = 上述两件 + `LEAF_RANK_REUHADY`。
  - 既有件搬移（陈述逐字未动，字节级一致）: `EDGE_LE_2RAD`/`RAD2_Y_SQRT8`
    自 Backfill 段上移至 `WEDGE3_Y4` 之前（Lean 无前向引用；消费面
    `MCELL4_DOMAIN` 等不受影响）。
  - 新雷区沉淀: ① 本 Mathlib 快照改名族——`le_or_lt`→`le_or_gt`、
    `lt_or_le`→`lt_or_ge`、`div_le_div_iff`→`div_le_div_iff₀`（带 0< 参数）、
    `div_le_div_right` 已消失、`sq_neg`→`neg_sq`、`push_neg` deprecated；
    ② `rw [L (by tac)]` 内嵌 by-块在 pattern-metavariable 未解时即报
    unsolved goals——提为前置 have；③ tactic 参数内 `_` 占位不与目标联解；
    ④ 跨行 term-`by` 块（续行缩进低于 by 所在列）解析断裂；⑤
    `GBEWYFX`（`l[i]!` 记法陈述）在 getD-归一上下文中应用会 whnf 爆心跳
    （10M 不够）——改用 `LEAF_DOMAIN` 首合取支（同为 ¬Collinear3）；
    ⑥ `Collinear3` 为 def，set-重写前须 `show Collinear ℝ ({...})`；
    ⑦ 全量 `simp [elV]` 换自备 rfl 三引理 `simp only [eV0, eV1, eV2]`。

FILL-ROUND STATUS r8 (2026-10-13 收官波: 90 -> 89, RAD_PI_IMP_WEDGE4 转真):
  - `RAD_PI_IMP_WEDGE4` 转真（探针车道 P4rpi 全程验证后移植，~420 行 kit）：
    非共面支 = 维数夹逼（`Coplanar` 第 4 点入 `{u0,u1,w1}` 平面向量 span，
    `azim_frame_spec` 极坐标 + `Real.sin_eq_zero_iff` + 值域夹逼收口
    azim ∈ {0,π}，mirror-of-Planarity 私件）；楔包含支 = `affGe` 2-2 ⊆
    `wedgeGe`（LocalAuto5 `WEDGE_GE_EQ_AFF_GE` ⊆ 方向移植，mirror-of-
    LocalAuto5，闭包不含 LocalAuto5 故本件重述）；barV 支 = `leaf V [u0,u1,f i]`
    的 `barV V 2` 子表下降 + 四元表 voronoi 面 = 外心单点（正交唯一性 +
    `vectorSpan = ⊤` + `affDim` 单点收口，`CIRCUMCENTER_IN_VORONOI_SET`
    供非空）；零测 = `ZWVCBMN`；edgeX = `BumpP4.MCELL4_EDGE`。
    `NOT_COPLANAR_AFF_3`/`LEAF_RANK_LEAF` 上移至 kit 之前（无前向引用）。
    消费的具名记账兄弟：无新增（`MCELL4_CONVEX_HULL`/`ZWVCBMN`/
    `BumpP4.MCELL4_EDGE`/`CONVEX_HULL_4_SUBSET_AFF_GE_2_2` 均为在库真叶）。
  - `critical_weight_wtcount6_y` 二次止损维持记账（CARD_INSERT_INTER 六步
    剥离 kit 已在探针车道 P4rpi 成型至最后 `split_ifs` 对齐：15 对互异事实、
    `p25rpi_critEdge_mem`/`p25rpi_critEdge_count` 全部走通，唯 final
    numerical-goal 的 finisher（rfl/omega/decide/norm_num/simp）全部意外
    失败待查——纯 ℕ 数值等式全部 tactic 失败为本次新雷区候选；
    接续点 = 探针文件 /tmp/p4rpi/lean/Kepler/Text/P4rpiProbe.lean）。

FILL-ROUND STATUS r9 (2026-10-16 wave: 87 -> 86, critical_weight_wtcount6_y 转真):
  - `critical_weight_wtcount6_y` 转真（finisher 落地，P4rpiMini2 配方在克隆
    /tmp/p4rpi 全程验证后移植）：新私件 `p25rpi_mem4`/`p25rpi_sub4`/
    `p25rpi_mem6`/`p25rpi_wtcount6_core` 六步 `CARD_INSERT_INTER` 剥离，
    ∉-合取项走 `simp only [nK, not_false_iff, and_true]`（`rw [nK]` 撞 False
    陷阱），末尾 `unfold wtcount6Y wtcount3Y; split_ifs <;> omega` 收口；
    六边链 ∩ 临界边集的集合等式由 16 分支枚举（对角支 `absurd rfl hpq`，
    其余 `simp [Set.pair_eq_pair_iff, hu01..hu34]`；纯 rfl-梯子撞 subst
    方向不定——新雷区候选）。
  - r8 雷区「0+1+1+1+1+1+1 = 1+1+1+(1+1+1) 双侧为 6 却 rfl/omega/decide/
    norm_num 全拒（疑卡死 mvar）」破解 = `congrArg` 绕开：`criticalWeight`
    先 rfl-化为 `1 / ((criticalEdgeX …).ncard : ℝ)`，`rw` 集合等式后把
    `ncard = wtcount6Y` 等式整只推过 `Nat.cast`——分式两侧的 ℕ 求和从不
    展开，卡死 mvar 的数值 finisher 根本不被调用。
  - 消费的具名记账兄弟：无新增（`CC_4_PROPS`/`LEAF_DOMAIN`/
    `LEAF_RANK_SUC_INJ`/`critical_edgeX_critical_edge_y`/`BumpP4.MCELL4_EDGE`
    均为在库件；`GG_MCELL_QUARTER` 的 hgw 消费位自动升零债）。
    剩余裸 sorry = 86（计数口径：行首裸 `sorry`）。

FILL-ROUND STATUS r7 (2026-10-13 wave: 97 -> 90, M4 车道批量装配·骨架式预消费)
  - 装配链 7 件转真（`cc_4_cc_ke4`→`cc_4_UL`→`CC_4_PROPS`→`cc_4_cc_cell`/
    `c_4_azim_mcell_dih_y`/`real_model_azim_c4`/`GG_MCELL_QUARTER`），全部
    骨架式预消费：消费的具名记账兄弟 = PA18 `MCELL4_EDGE_FIRST`（E8 车道在
    攻，落地时 `cc_4_cc_ke4`/`cc_4_UL`/`CC_4_PROPS`/`cc_4_cc_cell` 自动升零债）+
    本文件 `K3_CC_WI_ALT`/`MCELL4_FULL_WEDGE`/`K4_CC_WI_ALT`/
    `CC_CELL_WEDGE_MATCH_UH`/`MCELL4_GG`/`MCELL4_AZIM_LT_PI`/`LEAF_RANK_REUHADY`
    /`critical_weight_wtcount6_y`/`CC_4_BETA_BUMP_0`（兄弟翻转各自自动升零债）。
  - 关键新私件 `p25m_coplanar_hull_null`（零债）：Coplanar t → hull Haar 零测
    （affineSpan_le_of_subset_coe + addHaar_affineSubspace），CC_4_PROPS 的
    ¬Coplanar 合取由 `mcell4` 空支+零测反推。
  - 装配级技巧沉淀：`MCELL4_EDGE_FIRST` 见证表 getD 槽与目标 `elV` 槽不
    定义等价（vl 不透明）——所有 hnc/hr/hw 类前提先 `simp only [elV, ← hv0,
    ← hv1]` 改写再 exact；`f (i % n)` 必须带括号（`f i % n` 解析为 `(f i) % n`
    爆 HMod V3 ℕ）；bank 盒约束的 y5/y6 与 `MCELL4_DOMAIN` 合取序错位
    （y5=d(u1,f(i+1)) 在合取 11-12 而非 9-10）。
  - `RAD_PI_IMP_WEDGE4` 两波不下 2-strike 止损（本件 docstring 记账）：楔
    包含支与非共面支各卡一件闭包外 kit（LocalAuto5 的 WEDGE_GE_EQ_AFF_GE /
    Planarity 的 zOf 私件），五条支线侦察已走通、路线图写入 docstring。
  - `critical_weight_wtcount6_y` 一波止损（六边剥离计数需 15 对两两互异 +
    符号 if 对齐，预算不济；`GG_MCELL_QUARTER` 已按预消费模式吃其记账位）。

-/

/-! ## DEFINITIONS -/

/-- HOL `s_leaf` (OXLZLEZ3.hl:24): set-valued rendering — the leaves on the
stem `[EL 0 ul, EL 1 ul]` whose cc-cell dispatch is 4 (either stem order). -/
def s_leaf (V : Set V3) (ul : List V3) : Set V3 :=
  {u | leaf V [elV ul 0, elV ul 1, u] ∧
    (ccKe V [elV ul 0, elV ul 1, u] = 4 ∨ ccKe V [elV ul 1, elV ul 0, u] = 4)}

/-- HOL `gg_mcell` (OXLZLEZ3.hl:27): gamma-weight sum over the Marchal cells
in the wedge `wedge_ge u0 u1 (f i) (f (SUC i))`. -/
noncomputable def gg_mcell (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) (i : ℕ) : ℝ :=
  setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
    X ⊆ wedgeGe u0 u1 (f i) (f (i + 1))} fun X =>
      gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {u0, u1} X

/-- HOL `azim_mcell` (OXLZLEZ3.hl:32): dihedral-angle sum over the same
wedge cell set. -/
noncomputable def azim_mcell (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) (i : ℕ) : ℝ :=
  setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
    X ⊆ wedgeGe u0 u1 (f i) (f (i + 1))} fun X => dihX V X (u0, u1)

/-- HOL `cc_data_v8` (OXLZLEZ3.hl:36): the cc_v11 compression of the edge
data `(azim, gg, gg3a, gg3b)`, six boolean classifiers, and the leaf count. -/
noncomputable def cc_data_v8 (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) : CcV11 where
  ccReals :=
    [azim_mcell V f u0 u1,
     gg_mcell V f u0 u1,
     fun i => gammaX V (ccCell V [u0, u1, f i]) lmfun *
       criticalWeight V (ccCell V [u0, u1, f i]),
     fun i => gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
       criticalWeight V (ccCell V [u1, u0, f (i + 1)])]
  ccBools :=
    [fun i => dist (f i) (f (i + 1)) < 2 * hminus,
     fun i => 2 * hminus ≤ dist (f i) (f (i + 1)) ∧
       dist (f i) (f (i + 1)) ≤ 2 * hplus,
     fun i => 2 * hplus < dist (f i) (f (i + 1)),
     fun i => dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus,
     fun i => hl [u0, u1, f i] < 1.34,
     fun i => ∃ ul, barV V 3 ul ∧ {u0, u1} ∈ edgeX V (mcell4 V ul) ∧
       mcell4 V ul ⊆ wedgeGe u0 u1 (f i) (f (i + 1))]
  ccCard := (s_leaf V [u0, u1]).ncard

/-- HOL `leaf_rank` (OXLZLEZ3.hl:53): `f` enumerates `s_leaf V ul`
cyclically with period `n`, strictly `azim`-increasing on `0..n-1`. -/
def leaf_rank (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3) : Prop :=
  f '' (univ : Set ℕ) = s_leaf V ul ∧
    (∀ i, f (i + n) = f i) ∧
    ∀ i j, i < n → j < n → i < j →
      azim (elV ul 0) (elV ul 1) w0 (f i) < azim (elV ul 0) (elV ul 1) w0 (f j)

/-- HOL `cc_4` (OXLZLEZ3.hl:62): the wedge of `f i, f (SUC i)` over stem
`{u0,u1}` carries a 4-cell (a `barV V 3` list with `mcell4` in the wedge). -/
def cc_4 (V : Set V3) (u0 u1 : V3) (f : ℕ → V3) (i : ℕ) : Prop :=
  ∃ ul, barV V 3 ul ∧ {u0, u1} ∈ edgeX V (mcell4 V ul) ∧
    mcell4 V ul ⊆ wedgeGe u0 u1 (f i) (f (i + 1))

/-! ## GENERIC RESULTS -/

/-- HOL `CARD_INSERT_INTER`. -/
theorem CARD_INSERT_INTER {α : Type*} (a : α) (A B : Set α) (hB : B.Finite) :
    Set.ncard ((insert a A) ∩ B) =
      if a ∈ B ∧ a ∉ A then Set.ncard (A ∩ B) + 1 else Set.ncard (A ∩ B) := by
  by_cases h1 : a ∈ B ∧ a ∉ A
  · have hset : (insert a A) ∩ B = insert a (A ∩ B) := by
      refine Set.ext fun x => ?_
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨(rfl | hx), hxB⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hxB⟩
      · rintro (rfl | ⟨hxA, hxB⟩)
        · exact ⟨Or.inl rfl, h1.1⟩
        · exact ⟨Or.inr hxA, hxB⟩
    rw [hset, Set.ncard_insert_of_notMem (fun hm => absurd hm.1 h1.2)
      (hB.subset Set.inter_subset_right), if_pos h1]
  · have hset : (insert a A) ∩ B = A ∩ B := by
      refine Set.ext fun x => ?_
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨(rfl | hx), hxB⟩
        · exact ⟨Classical.byContradiction fun hc => h1 ⟨hxB, hc⟩, hxB⟩
        · exact ⟨hx, hxB⟩
      · rintro ⟨hx, hxB⟩
        exact ⟨Or.inr hx, hxB⟩
    rw [hset, if_neg h1]

/-- HOL `CARD_INSERT_INTER_ALT`. -/
theorem CARD_INSERT_INTER_ALT {α : Type*} (a : α) (A B : Set α) (hB : B.Finite) :
    Set.ncard ((insert a A) ∩ B) =
      (if a ∈ B ∧ a ∉ A then 1 else 0) + Set.ncard (A ∩ B) := by
  rw [CARD_INSERT_INTER a A B hB]
  split_ifs with h
  · omega
  · push Not at h
    omega

/-- HOL `NUMSEG_LT`: `0..(r-1) = {i | i < r}` for `r ≠ 0`. -/
theorem NUMSEG_LT (r : ℕ) (hr : r ≠ 0) :
    (Finset.Icc 0 (r - 1) : Set ℕ) = {i | i < r} := by
  ext i
  simp only [Set.mem_setOf_eq, Finset.coe_Icc]
  constructor
  · rintro ⟨-, hi⟩
    omega
  · intro hi
    exact ⟨Nat.zero_le _, by omega⟩

/-- HOL `CARD4_IN_PAIRS`: a 4-element set written over a common pair fixes
the complementary pair. -/
theorem CARD4_IN_PAIRS {α : Type*} (a b c d e f : α)
    (h4 : Nat.card ({a, b, c, d} : Set α) = 4) (heq : ({a, b, c, d} : Set α) = {a, b, e, f}) :
    ({c, d} : Set α) = {e, f} := by
  have h4n : ({a, b, c, d} : Set α).ncard = 4 := h4
  have h3 : ∀ (x y z : α), ({x, y, z} : Set α).ncard ≤ 3 := by
    intro x y z
    have hyz : ∀ (y z : α), ({y, z} : Set α).ncard ≤ 2 := by
      intro y z
      rcases eq_or_ne y z with hh | hh
      · rw [show ({y, z} : Set α) = ({y} : Set α) from by simp [hh], Set.ncard_singleton]
        omega
      · rw [Set.ncard_pair hh]
    calc ({x, y, z} : Set α).ncard = (insert x ({y, z} : Set α)).ncard := by simp
      _ ≤ ({y, z} : Set α).ncard + 1 := Set.ncard_insert_le x _
      _ ≤ 3 := by have h2 := hyz y z; omega
  have hq4 : ∀ q : α, q ∈ ({a, b, c, d} : Set α) ↔ (q = a ∨ q = b ∨ q = c ∨ q = d) := by
    intro q; simp
  have hq3 : ∀ q : α, q ∈ ({a, b, e, f} : Set α) ↔ (q = a ∨ q = b ∨ q = e ∨ q = f) := by
    intro q; simp
  -- `c` and `d` are not in `{a, b}`
  have hc : ¬ (c = a ∨ c = b) := by
    intro hm
    have hd2 : ({a, b, c, d} : Set α) = ({a, b, d} : Set α) := by
      ext q
      rw [hq4]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hq
        rcases hq with hq | hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · rcases hm with hm | hm
          · exact Or.inl (hq.trans hm)
          · exact Or.inr (Or.inl (hq.trans hm))
        · exact Or.inr (Or.inr hq)
      · intro hq
        rcases hq with hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inr hq))
    rw [hd2] at h4n
    have := h3 a b d
    omega
  have hd : ¬ (d = a ∨ d = b) := by
    intro hm
    have hd2 : ({a, b, c, d} : Set α) = ({a, b, c} : Set α) := by
      ext q
      rw [hq4]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hq
        rcases hq with hq | hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr hq)
        · rcases hm with hm | hm
          · exact Or.inl (hq.trans hm)
          · exact Or.inr (Or.inl (hq.trans hm))
      · intro hq
        rcases hq with hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inl hq))
    rw [hd2] at h4n
    have := h3 a b c
    omega
  -- `e` and `f` are not in `{a, b}`
  have he : ¬ (e = a ∨ e = b) := by
    intro hm
    have hd2 : ({a, b, e, f} : Set α) = ({a, b, f} : Set α) := by
      ext q
      rw [hq3]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hq
        rcases hq with hq | hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · rcases hm with hm | hm
          · exact Or.inl (hq.trans hm)
          · exact Or.inr (Or.inl (hq.trans hm))
        · exact Or.inr (Or.inr hq)
      · intro hq
        rcases hq with hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inr hq))
    rw [heq, hd2] at h4n
    have := h3 a b f
    omega
  have hf : ¬ (f = a ∨ f = b) := by
    intro hm
    have hd2 : ({a, b, e, f} : Set α) = ({a, b, e} : Set α) := by
      ext q
      rw [hq3]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hq
        rcases hq with hq | hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr hq)
        · rcases hm with hm | hm
          · exact Or.inl (hq.trans hm)
          · exact Or.inr (Or.inl (hq.trans hm))
      · intro hq
        rcases hq with hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inl hq))
    rw [heq, hd2] at h4n
    have := h3 a b e
    omega
  have hce : c = e ∨ c = f := by
    have hm : c ∈ ({a, b, e, f} : Set α) := by rw [← heq]; simp
    rw [hq3] at hm
    rcases hm with h | h | h | h
    · exact absurd (Or.inl h) hc
    · exact absurd (Or.inr h) hc
    · exact Or.inl h
    · exact Or.inr h
  have hdf : d = e ∨ d = f := by
    have hm : d ∈ ({a, b, e, f} : Set α) := by rw [← heq]; simp
    rw [hq3] at hm
    rcases hm with h | h | h | h
    · exact absurd (Or.inl h) hd
    · exact absurd (Or.inr h) hd
    · exact Or.inl h
    · exact Or.inr h
  have hec : e = c ∨ e = d := by
    have hm : e ∈ ({a, b, c, d} : Set α) := by rw [heq]; simp
    rw [hq4] at hm
    rcases hm with h | h | h | h
    · exact absurd (Or.inl h) he
    · exact absurd (Or.inr h) he
    · exact Or.inl h
    · exact Or.inr h
  have hfd : f = c ∨ f = d := by
    have hm : f ∈ ({a, b, c, d} : Set α) := by rw [heq]; simp
    rw [hq4] at hm
    rcases hm with h | h | h | h
    · exact absurd (Or.inl h) hf
    · exact absurd (Or.inr h) hf
    · exact Or.inl h
    · exact Or.inr h
  ext q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hq
    rcases hq with hq | hq
    · rcases hce with hce | hce
      · exact Or.inl (hq.trans hce)
      · exact Or.inr (hq.trans hce)
    · rcases hdf with hdf | hdf
      · exact Or.inl (hq.trans hdf)
      · exact Or.inr (hq.trans hdf)
  · intro hq
    rcases hq with hq | hq
    · rcases hec with hec | hec
      · exact Or.inl (hq.trans hec)
      · exact Or.inr (hq.trans hec)
    · rcases hfd with hfd | hfd
      · exact Or.inl (hq.trans hfd)
      · exact Or.inr (hq.trans hfd)

/-- HOL `initial_sublist_cons` (generic in the source; instantiated at `V3`
to reuse PackingAuto2's `initialSublist`). -/
theorem initial_sublist_cons (a b : V3) (x y : List V3) :
    initialSublist (a :: x) (b :: y) ↔ a = b ∧ initialSublist x y := by
  constructor
  · rintro ⟨zl, hzl⟩
    injection hzl with h1 h2
    exact ⟨h1.symm, zl, h2⟩
  · rintro ⟨hab, zl, hzl⟩
    subst hab
    exact ⟨zl, by rw [hzl]; simp [List.cons_append]⟩
/-- HOL `COPLANAR_CONVEX_HULL_COPLANAR`. -/
theorem COPLANAR_CONVEX_HULL_COPLANAR (s : Set V3) :
    Coplanar (convexHull ℝ s) ↔ Coplanar s := by
  constructor
  · rintro ⟨u, v, w, hsub⟩
    exact ⟨u, v, w, Set.Subset.trans (subset_convexHull ℝ s) hsub⟩
  · intro h
    obtain ⟨u, v, w, hsub⟩ := h
    refine ⟨u, v, w, ?_⟩
    intro x hx
    have h1' : x ∈ (affineSpan ℝ s : Set V3) := convexHull_subset_affineSpan (s := s) hx
    have h2' : (affineSpan ℝ s : AffineSubspace ℝ V3) ≤
        affineSpan ℝ ({u, v, w} : Set V3) := affineSpan_le.mpr hsub
    exact SetLike.mem_coe.mpr (h2' h1')

/-- HOL `BARV3_SET_OF_LIST4`. -/
theorem BARV3_SET_OF_LIST4 (V : Set V3) (ul : List V3) (hp : Packing V)
    (hb : barV V 3 ul) :
    setOfList ul = {elV ul 0, elV ul 1, elV ul 2, elV ul 3} := by
  rcases ul with _ | ⟨u0, t⟩
  · exact absurd hb.1 (by simp)
  rcases t with _ | ⟨u1, t⟩
  · exact absurd hb.1 (by simp)
  rcases t with _ | ⟨u2, t⟩
  · exact absurd hb.1 (by simp)
  rcases t with _ | ⟨u3, t⟩
  · exact absurd hb.1 (by simp)
  · have h4 : (u0 :: u1 :: u2 :: u3 :: t).length = 4 := hb.1
    cases t with
    | nil => ext x; simp [setOfList, elV]
    | cons e t' =>
      simp only [List.length_cons] at h4
      omega

/-- HOL `STRICT_SORT_FINITE` (OXLZLEZ3.hl:163): a finite set with an
asymmetric transitive `<<` can be enumerated by `1..n` in `<<`-increasing
order.  FAITHFUL-RESTATEMENT note: the HOL statement quantifies over all
types because HOL Light types are all inhabited; over an empty `α` the Lean
statement is FALSE (take `s = ∅`, `n = 0`: no function `ℕ → α` exists at
all), so the `Nonempty α` class side condition is added.  Proof: rank each
element by the cardinality of its strict down-set inside `s` (strictly
monotone along `lt`-comparable pairs by transitivity), then enumerate `s`
insertion-sorted by that rank (`List.Perm`/`List.Pairwise` bookkeeping). -/
theorem STRICT_SORT_FINITE {α : Type*} [Nonempty α] {lt : α → α → Prop} (s : Set α) (n : ℕ)
    (hirr : ∀ x y, x ∈ s → y ∈ s → lt x y → lt y x → x = y)
    (htr : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → lt x y → lt y z → lt x z)
    (hs : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → α, s = f '' Set.Icc 1 n ∧
      ∀ j k, j ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → j < k → ¬lt (f k) (f j) := by
  classical
  -- every down-set is finite (subset of `s`)
  have Dfin : ∀ x : α, ({z : α | z ∈ s ∧ lt z x ∧ z ≠ x} : Set α).Finite :=
    fun x => hs.1.subset fun z hz => hz.1
  -- rank function: cardinality of the strict down-set
  obtain ⟨mu, hmu⟩ :
      ∃ mu : α → ℕ, ∀ x, mu x = Set.ncard {z : α | z ∈ s ∧ lt z x ∧ z ≠ x} :=
    ⟨_, fun _ => rfl⟩
  -- the rank strictly increases along `lt`-comparable distinct pairs
  have key : ∀ x y : α, x ∈ s → y ∈ s → lt x y → x ≠ y → mu x < mu y := by
    intro x y hx hy hxy hne
    have hbelow : {z : α | z ∈ s ∧ lt z x ∧ z ≠ x} ⊆
        {z : α | z ∈ s ∧ lt z y ∧ z ≠ y} := by
      intro z hz
      refine ⟨hz.1, htr z x y hz.1 hx hy hz.2.1 hxy, ?_⟩
      intro hzy
      have hyx : lt y x := hzy ▸ hz.2.1
      exact absurd (hzy.trans (hirr x y hx hy hxy hyx).symm) hz.2.2
    have hxnot : x ∉ ({z : α | z ∈ s ∧ lt z x ∧ z ≠ x} : Set α) := fun h => h.2.2 rfl
    have hback : ¬ ({z : α | z ∈ s ∧ lt z y ∧ z ≠ y} : Set α) ⊆
        {z : α | z ∈ s ∧ lt z x ∧ z ≠ x} := by
      intro hcon
      exact hxnot (hcon (⟨hx, hxy, hne⟩ :
        x ∈ ({z : α | z ∈ s ∧ lt z y ∧ z ≠ y} : Set α)))
    rw [hmu x, hmu y]
    exact Set.ncard_lt_ncard ⟨hbelow, hback⟩ (Dfin y)
  -- enumerate `s` as a duplicate-free list
  set l0 : List α := hs.1.toFinset.toList with hl0def
  have hl0mem : ∀ a, a ∈ l0 ↔ a ∈ s := by
    intro a
    rw [hl0def, Finset.mem_toList, Set.Finite.mem_toFinset]
  have hl0nd : l0.Nodup := by
    rw [hl0def]; exact hs.1.toFinset.nodup_toList
  have hl0len : l0.length = n := by
    rw [hl0def, Finset.length_toList, ← Set.ncard_eq_toFinset_card s hs.1]
    exact hs.2
  -- insertion-sort it by the rank
  haveI : Std.Total (fun a b => mu a ≤ mu b) := ⟨fun a b => Nat.le_total (mu a) (mu b)⟩
  haveI : IsTrans α (fun a b => mu a ≤ mu b) := ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
  set l : List α := l0.insertionSort (fun a b => mu a ≤ mu b) with hldef
  have hlen : l.length = n := by
    rw [hldef]
    have hperml := (List.perm_insertionSort (fun a b => mu a ≤ mu b) l0).length_eq
    rw [hperml]; exact hl0len
  have hmem : ∀ a, a ∈ l ↔ a ∈ s := by
    intro a
    rw [hldef, List.mem_insertionSort, hl0mem a]
  have hlnd : l.Nodup := by
    rw [hldef]
    exact (List.perm_insertionSort (fun a b => mu a ≤ mu b) l0).nodup_iff.mpr hl0nd
  have hpair : l.Pairwise (fun a b => mu a ≤ mu b) := by
    rw [hldef]; exact List.pairwise_insertionSort _ l0
  refine ⟨fun i => l.getD (i - 1) (Classical.choice inferInstance), ?_, ?_⟩
  · refine Set.ext fun x => ?_
    constructor
    · intro hx
      obtain ⟨i, hi, hli⟩ := List.mem_iff_getElem.mp (hmem x |>.mpr hx)
      exact ⟨i + 1, ⟨by omega, by omega⟩, by
        show l.getD (i + 1 - 1) (Classical.choice inferInstance) = x
        rw [show i + 1 - 1 = i from by omega,
          List.getD_eq_getElem l (Classical.choice inferInstance) hi]
        exact hli⟩
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
      show l.getD (i - 1) (Classical.choice inferInstance) ∈ s
      have hilt : i - 1 < l.length := by rw [hlen]; omega
      rw [List.getD_eq_getElem l (Classical.choice inferInstance) hilt]
      exact (hmem _).mp (List.getElem_mem _)
  · intro j k kj kk hlt
    obtain ⟨hj1, hjn⟩ := kj
    obtain ⟨hk1, hkn⟩ := kk
    have hjlt : j - 1 < l.length := by rw [hlen]; omega
    have hklt : k - 1 < l.length := by rw [hlen]; omega
    intro hlt
    have hjk : j - 1 ≠ k - 1 := by omega
    have hne' : l[k - 1] ≠ l[j - 1] := by
      intro hcon
      exact hjk (congrArg Fin.val
        (List.nodup_iff_injective_getElem.mp hlnd
          (show l[(⟨k - 1, hklt⟩ : Fin l.length).val] =
              l[(⟨j - 1, hjlt⟩ : Fin l.length).val] from hcon))).symm
    beta_reduce at hlt
    rw [List.getD_eq_getElem l (Classical.choice inferInstance) hklt,
        List.getD_eq_getElem l (Classical.choice inferInstance) hjlt] at hlt
    have hge : mu l[j - 1] ≤ mu l[k - 1] :=
      List.pairwise_iff_getElem.mp hpair (j - 1) (k - 1) hjlt hklt (by omega)
    have hmut : mu l[k - 1] < mu l[j - 1] :=
      key _ _ (hmem _ |>.mp (List.getElem_mem _)) (hmem _ |>.mp (List.getElem_mem _))
        hlt hne'
    omega

/-- HOL `MOD_INJ1_ALT` (name sufficed; PackingAuto3.lean:445 has an
equivalent theorem under this name). -/
theorem MOD_INJ1_ALT_p25 {k n : ℕ} (hn : n ≠ 0) (hk : k < n) (hk0 : k ≠ 0)
    (x : ℕ) : x % n ≠ (x + k) % n := by
  intro h
  have hdvd : n ∣ x + k - x := (Nat.modEq_iff_dvd' (Nat.le_add_right x k)).mp h
  rw [Nat.add_sub_cancel_left] at hdvd
  have hle : n ≤ k := Nat.le_of_dvd (by omega) hdvd
  omega

/-- HOL `MOD_PERIOD_BOUNDED_ALT`. -/
theorem MOD_PERIOD_BOUNDED_ALT {k n : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (x : ℕ) (h : (x + k) % n = x % n) : n ≤ k := by
  by_contra hc
  have hlt : k < n := by omega
  exact MOD_INJ1_ALT_p25 hn hlt hk x h.symm

/-- HOL `MOD_REFL_ALT` (`MOD_MULT` at `m, 1` after `MULT_CLAUSES`). -/
theorem MOD_REFL_ALT (m : ℕ) : m % 1 = 0 := Nat.mod_one m

/-- HOL `periodic_o`. -/
theorem periodic_o {α β : Type*} (g : α → β) {f : ℕ → α} {n : ℕ}
    (h : periodic f n) : periodic (g ∘ f) n := fun i => congrArg g (h i)

/-- HOL `periodic_shift`. -/
theorem periodic_shift {α : Type*} (k : ℕ) {f : ℕ → α} {n : ℕ}
    (h : periodic f n) : periodic (fun i => f (i + k)) n := by
  intro i
  show f (i + n + k) = f (i + k)
  have h2 : i + n + k = i + k + n := by omega
  rw [h2]
  exact h (i + k)

/-- Helper: periodicity iterated `k` times. -/
private theorem p25_periodic_mul {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n)
    (k i : ℕ) : f (i + n * k) = f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, h, ih]

/-- Helper: `f i` depends on `i` only mod `n`. -/
private theorem p25_f_mod {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n)
    (i : ℕ) : f (i % n) = f i := by
  have h1 := Nat.mod_add_div i n
  calc f (i % n) = f (i % n + n * (i / n)) := (p25_periodic_mul h (i / n) (i % n)).symm
    _ = f i := by rw [h1]

/-- HOL `PERIODIC_IMAGE`. -/
theorem PERIODIC_IMAGE {α : Type*} {f : ℕ → α} {n : ℕ} (hn : n ≠ 0)
    (h : periodic f n) : f '' {i | i < n} = f '' (univ : Set ℕ) := by
  refine Set.ext fun y => ?_
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨i, Set.mem_univ _, rfl⟩
  · rintro ⟨i, _, rfl⟩
    refine ⟨i % n, ?_, p25_f_mod h i⟩
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact Nat.mod_lt _ this

/-- HOL `PERIODIC_REDUCE_MOD`. -/
theorem PERIODIC_REDUCE_MOD {α : Type*} {f : ℕ → α} {n : ℕ} (hn : 1 ≤ n)
    (h : periodic f n) (i : ℕ) :
    ∃ j, j < n ∧ f i = f j ∧ f (i + 1) = f (j + 1) := by
  have h0 : i % n < n := Nat.mod_lt i (by have := hn; omega)
  refine ⟨i % n, h0, ?_, ?_⟩
  · rw [p25_f_mod h i]
  · have h1 := Nat.mod_add_div i n
    have e : i + 1 = i % n + 1 + n * (i / n) := by omega
    rw [e, p25_periodic_mul h]

/-- HOL `PERIODIC_EQ_IMAGE` (renamed from PERIODIC_INJ). -/
theorem PERIODIC_EQ_IMAGE {α : Type*} {f : ℕ → α} {n : ℕ} (_hn : n ≠ 0)
    (h : periodic f n) {i j : ℕ} (hm : i % n = j % n) : f i = f j := by
  calc f i = f (i % n) := (p25_f_mod h i).symm
    _ = f (j % n) := by rw [hm]
    _ = f j := p25_f_mod h j

/-- HOL `F_SUC_PRE`. -/
theorem F_SUC_PRE {α : Type*} {f : ℕ → α} {n : ℕ} (hn : n ≠ 0) (h : periodic f n)
    (i : ℕ) : f (i + n - 1 + 1) = f i := by
  have e : i + n - 1 + 1 = i + n := by omega
  rw [e, h]

/-- HOL `F_DEMOD`. -/
theorem F_DEMOD {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n) (hn : 1 < n)
    (i : ℕ) : f (i % n) = f i ∧ f (i % n + 1) = f (i + 1) := by
  refine ⟨p25_f_mod h i, ?_⟩
  have h1 := Nat.mod_add_div i n
  have e : i + 1 = i % n + 1 + n * (i / n) := by omega
  rw [e, p25_periodic_mul h]

/-- HOL `FM_DEMOD`. -/
theorem FM_DEMOD {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n) (hn : 1 < n)
    (i : ℕ) : f (i % n) = f i ∧ f (i % n + n - 1) = f (i + n - 1) := by
  refine ⟨p25_f_mod h i, ?_⟩
  have h1 := Nat.mod_add_div i n
  have e : i + n - 1 = i % n + n - 1 + n * (i / n) := by omega
  rw [e, p25_periodic_mul h]

private theorem p25_finrank_span_pair_le_two (a b : V3) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  have h2 := finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset V3)
  unfold Set.finrank at h2
  rw [show (({a, b} : Finset V3) : Set V3) = ({a, b} : Set V3) from by simp] at h2
  refine h2.trans ?_
  calc ({a, b} : Finset V3).card ≤ ({b} : Finset V3).card + 1 := Finset.card_insert_le a {b}
    _ = 2 := by simp

private theorem p25_affineSpan_three_ne_top (x v u : V3) :
    (affineSpan ℝ ({x, v, u} : Set V3)) ≠ ⊤ := by
  intro h
  have hdir : (affineSpan ℝ ({x, v, u} : Set V3)).direction = ⊤ := by
    rw [h]; exact AffineSubspace.direction_top ℝ V3 V3
  have hvs : vectorSpan ℝ ({x, v, u} : Set V3)
      = Submodule.span ℝ ({v - x, u - x} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show x ∈ ({x, v, u} : Set V3) from by simp)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro p ⟨q, hq, rfl⟩
      rcases hq with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by left; rfl)
      · exact Submodule.subset_span (by right; rfl)
    · rw [Submodule.span_le]
      rintro p (rfl | rfl)
      · exact Submodule.subset_span ⟨v, by simp, rfl⟩
      · exact Submodule.subset_span ⟨u, by simp, rfl⟩
  have hle : Module.finrank ℝ (affineSpan ℝ ({x, v, u} : Set V3)).direction ≤ 2 := by
    rw [direction_affineSpan, hvs]
    exact p25_finrank_span_pair_le_two (v - x) (u - x)
  rw [hdir, finrank_top] at hle
  exact absurd hle (by norm_num)

private theorem p25_finset_sum_smul_mem_affineSpan {T : Set V3} {s : Finset V3}
    {f : V3 → ℝ}
    (hS : ∀ w ∈ s, w ∈ (affineSpan ℝ T : Set V3))
    (hsum : ∑ w ∈ s, f w = 1) :
    ∑ w ∈ s, f w • w ∈ (affineSpan ℝ T : Set V3) := by
  have hne : s.Nonempty :=
    Finset.nonempty_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  obtain ⟨b, hb⟩ := hne
  have hbS : b ∈ (affineSpan ℝ T : Set V3) := hS b hb
  have hdir : ∑ w ∈ s, f w • (w - b) ∈ (affineSpan ℝ T).direction := by
    apply Submodule.sum_mem
    intro w hw
    exact Submodule.smul_mem _ (f w)
      (AffineSubspace.vsub_mem_direction (hS w hw) hbS)
  have hsub : ∑ w ∈ s, f w • (w - b) = (∑ w ∈ s, f w • w) - b := by
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  have hy : ∑ w ∈ s, f w • w = (∑ w ∈ s, f w • (w - b)) +ᵥ b := by
    rw [vadd_eq_add, hsub]
    abel
  rw [hy]
  exact AffineSubspace.vadd_mem_of_mem_direction hdir hbS

private theorem p25_affGe_subset_affineSpan (s t : Set V3) :
    affGe s t ⊆ (affineSpan ℝ (s ∪ t : Set V3) : Set V3) := by
  intro v hv
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hv
  obtain ⟨f, hfin, hcomb, _, hone⟩ := hv
  have hmem : ∀ w ∈ hfin.toFinset, w ∈ (affineSpan ℝ (s ∪ t : Set V3) : Set V3) := by
    intro w hw
    have hw' : w ∈ s ∪ t := by
      rw [← hfin.coe_toFinset]
      exact hw
    exact subset_affineSpan ℝ _ hw'
  rw [hcomb]
  exact p25_finset_sum_smul_mem_affineSpan hmem hone

/-- HOL `NULLSET_AFF_2_1`. -/
theorem NULLSET_AFF_2_1 (x y z : V3) : nullSet (affGe {x, y} {z}) := by
  have hsub := p25_affGe_subset_affineSpan ({x, y} : Set V3) ({z} : Set V3)
  have h3 : (affineSpan ℝ ({x, y} ∪ {z} : Set V3)) ≠ ⊤ := by
    rw [show ({x, y} ∪ {z} : Set V3) = ({x, y, z} : Set V3) from by
      ext q; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact p25_affineSpan_three_ne_top x y z
  refine measure_mono_null hsub ?_
  exact MeasureTheory.Measure.addHaar_affineSubspace volume
    (affineSpan ℝ ({x, y} ∪ {z} : Set V3)) h3

/-- HOL `coplanar_delta_y` (renamed from coplanar_dih_y). -/
theorem coplanar_delta_y (u0 u1 u2 u3 : V3) :
    ¬ Coplanar ({u0, u1, u2, u3} : Set V3) ↔
      0 < deltaY (dist u0 u1) (dist u0 u2) (dist u0 u3) (dist u2 u3)
        (dist u1 u3) (dist u1 u2) := by
  have hdelta : deltaY (dist u0 u1) (dist u0 u2) (dist u0 u3) (dist u2 u3)
        (dist u1 u3) (dist u1 u2)
      = deltaP (dist u0 u1 ^ 2) (dist u0 u2 ^ 2) (dist u0 u3 ^ 2)
          (dist u1 u2 ^ 2) (dist u1 u3 ^ 2) (dist u2 u3 ^ 2) := by
    simp only [deltaY, pow_two, delta_delta_x]
  rw [hdelta, POS_EQ_NOT_COPLANANR, coplanar_eq_coplanar_alt]

/-- RADV_ETAY 的核心（无 eta_y 依赖形态）：三角形外心半径 = 三边长平方积
除以 upsX（Heron 行列式），即 `radV {三点}² = a²b²c²/upsX a² b² c²`。路线：
显式外心见证 `q = (α•a + β•b) +ᵥ u0`（α = b(b−c)/2Δ, β = a(b−c)/2Δ，
Δ = Gram 行列式 > 0 由非平行性给出）经 `OAPVION3_concl` 唯一性认定为
`circumcenter`，`OAPVION2_concl` 给 `radV = dist q u0`，平方后代数收口。 -/
private theorem p25_radv_etay_core (u0 u1 u2 : V3) (hnc : ¬ Collinear3 u0 u1 u2)
    (haff : ¬ affineDependent ({u0, u1, u2} : Set V3))
    (h01 : u0 ≠ u1) (h02 : u0 ≠ u2) (h12 : u1 ≠ u2) :
    radV ({u0, u1, u2} : Set V3) =
      Real.sqrt ((dist u0 u1 * dist u0 u1) * (dist u0 u2 * dist u0 u2)
          * (dist u1 u2 * dist u1 u2)
        / upsX (dist u0 u1 * dist u0 u1) (dist u0 u2 * dist u0 u2)
          (dist u1 u2 * dist u1 u2)) := by
  -- inner-product algebra helpers (atomic args; no vector collapse)
  have hgram : ∀ x y : V3, inner ℝ (x - y) (x - y)
      = inner ℝ x x + inner ℝ y y - 2 * inner ℝ x y := by
    intro x y
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm y x]
    ring
  have hgram2 : ∀ (x y : V3) (t : ℝ), inner ℝ (x - t • y) (x - t • y)
      = inner ℝ x x - 2 * t * inner ℝ x y + t * t * inner ℝ y y := by
    intro x y t
    have e : (x - t • y : V3) = x + (-t) • y := by
      rw [neg_smul]; abel
    rw [e]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm y x]
    ring
  have hexp : ∀ (r s : ℝ) (x y : V3),
      inner ℝ (r • x + s • y) (r • x + s • y)
        = r * r * inner ℝ x x + 2 * r * s * inner ℝ x y + s * s * inner ℝ y y := by
    intro r s x y
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm y x]
    ring
  -- Gram atoms
  obtain ⟨gaa, hga⟩ : ∃ x, x = inner ℝ (u1 - u0) (u1 - u0) := ⟨_, rfl⟩
  obtain ⟨gbb, hgb⟩ : ∃ x, x = inner ℝ (u2 - u0) (u2 - u0) := ⟨_, rfl⟩
  obtain ⟨gab, hgc⟩ : ∃ x, x = inner ℝ (u1 - u0) (u2 - u0) := ⟨_, rfl⟩
  obtain ⟨gde, hgd⟩ : ∃ x, x = gaa * gbb - gab * gab := ⟨_, rfl⟩
  -- links to distances
  have dA : gaa = dist u0 u1 * dist u0 u1 := by
    rw [hga, real_inner_self_eq_norm_sq, dist_eq_norm u0 u1,
      show (u0 : V3) - u1 = -(u1 - u0) from by abel, norm_neg, pow_two]
  have dB : gbb = dist u0 u2 * dist u0 u2 := by
    rw [hgb, real_inner_self_eq_norm_sq, dist_eq_norm u0 u2,
      show (u0 : V3) - u2 = -(u2 - u0) from by abel, norm_neg, pow_two]
  have hCc : dist u1 u2 * dist u1 u2 = gaa + gbb - 2 * gab := by
    have h1 : dist u1 u2 * dist u1 u2
        = inner ℝ ((u1 - u0) - (u2 - u0)) ((u1 - u0) - (u2 - u0)) := by
      rw [real_inner_self_eq_norm_sq, dist_eq_norm u1 u2,
        show (u1 : V3) - u2 = (u1 - u0) - (u2 - u0) from by abel, pow_two]
    rw [h1, hgram, ← hga, ← hgb, ← hgc]
  -- positivity of the Gram determinant
  have hApos : 0 < gaa := by
    rw [dA]; exact mul_pos (dist_pos.2 h01) (dist_pos.2 h01)
  have hDpos : 0 < gde := by
    have hbna : ((u2 - u0 : V3) - (gab / gaa) • (u1 - u0)) ≠ 0 := by
      intro hz
      have hbpara : (u2 - u0 : V3) = (gab / gaa) • (u1 - u0) := sub_eq_zero.mp hz
      refine hnc (show Collinear ℝ ({u0, u1, u2} : Set V3) from ?_)
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨u0, u1 - u0, ?_⟩
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | hx
      · exact ⟨0, by rw [zero_smul, vadd_eq_add, zero_add]⟩
      rcases hx with rfl | hx
      · exact ⟨1, by rw [one_smul, vadd_eq_add]; abel⟩
      · have hu2 : (u2 : V3) = (u2 - u0) + u0 := by abel
        exact ⟨gab / gaa, by rw [hx, hu2, hbpara, vadd_eq_add]⟩
    have hpos : 0 < inner ℝ ((u2 - u0) - (gab / gaa) • (u1 - u0))
        ((u2 - u0) - (gab / gaa) • (u1 - u0)) := by
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_iff.2 (norm_ne_zero_iff.mpr hbna)
    have hexpD : inner ℝ ((u2 - u0) - (gab / gaa) • (u1 - u0))
        ((u2 - u0) - (gab / gaa) • (u1 - u0)) = gbb - gab * gab / gaa := by
      rw [hgram2, real_inner_comm (u1 - u0) (u2 - u0), ← hgb, ← hgc, ← hga]
      field_simp
      ring
    rw [hexpD] at hpos
    have h2 : gab * gab / gaa < gbb := by linarith
    have h3 : gab * gab < gaa * gbb := by
      have h3' : gab * gab < gbb * gaa := (div_lt_iff₀ hApos).mp h2
      rwa [mul_comm gbb gaa] at h3'
    rw [hgd]; linarith
  have hDne : gde ≠ 0 := ne_of_gt hDpos
  -- explicit circumcenter witness: q = (al•a + be•b) +ᵥ u0
  obtain ⟨al, hal⟩ : ∃ x, x = gbb * (gaa - gab) / (2 * gde) := ⟨_, rfl⟩
  obtain ⟨be, hbe⟩ : ∃ x, x = gaa * (gbb - gab) / (2 * gde) := ⟨_, rfl⟩
  have k1 : 2 * (gaa * al + gab * be) = gaa := by
    rw [hal, hbe]; field_simp; rw [hgd]; ring
  have k2 : 2 * (gab * al + gbb * be) = gbb := by
    rw [hal, hbe]; field_simp; rw [hgd]; ring
  set q : V3 := (al • (u1 - u0) + be • (u2 - u0)) +ᵥ u0 with hqdef
  -- q is on the affine hull
  have hdir : (affineSpan ℝ ({u0, u1, u2} : Set V3)).direction
      = Submodule.span ℝ ({u1 - u0, u2 - u0} : Set V3) := by
    rw [direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right ℝ (show u0 ∈ ({u0, u1, u2} : Set V3) from by simp)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro p ⟨z, hz, rfl⟩
      rcases hz with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      rintro p (rfl | rfl)
      · exact Submodule.subset_span ⟨u1, by simp, rfl⟩
      · exact Submodule.subset_span ⟨u2, by simp, rfl⟩
  have hxmem : al • (u1 - u0) + be • (u2 - u0)
      ∈ (affineSpan ℝ ({u0, u1, u2} : Set V3)).direction := by
    rw [hdir]
    exact Submodule.mem_span_pair.mpr ⟨al, be, by abel⟩
  have hqmem : q ∈ (affineSpan ℝ ({u0, u1, u2} : Set V3) : Set V3) :=
    AffineSubspace.vadd_mem_of_mem_direction hxmem
      (subset_affineSpan ℝ ({u0, u1, u2} : Set V3) (by simp))
  -- key distances
  have hx0 : (q : V3) - u0 = al • (u1 - u0) + be • (u2 - u0) := by
    rw [hqdef, vadd_eq_add]; abel
  have hx1 : (q : V3) - u1 = (al - 1) • (u1 - u0) + be • (u2 - u0) := by
    have hu1 : (u1 : V3) = (u1 - u0) + u0 := by abel
    rw [hqdef, vadd_eq_add, hu1]
    module
  have hx2 : (q : V3) - u2 = al • (u1 - u0) + (be - 1) • (u2 - u0) := by
    have hu2 : (u2 : V3) = (u2 - u0) + u0 := by abel
    rw [hqdef, vadd_eq_add, hu2]
    module
  have n0 : ‖(q : V3) - u0‖ ^ 2
      = al * (gaa * al + gab * be) + be * (gab * al + gbb * be) := by
    rw [hx0, ← real_inner_self_eq_norm_sq, hexp, ← hga, ← hgb, ← hgc]
    ring
  have n1 : ‖(q : V3) - u1‖ ^ 2
      = al * (gaa * al + gab * be) + be * (gab * al + gbb * be) := by
    rw [hx1, ← real_inner_self_eq_norm_sq, hexp, ← hga, ← hgb, ← hgc]
    have hstep : ((al - 1) * (al - 1) * gaa + 2 * (al - 1) * be * gab
          + be * be * gbb)
        = al * (gaa * al + gab * be) + be * (gab * al + gbb * be)
          - (2 * (gaa * al + gab * be) - gaa) := by ring
    rw [hstep, k1]; ring
  have n2 : ‖(q : V3) - u2‖ ^ 2
      = al * (gaa * al + gab * be) + be * (gab * al + gbb * be) := by
    rw [hx2, ← real_inner_self_eq_norm_sq, hexp, ← hga, ← hgb, ← hgc]
    have hstep : (al * al * gaa + 2 * al * (be - 1) * gab
          + (be - 1) * (be - 1) * gbb)
        = al * (gaa * al + gab * be) + be * (gab * al + gbb * be)
          - (2 * (gab * al + gbb * be) - gbb) := by ring
    rw [hstep, k2]; ring
  have d01 : dist q u0 = dist q u1 := by
    rw [dist_eq_norm, dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (by rw [n0, n1])
  have d02 : dist q u0 = dist q u2 := by
    rw [dist_eq_norm, dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (by rw [n0, n2])
  -- q is THE circumcenter
  have hcd : ∃ c : ℝ, ∀ w ∈ ({u0, u1, u2} : Set V3), dist q w = c := by
    refine ⟨dist q u0, ?_⟩
    rintro w (rfl | rfl | rfl)
    · rfl
    · exact d01.symm
    · exact d02.symm
  have hqcc : q = circumcenter ({u0, u1, u2} : Set V3) :=
    OAPVION3_concl _ haff q hqmem hcd
  have hR := OAPVION2_concl ({u0, u1, u2} : Set V3) haff u0 (by simp)
  rw [← hqcc] at hR
  -- final computation
  have hups : upsX gaa gbb (gaa + gbb - 2 * gab) = 4 * gde := by
    simp only [upsX]
    rw [hgd]
    ring
  have hfin : ‖(q : V3) - u0‖ ^ 2
      = (gaa * gbb * (gaa + gbb - 2 * gab)) / (4 * gde) := by
    rw [n0, hal, hbe]
    field_simp
    rw [hgd]
    ring
  rw [hR, dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _)]
  congr 1
  rw [← dA, ← dB, hCc, hups, hfin]

/-- HOL `RADV_ETAY`（2026-10-13 转真：`p25_radv_etay_core`（外心-Heron 代数，
自身零债）+ `eta_y` 体定义性展开（`ETA_Y_POS_LE_ALT` 同款 rfl 钉扎）；
LEAF_DOMAIN 尾步的具名欠叶同步解除）。 -/
theorem RADV_ETAY (u0 u1 u2 : V3) (hnc : ¬ Collinear3 u0 u1 u2) :
    radV {u0, u1, u2} = eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) := by
  have h01 : u0 ≠ u1 := by
    intro he
    refine hnc (show Collinear ℝ ({u0, u1, u2} : Set V3) from ?_)
    have hset : ({u0, u1, u2} : Set V3) = ({u0, u2} : Set V3) := by
      rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact collinear_pair ℝ u0 u2
  have h02 : u0 ≠ u2 := by
    intro he
    refine hnc (show Collinear ℝ ({u0, u1, u2} : Set V3) from ?_)
    have hset : ({u0, u1, u2} : Set V3) = ({u0, u1} : Set V3) := by
      rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact collinear_pair ℝ u0 u1
  have h12 : u1 ≠ u2 := by
    intro he
    refine hnc (show Collinear ℝ ({u0, u1, u2} : Set V3) from ?_)
    have hset : ({u0, u1, u2} : Set V3) = ({u0, u1} : Set V3) := by
      rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact collinear_pair ℝ u0 u1
  have haff : ¬ affineDependent ({u0, u1, u2} : Set V3) := by
    -- `p25_not_affdep3` 的内联副本（该件定义在本文件后段，Lean 无前向引用）
    intro haff
    have hmem_a : (u0 : V3) ∈ ({u0, u1, u2} : Set V3) := by simp
    refine haff ((affineIndependent_set_iff_linearIndependent_vsub (k := ℝ) hmem_a).mpr ?_)
    have hdiff : (({u0, u1, u2} : Set V3) \ {u0}) = ({u1, u2} : Set V3) := by
      ext z
      by_cases hz : z = u0
      · subst hz; simp [h01, h02]
      · simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, hz,
          not_false_iff]
        by_cases h1 : z = u1 <;> by_cases h2 : z = u2 <;> simp [h1, h2]
    have himg : ((fun p : V3 => (p -ᵥ u0)) '' ({u1, u2} : Set V3))
        = ({u1 - u0, u2 - u0} : Set V3) := by
      rw [Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [hdiff, himg]
    apply (linearIndependent_subtype_iff).mpr
    refine LinearIndepOn.id_insert (s := ({u2 - u0} : Set V3)) ?_ ?_
    · exact LinearIndepOn.singleton
        (show (u2 - u0 : V3) ≠ 0 from sub_ne_zero.mpr h02.symm)
    · intro hm
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
      by_cases hc0 : c = 0
      · rw [hc0, zero_smul] at hc
        exact h01 (sub_eq_zero.mp hc.symm).symm
      · exact hnc ((collinear3_iff_smul (hw := Ne.symm h01)).mpr ⟨c⁻¹, by
          rw [hc.symm, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩)
  have hform : eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2)
      = Real.sqrt ((dist u0 u1 * dist u0 u1) * (dist u0 u2 * dist u0 u2)
          * (dist u1 u2 * dist u1 u2)
        / upsX (dist u0 u1 * dist u0 u1) (dist u0 u2 * dist u0 u2)
          (dist u1 u2 * dist u1 u2)) := rfl
  rw [hform]
  exact p25_radv_etay_core u0 u1 u2 hnc haff h01 h02 h12

/-- HOL `RADV2`. -/
theorem RADV2 (u v : V3) : radV {u, v} = (1 / 2 : ℝ) * dist u v := by
  have hset : setOfList [u, v] = ({u, v} : Set V3) := by
    ext x
    simp [setOfList]
  have h := HL_2 u v
  unfold hl at h
  rw [hset] at h
  rw [h]
  ring

/-- Span-成员升入三点仿射包（`p25_mem_affSpan3` 的本处内联副本：该件定义在
本文件后段，Lean 无前向引用）。 -/
private theorem p25g_mem_affSpan3 {a u v p : V3}
    (hp : (p - a : V3) ∈ Submodule.span ℝ ({u - a, v - a} : Set V3)) :
    p ∈ (affineSpan ℝ ({a, u, v} : Set V3) : Set V3) := by
  have hpv : (p : V3) = (p -ᵥ a) +ᵥ a := (vsub_vadd p a).symm
  rw [hpv]
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ (mem_affineSpan ℝ (by simp))
  rw [direction_affineSpan,
    vectorSpan_eq_span_vsub_set_right ℝ (show (a : V3) ∈ ({a, u, v} : Set V3) from by simp)]
  have hsub : ({u - a, v - a} : Set V3) ⊆
      ((fun q : V3 => (q -ᵥ a)) '' ({a, u, v} : Set V3)) := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact ⟨u, by simp, rfl⟩
    · rcases Set.mem_singleton_iff.mp hz with rfl
      exact ⟨v, by simp, rfl⟩
  exact Submodule.span_mono hsub hp

/-- 仿射相关四点组共面（`p25_affdep4_coplanar` 的本处内联副本：该件定义在
本文件后段，Lean 无前向引用）。 -/
private theorem p25g_affdep4_coplanar {a b c d : V3}
    (h : affineDependent ({a, b, c, d} : Set V3)) :
    Coplanar ({a, b, c, d} : Set V3) := by
  -- degenerate stem coincidences: the set drops to three points, which is
  -- coplanar outright
  rcases eq_or_ne a b with hab | hab
  · have hset : ({a, b, c, d} : Set V3) = ({b, c, d} : Set V3) := by
      rw [hab]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact coplanar_triple b c d
  rcases eq_or_ne a c with hac | hac
  · have hset : ({a, b, c, d} : Set V3) = ({b, c, d} : Set V3) := by
      rw [hac]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact coplanar_triple b c d
  rcases eq_or_ne a d with had | had
  · have hset : ({a, b, c, d} : Set V3) = ({b, c, d} : Set V3) := by
      rw [had]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact coplanar_triple b c d
  have hmem_a : (a : V3) ∈ ({a, b, c, d} : Set V3) := by simp
  have hdiff : (({a, b, c, d} : Set V3) \ {a}) = ({b, c, d} : Set V3) := by
    ext z
    by_cases hz : z = a
    · subst hz; simp [hab, hac, had]
    · simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, hz,
        not_false_iff]
      tauto
  have himg : ((fun p : V3 => (p -ᵥ a)) '' ({b, c, d} : Set V3))
      = ({b - a, c - a, d - a} : Set V3) := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [affineDependent,
    affineIndependent_set_iff_linearIndependent_vsub (k := ℝ) hmem_a, hdiff, himg] at h
  have h' : ¬ LinearIndepOn ℝ id ({b - a, c - a, d - a} : Set V3) := h
  by_cases hbb : (b - a : V3) ∈ Submodule.span ℝ ({c - a, d - a} : Set V3)
  · refine ⟨a, c, d, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with he | he | he | he
    · rw [he]; exact mem_affineSpan ℝ (by simp)
    · rw [he]; exact p25g_mem_affSpan3 hbb
    · rw [he]; exact mem_affineSpan ℝ (by simp)
    · rw [he]; exact mem_affineSpan ℝ (by simp)
  · by_cases hcc : (c - a : V3) ∈ Submodule.span ℝ ({b - a, d - a} : Set V3)
    · refine ⟨a, b, d, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with he | he | he | he
      · rw [he]; exact mem_affineSpan ℝ (by simp)
      · rw [he]; exact mem_affineSpan ℝ (by simp)
      · rw [he]; exact p25g_mem_affSpan3 hcc
      · rw [he]; exact mem_affineSpan ℝ (by simp)
    · by_cases hdd : (d - a : V3) ∈ Submodule.span ℝ ({b - a, c - a} : Set V3)
      · refine ⟨a, b, c, ?_⟩
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with he | he | he | he
        · rw [he]; exact mem_affineSpan ℝ (by simp)
        · rw [he]; exact mem_affineSpan ℝ (by simp)
        · rw [he]; exact mem_affineSpan ℝ (by simp)
        · rw [he]; exact p25g_mem_affSpan3 hdd
      · exfalso
        have hda : d ≠ a := fun heq => hdd (by rw [heq]; simp)
        have hca : c ≠ a := fun heq => hcc (by rw [heq]; simp)
        have s1 : LinearIndepOn ℝ id ({d - a} : Set V3) :=
          LinearIndepOn.singleton (show (d - a : V3) ≠ 0 from sub_ne_zero.mpr hda)
        have s2 : LinearIndepOn ℝ id ({c - a, d - a} : Set V3) :=
          LinearIndepOn.id_insert (s := ({d - a} : Set V3)) s1
            (fun hm => hcc (Submodule.span_mono (Set.subset_insert _ _) hm))
        exact h' (LinearIndepOn.id_insert (s := ({c - a, d - a} : Set V3)) s2 hbb)

set_option maxHeartbeats 25000000 in
/-- HOL `GDRQXLGv3`（2026-10-13 转真：radV²↔rad2XP25 解析桥，外心-Cramer
代数路线——OAPVION2+代数，自身零债、不依赖 edge-rigidity GIANT）：
`¬Coplanar` 经 `p25g_affdep4_coplanar` 给 `¬affineDependent`，经 PA18
`POS_EQ_NOT_COPLANANR`+`delta_delta_x` 给 Cayley–Menger 行列式 `deltaX > 0`；
Gram 矩阵（差向量 e₁=v₁−v₀、e₂=v₂−v₀、e₃=v₃−v₀ 的内积组）行列式 Δ>0，
显式 Cramer 见证 `q = (t₁•e₁+t₂•e₂+t₃•e₃)+ᵥv₀`（tᵢ=nᵢ/2Δ）经
`OAPVION3_concl` 认定为 circumcenter、`OAPVION2_concl` 给 `radV = dist q v₀`；
平方后由多项式恒等式 `deltaX = 4Δ`、`rhoX = 4·Σgᵢ·nᵢ` 纯 `ring` 收口
（与 `p25_radv_etay_core` 三点 Heron 版同构）。 -/
theorem GDRQXLGv3 (v0 v1 v2 v3 : V3) (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3)) :
    radV {v0, v1, v2, v3} ^ 2 =
      rad2XP25 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
  have haff : ¬ affineDependent ({v0, v1, v2, v3} : Set V3) :=
    fun hd => hnc (p25g_affdep4_coplanar hd)
  -- inner-product algebra helper (atomic args; no vector collapse)
  have hgram : ∀ x y : V3, inner ℝ (x - y) (x - y)
      = inner ℝ x x + inner ℝ y y - 2 * inner ℝ x y := by
    intro x y
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm y x]
    ring
  -- Gram atoms of e1 = v1 - v0, e2 = v2 - v0, e3 = v3 - v0
  obtain ⟨ga, hga⟩ : ∃ x, x = inner ℝ (v1 - v0) (v1 - v0) := ⟨_, rfl⟩
  obtain ⟨gb, hgb⟩ : ∃ x, x = inner ℝ (v2 - v0) (v2 - v0) := ⟨_, rfl⟩
  obtain ⟨gc, hgc⟩ : ∃ x, x = inner ℝ (v3 - v0) (v3 - v0) := ⟨_, rfl⟩
  obtain ⟨gab, hgab⟩ : ∃ x, x = inner ℝ (v1 - v0) (v2 - v0) := ⟨_, rfl⟩
  obtain ⟨gac, hgac⟩ : ∃ x, x = inner ℝ (v1 - v0) (v3 - v0) := ⟨_, rfl⟩
  obtain ⟨gbc, hgbc⟩ : ∃ x, x = inner ℝ (v2 - v0) (v3 - v0) := ⟨_, rfl⟩
  -- Cramer numerators n1, n2, n3 (2Δ·tᵢ) and the Gram determinant Δ
  obtain ⟨n1, hn1⟩ : ∃ x, x = ga * gb * gc - ga * (gbc * gbc)
      - gb * (gab * gc) + gb * (gac * gbc) + gc * (gab * gbc)
      - gc * (gac * gb) := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ x, x = ga * gb * gc - ga * (gbc * gc)
      - ga * (gab * gc) + ga * (gbc * gac) + gc * (gab * gac)
      - gb * (gac * gac) := ⟨_, rfl⟩
  obtain ⟨n3, hn3⟩ : ∃ x, x = ga * gb * gc - ga * (gb * gbc)
      - ga * (gb * gac) + ga * (gab * gbc) + gb * (gab * gac)
      - gc * (gab * gab) := ⟨_, rfl⟩
  obtain ⟨dda, hdda⟩ : ∃ x, x = ga * gb * gc + 2 * (gbc * gac * gab)
      - ga * (gbc * gbc) - gb * (gac * gac) - gc * (gab * gab) := ⟨_, rfl⟩
  -- the algebraic kernel: Cramer column identities + the rho/delta pins
  have hc1 : ga * n1 + gab * n2 + gac * n3 = ga * dda := by
    rw [hn1, hn2, hn3, hdda]
    ring
  have hc2 : gab * n1 + gb * n2 + gbc * n3 = gb * dda := by
    rw [hn1, hn2, hn3, hdda]
    ring
  have hc3 : gac * n1 + gbc * n2 + gc * n3 = gc * dda := by
    rw [hn1, hn2, hn3, hdda]
    ring
  have hdelt : deltaX ga gb gc (gb + gc - 2 * gbc) (ga + gc - 2 * gac)
      (ga + gb - 2 * gab) = 4 * dda := by
    simp only [deltaX]
    rw [hdda]
    ring
  have hrho : rhoX ga gb gc (gb + gc - 2 * gbc) (ga + gc - 2 * gac)
      (ga + gb - 2 * gab) = 4 * (ga * n1 + gb * n2 + gc * n3) := by
    simp only [rhoX]
    rw [hn1, hn2, hn3]
    ring
  -- distance links
  have dA : dist v0 v1 ^ 2 = ga := by
    rw [hga, real_inner_self_eq_norm_sq, dist_eq_norm v0 v1,
      show (v0 : V3) - v1 = -(v1 - v0) from by abel, norm_neg]
  have dB : dist v0 v2 ^ 2 = gb := by
    rw [hgb, real_inner_self_eq_norm_sq, dist_eq_norm v0 v2,
      show (v0 : V3) - v2 = -(v2 - v0) from by abel, norm_neg]
  have dC : dist v0 v3 ^ 2 = gc := by
    rw [hgc, real_inner_self_eq_norm_sq, dist_eq_norm v0 v3,
      show (v0 : V3) - v3 = -(v3 - v0) from by abel, norm_neg]
  have d12 : dist v1 v2 ^ 2 = ga + gb - 2 * gab := by
    rw [dist_eq_norm v1 v2, show (v1 : V3) - v2 = (v1 - v0) - (v2 - v0) from by abel,
      ← real_inner_self_eq_norm_sq, hgram (v1 - v0) (v2 - v0), ← hga, ← hgb, ← hgab]
  have d13 : dist v1 v3 ^ 2 = ga + gc - 2 * gac := by
    rw [dist_eq_norm v1 v3, show (v1 : V3) - v3 = (v1 - v0) - (v3 - v0) from by abel,
      ← real_inner_self_eq_norm_sq, hgram (v1 - v0) (v3 - v0), ← hga, ← hgc, ← hgac]
  have d23 : dist v2 v3 ^ 2 = gb + gc - 2 * gbc := by
    rw [dist_eq_norm v2 v3, show (v2 : V3) - v3 = (v2 - v0) - (v3 - v0) from by abel,
      ← real_inner_self_eq_norm_sq, hgram (v2 - v0) (v3 - v0), ← hgb, ← hgc, ← hgbc]
  -- Δ > 0 via the PA18 Cayley–Menger bridge
  have hDpos : 0 < dda := by
    have hd : 0 < deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
      rw [← delta_delta_x]
      exact (POS_EQ_NOT_COPLANANR v0 v1 v2 v3).mpr
        (fun hca => hnc (coplanar_eq_coplanar_alt.mpr hca))
    rw [dA, dB, dC, d23, d13, d12, hdelt] at hd
    linarith
  -- Cramer weights tᵢ = nᵢ / (2Δ)
  obtain ⟨t1, ht1⟩ : ∃ x, x = n1 / (2 * dda) := ⟨_, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ x, x = n2 / (2 * dda) := ⟨_, rfl⟩
  obtain ⟨t3, ht3⟩ : ∃ x, x = n3 / (2 * dda) := ⟨_, rfl⟩
  -- the Cramer column identities in weight form
  have hdda0 : dda ≠ 0 := ne_of_gt hDpos
  have col1 : t1 * ga + t2 * gab + t3 * gac = ga / 2 := by
    rw [ht1, ht2, ht3]
    field_simp
    linear_combination hc1
  have col2 : t1 * gab + t2 * gb + t3 * gbc = gb / 2 := by
    rw [ht1, ht2, ht3]
    field_simp
    linear_combination hc2
  have col3 : t1 * gac + t2 * gbc + t3 * gc = gc / 2 := by
    rw [ht1, ht2, ht3]
    field_simp
    linear_combination hc3
  -- explicit circumcenter witness q = (t1•e1 + t2•e2 + t3•e3) +ᵥ v0
  set q : V3 := (t1 • (v1 - v0) + t2 • (v2 - v0) + t3 • (v3 - v0)) +ᵥ v0 with hqdef
  have hx0 : (q : V3) - v0 = t1 • (v1 - v0) + t2 • (v2 - v0) + t3 • (v3 - v0) := by
    rw [hqdef, vadd_eq_add]
    abel
  -- inner products of (q - v0) against the edge vectors
  have M1 : inner ℝ ((q : V3) - v0) (v1 - v0) = ga / 2 := by
    rw [hx0]
    simp only [inner_add_left, real_inner_smul_left]
    rw [real_inner_comm (v1 - v0) (v2 - v0), real_inner_comm (v1 - v0) (v3 - v0),
      ← hga, ← hgab, ← hgac]
    exact col1
  have M2 : inner ℝ ((q : V3) - v0) (v2 - v0) = gb / 2 := by
    rw [hx0]
    simp only [inner_add_left, real_inner_smul_left]
    rw [real_inner_comm (v2 - v0) (v3 - v0), ← hgab, ← hgb, ← hgbc]
    exact col2
  have M3 : inner ℝ ((q : V3) - v0) (v3 - v0) = gc / 2 := by
    rw [hx0]
    simp only [inner_add_left, real_inner_smul_left, ← hgac, ← hgbc, ← hgc]
    exact col3
  -- equidistance of q from the four vertices
  have nA : ‖v1 - v0‖ ^ 2 = ga := by rw [hga, real_inner_self_eq_norm_sq]
  have nB : ‖v2 - v0‖ ^ 2 = gb := by rw [hgb, real_inner_self_eq_norm_sq]
  have nC : ‖v3 - v0‖ ^ 2 = gc := by rw [hgc, real_inner_self_eq_norm_sq]
  have nrm1 : ‖(q : V3) - v1‖ ^ 2 = ‖(q : V3) - v0‖ ^ 2 := by
    have e : ((q : V3) - v1) = ((q : V3) - v0) - (v1 - v0) := by abel
    have e2 : ‖((q : V3) - v0) - (v1 - v0)‖ ^ 2
        = ‖(q : V3) - v0‖ ^ 2 + ‖v1 - v0‖ ^ 2
          - 2 * inner ℝ ((q : V3) - v0) (v1 - v0) := by
      simp only [← real_inner_self_eq_norm_sq, hgram (q - v0) (v1 - v0)]
    rw [e, e2, M1, nA]
    ring
  have nrm2 : ‖(q : V3) - v2‖ ^ 2 = ‖(q : V3) - v0‖ ^ 2 := by
    have e : ((q : V3) - v2) = ((q : V3) - v0) - (v2 - v0) := by abel
    have e2 : ‖((q : V3) - v0) - (v2 - v0)‖ ^ 2
        = ‖(q : V3) - v0‖ ^ 2 + ‖v2 - v0‖ ^ 2
          - 2 * inner ℝ ((q : V3) - v0) (v2 - v0) := by
      simp only [← real_inner_self_eq_norm_sq, hgram (q - v0) (v2 - v0)]
    rw [e, e2, M2, nB]
    ring
  have nrm3 : ‖(q : V3) - v3‖ ^ 2 = ‖(q : V3) - v0‖ ^ 2 := by
    have e : ((q : V3) - v3) = ((q : V3) - v0) - (v3 - v0) := by abel
    have e2 : ‖((q : V3) - v0) - (v3 - v0)‖ ^ 2
        = ‖(q : V3) - v0‖ ^ 2 + ‖v3 - v0‖ ^ 2
          - 2 * inner ℝ ((q : V3) - v0) (v3 - v0) := by
      simp only [← real_inner_self_eq_norm_sq, hgram (q - v0) (v3 - v0)]
    rw [e, e2, M3, nC]
    ring
  have dd1 : dist (q : V3) v1 = dist (q : V3) v0 := by
    rw [dist_eq_norm, dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp nrm1
  have dd2 : dist (q : V3) v2 = dist (q : V3) v0 := by
    rw [dist_eq_norm, dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp nrm2
  have dd3 : dist (q : V3) v3 = dist (q : V3) v0 := by
    rw [dist_eq_norm, dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp nrm3
  have hcd : ∃ c : ℝ, ∀ w ∈ ({v0, v1, v2, v3} : Set V3), dist (q : V3) w = c := by
    refine ⟨dist (q : V3) v0, ?_⟩
    rintro w (rfl | rfl | rfl | rfl)
    · rfl
    · exact dd1
    · exact dd2
    · exact dd3
  -- q sits on the affine hull
  have hdir : (affineSpan ℝ ({v0, v1, v2, v3} : Set V3)).direction
      = Submodule.span ℝ ({v1 - v0, v2 - v0, v3 - v0} : Set V3) := by
    rw [direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right ℝ (show v0 ∈ ({v0, v1, v2, v3} : Set V3) from by simp)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro p ⟨z, hz, rfl⟩
      rcases hz with rfl | rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      rintro p (rfl | rfl | rfl)
      · exact Submodule.subset_span ⟨v1, by simp, rfl⟩
      · exact Submodule.subset_span ⟨v2, by simp, rfl⟩
      · exact Submodule.subset_span ⟨v3, by simp, rfl⟩
  have h1m : t1 • (v1 - v0) ∈ Submodule.span ℝ ({v1 - v0, v2 - v0, v3 - v0} : Set V3) :=
    Submodule.smul_mem _ t1 (Submodule.subset_span (by simp))
  have h2m : t2 • (v2 - v0) ∈ Submodule.span ℝ ({v1 - v0, v2 - v0, v3 - v0} : Set V3) :=
    Submodule.smul_mem _ t2 (Submodule.subset_span (by simp))
  have h3m : t3 • (v3 - v0) ∈ Submodule.span ℝ ({v1 - v0, v2 - v0, v3 - v0} : Set V3) :=
    Submodule.smul_mem _ t3 (Submodule.subset_span (by simp))
  have hxmem : t1 • (v1 - v0) + t2 • (v2 - v0) + t3 • (v3 - v0)
      ∈ (affineSpan ℝ ({v0, v1, v2, v3} : Set V3)).direction := by
    rw [hdir]
    exact Submodule.add_mem _ (Submodule.add_mem _ h1m h2m) h3m
  have hqmem : (q : V3) ∈ (affineSpan ℝ ({v0, v1, v2, v3} : Set V3) : Set V3) :=
    AffineSubspace.vadd_mem_of_mem_direction hxmem
      (subset_affineSpan ℝ ({v0, v1, v2, v3} : Set V3) (by simp))
  -- q is THE circumcenter; OAPVION2 hands radV to it
  have hqcc : (q : V3) = circumcenter ({v0, v1, v2, v3} : Set V3) :=
    OAPVION3_concl _ haff q hqmem hcd
  have hR := OAPVION2_concl ({v0, v1, v2, v3} : Set V3) haff v0 (by simp)
  rw [← hqcc] at hR
  -- the squared circumradius as a Cramer quotient
  have Xinner : ∀ y : V3, inner ℝ ((q : V3) - v0) y
      = t1 * inner ℝ (v1 - v0) y + t2 * inner ℝ (v2 - v0) y
        + t3 * inner ℝ (v3 - v0) y := by
    intro y
    rw [hx0]
    simp only [inner_add_left, real_inner_smul_left]
  have M1' : inner ℝ (v1 - v0) ((q : V3) - v0) = ga / 2 := by
    rw [real_inner_comm]
    exact M1
  have M2' : inner ℝ (v2 - v0) ((q : V3) - v0) = gb / 2 := by
    rw [real_inner_comm]
    exact M2
  have M3' : inner ℝ (v3 - v0) ((q : V3) - v0) = gc / 2 := by
    rw [real_inner_comm]
    exact M3
  have nfin : ‖(q : V3) - v0‖ ^ 2
      = (ga * n1 + gb * n2 + gc * n3) / (4 * dda) := by
    rw [← real_inner_self_eq_norm_sq, Xinner, M1', M2', M3', ht1, ht2, ht3]
    ring
  -- final assembly
  rw [hR, dist_eq_norm, nfin]
  simp only [rad2XP25, rad2X, dA, dB, dC, d23, d13, d12, hdelt, hrho]
  ring

/-- HOL `DIST_IMP_COLLINEAR`. -/
theorem DIST_IMP_COLLINEAR (u0 u1 u2 : V3)
    (h1 : 2 ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) (h3 : 2 ≤ dist u1 u2)
    (h4 : dist u0 u1 < 4) (h5 : dist u0 u2 < 4) (h6 : dist u1 u2 < 4) :
    ¬ Collinear3 u0 u1 u2 := by
  intro hcol
  rcases eq_or_ne u1 u0 with heq | hne
  · rw [heq, dist_self] at h1
    linarith
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := u0) (w := u1) (w1 := u2) hne).mp hcol
  have hω1 : dist u0 u1 = ‖u1 - u0‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  have hω2 : dist u0 u2 = |c| * ‖u1 - u0‖ := by
    rw [dist_eq_norm, norm_sub_rev, hc, norm_smul, Real.norm_eq_abs]
  have hsub : (u1 - u2 : V3) = (1 - c) • (u1 - u0) := by
    rw [sub_smul, one_smul, ← hc]
    abel
  have hω3 : dist u1 u2 = |1 - c| * ‖u1 - u0‖ := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
  rcases lt_or_ge c 1 with hc1 | hc1
  · rcases lt_or_ge 0 c with hc0 | hc0
    · have e : dist u0 u1 = dist u0 u2 + dist u1 u2 := by
        rw [hω2, hω3, hω1, abs_of_nonneg (by linarith : (0 : ℝ) ≤ c),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - c)]
        ring
      linarith
    · have e : dist u1 u2 = dist u0 u1 + dist u0 u2 := by
        rw [hω2, hω3, hω1, abs_of_nonpos (by linarith : (c : ℝ) ≤ 0),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - c)]
        ring
      linarith
  · have e : dist u0 u2 = dist u0 u1 + dist u1 u2 := by
      rw [hω2, hω3, hω1, abs_of_nonneg (by linarith : (0 : ℝ) ≤ c),
        abs_of_nonpos (by linarith : (1 - c : ℝ) ≤ 0)]
      ring
    linarith

/-- HOL `UPS_X8_POS` (needs certified interval bounds). -/
theorem UPS_X8_POS {y5 y6 : ℝ} (h5 : 2 ≤ y5) (h5' : y5 < 4) (h6 : 2 ≤ y6)
    (h6' : y6 < 4) : 0 < upsX 8 (y5 * y5) (y6 * y6) := by
  have ha : 4 ≤ y5 * y5 := by nlinarith
  have hb : y5 * y5 < 16 := by nlinarith
  have hc : 4 ≤ y6 * y6 := by nlinarith
  have hd : y6 * y6 < 16 := by nlinarith
  have key : upsX 8 (y5 * y5) (y6 * y6) =
      64 + 16 * (y5 * y5 - 4) + 16 * (y6 * y6 - 4) +
        2 * (y5 * y5 - 4) * (y6 * y6 - 4) -
        (y5 * y5 - 4) ^ 2 - (y6 * y6 - 4) ^ 2 := by
    unfold upsX
    ring
  have p1 : 0 ≤ (y5 * y5 - 4) * (y6 * y6 - 4) :=
    mul_nonneg (by linarith) (by linarith)
  have p2 : (y5 * y5 - 4) ^ 2 ≤ 12 * (y5 * y5 - 4) :=
    by have t2 : 0 ≤ (y5 * y5 - 4) * (12 - (y5 * y5 - 4)) :=
         mul_nonneg (by linarith) (by linarith)
       linarith
  have p3 : (y6 * y6 - 4) ^ 2 ≤ 12 * (y6 * y6 - 4) :=
    by have t2 : 0 ≤ (y6 * y6 - 4) * (12 - (y6 * y6 - 4)) :=
         mul_nonneg (by linarith) (by linarith)
       linarith
  rw [key]
  nlinarith

/-- HOL `DIST_IMP_UPS_X_POS`. -/
theorem DIST_IMP_UPS_X_POS (u0 u1 u2 : V3)
    (h1 : 2 ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) (h3 : 2 ≤ dist u1 u2)
    (h4 : dist u0 u1 < 4) (h5 : dist u0 u2 < 4) (h6 : dist u1 u2 < 4) :
    0 < upsX (dist u0 u1 ^ 2) (dist u0 u2 ^ 2) (dist u1 u2 ^ 2) := by
  have hnc := DIST_IMP_COLLINEAR u0 u1 u2 h1 h2 h3 h4 h5 h6
  have hd01 : dist u0 u1 ≠ 0 := by
    intro hzz
    rw [hzz] at h1
    linarith
  have hd02 : dist u0 u2 ≠ 0 := by
    intro hzz
    rw [hzz] at h2
    linarith
  have hne : u1 ≠ u0 := by
    intro hzz
    exact hd01 (by rw [hzz]; simp)
  have hne2 : u2 ≠ u0 := by
    intro hzz
    exact hd02 (by rw [hzz]; simp)
  have hv1n : (u1 - u0 : V3) ≠ 0 := by
    intro hzz
    exact hne (sub_eq_zero.mp hzz)
  have hv2n : (u2 - u0 : V3) ≠ 0 := by
    intro hzz
    exact hne2 (sub_eq_zero.mp hzz)
  have hx1n : (‖u1 - u0‖ ^ 2 : ℝ) ≠ 0 :=
    ne_of_gt (sq_pos_iff.mpr (norm_pos_iff.mpr hv1n).ne')
  have hcol0 : ¬ Collinear3 (0 : V3) (u1 - u0) (u2 - u0) := by
    intro h0
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := (0 : V3)) (w := u1 - u0)
      (w1 := u2 - u0) hv1n).mp h0
    exact hnc ((collinear3_iff_smul (v := u0) (w := u1) (w1 := u2) hne).mpr
      ⟨c, by simpa using hc⟩)
  -- the Gram identity for `ups_x`
  have hup : upsX (‖u1 - u0‖ ^ 2) (‖u2 - u0‖ ^ 2)
        (‖(u1 - u0) - (u2 - u0)‖ ^ 2) =
      4 * (‖u1 - u0‖ ^ 2 * ‖u2 - u0‖ ^ 2 -
        (inner ℝ (u1 - u0) (u2 - u0)) ^ 2) := by
    have hdsq : ‖(u1 - u0) - (u2 - u0)‖ ^ 2
        = ‖u1 - u0‖ ^ 2 + ‖u2 - u0‖ ^ 2 -
          2 * inner ℝ (u1 - u0) (u2 - u0) := by
      rw [norm_sub_sq_real]
      ring
    unfold upsX
    rw [hdsq]
    ring
  have e1 : dist u0 u1 ^ 2 = ‖u1 - u0‖ ^ 2 := by rw [dist_eq_norm, norm_sub_rev]
  have e2 : dist u0 u2 ^ 2 = ‖u2 - u0‖ ^ 2 := by rw [dist_eq_norm, norm_sub_rev]
  have hsub : ((u1 - u0) - (u2 - u0) : V3) = u1 - u2 := by abel
  have e3 : dist u1 u2 ^ 2 = ‖(u1 - u0) - (u2 - u0)‖ ^ 2 := by
    rw [dist_eq_norm, ← hsub]
  rw [e1, e2, e3, hup]
  -- strict Cauchy–Schwarz from non-collinearity
  have hcs : (inner ℝ (u1 - u0) (u2 - u0)) ^ 2 < ‖u1 - u0‖ ^ 2 * ‖u2 - u0‖ ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have hnorm0 : ‖(inner ℝ (u1 - u0) (u2 - u0)) • (u1 - u0) -
        ‖u1 - u0‖ ^ 2 • (u2 - u0)‖ ^ 2 =
        ‖u1 - u0‖ ^ 2 * (‖u1 - u0‖ ^ 2 * ‖u2 - u0‖ ^ 2 -
          (inner ℝ (u1 - u0) (u2 - u0)) ^ 2) := by
      rw [norm_sub_sq_real]
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [mul_pow, mul_pow]
      rw [sq_abs (a := inner ℝ (u1 - u0) (u2 - u0)),
        sq_abs (a := (‖u1 - u0‖ ^ 2 : ℝ))]
      rw [real_inner_smul_left, real_inner_smul_right]
      ring
    have hsq0 : ‖(inner ℝ (u1 - u0) (u2 - u0)) • (u1 - u0) -
        ‖u1 - u0‖ ^ 2 • (u2 - u0)‖ ^ 2 = 0 := by
      have hge : 0 ≤ ‖(inner ℝ (u1 - u0) (u2 - u0)) • (u1 - u0) -
          ‖u1 - u0‖ ^ 2 • (u2 - u0)‖ ^ 2 := sq_nonneg _
      rw [hnorm0]
      have h1n : 0 ≤ ‖u1 - u0‖ ^ 2 := sq_nonneg _
      have h2n : ‖u1 - u0‖ ^ 2 * ‖u2 - u0‖ ^ 2 -
          (inner ℝ (u1 - u0) (u2 - u0)) ^ 2 ≤ 0 := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2n h1n
      rw [mul_zero] at h3
      exact le_antisymm h3 (by rw [← hnorm0]; exact hge)
    have hwz : (inner ℝ (u1 - u0) (u2 - u0)) • (u1 - u0) -
        ‖u1 - u0‖ ^ 2 • (u2 - u0) = 0 := by
      rw [← norm_eq_zero]
      exact sq_eq_zero_iff.mp hsq0
    have hcancel : ‖u1 - u0‖ ^ 2 • (u2 - u0) =
        ‖u1 - u0‖ ^ 2 •
          ((inner ℝ (u1 - u0) (u2 - u0) / ‖u1 - u0‖ ^ 2) • (u1 - u0)) := by
      rw [smul_smul]
      have hscale : (‖u1 - u0‖ ^ 2 : ℝ) *
          (inner ℝ (u1 - u0) (u2 - u0) / ‖u1 - u0‖ ^ 2)
          = inner ℝ (u1 - u0) (u2 - u0) := by field_simp
      rw [hscale, sub_eq_zero.mp hwz]
    have hv2eq : (u2 - u0 : V3) =
        (inner ℝ (u1 - u0) (u2 - u0) / ‖u1 - u0‖ ^ 2) • (u1 - u0) :=
      smul_right_injective _ hx1n hcancel
    exact hcol0 ((collinear3_iff_smul (v := (0 : V3)) (w := u1 - u0)
      (w1 := u2 - u0) hv1n).mpr ⟨_, by simpa using hv2eq⟩)
  linarith [hcs]

/-- HOL `dih_x < pi`: the angle computed by `atn2` from a positive first
argument stays below `pi/2` in every quadrant branch. -/
theorem DIH_X_LT_PI {x1 x2 x3 x4 x5 x6 : ℝ} (h1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    dihXf x1 x2 x3 x4 x5 x6 < Real.pi := by
  unfold dihXf
  have hx : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (mul_pos (by linarith) hd)
  have harg : atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      (-(deltaX4 x1 x2 x3 x4 x5 x6)) < Real.pi / 2 := by
    unfold atn2
    split_ifs with hb hb2 hb3
    · have hfrac : -(deltaX4 x1 x2 x3 x4 x5 x6) /
          Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) < 1 := by
        rw [div_lt_one hx]
        have habs := abs_lt.mp hb
        linarith
      exact Real.arctan_lt_pi_div_two _
    · have hpos : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) /
            -(deltaX4 x1 x2 x3 x4 x5 x6) := div_pos hx hb2
      have hap := Real.arctan_pos.mpr hpos
      linarith
    · exact by
        have hge := Real.neg_pi_div_two_lt_arctan
          (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) /
            -(deltaX4 x1 x2 x3 x4 x5 x6))
        have hpi : 0 < Real.pi := Real.pi_pos
        linarith
    · exact absurd hx (by
        have hy : -(deltaX4 x1 x2 x3 x4 x5 x6) = 0 := by linarith
        rw [hy] at hb
        simp at hb
        have hle : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) = 0 :=
          Real.sqrt_eq_zero_of_nonpos hb
        linarith)
  linarith

/-- HOL `DIH_Y_LT_PI`. -/
theorem DIH_Y_LT_PI {y1 y2 y3 y4 y5 y6 : ℝ} (h1 : 0 < y1)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    dihY y1 y2 y3 y4 y5 y6 < Real.pi := by
  refine DIH_X_LT_PI (by positivity) hd

/-- HOL `CRITICAL_WEIGHT_POS_LE`. -/
theorem CRITICAL_WEIGHT_POS_LE (V X : Set V3) : 0 ≤ criticalWeight V X :=
  div_nonneg zero_le_one (Nat.cast_nonneg _)

/-- HOL `GAMMAX_NO_BETA`.  Proof: for `k < 4` cells the bump correction
`betaBumpV1` vanishes (`MCELL_BUMP_0`, PackingAuto4 — the bump condition
needs both `e` and its complement critical, killed by `k < 4`), and the
remaining product is nonnegative. -/
theorem GAMMAX_NO_BETA (V : Set V3) (ul : List V3) (X : Set V3) (e : Set V3) (k : ℕ)
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell k V ul)
    (hn : ¬ nullSet X) (hk : k < 4) (he : e ∈ criticalEdgeX V X)
    (hg : gammaX V X lmfun ≥ 0) :
    gammaX V X lmfun * criticalWeight V X + betaBumpV1 V e X ≥ 0 := by
  have hbb : betaBumpV1 V e X = 0 := by
    have hco : betaBumpV1 V e X = betaBump V e X := rfl
    have hnm : ¬ nullSet (mcell k V ul) := by rw [← hX]; exact hn
    rw [hco, hX]
    exact BumpP4.MCELL_BUMP_0 V ul e k hk hp hs hb hnm
  rw [hbb]
  exact add_nonneg (mul_nonneg hg (CRITICAL_WEIGHT_POS_LE V X)) (by simp)

/-- HOL `REUHADY` (owned by the REUHADY.hl lane — PackingAuto24; the copy
here is the form consumed by `LEAF_RANK_REUHADY` below). -/
theorem REUHADY (V : Set V3) (u0 u1 v1 v2 : V3) (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V [u0, u1, v1]) (hl2 : leaf V [u0, u1, v2]) (hv : v1 ≠ v2) :
    setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧ X ⊆ wedgeGe u0 u1 v1 v2}
        (fun t => dihX V t (u0, u1)) =
      azim u0 u1 v1 v2 := by
  sorry

/-- HOL `s_leaf_leaf`. -/
theorem s_leaf_leaf (V : Set V3) (ul : List V3) (x : V3) (hx : x ∈ s_leaf V ul) :
    leaf V [elV ul 0, elV ul 1, x] := hx.1

/-- Helper: three distinct collinear points have no equidistant point. -/
private theorem p25_collinear3_eq_dist {a b x p : V3} (hcol : Collinear3 a b x)
    (hab : a ≠ b) (h1 : dist p a = dist p b) (h2 : dist p a = dist p x) :
    x = a ∨ x = b := by
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := a) (w := b) (w1 := x) (Ne.symm hab)).mp hcol
  have hd : (b - a : V3) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hab h.symm
  have heq1 : ‖p - b‖ ^ 2 = ‖p - a‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, h1]
  have e1 : 2 * (inner ℝ (p - a) (b - a)) = ‖(b - a : V3)‖ ^ 2 := by
    have hsq : ‖p - b‖ ^ 2 =
        ‖p - a‖ ^ 2 - 2 * inner ℝ (p - a) (b - a) + ‖(b - a : V3)‖ ^ 2 := by
      rw [show (p - b : V3) = (p - a) - (b - a) from by abel, norm_sub_sq_real]
    linarith
  have heq2 : ‖p - x‖ ^ 2 = ‖p - a‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, h2]
  have e2 : 2 * (c * inner ℝ (p - a) (b - a)) = c ^ 2 * ‖(b - a : V3)‖ ^ 2 := by
    have hx' : x = c • (b - a) + a := sub_eq_iff_eq_add.mp hc
    have hpx : (p - x : V3) = (p - a) - c • (b - a) := by
      rw [hx']; abel
    have hsq : ‖p - x‖ ^ 2 =
        ‖p - a‖ ^ 2 - 2 * inner ℝ (p - a) (c • (b - a : V3)) +
          ‖c • (b - a : V3)‖ ^ 2 := by
      rw [hpx, norm_sub_sq_real]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right] at hsq
    linarith
  by_cases hc0 : c = 0
  · left
    rw [hc0] at hc
    have hza : x - a = 0 := by simpa using hc
    exact sub_eq_zero.mp hza
  · right
    have hY : ‖(b - a : V3)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
    have hz : c * (1 - c) * ‖(b - a : V3)‖ ^ 2 = 0 := by
      linear_combination (norm := ring_nf) (e2 - c * e1)
    rcases mul_eq_zero.mp hz with hz1 | hz1
    · rcases mul_eq_zero.mp hz1 with hz2 | hz2
      · exact absurd hz2 hc0
      · have hc1 : c = 1 := by linarith
        have hcs : x - a = b - a := by rw [hc1] at hc; simpa using hc
        calc x = x - a + a := by abel
          _ = b - a + a := by rw [hcs]
          _ = b := by abel
    · exact absurd hz1 hY

/-- HOL `s_leaf_collinear`.  Proof: the `voronoi_nondg` clauses of
`barV V 2 [u0, u1, x]` force the affDim values 3 / 2 / 1 on the three
initial sublists; a degenerate or collinear triple makes two of them refer
to the same voronoi set (or, when the three points are distinct and
collinear, to an empty set of equidistant points), contradicting the
distinct affine dimensions. -/
theorem s_leaf_collinear (V : Set V3) (ul : List V3) (x : V3) (hp : Packing V)
    (hs : saturated V) (hx : x ∈ s_leaf V ul) : ¬ Collinear3 (elV ul 0) (elV ul 1) x := by
  have hleaf : leaf V [elV ul 0, elV ul 1, x] := hx.1
  have hfull := hleaf.1.2 [elV ul 0, elV ul 1, x] ⟨⟨[], rfl⟩, by simp⟩
  have hpair := hleaf.1.2 [elV ul 0, elV ul 1] ⟨⟨[x], rfl⟩, by simp⟩
  have hsingle := hleaf.1.2 [elV ul 0] ⟨⟨[elV ul 1, x], rfl⟩, by simp⟩
  have hdim1 : affDim (voronoiList V [elV ul 0, elV ul 1, x]) = 1 := by
    have h := hfull.2.2
    rw [show ((([elV ul 0, elV ul 1, x] : List V3).length : ℤ)) = 3 from by simp] at h
    omega
  have hdim2 : affDim (voronoiList V [elV ul 0, elV ul 1]) = 2 := by
    have h := hpair.2.2
    rw [show ((([elV ul 0, elV ul 1] : List V3).length : ℤ)) = 2 from by simp] at h
    omega
  have hdim3 : affDim (voronoiList V [elV ul 0]) = 3 := by
    have h := hsingle.2.2
    rw [show ((([elV ul 0] : List V3).length : ℤ)) = 1 from by simp] at h
    omega
  intro hcol
  have vlist_eq : ∀ l1 l2 : List V3, setOfList l1 = setOfList l2 →
      voronoiList V l1 = voronoiList V l2 := by
    intro l1 l2 h
    show voronoiSet V (setOfList l1) = voronoiSet V (setOfList l2)
    rw [h]
  by_cases hab : elV ul 0 = elV ul 1
  · rw [hab] at hdim2 hdim3
    have hset := vlist_eq [elV ul 1, elV ul 1] [elV ul 1] (by
      ext q; simp [setOfList])
    rw [hset] at hdim2
    omega
  by_cases hax : elV ul 0 = x
  · rw [← hax] at hdim1
    have hset := vlist_eq [elV ul 0, elV ul 1, elV ul 0] [elV ul 0, elV ul 1] (by
      ext q
      simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil]
      tauto)
    rw [hset] at hdim1
    omega
  by_cases hbx : elV ul 1 = x
  · rw [← hbx] at hdim1
    have hset := vlist_eq [elV ul 0, elV ul 1, elV ul 1] [elV ul 0, elV ul 1] (by
      ext q; simp [setOfList])
    rw [hset] at hdim1
    omega
  · -- distinct and collinear: no equidistant point exists
    obtain ⟨p, hpmem⟩ : (voronoiList V [elV ul 0, elV ul 1, x] : Set V3).Nonempty := by
      by_contra hcon
      push_neg at hcon
      rw [hcon] at hdim1
      rw [affDim_empty] at hdim1
      omega
    simp only [voronoiList, voronoiSet, Set.mem_sInter] at hpmem
    have hmem : ∀ w ∈ (setOfList [elV ul 0, elV ul 1, x] : Set V3),
        ∀ z ∈ (setOfList [elV ul 0, elV ul 1, x] : Set V3), dist p w ≤ dist p z := by
      intro w hw z hz
      have hw' : p ∈ voronoiClosed V w :=
        hpmem (voronoiClosed V w) ⟨w, hw, rfl⟩
      exact hw' z (hfull.2.1 hz)
    have hab' : dist p (elV ul 0) = dist p (elV ul 1) :=
      le_antisymm (hmem _ (by simp [setOfList]) _ (by simp [setOfList]))
        (hmem _ (by simp [setOfList]) _ (by simp [setOfList]))
    have hax' : dist p (elV ul 0) = dist p x :=
      le_antisymm (hmem _ (by simp [setOfList]) _ (by simp [setOfList]))
        (hmem _ (by simp [setOfList]) _ (by simp [setOfList]))
    rcases p25_collinear3_eq_dist hcol hab hab' hax' with he | he
    · exact hax he.symm
    · exact hbx he.symm

/-- leaf-rank 波 helper（真证）：`COLL_IN_AFF_GT_AFF_GT_EQ`
（local_lemmas.hl:5488）的移植——非退化顶点锥的成员给出锥相等。
Proof: 两个方向都经 `affGt_pair_iff` 的射线表示重组（`module` 系数吸收）。 -/
private theorem p25_affGt_eq_of_mem {v0 v1 z a : V3}
    (hv0v1 : v0 ≠ v1) (hz0 : z ≠ v0) (hz1 : z ≠ v1) (ha0 : a ≠ v0) (ha1 : a ≠ v1)
    (ha : a ∈ affGt {v0, v1} {z}) :
    affGt {v0, v1} {z} = affGt {v0, v1} {a} := by
  obtain ⟨c, hc, h, hray⟩ := (affGt_pair_iff hv0v1 hz0 hz1).mp ha
  have hiffz : ∀ q : V3, q ∈ affGt {v0, v1} {z} ↔
      ∃ c : ℝ, 0 < c ∧ ∃ h : ℝ, q - v0 = c • (z - v0) + h • (v1 - v0) :=
    fun q => affGt_pair_iff hv0v1 hz0 hz1
  have hiffa : ∀ q : V3, q ∈ affGt {v0, v1} {a} ↔
      ∃ c : ℝ, 0 < c ∧ ∃ h : ℝ, q - v0 = c • (a - v0) + h • (v1 - v0) :=
    fun q => affGt_pair_iff hv0v1 ha0 ha1
  -- 射线反解：z 在 a 的射线表示下的坐标
  have hray' : c • (z - v0) = (a - v0) - h • (v1 - v0) := by
    rw [hray]; module
  have key : (z - v0 : V3) = (1 / c) • ((a - v0) - h • (v1 - v0)) := by
    have h1 : (z - v0 : V3) = (1 / c) • (c • (z - v0)) := by
      rw [smul_smul, show ((1 : ℝ) / c) * c = 1 from by field_simp, one_smul]
    rw [h1, hray']
  ext q
  constructor
  · intro hq
    obtain ⟨c2, hc2, h2, hq2⟩ := (hiffz q).mp hq
    refine (hiffa q).mpr ⟨c2 / c, by positivity, h2 - c2 * h / c, ?_⟩
    rw [hq2, key]
    module
  · intro hq
    obtain ⟨c3, hc3, h3, hq3⟩ := (hiffa q).mp hq
    refine (hiffz q).mpr ⟨c3 * c, by positivity, c3 * h + h3, ?_⟩
    rw [hq3, hray]
    module

/-- leaf-rank 波收窄件（GIANT 收窄的**唯一**残余债）：同一茎上两叶的 `w0`-方位角
相等 ⇒ 点相等。HOL OXLZLEZ3.hl:931-942（`LEAF_RANKING_LEMMA` 内联段）：
`azim w0 x = azim w0 y` 经 `AZIM_EQ_ALT` 得 `x ∈ aff_gt {u0,u1} {y}`，经
`COLL_IN_AFF_GT_AFF_GT_EQ` 得 `cc_A0` 两锥相等，最终由 `Leaf_cell.FCHKUGT`
（leaf_cell.hl:3432）收尾。
-- NEEDS: 仅欠 `FCHKUGT`（PA18 :2159 ⬜，leaf-cell 链 GIANT，PA18 车道
在攻）——落证后本件即刻全真，无其他缺口。 -/
private theorem p25_leaf_azim_inj (V : Set V3) (ul : List V3) (w0 x y : V3)
    (hp : Packing V) (hs : saturated V) (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0)
    (hx : x ∈ s_leaf V ul) (hy : y ∈ s_leaf V ul)
    (haz : azim (elV ul 0) (elV ul 1) w0 x = azim (elV ul 0) (elV ul 1) w0 y) :
    x = y := by
  have hcolx : ¬ Collinear3 (elV ul 0) (elV ul 1) x := s_leaf_collinear V ul x hp hs hx
  have hcoly : ¬ Collinear3 (elV ul 0) (elV ul 1) y := s_leaf_collinear V ul y hp hs hy
  have hxy : x ∈ affGt {elV ul 0, elV ul 1} {y} :=
    (azim_eq_azim_iff_alt hnc hcolx hcoly).mp haz
  have hv0v1 : (elV ul 0 : V3) ≠ elV ul 1 := fun he =>
    hcoly (collinear3_of_eq he.symm)
  have hy0 : (y : V3) ≠ elV ul 0 := fun he => hcoly (collinear3_pair_left he)
  have hy1 : (y : V3) ≠ elV ul 1 := fun he => hcoly (collinear3_pair_right he)
  have hx0 : (x : V3) ≠ elV ul 0 := fun he => hcolx (collinear3_pair_left he)
  have hx1 : (x : V3) ≠ elV ul 1 := fun he => hcolx (collinear3_pair_right he)
  have hcone : affGt {elV ul 0, elV ul 1} {y} = affGt {elV ul 0, elV ul 1} {x} :=
    p25_affGt_eq_of_mem hv0v1 hy0 hy1 hx0 hx1 hxy
  exact FCHKUGT hs hp (show ccA0 [elV ul 0, elV ul 1, x] = ccA0 [elV ul 0, elV ul 1, y] from
    hcone.symm) hx.1 hy.1

/-- HOL `LEAF_RANKING_LEMMA`: existence of the azim-ordered cyclic
parametrization of `s_leaf`.
leaf-rank 波（2026-10-08）转真：引擎 `STRICT_SORT_FINITE`（本文件 :539，
以 `w0`-方位角 `≤` 为序，反对称性由 `p25_leaf_azim_inj` 收窄件供给）给出
`1..n` 的 azim-单射枚举，再以 `i ↦ g (i % n + 1)` 做模 `n` 环参数化
（`p25_f_mod`/`Nat.mod_eq_of_lt` 记账）。债面 = `p25_leaf_azim_inj`
（上游 `FCHKUGT`，PA18 车道）。 -/
theorem LEAF_RANKING_LEMMA (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (hn : 0 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n) (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    ∃ f : ℕ → V3, f '' (univ : Set ℕ) = s_leaf V ul ∧
      (∀ i, f (i + n) = f i) ∧
      (∀ i j, i < n → j < n → i < j →
        azim (elV ul 0) (elV ul 1) w0 (f i) < azim (elV ul 0) (elV ul 1) w0 (f j)) := by
  classical
  obtain ⟨g, himg, hmono⟩ := STRICT_SORT_FINITE (α := V3)
    (lt := fun v w => azim (elV ul 0) (elV ul 1) w0 v ≤ azim (elV ul 0) (elV ul 1) w0 w)
    (s_leaf V ul) n
    (fun x y hx hy h1 h2 =>
      p25_leaf_azim_inj V ul w0 x y hp hs hnc hx hy (le_antisymm h1 h2))
    (fun _ _ _ _ _ _ h1 h2 => le_trans h1 h2)
    hsize
  refine ⟨fun i => g (i % n + 1), ?_, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨i, -, rfl⟩
      have h1 : i % n + 1 ∈ Set.Icc 1 n :=
        ⟨by omega, by have := Nat.mod_lt i hn; omega⟩
      have hmem : g (i % n + 1) ∈ g '' Set.Icc 1 n := ⟨i % n + 1, h1, rfl⟩
      rw [himg]
      exact hmem
    · intro hq
      rw [himg] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      obtain ⟨hk1, hk2⟩ := Set.mem_Icc.mp hk
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      have hklt : k - 1 < n := by omega
      show g ((k - 1) % n + 1) = g k
      rw [show ((k - 1 : ℕ) % n) = k - 1 from Nat.mod_eq_of_lt hklt,
        show k - 1 + 1 = k from by omega]
  · intro i
    have hmod : (i + n) % n = i % n := Nat.add_mod_right i n
    show g ((i + n) % n + 1) = g (i % n + 1)
    rw [hmod]
  · intro i j hi hj hij
    have hmi : i % n = i := Nat.mod_eq_of_lt hi
    have hmj : j % n = j := Nat.mod_eq_of_lt hj
    have hm1 : i + 1 ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
    have hm2 : j + 1 ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
    have hle := hmono (i + 1) (j + 1) hm1 hm2 (by omega)
    show azim (elV ul 0) (elV ul 1) w0 (g (i % n + 1)) <
      azim (elV ul 0) (elV ul 1) w0 (g (j % n + 1))
    rw [hmi, hmj]
    exact not_le.mp hle

/-- HOL `S_LEAF_SET` (definitional). -/
theorem S_LEAF_SET (V : Set V3) (ul : List V3) :
    s_leaf V ul = {u | leaf V [elV ul 0, elV ul 1, u] ∧
      (ccKe V [elV ul 0, elV ul 1, u] = 4 ∨ ccKe V [elV ul 1, elV ul 0, u] = 4)} :=
  rfl

/-- HOL `LEAF_RANK_COLLINEAR` (renamed from LEAF_RANK_COLLINEAR). -/
theorem LEAF_RANK_COLLINEAR (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (k : ℕ) (hp : Packing V) (hs : saturated V) (hr : leaf_rank V ul w0 n f) :
    ¬ Collinear3 (elV ul 0) (elV ul 1) (f k) := by
  have hm : f k ∈ s_leaf V ul := by
    have h1 : f k ∈ f '' (univ : Set ℕ) := ⟨k, Set.mem_univ _, rfl⟩
    exact hr.1 ▸ h1
  exact s_leaf_collinear V ul (f k) hp hs hm

/-- HOL `S_LEAF_SUBSET_PACKING`. -/
theorem S_LEAF_SUBSET_PACKING (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) : s_leaf V ul ⊆ V := by
  intro x hx
  have hleaf : barV V 2 [elV ul 0, elV ul 1, x] := hx.1.1
  obtain ⟨-, hpre⟩ := hleaf
  have hv := hpre [elV ul 0, elV ul 1, x] ⟨⟨[], rfl⟩, by simp⟩
  exact hv.2.1 (by simp [setOfList])

/-- Helper: a non-collinear triple is affinely independent as a set (the
`affineIndependent_set_iff_linearIndependent_vsub` route; the span of one
offset vector would make the third point lie on the line through the other
two). -/
private theorem p25_not_affdep3 {a b x : V3} (hab : a ≠ b) (hax : a ≠ x) (_hbx : b ≠ x)
    (hcol : ¬ Collinear3 a b x) : ¬ affineDependent ({a, b, x} : Set V3) := by
  intro haff
  have hmem_a : (a : V3) ∈ ({a, b, x} : Set V3) := by simp
  refine haff ((affineIndependent_set_iff_linearIndependent_vsub (k := ℝ) hmem_a).mpr ?_)
  have hdiff : (({a, b, x} : Set V3) \ {a}) = ({b, x} : Set V3) := by
    ext z
    by_cases hz : z = a
    · subst hz; simp [hab, hax]
    · simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, hz,
        not_false_iff]
      by_cases h1 : z = b <;> by_cases h2 : z = x <;> simp [h1, h2]
  have himg : ((fun p : V3 => (p -ᵥ a)) '' ({b, x} : Set V3))
      = ({b - a, x - a} : Set V3) := by
    rw [Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [hdiff, himg]
  apply (linearIndependent_subtype_iff).mpr
  refine LinearIndepOn.id_insert (s := ({x - a} : Set V3)) ?_ ?_
  · exact LinearIndepOn.singleton (show (x - a : V3) ≠ 0 from sub_ne_zero.mpr hax.symm)
  · intro hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul] at hc
      exact hab (sub_eq_zero.mp hc.symm).symm
    · exact hcol ((collinear3_iff_smul (hw := Ne.symm hab)).mpr ⟨c⁻¹, by
        rw [hc.symm, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩)

/-- HOL `S_LEAF_BOUNDED`.  Proof: a leaf `x` on the stem has circumradius
`hl [u0, u1, x] < sqrt 2`, and the stem point is at most twice the
circumradius from `x` (both are on the circumsphere, `OAPVION2_concl` —
the triple is affinely independent by `p25_not_affdep3` + `s_leaf_collinear`). -/
theorem S_LEAF_BOUNDED (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) :
    s_leaf V ul ⊆ Metric.ball (elV ul 0) (2 * Real.sqrt 2) := by
  intro x hx
  have hleaf : leaf V [elV ul 0, elV ul 1, x] := hx.1
  have hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) x := s_leaf_collinear V ul x hp hs hx
  have h01 : (elV ul 0 : V3) ≠ elV ul 1 := by
    intro he
    refine hnc (show Collinear ℝ ({elV ul 0, elV ul 1, x} : Set V3) from ?_)
    have hset : ({elV ul 0, elV ul 1, x} : Set V3) = ({elV ul 1, x} : Set V3) := by
      rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact collinear_pair _ _ _
  have h0x : (elV ul 0 : V3) ≠ x := by
    intro he
    refine hnc (show Collinear ℝ ({elV ul 0, elV ul 1, x} : Set V3) from ?_)
    have hset : ({elV ul 0, elV ul 1, x} : Set V3) = ({x, elV ul 1} : Set V3) := by
      rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact collinear_pair _ _ _
  have h1x : (elV ul 1 : V3) ≠ x := by
    intro he
    refine hnc (show Collinear ℝ ({elV ul 0, elV ul 1, x} : Set V3) from ?_)
    have hset : ({elV ul 0, elV ul 1, x} : Set V3) = ({elV ul 0, x} : Set V3) := by
      rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact collinear_pair _ _ _
  have haff : ¬ affineDependent ({elV ul 0, elV ul 1, x} : Set V3) :=
    p25_not_affdep3 h01 h0x h1x hnc
  have hradlt : radV ({elV ul 0, elV ul 1, x} : Set V3) < Real.sqrt 2 := by
    have h2 : hl [elV ul 0, elV ul 1, x] < Real.sqrt 2 := hleaf.2
    rw [hl] at h2
    have hset : setOfList [elV ul 0, elV ul 1, x] = ({elV ul 0, elV ul 1, x} : Set V3) := by
      ext q; simp [setOfList]
    rw [hset] at h2
    exact h2
  have d0 := OAPVION2_concl ({elV ul 0, elV ul 1, x} : Set V3) haff (elV ul 0) (by simp)
  have d1 := OAPVION2_concl ({elV ul 0, elV ul 1, x} : Set V3) haff x (by simp)
  have htri : dist (elV ul 0) x ≤
      dist (elV ul 0) (circumcenter ({elV ul 0, elV ul 1, x} : Set V3)) +
        dist (circumcenter ({elV ul 0, elV ul 1, x} : Set V3)) x :=
    dist_triangle _ _ _
  rw [dist_comm (elV ul 0) (circumcenter ({elV ul 0, elV ul 1, x} : Set V3)), ← d0, ← d1] at htri
  simp only [Metric.mem_ball]
  rw [dist_comm x (elV ul 0)]
  linarith

/-- HOL `S_LEAF_FINITE`.  Proof: `s_leaf` sits inside the packing and inside
a bounded ball (`S_LEAF_BOUNDED`), so it is finite by volume counting
(`Packing.finite_inter_ball`, Kepler.Statement). -/
theorem S_LEAF_FINITE (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) : (s_leaf V ul).Finite := by
  have hb := S_LEAF_BOUNDED V ul hp hs
  have hsub := S_LEAF_SUBSET_PACKING V ul hp hs
  refine Set.Finite.subset
    (hp.finite_inter_ball (2 * Real.sqrt 2 + ‖(elV ul 0 : V3)‖ + 1)) ?_
  intro x hx
  have hbc := hb hx
  refine ⟨hsub hx, ?_⟩
  have hdist : ‖(x : V3)‖ ≤ ‖(x - elV ul 0 : V3)‖ + ‖(elV ul 0 : V3)‖ := by
    conv_lhs => rw [show (x : V3) = (x - elV ul 0) + elV ul 0 from by abel]
    exact norm_add_le _ _
  simp only [Metric.mem_ball] at hbc
  rw [dist_eq_norm] at hbc
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

/-- Helper: prefix-cancel for `take` (used to pin down prefixes). -/
private theorem p25_take_cancel {α : Type*} {l1 l2 : List α} (n : ℕ) (h : n ≤ l1.length) :
    (l1 ++ l2).take n = l1.take n := by
  induction l1 generalizing n with
  | nil => simp at h; simp [h]
  | cons a t ih =>
    cases n with
    | zero => simp
    | succ n =>
      have key : (t ++ l2).take n = t.take n := ih n (Nat.le_of_succ_le_succ h)
      simp [key]

/-- Helper: `leaf` only sees the point set of a length-3 list and the
singleton-voronoi full-dimensionality (`AFF_DIM_VORONOI_CLOSED`), so the two
stem endpoints of a leaf may be swapped. -/
private theorem p25_leaf_swap (V : Set V3) (hp : Packing V) (a b c : V3)
    (hle : leaf V [a, b, c]) : leaf V [b, a, c] := by
  have hlt : hl [a, b, c] < Real.sqrt 2 := hle.2
  have horig := hle.1.2
  have h2 := horig [a, b] ⟨⟨[c], rfl⟩, by simp⟩
  have h3 := horig [a, b, c] ⟨⟨[], rfl⟩, by simp⟩
  have hvb : voronoiList V [b] = voronoiClosed V b := by
    refine Set.ext fun q => ?_
    simp only [voronoiList, voronoiSet, Set.mem_sInter]
    constructor
    · intro h
      exact h (voronoiClosed V b) ⟨b, by simp [setOfList], rfl⟩
    · intro h t ht
      obtain ⟨v, hv, hvt⟩ := ht
      subst hvt
      rw [show v = b from by simpa [setOfList] using hv]
      exact h
  have hsetabc : setOfList [b, a, c] = setOfList [a, b, c] := by
    refine Set.ext fun q => ?_
    simp only [setOfList, Set.mem_setOf_eq]
    constructor
    · intro h
      rcases List.mem_cons.mp h with h1 | h
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h1)))
      rcases List.mem_cons.mp h with h1 | h
      · exact List.mem_cons.mpr (Or.inl h1)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
    · intro h
      rcases List.mem_cons.mp h with h1 | h
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h1)))
      rcases List.mem_cons.mp h with h1 | h
      · exact List.mem_cons.mpr (Or.inl h1)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
  have hsetab : setOfList [b, a] = setOfList [a, b] := by
    refine Set.ext fun q => ?_
    simp only [setOfList, Set.mem_setOf_eq]
    constructor
    · intro h
      rcases List.mem_cons.mp h with h1 | h
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h1)))
      rcases List.mem_cons.mp h with h1 | h
      · exact List.mem_cons.mpr (Or.inl h1)
      · exact absurd h (by simp)
    · intro h
      rcases List.mem_cons.mp h with h1 | h
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h1)))
      rcases List.mem_cons.mp h with h1 | h
      · exact List.mem_cons.mpr (Or.inl h1)
      · exact absurd h (by simp)
  refine ⟨⟨by rfl, ?_⟩, ?_⟩
  · intro vl hv
    obtain ⟨zl, hzl⟩ := hv.1
    have htake : vl = [b, a, c].take vl.length := by
      rw [hzl, p25_take_cancel vl.length (Nat.le_refl _), List.take_length]
    rcases zl with _ | ⟨y, t⟩
    · have hv0 : vl = [b, a, c] := by
        rw [List.append_nil] at hzl
        exact hzl.symm
      subst hv0
      refine ⟨h3.1, ?_, ?_⟩
      · rw [hsetabc]; exact h3.2.1
      · have he : voronoiList V [b, a, c] = voronoiList V [a, b, c] := by
          show voronoiSet V (setOfList [b, a, c]) = voronoiSet V (setOfList [a, b, c])
          rw [hsetabc]
        rw [he]
        exact h3.2.2
    · rcases t with _ | u
      · have hv2 : vl.length = 2 := by
          have h := congrArg List.length hzl
          simp only [List.length_append, List.length_cons, List.length_nil] at h
          omega
        have hveq : vl = [b, a] := by
          rw [hv2] at htake
          simpa using htake
        subst hveq
        refine ⟨h2.1, ?_, ?_⟩
        · rw [hsetab]; exact h2.2.1
        · have he : voronoiList V [b, a] = voronoiList V [a, b] := by
            show voronoiSet V (setOfList [b, a]) = voronoiSet V (setOfList [a, b])
            rw [hsetab]
          rw [he]
          exact h2.2.2
      · have hv1 : vl.length = 1 := by
          have h := congrArg List.length hzl
          simp only [List.length_append, List.length_cons, List.length_nil] at h
          omega
        have hveq : vl = [b] := by
          rw [hv1] at htake
          simpa using htake
        subst hveq
        refine ⟨by simp, ?_, ?_⟩
        · intro q hq
          have hqb : q = b := by simpa [setOfList] using hq
          refine h3.2.1 ?_
          simp only [setOfList, List.mem_cons]
          exact Or.inr (Or.inl hqb)
        · rw [hvb, AFF_DIM_VORONOI_CLOSED V b hp]
          simp
  · show radV (setOfList [b, a, c]) < Real.sqrt 2
    rwa [hsetabc]

/-- HOL `S_LEAF_SYM`.  Proof: swapping the stem endpoints preserves `leaf`
(`p25_leaf_swap`, everything reads off the point set) and the `ccKe = 4`
disjunction is symmetric. -/
theorem S_LEAF_SYM (V : Set V3) (u0 u1 : V3) (hp : Packing V) (hs : saturated V) :
    s_leaf V [u1, u0] = s_leaf V [u0, u1] := by
  have h0 : elV [u1, u0] 0 = u1 := rfl
  have h1 : elV [u1, u0] 1 = u0 := rfl
  have h2 : elV [u0, u1] 0 = u0 := rfl
  have h3 : elV [u0, u1] 1 = u1 := rfl
  ext u
  show (leaf V [elV [u1, u0] 0, elV [u1, u0] 1, u] ∧
      (ccKe V [elV [u1, u0] 0, elV [u1, u0] 1, u] = 4 ∨
        ccKe V [elV [u1, u0] 1, elV [u1, u0] 0, u] = 4)) ↔
    (leaf V [elV [u0, u1] 0, elV [u0, u1] 1, u] ∧
      (ccKe V [elV [u0, u1] 0, elV [u0, u1] 1, u] = 4 ∨
        ccKe V [elV [u0, u1] 1, elV [u0, u1] 0, u] = 4))
  rw [h0, h1, h2, h3]
  constructor
  · rintro ⟨h, hc⟩
    refine ⟨p25_leaf_swap V hp u1 u0 u h, ?_⟩
    rcases hc with hc | hc
    · exact Or.inr hc
    · exact Or.inl hc
  · rintro ⟨h, hc⟩
    refine ⟨p25_leaf_swap V hp u0 u1 u h, ?_⟩
    rcases hc with hc | hc
    · exact Or.inr hc
    · exact Or.inl hc

/-- HOL `S_LEAF_TRUNCATE`. -/
theorem S_LEAF_TRUNCATE (V : Set V3) (ul : List V3) :
    s_leaf V ul = s_leaf V [elV ul 0, elV ul 1] := by
  simp [s_leaf, elV]

/-- HOL `MCELL_AVOID_LEAVES`.  Proof (HOL OXLZLEZ3.hl:1081): otherwise `X`
is covered by the finitely many leaf planes `aff_ge {u0,u1} {u}` (`s_leaf`
is finite by `S_LEAF_FINITE`, and each is null by `NULLSET_AFF_2_1`), so
`X` itself is null — contradiction. -/
theorem MCELL_AVOID_LEAVES (V : Set V3) (ul : List V3) (X : Set V3) (hp : Packing V)
    (hs : saturated V) (hn : ¬ nullSet X) (hm : mcellSet V X) :
    ∃ v, v ∈ X ∧ ∀ u, u ∈ s_leaf V ul → ¬ v ∈ affGe {elV ul 0, elV ul 1} {u} := by
  by_contra hcon
  push_neg at hcon
  have hsub : X ⊆ ⋃ u ∈ (s_leaf V ul), affGe {elV ul 0, elV ul 1} {u} := by
    intro v hv
    obtain ⟨u, hu, hvu⟩ := hcon v hv
    exact Set.mem_biUnion hu hvu
  have hsfin := S_LEAF_FINITE V ul hp hs
  have hnull : volume (⋃ u ∈ (s_leaf V ul), affGe {elV ul 0, elV ul 1} {u}) = 0 :=
    (measure_biUnion_null_iff hsfin.countable).mpr
      (fun u _ => NULLSET_AFF_2_1 (elV ul 0) (elV ul 1) u)
  exact hn (measure_mono_null hsub hnull)

/-- HOL `MCELL_WEDGE_UNIQUE`: a non-null cell with the stem edge sits in at
most one leaf wedge. -/
theorem MCELL_WEDGE_UNIQUE (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (X : Set V3) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0)
    (hr : leaf_rank V ul w0 n f) (hm : mcellSet V X) (hn : ¬ nullSet X)
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X) :
    ∀ i j, i < n → j < n →
      X ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)) →
      X ⊆ wedgeGe (elV ul 0) (elV ul 1) (f j) (f (j + 1)) → i = j := by
  sorry

/-- HOL `LEAF_RANK_PERIODIC`. -/
theorem LEAF_RANK_PERIODIC (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hr : leaf_rank V ul w0 n f) : periodic f n := hr.2.1

/-- HOL `LEAF_RANK_AZIM_INJ`.  Proof: `azim u0 u1 (f i) (f j) = 0` says the
two leaves share an azimuthal ray, which by `AZIM_ZERO_SHIFT` makes their
`w0`-azimuths equal — impossible under the strict `w0`-ordering unless
`i ≡ j (mod n)`; conversely `f i = f j` when the residues agree. -/
theorem LEAF_RANK_AZIM_INJ (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i j : ℕ) (hs : saturated V) (hp : Packing V) (hn : n ≠ 0)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hr : leaf_rank V ul w0 n f) :
    (azim (elV ul 0) (elV ul 1) (f i) (f j) = 0 ↔ i % n = j % n) := by
  have hper : periodic f n := LEAF_RANK_PERIODIC V ul w0 n f hr
  have hcol : ∀ k : ℕ, ¬ Collinear3 (elV ul 0) (elV ul 1) (f k) := fun k =>
    LEAF_RANK_COLLINEAR V ul w0 n f k hp hs hr
  constructor
  · intro h0
    by_contra hne
    have hlt1 : i % n < n := Nat.mod_lt i (by omega)
    have hlt2 : j % n < n := Nat.mod_lt j (by omega)
    have hfi : f (i % n) = f i := p25_f_mod hper i
    have hfj : f (j % n) = f j := p25_f_mod hper j
    rcases lt_trichotomy (i % n) (j % n) with hlt | heq | hgt
    · have hord := hr.2.2 (i % n) (j % n) hlt1 hlt2 hlt
      rw [hfi, hfj] at hord
      have hz : azim (elV ul 0) (elV ul 1) w0 (f i) = azim (elV ul 0) (elV ul 1) w0 (f j) :=
        ((azim_eq_azim_iff hnc (hcol i) (hcol j)).trans
          (azim_eq_zero_iff_alt (hcol i) (hcol j)).symm).mpr h0
      linarith
    · exact hne heq
    · have hord := hr.2.2 (j % n) (i % n) hlt2 hlt1 hgt
      rw [hfj, hfi] at hord
      have hz : azim (elV ul 0) (elV ul 1) w0 (f j) = azim (elV ul 0) (elV ul 1) w0 (f i) :=
        ((azim_eq_azim_iff hnc (hcol j) (hcol i)).trans
          (azim_eq_zero_iff (hcol i) (hcol j)).symm).mpr h0
      linarith
  · intro hm
    rw [PERIODIC_EQ_IMAGE hn hper hm, azim_self]

/-- HOL `LEAF_RANK_AZIM_NZ`. -/
theorem LEAF_RANK_AZIM_NZ (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hs : saturated V) (hp : Packing V) (hr : leaf_rank V ul w0 n f)
    (hn : 1 < n) (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    ¬ (azim (elV ul 0) (elV ul 1) (f i) (f (i + 1)) = 0) := by
  rw [LEAF_RANK_AZIM_INJ V ul w0 n f i (i + 1) hs hp (by omega) hnc hr]
  exact MOD_INJ1_ALT_p25 (by omega) (by omega) (by norm_num) i

/-- HOL `MCELL_IN_WEDGE`. -/
theorem MCELL_IN_WEDGE (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (X : Set V3) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0)
    (hr : leaf_rank V ul w0 n f) (hm : mcellSet V X) (hnn : ¬ nullSet X)
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X) :
    ∃ i, i < n ∧ X ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)) := by
  sorry

/-- HOL `LEAF_RANK_REUHADY`. -/
theorem LEAF_RANK_REUHADY (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hr : leaf_rank V ul w0 n f) :
    azim_mcell V f (elV ul 0) (elV ul 1) i =
      azim (elV ul 0) (elV ul 1) (f i) (f (i + 1)) := by
  sorry

/-- HOL `LEAF_RANK_BIJ`. -/
theorem LEAF_RANK_BIJ (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n) (h0 : elV ul 0 ∈ V) (h1 : elV ul 1 ∈ V)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hr : leaf_rank V ul w0 n f) :
    Set.BijOn Prod.snd
      {p : ℕ × Set V3 | p.1 < n ∧ mcellSet V p.2 ∧
        {elV ul 0, elV ul 1} ∈ edgeX V p.2 ∧
        p.2 ⊆ wedgeGe (elV ul 0) (elV ul 1) (f p.1) (f (p.1 + 1))}
      {X | mcellSet V X ∧ {elV ul 0, elV ul 1} ∈ edgeX V X} := by
  sorry

/-- HOL `LEAF_RANK_GRUTOTI` (consumes GRUTOTI via `REUHADY`; the sum of the
wedge azim-mcells around the stem is `2*pi`). -/
theorem LEAF_RANK_GRUTOTI (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n) (h0 : elV ul 0 ∈ V) (h1 : elV ul 1 ∈ V)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hr : leaf_rank V ul w0 n f)
    (hhl : hl [elV ul 0, elV ul 1] < Real.sqrt 2) :
    ∑ i ∈ Finset.Icc 0 (n - 1), azim_mcell V f (elV ul 0) (elV ul 1) i =
      2 * Real.pi := by
  sorry

/-- HOL `LEAF_RANK_GG_SUM`: the per-wedge gg sums telescope to the full
edge sum over all cells carrying the stem edge. -/
theorem LEAF_RANK_GG_SUM (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n) (h0 : elV ul 0 ∈ V) (h1 : elV ul 1 ∈ V)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hr : leaf_rank V ul w0 n f) :
    ∑ i ∈ Finset.Icc 0 (n - 1), gg_mcell V f (elV ul 0) (elV ul 1) i =
      setSum {X | mcellSet V X ∧ {elV ul 0, elV ul 1} ∈ edgeX V X} fun X =>
        gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {elV ul 0, elV ul 1} X := by
  sorry

/-- HOL `MCELL2_DIHX_POS`. -/
theorem MCELL2_DIHX_POS (V : Set V3) (X : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X) :
    0 < dihX V X (elV ul 0, elV ul 1) := by
  sorry

/-- Helper: `truncateSimplex j ul` is the `j+1`-st prefix of `ul` whenever
that prefix exists (unfolding the `Classical.epsilon`). -/
private theorem p25_truncate_take (ul : List V3) (j : ℕ) (hj : j + 1 ≤ ul.length) :
    truncateSimplex j ul = ul.take (j + 1) := by
  have hwit : ∃ vl : List V3, vl.length = j + 1 ∧ initialSublist vl ul :=
    ⟨ul.take (j + 1), by rw [List.length_take]; omega,
      ⟨ul.drop (j + 1), (List.take_append_drop (j + 1) ul).symm⟩⟩
  set eps := Classical.epsilon
    fun vl : List V3 => vl.length = j + 1 ∧ initialSublist vl ul with he
  obtain ⟨htl, w, hzl⟩ := Classical.epsilon_spec hwit
  rw [← he] at htl hzl
  have hkey : ul.take eps.length = eps := by
    rw [hzl, p25_take_cancel _ (Nat.le_refl _), List.take_length]
  show eps = ul.take (j + 1)
  rw [← hkey, htl]

/-- Helper: the convex hull of three points is a null set (it lives in a
proper affine subspace). -/
private theorem p25_null_conv3 (a b c : V3) :
    nullSet (convexHull ℝ ({a, b, c} : Set V3)) := by
  refine measure_mono_null (convexHull_subset_affineSpan (s := ({a, b, c} : Set V3))) ?_
  exact Measure.addHaar_affineSubspace volume (affineSpan ℝ ({a, b, c} : Set V3))
    (p25_affineSpan_three_ne_top a b c)

/-- Helper: a 4-element set of cardinality at most 3 is covered by one of
its 3-element subsets. -/
private theorem p25_set4_dedup {α : Type*} {a b c d : α}
    (h : Set.ncard ({a, b, c, d} : Set α) ≠ 4) :
    ({a, b, c, d} : Set α) ⊆ ({a, c, d} : Set α) ∨
      ({a, b, c, d} : Set α) ⊆ ({a, b, d} : Set α) ∨
      ({a, b, c, d} : Set α) ⊆ ({a, b, c} : Set α) ∨
      ({a, b, c, d} : Set α) ⊆ ({b, c, d} : Set α) := by
  have hle3 : Set.ncard ({a, b, c, d} : Set α) ≤ 3 := by
    have e1 := Set.ncard_insert_le a ({b, c, d} : Set α)
    have e2 := Set.ncard_insert_le b ({c, d} : Set α)
    have e3 := Set.ncard_insert_le c ({d} : Set α)
    have e4 : Set.ncard ({d} : Set α) = 1 := Set.ncard_singleton d
    omega
  have hdup : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by
    by_contra hall
    push_neg at hall
    have h4 : Set.ncard ({a, b, c, d} : Set α) = 4 := by
      rw [Set.ncard_insert_of_notMem (show a ∉ ({b, c, d} : Set α) from by
        simp [hall.1, hall.2.1, hall.2.2.1]),
        Set.ncard_insert_of_notMem (show b ∉ ({c, d} : Set α) from by
          simp [hall.2.2.2.1, hall.2.2.2.2.1]),
        Set.ncard_insert_of_notMem (show c ∉ ({d} : Set α) from by
          simp [hall.2.2.2.2.2]),
        Set.ncard_singleton]
    omega
  rcases hdup with rfl | rfl | rfl | rfl | rfl | rfl
  · refine Or.inl fun q hq => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    tauto
  · refine Or.inr (Or.inl fun q hq => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    tauto
  · refine Or.inr (Or.inr (Or.inl fun q hq => ?_))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    tauto
  · refine Or.inr (Or.inl fun q hq => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    tauto
  · refine Or.inr (Or.inr (Or.inl fun q hq => ?_))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    tauto
  · refine Or.inr (Or.inr (Or.inl fun q hq => ?_))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    tauto

/-- HOL `MCELL3_CONVEX_HULL`. -/
theorem MCELL3_CONVEX_HULL (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul)
    (hn : ¬ nullSet (mcell3 V ul)) :
    mcell3 V ul =
      convexHull ℝ ({elV ul 0, elV ul 1, elV ul 2, mxi V ul} : Set V3) := by
  have hlen : ul.length = 4 := hb.1
  rcases ul with _ | ⟨u0, _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, t⟩⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · have ht : t = [] := by
      cases t with
      | nil => rfl
      | cons a tl => simp at hlen
    subst ht
    have htr : truncateSimplex 2 [u0, u1, u2, u3] =
        [elV [u0, u1, u2, u3] 0, elV [u0, u1, u2, u3] 1, elV [u0, u1, u2, u3] 2] := by
      rw [p25_truncate_take _ 2 (by simp)]
      rfl
    by_cases hlt : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl [u0, u1, u2, u3]
    · have heq : mcell3 V [u0, u1, u2, u3] =
          convexHull ℝ (setOfList (truncateSimplex 2 [u0, u1, u2, u3]) ∪
            {mxi V [u0, u1, u2, u3]}) := by
        unfold mcell3
        rw [if_pos hlt]
      rw [heq, htr]
      congr 1
      ext q
      simp only [Set.mem_union, Set.mem_singleton_iff, setOfList, Set.mem_setOf_eq,
        List.mem_cons, Set.mem_insert_iff]
      tauto
    · have heq : mcell3 V [u0, u1, u2, u3] = ∅ := by
        unfold mcell3
        rw [if_neg hlt]
      rw [heq] at hn
      exact absurd measure_empty hn

/-- HOL `MCELL3_EXTREME_CARD`.  Proof: by `MCELL3_CONVEX_HULL` the cell is
the hull of the four points; a repeated point would collapse the set onto a
3-element subset, whose hull is null (`p25_null_conv3`). -/
theorem MCELL3_EXTREME_CARD (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul)
    (hn : ¬ nullSet (mcell3 V ul)) :
    Set.ncard ({elV ul 0, elV ul 1, elV ul 2, mxi V ul} : Set V3) = 4 := by
  have hcv := MCELL3_CONVEX_HULL V ul hp hs hb hn
  by_contra hcon
  refine hn ?_
  rw [hcv]
  rcases p25_set4_dedup hcon with hsub | hsub | hsub | hsub
  · exact measure_mono_null (convexHull_mono hsub) (p25_null_conv3 _ _ _)
  · exact measure_mono_null (convexHull_mono hsub) (p25_null_conv3 _ _ _)
  · exact measure_mono_null (convexHull_mono hsub) (p25_null_conv3 _ _ _)
  · exact measure_mono_null (convexHull_mono hsub) (p25_null_conv3 _ _ _)

/-- HOL `MCELL3_DIHX`. -/
theorem MCELL3_DIHX (V : Set V3) (X : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell3 V ul)
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X) (hn : ¬ nullSet X) :
    dihX V X (elV ul 0, elV ul 1) =
      dihV (elV ul 0) (elV ul 1) (elV ul 2) (mxi V ul) := by
  sorry

/-- HOL `MCELL3_DIHX_POS`. -/
theorem MCELL3_DIHX_POS (V : Set V3) (X : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell3 V ul)
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X) :
    0 < dihX V X (elV ul 0, elV ul 1) := by
  sorry

/-- HOL `MCELL3_DOMAIN`. -/
theorem MCELL3_DOMAIN (V : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hn : ¬ nullSet (mcell3 V ul)) :
    ¬ Collinear3 (elV ul 0) (elV ul 1) (elV ul 2) ∧
      2 ≤ dist (elV ul 1) (elV ul 2) ∧ 2 ≤ dist (elV ul 0) (elV ul 2) ∧
      2 ≤ dist (elV ul 0) (elV ul 1) ∧
      dist (elV ul 1) (elV ul 2) < 2 * Real.sqrt 2 ∧
      dist (elV ul 0) (elV ul 2) < 2 * Real.sqrt 2 ∧
      dist (elV ul 0) (elV ul 1) < 2 * Real.sqrt 2 ∧
      eta_y (dist (elV ul 0) (elV ul 1)) (dist (elV ul 0) (elV ul 2))
          (dist (elV ul 1) (elV ul 2)) < Real.sqrt 2 := by
  sorry

/-- HOL `TSKAJXY_3` (the 3-cell case of the TSKAJXY bank; consumes
`pack_nonlinear_non_ox3q1h`). -/
theorem TSKAJXY_3 (V : Set V3) (X : Set V3) (ul : List V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell3 V ul) (hn : ¬ nullSet X) :
    gammaX V X lmfun ≥ 0 := by
  sorry

/-- HOL `MCELL4_LEAF2`.
2026-10-12 转真（零新债）：HOL leaf_cell.hl:1881 原路线照搬——`hl ul < sqrt 2`
支取 `barV V 2` 面（`TRUNCATE_SIMPLEX_BARV` PA5:1381 + `BARV3_TRUNC2`
PA18:1692 换形）与 `hl` 单调（`HL_DECREASE` PA7:1305，已在库全证）；
空支经 `mcell4 = ∅` 与 `hn` 矛盾。 -/
theorem MCELL4_LEAF2 (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)) :
    leaf V [elV ul 0, elV ul 1, elV ul 2] := by
  by_cases hlt : hl ul < Real.sqrt 2
  · refine ⟨?_, ?_⟩
    · have hbar : barV V 2 (truncateSimplex 2 ul) :=
        TRUNCATE_SIMPLEX_BARV V 2 3 ul hb (by omega)
      rw [BARV3_TRUNC2 hb] at hbar
      exact hbar
    · have hdec := HL_DECREASE V ul 3 2 hp hb (by omega)
      rw [BARV3_TRUNC2 hb] at hdec
      have hlist : [elV ul 0, elV ul 1, elV ul 2]
          = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0] := rfl
      rw [hlist]
      linarith
  · exfalso
    have heq : mcell4 V ul = ∅ := by unfold mcell4; rw [if_neg hlt]
    rw [heq] at hn
    exact absurd measure_empty hn

/-- HOL `MCELL4_CONVEX_HULL`.  Proof: a null `mcell4` is the empty branch of
its `if`, so the `hl ul < sqrt 2` branch must hold and the cell is the hull
of the (reordered) point set (`BARV3_SET_OF_LIST4`). -/
theorem MCELL4_CONVEX_HULL (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)) :
    mcell4 V ul = convexHull ℝ ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3) := by
  by_cases hlt : hl ul < Real.sqrt 2
  · have heq : mcell4 V ul = convexHull ℝ (setOfList ul) := by
      unfold mcell4
      rw [if_pos hlt]
    rw [heq, BARV3_SET_OF_LIST4 V ul hp hb]
  · have heq : mcell4 V ul = ∅ := by
      unfold mcell4
      rw [if_neg hlt]
    rw [heq] at hn
    exact absurd measure_empty hn

/-- HOL `MCELL4_CARD4`.  Proof: by `MCELL4_CONVEX_HULL` the cell is the hull
of the four points; a repeated point would collapse the set onto one of its
3-element subsets, whose hull is null (`p25_null_conv3`). -/
theorem MCELL4_CARD4 (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)) :
    Set.ncard ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3) = 4 := by
  by_contra hcon
  have hcv := MCELL4_CONVEX_HULL V ul hp hs hb hn
  refine hn ?_
  rw [hcv]
  rcases p25_set4_dedup hcon with hsub | hsub | hsub | hsub
  · exact measure_mono_null (convexHull_mono hsub) (p25_null_conv3 _ _ _)
  · exact measure_mono_null (convexHull_mono hsub) (p25_null_conv3 _ _ _)
  · exact measure_mono_null (convexHull_mono hsub) (p25_null_conv3 _ _ _)
  · exact measure_mono_null (convexHull_mono hsub) (p25_null_conv3 _ _ _)

/-- HOL `MCELL4_LEAF3`.
2026-10-12 转真（装配级）：对换置换 `Equiv.swap 2 3` 的显式装配——
`YIFVQDV_1`（PA7:1936，具名桩）给置换后 `barV V 3`，`RVFXZBU_p14`（PA14，i=4 支
已证）给 `mcell4` 不变性，套 `MCELL4_LEAF2` 后经四点表 `[EL 0, EL 1, EL 3,
EL 2] = leftActionList (swap 2 3) ul` 换回。债走账本：闭包含 YIFVQDV_1 的
上游桩债（PA7 具名桩，非本波引入）。 -/
theorem MCELL4_LEAF3 (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)) :
    leaf V [elV ul 0, elV ul 1, elV ul 3] := by
  by_cases hlt : hl ul < Real.sqrt 2
  · have h4 : ul.length = 4 := hb.1
    have hsw : ∀ i : ℕ, Equiv.swap (2:ℕ) 3 i
        = (if i = 2 then 3 else if i = 3 then 2 else i) := by
      intro i
      by_cases h2 : i = 2
      · subst h2; simp
      · by_cases h3 : i = 3
        · subst h3; simp
        · rw [if_neg h2, if_neg h3]
          exact Equiv.swap_apply_of_ne_of_ne h2 h3
    have hs0 : (Equiv.swap (2:ℕ) 3).symm 0 = 0 := by
      rw [Equiv.symm_apply_eq]; simp [hsw]
    have hs1 : (Equiv.swap (2:ℕ) 3).symm 1 = 1 := by
      rw [Equiv.symm_apply_eq]; simp [hsw]
    have hs2 : (Equiv.swap (2:ℕ) 3).symm 2 = 3 := by
      rw [Equiv.symm_apply_eq]; simp [hsw]
    have hs3 : (Equiv.swap (2:ℕ) 3).symm 3 = 2 := by
      rw [Equiv.symm_apply_eq]; simp [hsw]
    have hwl : leftActionList (Equiv.swap (2:ℕ) 3) ul
        = [elV ul 0, elV ul 1, elV ul 3, elV ul 2] := by
      unfold leftActionList
      rw [h4, show List.range 4 = [0, 1, 2, 3] from by decide]
      show [ul.getD ((Equiv.swap (2:ℕ) 3).symm 0) default,
            ul.getD ((Equiv.swap (2:ℕ) 3).symm 1) default,
            ul.getD ((Equiv.swap (2:ℕ) 3).symm 2) default,
            ul.getD ((Equiv.swap (2:ℕ) 3).symm 3) default]
          = [elV ul 0, elV ul 1, elV ul 3, elV ul 2]
      rw [hs0, hs1, hs2, hs3]
      rfl
    have hperm : permutes (Equiv.swap (2:ℕ) 3) (Set.Icc 0 3) := by
      intro x
      simp only [Set.mem_Icc]
      have hx3 : Equiv.swap (2:ℕ) 3 x ≤ 3 ↔ x ≤ 3 := by
        rw [hsw x]
        split
        · omega
        · split
          · omega
          · omega
      constructor
      · intro hc; exact ⟨by omega, hx3.mpr hc.2⟩
      · intro hc; exact ⟨by omega, hx3.mp hc.2⟩
    have hfix : ∀ j, 4 ≤ j → Equiv.swap (2:ℕ) 3 j = j := by
      intro j hj
      rw [hsw j]
      split
      · omega
      · split
        · omega
        · rfl
    have hbP : barV V 3 (leftActionList (Equiv.swap (2:ℕ) 3) ul) :=
      YIFVQDV_1 V ul 3 (Equiv.swap (2:ℕ) 3) hp hb hlt hperm
    have hmc : mcell 4 V (leftActionList (Equiv.swap (2:ℕ) 3) ul)
        = mcell 4 V ul := RVFXZBU_p14 (i := 4) (by simp) hs hp hb hperm hfix
    have hn4 : ¬ nullSet (mcell4 V (leftActionList (Equiv.swap (2:ℕ) 3) ul)) := by
      rw [show mcell4 V (leftActionList (Equiv.swap (2:ℕ) 3) ul)
            = mcell 4 V (leftActionList (Equiv.swap (2:ℕ) 3) ul) from rfl,
          hmc, show mcell 4 V ul = mcell4 V ul from rfl]
      exact hn
    have hleaf := MCELL4_LEAF2 V (leftActionList (Equiv.swap (2:ℕ) 3) ul) hp hs hbP hn4
    rw [hwl] at hleaf
    exact hleaf
  · exfalso
    have heq : mcell4 V ul = ∅ := by unfold mcell4; rw [if_neg hlt]
    rw [heq] at hn
    exact absurd measure_empty hn

/-- 私件（PA18 私件 `list4_eq` 的本文件同款显式 cases 拷贝，供 :2303 装配在
:2570 的 `p25_list4_eq` 之前取用；查重后无公开同件，命名错开）。 -/
private theorem p25m_list4_eq (ul : List V3) (h : ul.length = 4) :
    ul = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0, ul.getD 3 0] := by
  cases ul with
  | nil => simp at h
  | cons a t1 =>
    cases t1 with
    | nil => simp at h
    | cons b t2 =>
      cases t2 with
      | nil => simp at h
      | cons c t3 =>
        cases t3 with
        | nil => simp at h
        | cons d t4 =>
          cases t4 with
          | nil => rfl
          | cons _ _ => exact absurd h (by simp)

/-- 私件：四点集基数 4 排除前两点相等（`S_LEAF_CARD2` 的三集上界模式）。 -/
private theorem p25m_ncard4_ne {x y z w : V3}
    (h : Set.ncard ({x, y, z, w} : Set V3) = 4) : x ≠ y := by
  intro he
  rw [he] at h
  have hsub : ({y, y, z, w} : Set V3) ⊆ ({y, z, w} : Set V3) := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    tauto
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : Set.ncard ({y, z, w} : Set V3) ≤ 3 := by
    have e1 := Set.ncard_insert_le y ({z, w} : Set V3)
    have e2 := Set.ncard_insert_le z ({w} : Set V3)
    have e3 : Set.ncard ({w} : Set V3) = 1 := Set.ncard_singleton w
    omega
  omega

/-- 私件：四点集基数 4 给两两互异（`MCELL4_DOMAIN` 距离域与楔边证书共用）。 -/
private theorem p25m_card4_ne {a b c d : V3}
    (h : Set.ncard ({a, b, c, d} : Set V3) = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have peq : ∀ (p q r s : V3), ({p, q, r, s} : Set V3) = ({a, b, c, d} : Set V3) →
      Set.ncard ({p, q, r, s} : Set V3) = 4 := by
    intro p q r s he
    rw [he]
    exact h
  refine ⟨p25m_ncard4_ne (peq a b c d rfl), p25m_ncard4_ne (peq a c b d ?_),
    p25m_ncard4_ne (peq a d b c ?_), p25m_ncard4_ne (peq b c a d ?_),
    p25m_ncard4_ne (peq b d a c ?_), p25m_ncard4_ne (peq c d a b ?_)⟩
  repeat' ext q
  repeat' simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  all_goals tauto

/-- HOL `MCELL4_LEAF_S_LEAF`.
2026-10-13 转真（装配级，零新增记账行）：`u ∈ {EL 2, EL 3}` 先定型，然后按
PA18 冻结版 `CFFONNL`（leaf_cell.hl:2178-2514 真证；其内部经规则⑤白名单流动
`pa18_ccCell_swap`/`ZWVCBMN` 两笔已记账债）做二分装配——以 `X := mcell4 V ul`、
叶表 `ul := [EL 0 ul, EL 1 ul, u]` 实例化。PA18 冻结陈述的 `hne` 恰为结论之
否定，故：(a) `mcell4 = ccCell [EL 1 ul, EL 0 ul, u]` 成立时经 `AJRIPQN`
（PA17:929 真证）配 `CC_KE_34`/`ZASUVOR`/`cc_uh_exists` 把派单值钉到 4
（右析取支）；(b) 不成立时该不等式正是 CFFONNL 之 `hne`，反得等式而爆炸。
楔边证书 `stem ∈ edgeX` 由 `HDTFNFZ`+`LEPJBDJ`(k=4)+`MCELL4_CARD4` 内联
（`MCELL4_EDGE_EXPLICIT` 在本件之后，取其 VX 论证内联版）；`u ∈ ccA0` 走
`MCELL4_CONVEX_HULL`+`U2_IN_AFF_GT`（HOL Local_lemmas.DISJOINT_IMP_Z_IN_AFF_GT
的杠杆件）。 -/
theorem MCELL4_LEAF_S_LEAF (V : Set V3) (ul : List V3) (u : V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul))
    (hl' : leaf V [elV ul 0, elV ul 1, u]) (hu : u ∈ ({elV ul 2, elV ul 3} : Set V3)) :
    u ∈ s_leaf V [elV ul 0, elV ul 1] := by
  -- 楔边证书：VX 钉死为见证四点（MCELL4_EDGE_EXPLICIT 的 VX 论证内联）
  have hne' : mcell4 V ul ≠ ∅ := by
    intro h0
    apply hn
    rw [h0]
    exact measure_empty
  have h4 : ul.length = 4 := hb.1
  have hul4 := p25m_list4_eq ul h4
  have htr : setOfList (truncateSimplex 3 ul)
      = ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3) := by
    conv_lhs => rw [hul4]
    rw [TRUNCATE_SIMPLEX_EXPLICIT_3 (ul.getD 0 0) (ul.getD 1 0) (ul.getD 2 0)
      (ul.getD 3 0)]
    ext q
    simp only [setOfList, elV, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hVX : VX V (mcell4 V ul) = setOfList (truncateSimplex 3 ul) := by
    have h1 : VX V (mcell4 V ul) = V ∩ mcell4 V ul :=
      HDTFNFZ (v := elV ul 0) (k := 4) hs hp hb rfl hn
    rw [h1, show mcell4 V ul = mcell 4 V ul from rfl,
      LEPJBDJ V ul 4 hs hp hb (by omega) (by omega) hne']
  have hVX4 : ∀ z : V3, z ∈ VX V (mcell4 V ul) ↔
      z ∈ ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3) := by
    intro z
    rw [hVX, htr]
  have hdd := p25m_card4_ne (MCELL4_CARD4 V ul hp hs hb hn)
  -- CFFONNL 实例的非平凡前提
  obtain ⟨e0, e1, e2⟩ := EL_CC_UH (V := V) (ul := [elV ul 0, elV ul 1, u]) hp hs hl'
  have hedge : ({(ccUh V [elV ul 0, elV ul 1, u]).getD 0 0,
      (ccUh V [elV ul 0, elV ul 1, u]).getD 1 0} : Set V3) ∈ edgeX V (mcell4 V ul) := by
    rw [e0, e1]
    exact ⟨elV ul 0, elV ul 1, rfl, (hVX4 _).mpr (by simp), (hVX4 _).mpr (by simp), hdd.1⟩
  have h4m : mcell4 V ul = mcell 4 V ul := by simp [mcell]
  have hX : mcell4 V ul ∈ mcellSet V := ⟨4, ul, h4m, hb⟩
  have hA : mcell4 V ul ∩ ccA0 [elV ul 0, elV ul 1, u] ≠ ∅ := by
    refine Set.nonempty_iff_ne_empty.mp ⟨u, Set.mem_inter ?_ ?_⟩
    · rw [MCELL4_CONVEX_HULL V ul hp hs hb hn]
      refine subset_convexHull ℝ _ ?_
      rcases Set.mem_insert_iff.mp hu with hx | hx
      · exact Or.inr (Or.inr (Or.inl hx))
      · rw [Set.mem_singleton_iff] at hx
        exact Or.inr (Or.inr (Or.inr hx))
    · unfold ccA0
      have hU := U2_IN_AFF_GT (V := V) (ul := [elV ul 0, elV ul 1, u]) hp hs hl'
      rw [e0, e1, e2] at hU
      exact hU
  by_cases hEq : mcell4 V ul = ccCell V [elV ul 1, elV ul 0, u]
  · -- 等式情形：AJRIPQN 钉出派单值 4（右析取支）
    refine Set.mem_setOf_eq.mpr ⟨hl', Or.inr ?_⟩
    unfold ccCell at hEq
    obtain ⟨hij, -⟩ := AJRIPQN V ul (ccUh V [elV ul 1, elV ul 0, u]) 4
      (ccKe V [elV ul 1, elV ul 0, u]) hs hp hb
      ((Classical.choose_spec (cc_uh_exists V [elV ul 1, elV ul 0, u]) hp hs
        (ZASUVOR hp hs hl').1).1)
      (by simp)
      (by rcases CC_KE_34 V [elV ul 1, elV ul 0, u] with h | h <;> simp [h])
      (by
        intro hcon
        have hI : mcell 4 V ul ∩ mcell (ccKe V [elV ul 1, elV ul 0, u])
              V (ccUh V [elV ul 1, elV ul 0, u]) = mcell4 V ul := by
          rw [← h4m, ← hEq, Set.inter_self]
        rw [hI] at hcon
        exact hn hcon)
    exact hij.symm
  · -- 不等式情形：正是 PA18 冻结 CFFONNL 的 hne，反得等式而爆炸
    exfalso
    have hne : mcell4 V ul ≠ ccCell V [(ccUh V [elV ul 0, elV ul 1, u]).getD 1 0,
        (ccUh V [elV ul 0, elV ul 1, u]).getD 0 0,
        (ccUh V [elV ul 0, elV ul 1, u]).getD 2 0] := by
      rw [e1, e0, e2]
      exact hEq
    exact absurd
      (CFFONNL (V := V) (ul := [elV ul 0, elV ul 1, u]) (X := mcell4 V ul)
        hp hs hl' hX hedge hA hne)
      hne

/-- HOL `S_LEAF_CARD2`.
leaf-rank 波（2026-10-08）转真（装配级）：`{EL 2, EL 3}` 两点互异（`MCELL4_CARD4`
✅ 的 4 点互异性）且都是茎叶（`MCELL4_LEAF2/3/LEAF_S_LEAF`），故
`2 = ncard {EL 2, EL 3} ≤ ncard (s_leaf ...)`（`S_LEAF_FINITE` ✅）。
2026-10-13：MCELL4_LEAF_S_LEAF 已转真（见该件 docstring），本件成为完整真证、
零在库欠件。 -/
theorem S_LEAF_CARD2 (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)) :
    2 ≤ Set.ncard (s_leaf V [elV ul 0, elV ul 1]) := by
  have h4 := MCELL4_CARD4 V ul hp hs hb hn
  have h23 : (elV ul 2 : V3) ≠ elV ul 3 := by
    intro he
    rw [show ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3)
          = ({elV ul 0, elV ul 1, elV ul 2} : Set V3) from by
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [he]
      tauto] at h4
    have hle : Set.ncard ({elV ul 0, elV ul 1, elV ul 2} : Set V3) ≤ 3 := by
      have e1 := Set.ncard_insert_le (elV ul 0) ({elV ul 1, elV ul 2} : Set V3)
      have e2 := Set.ncard_insert_le (elV ul 1) ({elV ul 2} : Set V3)
      have e3 : Set.ncard ({elV ul 2} : Set V3) = 1 := Set.ncard_singleton _
      omega
    omega
  have hsub : ({elV ul 2, elV ul 3} : Set V3) ⊆ s_leaf V [elV ul 0, elV ul 1] := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx' | hx'
    · subst hx'
      exact MCELL4_LEAF_S_LEAF V ul (elV ul 2) hp hs hb hn (MCELL4_LEAF2 V ul hp hs hb hn)
        (by simp)
    · rw [Set.mem_singleton_iff] at hx'
      subst hx'
      exact MCELL4_LEAF_S_LEAF V ul (elV ul 3) hp hs hb hn (MCELL4_LEAF3 V ul hp hs hb hn)
        (by simp)
  refine le_trans ?_ (Set.ncard_le_ncard hsub (S_LEAF_FINITE V [elV ul 0, elV ul 1] hp hs))
  rw [Set.ncard_pair h23]

/-- HOL `LEAF_RANK_ONTO`: the leaf-rank parametrization hits both vertices
of the 4-cell.
leaf-rank 波（2026-10-08）转真（装配级）：4-cell 顶点是茎叶
（`MCELL4_LEAF2/3` + `MCELL4_LEAF_S_LEAF`），落进 `leaf_rank` 的满射像
（`hr.1`），再经周期性折回 `j % n < n`（`p25_f_mod`）。
2026-10-13：MCELL4_LEAF_S_LEAF 已转真，本件成为完整真证、零在库欠件。 -/
theorem LEAF_RANK_ONTO (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (u : V3) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hn : n ≠ 0)
    (hnn : ¬ nullSet (mcell4 V ul)) (hu : u ∈ ({elV ul 2, elV ul 3} : Set V3)) :
    ∃ i, i < n ∧ u = f i := by
  have hleaf : leaf V [elV ul 0, elV ul 1, u] := by
    rcases Set.mem_insert_iff.mp hu with hx | hx
    · subst hx
      exact MCELL4_LEAF2 V ul hp hs hb hnn
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact MCELL4_LEAF3 V ul hp hs hb hnn
  have hmem : u ∈ s_leaf V [elV ul 0, elV ul 1] :=
    MCELL4_LEAF_S_LEAF V ul u hp hs hb hnn hleaf hu
  rw [← hr.1] at hmem
  obtain ⟨j, -, rfl⟩ := hmem
  exact ⟨j % n, Nat.mod_lt j (by omega), (p25_f_mod (LEAF_RANK_PERIODIC _ _ _ _ _ hr) j).symm⟩

/-- HOL `S_LEAF_IN_WEDGE_GE`.
leaf-rank 波（2026-10-12）转真：azim 链算术。周期归一 `j := j % n`
（`PERIODIC_REDUCE_MOD` ✅）后分两案，都只吃移位恒等式（`AZIM_BASE_SHIFT_LE`
PA18:2766 两点法，`hnc` 供 w0 侧、`LEAF_RANK_COLLINEAR` ✅ 供叶侧）+
补角恒等式（`azim_compl`，Geom.AzimLemmas ✅，在 import 闭包内经
TopologyFan→Fan→AzimLemmas 可见，无需 `WEDGE_COMPLEMENT`）+ `hr.2.2`
严格环序实数算术：`j < n-1` 时楔内叶 `i' < j` / `j+1 < i'` 均与楔上界矛盾；
`j = n-1` 时 `f (j+1) = f 0`，其余叶落在开楔 `(f 0, f (n-1))` 内亦与
楔上界矛盾。本波 LEAF_IN_WEDGE_GE（:2039 ✅）装配到本件。 -/
theorem S_LEAF_IN_WEDGE_GE (V : Set V3) (ul : List V3) (u w0 : V3) (n : ℕ)
    (f : ℕ → V3) (j i' : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hl' : leaf V [elV ul 0, elV ul 1, u])
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hu : u = f i') (hi' : i' < n)
    (hw : u ∈ wedgeGe (elV ul 0) (elV ul 1) (f j) (f (j + 1))) :
    u = f j ∨ u = f (j + 1) := by
  obtain ⟨k, hk, hjk, hjk1⟩ := PERIODIC_REDUCE_MOD (by omega) hr.2.1 j
  rw [hjk, hjk1] at hw ⊢
  have hcol : ∀ m, ¬ Collinear3 (elV ul 0) (elV ul 1) (f m) :=
    fun m => LEAF_RANK_COLLINEAR V [elV ul 0, elV ul 1] w0 n f m hp hs hr
  have key : ∀ p q, p < q → q < n →
      azim (elV ul 0) (elV ul 1) (f p) (f q)
        = azim (elV ul 0) (elV ul 1) w0 (f q)
          - azim (elV ul 0) (elV ul 1) w0 (f p) := by
    intro p q hpq hqn
    have hchain : azim (elV ul 0) (elV ul 1) w0 (f p)
        < azim (elV ul 0) (elV ul 1) w0 (f q) := hr.2.2 p q (by omega) hqn hpq
    have h := AZIM_BASE_SHIFT_LE (elV ul 0) (elV ul 1) w0 (f p) (f p) (f q)
      hnc (hcol p) (hcol p) (hcol q) (le_refl _) hchain.le
    rw [azim_self] at h
    linarith
  have comp : ∀ p q, p < q → q < n →
      azim (elV ul 0) (elV ul 1) (f q) (f p)
        = 2 * Real.pi - (azim (elV ul 0) (elV ul 1) w0 (f q)
          - azim (elV ul 0) (elV ul 1) w0 (f p)) := by
    intro p q hpq hqn
    have hchain : azim (elV ul 0) (elV ul 1) w0 (f p)
        < azim (elV ul 0) (elV ul 1) w0 (f q) := hr.2.2 p q (by omega) hqn hpq
    have hpos : (0:ℝ) < azim (elV ul 0) (elV ul 1) (f p) (f q) := by
      rw [key p q hpq hqn]; linarith
    have hc := azim_compl (hcol p) (hcol q)
    rw [key p q hpq hqn,
      if_neg (by rw [← key p q hpq hqn]; exact ne_of_gt hpos)] at hc
    exact hc
  rcases Nat.lt_or_ge k (n - 1) with hklt | hkge
  · have hk1 : k + 1 < n := by omega
    rw [wedgeGe, Set.mem_setOf_eq] at hw
    rw [hu] at hw
    rcases Nat.lt_trichotomy i' k with hlt | heq | hgt
    · exfalso
      have hc1 := comp i' k hlt hk
      have hc2 := key k (k + 1) (Nat.lt_succ_self k) hk1
      have hw2 := hw.2
      rw [hc1, hc2] at hw2
      have hch : azim (elV ul 0) (elV ul 1) w0 (f k)
          < azim (elV ul 0) (elV ul 1) w0 (f (k + 1)) :=
        hr.2.2 k (k + 1) hk hk1 (Nat.lt_succ_self k)
      have h2p := azim_lt_two_pi (elV ul 0) (elV ul 1) w0 (f (k + 1))
      have h0 := azim_nonneg (elV ul 0) (elV ul 1) w0 (f i')
      linarith
    · exact Or.inl (by rw [hu, heq])
    · by_cases heq1 : i' = k + 1
      · exact Or.inr (by rw [hu, heq1])
      · exfalso
        have hgt2 : k + 1 < i' := by omega
        have hc1 := key k i' (by omega) hi'
        have hc2 := key k (k + 1) (Nat.lt_succ_self k) hk1
        have hw2 := hw.2
        rw [hc1, hc2] at hw2
        have hch : azim (elV ul 0) (elV ul 1) w0 (f (k + 1))
            < azim (elV ul 0) (elV ul 1) w0 (f i') :=
          hr.2.2 (k + 1) i' hk1 hi' hgt2
        linarith
  · have hk_eq : k = n - 1 := by omega
    have hfn0 : f (k + 1) = f 0 := by
      have h := hr.2.1 0
      rw [Nat.zero_add] at h
      have he : k + 1 = n := by omega
      rw [he]
      exact h
    rw [wedgeGe, Set.mem_setOf_eq] at hw
    rw [hu] at hw
    by_cases hi0 : i' = 0
    · exact Or.inr (by rw [hu, hi0, hfn0])
    · by_cases hin1 : i' = n - 1
      · exact Or.inl (by rw [hu, hin1, hk_eq])
      · exfalso
        have h01 : 0 < i' := by omega
        have hin1' : i' < n - 1 := by omega
        have hc1 := comp i' (n - 1) hin1' (by omega)
        have hc2 := comp 0 (n - 1) (by omega) (by omega)
        have hw2 := hw.2
        rw [hfn0, hk_eq] at hw2
        rw [hc1, hc2] at hw2
        have hch : azim (elV ul 0) (elV ul 1) w0 (f 0)
            < azim (elV ul 0) (elV ul 1) w0 (f i') :=
          hr.2.2 0 i' (by omega) hi' h01
        linarith

/-- HOL `LEAF_IN_WEDGE_GE`.
leaf-rank 波（2026-10-08）转真（装配级）：4-cell 顶点先被参数化命中
（`LEAF_RANK_ONTO`，本波已转真），再由 `S_LEAF_IN_WEDGE_GE` 的楔形边界二择
收尾。
2026-10-12：`S_LEAF_IN_WEDGE_GE` 已转真（azim 链算术，见该件 docstring），
本件成为完整真证、零在库欠件。 -/
theorem LEAF_IN_WEDGE_GE (V : Set V3) (ul : List V3) (u w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hl' : leaf V [elV ul 0, elV ul 1, u]) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul)) (hu : u ∈ ({elV ul 2, elV ul 3} : Set V3))
    (hw : u ∈ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    u = f i ∨ u = f (i + 1) := by
  obtain ⟨i', hi', rfl⟩ :=
    LEAF_RANK_ONTO V ul w0 n f u hp hs hb hr (by omega) hnn hu
  exact S_LEAF_IN_WEDGE_GE V ul (f i') w0 n f i i' hp hs hr hl' hnc hn rfl hi' hw

/-- HOL `MCELL4_FI_EL`.
2026-10-12 转真（装配级）：4-cell 的 `{EL 2, EL 3}` 就是其楔的两个端点叶——
`MCELL4_CONVEX_HULL`/`MCELL4_CARD4`（已证）给凸包成员与 `EL 2 ≠ EL 3`，
`MCELL4_LEAF2/LEAF3`（本波转真）+ `LEAF_IN_WEDGE_GE`（本波转真）给两点各为
`f i` 或 `f (i+1)` 的二择。 -/
theorem MCELL4_FI_EL (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    ({elV ul 2, elV ul 3} : Set V3) = {f i, f (i + 1)} := by
  have hcv := MCELL4_CONVEX_HULL V ul hp hs hb hnn
  have hne23 : (elV ul 2 : V3) ≠ elV ul 3 := by
    have hcard := MCELL4_CARD4 V ul hp hs hb hnn
    intro he
    have hle : Set.ncard ({elV ul 0, elV ul 1, elV ul 2} : Set V3) ≤ 3 := by
      have e1 := Set.ncard_insert_le (elV ul 0) ({elV ul 1, elV ul 2} : Set V3)
      have e2 := Set.ncard_insert_le (elV ul 1) ({elV ul 2} : Set V3)
      have e3 : Set.ncard ({elV ul 2} : Set V3) = 1 := Set.ncard_singleton _
      omega
    rw [show ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3)
          = ({elV ul 0, elV ul 1, elV ul 2} : Set V3) from by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [he]; tauto] at hcard
    omega
  have hmem : ∀ x ∈ ({elV ul 2, elV ul 3} : Set V3), x = f i ∨ x = f (i + 1) := by
    intro x hx
    have hxleaf : leaf V [elV ul 0, elV ul 1, x] := by
      rcases Set.mem_insert_iff.mp hx with hx' | hx'
      · subst hx'
        exact MCELL4_LEAF2 V ul hp hs hb hnn
      · rw [Set.mem_singleton_iff] at hx'
        subst hx'
        exact MCELL4_LEAF3 V ul hp hs hb hnn
    have hx4 : x ∈ ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3) := by
      rcases Set.mem_insert_iff.mp hx with hx' | hx'
      · subst hx'; simp
      · rw [Set.mem_singleton_iff] at hx'
        subst hx'; simp
    have hxin : x ∈ mcell4 V ul := by rw [hcv]; exact subset_convexHull ℝ _ hx4
    exact LEAF_IN_WEDGE_GE V ul x w0 n f i hp hs hr hxleaf hb hnc hn hnn hx (hw hxin)
  have h23cases : (elV ul 2 = f i ∧ elV ul 3 = f (i + 1)) ∨
      (elV ul 2 = f (i + 1) ∧ elV ul 3 = f i) := by
    rcases hmem _ (Set.mem_insert _ _) with h2 | h2
    · rcases hmem _ (Or.inr (Set.mem_singleton _)) with h3 | h3
      · rw [h2] at hne23
        rw [h3] at hne23
        exact absurd rfl hne23
      · exact Or.inl ⟨h2, h3⟩
    · rcases hmem _ (Or.inr (Set.mem_singleton _)) with h3 | h3
      · exact Or.inr ⟨h2, h3⟩
      · rw [h2] at hne23
        rw [h3] at hne23
        exact absurd rfl hne23
  rcases h23cases with ⟨e2, e3⟩ | ⟨e2, e3⟩
  · ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [e2, e3]
  · ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [e2, e3]; tauto

/-- HOL `MCELL4_FI`.
2026-10-12 转真（装配级）：`MCELL4_CONVEX_HULL` + `MCELL4_FI_EL`（本波转真）
的两点集替换。 -/
theorem MCELL4_FI (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    mcell4 V ul = convexHull ℝ ({elV ul 0, elV ul 1, f i, f (i + 1)} : Set V3) := by
  have hcv := MCELL4_CONVEX_HULL V ul hp hs hb hnn
  have hfe := MCELL4_FI_EL V ul w0 n f i hp hs hr hb hnc hn hnn hw
  have h4set : ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3)
      = ({elV ul 0, elV ul 1} : Set V3) ∪ ({elV ul 2, elV ul 3} : Set V3) := by
    ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto
  have h4set' : ({elV ul 0, elV ul 1, f i, f (i + 1)} : Set V3)
      = ({elV ul 0, elV ul 1} : Set V3) ∪ ({f i, f (i + 1)} : Set V3) := by
    ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto
  rw [hcv, h4set, hfe, ← h4set']

/-- Helper: a 4-point list equals its `getD`-entries (PA18 私件 `list4_eq`
的同款显式 cases 论证，本文件自备以免跨文件私件）。 -/
private theorem p25_list4_eq (ul : List V3) (h : ul.length = 4) :
    ul = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0, ul.getD 3 0] := by
  cases ul with
  | nil => simp at h
  | cons a t1 =>
    cases t1 with
    | nil => simp at h
    | cons b t2 =>
      cases t2 with
      | nil => simp at h
      | cons c t3 =>
        cases t3 with
        | nil => simp at h
        | cons d t4 =>
          cases t4 with
          | nil => rfl
          | cons _ _ => exact absurd h (by simp)

/-- HOL `MCELL4_BARV_FI`.
2026-10-12 转真（装配级）：由 `MCELL4_FI_EL`（本波转真）的两序两案——
`el 2 = f i` 时表即 `ul`（`p25_list4_eq`）零成本；`el 2 = f (i+1)` 时表是
`leftActionList (Equiv.swap 2 3) ul`（同 `MCELL4_LEAF3` 的 swap 套件），经
`YIFVQDV_1`（PA7 具名桩）+ `RVFXZBU_p14`（PA14，i=4 支已证）搬移。 -/
theorem MCELL4_BARV_FI (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    barV V 3 [elV ul 0, elV ul 1, f i, f (i + 1)] ∧
      mcell4 V ul = mcell4 V [elV ul 0, elV ul 1, f i, f (i + 1)] := by
  have h4 : ul.length = 4 := hb.1
  have hfe := MCELL4_FI_EL V ul w0 n f i hp hs hr hb hnc hn hnn hw
  have hne23 : (elV ul 2 : V3) ≠ elV ul 3 := by
    have hcard := MCELL4_CARD4 V ul hp hs hb hnn
    intro he
    have hle : Set.ncard ({elV ul 0, elV ul 1, elV ul 2} : Set V3) ≤ 3 := by
      have e1 := Set.ncard_insert_le (elV ul 0) ({elV ul 1, elV ul 2} : Set V3)
      have e2 := Set.ncard_insert_le (elV ul 1) ({elV ul 2} : Set V3)
      have e3 : Set.ncard ({elV ul 2} : Set V3) = 1 := Set.ncard_singleton _
      omega
    rw [show ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3)
          = ({elV ul 0, elV ul 1, elV ul 2} : Set V3) from by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [he]; tauto] at hcard
    omega
  have hcases : (elV ul 2 = f i ∧ elV ul 3 = f (i + 1)) ∨
      (elV ul 2 = f (i + 1) ∧ elV ul 3 = f i) := by
    have h2in : elV ul 2 ∈ ({f i, f (i + 1)} : Set V3) := by
      have h2m : elV ul 2 ∈ ({elV ul 2, elV ul 3} : Set V3) := Set.mem_insert _ _
      exact hfe ▸ h2m
    have h3in : elV ul 3 ∈ ({f i, f (i + 1)} : Set V3) := by
      have h3m : elV ul 3 ∈ ({elV ul 2, elV ul 3} : Set V3) :=
        Or.inr (Set.mem_singleton _)
      exact hfe ▸ h3m
    rcases Set.mem_insert_iff.mp h2in with h2 | h2
    · rcases Set.mem_insert_iff.mp h3in with h3 | h3
      · rw [h2] at hne23
        rw [h3] at hne23
        exact absurd rfl hne23
      · exact Or.inl ⟨h2, h3⟩
    · rw [Set.mem_singleton_iff] at h2
      rcases Set.mem_insert_iff.mp h3in with h3 | h3
      · exact Or.inr ⟨h2, h3⟩
      · rw [Set.mem_singleton_iff] at h3
        rw [h2] at hne23
        rw [h3] at hne23
        exact absurd rfl hne23
  have hsw : ∀ m : ℕ, Equiv.swap (2:ℕ) 3 m
      = (if m = 2 then 3 else if m = 3 then 2 else m) := by
    intro m
    by_cases h2 : m = 2
    · subst h2; simp
    · by_cases h3 : m = 3
      · subst h3; simp
      · rw [if_neg h2, if_neg h3]
        exact Equiv.swap_apply_of_ne_of_ne h2 h3
  have hs0 : (Equiv.swap (2:ℕ) 3).symm 0 = 0 := by
    rw [Equiv.symm_apply_eq]; simp [hsw]
  have hs1 : (Equiv.swap (2:ℕ) 3).symm 1 = 1 := by
    rw [Equiv.symm_apply_eq]; simp [hsw]
  have hs2 : (Equiv.swap (2:ℕ) 3).symm 2 = 3 := by
    rw [Equiv.symm_apply_eq]; simp [hsw]
  have hs3 : (Equiv.swap (2:ℕ) 3).symm 3 = 2 := by
    rw [Equiv.symm_apply_eq]; simp [hsw]
  have hwl : leftActionList (Equiv.swap (2:ℕ) 3) ul
      = [elV ul 0, elV ul 1, elV ul 3, elV ul 2] := by
    unfold leftActionList
    rw [h4, show List.range 4 = [0, 1, 2, 3] from by decide]
    show [ul.getD ((Equiv.swap (2:ℕ) 3).symm 0) default,
          ul.getD ((Equiv.swap (2:ℕ) 3).symm 1) default,
          ul.getD ((Equiv.swap (2:ℕ) 3).symm 2) default,
          ul.getD ((Equiv.swap (2:ℕ) 3).symm 3) default]
        = [elV ul 0, elV ul 1, elV ul 3, elV ul 2]
    rw [hs0, hs1, hs2, hs3]
    rfl
  have hperm : permutes (Equiv.swap (2:ℕ) 3) (Set.Icc 0 3) := by
    intro x
    simp only [Set.mem_Icc]
    have hx3 : Equiv.swap (2:ℕ) 3 x ≤ 3 ↔ x ≤ 3 := by
      rw [hsw x]
      split
      · omega
      · split
        · omega
        · omega
    constructor
    · intro hc; exact ⟨by omega, hx3.mpr hc.2⟩
    · intro hc; exact ⟨by omega, hx3.mp hc.2⟩
  have hfix : ∀ j, 4 ≤ j → Equiv.swap (2:ℕ) 3 j = j := by
    intro j hj
    rw [hsw j]
    split
    · omega
    · split
      · omega
      · rfl
  have hlt : hl ul < Real.sqrt 2 := by
    by_contra hcon
    have heq : mcell4 V ul = ∅ := by unfold mcell4; rw [if_neg hcon]
    rw [heq] at hnn
    exact absurd measure_empty hnn
  rcases hcases with ⟨e2, e3⟩ | ⟨e2, e3⟩
  · have hul : ul = [elV ul 0, elV ul 1, f i, f (i + 1)] := by
      conv_lhs => rw [p25_list4_eq ul h4]
      show [elV ul 0, elV ul 1, elV ul 2, elV ul 3]
          = [elV ul 0, elV ul 1, f i, f (i + 1)]
      rw [e2, e3]
    rw [← hul]
    exact ⟨hb, rfl⟩
  · have hwlB : [elV ul 0, elV ul 1, f i, f (i + 1)]
        = leftActionList (Equiv.swap (2:ℕ) 3) ul := by
      rw [hwl, e3, e2]
    rw [hwlB]
    refine ⟨YIFVQDV_1 V ul 3 (Equiv.swap (2:ℕ) 3) hp hb hlt hperm, ?_⟩
    rw [show mcell4 V ul = mcell 4 V ul from rfl,
        show mcell4 V (leftActionList (Equiv.swap (2:ℕ) 3) ul)
          = mcell 4 V (leftActionList (Equiv.swap (2:ℕ) 3) ul) from rfl,
        RVFXZBU_p14 (i := 4) (by simp) hs hp hb hperm hfix]

/-- HOL `MCELL4_AZIM_LT_PI`. -/
theorem MCELL4_AZIM_LT_PI (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    azim (elV ul 0) (elV ul 1) (f i) (f (i + 1)) < Real.pi := by
  sorry

/-- HOL `MCELL4_DIHX_AZIM`. -/
theorem MCELL4_DIHX_AZIM (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    dihX V (mcell4 V ul) (elV ul 0, elV ul 1) =
      azim (elV ul 0) (elV ul 1) (f i) (f (i + 1)) := by
  sorry

/-- HOL `LEAF_RANK_HAS_SIZE`.  Proof: the `n`-periodicity collapses the
surjective image `f '' univ` to `f '' {i | i < n}` (PERIODIC_IMAGE), and the
strict `azim`-increase makes `f` injective there (an equal-value pair would
force `azim w0 x < azim w0 x`), so `Set.ncard (f '' Iio n) = ncard (Iio n) =
n` (InjOn.ncard_image + ncard_Iio_nat).  The geometric antecedents of the HOL
proof (S_LEAF_FINITE, LEAF_RANK_AZIM_INJ) are not needed. -/
theorem LEAF_RANK_HAS_SIZE (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hn : n ≠ 0) (hp : Packing V) (hs : saturated V) (hr : leaf_rank V ul w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    HasSizeP25 (s_leaf V ul) n := by
  have hper : periodic f n := LEAF_RANK_PERIODIC V ul w0 n f hr
  have himg : f '' {i : ℕ | i < n} = s_leaf V ul := by
    rw [PERIODIC_IMAGE hn hper]
    exact hr.1
  refine ⟨?_, ?_⟩
  · rw [← himg]
    exact (Set.finite_Iio n).image f
  · have hinj : Set.InjOn f {i : ℕ | i < n} := by
      intro i hi j hj hij
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact absurd (hr.2.2 i j hi hj hlt) (by rw [← hij]; exact lt_irrefl _)
      · exact heq
      · exact absurd (hr.2.2 j i hj hi hgt) (by rw [hij]; exact lt_irrefl _)
    rw [← himg, Set.InjOn.ncard_image hinj]
    exact Set.ncard_Iio_nat n

/-- HOL `MCELL4_FULL_WEDGE`: the 4-cell is the unique cell in its wedge. -/
theorem MCELL4_FULL_WEDGE (V : Set V3) (X : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul)) (hm : mcellSet V X)
    (hX : X ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)))
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X)
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    X = mcell4 V ul := by
  sorry

/-- HOL `MCELL4_REPARAM`. -/
theorem MCELL4_REPARAM (V : Set V3) (ul vl : List V3) (hp : Packing V)
    (hs : saturated V) (hc : Set.ncard (setOfList ul) = 4)
    (hs' : setOfList ul = setOfList vl) (hl : vl.length = 4)
    (hnn : ¬ nullSet (mcell4 V ul)) (hb : barV V 3 ul) :
    mcell4 V ul = mcell4 V vl ∧ barV V 3 vl := by
  sorry

/-- HOL `MCELL4_GG`: for the unique wedge cell, `gg_mcell` collapses to the
single cell weight. -/
theorem MCELL4_GG (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hX : mcell4 V ul = mcell4 V ul)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    gg_mcell V f (elV ul 0) (elV ul 1) i =
      gammaX V (mcell4 V ul) lmfun * criticalWeight V (mcell4 V ul) +
        betaBumpV1 V {elV ul 0, elV ul 1} (mcell4 V ul) := by
  sorry

/-- HOL `LEAF_RANK_TRUNCATE`. -/
theorem LEAF_RANK_TRUNCATE (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3) :
    leaf_rank V ul w0 n f = leaf_rank V [elV ul 0, elV ul 1] w0 n f := by
  unfold leaf_rank
  rw [S_LEAF_TRUNCATE]
  congr 1

/-- HOL `LEAF_RANK_S_LEAF`. -/
theorem LEAF_RANK_S_LEAF (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hr : leaf_rank V ul w0 n f) : f i ∈ s_leaf V ul := by
  have h1 : f i ∈ f '' (univ : Set ℕ) := ⟨i, Set.mem_univ _, rfl⟩
  exact hr.1 ▸ h1

/-- HOL `CC_CELL_SUBSET_WEDGE`. -/
theorem CC_CELL_SUBSET_WEDGE (V : Set V3) (ul : List V3) (u0 u1 w0 : V3) (n : ℕ)
    (f : ℕ → V3) (j : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hn : 1 < n)
    (he : ({u0, u1} : Set V3) = {elV ul 0, elV ul 1})
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    ccCell V [u0, u1, f j] ⊆ wedgeGe (elV ul 0) (elV ul 1) (f j) (f (j + 1)) ∨
      ccCell V [u0, u1, f j] ⊆
        wedgeGe (elV ul 0) (elV ul 1) (f (j + (n - 1))) (f j) := by
  sorry

/-- HOL `WEDGE_UNIQUE_CC_CELL`: the two cc-cells never sit in the same
interior wedge. -/
theorem WEDGE_UNIQUE_CC_CELL (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i j : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hn : 1 < n)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    ¬ (ccCell V [elV ul 0, elV ul 1, f j] ⊆
          wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)) ∧
        ccCell V [elV ul 1, elV ul 0, f j] ⊆
          wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) := by
  sorry

/-- HOL `LEAF_RANK4_CHI_MSB`. -/
theorem LEAF_RANK4_CHI_MSB (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n) (hi : i < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    0 < chiMsb [elV ul 0, elV ul 1, f i] (f (i + 1)) := by
  sorry

/-- HOL `LEAF_RANK4_CHI_MSB_ALT`. -/
theorem LEAF_RANK4_CHI_MSB_ALT (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    0 < chiMsb [elV ul 0, elV ul 1, f i] (f (i + 1)) := by
  sorry

/-- HOL `CC_CELL_WEDGE_MATCH_UH`. -/
theorem CC_CELL_WEDGE_MATCH_UH (V : Set V3) (ul : List V3) (u0 u1 w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i j : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (he : ({u0, u1} : Set V3) = {elV ul 0, elV ul 1})
    (hw : ccCell V [u0, u1, f j] ⊆
      wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)))
    (hk : ccKe V [u0, u1, f j] = 4) :
    ({f j, (ccUh V [u0, u1, f j]).getD 3 0} : Set V3) = {f i, f (i + 1)} := by
  sorry

/-- HOL `K4_CC_WI_ALT`. -/
theorem K4_CC_WI_ALT (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hk : ccKe V [elV ul 0, elV ul 1, f i] = 4) :
    ccCell V [elV ul 0, elV ul 1, f i] ⊆
      wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)) := by
  sorry

/-- HOL `K4_CC_WIM`. -/
theorem K4_CC_WIM (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hk : ccKe V [elV ul 1, elV ul 0, f i] = 4) :
    ccCell V [elV ul 1, elV ul 0, f i] ⊆
      wedgeGe (elV ul 0) (elV ul 1) (f (i + (n - 1))) (f i) := by
  sorry

/-- HOL `K3_CC_WI_ALT`. -/
theorem K3_CC_WI_ALT (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hk : ccKe V [elV ul 0, elV ul 1, f i] = 3) :
    ccCell V [elV ul 0, elV ul 1, f i] ⊆
      wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)) := by
  sorry

/-- HOL `K3_CC_WIM_ALT`. -/
theorem K3_CC_WIM_ALT (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hk : ccKe V [elV ul 1, elV ul 0, f i] = 3) :
    ccCell V [elV ul 1, elV ul 0, f i] ⊆
      wedgeGe (elV ul 0) (elV ul 1) (f (i + (n - 1))) (f i) := by
  sorry

/-- HOL `NO_4CELL_IMP_K3`: a wedge with no 4-cell carries two 3-cells.
楔形 3-cell 面 2026-10-13 波转真（装配级）：HOL OXLZLEZ3.hl:3705 逐支移植——
`k = 4` 反证经 `K4_CC_WI_ALT`/`K4_CC_WIM`（胞入楔）+ `STEM_EDGEX`（茎边入胞
edgeX）+ `cc_uh`/`ccCell` 定义改写（`mcell 4 = mcell4`）撞 `hno4`；
`k = 3` 双胞入楔取 `K3_CC_WI_ALT`/`K3_CC_WIM_ALT`（b-侧指标经
`F_SUC_PRE` 周期回卷）；互异取 `FUEIMOV_3`（同 stem 同胞 ⟹ 表相等 ⟹
首两点相等 ⟹ 共线撞 `hnc`）。债面 = PA18 `K3/K4` 家族 + `STEM_EDGEX`/
`FUEIMOV_3`（leaf_cell.hl edge-rigidity kit，PA18 在案）。 -/
theorem NO_4CELL_IMP_K3 (V : Set V3) (W : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0)
    (hW : W = wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) (hn : 1 < n)
    (hno4 : ¬ ∃ vl, barV V 3 vl ∧ {elV ul 0, elV ul 1} ∈ edgeX V (mcell4 V vl) ∧
      mcell4 V vl ⊆ W) :
    ccKe V [elV ul 1, elV ul 0, f (i + 1)] = 3 ∧
      ccKe V [elV ul 0, elV ul 1, f i] = 3 ∧
      ccCell V [elV ul 0, elV ul 1, f i] ⊆ W ∧
      ccCell V [elV ul 1, elV ul 0, f (i + 1)] ⊆ W ∧
      ccCell V [elV ul 0, elV ul 1, f i] ≠
        ccCell V [elV ul 1, elV ul 0, f (i + 1)] := by
  have hleafA : ∀ j : ℕ, leaf V [elV ul 0, elV ul 1, f j] := by
    intro j
    have hmem := LEAF_RANK_S_LEAF V [elV ul 0, elV ul 1] w0 n f j hr
    simp only [s_leaf, Set.mem_setOf_eq] at hmem
    exact hmem.1
  have hleafB : ∀ j : ℕ, leaf V [elV ul 1, elV ul 0, f j] := fun j =>
    (ZASUVOR hp hs (hleafA j)).1
  have hper : periodic f n := LEAF_RANK_PERIODIC V [elV ul 0, elV ul 1] w0 n f hr
  -- getD projections of `ccUh` on a 3-point leaf list (p25m_cc3_wit pattern)
  have hget3 : ∀ (a b c : V3), leaf V [a, b, c] →
      (ccUh V [a, b, c]).getD 0 0 = a ∧ (ccUh V [a, b, c]).getD 1 0 = b ∧
        (ccUh V [a, b, c]).getD 2 0 = c := by
    intro a b c hlf
    have htr : truncateSimplex 2 (ccUh V [a, b, c]) = [a, b, c] :=
      (Classical.choose_spec (cc_uh_exists V [a, b, c])) hp hs hlf |>.2.1
    have hlist := LIST_OF_CC_UH (V := V) (ul := [a, b, c]) hs hp hlf
    have htrI := htr
    rw [hlist, (TRUNCATE_SIMPLEX_EXPLICIT_2 _ _ _ _).2] at htrI
    obtain ⟨e0, e12⟩ := List.cons.inj htrI
    obtain ⟨e1, e2t⟩ := List.cons.inj e12
    obtain ⟨e2, -⟩ := List.cons.inj e2t
    exact ⟨e0, e1, e2⟩
  -- the k = 4 refutation: a stem-pair 4-cell inside W collides with hno4
  have hkey : ∀ (a b c : V3), leaf V [a, b, c] → ccKe V [a, b, c] = 4 →
      ({(ccUh V [a, b, c]).getD 0 0, (ccUh V [a, b, c]).getD 1 0} : Set V3)
        = {elV ul 0, elV ul 1} →
      ccCell V [a, b, c] ⊆ W → False := by
    intro a b c hlf hk4 hpair hsub
    have hcc : ccCell V [a, b, c] = mcell4 V (ccUh V [a, b, c]) := by
      show mcell (ccKe V [a, b, c]) V (ccUh V [a, b, c]) = _
      rw [hk4]
      simp [mcell]
    rw [hcc] at hsub
    have hst := STEM_EDGEX hp hs hlf
    rw [hcc] at hst
    rw [hpair] at hst
    exact hno4 ⟨ccUh V [a, b, c],
      (Classical.choose_spec (cc_uh_exists V [a, b, c])) hp hs hlf |>.1, hst, hsub⟩
  -- k = 3 for both stem orientations (4 refuted via the K4 routes)
  have hpairB : ({(ccUh V [elV ul 1, elV ul 0, f (i + 1)]).getD 0 0,
      (ccUh V [elV ul 1, elV ul 0, f (i + 1)]).getD 1 0} : Set V3)
      = {elV ul 0, elV ul 1} := by
    obtain ⟨g0, g1, -⟩ := hget3 _ _ _ (hleafB (i + 1))
    rw [g0, g1]
    ext q
    simp
    tauto
  have hpairA : ({(ccUh V [elV ul 0, elV ul 1, f i]).getD 0 0,
      (ccUh V [elV ul 0, elV ul 1, f i]).getD 1 0} : Set V3)
      = {elV ul 0, elV ul 1} := by
    obtain ⟨g0, g1, -⟩ := hget3 _ _ _ (hleafA i)
    rw [g0, g1]
  have hkB : ccKe V [elV ul 1, elV ul 0, f (i + 1)] = 3 := by
    rcases CC_KE_34 V [elV ul 1, elV ul 0, f (i + 1)] with hk | hk
    · exact hk
    · exfalso
      have hsub := K4_CC_WIM V ul w0 n f (i + 1) hp hs hr hnc hn hk
      rw [show (i + 1) + (n - 1) = i + n - 1 + 1 from by omega,
        F_SUC_PRE (by omega) hper i] at hsub
      refine hkey _ _ _ (hleafB (i + 1)) hk hpairB ?_
      rw [hW]
      exact hsub
  have hkA : ccKe V [elV ul 0, elV ul 1, f i] = 3 := by
    rcases CC_KE_34 V [elV ul 0, elV ul 1, f i] with hk | hk
    · exact hk
    · exfalso
      refine hkey _ _ _ (hleafA i) hk hpairA ?_
      rw [hW]
      exact K4_CC_WI_ALT V ul w0 n f i hp hs hr hnc hn hk
  refine ⟨hkB, hkA, ?_, ?_, ?_⟩
  · rw [hW]; exact K3_CC_WI_ALT V ul w0 n f i hp hs hr hnc hn hkA
  · rw [hW]
    have hsub := K3_CC_WIM_ALT V ul w0 n f (i + 1) hp hs hr hnc hn hkB
    rw [show (i + 1) + (n - 1) = i + n - 1 + 1 from by omega,
      F_SUC_PRE (by omega) hper i] at hsub
    exact hsub
  · intro heq
    obtain ⟨gA0, gA1, -⟩ := hget3 _ _ _ (hleafA i)
    obtain ⟨gB0, gB1, -⟩ := hget3 _ _ _ (hleafB (i + 1))
    have heq' := FUEIMOV_3 (V := V) (ul := [elV ul 0, elV ul 1, f i])
      (vl := [elV ul 1, elV ul 0, f (i + 1)]) hs hp (hleafA i) (hleafB (i + 1)) hkA
      (by rw [gA0, gA1, gB0, gB1]; ext q; simp; tauto) heq
    obtain ⟨h01, -⟩ := List.cons.inj heq'
    refine hnc ?_
    show Collinear ℝ ({elV ul 0, elV ul 1, w0} : Set V3)
    have hset : ({elV ul 0, elV ul 1, w0} : Set V3) = ({elV ul 1, w0} : Set V3) := by
      rw [h01]
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair _ (elV ul 1) w0

/-- HOL `JSPEVYT_EXPLICIT`. -/
theorem JSPEVYT_EXPLICIT (u0 u1 u2 : V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hnc : ¬ Collinear3 u0 u1 u2) (hhl : hl [u0, u1, u2] ≤ 1.34)
    (h1 : 2 * hminus ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) :
    dist u1 u2 < 2 * hminus := by
  sorry

/-- HOL `CELL_CLUSTER_ESTIMATE_REDUCE`: the per-edge statement implies the
cell-cluster inequality. -/
theorem CELL_CLUSTER_ESTIMATE_REDUCE (V : Set V3) (hp : Packing V) (hs : saturated V)
    (hedge : ∀ u0 u1 : V3, u0 ≠ u1 → hminus ≤ hl [u0, u1] → hl [u0, u1] ≤ hplus →
      0 ≤ setSum {X | {u0, u1} ∈ edgeX V X ∧ mcellSet V X} fun X =>
        gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {u0, u1} X) :
    cellClusterInequality V := by
  sorry

/-- HOL `cc_card_data` (field projection). -/
theorem cc_card_data (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) :
    cc_card_v11 (cc_data_v8 V f u0 u1) = Set.ncard (s_leaf V [u0, u1]) :=
  rfl

/-- HOL `cc_real_data` (field projections). -/
theorem cc_real_data (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) :
    cc_azim_v11 (cc_data_v8 V f u0 u1) = azim_mcell V f u0 u1 ∧
      cc_gg_v11 (cc_data_v8 V f u0 u1) = gg_mcell V f u0 u1 ∧
        cc_gg3a_v11 (cc_data_v8 V f u0 u1) =
            (fun i => gammaX V (ccCell V [u0, u1, f i]) lmfun *
              criticalWeight V (ccCell V [u0, u1, f i])) ∧
          cc_gg3b_v11 (cc_data_v8 V f u0 u1) =
            (fun i => gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
              criticalWeight V (ccCell V [u1, u0, f (i + 1)])) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- HOL `cc_bool_data` (field projections). -/
theorem cc_bool_data (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) :
    cc_subcrit_v11 (cc_data_v8 V f u0 u1) =
        (fun i => dist (f i) (f (i + 1)) < 2 * hminus) ∧
      cc_crit_v11 (cc_data_v8 V f u0 u1) =
        (fun i => 2 * hminus ≤ dist (f i) (f (i + 1)) ∧
          dist (f i) (f (i + 1)) ≤ 2 * hplus) ∧
      cc_supercrit_v11 (cc_data_v8 V f u0 u1) =
        (fun i => 2 * hplus < dist (f i) (f (i + 1))) ∧
      cc_small_v11 (cc_data_v8 V f u0 u1) =
        (fun i => dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
      cc_small_eta_v11 (cc_data_v8 V f u0 u1) =
        (fun i => hl [u0, u1, f i] < 1.34) ∧
      cc_4cell_v11 (cc_data_v8 V f u0 u1) =
        (fun i => ∃ ul, barV V 3 ul ∧ {u0, u1} ∈ edgeX V (mcell4 V ul) ∧
          mcell4 V ul ⊆ wedgeGe u0 u1 (f i) (f (i + 1))) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- HOL `cc_bool_model_data`. -/
theorem cc_bool_model_data (V : Set V3) (f : ℕ → V3) (w0 : V3) (n : ℕ) (u0 u1 : V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
    (h0 : u0 ∈ V) (h1 : u1 ∈ V) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    cc_bool_model_v11 (cc_data_v8 V f u0 u1) := by
  sorry

/-- HOL `cc_prep_model_data`. -/
theorem cc_prep_model_data (V : Set V3) (f : ℕ → V3) (w0 : V3) (n : ℕ) (u0 u1 : V3)
    (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hnc : ¬ Collinear3 u0 u1 w0) (hr : leaf_rank V [u0, u1] w0 n f) :
    cc_bool_prep_v11 (cc_data_v8 V f u0 u1) := by
  sorry

/-- HOL `LEAF_DOMAIN`.
leaf-rank 波（2026-10-08）转真（装配级）：叶面非退化由 `GBEWYFX`（PA18 ✅），
三组弦长 `dist < 2 * radV < 2 * sqrt 2` 由外心桥 `OAPVION2_concl`（PA2 ✅）+
三角不等式（`S_LEAF_BOUNDED` 同款套路），下界由 packing 分离
（`BARV_SUBSET` PA5 ✅ + `Packing.dist_ge_two`），`eta_y` 界由 `RADV_ETAY`。
-- 2026-10-13：原欠叶 `RADV_ETAY` 已转真（本文件，外心-Heron 代数），全链零债。 -/
theorem LEAF_DOMAIN (V : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hl' : leaf V ul) :
    ¬ Collinear3 (elV ul 0) (elV ul 1) (elV ul 2) ∧
      2 ≤ dist (elV ul 1) (elV ul 2) ∧ 2 ≤ dist (elV ul 0) (elV ul 2) ∧
      2 ≤ dist (elV ul 0) (elV ul 1) ∧
      dist (elV ul 1) (elV ul 2) < 2 * Real.sqrt 2 ∧
      dist (elV ul 0) (elV ul 2) < 2 * Real.sqrt 2 ∧
      dist (elV ul 0) (elV ul 1) < 2 * Real.sqrt 2 ∧
      eta_y (dist (elV ul 0) (elV ul 1)) (dist (elV ul 0) (elV ul 2))
          (dist (elV ul 1) (elV ul 2)) < Real.sqrt 2 := by
  have h3 : ul.length = 3 := hl'.1.1
  rcases ul with _ | ⟨a, t⟩
  · simp at h3
  rcases t with _ | ⟨b, t⟩
  · simp at h3
  rcases t with _ | ⟨c, t⟩
  · simp at h3
  cases t with
  | nil =>
    -- 字面表归约（GBEWYFX 同款 get!/getD 消解）
    have hget : [a, b, c][0]! = a ∧ [a, b, c][1]! = b ∧ [a, b, c][2]! = c := by simp
    obtain ⟨e0, e1, e2⟩ := hget
    have hgetD : elV [a, b, c] 0 = a ∧ elV [a, b, c] 1 = b ∧ elV [a, b, c] 2 = c := by
      simp [elV]
    obtain ⟨d0, d1, d2⟩ := hgetD
    rw [d0, d1, d2]
    have hnc : ¬ Collinear3 a b c := fun hcol =>
      GBEWYFX hp hs hl' (by rw [e0, e1, e2]; exact hcol)
    have hset : setOfList [a, b, c] = ({a, b, c} : Set V3) := by
      ext q; simp [setOfList]
    have hrad : radV ({a, b, c} : Set V3) < Real.sqrt 2 := by
      have h2 : hl [a, b, c] < Real.sqrt 2 := hl'.2
      rw [hl, hset] at h2
      exact h2
    -- 三点互异（非退化三点式的手工消解，S_LEAF_BOUNDED 同款）
    have hab : a ≠ b := by
      intro he
      refine hnc (show Collinear ℝ ({a, b, c} : Set V3) from ?_)
      have hset' : ({a, b, c} : Set V3) = ({b, c} : Set V3) := by
        rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset']; exact collinear_pair _ b c
    have hac : a ≠ c := by
      intro he
      refine hnc (show Collinear ℝ ({a, b, c} : Set V3) from ?_)
      have hset' : ({a, b, c} : Set V3) = ({b, c} : Set V3) := by
        rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset']; exact collinear_pair _ b c
    have hbc : b ≠ c := by
      intro he
      refine hnc (show Collinear ℝ ({a, b, c} : Set V3) from ?_)
      have hset' : ({a, b, c} : Set V3) = ({a, c} : Set V3) := by
        rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset']; exact collinear_pair _ a c
    -- 弦长上界：外心桥 + 三角不等式（radV = dist p circumcenter）
    have haff : ¬ affineDependent ({a, b, c} : Set V3) := p25_not_affdep3 hab hac hbc hnc
    have dp0 := OAPVION2_concl ({a, b, c} : Set V3) haff a (by simp)
    have dp1 := OAPVION2_concl ({a, b, c} : Set V3) haff b (by simp)
    have dp2 := OAPVION2_concl ({a, b, c} : Set V3) haff c (by simp)
    have f0 : dist a (circumcenter ({a, b, c} : Set V3)) = radV ({a, b, c} : Set V3) := by
      rw [dist_comm a (circumcenter ({a, b, c} : Set V3))]; exact dp0.symm
    have f1 : dist b (circumcenter ({a, b, c} : Set V3)) = radV ({a, b, c} : Set V3) := by
      rw [dist_comm b (circumcenter ({a, b, c} : Set V3))]; exact dp1.symm
    have g1 : dist (circumcenter ({a, b, c} : Set V3)) b = radV ({a, b, c} : Set V3) :=
      dp1.symm
    have g2 : dist (circumcenter ({a, b, c} : Set V3)) c = radV ({a, b, c} : Set V3) :=
      dp2.symm
    have tbc : dist b c ≤ dist b (circumcenter ({a, b, c} : Set V3)) +
        dist (circumcenter ({a, b, c} : Set V3)) c :=
      dist_triangle b (circumcenter ({a, b, c} : Set V3)) c
    have tac : dist a c ≤ dist a (circumcenter ({a, b, c} : Set V3)) +
        dist (circumcenter ({a, b, c} : Set V3)) c :=
      dist_triangle a (circumcenter ({a, b, c} : Set V3)) c
    have tab : dist a b ≤ dist a (circumcenter ({a, b, c} : Set V3)) +
        dist (circumcenter ({a, b, c} : Set V3)) b :=
      dist_triangle a (circumcenter ({a, b, c} : Set V3)) b
    rw [f1, g2] at tbc
    rw [f0, g2] at tac
    rw [f0, g1] at tab
    have bc : dist b c < 2 * Real.sqrt 2 := by linarith
    have ac : dist a c < 2 * Real.sqrt 2 := by linarith
    have ab : dist a b < 2 * Real.sqrt 2 := by linarith
    -- packing 分离下界
    have hsub : setOfList [a, b, c] ⊆ V := BARV_SUBSET V 2 [a, b, c] hl'.1
    have hmemV : ∀ p ∈ ({a, b, c} : Set V3), p ∈ V := by
      intro p hp'
      rw [← hset] at hp'
      exact hsub hp'
    refine ⟨hnc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hp.dist_ge_two (hmemV b (by simp)) (hmemV c (by simp)) hbc
    · exact hp.dist_ge_two (hmemV a (by simp)) (hmemV c (by simp)) hac
    · exact hp.dist_ge_two (hmemV a (by simp)) (hmemV b (by simp)) hab
    · exact bc
    · exact ac
    · exact ab
    · rw [← RADV_ETAY a b c hnc]; exact hrad
  | cons d t' => simp at h3

/-- HOL `CELL_CLUSTER_N_LE_1`: a critical stem with at most one leaf has a
nonnegative weight sum. -/
theorem CELL_CLUSTER_N_LE_1 (V : Set V3) (u0 u1 : V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hp : Packing V) (hs : saturated V) (hlo : hminus ≤ hl [u0, u1])
    (hhi : hl [u0, u1] ≤ hplus) (hcard : Set.ncard (s_leaf V [u0, u1]) ≤ 1) :
    0 ≤ setSum {X | {u0, u1} ∈ edgeX V X ∧ mcellSet V X} fun X =>
      gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {u0, u1} X := by
  sorry

/-- HOL `NOT_COPLANAR_AFF_3`.  Proof: if the direction of the affine span
had rank `< 3`, it would be spanned by two vectors `v1, v2` (a basis of the
rank-2 case, `finrank_le_one_iff` twice for the rank-`≤ 1` case), and `s`
would sit inside the plane `affineSpan {p, p + v1, p + v2}` — contradicting
non-coplanarity. -/
theorem NOT_COPLANAR_AFF_3 (s : Set V3) (hnc : ¬ Coplanar s) :
    affDim s = 3 := by
  by_contra hne
  have hsne : s ≠ ∅ := by
    intro he
    rw [he] at hnc
    exact hnc coplanar_empty
  have haff : affDim s = ((Module.finrank ℝ (vectorSpan ℝ s) : ℕ) : ℤ) := by
    rw [affDim, if_neg hsne]
  have hcast : ((Module.finrank ℝ (vectorSpan ℝ s) : ℕ) : ℤ) ≠ 3 := by
    rw [← haff]; exact hne
  have hle : Module.finrank ℝ (vectorSpan ℝ s) ≤ 3 := by
    simpa [finrank_euclideanSpace_fin] using Submodule.finrank_le (vectorSpan ℝ s)
  have hlt : Module.finrank ℝ (vectorSpan ℝ s) < 3 := by omega
  obtain ⟨v1, v2, hspan⟩ : ∃ v1 v2 : V3,
      (vectorSpan ℝ s : Submodule ℝ V3) ≤ Submodule.span ℝ ({v1, v2} : Set V3) := by
    by_cases h2 : Module.finrank ℝ (vectorSpan ℝ s) = 2
    · have hb : Module.Basis (Fin 2) ℝ ↥(vectorSpan ℝ s) :=
        Module.finBasisOfFinrankEq ℝ (vectorSpan ℝ s) h2
      refine ⟨(hb 0 : V3), (hb 1 : V3), ?_⟩
      intro w hw
      have hwspan : (⟨w, hw⟩ : ↥(vectorSpan ℝ s)) ∈
          (Submodule.span ℝ (Set.range hb) :
            Submodule ℝ ↥(vectorSpan ℝ s)) := by
        rw [Module.Basis.span_eq]
        exact Submodule.mem_top
      have hrng : Set.range hb ⊆
          ({(hb 0 : ↥(vectorSpan ℝ s)), (hb 1 : ↥(vectorSpan ℝ s))} :
            Set ↥(vectorSpan ℝ s)) := by
        intro y hy
        obtain ⟨i, rfl⟩ := hy
        fin_cases i
        · simp
        · simp
      have hwpairW : (⟨w, hw⟩ : ↥(vectorSpan ℝ s)) ∈
          (Submodule.span ℝ ({(hb 0 : ↥(vectorSpan ℝ s)), (hb 1 : ↥(vectorSpan ℝ s))} :
            Set ↥(vectorSpan ℝ s))) := Submodule.span_mono hrng hwspan
      obtain ⟨r, t, hrt⟩ := Submodule.mem_span_pair.mp hwpairW
      refine Submodule.mem_span_pair.mpr ⟨r, t, ?_⟩
      exact congrArg (fun x : ↥(vectorSpan ℝ s) => (x : V3)) hrt
    · have h1 : Module.finrank ℝ (vectorSpan ℝ s) ≤ 1 := by omega
      obtain ⟨v, hv⟩ := (finrank_le_one_iff (K := ℝ) (V := ↥(vectorSpan ℝ s))).mp h1
      refine ⟨(v : V3), 0, fun w hw => ?_⟩
      obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
      refine Submodule.mem_span_pair.mpr ⟨c, 0, ?_⟩
      rw [zero_smul, add_zero]
      have hcoe : ((c • v : ↥(vectorSpan ℝ s)) : V3)
          = (c : ℝ) • ((v : V3)) := rfl
      rw [← hcoe, hc]
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hsne
  refine absurd ?_ hnc
  refine ⟨p, p + v1, p + v2, ?_⟩
  intro q hq
  have hqp : q -ᵥ p ∈ (vectorSpan ℝ s) := by
    have hvd := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ s hq)
      (subset_affineSpan ℝ s hp)
    rwa [direction_affineSpan] at hvd
  have hdir : Submodule.span ℝ ({v1, v2} : Set V3) ≤
      (affineSpan ℝ ({p, p + v1, p + v2} : Set V3)).direction := by
    rw [direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right ℝ (show p ∈ ({p, p + v1, p + v2} : Set V3) from by simp)]
    refine Submodule.span_mono ?_
    intro z hz
    rcases Set.mem_insert_iff.mp hz with hz1 | hz1
    · rw [hz1]
      exact ⟨p + v1, by simp, by simp⟩
    · rw [Set.mem_singleton_iff.mp hz1]
      exact ⟨p + v2, by simp, by simp⟩
  rw [show (q : V3) = (q -ᵥ p) +ᵥ p from (vsub_vadd ..).symm]
  exact AffineSubspace.vadd_mem_of_mem_direction (hdir (hspan hqp))
    (mem_affineSpan ℝ (by simp : p ∈ ({p, p + v1, p + v2} : Set V3)))


/-- HOL `LEAF_RANK_LEAF`. -/
theorem LEAF_RANK_LEAF (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hr : leaf_rank V [u0, u1] w0 n f) : leaf V [u0, u1, f i] := by
  have h := LEAF_RANK_S_LEAF V [u0, u1] w0 n f i hr
  exact h.1


/-! ### Kit A: wedge inclusion (`affGe` 2-2 ⊆ `wedgeGe`; mirror of
LocalAuto5 `WEDGE_GE_EQ_AFF_GE` direction 2) -/

/-- A1: member of `affGe {v0,v1} {w}` has zero azimuth off the `w` boundary
(LocalAuto5 `AZIM_EQ_0_GE_ALT2`, ← direction only). -/
private theorem p25rpi_azim0_of_affGe {v0 v1 w z : V3} (hw : ¬ Collinear3 v0 v1 w)
    (hv0v1 : v0 ≠ v1) (hw0 : w ≠ v0) (hw1 : w ≠ v1) (t1 t2 t3 : ℝ) (ht3 : 0 ≤ t3)
    (hsum : t1 + t2 + t3 = 1) (hz : z = t1 • v0 + t2 • v1 + t3 • w) :
    azim v0 v1 w z = 0 := by
  by_cases hcolz : Collinear3 v0 v1 z
  · unfold azim
    exact if_pos (Or.inr hcolz)
  · have ht3pos : 0 < t3 := by
      by_contra hle
      have ht3z : t3 = 0 := le_antisymm (not_lt.mp hle) ht3
      refine hcolz ?_
      have hz2 : z - v0 = t2 • (v1 - v0) := by
        rw [hz, ht3z, zero_smul, add_zero, show t1 = 1 - t2 from by linarith]
        module
      exact (collinear3_iff_smul (v := v0) (w := v1) (w1 := z)
        (Ne.symm hv0v1)).mpr ⟨t2, hz2⟩
    refine (azim_eq_zero_iff_alt hw hcolz).mpr ?_
    refine (affGt_pair_iff hv0v1 hw0 hw1).mpr ⟨t3, ht3pos, t2, ?_⟩
    rw [hz, show t1 = 1 - t2 - t3 from by linarith]
    module

/-- A2: coefficient extraction from `affGe {a,b} {x,y}` (LocalAuto5 `AFF_GE22`,
→ direction only, with both pairs distinct). -/
private theorem p25rpi_affGe22_coeffs {a b x y z : V3}
    (hab : a ≠ b) (hxy : x ≠ y) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (hz : z ∈ affGe ({a, b} : Set V3) ({x, y} : Set V3)) :
    ∃ aa bb xx yy : ℝ, 0 ≤ xx ∧ 0 ≤ yy ∧ aa + bb + xx + yy = 1 ∧
      z = aa • a + bb • b + xx • x + yy • y := by
  obtain ⟨f, hfin, hval, hpos, hone⟩ := hz
  have hT : hfin.toFinset = ({a, b, x, y} : Finset V3) := by
    ext w
    simp only [hfin.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hT] at hval hone
  rw [Finset.sum_insert (by simp [hax, hay, hab]),
    Finset.sum_insert (by simp [hbx, hby]),
    Finset.sum_insert (by simp [hxy]), Finset.sum_singleton] at hval hone
  refine ⟨f a, f b, f x, f y, hpos x (by simp), hpos y (by simp), by linarith, ?_⟩
  rw [hval]
  abel

/-- A3: `affGt {a,b} {x,y}` membership by the four-coefficient witness
(mirror of LocalAuto5 `AFF_GE22` reverse direction; only the `x,y` coefficients
are sign-constrained). -/
private theorem p25rpi_mem_affGt22 {a b x y z : V3}
    (hab : a ≠ b) (hxy : x ≠ y) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (aa bb xx yy : ℝ) (hxx : 0 < xx) (hyy : 0 < yy) (hsum : aa + bb + xx + yy = 1)
    (hz : z = aa • a + bb • b + xx • x + yy • y) :
    z ∈ affGt ({a, b} : Set V3) ({x, y} : Set V3) := by
  have hfin : (({a, b} : Set V3) ∪ ({x, y} : Set V3)).Finite :=
    ((Set.finite_singleton b).insert a).union ((Set.finite_singleton y).insert x)
  have hT : hfin.toFinset = ({a, b, x, y} : Finset V3) := by
    ext w
    simp only [hfin.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨fun w => if w = x then xx else if w = y then yy else
    if w = b then bb else aa, hfin, ?_, ?_, ?_⟩
  · rw [hT, hz, Finset.sum_insert (by simp [hax, hay, hab]),
      Finset.sum_insert (by simp [hbx, hby]),
      Finset.sum_insert (by simp [hxy]), Finset.sum_singleton]
    simp only
    rw [if_neg hax, if_neg hay, if_neg hab, if_neg hbx, if_neg hby,
      if_neg (Ne.symm hxy)]
    simp only [if_true]
    abel
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · rw [hw]
      show 0 < (if x = x then xx else if x = y then yy else
        if x = b then bb else aa)
      rw [if_pos (rfl : x = x)]
      exact hxx
    · rw [hw]
      show 0 < (if y = x then xx else if y = y then yy else
        if y = b then bb else aa)
      rw [if_neg (Ne.symm hxy), if_pos (rfl : y = y)]
      exact hyy
  · rw [hT, Finset.sum_insert (by simp [hax, hay, hab]),
      Finset.sum_insert (by simp [hbx, hby]),
      Finset.sum_insert (by simp [hxy]), Finset.sum_singleton]
    simp only
    rw [if_neg hax, if_neg hay, if_neg hab, if_neg hbx, if_neg hby,
      if_neg (Ne.symm hxy)]
    simp only [if_true]
    linarith

/-- A4: the closed two-sided cone sits in the closed wedge (LocalAuto5
`WEDGE_GE_EQ_AFF_GE`, ⊆ direction). -/
private theorem p25rpi_affGe22_subset_wedgeGe (u0 u1 w1 w2 : V3)
    (hw1 : ¬ Collinear3 u0 u1 w1) (hw2 : ¬ Collinear3 u0 u1 w2)
    (hpos : 0 < azim u0 u1 w1 w2) (hpi : azim u0 u1 w1 w2 < Real.pi) :
    affGe ({u0, u1} : Set V3) ({w1, w2} : Set V3) ⊆ wedgeGe u0 u1 w1 w2 := by
  have hu0u1 : u0 ≠ u1 := fun he => hw1 (collinear3_of_eq he.symm)
  have hw1v0 : w1 ≠ u0 := fun he => hw1 (collinear3_pair_left he)
  have hw1v1 : w1 ≠ u1 := fun he => hw1 (collinear3_pair_right he)
  have hw2v0 : w2 ≠ u0 := fun he => hw2 (collinear3_pair_left he)
  have hw2v1 : w2 ≠ u1 := fun he => hw2 (collinear3_pair_right he)
  have hw1w2 : w1 ≠ w2 := by
    intro he
    subst he
    rw [azim_self] at hpos
    exact lt_irrefl 0 hpos
  intro z hz
  obtain ⟨aa, bb, xx, yy, hxx0, hyy0, hone, hzy⟩ :=
    p25rpi_affGe22_coeffs hu0u1 hw1w2 (Ne.symm hw1v0) (Ne.symm hw2v0) (Ne.symm hw1v1)
      (Ne.symm hw2v1) hz
  rw [wedgeGe, Set.mem_setOf_eq]
  by_cases hyyz : yy = 0
  · -- w1 侧：z 落在 {u0,u1,w1} 闭半平面，azim w1 z = 0
    have hzy0 : z = aa • u0 + bb • u1 + xx • w1 := by
      rw [hyyz] at hzy
      simpa using hzy
    have hz0 : azim u0 u1 w1 z = 0 :=
      p25rpi_azim0_of_affGe hw1 hu0u1 hw1v0 hw1v1 aa bb xx hxx0
        (by rw [hyyz] at hone; linarith) hzy0
    refine ⟨azim_nonneg u0 u1 w1 z, ?_⟩
    rw [hz0]
    exact azim_nonneg u0 u1 w1 w2
  · -- yy > 0
    have hyypos : 0 < yy := lt_of_le_of_ne hyy0 (Ne.symm hyyz)
    by_cases hxxz : xx = 0
    · -- w2 侧边界：azim w1 z = azim w1 w2
      have haa : aa = 1 - bb - yy := by rw [hxxz] at hone; linarith
      have hzy2 : z - u0 = yy • (w2 - u0) + bb • (u1 - u0) := by
        rw [hzy, hxxz, haa]
        module
      have hzGt : z ∈ affGt ({u0, u1} : Set V3) ({w2} : Set V3) :=
        (affGt_pair_iff hu0u1 hw2v0 hw2v1).mpr ⟨yy, hyypos, bb, hzy2⟩
      have hncz : ¬ Collinear3 u0 u1 z := by
        intro hcol
        obtain ⟨t, ht⟩ :=
          (collinear3_iff_smul (v := u0) (w := u1) (w1 := z) (Ne.symm hu0u1)).mp hcol
        rw [hzy2] at ht
        have hstep : yy • (w2 - u0) = ((t - bb) • (u1 - u0) : V3) := by
          rw [sub_smul]
          linear_combination (norm := module) ht
        have h5 : yy • (w2 - u0) = yy • (((t - bb) / yy) • (u1 - u0) : V3) := by
          rw [smul_smul, mul_comm yy ((t - bb) / yy),
            div_mul_cancel₀ (t - bb) (ne_of_gt hyypos)]
          exact hstep
        have h6 : (w2 - u0 : V3) = ((t - bb) / yy) • (u1 - u0) :=
          smul_right_injective _ (ne_of_gt hyypos) h5
        exact hw2 ((collinear3_iff_smul (v := u0) (w := u1) (w1 := w2)
          (Ne.symm hu0u1)).mpr ⟨(t - bb) / yy, h6⟩)
      exact ⟨azim_nonneg u0 u1 w1 z,
        le_of_eq ((azim_eq_azim_iff_alt hw1 hncz hw2).mpr hzGt)⟩
    · -- 严格内侧：wedge = affGt 2-2
      have hzGt : z ∈ affGt ({u0, u1} : Set V3) ({w1, w2} : Set V3) :=
        p25rpi_mem_affGt22 hu0u1 hw1w2 (Ne.symm hw1v0) (Ne.symm hw2v0) (Ne.symm hw1v1)
          (Ne.symm hw2v1) aa bb xx yy (lt_of_le_of_ne hxx0 (Ne.symm hxxz)) hyypos hone hzy
      have hzW : z ∈ Kepler.Geom.wedge u0 u1 w1 w2 := by
        rw [wedge_eq_affGt hw1 hw2 hpos hpi]
        exact hzGt
      exact WEDGE_SUBSET_WEDGE_GE u0 u1 w1 w2 hzW

/-! ### Kit B: coplanar fourth point into the stem-leaf plane, then the
azimuth collapses into {0, π} (Planarity `azim_eq_0_or_pi_of_coplanar`
independent route: dimension sandwich + `azim_frame_spec` polar). -/

/-- finrank of a two-generator span is at most 2 (PA25
`p25_finrank_span_pair_le_two` in-file twin). -/
private theorem p25rpi_finrank_span_pair_le_two (a b : V3) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  have h2 := finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset V3)
  unfold Set.finrank at h2
  rw [show (({a, b} : Finset V3) : Set V3) = ({a, b} : Set V3) from by simp] at h2
  refine h2.trans ?_
  calc ({a, b} : Finset V3).card ≤ ({b} : Finset V3).card + 1 := Finset.card_insert_le a {b}
    _ = 2 := by simp

/-- finrank monotone on submodules. -/
private theorem p25rpi_finrank_mono {S T : Submodule ℝ V3} (h : S ≤ T) :
    Module.finrank ℝ S ≤ Module.finrank ℝ T :=
  Submodule.finrank_mono h

/-- B1: a coplanar fourth point lies in the stem-leaf plane vector span:
`∃ β γ, w2 - u0 = β • (u1 - u0) + γ • (w1 - u0)`. -/
private theorem p25rpi_coplanar_combo {u0 u1 w1 w2 : V3}
    (hw1 : ¬ Collinear3 u0 u1 w1)
    (hcop : Coplanar ({u0, u1, w1, w2} : Set V3)) :
    ∃ β γ : ℝ, w2 - u0 = β • (u1 - u0) + γ • (w1 - u0) := by
  obtain ⟨p, q, r, hsp⟩ := hcop
  set T : Set V3 := ({u0, u1, w1} : Set V3) with hTdef
  set U : Set V3 := ({u0, u1, w1, w2} : Set V3) with hUdef
  have hleUP : affineSpan ℝ U ≤ affineSpan ℝ ({p, q, r} : Set V3) :=
    affineSpan_le.mpr hsp
  have hdUle : vectorSpan ℝ U ≤ Submodule.span ℝ ({q - p, r - p} : Set V3) := by
    have h1 : vectorSpan ℝ U ≤ vectorSpan ℝ ({p, q, r} : Set V3) := by
      have hd := AffineSubspace.direction_le hleUP
      rwa [direction_affineSpan, direction_affineSpan] at hd
    refine h1.trans ?_
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show p ∈ ({p, q, r} : Set V3) from by simp)]
    rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl | rfl
    · simp
    · exact Submodule.subset_span (by left; rfl)
    · exact Submodule.subset_span (by right; rfl)
  have hTsubU : T ⊆ U := by
    intro x hx
    simp only [hTdef, hUdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hu0T : u0 ∈ T := by simp [hTdef]
  have hdT : Module.finrank ℝ (vectorSpan ℝ T) = 2 := by
    have hne : T ≠ ∅ := by
      intro he
      rw [he] at hu0T
      exact hu0T
    have hdim := NOT_COLLINEAR_AFF_DIM2 u0 u1 w1 hw1
    rw [affDim, if_neg hne] at hdim
    exact_mod_cast hdim
  have hdU2 : Module.finrank ℝ (vectorSpan ℝ U) = 2 := by
    have hle := p25rpi_finrank_mono (vectorSpan_mono (k := ℝ) hTsubU)
    have hle2 := p25rpi_finrank_mono hdUle
    have hpair := p25rpi_finrank_span_pair_le_two (q - p) (r - p)
    omega
  -- vectorSpan T is exactly the two-difference span
  have hTeq : vectorSpan ℝ T = Submodule.span ℝ ({u1 - u0, w1 - u0} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show u0 ∈ T from hu0T)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro d ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by left; rfl)
      · exact Submodule.subset_span (by right; rfl)
    · rw [Submodule.span_le]
      rintro d (rfl | rfl)
      · exact Submodule.subset_span ⟨u1, by simp [hTdef], rfl⟩
      · exact Submodule.subset_span ⟨w1, by simp [hTdef], rfl⟩
  -- membership and pin-down
  have hm1 : (u1 - u0 : V3) ∈ vectorSpan ℝ U := by
    refine vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (s := U) (p₁ := u1) (p₂ := u0) ?_ ?_
    · exact mem_affineSpan ℝ (by simp [hUdef])
    · exact mem_affineSpan ℝ (by simp [hUdef])
  have hm2 : (w1 - u0 : V3) ∈ vectorSpan ℝ U := by
    refine vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (s := U) (p₁ := w1) (p₂ := u0) ?_ ?_
    · exact mem_affineSpan ℝ (by simp [hUdef])
    · exact mem_affineSpan ℝ (by simp [hUdef])
  have hspEq : Submodule.span ℝ ({u1 - u0, w1 - u0} : Set V3) = vectorSpan ℝ U :=
    Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (by
      intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | rfl
      · exact hm1
      · exact hm2))
      (by rw [← hTeq, hdT, hdU2])
  have hm4 : (w2 - u0 : V3) ∈ vectorSpan ℝ U := by
    refine vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (s := U) (p₁ := w2) (p₂ := u0) ?_ ?_
    · exact mem_affineSpan ℝ (by simp [hUdef])
    · exact mem_affineSpan ℝ (by simp [hUdef])
  rw [← hspEq] at hm4
  obtain ⟨β, γ, hcombo⟩ := Submodule.mem_span_pair.mp hm4
  exact ⟨β, γ, hcombo.symm⟩

/-- B2: with the fourth point in the stem-leaf plane, the azimuth collapses
into `{0, π}` (polar frame argument; sin A = 0 with `0 ≤ A < 2π`). -/
private theorem p25rpi_azim_0_or_pi_of_combo {u0 u1 w1 w2 : V3}
    (hw1 : ¬ Collinear3 u0 u1 w1) (hw2 : ¬ Collinear3 u0 u1 w2)
    (hu0u1 : u0 ≠ u1)
    (hcombo : ∃ β γ : ℝ, w2 - u0 = β • (u1 - u0) + γ • (w1 - u0)) :
    azim u0 u1 w1 w2 = 0 ∨ azim u0 u1 w1 w2 = Real.pi := by
  obtain ⟨β, γ, hβγ⟩ := hcombo
  obtain ⟨f1, f2, f3, hon, halign⟩ :=
    exists_on3_eq_smul (u1 - u0) (sub_ne_zero.mpr (Ne.symm hu0u1))
  have hax : (u1 - u0 : V3) = dist u1 u0 • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨psi, r1, r2, hr1, hr2, hz1, hz2⟩ :=
    azim_frame_spec hw1 hw2 hon hax (Ne.symm hu0u1)
  have hzline : zOf f1 f2 (w2 - u0)
      = ((γ : ℝ) : ℂ) * (((r1 : ℝ) : ℂ) * Complex.exp (((psi : ℝ) : ℂ) * Complex.I)) := by
    rw [hβγ, zOf_add, zOf_smul, zOf_smul, zOf_axis hax hon, hz1]
    push_cast
    ring
  rw [exp_add_I] at hz2
  have hkey : (r2 : ℂ) * Complex.exp (((azim u0 u1 w1 w2 : ℝ) : ℂ) * Complex.I)
      = ((γ : ℝ) : ℂ) * ((r1 : ℝ) : ℂ) := by
    refine mul_left_cancel₀ (Complex.exp_ne_zero (((psi : ℝ) : ℂ) * Complex.I)) ?_
    linear_combination (norm := ring_nf) (hz2.symm.trans hzline)
  have hsin : Real.sin (azim u0 u1 w1 w2) = 0 := by
    have him := congrArg Complex.im hkey
    rcases (by simpa using him :
        (r2 = 0) ∨ (Real.sin (azim u0 u1 w1 w2) = 0)) with h | h
    · exact absurd h hr2.ne'
    · exact h
  have h0 : 0 ≤ azim u0 u1 w1 w2 := azim_nonneg u0 u1 w1 w2
  have h2pi : azim u0 u1 w1 w2 < 2 * Real.pi := azim_lt_two_pi u0 u1 w1 w2
  rcases (Real.sin_eq_zero_iff).mp hsin with ⟨n, hn⟩
  rcases lt_trichotomy (n : ℤ) 0 with hneg | hzero | hposn
  · exfalso
    have hnz : (n : ℤ) ≤ -1 := by omega
    have hle : ((n : ℤ) : ℝ) ≤ ((-1 : ℤ) : ℝ) := by exact_mod_cast hnz
    have hmul := mul_le_mul_of_nonneg_right hle Real.pi_pos.le
    have hppi : (0:ℝ) < Real.pi := Real.pi_pos
    push_cast at hmul ⊢
    linarith
  · refine Or.inl ?_
    rw [← hn, hzero]
    push_cast
    ring
  · rcases lt_trichotomy (n : ℤ) 1 with hone | hn1 | hge
    · refine Or.inr ?_
      have hn2 : n = 1 := by omega
      rw [← hn, hn2]
      push_cast
      ring
    · refine Or.inr ?_
      rw [← hn, hn1]
      push_cast
      ring
    · exfalso
      have hnz : 2 ≤ (n : ℤ) := by omega
      have hle : ((2 : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hnz
      have h2p : ((2 : ℤ) : ℝ) = 2 := by push_cast; ring
      rw [h2p] at hle
      have hmul : (2:ℝ) * Real.pi ≤ ((n : ℤ) : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right hle Real.pi_pos.le
      linarith

/-! ### Kit C: the 4-point voronoi face is the circumcenter singleton
(non-coplanar + packing separation), giving the `barV V 3` face clause. -/

/-- C1: `affDim` of a singleton is 0. -/
private theorem p25rpi_affDim_singleton (a : V3) : affDim ({a} : Set V3) = 0 := by
  have hne : ({a} : Set V3) ≠ ∅ := by
    intro he
    have hm : a ∈ ({a} : Set V3) := Set.mem_singleton a
    rw [he] at hm
    exact hm
  rw [affDim, if_neg hne,
    vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_singleton a)]
  have hgen : ((fun x : V3 => x -ᵥ a) '' ({a} : Set V3)) = ({0} : Set V3) := by
    ext d
    simp only [Set.mem_image, Set.mem_singleton_iff, Set.mem_singleton_iff, vsub_eq_sub]
    constructor
    · rintro ⟨y, rfl, hdy⟩
      rw [← hdy]
      simp
    · rintro rfl
      exact ⟨a, rfl, by simp⟩
  rw [hgen, Submodule.span_singleton_eq_bot.mpr rfl]
  exact_mod_cast Submodule.finrank_eq_zero.mpr rfl

/-- C2: the voronoi face of a non-coplanar tetrahedron `S ⊆ V` (circumradius
`< √2`) is the circumcenter singleton, hence `affDim = 0`. -/
private theorem p25rpi_vor4_affDim0 (V : Set V3) (hp : Packing V) (u0 u1 w1 w2 : V3)
    (hSV : ({u0, u1, w1, w2} : Set V3) ⊆ V)
    (hncop : ¬ Coplanar ({u0, u1, w1, w2} : Set V3))
    (hrad : radV ({u0, u1, w1, w2} : Set V3) < Real.sqrt 2) :
    voronoiSet V ({u0, u1, w1, w2} : Set V3)
        = {circumcenter ({u0, u1, w1, w2} : Set V3)} ∧
      affDim (voronoiSet V ({u0, u1, w1, w2} : Set V3)) = 0 := by
  set S : Set V3 := ({u0, u1, w1, w2} : Set V3) with hSdef
  have hu0S : u0 ∈ S := by simp [hSdef]
  have hfin : S.Finite := by simp [hSdef]
  have hne : S ≠ ∅ := by
    intro he
    rw [he] at hu0S
    exact hu0S
  have haff3 : affDim S = 3 := NOT_COPLANAR_AFF_3 S hncop
  have hind : ¬ affineDependent S := by
    refine p6_affdep_of_dim S hfin ?_
    have hsub : S ⊆ Set.range ![u0, u1, w1, w2] := by
      intro x hx
      rw [hSdef] at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | hx
      · exact ⟨0, rfl⟩
      rcases hx with rfl | hx
      · exact ⟨1, rfl⟩
      rcases hx with rfl | hx
      · exact ⟨2, rfl⟩
      · exact ⟨3, hx.symm⟩
    have hle : Nat.card S ≤ Nat.card (Set.range ![u0, u1, w1, w2]) := by
      refine Nat.card_le_card_of_injective (f := fun x : S => ⟨x, hsub x.2⟩) ?_
      intro a b hab
      exact Subtype.ext (by simpa using hab)
    have hdrange : Nat.card (Set.range (![u0, u1, w1, w2] : Fin 4 → V3))
        ≤ Nat.card (Set.univ : Set (Fin 4)) := by
      refine Nat.card_le_card_of_injective
        (f := fun y : { y // y ∈ Set.range (![u0, u1, w1, w2] : Fin 4 → V3) } =>
          (⟨Classical.choose
              ((Set.mem_range (f := (![u0, u1, w1, w2] : Fin 4 → V3))).mp y.property),
            Set.mem_univ _⟩ :
            { x // x ∈ (Set.univ : Set (Fin 4)) })) ?_
      intro a b hab
      simp only at hab
      have hab' : (Classical.choose ((Set.mem_range (f := (![u0, u1, w1, w2] : Fin 4 → V3))).mp a.property))
          = (Classical.choose ((Set.mem_range (f := (![u0, u1, w1, w2] : Fin 4 → V3))).mp b.property)) :=
        Subtype.ext_iff.mp hab
      have ha := Classical.choose_spec ((Set.mem_range (f := (![u0, u1, w1, w2] : Fin 4 → V3))).mp a.property)
      have hb := Classical.choose_spec ((Set.mem_range (f := (![u0, u1, w1, w2] : Fin 4 → V3))).mp b.property)
      rw [hab'] at ha
      exact Subtype.ext (ha.symm.trans hb)
    have h4 : (Nat.card (Set.range ![u0, u1, w1, w2]) : ℤ) ≤ 4 := by
      have hcr := hdrange
      have hfin4 : Nat.card (Set.univ : Set (Fin 4)) = 4 := by simp
      omega
    omega
  have hcc := CIRCUMCENTER_IN_VORONOI_SET V S hp hSV hind hrad
  have hmem : ∀ x ∈ voronoiSet V S, ∀ u ∈ S, ∀ v ∈ V, dist x u ≤ dist x v := by
    intro x hx u hu v hv
    rw [voronoiSet, Set.mem_sInter] at hx
    exact hx (voronoiClosed V u) ⟨u, hu, rfl⟩ v hv
  have hdist0 : ∀ x ∈ voronoiSet V S, ∀ u ∈ S, dist x u = dist x u0 := by
    intro x hx u hu
    exact le_antisymm (hmem x hx u hu u0 (hSV hu0S)) (hmem x hx u0 hu0S u (hSV hu))
  have hcceq : ∀ u ∈ S, dist (circumcenter S) u = radV S := fun u hu =>
    (OAPVION2_concl S hind u hu).symm
  -- the pairwise differences span the whole space
  have htop : vectorSpan ℝ S = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have hdim : ((Module.finrank ℝ (vectorSpan ℝ S) : ℕ) : ℤ) = 3 := by
      rw [← haff3, affDim, if_neg hne]
    have hV3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    have h1 : Module.finrank ℝ (vectorSpan ℝ S) = 3 := by exact_mod_cast hdim
    rw [h1, hV3]
  -- a vector orthogonal to all pairwise differences is zero
  have hperp : ∀ z : V3, (∀ u ∈ S, ∀ u' ∈ S, inner ℝ z (u' - u) = 0) → z = 0 := by
    intro z hz
    have hzker : ∀ d ∈ vectorSpan ℝ S, inner ℝ z d = 0 := by
      intro d hd
      rw [vectorSpan_def] at hd
      refine Submodule.span_induction
        (p := fun e (_ : e ∈ Submodule.span ℝ (S -ᵥ S)) => inner ℝ z e = 0) ?_ ?_ ?_ ?_ hd
      · rintro d ⟨u, hu, u', hu', rfl⟩
        show inner ℝ z (u -ᵥ u') = 0
        rw [vsub_eq_sub]
        exact hz u' hu' u hu
      · simp
      · intro x y _ _ hx hy
        rw [inner_add_right, hx, hy, add_zero]
      · intro c x _ hx
        rw [inner_smul_right, hx, mul_zero]
    have hzin : z ∈ vectorSpan ℝ S := by rw [htop]; exact Submodule.mem_top
    exact inner_self_eq_zero.mp (hzker z hzin)
  -- uniqueness: any face member is equidistant from S, hence the circumcenter
  have huniq : ∀ x ∈ voronoiSet V S, x = circumcenter S := by
    intro x hx
    have hz := hperp (circumcenter S - x) ?_
    · rw [sub_eq_zero.mp hz]
    · intro u hu u' hu'
      have hxN : ‖x - u'‖ = ‖x - u‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, hdist0 x hx u' hu', hdist0 x hx u hu]
      have hcN : ‖circumcenter S - u'‖ = ‖circumcenter S - u‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, hcceq u' hu', hcceq u hu]
      have hXE : inner ℝ x u - inner ℝ x u' = (‖u‖ ^ 2 - ‖u'‖ ^ 2) / 2 := by
        have h1 := norm_sub_sq_real x u
        have h2 := norm_sub_sq_real x u'
        rw [congrArg (fun v => v ^ 2) hxN] at h2
        linear_combination (norm := ring_nf) (-(1 / 2)) * h1.symm.trans h2
      have hCE : inner ℝ (circumcenter S) u - inner ℝ (circumcenter S) u'
          = (‖u‖ ^ 2 - ‖u'‖ ^ 2) / 2 := by
        have h1 := norm_sub_sq_real (circumcenter S) u
        have h2 := norm_sub_sq_real (circumcenter S) u'
        rw [congrArg (fun v => v ^ 2) hcN] at h2
        linear_combination (norm := ring_nf) (-(1 / 2)) * h1.symm.trans h2
      rw [inner_sub_right, inner_sub_left, inner_sub_left]
      linear_combination (norm := ring_nf) (hXE - hCE)
  have hsing : voronoiSet V S = {circumcenter S} := by
    ext q
    simp only [Set.mem_singleton_iff]
    constructor
    · exact fun hq => huniq q hq
    · intro hq
      rw [hq]
      exact hcc
  refine ⟨hsing, ?_⟩
  rw [hsing]
  exact p25rpi_affDim_singleton (circumcenter S)

/-! ### Kit D: initial-sublist plumbing and the `barV V 3` clause for the
tetrahedron list. -/

private theorem p25rpi_init_len {xl zl : List V3} (h : initialSublist xl zl) :
    xl.length ≤ zl.length := by
  obtain ⟨t, ht⟩ := h
  rw [ht, List.length_append]
  omega

private theorem p25rpi_init_unique {xl yl zl : List V3} {n : ℕ}
    (h1 : initialSublist xl zl) (h2 : initialSublist yl zl)
    (hl1 : xl.length = n) (hl2 : yl.length = n) : xl = yl := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  have heq : xl ++ t1 = yl ++ t2 := by rw [← ht1, ht2]
  rcases List.append_eq_append_iff.1 heq with ⟨t, rfl, -⟩ | ⟨t, rfl, -⟩
  · rw [List.length_append, hl1] at hl2
    have ht0 : t.length = 0 := by omega
    rw [List.length_eq_zero_iff.1 ht0, List.append_nil]
  · rw [List.length_append, hl2] at hl1
    have ht0 : t.length = 0 := by omega
    rw [List.length_eq_zero_iff.1 ht0, List.append_nil]

private theorem p25rpi_init_self {vl ul : List V3} (h : initialSublist vl ul)
    (hlen : vl.length = ul.length) : vl = ul :=
  p25rpi_init_unique h (⟨[], by simp⟩ : initialSublist ul ul) hlen rfl

private theorem p25rpi_init_shift {vl : List V3} {a b c d : V3}
    (h : initialSublist vl [a, b, c, d]) (h3 : vl.length ≤ 3) :
    initialSublist vl [a, b, c] := by
  have hv : vl = [a, b, c, d].take vl.length := by
    obtain ⟨t, ht⟩ := h
    rw [ht, List.take_left]
  have htk : [a, b, c, d].take vl.length = [a, b, c].take vl.length := by
    have e : (([a, b, c] : List V3)) = [a, b, c, d].take 3 := rfl
    rw [e, List.take_take]
    congr 1
    omega
  have hlen3 : ([a, b, c].take vl.length).length = vl.length := by
    rw [List.length_take, show (([a, b, c] : List V3).length = 3) from rfl]
    omega
  refine ⟨[a, b, c].drop vl.length, ?_⟩
  rw [hv, htk, hlen3, List.take_append_drop vl.length ([a, b, c] : List V3)]

/-- D1: the `barV V 3` clause for the tetrahedron list `[u0, u1, w1, w2]`:
the three short prefixes come from `leaf V [u0, u1, w1]`; the full prefix's
voronoi face is the circumcenter singleton (Kit C). -/
private theorem p25rpi_barV3_of_ncop (V : Set V3) (hp : Packing V) (u0 u1 w1 w2 : V3)
    (hleaf1 : leaf V [u0, u1, w1]) (hw2V : w2 ∈ V)
    (hncop : ¬ Coplanar ({u0, u1, w1, w2} : Set V3))
    (hrad : radV ({u0, u1, w1, w2} : Set V3) < Real.sqrt 2) :
    barV V 3 [u0, u1, w1, w2] := by
  have hfull : initialSublist [u0, u1, w1, w2] [u0, u1, w1, w2] := ⟨[], by simp⟩
  have hvn3 : voronoiNondg V [u0, u1, w1] := hleaf1.1.2 _ ⟨⟨[], rfl⟩, by simp⟩
  have hV3 : setOfList [u0, u1, w1] ⊆ V := hvn3.2.1
  have hSV : setOfList [u0, u1, w1, w2] ⊆ V := by
    intro x hx
    simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.mem_singleton,
      List.not_mem_nil] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx
    · exact hV3 (by simp [setOfList])
    · exact hV3 (by simp [setOfList])
    · exact hV3 (by simp [setOfList])
    · exact hw2V
    · exact absurd hx (by simp)
  have hset : setOfList [u0, u1, w1, w2] = ({u0, u1, w1, w2} : Set V3) := by
    ext x
    simp [setOfList]
  have hVset : ({u0, u1, w1, w2} : Set V3) ⊆ V := by rw [← hset]; exact hSV
  refine ⟨rfl, ?_⟩
  intro vl hinit
  obtain ⟨hinit, hpos⟩ := hinit
  rcases Nat.lt_or_ge vl.length 4 with h4 | h4
  · exact hleaf1.1.2 vl ⟨p25rpi_init_shift hinit (by omega), hpos⟩
  · have heq : vl = [u0, u1, w1, w2] :=
      p25rpi_init_self hinit (by
        have hf : ([u0, u1, w1, w2] : List V3).length = 4 := rfl
        have := p25rpi_init_len hinit
        omega)
    subst heq
    refine ⟨by simp, hSV, ?_⟩
    have h0 := p25rpi_vor4_affDim0 V hp u0 u1 w1 w2 hVset hncop hrad
    rw [voronoiList, hset]
    have h4 : ([u0, u1, w1, w2] : List V3).length = 4 := rfl
    omega
/-- HOL `RAD_PI_IMP_WEDGE4`: an angle under `pi` with radius `< sqrt 2`
forces a 4-cell in the wedge.  2026-10-13 收官波转真（探针车道 P4rpi 全程
验证后移植）：非共面支 = 维数夹逼（`Coplanar` 第 4 点入 `{u0,u1,w1}` 平面向量
span，`azim_frame_spec` 极坐标 + `Real.sin_eq_zero_iff` + 值域夹逼收口
azim ∈ {0,π}）；楔包含支 = `CONVEX_HULL_4_SUBSET_AFF_GE_2_2` + `affGe` 2-2 ⊆
`wedgeGe`（LocalAuto5 `WEDGE_GE_EQ_AFF_GE` ⊆ 方向的本件移植，mirror-of-
LocalAuto5）；barV 支 = `leaf V [u0,u1,f i]` 的 `barV V 2` 子表 + 四元表
voronoi 面 = 外心单点（`CIRCUMCENTER_IN_VORONOI_SET` + 正交唯一性 +
`affDim` 单点收口）；零测 = `ZWVCBMN`；edgeX = `BumpP4.MCELL4_EDGE`。 -/

theorem RAD_PI_IMP_WEDGE4 (V : Set V3) (f : ℕ → V3) (w0 : V3) (n : ℕ) (i : ℕ)
    (u0 u1 : V3) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hnc : ¬ Collinear3 u0 u1 w0) (hr : leaf_rank V [u0, u1] w0 n f)
    (hapi : azim u0 u1 (f i) (f (i + 1)) < Real.pi)
    (hrad : radV {u0, u1, f i, f (i + 1)} < Real.sqrt 2) :
    ∃ ul, mcell4 V ul ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧ barV V 3 ul ∧
      {u0, u1} ∈ edgeX V (mcell4 V ul) := by
  -- 基础叶事实
  have hli : leaf V [u0, u1, f i] := LEAF_RANK_LEAF V u0 u1 w0 n f i hr
  have hlip : leaf V [u0, u1, f (i + 1)] := LEAF_RANK_LEAF V u0 u1 w0 n f (i + 1) hr
  have hcolA : ¬ Collinear3 u0 u1 (f i) := (LEAF_DOMAIN V [u0, u1, f i] hs hp hli).1
  have hcolB : ¬ Collinear3 u0 u1 (f (i + 1)) :=
    (LEAF_DOMAIN V [u0, u1, f (i + 1)] hs hp hlip).1
  have hu0u1 : u0 ≠ u1 := fun he => hnc (collinear3_of_eq he.symm)
  have hA : ¬ (azim u0 u1 (f i) (f (i + 1)) = 0) :=
    LEAF_RANK_AZIM_NZ V [u0, u1] w0 n f i hs hp hr hn hnc
  have hposA : 0 < azim u0 u1 (f i) (f (i + 1)) :=
    lt_of_le_of_ne (azim_nonneg u0 u1 (f i) (f (i + 1))) (Ne.symm hA)
  have hw1v0 : f i ≠ u0 := fun he => hcolA (collinear3_pair_left he)
  have hw1v1 : f i ≠ u1 := fun he => hcolA (collinear3_pair_right he)
  have hw2v0 : f (i + 1) ≠ u0 := fun he => hcolB (collinear3_pair_left he)
  have hw2v1 : f (i + 1) ≠ u1 := fun he => hcolB (collinear3_pair_right he)
  -- 第 1 步：非共面（共面 ⇒ azim ∈ {0, π}，撞 hA / hapi）
  have hncop : ¬ Coplanar ({u0, u1, f i, f (i + 1)} : Set V3) := by
    intro hcop
    obtain ⟨β, γ, hcombo⟩ := p25rpi_coplanar_combo hcolA hcop
    rcases p25rpi_azim_0_or_pi_of_combo hcolA hcolB hu0u1 ⟨β, γ, hcombo⟩ with h0 | hπ
    · exact hA h0
    · rw [hπ] at hapi
      exact lt_irrefl Real.pi hapi
  -- 第 2 步：barV V 3 四元表
  have hw2V : f (i + 1) ∈ V := by
    have hmem := hlip.1.2 [u0, u1, f (i + 1)] ⟨⟨[], rfl⟩, by simp⟩
    exact hmem.2.1 (by simp [setOfList])
  have hbar : barV V 3 [u0, u1, f i, f (i + 1)] :=
    p25rpi_barV3_of_ncop V hp u0 u1 (f i) (f (i + 1)) hli hw2V hncop hrad
  -- 第 3 步：mcell4 非零测（ZWVCBMN）
  have hset4 : setOfList [u0, u1, f i, f (i + 1)] = ({u0, u1, f i, f (i + 1)} : Set V3) := by
    ext x
    simp [setOfList]
  have hlt : hl [u0, u1, f i, f (i + 1)] < Real.sqrt 2 := by
    show radV (setOfList [u0, u1, f i, f (i + 1)]) < Real.sqrt 2
    rw [hset4]
    exact hrad
  have hnn : ¬ nullSet (mcell4 V [u0, u1, f i, f (i + 1)]) := by
    intro h0
    rw [mcell4, if_pos hlt, hset4] at h0
    exact absurd h0 (ne_of_gt (ZWVCBMN u0 u1 (f i) (f (i + 1)) hncop))
  refine ⟨[u0, u1, f i, f (i + 1)], ?_, hbar, ?_⟩
  · -- 第 4 步：楔包含（MCELL4_CONVEX_HULL + CONVEX_HULL_4_SUBSET + Kit A4）
    have hhull := MCELL4_CONVEX_HULL V [u0, u1, f i, f (i + 1)] hp hs hbar hnn
    rw [hhull]
    have helV : ({elV [u0, u1, f i, f (i + 1)] 0, elV [u0, u1, f i, f (i + 1)] 1,
        elV [u0, u1, f i, f (i + 1)] 2, elV [u0, u1, f i, f (i + 1)] 3} : Set V3)
        = ({u0, u1, f i, f (i + 1)} : Set V3) := by
      ext x
      simp [elV]
    rw [helV]
    exact (CONVEX_HULL_4_SUBSET_AFF_GE_2_2 u0 u1 (f i) (f (i + 1))).trans
      (p25rpi_affGe22_subset_wedgeGe u0 u1 (f i) (f (i + 1)) hcolA hcolB hposA hapi)
  · -- 第 5 步：edgeX（MCELL4_EDGE）
    rw [BumpP4.MCELL4_EDGE V [u0, u1, f i, f (i + 1)] u0 u1 hp hs hnn hbar]
    refine ⟨hu0u1, ?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact by simp [setOfList]
    · exact by simp [setOfList]


/-! ### critical_weight_wtcount6_y 装配（CARD_INSERT_INTER 六步剥离） -/


/-- HOL `LEAF_RANK_SUC_INJ`. -/
theorem LEAF_RANK_SUC_INJ (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) : f i ≠ f (i + 1) := by
  intro heq
  have hper : periodic f n := LEAF_RANK_PERIODIC V [u0, u1] w0 n f hr
  have h1 : f i = f (i % n) := (p25_f_mod hper i).symm
  have h2 : f (i + 1) = f ((i + 1) % n) := (p25_f_mod hper (i + 1)).symm
  have h3 : i % n < n := Nat.mod_lt i (by omega)
  have h4 : (i + 1) % n < n := Nat.mod_lt _ (by omega)
  rcases lt_trichotomy (i % n) ((i + 1) % n) with hlt | heq' | hgt
  · have hord := hr.2.2 _ _ h3 h4 hlt
    rw [← h2, ← h1, heq] at hord
    linarith
  · exact absurd heq' (MOD_INJ1_ALT_p25 (by omega) (by omega) (by omega) i)
  · have hord := hr.2.2 _ _ h4 h3 hgt
    rw [← h1, ← h2, heq] at hord
    linarith

/-- HOL `DIST_I_SUCI`.  Proof: consecutive leaves are packing points
(`leaf` carries `setOfList ⊆ V`) and distinct (`LEAF_RANK_SUC_INJ`), so the
packing separation gives the bound. -/
theorem DIST_I_SUCI (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hnc : ¬ Collinear3 u0 u1 w0) (hr : leaf_rank V [u0, u1] w0 n f) :
    2 ≤ dist (f i) (f (i + 1)) := by
  have hmem : ∀ k : ℕ, f k ∈ V := by
    intro k
    have hz : f k ∈ s_leaf V [u0, u1] := by
      have h1 : f k ∈ f '' (univ : Set ℕ) := ⟨k, Set.mem_univ _, rfl⟩
      exact hr.1 ▸ h1
    have hpre := hz.1.1.2 [u0, u1, f k] ⟨⟨[], rfl⟩, by simp⟩
    exact hpre.2.1 (by simp [setOfList])
  have hne := LEAF_RANK_SUC_INJ V u0 u1 w0 n f i hp hs hr hnc hn
  exact hp.dist_ge_two (hmem i) (hmem (i + 1)) hne

/-! ### 楔形 3-cell 面 2026-10-13 波：`dihY` 第 4 槽单调 kit（真证，自含）

HOL `Tame_inequalities.DIH_X_MONO_LT_4`（WEDGE3_Y4 的 dih 支核心）与
`dih_y_mono`（CUXVZOZ.hl:3206）的本文件解析版。路线：`atn2` 右半平面分支
消解（Mathlib `arctan_inv_of_pos`/`arctan_inv_of_neg`）把 `dih_x` 化为
`π/2 + arctan(-P/√(4·x1·Δ))` 的比值比较；比值单调由二次型 `delta_x` 与
仿射 `delta_x4` 的判别式不变量 `P^2 + 4*x1*Δ = const`（纯 `ring`）与中点
恒等式 `2*(Δ'-Δ) = (P+P')*(x4'-x4)` 纯代数收口，无需微积分。 -/

/-- 楔形 kit：`atn2` 右半平面分支消解。 -/
private theorem p25w_atn2_eq_arctan {A B : ℝ} (hA : 0 < A) :
    atn2 A B = Real.arctan (B / A) := by
  unfold atn2
  split_ifs with hb hb2 hb3
  · rfl
  · have hBA : 0 < B / A := div_pos hb2 hA
    have hrec : A / B = (B / A)⁻¹ := by field_simp
    rw [hrec, Real.arctan_inv_of_pos hBA]
    ring
  · have hBA : B / A < 0 := div_neg_of_neg_of_pos hb3 hA
    have hrec : A / B = (B / A)⁻¹ := by field_simp
    rw [hrec, Real.arctan_inv_of_neg hBA]
    ring
  · have hB : B = 0 := le_antisymm (not_lt.mp hb2) (not_lt.mp hb3)
    have hle : A ≤ |B| := le_of_not_gt hb
    rw [hB, abs_zero] at hle
    linarith

/-- 楔形 kit：`delta_x` 的两点判别式不变量（`P^2 + 4*x1*Δ` 与第 4 槽无关）。 -/
private theorem p25w_delta_inv (x1 x2 x3 x4 x4' x5 x6 : ℝ) :
    (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2 + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6
      = (deltaX4 x1 x2 x3 x4' x5 x6) ^ 2 + 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 := by
  simp only [deltaX, deltaX4]
  ring

/-- 楔形 kit：`delta_x4` 沿第 4 槽的仿射差（斜率 `-2*x1`）。 -/
private theorem p25w_dX4_sub (x1 x2 x3 x4 x4' x5 x6 : ℝ) :
    deltaX4 x1 x2 x3 x4' x5 x6
      = deltaX4 x1 x2 x3 x4 x5 x6 - 2 * x1 * (x4' - x4) := by
  simp only [deltaX4]
  ring

/-- 楔形 kit：`delta_x` 的两点中点恒等式。 -/
private theorem p25w_dX_mid (x1 x2 x3 x4 x4' x5 x6 : ℝ) :
    2 * (deltaX x1 x2 x3 x4' x5 x6 - deltaX x1 x2 x3 x4 x5 x6)
      = (deltaX4 x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4' x5 x6) * (x4' - x4) := by
  simp only [deltaX, deltaX4]
  ring

/-- 楔形 kit：`-delta_x4 / sqrt(4*x1*delta_x)` 沿第 4 槽的比值比较
（判别式不变量消平方，正分子支 `abs_le_of_sq_le_sq'` 收口）。 -/
private theorem p25w_ratio_le {x1 x2 x3 x4 x4' x5 x6 : ℝ} (hx1 : 0 < x1)
    (h44 : x4 ≤ x4') (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hd' : 0 < deltaX x1 x2 x3 x4' x5 x6) :
    -(deltaX4 x1 x2 x3 x4 x5 x6) / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
      ≤ -(deltaX4 x1 x2 x3 x4' x5 x6)
          / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) := by
  have h4 : (0:ℝ) < 4 := by norm_num
  have hdec : deltaX4 x1 x2 x3 x4' x5 x6 ≤ deltaX4 x1 x2 x3 x4 x5 x6 := by
    have h2 := p25w_dX4_sub x1 x2 x3 x4 x4' x5 x6
    have hprod : 0 ≤ 2 * x1 * (x4' - x4) :=
      mul_nonneg (mul_nonneg zero_le_two hx1.le) (sub_nonneg.mpr h44)
    linarith
  have hmid := p25w_dX_mid x1 x2 x3 x4 x4' x5 x6
  have hs0p : 0 ≤ 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 :=
    le_of_lt (mul_pos (mul_pos h4 hx1) hd)
  have hs1p : 0 ≤ 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 :=
    le_of_lt (mul_pos (mul_pos h4 hx1) hd')
  have hs0lt : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 :=
    mul_pos (mul_pos h4 hx1) hd
  have hs1lt : 0 < 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 :=
    mul_pos (mul_pos h4 hx1) hd'
  have hs0 : 0 ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := Real.sqrt_nonneg _
  have hs1 : 0 ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) := Real.sqrt_nonneg _
  rcases le_or_gt 0 (deltaX4 x1 x2 x3 x4' x5 x6) with hP1 | hP1
  · -- both P ≥ 0: delta increases along the slot, negative numerators compare
    have hP0 : 0 ≤ deltaX4 x1 x2 x3 x4 x5 x6 := hP1.trans hdec
    have hDle : deltaX x1 x2 x3 x4 x5 x6 ≤ deltaX x1 x2 x3 x4' x5 x6 := by
      nlinarith [hmid, hP0, hP1, h44]
    have hsq : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
        ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) :=
      Real.sqrt_le_sqrt (by nlinarith [hDle, hx1.le])
    have hnp0 : -(deltaX4 x1 x2 x3 x4 x5 x6) ≤ -(deltaX4 x1 x2 x3 x4' x5 x6) := by linarith
    have hnp1 : -(deltaX4 x1 x2 x3 x4' x5 x6) ≤ 0 := by linarith
    refine le_trans ((div_le_div_iff₀ (Real.sqrt_pos.mpr hs0lt)
      (Real.sqrt_pos.mpr hs0lt)).mpr
      (mul_le_mul_of_nonneg_right hnp0 (Real.sqrt_nonneg _)))
      ((div_le_div_iff₀ (Real.sqrt_pos.mpr hs0lt) (Real.sqrt_pos.mpr hs1lt)).mpr
        (mul_le_mul_of_nonpos_left hsq hnp1))
  · rcases le_or_gt 0 (deltaX4 x1 x2 x3 x4 x5 x6) with hP0 | hP0
    · -- P1 < 0 ≤ P0: left side nonpositive, right side positive
      have hL : -(deltaX4 x1 x2 x3 x4 x5 x6)
            / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≤ 0 :=
        (div_nonpos_iff).mpr (Or.inr ⟨by linarith, hs0⟩)
      have hR : 0 ≤ -(deltaX4 x1 x2 x3 x4' x5 x6)
            / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) :=
        (div_nonneg_iff).mpr (Or.inl ⟨by linarith, hs1⟩)
      linarith
    · -- both numerators positive: compare squares via the discriminant invariant
      have hnp0 : 0 < -(deltaX4 x1 x2 x3 x4 x5 x6) := by linarith
      have hnp1 : 0 < -(deltaX4 x1 x2 x3 x4' x5 x6) := by linarith
      have hDle : deltaX x1 x2 x3 x4' x5 x6 ≤ deltaX x1 x2 x3 x4 x5 x6 := by
        nlinarith [hmid, hdec, hP0, h44]
      have hcert : (deltaX x1 x2 x3 x4' x5 x6 - deltaX x1 x2 x3 x4 x5 x6)
          * ((deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
              + 4 * x1 * deltaX x1 x2 x3 x4' x5 x6) * (4 * x1) ≤ 0 := by
        have hbase : 0 ≤ 4 * x1 := by linarith
        have hdiff : deltaX x1 x2 x3 x4' x5 x6 - deltaX x1 x2 x3 x4 x5 x6 ≤ 0 := by
          nlinarith [hmid, hdec, hP0, h44]
        have hpos : 0 ≤ (deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
            + 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 := by nlinarith
        have hp1 : (deltaX x1 x2 x3 x4' x5 x6 - deltaX x1 x2 x3 x4 x5 x6)
            * ((deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
                + 4 * x1 * deltaX x1 x2 x3 x4' x5 x6) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hdiff hpos
        exact mul_nonpos_of_nonpos_of_nonneg hp1 hbase
      have heq : (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2
            * (4 * x1 * deltaX x1 x2 x3 x4' x5 x6)
          = (deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
              * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            + (deltaX x1 x2 x3 x4' x5 x6 - deltaX x1 x2 x3 x4 x5 x6)
              * ((deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
                  + 4 * x1 * deltaX x1 x2 x3 x4' x5 x6) * (4 * x1) := by
        linear_combination (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) *
          p25w_delta_inv x1 x2 x3 x4 x4' x5 x6
      have hsqnum : (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2
            * (4 * x1 * deltaX x1 x2 x3 x4' x5 x6)
          ≤ (deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
              * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by linarith
      have hsq0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 2
          = 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := Real.sq_sqrt hs0p
      have hsq1 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) ^ 2
          = 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 := Real.sq_sqrt hs1p
      have hA2 : (-(deltaX4 x1 x2 x3 x4 x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) ^ 2
          ≤ (-(deltaX4 x1 x2 x3 x4' x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6)) ^ 2 := by
        have h1 : (-(deltaX4 x1 x2 x3 x4 x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) ^ 2
            = (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2
                / (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
          rw [div_pow, neg_sq, hsq0]
        have h2 : (-(deltaX4 x1 x2 x3 x4' x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6)) ^ 2
            = (deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
                / (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) := by
          rw [div_pow, neg_sq, hsq1]
        rw [h1, h2]
        exact (div_le_div_iff₀ hs0lt hs1lt).mpr hsqnum
      exact (abs_le_of_sq_le_sq' hA2
        (le_of_lt (div_pos hnp1 (Real.sqrt_pos.mpr hs1lt)))).2

/-- 楔形 kit 主件：`dih_x` 沿第 4 槽单调（起点 `delta_x > 0`，终点 `≥ 0`；
终点退化时右侧值只增不减，`delta_x4 > 0` 支由中点恒等式排除）。 -/
private theorem p25w_dihXf_mono_x4 {x1 x2 x3 x4 x4' x5 x6 : ℝ} (hx1 : 0 < x1)
    (h44 : x4 ≤ x4') (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hd' : 0 ≤ deltaX x1 x2 x3 x4' x5 x6) :
    dihXf x1 x2 x3 x4 x5 x6 ≤ dihXf x1 x2 x3 x4' x5 x6 := by
  have h4 : (0:ℝ) < 4 := by norm_num
  have hs0 : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 :=
    mul_pos (mul_pos h4 hx1) hd
  unfold dihXf
  rcases lt_or_ge 0 (deltaX x1 x2 x3 x4' x5 x6) with hD1 | hD1
  · have hs1 : 0 < 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 :=
      mul_pos (mul_pos h4 hx1) hD1
    rw [p25w_atn2_eq_arctan (A := Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
        (B := -(deltaX4 x1 x2 x3 x4 x5 x6)) (Real.sqrt_pos.mpr hs0),
      p25w_atn2_eq_arctan (A := Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6))
        (B := -(deltaX4 x1 x2 x3 x4' x5 x6)) (Real.sqrt_pos.mpr hs1)]
    linarith [Real.arctan_le_arctan_iff.mpr (p25w_ratio_le hx1 h44 hd hD1)]
  · -- degenerate right endpoint: sqrt = 0, atn2 value only grows
    have hP1le : deltaX4 x1 x2 x3 x4' x5 x6 ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have h2 := p25w_dX4_sub x1 x2 x3 x4 x4' x5 x6
      have hprod : 0 ≤ 2 * x1 * (x4' - x4) :=
        mul_nonneg (mul_nonneg zero_le_two hx1.le) (sub_nonneg.mpr h44)
      have hP0pos : 0 < deltaX4 x1 x2 x3 x4 x5 x6 := by linarith
      have hsum : 0 < deltaX4 x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4' x5 x6 := by
        linarith
      have hprod2 : 0 ≤ (deltaX4 x1 x2 x3 x4 x5 x6
            + deltaX4 x1 x2 x3 x4' x5 x6) * (x4' - x4) :=
        mul_nonneg (le_of_lt hsum) (sub_nonneg.mpr h44)
      have hm := p25w_dX_mid x1 x2 x3 x4 x4' x5 x6
      linarith [hm, hprod2, hd]
    have hz : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (by nlinarith [hD1, hx1.le])
    rw [hz, p25w_atn2_eq_arctan (A := Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
        (B := -(deltaX4 x1 x2 x3 x4 x5 x6)) (Real.sqrt_pos.mpr hs0)]
    have hArcL : Real.arctan (-(deltaX4 x1 x2 x3 x4 x5 x6)
        / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) ≤ Real.pi / 2 :=
      (Real.arctan_lt_pi_div_two _).le
    unfold atn2
    split_ifs with hb1 hb2 hb3
    · linarith [abs_nonneg (-(deltaX4 x1 x2 x3 x4' x5 x6)), hArcL]
    · simp only [zero_div, Real.arctan_zero]
      linarith [hArcL]
    · linarith
    · linarith [Real.pi_pos, hArcL]

/-- 楔形 kit：`dih_y` 沿第 4 槽单调（y 空间版，即 HOL `dih_y_mono`）。 -/
private theorem p25w_dihY_mono_y4 {y1 y2 y3 y4 y4' y5 y6 : ℝ} (hy1 : 0 < y1)
    (hy4 : 0 ≤ y4) (h44 : y4 ≤ y4') (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hd' : 0 ≤ deltaY y1 y2 y3 y4' y5 y6) :
    dihY y1 y2 y3 y4 y5 y6 ≤ dihY y1 y2 y3 y4' y5 y6 := by
  show dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ≤
    dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4' * y4') (y5 * y5) (y6 * y6)
  refine p25w_dihXf_mono_x4 (mul_pos hy1 hy1) ?_ hd hd'
  have hstep1 : y4 * y4 ≤ y4' * y4 := mul_le_mul_of_nonneg_right h44 hy4
  have hstep2 : y4' * y4 ≤ y4' * y4' := by
    refine mul_le_mul_of_nonneg_left h44 ?_
    linarith
  linarith

/-- HOL `EDGE_LE_2RAD`. -/
theorem EDGE_LE_2RAD {x1 x2 x3 x4 x5 x6 : ℝ} (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (h4 : 0 < x4) (h5 : 0 < x5) (h6 : 0 < x6) (hup : 0 < upsX x4 x5 x6) :
    x4 ≤ 4 * rad2XP25 x1 x2 x3 x4 x5 x6 := by
  -- RHUFIIB 型恒等式（leg/collect_geom2.hl:1510）：rho·ups = chi² + 4·delta·x4x5x6
  have hchi0 : (x4 * x5 * x6) * (4 * deltaX x1 x2 x3 x4 x5 x6)
      ≤ upsX x4 x5 x6 * rhoX x1 x2 x3 x4 x5 x6 := by
    have hid : rhoX x1 x2 x3 x4 x5 x6 * upsX x4 x5 x6
        = (-x1*x4*x4 + x1*x4*x5 + x2*x4*x5 - x2*x5*x5 + x1*x4*x6 + x3*x4*x6
            + x2*x5*x6 + x3*x5*x6 - 2*x4*x5*x6 - x3*x6*x6) ^ 2
          + 4 * deltaX x1 x2 x3 x4 x5 x6 * (x4 * x5 * x6) := by
      simp only [rhoX, deltaX, upsX]
      ring
    have hcomm : 4 * deltaX x1 x2 x3 x4 x5 x6 * (x4 * x5 * x6)
        = (x4 * x5 * x6) * (4 * deltaX x1 x2 x3 x4 x5 x6) := by ring
    have hsq := sq_nonneg ((-x1*x4*x4 + x1*x4*x5 + x2*x4*x5 - x2*x5*x5 + x1*x4*x6
      + x3*x4*x6 + x2*x5*x6 + x3*x5*x6 - 2*x4*x5*x6 - x3*x6*x6 : ℝ))
    linarith
  -- 面半弦：4x5x6 − ups = (x5+x6−x4)² ≥ 0
  have hface : upsX x4 x5 x6 ≤ 4 * x5 * x6 := by
    have h : 4 * x5 * x6 - upsX x4 x5 x6 = (x5 + x6 - x4) ^ 2 := by
      simp only [upsX]
      ring
    have hsq := sq_nonneg ((x5 + x6 - x4 : ℝ))
    linarith
  have hchord : x4 * upsX x4 x5 x6 ≤ 4 * x4 * x5 * x6 := by
    calc x4 * upsX x4 x5 x6 ≤ x4 * (4 * x5 * x6) :=
          mul_le_mul_of_nonneg_left hface (le_of_lt h4)
      _ = 4 * x4 * x5 * x6 := by ring
  have hchord' : x4 ≤ 4 * x4 * x5 * x6 / upsX x4 x5 x6 :=
    (le_div_iff₀ hup).mpr hchord
  have hd0 : 0 < 4 * deltaX x1 x2 x3 x4 x5 x6 := by linarith
  have heta : x4 * x5 * x6 / upsX x4 x5 x6
      ≤ rhoX x1 x2 x3 x4 x5 x6 / (4 * deltaX x1 x2 x3 x4 x5 x6) := by
    rw [div_le_div_iff₀ hup hd0]
    linarith [hchi0]
  calc x4 ≤ 4 * x4 * x5 * x6 / upsX x4 x5 x6 := hchord'
    _ = 4 * (x4 * x5 * x6 / upsX x4 x5 x6) := by ring
    _ ≤ 4 * (rhoX x1 x2 x3 x4 x5 x6 / (4 * deltaX x1 x2 x3 x4 x5 x6)) :=
          mul_le_mul_of_nonneg_left heta (by norm_num)
    _ = 4 * rad2XP25 x1 x2 x3 x4 x5 x6 := by
          simp only [rad2XP25, rad2X]
          field_simp

/-- HOL `RAD2_Y_SQRT8`. -/
theorem RAD2_Y_SQRT8 {y1 y2 y3 y5 y6 : ℝ} (h5 : 2 ≤ y5) (h6 : 2 ≤ y6)
    (h5' : y5 < 4) (h6' : y6 < 4)
    (hd : 0 < deltaY y1 y2 y3 (Real.sqrt 8) y5 y6) :
    2 ≤ rad2YP25 y1 y2 y3 (Real.sqrt 8) y5 y6 := by
  have hs8 : (Real.sqrt 8) * (Real.sqrt 8) = 8 :=
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)
  have hd' : 0 < deltaX (y1 * y1) (y2 * y2) (y3 * y3) 8 (y5 * y5) (y6 * y6) := by
    have h : 0 < deltaY y1 y2 y3 (Real.sqrt 8) y5 y6 := hd
    rw [deltaY, hs8] at h
    exact h
  have hr : rad2YP25 y1 y2 y3 (Real.sqrt 8) y5 y6
      = rad2XP25 (y1 * y1) (y2 * y2) (y3 * y3) 8 (y5 * y5) (y6 * y6) := by
    rw [rad2YP25, hs8]
  rw [hr]
  have h8 : (0:ℝ) < 8 := by norm_num
  have e := EDGE_LE_2RAD hd' h8 (by positivity) (by positivity)
    (UPS_X8_POS h5 h5' h6 h6')
  linarith

set_option maxHeartbeats 10000000 in
/-- HOL `WEDGE3_Y4`: a 3-cell wedge yields the analytic `y4` certificate.
楔形 3-cell 面 2026-10-13 波转真（装配级）：三分 witness 对照 HOL
OXLZLEZ3.hl:4388。`pi ≤ azim` 与 `2√2 < d` 两枝取 `√8`：delta 支 =
`proj_bank_FWGKMBZ` 投影（盒 `[2hmin,2hplus]×[2,√8]⁵`），dih 支 =
`p25w_dihY_mono_y4`（`delta_y(d) ≥ 0` 由 `DELTA_Y_POS_4POINTS` 无条件给出）
+ `DIHV_EQ_DIH_Y_4PT_B` + `DIHV_LE_AZIM`，rad2 支 = `RAD2_Y_SQRT8`（解析，
r5 波）；末枝（`azim < pi ∧ d ≤ 2√2`）取 `d` 本身，rad2 ≥ 2 经
`coplanar_delta_y`（delta > 0 ⟹ ¬共面）+ `GDRQXLGv3`（radV² 桥）+
`RAD_PI_IMP_WEDGE4` 反证撞 `hno4`——与 HOL 同构，债面即 `RAD_PI_IMP_WEDGE4`
（本文件在案 sorried 兄弟）。本地预算：单件声明级心跳扩容（照 GDRQXLGv3
先例）。 -/
theorem WEDGE3_Y4 (V : Set V3) (f : ℕ → V3) (w0 : V3) (n : ℕ) (i : ℕ) (u0 u1 : V3)
    (y1 y2 y3 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n)
    (hp : Packing V) (hs : saturated V) (hnc : ¬ Collinear3 u0 u1 w0)
    (hr : leaf_rank V [u0, u1] w0 n f) (hcey : criticalEdgeY (dist u0 u1))
    (hno4 : ¬ ∃ vl, barV V 3 vl ∧ {u0, u1} ∈ edgeX V (mcell4 V vl) ∧
      mcell4 V vl ⊆ wedgeGe u0 u1 (f i) (f (i + 1)))
    (hy1 : y1 = dist u0 u1) (hy2 : y2 = dist u0 (f i))
    (hy3 : y3 = dist u0 (f (i + 1))) (hy5 : y5 = dist u1 (f (i + 1)))
    (hy6 : y6 = dist u1 (f i)) :
    ∃ y4, 2 ≤ y4 ∧ y4 ≤ 2 * Real.sqrt 2 ∧
      0 < deltaY y1 y2 y3 y4 y5 y6 ∧
      dihY y1 y2 y3 y4 y5 y6 ≤ azim u0 u1 (f i) (f (i + 1)) ∧
      2 ≤ rad2YP25 y1 y2 y3 y4 y5 y6 ∧
      (azim u0 u1 (f i) (f (i + 1)) < Real.pi →
        dist (f i) (f (i + 1)) ≤ 2 * Real.sqrt 2 → y4 = dist (f i) (f (i + 1))) := by
  obtain rfl := hy1
  obtain rfl := hy2
  obtain rfl := hy3
  obtain rfl := hy5
  obtain rfl := hy6
  -- leaves and their box facts
  have hleafA : leaf V [u0, u1, f i] := by
    have hmem := LEAF_RANK_S_LEAF V [u0, u1] w0 n f i hr
    simp only [s_leaf, Set.mem_setOf_eq] at hmem
    exact hmem.1
  have hleafB : leaf V [u0, u1, f (i + 1)] := by
    have hmem := LEAF_RANK_S_LEAF V [u0, u1] w0 n f (i + 1) hr
    simp only [s_leaf, Set.mem_setOf_eq] at hmem
    exact hmem.1
  obtain ⟨hcolA, h2_6, h2_2, h2_1, lt6, lt2, -, -⟩ :=
    LEAF_DOMAIN V [u0, u1, f i] hs hp hleafA
  obtain ⟨hcolB, h2_5, h2_3, -, lt5, lt3, -, -⟩ :=
    LEAF_DOMAIN V [u0, u1, f (i + 1)] hs hp hleafB
  have eV0 : ∀ (p q r : V3), elV [p, q, r] 0 = p := fun _ _ _ => rfl
  have eV1 : ∀ (p q r : V3), elV [p, q, r] 1 = q := fun _ _ _ => rfl
  have eV2 : ∀ (p q r : V3), elV [p, q, r] 2 = r := fun _ _ _ => rfl
  simp only [eV0, eV1, eV2] at hcolA hcolB h2_6 h2_2 h2_1 lt6 lt2 h2_5 h2_3 lt5 lt3
  -- distinctness
  have hu0u1 : u0 ≠ u1 := by
    intro he
    refine hcolA ?_
    show Collinear ℝ ({u0, u1, f i} : Set V3)
    have hs' : ({u0, u1, f i} : Set V3) = ({u1, f i} : Set V3) := by
      rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hs']; exact collinear_pair _ u1 (f i)
  have hu0i : u0 ≠ f i := by
    intro he
    refine hcolA ?_
    show Collinear ℝ ({u0, u1, f i} : Set V3)
    have hs' : ({f i, u1, f i} : Set V3) = ({u1, f i} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [he]; rw [hs']; exact collinear_pair _ u1 (f i)
  have hu1i : u1 ≠ f i := by
    intro he
    refine hcolA ?_
    show Collinear ℝ ({u0, u1, f i} : Set V3)
    have hs' : ({u0, f i, f i} : Set V3) = ({u0, f i} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [he]; rw [hs']; exact collinear_pair _ u0 (f i)
  have hu0s : u0 ≠ f (i + 1) := by
    intro he
    refine hcolB ?_
    show Collinear ℝ ({u0, u1, f (i + 1)} : Set V3)
    have hs' : ({f (i + 1), u1, f (i + 1)} : Set V3) = ({u1, f (i + 1)} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [he]; rw [hs']; exact collinear_pair _ u1 (f (i + 1))
  have hu1s : u1 ≠ f (i + 1) := by
    intro he
    refine hcolB ?_
    show Collinear ℝ ({u0, u1, f (i + 1)} : Set V3)
    have hs' : ({u0, f (i + 1), f (i + 1)} : Set V3) = ({u0, f (i + 1)} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [he]; rw [hs']; exact collinear_pair _ u0 (f (i + 1))
  -- the successor edge and the sqrt-8 bridge
  have hdsuc : 2 ≤ dist (f i) (f (i + 1)) :=
    DIST_I_SUCI V u0 u1 w0 n f i hnl hn hp hs hnc hr
  have hs8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    have h42 : (8:ℝ) = 4 * 2 := by norm_num
    have hge : (0:ℝ) ≤ 4 := by norm_num
    rw [h42, Real.sqrt_mul hge]
    norm_num
  have hone : (1:ℝ) ≤ Real.sqrt 2 :=
    (Real.le_sqrt (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 2 by norm_num)).mpr
      (by norm_num)
  have h28 : (2:ℝ) ≤ Real.sqrt 8 := by rw [hs8]; linarith [hone]
  have hsq2lt4 : (2:ℝ) * Real.sqrt 2 < 4 := by
    have h22 : Real.sqrt 2 < 2 :=
      lt_of_lt_of_eq (Real.sqrt_lt_sqrt (show (0:ℝ) ≤ 2 by norm_num)
        (show (2:ℝ) < 4 by norm_num)) (by norm_num)
    linarith
  -- FWGKMBZ bank projection: delta_y > 0 on the box
  have hbank := proj_bank_FWGKMBZ hnl
  have hd8 : ∀ z : ℝ, 2 ≤ z → z ≤ Real.sqrt 8 →
      0 < deltaY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1))) z
        (dist u1 (f (i + 1))) (dist u1 (f i)) := by
    intro z hz hz'
    exact hbank _ _ _ _ _ _ hcey.1 hcey.2 h2_2 (by rw [hs8]; exact lt2.le) h2_3
      (by rw [hs8]; exact lt3.le) hz hz' h2_5 (by rw [hs8]; exact lt5.le) h2_6
      (by rw [hs8]; exact lt6.le)
  -- the analytic block shared by the √8 witnesses
  have hrad8 : 2 ≤ rad2YP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
      (Real.sqrt 8) (dist u1 (f (i + 1))) (dist u1 (f i)) :=
    RAD2_Y_SQRT8 h2_5 h2_6 (by linarith [lt5, hsq2lt4]) (by linarith [lt6, hsq2lt4])
      (hd8 _ h28 le_rfl)
  have hdih8lt : dihY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1))) (Real.sqrt 8)
      (dist u1 (f (i + 1))) (dist u1 (f i)) < Real.pi :=
    DIH_Y_LT_PI (by linarith [h2_1]) (hd8 _ h28 le_rfl)
  rcases le_or_gt Real.pi (azim u0 u1 (f i) (f (i + 1))) with hapi | hlt
  · -- case 1: pi <= azim: witness sqrt 8
    refine ⟨Real.sqrt 8, by rw [hs8]; linarith [hone], by rw [hs8], hd8 _ h28 le_rfl,
      le_trans (le_of_lt hdih8lt) hapi, hrad8, ?_⟩
    intro hcon _
    exact absurd hcon (not_lt.mpr hapi)
  · -- azim < pi
    rcases le_or_gt (dist (f i) (f (i + 1))) (2 * Real.sqrt 2) with hle | hbig
    · -- case 3: witness d itself; rad2 via the 4-cell refutation (HOL isomorphic)
      have hd3 := hd8 _ hdsuc (by rw [hs8]; exact hle)
      have hncop := (coplanar_delta_y u0 u1 (f i) (f (i + 1))).mpr hd3
      have haff : ¬ affineDependent ({u0, u1, f i, f (i + 1)} : Set V3) :=
        fun hdep => hncop (p25g_affdep4_coplanar hdep)
      have hnn : 0 ≤ radV ({u0, u1, f i, f (i + 1)} : Set V3) := by
        rw [OAPVION2_concl ({u0, u1, f i, f (i + 1)} : Set V3) haff u0 (by simp)]
        exact dist_nonneg
      refine ⟨dist (f i) (f (i + 1)), hdsuc, hle, hd3, ?_, ?_, ?_⟩
      · calc dihY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
              (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i))
            = dihV u0 u1 (f i) (f (i + 1)) :=
              (DIHV_EQ_DIH_Y_4PT_B u0 u1 (f i) (f (i + 1)) hcolA hcolB).symm
          _ ≤ azim u0 u1 (f i) (f (i + 1)) :=
              DIHV_LE_AZIM u0 u1 (f i) (f (i + 1)) hcolA hcolB
      · by_contra hcon
        push_neg at hcon
        have hG := GDRQXLGv3 u0 u1 (f i) (f (i + 1)) hncop
        have hY1 : rad2YP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
            (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i))
          = rad2XP25 (dist u0 u1 * dist u0 u1) (dist u0 (f i) * dist u0 (f i))
              (dist u0 (f (i + 1)) * dist u0 (f (i + 1)))
              (dist (f i) (f (i + 1)) * dist (f i) (f (i + 1)))
              (dist u1 (f (i + 1)) * dist u1 (f (i + 1)))
              (dist u1 (f i) * dist u1 (f i)) := rfl
        have hY2 : rad2XP25 (dist u0 u1 * dist u0 u1) (dist u0 (f i) * dist u0 (f i))
              (dist u0 (f (i + 1)) * dist u0 (f (i + 1)))
              (dist (f i) (f (i + 1)) * dist (f i) (f (i + 1)))
              (dist u1 (f (i + 1)) * dist u1 (f (i + 1)))
              (dist u1 (f i) * dist u1 (f i))
          = rad2XP25 (dist u0 u1 ^ 2) (dist u0 (f i) ^ 2)
              (dist u0 (f (i + 1)) ^ 2) (dist (f i) (f (i + 1)) ^ 2)
              (dist u1 (f (i + 1)) ^ 2) (dist u1 (f i) ^ 2) := by
          simp only [pow_two]
        have hY := hY1.trans hY2
        rw [hY, ← hG] at hcon
        have hrad : radV ({u0, u1, f i, f (i + 1)} : Set V3) < Real.sqrt 2 :=
          (Real.lt_sqrt hnn).mpr hcon
        obtain ⟨vl, hsub4, hbar4, hedge4⟩ :=
          RAD_PI_IMP_WEDGE4 V f w0 n i u0 u1 hn hp hs hnc hr hlt hrad
        exact hno4 ⟨vl, hbar4, hedge4, hsub4⟩
      · intro _ _
        rfl
    · -- case 2: witness sqrt 8; dihedral via the slot-4 monotonicity kit
      have hmono := p25w_dihY_mono_y4 (by linarith [h2_1]) (Real.sqrt_nonneg 8)
        (by rw [hs8]; exact le_of_lt hbig)
        (hd8 _ h28 le_rfl) (DELTA_Y_POS_4POINTS_B u0 u1 (f i) (f (i + 1)))
      refine ⟨Real.sqrt 8, by rw [hs8]; linarith [hone], by rw [hs8],
        hd8 _ h28 le_rfl, ?_, hrad8, ?_⟩
      · calc dihY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1))) (Real.sqrt 8)
              (dist u1 (f (i + 1))) (dist u1 (f i)) ≤
            dihY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
              (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) := hmono
          _ = dihV u0 u1 (f i) (f (i + 1)) :=
              (DIHV_EQ_DIH_Y_4PT_B u0 u1 (f i) (f (i + 1)) hcolA hcolB).symm
          _ ≤ azim u0 u1 (f i) (f (i + 1)) :=
              DIHV_LE_AZIM u0 u1 (f i) (f (i + 1)) hcolA hcolB
      · intro _ hle2
        linarith

/-- HOL `cc_4_cc_ke4`.  2026-10-13 M4 波转真（装配级）：`MCELL4_EDGE_FIRST`
把楔胞见证改写为茎前置列表，`k = 3` 支经 `STEM_EDGEX`（茎边入胞 edgeX，PA18
真件）+ `K3_CC_WI_ALT`（胞入楔）喂 `MCELL4_FULL_WEDGE` 唯一性得
`ccCell = mcell4`，再以 `AJRIPQN` 的 `4 = 3` 撞死。骨架式预消费：具名记账件
= PA18 `MCELL4_EDGE_FIRST`（E8 车道在攻，随其落地自动升零债）+ 本文件
`K3_CC_WI_ALT`/`MCELL4_FULL_WEDGE`。 -/
theorem cc_4_cc_ke4 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hper : periodic f n) (hn : 1 < n)
    (hl' : leaf V [u0, u1, f i]) (h4 : cc_4 V u0 u1 f i) :
    ccKe V [u0, u1, f i] = 4 := by
  obtain ⟨ul, hbarU, hedge, hwedge⟩ := h4
  obtain ⟨vl, hbarV, hv0, hv1, hswap⟩ :=
    MCELL4_EDGE_FIRST (V := V) (ul := ul) (u := u0) (v := u1) hs hp hbarU hedge
  rcases CC_KE_34 V [u0, u1, f i] with h3 | h4k
  · exfalso
    have hj := F_DEMOD hper hn i
    obtain ⟨he0, he1, -⟩ := EL_CC_UH (V := V) (ul := [u0, u1, f i]) hp hs hl'
    have e0 : (ccUh V [u0, u1, f i]).getD 0 0 = u0 := by rw [he0]; simp
    have e1 : (ccUh V [u0, u1, f i]).getD 1 0 = u1 := by rw [he1]; simp
    have hstem := STEM_EDGEX (V := V) (ul := [u0, u1, f i]) hp hs hl'
    rw [e0, e1] at hstem
    have hd4 : mcell 4 V ul = mcell4 V ul := by simp [mcell]
    have hnnV : ¬ nullSet (mcell4 V vl) := by
      intro hc
      rw [← hswap] at hc
      rw [← hd4, BumpP4.RIJRIED V ul 4 hc] at hedge
      simpa using hedge
    have hrV : leaf_rank V [elV vl 0, elV vl 1] w0 n f := by
      simp only [elV, ← hv0, ← hv1]
      exact hr
    have hncV : ¬ Collinear3 (elV vl 0) (elV vl 1) w0 := by
      simp only [elV, ← hv0, ← hv1]
      exact hnc
    have hjw : mcell4 V vl ⊆ wedgeGe (elV vl 0) (elV vl 1) (f (i % n)) (f (i % n + 1)) := by
      simp only [elV, ← hv0, ← hv1, hj.1, hj.2, ← hswap]
      exact hwedge
    have hk3' : ccCell V [u0, u1, f i] ⊆
        wedgeGe (elV vl 0) (elV vl 1) (f (i % n)) (f (i % n + 1)) := by
      simp only [elV, ← hv0, ← hv1, hj.1, hj.2]
      exact K3_CC_WI_ALT V [u0, u1] w0 n f i hp hs hr hnc hn h3
    have hstem' : ({elV vl 0, elV vl 1} : Set V3) ∈ edgeX V (ccCell V [u0, u1, f i]) := by
      simp only [elV, ← hv0, ← hv1]
      exact hstem
    have huniq := MCELL4_FULL_WEDGE V (ccCell V [u0, u1, f i]) vl w0 n f (i % n) hp hs
      hrV hbarV hncV hn hnnV (CC_CELL_IN_MCELL_SET hs hp hl') hk3' hstem' hjw
    obtain ⟨hbarUh, -, -⟩ := (Classical.choose_spec (cc_uh_exists V [u0, u1, f i])) hp hs hl'
    have hj4 : mcell 4 V vl = mcell4 V vl := by simp [mcell]
    have hj3 : mcell 3 V (ccUh V [u0, u1, f i]) = ccCell V [u0, u1, f i] := by
      rw [ccCell, h3]
    have hvol : ¬ nullSet (mcell 4 V vl ∩ mcell 3 V (ccUh V [u0, u1, f i])) := by
      rw [hj4, hj3, huniq, Set.inter_self]
      exact hnnV
    obtain ⟨heqij, -⟩ := AJRIPQN V vl (ccUh V [u0, u1, f i]) 4 3 hs hp hbarV hbarUh
      (by simp) (by simp) hvol
    exact absurd heqij (by norm_num)
  · exact h4k

/-- HOL `cc_4_cc_cell`: on a 4-cell wedge, `gg_mcell` equals the cc-cell
weight.  2026-10-13 M4 波转真（装配级）：`cc_4_cc_ke4`（本波装配）钉派单值 4，
`MCELL4_GG`（具名记账件，唯一楔胞 gg 塌缩——随楔 kit 落地自动升零债）作用在
`cc_uh` 表上，`EL_CC_UH` 茎钉死 + `mcell4 (cc_uh) = ccCell` 改写。 -/
theorem cc_4_cc_cell (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hper : periodic f n)
    (hl' : leaf V [u0, u1, f i]) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) (h4 : cc_4 V u0 u1 f i) :
    gg_mcell V f u0 u1 i =
      gammaX V (ccCell V [u0, u1, f i]) lmfun *
          criticalWeight V (ccCell V [u0, u1, f i]) +
        betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) := by
  have hk4 := cc_4_cc_ke4 V u0 u1 w0 n f i hp hs hr hnc hper hn hl' h4
  obtain ⟨hbarUh, -, -⟩ := (Classical.choose_spec (cc_uh_exists V [u0, u1, f i])) hp hs hl'
  obtain ⟨he0, he1, -⟩ := EL_CC_UH (V := V) (ul := [u0, u1, f i]) hp hs hl'
  have e0 : (ccUh V [u0, u1, f i]).getD 0 0 = u0 := by rw [he0]; simp
  have e1 : (ccUh V [u0, u1, f i]).getD 1 0 = u1 := by rw [he1]; simp
  have hj4 : mcell 4 V (ccUh V [u0, u1, f i]) = mcell4 V (ccUh V [u0, u1, f i]) := by
    rw [mcell]; simp
  have hmcc : mcell4 V (ccUh V [u0, u1, f i]) = ccCell V [u0, u1, f i] := by
    rw [ccCell, hk4, hj4]
  have hnnU : ¬ nullSet (mcell4 V (ccUh V [u0, u1, f i])) := by
    rw [hmcc]
    exact CC_CELL_NOT_NULLSET hp hs hl'
  have hrU : leaf_rank V [elV (ccUh V [u0, u1, f i]) 0, elV (ccUh V [u0, u1, f i]) 1]
      w0 n f := by
    simp only [elV, e0, e1]
    exact hr
  have hncU : ¬ Collinear3 (elV (ccUh V [u0, u1, f i]) 0)
      (elV (ccUh V [u0, u1, f i]) 1) w0 := by
    simp only [elV, e0, e1]
    exact hnc
  have hwU : mcell4 V (ccUh V [u0, u1, f i]) ⊆
      wedgeGe (elV (ccUh V [u0, u1, f i]) 0) (elV (ccUh V [u0, u1, f i]) 1)
        (f i) (f (i + 1)) := by
    simp only [hmcc, elV, e0, e1]
    exact K4_CC_WI_ALT V [u0, u1] w0 n f i hp hs hr hnc hn hk4
  have hgg := MCELL4_GG V (ccUh V [u0, u1, f i]) w0 n f i hp hs hrU hbarUh hncU hn
    (rfl : mcell4 V (ccUh V [u0, u1, f i]) = mcell4 V (ccUh V [u0, u1, f i])) hnnU hwU
  simp only [elV, e0, e1] at hgg
  rw [hmcc] at hgg
  exact hgg

/-- Helper: `setSum` respects set equality. -/
private theorem p25_setSum_congr {α : Type*} {s t : Set α} {g : α → ℝ} (h : s = t) :
    setSum s g = setSum t g := by
  unfold setSum
  rw [h]

/-- HOL `cc_real_dat_def`: the cc_qx/qy/qu/hassmall classes of
`cc_data_v8` in terms of `cc_4` and distances (definitional). -/
theorem cc_real_dat_def (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) :
    cc_qx_v11 (cc_data_v8 V f u0 u1) =
        (fun i => cc_4 V u0 u1 f i ∧
          ¬ (dist u0 (f i) < 2 * hminus ∧
            dist u1 (f i) < 2 * hminus ∧
            dist u0 (f (i + 1)) < 2 * hminus ∧
            dist u1 (f (i + 1)) < 2 * hminus ∧
            dist (f i) (f (i + 1)) < 2 * hminus)) ∧
      cc_qy_v11 (cc_data_v8 V f u0 u1) = (fun i => ¬ cc_4 V u0 u1 f i) ∧
      cc_qu_v11 (cc_data_v8 V f u0 u1) =
        (fun i => cc_4 V u0 u1 f i ∧
          (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧
          dist u1 (f (i + 1)) < 2 * hminus ∧
          dist (f i) (f (i + 1)) < 2 * hminus) ∧
      cc_hassmall_v11 (cc_data_v8 V f u0 u1) =
        (fun i => (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧
          dist u1 (f (i + 1)) < 2 * hminus) := by
  have h4 : cc_4cell_v11 (cc_data_v8 V f u0 u1) = fun i => cc_4 V u0 u1 f i := rfl
  have hsm : cc_small_v11 (cc_data_v8 V f u0 u1) =
      fun i => (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) := rfl
  have hsc : cc_subcrit_v11 (cc_data_v8 V f u0 u1) =
      fun i => dist (f i) (f (i + 1)) < 2 * hminus := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i
    simp only [cc_qx_v11, cc_qu_v11, cc_hassmall_v11, h4, hsm, hsc]
    apply propext
    tauto
  · funext i
    simp only [cc_qy_v11, h4]
  · funext i
    simp only [cc_qu_v11, cc_hassmall_v11, h4, hsm, hsc]
    apply propext
    tauto
  · funext i
    simp only [cc_hassmall_v11, hsm]

/-- HOL `real_periodic_data`: the wedge sums are `n`-periodic. -/
theorem real_periodic_data (V : Set V3) (u0 u1 : V3) (f : ℕ → V3) (n : ℕ)
    (hper : periodic f n) :
    periodic (azim_mcell V f u0 u1) n ∧ periodic (gg_mcell V f u0 u1) n ∧
      periodic (fun i => gammaX V (ccCell V [u0, u1, f i]) lmfun) n ∧
      periodic (fun i => gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun) n ∧
      periodic (fun i => gammaX V (ccCell V [u0, u1, f i]) lmfun *
        criticalWeight V (ccCell V [u0, u1, f i])) n ∧
      periodic (fun i => gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
        criticalWeight V (ccCell V [u1, u0, f (i + 1)])) n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    unfold azim_mcell
    refine p25_setSum_congr ?_
    refine Set.ext fun X => ?_
    simp only [Set.mem_setOf_eq]
    rw [hper i, show (i + n) + 1 = i + 1 + n from by omega, hper (i + 1)]
  · intro i
    unfold gg_mcell
    refine p25_setSum_congr ?_
    refine Set.ext fun X => ?_
    simp only [Set.mem_setOf_eq]
    rw [hper i, show (i + n) + 1 = i + 1 + n from by omega, hper (i + 1)]
  · intro i
    simp only [hper i]
  · intro i
    simp only [show (i + n) + 1 = i + 1 + n from by omega, hper (i + 1)]
  · intro i
    simp only [hper i]
  · intro i
    simp only [show (i + n) + 1 = i + 1 + n from by omega, hper (i + 1)]

/-- HOL `cc_4_UL`.  2026-10-13 M4 波转真（装配级）：`cc_4_cc_ke4` 钉派单值 4 +
`CC_CELL_WEDGE_MATCH_UH`（楔匹配，具名记账件在案）给 `cc_uh` 第 4 槽 =
`f (i+1)`（另一支 `f i = f (i+1)` 撞 `LEAF_RANK_SUC_INJ`），`LIST_OF_CC_UH` +
`EL_CC_UH` 收口。 -/
theorem cc_4_UL (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) (h4 : cc_4 V u0 u1 f i) :
    ccCell V [u0, u1, f i] = mcell4 V [u0, u1, f i, f (i + 1)] := by
  have hl' : leaf V [u0, u1, f i] := LEAF_RANK_LEAF V u0 u1 w0 n f i hr
  have hper : periodic f n := LEAF_RANK_PERIODIC V [u0, u1] w0 n f hr
  have hk4 := cc_4_cc_ke4 V u0 u1 w0 n f i hp hs hr hnc hper hn hl' h4
  have hw := K4_CC_WI_ALT V [u0, u1] w0 n f i hp hs hr hnc hn hk4
  have he : ({u0, u1} : Set V3) = {elV [u0, u1] 0, elV [u0, u1] 1} := rfl
  have hmatch := CC_CELL_WEDGE_MATCH_UH V [u0, u1, f i] u0 u1 w0 n f i i hp hs hr hnc hn
    he hw hk4
  have hsuc := LEAF_RANK_SUC_INJ V u0 u1 w0 n f i hp hs hr hnc hn
  rcases Set.pair_eq_pair_iff.mp hmatch with ⟨-, h3d⟩ | ⟨hbad, -⟩
  · obtain ⟨he0, he1, he2⟩ := EL_CC_UH (V := V) (ul := [u0, u1, f i]) hp hs hl'
    have e0 : (ccUh V [u0, u1, f i]).getD 0 0 = u0 := by rw [he0]; simp
    have e1 : (ccUh V [u0, u1, f i]).getD 1 0 = u1 := by rw [he1]; simp
    have e2 : (ccUh V [u0, u1, f i]).getD 2 0 = f i := by rw [he2]; simp
    have hd4 : mcell 4 V (ccUh V [u0, u1, f i]) = mcell4 V (ccUh V [u0, u1, f i]) := by
      rw [mcell]; simp
    rw [ccCell, hk4, hd4, LIST_OF_CC_UH hs hp hl', e0, e1, e2, h3d]
  · exact absurd hbad hsuc

/-- HOL `EDGEX_PAIR`. -/
theorem EDGEX_PAIR (V : Set V3) (X : Set V3) (e : Set V3) (he : e ∈ edgeX V X) :
    ∃ u v : V3, e = {u, v} ∧ u ≠ v := by
  obtain ⟨u, v, huv, _, _, huvne⟩ := he
  exact ⟨u, v, huv, huvne⟩

/-- 私件（mcell3 波 2026-10-12）：`voronoiNondg` 长度差矛盾（PA20 `p20k_vn_contra`
的本文件私拷——上游 private 不可见，查重后无公开同件；affDim 恒等式 `omega` 收口，
自含完整证明）。 -/
private theorem p25m_vn_contra {V : Set V3} {ul vm : List V3}
    (h1 : voronoiNondg V ul) (h2 : voronoiNondg V vm)
    (hset : setOfList ul = setOfList vm) (hlen : ul.length = vm.length + 1) : False := by
  have e1 := h1.2.2
  have e2 := h2.2.2
  simp only [voronoiList] at e1 e2
  rw [hset, hlen] at e1
  omega

/-- HOL `MCELL4_EDGE_EXPLICIT`. -/
theorem MCELL4_EDGE_EXPLICIT (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hs : saturated V) (hn : ¬ nullSet (mcell4 V [u0, u1, u2, u3]))
    (hb : barV V 3 [u0, u1, u2, u3]) :
    edgeX V (mcell4 V [u0, u1, u2, u3]) =
      {{u0, u1}, {u0, u2}, {u0, u3}, {u1, u2}, {u1, u3}, {u2, u3}} := by
  -- MCELL3_EDGE_EXPLICIT 的 4 点版：`p25m_vn_contra` 给出六对茎点两两不等，
  -- `HDTFNFZ`+`LEPJBDJ`(k=4) 把 VX 钉死为见证四元组，`edgeX` 十六案鸽笼枚举。
  have hv0 : voronoiNondg V [u0] := hb.2 [u0] ⟨⟨[u1, u2, u3], rfl⟩, by simp⟩
  have hv1 : voronoiNondg V [u0, u1] := hb.2 [u0, u1] ⟨⟨[u2, u3], rfl⟩, by simp⟩
  have hv2 : voronoiNondg V [u0, u1, u2] := hb.2 [u0, u1, u2] ⟨⟨[u3], rfl⟩, by simp⟩
  have hv3 : voronoiNondg V [u0, u1, u2, u3] := hb.2 _ ⟨⟨[], rfl⟩, by simp⟩
  have hdd : u0 ≠ u1 ∧ u0 ≠ u2 ∧ u0 ≠ u3 ∧ u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      refine p25m_vn_contra hv1 hv0 ?_ ?_
      · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
      · simp
    · intro h
      refine p25m_vn_contra hv2 hv1 ?_ ?_
      · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
      · simp
    · intro h
      refine p25m_vn_contra hv3 hv2 ?_ ?_
      · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
      · simp
    · intro h
      refine p25m_vn_contra hv2 hv1 ?_ ?_
      · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
      · simp
    · intro h
      refine p25m_vn_contra hv3 hv2 ?_ ?_
      · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
      · simp
    · intro h
      refine p25m_vn_contra hv3 hv2 ?_ ?_
      · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
      · simp
  have hne : mcell4 V [u0, u1, u2, u3] ≠ ∅ := by
    intro h0
    apply hn
    rw [h0]
    exact measure_empty
  have hVX : VX V (mcell4 V [u0, u1, u2, u3])
      = setOfList (truncateSimplex 3 [u0, u1, u2, u3]) := by
    have h1 : VX V (mcell4 V [u0, u1, u2, u3])
        = V ∩ mcell4 V [u0, u1, u2, u3] :=
      HDTFNFZ (v := u0) (k := 4) hs hp hb rfl hn
    rw [h1, show mcell4 V [u0, u1, u2, u3] = mcell 4 V [u0, u1, u2, u3] from rfl,
      LEPJBDJ V [u0, u1, u2, u3] 4 hs hp hb (by omega) (by omega) hne]
  have htr : setOfList (truncateSimplex 3 [u0, u1, u2, u3])
      = ({u0, u1, u2, u3} : Set V3) := by
    rw [TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 u2 u3]
    ext z
    simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hVX4 : ∀ z : V3, z ∈ VX V (mcell4 V [u0, u1, u2, u3]) ↔
      z ∈ ({u0, u1, u2, u3} : Set V3) := by
    intro z
    rw [hVX, htr]
  have pEq : ∀ (p q : V3), ({p, q} : Set V3) = {q, p} := by
    intro p q
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have key : ∀ p q : V3, p ∈ ({u0, u1, u2, u3} : Set V3) →
      q ∈ ({u0, u1, u2, u3} : Set V3) → p ≠ q →
      ({p, q} : Set V3) = ({u0, u1} : Set V3) ∨ ({p, q} : Set V3) = {u0, u2} ∨
        ({p, q} : Set V3) = {u0, u3} ∨ ({p, q} : Set V3) = {u1, u2} ∨
          ({p, q} : Set V3) = {u1, u3} ∨ ({p, q} : Set V3) = {u2, u3} := by
    intro p q hp hq hpq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with ha | ha | ha | ha <;> rcases hq with hb | hb | hb | hb
    · exact absurd (ha.trans hb.symm) hpq
    · rw [ha, hb]; exact Or.inl rfl
    · rw [ha, hb]; exact Or.inr (Or.inl rfl)
    · rw [ha, hb]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [ha, hb]; exact Or.inl (pEq u1 u0)
    · exact absurd (ha.trans hb.symm) hpq
    · rw [ha, hb]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [ha, hb]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · rw [ha, hb]; exact Or.inr (Or.inl (pEq u2 u0))
    · rw [ha, hb]; exact Or.inr (Or.inr (Or.inr (Or.inl (pEq u2 u1))))
    · exact absurd (ha.trans hb.symm) hpq
    · rw [ha, hb]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · rw [ha, hb]; exact Or.inr (Or.inr (Or.inl (pEq u3 u0)))
    · rw [ha, hb]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (pEq u3 u1)))))
    · rw [ha, hb]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pEq u3 u2)))))
    · exact absurd (ha.trans hb.symm) hpq
  ext e
  simp only [edgeX, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, rfl, ha, hbv, hab⟩
    rcases key a b ((hVX4 a).mp ha) ((hVX4 b).mp hbv) hab with h | h | h | h | h | h
    · simp only [h]; exact Set.mem_insert ({u0, u1} : Set V3) _
    · simp only [h]
      exact Set.mem_insert_of_mem (y := ({u0, u1} : Set V3))
        (Set.mem_insert ({u0, u2} : Set V3) _)
    · simp only [h]
      exact Set.mem_insert_of_mem (y := ({u0, u1} : Set V3))
        (Set.mem_insert_of_mem (y := ({u0, u2} : Set V3))
          (Set.mem_insert ({u0, u3} : Set V3) _))
    · simp only [h]
      exact Set.mem_insert_of_mem (y := ({u0, u1} : Set V3))
        (Set.mem_insert_of_mem (y := ({u0, u2} : Set V3))
          (Set.mem_insert_of_mem (y := ({u0, u3} : Set V3))
            (Set.mem_insert ({u1, u2} : Set V3) _)))
    · simp only [h]
      exact Set.mem_insert_of_mem (y := ({u0, u1} : Set V3))
        (Set.mem_insert_of_mem (y := ({u0, u2} : Set V3))
          (Set.mem_insert_of_mem (y := ({u0, u3} : Set V3))
            (Set.mem_insert_of_mem (y := ({u1, u2} : Set V3))
              (Set.mem_insert ({u1, u3} : Set V3) _))))
    · simp [h]
  · rintro (rfl | rfl | rfl | rfl | h6)
    · exact ⟨u0, u1, rfl, (hVX4 u0).mpr (by simp), (hVX4 u1).mpr (by simp), hdd.1⟩
    · exact ⟨u0, u2, rfl, (hVX4 u0).mpr (by simp), (hVX4 u2).mpr (by simp), hdd.2.1⟩
    · exact ⟨u0, u3, rfl, (hVX4 u0).mpr (by simp), (hVX4 u3).mpr (by simp), hdd.2.2.1⟩
    · exact ⟨u1, u2, rfl, (hVX4 u1).mpr (by simp), (hVX4 u2).mpr (by simp), hdd.2.2.2.1⟩
    · rcases Set.mem_insert_iff.mp h6 with h6' | h6'
      · subst h6'
        exact ⟨u1, u3, rfl, (hVX4 u1).mpr (by simp), (hVX4 u3).mpr (by simp),
          hdd.2.2.2.2.1⟩
      · subst h6'
        exact ⟨u2, u3, rfl, (hVX4 u2).mpr (by simp), (hVX4 u3).mpr (by simp),
          hdd.2.2.2.2.2⟩

/-- 私件（M4 波 2026-10-13，零债）：共面集的凸包 Haar 零测——包 ⊆ 仿射包 ⊆
三点仿射平面（`affineSpan_mono`），后者 `p25_affineSpan_three_ne_top` 给非全空间，
`addHaar_affineSubspace` 收口（HOL `COPLANAR_IMP_NEGLIGIBLE` 的凸包形态）。 -/
private theorem p25m_coplanar_hull_null {t : Set V3} (hcop : Coplanar t) :
    MeasureTheory.volume (convexHull ℝ t) = 0 := by
  obtain ⟨u, v, w, hsp⟩ := hcop
  have hsub : (affineSpan ℝ t : Set V3) ⊆ (affineSpan ℝ ({u, v, w} : Set V3) : Set V3) :=
    affineSpan_le_of_subset_coe hsp
  exact measure_mono_null ((convexHull_subset_affineSpan (s := t)).trans hsub)
    (Measure.addHaar_affineSubspace volume
      (affineSpan ℝ ({u, v, w} : Set V3)) (p25_affineSpan_three_ne_top u v w))

/-- HOL `CC_4_PROPS`: the full 4-cell wedge certificate.  2026-10-13 M4 波转真
（装配级）：派单值 4（`cc_4_cc_ke4`，本波装配）+ 胞改写（`cc_4_UL`，本波装配，
预消费具名记账件 `K4_CC_WI_ALT` 胞入楔——随 E8/楔 kit 落地自动升零债）+
`CC_CELL_NOT_NULLSET` 真件反推 `hl < √2`（`mcell4` 空支归零）与 `¬Coplanar`
（`p25m_coplanar_hull_null` 新私件）；`barV` 支经 `MCELL4_BARV_FI` 作用于
`cc_uh` 表（`cc_uh_exists` 见证 + `EL_CC_UH` 茎钉死）。 -/
theorem CC_4_PROPS (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) (h4 : cc_4 V u0 u1 f i) :
    ccKe V [u0, u1, f i] = 4 ∧
      hl [u0, u1, f i, f (i + 1)] < Real.sqrt 2 ∧
      convexHull ℝ ({u0, u1, f i, f (i + 1)} : Set V3) = ccCell V [u0, u1, f i] ∧
      ¬ Coplanar ({u0, u1, f i, f (i + 1)} : Set V3) ∧
      ccCell V [u0, u1, f i] ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
      ccCell V [u0, u1, f i] = mcell4 V [u0, u1, f i, f (i + 1)] ∧
      ¬ Collinear3 u0 u1 (f i) ∧ ¬ Collinear3 u0 u1 (f (i + 1)) ∧
      leaf V [u0, u1, f i] ∧ leaf V [u0, u1, f (i + 1)] ∧
      ¬ nullSet (ccCell V [u0, u1, f i]) ∧
      barV V 3 [u0, u1, f i, f (i + 1)] := by
  have hl' : leaf V [u0, u1, f i] := LEAF_RANK_LEAF V u0 u1 w0 n f i hr
  have hl'B : leaf V [u0, u1, f (i + 1)] := LEAF_RANK_LEAF V u0 u1 w0 n f (i + 1) hr
  have hper : periodic f n := LEAF_RANK_PERIODIC V [u0, u1] w0 n f hr
  have hk4 := cc_4_cc_ke4 V u0 u1 w0 n f i hp hs hr hnc hper hn hl' h4
  have hcc4 := cc_4_UL V u0 u1 w0 n f i hp hs hr hnc hn h4
  have hnull : ¬ nullSet (ccCell V [u0, u1, f i]) := CC_CELL_NOT_NULLSET hp hs hl'
  have hset4 : setOfList [u0, u1, f i, f (i + 1)]
      = ({u0, u1, f i, f (i + 1)} : Set V3) := by
    ext z
    simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hhl4 : hl [u0, u1, f i, f (i + 1)] < Real.sqrt 2 := by
    by_contra hcon
    have he4 : mcell4 V [u0, u1, f i, f (i + 1)] = ∅ := by
      unfold mcell4
      rw [if_neg hcon]
    rw [hcc4, he4] at hnull
    exact hnull measure_empty
  have hncop : ¬ Coplanar ({u0, u1, f i, f (i + 1)} : Set V3) := by
    intro hcop
    refine hnull ?_
    rw [hcc4, mcell4, if_pos hhl4, hset4]
    exact p25m_coplanar_hull_null hcop
  refine ⟨hk4, hhl4, ?_, hncop, ?_, hcc4, ?_, ?_, hl', hl'B, hnull, ?_⟩
  · rw [hcc4, mcell4, if_pos hhl4, hset4]
  · exact K4_CC_WI_ALT V [u0, u1] w0 n f i hp hs hr hnc hn hk4
  · exact (LEAF_DOMAIN V [u0, u1, f i] hs hp hl').1
  · exact (LEAF_DOMAIN V [u0, u1, f (i + 1)] hs hp hl'B).1
  · -- barV 支：MCELL4_BARV_FI 作用于 cc_uh 表（cc_uh_exists 见证）
    obtain ⟨hbarUh, -, -⟩ :=
      (Classical.choose_spec (cc_uh_exists V [u0, u1, f i])) hp hs hl'
    have hj4 : mcell 4 V (ccUh V [u0, u1, f i]) = mcell4 V (ccUh V [u0, u1, f i]) := by
      rw [mcell]; simp
    have hmcc : mcell4 V (ccUh V [u0, u1, f i]) = ccCell V [u0, u1, f i] := by
      rw [ccCell, hk4, hj4]
    have hnnU : ¬ nullSet (mcell4 V (ccUh V [u0, u1, f i])) := by
      rw [hmcc]
      exact hnull
    obtain ⟨he0, he1, he2⟩ := EL_CC_UH (V := V) (ul := [u0, u1, f i]) hp hs hl'
    have e0 : (ccUh V [u0, u1, f i]).getD 0 0 = u0 := by rw [he0]; simp
    have e1 : (ccUh V [u0, u1, f i]).getD 1 0 = u1 := by rw [he1]; simp
    have hrU : leaf_rank V [elV (ccUh V [u0, u1, f i]) 0, elV (ccUh V [u0, u1, f i]) 1]
        w0 n f := by
      simp only [elV, e0, e1]
      exact hr
    have hncU : ¬ Collinear3 (elV (ccUh V [u0, u1, f i]) 0)
        (elV (ccUh V [u0, u1, f i]) 1) w0 := by
      simp only [elV, e0, e1]
      exact hnc
    have hwU : mcell4 V (ccUh V [u0, u1, f i]) ⊆
        wedgeGe (elV (ccUh V [u0, u1, f i]) 0) (elV (ccUh V [u0, u1, f i]) 1)
          (f i) (f (i + 1)) := by
      simp only [hmcc, elV, e0, e1]
      exact K4_CC_WI_ALT V [u0, u1] w0 n f i hp hs hr hnc hn hk4
    have hbar := MCELL4_BARV_FI V (ccUh V [u0, u1, f i]) w0 n f i hp hs hrU hbarUh hncU
      hn hnnU hwU
    simp only [elV, e0, e1] at hbar
    exact hbar.1

/-- HOL `CC_4_BETA_BUMP_EXPLICIT`. -/
theorem CC_4_BETA_BUMP_EXPLICIT (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n)
    (h4 : cc_4 V u0 u1 f i) (hcey : criticalEdgeY (dist u0 u1))
    (hcey' : criticalEdgeY (dist (f i) (f (i + 1))))
    (hd1 : dist u0 (f i) < 2 * hminus) (hd2 : dist u0 (f (i + 1)) < 2 * hminus)
    (hd3 : dist u1 (f i) < 2 * hminus) (hd4 : dist u1 (f (i + 1)) < 2 * hminus) :
    betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) =
      bump (dist u0 u1 / 2) - bump (dist (f i) (f (i + 1)) / 2) := by
  sorry

/-- HOL `CC_4_BETA_BUMP_0`. -/
theorem CC_4_BETA_BUMP_0 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) (h4 : cc_4 V u0 u1 f i)
    (hnot : ¬ (criticalEdgeY (dist u0 u1) ∧
      criticalEdgeY (dist (f i) (f (i + 1))) ∧
      dist u0 (f i) < 2 * hminus ∧ dist u0 (f (i + 1)) < 2 * hminus ∧
      dist u1 (f i) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus)) :
    betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) = 0 := by
  sorry

/-- HOL `critical_edgeX_critical_edge_y`. -/
theorem critical_edgeX_critical_edge_y (V : Set V3) (X : Set V3) (u v : V3) :
    ({u, v} : Set V3) ∈ criticalEdgeX V X ↔
      ({u, v} : Set V3) ∈ edgeX V X ∧ criticalEdgeY (dist u v) := by
  constructor
  · rintro ⟨u', v', huv, hmem, h1, h2⟩
    rw [pair_eq_pair_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨hmem, ?_⟩
      unfold criticalEdgeY
      rw [HL_2] at h1 h2
      exact ⟨by linarith, by linarith⟩
    · refine ⟨hmem, ?_⟩
      unfold criticalEdgeY
      rw [HL_2, dist_comm] at h1 h2
      exact ⟨by linarith, by linarith⟩
  · rintro ⟨hmem, h1, h2⟩
    have hhl := HL_2 u v
    exact ⟨u, v, rfl, hmem, by linarith, by linarith⟩

/-! ### critical_weight_wtcount6_y finisher（P4rpiMini2 配方，2026-10-16 落地）

六步 `CARD_INSERT_INTER` 剥离把六边插入链交临界边集的 `ncard` 化成 `wtcount6Y`；
∉-合取项走 `simp only [nK, not_false_iff, and_true]`（`rw [nK]` 撞 False 陷阱）；
末尾 `unfold wtcount6Y wtcount3Y; split_ifs <;> omega` 收口。r8 雷区「0+1+…=
1+1+1+(1+1+1) 双侧为 6 却 rfl/omega/decide/norm_num 全拒（疑卡死 mvar）」由
`congrArg` 绕开：`1/` 分式两侧不展开 ℕ 求和，`criticalWeight` 化为 `ncard`-cast
后把 `ncard = wtcount6Y` 等式整只推过 `Nat.cast`。 -/

/-- 四元表成员枚举。 -/
private theorem p25rpi_mem4 (u0 u1 : V3) (f : ℕ → V3) (i : ℕ) (z : V3)
    (hz : z ∈ setOfList [u0, u1, f i, f (i + 1)]) :
    z = u0 ∨ z = u1 ∨ z = f i ∨ z = f (i + 1) := by
  simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil] at hz
  rcases hz with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact h.elim

/-- 二元 `{p, q}` 落在四点表内。 -/
private theorem p25rpi_sub4 (u0 u1 : V3) (f : ℕ → V3) (i : ℕ) (p q : V3)
    (hp4 : p = u0 ∨ p = u1 ∨ p = f i ∨ p = f (i + 1))
    (hq4 : q = u0 ∨ q = u1 ∨ q = f i ∨ q = f (i + 1)) :
    ({p, q} : Set V3) ⊆ setOfList [u0, u1, f i, f (i + 1)] := by
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · rcases hp4 with rfl | rfl | rfl | rfl <;> simp [setOfList]
  · rcases hq4 with rfl | rfl | rfl | rfl <;> simp [setOfList]

/-- 六条候选边成员 ⟺ `criticalEdgeY`（p, q 取遍四点表；`BumpP4.MCELL4_EDGE` +
`critical_edgeX_critical_edge_y` 装配）。 -/
private theorem p25rpi_mem6 (V : Set V3) (u0 u1 : V3) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V)
    (hcc4 : ccCell V [u0, u1, f i] = mcell4 V [u0, u1, f i, f (i + 1)])
    (hnull : ¬ nullSet (ccCell V [u0, u1, f i]))
    (hbar4 : barV V 3 [u0, u1, f i, f (i + 1)])
    (p q : V3) (hp4 : p = u0 ∨ p = u1 ∨ p = f i ∨ p = f (i + 1))
    (hq4 : q = u0 ∨ q = u1 ∨ q = f i ∨ q = f (i + 1)) (hpq : p ≠ q) :
    (({p, q} : Set V3) ∈ criticalEdgeX V (ccCell V [u0, u1, f i]) ↔
      criticalEdgeY (dist p q)) := by
  have hnn4 : ¬ nullSet (mcell4 V [u0, u1, f i, f (i + 1)]) := by
    rw [← hcc4]
    exact hnull
  rw [critical_edgeX_critical_edge_y V (ccCell V [u0, u1, f i]) p q]
  refine ⟨fun h => h.2, fun hc => ⟨?_, hc⟩⟩
  rw [hcc4]
  exact (BumpP4.MCELL4_EDGE V [u0, u1, f i, f (i + 1)] p q hp hs hnn4 hbar4).mpr
    ⟨hpq, p25rpi_sub4 u0 u1 f i p q hp4 hq4⟩

/-- 临界边计数核心（P4rpiMini2 配方）：B 有限且六条候选边成员恰由
`criticalEdgeY` 判定时，六边插入链交 B 的基数即 `wtcount6Y`。 -/
private theorem p25rpi_wtcount6_core (B : Set (Set V3)) (u0 u1 : V3) (f : ℕ → V3)
    (i : ℕ) (hB : B.Finite)
    (hE0 : ({u0, u1} : Set V3) ∈ B ↔ criticalEdgeY (dist u0 u1))
    (hE1 : ({u0, f i} : Set V3) ∈ B ↔ criticalEdgeY (dist u0 (f i)))
    (hE2 : ({u0, f (i + 1)} : Set V3) ∈ B ↔ criticalEdgeY (dist u0 (f (i + 1))))
    (hE3 : ({u1, f i} : Set V3) ∈ B ↔ criticalEdgeY (dist u1 (f i)))
    (hE4 : ({u1, f (i + 1)} : Set V3) ∈ B ↔ criticalEdgeY (dist u1 (f (i + 1))))
    (hE5 : ({f i, f (i + 1)} : Set V3) ∈ B ↔ criticalEdgeY (dist (f i) (f (i + 1))))
    (h01 : u0 ≠ u1) (h02 : u0 ≠ f i) (h03 : u0 ≠ f (i + 1))
    (h13 : u1 ≠ f i) (h14 : u1 ≠ f (i + 1)) (h34 : f i ≠ f (i + 1)) :
    Set.ncard ((insert ({f i, f (i + 1)} : Set V3) (insert ({u1, f (i + 1)} : Set V3)
      (insert ({u1, f i} : Set V3) (insert ({u0, f (i + 1)} : Set V3)
        (insert ({u0, f i} : Set V3) (insert ({u0, u1} : Set V3)
          (∅ : Set (Set V3)))))))) ∩ B) =
      wtcount6Y (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
        (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) := by
  rw [CARD_INSERT_INTER ({f i, f (i + 1)} : Set V3)
    (insert ({u1, f (i + 1)} : Set V3) (insert ({u1, f i} : Set V3)
      (insert ({u0, f (i + 1)} : Set V3)
        (insert ({u0, f i} : Set V3) (insert ({u0, u1} : Set V3) (∅ : Set (Set V3))))))) B hB]
  rw [hE5]
  have n5 : ({f i, f (i + 1)} : Set V3) ∉ (insert ({u1, f (i + 1)} : Set V3)
      (insert ({u1, f i} : Set V3) (insert ({u0, f (i + 1)} : Set V3)
        (insert ({u0, f i} : Set V3) (insert ({u0, u1} : Set V3) (∅ : Set (Set V3))))))) := by
    simp [Set.pair_eq_pair_iff, ne_comm, eq_comm, h01, h02, h03, h13, h14, h34]
  simp only [n5, not_false_iff, and_true]
  rw [CARD_INSERT_INTER ({u1, f (i + 1)} : Set V3)
    (insert ({u1, f i} : Set V3) (insert ({u0, f (i + 1)} : Set V3)
      (insert ({u0, f i} : Set V3) (insert ({u0, u1} : Set V3) (∅ : Set (Set V3)))))) B hB]
  rw [hE4]
  have n4 : ({u1, f (i + 1)} : Set V3) ∉ (insert ({u1, f i} : Set V3)
      (insert ({u0, f (i + 1)} : Set V3)
        (insert ({u0, f i} : Set V3) (insert ({u0, u1} : Set V3) (∅ : Set (Set V3)))))) := by
    simp [Set.pair_eq_pair_iff, ne_comm, eq_comm, h01, h02, h03, h13, h14, h34]
  simp only [n4, not_false_iff, and_true]
  rw [CARD_INSERT_INTER ({u1, f i} : Set V3)
    (insert ({u0, f (i + 1)} : Set V3)
      (insert ({u0, f i} : Set V3) (insert ({u0, u1} : Set V3) (∅ : Set (Set V3))))) B hB]
  rw [hE3]
  have n3 : ({u1, f i} : Set V3) ∉ (insert ({u0, f (i + 1)} : Set V3)
      (insert ({u0, f i} : Set V3) (insert ({u0, u1} : Set V3) (∅ : Set (Set V3))))) := by
    simp [Set.pair_eq_pair_iff, ne_comm, eq_comm, h01, h02, h03, h13, h14, h34]
  simp only [n3, not_false_iff, and_true]
  rw [CARD_INSERT_INTER ({u0, f (i + 1)} : Set V3)
    (insert ({u0, f i} : Set V3) (insert ({u0, u1} : Set V3) (∅ : Set (Set V3)))) B hB]
  rw [hE2]
  have n2 : ({u0, f (i + 1)} : Set V3) ∉ (insert ({u0, f i} : Set V3)
      (insert ({u0, u1} : Set V3) (∅ : Set (Set V3)))) := by
    simp [Set.pair_eq_pair_iff, ne_comm, eq_comm, h01, h02, h03, h13, h14, h34]
  simp only [n2, not_false_iff, and_true]
  rw [CARD_INSERT_INTER ({u0, f i} : Set V3)
    (insert ({u0, u1} : Set V3) (∅ : Set (Set V3))) B hB]
  rw [hE1]
  have n1 : ({u0, f i} : Set V3) ∉ (insert ({u0, u1} : Set V3) (∅ : Set (Set V3))) := by
    simp [Set.pair_eq_pair_iff, ne_comm, eq_comm, h01, h02, h03, h13, h14, h34]
  simp only [n1, not_false_iff, and_true]
  rw [CARD_INSERT_INTER ({u0, u1} : Set V3) (∅ : Set (Set V3)) B hB]
  rw [hE0]
  have n0 : ({u0, u1} : Set V3) ∉ (∅ : Set (Set V3)) := by simp
  simp only [n0, not_false_iff, and_true]
  simp only [Set.empty_inter, Set.ncard_empty]
  unfold wtcount6Y wtcount3Y
  split_ifs <;> omega

/-- HOL `critical_weight_wtcount6_y`.  2026-10-16 finisher 落地（P4rpiMini2
配方克隆验证后移植）：`CC_4_PROPS` 供 `ccCell = mcell4`/非零测/`barV`/双叶，
`LEAF_DOMAIN` + `LEAF_RANK_SUC_INJ` 供六点互异，`p25rpi_mem6` 供六对候选边
成员 ⟺ `criticalEdgeY`，`p25rpi_wtcount6_core` 六步剥离计数；末步 `congrArg`
把 `ncard = wtcount6Y` 等式整只推过 `Nat.cast`（绕开 ℕ 求和 finisher 雷区）。 -/
theorem critical_weight_wtcount6_y (V : Set V3) (u0 u1 w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n)
    (h4 : cc_4 V u0 u1 f i) (hcey : criticalEdgeY (dist u0 u1)) :
    criticalWeight V (ccCell V [u0, u1, f i]) =
      1 / (wtcount6Y (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
        (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i))) := by
  obtain ⟨-, -, -, -, -, hcc4, -, -, hleafA, hleafB, hnull, hbar4⟩ :=
    CC_4_PROPS V u0 u1 w0 n f i hp hs hr hnc hn h4
  have hnn4 : ¬ nullSet (mcell4 V [u0, u1, f i, f (i + 1)]) := by
    rw [← hcc4]
    exact hnull
  -- 六点互异（LEAF_DOMAIN 距离下界 + LEAF_RANK_SUC_INJ）
  have hdA := LEAF_DOMAIN V [u0, u1, f i] hs hp hleafA
  have hdB := LEAF_DOMAIN V [u0, u1, f (i + 1)] hs hp hleafB
  have eA0 : elV [u0, u1, f i] 0 = u0 := rfl
  have eA1 : elV [u0, u1, f i] 1 = u1 := rfl
  have eA2 : elV [u0, u1, f i] 2 = f i := rfl
  have eB0 : elV [u0, u1, f (i + 1)] 0 = u0 := rfl
  have eB1 : elV [u0, u1, f (i + 1)] 1 = u1 := rfl
  have eB2 : elV [u0, u1, f (i + 1)] 2 = f (i + 1) := rfl
  simp only [eA0, eA1, eA2] at hdA
  simp only [eB0, eB1, eB2] at hdB
  have hu01 : u0 ≠ u1 := by
    intro he
    have h2 := hdA.2.2.2.1
    rw [he] at h2
    rw [dist_self] at h2
    linarith
  have hu02 : u0 ≠ f i := by
    intro he
    have h2 := hdA.2.2.1
    rw [he] at h2
    rw [dist_self] at h2
    linarith
  have hu03 : u0 ≠ f (i + 1) := by
    intro he
    have h2 := hdB.2.2.1
    rw [he] at h2
    rw [dist_self] at h2
    linarith
  have hu13 : u1 ≠ f i := by
    intro he
    have h2 := hdA.2.1
    rw [he] at h2
    rw [dist_self] at h2
    linarith
  have hu14 : u1 ≠ f (i + 1) := by
    intro he
    have h2 := hdB.2.1
    rw [he] at h2
    rw [dist_self] at h2
    linarith
  have hu34 : f i ≠ f (i + 1) := LEAF_RANK_SUC_INJ V u0 u1 w0 n f i hp hs hr hnc hn
  -- 六对候选边成员 ⟺ criticalEdgeY
  have hE0 := p25rpi_mem6 V u0 u1 f i hp hs hcc4 hnull hbar4 u0 u1
    (Or.inl rfl) (Or.inr (Or.inl rfl)) hu01
  have hE1 := p25rpi_mem6 V u0 u1 f i hp hs hcc4 hnull hbar4 u0 (f i)
    (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) hu02
  have hE2 := p25rpi_mem6 V u0 u1 f i hp hs hcc4 hnull hbar4 u0 (f (i + 1))
    (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) hu03
  have hE3 := p25rpi_mem6 V u0 u1 f i hp hs hcc4 hnull hbar4 u1 (f i)
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) hu13
  have hE4 := p25rpi_mem6 V u0 u1 f i hp hs hcc4 hnull hbar4 u1 (f (i + 1))
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) hu14
  have hE5 := p25rpi_mem6 V u0 u1 f i hp hs hcc4 hnull hbar4 (f i) (f (i + 1))
    (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) hu34
  -- 临界边集有限（六边链的子集），且恰为六边链之交
  have hfin6 : Set.Finite (insert ({f i, f (i + 1)} : Set V3)
      (insert ({u1, f (i + 1)} : Set V3) (insert ({u1, f i} : Set V3)
        (insert ({u0, f (i + 1)} : Set V3) (insert ({u0, f i} : Set V3)
          (insert ({u0, u1} : Set V3) (∅ : Set (Set V3)))))))) := by simp
  have hsub6 : ∀ e ∈ criticalEdgeX V (ccCell V [u0, u1, f i]),
      e ∈ insert ({f i, f (i + 1)} : Set V3) (insert ({u1, f (i + 1)} : Set V3)
        (insert ({u1, f i} : Set V3) (insert ({u0, f (i + 1)} : Set V3)
          (insert ({u0, f i} : Set V3) (insert ({u0, u1} : Set V3)
            (∅ : Set (Set V3))))))) := by
    intro e he
    simp only [criticalEdgeX, Set.mem_setOf_eq] at he
    obtain ⟨p, q, rfl, hEd, -, -⟩ := he
    rw [hcc4, BumpP4.MCELL4_EDGE V [u0, u1, f i, f (i + 1)] p q hp hs hnn4 hbar4] at hEd
    obtain ⟨hpq, hsub⟩ := hEd
    have hp4 := p25rpi_mem4 u0 u1 f i p (hsub (by simp))
    have hq4 := p25rpi_mem4 u0 u1 f i q (hsub (by simp))
    rcases hp4 with rfl | rfl | rfl | rfl <;>
      rcases hq4 with rfl | rfl | rfl | rfl <;>
        first
          | (simp [Set.pair_eq_pair_iff, hu01, hu02, hu03, hu13, hu14, hu34]; done)
          | exact absurd rfl hpq
  have hBfin : (criticalEdgeX V (ccCell V [u0, u1, f i])).Finite :=
    hfin6.subset hsub6
  have heq : criticalEdgeX V (ccCell V [u0, u1, f i]) =
      insert ({f i, f (i + 1)} : Set V3) (insert ({u1, f (i + 1)} : Set V3)
        (insert ({u1, f i} : Set V3) (insert ({u0, f (i + 1)} : Set V3)
          (insert ({u0, f i} : Set V3) (insert ({u0, u1} : Set V3) ∅))))) ∩
        criticalEdgeX V (ccCell V [u0, u1, f i]) := by
    ext e
    exact ⟨fun he => ⟨hsub6 e he, he⟩, fun h => h.2⟩
  -- congrArg 直推分式（不展开 ℕ 求和——绕开 r8 数值 finisher 雷区）
  have hCW : criticalWeight V (ccCell V [u0, u1, f i]) =
      1 / ((criticalEdgeX V (ccCell V [u0, u1, f i])).ncard : ℝ) := rfl
  rw [hCW, heq]
  exact congrArg (fun x : ℕ => (1 : ℝ) / (x : ℝ))
    (p25rpi_wtcount6_core (criticalEdgeX V (ccCell V [u0, u1, f i])) u0 u1 f i hBfin
      hE0 hE1 hE2 hE3 hE4 hE5 hu01 hu02 hu03 hu13 hu14 hu34)

/-- HOL `c_4_azim_mcell_dih_y`: the 4-cell wedge dihedral is the `dih_y`
value.  2026-10-13 M4 波转真（装配级）：`LEAF_RANK_REUHADY`（azim_mcell 塌缩，
具名记账件在案——随 REUHADY/GRUTOTI 车道落地自动升零债）+ `CC_4_PROPS`（本波
装配）供 `barV`/非零测/楔子集 + `MCELL4_AZIM_LT_PI`（具名记账件在案）供
`azim < π`，`azim_dihv_same` + `DIHV_EQ_DIH_Y_4PT_B` 收口。 -/
theorem c_4_azim_mcell_dih_y (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (h4 : cc_4 V u0 u1 f i) :
    azim_mcell V f u0 u1 i =
      dihY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
        (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) := by
  obtain ⟨hke, hhl4, hcvx, hncop, hwsub, hcc4, hcolA, hcolB, hleafA, hleafB, hnull,
    hbar4⟩ := CC_4_PROPS V u0 u1 w0 n f i hp hs hr hnc hn h4
  have hreu : azim_mcell V f u0 u1 i = azim u0 u1 (f i) (f (i + 1)) :=
    LEAF_RANK_REUHADY V [u0, u1] w0 n f i hn hp hs hsize hnc hr
  have hnn4 : ¬ nullSet (mcell4 V [u0, u1, f i, f (i + 1)]) := by
    rw [← hcc4]
    exact hnull
  have hsub4 : mcell4 V [u0, u1, f i, f (i + 1)] ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) := by
    rw [← hcc4]
    exact hwsub
  have hlt := MCELL4_AZIM_LT_PI V [u0, u1, f i, f (i + 1)] w0 n f i hp hs hr hbar4 hnc
    hn hnn4 hsub4
  rw [hreu, azim_dihv_same hcolA hcolB hlt]
  exact DIHV_EQ_DIH_Y_4PT_B u0 u1 (f i) (f (i + 1)) hcolA hcolB

/-- HOL `NOT_COPLANAR_IMP_CARD4_ALT`. -/
theorem NOT_COPLANAR_IMP_CARD4_ALT (u0 u1 u2 u3 : V3)
    (hnc : ¬ Coplanar ({u0, u1, u2, u3} : Set V3)) :
    Set.ncard ({u0, u1, u2, u3} : Set V3) = 4 := by
  by_contra hcon
  push_neg at hcon
  -- some pair must coincide; then the set lives in a plane
  have hdup : u0 = u1 ∨ u0 = u2 ∨ u0 = u3 ∨ u1 = u2 ∨ u1 = u3 ∨ u2 = u3 := by
    by_contra hall
    push_neg at hall
    apply hcon
    rw [Set.ncard_insert_of_notMem (show u0 ∉ ({u1, u2, u3} : Set V3) from by simp [hall.1,
      hall.2.1, hall.2.2.1]),
      Set.ncard_insert_of_notMem (show u1 ∉ ({u2, u3} : Set V3) from by simp [hall.2.2.2.1,
        hall.2.2.2.2.1]),
      Set.ncard_insert_of_notMem (show u2 ∉ ({u3} : Set V3) from by simp [hall.2.2.2.2.2]),
      Set.ncard_singleton]
  have mem3 : ∀ (t1 t2 t3 a : V3), a = t1 ∨ a = t2 ∨ a = t3 →
      a ∈ ({t1, t2, t3} : Set V3) := by
    intro t1 t2 t3 a hh
    rcases hh with hh | hh | hh
    · simp [hh]
    · simp [hh]
    · simp [hh]
  rcases hdup with h | h | h | h | h | h
  · exact hnc ⟨u0, u2, u3, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u2 u3 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inl (ha.trans h.symm)
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)))⟩
  · exact hnc ⟨u0, u1, u3, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u1 u3 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inl (ha.trans h.symm)
      · exact Or.inr (Or.inr ha)))⟩
  · exact hnc ⟨u0, u1, u2, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u1 u2 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)
      · exact Or.inl (ha.trans h.symm)))⟩
  · exact hnc ⟨u0, u2, u3, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u2 u3 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (ha.trans h))
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)))⟩
  · exact hnc ⟨u0, u1, u2, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u1 u2 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)
      · exact Or.inr (Or.inl (ha.trans h.symm))))⟩
  · exact hnc ⟨u0, u1, u2, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u1 u2 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)
      · exact Or.inr (Or.inr (ha.trans h.symm))))⟩

/-- Helper: a point whose offset from `a` lies in the span of the `u-a`,
`v-a` offsets lies in the plane through `a, u, v`. -/
private theorem p25_mem_affSpan3 {a u v p : V3}
    (hp : (p - a : V3) ∈ Submodule.span ℝ ({u - a, v - a} : Set V3)) :
    p ∈ (affineSpan ℝ ({a, u, v} : Set V3) : Set V3) := by
  have hpv : (p : V3) = (p -ᵥ a) +ᵥ a := (vsub_vadd p a).symm
  rw [hpv]
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ (mem_affineSpan ℝ (by simp))
  rw [direction_affineSpan,
    vectorSpan_eq_span_vsub_set_right ℝ (show (a : V3) ∈ ({a, u, v} : Set V3) from by simp)]
  have hsub : ({u - a, v - a} : Set V3) ⊆
      ((fun q : V3 => (q -ᵥ a)) '' ({a, u, v} : Set V3)) := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact ⟨u, by simp, rfl⟩
    · rcases Set.mem_singleton_iff.mp hz with rfl
      exact ⟨v, by simp, rfl⟩
  exact Submodule.span_mono hsub hp

/-- Helper: an affinely dependent 4-point set is coplanar — the forward
direction of `AFF_DEP_COPLANAR` (HOL Oxl_2012; here via the
`affineIndependent_set_iff_linearIndependent_vsub` characterization: failure
of independence puts one offset in the span of the other two). -/
private theorem p25_affdep4_coplanar {a b c d : V3}
    (h : affineDependent ({a, b, c, d} : Set V3)) :
    Coplanar ({a, b, c, d} : Set V3) := by
  -- degenerate stem coincidences: the set drops to three points, which is
  -- coplanar outright
  rcases eq_or_ne a b with hab | hab
  · have hset : ({a, b, c, d} : Set V3) = ({b, c, d} : Set V3) := by
      rw [hab]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact coplanar_triple b c d
  rcases eq_or_ne a c with hac | hac
  · have hset : ({a, b, c, d} : Set V3) = ({b, c, d} : Set V3) := by
      rw [hac]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact coplanar_triple b c d
  rcases eq_or_ne a d with had | had
  · have hset : ({a, b, c, d} : Set V3) = ({b, c, d} : Set V3) := by
      rw [had]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact coplanar_triple b c d
  have hmem_a : (a : V3) ∈ ({a, b, c, d} : Set V3) := by simp
  have hdiff : (({a, b, c, d} : Set V3) \ {a}) = ({b, c, d} : Set V3) := by
    ext z
    by_cases hz : z = a
    · subst hz; simp [hab, hac, had]
    · simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, hz,
        not_false_iff]
      tauto
  have himg : ((fun p : V3 => (p -ᵥ a)) '' ({b, c, d} : Set V3))
      = ({b - a, c - a, d - a} : Set V3) := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [affineDependent,
    affineIndependent_set_iff_linearIndependent_vsub (k := ℝ) hmem_a, hdiff, himg] at h
  have h' : ¬ LinearIndepOn ℝ id ({b - a, c - a, d - a} : Set V3) := h
  by_cases hbb : (b - a : V3) ∈ Submodule.span ℝ ({c - a, d - a} : Set V3)
  · refine ⟨a, c, d, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with he | he | he | he
    · rw [he]; exact mem_affineSpan ℝ (by simp)
    · rw [he]; exact p25_mem_affSpan3 hbb
    · rw [he]; exact mem_affineSpan ℝ (by simp)
    · rw [he]; exact mem_affineSpan ℝ (by simp)
  · by_cases hcc : (c - a : V3) ∈ Submodule.span ℝ ({b - a, d - a} : Set V3)
    · refine ⟨a, b, d, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with he | he | he | he
      · rw [he]; exact mem_affineSpan ℝ (by simp)
      · rw [he]; exact mem_affineSpan ℝ (by simp)
      · rw [he]; exact p25_mem_affSpan3 hcc
      · rw [he]; exact mem_affineSpan ℝ (by simp)
    · by_cases hdd : (d - a : V3) ∈ Submodule.span ℝ ({b - a, c - a} : Set V3)
      · refine ⟨a, b, c, ?_⟩
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with he | he | he | he
        · rw [he]; exact mem_affineSpan ℝ (by simp)
        · rw [he]; exact mem_affineSpan ℝ (by simp)
        · rw [he]; exact mem_affineSpan ℝ (by simp)
        · rw [he]; exact p25_mem_affSpan3 hdd
      · exfalso
        have hda : d ≠ a := fun heq => hdd (by rw [heq]; simp)
        have hca : c ≠ a := fun heq => hcc (by rw [heq]; simp)
        have s1 : LinearIndepOn ℝ id ({d - a} : Set V3) :=
          LinearIndepOn.singleton (show (d - a : V3) ≠ 0 from sub_ne_zero.mpr hda)
        have s2 : LinearIndepOn ℝ id ({c - a, d - a} : Set V3) :=
          LinearIndepOn.id_insert (s := ({d - a} : Set V3)) s1
            (fun hm => hcc (Submodule.span_mono (Set.subset_insert _ _) hm))
        exact h' (LinearIndepOn.id_insert (s := ({c - a, d - a} : Set V3)) s2 hbb)

/-- HOL `radius_le_circumradius`.  Proof: the non-coplanar quadruple is
affinely independent (`p25_affdep4_coplanar`), so both endpoints sit on the
circumsphere (`OAPVION2_concl`) and the chord is at most the diameter. -/
theorem radius_le_circumradius (u0 u1 u2 u3 : V3)
    (hnc : ¬ Coplanar ({u0, u1, u2, u3} : Set V3)) :
    dist u0 u1 ≤ 2 * radV {u0, u1, u2, u3} := by
  have haff : ¬ affineDependent ({u0, u1, u2, u3} : Set V3) :=
    fun hd => hnc (p25_affdep4_coplanar hd)
  have d0 := OAPVION2_concl ({u0, u1, u2, u3} : Set V3) haff u0 (by simp)
  have d1 := OAPVION2_concl ({u0, u1, u2, u3} : Set V3) haff u1 (by simp)
  have htri : dist u0 u1 ≤
      dist u0 (circumcenter ({u0, u1, u2, u3} : Set V3)) +
        dist (circumcenter ({u0, u1, u2, u3} : Set V3)) u1 :=
    dist_triangle _ _ _
  rw [dist_comm u0 (circumcenter ({u0, u1, u2, u3} : Set V3)), ← d0, ← d1] at htri
  linarith

/-- HOL `radius_le_circumradius_all`. -/
theorem radius_le_circumradius_all (u0 u1 u2 u3 : V3)
    (hnc : ¬ Coplanar ({u0, u1, u2, u3} : Set V3)) :
    dist u0 u1 ≤ 2 * radV {u0, u1, u2, u3} ∧
      dist u0 u2 ≤ 2 * radV {u0, u1, u2, u3} ∧
      dist u0 u3 ≤ 2 * radV {u0, u1, u2, u3} ∧
      dist u1 u2 ≤ 2 * radV {u0, u1, u2, u3} ∧
      dist u1 u3 ≤ 2 * radV {u0, u1, u2, u3} ∧
      dist u2 u3 ≤ 2 * radV {u0, u1, u2, u3} := by
  have hperm : ∀ (p q r s : V3), ({p, q, r, s} : Set V3) = ({u0, u1, u2, u3} : Set V3) →
      dist p q ≤ 2 * radV ({u0, u1, u2, u3} : Set V3) := by
    intro p q r s he
    have hkey := radius_le_circumradius p q r s (by rw [he]; exact hnc)
    rw [he] at hkey
    exact hkey
  refine ⟨hperm u0 u1 u2 u3 rfl, hperm u0 u2 u1 u3 ?_, hperm u0 u3 u1 u2 ?_,
    hperm u1 u2 u0 u3 ?_, hperm u1 u3 u0 u2 ?_, hperm u2 u3 u0 u1 ?_⟩
  repeat' ext q
  repeat' simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  all_goals tauto

/-- HOL `MCELL4_DOMAIN`: the 4-cell wedge distance certificate.
2026-10-13 转真（装配级）：`CC_4_PROPS` 十二合取全数消费——`hl < √2` 支经
`hl` 定义性展开（`radV ∘ setOfList`）+`BARV3_SET_OF_LIST4` 给 `radV < √2`；
`¬Coplanar` 支喂 `radius_le_circumradius_all`（弦长 ≤ 2r，六连）与
`coplanar_delta_y`（delta 合取与该 Iff 逐字同形，`.mp` 直接实例化）与
`NOT_COPLANAR_IMP_CARD4_ALT`（4 互异 → packing 分离给 `2 ≤ dist` 六连）；
`rad2_y` 支经 `GDRQXLGv3`（radV² ↔ rad2XP25 平方长解析桥，2026-10-13 r5 波
转真：外心-Cramer 代数，见其 docstring）+ 弦不等式。
`barV` 支走 `BARV_SUBSET` 给四点 ∈ V。债走账本：消费在库具名记账件
`CC_4_PROPS`（其上游 PA18 `MCELL4_EDGE_FIRST`/`STEM_EDGEX` edge-rigidity kit
未落地，本文件在案）；`GDRQXLGv3` 已 r5 同波转真出账（本体消费处不改）。 -/
theorem MCELL4_DOMAIN (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (h4 : cc_4 V u0 u1 f i) :
    2 * hminus ≤ dist u0 u1 ∧ dist u0 u1 ≤ 2 * hplus ∧
      2 ≤ dist u0 (f i) ∧ dist u0 (f i) < 2 * Real.sqrt 2 ∧
      2 ≤ dist u0 (f (i + 1)) ∧ dist u0 (f (i + 1)) < 2 * Real.sqrt 2 ∧
      2 ≤ dist (f i) (f (i + 1)) ∧ dist (f i) (f (i + 1)) < 2 * Real.sqrt 2 ∧
      2 ≤ dist u1 (f i) ∧ dist u1 (f i) < 2 * Real.sqrt 2 ∧
      2 ≤ dist u1 (f (i + 1)) ∧ dist u1 (f (i + 1)) < 2 * Real.sqrt 2 ∧
      rad2YP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) < 2 ∧
      0 < deltaY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
        (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) := by
  obtain ⟨-, hhl4, -, hncop, -, hcc4, -, -, -, -, hnull4, hbar4⟩ :=
    CC_4_PROPS V u0 u1 w0 n f i hp hs hr hnc hn h4
  have hnn4 : ¬ nullSet (mcell4 V [u0, u1, f i, f (i + 1)]) := by
    rw [← hcc4]
    exact hnull4
  have hcard4 := NOT_COPLANAR_IMP_CARD4_ALT u0 u1 (f i) (f (i + 1)) hncop
  obtain ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩ := p25m_card4_ne hcard4
  have hset4 : setOfList [u0, u1, f i, f (i + 1)]
      = ({u0, u1, f i, f (i + 1)} : Set V3) :=
    BARV3_SET_OF_LIST4 V [u0, u1, f i, f (i + 1)] hp hbar4
  have hsub : setOfList [u0, u1, f i, f (i + 1)] ⊆ V :=
    BARV_SUBSET V 3 [u0, u1, f i, f (i + 1)] hbar4
  have hinV : ∀ z : V3, z ∈ ({u0, u1, f i, f (i + 1)} : Set V3) → z ∈ V := by
    intro z hz
    rw [← hset4] at hz
    exact hsub hz
  have hge2 : ∀ p q : V3, p ∈ ({u0, u1, f i, f (i + 1)} : Set V3) →
      q ∈ ({u0, u1, f i, f (i + 1)} : Set V3) → p ≠ q → 2 ≤ dist p q := by
    intro p q hp1 hp2 hne
    exact hp.dist_ge_two (hinV _ hp1) (hinV _ hp2) hne
  have hrad : radV ({u0, u1, f i, f (i + 1)} : Set V3) < Real.sqrt 2 := by
    have hcv : hl [u0, u1, f i, f (i + 1)] < Real.sqrt 2 := hhl4
    unfold hl at hcv
    rw [hset4] at hcv
    exact hcv
  have haff : ¬ affineDependent ({u0, u1, f i, f (i + 1)} : Set V3) :=
    fun hd => hncop (p25_affdep4_coplanar hd)
  have hnn0 : 0 ≤ radV ({u0, u1, f i, f (i + 1)} : Set V3) := by
    rw [OAPVION2_concl ({u0, u1, f i, f (i + 1)} : Set V3) haff u0 (by simp)]
    exact dist_nonneg
  have h6 := radius_le_circumradius_all u0 u1 (f i) (f (i + 1)) hncop
  have hlt2 : ∀ x : ℝ, x ≤ 2 * radV ({u0, u1, f i, f (i + 1)} : Set V3) →
      x < 2 * Real.sqrt 2 := by
    intro x hx
    linarith [hrad]
  refine ⟨hcey.1, hcey.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hge2 u0 (f i) (by simp) (by simp) hd02
  · exact hlt2 _ h6.2.1
  · exact hge2 u0 (f (i + 1)) (by simp) (by simp) hd03
  · exact hlt2 _ h6.2.2.1
  · exact hge2 (f i) (f (i + 1)) (by simp) (by simp) hd23
  · exact hlt2 _ h6.2.2.2.2.2
  · exact hge2 u1 (f i) (by simp) (by simp) hd12
  · exact hlt2 _ h6.2.2.2.1
  · exact hge2 u1 (f (i + 1)) (by simp) (by simp) hd13
  · exact hlt2 _ h6.2.2.2.2.1
  · have hG := GDRQXLGv3 u0 u1 (f i) (f (i + 1)) hncop
    simp only [pow_two] at hG
    have hY : rad2YP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i))
        = rad2XP25 (dist u0 u1 * dist u0 u1) (dist u0 (f i) * dist u0 (f i))
            (dist u0 (f (i + 1)) * dist u0 (f (i + 1)))
            (dist (f i) (f (i + 1)) * dist (f i) (f (i + 1)))
            (dist u1 (f (i + 1)) * dist u1 (f (i + 1)))
            (dist u1 (f i) * dist u1 (f i)) := rfl
    rw [hY, ← hG]
    have hmul1 : radV ({u0, u1, f i, f (i + 1)} : Set V3)
        * radV ({u0, u1, f i, f (i + 1)} : Set V3)
        ≤ radV ({u0, u1, f i, f (i + 1)} : Set V3) * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hrad) hnn0
    have hmul2 : radV ({u0, u1, f i, f (i + 1)} : Set V3) * Real.sqrt 2
        < Real.sqrt 2 * Real.sqrt 2 :=
      mul_lt_mul_of_pos_right hrad (by norm_num : (0:ℝ) < Real.sqrt 2)
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 :=
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    linarith
  · exact (coplanar_delta_y u0 u1 (f i) (f (i + 1))).mp hncop

/-- HOL `real_model_azim_c4`.  2026-10-13 M4 波转真（装配级）：`c_4_azim_mcell_dih_y`
（本波装配）塌缩 azim_mcell 到 `dih_y` + `MCELL4_DOMAIN`（r4 真件）供盒约束 +
bank 投影 `proj_bank_BIXPCGW6652007036a2`（dih_y < 2.8 于盒 `[2hmin,2hplus]×[2,√8]⁵`）
——`2√2 = √8` 桥收口，零新增记账债。 -/
theorem real_model_azim_c4 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i → azim_mcell V f u0 u1 i < 2.8 := by
  intro i h4
  have hdih := c_4_azim_mcell_dih_y V u0 u1 w0 n f i hn hp hs hsize h0 h1 hper hnc hcey
    hr h4
  have hbox := MCELL4_DOMAIN V u0 u1 w0 n f i hnl hn hp hs hsize h0 h1 hper hnc hcey hr
    h4
  have hbank := proj_bank_BIXPCGW6652007036a2 hnl
  have hs8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    have h42 : (8:ℝ) = 4 * 2 := by norm_num
    have hge : (0:ℝ) ≤ 4 := by norm_num
    rw [h42, Real.sqrt_mul hge]
    norm_num
  have hle8 : ∀ q : ℝ, q < 2 * Real.sqrt 2 → q ≤ Real.sqrt 8 := by
    intro q hq
    rw [hs8]
    exact le_of_lt hq
  rw [hdih]
  refine hbank _ _ _ _ _ _ hbox.1 hbox.2.1 hbox.2.2.1 (hle8 _ hbox.2.2.2.1)
    hbox.2.2.2.2.1 (hle8 _ hbox.2.2.2.2.2.1) hbox.2.2.2.2.2.2.1
    (hle8 _ hbox.2.2.2.2.2.2.2.1) hbox.2.2.2.2.2.2.2.2.2.2.1
    (hle8 _ hbox.2.2.2.2.2.2.2.2.2.2.2.1) hbox.2.2.2.2.2.2.2.2.1
    (hle8 _ hbox.2.2.2.2.2.2.2.2.2.1)

/-- HOL `gammaX_gamma4fgcy_ALT` (renamed from gammaX_gamm4fgcy_ALT). -/
theorem gammaX_gamma4fgcy_ALT (V : Set V3) (X : Set V3) (u0 u1 u2 u3 : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 [u0, u1, u2, u3])
    (hX : X = mcell4 V [u0, u1, u2, u3]) (hn : ¬ nullSet X) :
    gammaX V X lmfun =
      gamma4fgcyP25 (dist u0 u1) (dist u0 u2) (dist u0 u3) (dist u2 u3)
        (dist u1 u3) (dist u1 u2) lmfun := by
  -- PA20 `gammaX_gamm4fgcy`（经 PA21 传递可见）的 `i := 4` 直接消费；`mcell4` 与
  -- `mcell 4` 定义性互换，`gamma4fgcyP25` 与 PA20 `gamma4fgcy` 同体（volY − vol4f）。
  have h := gammaX_gamm4fgcy (V := V) (X := X) (ul := [u0, u1, u2, u3]) (u0 := u0)
    (u1 := u1) (u2 := u2) (u3 := u3) (i := 4)
    (y1 := dist u0 u1) (y2 := dist u0 u2) (y3 := dist u0 u3) (y4 := dist u2 u3)
    (y5 := dist u1 u3) (y6 := dist u1 u2) hs hp hb (by omega) hX hn (hul := rfl)
    (hy1 := rfl) (hy2 := rfl) (hy3 := rfl) (hy4 := rfl) (hy5 := rfl) (hy6 := rfl)
  exact h.2

/-- HOL `GG_MCELL_QUARTER`: the quarter-wedge gg value. -/
theorem GG_MCELL_QUARTER (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (h4 : cc_4 V u0 u1 f i)
    (hd1 : dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus)
    (hd2 : dist u0 (f (i + 1)) < 2 * hminus) (hd3 : dist u1 (f (i + 1)) < 2 * hminus)
    (hd4 : dist (f i) (f (i + 1)) < 2 * hminus)
    (hr : leaf_rank V [u0, u1] w0 n f) :
    gg_mcell V f u0 u1 i =
      gamma4fgcyP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
        (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) lmfun := by
  -- 装配（2026-10-13 M4 波）：cc_4_cc_cell（本波装配，其债面 = MCELL4_GG 记账）
  -- + gammaX_gamma4fgcy_ALT（真件，barV/非零测取自 CC_4_PROPS）+ 具名记账件
  -- critical_weight_wtcount6_y / CC_4_BETA_BUMP_0（随 wtcount/Bump 车道落地自动
  -- 升零债）+ wtcount6 = 1 算术（茎临界、其余五边 < 2·hminus 非临界）。
  have hl' : leaf V [u0, u1, f i] := LEAF_RANK_LEAF V u0 u1 w0 n f i hr
  have hcc := cc_4_cc_cell V u0 u1 w0 n f i hp hs hper hl' hr hnc hn h4
  obtain ⟨hke, hhl4, hcvx, hncop, hwsub, hcc4, hcolA, hcolB, hleafA, hleafB, hnull,
    hbar4⟩ := CC_4_PROPS V u0 u1 w0 n f i hp hs hr hnc hn h4
  have hcey' : criticalEdgeY (dist (f i) (f (i + 1))) → False := fun hc =>
    absurd hd4 (not_lt.mpr hc.1)
  have hnc2 : ¬ criticalEdgeY (dist u0 (f i)) := fun hc =>
    absurd hd1.1 (not_lt.mpr hc.1)
  have hnc3 : ¬ criticalEdgeY (dist u0 (f (i + 1))) := fun hc =>
    absurd hd2 (not_lt.mpr hc.1)
  have hnc5 : ¬ criticalEdgeY (dist u1 (f (i + 1))) := fun hc =>
    absurd hd3 (not_lt.mpr hc.1)
  have hnc6 : ¬ criticalEdgeY (dist u1 (f i)) := fun hc =>
    absurd hd1.2 (not_lt.mpr hc.1)
  have hwt : wtcount6Y (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
      (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) = 1 := by
    unfold wtcount6Y wtcount3Y
    rw [if_pos hcey, if_neg hnc2, if_neg hnc3, if_neg hcey', if_neg hnc5, if_neg hnc6]
  have hnot0 : ¬ (criticalEdgeY (dist u0 u1) ∧
      criticalEdgeY (dist (f i) (f (i + 1))) ∧
      dist u0 (f i) < 2 * hminus ∧ dist u0 (f (i + 1)) < 2 * hminus ∧
      dist u1 (f i) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) :=
    fun hc => hcey' hc.2.1
  have hwb := CC_4_BETA_BUMP_0 V u0 u1 w0 n f i hp hs hr hnc hn h4 hnot0
  have hgw := critical_weight_wtcount6_y V u0 u1 w0 n f i hp hs hr hnc hn h4 hcey
  have hgam := gammaX_gamma4fgcy_ALT V (ccCell V [u0, u1, f i]) u0 u1 (f i) (f (i + 1))
    hs hp hbar4 hcc4 hnull
  rw [hcc, hgw, hwt, hwb, hgam]
  all_goals norm_num

/-- HOL `GG_MCELL_BETA`: the beta-wedge gg value. -/
theorem GG_MCELL_BETA (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (h4 : cc_4 V u0 u1 f i)
    (hd1 : dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus)
    (hd2 : dist u0 (f (i + 1)) < 2 * hminus) (hd3 : dist u1 (f (i + 1)) < 2 * hminus)
    (hcey' : criticalEdgeY (dist (f i) (f (i + 1))))
    (hr : leaf_rank V [u0, u1] w0 n f) :
    gg_mcell V f u0 u1 i =
      gamma4fgcyP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) lmfun / 2 +
        bump (dist u0 u1 / 2) - bump (dist (f i) (f (i + 1)) / 2) := by
  sorry

/-- HOL `GG_MCELL_NONBETA`. -/
theorem GG_MCELL_NONBETA (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (h4 : cc_4 V u0 u1 f i)
    (hnot : ¬ ((dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
      dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
      criticalEdgeY (dist (f i) (f (i + 1)))))
    (hr : leaf_rank V [u0, u1] w0 n f) :
    gg_mcell V f u0 u1 i =
      gamma4fgcyP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) lmfun /
        (wtcount6Y (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i))) := by
  sorry

/-- HOL `GG_MCELL_GENERAL`. -/
theorem GG_MCELL_GENERAL (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (h4 : cc_4 V u0 u1 f i)
    (hr : leaf_rank V [u0, u1] w0 n f) :
    gg_mcell V f u0 u1 i =
      gamma4fgcyP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) lmfun /
        (wtcount6Y (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i))) +
        beta_bumpA_yP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) := by
  sorry

/-- HOL `real_model_gamma_qu`. -/
theorem real_model_gamma_qu (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
        dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
        dist (f i) (f (i + 1)) < 2 * hminus →
      -0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `ETA_Y_POS_LE_ALT`. -/
theorem ETA_Y_POS_LE_ALT (u0 u1 u2 : V3) :
    0 ≤ eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) := by
  -- `eta_y` = `etaX`（平方长）= `Real.sqrt`，平方根非负，无条件成立。
  have hform : eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2)
      = Real.sqrt (dist u0 u1 * dist u0 u1 * (dist u0 u2 * dist u0 u2)
          * (dist u1 u2 * dist u1 u2)
        / upsX (dist u0 u1 * dist u0 u1) (dist u0 u2 * dist u0 u2)
          (dist u1 u2 * dist u1 u2)) := rfl
  rw [hform]
  exact Real.sqrt_nonneg _

/-- HOL `ETA_Y_LEMMA`（2026-10-13 转真：`RADV_ETAY` 把 `eta_y` 折算为
`radV {三点}`，`hl` 定义性展开后即 `pow_le_pow_left` 单调）。 -/
theorem ETA_Y_LEMMA (u0 u1 u2 : V3) (r : ℝ) (hnc : ¬ Collinear3 u0 u1 u2)
    (hr : 0 < r) (hrl : r ≤ hl [u0, u1, u2]) :
    r ^ 2 ≤ eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) ^ 2 := by
  have hset : setOfList [u0, u1, u2] = ({u0, u1, u2} : Set V3) := by
    ext x; simp [setOfList]
  have hrl' : r ≤ radV (setOfList [u0, u1, u2]) := hrl
  rw [hset] at hrl'
  rw [← RADV_ETAY u0 u1 u2 hnc]
  have hnn : 0 ≤ radV ({u0, u1, u2} : Set V3) := by
    rw [RADV_ETAY u0 u1 u2 hnc]
    exact ETA_Y_POS_LE_ALT u0 u1 u2
  exact (sq_le_sq₀ (le_of_lt hr) hnn).mpr hrl'

/-- HOL `ETA_Y_LEMMA_ALT`（2026-10-13 转真：同 `ETA_Y_LEMMA`，非负性由
`ETA_Y_POS_LE_ALT` 供）。 -/
theorem ETA_Y_LEMMA_ALT (u0 u1 u2 : V3) (r : ℝ) (hnc : ¬ Collinear3 u0 u1 u2)
    (hrl : hl [u0, u1, u2] ≤ r) :
    eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) ^ 2 ≤ r ^ 2 := by
  have hset : setOfList [u0, u1, u2] = ({u0, u1, u2} : Set V3) := by
    ext x; simp [setOfList]
  have hrl' : radV (setOfList [u0, u1, u2]) ≤ r := hrl
  rw [hset] at hrl'
  rw [← RADV_ETAY u0 u1 u2 hnc]
  have hnn : 0 ≤ radV ({u0, u1, u2} : Set V3) := by
    rw [RADV_ETAY u0 u1 u2 hnc]
    exact ETA_Y_POS_LE_ALT u0 u1 u2
  have hr0 : (0 : ℝ) ≤ r := le_trans hnn hrl'
  exact (sq_le_sq₀ hnn hr0).mpr hrl'

/-- HOL `real_model_fhbv2`. -/
theorem real_model_fhbv2 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, (cc_4 V u0 u1 f i ∧
          (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
          dist (f i) (f (i + 1)) < 2 * hminus) ∧
        ¬ (hl [u0, u1, f (i + 1)] < 1.34) →
      0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_fhbv2_sym`. -/
theorem real_model_fhbv2_sym (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, (cc_4 V u0 u1 f i ∧
          (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
          dist (f i) (f (i + 1)) < 2 * hminus) ∧
        ¬ (hl [u0, u1, f i] < 1.34) →
      0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `CC_3_PROPS`: the full 3-cell wedge certificate. -/
theorem CC_3_PROPS (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1))
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (hn : 1 < n)
    (hno4 : ¬ cc_4 V u0 u1 f i) :
    ccKe V [u0, u1, f i] = 3 ∧
      barV V 3 (ccUh V [u0, u1, f i]) ∧
      barV V 3 (ccUh V [u1, u0, f (i + 1)]) ∧
      betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) = 0 ∧
      betaBumpV1 V {u0, u1} (ccCell V [u1, u0, f (i + 1)]) = 0 ∧
      ccKe V [u1, u0, f (i + 1)] = 3 ∧
      ccCell V [u0, u1, f i] ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
      ccCell V [u1, u0, f (i + 1)] ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
      ccCell V [u0, u1, f i] ≠ ccCell V [u1, u0, f (i + 1)] ∧
      ¬ Collinear3 u0 u1 (f i) ∧ ¬ Collinear3 u0 u1 (f (i + 1)) ∧
      hl [u0, u1, f i] < Real.sqrt 2 ∧ hl [u0, u1, f (i + 1)] < Real.sqrt 2 ∧
      hl [u1, u0, f (i + 1)] < Real.sqrt 2 ∧
      leaf V [u0, u1, f i] ∧ leaf V [u0, u1, f (i + 1)] ∧
      leaf V [u1, u0, f (i + 1)] ∧
      2 ≤ dist u0 u1 ∧ 2 ≤ dist u0 (f i) ∧ 2 ≤ dist u0 (f (i + 1)) ∧
      2 ≤ dist u1 (f i) ∧ 2 ≤ dist u1 (f (i + 1)) ∧
      dist u0 u1 ≤ 2 * Real.sqrt 2 ∧ dist u0 (f i) ≤ 2 * Real.sqrt 2 ∧
      dist u0 (f (i + 1)) ≤ 2 * Real.sqrt 2 ∧
      dist u1 (f i) ≤ 2 * Real.sqrt 2 ∧
      dist u1 (f (i + 1)) ≤ 2 * Real.sqrt 2 ∧
      eta_y (dist u0 u1) (dist u0 (f i)) (dist u1 (f i)) < Real.sqrt 2 ∧
      eta_y (dist u0 u1) (dist u0 (f (i + 1))) (dist u1 (f (i + 1))) < Real.sqrt 2 ∧
      ¬ nullSet (ccCell V [u0, u1, f i]) ∧
      ¬ nullSet (ccCell V [u1, u0, f (i + 1)]) ∧
      azim_mcell V f u0 u1 i = azim u0 u1 (f i) (f (i + 1)) ∧
      (∃ y4, 2 ≤ y4 ∧ y4 ≤ 2 * Real.sqrt 2 ∧
        0 < deltaY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1))) y4
          (dist u1 (f (i + 1))) (dist u1 (f i)) ∧
        dihY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1))) y4
            (dist u1 (f (i + 1))) (dist u1 (f i)) ≤ azim u0 u1 (f i) (f (i + 1)) ∧
        2 ≤ rad2YP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1))) y4
          (dist u1 (f (i + 1))) (dist u1 (f i)) ∧
        (azim u0 u1 (f i) (f (i + 1)) < Real.pi ∧
            dist (f i) (f (i + 1)) ≤ 2 * Real.sqrt 2 →
          y4 = dist (f i) (f (i + 1)))) := by
  -- NO_4CELL_IMP_K3 dispatch (HOL OXLZLEZ3.hl:5965)
  simp only [cc_4] at hno4
  have hd := NO_4CELL_IMP_K3 V (wedgeGe u0 u1 (f i) (f (i + 1))) [u0, u1] w0 n f i
    hp hs hr hnc rfl hn hno4
  obtain ⟨hk3b, hk3a, hsubA, hsubB, hne⟩ := hd
  simp [elV] at hk3b hk3a hsubA hsubB hne
  -- leaves
  have hleafA : leaf V [u0, u1, f i] := LEAF_RANK_LEAF V u0 u1 w0 n f i hr
  have hleafB : leaf V [u0, u1, f (i + 1)] := LEAF_RANK_LEAF V u0 u1 w0 n f (i + 1) hr
  have hleafB2 : leaf V [u1, u0, f (i + 1)] := (ZASUVOR hp hs hleafB).1
  -- ccUh witnesses (p25m_cc3_wit pattern, inlined: the private kit sits below)
  have hbarA : barV V 3 (ccUh V [u0, u1, f i]) :=
    (Classical.choose_spec (cc_uh_exists V [u0, u1, f i])) hp hs hleafA |>.1
  have hbarB : barV V 3 (ccUh V [u1, u0, f (i + 1)]) :=
    (Classical.choose_spec (cc_uh_exists V [u1, u0, f (i + 1)])) hp hs hleafB2 |>.1
  -- cell equations and beta-bump nullity (k = 3 cells carry no bump)
  have hccA3 : ccCell V [u0, u1, f i] = mcell 3 V (ccUh V [u0, u1, f i]) := by
    show mcell (ccKe V [u0, u1, f i]) V (ccUh V [u0, u1, f i]) = _
    rw [hk3a]
  have hccB3 : ccCell V [u1, u0, f (i + 1)] = mcell 3 V (ccUh V [u1, u0, f (i + 1)]) := by
    show mcell (ccKe V [u1, u0, f (i + 1)]) V (ccUh V [u1, u0, f (i + 1)]) = _
    rw [hk3b]
  have hnnA : ¬ nullSet (ccCell V [u0, u1, f i]) :=
    CC_CELL_NOT_NULLSET (V := V) (ul := [u0, u1, f i]) hp hs hleafA
  have hnnB : ¬ nullSet (ccCell V [u1, u0, f (i + 1)]) :=
    CC_CELL_NOT_NULLSET (V := V) (ul := [u1, u0, f (i + 1)]) hp hs hleafB2
  have hbbA : betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) = 0 := by
    have heq : betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) =
        betaBump V {u0, u1} (mcell 3 V (ccUh V [u0, u1, f i])) := by rw [hccA3]; rfl
    rw [heq]
    refine BumpP4.MCELL_BUMP_0 V (ccUh V [u0, u1, f i]) {u0, u1} 3 (by omega) hp hs
      hbarA ?_
    rw [← hccA3]
    exact hnnA
  have hbbB : betaBumpV1 V {u0, u1} (ccCell V [u1, u0, f (i + 1)]) = 0 := by
    have heq : betaBumpV1 V {u0, u1} (ccCell V [u1, u0, f (i + 1)]) =
        betaBump V {u0, u1} (mcell 3 V (ccUh V [u1, u0, f (i + 1)])) := by
      rw [hccB3]; rfl
    rw [heq]
    refine BumpP4.MCELL_BUMP_0 V (ccUh V [u1, u0, f (i + 1)]) {u0, u1} 3 (by omega) hp hs
      hbarB ?_
    rw [← hccB3]
    exact hnnB
  -- leaf box facts
  obtain ⟨-, hd12i, hd02i, hd01i, hi12, hi02, hi01, hetai⟩ :=
    LEAF_DOMAIN V [u0, u1, f i] hs hp hleafA
  obtain ⟨-, hd12s, hd02s, -, hi12s, hi02s, -, hetas⟩ :=
    LEAF_DOMAIN V [u0, u1, f (i + 1)] hs hp hleafB
  have eV0 : ∀ (p q r : V3), elV [p, q, r] 0 = p := fun _ _ _ => rfl
  have eV1 : ∀ (p q r : V3), elV [p, q, r] 1 = q := fun _ _ _ => rfl
  have eV2 : ∀ (p q r : V3), elV [p, q, r] 2 = r := fun _ _ _ => rfl
  simp only [eV0, eV1, eV2] at hd12i hd02i hd01i hi12 hi02 hetai
  simp only [eV0, eV1, eV2] at hd12s hd02s hi12s hi02s hetas
  have hcolA : ¬ Collinear3 u0 u1 (f i) := by
    simpa using GBEWYFX (V := V) (ul := [u0, u1, f i]) hp hs hleafA
  have hcolB : ¬ Collinear3 u0 u1 (f (i + 1)) := by
    simpa using GBEWYFX (V := V) (ul := [u0, u1, f (i + 1)]) hp hs hleafB
  -- assembly
  refine ⟨hk3a, hbarA, hbarB, hbbA, hbbB, hk3b, hsubA, hsubB, hne, hcolA, hcolB,
    hleafA.2, hleafB.2, hleafB2.2, hleafA, hleafB, hleafB2,
    hd01i, hd02i, hd02s, hd12i, hd12s, hi01.le, hi02.le, hi02s.le, hi12.le, hi12s.le,
    hetai, hetas,
    hnnA, hnnB,
    LEAF_RANK_REUHADY V [u0, u1] w0 n f i hn hp hs hsize hnc hr, ?_⟩
  obtain ⟨y4, hy4a, hy4b, hy4c, hy4d, hy4e, hy4f⟩ :=
    WEDGE3_Y4 V f w0 n i u0 u1 (dist u0 u1) (dist u0 (f i))
      (dist u0 (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) hnl hn hp hs hnc hr
      hcey hno4 rfl rfl rfl rfl rfl
  exact ⟨y4, hy4a, hy4b, hy4c, hy4d, hy4e, fun h => hy4f h.1 h.2⟩

/-- HOL `real_model_gckb`. -/
theorem real_model_gckb (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, 0.606 ≤ azim_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_sum_azim`: the wedge dihedral sum is `2*pi`. -/
theorem real_model_sum_azim (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∑ i ∈ Finset.Icc 0 (n - 1), azim_mcell V f u0 u1 i = 2 * Real.pi := by
  sorry

/-! ### T4 展开波（2026-10-08）：leaf_rank 见证层 —— `LEAF_RANK_PROPS` 前提树
显式化（T 线 T4，PLAN.md §5；对齐 Assembly §2a' T1 先例与 SF31 debt-bridge 形：
冻结陈述签名不动，单根黑箱 sorry 分解为具名骨架节点 + 在库叶的显式装配）

  LEAF_RANK_PROPS（本件，真装配，冻结签名 2026-09-2x 一字未动）
  ├─ pkLeafRankCriticalEdge   ⬜ 临界边见证 + 负 gg 和（HOL Oxl_real.hl；
  │     子债：CELL_CLUSTER_ESTIMATE_REDUCE :2286 ⬜ + CELL_CLUSTER_N_LE_1
  │     :2449 ⬜ + LEAF_RANKING_LEMMA :1274 ✅（leaf-rank 波 2026-10-08 转真，
  │     债面收窄至 p25_leaf_azim_inj :1247 → PA18 FCHKUGT）；叶界
  │     S_LEAF_BOUNDED/FINITE :1382/:1429 ✅、s_leaf_collinear :1138 ✅、
  │     S_LEAF_SYM :1565 ✅）
  ├─ real_model_sum_azim      ⬜（本文件 :3139 在库 bank 叶——直接消费，
  │     B→T 会师位；G4/Flyspeck_constants.calc 认证口径）
  ├─ pkLeafRankAzimPointwise  ⬜ 楔形塌缩 azim_mcell = azim（新具名骨架；
  │     子债：MCELL_WEDGE_UNIQUE :1617 ⬜ + CC_3_PROPS :3086 ⬜（其结论含
  │     同款恒等式）+ c_4_azim_mcell_dih_y :2717 ⬜）
  ├─ cc_bool_model_data       ⬜（本文件 :2329 已具名叶——直接消费，会师位）
  └─ cc_prep_model_data       ⬜（本文件 :2338 已具名叶——直接消费，会师位）

债从 1 根黑箱变为 2 具名骨架 + 3 具名在库叶；三枚在库叶由纯 term 装配接入
（LEAF_RANK_PROPS 的前提面恰好覆盖它们的前提面）。
leaf-rank 波（2026-10-08，PA25 #4/#5 榜）：LEAF_RANKING_LEMMA 转真（引擎
STRICT_SORT_FINITE :539 ✅ + 模 n 环参数化），另转真装配级四件 S_LEAF_CARD2
:1951 ✅、LEAF_RANK_ONTO :1964 ✅、LEAF_IN_WEDGE_GE :1978 ✅、LEAF_DOMAIN
:2350 ✅；新残余债面 = p25_leaf_azim_inj（→FCHKUGT，PA18 车道）+
MCELL4_LEAF_S_LEAF（leaf-cell 链，LEAF2/LEAF3 已于 2026-10-12 转真）+
S_LEAF_IN_WEDGE_GE（已于 2026-10-12 转真，azim 链算术，HOL
OXLZLEZ3.hl:2279）+ RADV_ETAY（sphere.hl）。 -/

/-- T4 骨架 W1 `pkLeafRankCriticalEdge`：失败 cell-cluster 不等式的临界边
见证与 `leaf_rank` 参数化（含负 gg 和）。HOL Oxl_real.hl（CELL_CLUSTER_ESTIMATE
段的逐边化 + 临界茎选取）。
资产状态：**真缺口（装配级）**——逐边化（`CELL_CLUSTER_ESTIMATE_REDUCE`
:2286 ⬜）、退化茎非负和（`CELL_CLUSTER_N_LE_1` :2449 ⬜）两件上游落证后，
azim 环序参数化取 `LEAF_RANKING_LEMMA` :1274（leaf-rank 波已转真，其债面 =
`p25_leaf_azim_inj` :1247 → PA18 `FCHKUGT`）。
-- NEEDS: :2286 / :2449 按 HOL Oxl_real.hl 装配波展开（两件均在本文件内、
语义已成形）；:1208 位已由 leaf-rank 波清偿为 ✅（见 :1274）。 -/
theorem pkLeafRankCriticalEdge (V : Set V3) (hp : Packing V) (hs : saturated V)
    (hcc : ¬ cellClusterInequality V) (hnl : pack_nonlinear_non_ox3q1h) :
    ∃ u0 u1 n w0 f : _, 1 < n ∧ HasSizeP25 (s_leaf V [u0, u1]) n ∧ u0 ≠ u1 ∧
      hminus ≤ hl [u0, u1] ∧ hl [u0, u1] ≤ hplus ∧
      ¬ Collinear3 u0 u1 w0 ∧ leaf_rank V [u0, u1] w0 n f ∧
      u0 ∈ V ∧ u1 ∈ V ∧ periodic f n ∧
      (∀ j, leaf V [u0, u1, f j]) ∧ criticalEdgeY (dist u0 u1) ∧
      ∑ i ∈ Finset.Icc 0 (n - 1), gg_mcell V f u0 u1 i < 0 := by
  sorry

/-- T4 骨架 W2 `pkLeafRankAzimPointwise`：楔形二面角塌缩——wedge 内 Marchal
胞的 dihedral 和等于张角 `azim u0 u1 (f i) (f (i+1))`。HOL Oxl_real.hl。
资产状态：**真缺口**——`cc_4` 情形经 `c_4_azim_mcell_dih_y`(:2484 ⬜，
dih_y = 张角)，`¬cc_4` 情形 `CC_3_PROPS`(:2853 ⬜) 的结论已含本恒等式，
公共前提 `MCELL_WEDGE_UNIQUE`(:1512 ⬜)。
-- NEEDS: 上述三件 wedge 结构件落证后本件为分案装配（~60-100 行）。 -/
theorem pkLeafRankAzimPointwise (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, azim_mcell V f u0 u1 i = azim u0 u1 (f i) (f (i + 1)) := by
  sorry

/-- HOL `LEAF_RANK_PROPS`: the full leaf-rank extraction from a failing
cell-cluster inequality (the case-analysis engine).
T4 展开波（2026-10-08）：证明体由单根 `sorry` 换为上方具名骨架件与在库叶的
显式装配（冻结陈述签名不变）；债 = W1/W2 两具名骨架 + real_model_sum_azim /
cc_bool_model_data / cc_prep_model_data 三在库叶（会师位，见上层注记）。 -/
theorem LEAF_RANK_PROPS (V : Set V3) (hp : Packing V) (hs : saturated V)
    (hcc : ¬ cellClusterInequality V) (hnl : pack_nonlinear_non_ox3q1h) :
    ∃ u0 u1 n w0 f : _, 1 < n ∧ HasSizeP25 (s_leaf V [u0, u1]) n ∧ u0 ≠ u1 ∧
      hminus ≤ hl [u0, u1] ∧ hl [u0, u1] ≤ hplus ∧
      ¬ Collinear3 u0 u1 w0 ∧ leaf_rank V [u0, u1] w0 n f ∧
      u0 ∈ V ∧ u1 ∈ V ∧ periodic f n ∧
      (∀ j, leaf V [u0, u1, f j]) ∧ criticalEdgeY (dist u0 u1) ∧
      ∑ i ∈ Finset.Icc 0 (n - 1), gg_mcell V f u0 u1 i < 0 ∧
      ∑ i ∈ Finset.Icc 0 (n - 1), azim_mcell V f u0 u1 i = 2 * Real.pi ∧
      (∀ i, azim_mcell V f u0 u1 i = azim u0 u1 (f i) (f (i + 1))) ∧
      cc_bool_model_v11 (cc_data_v8 V f u0 u1) ∧
      cc_bool_prep_v11 (cc_data_v8 V f u0 u1) := by
  obtain ⟨u0, u1, n, w0, f, hn, hsize, hu0ne, hlo, hhi, hnc, hr, h0, h1, hper,
    hleaf, hcey, hneg⟩ := pkLeafRankCriticalEdge V hp hs hcc hnl
  refine ⟨u0, u1, n, w0, f, hn, hsize, hu0ne, hlo, hhi, hnc, hr, h0, h1, hper,
    hleaf, hcey, hneg, ?_, ?_, ?_, ?_⟩
  · -- 楔形二面角和 = 2π：在库 bank 叶 `real_model_sum_azim`（:2890）直接消费
    exact real_model_sum_azim V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr
  · -- 楔形塌缩恒等式：T4 骨架 W2
    exact pkLeafRankAzimPointwise V u0 u1 w0 n f hn hp hs hsize h0 h1 hper hnc
      hcey hr
  · -- cc_v11 布尔模型：在库数据叶 `cc_bool_model_data`（:2170）直接消费
    exact cc_bool_model_data V f w0 n u0 u1 hnl hn hp hs hsize h0 h1 hnc hcey hr
  · -- cc_v11 prep 模型：在库数据叶 `cc_prep_model_data`（:2179）直接消费
    exact cc_prep_model_data V f w0 n u0 u1 hn hp hs hnc hr

/-- HOL `real_model_ox3q1h_merge`: the ox3q1h certified 4-quarter bound. -/
theorem real_model_ox3q1h_merge (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ((Set.ncard (s_leaf V [u0, u1]) = 4 ∧ ∃ i, cc_4 V u0 u1 f i ∧
        2 * hminus ≤ dist (f i) (f (i + 1)) ∧
          dist (f i) (f (i + 1)) ≤ 2 * hplus ∧
        cc_4 V u0 u1 f (i + 1) ∧
          (dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) ∧
          dist u0 (f (i + 1 + 1)) < 2 * hminus ∧
          dist u1 (f (i + 1 + 1)) < 2 * hminus ∧
          dist (f (i + 1)) (f (i + 1 + 1)) < 2 * hminus ∧
        cc_4 V u0 u1 f (i + 2) ∧
          (dist u0 (f (i + 2)) < 2 * hminus ∧ dist u1 (f (i + 2)) < 2 * hminus) ∧
          dist u0 (f (i + 2 + 1)) < 2 * hminus ∧
          dist u1 (f (i + 2 + 1)) < 2 * hminus ∧
          dist (f (i + 2)) (f (i + 2 + 1)) < 2 * hminus ∧
        cc_4 V u0 u1 f (i + 3) ∧
          (dist u0 (f (i + 3)) < 2 * hminus ∧ dist u1 (f (i + 3)) < 2 * hminus) ∧
          dist u0 (f (i + 3 + 1)) < 2 * hminus ∧
          dist u1 (f (i + 3 + 1)) < 2 * hminus ∧
          dist (f (i + 3)) (f (i + 3 + 1)) < 2 * hminus) →
      0 ≤ ∑ i ∈ Finset.Icc 0 (n - 1), gg_mcell V f u0 u1 i) := by
  sorry

/-- 私件：`dihY` 的 (2 6)(3 5) 槽对称（PA20 `p20g_dihY_rev` 的本文件私拷——上游为
private 不可见，查重后无公开同件；`deltaX`/`deltaX4` 多项式恒等，自含完整证明）。 -/
private theorem p25m_dihY_rev (a b c d e f : ℝ) :
    dihY a b c d e f = dihY a f e d c b := by
  unfold dihY dihXf
  have h1 : deltaX (a * a) (f * f) (e * e) (d * d) (c * c) (b * b)
      = deltaX (a * a) (b * b) (c * c) (d * d) (e * e) (f * f) := by
    simp only [deltaX]; ring
  have h2 : deltaX4 (a * a) (f * f) (e * e) (d * d) (c * c) (b * b)
      = deltaX4 (a * a) (b * b) (c * c) (d * d) (e * e) (f * f) := by
    simp only [deltaX4]; ring
  simp only [h1, h2]

/-- 私件（mcell3 波 2026-10-12）：`¬ cc_4` 楔的 a-侧 3-胞见证包。`NO_4CELL_IMP_K3`
分派 `ccKe = 3`；叶性由 `leaf_rank`（`LEAF_RANK_S_LEAF` + `s_leaf` 展开）读出；
`cc_uh` 见证经 PA18 `cc_uh_exists` + `LIST_OF_CC_UH` +
`TRUNCATE_SIMPLEX_EXPLICIT_2` 注入定形（getD 三投影）；胞方程按 `ccCell`/`ccKe`
定义改写；非空性由 PA18 `CC_CELL_NOT_NULLSET` 给出。新代码自含完整证明，债面仅
继承 `NO_4CELL_IMP_K3` 骨架（HOL 同构：OXLZLEZ3 `CC_3_PROPS` 的NO_4CELL 前半）。 -/
private theorem p25m_cc3_wit (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i) :
    ccKe V [u0, u1, f i] = 3 ∧
      leaf V [u0, u1, f i] ∧
      barV V 3 (ccUh V [u0, u1, f i]) ∧
      ccUh V [u0, u1, f i] =
        [(ccUh V [u0, u1, f i]).getD 0 0, (ccUh V [u0, u1, f i]).getD 1 0,
          (ccUh V [u0, u1, f i]).getD 2 0, (ccUh V [u0, u1, f i]).getD 3 0] ∧
      (ccUh V [u0, u1, f i]).getD 0 0 = u0 ∧
      (ccUh V [u0, u1, f i]).getD 1 0 = u1 ∧
      (ccUh V [u0, u1, f i]).getD 2 0 = f i ∧
      ccCell V [u0, u1, f i] = mcell 3 V (ccUh V [u0, u1, f i]) ∧
      ¬ nullSet (ccCell V [u0, u1, f i]) := by
  have hd := NO_4CELL_IMP_K3 V (wedgeGe u0 u1 (f i) (f (i + 1))) [u0, u1] w0 n f i hp hs
    hr hnc rfl hn hno4
  obtain ⟨-, hk3, -, -, -⟩ := hd
  have hk3' : ccKe V [u0, u1, f i] = 3 := hk3
  have hmem := LEAF_RANK_S_LEAF V [u0, u1] w0 n f i hr
  have hleaf : leaf V [u0, u1, f i] := by
    have h2 := hmem
    simp only [s_leaf, Set.mem_setOf_eq] at h2
    exact h2.1
  have hbar : barV V 3 (ccUh V [u0, u1, f i]) :=
    (Classical.choose_spec (cc_uh_exists V [u0, u1, f i]) hp hs hleaf).1
  have htr : truncateSimplex 2 (ccUh V [u0, u1, f i]) = [u0, u1, f i] :=
    (Classical.choose_spec (cc_uh_exists V [u0, u1, f i]) hp hs hleaf).2.1
  have hlist := LIST_OF_CC_UH (V := V) (ul := [u0, u1, f i]) hs hp hleaf
  have htrI := htr
  rw [hlist, (TRUNCATE_SIMPLEX_EXPLICIT_2 _ _ _ _).2] at htrI
  obtain ⟨e0, e12⟩ := List.cons.inj htrI
  obtain ⟨e1, e2t⟩ := List.cons.inj e12
  obtain ⟨e2, -⟩ := List.cons.inj e2t
  refine ⟨hk3', hleaf, hbar, hlist, e0, e1, e2, ?_,
    CC_CELL_NOT_NULLSET (V := V) (ul := [u0, u1, f i]) hp hs hleaf⟩
  unfold ccCell
  rw [hk3']

/-- 私件（mcell3 波 2026-10-12）：`¬ cc_4` 楔的 b-侧（反序茎）3-胞见证包。同
`p25m_cc3_wit`，取 `NO_4CELL_IMP_K3` 的第一分量；叶性经 `S_LEAF_SYM` 换茎。 -/
private theorem p25m_cc3_wit_b (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i) :
    ccKe V [u1, u0, f (i + 1)] = 3 ∧
      leaf V [u1, u0, f (i + 1)] ∧
      barV V 3 (ccUh V [u1, u0, f (i + 1)]) ∧
      ccUh V [u1, u0, f (i + 1)] =
        [(ccUh V [u1, u0, f (i + 1)]).getD 0 0, (ccUh V [u1, u0, f (i + 1)]).getD 1 0,
          (ccUh V [u1, u0, f (i + 1)]).getD 2 0, (ccUh V [u1, u0, f (i + 1)]).getD 3 0] ∧
      (ccUh V [u1, u0, f (i + 1)]).getD 0 0 = u1 ∧
      (ccUh V [u1, u0, f (i + 1)]).getD 1 0 = u0 ∧
      (ccUh V [u1, u0, f (i + 1)]).getD 2 0 = f (i + 1) ∧
      ccCell V [u1, u0, f (i + 1)] = mcell 3 V (ccUh V [u1, u0, f (i + 1)]) ∧
      ¬ nullSet (ccCell V [u1, u0, f (i + 1)]) := by
  have hd := NO_4CELL_IMP_K3 V (wedgeGe u0 u1 (f i) (f (i + 1))) [u0, u1] w0 n f i hp hs
    hr hnc rfl hn hno4
  obtain ⟨hk3b, -, -, -, -⟩ := hd
  have hk3b' : ccKe V [u1, u0, f (i + 1)] = 3 := hk3b
  have hmemB := LEAF_RANK_S_LEAF V [u0, u1] w0 n f (i + 1) hr
  have hleafB : leaf V [u1, u0, f (i + 1)] := by
    have h2 : f (i + 1) ∈ s_leaf V [u1, u0] := by
      rw [S_LEAF_SYM V u0 u1 hp hs]
      exact hmemB
    have h3 := h2
    simp only [s_leaf, Set.mem_setOf_eq] at h3
    exact h3.1
  have hbarB : barV V 3 (ccUh V [u1, u0, f (i + 1)]) :=
    (Classical.choose_spec (cc_uh_exists V [u1, u0, f (i + 1)]) hp hs hleafB).1
  have htrB : truncateSimplex 2 (ccUh V [u1, u0, f (i + 1)]) = [u1, u0, f (i + 1)] :=
    (Classical.choose_spec (cc_uh_exists V [u1, u0, f (i + 1)]) hp hs hleafB).2.1
  have hlistB := LIST_OF_CC_UH (V := V) (ul := [u1, u0, f (i + 1)]) hs hp hleafB
  have htrI := htrB
  rw [hlistB, (TRUNCATE_SIMPLEX_EXPLICIT_2 _ _ _ _).2] at htrI
  obtain ⟨e0, e12⟩ := List.cons.inj htrI
  obtain ⟨e1, e2t⟩ := List.cons.inj e12
  obtain ⟨e2, -⟩ := List.cons.inj e2t
  refine ⟨hk3b', hleafB, hbarB, hlistB, e0, e1, e2, ?_,
    CC_CELL_NOT_NULLSET (V := V) (ul := [u1, u0, f (i + 1)]) hp hs hleafB⟩
  unfold ccCell
  rw [hk3b']

/-- HOL `mcell3_gammaX_gamma3f`. -/
theorem mcell3_gammaX_gamma3f (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
    (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i) :
    gammaX V (ccCell V [u0, u1, f i]) lmfun =
      gamma3f (dist u0 u1) (dist u0 (f i)) (dist u1 (f i)) (Real.sqrt 2) lmfun := by
  -- HOL OXLZLEZ3.hl:6242：CC_3_PROPS 分派 + Tskajxy_lemmas.gammaX_gamma3f 装配。
  -- Lean 侧：见证包私件 + PA20 `gammaX_gamma3f`（经 PA21 传递可见）第 8 合取支，
  -- 收口用 PA21 `mi_gamma3f_sym` 的 3-循环×交换把 (y4,y5,y6) 旋到目标次序。
  obtain ⟨-, hleaf, hbar, hlist, e0, e1, e2, hcell, hnn⟩ :=
    p25m_cc3_wit V u0 u1 w0 n f i hp hs hr hnc hn hno4
  have hres := gammaX_gamma3f (V := V) (X := ccCell V [u0, u1, f i])
    (ul := ccUh V [u0, u1, f i])
    (u0 := (ccUh V [u0, u1, f i]).getD 0 0) (u1 := (ccUh V [u0, u1, f i]).getD 1 0)
    (u2 := (ccUh V [u0, u1, f i]).getD 2 0) (u3 := (ccUh V [u0, u1, f i]).getD 3 0)
    (y4 := dist u1 (f i)) (y5 := dist u0 (f i)) (y6 := dist u0 u1)
    hs hp hbar hcell hnn hlist (by rw [e1, e2]) (by rw [e0, e2]) (by rw [e0, e1])
  exact hres.2.2.2.2.2.2.2.trans (by
    calc gamma3f (dist u1 (f i)) (dist u0 (f i)) (dist u0 u1) (Real.sqrt 2) lmfun
        = gamma3f (dist u0 (f i)) (dist u0 u1) (dist u1 (f i)) (Real.sqrt 2) lmfun :=
          (mi_gamma3f_sym _ _ _).2
      _ = gamma3f (dist u0 u1) (dist u1 (f i)) (dist u0 (f i)) (Real.sqrt 2) lmfun :=
          (mi_gamma3f_sym _ _ _).2
      _ = gamma3f (dist u0 u1) (dist u0 (f i)) (dist u1 (f i)) (Real.sqrt 2) lmfun :=
          (mi_gamma3f_sym _ _ _).1)

/-- HOL `mcell3_dihX_dih_y`. -/
theorem mcell3_dihX_dih_y (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
    (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i) :
    dihX V (ccCell V [u0, u1, f i]) (u0, u1) =
      dihY (dist u0 u1) (dist u0 (f i)) (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2)
        (dist u1 (f i)) := by
  -- HOL OXLZLEZ3.hl:6281：同一装配，取 PA20 `gammaX_gamma3f` 第 5 合取支
  -- （`dihX (u0,u1)` 槽），(2 6) 槽差由 `p25m_dihY_rev` 吸收。
  obtain ⟨-, hleaf, hbar, hlist, e0, e1, e2, hcell, hnn⟩ :=
    p25m_cc3_wit V u0 u1 w0 n f i hp hs hr hnc hn hno4
  have hres := gammaX_gamma3f (V := V) (X := ccCell V [u0, u1, f i])
    (ul := ccUh V [u0, u1, f i])
    (u0 := (ccUh V [u0, u1, f i]).getD 0 0) (u1 := (ccUh V [u0, u1, f i]).getD 1 0)
    (u2 := (ccUh V [u0, u1, f i]).getD 2 0) (u3 := (ccUh V [u0, u1, f i]).getD 3 0)
    (y4 := dist u1 (f i)) (y5 := dist u0 (f i)) (y6 := dist u0 u1)
    hs hp hbar hcell hnn hlist (by rw [e1, e2]) (by rw [e0, e2]) (by rw [e0, e1])
  have dX := hres.2.2.2.2.1
  rw [e0, e1] at dX
  rw [dX]
  exact p25m_dihY_rev _ _ _ _ _ _

/-- HOL `mcell3_gammaXb_gamma3f`. -/
theorem mcell3_gammaXb_gamma3f (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
    (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i) :
    gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun =
      gamma3f (dist u0 u1) (dist u0 (f (i + 1))) (dist u1 (f (i + 1)))
        (Real.sqrt 2) lmfun := by
  -- HOL OXLZLEZ3.hl:6316：b-侧（反序茎）见证包 + PA20 `gammaX_gamma3f` 第 8 合取支；
  -- `dist u1 u0` 由 `dist_comm` 归位后 `mi_gamma3f_sym` 两次 3-循环收口。
  obtain ⟨-, hleafB, hbarB, hlistB, e0, e1, e2, hcellB, hnnB⟩ :=
    p25m_cc3_wit_b V u0 u1 w0 n f i hp hs hr hnc hn hno4
  have hres := gammaX_gamma3f (V := V) (X := ccCell V [u1, u0, f (i + 1)])
    (ul := ccUh V [u1, u0, f (i + 1)])
    (u0 := (ccUh V [u1, u0, f (i + 1)]).getD 0 0)
    (u1 := (ccUh V [u1, u0, f (i + 1)]).getD 1 0)
    (u2 := (ccUh V [u1, u0, f (i + 1)]).getD 2 0)
    (u3 := (ccUh V [u1, u0, f (i + 1)]).getD 3 0)
    (y4 := dist u0 (f (i + 1))) (y5 := dist u1 (f (i + 1))) (y6 := dist u1 u0)
    hs hp hbarB hcellB hnnB hlistB (by rw [e1, e2]) (by rw [e0, e2]) (by rw [e0, e1])
  have hx := hres.2.2.2.2.2.2.2
  rw [dist_comm u1 u0] at hx
  exact hx.trans (by
    calc gamma3f (dist u0 (f (i + 1))) (dist u1 (f (i + 1))) (dist u0 u1) (Real.sqrt 2) lmfun
        = gamma3f (dist u1 (f (i + 1))) (dist u0 u1) (dist u0 (f (i + 1))) (Real.sqrt 2) lmfun :=
          (mi_gamma3f_sym _ _ _).2
      _ = gamma3f (dist u0 u1) (dist u0 (f (i + 1))) (dist u1 (f (i + 1))) (Real.sqrt 2) lmfun :=
          (mi_gamma3f_sym _ _ _).2)

/-- HOL `mcell3_dihXb_dih_y`. -/
theorem mcell3_dihXb_dih_y (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
    (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i) :
    dihX V (ccCell V [u1, u0, f (i + 1)]) (u0, u1) =
      dihY (dist u0 u1) (dist u0 (f (i + 1))) (Real.sqrt 2) (Real.sqrt 2)
        (Real.sqrt 2) (dist u1 (f (i + 1))) := by
  -- HOL OXLZLEZ3.hl:6353：b-侧装配 + PA20 第 5 合取支给的是 (u1,u0) 槽，目标槽
  -- (u0,u1) 经 PA15 `DIHX_SYM`（在库叶，债走账本）翻转；`{u0,u1} ∈ edgeX` 由
  -- `HDTFNFZ`+`LEPJBDJ` 的 VX 刻画与 `collinear_pair`（茎点不等）现场验证。
  obtain ⟨-, hleafB, hbarB, hlistB, e0, e1, e2, hcellB, hnnB⟩ :=
    p25m_cc3_wit_b V u0 u1 w0 n f i hp hs hr hnc hn hno4
  have hu0ne : u0 ≠ u1 := by
    intro h
    apply hnc
    rw [h]
    show Collinear ℝ ({u1, u1, w0} : Set V3)
    have hset : ({u1, u1, w0} : Set V3) = {u1, w0} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ u1 w0
  have hne : mcell 3 V (ccUh V [u1, u0, f (i + 1)]) ≠ ∅ := by
    intro h0
    apply hnnB
    rw [hcellB, h0]
    exact measure_empty
  have hVXeq : VX V (ccCell V [u1, u0, f (i + 1)]) =
      V ∩ ccCell V [u1, u0, f (i + 1)] :=
    HDTFNFZ (v := u0) hs hp hbarB hcellB hnnB
  have hcap : V ∩ ccCell V [u1, u0, f (i + 1)]
      = setOfList (truncateSimplex 2 (ccUh V [u1, u0, f (i + 1)])) := by
    rw [hcellB]
    exact LEPJBDJ V (ccUh V [u1, u0, f (i + 1)]) 3 hs hp hbarB (by omega) (by omega) hne
  have hsetB : setOfList (truncateSimplex 2 (ccUh V [u1, u0, f (i + 1)]))
      = ({u1, u0, f (i + 1)} : Set V3) := by
    rw [hlistB, (TRUNCATE_SIMPLEX_EXPLICIT_2 _ _ _ _).2, e0, e1, e2]
    ext z
    simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hu0V : u0 ∈ VX V (ccCell V [u1, u0, f (i + 1)]) := by
    rw [hVXeq, hcap, hsetB]
    simp
  have hu1V : u1 ∈ VX V (ccCell V [u1, u0, f (i + 1)]) := by
    rw [hVXeq, hcap, hsetB]
    simp
  have hed : ({u0, u1} : Set V3) ∈ edgeX V (ccCell V [u1, u0, f (i + 1)]) :=
    ⟨u0, u1, rfl, hu0V, hu1V, hu0ne⟩
  have hms : mcellSet V (ccCell V [u1, u0, f (i + 1)]) := CC_CELL_IN_MCELL_SET hs hp hleafB
  have dSymm := DIHX_SYM V (ccCell V [u1, u0, f (i + 1)]) u0 u1 hp hs hms hed
  have hres := gammaX_gamma3f (V := V) (X := ccCell V [u1, u0, f (i + 1)])
    (ul := ccUh V [u1, u0, f (i + 1)])
    (u0 := (ccUh V [u1, u0, f (i + 1)]).getD 0 0)
    (u1 := (ccUh V [u1, u0, f (i + 1)]).getD 1 0)
    (u2 := (ccUh V [u1, u0, f (i + 1)]).getD 2 0)
    (u3 := (ccUh V [u1, u0, f (i + 1)]).getD 3 0)
    (y4 := dist u0 (f (i + 1))) (y5 := dist u1 (f (i + 1))) (y6 := dist u1 u0)
    hs hp hbarB hcellB hnnB hlistB (by rw [e1, e2]) (by rw [e0, e2]) (by rw [e0, e1])
  have dXB := hres.2.2.2.2.1
  rw [e0, e1] at dXB
  rw [dSymm, dXB, dist_comm u1 u0]

/-- HOL `MCELL3_EDGE_EXPLICIT`. -/
theorem MCELL3_EDGE_EXPLICIT (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hs : saturated V) (hn : ¬ nullSet (mcell3 V [u0, u1, u2, u3]))
    (hb : barV V 3 [u0, u1, u2, u3]) :
    edgeX V (mcell3 V [u0, u1, u2, u3]) =
      {{u0, u1}, {u0, u2}, {u1, u2}} := by
  -- PA20 mcell3 章 `hedges` 同款骨架：barV 谱系给出茎点两两不等（voronoiNondg
  -- 长度差矛盾），`HDTFNFZ`+`LEPJBDJ` 把 VX 钉死为截断三元组，`edgeX` 逐对枚举。
  have hv1 : voronoiNondg V [u0, u1] := hb.2 [u0, u1] ⟨⟨[u2, u3], rfl⟩, by simp⟩
  have hv0 : voronoiNondg V [u0] := hb.2 [u0] ⟨⟨[u1, u2, u3], rfl⟩, by simp⟩
  have hv2 : voronoiNondg V [u0, u1, u2] := hb.2 [u0, u1, u2] ⟨⟨[u3], rfl⟩, by simp⟩
  have hd01 : u0 ≠ u1 := by
    intro h
    refine p25m_vn_contra hv1 hv0 ?_ ?_
    · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
    · simp
  have hd02 : u0 ≠ u2 := by
    intro h
    refine p25m_vn_contra hv2 hv1 ?_ ?_
    · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
    · simp
  have hd12 : u1 ≠ u2 := by
    intro h
    refine p25m_vn_contra hv2 hv1 ?_ ?_
    · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
    · simp
  have hne : mcell3 V [u0, u1, u2, u3] ≠ ∅ := by
    intro h0
    apply hn
    rw [h0]
    exact measure_empty
  have hVX : VX V (mcell3 V [u0, u1, u2, u3])
      = setOfList (truncateSimplex 2 [u0, u1, u2, u3]) := by
    have h1 : VX V (mcell3 V [u0, u1, u2, u3])
        = V ∩ mcell3 V [u0, u1, u2, u3] :=
      HDTFNFZ (v := u0) (k := 3) hs hp hb rfl hn
    rw [h1, show mcell3 V [u0, u1, u2, u3] = mcell 3 V [u0, u1, u2, u3] from rfl,
      LEPJBDJ V [u0, u1, u2, u3] 3 hs hp hb (by omega) (by omega) hne]
  have htr : setOfList (truncateSimplex 2 [u0, u1, u2, u3]) = ({u0, u1, u2} : Set V3) := by
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2]
    ext z
    simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hVX3 : ∀ z : V3, z ∈ VX V (mcell3 V [u0, u1, u2, u3]) ↔
      z ∈ ({u0, u1, u2} : Set V3) := by
    intro z
    rw [hVX, htr]
  have pEq : ∀ (p q : V3), ({p, q} : Set V3) = {q, p} := by
    intro p q
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hpair : ∀ p q : V3, p ∈ ({u0, u1, u2} : Set V3) →
      q ∈ ({u0, u1, u2} : Set V3) → p ≠ q →
      ({p, q} : Set V3) = ({u0, u1} : Set V3) ∨ ({p, q} : Set V3) = {u0, u2} ∨
        ({p, q} : Set V3) = {u1, u2} := by
    intro p q hp hq hpq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with ha3 | ha3 | ha3 <;> rcases hq with hb3 | hb3 | hb3
    · exact absurd (ha3.trans hb3.symm) hpq
    · rw [ha3, hb3]; exact Or.inl rfl
    · rw [ha3, hb3]; exact Or.inr (Or.inl rfl)
    · rw [ha3, hb3]; exact Or.inl (pEq u1 u0)
    · exact absurd (ha3.trans hb3.symm) hpq
    · rw [ha3, hb3]; exact Or.inr (Or.inr rfl)
    · rw [ha3, hb3]; exact Or.inr (Or.inl (pEq u2 u0))
    · rw [ha3, hb3]; exact Or.inr (Or.inr (pEq u2 u1))
    · exact absurd (ha3.trans hb3.symm) hpq
  ext e
  simp only [edgeX, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, rfl, ha, hbv, hab⟩
    rcases hpair a b ((hVX3 a).mp ha) ((hVX3 b).mp hbv) hab with h | h | h
    · simp only [h]
      exact Set.mem_insert ({u0, u1} : Set V3) _
    · simp only [h]
      exact Set.mem_insert_of_mem (y := ({u0, u1} : Set V3))
        (Set.mem_insert ({u0, u2} : Set V3) _)
    · simp [h]
  · rintro (rfl | rfl | rfl)
    · exact ⟨u0, u1, rfl, (hVX3 u0).mpr (by simp), (hVX3 u1).mpr (by simp), hd01⟩
    · exact ⟨u0, u2, rfl, (hVX3 u0).mpr (by simp), (hVX3 u2).mpr (by simp), hd02⟩
    · exact ⟨u1, u2, rfl, (hVX3 u1).mpr (by simp), (hVX3 u2).mpr (by simp), hd12⟩

/-- HOL `critical_weight1`. -/
theorem critical_weight1 (V : Set V3) (u0 u1 u2 : V3)
    (hcey : criticalEdgeY (dist u0 u1)) (hd1 : dist u0 u2 < 2 * hminus)
    (hd2 : dist u1 u2 < 2 * hminus) (hk : ccKe V [u0, u1, u2] = 3)
    (hp : Packing V) (hs : saturated V)
    (hb : barV V 3 (ccUh V [u0, u1, u2])) (hl' : leaf V [u0, u1, u2])
    (hnn : ¬ nullSet (ccCell V [u0, u1, u2])) :
    criticalWeight V (ccCell V [u0, u1, u2]) = 1 := by
  sorry

/-- HOL `critical_weight1a`. -/
theorem critical_weight1a (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (hno4 : ¬ cc_4 V u0 u1 f i)
    (hd : dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) :
    criticalWeight V (ccCell V [u0, u1, f i]) = 1 := by
  sorry

/-- HOL `critical_weight1b`. -/
theorem critical_weight1b (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (hno4 : ¬ cc_4 V u0 u1 f i)
    (hd : dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) :
    criticalWeight V (ccCell V [u1, u0, f (i + 1)]) = 1 := by
  sorry

/-- HOL `real_model_quqy`. -/
theorem real_model_quqy (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
            dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
            dist (f i) (f (i + 1)) < 2 * hminus) ∧
          ¬ cc_4 V u0 u1 f (i + 1)) →
      0 ≤ gg_mcell V f u0 u1 i +
        gammaX V (ccCell V [u0, u1, f (i + 1)]) lmfun *
          criticalWeight V (ccCell V [u0, u1, f (i + 1)]) := by
  sorry

/-- HOL `real_model_quqy_sym`. -/
theorem real_model_quqy_sym (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f (i + 1) ∧
            (dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) ∧
            dist u0 (f (i + 1 + 1)) < 2 * hminus ∧
            dist u1 (f (i + 1 + 1)) < 2 * hminus ∧
            dist (f (i + 1)) (f (i + 1 + 1)) < 2 * hminus) ∧
          ¬ cc_4 V u0 u1 f i) →
      0 ≤ gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
          criticalWeight V (ccCell V [u1, u0, f (i + 1)]) +
        gg_mcell V f u0 u1 (i + 1) := by
  sorry

/-- HOL `real_model_ztg4`. -/
theorem real_model_ztg4 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      a_spine5 + b_spine5 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_azim1`. -/
theorem real_model_azim1 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
        dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
        dist (f i) (f (i + 1)) < 2 * hminus →
      -0.0659 + 0.042 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_gaz4`. -/
theorem real_model_gaz4 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
        dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
        dist (f i) (f (i + 1)) < 2 * hminus →
      -0.0142852 + 0.00609451 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_gaz6`. -/
theorem real_model_gaz6 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
        dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
        dist (f i) (f (i + 1)) < 2 * hminus →
      0.161517 - 0.119482 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_gamma_qx`. -/
theorem real_model_gamma_qx (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
          dist (f i) (f (i + 1)) < 2 * hminus) →
      0 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_g_qxd`. -/
theorem real_model_g_qxd (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, (cc_4 V u0 u1 f i ∧
        ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
            dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
            dist (f i) (f (i + 1)) < 2 * hminus)) →
      2.3 < azim_mcell V f u0 u1 i → 0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `wtcount6_y_sym23` (the 2-3 swap symmetry of the weight count). -/
theorem wtcount6_y_sym23 (y1 y2 y3 y4 y5 y6 : ℝ) :
    wtcount6Y y1 y2 y3 y4 y5 y6 = wtcount6Y y1 y3 y2 y4 y6 y5 := by
  unfold wtcount6Y wtcount3Y
  ring

/-- HOL `wtcount6_y_sym26` (the 2-6/3-5 swap symmetry of the weight count). -/
theorem wtcount6_y_sym26 (y1 y2 y3 y4 y5 y6 : ℝ) :
    wtcount6Y y1 y2 y3 y4 y5 y6 = wtcount6Y y1 y6 y5 y4 y3 y2 := by
  unfold wtcount6Y wtcount3Y
  ring

/-- HOL `beta_bumpA_y_sym23`. -/
theorem beta_bumpA_y_sym23 (y1 y2 y3 y4 y5 y6 : ℝ) :
    beta_bumpA_yP25 y1 y2 y3 y4 y5 y6 = beta_bumpA_yP25 y1 y3 y2 y4 y6 y5 := by
  sorry

/-- HOL `real_model_gamma10`. -/
theorem real_model_gamma10 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
                dist u0 (f (i + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1)) < 2 * hminus ∧
                dist (f i) (f (i + 1)) < 2 * hminus)) ∧
          ((dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
            dist u0 (f (i + 1)) < 2 * hminus ∧
            dist u1 (f (i + 1)) < 2 * hminus) ∧
          ¬ cc_4 V u0 u1 f (i + 1)) →
      0.0057 ≤ gg_mcell V f u0 u1 i +
        gammaX V (ccCell V [u0, u1, f (i + 1)]) lmfun *
          criticalWeight V (ccCell V [u0, u1, f (i + 1)]) := by
  sorry

/-- HOL `real_model_gamma11`. -/
theorem real_model_gamma11 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f (i + 1) ∧
            ¬ (dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
                dist u0 (f (i + 1 + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1 + 1)) < 2 * hminus ∧
                dist (f (i + 1)) (f (i + 1 + 1)) < 2 * hminus)) ∧
          ((dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) ∧
            dist u0 (f (i + 1 + 1)) < 2 * hminus ∧
            dist u1 (f (i + 1 + 1)) < 2 * hminus) ∧
          ¬ cc_4 V u0 u1 f i) →
      0.0057 ≤ gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
          criticalWeight V (ccCell V [u1, u0, f (i + 1)]) +
        gg_mcell V f u0 u1 (i + 1) := by
  sorry

/-- HOL `leaf_CIHTIUM` (the certified bound makes long leaves impossible). -/
theorem leaf_CIHTIUM (V : Set V3) (u0 u1 u2 : V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hp : Packing V) (hs : saturated V) (hl' : leaf V [u0, u1, u2])
    (hcey : criticalEdgeY (dist u0 u1)) (hd1 : 2 * hminus ≤ dist u0 u2)
    (hd2 : 2 * hminus ≤ dist u1 u2) : False := by
  sorry

/-- HOL `gamma4fgcy_sym26`.  The `delta_x`/`delta_x4`/`dih_y` family is
invariant under the edge-endpoint swap `(2 6) (3 5)` (vertex swap `v0 ↔ v1`)
and under the face swap `(2 3) (5 6)` (vertex swap `v2 ↔ v3`); both are
polynomial identities on the bodies, and the four `solY` solid angles plus
the six `dihY`-weighted edge terms of `vol4f` then match term by term. -/
theorem gamma4fgcy_sym26 (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) :
    gamma4fgcyP25 y1 y2 y3 y4 y5 y6 f = gamma4fgcyP25 y1 y6 y5 y4 y3 y2 f := by
  have hD1 : ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      deltaX x1 x2 x3 x4 x5 x6 = deltaX x1 x6 x5 x4 x3 x2 := by
    intro x1 x2 x3 x4 x5 x6; unfold deltaX; ring
  have hD2 : ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      deltaX x1 x2 x3 x4 x5 x6 = deltaX x1 x3 x2 x4 x6 x5 := by
    intro x1 x2 x3 x4 x5 x6; unfold deltaX; ring
  have hD3 : ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      deltaX4 x1 x2 x3 x4 x5 x6 = deltaX4 x1 x6 x5 x4 x3 x2 := by
    intro x1 x2 x3 x4 x5 x6; unfold deltaX4; ring
  have hD4 : ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      deltaX4 x1 x2 x3 x4 x5 x6 = deltaX4 x1 x3 x2 x4 x6 x5 := by
    intro x1 x2 x3 x4 x5 x6; unfold deltaX4; ring
  have hdy26 : ∀ a b c d e g : ℝ, dihY a b c d e g = dihY a g e d c b := by
    intro a b c d e g
    show dihXf (a * a) (b * b) (c * c) (d * d) (e * e) (g * g) =
      dihXf (a * a) (g * g) (e * e) (d * d) (c * c) (b * b)
    unfold dihXf
    rw [hD1 (a * a) (b * b) (c * c) (d * d) (e * e) (g * g),
      hD3 (a * a) (b * b) (c * c) (d * d) (e * e) (g * g)]
  have hdy23 : ∀ a b c d e g : ℝ, dihY a b c d e g = dihY a c b d g e := by
    intro a b c d e g
    show dihXf (a * a) (b * b) (c * c) (d * d) (e * e) (g * g) =
      dihXf (a * a) (c * c) (b * b) (d * d) (g * g) (e * e)
    unfold dihXf
    rw [hD2 (a * a) (b * b) (c * c) (d * d) (e * e) (g * g),
      hD4 (a * a) (b * b) (c * c) (d * d) (e * e) (g * g)]
  have hvol : volY y1 y2 y3 y4 y5 y6 = volY y1 y6 y5 y4 y3 y2 := by
    unfold volY volXf
    rw [hD1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)]
  have hsol : solY y1 y6 y5 y4 y3 y2 + solY y1 y3 y2 y4 y6 y5 +
      solY y4 y3 y5 y1 y6 y2 + solY y4 y6 y2 y1 y3 y5 =
    solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
      solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3 := by
    unfold solY
    rw [hdy26 y1 y6 y5 y4 y3 y2, hdy23 y6 y5 y1 y3 y2 y4, hdy23 y5 y1 y6 y2 y4 y3,
      hdy26 y1 y3 y2 y4 y6 y5, hdy23 y3 y2 y1 y6 y5 y4, hdy23 y2 y1 y3 y5 y4 y6,
      hdy23 y4 y3 y5 y1 y6 y2, hdy23 y3 y5 y4 y6 y2 y1, hdy23 y5 y4 y3 y2 y1 y6,
      hdy23 y4 y6 y2 y1 y3 y5, hdy23 y6 y2 y4 y3 y5 y1, hdy23 y2 y4 y6 y5 y1 y3]
    ring
  unfold gamma4fgcyP25 vol4fP25
  rw [hvol, hsol,
    hdy26 y1 y6 y5 y4 y3 y2,          -- edge y1 term
    hdy23 y6 y5 y1 y3 y2 y4,          -- edge y6 term
    hdy23 y4 y5 y3 y1 y2 y6,          -- edge y4 term
    hdy23 y2 y1 y3 y5 y4 y6]          -- edge y2 term
  ring

/-- HOL `gamma4fgcy_POS`. -/
theorem gamma4fgcy_POS (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
    (hrad : rad2YP25 y1 y2 y3 y4 y5 y6 < 2) (hcey : criticalEdgeY y1)
    (hnot : ¬ (y2 < 2 * hminus ∧ y3 < 2 * hminus ∧ y4 < 2 * hminus ∧
        y5 < 2 * hminus ∧ y6 < 2 * hminus))
    (hb2 : 2 ≤ y2) (hb2' : y2 ≤ Real.sqrt 8) (hb3 : 2 ≤ y3) (hb3' : y3 ≤ Real.sqrt 8)
    (hb4 : 2 ≤ y4) (hb4' : y4 ≤ Real.sqrt 8) (hb5 : 2 ≤ y5) (hb5' : y5 ≤ Real.sqrt 8)
    (hb6 : 2 ≤ y6) (hb6' : y6 ≤ Real.sqrt 8) :
    0 < gamma4fgcyP25 y1 y2 y3 y4 y5 y6 lmfun := by
  sorry

/-- HOL `real_model_gamma8`. -/
theorem real_model_gamma8 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
                dist u0 (f (i + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1)) < 2 * hminus ∧
                dist (f i) (f (i + 1)) < 2 * hminus)) ∧
          (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          ¬ (dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus)) →
      0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_gamma8b`. -/
theorem real_model_gamma8b (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
                dist u0 (f (i + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1)) < 2 * hminus ∧
                dist (f i) (f (i + 1)) < 2 * hminus)) ∧
          (dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) ∧
          ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus)) →
      0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_gaz9`. -/
theorem real_model_gaz9 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
                dist u0 (f (i + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1)) < 2 * hminus ∧
                dist (f i) (f (i + 1)) < 2 * hminus)) ∧
          (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) →
      0.213849 - 0.119482 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_azim2`. -/
theorem real_model_azim2 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
                dist u0 (f (i + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1)) < 2 * hminus ∧
                dist (f i) (f (i + 1)) < 2 * hminus)) ∧
          ((dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
            dist u0 (f (i + 1)) < 2 * hminus ∧
            dist u1 (f (i + 1)) < 2 * hminus) ∧
          2 * hplus < dist (f i) (f (i + 1))) →
      0.00457511 + 0.00609451 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `CC_3_SUM_SET`: the 3-cell wedge cell set splits into the two
cc-cells plus the rest. -/
theorem CC_3_SUM_SET (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hno4 : ¬ cc_4 V u0 u1 f i)
    (hnc : ¬ Collinear3 u0 u1 w0) (hcey : criticalEdgeY (dist u0 u1))
    (hr : leaf_rank V [u0, u1] w0 n f) :
    {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 (f i) (f (i + 1))} =
      insert (ccCell V [u0, u1, f i]) (insert (ccCell V [u1, u0, f (i + 1)])
        {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
          X ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
          X ≠ ccCell V [u0, u1, f i] ∧ X ≠ ccCell V [u1, u0, f (i + 1)]}) := by
  sorry

/-- HOL `CC_3_SUM_fn`: the corresponding sum split. -/
theorem CC_3_SUM_fn (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (fn : Set V3 → ℝ) (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hno4 : ¬ cc_4 V u0 u1 f i)
    (hnc : ¬ Collinear3 u0 u1 w0) (hcey : criticalEdgeY (dist u0 u1))
    (hr : leaf_rank V [u0, u1] w0 n f) :
    setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 (f i) (f (i + 1))} fn =
      fn (ccCell V [u0, u1, f i]) + fn (ccCell V [u1, u0, f (i + 1)]) +
        setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
          X ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
          X ≠ ccCell V [u0, u1, f i] ∧ X ≠ ccCell V [u1, u0, f (i + 1)]} fn := by
  sorry

/-- HOL `EDGE_IMP_K23`: every wedge cell over the stem edge is a 2- or
3-cell. -/
theorem EDGE_IMP_K23 (V : Set V3) (X : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hno4 : ¬ cc_4 V u0 u1 f i)
    (hnc : ¬ Collinear3 u0 u1 w0) (hcey : criticalEdgeY (dist u0 u1))
    (hr : leaf_rank V [u0, u1] w0 n f) (hm : mcellSet V X)
    (he : {u0, u1} ∈ edgeX V X)
    (hX : X ⊆ wedgeGe u0 u1 (f i) (f (i + 1))) :
    ∃ k v1 v2, barV V 3 [u0, u1, v1, v2] ∧ (k = 2 ∨ k = 3) ∧
      X = mcell k V [u0, u1, v1, v2] := by
  sorry

/-- HOL `CC_2_PROPS`. -/
theorem CC_2_PROPS (V : Set V3) (X : Set V3) (u0 u1 : V3) (vl : List V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hcey : criticalEdgeY (dist u0 u1)) (hX : X = mcell2 V vl)
    (he : {u0, u1} ∈ edgeX V X) (hb : barV V 3 vl) :
    ¬ nullSet X ∧
      gammaX V X lmfun =
        gamma2_x_div_azim_v2 (h0cut (dist u0 u1)) (dist u0 u1 * dist u0 u1) *
          dihX V X (u0, u1) ∧
      0 < dihX V X (u0, u1) ∧
      0.008 * dihX V X (u0, u1) < gammaX V X lmfun := by
  sorry

/-- HOL `MCELL2_CRITICAL_WEIGHT1`. -/
theorem MCELL2_CRITICAL_WEIGHT1 (V : Set V3) (X : Set V3) (u0 u1 : V3)
    (vl : List V3) (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V)
    (hs : saturated V) (hcey : criticalEdgeY (dist u0 u1))
    (hX : X = mcell2 V vl) (he : {u0, u1} ∈ edgeX V X) (hb : barV V 3 vl) :
    criticalWeight V X = 1 := by
  sorry

/-- HOL `MCELL3_CRITICAL_WEIGHT`. -/
theorem MCELL3_CRITICAL_WEIGHT (V : Set V3) (X : Set V3) (u0 u1 v1 v2 : V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hcey : criticalEdgeY (dist u0 u1)) (hX : X = mcell3 V [u0, u1, v1, v2])
    (he : {u0, u1} ∈ edgeX V X) (hb : barV V 3 [u0, u1, v1, v2]) :
    criticalWeight V X =
      1 / (wtcount3Y (dist u0 u1) (dist u0 v1) (dist u1 v1)) := by
  sorry

/-- HOL `MCELL3_008`. -/
theorem MCELL3_008 (V : Set V3) (X : Set V3) (u0 u1 : V3) (ul : List V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hX : X = mcell3 V ul) (hcey : criticalEdgeY (dist u0 u1))
    (he : {u0, u1} ∈ edgeX V X) (hb : barV V 3 ul) :
    0.008 * dihX V X (u0, u1) ≤
      gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {u0, u1} X := by
  sorry

/-- HOL `real_model_008`: the non-cc-cell remainder has weight ≥ `0.008`
times its dihedral. -/
theorem real_model_008 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (hno4 : ¬ cc_4 V u0 u1 f i) :
    setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
        X ≠ ccCell V [u0, u1, f i] ∧ X ≠ ccCell V [u1, u0, f (i + 1)]}
        (fun X => 0.008 * dihX V X (u0, u1)) ≤
      setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
        X ≠ ccCell V [u0, u1, f i] ∧ X ≠ ccCell V [u1, u0, f (i + 1)]}
        (fun X => gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {u0, u1} X) := by
  sorry

/-- HOL `real_model_cell23`. -/
theorem real_model_cell23 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i →
      gammaX V (ccCell V [u0, u1, f i]) lmfun *
          criticalWeight V (ccCell V [u0, u1, f i]) +
          gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
            criticalWeight V (ccCell V [u1, u0, f (i + 1)]) ≤
        gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_cell23_008`. -/
theorem real_model_cell23_008 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i →
      (gammaX V (ccCell V [u0, u1, f i]) lmfun *
          criticalWeight V (ccCell V [u0, u1, f i]) -
          0.008 * dihX V (ccCell V [u0, u1, f i]) (u0, u1)) +
          (gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
              criticalWeight V (ccCell V [u1, u0, f (i + 1)]) -
            0.008 * dihX V (ccCell V [u1, u0, f (i + 1)]) (u0, u1)) +
          0.008 * azim_mcell V f u0 u1 i ≤
        gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `GAMMAX_008a`. -/
theorem GAMMAX_008a (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (hno4 : ¬ cc_4 V u0 u1 f i) :
    0.008 * dihX V (ccCell V [u0, u1, f i]) (u0, u1) ≤
      gammaX V (ccCell V [u0, u1, f i]) lmfun *
        criticalWeight V (ccCell V [u0, u1, f i]) := by
  sorry

/-- HOL `GAMMAX_008b`. -/
theorem GAMMAX_008b (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (hno4 : ¬ cc_4 V u0 u1 f i) :
    0.008 * dihX V (ccCell V [u1, u0, f (i + 1)]) (u0, u1) ≤
      gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
        criticalWeight V (ccCell V [u1, u0, f (i + 1)]) := by
  sorry

/-- HOL `real_model_3a`. -/
theorem real_model_3a (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i →
      0 ≤ gammaX V (ccCell V [u0, u1, f i]) lmfun *
        criticalWeight V (ccCell V [u0, u1, f i]) := by
  sorry

/-- HOL `real_model_3b`. -/
theorem real_model_3b (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i →
      0 ≤ gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
        criticalWeight V (ccCell V [u1, u0, f (i + 1)]) := by
  sorry

/-- HOL `real_model_gr`. -/
theorem real_model_gr (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i →
      0.008 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `JSP_BOUNDS`. -/
theorem JSP_BOUNDS (u0 u1 u2 : V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hnc : ¬ Collinear3 u0 u1 u2) (hhl : hl [u0, u1, u2] ≤ 1.34)
    (h1 : 2 * hminus ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) (h3 : 2 ≤ dist u1 u2) :
    dist u0 u2 < 2 * hminus ∧ dist u1 u2 < 2 * hminus := by
  sorry

/-- HOL `real_model_pema`. -/
theorem real_model_pema (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i ∧
        hl [u0, u1, f i] < 1.34 ∧ ¬ (hl [u0, u1, f (i + 1)] < 1.34) ∧
        azim_mcell V f u0 u1 i < 1.074 →
      a_spine5 + b_spine5 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_pemb`. -/
theorem real_model_pemb (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i ∧
        ¬ (hl [u0, u1, f i] < 1.34) ∧ hl [u0, u1, f (i + 1)] < 1.34 ∧
        azim_mcell V f u0 u1 i < 1.074 →
      a_spine5 + b_spine5 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- Taylor 下界包络：`arctan t ≥ t - t³/3 + t⁵/5 - t⁷/7 + t⁹/9 - t¹¹/11`（`[0,∞)`）。
导数误差 `+u¹²/(1+u²) ≥ 0`，FTC 于 `0`。 -/
private theorem p25_arctan_ge_taylor6 (t : ℝ) (ht : 0 ≤ t) :
    t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 - t ^ 11 / 11 ≤ Real.arctan t := by
  have h3 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 3 / 3) (u ^ 2) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 3).div_const 3
  have h5 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 5 / 5) (u ^ 4) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 5).div_const 5
  have h7 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 7 / 7) (u ^ 6) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 7).div_const 7
  have h9 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 9 / 9) (u ^ 8) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 9).div_const 9
  have h11 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 11 / 11) (u ^ 10) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 11).div_const 11
  have hpoly : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7
      + v ^ 9 / 9 - v ^ 11 / 11) (1 - u ^ 2 + u ^ 4 - u ^ 6 + u ^ 8 - u ^ 10) u := by
    intro u
    have s1 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3) (1 - u ^ 2) u :=
      (hasDerivAt_id u).sub (h3 u)
    have s2 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5)
        (1 - u ^ 2 + u ^ 4) u := s1.add (h5 u)
    have s3 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7)
        (1 - u ^ 2 + u ^ 4 - u ^ 6) u := s2.sub (h7 u)
    have s4 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7
        + v ^ 9 / 9) (1 - u ^ 2 + u ^ 4 - u ^ 6 + u ^ 8) u := s3.add (h9 u)
    exact s4.sub (h11 u)
  have hf' : deriv (fun u => Real.arctan u
      - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9 - u ^ 11 / 11))
      = fun u => u ^ 12 / (1 + u ^ 2) := by
    funext u
    have hd : HasDerivAt (fun v : ℝ => Real.arctan v
        - (v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7 + v ^ 9 / 9 - v ^ 11 / 11))
        (1 / (1 + u ^ 2) - (1 - u ^ 2 + u ^ 4 - u ^ 6 + u ^ 8 - u ^ 10)) u :=
      HasDerivAt.sub (Real.hasDerivAt_arctan u) (hpoly u)
    rw [hd.deriv]
    field_simp
    ring
  have hdiff : ∀ x ∈ uIcc (0:ℝ) t, DifferentiableAt ℝ (fun u => Real.arctan u
      - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9 - u ^ 11 / 11)) x := by
    intro x _
    exact DifferentiableAt.sub (Real.differentiableAt_arctan x) (by fun_prop)
  have hcont : Continuous (fun u : ℝ => u ^ 12 / (1 + u ^ 2)) :=
    Continuous.div (by fun_prop) (by fun_prop)
      (fun u => ne_of_gt (by positivity : (0:ℝ) < 1 + u ^ 2))
  have hftc := intervalIntegral.integral_deriv_eq_sub'
    (fun u => Real.arctan u
      - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9 - u ^ 11 / 11)) hf' hdiff
    hcont.continuousOn
  have hint : ∫ y in (0:ℝ)..t, y ^ 12 / (1 + y ^ 2)
      = Real.arctan t - (t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 - t ^ 11 / 11) := by
    have hzero : (fun u => Real.arctan u
        - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9 - u ^ 11 / 11)) (0:ℝ) = 0 := by
      simp [Real.arctan_zero]
    simpa [hzero] using hftc
  have hnonneg : (0:ℝ) ≤ ∫ y in (0:ℝ)..t, y ^ 12 / (1 + y ^ 2) :=
    intervalIntegral.integral_nonneg ht
      (fun y (hy : y ∈ Icc (0:ℝ) t) => div_nonneg (pow_nonneg hy.1 12) (by positivity))
  linarith

/-- Taylor 上界包络：`arctan t ≤ t - t³/3 + t⁵/5 - t⁷/7 + t⁹/9`（`[0,∞)`）。
导数误差 `-u¹⁰/(1+u²) ≤ 0`，FTC 于 `0`。 -/
private theorem p25_arctan_le_taylor5 (t : ℝ) (ht : 0 ≤ t) :
    Real.arctan t ≤ t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 := by
  have h3 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 3 / 3) (u ^ 2) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 3).div_const 3
  have h5 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 5 / 5) (u ^ 4) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 5).div_const 5
  have h7 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 7 / 7) (u ^ 6) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 7).div_const 7
  have h9 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 9 / 9) (u ^ 8) u := by
    intro u; simpa using ((hasDerivAt_id u).pow 9).div_const 9
  have hpoly : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7
      + v ^ 9 / 9) (1 - u ^ 2 + u ^ 4 - u ^ 6 + u ^ 8) u := by
    intro u
    have s1 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3) (1 - u ^ 2) u :=
      (hasDerivAt_id u).sub (h3 u)
    have s2 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5)
        (1 - u ^ 2 + u ^ 4) u := s1.add (h5 u)
    have s3 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7)
        (1 - u ^ 2 + u ^ 4 - u ^ 6) u := s2.sub (h7 u)
    exact s3.add (h9 u)
  have hf' : deriv (fun u => Real.arctan u
      - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9))
      = fun u => -(u ^ 10 / (1 + u ^ 2)) := by
    funext u
    have hd : HasDerivAt (fun v : ℝ => Real.arctan v
        - (v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7 + v ^ 9 / 9))
        (1 / (1 + u ^ 2) - (1 - u ^ 2 + u ^ 4 - u ^ 6 + u ^ 8)) u :=
      HasDerivAt.sub (Real.hasDerivAt_arctan u) (hpoly u)
    rw [hd.deriv]
    field_simp
    ring
  have hdiff : ∀ x ∈ uIcc (0:ℝ) t, DifferentiableAt ℝ (fun u => Real.arctan u
      - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9)) x := by
    intro x _
    exact DifferentiableAt.sub (Real.differentiableAt_arctan x) (by fun_prop)
  have hcont : Continuous (fun u : ℝ => -(u ^ 10 / (1 + u ^ 2))) :=
    (Continuous.div (by fun_prop) (by fun_prop)
      (fun u => ne_of_gt (by positivity : (0:ℝ) < 1 + u ^ 2))).neg
  have hftc := intervalIntegral.integral_deriv_eq_sub'
    (fun u => Real.arctan u
      - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9)) hf' hdiff hcont.continuousOn
  have hint : ∫ y in (0:ℝ)..t, -(y ^ 10 / (1 + y ^ 2))
      = Real.arctan t - (t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9) := by
    have hzero : (fun u => Real.arctan u
        - (u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7 + u ^ 9 / 9)) (0:ℝ) = 0 := by
      simp [Real.arctan_zero]
    simpa [hzero] using hftc
  have hpos : (0:ℝ) ≤ ∫ y in (0:ℝ)..t, y ^ 10 / (1 + y ^ 2) :=
    intervalIntegral.integral_nonneg ht
      (fun y (hy : y ∈ Icc (0:ℝ) t) => div_nonneg (pow_nonneg hy.1 10) (by positivity))
  have hneg : (∫ y in (0:ℝ)..t, -(y ^ 10 / (1 + y ^ 2))) ≤ 0 := by
    have hne : (∫ y in (0:ℝ)..t, -(y ^ 10 / (1 + y ^ 2)))
        = -(∫ y in (0:ℝ)..t, y ^ 10 / (1 + y ^ 2)) :=
      intervalIntegral.integral_neg (f := fun y : ℝ => y ^ 10 / (1 + y ^ 2))
    linarith [hne, hpos]
  linarith

/-- 补角恒等式：`arctan x + arctan x⁻¹ = π/2`（`0 < x`）。
`sin a sin b = cos a cos b`（`sin_arctan`/`cos_arctan` 精确式）给
`cos(a+b) = 0`，而 `a+b ∈ (0,π)` 且 `cos` 在 `[0,π]` 严格反单调。 -/
private theorem p25_arctan_add_arctan_inv (x : ℝ) (hx : 0 < x) :
    Real.arctan x + Real.arctan (x⁻¹) = Real.pi / 2 := by
  have hpos1 : (0:ℝ) < Real.arctan x := by
    have h := Real.arctan_lt_arctan_iff.2 hx
    rwa [Real.arctan_zero] at h
  have hpos2 : (0:ℝ) < Real.arctan (x⁻¹) := by
    have h := Real.arctan_lt_arctan_iff.2 (inv_pos.2 hx)
    rwa [Real.arctan_zero] at h
  have hcos : Real.cos (Real.arctan x + Real.arctan (x⁻¹)) = 0 := by
    rw [Real.cos_add]
    have e1 : Real.sin (Real.arctan x) * Real.sin (Real.arctan (x⁻¹))
        = Real.cos (Real.arctan x) * Real.cos (Real.arctan (x⁻¹)) := by
      rw [Real.sin_arctan, Real.sin_arctan, Real.cos_arctan, Real.cos_arctan]
      field_simp
    linarith
  have hrange1 : Real.arctan x + Real.arctan (x⁻¹) ∈ Icc (0:ℝ) Real.pi :=
    ⟨le_of_lt (by linarith),
      by linarith [Real.arctan_lt_pi_div_two x, Real.arctan_lt_pi_div_two (x⁻¹),
        Real.pi_pos]⟩
  have hrange2 : (Real.pi / 2 : ℝ) ∈ Icc (0:ℝ) Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have heq := Real.strictAntiOn_cos.injOn hrange1 hrange2
    (by rw [Real.cos_pi_div_two]; exact hcos)
  linarith

/-- HOL `c2089`: `atn (sqrt 3.07) < pi - 2.089`。2026-10-13 转真（零证书链）：
补角恒等式 + `arctan z ≥ S₆(z)`（六项 Taylor 下界，私件
`p25_arctan_ge_taylor6`）在 `z = (√3.07)⁻¹`（`z² = 100/307` 精确、
`z ≥ 190/333`）处取值，数值夹逼只用 `Real.pi_gt_d6`。 -/
theorem c2089 : Real.arctan (Real.sqrt 3.07) < Real.pi - 2.089 := by
  have hcomp := p25_arctan_add_arctan_inv (Real.sqrt 3.07) (by positivity)
  have hz2 : (Real.sqrt 3.07)⁻¹ * (Real.sqrt 3.07)⁻¹ = 100 / 307 := by
    have hsq : Real.sqrt 3.07 * Real.sqrt 3.07 = 3.07 := Real.mul_self_sqrt (by norm_num)
    calc (Real.sqrt 3.07)⁻¹ * (Real.sqrt 3.07)⁻¹
        = (Real.sqrt 3.07 * Real.sqrt 3.07)⁻¹ := by field_simp
      _ = 100 / 307 := by rw [hsq]; norm_num
  have hfact : (Real.sqrt 3.07)⁻¹ - ((Real.sqrt 3.07)⁻¹) ^ 3 / 3
      + ((Real.sqrt 3.07)⁻¹) ^ 5 / 5 - ((Real.sqrt 3.07)⁻¹) ^ 7 / 7
      + ((Real.sqrt 3.07)⁻¹) ^ 9 / 9 - ((Real.sqrt 3.07)⁻¹) ^ 11 / 11
      = (Real.sqrt 3.07)⁻¹ * (1 - ((Real.sqrt 3.07)⁻¹ * (Real.sqrt 3.07)⁻¹) / 3
        + ((Real.sqrt 3.07)⁻¹ * (Real.sqrt 3.07)⁻¹) ^ 2 / 5
        - ((Real.sqrt 3.07)⁻¹ * (Real.sqrt 3.07)⁻¹) ^ 3 / 7
        + ((Real.sqrt 3.07)⁻¹ * (Real.sqrt 3.07)⁻¹) ^ 4 / 9
        - ((Real.sqrt 3.07)⁻¹ * (Real.sqrt 3.07)⁻¹) ^ 5 / 11) := by
    ring
  have hlow := p25_arctan_ge_taylor6 ((Real.sqrt 3.07)⁻¹)
    (inv_nonneg.2 (Real.sqrt_nonneg 3.07))
  rw [hfact, hz2] at hlow
  have hFpos : (0:ℝ) < 1 - (100:ℝ)/307/3 + ((100:ℝ)/307) ^ 2 / 5 - ((100:ℝ)/307) ^ 3 / 7
      + ((100:ℝ)/307) ^ 4 / 9 - ((100:ℝ)/307) ^ 5 / 11 := by norm_num
  have hzge : (190 / 333 : ℝ) ≤ (Real.sqrt 3.07)⁻¹ := by
    have h1 : Real.sqrt 3.07 ≤ 333 / 190 := by
      calc Real.sqrt 3.07 ≤ Real.sqrt ((333 / 190 : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by norm_num : (3.07:ℝ) ≤ (333 / 190) ^ 2)
        _ = 333 / 190 := Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 333 / 190)
    calc (190:ℝ) / 333 = (333 / 190)⁻¹ := by field_simp
      _ ≤ (Real.sqrt 3.07)⁻¹ :=
            (inv_le_inv₀ (by norm_num : (0:ℝ) < 333 / 190) (by positivity)).2 h1
  have hL0 : (190:ℝ) * 9086 / (333 * 10000) ≤ Real.arctan ((Real.sqrt 3.07)⁻¹) := by
    calc (190:ℝ) * 9086 / (333 * 10000)
        = (190 / 333) * (9086 / 10000) := by norm_num
      _ ≤ (190 / 333) * (1 - (100:ℝ)/307/3 + ((100:ℝ)/307) ^ 2 / 5 - ((100:ℝ)/307) ^ 3 / 7
            + ((100:ℝ)/307) ^ 4 / 9 - ((100:ℝ)/307) ^ 5 / 11) :=
            mul_le_mul_of_nonneg_left (by norm_num) (by norm_num)
      _ ≤ (Real.sqrt 3.07)⁻¹ * (1 - (100:ℝ)/307/3 + ((100:ℝ)/307) ^ 2 / 5
            - ((100:ℝ)/307) ^ 3 / 7 + ((100:ℝ)/307) ^ 4 / 9 - ((100:ℝ)/307) ^ 5 / 11) :=
            mul_le_mul_of_nonneg_right hzge hFpos.le
      _ ≤ Real.arctan ((Real.sqrt 3.07)⁻¹) := hlow
  have h1 : Real.arctan (Real.sqrt 3.07) = Real.pi / 2 - Real.arctan ((Real.sqrt 3.07)⁻¹) := by
    linarith
  rw [h1]
  linarith [hL0, Real.pi_gt_d6]

/-- HOL `c1946`: `pi - 1.946 < atn (sqrt 6.45)`。2026-10-13 转真（零证书链）：
补角恒等式 + `arctan z ≤ S₅(z)`（五项 Taylor 上界，私件
`p25_arctan_le_taylor5`）在 `z = (√6.45)⁻¹`（`z² = 20/129` 精确、
`z ≤ 1969/5000`）处取值，数值夹逼只用 `Real.pi_lt_d4`。 -/
theorem c1946 : Real.pi - 1.946 < Real.arctan (Real.sqrt 6.45) := by
  have hcomp := p25_arctan_add_arctan_inv (Real.sqrt 6.45) (by positivity)
  have hz2 : (Real.sqrt 6.45)⁻¹ * (Real.sqrt 6.45)⁻¹ = 20 / 129 := by
    have hsq : Real.sqrt 6.45 * Real.sqrt 6.45 = 6.45 := Real.mul_self_sqrt (by norm_num)
    calc (Real.sqrt 6.45)⁻¹ * (Real.sqrt 6.45)⁻¹
        = (Real.sqrt 6.45 * Real.sqrt 6.45)⁻¹ := by field_simp
      _ = 20 / 129 := by rw [hsq]; norm_num
  have hfact : (Real.sqrt 6.45)⁻¹ - ((Real.sqrt 6.45)⁻¹) ^ 3 / 3
      + ((Real.sqrt 6.45)⁻¹) ^ 5 / 5 - ((Real.sqrt 6.45)⁻¹) ^ 7 / 7
      + ((Real.sqrt 6.45)⁻¹) ^ 9 / 9
      = (Real.sqrt 6.45)⁻¹ * (1 - ((Real.sqrt 6.45)⁻¹ * (Real.sqrt 6.45)⁻¹) / 3
        + ((Real.sqrt 6.45)⁻¹ * (Real.sqrt 6.45)⁻¹) ^ 2 / 5
        - ((Real.sqrt 6.45)⁻¹ * (Real.sqrt 6.45)⁻¹) ^ 3 / 7
        + ((Real.sqrt 6.45)⁻¹ * (Real.sqrt 6.45)⁻¹) ^ 4 / 9) := by
    ring
  have hupp := p25_arctan_le_taylor5 ((Real.sqrt 6.45)⁻¹)
    (inv_nonneg.2 (Real.sqrt_nonneg 6.45))
  rw [hfact, hz2] at hupp
  have hzle : (Real.sqrt 6.45)⁻¹ ≤ 1969 / 5000 := by
    have h1 : (5000:ℝ) / 1969 ≤ Real.sqrt 6.45 := Real.le_sqrt_of_sq_le (by norm_num)
    calc (Real.sqrt 6.45)⁻¹ ≤ (5000 / 1969)⁻¹ :=
          (inv_le_inv₀ (by positivity) (by norm_num : (0:ℝ) < 5000 / 1969)).2 h1
      _ = 1969 / 5000 := by field_simp
  have hgle : 1 - (20:ℝ)/129/3 + ((20:ℝ)/129) ^ 2 / 5 - ((20:ℝ)/129) ^ 3 / 7
      + ((20:ℝ)/129) ^ 4 / 9 ≤ 95266 / 100000 := by norm_num
  have hL0 : Real.arctan ((Real.sqrt 6.45)⁻¹)
      ≤ (1969:ℝ) * 95266 / (5000 * 100000) := by
    calc Real.arctan ((Real.sqrt 6.45)⁻¹)
        ≤ (Real.sqrt 6.45)⁻¹ * (1 - (20:ℝ)/129/3 + ((20:ℝ)/129) ^ 2 / 5
            - ((20:ℝ)/129) ^ 3 / 7 + ((20:ℝ)/129) ^ 4 / 9) := hupp
      _ ≤ (1969 / 5000) * (1 - (20:ℝ)/129/3 + ((20:ℝ)/129) ^ 2 / 5
            - ((20:ℝ)/129) ^ 3 / 7 + ((20:ℝ)/129) ^ 4 / 9) :=
            mul_le_mul_of_nonneg_right hzle (by positivity)
      _ ≤ (1969 / 5000) * (95266 / 100000) := mul_le_mul_of_nonneg_left hgle (by norm_num)
      _ = (1969:ℝ) * 95266 / (5000 * 100000) := by norm_num
  have h1 : Real.arctan (Real.sqrt 6.45) = Real.pi / 2 - Real.arctan ((Real.sqrt 6.45)⁻¹) := by
    linarith
  rw [h1]
  linarith [hL0, Real.pi_lt_d4]
/-- The `gamma23_full8_x` ↔ y-space composite consumed by the three MERGED
proofs (OXLZLEZ3.hl:8520-8528 etc.: the `GSYM Merge_ineq.gamma3_x_gamma3f` +
`Functional_equation.nonf_gamma23_full8_x` + `Sphere.y_of_x` +
`Nonlin_def.sqrt2_sqrt2` rewrite chain over `Merge_ineq.gamma3_x_gamma3f`,
merge_ineq.hl:4101). -/
private theorem p25_gamma23Full8X_yOfX_eq (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
    (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
    (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus)
    (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus) :
    yOfX (gamma23Full8X (h0cut y1)) y1 y2 y3 y4 y5 y6
      = gamma3f y1 y2 y6 (Real.sqrt 2) lmfun
        + gamma3f y1 y3 y5 (Real.sqrt 2) lmfun
        + (dihY y1 y2 y3 y4 y5 y6
            - (dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6
              + dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2)))
          * 0.008 := by
  have hsq2 : (Real.sqrt 2 * Real.sqrt 2 : ℝ) = 2 := Real.mul_self_sqrt (by norm_num)
  have he0 : dihY y1 y2 y3 y4 y5 y6
      = dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := rfl
  have hd1 : dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6
      = dihXf (y1 * y1) (y2 * y2) 2 2 2 (y6 * y6) := by
    show dihXf (y1 * y1) (y2 * y2) (Real.sqrt 2 * Real.sqrt 2)
      (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y6 * y6) = _
    rw [hsq2]
  have hd2 : dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2)
      = dihXf (y1 * y1) 2 (y3 * y3) 2 (y5 * y5) 2 := by
    show dihXf (y1 * y1) (Real.sqrt 2 * Real.sqrt 2) (y3 * y3)
      (Real.sqrt 2 * Real.sqrt 2) (y5 * y5) (Real.sqrt 2 * Real.sqrt 2) = _
    rw [hsq2]
  rw [show yOfX (gamma23Full8X (h0cut y1)) y1 y2 y3 y4 y5 y6
      = gamma23Full8X (h0cut y1) (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
          (y5 * y5) (y6 * y6) from rfl,
    show gamma23Full8X (h0cut y1) (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
          (y5 * y5) (y6 * y6)
      = gamma3X (h0cut y1) 0 0 0 (y1 * y1) (y2 * y2) (y6 * y6)
        + gamma3X (h0cut y1) 0 0 0 (y1 * y1) (y3 * y3) (y5 * y5)
        + (dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
            - (dihXf (y1 * y1) (y2 * y2) 2 2 2 (y6 * y6)
              + dihXf (y1 * y1) 2 (y3 * y3) 2 (y5 * y5) 2)) * 0.008 from rfl,
    mi_gamma3_x_gamma3f 0 0 0 y1 y2 y6 hy1.1 hb2 hb2' hb6 hb6',
    mi_gamma3_x_gamma3f 0 0 0 y1 y3 y5 hy1.1 hb3 hb3' hb5 hb5',
    ← he0, hd1, hd2]

/-- HOL `IXPOTPA_MERGED`. -/
theorem IXPOTPA_MERGED (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
    (hcey : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
    (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
    (hb4 : Real.sqrt 8 ≤ y4) (hb4' : y4 ≤ y5 + y6)
    (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus) (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hdi1 : dihY y1 y2 y3 y4 y5 y6 ≤ 2.089)
    (hdi2 : 1.946 ≤ dihY y1 y2 y3 y4 y5 y6)
    (he1 : eta_y y1 y2 y6 ^ 2 ≤ 1.34 ^ 2) (he2 : eta_y y1 y3 y5 ^ 2 ≤ 1.34 ^ 2) :
    3 * 0.0057 ≤ gamma3f y1 y2 y6 (Real.sqrt 2) lmfun +
      gamma3f y1 y3 y5 (Real.sqrt 2) lmfun +
      (dihY y1 y2 y3 y4 y5 y6 -
          (dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 +
            dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2))) * 0.008 := by
  -- prelims (OXLZLEZ3.hl:8502-8519)
  obtain ⟨hy1lo, hy1hi⟩ := id hcey
  have hy4ub : y4 ≤ 4 * hminus := by linarith
  have hy1pos : (0 : ℝ) < y1 := by
    have h12 := mi_hminus_prop.1
    linarith
  have hpi2 : Real.pi / 2 < dihY y1 y2 y3 y4 y5 y6 := by
    have hpi : Real.pi < (3.892 : ℝ) := by linarith [Real.pi_lt_d4]
    linarith
  have hd4neg : delta4Y y1 y2 y3 y4 y5 y6 < 0 :=
    mi_dih_gt_pi2 (x1 := y1 * y1) (by positivity)
      (show 0 < deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
        (y6 * y6) from hd)
      (show Real.pi / 2 < dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
        (y5 * y5) (y6 * y6) from hpi2)
  -- the two tan² arms (OXLZLEZ3.hl:8555-8571, via c2089/c1946 +
  -- Merge_ineq.lindihpi_lt_y / lindihpi_gt_y)
  have hsq3 : Real.sqrt 3.07 ^ 2 = (3.07 : ℝ) := by
    rw [pow_two]; exact Real.mul_self_sqrt (by norm_num)
  have hsq6 : Real.sqrt 6.45 ^ 2 = (6.45 : ℝ) := by
    rw [pow_two]; exact Real.mul_self_sqrt (by norm_num)
  have h307 : (3.07 : ℝ) * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6
      < 4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6 := by
    have hdihlt : dihY y1 y2 y3 y4 y5 y6
        < Real.pi - Real.arctan (Real.sqrt 3.07) := by
      linarith [hdi1, c2089]
    have hif := (mi_lindihpi_lt_y (a := Real.sqrt 3.07) hy1pos (by positivity) hd
      hd4neg).mp hdihlt
    rwa [hsq3] at hif
  have h645 : 4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6
      < (6.45 : ℝ) * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6 := by
    have hdihgt : Real.pi - Real.arctan (Real.sqrt 6.45)
        < dihY y1 y2 y3 y4 y5 y6 := by
      linarith [hdi2, c1946]
    have hif := (mi_lindihpi_gt_y (a := Real.sqrt 6.45) hy1pos (by positivity) hd
      hd4neg).mp hdihgt
    rwa [hsq6] at hif
  -- bank dispatch (OXLZLEZ3.hl:8520-8554)
  have hbank := proj_bank_IXPOTPA hnl y1 y2 y3 y4 y5 y6 hcey.1 hcey.2 hb2 hb2' hb3
    hb3' hb4 hy4ub hb5 hb5' hb6 hb6'
  rcases hbank with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact absurd h1 (by linarith)
  · linarith
  · exact absurd h3 (by linarith)
  · linarith
  · exact absurd h5 (by linarith)
  · exact absurd h6 (by linarith)
  · have hbr := p25_gamma23Full8X_yOfX_eq y1 y2 y3 y4 y5 y6 hcey hb2 hb2' hb3 hb3'
      hb5 hb5' hb6 hb6'
    rw [hbr] at h7
    linarith

/-- HOL `TXQTPVC_MERGED`. -/
theorem TXQTPVC_MERGED (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
    (hcey : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
    (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
    (hb4 : 2 ≤ y4) (hb4' : y4 ≤ y5 + y6)
    (hrad : 2 ≤ rad2YP25 y1 y2 y3 y4 y5 y6)
    (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus) (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hdi1 : dihY y1 y2 y3 y4 y5 y6 ≤ 2.089)
    (hdi2 : 1.946 ≤ dihY y1 y2 y3 y4 y5 y6)
    (he1 : eta_y y1 y2 y6 ^ 2 ≤ 1.34 ^ 2) (he2 : eta_y y1 y3 y5 ^ 2 ≤ 1.34 ^ 2) :
    3 * 0.0057 ≤ gamma3f y1 y2 y6 (Real.sqrt 2) lmfun +
      gamma3f y1 y3 y5 (Real.sqrt 2) lmfun +
      (dihY y1 y2 y3 y4 y5 y6 -
          (dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 +
            dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2))) * 0.008 := by
  rcases lt_trichotomy (Real.sqrt 8) y4 with hsup | heq | hsub
  · -- the y4 > sqrt8 arm is IXPOTPA (OXLZLEZ3.hl:8585-8587)
    exact IXPOTPA_MERGED y1 y2 y3 y4 y5 y6 hnl hcey hb2 hb2' hb3 hb3'
      (le_of_lt hsup) hb4' hb5 hb5' hb6 hb6' hd hdi1 hdi2 he1 he2
  · -- the y4 = sqrt8 boundary joins the IXPOTPA arm
    exact IXPOTPA_MERGED y1 y2 y3 y4 y5 y6 hnl hcey hb2 hb2' hb3 hb3'
      (le_of_eq heq) hb4' hb5 hb5' hb6 hb6' hd hdi1 hdi2 he1 he2
  · -- the sub-critical arm consumes the TXQTPVC bank entry
    -- (OXLZLEZ3.hl:8588-8608)
    have hy4ub : y4 ≤ Real.sqrt 8 := le_of_lt hsub
    have hbank := proj_bank_TXQTPVC hnl y1 y2 y3 y4 y5 y6 hcey.1 hcey.2 hb2 hb2'
      hb3 hb3' hb4 (le_of_lt hsub) hb5 hb5' hb6 hb6'
    have hbr := p25_gamma23Full8X_yOfX_eq y1 y2 y3 y4 y5 y6 hcey hb2 hb2' hb3 hb3'
      hb5 hb5' hb6 hb6'
    have hrad2 : rad2YP25 y1 y2 y3 y4 y5 y6 = yOfX rad2X y1 y2 y3 y4 y5 y6 := rfl
    rcases hbank with h1 | h2 | h3 | h4 | h5 | h6
    · rw [hbr] at h1
      linarith
    · have hrad' : (2 : ℝ) ≤ yOfX rad2X y1 y2 y3 y4 y5 y6 := by
        rw [← hrad2]; exact hrad
      linarith
    · linarith
    · linarith
    · exact absurd h5 (by linarith)
    · exact absurd h6 (by linarith)

/-- HOL `TEWNSCJ_MERGED`.  2026-10-13 wave (SF-41): PA3 opaque-constant 桥
落地——`a_spine5`/`b_spine5` 已重指向 sphere.hl:632/634 逐字体（PackingAuto3
re-point，`rad2XP25` 先例），桥 `a_spine5 = aSpine5 ∧ b_spine5 = bSpine5` 为
`rfl`；收口消费 `proj_bank_TEWNSCJ` 投影 + `p25_gamma23Full8X_yOfX_eq` 桥 +
hrad/he1/he2 否证支，与 TXQTPVC_MERGED 装配同构。 -/
theorem TEWNSCJ_MERGED (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
    (hcey : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
    (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
    (hb4 : 2 ≤ y4) (hb4' : y4 ≤ Real.sqrt 8)
    (hrad : 2 ≤ rad2YP25 y1 y2 y3 y4 y5 y6)
    (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus) (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus)
    (he1 : eta_y y1 y2 y6 ^ 2 ≤ 1.34 ^ 2) (he2 : eta_y y1 y3 y5 ^ 2 ≤ 1.34 ^ 2) :
    a_spine5 + b_spine5 * dihY y1 y2 y3 y4 y5 y6 ≤
      gamma3f y1 y2 y6 (Real.sqrt 2) lmfun +
        gamma3f y1 y3 y5 (Real.sqrt 2) lmfun +
        (dihY y1 y2 y3 y4 y5 y6 -
            (dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 +
              dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2))) * 0.008 := by
  -- SF-41 常数桥（PA3 体揭示后 rfl）；首析取支 = gamma23Full8X 复合下界
  have hbank := proj_bank_TEWNSCJ hnl y1 y2 y3 y4 y5 y6 hcey.1 hcey.2 hb2 hb2'
    hb3 hb3' hb4 hb4' hb5 hb5' hb6 hb6'
  have hrad2 : rad2YP25 y1 y2 y3 y4 y5 y6 = yOfX rad2X y1 y2 y3 y4 y5 y6 := rfl
  rcases hbank with h1 | h2 | h3 | h4
  · have hbr := p25_gamma23Full8X_yOfX_eq y1 y2 y3 y4 y5 y6 hcey hb2 hb2' hb3 hb3'
      hb5 hb5' hb6 hb6'
    rw [hbr] at h1
    rw [show a_spine5 = aSpine5 from rfl, show b_spine5 = bSpine5 from rfl]
    linarith
  · -- rad2 否证支（rad2XP25 = yOfX rad2X 为 rfl，TXQTPVC_MERGED 同款）
    have hrad' : (2 : ℝ) ≤ yOfX rad2X y1 y2 y3 y4 y5 y6 := by
      rw [← hrad2]; exact hrad
    linarith
  · linarith
  · linarith

/-- HOL `CC_3_AZIM_LT_PI_COPLANAR`. -/
theorem CC_3_AZIM_LT_PI_COPLANAR (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hno4 : ¬ cc_4 V u0 u1 f i)
    (hr : leaf_rank V [u0, u1] w0 n f)
    (hapi : azim u0 u1 (f i) (f (i + 1)) < Real.pi) :
    ¬ Coplanar ({u0, u1, f i, f (i + 1)} : Set V3) := by
  sorry

/-- HOL `real_model_txq`. -/
theorem real_model_txq (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i ∧
        hl [u0, u1, f i] < 1.34 ∧ hl [u0, u1, f (i + 1)] < 1.34 ∧
        1.946 ≤ azim_mcell V f u0 u1 i ∧ azim_mcell V f u0 u1 i ≤ 2.089 →
      3.0 * 0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_tew`. -/
theorem real_model_tew (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i ∧
        hl [u0, u1, f i] < 1.34 ∧ hl [u0, u1, f (i + 1)] < 1.34 →
      a_spine5 + b_spine5 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-! ### T4 展开波（2026-10-08）：real-model 切片层 —— `cc_real_model_data`
前提树显式化

`cc_real_model_v11`（PackingAuto3.lean:150-198）的 33 合取项逐一对应本文件
`real_model_*` bank 的具名条目；原 `cc_real_model_data` 为单根黑箱 sorry
（与 bank 零消费关系），现展开为六具名切片 + 周期性真推导的显式装配
（冻结陈述签名不变）：

  cc_real_model_data（真装配）
  ├─ pkrmPeriodic  ✅真推导（real_periodic_data :2355 ✅ + cc_card_data
  │                 :2135 ✅ 投影）——零 sorryAx 会师真叶
  ├─ pkrmAzim      ⬜（合取 5-7 ← real_model_gckb :2897 / real_model_azim_c4
  │                 :2713 / real_model_sum_azim :2890，三枚认证锚）
  ├─ pkrmQuarter   ⬜（合取 8 ← real_model_ox3q1h_merge :2983，消费
  │                 ox3q1hP25——Oxl_def.hl 外部锚，Assembly 侧 T1 骨架
  │                 nliOx3q1h 同根）
  ├─ pkrmQu        ⬜（合取 9-17 ← gamma_qu :2795 / fhbv2_sym :2839 /
  │                 fhbv2 :2825 / quqy :3025 / quqy_sym :3041 / ztg4 :3058 /
  │                 azim1 :3068 / gaz4 :3081 / gaz6 :3094）
  ├─ pkrmQx        ⬜（合取 18-25 ← gamma_qx :3107 / g_qxd :3120 /
  │                 gamma10 :3150 / gamma11 :3170 / gamma8 :3262 /
  │                 gamma8b :3278 / gaz9 :3294 / azim2 :3310）
  └─ pkrmQy        ⬜（合取 26-33 ← cell23 :3430 / 3a :3485 / 3b :3496 /
                    gr :3507 / pema :3524 / pemb :3536 / tew :3635 /
                    txq :3623）

分类词桥件（真推导，零 sorryAx）：`cc_qu/qx/qy/hassmall` 在 `cc_data_v8`
上的逐点几何展开（`cc_real_dat_def` :2316 ✅ 的函数等式形式）；其余布尔/
实域场在 `cc_data_v8` 上与几何谓词定义等价（`cc_bool_data`/`cc_real_data`
全 rfl），故各切片的 bank 派发是纯 term 装配。债 = 29 枚 bank 叶（外部
认证锚，G4 / Flyspeck_constants.calc 口径）+ ox3q1hP25。 -/

/-- T4 桥件（真推导）：`cc_card_v11 (cc_data_v8 …) = n`——`cc_card_data`
(:2135 ✅ rfl 投影) + `HasSizeP25` 的基数分量。 -/
private theorem pk_card_eq (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) (n : ℕ)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) :
    cc_card_v11 (cc_data_v8 V f u0 u1) = n := by
  rw [cc_card_data]
  exact hsize.2

/-- T4 桥件（真推导）：`cc_qu_v11` 在 `cc_data_v8` 上的逐点几何展开
（`cc_real_dat_def` :2316 ✅ 第三合取项）。 -/
private theorem pk_qu_geometric (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) (i : ℕ) :
    cc_qu_v11 (cc_data_v8 V f u0 u1) i ↔
      cc_4 V u0 u1 f i ∧ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
        dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
        dist (f i) (f (i + 1)) < 2 * hminus := by
  rw [(cc_real_dat_def V f u0 u1).2.2.1]

/-- T4 桥件（真推导）：`cc_qx_v11` 的逐点几何展开（`cc_real_dat_def` 第一
合取项）。 -/
private theorem pk_qx_geometric (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) (i : ℕ) :
    cc_qx_v11 (cc_data_v8 V f u0 u1) i ↔
      cc_4 V u0 u1 f i ∧
        ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
          dist (f i) (f (i + 1)) < 2 * hminus) := by
  rw [(cc_real_dat_def V f u0 u1).1]

/-- T4 桥件（真推导）：`cc_qy_v11` 的逐点几何展开（`cc_real_dat_def` 第二
合取项）。 -/
private theorem pk_qy_geometric (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) (i : ℕ) :
    cc_qy_v11 (cc_data_v8 V f u0 u1) i ↔ ¬ cc_4 V u0 u1 f i := by
  rw [(cc_real_dat_def V f u0 u1).2.1]

/-- T4 桥件（真推导）：`cc_hassmall_v11` 的逐点几何展开（`cc_real_dat_def`
第四合取项）。 -/
private theorem pk_hassmall_geometric (V : Set V3) (f : ℕ → V3) (u0 u1 : V3)
    (i : ℕ) :
    cc_hassmall_v11 (cc_data_v8 V f u0 u1) i ↔
      (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
        dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus := by
  rw [(cc_real_dat_def V f u0 u1).2.2.2]

/-- T4 桥件（真推导）：`3 * cc_eps` 与 bank 字面常数 `3.0 * 0.0057` 的
数值恒等（`cc_eps = 0.0057`，PackingAuto3.lean:46；数值实例仅命题等价，
非定义等价，故以 norm_num 桥接）。 -/
private theorem pk_three_eps : (3 : ℝ) * cc_eps = 3.0 * 0.0057 := by
  norm_num [cc_eps]

/-- T4 切片 R1（`cc_real_model_v11` 合取 1-4）：四个实域场的 n-周期性。
**真推导（零 sorryAx 会师真叶）**：`real_periodic_data`（:2355 ✅，wedge 和的
周期性）+ `cc_real_data`/`cc_card_data` 投影（rfl）。 -/
theorem pkrmPeriodic (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) (n : ℕ)
    (hper : periodic f n) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) :
    periodic (cc_azim_v11 (cc_data_v8 V f u0 u1))
        (cc_card_v11 (cc_data_v8 V f u0 u1)) ∧
      periodic (cc_gg_v11 (cc_data_v8 V f u0 u1))
        (cc_card_v11 (cc_data_v8 V f u0 u1)) ∧
      periodic (cc_gg3a_v11 (cc_data_v8 V f u0 u1))
        (cc_card_v11 (cc_data_v8 V f u0 u1)) ∧
      periodic (cc_gg3b_v11 (cc_data_v8 V f u0 u1))
        (cc_card_v11 (cc_data_v8 V f u0 u1)) := by
  have hcard := pk_card_eq V f u0 u1 n hsize
  have hp := real_periodic_data V u0 u1 f n hper
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; rw [hcard]; exact hp.1 i
  · intro i; rw [hcard]; exact hp.2.1 i
  · intro i; rw [hcard]; exact hp.2.2.2.2.1 i
  · intro i; rw [hcard]; exact hp.2.2.2.2.2 i

/-- T4 切片 R2（合取 5-7）：azim 锚——下界 0.606、4-cell 楔 < 2.8、和 = 2π。
资产状态：**deferred-compute（外部认证锚）**——三枚 bank 叶全 ⬜。
-- NEEDS: real_model_gckb / real_model_azim_c4 / real_model_sum_azim 落证
（G4 证书粘合，同 §2a 查表口径）。 -/
theorem pkrmAzim (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    (∀ i, (0.606 : ℝ) ≤ cc_azim_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_4cell_v11 (cc_data_v8 V f u0 u1) i →
        cc_azim_v11 (cc_data_v8 V f u0 u1) i < 2.8) ∧
      (∑ i ∈ Finset.Icc 0 (cc_card_v11 (cc_data_v8 V f u0 u1) - 1),
        cc_azim_v11 (cc_data_v8 V f u0 u1) i = 2 * Real.pi) := by
  have hcard := pk_card_eq V f u0 u1 n hsize
  refine ⟨?_, ?_, ?_⟩
  · -- 合取 5 ← real_model_gckb（:2897）
    intro i
    exact real_model_gckb V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i
  · -- 合取 6 ← real_model_azim_c4（:2713；cc_4cell_v11 在 cc_data_v8 上
    -- 定义等价 cc_4）
    intro i h4
    exact real_model_azim_c4 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i h4
  · -- 合取 7 ← real_model_sum_azim（:2890）
    rw [hcard]
    exact real_model_sum_azim V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr

/-- T4 切片 R3（合取 8）：n = 4 象限案的认证下和。
资产状态：**bank 叶**——`real_model_ox3q1h_merge`(:2983 ⬜) 消费
`ox3q1hP25`（Oxl_def.hl 外部锚；Assembly 侧 T1 骨架 `nliOx3q1h` 同根，
G4 证书侧）。
-- NEEDS: ox3q1hP25 本体回填（Oxl_def.hl）+ ox3q1h_merge 装配波。 -/
theorem pkrmQuarter (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25) (hn : 1 < n)
    (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    (cc_card_v11 (cc_data_v8 V f u0 u1) = 4 ∧ ∃ i,
        cc_4cell_v11 (cc_data_v8 V f u0 u1) i ∧
        cc_crit_v11 (cc_data_v8 V f u0 u1) i ∧
        cc_qu_v11 (cc_data_v8 V f u0 u1) (i + 1) ∧
        cc_qu_v11 (cc_data_v8 V f u0 u1) (i + 2) ∧
        cc_qu_v11 (cc_data_v8 V f u0 u1) (i + 3)) →
      (0 : ℝ) ≤ ∑ i ∈ Finset.Icc 0 (cc_card_v11 (cc_data_v8 V f u0 u1) - 1),
        cc_gg_v11 (cc_data_v8 V f u0 u1) i := by
  intro h4
  obtain ⟨h4n, i, hi4, hcrit, hq1, hq2, hq3⟩ := h4
  rw [pk_card_eq V f u0 u1 n hsize]
  -- cc_qu_v11 = hassmall ∧ (4cell ∧ subcrit) 的合取序与 bank 5-fold 不同，
  -- 逐分量重排（真推导，几何字段定义等价）
  refine real_model_ox3q1h_merge V u0 u1 w0 n f hnl hox hn hp hs hsize h0 h1 hper
    hnc hcey hr ⟨h4n, i, hi4, hcrit.1, hcrit.2,
      hq1.2.1, hq1.1.1, hq1.1.2.1, hq1.1.2.2, hq1.2.2,
      hq2.2.1, hq2.1.1, hq2.1.2.1, hq2.1.2.2, hq2.2.2,
      hq3.2.1, hq3.1.1, hq3.1.2.1, hq3.1.2.2, hq3.2.2⟩

/-- T4 切片 R4（合取 9-17）：qu 族——下和 −cc_eps / cc_eps 上下文三件、
与相邻 qy 胞的配对和两件、spine5 界、三条 azim 线性族。
资产状态：**deferred-compute（外部认证锚）**——九枚 bank 叶全 ⬜。
-- NEEDS: gamma_qu/fhbv2(_sym)/quqy(_sym)/ztg4/azim1/gaz4/gaz6 逐条证书。 -/
theorem pkrmQu (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    (∀ i, cc_qu_v11 (cc_data_v8 V f u0 u1) i →
        -cc_eps ≤ cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qu_v11 (cc_data_v8 V f u0 u1) i ∧
          ¬cc_small_eta_v11 (cc_data_v8 V f u0 u1) i →
        cc_eps ≤ cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qu_v11 (cc_data_v8 V f u0 u1) i ∧
          ¬cc_small_eta_v11 (cc_data_v8 V f u0 u1) (i + 1) →
        cc_eps ≤ cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qu_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_qy_v11 (cc_data_v8 V f u0 u1) (i + 1) →
        (0 : ℝ) ≤ cc_gg_v11 (cc_data_v8 V f u0 u1) i +
          cc_gg3a_v11 (cc_data_v8 V f u0 u1) (i + 1)) ∧
      (∀ i, cc_qu_v11 (cc_data_v8 V f u0 u1) (i + 1) ∧
          cc_qy_v11 (cc_data_v8 V f u0 u1) i →
        (0 : ℝ) ≤ cc_gg3b_v11 (cc_data_v8 V f u0 u1) i +
          cc_gg_v11 (cc_data_v8 V f u0 u1) (i + 1)) ∧
      (∀ i, cc_4cell_v11 (cc_data_v8 V f u0 u1) i →
        a_spine5 + b_spine5 * cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qu_v11 (cc_data_v8 V f u0 u1) i →
        (-0.0659 : ℝ) + 0.042 * cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qu_v11 (cc_data_v8 V f u0 u1) i →
        (-0.0142852 : ℝ) + 0.00609451 * cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qu_v11 (cc_data_v8 V f u0 u1) i →
        (0.161517 : ℝ) - 0.119482 * cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 合取 9 ← real_model_gamma_qu（:2795）
    intro i hq
    obtain ⟨h4, hp1, hp2, hp3, hp4⟩ := (pk_qu_geometric V f u0 u1 i).mp hq
    exact real_model_gamma_qu V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i h4 ⟨hp1, hp2, hp3, hp4⟩
  · -- 合取 10 ← real_model_fhbv2_sym（:2839；注意 bank 的 ¬small_eta 在 i 侧）
    intro i h
    obtain ⟨hq, hse⟩ := h
    obtain ⟨h4, hp1, hp2, hp3, hp4⟩ := (pk_qu_geometric V f u0 u1 i).mp hq
    exact real_model_fhbv2_sym V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i ⟨⟨h4, hp1, hp2, hp3, hp4⟩, hse⟩
  · -- 合取 11 ← real_model_fhbv2（:2825）
    intro i h
    obtain ⟨hq, hse⟩ := h
    obtain ⟨h4, hp1, hp2, hp3, hp4⟩ := (pk_qu_geometric V f u0 u1 i).mp hq
    exact real_model_fhbv2 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i ⟨⟨h4, hp1, hp2, hp3, hp4⟩, hse⟩
  · -- 合取 12 ← real_model_quqy（:3025）
    intro i h
    obtain ⟨hq, hqy⟩ := h
    obtain ⟨h4, hp1, hp2, hp3, hp4⟩ := (pk_qu_geometric V f u0 u1 i).mp hq
    exact real_model_quqy V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ⟨⟨h4, hp1, hp2, hp3, hp4⟩, (pk_qy_geometric V f u0 u1 (i + 1)).mp hqy⟩
  · -- 合取 13 ← real_model_quqy_sym（:3041）
    intro i h
    obtain ⟨hq, hqy⟩ := h
    obtain ⟨h4, hp1, hp2, hp3, hp4⟩ := (pk_qu_geometric V f u0 u1 (i + 1)).mp hq
    exact real_model_quqy_sym V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i ⟨⟨h4, hp1, hp2, hp3, hp4⟩, (pk_qy_geometric V f u0 u1 i).mp hqy⟩
  · -- 合取 14 ← real_model_ztg4（:3058）
    intro i h4
    exact real_model_ztg4 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i h4
  · -- 合取 15 ← real_model_azim1（:3068）
    intro i hq
    obtain ⟨h4, hp1, hp2, hp3, hp4⟩ := (pk_qu_geometric V f u0 u1 i).mp hq
    exact real_model_azim1 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i h4 ⟨hp1, hp2, hp3, hp4⟩
  · -- 合取 16 ← real_model_gaz4（:3081）
    intro i hq
    obtain ⟨h4, hp1, hp2, hp3, hp4⟩ := (pk_qu_geometric V f u0 u1 i).mp hq
    exact real_model_gaz4 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i h4 ⟨hp1, hp2, hp3, hp4⟩
  · -- 合取 17 ← real_model_gaz6（:3094）
    intro i hq
    obtain ⟨h4, hp1, hp2, hp3, hp4⟩ := (pk_qu_geometric V f u0 u1 i).mp hq
    exact real_model_gaz6 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i h4 ⟨hp1, hp2, hp3, hp4⟩

/-- T4 切片 R5（合取 18-25）：qx 族——非 qu 的 4-cell 楔：下和 0 / 2.3 张角
加强 / 与相邻 qy 胞配和两件 / 半 small 两件 / hassmall 线性 + supercrit。
资产状态：**deferred-compute（外部认证锚）**——八枚 bank 叶全 ⬜。
-- NEEDS: gamma_qx/g_qxd/gamma10/gamma11/gamma8/gamma8b/gaz9/azim2 逐条证书。 -/
theorem pkrmQx (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    (∀ i, cc_qx_v11 (cc_data_v8 V f u0 u1) i →
        (0 : ℝ) ≤ cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qx_v11 (cc_data_v8 V f u0 u1) i ∧
          2.3 < cc_azim_v11 (cc_data_v8 V f u0 u1) i →
        cc_eps ≤ cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qx_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_hassmall_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_qy_v11 (cc_data_v8 V f u0 u1) (i + 1) →
        cc_eps ≤ cc_gg_v11 (cc_data_v8 V f u0 u1) i +
          cc_gg3a_v11 (cc_data_v8 V f u0 u1) (i + 1)) ∧
      (∀ i, cc_qx_v11 (cc_data_v8 V f u0 u1) (i + 1) ∧
          cc_hassmall_v11 (cc_data_v8 V f u0 u1) (i + 1) ∧
          cc_qy_v11 (cc_data_v8 V f u0 u1) i →
        cc_eps ≤ cc_gg3b_v11 (cc_data_v8 V f u0 u1) i +
          cc_gg_v11 (cc_data_v8 V f u0 u1) (i + 1)) ∧
      (∀ i, cc_qx_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_small_v11 (cc_data_v8 V f u0 u1) i ∧
          ¬cc_small_v11 (cc_data_v8 V f u0 u1) (i + 1) →
        cc_eps ≤ cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qx_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_small_v11 (cc_data_v8 V f u0 u1) (i + 1) ∧
          ¬cc_small_v11 (cc_data_v8 V f u0 u1) i →
        cc_eps ≤ cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qx_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_hassmall_v11 (cc_data_v8 V f u0 u1) i →
        (0.213849 : ℝ) - 0.119482 * cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qx_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_hassmall_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_supercrit_v11 (cc_data_v8 V f u0 u1) i →
        (0.00457511 : ℝ) + 0.00609451 * cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 合取 18 ← real_model_gamma_qx（:3107）
    intro i hx
    obtain ⟨h4, hn5⟩ := (pk_qx_geometric V f u0 u1 i).mp hx
    exact real_model_gamma_qx V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i h4 hn5
  · -- 合取 19 ← real_model_g_qxd（:3120）
    intro i h
    obtain ⟨hx, haz⟩ := h
    obtain ⟨h4, hn5⟩ := (pk_qx_geometric V f u0 u1 i).mp hx
    exact real_model_g_qxd V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ⟨h4, hn5⟩ haz
  · -- 合取 20 ← real_model_gamma10（:3150）
    intro i h
    obtain ⟨hx, hsm, hqy⟩ := h
    obtain ⟨h4, hn5⟩ := (pk_qx_geometric V f u0 u1 i).mp hx
    exact real_model_gamma10 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i ⟨⟨h4, hn5⟩, (pk_hassmall_geometric V f u0 u1 i).mp hsm,
        (pk_qy_geometric V f u0 u1 (i + 1)).mp hqy⟩
  · -- 合取 21 ← real_model_gamma11（:3170）
    intro i h
    obtain ⟨hx, hsm, hqy⟩ := h
    obtain ⟨h4, hn5⟩ := (pk_qx_geometric V f u0 u1 (i + 1)).mp hx
    exact real_model_gamma11 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i ⟨⟨h4, hn5⟩, (pk_hassmall_geometric V f u0 u1 (i + 1)).mp hsm,
        (pk_qy_geometric V f u0 u1 i).mp hqy⟩
  · -- 合取 22 ← real_model_gamma8（:3262）
    intro i h
    obtain ⟨hx, hsm1, hsm2⟩ := h
    obtain ⟨h4, hn5⟩ := (pk_qx_geometric V f u0 u1 i).mp hx
    exact real_model_gamma8 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i ⟨⟨h4, hn5⟩, hsm1, hsm2⟩
  · -- 合取 23 ← real_model_gamma8b（:3278）
    intro i h
    obtain ⟨hx, hsm1, hsm2⟩ := h
    obtain ⟨h4, hn5⟩ := (pk_qx_geometric V f u0 u1 i).mp hx
    exact real_model_gamma8b V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i ⟨⟨h4, hn5⟩, hsm1, hsm2⟩
  · -- 合取 24 ← real_model_gaz9（:3294）
    intro i h
    obtain ⟨hx, hsm⟩ := h
    obtain ⟨h4, hn5⟩ := (pk_qx_geometric V f u0 u1 i).mp hx
    exact real_model_gaz9 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ⟨⟨h4, hn5⟩, (pk_hassmall_geometric V f u0 u1 i).mp hsm⟩
  · -- 合取 25 ← real_model_azim2（:3310；supercrit 定义等价 2*hplus < dist）
    intro i h
    obtain ⟨hx, hsm, hsc⟩ := h
    obtain ⟨h4, hn5⟩ := (pk_qx_geometric V f u0 u1 i).mp hx
    exact real_model_azim2 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ⟨⟨h4, hn5⟩, (pk_hassmall_geometric V f u0 u1 i).mp hsm, hsc⟩

/-- T4 切片 R6（合取 26-33）：qy 族——3-cell 配对和与两个 3a/3b 非负、
0.008·azim 下界、small_eta 混合 spine5 三件、txq 窗口 3·cc_eps。
资产状态：**deferred-compute（外部认证锚）**——八枚 bank 叶全 ⬜。
-- NEEDS: cell23/3a/3b/gr/pema/pemb/tew/txq 逐条证书。 -/
theorem pkrmQy (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    (∀ i, cc_qy_v11 (cc_data_v8 V f u0 u1) i →
        cc_gg3a_v11 (cc_data_v8 V f u0 u1) i + cc_gg3b_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qy_v11 (cc_data_v8 V f u0 u1) i →
        (0 : ℝ) ≤ cc_gg3a_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qy_v11 (cc_data_v8 V f u0 u1) i →
        (0 : ℝ) ≤ cc_gg3b_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qy_v11 (cc_data_v8 V f u0 u1) i →
        (0.008 : ℝ) * cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qy_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_small_eta_v11 (cc_data_v8 V f u0 u1) i ∧
          ¬cc_small_eta_v11 (cc_data_v8 V f u0 u1) (i + 1) ∧
          cc_azim_v11 (cc_data_v8 V f u0 u1) i < 1.074 →
        a_spine5 + b_spine5 * cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qy_v11 (cc_data_v8 V f u0 u1) i ∧
          ¬cc_small_eta_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_small_eta_v11 (cc_data_v8 V f u0 u1) (i + 1) ∧
          cc_azim_v11 (cc_data_v8 V f u0 u1) i < 1.074 →
        a_spine5 + b_spine5 * cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qy_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_small_eta_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_small_eta_v11 (cc_data_v8 V f u0 u1) (i + 1) →
        a_spine5 + b_spine5 * cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤
          cc_gg_v11 (cc_data_v8 V f u0 u1) i) ∧
      (∀ i, cc_qy_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_small_eta_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_small_eta_v11 (cc_data_v8 V f u0 u1) (i + 1) ∧
          (1.946 : ℝ) ≤ cc_azim_v11 (cc_data_v8 V f u0 u1) i ∧
          cc_azim_v11 (cc_data_v8 V f u0 u1) i ≤ 2.089 →
        (3 : ℝ) * cc_eps ≤ cc_gg_v11 (cc_data_v8 V f u0 u1) i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 合取 26 ← real_model_cell23（:3430）
    intro i hqy
    exact real_model_cell23 V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc
      hcey hr i ((pk_qy_geometric V f u0 u1 i).mp hqy)
  · -- 合取 27 ← real_model_3a（:3485）
    intro i hqy
    exact real_model_3a V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ((pk_qy_geometric V f u0 u1 i).mp hqy)
  · -- 合取 28 ← real_model_3b（:3496）
    intro i hqy
    exact real_model_3b V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ((pk_qy_geometric V f u0 u1 i).mp hqy)
  · -- 合取 29 ← real_model_gr（:3507）
    intro i hqy
    exact real_model_gr V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ((pk_qy_geometric V f u0 u1 i).mp hqy)
  · -- 合取 30 ← real_model_pema（:3524）
    intro i h
    obtain ⟨hqy, hse1, hse2, haz⟩ := h
    exact real_model_pema V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ⟨(pk_qy_geometric V f u0 u1 i).mp hqy, hse1, hse2, haz⟩
  · -- 合取 31 ← real_model_pemb（:3536）
    intro i h
    obtain ⟨hqy, hse1, hse2, haz⟩ := h
    exact real_model_pemb V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ⟨(pk_qy_geometric V f u0 u1 i).mp hqy, hse1, hse2, haz⟩
  · -- 合取 32 ← real_model_tew（:3635）
    intro i h
    obtain ⟨hqy, hse1, hse2⟩ := h
    exact real_model_tew V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ⟨(pk_qy_geometric V f u0 u1 i).mp hqy, hse1, hse2⟩
  · -- 合取 33 ← real_model_txq（:3623）
    intro i h
    obtain ⟨hqy, hse1, hse2, haz1, haz2⟩ := h
    rw [pk_three_eps]
    exact real_model_txq V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey
      hr i ⟨(pk_qy_geometric V f u0 u1 i).mp hqy, hse1, hse2, haz1, haz2⟩

/-- HOL `cc_real_model_data`: the geometric wedge data satisfies the full
cc_v11 real model (consumes all the `real_model_*` bank entries above).
T4 展开波（2026-10-08）：证明体由单根 `sorry` 换为六具名切片（上方 R1-R6）的
显式装配——冻结陈述签名不变；R1 为零 sorryAx 真推导，R2-R6 的债 = 29 枚
具名 bank 叶（见切片注记）。 -/
theorem cc_real_model_data (V : Set V3) (f : ℕ → V3) (w0 : V3) (n : ℕ) (u0 u1 : V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    cc_real_model_v11 (cc_data_v8 V f u0 u1) :=
  -- cc_real_model_v11 为 33 合取项右结合链：六切片按逐合取项投影装配
  have hpp := pkrmPeriodic V f u0 u1 n hper hsize
  have ha := pkrmAzim V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey hr
  have hq := pkrmQuarter V u0 u1 w0 n f hnl hox hn hp hs hsize h0 h1 hper hnc
    hcey hr
  have hqu := pkrmQu V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey hr
  have hqx := pkrmQx V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey hr
  have hqy := pkrmQy V u0 u1 w0 n f hnl hn hp hs hsize h0 h1 hper hnc hcey hr
  ⟨hpp.1, hpp.2.1, hpp.2.2.1, hpp.2.2.2,
    ha.1, ha.2.1, ha.2.2,
    hq,
    hqu.1, hqu.2.1, hqu.2.2.1, hqu.2.2.2.1, hqu.2.2.2.2.1, hqu.2.2.2.2.2.1,
      hqu.2.2.2.2.2.2.1, hqu.2.2.2.2.2.2.2.1, hqu.2.2.2.2.2.2.2.2,
    hqx.1, hqx.2.1, hqx.2.2.1, hqx.2.2.2.1, hqx.2.2.2.2.1, hqx.2.2.2.2.2.1,
      hqx.2.2.2.2.2.2.1, hqx.2.2.2.2.2.2.2,
    hqy.1, hqy.2.1, hqy.2.2.1, hqy.2.2.2.1, hqy.2.2.2.2.1, hqy.2.2.2.2.2.1,
      hqy.2.2.2.2.2.2.1, hqy.2.2.2.2.2.2.2⟩

/-- HOL `CELL_CLUSTER_ESTIMATE_PROPS`: a failing cell-cluster inequality
yields the compressed-model witness.
T4 展开波（2026-10-08）：证明体由单根 `sorry` 换为 `LEAF_RANK_PROPS`（见证
层骨架，:2955 同文件）+ 基数步真推导 + `cc_real_model_data`（real-model 切片
层，:4139 同文件）的显式装配——冻结陈述签名不变。债 = LEAF_RANK_PROPS
（W1/W2 + 三在库叶）+ cc_real_model_data（六切片）；基数合取项
`n = cc_card_v11 (cc_data_v8 …)` 为零 sorryAx 真叶（`cc_card_data` rfl +
`HasSizeP25`）。 -/
theorem CELL_CLUSTER_ESTIMATE_PROPS (V : Set V3) (hp : Packing V) (hs : saturated V)
    (hcc : ¬ cellClusterInequality V) (hnl : pack_nonlinear_non_ox3q1h)
    (hox : ox3q1hP25) :
    ∃ u0 u1 n f, 1 < n ∧
      ∑ i ∈ Finset.Icc 0 (n - 1), gg_mcell V f u0 u1 i < 0 ∧
      n = cc_card_v11 (cc_data_v8 V f u0 u1) ∧
      cc_bool_model_v11 (cc_data_v8 V f u0 u1) ∧
      cc_bool_prep_v11 (cc_data_v8 V f u0 u1) ∧
      cc_real_model_v11 (cc_data_v8 V f u0 u1) := by
  obtain ⟨u0, u1, n, w0, f, hn, hsize, hu0ne, hlo, hhi, hnc, hr, h0, h1, hper,
    hleaf, hcey, hneg, -, -, hbm, hbp⟩ := LEAF_RANK_PROPS V hp hs hcc hnl
  refine ⟨u0, u1, n, f, hn, hneg, ?_, hbm, hbp, ?_⟩
  · -- 基数步（真叶）：cc_card_data（rfl 投影）+ HasSizeP25
    rw [cc_card_data]
    exact hsize.2.symm
  · exact cc_real_model_data V f w0 n u0 u1 hnl hox hn hp hs hsize h0 h1 hper
      hnc hcey hr

/-- HOL `OXLZLEZ`: THE CAPSTONE — the cell-cluster inequality, conditional
on the two certified Merge_ineq/Oxl_def banks.  Proof: a failure yields
(CELL_CLUSTER_ESTIMATE_PROPS) a compressed model with negative gg-sum;
`GRHIDFA_concl` (PackingAuto3, the OXLZLEZ1 conclusion) derives `False`.
DISCHARGES: does not verbatim-match `OXLZLEZ_concl` (PackingAuto2.lean:838)
which lacks the two bank antecedents. -/
theorem OXLZLEZ (V : Set V3) (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25)
    (hp : Packing V) (hs : saturated V) : cellClusterInequality V := by
  by_contra hcc
  obtain ⟨u0, u1, n, f, hn, hneg, hcard, hbm, hprep, hr⟩ :=
    CELL_CLUSTER_ESTIMATE_PROPS V hp hs hcc hnl hox
  have hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 (cc_data_v8 V f u0 u1) - 1),
      cc_gg_v11 (cc_data_v8 V f u0 u1) i < 0 := by
    rw [← hcard, (cc_real_data V f u0 u1).2.1]
    exact hneg
  exact GRHIDFA_concl _ hbm hprep hr hsum

/-- HOL `PACKING_CHAPTER_MAIN_CONCLUSION`: the packing chapter main
conclusion, via `RDWKARC` + `TSKAJXY`.  The HOL proof rewrites with
`Pack_concl.TSKAJXY_statement` and applies `Tskajxy.TSKAJXY`.  The Lean
`TSKAJXY` (PackingAuto21:1407) is the pointwise form of
`TSKAJXY_statement` with the extra `pack_nonlinear_non_ox3q1h` bank
antecedent, which is exactly this theorem's `hnl` — so the HOL rewrite +
match assembly goes through verbatim. -/
theorem PACKING_CHAPTER_MAIN_CONCLUSION (hkc : ¬ keplerConjecture)
    (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25) :
    ∃ V : Set V3, Packing V ∧ V ⊆ ballAnnulus ∧ ¬ localAnnulusInequality V := by
  refine RDWKARC_concl hkc ?_ ?_
  · -- the `OXLZLEZ` arm of the HOL proof: `ASM_REWRITE_TAC[]` discharges
    -- both banks from the context.
    intro V hp hs
    exact OXLZLEZ V hnl hox hp hs
  · -- `REWRITE_TAC[Pack_concl.TSKAJXY_statement]` then `MATCH_MP_TAC
    -- Tskajxy.TSKAJXY`: the statement is the pointwise shape of PA21's
    -- capstone with the bank antecedent taken from `hnl`.
    intro V X hs hp hm hcrit
    exact TSKAJXY V X hnl hs hp hm hcrit

/-! ## Backfill: remaining source statements (kept with the file's section
order flattened; all giants) -/

/-- HOL `DIHV_EQ_0_PI_EQ_COPLANAR_ALT`.  Proof: `dihV = 0` forces
`azim v0 v1 w1 w2 = 0` (below `pi` via AZIM_DIHV_SAME; above `pi` the
complement identity would push `azim` to `2*pi`), and an `azim`-zero pair
puts `w1` in the `affGt`-ray of `w2`, hence in `affineSpan {v0, v1, w2}` —
making the quadruple coplanar. -/
theorem DIHV_EQ_0_PI_EQ_COPLANAR_ALT (v0 v1 w1 w2 : V3)
    (hnc : ¬ Coplanar ({v0, v1, w1, w2} : Set V3)) :
    ¬ (dihV v0 v1 w1 w2 = 0) := by
  classical
  -- a point collinear with the axis already lives in the axis line
  have axisLine : ∀ x : V3, Collinear3 v0 v1 x →
      x ∈ (affineSpan ℝ ({v0, v1} : Set V3)) := by
    intro x hx
    have hv : v1 ≠ v0 := by
      intro he
      have hset : ({v0, v1, w1, w2} : Set V3) = ({v0, w1, w2} : Set V3) := by
        rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      exact hnc (by rw [hset]; exact coplanar_triple v0 w1 w2)
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := v0) (w := v1) (w1 := x) hv).mp hx
    have hmem := smul_vsub_vadd_mem_affineSpan_pair (k := ℝ) (p₁ := v0) (p₂ := v1) (r := c)
    have heq : (c • (v1 -ᵥ v0) +ᵥ v0 : V3) = x := by
      rw [vadd_eq_add, vsub_eq_sub, ← hc]; abel
    rwa [heq] at hmem
  -- a plane spanned by the axis and either point contains the whole quadruple
  have copPlane : ∀ x y : V3, Collinear3 v0 v1 x →
      Coplanar ({v0, v1, x, y} : Set V3) := by
    intro x y hx
    refine ⟨v0, v1, y, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpe | hpe | hpe | hpe
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
    · rw [hpe]
      exact SetLike.le_def.mp (affineSpan_mono ℝ (by
        intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto))
        (axisLine x hx)
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
  have h1 : ¬ Collinear3 v0 v1 w1 := fun hc => hnc (copPlane w1 w2 hc)
  have h2 : ¬ Collinear3 v0 v1 w2 := by
    intro hc
    have hset : ({v0, v1, w1, w2} : Set V3) = ({v0, v1, w2, w1} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    exact hnc (by rw [hset]; exact copPlane w2 w1 hc)
  intro hdih
  rcases lt_or_ge (azim v0 v1 w1 w2) Real.pi with hlt | hge
  · have hazi : azim v0 v1 w1 w2 = 0 := by
      rw [azim_dihv_same h1 h2 hlt]; exact hdih
    have hw1gt : w1 ∈ affGt ({v0, v1} : Set V3) {w2} := (azim_eq_zero_iff h1 h2).mp hazi
    have hwv : v0 ≠ v1 := fun he => h1 (collinear3_of_eq he.symm)
    have hw20 : w2 ≠ v0 := fun he => h2 (collinear3_pair_left he)
    have hw21 : w2 ≠ v1 := fun he => h2 (collinear3_pair_right he)
    obtain ⟨c, -, h, hcomb⟩ :=
      (affGt_pair_iff (v0 := v0) (v1 := v1) (x := w2) (y := w1) hwv hw20 hw21) |>.mp hw1gt
    refine hnc ⟨v0, v1, w2, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpe | hpe | hpe | hpe
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
    · rw [hpe]
      have hw2mem : w2 ∈ (affineSpan ℝ ({v0, v1, w2} : Set V3)) :=
        mem_affineSpan (k := ℝ) (by simp : w2 ∈ ({v0, v1, w2} : Set V3))
      have hw1eq : (w1 - w2 : V3) = (1 - c - h) • (v0 - w2) + h • (v1 - w2) := by
        rw [show (w1 : V3) = v0 + (w1 - v0) from by abel, hcomb]; module
      have hvv : (w1 - w2 : V3) ∈ vectorSpan ℝ ({v0, v1, w2} : Set V3) := by
        rw [hw1eq, vectorSpan_eq_span_vsub_set_right ℝ (show w2 ∈ ({v0, v1, w2} : Set V3) from
          by simp)]
        have himg1 : (v0 -ᵥ w2 : V3) ∈
            (fun x : V3 => x -ᵥ w2) '' ({v0, v1, w2} : Set V3) := ⟨v0, by simp, rfl⟩
        have himg2 : (v1 -ᵥ w2 : V3) ∈
            (fun x : V3 => x -ᵥ w2) '' ({v0, v1, w2} : Set V3) := ⟨v1, by simp, rfl⟩
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span himg1))
          (Submodule.smul_mem _ _ (Submodule.subset_span himg2))
      have hres := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan hw2mem hvv
      rwa [vadd_eq_add, sub_add_cancel] at hres
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
  · have hazi := azim_dihv_compl h1 h2 hge
    rw [hdih] at hazi
    have h2pi := azim_lt_two_pi v0 v1 w1 w2
    linarith

/-- HOL `AZIM_ZERO_SHIFT`: two leaves subtend the same azimuth from `u2`
exactly when they lie on the same ray from the stem axis.  Both iff sides
chain through `w' ∈ affGt {u0, u1} {w}` (AZIM_EQ_AZIM ↔ AZIM_EQ_0_ALT). -/
theorem AZIM_ZERO_SHIFT (u0 u1 u2 w w' : V3)
    (h1 : ¬ Collinear3 u0 u1 u2) (h2 : ¬ Collinear3 u0 u1 w)
    (h3 : ¬ Collinear3 u0 u1 w') :
    (azim u0 u1 u2 w = azim u0 u1 u2 w' ↔ azim u0 u1 w w' = 0) :=
  (azim_eq_azim_iff h1 h2 h3).trans (azim_eq_zero_iff_alt h2 h3).symm

/-- HOL `ORDER_AZIM_SUM2Pi0`: the azim-sorted leaf walk winds once.
2026-10-12 转真（零新债）：azim 链算术（与 `S_LEAF_IN_WEDGE_GE` 同款工具）——
移位恒等式（`AZIM_BASE_SHIFT_LE`）+ 补角（`azim_compl`）给出
`azim (g i) (g (i+1)) = a_{i+1} - a_i` 与回卷项 `2π - (a_{n-1} - a_0)`，
`Finset.range` 上归纳望远镜求和即得 2π。 -/
theorem ORDER_AZIM_SUM2Pi0 (x y z : V3) (n : ℕ) (g : ℕ → V3)
    (h1 : ¬ Collinear3 x y z) (h2 : ∀ i, i < n → ¬ Collinear3 x y (g i))
    (h3 : g n = g 0) (hn : 1 < n)
    (h4 : ∀ j k, j < n → k < n → j < k → azim x y z (g j) < azim x y z (g k)) :
    ∑ i ∈ Finset.Icc 0 (n - 1), azim x y (g i) (g (i + 1)) = 2 * Real.pi := by
  have hcol : ∀ i, i < n → ¬ Collinear3 x y (g i) := h2
  have key : ∀ p q, p < q → q < n →
      azim x y (g p) (g q) = azim x y z (g q) - azim x y z (g p) := by
    intro p q hpq hqn
    have hchain : azim x y z (g p) < azim x y z (g q) := h4 p q (by omega) hqn hpq
    have h := AZIM_BASE_SHIFT_LE x y z (g p) (g p) (g q)
      h1 (hcol p (by omega)) (hcol p (by omega)) (hcol q (by omega)) (le_refl _) hchain.le
    rw [azim_self] at h
    linarith
  have comp : ∀ p q, p < q → q < n →
      azim x y (g q) (g p)
        = 2 * Real.pi - (azim x y z (g q) - azim x y z (g p)) := by
    intro p q hpq hqn
    have hchain : azim x y z (g p) < azim x y z (g q) := h4 p q (by omega) hqn hpq
    have hpos : (0:ℝ) < azim x y (g p) (g q) := by
      rw [key p q hpq hqn]; linarith
    have hc := azim_compl (hcol p (by omega)) (hcol q (by omega))
    rw [key p q hpq hqn,
      if_neg (by rw [← key p q hpq hqn]; exact ne_of_gt hpos)] at hc
    exact hc
  have hIcc : Finset.Icc 0 (n - 1) = Finset.range n := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hIcc]
  -- telescope: sum over range m of azim (g i) (g (i+1)) = a_m - a_0
  have tel : ∀ m, 1 ≤ m → m ≤ n - 1 →
      ∑ i ∈ Finset.range m, azim x y (g i) (g (i + 1))
        = azim x y z (g m) - azim x y z (g 0) := by
    intro m hm1 hm2
    induction m with
    | zero => omega
    | succ k ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · subst hk0
        simp only [Finset.sum_range_zero, Finset.sum_empty, zero_add]
        have hstep := key 0 1 (by omega) (by omega)
        linarith
      · have hkm : k ≤ n - 1 := by omega
        have hstep := key k (k + 1) (by omega) (by omega)
        linarith [ih hk1 hkm]
  have hsplit : ∑ i ∈ Finset.range n, azim x y (g i) (g (i + 1))
      = (∑ i ∈ Finset.range (n - 1), azim x y (g i) (g (i + 1)))
        + azim x y (g (n - 1)) (g n) := by
    have hs := Finset.sum_range_succ (fun i => azim x y (g i) (g (i + 1))) (n - 1)
    rw [show n - 1 + 1 = n from by omega] at hs
    exact hs
  rw [hsplit]
  have hwrap : azim x y (g (n - 1)) (g n) = 2 * Real.pi
      - (azim x y z (g (n - 1)) - azim x y z (g 0)) := by
    rw [h3]
    exact comp 0 (n - 1) (by omega) (by omega)
  linarith [tel (n - 1) (by omega) (Nat.le_refl _)]

private theorem p25_take_append_cancel {α : Type*} {l1 l2 : List α} (n : ℕ)
    (h : n ≤ l1.length) : (l1 ++ l2).take n = l1.take n := by
  induction l1 generalizing n with
  | nil => simp at h; simp [h]
  | cons a t ih =>
    cases n with
    | zero => simp
    | succ n =>
      have key : (t ++ l2).take n = t.take n := ih n (Nat.le_of_succ_le_succ h)
      simp [key]

/-- HOL `INITIAL_SUBLIST_TRUNCATE`. -/
theorem INITIAL_SUBLIST_TRUNCATE (vl ul : List V3) (hl : ul.length = 4)
    (h1 : initialSublist vl ul)
    (h2 : ¬ initialSublist vl (truncateSimplex 2 ul)) : vl = ul := by
  obtain ⟨htrlen, htrsub⟩ := Classical.epsilon_spec (p := fun t : List V3 =>
      t.length = 3 ∧ initialSublist t ul)
      ⟨ul.take 3, by simp [hl], ⟨ul.drop 3, (List.take_append_drop 3 ul).symm⟩⟩
  obtain ⟨zl, hzl⟩ := htrsub
  obtain ⟨yl, hyl⟩ := h1
  have hlen : vl.length + yl.length = 4 := by rw [← hl, hyl, List.length_append]
  by_cases hk : 4 ≤ vl.length
  · have hy0 : yl.length = 0 := by omega
    have hye : yl = [] := by
      cases yl with
      | nil => rfl
      | cons a t => simp at hy0
    rw [hye, List.append_nil] at hyl
    exact hyl.symm
  · exfalso
    apply h2
    have e1 : vl = ul.take vl.length := by
      rw [hyl, p25_take_append_cancel vl.length (Nat.le_refl vl.length), List.take_length]
    have e2 : ul.take vl.length = (truncateSimplex 2 ul).take vl.length := by
      conv_lhs => rw [hzl]
      exact p25_take_append_cancel vl.length (by rw [htrlen]; omega)
    have e3 : initialSublist vl (truncateSimplex 2 ul) := by
      rw [e1, e2]
      exact ⟨(truncateSimplex 2 ul).drop vl.length,
        (List.take_append_drop vl.length (truncateSimplex 2 ul)).symm⟩
    exact absurd e3 h2

/-- HOL `AFF_DEP_COPLANAR`.  2026-10-13 转真：backward 方向 = 独立性沿
`Set.Finite.subtypeEquivToFinset` 传输到 `toFinset`，再以
`AffineIndependent.card_le_card_of_subset_affineSpan`（Mathlib
FiniteDimensional.lean:256，`#s ≤ #t`）对 Coplanar 见证三元组（`#t ≤ 3`）
夹出 `4 ≤ 3` 矛盾；forward 方向即私有件 `p25_affdep4_coplanar`。 -/
theorem AFF_DEP_COPLANAR (a b c d : V3)
    (hc : Set.ncard ({a, b, c, d} : Set V3) = 4) :
    (affineDependent ({a, b, c, d} : Set V3) ↔ Coplanar ({a, b, c, d} : Set V3)) := by
  constructor
  · exact p25_affdep4_coplanar
  · intro hcop
    obtain ⟨u, v, w, hsub⟩ := hcop
    by_contra hnd
    have hindep : AffineIndependent ℝ (fun x : ({a, b, c, d} : Set V3) => (x : V3)) :=
      not_not.mp hnd
    have hfin : ({a, b, c, d} : Set V3).Finite :=
      Set.Finite.insert a (Set.Finite.insert b (Set.Finite.insert c (Set.finite_singleton d)))
    have htfin : ({u, v, w} : Set V3).Finite :=
      Set.Finite.insert u (Set.Finite.insert v (Set.finite_singleton w))
    -- transfer independence along the canonical subtype equivalence
    have hco : AffineIndependent ℝ
        ((fun x : ({a, b, c, d} : Set V3) => (x : V3)) ∘ hfin.subtypeEquivToFinset.symm) :=
      (affineIndependent_equiv (p := fun x : ({a, b, c, d} : Set V3) => (x : V3))
        hfin.subtypeEquivToFinset.symm).2 hindep
    have hst : ((hfin.toFinset : Set V3)) ⊆
        (affineSpan ℝ ((htfin.toFinset : Set V3))) := by
      rw [Set.Finite.coe_toFinset hfin, Set.Finite.coe_toFinset htfin]
      exact hsub
    have hle := AffineIndependent.card_le_card_of_subset_affineSpan (k := ℝ) hco hst
    have hcard1 : hfin.toFinset.card = 4 := by
      rw [← Set.ncard_eq_toFinset_card ({a, b, c, d} : Set V3) hfin]; exact hc
    have hcard2 : htfin.toFinset.card ≤ 3 := by
      rw [← Set.ncard_eq_toFinset_card ({u, v, w} : Set V3) htfin]
      have q1 := Set.ncard_insert_le (u : V3) ({v, w} : Set V3)
      have q2 := Set.ncard_insert_le (v : V3) ({w} : Set V3)
      have q3 : Set.ncard ({w} : Set V3) = 1 := Set.ncard_singleton _
      omega
    have hcon : (4 : ℕ) ≤ 3 := by
      rw [← hcard1]
      exact hle.trans hcard2
    exact absurd hcon (by omega)

/-- HOL `HL_IMP_BARV`. -/
theorem HL_IMP_BARV (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hnc : ¬ Coplanar (setOfList ul)) (hsub : setOfList ul ⊆ V)
    (hhl : hl ul < Real.sqrt 2) (hb : barV V 2 (truncateSimplex 2 ul))
    (hlen : ul.length = 4) : barV V 3 ul := by
  sorry

end Kepler.Text
