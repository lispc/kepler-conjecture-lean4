/-
PackingAuto24: port of `scripts/packing/REUHADY.hl` (Flyspeck chapter
"packing / Marchal cells", Vu Khac Ky, 8357 lines; 1 def + 11 theorems,
headlined by the measure-splitting/annulus book lemma `REUHADY1`).

FILE MAP (how this feeds the final Kepler count)
  The chapter establishes that, along a short edge `u0u1` of a saturated
  packing, the Marchal cells lying inside the closed azimuth wedge
  `wedge_ge u0 u1 n1 n2` have total dihedral angle exactly
  `azim u0 u1 n1 n2` (`REUHADY1`, the 8100-line giant refinement proof).
  Supporting kit: Harrison wedge lemmas (`WEDGE_SIMPLE`,
  `WEDGE_GE_WEDGE`: closed wedge = open wedge + the two azimuth level
  sets), Harrison `Arg`/halfline lemmas (`ARG_EQ_SUBSET_HALFLINE`,
  `ARG_DIV_EQ_SUBSET_HALFLINE`), the coplanarity of azimuth level sets
  (`COPLANAR_AZIM_EQ`), and the measure facts
  `MEASURABLE_CONIC_CAP_WEDGE_GE` /
  `VOLUME_CONIC_CAP_WEDGE_GE_VS_CONIC_CAP` (wedge proportionality of
  conic-cap volume) that downstream annulus estimates consume.
  Downstream in HL, OXLZLEZ3.hl instantiates `REUHADY1` on leaf cells
  (its `REUHADY`); the pack_concl conclusions `REUHADY_concl` /
  `REUHADY_concl_version2` (already stated in PackingAuto2) are
  discharged from `REUHADY1` only with the extra leaf-cell wedge
  disjointness input (HL `Leaf_cell.WEDGE_GE_ALMOST_DISJOINT`), so the
  capstones here are stated statement-identically to PackingAuto2 for
  merge-time discharge; since 2026-09-30 they are WIRED to `REUHADY1`
  with every other hypothesis synthesized genuinely in this file
  (wedge disjointness included), so their remaining content is exactly
  `REUHADY1` + the `p24_REUHADY_nondeg` shim.

ENCODING NOTES
  - HOL `real^3` <-> `V3` (Kepler.Geom); `packing` <-> `Packing`;
    `saturated` <-> `PackingAuto2.saturated`; `hl`, `barV`,
    `truncate_simplex`, `set_of_list`, `EL 2`, `mcell_set`, `edgeX`,
    `dihX`, `sum` over sets, `aff_ge`, `wedge_ge` <-> the PackingAuto2
    definitions `hl`, `barV`, `truncateSimplex`, `setOfList`, `elV`,
    `mcellSet`, `edgeX`, `setSum`, `affGe`, `wedgeGe` (imported;
    `wedge_ge` is NOT redefined here).
  - HOL `wedge` (open wedge) <-> `Kepler.Text.wedge` (PackingAuto15 /
    Kepler.Geom.Azim); `conic_cap` <-> `conicCap` (PackingAuto15);
    `collinear{...}` <-> `Collinear3`; `coplanar` <-> `Coplanar ℝ`.
  - HOL `real^2` content (the `Arg` halfline lemmas, planar rays) <->
    `ℂ`: `Complex.arg` is native; the closed halfline `aff_ge {vec 0}
    {b}` is the closed ray `{z : ℂ | ∃ t ≥ 0, z = t • b}` (real-scalar
    smul), matching PackingAuto22's real^2-↔-ℂ precedent.
  - `measurable s` <-> `MeasurableSet s` for Lebesgue `volume`
    (PackingAuto10 style); HOL `vol` <-> `volume.real` (real-valued
    Lebesgue measure, `MeasureTheory.Measure.real` under
    `open MeasureTheory`).

SORRY INVENTORY (giants, with blockers)
  - `REUHADY1`: the 8100-line `prove_by_refinement` giant (HL lines
    239-8356) — REDUCED (2026-09-30 REUHADY wave): the preamble segments
    (a) `barV V 1 [u0;u1]` (= `p24_barV1`, first genuine copy; PA15:578
    twin still a ported sorry), (b) GLTVHUM k-decomposition at k=3
    (= `p24_gltvhum3`, via PA6:1108 public genuine) and (c) leaf-triple
    singleton + omega identification (= `p24_leaf_singleton`, via
    PA12:1677 + PA5:2296, both closed 2026-09-30; PA24 now imports PA12),
    composed into the fan structure `p24_voronoi_pair_split`, are all
    GENUINE (private chain before the theorem). The single residual
    `sorry` is exactly (d), the dihedral-splitting bulk (HL ~400-8356:
    mcell4 leaf-cell realization over the fan + conic-cap/azimuth measure
    sandwich); full map in the REUHADY1 docstring.
  - `coplanarAzimEq`: FILLED (2026-09-30) from the documented route
    (frame + `azim_eq_azim_iff` + coplanarity plumbing; ingredients
    `p24_exists_azim_point` / `p24_mem_affineSpan_triple`).
  - `measurableConicCapWedgeGe`: FILLED (2026-09-30) via the documented
    ℂ-transport route (private `azim_sub_self` copy + `azim_eq_ang_of_frame`
    + `measurable_ang`, CCV `ccv_measSet_wedge` template): the closed wedge
    `wedgeGe` itself is the continuous preimage of a ℂ Borel fan whose
    closed interval bounds absorb both boundary azimuth level sets, so
    neither `coplanarAzimEq` nor coplanar-nullness is needed here.
  - `volumeConicCapWedgeGeVsConicCap`: FILLED (2026-09-30) once CCV
    (ConicCapVolume) delivered `volumeConicCap` / `volumeConicCapWedge`;
    the closed-vs-open wedge gap is the two azimuth boundary level sets,
    coplanar by `coplanarAzimEq` and null by `p24_coplanar_measure_null`
    (the `MEASURE_NEGLIGIBLE_SYMDIFF` content, as an outer-measure
    sandwich).
  - `REUHADY_p24` / `REUHADY_version2_p24`: RESTRUCTURED (2026-09-30,
    最小件波) — no longer standalone `sorry`s; both now apply `REUHADY1`
    with every other hypothesis synthesized genuinely in this file:
    `WEDGE_GE_ALMOST_DISJOINT_p24` (genuine, gives `REUHADY1`'s closed
    wedge-intersection hypothesis), `p24_REUHADY_extract` (barV/pair
    extraction: `u0,u1 ∈ V` + `¬Collinear3`), `p24_hl_pair_lt_sqrt2`
    (pair half-length, `HL_2` local copy). REMAINING sorryAx inputs:
    `REUHADY1` itself + the `p24_REUHADY_nondeg` NEEDS shim (the
    OXLZLEZ3 `FCHKUGT`/`EWYBJUA` degenerate-branch exclusion;
    PA18:2159/:2532 hold sorried twins).
  - `WEDGE_GE_ALMOST_DISJOINT_p24`: FILLED (2026-09-30) genuinely — the
    leaf_cell.hl:154-208 closed-wedge disjointness over
    `p24_exp_azim_mul` (azim exp-additivity via `azim_eq_ang_of_frame` +
    `ang_mul_exp`) and `azim_compl`. PA18:906's same-name twin remains a
    `ported sorry`; pick one at merge.
  - `GRUTOTI1_concl_p24`: SHIMMED (2026-09-19) to the statement-identical
    `PackingAuto2.GRUTOTI1_concl` interface (still `sorry`ed there; the
    Auto23 lane owns the real proof). Delete the `_p24` copy at merge.
    A public re-export `GRUTOTI1_concl_p24_pub` (same file, same
    statement) was added so the PackingConcl assembly can name the twin
    (its `private` is file-scoped).
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto12
import Kepler.Text.ConicCapVolume
import Kepler.Text.Polytope
import Kepler.Geom.Azim
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## `_p24` definition copies (`PackingAuto15.olean` now builds in this
checkout, but PA15 defines `Kepler.Text.wedge`, which would shadow this
file's open-wedge (`Kepler.Geom.wedge`) usage on import — so the chapter
keeps private copies instead of importing PA15; delete at merge into the
PackingAuto15 lane) -/

/-- HOL `conic_cap` (flyspeck_multivariate.ml:4832; PackingAuto15:109
copy): `conic_cap v0 v1 r a = normball v0 r INTER rcone_gt v0 v1 a`.
The HOL open `wedge` needs no copy: `Kepler.Geom.wedge` (Azim.lean:63)
is definitionally the PackingAuto15:113 `wedge`. -/
def conicCapP24 (v0 v1 : V3) (r a : ℝ) : Set V3 :=
  Metric.closedBall v0 r ∩ rconeGt v0 v1 a

/-! ## Private glue lemmas (azim degeneracy, list kit) -/

/-- HOL `AZIM_DEGENERATE` (flyspeck.ml, `azim_def` if-branch):
degenerate frames carry zero azimuth. -/
private theorem azim_eq_zero_of_collinearY (v0 v1 w y : V3) (h : Collinear3 v0 v1 y) :
    azim v0 v1 w y = 0 := by
  unfold azim
  exact if_pos (Or.inr h)

/-- HOL `UNIV_GSPEC` (REUHADY.hl:157). -/
theorem univGspec : {x : V3 | True} = (Set.univ : Set V3) := by
  rfl

/-- HOL `WEDGE_SIMPLE` (REUHADY.hl:68): the open wedge is the strict
azimuth interval (the `¬Collinear3` guard is implied by `0 < azim`). -/
theorem wedgeSimple (v0 v1 w1 w2 : V3) :
    wedge v0 v1 w1 w2 =
      {y | 0 < azim v0 v1 w1 y ∧ azim v0 v1 w1 y < azim v0 v1 w1 w2} := by
  ext y
  simp only [wedge, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    intro hc
    rw [azim_eq_zero_of_collinearY v0 v1 w1 y hc] at h1
    exact absurd h1 (by linarith)

/-- HOL `WEDGE_GE_WEDGE` (REUHADY.hl:77): the closed wedge is the open
wedge together with its two boundary azimuth level sets. (Union
parenthesization made explicit; `∪` associates in HOL.) -/
theorem wedgeGeWedge (v0 v1 w1 w2 : V3) :
    wedgeGe v0 v1 w1 w2 =
      wedge v0 v1 w1 w2 ∪ ({z | azim v0 v1 w1 z = 0} ∪
        {z | azim v0 v1 w1 z = azim v0 v1 w1 w2}) := by
  ext z
  have hb := azim_nonneg v0 v1 w1 w2
  simp only [wedgeGe, wedgeSimple, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨hle1, hle2⟩
    by_cases h0 : azim v0 v1 w1 z = 0
    · exact Or.inr (Or.inl h0)
    · rcases lt_or_eq_of_le hle2 with hlt | heq
      · exact Or.inl ⟨lt_of_le_of_ne hle1 (Ne.symm h0), hlt⟩
      · exact Or.inr (Or.inr heq)
  · rintro (h | h | h)
    · obtain ⟨hlt, hle2⟩ := h
      exact ⟨by linarith, hle2.le⟩
    · exact ⟨h.symm.le, by rw [h]; exact hb⟩
    · exact ⟨h ▸ hb, h.le⟩

/-- HOL `BARV_2_IMP_NOT_COLLINEAR_SET_OF_LIST` (REUHADY.hl:54): the
vertex set of a `barV V 2` simplex is not collinear. -/
theorem barV2_imp_not_collinear_setOfList (V : Set V3) (ul : List V3)
    (hP : Packing V) (hbar : barV V 2 ul) :
    ¬ Collinear ℝ (setOfList ul) := by
  intro hcol
  have hne : (setOfList ul) ≠ ∅ := by
    rintro hrfl
    have h1 : affDim (setOfList ul) = 2 := MHFTTZN1 V ul 2 hP hbar
    rw [affDim] at h1
    simp [hrfl] at h1
  have hd : affDim (setOfList ul) = 2 := MHFTTZN1 V ul 2 hP hbar
  rw [affDim, if_neg hne] at hd
  have hrank : Module.finrank ℝ (vectorSpan ℝ (setOfList ul)) ≤ 1 :=
    Collinear.finrank_le_one hcol
  exact absurd (by omega : (2 : ℤ) ≤ 1) (by norm_num)

/-! ## The REUHADY statement (REUHADY.hl:207 `REUHADY_concl1_new`) -/

/-- HOL `REUHADY_concl1_new` (REUHADY.hl:207-237): the Marchal cells in
the wedge `wedge_ge u0 u1 n1 n2` contribute total dihedral angle
`azim u0 u1 n1 n2` along the edge `u0u1`. -/
def REUHADY_concl1_new : Prop :=
  ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3) (n1 n2 : V3) (e : Set V3),
    saturated V →
    Packing V →
    u0 ∈ V →
    u1 ∈ V →
    u0 ≠ u1 →
    hl [u0, u1] < Real.sqrt 2 →
    e = {u0, u1} →
    wedgeGe u0 u1 n1 n2 ∩ wedgeGe u0 u1 n2 n1 ⊆
      affGe {u0, u1} {n1} ∪ affGe {u0, u1} {n2} →
    azim u0 u1 n1 n2 ≠ 0 →
    vl1 ≠ vl2 →
    hl vl1 < Real.sqrt 2 →
    hl vl2 < Real.sqrt 2 →
    barV V 2 vl1 →
    barV V 2 vl2 →
    setOfList (truncateSimplex 1 vl1) = e →
    setOfList (truncateSimplex 1 vl2) = e →
    n1 = elV vl1 2 →
    n2 = elV vl2 2 →
    (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 n1 n2 ∨ X ⊆ wedgeGe u0 u1 n2 n1) →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
      X ⊆ wedgeGe u0 u1 n1 n2} (fun t => dihX V t (u0, u1)) =
      azim u0 u1 n1 n2

/-! ## REUHADY1 分段私件链 (a)-(c)（2026-09-30 REUHADY 波，全部真证）

REUHADY1 前置三段（本文件 docstring 分步路线 (a)-(c)）的落地件：
(a) `p24_barV1`：`hl [u0,u1] < sqrt 2 → barV V 1 [u0,u1]`
    （marchal3.hl:1054 `HL_LE_SQRT2_IMP_BARV_1`；PA15:578 同名件仍是
    `ported sorry`，此处为公开首份真证；核心是 `p24_affDim_voronoiList2`
    ——bisector 平面方向 2 维 + packing 间距裕量造出一小块胞内补丁）；
(b) `p24_gltvhum3`：GLTVHUM k-分解在 `j = 1`、`k = 3` 处取件
    （PA6:1108 公开真证 `GLTVHUM_lemma1` 的直接应用）；
(c) `p24_leaf_singleton`：叶三元组的 voronoi 单点 + 外心 + omega 识别
    （PA12:1677 `VORONOI_LIST_3_SINGLETON_EXPLICIT` + PA5:2296
    `OMEGA_LIST_IN_VORONOI_LIST`，双前件 2026-09-30 已闭）；
(b)+(c) 合成 `p24_voronoi_pair_split`：配对 voronoi list 沿叶三元组
    分解为 `convexHull {ω₁, ω₂, circumcenter}` 之并（棱旁的 fan 结构）。
REUHADY1 本体的残余缺口只剩 (d)：闭楔内 mcell 二面角和的分裂主体
（HL ~400-8356 行），见 REUHADY1 证明内 NEEDS 记账。 -/

/-- PA15:553 `HL_2`（`hl [u,v] = dist u v / 2`）的本文件私拷：PA15 的
`Kepler.Text.wedge` 拷会与本文件 `wedge` 撞名，故不 import PA15；合并时
两者取一（证照 PackingAuto15.lean:552 逐字，`CIRCUMCENTER_2` 为 PA6:2975
公开真证）。（REUHADY 波从 pack_concl 段前移至此，供分段链 (a) 使用。） -/
private theorem p24_hl_pair (u v : V3) : hl [u, v] = dist u v / 2 := by
  have hset : setOfList [u, v] = ({u, v} : Set V3) := by
    ext x
    simp [setOfList]
  have hcc : circumcenter ({u, v} : Set V3) = midpoint ℝ u v := CIRCUMCENTER_2 u v
  have hexi : ∃ c : ℝ, ∀ w ∈ ({u, v} : Set V3),
      c = dist (circumcenter ({u, v} : Set V3)) w := by
    refine ⟨dist (midpoint ℝ u v) u, ?_⟩
    rw [hcc]
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw'
    · rfl
    · rcases Set.mem_singleton_iff.mp hw' with rfl
      simp
  have key : radV ({u, v} : Set V3) = dist (circumcenter ({u, v} : Set V3)) u :=
    (Classical.epsilon_spec (p := fun c : ℝ => ∀ w ∈ ({u, v} : Set V3),
      c = dist (circumcenter ({u, v} : Set V3)) w) hexi) u (Set.mem_insert u {v})
  have hhl : hl [u, v] = dist (circumcenter ({u, v} : Set V3)) u := by
    show radV (setOfList [u, v]) = _
    rw [hset, key]
  rw [hhl, hcc]
  simp
  ring

/-- Pythagoras on the inner product (PA12 idiom). -/
private theorem p24_pythI {u v : V3} (h : inner ℝ u v = 0) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, h]
  ring

/-- Real-linearity of `inner ℝ` in the left argument. -/
private theorem p24_hsmL (t : ℝ) (u v : V3) : inner ℝ (t • u) v = t * inner ℝ u v :=
  (inner_smul_real_left u v t).trans (smul_eq_mul t (inner ℝ u v))

/-- Dot functional on `V3`（Polytope `dotRight` 私拷）. -/
private def p24_dotR (a : V3) : V3 →ₗ[ℝ] ℝ where
  toFun x := a ⬝ᵥ x
  map_add' x y := by
    show a.ofLp ⬝ᵥ (x.ofLp + y.ofLp) = a.ofLp ⬝ᵥ x.ofLp + a.ofLp ⬝ᵥ y.ofLp
    rw [dotProduct_add]
  map_smul' r x := by
    show a.ofLp ⬝ᵥ (r • x.ofLp) = (RingHom.id ℝ) r • (a.ofLp ⬝ᵥ x.ofLp)
    rw [dotProduct_smul]
    simp

/-- The squared norm as the self dot product (PA14 bridge). -/
private theorem p24_norm_sq_dot (v : V3) : ‖v‖ ^ 2 = v ⬝ᵥ v := by
  have h := real_inner_self_eq_norm_sq v
  rw [← h, inner_eq_dot]

/-- For `a ≠ 0` the kernel of the dot functional has finrank `2`
（rank-nullity：range 是 `ℝ` 的非零子空间 = `⊤`）. -/
private theorem p24_finrank_ker_dot {a : V3} (ha : a ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (p24_dotR a)) = 2 := by
  have hDpos : (0:ℝ) < a ⬝ᵥ a := by
    rw [← p24_norm_sq_dot]
    exact pow_pos (norm_pos_iff.mpr ha) 2
  have hfa : p24_dotR a a = a ⬝ᵥ a := rfl
  have hrange_ne : LinearMap.range (p24_dotR a) ≠ ⊥ := by
    intro hbot
    have hx : p24_dotR a a ∈ LinearMap.range (p24_dotR a) := ⟨a, rfl⟩
    rw [hbot] at hx
    have h0 : p24_dotR a a = 0 := (Submodule.mem_bot (R := ℝ)).mp hx
    exact hDpos.ne' (by rw [← hfa, h0])
  have hnk := LinearMap.finrank_range_add_finrank_ker (p24_dotR a)
  have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
  rw [h3] at hnk
  have hfrle : Module.finrank ℝ (LinearMap.range (p24_dotR a)) ≤ 1 := by
    refine le_trans (Submodule.finrank_mono (le_top : LinearMap.range (p24_dotR a) ≤ _)) ?_
    simp
  have hfrne : Module.finrank ℝ (LinearMap.range (p24_dotR a)) ≠ 0 := by
    intro h
    apply hrange_ne
    exact (Submodule.finrank_eq_zero).mp h
  omega

/-- The bisector of a nondegenerate pair is a hyperplane, `affDim = 2`
（`BIS_EQ_HYPERPLANE`（PA5 公开）+ `affDim_hyperplane`（Polytope 公开））. -/
private theorem p24_affDim_bis_pair {u0 u1 : V3} (hne : u0 ≠ u1) :
    affDim (bis u0 u1) = 2 := by
  have hsub : u1 - u0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [BIS_EQ_HYPERPLANE]
  have heq : {x : V3 | 2 * ((u1 - u0) ⬝ᵥ x) = u1 ⬝ᵥ u1 - u0 ⬝ᵥ u0} =
      {x : V3 | (u1 - u0) ⬝ᵥ x = (u1 ⬝ᵥ u1 - u0 ⬝ᵥ u0) / 2} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [heq]
  exact affDim_hyperplane hsub _

/-- Segment (a) core: `affDim (voronoiList V [u0,u1]) = 2` under the
`hl < sqrt 2` margin (marchal3.hl:1054 `HL_LE_SQRT2_IMP_BARV_1`, case
`vl = [u0;u1]`).
Route: the pair cell is a convex subset of the bisector plane `bis u0 u1`
(affDim 2), and for `≥ 2`: with `p` the midpoint, `D` the 2-dim plane
direction and `R = (s - d/2)/8`, `s = sqrt(4 - (d/2)²) > d/2` (the
`hl < sqrt 2` margin, `d² < 8`), every other packing point `w` satisfies
`‖w - p‖ ≥ s` (sum-of-squares bound `‖w-p‖² = (‖w-u0‖²+‖w-u1‖²)/2 - (d/2)²`
via packing), while `p + v`, `v ∈ D`, `‖v‖ ≤ 2R`, is within
`d/2 + ‖v‖ ≤ d/2 + 2R ≤ s - 2R ≤ s - ‖v‖ ≤ ‖(p+v) - w‖` of both endpoints,
so the patch `p + v` lies in the pair cell; three patch points make two
independent directions `w1, w2 ∈ D` into differences of cell points, so the
cell's vectorSpan has finrank `≥ 2`. -/
private theorem p24_affDim_voronoiList2 (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) :
    affDim (voronoiList V [u0, u1]) = 2 := by
  classical
  set S : Set V3 := voronoiList V [u0, u1] with hSdef
  set p : V3 := u0 + (2:ℝ)⁻¹ • (u1 - u0) with hpdef
  set d : ℝ := dist u0 u1 with hddef
  have hdpos : (0:ℝ) ≤ d := dist_nonneg
  have hdlt : d < 2 * Real.sqrt 2 := by rw [p24_hl_pair] at hhl; linarith
  have hmid0 : p - u0 = (2:ℝ)⁻¹ • (u1 - u0) := by rw [hpdef]; module
  have hmid1 : p - u1 = -((2:ℝ)⁻¹ • (u1 - u0)) := by rw [hpdef]; module
  have hpu0 : ‖p - u0‖ = d / 2 := by
    rw [hmid0, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show (0:ℝ) < (2:ℝ)⁻¹ by norm_num), ← dist_eq_norm, dist_comm u1 u0,
      hddef]
    ring
  have hpu1 : ‖p - u1‖ = d / 2 := by
    rw [hmid1, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show (0:ℝ) < (2:ℝ)⁻¹ by norm_num), ← dist_eq_norm, dist_comm u1 u0,
      hddef]
    ring
  -- direction space `D` of the bisector plane and its dimension
  set D : Submodule ℝ V3 := LinearMap.ker (p24_dotR (u1 - u0)) with hDdef
  have hD2 : Module.finrank ℝ D = 2 :=
    p24_finrank_ker_dot (a := u1 - u0) (sub_ne_zero.mpr (Ne.symm hne))
  have hDax : ∀ v ∈ D, (u1 - u0) ⬝ᵥ v = 0 := fun v hv => LinearMap.mem_ker.mp hv
  have hDmid0 : ∀ v ∈ D, inner ℝ (p - u0) v = 0 := by
    intro v hv
    rw [hmid0, p24_hsmL, inner_eq_dot, hDax v hv]
    ring
  have hDmid1 : ∀ v ∈ D, inner ℝ (p - u1) v = 0 := by
    intro v hv
    rw [hmid1, inner_neg_left, p24_hsmL, inner_eq_dot, hDax v hv]
    ring
  -- the margin scale `s` and patch radius `R`
  set d2 : ℝ := d / 2 with hd2def
  have hd2pos : (0:ℝ) ≤ d2 := by positivity
  have hsqd : d ^ 2 < 8 := by
    have h4 : (0:ℝ) ≤ 2 * Real.sqrt 2 := by positivity
    have hsq1 : d ^ 2 < (2 * Real.sqrt 2) ^ 2 := by
      nlinarith [hdlt, hdpos, h4]
    have h82 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num)]
      norm_num
    rw [h82] at hsq1
    exact hsq1
  have hd2sq : d2 ^ 2 < 2 := by nlinarith
  set s : ℝ := Real.sqrt (4 - d2 ^ 2) with hsdef
  have hsnn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have h4pos : (0:ℝ) ≤ 4 - d2 ^ 2 := by linarith
  have hsd2 : d2 < s := by
    have h1 : d2 ^ 2 < s ^ 2 := by
      rw [hsdef, Real.sq_sqrt h4pos]
      nlinarith
    by_contra hcon
    have h2 : s ^ 2 ≤ d2 ^ 2 := by nlinarith [hsnn, hd2pos, hcon]
    linarith
  set R : ℝ := (s - d2) / 8 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRkey : d2 + 2 * R ≤ s - 2 * R := by
    have h1 : 4 * R ≤ s - d2 := by rw [hRdef]; field_simp; linarith
    linarith
  -- margin: every other packing point sits outside the radius-`s` ball at `p`
  have hmargin : ∀ w ∈ V, w ≠ u0 → w ≠ u1 → s ≤ ‖w - p‖ := by
    intro w hw hw0 hw1
    have hsep0 : (2:ℝ) ≤ ‖w - u0‖ := by
      have h := hp.dist_ge_two hw hu0 hw0
      rwa [dist_eq_norm] at h
    have hsep1 : (2:ℝ) ≤ ‖w - u1‖ := by
      have h := hp.dist_ge_two hw hu1 hw1
      rwa [dist_eq_norm] at h
    have hsplit0 : ‖w - u0‖ ^ 2 = ‖w - p‖ ^ 2 + 2 * inner ℝ (w - p) (p - u0)
        + ‖p - u0‖ ^ 2 := by
      rw [show (w - u0 : V3) = (w - p) + (p - u0) from by abel, norm_add_sq_real]
    have hsplit1 : ‖w - u1‖ ^ 2 = ‖w - p‖ ^ 2 + 2 * inner ℝ (w - p) (p - u1)
        + ‖p - u1‖ ^ 2 := by
      rw [show (w - u1 : V3) = (w - p) + (p - u1) from by abel, norm_add_sq_real]
    have hcross : inner ℝ (w - p) (p - u0) + inner ℝ (w - p) (p - u1) = 0 := by
      have hsum : (p - u0) + (p - u1) = 0 := by rw [hmid0, hmid1]; abel
      have hadd : inner ℝ (w - p) ((p - u0) + (p - u1))
          = inner ℝ (w - p) (p - u0) + inner ℝ (w - p) (p - u1) :=
        inner_add_right _ _ _
      rw [hsum] at hadd
      have hz : inner ℝ (w - p) (0:V3) = 0 := inner_zero_right _
      rw [hz] at hadd
      linarith
    rw [hpu0] at hsplit0
    rw [hpu1] at hsplit1
    have h4u0 : (4:ℝ) ≤ ‖w - u0‖ ^ 2 := by
      nlinarith [sq_nonneg (‖w - u0‖ - 2)]
    have h4u1 : (4:ℝ) ≤ ‖w - u1‖ ^ 2 := by
      nlinarith [sq_nonneg (‖w - u1‖ - 2)]
    have hpara : ‖w - u0‖ ^ 2 + ‖w - u1‖ ^ 2 = 2 * ‖w - p‖ ^ 2 + 2 * d2 ^ 2 := by
      rw [hsplit0, hsplit1]
      nlinarith
    have hsq : s ^ 2 ≤ ‖w - p‖ ^ 2 := by
      rw [hsdef, Real.sq_sqrt h4pos]
      nlinarith
    have h1 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsnn, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)] at h1
    exact h1
  -- the pair-cell set form
  have hpair : S = voronoiClosed V u1 ∩ voronoiClosed V u0 := by
    rw [hSdef]
    show voronoiSet V (setOfList [u0, u1]) = _
    rw [show (setOfList [u0, u1] : Set V3) = {u0, u1} from by
      ext x; simp [setOfList], VORONOI_SET_2]
  -- distances from patch points to the pair endpoints
  have hdu1 : ∀ v ∈ D, ‖(p + v) - u1‖ ≤ d2 + ‖v‖ := by
    intro v hv
    rw [show ((p + v) - u1 : V3) = (p - u1) + v from by abel]
    exact le_trans (norm_add_le _ _) (by rw [hpu1])
  have hdu0 : ∀ v ∈ D, ‖(p + v) - u0‖ ≤ d2 + ‖v‖ := by
    intro v hv
    rw [show ((p + v) - u0 : V3) = (p - u0) + v from by abel]
    exact le_trans (norm_add_le _ _) (by rw [hpu0])
  have hdeq : ∀ v ∈ D, ‖(p + v) - u0‖ = ‖(p + v) - u1‖ := by
    intro v hv
    have hq0 : ‖(p + v) - u0‖ ^ 2 = d2 ^ 2 + ‖v‖ ^ 2 := by
      rw [show ((p + v) - u0 : V3) = (p - u0) + v from by abel,
        p24_pythI (hDmid0 v hv), hpu0]
    have hq1 : ‖(p + v) - u1‖ ^ 2 = d2 ^ 2 + ‖v‖ ^ 2 := by
      rw [show ((p + v) - u1 : V3) = (p - u1) + v from by abel,
        p24_pythI (hDmid1 v hv), hpu1]
    have hsqeq : ‖(p + v) - u0‖ ^ 2 = ‖(p + v) - u1‖ ^ 2 := by rw [hq0, hq1]
    have h1 : Real.sqrt (‖(p + v) - u0‖ ^ 2) = Real.sqrt (‖(p + v) - u1‖ ^ 2) := by
      rw [hsqeq]
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (norm_nonneg _)] at h1
  -- membership of the patch in the pair cell
  have hmem : ∀ v ∈ D, ‖v‖ ≤ 2 * R → p + v ∈ S := by
    intro v hv hvR
    rw [hpair]
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · -- the cell of `u1`
      show dist (p + v) u1 ≤ dist (p + v) w
      rcases eq_or_ne w u1 with rfl | hw1
      · exact le_refl _
      rcases eq_or_ne w u0 with rfl | hw0
      · have he := hdeq v hv
        rw [← dist_eq_norm, ← dist_eq_norm] at he
        rw [he]
      · have h1 := hdu1 v hv
        have h3 := dist_triangle w (p + v) p
        have h4 : dist (p + v) p = ‖v‖ := by
          rw [dist_eq_norm]; congr 1; abel
        have h5 : dist w p = ‖w - p‖ := dist_eq_norm w p
        rw [h4, h5] at h3
        have h6 := hmargin w hw hw0 hw1
        have h7 : dist w (p + v) = ‖(p + v) - w‖ := by
          rw [dist_comm, dist_eq_norm]
        rw [h7] at h3
        rw [dist_eq_norm, dist_eq_norm]
        linarith
    · -- the cell of `u0`
      show dist (p + v) u0 ≤ dist (p + v) w
      rcases eq_or_ne w u1 with rfl | hw1
      · have he := hdeq v hv
        rw [← dist_eq_norm, ← dist_eq_norm] at he
        rw [he]
      rcases eq_or_ne w u0 with rfl | hw0
      · exact le_refl _
      · have h1 := hdu0 v hv
        have h3 := dist_triangle w (p + v) p
        have h4 : dist (p + v) p = ‖v‖ := by
          rw [dist_eq_norm]; congr 1; abel
        have h5 : dist w p = ‖w - p‖ := dist_eq_norm w p
        rw [h4, h5] at h3
        have h6 := hmargin w hw hw0 hw1
        have h7 : dist w (p + v) = ‖(p + v) - w‖ := by
          rw [dist_comm, dist_eq_norm]
        rw [h7] at h3
        rw [dist_eq_norm, dist_eq_norm]
        linarith
  -- pick two independent directions, scaled into the patch
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h] at hD2
    simp at hD2
  obtain ⟨v1, hv1D, hv1ne⟩ : ∃ v ∈ D, v ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ v ∈ D, v = 0 := fun v hv => by
      by_contra hh
      exact hcon ⟨v, hv, hh⟩
    refine hDne (Submodule.ext fun x => ?_)
    constructor
    · intro hx
      have hx0 : x = 0 := hcon' x hx
      rw [hx0]
      exact (Submodule.mem_bot (R := ℝ)).2 rfl
    · intro hx
      rw [Submodule.mem_bot] at hx
      exact hx.symm ▸ Submodule.zero_mem D
  have hv1pos : 0 < ‖v1‖ := norm_pos_iff.mpr hv1ne
  have hD1 : (Submodule.span ℝ {v1}) ≤ D := Submodule.span_le.2
    (Set.singleton_subset_iff.2 hv1D)
  have hfr1 : Module.finrank ℝ (Submodule.span ℝ {v1}) = 1 := finrank_span_singleton hv1ne
  have hDne1 : D ≠ (Submodule.span ℝ {v1}) := by
    intro h
    rw [h, hfr1] at hD2
    simp at hD2
  obtain ⟨v2, hv2D, hv2s⟩ : ∃ v2 ∈ D, v2 ∉ (Submodule.span ℝ {v1}) := by
    by_contra hcon
    have hcon' : ∀ v ∈ D, v ∈ (Submodule.span ℝ {v1}) := fun v hv => by
      by_contra hh
      exact hcon ⟨v, hv, hh⟩
    refine hDne1 (Submodule.ext fun x => ?_)
    exact ⟨fun hx => hcon' x hx, fun hx => hD1 hx⟩
  have hv2ne : v2 ≠ 0 := by
    intro h
    apply hv2s
    rw [h]
    exact Submodule.mem_span_singleton.2 ⟨0, by simp⟩
  have hv2pos : 0 < ‖v2‖ := norm_pos_iff.mpr hv2ne
  set c1 : ℝ := R / ‖v1‖ with hc1def
  set c2 : ℝ := R / ‖v2‖ with hc2def
  have hc1pos : 0 < c1 := by rw [hc1def]; positivity
  have hc2pos : 0 < c2 := by rw [hc2def]; positivity
  set w1 : V3 := c1 • v1 with hw1def
  set w2 : V3 := c2 • v2 with hw2def
  have hw1D : w1 ∈ D := Submodule.smul_mem _ _ hv1D
  have hw2D : w2 ∈ D := Submodule.smul_mem _ _ hv2D
  have hw1n : ‖w1‖ = R := by
    rw [hw1def, norm_smul, Real.norm_eq_abs, abs_of_pos hc1pos, hc1def]
    field_simp
  have hw2n : ‖w2‖ = R := by
    rw [hw2def, norm_smul, Real.norm_eq_abs, abs_of_pos hc2pos, hc2def]
    field_simp
  have hw1ne : w1 ≠ 0 := by
    intro h
    rw [hw1def] at h
    exact hv1ne (smul_right_injective V3 (ne_of_gt hc1pos)
      (show (c1:ℝ) • v1 = c1 • 0 from by rw [h]; simp))
  have hw2ne : w2 ≠ 0 := by
    intro h
    rw [hw2def] at h
    exact hv2ne (smul_right_injective V3 (ne_of_gt hc2pos)
      (show (c2:ℝ) • v2 = c2 • 0 from by rw [h]; simp))
  have hspanw1 : Submodule.span ℝ {w1} = Submodule.span ℝ {v1} := by
    rw [hw1def, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (ne_of_gt hc1pos))]
  have hw2n1 : w2 ∉ Submodule.span ℝ {w1} := by
    rw [hspanw1, hw2def]
    intro hcon
    rcases Submodule.mem_span_singleton.mp hcon with ⟨t, ht⟩
    refine hv2s (Submodule.mem_span_singleton.2 ⟨t / c2, ?_⟩)
    refine (smul_right_injective V3 (ne_of_gt hc2pos)) ?_
    show c2 • ((t / c2) • v1) = c2 • v2
    rw [smul_smul]
    have hrat : c2 * (t / c2) = t := by field_simp
    rw [hrat, ht]
  -- the three patch points
  set z1 : V3 := p + w1 with hz1def
  set z2 : V3 := p + w2 with hz2def
  set z3 : V3 := p + (w1 + w2) with hz3def
  have hz1S : z1 ∈ S := hmem w1 hw1D (by rw [hw1n]; linarith)
  have hz2S : z2 ∈ S := hmem w2 hw2D (by rw [hw2n]; linarith)
  have hz3S : z3 ∈ S := hmem (w1 + w2) (Submodule.add_mem _ hw1D hw2D)
    (by have := norm_add_le w1 w2; rw [hw1n, hw2n] at this; linarith)
  -- linear independence of the two scaled directions
  have hli : LinearIndependent ℝ ![w1, w2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    fin_cases i
    · by_contra hg0
      rcases eq_or_ne (g 1) 0 with hg1 | hg1
      · rw [hg1, zero_smul, add_zero] at hg
        exact hg0 ((smul_eq_zero.mp hg).resolve_right hw1ne)
      · apply hw2n1
        refine Submodule.mem_span_singleton.2 ⟨-g 0 / g 1, ?_⟩
        have hkey : g 1 • ((-g 0 / g 1) • w1) = g 1 • w2 := by
          rw [smul_smul]
          have hrat : g 1 * (-g 0 / g 1) = -g 0 := by field_simp
          rw [hrat, neg_smul, neg_eq_iff_add_eq_zero]
          exact hg
        exact smul_right_injective V3 hg1 hkey
    · by_contra hg1
      rcases eq_or_ne (g 0) 0 with hg0 | hg0
      · rw [hg0, zero_smul, zero_add] at hg
        exact hg1 ((smul_eq_zero.mp hg).resolve_right hw2ne)
      · apply hw2n1
        have hkey : g 0 • ((-g 1 / g 0) • w2) = g 0 • w1 := by
          rw [smul_smul]
          have hrat : g 0 * (-g 1 / g 0) = -g 1 := by field_simp
          rw [hrat, neg_smul, neg_eq_iff_add_eq_zero, add_comm]
          exact hg
        have hwt : w1 = (-g 1 / g 0) • w2 :=
          smul_right_injective V3 hg0 (by
            show g 0 • w1 = g 0 • ((-g 1 / g 0) • w2)
            rw [hkey])
        refine Submodule.mem_span_singleton.2 ⟨1 / (-g 1 / g 0), ?_⟩
        rw [hwt, smul_smul]
        have hng : (-g 1 / g 0) ≠ 0 :=
          div_ne_zero (neg_ne_zero.2 hg1) hg0
        have hrat : (1 / (-g 1 / g 0)) * (-g 1 / g 0) = 1 := by
          field_simp
          exact div_self hg1
        rw [hrat, one_smul]
  -- the span of the two directions sits inside the vectorSpan of the cell
  have hsuble : (Submodule.span ℝ {w1, w2}) ≤ vectorSpan ℝ S := by
    rw [vectorSpan_def, Submodule.span_le]
    intro t ht
    have hw1in : w1 ∈ (vectorSpan ℝ S : Set V3) :=
      Submodule.subset_span (Set.mem_vsub.2 ⟨z3, hz3S, z2, hz2S, by
        show z3 -ᵥ z2 = w1
        rw [vsub_eq_sub, hz3def, hz2def]
        abel⟩)
    have hw1w2 : w1 - w2 ∈ (vectorSpan ℝ S : Set V3) :=
      Submodule.subset_span (Set.mem_vsub.2 ⟨z1, hz1S, z2, hz2S, by
        show z1 -ᵥ z2 = w1 - w2
        rw [vsub_eq_sub, hz1def, hz2def]
        abel⟩)
    have hw2in : w2 ∈ (vectorSpan ℝ S : Set V3) := by
      have hsub := Submodule.sub_mem (vectorSpan ℝ S) hw1in hw1w2
      rwa [show (w1 - (w1 - w2) : V3) = w2 from by abel] at hsub
    rcases Set.mem_insert_iff.mp ht with rfl | rfl
    · exact hw1in
    · exact hw2in
  have hfrS : (2:ℕ) ≤ Module.finrank ℝ (vectorSpan ℝ S) := by
    have h1 := Submodule.finrank_mono hsuble
    have hrange : Set.range ![w1, w2] = {w1, w2} := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
    have h2 : Module.finrank ℝ (Submodule.span ℝ {w1, w2}) = 2 := by
      rw [show (Submodule.span ℝ {w1, w2}) = Submodule.span ℝ
        (Set.range ![w1, w2]) from by rw [hrange], finrank_span_eq_card hli]
      norm_num
    rw [h2] at h1
    exact h1
  -- conclusion
  have hneS : S.Nonempty := ⟨z1, hz1S⟩
  have hSsub : S ⊆ bis u0 u1 := by
    intro x hx
    rw [hpair] at hx
    rw [bis, Set.mem_setOf_eq]
    exact le_antisymm (hx.2 u1 hu1) (hx.1 u0 hu0)
  have hd_le : affDim S ≤ 2 := by
    refine le_trans (affDim_mono hSsub hneS) ?_
    exact le_of_eq (p24_affDim_bis_pair hne)
  have hd_ge : (2:ℤ) ≤ affDim S := by
    rw [affDim, if_neg (Set.nonempty_iff_ne_empty.mp hneS)]
    norm_cast
  exact le_antisymm hd_le hd_ge

/-- Segment (a): `hl [u0,u1] < sqrt 2 → barV V 1 [u0,u1]`
(marchal3.hl:1054 `HL_LE_SQRT2_IMP_BARV_1`; PA15:578 twin is a
`ported sorry`, this is the first genuine copy). -/
private theorem p24_barV1 (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) : barV V 1 [u0, u1] := by
  refine ⟨by norm_num, ?_⟩
  rintro vl ⟨⟨yl, hyl⟩, hpos⟩
  cases vl with
  | nil => exact absurd hpos (by simp)
  | cons a tl =>
    have hcon : u0 = a ∧ [u1] = tl ++ yl := List.cons.inj hyl
    have ha : a = u0 := hcon.1.symm
    cases tl with
    | nil =>
      have hy1 : yl = [u1] := by
        simpa using hcon.2.symm
      rw [ha]
      refine ⟨by norm_num, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hu0
        · exact absurd hx' (by simp)
      · have hsing : voronoiList V [u0] = voronoiClosed V u0 := by
          show voronoiSet V (setOfList [u0]) = _
          rw [show (setOfList [u0] : Set V3) = {u0} from by
            ext x; simp [setOfList], VORONOI_SET_SING]
        rw [hsing, AFF_DIM_VORONOI_CLOSED V u0 hp]
        norm_num
    | cons b tl2 =>
      have hcon2 : u1 = b ∧ [] = tl2 ++ yl := List.cons.inj hcon.2
      have hb : b = u1 := hcon2.1.symm
      have htl2 : tl2 = [] := by
        cases tl2 with
        | nil => rfl
        | cons c tl3 => exact absurd hcon2.2 (by simp)
      rw [ha, hb, htl2]
      refine ⟨by norm_num, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hu0
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact hu1
        · exact absurd hx' (by simp)
      · have h2 := p24_affDim_voronoiList2 V u0 u1 hp hu0 hu1 hne hhl
        rw [h2]
        norm_num

/-- Segment (b) (Rogers.hl:826 `GLTVHUM_lemma1` at `j = 1`, `k = 3`): the
pair Voronoi list is the union of convex hulls of `{ω₁, ω₂} ∪ voronoi_list`
over the leaf triples extending `[u0,u1]` (public genuine PA6:1108). -/
private theorem p24_gltvhum3 (V : Set V3) (u0 u1 : V3) (hs : saturated V)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) :
    voronoiList V [u0, u1] =
      ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc 1 (3 - 1)} ∪
        voronoiList V vl) | vl ∈ {vl : List V3 |
        barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]}} := by
  have hbar1 : barV V 1 [u0, u1] := p24_barV1 V u0 u1 hp hu0 hu1 hne hhl
  have hdec := GLTVHUM_lemma1 (V := V) (ul := [u0, u1]) (j := 1) hp hs
    (by norm_num) hbar1
  have h3 : 3 ∈ (Finset.Icc 1 3 : Set ℕ) := by simp
  rw [← hdec] at h3
  obtain ⟨-, hvor⟩ := h3
  exact hvor

/-- Segment (c) (marchal2.hl:2231 + pack3.hl:2507): a leaf triple over the
pair has a one-point Voronoi list `{a}`, `a` the circumcenter, and
`omega_list_n V vl 3 = a` (public genuine PA12:1677 + PA5:2296). -/
private theorem p24_leaf_singleton (V : Set V3) (vl : List V3) (hs : saturated V)
    (hp : Packing V) (hbar : barV V 3 vl) :
    ∃ a : V3, voronoiList V vl = {a} ∧ a = circumcenter (setOfList vl) ∧
      omegaListN V vl 3 = a := by
  obtain ⟨a, ha1, ha2, -⟩ := VORONOI_LIST_3_SINGLETON_EXPLICIT V vl hp hs hbar
  refine ⟨a, ha1, ha2, ?_⟩
  have h3 := OMEGA_LIST_IN_VORONOI_LIST (V := V) (ul := vl) (k := 3) hbar
  rw [ha1] at h3
  have hoe : omegaList V vl = omegaListN V vl 3 := by
    show omegaListN V vl (vl.length - 1) = omegaListN V vl 3
    rw [hbar.1]
  rw [hoe] at h3
  exact Set.mem_singleton_iff.mp h3

/-- Composed fan structure (segments (b)+(c)): `voronoiList V [u0,u1]` is
the union over leaf triples `vl` (barV V 3, truncating to `[u0,u1]`) of the
convex hulls of `{ω₁, ω₂, circumcenter vl}` — the per-cell fan around the
edge. -/
private theorem p24_voronoi_pair_split (V : Set V3) (u0 u1 : V3) (hs : saturated V)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) :
    voronoiList V [u0, u1] =
      ⋃₀ {convexHull ℝ {omegaListN V vl 1, omegaListN V vl 2,
        circumcenter (setOfList vl)} | vl ∈ {vl : List V3 |
        barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]}} := by
  have hsplit := p24_gltvhum3 V u0 u1 hs hp hu0 hu1 hne hhl
  rw [hsplit]
  have hleaf : ∀ vl ∈ {vl : List V3 | barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]},
      convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc 1 (3 - 1)} ∪ voronoiList V vl) =
      convexHull ℝ {omegaListN V vl 1, omegaListN V vl 2, circumcenter (setOfList vl)} := by
    rintro vl ⟨hbar3, -⟩
    obtain ⟨a, ha1, ha2, -⟩ := p24_leaf_singleton V vl hs hp hbar3
    have him : {omegaListN V vl i | i ∈ Finset.Icc 1 (3 - 1)} =
        {omegaListN V vl 1, omegaListN V vl 2} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        Finset.mem_Icc]
      constructor
      · rintro ⟨i, hi1, hi2, rfl⟩
        rcases i with _ | _ | _ | m
        · omega
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      · rintro (rfl | rfl)
        · exact ⟨1, by simp, rfl⟩
        · exact ⟨2, by simp, rfl⟩
    have hstep : ({omegaListN V vl 1, omegaListN V vl 2} ∪ ({a} : Set V3)) =
        {omegaListN V vl 1, omegaListN V vl 2, a} := by
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [him, ha1, hstep, ha2]
  refine Set.ext fun T => ?_
  rw [Set.mem_sUnion, Set.mem_sUnion]
  refine ⟨fun ⟨T', hT', hTT'⟩ => ?_, fun ⟨T', hT', hTT'⟩ => ?_⟩
  · obtain ⟨vl, hvl, heq⟩ := hT'
    exact ⟨T', ⟨vl, hvl, (hleaf vl hvl).symm.trans heq⟩, hTT'⟩
  · obtain ⟨vl, hvl, heq⟩ := hT'
    exact ⟨T', ⟨vl, hvl, (hleaf vl hvl).trans heq⟩, hTT'⟩

/-- HOL `REUHADY1` (REUHADY.hl:239, refinement proof over lines
239-8356). GIANT — the dihedral-splitting bulk (d) is the single
remaining `sorry`; the preamble (a)-(c) landed genuinely in the
2026-09-30 REUHADY wave (private chain right above).
REFINEMENT SKELETON vs. this file:
(a) `barV V 1 [u0;u1]` — FILLED genuinely: `p24_barV1`
    (`HL_LE_SQRT2_IMP_BARV_1`; PA15:578 twin is still a `ported sorry`;
    core = `p24_affDim_voronoiList2`, bisector-plane affDim via
    `p24_affDim_bis_pair`/`affDim_hyperplane` + packing-margin patch
    points for the `≥ 2` direction).
(b) the k-decomposition set `{k | ... voronoi_list V [u0;u1] = UNIONS ...}`
    pinned to `1..3` with `3 ∈` it via Rogers `GLTVHUM_lemma1` — public
    GENUINE copy at PackingAuto6:1108 (PA6 imported here; do NOT touch PA2's
    private `p2g_GLTVHUM_lemma1`, another lane owns that file) — wired as
    `p24_gltvhum3`.
(c) per-leaf-cell: `voronoi_list V vl = {circumcenter}` via
    `VORONOI_LIST_3_SINGLETON_EXPLICIT` (PA12:1677, CLOSED 2026-09-30,
    this file now imports PA12) and `omega_list_n V vl 3 = circumcenter`
    via `OMEGA_LIST_IN_VORONOI_LIST` (PA5:2296, CLOSED 2026-09-30) —
    wired as `p24_leaf_singleton`, composed with (b) into the fan
    structure `p24_voronoi_pair_split`.
(d) NEEDS (the residual, HL lines ~400-8356, new work): with the fan
    structure in hand, split `setSum` over the mcells inside the closed
    wedge: (i) mcell4 leaf-cell realization `X = mcell 4 V [u0;u1;u2;u3]`
    over the leaf triples of the fan (cell_params_d/china kit; the HL
    does this via MCELL_EXPLICIT + SET_TAC plumbing); (ii) the
    conic-cap/annulus measure argument around the edge — `vol (t ∩ E)`
    sums over the fan partitioning the azimuth wedge, `dihu4 = azim`
    additivity along the azimuth, and the finite fan sum
    `∑ leaf dihX = azim u0 u1 n1 n2` (HL ~7000-8356: SUM_EQ +
    SUM_SUPERSET + measure sandwich); upstream sorried twins to consume
    first: PA18 `FCHKUGT`/`EWYBJUA` (PA18:2159/:2532, ported sorry),
    PA7 `YIFVQDV_lemma_aff_dim` (PA7:854, ported sorry), PA15
    `HL_LE_SQRT2_IMP_BARV_1` (PA15:578, ported sorry — superseded here).
DOWNSTREAM (2026-09-30): the two capstones `REUHADY_p24` /
`REUHADY_version2_p24` (below) are wired to this theorem with every
hypothesis synthesized genuinely (see the kit before the capstone
section); their remaining content is exactly `REUHADY1` + the
`p24_REUHADY_nondeg` NEEDS shim. Statement (REUHADY_concl1_new) itself
needs only PA2 defs, no voronoi. -/
theorem REUHADY1 : REUHADY_concl1_new := by
  intro V u0 u1 vl1 vl2 n1 n2 e hs hp hu0 hu1 hne hhl he hwedge haz hvlne
    hhl1 hhl2 hbar1 hbar2 htr1 htr2 hn1 hn2 heX
  -- (a) genuine: the pair is barV V 1
  have hbarV1 : barV V 1 [u0, u1] := p24_barV1 V u0 u1 hp hu0 hu1 hne hhl
  -- (b)+(c) genuine: the pair voronoi list splits over the leaf triples
  have hfan := p24_voronoi_pair_split V u0 u1 hs hp hu0 hu1 hne hhl
  -- NEEDS (d): the dihedral-splitting bulk (HL REUHADY.hl ~400-8356, new
  -- work): mcell4 leaf-cell realization over the fan triples + the
  -- conic-cap/azimuth measure sandwich ∑ leaf dihX = azim u0 u1 n1 n2
  -- (see the docstring above for the full (d) map and upstream sorried
  -- twins to consume first). Segments (a)-(c) are genuinely closed above.
  sorry

/-! ## Harrison's `Arg` halfline lemmas (REUHADY.hl:88, :110)

HOL states these over `real^2` (complex identified); encoded over `ℂ`
(PackingAuto22 precedent). HOL `aff_ge {vec 0} {b}` (a closed halfline
from the origin through `b`) is encoded as the closed ray
`{z : ℂ | ∃ t ≥ 0, z = (t : ℂ) * b}`. -/

/-- HOL `ARG_EQ_SUBSET_HALFLINE` (REUHADY.hl:88). -/
theorem argEqSubsetHalfline : ∀ a : ℝ, ∃ b : ℂ, b ≠ 0 ∧
    {z : ℂ | Complex.arg z = a} ⊆ {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ z = (t : ℂ) * b} := by
  intro a
  by_cases hsub : {z : ℂ | Complex.arg z = a} ⊆ {0}
  · refine ⟨1, one_ne_zero, fun z hz => ?_⟩
    have hz0 : z = 0 := hsub hz
    exact ⟨0, le_refl 0, by simp [hz0]⟩
  · obtain ⟨z, hz, hz0⟩ := Set.not_subset.mp hsub
    simp only [Set.mem_setOf_eq] at hz
    simp only [Set.mem_singleton_iff] at hz0
    refine ⟨z, hz0, fun w hw => ?_⟩
    by_cases hwz : w = 0
    · exact ⟨0, le_refl 0, by simp [hwz]⟩
    · have hpz : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
      have hzne : ‖z‖ ≠ 0 := hpz.ne'
      refine ⟨‖w‖ / ‖z‖, div_nonneg (norm_nonneg _) hpz.le, ?_⟩
      have h1 : ‖((‖w‖ / ‖z‖ : ℝ) : ℂ)‖ = ‖w‖ / ‖z‖ := by
        norm_cast
        exact abs_of_nonneg (div_nonneg (norm_nonneg w) (norm_nonneg z))
      have hpw : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hwz
      have hre : Complex.arg ((↑(‖w‖ / ‖z‖) : ℂ) * z) = Complex.arg z :=
        Complex.arg_real_mul (r := ‖w‖ / ‖z‖) z (div_pos hpw hpz)
      refine Complex.ext_norm_arg ?_ ?_
      · rw [norm_mul, h1]
        field_simp
      · rw [hre, hw, hz]

/-- HOL `ARG_DIV_EQ_SUBSET_HALFLINE` (REUHADY.hl:110). -/
theorem argDivEqSubsetHalfline : ∀ w : ℂ, w ≠ 0 → ∀ a : ℝ, ∃ b : ℂ, b ≠ 0 ∧
    {z : ℂ | Complex.arg (z / w) = a} ⊆ {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ z = (t : ℂ) * b} := by
  intro w hw a
  obtain ⟨b₀, hb₀, hsub⟩ := argEqSubsetHalfline a
  refine ⟨b₀ * w, mul_ne_zero hb₀ hw, fun z hz => ?_⟩
  obtain ⟨t, ht0, hzr⟩ := hsub hz
  refine ⟨t, ht0, ?_⟩
  rw [← mul_assoc]
  exact (div_eq_iff hw).mp hzr

/-! ## List kit for the REUHADY1 preamble (glue, proved) -/

/-- `truncate_simplex 1 vl = [EL 0 vl; EL 1 vl]` for `2 ≤ LENGTH vl`
(HL `Marchal_cells.TRUNCATE_SIMPLEX_EXPLICIT_1/2` usage form, as
consumed by the `REUHADY1` preamble and OXLZLEZ3). -/
theorem truncateSimplex1_pair (vl : List V3) (h2 : 2 ≤ vl.length) :
    truncateSimplex 1 vl = [elV vl 0, elV vl 1] := by
  cases vl with
  | nil => exact absurd h2 (by simp)
  | cons x tl =>
    cases tl with
    | nil => exact absurd h2 (by simp)
    | cons y rest =>
      have hsub : initialSublist [x, y] (x :: y :: rest) := ⟨rest, rfl⟩
      have h := (INITIAL_SUBLIST_IMP_TRUNCATE_SIMPLEX hsub (by simp)).1
      exact h.symm

/-- HOL `set_of_list (truncate_simplex 1 vl) = {EL 0 vl, EL 1 vl}`. -/
theorem setOfList_truncateSimplex1 (vl : List V3) (h2 : 2 ≤ vl.length) :
    setOfList (truncateSimplex 1 vl) = {elV vl 0, elV vl 1} := by
  rw [truncateSimplex1_pair vl h2]
  ext x
  simp [setOfList]

/-- Collinearity with a pair puts the point on the pair's line
(forward direction; used by `coplanarAzimEq`'s axis case). -/
theorem collinear3_mem_affineSpan_pair {v0 v1 z : V3} (hne : v0 ≠ v1)
    (hc : Collinear3 v0 v1 z) : z ∈ (affineSpan ℝ {v0, v1} : Set V3) := by
  have hz : z ∈ ({v0, v1, z} : Set V3) := by simp
  have hm := hc.mem_affineSpan_of_mem_of_ne (p₁ := v0) (p₂ := v1) (p₃ := z)
    (by simp) (by simp) hz hne
  simpa using hm

/-! ## COPLANAR_AZIM_EQ and the measure theorems (giants for this lane) -/

/-! ### The azim witness/affine-span kit (2026-09-19 fill, proved) -/

private theorem p24_exists_azim_point (v0 v1 w1 : V3) (a : ℝ)
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


private theorem p24_mem_affineSpan_triple (v0 v1 w z : V3) (c₂ c₃ : ℝ)
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

/-! ### The measure-side helpers for the closed-wedge bridge (2026-09-30 fill,
PA25 `p25_affineSpan_three_ne_top` / `p25_finrank_span_pair_le_two` patterns) -/

private theorem p24_finrank_span_pair_le_two (a b : V3) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  have h2 := finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset V3)
  unfold Set.finrank at h2
  rw [show (({a, b} : Finset V3) : Set V3) = ({a, b} : Set V3) from by simp] at h2
  refine h2.trans ?_
  calc ({a, b} : Finset V3).card ≤ ({b} : Finset V3).card + 1 := Finset.card_insert_le a {b}
    _ = 2 := by simp

private theorem p24_affineSpan_triple_ne_top (x v u : V3) :
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
    exact p24_finrank_span_pair_le_two (v - x) (u - x)
  rw [hdir, finrank_top] at hle
  exact absurd hle (by norm_num)

/-- COPLANAR_IMP_NEGLIGIBLE (HOL `COPLANAR_IMP_NEGLIGIBLE` content, in the
root-`Coplanar` form `Module.rank ℝ (vectorSpan ℝ S) ≤ 2` that PA24's frozen
`Coplanar ℝ _` statements elaborate to): anything inside a coplanar set is
Lebesgue-null. The coplanar set lies in a proper affine subspace, null by
Mathlib `Measure.addHaar_affineSubspace`; outer-measure monotonicity (`measure_mono_null`)
needs no measurability of the inner set. -/
private theorem p24_coplanar_measure_null {T S : Set V3} (hS : Coplanar ℝ S)
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
private theorem p24_coplanar_affineSpan_triple (u v w : V3) :
    Coplanar ℝ ((affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) := by
  have h := _root_.coplanar_triple (k := ℝ) u v w
  show Module.rank ℝ ↥((affineSpan ℝ ({u, v, w} : Set V3)).direction) ≤ 2
  rw [direction_affineSpan]
  exact h

/-- HOL `COPLANAR_AZIM_EQ` (REUHADY.hl:121). FILLED (2026-09-30): the two
main ingredients proved above — `p24_exists_azim_point` (the frame/polar
witness `f` off the axis with `azim v0 v1 w1 f = a`) and
`p24_mem_affineSpan_triple` (affineSpan-triple membership) — splice into the
documented case tree. (1) `a ∉ [0, 2π)` is vacuous via `azim_nonneg` /
`azim_lt_two_pi`; (2) `a = 0` needs `¬Collinear3 v0 v1 w1` (from `h`), then
the zero sheet lies in `affineSpan ℝ {v0,v1,w1}` (`collinear3_iff_smul` on the
axis, `azim_eq_zero_iff_alt` + `affGt_pair_iff` off it); (3) `0 < a < 2π`:
`p24_exists_azim_point` gives the witness `f`, and `azim_eq_azim_iff` +
`affGt_pair_iff` put every `z` of the level set into `affineSpan ℝ {v0,v1,f}`;
(4) coplanarity is read off via `p24_coplanar_affineSpan_triple` +
`_root_.Coplanar.subset`. NOTE the Geom-vs-root `Coplanar` split: this frozen
statement is Mathlib's root `Coplanar` (two explicit arguments, rank-of-
vectorSpan ≤ 2), NOT `Kepler.Geom.Coplanar` (the affineSpan-triple
existential, one argument) — resolution is by arity. -/
theorem coplanarAzimEq (v0 v1 w1 : V3) (a : ℝ)
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
            (p24_coplanar_affineSpan_triple v0 v1 w1)
          by_cases hcz : Collinear3 v0 v1 z
          · obtain ⟨cc, hczv⟩ := (collinear3_iff_smul (Ne.symm hv01)).mp hcz
            exact p24_mem_affineSpan_triple v0 v1 w1 z cc 0 (by
              rw [show z = v0 + (z - v0) from by abel, hczv]; module)
          · obtain ⟨c, hcpos, t, hdec⟩ :=
              (affGt_pair_iff (v0 := v0) (v1 := v1) (x := w1) (y := z) hv01
                (fun he => hnc1 (collinear3_pair_left he))
                (fun he => hnc1 (collinear3_pair_right he))).mp
              ((azim_eq_zero_iff_alt hnc1 hcz).mp hz)
            exact p24_mem_affineSpan_triple v0 v1 w1 z t c (by
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
          · obtain ⟨f, hfnc, hfaz⟩ := p24_exists_azim_point v0 v1 w1 a hv01 hnc1
              hapos (lt_of_not_ge ha2')
            refine _root_.Coplanar.subset (fun z hz => ?_)
              (p24_coplanar_affineSpan_triple v0 v1 f)
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
              exact p24_mem_affineSpan_triple v0 v1 f z t c (by
                rw [show z = v0 + (z - v0) from by abel, hdec]; module)

/-! ## 闭楔 Borel（MEASURABLE_CONIC_CAP_WEDGE_GE 的楔半边） -/

/-- 平移保持三点共线（WedgeVolume.lean:32 / Planarity.lean:2822 私拷）。 -/
private theorem p24_collinear3_zero_sub {x a b : V3} :
    Collinear3 x a b ↔ Collinear3 0 (a - x) (b - x) := by
  by_cases h : a = x
  · rw [h]
    simp only [sub_self]
    constructor <;> intro _ <;> exact collinear3_of_eq rfl
  · have h' : a - x ≠ 0 := sub_ne_zero.mpr h
    rw [collinear3_iff_smul h, collinear3_iff_smul h']
    simp only [sub_zero]

private theorem p24_azimSubSpec {x a b c : V3} {θ : ℝ} :
    AzimSpec x a b c θ ↔ AzimSpec 0 (a - x) (b - x) (c - x) θ := by
  unfold AzimSpec
  simp only [sub_zero, sub_ne_zero]
  have hd : dist a x = dist (a - x) 0 := by rw [dist_eq_norm, dist_eq_norm, sub_zero]
  rw [hd]

/-- azim 平移桥：顶点移到原点（WedgeVolume.lean:50 私拷，此处 `azim_sub_self`
不可见）。 -/
private theorem p24_azim_sub_self (x a b c : V3) :
    azim x a b c = azim 0 (a - x) (b - x) (c - x) := by
  unfold azim
  rw [p24_collinear3_zero_sub (x := x) (a := a) (b := b),
    p24_collinear3_zero_sub (x := x) (a := a) (b := c)]
  have hpred : AzimSpec x a b c = AzimSpec 0 (a - x) (b - x) (c - x) :=
    funext fun _ => propext p24_azimSubSpec
  rw [hpred]

/-- azim 在第三个点（射线母点）落轴时为零（`azim_eq_zero_of_collinearY` 的
Or.inl 孪生：azim 定义 if 条件是两共线性的析取）。 -/
private theorem p24_azim_eq_zero_of_collinearW (v0 v1 w y : V3)
    (h : Collinear3 v0 v1 w) : azim v0 v1 w y = 0 := by
  unfold azim
  exact if_pos (Or.inl h)

/-- 闭楔 `wedgeGe` Borel，无退化前提：轴向标架把闭楔 transport 成连续映射
`y ↦ zOf e1 e2 (y − v0)` 的原像（ℂ 侧目标集 = {0} ∪ {ζ ≠ 0, 0 ≤ ang ≤ θ}，
两支皆 Borel；两个边界方位角层集作为闭区间端点免费搭车，无需
`coplanarAzimEq` + 零测论证）。w1 共线（含 v0 = v1）时 `azim ≡ 0`，闭楔为
全空间。对照 ConicCapVolume 私件 `ccv_measSet_wedge`（开楔版本）。雷区
（§5.3）：`azim_eq_ang_of_frame` 的 `hy` 必须传 0 心系形式
`¬ Collinear3 0 (v1 - v0) (y - v0)`——误传 `y` 系会触发 5M heartbeat
isDefEq 超时。 -/
private theorem p24_measSet_wedgeGe (v0 v1 w1 w2 : V3) :
    MeasurableSet (wedgeGe v0 v1 w1 w2) := by
  by_cases hc1 : Collinear3 v0 v1 w1
  · -- w1 落轴（覆盖 v0 = v1）：azim v0 v1 w1 · ≡ 0，闭楔为全空间
    have huniv : wedgeGe v0 v1 w1 w2 = (Set.univ : Set V3) := by
      ext z
      have h1 : azim v0 v1 w1 z = 0 := p24_azim_eq_zero_of_collinearW v0 v1 w1 z hc1
      have h2 : azim v0 v1 w1 w2 = 0 := p24_azim_eq_zero_of_collinearW v0 v1 w1 w2 hc1
      show (0 ≤ azim v0 v1 w1 z ∧ azim v0 v1 w1 z ≤ azim v0 v1 w1 w2) ↔ True
      rw [h1, h2]
      exact ⟨fun _ => trivial, fun _ => ⟨le_refl _, le_refl _⟩⟩
    rw [huniv]
    exact MeasurableSet.univ
  · rcases eq_or_ne v1 v0 with hv | hv01
    · exact absurd (by rw [hv]; exact collinear3_of_eq rfl : Collinear3 v0 v1 w1) hc1
    · -- 主情形：轴向标架 transport 到 ℂ
      obtain ⟨e1, e2, e3, he, halign⟩ :=
        exists_on3_eq_smul (v1 - v0) (sub_ne_zero.mpr hv01)
      have hax : (v1 - v0 : V3) = dist (v1 - v0) 0 • e3 := by
        rw [dist_eq_norm, sub_zero]; exact halign
      have hax2 : (v1 - v0 : V3) = dist v1 v0 • e3 := by
        rw [dist_eq_norm]; exact halign
      have hcont : Continuous fun y : V3 => zOf e1 e2 (y - v0) := by
        simp only [zOf]
        fun_prop
      have hset : wedgeGe v0 v1 w1 w2
          = (fun y : V3 => zOf e1 e2 (y - v0)) ⁻¹'
              {ζ : ℂ | ζ = 0 ∨ (ζ ≠ 0 ∧ 0 ≤ ang ((zOf e1 e2 (w1 - v0))⁻¹ * ζ) ∧
                ang ((zOf e1 e2 (w1 - v0))⁻¹ * ζ) ≤ azim v0 v1 w1 w2)} := by
        ext y
        simp only [Set.mem_preimage, Set.mem_setOf_eq, wedgeGe, Set.mem_setOf_eq]
        constructor
        · rintro ⟨ha1, ha2⟩
          by_cases hζ : zOf e1 e2 (y - v0) = 0
          · exact Or.inl hζ
          · have hnc : ¬ Collinear3 v0 v1 y :=
              (zOf_ne_zero_iff he hax2 hv01 y).mp hζ
            have ha1' := ha1
            have ha2' := ha2
            rw [p24_azim_sub_self v0 v1 w1 y, azim_eq_ang_of_frame e1 e2 e3 he hax
              (sub_ne_zero.mpr hv01) (p24_collinear3_zero_sub.not.mp hc1)
              (p24_collinear3_zero_sub.not.mp hnc)] at ha1' ha2'
            exact Or.inr ⟨hζ, ha1', ha2'⟩
        · rintro (hζ | ⟨hζne, ha1, ha2⟩)
          · have hcol : Collinear3 v0 v1 y := by
              by_contra hnc
              exact ((zOf_ne_zero_iff he hax2 hv01 y).mpr hnc) hζ
            have h0 : azim v0 v1 w1 y = 0 :=
              azim_eq_zero_of_collinearY v0 v1 w1 y hcol
            refine ⟨?_, ?_⟩
            · rw [h0]
            · rw [h0]
              have hθ := azim_nonneg v0 v1 w1 w2
              linarith
          · have hnc : ¬ Collinear3 v0 v1 y :=
              (zOf_ne_zero_iff he hax2 hv01 y).mp hζne
            rw [p24_azim_sub_self v0 v1 w1 y, azim_eq_ang_of_frame e1 e2 e3 he hax
              (sub_ne_zero.mpr hv01) (p24_collinear3_zero_sub.not.mp hc1)
              (p24_collinear3_zero_sub.not.mp hnc)]
            exact ⟨ha1, ha2⟩
      rw [hset]
      refine hcont.measurable
        (((measurableSet_singleton (0:ℂ)).union ?_))
      exact (((measurableSet_singleton (0:ℂ)).compl).inter
        ((measurableSet_le measurable_const
            (measurable_ang.comp (measurable_const.mul measurable_id))).inter
          (measurableSet_le (measurable_ang.comp (measurable_const.mul measurable_id))
            measurable_const)))

/-- HOL `MEASURABLE_CONIC_CAP_WEDGE_GE` (REUHADY.hl:162). FILLED (2026-09-30):
`conicCapP24` is definitionally CCV's `ccvConicCap` (Borel by
`measurableConicCap`), and the closed wedge is Borel by `p24_measSet_wedgeGe`
(the ℂ-transport of CCV's `ccv_measSet_wedge` template: axial frame +
`azim_eq_ang_of_frame` + `measurable_ang`; the two boundary azimuth level
sets ride along as the closed interval endpoints of the ℂ fan, so the
docstring's original route — `wedgeGeWedge` union with `coplanarAzimEq` +
nullness — is not needed here). HL uses `MEASURABLE_CONIC_CAP_WEDGE` +
`COPLANAR_IMP_NEGLIGIBLE` + `COPLANAR_AZIM_EQ`. -/
theorem measurableConicCapWedgeGe (v0 v1 w1 w2 : V3) (r a : ℝ) :
    MeasurableSet (conicCapP24 v0 v1 r a ∩ wedgeGe v0 v1 w1 w2) :=
  (measurableConicCap v0 v1 r a).inter (p24_measSet_wedgeGe v0 v1 w1 w2)

/-- HOL `VOLUME_CONIC_CAP_WEDGE_GE_VS_CONIC_CAP` (REUHADY.hl:178). FILLED
(2026-09-30) once CCV delivered `volumeConicCap` / `volumeConicCapWedge`
(ConicCapVolume 3→0): the closed wedge is the open wedge plus the two
azimuth level sets (`wedgeGeWedge`), both coplanar by `coplanarAzimEq` and
hence null (`p24_coplanar_measure_null`, the `MEASURE_NEGLIGIBLE_SYMDIFF`
content — carried out as an outer-measure sandwich rather than a literal
symmetric-difference identity), so `volume.real (cap ∩ wedgeGe)` equals
`volume.real (cap ∩ wedge)`, which CCV's `volumeConicCapWedge` evaluates to
`volume.real (cap) * azim / (2 * π)` (`conicCapP24` is definitionally CCV's
`ccvConicCap`). The collinear/degenerate wedge-empty branches are inside CCV's
`ccv_wedge_empty_of_collinearW1` handling. -/
private theorem p24_cap_eq_ccv (v0 v1 : V3) (r a : ℝ) :
    conicCapP24 v0 v1 r a = ccvConicCap v0 v1 r a := rfl

theorem volumeConicCapWedgeGeVsConicCap (v0 v1 w1 w2 : V3) (r a : ℝ)
    (ha1 : 0 < a) (ha2 : a < 1) (hr : 0 < r ∧ r ≤ 1)
    (h1 : ¬Collinear3 v0 v1 w1) (h2 : ¬Collinear3 v0 v1 w2) :
    volume.real (conicCapP24 v0 v1 r a ∩ wedgeGe v0 v1 w1 w2) =
      volume.real (conicCapP24 v0 v1 r a) * (azim v0 v1 w1 w2) / (2 * Real.pi) := by
  have hwg : wedgeGe v0 v1 w1 w2 = wedge v0 v1 w1 w2 ∪
      ({z : V3 | azim v0 v1 w1 z = 0} ∪
        {z : V3 | azim v0 v1 w1 z = azim v0 v1 w1 w2}) := wedgeGeWedge v0 v1 w1 w2
  -- the two boundary azimuth level sets are coplanar, hence null
  have hcopA : Coplanar ℝ {z : V3 | azim v0 v1 w1 z = 0} :=
    coplanarAzimEq v0 v1 w1 0 (fun hc => (h1 hc).elim)
  have hcopB : Coplanar ℝ {z : V3 | azim v0 v1 w1 z = azim v0 v1 w1 w2} :=
    coplanarAzimEq v0 v1 w1 (azim v0 v1 w1 w2) (fun hc => (h1 hc).elim)
  have hnullA : volume (conicCapP24 v0 v1 r a ∩ {z : V3 | azim v0 v1 w1 z = 0}) = 0 :=
    p24_coplanar_measure_null hcopA Set.inter_subset_right
  have hnullB : volume (conicCapP24 v0 v1 r a ∩
      {z : V3 | azim v0 v1 w1 z = azim v0 v1 w1 w2}) = 0 :=
    p24_coplanar_measure_null hcopB Set.inter_subset_right
  -- set decomposition of the closed-wedge intersection
  have hdecomp : conicCapP24 v0 v1 r a ∩ wedgeGe v0 v1 w1 w2 =
      (conicCapP24 v0 v1 r a ∩ wedge v0 v1 w1 w2) ∪
      (conicCapP24 v0 v1 r a ∩ {z : V3 | azim v0 v1 w1 z = 0} ∪
        conicCapP24 v0 v1 r a ∩ {z : V3 | azim v0 v1 w1 z = azim v0 v1 w1 w2}) := by
    rw [hwg, Set.inter_union_distrib_left, Set.inter_union_distrib_left]
  -- measure sandwich at the ENNReal level
  have hge : volume (conicCapP24 v0 v1 r a ∩ wedge v0 v1 w1 w2) ≤
      volume (conicCapP24 v0 v1 r a ∩ wedgeGe v0 v1 w1 w2) := by
    refine measure_mono (fun x hx => ?_)
    obtain ⟨hx1, hx2⟩ := hx
    exact ⟨hx1, by rw [hwg]; exact Set.mem_union_left _ hx2⟩
  have hle : volume (conicCapP24 v0 v1 r a ∩ wedgeGe v0 v1 w1 w2) ≤
      volume (conicCapP24 v0 v1 r a ∩ wedge v0 v1 w1 w2) := by
    rw [hdecomp]
    calc volume (conicCapP24 v0 v1 r a ∩ wedge v0 v1 w1 w2 ∪
          (conicCapP24 v0 v1 r a ∩ {z : V3 | azim v0 v1 w1 z = 0} ∪
            conicCapP24 v0 v1 r a ∩ {z : V3 | azim v0 v1 w1 z = azim v0 v1 w1 w2}))
        ≤ volume (conicCapP24 v0 v1 r a ∩ wedge v0 v1 w1 w2) +
          volume (conicCapP24 v0 v1 r a ∩ {z : V3 | azim v0 v1 w1 z = 0} ∪
            conicCapP24 v0 v1 r a ∩ {z : V3 | azim v0 v1 w1 z = azim v0 v1 w1 w2}) :=
          measure_union_le _ _
      _ ≤ volume (conicCapP24 v0 v1 r a ∩ wedge v0 v1 w1 w2) +
          (volume (conicCapP24 v0 v1 r a ∩ {z : V3 | azim v0 v1 w1 z = 0}) +
            volume (conicCapP24 v0 v1 r a ∩
              {z : V3 | azim v0 v1 w1 z = azim v0 v1 w1 w2})) :=
          add_le_add le_rfl (measure_union_le _ _)
      _ = volume (conicCapP24 v0 v1 r a ∩ wedge v0 v1 w1 w2) := by
          rw [hnullA, hnullB, add_zero, add_zero]
  have hvol : volume (conicCapP24 v0 v1 r a ∩ wedgeGe v0 v1 w1 w2) =
      volume (conicCapP24 v0 v1 r a ∩ wedge v0 v1 w1 w2) := le_antisymm hle hge
  -- real-valued conclusion via the CCV open-wedge formula
  have key : volume.real (conicCapP24 v0 v1 r a ∩ wedgeGe v0 v1 w1 w2) =
      volume.real (conicCapP24 v0 v1 r a ∩ wedge v0 v1 w1 w2) := by
    rw [Measure.real_def, Measure.real_def, hvol]
  rw [key, p24_cap_eq_ccv]
  exact volumeConicCapWedge v0 v1 w1 w2 r a ha1 h1 h2

/-! ## 闭楔不交与假设合成 kit（2026-09-30 fill，capstone 消费的私件群） -/

/-- `aff_gt ⊆ aff_ge`（同底同向：`0 <` 见证即 `0 ≤` 见证）。 -/
private theorem p24_affGt_subset_affGe (s t : Set V3) : affGt s t ⊆ affGe s t := by
  intro z hz
  rcases hz with ⟨f, hf, hv, hpos, hsum⟩
  exact ⟨f, hf, hv, fun w hw => le_of_lt (hpos w hw), hsum⟩

/-- 射线换向：`x` 落在过 `y` 的射线锥内蕴含 `y` 落在过 `x` 的射线锥内
（`affGt_pair_iff` 显式系数换算：`y - v0 = c⁻¹ • (x - v0) + (-h/c) • (v1 - v0)`）。 -/
private theorem p24_affGt_swap {v0 v1 x y : V3} (hv0v1 : v0 ≠ v1)
    (hx0 : x ≠ v0) (hx1 : x ≠ v1) (hy0 : y ≠ v0) (hy1 : y ≠ v1)
    (hmem : x ∈ affGt ({v0, v1} : Set V3) ({y} : Set V3)) :
    y ∈ affGt ({v0, v1} : Set V3) ({x} : Set V3) := by
  obtain ⟨c, hc, h, hrep⟩ :=
    (affGt_pair_iff (v0 := v0) (v1 := v1) (x := y) (y := x) hv0v1 hy0 hy1).mp hmem
  have hc0 : c ≠ 0 := ne_of_gt hc
  refine (affGt_pair_iff (v0 := v0) (v1 := v1) (x := x) (y := y) hv0v1 hx0 hx1).mpr
    ⟨c⁻¹, inv_pos.mpr hc, -h / c, ?_⟩
  rw [hrep, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hc0, neg_div]
  module

/-- 轴上点落在射线的闭锥内（`w` 系数取 0 的显式 Affsign 见证）。 -/
private theorem p24_collinear3_mem_affGe {v0 v1 w x : V3} (hwv : v0 ≠ v1)
    (hw : ¬ Collinear3 v0 v1 w) (hcol : Collinear3 v0 v1 x) :
    x ∈ affGe ({v0, v1} : Set V3) ({w} : Set V3) := by
  have hw1 : v1 ≠ v0 := Ne.symm hwv
  have hw0 : w ≠ v0 := fun he => hw (collinear3_pair_left he)
  have hw1' : w ≠ v1 := fun he => hw (collinear3_pair_right he)
  have hvw : v1 ≠ w := fun he => hw1' he.symm
  have hv0w : v0 ≠ w := fun he => hw0 he.symm
  obtain ⟨t, htx⟩ := (collinear3_iff_smul hw1).mp hcol
  have hrep : x = (1 - t) • v0 + t • v1 + (0 : ℝ) • w := by
    linear_combination (norm := module) htx
  have hfin : (({v0} : Set V3) ∪ {v1, w} : Set V3).Finite :=
    (Set.finite_singleton v0).union ((Set.finite_singleton w).insert v1)
  have hseteq : (({v0, v1} ∪ {w} : Set V3) : Set V3) = (({v0} : Set V3) ∪ {v1, w}) := by
    ext y
    simp
    tauto
  rw [affGe, Set.mem_setOf_eq, Affsign, hseteq]
  refine ⟨fun y => if y = w then 0 else if y = v1 then t else 1 - t, hfin, ?_, ?_, ?_⟩
  · rw [sum_insert_pair_v (f := fun y => if y = w then 0 else if y = v1 then t else 1 - t)
      hfin hwv hv0w hvw,
      if_neg hv0w, if_neg hwv, if_neg hvw, if_pos (rfl : v1 = v1),
      if_pos (rfl : w = w)]
    exact hrep
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    simp
  · rw [sum_insert_pair_s (f := fun y => if y = w then 0 else if y = v1 then t else 1 - t)
      hfin hwv hv0w hvw,
      if_neg hv0w, if_neg hwv, if_neg hvw, if_pos (rfl : v1 = v1),
      if_pos (rfl : w = w)]
    ring

/-- azim 零层集 ⊆ 闭半平面：`azim v0 v1 w x = 0 → x ∈ aff_ge {v0,v1} {w}`
（PA18:310 `pa18_azim_zero_affGe` 的公开孪生，此处私拷）。 -/
private theorem p24_azim_zero_affGe {v0 v1 w x : V3} (hw : ¬ Collinear3 v0 v1 w)
    (h0 : azim v0 v1 w x = 0) : x ∈ affGe ({v0, v1} : Set V3) ({w} : Set V3) := by
  by_cases hcolx : Collinear3 v0 v1 x
  · have hwv : v0 ≠ v1 := fun he => hw (collinear3_of_eq he.symm)
    exact p24_collinear3_mem_affGe hwv hw hcolx
  · have hwv : v0 ≠ v1 := fun he => hw (collinear3_of_eq he.symm)
    have hx0 : x ≠ v0 := fun he => hcolx (collinear3_pair_left he)
    have hx1 : x ≠ v1 := fun he => hcolx (collinear3_pair_right he)
    have hw0 : w ≠ v0 := fun he => hw (collinear3_pair_left he)
    have hw1' : w ≠ v1 := fun he => hw (collinear3_pair_right he)
    have hgt : w ∈ affGt ({v0, v1} : Set V3) ({x} : Set V3) :=
      (azim_eq_zero_iff hw hcolx).mp h0
    exact p24_affGt_subset_affGe _ _ (p24_affGt_swap hwv hw0 hw1' hx0 hx1 hgt)

/-- azim 的复指数加法性（相位差乘法）：三点均离轴时
`exp(i·azim a c) = exp(i·azim a b) * exp(i·azim b c)`。轴向标架 +
`azim_eq_ang_of_frame` + `ang_mul_exp` 极形 + ℂ 域代数。 -/
private theorem p24_exp_azim_mul {v0 v1 a b c : V3}
    (ha : ¬ Collinear3 v0 v1 a) (hb : ¬ Collinear3 v0 v1 b) (hc : ¬ Collinear3 v0 v1 c) :
    Complex.exp ((azim v0 v1 a c : ℝ) * Complex.I)
      = Complex.exp ((azim v0 v1 a b : ℝ) * Complex.I)
        * Complex.exp ((azim v0 v1 b c : ℝ) * Complex.I) := by
  have hwv : v1 ≠ v0 := fun he => ha (collinear3_of_eq he)
  obtain ⟨e1, e2, e3, hon, halign⟩ := exists_on3_eq_smul (v1 - v0) (sub_ne_zero.mpr hwv)
  have hax2 : (v1 - v0 : V3) = dist v1 v0 • e3 := by rw [dist_eq_norm]; exact halign
  have hax : (v1 - v0 : V3) = dist (v1 - v0) 0 • e3 := by
    rw [dist_eq_norm, sub_zero]; exact halign
  have hzOfne : ∀ y : V3, ¬ Collinear3 v0 v1 y → zOf e1 e2 (y - v0) ≠ 0 :=
    fun y hy => (zOf_ne_zero_iff hon hax2 hwv y).mpr hy
  have key : ∀ x y : V3, ¬ Collinear3 v0 v1 x → ¬ Collinear3 v0 v1 y →
      azim v0 v1 x y = ang ((zOf e1 e2 (x - v0))⁻¹ * zOf e1 e2 (y - v0)) := by
    intro x y hx hy
    rw [p24_azim_sub_self v0 v1 x y]
    exact azim_eq_ang_of_frame e1 e2 e3 hon hax (sub_ne_zero.mpr hwv)
      (p24_collinear3_zero_sub.not.mp hx) (p24_collinear3_zero_sub.not.mp hy)
  have polar : ∀ t : ℂ, t ≠ 0 →
      Complex.exp (ang t * Complex.I) = t * ((‖t‖ : ℝ) : ℂ)⁻¹ := by
    intro t ht
    have h2 : ((‖t‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ht
    have h1 := ang_mul_exp t
    have h3 := congrArg (fun x : ℂ => ((‖t‖ : ℝ) : ℂ)⁻¹ * x) h1
    rw [inv_mul_cancel_left₀ h2] at h3
    exact ((mul_comm t ((‖t‖ : ℝ) : ℂ)⁻¹).trans h3).symm
  have ha0 : zOf e1 e2 (a - v0) ≠ 0 := hzOfne a ha
  have hb0 : zOf e1 e2 (b - v0) ≠ 0 := hzOfne b hb
  have hc0 : zOf e1 e2 (c - v0) ≠ 0 := hzOfne c hc
  have hzab : (zOf e1 e2 (a - v0))⁻¹ * zOf e1 e2 (b - v0) ≠ 0 :=
    mul_ne_zero (inv_ne_zero ha0) hb0
  have hzbc : (zOf e1 e2 (b - v0))⁻¹ * zOf e1 e2 (c - v0) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hb0) hc0
  have hzac : (zOf e1 e2 (a - v0))⁻¹ * zOf e1 e2 (c - v0) ≠ 0 :=
    mul_ne_zero (inv_ne_zero ha0) hc0
  have hnorm : ∀ t s : ℂ, t ≠ 0 → ‖t⁻¹ * s‖ = ‖s‖ / ‖t‖ := by
    intro t s ht
    rw [norm_mul, norm_inv, div_eq_inv_mul]
  rw [key a c ha hc, key a b ha hb, key b c hb hc, polar _ hzac, polar _ hzab,
    polar _ hzbc, hnorm _ _ ha0, hnorm _ _ ha0, hnorm _ _ hb0]
  have hna : ((‖zOf e1 e2 (a - v0)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr ha0
  have hnb : ((‖zOf e1 e2 (b - v0)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hb0
  have hnc : ((‖zOf e1 e2 (c - v0)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hc0
  field_simp
  push_cast
  field_simp

/-- HOL `WEDGE_GE_ALMOST_DISJOINT` (leaf_cell.hl:154-208)。FILLED
(2026-09-30)：凸角度论证——设 `θ = azim u0 u1 v1 v2`，(i) `z` 落轴或
`θ = 0` 或 `azim u0 u1 v1 z = 0` 时 `z` 在 `v1` 闭半平面锥；(ii)
`azim u0 u1 v1 z = θ` 时经 `azim_eq_azim_iff_alt` 落 `v2` 锥；(iii)
`0 < azim u0 u1 v1 z < θ` 时由 `p24_exp_azim_mul` + `azim_compl` 的
`azim u0 u1 v2 z ≤ 2π - θ` 界推出矛盾（`θ + ψ ∈ (0, 2π]` 的两支分别与
`ψ ≥ 0`、`φ > 0` 抵触）。PA18:906 的同名公开件仍为 `ported sorry`；
合并时两者取一（PA18 侧可改引本件）。 -/
theorem WEDGE_GE_ALMOST_DISJOINT_p24 (u0 u1 v1 v2 : V3)
    (h1 : ¬ Collinear3 u0 u1 v1) (h2 : ¬ Collinear3 u0 u1 v2) :
    wedgeGe u0 u1 v1 v2 ∩ wedgeGe u0 u1 v2 v1 ⊆
      affGe ({u0, u1} : Set V3) ({v1} : Set V3) ∪
        affGe ({u0, u1} : Set V3) ({v2} : Set V3) := by
  intro z hz
  obtain ⟨ha1, ha2⟩ := hz
  simp only [wedgeGe, Set.mem_setOf_eq] at ha1 ha2
  by_cases hzcol : Collinear3 u0 u1 z
  · refine Set.mem_union_left _ (p24_azim_zero_affGe h1 ?_)
    rw [azim, if_pos (Or.inr hzcol)]
  · by_cases hθ : azim u0 u1 v1 v2 = 0
    · refine Set.mem_union_left _ (p24_azim_zero_affGe h1 ?_)
      have hle : azim u0 u1 v1 z ≤ 0 := by
        have hle' := ha1.2
        rw [hθ] at hle'
        exact hle'
      have hφ0 : azim u0 u1 v1 z = 0 := le_antisymm hle (azim_nonneg u0 u1 v1 z)
      rw [hφ0]
    · by_cases hφ0 : azim u0 u1 v1 z = 0
      · exact Set.mem_union_left _ (p24_azim_zero_affGe h1 hφ0)
      · rcases eq_or_lt_of_le ha1.2 with hφθ | hφlt
        · exact Set.mem_union_right _ (p24_affGt_subset_affGe _ _
            ((azim_eq_azim_iff_alt h1 hzcol h2).mp hφθ))
        · exfalso
          have hθpos : 0 < azim u0 u1 v1 v2 :=
            lt_of_le_of_ne (azim_nonneg u0 u1 v1 v2) (Ne.symm hθ)
          have hφpos : 0 < azim u0 u1 v1 z :=
            lt_of_le_of_ne (azim_nonneg u0 u1 v1 z) (Ne.symm hφ0)
          have hψle : azim u0 u1 v2 z ≤ 2 * Real.pi - azim u0 u1 v1 v2 := by
            have h' := ha2.2
            rw [azim_compl h1 h2, if_neg hθ] at h'
            exact h'
          have hexp := p24_exp_azim_mul h1 h2 hzcol
          have hηle : azim u0 u1 v1 v2 + azim u0 u1 v2 z ≤ 2 * Real.pi := by
            linarith
          have hηpos : (0:ℝ) < azim u0 u1 v1 v2 + azim u0 u1 v2 z := by
            linarith
          rcases lt_or_eq_of_le hηle with hη | hη
          · have heq := angle_eq_of_exp_eq (azim_nonneg u0 u1 v1 z)
              (azim_lt_two_pi u0 u1 v1 z) hηpos.le hη ?_
            · linarith
            · have hexp2 : Complex.exp ((azim u0 u1 v1 z : ℝ) * Complex.I)
                = Complex.exp
                    (((azim u0 u1 v1 v2 + azim u0 u1 v2 z : ℝ)) * Complex.I) := by
                rw [hexp, ← Complex.exp_add]
                congr 1
                push_cast
                ring
              exact hexp2
          · have hpi : (((2 * Real.pi : ℝ) : ℂ) * Complex.I)
              = ((Real.pi : ℝ) : ℂ) * Complex.I
                + ((Real.pi : ℝ) : ℂ) * Complex.I := by
              push_cast
              ring
            have base : ((azim u0 u1 v1 v2 + azim u0 u1 v2 z : ℝ) : ℂ) * Complex.I
                = (azim u0 u1 v1 v2 : ℝ) * Complex.I
                  + (azim u0 u1 v2 z : ℝ) * Complex.I := by
              push_cast
              ring
            have hexp3 : Complex.exp ((azim u0 u1 v1 z : ℝ) * Complex.I)
                = Complex.exp (((0:ℝ) : ℂ) * Complex.I) := by
              rw [hexp, ← Complex.exp_add, ← base, hη, hpi, Complex.exp_add,
                Complex.exp_pi_mul_I]
              simp
            exact hφ0 (angle_eq_of_exp_eq (azim_nonneg u0 u1 v1 z)
              (azim_lt_two_pi u0 u1 v1 z) (le_refl 0) (by positivity) hexp3)

/-- `elV ul i ∈ ul`（下标在界内；HOL `EL` 的 junk 约定下界内成立）。 -/
private theorem p24_elV_mem : ∀ {ul : List V3} {i : ℕ}, i < ul.length → elV ul i ∈ ul
  | [], i, h => absurd h (by simp)
  | _ :: _, 0, _ => by simp [elV]
  | _ :: tl, j + 1, h => List.mem_cons_of_mem _ (p24_elV_mem (by simpa using h))

/-- 长度 3 列表的成员枚举（`barV V 2` 三元组的坐标穷举用）。 -/
private theorem p24_mem_cases_len3 {vl : List V3} {x : V3} (h3 : vl.length = 3)
    (hx : x ∈ vl) : x = elV vl 0 ∨ x = elV vl 1 ∨ x = elV vl 2 := by
  cases vl with
  | nil => simp at h3
  | cons a tl =>
    cases tl with
    | nil =>
      rcases List.mem_cons.mp hx with rfl | hmem'
      · exact Or.inl (by simp [elV])
      · exact absurd hmem' (by simp)
    | cons b tl2 =>
      cases tl2 with
      | nil =>
        rcases List.mem_cons.mp hx with rfl | hmem'
        · exact Or.inl (by simp [elV])
        · rcases List.mem_cons.mp hmem' with rfl | hmem'
          · exact Or.inr (Or.inl (by simp [elV]))
          · exact absurd hmem' (by simp)
      | cons c tl3 =>
        have h0 : tl3 = [] := by
          have h4 := h3
          simp at h4
          exact h4
        subst h0
        rcases List.mem_cons.mp hx with rfl | hmem'
        · exact Or.inl (by simp [elV])
        · rcases List.mem_cons.mp hmem' with rfl | hmem'
          · exact Or.inr (Or.inl (by simp [elV]))
          · rcases List.mem_cons.mp hmem' with rfl | hmem'
            · exact Or.inr (Or.inr (by simp [elV]))
            · exact absurd hmem' (by simp)

/-- HOL pack_concl 的配对半长：`dist u0 u1 < sqrt 8 → hl [u0,u1] < sqrt 2`
（`HL_2` + `sqrt 8 / 2 = sqrt 2`）。 -/
private theorem p24_hl_pair_lt_sqrt2 {u0 u1 : V3} (hd : dist u0 u1 < Real.sqrt 8) :
    hl [u0, u1] < Real.sqrt 2 := by
  have h82 : (Real.sqrt 8 : ℝ) / 2 = Real.sqrt 2 := by
    have h8 : (Real.sqrt 8 : ℝ) = 2 * Real.sqrt 2 := by
      rw [show (8:ℝ) = 4 * 2 from by norm_num, Real.sqrt_mul (by norm_num)]
      norm_num
    rw [h8]
    field_simp
  rw [p24_hl_pair]
  linarith [hd, h82]

/-- `barV V 2 vl` + 截断像 `{u0,u1}` + 第三点 `v` ⇒ `u0,u1 ∈ V` 且三点不共线
（`MHFTTZN1` 仿射维数 + `barV2_imp_not_collinear_setOfList`；PA18 `GBEWYFX`
的 `barV V 2` 直接形式）。 -/
private theorem p24_REUHADY_extract {V : Set V3} {u0 u1 v : V3} {vl : List V3}
    (hp : Packing V) (hbar : barV V 2 vl)
    (htr : setOfList (truncateSimplex 1 vl) = ({u0, u1} : Set V3))
    (hv : v = elV vl 2) :
    u0 ∈ V ∧ u1 ∈ V ∧ ¬ Collinear3 u0 u1 v := by
  have h2 : 2 ≤ vl.length := by rw [hbar.1]; omega
  have htr' : ({elV vl 0, elV vl 1} : Set V3) = {u0, u1} := by
    rw [← htr, truncateSimplex1_pair vl h2]
    ext x
    simp [setOfList]
  have hm0 : elV vl 0 ∈ vl := p24_elV_mem (by have := hbar.1; omega)
  have hm1 : elV vl 1 ∈ vl := p24_elV_mem (by have := hbar.1; omega)
  have hm2 : elV vl 2 ∈ vl := p24_elV_mem (by have := hbar.1; omega)
  have hini : initialSublist vl vl := by
    show ∃ yl, vl = vl ++ yl
    exact ⟨[], by rw [List.append_nil]⟩
  have hvn : voronoiNondg V vl := hbar.2 vl ⟨hini, by have := hbar.1; omega⟩
  have hV : setOfList vl ⊆ V := hvn.2.1
  have h0eq : elV vl 0 = u0 ∨ elV vl 0 = u1 := by
    have hm : (elV vl 0 : V3) ∈ ({elV vl 0, elV vl 1} : Set V3) := by simp
    rw [htr'] at hm
    rcases Set.mem_insert_iff.mp hm with he | he
    · exact Or.inl he
    · exact Or.inr he
  have h1eq : elV vl 1 = u0 ∨ elV vl 1 = u1 := by
    have hm : (elV vl 1 : V3) ∈ ({elV vl 0, elV vl 1} : Set V3) := by simp
    rw [htr'] at hm
    rcases Set.mem_insert_iff.mp hm with he | he
    · exact Or.inl he
    · exact Or.inr he
  have hu0 : u0 ∈ vl := by
    have hm : u0 ∈ ({elV vl 0, elV vl 1} : Set V3) := by rw [htr']; simp
    rcases Set.mem_insert_iff.mp hm with hc | hc
    · rw [hc]; exact hm0
    · rw [hc]; exact hm1
  have hu1 : u1 ∈ vl := by
    have hm : u1 ∈ ({elV vl 0, elV vl 1} : Set V3) := by rw [htr']; simp
    rcases Set.mem_insert_iff.mp hm with hc | hc
    · rw [hc]; exact hm0
    · rw [hc]; exact hm1
  refine ⟨hV hu0, hV hu1, ?_⟩
  intro hc
  have hc' : Collinear ℝ ({u0, u1, v} : Set V3) := hc
  have hbig := barV2_imp_not_collinear_setOfList V vl hp hbar
  refine hbig (Collinear.subset ?_ hc')
  intro x hx
  have hx' : x ∈ vl := hx
  rcases p24_mem_cases_len3 hbar.1 hx' with rfl | rfl | rfl
  · rcases h0eq with he | he
    · rw [he]; exact Set.mem_insert u0 {u1, v}
    · rw [he]; exact Set.mem_insert_of_mem u0 (Set.mem_insert u1 {v})
  · rcases h1eq with he | he
    · rw [he]; exact Set.mem_insert u0 {u1, v}
    · rw [he]; exact Set.mem_insert_of_mem u0 (Set.mem_insert u1 {v})
  · rw [hv]
    simp

/-- NEEDS (OXLZLEZ3.hl 的 `FCHKUGT`/`EWYBJUA` 叶胞链；PA18:2159/:2532 有
同名 `ported sorry` 孪生): capstone 退化支排除。在 capstone 假设组下
`azim u0 u1 v1 v2 ≠ 0 ∧ vl1 ≠ vl2` 成立——`azim = 0`（v1、v2 同侧）或
`vl1 = vl2`（则 `v1 = v2`、`wedge_ge ... v1 v1` 退化为平坦半平面）时，
mcell 析取假设把棱 `e` 上全部胞压进一张平坦半平面，与饱和填充下短棱处
三维胞的存在性/正二面角矛盾。REUHADY1 落地后本件是两枚 capstone 的
唯一残余缺口。 -/
private theorem p24_REUHADY_nondeg (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3)
    (v1 v2 : V3) (e : Set V3) (hs : saturated V) (hp : Packing V)
    (hdist : dist u0 u1 < Real.sqrt 8) (he : e = {u0, u1})
    (hhl1 : hl vl1 < Real.sqrt 2) (hhl2 : hl vl2 < Real.sqrt 2)
    (hbar1 : barV V 2 vl1) (hbar2 : barV V 2 vl2)
    (htr1 : setOfList (truncateSimplex 1 vl1) = e)
    (htr2 : setOfList (truncateSimplex 1 vl2) = e)
    (hv1 : v1 = elV vl1 2) (hv2 : v2 = elV vl2 2)
    (heX : ∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) :
    azim u0 u1 v1 v2 ≠ 0 ∧ vl1 ≠ vl2 := by
  -- NEEDS: OXLZLEZ3.hl FCHKUGT/EWYBJUA 叶胞链（退化支排除：azim = 0 时
  -- 闭楔退化为平坦半平面，mcell 析取假设与短棱处三维胞矛盾）；PA18:2159/:2532
  -- 有 `ported sorry` 孪生，真证落地后本文件两枚 capstone 即闭合。
  sorry

/-! ## Capstones: the pack_concl REUHADY conclusions -/

/-- HOL `REUHADY_concl` (pack_concl.hl:306-321), statement-identical to
`PackingAuto2.REUHADY_concl` (DISCHARGE candidate at merge).
RESTRUCTURED (2026-09-30, 最小件波): no longer a standalone `sorry` — the
proof applies `REUHADY1` (upstream giant) with every hypothesis
synthesized genuinely in this file:
  • `u0, u1 ∈ V` + `¬Collinear3 u0 u1 v1/v2` — `p24_REUHADY_extract`
    (barV/mhfttzn/affDim route, PA18 `GBEWYFX`'s barV V 2 direct form);
  • `u0 ≠ u1` — from `azim ≠ 0` via `azim_eq_zero_of_collinearY`;
  • `hl [u0,u1] < sqrt 2` — `p24_hl_pair_lt_sqrt2` (`HL_2` local copy +
    `sqrt 8 / 2 = sqrt 2`; PA15's olean builds but its `Kepler.Text.wedge`
    copy would clash, so no import);
  • the closed-wedge-intersection hypothesis of `REUHADY1` —
    `WEDGE_GE_ALMOST_DISJOINT_p24` (genuine, this file; PA18:906 twin is
    still a `ported sorry`);
  • `azim u0 u1 v1 v2 ≠ 0` + `vl1 ≠ vl2` — `p24_REUHADY_nondeg` NEEDS
    shim (OXLZLEZ3 `FCHKUGT`/`EWYBJUA` leaf-cell chain; note this
    statement's `azim ≠ 0` hypothesis is about FREE points `w1 w2`, so it
    yields `u0 ≠ u1` only).
REMAINING `sorryAx` inputs: `REUHADY1` (giant) + `p24_REUHADY_nondeg`
(shim). When both land, this capstone closes with zero further edits. -/
theorem REUHADY_p24 : ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3) (v1 v2 : V3)
    (e : Set V3) (w1 w2 : V3), saturated V → Packing V → dist u0 u1 < Real.sqrt 8 →
    e = {u0, u1} → ¬(azim u0 u1 w1 w2 = 0) →
    hl vl1 < Real.sqrt 2 ∧ hl vl2 < Real.sqrt 2 →
    barV V 2 vl1 ∧ barV V 2 vl2 →
    setOfList (truncateSimplex 1 vl1) = e ∧
    setOfList (truncateSimplex 1 vl2) = e ∧
    v1 = elV vl1 2 ∧ v2 = elV vl2 2 ∧
    (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 v1 v2} (fun t => dihX V t (u0, u1)) =
      azim u0 u1 v1 v2 := by
  intro V u0 u1 vl1 vl2 v1 v2 e w1 w2 hs hp hdist he haz hhl hbar htr
  obtain ⟨hhl1, hhl2⟩ := hhl
  obtain ⟨hbar1, hbar2⟩ := hbar
  obtain ⟨htr1, htr2, hv1, hv2, heX⟩ := htr
  have htr1' : setOfList (truncateSimplex 1 vl1) = ({u0, u1} : Set V3) := by
    rw [htr1, he]
  have htr2' : setOfList (truncateSimplex 1 vl2) = ({u0, u1} : Set V3) := by
    rw [htr2, he]
  obtain ⟨hu0V, hu1V, hnc1⟩ := p24_REUHADY_extract hp hbar1 htr1' hv1
  have hnc2 := (p24_REUHADY_extract hp hbar2 htr2' hv2).2.2
  have hu01 : u0 ≠ u1 := by
    intro hsub
    rw [hsub] at haz
    exact haz (azim_eq_zero_of_collinearY u1 u1 w1 w2 (collinear3_of_eq rfl))
  have hhlpair := p24_hl_pair_lt_sqrt2 hdist
  have hwedge := WEDGE_GE_ALMOST_DISJOINT_p24 u0 u1 v1 v2 hnc1 hnc2
  obtain ⟨hazv1, hvlne⟩ := p24_REUHADY_nondeg V u0 u1 vl1 vl2 v1 v2 e hs hp
    hdist he hhl1 hhl2 hbar1 hbar2 htr1 htr2 hv1 hv2 heX
  exact REUHADY1 V u0 u1 vl1 vl2 v1 v2 e hs hp hu0V hu1V hu01 hhlpair he
    hwedge hazv1 hvlne hhl1 hhl2 hbar1 hbar2 htr1 htr2 hv1 hv2 heX

/-- HOL `REUHADY_concl_version2` (pack_concl.hl:325-340),
statement-identical to `PackingAuto2.REUHADY_concl_version2` (DISCHARGE
candidate at merge). RESTRUCTURED (2026-09-30): same wiring as
`REUHADY_p24` minus the free-point azimuth branch — the closed-wedge
intersection hypothesis is PRESENT here and passed to `REUHADY1`
verbatim; `u0,u1 ∈ V`, `u0 ≠ u1`, `hl [u0,u1] < sqrt 2` are synthesized
genuinely (`p24_REUHADY_extract` / `p24_hl_pair_lt_sqrt2`; `u0 ≠ u1` via
the shim's `azim ≠ 0` + `azim_eq_zero_of_collinearY`), and `azim ≠ 0` /
`vl1 ≠ vl2` come from the `p24_REUHADY_nondeg` NEEDS shim (the `azim ≠ 0`
is NOT derivable from the visible hypotheses: at `azim = 0` the
wedge-intersection hypothesis degenerates to a trivial half-plane
inclusion — the exclusion is the OXLZLEZ3 `FCHKUGT`/`EWYBJUA`
leaf-cell chain).
REMAINING `sorryAx` inputs: `REUHADY1` (giant) + `p24_REUHADY_nondeg`
(shim). When both land, this capstone closes with zero further edits. -/
theorem REUHADY_version2_p24 : ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3)
    (v1 v2 : V3) (e : Set V3), saturated V → Packing V → dist u0 u1 < Real.sqrt 8 →
    e = {u0, u1} →
    wedgeGe u0 u1 v1 v2 ∩ wedgeGe u0 u1 v2 v1 ⊆
      affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} →
    hl vl1 < Real.sqrt 2 ∧ hl vl2 < Real.sqrt 2 →
    barV V 2 vl1 ∧ barV V 2 vl2 →
    setOfList (truncateSimplex 1 vl1) = e ∧
    setOfList (truncateSimplex 1 vl2) = e ∧
    v1 = elV vl1 2 ∧ v2 = elV vl2 2 ∧
    (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 v1 v2} (fun t => dihX V t (u0, u1)) =
      azim u0 u1 v1 v2 := by
  intro V u0 u1 vl1 vl2 v1 v2 e hs hp hdist he hwedge hhl hbar htr
  obtain ⟨hhl1, hhl2⟩ := hhl
  obtain ⟨hbar1, hbar2⟩ := hbar
  obtain ⟨htr1, htr2, hv1, hv2, heX⟩ := htr
  have htr1' : setOfList (truncateSimplex 1 vl1) = ({u0, u1} : Set V3) := by
    rw [htr1, he]
  have htr2' : setOfList (truncateSimplex 1 vl2) = ({u0, u1} : Set V3) := by
    rw [htr2, he]
  obtain ⟨hu0V, hu1V, hnc1⟩ := p24_REUHADY_extract hp hbar1 htr1' hv1
  have hnc2 := (p24_REUHADY_extract hp hbar2 htr2' hv2).2.2
  have hhlpair := p24_hl_pair_lt_sqrt2 hdist
  obtain ⟨hazv1, hvlne⟩ := p24_REUHADY_nondeg V u0 u1 vl1 vl2 v1 v2 e hs hp
    hdist he hhl1 hhl2 hbar1 hbar2 htr1 htr2 hv1 hv2 heX
  have hu01 : u0 ≠ u1 := by
    intro hsub
    rw [hsub] at hazv1
    exact hazv1 (azim_eq_zero_of_collinearY u1 u1 v1 v2 (collinear3_of_eq rfl))
  exact REUHADY1 V u0 u1 vl1 vl2 v1 v2 e hs hp hu0V hu1V hu01 hhlpair he
    hwedge hazv1 hvlne hhl1 hhl2 hbar1 hbar2 htr1 htr2 hv1 hv2 heX

/-! ## GRUTOTI statement copy (parallel-owned Auto23) -/

/-- NEEDS (Auto23, GRUTOTI.hl:48-58): `GRUTOTI1_concl` statement copy —
the parallel Auto23 lane owns the proof of `GRUTOTI1_concl` (already
sorried in PackingAuto2); the 2π edge-total is the complementary
measure-splitting fact consumed alongside `REUHADY1` by downstream
wedge/annulus arguments. This `_p24` copy documents the dependency for
merge; delete at merge into Auto23's results.  `private` is
file-scoped, so the public re-export below gives the PackingConcl
assembly a nameable twin. -/
private theorem GRUTOTI1_concl_p24 : ∀ (V : Set V3) (u0 u1 : V3) (e : Set V3),
    saturated V → Packing V → u0 ∈ V → u1 ∈ V → u0 ≠ u1 →
    hl [u0, u1] < Real.sqrt 2 → e = {u0, u1} →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X}
        (fun t => dihX V t (u0, u1)) = 2 * Real.pi := by
  intro V u0 u1 e hs hp hu0 hu1 hne hhl he
  exact GRUTOTI1_concl V u0 u1 e hs hp hu0 hu1 hne hhl he

/-- Public re-export of the private `GRUTOTI1_concl_p24` above — same
statement, verbatim. PackingConcl discharges Auto2's `GRUTOTI1_concl`
interface through this name (the `private` modifier hides the original
from every other module); the upstream `sorry` in
`PackingAuto2.GRUTOTI1_concl` flows along the proof term. Delete
together with the `_p24` copy at merge into Auto23's results. -/
theorem GRUTOTI1_concl_p24_pub : ∀ (V : Set V3) (u0 u1 : V3) (e : Set V3),
    saturated V → Packing V → u0 ∈ V → u1 ∈ V → u0 ≠ u1 →
    hl [u0, u1] < Real.sqrt 2 → e = {u0, u1} →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X}
        (fun t => dihX V t (u0, u1)) = 2 * Real.pi :=
  GRUTOTI1_concl_p24

end Kepler.Text
