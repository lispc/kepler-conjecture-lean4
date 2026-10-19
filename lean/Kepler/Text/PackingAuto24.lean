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
  `REUHADY1` + the `p24_REUHADY_nondeg_azim` azimuth exclusion (2026-10-08
  split of the `p24_REUHADY_nondeg` shim; its `vl1 ≠ vl2` half is
  genuinely closed via `azim_self`).

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
    sandwich); full map in the REUHADY1 docstring. 2026-10-08 wave: the
    (d) azim-additivity + setSum final-assembly kit landed genuinely
    (`p24_azim_base_shift`, `p24_wedge_ge_split`, `p24_setSum_congr`/
    `_superset_eq`/`_union`; new imports `TopologyFan`/`LuneVolume`),
    shrinking the open work to the mcell4 realization + measure sandwich.
    2026-10-19 二发/三发 waves (lane pa24reuhady): the (d) bulk itself is now
    a layered scaffold (see chapter `## (d) 段分层施工骨架`) with its (d)-local
    pieces genuine (D-FIN finiteness / D6 union-sum bridge / junk-zero
    definitional / D7 end wall / `p24_barV2_far_noncollinear` / final
    assembly `p24_wedge_setSum_eq_azim`); `REUHADY1` is rewritten as a
    genuine assembly over the three scaffold items. File-level `sorryAx`
    entries are now exactly: the two open scaffolds (`p24_cell_cap_dihX`
    = D3+D4+D5 per-arm ratio, HL 2386-7358+8187-8241; `p24_cap_wedge_cover`
    = D1+D2 corridor/cover, HL 345-2386) plus, via scaffold 1
    `p24_wedge_cells_pair_null` — CLOSED 三发 2026-10-19 through
    `import Kepler.Text.PackingAuto17` + `AJRIPQN` — the upstream SF-20
    shim debt (PA13 `SLTSTLO2`/`DDZUPHJ`, PA10 `RVFXZBU` i=2,3, PA14
    `QZKSYKG1`/`QZKSYKG2`). Axiom probe (same day): `p24_barV2_far_noncollinear`
    and `p24_cap_wedge_vol` print [propext, Classical.choice, Quot.sound]
    only (三零); the assembly/`REUHADY1` carry the scaffold `sorryAx` as
    ledgered.
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
    (pair half-length, `HL_2` local copy). REMAINING file-level `sorry`
    input: `REUHADY1` itself only — the non-flat-cell existence
    `p24_exists_mcell_not_flat` (the (β) `v1 = v2` residual) is GENUINE
    since the 2026-10-10..12 waves (branch assembly `p24_caseB2_branch`;
    axiom-level taint persists only via upstream PA2/PA10/PA11 interface
    stubs, see the capstone docstrings). The (α)
    `v1 ≠ v2` azimuth exclusion is GENUINE (2026-10-08/09 wave):
    `p24_nondeg_azim_ne` (coordinate kit `p24_tri_data` + the strengthened
    `p24_tri_gamma` with the γ-relation, disk+cone bounds, final packing
    contradiction) closes the `v1 ≠ v2` branch of
    `p24_REUHADY_nondeg_azim`; the OXLZLEZ3 `FCHKUGT`/`EWYBJUA`
    degenerate-branch exclusion has sorried twins at PA18:2159/:2532).
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
import Kepler.Text.PackingAuto17
import Kepler.Text.ConicCapVolume
import Kepler.Text.Polytope
import Kepler.Text.TopologyFan
import Kepler.Geom.Azim
import Kepler.Geom.LuneVolume
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

/-! ## (d) 段 kit：azim 可加性 / 闭楔分裂 / setSum 装配件（2026-10-08 波，全部真证）

REUHADY1 残件 (d)（HL REUHADY.hl ~400-8356）的方位角-可加性前置件：
- `p24_azim_base_shift`：换基差等式（PA18:3532 `AZIM_BASE_SHIFT_LE` 的真证
  孪生，`sum4_azim_fan` 两次应用；合并时两者取一）；
- `p24_wedge_ge_split`：内射线把闭楔分成两枚闭楔之并（PA18:3566
  `WEDGE_GE_SPLIT` 的真证孪生；(d) 的 fan 逐叶求和按方位角切分的工具）；
- `p24_setSum_congr` / `p24_setSum_superset_eq` / `p24_setSum_union`：
  HOL `SUM_EQ` / `SUM_SUPERSET` / `SUM_UNION` 的 `setSum` 装配件（(d) 终段
  HL ~8200-8356 的 SUM 装配消费）；
- `p24_cellParamsD_spec` / `p24_dihX_of_k3` / `p24_dihX_of_k4`：(d)(i)
  叶胞实现的 `cell_params_d` 前置件（epsilon 满足谓词 + `dihX` 在
  `k = 3/4` 臂的读出式；PA21 wave-B1 前半的免 import 私拷——PA21 引入
  PA15/PA18 不可 import，`k'` 与给定 `k` 的同一性需 PA17 `AJRIPQN`
  刚性件，仍开放）。
新 import：`Kepler.Text.TopologyFan`（`sum4_azim_fan`；其闭包无 PA15 的
`Kepler.Text.wedge` 撞名）与 `Kepler.Geom.LuneVolume`（`azim_dihv_same` /
`azim_dihv_compl`：叶胞 `dihV` 项到方位角的换算件，(d) 测度三明治残件
消费）。 -/

/-- HOL `AZIM_BASE_SHIFT_LE` (leaf_cell.hl:3529-3547), via two applications of
fan.hl:1698 `sum4_azim_fan` (the three-point azimuth addition) and linear
arithmetic. Genuine twin of PA18:3532; pick one at merge. -/
private theorem p24_azim_base_shift (x y b1 b2 w1 w2 : V3)
    (h1 : ¬Collinear3 x y b1) (h2 : ¬Collinear3 x y b2) (h3 : ¬Collinear3 x y w1)
    (h4 : ¬Collinear3 x y w2)
    (h5 : azim x y b1 b2 ≤ azim x y b1 w1) (h6 : azim x y b1 b2 ≤ azim x y b1 w2) :
    azim x y b1 w2 - azim x y b1 w1 = azim x y b2 w2 - azim x y b2 w1 := by
  have hyx : y ≠ x := fun he => h1 (collinear3_of_eq he)
  have e1 := sum4_azim_fan hyx h1 h2 h4 h6
  have e2 := sum4_azim_fan hyx h1 h2 h3 h5
  linarith

/-- HOL `WEDGE_GE_SPLIT` (leaf_cell.hl:3548-3611): inserting an interior ray
splits the closed wedge into two closed wedges (`p24_azim_base_shift`).
Genuine twin of PA18:3566; pick one at merge. -/
private theorem p24_wedge_ge_split (u0 u1 u2 u3 w : V3)
    (h2 : ¬Collinear3 u0 u1 u2) (h3 : ¬Collinear3 u0 u1 u3)
    (hw : w ∈ wedge u0 u1 u2 u3) :
    ¬Collinear3 u0 u1 w ∧
      wedgeGe u0 u1 u2 u3 = wedgeGe u0 u1 u2 w ∪ wedgeGe u0 u1 w u3 := by
  rw [wedge, Set.mem_setOf_eq] at hw
  refine ⟨hw.1, ?_⟩
  refine Set.ext fun x => ?_
  by_cases hcol : Collinear3 u0 u1 x
  · have hx0 : azim u0 u1 u2 x = 0 := by rw [azim, if_pos (Or.inr hcol)]
    constructor
    · intro hx
      refine Set.mem_union_left _ ?_
      rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
      refine ⟨azim_nonneg u0 u1 u2 x, ?_⟩
      rw [hx0]
      exact le_of_lt hw.2.1
    · intro hx
      rw [Set.mem_union] at hx
      rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
      rcases hx with hx | hx
      · rw [hx0]
        exact ⟨le_refl 0, azim_nonneg u0 u1 u2 u3⟩
      · rw [hx0]
        exact ⟨le_refl 0, azim_nonneg u0 u1 u2 u3⟩
  · rcases le_or_gt (azim u0 u1 u2 x) (azim u0 u1 u2 w) with hle | hgt
    · constructor
      · intro hx
        refine Set.mem_union_left _ ?_
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        exact ⟨azim_nonneg u0 u1 u2 x, hle⟩
      · intro hx
        rw [Set.mem_union] at hx
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        rcases hx with hx | hx
        · exact ⟨hx.1, le_trans hx.2 (le_of_lt hw.right.right)⟩
        · exact ⟨azim_nonneg u0 u1 u2 x, le_trans hle (le_of_lt hw.right.right)⟩
    · have hshift := p24_azim_base_shift u0 u1 u2 w x u3 h2 hw.1 hcol h3 (le_of_lt hgt)
        (le_of_lt hw.2.2)
      constructor
      · intro hx
        refine Set.mem_union_right _ ?_
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        refine ⟨azim_nonneg u0 u1 w x, ?_⟩
        linarith
      · intro hx
        rw [Set.mem_union] at hx
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        rcases hx with hx | hx
        · exact ⟨hx.1, le_trans hx.2 (le_of_lt hw.right.right)⟩
        · rcases le_or_gt (azim u0 u1 u2 x) (azim u0 u1 u2 w) with hle'' | hgt''
          · exact ⟨azim_nonneg u0 u1 u2 x, le_trans hle'' (le_of_lt hw.2.2)⟩
          · have hshift' := p24_azim_base_shift u0 u1 u2 w x u3 h2 hw.1 hcol h3
              (le_of_lt hgt'') (le_of_lt hw.2.2)
            rw [wedgeGe, Set.mem_setOf_eq] at hx
            refine ⟨azim_nonneg u0 u1 u2 x, ?_⟩
            linarith

/-- HOL `SUM_EQ` content: `setSum` agrees on pointwise-equal functions
(junk convention: both sides `0` on infinite sets). (d) final-assembly kit
(HL REUHADY.hl ~8200-8356). -/
private theorem p24_setSum_congr {α : Type*} {s : Set α} {f g : α → ℝ}
    (h : ∀ a ∈ s, f a = g a) : setSum s f = setSum s g := by
  unfold setSum
  by_cases hs : Set.Finite s
  · rw [dif_pos hs, dif_pos hs]
    exact Finset.sum_congr rfl fun a ha => h a (hs.mem_toFinset.mp ha)
  · rw [dif_neg hs, dif_neg hs]

/-- HOL `SUM_SUPERSET` content: extending the family by zero-valued members
keeps the `setSum`. (d) final-assembly kit. -/
private theorem p24_setSum_superset_eq {α : Type*} {s t : Set α} (hs : s.Finite)
    (ht : t.Finite) (hsub : s ⊆ t) (f : α → ℝ)
    (hz : ∀ a ∈ t, a ∉ s → f a = 0) : setSum s f = setSum t f := by
  unfold setSum
  rw [dif_pos hs, dif_pos ht]
  have hsd : ht.toFinset \ hs.toFinset ⊆ ht.toFinset := fun a ha =>
    (Finset.mem_sdiff.mp ha).1
  have hsplit : ∑ x ∈ ht.toFinset \ hs.toFinset, f x + ∑ x ∈ hs.toFinset, f x
      = ∑ x ∈ ht.toFinset, f x := Finset.sum_sdiff
      (fun a ha => (Set.Finite.mem_toFinset ht).mpr
        (hsub ((Set.Finite.mem_toFinset hs).mp ha)))
  have hzero : ∑ x ∈ ht.toFinset \ hs.toFinset, f x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have h1 : x ∈ t := (Set.Finite.mem_toFinset ht).mp (Finset.mem_sdiff.mp hx).1
    have h2 : x ∉ s := fun hcon =>
      (Finset.mem_sdiff.mp hx).2 ((Set.Finite.mem_toFinset hs).mpr hcon)
    rw [hz x h1 h2]
  linarith [hsplit, hzero]

/-- HOL `SUM_UNION` content (disjoint finite families). (d) final-assembly
kit: the fan cells split side-wise along the interior ray. -/
private theorem p24_setSum_union {α : Type*} {s t : Set α} (hs : s.Finite) (ht : t.Finite)
    (hdisj : Disjoint s t) (f : α → ℝ) : setSum (s ∪ t) f = setSum s f + setSum t f := by
  unfold setSum
  rw [dif_pos (hs.union ht), dif_pos hs, dif_pos ht, Set.Finite.toFinset_union hs ht]
  exact Finset.sum_union (Finset.disjoint_left.mpr fun a ha hb =>
    Set.disjoint_left.mp hdisj ((Set.Finite.mem_toFinset hs).mp ha)
      ((Set.Finite.mem_toFinset ht).mp hb))

/-- The `cellParamsD` epsilon satisfies its predicate whenever a witness
exists (PA21 wave-B1 first half, import-free private copy; the `k'`
identification with a given `k` needs the PA17 `AJRIPQN` rigidity and is
NOT included). (d)(i) leaf-cell realization kit. -/
private theorem p24_cellParamsD_spec (V : Set V3) (X : Set V3) (vl : List V3)
    (h : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧
      initialSublist vl p.2) :
    (cellParamsD V X vl).1 ≤ 4 ∧ barV V 3 (cellParamsD V X vl).2 ∧
      X = mcell (cellParamsD V X vl).1 V (cellParamsD V X vl).2 ∧
      initialSublist vl (cellParamsD V X vl).2 :=
  Classical.epsilon_spec (p := fun p : ℕ × List V3 =>
    p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧ initialSublist vl p.2) h

/-- (d)(i) read-off kit, `k = 4` arm: for a non-null cell whose
`cellParamsD` witness at the edge `[u0,u1]` has first component `4`,
`dihX` is the plain tetrahedral dihedral `dihu4`. -/
private theorem p24_dihX_of_k4 (V X : Set V3) (u0 u1 : V3)
    (hn : ¬ nullSet X)
    (h2 : (cellParamsD V X [u0, u1]).1 ≠ 2) (h3 : (cellParamsD V X [u0, u1]).1 ≠ 3)
    (h4 : (cellParamsD V X [u0, u1]).1 = 4) :
    dihX V X (u0, u1) = dihu4 (cellParamsD V X [u0, u1]).2 := by
  have hd : dihX V X (u0, u1) =
      if nullSet X then 0
      else if (cellParamsD V X [u0, u1]).1 = 2 then dihu2 V (cellParamsD V X [u0, u1]).2
      else if (cellParamsD V X [u0, u1]).1 = 3 then dihu3 V (cellParamsD V X [u0, u1]).2
      else if (cellParamsD V X [u0, u1]).1 = 4 then dihu4 (cellParamsD V X [u0, u1]).2
      else 0 := by unfold dihX; rfl
  rw [hd, if_neg hn, if_neg h2, if_neg h3, if_pos h4]

/-- (d)(i) read-off kit, `k = 3` arm: for a non-null cell whose
`cellParamsD` witness at the edge `[u0,u1]` has first component `3`,
`dihX` is the `mxi`-dihedral `dihu3` (the HL leaf-cell arm). -/
private theorem p24_dihX_of_k3 (V X : Set V3) (u0 u1 : V3)
    (hn : ¬ nullSet X)
    (h2 : (cellParamsD V X [u0, u1]).1 ≠ 2) (h3 : (cellParamsD V X [u0, u1]).1 = 3) :
    dihX V X (u0, u1) = dihu3 V (cellParamsD V X [u0, u1]).2 := by
  have hd : dihX V X (u0, u1) =
      if nullSet X then 0
      else if (cellParamsD V X [u0, u1]).1 = 2 then dihu2 V (cellParamsD V X [u0, u1]).2
      else if (cellParamsD V X [u0, u1]).1 = 3 then dihu3 V (cellParamsD V X [u0, u1]).2
      else if (cellParamsD V X [u0, u1]).1 = 4 then dihu4 (cellParamsD V X [u0, u1]).2
      else 0 := by unfold dihX; rfl
  rw [hd, if_neg hn, if_neg h2, if_pos h3]


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

/-! ## (d) 段分层施工骨架（2026-10-19 REUHADY1 二发波，lane pa24reuhady）

HL REUHADY.hl 345-8356（(d) 主体，8100 行 / 642 NEW_GOAL）施工图（分层沿 HL 界标注释）：

- D1 走廊章（HL 345-1250，界标 "OK until here" :1250）：S = voronoi_list V [u0;u1]
  的闭性/仿射性/有界性矛盾（:416-504）、内点 p = circumcenter、margin d、最近包装点
  a' 与 8-界分离 `dist (p,u0) + 4d ≤ dist (p,w)`（:733-830）。产出 b ∈ (0,1)：
  无其他 Voronoi 胞侵入走廊。纯度量/凸性，无 Marchal 依赖，可独立移植。
- D2 覆盖章（HL 1251-2386）：aff_ge_alt W、c = max b (hl/√2)、C = ball(u0,1) ∩
  rcone_gt(u0,u1,c)；C 内每点落在某 `mcell i V ul`（i ≤ 4、barV V 3、
  truncate 1 = [u0;u1]，:1531-1629）；P1/P2/P3 半径参数集与 r1/r2/r、d1/d2/d 的
  min-max 装配（:1705-2790）。
- D3 k=2 章（HL 2834-3562，界标 "OK here" :3562）：mcell2 胞的
  `vol (X ∩ D) = vol D · dihX / (2π)`（VOLUME_CONIC_CAP_WEDGE + MCELL_EXPLICIT）。
- D4 k≥4 章（HL 3908-5596，界标 "OK here" :5198）：mcell4 胞同上 + AJRIPQN 首批识别。
- D5 k=3 章（HL 5627-7358）：mcell3 胞同上（"begin the computation" :6692）。
- D6 家族装配章（HL 7395-8250）：E = D ∩ wedge_ge、s = 楔族、
  MEASURE_NEGLIGIBLE_UNIONS_IMAGE 三支（有限性 FINITE_EDGE_X2 / 成对零交 AJRIPQN
  :7437 / 覆盖 = D2）+ 逐胞 SUM_EQ（junk 零侧 :8187-8241）。
- D7 终墙（HL 8250-8356）：`vol E = vol D · azim / (2π)`
  （VOLUME_CONIC_CAP_WEDGE_GE_VS_CONIC_CAP）+ vol D > 0 + 2π > 0 消去
  ⇒ `sum s dihX = azim`。

本章落地状态（2026-10-19）：
- **真证**：D6 并集-求和桥（`p24_measure_setSum_biUnion`，PA23 银行桥私拷——PA23
  import PA15 故不可 import）、有限性（`p24_finite_edge_cells`，PA15
  `FINITE_EDGE_X2` 链私拷——PA15 的 `Kepler.Text.wedge` 会遮蔽本文件的开楔，
  见文件头注）、D7 终墙（`p24_cap_wedge_vol`，消费本文件
  `volumeConicCapWedgeGeVsConicCap` + CCV `volumeConicCapPos`）、junk 零侧
  定义性件（`p24_dihX_of_nullSet`）、(d) 前置真证件
  `p24_barV2_far_noncollinear`、装配（`p24_wedge_setSum_eq_azim`，纯组合零 sorry）。
- **scaffold 三 sorry**（每条 `-- NEEDS` 记账，注 HL 行段 + 闭链路径）：
  `p24_wedge_cells_pair_null`（D6 成对零交支；闭链 = PA17 `AJRIPQN`——帽石
  2026-10-12 已闭，其上游 PA13 SLTSTLO2/DDZUPHJ、PA10 RVFXZBU、PA14 QZKSYKG
  语句在树而体开放（SF-20 shim 债）；PA17 import 拓扑 2026-10-19 已验证安全：
  不传递依赖 PA24，其 Kepler.Text 顶层 def 不遮蔽 wedge/dihV/azim/hl）；
  `p24_cell_cap_dihX`（D3+D4+D5 逐臂比例式 + junk 零侧，含 (d)(i) k′-vs-k
  识别与 fan-triple 胞非空性）；`p24_cap_wedge_cover`（D1+D2 走廊与覆盖，
  产出半径 r d 存在性）。
- `REUHADY1` 本体改真装配（消费以上全部），原 8100 行单体黑箱 `sorry` 退役；
  残余 sorryAx 入口从 1 个不可定位黑箱 → 3 个 HL 行段精确定位 scaffold。 -/

/-- (d) 骨架的楔形胞族：REUHADY_concl1_new 结论中 `setSum` 家族的本体。 -/
private def p24_wedgeCells (V : Set V3) (u0 u1 n1 n2 : V3) (e : Set V3) : Set (Set V3) :=
  {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧ X ⊆ wedgeGe u0 u1 n1 n2}

/-! ### D6 有限性支（真证；PA15 `FINITE_EDGE_X2` 链私拷，体逐字 p15_→p24_） -/

/-- A translate of a packing is a packing (rigidity of `dist`). -/
private theorem p24_packing_translate (V : Set V3) (t : V3) (hp : Packing V) :
    Packing ((fun w => w - t) '' V) := by
  intro a ha b hb hdist
  obtain ⟨u, huV, rfl⟩ := ha
  obtain ⟨v, hvV, rfl⟩ := hb
  simp only [] at hdist ⊢
  have hd : dist (u - t) (v - t) = dist u v := by
    simp only [dist_eq_norm]
    congr 1
    abel
  rw [hd] at hdist
  have huv := hp u huV v hvV hdist
  rw [huv]

/-- Finiteness of the packing points in a ball centered at an arbitrary point
(`Packing.finite_inter_ball` is stated for balls centered at `0`). -/
private theorem p24_finite_inter_ball_at (V : Set V3) (c : V3) (r : ℝ) (hp : Packing V) :
    (V ∩ Metric.ball c r).Finite := by
  classical
  have hfin : ((fun w : V3 => w - c) '' V ∩ Metric.ball 0 r).Finite :=
    (p24_packing_translate V c hp).finite_inter_ball r
  have hsub : V ∩ Metric.ball c r ⊆
      (fun w : V3 => w + c) '' ((fun w : V3 => w - c) '' V ∩ Metric.ball 0 r) := by
    rintro x ⟨hxV, hxb⟩
    refine ⟨x - c, ⟨⟨x, hxV, rfl⟩, ?_⟩, by simp⟩
    rw [Metric.mem_ball, dist_zero_right]
    have hxc : dist x c < r := Metric.mem_ball.mp hxb
    rw [dist_eq_norm] at hxc
    exact hxc
  exact (hfin.image (fun w : V3 => w + c)).subset hsub

/-- `BARV_3_IMP_FINITE_lemma1`（QZYZMJC.hl:62-100；PA15:207 私拷）：`barV V 3`
单形的两个表点相距 < 4（饱和包装 + PA12 单点 Voronoi 胞）。 -/
private theorem p24_barV3ImpFinite1 {V : Set V3} {ul : List V3} {u v : V3}
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

/-- `BARV_3_IMP_FINITE_lemma2`（QZYZMJC.hl:104-110；PA15:244 私拷）：整个表
落在任一表点的 4-球内。 -/
private theorem p24_barV3ImpFinite2 {V : Set V3} {ul : List V3} {v : V3}
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hv : v ∈ setOfList ul) :
    setOfList ul ⊆ Metric.ball v 4 := by
  intro s hsmem
  refine p24_barV3ImpFinite1 hp hs hb ?_
  intro x hx
  rcases (by simpa using hx : x = s ∨ x = v) with hx1 | hx1
  · rw [hx1]
    exact hsmem
  · rw [hx1]
    exact hv

/-- D-FIN（真证）：marchal3.hl:2184 `FINITE_EDGE_X2`（PA15:1257 私拷）。边上
胞族有限 —— (d) 的楔族是它的子集，D6 的 MEASURE_NEGLIGIBLE_UNIONS_IMAGE 支
由此吃饭；同时服务 GRUTOTI/OXLZLEZ3 等边胞装配。 -/
private theorem p24_finite_edge_cells (V : Set V3) (e : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (he : e = {u0, u1}) :
    {X : Set V3 | mcellSet V X ∧ edgeX V X e}.Finite := by
  classical
  -- the finite index tuples: 4-point lists drawn from `V ∩ ball u0 4`
  have hVb : (V ∩ Metric.ball u0 4).Finite := p24_finite_inter_ball_at V u0 4 hp
  have hT : {ul : List V3 | ∃ a b c d : V3, a ∈ V ∩ Metric.ball u0 4 ∧
      b ∈ V ∩ Metric.ball u0 4 ∧ c ∈ V ∩ Metric.ball u0 4 ∧
      d ∈ V ∩ Metric.ball u0 4 ∧ ul = [a, b, c, d]}.Finite := by
    have hsub : {ul : List V3 | ∃ a b c d : V3, a ∈ V ∩ Metric.ball u0 4 ∧
        b ∈ V ∩ Metric.ball u0 4 ∧ c ∈ V ∩ Metric.ball u0 4 ∧
        d ∈ V ∩ Metric.ball u0 4 ∧ ul = [a, b, c, d]} ⊆
        (fun q : V3 × V3 × V3 × V3 => [q.1, q.2.1, q.2.2.1, q.2.2.2]) ''
        ((V ∩ Metric.ball u0 4) ×ˢ ((V ∩ Metric.ball u0 4) ×ˢ
          ((V ∩ Metric.ball u0 4) ×ˢ (V ∩ Metric.ball u0 4)))) := by
      intro l hl
      rw [Set.mem_setOf_eq] at hl
      obtain ⟨a, b, c, d, h0, h1', h2', h3', rfl⟩ := hl
      exact ⟨(a, b, c, d),
        Set.mem_prod.mpr ⟨h0, Set.mem_prod.mpr ⟨h1', Set.mem_prod.mpr ⟨h2', h3'⟩⟩⟩, rfl⟩
    exact Set.Finite.subset ((hVb.prod (hVb.prod (hVb.prod hVb))).image _) hsub
  have hsub : {X : Set V3 | mcellSet V X ∧ edgeX V X e} ⊆
      (fun t : ℕ × List V3 => mcell t.1 V t.2) ''
        ((Set.Iic (4 : ℕ)) ×ˢ
          {ul : List V3 | ∃ a b c d : V3, a ∈ V ∩ Metric.ball u0 4 ∧
            b ∈ V ∩ Metric.ball u0 4 ∧ c ∈ V ∩ Metric.ball u0 4 ∧
            d ∈ V ∩ Metric.ball u0 4 ∧ ul = [a, b, c, d]}) := by
    intro X hX
    obtain ⟨hm, hedge⟩ := hX
    simp only [mcellSet] at hm
    obtain ⟨i, ul, hXmul, hbul⟩ := hm
    simp only [edgeX] at hedge
    obtain ⟨w0, w1, he0, hw0, hw1, hwne⟩ := hedge
    have heq : {w0, w1} = {u0, u1} := he0.symm.trans he
    have hw0in : w0 ∈ ({u0, u1} : Set V3) := by rw [← heq]; exact Set.mem_insert w0 {w1}
    have hu0in : u0 ∈ ({w0, w1} : Set V3) := by rw [heq]; exact Set.mem_insert u0 {u1}
    have hu1in : u1 ∈ ({w0, w1} : Set V3) := by
      rw [heq]
      exact Set.mem_insert_of_mem u0 (Set.mem_singleton u1)
    have hu0vx : u0 ∈ VX V X := by
      rcases Set.mem_insert_iff.mp hu0in with h | h
      · rw [h]
        exact hw0
      · rcases Set.mem_singleton_iff.mp h with h
        rw [h]
        exact hw1
    by_cases hnull : nullSet X
    · exfalso
      have hvx0 : VX V X = ∅ := by rw [VX, if_pos hnull]
      rw [hvx0] at hu0vx
      simp at hu0vx
    -- extract the cell parameters chosen by `cellParams`
    have hwit : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 := by
      refine ⟨(if i ≤ 4 then i else 4, ul), ?_, hbul, ?_⟩
      · by_cases hle : i ≤ 4 <;> simp [hle]
      · by_cases hle : i ≤ 4
        · rw [if_pos hle, hXmul]
        · rw [if_neg hle]
          exact hXmul.trans ((MCELL_EXPLICIT i V ul).2.2.2.2 (by omega))
    have hspec := Classical.epsilon_spec
      (p := fun p : ℕ × List V3 => p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2) hwit
    obtain ⟨hk4, hbarp, hXp⟩ := hspec
    by_cases hk0 : (cellParams V X).1 = 0
    · exfalso
      have hvx0 : VX V X = ∅ := by rw [VX, if_neg hnull, if_pos hk0]
      rw [hvx0] at hu0vx
      simp at hu0vx
    · -- `u0` is a list point of the parameter list
      have hvx : VX V X =
          setOfList (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2) := by
        rw [VX, if_neg hnull, if_neg hk0]
      have hu0tr : u0 ∈ setOfList (truncateSimplex ((cellParams V X).1 - 1)
          (cellParams V X).2) := hvx ▸ hu0vx
      have hk4' : (cellParams V X).1 ≤ 4 := hk4
      have hk0' : (cellParams V X).1 ≠ 0 := hk0
      have hlen4 : (cellParams V X).2.length = 3 + 1 := hbarp.1
      have hinit := (TRUNCATE_SIMPLEX_INITIAL_SUBLIST ((cellParams V X).1 - 1)
        (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2)
          (cellParams V X).2).1
        ⟨rfl, by omega⟩
      obtain ⟨hsubl, -⟩ := hinit
      rcases hsubl with ⟨yl, hyl⟩
      have hu0list : u0 ∈ setOfList (cellParams V X).2 := by
        rw [hyl]
        exact List.mem_append_left _ hu0tr
      obtain ⟨a, b, c, d, hulp⟩ := BARV_3_EXPLICIT V (cellParams V X).2 hbarp
      have hball := p24_barV3ImpFinite2 hp hs hbarp hu0list
      have hpts : ∀ z ∈ setOfList (cellParams V X).2, z ∈ V ∩ Metric.ball u0 4 := by
        intro z hz
        exact ⟨BARV_SUBSET V 3 (cellParams V X).2 hbarp hz, hball hz⟩
      refine ⟨((cellParams V X).1, (cellParams V X).2),
        ⟨hk4, ⟨a, b, c, d, ?_, ?_, ?_, ?_, hulp⟩⟩, hXp.symm⟩
      · exact hpts a (by rw [hulp]; simp [setOfList])
      · exact hpts b (by rw [hulp]; simp [setOfList])
      · exact hpts c (by rw [hulp]; simp [setOfList])
      · exact hpts d (by rw [hulp]; simp [setOfList])
  exact Set.Finite.subset
    ((((Set.finite_Iic 4).prod hT).image (fun t : ℕ × List V3 => mcell t.1 V t.2))) hsub

/-! ### D6 并集-求和桥（真证；PA23 `p23_measure_setSum_biUnion` 银行桥私拷） -/

/-- Finite `MEASURE_NEGLIGIBLE_UNIONS_IMAGE`（Pack2 桥；grutoti-scout §2.2）：
有限族 + 可测 + 成对零交 + 逐项有限体积 ⇒ 体积和 = 并的体积。 -/
private theorem p24_measure_setSum_biUnion {ι : Type*} {s : Set ι} {f : ι → Set V3}
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

/-! ### junk 零侧定义性件（真证） -/

/-- junk 零侧其一：null 胞的 `dihX` 为 0（`dihX` if-链首支；PA23:350 先例私拷）。
D3-D5 junk 臂的 vol 侧零（HL :8187-8241 共面性论证）留在
`p24_cell_cap_dihX` 的 NEEDS 债内。 -/
private theorem p24_dihX_of_nullSet (V : Set V3) (X : Set V3) (p : V3 × V3)
    (h : nullSet X) : dihX V X p = 0 := if_pos h

/-! ### (d) 前置真证件 -/

/-- (d) 前置真证件：`barV V 2` 单形的远顶点与截断边不共线（HL :8280-8315
BARV_2_EXPLICIT + BARV_2_IMP_NOT_COLLINEAR_SET_OF_LIST 支的 Lean 直推导，
消费本文件 `barV2_imp_not_collinear_setOfList`）。 -/
private theorem p24_barV2_far_noncollinear (V : Set V3) (u0 u1 : V3) (vl : List V3) (n : V3)
    (hp : Packing V) (hbar : barV V 2 vl)
    (he : setOfList (truncateSimplex 1 vl) = {u0, u1}) (hn : n = elV vl 2) :
    ¬ Collinear3 u0 u1 n := by
  have h3 : vl.length = 2 + 1 := hbar.1
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, vl = [a, b, c] := by
    rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
    · simp at h3
    · simp at h3
    · simp at h3
    · exact ⟨a, b, c, rfl⟩
    · simp at h3
  have htr : truncateSimplex 1 [a, b, c] = [a, b] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 a b c c).2.1
  have h2' : setOfList [a, b] = {u0, u1} := by rw [← he, htr]
  have hmem : ∀ z : V3, z ∈ ({a, b} : Set V3) → z ∈ ({u0, u1} : Set V3) := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with hza | hzb
    · have hzin : a ∈ setOfList [a, b] := by simp [setOfList]
      rw [h2'] at hzin
      rw [hza]
      exact hzin
    · have hzin : b ∈ setOfList [a, b] := by simp [setOfList]
      rw [h2'] at hzin
      rw [hzb]
      exact hzin
  have hnc : ¬ Collinear ℝ (setOfList [a, b, c]) :=
    barV2_imp_not_collinear_setOfList V [a, b, c] hp hbar
  have hn' : n = c := hn.trans rfl
  intro hcol
  rw [hn'] at hcol
  refine hnc ?_
  have hsub : (setOfList [a, b, c]) ⊆ ({u0, u1, c} : Set V3) := by
    intro z hz
    simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · rcases hmem z (Or.inl rfl) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hmem z (Or.inr rfl) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr rfl)
  exact Collinear.subset hsub hcol

/-! ### D7 终墙（真证） -/

/-- D7 终墙（真证）：REUHADY 实例形 —— 锥帽体积正性 + 闭楔比例式。消费
CCV `volumeConicCapPos` 与本文件 `volumeConicCapWedgeGeVsConicCap`（HL
VOLUME_CONIC_CAP / VOLUME_CONIC_CAP_WEDGE_GE_VS_CONIC_CAP 的真证孪生）。 -/
private theorem p24_cap_wedge_vol (u0 u1 n1 n2 : V3) (r d : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hd1 : d < 1) (hne : u0 ≠ u1)
    (h1 : ¬ Collinear3 u0 u1 n1) (h2 : ¬ Collinear3 u0 u1 n2) :
    0 < volume.real (conicCapP24 u0 u1 r d) ∧
      volume.real (conicCapP24 u0 u1 r d ∩ wedgeGe u0 u1 n1 n2)
        = volume.real (conicCapP24 u0 u1 r d) * azim u0 u1 n1 n2 / (2 * Real.pi) :=
  ⟨volumeConicCapPos hr hd hd1 hne,
    volumeConicCapWedgeGeVsConicCap u0 u1 n1 n2 r d hd hd1 ⟨hr, hr1⟩ h1 h2⟩

/-! ### D1 走廊真证子件（2026-10-19 四发波，lane pa24reuhady；HL REUHADY.hl
345-1250 的三条独立移植）：(i) margin——平分面上的等距点，其中点近邻整部落进
对的 Voronoi 胞（HL :733-830 的 8-界分离 Lean 形；**等距条件不可省**——中点
球内非等距点不属两闭胞之交）；(ii) 锥走廊——严格锥 ∩ 单位球的点在 `[u0, y]`
线段上且 `y` 等距近中点（射线-等距面交点，倾角
b = ‖u0−u1‖/√(‖u0−u1‖²+4d²) 恰匹配 margin 的角容差）；(iii) 扇叶桥——走廊点
落在某叶表的 Rogers 单形内（hfan 抽叶 + ω₃ = 外心 + hull 并集恒等式）。 -/
/-- 中点到对点的距离（两对称形）。 -/
private theorem p24_midpair_dist (u0 u1 : V3) :
    dist (midpoint ℝ u0 u1) u0 = dist u0 u1 / 2
    ∧ dist (midpoint ℝ u0 u1) u1 = dist u0 u1 / 2 := by
  have h20 : (0:ℝ) < (2:ℝ) := by norm_num
  refine ⟨?_, ?_⟩
  · rw [dist_comm, dist_left_midpoint, Real.norm_eq_abs, abs_of_pos h20, inv_mul_eq_div]
  · rw [dist_comm, dist_right_midpoint, Real.norm_eq_abs, abs_of_pos h20, inv_mul_eq_div]

/-- D1(i) margin（HL REUHADY.hl :733-830）：`u0u1` 短棱（`dist < 2√2`）处，
平分面上的等距点其近中点邻域整部落进对的 Voronoi 胞。 -/
private theorem p24_vor_pair_margin (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hu01 : u0 ≠ u1)
    (h8 : dist u0 u1 < 2 * Real.sqrt 2) :
    ∃ d : ℝ, 0 < d ∧ ∀ x, dist x u0 = dist x u1 →
      dist x (midpoint ℝ u0 u1) ≤ d → x ∈ voronoiList V [u0, u1] := by
  have hd2 : 2 ≤ dist u0 u1 := by
    by_contra hlt
    exact hu01 (hp u0 hu0 u1 hu1 (not_le.1 hlt))
  obtain ⟨hdm0, hdm1⟩ := p24_midpair_dist u0 u1
  have hdms : dist (midpoint ℝ u0 u1) u0 < Real.sqrt 2 := by rw [hdm0]; linarith [h8]
  -- Apollonius（平行四边形恒等式）：第三包装点离中点 > √2
  have hapo : ∀ w ∈ V, w ≠ u0 → w ≠ u1 →
      Real.sqrt 2 < dist (midpoint ℝ u0 u1) w := by
    intro w hw hw0 hw1
    have ha : (2:ℝ) ≤ ‖w - u0‖ := by
      by_contra hlt
      have hlt' : dist w u0 < 2 := by rw [dist_eq_norm]; exact not_le.1 hlt
      exact hw0 (hp w hw u0 hu0 hlt')
    have hb : (2:ℝ) ≤ ‖w - u1‖ := by
      by_contra hlt
      have hlt' : dist w u1 < 2 := by rw [dist_eq_norm]; exact not_le.1 hlt
      exact hw1 (hp w hw u1 hu1 hlt')
    have hc : ‖u1 - u0‖ ^ 2 < 8 := by
      have h1 : ‖u1 - u0‖ = dist u0 u1 :=
        (dist_eq_norm u1 u0).symm.trans (dist_comm u1 u0)
      have hpos : (0:ℝ) ≤ ‖u1 - u0‖ := norm_nonneg _
      have h8' : ‖u1 - u0‖ < 2 * Real.sqrt 2 := by rw [h1]; exact h8
      have h8sq : (2 * Real.sqrt 2) ^ 2 = 8 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring
      nlinarith [h8', hpos, h8sq]
    have h2m : (2 : ℝ) • midpoint ℝ u0 u1 = u0 + u1 := by
      rw [midpoint, AffineMap.lineMap_apply_module', smul_add, smul_smul]
      have h21 : (2:ℝ) * ⅟(2:ℝ) = 1 := by norm_num
      rw [h21, one_smul, two_smul]
      abel
    have h2m' : (2 : ℝ) • (w - midpoint ℝ u0 u1) = (w - u0) + (w - u1) := by
      rw [smul_sub, h2m]; module
    have hA : ‖(w - u0) + (w - u1)‖ ^ 2 = 4 * ‖w - midpoint ℝ u0 u1‖ ^ 2 := by
      rw [← h2m', norm_smul, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < 2 by norm_num)]
      ring
    have hB : ‖u1 - u0‖ ^ 2 = ‖w - u0‖ ^ 2 - 2 * inner ℝ (w - u0) (w - u1)
        + ‖w - u1‖ ^ 2 := by
      have hns := norm_sub_sq_real (w - u0) (w - u1)
      rw [show ((w - u0) - (w - u1) : V3) = u1 - u0 from by abel] at hns
      exact hns
    have hC : ‖(w - u0) + (w - u1)‖ ^ 2 = ‖w - u0‖ ^ 2 + 2 * inner ℝ (w - u0) (w - u1)
        + ‖w - u1‖ ^ 2 := norm_add_sq_real _ _
    have ha2 : (4:ℝ) ≤ ‖w - u0‖ ^ 2 := by nlinarith [ha]
    have hb2 : (4:ℝ) ≤ ‖w - u1‖ ^ 2 := by nlinarith [hb]
    have hres : 2 < ‖w - midpoint ℝ u0 u1‖ ^ 2 := by linarith
    calc Real.sqrt 2 = Real.sqrt 2 := rfl
      _ < Real.sqrt (‖w - midpoint ℝ u0 u1‖ ^ 2) :=
            Real.sqrt_lt_sqrt (by norm_num) hres
      _ = dist (midpoint ℝ u0 u1) w := by
            rw [Real.sqrt_sq (norm_nonneg _)]
            exact ((dist_eq_norm w (midpoint ℝ u0 u1)).symm.trans
              (dist_comm w (midpoint ℝ u0 u1)))
  refine ⟨(Real.sqrt 2 - dist (midpoint ℝ u0 u1) u0) / 2, by linarith, ?_⟩
  intro x hxe hxm
  show x ∈ ⋂₀ {voronoiClosed V v | v ∈ (setOfList [u0, u1] : Set V3)}
  refine Set.mem_sInter.2 fun w hw => ?_
  obtain ⟨v, hv, rfl⟩ := hw
  simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false] at hv
  simp only [voronoiClosed, Set.mem_setOf_eq]
  rcases hv with hzv | hvz
  · rw [hzv]
    intro z hz
    rcases eq_or_ne z u0 with hz0 | hz0
    · rw [hz0]
    rcases eq_or_ne z u1 with hz1 | hz1
    · rw [hz1, hxe]
    · have hap := hapo z hz hz0 hz1
      have hup : dist x u0 ≤ dist x (midpoint ℝ u0 u1)
          + dist (midpoint ℝ u0 u1) u0 := dist_triangle x (midpoint ℝ u0 u1) u0
      have hlow : dist (midpoint ℝ u0 u1) z - dist x (midpoint ℝ u0 u1)
          ≤ dist x z := by
        have ht := dist_triangle (midpoint ℝ u0 u1) x z
        linarith [dist_comm x (midpoint ℝ u0 u1)]
      linarith
  · rw [hvz]
    intro z hz
    rcases eq_or_ne z u1 with hz1 | hz1
    · rw [hz1]
    rcases eq_or_ne z u0 with hz0 | hz0
    · rw [hz0, ← hxe]
    · have hap := hapo z hz hz0 hz1
      have hup : dist x u1 ≤ dist x (midpoint ℝ u0 u1)
          + dist (midpoint ℝ u0 u1) u1 := dist_triangle x (midpoint ℝ u0 u1) u1
      have hlow : dist (midpoint ℝ u0 u1) z - dist x (midpoint ℝ u0 u1)
          ≤ dist x z := by
        have ht := dist_triangle (midpoint ℝ u0 u1) x z
        linarith [dist_comm x (midpoint ℝ u0 u1)]
      linarith

/- D1(ii) 锥走廊（HL REUHADY.hl :1251-1530）——**本浪只留施工图，未落码**
（三次编译迭代未收敛，余量让位给 D1(i)/(iii)；完整初等证明如下，下一浪照抄
即得）：设 m = 中点、dm = dist(m,u0)、margin 参数 d > 0（(i) 的产出），
倾角 `b = ‖u0−u1‖/√(‖u0−u1‖²+4d²) ∈ (0,1)`（恒等式 `b²(dm²+d²) = dm²` 由
hb 平方 + d01 = 2·dm 圈闭）。对 `x ∈ rconeGt u0 u1 b ∩ ball(u0,1)`，x ≠ u0：
置 v = x − u0（t = ‖v‖ ∈ (0,1)）、`vdot = v ⬝ᵥ (u1−u0) > t·‖u0−u1‖·b > 0`
（Cauchy–Schwarz 给上界 vdot ≤ t·‖u0−u1‖），射线-等距面交点参数
`s = ‖u0−u1‖²/(2·vdot)`，y = u0 + s•v。五条事实（全部纯内积代数，本轮草稿
已推净）：(1) s ≥ 1：2·vdot ≤ 2·t·‖u0−u1‖ ≤ ‖u0−u1‖²（d01 ≥ 2）；(2) y 在
平分面：‖y−u1‖² = s²t² − 2·s·vdot + ‖u0−u1‖² = s²t²（s 的定义消去）；(3)
‖y−m‖² = s²t² − dm²（y−m = s•v − (u1−u0)/2，内积项 = d01²/4 = ‖m−u0‖²，
展开后相消）；(4) `b·(s·t) < dm`：等价于 s 的定义代入后恰为 hvx（vdot >
t·‖u0−u1‖·b）两端乘 ‖u0−u1‖；(5) 由 (3)+(4)+b²(dm²+d²) = dm²：
b²‖y−m‖² < b²d² ⟹ dist(y,m) < d。于是 y 等距（(2)）且近中点（(5)），
`hmargin` 给 y ∈ voronoiList V [u0,u1]；而 x = u0 + (1/s)•(y−u0)、
1/s ∈ [0,1]（(1)），即 `x ∈ convexHull ℝ {u0, y}`（convexHull_pair +
lineMap image）。∎Lean 落码时注意：`⅟2`/`2⁻¹` 形（midpoint 展开为
AffineMap.lineMap，用 lineMap_apply_module'）；hmargin 应用处的 dist_self
先 rw；hvx 从 rconeGt 成员提出时 dist u1 u0 与 dist u0 u1 需 dist_comm 对齐；
内积-点积转换用 `inner_eq_dot` 的 rw 形（ofLp 展开会破 syntactic rw）；
`mem_segment_iff` 在本 Mathlib 不存在，走 `convexHull_pair` + lineMap image。
-/

/- D1(iii) 扇叶桥（HL REUHADY.hl :1531-1629）——**本浪只留施工图，未落码**
（凸包并集塌缩 conv (insert u0 (conv S)) = conv (insert u0 S) 的
mono/antisymm 装配经三次编译迭代未收敛；完整路线：hy ∈ hfan 抽叶
⟨T, hT, hyT⟩ → ⟨vl, hbar, htr⟩（barV V 3 + truncate 1 = [u0,u1]）→
BARV_3_EXPLICIT 换表 [v0;v1;v2;v3]（v0 = u0 由 injection htr）→
p24_leaf_singleton 给 ω₃ = circumcenter (setOfList vl) →
x ∈ conv {u0, y} ⊆ conv (insert u0 (conv {ω₁,ω₂,cc})) = conv (insert u0
{ω₁,ω₂,cc})（conv-mono：{u0,y} ⊆ insert u0 (conv S) 与
S ⊆ insert u0 (conv S)（经 subset_convexHull ℝ S）两个方向，再
convHull_mono-antisymm；凸包并集塌缩 = 同法）→ 顶点集包含
insert u0 {ω₁,ω₂,cc} ⊆ ω-image{0..3}（ω₀ = v0 = u0、ω₃ = cc）→
convHull_mono 得 x ∈ rogers V vl。∎下一浪照抄；注意 `set S := ... with
hSdef` 的 let-fvar 会让 rw [hSdef] 与 mem_insert_iff 的 insert-结构展开失灵
——直接内联集合表达式；`mem_segment_iff` 不存在于本 Mathlib，走
convexHull_pair + lineMap image（AffineMap.lineMap_apply_module'）。-/

/-! ### scaffold 三 sorry（NEEDS 记账；三发波后残余债务 = scaffold 2/3 两条） -/
/-! ### scaffold 三 sorry（NEEDS 记账；三发波后残余债务 = scaffold 2/3 两条） -/
/-! ### scaffold 三 sorry（NEEDS 记账；三发波后残余债务 = scaffold 2/3 两条） -/

/-- NEEDS → CLOSED（2026-10-19 三发波，lane pa24reuhady）：scaffold 1/3，D6 成对
零交支；HL REUHADY.hl 7395-7470，核心 :7437 `i' = i ∧ mcell i' V ul' = mcell i V ul`。
楔族中两个不同胞的交为零体积。闭链：两楔族胞的胞参数 `(i, ul)` / `(i', ul')`
（`mcellSet` 给 barV V 3）若有正体积交，则 PA17 `AJRIPQN`（五阶段覆盖装配；帽石
2026-10-12 已闭 = `p17_ajripqn_of_tailfix` + SF-38 tail-fixed `QZKSYKG2`，其上游
PA13 `SLTSTLO2`/`DDZUPHJ`、PA10 `RVFXZBU`、PA14 `QZKSYKG1`/`QZKSYKG2` 语句在树而
体开放 = SF-20 shim 债）给出 `k = k' ∧ mcell k V ul = mcell k' V vl`，故 X = Y，
与 X ≠ Y 矛盾。Lean 侧比 HL 多一步归一化：本仓 `mcellSet`（PA2:368）不含
`i ≤ 4` 合取项（HOL `mcell_set` 亦然——两边的 i 有界性都由 `mcell` 的 if 链
`i > 3 ⇒ mcell4` 吸收），故先按 `mcell` 分派把任意指标折入 `{0,1,2,3,4}` 再施
AJRIPQN。import 拓扑（2026-10-19 验证并落地）：`import Kepler.Text.PackingAuto17`
进 PA24 无环（PA17 闭包 = PA2/5/6/7/8/10/11/12/13/14，不传递依赖 PA24；
Kepler.Text 顶层 def 不遮蔽本文件用名 wedge/dihV/azim/hl/wedgeGe）。
HL 侧同型论证的 `mcell_set_2`（两胞共边 ⇒ 交在公共仿射壳内共面零体积）在
Lean 侧不需要——AJRIPQN 对任意两胞直接给胞同一性，无需共边结构。 -/
private theorem p24_wedge_cells_pair_null (V : Set V3) (u0 u1 n1 n2 : V3) (e : Set V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (he : e = {u0, u1})
    (hnc1 : ¬ Collinear3 u0 u1 n1) (hnc2 : ¬ Collinear3 u0 u1 n2) :
    ∀ X ∈ p24_wedgeCells V u0 u1 n1 n2 e, ∀ Y ∈ p24_wedgeCells V u0 u1 n1 n2 e,
      X ≠ Y → volume (X ∩ Y) = 0 := by
  -- CLOSED (d)(ii)-pair via PA17 `AJRIPQN` (HL REUHADY.hl 7395-7470, :7437).
  intro X hX Y hY hXY
  obtain ⟨hmX, -, -⟩ := hX
  obtain ⟨hmY, -, -⟩ := hY
  obtain ⟨i, ul, rfl, hbarX⟩ := hmX
  obtain ⟨j, vl, rfl, hbarY⟩ := hmY
  -- `mcell` dispatch collapses every index into {0,1,2,3,4} (i > 3 ⇒ mcell4)
  have hnorm : ∀ (f : ℕ) (t : List V3), ∃ k, k ∈ ({0, 1, 2, 3, 4} : Set ℕ) ∧
      mcell k V t = mcell f V t := by
    intro f t
    rcases Nat.lt_or_ge f 4 with hf | hf
    · exact ⟨f, by simp; omega, rfl⟩
    · have hL : mcell 4 V t = mcell4 V t := by
        rw [mcell, if_neg (show (4:ℕ) ≠ 0 by decide), if_neg (show (4:ℕ) ≠ 1 by decide),
          if_neg (show (4:ℕ) ≠ 2 by decide), if_neg (show (4:ℕ) ≠ 3 by decide)]
      have hR : mcell f V t = mcell4 V t := by
        rw [mcell, if_neg (show (f:ℕ) ≠ 0 by omega), if_neg (show f ≠ 1 by omega),
          if_neg (show f ≠ 2 by omega), if_neg (show f ≠ 3 by omega)]
      exact ⟨4, by simp, by rw [hL, hR]⟩
  obtain ⟨k, hk, hki⟩ := hnorm i ul
  obtain ⟨k', hk', hkj⟩ := hnorm j vl
  by_contra hpos
  have hvol : ¬ nullSet (mcell k V ul ∩ mcell k' V vl) := by
    intro hcon
    rw [hki, hkj] at hcon
    exact hpos hcon
  have hij := AJRIPQN V ul vl k k' hs hp hbarX hbarY hk hk' hvol
  refine hXY ?_
  rw [← hki, ← hkj, hij.2]

/-- NEEDS（scaffold 2/3，D3+D4+D5 逐臂锥帽比例式；HL REUHADY.hl 2386-7358：
k=2 章 :2834-3562 / k≥4 章 :3908-5596 / k=3 章 :5627-7358 的
`vol (X ∩ D) = vol D · dihX V X (u0,u1) / (2π)`，junk 零侧 :8187-8241）。
分解：(α) junk 侧（nullSet 或 cellParamsD 首 ∈ {0,1}）双零——dihX 侧已由
`p24_dihX_of_nullSet` 与 `dihX` if-链定义性收口；vol 侧需 MCELL_EXPLICIT 的
mcell0/1 显式形 + {u0,u1,m,R} 共面零体积（COPLANAR_IMP_NEGLIGIBLE）。
(β) k′ ∈ {2,3,4} 侧：`p24_cellParamsD_spec`（已落）读出臂型，`p24_dihX_of_k3`/
`p24_dihX_of_k4`（已落）读出 dihX；vol 侧 = VOLUME_CONIC_CAP_WEDGE per 臂
（锥帽 ∩ aff_ge 楔片比例）+ mcell k′ 形状按 MCELL_EXPLICIT 分解 + 共面零体积修边；
其中 (d)(i) 的 k′-vs-k 识别（给定的楔族胞 X 的参数表 ul 与 fan 叶表 vl 的同一化，
PA17 `AJRIPQN` 刚性，见 scaffold 1 记账）与 fan-triple 胞非空性（HL :1476-1629）
也在本债内。消(side) 费件已全部在树：`volumeConicCapWedgeGeVsConicCap`（本文件
:1599）、`azim_dihv_same`/`azim_dihv_compl`（LuneVolume）、MCELL_EXPLICIT
（PA12:623）、`MEASURABLE_MCELL`（PA10:585）。 -/
private theorem p24_cell_cap_dihX (V : Set V3) (u0 u1 n1 n2 : V3) (e : Set V3) (X : Set V3)
    (r d : ℝ) (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (he : e = {u0, u1}) (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hd1 : d < 1)
    (hX : X ∈ p24_wedgeCells V u0 u1 n1 n2 e) :
    volume.real (conicCapP24 u0 u1 r d ∩ X)
      = volume.real (conicCapP24 u0 u1 r d) * dihX V X (u0, u1) / (2 * Real.pi) := by
  -- NEEDS (d)(i)+(ii)-bulk: see docstring. HL REUHADY.hl 2386-7358 + 8187-8241.
  sorry

/-- NEEDS（scaffold 3/3，D1+D2 走廊与覆盖；HL REUHADY.hl 345-2386，界标
"OK until here" :1250）：产出锥帽半径 `r d`（0 < r ≤ 1、0 < d < 1）并证覆盖
`cap ∩ wedgeGe ⊆ ⋃楔族胞`。HL 路线：S = voronoi_list V [u0;u1] 闭/仿射/有界
论证（:416-504）→ 内点 p = circumcenter、margin d、最近包装点 a'、8-界分离
（:733-830）→ C = ball(u0,1) ∩ rcone_gt(u0,u1,c) 内每点落某 `mcell i V ul`
（i ≤ 4、barV V 3、truncate 1 = [u0;u1]，:1531-1629；消费 PA6 `GLTVHUM`
闭 Voronoi 胞 = 根 u0 的 Rogers 单形并 + PA12 `MCELL_EXPLICIT`）→ e ∈ edgeX 由
truncate 结构 + heX 定楔侧 → P1/P2/P3 半径参数集 min-max 装配（:1705-2790）。
纯度量/凸性/覆盖，无测量论证，可独立移植（本车道下一浪首选）。 -/
private theorem p24_cap_wedge_cover (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3)
    (n1 n2 : V3) (e : Set V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) (he : e = {u0, u1})
    (hwedge : wedgeGe u0 u1 n1 n2 ∩ wedgeGe u0 u1 n2 n1 ⊆
      affGe {u0, u1} {n1} ∪ affGe {u0, u1} {n2})
    (haz : azim u0 u1 n1 n2 ≠ 0) (hvlne : vl1 ≠ vl2)
    (hhl1 : hl vl1 < Real.sqrt 2) (hhl2 : hl vl2 < Real.sqrt 2)
    (hbar1 : barV V 2 vl1) (hbar2 : barV V 2 vl2)
    (htr1 : setOfList (truncateSimplex 1 vl1) = e)
    (htr2 : setOfList (truncateSimplex 1 vl2) = e)
    (hn1 : n1 = elV vl1 2) (hn2 : n2 = elV vl2 2)
    (heX : ∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 n1 n2 ∨ X ⊆ wedgeGe u0 u1 n2 n1)
    (hbarV1 : barV V 1 [u0, u1])
    (hfan : voronoiList V [u0, u1] =
      ⋃₀ {convexHull ℝ {omegaListN V vl 1, omegaListN V vl 2,
        circumcenter (setOfList vl)} | vl ∈ {vl : List V3 |
        barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]}}) :
    ∃ r d : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < d ∧ d < 1 ∧
      ∀ x ∈ conicCapP24 u0 u1 r d ∩ wedgeGe u0 u1 n1 n2,
        x ∈ ⋃₀ p24_wedgeCells V u0 u1 n1 n2 e := by
  -- NEEDS (d)-cover/corridor: see docstring. HL REUHADY.hl 345-2386.
  -- 四发波（2026-10-19）推进：D1(i) margin 已真证落码（`p24_vor_pair_margin`，
  -- 等距点近中点球 ⊆ 对胞）；D1(ii) 锥走廊与 D1(iii) 扇叶桥留有完整施工图
  -- （见上方两则块注释，含全部中间事实与坑位记录）。闭链残余 =
  -- (ii)+(iii) 落码 + SLTSTLO1 逐叶分派 + edgeX 装配 + **楔侧指认 min-max**
  -- （HL :1705-2386 的 P1/P2/P3 半径集——轴与两边界方位平面同属
  -- W1 ∩ W2（hwedge），heX 二分对边界扇上的点不判定，须以半径 min-max
  -- 排除非本侧叶。此为 scaffold 3 的最后硬核，多会话量级）。
  sorry

/-! ### (d) 装配章（真证，零 sorry）：D6+D7 的家族求和恒等式 -/

/-- (d) 装配（真证）：楔族上 `dihX` 的 `setSum` = 边方位角。消费 D-FIN
（有限性）、scaffold 1-3（成对零交 / 逐胞比例式 / 覆盖）、D-WALL（终墙）、
D6 并集-求和桥与 `p24_setSum_congr`。HL 对应 = REUHADY.hl 7395-8356 的
家族章 + 终墙章；三 scaffold 收口后本件即 (d) 完整真证。 -/
private theorem p24_wedge_setSum_eq_azim (V : Set V3) (u0 u1 n1 n2 : V3) (e : Set V3)
    (r d : ℝ) (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hd1 : d < 1)
    (hnc1 : ¬ Collinear3 u0 u1 n1) (hnc2 : ¬ Collinear3 u0 u1 n2)
    (hfin : {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X}.Finite)
    (hpair : ∀ X ∈ p24_wedgeCells V u0 u1 n1 n2 e, ∀ Y ∈ p24_wedgeCells V u0 u1 n1 n2 e,
      X ≠ Y → volume (X ∩ Y) = 0)
    (hcov : ∀ x ∈ conicCapP24 u0 u1 r d ∩ wedgeGe u0 u1 n1 n2,
      x ∈ ⋃₀ p24_wedgeCells V u0 u1 n1 n2 e)
    (hcell : ∀ X ∈ p24_wedgeCells V u0 u1 n1 n2 e,
      volume.real (conicCapP24 u0 u1 r d ∩ X)
        = volume.real (conicCapP24 u0 u1 r d) * dihX V X (u0, u1) / (2 * Real.pi)) :
    setSum (p24_wedgeCells V u0 u1 n1 n2 e) (fun X => dihX V X (u0, u1))
      = azim u0 u1 n1 n2 := by
  classical
  set s : Set (Set V3) := p24_wedgeCells V u0 u1 n1 n2 e with hsdef
  -- D-FIN: the wedge family is finite (subset of the edge-cell family)
  have hsfin : s.Finite := hfin.subset (fun X hX => ⟨hX.1, hX.2.1⟩)
  -- measurability of the traces `X ∩ cap` (X is an mcell, cap is Borel)
  have hmeas : ∀ X ∈ s, MeasurableSet (X ∩ conicCapP24 u0 u1 r d) := by
    intro X hX
    obtain ⟨hm, -, -⟩ := hX
    obtain ⟨i, ul, rfl, hbar⟩ := hm
    exact (MEASURABLE_MCELL V ul i hs hp hbar).inter (measurableConicCap u0 u1 r d)
  -- traces have finite volume (they sit in the closed ball of radius r)
  have hnetop : ∀ X ∈ s, volume (X ∩ conicCapP24 u0 u1 r d) ≠ ⊤ := by
    intro X hX
    have hsub : X ∩ conicCapP24 u0 u1 r d ⊆ Metric.closedBall u0 r := fun z hz => hz.2.1
    have hlt : volume (Metric.closedBall u0 r) < ⊤ :=
      IsCompact.measure_lt_top (isCompact_closedBall u0 r)
    exact fun hcon =>
      absurd (lt_of_le_of_lt (measure_mono hsub) hlt)
        (by rw [hcon]; exact not_lt.mpr le_top)
  -- pairwise-null for the traces (subsets of the pairwise-null cell intersections)
  have hpair' : ∀ X ∈ s, ∀ Y ∈ s, X ≠ Y →
      volume ((X ∩ conicCapP24 u0 u1 r d) ∩ (Y ∩ conicCapP24 u0 u1 r d)) = 0 := by
    intro X hX Y hY hne
    exact measure_mono_null
      (fun z hz => ⟨hz.1.1, hz.2.1⟩ :
        (X ∩ conicCapP24 u0 u1 r d) ∩ (Y ∩ conicCapP24 u0 u1 r d) ⊆ X ∩ Y)
      (hpair X hX Y hY hne)
  -- the trace family's union is exactly `cap ∩ wedgeGe` (set identity + D-COVER)
  have huniteq : ⋃₀ ((fun X => X ∩ conicCapP24 u0 u1 r d) '' s)
      = conicCapP24 u0 u1 r d ∩ wedgeGe u0 u1 n1 n2 := by
    ext z
    constructor
    · rintro ⟨S, ⟨X, hX, rfl⟩, hz⟩
      obtain ⟨hz1, hz2⟩ : z ∈ X ∩ conicCapP24 u0 u1 r d := hz
      exact ⟨hz2, hX.2.2 hz1⟩
    · rintro ⟨hzc, hzw⟩
      obtain ⟨X, hX, hzX⟩ := hcov z ⟨hzc, hzw⟩
      exact ⟨X ∩ conicCapP24 u0 u1 r d, ⟨X, hX, rfl⟩, ⟨hzX, hzc⟩⟩
  -- D6 sum identity: sum of trace volumes = volume of the union = vol E
  have hsum : setSum s (fun X => volume.real (X ∩ conicCapP24 u0 u1 r d))
      = volume.real (conicCapP24 u0 u1 r d ∩ wedgeGe u0 u1 n1 n2) := by
    rw [p24_measure_setSum_biUnion hsfin hmeas hpair' hnetop, huniteq]
  -- D7 wall: vol E = vol D * azim / (2π), with vol D > 0
  have hwpos := p24_cap_wedge_vol u0 u1 n1 n2 r d hr hr1 hd hd1 hne hnc1 hnc2
  -- per-cell congruence + factorization
  have hc := p24_setSum_congr (s := s)
    (f := fun X : Set V3 => volume.real (X ∩ conicCapP24 u0 u1 r d))
    (g := fun X : Set V3 => volume.real (conicCapP24 u0 u1 r d)
      * dihX V X (u0, u1) / (2 * Real.pi))
    (fun X hX => by
      rw [Set.inter_comm]
      exact hcell X hX)
  have hfactor : setSum s (fun X => volume.real (conicCapP24 u0 u1 r d)
        * dihX V X (u0, u1) / (2 * Real.pi))
      = volume.real (conicCapP24 u0 u1 r d) / (2 * Real.pi)
        * setSum s (fun X => dihX V X (u0, u1)) := by
    unfold setSum
    simp only [dif_pos hsfin]
    calc ∑ a ∈ hsfin.toFinset,
          volume.real (conicCapP24 u0 u1 r d) * dihX V a (u0, u1) / (2 * Real.pi)
        = ∑ a ∈ hsfin.toFinset,
            volume.real (conicCapP24 u0 u1 r d) / (2 * Real.pi) * dihX V a (u0, u1) :=
          Finset.sum_congr rfl fun a _ => by ring
      _ = volume.real (conicCapP24 u0 u1 r d) / (2 * Real.pi)
            * ∑ a ∈ hsfin.toFinset, dihX V a (u0, u1) := (Finset.mul_sum _ _ _).symm
  have hkey : volume.real (conicCapP24 u0 u1 r d) / (2 * Real.pi)
      * setSum s (fun X => dihX V X (u0, u1))
      = volume.real (conicCapP24 u0 u1 r d) / (2 * Real.pi) * azim u0 u1 n1 n2 := by
    rw [← hfactor, ← hc, hsum, hwpos.2]
    ring
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  exact mul_left_cancel₀ (ne_of_gt (div_pos hwpos.1 h2pi)) hkey

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
    does this via MCELL_EXPLICIT + SET_TAC plumbing; PA21's genuine
    `MCELL_CELL_PARAMETERS_D_EXIST` kit shows the route but PA21 imports
    PA15/PA18, so it is NOT importable here — re-derive privately);
    (ii) the conic-cap/annulus measure argument around the edge —
    `vol (t ∩ E)` sums over the fan partitioning the azimuth wedge,
    `dihV = azim` conversion (`azim_dihv_same`/`azim_dihv_compl`,
    now imported from `Kepler.Geom.LuneVolume`), and the finite fan sum
    `∑ leaf dihX = azim u0 u1 n1 n2` (HL ~7000-8356: SUM_EQ +
    SUM_SUPERSET + measure sandwich). LANDED 2026-10-08 (all genuine,
    section above): the azim-additivity kit `p24_azim_base_shift` +
    `p24_wedge_ge_split` (PA18:3532/:3566 genuine twins, re-ported here
    since PA18 is not importable), the `setSum` final-assembly kit
    `p24_setSum_congr`/`p24_setSum_superset_eq`/`p24_setSum_union`
    (SUM_EQ/SUM_SUPERSET/SUM_UNION), and the (d)(i) `cell_params_d`
    front half `p24_cellParamsD_spec` + `dihX` read-offs
    `p24_dihX_of_k3`/`p24_dihX_of_k4` (PA21 wave-B1 first half,
    import-free). STILL OPEN: (i) the mcell4 realization (the `k'`
    identification with a given `k` — PA17 `AJRIPQN` rigidity, and the
    fan-triple cells' non-nullness) and (ii) the measure sandwich that
    identifies `∑ leaf dihX` with the azimuth split of `wedgeGe` (consume
    `p24_wedge_ge_split` + `p24_setSum_*` there); upstream sorried
    twins: PA7 `YIFVQDV_lemma_aff_dim` (PA7:854, ported sorry), PA15
    `HL_LE_SQRT2_IMP_BARV_1` (PA15:578, ported sorry — superseded here).
DOWNSTREAM (2026-09-30; shim split 2026-10-08): the two capstones
`REUHADY_p24` / `REUHADY_version2_p24` (below) are wired to this theorem
with every hypothesis synthesized genuinely (see the kit before the
capstone section); their remaining content is exactly `REUHADY1` + the
`p24_REUHADY_nondeg_azim` azimuth exclusion (2026-10-08 wave: that shim's
own residue is narrowed to two precisely-scoped facts — the pure-metric
exclusion `p24_nondeg_azim_ne` for `v1 ≠ v2` — GENUINE 2026-10-08/09: the coordinate
kit `p24_tri_data` + the strengthened `p24_tri_gamma` (γ-relation
`2wh = h² + t² − dt`) + disk/cone bounds + the final `dist v1 v2 < 2`
contradiction) and the non-flat-cell existence `p24_exists_mcell_not_flat`
for `v1 = v2` — GENUINE since the 2026-10-10..12 waves (branch assembly
`p24_caseB2_branch`; see its docstring). Both branches are wired into
`p24_REUHADY_nondeg_azim`, which is genuinely closed. The file's single
remaining `sorry` is THIS theorem's (d) body below (the dihedral-splitting
bulk). Statement (REUHADY_concl1_new) itself needs only PA2 defs,
no voronoi.

UPDATE 2026-10-19 (REUHADY1 二发波，lane pa24reuhady)：本体的单体黑箱 `sorry`
退役，改为真装配（下方 proof 体）＝ (a)(b)(c) 真证前置 + (d) 前置真证
`p24_barV2_far_noncollinear` + scaffold 3（`p24_cap_wedge_cover`，产出锥帽半径
r d 与覆盖）+ 真装配 `p24_wedge_setSum_eq_azim`（消费 D-FIN `p24_finite_edge_cells`
/ scaffold 1 `p24_wedge_cells_pair_null` / scaffold 2 `p24_cell_cap_dihX` /
D-WALL `p24_cap_wedge_vol` / D6 并集-求和桥）。残余 sorryAx 入口 = 恰好三个
scaffold，各自 docstring 记 HL 行段与闭链路径（施工图见 (d) 骨架章节头）。 -/
theorem REUHADY1 : REUHADY_concl1_new := by
  intro V u0 u1 vl1 vl2 n1 n2 e hs hp hu0 hu1 hne hhl he hwedge haz hvlne
    hhl1 hhl2 hbar1 hbar2 htr1 htr2 hn1 hn2 heX
  -- (a) genuine: the pair is barV V 1
  have hbarV1 : barV V 1 [u0, u1] := p24_barV1 V u0 u1 hp hu0 hu1 hne hhl
  -- (b)+(c) genuine: the pair voronoi list splits over the leaf triples
  have hfan := p24_voronoi_pair_split V u0 u1 hs hp hu0 hu1 hne hhl
  -- (d) genuinely derived: the far vertices are non-collinear with the edge
  have hnc1 : ¬ Collinear3 u0 u1 n1 :=
    p24_barV2_far_noncollinear V u0 u1 vl1 n1 hp hbar1 (htr1.trans he) hn1
  have hnc2 : ¬ Collinear3 u0 u1 n2 :=
    p24_barV2_far_noncollinear V u0 u1 vl2 n2 hp hbar2 (htr2.trans he) hn2
  -- (d) scaffold chapters (each NEEDS item is ledgered at its own docstring):
  -- cover/corridor (scaffold 3) produces the cone-cap radii r d
  obtain ⟨r, d, hr, hr1, hd, hd1, hcov⟩ :=
    p24_cap_wedge_cover V u0 u1 vl1 vl2 n1 n2 e hs hp hu0 hu1 hne hhl he hwedge haz
      hvlne hhl1 hhl2 hbar1 hbar2 htr1 htr2 hn1 hn2 heX hbarV1 hfan
  -- genuine assembly over the three scaffold chapters
  exact p24_wedge_setSum_eq_azim V u0 u1 n1 n2 e r d hs hp hu0 hu1 hne hr hr1 hd hd1
    hnc1 hnc2 (p24_finite_edge_cells V e u0 u1 hp hs he)
    (p24_wedge_cells_pair_null V u0 u1 n1 n2 e hs hp hu0 hu1 hne he hnc1 hnc2)
    hcov
    (fun X hX => p24_cell_cap_dihX V u0 u1 n1 n2 e X r d hs hp hu0 hu1 hne he
      hr hr1 hd hd1 hX)


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

/-- azim-零退化形态（2026-10-08 波，真证）：`azim u0 u1 v1 v2 = 0` 且
v1、v2 均离轴时，v1、v2 同侧同射线（`azim_eq_zero_iff` + `p24_affGt_swap`
换向），两枚闭楔同时塌进边界闭半平面之并 `aff_ge {u0,u1} {v1} ∪
aff_ge {u0,u1} {v2}`（`p24_azim_zero_affGe`）。nondeg 排除的对照面：此时
mcell 析取假设把棱 `e` 上全部胞压进一张平坦半平面。 -/
private theorem p24_wedgeGe_flat_subset (u0 u1 v1 v2 : V3)
    (h1 : ¬ Collinear3 u0 u1 v1) (h2 : ¬ Collinear3 u0 u1 v2)
    (h0 : azim u0 u1 v1 v2 = 0) :
    wedgeGe u0 u1 v1 v2 ⊆ affGe ({u0, u1} : Set V3) ({v1} : Set V3) ∪
      affGe ({u0, u1} : Set V3) ({v2} : Set V3) ∧
    wedgeGe u0 u1 v2 v1 ⊆ affGe ({u0, u1} : Set V3) ({v1} : Set V3) ∪
      affGe ({u0, u1} : Set V3) ({v2} : Set V3) := by
  have hv1u0 : v1 ≠ u0 := fun he => h1 (collinear3_pair_left he)
  have hv1u1 : v1 ≠ u1 := fun he => h1 (collinear3_pair_right he)
  have hv2u0 : v2 ≠ u0 := fun he => h2 (collinear3_pair_left he)
  have hv2u1 : v2 ≠ u1 := fun he => h2 (collinear3_pair_right he)
  have hpair : u0 ≠ u1 := fun he => h1 (collinear3_of_eq he.symm)
  have hv12 : v1 ∈ affGt ({u0, u1} : Set V3) ({v2} : Set V3) :=
    (azim_eq_zero_iff h1 h2).mp h0
  have hv21 : v2 ∈ affGt ({u0, u1} : Set V3) ({v1} : Set V3) :=
    p24_affGt_swap (v0 := u0) (v1 := u1) hpair hv1u0 hv1u1 hv2u0 hv2u1 hv12
  have haz21 : azim u0 u1 v2 v1 = 0 := (azim_eq_zero_iff h2 h1).mpr hv21
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [wedgeGe, Set.mem_setOf_eq] at hz
    refine Set.mem_union_left _ (p24_azim_zero_affGe h1 ?_)
    exact le_antisymm (h0 ▸ hz.2) (azim_nonneg u0 u1 v1 z)
  · rw [wedgeGe, Set.mem_setOf_eq] at hz
    refine Set.mem_union_right _ (p24_azim_zero_affGe h2 ?_)
    exact le_antisymm (haz21 ▸ hz.2) (azim_nonneg u0 u1 v2 z)

/-! ## `p24_REUHADY_nondeg_azim` 的纯度量排除工具群（2026-10-08 波，全部真证）

`p24_REUHADY_nondeg_azim` 的 `v1 ≠ v2` 支归约为纯度量事实：饱和 packing 的
短棱 `u0u1`（`2 ≤ dist < √8`）上两个 `V`-三角形 `[u0,u1,v_i]`（外接半径
`< √2`，即 `hl < √2`）不可能 `azim u0 u1 v1 v2 = 0` 而 `v1 ≠ v2`——azim = 0
把 `v1,v2` 压到轴的同一垂线上（`azim_eq_zero_iff` + `affGt_pair_iff`）；
外心（`p24_circumcenter_exists` + `p24_radV_extract` 的 `ε`-提取）经
`p24_tri_data` 给出坐标数据 `(h_i, t_i, γ_i)`；`p24_tri_bound` 由 `ρ < √2`
+ packing `≥ 2` 推出圆盘界 `(h_i − β)² + s_i² < 2` 与锥形界
`2β(h_i − β) > d|s_i|`（`β = √(2 − d²/4)`，`s_i = t_i − d/2`）；两者拼合
（圆心 `q` = 中点沿垂线上移 `β`）得 `dist v1 v2 < 2`，与 packing 矛盾。
剩余工作（下波）：主装配 `p24_nondeg_azim_ne` 的最终拼装（约 40 行）与
`v1 = v2` 支的非平坦胞存在性 `p24_exists_mcell_not_flat`。 -/

private theorem p24_zeta_add (a b : V3) (x y : V3) :
    zOf a b (x + y) = zOf a b x + zOf a b y := by
  have h1 : zOf a b (x + y)
      = Complex.ofReal ((x + y : V3) ⬝ᵥ a)
        + Complex.ofReal ((x + y : V3) ⬝ᵥ b) * Complex.I := rfl
  have h2 : zOf a b x
      = Complex.ofReal (x ⬝ᵥ a) + Complex.ofReal (x ⬝ᵥ b) * Complex.I := rfl
  have h3 : zOf a b y
      = Complex.ofReal (y ⬝ᵥ a) + Complex.ofReal (y ⬝ᵥ b) * Complex.I := rfl
  rw [h1, h2, h3, WithLp.ofLp_add, add_dotProduct, add_dotProduct,
    Complex.ofReal_add, Complex.ofReal_add]
  ring

private theorem p24_zeta_sub (a b : V3) (x y : V3) :
    zOf a b (x - y) = zOf a b x - zOf a b y := by
  have h1 : zOf a b (x - y)
      = Complex.ofReal ((x - y : V3) ⬝ᵥ a)
        + Complex.ofReal ((x - y : V3) ⬝ᵥ b) * Complex.I := rfl
  have h2 : zOf a b x
      = Complex.ofReal (x ⬝ᵥ a) + Complex.ofReal (x ⬝ᵥ b) * Complex.I := rfl
  have h3 : zOf a b y
      = Complex.ofReal (y ⬝ᵥ a) + Complex.ofReal (y ⬝ᵥ b) * Complex.I := rfl
  rw [h1, h2, h3]
  simp only [WithLp.ofLp_sub, sub_dotProduct, dotProduct_sub, Complex.ofReal_sub]
  ring

private theorem p24_zeta_smul (a b : V3) (r : ℝ) (x : V3) :
    zOf a b (r • x) = (r : ℂ) * zOf a b x := by
  have h1 : zOf a b (r • x)
      = Complex.ofReal ((r • x : V3) ⬝ᵥ a)
        + Complex.ofReal ((r • x : V3) ⬝ᵥ b) * Complex.I := rfl
  have h2 : zOf a b x
      = Complex.ofReal (x ⬝ᵥ a) + Complex.ofReal (x ⬝ᵥ b) * Complex.I := rfl
  rw [h1, h2]
  simp only [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, Complex.ofReal_mul]
  ring

private theorem p24_norm_e3 {e1 e2 e3 : V3} (hon : Orthonormal3 e1 e2 e3) : ‖e3‖ = 1 := by
  have h33 : e3 ⬝ᵥ e3 = 1 := hon.2.2.1
  have h : ‖e3‖ ^ 2 = 1 := by rw [norm_sq_eq_dot e3]; exact h33
  nlinarith [norm_nonneg e3]

private theorem p24_zeta_e3 {e1 e2 e3 : V3} (hon : Orthonormal3 e1 e2 e3) :
    zOf e1 e2 e3 = 0 := by
  obtain ⟨h11, h22, h33, h12, h13, h23, -⟩ := hon
  have k13 : e3 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact h13
  have k23 : e3 ⬝ᵥ e2 = 0 := by rw [dotProduct_comm]; exact h23
  simp only [zOf, k13, k23, Complex.ofReal_zero]
  ring

private theorem p24_norm_sq_decomp {e1 e2 e3 : V3} (hon : Orthonormal3 e1 e2 e3) (z : V3) :
    ‖z‖ ^ 2 = (z ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 z‖ ^ 2 := by
  have hon' := hon
  obtain ⟨h11, h22, h33, h12, h13, h23, -⟩ := hon'
  have hzeta : ‖zOf e1 e2 z‖ ^ 2 = (z ⬝ᵥ e1) ^ 2 + (z ⬝ᵥ e2) ^ 2 := by
    have hz' : zOf e1 e2 z
        = Complex.ofReal (z ⬝ᵥ e1) + Complex.ofReal (z ⬝ᵥ e2) * Complex.I := rfl
    rw [hz', Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    simp
    ring
  have hz : ‖z‖ ^ 2 = (z ⬝ᵥ e1) ^ 2 + (z ⬝ᵥ e2) ^ 2 + (z ⬝ᵥ e3) ^ 2 := by
    have hnorm : ‖z‖ ^ 2 = z ⬝ᵥ z := norm_sq_eq_dot z
    have k12 : e2 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact h12
    have k13 : e3 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact h13
    have k23 : e3 ⬝ᵥ e2 = 0 := by rw [dotProduct_comm]; exact h23
    conv_lhs => rw [hnorm, on3_expand hon z]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, h11, h22, h33, h12, h13, h23,
      k12, k13, k23]
    ring
  linarith [hz, hzeta]

private theorem p24_zeta_axis_eq {e1 e2 e3 : V3} (hon : Orthonormal3 e1 e2 e3) {x y : V3}
    (hz : zOf e1 e2 x = zOf e1 e2 y) (ha : x ⬝ᵥ e3 = y ⬝ᵥ e3) : x = y := by
  have hd : x - y = 0 := by
    have hn : ‖x - y‖ ^ 2 = 0 := by
      rw [p24_norm_sq_decomp hon]
      have a1 : (x - y : V3) ⬝ᵥ e3 = 0 := by
        simp only [WithLp.ofLp_sub, sub_dotProduct, ha]
        ring
      have a2 : zOf e1 e2 (x - y) = 0 := by
        rw [p24_zeta_sub, hz]
        ring
      rw [a1, a2]
      simp
    have h1 : ‖x - y‖ = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hn
    exact norm_eq_zero.mp h1
  exact sub_eq_zero.mp hd

private theorem p24_norm_sq_of_orth {x y : V3} (h : x ⬝ᵥ y = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h1 : ‖x‖ ^ 2 = x ⬝ᵥ x := norm_sq_eq_dot x
  have h2 : ‖y‖ ^ 2 = y ⬝ᵥ y := norm_sq_eq_dot y
  have h' : y ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact h
  rw [norm_sq_eq_dot (x + y), h1, h2]
  simp only [WithLp.ofLp_add, dotProduct_add, add_dotProduct, h, h',
    WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- ON 标架下：内积的复分解。 -/
private theorem p24_dot_eq {e1 e2 e3 : V3} (hon : Orthonormal3 e1 e2 e3) (x y : V3) :
    x ⬝ᵥ y = Complex.re (zOf e1 e2 x * (starRingEnd ℂ) (zOf e1 e2 y))
      + (x ⬝ᵥ e3) * (y ⬝ᵥ e3) := by
  have hon' := hon
  obtain ⟨h11, h22, h33, h12, h13, h23, -⟩ := hon'
  have k12 : e2 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact hon.2.2.2.1
  have k13 : e3 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact hon.2.2.2.2.1
  have k23 : e3 ⬝ᵥ e2 = 0 := by rw [dotProduct_comm]; exact hon.2.2.2.2.2.1
  have hd : x ⬝ᵥ y = ((x ⬝ᵥ e1) • e1 + (x ⬝ᵥ e2) • e2 + (x ⬝ᵥ e3) • e3) ⬝ᵥ
      ((y ⬝ᵥ e1) • e1 + (y ⬝ᵥ e2) • e2 + (y ⬝ᵥ e3) • e3) := by
    conv_lhs =>
      rw [on3_expand hon x]
      arg 2
      rw [on3_expand hon y]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul]
  rw [hd]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, h11, h22, h33, h12, h13, h23,
    k12, k13, k23]
  have hre : Complex.re (zOf e1 e2 x * (starRingEnd ℂ) (zOf e1 e2 y))
      = (x ⬝ᵥ e1) * (y ⬝ᵥ e1) + (x ⬝ᵥ e2) * (y ⬝ᵥ e2) := by
    have hx' : zOf e1 e2 x
        = Complex.ofReal (x ⬝ᵥ e1) + Complex.ofReal (x ⬝ᵥ e2) * Complex.I := rfl
    have hy' : zOf e1 e2 y
        = Complex.ofReal (y ⬝ᵥ e1) + Complex.ofReal (y ⬝ᵥ e2) * Complex.I := rfl
    rw [hx', hy', Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    simp
  rw [hre]
  ring

/-- 距离平方相等的点积读出：`‖y‖² = ‖y − z‖² → 2 y⬝z = ‖z‖²`。 -/
private theorem p24_sq_eq_doteq {y z : V3} (h : ‖y‖ ^ 2 = ‖y - z‖ ^ 2) :
    2 * (y ⬝ᵥ z) = ‖z‖ ^ 2 := by
  have q : ‖y - z‖ ^ 2 = ‖y‖ ^ 2 - 2 * (y ⬝ᵥ z) + ‖z‖ ^ 2 := by
    have q0 : ‖y - z‖ ^ 2 = (y - z) ⬝ᵥ (y - z) := norm_sq_eq_dot _
    rw [q0]
    simp only [WithLp.ofLp_sub, sub_dotProduct, dotProduct_sub,
      ← norm_sq_eq_dot y, ← norm_sq_eq_dot z]
    rw [dotProduct_comm]
    ring
  linarith

private theorem p24_affspan_dir {x v u z : V3}
    (hz : z ∈ (affineSpan ℝ ({x, v, u} : Set V3))) :
    (z - x : V3) ∈ Submodule.span ℝ ({v - x, u - x} : Set V3) := by
  have hdir : (affineSpan ℝ ({x, v, u} : Set V3)).direction
      = Submodule.span ℝ ({v - x, u - x} : Set V3) := by
    rw [direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right ℝ (show x ∈ ({x, v, u} : Set V3) from by simp)]
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
  rw [← hdir]
  exact AffineSubspace.vsub_mem_direction (k := ℝ) hz
    (mem_affineSpan (k := ℝ) (by simp))

/-! ### 外心存在性（非退化三点组） -/

private theorem p24_cc_exists (a b c : V3) (hab : a ≠ b) (hnc : ¬ Collinear3 a b c) :
    ∃ p : V3, p ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) ∧
      ∃ ρ : ℝ, ∀ w ∈ ({a, b, c} : Set V3), ρ = dist p w := by
  obtain ⟨e1, e2, e3, hon, hax⟩ := exists_on3_eq_smul (b - a) (sub_ne_zero.mpr (Ne.symm hab))
  have haxd : (b - a : V3) = dist a b • e3 := by
    have hn : ‖b - a‖ = dist a b := (dist_eq_norm b a).symm.trans (dist_comm b a)
    rw [hn] at hax
    exact hax
  have h33 : e3 ⬝ᵥ e3 = 1 := hon.2.2.1
  set d := dist a b with hddef
  have hd0 : 0 < d := dist_pos.mpr hab
  set t := (c - a) ⬝ᵥ e3 with htdef
  set perp := (c - a) - t • e3 with hpdef
  have hpperp : perp ⬝ᵥ e3 = 0 := by
    rw [hpdef, htdef]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct, h33]
    ring
  have hph : 0 < ‖perp‖ := by
    by_contra hcon
    have h0 : ‖perp‖ ≤ 0 := le_of_not_gt hcon
    have h0' : perp = 0 := norm_eq_zero.mp (le_antisymm h0 (norm_nonneg perp))
    have hdne : d ≠ 0 := ne_of_gt hd0
    have hrep : (c - a : V3) = (t / d) • (b - a) := by
      have h1 : (c - a : V3) = perp + t • e3 := by rw [hpdef]; module
      rw [h1, haxd, h0', zero_add, smul_smul, div_mul_cancel₀ _ hdne]
    exact hnc ((collinear3_iff_smul (Ne.symm hab)).mpr ⟨t / d, hrep⟩)
  have hpsq : ‖perp‖ ^ 2 = perp ⬝ᵥ perp := norm_sq_eq_dot perp
  set γ := (t ^ 2 - d * t + ‖perp‖ ^ 2) / (2 * ‖perp‖ ^ 2) with hγdef
  set p : V3 := a + (1 / 2 : ℝ) • (b - a) + γ • perp with hpdef2
  refine ⟨p, ?_, Real.sqrt (d ^ 2 / 4 + γ ^ 2 * ‖perp‖ ^ 2), fun w hw => ?_⟩
  · have hscal : ((1 / 2 : ℝ) - γ * (t / d)) * d = d / 2 - γ * t := by
      field_simp
    have hrep : p = a + ((1 / 2 : ℝ) - γ * (t / d)) • (b - a) + γ • (c - a) := by
      rw [hpdef2, hpdef, haxd, smul_smul, smul_smul, hscal]
      module
    exact p24_mem_affineSpan_triple a b c p _ _ hrep
  · rw [dist_eq_norm]
    have hpe : e3 ⬝ᵥ perp = 0 := by rw [dotProduct_comm]; exact hpperp
    have hsmot : ∀ r s : ℝ, ((r : ℝ) • e3) ⬝ᵥ ((s : ℝ) • perp) = 0 := by
      intro r s
      simp only [WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        hpe]
      ring
    have he3n : ∀ r : ℝ, ‖((r : ℝ) • e3 : V3)‖ ^ 2 = r ^ 2 := by
      intro r
      have h0 : ‖((r : ℝ) • e3 : V3)‖ ^ 2 = ((r : ℝ) • e3 : V3) ⬝ᵥ ((r : ℝ) • e3 : V3) :=
        norm_sq_eq_dot _
      simp only [h0, WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        h33]
      ring
    have hp2n : ∀ s : ℝ, ‖((s : ℝ) • perp : V3)‖ ^ 2 = s ^ 2 * ‖perp‖ ^ 2 := by
      intro s
      have h0 : ‖((s : ℝ) • perp : V3)‖ ^ 2
          = ((s : ℝ) • perp : V3) ⬝ᵥ ((s : ℝ) • perp : V3) := norm_sq_eq_dot _
      simp only [h0, WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        hpsq]
      ring
    have hx : p - a = (d / 2) • e3 + γ • perp := by
      have h1 : p - a = (1 / 2 : ℝ) • (b - a) + γ • perp := by rw [hpdef2]; module
      rw [h1, haxd, smul_smul, show (1 : ℝ) / 2 * d = d / 2 from by ring]
    have hxb : p - b = (-(d / 2)) • e3 + γ • perp := by
      have h1 : p - b = (p - a) - (b - a) := by module
      rw [h1, hx, haxd]
      module
    have hxc : p - c = (d / 2 - t) • e3 + (γ - 1) • perp := by
      have h1 : p - c = (p - a) - (c - a) := by module
      have h2 : (c - a : V3) = t • e3 + perp := by rw [hpdef]; module
      rw [h1, hx, h2]
      module
    have hna : ‖p - a‖ ^ 2 = d ^ 2 / 4 + γ ^ 2 * ‖perp‖ ^ 2 := by
      have hsplit := p24_norm_sq_of_orth (x := ((d / 2 : ℝ) • e3)) (y := ((γ : ℝ) • perp))
        (hsmot (d / 2) γ)
      rw [he3n (d / 2), hp2n γ] at hsplit
      rw [hx]
      linarith [hsplit]
    have hnb : ‖p - b‖ ^ 2 = d ^ 2 / 4 + γ ^ 2 * ‖perp‖ ^ 2 := by
      have hsplit := p24_norm_sq_of_orth (x := ((-(d / 2) : ℝ) • e3)) (y := ((γ : ℝ) • perp))
        (hsmot (-(d / 2)) γ)
      rw [he3n (-(d / 2)), hp2n γ] at hsplit
      rw [show ((-(d / 2) : ℝ)) ^ 2 = d ^ 2 / 4 from by ring] at hsplit
      rw [hxb]
      linarith [hsplit]
    have hnc2 : ‖p - c‖ ^ 2 = d ^ 2 / 4 + γ ^ 2 * ‖perp‖ ^ 2 := by
      have hsplit := p24_norm_sq_of_orth
        (x := (((d / 2 - t : ℝ)) • e3)) (y := (((γ - 1 : ℝ)) • perp))
        (hsmot (d / 2 - t) (γ - 1))
      rw [he3n (d / 2 - t), hp2n (γ - 1)] at hsplit
      rw [hxc]
      have e1 : (d / 2 - t) ^ 2 = d ^ 2 / 4 - d * t + t ^ 2 := by ring
      have e2 : ((γ - 1 : ℝ)) ^ 2 * ‖perp‖ ^ 2
          = γ ^ 2 * ‖perp‖ ^ 2 - 2 * γ * ‖perp‖ ^ 2 + ‖perp‖ ^ 2 := by ring
      have key : 2 * γ * ‖perp‖ ^ 2 = t ^ 2 - d * t + ‖perp‖ ^ 2 := by
        rw [hγdef]
        field_simp [show ‖perp‖ ≠ 0 from ne_of_gt hph]
      rw [e1, e2, key] at hsplit
      linarith [hsplit]
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact (Real.sqrt_eq_iff_eq_sq (by positivity) (norm_nonneg _)).mpr hna.symm
    · rcases Set.mem_insert_iff.mp hw with rfl | hw
      · exact (Real.sqrt_eq_iff_eq_sq (by positivity) (norm_nonneg _)).mpr hnb.symm
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        exact (Real.sqrt_eq_iff_eq_sq (by positivity) (norm_nonneg _)).mpr hnc2.symm

/-! ### `radV` 的含义提取 -/

private theorem p24_radV_extract {S : Set V3}
    (hex : ∃ p : V3, p ∈ (affineSpan ℝ S : Set V3) ∧ ∃ ρ : ℝ, ∀ w ∈ S, ρ = dist p w) :
    (circumcenter S) ∈ (affineSpan ℝ S : Set V3) ∧
      ∀ w ∈ S, radV S = dist (circumcenter S) w := by
  obtain ⟨hccA, ρ0, hρ0⟩ := Classical.epsilon_spec
    (p := fun v : V3 => v ∈ (affineSpan ℝ S : Set V3) ∧ ∃ ρ : ℝ, ∀ w ∈ S, ρ = dist v w) hex
  refine ⟨hccA, fun w hw => ?_⟩
  exact Classical.epsilon_spec
    (p := fun ρ : ℝ => ∀ w ∈ S, ρ = dist (circumcenter S) w) ⟨ρ0, hρ0⟩ w hw

/-! ### 三角形坐标数据提取 -/

private theorem p24_tri_data (u0 u1 v : V3) {e1 e2 e3 : V3} (hon : Orthonormal3 e1 e2 e3)
    (hax : (u1 - u0 : V3) = dist u0 u1 • e3) (hu01 : u0 ≠ u1)
    (hnc : ¬ Collinear3 u0 u1 v)
    (hex : ∃ p : V3, p ∈ (affineSpan ℝ ({u0, u1, v} : Set V3) : Set V3) ∧
      ∃ ρ : ℝ, ∀ w ∈ ({u0, u1, v} : Set V3), ρ = dist p w) :
    ∃ h t γ : ℝ, 0 < h ∧ ‖zOf e1 e2 (v - u0)‖ = h ∧
      radV ({u0, u1, v} : Set V3) ^ 2 = dist u0 u1 ^ 2 / 4 + (γ * h) ^ 2 := by
  obtain ⟨hccP, hrad⟩ := p24_radV_extract hex
  set CC := circumcenter ({u0, u1, v} : Set V3) with hCCdef
  obtain ⟨α, γ, hrep⟩ := Submodule.mem_span_pair.mp (p24_affspan_dir hccP)
  have hax' : (u1 - u0 : V3) = dist u1 u0 • e3 := by rw [dist_comm u1 u0]; exact hax
  have hζ0 : zOf e1 e2 (v - u0) ≠ 0 := (zOf_ne_zero_iff hon hax' hu01.symm v).mpr hnc
  have hζy : zOf e1 e2 (CC - u0) = (γ : ℂ) * zOf e1 e2 (v - u0) := by
    rw [← hrep, p24_zeta_add, p24_zeta_smul, p24_zeta_smul,
      show zOf e1 e2 (u1 - u0) = 0 from by
        rw [hax, p24_zeta_smul, p24_zeta_e3 hon]; ring]
    ring
  have hd0 : 0 < dist u0 u1 := dist_pos.mpr hu01
  have hdu0 : dist CC u0 = dist CC u1 := (hrad u0 (by simp)).symm.trans (hrad u1 (by simp))
  have hd3 : ‖(dist u0 u1 • e3 : V3)‖ ^ 2 = dist u0 u1 ^ 2 := by
    have h1 : ‖(dist u0 u1 • e3 : V3)‖ = dist u0 u1 * ‖e3‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hd0)]
    rw [h1, p24_norm_e3 hon]
    simp
  have haxis : (CC - u0 : V3) ⬝ᵥ e3 = dist u0 u1 / 2 := by
    have e0 : (CC - u0 : V3) - dist u0 u1 • e3 = CC - u1 := by rw [← hax]; module
    have h1 : ‖CC - u0‖ ^ 2 = ‖CC - u1‖ ^ 2 := by
      rw [← dist_eq_norm CC u1, ← hdu0, ← dist_eq_norm]
    have h2 := p24_sq_eq_doteq (y := (CC - u0 : V3)) (z := (dist u0 u1 • e3 : V3))
      (by rw [e0]; exact h1)
    have hsmul : (CC - u0 : V3) ⬝ᵥ ((dist u0 u1 • e3 : V3))
        = dist u0 u1 * ((CC - u0 : V3) ⬝ᵥ e3) := by
      rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul]
    rw [hsmul, hd3] at h2
    have hd0' : (dist u0 u1 : ℝ) ≠ 0 := ne_of_gt hd0
    refine mul_left_cancel₀ hd0' ?_
    linarith
  have hdv : dist CC u0 = dist CC v := (hrad u0 (by simp)).symm.trans (hrad v (by simp))
  -- 等距关系：2 (CC − u0) ⬝ᵥ (v − u0) = ‖v − u0‖²
  have hmid : 2 * ((CC - u0 : V3) ⬝ᵥ (v - u0)) = ‖v - u0‖ ^ 2 := by
    have e0 : (CC - u0 : V3) - (v - u0) = CC - v := by module
    have h1 : ‖CC - u0‖ ^ 2 = ‖CC - v‖ ^ 2 := by
      rw [← dist_eq_norm CC v, ← hdv, ← dist_eq_norm]
    have h2 := p24_sq_eq_doteq (y := (CC - u0 : V3)) (z := (v - u0 : V3))
      (by rw [e0]; exact h1)
    exact h2
  -- 实/虚部抽取（zOf 的坐标语义）
  have hreE : ∀ z : V3, Complex.re (zOf e1 e2 z) = z ⬝ᵥ e1 := by
    intro z
    simp only [zOf, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    simp
  have himE : ∀ z : V3, Complex.im (zOf e1 e2 z) = z ⬝ᵥ e2 := by
    intro z
    simp only [zOf, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
      Complex.I_im]
    simp
  -- γ 系数（hζy 的 re/im 分量）
  have hcoef1 : (CC - u0 : V3) ⬝ᵥ e1 = γ * ((v - u0 : V3) ⬝ᵥ e1) := by
    have hre1 := hreE (CC - u0)
    rw [hζy, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hreE, himE] at hre1
    linarith
  have hcoef2 : (CC - u0 : V3) ⬝ᵥ e2 = γ * ((v - u0 : V3) ⬝ᵥ e2) := by
    have him1 := himE (CC - u0)
    rw [hζy, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, himE, hreE] at him1
    linarith
  have hreN : ((Complex.normSq (zOf e1 e2 (v - u0)) : ℂ)).re
      = Complex.normSq (zOf e1 e2 (v - u0)) := rfl
  have hz0 : (0:ℝ) * ((Complex.normSq (zOf e1 e2 (v - u0)) : ℂ).im) = 0 := by ring
  have hnsqv : ‖zOf e1 e2 (v - u0)‖ ^ 2 = Complex.normSq (zOf e1 e2 (v - u0)) :=
    Complex.sq_norm (zOf e1 e2 (v - u0))
  refine ⟨‖zOf e1 e2 (v - u0)‖, (v - u0 : V3) ⬝ᵥ e3, γ, norm_pos_iff.mpr hζ0, rfl, ?_⟩
  · -- radV² 分解：ρ² = d²/4 + (γh)²
    have hρ := hrad u0 (by simp)
    have hnsqCC : Complex.normSq (zOf e1 e2 (CC - u0))
        = γ ^ 2 * Complex.normSq (zOf e1 e2 (v - u0)) := by
      have hd1 : Complex.normSq (zOf e1 e2 (CC - u0))
          = ((CC - u0 : V3) ⬝ᵥ e1) ^ 2 + ((CC - u0 : V3) ⬝ᵥ e2) ^ 2 := by
        rw [Complex.normSq_apply, hreE, himE]
        ring
      have hd2 : Complex.normSq (zOf e1 e2 (v - u0))
          = ((v - u0 : V3) ⬝ᵥ e1) ^ 2 + ((v - u0 : V3) ⬝ᵥ e2) ^ 2 := by
        rw [Complex.normSq_apply, hreE, himE]
        ring
      rw [hd1, hcoef1, hcoef2, mul_pow, mul_pow]
      rw [← mul_add, ← hd2]
    rw [hρ, dist_eq_norm, p24_norm_sq_decomp hon (CC - u0), haxis, Complex.sq_norm,
      hnsqCC, mul_pow, Complex.sq_norm]
    ring
  -- NEEDS（下波）：2γh² = h² + t² − d·t 关系（等距 + ζ 比例 + haxis 的最终
  -- 消元；本件上方 hmid/hζy/hcoef*/hnsqCC 已给出全部输入）。
  -- 该关系为下游 `p24_nondeg_azim_ne`（主装配）所需。
  -- （2026-10-08/09 波：该关系已在下方 `p24_tri_gamma` 中以 `w = γ·h` 的
  -- 合并形态 `2*w*h = h² + t² − d·t` 真证落地——证明体为本件的超集拷贝，
  -- 仅末段 γ 消元（hmid + p24_dot_eq + hζy + haxis）为新；本件陈述按冻结
  -- 纪律保持不变，合并时二取一。）


/-- 增强版三角形坐标数据（`p24_tri_data` 的超集，2026-10-08/09 波）：在
`p24_tri_data` 的 `(h, t, γ)` 输出之上并合
  • 垂距读出 `‖(v − u0) − ((v − u0) ⬝ᵥ e3) • e3‖ = h`（垂足向量范数 = ζ 模，
    `p24_norm_sq_decomp` 再包装）；
  • γ 关系 `2 * (γ*h) * h = h² + t² − d·t`（等距 `hmid` + `p24_dot_eq` 的
    re 分解 + `hζy` + `haxis` 的最终消元；单线性形态——`w := γ·h` 合并后
    对 `w` 线性，避开 γ×变量单项式的 linarith 盲区）。
证明体为 `p24_tri_data` 的逐行拷贝 + 末段新增（合并时二取一）。 -/
private theorem p24_tri_gamma (u0 u1 v : V3) {e1 e2 e3 : V3} (hon : Orthonormal3 e1 e2 e3)
    (hax : (u1 - u0 : V3) = dist u0 u1 • e3) (hu01 : u0 ≠ u1)
    (hnc : ¬ Collinear3 u0 u1 v)
    (hex : ∃ p : V3, p ∈ (affineSpan ℝ ({u0, u1, v} : Set V3) : Set V3) ∧
      ∃ ρ : ℝ, ∀ w ∈ ({u0, u1, v} : Set V3), ρ = dist p w) :
    ∃ h t w : ℝ, 0 < h ∧ (v - u0 : V3) ⬝ᵥ e3 = t ∧
      ‖(v - u0 : V3) - ((v - u0 : V3) ⬝ᵥ e3) • e3‖ = h ∧
      radV ({u0, u1, v} : Set V3) ^ 2 = dist u0 u1 ^ 2 / 4 + w ^ 2 ∧
      2 * w * h = h ^ 2 + t ^ 2 - dist u0 u1 * t ∧
      0 ≤ radV ({u0, u1, v} : Set V3) := by
  obtain ⟨hccP, hrad⟩ := p24_radV_extract hex
  set CC := circumcenter ({u0, u1, v} : Set V3) with hCCdef
  obtain ⟨α, γ, hrep⟩ := Submodule.mem_span_pair.mp (p24_affspan_dir hccP)
  have hax' : (u1 - u0 : V3) = dist u1 u0 • e3 := by rw [dist_comm u1 u0]; exact hax
  have hζ0 : zOf e1 e2 (v - u0) ≠ 0 := (zOf_ne_zero_iff hon hax' hu01.symm v).mpr hnc
  have hζy : zOf e1 e2 (CC - u0) = (γ : ℂ) * zOf e1 e2 (v - u0) := by
    rw [← hrep, p24_zeta_add, p24_zeta_smul, p24_zeta_smul,
      show zOf e1 e2 (u1 - u0) = 0 from by
        rw [hax, p24_zeta_smul, p24_zeta_e3 hon]; ring]
    ring
  have hd0 : 0 < dist u0 u1 := dist_pos.mpr hu01
  have hdu0 : dist CC u0 = dist CC u1 := (hrad u0 (by simp)).symm.trans (hrad u1 (by simp))
  have hd3 : ‖(dist u0 u1 • e3 : V3)‖ ^ 2 = dist u0 u1 ^ 2 := by
    have h1 : ‖(dist u0 u1 • e3 : V3)‖ = dist u0 u1 * ‖e3‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hd0)]
    rw [h1, p24_norm_e3 hon]
    simp
  have haxis : (CC - u0 : V3) ⬝ᵥ e3 = dist u0 u1 / 2 := by
    have e0 : (CC - u0 : V3) - dist u0 u1 • e3 = CC - u1 := by rw [← hax]; module
    have h1 : ‖CC - u0‖ ^ 2 = ‖CC - u1‖ ^ 2 := by
      rw [← dist_eq_norm CC u1, ← hdu0, ← dist_eq_norm]
    have h2 := p24_sq_eq_doteq (y := (CC - u0 : V3)) (z := (dist u0 u1 • e3 : V3))
      (by rw [e0]; exact h1)
    have hsmul : (CC - u0 : V3) ⬝ᵥ ((dist u0 u1 • e3 : V3))
        = dist u0 u1 * ((CC - u0 : V3) ⬝ᵥ e3) := by
      rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul]
    rw [hsmul, hd3] at h2
    have hd0' : (dist u0 u1 : ℝ) ≠ 0 := ne_of_gt hd0
    refine mul_left_cancel₀ hd0' ?_
    linarith
  have hdv : dist CC u0 = dist CC v := (hrad u0 (by simp)).symm.trans (hrad v (by simp))
  -- 等距关系：2 (CC − u0) ⬝ᵥ (v − u0) = ‖v − u0‖²
  have hmid : 2 * ((CC - u0 : V3) ⬝ᵥ (v - u0 : V3)) = ‖(v - u0 : V3)‖ ^ 2 := by
    have e0 : (CC - u0 : V3) - (v - u0) = CC - v := by module
    have h1 : ‖CC - u0‖ ^ 2 = ‖CC - v‖ ^ 2 := by
      rw [← dist_eq_norm CC v, ← hdv, ← dist_eq_norm]
    have h2 := p24_sq_eq_doteq (y := (CC - u0 : V3)) (z := (v - u0 : V3))
      (by rw [e0]; exact h1)
    exact h2
  -- 实/虚部抽取（zOf 的坐标语义）
  have hreE : ∀ z : V3, Complex.re (zOf e1 e2 z) = z ⬝ᵥ e1 := by
    intro z
    simp only [zOf, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    simp
  have himE : ∀ z : V3, Complex.im (zOf e1 e2 z) = z ⬝ᵥ e2 := by
    intro z
    simp only [zOf, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
      Complex.I_im]
    simp
  -- γ 系数（hζy 的 re/im 分量）
  have hcoef1 : (CC - u0 : V3) ⬝ᵥ e1 = γ * ((v - u0 : V3) ⬝ᵥ e1) := by
    have hre1 := hreE (CC - u0)
    rw [hζy, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hreE, himE] at hre1
    linarith
  have hcoef2 : (CC - u0 : V3) ⬝ᵥ e2 = γ * ((v - u0 : V3) ⬝ᵥ e2) := by
    have him1 := himE (CC - u0)
    rw [hζy, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, himE, hreE] at him1
    linarith
  have hnsqv : ‖zOf e1 e2 (v - u0)‖ ^ 2 = Complex.normSq (zOf e1 e2 (v - u0)) :=
    Complex.sq_norm (zOf e1 e2 (v - u0))
  have h33 : e3 ⬝ᵥ e3 = 1 := hon.2.2.1
  refine ⟨‖zOf e1 e2 (v - u0)‖, (v - u0 : V3) ⬝ᵥ e3, γ * ‖zOf e1 e2 (v - u0)‖,
    norm_pos_iff.mpr hζ0, rfl, ?_, ?_, ?_, ?_⟩
  · -- 垂距读出：‖(v − u0) − T•e3‖ = ‖ζ‖（正交分解 + 平方相等 + 非负；
    -- 雷区规避：点积目标一律以 `set` 原子化 + `rw` 产形，避免 binop 重结合）
    set P := (v - u0 : V3) - ((v - u0 : V3) ⬝ᵥ e3) • e3 with hP
    have hPorth : (P : V3) ⬝ᵥ e3 = 0 := by
      rw [hP, WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct,
        smul_eq_mul, h33]
      ring
    have hvy : P + (((v - u0 : V3) ⬝ᵥ e3) • e3 : V3) = (v - u0 : V3) := by
      rw [hP]; module
    have hsplit : ‖v - u0‖ ^ 2
        = ‖P‖ ^ 2 + ‖(((v - u0 : V3) ⬝ᵥ e3) • e3 : V3)‖ ^ 2 := by
      have h0 := p24_norm_sq_of_orth (x := P)
        (y := (((v - u0 : V3) ⬝ᵥ e3) • e3 : V3)) (show
        P ⬝ᵥ (((v - u0 : V3) ⬝ᵥ e3) • e3 : V3) = 0 by
        rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul, hPorth, mul_zero])
      rw [hvy] at h0
      exact h0
    have hzsq2 : ‖(((v - u0 : V3) ⬝ᵥ e3) • e3 : V3)‖ ^ 2
        = ((v - u0 : V3) ⬝ᵥ e3) ^ 2 := by
      have h0 : ‖(((v - u0 : V3) ⬝ᵥ e3) • e3 : V3)‖ ^ 2
          = (((v - u0 : V3) ⬝ᵥ e3) • e3 : V3) ⬝ᵥ (((v - u0 : V3) ⬝ᵥ e3) • e3 : V3) :=
        norm_sq_eq_dot _
      simp only [h0, WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, h33]
      ring
    have hdecomp : ‖v - u0‖ ^ 2
        = ‖zOf e1 e2 (v - u0)‖ ^ 2 + ((v - u0 : V3) ⬝ᵥ e3) ^ 2 := by
      have h1 := p24_norm_sq_decomp hon (v - u0)
      have h2 : ‖zOf e1 e2 (v - u0)‖ ^ 2
          = ((v - u0 : V3) ⬝ᵥ e1) ^ 2 + ((v - u0 : V3) ⬝ᵥ e2) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hreE, himE]
        ring
      rw [h2] at h1 ⊢
      linarith
    have key : ‖P‖ ^ 2 = ‖zOf e1 e2 (v - u0)‖ ^ 2 := by
      linarith [hsplit, hzsq2, hdecomp]
    by_contra hcon
    rcases lt_or_gt_of_ne hcon with h1 | h1
    · nlinarith [key, norm_nonneg P, norm_nonneg (zOf e1 e2 (v - u0))]
    · nlinarith [key, norm_nonneg P, norm_nonneg (zOf e1 e2 (v - u0))]
  · -- radV² 分解：ρ² = d²/4 + w²（w = γ·h；与 p24_tri_data 末段同）
    have hρ := hrad u0 (by simp)
    have hnsqCC : Complex.normSq (zOf e1 e2 (CC - u0))
        = γ ^ 2 * Complex.normSq (zOf e1 e2 (v - u0)) := by
      have hd1 : Complex.normSq (zOf e1 e2 (CC - u0))
          = ((CC - u0 : V3) ⬝ᵥ e1) ^ 2 + ((CC - u0 : V3) ⬝ᵥ e2) ^ 2 := by
        rw [Complex.normSq_apply, hreE, himE]
        ring
      have hd2 : Complex.normSq (zOf e1 e2 (v - u0))
          = ((v - u0 : V3) ⬝ᵥ e1) ^ 2 + ((v - u0 : V3) ⬝ᵥ e2) ^ 2 := by
        rw [Complex.normSq_apply, hreE, himE]
        ring
      rw [hd1, hcoef1, hcoef2, mul_pow, mul_pow]
      rw [← mul_add, ← hd2]
    rw [hρ, dist_eq_norm, p24_norm_sq_decomp hon (CC - u0), haxis, Complex.sq_norm,
      hnsqCC, mul_pow, Complex.sq_norm]
    ring
  · -- γ 关系：2(γh)h = h² + t² − dt（hmid + p24_dot_eq + hζy + haxis 消元）
    have hdecomp : ‖v - u0‖ ^ 2 = ‖zOf e1 e2 (v - u0)‖ ^ 2 + ((v - u0 : V3) ⬝ᵥ e3) ^ 2 := by
      have h1 := p24_norm_sq_decomp hon (v - u0)
      have h2 : ‖zOf e1 e2 (v - u0)‖ ^ 2
          = ((v - u0 : V3) ⬝ᵥ e1) ^ 2 + ((v - u0 : V3) ⬝ᵥ e2) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hreE, himE]
        ring
      rw [h2]
      linarith
    have hdot := p24_dot_eq hon (CC - u0) (v - u0)
    rw [hζy] at hdot
    have hre2 : Complex.re
        ((γ : ℂ) * zOf e1 e2 (v - u0) * (starRingEnd ℂ) (zOf e1 e2 (v - u0)))
        = γ * Complex.normSq (zOf e1 e2 (v - u0)) := by
      have hgen : ∀ W : ℂ, Complex.re ((γ : ℂ) * W * (starRingEnd ℂ) W)
          = γ * Complex.normSq W := by
        intro W
        have h1 : Complex.re ((γ : ℂ) * W * (starRingEnd ℂ) W)
            = Complex.re ((γ : ℂ) * W) * Complex.re ((starRingEnd ℂ) W)
              - Complex.im ((γ : ℂ) * W) * Complex.im ((starRingEnd ℂ) W) :=
          Complex.mul_re _ _
        have h2 : Complex.re ((γ : ℂ) * W) = γ * Complex.re W := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
        have h3 : Complex.im ((γ : ℂ) * W) = γ * Complex.im W := by
          rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
        rw [h1, h2, h3, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
        ring
      exact hgen _
    rw [hre2, haxis] at hdot
    have hkey1 : 2 * (γ * ‖zOf e1 e2 (v - u0)‖) * ‖zOf e1 e2 (v - u0)‖
        + dist u0 u1 * ((v - u0 : V3) ⬝ᵥ e3)
        = ‖zOf e1 e2 (v - u0)‖ ^ 2 + ((v - u0 : V3) ⬝ᵥ e3) ^ 2 := by
      have h2 : Complex.normSq (zOf e1 e2 (v - u0))
          = ‖zOf e1 e2 (v - u0)‖ * ‖zOf e1 e2 (v - u0)‖ :=
        hnsqv.symm.trans (pow_two _)
      rw [h2] at hdot
      -- 双形态坑：hmid 陈述已全标注 V3（WRAPPED 形态），与 hdot 一致
      linear_combination hmid + hdecomp - 2 * hdot
    linarith
  · -- radV 非负（= 外心到顶点的距离）
    rw [hrad v (by simp)]
    exact dist_nonneg


set_option maxHeartbeats 20000000 in
/-- (α) 支纯度量排除主装配（2026-10-08/09 波；`p24_REUHADY_nondeg_azim` 的
`v1 ≠ v2` 支）：饱和 packing 的棱 `u0u1`（`2 ≤ d < 2√2`）上 `azim = 0` 与
`v1 ≠ v2` 不相容。骨架：`azim = 0` 经 `azim_eq_zero_iff` + `affGt_pair_iff`
给出 `v1 − u0 = c•(v2 − u0) + k•(u1 − u0)`（`c > 0`）；`p24_tri_gamma` 给出
每三角形的坐标数据 `(h_i, t_i, w_i)`（垂距、轴坐标、外心垂坐标积）；关键
几何（同一垂线射线上的两点必有一对 ≥ 2 相距，与 packing 相抵）：
  • 盘界（γ 关系消元）：`dist(v_i, q)² = 2 − 2h_i(β − w_i)`，其中
    `q = 中点沿垂线上移 β`（`β = √(2 − d²/4)`，`d²/4 + β² = 2`）——圆心
    在 `w_i < β`（由 `ρ_i < √2`）时严格在开球内；
  • 锥界（packing `v_i` 距 `u0,u1 ≥ 2` + 盘界）：
    `|t_i − d/2| < 2β(h_i − β)/d`（HL 锥形界 `2β(h_i − β) > d|s_i|`），
    并迫使 `h_i > β`；
  • 终步：`dist(v₁,v₂)² = 4 − 2(p₁ + p₂ + Q)`，其中 `p_i = h_i(β − w_i) > 0`，
    `Q = (t₁−d/2)(t₂−d/2) + (h₁−β)(h₂−β) > 0`（锥界 + `4β² ≤ d²`——这用
    `d ≥ 2`，即 packing 对棱自身的下界）。
陈述冻结纪律：本件为新私件，`hr1/hr2` 以 `radV` 半径显式入参（shim 侧由
`hl vl_i < √2` 派生）。 -/
private theorem p24_nondeg_azim_ne {V : Set V3} {u0 u1 v1 v2 : V3}
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hv1V : v1 ∈ V) (hv2V : v2 ∈ V) (hnc1 : ¬ Collinear3 u0 u1 v1)
    (hnc2 : ¬ Collinear3 u0 u1 v2) (hd8 : dist u0 u1 < Real.sqrt 8)
    (hr1 : radV ({u0, u1, v1} : Set V3) < Real.sqrt 2)
    (hr2 : radV ({u0, u1, v2} : Set V3) < Real.sqrt 2)
    (hvne : v1 ≠ v2) (haz : azim u0 u1 v1 v2 = 0) : False := by
  have hu01 : u0 ≠ u1 := by
    intro hcon
    rw [hcon] at hnc1
    exact hnc1 (collinear3_of_eq rfl)
  have hpku0u1 : 2 ≤ dist u0 u1 := hp.dist_ge_two hu0 hu1 hu01
  have hdlt : dist u0 u1 < 2 * Real.sqrt 2 := by
    have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      have h4 : Real.sqrt 4 = 2 := by
        have h22 := Real.sqrt_mul_self (show (0:ℝ) ≤ 2 from by norm_num)
        rw [show (2:ℝ) * 2 = 4 from by norm_num] at h22
        exact h22
      rw [show (8:ℝ) = 4 * 2 from by norm_num,
        Real.sqrt_mul (x := 4) (by norm_num) 2, h4]
    rw [h8] at hd8
    exact hd8
  obtain ⟨d, hdd⟩ : ∃ δ : ℝ, δ = dist u0 u1 := ⟨_, rfl⟩
  rw [← hdd] at hd8 hpku0u1 hdlt
  have hd2 : (0:ℝ) < d := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hpku0u1
  have hd8sq : d ^ 2 < 8 := by
    have h2p : (0:ℝ) < 2 * Real.sqrt 2 := by positivity
    have h3 := mul_lt_mul_of_pos_right hdlt h2p
    have h4 := mul_le_mul_of_nonneg_right (le_of_lt hdlt) hd2.le
    have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
      ((Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)).symm.trans (sq (Real.sqrt 2))).symm
    have h5 : (2 * Real.sqrt 2) * (2 * Real.sqrt 2) = 8 := by
      have e1 : (2 * Real.sqrt 2) * (2 * Real.sqrt 2)
          = 2 * 2 * (Real.sqrt 2 * Real.sqrt 2) := by ring
      rw [e1, h22]
      norm_num
    rw [h5, mul_comm d (2 * Real.sqrt 2)] at h3
    linarith only [h3, h4]
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = Real.sqrt (2 - d ^ 2 / 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]
    exact Real.sqrt_pos.mpr (by linarith only [hd8sq])
  have hβsq : β ^ 2 = 2 - d ^ 2 / 4 := by
    rw [hβdef, Real.sq_sqrt (by linarith only [hd8sq])]
  have hβ2 : d ^ 2 / 4 + β ^ 2 = 2 := by rw [hβsq]; ring
  have hdsq4 : (4:ℝ) ≤ d ^ 2 := by nlinarith only [hpku0u1]
  have hβd : 4 * β ^ 2 ≤ d ^ 2 := by
    have h4b : 4 * β ^ 2 = 8 - d ^ 2 := by rw [hβsq]; ring
    linarith only [h4b, hdsq4]
  -- 标架
  obtain ⟨e1, e2, e3, hon, hax0⟩ :=
    exists_on3_eq_smul (u1 - u0) (sub_ne_zero.mpr (Ne.symm hu01))
  have hax : (u1 - u0 : V3) = d • e3 := by
    have hn : ‖u1 - u0‖ = dist u0 u1 := (dist_eq_norm u1 u0).symm.trans (dist_comm u1 u0)
    rw [hdd, ← hn]
    exact hax0
  have h33 : e3 ⬝ᵥ e3 = 1 := hon.2.2.1
  have he3n : ∀ r : ℝ, ‖((r : ℝ) • e3 : V3)‖ ^ 2 = r ^ 2 := by
    intro r
    have h0 : ‖((r : ℝ) • e3 : V3)‖ ^ 2 = ((r : ℝ) • e3 : V3) ⬝ᵥ ((r : ℝ) • e3 : V3) :=
      norm_sq_eq_dot _
    simp only [h0, WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, h33]
    ring
  -- azim = 0 的仿射表示
  have hv20 : v2 ≠ u0 := by
    intro hcon
    rw [hcon] at hnc2
    refine hnc2 ?_
    rw [collinear3_iff_smul (Ne.symm hu01)]
    exact ⟨0, by rw [zero_smul, sub_self]⟩
  have hv21 : v2 ≠ u1 := by
    intro hcon
    rw [hcon] at hnc2
    refine hnc2 ?_
    rw [collinear3_iff_smul (Ne.symm hu01)]
    exact ⟨1, by rw [one_smul]⟩
  have hmem : v1 ∈ affGt {u0, u1} {v2} := (azim_eq_zero_iff hnc1 hnc2).mp haz
  obtain ⟨c, hc0, k, hrep⟩ := (affGt_pair_iff hu01 hv20 hv21).mp hmem
  -- 三角形坐标数据（tri_gamma 的 hax 入参取 dist 形态）
  have haxd' : (u1 - u0 : V3) = dist u0 u1 • e3 := by rw [← hdd]; exact hax
  obtain ⟨h1, t1, w1, hh1pos, ht1eq, hPn1, hrad1, hgam1, hnn1⟩ :=
    p24_tri_gamma u0 u1 v1 hon haxd' hu01 hnc1 (p24_cc_exists u0 u1 v1 hu01 hnc1)
  obtain ⟨h2, t2, w2, hh2pos, ht2eq, hPn2, hrad2, hgam2, hnn2⟩ :=
    p24_tri_gamma u0 u1 v2 hon haxd' hu01 hnc2 (p24_cc_exists u0 u1 v2 hu01 hnc2)
  rw [← hdd] at hgam1 hgam2 hrad1 hrad2
  rw [ht1eq] at hPn1
  rw [ht2eq] at hPn2
  obtain ⟨P1, hP1d⟩ : ∃ P : V3, P = (v1 - u0 : V3) - t1 • e3 := ⟨_, rfl⟩
  obtain ⟨P2, hP2d⟩ : ∃ P : V3, P = (v2 - u0 : V3) - t2 • e3 := ⟨_, rfl⟩
  rw [← hP1d] at hPn1
  rw [← hP2d] at hPn2
  have hP1e3 : (P1 : V3) ⬝ᵥ e3 = 0 := by
    rw [hP1d, WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, h33, ht1eq]
    ring
  have hP2e3 : (P2 : V3) ⬝ᵥ e3 = 0 := by
    rw [hP2d, WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, h33, ht2eq]
    ring
  -- 轴坐标关系与垂足线性关系（同一垂线射线）
  have htrel : t1 = c * t2 + k * d := by
    have e1v : (u1 - u0 : V3) ⬝ᵥ e3 = d := by
      rw [hax, WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, h33]; ring
    have e2v : (v1 - u0 : V3) ⬝ᵥ e3
        = c * ((v2 - u0 : V3) ⬝ᵥ e3) + k * ((u1 - u0 : V3) ⬝ᵥ e3) := by
      rw [hrep, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul, add_dotProduct,
        smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    rw [← ht1eq, e2v, ← ht2eq, e1v]
  have hPP : (P1 : V3) = c • (P2 : V3) := by
    rw [hP1d, hP2d, hrep, htrel, hax, smul_smul]
    module
  have hh1c : h1 = c * h2 := by
    rw [← hPn1, ← hPn2, hPP, norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
  -- 半径事实：radV_i² < 2（单调平方）→ |w_i| < β（ρ_i < √2）
  have hr1sq : radV ({u0, u1, v1} : Set V3) ^ 2 < 2 := by
    have h2p : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h3 := mul_lt_mul_of_pos_right hr1 h2p
    rw [← sq (Real.sqrt 2), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h3
    have h4 := mul_le_mul_of_nonneg_left (le_of_lt hr1) hnn1
    linarith
  have hr2sq : radV ({u0, u1, v2} : Set V3) ^ 2 < 2 := by
    have h2p : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h3 := mul_lt_mul_of_pos_right hr2 h2p
    rw [← sq (Real.sqrt 2), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h3
    have h4 := mul_le_mul_of_nonneg_left (le_of_lt hr2) hnn2
    linarith
  have hw1lt : w1 ^ 2 < β ^ 2 := by rw [hβsq]; linarith only [hrad1, hr1sq]
  have hw1ltβ : w1 < β := by
    rcases le_or_gt β w1 with hx | hx
    · exact absurd hw1lt (not_lt.mpr (by
        have hkey : β ^ 2 ≤ w1 ^ 2 := by
          have hbb := mul_le_mul_of_nonneg_right hx hβpos.le
          have hww := mul_le_mul_of_nonneg_left hx (le_trans hβpos.le hx)
          calc β ^ 2 = β * β := sq β
            _ ≤ w1 * β := hbb
            _ ≤ w1 * w1 := hww
            _ = w1 ^ 2 := (sq w1).symm
        exact hkey))
    · exact hx
  have hn1 : 0 < β - w1 := by linarith only [hw1ltβ]
  have hw2lt : w2 ^ 2 < β ^ 2 := by rw [hβsq]; linarith only [hrad2, hr2sq]
  have hw2ltβ : w2 < β := by
    rcases le_or_gt β w2 with hx | hx
    · exact absurd hw2lt (not_lt.mpr (by
        have hkey : β ^ 2 ≤ w2 ^ 2 := by
          have hbb := mul_le_mul_of_nonneg_right hx hβpos.le
          have hww := mul_le_mul_of_nonneg_left hx (le_trans hβpos.le hx)
          calc β ^ 2 = β * β := sq β
            _ ≤ w2 * β := hbb
            _ ≤ w2 * w2 := hww
            _ = w2 ^ 2 := (sq w2).symm
        exact hkey))
    · exact hx
  have hn2 : 0 < β - w2 := by linarith only [hw2ltβ]
  -- 盘界方程：dist(v_i, q)² = 2 − 2·h_i·(β − w_i) < 2
  have hdsk1 : (t1 - d / 2) ^ 2 + (h1 - β) ^ 2 = 2 - 2 * (h1 * (β - w1)) := by
    have hbm : h1 * (β - w1) = β * h1 - w1 * h1 := by ring
    have hA : (t1 - d / 2) ^ 2 + (h1 - β) ^ 2
        = t1 ^ 2 + h1 ^ 2 - d * t1 - 2 * β * h1 + (d ^ 2 / 4 + β ^ 2) := by ring
    rw [hβ2] at hA
    linarith only [hA, hgam1, hbm]
  have hdsk2 : (t2 - d / 2) ^ 2 + (h2 - β) ^ 2 = 2 - 2 * (h2 * (β - w2)) := by
    have hbm : h2 * (β - w2) = β * h2 - w2 * h2 := by ring
    have hA : (t2 - d / 2) ^ 2 + (h2 - β) ^ 2
        = t2 ^ 2 + h2 ^ 2 - d * t2 - 2 * β * h2 + (d ^ 2 / 4 + β ^ 2) := by ring
    rw [hβ2] at hA
    linarith only [hA, hgam2, hbm]
  have hdsklt1 : 2 - 2 * (h1 * (β - w1)) < 2 := by
    linarith only [mul_pos hh1pos hn1]
  have hdsklt2 : 2 - 2 * (h2 * (β - w2)) < 2 := by
    linarith only [mul_pos hh2pos hn2]
  -- A_i：盘界展开（t² + h² < dt + 2βh）
  have hA1 : t1 ^ 2 + h1 ^ 2 < d * t1 + 2 * β * h1 := by
    have hE : (t1 - d / 2) ^ 2 + (h1 - β) ^ 2
        = t1 ^ 2 + h1 ^ 2 - d * t1 - 2 * β * h1 + 2 := by
      have hE2 : (t1 - d / 2) ^ 2 + (h1 - β) ^ 2
          = t1 ^ 2 + h1 ^ 2 - d * t1 - 2 * β * h1 + (d ^ 2 / 4 + β ^ 2) := by ring
      rwa [hβ2] at hE2
    have hMs : (t1 - d / 2) ^ 2 + (h1 - β) ^ 2 < 2 := by
      rw [hdsk1]; exact hdsklt1
    linarith only [hE, hMs]
  have hA2 : t2 ^ 2 + h2 ^ 2 < d * t2 + 2 * β * h2 := by
    have hE : (t2 - d / 2) ^ 2 + (h2 - β) ^ 2
        = t2 ^ 2 + h2 ^ 2 - d * t2 - 2 * β * h2 + 2 := by
      have hE2 : (t2 - d / 2) ^ 2 + (h2 - β) ^ 2
          = t2 ^ 2 + h2 ^ 2 - d * t2 - 2 * β * h2 + (d ^ 2 / 4 + β ^ 2) := by ring
      rwa [hβ2] at hE2
    have hMs : (t2 - d / 2) ^ 2 + (h2 - β) ^ 2 < 2 := by
      rw [hdsk2]; exact hdsklt2
    linarith only [hE, hMs]
  -- packing：dist(v_i, u0), dist(v_i, u1) ≥ 2
  have hv10 : v1 ≠ u0 := by
    intro hcon
    rw [hcon] at hnc1
    refine hnc1 ?_
    rw [collinear3_iff_smul (Ne.symm hu01)]
    exact ⟨0, by rw [zero_smul, sub_self]⟩
  have hv11 : v1 ≠ u1 := by
    intro hcon
    rw [hcon] at hnc1
    refine hnc1 ?_
    rw [collinear3_iff_smul (Ne.symm hu01)]
    exact ⟨1, by rw [one_smul]⟩
  have hvu01 : (v1 - u0 : V3) = (P1 : V3) + ((t1 : ℝ) • e3 : V3) := by
    rw [hP1d, sub_add_cancel]
  have hvu11 : (v1 - u1 : V3) = (P1 : V3) + ((t1 - d : ℝ) • e3 : V3) := by
    rw [hP1d, sub_smul, ← hax]
    abel
  have n01 : ‖v1 - u0‖ ^ 2 = t1 ^ 2 + h1 ^ 2 := by
    have h0 := p24_norm_sq_of_orth (x := (P1 : V3)) (y := ((t1 : ℝ) • e3 : V3))
      (show (P1 : V3) ⬝ᵥ ((t1 : ℝ) • e3 : V3) = 0 by
        rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul, hP1e3, mul_zero])
    rw [← hvu01, hPn1, he3n] at h0
    linarith only [h0]
  have n11 : ‖v1 - u1‖ ^ 2 = (t1 - d) ^ 2 + h1 ^ 2 := by
    have h0 := p24_norm_sq_of_orth (x := (P1 : V3)) (y := ((t1 - d : ℝ) • e3 : V3))
      (show (P1 : V3) ⬝ᵥ ((t1 - d : ℝ) • e3 : V3) = 0 by
        rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul, hP1e3, mul_zero])
    rw [← hvu11, hPn1, he3n] at h0
    linarith only [h0]
  have pk1a : (4:ℝ) ≤ t1 ^ 2 + h1 ^ 2 := by
    have hsq : (4:ℝ) ≤ dist v1 u0 ^ 2 := by
      have h2le : (2:ℝ) ≤ dist v1 u0 := hp.dist_ge_two hv1V hu0 hv10
      nlinarith only [h2le]
    rwa [dist_eq_norm, n01] at hsq
  have pk1b : (4:ℝ) ≤ (t1 - d) ^ 2 + h1 ^ 2 := by
    have hsq : (4:ℝ) ≤ dist v1 u1 ^ 2 := by
      have h2le : (2:ℝ) ≤ dist v1 u1 := hp.dist_ge_two hv1V hu1 hv11
      nlinarith only [h2le]
    rwa [dist_eq_norm, n11] at hsq
  have hC1 : (4:ℝ) ≤ t1 ^ 2 + h1 ^ 2 - 2 * d * t1 + d ^ 2 := by
    have hE : (t1 - d) ^ 2 + h1 ^ 2 = t1 ^ 2 + h1 ^ 2 - 2 * d * t1 + d ^ 2 := by ring
    linarith only [hE, pk1b]
  have hD1 : (4:ℝ) < d * t1 + 2 * β * h1 := by linarith only [hA1, pk1a]
  have hE1 : d * t1 < 2 * β * h1 + d ^ 2 - 4 := by linarith only [hA1, hC1]
  have hvu02 : (v2 - u0 : V3) = (P2 : V3) + ((t2 : ℝ) • e3 : V3) := by
    rw [hP2d, sub_add_cancel]
  have hvu12 : (v2 - u1 : V3) = (P2 : V3) + ((t2 - d : ℝ) • e3 : V3) := by
    rw [hP2d, sub_smul, ← hax]
    abel
  have n02 : ‖v2 - u0‖ ^ 2 = t2 ^ 2 + h2 ^ 2 := by
    have h0 := p24_norm_sq_of_orth (x := (P2 : V3)) (y := ((t2 : ℝ) • e3 : V3))
      (show (P2 : V3) ⬝ᵥ ((t2 : ℝ) • e3 : V3) = 0 by
        rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul, hP2e3, mul_zero])
    rw [← hvu02, hPn2, he3n] at h0
    linarith only [h0]
  have n12 : ‖v2 - u1‖ ^ 2 = (t2 - d) ^ 2 + h2 ^ 2 := by
    have h0 := p24_norm_sq_of_orth (x := (P2 : V3)) (y := ((t2 - d : ℝ) • e3 : V3))
      (show (P2 : V3) ⬝ᵥ ((t2 - d : ℝ) • e3 : V3) = 0 by
        rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul, hP2e3, mul_zero])
    rw [← hvu12, hPn2, he3n] at h0
    linarith only [h0]
  have pk2a : (4:ℝ) ≤ t2 ^ 2 + h2 ^ 2 := by
    have hsq : (4:ℝ) ≤ dist v2 u0 ^ 2 := by
      have h2le : (2:ℝ) ≤ dist v2 u0 := hp.dist_ge_two hv2V hu0 hv20
      nlinarith only [h2le]
    rwa [dist_eq_norm, n02] at hsq
  have pk2b : (4:ℝ) ≤ (t2 - d) ^ 2 + h2 ^ 2 := by
    have hsq : (4:ℝ) ≤ dist v2 u1 ^ 2 := by
      have h2le : (2:ℝ) ≤ dist v2 u1 := hp.dist_ge_two hv2V hu1 hv21
      nlinarith only [h2le]
    rwa [dist_eq_norm, n12] at hsq
  have hC2 : (4:ℝ) ≤ t2 ^ 2 + h2 ^ 2 - 2 * d * t2 + d ^ 2 := by
    have hE : (t2 - d) ^ 2 + h2 ^ 2 = t2 ^ 2 + h2 ^ 2 - 2 * d * t2 + d ^ 2 := by ring
    linarith only [hE, pk2b]
  have hD2 : (4:ℝ) < d * t2 + 2 * β * h2 := by linarith only [hA2, pk2a]
  have hE2' : d * t2 < 2 * β * h2 + d ^ 2 - 4 := by linarith only [hA2, hC2]
  -- 锥界：|t_i − d/2| < 2β(h_i − β)/d，并迫使 h_i > β
  have hexp1 : d * (t1 - d / 2) = d * t1 - d ^ 2 / 2 := by ring
  have hexp2 : d * (t2 - d / 2) = d * t2 - d ^ 2 / 2 := by ring
  have hyexp1 : 2 * β * (h1 - β) = 2 * β * h1 - (4 - d ^ 2 / 2) := by
    linear_combination -2 * hβsq
  have hyexp2 : 2 * β * (h2 - β) = 2 * β * h2 - (4 - d ^ 2 / 2) := by
    linear_combination -2 * hβsq
  have hcone1 : |t1 - d / 2| < 2 * β * (h1 - β) / d := by
    rw [abs_lt]
    constructor
    · rw [← neg_div d (2 * β * (h1 - β)), div_lt_iff₀ hd2]
      linarith only [hD1, hexp1, hyexp1]
    · rw [lt_div_iff₀ hd2]
      linarith only [hE1, hexp1, hyexp1]
  have hcone2 : |t2 - d / 2| < 2 * β * (h2 - β) / d := by
    rw [abs_lt]
    constructor
    · rw [← neg_div d (2 * β * (h2 - β)), div_lt_iff₀ hd2]
      linarith only [hD2, hexp2, hyexp2]
    · rw [lt_div_iff₀ hd2]
      linarith only [hE2', hexp2, hyexp2]
  have hb1 : 0 < h1 - β := by
    have hpos2 : (0:ℝ) < 2 * β * (h1 - β) / d := lt_of_le_of_lt (abs_nonneg _) hcone1
    rcases div_pos_iff.mp hpos2 with h3 | h3
    · have h4' : (2 * β) * 0 < (2 * β) * (h1 - β) := by
        rw [mul_zero]; exact h3.1
      exact lt_of_mul_lt_mul_left h4' (by linarith only [hβpos])
    · exact absurd h3.2 (not_lt.mpr (le_of_lt hd2))
  have hb2 : 0 < h2 - β := by
    have hpos2 : (0:ℝ) < 2 * β * (h2 - β) / d := lt_of_le_of_lt (abs_nonneg _) hcone2
    rcases div_pos_iff.mp hpos2 with h3 | h3
    · have h4' : (2 * β) * 0 < (2 * β) * (h2 - β) := by
        rw [mul_zero]; exact h3.1
      exact lt_of_mul_lt_mul_left h4' (by linarith only [hβpos])
    · exact absurd h3.2 (not_lt.mpr (le_of_lt hd2))
  -- 终步拼装：dist(v₁,v₂)² = 4 − 2(p₁ + p₂ + Q) < 4
  have hQpos : 0 < (t1 - d / 2) * (t2 - d / 2) + (h1 - β) * (h2 - β) := by
    have hy12 : 0 < (h1 - β) * (h2 - β) := mul_pos hb1 hb2
    have hm12 : |t1 - d / 2| * |t2 - d / 2|
        < (2 * β * (h1 - β) / d) * (2 * β * (h2 - β) / d) :=
      mul_lt_mul'' hcone1 hcone2 (abs_nonneg _) (abs_nonneg _)
    have hdiv : (2 * β * (h1 - β) / d) * (2 * β * (h2 - β) / d)
        ≤ (h1 - β) * (h2 - β) := by
      have hexp : (2 * β * (h1 - β) / d) * (2 * β * (h2 - β) / d)
          = 4 * β ^ 2 * ((h1 - β) * (h2 - β)) / (d * d) := by
        field_simp
        ring
      rw [hexp, div_le_iff₀ (mul_pos hd2 hd2)]
      have step := mul_le_mul_of_nonneg_right hβd (le_of_lt hy12)
      have dd : d * d = d ^ 2 := (sq d).symm
      linarith
    have exx : -(|t1 - d / 2| * |t2 - d / 2|) ≤ (t1 - d / 2) * (t2 - d / 2) := by
      have h9 := neg_abs_le ((t1 - d / 2) * (t2 - d / 2))
      rwa [abs_mul] at h9
    linarith only [exx, hm12, hdiv, hy12]
  have hvv : (v1 - v2 : V3) = ((t1 - t2 : ℝ) • e3 : V3) + ((P1 - P2 : V3)) := by
    have hsub : (v1 - v2 : V3) = (v1 - u0 : V3) - (v2 - u0 : V3) := by
      rw [sub_sub_sub_cancel_right]
    rw [hsub, hvu01, hvu02, sub_smul]
    module
  have hP12e3 : ((P1 - P2 : V3)) ⬝ᵥ e3 = 0 := by
    rw [WithLp.ofLp_sub, sub_dotProduct, hP1e3, hP2e3]; ring
  have hP12n : ‖(P1 - P2 : V3)‖ = |h1 - h2| := by
    have hsub : (P1 - P2 : V3) = ((c - 1 : ℝ)) • ((P2 : V3)) := by
      rw [hPP]; module
    have hh : h1 - h2 = (c - 1) * h2 := by rw [hh1c]; ring
    rw [hsub, norm_smul, Real.norm_eq_abs, hPn2, hh, abs_mul, abs_of_pos hh2pos]
  have hsplit2 : ‖v1 - v2‖ ^ 2 = (t1 - t2) ^ 2 + (h1 - h2) ^ 2 := by
    have h0 := p24_norm_sq_of_orth (x := ((t1 - t2 : ℝ) • e3 : V3))
      (y := ((P1 - P2 : V3))) (show
      ((t1 - t2 : ℝ) • e3 : V3) ⬝ᵥ ((P1 - P2 : V3)) = 0 by
      simp only [WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm, hP12e3, mul_zero])
    rw [← hvv, hP12n, he3n, sq_abs] at h0
    linarith only [h0]
  have hpk12 : 2 ≤ dist v1 v2 := hp.dist_ge_two hv1V hv2V hvne
  have hdge : (4:ℝ) ≤ ‖v1 - v2‖ ^ 2 := by
    rw [← dist_eq_norm]
    nlinarith only [hpk12]
  have idr : (t1 - t2) ^ 2 + (h1 - h2) ^ 2
      + 2 * ((t1 - d / 2) * (t2 - d / 2) + (h1 - β) * (h2 - β))
      = ((t1 - d / 2) ^ 2 + (h1 - β) ^ 2) + ((t2 - d / 2) ^ 2 + (h2 - β) ^ 2) := by
    ring
  rw [hdsk1, hdsk2] at idr
  rw [hsplit2] at hdge
  linarith only [idr, mul_pos hh1pos hn1, mul_pos hh2pos hn2, hQpos, hdge]


/-- barV V 2 三元组的承载集读出：`barV V 2 vl` + 前二元集为 `{u0, u1}` +
第三元为 `v` 时，`setOfList vl = {u0, u1, v}`。(α) 支 shim 侧把 `hl vl < √2`
翻译成 `radV {u0, u1, v} < √2` 的桥件（2026-10-08/09 波）。 -/
private theorem p24_setOfList_pair2 {V : Set V3} {u0 u1 v : V3} {vl : List V3}
    (hbar : barV V 2 vl) (htr : setOfList (truncateSimplex 1 vl) = ({u0, u1} : Set V3))
    (hv : v = elV vl 2) :
    setOfList vl = ({u0, u1, v} : Set V3) := by
  have h3 : vl.length = 3 := hbar.1
  have hpair : ({elV vl 0, elV vl 1} : Set V3) = {u0, u1} := by
    have h4 : setOfList (truncateSimplex 1 vl) = ({elV vl 0, elV vl 1} : Set V3) := by
      rw [truncateSimplex1_pair vl (by have := hbar.1; omega)]
      ext x
      simp [setOfList]
    rw [← h4, htr]
  ext x
  simp only [setOfList, Set.mem_insert_iff]
  constructor
  · intro hx
    have hx3 := p24_mem_cases_len3 h3 hx
    have hm0 : (elV vl 0 : V3) ∈ ({elV vl 0, elV vl 1} : Set V3) := by simp
    have hm1 : (elV vl 1 : V3) ∈ ({elV vl 0, elV vl 1} : Set V3) := by simp
    rw [hpair] at hm0 hm1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm0 hm1
    rcases hx3 with hc | hc | hc
    · rw [← hc] at hm0
      rcases hm0 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [← hc] at hm1
      rcases hm1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by rw [Set.mem_singleton_iff]; exact hc.trans hv.symm))
  · have hu0v : u0 = elV vl 0 ∨ u0 = elV vl 1 := by
      have hm : (u0 : V3) ∈ setOfList (truncateSimplex 1 vl) := by rw [htr]; simp
      rw [truncateSimplex1_pair vl (by have := hbar.1; omega)] at hm
      simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hm
      exact hm
    have hu1v : u1 = elV vl 0 ∨ u1 = elV vl 1 := by
      have hm : (u1 : V3) ∈ setOfList (truncateSimplex 1 vl) := by rw [htr]; simp
      rw [truncateSimplex1_pair vl (by have := hbar.1; omega)] at hm
      simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hm
      exact hm
    rintro (rfl | rfl | rfl)
    · rcases hu0v with h | h
      · rw [h]; exact p24_elV_mem (by have := hbar.1; omega)
      · rw [h]; exact p24_elV_mem (by have := hbar.1; omega)
    · rcases hu1v with h | h
      · rw [h]; exact p24_elV_mem (by have := hbar.1; omega)
      · rw [h]; exact p24_elV_mem (by have := hbar.1; omega)
    · rw [hv]; exact p24_elV_mem (by have := hbar.1; omega)

/-! ## (β) 支独立存在性引理第一波：margin + 中点 ∈ voronoiList + fan 抽叶
（2026-10-10 波，三件全真证，供 `p24_exists_mcell_not_flat` 后续波装配）

- `p24_voronoiList_pair`：`voronoi_list V [u0;u1]` = 两闭胞之交
  （PA23:846 `p23_voronoiList_pair` 证照逐字私拷——PA23 并行工位不 import，
  合并时两者取一）；
- `p24_mid_margin`：短棱外任一 packing 点到棱中点 `p` 的距离不低于
  `s = √(4−(d/2)²)`（packing 两两距离 ≥ 2 + 平行四边形恒等式；对 `d`
  无假设恒成立）；
- `p24_mid_mem_voronoiList`：中点 `u0 + (1/2)•(u1−u0)` 落进
  `voronoiList V [u0,u1]`（margin + `d/2 < s` 严格不等式 + 成员定义展开；
  HL Rogers.XYOFCGX 对应物，PA23:1037 孪生）；
- `p24_leaf_exists`：`p24_voronoi_pair_split`（本文件 fan 结构，真证）右端
  并集非空（中点成员供给）抽出叶三元组 `vl`（`barV V 3 vl ∧
  truncateSimplex 1 vl = [u0, u1]`；`barV` 自带 nondg 链免费）——
  路线图（docs/pa24-nonflat-roadmap.md）第一档，装配的第一块砖。 -/

/-- `voronoi_list V [u0;u1]` = the intersection of the two closed cells
(PA23:846 proven-pattern private copy). -/
private theorem p24_voronoiList_pair (V : Set V3) (u0 u1 : V3) :
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

/-- (β) 支第一波件 1（margin）：短棱外任一 packing 点到棱中点 `p` 的距离
不低于 `s = √(4−(d/2)²)`（packing 两两距离 ≥ 2 + 平行四边形恒等式
`4·‖w−p‖² = 2(‖w−u0‖²+‖w−u1‖²) − d²`；对 `d` 无假设，恒成立）。 -/
private theorem p24_mid_margin (V : Set V3) (u0 u1 w : V3) (hp : Packing V)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hw : w ∈ V) (hw0 : w ≠ u0) (hw1 : w ≠ u1)
    (hd : dist u0 u1 < Real.sqrt 2) :
    Real.sqrt (4 - (dist u0 u1 / 2) ^ 2) ≤ dist (u0 + (1 / 2 : ℝ) • (u1 - u0)) w := by
  set d := dist u0 u1 with hddef
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
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
  have hdw0 : (0:ℝ) ≤ dist w u0 := dist_nonneg
  have hdw1 : (0:ℝ) ≤ dist w u1 := dist_nonneg
  have hq0 : 4 ≤ dist w u0 ^ 2 := by nlinarith
  have hq1 : 4 ≤ dist w u1 ^ 2 := by nlinarith
  have hdpw : (0:ℝ) ≤ dist p w := dist_nonneg
  have hsq2 : (d / 2) ^ 2 = d ^ 2 / 4 := by ring
  have hsx : 4 - (d / 2) ^ 2 ≤ dist p w ^ 2 := by linarith
  calc Real.sqrt (4 - (d / 2) ^ 2) ≤ Real.sqrt (dist p w ^ 2) := Real.sqrt_le_sqrt hsx
    _ = |dist p w| := Real.sqrt_sq_eq_abs (dist p w)
    _ = dist p w := abs_of_nonneg hdpw

/-- (β) 支第一波件 2：棱中点落在配对 voronoi list 内
（margin + `d/2 < s` 严格不等式 + voronoiList 成员定义展开），
中点写成 `u0 + (1/2)•(u1−u0)`（PA23 中点桥 XYOFCGX 的私拷形式）。 -/
private theorem p24_mid_mem_voronoiList (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hd : dist u0 u1 < Real.sqrt 2) :
    u0 + (1 / 2 : ℝ) • (u1 - u0) ∈ voronoiList V [u0, u1] := by
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hpu0 : dist p u0 = dist u0 u1 / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show dist u0 u1 = ‖u1 - u0‖ from by rw [dist_eq_norm, norm_sub_rev]]
    ring
  have hpu1 : dist p u1 = dist u0 u1 / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u1 = (1 / 2 : ℝ) • (u0 - u1) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show dist u0 u1 = ‖u0 - u1‖ from by rw [dist_eq_norm]]
    ring
  have hd2 : dist u0 u1 ^ 2 < 8 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (le_of_lt (by norm_num : (0:ℝ) < 2))
    have hdpos : (0:ℝ) ≤ dist u0 u1 := dist_nonneg
    nlinarith
  have hhalf : (dist u0 u1 / 2) ^ 2 < 4 - (dist u0 u1 / 2) ^ 2 := by
    have hq : (dist u0 u1 / 2) ^ 2 = dist u0 u1 ^ 2 / 4 := by ring
    linarith
  have hstrict : dist u0 u1 / 2 < Real.sqrt (4 - (dist u0 u1 / 2) ^ 2) := by
    have hdpos : (0:ℝ) ≤ dist u0 u1 := dist_nonneg
    have hpos : (0:ℝ) ≤ dist u0 u1 / 2 := by linarith
    have e1 : Real.sqrt ((dist u0 u1 / 2) ^ 2) < Real.sqrt (4 - (dist u0 u1 / 2) ^ 2) :=
      Real.sqrt_lt_sqrt (sq_nonneg (dist u0 u1 / 2)) hhalf
    have e2 : Real.sqrt ((dist u0 u1 / 2) ^ 2) = dist u0 u1 / 2 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hpos]
    linarith
  rw [p24_voronoiList_pair V u0 u1]
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
      exact le_trans (le_of_lt hstrict)
        (p24_mid_margin V u0 u1 w hp hu0 hu1 hw hw0 hw1 hd)
  · rw [voronoiClosed, Set.mem_setOf_eq]
    intro w hw
    by_cases hw0 : w = u0
    · subst hw0
      rw [hpu1, hpu0]
    by_cases hw1 : w = u1
    · subst hw1
      exact le_refl _
    · rw [hpu1]
      exact le_trans (le_of_lt hstrict)
        (p24_mid_margin V u0 u1 w hp hu0 hu1 hw hw0 hw1 hd)

/-- (β) 支第一波件 3（fan 抽叶）：短棱处存在叶三元组 `vl`
（`barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]`）——配对 voronoi 非空
（件 2 中点成员供给）+ `p24_voronoi_pair_split` 叶并集分解抽出；
`barV` 自带 nondg 链（后续波免费取用）。 -/
private theorem p24_leaf_exists (V : Set V3) (u0 u1 : V3) (hs : saturated V)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hd : dist u0 u1 < Real.sqrt 2) :
    ∃ vl : List V3, barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1] := by
  have hhl : hl [u0, u1] < Real.sqrt 2 :=
    p24_hl_pair_lt_sqrt2
      (lt_of_lt_of_le hd (Real.sqrt_le_sqrt (by norm_num : (2:ℝ) ≤ 8)))
  have hmem := p24_mid_mem_voronoiList V u0 u1 hp hu0 hu1 hne hd
  rw [p24_voronoi_pair_split V u0 u1 hs hp hu0 hu1 hne hhl] at hmem
  obtain ⟨T, hT, hTm⟩ := Set.mem_sUnion.mp hmem
  obtain ⟨vl, hvl, hTeq⟩ := hT
  rcases hvl with ⟨hb3, htr⟩
  exact ⟨vl, hb3, htr⟩

/-! ## (β) 支独立存在性引理第二波：ω₁ 识别 + 叶三点外接半径上界
（2026-10-10 波，真证，插在第一波三件之后、本体之前；供后续波装配）

- `p24_pgram_mid`：中点平行四边形恒等式（无假设恒成立）；
- `p24_mid_margin_sq`：margin 的平方形态 `4 − (d/2)² ≤ dist(p,w)²`
  （packing 两两距离 ≥ 2 + 恒等式；无 d 假设，比第一波 `p24_mid_margin`
  更强且免 sqrt）；
- `p24_mid_eq_of_dist`：到棱两端均为 `d/2` 的点必为中点（恒等式零化 +
  `dist_eq_zero`；`dist(u0,·)` 在中点取唯一最小值的初等核心）；
- `p24_mid_mem_voronoiList_sqrt8`：中点 ∈ 配对 voronoi list（`d < √8` 形态；
  第一波冻结件 `p24_mid_mem_voronoiList`（`d < √2` 形态）的泛化私拷，
  合并时二取一）；
- `p24_omega1_eq_mid`：ω₁ = 棱中点——配对胞 S 内 `dist(u0,·)` 在中点处取
  唯一最小值 `d/2`（S ⊆ bis(u0,u1) 等距 + 三角不等式下界 + 件 3 唯一性），
  `closestPoint` 的 ε-选取被唯一性锁定为中点；
- `p24_hl_trunc2_lt_two`：叶四元组 `vl`（`truncateSimplex 1 vl = [u0,u1]`）的
  mate 三点 `{u0,u1,v}` 外接半径严格 < 2（B2 杀死链的可证内核：`p24_tri_gamma`
  给 `r₃² = d²/4 + w²`，三重点非空任取 `x*`，其三点等距把 `x*` 钉在外轴线上
  `ζ⬝P = w·h`，饱和球界 `‖x* − u0‖ < 2` 经正交分解给 `‖ζ‖² + d²/4 < 4`，
  Cauchy–Schwarz `|w·h| ≤ ‖ζ‖·h` 合成 `r₃² < 4`）。路线图原定 `r₃ < √2` 目标
  不可达（近正则 Delaunay 四面体反例，见波报告），情形分叉时 `r₃ ≥ √2` 的
  叶走 mcell 2 支。 -/

/-- 中点平行四边形恒等式：`4·dist(p,w)² = 2(dist(w,u0)² + dist(w,u1)²) −
dist(u0,u1)²`（p = 中点；对一切 u0 u1 w 成立；第一波 `p24_mid_margin` 的
恒等式核，无假设形态）。 -/
private theorem p24_pgram_mid (u0 u1 w : V3) :
    4 * dist (u0 + (1 / 2 : ℝ) • (u1 - u0)) w ^ 2
      = 2 * (dist w u0 ^ 2 + dist w u1 ^ 2) - dist u0 u1 ^ 2 := by
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
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
  have e2 : dist u0 u1 ^ 2 = inner ℝ (u0 - w) (u0 - w)
      - 2 * inner ℝ (u0 - w) (u1 - w) + inner ℝ (u1 - w) (u1 - w) := by
    have h3 : dist u0 u1 = ‖(u0 - w) - (u1 - w)‖ := by
      rw [dist_eq_norm]; congr 1; module
    rw [h3, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  have n1 : ‖u0 - w‖ = dist w u0 := by rw [dist_eq_norm, norm_sub_rev]
  have n2 : ‖u1 - w‖ = dist w u1 := by rw [dist_eq_norm, norm_sub_rev]
  have n3 : ‖(u0 - w) + (u1 - w)‖ ^ 2
      = inner ℝ ((u0 - w) + (u1 - w)) ((u0 - w) + (u1 - w)) :=
    (real_inner_self_eq_norm_sq _).symm
  have h4 : dist p w ^ 2 = ‖(u0 - w) + (u1 - w)‖ ^ 2 / 4 := by
    rw [h2]; field_simp; ring
  rw [h4, n3, e1, e2]
  rw [real_inner_self_eq_norm_sq (u0 - w), real_inner_self_eq_norm_sq (u1 - w), n1, n2]
  field_simp
  linarith

/-- margin 的平方形态（无 d 假设）：`4 − (d/2)² ≤ dist(p,w)²`
（packing 两两距离 ≥ 2 + `p24_pgram_mid`）。 -/
private theorem p24_mid_margin_sq (V : Set V3) (u0 u1 w : V3) (hp : Packing V)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hw : w ∈ V) (hw0 : w ≠ u0) (hw1 : w ≠ u1) :
    4 - (dist u0 u1 / 2) ^ 2 ≤ dist (u0 + (1 / 2 : ℝ) • (u1 - u0)) w ^ 2 := by
  have apol := p24_pgram_mid u0 u1 w
  have hge0 : 2 ≤ dist w u0 := hp.dist_ge_two hw hu0 hw0
  have hge1 : 2 ≤ dist w u1 := hp.dist_ge_two hw hu1 hw1
  have hq0 : 4 ≤ dist w u0 ^ 2 := by nlinarith
  have hq1 : 4 ≤ dist w u1 ^ 2 := by nlinarith
  have hsq2 : (dist u0 u1 / 2) ^ 2 = dist u0 u1 ^ 2 / 4 := by ring
  linarith

/-- 到棱两端均为 `dist u0 u1 / 2` 的点必为中点
（`p24_pgram_mid` 右端零化 + `dist_eq_zero`）。 -/
private theorem p24_mid_eq_of_dist {u0 u1 y : V3}
    (h0 : dist y u0 = dist u0 u1 / 2) (h1 : dist y u1 = dist u0 u1 / 2) :
    y = u0 + (1 / 2 : ℝ) • (u1 - u0) := by
  have apol := p24_pgram_mid u0 u1 y
  rw [h0, h1] at apol
  have hsq2 : (dist u0 u1 / 2) ^ 2 = dist u0 u1 ^ 2 / 4 := by ring
  rw [hsq2] at apol
  have h4 : dist (u0 + (1 / 2 : ℝ) • (u1 - u0)) y ^ 2 = 0 := by linarith
  have hzero : dist (u0 + (1 / 2 : ℝ) • (u1 - u0)) y = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
  exact (dist_eq_zero.mp hzero).symm

/-- 中点落在配对 voronoi list 内（`d < √8` 形态；第一波冻结件
`p24_mid_mem_voronoiList`（`d < √2` 形态）的泛化私拷，合并时二取一）：
margin 平方形态 + `d/2 < √(4 − (d/2)²)` 严格链 + 两闭胞分情况。 -/
private theorem p24_mid_mem_voronoiList_sqrt8 (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hd8 : dist u0 u1 < Real.sqrt 8) :
    u0 + (1 / 2 : ℝ) • (u1 - u0) ∈ voronoiList V [u0, u1] := by
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hpu0 : dist p u0 = dist u0 u1 / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show dist u0 u1 = ‖u1 - u0‖ from by rw [dist_eq_norm, norm_sub_rev]]
    ring
  have hpu1 : dist p u1 = dist u0 u1 / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u1 = (1 / 2 : ℝ) • (u0 - u1) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show dist u0 u1 = ‖u0 - u1‖ from by rw [dist_eq_norm]]
    ring
  have hdpos : (0:ℝ) ≤ dist u0 u1 := dist_nonneg
  have hd2 : dist u0 u1 ^ 2 < 8 := by
    have hs8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    nlinarith [hd8, hs8, hdpos]
  have hsq2 : (dist u0 u1 / 2) ^ 2 = dist u0 u1 ^ 2 / 4 := by ring
  have hhalf : (dist u0 u1 / 2) ^ 2 < 4 - (dist u0 u1 / 2) ^ 2 := by
    rw [hsq2]; linarith
  have hstrict : dist u0 u1 / 2 < Real.sqrt (4 - (dist u0 u1 / 2) ^ 2) := by
    have hdpos2 : (0:ℝ) ≤ dist u0 u1 / 2 := by linarith
    have e1 : Real.sqrt ((dist u0 u1 / 2) ^ 2) < Real.sqrt (4 - (dist u0 u1 / 2) ^ 2) :=
      Real.sqrt_lt_sqrt (sq_nonneg (dist u0 u1 / 2)) hhalf
    have e2 : Real.sqrt ((dist u0 u1 / 2) ^ 2) = dist u0 u1 / 2 := by
      rw [Real.sqrt_sq_eq_abs (dist u0 u1 / 2), abs_of_nonneg hdpos2]
    linarith
  -- margin（平方形态的 sqrt 包装；对棱外任一 packing 点）
  have hmargin : ∀ w : V3, w ∈ V → w ≠ u0 → w ≠ u1 →
      Real.sqrt (4 - (dist u0 u1 / 2) ^ 2) ≤ dist p w := by
    intro w hw hw0 hw1
    have hm := p24_mid_margin_sq V u0 u1 w hp hu0 hu1 hw hw0 hw1
    have hnpos : (0:ℝ) ≤ dist p w := dist_nonneg
    have hsqrtle : Real.sqrt (4 - (dist u0 u1 / 2) ^ 2) ≤ Real.sqrt (dist p w ^ 2) :=
      Real.sqrt_le_sqrt hm
    rw [Real.sqrt_sq_eq_abs (dist p w), abs_of_nonneg hnpos] at hsqrtle
    exact hsqrtle
  rw [p24_voronoiList_pair V u0 u1]
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
      exact le_trans (le_of_lt hstrict) (hmargin w hw hw0 hw1)
  · rw [voronoiClosed, Set.mem_setOf_eq]
    intro w hw
    by_cases hw0 : w = u0
    · subst hw0
      rw [hpu1, hpu0]
    by_cases hw1 : w = u1
    · subst hw1
      exact le_refl _
    · rw [hpu1]
      exact le_trans (le_of_lt hstrict) (hmargin w hw hw0 hw1)

/-- ω₁ = 棱中点：`omegaListN V [u0, u1] 1 = u0 + (1/2)•(u1 − u0)`。
配对胞 S（两闭 Voronoi 胞之交）内任一点与 u0、u1 等距，三角不等式给
`dist(u0,·) ≥ d/2`；中点 ∈ S 取值恰 `d/2`；最小值点由
`p24_mid_eq_of_dist` 唯一，故 `closestPoint S u0` 的 ε-选取必为中点。
（叶三元组形态经 `OMEGA_LIST_N_LEMMA` 传输：`omegaListN V vl 1 =
omegaListN V (truncateSimplex 1 vl) 1`。） -/
private theorem p24_omega1_eq_mid (V : Set V3) (u0 u1 : V3) (hs : saturated V)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hd8 : dist u0 u1 < Real.sqrt 8) :
    omegaListN V [u0, u1] 1 = u0 + (1 / 2 : ℝ) • (u1 - u0) := by
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have htr : truncateSimplex 1 [u0, u1] = [u0, u1] := by
    rw [truncateSimplex1_pair [u0, u1] (by simp)]
    simp [elV]
  have hhd : hdV [u0, u1] = u0 := rfl
  -- 胞上等距 + 下界
  have hS : ∀ z ∈ voronoiList V [u0, u1],
      dist z u0 = dist z u1 ∧ dist u0 u1 / 2 ≤ dist u0 z := by
    intro z hz
    rw [p24_voronoiList_pair V u0 u1] at hz
    obtain ⟨hz0, hz1⟩ := hz
    rw [voronoiClosed, Set.mem_setOf_eq] at hz0 hz1
    have heq : dist z u0 = dist z u1 := le_antisymm (hz0 u1 hu1) (hz1 u0 hu0)
    have htri : dist u0 u1 ≤ dist u0 z + dist z u1 := dist_triangle u0 z u1
    rw [← heq, dist_comm z u0] at htri
    exact ⟨heq, by linarith⟩
  have hpmem : p ∈ voronoiList V [u0, u1] :=
    p24_mid_mem_voronoiList_sqrt8 V u0 u1 hp hu0 hu1 hne hd8
  have hpu0 : dist u0 p = dist u0 u1 / 2 := by
    rw [dist_comm u0 p, dist_eq_norm]
    have h1 : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show dist u0 u1 = ‖u1 - u0‖ from by rw [dist_eq_norm, norm_sub_rev]]
    ring
  have hpmin : ∀ z ∈ voronoiList V [u0, u1], dist u0 p ≤ dist u0 z := by
    intro z hz
    linarith [(hS z hz).2, hpu0]
  -- 唯一性
  have key : ∀ y : V3, (y ∈ voronoiList V [u0, u1] ∧
      ∀ z ∈ voronoiList V [u0, u1], dist u0 y ≤ dist u0 z) → y = p := by
    intro y hy
    obtain ⟨hyS, hymin⟩ := hy
    obtain ⟨hyeq, hylow⟩ := hS y hyS
    have hy2 : dist u0 y ≤ dist u0 u1 / 2 := by
      have h1 : dist u0 y ≤ dist u0 p := hymin p hpmem
      rw [hpu0] at h1
      exact h1
    have hye : dist y u0 = dist u0 u1 / 2 := by
      rw [dist_comm y u0]; linarith
    have hye1 : dist y u1 = dist u0 u1 / 2 := by
      rw [← hyeq, dist_comm y u0]; linarith
    exact p24_mid_eq_of_dist hye hye1
  show closestPoint (voronoiList V (truncateSimplex 1 [u0, u1])) (hdV [u0, u1]) = p
  rw [htr, hhd]
  show (Classical.epsilon fun y : V3 => y ∈ voronoiList V [u0, u1] ∧
      ∀ z ∈ voronoiList V [u0, u1], dist u0 y ≤ dist u0 z) = p
  exact key _ (Classical.epsilon_spec
    (p := fun y : V3 => y ∈ voronoiList V [u0, u1] ∧
      ∀ z ∈ voronoiList V [u0, u1], dist u0 y ≤ dist u0 z)
    ⟨p, hpmem, hpmin⟩)

/-- B2 杀死（可证内核）：叶四元组 `vl`（`barV V 3 vl ∧ truncateSimplex 1 vl =
[u0, u1]`）的 mate 三点 `{u0, u1, elV vl 2}` 外接半径严格 < 2。
链（全初等）：`p24_tri_gamma` 给 `r₃² = d²/4 + w²`（w = 外心垂坐标·垂距，
P = v 的垂分量，h = ‖P‖ > 0）；三重点 `voronoiList V [u0,u1,v] ≠ ∅`
（`BARV_IMP_VORONOI_LIST_NOT_EMPTY` + `TRUNCATE_SIMPLEX_BARV`）任取 `x*`，
三点等距把 `x*` 钉在 `{u0,u1,v}` 的外轴线上：`ζ⬝P = w·h`（ζ = x* − 中点）；
饱和球界 `‖x* − u0‖ < 2` 经正交分解（`ζ ⊥ e3`）给 `‖ζ‖² + d²/4 < 4`；
Cauchy–Schwarz `|w·h| ≤ ‖ζ‖·h` 合成 `w² ≤ ‖ζ‖²`，故 `r₃² ≤ d²/4 + ‖ζ‖² < 4`。
（路线图原定目标 `r₃ < √2` 不可达：近正则 Delaunay 四面体——棱距
d ∈ [2, 2√2)、四点外接半径 < 2——的第三点外接半径可达 ~1.58 > √2；见波
报告。情形分叉时 `r₃ ≥ √2` 的叶走 mcell 2 支，本件给出该支的半径上界。） -/
private theorem p24_hl_trunc2_lt_two (V : Set V3) (u0 u1 : V3) (vl : List V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar3 : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1]) :
    hl (truncateSimplex 2 vl) < 2 := by
  have hvlen : vl.length = 4 := hbar3.1
  have hu01 : u0 ≠ u1 := hne
  -- mate 三点列表 ul := truncateSimplex 2 vl
  set ul := truncateSimplex 2 vl with huldef
  have hbar2 : barV V 2 ul := TRUNCATE_SIMPLEX_BARV V 2 3 vl hbar3 (by omega)
  have htr1 : setOfList (truncateSimplex 1 ul) = ({u0, u1} : Set V3) := by
    rw [huldef, TRUNCATE_TRUNCATE_SIMPLEX vl 1 2 (by omega) (by omega), htr]
    ext x
    simp [setOfList]
  obtain ⟨-, -, hnc⟩ := p24_REUHADY_extract hp hbar2 htr1 rfl
  have hv0 : elV ul 2 ≠ u0 := fun hc => hnc (collinear3_pair_left hc)
  have hv1 : elV ul 2 ≠ u1 := fun hc => hnc (collinear3_pair_right hc)
  have hsetul : setOfList ul = ({u0, u1, elV ul 2} : Set V3) :=
    p24_setOfList_pair2 hbar2 htr1 rfl
  -- 外接半径形态
  have hrad3 : hl ul = radV ({u0, u1, elV ul 2} : Set V3) := by
    rw [show hl ul = radV (setOfList ul) from rfl, hsetul]
  -- 标架
  have hu0u1n : (u1 - u0 : V3) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu01)
  obtain ⟨e1, e2, e3, hon, hax0⟩ := exists_on3_eq_smul (u1 - u0) hu0u1n
  have haxd : (u1 - u0 : V3) = dist u0 u1 • e3 := by
    have hn : ‖u1 - u0‖ = dist u0 u1 := (dist_eq_norm u1 u0).symm.trans (dist_comm u1 u0)
    rw [hn] at hax0
    exact hax0
  have h33 : e3 ⬝ᵥ e3 = 1 := hon.2.2.1
  have he3n : ∀ r : ℝ, ‖((r : ℝ) • e3 : V3)‖ ^ 2 = r ^ 2 := by
    intro r
    have h0 : ‖((r : ℝ) • e3 : V3)‖ ^ 2 = ((r : ℝ) • e3 : V3) ⬝ᵥ ((r : ℝ) • e3 : V3) :=
      norm_sq_eq_dot _
    simp only [h0, WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, h33]
    ring
  -- tri_gamma 坐标数据
  obtain ⟨h, t, w, hhpos, hteq, hPn, hrad, hgam, hnn⟩ :=
    p24_tri_gamma u0 u1 (elV ul 2) hon haxd hu01 hnc
      (p24_cc_exists u0 u1 (elV ul 2) hu01 hnc)
  rw [hteq] at hPn
  set P : V3 := (elV ul 2 - u0 : V3) - t • e3 with hPdef
  have hPe3 : P ⬝ᵥ e3 = 0 := by
    rw [hPdef, WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, hteq, h33]
    ring
  have he3P : e3 ⬝ᵥ P = 0 := by rw [dotProduct_comm]; exact hPe3
  have hPnorm : ‖P‖ = h := by rw [hPdef]; exact hPn
  -- 三重点非空，取 x*
  have hTne : voronoiList V ul ≠ ∅ := BARV_IMP_VORONOI_LIST_NOT_EMPTY V ul 2 hbar2
  obtain ⟨x, hxT⟩ := Set.nonempty_iff_ne_empty.mpr hTne
  have hxT' : x ∈ ⋂₀ {voronoiClosed V z | z ∈ setOfList ul} := hxT
  -- u0、u1 ∈ setOfList ul（经 htr 与 EL_TRUNCATE_SIMPLEX 的坐标读出）
  have hpair01 : [u0, u1] = [elV vl 0, elV vl 1] := by
    rw [← htr, truncateSimplex1_pair vl (by omega)]
  injection hpair01 with h01 hrest
  injection hrest with h11
  have he0ul : elV ul 0 = elV vl 0 := EL_TRUNCATE_SIMPLEX vl 2 0 (by omega) (by omega)
  have he1ul : elV ul 1 = elV vl 1 := EL_TRUNCATE_SIMPLEX vl 2 1 (by omega) (by omega)
  have hu0ul : u0 ∈ setOfList ul := by
    rw [h01, ← he0ul]
    exact p24_elV_mem (by have := hbar2.1; omega)
  have hu1ul : u1 ∈ setOfList ul := by
    rw [h11, ← he1ul]
    exact p24_elV_mem (by have := hbar2.1; omega)
  have hx0 : x ∈ voronoiClosed V u0 :=
    hxT' (voronoiClosed V u0) (Set.mem_image_of_mem _ hu0ul)
  have hx1 : x ∈ voronoiClosed V u1 :=
    hxT' (voronoiClosed V u1) (Set.mem_image_of_mem _ hu1ul)
  have hxv : x ∈ voronoiClosed V (elV ul 2) :=
    hxT' (voronoiClosed V (elV ul 2))
      (Set.mem_image_of_mem _ (p24_elV_mem (by have := hbar2.1; omega)))
  -- x* 的成员性与三点等距
  have hvnul : voronoiNondg V ul :=
    hbar2.2 ul ⟨⟨[], by rw [List.append_nil]⟩, by have := hbar2.1; omega⟩
  have hvV : elV ul 2 ∈ V := hvnul.2.1 (p24_elV_mem (by have := hbar2.1; omega))
  have hxu0v : dist x u0 = dist x (elV ul 2) := le_antisymm (hx0 _ hvV) (hxv _ hu0)
  have hxu01 : dist x u0 = dist x u1 := le_antisymm (hx0 _ hu1) (hx1 _ hu0)
  -- ζ := x* − 中点 的坐标代数
  set zeta : V3 := x - (u0 + (1 / 2 : ℝ) • (u1 - u0)) with hzdef
  -- (a) zeta ⊥ 轴：与 u0、u1 等距
  have hsq01 : ‖(x - u0 : V3)‖ ^ 2 = ‖(x - u1 : V3)‖ ^ 2 := by
    rw [← dist_eq_norm x u0, ← dist_eq_norm x u1, hxu01]
  have k1 := p24_sq_eq_doteq (y := (x - u0 : V3)) (z := (u1 - u0 : V3)) (by
    rw [show ((x - u0 : V3) - (u1 - u0 : V3)) = (x - u1 : V3) from by module]
    exact hsq01)
  have k1' : (x - u0 : V3) ⬝ᵥ (u1 - u0 : V3) = ‖u1 - u0‖ ^ 2 / 2 := by linarith
  have k2 : ((1 / 2 : ℝ) • (u1 - u0 : V3)) ⬝ᵥ (u1 - u0 : V3) = ‖u1 - u0‖ ^ 2 / 2 := by
    rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, norm_sq_eq_dot]
    ring
  have kz : zeta ⬝ᵥ (u1 - u0 : V3) = 0 := by
    have hzo : (zeta : V3) + (1 / 2 : ℝ) • (u1 - u0 : V3) = (x - u0 : V3) := by
      rw [hzdef]; module
    have e0 : zeta ⬝ᵥ (u1 - u0 : V3)
        + ((1 / 2 : ℝ) • (u1 - u0 : V3)) ⬝ᵥ (u1 - u0 : V3)
        = (x - u0 : V3) ⬝ᵥ (u1 - u0 : V3) := by
      rw [← hzo, WithLp.ofLp_add, add_dotProduct]
    rw [k1'] at e0
    rw [k2] at e0
    linarith
  have hzetae3 : zeta ⬝ᵥ e3 = 0 := by
    have h1 : zeta ⬝ᵥ (u1 - u0 : V3) = dist u0 u1 * (zeta ⬝ᵥ e3) := by
      rw [haxd, WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul]
    rw [h1] at kz
    have hd0 : (dist u0 u1 : ℝ) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (hp.dist_ge_two hu0 hu1 hne))
    exact (mul_eq_zero.mp kz).resolve_left hd0
  -- (b) zeta ⬝ P = w * h：与 v 等距
  have hsq0v : ‖(x - u0 : V3)‖ ^ 2 = ‖(x - (elV ul 2 : V3))‖ ^ 2 := by
    rw [← dist_eq_norm x u0, ← dist_eq_norm x (elV ul 2), hxu0v]
  have k3 := p24_sq_eq_doteq (y := (x - u0 : V3)) (z := (elV ul 2 - u0 : V3)) (by
    rw [show ((x - u0 : V3) - (elV ul 2 - u0 : V3)) = (x - (elV ul 2 : V3)) from by module]
    exact hsq0v)
  have hvu0P : (elV ul 2 - u0 : V3) = P + t • e3 := by rw [hPdef]; module
  have hxu0z : (x - u0 : V3) = zeta + (dist u0 u1 / 2) • e3 := by
    have e0 : (x - u0 : V3) = zeta + (1 / 2 : ℝ) • (u1 - u0 : V3) := by rw [hzdef]; module
    rw [e0, haxd, smul_smul, show (1:ℝ) / 2 * dist u0 u1 = dist u0 u1 / 2 from by ring]
  have kvnorm : ‖(elV ul 2 - u0 : V3)‖ ^ 2 = h ^ 2 + t ^ 2 := by
    rw [hvu0P]
    rw [p24_norm_sq_of_orth (x := P) (y := ((t : ℝ) • e3)) (by
      rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul, hPe3, mul_zero])]
    rw [he3n t, hPnorm]
  have k4 : zeta ⬝ᵥ P = w * h := by
    have e1 : (x - u0 : V3) ⬝ᵥ (elV ul 2 - u0 : V3) = zeta ⬝ᵥ P + (dist u0 u1 / 2) * t := by
      rw [hxu0z, hvu0P]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hzetae3, he3P, h33]
      ring
    rw [e1, kvnorm] at k3
    have hdt : (dist u0 u1 / 2) * t = dist u0 u1 * t / 2 := by ring
    rw [hdt] at k3
    linarith
  -- (c) 正交分解 + 饱和球界：‖zeta‖² + (d/2)² < 4
  have hdecomp : ‖(x - u0 : V3)‖ ^ 2 = ‖zeta‖ ^ 2 + (dist u0 u1 / 2) ^ 2 := by
    rw [hxu0z, p24_norm_sq_of_orth (x := zeta)
      (y := ((dist u0 u1 / 2) • e3 : V3)) (by
      rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul, hzetae3, mul_zero]),
      he3n (dist u0 u1 / 2)]
  obtain ⟨y, hyV, hyd⟩ := hs x
  have hball : ‖zeta‖ ^ 2 + (dist u0 u1 / 2) ^ 2 < 4 := by
    have h2 : dist x u0 < 2 := lt_of_le_of_lt (hx0 y hyV) hyd
    have hsqx : ‖(x - u0 : V3)‖ ^ 2 < 4 := by
      have h3 : ‖(x - u0 : V3)‖ = dist x u0 := dist_eq_norm x u0
      have h4 : (0:ℝ) ≤ dist x u0 := dist_nonneg
      rw [h3]
      nlinarith [h2, h4]
    rw [← hdecomp]
    exact hsqx
  -- (d) Cauchy–Schwarz：|w·h| ≤ ‖zeta‖·h
  have hwbound : w ^ 2 ≤ ‖zeta‖ ^ 2 := by
    have hcs : |w * h| ≤ ‖zeta‖ * ‖P‖ := by
      have h0 := abs_real_inner_le_norm (x := zeta) (y := P)
      rwa [inner_eq_dot, k4] at h0
    rw [hPnorm] at hcs
    have h0 : |w * h| = |w| * h := by rw [abs_mul, abs_of_pos hhpos]
    have h1 : |w| * h ≤ ‖zeta‖ * h := by rw [← h0]; exact hcs
    have h2 : |w| ≤ ‖zeta‖ := le_of_mul_le_mul_right h1 hhpos
    have h3 : |w| ^ 2 = w ^ 2 := by
      rcases le_or_gt 0 w with hn | hpw
      · rw [abs_of_nonneg hn]
      · rw [abs_of_nonpos (le_of_lt hpw)]; ring
    rw [← h3]
    nlinarith [h2, abs_nonneg w, norm_nonneg zeta]
  -- (e) 结论：r₃² < 4
  have hsq4 : (dist u0 u1 / 2) ^ 2 = dist u0 u1 ^ 2 / 4 := by ring
  have hrad4 : radV ({u0, u1, elV ul 2} : Set V3) ^ 2 < 4 := by
    rw [hrad]
    nlinarith [hball, hwbound, hsq4]
  rw [hrad3]
  nlinarith [hrad4, hnn]

/-- W-楔代数辅助件 1：等距方程的锥系数 S-等式（正号版）。
`ξ = (x,y)`（圆心坐标）的斜基负系数 `α = (x−k)/(2k)+y/d`、`β =
(x−k)/(2k)−y/d` 满足 `ρ²α+qβ = (x²+(y+d/2)²)/2 − ρ²`（`hC` 为共圆等距
方程；两步证明：分母清空恒等式 + `hC` 差恰为二分之一）。 -/
private theorem p24_wedge_S_pos (d k x y a b : ℝ) (hd0 : d ≠ 0) (hk : k ≠ 0)
    (ha : a = (x - k) / (2 * k) + y / d) (hb : b = (x - k) / (2 * k) - y / d)
    (hC : 2 * k * x = x ^ 2 + y ^ 2 - d ^ 2 / 4) :
    (k ^ 2 + d ^ 2 / 4) * a + (k ^ 2 - d ^ 2 / 4) * b
      = (x ^ 2 + (y + d / 2) ^ 2) / 2 - (k ^ 2 + d ^ 2 / 4) := by
  subst ha; subst hb
  have L : (k ^ 2 + d ^ 2 / 4) * ((x - k) / (2 * k) + y / d)
        + (k ^ 2 - d ^ 2 / 4) * ((x - k) / (2 * k) - y / d)
      = k * (x - k) + (d / 2) * y := by
    field_simp; ring
  rw [L]
  linear_combination hC / 2

private theorem p24_wedge_S_neg (d k x y a b : ℝ) (hd0 : d ≠ 0) (hk : k ≠ 0)
    (ha : a = (x - k) / (2 * k) + y / d) (hb : b = (x - k) / (2 * k) - y / d)
    (hC : 2 * k * x = x ^ 2 + y ^ 2 - d ^ 2 / 4) :
    (k ^ 2 + d ^ 2 / 4) * b + (k ^ 2 - d ^ 2 / 4) * a
      = (x ^ 2 + (y - d / 2) ^ 2) / 2 - (k ^ 2 + d ^ 2 / 4) := by
  subst ha; subst hb
  have L : (k ^ 2 + d ^ 2 / 4) * ((x - k) / (2 * k) - y / d)
        + (k ^ 2 - d ^ 2 / 4) * ((x - k) / (2 * k) + y / d)
      = k * (x - k) - (d / 2) * y := by
    field_simp; ring
  rw [L]
  linear_combination hC / 2

private theorem p24_wedge_coef_pos (ρ2 q z w : ℝ) (hr2 : 0 < ρ2) (hq : q < 0)
    (hXpos : 0 < ρ2 ^ 2 - q ^ 2) (hz : 0 < ρ2 * z + q * w) (hw : 0 < ρ2 * w + q * z)
    (hX0 : ρ2 ^ 2 - q ^ 2 ≠ 0) : 0 < z ∧ 0 < w := by
  have E1 : (ρ2 ^ 2 - q ^ 2) * z = ρ2 * (ρ2 * z + q * w) + (-q) * (ρ2 * w + q * z) := by
    ring
  have E2 : (ρ2 ^ 2 - q ^ 2) * w = ρ2 * (ρ2 * w + q * z) + (-q) * (ρ2 * z + q * w) := by
    ring
  have hqpos : 0 < -q := by linarith
  have tz : 0 < (ρ2 ^ 2 - q ^ 2) * z := by
    rw [E1]; linarith [mul_pos hr2 hz, mul_pos hqpos hw]
  have tw : 0 < (ρ2 ^ 2 - q ^ 2) * w := by
    rw [E2]; linarith [mul_pos hr2 hw, mul_pos hqpos hz]
  refine ⟨?_, ?_⟩
  · have hz' : z = (ρ2 ^ 2 - q ^ 2) * z / (ρ2 ^ 2 - q ^ 2) := by
      field_simp
    rw [hz']; exact div_pos tz hXpos
  · have hw' : w = (ρ2 ^ 2 - q ^ 2) * w / (ρ2 ^ 2 - q ^ 2) := by
      field_simp
    rw [hw']; exact div_pos tw hXpos

/-- **情形 A · W-楔代数（纯实数核）**。坐标形态（以圆心为原点的 (S,t)-坐标，
S 轴 = 棱的垂直方向、t 轴 = 棱轴方向）：`u0=(0,−d/2)`、`u1=(0,d/2)`、
`v=(n,tv)`、`w=(μn,tw)`、圆心 `(k,0)`、半径² `= k²+d²/4 < 2`。
`hC2/hC3` 是 `v`、`w` 与 `u0` 的共圆等距方程（圆心在弦 `u0u1` 的垂直平分线
`t=0` 上，故只此两条）；五个 `≥ 4` 是四点到 `u0,u1` 的弦与 `dist(v,w)` 的弦
（packing 两两距离 ≥ 2 的平方形态）。
结论 `False`：`ξ₁ = u0−c`、`ξ₂ = u1−c`、`ξ₃ = v−c`、`ξ₄ = w−c` 两两内积
`≤ ρ²−2 < 0`，故 `ξ₃,ξ₄` 同落 `ξ₁,ξ₂` 的严格负锥；斜基坐标解出
`α = x/(2k)+y/d` 型负系数后，w 的锥系数全正（Rankin 判别式）给
`ξ₃·ξ₄ = α₄·S₃ + β₄·S₄ > 0`，于是 `dist(v,w)² = 2ρ² − 2ξ₃·ξ₄ < 2ρ² < 4`，
与弦 `h34` 矛盾（半径 < √2 的圆上四点不可能两两弦 ≥ 2）。 -/
private theorem p24_wedge_quad_kill (d k n μ tv tw : ℝ)
    (hd2 : 2 ≤ d) (hk : k ≠ 0)
    (hrho : k ^ 2 + d ^ 2 / 4 < 2)
    (hC2 : 2 * k * n = n ^ 2 + tv ^ 2 - d ^ 2 / 4)
    (hC3 : 2 * k * (μ * n) = (μ * n) ^ 2 + tw ^ 2 - d ^ 2 / 4)
    (h03 : 4 ≤ n ^ 2 + (tv + d / 2) ^ 2) (h13 : 4 ≤ n ^ 2 + (tv - d / 2) ^ 2)
    (h04 : 4 ≤ (μ * n) ^ 2 + (tw + d / 2) ^ 2)
    (h14 : 4 ≤ (μ * n) ^ 2 + (tw - d / 2) ^ 2)
    (h34 : 4 ≤ (μ * n - n) ^ 2 + (tw - tv) ^ 2) : False := by
  have hd0 : (0:ℝ) < d := by nlinarith
  have hd0ne : (d:ℝ) ≠ 0 := ne_of_gt hd0
  have hd2pos : 0 < d ^ 2 := by nlinarith
  have hq : k ^ 2 - d ^ 2 / 4 < 0 := by
    have hd4 : 4 ≤ d ^ 2 := by nlinarith
    linarith
  have hr2pos : 0 < k ^ 2 + d ^ 2 / 4 := by
    have h2 : 0 < k ^ 2 := sq_pos_of_ne_zero hk
    exact add_pos h2 (div_pos hd2pos (by norm_num))
  have hXpos : 0 < (k ^ 2 + d ^ 2 / 4) ^ 2 - (k ^ 2 - d ^ 2 / 4) ^ 2 := by
    have e : (k ^ 2 + d ^ 2 / 4) ^ 2 - (k ^ 2 - d ^ 2 / 4) ^ 2 = k ^ 2 * d ^ 2 := by ring
    rw [e]; exact mul_pos (sq_pos_of_ne_zero hk) hd2pos
  -- 锥系数（helper 展开）与正性（弦 + ρ² < 2）
  -- 负锥坐标（斜基 (ξ₁,ξ₂) 下 ξ₃, ξ₄ 的系数）
  set a3 := (n - k) / (2 * k) + tv / d with ha3
  set b3 := (n - k) / (2 * k) - tv / d with hb3
  set a4 := (μ * n - k) / (2 * k) + tw / d with ha4
  set b4 := (μ * n - k) / (2 * k) - tw / d with hb4
  -- S-等式（helper 展开）与正性（弦 + ρ² < 2）
  have S3 := p24_wedge_S_pos d k n tv a3 b3 hd0ne hk ha3 hb3 hC2
  have S4 := p24_wedge_S_neg d k n tv a3 b3 hd0ne hk ha3 hb3 hC2
  have S5 := p24_wedge_S_pos d k (μ * n) tw a4 b4 hd0ne hk ha4 hb4 hC3
  have S6 := p24_wedge_S_neg d k (μ * n) tw a4 b4 hd0ne hk ha4 hb4 hC3
  have S3pos : 0 < (k ^ 2 + d ^ 2 / 4) * a3 + (k ^ 2 - d ^ 2 / 4) * b3 := by
    linarith [S3, h03, hrho]
  have S4pos : 0 < (k ^ 2 + d ^ 2 / 4) * b3 + (k ^ 2 - d ^ 2 / 4) * a3 := by
    linarith [S4, h13, hrho]
  have S5pos : 0 < (k ^ 2 + d ^ 2 / 4) * a4 + (k ^ 2 - d ^ 2 / 4) * b4 := by
    linarith [S5, h04, hrho]
  have S6pos : 0 < (k ^ 2 + d ^ 2 / 4) * b4 + (k ^ 2 - d ^ 2 / 4) * a4 := by
    linarith [S6, h14, hrho]
  -- w 的锥坐标全正（Rankin 判别式）
  have hX0 : (k ^ 2 + d ^ 2 / 4) ^ 2 - (k ^ 2 - d ^ 2 / 4) ^ 2 ≠ 0 := ne_of_gt hXpos
  obtain ⟨ha4pos, hb4pos⟩ := p24_wedge_coef_pos (k ^ 2 + d ^ 2 / 4) (k ^ 2 - d ^ 2 / 4)
    a4 b4 hr2pos hq hXpos S5pos S6pos hX0
  -- 共圆读出：‖ξ₃‖² = ‖ξ₄‖² = ρ²（hC2/hC3）
  have n3 : (n - k) ^ 2 + tv ^ 2 = k ^ 2 + d ^ 2 / 4 := by
    have key : (n - k) ^ 2 + tv ^ 2 - (k ^ 2 + d ^ 2 / 4) = 0 := by
      have e : (n - k) ^ 2 + tv ^ 2 - (k ^ 2 + d ^ 2 / 4)
          = -(2 * k * n - (n ^ 2 + tv ^ 2 - d ^ 2 / 4)) := by ring
      rw [e, neg_eq_zero]; linarith [hC2]
    linarith [key]
  have n4 : (μ * n - k) ^ 2 + tw ^ 2 = k ^ 2 + d ^ 2 / 4 := by
    have key : (μ * n - k) ^ 2 + tw ^ 2 - (k ^ 2 + d ^ 2 / 4) = 0 := by
      have e : (μ * n - k) ^ 2 + tw ^ 2 - (k ^ 2 + d ^ 2 / 4)
          = -(2 * k * (μ * n) - ((μ * n) ^ 2 + tw ^ 2 - d ^ 2 / 4)) := by ring
      rw [e, neg_eq_zero]; linarith [hC3]
    linarith [key]
  -- 点积正性：ξ₃·ξ₄ = α₄·S3 + β₄·S4 > 0
  have c3x : n - k = k * (a3 + b3) := by rw [ha3, hb3]; field_simp; ring
  have c3y : tv = (d / 2) * (a3 - b3) := by rw [ha3, hb3]; field_simp; ring
  have c4x : μ * n - k = k * (a4 + b4) := by rw [ha4, hb4]; field_simp; ring
  have c4y : tw = (d / 2) * (a4 - b4) := by rw [ha4, hb4]; field_simp; ring
  have dotE : (n - k) * (μ * n - k) + tv * tw
      = (k ^ 2 + d ^ 2 / 4) * (a3 * a4 + b3 * b4)
        + (k ^ 2 - d ^ 2 / 4) * (a3 * b4 + b3 * a4) := by
    rw [c3x, c3y, c4x, c4y]; ring
  have dotF : (k ^ 2 + d ^ 2 / 4) * (a3 * a4 + b3 * b4)
        + (k ^ 2 - d ^ 2 / 4) * (a3 * b4 + b3 * a4)
      = a4 * ((k ^ 2 + d ^ 2 / 4) * a3 + (k ^ 2 - d ^ 2 / 4) * b3)
        + b4 * ((k ^ 2 + d ^ 2 / 4) * b3 + (k ^ 2 - d ^ 2 / 4) * a3) := by
    ring
  have dotpos : 0 < (n - k) * (μ * n - k) + tv * tw := by
    rw [dotE, dotF]; linarith [mul_pos ha4pos S3pos, mul_pos hb4pos S4pos]
  -- 终局：dist(v,w)² = 2ρ² − 2ξ₃·ξ₄ < 2ρ² < 4，与 h34 矛盾
  have flat : (μ * n - n) ^ 2 + (tw - tv) ^ 2
      = 2 * (k ^ 2 + d ^ 2 / 4) - 2 * ((n - k) * (μ * n - k) + tv * tw) := by
    have key : (μ * n - n) ^ 2 + (tw - tv) ^ 2
        - (2 * (k ^ 2 + d ^ 2 / 4) - 2 * ((n - k) * (μ * n - k) + tv * tw)) = 0 := by
      have e : (μ * n - n) ^ 2 + (tw - tv) ^ 2
          - (2 * (k ^ 2 + d ^ 2 / 4) - 2 * ((n - k) * (μ * n - k) + tv * tw))
        = ((n - k) ^ 2 + tv ^ 2 - (k ^ 2 + d ^ 2 / 4))
          + ((μ * n - k) ^ 2 + tw ^ 2 - (k ^ 2 + d ^ 2 / 4)) := by ring
      rw [e, n3, n4]; ring
    linarith [key]
  linarith [flat, dotpos, hrho, h34]

/-! ## 新件 1：p24_caseA_concyclic（共圆件） -/

/-- **情形 A · 共圆件**（2026-10-11 波，探针零错后落盘）：叶四元组
（`barV V 3 vl` + `truncateSimplex 1 vl = [u0, u1]`）+ 四点共面
（`Coplanar ℝ (setOfList vl)`）+ 情形 A 判别 `hl vl < √2` ⇒
`p24_wedge_quad_kill` 的输入形（标量坐标包 `∃ d k n μ tv tw`）。
路线（全初等，上波处方逐条落地）：
(1) PA12:1677 `VORONOI_LIST_3_SINGLETON_EXPLICIT` 直接给胞单点 `a`
（`hl vl = dist u0 a`，无需 p24_mid_*/p24_voronoiList_pair），胞成员对 V
两两夹逼给四点等距 `dist a z = hl vl`；
(2) 四点两两异走 barV 初始子列链：MHFTTZN1 给 `affDim (setOfList vl) = 3`，
任两点重合使 `setOfList vl ⊆ {p,q,r}` ⇒ vectorSpan finrank ≤ 2（共面），矛盾
（不走 packing 循环论证）；
(3) ON 标架 (e1,e2,e3)（e3 = 棱轴）：`A' = a − mid ⊥ e3`（等距读出，复刻
`p24_hl_trunc2_lt_two` 的 kz/hzetae3 模式）；`v` 的垂分量 `P`（`‖P‖ = n`，
`P = 0` 退化支经 `tv² = (d/2)² ⇒ v ∈ {u0,u1}` 矛盾）；
(4) 共面塌缩：`vectorSpan (setOfList vl) = span{u1−u0, v−u0}`（span 侧
`barV V 2 [u0,u1,v]` 经 MHFTTZN1 给 finrank = 2，⊥ 侧 coplanar finrank ≤ 2），
`w − u0 ∈ span{u1−u0, v−u0}` 读出 `w − mid = tw•e3 + μ•P`；
(5) 圆心 `c = mid + (k/n)•P`（`k = A'⬝P/n`；无需 `a` 的 affineSpan 成员——
`a − c ⊥ e3` 且 `⊥ P` 直接验证），Pythagoras 把
`r₄² = ‖a−u0‖² = ‖a−v‖² = ‖a−w‖²` 读成 hC2/hC3；`hrho` 经
`k² + d²/4 = ‖c−u0‖² ≤ r₄² < 2`；`k ≠ 0` 经 h03+h13 相加 ⊕ hrho 的
`d² < 8`。弦组 h03/h13/h04/h14/h34 = packing 两两距离 ≥ 2 的平方形态。 -/
private theorem p24_caseA_concyclic (V : Set V3) (u0 u1 : V3) (vl : List V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1])
    (hhl : hl vl < Real.sqrt 2) (hcp : Coplanar ℝ (setOfList vl)) :
    ∃ d k n μ tv tw : ℝ, 2 ≤ d ∧ k ≠ 0 ∧ k ^ 2 + d ^ 2 / 4 < 2 ∧
      2 * k * n = n ^ 2 + tv ^ 2 - d ^ 2 / 4 ∧
      2 * k * (μ * n) = (μ * n) ^ 2 + tw ^ 2 - d ^ 2 / 4 ∧
      4 ≤ n ^ 2 + (tv + d / 2) ^ 2 ∧ 4 ≤ n ^ 2 + (tv - d / 2) ^ 2 ∧
      4 ≤ (μ * n) ^ 2 + (tw + d / 2) ^ 2 ∧
      4 ≤ (μ * n) ^ 2 + (tw - d / 2) ^ 2 ∧
      4 ≤ (μ * n - n) ^ 2 + (tw - tv) ^ 2 := by
  -- 0. 四元组显式化 + u0/u1 识别
  obtain ⟨q0, q1, q2, q3, hvll⟩ := BARV_3_EXPLICIT V vl hbar
  subst hvll
  have htrq : truncateSimplex 1 [q0, q1, q2, q3] = [q0, q1] := by
    rw [truncateSimplex1_pair [q0, q1, q2, q3] (by norm_num)]
    simp [elV]
  have hpair01 : [u0, u1] = [q0, q1] := htr.symm.trans htrq
  injection hpair01 with e0 e1l
  injection e1l with e1 e1nil
  subst e0
  subst e1
  set v : V3 := q2 with hvdef
  set w : V3 := q3 with hwdef
  have hset : setOfList [u0, u1, v, w] = ({u0, u1, v, w} : Set V3) := by
    ext y
    simp [setOfList]
  have hu0s : u0 ∈ setOfList [u0, u1, v, w] := by simp [setOfList]
  have hu1s : u1 ∈ setOfList [u0, u1, v, w] := by simp [setOfList]
  have hvs : v ∈ setOfList [u0, u1, v, w] := by simp [setOfList]
  have hws : w ∈ setOfList [u0, u1, v, w] := by simp [setOfList]
  have hvn : voronoiNondg V [u0, u1, v, w] :=
    hbar.2 [u0, u1, v, w] ⟨⟨[], by rw [List.append_nil]⟩, by simp⟩
  have hsubV : setOfList [u0, u1, v, w] ⊆ V := hvn.2.1
  have hvV : v ∈ V := hsubV hvs
  have hwV : w ∈ V := hsubV hws
  -- 1. 四点两两异（MHFTTZN1 affDim = 3 vs 共面 vectorSpan ≤ 2 的维数矛盾）
  have hneS : (setOfList [u0, u1, v, w] : Set V3) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp ⟨u0, hu0s⟩
  have hd3 : affDim (setOfList [u0, u1, v, w]) = (3 : ℤ) :=
    MHFTTZN1 V [u0, u1, v, w] 3 hp hbar
  have hkey : ∀ p q r : V3, setOfList [u0, u1, v, w] ⊆ ({p, q, r} : Set V3) → False := by
    intro p q r hsub
    have hle : vectorSpan ℝ (setOfList [u0, u1, v, w])
        ≤ Submodule.span ℝ ({q - p, r - p} : Set V3) := by
      refine le_trans (vectorSpan_mono ℝ hsub) ?_
      rw [vectorSpan_eq_span_vsub_set_right ℝ (show p ∈ ({p, q, r} : Set V3) from by simp)]
      rw [Submodule.span_le]
      rintro z ⟨y, hy, rfl⟩
      rcases Set.mem_insert_iff.mp hy with hcy | hy
      · rw [hcy]; simp
      · rcases hy with hcy | hcy
        · rw [hcy]; exact Submodule.subset_span (by simp)
        · rw [hcy]; exact Submodule.subset_span (by simp)
    exfalso
    have hd3' := hd3
    rw [affDim, if_neg hneS] at hd3'
    norm_cast at hd3'
    have hfr : Module.finrank ℝ (vectorSpan ℝ (setOfList [u0, u1, v, w])) ≤ 2 := by
      refine le_trans (Submodule.finrank_mono hle) ?_
      exact p24_finrank_span_pair_le_two (q - p) (r - p)
    omega
  have hv0 : v ≠ u0 := by
    intro hc
    refine hkey u0 u1 w ?_
    rw [hset]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rw [hc] at hy
    tauto
  have hv1 : v ≠ u1 := by
    intro hc
    refine hkey u0 u1 w ?_
    rw [hset]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rw [hc] at hy
    tauto
  have hw0 : w ≠ u0 := by
    intro hc
    refine hkey u0 u1 v ?_
    rw [hset]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rw [hc] at hy
    tauto
  have hw1 : w ≠ u1 := by
    intro hc
    refine hkey u0 u1 v ?_
    rw [hset]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rw [hc] at hy
    tauto
  have hvw : v ≠ w := by
    intro hc
    refine hkey u0 u1 w ?_
    rw [hset]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rw [hc] at hy
    tauto
  -- 2. Voronoi 胞单点 a + 四点等距
  obtain ⟨a, ha1, ha2, ha3⟩ := VORONOI_LIST_3_SINGLETON_EXPLICIT V [u0, u1, v, w] hp hs hbar
  have hhdu : hdV [u0, u1, v, w] = u0 := rfl
  rw [hhdu] at ha3
  have hamem : a ∈ voronoiList V [u0, u1, v, w] := by rw [ha1]; simp
  have hxa : ∀ z ∈ setOfList [u0, u1, v, w], a ∈ voronoiClosed V z := by
    intro z hz
    have h0 : a ∈ ⋂₀ {voronoiClosed V q | q ∈ setOfList [u0, u1, v, w]} := hamem
    exact h0 (voronoiClosed V z) ⟨z, hz, rfl⟩
  have hEq : ∀ z ∈ setOfList [u0, u1, v, w], dist a z = hl [u0, u1, v, w] := by
    intro z hz
    have h0 : dist a z ≤ dist a u0 := hxa z hz u0 (hsubV hu0s)
    have h1 : dist a u0 ≤ dist a z := hxa u0 hu0s z (hsubV hz)
    rw [le_antisymm h0 h1, dist_comm a u0, ha3]
  -- 3. 标架（e3 = 棱轴）+ 中点端点读出
  have hdgt : 2 ≤ dist u0 u1 := hp.dist_ge_two hu0 hu1 hne
  have hu0u1n : (u1 - u0 : V3) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨e1, e2, e3, hon, hax0⟩ := exists_on3_eq_smul (u1 - u0) hu0u1n
  have haxd : (u1 - u0 : V3) = dist u0 u1 • e3 := by
    have hn : ‖u1 - u0‖ = dist u0 u1 := (dist_eq_norm u1 u0).symm.trans (dist_comm u1 u0)
    rw [hn] at hax0
    exact hax0
  have h33 : e3 ⬝ᵥ e3 = 1 := hon.2.2.1
  have he3n : ∀ r : ℝ, ‖((r : ℝ) • e3 : V3)‖ ^ 2 = r ^ 2 := by
    intro r
    have h0 : ‖((r : ℝ) • e3 : V3)‖ ^ 2 = ((r : ℝ) • e3 : V3) ⬝ᵥ ((r : ℝ) • e3 : V3) :=
      norm_sq_eq_dot _
    simp only [h0, WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, h33]
    ring
  -- 4. A' = a − mid 与轴垂直（等距读出）
  set mid : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hmiddef
  have hu1eq : (u1 : V3) = u0 + dist u0 u1 • e3 := by
    rw [← haxd]
    module
  have hmidu1 : mid + (dist u0 u1 / 2) • e3 = u1 := by
    rw [hmiddef, haxd, smul_smul]
    conv_rhs => rw [hu1eq]
    module
  have hmidu0 : mid + (-(dist u0 u1 / 2)) • e3 = u0 := by
    rw [hmiddef, haxd, smul_smul]
    module
  set A' : V3 := a - mid with hAdef
  have hsq01 : ‖(a - u0 : V3)‖ ^ 2 = ‖(a - u1 : V3)‖ ^ 2 := by
    rw [← dist_eq_norm a u0, ← dist_eq_norm a u1, hEq u0 hu0s, hEq u1 hu1s]
  have k1 := p24_sq_eq_doteq (y := (a - u0 : V3)) (z := (u1 - u0 : V3)) (by
    rw [show ((a - u0 : V3) - (u1 - u0 : V3)) = (a - u1 : V3) from by module]
    exact hsq01)
  have k1' : (a - u0 : V3) ⬝ᵥ (u1 - u0 : V3) = ‖u1 - u0‖ ^ 2 / 2 := by linarith
  have k2 : ((1 / 2 : ℝ) • (u1 - u0 : V3)) ⬝ᵥ (u1 - u0 : V3) = ‖u1 - u0‖ ^ 2 / 2 := by
    rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, norm_sq_eq_dot]
    ring
  have hzo : (A' : V3) + (1 / 2 : ℝ) • (u1 - u0 : V3) = (a - u0 : V3) := by
    rw [hAdef, hmiddef]
    module
  have e0 : A' ⬝ᵥ (u1 - u0 : V3)
      + ((1 / 2 : ℝ) • (u1 - u0 : V3)) ⬝ᵥ (u1 - u0 : V3)
      = (a - u0 : V3) ⬝ᵥ (u1 - u0 : V3) := by
    rw [← hzo, WithLp.ofLp_add, add_dotProduct]
  rw [k1', k2] at e0
  have hAax : A' ⬝ᵥ (u1 - u0 : V3) = 0 := by linarith
  have hAax' : (u1 - u0 : V3) ⬝ᵥ A' = 0 := by rw [dotProduct_comm]; exact hAax
  have hdne : (dist u0 u1 : ℝ) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hdgt)
  have hAe3 : A' ⬝ᵥ e3 = 0 := by
    have h1 : A' ⬝ᵥ (u1 - u0 : V3) = dist u0 u1 * (A' ⬝ᵥ e3) := by
      rw [haxd, WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul]
    rw [h1] at hAax
    exact (mul_eq_zero.mp hAax).resolve_left hdne
  have hAe3' : e3 ⬝ᵥ A' = 0 := by rw [dotProduct_comm]; exact hAe3
  -- 5. v 的坐标（垂分量 P，长度 n）与 P ≠ 0（退化支：tv² = (d/2)² ⇒ v ∈ {u0,u1}）
  set Pv : V3 := v - mid with hPvdef
  set tv : ℝ := Pv ⬝ᵥ e3 with htvdef
  set P : V3 := Pv - tv • e3 with hPdef
  have hPve : Pv = P + tv • e3 := by rw [hPdef]; module
  have hPe3 : P ⬝ᵥ e3 = 0 := by
    rw [hPdef, htvdef]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, h33]
    ring
  have hPe3' : e3 ⬝ᵥ P = 0 := by rw [dotProduct_comm]; exact hPe3
  set n : ℝ := ‖P‖ with hnndef
  have hPnsq : P ⬝ᵥ P = n ^ 2 := by rw [← norm_sq_eq_dot P]
  have hPne : P ≠ 0 := by
    intro hP0
    have hvvm : v = mid + tv • e3 := by
      have h1 : v - mid = tv • e3 := by rw [← hPvdef, hPve, hP0, zero_add]
      have h2 := (sub_eq_iff_eq_add (a := v) (b := mid) (c := (tv • e3 : V3))).mp h1
      rw [add_comm] at h2
      exact h2
    have hsqv : ‖(a - v : V3)‖ ^ 2 = ‖A'‖ ^ 2 + tv ^ 2 := by
      have hv' : (a - v : V3) = A' + (-(tv : ℝ)) • e3 := by
        rw [hAdef, hvvm, hmiddef]; module
      have hd0 : A' ⬝ᵥ ((-(tv : ℝ)) • e3) = 0 := by
        rw [dotProduct_smul, smul_eq_mul, hAe3, neg_mul, mul_zero, neg_zero]
      rw [hv', p24_norm_sq_of_orth (x := A') (y := ((-(tv : ℝ)) • e3 : V3)) hd0,
        he3n (-(tv : ℝ))]
      ring
    have hsq0 : ‖(a - u0 : V3)‖ ^ 2 = ‖A'‖ ^ 2 + (dist u0 u1 / 2) ^ 2 := by
      have hu' : (a - u0 : V3) = A' + (1 / 2 : ℝ) • (u1 - u0) := by
        rw [hAdef, hmiddef]; module
      have hd0 : A' ⬝ᵥ ((1 / 2 : ℝ) • (u1 - u0 : V3)) = 0 := by
        rw [dotProduct_smul, smul_eq_mul, hAax, mul_zero]
      have hwn : ‖(u1 - u0 : V3)‖ = dist u0 u1 := by
        rw [← dist_eq_norm u1 u0, dist_comm u1 u0]
      have hyn : ‖((1 / 2 : ℝ) • (u1 - u0 : V3) : V3)‖ ^ 2 = (dist u0 u1 / 2) ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hwn]
        ring
      rw [hu', p24_norm_sq_of_orth (x := A')
        (y := ((1 / 2 : ℝ) • (u1 - u0 : V3))) hd0, hyn]
    have hEqv : ‖(a - v : V3)‖ ^ 2 = ‖(a - u0 : V3)‖ ^ 2 := by
      rw [← dist_eq_norm a v, ← dist_eq_norm a u0, hEq v hvs, hEq u0 hu0s]
    have htv2 : tv ^ 2 = (dist u0 u1 / 2) ^ 2 := by linarith
    have hzero : (tv - dist u0 u1 / 2) * (tv + dist u0 u1 / 2) = 0 := by
      linear_combination htv2
    rcases mul_eq_zero.mp hzero with hcase | hcase
    · exfalso
      refine hv1 ?_
      have hvtv : tv = dist u0 u1 / 2 := by linarith
      rw [hvvm, hvtv, hmidu1]
    · exfalso
      refine hv0 ?_
      have hvtv : tv = -(dist u0 u1 / 2) := by linarith
      rw [hvvm, hvtv, hmidu0]
  have hnpos : 0 < n := norm_pos_iff.mpr hPne
  -- 6. 共面塌缩：vectorSpan (setOfList vl) = span{u1−u0, v−u0}，w 的坐标分解
  have hbar2v : barV V 2 [u0, u1, v] := by
    refine ⟨by norm_num, ?_⟩
    rintro zl ⟨⟨yl, hyll⟩, hpos⟩
    exact hbar.2 zl ⟨⟨yl ++ [w], by rw [← List.append_assoc, ← hyll]; rfl⟩, hpos⟩
  have hneS2 : (setOfList [u0, u1, v] : Set V3) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp ⟨u0, by simp [setOfList]⟩
  have hfr2 : Module.finrank ℝ (vectorSpan ℝ (setOfList [u0, u1, v])) = 2 := by
    have h := MHFTTZN1 V [u0, u1, v] 2 hp hbar2v
    rw [affDim, if_neg hneS2] at h
    exact_mod_cast h
  have hvs3 : vectorSpan ℝ (setOfList [u0, u1, v])
      = Submodule.span ℝ ({u1 - u0, v - u0} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ
      (show u0 ∈ (setOfList [u0, u1, v] : Set V3) from by simp [setOfList])]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨y, hy, rfl⟩
      simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hcy | hcy | hcy
      · rw [hcy]; simp
      · rw [hcy]; exact Submodule.subset_span (by simp)
      · rw [hcy]; exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact Submodule.subset_span ⟨u1, by simp [setOfList], rfl⟩
      · exact Submodule.subset_span ⟨v, by simp [setOfList], rfl⟩
  have hcp2 : Module.finrank ℝ (vectorSpan ℝ (setOfList [u0, u1, v, w])) ≤ 2 :=
    ((coplanar_iff_finrank_le_two (k := ℝ) (s := setOfList [u0, u1, v, w])).mp hcp)
  have hspanW : Submodule.span ℝ ({u1 - u0, v - u0} : Set V3)
      ≤ vectorSpan ℝ (setOfList [u0, u1, v, w]) := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact Submodule.subset_span ⟨u1, hu1s, u0, hu0s, rfl⟩
    · exact Submodule.subset_span ⟨v, hvs, u0, hu0s, rfl⟩
  have hWeq : vectorSpan ℝ (setOfList [u0, u1, v, w])
      = Submodule.span ℝ ({u1 - u0, v - u0} : Set V3) := by
    haveI := hcp.finiteDimensional_vectorSpan
    refine (Submodule.eq_of_le_of_finrank_le hspanW ?_).symm
    rw [← hvs3]
    exact le_trans hcp2 hfr2.ge
  have hwsW : (w - u0 : V3) ∈ Submodule.span ℝ ({u1 - u0, v - u0} : Set V3) := by
    have h0 : (w - u0 : V3) ∈ vectorSpan ℝ (setOfList [u0, u1, v, w]) :=
      Submodule.subset_span ⟨w, hws, u0, hu0s, rfl⟩
    rw [hWeq] at h0
    exact h0
  obtain ⟨α, β, hwu0⟩ := Submodule.mem_span_pair.mp hwsW
  have hvu0P : (v - u0 : V3) = (tv + dist u0 u1 / 2) • e3 + (1:ℝ) • P := by
    calc (v - u0 : V3) = Pv + (1 / 2 : ℝ) • (u1 - u0) := by rw [hPvdef, hmiddef]; module
      _ = (P + tv • e3) + (1 / 2 : ℝ) • (u1 - u0) := by rw [hPve]
      _ = (tv + dist u0 u1 / 2) • e3 + (1:ℝ) • P := by rw [haxd]; module
  obtain ⟨γ, μ, hwm⟩ : ∃ γ μ : ℝ, (w - mid : V3) = γ • e3 + μ • P := by
    refine ⟨(α - 1 / 2) * dist u0 u1 + β * (tv + dist u0 u1 / 2), β, ?_⟩
    calc (w - mid : V3)
        = (α • (u1 - u0 : V3) + β • (v - u0 : V3)) - (1 / 2 : ℝ) • (u1 - u0) := by
          rw [hwu0, hmiddef]; module
      _ = ((α - 1 / 2) * dist u0 u1 + β * (tv + dist u0 u1 / 2)) • e3 + β • P := by
          rw [haxd, hvu0P]; module
  set tw : ℝ := (w - mid) ⬝ᵥ e3 with htwdef
  have hγtw : γ = tw := by
    rw [htwdef, hwm]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hPe3, h33, mul_zero, zero_add,
      mul_one]
    ring
  have hwdecomp : (w - mid : V3) = tw • e3 + μ • P := by
    rw [← hγtw]
    exact hwm
  -- 7. 圆心 c = mid + (k/n)•P 与 a − c 的双重垂直
  set k : ℝ := A' ⬝ᵥ P / n with hkdef
  have hkn : A' ⬝ᵥ P = k * n := by rw [hkdef]; field_simp
  set c : V3 := mid + (k / n) • P with hcdef
  have hac : (a - c : V3) = A' - (k / n) • P := by rw [hcdef, hAdef]; module
  have hqcE3 : (a - c : V3) ⬝ᵥ e3 = 0 := by
    rw [hac]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hAe3, hPe3]
    ring
  have hqcP : (a - c : V3) ⬝ᵥ P = 0 := by
    rw [hac]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [hkn, hPnsq]
    field_simp
    ring
  have hnormSP : ∀ s t : ℝ, ‖((s : ℝ) • e3 + (t : ℝ) • P : V3)‖ ^ 2 = s ^ 2 + t ^ 2 * n ^ 2 := by
    intro s t
    have h0 := p24_norm_sq_of_orth (x := ((s : ℝ) • e3 : V3)) (y := ((t : ℝ) • P : V3))
      (show ((s : ℝ) • e3 : V3) ⬝ᵥ ((t : ℝ) • P : V3) = 0 by
        simp only [WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hPe3',
          mul_zero])
    rw [h0, he3n s, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnndef]
  have hpyth : ∀ s t : ℝ, ‖(a - c : V3) + ((s : ℝ) • e3 + (t : ℝ) • P)‖ ^ 2
      = ‖(a - c : V3)‖ ^ 2 + s ^ 2 + t ^ 2 * n ^ 2 := by
    intro s t
    have hy0 : (a - c : V3) ⬝ᵥ ((s : ℝ) • e3 + (t : ℝ) • P) = 0 := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hqcE3,
        hqcP, mul_zero, zero_add]
    rw [p24_norm_sq_of_orth (x := (a - c : V3))
      (y := ((s : ℝ) • e3 + (t : ℝ) • P)) hy0, hnormSP s t]
    ring
  -- 8. c − 端点表示 + 距离方程
  have hvVm : (v : V3) = mid + Pv := by rw [hPvdef]; module
  have hwWm : (w : V3) = mid + (w - mid) := by module
  have hcu0 : (c - u0 : V3) = (dist u0 u1 / 2) • e3 + (k / n) • P := by
    rw [hcdef, hmiddef, haxd]; module
  have hcv : (c - v : V3) = (-(tv : ℝ)) • e3 + (k / n - 1) • P := by
    have step : (c - v : V3) = (k / n) • P - Pv := by rw [hcdef, hvVm]; module
    rw [step, hPve]; module
  have hcw : (c - w : V3) = (-(tw : ℝ)) • e3 + (k / n - μ) • P := by
    have step : (c - w : V3) = (k / n) • P - (w - mid) := by rw [hcdef, hwWm]; module
    rw [step, hwdecomp]; module
  have hncu0 : ‖(c - u0 : V3)‖ ^ 2 = k ^ 2 + dist u0 u1 ^ 2 / 4 := by
    rw [hcu0, hnormSP (dist u0 u1 / 2) (k / n)]
    have h1 : (k / n) ^ 2 * n ^ 2 = k ^ 2 := by field_simp
    rw [h1]
    ring
  have hncv : ‖(c - v : V3)‖ ^ 2 = (k - n) ^ 2 + tv ^ 2 := by
    rw [hcv, hnormSP (-(tv : ℝ)) (k / n - 1)]
    have h1 : (k / n - 1) ^ 2 * n ^ 2 = (k - n) ^ 2 := by field_simp
    rw [h1]
    ring
  have hncw : ‖(c - w : V3)‖ ^ 2 = (k - μ * n) ^ 2 + tw ^ 2 := by
    rw [hcw, hnormSP (-(tw : ℝ)) (k / n - μ)]
    have h1 : (k / n - μ) ^ 2 * n ^ 2 = (k - μ * n) ^ 2 := by field_simp
    rw [h1]
    ring
  have hau0v : (a - u0 : V3) = (a - c : V3) + (c - u0 : V3) := by module
  have havv : (a - v : V3) = (a - c : V3) + (c - v : V3) := by module
  have haww : (a - w : V3) = (a - c : V3) + (c - w : V3) := by module
  have hdu0 : ‖(a - u0 : V3)‖ ^ 2
      = ‖(a - c : V3)‖ ^ 2 + (k ^ 2 + dist u0 u1 ^ 2 / 4) := by
    rw [hau0v, hcu0, hpyth (dist u0 u1 / 2) (k / n)]
    have h1 : (k / n) ^ 2 * n ^ 2 = k ^ 2 := by field_simp
    rw [h1]
    ring
  have hdv : ‖(a - v : V3)‖ ^ 2
      = ‖(a - c : V3)‖ ^ 2 + ((k - n) ^ 2 + tv ^ 2) := by
    rw [havv, hcv, hpyth (-(tv : ℝ)) (k / n - 1)]
    have h1 : (k / n - 1) ^ 2 * n ^ 2 = (k - n) ^ 2 := by field_simp
    rw [h1]
    ring
  have hdw : ‖(a - w : V3)‖ ^ 2
      = ‖(a - c : V3)‖ ^ 2 + ((k - μ * n) ^ 2 + tw ^ 2) := by
    rw [haww, hcw, hpyth (-(tw : ℝ)) (k / n - μ)]
    have h1 : (k / n - μ) ^ 2 * n ^ 2 = (k - μ * n) ^ 2 := by field_simp
    rw [h1]
    ring
  have hEu0 : ‖(a - u0 : V3)‖ ^ 2 = hl [u0, u1, v, w] ^ 2 := by
    rw [← dist_eq_norm a u0, hEq u0 hu0s]
  have hEv : ‖(a - v : V3)‖ ^ 2 = hl [u0, u1, v, w] ^ 2 := by
    rw [← dist_eq_norm a v, hEq v hvs]
  have hEw : ‖(a - w : V3)‖ ^ 2 = hl [u0, u1, v, w] ^ 2 := by
    rw [← dist_eq_norm a w, hEq w hws]
  -- 9. hC2 / hC3 / hrho
  have ek : (k - n) ^ 2 = k ^ 2 - 2 * k * n + n ^ 2 := by ring
  have ekμ : (k - μ * n) ^ 2 = k ^ 2 - 2 * k * (μ * n) + (μ * n) ^ 2 := by ring
  have hC2 : 2 * k * n = n ^ 2 + tv ^ 2 - dist u0 u1 ^ 2 / 4 := by
    linarith [hEu0, hdu0, hEv, hdv, ek]
  have hC3 : 2 * k * (μ * n) = (μ * n) ^ 2 + tw ^ 2 - dist u0 u1 ^ 2 / 4 := by
    linarith [hEu0, hdu0, hEw, hdw, ekμ]
  have hhlpos : (0:ℝ) ≤ hl [u0, u1, v, w] := by rw [ha3]; exact dist_nonneg
  have hhl2 : hl [u0, u1, v, w] ^ 2 < 2 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (le_of_lt (by norm_num : (0:ℝ) < 2))
    nlinarith [hhl, hhlpos, hs2]
  have hqnpos : (0:ℝ) ≤ ‖(a - c : V3)‖ ^ 2 := sq_nonneg _
  have hrho : k ^ 2 + dist u0 u1 ^ 2 / 4 < 2 := by
    linarith [hEu0, hdu0, hqnpos, hhl2]
  -- 10. 弦组（packing 两两距离 ≥ 2 的平方形态）
  have hsq2 : ∀ x y : V3, x ∈ V → y ∈ V → x ≠ y → (4:ℝ) ≤ dist x y ^ 2 := by
    intro x y hx hy hxy
    have h1 : 2 ≤ dist x y := hp.dist_ge_two hx hy hxy
    have hdn : (0:ℝ) ≤ dist x y := dist_nonneg
    nlinarith [h1, hdn]
  have hvu1P : (v - u1 : V3) = (tv - dist u0 u1 / 2) • e3 + (1:ℝ) • P := by
    calc (v - u1 : V3) = Pv - (1 / 2 : ℝ) • (u1 - u0) := by rw [hPvdef, hmiddef]; module
      _ = (P + tv • e3) - (1 / 2 : ℝ) • (u1 - u0) := by rw [hPve]
      _ = (tv - dist u0 u1 / 2) • e3 + (1:ℝ) • P := by rw [haxd]; module
  have hwu0P : (w - u0 : V3) = (tw + dist u0 u1 / 2) • e3 + μ • P := by
    have step : (w - u0 : V3) = (w - mid) + (1 / 2 : ℝ) • (u1 - u0) := by
      rw [hmiddef]; module
    rw [step, hwdecomp, haxd]; module
  have hwu1P : (w - u1 : V3) = (tw - dist u0 u1 / 2) • e3 + μ • P := by
    have step : (w - u1 : V3) = (w - mid) - (1 / 2 : ℝ) • (u1 - u0) := by
      rw [hmiddef]; module
    rw [step, hwdecomp, haxd]; module
  have hwvP : (w - v : V3) = (tw - tv) • e3 + (μ - 1) • P := by
    have step : (w - v : V3) = (w - mid) - Pv := by rw [hPvdef]; module
    rw [step, hwdecomp, hPve]; module
  have h03 : 4 ≤ n ^ 2 + (tv + dist u0 u1 / 2) ^ 2 := by
    have h1 : 4 ≤ dist u0 v ^ 2 := hsq2 u0 v hu0 hvV hv0.symm
    have h2 : dist u0 v ^ 2 = n ^ 2 + (tv + dist u0 u1 / 2) ^ 2 := by
      rw [dist_comm u0 v, dist_eq_norm v u0, hvu0P, hnormSP (tv + dist u0 u1 / 2) 1]
      ring
    rw [← h2]; linarith
  have h13 : 4 ≤ n ^ 2 + (tv - dist u0 u1 / 2) ^ 2 := by
    have h1 : 4 ≤ dist u1 v ^ 2 := hsq2 u1 v hu1 hvV hv1.symm
    have h2 : dist u1 v ^ 2 = n ^ 2 + (tv - dist u0 u1 / 2) ^ 2 := by
      rw [dist_comm u1 v, dist_eq_norm v u1, hvu1P, hnormSP (tv - dist u0 u1 / 2) 1]
      ring
    rw [← h2]; linarith
  have h04 : 4 ≤ (μ * n) ^ 2 + (tw + dist u0 u1 / 2) ^ 2 := by
    have h1 : 4 ≤ dist u0 w ^ 2 := hsq2 u0 w hu0 hwV hw0.symm
    have h2 : dist u0 w ^ 2 = (μ * n) ^ 2 + (tw + dist u0 u1 / 2) ^ 2 := by
      rw [dist_comm u0 w, dist_eq_norm w u0, hwu0P, hnormSP (tw + dist u0 u1 / 2) μ]
      ring
    rw [← h2]; linarith
  have h14 : 4 ≤ (μ * n) ^ 2 + (tw - dist u0 u1 / 2) ^ 2 := by
    have h1 : 4 ≤ dist u1 w ^ 2 := hsq2 u1 w hu1 hwV hw1.symm
    have h2 : dist u1 w ^ 2 = (μ * n) ^ 2 + (tw - dist u0 u1 / 2) ^ 2 := by
      rw [dist_comm u1 w, dist_eq_norm w u1, hwu1P, hnormSP (tw - dist u0 u1 / 2) μ]
      ring
    rw [← h2]; linarith
  have h34 : 4 ≤ (μ * n - n) ^ 2 + (tw - tv) ^ 2 := by
    have h1 : 4 ≤ dist v w ^ 2 := hsq2 v w hvV hwV hvw
    have h2 : dist v w ^ 2 = (μ * n - n) ^ 2 + (tw - tv) ^ 2 := by
      rw [dist_comm v w, dist_eq_norm w v, hwvP, hnormSP (tw - tv) (μ - 1)]
      ring
    rw [← h2]; linarith
  -- 11. k ≠ 0（h03 + h13 相加 + hrho 的 d² < 8）与组装
  have hk0 : k ≠ 0 := by
    intro hk0
    have hsum : n ^ 2 + tv ^ 2 = dist u0 u1 ^ 2 / 4 := by rw [hk0] at hC2; linarith
    have ex1 : (tv + dist u0 u1 / 2) ^ 2
        = tv ^ 2 + tv * dist u0 u1 + dist u0 u1 ^ 2 / 4 := by ring
    have ex2 : (tv - dist u0 u1 / 2) ^ 2
        = tv ^ 2 - tv * dist u0 u1 + dist u0 u1 ^ 2 / 4 := by ring
    have hdd : dist u0 u1 ^ 2 < 8 := by rw [hk0] at hrho; nlinarith
    linarith [hC2, h03, h13, hsum, ex1, ex2, hdd]
  exact ⟨dist u0 u1, k, n, μ, tv, tw, hdgt, hk0, hrho, hC2, hC3, h03, h13, h04, h14, h34⟩

/-! ## 新件 2：p24_caseA_coplanar_false（合成件） -/

/-- **情形 A 完结件**（2026-10-11 波）：`p24_caseA_concyclic`（共圆件，
上件）产出 `p24_wedge_quad_kill`（上波真证落地的 W-楔代数核心）的精确输入形，
本件逐参转发 ⇒ 情形 A（`hl vl < √2`，路线图第 4 条）下四点共面不可能——
即「四点共面 ⇒ 仿射独立」的反证收口，供后续波装配进
`p24_exists_mcell_not_flat` 的非平坦胞论证（情形 B `r₄ ≥ √2` 分支不在本件
范围）。 -/
private theorem p24_caseA_coplanar_false (V : Set V3) (u0 u1 : V3) (vl : List V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1])
    (hhl : hl vl < Real.sqrt 2) (hcp : Coplanar ℝ (setOfList vl)) : False := by
  obtain ⟨d, k, n, μ, tv, tw, hd2, hk, hrho, hC2, hC3, h03, h13, h04, h14, h34⟩ :=
    p24_caseA_concyclic V u0 u1 vl hs hp hu0 hu1 hne hbar htr hhl hcp
  exact p24_wedge_quad_kill d k n μ tv tw hd2 hk hrho hC2 hC3 h03 h13 h04 h14 h34


/-! ## (β) 支独立存在性引理第三波：情形 A/B3 全支真证（2026-10-12 波）

供 `p24_exists_mcell_not_flat` 装配的真证前置件群（全部 private、全真证；
唯一 sorried 上游输入为 PA2 公开残件 `MXI_EXISTS_concl`，见
`p24_caseB3_mxi_not_mem` docstring 记账）：

- `p24_volume_pos_of_affineSpan`：affineSpan = ⊤ ⇒ 凸包体积 > 0
  （路线图"正体积工具"档：非空内部 Haar 测度为正 + 单形内部非空）；
- `p24_affineSpan_top_of_finrank`：vectorSpan finrank = 3 ⇒ affineSpan = ⊤；
- `p24_axial_e3` / `p24_axial_eqs`：棱轴标架下与 u0,u1,v 等距的点满足双
  仿射方程 `(x−mid)⊥e3`、`(x−mid)⬝P = wg·h`（γ 关系消元）；
- `p24_affGt_mem_affineSpan_triple`：affGt 成员 ⇒ affineSpan 三点成员；
- `p24_leaf_exists_sqrt8`：叶三元组存在性（`d < √8` 形态；第一波冻结件
  `p24_leaf_exists`（`d < √2` 形态 vacuous）的泛化私拷，合并时二取一）；
- `p24_caseA_edgeX` / `p24_caseA_branch`：情形 A（`r₄ < √2`，X := mcell 4）
  的 edgeX 成员（正体积 + HDTFNFZ 的 `VX = V ∩ X`）与全支 capstone 形；
- `p24_caseB3_mxi_not_mem`：情形 B3 对齐排除核——`mxi ∉ affineSpan
  {u0,u1,v}`（ω₃ = 四点 Voronoi 单点 = 外心、ω₂ ∈ 三重点 Voronoi 胞，
  双仿射方程经 segment 权重线性性传给 mxi，与 affineSpan 坐标联立得
  `dist(u0,mxi)² = r₃² < 2`，而 `dist(u0,mxi) = √2`）；
- `p24_caseB3_edgeX` / `p24_caseB3_not_flat` / `p24_caseB3_branch`：
  B3 支 edgeX 成员（正体积 + 三向量线性无关）、非平坦排除（azim 零水平集
  传输）与全支 capstone 形。
-/

/-- 正体积工具：affineSpan 为全空间的集合，其凸包体积为正。
路线图（docs/projects/pa24-nonflat-roadmap.md）"正体积工具"档：非空内部
的 Haar 测度为正（Mathlib `Measure.measure_pos_of_nonempty_interior`），
仿射无关单形的内部非空由
`interior_convexHull_nonempty_iff_affineSpan_eq_top` 给出。 -/
private theorem p24_volume_pos_of_affineSpan {S : Set V3}
    (hspan : affineSpan ℝ S = ⊤) :
    0 < volume (convexHull ℝ S) :=
  Measure.measure_pos_of_nonempty_interior (μ := volume)
    (s := convexHull ℝ S) (interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan)

/-- vectorSpan 有限维维数 = 3 ⇒ affineSpan = ⊤（`direction_affineSpan` +
`Submodule.eq_top_of_finrank_eq` + vadd 逐点构造）。 -/
private theorem p24_affineSpan_top_of_finrank {S : Set V3} (hne : S.Nonempty)
    (hfr : Module.finrank ℝ (vectorSpan ℝ S) = 3) :
    affineSpan ℝ S = ⊤ := by
  obtain ⟨p0, hp0⟩ := hne
  refine top_unique (fun p _ => ?_)
  have hdir : (affineSpan ℝ S).direction = (⊤ : Submodule ℝ V3) := by
    rw [direction_affineSpan]
    refine Submodule.eq_top_of_finrank_eq ?_
    have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    omega
  have hp0m : p0 ∈ (affineSpan ℝ S) := subset_affineSpan ℝ S hp0
  have hv : (p -ᵥ p0) ∈ (affineSpan ℝ S).direction := by
    rw [hdir]; exact Submodule.mem_top
  have hvadd := AffineSubspace.vadd_mem_of_mem_direction hv hp0m
  rwa [show ((p -ᵥ p0) +ᵥ p0) = p from vsub_vadd p p0] at hvadd

/-- W-楔代数辅助件（情形 B3 对齐排除的 E1）：与棱两端等距的点关于中点
轴正交（`p24_sq_eq_doteq` 的平方差读出 + 轴坐标）。 -/
private theorem p24_axial_e3 (u0 u1 mid e3 : V3) (d : ℝ) (x : V3)
    (hax : (u1 - u0 : V3) = d • e3) (hd : d ≠ 0)
    (hmid : (mid : V3) = u0 + (1 / 2 : ℝ) • (u1 - u0))
    (hx1 : dist x u0 = dist x u1) :
    (x - mid) ⬝ᵥ e3 = 0 := by
  have hsq : ‖(x - u0 : V3)‖ ^ 2 = ‖(x - u1 : V3)‖ ^ 2 := by
    rw [← dist_eq_norm x u0, ← dist_eq_norm x u1, hx1]
  have k1 := p24_sq_eq_doteq (y := (x - u0 : V3)) (z := (u1 - u0 : V3)) (by
    rw [show ((x - u0 : V3) - (u1 - u0 : V3)) = (x - u1 : V3) from by module]
    exact hsq)
  have k1' : (x - u0 : V3) ⬝ᵥ (u1 - u0 : V3) = ‖u1 - u0‖ ^ 2 / 2 := by linarith
  have k2 : ((1 / 2 : ℝ) • (u1 - u0 : V3)) ⬝ᵥ (u1 - u0 : V3) = ‖u1 - u0‖ ^ 2 / 2 := by
    rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, norm_sq_eq_dot]
    ring
  have hzo : (x - mid : V3) + (1 / 2 : ℝ) • (u1 - u0 : V3) = (x - u0 : V3) := by
    rw [hmid]; module
  have e0 : (x - mid : V3) ⬝ᵥ (u1 - u0 : V3)
      + ((1 / 2 : ℝ) • (u1 - u0 : V3)) ⬝ᵥ (u1 - u0 : V3)
      = (x - u0 : V3) ⬝ᵥ (u1 - u0 : V3) := by
    rw [← hzo, WithLp.ofLp_add, add_dotProduct]
  rw [k1', k2] at e0
  have kz : (x - mid : V3) ⬝ᵥ (u1 - u0 : V3) = 0 := by linarith
  have h1 : (x - mid : V3) ⬝ᵥ (u1 - u0 : V3) = d * ((x - mid : V3) ⬝ᵥ e3) := by
    rw [hax, WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul]
  rw [h1] at kz
  exact (mul_eq_zero.mp kz).resolve_left hd

/-- W-楔代数辅助件（情形 B3 对齐排除的 E1+E2）：与 u0、u1、v 三点等距的
`x` 在轴标架（`p24_tri_gamma` 数据 `d, t, h, wg`，`P` = v 的垂分量）下满足
双仿射方程 `(x − mid) ⬝ᵥ e3 = 0 ∧ (x − mid) ⬝ᵥ P = wg * h`（E2 = 两距离
平方的正交分解 + γ 关系 `2·wg·h = h² + t² − d·t` 消元）。 -/
private theorem p24_axial_eqs (u0 u1 v mid e3 P : V3) (d t h wg : ℝ) (x : V3)
    (hax : (u1 - u0 : V3) = d • e3) (hd : d ≠ 0)
    (h33 : e3 ⬝ᵥ e3 = 1)
    (hmid : (mid : V3) = u0 + (d / 2) • e3)
    (hv : (v - u0 : V3) = t • e3 + P)
    (hPe3 : P ⬝ᵥ e3 = 0) (hPn : ‖P‖ = h) (hh : 0 < h)
    (hgam : 2 * wg * h = h ^ 2 + t ^ 2 - d * t)
    (hx1 : dist x u0 = dist x u1) (hxv : dist x u0 = dist x v) :
    (x - mid : V3) ⬝ᵥ e3 = 0 ∧ (x - mid : V3) ⬝ᵥ P = wg * h := by
  have he3n : ∀ r : ℝ, ‖((r : ℝ) • e3 : V3)‖ ^ 2 = r ^ 2 := by
    intro r
    have h0 : ‖((r : ℝ) • e3 : V3)‖ ^ 2 = ((r : ℝ) • e3 : V3) ⬝ᵥ ((r : ℝ) • e3 : V3) :=
      norm_sq_eq_dot _
    simp only [h0, WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      h33]
    ring
  set ζ : V3 := x - mid with hζ
  have he1 : ζ ⬝ᵥ e3 = 0 :=
    p24_axial_e3 u0 u1 mid e3 d x hax hd (by rw [hmid, hax]; module) hx1
  refine ⟨he1, ?_⟩
  have hvm : (v - mid : V3) = (t - d / 2) • e3 + P := by
    have e1 : (v - mid : V3) = (v - u0) - (mid - u0) := by rw [hmid]; module
    rw [e1, hv, hmid]; module
  have hxu : (x - u0 : V3) = ζ + (d / 2) • e3 := by rw [hζ, hmid]; module
  have hz1 : ζ ⬝ᵥ ((d / 2) • e3 : V3) = 0 := by
    rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul, he1]
    exact mul_zero ((d / 2 : ℝ))
  have hnu0 : ‖(x - u0 : V3)‖ ^ 2 = ‖ζ‖ ^ 2 + d ^ 2 / 4 := by
    rw [hxu, p24_norm_sq_of_orth hz1, he3n (d / 2)]
    ring
  have hxv' : (x - v : V3) = (ζ - P) + ((d / 2 - t) • e3 : V3) := by
    rw [hζ]
    have e2 : (x - v : V3) = (x - mid) - (v - mid) := by rw [hmid]; module
    rw [e2, hvm]; module
  have hz2 : (ζ - P : V3) ⬝ᵥ ((d / 2 - t) • e3 : V3) = 0 := by
    have h1 : (ζ - P : V3) ⬝ᵥ e3 = (0 : ℝ) := by
      simp only [WithLp.ofLp_sub, sub_dotProduct, ← hζ, he1, hPe3, sub_self]
    rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul, h1]
    exact mul_zero ((d / 2 - t : ℝ))
  have hnv : ‖(x - v : V3)‖ ^ 2
      = ‖(ζ - P : V3)‖ ^ 2 + (t - d / 2) ^ 2 := by
    rw [hxv', p24_norm_sq_of_orth hz2, he3n (d / 2 - t)]
    ring
  have hnP : ‖(ζ - P : V3)‖ ^ 2 = ‖ζ‖ ^ 2 - 2 * (ζ ⬝ᵥ P) + ‖P‖ ^ 2 := by
    have q0 : ‖(ζ - P : V3)‖ ^ 2 = (ζ - P) ⬝ᵥ (ζ - P) := norm_sq_eq_dot _
    rw [q0]
    simp only [WithLp.ofLp_sub, sub_dotProduct, dotProduct_sub,
      ← norm_sq_eq_dot ζ, ← norm_sq_eq_dot P]
    rw [dotProduct_comm]
    ring
  have hdist : dist x u0 = dist x v := hxv
  have hsqeq : ‖(x - u0 : V3)‖ ^ 2 = ‖(x - v : V3)‖ ^ 2 := by
    rw [← dist_eq_norm x u0, ← dist_eq_norm x v, hdist]
  rw [hnu0, hnv, hnP] at hsqeq
  have hPn2 : ‖P‖ ^ 2 = h ^ 2 := by rw [hPn]
  linarith [hgam, hPn2]

/-- affGt {u0,u1} {v} 成员 ⇒ affineSpan {u0,u1,v} 成员（HOL `affsign` 的
有限支撑加权和 + 权重和 1 + 逐项 span 归属；供 azim 零水平集的 span 传输）。 -/
private theorem p24_affGt_mem_affineSpan_triple (u0 u1 v z : V3)
    (hz : z ∈ affGt {u0, u1} {v}) :
    z ∈ (affineSpan ℝ ({u0, u1, v} : Set V3)) := by
  obtain ⟨f, hfin, hzsum, -, hsum1⟩ := hz
  have key : (z - u0 : V3) = ∑ x ∈ hfin.toFinset, f x • (x - u0) := by
    calc (z - u0 : V3) = (∑ x ∈ hfin.toFinset, f x • (x : V3)) - u0 := by
          rw [hzsum]
      _ = (∑ x ∈ hfin.toFinset, f x • (x : V3))
            - (∑ x ∈ hfin.toFinset, f x) • u0 := by rw [hsum1, one_smul]
      _ = ∑ x ∈ hfin.toFinset, (f x • (x : V3) - f x • u0) := by
          rw [Finset.sum_sub_distrib, Finset.sum_smul]
      _ = ∑ x ∈ hfin.toFinset, f x • (x - u0) :=
          Finset.sum_congr rfl fun x _ => by rw [smul_sub]
  have hmem : (z - u0 : V3) ∈ Submodule.span ℝ ({u1 - u0, v - u0} : Set V3) := by
    rw [key]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hxset : x ∈ ({u0, u1, v} : Set V3) := by
      have hx' := (Set.Finite.mem_toFinset hfin).mp hx
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff] at hx'
      rcases hx' with (hx1 | hx1) | hx1
      · rw [hx1]; exact Set.mem_insert u0 {u1, v}
      · rw [hx1]; exact Set.mem_insert_of_mem u0 (Set.mem_insert u1 {v})
      · rw [hx1]
        exact Set.mem_insert_of_mem u0 (Set.mem_insert_of_mem u1 (Set.mem_singleton v))
    rcases hxset with hx1 | hx1 | hx1
    · rw [hx1, sub_self, smul_zero]; exact Submodule.zero_mem _
    · rw [hx1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_insert (u1 - u0) ({v - u0} : Set V3)))
    · rw [hx1]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Set.mem_insert_of_mem (u1 - u0) (Set.mem_singleton_iff.mpr rfl)
  have hu0m : u0 ∈ (affineSpan ℝ ({u0, u1, v} : Set V3)) :=
    mem_affineSpan (k := ℝ) (by simp)
  have hdirEq : Submodule.span ℝ ({u1 - u0, v - u0} : Set V3)
      ≤ (affineSpan ℝ ({u0, u1, v} : Set V3)).direction := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ
      (show u0 ∈ ({u0, u1, v} : Set V3) from by simp)]
    rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · exact Submodule.subset_span ⟨u1, by simp, rfl⟩
    · exact Submodule.subset_span ⟨v, by simp, rfl⟩
  have hvadd := AffineSubspace.vadd_mem_of_mem_direction (hdirEq hmem) hu0m
  rwa [show ((z - u0 : V3) +ᵥ u0) = z from vsub_vadd z u0] at hvadd

/-- 叶三元组存在性（`d < √8` 形态；第一波冻结件 `p24_leaf_exists`
（`d < √2` 形态，与 packing 的 `d ≥ 2` 联立 vacuous）的泛化私拷，合并时
二取一）：`p24_mid_mem_voronoiList_sqrt8`（中点 ∈ 配对 Voronoi 胞）+
`p24_voronoi_pair_split`（fan 结构，真证）右端并集非空抽出叶三元组。 -/
private theorem p24_leaf_exists_sqrt8 (V : Set V3) (u0 u1 : V3) (hs : saturated V)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hd8 : dist u0 u1 < Real.sqrt 8) :
    ∃ vl : List V3, barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1] := by
  have hhl : hl [u0, u1] < Real.sqrt 2 := p24_hl_pair_lt_sqrt2 hd8
  have hmem := p24_mid_mem_voronoiList_sqrt8 V u0 u1 hp hu0 hu1 hne hd8
  rw [p24_voronoi_pair_split V u0 u1 hs hp hu0 hu1 hne hhl] at hmem
  obtain ⟨T, hT, hTm⟩ := Set.mem_sUnion.mp hmem
  obtain ⟨vl, hvl, hTeq⟩ := hT
  rcases hvl with ⟨hb3, htr⟩
  exact ⟨vl, hb3, htr⟩

/-- **情形 A · edgeX 成员件**：情形 A（`hl vl < √2`，X := `mcell 4 V vl`
= 四点凸包）处 `{u0,u1} ∈ edgeX V X`——正体积工具（affineSpan = ⊤ ⇒ 体积
> 0 ⇒ 非 nullSet）+ HDTFNFZ 的 `VX V X = V ∩ X` 读出（PA10:257，经
PA12→PA10→PA11 传递可见）+ `u0, u1 ∈ V ∩ X`（凸包含四点、四点 ∈ V 经
barV nondg；`hncp` 由 `p24_caseA_coplanar_false` 供给）。 -/
private theorem p24_caseA_edgeX (V : Set V3) (u0 u1 : V3) (v w : V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar : barV V 3 [u0, u1, v, w])
    (hhl : hl [u0, u1, v, w] < Real.sqrt 2)
    (hncp : ¬ Coplanar ℝ (setOfList [u0, u1, v, w])) :
    ({u0, u1} : Set V3) ∈ edgeX V (mcell 4 V [u0, u1, v, w]) := by
  have hset4 : setOfList [u0, u1, v, w] = ({u0, u1, v, w} : Set V3) := by
    ext y
    simp [setOfList]
  have hvn : voronoiNondg V [u0, u1, v, w] :=
    hbar.2 [u0, u1, v, w] ⟨⟨[], by rw [List.append_nil]⟩, by simp⟩
  have hvV : v ∈ V := hvn.2.1 (by simp [setOfList])
  have hu0S : u0 ∈ setOfList [u0, u1, v, w] := by simp [setOfList]
  have hu1S : u1 ∈ setOfList [u0, u1, v, w] := by simp [setOfList]
  have hneS : (setOfList [u0, u1, v, w] : Set V3).Nonempty := Exists.intro u0 hu0S
  have hXeq : mcell 4 V [u0, u1, v, w] = convexHull ℝ (setOfList [u0, u1, v, w]) := by
    show mcell4 V [u0, u1, v, w] = _
    rw [mcell4, if_pos hhl]
  have hfr3 : Module.finrank ℝ (vectorSpan ℝ (setOfList [u0, u1, v, w])) = 3 := by
    have hle : Module.finrank ℝ (vectorSpan ℝ (setOfList [u0, u1, v, w])) ≤ 3 := by
      have h1 := Submodule.finrank_le (vectorSpan ℝ (setOfList [u0, u1, v, w]))
      rw [finrank_euclideanSpace_fin] at h1
      exact h1
    have hge : ¬ (Module.finrank ℝ (vectorSpan ℝ (setOfList [u0, u1, v, w])) ≤ 2) := fun hcon =>
      hncp ((coplanar_iff_finrank_le_two (k := ℝ)).mpr hcon)
    omega
  have hvpos : 0 < volume (convexHull ℝ (setOfList [u0, u1, v, w])) :=
    p24_volume_pos_of_affineSpan (p24_affineSpan_top_of_finrank hneS hfr3)
  have hnull : ¬ nullSet (mcell 4 V [u0, u1, v, w]) := by
    intro hc
    rw [nullSet, hXeq] at hc
    exact hvpos.ne hc.symm
  have hm0 : u0 ∈ V ∩ convexHull ℝ (setOfList [u0, u1, v, w]) :=
    And.intro hu0 (subset_convexHull ℝ (setOfList [u0, u1, v, w]) hu0S)
  have hm1 : u1 ∈ V ∩ convexHull ℝ (setOfList [u0, u1, v, w]) :=
    And.intro hu1 (subset_convexHull ℝ (setOfList [u0, u1, v, w]) hu1S)
  have hvxeq : VX V (mcell 4 V [u0, u1, v, w]) = V ∩ (mcell 4 V [u0, u1, v, w]) :=
    HDTFNFZ (v := u0) hs hp hbar rfl hnull
  rw [edgeX, hvxeq, hXeq]
  exact Set.mem_setOf.mpr ⟨u0, u1, rfl, hm0, hm1, hne⟩

/-- **情形 A 全支**（capstone 的 `hl vl < √2` 分支，capstone 形）：
X := `mcell 4 V vl`（= 四点凸包），mcellSet 成员（`mcell` 分派 + barV）、
edgeX 成员（`p24_caseA_edgeX`）、非平坦（含于任一过轴平坦半平面
`{z | azim u0 u1 q z = 0}` ⇒ 四点全落该水平集 ⇒ 共面，与
`p24_caseA_coplanar_false`（W-楔代数收口，2026-10-11 波）矛盾；水平集
共面由 `coplanarAzimEq`（HOL COPLANAR_AZIM_EQ，真证）给出）。 -/
private theorem p24_caseA_branch (V : Set V3) (u0 u1 : V3) (vl : List V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1])
    (hhl : hl vl < Real.sqrt 2) :
    ∃ X : Set V3, X ∈ mcellSet V ∧ ({u0, u1} : Set V3) ∈ edgeX V X ∧
      ∀ q : V3, ¬ Collinear3 u0 u1 q →
        ¬ ((X : Set V3) ⊆ {z : V3 | azim u0 u1 q z = 0}) := by
  have hncp : ¬ Coplanar ℝ (setOfList vl) := fun hcp =>
    p24_caseA_coplanar_false V u0 u1 vl hs hp hu0 hu1 hne hbar htr hhl hcp
  obtain ⟨q0, q1, q2, q3, hvll⟩ := BARV_3_EXPLICIT V vl hbar
  subst hvll
  have htrq : truncateSimplex 1 [q0, q1, q2, q3] = [q0, q1] := by
    rw [truncateSimplex1_pair [q0, q1, q2, q3] (by norm_num)]
    simp [elV]
  have hpair01 : [u0, u1] = [q0, q1] := htr.symm.trans htrq
  injection hpair01 with e0 e1l
  injection e1l with e1 e1nil
  subst e0
  subst e1
  have hXeq : mcell 4 V [u0, u1, q2, q3] = convexHull ℝ
      (setOfList [u0, u1, q2, q3]) := by
    show mcell4 V [u0, u1, q2, q3] = _
    rw [mcell4, if_pos hhl]
  refine ⟨mcell 4 V [u0, u1, q2, q3],
    Set.mem_setOf.mpr ⟨4, [u0, u1, q2, q3], rfl, hbar⟩,
    p24_caseA_edgeX V u0 u1 q2 q3 hs hp hu0 hu1 hne hbar hhl hncp, ?_⟩
  intro q hq hsub
  rw [hXeq] at hsub
  refine hncp (_root_.Coplanar.subset
    (fun z hz => hsub (subset_convexHull ℝ (setOfList [u0, u1, q2, q3]) hz))
    (coplanarAzimEq u0 u1 q 0 (fun hc _ => (hq hc).elim)))

/-- **情形 B3 · mxi 仿射排除核**：叶四元组 `vl`（`barV V 3 vl` +
`truncateSimplex 1 vl = [u0,u1]`）+ 情形 B3 判别（`√2 ≤ hl vl` 且
`hl (truncateSimplex 2 vl) < √2`）下，
`mxi V vl ∉ affineSpan ℝ {u0, u1, elV vl 2}`（三角形过轴平面）且 mxi 离轴
（`¬ Collinear3 u0 u1 (mxi V vl)`）。
路线（路线图第 5 条"对齐排除"的 mcell-3 支，全初等）：
(1) `p24_leaf_singleton` 给 ω₃ = 四点 Voronoi 单点 = 外心 `a`（PA12:1677 +
PA5:2296，真证）；`OMEGA_LIST_N_IN_VORONOI_LIST`（PA5:2253，真证）给
ω₂ ∈ 三重点 Voronoi 胞——两者与 u0,u1,v 等距；
(2) `p24_tri_gamma`（真证）给三角形坐标数据 `h, t, wg`（垂距、轴坐标、
外心垂坐标积）与 γ 关系 `2·wg·h = h² + t² − d·t`、外接半径平方
`r₃² = d²/4 + wg²`；
(3) `p24_axial_eqs` 把 ω₂、a 钉在双仿射方程 `(x−mid)⊥e3`、
`(x−mid)⬝P = wg·h` 上；`MXI_EXISTS_concl`（PA2 公开残件——**sorried
上游输入**，本波唯一非真证输入；HL marchal2.hl `MXI_EXPLICIT` 的
pack_concl 接口，PA11 `MXI_EXPLICIT` 同源）给 `mxi ∈ convexHull {ω₂, ω₃}`
与 `dist(u0,mxi) = √2`；segment 权重线性性把双仿射方程传给 mxi；
(4) mxi 离轴：若 `Collinear3 u0 u1 mxi` 则 `mxi = u0 + c•(u1−u0)`，与
E1（轴正交）联立得 `c = 1/2`，于是 `dist(u0,mxi) = d/2 < √2`，矛盾；
(5) 反设 `mxi ∈ affineSpan {u0,u1,v}`：坐标
`mxi−u0 = α•(u1−u0) + β•(v−u0)` 与双仿射方程联立得 `αd + βt = d/2`、
`β = wg/h`，于是 `dist(u0,mxi)² = d²/4 + wg² = r₃² < 2`，与
`dist(u0,mxi) = √2` 矛盾。 -/
private theorem p24_caseB3_aux (V : Set V3) (u0 u1 : V3) (vl : List V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1])
    (hd8 : dist u0 u1 < Real.sqrt 8)
    (hr4 : Real.sqrt 2 ≤ hl vl)
    (hr3 : hl (truncateSimplex 2 vl) < Real.sqrt 2) :
    ¬ Collinear3 u0 u1 (mxi V vl) ∧
      mxi V vl ∉ (affineSpan ℝ ({u0, u1, elV vl 2} : Set V3)) := by
  -- 0. 叶四元组显式化 + u0/u1 识别（情形 A 同款）
  obtain ⟨q0, q1, q2, q3, hvll⟩ := BARV_3_EXPLICIT V vl hbar
  subst hvll
  have htrq : truncateSimplex 1 [q0, q1, q2, q3] = [q0, q1] := by
    rw [truncateSimplex1_pair [q0, q1, q2, q3] (by norm_num)]
    simp [elV]
  have hpair01 : [u0, u1] = [q0, q1] := htr.symm.trans htrq
  injection hpair01 with e0 e1l
  injection e1l with e1 e1nil
  subst e0
  subst e1
  set v : V3 := q2 with hvdef
  set w : V3 := q3 with hwdef
  -- 1. 截断读出 + barV V 2 + v 非共线
  have htr2 : truncateSimplex 2 [u0, u1, v, w] = [u0, u1, v] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 v w).2
  have hset3 : setOfList [u0, u1, v] = ({u0, u1, v} : Set V3) := by
    ext y
    simp [setOfList]
  have hr3' : hl [u0, u1, v] < Real.sqrt 2 := by
    have hcopy := hr3
    rw [htr2] at hcopy
    exact hcopy
  have hbar2 : barV V 2 [u0, u1, v] := by
    have hb := TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, v, w] hbar (by norm_num)
    rwa [htr2] at hb
  have htr1 : setOfList (truncateSimplex 1 [u0, u1, v]) = ({u0, u1} : Set V3) := by
    rw [truncateSimplex1_pair [u0, u1, v] (by have := hbar2.1; omega)]
    ext x
    simp [setOfList, elV]
  obtain ⟨-, -, hnc⟩ := p24_REUHADY_extract hp hbar2 htr1 rfl
  -- 2. 标架数值
  have hdgt : 2 ≤ dist u0 u1 := hp.dist_ge_two hu0 hu1 hne
  have hdne : (dist u0 u1 : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hdgt)
  have hu0u1n : (u1 - u0 : V3) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨e1, e2, e3, hon, hax0⟩ := exists_on3_eq_smul (u1 - u0) hu0u1n
  have haxd : (u1 - u0 : V3) = dist u0 u1 • e3 := by
    have hn : ‖u1 - u0‖ = dist u0 u1 := (dist_eq_norm u1 u0).symm.trans (dist_comm u1 u0)
    rw [hn] at hax0
    exact hax0
  have h33 : e3 ⬝ᵥ e3 = 1 := hon.2.2.1
  set mid : V3 := u0 + (dist u0 u1 / 2) • e3 with hmiddef
  -- 3. tri-数据与垂分量 P
  obtain ⟨h, t, wg, hhpos, hteq, hPn0, hrad, hgam, hnn⟩ :=
    p24_tri_gamma u0 u1 v hon haxd hne hnc (p24_cc_exists u0 u1 v hne hnc)
  have hPex : ∃ P : V3, (v - u0 : V3) = t • e3 + P ∧ P ⬝ᵥ e3 = 0 ∧ ‖P‖ = h := by
    refine ⟨(v - u0 : V3) - t • e3, ?_, ?_, ?_⟩
    · have e0 : (((v - u0 : V3) - t • e3 : V3) + t • e3) = (v - u0 : V3) := by module
      rw [add_comm, e0]
    · have hsmul : ((t • e3 : V3) ⬝ᵥ e3) = t * (e3 ⬝ᵥ e3) := by
        rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]
      have hsub' : (((v - u0 : V3) - t • e3 : V3) ⬝ᵥ e3)
          = ((v - u0 : V3) ⬝ᵥ e3) - ((t • e3 : V3) ⬝ᵥ e3) := by
        rw [WithLp.ofLp_sub, sub_dotProduct]
      rw [hsub', hsmul, hteq, h33]
      ring
    · have he : ((v - u0 : V3) - t • e3 : V3)
          = (v - u0) - ((v - u0) ⬝ᵥ e3) • e3 := by rw [hteq]
      rw [he]
      exact hPn0
  obtain ⟨P, hv', hPe3, hPn⟩ := hPex
  have hPe3' : e3 ⬝ᵥ P = 0 := by rw [dotProduct_comm]; exact hPe3
  -- 4. ω₂ 的三重点等距
  have hw2mem := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, v, w] 3 2 hbar (by norm_num)
  rw [htr2] at hw2mem
  have hvn4 : voronoiNondg V [u0, u1, v, w] :=
    hbar.2 [u0, u1, v, w] ⟨⟨[], by rw [List.append_nil]⟩, by simp⟩
  have hsubV : setOfList [u0, u1, v, w] ⊆ V := hvn4.2.1
  have hvV : v ∈ V := hsubV (by simp [setOfList])
  have hVsub3 : setOfList [u0, u1, v] ⊆ V := by
    intro x hx
    rw [hset3] at hx
    rcases hx with hx1 | hx1 | hx1
    · rw [hx1]; exact hu0
    · rw [hx1]; exact hu1
    · rw [hx1]; exact hvV
  have hw2cell : ∀ z ∈ ({u0, u1, v} : Set V3), ∀ y ∈ V,
      dist (omegaListN V [u0, u1, v, w] 2) z
        ≤ dist (omegaListN V [u0, u1, v, w] 2) y := by
    intro z hz y hy
    have h0 : (omegaListN V [u0, u1, v, w] 2 : V3)
        ∈ ⋂₀ {voronoiClosed V p | p ∈ setOfList [u0, u1, v]} := hw2mem
    exact h0 (voronoiClosed V z) ⟨z, by rw [hset3]; exact hz, rfl⟩ y hy
  have heqw2u1 : dist (omegaListN V [u0, u1, v, w] 2) u0
      = dist (omegaListN V [u0, u1, v, w] 2) u1 :=
    le_antisymm (hw2cell u0 (by simp) u1 hu1) (hw2cell u1 (by simp) u0 hu0)
  have heqw2v : dist (omegaListN V [u0, u1, v, w] 2) u0
      = dist (omegaListN V [u0, u1, v, w] 2) v :=
    le_antisymm (hw2cell u0 (by simp) v hvV) (hw2cell v (by simp) u0 hu0)
  -- 5. ω₃ = a（四点 Voronoi 单点 = 外心）与 a 的等距
  obtain ⟨a, ha1, ha2, -⟩ :=
    VORONOI_LIST_3_SINGLETON_EXPLICIT V [u0, u1, v, w] hp hs hbar
  have hw3eq : omegaListN V [u0, u1, v, w] 3 = a := by
    have h3 := OMEGA_LIST_IN_VORONOI_LIST (V := V) (ul := [u0, u1, v, w]) (k := 3) hbar
    rw [ha1] at h3
    exact Set.mem_singleton_iff.mp h3
  have hamem : (a : V3) ∈ voronoiList V [u0, u1, v, w] := by rw [ha1]; simp
  have hacell : ∀ z ∈ ({u0, u1, v, w} : Set V3), ∀ y ∈ V, dist a z ≤ dist a y := by
    intro z hz y hy
    have h0 : (a : V3) ∈ ⋂₀ {voronoiClosed V p | p ∈ setOfList [u0, u1, v, w]} := hamem
    exact h0 (voronoiClosed V z) ⟨z, by simp [setOfList]; exact hz, rfl⟩ y hy
  have heqa1 : dist a u0 = dist a u1 :=
    le_antisymm (hacell u0 (by simp) u1 hu1) (hacell u1 (by simp) u0 hu0)
  have heqav : dist a u0 = dist a v :=
    le_antisymm (hacell u0 (by simp) v hvV) (hacell v (by simp) u0 hu0)
  -- 6. 双仿射方程于 ω₂ 与 a
  obtain ⟨hE2e3, hE2P⟩ := p24_axial_eqs u0 u1 v mid e3 P (dist u0 u1) t h wg
    (omegaListN V [u0, u1, v, w] 2) haxd hdne h33 hmiddef hv' hPe3 hPn hhpos hgam
    heqw2u1 heqw2v
  obtain ⟨hEae3, hEaP⟩ := p24_axial_eqs u0 u1 v mid e3 P (dist u0 u1) t h wg
    a haxd hdne h33 hmiddef hv' hPe3 hPn hhpos hgam heqa1 heqav
  -- 7. mxi 数据 + segment 权重线性传播
  obtain ⟨hmx1, hmx2⟩ := MXI_EXISTS_concl V [u0, u1, v, w] hs hp hbar hr3 hr4
  have hmx2' : dist (mxi V [u0, u1, v, w]) u0 = Real.sqrt 2 := by
    rwa [show hdV [u0, u1, v, w] = u0 from rfl] at hmx2
  rw [convexHull_pair, hw3eq] at hmx1
  obtain ⟨s1, s2, hs10, hs20, hssum, hmxeq⟩ := hmx1
  have hζeq : ((mxi V [u0, u1, v, w] - mid : V3))
      = (s1 : ℝ) • ((omegaListN V [u0, u1, v, w] 2 - mid : V3))
        + (s2 : ℝ) • ((a - mid : V3)) := by
    rw [← hmxeq]
    rw [show ((s1 • omegaListN V [u0, u1, v, w] 2 + s2 • a : V3) - mid : V3)
        = (s1 • omegaListN V [u0, u1, v, w] 2 + s2 • a : V3) - (1 : ℝ) • mid from by
        rw [one_smul]]
    rw [← hssum]
    module
  have hE1m : ((mxi V [u0, u1, v, w] - mid : V3)) ⬝ᵥ e3 = 0 := by
    rw [hζeq]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hE2e3, hEae3]
    ring
  have hE2m : ((mxi V [u0, u1, v, w] - mid : V3)) ⬝ᵥ P = wg * h := by
    rw [hζeq]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hE2P, hEaP]
    rw [← add_mul, hssum, one_mul]
  -- 8. mxi 离轴
  have hmxnc : ¬ Collinear3 u0 u1 (mxi V [u0, u1, v, w]) := by
    intro hcol
    obtain ⟨c, hc⟩ :=
      (collinear3_iff_smul (v := u0) (w := u1) (w1 := mxi V [u0, u1, v, w])
        (Ne.symm hne)).mp hcol
    have hsplit : ((mxi V [u0, u1, v, w] - u0 : V3))
        = (mxi V [u0, u1, v, w] - mid) + (dist u0 u1 / 2) • e3 := by
      rw [hmiddef]; module
    have hcd : ((mxi V [u0, u1, v, w] - u0 : V3)) ⬝ᵥ e3 = dist u0 u1 / 2 := by
      rw [hsplit]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, hE1m, h33]
      ring
    have hcval : ((mxi V [u0, u1, v, w] - u0 : V3)) ⬝ᵥ e3
        = c * dist u0 u1 := by
      rw [hc, haxd]
      simp only [WithLp.ofLp_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        h33]
      ring
    have hchalf : c = 1 / 2 := by
      have hceq : c * dist u0 u1 = dist u0 u1 / 2 := hcval.symm.trans hcd
      have h2 : c * dist u0 u1 = (1 / 2) * dist u0 u1 := by rw [hceq]; ring
      exact mul_right_cancel₀ hdne h2
    have hnorm : dist (mxi V [u0, u1, v, w]) u0 = dist u0 u1 / 2 := by
      rw [dist_eq_norm, hc, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (by rw [hchalf]; norm_num))]
      have hdn : ‖(u1 - u0 : V3)‖ = dist u0 u1 :=
        (dist_eq_norm u1 u0).symm.trans (dist_comm u1 u0)
      rw [hdn, hchalf]
      ring
    rw [hnorm] at hmx2'
    have h82 : (Real.sqrt 8 : ℝ) / 2 = Real.sqrt 2 := by
      have h8 : (Real.sqrt 8 : ℝ) = 2 * Real.sqrt 2 := by
        rw [show (8 : ℝ) = 4 * 2 from by norm_num, Real.sqrt_mul (by norm_num)]
        norm_num
      rw [h8]
      field_simp
    have hhalf : dist u0 u1 / 2 < Real.sqrt 2 := by linarith [hd8, h82]
    linarith
  -- 9. 反设 mxi ∈ affineSpan：坐标联立
  refine ⟨hmxnc, fun hmxspan => ?_⟩
  have hmxspan' : (mxi V [u0, u1, v, w] : V3)
      ∈ (affineSpan ℝ ({u0, u1, v} : Set V3)) :=
    hmxspan
  obtain ⟨α, β, hrep⟩ := Submodule.mem_span_pair.mp (p24_affspan_dir hmxspan')
  have hξ : ((mxi V [u0, u1, v, w] - mid : V3))
      = ((α * dist u0 u1 + β * t - dist u0 u1 / 2 : ℝ)) • e3 + (β : ℝ) • P := by
    rw [show ((mxi V [u0, u1, v, w] - mid : V3))
        = (mxi V [u0, u1, v, w] - u0) - (mid - u0) from by rw [hmiddef]; module,
      ← hrep, hv', haxd, hmiddef]
    module
  have hPnP : P ⬝ᵥ P = h ^ 2 := by rw [← norm_sq_eq_dot P, hPn]
  have hEdot3 : ((mxi V [u0, u1, v, w] - mid : V3)) ⬝ᵥ e3
      = (α * dist u0 u1 + β * t - dist u0 u1 / 2 : ℝ) := by
    rw [hξ]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hPe3, h33]
    ring
  have hsum2 : α * dist u0 u1 + β * t = dist u0 u1 / 2 := by
    have hz : (0 : ℝ) = α * dist u0 u1 + β * t - dist u0 u1 / 2 :=
      hE1m.symm.trans hEdot3
    linarith
  have hPe3' : e3 ⬝ᵥ P = 0 := by rw [dotProduct_comm]; exact hPe3
  have hEdotP : ((mxi V [u0, u1, v, w] - mid : V3)) ⬝ᵥ P = (β : ℝ) * (P ⬝ᵥ P) := by
    rw [hξ]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hPe3']
    ring
  have hβ : β * h ^ 2 = wg * h := by
    have h1 : (β : ℝ) * (P ⬝ᵥ P) = wg * h := by
      rw [← hEdotP]
      exact hE2m
    rwa [hPnP] at h1
  have hbval : β = wg / h := by
    have h2 : β * h = wg := by
      have key : (β * h - wg) * h = 0 := by
        have e1 : (β * h - wg) * h = β * h ^ 2 - wg * h := by ring
        rw [e1, hβ, sub_self]
      rcases mul_eq_zero.mp key with h3 | h3
      · linarith
      · exact absurd h3 (ne_of_gt hhpos)
    exact ((div_eq_iff (ne_of_gt hhpos)).mpr h2.symm).symm
  have he3n : ∀ r : ℝ, ‖((r : ℝ) • e3 : V3)‖ ^ 2 = r ^ 2 := by
    intro r
    have h0 : ‖((r : ℝ) • e3 : V3)‖ ^ 2 = ((r : ℝ) • e3 : V3) ⬝ᵥ ((r : ℝ) • e3 : V3) :=
      norm_sq_eq_dot _
    simp only [h0, WithLp.ofLp_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      h33]
    ring
  have hwnorm : ‖(mxi V [u0, u1, v, w] - u0 : V3)‖ ^ 2
      = ((α * dist u0 u1 + β * t : ℝ)) ^ 2 + (β : ℝ) ^ 2 * h ^ 2 := by
    have hw : ((mxi V [u0, u1, v, w] - u0 : V3))
        = ((α * dist u0 u1 + β * t : ℝ)) • e3 + (β : ℝ) • P := by
      rw [← hrep, hv', haxd]; module
    have horth : (((α * dist u0 u1 + β * t : ℝ)) • e3 : V3) ⬝ᵥ ((β : ℝ) • P : V3) = 0 := by
      simp only [WithLp.ofLp_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        hPe3', mul_zero]
    have hb2 : ‖((β : ℝ) • P : V3)‖ ^ 2 = (β : ℝ) ^ 2 * h ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hPn]
    rw [hw, p24_norm_sq_of_orth horth, he3n, hb2]
  have hsq2 : ‖(mxi V [u0, u1, v, w] - u0 : V3)‖ ^ 2 = 2 := by
    rw [← dist_eq_norm (a := mxi V [u0, u1, v, w]) (b := u0), hmx2']
    exact Real.sq_sqrt (by norm_num)
  have hwnorm' : ‖(mxi V [u0, u1, v, w] - u0 : V3)‖ ^ 2
      = dist u0 u1 ^ 2 / 4 + wg ^ 2 := by
    rw [hwnorm, hsum2, hbval]
    field_simp
    ring
  -- 10. 终局：r₃² = 2 与 r₃ < √2 矛盾
  have hradV : hl [u0, u1, v] = radV ({u0, u1, v} : Set V3) := by
    show radV (setOfList [u0, u1, v]) = _
    rw [hset3]
  have hr3sq : radV ({u0, u1, v} : Set V3) ^ 2 < 2 := by
    rw [hradV] at hr3'
    have hs2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [hr3', hnn, hs2]
  linarith [hrad, hwnorm', hsq2, hr3sq]

/-- **情形 B3 · 非平坦排除**：情形 B3 判别（`√2 ≤ hl vl` 且
`hl (truncateSimplex 2 vl) < √2`，X := `mcell 3 V vl` = 三角形截断凸包 ∪
{mxi}）下，胞不含于任一过轴平坦半平面。反设 `X ⊆ {z | azim u0 u1 q z = 0}`：
胞含 v（三角形截断顶点，凸包成员）与 mxi（mcell 3 定义的第二并集支）⇒
`azim u0 u1 q v = 0`、`azim u0 u1 q mxi = 0`；`azim_eq_zero_iff(_alt)`
（HOL AZIM_EQ_0/_ALT）把 q、mxi 分别钉进 affGt {u0,u1} {v}、affGt {u0,u1}
{q}，前者经 `p24_affGt_mem_affineSpan_triple` 给 `q ∈ affineSpan {u0,u1,v}`
（v 非共线经 `p24_REUHADY_extract`），span 单调传输得
`mxi ∈ affineSpan {u0,u1,v}`，与 `p24_caseB3_aux` 矛盾。 -/
private theorem p24_caseB3_not_flat (V : Set V3) (u0 u1 : V3) (vl : List V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1])
    (hd8 : dist u0 u1 < Real.sqrt 8)
    (hr4 : Real.sqrt 2 ≤ hl vl)
    (hr3 : hl (truncateSimplex 2 vl) < Real.sqrt 2)
    (q : V3) (hq : ¬ Collinear3 u0 u1 q) :
    ¬ (mcell3 V vl ⊆ {z : V3 | azim u0 u1 q z = 0}) := by
  obtain ⟨hmxnc, hnotmem⟩ :=
    p24_caseB3_aux V u0 u1 vl hs hp hu0 hu1 hne hbar htr hd8 hr4 hr3
  intro hsub
  have hbar2 : barV V 2 (truncateSimplex 2 vl) :=
    TRUNCATE_SIMPLEX_BARV V 2 3 vl hbar (by omega)
  have hv2 : elV (truncateSimplex 2 vl) 2 = elV vl 2 := by
    have h3 : 2 + 1 ≤ vl.length := by rw [hbar.1]; omega
    exact EL_TRUNCATE_SIMPLEX vl 2 2 h3 (by omega)
  have htr1 : setOfList (truncateSimplex 1 (truncateSimplex 2 vl))
      = ({u0, u1} : Set V3) := by
    have hij : (1 : ℕ) ≤ 2 := by omega
    have hlen : 2 + 1 ≤ vl.length := by rw [hbar.1]; omega
    rw [TRUNCATE_TRUNCATE_SIMPLEX vl 1 2 hij hlen, htr]
    ext x
    simp [setOfList, elV]
  have hset3 : setOfList (truncateSimplex 2 vl) = ({u0, u1, elV vl 2} : Set V3) :=
    p24_setOfList_pair2 hbar2 htr1 hv2.symm
  have hnc : ¬ Collinear3 u0 u1 (elV (truncateSimplex 2 vl) 2) :=
    (p24_REUHADY_extract hp hbar2 htr1 rfl).2.2
  rw [hv2] at hnc
  have hvcell : elV vl 2 ∈ mcell3 V vl := by
    rw [mcell3, if_pos ⟨hr3, hr4⟩]
    refine subset_convexHull ℝ _ (Set.mem_union_left _ (Set.mem_setOf.mpr ?_))
    rw [← hv2]
    exact p24_elV_mem (by have := hbar2.1; omega)
  have hxcell : mxi V vl ∈ mcell3 V vl := by
    rw [mcell3, if_pos ⟨hr3, hr4⟩]
    exact subset_convexHull ℝ _ (Set.mem_union_right _ (Set.mem_singleton _))
  have hvaz : azim u0 u1 q (elV vl 2) = 0 := hsub hvcell
  have hxaz : azim u0 u1 q (mxi V vl) = 0 := hsub hxcell
  have hqgt : q ∈ affGt {u0, u1} {elV vl 2} := (azim_eq_zero_iff hq hnc).mp hvaz
  have hqspan : q ∈ (affineSpan ℝ ({u0, u1, elV vl 2} : Set V3)) :=
    p24_affGt_mem_affineSpan_triple u0 u1 (elV vl 2) q hqgt
  have hmxgt : mxi V vl ∈ affGt {u0, u1} {q} :=
    (azim_eq_zero_iff_alt hq hmxnc).mp hxaz
  have hmxmem3 : mxi V vl ∈ (affineSpan ℝ ({u0, u1, q} : Set V3)) :=
    p24_affGt_mem_affineSpan_triple u0 u1 q _ hmxgt
  have hmxspan : (mxi V vl : V3) ∈ (affineSpan ℝ ({u0, u1, elV vl 2} : Set V3)) :=
    (affineSpan_le.mpr (by
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact mem_affineSpan (k := ℝ) (by simp)
      · exact mem_affineSpan (k := ℝ) (by simp)
      · exact hqspan)) hmxmem3
  exact hnotmem hmxspan

/-- **情形 B3 · edgeX 成员件**：B3 判别下 `{u0,u1} ∈ edgeX V (mcell3 V vl)`
——`p24_caseB3_aux` 给 `mxi ∉ affineSpan {u0,u1,v}`；若四点集
{u0,u1,v,mxi} 的 vectorSpan finrank ≤ 2，结合 vectorSpan {u0,u1,v} 的
finrank = 2（MHFTTZN1 的 `affDim` 读出）两子空间相等得
mxi − u0 ∈ vectorSpan {u0,u1,v}，即 mxi ∈ affineSpan {u0,u1,v}，矛盾；于是
vectorSpan finrank = 3 ⇒ affineSpan = ⊤ ⇒ 正体积 ⇒ 非 nullSet，HDTFNFZ
读出 edgeX。 -/
private theorem p24_caseB3_edgeX (V : Set V3) (u0 u1 : V3) (vl : List V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1])
    (hd8 : dist u0 u1 < Real.sqrt 8)
    (hr4 : Real.sqrt 2 ≤ hl vl)
    (hr3 : hl (truncateSimplex 2 vl) < Real.sqrt 2) :
    ({u0, u1} : Set V3) ∈ edgeX V (mcell3 V vl) := by
  obtain ⟨hmxnc, hnotmem⟩ :=
    p24_caseB3_aux V u0 u1 vl hs hp hu0 hu1 hne hbar htr hd8 hr4 hr3
  have hbar2 : barV V 2 (truncateSimplex 2 vl) :=
    TRUNCATE_SIMPLEX_BARV V 2 3 vl hbar (by omega)
  have hv2 : elV (truncateSimplex 2 vl) 2 = elV vl 2 := by
    have h3 : 2 + 1 ≤ vl.length := by rw [hbar.1]; omega
    exact EL_TRUNCATE_SIMPLEX vl 2 2 h3 (by omega)
  have htr1 : setOfList (truncateSimplex 1 (truncateSimplex 2 vl))
      = ({u0, u1} : Set V3) := by
    have hij : (1 : ℕ) ≤ 2 := by omega
    have hlen : 2 + 1 ≤ vl.length := by rw [hbar.1]; omega
    rw [TRUNCATE_TRUNCATE_SIMPLEX vl 1 2 hij hlen, htr]
    ext x
    simp [setOfList, elV]
  have hset3 : setOfList (truncateSimplex 2 vl) = ({u0, u1, elV vl 2} : Set V3) :=
    p24_setOfList_pair2 hbar2 htr1 hv2.symm
  have hnc : ¬ Collinear3 u0 u1 (elV (truncateSimplex 2 vl) 2) :=
    (p24_REUHADY_extract hp hbar2 htr1 rfl).2.2
  rw [hv2] at hnc
  have hvV : elV vl 2 ∈ V := by
    have hvn : voronoiNondg V (truncateSimplex 2 vl) :=
      hbar2.2 (truncateSimplex 2 vl)
        ⟨⟨[], by rw [List.append_nil]⟩, by have := hbar2.1; omega⟩
    have hmem : elV vl 2 ∈ setOfList (truncateSimplex 2 vl) := by
      rw [hset3]
      simp
    exact hvn.2.1 hmem
  have hneS : (setOfList (truncateSimplex 2 vl) : Set V3) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp
      (⟨u0, by rw [hset3]; simp⟩ :
        (setOfList (truncateSimplex 2 vl) : Set V3).Nonempty)
  have hfr2 : Module.finrank ℝ (vectorSpan ℝ (setOfList (truncateSimplex 2 vl))) = 2 := by
    have hd2 : affDim (setOfList (truncateSimplex 2 vl)) = (2 : ℤ) :=
      MHFTTZN1 V (truncateSimplex 2 vl) 2 hp hbar2
    rw [affDim, if_neg hneS] at hd2
    norm_cast at hd2
  have hfr4 : Module.finrank ℝ (vectorSpan ℝ
      ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3))) = 3 := by
    have hle : Module.finrank ℝ (vectorSpan ℝ
        ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3))) ≤ 3 := by
      have h1 := Submodule.finrank_le (vectorSpan ℝ
        ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3)))
      rw [finrank_euclideanSpace_fin] at h1
      exact h1
    have hge : ¬ (Module.finrank ℝ (vectorSpan ℝ
        ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3))) ≤ 2) := by
      intro hcon
      have heq : vectorSpan ℝ (setOfList (truncateSimplex 2 vl))
          = vectorSpan ℝ
              ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3)) :=
        Submodule.eq_of_le_of_finrank_le
          (vectorSpan_mono ℝ (Set.subset_union_left)) (le_trans hcon hfr2.ge)
      have hmem : (mxi V vl - u0 : V3) ∈
          (affineSpan ℝ
              ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3))).direction :=
        AffineSubspace.vsub_mem_direction
          (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp [hset3]))
      rw [direction_affineSpan] at hmem
      have hdir' : (mxi V vl - u0 : V3) ∈ vectorSpan ℝ
          (setOfList (truncateSimplex 2 vl)) := by
        rw [heq.symm] at hmem
        exact hmem
      have hu0m : u0 ∈ (affineSpan ℝ ({u0, u1, elV vl 2} : Set V3)) :=
        mem_affineSpan (k := ℝ) (by simp)
      have hvadd := AffineSubspace.vadd_mem_of_mem_direction
        (by rw [direction_affineSpan, ← hset3]; exact hdir') hu0m
      rw [show ((mxi V vl - u0 : V3) +ᵥ u0) = mxi V vl from
        vsub_vadd (mxi V vl) u0] at hvadd
      exact hnotmem hvadd
    omega
  have hspan : affineSpan ℝ
      ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3)) = ⊤ :=
    p24_affineSpan_top_of_finrank
      (⟨mxi V vl, Set.mem_union_right _ (Set.mem_singleton _)⟩ :
        ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3)).Nonempty) hfr4
  have hvpos : 0 < volume (convexHull ℝ
      ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3))) :=
    p24_volume_pos_of_affineSpan hspan
  have hnull : ¬ nullSet (mcell3 V vl) := by
    intro hc
    rw [nullSet, mcell3, if_pos ⟨hr3, hr4⟩] at hc
    exact hvpos.ne hc.symm
  have hvxeq : VX V (mcell3 V vl) = V ∩ (mcell3 V vl) :=
    HDTFNFZ (v := u0) hs hp hbar (show mcell3 V vl = mcell 3 V vl from rfl) hnull
  have hXeq : mcell3 V vl = convexHull ℝ
      (setOfList (truncateSimplex 2 vl) ∪ {mxi V vl}) := by
    rw [mcell3, if_pos ⟨hr3, hr4⟩]
  have hm0 : u0 ∈ V ∩ convexHull ℝ
      (setOfList (truncateSimplex 2 vl) ∪ {mxi V vl}) := by
    refine ⟨hu0, subset_convexHull ℝ ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3))
      (Set.mem_union_left _ (by rw [hset3]; simp))⟩
  have hm1 : u1 ∈ V ∩ convexHull ℝ
      (setOfList (truncateSimplex 2 vl) ∪ {mxi V vl}) := by
    refine ⟨hu1, subset_convexHull ℝ ((setOfList (truncateSimplex 2 vl) ∪ {mxi V vl} : Set V3))
      (Set.mem_union_left _ (by rw [hset3]; simp))⟩
  rw [edgeX, hvxeq, hXeq]
  exact Set.mem_setOf.mpr ⟨u0, u1, rfl, hm0, hm1, hne⟩

/-- **情形 B3 全支**（capstone 的 `r₄ ≥ √2 ∧ r₃ < √2` 分支，capstone 形）：
X := `mcell 3 V vl`，mcellSet 成员（`mcell` 分派 + barV）、edgeX 成员
（`p24_caseB3_edgeX`）、非平坦排除（`p24_caseB3_not_flat`）。 -/
private theorem p24_caseB3_branch (V : Set V3) (u0 u1 : V3) (vl : List V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1])
    (hd8 : dist u0 u1 < Real.sqrt 8)
    (hr4 : Real.sqrt 2 ≤ hl vl)
    (hr3 : hl (truncateSimplex 2 vl) < Real.sqrt 2) :
    ∃ X : Set V3, X ∈ mcellSet V ∧ ({u0, u1} : Set V3) ∈ edgeX V X ∧
      ∀ q : V3, ¬ Collinear3 u0 u1 q →
        ¬ ((X : Set V3) ⊆ {z : V3 | azim u0 u1 q z = 0}) :=
  ⟨mcell3 V vl, Set.mem_setOf.mpr ⟨3, vl, rfl, hbar⟩,
    p24_caseB3_edgeX V u0 u1 vl hs hp hu0 hu1 hne hbar htr hd8 hr4 hr3,
    p24_caseB3_not_flat V u0 u1 vl hs hp hu0 hu1 hne hbar htr hd8 hr4 hr3⟩

/-! ## (β) 支第四波：情形 B2 结构件群（2026-10-12 波）

**原处方纠错（实质，2026-10-12 第四波侦察）**：第三波 capstone docstring 记
B2 支「`mxi ∈ X` 由 `dist(u0,mxi) = √2`」——依据是 PA2 公开残件
`MXI_EXISTS_concl`。但 HL 本体 `MXI_EXPLICIT`（marchal2.hl:2516）假设含
`hl (truncate_simplex 2 ul) < sqrt 2`：它只是 **B3 支**的定理。B2 支
（`r₃ ≥ √2`）中 `mxi V vl = ω₂`（`mxi` 定义 if 正支，见
`p24_caseB2_mxi_eq`），而 `ω₂ ∈ T ⊆ L`（三点 voronoi 胞 ⊆ 外轴线
`L = {x | dist x u0 = dist x u1 = dist x v}`，⊥ 三角平面 Π 于外心 cc），
毕氏恒等式 `dist(u0,ω₂)² = r₃² + ‖ω₂−cc‖² ≥ r₃`——一般 **> √2**。故
`MXI_EXISTS_concl` 在 B2 支为**假**（PA2 concl-shim 欠 `r₃ < √2` 假设；
记账待 PA2 车道修；B3 波的使用不受影响——B3 分支假设恰为 `r₃ < √2`）。

**修正后 B2 路线**（记档，下两波执行；支级残件见 `p24_caseB2_branch`）：
X := `mcell 2 V vl` = (两对称 `rconeGe`，`a = hl (truncateSimplex 1 vl)/√2
= d/(2√2) < 1`) ∩ `affGe {u0,u1} {ω₂, ω₃}`（Affsign 非负权 = 四点凸包
语义）。
• **泛具子情形 ω₂ ≠ ω₃**：ω₂、ω₃ 同在外轴线 L 上（ω₂ ∈ T ⊆ L；ω₃ = 四点
  外心 ∈ L，经 singleton-voronoi 等距；cc ≠ mid ⟸ r₃ ≥ √2 > d/2）。X 凸
  （两 rcone 凸 + `p24_rconeGe_convex` + 凸包凸）、含轴段 [u0,u1]
  （`p24_caseB2_ends_mem`）与近轴双楔：s 为轴段内点，g(x) := a‖x−u0‖ −
  (x−u0)⬝ê 是 (a+1)-Lipschitz、g(s) = (a−1)‖s−u0‖ < 0，取
  xᵢ := s + εᵢ(ωᵢ−s)、εᵢ ≤ (1−a)‖s−u0‖/(2(a+1)‖ωᵢ−s‖) 得 xᵢ ∈ X；
  {u0,u1,x₂,x₃} 仿射独立（xᵢ−u0 = λᵢê + εᵢ(cc−mid) + εᵢτᵢn，其中
  n := ω₃−cc ⊥ Π、cc−mid ∈ Π ∖ 轴向；τ₂ ≠ τ₃ 时 n-分量与 (cc−mid)-分量
  联立零化 ⇒ 系数全零）⇒ X ⊇ 四点凸包正体积
  （`p24_volume_pos_of_affineSpan`）⇒ HDTFNFZ ⇒ edgeX。非平坦：X 的方位
  角集合为 {cc⊥+τ₂n, cc⊥+τ₃n} 张的扇形（两点方位相异 ⟺ τ₂ ≠ τ₃），任一
  q 的方位角至多占扇形一点，取异侧楔点为见证（`azim_eq_zero_iff_alt` +
  `p24_affGt_swap` 传输，B3 波同款）。
• **退化子情形 ω₂ = ω₃**：W ⊆ 平面(轴 ∪ ω₂) ⇒ X 平坦 ⇒ nullSet ⇒
  edgeX 不可得——**必须换叶**：配对胞 S = voronoiList V [u0,u1]
  （affDim = 2，barV 的 [u0,u1] 子表 voronoiNondg 强制）= 叶 fan 三角形
  并（`p24_voronoi_pair_split`），中点 p ∈ relint S（margin 严格），退化
  叶的 fan 三角 conv{p, ω₂, cc} 在 p 处为尖角扇形 ⇒ relint 圆盘余部强制
  另一叶；换叶后按该叶三分支重新装配（A/B3 支全真证可复用；仍 B2 则
  其 ω₂′ ≠ ω₃′，否则 fan 三角继续张向更异侧）——此即"支撑面引理"
  （路线图 §剩余风险：affDim(S∩H_v) = 1 + relint 内球论证）的真正角色。

本波真证：`p24_mem_affGe_base`、`p24_mem_rconeGe_apex`/
`p24_mem_rconeGe_cross`、`p24_rconeGe_convex`、`p24_caseB2_mxi_eq`、
`p24_caseB2_mcellSet`、`p24_caseB2_ends_mem`；第五波（2026-10-12）续作：
换叶件群 `p24_pair_patch_mem`/`p24_packing_finite_inter_ball_at`/
`p24_escape_direction` + 换叶主件 `p24_nondeg_leaf_exists`（本波真证），
支级装配 `p24_caseB2_branch` 全两支闭合（capstone 随之接线）。
-/

/-- affGe 基点成员：`x ∈ {a,b}` ⇒ `x ∈ affGe {a,b} t`（t 有限；Affsign
权函数取基点指示函数——权重于 t 上恒 0 ≥ 0、总和 1、加权和即 x）。 -/
private theorem p24_mem_affGe_base {a b : V3} {t : Set V3} (ht : t.Finite)
    (x : V3) (hx : x = a ∨ x = b) : x ∈ affGe {a, b} t := by
  have hK : (({a, b} : Set V3) ∪ t).Finite :=
    (Set.Finite.insert a (Set.finite_singleton b)).union ht
  have hxe : x ∈ hK.toFinset := by
    refine (Set.Finite.mem_toFinset _).mpr ?_
    rcases hx with e | e
    · rw [e]
      exact Set.mem_union_left _ (Set.mem_insert a {b})
    · rw [e]
      exact Set.mem_union_left _ (Set.mem_insert_of_mem a (Set.mem_singleton b))
  refine ⟨fun w => if w = x then 1 else 0, hK, ?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single_of_mem x hxe
      (fun b hb hne => by
        simp only [hne, if_false, zero_smul])]
    simp
  · intro w hw
    by_cases h : w = x <;> simp [h]
  · rw [Finset.sum_eq_single_of_mem x hxe
      (fun b hb hne => by
        simp only [hne, if_false])]
    simp

/-- rcone 自顶点成员：`v ∈ rconeGe v w c`（平凡支 `(x−v) = 0`）。 -/
private theorem p24_mem_rconeGe_apex {v w : V3} {c : ℝ} (_hc1 : c ≤ 1) :
    v ∈ rconeGe v w c := by
  show (v - v : V3) ⬝ᵥ (w - v) ≥ dist v v * dist w v * c
  have h0 : (v - v : V3) ⬝ᵥ (w - v) = 0 := by simp
  have h1 : dist v v * dist w v * c = 0 := by simp
  rw [h0, h1]

/-- rcone 对顶点成员：`w ∈ rconeGe v w c`（`c ≤ 1` 支：`‖w−v‖² ≥
‖w−v‖²·c`）。 -/
private theorem p24_mem_rconeGe_cross {v w : V3} {c : ℝ} (hc1 : c ≤ 1) :
    w ∈ rconeGe v w c := by
  show (w - v : V3) ⬝ᵥ (w - v) ≥ dist w v * dist w v * c
  have h1 : (w - v : V3) ⬝ᵥ (w - v) = ‖(w - v : V3)‖ ^ 2 :=
    (norm_sq_eq_dot _).symm
  have h2 : dist w v = ‖(w - v : V3)‖ := dist_eq_norm w v
  rw [h1, h2, pow_two]
  have key := mul_le_mul_of_nonneg_left hc1 (sq_nonneg ‖(w - v : V3)‖)
  rw [mul_one, pow_two] at key
  exact key

/-- rcone 锥凸性（泛具子情形 X 凸性的两 ingredient 之一；凸组合
`z = α•x + β•y` 的锥不等式 = 点积线性 + 范数凸（三角不等式）+ 权重
非负乘法）。需 `0 ≤ c`（c < 0 时锥为凸函数上水平集，凸性不真）。 -/
private theorem p24_rconeGe_convex (v w : V3) (c : ℝ) (hc0 : 0 ≤ c) :
    Convex ℝ (rconeGe v w c) := by
  intro x hx y hy α β hα hβ hαβ
  have hv : ((α • x + β • y : V3) - v) = α • (x - v) + β • (y - v) := by
    have hvs : ((α • x + β • y : V3) - v)
        = α • (x - v) + β • (y - v) + ((α + β - 1 : ℝ)) • v := by
      module
    rw [hvs]
    have hz : ((α + β - 1 : ℝ)) • v = 0 := by
      rw [← hαβ]
      simp
    rw [hz, add_zero]
  have hdot : ((α • x + β • y : V3) - v) ⬝ᵥ (w - v)
      = α * ((x - v : V3) ⬝ᵥ (w - v)) + β * ((y - v : V3) ⬝ᵥ (w - v)) := by
    rw [hv]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, smul_dotProduct,
      smul_eq_mul]
  have hdist : dist (α • x + β • y) v ≤ α * dist x v + β * dist y v := by
    have h1 : dist (α • x + β • y) v = ‖((α • x + β • y : V3) - v)‖ :=
      dist_eq_norm _ _
    have h3 : ‖α • (x - v) + β • (y - v)‖
        ≤ ‖(α : ℝ) • (x - v)‖ + ‖(β : ℝ) • (y - v)‖ := norm_add_le _ _
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hα, abs_of_nonneg hβ] at h3
    rw [h1, hv]
    calc ‖α • (x - v) + β • (y - v)‖
        ≤ α * ‖(x - v : V3)‖ + β * ‖(y - v : V3)‖ := h3
      _ = α * dist x v + β * dist y v := by
          rw [← dist_eq_norm, ← dist_eq_norm]
  have hD : 0 ≤ dist w v := dist_nonneg
  show ((α • x + β • y : V3) - v) ⬝ᵥ (w - v)
      ≥ dist (α • x + β • y) v * dist w v * c
  calc ((α • x + β • y : V3) - v) ⬝ᵥ (w - v)
      = α * ((x - v : V3) ⬝ᵥ (w - v)) + β * ((y - v : V3) ⬝ᵥ (w - v)) := hdot
    _ ≥ α * (dist x v * dist w v * c) + β * (dist y v * dist w v * c) := by
        have e1 := mul_le_mul_of_nonneg_left hx hα
        have e2 := mul_le_mul_of_nonneg_left hy hβ
        linarith
    _ = (α * dist x v + β * dist y v) * dist w v * c := by ring
    _ ≥ dist (α • x + β • y) v * dist w v * c :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdist hD) hc0

/-- **情形 B2 · mxi 读出**：`r₃ ≥ √2` 时 `mxi V vl = ω₂`（mxi 定义的 if
正支；B2 支中 mxi 即三点 voronoi 胞最近点，不再有 B3 支的 √2-球面
segment 选取——见第四波 docstring 纠错）。 -/
private theorem p24_caseB2_mxi_eq (V : Set V3) (vl : List V3)
    (hr3 : Real.sqrt 2 ≤ hl (truncateSimplex 2 vl)) :
    mxi V vl = omegaListN V vl 2 := by
  rw [mxi, if_pos hr3]

/-- **情形 B2 · mcellSet 成员**：`mcell 2` 分派 + barV。 -/
private theorem p24_caseB2_mcellSet (V : Set V3) (vl : List V3)
    (hbar : barV V 3 vl) : (mcell2 V vl : Set V3) ∈ mcellSet V :=
  Set.mem_setOf.mpr ⟨2, vl, rfl, hbar⟩

/-- **情形 B2 · 两端点成员**：mcell2 分支条件下，u0、u1 ∈ `mcell2 V
[u0,u1,v,w]`——rcone 顶点成员（自顶点 `p24_mem_rconeGe_apex` 平凡支 +
对顶点 `p24_mem_rconeGe_cross` 的 `a ≤ 1` 支，a = hl (truncate 1)/√2 < 1
由 `hd8` 经 `p24_hl_pair_lt_sqrt2`）+ affGe 基点成员
（`p24_mem_affGe_base`，t = {mxi, ω₃} 有限）。 -/
private theorem p24_caseB2_ends_mem (V : Set V3) (u0 u1 v w : V3)
    (hcond : hl (truncateSimplex 1 [u0, u1, v, w]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, v, w])
    (ha1 : hl (truncateSimplex 1 [u0, u1, v, w]) / Real.sqrt 2 ≤ 1) :
    u0 ∈ mcell2 V [u0, u1, v, w] ∧ u1 ∈ mcell2 V [u0, u1, v, w] := by
  have hfin : ({mxi V [u0, u1, v, w],
      omegaListN V [u0, u1, v, w] 3} : Set V3).Finite :=
    Set.Finite.insert _ (Set.finite_singleton _)
  constructor
  · rw [mcell2, if_pos hcond]
    simp only
    exact Set.mem_inter
      (Set.mem_inter (p24_mem_rconeGe_apex ha1) (p24_mem_rconeGe_cross ha1))
      (p24_mem_affGe_base hfin u0 (Or.inl rfl))
  · rw [mcell2, if_pos hcond]
    simp only
    exact Set.mem_inter
      (Set.mem_inter (p24_mem_rconeGe_cross ha1) (p24_mem_rconeGe_apex ha1))
      (p24_mem_affGe_base hfin u1 (Or.inr rfl))

/-! ### 新件 1：affGe 四点组合成员 -/

private theorem p24_mem_affGe_quad {a b c d y : V3} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (w1 w2 w3 w4 : ℝ)
    (hsum : w1 + w2 + w3 + w4 = 1) (hw3 : 0 ≤ w3) (hw4 : 0 ≤ w4)
    (hy : y = w1 • a + w2 • b + w3 • c + w4 • d) :
    y ∈ affGe {a, b} {c, d} := by
  have hfin : (({a, b} : Set V3) ∪ {c, d}).Finite :=
    ((Set.finite_singleton b).insert a).union ((Set.finite_singleton d).insert c)
  have h4 : hfin.toFinset = ({a, b} : Finset V3) ∪ ({c, d} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert,
      Finset.mem_singleton]
  have hdisj : Disjoint ({a, b} : Finset V3) ({c, d} : Finset V3) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx, hy]; exact hac
    · rw [hx, hy]; exact had
    · rw [hx, hy]; exact hbc
    · rw [hx, hy]; exact hbd
  have hins1 : (a : V3) ∉ ({b} : Finset V3) := by simp [hab]
  have hins2 : (c : V3) ∉ ({d} : Finset V3) := by simp [hcd]
  have h2sum : ∑ x ∈ ({a, b} : Finset V3),
      (fun z : V3 => if z = a then w1 else if z = b then w2
        else if z = c then w3 else w4) x = w1 + w2 := by
    rw [Finset.sum_insert hins1, Finset.sum_singleton]
    show (if a = a then w1 else if a = b then w2 else if a = c then w3 else w4)
      + (if b = a then w1 else if b = b then w2 else if b = c then w3 else w4) = w1 + w2
    rw [if_pos (rfl : a = a), if_neg (Ne.symm hab), if_pos (rfl : b = b)]
  have hcdsum : ∑ x ∈ ({c, d} : Finset V3),
      (fun z : V3 => if z = a then w1 else if z = b then w2
        else if z = c then w3 else w4) x = w3 + w4 := by
    rw [Finset.sum_insert hins2, Finset.sum_singleton]
    show (if c = a then w1 else if c = b then w2 else if c = c then w3 else w4)
      + (if d = a then w1 else if d = b then w2 else if d = c then w3 else w4) = w3 + w4
    rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), if_pos (rfl : c = c),
      if_neg (Ne.symm had), if_neg (Ne.symm hbd), if_neg (Ne.symm hcd)]
  have h2vsum : ∑ x ∈ ({a, b} : Finset V3),
      (fun z : V3 => if z = a then w1 else if z = b then w2
        else if z = c then w3 else w4) x • x = w1 • a + w2 • b := by
    rw [Finset.sum_insert hins1, Finset.sum_singleton]
    show (if a = a then w1 else if a = b then w2 else if a = c then w3 else w4) • a
      + (if b = a then w1 else if b = b then w2 else if b = c then w3 else w4) • b
        = w1 • a + w2 • b
    rw [if_pos (rfl : a = a), if_neg (Ne.symm hab), if_pos (rfl : b = b)]
  have hcdvsum : ∑ x ∈ ({c, d} : Finset V3),
      (fun z : V3 => if z = a then w1 else if z = b then w2
        else if z = c then w3 else w4) x • x = w3 • c + w4 • d := by
    rw [Finset.sum_insert hins2, Finset.sum_singleton]
    show (if c = a then w1 else if c = b then w2 else if c = c then w3 else w4) • c
      + (if d = a then w1 else if d = b then w2 else if d = c then w3 else w4) • d
        = w3 • c + w4 • d
    rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), if_pos (rfl : c = c),
      if_neg (Ne.symm had), if_neg (Ne.symm hbd), if_neg (Ne.symm hcd)]
  refine ⟨fun z => if z = a then w1 else if z = b then w2 else if z = c then w3 else w4,
    hfin, ?_, ?_, ?_⟩
  · rw [h4, Finset.sum_union hdisj, h2vsum, hcdvsum, hy]
    module
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with hzc | hzd
    · rw [hzc]
      simp only
      rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), if_pos trivial]
      exact hw3
    · rw [hzd]
      simp only
      rw [if_neg (Ne.symm had), if_neg (Ne.symm hbd), if_neg (Ne.symm hcd)]
      exact hw4
  · rw [h4, Finset.sum_union hdisj, h2sum, hcdsum]
    linarith

/-! ### 新件 2：affGe 凸性 -/

private theorem p24_affGe_convex (s t : Set V3) (hfin : (s ∪ t).Finite) :
    Convex ℝ (affGe s t) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b hα hβ hab
  have hx' : Affsign (fun x : ℝ => 0 ≤ x) s t x := hx
  have hy' : Affsign (fun x : ℝ => 0 ≤ x) s t y := hy
  obtain ⟨f1, hf1, hs1, hp1, ho1⟩ := hx'
  obtain ⟨f2, hf2, hs2, hp2, ho2⟩ := hy'
  have e1 : a • x = ∑ w ∈ hf1.toFinset, (a * f1 w) • w := by
    rw [hs1, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun w _ => by module)
  have e2 : b • y = ∑ w ∈ hf2.toFinset, (b * f2 w) • w := by
    rw [hs2, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun w _ => by module)
  have heq : hf1.toFinset = hf2.toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset]
  refine ⟨fun z => a * f1 z + b * f2 z, hfin, ?_, ?_, ?_⟩
  · rw [e1, e2, heq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => (add_smul _ _ _).symm)
  · intro z hz
    exact add_nonneg (mul_nonneg hα (hp1 z hz)) (mul_nonneg hβ (hp2 z hz))
  · rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ho1, ho2]
    linarith

/-! ### 新件 3：近轴 ε 点的双 rcone 成员（e3 标架形） -/

private theorem p24_rconeGe_eps_mem (u0 u1 mid ζ e3 : V3) (d a : ℝ)
    (hax : (u1 - u0 : V3) = d • e3) (h33 : e3 ⬝ᵥ e3 = 1)
    (hmid : (mid : V3) = u0 + (d / 2) • e3)
    (hd : 0 < d) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hζ : (ζ : V3) ⬝ᵥ e3 = 0) (hζ0 : (ζ : V3) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ (mid + ε • ζ : V3) ∈ rconeGe u0 u1 a ∧
      (mid + ε • ζ : V3) ∈ rconeGe u1 u0 a := by
  have hζ' : e3 ⬝ᵥ (ζ : V3) = 0 := by rw [dotProduct_comm]; exact hζ
  have hζsq : ‖(ζ : V3)‖ ^ 2 = ((ζ : V3) ⬝ᵥ (ζ : V3)) := norm_sq_eq_dot (ζ : V3)
  have hζnpos : 0 < ‖(ζ : V3)‖ := norm_pos_iff.mpr hζ0
  have hzn : ‖(ζ : V3)‖ ≠ 0 := ne_of_gt hζnpos
  have he3n : ‖e3‖ = 1 := by
    have h4 : ‖e3‖ ^ 2 = (1:ℝ) ^ 2 := by rw [norm_sq_eq_dot e3, h33]; norm_num
    exact (sq_eq_sq₀ (norm_nonneg e3) (by norm_num)).mp h4
  have hmd : ‖(u1 - u0 : V3)‖ = d := by
    have h1 : ‖(u1 - u0 : V3)‖ = ‖(d : ℝ) • e3‖ := by rw [hax]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hd), he3n]
    ring
  set ε : ℝ := d * Real.sqrt (1 - a ^ 2) / (4 * (a + 1 / 2) * ‖(ζ : V3)‖) with hεdef
  have hpos1 : 0 < 1 - a ^ 2 := by nlinarith [ha1]
  have hεpos : 0 < ε := by
    rw [hεdef]
    refine div_pos (mul_pos hd (Real.sqrt_pos.mpr hpos1)) ?_
    have hap : (0:ℝ) < a + 1 / 2 := by linarith
    exact mul_pos (mul_pos (by norm_num) hap) hζnpos
  have hεsq : ε ^ 2 * ‖(ζ : V3)‖ ^ 2 = d ^ 2 * (1 - a ^ 2) / (16 * (a + 1 / 2) ^ 2) := by
    rw [hεdef]
    field_simp [hzn]
    rw [Real.sq_sqrt (le_of_lt hpos1)]
    ring
  have hnsq1 : ‖(((d / 2) • e3 + ε • ζ : V3))‖ ^ 2 = d ^ 2 / 4 + ε ^ 2 * ‖(ζ : V3)‖ ^ 2 := by
    rw [norm_sq_eq_dot (x := (((d / 2) • e3 + ε • ζ : V3))), hζsq]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hζ, hζ', h33]
    ring
  have hnsq2 : ‖((-(d / 2)) • e3 + ε • ζ : V3)‖ ^ 2 = d ^ 2 / 4 + ε ^ 2 * ‖(ζ : V3)‖ ^ 2 := by
    rw [norm_sq_eq_dot (x := (((-(d / 2)) • e3 + ε • ζ : V3))), hζsq]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hζ, hζ', h33]
    ring
  have hbound : ∀ X : V3, ‖X‖ ^ 2 = d ^ 2 / 4 + ε ^ 2 * ‖(ζ : V3)‖ ^ 2 →
      a * ‖X‖ ≤ d / 2 := by
    intro X hX
    have hnn : 0 ≤ ‖X‖ := norm_nonneg _
    have h2 : a ^ 2 ≤ 4 * (a + 1 / 2) ^ 2 := by nlinarith [ha0, sq_nonneg a]
    have hnon : 0 ≤ d ^ 2 * (1 - a ^ 2) / (16 * (a + 1 / 2) ^ 2) :=
      div_nonneg (mul_nonneg (sq_nonneg d) hpos1.le) (by positivity)
    have hx : a ^ 2 * (d ^ 2 * (1 - a ^ 2) / (16 * (a + 1 / 2) ^ 2))
        ≤ (4 * (a + 1 / 2) ^ 2) * (d ^ 2 * (1 - a ^ 2) / (16 * (a + 1 / 2) ^ 2)) :=
      mul_le_mul_of_nonneg_right h2 hnon
    have hreform : (4 * (a + 1 / 2) ^ 2) * (d ^ 2 * (1 - a ^ 2) / (16 * (a + 1 / 2) ^ 2))
        = d ^ 2 * (1 - a ^ 2) / 4 := by
      field_simp
      ring
    have hfinal : a ^ 2 * (d ^ 2 / 4) + a ^ 2 * (d ^ 2 * (1 - a ^ 2)
        / (16 * (a + 1 / 2) ^ 2)) ≤ d ^ 2 / 4 := by
      have h3 : a ^ 2 * (d ^ 2 / 4) + (4 * (a + 1 / 2) ^ 2)
          * (d ^ 2 * (1 - a ^ 2) / (16 * (a + 1 / 2) ^ 2)) = d ^ 2 / 4 := by
        field_simp
        ring
      linarith [hx, hreform, h3]
    have hsq : (a * ‖X‖) ^ 2 ≤ (d / 2) ^ 2 := by
      have h4 : (a * ‖X‖) ^ 2 = a ^ 2 * (d ^ 2 / 4)
          + a ^ 2 * (d ^ 2 * (1 - a ^ 2) / (16 * (a + 1 / 2) ^ 2)) := by
        rw [mul_pow, hX, hεsq]
        ring
      have h5 : (d / 2) ^ 2 = d ^ 2 / 4 := by ring
      rw [h4, h5]
      exact hfinal
    have hres := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (mul_nonneg ha0 hnn), Real.sqrt_sq (by linarith)] at hres
    exact hres
  have hbd1 := hbound _ hnsq1
  have hbd2 := hbound _ hnsq2
  refine ⟨ε, hεpos, ?_, ?_⟩
  · have hsplit : ((mid + ε • ζ : V3) - u0) = ((d / 2) • e3 + ε • ζ) := by
      rw [hmid]; module
    have hdot : ((mid + ε • ζ : V3) - u0) ⬝ᵥ (u1 - u0 : V3) = d ^ 2 / 2 := by
      rw [hsplit, hax]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hζ, h33]
      ring
    have hdist : dist (mid + ε • ζ) u0 = ‖(((d / 2) • e3 + ε • ζ : V3))‖ := by
      rw [dist_eq_norm, hsplit]
    have hdc : dist u1 u0 = d := by rw [dist_eq_norm u1 u0, hmd]
    have hfin1 : ((mid + ε • ζ : V3) - u0) ⬝ᵥ (u1 - u0 : V3)
        ≥ dist (mid + ε • ζ) u0 * dist u1 u0 * a := by
      rw [hdot, hdist, hdc]
      calc d ^ 2 / 2 = (d / 2) * d := by ring
        _ ≥ (a * ‖(((d / 2) • e3 + ε • ζ : V3))‖) * d :=
            mul_le_mul_of_nonneg_right hbd1 (le_of_lt hd)
        _ = ‖(((d / 2) • e3 + ε • ζ : V3))‖ * d * a := by ring
    exact hfin1
  · have hu1 : (u1 : V3) = u0 + d • e3 := by
      have h1 : (u1 : V3) = u0 + (u1 - u0 : V3) := by module
      rw [h1, hax]
    have hsplit : ((mid + ε • ζ : V3) - u1) = ((-(d / 2)) • e3 + ε • ζ) := by
      rw [hmid, hu1]; module
    have hζneg : (ζ : V3) ⬝ᵥ (u0 - u1 : V3) = 0 := by
      have h2 : ((u0 - u1 : V3)) = -(d • e3) := by rw [← hax]; module
      rw [h2, WithLp.ofLp_neg, WithLp.ofLp_smul, dotProduct_neg, dotProduct_smul,
        smul_eq_mul, hζ]
      ring
    have he3neg : e3 ⬝ᵥ (u0 - u1 : V3) = -d := by
      have h2 : ((u0 - u1 : V3)) = -(d • e3) := by rw [← hax]; module
      rw [h2, WithLp.ofLp_neg, WithLp.ofLp_smul, dotProduct_neg, dotProduct_smul,
        smul_eq_mul, h33]
      ring
    have hdot : ((mid + ε • ζ : V3) - u1) ⬝ᵥ (u0 - u1 : V3) = d ^ 2 / 2 := by
      rw [hsplit]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hζneg,
        he3neg, h33]
      ring
    have hdist : dist (mid + ε • ζ) u1 = ‖((-(d / 2)) • e3 + ε • ζ : V3)‖ := by
      rw [dist_eq_norm, hsplit]
    have hfin2 : ((mid + ε • ζ : V3) - u1) ⬝ᵥ (u0 - u1 : V3)
        ≥ dist (mid + ε • ζ) u1 * dist u0 u1 * a := by
      have h2 : (d / 2) * d = d ^ 2 / 2 := by ring
      have h3 : ‖((-(d / 2)) • e3 + ε • ζ : V3)‖ * d * a
          = (a * ‖((-(d / 2)) • e3 + ε • ζ : V3)‖) * d := by ring
      have hdc : dist u0 u1 = d := by
        have hn : ((u0 - u1 : V3)) = -((u1 - u0 : V3)) := by module
        rw [dist_eq_norm u0 u1, hn, norm_neg, hmd]
      rw [hdot, hdist, hdc, h3]
      exact le_trans (mul_le_mul_of_nonneg_right hbd2 (le_of_lt hd)) h2.le
    exact hfin2

/-! ### 新件 4：近轴点离轴（非共线） -/

private theorem p24_offaxis_of_orth (u0 u1 mid x ζ e3 : V3) (d ε : ℝ)
    (hne : u0 ≠ u1) (hax : (u1 - u0 : V3) = d • e3) (h33 : e3 ⬝ᵥ e3 = 1)
    (hmid : (mid : V3) = u0 + (d / 2) • e3)
    (hx : (x : V3) = mid + ε • ζ) (hε : ε ≠ 0)
    (hζ : (ζ : V3) ⬝ᵥ e3 = 0) (hζ0 : (ζ : V3) ≠ 0) :
    ¬ Collinear3 u0 u1 x := by
  intro hcol
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (Ne.symm hne)).mp hcol
  have hd0 : (d : ℝ) ≠ 0 := by
    intro hcon
    rw [hcon] at hax
    simp only [zero_smul] at hax
    exact hne (sub_eq_zero.mp hax).symm
  have hsplit : ((x - u0 : V3)) = (ε • ζ + (d / 2) • e3) := by
    rw [hx, hmid]; module
  have hcd : ((x - u0 : V3)) ⬝ᵥ e3 = d / 2 := by
    rw [hsplit]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hζ, h33]
    ring
  have hcval : ((x - u0 : V3)) ⬝ᵥ e3 = c * d := by
    rw [hc, hax]
    simp only [WithLp.ofLp_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, h33]
    ring
  have hchalf : c = 1 / 2 := by
    have h2 : c * d = (1 / 2) * d := by rw [← hcval, hcd]; ring
    exact mul_right_cancel₀ hd0 h2
  have hxeq : ((x - u0 : V3)) = ((d / 2) • e3) := by
    rw [hc, hchalf, hax]; module
  have hsplit2 : (ε • ζ + (d / 2) • e3 : V3) = ((d / 2) • e3) := hsplit.symm.trans hxeq
  have hzero : (ε • ζ : V3) = 0 := by
    have h1 : ((ε • ζ + (d / 2) • e3 : V3) - ((d / 2) • e3)) = 0 := by
      rw [hsplit2]; simp
    have h2 : ((ε • ζ + (d / 2) • e3 : V3) - ((d / 2) • e3)) = (ε • ζ) := by module
    rw [h2] at h1
    exact h1
  exact hζ0 ((smul_eq_zero.mp hzero).resolve_left hε)

/-! ### 新件 5：γ·h > 0（wg·h 非零的算术核） -/

private theorem p24_caseB2_gamma_pos (t h wg d : ℝ) (hh : 0 < h)
    (hgam : 2 * wg * h = h ^ 2 + t ^ 2 - d * t)
    (hu0 : (4 : ℝ) ≤ t ^ 2 + h ^ 2) (hu1 : (4 : ℝ) ≤ (t - d) ^ 2 + h ^ 2)
    (hd8 : d ^ 2 < 8) :
    0 < wg * h := by
  have hexp : (t - d) ^ 2 = t ^ 2 - 2 * t * d + d ^ 2 := by ring
  have h1 : 2 * (wg * h) = h ^ 2 + t ^ 2 - d * t := by linarith [hgam]
  have h2 : (t ^ 2 + h ^ 2) + ((t - d) ^ 2 + h ^ 2) ≥ 8 := by linarith
  have hkey : 4 * (wg * h) ≥ 8 - d ^ 2 := by
    nlinarith [h1, h2, hexp, sq_nonneg d]
  nlinarith

/-! ### 新件 6：双楔点方位角相异 ⟹ 不能同时为零 -/

private theorem p24_caseB2_azim_kill (u0 u1 q mid z1 z2 : V3) (e3 : V3) (d ε1 ε2 : ℝ)
    (hne : u0 ≠ u1) (hax : (u1 - u0 : V3) = d • e3) (h33 : e3 ⬝ᵥ e3 = 1)
    (hmid : (mid : V3) = u0 + (d / 2) • e3) (hd : 0 < d)
    (hq : ¬ Collinear3 u0 u1 q)
    (hy1 : ¬ Collinear3 u0 u1 z1) (hy2 : ¬ Collinear3 u0 u1 z2)
    (ha1 : azim u0 u1 q z1 = 0) (ha2 : azim u0 u1 q z2 = 0)
    (hε1 : 0 < ε1) (hε2 : 0 < ε2)
    (hζ1 : (z1 - mid : V3) ⬝ᵥ e3 = 0) (hζ2 : (z2 - mid : V3) ⬝ᵥ e3 = 0)
    (hindep : ∀ r : ℝ, (z2 - mid : V3) ≠ r • (z1 - mid : V3)) :
    False := by
  have hzsub : ∀ w : V3, w = u0 → Collinear3 u0 u1 w := fun w hw =>
    (collinear3_iff_smul (Ne.symm hne)).mpr ⟨0, by rw [hw, zero_smul, sub_self]⟩
  have hq0 : (q : V3) ≠ u0 := fun hcon => hq (hzsub q hcon)
  have hq1 : (q : V3) ≠ u1 := by
    intro hcon
    exact hq ((collinear3_iff_smul (Ne.symm hne)).mpr ⟨1, by rw [hcon, one_smul]⟩)
  have hmidcol : Collinear3 u0 u1 mid := by
    refine (collinear3_iff_smul (Ne.symm hne)).mpr ⟨(1 / 2 : ℝ), ?_⟩
    rw [hmid, hax]; module
  have hz10 : (z1 : V3) ≠ u0 := fun hcon => hy1 (hzsub z1 hcon)
  have hz11 : (z1 : V3) ≠ u1 := by
    intro hcon
    exact hy1 ((collinear3_iff_smul (Ne.symm hne)).mpr ⟨1, by rw [hcon, one_smul]⟩)
  have hz20 : (z2 : V3) ≠ u0 := fun hcon => hy2 (hzsub z2 hcon)
  have hz21 : (z2 : V3) ≠ u1 := by
    intro hcon
    exact hy2 ((collinear3_iff_smul (Ne.symm hne)).mpr ⟨1, by rw [hcon, one_smul]⟩)
  have hmem1 : (z1 : V3) ∈ affGt {u0, u1} {q} := (azim_eq_zero_iff_alt hq hy1).mp ha1
  have hmem2 : (z2 : V3) ∈ affGt {u0, u1} {q} := (azim_eq_zero_iff_alt hq hy2).mp ha2
  obtain ⟨c1, hc1, g1, hg1⟩ := (affGt_pair_iff hne hq0 hq1).mp hmem1
  obtain ⟨c2, hc2, g2, hg2⟩ := (affGt_pair_iff hne hq0 hq1).mp hmem2
  have hkey : (c2 • ((z1 : V3) - u0) - c1 • ((z2 : V3) - u0) : V3)
      = ((c2 * g1 - c1 * g2) • (u1 - u0 : V3)) := by
    rw [hg1, hg2]; module
  have hsplit : (c2 • ((z1 : V3) - u0) - c1 • ((z2 : V3) - u0) : V3)
      = (c2 • ((z1 : V3) - mid) - c1 • ((z2 : V3) - mid))
        + (((c2 - c1) * (d / 2)) • e3) := by
    rw [hmid]; module
  rw [hax, smul_smul] at hkey
  have h8 : ((c2 • ((z1 : V3) - mid) - c1 • ((z2 : V3) - mid) : V3))
      + (((c2 - c1) * (d / 2)) • e3) = ((c2 * g1 - c1 * g2) * d) • e3 := by
    rw [← hkey]; rw [hsplit]
  have hcomb : (c2 • ((z1 : V3) - mid) - c1 • ((z2 : V3) - mid) : V3)
      = (((c2 * g1 - c1 * g2) * d - (c2 - c1) * (d / 2)) • e3) := by
    have h9 : (((c2 * g1 - c1 * g2) * d - (c2 - c1) * (d / 2)) • e3 : V3)
        = ((c2 * g1 - c1 * g2) * d) • e3 - ((c2 - c1) * (d / 2)) • e3 := sub_smul _ _ _
    rw [h9]
    exact eq_sub_of_add_eq h8
  have hdot0 : (((c2 * g1 - c1 * g2) * d - (c2 - c1) * (d / 2)) • e3 : V3) ⬝ᵥ e3 = 0 := by
    have h1 : ((c2 • ((z1 : V3) - mid) : V3)) ⬝ᵥ e3 = c2 * (((z1 : V3) - mid) ⬝ᵥ e3) := by
      rw [WithLp.ofLp_smul, smul_dotProduct]
      rfl
    have h2' : ((c1 • ((z2 : V3) - mid) : V3)) ⬝ᵥ e3 = c1 * (((z2 : V3) - mid) ⬝ᵥ e3) := by
      rw [WithLp.ofLp_smul, smul_dotProduct]
      rfl
    have hB : ((c2 • ((z1 : V3) - mid) - c1 • ((z2 : V3) - mid) : V3)) ⬝ᵥ e3 = 0 := by
      rw [WithLp.ofLp_sub, sub_dotProduct, h1, h2', hζ1, hζ2]
      ring
    rw [← hcomb]
    exact hB
  have hk : ((c2 * g1 - c1 * g2) * d - (c2 - c1) * (d / 2) : ℝ) = 0 := by
    have h2 : (((c2 * g1 - c1 * g2) * d - (c2 - c1) * (d / 2)) • e3 : V3) ⬝ᵥ e3
        = ((c2 * g1 - c1 * g2) * d - (c2 - c1) * (d / 2)) := by
      rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, h33, mul_one]
    rw [← h2, hdot0]
  have hzero : (c2 • ((z1 : V3) - mid) - c1 • ((z2 : V3) - mid) : V3) = 0 := by
    rw [hcomb, hk, zero_smul]
  rw [sub_eq_zero] at hzero
  rcases eq_or_ne (c1 : ℝ) 0 with hc1z | hc1nz
  · rw [hc1z, zero_smul] at hzero
    have hζ1z : ((z1 : V3) - mid) = 0 := by
      rcases smul_eq_zero.mp hzero with h | h
      · exact absurd h hc2.ne'
      · exact h
    have hz1m : (z1 : V3) = mid := sub_eq_zero.mp hζ1z
    apply hy1
    rw [hz1m]
    exact hmidcol
  · have h7 : ((ε2 * c1 : ℝ)) • ((z2 : V3) - mid) = ((ε2 * c2 : ℝ)) • ((z1 : V3) - mid) := by
      rw [mul_smul, mul_smul, ← hzero]
    have hnez : (ε2 * c1 : ℝ) ≠ 0 := mul_ne_zero (ne_of_gt hε2) hc1nz
    have h8' : ((z2 : V3) - mid) = ((ε2 * c1 : ℝ)⁻¹ * (ε2 * c2)) • ((z1 : V3) - mid) := by
      rw [mul_smul, eq_inv_smul_iff₀ hnez]
      exact h7
    exact hindep ((ε2 * c1 : ℝ)⁻¹ * (ε2 * c2)) h8'


/-! ### 主装配：B2 泛具支 -/

private theorem p24_caseB2_general (V : Set V3) (u0 u1 : V3) (vl : List V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1])
    (hd8 : dist u0 u1 < Real.sqrt 8)
    (hr4 : Real.sqrt 2 ≤ hl vl)
    (hr3 : Real.sqrt 2 ≤ hl (truncateSimplex 2 vl))
    (hw23 : omegaListN V vl 2 ≠ omegaListN V vl 3) :
    ∃ X : Set V3, X ∈ mcellSet V ∧ ({u0, u1} : Set V3) ∈ edgeX V X ∧
      ∀ q : V3, ¬ Collinear3 u0 u1 q →
        ¬ ((X : Set V3) ⊆ {z : V3 | azim u0 u1 q z = 0}) := by
  -- 0. 四元组显式化 + u0/u1 识别
  obtain ⟨q0, q1, q2, q3, hvll⟩ := BARV_3_EXPLICIT V vl hbar
  subst hvll
  have htrq : truncateSimplex 1 [q0, q1, q2, q3] = [q0, q1] := by
    rw [truncateSimplex1_pair [q0, q1, q2, q3] (by norm_num)]
    simp [elV]
  have hpair01 : [u0, u1] = [q0, q1] := htr.symm.trans htrq
  injection hpair01 with e0 e1l
  injection e1l with e1 e1nil
  subst e0
  subst e1
  obtain ⟨v, hvdef⟩ : ∃ v : V3, v = q2 := ⟨q2, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : V3, w = q3 := ⟨q3, rfl⟩
  rw [← hvdef, ← hwdef] at hbar hr4 hr3 hw23
  have h82 : (Real.sqrt 8 : ℝ) / 2 = Real.sqrt 2 := by
    have h8 : (Real.sqrt 8 : ℝ) = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 4 * 2 from by norm_num, Real.sqrt_mul (by norm_num)]
      norm_num
    rw [h8]
    field_simp
  -- 1. 截断与 barV 数据
  have htr1 : truncateSimplex 1 [u0, u1, v, w] = [u0, u1] := by
    rw [truncateSimplex1_pair [u0, u1, v, w] (by norm_num)]
    simp [elV]
  have htr2 : truncateSimplex 2 [u0, u1, v, w] = [u0, u1, v] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 v w).2
  have htr3 : truncateSimplex 3 [u0, u1, v, w] = [u0, u1, v, w] :=
    TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 v w
  have hbar2 : barV V 2 [u0, u1, v] := by
    have hb := TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, v, w] hbar (by norm_num)
    rwa [htr2] at hb
  have htr1' : setOfList (truncateSimplex 1 [u0, u1, v]) = ({u0, u1} : Set V3) := by
    rw [truncateSimplex1_pair [u0, u1, v] (by have := hbar2.1; omega)]
    ext x
    simp [setOfList, elV]
  obtain ⟨-, -, hnc⟩ := p24_REUHADY_extract (v := v) hp hbar2 htr1' rfl
  -- v, w ∈ V；v 离两端
  have hvn4 : voronoiNondg V [u0, u1, v, w] :=
    hbar.2 [u0, u1, v, w] ⟨⟨[], by rw [List.append_nil]⟩, by simp⟩
  have hsubV : setOfList [u0, u1, v, w] ⊆ V := hvn4.2.1
  have hvV : v ∈ V := hsubV (by rw [hvdef]; simp [setOfList])
  have hv0ne : u0 ≠ v := by
    intro hcon
    rw [← hcon] at hnc
    exact hnc ((collinear3_iff_smul (Ne.symm hne)).mpr
      ⟨0, by rw [zero_smul, sub_self]⟩)
  have hv1ne : u1 ≠ v := by
    intro hcon
    rw [← hcon] at hnc
    exact hnc ((collinear3_iff_smul (Ne.symm hne)).mpr
      ⟨1, by rw [one_smul]⟩)
  -- 2. 标架
  have hdgt : 2 ≤ dist u0 u1 := hp.dist_ge_two hu0 hu1 hne
  have hdne : (dist u0 u1 : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hdgt)
  have hu0u1n : (u1 - u0 : V3) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨e1, e2, e3, hon, hax0⟩ := exists_on3_eq_smul (u1 - u0) hu0u1n
  have haxd : (u1 - u0 : V3) = dist u0 u1 • e3 := by
    have hn : ‖u1 - u0‖ = dist u0 u1 := (dist_eq_norm u1 u0).symm.trans (dist_comm u1 u0)
    rw [hn] at hax0
    exact hax0
  have h33 : e3 ⬝ᵥ e3 = 1 := hon.2.2.1
  have hmd : ‖(u1 - u0 : V3)‖ = dist u0 u1 :=
    (dist_eq_norm u1 u0).symm.trans (dist_comm u1 u0)
  have hmnn : ((u1 - u0 : V3)) ⬝ᵥ (u1 - u0) = dist u0 u1 ^ 2 := by
    have h1 : ((u1 - u0 : V3)) ⬝ᵥ (u1 - u0) = ‖(u1 - u0 : V3)‖ ^ 2 :=
      (norm_sq_eq_dot _).symm
    rw [h1, hmd]
  have he3n : ‖e3‖ = 1 := by
    have h4 : ‖e3‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [norm_sq_eq_dot e3, h33]; norm_num
    exact (sq_eq_sq₀ (norm_nonneg e3) (by norm_num)).mp h4
  set mid : V3 := u0 + (dist u0 u1 / 2) • e3 with hmiddef
  -- 3. tri-数据与垂分量 P
  obtain ⟨h, t, wg, hhpos, hteq, hPn0, hrad, hgam, hnn⟩ :=
    p24_tri_gamma u0 u1 v hon haxd hne hnc (p24_cc_exists u0 u1 v hne hnc)
  obtain ⟨P, hv', hPe3, hPn⟩ : ∃ P : V3, (v - u0 : V3) = t • e3 + P ∧ P ⬝ᵥ e3 = 0 ∧ ‖P‖ = h := by
    refine ⟨(v - u0 : V3) - t • e3, ?_, ?_, ?_⟩
    · have e0 : (((v - u0 : V3) - t • e3 : V3) + t • e3) = (v - u0 : V3) := by module
      rw [add_comm, e0]
    · have hsmul : ((t • e3 : V3) ⬝ᵥ e3) = t * (e3 ⬝ᵥ e3) := by
        rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]
      have hsub' : (((v - u0 : V3) - t • e3 : V3) ⬝ᵥ e3)
          = ((v - u0 : V3) ⬝ᵥ e3) - ((t • e3 : V3) ⬝ᵥ e3) := by
        rw [WithLp.ofLp_sub, sub_dotProduct]
      rw [hsub', hsmul, hteq, h33]
      ring
    · have he : ((v - u0 : V3) - t • e3 : V3)
        = (v - u0) - ((v - u0) ⬝ᵥ e3) • e3 := by rw [hteq]
      rw [he]
      exact hPn0
  -- 4a. 距离平方
  have hdu0v : 2 ≤ dist u0 v := hp.dist_ge_two hu0 hvV hv0ne
  have hdu1v : 2 ≤ dist u1 v := hp.dist_ge_two hu1 hvV hv1ne
  have hdu1v' : dist u1 v = ‖((v - u1 : V3))‖ := by
    have hn : ((u1 - v : V3)) = -((v - u1 : V3)) := by module
    rw [dist_eq_norm u1 v, hn, norm_neg]
  have hvsq0 : ‖(v - u0 : V3)‖ ^ 2 = t ^ 2 + h ^ 2 := by
    have horth : ((t • e3 : V3)) ⬝ᵥ P = 0 := by
      rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, show e3 ⬝ᵥ P = 0 from by rw [dotProduct_comm]; exact hPe3]
      ring
    rw [hv', p24_norm_sq_of_orth horth]
    have e1 : ‖((t • e3 : V3))‖ ^ 2 = t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he3n, one_pow, mul_one]
    have e2 : ‖((P : V3))‖ ^ 2 = h ^ 2 := by rw [hPn]
    rw [e1, e2]
  have hvsq1 : ‖((v - u1 : V3))‖ ^ 2 = (t - dist u0 u1) ^ 2 + h ^ 2 := by
    have hv1' : ((v - u1 : V3)) = ((t - dist u0 u1) • e3 + P) := by
      have h1 : ((v - u1 : V3)) = ((v - u0 : V3)) - ((u1 - u0 : V3)) := by module
      rw [h1, hv', haxd]; module
    have horth : (((t - dist u0 u1) • e3 : V3)) ⬝ᵥ P = 0 := by
      rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, show e3 ⬝ᵥ P = 0 from by rw [dotProduct_comm]; exact hPe3]
      ring
    rw [hv1', p24_norm_sq_of_orth horth]
    have e1 : ‖(((t - dist u0 u1) • e3 : V3))‖ ^ 2 = (t - dist u0 u1) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he3n, one_pow, mul_one]
    have e2 : ‖((P : V3))‖ ^ 2 = h ^ 2 := by rw [hPn]
    rw [e1, e2]
  -- 4. wg·h > 0（线性独立核）
  have hwgpos : 0 < wg * h :=
    p24_caseB2_gamma_pos t h wg (dist u0 u1) hhpos hgam
      (by
        have hb : (dist u0 v : ℝ) = ‖((v - u0 : V3))‖ := by
          have hn : ((u0 - v : V3)) = -((v - u0 : V3)) := by module
          rw [dist_eq_norm u0 v, hn, norm_neg]
        have h4 : (2 : ℝ) ^ 2 ≤ (dist u0 v) ^ 2 := by
          nlinarith [hdu0v, sq_nonneg (dist u0 v)]
        norm_num at h4
        rw [hb, hvsq0] at h4
        exact h4)
      (by
        have hb : (dist u1 v : ℝ) = ‖((v - u1 : V3))‖ := by rw [hdu1v']
        have h4 : (2 : ℝ) ^ 2 ≤ (dist u1 v) ^ 2 := by
          nlinarith [hdu1v, sq_nonneg (dist u1 v)]
        norm_num at h4
        rw [hb, hvsq1] at h4
        exact h4)
      (by
        nlinarith [hd8, show (Real.sqrt 8 : ℝ) ^ 2 = 8 from Real.sq_sqrt (le_of_lt (by norm_num))])
  -- 5. omega2、omega3 的 Voronoi 成员与等距
  have hw2mem := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, v, w] 3 2 hbar (by norm_num)
  rw [htr2] at hw2mem
  have hw2cell : ∀ z ∈ ({u0, u1, v} : Set V3), ∀ y ∈ V,
      dist (omegaListN V [u0, u1, v, w] 2) z
        ≤ dist (omegaListN V [u0, u1, v, w] 2) y := by
    intro z hz y hy
    have h0 : (omegaListN V [u0, u1, v, w] 2 : V3)
        ∈ ⋂₀ {voronoiClosed V p | p ∈ setOfList [u0, u1, v]} := hw2mem
    have hset3 : setOfList [u0, u1, v] = ({u0, u1, v} : Set V3) := by
      ext y; simp [setOfList]
    exact h0 (voronoiClosed V z) ⟨z, by rw [hset3]; exact hz, rfl⟩ y hy
  have heqw2u1 : dist (omegaListN V [u0, u1, v, w] 2) u0
      = dist (omegaListN V [u0, u1, v, w] 2) u1 :=
    le_antisymm (hw2cell u0 (by simp) u1 hu1) (hw2cell u1 (by simp) u0 hu0)
  have heqw2v : dist (omegaListN V [u0, u1, v, w] 2) u0
      = dist (omegaListN V [u0, u1, v, w] 2) v :=
    le_antisymm (hw2cell u0 (by simp) v hvV) (hw2cell v (by simp) u0 hu0)
  -- 6. omega3 = a（四点 Voronoi 单点）与 a 的等距
  obtain ⟨a, ha1, ha2, ha3⟩ := VORONOI_LIST_3_SINGLETON_EXPLICIT V [u0, u1, v, w] hp hs hbar
  have hw3eq : omegaListN V [u0, u1, v, w] 3 = a := by
    have h3 := OMEGA_LIST_IN_VORONOI_LIST (V := V) (ul := [u0, u1, v, w]) (k := 3) hbar
    rw [ha1] at h3
    exact Set.mem_singleton_iff.mp h3
  have hamem : (a : V3) ∈ voronoiList V [u0, u1, v, w] := by rw [ha1]; simp
  have hacell : ∀ z ∈ ({u0, u1, v, w} : Set V3), ∀ y ∈ V, dist a z ≤ dist a y := by
    intro z hz y hy
    have h0 : (a : V3) ∈ ⋂₀ {voronoiClosed V p | p ∈ setOfList [u0, u1, v, w]} := hamem
    exact h0 (voronoiClosed V z) ⟨z, by simp [setOfList]; exact hz, rfl⟩ y hy
  have heqa1 : dist a u0 = dist a u1 :=
    le_antisymm (hacell u0 (by simp) u1 hu1) (hacell u1 (by simp) u0 hu0)
  have heqav : dist a u0 = dist a v :=
    le_antisymm (hacell u0 (by simp) v hvV) (hacell v (by simp) u0 hu0)
  -- 7. 轴方程（axial_eqs 双应用）
  obtain ⟨hE2e3, hE2P⟩ := p24_axial_eqs u0 u1 v mid e3 P (dist u0 u1) t h wg
    (omegaListN V [u0, u1, v, w] 2) haxd hdne h33 hmiddef hv' hPe3 hPn hhpos hgam
    heqw2u1 heqw2v
  obtain ⟨hEae3, hEaP⟩ := p24_axial_eqs u0 u1 v mid e3 P (dist u0 u1) t h wg
    a haxd hdne h33 hmiddef hv' hPe3 hPn hhpos hgam heqa1 heqav
  have hnez : (wg * h : ℝ) ≠ 0 := ne_of_gt hwgpos
  have hz2n : (omegaListN V [u0, u1, v, w] 2 - mid : V3) ≠ 0 := by
    intro hcon
    rw [hcon] at hE2P
    have h4 : ((0 : V3)) ⬝ᵥ P = 0 := by simp
    rw [h4] at hE2P
    linarith
  have hz3n : (a - mid : V3) ≠ 0 := by
    intro hcon
    rw [hcon] at hEaP
    have h4 : ((0 : V3)) ⬝ᵥ P = 0 := by simp
    rw [h4] at hEaP
    linarith
  -- 8. 两 ζ 线性无关（omega2 ≠ omega3 直接读出）
  have hindep : ∀ r : ℝ, (a - mid : V3) ≠ r • (omegaListN V [u0, u1, v, w] 2 - mid : V3) := by
    intro r hr
    apply hw23
    have h1 := hEaP
    rw [hr] at h1
    rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, hE2P] at h1
    have hr1 : r = 1 := by
      have h9 := mul_right_cancel₀ hnez (show (r : ℝ) * (wg * h) = 1 * (wg * h) from by rw [h1]; ring)
      exact h9
    rw [hr1, one_smul] at hr
    have haeq : (a : V3) = omegaListN V [u0, u1, v, w] 2 := by
      have h3 : (((a - mid : V3)) - ((omegaListN V [u0, u1, v, w] 2 - mid : V3))) = 0 := by
        rw [hr]; simp
      have h4 : (((a - mid : V3)) - ((omegaListN V [u0, u1, v, w] 2 - mid : V3)))
          = (a - omegaListN V [u0, u1, v, w] 2 : V3) := by module
      rw [h4] at h3
      exact sub_eq_zero.mp h3
    exact haeq.symm.trans hw3eq.symm
  -- 9. mcell2 显式形 + 两端成员
  have hcond : hl (truncateSimplex 1 [u0, u1, v, w]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, v, w] :=
    ⟨by rw [htr1]; exact p24_hl_pair_lt_sqrt2 hd8, hr4⟩
  have ends := p24_caseB2_ends_mem V u0 u1 v w hcond (by
    rw [htr1, p24_hl_pair u0 u1]
    exact (div_le_one (Real.sqrt_pos.mpr (by norm_num))).mpr (by linarith [hd8, h82]))
  have hr3' : Real.sqrt 2 ≤ hl (truncateSimplex 2 [u0, u1, v, w]) := hr3
  -- 10. ε-点构造（双 rcone）
  have ha0' : 0 ≤ hl (truncateSimplex 1 [u0, u1, v, w]) / Real.sqrt 2 := by
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    apply div_nonneg _ hpos.le
    rw [htr1, p24_hl_pair u0 u1]
    linarith [hdgt]
  have ha1lt : hl (truncateSimplex 1 [u0, u1, v, w]) / Real.sqrt 2 < 1 := by
    rw [htr1, p24_hl_pair u0 u1]
    exact (div_lt_one (Real.sqrt_pos.mpr (by norm_num))).mpr (by linarith [hd8, h82])
  obtain ⟨eps2, heps2, hx2r1, hx2r2⟩ :=
    p24_rconeGe_eps_mem u0 u1 mid (omegaListN V [u0, u1, v, w] 2 - mid) e3
      (dist u0 u1) (hl (truncateSimplex 1 [u0, u1, v, w]) / Real.sqrt 2)
      haxd h33 hmiddef (lt_of_lt_of_le (by norm_num) hdgt) ha0' ha1lt hE2e3 hz2n
  obtain ⟨eps3, heps3, hx3r1, hx3r2⟩ :=
    p24_rconeGe_eps_mem u0 u1 mid (a - mid) e3
      (dist u0 u1) (hl (truncateSimplex 1 [u0, u1, v, w]) / Real.sqrt 2)
      haxd h33 hmiddef (lt_of_lt_of_le (by norm_num) hdgt) ha0' ha1lt hEae3 hz3n
  -- 11. affGe 成员（四点组合）
  have hw2ne0 : (omegaListN V [u0, u1, v, w] 2 : V3) ≠ u0 := by
    intro hcon
    rw [hcon] at heqw2u1
    rw [dist_self] at heqw2u1
    exact hne (dist_eq_zero.mp heqw2u1.symm)
  have hw2ne1 : (omegaListN V [u0, u1, v, w] 2 : V3) ≠ u1 := by
    intro hcon
    rw [hcon] at heqw2u1
    rw [dist_self] at heqw2u1
    exact hne (dist_eq_zero.mp heqw2u1).symm
  have hw3ne0 : (omegaListN V [u0, u1, v, w] 3 : V3) ≠ u0 := by
    intro hcon
    rw [hw3eq] at hcon
    rw [hcon] at heqa1
    rw [dist_self] at heqa1
    exact hne (dist_eq_zero.mp heqa1.symm)
  have hw3ne1 : (omegaListN V [u0, u1, v, w] 3 : V3) ≠ u1 := by
    intro hcon
    rw [hw3eq] at hcon
    rw [hcon] at heqa1
    rw [dist_self] at heqa1
    exact hne (dist_eq_zero.mp heqa1).symm
  have hmid' : (mid : V3) = u0 + (1 / 2 : ℝ) • (u1 - u0 : V3) := by
    rw [hmiddef, haxd]; module
  have hfin' : (({u0, u1} : Set V3) ∪ {omegaListN V [u0, u1, v, w] 2,
      omegaListN V [u0, u1, v, w] 3}).Finite :=
    ((Set.finite_singleton u1).insert u0).union
      ((Set.finite_singleton (omegaListN V [u0, u1, v, w] 3)).insert
        (omegaListN V [u0, u1, v, w] 2))
  have hsum2 : (1 - eps2) / 2 + (1 - eps2) / 2 + eps2 + 0 = 1 := by ring
  have hx2aff : (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3)
      ∈ affGe {u0, u1} {omegaListN V [u0, u1, v, w] 2, omegaListN V [u0, u1, v, w] 3} := by
    refine p24_mem_affGe_quad (hab := hne) (hac := Ne.symm hw2ne0) (had := Ne.symm hw3ne0)
      (hbc := Ne.symm hw2ne1) (hbd := Ne.symm hw3ne1) (hcd := hw23)
      (w1 := (1 - eps2) / 2) (w2 := (1 - eps2) / 2) (w3 := eps2) (w4 := 0)
      (hsum := hsum2) (hw3 := le_of_lt heps2) (hw4 := by norm_num) (hy := ?_)
    have h1 : ((mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3))
        = ((1 - eps2) • mid + eps2 • (omegaListN V [u0, u1, v, w] 2)) := by module
    rw [h1, hmid']
    module
  have hsum3 : (1 - eps3) / 2 + (1 - eps3) / 2 + 0 + eps3 = 1 := by ring
  have hx3aff : (mid + eps3 • (a - mid) : V3)
      ∈ affGe {u0, u1} {omegaListN V [u0, u1, v, w] 2, omegaListN V [u0, u1, v, w] 3} := by
    refine p24_mem_affGe_quad (hab := hne) (hac := Ne.symm hw2ne0) (had := Ne.symm hw3ne0)
      (hbc := Ne.symm hw2ne1) (hbd := Ne.symm hw3ne1) (hcd := hw23)
      (w1 := (1 - eps3) / 2) (w2 := (1 - eps3) / 2) (w3 := 0) (w4 := eps3)
      (hsum := hsum3) (hw3 := le_refl 0) (hw4 := le_of_lt heps3) (hy := ?_)
    have h1 : ((mid + eps3 • (a - mid) : V3))
        = ((1 - eps3) • mid + eps3 • a) := by module
    have h2 : ((1 - eps3 : ℝ)) • (u0 + (1 / 2 : ℝ) • (u1 - u0 : V3))
        = ((1 - eps3) / 2) • u0 + ((1 - eps3) / 2) • u1 := by module
    rw [h1, hmid', hw3eq.symm, h2, zero_smul, add_zero]
  -- 12. X 的四点成员与凸性
  have hXeq : mcell2 V [u0, u1, v, w]
      = ((rconeGe u0 u1 (hl (truncateSimplex 1 [u0, u1, v, w]) / Real.sqrt 2)
          ∩ rconeGe u1 u0 (hl (truncateSimplex 1 [u0, u1, v, w]) / Real.sqrt 2))
        ∩ affGe {u0, u1} {omegaListN V [u0, u1, v, w] 2, omegaListN V [u0, u1, v, w] 3}) := by
    rw [mcell2, if_pos hcond, p24_caseB2_mxi_eq V [u0, u1, v, w] hr3']
    rfl
  have hx2X : (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3)
      ∈ mcell2 V [u0, u1, v, w] := by
    rw [hXeq]
    exact ⟨⟨hx2r1, hx2r2⟩, hx2aff⟩
  have hx3X : (mid + eps3 • (a - mid) : V3)
      ∈ mcell2 V [u0, u1, v, w] := by
    rw [hXeq]
    exact ⟨⟨hx3r1, hx3r2⟩, hx3aff⟩
  have hconv : Convex ℝ (mcell2 V [u0, u1, v, w]) := by
    rw [hXeq]
    refine Convex.inter
      (Convex.inter (p24_rconeGe_convex u0 u1 _ ha0') (p24_rconeGe_convex u1 u0 _ ha0'))
      (p24_affGe_convex _ _ hfin')
  -- 13. x_i − u0 分解 + 三向量线性无关
  have hxs2 : ((mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3)) - u0
      = ((dist u0 u1 / 2) • e3
        + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid : V3)) := by
    rw [hmiddef]; module
  have hxs3 : ((mid + eps3 • (a - mid) : V3)) - u0
      = ((dist u0 u1 / 2) • e3 + eps3 • (a - mid : V3)) := by
    rw [hmiddef]; module
  have hvec3 : ∀ α β γ : ℝ,
      α • (u1 - u0 : V3) + β • ((mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3) - u0)
        + γ • ((mid + eps3 • (a - mid) : V3) - u0) = 0 →
      α = 0 ∧ β = 0 ∧ γ = 0 := by
    intro α β γ hvec
    have hAB : ((α • (u1 - u0 : V3)
        + β • ((mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3) - u0)
        + γ • ((mid + eps3 • (a - mid) : V3) - u0) : V3))
        = (((α * dist u0 u1 + (β + γ) * (dist u0 u1 / 2)) • e3
          + (β * eps2) • (omegaListN V [u0, u1, v, w] 2 - mid)
          + (γ * eps3) • (a - mid) : V3)) := by
      rw [hxs2, hxs3, haxd]
      module
    have hexp : (((α * dist u0 u1 + (β + γ) * (dist u0 u1 / 2)) • e3
        + (β * eps2) • (omegaListN V [u0, u1, v, w] 2 - mid)
        + (γ * eps3) • (a - mid) : V3)) = 0 := by
      rw [← hAB]
      exact hvec
    have hdote : (((α * dist u0 u1 + (β + γ) * (dist u0 u1 / 2)) • e3
        + (β * eps2) • (omegaListN V [u0, u1, v, w] 2 - mid)
        + (γ * eps3) • (a - mid) : V3)) ⬝ᵥ e3 = 0 := by
      rw [← hAB, hvec]
      simp [zero_dotProduct]
    have hsc : (((β * eps2) • (omegaListN V [u0, u1, v, w] 2 - mid)
        + (γ * eps3) • (a - mid) : V3)) ⬝ᵥ e3 = 0 := by
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, hE2e3, hEae3]
      ring
    have hs0 : (α * dist u0 u1 + (β + γ) * (dist u0 u1 / 2) : ℝ) = 0 := by
      have hD : (((α * dist u0 u1 + (β + γ) * (dist u0 u1 / 2)) • e3
          + (β * eps2) • (omegaListN V [u0, u1, v, w] 2 - mid)
          + (γ * eps3) • (a - mid) : V3)) ⬝ᵥ e3
          = (α * dist u0 u1 + (β + γ) * (dist u0 u1 / 2)) * ((e3 : V3) ⬝ᵥ e3) := by
        simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
          dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hE2e3, hEae3, h33]
        ring
      rw [hdote, h33] at hD
      linarith
    have hsc : (((β * eps2) • (omegaListN V [u0, u1, v, w] 2 - mid)
        + (γ * eps3) • (a - mid) : V3)) ⬝ᵥ e3 = 0 := by
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, hE2e3, hEae3]
      ring
    have hres : (((β * eps2) • (omegaListN V [u0, u1, v, w] 2 - mid)
        + (γ * eps3) • (a - mid) : V3)) = 0 := by
      have h7 := hexp
      rw [hs0, zero_smul, zero_add] at h7
      exact h7
    have hβz : (β : ℝ) = 0 ∧ (γ : ℝ) = 0 := by
      rcases eq_or_ne (β * eps2 : ℝ) 0 with hbz | hbn
      · have hb : (β : ℝ) = 0 := by
          rcases mul_eq_zero.mp hbz with h | h
          · exact h
          · exact absurd h (ne_of_gt heps2)
        rw [hb, zero_mul, zero_smul, zero_add] at hres
        rcases smul_eq_zero.mp hres with h | h
        · refine ⟨hb, ?_⟩
          rcases mul_eq_zero.mp h with h1 | h1
          · exact h1
          · exact absurd h1 (ne_of_gt heps3)
        · exact absurd h hz3n
      · have hres' : (((γ * eps3 : ℝ)) • ((a - mid : V3)))
          = -(((β * eps2 : ℝ)) • ((omegaListN V [u0, u1, v, w] 2 - mid : V3))) :=
          eq_neg_of_add_eq_zero_right hres
        rcases eq_or_ne ((γ * eps3 : ℝ)) 0 with hgz | hgn
        · rw [hgz, zero_smul, eq_comm, neg_eq_zero] at hres'
          rcases smul_eq_zero.mp hres' with h | h
          · exact absurd h hbn
          · exact absurd h hz2n
        · have h11 : ((a - mid : V3))
            = -(((γ * eps3 : ℝ)⁻¹ * (β * eps2)) •
              ((omegaListN V [u0, u1, v, w] 2 - mid : V3))) := by
            have h5 := congrArg
              (fun x : V3 => ((γ * eps3 : ℝ)⁻¹) • x) hres'
            simp only [smul_smul, mul_comm (γ * eps3 : ℝ) ((γ * eps3 : ℝ)⁻¹),
              inv_mul_cancel₀ hgn, one_smul, smul_neg, ← mul_smul, neg_smul] at h5
            exact h5
          exact absurd (by
            rw [h11, neg_smul]) (hindep (-(((γ * eps3 : ℝ)⁻¹ * (β * eps2)))))
    have hα : (α : ℝ) = 0 := by
      rw [hβz.1, hβz.2] at hs0
      simp only [mul_zero, zero_mul, add_zero, zero_add] at hs0
      exact Or.resolve_right (mul_eq_zero.mp hs0) hdne
    exact ⟨hα, hβz⟩
  -- 14. 线性无关族 → span = ⊤
  have hli : LinearIndependent ℝ (![(u1 - u0 : V3),
      (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3) - u0,
      (mid + eps3 • (a - mid) : V3) - u0]) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one] at hg
    have h5 := hvec3 (g 0) (g 1) (g 2) hg
    intro i
    fin_cases i
    · exact h5.1
    · exact h5.2.1
    · exact h5.2.2
  have hspan3 : Submodule.span ℝ
      (Set.range (![(u1 - u0 : V3),
        (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3) - u0,
        (mid + eps3 • (a - mid) : V3) - u0])) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [finrank_euclideanSpace_fin])
  -- 15. vectorSpan = ⊤ → affineSpan = ⊤ → 正体积 → 非 nullSet
  have hu0S : (u0 : V3) ∈ ({u0, u1, (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3),
      (mid + eps3 • (a - mid) : V3)} : Set V3) := Set.mem_insert _ _
  have hvtop : vectorSpan
      ℝ ({u0, u1, (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3),
        (mid + eps3 • (a - mid) : V3)} : Set V3) = ⊤ := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ hu0S]
    refine top_le_iff.mp ?_
    rw [← hspan3]
    exact Submodule.span_le.mpr (by
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact Submodule.subset_span (Set.mem_image_of_mem _ (by simp))
      · exact Submodule.subset_span (Set.mem_image_of_mem _ (by simp))
      · exact Submodule.subset_span (Set.mem_image_of_mem _ (by simp)))
  have hfr : Module.finrank ℝ (vectorSpan
      ℝ ({u0, u1, (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3),
        (mid + eps3 • (a - mid) : V3)} : Set V3)) = 3 := by
    rw [hvtop]
    simp [finrank_euclideanSpace_fin]
  have htop : affineSpan
      ℝ ({u0, u1, (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3),
        (mid + eps3 • (a - mid) : V3)} : Set V3) = ⊤ :=
    p24_affineSpan_top_of_finrank (⟨u0, hu0S⟩ :
      ({u0, u1, (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3),
        (mid + eps3 • (a - mid) : V3)} : Set V3).Nonempty) hfr
  have hvpos : 0 < volume (convexHull
      ℝ ({u0, u1, (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3),
        (mid + eps3 • (a - mid) : V3)} : Set V3)) := p24_volume_pos_of_affineSpan htop
  -- 16. hull ⊆ X 与非 nullSet
  have hsub4 : ({u0, u1, (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3),
      (mid + eps3 • (a - mid) : V3)} : Set V3) ⊆ mcell2 V [u0, u1, v, w] := by
    intro z hz
    simp only [Set.mem_insert_iff] at hz
    rcases hz with rfl | hz
    · exact ends.1
    · rcases hz with rfl | hz
      · exact ends.2
      · rcases hz with rfl | rfl
        · exact hx2X
        · exact hx3X
  have hsubX : convexHull
      ℝ ({u0, u1, (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3),
        (mid + eps3 • (a - mid) : V3)} : Set V3) ⊆ mcell2 V [u0, u1, v, w] :=
    convexHull_min hsub4 hconv
  have hnull : ¬ nullSet (mcell2 V [u0, u1, v, w]) := by
    intro hc
    rw [nullSet] at hc
    have hle : volume (convexHull
        ℝ ({u0, u1, (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3),
          (mid + eps3 • (a - mid) : V3)} : Set V3)) ≤ volume (mcell2 V [u0, u1, v, w]) :=
      measure_mono hsubX
    have hpos2 : 0 < volume (mcell2 V [u0, u1, v, w]) :=
      lt_of_lt_of_le hvpos hle
    rw [hc] at hpos2
    exact lt_irrefl _ hpos2
  -- 17. HDTFNFZ → edgeX
  have hvxeq : VX V (mcell2 V [u0, u1, v, w]) = V ∩ mcell2 V [u0, u1, v, w] :=
    HDTFNFZ (v := u0) hs hp hbar (show mcell2 V [u0, u1, v, w] = mcell 2 V [u0, u1, v, w] from rfl)
      hnull
  refine ⟨mcell2 V [u0, u1, v, w], Set.mem_setOf.mpr ⟨2, [u0, u1, v, w], rfl, hbar⟩, ?_, ?_⟩
  · rw [edgeX, hvxeq]
    exact Set.mem_setOf.mpr ⟨u0, u1, rfl, ⟨hu0, ends.1⟩, ⟨hu1, ends.2⟩, hne⟩
  · intro q hq hsub
    -- 18. x_i 离轴 + 方位角双零矛盾
    have hx2off : ¬ Collinear3 u0 u1 (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3) :=
      p24_offaxis_of_orth u0 u1 mid _ (omegaListN V [u0, u1, v, w] 2 - mid) e3
        (dist u0 u1) eps2 hne haxd h33 hmiddef rfl (ne_of_gt heps2) hE2e3 hz2n
    have hx3off : ¬ Collinear3 u0 u1 (mid + eps3 • (a - mid) : V3) :=
      p24_offaxis_of_orth u0 u1 mid _ (a - mid) e3
        (dist u0 u1) eps3 hne haxd h33 hmiddef rfl (ne_of_gt heps3) hEae3 hz3n
    have ha2x2 : azim u0 u1 q (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3) = 0 :=
      hsub hx2X
    have ha2x3 : azim u0 u1 q (mid + eps3 • (a - mid) : V3) = 0 :=
      hsub hx3X
    have hz1' : (((mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3)) - mid)
        = (eps2 • (omegaListN V [u0, u1, v, w] 2 - mid : V3)) := by module
    have hz3' : (((mid + eps3 • (a - mid) : V3)) - mid)
        = (eps3 • (a - mid : V3)) := by module
    have hζ1x : (((mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3)) - mid) ⬝ᵥ e3 = 0 := by
      rw [hz1', WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, hE2e3]
      ring
    have hζ3x : (((mid + eps3 • (a - mid) : V3)) - mid) ⬝ᵥ e3 = 0 := by
      rw [hz3', WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, hEae3]
      ring
    have hindep' : ∀ r : ℝ, (((mid + eps3 • (a - mid) : V3)) - mid) ≠
        r • (((mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3)) - mid) := by
      intro r hr
      have hz3'' : (((mid + eps3 • (a - mid) : V3)) - mid)
          = (eps3 • (a - mid : V3)) := by module
      have hz2'' : (((mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3)) - mid)
          = (eps2 • (omegaListN V [u0, u1, v, w] 2 - mid : V3)) := by module
      rw [hz3'', hz2''] at hr
      have h6 : ((a - mid : V3)) = (eps3⁻¹) • (r • (eps2 •
        ((omegaListN V [u0, u1, v, w] 2 - mid : V3)))) := by
        have h7 := congrArg (fun x : V3 => ((eps3 : ℝ)⁻¹) • x) hr
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt heps3), one_smul] at h7
        exact h7
      have hfinal := hindep (eps3⁻¹ * (r * eps2))
      rw [mul_smul, mul_smul] at hfinal
      exact absurd h6 hfinal
    exact p24_caseB2_azim_kill u0 u1 q mid
      (mid + eps2 • (omegaListN V [u0, u1, v, w] 2 - mid) : V3)
      (mid + eps3 • (a - mid) : V3) e3 (dist u0 u1) eps2 eps3
      hne haxd h33 hmiddef (lt_of_lt_of_le (by norm_num) hdgt) hq hx2off hx3off
      ha2x2 ha2x3 heps2 heps3 hζ1x hζ3x hindep'

/-! ## (β) 支第五波：换叶主件群（2026-10-12 波，支撑面引理的换叶等效路线，
全部真证零 sorry）

**数学骨架**（退化子情形 ω₂ = ω₃ 换叶的存在性内核）：饱和 packing 短棱
（`d < √8`）处必存在叶三元组 `vl`（`barV V 3 vl ∧ truncateSimplex 1 vl =
[u0,u1]`）使 `omegaListN V vl 2 ≠ omegaListN V vl 3`。反证：设每叶皆退化，
则 fan 分解（`p24_voronoi_pair_split`）+ `p24_leaf_singleton`（叶胞 = {外心}，
ω₃ = 外心）+ `p24_omega1_eq_mid`（ω₁ = 棱中点 p）把配对胞 S 写成过 p 的线段并
S = ∪_v [p, ω₂(v)]（ω₂(v) = `omegaListN V [u0,u1,v] 2`）；而
`p24_pair_patch_mem`（中点 margin 严格的圆盘 patch——affDim 波 patch 三点件
的全量化，路线图 §剩余风险"affDim(S∩H_v) = 1 + relint 内球论证"的等效件）
给出 S ⊇ p 处 2 维圆盘；叶指标局部有限（`p24_packing_finite_inter_ball_at`，
体积计数 packing 局部有限的平移形式）+ `p24_escape_direction`（有限条过 p
射线盖不住 2 维圆盘：逃逸方向 = 斜率 sup+1 构造）——圆盘点 x* ∈ S 不落在
任何线段上，矛盾。此即路线图"退化叶 fan 三角 conv{p, ω₂, cc} 在 p 处尖角
⟹ relint 圆盘余部强制另一叶"的形式化（尖角逼叶 = 圆盘 vs 有限射线覆盖）。 -/

/-- **换叶件 1 · patch 圆盘**（affDim 波 `p24_affDim_voronoiList2` 内部
`hmem` 件的全量提取，`d < √8` 形态）：中点 `p = u0 + (1/2)•(u1−u0)` 处，
bisector 平面方向 `D = ker (p24_dotR (u1−u0))` 内 `‖v‖ ≤ 2R`
（`R = (s − d/2)/8`，`s = √(4−(d/2)²)`）的 `p + v` 全部落进配对胞
`voronoiList V [u0,u1]`。数学：margin（packing 两两 ≥ 2 + 平行四边形恒等式
给 `‖w − p‖ ≥ s > d/2`）+ 三角不等式 `d/2 + ‖v‖ ≤ s − 2R ≤ s − ‖v‖`。 -/
private theorem p24_pair_patch_mem (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1) (hd8 : dist u0 u1 < Real.sqrt 8)
    (s : ℝ) (hsdef : s = Real.sqrt (4 - (dist u0 u1 / 2) ^ 2))
    (R : ℝ) (hRdef : R = (s - dist u0 u1 / 2) / 8)
    (v : V3) (hvD : v ∈ LinearMap.ker (p24_dotR (u1 - u0)))
    (hvn : ‖v‖ ≤ 2 * R) :
    u0 + (1 / 2 : ℝ) • (u1 - u0) + v ∈ voronoiList V [u0, u1] := by
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  set d : ℝ := dist u0 u1 with hddef
  have hdpos : (0:ℝ) ≤ d := dist_nonneg
  have hmid0 : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
  have hmid1 : p - u1 = -((1 / 2 : ℝ) • (u1 - u0)) := by rw [hpdef]; module
  have hpu0 : ‖p - u0‖ = d / 2 := by
    rw [hmid0, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show (0:ℝ) < (1 / 2 : ℝ) by norm_num), ← dist_eq_norm,
      dist_comm u1 u0, hddef]
    ring
  have hpu1 : ‖p - u1‖ = d / 2 := by
    rw [hmid1, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show (0:ℝ) < (1 / 2 : ℝ) by norm_num), ← dist_eq_norm,
      dist_comm u1 u0, hddef]
    ring
  -- bisector 平面方向子模与维数
  set D : Submodule ℝ V3 := LinearMap.ker (p24_dotR (u1 - u0)) with hDdef
  have hDax : ∀ z ∈ D, (u1 - u0) ⬝ᵥ z = 0 := fun z hz => LinearMap.mem_ker.mp hz
  have hDmid0 : ∀ z ∈ D, inner ℝ (p - u0) z = 0 := by
    intro z hz
    rw [hmid0, p24_hsmL, inner_eq_dot, hDax z hz]
    ring
  have hDmid1 : ∀ z ∈ D, inner ℝ (p - u1) z = 0 := by
    intro z hz
    rw [hmid1, inner_neg_left, p24_hsmL, inner_eq_dot, hDax z hz]
    ring
  -- margin 刻度与 patch 半径
  set d2 : ℝ := d / 2 with hd2def
  have hd2pos : (0:ℝ) ≤ d2 := by positivity
  have hsqd : d ^ 2 < 8 := by
    have h1 : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
    have hsq1 : d ^ 2 < (Real.sqrt 8) ^ 2 := by nlinarith
    rwa [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8)] at hsq1
  have hd2sq : d2 ^ 2 < 2 := by nlinarith
  have hsnn : (0:ℝ) ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  have h4pos : (0:ℝ) ≤ 4 - d2 ^ 2 := by linarith
  have hsd2 : d2 < s := by
    have h1 : d2 ^ 2 < s ^ 2 := by
      rw [hsdef, Real.sq_sqrt h4pos]
      nlinarith
    by_contra hcon
    have h2 : s ^ 2 ≤ d2 ^ 2 := by nlinarith [hsnn, hd2pos, hcon]
    linarith
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRkey : d2 + 2 * R ≤ s - 2 * R := by
    have h1 : 4 * R ≤ s - d2 := by rw [hRdef]; field_simp; linarith
    linarith
  have hvn' : ‖v‖ ≤ 2 * R := hvn
  -- margin：其余 packing 点在 p 为心半径 s 球外
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
  -- 配对胞的两闭胞交形式
  have hpair : voronoiList V [u0, u1] = voronoiClosed V u1 ∩ voronoiClosed V u0 := by
    rw [show (voronoiList V [u0, u1] : Set V3) = voronoiSet V (setOfList [u0, u1]) from rfl,
      show (setOfList [u0, u1] : Set V3) = {u0, u1} from by ext x; simp [setOfList],
      VORONOI_SET_2]
  -- patch 点到两端的距离
  have hdu1 : ∀ z ∈ D, ‖(p + z) - u1‖ ≤ d2 + ‖z‖ := by
    intro z hz
    rw [show ((p + z) - u1 : V3) = (p - u1) + z from by abel]
    exact le_trans (norm_add_le _ _) (by rw [hpu1])
  have hdu0 : ∀ z ∈ D, ‖(p + z) - u0‖ ≤ d2 + ‖z‖ := by
    intro z hz
    rw [show ((p + z) - u0 : V3) = (p - u0) + z from by abel]
    exact le_trans (norm_add_le _ _) (by rw [hpu0])
  have hdeq : ∀ z ∈ D, ‖(p + z) - u0‖ = ‖(p + z) - u1‖ := by
    intro z hz
    have hq0 : ‖(p + z) - u0‖ ^ 2 = d2 ^ 2 + ‖z‖ ^ 2 := by
      rw [show ((p + z) - u0 : V3) = (p - u0) + z from by abel,
        p24_pythI (hDmid0 z hz), hpu0]
    have hq1 : ‖(p + z) - u1‖ ^ 2 = d2 ^ 2 + ‖z‖ ^ 2 := by
      rw [show ((p + z) - u1 : V3) = (p - u1) + z from by abel,
        p24_pythI (hDmid1 z hz), hpu1]
    have hsqeq : ‖(p + z) - u0‖ ^ 2 = ‖(p + z) - u1‖ ^ 2 := by rw [hq0, hq1]
    have h1 : Real.sqrt (‖(p + z) - u0‖ ^ 2) = Real.sqrt (‖(p + z) - u1‖ ^ 2) := by
      rw [hsqeq]
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (norm_nonneg _)] at h1
  -- patch 点 ∈ 配对胞
  rw [hpair]
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · show dist (p + v) u1 ≤ dist (p + v) w
    rcases eq_or_ne w u1 with rfl | hw1
    · exact le_refl _
    rcases eq_or_ne w u0 with rfl | hw0
    · have he := hdeq v hvD
      rw [← dist_eq_norm, ← dist_eq_norm] at he
      rw [he]
    · have h1 := hdu1 v hvD
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
  · show dist (p + v) u0 ≤ dist (p + v) w
    rcases eq_or_ne w u1 with rfl | hw1
    · have he := hdeq v hvD
      rw [← dist_eq_norm, ← dist_eq_norm] at he
      rw [he]
    rcases eq_or_ne w u0 with rfl | hw0
    · exact le_refl _
    · have h1 := hdu0 v hvD
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

/-- **换叶件 2 · packing 局部有限**（`Packing.finite_inter_ball` 的平移形式：
球心任意）。证明：平移 `x ↦ x − c` 保持 packing，归约到 0 心版本 +
单射原像有限。 -/
private theorem p24_packing_finite_inter_ball_at {V : Set V3} (hp : Packing V)
    (c : V3) (r : ℝ) : (V ∩ Metric.ball c r).Finite := by
  classical
  have hpT : Packing ((fun x : V3 => x - c) '' V) := by
    intro u hu v hv hlt
    simp only [Set.mem_image] at hu hv
    obtain ⟨x, hxV, rfl⟩ := hu
    obtain ⟨y, hyV, rfl⟩ := hv
    have hd : dist x y < 2 := by
      have h1 : dist (x - c) (y - c) < 2 := hlt
      have h2 : dist (x - c) (y - c) = dist x y := by
        rw [dist_eq_norm, dist_eq_norm]; congr 1; module
      rwa [h2] at h1
    exact congrArg (fun z : V3 => z - c) (hp x hxV y hyV hd)
  have hfin0 : (((fun x : V3 => x - c) '' V) ∩ Metric.ball 0 r).Finite :=
    hpT.finite_inter_ball r
  have hf_inj : Function.Injective (fun x : V3 => x - c) := by
    intro x y hxy
    have hxy' : x - c = y - c := hxy
    have h2 : x - c + c = y - c + c := by rw [hxy']
    simpa using h2
  set S' : Set V3 := ((fun x : V3 => x - c) '' V) ∩ Metric.ball 0 r with hS'
  have hinj : Set.InjOn (fun x : V3 => x - c) ((fun x : V3 => x - c) ⁻¹' S') :=
    fun x _ y _ h => hf_inj h
  have hpre : ((fun x : V3 => x - c) ⁻¹' S').Finite := Set.Finite.preimage hinj hfin0
  have hkey : V ∩ Metric.ball c r ⊆ (fun x : V3 => x - c) ⁻¹' S' := by
    intro x hx
    obtain ⟨hxV, hball⟩ := hx
    refine ⟨⟨x, hxV, rfl⟩, ?_⟩
    show dist (x - c) 0 < r
    have h3 : dist (x - c) 0 = dist x c := by
      rw [dist_eq_norm, dist_eq_norm]; congr 1; module
    rwa [h3]
  exact Set.Finite.subset hpre hkey

/-- **换叶件 3 · 方向逃逸**：2 维子空间内有限条过原点射线盖不满任意小球。
有限方向集 {w v}（皆非零、皆在 D 内）构造逃逸向量 u ∈ D：取独立
a, b ∈ D，斜率参数 τ ↦ a + τ•b 的"坏 τ"每 v 至多一个（两解 ⟹ D = span{w v}
与维数 1 矛盾），取 sup + 1 逃出全部；正数缩放进指定球（缩放保持不平行）。 -/
private theorem p24_escape_direction {D : Submodule ℝ V3}
    (hD2 : Module.finrank ℝ D = 2) (F : Set V3) (hFin : F.Finite) (w : V3 → V3)
    (hwD : ∀ v ∈ F, w v ∈ D) (hwne : ∀ v ∈ F, w v ≠ 0) (eps : ℝ) (hε : 0 < eps) :
    ∃ u ∈ D, u ≠ 0 ∧ ‖u‖ ≤ eps ∧ ∀ v ∈ F, ∀ t : ℝ, 0 < t → u ≠ t • w v := by
  classical
  -- 1. 取 D 内独立向量 a, b
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h] at hD2
    simp at hD2
  obtain ⟨a, haD, hane⟩ : ∃ a ∈ D, a ≠ 0 := by
    by_contra hcon
    refine hDne (Submodule.ext fun x => ?_)
    constructor
    · intro hx
      have hx0 : x = 0 := by
        by_contra hh
        exact hcon ⟨x, hx, hh⟩
      rw [hx0]
      exact (Submodule.mem_bot (R := ℝ)).2 rfl
    · intro hx
      rw [Submodule.mem_bot] at hx
      exact hx.symm ▸ Submodule.zero_mem D
  have hfr1 : Module.finrank ℝ (Submodule.span ℝ {a}) = 1 := finrank_span_singleton hane
  have hDne1 : D ≠ (Submodule.span ℝ {a}) := by
    intro h
    rw [h, hfr1] at hD2
    simp at hD2
  obtain ⟨b, hbD, hbs⟩ : ∃ b ∈ D, b ∉ (Submodule.span ℝ {a}) := by
    by_contra hcon
    push_neg at hcon
    refine hDne1 (Submodule.ext fun x => ?_)
    exact ⟨fun hx => hcon x hx, fun hx =>
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr haD) : _ ≤ D) hx⟩
  have hbne : b ≠ 0 := by
    intro h
    apply hbs
    rw [h]
    exact Submodule.mem_span_singleton.2 ⟨0, by simp⟩
  -- 2. ![a, b] 线性无关 ⟹ span = D（finrank = 2）
  have hli : LinearIndependent ℝ ![a, b] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    fin_cases i
    · by_contra hg0
      rcases eq_or_ne (g 1) 0 with hg1 | hg1
      · simp only [hg1, zero_smul, add_zero] at hg
        exact hg0 ((smul_eq_zero.mp hg).resolve_right hane)
      · apply hbs
        refine Submodule.mem_span_singleton.2 ⟨-g 0 / g 1, ?_⟩
        have hkey : g 1 • ((-g 0 / g 1) • a) = g 1 • b := by
          rw [smul_smul]
          have hrat : g 1 * (-g 0 / g 1) = -g 0 := by field_simp
          rw [hrat, neg_smul, neg_eq_iff_add_eq_zero]
          exact hg
        exact smul_right_injective V3 hg1 hkey
    · by_contra hg1'
      have hg1 : g 1 ≠ 0 := fun hh => hg1' hh
      apply hbs
      refine Submodule.mem_span_singleton.2 ⟨-g 0 / g 1, ?_⟩
      have hkey : g 1 • ((-g 0 / g 1) • a) = g 1 • b := by
        rw [smul_smul]
        have hrat : g 1 * (-g 0 / g 1) = -g 0 := by field_simp
        rw [hrat, neg_smul, neg_eq_iff_add_eq_zero]
        exact hg
      exact smul_right_injective V3 hg1 hkey
  have hspD : Submodule.span ℝ (Set.range ![a, b]) = D := by
    have hle : Submodule.span ℝ (Set.range ![a, b]) ≤ D := by
      rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact haD
      · exact hbD
    have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range ![a, b])) = 2 := by
      rw [finrank_span_eq_card hli]
      simp
    exact Submodule.eq_of_le_of_finrank_eq hle (hfr.trans hD2.symm)
  -- 3. 每 v 的直线参数至多一个（两解 ⟹ D ≤ span{w v} ⟹ finrank 矛盾）
  set T : V3 → Set ℝ := fun v => {τ : ℝ | ∃ r : ℝ, a + τ • b = r • w v} with hTdef
  have hTsub : ∀ v ∈ F, ∀ τ₁ ∈ T v, ∀ τ₂ ∈ T v, τ₁ = τ₂ := by
    intro v hv τ₁ hτ₁ τ₂ hτ₂
    obtain ⟨r₁, hr₁⟩ := hτ₁
    obtain ⟨r₂, hr₂⟩ := hτ₂
    by_contra hne
    have hτne : (τ₁ - τ₂ : ℝ) ≠ 0 := sub_ne_zero.mpr hne
    have hsub1 : (τ₁ - τ₂ : ℝ) • b = (r₁ - r₂) • w v := by
      have heq : (a + τ₁ • b) - (a + τ₂ • b) = r₁ • w v - r₂ • w v := by rw [hr₁, hr₂]
      have he1 : (a + τ₁ • b) - (a + τ₂ • b) = (τ₁ - τ₂ : ℝ) • b := by
        simp only [add_sub_add_left_eq_sub]
        module
      have he2 : r₁ • w v - r₂ • w v = (r₁ - r₂) • w v := (sub_smul r₁ r₂ (w v)).symm
      rw [he1, he2] at heq
      exact heq
    have hb' : b = ((r₁ - r₂) / (τ₁ - τ₂ : ℝ)) • w v := by
      apply smul_right_injective V3 hτne
      show (τ₁ - τ₂ : ℝ) • b = (τ₁ - τ₂ : ℝ) • (((r₁ - r₂) / (τ₁ - τ₂ : ℝ)) • w v)
      rw [smul_smul]
      have hrat : (τ₁ - τ₂ : ℝ) * ((r₁ - r₂) / (τ₁ - τ₂ : ℝ)) = r₁ - r₂ := by
        field_simp
      rw [hrat]
      exact hsub1
    have hain : a ∈ Submodule.span ℝ {w v} := by
      have e1 : a = r₁ • w v - τ₁ • b := by
        rw [eq_comm, sub_eq_iff_eq_add]
        exact hr₁.symm
      have h3 : a = (r₁ - τ₁ * ((r₁ - r₂) / (τ₁ - τ₂ : ℝ))) • w v := by
        rw [e1, hb', smul_smul, ← sub_smul]
      exact Submodule.mem_span_singleton.2 ⟨_, h3.symm⟩
    have hbin : b ∈ Submodule.span ℝ {w v} :=
      Submodule.mem_span_singleton.2 ⟨_, hb'.symm⟩
    have hle1 : D ≤ Submodule.span ℝ {w v} := by
      rw [← hspD, Submodule.span_le]
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact hain
      · exact hbin
    have hle2 : Submodule.span ℝ {w v} ≤ D :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hwD v hv))
    have h1 : Module.finrank ℝ (Submodule.span ℝ {w v}) = 1 :=
      finrank_span_singleton (hwne v hv)
    have heq : Submodule.span ℝ {w v} = D := le_antisymm hle2 hle1
    rw [heq] at h1
    omega
  -- 4. 逃逸参数 τ* = sup + 1 与逃逸向量
  set rep : V3 → ℝ := fun v =>
    if h : (T v).Nonempty then Classical.choose h else 0 with hrepdef
  set τstar : ℝ := sSup (rep '' F) + 1 with hτdef
  set ustar : V3 := a + τstar • b with hustardef
  have huDstar : ustar ∈ D := Submodule.add_mem _ haD (Submodule.smul_mem _ _ hbD)
  have hune : ustar ≠ 0 := by
    intro hu0
    rcases eq_or_ne τstar 0 with hτ0 | hτ0
    · rw [hustardef, hτ0, zero_smul, add_zero] at hu0
      exact hane hu0
    · apply hbs
      refine Submodule.mem_span_singleton.2 ⟨-1 / τstar, ?_⟩
      have h2 : τstar • b = -a := eq_neg_of_add_eq_zero_right hu0
      refine smul_right_injective V3 hτ0 ?_
      show τstar • ((-1 / τstar) • a) = τstar • b
      rw [smul_smul]
      have hrat : (τstar : ℝ) * (-1 / τstar) = -1 := by field_simp
      rw [hrat, neg_one_smul, h2]
  -- 5. 正数缩放进指定球
  have hunepos : 0 < ‖ustar‖ := norm_pos_iff.mpr hune
  set c : ℝ := min 1 (eps / ‖ustar‖) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact lt_min (by norm_num) (div_pos hε hunepos)
  refine ⟨c • ustar, Submodule.smul_mem _ _ huDstar, ?_, ?_, ?_⟩
  · intro h
    have hz : ustar = 0 := smul_right_injective V3 (ne_of_gt hcpos)
      (show c • ustar = c • (0 : V3) from by rw [h]; simp)
    exact hune hz
  · have h1 : ‖c • ustar‖ = c * ‖ustar‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    have h2 : c ≤ eps / ‖ustar‖ := min_le_right _ _
    rw [h1]
    have h3 : c * ‖ustar‖ ≤ (eps / ‖ustar‖) * ‖ustar‖ := by
      apply mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    calc c * ‖ustar‖ ≤ (eps / ‖ustar‖) * ‖ustar‖ := h3
      _ = eps := by field_simp
  · intro v hv t ht hcon
    have hct : ustar = (t / c) • w v := by
      apply smul_right_injective V3 (ne_of_gt hcpos)
      show c • ustar = c • ((t / c) • w v)
      rw [hcon, smul_smul]
      have hrat : c * (t / c) = t := by field_simp
      rw [hrat]
    have hτin : τstar ∈ T v := ⟨t / c, hct⟩
    have hne : (T v).Nonempty := ⟨τstar, hτin⟩
    have hrepin : Classical.choose hne ∈ T v := Classical.choose_spec hne
    have hτeq : τstar = Classical.choose hne := hTsub v hv τstar hτin _ hrepin
    have himg : rep v ∈ rep '' F := ⟨v, hv, rfl⟩
    have hbd : BddAbove (rep '' F) := Set.Finite.bddAbove (Set.Finite.image rep hFin)
    have hsup : rep v ≤ sSup (rep '' F) := le_csSup hbd himg
    have hrv : rep v = Classical.choose hne := dif_pos hne
    rw [hrv, ← hτeq] at hsup
    have hτ1 : τstar = sSup (rep '' F) + 1 := rfl
    linarith [hsup]

/-- 轴正交件：`z, w` 各自与 `u0, u1` 等距 ⟹ 轴向量 `u1 − u0` 与差向量
`z − w` 正交（两点平方恒等式 `norm_sub_sq_real` 相减；bisector 平面方向子模
成员判定的初等核）。 -/
private theorem p24_eqdist_axis_dot {u0 u1 z w : V3} (hz : dist z u0 = dist z u1)
    (hw : dist w u0 = dist w u1) : (u1 - u0 : V3) ⬝ᵥ (z - w) = 0 := by
  have hzn : ‖z - u0‖ = ‖z - u1‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]; exact hz
  have hwn : ‖w - u0‖ = ‖w - u1‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]; exact hw
  have ez0 : ‖z - u0‖ ^ 2 = ‖z‖ ^ 2 - 2 * inner ℝ z u0 + ‖u0‖ ^ 2 := norm_sub_sq_real z u0
  have ez1 : ‖z - u1‖ ^ 2 = ‖z‖ ^ 2 - 2 * inner ℝ z u1 + ‖u1‖ ^ 2 := norm_sub_sq_real z u1
  have ew0 : ‖w - u0‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w u0 + ‖u0‖ ^ 2 := norm_sub_sq_real w u0
  have ew1 : ‖w - u1‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w u1 + ‖u1‖ ^ 2 := norm_sub_sq_real w u1
  have hzsq : ‖z - u0‖ ^ 2 = ‖z - u1‖ ^ 2 := by rw [hzn]
  have hwsq : ‖w - u0‖ ^ 2 = ‖w - u1‖ ^ 2 := by rw [hwn]
  have key1 : 2 * inner ℝ z u1 - 2 * inner ℝ z u0 = ‖u1‖ ^ 2 - ‖u0‖ ^ 2 := by
    linarith [ez0, ez1, hzsq]
  have key2 : 2 * inner ℝ w u1 - 2 * inner ℝ w u0 = ‖u1‖ ^ 2 - ‖u0‖ ^ 2 := by
    linarith [ew0, ew1, hwsq]
  have hzwi : inner ℝ (u1 - u0) (z - w) = 0 := by
    rw [real_inner_comm (z - w) (u1 - u0), inner_sub_left z w (u1 - u0),
      inner_sub_right z u1 u0, inner_sub_right w u1 u0]
    linarith
  rw [← inner_eq_dot]
  exact hzwi

/-- 叶四元组显式化：`barV V 3 vl` 的叶（长度 4）若截断到 `j=1` 是
`[u0, u1]`，则 `vl` 逐位为 `[u0, u1, v, w]`（`BARV_3_EXPLICIT` + 前两位
注入相等；`p24_caseB2_general` 开头同款）。 -/
private theorem p24_leaf_quad_of_trunc (V : Set V3) (u0 u1 : V3) {vl : List V3}
    (hbar : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1]) :
    ∃ v w : V3, vl = [u0, u1, v, w] := by
  obtain ⟨q0, q1, q2, q3, hvll⟩ := BARV_3_EXPLICIT V vl hbar
  subst hvll
  have htrq : truncateSimplex 1 [q0, q1, q2, q3] = [q0, q1] := by
    rw [truncateSimplex1_pair [q0, q1, q2, q3] (by norm_num)]
    simp [elV]
  have hpair01 : [u0, u1] = [q0, q1] := htr.symm.trans htrq
  injection hpair01 with e0 e1l
  injection e1l with e1 e1nil
  subst e0
  subst e1
  exact ⟨q2, q3, rfl⟩

/-- **换叶主件**（退化支的支撑面引理等效路线，第五波件群的装配收口）：
饱和 packing 的短棱（`d < √8`）处必存在**非退化叶**——`barV V 3 vl ∧
truncateSimplex 1 vl = [u0, u1] ∧ omegaListN V vl 2 ≠ omegaListN V vl 3`。
反证：设每叶皆退化（`ω₂ = ω₃`），则
(1) fan 分解 `p24_voronoi_pair_split` + 叶胞单点 `p24_leaf_singleton` +
`p24_omega1_eq_mid`（ω₁ = 棱中点 p）把配对胞 S 写成过 p 的线段并
S = ∪_叶 [p, e vl]（e vl = 叶胞单点 = ω₂ = ω₃）；
(2) 叶集有限：每叶四顶点等距于 e vl（闭胞交成员），饱和 packing 给外接
半径 < 2，顶点全落进 p 的固定球 `V ∩ ball p (4 + √8)`，经
`p24_packing_finite_inter_ball_at` + 四元组显式化截断；
(3) 方向集 {e vl − p} ⊆ bisector 平面方向子模 D（`p24_eqdist_axis_dot`，
两端等距）有限非零，`p24_escape_direction` 给 D 内小球逃逸向量 u；
(4) `p24_pair_patch_mem`（中点 margin 严格圆盘 patch）把 p + u 抬进 S；
fan 分解迫使 p + u 落在某叶线段 [p, e vl₀] 上，即 u = t₂•(e vl₀ − p)、
t₂ > 0——与逃逸方向（对一切叶方向非平行）矛盾。 -/
private theorem p24_nondeg_leaf_exists (V : Set V3) (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hd8 : dist u0 u1 < Real.sqrt 8) :
    ∃ vl : List V3, barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1] ∧
      omegaListN V vl 2 ≠ omegaListN V vl 3 := by
  classical
  by_contra hcon
  push_neg at hcon
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hhl : hl [u0, u1] < Real.sqrt 2 := p24_hl_pair_lt_sqrt2 hd8
  have hu0u1n : (u1 - u0 : V3) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hD2 : Module.finrank ℝ (LinearMap.ker (p24_dotR (u1 - u0))) = 2 :=
    p24_finrank_ker_dot (a := u1 - u0) hu0u1n
  -- 中点距离数据
  have hpu0 : dist p u0 = dist u0 u1 / 2 := by
    rw [dist_eq_norm]
    have h1 : (p - u0 : V3) = (1 / 2 : ℝ) • (u1 - u0) := by
      rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < 1 / 2 by norm_num)]
    rw [show dist u0 u1 = ‖u1 - u0‖ from by rw [dist_eq_norm, norm_sub_rev]]
    ring
  have hpu1 : dist p u1 = dist u0 u1 / 2 := by
    rw [dist_eq_norm]
    have h1 : (p - u1 : V3) = (1 / 2 : ℝ) • (u0 - u1) := by
      rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < 1 / 2 by norm_num)]
    rw [show dist u0 u1 = ‖u1 - u0‖ from by rw [dist_eq_norm, norm_sub_rev]]
    rw [norm_sub_rev]
    ring
  -- patch 半径刻度
  have hdpos : (0:ℝ) ≤ dist u0 u1 := dist_nonneg
  have hsqd : dist u0 u1 ^ 2 < 8 := by
    have hs8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    nlinarith [hd8, hs8, hdpos]
  have hd2lt : (dist u0 u1 / 2) ^ 2 < 4 - (dist u0 u1 / 2) ^ 2 := by
    have hsq2 : (dist u0 u1 / 2) ^ 2 = dist u0 u1 ^ 2 / 4 := by ring
    rw [hsq2]; linarith
  have hsd2 : dist u0 u1 / 2 < Real.sqrt (4 - (dist u0 u1 / 2) ^ 2) := by
    have hd2pos : (0:ℝ) ≤ dist u0 u1 / 2 := by linarith
    have e1 : Real.sqrt ((dist u0 u1 / 2) ^ 2) < Real.sqrt (4 - (dist u0 u1 / 2) ^ 2) :=
      Real.sqrt_lt_sqrt (sq_nonneg (dist u0 u1 / 2)) hd2lt
    have e2 : Real.sqrt ((dist u0 u1 / 2) ^ 2) = dist u0 u1 / 2 := by
      rw [Real.sqrt_sq_eq_abs (dist u0 u1 / 2), abs_of_nonneg hd2pos]
    linarith
  set s : ℝ := Real.sqrt (4 - (dist u0 u1 / 2) ^ 2) with hsdef
  set R : ℝ := (s - dist u0 u1 / 2) / 8 with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    exact div_pos (sub_pos.mpr hsd2) (by norm_num)
  -- 1. 叶集有限：顶点全落进 p 的固定球
  set Vb : Set V3 := V ∩ Metric.ball p (4 + Real.sqrt 8) with hVbdef
  have hVbfin : Vb.Finite := p24_packing_finite_inter_ball_at hp p (4 + Real.sqrt 8)
  have hLsub : {vl : List V3 | barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]} ⊆
      (fun q : V3 × V3 => [u0, u1, q.1, q.2]) '' (Vb ×ˢ Vb) := by
    rintro vl ⟨hbar, htr⟩
    obtain ⟨v, w, hvw⟩ := p24_leaf_quad_of_trunc V u0 u1 hbar htr
    rw [hvw] at hbar
    have hvn4 : voronoiNondg V [u0, u1, v, w] :=
      hbar.2 [u0, u1, v, w] ⟨⟨[], by rw [List.append_nil]⟩, by simp⟩
    have hsubV : setOfList [u0, u1, v, w] ⊆ V := hvn4.2.1
    have hvv : v ∈ V := hsubV (by simp [setOfList])
    have hwv : w ∈ V := hsubV (by simp [setOfList])
    -- 叶胞单点 a 与四点等距
    obtain ⟨a, ha1, -, -⟩ := p24_leaf_singleton V [u0, u1, v, w] hs hp hbar
    have hmemA : a ∈ voronoiList V [u0, u1, v, w] := by rw [ha1]; rfl
    have hcl : ∀ y ∈ (setOfList [u0, u1, v, w] : Set V3), a ∈ voronoiClosed V y := by
      intro y hy
      exact Set.mem_sInter.mp hmemA (voronoiClosed V y) ⟨y, hy, rfl⟩
    have hu0L : u0 ∈ (setOfList [u0, u1, v, w] : Set V3) := by simp [setOfList]
    have hu1L : u1 ∈ (setOfList [u0, u1, v, w] : Set V3) := by simp [setOfList]
    have hvL : v ∈ (setOfList [u0, u1, v, w] : Set V3) := by simp [setOfList]
    have hwL : w ∈ (setOfList [u0, u1, v, w] : Set V3) := by simp [setOfList]
    have heq0 : ∀ y ∈ (setOfList [u0, u1, v, w] : Set V3),
        dist a y = dist a u0 := by
      intro y hy
      exact le_antisymm (Set.mem_setOf.mp (hcl y hy) u0 hu0)
        (Set.mem_setOf.mp (hcl u0 hu0L) y (hsubV hy))
    -- 饱和给外接半径 < 2（a 在 u0 的闭胞内）
    obtain ⟨y0, hy0V, hy0d⟩ := hs a
    have hr2 : dist a u0 < 2 :=
      lt_of_le_of_lt (Set.mem_setOf.mp (hcl u0 hu0L) y0 hy0V) hy0d
    -- 顶点球界：dist(y, p) ≤ 2·r + d/2 < 4 + √8
    have hballb : ∀ y : V3, y ∈ (setOfList [u0, u1, v, w] : Set V3) →
        dist y p < 4 + Real.sqrt 8 := by
      intro y hy
      have h1 : dist y u0 ≤ dist y a + dist a u0 := dist_triangle y a u0
      have h2 : dist y a = dist a y := dist_comm y a
      have h4 : dist y p ≤ dist y u0 + dist u0 p := dist_triangle y u0 p
      have h5 : dist u0 p = dist p u0 := dist_comm u0 p
      rw [h2, heq0 y hy] at h1
      rw [h5, hpu0] at h4
      linarith
    refine ⟨(v, w), ⟨⟨hvv, Metric.mem_ball.mpr (hballb v hvL)⟩,
      ⟨hwv, Metric.mem_ball.mpr (hballb w hwL)⟩⟩, hvw.symm⟩
  have hLfin : ({vl : List V3 | barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]} :
      Set (List V3)).Finite :=
    Set.Finite.subset ((hVbfin.prod hVbfin).image
      (fun q : V3 × V3 => [u0, u1, q.1, q.2])) hLsub
  -- 2. 方向集（退化叶单点 − 中点）：有限、非零、落 bisector 方向子模
  have hsin2 : ∀ vl ∈ {vl : List V3 | barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]},
      ∃ a : V3, voronoiList V vl = {a} := by
    rintro vl ⟨hbar, -⟩
    obtain ⟨a, ha1, -, -⟩ := p24_leaf_singleton V vl hs hp hbar
    exact ⟨a, ha1⟩
  choose! e heVl using hsin2
  set F : Set V3 := (fun vl : List V3 => e vl - p) ''
    {vl : List V3 | (barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]) ∧ e vl ≠ p}
    with hFdef
  have hFfin : F.Finite :=
    (Set.Finite.subset hLfin (fun _ hvl => ⟨hvl.1.1, hvl.1.2⟩)).image
      (fun vl : List V3 => e vl - p)
  have hFD : ∀ z ∈ F, z ∈ LinearMap.ker (p24_dotR (u1 - u0)) := by
    intro z hz
    rw [hFdef] at hz
    obtain ⟨vl, ⟨⟨hbar, htr⟩, -⟩, hze⟩ := (Set.mem_image _ _ _).mp hz
    obtain ⟨v2, w2, hvw⟩ := p24_leaf_quad_of_trunc V u0 u1 hbar htr
    rw [hvw] at hbar htr hze
    have hmemA : e [u0, u1, v2, w2] ∈ voronoiList V [u0, u1, v2, w2] := by
      rw [heVl [u0, u1, v2, w2] ⟨hbar, htr⟩]; rfl
    have hcl0 : e [u0, u1, v2, w2] ∈ voronoiClosed V u0 :=
      Set.mem_sInter.mp hmemA (voronoiClosed V u0) ⟨u0, by simp [setOfList], rfl⟩
    have hcl1 : e [u0, u1, v2, w2] ∈ voronoiClosed V u1 :=
      Set.mem_sInter.mp hmemA (voronoiClosed V u1) ⟨u1, by simp [setOfList], rfl⟩
    have hd01 : dist (e [u0, u1, v2, w2]) u0 = dist (e [u0, u1, v2, w2]) u1 :=
      le_antisymm (Set.mem_setOf.mp hcl0 u1 hu1) (Set.mem_setOf.mp hcl1 u0 hu0)
    rw [← hze]
    exact p24_eqdist_axis_dot hd01 (hpu0.trans hpu1.symm)
  have hFne : ∀ z ∈ F, z ≠ 0 := by
    intro z hz
    rw [hFdef] at hz
    obtain ⟨vl, ⟨-, hene⟩, hze⟩ := (Set.mem_image _ _ _).mp hz
    intro h0
    rw [h0] at hze
    exact hene (sub_eq_zero.mp hze)
  -- 3. 逃逸方向（D 内小球向量，对一切叶方向非平行）
  obtain ⟨u, huD, hune, hnle, hesc⟩ := p24_escape_direction hD2 F hFfin id hFD hFne
    (2 * R) (mul_pos (by norm_num) hRpos)
  -- 4. patch 圆盘把 p + u 抬进配对胞
  have hxS : p + u ∈ voronoiList V [u0, u1] := by
    have hraw := p24_pair_patch_mem V u0 u1 hp hu0 hu1 hne hd8 s hsdef R hRdef u huD hnle
    rwa [← hpdef] at hraw
  -- 5. fan 分解 + 线段背逼出矛盾
  have hfan := p24_voronoi_pair_split V u0 u1 hs hp hu0 hu1 hne hhl
  rw [hfan] at hxS
  obtain ⟨T, hT, hTm⟩ := Set.mem_sUnion.mp hxS
  obtain ⟨vl0, hvl0, hTeq⟩ := hT
  rcases hvl0 with ⟨hb0, htr0⟩
  obtain ⟨v, w, hvw⟩ := p24_leaf_quad_of_trunc V u0 u1 hb0 htr0
  rw [hvw] at hb0 htr0 hTeq
  rw [← hTeq] at hTm
  have hom1 : omegaListN V [u0, u1, v, w] 1 = p := by
    have hkey := p24_omega1_eq_mid V u0 u1 hs hp hu0 hu1 hne hd8
    rw [show omegaListN V [u0, u1] 1 = closestPoint
        (voronoiList V (truncateSimplex 1 [u0, u1])) (hdV [u0, u1]) from rfl] at hkey
    rw [truncateSimplex1_pair [u0, u1] (by simp)] at hkey
    simp only [elV, hdV] at hkey
    rw [← hpdef] at hkey
    show closestPoint (voronoiList V (truncateSimplex 1 [u0, u1, v, w]))
      (hdV [u0, u1, v, w]) = p
    rw [htr0, show hdV [u0, u1, v, w] = u0 from by simp [hdV]]
    exact hkey
  obtain ⟨a, ha1, ha2, ha3⟩ := p24_leaf_singleton V [u0, u1, v, w] hs hp hb0
  have hmemA : e [u0, u1, v, w] ∈ voronoiList V [u0, u1, v, w] := by
    rw [heVl [u0, u1, v, w] ⟨hb0, htr0⟩]; rfl
  have hea : e [u0, u1, v, w] = a := by
    rw [ha1] at hmemA
    exact Set.mem_singleton_iff.mp hmemA
  have hom3 : omegaListN V [u0, u1, v, w] 3 = e [u0, u1, v, w] := ha3.trans hea.symm
  have hom2 : omegaListN V [u0, u1, v, w] 2 = e [u0, u1, v, w] :=
    (hcon [u0, u1, v, w] hb0 htr0).trans hom3
  have hset3 : ({omegaListN V [u0, u1, v, w] 1, omegaListN V [u0, u1, v, w] 2,
      circumcenter (setOfList [u0, u1, v, w])} : Set V3) = {p, e [u0, u1, v, w]} := by
    rw [hom1, hom2, ← ha2, hea]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset3, convexHull_pair] at hTm
  obtain ⟨t1, t2, ht1, ht2, hsum, hxe⟩ := hTm
  have hup : u = t2 • (e [u0, u1, v, w] - p) := by
    have ht1e : t1 = 1 - t2 := by linarith
    have hxe1 : t1 • p + t2 • e [u0, u1, v, w] = p + u := hxe
    rw [ht1e] at hxe1
    have hxe2 : (((1 - t2 : ℝ)) • p + t2 • e [u0, u1, v, w] : V3)
        = p + t2 • (e [u0, u1, v, w] - p) := by module
    rw [hxe2] at hxe1
    exact (add_left_cancel_iff.mp hxe1).symm
  have ht2pos : 0 < t2 := by
    rcases eq_or_lt_of_le ht2 with h | h
    · rw [show t2 = 0 from h.symm, zero_smul] at hup
      exact absurd hup hune
    · exact h
  rcases eq_or_ne (e [u0, u1, v, w]) p with hcc | hcc
  · rw [hcc, sub_self, smul_zero] at hup
    exact absurd hup hune
  · exact hesc (e [u0, u1, v, w] - p)
      ⟨[u0, u1, v, w], ⟨⟨hb0, htr0⟩, hcc⟩, rfl⟩ t2 ht2pos hup

/-- **情形 B2 全支**（capstone 的 `r₄ ≥ √2 ∧ r₃ ≥ √2` 分支，capstone 形，
2026-10-12 第五波收口——支级装配零缺口）：
(1) 泛具子情形（ω₂ ≠ ω₃）：X := `mcell 2 V vl`，`p24_caseB2_general` 全真证；
(2) 退化子情形（ω₂ = ω₃）：本叶平坦，**换叶**——`p24_nondeg_leaf_exists`
  （本波真证，支撑面引理的等效路线）给出非退化新叶 `vl'`，按 `hl vl'` 与
  `hl (truncateSimplex 2 vl')` 三分装配：A 支 `p24_caseA_branch`、
  B3′ 支 `p24_caseB3_branch`、B2′ 支 `p24_caseB2_general`（新叶非退化），
  三支全部真证。两子情形的 mcellSet/edgeX/非平坦细节见各分支件 docstring。 -/

private theorem p24_caseB2_branch (V : Set V3) (u0 u1 : V3) (vl : List V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hbar : barV V 3 vl) (htr : truncateSimplex 1 vl = [u0, u1])
    (hd8 : dist u0 u1 < Real.sqrt 8)
    (hr4 : Real.sqrt 2 ≤ hl vl)
    (hr3 : Real.sqrt 2 ≤ hl (truncateSimplex 2 vl)) :
    ∃ X : Set V3, X ∈ mcellSet V ∧ ({u0, u1} : Set V3) ∈ edgeX V X ∧
      ∀ q : V3, ¬ Collinear3 u0 u1 q →
        ¬ ((X : Set V3) ⊆ {z : V3 | azim u0 u1 q z = 0}) := by
  by_cases hw23 : omegaListN V vl 2 = omegaListN V vl 3
  · -- 退化支：换叶（饱和 packing 短棱处必存在非退化叶），按新叶三分支装配
    obtain ⟨vl', hbar', htr', hne23⟩ :=
      p24_nondeg_leaf_exists V u0 u1 hs hp hu0 hu1 hne hd8
    by_cases hr4' : hl vl' < Real.sqrt 2
    · exact p24_caseA_branch V u0 u1 vl' hs hp hu0 hu1 hne hbar' htr' hr4'
    · rw [not_lt] at hr4'
      by_cases hr3' : hl (truncateSimplex 2 vl') < Real.sqrt 2
      · exact p24_caseB3_branch V u0 u1 vl' hs hp hu0 hu1 hne hbar' htr' hd8 hr4' hr3'
      · rw [not_lt] at hr3'
        exact p24_caseB2_general V u0 u1 vl' hs hp hu0 hu1 hne hbar' htr' hd8 hr4' hr3'
          hne23
  · exact p24_caseB2_general V u0 u1 vl hs hp hu0 hu1 hne hbar htr hd8 hr4 hr3 hw23


/-- （(β) 支独立存在性引理——**本件已全真证**，2026-10-12 第五波随 B2 支
收口；HL OXLZLEZ3 `FCHKUGT`/`EWYBJUA` 叶胞链的对应物，
PA18:2159/:2532 有同名孪生（ported 残件形态）——下游合并时二取一）：
饱和 packing 的短棱 `u0u1`（`d < 2√2`）处存在以 `e = {u0,u1}` 为边的
mcell，且它不落在任一过轴平坦半平面 `{z | azim u0 u1 q z = 0}`（`q` 过轴
外任一点）内。
装配（本波真证落地，见上方第三波件群）：`p24_leaf_exists_sqrt8` 抽叶三元组
`vl`（`barV V 3 vl ∧ truncateSimplex 1 vl = [u0,u1]`）；按 `r₄ := hl vl` 与
`r₃ := hl (truncateSimplex 2 vl)` 三分：
• 情形 A（`r₄ < √2`）：`p24_caseA_branch`——X := `mcell 4 V vl`（四点凸包；
  `mcell` 分派 + barV 给 mcellSet 成员），edgeX 经 `p24_caseA_edgeX`
  （正体积工具 ⇒ 非 nullSet + HDTFNFZ 的 `VX = V ∩ X`），非平坦经
  `p24_caseA_coplanar_false`（W-楔代数收口，2026-10-11 波）+
  `coplanarAzimEq`。全真证；
• 情形 B3（`r₄ ≥ √2 ∧ r₃ < √2`）：`p24_caseB3_branch`——X :=
  `mcell 3 V vl`（三角形截断凸包 ∪ {mxi}），edgeX 经 `p24_caseB3_edgeX`
  （`p24_caseB3_aux` 的 `mxi ∉ affineSpan {u0,u1,v}` + 正体积），非平坦经
  `p24_caseB3_not_flat`（azim 零水平集传输）。真证；唯一 sorried 上游输入
  为 PA2 `MXI_EXISTS_concl`（见 `p24_caseB3_aux` docstring 记账）；
• 情形 B2（`r₄ ≥ √2 ∧ r₃ ≥ √2`）：候选胞 X := `mcell 2 V vl`。第四波
  （2026-10-12）侦察纠错：原记「`mxi ∈ X` 由 `dist(u0,mxi) = √2`」所依
  赖的 PA2 `MXI_EXISTS_concl` 在 B2 支为**假**（HL `MXI_EXPLICIT` 仅为
  B3 支定理，欠 `r₃ < √2` 假设；B2 中 `mxi = ω₂` 且
  `dist(u0,ω₂)² = r₃² + ‖ω₂−cc‖²` 一般 > 2）；修正路线（泛具子情形 ω₂ ≠
  ω₃ 的近轴双楔四点凸包 + 退化子情形 ω₂ = ω₃ 的支撑面换叶）与真证
  结构件记档于第四波 docstring。装配经 `p24_caseB2_branch`——第五波
  （2026-10-12）已两支闭合（退化支经换叶主件 `p24_nondeg_leaf_exists`，
  真证）。
本件本体随 B2 支收口而全真证；`p24_REUHADY_nondeg_azim` 随之零编辑
闭合（(α) 支已由 `p24_nondeg_azim_ne` 真证收口）。 -/
private theorem p24_exists_mcell_not_flat (V : Set V3) (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hd8 : dist u0 u1 < Real.sqrt 8) :
    ∃ X : Set V3, X ∈ mcellSet V ∧ ({u0, u1} : Set V3) ∈ edgeX V X ∧
      ∀ q : V3, ¬ Collinear3 u0 u1 q →
        ¬ ((X : Set V3) ⊆ {z : V3 | azim u0 u1 q z = 0}) := by
  obtain ⟨vl, hbar, htr⟩ := p24_leaf_exists_sqrt8 V u0 u1 hs hp hu0 hu1 hne hd8
  by_cases hr4 : hl vl < Real.sqrt 2
  · exact p24_caseA_branch V u0 u1 vl hs hp hu0 hu1 hne hbar htr hr4
  · rw [not_lt] at hr4
    by_cases hr3 : hl (truncateSimplex 2 vl) < Real.sqrt 2
    · exact p24_caseB3_branch V u0 u1 vl hs hp hu0 hu1 hne hbar htr hd8 hr4 hr3
    · rw [not_lt] at hr3
      -- 情形 B2（r₄ ≥ √2 ∧ r₃ ≥ √2）：X := mcell 2 V vl；泛具/退化两子
      -- 情形装配 = precisely-scoped 残余缺口（p24_caseB2_branch 记账）。
      exact p24_caseB2_branch V u0 u1 vl hs hp hu0 hu1 hne hbar htr hd8 hr4 hr3

/-- capstone 退化支排除（2026-10-08/09 波两支收口，本件本体真证——文件级
`sorry` 零：`(β)` 支独立存在性引理 `p24_exists_mcell_not_flat` 已于
2026-10-10..12 波全真证（公理面残余 taint 仅经上游 PA2/PA10/PA11 接口桩
传入，PA24 侧零 `sorry` 项）；HL OXLZLEZ3 `FCHKUGT`/`EWYBJUA` 对应物，
PA18:2159/:2532 有同名 `ported sorry` 孪生）：capstone 假设组下
`azim u0 u1 v1 v2 ≠ 0`。
(α) `v1 ≠ v2` 支——GENUINE（2026-10-08/09 波）：`azim = 0` 经
`azim_eq_zero_iff` + `affGt_pair_iff` 给出 `v1 − u0 = c•(v2 − u0) + k•(u1 − u0)`
（`c > 0`，同一垂线射线）；`p24_tri_gamma` 给出每三角形的坐标数据
`(h_i, t_i, w_i)`（垂距、轴坐标、外心垂坐标积）与其 γ 关系
`2w_ih_i = h_i² + t_i² − d·t_i`；盘界（`dist(v_i, q)² = 2 − 2h_i(β − w_i)`，
`q` = 中点沿垂线上移 `β = √(2 − d²/4)`）+ 锥界（packing 距 `u0,u1 ≥ 2` 推出
`|t_i − d/2| < 2β(h_i − β)/d`）拼合得 `dist v1 v2 < 2`，与 packing 矛盾
（`p24_nondeg_azim_ne`，真证）。
(β) `v1 = v2` 支——两闭楔同为平坦半平面
`wedgeGe u0 u1 v v = {z | azim u0 u1 v z = 0}`，`heX` 把所有以 `e` 为边的胞
压进该半平面，与独立存在性引理 `p24_exists_mcell_not_flat`（上方，真证
——饱和 packing 短棱处存在以 `e` 为边、不落在任一过轴平坦半平面内的
mcell）相抵。 -/
private theorem p24_REUHADY_nondeg_azim (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3)
    (v1 v2 : V3) (e : Set V3) (hs : saturated V) (hp : Packing V)
    (hdist : dist u0 u1 < Real.sqrt 8) (he : e = {u0, u1})
    (hhl1 : hl vl1 < Real.sqrt 2) (hhl2 : hl vl2 < Real.sqrt 2)
    (hbar1 : barV V 2 vl1) (hbar2 : barV V 2 vl2)
    (htr1 : setOfList (truncateSimplex 1 vl1) = e)
    (htr2 : setOfList (truncateSimplex 1 vl2) = e)
    (hv1 : v1 = elV vl1 2) (hv2 : v2 = elV vl2 2)
    (heX : ∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) :
    azim u0 u1 v1 v2 ≠ 0 := by
  by_cases hv12 : v1 = v2
  · -- (β) 支：`v1 = v2` 使两闭楔同为平坦半平面，heX 把所有以 e 为边的胞
    --   压进该半平面，与 `p24_exists_mcell_not_flat` 的非平坦胞存在性相抵。
    exfalso
    have htr1' : setOfList (truncateSimplex 1 vl1) = ({u0, u1} : Set V3) := by
      rw [htr1, he]
    obtain ⟨hu0V, hu1V, hnc1⟩ := p24_REUHADY_extract hp hbar1 htr1' hv1
    have hu01 : u0 ≠ u1 := by
      intro hcon
      rw [hcon] at hnc1
      exact hnc1 (collinear3_of_eq rfl)
    obtain ⟨X, hXm, hXe, hXnf⟩ :=
      p24_exists_mcell_not_flat V u0 u1 hs hp hu0V hu1V hu01 hdist
    have hXe' : e ∈ edgeX V X := by rw [he]; exact hXe
    rcases heX X ⟨hXm, hXe'⟩ with hw | hw
    · refine hXnf v1 hnc1 ?_
      rw [hv12] at hw
      intro z hz
      have ha := hw hz
      simp only [wedgeGe, Set.mem_setOf_eq] at ha ⊢
      rw [hv12]
      exact le_antisymm (ha.2.trans (by rw [azim_self])) ha.1
    · refine hXnf v1 hnc1 ?_
      rw [← hv12] at hw
      intro z hz
      have ha := hw hz
      simp only [wedgeGe, Set.mem_setOf_eq] at ha ⊢
      exact le_antisymm (ha.2.trans (by rw [azim_self])) ha.1
  · -- (α) 支：`v1 ≠ v2` 纯度量排除（p24_nondeg_azim_ne 主装配，真证）
    intro haz
    have htr1' : setOfList (truncateSimplex 1 vl1) = ({u0, u1} : Set V3) := by
      rw [htr1, he]
    have htr2' : setOfList (truncateSimplex 1 vl2) = ({u0, u1} : Set V3) := by
      rw [htr2, he]
    obtain ⟨hu0V, hu1V, hnc1⟩ := p24_REUHADY_extract hp hbar1 htr1' hv1
    obtain ⟨-, -, hnc2⟩ := p24_REUHADY_extract hp hbar2 htr2' hv2
    have hv1V : v1 ∈ V := by
      have hvn : voronoiNondg V vl1 := hbar1.2 vl1
        ⟨⟨[], by rw [List.append_nil]⟩, by have := hbar1.1; omega⟩
      rw [hv1]
      exact hvn.2.1 (p24_elV_mem (by have := hbar1.1; omega))
    have hv2V : v2 ∈ V := by
      have hvn : voronoiNondg V vl2 := hbar2.2 vl2
        ⟨⟨[], by rw [List.append_nil]⟩, by have := hbar2.1; omega⟩
      rw [hv2]
      exact hvn.2.1 (p24_elV_mem (by have := hbar2.1; omega))
    have hrad1' : radV ({u0, u1, v1} : Set V3) < Real.sqrt 2 := by
      have hset1 := p24_setOfList_pair2 hbar1 htr1' hv1
      have he' : hl vl1 = radV (setOfList vl1) := rfl
      rwa [he', hset1] at hhl1
    have hrad2' : radV ({u0, u1, v2} : Set V3) < Real.sqrt 2 := by
      have hset2 := p24_setOfList_pair2 hbar2 htr2' hv2
      have he' : hl vl2 = radV (setOfList vl2) := rfl
      rwa [he', hset2] at hhl2
    exact p24_nondeg_azim_ne hs hp hu0V hu1V hv1V hv2V hnc1 hnc2 hdist
      hrad1' hrad2' hv12 haz

/-- capstone 退化支排除（2026-10-08 波拆分）：`vl1 ≠ vl2` 已真证——
`vl1 = vl2` 强制 `v1 = v2`（`hv1`/`hv2`），而 `azim u0 u1 v1 v1 = 0`
（`azim_self`），与残件 `p24_REUHADY_nondeg_azim` 相抵；本件的唯一残余
缺口即方位角排除一件（2026-10-08 进一步收窄为 `p24_nondeg_azim_ne` +
`p24_exists_mcell_not_flat` 两支，见 `p24_REUHADY_nondeg_azim` docstring
的 (α)/(β) 记账；坐标工具链已真证落盘）。PA18:2159/:2532 的
`FCHKUGT`/`EWYBJUA` 同名孪生仍为 `ported sorry`；本件的两支收口中
(α) 支已真证（`p24_nondeg_azim_ne`），(β) 支 `p24_exists_mcell_not_flat`
亦已真证（2026-10-10..12 波）——本件两支零缺口、PA24 侧零 `sorry` 项。 -/
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
  have haz := p24_REUHADY_nondeg_azim V u0 u1 vl1 vl2 v1 v2 e hs hp hdist he
    hhl1 hhl2 hbar1 hbar2 htr1 htr2 hv1 hv2 heX
  refine ⟨haz, fun hcon => ?_⟩
  have hvv : v2 = v1 := by rw [hv2, hv1, hcon]
  rw [hvv] at haz
  exact haz (azim_self u0 u1 v1)

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
  • `azim u0 u1 v1 v2 ≠ 0` + `vl1 ≠ vl2` — `p24_REUHADY_nondeg`
    (2026-10-08 split: `vl1 ≠ vl2` is GENUINE via `azim_self`; the
    residual is the pure azimuth exclusion `p24_REUHADY_nondeg_azim`,
    the OXLZLEZ3 `FCHKUGT`/`EWYBJUA` leaf-cell chain; note this
    statement's `azim ≠ 0` hypothesis is about FREE points `w1 w2`, so it
    yields `u0 ≠ u1` only).
REMAINING file-level `sorry` input: `REUHADY1` (giant) only —
`p24_exists_mcell_not_flat` (the (β) `v1 = v2` non-flat-cell existence)
is GENUINE since the 2026-10-10..12 waves.
The (α) `v1 ≠ v2` azimuth exclusion `p24_nondeg_azim_ne` is GENUINE
(2026-10-08/09 wave; the shim `p24_REUHADY_nondeg_azim` is wired to it).
When `REUHADY1`'s (d) body lands, each capstone closes with zero further
edits. -/
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
`vl1 ≠ vl2` come from `p24_REUHADY_nondeg` (2026-10-08 split: `vl1 ≠ vl2`
genuine via `azim_self`; the `azim ≠ 0` residual `p24_REUHADY_nondeg_azim`
is NOT derivable from the visible hypotheses: at `azim = 0` the
wedge-intersection hypothesis degenerates to a trivial half-plane
inclusion — the exclusion is the OXLZLEZ3 `FCHKUGT`/`EWYBJUA`
leaf-cell chain, see `p24_wedgeGe_flat_subset` for the flat degeneration).
REMAINING file-level `sorry` input: `REUHADY1` (giant) only —
`p24_exists_mcell_not_flat` (the (β) `v1 = v2` non-flat-cell existence)
is GENUINE since the 2026-10-10..12 waves.
The (α) `v1 ≠ v2` azimuth exclusion `p24_nondeg_azim_ne` is GENUINE
(2026-10-08/09 wave; the shim `p24_REUHADY_nondeg_azim` is wired to it).
When `REUHADY1`'s (d) body lands, each capstone closes with zero further
edits. -/
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
statement, verbatim. Formerly the PackingConcl discharge path
(`GRUTOTI1_concl_discharged` routed through this name, since the
`private` modifier hides the original from every other module); since
2026-10-12 PackingConcl discharges via `PackingAuto23.GRUTOTI` instead,
so this twin is consumer-free. Kept in place because the EV20
duplicate-provision precondition does not hold (PA23's provider is named
`GRUTOTI`, and the set-builder binder here carries an explicit
`: Set V3` ascription) — delete at merge into Auto23's results once the
name/binder mismatch is ruled on. -/
theorem GRUTOTI1_concl_p24_pub : ∀ (V : Set V3) (u0 u1 : V3) (e : Set V3),
    saturated V → Packing V → u0 ∈ V → u1 ∈ V → u0 ≠ u1 →
    hl [u0, u1] < Real.sqrt 2 → e = {u0, u1} →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X}
        (fun t => dihX V t (u0, u1)) = 2 * Real.pi :=
  GRUTOTI1_concl_p24


end Kepler.Text
