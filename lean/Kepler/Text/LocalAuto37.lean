/-
LocalAuto37 — port of `scripts/local/lunar_deform.hl` (5039 ln, module
`Lunar_deform`, Nguyen Quang Truong / T. Hales 2013; 0 defs + 48 theorems):
the MHAEYJN *deformation* bank of the Local Fan chapter.  The file proves
that a lunar (two-half) convex local fan survives a small deformation
`f : V3 → ℝ → V3` that moves only the apex `u` inside the plane
`aff {0, v, w, u}`:

  * geometry localisation kit: `aff_gt` subset/`azim` lemmas
    (`AFF_GT_SUBSET_AFFINE_HULL21`, `TOW_POINTS_IN_IMP_AFF_GT_SUBSET`,
    `COLL_IN_AFF_GT_INTER_EMPTY`, `AZIM_PI_LEMMA`, `IN_AFF_GT_IMP_AZIMEQ*`),
    the lunar two-half characterisation (`HKIRPEP_ALT`,
    `LUNAR_IMP_IN_TWO_HAFLS_PLANE`, `LOCAL_CONVEX_NOT_COLLINEAR`);
  * the `SUB_LUNAR_DEFORM_LEMMA` giant (528-1830: `Lunar` survives the
    deformation) and its `ConvexLocalFan` wrapper `MHAEYJN_CONVEX_LOCAL_FAN`;
  * the hypermap-iso kit (darts/`ff_of`/`nn_of`/`ee_of` transfer under a
    vertex bijection: `ORD_PAIRS_INJ_IMAGE`, `BIJ_AND_MAP_COMM`,
    `NODE_EDGE_COMM_LEMMA`, `HYP_ISO_LEMMAA`, `IMAGE_FACE_F`, `ITER_COMM*`,
    `HAS_THE_SAME_ORD_LEM`, `HYP_ISO_DIH2K_PRESERVED`);
  * continuity-at-`atreal` preservation kit (`CONS_IMP_CONTINUOUS_ATREAL`,
    `DISJTINCT_PROPERTY`, `CONT_ATREAL_INJ_PRESERVED`,
    `CONT_ATREAL_REAL_CONTS`, `CONTINUOUS_POS_PRES`);
  * the iterated `rho_node1` plane/cross kit (`IVS_RHO_NODE_V_IN_FF`,
    `CROSS_IN_SAME_DIRECTION`, `ITER_CROSS_SAME_DIRECTION`,
    `ITER_IN_AFF_GT_2_1`, `AZIM_PI_ITER_LOCAL_FAN`);
  * the registry conclusion `MHAEYJN`.

ALIGNMENT (twin policy): `LocalAuto34` carries `MHAEYJN_prop_p34` (the
`real_interval (a,b)` ↔ `Icc a b` rendering of appendix.hl:25), but the
LocalAuto34 olean is NOT built in this checkout (same-wave lanes are
mutually non-imported), so alignment is not reachable here.  We therefore
carry the verbatim `_p37` copy `MHAEYJN_prop_p37` with a NEEDS marker to
merge against `MHAEYJN_prop_p34` at the LocalAuto34 merge point.

Encoding (house conventions, cf. LocalAuto31/34):
- HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `(0 : V3)`; `&0` ↔ `(0:ℝ)`;
  `#` rationals ↔ exact literals; `real_interval (a,b)` ↔ `Set.Icc a b`;
  `--e` ↔ `-e`; `!`/`?` ↔ `∀`/`∃`; `x IN s` ↔ `x ∈ s`; `A SUBSET B` ↔ `A ⊆ B`;
  `IMAGE f s` ↔ `f '' s`; `~(a = b)` ↔ `a ≠ b`; `DISJOINT s t` ↔ `Disjoint s t`;
  `ITER i f x` ↔ `f^[i] x` (`Function.iterate`); `POWER n f x` likewise.
- `convex_local_fan`/`local_fan`/`lunar`/`deformation`/`interior_angle1`/
  `rho_node1`/`ivs_rho_node1` ↔ `ConvexLocalFan`/`LocalFan`/`Lunar`/
  `Deformation`/`interiorAngle1`/`rhoNode1`/`ivsRhoNode1` (LocalAuto1; the
  registry `LocalFan` is the stub `True` there, so `LocalFan`-conditioned
  statements keep the hypothesis for signature fidelity and theorems whose
  proof needs fan substance are `sorry` — see NEEDS markers).
- `aff_gt`/`aff_lt` ↔ `affGt`/`affLt` (Geom.Aff `Affsign` rendering);
  `aff {a,b}` ↔ `affineSpan ℝ ({a, b} : Set V3)`; `collinear {a,b,c}` ↔
  `Collinear ℝ ({a, b, c} : Set V3)`; `azim` ↔ `Kepler.Geom.azim`.
- `x cross y` ↔ `cross3_p37` (verbatim copy of the shared `cross3`; see the
  def comment — the PackingAuto18/PackingAuto20 `atn2PA18` conflict that
  forced the copy is resolved (atn2-merge wave 3 single-sourced it into
  `SphereKit`; la35-access-recon-w1 ruling, 2026-10-28); the copy is kept
  for diff stability);
  `x dot y` ↔ `⬝ᵥ` after coercion to `Fin 3 → ℝ`; `norm` ↔ `‖·‖`.
- HOL `f continuous atreal r` ↔ `ContinuousAt f r` for point-`atreal`
  statements (LocalAuto6/14 convention).  EXCEPTION, documented: in
  `CONS_IMP_CONTINUOUS_ATREAL` the source unfolds `continuous_atreal`
  *against* the ambient `real_interval (a,b)` (its HOL proof rewrites both),
  i.e. the conclusion is continuity *within* the interval; we therefore
  render that single conclusion as `ContinuousWithinAt f t (Icc a b)`.
- `plane P` (Collect_geom) ↔ `PlaneP_p37 P` := `∃ a b c, ¬Collinear ℝ {a,b,c}
  ∧ P = affineSpan ℝ {a,b,c}`.  NEEDS: verify against the azure `plane`
  definition before merging.
- `hyp_iso f (H,HH)` (Hypermap_iso) ↔ `hypIso_p37 f H HH` := dart `BijOn` +
  commuting face/node/edge maps (shape follows the consumer lemmas of this
  file).  NEEDS: verbatim check against `hypermap_iso.hl`; the
  `hypermap (HYP (vec 0,V,E))` instances go through `hypermapOfFan`
  (Fan.lean), kept explicit as `FAN` hypotheses at the skeleton level.
- `{ITER l (rho_node1 FF) v | 0 < l /\ l < i}` ↔ `{z | ∃ l, 0 < l ∧ l < i ∧
  z = (rhoNode1 FF)^[l] v}`; `CARD V` ↔ `Set.ncard V`; `dih2k H k` ↔
  `dih2k_p2 H k` (LocalAuto2); `darts_of_hyp`/`ff_of_hyp`/`nn_of_hyp`/
  `ee_of_hyp`/`face`/`ord_pairs` ↔ the `*_p4` twins (LocalAuto4/5).
- TACTIC-HELPER NON-PORT.  The OCaml block `ATTACH`…`MAKE_FIRST_TAC`
  (source lines 33-89: `NHANH`/`PHA`/`DOWN_TAC`/`PAT_*_REWRITE_TAC`/…
  hypothesis-shuffling tactics) and the debug `els`/`bls` carry no
  mathematical content and are deliberately NOT ported; their effect is
  folded into the direct proofs below.  The mid-file `let tt = GEN_ALL …`
  bindings are HOL proof-script scoping (ISPECL instantiations inside
  tactic blocks), likewise folded.
- DISCHARGES (2026-09-20, +3 sorries filled, 1 error fixed; 0 errors,
  27 remaining): `HAS_THE_SAME_ORD_LEM_p37` (iterate conjugation + minimality
  transfer via the dart `BijOn`), `HYP_ISO_DIH2K_PRESERVED_p37` (card via
  `BijOn`/`ncard`, face-union via `IMAGE_FACE_F_p37` + node-map commutation,
  orders via `HAS_THE_SAME_ORD_LEM_p37`), `AFF_LT_SUBSET_AFF11_p37`
  (Affsign coefficient sum = lineMap parametrisation).  `XRECQNS_UPDATE_p37`
  reverted to an honest `sorry` (the registry `LocalFan` upgrade made its old
  `trivial` proof invalid; blocked on `Deformation.XRECQNS`).  The giants
  (`SUB_LUNAR_DEFORM_LEMMA`, `MHAEYJN_CONVEX_LOCAL_FAN`, `MHAEYJN` and the
  lunar characterisation chain) are `sorry` with NEEDS markers naming the
  blocking kit.  UPDATE (w5cB5/w5cB6 waves, 2026-11-04): the LocalAuto5
  fan-rho substance kit (`RHO_NODE_SET_IN_A_PLANE_IMP_POS_DIRECT`,
  `LOCAL_FAN_RHO_NODE_PROS/PROS2`, `DETER_RHO_NODE`, `LOFA_IN_E_IMP_IN_FF`,
  `LOCAL_FAN_CHARACTER_OF_RHO_NODE2` ...) is now PROVED and is consumed here
  through the AzimBridge `localFanEquiv_p35` registry bridge (five items
  closed at w5cB5, the plane/cross chain at w5cB6).  Still sorried twins:
  LocalAuto6 `CARD_V_TWO_HAFL_CIRCLE` (HKIRPEP chain) and
  `LOCAL_FAN_CHARACTER_OF_RHO_NODE3` (nowhere materialised).  UPDATE
  (w5cB10 wave, 2026-11-04): the hypermap-iso kit (`BIJ_AND_MAP_COMM`,
  `NODE_EDGE_COMM_LEMMA`, `HYP_ISO_LEMMAA`) is now PROVED (standard
  three, via the local-fan two-point neighbour sets); `XRECQNS_UPDATE`
  remains blocked on the unported `Deformation.XRECQNS` fan-transfer
  tower (LocalAuto17 `XRECQNS_p17` / `FAN7_SMALL_DEFORMATION_p17` and
  LocalAuto2 `ALL_TO_THE_NONPARALLEL_PART_ALT` are still `sorry`).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto4
import Kepler.Text.AzimBridge
import Kepler.Text.LocalAuto5
import Kepler.Text.LocalAuto17
import Kepler.Text.LocalAuto6
import Kepler.Text.PlanarityAngle
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

-- LA2/LA3 的 `dartDecEq2`/`dartDecEq3`（DecidableEq (V3×V3) 的非可计算实例）
-- 会改变本文件既有净证的实例解析（`faceMap_mem_iter_p37` 实测被破坏：
-- synthesis 出 `dartDecEq3` 而冻结态 inferred `instDecidableEqProd`）；
-- 本文件冻结态按旧解析 elaborate，故在本地摘除（须置于 namespace/open 之后）。
attribute [-instance] dartDecEq2 dartDecEq3

/-! ## Local twin defs (`_p37` copies) -/

/-- HOL `u cross v` on `real^3` — verbatim copy of the shared
`PackingAuto18.cross3` / `TopologyFan.cross3` body.  WHY A COPY (historic):
this file imports `LocalAuto1`, whose tree loads `PackingAuto18`; the
same-wave `LocalAuto2`/`LocalAuto9` trees load `PackingAuto20`, and the two
used to declare conflicting `Kepler.Text.atn2PA18` copies.  RESOLVED:
atn2-merge wave 3 single-sourced `atn2` into `SphereKit`, the clash does not
exist and the trees coexist (la35-access-recon-w1 ruling, 2026-10-28).
NOTE: switching to the shared `cross3` is now a plain refactor (no shadowing
left to merge); the local copy is kept for diff stability. -/
noncomputable def cross3_p37 (a b : V3) : V3 :=
  WithLp.toLp 2 (crossProduct ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ))

/-- HOL `has_orders h k` (localization.hl:24; `LocalAuto2.hasOrders_p2`
copy — LocalAuto2 is not importable here, see `cross3_p37`).
NEEDS: merge with `hasOrders_p2`. -/
def hasOrders_p37 {α : Type*} (f : α → α) (k : ℕ) : Prop :=
  (∀ i, 0 < i → i < k → ¬(f^[i] = id)) ∧ f^[k] = id

/-- HOL `dih2k H k` (localization.hl:30; `LocalAuto2.dih2k_p2` copy).
NEEDS: merge with `dih2k_p2`. -/
def dih2k_p37 {α : Type*} [DecidableEq α] (H : Hypermap α) (k : ℕ) : Prop :=
  H.darts.card = 2 * k ∧
    (∀ x ∈ (H.darts : Set α), (↑H.darts : Set α) = H.face x ∪ (H.nodeMap : α → α) '' H.face x) ∧
    hasOrders_p37 (H.faceMap : α → α) k ∧
    hasOrders_p37 (H.edgeMap : α → α) 2 ∧
    hasOrders_p37 (H.nodeMap : α → α) 2

/-! ## Geometric localisation kit (source 109-527) -/

/-- HOL `CONS_IMP_CONTINUOUS_ATREAL` (lunar_deform.hl:109).  The `atreal`
continuity is rendered *within* the ambient interval (see header): the
source proof unfolds `continuous_atreal` against `real_interval (a,b)`. -/
theorem CONS_IMP_CONTINUOUS_ATREAL_p37 {a b : ℝ} {f : ℝ → V3} {u : V3}
    (h : ∀ t ∈ Icc a b, f t = u) :
    ∀ t ∈ Icc a b, ContinuousWithinAt f (Icc a b) t := by
  intro t ht
  exact (continuous_const.continuousWithinAt).congr (fun y hy => h y hy) (h t ht)

/-! ## w5cB2 kit (W5c-B 第二波): `Affsign` coefficient bookkeeping -/

/-- 实数左消去（ℝ-模上 `s • p = s • q → p = q`）。 -/
private theorem w5cB_smul_left_cancel {s : ℝ} (hs : s ≠ 0) {p q : V3} (h : s • p = s • q) :
    p = q := by
  have h2 : s • (p - q) = (0 : V3) := by rw [smul_sub, h, sub_self]
  rcases smul_eq_zero.mp h2 with h' | h'
  · exact absurd h' hs
  · exact sub_eq_zero.mp h'

private theorem w5cB_evsub (z w : V3) : z -ᵥ w = z - w := rfl

private theorem w5cB_evadd (p v : V3) : p +ᵥ v = p + v := rfl

/-- 三槽存在形：finset 元素都落在 `{u, v, w}` 时，和可拆成三系数形。 -/
private theorem w5cB_finset3_sum (u v w : V3) {F : Finset V3} {c : V3 → ℝ}
    (hF : ∀ x ∈ F, x = u ∨ x = v ∨ x = w) :
    ∃ t1 t2 t3 : ℝ, (∑ x ∈ F, c x • x) = t1 • u + t2 • v + t3 • w ∧
      ∑ x ∈ F, c x = t1 + t2 + t3 := by
  classical
  induction F using Finset.induction with
  | empty => exact ⟨0, 0, 0, by simp, by simp⟩
  | insert a F ha ih =>
      obtain ⟨e1, e2, e3, hv, hs⟩ :=
        ih (fun x hx => hF x (Finset.mem_insert_of_mem hx))
      have ha3 := hF a (Finset.mem_insert_self a F)
      rcases ha3 with he | he | he
      · have hca : c a • a = c a • u := by rw [he]
        refine ⟨e1 + c a, e2, e3, ?_, ?_⟩
        · rw [Finset.sum_insert ha, hv, add_smul, hca]
          abel
        · rw [Finset.sum_insert ha]
          linarith
      · have hca : c a • a = c a • v := by rw [he]
        refine ⟨e1, e2 + c a, e3, ?_, ?_⟩
        · rw [Finset.sum_insert ha, hv, add_smul, hca]
          abel
        · rw [Finset.sum_insert ha]
          linarith
      · have hca : c a • a = c a • w := by rw [he]
        refine ⟨e1, e2, e3 + c a, ?_, ?_⟩
        · rw [Finset.sum_insert ha, hv, add_smul, hca]
          abel
        · rw [Finset.sum_insert ha]
          linarith

/-- 双点 lineMap 组合：`s • a + t • b`（`s + t ≠ 0`）。 -/
private theorem w5cB_lineMap_pair_smul (a b : V3) {s t : ℝ} (hst : s + t ≠ 0) :
    s • a + t • b = (s + t) • (AffineMap.lineMap a b (t / (s + t))) := by
  have hmd : (s + t) * (t / (s + t)) = t := by
    field_simp
  rw [AffineMap.lineMap_apply, w5cB_evsub, w5cB_evadd, smul_add, smul_smul, hmd, smul_sub]
  module

/-- 三点系数组合入三点仿射包（direction-法，同 LuneVolume 惯例；无需互异）。 -/
private theorem w5cB2_line3_mem {p q r : V3} (a b c : ℝ) (hsum : a + b + c = 1) :
    (a • p + b • q + c • r) ∈ (affineSpan ℝ ({p, q, r} : Set V3) : Set V3) := by
  have hpS : p ∈ affineSpan ℝ ({p, q, r} : Set V3) := mem_affineSpan ℝ (by simp)
  have hqS : q ∈ affineSpan ℝ ({p, q, r} : Set V3) := mem_affineSpan ℝ (by simp)
  have hrS : r ∈ affineSpan ℝ ({p, q, r} : Set V3) := mem_affineSpan ℝ (by simp)
  have hd3 : b • (q - p) ∈ (affineSpan ℝ ({p, q, r} : Set V3)).direction :=
    Submodule.smul_mem _ b (AffineSubspace.vsub_mem_direction hqS hpS)
  have hd4 : c • (r - p) ∈ (affineSpan ℝ ({p, q, r} : Set V3)).direction :=
    Submodule.smul_mem _ c (AffineSubspace.vsub_mem_direction hrS hpS)
  have hd5 : b • (q - p) + c • (r - p) ∈ (affineSpan ℝ ({p, q, r} : Set V3)).direction :=
    Submodule.add_mem _ hd3 hd4
  have hval2 : (a • p + b • q + c • r) -ᵥ p = b • (q - p) + c • (r - p) := by
    rw [w5cB_evsub, show a = 1 - b - c from by linarith, sub_smul, sub_smul]
    module
  rw [← vsub_vadd (a • p + b • q + c • r) p, hval2]
  exact AffineSubspace.vadd_mem_of_mem_direction hd5 hpS

/-- 三点系数和为 1 的组合落在三点仿射包内。 -/
private theorem w5cB_affine3_mem_affineSpan (u v w : V3) (t1 t2 t3 : ℝ)
    (hsum : t1 + t2 + t3 = 1) :
    (t1 • u + t2 • v + t3 • w) ∈ (affineSpan ℝ ({u, v, w} : Set V3) : Set V3) :=
  w5cB2_line3_mem t1 t2 t3 hsum

/-- 三点并集（两基点 + 一锥点）的 toFinset 标量和分解。 -/
private theorem w5cB2_pus3_sum {f : V3 → ℝ} {a b c : V3} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hfin : ({a, b} ∪ {c} : Set V3).Finite) :
    ∑ w ∈ hfin.toFinset, f w = f a + f b + f c := by
  have h3 : hfin.toFinset = ({a, b, c} : Finset V3) := by
    apply Finset.ext
    intro w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [h3, Finset.sum_insert (by simp [hab, Ne.symm hca]),
    Finset.sum_insert (by simp [Ne.symm hcb]), Finset.sum_singleton]
  ring

/-- 三点并集（两基点 + 一锥点）的 toFinset 向量和分解。 -/
private theorem w5cB2_pus3_v {f : V3 → ℝ} {a b c : V3} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hfin : ({a, b} ∪ {c} : Set V3).Finite) :
    ∑ w ∈ hfin.toFinset, f w • w = f a • a + f b • b + f c • c := by
  have h3 : hfin.toFinset = ({a, b, c} : Finset V3) := by
    apply Finset.ext
    intro w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [h3, Finset.sum_insert (by simp [hab, Ne.symm hca]),
    Finset.sum_insert (by simp [Ne.symm hcb]), Finset.sum_singleton]
  abel

/-- `affGt {x} {u, v}` 的三系数形（AFF_GT_1_2 提取向）。 -/
private theorem w5cB_affGt_1_2_mp {x u v z : V3} (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v)
    (h : z ∈ affGt {x} {u, v}) :
    ∃ t1 t2 t3 : ℝ, 0 < t2 ∧ 0 < t3 ∧ t1 + t2 + t3 = 1 ∧ z = t1 • x + t2 • u + t3 • v := by
  obtain ⟨f, hfin, hsumv, hpos, hone⟩ := h
  refine ⟨f x, f u, f v, hpos u (Set.mem_insert u ({v} : Set V3)),
    hpos v (Set.mem_insert_of_mem u (Set.mem_singleton v)), ?_, ?_⟩
  · rw [sum_insert_pair_s (x := x) (v := u) (u := v) hfin hxu hxv huv] at hone
    linarith
  · rw [sum_insert_pair_v (x := x) (v := u) (u := v) hfin hxu hxv huv] at hsumv
    rw [hsumv]

/-- 三系数形构造回 `affGt {x} {u, v}`（AFF_GT_1_2 构造向）。 -/
private theorem w5cB_affGt_1_2_mpr {x u v z : V3} (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v)
    {t1 t2 t3 : ℝ} (ht2 : 0 < t2) (ht3 : 0 < t3) (hsum : t1 + t2 + t3 = 1)
    (hz : z = t1 • x + t2 • u + t3 • v) :
    z ∈ affGt {x} {u, v} :=
  Affsign.of_triple (sgn := fun r : ℝ => 0 < r) (x := x) (v := u) (u := v) t2 t3 ht2 ht3
    (by rw [hz, show t1 = 1 - t2 - t3 from by linarith]) hxu hxv huv

/-- `affGt {x, u} {v}` 的三系数形（AFF_GT_2_1 提取向）。 -/
private theorem w5cB_affGt_2_1_mp {x u v z : V3} (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v)
    (h : z ∈ affGt {x, u} {v}) :
    ∃ t1 t2 t3 : ℝ, 0 < t3 ∧ t1 + t2 + t3 = 1 ∧ z = t1 • x + t2 • u + t3 • v := by
  obtain ⟨f, hfin, hsumv, hpos, hone⟩ := h
  refine ⟨f x, f u, f v, hpos v (Set.mem_singleton v), ?_, ?_⟩
  · rw [w5cB2_pus3_sum (a := x) (b := u) (c := v) hxu (Ne.symm hxv) (Ne.symm huv) hfin]
      at hone
    linarith
  · rw [w5cB2_pus3_v (a := x) (b := u) (c := v) hxu (Ne.symm hxv) (Ne.symm huv) hfin]
      at hsumv
    rw [hsumv]

/-- `affGt {x, u} {v}` 的三系数形构造（AFF_GT_2_1 构造向）。 -/
private theorem w5cB_affGt_2_1_mpr {x u v z : V3} (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v)
    {t1 t2 t3 : ℝ} (ht3 : 0 < t3) (hsum : t1 + t2 + t3 = 1)
    (hz : z = t1 • x + t2 • u + t3 • v) :
    z ∈ affGt {x, u} {v} := by
  have hfin : (({x, u} : Set V3) ∪ {v} : Set V3).Finite :=
    ((Set.finite_singleton u).insert x).union (Set.finite_singleton v)
  refine ⟨fun q => if q = v then t3 else if q = u then t2 else t1, hfin, ?_, ?_, ?_⟩
  · rw [w5cB2_pus3_v (a := x) (b := u) (c := v) hxu (Ne.symm hxv) (Ne.symm huv) hfin]
    simp only [if_neg hxv, if_neg hxu, if_neg huv, if_true, hz]
  · intro q hq
    simp only [Set.mem_singleton_iff] at hq
    subst hq
    simp only [if_true]
    exact ht3
  · rw [w5cB2_pus3_sum (a := x) (b := u) (c := v) hxu (Ne.symm hxv) (Ne.symm huv) hfin]
    simp only [if_neg hxv, if_neg hxu, if_neg huv, if_true]
    linarith

/-- `affGt {x} {v}` 的两系数形提取。 -/
private theorem w5cB_affGt_single_mp {x v z : V3} (hxv : x ≠ v)
    (h : z ∈ affGt {x} {v}) :
    ∃ t1 t2 : ℝ, 0 < t2 ∧ t1 + t2 = 1 ∧ z = t1 • x + t2 • v := by
  obtain ⟨f, hfin, hsumv, hpos, hone⟩ := h
  refine ⟨f x, f v, hpos v (Set.mem_singleton v), ?_, ?_⟩
  · rw [sum_insert_single_s hfin hxv] at hone
    linarith
  · rw [sum_insert_single_v hfin hxv] at hsumv
    rw [hsumv]

/-- 两系数形构造回 `affGt {x} {v}`。 -/
private theorem w5cB_affGt_single_mpr {x v z : V3} (hxv : x ≠ v) {t1 t2 : ℝ}
    (ht2 : 0 < t2) (hsum : t1 + t2 = 1) (hz : z = t1 • x + t2 • v) :
    z ∈ affGt {x} {v} := by
  have hfin : (({x} : Set V3) ∪ {v} : Set V3).Finite :=
    (Set.finite_singleton x).union (Set.finite_singleton v)
  refine ⟨fun q => if q = v then t2 else 1 - t2, hfin, ?_, ?_, ?_⟩
  · rw [sum_insert_single_v hfin hxv]
    simp only [if_neg hxv, if_true, hz, show t1 = 1 - t2 from by linarith]
  · intro q hq
    simp only [Set.mem_singleton_iff] at hq
    subst hq
    simp only [if_true]
    exact ht2
  · rw [sum_insert_single_s hfin hxv]
    simp only [if_neg hxv, if_true]
    linarith

/-- `affLt {x} {w}` 的两系数形提取（AFF_LT_1_1 提取向）。 -/
private theorem w5cB_affLt_1_1_mp {x w z : V3} (hxw : x ≠ w)
    (h : z ∈ affLt {x} {w}) :
    ∃ t1 t2 : ℝ, t2 < 0 ∧ t1 + t2 = 1 ∧ z = t1 • x + t2 • w := by
  obtain ⟨f, hfin, hsumv, hpos, hone⟩ := h
  refine ⟨f x, f w, hpos w (Set.mem_singleton w), ?_, ?_⟩
  · rw [sum_insert_single_s hfin hxw] at hone
    linarith
  · rw [sum_insert_single_v hfin hxw] at hsumv
    rw [hsumv]

/-- `affLt {u, v} {a}` 的三系数形提取（AFF_LT_2_1 提取向）。 -/
private theorem w5cB_affLt_2_1_mp {u v a z : V3} (huv : u ≠ v) (hva : v ≠ a) (hua : u ≠ a)
    (h : z ∈ affLt {u, v} {a}) :
    ∃ t1 t2 t3 : ℝ, t3 < 0 ∧ t1 + t2 + t3 = 1 ∧ z = t1 • u + t2 • v + t3 • a := by
  obtain ⟨f, hfin, hsumv, hpos, hone⟩ := h
  refine ⟨f u, f v, f a, hpos a (Set.mem_singleton a), ?_, ?_⟩
  · rw [w5cB2_pus3_sum (a := u) (b := v) (c := a) huv (Ne.symm hua) (Ne.symm hva) hfin]
      at hone
    linarith
  · rw [w5cB2_pus3_v (a := u) (b := v) (c := a) huv (Ne.symm hua) (Ne.symm hva) hfin]
      at hsumv
    rw [hsumv]

/-- 三系数形构造回 `affLt {u, v} {a}`（AFF_LT_2_1 构造向）。 -/
private theorem w5cB_affLt_2_1_mpr {u v a z : V3} (huv : u ≠ v) (hva : v ≠ a) (hua : u ≠ a)
    {t1 t2 t3 : ℝ} (ht3 : t3 < 0) (hsum : t1 + t2 + t3 = 1)
    (hz : z = t1 • u + t2 • v + t3 • a) :
    z ∈ affLt {u, v} {a} := by
  have hfin : (({u, v} : Set V3) ∪ {a} : Set V3).Finite :=
    ((Set.finite_singleton v).insert u).union (Set.finite_singleton a)
  refine ⟨fun q => if q = a then t3 else if q = v then t2 else t1, hfin, ?_, ?_, ?_⟩
  · rw [w5cB2_pus3_v (a := u) (b := v) (c := a) huv (Ne.symm hua) (Ne.symm hva) hfin]
    simp only [if_neg hua, if_neg huv, if_neg hva, if_true, hz]
  · intro q hq
    simp only [Set.mem_singleton_iff] at hq
    subst hq
    simp only [if_true]
    exact ht3
  · rw [w5cB2_pus3_sum (a := u) (b := v) (c := a) huv (Ne.symm hua) (Ne.symm hva) hfin]
    simp only [if_neg hua, if_neg huv, if_neg hva, if_true]
    linarith

/-- 非共线三元组的第二方向系数零化：`r•(b-a) + s•(x-a) = 0 → s = 0`。 -/
private theorem w5cB_nc_second_coeff_zero {a b x : V3} (hab : a ≠ b) (hax : a ≠ x)
    (hnc : ¬Collinear ℝ ({a, b, x} : Set V3)) {r s : ℝ}
    (h0 : r • (b - a) + s • (x - a) = (0 : V3)) : s = 0 := by
  by_cases hs : s = 0
  · exact hs
  · exfalso
    apply hnc
    have hlin : s • (x - a) = -(r • (b - a)) := by
      rw [eq_comm, neg_eq_iff_add_eq_zero]
      exact h0
    have hmul : s * (r / s) = r := by
      field_simp
    have hxeq : x - a = (-(r / s)) • (b - a) := by
      refine w5cB_smul_left_cancel hs ?_
      rw [hlin, smul_smul, mul_neg, neg_smul, hmul]
    exact collinear3_iff_smul (v := a) (w := b) (w1 := x) (Ne.symm hab) |>.mpr
      ⟨-(r / s), hxeq⟩

/-- `COLL_IN_AFF_GT_TOO` 的就地重制：aff_gt 内的点与基座不共线。 -/
private theorem w5cB_coll_in_aff_gt_too {x y z a : V3} (hnc : ¬Collinear ℝ ({x, y, z} : Set V3))
    (ha : a ∈ affGt {x, y} {z}) : ¬Collinear ℝ ({x, y, a} : Set V3) := by
  intro hca
  have hxy : x ≠ y := fun he => hnc (collinear3_of_eq he.symm)
  have hyx : y ≠ x := Ne.symm hxy
  have hzx : z ≠ x := fun he => hnc (collinear3_pair_left he)
  have hzy : z ≠ y := fun he => hnc (collinear3_pair_right he)
  obtain ⟨c, hc, h, hsub⟩ :=
    affGt_pair_iff (v0 := x) (v1 := y) (x := z) (y := a) hxy hzx hzy |>.mp ha
  obtain ⟨c', hsub'⟩ :=
    collinear3_iff_smul (v := x) (w := y) (w1 := a) hyx |>.mp hca
  have hkey : c • (z - x) + h • (y - x) = c' • (y - x) := by
    rw [← hsub, hsub']
  have hkey2 : c • (z - x) = (c' - h) • (y - x) := by
    have h1 : c • (z - x) = c' • (y - x) - h • (y - x) := by
      rw [hkey.symm]
      module
    rw [h1]
    module
  have hmd : c * ((c' - h) / c) = c' - h := by
    field_simp
  have hz' : z - x = ((c' - h) / c) • (y - x) := by
    refine w5cB_smul_left_cancel (ne_of_gt hc) ?_
    rw [hkey2, smul_smul, hmd]
  exact hnc (collinear3_iff_smul (v := x) (w := y) (w1 := z) hyx |>.mpr ⟨(c' - h) / c, hz'⟩)

/-- `aff_gt` 射线上的点与轴基点共线性互相传递。 -/
private theorem w5cB_collinear3_affGt_transfer {u v x y : V3} (h : x ∈ affGt {u, v} {y}) :
    Collinear ℝ ({u, v, x} : Set V3) ↔ Collinear ℝ ({u, v, y} : Set V3) := by
  by_cases huv : u = v
  · constructor
    · exact fun _ => collinear3_of_eq huv.symm
    · exact fun _ => collinear3_of_eq huv.symm
  · by_cases huy : u = y
    · obtain ⟨f, hfin, hsumv, hpos, hone⟩ := h
      have h3 : hfin.toFinset = ({u, v} : Finset V3) := by
        ext q
        rw [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        simp only [huy]
        tauto
      rw [h3] at hsumv hone
      rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; exact huv),
        Finset.sum_singleton] at hsumv hone
      constructor
      · exact fun _ => collinear3_pair_left huy.symm
      · intro _
        refine collinear3_iff_smul (v := u) (w := v) (w1 := x) (Ne.symm huv) |>.mpr ⟨f v, ?_⟩
        rw [hsumv, show f u = 1 - f v from by linarith]
        module
    · by_cases hvy : v = y
      · obtain ⟨f, hfin, hsumv, hpos, hone⟩ := h
        have h3 : hfin.toFinset = ({u, v} : Finset V3) := by
          ext q
          rw [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
          simp only [hvy]
          tauto
        rw [h3] at hsumv hone
        rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; exact huv),
          Finset.sum_singleton] at hsumv hone
        constructor
        · exact fun _ => collinear3_pair_right hvy.symm
        · intro _
          refine collinear3_iff_smul (v := u) (w := v) (w1 := x) (Ne.symm huv) |>.mpr
            ⟨f v, ?_⟩
          rw [hsumv, show f u = 1 - f v from by linarith]
          module
      · -- 一般：三系数形
        obtain ⟨f, hfin, hsumv, hpos, hone⟩ := h
        have hfy : f y > 0 := hpos y (Set.mem_singleton y)
        have h3 : hfin.toFinset = ({u, v, y} : Finset V3) := by
          ext q
          rw [Set.Finite.mem_toFinset]
          simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
            Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [h3] at hsumv hone
        rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
          Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hvy),
          Finset.sum_singleton] at hsumv hone
        have key : x - u = f y • (y - u) + f v • (v - u) := by
          rw [hsumv, show f u = 1 - f v - f y from by linarith]
          module
        constructor
        · intro hcy
          obtain ⟨c, hcyy⟩ :=
            collinear3_iff_smul (v := u) (w := v) (w1 := x) (Ne.symm huv) |>.mp hcy
          refine collinear3_iff_smul (v := u) (w := v) (w1 := y) (Ne.symm huv) |>.mpr
            ⟨(c - f v) / f y, ?_⟩
          have h2 : f y • (y - u) + f v • (v - u) = c • (v - u) := key.symm.trans hcyy
          rw [show c = f v + (c - f v) from by ring, add_smul] at h2
          have hA : f y • (y - u) = (c - f v) • (v - u) :=
            add_right_cancel (h2.trans (add_comm (f v • (v - u)) ((c - f v) • (v - u))))
          have hmd : f y * ((c - f v) / f y) = c - f v := by
            field_simp
          refine w5cB_smul_left_cancel (ne_of_gt hfy) ?_
          rw [hA, smul_smul, hmd]
        · intro hcx
          obtain ⟨c, hcyy⟩ :=
            collinear3_iff_smul (v := u) (w := v) (w1 := y) (Ne.symm huv) |>.mp hcx
          refine collinear3_iff_smul (v := u) (w := v) (w1 := x) (Ne.symm huv) |>.mpr
            ⟨f v + f y * c, ?_⟩
          rw [hcyy] at key
          rw [smul_smul] at key
          rw [key, add_smul]
          abel

/-- `azim u v a z = π` 当 `z` 在 `a` 关于轴 `u v` 的对侧（affLt {u,v} {a} 形）。 -/
private theorem w5cB_azim_eq_pi_of_affLt {u v a z : V3}
    (hncA : ¬Collinear ℝ ({u, v, a} : Set V3)) (hncZ : ¬Collinear ℝ ({u, v, z} : Set V3))
    (hmem : z ∈ affLt {u, v} {a}) :
    azim u v a z = Real.pi := by
  have huv : u ≠ v := fun he => hncA (collinear3_of_eq he.symm)
  have hau : a ≠ u := fun he => hncA (collinear3_pair_left he)
  have hav : a ≠ v := fun he => hncA (collinear3_pair_right he)
  obtain ⟨t1, t2, t3, ht3, hsum, hz⟩ :=
    w5cB_affLt_2_1_mp (u := u) (v := v) (a := a) huv (Ne.symm hav) (Ne.symm hau) hmem
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (v - u) (sub_ne_zero.mpr (Ne.symm huv))
  have hax : (v - u : V3) = dist v u • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψ, r1, r2, hr1, hr2, hza, hzz⟩ :=
    azim_frame_spec (v := u) (w := v) (w1 := a) (w2 := z) hncA hncZ hon hax (Ne.symm huv)
  have hzu : z - u = t2 • (v - u) + t3 • (a - u) := by
    rw [hz, show t1 = 1 - t2 - t3 from by linarith]
    module
  have hzof : zOf f1 f2 (z - u) = ((t3 * r1 : ℝ) : ℂ) *
      Complex.exp (((ψ : ℝ) : ℂ) * Complex.I) := by
    rw [hzu, zOf_add, zOf_smul, zOf_smul, zOf_axis hax hon, mul_zero, zero_add, hza]
    push_cast
    ring
  rw [exp_add_I ψ (azim u v a z)] at hzz
  rw [hzof] at hzz
  rw [← mul_assoc] at hzz
  rw [mul_right_comm ((r2 : ℝ) : ℂ) (Complex.exp (((ψ : ℝ) : ℂ) * Complex.I))
    (Complex.exp (((azim u v a z : ℝ) : ℂ) * Complex.I))] at hzz
  have hkey : ((t3 * r1 : ℝ) : ℂ) = ((r2 : ℝ) : ℂ) *
      Complex.exp (((azim u v a z : ℝ) : ℂ) * Complex.I) :=
    mul_right_cancel₀ (Complex.exp_ne_zero _) hzz
  have hsin : Real.sin (azim u v a z) = 0 := by
    have hi := congrArg Complex.im hkey
    simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.exp_mul_I,
      Complex.add_im, Complex.add_re, Complex.I_re, Complex.I_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im, mul_zero,
      zero_mul, add_zero, zero_add, mul_one] at hi
    have h0 : (r2 : ℝ) * Real.sin (azim u v a z) = 0 := hi.symm
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hr2.ne'
    · exact h
  have hcoslt : Real.cos (azim u v a z) < 0 := by
    have hr := congrArg Complex.re hkey
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.exp_mul_I,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im, mul_zero,
      zero_mul, add_zero, zero_add, mul_one, sub_self, sub_zero] at hr
    have hreq : (r2 : ℝ) * Real.cos (azim u v a z) = (t3 : ℝ) * r1 := hr.symm
    by_contra hge
    push_neg at hge
    have hge2 : (0 : ℝ) ≤ (r2 : ℝ) * Real.cos (azim u v a z) := mul_nonneg hr2.le hge
    rw [hreq] at hge2
    have hneg : (t3 : ℝ) * r1 < 0 := mul_neg_of_neg_of_pos ht3 hr1
    linarith
  rcases Real.sin_eq_zero_iff.mp hsin with ⟨n, hn⟩
  have hpi : Real.pi > 0 := Real.pi_pos
  have hzero : (0 : ℝ) ≤ azim u v a z := azim_nonneg u v a z
  have hlt : azim u v a z < 2 * Real.pi := azim_lt_two_pi u v a z
  have hnge : (0 : ℝ) ≤ (n : ℝ) * Real.pi := by rw [hn]; exact hzero
  have hnlt : (n : ℝ) * Real.pi < 2 * Real.pi := by rw [hn]; exact hlt
  have hngR : (0 : ℝ) ≤ (n : ℝ) := by
    by_contra hneg
    push_neg at hneg
    have hmul : (n : ℝ) * Real.pi < 0 := mul_neg_of_neg_of_pos hneg hpi
    linarith
  have hn0 : n ≠ 0 := by
    intro h0
    have htheta0 : azim u v a z = (0 : ℝ) := by
      rw [← hn, h0]
      simp
    rw [htheta0, Real.cos_zero] at hcoslt
    linarith
  have hn1 : n = 1 := by
    have hr2' : (n : ℝ) < 2 := lt_of_mul_lt_mul_right hnlt hpi.le
    have hz2 : (n : ℤ) < 2 := by exact_mod_cast hr2'
    have hz0 : (0 : ℤ) ≤ n := by exact_mod_cast hngR
    omega
  rw [← hn, show ((n : ℝ) : ℝ) = 1 from by exact_mod_cast hn1, one_mul]

/-- HOL `AFF_GT_SUBSET_AFFINE_HULL21` (lunar_deform.hl:127): the
`{u,v} ∪ {w}` instance of `AFF_GT_SUBSET_AFFINE_HULL`.
NEEDS: `Affsign` → affine-combination → `affineSpan` bridge (Mathlib
`mem_affineSpan_iff_eq_affineCombination` bookkeeping over the explicit
finite witness of `Affsign`). -/
theorem AFF_GT_SUBSET_AFFINE_HULL21_p37 (u v w : V3) :
    affGt {u, v} {w} ⊆ (affineSpan ℝ ({u, v, w} : Set V3) : Set V3) := by
  intro z hz
  obtain ⟨f, hfin, hsumv, hpos, hone⟩ := hz
  have hFsub : ∀ x ∈ hfin.toFinset, x = u ∨ x = v ∨ x = w := by
    intro x hx
    rw [Set.Finite.mem_toFinset, Set.mem_union] at hx
    rcases hx with h1 | h1
    · rcases Set.mem_insert_iff.mp h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Set.mem_singleton_iff.mp h1))
  obtain ⟨t1, t2, t3, hv, hs⟩ := w5cB_finset3_sum u v w hFsub
  rw [hv] at hsumv
  rw [hsumv]
  exact w5cB_affine3_mem_affineSpan u v w t1 t2 t3 (by rw [← hs]; exact hone)

/-- HOL `DISJTINCT_PROPERTY` (lunar_deform.hl:131; source spelling kept):
a deformation pinning `V \\ {u}` while moving `u` continuously off them
separates `u` from `V \\ {u}` in a uniform time window. -/
theorem DISJTINCT_PROPERTY_p37 {V : Set V3} {f : V3 → ℝ → V3} {u : V3} {a b : ℝ}
    (hV : V.Finite) (hcu : ContinuousAt (f u) 0) (hu0 : f u 0 = u)
    (ha : a < 0) (hb : 0 < b)
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') :
    ∃ e : ℝ, 0 < e ∧ ∀ t u', -e < t ∧ t < e ∧ u' ∈ V ∧ u' ≠ u → f u t ≠ f u' t := by
  by_cases hempty : (V \ {u}).Nonempty
  · obtain ⟨s0, hs0⟩ := hempty
    haveI : Nonempty {z // z ∈ (V \ {u} : Set V3)} := ⟨⟨s0, hs0⟩⟩
    have hVd : (V \ {u} : Set V3).Finite := hV.sdiff
    obtain ⟨s, hmin⟩ := hVd.exists_min (fun z : {z // z ∈ (V \ {u} : Set V3)} => dist u z)
    have hsu : (s : V3) ≠ u := by
      intro heq
      exact s.2.2 (by rw [heq]; exact Set.mem_singleton u)
    have hsd : 0 < dist u (s : V3) := by
      have h0 : dist u (s : V3) ≠ 0 := fun hzero => hsu (dist_eq_zero.mp hzero).symm
      exact lt_of_le_of_ne (by norm_num : 0 ≤ dist u (s : V3)) (Ne.symm h0)
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ s' : ℝ, dist s' 0 < δ →
        dist (f u s') (f u 0) < dist u (s : V3) / 2 := by
      have h2 := Metric.continuousAt_iff.mp hcu (dist u (s : V3) / 2) (by linarith)
      obtain ⟨δ, hδ0, hδ⟩ := h2
      exact ⟨δ, hδ0, hδ⟩
    have hpos : 0 < min (min (-a) b) (min δ (dist u (s : V3) / 2)) :=
      lt_min (lt_min (by linarith) hb) (lt_min hδ0 (by linarith))
    refine ⟨min (min (-a) b) (min δ (dist u (s : V3) / 2)), hpos, ?_⟩
    intro t u' hcon
    obtain ⟨ht1, ht2, hmem, hne⟩ := hcon
    have hea : min (min (-a) b) (min δ (dist u (s : V3) / 2)) ≤ -a :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hebs : min (min (-a) b) (min δ (dist u (s : V3) / 2)) ≤ b :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hicc : t ∈ Icc a b := by
      have h1 : a ≤ t := by linarith
      have h2 : t ≤ b := by linarith
      exact ⟨h1, h2⟩
    have hpin' : f u' t = u' := hpin u' hmem (Ne.symm hne) t hicc
    have hpin0 : f u' 0 = u' := hpin u' hmem (Ne.symm hne) 0 ⟨by linarith, by linarith⟩
    have hts : dist t 0 < δ := by
      rw [Real.dist_0_eq_abs]
      have hab : |t| < min (min (-a) b) (min δ (dist u (s : V3) / 2)) := by
        rw [abs_lt]; exact ⟨ht1, ht2⟩
      exact lt_of_lt_of_le hab (le_trans (min_le_right _ _) (min_le_left _ _))
    have hcontr : dist (f u t) (f u 0) < dist u (s : V3) / 2 := hδ t hts
    rw [hu0] at hcontr
    intro heq
    rw [heq, hpin'] at hcontr
    rw [dist_comm u' u] at hcontr
    have h1 : dist u (s : V3) ≤ dist u u' := by
      have hsu' : u' ∈ (V \ {u} : Set V3) := ⟨hmem, hne⟩
      have := hmin ⟨u', hsu'⟩
      simpa using this
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro t u' hcon
    obtain ⟨_, _, hmem, hne⟩ := hcon
    exact absurd (⟨u', ⟨hmem, hne⟩⟩ : (V \ {u} : Set V3).Nonempty) hempty

/-- HOL `EDGE_FORM_IN_LOCAL_FAN` (lunar_deform.hl:175).  NEEDS: the fan
`E`-is-2-sets kit (`Local_lemmas1.HAS_SIZE_2_EXISTS2` path) — the registry
`LocalFan` stub carries no `E` substance. -/
theorem EDGE_FORM_IN_LOCAL_FAN_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {x : Set V3} (h : LocalFan V E FF) (hx : x ∈ E) :
    ∃ u v : V3, u ≠ v ∧ {u, v} = x := by
  obtain ⟨hfan, d, hd, -, -, -⟩ := h
  obtain ⟨hfin, hcard⟩ := hfan.2.1 x hx
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hcard
  refine ⟨a, b, hab, ?_⟩
  rw [← Set.Finite.coe_toFinset hfin, hset]
  simp

/-- W5c-B5 助件：registry `LocalFan` → LA2 `localFan_p2` 编码桥
（经 AzimBridge 的 α2 等价 `localFanEquiv_p35 : LocalFan ↔ localFan_p3`，
`_p2`/`_p3` 定义相等）。LA5 fan-rho kit 的消费入口。 -/
private theorem w5cB5_to_localFan_p2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) : localFan_p2 V E FF :=
  localFan_p2.of_localFan_p3 (localFanEquiv_p35.mp h)

/-- HOL `EDGE_IN_LOCAL_FAN_DET_RHO_NODE` (lunar_deform.hl:185).  消费 LA5 净证
`LOFA_IN_E_IMP_IN_FF` + `DETER_RHO_NODE`（`localFan_p2` 编码，经桥进入）+
本文件已净的 `EDGE_FORM_IN_LOCAL_FAN_p37`。 -/
theorem EDGE_IN_LOCAL_FAN_DET_RHO_NODE_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {x : Set V3} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hx : x ∈ E) :
    ∃ v ∈ V, {v, rhoNode1 FF v} = x := by
  obtain ⟨a, b, hab, hset⟩ := EDGE_FORM_IN_LOCAL_FAN_p37 h hx
  have hxE : ({a, b} : Set V3) ∈ E := by rw [hset]; exact hx
  rcases LOFA_IN_E_IMP_IN_FF (w5cB5_to_localFan_p2 h) hxE with hd | hd
  · have hrho : rhoNode1 FF a = b := DETER_RHO_NODE (w5cB5_to_localFan_p2 h) hd
    exact ⟨a, (WRGCVDR_BIJ (w5cB5_to_localFan_p2 h)).1 hd, by rw [hrho, ← hset]⟩
  · have hrho : rhoNode1 FF b = a := DETER_RHO_NODE (w5cB5_to_localFan_p2 h) hd
    refine ⟨b, (WRGCVDR_BIJ (w5cB5_to_localFan_p2 h)).1 hd, ?_⟩
    rw [hrho, ← hset]
    ext q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- HOL `TOW_POINTS_IN_IMP_AFF_GT_SUBSET` (lunar_deform.hl:209; source
spelling kept).  NEEDS: the `AFF_GT_2_1`/`AFF_GT_1_2` affine-coordinate
decomposition twins (positive-coefficient rewriting kit). -/
theorem TOW_POINTS_IN_IMP_AFF_GT_SUBSET_p37 {x u v a b : V3}
    (_h1 : Disjoint ({x, u} : Set V3) ({v} : Set V3))
    (_ha : a ∈ affGt {x, u} {v}) (_hb : b ∈ affGt {x, u} {v})
    (_h2 : Disjoint ({x} : Set V3) ({a, b} : Set V3)) :
    affGt {x} {a, b} ⊆ affGt {x, u} {v} := by
  have hxv : x ≠ v := fun he =>
    Set.disjoint_left.mp _h1 (Set.mem_insert x ({u} : Set V3)) (by rw [he]; simp)
  have huv : u ≠ v := fun he =>
    Set.disjoint_left.mp _h1 (Set.mem_insert_of_mem x (Set.mem_singleton u))
      (by rw [he]; simp)
  have hxa : x ≠ a := fun he =>
    Set.disjoint_left.mp _h2 (Set.mem_singleton x) (by rw [he]; simp)
  have hxb : x ≠ b := fun he =>
    Set.disjoint_left.mp _h2 (Set.mem_singleton x) (by rw [he]; simp)
  by_cases hab : a = b
  · -- a = b：集合塌缩，两系数形复合
    rw [show ({a, b} : Set V3) = ({b} : Set V3) from by rw [hab]; ext q; simp]
    intro w hw
    obtain ⟨p1, p2, hp2, hpsum, hpb⟩ := w5cB_affGt_single_mp hxb hw
    by_cases hxu : x = u
    · subst hxu
      rw [show ({x, x} : Set V3) = ({x} : Set V3) from by ext q; simp] at _hb ⊢
      obtain ⟨q1, q2, hq2, hqsum, hqb⟩ := w5cB_affGt_single_mp hxv _hb
      have hs : p1 + p2 * q1 + p2 * q2 = 1 :=
        by linear_combination hpsum + p2 * hqsum
      refine w5cB_affGt_single_mpr hxv (t1 := p1 + p2 * q1) (t2 := p2 * q2)
        (mul_pos hp2 hq2) hs ?_
      rw [hpb, hqb]
      module
    · obtain ⟨q1, q2, q3, hq3, hqsum, hqb⟩ := w5cB_affGt_2_1_mp hxu hxv huv _hb
      have hs : p1 + p2 * q1 + p2 * q2 + p2 * q3 = 1 :=
        by linear_combination hpsum + p2 * hqsum
      refine w5cB_affGt_2_1_mpr hxu hxv huv (t1 := p1 + p2 * q1) (t2 := p2 * q2)
        (t3 := p2 * q3) (mul_pos hp2 hq3) hs ?_
      rw [hpb, hqb]
      module
  · -- a ≠ b：三系数形复合
    by_cases hxu : x = u
    · subst hxu
      rw [show ({x, x} : Set V3) = ({x} : Set V3) from by ext q; simp] at _ha _hb ⊢
      intro w hw
      obtain ⟨r1, r2, r3, hr2, hr3, hrsum, hrw⟩ := w5cB_affGt_1_2_mp hxa hxb hab hw
      obtain ⟨p1, p2, hp2, hpsum, hpa⟩ := w5cB_affGt_single_mp hxv _ha
      obtain ⟨q1, q2, hq2, hqsum, hqb⟩ := w5cB_affGt_single_mp hxv _hb
      have hs : r1 + r2 * p1 + r3 * q1 + (r2 * p2 + r3 * q2) = 1 :=
        by linear_combination hrsum + r2 * hpsum + r3 * hqsum
      refine w5cB_affGt_single_mpr hxv (t1 := r1 + r2 * p1 + r3 * q1)
        (t2 := r2 * p2 + r3 * q2) (add_pos (mul_pos hr2 hp2) (mul_pos hr3 hq2))
        hs ?_
      rw [hrw, hpa, hqb]
      module
    · intro w hw
      obtain ⟨r1, r2, r3, hr2, hr3, hrsum, hrw⟩ := w5cB_affGt_1_2_mp hxa hxb hab hw
      obtain ⟨p1, p2, p3, hp3, hpsum, hpa⟩ := w5cB_affGt_2_1_mp hxu hxv huv _ha
      obtain ⟨q1, q2, q3, hq3, hqsum, hqb⟩ := w5cB_affGt_2_1_mp hxu hxv huv _hb
      have hs : r1 + r2 * p1 + r3 * q1 + (r2 * p2 + r3 * q2) + (r2 * p3 + r3 * q3) = 1 :=
        by linear_combination hrsum + r2 * hpsum + r3 * hqsum
      refine w5cB_affGt_2_1_mpr hxu hxv huv (t1 := r1 + r2 * p1 + r3 * q1)
        (t2 := r2 * p2 + r3 * q2) (t3 := r2 * p3 + r3 * q3)
        (add_pos (mul_pos hr2 hp3) (mul_pos hr3 hq3)) hs ?_
      rw [hrw, hpa, hqb]
      module

/-- HOL `REAL_LT_MUL12` (lunar_deform.hl:251). -/
theorem REAL_LT_MUL12_p37 {a b : ℝ} (hb : 0 < b) (ha : a < 0) : a * b < 0 :=
  mul_neg_of_neg_of_pos ha hb

/-- HOL `COLL_IN_AFF_GT_INTER_EMPTY` (lunar_deform.hl:259).  NEEDS:
`Local_lemmas.COLL_IN_AFF_GT_TOO` + `Fan.th3a` + the affine-coordinate
decomposition kit. -/
theorem COLL_IN_AFF_GT_INTER_EMPTY_p37 {a b x u : V3}
    (hnc : ¬Collinear ℝ ({a, b, x} : Set V3)) (hu : u ∈ affGt {a, b} {x}) :
    affGt {a, b} {x} ∩ affLt {a} {u} = ∅ := by
  have hab : a ≠ b := fun he => hnc (collinear3_of_eq he.symm)
  have hax : a ≠ x := fun he => hnc (collinear3_pair_left he.symm)
  have hbx : b ≠ x := fun he => hnc (collinear3_pair_right he.symm)
  have hncu := w5cB_coll_in_aff_gt_too (x := a) (y := b) (z := x) (a := u) hnc hu
  have hua : u ≠ a := fun he => hncu (collinear3_pair_left he)
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨t1, t2, t3, ht3, hsum, hw1'⟩ := w5cB_affGt_2_1_mp hab hax hbx hw1
  obtain ⟨s1, s2, hs2, ssum, hw2'⟩ := w5cB_affLt_1_1_mp (Ne.symm hua) hw2
  obtain ⟨t1', t2', t3', ht3', hsum', hu'⟩ := w5cB_affGt_2_1_mp hab hax hbx hu
  rw [hu'] at hw2'
  have hsub1 : w - a = t2 • (b - a) + t3 • (x - a) := by
    rw [hw1', show t1 = 1 - t2 - t3 from by linarith]
    module
  have hsub2 : w - a = (s2 * t2') • (b - a) + (s2 * t3') • (x - a) := by
    rw [hw2', show s1 = 1 - s2 from by linarith,
      show t1' = 1 - t2' - t3' from by linarith]
    module
  have hd : (t2 • (b - a) + t3 • (x - a)) -
      ((s2 * t2') • (b - a) + (s2 * t3') • (x - a)) = (0 : V3) := by
    rw [← hsub1, ← hsub2, sub_self]
  have hcoef : (t2 - s2 * t2') • (b - a) + (t3 - s2 * t3') • (x - a) = (0 : V3) := by
    rw [smul_sub, smul_sub, ← hd]
    module
  have hzero := w5cB_nc_second_coeff_zero hab hax hnc hcoef
  linarith [mul_neg_of_neg_of_pos hs2 ht3', hzero, ht3]

/-! ### G5 kit: LA1→LA2 convex bridge, arc-set rewrite, iterate mod-folding

The `ConvexLocalFan` (LA1) → `convexLocalFan_p2` (LA2) transport is the
`private` `kcs_clf2` of `CircularSolKit` (and its LocalAuto26 copy
`w5sg_clf2_p26`); its body is carried here verbatim, with the two private
helpers (`kcs_hedge`, `kcs_ffSubDart`) re-made locally.  Also the
`image ↔ set-builder` rewrite for the `LUNA`-arc sets (`HKIRPEP` states the
arcs as images, the `lunar_deform.hl` statements as set-builders) and the
iterate mod-folding used by the two-half membership argument. -/

private theorem la37g5_hedge {V : Set V3} {E : Set (Set V3)}
    (h2reg : ∀ u ∈ V, (ee u E).ncard = 2) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  intro v hv
  have h2 : (ee v E).ncard = 2 := h2reg v hv
  have hne : (ee v E) ≠ ∅ := by
    intro hE
    rw [hE, Set.ncard_empty] at h2
    omega
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact ⟨w, hw⟩

private theorem la37g5_ffSubDart {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : LocalFan V E FF) : FF ⊆ Fan.dart1OfFan V E := by
  obtain ⟨-, -, -, -, -, hsub, -⟩ := localFan_data hlf
  exact hsub

private theorem la37g5_clf2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : ConvexLocalFan V E FF) : convexLocalFan_p2 V E FF := by
  obtain ⟨hlf, hcvx⟩ := h
  have hcopy := hlf
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := hcopy
  have hlf2 := localFan_p2.of_LocalFan_noIso hlf (la37g5_hedge h2reg)
  have hsub := la37g5_ffSubDart hlf
  refine ⟨hlf2, ?_⟩
  intro d hd
  refine ⟨?_, ?_⟩
  · have hb : azimInFan d E = azimInFan_p3 d E :=
      azimInFan_eq_azimInFan_p3 hfan (hsub hd)
    show azimInFan_p2 d E ≤ Real.pi
    rw [show azimInFan_p2 d E = azimInFan_p3 d E from rfl, ← hb]
    exact (hcvx d hd).1
  · show V ⊆ wedgeInFanGe_p2 d E
    rw [show wedgeInFanGe_p2 d E = wedgeInFanGe_p3 d E from rfl,
      ← wedgeInFanGe_eq_wedgeInFanGe_p3 hfan (hsub hd)]
    exact (hcvx d hd).2

private theorem la37g5_arc_image (FF : Set (V3 × V3)) (v : V3) (i : ℕ) :
    ((fun l => (rhoNode1 FF)^[l] v) '' {l : ℕ | 0 < l ∧ l < i})
      = {z | ∃ l, 0 < l ∧ l < i ∧ z = (rhoNode1 FF)^[l] v} := by
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l, ⟨h1, h2⟩, rfl⟩
    exact ⟨l, h1, h2, rfl⟩
  · rintro ⟨l, h1, h2, rfl⟩
    exact ⟨l, ⟨h1, h2⟩, rfl⟩

private theorem la37g5_iter_mod {α : Type*} {f : α → α} {x : α} {k : ℕ} (_hk : 0 < k)
    (hper : f^[k] x = x) (m : ℕ) : f^[m] x = f^[m % k] x := by
  have hstep : ∀ r : ℕ, f^[r + k] x = f^[r] x := by
    intro r
    rw [Function.iterate_add_apply f r k x, hper]
  have hmain : ∀ q r : ℕ, f^[q * k + r] x = f^[r] x := by
    intro q
    induction q with
    | zero =>
        intro r
        simp
    | succ q ih =>
        intro r
        have hq : q.succ * k + r = (q * k + r) + k := by
          rw [Nat.succ_eq_add_one]
          ring_nf
        rw [hq, hstep, ih r]
  calc f^[m] x = f^[m / k * k + m % k] x := by
        conv_lhs =>
          rw [show m = m / k * k + m % k from by
            rw [Nat.mul_comm (m / k) k]
            exact (Nat.div_add_mod m k).symm]
    _ = f^[m % k] x := hmain (m / k) (m % k)

/-- HOL `HKIRPEP_ALT` (lunar_deform.hl:316): the lunar two-half circle
characterisation, `Local_lemmas.HKIRPEP` re-pruned for the deformation
file.  PROVED (la37-g5-w1): LA5 `HKIRPEP` + LA6 `CARD_V_TWO_HAFL_CIRCLE`
(the `i + j = ncard` increment) + the `ConvexLocalFan`→`convexLocalFan_p2`
bridge and the arc-set rewrite of the G5 kit above. -/
theorem HKIRPEP_ALT_p37 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} (_h : ConvexLocalFan V E FF) (_hl : Lunar v w V E) :
    (∀ u ∈ V \ {v, w}, interiorAngle1 0 FF u = Real.pi) ∧
      0 < interiorAngle1 0 FF v ∧
      interiorAngle1 0 FF v ≤ Real.pi ∧
      interiorAngle1 0 FF v = interiorAngle1 0 FF w ∧
      ∃ i j : ℕ, i + j = Set.ncard V ∧ i < Set.ncard V ∧ i ≠ 0 ∧ i ≠ 1 ∧
        w = (rhoNode1 FF)^[i] v ∧
        {z | ∃ l, 0 < l ∧ l < i ∧ z = (rhoNode1 FF)^[l] v} =
          affGt {0, v} {rhoNode1 FF v} ∩ V ∧
        j < Set.ncard V ∧ j ≠ 0 ∧ j ≠ 1 ∧
        v = (rhoNode1 FF)^[j] w ∧
        {z | ∃ l, 0 < l ∧ l < j ∧ z = (rhoNode1 FF)^[l] w} =
          affGt {0, v} {ivsRhoNode1 FF v} ∩ V := by
  have hclf : convexLocalFan_p2 V E FF := la37g5_clf2 _h
  have hl2 : lunar_p2 v w V E := _hl
  have hvV : v ∈ V := _hl.2.1 (by simp)
  have hwV : w ∈ V := _hl.2.1 (by simp)
  obtain ⟨hpi, hpos, hle, heq, hi, hj⟩ := HKIRPEP hclf hl2
  obtain ⟨i, hiV, hi0, hi1, hwi, harci⟩ := hi
  obtain ⟨j, hjV, hj0, hj1, hvj, harcj⟩ := hj
  have hsum : i + j = Set.ncard V :=
    CARD_V_TWO_HAFL_CIRCLE hclf.1 hvV hwV _hl.2.2.1 i j hwi.symm hvj.symm hiV hjV
  refine ⟨?_, ?_, ?_, ?_, i, j, hsum, hiV, hi0, hi1, hwi, ?_, hjV, hj0, hj1, hvj, ?_⟩
  · exact hpi
  · exact hpos
  · exact hle
  · exact heq
  · rw [← la37g5_arc_image FF v i]
    exact harci
  · rw [← la37g5_arc_image FF w j]
    exact harcj

/-- HOL `LUNAR_IMP_IN_TWO_HAFLS_PLANE` (lunar_deform.hl:358).
PROVED (la37-g5-w1): the two `HKIRPEP_ALT` arc equalities plus rho-orbit
mod-folding (`la37g5_iter_mod`) place every vertex of `V \ {v, w}` on one
of the two `affGt` cones. -/
theorem LUNAR_IMP_IN_TWO_HAFLS_PLANE_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v w : V3} (_h : ConvexLocalFan V E FF)
    (_hl : Lunar v w V E) :
    ∀ u ∈ V, u ≠ v → u ≠ w →
      u ∈ affGt {0, v} {rhoNode1 FF v} ∨ u ∈ affGt {0, v} {ivsRhoNode1 FF v} := by
  have hlf : localFan_p2 V E FF := (CVLF_LF_F (la37g5_clf2 _h)).1
  have hvV : v ∈ V := _hl.2.1 (by simp)
  obtain ⟨-, -, -, -, i, j, hsum, hiV, hi0, hi1, hwi, harci, hjV, hj0, hj1, hvj, harcj⟩ :=
    HKIRPEP_ALT_p37 _h _hl
  have hper : (rhoNode1 FF)^[i + j] v = v := by
    rw [show i + j = j + i from Nat.add_comm i j, Function.iterate_add_apply, ← hwi, ← hvj]
  intro u hu hne1 hne2
  have hu2 : u ∈ orbitF_p2 (rhoNode1_p2 FF) v := by
    rw [LOCAL_FAN_ORBIT_MAP_V hlf hvV]
    exact hu
  simp only [orbitF_p2, Set.mem_setOf_eq] at hu2
  obtain ⟨m, hm⟩ := hu2
  have hf := la37g5_iter_mod (α := V3) (f := rhoNode1 FF) (x := v)
    (k := i + j) (by omega) hper m
  have hur : (rhoNode1 FF)^[m % (i + j)] v = u := hf.symm.trans hm
  rcases Nat.lt_trichotomy (m % (i + j)) i with hri | hri | hri
  · rcases Nat.eq_zero_or_pos (m % (i + j)) with hr0 | hrpos
    · rw [hr0, Function.iterate_zero_apply] at hur
      exact absurd hur.symm hne1
    · left
      have huarc : u ∈ {z | ∃ l, 0 < l ∧ l < i ∧ z = (rhoNode1 FF)^[l] v} :=
        ⟨m % (i + j), hrpos, hri, hur.symm⟩
      have humem : u ∈ affGt {0, v} {rhoNode1 FF v} ∩ V := by
        rw [← harci]
        exact huarc
      exact humem.1
  · right
    rw [hri, ← hwi] at hur
    exact absurd hur.symm hne2
  · right
    have hrlt : m % (i + j) < i + j := Nat.mod_lt _ (by omega)
    have hsplit : (rhoNode1 FF)^[m % (i + j)] v
        = (rhoNode1 FF)^[m % (i + j) - i] ((rhoNode1 FF)^[i] v) := by
      have hradd : m % (i + j) = m % (i + j) - i + i := by omega
      conv_lhs =>
        rw [hradd, Function.iterate_add_apply]
    rw [hsplit, ← hwi] at hur
    have huarc : u ∈ {z | ∃ l, 0 < l ∧ l < j ∧ z = (rhoNode1 FF)^[l] w} :=
      ⟨m % (i + j) - i, by omega, by omega, hur.symm⟩
    have humem : u ∈ affGt {0, v} {ivsRhoNode1 FF v} ∩ V := by
      rw [← harcj]
      exact huarc
    exact humem.1

/-- HOL `IN_CONV0_IMP_AFF_EQ1` (lunar_deform.hl:434).  The twin
`Local_lemmas.IN_CONV0_IMP_AFF_EQ` lives in the unbuilt LocalAuto5, so
`conv0 {x, y}` is rendered as Mathlib `openSegment ℝ x y` (open segment;
`conv0` in the azure tree is `open_segment` per Polytope.lean head note)
and the two-span equality is proved directly.
NEEDS: re-align with `conv0_p2`/`IN_CONV0_IMP_AFF_EQ` at the LocalAuto5
merge point. -/
theorem IN_CONV0_IMP_AFF_EQ1_p37 {x y a : V3} (ha : a ∈ openSegment ℝ x y) :
    (affineSpan ℝ ({a, x} : Set V3) : Set V3) = (affineSpan ℝ ({a, y} : Set V3) : Set V3) := by
  obtain ⟨p, q, hp, hq, hpq, hab⟩ := ha
  have hq1 : q = 1 - p := by linarith
  have hxmem : x ∈ (affineSpan ℝ ({a, y} : Set V3) : Set V3) := by
    have hx0 : x -ᵥ a = q • (x - y) := by
      rw [vsub_eq_sub, ← hab, hq1]
      module
    have hy0 : y -ᵥ a = p • (y - x) := by
      rw [vsub_eq_sub, ← hab, hq1]
      module
    have hp0 : p ≠ 0 := ne_of_gt hp
    have hcancel : (-q / p) * p = -q := by field_simp
    have hv : x -ᵥ a = (-q / p) • (y -ᵥ a) := by
      rw [hx0, hy0, smul_smul, hcancel]
      module
    have h1 : x = AffineMap.lineMap a y (-q / p) := by
      rw [AffineMap.lineMap_apply, ← hv, vsub_vadd]
    rw [h1]
    exact AffineMap.lineMap_mem_affineSpan_pair (-q / p) a y
  have hymem : y ∈ (affineSpan ℝ ({a, x} : Set V3) : Set V3) := by
    have hx2 : a -ᵥ x = q • (y - x) := by
      rw [vsub_eq_sub, ← hab, hq1]
      module
    have hcancel2 : 1 / q * q = 1 := by field_simp
    have hv2 : y -ᵥ x = (1 / q) • (a -ᵥ x) := by
      rw [hx2, smul_smul, hcancel2, vsub_eq_sub]
      module
    have h1 : y = AffineMap.lineMap x a (1 / q) := by
      rw [AffineMap.lineMap_apply, ← hv2, vsub_vadd]
    have h3 := AffineMap.lineMap_mem_affineSpan_pair (1 / q) x a
    rw [show ({x, a} : Set V3) = {a, x} by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h3
    rw [h1]
    exact h3
  have hsp : affineSpan ℝ ({a, x} : Set V3) ≤ affineSpan ℝ ({a, y} : Set V3) :=
    affineSpan_pair_le_of_mem_of_mem (mem_affineSpan (k := ℝ) (Set.mem_insert _ _)) hxmem
  have hsp' : affineSpan ℝ ({a, y} : Set V3) ≤ affineSpan ℝ ({a, x} : Set V3) :=
    affineSpan_pair_le_of_mem_of_mem (mem_affineSpan (k := ℝ) (Set.mem_insert _ _)) hymem
  exact le_antisymm hsp hsp'

/-- HOL `AFF_LT_SUBSET_AFF11` (lunar_deform.hl:444).  DISCHARGED 2026-09-20:
the `Affsign` coefficient sum (total 1 over the `{a, b}` support) is exactly
an affine line parametrisation, so the point lands in `affineSpan {a, b}`;
the sign bookkeeping is irrelevant for the hull inclusion. -/
theorem AFF_LT_SUBSET_AFF11_p37 {a b : V3} (_h : Disjoint ({a} : Set V3) ({b} : Set V3)) :
    affLt {a} {b} ⊆ (affineSpan ℝ ({a, b} : Set V3) : Set V3) := by
  intro x hx
  obtain ⟨f, hfin, hx, -, hsum⟩ := hx
  have h2f : hfin.toFinset = ({a, b} : Finset V3) := by
    ext u
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  rw [h2f] at hx hsum
  by_cases hab : a = b
  · rw [hab] at hx hsum
    have h1 : f b = 1 := by simpa using hsum
    have hxe : x = f b • b := by simpa using hx
    rw [h1] at hxe
    have hxb : x = b := by simpa using hxe
    rw [hxb]
    exact mem_affineSpan (k := ℝ) (Set.mem_insert_of_mem _ rfl)
  · have hpa : ∑ w ∈ ({a, b} : Finset V3), f w • w = f a • a + f b • b := by
      rw [Finset.sum_insert (by simp [hab]), Finset.sum_singleton]
    have hpb : ∑ w ∈ ({a, b} : Finset V3), f w = f a + f b := by
      rw [Finset.sum_insert (by simp [hab]), Finset.sum_singleton]
    rw [hpa] at hx
    rw [hpb] at hsum
    have h1 : f a = 1 - f b := by linarith
    have h2 : AffineMap.lineMap a b (f b) = f b • (b -ᵥ a) +ᵥ a :=
      AffineMap.lineMap_apply a b (f b)
    have e1 : ∀ z w : V3, z -ᵥ w = z - w := fun _ _ => rfl
    have e2 : ∀ p v : V3, p +ᵥ v = p + v := fun _ _ => rfl
    have hline : x = AffineMap.lineMap a b (f b) := by
      rw [h2, hx, h1, e1, e2, sub_smul, one_smul, smul_sub]
      abel
    rw [hline]
    exact AffineMap.lineMap_mem_affineSpan_pair (f b) a b

/-- HOL `AZIM_PI_LEMMA` (lunar_deform.hl:459).  NEEDS:
`Local_lemmas.COLL_IN_AFF_GT_AFF_GT_EQ`/`COLL_IN_AFF_GT_TOO` +
`AFF_LT_MONO_LEFT` kit. -/
theorem AZIM_PI_LEMMA_p37 {u v x y a : V3} {s : Set V3}
    (_h1 : ¬(affGt {u} s ∩ affLt {u} {a} = ∅))
    (_h2 : affGt {u} s ⊆ affGt {u, v} {y})
    (_h3 : a ∈ affGt {u, v} {x})
    (_h4 : ¬Collinear ℝ ({u, v, x} : Set V3))
    (_h5 : ¬Collinear ℝ ({u, v, y} : Set V3)) :
    azim u v x y = Real.pi := by
  obtain ⟨z', hz'1, hz'2⟩ := Set.nonempty_iff_ne_empty.mpr _h1
  have huv : u ≠ v := fun he => _h5 (collinear3_of_eq he.symm)
  have hz'1' : z' ∈ affGt {u, v} {y} := _h2 hz'1
  have hncA := w5cB_coll_in_aff_gt_too (x := u) (y := v) (z := x) (a := a) _h4 _h3
  have hncZ := w5cB_coll_in_aff_gt_too (x := u) (y := v) (z := y) (a := z') _h5 hz'1'
  have hua : u ≠ a := fun he => hncA (collinear3_pair_left he.symm)
  have hav : a ≠ v := fun he => hncA (collinear3_pair_right he)
  have hz'2' : z' ∈ affLt {u, v} {a} := by
    obtain ⟨s1, s2, hs2, ssum, hzz⟩ := w5cB_affLt_1_1_mp hua hz'2
    exact w5cB_affLt_2_1_mpr (u := u) (v := v) (a := a) huv (Ne.symm hav) hua
      (t1 := s1) (t2 := 0) (t3 := s2) hs2 (by linarith)
      (by rw [hzz, zero_smul, add_zero])
  have hpi : azim u v a z' = Real.pi := w5cB_azim_eq_pi_of_affLt hncA hncZ hz'2'
  have hchain2 : azim u v a y = Real.pi := by
    have heq := (azim_eq_azim_iff_alt (v0 := u) (v1 := v) (w := a) (x := z') (y := y)
      hncA hncZ _h5).mpr hz'1'
    rw [← heq]
    exact hpi
  have hcompl1 : azim u v y a = Real.pi := by
    have hc := azim_compl (z := u) (w := v) (w1 := y) (w2 := a) _h5 hncA
    by_cases hz0 : azim u v y a = 0
    · rw [hz0, if_pos rfl] at hc
      linarith
    · rw [if_neg hz0] at hc
      have hval : Real.pi = 2 * Real.pi - azim u v y a := by linarith [hchain2, hc]
      linarith
  have hchain3 : azim u v y x = Real.pi := by
    have heq := (azim_eq_azim_iff_alt (v0 := u) (v1 := v) (w := y) (x := a) (y := x)
      _h5 hncA _h4).mpr _h3
    rw [← heq]
    exact hcompl1
  have hc2 := azim_compl (z := u) (w := v) (w1 := y) (w2 := x) _h5 _h4
  by_cases hz0 : azim u v y x = 0
  · rw [hz0, if_pos rfl] at hc2
    linarith
  · rw [if_neg hz0] at hc2
    rw [hc2]
    linarith

/-! ## w5cB3 kit (W5c-B 第三波): `SUB_LUNAR_DEFORM_LEMMA` 分段 1–6

HOL 源 `lunar_deform.hl:528-1830` 按消费点切段；本区承载前六段（全部净证）。
剩余段的划分图与下波工单见 `DELIVERY.md` §5。 -/

/-- 分段 1（HOL `lunar_deform.hl:556-640`，SUB_LUNAR 首个子目标）：
`t ∈ Icc a b` 时形变钉住 `v, w`（`u ≠ v, u ≠ w` + `hpin`），故
`{v, w}` 仍在形变像 `(f · t) '' V` 中，且 `v ≠ w` 保持（`Lunar`）。 -/
private theorem w5cB3_image_preserves_lunar
    {a b : ℝ} {V : Set V3} {E : Set (Set V3)} {f : V3 → ℝ → V3} {u v w : V3}
    (hl : Lunar v w V E) (huv : u ≠ v) (huw : u ≠ w)
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') :
    ∀ t ∈ Icc a b, f v t = v ∧ f w t = w ∧
      ({v, w} ⊆ (fun z => f z t) '' V) ∧ v ≠ w := by
  obtain ⟨-, hVsub, hvw, -⟩ := hl
  have hvV : v ∈ V := hVsub (by simp)
  have hwV : w ∈ V := hVsub (by simp)
  intro t ht
  have hfv : f v t = v := hpin v hvV huv t ht
  have hfw : f w t = w := hpin w hwV huw t ht
  refine ⟨hfv, hfw, ?_, hvw⟩
  intro z hz
  rcases Set.mem_insert_iff.mp hz with heq | hz
  · rw [heq]
    exact ⟨v, hvV, hfv⟩
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨w, hwV, hfw⟩

/-- 分段 2（HOL `lunar_deform.hl:648-700`，`Counting_spheres.pad2d3d_dropout_lemma`
的显式版）：`x ⊆ V` 的形变像等于 `x \ {u}` 再按需换入 `f u t`。 -/
private theorem w5cB3_image_sdiff
    {a b : ℝ} {V : Set V3} {f : V3 → ℝ → V3} {u : V3}
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') :
    ∀ t ∈ Icc a b, ∀ x ⊆ V,
      (fun z => f z t) '' x = (x \ {u}) ∪ (if u ∈ x then {f u t} else ∅) := by
  intro t ht x hx
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    by_cases hzu : z = u
    · subst hzu
      rw [if_pos hz]
      exact Set.mem_union_right _ (Set.mem_singleton _)
    · have hfix : f z t = z := hpin z (hx hz) (Ne.symm hzu) t ht
      change f z t ∈ (x \ {u}) ∪ (if u ∈ x then {f u t} else ∅)
      rw [hfix]
      exact Set.mem_union_left _ ⟨hz, hzu⟩
  · intro hy
    rw [Set.mem_union] at hy
    rcases hy with hy | hy
    · refine ⟨y, hy.1, ?_⟩
      exact hpin y (hx hy.1) (fun he => hy.2 (by rw [he]; simp)) t ht
    · by_cases hux : u ∈ x
      · rw [if_pos hux] at hy
        rw [Set.mem_singleton_iff] at hy
        exact ⟨u, hux, hy.symm⟩
      · rw [if_neg hux] at hy
        exact absurd hy (Set.notMem_empty y)

/-- 分段 2 特例（HOL `lunar_deform.hl:666-690`）：`V` 的像 = `V \ {u}` 换入 `f u t`。 -/
private theorem w5cB3_image_V_eq
    {a b : ℝ} {V : Set V3} {f : V3 → ℝ → V3} {u : V3}
    (hu : u ∈ V)
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') :
    ∀ t ∈ Icc a b, (fun z => f z t) '' V = insert (f u t) (V \ {u}) := by
  intro t ht
  have h := w5cB3_image_sdiff (a := a) (b := b) (V := V) (f := f) (u := u) hpin
    t ht (x := V) (Set.Subset.refl V)
  rw [h, if_pos hu, Set.union_singleton]

/-- 分段 3（HOL `lunar_deform.hl:700-760`）：分离窗口 `hsep`（`DISJTINCT_PROPERTY`
输出形）下，`V` 内 2 元集的形变像仍是 2 元集（边像保基数）。 -/
private theorem w5cB3_image_ncard_two
    {a b : ℝ} {V : Set V3} {f : V3 → ℝ → V3} {u : V3} {e : ℝ}
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (hsep : ∀ t u', -e < t ∧ t < e ∧ u' ∈ V ∧ u' ≠ u → f u t ≠ f u' t) :
    ∀ t ∈ Icc a b, -e < t → t < e → ∀ x ⊆ V, x.Finite → x.ncard = 2 →
      ((fun z => f z t) '' x).ncard = 2 := by
  intro t ht hte1 hte2 x hx hxfin hx2
  have hdrop := w5cB3_image_sdiff (a := a) (b := b) (V := V) (f := f) (u := u) hpin
    t ht x hx
  rw [hdrop]
  by_cases hux : u ∈ x
  · rw [if_pos hux, Set.union_singleton]
    have hx1 : (x \ {u}).ncard = 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem hux, hx2]
    have hnot : f u t ∉ x \ {u} := by
      intro hmem
      have hV' : f u t ∈ V := hx hmem.1
      have hne : f u t ≠ u := hmem.2
      have hfix : f (f u t) t = f u t := hpin (f u t) hV' (Ne.symm hne) t ht
      exact (hsep t (f u t) ⟨hte1, hte2, hV', hne⟩) hfix.symm
    rw [Set.ncard_insert_of_notMem hnot hxfin.sdiff, hx1]
  · rw [if_neg hux, Set.union_empty]
    have hxs : x \ {u} = x := by
      ext y
      exact ⟨fun hy => hy.1, fun hy => ⟨hy, fun h => hux (h ▸ hy)⟩⟩
    rw [hxs, hx2]

/-- 分段 4 助件：`affineSpan {0, v, u}` 的显式线性坐标
（`affineCombination` 提取 → `Fin 3` 三槽拆分）。 -/
private theorem w5cB3_affineSpan_triple_repr {x v u : V3}
    (h : x ∈ (affineSpan ℝ ({0, v, u} : Set V3) : Set V3)) :
    ∃ c1 c2 : ℝ, x = c1 • v + c2 • u := by
  classical
  let p : Fin 3 → V3 := fun j => if j = 0 then 0 else if j = 1 then v else u
  have hrange : Set.range p = ({0, v, u} : Set V3) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j
      · simp [p]
      · simp [p]
      · simp [p]
    · intro hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact ⟨0, by simp [p]⟩
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact ⟨1, by simp [p]⟩
      · rw [Set.mem_singleton_iff] at hz
        exact ⟨2, by simp [p, hz]⟩
  obtain ⟨s, W, hWsum, hxW⟩ :=
    (mem_affineSpan_iff_eq_affineCombination ℝ V3 (p1 := x) (p := p)).mp (by
      rw [hrange]; exact h)
  have hlin : s.affineCombination ℝ p W = ∑ j ∈ s, W j • p j :=
    s.affineCombination_eq_linear_combination p W hWsum
  set W' : Fin 3 → ℝ := fun j => if j ∈ s then W j else 0 with hW'
  have hstep1 : ∑ j ∈ s, W j • p j = ∑ j ∈ s, W' j • p j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hW']
    simp [hj]
  have hstep2 : ∑ j ∈ s, W' j • p j = ∑ j : Fin 3, W' j • p j := by
    refine Finset.sum_subset (Finset.subset_univ s) ?_
    intro j _ hj
    rw [hW']
    simp [hj]
  rw [Fin.sum_univ_three] at hstep2
  refine ⟨W' 1, W' 2, ?_⟩
  rw [hxW, hlin, hstep1, hstep2]
  simp [p]

/-- 分段 4（HOL `lunar_deform.hl:690-1020`）：`uh = u - ((u·v)/(v·v)) v` 连续窗口
`d`；`|t| < d` 且 `t ∈ Icc a b` 时 `f u t ∈ affGt {0, v} {u}`（HOL 的
`! t. --d < t /\ t < d /\ t IN real_interval (a,b) ==> f u t IN aff_gt {0,v} {u}`）。 -/
private theorem w5cB3_affGt_window
    {a b : ℝ} {V : Set V3} {E : Set (Set V3)} {f : V3 → ℝ → V3} {u v w : V3}
    (hl : Lunar v w V E)
    (hnc : ¬ Collinear ℝ ({0, v, u} : Set V3))
    (hu0 : f u 0 = u) (hcu : ContinuousAt (f u) 0)
    (haff : ∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t| < d → t ∈ Icc a b →
      f u t ∈ affGt {0, v} {u} := by
  have hcol : Collinear ℝ ({0, v, w} : Set V3) := hl.2.2.2
  have h0v : (0 : V3) ≠ v := by
    intro he
    exact hnc (collinear3_of_eq (v := 0) (w := v) (w1 := u) he.symm)
  have hv0 : v ≠ 0 := Ne.symm h0v
  have huv : u ≠ v := by
    intro he
    apply hnc
    have hset : ({0, v, u} : Set V3) = ({0, v} : Set V3) := by
      rw [he]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ (0 : V3) v
  have hu0' : u ≠ 0 := by
    intro he
    apply hnc
    have hset : ({0, v, u} : Set V3) = ({0, v} : Set V3) := by
      rw [he]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ (0 : V3) v
  set c : ℝ := (u ⬝ᵥ v) / (v ⬝ᵥ v) with hc
  set uh : V3 := u - c • v with huh
  have hvv : v ⬝ᵥ v ≠ 0 := by
    intro hzero
    have h2 : ‖v‖ ^ 2 = (0 : ℝ) := by rw [norm_sq_eq_dot]; exact hzero
    have h3 : ‖v‖ = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
    exact hv0 (norm_eq_zero.mp h3)
  have hc_mul : c * (v ⬝ᵥ v) = u ⬝ᵥ v := by
    rw [hc]
    exact div_mul_cancel₀ _ hvv
  have horth : uh ⬝ᵥ v = 0 := by
    simp only [huh, WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct,
      smul_dotProduct, smul_eq_mul]
    rw [hc_mul, sub_self]
  have horth' : v ⬝ᵥ uh = 0 := by rw [dotProduct_comm]; exact horth
  have huhne : uh ≠ 0 := by
    intro hzero
    have hueq : u = c • v := by
      have h1 : u - c • v = 0 := hzero
      exact sub_eq_zero.mp h1
    apply hnc
    apply (collinear3_iff_smul (v := (0 : V3)) (w := v) (w1 := u) hv0).mpr
    exact ⟨c, by rw [hueq]; simp⟩
  have huhmem : uh ∈ affGt {0, v} {u} := by
    rw [affGt_pair_iff (v0 := (0 : V3)) (v1 := v) (x := u) (y := uh) h0v hu0' huv]
    refine ⟨1, one_pos, -c, ?_⟩
    simp only [huh, one_smul, sub_zero]
    module
  obtain ⟨d, hd0, hd⟩ := Metric.continuousAt_iff.mp hcu ‖uh‖ (norm_pos_iff.mpr huhne)
  refine ⟨d, hd0, ?_⟩
  intro t htI htIcc
  have hspan : (affineSpan ℝ ({0, v, w, u} : Set V3) : Set V3) =
      affineSpan ℝ ({0, v, u} : Set V3) := by
    have hwmem : w ∈ (affineSpan ℝ ({0, v} : Set V3) : Set V3) :=
      hcol.mem_affineSpan_of_mem_of_ne (p₁ := (0 : V3)) (p₂ := v) (p₃ := w)
        (by simp) (by simp) (by simp) h0v
    have hwmem' : w ∈ (affineSpan ℝ ({0, v, u} : Set V3) : Set V3) := by
      have hsub : ({0, v} : Set V3) ⊆ ({0, v, u} : Set V3) := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto
      exact affineSpan_mono ℝ hsub hwmem
    have hset : ({0, v, w, u} : Set V3) = insert w ({0, v, u} : Set V3) := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset, affineSpan_insert_eq_affineSpan ℝ hwmem']
  obtain ⟨c1, c2, hrepr⟩ := w5cB3_affineSpan_triple_repr (v := v) (u := u) (x := f u t) (by
    rw [← hspan]
    exact haff t htIcc)
  have hdist : dist (f u t) (f u 0) < ‖uh‖ := hd (by
    rw [Real.dist_eq, sub_zero]
    exact htI)
  have hdist' : ‖f u t - f u 0‖ < ‖uh‖ := by
    rw [dist_eq_norm] at hdist
    exact hdist
  have hnorm2 : ‖f u t - f u 0‖ ^ 2 < ‖uh‖ ^ 2 := by
    nlinarith [norm_nonneg (f u t - f u 0), norm_nonneg uh]
  have hdecomp : f u t - f u 0 = (c1 + c2 * c - c) • v + (c2 - 1) • uh := by
    rw [hrepr, hu0]
    have huu : u = uh + c • v := by
      rw [huh]; abel
    rw [huu]
    module
  have hinner : inner ℝ ((c1 + c2 * c - c) • v) ((c2 - 1) • uh) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, inner_eq_dot, horth']
    ring
  have hsq : ‖(c1 + c2 * c - c) • v + (c2 - 1) • uh‖ ^ 2
      = ‖(c1 + c2 * c - c) • v‖ ^ 2 + ‖(c2 - 1) • uh‖ ^ 2 := by
    have h := (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
      ((c1 + c2 * c - c) • v) ((c2 - 1) • uh)).mpr hinner
    simpa [pow_two] using h
  have hsmul1 : ‖(c1 + c2 * c - c) • v‖ ^ 2 = (c1 + c2 * c - c) ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hsmul2 : ‖(c2 - 1) • uh‖ ^ 2 = (c2 - 1) ^ 2 * ‖uh‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hlt : (c1 + c2 * c - c) ^ 2 * ‖v‖ ^ 2 + (c2 - 1) ^ 2 * ‖uh‖ ^ 2 < ‖uh‖ ^ 2 := by
    rw [← hsmul1, ← hsmul2, ← hsq, ← hdecomp]
    exact hnorm2
  have hc2pos : 0 < c2 := by
    by_contra hcon
    push_neg at hcon
    have h1 : (1 : ℝ) ≤ (c2 - 1) ^ 2 := by
      have hh : 0 ≤ c2 * (c2 - 2) := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      nlinarith
    have h2 : 0 ≤ (c1 + c2 * c - c) ^ 2 * ‖v‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have h3 : 0 ≤ ‖uh‖ ^ 2 := sq_nonneg _
    have h4 : ‖uh‖ ^ 2 ≤ (c2 - 1) ^ 2 * ‖uh‖ ^ 2 := by
      calc ‖uh‖ ^ 2 = 1 * ‖uh‖ ^ 2 := (one_mul _).symm
        _ ≤ (c2 - 1) ^ 2 * ‖uh‖ ^ 2 := mul_le_mul_of_nonneg_right h1 h3
    linarith
  rw [affGt_pair_iff (v0 := (0 : V3)) (v1 := v) (x := u) (y := f u t) h0v hu0' huv]
  refine ⟨c2, hc2pos, c1, ?_⟩
  rw [hrepr]
  module

/-- 分段 5 助件：`z ∈ affGt {0, v} {z}`（系数 `1 · z`；免互异）。 -/
private theorem w5cB3_mem_affGt_self (z v : V3) : z ∈ affGt ({0, v} : Set V3) {z} := by
  classical
  have hfin : ({0, v} ∪ {z} : Set V3).Finite :=
    ((Set.finite_singleton v).insert 0).union (Set.finite_singleton z)
  have hz : z ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_union_right _ (Set.mem_singleton z)
  refine ⟨fun w => if w = z then 1 else 0, hfin, ?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single z]
    · simp
    · intro c _ hc
      simp [hc]
    · intro hznot
      exact absurd hz hznot
  · intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    simp
  · rw [Finset.sum_eq_single z]
    · simp
    · intro c _ hc
      simp [hc]
    · intro hznot
      exact absurd hz hznot

/-- 分段 5（HOL `lunar_deform.hl:999-1017`）：窗口内 `V` 的每个顶点 `u'` 满足
`f u' t ∈ affGt {0, v} {u'}`（`u' ≠ u` 用钉住，`u' = u` 用分段 4）。 -/
private theorem w5cB3_affGt_window_all
    {a b : ℝ} {V : Set V3} {E : Set (Set V3)} {f : V3 → ℝ → V3} {u v w : V3}
    (hl : Lunar v w V E)
    (hnc : ¬ Collinear ℝ ({0, v, u} : Set V3))
    (hu0 : f u 0 = u) (hcu : ContinuousAt (f u) 0)
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (haff : ∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t| < d → t ∈ Icc a b → ∀ u' ∈ V,
      f u' t ∈ affGt ({0, v} : Set V3) {u'} := by
  obtain ⟨d, hd0, hd⟩ := w5cB3_affGt_window (a := a) (b := b) (V := V) (E := E)
    (f := f) (u := u) (v := v) (w := w) hl hnc hu0 hcu haff
  refine ⟨d, hd0, ?_⟩
  intro t ht htIcc u' hu'
  by_cases hzu : u' = u
  · subst hzu
    exact hd t ht htIcc
  · have hfix : f u' t = u' := hpin u' hu' (Ne.symm hzu) t htIcc
    rw [hfix]
    exact w5cB3_mem_affGt_self u' v

private theorem w5cB3_lunar_window
    {a b : ℝ} {V : Set V3} {E : Set (Set V3)} {f : V3 → ℝ → V3} {u v w : V3} {e : ℝ}
    (hl : Lunar v w V E) (huv : u ≠ v) (huw : u ≠ w)
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (ha : a < 0) (hb : 0 < b) (he : 0 < e)
    (hsep : ∀ t, -e < t → t < e → t ∈ Icc a b →
      ∀ s : Set V3, s ∈ (fun s => (fun z => f z t) '' s) '' E →
        ∀ u' : V3, u' ∈ (fun z => f z t) '' V →
        affGt ({0} : Set V3) s ∩ affLt ({0} : Set V3) {u'} = ∅) :
    ∃ e' : ℝ, 0 < e' ∧ ∀ t : ℝ, -e' < t ∧ t < e' →
      Lunar v w ((fun z => f z t) '' V) ((fun s => (fun z => f z t) '' s) '' E) := by
  refine ⟨min (min (-a) b) e, ?_, ?_⟩
  · exact lt_min (lt_min (by linarith) hb) he
  · intro t ht
    have hle1 : min (min (-a) b) e ≤ e := min_le_right _ _
    have hle2 : min (min (-a) b) e ≤ -a := le_trans (min_le_left _ _) (min_le_left _ _)
    have hle3 : min (min (-a) b) e ≤ b := le_trans (min_le_left _ _) (min_le_right _ _)
    have hte1 : -e < t := by linarith [ht.1]
    have hte2 : t < e := by linarith [ht.2]
    have hta : a ≤ t := by linarith [ht.1]
    have htb : t ≤ b := by linarith [ht.2]
    have htIcc : t ∈ Icc a b := ⟨hta, htb⟩
    obtain ⟨hfv, hfw, hsub, hvw⟩ := w5cB3_image_preserves_lunar (a := a) (b := b)
      (V := V) (E := E) (f := f) (u := u) (v := v) (w := w) hl huv huw hpin t htIcc
    refine ⟨?_, hsub, hvw, hl.2.2.2⟩
    intro hcirc
    unfold Circular at hcirc
    obtain ⟨v', w', u', hE, hV, hne⟩ := hcirc
    exact hne (hsep t hte1 hte2 htIcc {v', w'} hE u' hV)

/-! ## w5cB4 kit (W5c-B 第四波): `SUB_LUNAR_DEFORM_LEMMA` 段 7 / 7b / 8 的条件形

HOL 源 `lunar_deform.hl:695-788`（段 7a）、`1018-1532`（段 7b）、`1533-1750`
（段 8）。上游 twins（`HKIRPEP_ALT` / `LUNAR_IMP_IN_TWO_HAFLS_PLANE`）仍为
`sorry`，故本区把它们的结论作为**显式前提**，交付一面标准三的条件件；
`DELIVERY.md` §2 给出逐件缺口与下一波总装接口。  UPDATE（w5cB5/B6 波）：
LA5 fan-rho 物质件已全部净证并经 AzimBridge `localFanEquiv_p35` 桥在本文件
消费（原"仍 sorry、不可消费"注记失效）；LA6 twin `CARD_V_TWO_HAFL_CIRCLE`
等仍 sorried。 -/

/-- 段 7a（HOL `lunar_deform.hl:695-788`）：设 `V` 的点都可写成
`rhoNode1 FF` 在 `v` 上的迭代（`LOFA_IMP_LT_CARD_SET_V` 的轨道覆盖形），且
`w = rho^[i] v`、两半集合等于相应半锥与 `V` 的交，则 `u ∈ V \ {v,w}` 落在
`v` 侧或 `w` 侧的半锥内。 -/
private theorem w5cB4_mem_half_of_orbits
    {V : Set V3} {FF : Set (V3 × V3)} {u v w : V3}
    (huv : u ≠ v) (huw : u ≠ w)
    (horb : ∃ n : ℕ, n < Set.ncard V ∧ u = (rhoNode1 FF)^[n] v)
    {i j : ℕ} (hij : i + j = Set.ncard V)
    (hwi : w = (rhoNode1 FF)^[i] v)
    (hsv : {z | ∃ l, 0 < l ∧ l < i ∧ z = (rhoNode1 FF)^[l] v} =
      affGt ({0, v} : Set V3) {rhoNode1 FF v} ∩ V)
    (hsw : {z | ∃ l, 0 < l ∧ l < j ∧ z = (rhoNode1 FF)^[l] w} =
      affGt ({0, v} : Set V3) {ivsRhoNode1 FF v} ∩ V)
    (hivs : affGt ({0, v} : Set V3) {ivsRhoNode1 FF v} =
      affGt ({0, w} : Set V3) {rhoNode1 FF w}) :
    u ∈ affGt ({0, v} : Set V3) {rhoNode1 FF v} ∨
      u ∈ affGt ({0, w} : Set V3) {rhoNode1 FF w} := by
  obtain ⟨n, hnV, hun⟩ := horb
  have hn0 : n ≠ 0 := by
    intro h0
    exact huv (by rw [hun, h0, Function.iterate_zero_apply])
  have hne : n ≠ i := by
    intro he
    exact huw (by rw [hun, he]; exact hwi.symm)
  by_cases hni : n < i
  · left
    have hmem : u ∈ {z | ∃ l, 0 < l ∧ l < i ∧ z = (rhoNode1 FF)^[l] v} :=
      ⟨n, Nat.pos_of_ne_zero hn0, hni, hun⟩
    rw [hsv] at hmem
    exact hmem.1
  · right
    have hin : i < n := by omega
    set m : ℕ := n - i with hm
    have hnm : n = m + i := by omega
    have hm0 : m ≠ 0 := by omega
    have hmlt : m < j := by omega
    have hum : u = (rhoNode1 FF)^[m] w := by
      rw [hun, hnm, Function.iterate_add_apply, ← hwi]
    have hmem : u ∈ {z | ∃ l, 0 < l ∧ l < j ∧ z = (rhoNode1 FF)^[l] w} :=
      ⟨m, Nat.pos_of_ne_zero hm0, hmlt, hum⟩
    rw [hsw] at hmem
    rw [hivs] at hmem
    exact hmem.1

/-- 段 7a 的 twin 消费形：把 `HKIRPEP_ALT_p37` 的整个结论（LA6 twin
`Local_lemmas1.CARD_V_TWO_HAFL_CIRCLE` 链的输出）作为显式前提，加上 `V` 的
`v`-轨道覆盖与 `AFF_IVS_RHO_NODE_EQQ` 的半锥等式，交出段 7a 的析取
（标准三，不消费 sorry）。 -/
private theorem w5cB4_mem_half_of_hkir
    {V : Set V3} {FF : Set (V3 × V3)} {u v w : V3}
    (huv : u ≠ v) (huw : u ≠ w)
    (horb : ∃ n : ℕ, n < Set.ncard V ∧ u = (rhoNode1 FF)^[n] v)
    (hivs : affGt ({0, v} : Set V3) {ivsRhoNode1 FF v} =
      affGt ({0, w} : Set V3) {rhoNode1 FF w})
    (hkir :
      (∀ u' ∈ V \ {v, w}, interiorAngle1 0 FF u' = Real.pi) ∧
      0 < interiorAngle1 0 FF v ∧
      interiorAngle1 0 FF v ≤ Real.pi ∧
      interiorAngle1 0 FF v = interiorAngle1 0 FF w ∧
      ∃ i j : ℕ, i + j = Set.ncard V ∧ i < Set.ncard V ∧ i ≠ 0 ∧ i ≠ 1 ∧
        w = (rhoNode1 FF)^[i] v ∧
        {z | ∃ l, 0 < l ∧ l < i ∧ z = (rhoNode1 FF)^[l] v} =
          affGt ({0, v} : Set V3) {rhoNode1 FF v} ∩ V ∧
        j < Set.ncard V ∧ j ≠ 0 ∧ j ≠ 1 ∧
        v = (rhoNode1 FF)^[j] w ∧
        {z | ∃ l, 0 < l ∧ l < j ∧ z = (rhoNode1 FF)^[l] w} =
          affGt ({0, v} : Set V3) {ivsRhoNode1 FF v} ∩ V) :
    u ∈ affGt ({0, v} : Set V3) {rhoNode1 FF v} ∨
      u ∈ affGt ({0, w} : Set V3) {rhoNode1 FF w} := by
  obtain ⟨_, _, _, _, i, j, hij, _, _, _, hwi, hsv, _, _, _, _, hsw⟩ := hkir
  exact w5cB4_mem_half_of_orbits (V := V) (FF := FF) (u := u) (v := v) (w := w)
    huv huw horb hij hwi hsv hsw hivs

/-- 半锥不含基点 `0`（基点只在支撑集里，`dot` 系数为 `0`）：非共线
`{0, u, dir}` 下 `affGt {0,u} {dir}` 的点不等于 `0`（段 7b 的 `0 ∉ s`
边条件）。 -/
private theorem w5cB4_zero_ne_of_mem {u dir z : V3}
    (hnc : ¬ Collinear ℝ ({(0 : V3), u, dir} : Set V3))
    (hz : z ∈ affGt ({(0 : V3), u} : Set V3) {dir}) : z ≠ (0 : V3) := by
  have h0u : (0 : V3) ≠ u :=
    fun he => hnc (collinear3_of_eq (v := (0 : V3)) (w := u) (w1 := dir) he.symm)
  have h0d : (0 : V3) ≠ dir :=
    fun he => hnc (collinear3_pair_left (v0 := (0 : V3)) (v1 := u) (x := dir) he.symm)
  have hud : u ≠ dir :=
    fun he => hnc (collinear3_pair_right (v0 := (0 : V3)) (v1 := u) (x := dir) he.symm)
  intro hz0
  obtain ⟨t1, t2, t3, ht3, hsum, hze⟩ :=
    w5cB_affGt_2_1_mp (x := (0 : V3)) (u := u) (v := dir) h0u h0d hud hz
  have hlin : t2 • u + t3 • dir = (0 : V3) := by
    have h' : (0 : V3) = t1 • (0 : V3) + t2 • u + t3 • dir := hz0.symm.trans hze
    simpa using h'.symm
  have ht3ne : t3 ≠ 0 := ne_of_gt ht3
  have hdir : dir = (-(t2 / t3)) • u := by
    have h1 : t3 • dir = (-t2) • u := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
      exact hlin
    refine w5cB_smul_left_cancel ht3ne ?_
    have hcoef : t3 * (-(t2 / t3)) = -t2 := by
      rw [mul_neg, mul_comm t3 (t2 / t3), div_mul_cancel₀ t2 ht3ne]
    rw [h1, smul_smul, hcoef]
  exact hnc ((collinear3_iff_smul (v := (0 : V3)) (w := u) (w1 := dir)
    (Ne.symm h0u)).mpr ⟨-(t2 / t3), by simpa using hdir⟩)

/-- 段 7b 的锥传递（`TOW_POINTS_IN_IMP_AFF_GT_SUBSET` 的直接消费）：两个像点
落在同一半锥时，边像（二元集）生成的锥也落在该半锥。 -/
private theorem w5cB4_cone_subset_of_half {x u dir a b : V3}
    (hnc : ¬ Collinear ℝ ({x, u, dir} : Set V3))
    (ha : a ∈ affGt ({x, u} : Set V3) {dir})
    (hb : b ∈ affGt ({x, u} : Set V3) {dir})
    (hxa : x ≠ a) (hxb : x ≠ b) :
    affGt ({x} : Set V3) {a, b} ⊆ affGt ({x, u} : Set V3) {dir} := by
  have hxu : x ≠ u :=
    fun he => hnc (collinear3_of_eq (v := x) (w := u) (w1 := dir) he.symm)
  have hxd : x ≠ dir :=
    fun he => hnc (collinear3_pair_left (v0 := x) (v1 := u) (x := dir) he.symm)
  have hud : u ≠ dir :=
    fun he => hnc (collinear3_pair_right (v0 := x) (v1 := u) (x := dir) he.symm)
  refine TOW_POINTS_IN_IMP_AFF_GT_SUBSET_p37 ?_ ha hb ?_
  · refine Set.disjoint_left.mpr ?_
    intro q hq hqd
    rw [Set.mem_singleton_iff] at hqd
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact hxd hqd
    · exact hud hqd
  · refine Set.disjoint_left.mpr ?_
    intro q hq hqd
    rw [Set.mem_singleton_iff] at hq
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hqd
    rcases hqd with rfl | rfl
    · exact hxa hq.symm
    · exact hxb hq.symm

/-- 段 7b 的边像步：若边 `x = {a,b}` 的两端点像都落在同一半锥
`affGt {0,u} {dir}`，则该边像 `(f · t) '' x` 生成的锥也落在其中。 -/
private theorem w5cB4_cone_image_edge {t : ℝ} {f : V3 → ℝ → V3} {x : Set V3}
    {a b u dir : V3}
    (hx : x = {a, b})
    (hnc : ¬ Collinear ℝ ({(0 : V3), u, dir} : Set V3))
    (ha : f a t ∈ affGt ({(0 : V3), u} : Set V3) {dir})
    (hb : f b t ∈ affGt ({(0 : V3), u} : Set V3) {dir}) :
    affGt ({0} : Set V3) ((fun z => f z t) '' x) ⊆
      affGt ({(0 : V3), u} : Set V3) {dir} := by
  subst hx
  have himg : (fun z => f z t) '' ({a, b} : Set V3) = ({f a t, f b t} : Set V3) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      rcases hy with rfl | rfl <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      rcases hz with rfl | rfl
      · exact ⟨a, Or.inl rfl, rfl⟩
      · exact ⟨b, Or.inr rfl, rfl⟩
  rw [himg]
  exact w5cB4_cone_subset_of_half (x := (0 : V3)) (u := u) (dir := dir) hnc ha hb
    (Ne.symm (w5cB4_zero_ne_of_mem hnc ha)) (Ne.symm (w5cB4_zero_ne_of_mem hnc hb))

/-- 段 8 的集合步：边锥落在半锥 `H` 内、且 `H` 与对侧仿射负锥不交时，
边锥与 `affLt {0} {u'}` 不交（HOL 1533-1750 的 `SET_RULE` 收口形）。 -/
private theorem w5cB4_disjoint_of_cone {s : Set V3} {u' : V3} {H : Set V3}
    (hsub : affGt ({0} : Set V3) s ⊆ H)
    (hdisj : H ∩ affLt ({0} : Set V3) {u'} = ∅) :
    affGt ({0} : Set V3) s ∩ affLt ({0} : Set V3) {u'} = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro z hz
  have h1 : z ∈ H := hsub hz.1
  have h2 : z ∈ H ∩ affLt ({0} : Set V3) {u'} := ⟨h1, hz.2⟩
  rw [hdisj] at h2
  exact (Set.notMem_empty z) h2

/-- 段 7b 的边扫描：每条边经 `EDGE_IN_LOCAL_FAN_DET_RHO_NODE` 写成
`{v', rho v'}`，两端点像同属一半时，边像锥落在那半（`hdet` 与 `hhalf`
分别承接 LA5 的边 rho 形与 fan 侧分解，即 HOL 1018-1532 的物质前提）。 -/
private theorem w5cB4_cover_of_edges
    {e : ℝ} {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {f : V3 → ℝ → V3} {u v w : V3}
    (hdet : ∀ x ∈ E, ∃ v' ∈ V, x = {v', rhoNode1 FF v'})
    (hncv : ¬ Collinear ℝ ({(0 : V3), v, rhoNode1 FF v} : Set V3))
    (hncw : ¬ Collinear ℝ ({(0 : V3), w, rhoNode1 FF w} : Set V3))
    (hhalf : ∀ t : ℝ, -e < t → t < e →
      ∀ x ∈ E, ∀ v' ∈ V, x = {v', rhoNode1 FF v'} →
        ((f v' t ∈ affGt ({0, v} : Set V3) {rhoNode1 FF v} ∧
            f (rhoNode1 FF v') t ∈ affGt ({0, v} : Set V3) {rhoNode1 FF v}) ∨
          (f v' t ∈ affGt ({0, w} : Set V3) {rhoNode1 FF w} ∧
            f (rhoNode1 FF v') t ∈ affGt ({0, w} : Set V3) {rhoNode1 FF w}))) :
    ∀ t : ℝ, -e < t → t < e → t ∈ Icc a b →
      ∀ s : Set V3, s ∈ (fun s => (fun z => f z t) '' s) '' E →
        affGt ({0} : Set V3) s ⊆ affGt ({0, v} : Set V3) {rhoNode1 FF v} ∨
        affGt ({0} : Set V3) s ⊆ affGt ({0, w} : Set V3) {rhoNode1 FF w} := by
  intro t ht1 ht2 _
  rintro s ⟨x, hxE, rfl⟩
  obtain ⟨v', hv'V, hx⟩ := hdet x hxE
  rcases hhalf t ht1 ht2 x hxE v' hv'V hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (w5cB4_cone_image_edge (f := f) (t := t) hx hncv h1 h2)
  · exact Or.inr (w5cB4_cone_image_edge (f := f) (t := t) hx hncw h1 h2)

/-- 段 8 的装配接口：窗口内 (i) 每条边像锥落在 `v` 半或 `w` 半、(ii) 每半与
每个像点的 `affLt {0}` 不交，则 `SUB_LUNAR_DEFORM_LEMMA` 的 `hsep` 成立，
由分段 6（`w5cB3_lunar_window`）收口。前提 (i)/(ii) 精确承接段 7b/8 的
HOL 输出（见 `DELIVERY.md` §2）。 -/
private theorem w5cB4_lunar_of_cover
    {a b e : ℝ} {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {f : V3 → ℝ → V3} {u v w : V3}
    (hl : Lunar v w V E) (huv : u ≠ v) (huw : u ≠ w)
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (ha : a < 0) (hb : 0 < b) (he : 0 < e)
    (hcover : ∀ t : ℝ, -e < t → t < e → t ∈ Icc a b →
      ∀ s : Set V3, s ∈ (fun s => (fun z => f z t) '' s) '' E →
        affGt ({0} : Set V3) s ⊆ affGt ({0, v} : Set V3) {rhoNode1 FF v} ∨
        affGt ({0} : Set V3) s ⊆ affGt ({0, w} : Set V3) {rhoNode1 FF w})
    (hdv : ∀ t : ℝ, -e < t → t < e → t ∈ Icc a b → ∀ u' : V3,
      u' ∈ (fun z => f z t) '' V →
        affGt ({0, v} : Set V3) {rhoNode1 FF v} ∩ affLt ({0} : Set V3) {u'} = ∅)
    (hdw : ∀ t : ℝ, -e < t → t < e → t ∈ Icc a b → ∀ u' : V3,
      u' ∈ (fun z => f z t) '' V →
        affGt ({0, w} : Set V3) {rhoNode1 FF w} ∩ affLt ({0} : Set V3) {u'} = ∅) :
    ∃ e' : ℝ, 0 < e' ∧ ∀ t : ℝ, -e' < t ∧ t < e' →
      Lunar v w ((fun z => f z t) '' V) ((fun s => (fun z => f z t) '' s) '' E) := by
  refine w5cB3_lunar_window (a := a) (b := b) (V := V) (E := E) (f := f)
    (u := u) (v := v) (w := w) (e := e) hl huv huw hpin ha hb he ?_
  intro t ht1 ht2 htIcc s hs u' hu'
  rcases hcover t ht1 ht2 htIcc s hs with hsub | hsub
  · exact w5cB4_disjoint_of_cone hsub (hdv t ht1 ht2 htIcc u' hu')
  · exact w5cB4_disjoint_of_cone hsub (hdw t ht1 ht2 htIcc u' hu')

/-- `SUB_LUNAR_DEFORM_LEMMA_p37` 的显式条件形：签名与目标逐字一致，另挂窗口
半径 `d` 与段 7b/8 的两条 HOL 输出（边像锥落半、半锥与 `affLt` 不交）。
target 体中 `d` 由分段 4/5 的 `w5cB3_affGt_window_all` 产出（其非共线前提
`¬Collinear {0,v,u}` 由已净证 `LOCAL_CONVEX_NOT_COLLINEAR_p37` 提供
（la37-g5-w1）），
产出后本件即给出目标的结论（标准三）。 -/
private theorem w5cB4_SUB_LUNAR_DF_cond
    {a b : ℝ} {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {f : V3 → ℝ → V3} {u v w : V3}
    (_hV : V.Finite) (_hcf : ConvexLocalFan V E FF) (hl : Lunar v w V E)
    (_hE : ∀ x ∈ E, x ⊆ V) (_hu0 : f u 0 = u) (_hcu : ContinuousAt (f u) 0)
    (_hang : interiorAngle1 0 FF v < Real.pi) (ha : a < 0) (hb : 0 < b)
    (_hu : u ∈ V) (huv : u ≠ v) (huw : u ≠ w)
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (_haff : ∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3))
    (d : ℝ) (hd : 0 < d)
    (hcover : ∀ t : ℝ, -d < t → t < d → t ∈ Icc a b →
      ∀ s : Set V3, s ∈ (fun s => (fun z => f z t) '' s) '' E →
        affGt ({0} : Set V3) s ⊆ affGt ({0, v} : Set V3) {rhoNode1 FF v} ∨
        affGt ({0} : Set V3) s ⊆ affGt ({0, w} : Set V3) {rhoNode1 FF w})
    (hdv : ∀ t : ℝ, -d < t → t < d → t ∈ Icc a b → ∀ u' : V3,
      u' ∈ (fun z => f z t) '' V →
        affGt ({0, v} : Set V3) {rhoNode1 FF v} ∩ affLt ({0} : Set V3) {u'} = ∅)
    (hdw : ∀ t : ℝ, -d < t → t < d → t ∈ Icc a b → ∀ u' : V3,
      u' ∈ (fun z => f z t) '' V →
        affGt ({0, w} : Set V3) {rhoNode1 FF w} ∩ affLt ({0} : Set V3) {u'} = ∅) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      Lunar v w ((fun z => f z t) '' V) ((fun s => (fun z => f z t) '' s) '' E) :=
  w5cB4_lunar_of_cover (a := a) (b := b) (e := d) (V := V) (E := E) (FF := FF)
    (f := f) (u := u) (v := v) (w := w) hl huv huw hpin ha hb hd hcover hdv hdw

/-! ## The SUB_LUNAR_DEFORM_LEMMA giant (source 528-1830) -/

/-- HOL `SUB_LUNAR_DEFORM_LEMMA` (lunar_deform.hl:528): the lunar
`Lunar` conclusion survives the pinned deformation.  GIANT (sorry):
needs the `Local_lemmas.HKIRPEP` + azim/cross iteration kit below. -/
theorem SUB_LUNAR_DEFORM_LEMMA_p37 {a b : ℝ} {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → ℝ → V3} {u v w : V3}
    (_hV : V.Finite) (_hcf : ConvexLocalFan V E FF) (_hl : Lunar v w V E)
    (_hE : ∀ x ∈ E, x ⊆ V) (_hu0 : f u 0 = u) (_hcu : ContinuousAt (f u) 0)
    (_hang : interiorAngle1 0 FF v < Real.pi) (_ha : a < 0) (_hb : 0 < b)
    (_hu : u ∈ V) (_hv : u ≠ v) (_hw : u ≠ w)
    (_hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (_haff : ∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      Lunar v w ((fun z => f z t) '' V) ((fun s => (fun z => f z t) '' s) '' E) := by
  sorry

/-! ## The local-fan / hypermap-iso kit (source 1836-3160) -/

/-- HOL `LOCAL_FAN_SET_E` (lunar_deform.hl:1836).  NEEDS: fan substance
(`Local_lemmas1.LOCAL_RHO_NODE_PAIR_E` + `EDGE_IN_LOCAL_FAN_DET_RHO_NODE`);
the registry `LocalFan` stub carries no `E` data. -/
theorem LOCAL_FAN_SET_E_p37 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (_h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    {p : Set V3 | ∃ v ∈ V, p = {v, rhoNode1 FF v}} = E := by
  have h2 := w5cB5_to_localFan_p2 _h
  have hpros := LOCAL_FAN_RHO_NODE_PROS2 h2
  ext x
  constructor
  · rintro ⟨v, hvV, hvdef⟩
    have hd : (v, rhoNode1_p2 FF v) ∈ dartsOfHyp_p2 E V := by
      rw [LOFA_DARTS_FF_UNION_SWITCH_FF h2]
      exact Set.mem_union_left _ (hpros.2 v hvV)
    rw [hvdef]
    have hd' : (v, rhoNode1_p2 FF v) ∈ ordPairs_p2 E ∪ selfPairs_p2 E V := hd
    rcases Set.mem_or_mem_of_mem_union hd' with hd | hd
    · exact hd
    · exfalso
      obtain ⟨hfan, -, -, -, -, h2reg⟩ := _h
      simp only [selfPairs_p2, Set.mem_setOf_eq] at hd
      obtain ⟨-, hvV', hEE⟩ := hd
      have hee : (ee v E).ncard = 2 := h2reg v hvV
      have hdef : EE_p2 v E = ee v E := rfl
      rw [← hdef, hEE, Set.ncard_empty V3] at hee
      omega
  · intro hx
    obtain ⟨a, b, hab, hset⟩ := EDGE_FORM_IN_LOCAL_FAN_p37 _h hx
    have hxE : ({a, b} : Set V3) ∈ E := by rw [hset]; exact hx
    rw [← hset]
    rcases LOFA_IN_E_IMP_IN_FF h2 hxE with hd | hd
    · have hrho : rhoNode1 FF a = b := DETER_RHO_NODE h2 hd
      exact ⟨a, (WRGCVDR_BIJ h2).1 hd, by rw [hrho]⟩
    · have hrho : rhoNode1 FF b = a := DETER_RHO_NODE h2 hd
      refine ⟨b, (WRGCVDR_BIJ h2).1 hd, ?_⟩
      rw [hrho]
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

/-- HOL `LOCAL_FAN_FACE_FF` (lunar_deform.hl:1856).  NEEDS:
`Local_lemmas.LOCAL_FAN_RHO_NODE_PROS`/`PROS2` twins. -/
theorem LOCAL_FAN_FACE_FF_p37 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (_h : LocalFan V E FF) :
    {p : V3 × V3 | ∃ v ∈ V, p = (v, rhoNode1 FF v)} = FF := by
  have h2 := w5cB5_to_localFan_p2 _h
  have hpros := LOCAL_FAN_RHO_NODE_PROS2 h2
  ext p
  constructor
  · rintro ⟨v, hvV, hvdef⟩
    rw [hvdef]
    exact hpros.2 v hvV
  · intro hp
    have hp' : p = (p.1, rhoNode1_p2 FF p.1) := hpros.1 p hp
    exact ⟨p.1, (WRGCVDR_BIJ h2).1 hp, hp'⟩

/-- HOL `ORD_PAIRS_INJ_IMAGE` (lunar_deform.hl:1881): `ord_pairs` commutes
with a piecewise-injective vertex map. -/
theorem ORD_PAIRS_INJ_IMAGE_p37 {E : Set (Set V3)} {f : V3 → V3}
    (h : ∀ s ∈ E, Set.InjOn f s) :
    ordPairs_p4 ((fun s => f '' s) '' E) = (fun p => (f p.1, f p.2)) '' ordPairs_p4 E := by
  ext p
  constructor
  · intro hp
    obtain ⟨s, hsE, hseq⟩ := hp
    have hseq' : (f '' s : Set V3) = {p.1, p.2} := hseq
    have h1 : p.1 ∈ (f '' s : Set V3) := by rw [hseq']; simp
    have h2 : p.2 ∈ (f '' s : Set V3) := by rw [hseq']; simp
    obtain ⟨x, hxs, hx⟩ := h1
    obtain ⟨y, hys, hy⟩ := h2
    have hinj : Set.InjOn f s := h s hsE
    have hsset : s = {x, y} := by
      refine Set.Subset.antisymm ?_ ?_
      · intro z hz
        have hz0 : f z ∈ (f '' s : Set V3) := ⟨z, hz, rfl⟩
        have hz' : f z ∈ ({p.1, p.2} : Set V3) := by rwa [hseq'] at hz0
        rcases Set.mem_insert_iff.mp hz' with he | he
        · left; exact (hinj hxs hz (hx.trans he.symm)).symm
        · right; exact (hinj hys hz (hy.trans he.symm)).symm
      · intro z hz
        rcases Set.mem_insert_iff.mp hz with he | he
        · rw [he]; exact hxs
        · rw [he]; exact hys
    refine ⟨(x, y), ?_, ?_⟩
    · exact show {x, y} ∈ E from hsset ▸ hsE
    · rw [Prod.mk.injEq]; exact ⟨hx, hy⟩
  · rintro ⟨d, hd, rfl⟩
    refine ⟨{d.1, d.2}, hd, ?_⟩
    show f '' {d.1, d.2} = {f d.1, f d.2}
    rw [Set.image_insert_eq, Set.image_singleton]

/-- HOL `SET2_DETER` (lunar_deform.hl:1920): a two-point set is determined
by any two distinct members. -/
theorem SET2_DETER_p37 {x y a b : V3} {s : Set V3} (hs : s = {x, y}) (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) : s = {a, b} := by
  subst hs
  ext z
  constructor <;> intro hz <;>
    rcases Set.mem_insert_iff.mp hz with rfl | rfl <;>
    rcases Set.mem_insert_iff.mp ha with rfl | rfl <;>
    rcases Set.mem_insert_iff.mp hb with rfl | rfl <;> simp_all

/-- HOL `INJ_IMP_BIJ_IMAGE` (lunar_deform.hl:1929). -/
theorem INJ_IMP_BIJ_IMAGE_p37 {f : V3 → V3} {S S' : Set V3}
    (h : Set.InjOn f S) : Set.BijOn f S (f '' S) :=
  ⟨Set.mapsTo_image f S, h, Set.surjOn_image f S⟩

/-! ### B10 hypermap-iso kit (`w5cB10_*` private helpers)

The HOL proofs (`lunar_deform.hl:1938/2308/2612`) run the same core script
three times: `ELMS_OF_HYPERMAP_HYP` pins the HYP dart set to
`darts_of_hyp`, the local-fan face `FF` makes every neighbour set a
two-point set (`FF = face` + `dih2k`), and the transfer is then pure
set algebra on those two-point sets.  In this file the HYP dart set is
already `dartsOfHyp_p4`, and `LocalFan`'s 2-regular conjunct makes the
`self_pairs` branch empty, so the core script reduces to the helpers
below (no `ELMS_OF_HYPERMAP_HYP`, no `dih2k` card transfer needed). -/

/-- `LocalFan` has no isolated vertices: the 2-regular conjunct supplies an
edge at every vertex. -/
private theorem w5cB10_hedge {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : LocalFan V E FF) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  obtain ⟨_hfan, _x0, _hx0, _hFF, _hD, h2reg⟩ := hlf
  intro v hv
  have h2 : (EE_p4 v E).ncard = 2 := h2reg v hv
  by_contra hc
  have hempty : EE_p4 v E = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hc ⟨w, hw⟩
  rw [hempty, Set.ncard_empty] at h2
  omega

/-- Under `LocalFan` the HYP dart set is the fan dart set (no self-pairs). -/
private theorem w5cB10_hno {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : LocalFan V E FF) : dartsOfHyp_p4 E V = Fan.dart1OfFan V E :=
  (dartsOfHyp_p4_eq_dartsOfHyp_p3 E V).trans (hno_of_no_isolated (w5cB10_hedge hlf))

/-- The target-side counterpart of `w5cB10_hno`: the vertex bijection carries
the source edge set, so the deformed fan has no isolated vertices either. -/
private theorem w5cB10_hno_image {V V' : Set V3} {E E' : Set (Set V3)} {f : V3 → V3}
    (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hbij : Set.BijOn f V V')
    (hE : (fun s => f '' s) '' E = E') :
    dartsOfHyp_p4 E' V' = Fan.dart1OfFan V' E' := by
  have hedge' : ∀ v' ∈ V', ∃ w', {v', w'} ∈ E' := by
    intro v' hv'
    obtain ⟨v, hv, rfl⟩ := hbij.2.2 hv'
    obtain ⟨w, hw⟩ := hedge v hv
    refine ⟨f w, ?_⟩
    show ({f v, f w} : Set V3) ∈ E'
    rw [← hE]
    exact ⟨{v, w}, hw, by simp only [Set.image_insert_eq, Set.image_singleton]⟩
  exact (dartsOfHyp_p4_eq_dartsOfHyp_p3 E' V').trans (hno_of_no_isolated hedge')

/-- Two-point `azimCycle` swap (`_p4` form): on `{a, b}` the epsilon pick
at `a` is `b` (single-candidate specification, no azimuth comparison). -/
private theorem w5cB10_azimCycle_pair (a b v0 c : V3) (hab : a ≠ b) :
    azimCycle_p4 ({a, b} : Set V3) v0 c a = b := by
  unfold azimCycle_p4
  split
  · rename_i hsub
    have hb : b ∈ ({a, b} : Set V3) := by simp
    exact absurd (Set.mem_singleton_iff.mp (hsub hb)) hab.symm
  · rename_i _hsub
    let P : V3 → Prop := fun z => z ≠ a ∧ z ∈ ({a, b} : Set V3) ∧
      ∀ q ∈ ({a, b} : Set V3), q ≠ a →
        azim v0 c a z < azim v0 c a q ∨
          azim v0 c a z = azim v0 c a q ∧
            ‖projection (z - v0) (c - v0)‖ ≤ ‖projection (q - v0) (c - v0)‖
    have hbprop : P b := by
      refine ⟨hab.symm, by simp, ?_⟩
      intro q hq hqa
      rcases Set.mem_insert_iff.mp hq with rfl | hq
      · exact absurd rfl hqa
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        exact Or.inr ⟨rfl, le_refl _⟩
    have huniq : ∀ z, P z → z = b := by
      intro z hz
      rcases Set.mem_insert_iff.mp hz.2.1 with h | h
      · exact absurd h hz.1
      · exact Set.mem_singleton_iff.mp h
    change Classical.epsilon P = b
    exact huniq _ (Classical.epsilon_spec ⟨b, hbprop⟩)

/-- Two-point `azimCycle` swap (`_p3` form, for the `ff_of_hyp` bridge). -/
private theorem w5cB10_azimCycle_pair_p3 (a b v0 c : V3) (hab : a ≠ b) :
    azimCycle_p3 ({a, b} : Set V3) v0 c a = b := by
  unfold azimCycle_p3
  split
  · rename_i hsub
    have hb : b ∈ ({a, b} : Set V3) := by simp
    exact absurd (Set.mem_singleton_iff.mp (hsub hb)) hab.symm
  · rename_i _hsub
    let P : V3 → Prop := fun z => z ≠ a ∧ z ∈ ({a, b} : Set V3) ∧
      ∀ q ∈ ({a, b} : Set V3), q ≠ a →
        azim v0 c a z < azim v0 c a q ∨
          azim v0 c a z = azim v0 c a q ∧
            ‖projection (z - v0) (c - v0)‖ ≤ ‖projection (q - v0) (c - v0)‖
    have hbprop : P b := by
      refine ⟨hab.symm, by simp, ?_⟩
      intro q hq hqa
      rcases Set.mem_insert_iff.mp hq with rfl | hq
      · exact absurd rfl hqa
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        exact Or.inr ⟨rfl, le_refl _⟩
    have huniq : ∀ z, P z → z = b := by
      intro z hz
      rcases Set.mem_insert_iff.mp hz.2.1 with h | h
      · exact absurd h hz.1
      · exact Set.mem_singleton_iff.mp h
    change Classical.epsilon P = b
    exact huniq _ (Classical.epsilon_spec ⟨b, hbprop⟩)

/-- Two-point `ivsAzimCycle` preimage (`_p4` form): on `{a, b}` the
preimage of `a` is `b`. -/
private theorem w5cB10_ivs_pair (a b v0 c : V3) (hab : a ≠ b) :
    ivsAzimCycle_p4 ({a, b} : Set V3) v0 c a = b := by
  have hba : b ≠ a := hab.symm
  have hcyc_b : azimCycle_p4 ({a, b} : Set V3) v0 c b = a := by
    have h := w5cB10_azimCycle_pair b a v0 c hba
    rwa [Set.pair_comm] at h
  have hcyc_a : azimCycle_p4 ({a, b} : Set V3) v0 c a = b :=
    w5cB10_azimCycle_pair a b v0 c hab
  unfold ivsAzimCycle_p4
  have hex : ∃ x, x ∈ ({a, b} : Set V3) ∧
      azimCycle_p4 ({a, b} : Set V3) v0 c x = a :=
    ⟨b, by simp, hcyc_b⟩
  rw [dif_pos hex]
  have hprop := hex.choose_spec
  rcases Set.mem_insert_iff.mp hprop.1 with h | h
  · rw [h] at hprop
    rw [hcyc_a] at hprop
    exact absurd hprop.2.symm hab
  · exact Set.mem_singleton_iff.mp h

/-- Two-point `ivsAzimCycle` preimage (`_p3` form). -/
private theorem w5cB10_ivs_pair_p3 (a b v0 c : V3) (hab : a ≠ b) :
    ivsAzimCycle_p3 ({a, b} : Set V3) v0 c a = b := by
  have hba : b ≠ a := hab.symm
  have hcyc_b : azimCycle_p3 ({a, b} : Set V3) v0 c b = a := by
    have h := w5cB10_azimCycle_pair_p3 b a v0 c hba
    rwa [Set.pair_comm] at h
  unfold ivsAzimCycle_p3
  have hne : ({a, b} : Set V3) ≠ ∅ := by
    intro hc
    have hb : b ∈ ({a, b} : Set V3) := by simp
    rw [hc] at hb
    exact absurd hb (by simp)
  rw [if_neg hne]
  let P : V3 → Prop := fun z => z ∈ ({a, b} : Set V3) ∧
    azimCycle_p3 ({a, b} : Set V3) v0 c z = a
  have hbprop : P b := ⟨by simp, hcyc_b⟩
  have huniq : ∀ z, P z → z = b := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz.1 with h | h
    · rw [h] at hz
      have hcy : azimCycle_p3 ({a, b} : Set V3) v0 c a = a := hz.2
      rw [w5cB10_azimCycle_pair_p3 a b v0 c hab] at hcy
      exact h.trans hcy.symm
    · exact Set.mem_singleton_iff.mp h
  change Classical.epsilon P = b
  exact huniq _ (Classical.epsilon_spec ⟨b, hbprop⟩)

/-- Neighbour-set transfer: a vertex bijection carrying the fan edge set
carries `EE` to `EE` (`{f u, y} ∈ E'` unfolds to `{u, x} ∈ E` using the
two-point graph condition). -/
private theorem w5cB10_EE_image {V V' : Set V3} {E E' : Set (Set V3)} {f : V3 → V3}
    (hbij : Set.BijOn f V V') (hE : (fun s => f '' s) '' E = E')
    (hG : Kepler.Text.Fan.Graph E) (hsub : ⋃₀ E ⊆ V) {u : V3} (hu : u ∈ V) :
    EE_p4 (f u) E' = f '' EE_p4 u E := by
  ext y
  constructor
  · intro hy
    have hy' : ({f u, y} : Set V3) ∈ E' := hy
    rw [← hE] at hy'
    obtain ⟨s, hsE, hseq⟩ := hy'
    obtain ⟨hfin, hcard⟩ := hG s hsE
    obtain ⟨a, b, hab, hfab⟩ := Finset.card_eq_two.mp hcard
    have hset : s = {a, b} := by
      rw [← hfin.coe_toFinset, hfab]
      simp
    have haV : a ∈ V := hsub (Set.mem_sUnion_of_mem (by rw [hset]; simp) hsE)
    have hbV : b ∈ V := hsub (Set.mem_sUnion_of_mem (by rw [hset]; simp) hsE)
    have hne : f a ≠ f b := fun h => hab (hbij.2.1 haV hbV h)
    have hseq' : ({f a, f b} : Set V3) = {f u, y} := by
      rw [← hseq, hset]
      show ({f a, f b} : Set V3) = f '' ({a, b} : Set V3)
      rw [Set.image_insert_eq, Set.image_singleton]
    have ha_in : f a ∈ ({f u, y} : Set V3) := by rw [← hseq']; simp
    rcases Set.mem_insert_iff.mp ha_in with hfa | hfa
    · -- `f a = f u`: then `y = f b` and `a = u`
      have hau : a = u := hbij.2.1 haV hu hfa
      have hseq2 : ({f u, f b} : Set V3) = {f u, y} := by
        have h := hseq'
        rw [hfa] at h
        exact h
      have hfb_in : f b ∈ ({f u, y} : Set V3) := by rw [← hseq2]; simp
      have hne_u : f u ≠ f b := by rw [← hfa]; exact hne
      have hyb : f b = y := by
        rcases Set.mem_insert_iff.mp hfb_in with h | h
        · exact absurd h hne_u.symm
        · exact Set.mem_singleton_iff.mp h
      refine ⟨b, ?_, hyb⟩
      have hEq : ({u, b} : Set V3) = s := by rw [hset, hau]
      show ({u, b} : Set V3) ∈ E
      rw [hEq]
      exact hsE
    · -- `f a = y`: then `f b = f u` and `b = u`
      have hfb_in : f b ∈ ({f u, y} : Set V3) := by rw [← hseq']; simp
      have hfa_ne : f b ≠ y := by rw [← hfa]; exact hne.symm
      have hfb : f b = f u := by
        rcases Set.mem_insert_iff.mp hfb_in with h | h
        · exact h
        · exact absurd (Set.mem_singleton_iff.mp h) hfa_ne
      have hbu : b = u := hbij.2.1 hbV hu hfb
      refine ⟨a, ?_, hfa⟩
      have hEq : ({u, a} : Set V3) = s := by
        rw [hset, hbu]
        exact Set.pair_comm u a
      show ({u, a} : Set V3) ∈ E
      rw [hEq]
      exact hsE
  · rintro ⟨x, hx, rfl⟩
    show ({f u, f x} : Set V3) ∈ E'
    rw [← hE]
    exact ⟨{u, x}, hx, by simp only [Set.image_insert_eq, Set.image_singleton]⟩

/-- The neighbour set of an interior vertex is the two-point set
`{other, v}` under `LocalFan`'s 2-regularity. -/
private theorem w5cB10_EE_pair {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : LocalFan V E FF) {v w : V3} (hxE : ({v, w} : Set V3) ∈ E) (hwV : w ∈ V) :
    ∃ z, EE_p4 w E = {v, z} ∧ z ≠ v := by
  obtain ⟨_hfan, _x0, _hx0, _hFF, _hD, h2reg⟩ := hlf
  have h2w : (EE_p4 w E).ncard = 2 := h2reg w hwV
  have hvW : v ∈ EE_p4 w E := by
    show ({w, v} : Set V3) ∈ E
    rw [Set.pair_comm]
    exact hxE
  obtain ⟨z, hWz⟩ : ∃ z, EE_p4 w E = {v, z} := by
    obtain ⟨a, b, _hab, hW⟩ := Set.ncard_eq_two.mp h2w
    rw [hW] at hvW
    rcases Set.mem_insert_iff.mp hvW with h | h
    · refine ⟨b, ?_⟩
      rw [hW, ← h]
    · rw [Set.mem_singleton_iff] at h
      refine ⟨a, ?_⟩
      rw [hW, ← h]
      exact Set.pair_comm a v
  refine ⟨z, hWz, ?_⟩
  intro hzv
  rw [hzv] at hWz
  rw [hWz] at h2w
  simp at h2w

/-- Source `ff_of_hyp` read at a dart. -/
private theorem w5cB10_ff_unfold {V : Set V3} {E : Set (Set V3)} {v w : V3}
    (hd : (v, w) ∈ dartsOfHyp_p4 E V) :
    ffOfHyp_p4 0 V E (v, w) = (w, ivsAzimCycle_p4 (EE_p4 w E) 0 w v) := by
  rw [ffOfHyp_p4, if_pos hd]

/-- On a two-point neighbour set the `_p3` and `_p4` `ff_of_hyp` readings
coincide (`ivs_azim_cycle` bodies differ, but both pick the unique other
point). -/
private theorem w5cB10_ff_p3_eq_p4_pair (x : V3) (V : Set V3) {E : Set (Set V3)}
    {v w z : V3} (hW : EE_p4 w E = {v, z}) (hzv : z ≠ v) :
    ffOfHyp_p3 x V E (v, w) = ffOfHyp_p4 x V E (v, w) := by
  have hvW : v ∈ EE_p4 w E := by rw [hW]; simp
  have hxE : ({v, w} : Set V3) ∈ E := by
    have h : ({w, v} : Set V3) ∈ E := hvW
    rwa [Set.pair_comm] at h
  have hd4 : (v, w) ∈ dartsOfHyp_p4 E V := by
    show (v, w) ∈ ordPairs_p4 E ∪ selfPairs_p4 E V
    exact Set.mem_union_left _ hxE
  have hd3 : (v, w) ∈ dartsOfHyp_p3 E V := by
    rw [← dartsOfHyp_p4_eq_dartsOfHyp_p3]
    exact hd4
  unfold ffOfHyp_p3 ffOfHyp_p4
  rw [if_pos hd3, if_pos hd4]
  have hW3 : EE_p3 w E = {v, z} := by
    rw [show EE_p3 w E = EE_p4 w E from rfl]
    exact hW
  show (w, ivsAzimCycle_p3 (EE_p3 w E) x w v) =
    (w, ivsAzimCycle_p4 (EE_p4 w E) x w v)
  rw [hW3, hW, w5cB10_ivs_pair_p3 v z x w hzv.symm,
    w5cB10_ivs_pair v z x w hzv.symm]

/-- Core transfer: dart bijection + `ff_of_hyp` commutation (HOL
`BIJ_AND_MAP_COMM` core script, restated for the explicit vertex map). -/
private theorem w5cB10_bij_and_map_comm {V V' : Set V3} {E E' : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → V3}
    (hlf : LocalFan V E FF) (hbij : Set.BijOn f V V')
    (hE : (fun s => f '' s) '' E = E') (hfan' : Fan.FAN 0 V' E') :
    Set.BijOn (fun p : V3 × V3 => (f p.1, f p.2)) (dartsOfHyp_p4 E V) (dartsOfHyp_p4 E' V') ∧
      (∀ x ∈ dartsOfHyp_p4 E V,
        ffOfHyp_p4 0 V' E' (f x.1, f x.2) =
          (f (ffOfHyp_p4 0 V E x).1, f (ffOfHyp_p4 0 V E x).2)) := by
  have hkeep := hlf
  obtain ⟨hfan, _x0, _hx0, _hFF, _hD, h2reg⟩ := hlf
  have hsub : ⋃₀ E ⊆ V := hfan.1
  have hG : Kepler.Text.Fan.Graph E := hfan.2.1
  have hedge := w5cB10_hedge hkeep
  have hno := w5cB10_hno hkeep
  have hno' := w5cB10_hno_image hedge hbij hE
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rw [hno] at hp
      rw [hno']
      show ({f p.1, f p.2} : Set V3) ∈ E'
      rw [← hE]
      exact ⟨{p.1, p.2}, hp, by simp only [Set.image_insert_eq, Set.image_singleton]⟩
    · intro p hp q hq heq
      rw [hno] at hp hq
      have hp1 : p.1 ∈ V := hsub (Set.mem_sUnion_of_mem (by simp) hp)
      have hp2 : p.2 ∈ V := hsub (Set.mem_sUnion_of_mem (by simp) hp)
      have hq1 : q.1 ∈ V := hsub (Set.mem_sUnion_of_mem (by simp) hq)
      have hq2 : q.2 ∈ V := hsub (Set.mem_sUnion_of_mem (by simp) hq)
      have h1 : f p.1 = f q.1 := congrArg Prod.fst heq
      have h2 : f p.2 = f q.2 := congrArg Prod.snd heq
      exact Prod.ext (hbij.2.1 hp1 hq1 h1) (hbij.2.1 hp2 hq2 h2)
    · intro q hq
      rw [hno'] at hq
      have hq' : ({q.1, q.2} : Set V3) ∈ E' := hq
      rw [← hE] at hq'
      obtain ⟨s, hsE, hseq⟩ := hq'
      obtain ⟨hfin, hcard⟩ := hG s hsE
      obtain ⟨a, b, hab, hfab⟩ := Finset.card_eq_two.mp hcard
      have hset : s = {a, b} := by
        rw [← hfin.coe_toFinset, hfab]
        simp
      have haV : a ∈ V := hsub (Set.mem_sUnion_of_mem (by rw [hset]; simp) hsE)
      have hbV : b ∈ V := hsub (Set.mem_sUnion_of_mem (by rw [hset]; simp) hsE)
      have hne : f a ≠ f b := fun h => hab (hbij.2.1 haV hbV h)
      have hseq' : ({f a, f b} : Set V3) = {q.1, q.2} := by
        rw [← hseq, hset]
        show ({f a, f b} : Set V3) = f '' ({a, b} : Set V3)
        rw [Set.image_insert_eq, Set.image_singleton]
      by_cases hfa : f a = q.1
      · refine ⟨(a, b), ?_, ?_⟩
        · rw [hno]
          show ({a, b} : Set V3) ∈ E
          rw [← hset]
          exact hsE
        · have hfb : f b = q.2 := by
            have hbin : f b ∈ ({q.1, q.2} : Set V3) := by rw [← hseq']; simp
            rcases Set.mem_insert_iff.mp hbin with h | h
            · exact absurd (h.trans hfa.symm) hne.symm
            · exact Set.mem_singleton_iff.mp h
          show (f a, f b) = q
          rw [hfa, hfb]
      · have hfa2 : f a = q.2 := by
          have hain : f a ∈ ({q.1, q.2} : Set V3) := by rw [← hseq']; simp
          rcases Set.mem_insert_iff.mp hain with h | h
          · exact absurd h hfa
          · exact Set.mem_singleton_iff.mp h
        refine ⟨(b, a), ?_, ?_⟩
        · rw [hno]
          show ({b, a} : Set V3) ∈ E
          rw [Set.pair_comm]
          show ({a, b} : Set V3) ∈ E
          rw [← hset]
          exact hsE
        · have hfb : f b = q.1 := by
            have hbin : f b ∈ ({q.1, q.2} : Set V3) := by rw [← hseq']; simp
            rcases Set.mem_insert_iff.mp hbin with h | h
            · exact h
            · exact absurd (hfa2.trans (Set.mem_singleton_iff.mp h).symm) hne
          show (f b, f a) = q
          rw [hfb, hfa2]
  · intro x hx
    rw [hno] at hx
    cases x with
    | mk v w =>
      have hxE : ({v, w} : Set V3) ∈ E := hx
      have hvV : v ∈ V := hsub (Set.mem_sUnion_of_mem (by simp) hxE)
      have hwV : w ∈ V := hsub (Set.mem_sUnion_of_mem (by simp) hxE)
      have hxd : (v, w) ∈ dartsOfHyp_p4 E V :=
        Set.mem_union_left _ (show ({v, w} : Set V3) ∈ E from hxE)
      have hxd' : (f v, f w) ∈ dartsOfHyp_p4 E' V' := by
        show (f v, f w) ∈ ordPairs_p4 E' ∪ selfPairs_p4 E' V'
        exact Set.mem_union_left _ (show ({f v, f w} : Set V3) ∈ E' from by
          rw [← hE]
          exact ⟨{v, w}, hxE, by simp only [Set.image_insert_eq, Set.image_singleton]⟩)
      obtain ⟨z, hWz, hzv⟩ := w5cB10_EE_pair hkeep hxE hwV
      have hzW : z ∈ EE_p4 w E := by rw [hWz]; simp
      have hzV : z ∈ V := hsub (Set.mem_sUnion_of_mem (by simp)
        (show ({w, z} : Set V3) ∈ E from hzW))
      have hfvz : f v ≠ f z := fun h => hzv (hbij.2.1 hvV hzV h).symm
      have hW' : EE_p4 (f w) E' = f '' EE_p4 w E :=
        w5cB10_EE_image hbij hE hG hsub hwV
      rw [w5cB10_ff_unfold hxd', w5cB10_ff_unfold (V := V) (E := E) hxd]
      show (f w, ivsAzimCycle_p4 (EE_p4 (f w) E') 0 (f w) (f v)) =
        (f w, f (ivsAzimCycle_p4 (EE_p4 w E) 0 w v))
      congr 1
      rw [hW', hWz, Set.image_insert_eq, Set.image_singleton,
        w5cB10_ivs_pair v z 0 w hzv.symm,
        w5cB10_ivs_pair (f v) (f z) 0 (f w) hfvz]

/-- HOL `BIJ_AND_MAP_COMM` (lunar_deform.hl:1938): the dart/`ff_of` transfer
kit.  DISCHARGED (B10): the HOL `ELMS_OF_HYPERMAP_HYP` step is replaced by
`LocalFan`'s 2-regularity (no self-pair darts) + `w5cB10_EE_image` (the
neighbour sets transfer as two-point images). -/
theorem BIJ_AND_MAP_COMM_p37 {V V' : Set V3} {E E' : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → V3} {ff : V3 × V3 → V3 × V3}
    (_hlf : LocalFan V E FF) (_hbij : Set.BijOn f V V')
    (_hE : (fun s => f '' s) '' E = E') (_hfan' : Fan.FAN 0 V' E')
    (_hff : (fun p => (f p.1, f p.2)) = ff) :
    Set.BijOn ff (dartsOfHyp_p4 E V) (dartsOfHyp_p4 E' V') ∧
      (∀ x ∈ dartsOfHyp_p4 E V,
        ffOfHyp_p4 0 V' E' (ff x) = ff (ffOfHyp_p4 0 V E x)) := by
  have hcomm := w5cB10_bij_and_map_comm _hlf _hbij _hE _hfan'
  have hF : ff = fun p : V3 × V3 => (f p.1, f p.2) := _hff.symm
  constructor
  · rw [hF]
    exact hcomm.1
  · intro x hx
    rw [hF]
    exact hcomm.2 x hx

/-- HOL `NODE_EDGE_COMM_LEMMA` (lunar_deform.hl:2308): `nn_of`/`ee_of`
commutation under the dart map.  DISCHARGED (B10): both maps are read off
the two-point neighbour sets (`w5cB10_azimCycle_pair`, `ee_of_hyp` is the
swap), consuming the closed `BIJ_AND_MAP_COMM_p37` for dart membership. -/
theorem NODE_EDGE_COMM_LEMMA_p37 {V V' : Set V3} {E E' : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → V3} {ff : V3 × V3 → V3 × V3}
    (_hlf : LocalFan V E FF) (_hbij : Set.BijOn f V V')
    (_hE : (fun s => f '' s) '' E = E') (_hfan' : Fan.FAN 0 V' E')
    (_hff : (fun p => (f p.1, f p.2)) = ff) :
    ∀ x ∈ dartsOfHyp_p4 E V,
      nnOfHyp_p4 0 V' E' (ff x) = ff (nnOfHyp_p4 0 V E x) ∧
      eeOfHyp_p4 0 V' E' (ff x) = ff (eeOfHyp_p4 0 V E x) := by
  have hkeep := _hlf
  obtain ⟨hfan, _x0, _hx0, _hFF, _hD, h2reg⟩ := _hlf
  have hsub : ⋃₀ E ⊆ V := hfan.1
  have hG : Kepler.Text.Fan.Graph E := hfan.2.1
  have hedge := w5cB10_hedge hkeep
  have hno := w5cB10_hno hkeep
  have hno' := w5cB10_hno_image hedge _hbij _hE
  have hbij := (BIJ_AND_MAP_COMM_p37 hkeep _hbij _hE _hfan' _hff).1
  have hF : ff = fun p : V3 × V3 => (f p.1, f p.2) := _hff.symm
  intro x hx
  rw [hno] at hx
  cases x with
  | mk v w =>
    rw [hF]
    have hxE : ({v, w} : Set V3) ∈ E := hx
    have hvV : v ∈ V := hsub (Set.mem_sUnion_of_mem (by simp) hxE)
    have hwV : w ∈ V := hsub (Set.mem_sUnion_of_mem (by simp) hxE)
    have hxd : (v, w) ∈ dartsOfHyp_p4 E V :=
      Set.mem_union_left _ (show ({v, w} : Set V3) ∈ E from hxE)
    have hxd' : (f v, f w) ∈ dartsOfHyp_p4 E' V' := by
      show (fun p : V3 × V3 => (f p.1, f p.2)) (v, w) ∈ dartsOfHyp_p4 E' V'
      rw [← hF]
      exact hbij.1 hxd
    constructor
    · have hxE' : ({w, v} : Set V3) ∈ E := by rw [Set.pair_comm]; exact hxE
      obtain ⟨z, hWz, hzw⟩ := w5cB10_EE_pair hkeep (v := w) (w := v) hxE' hvV
      have hzW : z ∈ EE_p4 v E := by rw [hWz]; simp
      have hzV : z ∈ V := hsub (Set.mem_sUnion_of_mem (by simp)
        (show ({v, z} : Set V3) ∈ E from hzW))
      have hfzw : f w ≠ f z := fun h => hzw (_hbij.2.1 hwV hzV h).symm
      have hW' : EE_p4 (f v) E' = f '' EE_p4 v E :=
        w5cB10_EE_image _hbij _hE hG hsub hvV
      rw [nnOfHyp_p4, if_pos hxd', nnOfHyp_p4, if_pos hxd]
      show (f v, azimCycle_p4 (EE_p4 (f v) E') 0 (f v) (f w)) =
        (f v, f (azimCycle_p4 (EE_p4 v E) 0 v w))
      congr 1
      rw [hW', hWz, Set.image_insert_eq, Set.image_singleton,
        w5cB10_azimCycle_pair w z 0 v hzw.symm,
        w5cB10_azimCycle_pair (f w) (f z) 0 (f v) hfzw]
    · rw [eeOfHyp_p4, if_pos hxd', eeOfHyp_p4, if_pos hxd]

/-- HOL `hyp_iso f (H,HH)` (Hypermap_iso): dart bijection commuting with the
face/node/edge maps.  Shape reconstructed from this file's consumer lemmas.
NEEDS: verbatim check against `hypermap_iso.hl`. -/
def hypIso_p37 {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (H : Hypermap α) (HH : Hypermap β) : Prop :=
  Set.BijOn f (H.darts : Set α) (HH.darts : Set β) ∧
    (∀ p ∈ (H.darts : Set α), (HH.faceMap : β → β) (f p) = f ((H.faceMap : α → α) p)) ∧
    (∀ p ∈ (H.darts : Set α), (HH.nodeMap : β → β) (f p) = f ((H.nodeMap : α → α) p)) ∧
    (∀ p ∈ (H.darts : Set α), (HH.edgeMap : β → β) (f p) = f ((H.edgeMap : α → α) p))

/-- Bridge: `hypermapOfFan`'s node map = `nnOfHyp_p4` (instance-explicit
form; `_p3`/`_p4` node readings are definitionally equal). -/
private theorem w5cB10_nodeMap_eq (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : Fan.FAN x V E) (d : V3 × V3) :
    (Fan.hypermapOfFan x V E hfan).nodeMap d = nnOfHyp_p4 x V E d :=
  (congrFun (nnOfHyp_p3_eq_nodeMapLA1_fun (x := x) hfan) d).symm

/-- Bridge: `hypermapOfFan`'s edge map = `eeOfHyp_p4`. -/
private theorem w5cB10_edgeMap_eq (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : Fan.FAN x V E) (d : V3 × V3) :
    (Fan.hypermapOfFan x V E hfan).edgeMap d = eeOfHyp_p4 x V E d :=
  (congrFun (eeOfHyp_p3_eq_edgeMapLA1_fun (x := x) hfan) d).symm

/-- Bridge on a two-point dart: `hypermapOfFan`'s face map = `ffOfHyp_p4`. -/
private theorem w5cB10_faceMap_eq_pair (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : Fan.FAN x V E) {v w z : V3}
    (hW : EE_p4 w E = {v, z}) (hzv : z ≠ v) :
    (Fan.hypermapOfFan x V E hfan).faceMap (v, w) = ffOfHyp_p4 x V E (v, w) := by
  have hface : (Fan.hypermapOfFan x V E hfan).faceMap (v, w) =
      ffOfHyp_p3 x V E (v, w) :=
    (congrFun (ffOfHyp_p3_eq_faceMapLA1_fun (x := x) hfan) (v, w)).symm
  exact hface.trans (w5cB10_ff_p3_eq_p4_pair x V hW hzv)

/-- HOL `HYP_ISO_LEMMAA` (lunar_deform.hl:2612): the `HYP`-hypermaps of a
vertex-bijective fan pair are `hyp_iso`.  DISCHARGED (B10): the dart
bijection is `BIJ_AND_MAP_COMM_p37`'s first conjunct (the HYP dart set is
`dart1OfFan` on both sides), and the three map commutations are that
theorem's second conjunct (face) plus `NODE_EDGE_COMM_LEMMA_p37`
(node/edge) read through the `hypermapOfFan` bridges. -/
theorem HYP_ISO_LEMMAA_p37 {V V' : Set V3} {E E' : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → V3}
    (_hlf : LocalFan V E FF) (_hbij : Set.BijOn f V V')
    (_hE : (fun s => f '' s) '' E = E') (_hfan : Fan.FAN 0 V E)
    (_hfan' : Fan.FAN 0 V' E') :
    hypIso_p37 (fun (p : V3 × V3) => (f p.1, f p.2)) (Fan.hypermapOfFan 0 V E _hfan)
      (Fan.hypermapOfFan 0 V' E' _hfan') := by
  have hedge := w5cB10_hedge _hlf
  have hno := w5cB10_hno _hlf
  have hno' := w5cB10_hno_image hedge _hbij _hE
  have hcomm := w5cB10_bij_and_map_comm _hlf _hbij _hE _hfan'
  have hNE := NODE_EDGE_COMM_LEMMA_p37 _hlf _hbij _hE _hfan'
    (rfl : (fun p : V3 × V3 => (f p.1, f p.2)) = fun p => (f p.1, f p.2))
  have hkeep := _hlf
  obtain ⟨hfan0, _x0, _hx0, _hFF, _hD, h2reg⟩ := _hlf
  have hsub : ⋃₀ E ⊆ V := hfan0.1
  have hG : Kepler.Text.Fan.Graph E := hfan0.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hA : Set.BijOn (fun p : V3 × V3 => (f p.1, f p.2))
        (Fan.dart1OfFan V E) (Fan.dart1OfFan V' E') := by
      have h := hcomm.1
      rwa [hno, hno'] at h
    rwa [dartsLA1 0 V E _hfan, dartsLA1 0 V' E' _hfan']
  · intro p hp
    have hp1 : p ∈ Fan.dart1OfFan V E := by rwa [dartsLA1 0 V E _hfan] at hp
    have hpD : p ∈ dartsOfHyp_p4 E V := by rw [hno]; exact hp1
    cases p with
    | mk v w =>
      have hxE : ({v, w} : Set V3) ∈ E := hp1
      have hwV : w ∈ V := hsub (Set.mem_sUnion_of_mem (by simp) hxE)
      have hvV : v ∈ V := hsub (Set.mem_sUnion_of_mem (by simp) hxE)
      obtain ⟨z, hWz, hzv⟩ := w5cB10_EE_pair hkeep hxE hwV
      have hzW : z ∈ EE_p4 w E := by rw [hWz]; simp
      have hzV : z ∈ V := hsub (Set.mem_sUnion_of_mem (by simp)
        (show ({w, z} : Set V3) ∈ E from hzW))
      have hfvz : f v ≠ f z := fun h => hzv (_hbij.2.1 hvV hzV h).symm
      have hW' : EE_p4 (f w) E' = {f v, f z} := by
        rw [w5cB10_EE_image _hbij _hE hG hsub hwV, hWz,
          Set.image_insert_eq, Set.image_singleton]
      calc (Fan.hypermapOfFan 0 V' E' _hfan').faceMap (f v, f w)
          = ffOfHyp_p4 0 V' E' (f v, f w) :=
            w5cB10_faceMap_eq_pair 0 V' E' _hfan' hW' hfvz.symm
        _ = (f (ffOfHyp_p4 0 V E (v, w)).1, f (ffOfHyp_p4 0 V E (v, w)).2) :=
            hcomm.2 (v, w) hpD
        _ = (fun p : V3 × V3 => (f p.1, f p.2))
              ((Fan.hypermapOfFan 0 V E _hfan).faceMap (v, w)) := by
            simp only [w5cB10_faceMap_eq_pair 0 V E _hfan hWz hzv]
  · intro p hp
    have hp1 : p ∈ Fan.dart1OfFan V E := by rwa [dartsLA1 0 V E _hfan] at hp
    have hpD : p ∈ dartsOfHyp_p4 E V := by rw [hno]; exact hp1
    cases p with
    | mk v w =>
      calc (Fan.hypermapOfFan 0 V' E' _hfan').nodeMap (f v, f w)
          = nnOfHyp_p4 0 V' E' (f v, f w) :=
            w5cB10_nodeMap_eq 0 V' E' _hfan' _
        _ = (f (nnOfHyp_p4 0 V E (v, w)).1, f (nnOfHyp_p4 0 V E (v, w)).2) :=
            (hNE (v, w) hpD).1
        _ = (fun p : V3 × V3 => (f p.1, f p.2))
              ((Fan.hypermapOfFan 0 V E _hfan).nodeMap (v, w)) := by
            simp only [w5cB10_nodeMap_eq 0 V E _hfan (v, w)]
  · intro p hp
    have hp1 : p ∈ Fan.dart1OfFan V E := by rwa [dartsLA1 0 V E _hfan] at hp
    have hpD : p ∈ dartsOfHyp_p4 E V := by rw [hno]; exact hp1
    cases p with
    | mk v w =>
      calc (Fan.hypermapOfFan 0 V' E' _hfan').edgeMap (f v, f w)
          = eeOfHyp_p4 0 V' E' (f v, f w) :=
            w5cB10_edgeMap_eq 0 V' E' _hfan' _
        _ = (f (eeOfHyp_p4 0 V E (v, w)).1, f (eeOfHyp_p4 0 V E (v, w)).2) :=
            (hNE (v, w) hpD).2
        _ = (fun p : V3 × V3 => (f p.1, f p.2))
              ((Fan.hypermapOfFan 0 V E _hfan).edgeMap (v, w)) := by
            simp only [w5cB10_edgeMap_eq 0 V E _hfan (v, w)]

/-- Iterate of the face map stays on the dart set (helper for
`POWER_COMM_p37`/`IMAGE_FACE_F_p37`). -/
private theorem faceMap_mem_iter_p37 {α : Type*} [DecidableEq α] (H : Hypermap α)
    (p : α) (hp : p ∈ (H.darts : Set α)) (n : ℕ) :
    ((H.faceMap : α → α))^[n] p ∈ (H.darts : Set α) := by
  have hstep : ∀ q ∈ (H.darts : Set α), ((H.faceMap : α → α)) q ∈ (H.darts : Set α) := by
    intro q hq
    by_contra hnot
    have h1 : ((H.faceMap : α → α)) ((H.faceMap : α → α) q) = ((H.faceMap : α → α)) q :=
      H.faceMap_permutes _ (Finset.mem_coe.not.mp hnot)
    have h2 : ((H.faceMap : α → α)) q = q := Equiv.injective _ h1
    exact hnot (by rw [h2]; exact hq)
  induction n with
  | zero => simpa using hp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact hstep _ ih

/-- HOL `POWER_COMM` (lunar_deform.hl:2817; source is a spec'd instance of
`Hypermap_iso.power_comm`): face-map iterates commute with the dart map. -/
theorem POWER_COMM_p37 {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {H : Hypermap α} {HH : Hypermap β} (hiso : hypIso_p37 f H HH)
    (x : α) (hx : x ∈ (H.darts : Set α)) (n : ℕ) :
    (HH.faceMap : β → β)^[n] (f x) = f ((H.faceMap : α → α)^[n] x) := by
  have key : ∀ (m : ℕ) (q : α), q ∈ (H.darts : Set α) →
      (HH.faceMap : β → β)^[m] (f q) = f ((H.faceMap : α → α)^[m] q) := by
    intro m
    induction m with
    | zero => intro q _; simp
    | succ m ih =>
        intro q hq
        have hqm : ((H.faceMap : α → α)^[m]) q ∈ (H.darts : Set α) :=
          faceMap_mem_iter_p37 H q hq m
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih q hq,
          hiso.2.1 _ hqm]
  exact key n x hx

/-- HOL `ITER_COMM` (lunar_deform.hl:2820; the `POWER_TO_ITER` form of
`POWER_COMM`): function iterates commute with a conjugation. -/
theorem ITER_COMM_p37 {α β : Type*} {h : α → α} {k : β → β} {f : α → β}
    (hcomm : ∀ x, k (f x) = f (h x)) (x : α) (n : ℕ) :
    k^[n] (f x) = f (h^[n] x) := by
  induction n generalizing x with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hcomm]

/-- HOL `IMAGE_FACE_F` (lunar_deform.hl:2826): faces (`Hypermap.face`, the
face-map orbit) are carried to faces by a hypermap isomorphism. -/
theorem IMAGE_FACE_F_p37 {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {H : Hypermap α} {HH : Hypermap β} (hiso : hypIso_p37 f H HH)
    (p : α) (hp : p ∈ (H.darts : Set α)) :
    f '' (H.face p) = HH.face (f p) := by
  have key : ∀ (m : ℕ) (q : α), q ∈ (H.darts : Set α) →
      ((HH.faceMap : β → β))^[m] (f q) = f (((H.faceMap : α → α))^[m] q) :=
    fun m q hq => POWER_COMM_p37 hiso q hq m
  have hcoe : ∀ (m : ℕ) (q : α), ((H.faceMap ^ m) q) = ((H.faceMap : α → α))^[m] q :=
    fun m q => by rw [Equiv.Perm.coe_pow]
  have hcoe2 : ∀ (m : ℕ) (q : β), ((HH.faceMap ^ m) q) = ((HH.faceMap : β → β))^[m] q :=
    fun m q => by rw [Equiv.Perm.coe_pow]
  ext z
  constructor
  · rintro ⟨y, ymem, rfl⟩
    obtain ⟨m, hm⟩ := ymem
    have hz : ((HH.faceMap : β → β))^[m] (f p) = f y := by
      rw [key m p hp, ← hcoe, hm]
    exact ⟨m, hz⟩
  · intro hmem
    obtain ⟨m, hm⟩ := hmem
    refine ⟨(H.faceMap ^ m) p, ⟨⟨m, rfl⟩, ?_⟩⟩
    rw [hcoe, ← key m p hp, ← hcoe2]
    exact hm

/-- HOL `AUTOMAP_IMP_ALL_ITER_IN2` (lunar_deform.hl:2844): an invariant set
absorbs all iterates. -/
theorem AUTOMAP_IMP_ALL_ITER_IN2_p37 {α : Type*} {f : α → α} {W : Set α}
    {p : α} {N : ℕ} (hp : p ∈ W) (hf : ∀ x ∈ W, f x ∈ W) : f^[N] p ∈ W := by
  induction N with
  | zero => simpa using hp
  | succ n ih => simpa [Function.iterate_succ_apply'] using hf (f^[n] p) ih

/-- HOL `ITER_COMM_RESTRICTED` (lunar_deform.hl:2849): iterate commutation
with membership invariants on both sides. -/
theorem ITER_COMM_RESTRICTED_p37 {α β : Type*} {V : Set α} {V' : Set β}
    {f : α → β} {h : α → α} {g : β → β}
    (hf : ∀ x ∈ V, f x ∈ V') (hh : ∀ x, h x ∈ V ↔ x ∈ V)
    (_hg : ∀ y, g y ∈ V' ↔ y ∈ V')
    (hcomm : ∀ x ∈ V, f (h x) = g (f x)) (x : α) (hx : x ∈ V) (n : ℕ) :
    f (h^[n] x) = g^[n] (f x) := by
  have hinv : ∀ m, h^[m] x ∈ V := by
    intro m
    induction m with
    | zero =>
        simp only [Function.iterate_zero, id_eq]
        exact hx
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (hh _).mpr ih
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        hcomm (h^[m] x) (hinv m), ih]

/-- HOL `HAS_THE_SAME_ORD_LEM` (lunar_deform.hl:2871).  DISCHARGED 2026-09-20:
iterate conjugation on `V` (with the `h`-invariance of `V` and the
`g`-invariance of `V'`), minimality transfer via the `BijOn` injection, and
identity-off-`V`/`V'` for the fixed points. -/
theorem HAS_THE_SAME_ORD_LEM_p37 {α β : Type*} {V : Set α} {V' : Set β}
    {h : α → α} {g : β → β} {f : α → β} {k : ℕ}
    (_h1 : ∀ x ∉ V, h x = x) (_h2 : ∀ y ∉ V', g y = y)
    (_hbij : Set.BijOn f V V') (_h3 : ∀ x, h x ∈ V ↔ x ∈ V)
    (_h4 : ∀ y, g y ∈ V' ↔ y ∈ V')
    (_h5 : ∀ x ∈ V, f (h x) = g (f x)) (_h6 : hasOrders_p37 h k) :
    hasOrders_p37 g k := by
  obtain ⟨hmin, htop⟩ := _h6
  have hVin : ∀ (n : ℕ) (x : α), x ∈ V → h^[n] x ∈ V := by
    intro n
    induction n with
    | zero => intro x hx; exact hx
    | succ m ih =>
        intro x hx
        rw [Function.iterate_succ_apply']
        exact (_h3 _).mpr (ih x hx)
  have hconj : ∀ (n : ℕ) (x : α), x ∈ V → g^[n] (f x) = f (h^[n] x) := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ m ih =>
        intro x hx
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih x hx,
          ← _h5 (h^[m] x) (hVin m x hx)]
  have hfix : ∀ (m : ℕ) (x : α), x ∉ V → h^[m] x = x := by
    intro m
    induction m with
    | zero => intro x _; simp
    | succ n ih =>
        intro x hx
        rw [Function.iterate_succ_apply, _h1 x hx, ih x hx]
  refine ⟨fun i hi1 hi2 heq => ?_, funext fun y => ?_⟩
  · obtain ⟨x, hxne⟩ : ∃ x, h^[i] x ≠ x := by
      by_contra hall
      push_neg at hall
      exact hmin i hi1 hi2 (funext hall)
    have hxV : x ∈ V := by
      by_contra hx
      exact hxne (hfix i x hx)
    have hne : g^[i] (f x) ≠ f x := by
      intro hc
      rw [hconj i x hxV] at hc
      exact hxne (_hbij.injOn (hVin i x hxV) hxV hc)
    exact hne (congrFun heq (f x))
  · by_cases hy : y ∈ V'
    · obtain ⟨x, hxV, hfx⟩ := _hbij.surjOn hy
      rw [← hfx, hconj k x hxV, htop]
      simp
    · have gfix : ∀ (m : ℕ) (z : β), z ∉ V' → g^[m] z = z := by
        intro m
        induction m with
        | zero => intro z _; simp
        | succ n ih =>
            intro z hz
            rw [Function.iterate_succ_apply, _h2 z hz, ih z hz]
      exact gfix k y hy

/-- HOL `COMM_THEN_IMAGE_IMAGE_EQ` (lunar_deform.hl:2926). -/
theorem COMM_THEN_IMAGE_IMAGE_EQ_p37 {S A : Set V3} {f g h : V3 → V3}
    (hcomm : ∀ x ∈ S, f (g x) = h (f x)) (hA : A ⊆ S) :
    f '' (g '' A) = h '' (f '' A) := by
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr fun a ha => hcomm a (hA ha)

/-- HOL `IN_DART_PRESERVED` (lunar_deform.hl:2931): dart-closedness of the
three maps, stated over the proof-carrying `Hypermap` structure. -/
theorem IN_DART_PRESERVED_p37 {α : Type*} [DecidableEq α] (H : Hypermap α)
    (h1 : ∀ x, (H.faceMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α))
    (h2 : ∀ x, (H.nodeMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α))
    (h3 : ∀ x, (H.edgeMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α)) :
    (∀ x, (H.faceMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α)) ∧
      (∀ x, (H.nodeMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α)) ∧
      (∀ x, (H.edgeMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α)) :=
  ⟨h1, h2, h3⟩

/-- HOL `HYP_ISO_DIH2K_PRESERVED` (lunar_deform.hl:2937).  DISCHARGED
2026-09-20: card transfer via the dart `BijOn` (`ncard` of the image),
face-union transfer via `IMAGE_FACE_F_p37` + node-map commutation, and the
three order transfers via `HAS_THE_SAME_ORD_LEM_p37` (the hypermap maps fix
the co-darts pointwise and preserve dart membership by `permutes`). -/
theorem HYP_ISO_DIH2K_PRESERVED_p37 {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H : Hypermap α} {HH : Hypermap β} {f : α → β} {k : ℕ}
    (_hfin : (H.darts : Set α).Finite) (_hd : dih2k_p37 H k)
    (_hiso : hypIso_p37 f H HH) :
    dih2k_p37 HH k := by
  obtain ⟨hcard, hface, hord, hordE, hordN⟩ := _hd
  have himg : f '' (H.darts : Set α) = (HH.darts : Set β) := Set.BijOn.image_eq _hiso.1
  have hmemF : ∀ x : α, (H.faceMap : α → α) x ∈ (H.darts : Set α) ↔
      x ∈ (H.darts : Set α) := by
    intro x
    constructor
    · intro hx
      by_contra hnot
      have h1 : (H.faceMap : α → α) x = x :=
        H.faceMap_permutes x (fun hc => hnot (Finset.mem_coe.mp hc))
      exact hnot (h1 ▸ hx)
    · intro hx
      by_contra hnot
      have h1 : (H.faceMap : α → α) ((H.faceMap : α → α) x) =
          (H.faceMap : α → α) x :=
        H.faceMap_permutes ((H.faceMap : α → α) x)
          (fun hc => hnot (Finset.mem_coe.mpr hc))
      rw [← Equiv.injective H.faceMap h1] at hx
      exact hnot hx
  have hmemN : ∀ x : α, (H.nodeMap : α → α) x ∈ (H.darts : Set α) ↔
      x ∈ (H.darts : Set α) := by
    intro x
    constructor
    · intro hx
      by_contra hnot
      have h1 : (H.nodeMap : α → α) x = x :=
        H.nodeMap_permutes x (fun hc => hnot (Finset.mem_coe.mp hc))
      exact hnot (h1 ▸ hx)
    · intro hx
      by_contra hnot
      have h1 : (H.nodeMap : α → α) ((H.nodeMap : α → α) x) =
          (H.nodeMap : α → α) x :=
        H.nodeMap_permutes ((H.nodeMap : α → α) x)
          (fun hc => hnot (Finset.mem_coe.mpr hc))
      rw [← Equiv.injective H.nodeMap h1] at hx
      exact hnot hx
  have hmemE : ∀ x : α, (H.edgeMap : α → α) x ∈ (H.darts : Set α) ↔
      x ∈ (H.darts : Set α) := by
    intro x
    constructor
    · intro hx
      by_contra hnot
      have h1 : (H.edgeMap : α → α) x = x :=
        H.edgeMap_permutes x (fun hc => hnot (Finset.mem_coe.mp hc))
      exact hnot (h1 ▸ hx)
    · intro hx
      by_contra hnot
      have h1 : (H.edgeMap : α → α) ((H.edgeMap : α → α) x) =
          (H.edgeMap : α → α) x :=
        H.edgeMap_permutes ((H.edgeMap : α → α) x)
          (fun hc => hnot (Finset.mem_coe.mpr hc))
      rw [← Equiv.injective H.edgeMap h1] at hx
      exact hnot hx
  have hmemF' : ∀ y : β, (HH.faceMap : β → β) y ∈ (HH.darts : Set β) ↔
      y ∈ (HH.darts : Set β) := by
    intro y
    constructor
    · intro hx
      by_contra hnot
      have h1 : (HH.faceMap : β → β) y = y :=
        HH.faceMap_permutes y (fun hc => hnot (Finset.mem_coe.mp hc))
      exact hnot (h1 ▸ hx)
    · intro hx
      by_contra hnot
      have h1 : (HH.faceMap : β → β) ((HH.faceMap : β → β) y) =
          (HH.faceMap : β → β) y :=
        HH.faceMap_permutes ((HH.faceMap : β → β) y)
          (fun hc => hnot (Finset.mem_coe.mpr hc))
      rw [← Equiv.injective HH.faceMap h1] at hx
      exact hnot hx
  have hmemN' : ∀ y : β, (HH.nodeMap : β → β) y ∈ (HH.darts : Set β) ↔
      y ∈ (HH.darts : Set β) := by
    intro y
    constructor
    · intro hx
      by_contra hnot
      have h1 : (HH.nodeMap : β → β) y = y :=
        HH.nodeMap_permutes y (fun hc => hnot (Finset.mem_coe.mp hc))
      exact hnot (h1 ▸ hx)
    · intro hx
      by_contra hnot
      have h1 : (HH.nodeMap : β → β) ((HH.nodeMap : β → β) y) =
          (HH.nodeMap : β → β) y :=
        HH.nodeMap_permutes ((HH.nodeMap : β → β) y)
          (fun hc => hnot (Finset.mem_coe.mpr hc))
      rw [← Equiv.injective HH.nodeMap h1] at hx
      exact hnot hx
  have hmemE' : ∀ y : β, (HH.edgeMap : β → β) y ∈ (HH.darts : Set β) ↔
      y ∈ (HH.darts : Set β) := by
    intro y
    constructor
    · intro hx
      by_contra hnot
      have h1 : (HH.edgeMap : β → β) y = y :=
        HH.edgeMap_permutes y (fun hc => hnot (Finset.mem_coe.mp hc))
      exact hnot (h1 ▸ hx)
    · intro hx
      by_contra hnot
      have h1 : (HH.edgeMap : β → β) ((HH.edgeMap : β → β) y) =
          (HH.edgeMap : β → β) y :=
        HH.edgeMap_permutes ((HH.edgeMap : β → β) y)
          (fun hc => hnot (Finset.mem_coe.mpr hc))
      rw [← Equiv.injective HH.edgeMap h1] at hx
      exact hnot hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Set.ncard_coe_finset, ← himg, Set.InjOn.ncard_image _hiso.1.injOn,
      Set.ncard_coe_finset]
    exact hcard
  · intro x hx
    obtain ⟨p, hp, hfx⟩ := _hiso.1.surjOn hx
    rw [← hfx, ← IMAGE_FACE_F_p37 _hiso p hp, Set.image_image,
      Set.image_congr fun y hy =>
        _hiso.2.2.1 y (H.face_subset_darts (Finset.mem_coe.mpr hp) hy),
      ← Set.BijOn.image_eq _hiso.1, hface p hp, Set.image_union, Set.image_image]
  · exact HAS_THE_SAME_ORD_LEM_p37
      (fun x hx => H.faceMap_permutes x (fun hc => hx (Finset.mem_coe.mpr hc)))
      (fun y hy => HH.faceMap_permutes y (fun hc => hy (Finset.mem_coe.mpr hc)))
      _hiso.1 hmemF hmemF' (fun x hx => (_hiso.2.1 x hx).symm) hord
  · exact HAS_THE_SAME_ORD_LEM_p37
      (fun x hx => H.edgeMap_permutes x (fun hc => hx (Finset.mem_coe.mpr hc)))
      (fun y hy => HH.edgeMap_permutes y (fun hc => hy (Finset.mem_coe.mpr hc)))
      _hiso.1 hmemE hmemE' (fun x hx => (_hiso.2.2.2 x hx).symm) hordE
  · exact HAS_THE_SAME_ORD_LEM_p37
      (fun x hx => H.nodeMap_permutes x (fun hc => hx (Finset.mem_coe.mpr hc)))
      (fun y hy => HH.nodeMap_permutes y (fun hc => hy (Finset.mem_coe.mpr hc)))
      _hiso.1 hmemN hmemN' (fun x hx => (_hiso.2.2.1 x hx).symm) hordN

/-! ## Continuity preservation, the cross/plane kit, and MHAEYJN
(source 3073-5039) -/

/-- B12: the `_p37` copy of HOL `dih2k` and LA1's registry `Dih2k` are the
same proposition: `H.face` is `orbitMap H.faceMap` by definition, the
face-union equation differs only by symmetry, and `hasOrders_p37` is
`hasOrders_p4` (same body) bridged to `HasOrders` by
`hasOrders_iff_hasOrders_p4`. -/
private theorem w_b12_dih2k_p37_iff_Dih2k {α : Type*} [DecidableEq α]
    (H : Hypermap α) (k : ℕ) : dih2k_p37 H k ↔ Dih2k H k := by
  unfold dih2k_p37 Dih2k Hypermap.face
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, fun d hd => (h2 d hd).symm,
      (hasOrders_iff_hasOrders_p4 H.faceMap k).mpr h3,
      (hasOrders_iff_hasOrders_p4 H.edgeMap 2).mpr h4,
      (hasOrders_iff_hasOrders_p4 H.nodeMap 2).mpr h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, fun d hd => (h2 d hd).symm,
      (hasOrders_iff_hasOrders_p4 H.faceMap k).mp h3,
      (hasOrders_iff_hasOrders_p4 H.edgeMap 2).mp h4,
      (hasOrders_iff_hasOrders_p4 H.nodeMap 2).mp h5⟩

/-- B12: a `Deformation` is injective on the finite vertex set for small
times.  Each pair `(v,w)` of distinct vertices is separated at `t = 0`
(`f v 0 = v`, `f w 0 = w`, continuity); the finite set `V × V` then yields
a positive minimum radius.  (Local copy: `CONT_ATREAL_INJ_PRESERVED_p37`
is declared later in this file, after `XRECQNS_UPDATE_p37`.) -/
private theorem w_b12_inj_window {V : Set V3} {f : V3 → ℝ → V3} {a b : ℝ}
    (hd : Deformation f V a b) (hV : V.Finite) (hne : V.Nonempty) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → Set.InjOn (fun v => f v t) V := by
  classical
  have hpair : ∀ p : V3 × V3, ∃ d : ℝ, 0 < d ∧
      ((p.1 ∈ V ∧ p.2 ∈ V ∧ p.1 ≠ p.2) → ∀ t : ℝ, |t| < d → f p.1 t ≠ f p.2 t) := by
    intro p
    by_cases hp : p.1 ∈ V ∧ p.2 ∈ V ∧ p.1 ≠ p.2
    · obtain ⟨h1V, h2V, hne'⟩ := hp
      have hcont : ContinuousAt (fun t => dist (f p.1 t) (f p.2 t)) 0 :=
        (hd.2.1 p.1 h1V 0 hd.1).dist (hd.2.1 p.2 h2V 0 hd.1)
      have hne0 : f p.1 0 ≠ f p.2 0 := by
        rw [hd.2.2 p.1 h1V, hd.2.2 p.2 h2V]
        exact hne'
      have hpos : (0 : ℝ) < dist (f p.1 0) (f p.2 0) := dist_pos.mpr hne0
      obtain ⟨d, hd0, hd1⟩ := Metric.continuousAt_iff.mp hcont
        (dist (f p.1 0) (f p.2 0) / 2) (by linarith)
      refine ⟨d, hd0, fun _ t ht heq => ?_⟩
      have h3 : dist (dist (f p.1 t) (f p.2 t)) (dist (f p.1 0) (f p.2 0)) <
          dist (f p.1 0) (f p.2 0) / 2 :=
        hd1 (by simpa [Real.dist_eq] using ht)
      have h4 : dist (0 : ℝ) (dist (f p.1 0) (f p.2 0)) = dist (f p.1 0) (f p.2 0) := by
        rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hpos]
      rw [heq, dist_self, h4] at h3
      linarith
    · exact ⟨1, one_pos, fun h _ _ => absurd h hp⟩
  let d : V3 × V3 → ℝ := fun p => Classical.choose (hpair p)
  have hdpos : ∀ p, 0 < d p := fun p => (Classical.choose_spec (hpair p)).1
  have hdprop : ∀ p, (p.1 ∈ V ∧ p.2 ∈ V ∧ p.1 ≠ p.2) →
      ∀ t : ℝ, |t| < d p → f p.1 t ≠ f p.2 t :=
    fun p => (Classical.choose_spec (hpair p)).2
  let S : Finset (V3 × V3) := hV.toFinset.product hV.toFinset
  have hSmem : ∀ p : V3 × V3, p ∈ S ↔ p.1 ∈ V ∧ p.2 ∈ V := by
    intro p
    have h1 : p ∈ S ↔ p.1 ∈ hV.toFinset ∧ p.2 ∈ hV.toFinset := Finset.mem_product
    rw [h1, hV.mem_toFinset, hV.mem_toFinset]
  have hSne : S.Nonempty := by
    obtain ⟨v0, hv0⟩ := hne
    exact ⟨(v0, v0), by rw [hSmem]; exact ⟨hv0, hv0⟩⟩
  obtain ⟨p0, -, hmin⟩ := Finset.exists_min_image S d hSne
  refine ⟨d p0, hdpos p0, fun t ht => ?_⟩
  intro v hv w hw heq
  by_contra hvw
  have hpS : (v, w) ∈ S := by rw [hSmem]; exact ⟨hv, hw⟩
  have ht' : |t| < d (v, w) := lt_of_lt_of_le ht (hmin (v, w) hpS)
  exact hdprop (v, w) ⟨hv, hw, hvw⟩ t ht' heq

/-- HOL `XRECQNS_UPDATE` (lunar_deform.hl:3073).  DISCHARGED (B12): the fan
component is LA17's `XRECQNS_p17` (fan transfer: `FAN7_SMALL_DEFORMATION_p17`
+ `w_xrq17_image_fan_data`); the injectivity window is the local
`w_b12_inj_window` (pairwise separation + finite minimum); the
hypermap-face/dih2k/2-regular
components transfer along the vertex bijection through the B10 kit
(`BIJ_AND_MAP_COMM_p37` / `HYP_ISO_LEMMAA_p37` /
`HYP_ISO_DIH2K_PRESERVED_p37` + `IMAGE_FACE_F_p37`). -/
theorem XRECQNS_UPDATE_p37 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {f : V3 → ℝ → V3} {a b : ℝ} (_hd : Deformation f V a b) (_hl : LocalFan V E FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
      LocalFan ((fun v => f v t) '' V)
        ((fun s => (fun v => f v t) '' s) '' E)
        ((fun p => (f p.1 t, f p.2 t)) '' FF) := by
  obtain ⟨hfan, x, hx, hFF, hD, h2reg⟩ := _hl
  have hlf : LocalFan V E FF := ⟨hfan, x, hx, hFF, hD, h2reg⟩
  obtain ⟨hVfin, hVne⟩ := hfan.2.2.1
  obtain ⟨einj, heinj, hinj⟩ := w_b12_inj_window (f := f) _hd hVfin
    (Set.nonempty_iff_ne_empty.mpr hVne)
  obtain ⟨efan, hefan, hfanz⟩ := XRECQNS_p17 a b V E f _hd hfan
  refine ⟨min efan einj, lt_min hefan heinj, fun t ht => ?_⟩
  have ht1 : -efan < t := by
    have h1 := (abs_lt.mp ht).1
    have h2 : min efan einj ≤ efan := min_le_left _ _
    linarith
  have ht2 : t < efan := by
    have h1 := (abs_lt.mp ht).2
    have h2 : min efan einj ≤ efan := min_le_left _ _
    linarith
  have htI : |t| < einj := lt_of_lt_of_le ht (min_le_right _ _)
  let g : V3 → V3 := fun v => f v t
  show LocalFan (g '' V) ((fun s => g '' s) '' E) ((fun p => (g p.1, g p.2)) '' FF)
  have hfan' : Fan.FAN 0 (g '' V) ((fun s => g '' s) '' E) := hfanz t ht1 ht2
  have hbij : Set.BijOn g V (g '' V) :=
    INJ_IMP_BIJ_IMAGE_p37 (S := V) (S' := g '' V) (hinj t htI)
  have hcomm := w5cB10_bij_and_map_comm (V' := g '' V)
    (E' := (fun s => g '' s) '' E) (f := g) hlf hbij rfl hfan'
  have hno : dartsOfHyp_p4 E V = Fan.dart1OfFan V E := w5cB10_hno hlf
  have hno' : dartsOfHyp_p4 ((fun s => g '' s) '' E) (g '' V)
      = Fan.dart1OfFan (g '' V) ((fun s => g '' s) '' E) :=
    w5cB10_hno_image (V' := g '' V) (E' := (fun s => g '' s) '' E) (f := g)
      (w5cB10_hedge hlf) hbij rfl
  have hiso := HYP_ISO_LEMMAA_p37 (V' := g '' V) (E' := (fun s => g '' s) '' E)
    (f := g) hlf hbij rfl hfan hfan'
  have hFFsub : FF ⊆ ((Fan.hypermapOfFan 0 V E hfan).darts : Set (V3 × V3)) := by
    rw [hFF]
    exact Hypermap.face_subset_darts (Fan.hypermapOfFan 0 V E hfan) hx
  have hinjpair : Set.InjOn (fun p : V3 × V3 => (g p.1, g p.2)) FF := by
    intro p hp q hq heq
    have hp1 : p ∈ Fan.dart1OfFan V E := (dartsLA1 0 V E hfan) ▸ hFFsub hp
    have hq1 : q ∈ Fan.dart1OfFan V E := (dartsLA1 0 V E hfan) ▸ hFFsub hq
    have hpD : p ∈ dartsOfHyp_p4 E V := hno.symm ▸ hp1
    have hqD : q ∈ dartsOfHyp_p4 E V := hno.symm ▸ hq1
    exact hcomm.1.2.1 hpD hqD heq
  have hncard : ((fun p : V3 × V3 => (g p.1, g p.2)) '' FF).ncard = FF.ncard :=
    Set.InjOn.ncard_image hinjpair
  have hx1 : x ∈ Fan.dart1OfFan V E := (dartsLA1 0 V E hfan) ▸ Finset.mem_coe.mpr hx
  have hxD : x ∈ dartsOfHyp_p4 E V := hno.symm ▸ hx1
  have hx'D : (fun p : V3 × V3 => (g p.1, g p.2)) x
      ∈ dartsOfHyp_p4 ((fun s => g '' s) '' E) (g '' V) := hcomm.1.1 hxD
  have hx'1 : (g x.1, g x.2) ∈ Fan.dart1OfFan (g '' V) ((fun s => g '' s) '' E) :=
    hno' ▸ hx'D
  refine ⟨hfan', (g x.1, g x.2), ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_coe.mp
      ((dartsLA1 0 (g '' V) ((fun s => g '' s) '' E) hfan').symm ▸ hx'1)
  · have hface := IMAGE_FACE_F_p37 hiso x (Finset.mem_coe.mpr hx)
    rw [hFF]
    exact hface
  · have hD37 : dih2k_p37 (Fan.hypermapOfFan 0 V E hfan) FF.ncard :=
      (w_b12_dih2k_p37_iff_Dih2k (Fan.hypermapOfFan 0 V E hfan) FF.ncard).mpr hD
    have hD37' := HYP_ISO_DIH2K_PRESERVED_p37
      (H := Fan.hypermapOfFan 0 V E hfan)
      (HH := Fan.hypermapOfFan 0 (g '' V) ((fun s => g '' s) '' E) hfan')
      (f := fun p : V3 × V3 => (g p.1, g p.2))
      (Fan.hypermapOfFan 0 V E hfan).darts.finite_toSet hD37 hiso
    rw [hncard]
    exact (w_b12_dih2k_p37_iff_Dih2k
      (Fan.hypermapOfFan 0 (g '' V) ((fun s => g '' s) '' E) hfan') FF.ncard).mp hD37'
  · intro u' hu'
    obtain ⟨u, hu, rfl⟩ := hu'
    have hEEV : EE_p4 u E ⊆ V := fun p hp =>
      hfan.1 (Set.mem_sUnion_of_mem (by simp) hp)
    have hEEimg : EE_p4 (g u) ((fun s => g '' s) '' E) = g '' EE_p4 u E :=
      w5cB10_EE_image (V' := g '' V) (E' := (fun s => g '' s) '' E) (f := g)
        hbij rfl hfan.2.1 hfan.1 hu
    show (ee (g u) ((fun s => g '' s) '' E)).ncard = 2
    rw [show ee (g u) ((fun s => g '' s) '' E)
        = EE_p4 (g u) ((fun s => g '' s) '' E) from rfl, hEEimg,
      Set.InjOn.ncard_image (fun p hp q hq heq =>
        hbij.2.1 (hEEV hp) (hEEV hq) heq)]
    exact h2reg u hu

/-- HOL `NORM_CROSS_LE` (lunar_deform.hl:3200): `|u cross v| <= |u| |v|`
(via Mathlib's sin-of-angle form of the cross-product norm). -/
theorem NORM_CROSS_LE_p37 (u w : V3) : ‖cross3_p37 u w‖ ≤ ‖u‖ * ‖w‖ := by
  rw [cross3_p37, InnerProductGeometry.norm_toLp_symm_crossProduct]
  simp only [WithLp.toLp_ofLp]
  calc ‖u‖ * ‖w‖ * Real.sin (InnerProductGeometry.angle u w)
      ≤ ‖u‖ * ‖w‖ * 1 :=
        mul_le_mul_of_nonneg_left (Real.sin_le_one (InnerProductGeometry.angle u w))
          (mul_nonneg (norm_nonneg u) (norm_nonneg w))
    _ = ‖u‖ * ‖w‖ := by rw [mul_one]

/-- HOL `CONT_ATREAL_INJ_PRESERVED` (lunar_deform.hl:3043).  NEEDS: the
`Local_lemmas1.CONTINUOUS_ATREAL_INJ_PRESERVED` twin (unbuilt LocalAuto6,
itself `sorry` there). -/
theorem CONT_ATREAL_INJ_PRESERVED_p37 {V : Set V3} {ff : V3 → ℝ → V3} {r : ℝ}
    (_hV : V.Finite) (_hc : ∀ v ∈ V, ContinuousAt (ff v) r)
    (_hinj : Set.InjOn (fun v => ff v r) V) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t - r| < e →
      Set.InjOn (fun v => ff v t) V := by
  classical
  have hpair : ∀ p : V3 × V3, ∃ d : ℝ, 0 < d ∧
      ((p.1 ∈ V ∧ p.2 ∈ V ∧ p.1 ≠ p.2) → ∀ t : ℝ, |t - r| < d → ff p.1 t ≠ ff p.2 t) := by
    intro p
    by_cases hd : p.1 ∈ V ∧ p.2 ∈ V ∧ p.1 ≠ p.2
    · have hcon : ContinuousAt (fun t => dist (ff p.1 t) (ff p.2 t)) r :=
        (_hc p.1 hd.1).dist (_hc p.2 hd.2.1)
      have hne : ff p.1 r ≠ ff p.2 r := fun heq => hd.2.2 (_hinj hd.1 hd.2.1 heq)
      have hpos : (0 : ℝ) < dist (ff p.1 r) (ff p.2 r) := dist_pos.mpr hne
      obtain ⟨d, hd0, hd1⟩ := Metric.continuousAt_iff.mp hcon
        (dist (ff p.1 r) (ff p.2 r) / 2) (by linarith)
      refine ⟨d, hd0, fun _ t ht => ?_⟩
      have h3 : dist (dist (ff p.1 t) (ff p.2 t)) (dist (ff p.1 r) (ff p.2 r)) <
          dist (ff p.1 r) (ff p.2 r) / 2 :=
        hd1 (by rw [Real.dist_eq]; exact ht)
      have hd2 : (0 : ℝ) < dist (ff p.1 t) (ff p.2 t) := by
        rw [Real.dist_eq] at h3
        obtain ⟨h3a, -⟩ := abs_lt.mp h3
        linarith
      intro heq
      rw [dist_eq_zero.mpr heq] at hd2
      exact lt_irrefl (0 : ℝ) hd2
    · refine ⟨1, by norm_num, ?_⟩
      intro hh
      exact absurd hh hd
  choose d hd using hpair
  by_cases hV : V.Nonempty
  · obtain ⟨v0, hv0⟩ := hV
    have hPf : ((V ×ˢ V) : Set (V3 × V3)).Finite := _hV.prod _hV
    have hSne : (hPf.toFinset.image (fun p : V3 × V3 => d p)).Nonempty := by
      refine ⟨d (v0, v0), ?_⟩
      exact Finset.mem_image.mpr ⟨(v0, v0), by
        rw [Set.Finite.mem_toFinset]
        exact ⟨hv0, hv0⟩, rfl⟩
    have hminpos : 0 < Finset.min'
        (hPf.toFinset.image (fun p : V3 × V3 => d p)) hSne := by
      have hmem := Finset.mem_image.mp (Finset.min'_mem _ hSne)
      obtain ⟨p, hp, he⟩ := hmem
      obtain ⟨h1, -⟩ := hd p
      rw [← he]
      exact h1
    refine ⟨Finset.min' (hPf.toFinset.image (fun p : V3 × V3 => d p)) hSne,
      hminpos, ?_⟩
    intro t ht u hu u' hu' heq
    by_cases hne : u = u'
    · exact hne
    · have hpS : (u, u') ∈ hPf.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨hu, hu'⟩
      have hle := Finset.min'_le (hPf.toFinset.image (fun p : V3 × V3 => d p))
        (d (u, u')) (Finset.mem_image.mpr ⟨(u, u'), hpS, rfl⟩)
      obtain ⟨-, hinj⟩ := hd (u, u')
      exact absurd heq (hinj ⟨hu, hu', hne⟩ t (lt_of_lt_of_le ht hle))
  · refine ⟨1, by norm_num, ?_⟩
    intro t _ u hu
    exact absurd ⟨u, hu⟩ hV

/-- HOL `INJ_BIJ_IMAGE` (lunar_deform.hl:3066). -/
theorem INJ_BIJ_IMAGE_p37 {f : V3 → V3} {S S' A : Set V3}
    (h : Set.InjOn f S) (hA : A ⊆ S) : Set.BijOn f A (f '' A) :=
  ⟨Set.mapsTo_image f A, h.mono hA, Set.surjOn_image f A⟩

/-- HOL `CONT_ATREAL_REAL_CONTS` (lunar_deform.hl:3214): post-composing with
`cross _ y` and a fixed dot product keeps continuity. -/
theorem CONT_ATREAL_REAL_CONTS_p37 {f : ℝ → V3} {r : ℝ} {x y : V3}
    (h : ContinuousAt f r) :
    ContinuousAt
      (fun s => ((cross3_p37 (f s) y : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((cross3_p37 x y : V3) : Fin 3 → ℝ)) r := by
  have hcross : Continuous fun w : Fin 3 → ℝ => crossProduct w ((y : V3) : Fin 3 → ℝ) :=
    LinearMap.continuous_of_finiteDimensional (LinearMap.flip crossProduct ((y : V3) : Fin 3 → ℝ))
  have h2 : Continuous fun z : V3 => ((z : V3) : Fin 3 → ℝ) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)
  have h3 : Continuous fun w : Fin 3 → ℝ => WithLp.toLp 2 w :=
    PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)
  have hmidG : Continuous (fun z : V3 => cross3_p37 z y) :=
    Continuous.comp h3 (hcross.comp h2)
  have hstep : Continuous (fun z : V3 => ((cross3_p37 z y : V3) : Fin 3 → ℝ)) :=
    Continuous.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)) hmidG
  have h1 : ContinuousAt (fun s : ℝ => ((cross3_p37 (f s) y : V3) : Fin 3 → ℝ)) r :=
    (hstep.continuousAt).comp h
  have hfun : Continuous fun w : Fin 3 → ℝ =>
      w ⬝ᵥ ((cross3_p37 x y : V3) : Fin 3 → ℝ) := by
    unfold dotProduct
    exact continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).mul continuous_const)
  exact hfun.continuousAt.comp h1

/-- HOL `CONTINUOUS_POS_PRES` (lunar_deform.hl:3288).  NEEDS: the
coefficient-extraction kit (`CONT_ATREAL_REAL_CONTS` numeric margins +
`Collect_geom` affine representation). -/
theorem CONTINUOUS_POS_PRES_p37 {x y : V3} {a b r : ℝ} {f : ℝ → V3}
    (_hnc : ¬Collinear ℝ ({x, y, (0 : V3)} : Set V3)) (_hab : f r = a • x + b • y)
    (_h0 : 0 < a) (_hc : ContinuousAt f r) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → ∀ t1 t2 : ℝ,
      f (r + t) = t1 • x + t2 • y → 0 < t1 := by
  classical
  have hx0 : x ≠ 0 := by
    intro he
    apply _hnc
    have hset : ({x, y, (0 : V3)} : Set V3) = ({y, (0 : V3)} : Set V3) := by
      rw [he]; ext z; simp
    rw [hset]
    exact collinear_pair ℝ y (0 : V3)
  have hy0 : y ≠ 0 := by
    intro he
    apply _hnc
    have hset : ({x, y, (0 : V3)} : Set V3) = ({x, (0 : V3)} : Set V3) := by
      rw [he]; ext z; simp
    rw [hset]
    exact collinear_pair ℝ x (0 : V3)
  have hyv : y ⬝ᵥ y ≠ 0 := by
    intro he
    have h2 : ‖y‖ ^ 2 = (0 : ℝ) := by rw [norm_sq_eq_dot y]; exact he
    exact hy0 (norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2))
  have hD : (x ⬝ᵥ x) * (y ⬝ᵥ y) - (x ⬝ᵥ y) * (x ⬝ᵥ y) ≠ 0 := by
    intro hD0
    apply _hnc
    have hset0 : ({0, y, x} : Set V3) = ({x, y, 0} : Set V3) := by
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [← hset0]
    have hcy : (x ⬝ᵥ y) / (y ⬝ᵥ y) * (y ⬝ᵥ y) = x ⬝ᵥ y :=
      div_mul_cancel₀ (x ⬝ᵥ y) hyv
    have hnorm : ‖x - ((x ⬝ᵥ y) / (y ⬝ᵥ y)) • y‖ ^ 2 =
        ((x ⬝ᵥ x) * (y ⬝ᵥ y) - (x ⬝ᵥ y) * (x ⬝ᵥ y)) / (y ⬝ᵥ y) := by
      rw [norm_sq_eq_dot]
      simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm]
      rw [hcy, sub_self, sub_zero, sub_div, mul_div_assoc (x ⬝ᵥ x) (y ⬝ᵥ y) (y ⬝ᵥ y),
        div_self hyv, mul_one, div_mul_eq_mul_div]
    have hzero : ‖x - ((x ⬝ᵥ y) / (y ⬝ᵥ y)) • y‖ ^ 2 = (0 : ℝ) := by
      rw [hnorm, hD0, zero_div]
    have hxpy : x = ((x ⬝ᵥ y) / (y ⬝ᵥ y)) • y :=
      sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hzero))
    exact (collinear3_iff_smul (v := (0 : V3)) (w := y) (w1 := x) hy0).mpr ⟨_, by
      rw [sub_zero, sub_zero, hxpy]⟩
  have hcoe : Continuous fun z : V3 => ((z : V3) : Fin 3 → ℝ) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)
  have hdotx : Continuous fun p : V3 => p ⬝ᵥ x := by
    simp only [dotProduct]
    exact continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).comp hcoe).mul continuous_const
  have hdoty : Continuous fun p : V3 => p ⬝ᵥ y := by
    simp only [dotProduct]
    exact continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).comp hcoe).mul continuous_const
  set g : V3 → ℝ := fun p =>
    ((p ⬝ᵥ x) * (y ⬝ᵥ y) - (p ⬝ᵥ y) * (x ⬝ᵥ y)) /
      ((x ⬝ᵥ x) * (y ⬝ᵥ y) - (x ⬝ᵥ y) * (x ⬝ᵥ y)) with hg
  have hgcont : ContinuousAt g (f r) :=
    (((hdotx.mul continuous_const).sub (hdoty.mul continuous_const)).div continuous_const
      (fun _p => hD)).continuousAt
  have hcoef1 : ∀ t1 t2 : ℝ, (t1 • x + t2 • y) ⬝ᵥ x = t1 * (x ⬝ᵥ x) + t2 * (x ⬝ᵥ y) := by
    intro t1 t2
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  have hcoef2 : ∀ t1 t2 : ℝ, (t1 • x + t2 • y) ⬝ᵥ y = t1 * (x ⬝ᵥ y) + t2 * (y ⬝ᵥ y) := by
    intro t1 t2
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have hgfr : g (f r) = a := by
    simp only [hg, _hab, hcoef1, hcoef2]
    rw [div_eq_iff hD]
    ring
  obtain ⟨e0, he0, he⟩ := Metric.continuousAt_iff.mp hgcont (a / 2) (by linarith)
  obtain ⟨ef, hef0, hef⟩ := Metric.continuousAt_iff.mp _hc e0 he0
  refine ⟨ef, hef0, ?_⟩
  intro t ht t1 t2 hf
  have hgt : g (f (r + t)) = t1 := by
    simp only [hg, hf, hcoef1, hcoef2]
    rw [div_eq_iff hD]
    ring
  have hpt : dist (f (r + t)) (f r) < e0 := hef (by
    rw [Real.dist_eq, show (r + t) - r = (t : ℝ) from by ring]
    exact ht)
  have hw : |g (f (r + t)) - g (f r)| < a / 2 := he hpt
  rw [hgfr] at hw
  rcases abs_lt.mp hw with ⟨ha1, ha2⟩
  rw [← hgt]
  linarith

/-- HOL `IVS_RHO_NODE_V_IN_FF` (lunar_deform.hl:3334).  NEEDS:
`Local_lemmas.LOCAL_FAN_RHO_NODE_PROS2` + `Local_lemmas1.LOCAL_FAN_IVS_IN_V`
twins (fan substance beyond the registry stub). -/
theorem IVS_RHO_NODE_V_IN_FF_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (_h : LocalFan V E FF) (hv : v ∈ V) :
    (ivsRhoNode1 FF v, v) ∈ FF := by
  have h2 := w5cB5_to_localFan_p2 _h
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := _h
  have hee : (ee v E).ncard = 2 := h2reg v hv
  obtain ⟨w1, w2, hw12, hset⟩ := Set.ncard_eq_two.mp hee
  have h1mem : w1 ∈ (ee v E) := by rw [hset]; simp
  have h2mem : w2 ∈ (ee v E) := by rw [hset]; simp
  have hE1 : ({v, w1} : Set V3) ∈ E := h1mem
  have hE2 : ({v, w2} : Set V3) ∈ E := h2mem
  rcases LOFA_IN_E_IMP_IN_FF h2 hE1 with hd | hd
  · rcases LOFA_IN_E_IMP_IN_FF h2 hE2 with hd2 | hd2
    · exact absurd (congrArg Prod.snd ((WRGCVDR_BIJ h2).2.1 hd hd2 rfl)) hw12
    · exact Classical.epsilon_spec (p := fun a : V3 => (a, v) ∈ FF) ⟨w2, hd2⟩
  · exact Classical.epsilon_spec (p := fun a : V3 => (a, v) ∈ FF) ⟨w1, hd⟩

/-- HOL `IN_AFF_GT_IMP_AZIMEQ` (lunar_deform.hl:3348): `azim` is constant
along `aff_gt {u,v} {y}` rays.  NEEDS: `AZIM_DEGENERATE` + the
`aff_gt`-ray `azim` invariance kit. -/
theorem IN_AFF_GT_IMP_AZIMEQ_p37 {u v w x y : V3}
    (_hx : x ∈ affGt {u, v} {y}) : azim u v w x = azim u v w y := by
  have htr : Collinear ℝ ({u, v, x} : Set V3) ↔ Collinear ℝ ({u, v, y} : Set V3) :=
    w5cB_collinear3_affGt_transfer _hx
  by_cases hcw : Collinear ℝ ({u, v, w} : Set V3)
  · have hcw3 : Collinear3 u v w := hcw
    unfold azim
    rw [if_pos (Or.inl hcw3), if_pos (Or.inl hcw3)]
  · by_cases hcy : Collinear ℝ ({u, v, y} : Set V3)
    · have hcx := htr.mpr hcy
      have hcy3 : Collinear3 u v y := hcy
      have hcx3 : Collinear3 u v x := hcx
      unfold azim
      rw [if_pos (Or.inr hcx3), if_pos (Or.inr hcy3)]
    · have hcx : ¬Collinear ℝ ({u, v, x} : Set V3) := fun hc => hcy (htr.mp hc)
      exact (azim_eq_azim_iff_alt hcw hcx hcy).mpr _hx

/-- HOL `IN_AFF_GT_IMP_AZIMEQ2` (lunar_deform.hl:3384). -/
theorem IN_AFF_GT_IMP_AZIMEQ2_p37 {u v x y : V3} (hx : x ∈ affGt {u, v} {y})
    (w : V3) : azim u v w x = azim u v w y :=
  IN_AFF_GT_IMP_AZIMEQ_p37 hx

/-- HOL `plane P` (Collect_geom): `P` is the affine hull of three
non-collinear points.  NEEDS: verbatim check against the azure `plane`
definition before merging. -/
def PlaneP_p37 (P : Set V3) : Prop :=
  ∃ a b c : V3, ¬Collinear ℝ ({a, b, c} : Set V3) ∧ P = affineSpan ℝ ({a, b, c} : Set V3)

/-- W5c-B6 助件：`⬝ᵥ`（V3 内积）与 Fin 3 → ℝ 点积的传递（定义相等）。 -/
private theorem w5cB6_dot_ofLp (x y : V3) :
    (x : V3) ⬝ᵥ (y : V3) = ((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y : V3) : Fin 3 → ℝ) := rfl

/-- W5c-B6 助件：`cross3_p37` 的点积的 Fin 3 形（定义相等）。 -/
private theorem w5cB6_cross3_dot (x y z : V3) :
    cross3_p37 x y ⬝ᵥ z =
      (crossProduct ((x : V3) : Fin 3 → ℝ) ((y : V3) : Fin 3 → ℝ)) ⬝ᵥ
        ((z : V3) : Fin 3 → ℝ) := rfl

/-- W5c-B6 助件：`span ℝ {A, B}` 对 `c • (p₁ -ᵥ p₂) +ᵥ p₃` 封闭
（纯 Submodule 线性组合）。 -/
private theorem w5cB6_span_smul_vsub_vadd_mem {A B : V3} (c : ℝ)
    {p₁ p₂ p₃ : V3} (hp₁ : p₁ ∈ (Submodule.span ℝ {A, B}))
    (hp₂ : p₂ ∈ (Submodule.span ℝ {A, B}))
    (hp₃ : p₃ ∈ (Submodule.span ℝ {A, B})) :
    c • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ (Submodule.span ℝ {A, B}) := by
  obtain ⟨α, β, hα⟩ := Submodule.mem_span_pair.mp hp₁
  obtain ⟨μ, ν, hμ⟩ := Submodule.mem_span_pair.mp hp₂
  obtain ⟨γ, δ, hγ⟩ := Submodule.mem_span_pair.mp hp₃
  rw [← hα, ← hμ, ← hγ, vadd_eq_add, vsub_eq_sub, smul_sub]
  refine Submodule.mem_span_pair.mpr ⟨c * α + γ - c * μ, c * β + δ - c * ν, ?_⟩
  module

/-- W5c-B6 助件：`0` 入座的三点仿射包落在二元线性包内
（`affineSpan_le` + submodule 即 affine subspace）。 -/
private theorem w5cB6_mem_span_of_affSpan0 {A B w : V3}
    (hw : w ∈ (affineSpan ℝ ({0, A, B} : Set V3))) :
    w ∈ (Submodule.span ℝ {A, B}) := by
  have hQ : (affineSpan ℝ ({0, A, B} : Set V3)) ≤
      (AffineSubspace.mk ((Submodule.span ℝ {A, B} : Set V3))
        (fun c p₁ p₂ p₃ hp₁ hp₂ hp₃ =>
          w5cB6_span_smul_vsub_vadd_mem c hp₁ hp₂ hp₃)) := by
    refine affineSpan_le.mpr ?_
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact Submodule.zero_mem _
    · rcases Set.mem_insert_iff.mp hz with rfl | rfl
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact hQ hw

/-- W5c-B6 助件：非共线 `{0, A, B}` 确定的平面（`affineSpan {0,A,B} = Q`）内任意点与
`cross A B` 点积为零——`DET_CROSS`（三重积 = 行列式）+ 双重复行置零。 -/
private theorem w5cB6_cross_dot_of_mem_affSpan0 {A B z : V3}
    (hnc : ¬Collinear ℝ ({0, A, B} : Set V3))
    (hz : z ∈ (affineSpan ℝ ({0, A, B} : Set V3))) :
    cross3_p37 A B ⬝ᵥ z = 0 := by
  have hw : z ∈ (Submodule.span ℝ {A, B}) := w5cB6_mem_span_of_affSpan0 hz
  obtain ⟨α, β, hz'⟩ := Submodule.mem_span_pair.mp hw
  have hA : cross3_p37 A B ⬝ᵥ A = 0 := by
    rw [w5cB6_cross3_dot, ← DET_CROSS A B A]
    exact Matrix.det_zero_of_row_eq (i := (0 : Fin 3)) (j := (2 : Fin 3))
      (by decide) (by funext j; simp)
  have hB : cross3_p37 A B ⬝ᵥ B = 0 := by
    rw [w5cB6_cross3_dot, ← DET_CROSS A B B]
    exact Matrix.det_zero_of_row_eq (i := (1 : Fin 3)) (j := (2 : Fin 3))
      (by decide) (by funext j; simp)
  rw [← hz']
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, dotProduct_add, dotProduct_smul,
    smul_eq_mul, hA, hB]
  ring

/-- HOL `CROSS_IN_SAME_DIRECTION` (lunar_deform.hl:3389): consecutive
`rho_node1` crosses point along the initial cross direction.  消费 LA5 净证
`RHO_NODE_SET_IN_A_PLANE_IMP_POS_DIRECT`（正点积）+ 平面正交重构：
`{A, B, e}` 行列式非零（`DET_CROSS`）张成全空间，`C - k•e` 全空间正交故为零。
（B6 收敛：w5cB5 draft 的 8 处收尾点 (a)-(h) 逐条落定。） -/
theorem CROSS_IN_SAME_DIRECTION_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3} {e : V3}
    (_hlf : LocalFan V E FF) (_hv : v ∈ V)
    (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
    (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P)
    (_he : cross3_p37 v (rhoNode1 FF v) = e) :
    ∀ i < l, ∃ k : ℝ, 0 < k ∧
      cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) = k • e := by
  classical
  have h2 := w5cB5_to_localFan_p2 _hlf
  have hP2 : plane_p2 P := _hP
  have hmemV : ∀ n : ℕ, (rhoNode1 FF)^[n] v ∈ V := LOCAL_FAN_ITER_RHO_NODE_IN_V h2 _hv
  have hUmem : ∀ n : ℕ, n ≤ l → (rhoNode1 FF)^[n] v ∈ U := fun n hn => by
    rw [← _hU]
    exact ⟨n, hn, rfl⟩
  have hU' : {(rhoNode1_p2 FF)^[n] v | n ≤ l} = U := by
    ext z
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [← _hU]
      exact ⟨n, hn, rfl⟩
    · intro hz
      rw [← _hU] at hz
      obtain ⟨n, hn, rfl⟩ := hz
      exact ⟨n, hn, rfl⟩
  have he' : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e := _he
  have hpos : ∀ i : ℕ, i < l →
      0 < cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) ⬝ᵥ e :=
    RHO_NODE_SET_IN_A_PLANE_IMP_POS_DIRECT h2 _hv hU' hP2 _h0 _hUsub he'
  by_cases hl : l = 0
  · intro i hi
    rw [hl] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · have h0l : 0 < l := Nat.pos_of_ne_zero hl
    have h0e : 0 < cross3_p37 v (rhoNode1 FF v) ⬝ᵥ (e : V3) := hpos 0 h0l
    rw [_he] at h0e
    have hEpos : 0 < e ⬝ᵥ (e : V3) := h0e
    have hEne : (e : V3) ≠ 0 := fun h0 => by
      rw [h0] at hEpos
      simp at hEpos
    have hv1 : (rhoNode1 FF)^[1] v ∈ P := _hUsub (hUmem 1 h0l)
    have hncV : ¬Collinear ℝ ({0, v, rhoNode1 FF v} : Set V3) := by
      intro hc
      have hcz := COLLINEAR_CROSS_0 (x := (0 : V3)) (y := v)
        (z := rhoNode1 FF v) |>.mp hc
      rw [sub_zero, sub_zero] at hcz
      have hcz2 : cross3_p37 v (rhoNode1 FF v) = 0 := hcz
      rw [_he] at hcz2
      exact hEne hcz2
    have hPspanV : (affineSpan ℝ ({0, v, rhoNode1 FF v} : Set V3)) = P :=
      THREE_NOT_COLL_DETER_PLANE hP2
        (by
          intro z hz
          rcases Set.mem_insert_iff.mp hz with rfl | hz
          · exact _h0
          · rcases Set.mem_insert_iff.mp hz with rfl | rfl
            · exact _hUsub (hUmem 0 (Nat.zero_le l))
            · exact hv1)
        hncV
    intro i hi
    have hAU : (rhoNode1 FF)^[i] v ∈ U := hUmem i (Nat.le_of_lt hi)
    have hBU : (rhoNode1 FF)^[i + 1] v ∈ U := hUmem (i + 1) (Nat.succ_le_of_lt hi)
    have hAP : (rhoNode1 FF)^[i] v ∈ P := _hUsub hAU
    have hBP : (rhoNode1 FF)^[i + 1] v ∈ P := _hUsub hBU
    have hCpos : 0 < cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) ⬝ᵥ e :=
      hpos i hi
    have hCne : cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) ≠ 0 := by
      intro h0
      rw [h0] at hCpos
      simp at hCpos
    have hncAB : ¬Collinear ℝ ({0, (rhoNode1 FF)^[i] v,
        (rhoNode1 FF)^[i + 1] v} : Set V3) := by
      intro hc
      have hcz := COLLINEAR_CROSS_0 (x := (0 : V3)) (y := (rhoNode1 FF)^[i] v)
        (z := (rhoNode1 FF)^[i + 1] v) |>.mp hc
      rw [sub_zero, sub_zero] at hcz
      exact hCne hcz
    have hPspanAB : (affineSpan ℝ ({0, (rhoNode1 FF)^[i] v,
        (rhoNode1 FF)^[i + 1] v} : Set V3)) = P :=
      THREE_NOT_COLL_DETER_PLANE hP2
        (by
          intro z hz
          rcases Set.mem_insert_iff.mp hz with rfl | hz
          · exact _h0
          · rcases Set.mem_insert_iff.mp hz with rfl | rfl
            · exact hAP
            · exact hBP)
        hncAB
    set A : V3 := (rhoNode1 FF)^[i] v with hAdef
    set B : V3 := (rhoNode1 FF)^[i + 1] v with hBdef
    set C : V3 := cross3_p37 A B with hCdef
    have hCperp : ∀ z ∈ P, C ⬝ᵥ z = 0 := by
      intro z hzP
      have hz2 : z ∈ ((affineSpan ℝ ({0, A, B} : Set V3) : Set V3)) :=
        hPspanAB.symm ▸ hzP
      exact w5cB6_cross_dot_of_mem_affSpan0 hncAB hz2
    have heperp : ∀ z ∈ P, cross3_p37 v (rhoNode1 FF v) ⬝ᵥ z = 0 := by
      intro z hzP
      have hz2 : z ∈ ((affineSpan ℝ ({0, v, rhoNode1 FF v} : Set V3) : Set V3)) :=
        hPspanV.symm ▸ hzP
      exact w5cB6_cross_dot_of_mem_affSpan0 hncV hz2
    rw [_he] at heperp
    have hAC : C ⬝ᵥ A = 0 := hCperp A hAP
    have hBC : C ⬝ᵥ B = 0 := hCperp B hBP
    have hAE : e ⬝ᵥ A = 0 := heperp A hAP
    have hBE : e ⬝ᵥ B = 0 := heperp B hBP
    -- 行列式非零 ⇒ {A', B', e'} 线性无关 ⇒ 张成全空间
    set Mrow : Fin 3 → Fin 3 → ℝ :=
      fun i j => (![A, B, e] : Fin 3 → V3) i j with hMrowdef
    have hdet : Matrix.det (Matrix.of Mrow) ≠ 0 := by
      intro h0
      have h1 := DET_CROSS A B e
      rw [h0] at h1
      rw [← w5cB6_cross3_dot] at h1
      linarith [hCpos, h1]
    have hli : LinearIndependent ℝ Mrow := by
      refine Matrix.linearIndependent_rows_of_isUnit ?_
      refine (Matrix.isUnit_iff_isUnit_det (A := Matrix.of Mrow)).mpr ?_
      exact (isUnit_iff_ne_zero).mpr hdet
    have htop : (Submodule.span ℝ (Set.range Mrow)) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [finrank_span_eq_card hli]
      simp [Module.finrank_fin_fun]
    set k : ℝ := C ⬝ᵥ e / (e ⬝ᵥ (e : V3)) with hkdef
    have hkpos : 0 < k := by rw [hkdef]; exact div_pos hCpos hEpos
    refine ⟨k, hkpos, ?_⟩
    have hDfin : ((C - k • e : V3) : Fin 3 → ℝ) = 0 := by
      apply dotProduct_self_eq_zero.mp
      have hmem : ((C - k • e : V3) : Fin 3 → ℝ) ∈
          (Submodule.span ℝ (Set.range Mrow)) := by
        rw [htop]
        exact Submodule.mem_top
      clear hli htop hdet
      have hperp0 : ∀ u ∈ ((Submodule.span ℝ (Set.range Mrow) : Set (Fin 3 → ℝ))),
          ((C - k • e : V3) : Fin 3 → ℝ) ⬝ᵥ u = 0 := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem w hw' =>
            obtain ⟨j, rfl⟩ := hw'
            fin_cases j
            · show ((C - k • e : V3) : Fin 3 → ℝ) ⬝ᵥ ((A : V3) : Fin 3 → ℝ) = 0
              rw [show ((C - k • e : V3) : Fin 3 → ℝ)
                  = ((C : V3) : Fin 3 → ℝ) - k • ((e : V3) : Fin 3 → ℝ) from rfl,
                sub_dotProduct, smul_dotProduct, ← w5cB6_dot_ofLp, ← w5cB6_dot_ofLp,
                hAC, hAE, hkdef]
              ring
            · show ((C - k • e : V3) : Fin 3 → ℝ) ⬝ᵥ ((B : V3) : Fin 3 → ℝ) = 0
              rw [show ((C - k • e : V3) : Fin 3 → ℝ)
                  = ((C : V3) : Fin 3 → ℝ) - k • ((e : V3) : Fin 3 → ℝ) from rfl,
                sub_dotProduct, smul_dotProduct, ← w5cB6_dot_ofLp, ← w5cB6_dot_ofLp,
                hBC, hBE, hkdef]
              ring
            · show ((C - k • e : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ) = 0
              rw [show ((C - k • e : V3) : Fin 3 → ℝ)
                  = ((C : V3) : Fin 3 → ℝ) - k • ((e : V3) : Fin 3 → ℝ) from rfl,
                sub_dotProduct, smul_dotProduct, ← w5cB6_dot_ofLp, ← w5cB6_dot_ofLp,
                hkdef, smul_eq_mul]
              field_simp
              ring
        | zero => simp
        | add x y hx hy ihx ihy => rw [dotProduct_add, ihx, ihy]; ring
        | smul r x hx ihx => rw [dotProduct_smul, ihx]; ring
      exact hperp0 _ hmem
    rw [← sub_eq_zero]
    show (WithLp.toLp 2 ((C - k • e : V3) : Fin 3 → ℝ) : V3) = 0
    rw [hDfin]
    rfl

/-- HOL `ITER_CROSS_SAME_DIRECTION` (lunar_deform.hl:3461): all consecutive
crosses are positive multiples of one another.  消费 `CROSS_IN_SAME_DIRECTION_p37`
两次（`e` 即初始 cross）+ 除法代数。 -/
theorem ITER_CROSS_SAME_DIRECTION_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
    (_hlf : LocalFan V E FF) (_hv : v ∈ V)
    (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
    (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P) :
    ∀ i j, i < l → j < l → ∃ k : ℝ, 0 < k ∧
      cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) =
        k • (cross3_p37 ((rhoNode1 FF)^[j] v) ((rhoNode1 FF)^[j + 1] v)) := by
  intro i j hi hj
  obtain ⟨k1, hk1, heq1⟩ :=
    CROSS_IN_SAME_DIRECTION_p37 _hlf _hv _hU _hP _h0 _hUsub rfl i hi
  obtain ⟨k2, hk2, heq2⟩ :=
    CROSS_IN_SAME_DIRECTION_p37 _hlf _hv _hU _hP _h0 _hUsub rfl j hj
  refine ⟨k1 / k2, div_pos hk1 hk2, ?_⟩
  rw [heq1, heq2, smul_smul]
  field_simp

/-- HOL `LOCAL_FAN_CHARACTER_OF_RHO_NODE3` (local_lemmas.hl:7065) 的本 port 形：
LA5 `LOCAL_FAN_ITER_RHO_NODE_IN_V` + LA5 `LOCAL_FAN_CHARACTER_OF_RHO_NODE2`
（对 `w := ρ^[i] v` 逐点应用）。B8 轮 2-strike 止损：主体已写至收尾态
（Kit-draft-w5cB8.lean，余 6 处机械收尾点已逐条注记），B9 首项照录收口。 -/
private theorem w5cB7_char3 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) (i : ℕ) :
    ¬Collinear ℝ ({0, (rhoNode1_p2 FF)^[i] v, (rhoNode1_p2 FF)^[i + 1] v} : Set V3) := by
  have hbase : ¬Collinear ℝ ({0, (rhoNode1_p2 FF)^[i] v,
      rhoNode1_p2 FF ((rhoNode1_p2 FF)^[i] v)} : Set V3) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h (LOCAL_FAN_ITER_RHO_NODE_IN_V h hv i)
  rw [(Function.iterate_succ_apply' (rhoNode1_p2 FF) i v)]
  exact hbase

/-- HOL `ITER_IN_AFF_GT_2_1` (lunar_deform.hl:3486)。本 port：`ρ^[i+2] v` 在
`ρ^i` 关于轴 `0, ρ^{i+1}` 的对侧。证法：`w5cB7_char3` 给非共线 → 三点确定平面
`P`；`w5cB6_mem_span_of_affSpan0` 把 `ρ^{i+2}` 落入 `span {ρ^i, ρ^{i+1}}`
（系数 `a b`）；`ITER_CROSS_SAME_DIRECTION_p37` 给 `cross(ρ^{i+1}, ρ^{i+2}) =
k • cross(ρ^i, ρ^{i+1})`（`k > 0`），线性展开比对得 `a = -k`，再以
`w5cB_affLt_2_1_mpr` 三系数形（`t3 = -k < 0`）构造。 -/
theorem ITER_IN_AFF_GT_2_1_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
    (_hlf : LocalFan V E FF) (_hv : v ∈ V)
    (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
    (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P) :
    ∀ i < l - 1,
      (rhoNode1 FF)^[i + 2] v ∈
        affLt {0, (rhoNode1 FF)^[i + 1] v} {(rhoNode1 FF)^[i] v} := by
  classical
  have h2 := w5cB5_to_localFan_p2 _hlf
  have hP2 : plane_p2 P := _hP
  have hfan : Fan.FAN 0 V E := _hlf.1
  have hmemV : ∀ n : ℕ, (rhoNode1 FF)^[n] v ∈ V := LOCAL_FAN_ITER_RHO_NODE_IN_V h2 _hv
  have hUmem : ∀ n : ℕ, n ≤ l → (rhoNode1 FF)^[n] v ∈ U := fun n hn => by
    rw [← _hU]
    exact ⟨n, hn, rfl⟩
  intro i hi
  have hmemVi := hmemV i
  have hmemVi1 := hmemV (i + 1)
  have h0X : (0 : V3) ≠ (rhoNode1 FF)^[i] v :=
    Ne.symm (FAN_IMP_V_DIFF hfan ((rhoNode1 FF)^[i] v) hmemVi)
  have hncXY : ¬Collinear ℝ ({0, (rhoNode1 FF)^[i] v,
      (rhoNode1 FF)^[i + 1] v} : Set V3) := w5cB7_char3 h2 _hv i
  have hXYne : (rhoNode1 FF)^[i] v ≠ (rhoNode1 FF)^[i + 1] v := by
    intro hXY
    refine hncXY ?_
    rw [COLLINEAR_CROSS_0 (x := (0 : V3)) (y := (rhoNode1 FF)^[i] v)
      (z := (rhoNode1 FF)^[i + 1] v), sub_zero, sub_zero, ← hXY, cross_self]
    rfl
  have hXP : (rhoNode1 FF)^[i] v ∈ P := _hUsub (hUmem i (by omega))
  have hYP : (rhoNode1 FF)^[i + 1] v ∈ P := _hUsub (hUmem (i + 1) (by omega))
  have hZP : (rhoNode1 FF)^[i + 2] v ∈ P := _hUsub (hUmem (i + 2) (by omega))
  have hPspan : (affineSpan ℝ ({0, (rhoNode1 FF)^[i] v,
      (rhoNode1 FF)^[i + 1] v} : Set V3)) = P :=
    THREE_NOT_COLL_DETER_PLANE hP2
      (by
        intro q hq
        rcases Set.mem_insert_iff.mp hq with rfl | hq
        · exact _h0
        · rcases Set.mem_insert_iff.mp hq with rfl | rfl
          · exact hXP
          · exact hYP)
      hncXY
  have hZaff : (rhoNode1 FF)^[i + 2] v ∈
      ((affineSpan ℝ ({0, (rhoNode1 FF)^[i] v, (rhoNode1 FF)^[i + 1] v} : Set V3) : Set V3)) := by
    rw [hPspan]
    exact hZP
  have hZspan : (rhoNode1 FF)^[i + 2] v ∈
      (Submodule.span ℝ ({(rhoNode1 FF)^[i] v, (rhoNode1 FF)^[i + 1] v} : Set V3)) :=
    w5cB6_mem_span_of_affSpan0 hZaff
  obtain ⟨a, b, hZab⟩ := Submodule.mem_span_pair.mp hZspan
  obtain ⟨k, hk, hkc⟩ :=
    ITER_CROSS_SAME_DIRECTION_p37 _hlf _hv _hU _hP _h0 _hUsub (i + 1) i
      (by omega) (by omega)
  rw [← hZab] at hkc
  -- cross 线性展开（B7 轮心跳热点；B9 以具名 `simp only` 集收口，见 DELIVERY-b9 §3）
  have hlin : cross3_p37 ((rhoNode1 FF)^[i + 1] v)
      (a • (rhoNode1 FF)^[i] v + b • (rhoNode1 FF)^[i + 1] v) =
      a • cross3_p37 ((rhoNode1 FF)^[i + 1] v) ((rhoNode1 FF)^[i] v) := by
    rw [cross3_p37, cross3_p37]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.toLp_smul, map_add, map_smul,
      cross_self, smul_zero, add_zero]
  rw [hlin] at hkc
  have hcXY : cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) ≠ 0 := by
    intro hcz
    refine hncXY ?_
    rw [COLLINEAR_CROSS_0 (x := (0 : V3)) (y := (rhoNode1 FF)^[i] v)
      (z := (rhoNode1 FF)^[i + 1] v), sub_zero, sub_zero]
    exact hcz
  have hak : a = -k := by
    have h1 : a • cross3_p37 ((rhoNode1 FF)^[i + 1] v) ((rhoNode1 FF)^[i] v) =
        k • cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) := hkc
    have hsym : cross3_p37 ((rhoNode1 FF)^[i + 1] v) ((rhoNode1 FF)^[i] v) =
        -(cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v)) := by
      rw [cross3_p37, cross3_p37, ← WithLp.toLp_neg, ← cross_anticomm]
    rw [hsym, smul_neg, ← neg_smul] at h1
    have h2' : ((-a) - k) • cross3_p37 ((rhoNode1 FF)^[i] v)
        ((rhoNode1 FF)^[i + 1] v) = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 := (smul_eq_zero.mp h2').resolve_right hcXY
    linarith
  rw [hak] at hZab
  have h0Y : (0 : V3) ≠ (rhoNode1 FF)^[i + 1] v :=
    Ne.symm (FAN_IMP_V_DIFF hfan ((rhoNode1 FF)^[i + 1] v) hmemVi1)
  refine w5cB_affLt_2_1_mpr (u := 0) (v := (rhoNode1 FF)^[i + 1] v)
    (a := (rhoNode1 FF)^[i] v) (z := (rhoNode1 FF)^[i + 2] v)
    (t1 := 1 - b + k) (t2 := b) (t3 := -k) h0Y (Ne.symm hXYne) h0X
    (by linarith) (by ring) ?_
  rw [smul_zero, zero_add, ← hZab]
  module

/-- HOL `AZIM_PI_ITER_LOCAL_FAN` (lunar_deform.hl:3589)。本 port：
`ITER_IN_AFF_GT_2_1_p37` 的 `affLt` 成员 + CHARACTER3 两非共线前提
（`w := ρ^[i+1] v`）→ B2 闭件 `w5cB_azim_eq_pi_of_affLt` 一直消费。 -/
theorem AZIM_PI_ITER_LOCAL_FAN_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
    (_hlf : LocalFan V E FF) (_hv : v ∈ V)
    (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
    (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P) :
    ∀ i < l - 1,
      azim 0 ((rhoNode1 FF)^[i + 1] v) ((rhoNode1 FF)^[i] v)
        ((rhoNode1 FF)^[i + 2] v) = Real.pi := by
  classical
  have h2 := w5cB5_to_localFan_p2 _hlf
  intro i hi
  have hprev := ITER_IN_AFF_GT_2_1_p37 _hlf _hv _hU _hP _h0 _hUsub i (by omega)
  have hncA : ¬Collinear ℝ ({0, (rhoNode1 FF)^[i + 1] v,
      (rhoNode1 FF)^[i] v} : Set V3) := by
    have hc : ¬Collinear ℝ ({0, (rhoNode1 FF)^[i] v,
        (rhoNode1 FF)^[i + 1] v} : Set V3) := w5cB7_char3 h2 _hv i
    rwa [show ({0, (rhoNode1 FF)^[i] v, (rhoNode1 FF)^[i + 1] v} : Set V3) =
        ({0, (rhoNode1 FF)^[i + 1] v, (rhoNode1 FF)^[i] v} : Set V3) from by
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto] at hc
  have hncZ : ¬Collinear ℝ ({0, (rhoNode1 FF)^[i + 1] v,
      (rhoNode1 FF)^[i + 2] v} : Set V3) := w5cB7_char3 h2 _hv (i + 1)
  exact w5cB_azim_eq_pi_of_affLt (u := 0) (v := (rhoNode1 FF)^[i + 1] v)
    (a := (rhoNode1 FF)^[i] v) (z := (rhoNode1 FF)^[i + 2] v) hncA hncZ hprev

/-- HOL `LOCAL_CONVEX_NOT_COLLINEAR` (lunar_deform.hl:3616).
PROVED (la37-g5-w1): `LUNAR_IMP_IN_TWO_HAFLS_PLANE_p37` + the two
successor/predecessor non-collinearities
(`LOCAL_FAN_CHARACTER_OF_RHO_NODE2`, `LOFA_IMP_NOT_COLL_IVS`) through
`PlanarityAngle.aff_gt_imp_not_collinear`. -/
theorem LOCAL_CONVEX_NOT_COLLINEAR_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v w : V3}
    (_h : ConvexLocalFan V E FF) (_hl : Lunar v w V E) :
    ∀ u ∈ V, u ≠ v → u ≠ w → ¬Collinear ℝ ({0, v, u} : Set V3) := by
  have hlf : localFan_p2 V E FF := (CVLF_LF_F (la37g5_clf2 _h)).1
  have hvV : v ∈ V := _hl.2.1 (by simp)
  have hrho : ¬ Collinear3 (0 : V3) v (rhoNode1 FF v) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf hvV
  have hivs : ¬ Collinear3 (0 : V3) v (ivsRhoNode1 FF v) :=
    LOFA_IMP_NOT_COLL_IVS hlf hvV
  intro u hu hne1 hne2
  rcases LUNAR_IMP_IN_TWO_HAFLS_PLANE_p37 _h _hl u hu hne1 hne2 with hum | hum
  · exact aff_gt_imp_not_collinear (x := (0 : V3)) (v := v)
      (u := rhoNode1 FF v) (w := u) hrho hum
  · exact aff_gt_imp_not_collinear (x := (0 : V3)) (v := v)
      (u := ivsRhoNode1 FF v) (w := u) hivs hum

/-- HOL `LOCAL_FAN_RHO_NODE_PROS2` (lunar_deform.hl:3633).  NEEDS:
`Local_lemmas.LOCAL_FAN_RHO_NODE_PROS` (fan substance). -/
theorem LOCAL_FAN_RHO_NODE_PROS2_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (_h : LocalFan V E FF) :
    ∀ x ∈ V, (x, rhoNode1 FF x) ∈ FF := by
  exact (LOCAL_FAN_RHO_NODE_PROS2 (w5cB5_to_localFan_p2 _h)).2

/-- HOL `MHAEYJN_CONVEX_LOCAL_FAN` (lunar_deform.hl:3644): the
`ConvexLocalFan` conclusion of MHAEYJN without the lunar conjunct.
GIANT (sorry): combines `SUB_LUNAR_DEFORM_LEMMA_p37` with the
`XRECQNS_UPDATE` fan-transfer kit (`Wrgcvdr_cizmrrh.LOCAL_FAN_IMP_FAN`,
`UNIONS_SUBSET`, epsilon min). -/
theorem MHAEYJN_CONVEX_LOCAL_FAN_p37 {a b : ℝ} {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → ℝ → V3} {v w u : V3}
    (_hcf : ConvexLocalFan V E FF) (_hl : Lunar v w V E) (_hd : Deformation f V a b)
    (_hang : interiorAngle1 0 FF v < Real.pi) (_hu : u ∈ V) (_hv : u ≠ v)
    (_hw : u ≠ w)
    (_hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (_haff : ∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      ConvexLocalFan ((fun z => f z t) '' V)
        ((fun s => (fun z => f z t) '' s) '' E)
        ((fun p => (f p.1 t, f p.2 t)) '' FF) := by
  sorry

/-- The registry `MHAEYJN_concl` (appendix.hl:25) as a `Prop`: the
`real_interval (a,b)` ↔ `Icc a b` rendering, verbatim `_p37` copy.
NEEDS: merge with the NUXCOEA/IMJXPHR-lane twin `MHAEYJN_prop_p34`
(LocalAuto34; its olean is not built in this checkout). -/
def MHAEYJN_prop_p37 : Prop :=
  ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3) (v w u : V3),
    ConvexLocalFan V E FF →
    Lunar v w V E →
    Deformation f V a b →
    interiorAngle1 0 FF v < Real.pi →
    u ∈ V → u ≠ v → u ≠ w →
    (∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') →
    (∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      ConvexLocalFan ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
      Lunar v w ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)

/-- HOL `MHAEYJN` (lunar_deform.hl:4985): the lunar deformation registry
conclusion.  GIANT (sorry): needs `MHAEYJN_CONVEX_LOCAL_FAN_p37` +
`SUB_LUNAR_DEFORM_LEMMA_p37` (the `if e < e' then e else e'` min of the two
windows; the Lunar conjunct comes from `SUB_LUNAR_DEFORM_LEMMA_p37`). -/
theorem MHAEYJN_p37 : MHAEYJN_prop_p37 := by
  sorry


/-! ## w5cB7 kit (B7 波): G4 接口的正确形 + p2 桥 — 见 DELIVERY-b7 §1 -/

/-- HOL `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS` (Nkezbfc.hl:214)。本 port 中
`interiorAngle1 x FF v` 的定义体即 `azim x v (rhoNode1 FF v) (ivsRhoNode1 FF v)`
（localization.hl:119-120 直译：`ivs_rho_node1` 的 `@a`-选择项与定义同项），
故本件为定义相等（NKEZBFC 的重型 HOL 证法在本编码下平凡）。 -/
theorem CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (_h : ConvexLocalFan V E FF) :
    ∀ v ∈ V, interiorAngle1 0 FF v = azim 0 v (rhoNode1 FF v) (ivsRhoNode1 FF v) :=
  fun _ _ => rfl

/-- B7 助件：registry `Lunar` → LA2 `lunar_p2` 桥。两定义逐字同构
（`circular_p2` ≡ `Circular`，LA2:278 vs LA1:125），定义相等。 -/
private theorem w5cB7_lunar_p2_of_lunar {v w : V3} {V : Set V3} {E : Set (Set V3)}
    (hl : Lunar v w V E) : lunar_p2 v w V E := hl

/-! **B7 接口诊断（B9 已按此落地，见下）**：tower-b4 条件形
`w5cB4_SUB_LUNAR_DF_cond` 的 `hdv/hdw` 槽取半平面锥形
`affGt {0,v} {ρv} ∩ affLt {0} {u'} = ∅`（对所有像点 `u'` 量词化），该形
不可满足：对面半 run 像点 `x` 的反向射线 `-c•x` 落入 `affGt {0,v} {ρv}`
的开半平面（二维坐标反例：`x = α•v + β•ρv, β < 0` ⇒ `-c•x = (-cα)•v +
(-cβ)•ρv`，`-cβ > 0`）。正确接口为 HOL 逐字 wedge 形
`∀ s ∈ image E, ∀ u' ∈ image V, aff_gt {0} s ∩ aff_lt {0} {u'} = ∅`
（lunar_deform.hl:1533-1537）。**B9 落地**：wedge 条件件
`w5cB9_SUB_LUNAR_DF_cond`（`w5cB3_lunar_window` 一行消费）+ 非 `u`-边∧
钉住顶点的直释部分 `w5cB9_hsep_pinned`。含 `u` 边与 `u'=u_t` 两情形仍需
段 7b/8 两半分解（`LUNAR_IMP_IN_TWO_HAFLS_PLANE_p37` / `HKIRPEP_ALT_p37`，
G5 边界，未消费）。 **B9 iter 链**：`LOCAL_FAN_CHARACTER_OF_RHO_NODE3` 由
`w5cB7_char3` 提供；`ITER_IN_AFF_GT_2_1_p37` 与 `AZIM_PI_ITER_LOCAL_FAN_p37`
已全闭（标准三，见 DELIVERY-b9.md）。 -/

/-- B9 段 8 部分收口：非 `u`-边情形 + 钉住顶点（`u' ≠ u`）。边像在钉住下
即原边，`¬Circular`（`Lunar` 首合取）直释 wedge 不交。含 `u` 边与 `u' = u_t`
两情形需段 7b/8 的两半分解（G5 边界物料），本件不覆盖。 -/
private theorem w5cB9_hsep_pinned
    {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} {v w : V3}
    (hl : Lunar v w V E) (hcf : ConvexLocalFan V E FF)
    {x : Set V3} (hxE : x ∈ E) {u' : V3} (hu'V : u' ∈ V) :
    affGt ({0} : Set V3) x ∩ affLt ({0} : Set V3) {u'} = ∅ := by
  obtain ⟨a, b, hab, hx⟩ := EDGE_FORM_IN_LOCAL_FAN_p37 hcf.1 hxE
  by_contra hne
  rw [← hx] at hne
  exact hl.1 ⟨a, b, u', hx ▸ hxE, hu'V, hne⟩

/-- B9 钉住边的像复原：`u ∉ x` 时边像 = 原边（逐点用 `hpin`）。 -/
private theorem w5cB9_image_eq_of_notMem_u
    {a b : ℝ} {V : Set V3} {E : Set (Set V3)} {f : V3 → ℝ → V3} {u : V3} {t : ℝ}
    (hE : ∀ x ∈ E, x ⊆ V) {x : Set V3} (hxE : x ∈ E) (hu : u ∉ x)
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') (ht : t ∈ Icc a b) :
    (fun z => f z t) '' x = x := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyV := hE x hxE hy
    have hyu : y ≠ u := fun he => hu (he ▸ hy)
    show f y t ∈ x
    rw [hpin y hyV (Ne.symm hyu) t ht]
    exact hy
  · intro hz
    refine ⟨z, hz, ?_⟩
    have hzV := hE x hxE hz
    have hzu : z ≠ u := fun he => hu (he ▸ hz)
    exact hpin z hzV (Ne.symm hzu) t ht

/-- B9 段 8 部分收口（像形）：`u ∉ x` 且 `u'' ≠ u` 时 wedge 不交成立。
剩下 `u' = u_t` 与含 `u` 边两情形需 G5 边界的两半分解物料。 -/
private theorem w5cB9_hsep_pinned_image
    {a b : ℝ} {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {f : V3 → ℝ → V3} {u v w : V3} {t : ℝ}
    (hl : Lunar v w V E) (hcf : ConvexLocalFan V E FF)
    (hE : ∀ x ∈ E, x ⊆ V) {x : Set V3} (hxE : x ∈ E) (hu : u ∉ x)
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (ht : t ∈ Icc a b) {u'' : V3} (hu''V : u'' ∈ V) (hu''u : u'' ≠ u) :
    affGt ({0} : Set V3) ((fun z => f z t) '' x) ∩
      affLt ({0} : Set V3) {f u'' t} = ∅ := by
  rw [w5cB9_image_eq_of_notMem_u (V := V) (E := E) (f := f) (u := u)
    (a := a) (b := b) hE hxE hu hpin ht, hpin u'' hu''V (Ne.symm hu''u) t ht]
  exact w5cB9_hsep_pinned hl hcf hxE hu''V

/-- **G4 wedge 接口（B9 落地）**：`SUB_LUNAR_DEFORM_LEMMA_p37` 的显式条件形。
签名与目标逐字一致，另挂窗口半径 `d` 与 HOL 逐字 wedge 前提
（lunar_deform.hl:1533-1537：每条边像锥与每个顶点像的 `affLt {0}` 不交）。
由分段 6 `w5cB3_lunar_window` 一行收口；取代 B4 的 `hdv/hdw` 半锥槽
（B7 已裁定不可满足）。 -/
private theorem w5cB9_SUB_LUNAR_DF_cond
    {a b : ℝ} {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {f : V3 → ℝ → V3} {u v w : V3}
    (_hV : V.Finite) (_hcf : ConvexLocalFan V E FF) (_hl : Lunar v w V E)
    (_hE : ∀ x ∈ E, x ⊆ V) (_hu0 : f u 0 = u) (_hcu : ContinuousAt (f u) 0)
    (_hang : interiorAngle1 0 FF v < Real.pi) (_ha : a < 0) (_hb : 0 < b)
    (_hu : u ∈ V) (_huv : u ≠ v) (_huw : u ≠ w)
    (_hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (_haff : ∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3))
    (d : ℝ) (hd : 0 < d)
    (hsep : ∀ t : ℝ, -d < t → t < d → t ∈ Icc a b →
      ∀ s : Set V3, s ∈ (fun s => (fun z => f z t) '' s) '' E →
        ∀ u' : V3, u' ∈ (fun z => f z t) '' V →
        affGt ({0} : Set V3) s ∩ affLt ({0} : Set V3) {u'} = ∅) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      Lunar v w ((fun z => f z t) '' V) ((fun s => (fun z => f z t) '' s) '' E) :=
  w5cB3_lunar_window (a := a) (b := b) (V := V) (E := E) (f := f)
    (u := u) (v := v) (w := w) (e := d) _hl _huv _huw _hpin _ha _hb hd hsep

end Kepler.Text
