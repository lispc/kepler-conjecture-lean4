/-
CircularSolKit — packaging of HOL `CIRCULAR_SOL_EQ_2PI` (GBYCPXS.hl:592):
on a circular convex local fan the total solid angle is `2 * pi`.

PUBLIC FACE (LA1 encoding — verbatim the consumer shapes at
LocalAuto26:1281 and the planned LocalAuto23 CASE_5/6 consumption):

* `circularSolEq2Pi_cs {V E FF} (hclf : ConvexLocalFan V E FF)
  (hc : Circular V E) : solLocal E FF = 2 * Real.pi` — verbatim the
  statement of `CIRCULAR_SOL_EQ_2PI_p26` (LocalAuto26:1281).
* `circularAzimInFanPi_cs` — the per-dart form of the same fact,
  `∀ d ∈ FF, azimInFan d E = Real.pi`: the shape LocalAuto23's
  `tauFun` final computation consumes (JKQEWGV2_CASE_5/6_p23, W3 wave).

ENGINE (zero new mathematics): `KCHMAMG` (LocalAuto5:5833, public, real:
`convexLocalFan_p2 → circular_p2 → every interior angle is pi` + plane +
rho-orbit slots), the AzimBridge local-fan p1→p2 bridge
`localFan_p2.of_LocalFan_noIso` (AzimBridge:1251; its no-isolated premise
is discharged by the LA1 `LocalFan` 2-regularity conjunct through
`hno_of_no_isolated`, AzimBridge:1151), and the p1↔p3 point bridge
`azimInFan_eq_azimInFan_p3` (AzimBridge:473).  The only packaging proof
is `kcs_clf2` (transport LA1 `ConvexLocalFan` → LA2 `convexLocalFan_p2`),
carried verbatim from the verified probe of lane scsgeneric-recon3
(`probes/probe2.lean`, 89 lines, RC=0, axioms standard triple).  The
probe's four defeq spot-checks (`azimInFan_p2 = azimInFan_p3`,
`wedgeInFanGe_p2 = wedgeInFanGe_p3`, `Circular ↔ circular_p2` coerced,
`rhoNode1_p2 = rhoNode1`) are recorded in that lane's Evidence and are
subsumed here by the compiled `rfl`/coercion steps of `kcs_clf2` and
`circularAzimInFanPi_cs`.

IMPORT SAFETY (python BFS over `^import Kepler.*` edges, lane
scsgeneric-recon3 Evidence §3): the transitive Kepler closure of
{AzimBridge, LocalAuto5, LocalAuto9} is 63 modules and is disjoint from
{LocalAuto18, LocalAuto23, LocalAuto24, LocalAuto25, LocalAuto26,
LocalAuto27, LocalAuto35, LocalAuto36, LocalAuto37, ClosedSyKit}; the
kit may therefore sit upstream of LA18/LA23/LA26 and of every
LA23-importer with no new cycle (re-run in this lane's Evidence.md).
-/
import Kepler.Text.AzimBridge
import Kepler.Text.LocalAuto5
import Kepler.Text.LocalAuto9

namespace Kepler.Text

open Kepler.Geom Kepler.Text Kepler.Text.Fan Set

/-- 2-regularity ⇒ every vertex lies on some edge.  Twin of the
`w1hedge` step already consumed in LocalAuto25; discharges the `hno`
premise of `localFan_p2.of_LocalFan_noIso`. -/
private theorem kcs_hedge {V : Set V3} {E : Set (Set V3)}
    (h2reg : ∀ u ∈ V, (ee u E).ncard = 2) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  intro v hv
  have h2 : (ee v E).ncard = 2 := h2reg v hv
  have hne : (ee v E) ≠ ∅ := by
    intro hE
    rw [hE, Set.ncard_empty] at h2
    omega
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact ⟨w, hw⟩

/-- `localFan_p2 ⇒ FF ⊆ dart1OfFan` (pattern of LocalAuto9:1422-1428;
the `dartsOfHyp` side collapses to darts via `hno_p2_of_no_isolated`). -/
private theorem kcs_ffSubDart {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : localFan_p2 V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    FF ⊆ dart1OfFan V E := by
  obtain ⟨H, hd, -, -, -, -, hface, -⟩ := hlf
  obtain ⟨z, hzd, hFF⟩ := hface
  intro d hdF
  have hsub := H.face_subset_darts hzd (hFF ▸ hdF)
  rw [hd] at hsub
  exact (hno_p2_of_no_isolated hedge) ▸ hsub

/-- `localFan_p2 ⇒ FF.Finite`: every dart is `(FST x, rhoNode1 FF x)`
(`LOCAL_FAN_RHO_NODE_PROS.2`) with `FST x ∈ V` (`LOCAL_FAN_IMP_IN_V`),
so `FF` is an image of the finite `V` (`LOCAL_FAN_FINITE_V`). -/
private theorem kcs_ffFinite {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : localFan_p2 V E FF) : FF.Finite := by
  have h1 := LOCAL_FAN_RHO_NODE_PROS hlf
  have hV := LOCAL_FAN_FINITE_V hlf
  have hsub : FF ⊆ (fun v : V3 => (v, rhoNode1_p2 FF v)) '' V := by
    intro d hd
    have hinV := LOCAL_FAN_IMP_IN_V hlf hd hd
    rw [h1.2 d hd]
    exact ⟨d.1, hinV.1, rfl⟩
  exact (hV.image fun v : V3 => (v, rhoNode1_p2 FF v)).subset hsub

/-- The one packaging proof of this module: transport the LA1
`ConvexLocalFan` hypothesis to the LA2 `convexLocalFan_p2` encoding
(azim/wedge slots via the AzimBridge p1↔p3 point bridges on fan darts). -/
private theorem kcs_clf2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : ConvexLocalFan V E FF) : convexLocalFan_p2 V E FF := by
  obtain ⟨hlf, hcvx⟩ := h
  have hcopy := hlf
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := hcopy
  have hlf2 := localFan_p2.of_LocalFan_noIso hlf (kcs_hedge h2reg)
  have hsub := kcs_ffSubDart hlf2 (kcs_hedge h2reg)
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

/-- Per-dart face of the circular-fan engine: on a circular convex local
fan every dart's in-fan azimuth is `pi` (the inner step of HOL
`CIRCULAR_SOL_EQ_2PI`, via `KCHMAMG` + `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_p9`
+ the `LOCAL_FAN_RHO_NODE_PROS` dart rendering).  This is the shape
LocalAuto23's `tauFun` final computation consumes (W3 wave). -/
theorem circularAzimInFanPi_cs {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hclf : ConvexLocalFan V E FF) (hc : Circular V E) :
    ∀ d ∈ FF, azimInFan d E = Real.pi := by
  have h1 := kcs_clf2 hclf
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := hclf.1
  have hsub := kcs_ffSubDart h1.1 (kcs_hedge h2reg)
  have hhang := (KCHMAMG h1 hc).1
  have hRNP := LOCAL_FAN_RHO_NODE_PROS h1.1
  intro d hd
  have hdV : d.1 ∈ V := (LOCAL_FAN_IMP_IN_V h1.1 hd hd).1
  have hdeq : d = (d.1, rhoNode1_p2 FF d.1) := hRNP.2 d hd
  have hθ := CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_p9 h1 d.1 hdV
  have hb : azimInFan d E = azimInFan_p2 d E :=
    (azimInFan_eq_azimInFan_p3 hfan (hsub hd)).trans rfl
  have hbd : azimInFan_p2 (d.1, rhoNode1_p2 FF d.1) E = azimInFan_p2 d E := by
    rw [hdeq]
  rw [hb, ← hbd, ← hθ, hhang d.1 hdV]

/-- HOL `CIRCULAR_SOL_EQ_2PI` (GBYCPXS.hl:592): a circular convex local
fan carries total solid angle `2 * pi`.  Verbatim the statement of
`CIRCULAR_SOL_EQ_2PI_p26` (LocalAuto26:1281), discharged by the per-dart
`circularAzimInFanPi_cs` zero-sum over the finite dart set. -/
theorem circularSolEq2Pi_cs {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hclf : ConvexLocalFan V E FF) (hc : Circular V E) : solLocal E FF = 2 * Real.pi := by
  have h1 := kcs_clf2 hclf
  have hfinFF := kcs_ffFinite h1.1
  unfold solLocal
  rw [setSum, dif_pos hfinFF]
  have hz : ∑ d ∈ hfinFF.toFinset, (azimInFan d E - Real.pi) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hmem : d ∈ FF := hfinFF.mem_toFinset.mp hd
    rw [circularAzimInFanPi_cs hclf hc d hmem]
    ring
  rw [hz, add_zero]
