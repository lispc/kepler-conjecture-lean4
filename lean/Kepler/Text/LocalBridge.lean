/-
Kepler.Text.LocalBridge — the W7 capstone bridge: local chapter ⟹ packing side.

Connects the local chapter's capstone contract to the packing-side interface:

  * terminal.hl      → LocalAuto38 (`BBs_terminal` case bank + the §F
    `OWZLKVY*`/`EAR_*` y-box family under the `main_nonlinear_terminal_v11`
    seal; LocalAuto38.olean is ABSENT from this checkout, so the bank is
    carried as the hypothesis `hbank` over a parameter `terminalCases` that
    instantiates to `scsTerminalV116_p38`, LocalAuto38:166),
  * lunar_deform.hl  → LocalAuto37 (`MHAEYJN_prop_p37`/`MHAEYJN_p37`,
    LocalAuto37:805-826; verbatim twin `MHAEYJN_prop_bridge` below),
  * IMJXPHR.hl       → LocalAuto34 (`IMJXPHR_concl_p34`, LocalAuto34:273-287,
    aligned with LocalAuto1 `IMJXPHRv2_concl`:976; verbatim twin
    `IMJXPHR_concl_bridge` below; its antecedents are `ZLZTHIC_concl`
    (LocalAuto1:881, exact) and `MHAEYJN` via `IMJXPHR_p34`, LocalAuto34:2433),

to the packing-side interface `localAnnulusInequalityP22`
(PackingAuto22:226-228, `:= True` placeholder), which is the
counting_spheres-lane rendering of HOL `local_annulus_inequality`
(pack_defs.hl:202-203: `sum V (\v. lmfun (hl [vec 0;v])) <= &12`, ported
verbatim as `localAnnulusInequality`, PackingAuto2:535-537; cf.
LocalAnchors §3 — the P22 stub should be replaced there by the ported
definition, after which `localAnnulusInequalityP22_of_ported` below becomes
`id`).

No LocalAuto34/37/38 import: their oleans are not built in this checkout.
Their statement shapes are carried as verbatim twins (merge note: delete the
twins in favour of the built lane constants). `Kepler.Text.LocalAnchors` is
NOT imported either (its `scsBasicV39` twin, LocalAnchors:65, hard-clashes
with LocalAuto1's on import, cf. LocalAuto38 header:52-56); the anchor shapes
`MainNonlinearTerminalV11` (LocalAnchors:49) and `cstabAnchor`
(LocalAnchors:34) are carried as the verbatim twins
`mainNonlinearTerminalV11Bridge`/`cstabAnchorBridge` below.
-/

import Kepler.Text.PackingAuto22
import Kepler.Text.LocalAuto1
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## 0. Verbatim twins of the LocalAuto34/37 capstone statements and of the
LocalAnchors shapes -/

/-- Verbatim twin of `cstabAnchor` (LocalAnchors:31-34): HOL `cstab = #3.01`
(appendix.hl:78). The appendix lane owns the canonical constant; this bridge
copy exists only so the anchor shapes below need no LocalAnchors import
(hard `scsBasicV39` import clash with LocalAuto1). -/
def cstabAnchorBridge : ℝ := 3.01

/-- Verbatim twin of `MainNonlinearTerminalV11` (LocalAnchors:36-54): the
visible box shape of HOL `main_nonlinear_terminal_v11` (terminal.hl:24-44):
`2 ≤ y1..y3 ≤ 2*h0`, `cstab ≤ y4 ≤ 3.915`, `y5 = y6 = 2` (terminal subcase:
`y1 = 2*h0`), guarding inequalities of the family `200 ≤ delta_y → 0 ≤ taum`. -/
def mainNonlinearTerminalV11Bridge (y : Fin 6 → ℝ) : Prop :=
  2 ≤ y 0 ∧ y 0 ≤ 2 * h0 ∧
    2 ≤ y 1 ∧ y 1 ≤ 2 * h0 ∧
    2 ≤ y 2 ∧ y 2 ≤ 2 * h0 ∧
    cstabAnchorBridge ≤ y 3 ∧ y 3 ≤ 3.915 ∧
    y 4 = 2 ∧ y 5 = 2

/-- Verbatim twin of LocalAuto34 `MHAEYJN_prop_p34` (LocalAuto34:154-169) =
LocalAuto37 `MHAEYJN_prop_p37` (LocalAuto37:805-820) — the two source defs
are term-identical, so the twins are interchangeably defeq. HOL registry
`MHAEYJN_concl` (appendix.hl:25; lunar_deform.hl:4985): a lunar convex local
fan survives the pinned deformation, with the Lunar conjunct. -/
def MHAEYJN_prop_bridge : Prop :=
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

/-- Verbatim twin of LocalAuto34 `IMJXPHR_concl_p34` (LocalAuto34:273-287;
HOL `IMJXPHR_concl`, IMJXPHR.hl:9682, aligned with LocalAuto1
`IMJXPHRv2_concl`:976): the azim = π ear-tightening
`s.a l (l±1) = dist (w l) (w (l±1))` on the minimal-fan vertex `w l`. -/
def IMJXPHR_concl_bridge : Prop :=
  ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
    s.k = k → isScsV39 s → w ∈ MMsV39 s →
    azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
    3 < k →
    ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3) →
    w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3) →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) →
    ¬(2 = ‖w l‖) →
    (∀ i, scsDiag k l i → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬s.J l i) →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    s.a l (l + 1) = dist (w l) (w (l + 1)) ∧
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1)))

/-! ## 1. Exact glue: the P22 interface and the anchor box shape -/

/-- Exact paste between the packed inequality and the P22 interface.
Today `localAnnulusInequalityP22` is the `:= True` stub (PackingAuto22:228),
so this is `trivial`; once the stub is replaced by `localAnnulusInequality`
(PackingAuto2:536-537) per the LocalAnchors §3 merge note, the same statement
is `id` — the hypothesis IS the conclusion. -/
theorem localAnnulusInequalityP22_of_ported {V : Set V3}
    (_h : localAnnulusInequality V) : localAnnulusInequalityP22 V := by
  trivial

/-- Exact: the visible box shape of the external anchor
(`mainNonlinearTerminalV11Bridge`, verbatim twin of `MainNonlinearTerminalV11`,
LocalAnchors:49-54, HOL terminal.hl:24-44) is literally the box family
consumed by the LocalAuto38 §F terminal bank (`OWZLKVY0` LocalAuto38:1048,
`OWZLKVY2` :1096, `EAR_DELTA_X4` :1057, ...; there the duplicated conjunct
`2 ≤ y1` and the `cstab` constant appear, the latter via the `cstabAnchor`
bridge copy). -/
theorem mainTerminalAnchorBox (y : Fin 6 → ℝ) (h : mainNonlinearTerminalV11Bridge y) :
    2 ≤ y 0 ∧ y 0 ≤ 2 * h0 ∧ 2 ≤ y 1 ∧ y 1 ≤ 2 * h0 ∧ 2 ≤ y 2 ∧ y 2 ≤ 2 * h0 ∧
      cstabAnchorBridge ≤ y 3 ∧ y 3 ≤ 3.915 ∧ y 4 = 2 ∧ y 5 = 2 :=
  h

/-! ## 2. The giant core (sorry) -/

/-- The giant core of the capstone contract: the terminal case bank (sealed by
the anchor) + the lunar deformation registry + the IMJXPHR master arrow yield
HOL `local_annulus_inequality` (pack_defs.hl:202-203, `localAnnulusInequality`,
PackingAuto2:536). GIANT (sorry). -/
theorem terminal_bank_lunar_imjxphr_imp_localAnnulusInequality
    (V : Set V3) (hP : Packing V) (hV : V ⊆ ballAnnulus)
    (terminalCases : List ScsV39)
    (hbank : ∀ s ∈ terminalCases, ∀ vv : ℕ → V3, BBsV39 s vv → 0 ≤ taustarV39 s vv)
    (hterm : main_nonlinear_terminal_v11)
    (hlunar : MHAEYJN_prop_bridge)
    (himj : IMJXPHR_concl_bridge) :
    localAnnulusInequality V := by
  -- REMAINING: the taustar/lunar/IMJXPHR capstones ⇒ lmfun-sum transfer is
  -- unported. Missing local-chapter lemmas (names/lines as in-tree):
  -- · terminal lane (LocalAuto38): `scsTerminalV116_p38` (EXTERNAL-ANCHOR
  --   stub, :166), `BBs_terminal` body (:250), and the LP-backed §F bank
  --   `OWZLKVY0` (:1048), `EAR_DELTA_X4` (:1057), `EAR_DIH1_DELTA_0` (:1068),
  --   `OWZLKVY3` (:1077), `OWZLKVY1` (:1087), `OWZLKVY2` (:1096),
  --   `empty_3T2` (:1115), `OWZLKVY4` (:1162),
  --   `quad_4680581274_delta_issue` (:1279), `quad_4680581274_a` (:1296),
  --   `quad_4680581274_y` (:1314), `taud_x_taum_x` (:1332),
  --   `quad_4680581274_derived` (:1342) — each DISCHARGES:
  --   main_nonlinear_terminal_v11 + LP.
  -- · lunar lane (LocalAuto37): `SUB_LUNAR_DEFORM_LEMMA_p37` (:344),
  --   `MHAEYJN_CONVEX_LOCAL_FAN_p37` (:788), `MHAEYJN_p37` (:826).
  -- · IMJXPHR lane (LocalAuto34): `IMJXPHR_p34` (:2433; antecedents =
  --   `ZLZTHIC_concl` LocalAuto1:881, exact, and `MHAEYJN_prop_p34`, defeq to
  --   `MHAEYJN_prop_bridge` above), `TAUSTAR_V3_DEFOR_TWO_CASES_p34` (:2425),
  --   `INTERIOR_ANGLE_SAME_V3_DEFOR1_TWO_CASES_p34` (:2401).
  -- · bridge-owned: the `taustarV39`-nonnegativity ⇒ `lmfun (hl [0, ·])`-sum
  --   transfer (HOL lanes Sum_gammax_lmfun_estimate / Kizhltl, opened at
  --   RDWKARC.hl:55-57; counting_spheres.hl:6176-7065).
  -- · packing-side GIANTs around the interface (PackingAuto22): `XULJEPR`
  --   (:1764), `DLWCHEM` (:1757), `XULJEPR_VECTOR_sum` (:1733),
  --   `DLWCHEM_VECTOR_sum` (:1720), `SOL_NN` (:1745), `FACET_SOL_NN` (:1751);
  --   stubs `packIneqDefAP22` (:232), `localAnnulusInequalityP22` (:228),
  --   `weaklySaturatedP22` (:224).
  sorry

/-! ## 3. The bridge -/

/-- THE BRIDGE (W7 capstone contract): the local chapter's three capstones —
the terminal case bank + anchor (LocalAuto38), the lunar deformation registry
(LocalAuto37), the IMJXPHR master arrow (LocalAuto34) — yield the packing-side
interface `localAnnulusInequalityP22` (PackingAuto22:226-228), i.e. HOL
`local_annulus_inequality` (pack_defs.hl:202-203) for a packing `V` in the
ball annulus (pack_defs.hl:199-200), in the interface context of the
counting_spheres consumers (`XULJEPR` counting_spheres.hl:7191 /
PackingAuto22:1764; `DLWCHEM` counting_spheres.hl:7063 / PackingAuto22:1757).

Hypothesis → HOL origin map:
* `hP`, `hV` — the packing-side interface context: `packing V` and
  `V SUBSET ball_annulus` (pack_defs.hl:199-200), as in the `XULJEPR`/`DLWCHEM`
  signatures.
* `terminalCases`, `hbank` — HOL `BBs_terminal` (terminal.hl:184; LocalAuto38:247):
  `!s. MEM s scs_terminal_v116 ==> !vv. BBs_v39 s vv ==> &0 <= taustar_v39 s vv`;
  `terminalCases` instantiates to `scsTerminalV116_p38` (LocalAuto38:166;
  parameter here because LocalAuto38.olean is absent from this checkout).
* `hterm` — HOL `main_nonlinear_terminal_v11` (terminal.hl:24-44; LocalAuto1:796
  registry Prop; visible box shape `MainNonlinearTerminalV11`, LocalAnchors:49,
  twin `mainNonlinearTerminalV11Bridge` above, exactly extracted by
  `mainTerminalAnchorBox`): the closed `Main_estimate`
  conjunction powering the LocalAuto38 §F y-box case bank.
* `hlunar` — HOL `MHAEYJN` (appendix.hl:25; lunar_deform.hl:4985; LocalAuto37:826;
  LocalAuto34 twin `MHAEYJN_prop_p34`:154, defeq): lunar convex local fans
  survive the pinned deformation.
* `himj` — HOL `IMJXPHR_concl` (IMJXPHR.hl:9682; LocalAuto34:273; aligned with
  LocalAuto1 `IMJXPHRv2_concl`:976): the ear-tightening identity; its
  antecedents are `ZLZTHIC_concl` (LocalAuto1:881, exact) and `MHAEYJN`,
  composed by `IMJXPHR_p34` (LocalAuto34:2433).
Conclusion — `localAnnulusInequalityP22 V` (PackingAuto22:228) via the real
packed inequality (`localAnnulusInequality`, PackingAuto2:536) and the exact
paste `localAnnulusInequalityP22_of_ported`. The debt lives entirely in the
giant core (`terminal_bank_lunar_imjxphr_imp_localAnnulusInequality`). -/
theorem local_annulus_inequality_bridge
    (V : Set V3) (hP : Packing V) (hV : V ⊆ ballAnnulus)
    (terminalCases : List ScsV39)
    (hbank : ∀ s ∈ terminalCases, ∀ vv : ℕ → V3, BBsV39 s vv → 0 ≤ taustarV39 s vv)
    (hterm : main_nonlinear_terminal_v11)
    (hlunar : MHAEYJN_prop_bridge)
    (himj : IMJXPHR_concl_bridge) :
    localAnnulusInequalityP22 V :=
  localAnnulusInequalityP22_of_ported
    (terminal_bank_lunar_imjxphr_imp_localAnnulusInequality V hP hV terminalCases
      hbank hterm hlunar himj)

/-! ## 4. W7 manifest endpoint (docs/local-manifest.md:128) -/

/-- W7 manifest item (docs/local-manifest.md:128,139): "capstone: MHAEYJN
deformation lemmas + main-estimate terminal case bank; ends in bridge def
matching `localAnnulusInequalityP22`" — the terminal-case-bank ⟹ bridge-def
direction, stated as the assembly endpoint: seal the case bank with the
anchor, take the lunar (LocalAuto37) and IMJXPHR (LocalAuto34) capstones, and
the bridge definition follows for every annulus packing. Exact composition;
the proof debt is exactly that of
`terminal_bank_lunar_imjxphr_imp_localAnnulusInequality` (no new sorry). -/
theorem terminal_case_bank_imp_bridge_def
    (hterm : main_nonlinear_terminal_v11)
    (terminalCases : List ScsV39)
    (hbank : ∀ s ∈ terminalCases, ∀ vv : ℕ → V3, BBsV39 s vv → 0 ≤ taustarV39 s vv)
    (hlunar : MHAEYJN_prop_bridge)
    (himj : IMJXPHR_concl_bridge) :
    ∀ V : Set V3, Packing V → V ⊆ ballAnnulus → localAnnulusInequalityP22 V :=
  fun V hP hV =>
    local_annulus_inequality_bridge V hP hV terminalCases hbank hterm hlunar himj

end Kepler.Text
