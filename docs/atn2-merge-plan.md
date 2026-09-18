# atn2 merge plan — single-sourcing the sphere.hl / localization.hl kit

Status: proposal (read-only survey, 2026-09-18). Executor may edit `lean/Kepler/**` per §5.
Goal: make the **PackingAuto18/20-rooted family** (LocalAuto1/16/18/19/22/23/25/28/31/33/34/37/38, …)
and the **PackingAuto21-rooted family** (PackingAuto25, and by extension the LocalAuto2/9/11 lane)
co-importable by removing the duplicate `Kepler.Text.atn2` (and its kit twins), then
delete the ~80 `_pNN` verbatim twins against one canonical home.

Method: every claim below was checked by `grep -rn` over `lean/Kepler/Text/*.lean` plus
≤80-line reads of the def bodies; def bodies were diffed mechanically (verbatim-equal
unless flagged in §6).

---

## 1. Duplicate-def inventory

### 1.1 The blocking clash (why the families cannot be imported today)

| def | defined at (module:line) | family that sees it |
|---|---|---|
| `atn2` | PackingAuto18.lean:154 | PA18 root (imported by LocalAuto1:74) → LocalAuto1/7/8/12/14/16/17/18/19/20/21/22/23/24/25/26/27/28/29/30/31/32/33/34/35/36/37/38 |
| `atn2` | PackingAuto20.lean:66 | PA20 root (via LocalAuto2:58) → LocalAuto2/5/6/9/11 |
| `atn2` | PackingAuto21.lean:106 | PA21 root → PackingAuto25 (PA25:68) |

All three bodies are **verbatim identical** (PA21:105 even says “PackingAuto18/20 verbatim”).
`PackingAuto20` and `PackingAuto21` have the *same import list* (PA2,5,6,7,8,10,11,12,13,Polytope)
and duplicate 11 more defs: `deltaXf`(73/113) `deltaX4f`(80/120) `dihXf`(85/125) `dihY`(90/130)
`solY`(94/134) `volXf`(99/139) `volY`(103/143) `vol3r`(126/147) `vol3f`(129/150) `gamma3f`(138/159)
+ theorem `HJKDESR1a_1cell`(PA20:241 / PA21:628, byte-identical statements).
`PackingAuto18` additionally duplicates `deltaX`(134 ≡ `deltaXf`), `upsX`(149 ≡ PA25:171), `atn2`,
and *near*-duplicates theorem `MCELL2_SUBSET_AFF_GE`(PA18:1056 vs PA21:821 — **statements differ**, see §6).
PA18 also defines the unsuffixed kit-names `arcLength`(161), `deltaP`(142), `selectd`, `complexDot`,
`normalize` — only `arcLength` moves (§3); the rest stay (no twin anywhere).

Import-graph fact: **no module reaches two of {PA18, PA20, PA21} today**; that is exactly the split.

### 1.2 `_pNN` twins of the sphere.hl numeric kit (all verbatim-equal to §3 bodies unless noted)

| canonical name | twins (module:line, body verdict) |
|---|---|
| `atn2` | atn2_p11 LA11:127 (alias `= atn2`), atn2_p16 LA16:269 ✔, atn2_p22 LA22:91 ✔ |
| `deltaX` (PA18 name; PA20/21 call it `deltaXf`) | deltaXf_p11 LA11:129 (alias), deltaXf_p16 LA16:276 ✔ |
| `deltaX4` (LA1:766; ≡ PA20 `deltaX4f`:80) | deltaX4f_p11 LA11:132 (alias), deltaX4f_p16 LA16:283 ✔, deltaX4_p18 LA18:103 ✔, deltaX4_p23 LA23:111 ✔ |
| `deltaX5` | deltaX5f_p11 LA11:165 ✔**correct**, deltaX5_p21 LA21:113 ✔**correct**, deltaX5_p22 LA22:120 ✔**correct**; **LA1:772 is a MIS-PORT — see §2.1** |
| `deltaX6` | deltaX6_p21 LA21:119 ✔, deltaX6_p22 LA22:125 ✔ |
| `deltaX1f` | deltaX1f_p11 LA11:159 (only copy) |
| `deltaY` (= `deltaX` at squared y) | deltaY_p11 LA11:149, deltaY_p16 LA16:298, deltaY_p18 LA18:110, deltaY_p22 LA22:108, deltaY_p23 LA23:117, deltaYP25 PA25:98 — all ✔ (no unsuffixed def exists yet) |
| `delta4Y` (= `deltaX4` at squared y) | delta4Y_p11 LA11:188, delta4Y_p22 LA22:130 ✔; delta4YP38 LA38:126 (`sorry` stub) |
| `yOfX` | yOfX_p11 LA11:177, yOfX_p22 LA22:86, yOfXP38 LA38:130 — all ✔ |
| `dihXf` | dihXf_p11 LA11:135 (alias), dihXf_p16 LA16:288 ✔, dihXf_p22 LA22:98 ✔ (uses LA1 `deltaX`/`deltaX4`); dihY_p18/dihY_p23 inline the same formula ✔ |
| `dihY` | dihY_p11 LA11:138 (alias), dihY_p16 LA16:294 ✔, dihY_p18 LA18:115 ✔(inlined), dihY_p23 LA23:122 ✔(inlined) |
| `solY` | solY_p19 LA19:119 ✔ (via dihY_p18); **solY_p22 LA22:148 is a `sorry` stub** — replacement upgrades it to the real body |
| `upsX` (sphere.hl `ups_x`, Gram form) | upsX_p11 LA11:144 ✔, PA25:171 ✔. **Not a twin:** upsX_p6 LA6:63 is a *different* HOL function (packing_defs rendering, `½(x1+x2+x6+√…)`); keep it in LA6 |
| `arcLength` | only PA18:161 (move, no twin) |
| `quadraticRootPlus` | quadraticRootPlus_p11 LA11:154 ✔, quadraticRootPlus_p19 LA19:164 ✔ (`b*b` vs `b^2` spelling), quadraticRootPlusP38 LA38:135 ✔ |
| `num1`/`dnum1` | num1_p22 LA22:136, dnum1_p22 LA22:140 (only copies; move) |
| `taum` (real body = LA19) | **real:** taumP19 LA19:135 (body via solY/const1/lnazim). **opaque `sorry` stubs:** taum_p11 LA11:220, taum_p16 LA16:303, taum_p22 LA22:114, taum_p23 LA23:132. **x-space stubs:** taumX_p19 LA19:143, taumXP38 LA38:98 |
| `const1` (= `solY 2 2 2 2 2 2 / π`) | const1_p2 LA2:333 ✔, const1P19 LA19:128 ✔ (formula identical; LA19:126 “wrong atn2 side” remark is stale — §6) |
| `ly` | lyP19 LA19:124 (inlined). **Not verbatim:** ly_p2 LA2:329 (`interp_p2 2 1 2.52 0 y`) — propositionally equal, do NOT merge in this pass |

### 1.3 `_pNN` twins of the localization.hl / hypermap kit

| canonical name | twins (module:line, body verdict) |
|---|---|
| `EE` (generic `EE v S = {w | {v,w} ∈ S}`) | EE_p2 LA2:117 ✔, EE_p3 LA3:106 ✔, EE_p18 LA18:124 ✔, EE_p4 LA4:731 ✔ (V3-monomorphic); LA1:89 `ee` (V3) ✔ same body; LA13:87 `eeP13` ✔ body but different lane (keep) |
| `azimCycle` | azimCycle_p2 LA2:82 ✔, azimCycle_p3 LA3:78 ✔, azimCycle_p7 LA7:125 ✔, azimCycle_p14 LA14:234 ✔, azimCycle_p18 LA18:128 ✔; azimCycle_p4 LA4:734 is a **`sorry` stub** (keep, see §6); azimCycleP13 LA13:106 **different semantics** (junk `u`, `≤`, arg order) — keep |
| `azimInFan` | LA1:94 (canonical body, `sigmaFan`-rendered). azimInFan_p2 LA2:201, _p3 LA3:161, _p4 LA4:798, _p18 LA18:143 render via `EE`+`azimCycle` — **NOT syntactically equal**; azimInFanP13 LA13:154 uses `sigmaFan` ✔-body but different lane. Do not merge twins in pass 1 (§6) |
| `rhoNode1` | LA1:99 canonical body; rhoNode1_p2 LA2:186 ✔, rhoNode1_p18 LA18:138 ✔ |
| `ivsRhoNode1` | LA1:103 canonical; ivsRhoNode1_p2 LA2:191 ✔ |
| `interiorAngle1` | LA1:107 canonical; interiorAngle1_p2 LA2:196 ✔ (equal once `rhoNode1_p2` is renamed) |

### 1.4 dih2k kit (`torsor` / `constraintSystem` / `stableSystem`) — shape forks

| shape | copies |
|---|---|
| A: `Finset ℕ`, `d : ℝ` (the dih2k-chapter instantiation) | torsor_p9 LA9:145 ≡ torsor_p18 LA18:149 ✔; constraintSystem_p9 LA9:151 ≡ constraintSystem_p18 LA18:156 ✔; stableSystem_p9 LA9:160 ≡ stableSystem_p18 LA18:166 ✔ |
| B: generic `Finset α`, `d : ℕ` | torsor_p4 LA4:832, constraintSystem_p4 LA4:840, stableSystem_p4 LA4:848 (only copies of shape B; keep) |
| C: `Set ℕ`/generic `Set α`, `d : ℕ`, `Nat.card` | torsor_p8 LA8:74 {α}, torsor_p23 LA23:136 (ℕ) ✔-pair; constraintSystem_p8 LA8:79 ≡ constraintSystem_p23 LA23:141 ✔; stableSystem_p8 LA8:88 ≡ stableSystem_p23 LA23:152 ✔ |
| records | StableSy LA8:97 (`d : ℕ`) vs StableSyP23 LA23 (~157) (`d : ℝ`) — **not twins**, see §6 |

Only shape A is verbatim-duplicated across *both* families, so only shape A is canonicalized in
pass 1. Shapes B/C stay suffixed where they are (not import blockers).

---

## 2. Canonical home: new module `lean/Kepler/Text/SphereKit.lean`

One module, imported by PA18/PA20/PA21/PA25/LA3 (+ transitively by everybody else).
It must NOT import PA18/PA20/PA21 (that would re-create the clash); its only deps are
already shared by both families. Skeleton (bodies = the most-used/verified variant; all are
verbatim from the cited line):

```lean
/-
Kepler.Text.SphereKit — single home of the sphere.hl numeric kit and the
localization.hl fan kit, deduplicated from the PackingAuto18/20/21 hub split
and the `_pNN` verbatim twins.  Bodies are the verified variants; see
docs/atn2-merge-plan.md.  Do NOT import PackingAuto18/20/21 here.
-/
import Kepler.Geom.Azim          -- V3, azim, projection
import Kepler.Text.Fan           -- sigmaFan (azimInFan)
import Kepler.Text.PackingAuto2  -- sol0, mm1, mm2, h0, lfun (shared constants)
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## sphere.hl: two-argument arctangent and the delta_x family -/

/-- HOL `atn2` (sphere.hl:48-52). Verbatim = PackingAuto18.lean:154 =
PackingAuto20.lean:66 = PackingAuto21.lean:106. -/
noncomputable def atn2 (x y : ℝ) : ℝ :=
  if |y| < x then Real.arctan (y / x)
  else if 0 < y then Real.pi / 2 - Real.arctan (x / y)
  else if y < 0 then -(Real.pi / 2) - Real.arctan (x / y)
  else Real.pi

/-- HOL `delta_x` (sphere.hl:86). = PackingAuto18.lean:134 (`deltaX`) =
PackingAuto20.lean:73 (`deltaXf`). Canonical name follows the LocalAuto1 lane. -/
def deltaX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6) +
    x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6) +
    x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) -
    x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6

/-- HOL `delta_x4` (sphere.hl:110). = LA1:766 = PA20:80 `deltaX4f`. -/
noncomputable def deltaX4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6 +
    x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

/-- HOL `delta_x5` (sphere.hl): partial of `delta_x` at `x5`. CORRECTED body
(= LocalAuto21.lean:113 = LocalAuto11.lean:165 = LocalAuto22.lean:120);
LocalAuto1.lean:772 was a mis-port dropping `- x1 * x3 + x1 * x4`. See §2.1. -/
noncomputable def deltaX5 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x1 * x3 + x1 * x4 - x2 * x5 + x3 * x6 - x4 * x6 +
    x2 * (x1 - x2 + x3 + x4 - x5 + x6)

/-- HOL `delta_x6` (sphere.hl:114). = LA22:125 = LA21:119. -/
noncomputable def deltaX6 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 + x2 * x5 - x1 * x2 - x4 * x5 - x3 * x6 +
    x3 * (x1 + x2 - x3 + x4 + x5 - x6)

/-- HOL `delta_x1` (Nonlin_def.hl; partial at `x1`). = LA11:159 (only copy). -/
noncomputable def deltaX1f (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x4 * (-x1 + x2 + x3 - x4 + x5 + x6) - x1 * x4 +
    x2 * x5 + x3 * x6 - x2 * x6 - x3 * x5

/-- HOL `y_of_x` (sphere.hl). = LA22:86. -/
def yOfX (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  f (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `delta_y` (sphere.hl): `y_of_x delta_x`. Body = deltaY_p11/p16/p18/p22/p23,
deltaYP25 (all `deltaX` at squared lengths). -/
noncomputable def deltaY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `delta4_y` (sphere.hl): `y_of_x delta_x4`. -/
noncomputable def delta4Y (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  yOfX (deltaX4) y1 y2 y3 y4 y5 y6

/-! ## sphere.hl: dihedral angles and spherical excess -/

/-- HOL `dih_x` (sphere.hl:153). = PackingAuto20.lean:85. -/
noncomputable def dihXf (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 + atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
    (-(deltaX4 x1 x2 x3 x4 x5 x6))

/-- HOL `dih_y` (sphere.hl:159). = PackingAuto20.lean:90 (≡ all `_pNN` twins). -/
noncomputable def dihY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `sol_y` (sphere.hl:185). = PackingAuto20.lean:94 (solY_p19 upgrades
LA22's `sorry` stub to the real body). -/
noncomputable def solY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  dihY y1 y2 y3 y4 y5 y6 + dihY y2 y3 y1 y5 y6 y4 + dihY y3 y1 y2 y6 y4 y5 -
    Real.pi

/-! ## sphere.hl: ups_x, arclength, root, Terminal.hl tau kit -/

/-- HOL `ups_x` (sphere.hl:122-124). = PackingAuto18.lean:149.
(NB: LocalAuto6 `upsX_p6` is a DIFFERENT HOL function and stays there.) -/
def upsX (x1 x2 x6 : ℝ) : ℝ :=
  -(x1 * x1) - x2 * x2 - x6 * x6 + 2 * x1 * x6 + 2 * x1 * x2 + 2 * x2 * x6

/-- HOL `arclength` (sphere.hl:258-260). = PackingAuto18.lean:161. -/
noncomputable def arcLength (a b c : ℝ) : ℝ :=
  Real.pi / 2 +
    atn2 (Real.sqrt (upsX (a * a) (b * b) (c * c))) (c * c - a * a - b * b)

/-- HOL `quadratic_root_plus` (sphere.hl:67). = LA11:154 = LA19:164 = LA38:135. -/
noncomputable def quadraticRootPlus (a b c : ℝ) : ℝ :=
  (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)

/-- HOL `num1` (Terminal.hl, reconstructed). = LA22:136 (only copy). -/
noncomputable def num1 (e1 e2 e3 x4 x5 x6 : ℝ) : ℝ := -- body verbatim LA22:136-137

/-- HOL `dnum1` (Terminal.hl). = LA22:140 (only copy). -/
noncomputable def dnum1 (e1 e2 e3 x4 x5 x6 : ℝ) : ℝ := -- body verbatim LA22:140-141

/-- HOL `const1` (sphere.hl:197) = `solY 2 2 2 2 2 2 / π`; = const1_p2 (LA2:333) =
const1P19 (LA19:128). -/
noncomputable def const1 : ℝ := solY 2 2 2 2 2 2 / Real.pi

/-- HOL `ly` (sphere.hl:199). = lyP19 (LA19:124), inlined rendering.
(LA2 `ly_p2` keeps the `interp_p2` rendering; see §6.) -/
noncomputable def ly (y : ℝ) : ℝ := 1 + (y - 2) * (0 - 1) / (2.52 - 2)

/-- HOL `lnazim` (sphere.hl:214). = LA19:131. -/
noncomputable def lnazim (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  ly y1 * dihY y1 y2 y3 y4 y5 y6

/-- HOL `taum` (sphere.hl:215, the truncated tau of a quad). Body = taumP19
(LA19:135) — the only real body; replaces the opaque `sorry` stubs
taum_p11/taum_p16/taum_p22/taum_p23 at their use sites. -/
noncomputable def taum (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  solY y1 y2 y3 y4 y5 y6 * (1 + const1) -
    const1 * (lnazim y1 y2 y3 y4 y5 y6 +
      lnazim y2 y3 y1 y5 y6 y4 + lnazim y3 y1 y2 y6 y4 y5)

/-- EXTERNAL-ANCHOR: HOL `taum_x` (sphere.hl:827); `rhazim_x` kit unported.
Stub = taumX_p19 (LA19:143) = taumXP38 (LA38:98). -/
noncomputable def taumX : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ _ _ _ _ => (0 : ℝ)

/-! ## localization.hl: EE, azim_cycle, rho_node1, azim_in_fan -/

/-- HOL `EE` (localization.hl:38). = EE_p2 (LA2:117) = EE_p3 (LA3:106) =
EE_p18 (LA18:124) = EE_p4 (LA4:731) = `ee` (LA1:89). -/
def EE {α : Type*} (v : α) (S : Set (Set α)) : Set α := {w | {v, w} ∈ S}

/-- HOL `azim_cycle` (sphere.hl:414). = azimCycle_p2 (LA2:82) = _p3 (LA3:78) =
_p7 (LA7:125) = _p14 (LA14:234) = _p18 (LA18:128). HOL `projection (w-v) (u-v)`
↔ repo `projection (u - v) (w - v)`. -/
noncomputable def azimCycle (W : Set V3) (v w p : V3) : V3 :=
  if W ⊆ {p} then p
  else
    Classical.epsilon fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖

/-- HOL `azim_in_fan` (localization.hl:74). = LocalAuto1.lean:94 (the
`sigmaFan`-rendered body used by the whole LocalAuto1 lane). The
`EE`+`azimCycle`-rendered twins azimInFan_p2/_p3/_p4/_p18 stay put (§6). -/
noncomputable def azimInFan (e : V3 × V3) (E : Set (Set V3)) : ℝ :=
  if 1 < (EE e.1 E).ncard then azim 0 e.1 e.2 (sigmaFan 0 Set.univ E e.1 e.2)
  else 2 * Real.pi

/-- HOL `rho_node1` (localization.hl:115). = LA1:99 = rhoNode1_p2 = rhoNode1_p18. -/
noncomputable def rhoNode1 (FF : Set (V3 × V3)) (v : V3) : V3 :=
  Classical.epsilon (fun w => (v, w) ∈ FF)

/-- HOL `ivs_rho_node1` (localization.hl:117). = LA1:103 = ivsRhoNode1_p2. -/
noncomputable def ivsRhoNode1 (FF : Set (V3 × V3)) (v : V3) : V3 :=
  Classical.epsilon (fun a => (a, v) ∈ FF)

/-- HOL `interior_angle1` (localization.hl:119). = LA1:107 = interiorAngle1_p2. -/
noncomputable def interiorAngle1 (x : V3) (FF : Set (V3 × V3)) (v : V3) : ℝ :=
  azim x v (rhoNode1 FF v) (ivsRhoNode1 FF v)

/-! ## dih2k.hl: torsor / constraint_system / stable_system (shape A:
`Finset ℕ`, `d : ℝ`) -/

/-- HOL `torsor` (dih2k.hl:48). = torsor_p9 (LA9:145) = torsor_p18 (LA18:149). -/
def torsor (s : Finset ℕ) (k : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ x ∈ s, f x ∈ s) ∧ (∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂) ∧
    (∀ i x, 0 < i → i < k → x ∈ s → f^[i] x ≠ x) ∧
    (∀ x ∈ s, f^[k] x = x) ∧ s.card = k

/-- HOL `constraint_system` (dih2k.hl:52), `d : ℝ`. = constraintSystem_p9 =
constraintSystem_p18. -/
def constraintSystem (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  3 ≤ k ∧ k ≤ 6 ∧ torsor s k f ∧
    (∀ i j, a i j = a j i ∧ b i j = b j i ∧ a i j ≤ b i j) ∧
    (∀ i j, a i j = a i (f^[k] j) ∧ b i j = b i (f^[k] j)) ∧
    J ⊆ s.image (fun i => {i, f i}) ∧
    J.card + k ≤ 6

/-- HOL `stable_system` (dih2k.hl:61), `d : ℝ`. = stableSystem_p9 =
stableSystem_p18 (keep the `cstab_p4` anchor reference). -/
def stableSystem (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  constraintSystem k d s a b J f ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 ≤ a i j) ∧
    (∀ i ∈ s, a i i = 0 ∧ b i (f i) ≤ cstab_p4) ∧
    (∀ i j, {i, j} ∈ J → a i j = Real.sqrt 8 ∧ b i j = cstab_p4)

end Kepler.Text
```

Implementation notes:
* `num1`/`dnum1`: copy the bodies from LocalAuto22.lean:136-141 verbatim (placeholders above).
* `stableSystem` references `cstab_p4` (LocalAuto4.lean:358) exactly as LA9/LA18 do today —
  that keeps a SphereKit → LocalAuto4 dependency for a *constant*. If a root-level dependency on
  LocalAuto4 is undesirable, move `cstab_p4 : ℝ := 3.01` into SphereKit (it equals LA1:172 `cstab`
  and LocalAnchors:34 `cstabAnchor`; keep all three names pointing at one literal — see §6) and
  re-point LA4/LA9/LA18 at it.
* `deltaXf`/`deltaX4f` are NOT exported: every use site is renamed to `deltaX`/`deltaX4` (§5).

### 2.1 deltaX5 mis-port — VERIFIED

* LocalAuto1.lean:772-773 defines
  `deltaX5 := x2 * (x1 - x2 + x3 + x4 - x5 + x6) - x2 * x5 + x3 * x6 - x4 * x6`
  — **4 terms; it drops `- x1 * x3 + x1 * x4`.**
* LocalAuto11.lean:165-167, LocalAuto21.lean:113-115 and LocalAuto22.lean:120-121 all carry the
  full 6-term body, and LA21:110-112 + LA22:116-119 both flag LA1's version in comments.
* Independent check by differentiating the §3 `deltaX` body w.r.t. `x5`:
  `∂/∂x5 = x1*x4 + x2*e2 - x2*x5 - x1*x3 - x4*x6 + x3*x6` with
  `e2 = x1 - x2 + x3 + x4 - x5 + x6` — the 6-term body. ✔
* Consequence: LocalAuto1's `mkSimplex1` (LA1:777-783) consumes the wrong `deltaX5`; after the
  fix its value changes. LA11 already has the correct twin `mkSimplex1_p11` (built on
  `deltaX5f_p11`) with theorems (LA11:918-1006). After the merge, LA1's `mkSimplex1` theorems
  (e.g. LA1:1032) must be recompiled; any whose *statement* hardcoded the mis-ported value needs
  restating against the corrected body. The corrected body is canonical.

---

## 3. What stays where (not moved)

| item | home | reason |
|---|---|---|
| `volXf` `volY` `vol3r` `vol3f` `gamma3f` `vol4f` | PackingAuto20 (PA21 deletes its copies and imports PA20) | duplicated only between PA20/PA21; no LocalAuto user |
| `deltaP` `selectd` `complexDot` `normalize` `SUM_GAMMAX…` | PackingAuto18 | no twins |
| `upsX_p6` | LocalAuto6 | different HOL function (packing_defs `ups_x`) |
| `azimCycleP13` `azimInFanP13` `eeP13` `ivsAzimCycleP13` … | LocalAuto13 | different junk-value semantics; separate reconciliation |
| `azimInFan_p2/_p3/_p4/_p18`, `wedgeInFanGt_p2`, `wedgeInFanGe_p4/P13` | in place | not syntactic twins of the canonical body (§6) |
| `azimCycle_p4` (sorry stub), `EE_p4`→`EE` only at use sites of LA11 | LocalAuto4 | LA4 does not reach SphereKit in pass 1; stub stays |
| `torsor_p4`/`constraintSystem_p4`/`stableSystem_p4` (shape B), `torsor_p8`/`torsor_p23`, `constraintSystem_p8`/`_p23`, `stableSystem_p8`/`_p23`, `StableSy`/`StableSyP23` | in place | shape forks, not verbatim twins (§1.4) |
| `hasOrders_p2/_p3/_p4`, `cyclicOn_*`, `dih2k_p2/_p3/_p4`, `ordPairs_*`, `selfPairs_*`, `dartsOfHyp_*`, `eeOfHyp_*`, `nnOfHyp_*`, `ffOfHyp_*`, `interp_p2`, `ly_p2`, `rho_p2`, `hDart_p2` | in place | phase-3 backlog (suffixed, not blocking) |
| `cstab` (LA1:172) / `cstab_p4` (LA4:358) / `cstabAnchor` (LocalAnchors:34) | in place | three names, same literal 3.01; unify in phase 3 |

---

## 4. Rename map (mechanical, word-boundary `sed -i`, skip doc comments where noted)

| old → new | files (use-site counts incl. def-adjacent docs) |
|---|---|
| `deltaXf` → `deltaX` | PA20 (3), PA21 (4), PA25 (11), LA2 (3), LA11 (8 incl. its alias def) |
| `deltaX4f` → `deltaX4` | PA20 (2), PA21 (2), LA11 (10 incl. alias), LA16 (3), LA22 (1 doc), LA23 (1 doc) |
| `deltaY_p11`→`deltaY`; `deltaY_p16`→`deltaY`; `deltaY_p18`→`deltaY`; `deltaY_p22`→`deltaY`; `deltaY_p23`→`deltaY`; `deltaYP25`→`deltaY` | LA11 (27), LA16 (6), LA18 (1)+LA19 (188)+LA23 (1 doc), LA22 (28), LA23 (3)+LA38 (20), PA25 (9) |
| `delta4Y_p11`→`delta4Y`; `delta4Y_p22`→`delta4Y`; `delta4YP38`→`delta4Y` | LA11 (4), LA22 (3), LA38 (2) |
| `deltaX5f_p11`→`deltaX5`; `deltaX5_p21`→`deltaX5`; `deltaX5_p22`→`deltaX5` | LA11 (3), LA21 (5), LA22 (7) |
| `deltaX6_p21`→`deltaX6`; `deltaX6_p22`→`deltaX6` | LA21 (4), LA22 (4) |
| `deltaX1f_p11`→`deltaX1f` | LA11 (41) |
| `upsX_p11`→`upsX` | LA11 (42) |
| `yOfX_p11`→`yOfX`; `yOfX_p22`→`yOfX`; `yOfXP38`→`yOfX` | LA11 (4), LA22 (9), LA38 (1) |
| `quadraticRootPlus_p11`→`quadraticRootPlus`; `_p19`→same; `P38`→same | LA11 (11), LA19 (8), LA38 (9) |
| `num1_p22`→`num1`; `dnum1_p22`→`dnum1` | LA22 (17/6) |
| `dihXf_p11`→`dihXf`; `dihXf_p16`→`dihXf`; `dihXf_p22`→`dihXf` | LA11 (2), LA16 (3)+LA21 (9)+LA22 (1 doc), LA22 (20) |
| `dihY_p11`→`dihY`; `dihY_p16`→`dihY`; `dihY_p18`→`dihY`; `dihY_p23`→`dihY` | LA11 (11)+LA23 (1 doc), LA16 (9)+LA21 (1)+LA22 (1 doc), LA18 (4)+LA19 (6)+LA23 (1 doc)+LA33 (2), LA23 (3)+LA38 (4) |
| `taum_p11`→`taum`; `taum_p16`→`taum`; `taum_p22`→`taum`; `taum_p23`→`taum`; `taumP19`→`taum`; `taumX_p19`→`taumX`; `taumXP38`→`taumX` | LA11 (9), LA16 (6), LA22 (18), LA23 (8)+LA38 (17), LA19 (26), LA19 (4)+LA38 (1 doc), LA38 (9) |
| `solY_p19`→`solY`; `solY_p22`→`solY` | LA19 (4), LA22 (3) |
| `const1_p2`→`const1`; `const1P19`→`const1` | LA2 (1, in rho_p2), LA19 (2) |
| `lyP19`→`ly` | LA19 (2 — its def + lnazim) |
| `EE_p2`→`EE`; `EE_p3`→`EE`; `EE_p18`→`EE`; `EE_p4`→`EE`; LA1 `ee`→(deleted, uses become `EE`) | LA2 (14)+LA5 (21)+LA6 (8)+LA9 (3)+LA18 (1 doc); LA3 (45)+LA10 (40); LA18 (5); LA11 (3); LA1 (≥2: azimInFan body) |
| `azimCycle_p2`→`azimCycle`; `azimCycle_p3`→`azimCycle`; `azimCycle_p7`→`azimCycle`; `azimCycle_p14`→`azimCycle`; `azimCycle_p18`→`azimCycle` | LA2 (7)+LA5 (15)+LA6 (1)+LA9 (3); LA3 (24)+LA10 (19); LA7 (21); LA14 (20); LA18 (4)+LA38 (2) |
| `rhoNode1_p2`→`rhoNode1`; `rhoNode1_p18`→`rhoNode1` | LA2 (36)+LA5 (120)+LA6 (81)+LA9 (22)+LA11 (1 doc); LA18 (5) |
| `ivsRhoNode1_p2`→`ivsRhoNode1` | LA2 (2)+LA5 (13)+LA6 (8)+LA9 (3)+LA11 (2) |
| `interiorAngle1_p2`→`interiorAngle1` | LA2 (4)+LA5 (14)+LA6 (20)+LA9 (5) |
| `torsor_p9`→`torsor`; `torsor_p18`→`torsor`; `constraintSystem_p9`→`constraintSystem`; `constraintSystem_p18`→`constraintSystem`; `stableSystem_p9`→`stableSystem`; `stableSystem_p18`→`stableSystem` | LA9 (3/2/7 uses), LA18 (4/4/5 uses) |

Not renamed (stay suffixed, see §3): `azimInFan_p2/_p3/_p4/_p18`, `azimCycle_p4`, `upsX_p6`,
all P13 kit, dih2k shapes B/C, `ly_p2`, `StableSyP23`, PA25's own `vol4fP25`/`gamma4fgcyP25`/`rad2YP25`
(already suffixed, keep).

---

## 5. Per-file edit map (every Kepler/Text/*.lean)

Legend: **DEL** = delete def + its `/--` doc-comment (ranges from current file);
**IMP+** = add `import Kepler.Text.SphereKit` (even where transitive, for the 6 anchor files);
**REN** = apply §4 renames. Files not listed as edited are in the no-op list.

**New file — SphereKit.lean** (§3 skeleton) — create.

1. **PackingAuto18.lean** — IMP+. DEL `deltaX`(133-138), `upsX`(148-150), `atn2`(152-158), `arcLength`(160-163). Internal uses of those 4 names resolve to SphereKit. Everything else unchanged.
2. **PackingAuto20.lean** — IMP+. DEL `atn2`(65-70), `deltaXf`(72-77), `deltaX4f`(79-82), `dihXf`(84-87), `dihY`(89-91), `solY`(93-96). REN `deltaXf`→`deltaX`, `deltaX4f`→`deltaX4` (vol/dihXf/theorem bodies + headers). Keeps vol kit + `HJKDESR1a_1cell`.
3. **PackingAuto21.lean** — IMP+ **and** add `import Kepler.Text.PackingAuto20` (its kit header at 102-103 explicitly requests this). DEL lines 102-167 (whole “Verbatim hub-lane kit” block: atn2, deltaXf, deltaX4f, dihXf, dihY, solY, volXf, volY, vol3r, vol3f, gamma3f), DEL `gamma2_x_div_azim_v2` **only if** it too is a PA20 twin — check before deleting; otherwise keep. DEL `HJKDESR1a_1cell`(624-629) (byte-identical to PA20's). REN `deltaXf`→`deltaX`, `deltaX4f`→`deltaX4`. REN its `MCELL2_SUBSET_AFF_GE`(820-…) → `MCELL2_SUBSET_AFF_GE_p21` (statement differs from PA18's; §6).
4. **PackingAuto25.lean** — IMP+. DEL `upsX`(170-172), DEL `deltaYP25`(96-99). REN `deltaYP25`→`deltaY` (9 uses), `deltaXf`→`deltaX` (11).
5. **LocalAuto1.lean** — IMP+ (optional; transitive via PA18 — skip if minimal). DEL `ee`(88-89), `azimInFan`(91-96), `rhoNode1`(98-100), `ivsRhoNode1`(102-104), `interiorAngle1`(106-108), `deltaX4`(764-768), `deltaX5`(770-773). REN its internal `ee`→`EE` (azimInFan moved out, so mostly none), nothing else — `deltaX`/`deltaX4`/`deltaX5` uses (mkSimplex1 775-783, delta126x… in LA19 style) keep their names and now get the **corrected** `deltaX5`. Re-examine mkSimplex1 theorems (§2.1).
6. **LocalAuto2.lean** — IMP+ (transitive via PA20; add only if you want it explicit — skip). DEL `azimCycle_p2`(78-88), `EE_p2`(116-117), `rhoNode1_p2`(183-187), `ivsRhoNode1_p2`(189-192), `interiorAngle1_p2`(194-197), `const1_p2`(331-333). REN per §4 (EE_p2 14, azimCycle_p2 7, rhoNode1_p2 36, ivsRhoNode1_p2 2, interiorAngle1_p2 4, const1_p2 1, deltaXf 3). Keep `ly_p2`, `interp_p2`, `rho_p2`, `azimInFan_p2`, `wedgeInFanGt_p2`, `hasOrders_p2`, `dih2k_p2`, HYP kit `_p2`s.
7. **LocalAuto3.lean** — **IMP+ (required: LA3 reaches no kit root)**. DEL `azimCycle_p3`(73-84), `EE_p3`(105-106). REN EE_p3 (45), azimCycle_p3 (24). Keep azimInFan_p3, hasOrders_p3, cyclicOn_p3, dih2k_p3, WRGCVDR `_p3` kit.
8. **LocalAuto4.lean** — NO structural change in pass 1 (stays off-SphereKit). Optional: DEL `EE_p4`(730-731)+IMP+ and REN its 13 uses → `EE`; if done, LA11's 3 `EE_p4` uses also flip. Defer to phase 3 if touched lasily — do it in the same wave as LA11 or not at all.
9. **LocalAuto5.lean** — REN via §4 (EE_p2 21, azimCycle_p2 15, rhoNode1_p2 120, ivsRhoNode1_p2 13, interiorAngle1_p2 14). No def deletions. Gets SphereKit via LA2.
10. **LocalAuto6.lean** — REN (EE_p2 8, azimCycle_p2 1, rhoNode1_p2 81, ivsRhoNode1_p2 8, interiorAngle1_p2 20). KEEP `upsX_p6`(60-66) as-is.
11. **LocalAuto7.lean** — DEL `azimCycle_p7`(121-131). REN azimCycle_p7 (21). Plain `atn2` uses (2) keep working (PA18 root).
12. **LocalAuto8.lean** — NO EDIT in pass 1 (torsor_p8/constraintSystem_p8/stableSystem_p8/StableSy stay; shape C).
13. **LocalAuto9.lean** — DEL `torsor_p9`(144-148), `constraintSystem_p9`(150-157), `stableSystem_p9`(159-165). REN torsor_p9 (3), constraintSystem_p9 (2), stableSystem_p9 (7) → canonical; plus the LA2-lane localization renames (EE_p2 3, azimCycle_p2 3, rhoNode1_p2 22, ivsRhoNode1_p2 3, interiorAngle1_p2 5). Keep azimInFan_p2. Note its `stableSystem_p9` body's `cstab_p4` ref keeps LA4 import.
14. **LocalAuto10.lean** — REN (EE_p3 40, azimCycle_p3 19). Keep azimInFan_p3.
15. **LocalAuto11.lean** — DEL Section A aliases + twins: `atn2_p11`(123-127), `deltaXf_p11`(129-130), `deltaX4f_p11`(132-133), `dihXf_p11`(135-136), `dihY_p11`(138-139), `upsX_p11`(141-145), `deltaY_p11`(147-150), `quadraticRootPlus_p11`(152-155), `deltaX1f_p11`(157-161), `deltaX5f_p11`(163-167), `yOfX_p11`(177-179), `delta4Y_p11`(187-189), `taum_p11`(218-220). REN per §4 (deltaXf_p11 48→`deltaX`, deltaX4f_p11 10, deltaY_p11 27, deltaX1f 41, upsX_p11 42, taum_p11 9, EE_p4 3→`EE`). Keep torsor_p4/stableSystem_p4/azimCycle_p4 references (LA4 lane). Its `mkSimplex1_p11` theorems now agree with the corrected canonical `deltaX5`.
16. **LocalAuto12.lean** — NO EDIT (plain-name user only).
17. **LocalAuto13.lean** — NO EDIT (P13 kit intentionally distinct).
18. **LocalAuto14.lean** — DEL `azimCycle_p14`(229-240). REN azimCycle_p14 (20).
19. **LocalAuto15.lean** — NO EDIT.
20. **LocalAuto16.lean** — DEL `atn2_p16`(267-273), `deltaXf_p16`(275-280), `deltaX4f_p16`(282-285), `dihXf_p16`(287-291), `dihY_p16`(293-295), `deltaY_p16`(297-299), `taum_p16`(301-303). REN (dihY_p16 9, taum_p16 6, deltaY_p16 6, dihXf_p16 3, deltaX4f_p16 3). Also delete the stale split comment at 262-265.
21. **LocalAuto17.lean** — NO EDIT (plain `upsX` user, 47 uses, unchanged name).
22. **LocalAuto18.lean** — DEL Section 0 verbatim twins: `deltaX4_p18`(101-105), `deltaY_p18`(107-111), `dihY_p18`(113-120), `EE_p18`(122-124), `azimCycle_p18`(126-134), `rhoNode1_p18`(136-139), `azimInFan_p18`(141-145), `torsor_p18`(147-152), `constraintSystem_p18`(154-162), `stableSystem_p18`(164-171). REN (deltaY_p18 5→`deltaY`, dihY_p18 4, EE_p18 5→`EE`, azimCycle_p18 4, rhoNode1_p18 5, torsor_p18 4, constraintSystem_p18 2, stableSystem_p18 5). Keep `azimInFan` references pointing at SphereKit's (body switches from azimCycle-rendered to sigmaFan-rendered — verify LA18's azimInFan-consuming proofs, §6). Keep torsor_p23 etc. untouched.
23. **LocalAuto19.lean** — DEL `solY_p19`(117-121), `lyP19`(123-124), `const1P19`(126-128), `lnazimP19`(130-132), `taumP19`(134-138), `taumX_p19`(140-143), `quadraticRootPlus_p19`(163-165). REN (taumP19 26→`taum`, deltaY_p18 188→`deltaY`, dihY_p18 6→`dihY`, deltaX4_p18 3→`deltaX4`, solY_p19 4→`solY`, taumX_p19 4→`taumX`, yOfX_p11 1→`yOfX`, quadraticRootPlus_p19 8). Its `delta126x_p19`-kit uses of plain `deltaX` keep working.
24. **LocalAuto20.lean** — NO EDIT.
25. **LocalAuto21.lean** — DEL `deltaX5_p21`(110-115), `deltaX6_p21`(117-121). REN (deltaX5_p21 5, deltaX6_p21 4, dihXf_p16 9→`dihXf`, dihY_p16 1, taum_p16 3→`taum`, taum_p11 1 doc). Keep its LocalAnchors-related verbatim `MainNonlinearTerminalV11_p21` (separate clash, phase 3).
26. **LocalAuto22.lean** — DEL Section 0: `yOfX_p22`(84-87), `atn2_p22`(89-95), `dihXf_p22`(97-101), `dihY_p22`(103-105), `deltaY_p22`(107-109), `taum_p22`(111-114), `deltaX5_p22`(116-121), `deltaX6_p22`(123-127), `delta4Y_p22`(129-131), `num1_p22`(133-137), `dnum1_p22`(139-141), `solY_p22`(146-148). REN (dihXf_p22 20→`dihXf`, dihY_p22 via deltaY_p22 28, taum_p22 18→`taum`, num1_p22 17, dnum1_p22 6, atn2_p22 3→`atn2`, solY_p22 3→`solY`). NOTE: `solY_p22`→`solY` and `taum_p22`→`taum` upgrade LA22's `sorry` stubs to real bodies — its NEEDS-theorems stay sorry-proven; verify no non-sorry proof exploited opacity.
27. **LocalAuto23.lean** — DEL `deltaX4_p23`(108-113), `deltaY_p23`(115-118), `dihY_p23`(120-127), `taum_p23`(129-132). REN (taum_p23 8→`taum`, deltaY_p23 3→`deltaY`, dihY_p23 3→`dihY`, dihY_p11/dihY_p18 doc mentions cleanup, deltaX4_p23 3→`deltaX4`). KEEP `torsor_p23`, `constraintSystem_p23`, `stableSystem_p23`, `StableSyP23` (shape C; phase 3).
28. **LocalAuto24.lean** — REN only (stableSystem_p23 1 doc mention). Otherwise NO EDIT.
29. **LocalAuto25.lean / 26 / 27 / 29 / 30 / 32** — NO EDIT (plain-name users: atn2/arcLength/upsX keep resolving).
30. **LocalAuto28.lean / 33 / 34 / 35 / 36 / 37** — NO EDIT except **LA33**: REN `dihY_p18` (2) → `dihY`; **LA36**: REN `stableSystem_p23` mentions stay; plain `taum` mention is a comment. **LA38**: DEL stubs `taumXP38`(96-98), `delta4YP38`(125-126), `yOfXP38`(128-131), `quadraticRootPlusP38`(133-136), `dihXP38`(117-119); REN their uses (9/2/1/9) → `taumX`/`delta4Y`/`yOfX`/`quadraticRootPlus`/`dihXf` (stub→real-body upgrades; same caveat as LA22). KEEP `taudP38`, `taudXP38`, `tauResidualXP38`, `flatTermXP38`, `eulerAXP38`, `cayleyRP38`, `cayleytrP38`, `tauqP38` (unported kit, no canonical yet). REN azimCycle_p18 (2)→`azimCycle`, taum_p23 (17)→`taum`, deltaY_p23 (20)→`deltaY`, dihY_p23 (4)→`dihY`, deltaX4_p23 (9)→`deltaX4`.
31. **LocalAuto31.lean** — NO EDIT.
32. **LocalAnchors.lean** — NO EDIT (zero importers; phase-3: `scsBasicV39`/`MainNonlinearTerminalV11` clash with LA1/LA21 lanes noted in §6).
33. **All remaining files — NO EDIT, verified**: AffGtCut, ConformingAuto1-23, ConformingDefs, Fan, Hypermap, Planarity.lean, PlanarityAngle, PlanarityAuto6-15, PlanarityComponent, PlanarityConnect, PlanarityDarts, PlanarityNotCut, PolyAuto1-7, Polytope, TestSgn18, TopologyFan, VectorAngleLemmas, PackingAuto1-17, PackingAuto19, PackingAuto22, PackingAuto23, PackingAuto24 (grep-checked: no kit defs, no kit-twin tokens, no kit-root imports; PA19/PA22 merely import PA18 and keep working unchanged).

---

## 6. Risk list

1. **Name collisions at merge time.**
   * `MCELL2_SUBSET_AFF_GE`: PA18:1056 (no hypotheses, `sorry`, `hdV/tail` form) vs PA21:821 (proved, `elV` form, extra `Packing/saturated/barV` hypotheses). Statements differ — PA21's copy is renamed `_p21` in wave 2; do NOT "dedupe" them.
   * `HJKDESR1a_1cell`: byte-identical in PA20:241/PA21:628 — safe to keep only PA20's.
   * After PA21 imports PA20, re-run the overlap check: expected residual ∩ = ∅.
   * `atn2`: three copies must be deleted in the same wave that SphereKit lands, or modules briefly see zero/`_pNN` only.
   * `upsX`: SphereKit's is the sphere.hl Gram form; LA6's `upsX_p6` is a *different function* — never rename it to `upsX`.
   * `ee`→`EE` rename inside LA1 must land in the same commit as the LA1 localization deletions, else `azimInFan` (SphereKit) vs local `ee` mismatches.
   * LA3 must gain the explicit SphereKit import before its `EE_p3`/`azimCycle_p3` deletions, or LA5/LA6/LA10 lose the name entirely (LA5/LA6 import LA3 without any kit root).
2. **DISCHARGES/NEEDS markers referencing twins.** Many doc-comments name the twins (`NEEDS: merge`, “verbatim twin of …”): LA11:123-126, LA16:262-267, LA18:99/102/107/113/122/126/136/141/147, LA19:117/126, LA21:110-112, LA22:82/89/111/116, LA23:108/115/120/129/134, LA2:78-80/183/189/199, LA6:60-62, LA7:121-124, LA14:229-233, PA21:102-103/105-160. Executing workers must update/delete these markers (a stale “twin of X” comment pointing at a deleted def is documentation rot; grep `NEEDS-merge\|NEEDS: merge\|verbatim twin\|verbatim cop` after each wave).
3. **Statement-shape / body drift found while diffing twins.**
   * `deltaX5` (LA1:772) mis-port — §2.1; fixes `mkSimplex1`'s value. Any theorem whose *statement* encodes mkSimplex1's numeric output must be re-derived (LA1:1032 onward).
   * `solY_p22`/`taum_p22`/`taum_p11/16/23`/`delta4YP38`/`taumXP38`/`dihXP38` are `sorry` stubs whose canonical replacements have real bodies: renames silently change the described function (intended, but every proof that leaned on opacity must be rechecked; statements themselves are unchanged signatures).
   * `azimInFan`: LA1/SphereKit body is `sigmaFan`-rendered; `_p2/_p3/_p4/_p18` are `EE`+`azimCycle`-rendered. Not syntactically equal ⇒ twins stay; a phase-3 bridge lemma (`azimInFan = azimInFan_pN` under `FAN 0 V E`) is required before deleting them. Same for `azimCycleP13` (different junk/`≤`/arg-order semantics — genuinely different, likely a wrong port to reconcile separately).
   * `ly_p2` (`interp_p2` form) vs `ly` (inlined): propositionally equal, syntactically different — LA2's `lmfun`/`ly_p2` lemma (LA2:450) depends on the `interp_p2` unfolding; do not rename in pass 1.
   * `StableSy` (LA8, `d : ℕ`) vs `StableSyP23` (LA23, `d : ℝ`): NOT twins despite identical field names.
   * `torsor_p4` (generic `Finset α`, `s.card`) vs `torsor_p8` (generic `Set α`, `Nat.card`): cardinality operation differs; do not cross-rename.
   * `const1_p2`/`const1P19` are formula-identical; LA19:126's “wrong atn2 side” remark is stale (both sides use verbatim-identical `solY`/`atn2` bodies) — delete the remark, no value change.
   * PA18's kit neighbors (`deltaP`, `upsX`, `arcLength`) vs PA20's naming (`deltaXf`): the canonical-name choice `deltaX`/`deltaX4` follows the LocalAuto1 lane (largest user base); every `deltaXf`/`deltaX4f` occurrence (PA20/21/25, LA2, LA11, LA16) must be renamed in the same wave as the PA20/PA21 def deletions, or those files won't compile.
4. **Heartbeat/perf**: SphereKit is small, but LA19 carries 188 `deltaY_p18` renames and LA5/LA6 carry 200+ `rhoNode1_p2` renames — pure renames don't change elaboration, but the LA22/LA38 stub→real-body upgrades replace `sorry` with real `solY`/`taum` unfolding; watch `maxHeartbeats` in files with heavy `simp [taum_p22]`-style proofs.
5. **Ordering deadlock**: do not delete a twin before its file can see the canonical name (transitively or via the explicit LA3 import). The wave order in §7 guarantees this; running waves out of order will produce “unknown constant” errors, not silent wrongness.

---

## 7. Ordering plan and verification recipe

Order (each wave = one commit, compiling cleanly before the next):

* **W0** — add `SphereKit.lean` (§3). Nothing imports it yet; compile the module alone.
* **W1** — PA18, PA20 (edit map items 1-2). After W1, PA18 and PA20 are co-importable for the first time.
* **W2** — PA21, PA25 (items 3-4). After W2, the PA21/PA25 lane and the PA18 lane are co-importable.
* **W3** — LA3 (item 7, with explicit SphereKit import), then the LA2 lane: LA2, LA5, LA6, LA9, LA11 (items 6, 9, 10, 13, 15).
* **W4** — LA7, LA14 (items 11, 18).
* **W5** — LA1 (item 5; includes the deltaX5 fix), then LA16, LA18, LA19, LA21, LA22, LA23, LA33, LA38 (items 20, 22, 23, 25, 26, 27, 30, 31).
* **W6** — sweep: `grep -rn "_p11\|_p16\|_p18\|_p19\|_p21\|_p22\|_p23\|P38\|P25\|deltaXf\|deltaX4f" lean/Kepler/Text` and delete/redirect the remaining sphere/localization-kit hits (docs + stale markers); leave the intentionally-kept twins of §3.

Verification recipe (per wave and final):

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/scroll/repos/kepler-conjecture-lean4/lean
# 1. cold traces for touched modules (no stale olean reuse)
find .lake/build -name '*SphereKit*' -o -name '*PackingAuto1[89]*' -o -name '*PackingAuto2[015]*' \
  -o -name '*PackingAuto25*' -o -name '*LocalAuto*' | xargs -r rm -f
# 2. compile the whole root (Kepler.lean imports Statement/Geom/...; Text modules compile
#    through their dependents — if Kepler.lean does not reach a Text lane, use a probe file)
lake build
# 3. dual-family probe: BOTH roots together (the assertion this whole plan exists for)
cat > ProbeMerge.lean <<'EOF'
import Kepler.Text.PackingAuto18      -- family A root (PA18 lane)
import Kepler.Text.PackingAuto20      -- family B root (PA20 = PA21 kit)
import Kepler.Text.PackingAuto21      -- family B hub (now imports PA20)
import Kepler.Text.PackingAuto25      -- family B consumer
import Kepler.Text.LocalAuto16        -- A lane (was PA18-only)
import Kepler.Text.LocalAuto11        -- B lane (was PA20-only)
import Kepler.Text.LocalAuto22        -- A lane heavy kit user
#print axioms Kepler.Text.taum
example (x y : ℝ) : Kepler.Text.deltaY x x x x x x = Kepler.Text.deltaX (x*x) (x*x) (x*x) (x*x) (x*x) (x*x) := rfl
EOF
lake env lean ProbeMerge.lean    # expect: no duplicate-declaration errors, exit 0
# 4. twin-free sweep
grep -rn "atn2_p\|dihY_p1\|dihY_p2\|deltaY_p\|deltaX4_p\|deltaX5_p\|deltaX6_p\|taum_p1\|taum_p2\|EE_p[0-9]\|azimCycle_p[0-9]\|rhoNode1_p\|ivsRhoNode1_p2\|interiorAngle1_p2\|torsor_p9\|torsor_p18\|stableSystem_p9\|stableSystem_p18\|deltaXf\b\|deltaX4f\b" Kepler/Text | grep -v '^Binary'
#    expected: only the intentionally-kept names listed in §3.
```

(Existing scratch probes `Probe20.lean`/`Probe25.lean` at `lean/` are single-family; keep or
delete them independently — this plan does not depend on them.)
