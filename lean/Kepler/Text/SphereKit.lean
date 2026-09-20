/-
Kepler.Text.SphereKit — single home of the sphere.hl numeric kit, deduplicated
from the PackingAuto18/20/21 hub split and the `_pNN` verbatim twins
(docs/atn2-merge-plan.md, §1.2/§2).  Wave-1 subset: the numeric family only
(`atn2`, the `delta_x` family, `dih_x`/`dih_y`/`sol_y`, `ups_x`, the
Terminal.hl tau kit, `num1`/`dnum1`) plus the localization.hl syntactic-twin
core (`EE`, `azimCycle` — verbatim over their `_p2/_p3/_p7/_p14/_p18`
twins).  Still DEFERRED (plan §6): `azimInFan`/`rhoNode1`/`ivsRhoNode1`/
`interiorAngle1` (their `_pNN` twins are not syntactic — `sigmaFan` vs
`EE`+`azimCycle` renderings — and LocalAuto1 still owns the unsuffixed
names) and the dih2k.hl torsor/constraint/stable systems.  Do NOT import
PackingAuto18/20/21 here — that would re-create the fatal `atn2` clash this
module exists to remove.  `PackingAuto5` is imported for `projection`
(azimCycle's tiebreak); every current downstream module already imports it.

Body provenance: every body is verbatim from the surveyed variant named in
its docstring; the whole family was mechanically diffed for the plan
(§1.2: verbatim-equal unless flagged).  The one flagged drift, `deltaX5`,
carries the CORRECTED 6-term body below (LocalAuto1.lean:772 was a mis-port).
-/

import Kepler.Geom.Azim
import Kepler.Text.PackingAuto5
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom

/-! ## sphere.hl: two-argument arctangent and the `delta_x` family -/

/-- HOL `atn2` (sphere.hl:48-52). Verbatim = PackingAuto18.lean:154 =
PackingAuto20.lean:66 = PackingAuto21.lean:106; `atn2 x y = Real.atan2 y x`
off the degenerate `(0,0)`-with-`x ≤ 0` corner. -/
noncomputable def atn2 (x y : ℝ) : ℝ :=
  if |y| < x then Real.arctan (y / x)
  else if 0 < y then Real.pi / 2 - Real.arctan (x / y)
  else if y < 0 then -(Real.pi / 2) - Real.arctan (x / y)
  else Real.pi

/-- HOL `delta_x` (sphere.hl:86-90). Verbatim = PackingAuto18.lean:134
(`deltaX`) = PackingAuto20.lean:73 (`deltaXf`). Canonical name follows the
LocalAuto1 lane (largest user base). -/
def deltaX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6) +
    x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6) +
    x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) -
    x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6

/-- HOL `delta` (collect_geom.hl:94-100): the Cayley–Menger style
determinant on edge-squared entries. Verbatim = PackingAuto18.lean:142 (only
copy; moved here so the PA18/PA20/PA21 lanes can share one kit). -/
def deltaP (x12 x13 x14 x23 x24 x34 : ℝ) : ℝ :=
  -(x12 * x13 * x23) - x12 * x14 * x24 - x13 * x14 * x34 - x23 * x24 * x34 +
    x12 * x34 * (-x12 + x13 + x14 + x23 + x24 - x34) +
    x13 * x24 * (x12 - x13 + x14 + x23 - x24 + x34) +
    x14 * x23 * (x12 + x13 - x14 - x23 + x24 + x34)

/-- HOL `chi_msb` (leaf_cell.hl:781-782): the signed volume functional of the
ordered triple `ul` at `p`. Verbatim = PackingAuto18.lean:91 =
PackingAuto25.lean:134. -/
noncomputable def chiMsb (ul : List V3) (p : V3) : ℝ :=
  (crossProduct ((ul[1]! - ul[0]! : V3) : Fin 3 → ℝ)
      ((ul[2]! - ul[0]! : V3) : Fin 3 → ℝ)) ⬝ᵥ ((p - ul[0]! : V3) : Fin 3 → ℝ)

/-- HOL `ups_x` (sphere.hl:122-124): the Gram-form minor. Verbatim =
PackingAuto18.lean:149 = PackingAuto25.lean:170 (upsX twins). NB: LocalAuto6
`upsX_p6` is a DIFFERENT HOL function (packing_defs `ups_x`) and stays there
(plan §3). -/
def upsX (x1 x2 x6 : ℝ) : ℝ :=
  -(x1 * x1) - x2 * x2 - x6 * x6 + 2 * x1 * x6 + 2 * x1 * x2 + 2 * x2 * x6

/-- HOL `delta_x4` (sphere.hl:110): partial of `delta_x` at `x4`. Verbatim =
LocalAuto1.lean:766 = PackingAuto20.lean:80 (`deltaX4f`) = the `deltaX4_pNN`
twins. -/
noncomputable def deltaX4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6 +
    x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

/-- HOL `delta_x5` (sphere.hl; Nonlin_def.hl:435): partial of `delta_x` at
`x5`. CORRECTED 6-term body = LocalAuto21.lean:113 (`deltaX5_p21`) =
LocalAuto22.lean:120 (`deltaX5_p22`) = LocalAuto11.lean:165
(`deltaX5f_p11`); independently verified as `∂deltaX/∂x5` (plan §2.1).
LocalAuto1.lean:772 was a mis-port dropping `- x1 * x3 + x1 * x4` — fixed
there 2026-09-17 against this body. -/
noncomputable def deltaX5 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x1 * x3 + x1 * x4 - x2 * x5 + x3 * x6 - x4 * x6 +
    x2 * (x1 - x2 + x3 + x4 - x5 + x6)

/-! ## sphere.hl: dihedral angles and spherical excess -/

/-- HOL `dih_x` (sphere.hl:153): dihedral angle from squared lengths.
Verbatim = PackingAuto20.lean:85 = the `dihXf_p11/_p16/_p22` twins. -/
noncomputable def dihXf (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 + atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
    (-(deltaX4 x1 x2 x3 x4 x5 x6))

/-- HOL `dih_y` (sphere.hl:159): `dih_x` at squared lengths. Verbatim =
PackingAuto20.lean:90 ≡ the `dihY_p11/_p16/_p18/_p23` twins (the latter two
inlined). -/
noncomputable def dihY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `sol_y` (sphere.hl:185): spherical excess `α + β + γ - π`. Verbatim =
PackingAuto20.lean:94 = PackingAuto21.lean:134 = `solY_p19` (LocalAuto19:119);
upgrades LocalAuto22's `sorry` stub `solY_p22` to the real body. -/
noncomputable def solY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  dihY y1 y2 y3 y4 y5 y6 + dihY y2 y3 y1 y5 y6 y4 + dihY y3 y1 y2 y6 y4 y5 -
    Real.pi

/-! ## sphere.hl: y-space family and the root helper -/

/-- HOL `y_of_x` (sphere.hl): rescale a symmetric x-space function to
y-coordinates. Verbatim = LocalAuto22.lean:84 (`yOfX_p22`) = LocalAuto11:177
(`yOfX_p11`). -/
def yOfX (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  f (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `delta_y` (sphere.hl): `y_of_x delta_x`. Body = `deltaY_p11` (LA11:149)
= `deltaY_p16/_p18/_p22/_p23` = `deltaYP25` (PA25:98) — all `deltaX` at
squared lengths (no unsuffixed def existed before this module). -/
noncomputable def deltaY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `delta4_y` (sphere.hl): `y_of_x delta_x4`. Verbatim = `delta4Y_p11`
(LA11:188) = `delta4Y_p22` (LA22:129); upgrades LocalAuto38's `sorry` stub
`delta4YP38` to the real body. -/
noncomputable def delta4Y (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  yOfX (deltaX4) y1 y2 y3 y4 y5 y6

/-- HOL `quadratic_root_plus` (sphere.hl:67): the larger root of
`a*z^2 + b*z + c = 0`. Verbatim = `quadraticRootPlus_p11` (LA11:154) =
`_p19` (LA19:164, `b*b` spelling) = `P38` (LA38:135). -/
noncomputable def quadraticRootPlus (a b c : ℝ) : ℝ :=
  (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)

/-! ## Terminal.hl: num1/dnum1 and the truncated tau kit -/

/-- HOL `num1` (Terminal.hl, body reconstructed from its uses). Verbatim =
`num1_p22` (LocalAuto22.lean:136, the only copy). -/
noncomputable def num1 (e1 e2 e3 x4 x5 x6 : ℝ) : ℝ :=
  4 * ((16 * x4 - x4 * x4) * e1 + (x5 - 8) * x4 * e2 + (x6 - 8) * x4 * e3)

/-- HOL `dnum1` (Terminal.hl, reconstructed; derivative of `num1`). Verbatim =
`dnum1_p22` (LocalAuto22.lean:140, the only copy). -/
noncomputable def dnum1 (e1 e2 e3 x4 x5 x6 : ℝ) : ℝ :=
  (16 - 2 * x4) * e1 + (x5 - 8) * e2 + (x6 - 8) * e3

/-- HOL `ly` (sphere.hl:199): `interp 2 1 2.52 0 y`. Verbatim = `lyP19`
(LocalAuto19.lean:124). NB LocalAuto2's `ly_p2` keeps the `interp_p2`
rendering (propositionally equal; plan §6 — not merged in this pass). -/
noncomputable def ly (y : ℝ) : ℝ := 1 + (y - 2) * (0 - 1) / (2.52 - 2)

/-- HOL `const1` (sphere.hl:197) = `solY 2 2 2 2 2 2 / π`. Formula = `const1_p2`
(LA2:333) = `const1P19` (LA19:128); the LA19:126 "wrong atn2 side" remark is
stale (plan §6: both sides use verbatim-identical `solY`/`atn2`). -/
noncomputable def const1 : ℝ := solY 2 2 2 2 2 2 / Real.pi

/-- HOL `lnazim` (sphere.hl:214). Verbatim = `lnazimP19` (LocalAuto19:130). -/
noncomputable def lnazim (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  ly y1 * dihY y1 y2 y3 y4 y5 y6

/-- HOL `taum` (sphere.hl:215): the truncated tau of a quad. Body =
`taumP19` (LocalAuto19.lean:135) — the only real body in the corpus; replaces
the opaque `sorry` stubs `taum_p11`/`taum_p16`/`taum_p22`/`taum_p23` at their
use sites in later waves. -/
noncomputable def taum (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  solY y1 y2 y3 y4 y5 y6 * (1 + const1) -
    const1 * (lnazim y1 y2 y3 y4 y5 y6 +
      lnazim y2 y3 y1 y5 y6 y4 + lnazim y3 y1 y2 y6 y4 y5)

/-! ## localization.hl: `EE` and `azim_cycle` (syntactic-twin core)

The two localization-kit names whose `_pNN` twins are byte-identical across
lanes.  Still deferred here (plan §6): `azimInFan` (its `sigmaFan`-rendered
LA1/LA13 body and the `EE`+`azimCycle`-rendered `azimInFan_p2/_p3/_p4/_p18`
bodies are not syntactically equal — a `FAN`-conditional bridge lemma is
needed first, and LocalAuto1 currently owns the unsuffixed name), and
`rhoNode1`/`ivsRhoNode1`/`interiorAngle1` (unsuffixed names still owned by
LocalAuto1; bodies are the trivial `Classical.epsilon` forms). -/

open Classical

/-- HOL `EE v S = {w | {v,w} ∈ S}` (localization.hl:38; also
WRGCVDR.hl:95): the `S`-neighbours of `v`.  Verbatim = `EE_p2`
(LocalAuto2.lean:126) = `EE_p3` (LocalAuto3.lean:132) = `EE_p18`
(LocalAuto18.lean:117) — the α-generic majority.  V3-monomorphic same-body
variants: `ee` (LA1:90), `EE_p4` (LA4:758), `eeP13` (LA13:96, separate
lane). -/
def EE {α : Type*} (v : α) (S : Set (Set α)) : Set α := {w | {v, w} ∈ S}

/-- HOL `azim_cycle` (sphere.hl:414): the azimuthal successor of `p` around
the axis `(v, w)` within `W` — least azimuth, `‖projection ‖`-distance
tiebreak, `p` itself on the degenerate `W ⊆ {p}`.  Verbatim =
`azimCycle_p2` (LA2:91) = `_p3` (LA3:104) = `_p7` (LA7:128) = `_p14`
(LA14:234) = `_p18` (LA18:121); `azimCycle_p4` (LA4:764) is the same body
modulo binder names.  NOT a twin: `azimCycleP13` (LA13:115 — different junk
value, `≤`-tiebreak, argument order; plan §3 keeps it separate).  HOL
`projection (w-v) (u-v)` ↔ repo `projection (u - v) (w - v)`. -/
noncomputable def azimCycle (W : Set V3) (v w p : V3) : V3 :=
  if W ⊆ {p} then p
  else
    Classical.epsilon fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖

end Kepler.Text
