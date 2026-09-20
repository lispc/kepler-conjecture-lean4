/-
FQN conflict governance regression probe (docs/fqn-conflicts.md, 2026-09-20,
branch wip/pa-conflict-fix).

Before the governance, this import set failed at import time:
  `environment already contains 'Kepler.Text.deltaP' from ...`
because SphereKit / PackingAuto18 / PackingAuto20 / PackingAuto21 exported
duplicate FQNs (`atn2`, `deltaX`, `deltaP`, `chiMsb`, `upsX`, `dihXf`,
`dihY`, `solY`, ...).  After the rename-with-suffix governance the five
modules co-import cleanly; the `#check`s below pin both the canonical names
(SphereKit / PackingAuto7 / PackingAuto20 / PackingAuto21 side) and the
renamed `PA18`/`PA20`/`PA21`-suffixed copies.

Not wired into the library; compile via the worktree overlay:
  LEAN_PATH=.build/lib:<deps> lean lean/scripts/CoImportProbe.lean
-/
import Kepler.Text.SphereKit
import Kepler.Text.PackingAuto18
import Kepler.Text.PackingAuto20
import Kepler.Text.PackingAuto21
import Kepler.Text.IneqClosureDefs

open Kepler.Text

-- Canonical (SphereKit) side: unique resolution after governance.
#check @atn2
#check @deltaX
#check @deltaP
#check @chiMsb
#check @upsX
#check @dihXf
#check @dihY
#check @solY
-- PackingAuto7 canonical (vs PackingAuto6's renamed stubs).
#check @ANGLE_GT_PI2
#check @ARCV_GT_PI2
#check @AZIM_COMPL_EXT
#check @AZIM_EQ_SYM
-- PackingAuto20 canonical hub kit (vs PackingAuto21's renamed twins).
#check @deltaXf
#check @deltaX4f
#check @volXf
#check @volY
#check @vol3r
#check @vol3f
#check @gamma3f
#check @HJKDESR1a_1cell
-- PackingAuto21 canonical (proved; vs PackingAuto18's renamed stub).
#check @MCELL2_SUBSET_AFF_GE
-- Renamed copies still exist and are usable.
#check @atn2PA18
#check @chiMsbPA18
#check @deltaPPA18
#check @deltaXPA18
#check @upsXPA18
#check @MCELL2_SUBSET_AFF_GE_PA18
#check @atn2PA20
#check @dihXfPA20
#check @dihYPA20
#check @solYPA20
#check @atn2PA21
#check @dihYPA21
#check @solYPA21
#check @gamma3fPA21
#check @HJKDESR1a_1cell_PA21

-- Axiom spot checks: renamed defs must not have gained `sorryAx`;
-- proved theorems keep their axiom profile.
#print axioms Kepler.Text.solY
#print axioms Kepler.Text.dihXf
#print axioms Kepler.Text.ANGLE_GT_PI2
#print axioms Kepler.Text.ATN2_Y_NEG
#print axioms Kepler.Text.MCELL2_SUBSET_AFF_GE
#print axioms Kepler.Text.solX
