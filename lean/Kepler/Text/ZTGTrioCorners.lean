/-
Kepler.Text.ZTGTrioCorners — lane `ztg-joint6-trio-w1`, M3: the 36 corner-value certificates `0 < ztgMain 1 0 0 0 c1..c6` of the W1 trio base debt, plus the Klein-4 atom-to-representative transfer lemmas of the corner alphabet.

Machine-generated (`trio_gen_corners.py`); envelopes self-verified at three
`hminus` samples; branch-1 and Taylor feasibility checked per bracket; every
declaration axiom-audited; no `sorry`/`axiom`/`native_decide`.
-/
import Kepler.Text.ZTGTrioCornerTHMc
import Kepler.Text.ZTGTrioCornerTHMb
import Kepler.Text.ZTGTrioCornerTHMa
import Kepler.Text.ZTGTrioCornerTR
import Kepler.Text.Gamma4ValCornerKit
import Kepler.Text.ZTGTrioSym

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route


/-! ## Atom-to-representative transfers -/

theorem ztgcTrio_eq0 : dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 = dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq1 : dihY (2 * hminus) (2 * hminus) (2 * hminus) (Real.sqrt 8) 2 2 = dihY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq2 : dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 = dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq3 : dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2.52 2 = dihY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq4 : dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 = dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq5 : dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2.52 = dihY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq6 : dihY (2 * hminus) (2 * hminus) 2.52 2 (2 * hminus) 2 = dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq7 : dihY (2 * hminus) (2 * hminus) 2.52 2 2.52 2 = dihY (2 * hminus) 2 2.52 2 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq8 : dihY (2 * hminus) (2 * hminus) 2.52 2 (Real.sqrt 8) 2 = dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq9 : dihY (2 * hminus) (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 = dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq10 : dihY (2 * hminus) (2 * hminus) (2 * hplus) 2 2.52 2 = dihY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq11 : dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 = dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq12 : dihY (2 * hminus) (2 * hminus) 2 2.52 2 2 = dihY (2 * hminus) 2 (2 * hminus) 2.52 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq13 : dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) = dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq14 : dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2.52 = dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq15 : dihY (2 * hminus) (2 * hminus) 2 2 2 2.52 = dihY (2 * hminus) 2.52 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq16 : dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hplus) = dihY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq17 : dihY (2 * hminus) (2 * hminus) 2 2 2 (Real.sqrt 8) = dihY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq18 : dihY (2 * hminus) (2 * hminus) 2 2 2 2 = dihY (2 * hminus) 2 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq19 : dihY (2 * hminus) 2.52 (2 * hminus) 2.52 2 2 = dihY (2 * hminus) 2 2 2.52 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq20 : dihY (2 * hminus) 2.52 (2 * hminus) (Real.sqrt 8) 2 2 = dihY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq21 : dihY (2 * hminus) 2.52 (2 * hminus) 2 2 2.52 = dihY (2 * hminus) 2 2.52 2 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq22 : dihY (2 * hminus) 2.52 2 (2 * hminus) 2 2 = dihY (2 * hminus) 2 2 (2 * hminus) 2.52 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq23 : dihY (2 * hminus) 2.52 2 2.52 2 2 = dihY (2 * hminus) 2 2 2.52 2.52 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq24 : dihY (2 * hminus) 2.52 2 2 (2 * hminus) 2.52 = dihY (2 * hminus) 2 2.52 2 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq25 : dihY (2 * hminus) 2.52 2 2 2 2.52 = dihY (2 * hminus) 2 2.52 2 2.52 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq26 : dihY (2 * hminus) 2.52 2 2 2 (2 * hplus) = dihY (2 * hminus) 2 (2 * hplus) 2 2.52 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq27 : dihY (2 * hminus) 2.52 2 2 2 (Real.sqrt 8) = dihY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq28 : dihY (2 * hminus) 2.52 2 2 2 2 = dihY (2 * hminus) 2 2 2 2.52 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq29 : dihY (2 * hminus) (2 * hplus) (2 * hminus) 2.52 2 2 = dihY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq30 : dihY (2 * hminus) (2 * hplus) (2 * hminus) (Real.sqrt 8) 2 2 = dihY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq31 : dihY (2 * hminus) (2 * hplus) (2 * hminus) 2 2 (2 * hminus) = dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq32 : dihY (2 * hminus) (2 * hplus) (2 * hminus) 2 2 2.52 = dihY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq33 : dihY (2 * hminus) (2 * hplus) (2 * hminus) 2 2 (Real.sqrt 8) = dihY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq34 : dihY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 2 = dihY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq35 : dihY (2 * hminus) (2 * hplus) 2 2.52 2 2 = dihY (2 * hminus) 2 2 2.52 2 (2 * hplus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq36 : dihY (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2 2 = dihY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq37 : dihY (2 * hminus) (2 * hplus) 2 2 2 2.52 = dihY (2 * hminus) 2 (2 * hplus) 2 2.52 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq38 : dihY (2 * hminus) (2 * hplus) 2 2 2 (Real.sqrt 8) = dihY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq39 : dihY (2 * hminus) (Real.sqrt 8) 2 2 (2 * hminus) (2 * hminus) = dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq40 : dihY (2 * hminus) (Real.sqrt 8) 2 2 (2 * hminus) 2.52 = dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq41 : dihY (2 * hminus) (Real.sqrt 8) 2 2 (2 * hminus) (2 * hplus) = dihY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq42 : dihY (2 * hminus) (Real.sqrt 8) 2 2 2 (2 * hminus) = dihY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq43 : dihY (2 * hminus) (Real.sqrt 8) 2 2 2 2.52 = dihY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq44 : dihY (2 * hminus) (Real.sqrt 8) 2 2 2 (2 * hplus) = dihY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq45 : dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 = dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq46 : dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2.52 2 = dihY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq47 : dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 = dihY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq48 : dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) = dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq49 : dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 = dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq50 : dihY (2 * hminus) 2 (2 * hminus) 2 2.52 2 = dihY (2 * hminus) 2.52 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq51 : dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hplus) 2 = dihY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq52 : dihY (2 * hminus) 2 (2 * hminus) 2 2 2.52 = dihY (2 * hminus) (2 * hminus) 2 2 2.52 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq53 : dihY (2 * hminus) 2 (2 * hminus) 2 2 (Real.sqrt 8) = dihY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq54 : dihY (2 * hminus) 2 (2 * hminus) 2 2 2 = dihY (2 * hminus) 2 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq55 : dihY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) = dihY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq56 : dihY (2 * hminus) 2 2.52 2 (2 * hminus) 2 = dihY (2 * hminus) 2.52 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq57 : dihY (2 * hminus) 2 2.52 2 2 (2 * hminus) = dihY (2 * hminus) (2 * hminus) 2 2 2.52 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq58 : dihY (2 * hminus) 2 2.52 2 2 2 = dihY (2 * hminus) 2 2 2 2.52 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq59 : dihY (2 * hminus) 2 (2 * hplus) 2 (2 * hminus) 2 = dihY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq60 : dihY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) = dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq61 : dihY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 = dihY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq62 : dihY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 = dihY (2 * hminus) (Real.sqrt 8) 2 2 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq63 : dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 = dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq64 : dihY (2 * hminus) 2 2 (2 * hminus) 2.52 (2 * hminus) = dihY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq65 : dihY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) (2 * hminus) = dihY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq66 : dihY (2 * hminus) 2 2 2.52 (2 * hminus) (2 * hminus) = dihY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq67 : dihY (2 * hminus) 2 2 2.52 (2 * hminus) 2 = dihY (2 * hminus) 2 (2 * hminus) 2.52 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq68 : dihY (2 * hminus) 2 2 2.52 (2 * hplus) (2 * hminus) = dihY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq69 : dihY (2 * hminus) 2 2 2.52 (2 * hplus) 2 = dihY (2 * hminus) 2 2 2.52 2 (2 * hplus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq70 : dihY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) 2 = dihY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq71 : dihY (2 * hminus) 2 2 (Real.sqrt 8) 2.52 (2 * hminus) = dihY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq72 : dihY (2 * hminus) 2 2 (Real.sqrt 8) 2.52 2 = dihY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq73 : dihY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hplus) (2 * hminus) = dihY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq74 : dihY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hplus) 2 = dihY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq75 : dihY (2 * hminus) 2 2 2 (2 * hminus) 2 = dihY (2 * hminus) 2 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq76 : dihY (2 * hminus) 2 2 2 (2 * hplus) 2 = dihY (2 * hminus) (2 * hplus) 2 2 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq77 : dihY (2 * hminus) 2 2 2 2 2.52 = dihY (2 * hminus) 2 2 2 2.52 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq78 : dihY (2 * hminus) 2 2 2 2 (Real.sqrt 8) = dihY (2 * hminus) (Real.sqrt 8) 2 2 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq79 : dihY 2.52 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) = dihY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq80 : dihY 2.52 (2 * hminus) (2 * hminus) 2 2 2.52 = dihY 2.52 2.52 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq81 : dihY 2.52 (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) = dihY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq82 : dihY 2.52 (2 * hminus) 2 (2 * hminus) 2 2 = dihY 2.52 2 (2 * hminus) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq83 : dihY 2.52 (2 * hminus) 2 2 2 (2 * hminus) = dihY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq84 : dihY 2.52 (2 * hminus) 2 2 2 2.52 = dihY 2.52 2 2.52 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq85 : dihY 2.52 (2 * hminus) 2 2 2 (Real.sqrt 8) = dihY 2.52 (Real.sqrt 8) 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq86 : dihY 2.52 (2 * hminus) 2 2 2 2 = dihY 2.52 2 2 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq87 : dihY 2.52 2.52 2 (2 * hminus) 2 (2 * hminus) = dihY 2.52 2 2.52 (2 * hminus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq88 : dihY 2.52 2.52 2 (2 * hminus) 2 2 = dihY 2.52 2 2 (2 * hminus) 2 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq89 : dihY 2.52 2.52 2 2 2 (2 * hminus) = dihY 2.52 2 2.52 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq90 : dihY 2.52 2.52 2 2 2 2 = dihY 2.52 2 2.52 2 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq91 : dihY 2.52 (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) = dihY 2.52 2 (2 * hplus) (2 * hminus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq92 : dihY 2.52 (2 * hplus) 2 (2 * hminus) 2 2 = dihY 2.52 2 2 (2 * hminus) (2 * hplus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq93 : dihY 2.52 (2 * hplus) 2 2 2 2 = dihY 2.52 2 2 2 (2 * hplus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq94 : dihY 2.52 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 = dihY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq95 : dihY 2.52 2 (2 * hminus) (2 * hminus) 2.52 2 = dihY 2.52 2 2.52 (2 * hminus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq96 : dihY 2.52 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 = dihY 2.52 2 (2 * hplus) (2 * hminus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq97 : dihY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) = dihY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq98 : dihY 2.52 2 (2 * hminus) 2 2.52 2 = dihY 2.52 2 2.52 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq99 : dihY 2.52 2 (2 * hminus) 2 (2 * hplus) 2 = dihY 2.52 (2 * hplus) 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq100 : dihY 2.52 2 (2 * hminus) 2 2 (2 * hminus) = dihY 2.52 (2 * hminus) 2 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq101 : dihY 2.52 2 (2 * hminus) 2 2 2.52 = dihY 2.52 2.52 2 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq102 : dihY 2.52 2 (2 * hminus) 2 2 (Real.sqrt 8) = dihY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq103 : dihY 2.52 2 (2 * hminus) 2 2 2 = dihY 2.52 2 2 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq104 : dihY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) = dihY 2.52 2.52 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq105 : dihY 2.52 2 2.52 2 2 (2 * hminus) = dihY 2.52 2.52 2 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq106 : dihY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 = dihY 2.52 (Real.sqrt 8) 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq107 : dihY 2.52 2 (Real.sqrt 8) 2 2 2 = dihY 2.52 (Real.sqrt 8) 2 2 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq108 : dihY 2.52 2 2 (2 * hminus) (2 * hminus) 2 = dihY 2.52 2 (2 * hminus) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq109 : dihY 2.52 2 2 (2 * hminus) 2.52 2 = dihY 2.52 2 2 (2 * hminus) 2 2.52 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq110 : dihY 2.52 2 2 2 2.52 2 = dihY 2.52 2 2.52 2 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq111 : dihY 2.52 2 2 2 2 (2 * hminus) = dihY 2.52 2 2 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq112 : dihY 2.52 2 2 2 2 2.52 = dihY 2.52 2 2.52 2 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq113 : dihY 2.52 2 2 2 2 (Real.sqrt 8) = dihY 2.52 (Real.sqrt 8) 2 2 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq114 : dihY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) = dihY (2 * hplus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq115 : dihY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 2.52 = dihY (2 * hplus) (2 * hminus) (2 * hminus) 2 2.52 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq116 : dihY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) = dihY (2 * hplus) (Real.sqrt 8) 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq117 : dihY (2 * hplus) (2 * hminus) 2 2 2 2.52 = dihY (2 * hplus) 2 (2 * hminus) 2 2.52 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq118 : dihY (2 * hplus) (2 * hminus) 2 2 2 (Real.sqrt 8) = dihY (2 * hplus) 2 (2 * hminus) 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq119 : dihY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) = dihY (2 * hplus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq120 : dihY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 = dihY (2 * hplus) (2 * hminus) 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq121 : dihY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) = dihY (2 * hplus) (2 * hminus) 2 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq122 : dihY (2 * hplus) 2 (2 * hminus) 2 2 2.52 = dihY (2 * hplus) 2 2.52 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq123 : dihY (2 * hplus) 2 (2 * hminus) 2 2 2 = dihY (2 * hplus) (2 * hminus) 2 2 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq124 : dihY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) = dihY (2 * hplus) (2 * hminus) (2 * hminus) 2 2.52 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq125 : dihY (2 * hplus) 2 2.52 2 (2 * hminus) 2 = dihY (2 * hplus) 2 (2 * hminus) 2 2.52 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq126 : dihY (2 * hplus) 2 2.52 2 2 2 = dihY (2 * hplus) 2 2 2 2.52 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq127 : dihY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) = dihY (2 * hplus) (Real.sqrt 8) 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq128 : dihY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 = dihY (2 * hplus) 2 (2 * hminus) 2 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq129 : dihY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) = dihY (2 * hplus) 2 (2 * hminus) 2 2 (Real.sqrt 8) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq130 : dihY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 = dihY (2 * hplus) (Real.sqrt 8) 2 2 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq131 : dihY (2 * hplus) 2 2 2 2 (2 * hminus) = dihY (2 * hplus) (2 * hminus) 2 2 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq132 : dihY (2 * hplus) 2 2 2 2 2.52 = dihY (2 * hplus) 2 2 2 2.52 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq133 : dihY (2 * hplus) 2 2 2 2 (Real.sqrt 8) = dihY (2 * hplus) (Real.sqrt 8) 2 2 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq134 : dihY (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 2 = dihY (Real.sqrt 8) 2 2 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq135 : dihY (Real.sqrt 8) (2 * hminus) 2 2 2 (2 * hminus) = dihY (Real.sqrt 8) 2 (2 * hminus) 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq136 : dihY (Real.sqrt 8) (2 * hminus) 2 2 2 2 = dihY (Real.sqrt 8) 2 2 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq137 : dihY (Real.sqrt 8) 2.52 2 (2 * hminus) 2 2 = dihY (Real.sqrt 8) 2 2 (2 * hminus) 2.52 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq138 : dihY (Real.sqrt 8) 2.52 2 2 2 (2 * hminus) = dihY (Real.sqrt 8) 2 (2 * hminus) 2 2.52 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq139 : dihY (Real.sqrt 8) 2.52 2 2 2 2 = dihY (Real.sqrt 8) 2 2 2 2.52 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq140 : dihY (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) = dihY (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 (2 * hplus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq141 : dihY (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) 2 2 = dihY (Real.sqrt 8) 2 2 (2 * hminus) 2 (2 * hplus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq142 : dihY (Real.sqrt 8) (2 * hplus) 2 2 2 (2 * hminus) = dihY (Real.sqrt 8) 2 (2 * hminus) 2 (2 * hplus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq143 : dihY (Real.sqrt 8) (2 * hplus) 2 2 2 2 = dihY (Real.sqrt 8) 2 2 2 (2 * hplus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq144 : dihY (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 = dihY (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq145 : dihY (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) 2.52 2 = dihY (Real.sqrt 8) 2.52 2 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq146 : dihY (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 = dihY (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 (2 * hplus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq147 : dihY (Real.sqrt 8) 2 2 (2 * hminus) (2 * hminus) 2 = dihY (Real.sqrt 8) 2 2 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq148 : dihY (Real.sqrt 8) 2 2 (2 * hminus) (2 * hplus) 2 = dihY (Real.sqrt 8) 2 2 (2 * hminus) 2 (2 * hplus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq149 : dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 = dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq150 : dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) = dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq151 : dihY 2 (2 * hminus) (2 * hminus) 2.52 (2 * hminus) 2 = dihY 2 2 (2 * hminus) 2.52 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq152 : dihY 2 (2 * hminus) (2 * hminus) 2.52 2 (2 * hminus) = dihY 2 2 (2 * hminus) 2.52 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq153 : dihY 2 (2 * hminus) (2 * hminus) 2.52 2 2 = dihY 2 2 2 2.52 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq154 : dihY 2 (2 * hminus) (2 * hminus) (2 * hplus) (2 * hminus) 2 = dihY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq155 : dihY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 (2 * hminus) = dihY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq156 : dihY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 2 = dihY 2 2 2 (2 * hplus) (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq157 : dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 = dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq158 : dihY 2 (2 * hminus) (2 * hminus) 2 2.52 2 = dihY 2 2.52 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq159 : dihY 2 (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 = dihY 2 (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq160 : dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) = dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq161 : dihY 2 (2 * hminus) (2 * hminus) 2 2 2.52 = dihY 2 2.52 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq162 : dihY 2 (2 * hminus) (2 * hminus) 2 2 2 = dihY 2 2 2 2 (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq163 : dihY 2 (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 = dihY 2 2 (2 * hminus) (2 * hminus) 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq164 : dihY 2 (2 * hminus) 2.52 (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq165 : dihY 2 (2 * hminus) 2.52 2.52 2 (2 * hminus) = dihY 2 (2 * hminus) 2 2.52 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq166 : dihY 2 (2 * hminus) 2.52 2.52 2 2 = dihY 2 2 2 2.52 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq167 : dihY 2 (2 * hminus) 2.52 (2 * hplus) 2 2 = dihY 2 2 2 (2 * hplus) (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq168 : dihY 2 (2 * hminus) 2.52 2 (Real.sqrt 8) 2 = dihY 2 2 (Real.sqrt 8) 2 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq169 : dihY 2 (2 * hminus) 2.52 2 2 2 = dihY 2 2 2 2 (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq170 : dihY 2 (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 = dihY 2 (2 * hplus) (2 * hminus) (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq171 : dihY 2 (2 * hminus) (2 * hplus) (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq172 : dihY 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 = dihY 2 2 (2 * hminus) 2 (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq173 : dihY 2 (2 * hminus) (2 * hplus) 2 2.52 2 = dihY 2 2 2.52 2 (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq174 : dihY 2 (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2 = dihY 2 (Real.sqrt 8) 2 2 (2 * hminus) (2 * hplus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq175 : dihY 2 (2 * hminus) (2 * hplus) 2 2 2 = dihY 2 2 2 2 (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq176 : dihY 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) = dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq177 : dihY 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq178 : dihY 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) = dihY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq179 : dihY 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) 2 2 = dihY 2 2 2 (2 * hplus) (Real.sqrt 8) (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq180 : dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) = dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq181 : dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2.52 = dihY 2 2 (2 * hminus) (2 * hminus) 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq182 : dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hplus) = dihY 2 (2 * hplus) (2 * hminus) (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq183 : dihY 2 (2 * hminus) 2 (2 * hminus) 2.52 (2 * hminus) = dihY 2 (2 * hminus) 2.52 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq184 : dihY 2 (2 * hminus) 2 (2 * hminus) 2.52 2.52 = dihY 2 2.52 2.52 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq185 : dihY 2 (2 * hminus) 2 (2 * hminus) 2.52 (2 * hplus) = dihY 2 2 (2 * hminus) (2 * hminus) (2 * hplus) 2.52 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq186 : dihY 2 (2 * hminus) 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) = dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq187 : dihY 2 (2 * hminus) 2 (2 * hminus) (Real.sqrt 8) 2.52 = dihY 2 2.52 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq188 : dihY 2 (2 * hminus) 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) = dihY 2 2 (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq189 : dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 = dihY 2 2 (2 * hminus) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq190 : dihY 2 (2 * hminus) 2 2.52 (2 * hminus) 2 = dihY 2 2 (2 * hminus) 2.52 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq191 : dihY 2 (2 * hminus) 2 2.52 2 2 = dihY 2 2 2 2.52 (2 * hminus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq192 : dihY 2 (2 * hminus) 2 (2 * hplus) 2 2 = dihY 2 2 2 (2 * hplus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq193 : dihY 2 (2 * hminus) 2 (Real.sqrt 8) 2 2 = dihY 2 2 (2 * hminus) (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq194 : dihY 2 (2 * hminus) 2 2 (2 * hminus) 2.52 = dihY 2 (2 * hminus) 2.52 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq195 : dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hplus) = dihY 2 2 (2 * hminus) 2 (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq196 : dihY 2 (2 * hminus) 2 2 2.52 (2 * hminus) = dihY 2 2 (2 * hminus) 2 (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq197 : dihY 2 (2 * hminus) 2 2 2.52 2.52 = dihY 2 2.52 2.52 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq198 : dihY 2 (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) = dihY 2 2 (2 * hminus) 2 (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq199 : dihY 2 (2 * hminus) 2 2 (Real.sqrt 8) 2.52 = dihY 2 2.52 (Real.sqrt 8) 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq200 : dihY 2 (2 * hminus) 2 2 (Real.sqrt 8) (2 * hplus) = dihY 2 2 (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq201 : dihY 2 (2 * hminus) 2 2 2 (2 * hminus) = dihY 2 2 (2 * hminus) 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq202 : dihY 2 (2 * hminus) 2 2 2 2.52 = dihY 2 2 (2 * hminus) 2 2.52 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq203 : dihY 2 (2 * hminus) 2 2 2 (2 * hplus) = dihY 2 2 (2 * hplus) 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq204 : dihY 2 (2 * hminus) 2 2 2 (Real.sqrt 8) = dihY 2 (Real.sqrt 8) 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq205 : dihY 2 2.52 (2 * hminus) (2 * hminus) (2 * hminus) 2 = dihY 2 (2 * hminus) 2.52 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq206 : dihY 2 2.52 (2 * hminus) (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq207 : dihY 2 2.52 (2 * hminus) 2.52 (2 * hminus) 2 = dihY 2 (2 * hminus) 2 2.52 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq208 : dihY 2 2.52 (2 * hminus) 2.52 2 2 = dihY 2 2 2 2.52 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq209 : dihY 2 2.52 (2 * hminus) (2 * hplus) (2 * hminus) 2 = dihY 2 (2 * hminus) 2.52 (2 * hplus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq210 : dihY 2 2.52 (2 * hminus) (2 * hplus) 2 2 = dihY 2 2 2 (2 * hplus) (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq211 : dihY 2 2.52 (2 * hminus) (Real.sqrt 8) 2 2 = dihY 2 2 2 (Real.sqrt 8) (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq212 : dihY 2 2.52 (2 * hminus) 2 (2 * hminus) 2 = dihY 2 2 (2 * hminus) 2 (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq213 : dihY 2 2.52 (2 * hminus) 2 2 (2 * hminus) = dihY 2 (2 * hminus) 2.52 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq214 : dihY 2 2.52 (2 * hminus) 2 2 2.52 = dihY 2 (2 * hminus) 2.52 2 2.52 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq215 : dihY 2 2.52 (2 * hminus) 2 2 (Real.sqrt 8) = dihY 2 2 (Real.sqrt 8) 2 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq216 : dihY 2 2.52 (2 * hminus) 2 2 2 = dihY 2 2 2 2 (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq217 : dihY 2 2.52 2.52 (2 * hminus) (2 * hminus) 2 = dihY 2 2.52 2.52 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq218 : dihY 2 2.52 2.52 (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) 2.52 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq219 : dihY 2 2.52 2.52 2 (2 * hminus) 2 = dihY 2 2.52 2.52 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq220 : dihY 2 2.52 (2 * hplus) (2 * hminus) (2 * hminus) 2 = dihY 2 2 (2 * hminus) (2 * hminus) (2 * hplus) 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq221 : dihY 2 2.52 (2 * hplus) (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) (2 * hplus) 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq222 : dihY 2 2.52 (2 * hplus) 2 (2 * hminus) 2 = dihY 2 (2 * hminus) 2 2 2.52 (2 * hplus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq223 : dihY 2 2.52 (2 * hplus) 2 2 2 = dihY 2 2 2 2 (2 * hplus) 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq224 : dihY 2 2.52 2 (2 * hminus) 2 2 = dihY 2 2 2.52 (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq225 : dihY 2 2.52 2 2.52 2 2 = dihY 2 2 2 2.52 2 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq226 : dihY 2 2.52 2 (2 * hplus) 2 2 = dihY 2 2 2.52 (2 * hplus) 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq227 : dihY 2 2.52 2 (Real.sqrt 8) 2 2 = dihY 2 2 2 (Real.sqrt 8) 2 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq228 : dihY 2 2.52 2 2 (2 * hminus) 2.52 = dihY 2 (2 * hminus) 2.52 2 2.52 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq229 : dihY 2 2.52 2 2 (2 * hminus) (2 * hplus) = dihY 2 2 2.52 2 (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq230 : dihY 2 2.52 2 2 2 (2 * hminus) = dihY 2 2 (2 * hminus) 2 2.52 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq231 : dihY 2 2.52 2 2 2 2.52 = dihY 2 2 2.52 2 2.52 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq232 : dihY 2 2.52 2 2 2 (2 * hplus) = dihY 2 2 2.52 2 (2 * hplus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq233 : dihY 2 2.52 2 2 2 (Real.sqrt 8) = dihY 2 (Real.sqrt 8) 2 2 2 2.52 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq234 : dihY 2 (2 * hplus) (2 * hminus) (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq235 : dihY 2 (2 * hplus) (2 * hminus) 2.52 2 2 = dihY 2 2 2 2.52 (2 * hminus) (2 * hplus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq236 : dihY 2 (2 * hplus) (2 * hminus) 2 2 (2 * hminus) = dihY 2 2 (2 * hminus) 2 (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq237 : dihY 2 (2 * hplus) (2 * hminus) 2 2 2.52 = dihY 2 2 2.52 2 (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq238 : dihY 2 (2 * hplus) (2 * hminus) 2 2 (Real.sqrt 8) = dihY 2 (Real.sqrt 8) 2 2 (2 * hminus) (2 * hplus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq239 : dihY 2 (2 * hplus) 2 (2 * hminus) 2 2 = dihY 2 2 (2 * hplus) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq240 : dihY 2 (2 * hplus) 2 2.52 2 2 = dihY 2 2 2 2.52 (2 * hplus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq241 : dihY 2 (2 * hplus) 2 (Real.sqrt 8) 2 2 = dihY 2 2 2 (Real.sqrt 8) (2 * hplus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq242 : dihY 2 (2 * hplus) 2 2 2 (2 * hminus) = dihY 2 2 (2 * hplus) 2 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq243 : dihY 2 (2 * hplus) 2 2 2 2.52 = dihY 2 2 2.52 2 (2 * hplus) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq244 : dihY 2 (2 * hplus) 2 2 2 (Real.sqrt 8) = dihY 2 (Real.sqrt 8) 2 2 2 (2 * hplus) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq245 : dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) (2 * hminus) 2 = dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq246 : dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq247 : dihY 2 (Real.sqrt 8) (2 * hminus) 2.52 (2 * hminus) 2 = dihY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq248 : dihY 2 (Real.sqrt 8) (2 * hminus) 2.52 2 2 = dihY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq249 : dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hplus) (2 * hminus) 2 = dihY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq250 : dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hplus) 2 2 = dihY 2 2 2 (2 * hplus) (Real.sqrt 8) (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq251 : dihY 2 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 = dihY 2 2 (2 * hminus) 2 (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq252 : dihY 2 (Real.sqrt 8) (2 * hminus) 2 2 2 = dihY 2 2 2 2 (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq253 : dihY 2 (Real.sqrt 8) 2.52 (2 * hminus) (2 * hminus) 2 = dihY 2 2.52 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq254 : dihY 2 (Real.sqrt 8) 2.52 (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) (Real.sqrt 8) 2.52 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq255 : dihY 2 (Real.sqrt 8) 2.52 2 (2 * hminus) 2 = dihY 2 2.52 (Real.sqrt 8) 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq256 : dihY 2 (Real.sqrt 8) (2 * hplus) (2 * hminus) (2 * hminus) 2 = dihY 2 2 (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq257 : dihY 2 (Real.sqrt 8) (2 * hplus) (2 * hminus) 2 2 = dihY 2 (2 * hplus) (Real.sqrt 8) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq258 : dihY 2 (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) 2 = dihY 2 2 (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq259 : dihY 2 (Real.sqrt 8) (2 * hplus) 2 2 2 = dihY 2 (2 * hplus) (Real.sqrt 8) 2 2 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq260 : dihY 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) 2 = dihY 2 2 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq261 : dihY 2 (Real.sqrt 8) 2 (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) 2 (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq262 : dihY 2 (Real.sqrt 8) 2 2.52 (2 * hminus) 2 = dihY 2 (2 * hminus) 2 2.52 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq263 : dihY 2 (Real.sqrt 8) 2 2.52 2 2 = dihY 2 2 2 2.52 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq264 : dihY 2 (Real.sqrt 8) 2 (2 * hplus) (2 * hminus) 2 = dihY 2 (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq265 : dihY 2 (Real.sqrt 8) 2 (2 * hplus) 2 2 = dihY 2 2 2 (2 * hplus) (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq266 : dihY 2 (Real.sqrt 8) 2 2 (2 * hminus) (2 * hminus) = dihY 2 (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq267 : dihY 2 (Real.sqrt 8) 2 2 (2 * hminus) 2.52 = dihY 2 2 (Real.sqrt 8) 2 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq268 : dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2.52 = dihY 2 (2 * hminus) 2.52 (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq269 : dihY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) = dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq270 : dihY 2 2 (2 * hminus) (2 * hminus) 2 2.52 = dihY 2 2.52 2 (2 * hminus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq271 : dihY 2 2 (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) = dihY 2 2 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq272 : dihY 2 2 (2 * hminus) 2.52 (2 * hminus) 2.52 = dihY 2 (2 * hminus) 2 2.52 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq273 : dihY 2 2 (2 * hminus) 2.52 (2 * hminus) (Real.sqrt 8) = dihY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq274 : dihY 2 2 (2 * hminus) 2.52 2 2.52 = dihY 2 2.52 2 2.52 (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq275 : dihY 2 2 (2 * hminus) 2.52 2 (Real.sqrt 8) = dihY 2 (2 * hminus) 2 2.52 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq276 : dihY 2 2 (2 * hminus) 2.52 2 2 = dihY 2 2 2 2.52 (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq277 : dihY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) 2.52 = dihY 2 (2 * hminus) 2.52 (2 * hplus) 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq278 : dihY 2 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) = dihY 2 (2 * hminus) 2 (2 * hplus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq279 : dihY 2 2 (2 * hminus) (2 * hplus) 2 2.52 = dihY 2 2.52 2 (2 * hplus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq280 : dihY 2 2 (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) = dihY 2 (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq281 : dihY 2 2 (2 * hminus) (2 * hplus) 2 2 = dihY 2 2 2 (2 * hplus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq282 : dihY 2 2 (2 * hminus) 2 (Real.sqrt 8) 2 = dihY 2 (Real.sqrt 8) 2 2 2 (2 * hminus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq283 : dihY 2 2 2.52 (2 * hminus) 2 (2 * hminus) = dihY 2 2.52 2 (2 * hminus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq284 : dihY 2 2 2.52 2.52 2 (2 * hminus) = dihY 2 2.52 2 2.52 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq285 : dihY 2 2 2.52 2.52 2 2 = dihY 2 2 2 2.52 2 2.52 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq286 : dihY 2 2 2.52 (2 * hplus) 2 (2 * hminus) = dihY 2 2.52 2 (2 * hplus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq287 : dihY 2 2 2.52 2 (2 * hminus) 2 = dihY 2 2 (2 * hminus) 2 2.52 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq288 : dihY 2 2 2.52 2 (Real.sqrt 8) 2 = dihY 2 (Real.sqrt 8) 2 2 2 2.52 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq289 : dihY 2 2 (2 * hplus) 2 2.52 2 = dihY 2 2 2.52 2 (2 * hplus) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq290 : dihY 2 2 (2 * hplus) 2 (Real.sqrt 8) 2 = dihY 2 (Real.sqrt 8) 2 2 2 (2 * hplus) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq291 : dihY 2 2 (Real.sqrt 8) (2 * hminus) 2 2 = dihY 2 2 2 (2 * hminus) 2 (Real.sqrt 8) := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq292 : dihY 2 2 (Real.sqrt 8) 2.52 2 (2 * hminus) = dihY 2 (2 * hminus) 2 2.52 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq293 : dihY 2 2 (Real.sqrt 8) 2.52 2 2 = dihY 2 2 2 2.52 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq294 : dihY 2 2 (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) = dihY 2 (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq295 : dihY 2 2 (Real.sqrt 8) (2 * hplus) 2 2 = dihY 2 2 2 (2 * hplus) (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq296 : dihY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) = dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq297 : dihY 2 2 2 (2 * hminus) (2 * hminus) (2 * hplus) = dihY 2 2 2 (2 * hminus) (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq298 : dihY 2 2 2 (2 * hminus) (2 * hminus) 2 = dihY 2 2 (2 * hminus) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq299 : dihY 2 2 2 (2 * hminus) 2.52 (2 * hminus) = dihY 2 2 2 (2 * hminus) (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq300 : dihY 2 2 2 (2 * hminus) 2.52 (2 * hplus) = dihY 2 2 2 (2 * hminus) (2 * hplus) 2.52 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq301 : dihY 2 2 2 (2 * hminus) 2.52 2 = dihY 2 2 2.52 (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq302 : dihY 2 2 2 (2 * hminus) (2 * hplus) 2 = dihY 2 2 (2 * hplus) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq303 : dihY 2 2 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) = dihY 2 2 2 (2 * hminus) (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq304 : dihY 2 2 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) = dihY 2 (2 * hplus) (Real.sqrt 8) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq305 : dihY 2 2 2 (2 * hminus) 2 (2 * hminus) = dihY 2 2 (2 * hminus) (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq306 : dihY 2 2 2 (2 * hminus) 2 2.52 = dihY 2 2 2.52 (2 * hminus) 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq307 : dihY 2 2 2 2.52 (2 * hminus) 2.52 = dihY 2 2 2 2.52 2.52 (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq308 : dihY 2 2 2 2.52 (2 * hminus) (Real.sqrt 8) = dihY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq309 : dihY 2 2 2 2.52 2.52 2 = dihY 2 2 2 2.52 2 2.52 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq310 : dihY 2 2 2 2.52 (2 * hplus) (2 * hminus) = dihY 2 2 2 2.52 (2 * hminus) (2 * hplus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq311 : dihY 2 2 2 2.52 2 (2 * hminus) = dihY 2 2 2 2.52 (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq312 : dihY 2 2 2 2.52 2 (Real.sqrt 8) = dihY 2 2 2 2.52 (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq313 : dihY 2 2 2 (2 * hplus) (2 * hminus) (Real.sqrt 8) = dihY 2 2 2 (2 * hplus) (Real.sqrt 8) (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq314 : dihY 2 2 2 (2 * hplus) 2 (2 * hminus) = dihY 2 2 2 (2 * hplus) (2 * hminus) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq315 : dihY 2 2 2 (2 * hplus) 2 2.52 = dihY 2 2 2.52 (2 * hplus) 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq316 : dihY 2 2 2 (2 * hplus) 2 (Real.sqrt 8) = dihY 2 2 2 (2 * hplus) (Real.sqrt 8) 2 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq317 : dihY 2 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) = dihY 2 (2 * hminus) (2 * hminus) (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq318 : dihY 2 2 2 (Real.sqrt 8) (2 * hminus) 2 = dihY 2 2 (2 * hminus) (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq319 : dihY 2 2 2 (Real.sqrt 8) 2.52 (2 * hminus) = dihY 2 2 2 (Real.sqrt 8) (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq320 : dihY 2 2 2 (Real.sqrt 8) 2.52 2 = dihY 2 2 2 (Real.sqrt 8) 2 2.52 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq321 : dihY 2 2 2 (Real.sqrt 8) (2 * hplus) (2 * hminus) = dihY 2 (2 * hplus) (2 * hminus) (Real.sqrt 8) 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq322 : dihY 2 2 2 2 (2 * hminus) (2 * hplus) = dihY 2 2 2 2 (2 * hplus) (2 * hminus) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq323 : dihY 2 2 2 2 2.52 (2 * hminus) = dihY 2 2 2 2 (2 * hminus) 2.52 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq324 : dihY 2 2 2 2 2.52 2.52 = dihY 2 2.52 2.52 2 2 2 := by
  rw [ztg_dihY_sym26]

theorem ztgcTrio_eq325 : dihY 2 2 2 2 2.52 (2 * hplus) = dihY 2 2 2 2 (2 * hplus) 2.52 := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq326 : dihY 2 2 2 2 (Real.sqrt 8) (2 * hminus) = dihY 2 2 2 2 (2 * hminus) (Real.sqrt 8) := by
  rw [ztg_dihY_sym23]

theorem ztgcTrio_eq327 : dihY 2 2 2 2 (Real.sqrt 8) 2.52 = dihY 2 (Real.sqrt 8) 2.52 2 2 2 := by
  rw [ztg_dihY_sym_psi]

theorem ztgcTrio_eq328 : dihY 2 2 2 2 (Real.sqrt 8) (2 * hplus) = dihY 2 (2 * hplus) (Real.sqrt 8) 2 2 2 := by
  rw [ztg_dihY_sym26]

/-! ## Per-solY-term brackets (hoisted standalone: context-free proofs) -/

theorem ztgcTrio_s0_1 : ((1866607521295114209/5000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 2 2 ∧ solY (2 * hminus) 2 (2 * hminus) 2 2 2 ≤ ((14936454666047844417/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq54, ztgcTrio_eq162, ztgcTrio_eq18]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1866607521295114209/5000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((121618696337696172259/100000000000000000000 : ℝ)) + ((108254023109499263509/100000000000000000000 : ℝ)) + ((121618696337696172259/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1866607521295114209/5000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t20.1, ztgcTrioT_t99.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((48648203703630582693/40000000000000000000 : ℝ)) + ((216518767011872042847/200000000000000000000 : ℝ)) + ((48648203703630582693/40000000000000000000 : ℝ)) ≤ ((14936454666047844417/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t20.2, ztgcTrioT_t99.2]) (le_trans hm2 (add_le_add_right hπlo ((14936454666047844417/40000000000000000000 : ℝ))))

theorem ztgcTrio_s0_2 : ((5232040888056777083/10000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2 2 2 (2 * hminus) ∧ solY (2 * hminus) 2 2 2 2 (2 * hminus) ≤ ((104651728395127182679/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq189]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((5232040888056777083/10000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((121618696337696172259/100000000000000000000 : ℝ)) + ((102193098252869605239/100000000000000000000 : ℝ)) + ((142667879648991317179/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((5232040888056777083/10000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t20.1, ztgcTrioT_t140.1, ztgcTrioT_t128.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((48648203703630582693/40000000000000000000 : ℝ)) + ((204391140296501819791/200000000000000000000 : ℝ)) + ((57067620059682219423/40000000000000000000 : ℝ)) ≤ ((104651728395127182679/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t20.2, ztgcTrioT_t140.2, ztgcTrioT_t128.2]) (le_trans hm2 (add_le_add_right hπlo ((104651728395127182679/200000000000000000000 : ℝ))))

theorem ztgcTrio_s0_3 : ((5232040888056777083/10000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hminus) 2 2 ∧ solY 2 2 (2 * hminus) (2 * hminus) 2 2 ≤ ((104651728395127182679/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq201, ztgcTrio_eq75]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((5232040888056777083/10000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((142667879648991317179/100000000000000000000 : ℝ)) + ((102193098252869605239/100000000000000000000 : ℝ)) + ((121618696337696172259/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((5232040888056777083/10000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t128.1, ztgcTrioT_t140.1, ztgcTrioT_t20.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((57067620059682219423/40000000000000000000 : ℝ)) + ((204391140296501819791/200000000000000000000 : ℝ)) + ((48648203703630582693/40000000000000000000 : ℝ)) ≤ ((104651728395127182679/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t128.2, ztgcTrioT_t140.2, ztgcTrioT_t20.2]) (le_trans hm2 (add_le_add_right hπlo ((104651728395127182679/200000000000000000000 : ℝ))))

theorem ztgcTrio_s0_4 : ((3971525852424628701/5000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hminus) 2 (2 * hminus) ∧ solY 2 2 2 (2 * hminus) 2 (2 * hminus) ≤ ((31775287378151117877/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq305, ztgcTrio_eq298]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((3971525852424628701/5000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((142667879648991317179/100000000000000000000 : ℝ)) + ((108254023109499263509/100000000000000000000 : ℝ)) + ((142667879648991317179/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((3971525852424628701/5000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t128.1, ztgcTrioT_t99.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((57067620059682219423/40000000000000000000 : ℝ)) + ((216518767011872042847/200000000000000000000 : ℝ)) + ((57067620059682219423/40000000000000000000 : ℝ)) ≤ ((31775287378151117877/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t128.2, ztgcTrioT_t99.2]) (le_trans hm2 (add_le_add_right hπlo ((31775287378151117877/40000000000000000000 : ℝ))))

theorem ztgcTrio_s1_1 : ((855044335665550990799/2000000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((427626676233639486697/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq157, ztgcTrio_eq11]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((855044335665550990799/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((51958550789785395683/50000000000000000000 : ℝ)) + ((378879103530576266069/400000000000000000000 : ℝ)) + ((1582746046800520155037/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((855044335665550990799/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t41.1, ztgcTrioT_t96.1, ztgcTrioT_t13.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((207845084726220112153/200000000000000000000 : ℝ)) + ((47361499662518775687/50000000000000000000 : ℝ)) + ((395690978235464162663/250000000000000000000 : ℝ)) ≤ ((427626676233639486697/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t41.2, ztgcTrioT_t96.2, ztgcTrioT_t13.2]) (le_trans hm2 (add_le_add_right hπlo ((427626676233639486697/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s1_2 : ((855044335665550990799/2000000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((427626676233639486697/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq157, ztgcTrio_eq11]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((855044335665550990799/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((51958550789785395683/50000000000000000000 : ℝ)) + ((378879103530576266069/400000000000000000000 : ℝ)) + ((1582746046800520155037/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((855044335665550990799/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t41.1, ztgcTrioT_t96.1, ztgcTrioT_t13.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((207845084726220112153/200000000000000000000 : ℝ)) + ((47361499662518775687/50000000000000000000 : ℝ)) + ((395690978235464162663/250000000000000000000 : ℝ)) ≤ ((427626676233639486697/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t41.2, ztgcTrioT_t96.2, ztgcTrioT_t13.2]) (le_trans hm2 (add_le_add_right hπlo ((427626676233639486697/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s1_3 : ((1231886097750708552059/2000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((616036523619123348057/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq269, ztgcTrio_eq63]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1231886097750708552059/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((122759189683828669429/100000000000000000000 : ℝ)) + ((378879103530576266069/400000000000000000000 : ℝ)) + ((1582746046800520155037/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1231886097750708552059/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t123.1, ztgcTrioT_t96.1, ztgcTrioT_t13.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((9821082168132675377/8000000000000000000 : ℝ)) + ((47361499662518775687/50000000000000000000 : ℝ)) + ((395690978235464162663/250000000000000000000 : ℝ)) ≤ ((616036523619123348057/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t123.2, ztgcTrioT_t96.2, ztgcTrioT_t13.2]) (le_trans hm2 (add_le_add_right hπlo ((616036523619123348057/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s1_4 : ((1231886097750708552059/2000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((616036523619123348057/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq269, ztgcTrio_eq63]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1231886097750708552059/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((122759189683828669429/100000000000000000000 : ℝ)) + ((378879103530576266069/400000000000000000000 : ℝ)) + ((1582746046800520155037/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1231886097750708552059/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t123.1, ztgcTrioT_t96.1, ztgcTrioT_t13.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((9821082168132675377/8000000000000000000 : ℝ)) + ((47361499662518775687/50000000000000000000 : ℝ)) + ((395690978235464162663/250000000000000000000 : ℝ)) ≤ ((616036523619123348057/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t123.2, ztgcTrioT_t96.2, ztgcTrioT_t13.2]) (le_trans hm2 (add_le_add_right hπlo ((616036523619123348057/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s2_1 : ((43855193457473823691/100000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ∧ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((87724383891292527549/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq49]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((43855193457473823691/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((55126375427410257267/50000000000000000000 : ℝ)) + ((13750895710682211847/10000000000000000000 : ℝ)) + ((55126375427410257267/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((43855193457473823691/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t16.1, ztgcTrioT_t90.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((220510748838481597491/200000000000000000000 : ℝ)) + ((275021416932267980259/200000000000000000000 : ℝ)) + ((220510748838481597491/200000000000000000000 : ℝ)) ≤ ((87724383891292527549/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t16.2, ztgcTrioT_t90.2]) (le_trans hm2 (add_le_add_right hπlo ((87724383891292527549/200000000000000000000 : ℝ))))

theorem ztgcTrio_s2_2 : ((43855193457473823691/100000000000000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ∧ solY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ≤ ((87724383891292527549/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq49]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((43855193457473823691/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((55126375427410257267/50000000000000000000 : ℝ)) + ((55126375427410257267/50000000000000000000 : ℝ)) + ((13750895710682211847/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((43855193457473823691/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t16.1, ztgcTrioT_t90.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((220510748838481597491/200000000000000000000 : ℝ)) + ((220510748838481597491/200000000000000000000 : ℝ)) + ((275021416932267980259/200000000000000000000 : ℝ)) ≤ ((87724383891292527549/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t16.2, ztgcTrioT_t90.2]) (le_trans hm2 (add_le_add_right hπlo ((87724383891292527549/200000000000000000000 : ℝ))))

theorem ztgcTrio_s2_3 : ((43855193457473823691/100000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((87724383891292527549/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq49]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((43855193457473823691/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((13750895710682211847/10000000000000000000 : ℝ)) + ((55126375427410257267/50000000000000000000 : ℝ)) + ((55126375427410257267/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((43855193457473823691/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t90.1, ztgcTrioT_t16.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((275021416932267980259/200000000000000000000 : ℝ)) + ((220510748838481597491/200000000000000000000 : ℝ)) + ((220510748838481597491/200000000000000000000 : ℝ)) ≤ ((87724383891292527549/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t90.2, ztgcTrioT_t16.2]) (le_trans hm2 (add_le_add_right hπlo ((87724383891292527549/200000000000000000000 : ℝ))))

theorem ztgcTrio_s2_4 : ((98367605961477031563/100000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((39349144015773058617/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq296, ztgcTrio_eq296, ztgcTrio_eq296]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((98367605961477031563/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((13750895710682211847/10000000000000000000 : ℝ)) + ((13750895710682211847/10000000000000000000 : ℝ)) + ((13750895710682211847/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((98367605961477031563/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t90.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((275021416932267980259/200000000000000000000 : ℝ)) + ((275021416932267980259/200000000000000000000 : ℝ)) + ((275021416932267980259/200000000000000000000 : ℝ)) ≤ ((39349144015773058617/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t90.2]) (le_trans hm2 (add_le_add_right hπlo ((39349144015773058617/40000000000000000000 : ℝ))))

theorem ztgcTrio_s3_1 : ((26159727705155581283/50000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((104653635244753755861/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq48, ztgcTrio_eq149]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((26159727705155581283/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((102192375561257185251/100000000000000000000 : ℝ)) + ((121618696337696172259/100000000000000000000 : ℝ)) + ((142667648870347128903/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((26159727705155581283/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t3.1, ztgcTrioT_t89.1, ztgcTrioT_t12.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((204392585632461373687/200000000000000000000 : ℝ)) + ((48648203703630582693/40000000000000000000 : ℝ)) + ((285338561812078116401/200000000000000000000 : ℝ)) ≤ ((104653635244753755861/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t3.2, ztgcTrioT_t89.2, ztgcTrioT_t12.2]) (le_trans hm2 (add_le_add_right hπlo ((104653635244753755861/200000000000000000000 : ℝ))))

theorem ztgcTrio_s3_2 : ((381165979536008017281/1000000000000000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((190648699676927103843/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq2, ztgcTrio_eq0]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((381165979536008017281/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((102192375561257185251/100000000000000000000 : ℝ)) + ((102192375561257185251/100000000000000000000 : ℝ)) + ((1478911121900757550731/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((381165979536008017281/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t3.1, ztgcTrioT_t0.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((204392585632461373687/200000000000000000000 : ℝ)) + ((204392585632461373687/200000000000000000000 : ℝ)) + ((369741049154733427319/250000000000000000000 : ℝ)) ≤ ((190648699676927103843/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t3.2, ztgcTrioT_t0.2]) (le_trans hm2 (add_le_add_right hπlo ((190648699676927103843/500000000000000000000 : ℝ))))

theorem ztgcTrio_s3_3 : ((26159727705155581283/50000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((104653635244753755861/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq150, ztgcTrio_eq13, ztgcTrio_eq45]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((26159727705155581283/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((121618696337696172259/100000000000000000000 : ℝ)) + ((102192375561257185251/100000000000000000000 : ℝ)) + ((142667648870347128903/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((26159727705155581283/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t89.1, ztgcTrioT_t3.1, ztgcTrioT_t12.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((48648203703630582693/40000000000000000000 : ℝ)) + ((204392585632461373687/200000000000000000000 : ℝ)) + ((285338561812078116401/200000000000000000000 : ℝ)) ≤ ((104653635244753755861/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t89.2, ztgcTrioT_t3.2, ztgcTrioT_t12.2]) (le_trans hm2 (add_le_add_right hπlo ((104653635244753755861/200000000000000000000 : ℝ))))

theorem ztgcTrio_s3_4 : ((769692395064787757441/1000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((384890864105384802733/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq180]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((769692395064787757441/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((121618696337696172259/100000000000000000000 : ℝ)) + ((121618696337696172259/100000000000000000000 : ℝ)) + ((1478911121900757550731/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((769692395064787757441/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t89.1, ztgcTrioT_t0.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((48648203703630582693/40000000000000000000 : ℝ)) + ((48648203703630582693/40000000000000000000 : ℝ)) + ((369741049154733427319/250000000000000000000 : ℝ)) ≤ ((384890864105384802733/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t89.2, ztgcTrioT_t0.2]) (le_trans hm2 (add_le_add_right hπlo ((384890864105384802733/500000000000000000000 : ℝ))))

theorem ztgcTrio_s4_1 : ((18217516232455841111/50000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2.52 2 2 2 ∧ solY (2 * hminus) 2 2.52 2 2 2 ≤ ((14576334043769359467/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq58, ztgcTrio_eq216, ztgcTrio_eq86]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((18217516232455841111/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((119524682053453925961/100000000000000000000 : ℝ)) + ((53840426283111398607/50000000000000000000 : ℝ)) + ((61694381602112141447/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((18217516232455841111/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t31.1, ztgcTrioT_t110.1, ztgcTrioT_t53.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((239054588069088520241/200000000000000000000 : ℝ)) + ((43072922448584515949/40000000000000000000 : ℝ)) + ((246781000624774345041/200000000000000000000 : ℝ)) ≤ ((14576334043769359467/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t31.2, ztgcTrioT_t110.2, ztgcTrioT_t53.2]) (le_trans hm2 (add_le_add_right hπlo ((14576334043769359467/40000000000000000000 : ℝ))))

theorem ztgcTrio_s4_2 : ((10631281659924953891/20000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2 2 2 2.52 ∧ solY (2 * hminus) 2 2 2 2 2.52 ≤ ((106323775571938642223/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq77, ztgcTrio_eq191]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((10631281659924953891/20000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((119524682053453925961/100000000000000000000 : ℝ)) + ((100903651456755912911/100000000000000000000 : ℝ)) + ((14688734014840425443/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((10631281659924953891/20000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t31.1, ztgcTrioT_t141.1, ztgcTrioT_t130.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((239054588069088520241/200000000000000000000 : ℝ)) + ((201810988923010671481/200000000000000000000 : ℝ)) + ((293776729297778098193/200000000000000000000 : ℝ)) ≤ ((106323775571938642223/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t31.2, ztgcTrioT_t141.2, ztgcTrioT_t130.2]) (le_trans hm2 (add_le_add_right hπlo ((106323775571938642223/200000000000000000000 : ℝ))))

theorem ztgcTrio_s4_3 : ((25409742902353012081/50000000000000000000 : ℝ)) ≤ solY 2 2 2.52 (2 * hminus) 2 2 ∧ solY 2 2 2.52 (2 * hminus) 2 2 ≤ ((101649939761706503813/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq230]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((25409742902353012081/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((35171584125678788051/25000000000000000000 : ℝ)) + ((100903651456755912911/100000000000000000000 : ℝ)) + ((61694381602112141447/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((25409742902353012081/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t150.1, ztgcTrioT_t141.1, ztgcTrioT_t53.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((281376480931860134983/200000000000000000000 : ℝ)) + ((201810988923010671481/200000000000000000000 : ℝ)) + ((246781000624774345041/200000000000000000000 : ℝ)) ≤ ((101649939761706503813/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t150.2, ztgcTrioT_t141.2, ztgcTrioT_t53.2]) (le_trans hm2 (add_le_add_right hπlo ((101649939761706503813/200000000000000000000 : ℝ))))

theorem ztgcTrio_s4_4 : ((81095263858352880001/100000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hminus) 2 2.52 ∧ solY 2 2 2 (2 * hminus) 2 2.52 ≤ ((162199291754622165229/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq306, ztgcTrio_eq323]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((81095263858352880001/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((35171584125678788051/25000000000000000000 : ℝ)) + ((53840426283111398607/50000000000000000000 : ℝ)) + ((14688734014840425443/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((81095263858352880001/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t150.1, ztgcTrioT_t110.1, ztgcTrioT_t130.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((281376480931860134983/200000000000000000000 : ℝ)) + ((43072922448584515949/40000000000000000000 : ℝ)) + ((293776729297778098193/200000000000000000000 : ℝ)) ≤ ((162199291754622165229/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t150.2, ztgcTrioT_t110.2, ztgcTrioT_t130.2]) (le_trans hm2 (add_le_add_right hπlo ((162199291754622165229/200000000000000000000 : ℝ))))

theorem ztgcTrio_s5_1 : ((828528066835227668861/2000000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2.52 2 2 (2 * hminus) ∧ solY (2 * hminus) 2 2.52 2 2 (2 * hminus) ≤ ((414321844391632204449/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq57, ztgcTrio_eq212, ztgcTrio_eq82]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((828528066835227668861/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((101438567402920726463/100000000000000000000 : ℝ)) + ((373359186450437003429/400000000000000000000 : ℝ)) + ((804036523426103649849/500000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((828528066835227668861/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t42.1, ztgcTrioT_t134.1, ztgcTrioT_t49.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((202882199970615821293/200000000000000000000 : ℝ)) + ((2333551575713769551/2500000000000000000 : ℝ)) + ((402020716960684629011/250000000000000000000 : ℝ)) ≤ ((414321844391632204449/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t42.2, ztgcTrioT_t134.2, ztgcTrioT_t49.2]) (le_trans hm2 (add_le_add_right hπlo ((414321844391632204449/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s5_2 : ((862471940503766378337/2000000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 2 2.52 ∧ solY (2 * hminus) 2 (2 * hminus) 2 2 2.52 ≤ ((17252486295974834567/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq52, ztgcTrio_eq158, ztgcTrio_eq12]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((862471940503766378337/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((101438567402920726463/100000000000000000000 : ℝ)) + ((370711393699301358141/400000000000000000000 : ℝ)) + ((203958058195539470957/125000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((862471940503766378337/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t42.1, ztgcTrioT_t97.1, ztgcTrioT_t14.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((202882199970615821293/200000000000000000000 : ℝ)) + ((23170653210848918619/25000000000000000000 : ℝ)) + ((163166768270202825141/100000000000000000000 : ℝ)) ≤ ((17252486295974834567/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t42.2, ztgcTrioT_t97.2, ztgcTrioT_t14.2]) (le_trans hm2 (add_le_add_right hπlo ((17252486295974834567/40000000000000000000 : ℝ))))

theorem ztgcTrio_s5_3 : ((1187659737632781467661/2000000000000000000000 : ℝ)) ≤ solY 2 2 2.52 (2 * hminus) 2 (2 * hminus) ∧ solY 2 2 2.52 (2 * hminus) 2 (2 * hminus) ≤ ((593899474663812168739/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq283, ztgcTrio_eq108]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1187659737632781467661/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((4802283965223293109/4000000000000000000 : ℝ)) + ((370711393699301358141/400000000000000000000 : ℝ)) + ((804036523426103649849/500000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1187659737632781467661/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t149.1, ztgcTrioT_t97.1, ztgcTrioT_t49.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((240116626395362029279/200000000000000000000 : ℝ)) + ((23170653210848918619/25000000000000000000 : ℝ)) + ((402020716960684629011/250000000000000000000 : ℝ)) ≤ ((593899474663812168739/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t149.2, ztgcTrioT_t97.2, ztgcTrioT_t49.2]) (le_trans hm2 (add_le_add_right hπlo ((593899474663812168739/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s5_4 : ((1248081538812676630017/2000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hminus) 2 2.52 ∧ solY 2 2 (2 * hminus) (2 * hminus) 2 2.52 ≤ ((124815758274930595949/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq270, ztgcTrio_eq196, ztgcTrio_eq67]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1248081538812676630017/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((4802283965223293109/4000000000000000000 : ℝ)) + ((373359186450437003429/400000000000000000000 : ℝ)) + ((203958058195539470957/125000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1248081538812676630017/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t149.1, ztgcTrioT_t134.1, ztgcTrioT_t14.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((240116626395362029279/200000000000000000000 : ℝ)) + ((2333551575713769551/2500000000000000000 : ℝ)) + ((163166768270202825141/100000000000000000000 : ℝ)) ≤ ((124815758274930595949/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t149.2, ztgcTrioT_t134.2, ztgcTrioT_t14.2]) (le_trans hm2 (add_le_add_right hπlo ((124815758274930595949/200000000000000000000 : ℝ))))

theorem ztgcTrio_s6_1 : ((1337386894449356471/3125000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2.52 2 (2 * hminus) 2 ∧ solY (2 * hminus) 2 2.52 2 (2 * hminus) 2 ≤ ((17121493118235217913/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq56, ztgcTrio_eq206, ztgcTrio_eq83]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1337386894449356471/3125000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((21736395041515063001/20000000000000000000 : ℝ)) + ((27352026969511783927/20000000000000000000 : ℝ)) + ((111513535926234496279/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1337386894449356471/3125000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t17.1, ztgcTrioT_t102.1, ztgcTrioT_t50.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((43473846397086847289/40000000000000000000 : ℝ)) + ((273523858699687463341/200000000000000000000 : ℝ)) + ((223032905623993037471/200000000000000000000 : ℝ)) ≤ ((17121493118235217913/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t17.2, ztgcTrioT_t102.2, ztgcTrioT_t50.2]) (le_trans hm2 (add_le_add_right hπlo ((17121493118235217913/40000000000000000000 : ℝ))))

theorem ztgcTrio_s6_2 : ((11126999409245204217/25000000000000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 2 2 2.52 ∧ solY (2 * hminus) (2 * hminus) 2 2 2 2.52 ≤ ((89036879012176240211/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq15, ztgcTrio_eq50, ztgcTrio_eq153]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((11126999409245204217/25000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((21736395041515063001/20000000000000000000 : ℝ)) + ((21736395041515063001/20000000000000000000 : ℝ)) + ((28260662516163902141/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((11126999409245204217/25000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t17.1, ztgcTrioT_t92.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((43473846397086847289/40000000000000000000 : ℝ)) + ((43473846397086847289/40000000000000000000 : ℝ)) + ((282616945759246415013/200000000000000000000 : ℝ)) ≤ ((89036879012176240211/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t17.2, ztgcTrioT_t92.2]) (le_trans hm2 (add_le_add_right hπlo ((89036879012176240211/200000000000000000000 : ℝ))))

theorem ztgcTrio_s6_3 : ((1337386894449356471/3125000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) 2.52 (2 * hminus) 2 2 ∧ solY 2 (2 * hminus) 2.52 (2 * hminus) 2 2 ≤ ((17121493118235217913/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq164]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1337386894449356471/3125000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((27352026969511783927/20000000000000000000 : ℝ)) + ((21736395041515063001/20000000000000000000 : ℝ)) + ((111513535926234496279/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1337386894449356471/3125000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t102.1, ztgcTrioT_t17.1, ztgcTrioT_t50.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((273523858699687463341/200000000000000000000 : ℝ)) + ((43473846397086847289/40000000000000000000 : ℝ)) + ((223032905623993037471/200000000000000000000 : ℝ)) ≤ ((17121493118235217913/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t102.2, ztgcTrioT_t17.2, ztgcTrioT_t50.2]) (le_trans hm2 (add_le_add_right hπlo ((17121493118235217913/40000000000000000000 : ℝ))))

theorem ztgcTrio_s6_4 : ((6291519807309251633/6250000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hminus) (2 * hminus) 2.52 ∧ solY 2 2 2 (2 * hminus) (2 * hminus) 2.52 ≤ ((201346132440682694003/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq299]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((6291519807309251633/6250000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((27352026969511783927/20000000000000000000 : ℝ)) + ((27352026969511783927/20000000000000000000 : ℝ)) + ((28260662516163902141/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((6291519807309251633/6250000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t102.1, ztgcTrioT_t92.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((273523858699687463341/200000000000000000000 : ℝ)) + ((273523858699687463341/200000000000000000000 : ℝ)) + ((282616945759246415013/200000000000000000000 : ℝ)) ≤ ((201346132440682694003/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t102.2, ztgcTrioT_t92.2]) (le_trans hm2 (add_le_add_right hπlo ((201346132440682694003/200000000000000000000 : ℝ))))

theorem ztgcTrio_s7_1 : ((12713306380857132191/25000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) ≤ ((101711426638523226979/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq55, ztgcTrio_eq205]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((12713306380857132191/25000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((4011623142509882223/4000000000000000000 : ℝ)) + ((3005455622006219641/2500000000000000000 : ℝ)) + ((36125921859855502849/25000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((12713306380857132191/25000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t4.1, ztgcTrioT_t101.1, ztgcTrioT_t48.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((200585102984727969061/200000000000000000000 : ℝ)) + ((240437201082641416391/200000000000000000000 : ℝ)) + ((289007653289092489219/200000000000000000000 : ℝ)) ≤ ((101711426638523226979/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t4.2, ztgcTrioT_t101.2, ztgcTrioT_t48.2]) (le_trans hm2 (add_le_add_right hπlo ((101711426638523226979/200000000000000000000 : ℝ))))

theorem ztgcTrio_s7_2 : ((38539500220527376047/100000000000000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2.52 ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2.52 ≤ ((4817992774862209077/12500000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq5, ztgcTrio_eq3]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((38539500220527376047/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((4011623142509882223/4000000000000000000 : ℝ)) + ((4011623142509882223/4000000000000000000 : ℝ)) + ((19014701056752823593/12500000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((38539500220527376047/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t4.1, ztgcTrioT_t1.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((200585102984727969061/200000000000000000000 : ℝ)) + ((200585102984727969061/200000000000000000000 : ℝ)) + ((152118104573139027401/100000000000000000000 : ℝ)) ≤ ((4817992774862209077/12500000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t4.2, ztgcTrioT_t1.2]) (le_trans hm2 (add_le_add_right hπlo ((4817992774862209077/12500000000000000000 : ℝ))))

theorem ztgcTrio_s7_3 : ((12713306380857132191/25000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) 2.52 (2 * hminus) 2 (2 * hminus) ∧ solY 2 (2 * hminus) 2.52 (2 * hminus) 2 (2 * hminus) ≤ ((101711426638523226979/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq94]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((12713306380857132191/25000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((3005455622006219641/2500000000000000000 : ℝ)) + ((4011623142509882223/4000000000000000000 : ℝ)) + ((36125921859855502849/25000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((12713306380857132191/25000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t101.1, ztgcTrioT_t4.1, ztgcTrioT_t48.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((240437201082641416391/200000000000000000000 : ℝ)) + ((200585102984727969061/200000000000000000000 : ℝ)) + ((289007653289092489219/200000000000000000000 : ℝ)) ≤ ((101711426638523226979/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t101.2, ztgcTrioT_t4.2, ztgcTrioT_t48.2]) (le_trans hm2 (add_le_add_right hπlo ((101711426638523226979/200000000000000000000 : ℝ))))

theorem ztgcTrio_s7_4 : ((78394792855530836177/100000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2.52 ∧ solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2.52 ≤ ((39198020148405559973/50000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq268, ztgcTrio_eq183, ztgcTrio_eq66]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((78394792855530836177/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((3005455622006219641/2500000000000000000 : ℝ)) + ((3005455622006219641/2500000000000000000 : ℝ)) + ((19014701056752823593/12500000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((78394792855530836177/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t101.1, ztgcTrioT_t1.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((240437201082641416391/200000000000000000000 : ℝ)) + ((240437201082641416391/200000000000000000000 : ℝ)) + ((152118104573139027401/100000000000000000000 : ℝ)) ≤ ((39198020148405559973/50000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t101.2, ztgcTrioT_t1.2]) (le_trans hm2 (add_le_add_right hπlo ((39198020148405559973/50000000000000000000 : ℝ))))

theorem ztgcTrio_s8_1 : ((15549141926652686001/50000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 ∧ solY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 ≤ ((62208744732933266133/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq62, ztgcTrio_eq252, ztgcTrio_eq136]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((15549141926652686001/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((106870594681673489937/100000000000000000000 : ℝ)) + ((20590117898267071131/20000000000000000000 : ℝ)) + ((135436365039285850257/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((15549141926652686001/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t44.1, ztgcTrioT_t165.1, ztgcTrioT_t80.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((213747288495744806849/200000000000000000000 : ℝ)) + ((205903945048607932613/200000000000000000000 : ℝ)) + ((270876041906519174363/200000000000000000000 : ℝ)) ≤ ((62208744732933266133/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t44.2, ztgcTrioT_t165.2, ztgcTrioT_t80.2]) (le_trans hm2 (add_le_add_right hπlo ((62208744732933266133/200000000000000000000 : ℝ))))

theorem ztgcTrio_s8_2 : ((226024397969809150053/400000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2 2 2 (Real.sqrt 8) ∧ solY (2 * hminus) 2 2 2 2 (Real.sqrt 8) ≤ ((56512297464268257859/100000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq78, ztgcTrio_eq282, ztgcTrio_eq193]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((226024397969809150053/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((106870594681673489937/100000000000000000000 : ℝ)) + ((369218219839977384537/400000000000000000000 : ℝ)) + ((171490215209773775289/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((226024397969809150053/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t44.1, ztgcTrioT_t143.1, ztgcTrioT_t133.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((213747288495744806849/200000000000000000000 : ℝ)) + ((92306532865377171613/100000000000000000000 : ℝ)) + ((68596554283995202667/40000000000000000000 : ℝ)) ≤ ((56512297464268257859/100000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t44.2, ztgcTrioT_t143.2, ztgcTrioT_t133.2]) (le_trans hm2 (add_le_add_right hπlo ((56512297464268257859/100000000000000000000 : ℝ))))

theorem ztgcTrio_s8_3 : ((169650935468119939673/400000000000000000000 : ℝ)) ≤ solY 2 2 (Real.sqrt 8) (2 * hminus) 2 2 ∧ solY 2 2 (Real.sqrt 8) (2 * hminus) 2 2 ≤ ((42418572098760087181/100000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq291]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((169650935468119939673/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((64415539613369556187/50000000000000000000 : ℝ)) + ((369218219839977384537/400000000000000000000 : ℝ)) + ((135436365039285850257/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((169650935468119939673/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t171.1, ztgcTrioT_t143.1, ztgcTrioT_t80.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((51533313455637060893/40000000000000000000 : ℝ)) + ((92306532865377171613/100000000000000000000 : ℝ)) + ((270876041906519174363/200000000000000000000 : ℝ)) ≤ ((42418572098760087181/100000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t171.2, ztgcTrioT_t143.2, ztgcTrioT_t80.2]) (le_trans hm2 (add_le_add_right hπlo ((42418572098760087181/100000000000000000000 : ℝ))))

theorem ztgcTrio_s8_4 : ((89112618568858919471/100000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hminus) 2 (Real.sqrt 8) ∧ solY 2 2 2 (2 * hminus) 2 (Real.sqrt 8) ≤ ((178234753028830602721/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq326, ztgcTrio_eq318]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((89112618568858919471/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((64415539613369556187/50000000000000000000 : ℝ)) + ((20590117898267071131/20000000000000000000 : ℝ)) + ((171490215209773775289/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((89112618568858919471/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t171.1, ztgcTrioT_t165.1, ztgcTrioT_t133.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((51533313455637060893/40000000000000000000 : ℝ)) + ((205903945048607932613/200000000000000000000 : ℝ)) + ((68596554283995202667/40000000000000000000 : ℝ)) ≤ ((178234753028830602721/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t171.2, ztgcTrioT_t165.2, ztgcTrioT_t133.2]) (le_trans hm2 (add_le_add_right hπlo ((178234753028830602721/200000000000000000000 : ℝ))))

theorem ztgcTrio_s9_1 : ((166797984897062472921/500000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) ∧ solY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) ≤ ((4170825307705462863/12500000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq251, ztgcTrio_eq134]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((166797984897062472921/500000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((1713321043047674165203/2000000000000000000000 : ℝ)) + ((1662631315605967470121/2000000000000000000000 : ℝ)) + ((35744248881143947333/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((166797984897062472921/500000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t43.1, ztgcTrioT_t137.1, ztgcTrioT_t78.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((856690339255206968971/1000000000000000000000 : ℝ)) + ((415669667876994281317/500000000000000000000 : ℝ)) + ((357445800639386947179/200000000000000000000 : ℝ)) ≤ ((4170825307705462863/12500000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t43.2, ztgcTrioT_t137.2, ztgcTrioT_t78.2]) (le_trans hm2 (add_le_add_right hπlo ((4170825307705462863/12500000000000000000 : ℝ))))

theorem ztgcTrio_s9_2 : ((16886136690515368191/39062500000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 2 (Real.sqrt 8) ∧ solY (2 * hminus) 2 (2 * hminus) 2 2 (Real.sqrt 8) ≤ ((2161894180850740077743/5000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq53, ztgcTrio_eq159]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((16886136690515368191/39062500000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((1713321043047674165203/2000000000000000000000 : ℝ)) + ((7918296703442209104181/10000000000000000000000 : ℝ)) + ((96269378049951433557/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((16886136690515368191/39062500000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t43.1, ztgcTrioT_t98.1, ztgcTrioT_t15.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((856690339255206968971/1000000000000000000000 : ℝ)) + ((3959377301459013845813/5000000000000000000000 : ℝ)) + ((15403245521702652127/8000000000000000000 : ℝ)) ≤ ((2161894180850740077743/5000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t43.2, ztgcTrioT_t98.2, ztgcTrioT_t15.2]) (le_trans hm2 (add_le_add_right hπlo ((2161894180850740077743/5000000000000000000000 : ℝ))))

theorem ztgcTrio_s9_3 : ((4669553557248785951481/10000000000000000000000 : ℝ)) ≤ solY 2 2 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) ∧ solY 2 2 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) ≤ ((2335157675710419648313/5000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq266, ztgcTrio_eq147]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((4669553557248785951481/10000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((20590117898267071131/20000000000000000000 : ℝ)) + ((7918296703442209104181/10000000000000000000000 : ℝ)) + ((35744248881143947333/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((4669553557248785951481/10000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t170.1, ztgcTrioT_t98.1, ztgcTrioT_t78.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((205903945048607932613/200000000000000000000 : ℝ)) + ((3959377301459013845813/5000000000000000000000 : ℝ)) + ((357445800639386947179/200000000000000000000 : ℝ)) ≤ ((2335157675710419648313/5000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t170.2, ztgcTrioT_t98.2, ztgcTrioT_t78.2]) (le_trans hm2 (add_le_add_right hπlo ((2335157675710419648313/5000000000000000000000 : ℝ))))

theorem ztgcTrio_s9_4 : ((1289232920250945448561/2000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) ∧ solY 2 2 (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) ≤ ((322336048810083251557/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq271, ztgcTrio_eq198, ztgcTrio_eq70]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1289232920250945448561/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((20590117898267071131/20000000000000000000 : ℝ)) + ((1662631315605967470121/2000000000000000000000 : ℝ)) + ((96269378049951433557/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1289232920250945448561/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t170.1, ztgcTrioT_t137.1, ztgcTrioT_t15.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((205903945048607932613/200000000000000000000 : ℝ)) + ((415669667876994281317/500000000000000000000 : ℝ)) + ((15403245521702652127/8000000000000000000 : ℝ)) ≤ ((322336048810083251557/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t170.2, ztgcTrioT_t137.2, ztgcTrioT_t15.2]) (le_trans hm2 (add_le_add_right hπlo ((322336048810083251557/500000000000000000000 : ℝ))))

theorem ztgcTrio_s10_1 : ((36823711754898329207/100000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 ∧ solY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 ≤ ((14733101826645220879/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq61, ztgcTrio_eq246, ztgcTrio_eq135]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((36823711754898329207/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((49536471084505416149/50000000000000000000 : ℝ)) + ((65969963925844529591/50000000000000000000 : ℝ)) + ((59985053546593880787/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((36823711754898329207/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t19.1, ztgcTrioT_t118.1, ztgcTrioT_t79.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((198152613812277251327/200000000000000000000 : ℝ)) + ((263884677837807153771/200000000000000000000 : ℝ)) + ((239946748201080346989/200000000000000000000 : ℝ)) ≤ ((14733101826645220879/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t19.2, ztgcTrioT_t118.2, ztgcTrioT_t79.2]) (le_trans hm2 (add_le_add_right hπlo ((14733101826645220879/40000000000000000000 : ℝ))))

theorem ztgcTrio_s10_2 : ((472571801288646951457/1000000000000000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 2 2 (Real.sqrt 8) ∧ solY (2 * hminus) (2 * hminus) 2 2 2 (Real.sqrt 8) ≤ ((472648428987023397013/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq17]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((472571801288646951457/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((49536471084505416149/50000000000000000000 : ℝ)) + ((49536471084505416149/50000000000000000000 : ℝ)) + ((1632705611498323543967/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((472571801288646951457/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t19.1, ztgcTrioT_t95.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((198152613812277251327/200000000000000000000 : ℝ)) + ((198152613812277251327/200000000000000000000 : ℝ)) + ((1632714944453944122203/1000000000000000000000 : ℝ)) ≤ ((472648428987023397013/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t19.2, ztgcTrioT_t95.2]) (le_trans hm2 (add_le_add_right hπlo ((472648428987023397013/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s10_3 : ((36823711754898329207/100000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) 2 2 ∧ solY 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) 2 2 ≤ ((14733101826645220879/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq177, ztgcTrio_eq42]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((36823711754898329207/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((65969963925844529591/50000000000000000000 : ℝ)) + ((49536471084505416149/50000000000000000000 : ℝ)) + ((59985053546593880787/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((36823711754898329207/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t118.1, ztgcTrioT_t19.1, ztgcTrioT_t79.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((263884677837807153771/200000000000000000000 : ℝ)) + ((198152613812277251327/200000000000000000000 : ℝ)) + ((239946748201080346989/200000000000000000000 : ℝ)) ≤ ((14733101826645220879/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t118.2, ztgcTrioT_t19.2, ztgcTrioT_t79.2]) (le_trans hm2 (add_le_add_right hπlo ((14733101826645220879/40000000000000000000 : ℝ))))

theorem ztgcTrio_s10_4 : ((1129911514942211489137/1000000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hminus) (2 * hminus) (Real.sqrt 8) ∧ solY 2 2 2 (2 * hminus) (2 * hminus) (Real.sqrt 8) ≤ ((1129969069242322421453/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq303, ztgcTrio_eq317]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1129911514942211489137/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((65969963925844529591/50000000000000000000 : ℝ)) + ((65969963925844529591/50000000000000000000 : ℝ)) + ((1632705611498323543967/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1129911514942211489137/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t118.1, ztgcTrioT_t95.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((263884677837807153771/200000000000000000000 : ℝ)) + ((263884677837807153771/200000000000000000000 : ℝ)) + ((1632714944453944122203/1000000000000000000000 : ℝ)) ≤ ((1129969069242322421453/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t118.2, ztgcTrioT_t95.2]) (le_trans hm2 (add_le_add_right hπlo ((1129969069242322421453/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s11_1 : ((169774267866452725029/400000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ≤ ((212231140289927598989/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq60, ztgcTrio_eq245]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((169774267866452725029/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((70774375122673751573/80000000000000000000 : ℝ)) + ((22211046168954130743/20000000000000000000 : ℝ)) + ((157079632577489661923/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((169774267866452725029/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t5.1, ztgcTrioT_t117.1, ztgcTrioT_t77.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((110587684639245952581/125000000000000000000 : ℝ)) + ((222111425848136839311/200000000000000000000 : ℝ)) + ((314159265562979323847/200000000000000000000 : ℝ)) ≤ ((212231140289927598989/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t5.2, ztgcTrioT_t117.2, ztgcTrioT_t77.2]) (le_trans hm2 (add_le_add_right hπlo ((212231140289927598989/500000000000000000000 : ℝ))))

theorem ztgcTrio_s11_2 : ((79429186719998218587/200000000000000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) ≤ ((397193423904724031131/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq4, ztgcTrio_eq1]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((79429186719998218587/200000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((70774375122673751573/80000000000000000000 : ℝ)) + ((70774375122673751573/80000000000000000000 : ℝ)) + ((2764655014254750847/1562500000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((79429186719998218587/200000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t5.1, ztgcTrioT_t2.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((110587684639245952581/125000000000000000000 : ℝ)) + ((110587684639245952581/125000000000000000000 : ℝ)) + ((353876624653296405659/200000000000000000000 : ℝ)) ≤ ((397193423904724031131/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t5.2, ztgcTrioT_t2.2]) (le_trans hm2 (add_le_add_right hπlo ((397193423904724031131/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s11_3 : ((169774267866452725029/400000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) ∧ solY 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) ≤ ((212231140289927598989/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq176, ztgcTrio_eq39, ztgcTrio_eq144]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((169774267866452725029/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((22211046168954130743/20000000000000000000 : ℝ)) + ((70774375122673751573/80000000000000000000 : ℝ)) + ((157079632577489661923/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((169774267866452725029/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t117.1, ztgcTrioT_t5.1, ztgcTrioT_t77.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((222111425848136839311/200000000000000000000 : ℝ)) + ((110587684639245952581/125000000000000000000 : ℝ)) + ((314159265562979323847/200000000000000000000 : ℝ)) ≤ ((212231140289927598989/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t117.2, ztgcTrioT_t5.2, ztgcTrioT_t77.2]) (le_trans hm2 (add_le_add_right hπlo ((212231140289927598989/500000000000000000000 : ℝ))))

theorem ztgcTrio_s11_4 : ((84889117242856037791/100000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (Real.sqrt 8) ∧ solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (Real.sqrt 8) ≤ ((169780945631631436589/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq186]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((84889117242856037791/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((22211046168954130743/20000000000000000000 : ℝ)) + ((22211046168954130743/20000000000000000000 : ℝ)) + ((2764655014254750847/1562500000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((84889117242856037791/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t117.1, ztgcTrioT_t2.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((222111425848136839311/200000000000000000000 : ℝ)) + ((222111425848136839311/200000000000000000000 : ℝ)) + ((353876624653296405659/200000000000000000000 : ℝ)) ≤ ((169780945631631436589/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t117.2, ztgcTrioT_t2.2]) (le_trans hm2 (add_le_add_right hπlo ((169780945631631436589/200000000000000000000 : ℝ))))

theorem ztgcTrio_s12_1 : ((18217516232455841111/50000000000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 2 2 ∧ solY 2.52 2 (2 * hminus) 2 2 2 ≤ ((14576334043769359467/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq103, ztgcTrio_eq169, ztgcTrio_eq28]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((18217516232455841111/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((61694381602112141447/50000000000000000000 : ℝ)) + ((53840426283111398607/50000000000000000000 : ℝ)) + ((119524682053453925961/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((18217516232455841111/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t53.1, ztgcTrioT_t110.1, ztgcTrioT_t31.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((246781000624774345041/200000000000000000000 : ℝ)) + ((43072922448584515949/40000000000000000000 : ℝ)) + ((239054588069088520241/200000000000000000000 : ℝ)) ≤ ((14576334043769359467/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t53.2, ztgcTrioT_t110.2, ztgcTrioT_t31.2]) (le_trans hm2 (add_le_add_right hπlo ((14576334043769359467/40000000000000000000 : ℝ))))

theorem ztgcTrio_s12_2 : ((25409742902353012081/50000000000000000000 : ℝ)) ≤ solY 2.52 2 2 2 2 (2 * hminus) ∧ solY 2.52 2 2 2 2 (2 * hminus) ≤ ((101649939761706503813/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq111, ztgcTrio_eq287, ztgcTrio_eq224]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((25409742902353012081/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((61694381602112141447/50000000000000000000 : ℝ)) + ((100903651456755912911/100000000000000000000 : ℝ)) + ((35171584125678788051/25000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((25409742902353012081/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t53.1, ztgcTrioT_t141.1, ztgcTrioT_t150.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((246781000624774345041/200000000000000000000 : ℝ)) + ((201810988923010671481/200000000000000000000 : ℝ)) + ((281376480931860134983/200000000000000000000 : ℝ)) ≤ ((101649939761706503813/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t53.2, ztgcTrioT_t141.2, ztgcTrioT_t150.2]) (le_trans hm2 (add_le_add_right hπlo ((101649939761706503813/200000000000000000000 : ℝ))))

theorem ztgcTrio_s12_3 : ((10631281659924953891/20000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) 2.52 2 2 ∧ solY 2 2 (2 * hminus) 2.52 2 2 ≤ ((106323775571938642223/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq276, ztgcTrio_eq202]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((10631281659924953891/20000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((14688734014840425443/10000000000000000000 : ℝ)) + ((100903651456755912911/100000000000000000000 : ℝ)) + ((119524682053453925961/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((10631281659924953891/20000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t130.1, ztgcTrioT_t141.1, ztgcTrioT_t31.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((293776729297778098193/200000000000000000000 : ℝ)) + ((201810988923010671481/200000000000000000000 : ℝ)) + ((239054588069088520241/200000000000000000000 : ℝ)) ≤ ((106323775571938642223/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t130.2, ztgcTrioT_t141.2, ztgcTrioT_t31.2]) (le_trans hm2 (add_le_add_right hπlo ((106323775571938642223/200000000000000000000 : ℝ))))

theorem ztgcTrio_s12_4 : ((81095263858352880001/100000000000000000000 : ℝ)) ≤ solY 2 2 2 2.52 2 (2 * hminus) ∧ solY 2 2 2 2.52 2 (2 * hminus) ≤ ((162199291754622165229/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq311, ztgcTrio_eq301]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((81095263858352880001/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((14688734014840425443/10000000000000000000 : ℝ)) + ((53840426283111398607/50000000000000000000 : ℝ)) + ((35171584125678788051/25000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((81095263858352880001/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t130.1, ztgcTrioT_t110.1, ztgcTrioT_t150.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((293776729297778098193/200000000000000000000 : ℝ)) + ((43072922448584515949/40000000000000000000 : ℝ)) + ((281376480931860134983/200000000000000000000 : ℝ)) ≤ ((162199291754622165229/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t130.2, ztgcTrioT_t110.2, ztgcTrioT_t150.2]) (le_trans hm2 (add_le_add_right hπlo ((162199291754622165229/200000000000000000000 : ℝ))))

theorem ztgcTrio_s13_1 : ((839240324820873829157/2000000000000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 2 (2 * hminus) ∧ solY 2.52 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((419710220021435569869/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq100, ztgcTrio_eq22]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((839240324820873829157/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((105555274996396205067/100000000000000000000 : ℝ)) + ((606202703181137297/640000000000000000 : ℝ)) + ((194808542789480134477/125000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((839240324820873829157/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t61.1, ztgcTrioT_t107.1, ztgcTrioT_t25.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((211116897887008951973/200000000000000000000 : ℝ)) + ((47361200212244597893/50000000000000000000 : ℝ)) + ((389623594982798022651/250000000000000000000 : ℝ)) ≤ ((419710220021435569869/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t61.2, ztgcTrioT_t107.2, ztgcTrioT_t25.2]) (le_trans hm2 (add_le_add_right hπlo ((419710220021435569869/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s13_2 : ((839240324820873829157/2000000000000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 2 (2 * hminus) ∧ solY 2.52 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((419710220021435569869/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq100, ztgcTrio_eq22]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((839240324820873829157/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((105555274996396205067/100000000000000000000 : ℝ)) + ((606202703181137297/640000000000000000 : ℝ)) + ((194808542789480134477/125000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((839240324820873829157/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t61.1, ztgcTrioT_t107.1, ztgcTrioT_t25.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((211116897887008951973/200000000000000000000 : ℝ)) + ((47361200212244597893/50000000000000000000 : ℝ)) + ((389623594982798022651/250000000000000000000 : ℝ)) ≤ ((419710220021435569869/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t61.2, ztgcTrioT_t107.2, ztgcTrioT_t25.2]) (le_trans hm2 (add_le_add_right hπlo ((419710220021435569869/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s13_3 : ((1262160907408323245697/2000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) 2.52 2 (2 * hminus) ∧ solY 2 2 (2 * hminus) 2.52 2 (2 * hminus) ≤ ((631167295178705866059/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq194]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1262160907408323245697/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((63350652062884337947/50000000000000000000 : ℝ)) + ((606202703181137297/640000000000000000 : ℝ)) + ((194808542789480134477/125000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1262160907408323245697/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t129.1, ztgcTrioT_t107.1, ztgcTrioT_t25.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((253408312918463011211/200000000000000000000 : ℝ)) + ((47361200212244597893/50000000000000000000 : ℝ)) + ((389623594982798022651/250000000000000000000 : ℝ)) ≤ ((631167295178705866059/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t129.2, ztgcTrioT_t107.2, ztgcTrioT_t25.2]) (le_trans hm2 (add_le_add_right hπlo ((631167295178705866059/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s13_4 : ((1262160907408323245697/2000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) 2.52 2 (2 * hminus) ∧ solY 2 2 (2 * hminus) 2.52 2 (2 * hminus) ≤ ((631167295178705866059/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq194]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1262160907408323245697/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((63350652062884337947/50000000000000000000 : ℝ)) + ((606202703181137297/640000000000000000 : ℝ)) + ((194808542789480134477/125000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1262160907408323245697/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t129.1, ztgcTrioT_t107.1, ztgcTrioT_t25.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((253408312918463011211/200000000000000000000 : ℝ)) + ((47361200212244597893/50000000000000000000 : ℝ)) + ((389623594982798022651/250000000000000000000 : ℝ)) ≤ ((631167295178705866059/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t129.2, ztgcTrioT_t107.2, ztgcTrioT_t25.2]) (le_trans hm2 (add_le_add_right hπlo ((631167295178705866059/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s14_1 : ((1337386894449356471/3125000000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 ∧ solY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((17121493118235217913/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq164]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1337386894449356471/3125000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((111513535926234496279/100000000000000000000 : ℝ)) + ((27352026969511783927/20000000000000000000 : ℝ)) + ((21736395041515063001/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1337386894449356471/3125000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t50.1, ztgcTrioT_t102.1, ztgcTrioT_t17.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((223032905623993037471/200000000000000000000 : ℝ)) + ((273523858699687463341/200000000000000000000 : ℝ)) + ((43473846397086847289/40000000000000000000 : ℝ)) ≤ ((17121493118235217913/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t50.2, ztgcTrioT_t102.2, ztgcTrioT_t17.2]) (le_trans hm2 (add_le_add_right hπlo ((17121493118235217913/40000000000000000000 : ℝ))))

theorem ztgcTrio_s14_2 : ((1337386894449356471/3125000000000000000 : ℝ)) ≤ solY 2.52 (2 * hminus) 2 2 2 (2 * hminus) ∧ solY 2.52 (2 * hminus) 2 2 2 (2 * hminus) ≤ ((17121493118235217913/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq83, ztgcTrio_eq56, ztgcTrio_eq206]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1337386894449356471/3125000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((111513535926234496279/100000000000000000000 : ℝ)) + ((21736395041515063001/20000000000000000000 : ℝ)) + ((27352026969511783927/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1337386894449356471/3125000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t50.1, ztgcTrioT_t17.1, ztgcTrioT_t102.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((223032905623993037471/200000000000000000000 : ℝ)) + ((43473846397086847289/40000000000000000000 : ℝ)) + ((273523858699687463341/200000000000000000000 : ℝ)) ≤ ((17121493118235217913/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t50.2, ztgcTrioT_t17.2, ztgcTrioT_t102.2]) (le_trans hm2 (add_le_add_right hπlo ((17121493118235217913/40000000000000000000 : ℝ))))

theorem ztgcTrio_s14_3 : ((11126999409245204217/25000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (2 * hminus) 2.52 2 2 ∧ solY 2 (2 * hminus) (2 * hminus) 2.52 2 2 ≤ ((89036879012176240211/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq153, ztgcTrio_eq15, ztgcTrio_eq50]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((11126999409245204217/25000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((28260662516163902141/20000000000000000000 : ℝ)) + ((21736395041515063001/20000000000000000000 : ℝ)) + ((21736395041515063001/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((11126999409245204217/25000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t92.1, ztgcTrioT_t17.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((282616945759246415013/200000000000000000000 : ℝ)) + ((43473846397086847289/40000000000000000000 : ℝ)) + ((43473846397086847289/40000000000000000000 : ℝ)) ≤ ((89036879012176240211/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t92.2, ztgcTrioT_t17.2]) (le_trans hm2 (add_le_add_right hπlo ((89036879012176240211/200000000000000000000 : ℝ))))

theorem ztgcTrio_s14_4 : ((6291519807309251633/6250000000000000000 : ℝ)) ≤ solY 2 2 2 2.52 (2 * hminus) (2 * hminus) ∧ solY 2 2 2 2.52 (2 * hminus) (2 * hminus) ≤ ((201346132440682694003/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq299]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((6291519807309251633/6250000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((28260662516163902141/20000000000000000000 : ℝ)) + ((27352026969511783927/20000000000000000000 : ℝ)) + ((27352026969511783927/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((6291519807309251633/6250000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t92.1, ztgcTrioT_t102.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((282616945759246415013/200000000000000000000 : ℝ)) + ((273523858699687463341/200000000000000000000 : ℝ)) + ((273523858699687463341/200000000000000000000 : ℝ)) ≤ ((201346132440682694003/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t92.2, ztgcTrioT_t102.2]) (le_trans hm2 (add_le_add_right hπlo ((201346132440682694003/200000000000000000000 : ℝ))))

theorem ztgcTrio_s15_1 : ((6399746997479621471/12500000000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ solY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((102417653509864195069/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq97, ztgcTrio_eq163]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((6399746997479621471/12500000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((20655510982699535937/20000000000000000000 : ℝ)) + ((3032127677935233951/2500000000000000000 : ℝ)) + ((14079457930791925789/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((6399746997479621471/12500000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t45.1, ztgcTrioT_t100.1, ztgcTrioT_t24.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((41312528297451453183/40000000000000000000 : ℝ)) + ((242579220606856552517/200000000000000000000 : ℝ)) + ((281594322133689024329/200000000000000000000 : ℝ)) ≤ ((102417653509864195069/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t45.2, ztgcTrioT_t100.2, ztgcTrioT_t24.2]) (le_trans hm2 (add_le_add_right hπlo ((102417653509864195069/200000000000000000000 : ℝ))))

theorem ztgcTrio_s15_2 : ((37474256012808223187/100000000000000000000 : ℝ)) ≤ solY 2.52 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ solY 2.52 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((74976504877548071993/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq79, ztgcTrio_eq6]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((37474256012808223187/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((20655510982699535937/20000000000000000000 : ℝ)) + ((101720469107867785339/100000000000000000000 : ℝ)) + ((14663549735043208201/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((37474256012808223187/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t45.1, ztgcTrioT_t6.1, ztgcTrioT_t21.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((41312528297451453183/40000000000000000000 : ℝ)) + ((203451584727644819747/200000000000000000000 : ℝ)) + ((293280809380584634023/200000000000000000000 : ℝ)) ≤ ((74976504877548071993/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t45.2, ztgcTrioT_t6.2, ztgcTrioT_t21.2]) (le_trans hm2 (add_le_add_right hπlo ((74976504877548071993/200000000000000000000 : ℝ))))

theorem ztgcTrio_s15_3 : ((53387931936544582033/100000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (2 * hminus) 2.52 2 (2 * hminus) ∧ solY 2 (2 * hminus) (2 * hminus) 2.52 2 (2 * hminus) ≤ ((106797751655592792159/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq152, ztgcTrio_eq14, ztgcTrio_eq46]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((53387931936544582033/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((125032148879746862651/100000000000000000000 : ℝ)) + ((101720469107867785339/100000000000000000000 : ℝ)) + ((14079457930791925789/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((53387931936544582033/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t91.1, ztgcTrioT_t6.1, ztgcTrioT_t24.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((10002815020487903831/8000000000000000000 : ℝ)) + ((203451584727644819747/200000000000000000000 : ℝ)) + ((281594322133689024329/200000000000000000000 : ℝ)) ≤ ((106797751655592792159/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t91.2, ztgcTrioT_t6.2, ztgcTrioT_t24.2]) (le_trans hm2 (add_le_add_right hπlo ((106797751655592792159/200000000000000000000 : ℝ))))

theorem ztgcTrio_s15_4 : ((39396743994299489427/50000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) 2.52 (2 * hminus) (2 * hminus) ∧ solY 2 2 (2 * hminus) 2.52 (2 * hminus) (2 * hminus) ≤ ((157611874781700134623/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq181, ztgcTrio_eq64]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((39396743994299489427/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((125032148879746862651/100000000000000000000 : ℝ)) + ((3032127677935233951/2500000000000000000 : ℝ)) + ((14663549735043208201/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((39396743994299489427/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t91.1, ztgcTrioT_t100.1, ztgcTrioT_t21.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((10002815020487903831/8000000000000000000 : ℝ)) + ((242579220606856552517/200000000000000000000 : ℝ)) + ((293280809380584634023/200000000000000000000 : ℝ)) ≤ ((157611874781700134623/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t91.2, ztgcTrioT_t100.2, ztgcTrioT_t21.2]) (le_trans hm2 (add_le_add_right hπlo ((157611874781700134623/200000000000000000000 : ℝ))))

theorem ztgcTrio_s16_1 : ((17799257380265211687/50000000000000000000 : ℝ)) ≤ solY 2.52 2 2.52 2 2 2 ∧ solY 2.52 2 2.52 2 2 2 ≤ ((71197030745105153171/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq90]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((17799257380265211687/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((60623159968524661929/50000000000000000000 : ℝ)) + ((21453028049084219901/20000000000000000000 : ℝ)) + ((60623159968524661929/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((17799257380265211687/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t56.1, ztgcTrioT_t146.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((48498528056419992293/40000000000000000000 : ℝ)) + ((214530280898843877933/200000000000000000000 : ℝ)) + ((48498528056419992293/40000000000000000000 : ℝ)) ≤ ((71197030745105153171/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t56.2, ztgcTrioT_t146.2]) (le_trans hm2 (add_le_add_right hπlo ((71197030745105153171/200000000000000000000 : ℝ))))

theorem ztgcTrio_s16_2 : ((10331444662651632189/20000000000000000000 : ℝ)) ≤ solY 2.52 2 2 2 2 2.52 ∧ solY 2.52 2 2 2 2 2.52 ≤ ((103314447850559942451/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq112, ztgcTrio_eq225]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((10331444662651632189/20000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((60623159968524661929/50000000000000000000 : ℝ)) + ((99687173333420022677/100000000000000000000 : ℝ)) + ((144882995401778138257/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((10331444662651632189/20000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t56.1, ztgcTrioT_t156.1, ztgcTrioT_t152.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((48498528056419992293/40000000000000000000 : ℝ)) + ((199374347074841869121/200000000000000000000 : ℝ)) + ((289765991211556759557/200000000000000000000 : ℝ)) ≤ ((103314447850559942451/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t56.2, ztgcTrioT_t156.2, ztgcTrioT_t152.2]) (le_trans hm2 (add_le_add_right hπlo ((103314447850559942451/200000000000000000000 : ℝ))))

theorem ztgcTrio_s16_3 : ((10331444662651632189/20000000000000000000 : ℝ)) ≤ solY 2 2 2.52 2.52 2 2 ∧ solY 2 2 2.52 2.52 2 2 ≤ ((103314447850559942451/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq285, ztgcTrio_eq231, ztgcTrio_eq110]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((10331444662651632189/20000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((144882995401778138257/100000000000000000000 : ℝ)) + ((99687173333420022677/100000000000000000000 : ℝ)) + ((60623159968524661929/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((10331444662651632189/20000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t152.1, ztgcTrioT_t156.1, ztgcTrioT_t56.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((289765991211556759557/200000000000000000000 : ℝ)) + ((199374347074841869121/200000000000000000000 : ℝ)) + ((48498528056419992293/40000000000000000000 : ℝ)) ≤ ((103314447850559942451/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t152.2, ztgcTrioT_t156.2, ztgcTrioT_t56.2]) (le_trans hm2 (add_le_add_right hπlo ((103314447850559942451/200000000000000000000 : ℝ))))

theorem ztgcTrio_s16_4 : ((20717966422497013043/25000000000000000000 : ℝ)) ≤ solY 2 2 2 2.52 2 2.52 ∧ solY 2 2 2 2.52 2 2.52 ≤ ((33148746520803749871/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq324, ztgcTrio_eq309]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((20717966422497013043/25000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((144882995401778138257/100000000000000000000 : ℝ)) + ((21453028049084219901/20000000000000000000 : ℝ)) + ((144882995401778138257/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((20717966422497013043/25000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t152.1, ztgcTrioT_t146.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((289765991211556759557/200000000000000000000 : ℝ)) + ((214530280898843877933/200000000000000000000 : ℝ)) + ((289765991211556759557/200000000000000000000 : ℝ)) ≤ ((33148746520803749871/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t152.2, ztgcTrioT_t146.2]) (le_trans hm2 (add_le_add_right hπlo ((33148746520803749871/40000000000000000000 : ℝ))))

theorem ztgcTrio_s17_1 : ((814381539623011326741/2000000000000000000000 : ℝ)) ≤ solY 2.52 2 2.52 2 2 (2 * hminus) ∧ solY 2.52 2 2.52 2 2 (2 * hminus) ≤ ((203628928468524130877/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq105, ztgcTrio_eq219, ztgcTrio_eq88]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((814381539623011326741/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((6443032999450695269/6250000000000000000 : ℝ)) + ((374012614695620396789/400000000000000000000 : ℝ)) + ((395716651687559166707/250000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((814381539623011326741/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t62.1, ztgcTrioT_t135.1, ztgcTrioT_t55.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((206182023889942119371/200000000000000000000 : ℝ)) + ((93505606205449103547/100000000000000000000 : ℝ)) + ((1582884329022539867889/1000000000000000000000 : ℝ)) ≤ ((203628928468524130877/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t62.2, ztgcTrioT_t135.2, ztgcTrioT_t55.2]) (le_trans hm2 (add_le_add_right hπlo ((203628928468524130877/500000000000000000000 : ℝ))))

theorem ztgcTrio_s17_2 : ((847258836609165564809/2000000000000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 2 2.52 ∧ solY 2.52 2 (2 * hminus) 2 2 2.52 ≤ ((105921707181195783431/250000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq101, ztgcTrio_eq23]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((847258836609165564809/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((6443032999450695269/6250000000000000000 : ℝ)) + ((371048301274298193529/400000000000000000000 : ℝ)) + ((401679009699154823503/250000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((847258836609165564809/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t62.1, ztgcTrioT_t108.1, ztgcTrioT_t26.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((206182023889942119371/200000000000000000000 : ℝ)) + ((92764269905373828469/100000000000000000000 : ℝ)) + ((1606726663811027490639/1000000000000000000000 : ℝ)) ≤ ((105921707181195783431/250000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t62.2, ztgcTrioT_t108.2, ztgcTrioT_t26.2]) (le_trans hm2 (add_le_add_right hπlo ((105921707181195783431/250000000000000000000 : ℝ))))

theorem ztgcTrio_s17_3 : ((1217842391910392974861/2000000000000000000000 : ℝ)) ≤ solY 2 2 2.52 2.52 2 (2 * hminus) ∧ solY 2 2 2.52 2.52 2 (2 * hminus) ≤ ((304490919682110730247/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq284, ztgcTrio_eq228, ztgcTrio_eq109]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1217842391910392974861/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((4960105958436430301/4000000000000000000 : ℝ)) + ((371048301274298193529/400000000000000000000 : ℝ)) + ((395716651687559166707/250000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1217842391910392974861/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t151.1, ztgcTrioT_t108.1, ztgcTrioT_t55.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((9920379719021092371/8000000000000000000 : ℝ)) + ((92764269905373828469/100000000000000000000 : ℝ)) + ((1582884329022539867889/1000000000000000000000 : ℝ)) ≤ ((304490919682110730247/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t151.2, ztgcTrioT_t108.2, ztgcTrioT_t55.2]) (le_trans hm2 (add_le_add_right hπlo ((304490919682110730247/500000000000000000000 : ℝ))))

theorem ztgcTrio_s17_4 : ((1280362823109769245529/2000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) 2.52 2 2.52 ∧ solY 2 2 (2 * hminus) 2.52 2 2.52 ≤ ((80029692144182729253/125000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq274, ztgcTrio_eq197]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1280362823109769245529/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((4960105958436430301/4000000000000000000 : ℝ)) + ((374012614695620396789/400000000000000000000 : ℝ)) + ((401679009699154823503/250000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1280362823109769245529/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t151.1, ztgcTrioT_t135.1, ztgcTrioT_t26.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((9920379719021092371/8000000000000000000 : ℝ)) + ((93505606205449103547/100000000000000000000 : ℝ)) + ((1606726663811027490639/1000000000000000000000 : ℝ)) ≤ ((80029692144182729253/125000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t151.2, ztgcTrioT_t135.2, ztgcTrioT_t26.2]) (le_trans hm2 (add_le_add_right hπlo ((80029692144182729253/125000000000000000000 : ℝ))))

theorem ztgcTrio_s18_1 : ((522353309683672727/1250000000000000000 : ℝ)) ≤ solY 2.52 2 2.52 2 (2 * hminus) 2 ∧ solY 2.52 2 2.52 2 (2 * hminus) 2 ≤ ((83584400605119445981/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq218, ztgcTrio_eq89]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((522353309683672727/1250000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((2747390430343595661/2500000000000000000 : ℝ)) + ((136156295706195489127/100000000000000000000 : ℝ)) + ((2747390430343595661/2500000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((522353309683672727/1250000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t51.1, ztgcTrioT_t145.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((8791745527868926831/8000000000000000000 : ℝ)) + ((272315654929611752123/200000000000000000000 : ℝ)) + ((8791745527868926831/8000000000000000000 : ℝ)) ≤ ((83584400605119445981/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t51.2, ztgcTrioT_t145.2]) (le_trans hm2 (add_le_add_right hπlo ((83584400605119445981/200000000000000000000 : ℝ))))

theorem ztgcTrio_s18_2 : ((43437029312702146129/100000000000000000000 : ℝ)) ≤ solY 2.52 (2 * hminus) 2 2 2 2.52 ∧ solY 2.52 (2 * hminus) 2 2 2 2.52 ≤ ((86881853605210640999/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq84, ztgcTrio_eq208]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((43437029312702146129/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((2747390430343595661/2500000000000000000 : ℝ)) + ((107169943338377136969/100000000000000000000 : ℝ)) + ((140530734119570506567/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((43437029312702146129/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t51.1, ztgcTrioT_t28.1, ztgcTrioT_t104.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((8791745527868926831/8000000000000000000 : ℝ)) + ((214344312937965285413/200000000000000000000 : ℝ)) + ((281062433188460832503/200000000000000000000 : ℝ)) ≤ ((86881853605210640999/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t51.2, ztgcTrioT_t28.2, ztgcTrioT_t104.2]) (le_trans hm2 (add_le_add_right hπlo ((86881853605210640999/200000000000000000000 : ℝ))))

theorem ztgcTrio_s18_3 : ((43437029312702146129/100000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) 2.52 2.52 2 2 ∧ solY 2 (2 * hminus) 2.52 2.52 2 2 ≤ ((86881853605210640999/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq166, ztgcTrio_eq25, ztgcTrio_eq98]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((43437029312702146129/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((140530734119570506567/100000000000000000000 : ℝ)) + ((107169943338377136969/100000000000000000000 : ℝ)) + ((2747390430343595661/2500000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((43437029312702146129/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t104.1, ztgcTrioT_t28.1, ztgcTrioT_t51.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((281062433188460832503/200000000000000000000 : ℝ)) + ((214344312937965285413/200000000000000000000 : ℝ)) + ((8791745527868926831/8000000000000000000 : ℝ)) ≤ ((86881853605210640999/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t104.2, ztgcTrioT_t28.2, ztgcTrioT_t51.2]) (le_trans hm2 (add_le_add_right hπlo ((86881853605210640999/200000000000000000000 : ℝ))))

theorem ztgcTrio_s18_4 : ((51529249293173589207/50000000000000000000 : ℝ)) ≤ solY 2 2 2 2.52 (2 * hminus) 2.52 ∧ solY 2 2 2 2.52 (2 * hminus) 2.52 ≤ ((206121990588594769437/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq307]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((51529249293173589207/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((140530734119570506567/100000000000000000000 : ℝ)) + ((136156295706195489127/100000000000000000000 : ℝ)) + ((140530734119570506567/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((51529249293173589207/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t104.1, ztgcTrioT_t145.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((281062433188460832503/200000000000000000000 : ℝ)) + ((272315654929611752123/200000000000000000000 : ℝ)) + ((281062433188460832503/200000000000000000000 : ℝ)) ≤ ((206121990588594769437/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t104.2, ztgcTrioT_t145.2]) (le_trans hm2 (add_le_add_right hπlo ((206121990588594769437/200000000000000000000 : ℝ))))

theorem ztgcTrio_s19_1 : ((24902100313654952663/50000000000000000000 : ℝ)) ≤ solY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) ∧ solY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) ≤ ((99620711574954410473/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq104, ztgcTrio_eq217, ztgcTrio_eq87]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((24902100313654952663/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((2027398434405461557/2000000000000000000 : ℝ)) + ((120028204711367140949/100000000000000000000 : ℝ)) + ((71282669777329505187/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((24902100313654952663/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t46.1, ztgcTrioT_t124.1, ztgcTrioT_t54.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((202747957067890057373/200000000000000000000 : ℝ)) + ((240058457062213181467/200000000000000000000 : ℝ)) + ((11405313126511592773/8000000000000000000 : ℝ)) ≤ ((99620711574954410473/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t46.2, ztgcTrioT_t124.2, ztgcTrioT_t54.2]) (le_trans hm2 (add_le_add_right hπlo ((99620711574954410473/200000000000000000000 : ℝ))))

theorem ztgcTrio_s19_2 : ((378995715904985624487/1000000000000000000000 : ℝ)) ≤ solY 2.52 (2 * hminus) (2 * hminus) 2 2 2.52 ∧ solY 2.52 (2 * hminus) (2 * hminus) 2 2 2.52 ≤ ((379061166296539872439/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq80, ztgcTrio_eq7, ztgcTrio_eq19]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((378995715904985624487/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((2027398434405461557/2000000000000000000 : ℝ)) + ((1560599470551627697/1562500000000000000 : ℝ)) + ((1508105491139106358377/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((378995715904985624487/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t46.1, ztgcTrioT_t7.1, ztgcTrioT_t22.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((202747957067890057373/200000000000000000000 : ℝ)) + ((199761138359758768247/200000000000000000000 : ℝ)) + ((1508108342747988982799/1000000000000000000000 : ℝ)) ≤ ((379061166296539872439/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t46.2, ztgcTrioT_t7.2, ztgcTrioT_t22.2]) (le_trans hm2 (add_le_add_right hπlo ((379061166296539872439/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s19_3 : ((51904956101700893541/100000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) 2.52 2.52 2 (2 * hminus) ∧ solY 2 (2 * hminus) 2.52 2.52 2 (2 * hminus) ≤ ((103820071718526025081/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq165, ztgcTrio_eq24, ztgcTrio_eq95]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((51904956101700893541/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((61810257895363517203/50000000000000000000 : ℝ)) + ((1560599470551627697/1562500000000000000 : ℝ)) + ((71282669777329505187/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((51904956101700893541/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t103.1, ztgcTrioT_t7.1, ztgcTrioT_t54.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((247244635913916085201/200000000000000000000 : ℝ)) + ((199761138359758768247/200000000000000000000 : ℝ)) + ((11405313126511592773/8000000000000000000 : ℝ)) ≤ ((103820071718526025081/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t103.2, ztgcTrioT_t7.2, ztgcTrioT_t54.2]) (le_trans hm2 (add_le_add_right hπlo ((103820071718526025081/200000000000000000000 : ℝ))))

theorem ztgcTrio_s19_4 : ((803000042570154873457/1000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) 2.52 (2 * hminus) 2.52 ∧ solY 2 2 (2 * hminus) 2.52 (2 * hminus) 2.52 ≤ ((803031154038942077679/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq272, ztgcTrio_eq184]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((803000042570154873457/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((61810257895363517203/50000000000000000000 : ℝ)) + ((120028204711367140949/100000000000000000000 : ℝ)) + ((1508105491139106358377/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((803000042570154873457/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t103.1, ztgcTrioT_t124.1, ztgcTrioT_t22.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((247244635913916085201/200000000000000000000 : ℝ)) + ((240058457062213181467/200000000000000000000 : ℝ)) + ((1508108342747988982799/1000000000000000000000 : ℝ)) ≤ ((803031154038942077679/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t103.2, ztgcTrioT_t124.2, ztgcTrioT_t22.2]) (le_trans hm2 (add_le_add_right hπlo ((803031154038942077679/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s20_1 : ((6115844382924451907/20000000000000000000 : ℝ)) ≤ solY 2.52 2 (Real.sqrt 8) 2 2 2 ∧ solY 2.52 2 (Real.sqrt 8) 2 2 2 ≤ ((61158445053288860403/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq107, ztgcTrio_eq139]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((6115844382924451907/20000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((21685231404168188973/20000000000000000000 : ℝ)) + ((10344706240377846307/10000000000000000000 : ℝ)) + ((132865267848992175447/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((6115844382924451907/20000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t64.1, ztgcTrioT_t167.1, ztgcTrioT_t84.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((43370462889936708593/40000000000000000000 : ℝ)) + ((206894125215558683081/200000000000000000000 : ℝ)) + ((265730536105985282049/200000000000000000000 : ℝ)) ≤ ((61158445053288860403/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t64.2, ztgcTrioT_t167.2, ztgcTrioT_t84.2]) (le_trans hm2 (add_le_add_right hπlo ((61158445053288860403/200000000000000000000 : ℝ))))

theorem ztgcTrio_s20_2 : ((44049444869827645269/80000000000000000000 : ℝ)) ≤ solY 2.52 2 2 2 2 (Real.sqrt 8) ∧ solY 2.52 2 2 2 2 (Real.sqrt 8) ≤ ((27530903349653295613/50000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq113, ztgcTrio_eq288, ztgcTrio_eq227]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((44049444869827645269/80000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((21685231404168188973/20000000000000000000 : ℝ)) + ((366074578688927966001/400000000000000000000 : ℝ)) + ((42319067438300236017/25000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((44049444869827645269/80000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t64.1, ztgcTrioT_t158.1, ztgcTrioT_t155.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((43370462889936708593/40000000000000000000 : ℝ)) + ((45759322438116479/50000000000000000 : ℝ)) + ((338552539914402371179/200000000000000000000 : ℝ)) ≤ ((27530903349653295613/50000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t64.2, ztgcTrioT_t158.2, ztgcTrioT_t155.2]) (le_trans hm2 (add_le_add_right hπlo ((27530903349653295613/50000000000000000000 : ℝ))))

theorem ztgcTrio_s20_3 : ((173053779554389811017/400000000000000000000 : ℝ)) ≤ solY 2 2 (Real.sqrt 8) 2.52 2 2 ∧ solY 2 2 (Real.sqrt 8) 2.52 2 2 ≤ ((43263445500619347337/100000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq293]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((173053779554389811017/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((66519398863181304827/50000000000000000000 : ℝ)) + ((366074578688927966001/400000000000000000000 : ℝ)) + ((132865267848992175447/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((173053779554389811017/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t173.1, ztgcTrioT_t158.1, ztgcTrioT_t84.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((266077595860726144317/200000000000000000000 : ℝ)) + ((45759322438116479/50000000000000000 : ℝ)) + ((265730536105985282049/200000000000000000000 : ℝ)) ≤ ((43263445500619347337/100000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t173.2, ztgcTrioT_t158.2, ztgcTrioT_t84.2]) (le_trans hm2 (add_le_add_right hπlo ((43263445500619347337/100000000000000000000 : ℝ))))

theorem ztgcTrio_s20_4 : ((18320572904870538589/20000000000000000000 : ℝ)) ≤ solY 2 2 2 2.52 2 (Real.sqrt 8) ∧ solY 2 2 2 2.52 2 (Real.sqrt 8) ≤ ((36641146054549710177/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq312, ztgcTrio_eq327, ztgcTrio_eq320]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((18320572904870538589/20000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((66519398863181304827/50000000000000000000 : ℝ)) + ((10344706240377846307/10000000000000000000 : ℝ)) + ((42319067438300236017/25000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((18320572904870538589/20000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t173.1, ztgcTrioT_t167.1, ztgcTrioT_t155.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((266077595860726144317/200000000000000000000 : ℝ)) + ((206894125215558683081/200000000000000000000 : ℝ)) + ((338552539914402371179/200000000000000000000 : ℝ)) ≤ ((36641146054549710177/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t173.2, ztgcTrioT_t167.2, ztgcTrioT_t155.2]) (le_trans hm2 (add_le_add_right hπlo ((36641146054549710177/40000000000000000000 : ℝ))))

theorem ztgcTrio_s21_1 : ((331438054681413340137/1000000000000000000000 : ℝ)) ≤ solY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) ∧ solY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) ≤ ((165765185626196644099/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq255, ztgcTrio_eq137]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((331438054681413340137/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((1751305615179934068249/2000000000000000000000 : ℝ)) + ((337290296783636222253/400000000000000000000 : ℝ)) + ((35083043174444979777/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((331438054681413340137/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t63.1, ztgcTrioT_t138.1, ztgcTrioT_t82.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((875685035310861236239/1000000000000000000000 : ℝ)) + ((421628752769586407227/500000000000000000000 : ℝ)) + ((350836096798410495193/200000000000000000000 : ℝ)) ≤ ((165765185626196644099/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t63.2, ztgcTrioT_t138.2, ztgcTrioT_t82.2]) (le_trans hm2 (add_le_add_right hπlo ((165765185626196644099/500000000000000000000 : ℝ))))

theorem ztgcTrio_s21_2 : ((213849592342576038053/500000000000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 2 (Real.sqrt 8) ∧ solY 2.52 2 (2 * hminus) 2 2 (Real.sqrt 8) ≤ ((106947567191518460287/250000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq102, ztgcTrio_eq168]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((213849592342576038053/500000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((1751305615179934068249/2000000000000000000000 : ℝ)) + ((1597338108360766933643/2000000000000000000000 : ℝ)) + ((189496997650469481363/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((213849592342576038053/500000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t63.1, ztgcTrioT_t109.1, ztgcTrioT_t27.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((875685035310861236239/1000000000000000000000 : ℝ)) + ((199674536460273846021/250000000000000000000 : ℝ)) + ((378999948240762091857/200000000000000000000 : ℝ)) ≤ ((106947567191518460287/250000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t63.2, ztgcTrioT_t109.2, ztgcTrioT_t27.2]) (le_trans hm2 (add_le_add_right hπlo ((106947567191518460287/250000000000000000000 : ℝ))))

theorem ztgcTrio_s21_3 : ((965046776022151016203/2000000000000000000000 : ℝ)) ≤ solY 2 2 (Real.sqrt 8) 2.52 2 (2 * hminus) ∧ solY 2 2 (Real.sqrt 8) 2.52 2 (2 * hminus) ≤ ((241306005348375627247/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq292, ztgcTrio_eq267]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((965046776022151016203/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((10712948286983362909/10000000000000000000 : ℝ)) + ((1597338108360766933643/2000000000000000000000 : ℝ)) + ((35083043174444979777/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((965046776022151016203/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t172.1, ztgcTrioT_t109.1, ztgcTrioT_t82.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((214265206890659326581/200000000000000000000 : ℝ)) + ((199674536460273846021/250000000000000000000 : ℝ)) + ((350836096798410495193/200000000000000000000 : ℝ)) ≤ ((241306005348375627247/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t172.2, ztgcTrioT_t109.2, ztgcTrioT_t82.2]) (le_trans hm2 (add_le_add_right hπlo ((241306005348375627247/500000000000000000000 : ℝ))))

theorem ztgcTrio_s21_4 : ((267159157428891368677/400000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) 2.52 2 (Real.sqrt 8) ∧ solY 2 2 (2 * hminus) 2.52 2 (Real.sqrt 8) ≤ ((83498828450823333523/125000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq275, ztgcTrio_eq199, ztgcTrio_eq72]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((267159157428891368677/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((10712948286983362909/10000000000000000000 : ℝ)) + ((337290296783636222253/400000000000000000000 : ℝ)) + ((189496997650469481363/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((267159157428891368677/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t172.1, ztgcTrioT_t138.1, ztgcTrioT_t27.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((214265206890659326581/200000000000000000000 : ℝ)) + ((421628752769586407227/500000000000000000000 : ℝ)) + ((378999948240762091857/200000000000000000000 : ℝ)) ≤ ((83498828450823333523/125000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t172.2, ztgcTrioT_t138.2, ztgcTrioT_t27.2]) (le_trans hm2 (add_le_add_right hπlo ((83498828450823333523/125000000000000000000 : ℝ))))

theorem ztgcTrio_s22_1 : ((36074916552452782523/100000000000000000000 : ℝ)) ≤ solY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 ∧ solY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 ≤ ((72160042129062998027/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq106, ztgcTrio_eq254, ztgcTrio_eq138]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((36074916552452782523/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((100077274623951082549/100000000000000000000 : ℝ)) + ((33038071677963996427/25000000000000000000 : ℝ)) + ((118004620575635038113/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((36074916552452782523/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t52.1, ztgcTrioT_t166.1, ztgcTrioT_t83.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((200157898609740324389/200000000000000000000 : ℝ)) + ((264308165447616271861/200000000000000000000 : ℝ)) + ((236012508789645049469/200000000000000000000 : ℝ)) ≤ ((72160042129062998027/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t52.2, ztgcTrioT_t166.2, ztgcTrioT_t83.2]) (le_trans hm2 (add_le_add_right hπlo ((72160042129062998027/200000000000000000000 : ℝ))))

theorem ztgcTrio_s22_2 : ((92256964615178534571/200000000000000000000 : ℝ)) ≤ solY 2.52 (2 * hminus) 2 2 2 (Real.sqrt 8) ∧ solY 2.52 (2 * hminus) 2 2 2 (Real.sqrt 8) ≤ ((115333361764113398899/250000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq85, ztgcTrio_eq211]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((92256964615178534571/200000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((100077274623951082549/100000000000000000000 : ℝ)) + ((97886851619379889043/100000000000000000000 : ℝ)) + ((324647242846495239081/200000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((92256964615178534571/200000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t52.1, ztgcTrioT_t30.1, ztgcTrioT_t144.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((200157898609740324389/200000000000000000000 : ℝ)) + ((195779291850156372743/200000000000000000000 : ℝ)) + ((405810037086665837099/250000000000000000000 : ℝ)) ≤ ((115333361764113398899/250000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t52.2, ztgcTrioT_t30.2, ztgcTrioT_t144.2]) (le_trans hm2 (add_le_add_right hπlo ((115333361764113398899/250000000000000000000 : ℝ))))

theorem ztgcTrio_s22_3 : ((9350002074830683537/25000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 2 ∧ solY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 2 ≤ ((74809873612397905041/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq43]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((9350002074830683537/25000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((135667801463297130839/100000000000000000000 : ℝ)) + ((97886851619379889043/100000000000000000000 : ℝ)) + ((118004620575635038113/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((9350002074830683537/25000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t120.1, ztgcTrioT_t30.1, ztgcTrioT_t83.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((271336603690535130521/200000000000000000000 : ℝ)) + ((195779291850156372743/200000000000000000000 : ℝ)) + ((236012508789645049469/200000000000000000000 : ℝ)) ≤ ((74809873612397905041/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t120.2, ztgcTrioT_t30.2, ztgcTrioT_t83.2]) (le_trans hm2 (add_le_add_right hπlo ((74809873612397905041/200000000000000000000 : ℝ))))

theorem ztgcTrio_s22_4 : ((231968888478822824481/200000000000000000000 : ℝ)) ≤ solY 2 2 2 2.52 (2 * hminus) (Real.sqrt 8) ∧ solY 2 2 2 2.52 (2 * hminus) (Real.sqrt 8) ≤ ((579935670223863560923/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq308, ztgcTrio_eq319]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((231968888478822824481/200000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((135667801463297130839/100000000000000000000 : ℝ)) + ((33038071677963996427/25000000000000000000 : ℝ)) + ((324647242846495239081/200000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((231968888478822824481/200000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t120.1, ztgcTrioT_t166.1, ztgcTrioT_t144.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((271336603690535130521/200000000000000000000 : ℝ)) + ((264308165447616271861/200000000000000000000 : ℝ)) + ((405810037086665837099/250000000000000000000 : ℝ)) ≤ ((579935670223863560923/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t120.2, ztgcTrioT_t166.2, ztgcTrioT_t144.2]) (le_trans hm2 (add_le_add_right hπlo ((579935670223863560923/500000000000000000000 : ℝ))))

theorem ztgcTrio_s23_1 : ((835938560938915470671/2000000000000000000000 : ℝ)) ≤ solY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ∧ solY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ≤ ((209013266026239127821/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq253]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((835938560938915470671/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((358394044511127596341/400000000000000000000 : ℝ)) + ((27926252603403073557/25000000000000000000 : ℝ)) + ((1546526718645409040673/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((835938560938915470671/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t47.1, ztgcTrioT_t126.1, ztgcTrioT_t81.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((5600147596286243/6250000000000000 : ℝ)) + ((223411916269053594659/200000000000000000000 : ℝ)) + ((1546535988891104640807/1000000000000000000000 : ℝ)) ≤ ((209013266026239127821/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t47.2, ztgcTrioT_t126.2, ztgcTrioT_t81.2]) (le_trans hm2 (add_le_add_right hπlo ((209013266026239127821/500000000000000000000 : ℝ))))

theorem ztgcTrio_s23_2 : ((39149442965142297021/100000000000000000000 : ℝ)) ≤ solY 2.52 (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) ∧ solY 2.52 (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) ≤ ((7831358089125325787/20000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq81, ztgcTrio_eq8, ztgcTrio_eq20]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((39149442965142297021/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((358394044511127596341/400000000000000000000 : ℝ)) + ((353727550941508231907/400000000000000000000 : ℝ)) + ((87639154730486331903/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((39149442965142297021/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t47.1, ztgcTrioT_t8.1, ztgcTrioT_t23.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((5600147596286243/6250000000000000 : ℝ)) + ((176868680593933769287/200000000000000000000 : ℝ)) + ((14022348317363934411/8000000000000000000 : ℝ)) ≤ ((7831358089125325787/20000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t47.2, ztgcTrioT_t8.2, ztgcTrioT_t23.2]) (le_trans hm2 (add_le_add_right hπlo ((7831358089125325787/20000000000000000000 : ℝ))))

theorem ztgcTrio_s23_3 : ((868798009850155129061/2000000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 (2 * hminus) ∧ solY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 (2 * hminus) ≤ ((434451812858751264847/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq40, ztgcTrio_eq145]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((868798009850155129061/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((7157162890723694891/6250000000000000000 : ℝ)) + ((353727550941508231907/400000000000000000000 : ℝ)) + ((1546526718645409040673/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((868798009850155129061/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t119.1, ztgcTrioT_t8.1, ztgcTrioT_t81.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((229033014917534203213/200000000000000000000 : ℝ)) + ((176868680593933769287/200000000000000000000 : ℝ)) + ((1546535988891104640807/1000000000000000000000 : ℝ)) ≤ ((434451812858751264847/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t119.2, ztgcTrioT_t8.2, ztgcTrioT_t81.2]) (le_trans hm2 (add_le_add_right hπlo ((434451812858751264847/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s23_4 : ((87338660767174752443/100000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) 2.52 (2 * hminus) (Real.sqrt 8) ∧ solY 2 2 (2 * hminus) 2.52 (2 * hminus) (Real.sqrt 8) ≤ ((34937021680549502091/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq273, ztgcTrio_eq187, ztgcTrio_eq71]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((87338660767174752443/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((7157162890723694891/6250000000000000000 : ℝ)) + ((27926252603403073557/25000000000000000000 : ℝ)) + ((87639154730486331903/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((87338660767174752443/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t119.1, ztgcTrioT_t126.1, ztgcTrioT_t23.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((229033014917534203213/200000000000000000000 : ℝ)) + ((223411916269053594659/200000000000000000000 : ℝ)) + ((14022348317363934411/8000000000000000000 : ℝ)) ≤ ((34937021680549502091/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t119.2, ztgcTrioT_t126.2, ztgcTrioT_t23.2]) (le_trans hm2 (add_le_add_right hπlo ((34937021680549502091/40000000000000000000 : ℝ))))

theorem ztgcTrio_s24_1 : ((34264891872146487567/100000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 2 2 ∧ solY (2 * hplus) 2 (2 * hminus) 2 2 2 ≤ ((68541552566725829539/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq123, ztgcTrio_eq175]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((34264891872146487567/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((127946324982828187619/100000000000000000000 : ℝ)) + ((106030032102577501831/100000000000000000000 : ℝ)) + ((28611950036432530491/25000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((34264891872146487567/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t74.1, ztgcTrioT_t116.1, ztgcTrioT_t40.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((51179212374569044243/40000000000000000000 : ℝ)) + ((212062860582860349553/200000000000000000000 : ℝ)) + ((228901160828958906463/200000000000000000000 : ℝ)) ≤ ((68541552566725829539/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t74.2, ztgcTrioT_t116.2, ztgcTrioT_t40.2]) (le_trans hm2 (add_le_add_right hπlo ((68541552566725829539/200000000000000000000 : ℝ))))

theorem ztgcTrio_s24_2 : ((9461728993957061811/20000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2 2 2 (2 * hminus) ∧ solY (2 * hplus) 2 2 2 2 (2 * hminus) ≤ ((18925694898622455291/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq131, ztgcTrio_eq239]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((9461728993957061811/20000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((127946324982828187619/100000000000000000000 : ℝ)) + ((48803001069332032559/50000000000000000000 : ℝ)) + ((27183116641456476033/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((9461728993957061811/20000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t74.1, ztgcTrioT_t142.1, ztgcTrioT_t161.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((51179212374569044243/40000000000000000000 : ℝ)) + ((195215758417795552447/200000000000000000000 : ℝ)) + ((54367036984082030097/40000000000000000000 : ℝ)) ≤ ((18925694898622455291/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t74.2, ztgcTrioT_t142.2, ztgcTrioT_t161.2]) (le_trans hm2 (add_le_add_right hπlo ((18925694898622455291/40000000000000000000 : ℝ))))

theorem ztgcTrio_s24_3 : ((685740911191774765929/1250000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hplus) 2 2 ∧ solY 2 2 (2 * hminus) (2 * hplus) 2 2 ≤ ((1371616666347632392749/2500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq281, ztgcTrio_eq203, ztgcTrio_eq76]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((685740911191774765929/1250000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((3924118399248427950983/2500000000000000000000 : ℝ)) + ((48803001069332032559/50000000000000000000 : ℝ)) + ((28611950036432530491/25000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((685740911191774765929/1250000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t132.1, ztgcTrioT_t142.1, ztgcTrioT_t40.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((981034202434358688131/625000000000000000000 : ℝ)) + ((195215758417795552447/200000000000000000000 : ℝ)) + ((228901160828958906463/200000000000000000000 : ℝ)) ≤ ((1371616666347632392749/2500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t132.2, ztgcTrioT_t142.2, ztgcTrioT_t40.2]) (le_trans hm2 (add_le_add_right hπlo ((1371616666347632392749/2500000000000000000000 : ℝ))))

theorem ztgcTrio_s24_4 : ((529694287005047976177/625000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hplus) 2 (2 * hminus) ∧ solY 2 2 2 (2 * hplus) 2 (2 * hminus) ≤ ((2118880744554082906849/2500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq314, ztgcTrio_eq322, ztgcTrio_eq302]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((529694287005047976177/625000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((3924118399248427950983/2500000000000000000000 : ℝ)) + ((106030032102577501831/100000000000000000000 : ℝ)) + ((27183116641456476033/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((529694287005047976177/625000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t132.1, ztgcTrioT_t116.1, ztgcTrioT_t161.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((981034202434358688131/625000000000000000000 : ℝ)) + ((212062860582860349553/200000000000000000000 : ℝ)) + ((54367036984082030097/40000000000000000000 : ℝ)) ≤ ((2118880744554082906849/2500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t132.2, ztgcTrioT_t116.2, ztgcTrioT_t161.2]) (le_trans hm2 (add_le_add_right hπlo ((2118880744554082906849/2500000000000000000000 : ℝ))))

theorem ztgcTrio_s25_1 : ((160133371217304849123/400000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ solY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((100106395142431538059/250000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq121, ztgcTrio_eq172, ztgcTrio_eq34]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((160133371217304849123/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((54777465021194071293/50000000000000000000 : ℝ)) + ((377619211298579237637/400000000000000000000 : ℝ)) + ((60093150118513033653/40000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((160133371217304849123/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t71.1, ztgcTrioT_t113.1, ztgcTrioT_t36.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((219116153473475067173/200000000000000000000 : ℝ)) + ((94408021705809893399/100000000000000000000 : ℝ)) + ((1502357249733945120841/1000000000000000000000 : ℝ)) ≤ ((100106395142431538059/250000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t71.2, ztgcTrioT_t113.2, ztgcTrioT_t36.2]) (le_trans hm2 (add_le_add_right hπlo ((100106395142431538059/250000000000000000000 : ℝ))))

theorem ztgcTrio_s25_2 : ((160133371217304849123/400000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ solY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((100106395142431538059/250000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq121, ztgcTrio_eq172, ztgcTrio_eq34]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((160133371217304849123/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((54777465021194071293/50000000000000000000 : ℝ)) + ((377619211298579237637/400000000000000000000 : ℝ)) + ((60093150118513033653/40000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((160133371217304849123/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t71.1, ztgcTrioT_t113.1, ztgcTrioT_t36.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((219116153473475067173/200000000000000000000 : ℝ)) + ((94408021705809893399/100000000000000000000 : ℝ)) + ((1502357249733945120841/1000000000000000000000 : ℝ)) ≤ ((100106395142431538059/250000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t71.2, ztgcTrioT_t113.2, ztgcTrioT_t36.2]) (le_trans hm2 (add_le_add_right hπlo ((100106395142431538059/250000000000000000000 : ℝ))))

theorem ztgcTrio_s25_3 : ((265864857108299881223/400000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) ∧ solY 2 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) ≤ ((166187234455943960549/250000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq278, ztgcTrio_eq195]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((265864857108299881223/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((135987801515136900611/100000000000000000000 : ℝ)) + ((377619211298579237637/400000000000000000000 : ℝ)) + ((60093150118513033653/40000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((265864857108299881223/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t131.1, ztgcTrioT_t113.1, ztgcTrioT_t36.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((54396164984857001033/40000000000000000000 : ℝ)) + ((94408021705809893399/100000000000000000000 : ℝ)) + ((1502357249733945120841/1000000000000000000000 : ℝ)) ≤ ((166187234455943960549/250000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t131.2, ztgcTrioT_t113.2, ztgcTrioT_t36.2]) (le_trans hm2 (add_le_add_right hπlo ((166187234455943960549/250000000000000000000 : ℝ))))

theorem ztgcTrio_s25_4 : ((265864857108299881223/400000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) ∧ solY 2 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) ≤ ((166187234455943960549/250000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq278, ztgcTrio_eq195]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((265864857108299881223/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((135987801515136900611/100000000000000000000 : ℝ)) + ((377619211298579237637/400000000000000000000 : ℝ)) + ((60093150118513033653/40000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((265864857108299881223/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t131.1, ztgcTrioT_t113.1, ztgcTrioT_t36.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((54396164984857001033/40000000000000000000 : ℝ)) + ((94408021705809893399/100000000000000000000 : ℝ)) + ((1502357249733945120841/1000000000000000000000 : ℝ)) ≤ ((166187234455943960549/250000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t131.2, ztgcTrioT_t113.2, ztgcTrioT_t36.2]) (le_trans hm2 (add_le_add_right hπlo ((166187234455943960549/250000000000000000000 : ℝ))))

theorem ztgcTrio_s26_1 : ((2519271377922934907/6250000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 ∧ solY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((3225307156078686653/8000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq120, ztgcTrio_eq171]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((2519271377922934907/6250000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((14342823058098574621/12500000000000000000 : ℝ)) + ((13488498474922468661/10000000000000000000 : ℝ)) + ((104840038191742998781/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((2519271377922934907/6250000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t68.1, ztgcTrioT_t112.1, ztgcTrioT_t18.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((229491286743461605409/200000000000000000000 : ℝ)) + ((269774012248337020139/200000000000000000000 : ℝ)) + ((209685910628107188469/200000000000000000000 : ℝ)) ≤ ((3225307156078686653/8000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t68.2, ztgcTrioT_t112.2, ztgcTrioT_t18.2]) (le_trans hm2 (add_le_add_right hπlo ((3225307156078686653/8000000000000000000 : ℝ))))

theorem ztgcTrio_s26_2 : ((2519271377922934907/6250000000000000000 : ℝ)) ≤ solY (2 * hplus) (2 * hminus) 2 2 2 (2 * hminus) ∧ solY (2 * hplus) (2 * hminus) 2 2 2 (2 * hminus) ≤ ((3225307156078686653/8000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq59, ztgcTrio_eq234]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((2519271377922934907/6250000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((14342823058098574621/12500000000000000000 : ℝ)) + ((104840038191742998781/100000000000000000000 : ℝ)) + ((13488498474922468661/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((2519271377922934907/6250000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t68.1, ztgcTrioT_t18.1, ztgcTrioT_t112.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((229491286743461605409/200000000000000000000 : ℝ)) + ((209685910628107188469/200000000000000000000 : ℝ)) + ((269774012248337020139/200000000000000000000 : ℝ)) ≤ ((3225307156078686653/8000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t68.2, ztgcTrioT_t18.2, ztgcTrioT_t112.2]) (le_trans hm2 (add_le_add_right hπlo ((3225307156078686653/8000000000000000000 : ℝ))))

theorem ztgcTrio_s26_3 : ((458618609325329248553/1000000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 2 ∧ solY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 2 ≤ ((458725748330188444927/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq156, ztgcTrio_eq16, ztgcTrio_eq51]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((458618609325329248553/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((1503410499080362511403/1000000000000000000000 : ℝ)) + ((104840038191742998781/100000000000000000000 : ℝ)) + ((104840038191742998781/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((458618609325329248553/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t94.1, ztgcTrioT_t18.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((1503459295638809798697/1000000000000000000000 : ℝ)) + ((209685910628107188469/200000000000000000000 : ℝ)) + ((209685910628107188469/200000000000000000000 : ℝ)) ≤ ((458725748330188444927/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t94.2, ztgcTrioT_t18.2]) (le_trans hm2 (add_le_add_right hπlo ((458725748330188444927/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s26_4 : ((1059517540474963005133/1000000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hplus) (2 * hminus) (2 * hminus) ∧ solY 2 2 2 (2 * hplus) (2 * hminus) (2 * hminus) ≤ ((1059606764532486761627/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq297]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1059517540474963005133/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((1503410499080362511403/1000000000000000000000 : ℝ)) + ((13488498474922468661/10000000000000000000 : ℝ)) + ((13488498474922468661/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1059517540474963005133/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t94.1, ztgcTrioT_t112.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((1503459295638809798697/1000000000000000000000 : ℝ)) + ((269774012248337020139/200000000000000000000 : ℝ)) + ((269774012248337020139/200000000000000000000 : ℝ)) ≤ ((1059606764532486761627/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t94.2, ztgcTrioT_t112.2]) (le_trans hm2 (add_le_add_right hπlo ((1059606764532486761627/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s27_1 : ((48602952940289367633/100000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ solY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((19445613931840377521/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq119, ztgcTrio_eq170]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((48602952940289367633/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((105990833056916243187/100000000000000000000 : ℝ)) + ((60176742544483799769/50000000000000000000 : ℝ)) + ((27283580030678969751/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((48602952940289367633/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t65.1, ztgcTrioT_t111.1, ztgcTrioT_t35.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((211989201596750168811/200000000000000000000 : ℝ)) + ((240715987044746791719/200000000000000000000 : ℝ)) + ((272841411735643574767/200000000000000000000 : ℝ)) ≤ ((19445613931840377521/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t65.2, ztgcTrioT_t111.2, ztgcTrioT_t35.2]) (le_trans hm2 (add_le_add_right hπlo ((19445613931840377521/40000000000000000000 : ℝ))))

theorem ztgcTrio_s27_2 : ((35932002033707351559/100000000000000000000 : ℝ)) ≤ solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((71891817689392044791/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq114, ztgcTrio_eq9]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((35932002033707351559/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((105990833056916243187/100000000000000000000 : ℝ)) + ((100416232887324064457/100000000000000000000 : ℝ)) + ((71842100724228183881/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((35932002033707351559/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t65.1, ztgcTrioT_t9.1, ztgcTrioT_t32.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((211989201596750168811/200000000000000000000 : ℝ)) + ((8033715456123934279/8000000000000000000 : ℝ)) + ((287378260407482166697/200000000000000000000 : ℝ)) ≤ ((71891817689392044791/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t65.2, ztgcTrioT_t9.2, ztgcTrioT_t32.2]) (le_trans hm2 (add_le_add_right hπlo ((71891817689392044791/200000000000000000000 : ℝ))))

theorem ztgcTrio_s27_3 : ((27881199723378842039/50000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 (2 * hminus) ∧ solY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 (2 * hminus) ≤ ((111546294145632149939/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq155, ztgcTrio_eq47]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((27881199723378842039/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((133087531765028094713/100000000000000000000 : ℝ)) + ((100416232887324064457/100000000000000000000 : ℝ)) + ((27283580030678969751/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((27881199723378842039/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t93.1, ztgcTrioT_t9.1, ztgcTrioT_t35.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((266180526724828865889/200000000000000000000 : ℝ)) + ((8033715456123934279/8000000000000000000 : ℝ)) + ((272841411735643574767/200000000000000000000 : ℝ)) ≤ ((111546294145632149939/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t93.2, ztgcTrioT_t9.2, ztgcTrioT_t35.2]) (le_trans hm2 (add_le_add_right hπlo ((111546294145632149939/200000000000000000000 : ℝ))))

theorem ztgcTrio_s27_4 : ((41482976471731369083/50000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) ∧ solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) ≤ ((165956243459119176613/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq182, ztgcTrio_eq65]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((41482976471731369083/50000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((133087531765028094713/100000000000000000000 : ℝ)) + ((60176742544483799769/50000000000000000000 : ℝ)) + ((71842100724228183881/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((41482976471731369083/50000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t93.1, ztgcTrioT_t111.1, ztgcTrioT_t32.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((266180526724828865889/200000000000000000000 : ℝ)) + ((240715987044746791719/200000000000000000000 : ℝ)) + ((287378260407482166697/200000000000000000000 : ℝ)) ≤ ((165956243459119176613/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t93.2, ztgcTrioT_t111.2, ztgcTrioT_t32.2]) (le_trans hm2 (add_le_add_right hπlo ((165956243459119176613/200000000000000000000 : ℝ))))

theorem ztgcTrio_s28_1 : ((33563273111124891427/100000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2.52 2 2 2 ∧ solY (2 * hplus) 2 2.52 2 2 2 ≤ ((67126547446294127119/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq126, ztgcTrio_eq223, ztgcTrio_eq93]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((33563273111124891427/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((125658578156268873167/100000000000000000000 : ℝ)) + ((2649701037173743693/2500000000000000000 : ℝ)) + ((116075918826895594387/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((33563273111124891427/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t75.1, ztgcTrioT_t148.1, ztgcTrioT_t60.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((251317156720538922071/200000000000000000000 : ℝ)) + ((211976083381901201571/200000000000000000000 : ℝ)) + ((232151838061792651169/200000000000000000000 : ℝ)) ≤ ((67126547446294127119/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t75.2, ztgcTrioT_t148.2, ztgcTrioT_t60.2]) (le_trans hm2 (add_le_add_right hπlo ((67126547446294127119/200000000000000000000 : ℝ))))

theorem ztgcTrio_s28_2 : ((9629494145139626887/20000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2 2 2 2.52 ∧ solY (2 * hplus) 2 2 2 2 2.52 ≤ ((19258988535087996563/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq132, ztgcTrio_eq289, ztgcTrio_eq240]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((9629494145139626887/20000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((125658578156268873167/100000000000000000000 : ℝ)) + ((48280921006685500473/50000000000000000000 : ℝ)) + ((140086315915047584169/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((9629494145139626887/20000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t75.1, ztgcTrioT_t157.1, ztgcTrioT_t162.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((251317156720538922071/200000000000000000000 : ℝ)) + ((1544989475477950987/1600000000000000000 : ℝ)) + ((280172632238095835061/200000000000000000000 : ℝ)) ≤ ((19258988535087996563/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t75.2, ztgcTrioT_t157.2, ztgcTrioT_t162.2]) (le_trans hm2 (add_le_add_right hπlo ((19258988535087996563/40000000000000000000 : ℝ))))

theorem ztgcTrio_s28_3 : ((266840328678624057881/500000000000000000000 : ℝ)) ≤ solY 2 2 2.52 (2 * hplus) 2 2 ∧ solY 2 2 2.52 (2 * hplus) 2 2 ≤ ((533680663477465223039/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq232]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((266840328678624057881/500000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((774447851272237700451/500000000000000000000 : ℝ)) + ((48280921006685500473/50000000000000000000 : ℝ)) + ((116075918826895594387/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((266840328678624057881/500000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t154.1, ztgcTrioT_t157.1, ztgcTrioT_t60.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((1548895704584475838779/1000000000000000000000 : ℝ)) + ((1544989475477950987/1600000000000000000 : ℝ)) + ((232151838061792651169/200000000000000000000 : ℝ)) ≤ ((533680663477465223039/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t154.2, ztgcTrioT_t157.2, ztgcTrioT_t60.2]) (le_trans hm2 (add_le_add_right hπlo ((533680663477465223039/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s28_4 : ((434023311487277740661/500000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hplus) 2 2.52 ∧ solY 2 2 2 (2 * hplus) 2 2.52 ≤ ((868046629094767783479/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq315, ztgcTrio_eq325]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((434023311487277740661/500000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((774447851272237700451/500000000000000000000 : ℝ)) + ((2649701037173743693/2500000000000000000 : ℝ)) + ((140086315915047584169/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((434023311487277740661/500000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t154.1, ztgcTrioT_t148.1, ztgcTrioT_t162.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((1548895704584475838779/1000000000000000000000 : ℝ)) + ((211976083381901201571/200000000000000000000 : ℝ)) + ((280172632238095835061/200000000000000000000 : ℝ)) ≤ ((868046629094767783479/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t154.2, ztgcTrioT_t148.2, ztgcTrioT_t162.2]) (le_trans hm2 (add_le_add_right hπlo ((868046629094767783479/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s29_1 : ((155893345766009165567/400000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2.52 2 2 (2 * hminus) ∧ solY (2 * hplus) 2 2.52 2 2 (2 * hminus) ≤ ((194899867868859597439/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq222, ztgcTrio_eq92]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((155893345766009165567/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((107087179522832868349/100000000000000000000 : ℝ)) + ((374238121290733610889/400000000000000000000 : ℝ)) + ((60994356781990137667/40000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((155893345766009165567/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t72.1, ztgcTrioT_t136.1, ztgcTrioT_t58.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((214179174308225756637/200000000000000000000 : ℝ)) + ((93561918002181167907/100000000000000000000 : ℝ)) + ((1524877337764471971083/1000000000000000000000 : ℝ)) ≤ ((194899867868859597439/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t72.2, ztgcTrioT_t136.2, ztgcTrioT_t58.2]) (le_trans hm2 (add_le_add_right hπlo ((194899867868859597439/500000000000000000000 : ℝ))))

theorem ztgcTrio_s29_2 : ((809883822558852086713/2000000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 2 2.52 ∧ solY (2 * hplus) 2 (2 * hminus) 2 2 2.52 ≤ ((80999228413942545993/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq122, ztgcTrio_eq173, ztgcTrio_eq35]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((809883822558852086713/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((107087179522832868349/100000000000000000000 : ℝ)) + ((370525111940529436857/400000000000000000000 : ℝ)) + ((774674994894833503097/500000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((809883822558852086713/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t72.1, ztgcTrioT_t114.1, ztgcTrioT_t37.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((214179174308225756637/200000000000000000000 : ℝ)) + ((92633343000525519627/100000000000000000000 : ℝ)) + ((154935949411302198897/100000000000000000000 : ℝ)) ≤ ((80999228413942545993/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t72.2, ztgcTrioT_t114.2, ztgcTrioT_t37.2]) (le_trans hm2 (add_le_add_right hπlo ((80999228413942545993/200000000000000000000 : ℝ))))

theorem ztgcTrio_s29_3 : ((256958993332277087771/400000000000000000000 : ℝ)) ≤ solY 2 2 2.52 (2 * hplus) 2 (2 * hminus) ∧ solY 2 2 2.52 (2 * hplus) 2 (2 * hminus) ≤ ((160613679762825081547/250000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq286, ztgcTrio_eq229]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((256958993332277087771/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((16660230468993861551/12500000000000000000 : ℝ)) + ((370525111940529436857/400000000000000000000 : ℝ)) + ((60994356781990137667/40000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((256958993332277087771/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t153.1, ztgcTrioT_t114.1, ztgcTrioT_t58.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((266567320974253279459/200000000000000000000 : ℝ)) + ((92633343000525519627/100000000000000000000 : ℝ)) + ((1524877337764471971083/1000000000000000000000 : ℝ)) ≤ ((160613679762825081547/250000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t153.2, ztgcTrioT_t114.2, ztgcTrioT_t58.2]) (le_trans hm2 (add_le_add_right hπlo ((160613679762825081547/250000000000000000000 : ℝ))))

theorem ztgcTrio_s29_4 : ((1352342153892233438053/2000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hplus) 2 2.52 ∧ solY 2 2 (2 * hminus) (2 * hplus) 2 2.52 ≤ ((1081956200666250923/1600000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq279, ztgcTrio_eq69]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1352342153892233438053/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((16660230468993861551/12500000000000000000 : ℝ)) + ((374238121290733610889/400000000000000000000 : ℝ)) + ((774674994894833503097/500000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1352342153892233438053/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t153.1, ztgcTrioT_t136.1, ztgcTrioT_t37.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((266567320974253279459/200000000000000000000 : ℝ)) + ((93561918002181167907/100000000000000000000 : ℝ)) + ((154935949411302198897/100000000000000000000 : ℝ)) ≤ ((1081956200666250923/1600000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t153.2, ztgcTrioT_t136.2, ztgcTrioT_t37.2]) (le_trans hm2 (add_le_add_right hπlo ((1081956200666250923/1600000000000000000 : ℝ))))

theorem ztgcTrio_s30_1 : ((4926357200592438133/12500000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2.52 2 (2 * hminus) 2 ∧ solY (2 * hplus) 2 2.52 2 (2 * hminus) 2 ≤ ((15766350249672567651/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq125, ztgcTrio_eq221]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((4926357200592438133/12500000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((112997018594525988647/100000000000000000000 : ℝ)) + ((67309769632004205367/50000000000000000000 : ℝ)) + ((10595356510519442953/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((4926357200592438133/12500000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t69.1, ztgcTrioT_t147.1, ztgcTrioT_t59.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((225997286080729585539/200000000000000000000 : ℝ)) + ((269242585909022444251/200000000000000000000 : ℝ)) + ((211910409976549456157/200000000000000000000 : ℝ)) ≤ ((15766350249672567651/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t69.2, ztgcTrioT_t147.2, ztgcTrioT_t59.2]) (le_trans hm2 (add_le_add_right hπlo ((15766350249672567651/40000000000000000000 : ℝ))))

theorem ztgcTrio_s30_2 : ((40917223356222779697/100000000000000000000 : ℝ)) ≤ solY (2 * hplus) (2 * hminus) 2 2 2 2.52 ∧ solY (2 * hplus) (2 * hminus) 2 2 2 2.52 ≤ ((81844277195960218299/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq117, ztgcTrio_eq235]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((40917223356222779697/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((112997018594525988647/100000000000000000000 : ℝ)) + ((5173169507298224253/5000000000000000000 : ℝ)) + ((138616079974721629837/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((40917223356222779697/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t69.1, ztgcTrioT_t29.1, ztgcTrioT_t159.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((225997286080729585539/200000000000000000000 : ℝ)) + ((206932195976520994851/200000000000000000000 : ℝ)) + ((277233325856648285601/200000000000000000000 : ℝ)) ≤ ((81844277195960218299/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t69.2, ztgcTrioT_t29.2, ztgcTrioT_t159.2]) (le_trans hm2 (add_le_add_right hπlo ((81844277195960218299/200000000000000000000 : ℝ))))

theorem ztgcTrio_s30_3 : ((447598379354638004521/1000000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) 2.52 (2 * hplus) 2 2 ∧ solY 2 (2 * hminus) 2.52 (2 * hplus) 2 2 ≤ ((447646323531743095427/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq167, ztgcTrio_eq26, ztgcTrio_eq99]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((447598379354638004521/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((1495021480432942097091/1000000000000000000000 : ℝ)) + ((5173169507298224253/5000000000000000000 : ℝ)) + ((10595356510519442953/10000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((447598379354638004521/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t106.1, ztgcTrioT_t29.1, ztgcTrioT_t59.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((1495025947356084078847/1000000000000000000000 : ℝ)) + ((206932195976520994851/200000000000000000000 : ℝ)) + ((211910409976549456157/200000000000000000000 : ℝ)) ≤ ((447646323531743095427/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t106.2, ztgcTrioT_t29.2, ztgcTrioT_t59.2]) (le_trans hm2 (add_le_add_right hπlo ((447646323531743095427/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s30_4 : ((1085785019230349264331/1000000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hplus) (2 * hminus) 2.52 ∧ solY 2 2 2 (2 * hplus) (2 * hminus) 2.52 ≤ ((1085812852594744489647/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq300, ztgcTrio_eq310]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1085785019230349264331/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((1495021480432942097091/1000000000000000000000 : ℝ)) + ((67309769632004205367/50000000000000000000 : ℝ)) + ((138616079974721629837/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1085785019230349264331/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t106.1, ztgcTrioT_t147.1, ztgcTrioT_t159.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((1495025947356084078847/1000000000000000000000 : ℝ)) + ((269242585909022444251/200000000000000000000 : ℝ)) + ((277233325856648285601/200000000000000000000 : ℝ)) ≤ ((1085812852594744489647/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t106.2, ztgcTrioT_t147.2, ztgcTrioT_t159.2]) (le_trans hm2 (add_le_add_right hπlo ((1085812852594744489647/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s31_1 : ((236838468773921273/500000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) ∧ solY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) ≤ ((94747723279762473373/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq124, ztgcTrio_eq220, ztgcTrio_eq91]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((236838468773921273/500000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((104055314058689365787/100000000000000000000 : ℝ)) + ((59710304215362806997/50000000000000000000 : ℝ)) + ((69025518312179299333/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((236838468773921273/500000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t66.1, ztgcTrioT_t125.1, ztgcTrioT_t57.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((208118633664223531101/200000000000000000000 : ℝ)) + ((238843258283455740543/200000000000000000000 : ℝ)) + ((276104362050021849421/200000000000000000000 : ℝ)) ≤ ((94747723279762473373/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t66.2, ztgcTrioT_t125.2, ztgcTrioT_t57.2]) (le_trans hm2 (add_le_add_right hπlo ((94747723279762473373/200000000000000000000 : ℝ))))

theorem ztgcTrio_s31_2 : ((363634997082195298231/1000000000000000000000 : ℝ)) ≤ solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 2.52 ∧ solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 2.52 ≤ ((363700591442766168163/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq115, ztgcTrio_eq10, ztgcTrio_eq29]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((363634997082195298231/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((104055314058689365787/100000000000000000000 : ℝ)) + ((49353111673448186127/50000000000000000000 : ℝ)) + ((1477612276616231156291/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((363634997082195298231/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t66.1, ztgcTrioT_t10.1, ztgcTrioT_t33.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((208118633664223531101/200000000000000000000 : ℝ)) + ((197416804971844286413/200000000000000000000 : ℝ)) + ((1477616051852120319053/1000000000000000000000 : ℝ)) ≤ ((363700591442766168163/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t66.2, ztgcTrioT_t10.2, ztgcTrioT_t33.2]) (le_trans hm2 (add_le_add_right hπlo ((363700591442766168163/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s31_3 : ((5424106012875551817/10000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) 2.52 (2 * hplus) 2 (2 * hminus) ∧ solY 2 (2 * hminus) 2.52 (2 * hplus) 2 (2 * hminus) ≤ ((108492092266682714993/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq96]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((5424106012875551817/10000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((131643065516489871097/100000000000000000000 : ℝ)) + ((49353111673448186127/50000000000000000000 : ℝ)) + ((69025518312179299333/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((5424106012875551817/10000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t105.1, ztgcTrioT_t10.1, ztgcTrioT_t57.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((263289455962755226851/200000000000000000000 : ℝ)) + ((197416804971844286413/200000000000000000000 : ℝ)) + ((276104362050021849421/200000000000000000000 : ℝ)) ≤ ((108492092266682714993/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t105.2, ztgcTrioT_t10.2, ztgcTrioT_t57.2]) (le_trans hm2 (add_le_add_right hπlo ((108492092266682714993/200000000000000000000 : ℝ))))

theorem ztgcTrio_s31_4 : ((846656362498492768731/1000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) 2.52 ∧ solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) 2.52 ≤ ((846686969493481917563/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq277, ztgcTrio_eq185, ztgcTrio_eq68]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((846656362498492768731/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((131643065516489871097/100000000000000000000 : ℝ)) + ((59710304215362806997/50000000000000000000 : ℝ)) + ((1477612276616231156291/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((846656362498492768731/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t105.1, ztgcTrioT_t125.1, ztgcTrioT_t33.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((263289455962755226851/200000000000000000000 : ℝ)) + ((238843258283455740543/200000000000000000000 : ℝ)) + ((1477616051852120319053/1000000000000000000000 : ℝ)) ≤ ((846686969493481917563/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t105.2, ztgcTrioT_t125.2, ztgcTrioT_t33.2]) (le_trans hm2 (add_le_add_right hπlo ((846686969493481917563/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s32_1 : ((29253255013751804841/100000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 ∧ solY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 ≤ ((58506511251548049067/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq130, ztgcTrio_eq259, ztgcTrio_eq143]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((29253255013751804841/100000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((56144756473211449677/50000000000000000000 : ℝ)) + ((20857431409310507411/20000000000000000000 : ℝ)) + ((126835850379765692279/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((29253255013751804841/100000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t76.1, ztgcTrioT_t169.1, ztgcTrioT_t88.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((224579026300847360131/200000000000000000000 : ℝ)) + ((208574314501106814749/200000000000000000000 : ℝ)) + ((253671701167532521879/200000000000000000000 : ℝ)) ≤ ((58506511251548049067/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t76.2, ztgcTrioT_t169.2, ztgcTrioT_t88.2]) (le_trans hm2 (add_le_add_right hπlo ((58506511251548049067/200000000000000000000 : ℝ))))

theorem ztgcTrio_s32_2 : ((1033383000993764373367/2000000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2 2 2 (Real.sqrt 8) ∧ solY (2 * hplus) 2 2 2 2 (Real.sqrt 8) ≤ ((258345753308550585797/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq133, ztgcTrio_eq290, ztgcTrio_eq241]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1033383000993764373367/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((56144756473211449677/50000000000000000000 : ℝ)) + ((71501514568773064057/80000000000000000000 : ℝ)) + ((1641620092512883130901/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1033383000993764373367/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t76.1, ztgcTrioT_t164.1, ztgcTrioT_t163.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((224579026300847360131/200000000000000000000 : ℝ)) + ((3575075736598692267/4000000000000000000 : ℝ)) + ((1641620094552884542649/1000000000000000000000 : ℝ)) ≤ ((258345753308550585797/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t76.2, ztgcTrioT_t164.2, ztgcTrioT_t163.2]) (le_trans hm2 (add_le_add_right hπlo ((258345753308550585797/500000000000000000000 : ℝ))))

theorem ztgcTrio_s32_3 : ((180154814091135983489/400000000000000000000 : ℝ)) ≤ solY 2 2 (Real.sqrt 8) (2 * hplus) 2 2 ∧ solY 2 2 (Real.sqrt 8) (2 * hplus) 2 2 ≤ ((11259676033701454827/25000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq295]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((180154814091135983489/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((142985225291041297369/100000000000000000000 : ℝ)) + ((71501514568773064057/80000000000000000000 : ℝ)) + ((126835850379765692279/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((180154814091135983489/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t175.1, ztgcTrioT_t164.1, ztgcTrioT_t88.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((285970450990083151079/200000000000000000000 : ℝ)) + ((3575075736598692267/4000000000000000000 : ℝ)) + ((253671701167532521879/200000000000000000000 : ℝ)) ≤ ((11259676033701454827/25000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t175.2, ztgcTrioT_t164.2, ztgcTrioT_t88.2]) (le_trans hm2 (add_le_add_right hπlo ((11259676033701454827/25000000000000000000 : ℝ))))

theorem ztgcTrio_s32_4 : ((972751262298928236671/1000000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hplus) 2 (Real.sqrt 8) ∧ solY 2 2 2 (2 * hplus) 2 (Real.sqrt 8) ≤ ((972751268419141133329/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq316, ztgcTrio_eq328]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((972751262298928236671/1000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((142985225291041297369/100000000000000000000 : ℝ)) + ((20857431409310507411/20000000000000000000 : ℝ)) + ((1641620092512883130901/1000000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((972751262298928236671/1000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t175.1, ztgcTrioT_t169.1, ztgcTrioT_t163.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((285970450990083151079/200000000000000000000 : ℝ)) + ((208574314501106814749/200000000000000000000 : ℝ)) + ((1641620094552884542649/1000000000000000000000 : ℝ)) ≤ ((972751268419141133329/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t175.2, ztgcTrioT_t169.2, ztgcTrioT_t163.2]) (le_trans hm2 (add_le_add_right hπlo ((972751268419141133329/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s33_1 : ((20277851007300440717/62500000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) ∧ solY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) ≤ ((162265249271659430641/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq129, ztgcTrio_eq258, ztgcTrio_eq141]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((20277851007300440717/62500000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((367692182738793902369/400000000000000000000 : ℝ)) + ((1732947455154749257679/2000000000000000000000 : ℝ)) + ((84016704264117045259/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((20277851007300440717/62500000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t73.1, ztgcTrioT_t139.1, ztgcTrioT_t86.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((91926110496246127853/100000000000000000000 : ℝ)) + ((866503819734088938927/1000000000000000000000 : ℝ)) + ((336071645487292376457/200000000000000000000 : ℝ)) ≤ ((162265249271659430641/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t73.2, ztgcTrioT_t139.2, ztgcTrioT_t86.2]) (le_trans hm2 (add_le_add_right hπlo ((162265249271659430641/500000000000000000000 : ℝ))))

theorem ztgcTrio_s33_2 : ((82988096130288109101/200000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 2 (Real.sqrt 8) ∧ solY (2 * hplus) 2 (2 * hminus) 2 2 (Real.sqrt 8) ≤ ((207511442554409444299/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq174, ztgcTrio_eq36]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((82988096130288109101/200000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((367692182738793902369/400000000000000000000 : ℝ)) + ((323994179939998345241/400000000000000000000 : ℝ)) + ((36546344550887063299/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((82988096130288109101/200000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t73.1, ztgcTrioT_t115.1, ztgcTrioT_t38.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((91926110496246127853/100000000000000000000 : ℝ)) + ((810012295714359766753/1000000000000000000000 : ℝ)) + ((73093685520867643271/40000000000000000000 : ℝ)) ≤ ((207511442554409444299/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t73.2, ztgcTrioT_t115.2, ztgcTrioT_t38.2]) (le_trans hm2 (add_le_add_right hπlo ((207511442554409444299/500000000000000000000 : ℝ))))

theorem ztgcTrio_s33_3 : ((206744727990200877069/400000000000000000000 : ℝ)) ≤ solY 2 2 (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) ∧ solY 2 2 (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) ≤ ((516940618644720722293/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq294, ztgcTrio_eq148]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((206744727990200877069/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((58406746921652933143/50000000000000000000 : ℝ)) + ((323994179939998345241/400000000000000000000 : ℝ)) + ((84016704264117045259/50000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((206744727990200877069/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t174.1, ztgcTrioT_t115.1, ztgcTrioT_t86.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((233632549816718462343/200000000000000000000 : ℝ)) + ((810012295714359766753/1000000000000000000000 : ℝ)) + ((336071645487292376457/200000000000000000000 : ℝ)) ≤ ((516940618644720722293/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t174.2, ztgcTrioT_t115.2, ztgcTrioT_t86.2]) (le_trans hm2 (add_le_add_right hπlo ((516940618644720722293/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s33_4 : ((1440666479929786436359/2000000000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) ∧ solY 2 2 (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) ≤ ((720416053249679093957/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq280, ztgcTrio_eq200, ztgcTrio_eq74]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((1440666479929786436359/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((58406746921652933143/50000000000000000000 : ℝ)) + ((1732947455154749257679/2000000000000000000000 : ℝ)) + ((36546344550887063299/20000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((1440666479929786436359/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t174.1, ztgcTrioT_t139.1, ztgcTrioT_t38.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((233632549816718462343/200000000000000000000 : ℝ)) + ((866503819734088938927/1000000000000000000000 : ℝ)) + ((73093685520867643271/40000000000000000000 : ℝ)) ≤ ((720416053249679093957/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t174.2, ztgcTrioT_t139.2, ztgcTrioT_t38.2]) (le_trans hm2 (add_le_add_right hπlo ((720416053249679093957/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s34_1 : ((3427927722587692231/10000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 ∧ solY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 ≤ ((68568655790018856647/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq128, ztgcTrio_eq257, ztgcTrio_eq142]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((3427927722587692231/10000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((12825428546077987861/12500000000000000000 : ℝ)) + ((1060102310552585929/800000000000000000 : ℝ)) + ((1770661334330767221/1562500000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((3427927722587692231/10000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t70.1, ztgcTrioT_t168.1, ztgcTrioT_t87.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((205210168937587456251/200000000000000000000 : ℝ)) + ((265029088018397175459/200000000000000000000 : ℝ)) + ((226647929551972872629/200000000000000000000 : ℝ)) ≤ ((68568655790018856647/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t70.2, ztgcTrioT_t168.2, ztgcTrioT_t87.2]) (le_trans hm2 (add_le_add_right hπlo ((68568655790018856647/200000000000000000000 : ℝ))))

theorem ztgcTrio_s34_2 : ((869882055749902918249/2000000000000000000000 : ℝ)) ≤ solY (2 * hplus) (2 * hminus) 2 2 2 (Real.sqrt 8) ∧ solY (2 * hplus) (2 * hminus) 2 2 2 (Real.sqrt 8) ≤ ((434987660685281310639/1000000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq118]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((869882055749902918249/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((12825428546077987861/12500000000000000000 : ℝ)) + ((379684505358154045261/400000000000000000000 : ℝ)) + ((800644067191610277781/500000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((869882055749902918249/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t70.1, ztgcTrioT_t39.1, ztgcTrioT_t160.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((205210168937587456251/200000000000000000000 : ℝ)) + ((94923906598674265287/100000000000000000000 : ℝ)) + ((800645201800147307487/500000000000000000000 : ℝ)) ≤ ((434987660685281310639/1000000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t70.2, ztgcTrioT_t39.2, ztgcTrioT_t160.2]) (le_trans hm2 (add_le_add_right hπlo ((434987660685281310639/1000000000000000000000 : ℝ))))

theorem ztgcTrio_s34_3 : ((154376535609308452589/400000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) 2 2 ∧ solY 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) 2 2 ≤ ((2412427775136334987/6250000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq179, ztgcTrio_eq44]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((154376535609308452589/400000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((28901989504921764707/20000000000000000000 : ℝ)) + ((379684505358154045261/400000000000000000000 : ℝ)) + ((1770661334330767221/1562500000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((154376535609308452589/400000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t122.1, ztgcTrioT_t39.1, ztgcTrioT_t87.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((289020476772979964073/200000000000000000000 : ℝ)) + ((94923906598674265287/100000000000000000000 : ℝ)) + ((226647929551972872629/200000000000000000000 : ℝ)) ≤ ((2412427775136334987/6250000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t122.2, ztgcTrioT_t39.2, ztgcTrioT_t87.2]) (le_trans hm2 (add_le_add_right hπlo ((2412427775136334987/6250000000000000000 : ℝ))))

theorem ztgcTrio_s34_4 : ((307480711057536990923/250000000000000000000 : ℝ)) ≤ solY 2 2 2 (2 * hplus) (2 * hminus) (Real.sqrt 8) ∧ solY 2 2 2 (2 * hplus) (2 * hminus) (Real.sqrt 8) ≤ ((614972786983743537087/500000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq313, ztgcTrio_eq304, ztgcTrio_eq321]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((307480711057536990923/250000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((28901989504921764707/20000000000000000000 : ℝ)) + ((1060102310552585929/800000000000000000 : ℝ)) + ((800644067191610277781/500000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((307480711057536990923/250000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t122.1, ztgcTrioT_t168.1, ztgcTrioT_t160.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((289020476772979964073/200000000000000000000 : ℝ)) + ((265029088018397175459/200000000000000000000 : ℝ)) + ((800645201800147307487/500000000000000000000 : ℝ)) ≤ ((614972786983743537087/500000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t122.2, ztgcTrioT_t168.2, ztgcTrioT_t160.2]) (le_trans hm2 (add_le_add_right hπlo ((614972786983743537087/500000000000000000000 : ℝ))))

theorem ztgcTrio_s35_1 : ((804571643915319262181/2000000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ∧ solY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ≤ ((80468687160691372247/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq127, ztgcTrio_eq256, ztgcTrio_eq140]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((804571643915319262181/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((369180906589825648841/400000000000000000000 : ℝ)) + ((56493603019607341269/50000000000000000000 : ℝ)) + ((745527074340420961039/500000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((804571643915319262181/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t67.1, ztgcTrioT_t127.1, ztgcTrioT_t85.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((46149508790932973223/50000000000000000000 : ℝ)) + ((225976222384494464431/200000000000000000000 : ℝ)) + ((37276620041300457827/25000000000000000000 : ℝ)) ≤ ((80468687160691372247/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t67.2, ztgcTrioT_t127.2, ztgcTrioT_t85.2]) (le_trans hm2 (add_le_add_right hπlo ((80468687160691372247/200000000000000000000 : ℝ))))

theorem ztgcTrio_s35_2 : ((3776274440192335267/10000000000000000000 : ℝ)) ≤ solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) ∧ solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) ≤ ((75539679799830317283/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq116, ztgcTrio_eq30]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((3776274440192335267/10000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((369180906589825648841/400000000000000000000 : ℝ)) + ((70464590362796612027/80000000000000000000 : ℝ)) + ((171546045159960499273/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((3776274440192335267/10000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t67.1, ztgcTrioT_t11.1, ztgcTrioT_t34.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((46149508790932973223/50000000000000000000 : ℝ)) + ((88083129906972659169/100000000000000000000 : ℝ)) + ((68618783108018350749/40000000000000000000 : ℝ)) ≤ ((75539679799830317283/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t67.2, ztgcTrioT_t11.2, ztgcTrioT_t34.2]) (le_trans hm2 (add_le_add_right hπlo ((75539679799830317283/200000000000000000000 : ℝ))))

theorem ztgcTrio_s35_3 : ((912949637007320786111/2000000000000000000000 : ℝ)) ≤ solY 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) ∧ solY 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) ≤ ((91305429352361685883/200000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq178, ztgcTrio_eq41, ztgcTrio_eq146]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((912949637007320786111/2000000000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((122620594387775405911/100000000000000000000 : ℝ)) + ((70464590362796612027/80000000000000000000 : ℝ)) + ((745527074340420961039/500000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((912949637007320786111/2000000000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t121.1, ztgcTrioT_t11.1, ztgcTrioT_t85.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((245244739925951352621/200000000000000000000 : ℝ)) + ((88083129906972659169/100000000000000000000 : ℝ)) + ((37276620041300457827/25000000000000000000 : ℝ)) ≤ ((91305429352361685883/200000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t121.2, ztgcTrioT_t11.2, ztgcTrioT_t85.2]) (le_trans hm2 (add_le_add_right hπlo ((91305429352361685883/200000000000000000000 : ℝ))))

theorem ztgcTrio_s35_4 : ((743956641823690111/800000000000000000 : ℝ)) ≤ solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (Real.sqrt 8) ∧ solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (Real.sqrt 8) ≤ ((37199269426519784621/40000000000000000000 : ℝ)) := by
    unfold solY
    simp only [ztgcTrio_eq188, ztgcTrio_eq73]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor
    · rw [le_sub_iff_add_le]
      have hπhi : Real.pi ≤ (3.14159265358979323847 : ℝ) := le_of_lt hp2
      have hm1 : ((743956641823690111/800000000000000000 : ℝ)) + (3.14159265358979323847 : ℝ) ≤ ((122620594387775405911/100000000000000000000 : ℝ)) + ((56493603019607341269/50000000000000000000 : ℝ)) + ((171546045159960499273/100000000000000000000 : ℝ)) := by norm_num
      exact le_trans (add_le_add_right hπhi ((743956641823690111/800000000000000000 : ℝ))) (le_trans hm1 (by linarith [ztgcTrioT_t121.1, ztgcTrioT_t127.1, ztgcTrioT_t34.1]))
    · rw [sub_le_iff_le_add]
      have hπlo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt hp1
      have hm2 : ((245244739925951352621/200000000000000000000 : ℝ)) + ((225976222384494464431/200000000000000000000 : ℝ)) + ((68618783108018350749/40000000000000000000 : ℝ)) ≤ ((37199269426519784621/40000000000000000000 : ℝ)) + (3.14159265358979323846 : ℝ) := by norm_num
      exact le_trans (by linarith [ztgcTrioT_t121.2, ztgcTrioT_t127.2, ztgcTrioT_t34.2]) (le_trans hm2 (add_le_add_right hπlo ((37199269426519784621/40000000000000000000 : ℝ))))

/-! ## The 36 corner certificates -/

theorem ztgcTrio_c0 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 (2 * hminus) 2 2 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1330705002039654856249979603318367/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)) ≤ ((1330746674130892922166741308796147/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1330705002039654856249979603318367/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((16887434029134686/95367431640625 : ℝ)) := by norm_num
    have hs2 : ((708354684284159/4000000000000 : ℝ)) ≤ ((1330746674130892922166741308796147/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((443568334012818285416659867772789/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) 2 2 2 ∧ volY (2 * hminus) 2 (2 * hminus) 2 2 2 ≤ ((443582224710697640722247102932049/400000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hminus) 2 (2 * hminus) 2 2 2 = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((11070174261771519993/5000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 2 2 + solY (2 * hminus) 2 2 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) 2 (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 2 2 + solY (2 * hminus) 2 2 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) 2 (2 * hminus) ≤ ((110715541752862294207/50000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s0_1.1, ztgcTrio_s0_1.2, ztgcTrio_s0_2.1, ztgcTrio_s0_2.2, ztgcTrio_s0_3.1, ztgcTrio_s0_3.2, ztgcTrio_s0_4.1, ztgcTrio_s0_4.2]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((52220211006568924260582257/10000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((52222216357876941509362611/10000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq54, ztgcTrio_eq162, ztgcTrio_eq18, ztgcTrio_eq189, ztgcTrio_eq201, ztgcTrio_eq189]
    rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t20.1, ztgcTrioT_t20.2, hlm.1, hlm.2, ztgcTrioT_t20.1, ztgcTrioT_t20.2, ztgcTrioT_t99.1, ztgcTrioT_t99.2, ztgcTrioT_t128.1, ztgcTrioT_t128.2, ztgcTrioT_t140.1, ztgcTrioT_t140.2, ztgcTrioT_t128.1, ztgcTrioT_t128.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((121618696337696172259/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2 2 2 := by
    rw [ztgcTrio_eq54]
    exact ztgcTrioT_t20.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c1 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
      have hf := ztgcTrioF_f18
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
      have hf := ztgcTrioF_f19
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f20
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hsqc : ((177359979509643989500204903542369/12500000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ≤ ((1418935217426743341052174267291517/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((177359979509643989500204903542369/12500000000000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/1250000000000000000000 : ℝ)) := by norm_num
    have hs2 : ((1228867890169579548417611/6103515625000000000000 : ℝ)) ≤ ((1418935217426743341052174267291517/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((59119993169831329833401634514123/50000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ volY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((1418935217427943341052174267291517/1200000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1043465216707629771429/500000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((521831599926631417377/250000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s1_1.1, ztgcTrio_s1_1.2, ztgcTrio_s1_2.1, ztgcTrio_s1_2.2, ztgcTrio_s1_3.1, ztgcTrio_s1_3.2, ztgcTrio_s1_4.1, ztgcTrio_s1_4.2]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((357867689811729583295586841/100000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((1789479258545559017487122563/500000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq157, ztgcTrio_eq11, ztgcTrio_eq160, ztgcTrio_eq11]
    rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t41.1, ztgcTrioT_t41.2, hlm.1, hlm.2, ztgcTrioT_t13.1, ztgcTrioT_t13.2, hlm.1, hlm.2, ztgcTrioT_t13.1, ztgcTrioT_t13.2, ztgcTrioT_t96.1, ztgcTrioT_t96.2, ztgcTrioT_t123.1, ztgcTrioT_t123.2, ztgcTrioT_t96.1, ztgcTrioT_t96.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((51958550789785395683/50000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) :=
    ztgcTrioT_t41.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c2 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-3650129975773/30517578125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/1000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-56201051236976881/381469726562500 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/4000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f23
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp5.1, le_trans hp5.2 (by norm_num)⟩
  have hsqc : ((738995227141127080147728588655299/50000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ≤ ((23094167665897346241676658971153/1562500000000000000000000000000 : ℝ)) := by
    have hs1 : ((738995227141127080147728588655299/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((136528486434344232134231/625000000000000000000 : ℝ)) := by norm_num
    have hs2 : ((1333351450451419536331151/6103515625000000000000 : ℝ)) ≤ ((23094167665897346241676658971153/1562500000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((246331742380175693382576196218433/200000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ∧ volY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((23094167665916096241676658971153/18750000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((57483296583449625659/25000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((114979717938235718933/50000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s2_1.1, ztgcTrio_s2_1.2, ztgcTrio_s2_2.1, ztgcTrio_s2_2.2, ztgcTrio_s2_3.1, ztgcTrio_s2_3.2, ztgcTrio_s2_4.1, ztgcTrio_s2_4.2]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((44845217892265534596833123/10000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((448471187754946539629180671/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq49]
    rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t16.1, ztgcTrioT_t16.2, hlm.1, hlm.2, ztgcTrioT_t16.1, ztgcTrioT_t16.2, hlm.1, hlm.2, ztgcTrioT_t16.1, ztgcTrioT_t16.2, ztgcTrioT_t90.1, ztgcTrioT_t90.2, ztgcTrioT_t90.1, ztgcTrioT_t90.2, ztgcTrioT_t90.1, ztgcTrioT_t90.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((55126375427410257267/50000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 := by
    rw [ztgcTrio_eq49]
    exact ztgcTrioT_t16.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c3 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hsqc : ((819547943131172434620568688193699/50000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((819580261663734332902616637261371/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((819547943131172434620568688193699/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/762939453125000000000 : ℝ)) := by norm_num
    have hs2 : ((167927951327195450705831/625000000000000000000 : ℝ)) ≤ ((819580261663734332902616637261371/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((273182647710190811540189562731233/200000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((819580261664334332902616637261371/600000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1098623741403009513021/500000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((1098807740006580685881/500000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s3_1.1, ztgcTrio_s3_1.2, ztgcTrio_s3_2.1, ztgcTrio_s3_2.2, ztgcTrio_s3_3.1, ztgcTrio_s3_3.2, ztgcTrio_s3_4.1, ztgcTrio_s3_4.2]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((593991364502084148826277663/200000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((1485101080735352508580359377/500000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq48, ztgcTrio_eq149, ztgcTrio_eq149, ztgcTrio_eq0]
    rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t3.1, ztgcTrioT_t3.2, hlm.1, hlm.2, ztgcTrioT_t12.1, ztgcTrioT_t12.2, hlm.1, hlm.2, ztgcTrioT_t3.1, ztgcTrioT_t3.2, hlm.1, hlm.2, ztgcTrioT_t0.1, ztgcTrioT_t0.2, ztgcTrioT_t89.1, ztgcTrioT_t89.2, ztgcTrioT_t89.1, ztgcTrioT_t89.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((102192375561257185251/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) := by
    rw [ztgcTrio_eq48]
    exact ztgcTrioT_t3.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c4 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 2.52 2 2 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((1092135479046260529/6103515625000000 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) ≤ ((17894591750366439/100000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((1092135479046260529/6103515625000000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ≤ ((17894591750366439/100000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f44
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((334416915024247601930849757490539/25000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2)) ≤ ((668853342489345658433424893389699/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((334416915024247601930849757490539/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((1092135479046260529/6103515625000000 : ℝ)) := by norm_num
    have hs2 : ((17894591750366439/100000000000000 : ℝ)) ≤ ((668853342489345658433424893389699/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((111472305007982533976949919163513/100000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 2.52 2 2 2 ∧ volY (2 * hminus) 2 2.52 2 2 2 ≤ ((668853342489945658433424893389699/600000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hminus) 2 2.52 2 2 2 = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((692206845085922987/312500000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2.52 2 2 2 + solY (2 * hminus) 2 2 2 2 2.52 + solY 2 2 2.52 (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) 2 2.52 ∧ solY (2 * hminus) 2 2.52 2 2 2 + solY (2 * hminus) 2 2 2 2 2.52 + solY 2 2 2.52 (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) 2 2.52 ≤ ((2215273386536570543/1000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s4_1.1, ztgcTrio_s4_1.2, ztgcTrio_s4_2.1, ztgcTrio_s4_2.2, ztgcTrio_s4_3.1, ztgcTrio_s4_3.2, ztgcTrio_s4_4.1, ztgcTrio_s4_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((101828070803046802985450803/20000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2.52 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2 2 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hminus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2.52 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2.52 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2 2 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hminus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2.52 2 2 ≤ ((509151524303915114240132807/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq58, ztgcTrio_eq216, ztgcTrio_eq224, ztgcTrio_eq202, ztgcTrio_eq191, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t31.1, ztgcTrioT_t31.2, ztgcTrioT_t110.1, ztgcTrioT_t110.2, ztgcTrioT_t150.1, ztgcTrioT_t150.2, ztgcTrioT_t141.1, ztgcTrioT_t141.2, ztgcTrioT_t130.1, ztgcTrioT_t130.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((119524682053453925961/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2.52 2 2 2 := by
    rw [ztgcTrio_eq58]
    exact ztgcTrioT_t31.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c5 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 2.52 2 2 (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((4897650806901151491/24414062500000000 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((12538703121197844471/62500000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((4897650806901151491/24414062500000000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ≤ ((12538703121197844471/62500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f22
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((283272149743434645978502565625213/20000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ≤ ((177050156178963135401561789613649/12500000000000000000000000000000 : ℝ)) := by
    have hs1 : ((283272149743434645978502565625213/20000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((4897650806901151491/24414062500000000 : ℝ)) := by norm_num
    have hs2 : ((12538703121197844471/62500000000000000 : ℝ)) ≤ ((177050156178963135401561789613649/12500000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((94424049914398215326167521875071/80000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 2.52 2 2 (2 * hminus) ∧ volY (2 * hminus) 2 2.52 2 2 (2 * hminus) ≤ ((177050156179113135401561789613649/150000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hminus) 2 2.52 2 2 (2 * hminus) = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1031685320945613036219/500000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2.52 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 2 2.52 + solY 2 2 2.52 (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 2.52 ∧ solY (2 * hminus) 2 2.52 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 2 2.52 + solY 2 2 2.52 (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 2.52 ≤ ((515903066957617054277/250000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s5_1.1, ztgcTrio_s5_1.2, ztgcTrio_s5_2.1, ztgcTrio_s5_2.2, ztgcTrio_s5_3.1, ztgcTrio_s5_3.2, ztgcTrio_s5_4.1, ztgcTrio_s5_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((334814817759111968532674389/100000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2.52 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2.52 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2.52 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2.52 2 2 ≤ ((13393347695486469385670201/4000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq57, ztgcTrio_eq212, ztgcTrio_eq161, ztgcTrio_eq12, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t42.1, ztgcTrioT_t42.2, hlm.1, hlm.2, ztgcTrioT_t14.1, ztgcTrioT_t14.2, ztgcTrioT_t134.1, ztgcTrioT_t134.2, ztgcTrioT_t149.1, ztgcTrioT_t149.2, ztgcTrioT_t97.1, ztgcTrioT_t97.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((101438567402920726463/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2.52 2 2 (2 * hminus) := by
    rw [ztgcTrio_eq57]
    exact ztgcTrioT_t42.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c6 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 2.52 2 (2 * hminus) 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-15876/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((26395850867927159367/119209289550781250 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((2214420535523827071/10000000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-15876/390625 : ℝ)) ≤ ((-15876/390625 : ℝ)) ∧ ((-15876/390625 : ℝ)) ≤ ((-15876/390625 : ℝ)) := by norm_num
    have hp1 : ((26395850867927159367/119209289550781250 : ℝ)) ≤ ((-15876/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ∧ ((-15876/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ≤ ((2214420535523827071/10000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f24
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1488033755522690701562444772944181/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ≤ ((148809291898183271992918981817839/10000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1488033755522690701562444772944181/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((26395850867927159367/119209289550781250 : ℝ)) := by norm_num
    have hs2 : ((2214420535523827071/10000000000000000 : ℝ)) ≤ ((148809291898183271992918981817839/10000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((496011251840496900520814924314727/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 2.52 2 (2 * hminus) 2 ∧ volY (2 * hminus) 2 2.52 2 (2 * hminus) 2 ≤ ((148809291898303271992918981817839/120000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hminus) 2 2.52 2 (2 * hminus) 2 = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((11538253789929382857/5000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2.52 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 2 2.52 + solY 2 (2 * hminus) 2.52 (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) (2 * hminus) 2.52 ∧ solY (2 * hminus) 2 2.52 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 2 2.52 + solY 2 (2 * hminus) 2.52 (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) (2 * hminus) 2.52 ≤ ((3606233926839149323/1562500000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s6_1.1, ztgcTrio_s6_1.2, ztgcTrio_s6_2.1, ztgcTrio_s6_2.2, ztgcTrio_s6_3.1, ztgcTrio_s6_3.2, ztgcTrio_s6_4.1, ztgcTrio_s6_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((8768651355003578713070723/2000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2.52 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hminus) 2 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2.52 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2.52 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hminus) 2 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2.52 2 2 ≤ ((43845036811155604237419503/10000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq56, ztgcTrio_eq206, ztgcTrio_eq206, ztgcTrio_eq15, ztgcTrio_eq153, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t17.1, ztgcTrioT_t17.2, hlm.1, hlm.2, ztgcTrioT_t17.1, ztgcTrioT_t17.2, ztgcTrioT_t102.1, ztgcTrioT_t102.2, ztgcTrioT_t102.1, ztgcTrioT_t102.2, ztgcTrioT_t92.1, ztgcTrioT_t92.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((21736395041515063001/20000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2.52 2 (2 * hminus) 2 := by
    rw [ztgcTrio_eq56]
    exact ztgcTrioT_t17.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c7 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((15876/390625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((422319497010831/1562500000000 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((4124305977269751/15258789062500 : ℝ)) := by
    rw [hEc]
    have hp0 : ((15876/390625 : ℝ)) ≤ ((15876/390625 : ℝ)) ∧ ((15876/390625 : ℝ)) ≤ ((15876/390625 : ℝ)) := by norm_num
    have hp1 : ((422319497010831/1562500000000 : ℝ)) ≤ ((15876/390625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ∧ ((15876/390625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ≤ ((4124305977269751/15258789062500 : ℝ)) := by
      have hf := ztgcTrioF_f3
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((164403308387309053666916126893023/10000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((822025724242185451557242421772313/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((164403308387309053666916126893023/10000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((422319497010831/1562500000000 : ℝ)) := by norm_num
    have hs2 : ((4124305977269751/15258789062500 : ℝ)) ≤ ((822025724242185451557242421772313/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((54801102795729684555638708964341/40000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) ≤ ((822025724242785451557242421772313/600000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((27330093015351908719/12500000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2.52 + solY 2 (2 * hminus) 2.52 (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2.52 ∧ solY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2.52 + solY 2 (2 * hminus) 2.52 (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2.52 ≤ ((218651409134332019541/100000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s7_1.1, ztgcTrio_s7_1.2, ztgcTrio_s7_2.1, ztgcTrio_s7_2.2, ztgcTrio_s7_3.1, ztgcTrio_s7_3.2, ztgcTrio_s7_4.1, ztgcTrio_s7_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((27874482618381677763898681/10000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2 ≤ ((69689953849183474256145537/25000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq55, ztgcTrio_eq205, ztgcTrio_eq205, ztgcTrio_eq5, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t4.1, ztgcTrioT_t4.2, hlm.1, hlm.2, ztgcTrioT_t4.1, ztgcTrioT_t4.2, hlm.1, hlm.2, ztgcTrioT_t1.1, ztgcTrioT_t1.2, ztgcTrioT_t101.1, ztgcTrioT_t101.2, ztgcTrioT_t101.1, ztgcTrioT_t101.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((4011623142509882223/4000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2.52 2 (2 * hminus) (2 * hminus) := by
    rw [ztgcTrio_eq55]
    exact ztgcTrioT_t4.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c8 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 (Real.sqrt 8) 2 2 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1330705002039654856249979603318367/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2)) ≤ ((1330746674130892922166741308796147/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1330705002039654856249979603318367/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((16887434029134686/95367431640625 : ℝ)) := by norm_num
    have hs2 : ((708354684284159/4000000000000 : ℝ)) ≤ ((1330746674130892922166741308796147/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((443568334012818285416659867772789/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 ∧ volY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 ≤ ((443582224710697640722247102932049/400000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2)) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((438259471563093127809/200000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 + solY (2 * hminus) 2 2 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) 2 (Real.sqrt 8) ∧ solY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 + solY (2 * hminus) 2 2 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) 2 (Real.sqrt 8) ≤ ((219152618444010279467/100000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s8_1.1, ztgcTrio_s8_1.2, ztgcTrio_s8_2.1, ztgcTrio_s8_2.2, ztgcTrio_s8_3.1, ztgcTrio_s8_3.2, ztgcTrio_s8_4.1, ztgcTrio_s8_4.2]
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((101436837705818511112351451/20000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) 2 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hminus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (Real.sqrt 8) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) 2 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hminus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (Real.sqrt 8) 2 2 ≤ ((507195423680970124941185623/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq62, ztgcTrio_eq252, ztgcTrio_eq261, ztgcTrio_eq204, ztgcTrio_eq193, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t44.1, ztgcTrioT_t44.2, ztgcTrioT_t165.1, ztgcTrioT_t165.2, ztgcTrioT_t171.1, ztgcTrioT_t171.2, ztgcTrioT_t143.1, ztgcTrioT_t143.2, ztgcTrioT_t133.1, ztgcTrioT_t133.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((106870594681673489937/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (Real.sqrt 8) 2 2 2 := by
    rw [ztgcTrio_eq62]
    exact ztgcTrioT_t44.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c9 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1330705002039654856249979603318367/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ≤ ((1330746674130892922166741308796147/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1330705002039654856249979603318367/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((16887434029134686/95367431640625 : ℝ)) := by norm_num
    have hs2 : ((708354684284159/4000000000000 : ℝ)) ≤ ((1330746674130892922166741308796147/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((443568334012818285416659867772789/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) ∧ volY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) ≤ ((443582224710697640722247102932049/400000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((9387264424603348454801/5000000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) ∧ solY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) ≤ ((4694371233874588693413/2500000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s9_1.1, ztgcTrio_s9_1.2, ztgcTrio_s9_2.1, ztgcTrio_s9_2.2, ztgcTrio_s9_3.1, ztgcTrio_s9_3.2, ztgcTrio_s9_4.1, ztgcTrio_s9_4.2]
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((1181929350217111706348493209/400000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2 ≤ ((738755095818912812098514321/250000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq251, ztgcTrio_eq260, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t43.1, ztgcTrioT_t43.2, hlm.1, hlm.2, ztgcTrioT_t15.1, ztgcTrioT_t15.2, ztgcTrioT_t137.1, ztgcTrioT_t137.2, ztgcTrioT_t170.1, ztgcTrioT_t170.2, ztgcTrioT_t98.1, ztgcTrioT_t98.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((1713321043047674165203/2000000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) :=
    ztgcTrioT_t43.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c10 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-128/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((21567836808269372/95367431640625 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((452354684284159/2000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-128/1 : ℝ)) ≤ ((-128/1 : ℝ)) ∧ ((-128/1 : ℝ)) ≤ ((-128/1 : ℝ)) := by norm_num
    have hp1 : ((21567836808269372/95367431640625 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((-128/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((452354684284159/2000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f26
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1503845605408594220443945913907411/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ≤ ((75195967668167557059676681668051/5000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1503845605408594220443945913907411/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((21567836808269372/95367431640625 : ℝ)) := by norm_num
    have hs2 : ((452354684284159/2000000000000 : ℝ)) ≤ ((75195967668167557059676681668051/5000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((501281868469131406814648637969137/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 ∧ volY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 ≤ ((25065322556075852353225560556017/20000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1169478775663912512367/500000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) (2 * hminus) (Real.sqrt 8) ∧ solY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) (2 * hminus) (Real.sqrt 8) ≤ ((146204536847662928901/62500000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s10_1.1, ztgcTrio_s10_1.2, ztgcTrio_s10_2.1, ztgcTrio_s10_2.2, ztgcTrio_s10_3.1, ztgcTrio_s10_3.2, ztgcTrio_s10_4.1, ztgcTrio_s10_4.2]
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((22433601604024234793039727/5000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (Real.sqrt 8) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (Real.sqrt 8) 2 2 ≤ ((224343123192230369228491929/50000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq61, ztgcTrio_eq246, ztgcTrio_eq246, ztgcTrio_eq17, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t19.1, ztgcTrioT_t19.2, hlm.1, hlm.2, ztgcTrioT_t19.1, ztgcTrioT_t19.2, ztgcTrioT_t118.1, ztgcTrioT_t118.2, ztgcTrioT_t118.1, ztgcTrioT_t118.2, ztgcTrioT_t95.1, ztgcTrioT_t95.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((49536471084505416149/50000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 := by
    rw [ztgcTrio_eq61]
    exact ztgcTrioT_t19.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c11 : 0 < ztgMain 1 0 0 0 (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((16275329/62500 : ℝ)) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((2543081744/9765625 : ℝ)) := by
    rw [hEc]
    have hp0 : ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) ∧ ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) := by norm_num
    have hp1 : ((16275329/62500 : ℝ)) ≤ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2543081744/9765625 : ℝ)) := by
      have hf := ztgcTrioF_f5
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1613707730662510000622693374738623/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((806863635606422047536356064139789/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1613707730662510000622693374738623/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((16275329/62500 : ℝ)) := by norm_num
    have hs2 : ((2543081744/9765625 : ℝ)) ≤ ((806863635606422047536356064139789/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((537902576887103333540897791579541/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ≤ ((806863635607022047536356064139789/600000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) = Real.sqrt (deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((209490844535981509599/100000000000000000000 : ℝ)) ≤ solY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (Real.sqrt 8) ∧ solY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (Real.sqrt 8) ≤ ((130938919576474475627/62500000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s11_1.1, ztgcTrio_s11_1.2, ztgcTrio_s11_2.1, ztgcTrio_s11_2.2, ztgcTrio_s11_3.1, ztgcTrio_s11_3.2, ztgcTrio_s11_4.1, ztgcTrio_s11_4.2]
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((104218588341681694438222163/40000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (Real.sqrt 8) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (Real.sqrt 8) 2 2 ≤ ((1302808760473223403560070257/500000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq60, ztgcTrio_eq245, ztgcTrio_eq245, ztgcTrio_eq1, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t5.1, ztgcTrioT_t5.2, hlm.1, hlm.2, ztgcTrioT_t5.1, ztgcTrioT_t5.2, hlm.1, hlm.2, ztgcTrioT_t2.1, ztgcTrioT_t2.2, ztgcTrioT_t117.1, ztgcTrioT_t117.2, ztgcTrioT_t117.1, ztgcTrioT_t117.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((70774375122673751573/80000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) := by
    rw [ztgcTrio_eq60]
    exact ztgcTrioT_t5.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c12 : 0 < ztgMain 1 0 0 0 2.52 2 (2 * hminus) 2 2 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((1092135479046260529/6103515625000000 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ∧ deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ≤ ((17894591750366439/100000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((1092135479046260529/6103515625000000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ≤ ((17894591750366439/100000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f44
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((334416915024247601930849757490539/25000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)) ≤ ((668853342489345658433424893389699/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((334416915024247601930849757490539/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((1092135479046260529/6103515625000000 : ℝ)) := by norm_num
    have hs2 : ((17894591750366439/100000000000000 : ℝ)) ≤ ((668853342489345658433424893389699/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((111472305007982533976949919163513/100000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 (2 * hminus) 2 2 2 ∧ volY 2.52 2 (2 * hminus) 2 2 2 ≤ ((668853342489945658433424893389699/600000000000000000000000000000000 : ℝ)) := by
    have hv : volY 2.52 2 (2 * hminus) 2 2 2 = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((692206845085922987/312500000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 2 2 + solY 2.52 2 2 2 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 2 2 + solY 2 2 2 2.52 2 (2 * hminus) ∧ solY 2.52 2 (2 * hminus) 2 2 2 + solY 2.52 2 2 2 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 2 2 + solY 2 2 2 2.52 2 (2 * hminus) ≤ ((2215273386536570543/1000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s12_1.1, ztgcTrio_s12_1.2, ztgcTrio_s12_2.1, ztgcTrio_s12_2.2, ztgcTrio_s12_3.1, ztgcTrio_s12_3.2, ztgcTrio_s12_4.1, ztgcTrio_s12_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((101828070803046802985450803/20000000000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2.52 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2.52 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 2 (2 * hminus) 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2.52 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2.52 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 2 (2 * hminus) 2 2 ≤ ((509151524303915114240132807/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq169, ztgcTrio_eq28, ztgcTrio_eq191, ztgcTrio_eq230, ztgcTrio_eq224, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t31.1, ztgcTrioT_t31.2, ztgcTrioT_t110.1, ztgcTrioT_t110.2, ztgcTrioT_t130.1, ztgcTrioT_t130.2, ztgcTrioT_t141.1, ztgcTrioT_t141.2, ztgcTrioT_t150.1, ztgcTrioT_t150.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((61694381602112141447/50000000000000000000 : ℝ)) ≤ dihY 2.52 2 (2 * hminus) 2 2 2 := by
    rw [ztgcTrio_eq103]
    exact ztgcTrioT_t53.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c13 : 0 < ztgMain 1 0 0 0 2.52 2 (2 * hminus) 2 2 (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((64598492267271758138031/312500000000000000000 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((630887022480712265572401/3051757812500000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((116057391/305175781250 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) ≤ ((11884671/31250000000 : ℝ)) := by
      have hf := ztgcTrioF_f31
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((3300130095966639/97656250000000000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) ≤ ((3300285297096639/97656250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f32
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((64598492267271758138031/312500000000000000000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ≤ ((630887022480712265572401/3051757812500000000000 : ℝ)) := by
      have hf := ztgcTrioF_f33
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hsqc : ((1437759281852374242307181476113801/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ≤ ((1437807565449855079375654498407013/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1437759281852374242307181476113801/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((64598492267271758138031/312500000000000000000 : ℝ)) := by norm_num
    have hs2 : ((630887022480712265572401/3051757812500000000000 : ℝ)) ≤ ((1437807565449855079375654498407013/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((479253093950391414102393825371267/400000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 (2 * hminus) 2 2 (2 * hminus) ∧ volY 2.52 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((1437807565451055079375654498407013/1200000000000000000000000000000000 : ℝ)) := by
    have hv : volY 2.52 2 (2 * hminus) 2 2 (2 * hminus) = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1050700616114098537427/500000000000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 2 (2 * hminus) + solY 2.52 2 (2 * hminus) 2 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 2 (2 * hminus) ∧ solY 2.52 2 (2 * hminus) 2 2 (2 * hminus) + solY 2.52 2 (2 * hminus) 2 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 2 (2 * hminus) ≤ ((131359689400080179491/62500000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s13_1.1, ztgcTrio_s13_1.2, ztgcTrio_s13_2.1, ztgcTrio_s13_2.2, ztgcTrio_s13_3.1, ztgcTrio_s13_3.2, ztgcTrio_s13_4.1, ztgcTrio_s13_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((43749282083737637112056371/12500000000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2.52 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2.52 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 (2 * hminus) 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2.52 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2.52 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 (2 * hminus) 2 2 ≤ ((218760179362324153912498377/62500000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq22, ztgcTrio_eq190, ztgcTrio_eq213, ztgcTrio_eq22, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t25.1, ztgcTrioT_t25.2, hlm.1, hlm.2, ztgcTrioT_t25.1, ztgcTrioT_t25.2, ztgcTrioT_t107.1, ztgcTrioT_t107.2, ztgcTrioT_t129.1, ztgcTrioT_t129.2, ztgcTrioT_t107.1, ztgcTrioT_t107.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((105555274996396205067/100000000000000000000 : ℝ)) ≤ dihY 2.52 2 (2 * hminus) 2 2 (2 * hminus) := by
    rw [ztgcTrio_eq100]
    exact ztgcTrioT_t61.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c14 : 0 < ztgMain 1 0 0 0 2.52 2 (2 * hminus) 2 (2 * hminus) 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-15876/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((26395850867927159367/119209289550781250 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((2214420535523827071/10000000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-15876/390625 : ℝ)) ≤ ((-15876/390625 : ℝ)) ∧ ((-15876/390625 : ℝ)) ≤ ((-15876/390625 : ℝ)) := by norm_num
    have hp1 : ((26395850867927159367/119209289550781250 : ℝ)) ≤ ((-15876/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ∧ ((-15876/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ≤ ((2214420535523827071/10000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f24
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1488033755522690701562444772944181/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ≤ ((148809291898183271992918981817839/10000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1488033755522690701562444772944181/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((26395850867927159367/119209289550781250 : ℝ)) := by norm_num
    have hs2 : ((2214420535523827071/10000000000000000 : ℝ)) ≤ ((148809291898183271992918981817839/10000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((496011251840496900520814924314727/400000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 ∧ volY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((148809291898303271992918981817839/120000000000000000000000000000000 : ℝ)) := by
    have hv : volY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((11538253789929382857/5000000000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 + solY 2.52 (2 * hminus) 2 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) 2.52 2 2 + solY 2 2 2 2.52 (2 * hminus) (2 * hminus) ∧ solY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 + solY 2.52 (2 * hminus) 2 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) 2.52 2 2 + solY 2 2 2 2.52 (2 * hminus) (2 * hminus) ≤ ((3606233926839149323/1562500000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s14_1.1, ztgcTrio_s14_1.2, ztgcTrio_s14_2.1, ztgcTrio_s14_2.2, ztgcTrio_s14_3.1, ztgcTrio_s14_3.2, ztgcTrio_s14_4.1, ztgcTrio_s14_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((8768651355003578713070723/2000000000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2.52 (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2.52 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hminus) 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2.52 (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2.52 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hminus) 2 2 ≤ ((43845036811155604237419503/10000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq164, ztgcTrio_eq153, ztgcTrio_eq206, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t17.1, ztgcTrioT_t17.2, hlm.1, hlm.2, ztgcTrioT_t17.1, ztgcTrioT_t17.2, ztgcTrioT_t102.1, ztgcTrioT_t102.2, ztgcTrioT_t92.1, ztgcTrioT_t92.2, ztgcTrioT_t102.1, ztgcTrioT_t102.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((111513535926234496279/100000000000000000000 : ℝ)) ≤ dihY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 :=
    ztgcTrioT_t50.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c15 : 0 < ztgMain 1 0 0 0 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((2099441003262916470377981913/7629394531250000000000000 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((440326912615723395864423/1600000000000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((2099441003262916470377981913/7629394531250000000000000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ≤ ((440326912615723395864423/1600000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f6
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((207356098889865473339011101324531/12500000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((1658928329931201779183299311851899/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((207356098889865473339011101324531/12500000000000000000000000000000 : ℝ)) ^ 2 ≤ ((2099441003262916470377981913/7629394531250000000000000 : ℝ)) := by norm_num
    have hs2 : ((440326912615723395864423/1600000000000000000000 : ℝ)) ≤ ((1658928329931201779183299311851899/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((69118699629905157779670367108177/50000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ volY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((1658928329932401779183299311851899/1200000000000000000000000000000000 : ℝ)) := by
    have hv : volY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((110426825958844377921/50000000000000000000 : ℝ)) ≤ solY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY 2.52 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 (2 * hminus) (2 * hminus) ∧ solY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY 2.52 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 (2 * hminus) (2 * hminus) ≤ ((110450946206226298461/50000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s15_1.1, ztgcTrio_s15_1.2, ztgcTrio_s15_2.1, ztgcTrio_s15_2.2, ztgcTrio_s15_3.1, ztgcTrio_s15_3.2, ztgcTrio_s15_4.1, ztgcTrio_s15_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((57716968505090822195766797/20000000000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2.52 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2.52 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2 ≤ ((288608953572901779305684373/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq163, ztgcTrio_eq151, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t24.1, ztgcTrioT_t24.2, hlm.1, hlm.2, ztgcTrioT_t6.1, ztgcTrioT_t6.2, hlm.1, hlm.2, ztgcTrioT_t21.1, ztgcTrioT_t21.2, ztgcTrioT_t100.1, ztgcTrioT_t100.2, ztgcTrioT_t91.1, ztgcTrioT_t91.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((20655510982699535937/20000000000000000000 : ℝ)) ≤ dihY 2.52 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) := by
    rw [ztgcTrio_eq97]
    exact ztgcTrioT_t45.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c16 : 0 < ztgMain 1 0 0 0 2.52 2 2.52 2 2 2 := by
  have hDc : ((70748156/390625 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) ∧ deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) ≤ ((70748156/390625 : ℝ)) := by norm_num [deltaX, hplus]
  have hsqc : ((1345790768879012550992311209739911/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2)) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2)) ≤ ((1345790768879039466807688790260089/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1345790768879012550992311209739911/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((70748156/390625 : ℝ)) := by norm_num
    have hs2 : ((70748156/390625 : ℝ)) ≤ ((1345790768879039466807688790260089/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((448596922959270850330770403246637/400000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 2.52 2 2 2 ∧ volY 2.52 2 2.52 2 2 2 ≤ ((448596922960079822269229596753363/400000000000000000000000000000000 : ℝ)) := by
    have hv : volY 2.52 2 2.52 2 2 2 = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((55446206769233699359/25000000000000000000 : ℝ)) ≤ solY 2.52 2 2.52 2 2 2 + solY 2.52 2 2 2 2 2.52 + solY 2 2 2.52 2.52 2 2 + solY 2 2 2 2.52 2 2.52 ∧ solY 2.52 2 2.52 2 2 2 + solY 2.52 2 2 2 2 2.52 + solY 2 2 2.52 2.52 2 2 + solY 2 2 2 2.52 2 2.52 ≤ ((110892414762610946857/50000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s16_1.1, ztgcTrio_s16_1.2, ztgcTrio_s16_2.1, ztgcTrio_s16_2.2, ztgcTrio_s16_3.1, ztgcTrio_s16_3.2, ztgcTrio_s16_4.1, ztgcTrio_s16_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hD : ((62089788047787174837/12500000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 2.52 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 2.52 2 2 2 + lmfun (2.52 / 2) * dihY 2.52 2.52 2 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 2.52 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 2.52 2 2.52 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 2.52 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 2.52 2 2 2 + lmfun (2.52 / 2) * dihY 2.52 2.52 2 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 2.52 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 2.52 2 2.52 2 2 ≤ ((124179576299624908271/25000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq225, ztgcTrio_eq231, ztgcTrio_eq225, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]
    constructor <;> linarith [ztgcTrioT_t146.1, ztgcTrioT_t146.2, ztgcTrioT_t152.1, ztgcTrioT_t152.2, ztgcTrioT_t156.1, ztgcTrioT_t156.2, ztgcTrioT_t152.1, ztgcTrioT_t152.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((60623159968524661929/50000000000000000000 : ℝ)) ≤ dihY 2.52 2 2.52 2 2 2 :=
    ztgcTrioT_t56.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c17 : 0 < ztgMain 1 0 0 0 2.52 2 2.52 2 2 (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((787655626205065584119/3814697265625000000 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((2064943011869580671/10000000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((787655626205065584119/3814697265625000000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ≤ ((2064943011869580671/10000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f35
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((57477535991153494524640088459307/4000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ≤ ((179623869684579625138696845778289/12500000000000000000000000000000 : ℝ)) := by
    have hs1 : ((57477535991153494524640088459307/4000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((787655626205065584119/3814697265625000000 : ℝ)) := by norm_num
    have hs2 : ((2064943011869580671/10000000000000000 : ℝ)) ≤ ((179623869684579625138696845778289/12500000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((19159178663701831508213362819769/16000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 2.52 2 2 (2 * hminus) ∧ volY 2.52 2 2.52 2 2 (2 * hminus) ≤ ((179623869684729625138696845778289/150000000000000000000000000000000 : ℝ)) := by
    have hv : volY 2.52 2 2.52 2 2 (2 * hminus) = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((207992279562516955597/100000000000000000000 : ℝ)) ≤ solY 2.52 2 2.52 2 2 (2 * hminus) + solY 2.52 2 (2 * hminus) 2 2 2.52 + solY 2 2 2.52 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 2 2.52 ∧ solY 2.52 2 2.52 2 2 (2 * hminus) + solY 2.52 2 (2 * hminus) 2 2 2.52 + solY 2 2 2.52 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 2 2.52 ≤ ((520041015545128672499/250000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s17_1.1, ztgcTrio_s17_1.2, ztgcTrio_s17_2.1, ztgcTrio_s17_2.2, ztgcTrio_s17_3.1, ztgcTrio_s17_3.2, ztgcTrio_s17_4.1, ztgcTrio_s17_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((163859612104339942783205669/50000000000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 2.52 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 2.52 2 (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 2.52 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 2.52 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2.52 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 2.52 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 2.52 2 (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 2.52 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 2.52 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2.52 2 2 ≤ ((1638661752458294623751444953/500000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq219, ztgcTrio_eq214, ztgcTrio_eq23, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t26.1, ztgcTrioT_t26.2, ztgcTrioT_t135.1, ztgcTrioT_t135.2, ztgcTrioT_t151.1, ztgcTrioT_t151.2, ztgcTrioT_t108.1, ztgcTrioT_t108.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((6443032999450695269/6250000000000000000 : ℝ)) ≤ dihY 2.52 2 2.52 2 2 (2 * hminus) := by
    rw [ztgcTrio_eq105]
    exact ztgcTrioT_t62.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c18 : 0 < ztgMain 1 0 0 0 2.52 2 2.52 2 (2 * hminus) 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-4/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((4386046610776207/19531250000000 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((219308227452305039/976562500000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((-15397/1220703125 : ℝ)) ≤ ((-4/390625 : ℝ)) * (hminus) ∧ ((-4/390625 : ℝ)) * (hminus) ≤ ((-4927/390625000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/15258789062500 : ℝ)) ≤ ((-4/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-4/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1562500000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((4386046610776207/19531250000000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) ≤ ((219308227452305039/976562500000000 : ℝ)) := by
      have hf := ztgcTrioF_f38
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hsqc : ((749275627642687486143723573050211/50000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ≤ ((1498571402740506226814027404912411/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((749275627642687486143723573050211/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((4386046610776207/19531250000000 : ℝ)) := by norm_num
    have hs2 : ((219308227452305039/976562500000000 : ℝ)) ≤ ((1498571402740506226814027404912411/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((249758542547362495381241191016737/200000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 2.52 2 (2 * hminus) 2 ∧ volY 2.52 2 2.52 2 (2 * hminus) 2 ≤ ((1498571402741706226814027404912411/1200000000000000000000000000000000 : ℝ)) := by
    have hv : volY 2.52 2 2.52 2 (2 * hminus) 2 = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1810318921768322569/781250000000000000 : ℝ)) ≤ solY 2.52 2 2.52 2 (2 * hminus) 2 + solY 2.52 (2 * hminus) 2 2 2 2.52 + solY 2 (2 * hminus) 2.52 2.52 2 2 + solY 2 2 2 2.52 (2 * hminus) 2.52 ∧ solY 2.52 2 2.52 2 (2 * hminus) 2 + solY 2.52 (2 * hminus) 2 2 2 2.52 + solY 2 (2 * hminus) 2.52 2.52 2 2 + solY 2 2 2 2.52 (2 * hminus) 2.52 ≤ ((57933762300541937177/25000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s18_1.1, ztgcTrio_s18_1.2, ztgcTrio_s18_2.1, ztgcTrio_s18_2.2, ztgcTrio_s18_3.1, ztgcTrio_s18_3.2, ztgcTrio_s18_4.1, ztgcTrio_s18_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((85771605468186866998577587/20000000000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 2.52 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 2.52 (2 * hminus) 2 2 + lmfun (2.52 / 2) * dihY 2.52 2.52 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2.52 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2.52 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 2.52 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 2.52 (2 * hminus) 2 2 + lmfun (2.52 / 2) * dihY 2.52 2.52 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2.52 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2.52 2 2 ≤ ((428864944142347548625132051/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq218, ztgcTrio_eq208, ztgcTrio_eq25, ztgcTrio_eq208, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t28.1, ztgcTrioT_t28.2, ztgcTrioT_t145.1, ztgcTrioT_t145.2, ztgcTrioT_t104.1, ztgcTrioT_t104.2, ztgcTrioT_t104.1, ztgcTrioT_t104.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((2747390430343595661/2500000000000000000 : ℝ)) ≤ dihY 2.52 2 2.52 2 (2 * hminus) 2 :=
    ztgcTrioT_t51.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c19 : 0 < ztgMain 1 0 0 0 2.52 2 2.52 2 (2 * hminus) (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((6765499111666776491/24414062500000000 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((17320510586075924471/62500000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((6765499111666776491/24414062500000000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ≤ ((17320510586075924471/62500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f8
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1664676676156260749933238437226033/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((832358350377438596683503774302731/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1664676676156260749933238437226033/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((6765499111666776491/24414062500000000 : ℝ)) := by norm_num
    have hs2 : ((17320510586075924471/62500000000000000 : ℝ)) ≤ ((832358350377438596683503774302731/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((554892225385020249977746145742011/400000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) ∧ volY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) ≤ ((832358350378038596683503774302731/600000000000000000000000000000000 : ℝ)) := by
    have hv : volY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1099543662882124243307/500000000000000000000 : ℝ)) ≤ solY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) + solY 2.52 (2 * hminus) (2 * hminus) 2 2 2.52 + solY 2 (2 * hminus) 2.52 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 (2 * hminus) 2.52 ∧ solY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) + solY 2.52 (2 * hminus) (2 * hminus) 2 2 2.52 + solY 2 (2 * hminus) 2.52 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 (2 * hminus) 2.52 ≤ ((137456014800242757993/62500000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s19_1.1, ztgcTrio_s19_1.2, ztgcTrio_s19_2.1, ztgcTrio_s19_2.2, ztgcTrio_s19_3.1, ztgcTrio_s19_3.2, ztgcTrio_s19_4.1, ztgcTrio_s19_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((541754594059230683548659411/200000000000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 2.52 (2 * hminus) (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 2.52 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2.52 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) 2.52 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 2.52 (2 * hminus) (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 2.52 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2.52 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) 2.52 2 2 ≤ ((677225425597823118575647559/250000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq217, ztgcTrio_eq207, ztgcTrio_eq21, ztgcTrio_eq19, hfK]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t7.1, ztgcTrioT_t7.2, hlm.1, hlm.2, ztgcTrioT_t22.1, ztgcTrioT_t22.2, ztgcTrioT_t124.1, ztgcTrioT_t124.2, ztgcTrioT_t103.1, ztgcTrioT_t103.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((2027398434405461557/2000000000000000000 : ℝ)) ≤ dihY 2.52 2 2.52 2 (2 * hminus) (2 * hminus) := by
    rw [ztgcTrio_eq104]
    exact ztgcTrioT_t46.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c20 : 0 < ztgMain 1 0 0 0 2.52 2 (Real.sqrt 8) 2 2 2 := by
  have hDc : ((70748156/390625 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) ∧ deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) ≤ ((70748156/390625 : ℝ)) := by norm_num [deltaX, hplus]
  have hsqc : ((1345790768879012550992311209739911/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2)) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2)) ≤ ((1345790768879039466807688790260089/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1345790768879012550992311209739911/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((70748156/390625 : ℝ)) := by norm_num
    have hs2 : ((70748156/390625 : ℝ)) ≤ ((1345790768879039466807688790260089/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((448596922959270850330770403246637/400000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 (Real.sqrt 8) 2 2 2 ∧ volY 2.52 2 (Real.sqrt 8) 2 2 2 ≤ ((448596922960079822269229596753363/400000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY 2.52 2 (Real.sqrt 8) 2 2 2 = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2)) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((441014674829513923641/200000000000000000000 : ℝ)) ≤ solY 2.52 2 (Real.sqrt 8) 2 2 2 + solY 2.52 2 2 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) 2.52 2 2 + solY 2 2 2 2.52 2 (Real.sqrt 8) ∧ solY 2.52 2 (Real.sqrt 8) 2 2 2 + solY 2.52 2 2 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) 2.52 2 2 + solY 2 2 2 2.52 2 (Real.sqrt 8) ≤ ((220507339863044644207/100000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s20_1.1, ztgcTrio_s20_1.2, ztgcTrio_s20_2.1, ztgcTrio_s20_2.2, ztgcTrio_s20_3.1, ztgcTrio_s20_3.2, ztgcTrio_s20_4.1, ztgcTrio_s20_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hD : ((1989123098221896033169/400000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 (Real.sqrt 8) 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2.52 2 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) 2.52 2 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2.52 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 2.52 2 (Real.sqrt 8) 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 (Real.sqrt 8) 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2.52 2 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) 2.52 2 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2.52 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 2.52 2 (Real.sqrt 8) 2 2 ≤ ((994561550743353114577/200000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq263, ztgcTrio_eq233, ztgcTrio_eq227, hfK, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]
    constructor <;> linarith [ztgcTrioT_t167.1, ztgcTrioT_t167.2, ztgcTrioT_t173.1, ztgcTrioT_t173.2, ztgcTrioT_t158.1, ztgcTrioT_t158.2, ztgcTrioT_t155.1, ztgcTrioT_t155.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((21685231404168188973/20000000000000000000 : ℝ)) ≤ dihY 2.52 2 (Real.sqrt 8) 2 2 2 := by
    rw [ztgcTrio_eq107]
    exact ztgcTrioT_t64.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c21 : 0 < ztgMain 1 0 0 0 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((566912360882198029/3051757812500000 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((9289178517726439/50000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((566912360882198029/3051757812500000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ≤ ((9289178517726439/50000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f37
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((340739858996084921301410039116713/25000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ≤ ((681512234583012632222345830058171/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((340739858996084921301410039116713/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((566912360882198029/3051757812500000 : ℝ)) := by norm_num
    have hs2 : ((9289178517726439/50000000000000 : ℝ)) ≤ ((681512234583012632222345830058171/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((113579952998594973767136679705571/100000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) ∧ volY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) ≤ ((681512234583612632222345830058171/600000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1909558520948869346037/1000000000000000000000 : ℝ)) ≤ solY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) + solY 2.52 2 (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 2 (Real.sqrt 8) ∧ solY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) + solY 2.52 2 (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 2 (Real.sqrt 8) ≤ ((238740409790350631503/125000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s21_1.1, ztgcTrio_s21_1.2, ztgcTrio_s21_2.1, ztgcTrio_s21_2.2, ztgcTrio_s21_3.1, ztgcTrio_s21_3.2, ztgcTrio_s21_4.1, ztgcTrio_s21_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((58380235776697354810728449/20000000000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2.52 2 (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) 2.52 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2.52 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2.52 2 (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) 2.52 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2.52 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2 ≤ ((291918098771532365308615239/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq255, ztgcTrio_eq262, ztgcTrio_eq215, hfK, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t27.1, ztgcTrioT_t27.2, ztgcTrioT_t138.1, ztgcTrioT_t138.2, ztgcTrioT_t172.1, ztgcTrioT_t172.2, ztgcTrioT_t109.1, ztgcTrioT_t109.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((1751305615179934068249/2000000000000000000000 : ℝ)) ≤ dihY 2.52 2 (Real.sqrt 8) 2 2 (2 * hminus) :=
    ztgcTrioT_t63.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c22 : 0 < ztgMain 1 0 0 0 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((21952901802572186/95367431640625 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((920815801724159/4000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((21952901802572186/95367431640625 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ))) ≤ ((920815801724159/4000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f42
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((303442158972898636478410270983291/20000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ≤ ((758623672236512064136722365044779/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((303442158972898636478410270983291/20000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((21952901802572186/95367431640625 : ℝ)) := by norm_num
    have hs2 : ((920815801724159/4000000000000 : ℝ)) ≤ ((758623672236512064136722365044779/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((101147386324219545492803423661097/80000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 ∧ volY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 ≤ ((252874557412370688045574121681593/200000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((235587851398676196197/100000000000000000000 : ℝ)) ≤ solY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 + solY 2.52 (2 * hminus) 2 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 2 + solY 2 2 2 2.52 (2 * hminus) (Real.sqrt 8) ∧ solY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 + solY 2.52 (2 * hminus) 2 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 2 + solY 2 2 2 2.52 (2 * hminus) (Real.sqrt 8) ≤ ((1178027183106242616391/500000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s22_1.1, ztgcTrio_s22_1.2, ztgcTrio_s22_2.1, ztgcTrio_s22_2.2, ztgcTrio_s22_3.1, ztgcTrio_s22_3.2, ztgcTrio_s22_4.1, ztgcTrio_s22_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((88155137997387936547181089/20000000000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2.52 (2 * hminus) 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) 2.52 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) 2.52 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (Real.sqrt 8) 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2.52 (2 * hminus) 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) 2.52 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) 2.52 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (Real.sqrt 8) 2 2 ≤ ((440782500992185481292608961/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq254, ztgcTrio_eq248, ztgcTrio_eq27, ztgcTrio_eq211, hfK, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t30.1, ztgcTrioT_t30.2, ztgcTrioT_t166.1, ztgcTrioT_t166.2, ztgcTrioT_t120.1, ztgcTrioT_t120.2, ztgcTrioT_t144.1, ztgcTrioT_t144.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((100077274623951082549/100000000000000000000 : ℝ)) ≤ dihY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) 2 := by
    rw [ztgcTrio_eq106]
    exact ztgcTrioT_t52.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c23 : 0 < ztgMain 1 0 0 0 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hEc : deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) := by
    unfold deltaX; ring
  have hDc : ((821208270778013077/3051757812500000 : ℝ)) ≤ deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((26910646986908903/100000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) ∧ ((-4/390625 : ℝ)) ≤ ((-4/390625 : ℝ)) := by norm_num
    have hp1 : ((821208270778013077/3051757812500000 : ℝ)) ≤ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ∧ ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ≤ ((26910646986908903/100000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f9
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((410101760366050750882396339451481/25000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((820223246849743969332468497357671/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((410101760366050750882396339451481/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((821208270778013077/3051757812500000 : ℝ)) := by norm_num
    have hs2 : ((26910646986908903/100000000000000 : ℝ)) ≤ ((820223246849743969332468497357671/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((136700586788583583627465446483827/100000000000000000000000000000000 : ℝ)) ≤ volY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ∧ volY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ≤ ((820223246850343969332468497357671/600000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) = Real.sqrt (deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1058624661358352897253/500000000000000000000 : ℝ)) ≤ solY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + solY 2.52 (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 (2 * hminus) (Real.sqrt 8) ∧ solY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + solY 2.52 (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) 2.52 2 (2 * hminus) + solY 2 2 (2 * hminus) 2.52 (2 * hminus) (Real.sqrt 8) ≤ ((1058735895691116681057/500000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s23_1.1, ztgcTrio_s23_1.2, ztgcTrio_s23_2.1, ztgcTrio_s23_2.2, ztgcTrio_s23_3.1, ztgcTrio_s23_3.2, ztgcTrio_s23_4.1, ztgcTrio_s23_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((203889999786858350012346713/80000000000000000000000000 : ℝ)) ≤ lmfun (2.52 / 2) * dihY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2.52 (2 * hminus) (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) 2.52 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) 2.52 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) (Real.sqrt 8) 2 2 ∧ lmfun (2.52 / 2) * dihY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2.52 (2 * hminus) (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) 2.52 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) 2.52 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2.52 (2 * hminus) (Real.sqrt 8) 2 2 ≤ ((127438006664978150219357387/50000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq253, ztgcTrio_eq247, ztgcTrio_eq20, hfK, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t8.1, ztgcTrioT_t8.2, hlm.1, hlm.2, ztgcTrioT_t23.1, ztgcTrioT_t23.2, ztgcTrioT_t126.1, ztgcTrioT_t126.2, ztgcTrioT_t119.1, ztgcTrioT_t119.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((358394044511127596341/400000000000000000000 : ℝ)) ≤ dihY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) :=
    ztgcTrioT_t47.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c24 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 (2 * hminus) 2 2 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hpsq : 2 * hplus * (2 * hplus) = ((43917129/6250000 : ℝ)) := by norm_num [hplus]
  have hEc : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) := by
    unfold deltaX; simp only [hpsq]; ring
  have hDc : ((17656909518720649089/97656250000000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ≤ ((11301091292245832439/62500000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((17656909518720649089/97656250000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ≤ ((11301091292245832439/62500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f59
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((672322008920754859079910792384177/50000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)) ≤ ((672341915761498792519157614920691/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((672322008920754859079910792384177/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((17656909518720649089/97656250000000000 : ℝ)) := by norm_num
    have hs2 : ((11301091292245832439/62500000000000000 : ℝ)) ≤ ((672341915761498792519157614920691/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((224107336306718286359970264128059/200000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 (2 * hminus) 2 2 2 ∧ volY (2 * hplus) 2 (2 * hminus) 2 2 2 ≤ ((672341915762098792519157614920691/600000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hplus) 2 (2 * hminus) 2 2 2 = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1382399347862384088029/625000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 2 2 + solY (2 * hplus) 2 2 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) 2 (2 * hminus) ∧ solY (2 * hplus) 2 (2 * hminus) 2 2 2 + solY (2 * hplus) 2 2 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) 2 (2 * hminus) ≤ ((5530122749152191624523/2500000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s24_1.1, ztgcTrio_s24_1.2, ztgcTrio_s24_2.1, ztgcTrio_s24_2.2, ztgcTrio_s24_3.1, ztgcTrio_s24_3.2, ztgcTrio_s24_4.1, ztgcTrio_s24_4.2]
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((25447355061559477117521993/5000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hplus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hplus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 (2 * hminus) 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hplus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hplus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 (2 * hminus) 2 2 ≤ ((508957887714485266854875401/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq175, ztgcTrio_eq192, ztgcTrio_eq242, ztgcTrio_eq239, hfP]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t40.1, ztgcTrioT_t40.2, ztgcTrioT_t116.1, ztgcTrioT_t116.2, ztgcTrioT_t132.1, ztgcTrioT_t132.2, ztgcTrioT_t142.1, ztgcTrioT_t142.2, ztgcTrioT_t161.1, ztgcTrioT_t161.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((127946324982828187619/100000000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 (2 * hminus) 2 2 2 := by
    rw [ztgcTrio_eq123]
    exact ztgcTrioT_t74.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c25 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hpsq : 2 * hplus * (2 * hplus) = ((43917129/6250000 : ℝ)) := by norm_num [hplus]
  have hEc : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) := by
    unfold deltaX; simp only [hpsq]; ring
  have hDc : ((1695925119082662616457277/7812500000000000000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((5300113052227300899529383/24414062500000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((126276141/305175781250000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) ≤ ((12931071/31250000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f50
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((3722838968127789/976562500000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) ≤ ((3723002224935489/976562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f51
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1695925119082662616457277/7812500000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ≤ ((5300113052227300899529383/24414062500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f52
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hsqc : ((736679060450642361909395493502713/50000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ≤ ((1473406361528395827163615283810931/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((736679060450642361909395493502713/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((1695925119082662616457277/7812500000000000000000 : ℝ)) := by norm_num
    have hs2 : ((5300113052227300899529383/24414062500000000000000 : ℝ)) ≤ ((1473406361528395827163615283810931/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((245559686816680787303131831167571/200000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ volY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((491135453843198609054538427936977/400000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((212999114162702365173/100000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) + solY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) ∧ solY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) + solY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) ≤ ((16643351849906281163/7812500000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s25_1.1, ztgcTrio_s25_1.2, ztgcTrio_s25_2.1, ztgcTrio_s25_2.2, ztgcTrio_s25_3.1, ztgcTrio_s25_3.2, ztgcTrio_s25_4.1, ztgcTrio_s25_4.2]
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((14297299786597519407224119/4000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hplus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hplus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 2 ≤ ((893634701990951760031179007/250000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq172, ztgcTrio_eq34, ztgcTrio_eq236, ztgcTrio_eq34, hfP]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t36.1, ztgcTrioT_t36.2, hlm.1, hlm.2, ztgcTrioT_t36.1, ztgcTrioT_t36.2, ztgcTrioT_t113.1, ztgcTrioT_t113.2, ztgcTrioT_t131.1, ztgcTrioT_t131.2, ztgcTrioT_t113.1, ztgcTrioT_t113.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((54777465021194071293/50000000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 (2 * hminus) 2 2 (2 * hminus) := by
    rw [ztgcTrio_eq121]
    exact ztgcTrioT_t71.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c26 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hpsq : 2 * hplus * (2 * hplus) = ((43917129/6250000 : ℝ)) := by norm_num [hplus]
  have hEc : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-43917129/9765625000000 : ℝ)) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) := by
    unfold deltaX; simp only [hpsq]; ring
  have hDc : ((538819006772962363045869/2384185791015625000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((22601655462730639619511/100000000000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-43917129/9765625000000 : ℝ)) ≤ ((-43917129/9765625000000 : ℝ)) ∧ ((-43917129/9765625000000 : ℝ)) ≤ ((-43917129/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((538819006772962363045869/2384185791015625000000 : ℝ)) ≤ ((-43917129/9765625000000 : ℝ)) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) ∧ ((-43917129/9765625000000 : ℝ)) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) ≤ ((22601655462730639619511/100000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f25
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((751659948943639329100510563531543/50000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ≤ ((1503384696700451705546967004366717/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((751659948943639329100510563531543/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((538819006772962363045869/2384185791015625000000 : ℝ)) := by norm_num
    have hs2 : ((22601655462730639619511/100000000000000000000 : ℝ)) ≤ ((1503384696700451705546967004366717/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((250553316314346443033503521177181/200000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 ∧ volY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((1503384696701651705546967004366717/1200000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1162151495367315711963/500000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 + solY (2 * hplus) (2 * hminus) 2 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) (2 * hminus) (2 * hminus) ∧ solY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 + solY (2 * hplus) (2 * hminus) 2 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) (2 * hminus) (2 * hminus) ≤ ((581164825470836717451/250000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s26_1.1, ztgcTrio_s26_1.2, ztgcTrio_s26_2.1, ztgcTrio_s26_2.2, ztgcTrio_s26_3.1, ztgcTrio_s26_3.2, ztgcTrio_s26_4.1, ztgcTrio_s26_4.2]
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((44288542090277795598549663/10000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hplus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hplus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) (2 * hminus) 2 2 ≤ ((221451577372852179232305363/50000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq171, ztgcTrio_eq156, ztgcTrio_eq234, hfP]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t18.1, ztgcTrioT_t18.2, hlm.1, hlm.2, ztgcTrioT_t18.1, ztgcTrioT_t18.2, ztgcTrioT_t112.1, ztgcTrioT_t112.2, ztgcTrioT_t94.1, ztgcTrioT_t94.2, ztgcTrioT_t112.1, ztgcTrioT_t112.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((14342823058098574621/12500000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) 2 := by
    rw [ztgcTrio_eq120]
    exact ztgcTrioT_t68.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c27 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hpsq : 2 * hplus * (2 * hplus) = ((43917129/6250000 : ℝ)) := by norm_num [hplus]
  have hEc : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
    unfold deltaX; simp only [hpsq]; ring
  have hDc : ((2199120257481218179362356913/7629394531250000000000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((461232446970007658059623/1600000000000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((2199120257481218179362356913/7629394531250000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((461232446970007658059623/1600000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f11
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((848886167852575602838321474159083/50000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((1697852406295260258624062952432801/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((848886167852575602838321474159083/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((2199120257481218179362356913/7629394531250000000000000 : ℝ)) := by norm_num
    have hs2 : ((461232446970007658059623/1600000000000000000000 : ℝ)) ≤ ((1697852406295260258624062952432801/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((282962055950658534279440491386361/200000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ volY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((565950802098820086208020984144267/400000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((55815826841029285359/25000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) ∧ solY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) ≤ ((111655606238386314737/50000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s27_1.1, ztgcTrio_s27_1.2, ztgcTrio_s27_2.1, ztgcTrio_s27_2.2, ztgcTrio_s27_3.1, ztgcTrio_s27_3.2, ztgcTrio_s27_4.1, ztgcTrio_s27_4.2]
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((29477101575443746739399101/10000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hplus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hplus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2 ≤ ((294794502503028545399895553/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq170, ztgcTrio_eq154, ztgcTrio_eq31, hfP]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t35.1, ztgcTrioT_t35.2, hlm.1, hlm.2, ztgcTrioT_t9.1, ztgcTrioT_t9.2, hlm.1, hlm.2, ztgcTrioT_t32.1, ztgcTrioT_t32.2, ztgcTrioT_t111.1, ztgcTrioT_t111.2, ztgcTrioT_t93.1, ztgcTrioT_t93.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((105990833056916243187/100000000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) := by
    rw [ztgcTrio_eq119]
    exact ztgcTrioT_t65.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c28 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 2.52 2 2 2 := by
  have hDc : ((1794416980407359/9765625000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) ≤ ((1794416980407359/9765625000000 : ℝ)) := by norm_num [deltaX, hplus]
  have hsqc : ((1355537896164138550321038358478943/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2)) ≤ ((1355537896164165661078961641521057/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1355537896164138550321038358478943/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((1794416980407359/9765625000000 : ℝ)) := by norm_num
    have hs2 : ((1794416980407359/9765625000000 : ℝ)) ≤ ((1355537896164165661078961641521057/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((451845965387646183440346119492981/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 2.52 2 2 2 ∧ volY (2 * hplus) 2 2.52 2 2 2 ≤ ((451845965388455220359653880507019/400000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hplus) 2 2.52 2 2 2 = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((277354339837379231963/125000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2.52 2 2 2 + solY (2 * hplus) 2 2 2 2 2.52 + solY 2 2 2.52 (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) 2 2.52 ∧ solY (2 * hplus) 2 2.52 2 2 2 + solY (2 * hplus) 2 2 2 2 2.52 + solY 2 2 2.52 (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) 2 2.52 ≤ ((554708685795475889047/250000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s28_1.1, ztgcTrio_s28_1.2, ztgcTrio_s28_2.1, ztgcTrio_s28_2.2, ztgcTrio_s28_3.1, ztgcTrio_s28_3.2, ztgcTrio_s28_4.1, ztgcTrio_s28_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hD : ((1243814424174289682313/250000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 2.52 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hplus) 2 2 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hplus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 (2 * hplus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2.52 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 2.52 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hplus) 2 2 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hplus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 (2 * hplus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2.52 2 2 ≤ ((2487628852429590194407/500000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq223, ztgcTrio_eq226, ztgcTrio_eq243, ztgcTrio_eq240, hfK, hfP]
    simp only [zero_mul, zero_add]; rw [hf1]
    constructor <;> linarith [ztgcTrioT_t148.1, ztgcTrioT_t148.2, ztgcTrioT_t154.1, ztgcTrioT_t154.2, ztgcTrioT_t157.1, ztgcTrioT_t157.2, ztgcTrioT_t162.1, ztgcTrioT_t162.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((125658578156268873167/100000000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 2.52 2 2 2 := by
    rw [ztgcTrio_eq126]
    exact ztgcTrioT_t75.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c29 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 2.52 2 2 (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hpsq : 2 * hplus * (2 * hplus) = ((43917129/6250000 : ℝ)) := by norm_num [hplus]
  have hEc : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-49/9765625000000 : ℝ)) * (((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ))) := by
    unfold deltaX; simp only [hpsq]; ring
  have hDc : ((53222148422035521274241/244140625000000000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((34064601231569348815991/156250000000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-49/9765625000000 : ℝ)) ≤ ((-49/9765625000000 : ℝ)) ∧ ((-49/9765625000000 : ℝ)) ≤ ((-49/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((53222148422035521274241/244140625000000000000 : ℝ)) ≤ ((-49/9765625000000 : ℝ)) * (((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ))) ∧ ((-49/9765625000000 : ℝ)) * (((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ))) ≤ ((34064601231569348815991/156250000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f54
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1476475262023218373347379767668619/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ≤ ((738263922798019760939227980123783/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1476475262023218373347379767668619/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((53222148422035521274241/244140625000000000000 : ℝ)) := by norm_num
    have hs2 : ((34064601231569348815991/156250000000000000000 : ℝ)) ≤ ((738263922798019760939227980123783/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((492158420674006124449126589222873/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 2.52 2 2 (2 * hminus) ∧ volY (2 * hplus) 2 2.52 2 2 (2 * hminus) ≤ ((246087974266206586979742660041261/200000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hplus) 2 2.52 2 2 (2 * hminus) = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((132077739748141149733/62500000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2.52 2 2 (2 * hminus) + solY (2 * hplus) 2 (2 * hminus) 2 2 2.52 + solY 2 2 2.52 (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) 2 2.52 ∧ solY (2 * hplus) 2 2.52 2 2 (2 * hminus) + solY (2 * hplus) 2 (2 * hminus) 2 2 2.52 + solY 2 2 2.52 (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) 2 2.52 ≤ ((1056736611138069538953/500000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s29_1.1, ztgcTrio_s29_1.2, ztgcTrio_s29_2.1, ztgcTrio_s29_2.2, ztgcTrio_s29_3.1, ztgcTrio_s29_3.2, ztgcTrio_s29_4.1, ztgcTrio_s29_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((336300916973767122532276131/100000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 2.52 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hplus) 2 (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hplus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 (2 * hplus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2.52 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 2.52 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hplus) 2 (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hplus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2.52 2 (2 * hplus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2.52 2 2 ≤ ((168156666068634478191227319/50000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq222, ztgcTrio_eq237, ztgcTrio_eq35, hfK, hfP]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t37.1, ztgcTrioT_t37.2, ztgcTrioT_t136.1, ztgcTrioT_t136.2, ztgcTrioT_t153.1, ztgcTrioT_t153.2, ztgcTrioT_t114.1, ztgcTrioT_t114.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((107087179522832868349/100000000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 2.52 2 2 (2 * hminus) :=
    ztgcTrioT_t72.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c30 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 2.52 2 (2 * hminus) 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hpsq : 2 * hplus * (2 * hplus) = ((43917129/6250000 : ℝ)) := by norm_num [hplus]
  have hEc : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ))) := by
    unfold deltaX; simp only [hpsq]; ring
  have hDc : ((89650153266829150631/390625000000000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((8965442382159775166471/39062500000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((89650153266829150631/390625000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ))) ≤ ((8965442382159775166471/39062500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f40
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1514940237643313887297623566709633/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ≤ ((1514976319891815452863198918003031/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1514940237643313887297623566709633/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((89650153266829150631/390625000000000000 : ℝ)) := by norm_num
    have hs2 : ((8965442382159775166471/39062500000000000000 : ℝ)) ≤ ((1514976319891815452863198918003031/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((504980079214037962432541188903211/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 2.52 2 (2 * hminus) 2 ∧ volY (2 * hplus) 2 2.52 2 (2 * hminus) 2 ≤ ((1514976319893015452863198918003031/1200000000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hplus) 2 2.52 2 (2 * hminus) 2 = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1168332104096805058231/500000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2.52 2 (2 * hminus) 2 + solY (2 * hplus) (2 * hminus) 2 2 2 2.52 + solY 2 (2 * hminus) 2.52 (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) (2 * hminus) 2.52 ∧ solY (2 * hplus) 2 2.52 2 (2 * hminus) 2 + solY (2 * hplus) (2 * hminus) 2 2 2 2.52 + solY 2 (2 * hminus) 2.52 (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) (2 * hminus) 2.52 ≤ ((584209829587275716961/250000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s30_1.1, ztgcTrio_s30_1.2, ztgcTrio_s30_2.1, ztgcTrio_s30_2.2, ztgcTrio_s30_3.1, ztgcTrio_s30_3.2, ztgcTrio_s30_4.1, ztgcTrio_s30_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((4339754434026281828248919/1000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 2.52 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hplus) (2 * hminus) 2 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hplus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hplus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) 2.52 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 2.52 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2.52 (2 * hplus) (2 * hminus) 2 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hplus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hplus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2 2 2.52 + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) 2.52 2 2 ≤ ((433982556029360228897970277/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq221, ztgcTrio_eq210, ztgcTrio_eq37, ztgcTrio_eq235, hfK, hfP]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t29.1, ztgcTrioT_t29.2, ztgcTrioT_t147.1, ztgcTrioT_t147.2, ztgcTrioT_t106.1, ztgcTrioT_t106.2, ztgcTrioT_t159.1, ztgcTrioT_t159.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((112997018594525988647/100000000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 2.52 2 (2 * hminus) 2 := by
    rw [ztgcTrio_eq125]
    exact ztgcTrioT_t69.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c31 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hpsq : 2 * hplus * (2 * hplus) = ((43917129/6250000 : ℝ)) := by norm_num [hplus]
  have hEc : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) := by
    unfold deltaX; simp only [hpsq]; ring
  have hDc : ((14206139925377238607/48828125000000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((18184725288130442999/62500000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((14206139925377238607/48828125000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) ≤ ((18184725288130442999/62500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f13
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((852850727958474612192720415168593/50000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((53304440023983354344400239828213/3125000000000000000000000000000 : ℝ)) := by
    have hs1 : ((852850727958474612192720415168593/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((14206139925377238607/48828125000000000 : ℝ)) := by norm_num
    have hs2 : ((18184725288130442999/62500000000000000 : ℝ)) ≤ ((53304440023983354344400239828213/3125000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((284283575985958204064240138389531/200000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) ∧ volY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) ≤ ((53304440024020854344400239828213/37500000000000000000000000000000 : ℝ)) := by
    have hv : volY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) / 12 := rfl
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1113189449207542897331/500000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) + solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 2.52 + solY 2 (2 * hminus) 2.52 (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) 2.52 ∧ solY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) + solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 2.52 + solY 2 (2 * hminus) 2.52 (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) 2.52 ≤ ((556646659667368506889/250000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s31_1.1, ztgcTrio_s31_1.2, ztgcTrio_s31_2.1, ztgcTrio_s31_2.2, ztgcTrio_s31_3.1, ztgcTrio_s31_3.2, ztgcTrio_s31_4.1, ztgcTrio_s31_4.2]
  have hfK : lmfun (2.52 / 2) = 0 := ztg_lmfun_kink_zero
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((555667472276811658534845813/200000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hplus) (2 * hminus) (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hplus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) 2.52 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hplus) (2 * hminus) (2 * hminus) 2 + lmfun (2.52 / 2) * dihY 2.52 (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2.52 (2 * hminus) (2 * hplus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) 2 2 2.52 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) 2.52 2 2 ≤ ((694615773341762240898993793/250000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq220, ztgcTrio_eq209, ztgcTrio_eq32, ztgcTrio_eq29, hfK, hfP]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t10.1, ztgcTrioT_t10.2, hlm.1, hlm.2, ztgcTrioT_t33.1, ztgcTrioT_t33.2, ztgcTrioT_t125.1, ztgcTrioT_t125.2, ztgcTrioT_t105.1, ztgcTrioT_t105.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((104055314058689365787/100000000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 2.52 2 (2 * hminus) (2 * hminus) := by
    rw [ztgcTrio_eq124]
    exact ztgcTrioT_t66.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c32 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 (Real.sqrt 8) 2 2 2 := by
  have hDc : ((1837998680397359/9765625000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) ≤ ((1837998680397359/9765625000000 : ℝ)) := by norm_num [deltaX, hplus]
  have hsqc : ((1371900378572313819096214276724619/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2)) ≤ ((1371900378572341257103785723275381/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1371900378572313819096214276724619/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((1837998680397359/9765625000000 : ℝ)) := by norm_num
    have hs2 : ((1837998680397359/9765625000000 : ℝ)) ≤ ((1371900378572341257103785723275381/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((457300126190371273032071425574873/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 ∧ volY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 ≤ ((1371900378573541257103785723275381/1200000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2)) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((2232362348160168430487/1000000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 + solY (2 * hplus) 2 2 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) 2 (Real.sqrt 8) ∧ solY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 + solY (2 * hplus) 2 2 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) 2 (Real.sqrt 8) ≤ ((1116181186321520371669/500000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s32_1.1, ztgcTrio_s32_1.2, ztgcTrio_s32_2.1, ztgcTrio_s32_2.2, ztgcTrio_s32_3.1, ztgcTrio_s32_3.2, ztgcTrio_s32_4.1, ztgcTrio_s32_4.2]
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hD : ((10016225695994969551707/2000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hplus) 2 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hplus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 (2 * hplus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 (Real.sqrt 8) 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hplus) 2 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hplus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 (2 * hplus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 (2 * hplus) 2 (Real.sqrt 8) 2 2 ≤ ((5008112856159507438539/1000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq259, ztgcTrio_eq265, ztgcTrio_eq244, ztgcTrio_eq241, hfP, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]
    constructor <;> linarith [ztgcTrioT_t169.1, ztgcTrioT_t169.2, ztgcTrioT_t175.1, ztgcTrioT_t175.2, ztgcTrioT_t164.1, ztgcTrioT_t164.2, ztgcTrioT_t163.1, ztgcTrioT_t163.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((56144756473211449677/50000000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 (Real.sqrt 8) 2 2 2 := by
    rw [ztgcTrio_eq130]
    exact ztgcTrioT_t76.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c33 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hpsq : 2 * hplus * (2 * hplus) = ((43917129/6250000 : ℝ)) := by norm_num [hplus]
  have hEc : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) := by
    unfold deltaX; simp only [hpsq]; ring
  have hDc : ((9963647976108854089/48828125000000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((6377305364574283639/31250000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((9963647976108854089/48828125000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ≤ ((6377305364574283639/31250000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f56
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1428479998287358767100017126269481/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ≤ ((1428543914853096694739148530824093/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1428479998287358767100017126269481/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((9963647976108854089/48828125000000000 : ℝ)) := by norm_num
    have hs2 : ((6377305364574283639/31250000000000000 : ℝ)) ≤ ((1428543914853096694739148530824093/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((476159999428719589033339042089827/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) ∧ volY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) ≤ ((1428543914854296694739148530824093/1200000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((1976581156707643007829/1000000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) + solY (2 * hplus) 2 (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) ∧ solY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) + solY (2 * hplus) 2 (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 2 (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) ≤ ((197691005554753756613/100000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s33_1.1, ztgcTrio_s33_1.2, ztgcTrio_s33_2.1, ztgcTrio_s33_2.2, ztgcTrio_s33_3.1, ztgcTrio_s33_3.2, ztgcTrio_s33_4.1, ztgcTrio_s33_4.2]
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((12172272706116636295252177/4000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 (2 * hplus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 (2 * hplus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2 2 ≤ ((60864537943952996803883617/20000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq258, ztgcTrio_eq264, ztgcTrio_eq238, ztgcTrio_eq36, hfP, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t38.1, ztgcTrioT_t38.2, ztgcTrioT_t139.1, ztgcTrioT_t139.2, ztgcTrioT_t174.1, ztgcTrioT_t174.2, ztgcTrioT_t115.1, ztgcTrioT_t115.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((367692182738793902369/400000000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 (Real.sqrt 8) 2 2 (2 * hminus) := by
    rw [ztgcTrio_eq129]
    exact ztgcTrioT_t73.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c34 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hpsq : 2 * hplus * (2 * hplus) = ((43917129/6250000 : ℝ)) := by norm_num [hplus]
  have hEc : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) := by
    unfold deltaX; simp only [hpsq]; ring
  have hDc : ((1448294953112969279/6103515625000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((593249339859323279/2500000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((1448294953112969279/6103515625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) ≤ ((593249339859323279/2500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f57
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((308083524465703385264755342935339/20000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) ≤ ((1540453621319817786636213198023821/100000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((308083524465703385264755342935339/20000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((1448294953112969279/6103515625000000 : ℝ)) := by norm_num
    have hs2 : ((593249339859323279/2500000000000000 : ℝ)) ≤ ((1540453621319817786636213198023821/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((102694508155154461754918447645113/80000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 ∧ volY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 ≤ ((1540453621321017786636213198023821/1200000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((2393597983386139777389/1000000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 + solY (2 * hplus) (2 * hminus) 2 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) (2 * hminus) (Real.sqrt 8) ∧ solY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 + solY (2 * hplus) (2 * hminus) 2 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) (2 * hminus) (Real.sqrt 8) ≤ ((149610309851604766623/62500000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s34_1.1, ztgcTrio_s34_1.2, ztgcTrio_s34_2.1, ztgcTrio_s34_2.2, ztgcTrio_s34_3.1, ztgcTrio_s34_3.2, ztgcTrio_s34_4.1, ztgcTrio_s34_4.2]
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((357969126335418476498164703/80000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hplus) (2 * hminus) 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hplus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hplus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) (Real.sqrt 8) 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hplus) (2 * hminus) 2 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hplus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hplus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) 2 2 2 (Real.sqrt 8) + lmfun (2 / 2) * dihY 2 (2 * hplus) (2 * hminus) (Real.sqrt 8) 2 2 ≤ ((223733842451695192441946849/50000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq257, ztgcTrio_eq250, ztgcTrio_eq38, hfP, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t39.1, ztgcTrioT_t39.2, ztgcTrioT_t168.1, ztgcTrioT_t168.2, ztgcTrioT_t122.1, ztgcTrioT_t122.2, ztgcTrioT_t160.1, ztgcTrioT_t160.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((12825428546077987861/12500000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) 2 := by
    rw [ztgcTrio_eq128]
    exact ztgcTrioT_t70.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

theorem ztgcTrio_c35 : 0 < ztgMain 1 0 0 0 (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hpsq : 2 * hplus * (2 * hplus) = ((43917129/6250000 : ℝ)) := by norm_num [hplus]
  have hEc : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) := by
    unfold deltaX; simp only [hpsq]; ring
  have hDc : ((14032382534441894857/48828125000000000 : ℝ)) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((17962291948808582903/62500000000000000 : ℝ)) := by
    rw [hEc]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((14032382534441894857/48828125000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ≤ ((17962291948808582903/62500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f15
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hsqc : ((1695238019587114672519804128683751/100000000000000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ∧ Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((847638884167283636488841672751601/50000000000000000000000000000000 : ℝ)) := by
    have hs1 : ((1695238019587114672519804128683751/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((14032382534441894857/48828125000000000 : ℝ)) := by norm_num
    have hs2 : ((17962291948808582903/62500000000000000 : ℝ)) ≤ ((847638884167283636488841672751601/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hDc.1]) (by linarith [hDc.2, hs2])
  have hV : ((565079339861971557506601376227917/400000000000000000000000000000000 : ℝ)) ≤ volY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ∧ volY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ≤ ((847638884167883636488841672751601/600000000000000000000000000000000 : ℝ)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hv : volY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) = Real.sqrt (deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) / 12 := by
      unfold volY volXf; rw [hsq8]
    rw [hv]; constructor <;> linarith [hsqc.1, hsqc.2]
  have hS : ((541583471689791547399/250000000000000000000 : ℝ)) ≤ solY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (Real.sqrt 8) ∧ solY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + solY (2 * hplus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) + solY 2 (2 * hminus) (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hplus) (2 * hminus) (Real.sqrt 8) ≤ ((216655071722841149259/100000000000000000000 : ℝ)) := by
    constructor <;> linarith [ztgcTrio_s35_1.1, ztgcTrio_s35_1.2, ztgcTrio_s35_2.1, ztgcTrio_s35_2.2, ztgcTrio_s35_3.1, ztgcTrio_s35_3.2, ztgcTrio_s35_4.1, ztgcTrio_s35_4.2]
  have hfP : lmfun (2 * hplus / 2) = 0 := by norm_num [lmfun, h0, hplus]
  have hfS8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have hf1 : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
  have hlmv : 2 * hminus / 2 = hminus := by ring
  have hlm := ztg_lmfun_hminus_bounds
  have hD : ((211045730779806512477342121/80000000000000000000000000 : ℝ)) ≤ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hplus) (2 * hminus) (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hplus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) (Real.sqrt 8) 2 2 ∧ lmfun ((2 * hplus) / 2) * dihY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hplus) (2 * hminus) (2 * hminus) 2 + lmfun ((Real.sqrt 8) / 2) * dihY (Real.sqrt 8) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (Real.sqrt 8) (2 * hminus) (2 * hplus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) 2 2 (Real.sqrt 8) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hplus) (2 * hminus) (Real.sqrt 8) 2 2 ≤ ((263820328701781680541053141/100000000000000000000000000 : ℝ)) := by
    simp only [ztgcTrio_eq256, ztgcTrio_eq249, ztgcTrio_eq33, ztgcTrio_eq30, hfP, hfS8]
    simp only [zero_mul, zero_add]; rw [hf1]; rw [hlmv]
    constructor <;> nlinarith [hlm.1, hlm.2, ztgcTrioT_t11.1, ztgcTrioT_t11.2, hlm.1, hlm.2, ztgcTrioT_t34.1, ztgcTrioT_t34.2, ztgcTrioT_t127.1, ztgcTrioT_t127.2, ztgcTrioT_t121.1, ztgcTrioT_t121.2]
  have hA := g4v_AB_bounds
  have hγ := g4v_corner_value_bounds hV hS hD ⟨hA.1, hA.2.1⟩ ⟨hA.2.2.1, hA.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdmain : ((369180906589825648841/400000000000000000000 : ℝ)) ≤ dihY (2 * hplus) 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) := by
    rw [ztgcTrio_eq127]
    exact ztgcTrioT_t67.1
  exact ztg_main_pos_of_gD 1 0 0 0 _ _ _ _ _ _ _ _ hγ.1 hdmain (by norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5])

/-! ## Axiom audit -/

#print axioms ztgcTrio_c0
#print axioms ztgcTrio_c1
#print axioms ztgcTrio_c2
#print axioms ztgcTrio_c3
#print axioms ztgcTrio_c4
#print axioms ztgcTrio_c5
#print axioms ztgcTrio_c6
#print axioms ztgcTrio_c7
#print axioms ztgcTrio_c8
#print axioms ztgcTrio_c9
#print axioms ztgcTrio_c10
#print axioms ztgcTrio_c11
#print axioms ztgcTrio_c12
#print axioms ztgcTrio_c13
#print axioms ztgcTrio_c14
#print axioms ztgcTrio_c15
#print axioms ztgcTrio_c16
#print axioms ztgcTrio_c17
#print axioms ztgcTrio_c18
#print axioms ztgcTrio_c19
#print axioms ztgcTrio_c20
#print axioms ztgcTrio_c21
#print axioms ztgcTrio_c22
#print axioms ztgcTrio_c23
#print axioms ztgcTrio_c24
#print axioms ztgcTrio_c25
#print axioms ztgcTrio_c26
#print axioms ztgcTrio_c27
#print axioms ztgcTrio_c28
#print axioms ztgcTrio_c29
#print axioms ztgcTrio_c30
#print axioms ztgcTrio_c31
#print axioms ztgcTrio_c32
#print axioms ztgcTrio_c33
#print axioms ztgcTrio_c34
#print axioms ztgcTrio_c35
#print axioms ztgcTrio_eq0
#print axioms ztgcTrio_eq1
#print axioms ztgcTrio_eq2
#print axioms ztgcTrio_eq3
#print axioms ztgcTrio_eq4
#print axioms ztgcTrio_eq5
#print axioms ztgcTrio_eq6
#print axioms ztgcTrio_eq7
#print axioms ztgcTrio_eq8
#print axioms ztgcTrio_eq9
#print axioms ztgcTrio_eq10
#print axioms ztgcTrio_eq11
#print axioms ztgcTrio_eq12
#print axioms ztgcTrio_eq13
#print axioms ztgcTrio_eq14
#print axioms ztgcTrio_eq15
#print axioms ztgcTrio_eq16
#print axioms ztgcTrio_eq17
#print axioms ztgcTrio_eq18
#print axioms ztgcTrio_eq19
#print axioms ztgcTrio_eq20
#print axioms ztgcTrio_eq21
#print axioms ztgcTrio_eq22
#print axioms ztgcTrio_eq23
#print axioms ztgcTrio_eq24
#print axioms ztgcTrio_eq25
#print axioms ztgcTrio_eq26
#print axioms ztgcTrio_eq27
#print axioms ztgcTrio_eq28
#print axioms ztgcTrio_eq29
#print axioms ztgcTrio_eq30
#print axioms ztgcTrio_eq31
#print axioms ztgcTrio_eq32
#print axioms ztgcTrio_eq33
#print axioms ztgcTrio_eq34
#print axioms ztgcTrio_eq35
#print axioms ztgcTrio_eq36
#print axioms ztgcTrio_eq37
#print axioms ztgcTrio_eq38
#print axioms ztgcTrio_eq39
#print axioms ztgcTrio_eq40
#print axioms ztgcTrio_eq41
#print axioms ztgcTrio_eq42
#print axioms ztgcTrio_eq43
#print axioms ztgcTrio_eq44
#print axioms ztgcTrio_eq45
#print axioms ztgcTrio_eq46
#print axioms ztgcTrio_eq47
#print axioms ztgcTrio_eq48
#print axioms ztgcTrio_eq49
#print axioms ztgcTrio_eq50
#print axioms ztgcTrio_eq51
#print axioms ztgcTrio_eq52
#print axioms ztgcTrio_eq53
#print axioms ztgcTrio_eq54
#print axioms ztgcTrio_eq55
#print axioms ztgcTrio_eq56
#print axioms ztgcTrio_eq57
#print axioms ztgcTrio_eq58
#print axioms ztgcTrio_eq59
#print axioms ztgcTrio_eq60
#print axioms ztgcTrio_eq61
#print axioms ztgcTrio_eq62
#print axioms ztgcTrio_eq63
#print axioms ztgcTrio_eq64
#print axioms ztgcTrio_eq65
#print axioms ztgcTrio_eq66
#print axioms ztgcTrio_eq67
#print axioms ztgcTrio_eq68
#print axioms ztgcTrio_eq69
#print axioms ztgcTrio_eq70
#print axioms ztgcTrio_eq71
#print axioms ztgcTrio_eq72
#print axioms ztgcTrio_eq73
#print axioms ztgcTrio_eq74
#print axioms ztgcTrio_eq75
#print axioms ztgcTrio_eq76
#print axioms ztgcTrio_eq77
#print axioms ztgcTrio_eq78
#print axioms ztgcTrio_eq79
#print axioms ztgcTrio_eq80
#print axioms ztgcTrio_eq81
#print axioms ztgcTrio_eq82
#print axioms ztgcTrio_eq83
#print axioms ztgcTrio_eq84
#print axioms ztgcTrio_eq85
#print axioms ztgcTrio_eq86
#print axioms ztgcTrio_eq87
#print axioms ztgcTrio_eq88
#print axioms ztgcTrio_eq89
#print axioms ztgcTrio_eq90
#print axioms ztgcTrio_eq91
#print axioms ztgcTrio_eq92
#print axioms ztgcTrio_eq93
#print axioms ztgcTrio_eq94
#print axioms ztgcTrio_eq95
#print axioms ztgcTrio_eq96
#print axioms ztgcTrio_eq97
#print axioms ztgcTrio_eq98
#print axioms ztgcTrio_eq99
#print axioms ztgcTrio_eq100
#print axioms ztgcTrio_eq101
#print axioms ztgcTrio_eq102
#print axioms ztgcTrio_eq103
#print axioms ztgcTrio_eq104
#print axioms ztgcTrio_eq105
#print axioms ztgcTrio_eq106
#print axioms ztgcTrio_eq107
#print axioms ztgcTrio_eq108
#print axioms ztgcTrio_eq109
#print axioms ztgcTrio_eq110
#print axioms ztgcTrio_eq111
#print axioms ztgcTrio_eq112
#print axioms ztgcTrio_eq113
#print axioms ztgcTrio_eq114
#print axioms ztgcTrio_eq115
#print axioms ztgcTrio_eq116
#print axioms ztgcTrio_eq117
#print axioms ztgcTrio_eq118
#print axioms ztgcTrio_eq119
#print axioms ztgcTrio_eq120
#print axioms ztgcTrio_eq121
#print axioms ztgcTrio_eq122
#print axioms ztgcTrio_eq123
#print axioms ztgcTrio_eq124
#print axioms ztgcTrio_eq125
#print axioms ztgcTrio_eq126
#print axioms ztgcTrio_eq127
#print axioms ztgcTrio_eq128
#print axioms ztgcTrio_eq129
#print axioms ztgcTrio_eq130
#print axioms ztgcTrio_eq131
#print axioms ztgcTrio_eq132
#print axioms ztgcTrio_eq133
#print axioms ztgcTrio_eq134
#print axioms ztgcTrio_eq135
#print axioms ztgcTrio_eq136
#print axioms ztgcTrio_eq137
#print axioms ztgcTrio_eq138
#print axioms ztgcTrio_eq139
#print axioms ztgcTrio_eq140
#print axioms ztgcTrio_eq141
#print axioms ztgcTrio_eq142
#print axioms ztgcTrio_eq143
#print axioms ztgcTrio_eq144
#print axioms ztgcTrio_eq145
#print axioms ztgcTrio_eq146
#print axioms ztgcTrio_eq147
#print axioms ztgcTrio_eq148
#print axioms ztgcTrio_eq149
#print axioms ztgcTrio_eq150
#print axioms ztgcTrio_eq151
#print axioms ztgcTrio_eq152
#print axioms ztgcTrio_eq153
#print axioms ztgcTrio_eq154
#print axioms ztgcTrio_eq155
#print axioms ztgcTrio_eq156
#print axioms ztgcTrio_eq157
#print axioms ztgcTrio_eq158
#print axioms ztgcTrio_eq159
#print axioms ztgcTrio_eq160
#print axioms ztgcTrio_eq161
#print axioms ztgcTrio_eq162
#print axioms ztgcTrio_eq163
#print axioms ztgcTrio_eq164
#print axioms ztgcTrio_eq165
#print axioms ztgcTrio_eq166
#print axioms ztgcTrio_eq167
#print axioms ztgcTrio_eq168
#print axioms ztgcTrio_eq169
#print axioms ztgcTrio_eq170
#print axioms ztgcTrio_eq171
#print axioms ztgcTrio_eq172
#print axioms ztgcTrio_eq173
#print axioms ztgcTrio_eq174
#print axioms ztgcTrio_eq175
#print axioms ztgcTrio_eq176
#print axioms ztgcTrio_eq177
#print axioms ztgcTrio_eq178
#print axioms ztgcTrio_eq179
#print axioms ztgcTrio_eq180
#print axioms ztgcTrio_eq181
#print axioms ztgcTrio_eq182
#print axioms ztgcTrio_eq183
#print axioms ztgcTrio_eq184
#print axioms ztgcTrio_eq185
#print axioms ztgcTrio_eq186
#print axioms ztgcTrio_eq187
#print axioms ztgcTrio_eq188
#print axioms ztgcTrio_eq189
#print axioms ztgcTrio_eq190
#print axioms ztgcTrio_eq191
#print axioms ztgcTrio_eq192
#print axioms ztgcTrio_eq193
#print axioms ztgcTrio_eq194
#print axioms ztgcTrio_eq195
#print axioms ztgcTrio_eq196
#print axioms ztgcTrio_eq197
#print axioms ztgcTrio_eq198
#print axioms ztgcTrio_eq199
#print axioms ztgcTrio_eq200
#print axioms ztgcTrio_eq201
#print axioms ztgcTrio_eq202
#print axioms ztgcTrio_eq203
#print axioms ztgcTrio_eq204
#print axioms ztgcTrio_eq205
#print axioms ztgcTrio_eq206
#print axioms ztgcTrio_eq207
#print axioms ztgcTrio_eq208
#print axioms ztgcTrio_eq209
#print axioms ztgcTrio_eq210
#print axioms ztgcTrio_eq211
#print axioms ztgcTrio_eq212
#print axioms ztgcTrio_eq213
#print axioms ztgcTrio_eq214
#print axioms ztgcTrio_eq215
#print axioms ztgcTrio_eq216
#print axioms ztgcTrio_eq217
#print axioms ztgcTrio_eq218
#print axioms ztgcTrio_eq219
#print axioms ztgcTrio_eq220
#print axioms ztgcTrio_eq221
#print axioms ztgcTrio_eq222
#print axioms ztgcTrio_eq223
#print axioms ztgcTrio_eq224
#print axioms ztgcTrio_eq225
#print axioms ztgcTrio_eq226
#print axioms ztgcTrio_eq227
#print axioms ztgcTrio_eq228
#print axioms ztgcTrio_eq229
#print axioms ztgcTrio_eq230
#print axioms ztgcTrio_eq231
#print axioms ztgcTrio_eq232
#print axioms ztgcTrio_eq233
#print axioms ztgcTrio_eq234
#print axioms ztgcTrio_eq235
#print axioms ztgcTrio_eq236
#print axioms ztgcTrio_eq237
#print axioms ztgcTrio_eq238
#print axioms ztgcTrio_eq239
#print axioms ztgcTrio_eq240
#print axioms ztgcTrio_eq241
#print axioms ztgcTrio_eq242
#print axioms ztgcTrio_eq243
#print axioms ztgcTrio_eq244
#print axioms ztgcTrio_eq245
#print axioms ztgcTrio_eq246
#print axioms ztgcTrio_eq247
#print axioms ztgcTrio_eq248
#print axioms ztgcTrio_eq249
#print axioms ztgcTrio_eq250
#print axioms ztgcTrio_eq251
#print axioms ztgcTrio_eq252
#print axioms ztgcTrio_eq253
#print axioms ztgcTrio_eq254
#print axioms ztgcTrio_eq255
#print axioms ztgcTrio_eq256
#print axioms ztgcTrio_eq257
#print axioms ztgcTrio_eq258
#print axioms ztgcTrio_eq259
#print axioms ztgcTrio_eq260
#print axioms ztgcTrio_eq261
#print axioms ztgcTrio_eq262
#print axioms ztgcTrio_eq263
#print axioms ztgcTrio_eq264
#print axioms ztgcTrio_eq265
#print axioms ztgcTrio_eq266
#print axioms ztgcTrio_eq267
#print axioms ztgcTrio_eq268
#print axioms ztgcTrio_eq269
#print axioms ztgcTrio_eq270
#print axioms ztgcTrio_eq271
#print axioms ztgcTrio_eq272
#print axioms ztgcTrio_eq273
#print axioms ztgcTrio_eq274
#print axioms ztgcTrio_eq275
#print axioms ztgcTrio_eq276
#print axioms ztgcTrio_eq277
#print axioms ztgcTrio_eq278
#print axioms ztgcTrio_eq279
#print axioms ztgcTrio_eq280
#print axioms ztgcTrio_eq281
#print axioms ztgcTrio_eq282
#print axioms ztgcTrio_eq283
#print axioms ztgcTrio_eq284
#print axioms ztgcTrio_eq285
#print axioms ztgcTrio_eq286
#print axioms ztgcTrio_eq287
#print axioms ztgcTrio_eq288
#print axioms ztgcTrio_eq289
#print axioms ztgcTrio_eq290
#print axioms ztgcTrio_eq291
#print axioms ztgcTrio_eq292
#print axioms ztgcTrio_eq293
#print axioms ztgcTrio_eq294
#print axioms ztgcTrio_eq295
#print axioms ztgcTrio_eq296
#print axioms ztgcTrio_eq297
#print axioms ztgcTrio_eq298
#print axioms ztgcTrio_eq299
#print axioms ztgcTrio_eq300
#print axioms ztgcTrio_eq301
#print axioms ztgcTrio_eq302
#print axioms ztgcTrio_eq303
#print axioms ztgcTrio_eq304
#print axioms ztgcTrio_eq305
#print axioms ztgcTrio_eq306
#print axioms ztgcTrio_eq307
#print axioms ztgcTrio_eq308
#print axioms ztgcTrio_eq309
#print axioms ztgcTrio_eq310
#print axioms ztgcTrio_eq311
#print axioms ztgcTrio_eq312
#print axioms ztgcTrio_eq313
#print axioms ztgcTrio_eq314
#print axioms ztgcTrio_eq315
#print axioms ztgcTrio_eq316
#print axioms ztgcTrio_eq317
#print axioms ztgcTrio_eq318
#print axioms ztgcTrio_eq319
#print axioms ztgcTrio_eq320
#print axioms ztgcTrio_eq321
#print axioms ztgcTrio_eq322
#print axioms ztgcTrio_eq323
#print axioms ztgcTrio_eq324
#print axioms ztgcTrio_eq325
#print axioms ztgcTrio_eq326
#print axioms ztgcTrio_eq327
#print axioms ztgcTrio_eq328
#print axioms ztgcTrio_s0_1
#print axioms ztgcTrio_s0_2
#print axioms ztgcTrio_s0_3
#print axioms ztgcTrio_s0_4
#print axioms ztgcTrio_s1_1
#print axioms ztgcTrio_s1_2
#print axioms ztgcTrio_s1_3
#print axioms ztgcTrio_s1_4
#print axioms ztgcTrio_s2_1
#print axioms ztgcTrio_s2_2
#print axioms ztgcTrio_s2_3
#print axioms ztgcTrio_s2_4
#print axioms ztgcTrio_s3_1
#print axioms ztgcTrio_s3_2
#print axioms ztgcTrio_s3_3
#print axioms ztgcTrio_s3_4
#print axioms ztgcTrio_s4_1
#print axioms ztgcTrio_s4_2
#print axioms ztgcTrio_s4_3
#print axioms ztgcTrio_s4_4
#print axioms ztgcTrio_s5_1
#print axioms ztgcTrio_s5_2
#print axioms ztgcTrio_s5_3
#print axioms ztgcTrio_s5_4
#print axioms ztgcTrio_s6_1
#print axioms ztgcTrio_s6_2
#print axioms ztgcTrio_s6_3
#print axioms ztgcTrio_s6_4
#print axioms ztgcTrio_s7_1
#print axioms ztgcTrio_s7_2
#print axioms ztgcTrio_s7_3
#print axioms ztgcTrio_s7_4
#print axioms ztgcTrio_s8_1
#print axioms ztgcTrio_s8_2
#print axioms ztgcTrio_s8_3
#print axioms ztgcTrio_s8_4
#print axioms ztgcTrio_s9_1
#print axioms ztgcTrio_s9_2
#print axioms ztgcTrio_s9_3
#print axioms ztgcTrio_s9_4
#print axioms ztgcTrio_s10_1
#print axioms ztgcTrio_s10_2
#print axioms ztgcTrio_s10_3
#print axioms ztgcTrio_s10_4
#print axioms ztgcTrio_s11_1
#print axioms ztgcTrio_s11_2
#print axioms ztgcTrio_s11_3
#print axioms ztgcTrio_s11_4
#print axioms ztgcTrio_s12_1
#print axioms ztgcTrio_s12_2
#print axioms ztgcTrio_s12_3
#print axioms ztgcTrio_s12_4
#print axioms ztgcTrio_s13_1
#print axioms ztgcTrio_s13_2
#print axioms ztgcTrio_s13_3
#print axioms ztgcTrio_s13_4
#print axioms ztgcTrio_s14_1
#print axioms ztgcTrio_s14_2
#print axioms ztgcTrio_s14_3
#print axioms ztgcTrio_s14_4
#print axioms ztgcTrio_s15_1
#print axioms ztgcTrio_s15_2
#print axioms ztgcTrio_s15_3
#print axioms ztgcTrio_s15_4
#print axioms ztgcTrio_s16_1
#print axioms ztgcTrio_s16_2
#print axioms ztgcTrio_s16_3
#print axioms ztgcTrio_s16_4
#print axioms ztgcTrio_s17_1
#print axioms ztgcTrio_s17_2
#print axioms ztgcTrio_s17_3
#print axioms ztgcTrio_s17_4
#print axioms ztgcTrio_s18_1
#print axioms ztgcTrio_s18_2
#print axioms ztgcTrio_s18_3
#print axioms ztgcTrio_s18_4
#print axioms ztgcTrio_s19_1
#print axioms ztgcTrio_s19_2
#print axioms ztgcTrio_s19_3
#print axioms ztgcTrio_s19_4
#print axioms ztgcTrio_s20_1
#print axioms ztgcTrio_s20_2
#print axioms ztgcTrio_s20_3
#print axioms ztgcTrio_s20_4
#print axioms ztgcTrio_s21_1
#print axioms ztgcTrio_s21_2
#print axioms ztgcTrio_s21_3
#print axioms ztgcTrio_s21_4
#print axioms ztgcTrio_s22_1
#print axioms ztgcTrio_s22_2
#print axioms ztgcTrio_s22_3
#print axioms ztgcTrio_s22_4
#print axioms ztgcTrio_s23_1
#print axioms ztgcTrio_s23_2
#print axioms ztgcTrio_s23_3
#print axioms ztgcTrio_s23_4
#print axioms ztgcTrio_s24_1
#print axioms ztgcTrio_s24_2
#print axioms ztgcTrio_s24_3
#print axioms ztgcTrio_s24_4
#print axioms ztgcTrio_s25_1
#print axioms ztgcTrio_s25_2
#print axioms ztgcTrio_s25_3
#print axioms ztgcTrio_s25_4
#print axioms ztgcTrio_s26_1
#print axioms ztgcTrio_s26_2
#print axioms ztgcTrio_s26_3
#print axioms ztgcTrio_s26_4
#print axioms ztgcTrio_s27_1
#print axioms ztgcTrio_s27_2
#print axioms ztgcTrio_s27_3
#print axioms ztgcTrio_s27_4
#print axioms ztgcTrio_s28_1
#print axioms ztgcTrio_s28_2
#print axioms ztgcTrio_s28_3
#print axioms ztgcTrio_s28_4
#print axioms ztgcTrio_s29_1
#print axioms ztgcTrio_s29_2
#print axioms ztgcTrio_s29_3
#print axioms ztgcTrio_s29_4
#print axioms ztgcTrio_s30_1
#print axioms ztgcTrio_s30_2
#print axioms ztgcTrio_s30_3
#print axioms ztgcTrio_s30_4
#print axioms ztgcTrio_s31_1
#print axioms ztgcTrio_s31_2
#print axioms ztgcTrio_s31_3
#print axioms ztgcTrio_s31_4
#print axioms ztgcTrio_s32_1
#print axioms ztgcTrio_s32_2
#print axioms ztgcTrio_s32_3
#print axioms ztgcTrio_s32_4
#print axioms ztgcTrio_s33_1
#print axioms ztgcTrio_s33_2
#print axioms ztgcTrio_s33_3
#print axioms ztgcTrio_s33_4
#print axioms ztgcTrio_s34_1
#print axioms ztgcTrio_s34_2
#print axioms ztgcTrio_s34_3
#print axioms ztgcTrio_s34_4
#print axioms ztgcTrio_s35_1
#print axioms ztgcTrio_s35_2
#print axioms ztgcTrio_s35_3
#print axioms ztgcTrio_s35_4

end Kepler.Text
