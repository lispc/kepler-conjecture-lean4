/-
Ox3q1hChainBatch5: S3 mass-production batch 5 (32 conjuncts, idx 141-179, boxes 6-41).
Routes per CONCAVITY_CENSUS (CORNER / Y4PATCH) emit the same unsplit
two-corner chain shape; KENV per-coordinate K and exact rebates R
close each chain at `B_i - sum R_i <= f x` (landed ChainBatch2 paradigm,
rebate direction). REBATE rows carry the RNv_def norm_num bridge, which
doubles as the per-row data-consistency check R_i = K_i*W_i^2/8.

All numeric literals are generated verbatim from
corner184/{KENV,CONJ_TABLE,BOXES_EXACT}.tsv by scripts/emit_chain.py;
no value is hand-written. No new sorry/axiom/native_decide.
-/
import Mathlib
import Kepler.Text.Ox3q1hChainBatch4

open Set Filter Topology

namespace Kepler.Text

/-- Box 35 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b35lo : Fin 6 → ℝ := ![(50727/20000), 2, 2, (26181/10000), 2, 2]

/-- Box 35 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b35hi : Fin 6 → ℝ := ![(25527/10000), (15397/6250), (15397/6250), (6627/2500), (15397/6250), (15397/6250)]

theorem b35lo_le_b35hi (i : Fin 6) : b35lo i ≤ b35hi i := by
  fin_cases i
  all_goals norm_num [b35lo, b35hi]

/-- Box 36 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b36lo : Fin 6 → ℝ := ![(50727/20000), 2, 2, 2, 2, 2]

/-- Box 36 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b36hi : Fin 6 → ℝ := ![(25527/10000), (15397/6250), (15397/6250), (102897/50000), (15397/6250), (15397/6250)]

theorem b36lo_le_b36hi (i : Fin 6) : b36lo i ≤ b36hi i := by
  fin_cases i
  all_goals norm_num [b36lo, b36hi]

/-- Box 37 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b37lo : Fin 6 → ℝ := ![(63/25), 2, 2, (26181/10000), 2, 2]

/-- Box 37 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b37hi : Fin 6 → ℝ := ![(50727/20000), (15397/6250), (15397/6250), (6627/2500), (15397/6250), (15397/6250)]

theorem b37lo_le_b37hi (i : Fin 6) : b37lo i ≤ b37hi i := by
  fin_cases i
  all_goals norm_num [b37lo, b37hi]

/-- Box 38 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b38lo : Fin 6 → ℝ := ![(63/25), 2, 2, 2, 2, 2]

/-- Box 38 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b38hi : Fin 6 → ℝ := ![(50727/20000), (15397/6250), (15397/6250), (102897/50000), (15397/6250), (15397/6250)]

theorem b38lo_le_b38hi (i : Fin 6) : b38lo i ≤ b38hi i := by
  fin_cases i
  all_goals norm_num [b38lo, b38hi]

/-- Box 39 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b39lo : Fin 6 → ℝ := ![(63/25), 2, 2, (12927/5000), 2, 2]

/-- Box 39 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b39hi : Fin 6 → ℝ := ![(25527/10000), (15397/6250), (15397/6250), (26181/10000), (15397/6250), (15397/6250)]

theorem b39lo_le_b39hi (i : Fin 6) : b39lo i ≤ b39hi i := by
  fin_cases i
  all_goals norm_num [b39lo, b39hi]

/-- Box 40 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b40lo : Fin 6 → ℝ := ![(63/25), 2, 2, (63/25), 2, 2]

/-- Box 40 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b40hi : Fin 6 → ℝ := ![(12927/5000), (15397/6250), (15397/6250), (12927/5000), (15397/6250), (15397/6250)]

theorem b40lo_le_b40hi (i : Fin 6) : b40lo i ≤ b40hi i := by
  fin_cases i
  all_goals norm_num [b40lo, b40hi]

/-- Box 41 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b41lo : Fin 6 → ℝ := ![(63/25), 2, 2, (4927/2000), 2, 2]

/-- Box 41 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b41hi : Fin 6 → ℝ := ![(6627/2500), (15397/6250), (15397/6250), (63/25), (15397/6250), (15397/6250)]

theorem b41lo_le_b41hi (i : Fin 6) : b41lo i ≤ b41hi i := by
  fin_cases i
  all_goals norm_num [b41lo, b41hi]


/-- idx 141 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K141 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (597292424679/1099511627776), (0/1), (0/1)]

/-- idx 141 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B141 : ℝ := (8368001249050912669019/7205759403792793600000000)

/-- idx 141 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R141 : Fin 6 → ℝ := ![0, 0, 0, (63867881678500791/219902325555200000000), 0, 0]

/-- idx 142 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K142 : Fin 6 → ℝ := fun _ => 0

/-- idx 142 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B142 : ℝ := (33463658327056294170159/28823037615171174400000000)

/-- idx 142 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R142 : Fin 6 → ℝ :=
  fun j => K142 j * (b33hi j - b33lo j) ^ 2 / 8

/-- idx 143 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K143 : Fin 6 → ℝ := fun _ => 0

/-- idx 143 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B143 : ℝ := (836140091848463825143807/720575940379279360000000000)

/-- idx 143 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R143 : Fin 6 → ℝ :=
  fun j => K143 j * (b34hi j - b34lo j) ^ 2 / 8

/-- idx 144 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K144 : Fin 6 → ℝ := fun _ => 0

/-- idx 144 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B144 : ℝ := (16717215835007905123773/14411518807585587200000000)

/-- idx 144 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R144 : Fin 6 → ℝ :=
  fun j => K144 j * (b34hi j - b34lo j) ^ 2 / 8

/-- idx 146 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K146 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (145499252149/274877906944), (0/1), (0/1)]

/-- idx 146 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B146 : ℝ := (44924689928774775587397/144115188075855872000000000)

/-- idx 146 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R146 : Fin 6 → ℝ := ![0, 0, 0, (15558089533040421/219902325555200000000), 0, 0]

/-- idx 147 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K147 : Fin 6 → ℝ := fun _ => 0

/-- idx 147 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B147 : ℝ := (13597274230923500954187/45035996273704960000000000)

/-- idx 147 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R147 : Fin 6 → ℝ :=
  fun j => K147 j * (b36hi j - b36lo j) ^ 2 / 8

/-- idx 148 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K148 : Fin 6 → ℝ := fun _ => 0

/-- idx 148 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B148 : ℝ := (111900521944593733199293/360287970189639680000000000)

/-- idx 148 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R148 : Fin 6 → ℝ :=
  fun j => K148 j * (b36hi j - b36lo j) ^ 2 / 8

/-- idx 149 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K149 : Fin 6 → ℝ := fun _ => 0

/-- idx 149 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B149 : ℝ := (13597274230923500954187/45035996273704960000000000)

/-- idx 149 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R149 : Fin 6 → ℝ :=
  fun j => K149 j * (b36hi j - b36lo j) ^ 2 / 8

/-- idx 151 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K151 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (566315993789/1099511627776), (0/1), (0/1)]

/-- idx 151 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B151 : ℝ := (6018825145969899828821/14411518807585587200000000)

/-- idx 151 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R151 : Fin 6 → ℝ := ![0, 0, 0, (60555602899863981/879609302220800000000), 0, 0]

/-- idx 152 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K152 : Fin 6 → ℝ := fun _ => 0

/-- idx 152 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B152 : ℝ := (9345042883342261834513/22517998136852480000000000)

/-- idx 152 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R152 : Fin 6 → ℝ :=
  fun j => K152 j * (b38hi j - b38lo j) ^ 2 / 8

/-- idx 153 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K153 : Fin 6 → ℝ := fun _ => 0

/-- idx 153 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B153 : ℝ := (150056327510774085708757/360287970189639680000000000)

/-- idx 153 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R153 : Fin 6 → ℝ :=
  fun j => K153 j * (b38hi j - b38lo j) ^ 2 / 8

/-- idx 154 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K154 : Fin 6 → ℝ := fun _ => 0

/-- idx 154 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B154 : ℝ := (9345042883342261834513/22517998136852480000000000)

/-- idx 154 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R154 : Fin 6 → ℝ :=
  fun j => K154 j * (b38hi j - b38lo j) ^ 2 / 8

/-- idx 156 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K156 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (574542099917/1099511627776), (0/1), (0/1)]

/-- idx 156 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B156 : ℝ := (1858386252607482077749/2882303761517117440000000)

/-- idx 156 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R156 : Fin 6 → ℝ := ![0, 0, 0, (61435212202024893/879609302220800000000), 0, 0]

/-- idx 157 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K157 : Fin 6 → ℝ := fun _ => 0

/-- idx 157 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B157 : ℝ := (2316670520307222761309/3602879701896396800000000)

/-- idx 157 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R157 : Fin 6 → ℝ :=
  fun j => K157 j * (b34hi j - b34lo j) ^ 2 / 8

/-- idx 158 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K158 : Fin 6 → ℝ := fun _ => 0

/-- idx 158 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B158 : ℝ := (46306031555053243689003/72057594037927936000000000)

/-- idx 158 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R158 : Fin 6 → ℝ :=
  fun j => K158 j * (b34hi j - b34lo j) ^ 2 / 8

/-- idx 159 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K159 : Fin 6 → ℝ := fun _ => 0

/-- idx 159 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B159 : ℝ := (2316670520307222761309/3602879701896396800000000)

/-- idx 159 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R159 : Fin 6 → ℝ :=
  fun j => K159 j * (b34hi j - b34lo j) ^ 2 / 8

/-- idx 161 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K161 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (610081449051/1099511627776), (0/1), (0/1)]

/-- idx 161 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B161 : ℝ := (22395744817333092846543/72057594037927936000000000)

/-- idx 161 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R161 : Fin 6 → ℝ := ![0, 0, 0, (65235399265574379/219902325555200000000), 0, 0]

/-- idx 162 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K162 : Fin 6 → ℝ := fun _ => 0

/-- idx 162 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B162 : ℝ := (1109777245112725649005449/3602879701896396800000000000)

/-- idx 162 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R162 : Fin 6 → ℝ :=
  fun j => K162 j * (b28hi j - b28lo j) ^ 2 / 8

/-- idx 163 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K163 : Fin 6 → ℝ := fun _ => 0

/-- idx 163 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B163 : ℝ := (1109777245112725649005449/3602879701896396800000000000)

/-- idx 163 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R163 : Fin 6 → ℝ :=
  fun j => K163 j * (b28hi j - b28lo j) ^ 2 / 8

/-- idx 164 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K164 : Fin 6 → ℝ := fun _ => 0

/-- idx 164 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B164 : ℝ := (225698054889908608616367/720575940379279360000000000)

/-- idx 164 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R164 : Fin 6 → ℝ :=
  fun j => K164 j * (b28hi j - b28lo j) ^ 2 / 8

/-- idx 166 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K166 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (306285759261/549755813888), (0/1), (0/1)]

/-- idx 166 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B166 : ℝ := (78283134124333786320869/28823037615171174400000000)

/-- idx 166 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R166 : Fin 6 → ℝ := ![0, 0, 0, (3910962860003709/17592186044416000000), 0, 0]

/-- idx 167 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K167 : Fin 6 → ℝ := fun _ => 0

/-- idx 167 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B167 : ℝ := (3924208341292139308301/1441151880758558720000000)

/-- idx 167 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R167 : Fin 6 → ℝ :=
  fun j => K167 j * (b6hi j - b6lo j) ^ 2 / 8

/-- idx 168 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K168 : Fin 6 → ℝ := fun _ => 0

/-- idx 168 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B168 : ℝ := (489545085008139688213137/180143985094819840000000000)

/-- idx 168 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R168 : Fin 6 → ℝ :=
  fun j => K168 j * (b6hi j - b6lo j) ^ 2 / 8

/-- idx 169 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K169 : Fin 6 → ℝ := fun _ => 0

/-- idx 169 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B169 : ℝ := (98043888100283974166987/36028797018963968000000000)

/-- idx 169 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R169 : Fin 6 → ℝ :=
  fun j => K169 j * (b7hi j - b7lo j) ^ 2 / 8

/-- idx 171 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K171 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (306285759261/549755813888), (0/1), (0/1)]

/-- idx 171 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B171 : ℝ := (78398426274794471018469/28823037615171174400000000)

/-- idx 171 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R171 : Fin 6 → ℝ := ![0, 0, 0, (3910962860003709/17592186044416000000), 0, 0]

/-- idx 172 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K172 : Fin 6 → ℝ := fun _ => 0

/-- idx 172 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B172 : ℝ := (3918443733769105073421/1441151880758558720000000)

/-- idx 172 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R172 : Fin 6 → ℝ :=
  fun j => K172 j * (b6hi j - b6lo j) ^ 2 / 8

/-- idx 173 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K173 : Fin 6 → ℝ := fun _ => 0

/-- idx 173 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B173 : ℝ := (98043888100283974166987/36028797018963968000000000)

/-- idx 173 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R173 : Fin 6 → ℝ :=
  fun j => K173 j * (b7hi j - b7lo j) ^ 2 / 8

/-- idx 174 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K174 : Fin 6 → ℝ := fun _ => 0

/-- idx 174 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B174 : ℝ := (489545085008139688213137/180143985094819840000000000)

/-- idx 174 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R174 : Fin 6 → ℝ :=
  fun j => K174 j * (b8hi j - b8lo j) ^ 2 / 8

/-- idx 176 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K176 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (306285759261/549755813888), (0/1), (0/1)]

/-- idx 176 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B176 : ℝ := (78369603237179299844069/28823037615171174400000000)

/-- idx 176 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R176 : Fin 6 → ℝ := ![0, 0, 0, (3910962860003709/17592186044416000000), 0, 0]

/-- idx 177 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K177 : Fin 6 → ℝ := fun _ => 0

/-- idx 177 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B177 : ℝ := (97935801709227082262987/36028797018963968000000000)

/-- idx 177 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R177 : Fin 6 → ℝ :=
  fun j => K177 j * (b7hi j - b7lo j) ^ 2 / 8

/-- idx 178 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K178 : Fin 6 → ℝ := fun _ => 0

/-- idx 178 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B178 : ℝ := (3924208341292139308301/1441151880758558720000000)

/-- idx 178 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R178 : Fin 6 → ℝ :=
  fun j => K178 j * (b8hi j - b8lo j) ^ 2 / 8

/-- idx 179 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K179 : Fin 6 → ℝ := fun _ => 0

/-- idx 179 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B179 : ℝ := (489545085008139688213137/180143985094819840000000000)

/-- idx 179 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R179 : Fin 6 → ℝ :=
  fun j => K179 j * (b8hi j - b8lo j) ^ 2 / 8


/-- The unsplit two-corner grid of box 35. -/
noncomputable def candsb35 : Fin 6 → Finset ℝ :=
  fun i => insert (b35lo i) {b35hi i}

theorem candsb35_eq (i : Fin 6) : candsb35 i = insert (b35lo i) {b35hi i} := rfl

theorem candsb35_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb35 i) :
    c ∈ Set.Icc (b35lo i) (b35hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b35lo_le_b35hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b35lo_le_b35hi i, le_rfl⟩

theorem candsb35_ne (i : Fin 6) : (candsb35 i).Nonempty := ⟨b35lo i, by
  simp only [candsb35]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 36. -/
noncomputable def candsb36 : Fin 6 → Finset ℝ :=
  fun i => insert (b36lo i) {b36hi i}

theorem candsb36_eq (i : Fin 6) : candsb36 i = insert (b36lo i) {b36hi i} := rfl

theorem candsb36_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb36 i) :
    c ∈ Set.Icc (b36lo i) (b36hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b36lo_le_b36hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b36lo_le_b36hi i, le_rfl⟩

theorem candsb36_ne (i : Fin 6) : (candsb36 i).Nonempty := ⟨b36lo i, by
  simp only [candsb36]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 37. -/
noncomputable def candsb37 : Fin 6 → Finset ℝ :=
  fun i => insert (b37lo i) {b37hi i}

theorem candsb37_eq (i : Fin 6) : candsb37 i = insert (b37lo i) {b37hi i} := rfl

theorem candsb37_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb37 i) :
    c ∈ Set.Icc (b37lo i) (b37hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b37lo_le_b37hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b37lo_le_b37hi i, le_rfl⟩

theorem candsb37_ne (i : Fin 6) : (candsb37 i).Nonempty := ⟨b37lo i, by
  simp only [candsb37]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 38. -/
noncomputable def candsb38 : Fin 6 → Finset ℝ :=
  fun i => insert (b38lo i) {b38hi i}

theorem candsb38_eq (i : Fin 6) : candsb38 i = insert (b38lo i) {b38hi i} := rfl

theorem candsb38_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb38 i) :
    c ∈ Set.Icc (b38lo i) (b38hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b38lo_le_b38hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b38lo_le_b38hi i, le_rfl⟩

theorem candsb38_ne (i : Fin 6) : (candsb38 i).Nonempty := ⟨b38lo i, by
  simp only [candsb38]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 39. -/
noncomputable def candsb39 : Fin 6 → Finset ℝ :=
  fun i => insert (b39lo i) {b39hi i}

theorem candsb39_eq (i : Fin 6) : candsb39 i = insert (b39lo i) {b39hi i} := rfl

theorem candsb39_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb39 i) :
    c ∈ Set.Icc (b39lo i) (b39hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b39lo_le_b39hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b39lo_le_b39hi i, le_rfl⟩

theorem candsb39_ne (i : Fin 6) : (candsb39 i).Nonempty := ⟨b39lo i, by
  simp only [candsb39]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 40. -/
noncomputable def candsb40 : Fin 6 → Finset ℝ :=
  fun i => insert (b40lo i) {b40hi i}

theorem candsb40_eq (i : Fin 6) : candsb40 i = insert (b40lo i) {b40hi i} := rfl

theorem candsb40_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb40 i) :
    c ∈ Set.Icc (b40lo i) (b40hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b40lo_le_b40hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b40lo_le_b40hi i, le_rfl⟩

theorem candsb40_ne (i : Fin 6) : (candsb40 i).Nonempty := ⟨b40lo i, by
  simp only [candsb40]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 41. -/
noncomputable def candsb41 : Fin 6 → Finset ℝ :=
  fun i => insert (b41lo i) {b41hi i}

theorem candsb41_eq (i : Fin 6) : candsb41 i = insert (b41lo i) {b41hi i} := rfl

theorem candsb41_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb41 i) :
    c ∈ Set.Icc (b41lo i) (b41hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b41lo_le_b41hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b41lo_le_b41hi i, le_rfl⟩

theorem candsb41_ne (i : Fin 6) : (candsb41 i).Nonempty := ⟨b41lo i, by
  simp only [candsb41]
  exact Finset.mem_insert_self _ _⟩


/-- idx 141 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R141v_def (i : Fin 6) : R141 i = K141 i * (b31hi i - b31lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R141, K141, b31lo, b31hi]

/-- idx 141 chain: corner bound minus the grid rebate lower-bounds the margin (box 31; REBATE coordinates per KENV). -/

theorem chain_idx141 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b31lo i) (b31hi i))
        (fun t => f (Function.update y i t) - K141 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K141 i)
    (hR0 : ∀ i, 0 ≤ R141 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb31 j) → B141 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b31lo j) (b31hi j)) :
    B141 - ∑ j, R141 j ≤ f x :=
  final_bound candsb31 candsb31_ne hR0 candsb31_sub
    (fun i y hy => by
      rw [R141v_def i]
      exact hstep_of_shifted_concave (b31lo_le_b31hi i) (hK0 i)
        (hsl i) candsb31_eq y hy)
    hcorner x hx

/-- idx 142 chain: corner bound minus the grid rebate lower-bounds the margin (box 33; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx142 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b33lo i) (b33hi i))
        (fun t => f (Function.update y i t) - K142 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K142 i)
    (hR0 : ∀ i, 0 ≤ R142 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb33 j) → B142 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b33lo j) (b33hi j)) :
    B142 - ∑ j, R142 j ≤ f x :=
  final_bound candsb33 candsb33_ne hR0 candsb33_sub
    (fun i y hy => hstep_of_shifted_concave (b33lo_le_b33hi i) (hK0 i)
      (hsl i) candsb33_eq y hy)
    hcorner x hx

/-- idx 143 chain: corner bound minus the grid rebate lower-bounds the margin (box 34; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx143 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => f (Function.update y i t) - K143 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K143 i)
    (hR0 : ∀ i, 0 ≤ R143 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B143 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b34lo j) (b34hi j)) :
    B143 - ∑ j, R143 j ≤ f x :=
  final_bound candsb34 candsb34_ne hR0 candsb34_sub
    (fun i y hy => hstep_of_shifted_concave (b34lo_le_b34hi i) (hK0 i)
      (hsl i) candsb34_eq y hy)
    hcorner x hx

/-- idx 144 chain: corner bound minus the grid rebate lower-bounds the margin (box 34; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx144 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => f (Function.update y i t) - K144 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K144 i)
    (hR0 : ∀ i, 0 ≤ R144 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B144 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b34lo j) (b34hi j)) :
    B144 - ∑ j, R144 j ≤ f x :=
  final_bound candsb34 candsb34_ne hR0 candsb34_sub
    (fun i y hy => hstep_of_shifted_concave (b34lo_le_b34hi i) (hK0 i)
      (hsl i) candsb34_eq y hy)
    hcorner x hx

/-- idx 146 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R146v_def (i : Fin 6) : R146 i = K146 i * (b35hi i - b35lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R146, K146, b35lo, b35hi]

/-- idx 146 chain: corner bound minus the grid rebate lower-bounds the margin (box 35; REBATE coordinates per KENV). -/

theorem chain_idx146 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b35lo i) (b35hi i))
        (fun t => f (Function.update y i t) - K146 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K146 i)
    (hR0 : ∀ i, 0 ≤ R146 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb35 j) → B146 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b35lo j) (b35hi j)) :
    B146 - ∑ j, R146 j ≤ f x :=
  final_bound candsb35 candsb35_ne hR0 candsb35_sub
    (fun i y hy => by
      rw [R146v_def i]
      exact hstep_of_shifted_concave (b35lo_le_b35hi i) (hK0 i)
        (hsl i) candsb35_eq y hy)
    hcorner x hx

/-- idx 147 chain: corner bound minus the grid rebate lower-bounds the margin (box 36; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx147 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b36lo i) (b36hi i))
        (fun t => f (Function.update y i t) - K147 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K147 i)
    (hR0 : ∀ i, 0 ≤ R147 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb36 j) → B147 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b36lo j) (b36hi j)) :
    B147 - ∑ j, R147 j ≤ f x :=
  final_bound candsb36 candsb36_ne hR0 candsb36_sub
    (fun i y hy => hstep_of_shifted_concave (b36lo_le_b36hi i) (hK0 i)
      (hsl i) candsb36_eq y hy)
    hcorner x hx

/-- idx 148 chain: corner bound minus the grid rebate lower-bounds the margin (box 36; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx148 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b36lo i) (b36hi i))
        (fun t => f (Function.update y i t) - K148 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K148 i)
    (hR0 : ∀ i, 0 ≤ R148 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb36 j) → B148 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b36lo j) (b36hi j)) :
    B148 - ∑ j, R148 j ≤ f x :=
  final_bound candsb36 candsb36_ne hR0 candsb36_sub
    (fun i y hy => hstep_of_shifted_concave (b36lo_le_b36hi i) (hK0 i)
      (hsl i) candsb36_eq y hy)
    hcorner x hx

/-- idx 149 chain: corner bound minus the grid rebate lower-bounds the margin (box 36; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx149 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b36lo i) (b36hi i))
        (fun t => f (Function.update y i t) - K149 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K149 i)
    (hR0 : ∀ i, 0 ≤ R149 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb36 j) → B149 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b36lo j) (b36hi j)) :
    B149 - ∑ j, R149 j ≤ f x :=
  final_bound candsb36 candsb36_ne hR0 candsb36_sub
    (fun i y hy => hstep_of_shifted_concave (b36lo_le_b36hi i) (hK0 i)
      (hsl i) candsb36_eq y hy)
    hcorner x hx

/-- idx 151 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R151v_def (i : Fin 6) : R151 i = K151 i * (b37hi i - b37lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R151, K151, b37lo, b37hi]

/-- idx 151 chain: corner bound minus the grid rebate lower-bounds the margin (box 37; REBATE coordinates per KENV). -/

theorem chain_idx151 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b37lo i) (b37hi i))
        (fun t => f (Function.update y i t) - K151 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K151 i)
    (hR0 : ∀ i, 0 ≤ R151 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb37 j) → B151 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b37lo j) (b37hi j)) :
    B151 - ∑ j, R151 j ≤ f x :=
  final_bound candsb37 candsb37_ne hR0 candsb37_sub
    (fun i y hy => by
      rw [R151v_def i]
      exact hstep_of_shifted_concave (b37lo_le_b37hi i) (hK0 i)
        (hsl i) candsb37_eq y hy)
    hcorner x hx

/-- idx 152 chain: corner bound minus the grid rebate lower-bounds the margin (box 38; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx152 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b38lo i) (b38hi i))
        (fun t => f (Function.update y i t) - K152 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K152 i)
    (hR0 : ∀ i, 0 ≤ R152 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb38 j) → B152 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b38lo j) (b38hi j)) :
    B152 - ∑ j, R152 j ≤ f x :=
  final_bound candsb38 candsb38_ne hR0 candsb38_sub
    (fun i y hy => hstep_of_shifted_concave (b38lo_le_b38hi i) (hK0 i)
      (hsl i) candsb38_eq y hy)
    hcorner x hx

/-- idx 153 chain: corner bound minus the grid rebate lower-bounds the margin (box 38; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx153 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b38lo i) (b38hi i))
        (fun t => f (Function.update y i t) - K153 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K153 i)
    (hR0 : ∀ i, 0 ≤ R153 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb38 j) → B153 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b38lo j) (b38hi j)) :
    B153 - ∑ j, R153 j ≤ f x :=
  final_bound candsb38 candsb38_ne hR0 candsb38_sub
    (fun i y hy => hstep_of_shifted_concave (b38lo_le_b38hi i) (hK0 i)
      (hsl i) candsb38_eq y hy)
    hcorner x hx

/-- idx 154 chain: corner bound minus the grid rebate lower-bounds the margin (box 38; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx154 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b38lo i) (b38hi i))
        (fun t => f (Function.update y i t) - K154 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K154 i)
    (hR0 : ∀ i, 0 ≤ R154 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb38 j) → B154 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b38lo j) (b38hi j)) :
    B154 - ∑ j, R154 j ≤ f x :=
  final_bound candsb38 candsb38_ne hR0 candsb38_sub
    (fun i y hy => hstep_of_shifted_concave (b38lo_le_b38hi i) (hK0 i)
      (hsl i) candsb38_eq y hy)
    hcorner x hx

/-- idx 156 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R156v_def (i : Fin 6) : R156 i = K156 i * (b39hi i - b39lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R156, K156, b39lo, b39hi]

/-- idx 156 chain: corner bound minus the grid rebate lower-bounds the margin (box 39; REBATE coordinates per KENV). -/

theorem chain_idx156 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b39lo i) (b39hi i))
        (fun t => f (Function.update y i t) - K156 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K156 i)
    (hR0 : ∀ i, 0 ≤ R156 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb39 j) → B156 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b39lo j) (b39hi j)) :
    B156 - ∑ j, R156 j ≤ f x :=
  final_bound candsb39 candsb39_ne hR0 candsb39_sub
    (fun i y hy => by
      rw [R156v_def i]
      exact hstep_of_shifted_concave (b39lo_le_b39hi i) (hK0 i)
        (hsl i) candsb39_eq y hy)
    hcorner x hx

/-- idx 157 chain: corner bound minus the grid rebate lower-bounds the margin (box 34; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx157 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => f (Function.update y i t) - K157 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K157 i)
    (hR0 : ∀ i, 0 ≤ R157 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B157 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b34lo j) (b34hi j)) :
    B157 - ∑ j, R157 j ≤ f x :=
  final_bound candsb34 candsb34_ne hR0 candsb34_sub
    (fun i y hy => hstep_of_shifted_concave (b34lo_le_b34hi i) (hK0 i)
      (hsl i) candsb34_eq y hy)
    hcorner x hx

/-- idx 158 chain: corner bound minus the grid rebate lower-bounds the margin (box 34; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx158 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => f (Function.update y i t) - K158 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K158 i)
    (hR0 : ∀ i, 0 ≤ R158 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B158 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b34lo j) (b34hi j)) :
    B158 - ∑ j, R158 j ≤ f x :=
  final_bound candsb34 candsb34_ne hR0 candsb34_sub
    (fun i y hy => hstep_of_shifted_concave (b34lo_le_b34hi i) (hK0 i)
      (hsl i) candsb34_eq y hy)
    hcorner x hx

/-- idx 159 chain: corner bound minus the grid rebate lower-bounds the margin (box 34; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx159 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => f (Function.update y i t) - K159 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K159 i)
    (hR0 : ∀ i, 0 ≤ R159 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B159 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b34lo j) (b34hi j)) :
    B159 - ∑ j, R159 j ≤ f x :=
  final_bound candsb34 candsb34_ne hR0 candsb34_sub
    (fun i y hy => hstep_of_shifted_concave (b34lo_le_b34hi i) (hK0 i)
      (hsl i) candsb34_eq y hy)
    hcorner x hx

/-- idx 161 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R161v_def (i : Fin 6) : R161 i = K161 i * (b40hi i - b40lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R161, K161, b40lo, b40hi]

/-- idx 161 chain: corner bound minus the grid rebate lower-bounds the margin (box 40; REBATE coordinates per KENV). -/

theorem chain_idx161 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b40lo i) (b40hi i))
        (fun t => f (Function.update y i t) - K161 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K161 i)
    (hR0 : ∀ i, 0 ≤ R161 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb40 j) → B161 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b40lo j) (b40hi j)) :
    B161 - ∑ j, R161 j ≤ f x :=
  final_bound candsb40 candsb40_ne hR0 candsb40_sub
    (fun i y hy => by
      rw [R161v_def i]
      exact hstep_of_shifted_concave (b40lo_le_b40hi i) (hK0 i)
        (hsl i) candsb40_eq y hy)
    hcorner x hx

/-- idx 162 chain: corner bound minus the grid rebate lower-bounds the margin (box 28; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx162 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => f (Function.update y i t) - K162 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K162 i)
    (hR0 : ∀ i, 0 ≤ R162 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B162 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b28lo j) (b28hi j)) :
    B162 - ∑ j, R162 j ≤ f x :=
  final_bound candsb28 candsb28_ne hR0 candsb28_sub
    (fun i y hy => hstep_of_shifted_concave (b28lo_le_b28hi i) (hK0 i)
      (hsl i) candsb28_eq y hy)
    hcorner x hx

/-- idx 163 chain: corner bound minus the grid rebate lower-bounds the margin (box 28; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx163 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => f (Function.update y i t) - K163 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K163 i)
    (hR0 : ∀ i, 0 ≤ R163 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B163 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b28lo j) (b28hi j)) :
    B163 - ∑ j, R163 j ≤ f x :=
  final_bound candsb28 candsb28_ne hR0 candsb28_sub
    (fun i y hy => hstep_of_shifted_concave (b28lo_le_b28hi i) (hK0 i)
      (hsl i) candsb28_eq y hy)
    hcorner x hx

/-- idx 164 chain: corner bound minus the grid rebate lower-bounds the margin (box 28; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx164 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => f (Function.update y i t) - K164 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K164 i)
    (hR0 : ∀ i, 0 ≤ R164 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B164 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b28lo j) (b28hi j)) :
    B164 - ∑ j, R164 j ≤ f x :=
  final_bound candsb28 candsb28_ne hR0 candsb28_sub
    (fun i y hy => hstep_of_shifted_concave (b28lo_le_b28hi i) (hK0 i)
      (hsl i) candsb28_eq y hy)
    hcorner x hx

/-- idx 166 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R166v_def (i : Fin 6) : R166 i = K166 i * (b41hi i - b41lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R166, K166, b41lo, b41hi]

/-- idx 166 chain: corner bound minus the grid rebate lower-bounds the margin (box 41; REBATE coordinates per KENV). -/

theorem chain_idx166 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b41lo i) (b41hi i))
        (fun t => f (Function.update y i t) - K166 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K166 i)
    (hR0 : ∀ i, 0 ≤ R166 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb41 j) → B166 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b41lo j) (b41hi j)) :
    B166 - ∑ j, R166 j ≤ f x :=
  final_bound candsb41 candsb41_ne hR0 candsb41_sub
    (fun i y hy => by
      rw [R166v_def i]
      exact hstep_of_shifted_concave (b41lo_le_b41hi i) (hK0 i)
        (hsl i) candsb41_eq y hy)
    hcorner x hx

/-- idx 167 chain: corner bound minus the grid rebate lower-bounds the margin (box 6; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx167 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => f (Function.update y i t) - K167 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K167 i)
    (hR0 : ∀ i, 0 ≤ R167 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B167 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b6lo j) (b6hi j)) :
    B167 - ∑ j, R167 j ≤ f x :=
  final_bound candsb6 candsb6_ne hR0 candsb6_sub
    (fun i y hy => hstep_of_shifted_concave (b6lo_le_b6hi i) (hK0 i)
      (hsl i) candsb6_eq y hy)
    hcorner x hx

/-- idx 168 chain: corner bound minus the grid rebate lower-bounds the margin (box 6; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx168 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => f (Function.update y i t) - K168 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K168 i)
    (hR0 : ∀ i, 0 ≤ R168 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B168 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b6lo j) (b6hi j)) :
    B168 - ∑ j, R168 j ≤ f x :=
  final_bound candsb6 candsb6_ne hR0 candsb6_sub
    (fun i y hy => hstep_of_shifted_concave (b6lo_le_b6hi i) (hK0 i)
      (hsl i) candsb6_eq y hy)
    hcorner x hx

/-- idx 169 chain: corner bound minus the grid rebate lower-bounds the margin (box 7; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx169 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => f (Function.update y i t) - K169 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K169 i)
    (hR0 : ∀ i, 0 ≤ R169 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B169 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b7lo j) (b7hi j)) :
    B169 - ∑ j, R169 j ≤ f x :=
  final_bound candsb7 candsb7_ne hR0 candsb7_sub
    (fun i y hy => hstep_of_shifted_concave (b7lo_le_b7hi i) (hK0 i)
      (hsl i) candsb7_eq y hy)
    hcorner x hx

/-- idx 171 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R171v_def (i : Fin 6) : R171 i = K171 i * (b41hi i - b41lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R171, K171, b41lo, b41hi]

/-- idx 171 chain: corner bound minus the grid rebate lower-bounds the margin (box 41; REBATE coordinates per KENV). -/

theorem chain_idx171 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b41lo i) (b41hi i))
        (fun t => f (Function.update y i t) - K171 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K171 i)
    (hR0 : ∀ i, 0 ≤ R171 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb41 j) → B171 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b41lo j) (b41hi j)) :
    B171 - ∑ j, R171 j ≤ f x :=
  final_bound candsb41 candsb41_ne hR0 candsb41_sub
    (fun i y hy => by
      rw [R171v_def i]
      exact hstep_of_shifted_concave (b41lo_le_b41hi i) (hK0 i)
        (hsl i) candsb41_eq y hy)
    hcorner x hx

/-- idx 172 chain: corner bound minus the grid rebate lower-bounds the margin (box 6; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx172 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => f (Function.update y i t) - K172 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K172 i)
    (hR0 : ∀ i, 0 ≤ R172 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B172 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b6lo j) (b6hi j)) :
    B172 - ∑ j, R172 j ≤ f x :=
  final_bound candsb6 candsb6_ne hR0 candsb6_sub
    (fun i y hy => hstep_of_shifted_concave (b6lo_le_b6hi i) (hK0 i)
      (hsl i) candsb6_eq y hy)
    hcorner x hx

/-- idx 173 chain: corner bound minus the grid rebate lower-bounds the margin (box 7; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx173 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => f (Function.update y i t) - K173 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K173 i)
    (hR0 : ∀ i, 0 ≤ R173 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B173 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b7lo j) (b7hi j)) :
    B173 - ∑ j, R173 j ≤ f x :=
  final_bound candsb7 candsb7_ne hR0 candsb7_sub
    (fun i y hy => hstep_of_shifted_concave (b7lo_le_b7hi i) (hK0 i)
      (hsl i) candsb7_eq y hy)
    hcorner x hx

/-- idx 174 chain: corner bound minus the grid rebate lower-bounds the margin (box 8; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx174 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => f (Function.update y i t) - K174 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K174 i)
    (hR0 : ∀ i, 0 ≤ R174 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B174 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b8lo j) (b8hi j)) :
    B174 - ∑ j, R174 j ≤ f x :=
  final_bound candsb8 candsb8_ne hR0 candsb8_sub
    (fun i y hy => hstep_of_shifted_concave (b8lo_le_b8hi i) (hK0 i)
      (hsl i) candsb8_eq y hy)
    hcorner x hx

/-- idx 176 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R176v_def (i : Fin 6) : R176 i = K176 i * (b41hi i - b41lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R176, K176, b41lo, b41hi]

/-- idx 176 chain: corner bound minus the grid rebate lower-bounds the margin (box 41; REBATE coordinates per KENV). -/

theorem chain_idx176 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b41lo i) (b41hi i))
        (fun t => f (Function.update y i t) - K176 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K176 i)
    (hR0 : ∀ i, 0 ≤ R176 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb41 j) → B176 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b41lo j) (b41hi j)) :
    B176 - ∑ j, R176 j ≤ f x :=
  final_bound candsb41 candsb41_ne hR0 candsb41_sub
    (fun i y hy => by
      rw [R176v_def i]
      exact hstep_of_shifted_concave (b41lo_le_b41hi i) (hK0 i)
        (hsl i) candsb41_eq y hy)
    hcorner x hx

/-- idx 177 chain: corner bound minus the grid rebate lower-bounds the margin (box 7; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx177 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => f (Function.update y i t) - K177 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K177 i)
    (hR0 : ∀ i, 0 ≤ R177 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B177 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b7lo j) (b7hi j)) :
    B177 - ∑ j, R177 j ≤ f x :=
  final_bound candsb7 candsb7_ne hR0 candsb7_sub
    (fun i y hy => hstep_of_shifted_concave (b7lo_le_b7hi i) (hK0 i)
      (hsl i) candsb7_eq y hy)
    hcorner x hx

/-- idx 178 chain: corner bound minus the grid rebate lower-bounds the margin (box 8; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx178 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => f (Function.update y i t) - K178 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K178 i)
    (hR0 : ∀ i, 0 ≤ R178 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B178 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b8lo j) (b8hi j)) :
    B178 - ∑ j, R178 j ≤ f x :=
  final_bound candsb8 candsb8_ne hR0 candsb8_sub
    (fun i y hy => hstep_of_shifted_concave (b8lo_le_b8hi i) (hK0 i)
      (hsl i) candsb8_eq y hy)
    hcorner x hx

/-- idx 179 chain: corner bound minus the grid rebate lower-bounds the margin (box 8; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx179 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => f (Function.update y i t) - K179 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K179 i)
    (hR0 : ∀ i, 0 ≤ R179 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B179 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b8lo j) (b8hi j)) :
    B179 - ∑ j, R179 j ≤ f x :=
  final_bound candsb8 candsb8_ne hR0 candsb8_sub
    (fun i y hy => hstep_of_shifted_concave (b8lo_le_b8hi i) (hK0 i)
      (hsl i) candsb8_eq y hy)
    hcorner x hx

/-! ### Axiom audit -/

#print axioms chain_idx141

#print axioms chain_idx142

#print axioms chain_idx143

#print axioms chain_idx144

#print axioms chain_idx146

#print axioms chain_idx147

#print axioms chain_idx148

#print axioms chain_idx149

#print axioms chain_idx151

#print axioms chain_idx152

#print axioms chain_idx153

#print axioms chain_idx154

#print axioms chain_idx156

#print axioms chain_idx157

#print axioms chain_idx158

#print axioms chain_idx159

#print axioms chain_idx161

#print axioms chain_idx162

#print axioms chain_idx163

#print axioms chain_idx164

#print axioms chain_idx166

#print axioms chain_idx167

#print axioms chain_idx168

#print axioms chain_idx169

#print axioms chain_idx171

#print axioms chain_idx172

#print axioms chain_idx173

#print axioms chain_idx174

#print axioms chain_idx176

#print axioms chain_idx177

#print axioms chain_idx178

#print axioms chain_idx179

end Kepler.Text
