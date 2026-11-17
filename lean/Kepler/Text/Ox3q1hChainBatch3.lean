/-
Ox3q1hChainBatch3: S3 mass-production batch 3 (32 conjuncts, idx 61-99, boxes 9-21).
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
import Kepler.Text.Ox3q1hChainBatch2

open Set Filter Topology

namespace Kepler.Text

/-- Box 12 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b12lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, 2, 2, 2]

/-- Box 12 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b12hi : Fin 6 → ℝ := ![(6627/2500), (15397/6250), (15397/6250), (52897/25000), (15397/6250), (15397/6250)]

theorem b12lo_le_b12hi (i : Fin 6) : b12lo i ≤ b12hi i := by
  fin_cases i
  all_goals norm_num [b12lo, b12hi]

/-- Box 13 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b13lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, (12927/5000), 2, 2]

/-- Box 13 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b13hi : Fin 6 → ℝ := ![(6627/2500), (15397/6250), (15397/6250), (6627/2500), (15397/6250), (15397/6250)]

theorem b13lo_le_b13hi (i : Fin 6) : b13lo i ≤ b13hi i := by
  fin_cases i
  all_goals norm_num [b13lo, b13hi]

/-- Box 14 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b14lo : Fin 6 → ℝ := ![(26181/10000), 2, 2, (63/25), 2, 2]

/-- Box 14 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b14hi : Fin 6 → ℝ := ![(6627/2500), (15397/6250), (15397/6250), (12927/5000), (15397/6250), (15397/6250)]

theorem b14lo_le_b14hi (i : Fin 6) : b14lo i ≤ b14hi i := by
  fin_cases i
  all_goals norm_num [b14lo, b14hi]

/-- Box 15 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b15lo : Fin 6 → ℝ := ![(26181/10000), 2, 2, 2, 2, 2]

/-- Box 15 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b15hi : Fin 6 → ℝ := ![(6627/2500), (15397/6250), (15397/6250), (52897/25000), (15397/6250), (15397/6250)]

theorem b15lo_le_b15hi (i : Fin 6) : b15lo i ≤ b15hi i := by
  fin_cases i
  all_goals norm_num [b15lo, b15hi]

/-- Box 16 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b16lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, (63/25), 2, 2]

/-- Box 16 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b16hi : Fin 6 → ℝ := ![(26181/10000), (15397/6250), (15397/6250), (12927/5000), (15397/6250), (15397/6250)]

theorem b16lo_le_b16hi (i : Fin 6) : b16lo i ≤ b16hi i := by
  fin_cases i
  all_goals norm_num [b16lo, b16hi]

/-- Box 17 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b17lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, 2, 2, 2]

/-- Box 17 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b17hi : Fin 6 → ℝ := ![(26181/10000), (15397/6250), (15397/6250), (52897/25000), (15397/6250), (15397/6250)]

theorem b17lo_le_b17hi (i : Fin 6) : b17lo i ≤ b17hi i := by
  fin_cases i
  all_goals norm_num [b17lo, b17hi]

/-- Box 18 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b18lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, (32927/16000), 2, 2]

/-- Box 18 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b18hi : Fin 6 → ℝ := ![(26181/10000), (15397/6250), (15397/6250), (52897/25000), (15397/6250), (15397/6250)]

theorem b18lo_le_b18hi (i : Fin 6) : b18lo i ≤ b18hi i := by
  fin_cases i
  all_goals norm_num [b18lo, b18hi]

/-- Box 19 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b19lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, 2, 2, 2]

/-- Box 19 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b19hi : Fin 6 → ℝ := ![(26181/10000), (15397/6250), (15397/6250), (102897/50000), (15397/6250), (15397/6250)]

theorem b19lo_le_b19hi (i : Fin 6) : b19lo i ≤ b19hi i := by
  fin_cases i
  all_goals norm_num [b19lo, b19hi]

/-- Box 20 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b20lo : Fin 6 → ℝ := ![(10407/4000), 2, 2, (63/25), 2, 2]

/-- Box 20 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b20hi : Fin 6 → ℝ := ![(26181/10000), (15397/6250), (15397/6250), (12927/5000), (15397/6250), (15397/6250)]

theorem b20lo_le_b20hi (i : Fin 6) : b20lo i ≤ b20hi i := by
  fin_cases i
  all_goals norm_num [b20lo, b20hi]

/-- Box 21 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b21lo : Fin 6 → ℝ := ![(10407/4000), 2, 2, 2, 2, 2]

/-- Box 21 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b21hi : Fin 6 → ℝ := ![(26181/10000), (15397/6250), (15397/6250), (102897/50000), (15397/6250), (15397/6250)]

theorem b21lo_le_b21hi (i : Fin 6) : b21lo i ≤ b21hi i := by
  fin_cases i
  all_goals norm_num [b21lo, b21hi]


/-- idx 61 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K61 : Fin 6 → ℝ := ![(0/1), (46446597/268435456), (46446597/268435456), (236299718527/274877906944), (46446597/268435456), (46446597/268435456)]

/-- idx 61 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B61 : ℝ := (9664178295251377365438751/1801439850948198400000000000)

/-- idx 61 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R61 : Fin 6 → ℝ := ![0, (389808128001573/83886080000000000), (389808128001573/83886080000000000), (25267292602373583/13743895347200000000), (389808128001573/83886080000000000), (389808128001573/83886080000000000)]

/-- idx 62 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K62 : Fin 6 → ℝ := fun _ => 0

/-- idx 62 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B62 : ℝ := (2411278762556442976863527/450359962737049600000000000)

/-- idx 62 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R62 : Fin 6 → ℝ :=
  fun j => K62 j * (b10hi j - b10lo j) ^ 2 / 8

/-- idx 63 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K63 : Fin 6 → ℝ := fun _ => 0

/-- idx 63 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B63 : ℝ := (96603266922478069066113/18014398509481984000000000)

/-- idx 63 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R63 : Fin 6 → ℝ :=
  fun j => K63 j * (b11hi j - b11lo j) ^ 2 / 8

/-- idx 64 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K64 : Fin 6 → ℝ := fun _ => 0

/-- idx 64 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B64 : ℝ := (2411278762556442976863527/450359962737049600000000000)

/-- idx 64 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R64 : Fin 6 → ℝ :=
  fun j => K64 j * (b12hi j - b12lo j) ^ 2 / 8

/-- idx 66 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K66 : Fin 6 → ℝ := ![(0/1), (46446597/268435456), (46446597/268435456), (236299718527/274877906944), (46446597/268435456), (46446597/268435456)]

/-- idx 66 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B66 : ℝ := (9661903076719629790859551/1801439850948198400000000000)

/-- idx 66 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R66 : Fin 6 → ℝ := ![0, (389808128001573/83886080000000000), (389808128001573/83886080000000000), (25267292602373583/13743895347200000000), (389808128001573/83886080000000000), (389808128001573/83886080000000000)]

/-- idx 67 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K67 : Fin 6 → ℝ := fun _ => 0

/-- idx 67 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B67 : ℝ := (965116392831417524879401/180143985094819840000000000)

/-- idx 67 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R67 : Fin 6 → ℝ :=
  fun j => K67 j * (b11hi j - b11lo j) ^ 2 / 8

/-- idx 68 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K68 : Fin 6 → ℝ := fun _ => 0

/-- idx 68 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B68 : ℝ := (1932823063922836623361699/360287970189639680000000000)

/-- idx 68 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R68 : Fin 6 → ℝ :=
  fun j => K68 j * (b12hi j - b12lo j) ^ 2 / 8

/-- idx 69 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K69 : Fin 6 → ℝ := fun _ => 0

/-- idx 69 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B69 : ℝ := (2411278762556442976863527/450359962737049600000000000)

/-- idx 69 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R69 : Fin 6 → ℝ :=
  fun j => K69 j * (b12hi j - b12lo j) ^ 2 / 8

/-- idx 71 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K71 : Fin 6 → ℝ := ![(0/1), (187814420717/1099511627776), (187814420717/1099511627776), (235857886655/274877906944), (187814420717/1099511627776), (187814420717/1099511627776)]

/-- idx 71 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B71 : ℝ := (2950192360984928262663659/1801439850948198400000000000)

/-- idx 71 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R71 : Fin 6 → ℝ := ![0, (1576252997639280653/343597383680000000000), (1576252997639280653/343597383680000000000), (5044009592426499/10995116277760000000), (1576252997639280653/343597383680000000000), (1576252997639280653/343597383680000000000)]

/-- idx 72 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K72 : Fin 6 → ℝ := fun _ => 0

/-- idx 72 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B72 : ℝ := (2939589470258301474704291/1801439850948198400000000000)

/-- idx 72 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R72 : Fin 6 → ℝ :=
  fun j => K72 j * (b12hi j - b12lo j) ^ 2 / 8

/-- idx 73 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K73 : Fin 6 → ℝ := fun _ => 0

/-- idx 73 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B73 : ℝ := (591232786076284384171393/360287970189639680000000000)

/-- idx 73 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R73 : Fin 6 → ℝ :=
  fun j => K73 j * (b12hi j - b12lo j) ^ 2 / 8

/-- idx 74 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K74 : Fin 6 → ℝ := fun _ => 0

/-- idx 74 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B74 : ℝ := (734387772039426955678493/450359962737049600000000000)

/-- idx 74 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R74 : Fin 6 → ℝ :=
  fun j => K74 j * (b12hi j - b12lo j) ^ 2 / 8

/-- idx 76 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def b3K76 : Fin 6 → ℝ := ![(0/1), (98525807489/1099511627776), (98525807489/1099511627776), (854743839921/1099511627776), (98525807489/1099511627776), (98525807489/1099511627776)]

/-- idx 76 corner-table bound (CONJ_TABLE exact). -/
noncomputable def b3B76 : ℝ := (902012941778731983592301/720575940379279360000000000)

/-- idx 76 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def b3R76 : Fin 6 → ℝ := ![0, (826888578664448801/343597383680000000000), (826888578664448801/343597383680000000000), (91396904058912609/219902325555200000000), (826888578664448801/343597383680000000000), (826888578664448801/343597383680000000000)]

/-- idx 77 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K77 : Fin 6 → ℝ := fun _ => 0

/-- idx 77 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B77 : ℝ := (224290941405761395729149/180143985094819840000000000)

/-- idx 77 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R77 : Fin 6 → ℝ :=
  fun j => K77 j * (b15hi j - b15lo j) ^ 2 / 8

/-- idx 78 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K78 : Fin 6 → ℝ := fun _ => 0

/-- idx 78 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B78 : ℝ := (902784802057526008673009/720575940379279360000000000)

/-- idx 78 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R78 : Fin 6 → ℝ :=
  fun j => K78 j * (b15hi j - b15lo j) ^ 2 / 8

/-- idx 79 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K79 : Fin 6 → ℝ := fun _ => 0

/-- idx 79 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B79 : ℝ := (44885544409492759765531/36028797018963968000000000)

/-- idx 79 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R79 : Fin 6 → ℝ :=
  fun j => K79 j * (b15hi j - b15lo j) ^ 2 / 8

/-- idx 81 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K81 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (604233201725/1099511627776), (0/1), (0/1)]

/-- idx 81 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B81 : ℝ := (177643353933028257987441/90071992547409920000000000)

/-- idx 81 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R81 : Fin 6 → ℝ := ![0, 0, 0, (2584402081090101/8796093022208000000), 0, 0]

/-- idx 82 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K82 : Fin 6 → ℝ := fun _ => 0

/-- idx 82 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B82 : ℝ := (1775586001116581819034139/900719925474099200000000000)

/-- idx 82 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R82 : Fin 6 → ℝ :=
  fun j => K82 j * (b17hi j - b17lo j) ^ 2 / 8

/-- idx 83 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K83 : Fin 6 → ℝ := fun _ => 0

/-- idx 83 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B83 : ℝ := (356291706314003806959607/180143985094819840000000000)

/-- idx 83 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R83 : Fin 6 → ℝ :=
  fun j => K83 j * (b17hi j - b17lo j) ^ 2 / 8

/-- idx 84 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K84 : Fin 6 → ℝ := fun _ => 0

/-- idx 84 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B84 : ℝ := (35526606265659279942811/18014398509481984000000000)

/-- idx 84 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R84 : Fin 6 → ℝ :=
  fun j => K84 j * (b18hi j - b18lo j) ^ 2 / 8

/-- idx 86 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K86 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (604233201725/1099511627776), (0/1), (0/1)]

/-- idx 86 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B86 : ℝ := (177733425925575667907441/90071992547409920000000000)

/-- idx 86 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R86 : Fin 6 → ℝ := ![0, 0, 0, (2584402081090101/8796093022208000000), 0, 0]

/-- idx 87 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K87 : Fin 6 → ℝ := fun _ => 0

/-- idx 87 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B87 : ℝ := (1775586001116581819034139/900719925474099200000000000)

/-- idx 87 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R87 : Fin 6 → ℝ :=
  fun j => K87 j * (b17hi j - b17lo j) ^ 2 / 8

/-- idx 88 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K88 : Fin 6 → ℝ := fun _ => 0

/-- idx 88 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B88 : ℝ := (35580649461187725894811/18014398509481984000000000)

/-- idx 88 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R88 : Fin 6 → ℝ :=
  fun j => K88 j * (b18hi j - b18lo j) ^ 2 / 8

/-- idx 89 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K89 : Fin 6 → ℝ := fun _ => 0

/-- idx 89 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B89 : ℝ := (1775586001116581819034139/900719925474099200000000000)

/-- idx 89 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R89 : Fin 6 → ℝ :=
  fun j => K89 j * (b19hi j - b19lo j) ^ 2 / 8

/-- idx 91 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K91 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (604233201725/1099511627776), (0/1), (0/1)]

/-- idx 91 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B91 : ℝ := (177643353933028257987441/90071992547409920000000000)

/-- idx 91 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R91 : Fin 6 → ℝ := ![0, 0, 0, (2584402081090101/8796093022208000000), 0, 0]

/-- idx 92 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K92 : Fin 6 → ℝ := fun _ => 0

/-- idx 92 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B92 : ℝ := (35526606265659279942811/18014398509481984000000000)

/-- idx 92 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R92 : Fin 6 → ℝ :=
  fun j => K92 j * (b18hi j - b18lo j) ^ 2 / 8

/-- idx 93 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K93 : Fin 6 → ℝ := fun _ => 0

/-- idx 93 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B93 : ℝ := (356291706314003806959607/180143985094819840000000000)

/-- idx 93 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R93 : Fin 6 → ℝ :=
  fun j => K93 j * (b19hi j - b19lo j) ^ 2 / 8

/-- idx 94 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K94 : Fin 6 → ℝ := fun _ => 0

/-- idx 94 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B94 : ℝ := (1775586001116581819034139/900719925474099200000000000)

/-- idx 94 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R94 : Fin 6 → ℝ :=
  fun j => K94 j * (b19hi j - b19lo j) ^ 2 / 8

/-- idx 96 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K96 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (150720901547/274877906944), (0/1), (0/1)]

/-- idx 96 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B96 : ℝ := (234908646216233356851499/720575940379279360000000000)

/-- idx 96 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R96 : Fin 6 → ℝ := ![0, 0, 0, (16116435281519163/54975581388800000000), 0, 0]

/-- idx 97 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K97 : Fin 6 → ℝ := fun _ => 0

/-- idx 97 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B97 : ℝ := (23734450474249571838381/72057594037927936000000000)

/-- idx 97 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R97 : Fin 6 → ℝ :=
  fun j => K97 j * (b21hi j - b21lo j) ^ 2 / 8

/-- idx 98 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K98 : Fin 6 → ℝ := fun _ => 0

/-- idx 98 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B98 : ℝ := (295631055591770941384851/900719925474099200000000000)

/-- idx 98 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R98 : Fin 6 → ℝ :=
  fun j => K98 j * (b21hi j - b21lo j) ^ 2 / 8

/-- idx 99 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K99 : Fin 6 → ℝ := fun _ => 0

/-- idx 99 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B99 : ℝ := (295631055591770941384851/900719925474099200000000000)

/-- idx 99 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R99 : Fin 6 → ℝ :=
  fun j => K99 j * (b21hi j - b21lo j) ^ 2 / 8


/-- The unsplit two-corner grid of box 12. -/
noncomputable def candsb12 : Fin 6 → Finset ℝ :=
  fun i => insert (b12lo i) {b12hi i}

theorem candsb12_eq (i : Fin 6) : candsb12 i = insert (b12lo i) {b12hi i} := rfl

theorem candsb12_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb12 i) :
    c ∈ Set.Icc (b12lo i) (b12hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b12lo_le_b12hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b12lo_le_b12hi i, le_rfl⟩

theorem candsb12_ne (i : Fin 6) : (candsb12 i).Nonempty := ⟨b12lo i, by
  simp only [candsb12]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 13. -/
noncomputable def candsb13 : Fin 6 → Finset ℝ :=
  fun i => insert (b13lo i) {b13hi i}

theorem candsb13_eq (i : Fin 6) : candsb13 i = insert (b13lo i) {b13hi i} := rfl

theorem candsb13_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb13 i) :
    c ∈ Set.Icc (b13lo i) (b13hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b13lo_le_b13hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b13lo_le_b13hi i, le_rfl⟩

theorem candsb13_ne (i : Fin 6) : (candsb13 i).Nonempty := ⟨b13lo i, by
  simp only [candsb13]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 14. -/
noncomputable def candsb14 : Fin 6 → Finset ℝ :=
  fun i => insert (b14lo i) {b14hi i}

theorem candsb14_eq (i : Fin 6) : candsb14 i = insert (b14lo i) {b14hi i} := rfl

theorem candsb14_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb14 i) :
    c ∈ Set.Icc (b14lo i) (b14hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b14lo_le_b14hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b14lo_le_b14hi i, le_rfl⟩

theorem candsb14_ne (i : Fin 6) : (candsb14 i).Nonempty := ⟨b14lo i, by
  simp only [candsb14]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 15. -/
noncomputable def candsb15 : Fin 6 → Finset ℝ :=
  fun i => insert (b15lo i) {b15hi i}

theorem candsb15_eq (i : Fin 6) : candsb15 i = insert (b15lo i) {b15hi i} := rfl

theorem candsb15_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb15 i) :
    c ∈ Set.Icc (b15lo i) (b15hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b15lo_le_b15hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b15lo_le_b15hi i, le_rfl⟩

theorem candsb15_ne (i : Fin 6) : (candsb15 i).Nonempty := ⟨b15lo i, by
  simp only [candsb15]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 16. -/
noncomputable def candsb16 : Fin 6 → Finset ℝ :=
  fun i => insert (b16lo i) {b16hi i}

theorem candsb16_eq (i : Fin 6) : candsb16 i = insert (b16lo i) {b16hi i} := rfl

theorem candsb16_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb16 i) :
    c ∈ Set.Icc (b16lo i) (b16hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b16lo_le_b16hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b16lo_le_b16hi i, le_rfl⟩

theorem candsb16_ne (i : Fin 6) : (candsb16 i).Nonempty := ⟨b16lo i, by
  simp only [candsb16]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 17. -/
noncomputable def candsb17 : Fin 6 → Finset ℝ :=
  fun i => insert (b17lo i) {b17hi i}

theorem candsb17_eq (i : Fin 6) : candsb17 i = insert (b17lo i) {b17hi i} := rfl

theorem candsb17_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb17 i) :
    c ∈ Set.Icc (b17lo i) (b17hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b17lo_le_b17hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b17lo_le_b17hi i, le_rfl⟩

theorem candsb17_ne (i : Fin 6) : (candsb17 i).Nonempty := ⟨b17lo i, by
  simp only [candsb17]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 18. -/
noncomputable def candsb18 : Fin 6 → Finset ℝ :=
  fun i => insert (b18lo i) {b18hi i}

theorem candsb18_eq (i : Fin 6) : candsb18 i = insert (b18lo i) {b18hi i} := rfl

theorem candsb18_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb18 i) :
    c ∈ Set.Icc (b18lo i) (b18hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b18lo_le_b18hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b18lo_le_b18hi i, le_rfl⟩

theorem candsb18_ne (i : Fin 6) : (candsb18 i).Nonempty := ⟨b18lo i, by
  simp only [candsb18]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 19. -/
noncomputable def candsb19 : Fin 6 → Finset ℝ :=
  fun i => insert (b19lo i) {b19hi i}

theorem candsb19_eq (i : Fin 6) : candsb19 i = insert (b19lo i) {b19hi i} := rfl

theorem candsb19_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb19 i) :
    c ∈ Set.Icc (b19lo i) (b19hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b19lo_le_b19hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b19lo_le_b19hi i, le_rfl⟩

theorem candsb19_ne (i : Fin 6) : (candsb19 i).Nonempty := ⟨b19lo i, by
  simp only [candsb19]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 20. -/
noncomputable def candsb20 : Fin 6 → Finset ℝ :=
  fun i => insert (b20lo i) {b20hi i}

theorem candsb20_eq (i : Fin 6) : candsb20 i = insert (b20lo i) {b20hi i} := rfl

theorem candsb20_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb20 i) :
    c ∈ Set.Icc (b20lo i) (b20hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b20lo_le_b20hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b20lo_le_b20hi i, le_rfl⟩

theorem candsb20_ne (i : Fin 6) : (candsb20 i).Nonempty := ⟨b20lo i, by
  simp only [candsb20]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 21. -/
noncomputable def candsb21 : Fin 6 → Finset ℝ :=
  fun i => insert (b21lo i) {b21hi i}

theorem candsb21_eq (i : Fin 6) : candsb21 i = insert (b21lo i) {b21hi i} := rfl

theorem candsb21_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb21 i) :
    c ∈ Set.Icc (b21lo i) (b21hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b21lo_le_b21hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b21lo_le_b21hi i, le_rfl⟩

theorem candsb21_ne (i : Fin 6) : (candsb21 i).Nonempty := ⟨b21lo i, by
  simp only [candsb21]
  exact Finset.mem_insert_self _ _⟩


/-- idx 61 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R61v_def (i : Fin 6) : R61 i = K61 i * (b9hi i - b9lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R61, K61, b9lo, b9hi]

/-- idx 61 chain: corner bound minus the grid rebate lower-bounds the margin (box 9; REBATE coordinates per KENV). -/

theorem chain_idx61 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b9lo i) (b9hi i))
        (fun t => f (Function.update y i t) - K61 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K61 i)
    (hR0 : ∀ i, 0 ≤ R61 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb9 j) → B61 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b9lo j) (b9hi j)) :
    B61 - ∑ j, R61 j ≤ f x :=
  final_bound candsb9 candsb9_ne hR0 candsb9_sub
    (fun i y hy => by
      rw [R61v_def i]
      exact hstep_of_shifted_concave (b9lo_le_b9hi i) (hK0 i)
        (hsl i) candsb9_eq y hy)
    hcorner x hx

/-- idx 62 chain: corner bound minus the grid rebate lower-bounds the margin (box 10; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx62 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => f (Function.update y i t) - K62 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K62 i)
    (hR0 : ∀ i, 0 ≤ R62 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B62 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b10lo j) (b10hi j)) :
    B62 - ∑ j, R62 j ≤ f x :=
  final_bound candsb10 candsb10_ne hR0 candsb10_sub
    (fun i y hy => hstep_of_shifted_concave (b10lo_le_b10hi i) (hK0 i)
      (hsl i) candsb10_eq y hy)
    hcorner x hx

/-- idx 63 chain: corner bound minus the grid rebate lower-bounds the margin (box 11; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx63 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => f (Function.update y i t) - K63 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K63 i)
    (hR0 : ∀ i, 0 ≤ R63 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B63 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b11lo j) (b11hi j)) :
    B63 - ∑ j, R63 j ≤ f x :=
  final_bound candsb11 candsb11_ne hR0 candsb11_sub
    (fun i y hy => hstep_of_shifted_concave (b11lo_le_b11hi i) (hK0 i)
      (hsl i) candsb11_eq y hy)
    hcorner x hx

/-- idx 64 chain: corner bound minus the grid rebate lower-bounds the margin (box 12; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx64 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => f (Function.update y i t) - K64 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K64 i)
    (hR0 : ∀ i, 0 ≤ R64 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B64 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b12lo j) (b12hi j)) :
    B64 - ∑ j, R64 j ≤ f x :=
  final_bound candsb12 candsb12_ne hR0 candsb12_sub
    (fun i y hy => hstep_of_shifted_concave (b12lo_le_b12hi i) (hK0 i)
      (hsl i) candsb12_eq y hy)
    hcorner x hx

/-- idx 66 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R66v_def (i : Fin 6) : R66 i = K66 i * (b9hi i - b9lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R66, K66, b9lo, b9hi]

/-- idx 66 chain: corner bound minus the grid rebate lower-bounds the margin (box 9; REBATE coordinates per KENV). -/

theorem chain_idx66 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b9lo i) (b9hi i))
        (fun t => f (Function.update y i t) - K66 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K66 i)
    (hR0 : ∀ i, 0 ≤ R66 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb9 j) → B66 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b9lo j) (b9hi j)) :
    B66 - ∑ j, R66 j ≤ f x :=
  final_bound candsb9 candsb9_ne hR0 candsb9_sub
    (fun i y hy => by
      rw [R66v_def i]
      exact hstep_of_shifted_concave (b9lo_le_b9hi i) (hK0 i)
        (hsl i) candsb9_eq y hy)
    hcorner x hx

/-- idx 67 chain: corner bound minus the grid rebate lower-bounds the margin (box 11; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx67 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => f (Function.update y i t) - K67 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K67 i)
    (hR0 : ∀ i, 0 ≤ R67 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B67 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b11lo j) (b11hi j)) :
    B67 - ∑ j, R67 j ≤ f x :=
  final_bound candsb11 candsb11_ne hR0 candsb11_sub
    (fun i y hy => hstep_of_shifted_concave (b11lo_le_b11hi i) (hK0 i)
      (hsl i) candsb11_eq y hy)
    hcorner x hx

/-- idx 68 chain: corner bound minus the grid rebate lower-bounds the margin (box 12; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx68 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => f (Function.update y i t) - K68 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K68 i)
    (hR0 : ∀ i, 0 ≤ R68 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B68 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b12lo j) (b12hi j)) :
    B68 - ∑ j, R68 j ≤ f x :=
  final_bound candsb12 candsb12_ne hR0 candsb12_sub
    (fun i y hy => hstep_of_shifted_concave (b12lo_le_b12hi i) (hK0 i)
      (hsl i) candsb12_eq y hy)
    hcorner x hx

/-- idx 69 chain: corner bound minus the grid rebate lower-bounds the margin (box 12; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx69 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => f (Function.update y i t) - K69 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K69 i)
    (hR0 : ∀ i, 0 ≤ R69 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B69 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b12lo j) (b12hi j)) :
    B69 - ∑ j, R69 j ≤ f x :=
  final_bound candsb12 candsb12_ne hR0 candsb12_sub
    (fun i y hy => hstep_of_shifted_concave (b12lo_le_b12hi i) (hK0 i)
      (hsl i) candsb12_eq y hy)
    hcorner x hx

/-- idx 71 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R71v_def (i : Fin 6) : R71 i = K71 i * (b13hi i - b13lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R71, K71, b13lo, b13hi]

/-- idx 71 chain: corner bound minus the grid rebate lower-bounds the margin (box 13; REBATE coordinates per KENV). -/

theorem chain_idx71 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b13lo i) (b13hi i))
        (fun t => f (Function.update y i t) - K71 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K71 i)
    (hR0 : ∀ i, 0 ≤ R71 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb13 j) → B71 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b13lo j) (b13hi j)) :
    B71 - ∑ j, R71 j ≤ f x :=
  final_bound candsb13 candsb13_ne hR0 candsb13_sub
    (fun i y hy => by
      rw [R71v_def i]
      exact hstep_of_shifted_concave (b13lo_le_b13hi i) (hK0 i)
        (hsl i) candsb13_eq y hy)
    hcorner x hx

/-- idx 72 chain: corner bound minus the grid rebate lower-bounds the margin (box 12; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx72 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => f (Function.update y i t) - K72 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K72 i)
    (hR0 : ∀ i, 0 ≤ R72 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B72 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b12lo j) (b12hi j)) :
    B72 - ∑ j, R72 j ≤ f x :=
  final_bound candsb12 candsb12_ne hR0 candsb12_sub
    (fun i y hy => hstep_of_shifted_concave (b12lo_le_b12hi i) (hK0 i)
      (hsl i) candsb12_eq y hy)
    hcorner x hx

/-- idx 73 chain: corner bound minus the grid rebate lower-bounds the margin (box 12; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx73 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => f (Function.update y i t) - K73 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K73 i)
    (hR0 : ∀ i, 0 ≤ R73 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B73 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b12lo j) (b12hi j)) :
    B73 - ∑ j, R73 j ≤ f x :=
  final_bound candsb12 candsb12_ne hR0 candsb12_sub
    (fun i y hy => hstep_of_shifted_concave (b12lo_le_b12hi i) (hK0 i)
      (hsl i) candsb12_eq y hy)
    hcorner x hx

/-- idx 74 chain: corner bound minus the grid rebate lower-bounds the margin (box 12; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx74 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => f (Function.update y i t) - K74 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K74 i)
    (hR0 : ∀ i, 0 ≤ R74 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B74 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b12lo j) (b12hi j)) :
    B74 - ∑ j, R74 j ≤ f x :=
  final_bound candsb12 candsb12_ne hR0 candsb12_sub
    (fun i y hy => hstep_of_shifted_concave (b12lo_le_b12hi i) (hK0 i)
      (hsl i) candsb12_eq y hy)
    hcorner x hx

/-- idx 76 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem b3R76v_def (i : Fin 6) : b3R76 i = b3K76 i * (b14hi i - b14lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [b3R76, b3K76, b14lo, b14hi]

/-- idx 76 chain: corner bound minus the grid rebate lower-bounds the margin (box 14; REBATE coordinates per KENV). -/

theorem chain_idx76b3 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b14lo i) (b14hi i))
        (fun t => f (Function.update y i t) - b3K76 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ b3K76 i)
    (hR0 : ∀ i, 0 ≤ b3R76 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb14 j) → b3B76 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b14lo j) (b14hi j)) :
    b3B76 - ∑ j, b3R76 j ≤ f x :=
  final_bound candsb14 candsb14_ne hR0 candsb14_sub
    (fun i y hy => by
      rw [b3R76v_def i]
      exact hstep_of_shifted_concave (b14lo_le_b14hi i) (hK0 i)
        (hsl i) candsb14_eq y hy)
    hcorner x hx

/-- idx 77 chain: corner bound minus the grid rebate lower-bounds the margin (box 15; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx77 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => f (Function.update y i t) - K77 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K77 i)
    (hR0 : ∀ i, 0 ≤ R77 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B77 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b15lo j) (b15hi j)) :
    B77 - ∑ j, R77 j ≤ f x :=
  final_bound candsb15 candsb15_ne hR0 candsb15_sub
    (fun i y hy => hstep_of_shifted_concave (b15lo_le_b15hi i) (hK0 i)
      (hsl i) candsb15_eq y hy)
    hcorner x hx

/-- idx 78 chain: corner bound minus the grid rebate lower-bounds the margin (box 15; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx78 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => f (Function.update y i t) - K78 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K78 i)
    (hR0 : ∀ i, 0 ≤ R78 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B78 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b15lo j) (b15hi j)) :
    B78 - ∑ j, R78 j ≤ f x :=
  final_bound candsb15 candsb15_ne hR0 candsb15_sub
    (fun i y hy => hstep_of_shifted_concave (b15lo_le_b15hi i) (hK0 i)
      (hsl i) candsb15_eq y hy)
    hcorner x hx

/-- idx 79 chain: corner bound minus the grid rebate lower-bounds the margin (box 15; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx79 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => f (Function.update y i t) - K79 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K79 i)
    (hR0 : ∀ i, 0 ≤ R79 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B79 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b15lo j) (b15hi j)) :
    B79 - ∑ j, R79 j ≤ f x :=
  final_bound candsb15 candsb15_ne hR0 candsb15_sub
    (fun i y hy => hstep_of_shifted_concave (b15lo_le_b15hi i) (hK0 i)
      (hsl i) candsb15_eq y hy)
    hcorner x hx

/-- idx 81 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R81v_def (i : Fin 6) : R81 i = K81 i * (b16hi i - b16lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R81, K81, b16lo, b16hi]

/-- idx 81 chain: corner bound minus the grid rebate lower-bounds the margin (box 16; REBATE coordinates per KENV). -/

theorem chain_idx81 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b16lo i) (b16hi i))
        (fun t => f (Function.update y i t) - K81 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K81 i)
    (hR0 : ∀ i, 0 ≤ R81 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb16 j) → B81 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b16lo j) (b16hi j)) :
    B81 - ∑ j, R81 j ≤ f x :=
  final_bound candsb16 candsb16_ne hR0 candsb16_sub
    (fun i y hy => by
      rw [R81v_def i]
      exact hstep_of_shifted_concave (b16lo_le_b16hi i) (hK0 i)
        (hsl i) candsb16_eq y hy)
    hcorner x hx

/-- idx 82 chain: corner bound minus the grid rebate lower-bounds the margin (box 17; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx82 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => f (Function.update y i t) - K82 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K82 i)
    (hR0 : ∀ i, 0 ≤ R82 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B82 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b17lo j) (b17hi j)) :
    B82 - ∑ j, R82 j ≤ f x :=
  final_bound candsb17 candsb17_ne hR0 candsb17_sub
    (fun i y hy => hstep_of_shifted_concave (b17lo_le_b17hi i) (hK0 i)
      (hsl i) candsb17_eq y hy)
    hcorner x hx

/-- idx 83 chain: corner bound minus the grid rebate lower-bounds the margin (box 17; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx83 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => f (Function.update y i t) - K83 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K83 i)
    (hR0 : ∀ i, 0 ≤ R83 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B83 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b17lo j) (b17hi j)) :
    B83 - ∑ j, R83 j ≤ f x :=
  final_bound candsb17 candsb17_ne hR0 candsb17_sub
    (fun i y hy => hstep_of_shifted_concave (b17lo_le_b17hi i) (hK0 i)
      (hsl i) candsb17_eq y hy)
    hcorner x hx

/-- idx 84 chain: corner bound minus the grid rebate lower-bounds the margin (box 18; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx84 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => f (Function.update y i t) - K84 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K84 i)
    (hR0 : ∀ i, 0 ≤ R84 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B84 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b18lo j) (b18hi j)) :
    B84 - ∑ j, R84 j ≤ f x :=
  final_bound candsb18 candsb18_ne hR0 candsb18_sub
    (fun i y hy => hstep_of_shifted_concave (b18lo_le_b18hi i) (hK0 i)
      (hsl i) candsb18_eq y hy)
    hcorner x hx

/-- idx 86 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R86v_def (i : Fin 6) : R86 i = K86 i * (b16hi i - b16lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R86, K86, b16lo, b16hi]

/-- idx 86 chain: corner bound minus the grid rebate lower-bounds the margin (box 16; REBATE coordinates per KENV). -/

theorem chain_idx86 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b16lo i) (b16hi i))
        (fun t => f (Function.update y i t) - K86 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K86 i)
    (hR0 : ∀ i, 0 ≤ R86 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb16 j) → B86 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b16lo j) (b16hi j)) :
    B86 - ∑ j, R86 j ≤ f x :=
  final_bound candsb16 candsb16_ne hR0 candsb16_sub
    (fun i y hy => by
      rw [R86v_def i]
      exact hstep_of_shifted_concave (b16lo_le_b16hi i) (hK0 i)
        (hsl i) candsb16_eq y hy)
    hcorner x hx

/-- idx 87 chain: corner bound minus the grid rebate lower-bounds the margin (box 17; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx87 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => f (Function.update y i t) - K87 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K87 i)
    (hR0 : ∀ i, 0 ≤ R87 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B87 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b17lo j) (b17hi j)) :
    B87 - ∑ j, R87 j ≤ f x :=
  final_bound candsb17 candsb17_ne hR0 candsb17_sub
    (fun i y hy => hstep_of_shifted_concave (b17lo_le_b17hi i) (hK0 i)
      (hsl i) candsb17_eq y hy)
    hcorner x hx

/-- idx 88 chain: corner bound minus the grid rebate lower-bounds the margin (box 18; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx88 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => f (Function.update y i t) - K88 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K88 i)
    (hR0 : ∀ i, 0 ≤ R88 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B88 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b18lo j) (b18hi j)) :
    B88 - ∑ j, R88 j ≤ f x :=
  final_bound candsb18 candsb18_ne hR0 candsb18_sub
    (fun i y hy => hstep_of_shifted_concave (b18lo_le_b18hi i) (hK0 i)
      (hsl i) candsb18_eq y hy)
    hcorner x hx

/-- idx 89 chain: corner bound minus the grid rebate lower-bounds the margin (box 19; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx89 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => f (Function.update y i t) - K89 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K89 i)
    (hR0 : ∀ i, 0 ≤ R89 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B89 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b19lo j) (b19hi j)) :
    B89 - ∑ j, R89 j ≤ f x :=
  final_bound candsb19 candsb19_ne hR0 candsb19_sub
    (fun i y hy => hstep_of_shifted_concave (b19lo_le_b19hi i) (hK0 i)
      (hsl i) candsb19_eq y hy)
    hcorner x hx

/-- idx 91 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R91v_def (i : Fin 6) : R91 i = K91 i * (b16hi i - b16lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R91, K91, b16lo, b16hi]

/-- idx 91 chain: corner bound minus the grid rebate lower-bounds the margin (box 16; REBATE coordinates per KENV). -/

theorem chain_idx91 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b16lo i) (b16hi i))
        (fun t => f (Function.update y i t) - K91 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K91 i)
    (hR0 : ∀ i, 0 ≤ R91 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb16 j) → B91 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b16lo j) (b16hi j)) :
    B91 - ∑ j, R91 j ≤ f x :=
  final_bound candsb16 candsb16_ne hR0 candsb16_sub
    (fun i y hy => by
      rw [R91v_def i]
      exact hstep_of_shifted_concave (b16lo_le_b16hi i) (hK0 i)
        (hsl i) candsb16_eq y hy)
    hcorner x hx

/-- idx 92 chain: corner bound minus the grid rebate lower-bounds the margin (box 18; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx92 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => f (Function.update y i t) - K92 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K92 i)
    (hR0 : ∀ i, 0 ≤ R92 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B92 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b18lo j) (b18hi j)) :
    B92 - ∑ j, R92 j ≤ f x :=
  final_bound candsb18 candsb18_ne hR0 candsb18_sub
    (fun i y hy => hstep_of_shifted_concave (b18lo_le_b18hi i) (hK0 i)
      (hsl i) candsb18_eq y hy)
    hcorner x hx

/-- idx 93 chain: corner bound minus the grid rebate lower-bounds the margin (box 19; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx93 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => f (Function.update y i t) - K93 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K93 i)
    (hR0 : ∀ i, 0 ≤ R93 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B93 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b19lo j) (b19hi j)) :
    B93 - ∑ j, R93 j ≤ f x :=
  final_bound candsb19 candsb19_ne hR0 candsb19_sub
    (fun i y hy => hstep_of_shifted_concave (b19lo_le_b19hi i) (hK0 i)
      (hsl i) candsb19_eq y hy)
    hcorner x hx

/-- idx 94 chain: corner bound minus the grid rebate lower-bounds the margin (box 19; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx94 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => f (Function.update y i t) - K94 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K94 i)
    (hR0 : ∀ i, 0 ≤ R94 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B94 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b19lo j) (b19hi j)) :
    B94 - ∑ j, R94 j ≤ f x :=
  final_bound candsb19 candsb19_ne hR0 candsb19_sub
    (fun i y hy => hstep_of_shifted_concave (b19lo_le_b19hi i) (hK0 i)
      (hsl i) candsb19_eq y hy)
    hcorner x hx

/-- idx 96 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R96v_def (i : Fin 6) : R96 i = K96 i * (b20hi i - b20lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R96, K96, b20lo, b20hi]

/-- idx 96 chain: corner bound minus the grid rebate lower-bounds the margin (box 20; REBATE coordinates per KENV). -/

theorem chain_idx96 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b20lo i) (b20hi i))
        (fun t => f (Function.update y i t) - K96 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K96 i)
    (hR0 : ∀ i, 0 ≤ R96 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb20 j) → B96 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b20lo j) (b20hi j)) :
    B96 - ∑ j, R96 j ≤ f x :=
  final_bound candsb20 candsb20_ne hR0 candsb20_sub
    (fun i y hy => by
      rw [R96v_def i]
      exact hstep_of_shifted_concave (b20lo_le_b20hi i) (hK0 i)
        (hsl i) candsb20_eq y hy)
    hcorner x hx

/-- idx 97 chain: corner bound minus the grid rebate lower-bounds the margin (box 21; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx97 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => f (Function.update y i t) - K97 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K97 i)
    (hR0 : ∀ i, 0 ≤ R97 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B97 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b21lo j) (b21hi j)) :
    B97 - ∑ j, R97 j ≤ f x :=
  final_bound candsb21 candsb21_ne hR0 candsb21_sub
    (fun i y hy => hstep_of_shifted_concave (b21lo_le_b21hi i) (hK0 i)
      (hsl i) candsb21_eq y hy)
    hcorner x hx

/-- idx 98 chain: corner bound minus the grid rebate lower-bounds the margin (box 21; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx98 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => f (Function.update y i t) - K98 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K98 i)
    (hR0 : ∀ i, 0 ≤ R98 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B98 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b21lo j) (b21hi j)) :
    B98 - ∑ j, R98 j ≤ f x :=
  final_bound candsb21 candsb21_ne hR0 candsb21_sub
    (fun i y hy => hstep_of_shifted_concave (b21lo_le_b21hi i) (hK0 i)
      (hsl i) candsb21_eq y hy)
    hcorner x hx

/-- idx 99 chain: corner bound minus the grid rebate lower-bounds the margin (box 21; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx99 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => f (Function.update y i t) - K99 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K99 i)
    (hR0 : ∀ i, 0 ≤ R99 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B99 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b21lo j) (b21hi j)) :
    B99 - ∑ j, R99 j ≤ f x :=
  final_bound candsb21 candsb21_ne hR0 candsb21_sub
    (fun i y hy => hstep_of_shifted_concave (b21lo_le_b21hi i) (hK0 i)
      (hsl i) candsb21_eq y hy)
    hcorner x hx

/-! ### Axiom audit -/

#print axioms chain_idx61

#print axioms chain_idx62

#print axioms chain_idx63

#print axioms chain_idx64

#print axioms chain_idx66

#print axioms chain_idx67

#print axioms chain_idx68

#print axioms chain_idx69

#print axioms chain_idx71

#print axioms chain_idx72

#print axioms chain_idx73

#print axioms chain_idx74

#print axioms chain_idx76b3

#print axioms chain_idx77

#print axioms chain_idx78

#print axioms chain_idx79

#print axioms chain_idx81

#print axioms chain_idx82

#print axioms chain_idx83

#print axioms chain_idx84

#print axioms chain_idx86

#print axioms chain_idx87

#print axioms chain_idx88

#print axioms chain_idx89

#print axioms chain_idx91

#print axioms chain_idx92

#print axioms chain_idx93

#print axioms chain_idx94

#print axioms chain_idx96

#print axioms chain_idx97

#print axioms chain_idx98

#print axioms chain_idx99

end Kepler.Text
