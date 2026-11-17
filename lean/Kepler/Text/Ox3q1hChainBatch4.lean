/-
Ox3q1hChainBatch4: S3 mass-production batch 4 (32 conjuncts, idx 101-139, boxes 22-34).
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
import Kepler.Text.Ox3q1hChainBatch3

open Set Filter Topology

namespace Kepler.Text

/-- Box 22 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b22lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, (25527/10000), 2, 2]

/-- Box 22 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b22hi : Fin 6 → ℝ := ![(10407/4000), (15397/6250), (15397/6250), (12927/5000), (15397/6250), (15397/6250)]

theorem b22lo_le_b22hi (i : Fin 6) : b22lo i ≤ b22hi i := by
  fin_cases i
  all_goals norm_num [b22lo, b22hi]

/-- Box 23 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b23lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, 2, 2, 2]

/-- Box 23 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b23hi : Fin 6 → ℝ := ![(10407/4000), (15397/6250), (15397/6250), (102897/50000), (15397/6250), (15397/6250)]

theorem b23lo_le_b23hi (i : Fin 6) : b23lo i ≤ b23hi i := by
  fin_cases i
  all_goals norm_num [b23lo, b23hi]

/-- Box 24 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b24lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, (63/25), 2, 2]

/-- Box 24 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b24hi : Fin 6 → ℝ := ![(10407/4000), (15397/6250), (15397/6250), (25527/10000), (15397/6250), (15397/6250)]

theorem b24lo_le_b24hi (i : Fin 6) : b24lo i ≤ b24hi i := by
  fin_cases i
  all_goals norm_num [b24lo, b24hi]

/-- Box 25 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b25lo : Fin 6 → ℝ := ![(63/25), 2, 2, (63/25), 2, 2]

/-- Box 25 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b25hi : Fin 6 → ℝ := ![(12927/5000), (15397/6250), (15397/6250), (6627/2500), (15397/6250), (15397/6250)]

theorem b25lo_le_b25hi (i : Fin 6) : b25lo i ≤ b25hi i := by
  fin_cases i
  all_goals norm_num [b25lo, b25hi]

/-- Box 26 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b26lo : Fin 6 → ℝ := ![(63/25), 2, 2, 2, 2, 2]

/-- Box 26 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b26hi : Fin 6 → ℝ := ![(12927/5000), (15397/6250), (15397/6250), (27897/12500), (15397/6250), (15397/6250)]

theorem b26lo_le_b26hi (i : Fin 6) : b26lo i ≤ b26hi i := by
  fin_cases i
  all_goals norm_num [b26lo, b26hi]

/-- Box 27 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b27lo : Fin 6 → ℝ := ![(63/25), 2, 2, (16927/8000), 2, 2]

/-- Box 27 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b27hi : Fin 6 → ℝ := ![(12927/5000), (15397/6250), (15397/6250), (27897/12500), (15397/6250), (15397/6250)]

theorem b27lo_le_b27hi (i : Fin 6) : b27lo i ≤ b27hi i := by
  fin_cases i
  all_goals norm_num [b27lo, b27hi]

/-- Box 28 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b28lo : Fin 6 → ℝ := ![(63/25), 2, 2, 2, 2, 2]

/-- Box 28 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b28hi : Fin 6 → ℝ := ![(12927/5000), (15397/6250), (15397/6250), (52897/25000), (15397/6250), (15397/6250)]

theorem b28lo_le_b28hi (i : Fin 6) : b28lo i ≤ b28hi i := by
  fin_cases i
  all_goals norm_num [b28lo, b28hi]

/-- Box 29 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b29lo : Fin 6 → ℝ := ![(25527/10000), 2, 2, (12927/5000), 2, 2]

/-- Box 29 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b29hi : Fin 6 → ℝ := ![(12927/5000), (15397/6250), (15397/6250), (6627/2500), (15397/6250), (15397/6250)]

theorem b29lo_le_b29hi (i : Fin 6) : b29lo i ≤ b29hi i := by
  fin_cases i
  all_goals norm_num [b29lo, b29hi]

/-- Box 30 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b30lo : Fin 6 → ℝ := ![(25527/10000), 2, 2, 2, 2, 2]

/-- Box 30 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b30hi : Fin 6 → ℝ := ![(12927/5000), (15397/6250), (15397/6250), (52897/25000), (15397/6250), (15397/6250)]

theorem b30lo_le_b30hi (i : Fin 6) : b30lo i ≤ b30hi i := by
  fin_cases i
  all_goals norm_num [b30lo, b30hi]

/-- Box 31 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b31lo : Fin 6 → ℝ := ![(63/25), 2, 2, (12927/5000), 2, 2]

/-- Box 31 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b31hi : Fin 6 → ℝ := ![(25527/10000), (15397/6250), (15397/6250), (6627/2500), (15397/6250), (15397/6250)]

theorem b31lo_le_b31hi (i : Fin 6) : b31lo i ≤ b31hi i := by
  fin_cases i
  all_goals norm_num [b31lo, b31hi]

/-- Box 32 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b32lo : Fin 6 → ℝ := ![(63/25), 2, 2, 2, 2, 2]

/-- Box 32 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b32hi : Fin 6 → ℝ := ![(25527/10000), (15397/6250), (15397/6250), (52897/25000), (15397/6250), (15397/6250)]

theorem b32lo_le_b32hi (i : Fin 6) : b32lo i ≤ b32hi i := by
  fin_cases i
  all_goals norm_num [b32lo, b32hi]

/-- Box 33 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b33lo : Fin 6 → ℝ := ![(63/25), 2, 2, (32927/16000), 2, 2]

/-- Box 33 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b33hi : Fin 6 → ℝ := ![(25527/10000), (15397/6250), (15397/6250), (52897/25000), (15397/6250), (15397/6250)]

theorem b33lo_le_b33hi (i : Fin 6) : b33lo i ≤ b33hi i := by
  fin_cases i
  all_goals norm_num [b33lo, b33hi]

/-- Box 34 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b34lo : Fin 6 → ℝ := ![(63/25), 2, 2, 2, 2, 2]

/-- Box 34 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b34hi : Fin 6 → ℝ := ![(25527/10000), (15397/6250), (15397/6250), (102897/50000), (15397/6250), (15397/6250)]

theorem b34lo_le_b34hi (i : Fin 6) : b34lo i ≤ b34hi i := by
  fin_cases i
  all_goals norm_num [b34lo, b34hi]


/-- idx 101 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K101 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (596135628505/1099511627776), (0/1), (0/1)]

/-- idx 101 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B101 : ℝ := (60425570515597217172127/144115188075855872000000000)

/-- idx 101 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R101 : Fin 6 → ℝ := ![0, 0, 0, (12748837324082229/175921860444160000000), 0, 0]

/-- idx 102 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K102 : Fin 6 → ℝ := fun _ => 0

/-- idx 102 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B102 : ℝ := (298715483867368104034829/720575940379279360000000000)

/-- idx 102 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R102 : Fin 6 → ℝ :=
  fun j => K102 j * (b23hi j - b23lo j) ^ 2 / 8

/-- idx 103 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K103 : Fin 6 → ℝ := fun _ => 0

/-- idx 103 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B103 : ℝ := (1508718784408980513689881/3602879701896396800000000000)

/-- idx 103 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R103 : Fin 6 → ℝ :=
  fun j => K103 j * (b23hi j - b23lo j) ^ 2 / 8

/-- idx 104 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K104 : Fin 6 → ℝ := fun _ => 0

/-- idx 104 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B104 : ℝ := (298715483867368104034829/720575940379279360000000000)

/-- idx 104 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R104 : Fin 6 → ℝ :=
  fun j => K104 j * (b23hi j - b23lo j) ^ 2 / 8

/-- idx 106 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K106 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (301409669867/549755813888), (0/1), (0/1)]

/-- idx 106 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B106 : ℝ := (28193936750087767554951/72057594037927936000000000)

/-- idx 106 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R106 : Fin 6 → ℝ := ![0, 0, 0, (32229434589208443/439804651110400000000), 0, 0]

/-- idx 107 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K107 : Fin 6 → ℝ := fun _ => 0

/-- idx 107 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B107 : ℝ := (14320576368836929194993/36028797018963968000000000)

/-- idx 107 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R107 : Fin 6 → ℝ :=
  fun j => K107 j * (b23hi j - b23lo j) ^ 2 / 8

/-- idx 108 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K108 : Fin 6 → ℝ := fun _ => 0

/-- idx 108 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B108 : ℝ := (35127315796962965609979/90071992547409920000000000)

/-- idx 108 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R108 : Fin 6 → ℝ :=
  fun j => K108 j * (b23hi j - b23lo j) ^ 2 / 8

/-- idx 109 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K109 : Fin 6 → ℝ := fun _ => 0

/-- idx 109 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B109 : ℝ := (710744425100943783814353/1801439850948198400000000000)

/-- idx 109 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R109 : Fin 6 → ℝ :=
  fun j => K109 j * (b23hi j - b23lo j) ^ 2 / 8

/-- idx 111 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K111 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (76718079617/137438953472), (0/1), (0/1)]

/-- idx 111 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B111 : ℝ := (58003536949343176040209/28823037615171174400000000)

/-- idx 111 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R111 : Fin 6 → ℝ := ![0, 0, 0, (8203387535366193/6871947673600000000), 0, 0]

/-- idx 112 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K112 : Fin 6 → ℝ := fun _ => 0

/-- idx 112 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B112 : ℝ := (7238830132115033097287123/3602879701896396800000000000)

/-- idx 112 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R112 : Fin 6 → ℝ :=
  fun j => K112 j * (b26hi j - b26lo j) ^ 2 / 8

/-- idx 113 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K113 : Fin 6 → ℝ := fun _ => 0

/-- idx 113 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B113 : ℝ := (289707778743033646466769/144115188075855872000000000)

/-- idx 113 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R113 : Fin 6 → ℝ :=
  fun j => K113 j * (b26hi j - b26lo j) ^ 2 / 8

/-- idx 114 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K114 : Fin 6 → ℝ := fun _ => 0

/-- idx 114 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B114 : ℝ := (181114808578158272291353/90071992547409920000000000)

/-- idx 114 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R114 : Fin 6 → ℝ :=
  fun j => K114 j * (b27hi j - b27lo j) ^ 2 / 8

/-- idx 116 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K116 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (76718079617/137438953472), (0/1), (0/1)]

/-- idx 116 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B116 : ℝ := (58000078184829355499281/28823037615171174400000000)

/-- idx 116 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R116 : Fin 6 → ℝ := ![0, 0, 0, (8203387535366193/6871947673600000000), 0, 0]

/-- idx 117 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K117 : Fin 6 → ℝ := fun _ => 0

/-- idx 117 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B117 : ℝ := (7238830132115033097287123/3602879701896396800000000000)

/-- idx 117 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R117 : Fin 6 → ℝ :=
  fun j => K117 j * (b26hi j - b26lo j) ^ 2 / 8

/-- idx 118 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K118 : Fin 6 → ℝ := fun _ => 0

/-- idx 118 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B118 : ℝ := (57932445597151768384501/28823037615171174400000000)

/-- idx 118 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R118 : Fin 6 → ℝ :=
  fun j => K118 j * (b27hi j - b27lo j) ^ 2 / 8

/-- idx 119 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K119 : Fin 6 → ℝ := fun _ => 0

/-- idx 119 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B119 : ℝ := (7238830132115033097287123/3602879701896396800000000000)

/-- idx 119 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R119 : Fin 6 → ℝ :=
  fun j => K119 j * (b28hi j - b28lo j) ^ 2 / 8

/-- idx 121 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K121 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (76718079617/137438953472), (0/1), (0/1)]

/-- idx 121 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B121 : ℝ := (58028901222444526673681/28823037615171174400000000)

/-- idx 121 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R121 : Fin 6 → ℝ := ![0, 0, 0, (8203387535366193/6871947673600000000), 0, 0]

/-- idx 122 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K122 : Fin 6 → ℝ := fun _ => 0

/-- idx 122 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B122 : ℝ := (57932445597151768384501/28823037615171174400000000)

/-- idx 122 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R122 : Fin 6 → ℝ :=
  fun j => K122 j * (b27hi j - b27lo j) ^ 2 / 8

/-- idx 123 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K123 : Fin 6 → ℝ := fun _ => 0

/-- idx 123 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B123 : ℝ := (7238830132115033097287123/3602879701896396800000000000)

/-- idx 123 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R123 : Fin 6 → ℝ :=
  fun j => K123 j * (b28hi j - b28lo j) ^ 2 / 8

/-- idx 124 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K124 : Fin 6 → ℝ := fun _ => 0

/-- idx 124 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B124 : ℝ := (289707778743033646466769/144115188075855872000000000)

/-- idx 124 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R124 : Fin 6 → ℝ :=
  fun j => K124 j * (b28hi j - b28lo j) ^ 2 / 8

/-- idx 126 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K126 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (147700378203/274877906944), (0/1), (0/1)]

/-- idx 126 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B126 : ℝ := (5775702846294293121687/14411518807585587200000000)

/-- idx 126 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R126 : Fin 6 → ℝ := ![0, 0, 0, (15793453740868587/54975581388800000000), 0, 0]

/-- idx 127 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K127 : Fin 6 → ℝ := fun _ => 0

/-- idx 127 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B127 : ℝ := (291772139870702040537501/720575940379279360000000000)

/-- idx 127 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R127 : Fin 6 → ℝ :=
  fun j => K127 j * (b30hi j - b30lo j) ^ 2 / 8

/-- idx 128 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K128 : Fin 6 → ℝ := fun _ => 0

/-- idx 128 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B128 : ℝ := (288741571694175972094227/720575940379279360000000000)

/-- idx 128 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R128 : Fin 6 → ℝ :=
  fun j => K128 j * (b30hi j - b30lo j) ^ 2 / 8

/-- idx 129 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K129 : Fin 6 → ℝ := fun _ => 0

/-- idx 129 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B129 : ℝ := (291772139870702040537501/720575940379279360000000000)

/-- idx 129 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R129 : Fin 6 → ℝ :=
  fun j => K129 j * (b30hi j - b30lo j) ^ 2 / 8

/-- idx 131 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K131 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (597292424679/1099511627776), (0/1), (0/1)]

/-- idx 131 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B131 : ℝ := (1667201535459614533087/1441151880758558720000000)

/-- idx 131 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R131 : Fin 6 → ℝ := ![0, 0, 0, (63867881678500791/219902325555200000000), 0, 0]

/-- idx 132 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K132 : Fin 6 → ℝ := fun _ => 0

/-- idx 132 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B132 : ℝ := (836140091848463825143807/720575940379279360000000000)

/-- idx 132 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R132 : Fin 6 → ℝ :=
  fun j => K132 j * (b32hi j - b32lo j) ^ 2 / 8

/-- idx 133 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K133 : Fin 6 → ℝ := fun _ => 0

/-- idx 133 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B133 : ℝ := (16737968422090828369341/14411518807585587200000000)

/-- idx 133 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R133 : Fin 6 → ℝ :=
  fun j => K133 j * (b32hi j - b32lo j) ^ 2 / 8

/-- idx 134 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K134 : Fin 6 → ℝ := fun _ => 0

/-- idx 134 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B134 : ℝ := (33521304402286636518959/28823037615171174400000000)

/-- idx 134 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R134 : Fin 6 → ℝ :=
  fun j => K134 j * (b33hi j - b33lo j) ^ 2 / 8

/-- idx 136 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K136 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (597292424679/1099511627776), (0/1), (0/1)]

/-- idx 136 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B136 : ℝ := (8339178211435741494619/7205759403792793600000000)

/-- idx 136 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R136 : Fin 6 → ℝ := ![0, 0, 0, (63867881678500791/219902325555200000000), 0, 0]

/-- idx 137 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K137 : Fin 6 → ℝ := fun _ => 0

/-- idx 137 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B137 : ℝ := (16766791459705999543741/14411518807585587200000000)

/-- idx 137 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R137 : Fin 6 → ℝ :=
  fun j => K137 j * (b32hi j - b32lo j) ^ 2 / 8

/-- idx 138 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K138 : Fin 6 → ℝ := fun _ => 0

/-- idx 138 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B138 : ℝ := (4174175383681885475029337/3602879701896396800000000000)

/-- idx 138 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R138 : Fin 6 → ℝ :=
  fun j => K138 j * (b33hi j - b33lo j) ^ 2 / 8

/-- idx 139 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K139 : Fin 6 → ℝ := fun _ => 0

/-- idx 139 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B139 : ℝ := (16760450391430661885373/14411518807585587200000000)

/-- idx 139 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R139 : Fin 6 → ℝ :=
  fun j => K139 j * (b34hi j - b34lo j) ^ 2 / 8


/-- The unsplit two-corner grid of box 22. -/
noncomputable def candsb22 : Fin 6 → Finset ℝ :=
  fun i => insert (b22lo i) {b22hi i}

theorem candsb22_eq (i : Fin 6) : candsb22 i = insert (b22lo i) {b22hi i} := rfl

theorem candsb22_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb22 i) :
    c ∈ Set.Icc (b22lo i) (b22hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b22lo_le_b22hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b22lo_le_b22hi i, le_rfl⟩

theorem candsb22_ne (i : Fin 6) : (candsb22 i).Nonempty := ⟨b22lo i, by
  simp only [candsb22]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 23. -/
noncomputable def candsb23 : Fin 6 → Finset ℝ :=
  fun i => insert (b23lo i) {b23hi i}

theorem candsb23_eq (i : Fin 6) : candsb23 i = insert (b23lo i) {b23hi i} := rfl

theorem candsb23_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb23 i) :
    c ∈ Set.Icc (b23lo i) (b23hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b23lo_le_b23hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b23lo_le_b23hi i, le_rfl⟩

theorem candsb23_ne (i : Fin 6) : (candsb23 i).Nonempty := ⟨b23lo i, by
  simp only [candsb23]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 24. -/
noncomputable def candsb24 : Fin 6 → Finset ℝ :=
  fun i => insert (b24lo i) {b24hi i}

theorem candsb24_eq (i : Fin 6) : candsb24 i = insert (b24lo i) {b24hi i} := rfl

theorem candsb24_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb24 i) :
    c ∈ Set.Icc (b24lo i) (b24hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b24lo_le_b24hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b24lo_le_b24hi i, le_rfl⟩

theorem candsb24_ne (i : Fin 6) : (candsb24 i).Nonempty := ⟨b24lo i, by
  simp only [candsb24]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 25. -/
noncomputable def candsb25 : Fin 6 → Finset ℝ :=
  fun i => insert (b25lo i) {b25hi i}

theorem candsb25_eq (i : Fin 6) : candsb25 i = insert (b25lo i) {b25hi i} := rfl

theorem candsb25_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb25 i) :
    c ∈ Set.Icc (b25lo i) (b25hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b25lo_le_b25hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b25lo_le_b25hi i, le_rfl⟩

theorem candsb25_ne (i : Fin 6) : (candsb25 i).Nonempty := ⟨b25lo i, by
  simp only [candsb25]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 26. -/
noncomputable def candsb26 : Fin 6 → Finset ℝ :=
  fun i => insert (b26lo i) {b26hi i}

theorem candsb26_eq (i : Fin 6) : candsb26 i = insert (b26lo i) {b26hi i} := rfl

theorem candsb26_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb26 i) :
    c ∈ Set.Icc (b26lo i) (b26hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b26lo_le_b26hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b26lo_le_b26hi i, le_rfl⟩

theorem candsb26_ne (i : Fin 6) : (candsb26 i).Nonempty := ⟨b26lo i, by
  simp only [candsb26]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 27. -/
noncomputable def candsb27 : Fin 6 → Finset ℝ :=
  fun i => insert (b27lo i) {b27hi i}

theorem candsb27_eq (i : Fin 6) : candsb27 i = insert (b27lo i) {b27hi i} := rfl

theorem candsb27_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb27 i) :
    c ∈ Set.Icc (b27lo i) (b27hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b27lo_le_b27hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b27lo_le_b27hi i, le_rfl⟩

theorem candsb27_ne (i : Fin 6) : (candsb27 i).Nonempty := ⟨b27lo i, by
  simp only [candsb27]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 28. -/
noncomputable def candsb28 : Fin 6 → Finset ℝ :=
  fun i => insert (b28lo i) {b28hi i}

theorem candsb28_eq (i : Fin 6) : candsb28 i = insert (b28lo i) {b28hi i} := rfl

theorem candsb28_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb28 i) :
    c ∈ Set.Icc (b28lo i) (b28hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b28lo_le_b28hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b28lo_le_b28hi i, le_rfl⟩

theorem candsb28_ne (i : Fin 6) : (candsb28 i).Nonempty := ⟨b28lo i, by
  simp only [candsb28]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 29. -/
noncomputable def candsb29 : Fin 6 → Finset ℝ :=
  fun i => insert (b29lo i) {b29hi i}

theorem candsb29_eq (i : Fin 6) : candsb29 i = insert (b29lo i) {b29hi i} := rfl

theorem candsb29_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb29 i) :
    c ∈ Set.Icc (b29lo i) (b29hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b29lo_le_b29hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b29lo_le_b29hi i, le_rfl⟩

theorem candsb29_ne (i : Fin 6) : (candsb29 i).Nonempty := ⟨b29lo i, by
  simp only [candsb29]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 30. -/
noncomputable def candsb30 : Fin 6 → Finset ℝ :=
  fun i => insert (b30lo i) {b30hi i}

theorem candsb30_eq (i : Fin 6) : candsb30 i = insert (b30lo i) {b30hi i} := rfl

theorem candsb30_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb30 i) :
    c ∈ Set.Icc (b30lo i) (b30hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b30lo_le_b30hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b30lo_le_b30hi i, le_rfl⟩

theorem candsb30_ne (i : Fin 6) : (candsb30 i).Nonempty := ⟨b30lo i, by
  simp only [candsb30]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 31. -/
noncomputable def candsb31 : Fin 6 → Finset ℝ :=
  fun i => insert (b31lo i) {b31hi i}

theorem candsb31_eq (i : Fin 6) : candsb31 i = insert (b31lo i) {b31hi i} := rfl

theorem candsb31_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb31 i) :
    c ∈ Set.Icc (b31lo i) (b31hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b31lo_le_b31hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b31lo_le_b31hi i, le_rfl⟩

theorem candsb31_ne (i : Fin 6) : (candsb31 i).Nonempty := ⟨b31lo i, by
  simp only [candsb31]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 32. -/
noncomputable def candsb32 : Fin 6 → Finset ℝ :=
  fun i => insert (b32lo i) {b32hi i}

theorem candsb32_eq (i : Fin 6) : candsb32 i = insert (b32lo i) {b32hi i} := rfl

theorem candsb32_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb32 i) :
    c ∈ Set.Icc (b32lo i) (b32hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b32lo_le_b32hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b32lo_le_b32hi i, le_rfl⟩

theorem candsb32_ne (i : Fin 6) : (candsb32 i).Nonempty := ⟨b32lo i, by
  simp only [candsb32]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 33. -/
noncomputable def candsb33 : Fin 6 → Finset ℝ :=
  fun i => insert (b33lo i) {b33hi i}

theorem candsb33_eq (i : Fin 6) : candsb33 i = insert (b33lo i) {b33hi i} := rfl

theorem candsb33_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb33 i) :
    c ∈ Set.Icc (b33lo i) (b33hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b33lo_le_b33hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b33lo_le_b33hi i, le_rfl⟩

theorem candsb33_ne (i : Fin 6) : (candsb33 i).Nonempty := ⟨b33lo i, by
  simp only [candsb33]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 34. -/
noncomputable def candsb34 : Fin 6 → Finset ℝ :=
  fun i => insert (b34lo i) {b34hi i}

theorem candsb34_eq (i : Fin 6) : candsb34 i = insert (b34lo i) {b34hi i} := rfl

theorem candsb34_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb34 i) :
    c ∈ Set.Icc (b34lo i) (b34hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b34lo_le_b34hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b34lo_le_b34hi i, le_rfl⟩

theorem candsb34_ne (i : Fin 6) : (candsb34 i).Nonempty := ⟨b34lo i, by
  simp only [candsb34]
  exact Finset.mem_insert_self _ _⟩


/-- idx 101 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R101v_def (i : Fin 6) : R101 i = K101 i * (b22hi i - b22lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R101, K101, b22lo, b22hi]

/-- idx 101 chain: corner bound minus the grid rebate lower-bounds the margin (box 22; REBATE coordinates per KENV). -/

theorem chain_idx101 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b22lo i) (b22hi i))
        (fun t => f (Function.update y i t) - K101 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K101 i)
    (hR0 : ∀ i, 0 ≤ R101 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb22 j) → B101 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b22lo j) (b22hi j)) :
    B101 - ∑ j, R101 j ≤ f x :=
  final_bound candsb22 candsb22_ne hR0 candsb22_sub
    (fun i y hy => by
      rw [R101v_def i]
      exact hstep_of_shifted_concave (b22lo_le_b22hi i) (hK0 i)
        (hsl i) candsb22_eq y hy)
    hcorner x hx

/-- idx 102 chain: corner bound minus the grid rebate lower-bounds the margin (box 23; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx102 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => f (Function.update y i t) - K102 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K102 i)
    (hR0 : ∀ i, 0 ≤ R102 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B102 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b23lo j) (b23hi j)) :
    B102 - ∑ j, R102 j ≤ f x :=
  final_bound candsb23 candsb23_ne hR0 candsb23_sub
    (fun i y hy => hstep_of_shifted_concave (b23lo_le_b23hi i) (hK0 i)
      (hsl i) candsb23_eq y hy)
    hcorner x hx

/-- idx 103 chain: corner bound minus the grid rebate lower-bounds the margin (box 23; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx103 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => f (Function.update y i t) - K103 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K103 i)
    (hR0 : ∀ i, 0 ≤ R103 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B103 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b23lo j) (b23hi j)) :
    B103 - ∑ j, R103 j ≤ f x :=
  final_bound candsb23 candsb23_ne hR0 candsb23_sub
    (fun i y hy => hstep_of_shifted_concave (b23lo_le_b23hi i) (hK0 i)
      (hsl i) candsb23_eq y hy)
    hcorner x hx

/-- idx 104 chain: corner bound minus the grid rebate lower-bounds the margin (box 23; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx104 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => f (Function.update y i t) - K104 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K104 i)
    (hR0 : ∀ i, 0 ≤ R104 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B104 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b23lo j) (b23hi j)) :
    B104 - ∑ j, R104 j ≤ f x :=
  final_bound candsb23 candsb23_ne hR0 candsb23_sub
    (fun i y hy => hstep_of_shifted_concave (b23lo_le_b23hi i) (hK0 i)
      (hsl i) candsb23_eq y hy)
    hcorner x hx

/-- idx 106 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R106v_def (i : Fin 6) : R106 i = K106 i * (b24hi i - b24lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R106, K106, b24lo, b24hi]

/-- idx 106 chain: corner bound minus the grid rebate lower-bounds the margin (box 24; REBATE coordinates per KENV). -/

theorem chain_idx106 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b24lo i) (b24hi i))
        (fun t => f (Function.update y i t) - K106 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K106 i)
    (hR0 : ∀ i, 0 ≤ R106 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb24 j) → B106 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b24lo j) (b24hi j)) :
    B106 - ∑ j, R106 j ≤ f x :=
  final_bound candsb24 candsb24_ne hR0 candsb24_sub
    (fun i y hy => by
      rw [R106v_def i]
      exact hstep_of_shifted_concave (b24lo_le_b24hi i) (hK0 i)
        (hsl i) candsb24_eq y hy)
    hcorner x hx

/-- idx 107 chain: corner bound minus the grid rebate lower-bounds the margin (box 23; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx107 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => f (Function.update y i t) - K107 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K107 i)
    (hR0 : ∀ i, 0 ≤ R107 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B107 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b23lo j) (b23hi j)) :
    B107 - ∑ j, R107 j ≤ f x :=
  final_bound candsb23 candsb23_ne hR0 candsb23_sub
    (fun i y hy => hstep_of_shifted_concave (b23lo_le_b23hi i) (hK0 i)
      (hsl i) candsb23_eq y hy)
    hcorner x hx

/-- idx 108 chain: corner bound minus the grid rebate lower-bounds the margin (box 23; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx108 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => f (Function.update y i t) - K108 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K108 i)
    (hR0 : ∀ i, 0 ≤ R108 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B108 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b23lo j) (b23hi j)) :
    B108 - ∑ j, R108 j ≤ f x :=
  final_bound candsb23 candsb23_ne hR0 candsb23_sub
    (fun i y hy => hstep_of_shifted_concave (b23lo_le_b23hi i) (hK0 i)
      (hsl i) candsb23_eq y hy)
    hcorner x hx

/-- idx 109 chain: corner bound minus the grid rebate lower-bounds the margin (box 23; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx109 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => f (Function.update y i t) - K109 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K109 i)
    (hR0 : ∀ i, 0 ≤ R109 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B109 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b23lo j) (b23hi j)) :
    B109 - ∑ j, R109 j ≤ f x :=
  final_bound candsb23 candsb23_ne hR0 candsb23_sub
    (fun i y hy => hstep_of_shifted_concave (b23lo_le_b23hi i) (hK0 i)
      (hsl i) candsb23_eq y hy)
    hcorner x hx

/-- idx 111 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R111v_def (i : Fin 6) : R111 i = K111 i * (b25hi i - b25lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R111, K111, b25lo, b25hi]

/-- idx 111 chain: corner bound minus the grid rebate lower-bounds the margin (box 25; REBATE coordinates per KENV). -/

theorem chain_idx111 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b25lo i) (b25hi i))
        (fun t => f (Function.update y i t) - K111 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K111 i)
    (hR0 : ∀ i, 0 ≤ R111 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb25 j) → B111 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b25lo j) (b25hi j)) :
    B111 - ∑ j, R111 j ≤ f x :=
  final_bound candsb25 candsb25_ne hR0 candsb25_sub
    (fun i y hy => by
      rw [R111v_def i]
      exact hstep_of_shifted_concave (b25lo_le_b25hi i) (hK0 i)
        (hsl i) candsb25_eq y hy)
    hcorner x hx

/-- idx 112 chain: corner bound minus the grid rebate lower-bounds the margin (box 26; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx112 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => f (Function.update y i t) - K112 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K112 i)
    (hR0 : ∀ i, 0 ≤ R112 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B112 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b26lo j) (b26hi j)) :
    B112 - ∑ j, R112 j ≤ f x :=
  final_bound candsb26 candsb26_ne hR0 candsb26_sub
    (fun i y hy => hstep_of_shifted_concave (b26lo_le_b26hi i) (hK0 i)
      (hsl i) candsb26_eq y hy)
    hcorner x hx

/-- idx 113 chain: corner bound minus the grid rebate lower-bounds the margin (box 26; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx113 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => f (Function.update y i t) - K113 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K113 i)
    (hR0 : ∀ i, 0 ≤ R113 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B113 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b26lo j) (b26hi j)) :
    B113 - ∑ j, R113 j ≤ f x :=
  final_bound candsb26 candsb26_ne hR0 candsb26_sub
    (fun i y hy => hstep_of_shifted_concave (b26lo_le_b26hi i) (hK0 i)
      (hsl i) candsb26_eq y hy)
    hcorner x hx

/-- idx 114 chain: corner bound minus the grid rebate lower-bounds the margin (box 27; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx114 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b27lo i) (b27hi i))
        (fun t => f (Function.update y i t) - K114 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K114 i)
    (hR0 : ∀ i, 0 ≤ R114 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb27 j) → B114 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b27lo j) (b27hi j)) :
    B114 - ∑ j, R114 j ≤ f x :=
  final_bound candsb27 candsb27_ne hR0 candsb27_sub
    (fun i y hy => hstep_of_shifted_concave (b27lo_le_b27hi i) (hK0 i)
      (hsl i) candsb27_eq y hy)
    hcorner x hx

/-- idx 116 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R116v_def (i : Fin 6) : R116 i = K116 i * (b25hi i - b25lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R116, K116, b25lo, b25hi]

/-- idx 116 chain: corner bound minus the grid rebate lower-bounds the margin (box 25; REBATE coordinates per KENV). -/

theorem chain_idx116 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b25lo i) (b25hi i))
        (fun t => f (Function.update y i t) - K116 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K116 i)
    (hR0 : ∀ i, 0 ≤ R116 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb25 j) → B116 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b25lo j) (b25hi j)) :
    B116 - ∑ j, R116 j ≤ f x :=
  final_bound candsb25 candsb25_ne hR0 candsb25_sub
    (fun i y hy => by
      rw [R116v_def i]
      exact hstep_of_shifted_concave (b25lo_le_b25hi i) (hK0 i)
        (hsl i) candsb25_eq y hy)
    hcorner x hx

/-- idx 117 chain: corner bound minus the grid rebate lower-bounds the margin (box 26; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx117 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => f (Function.update y i t) - K117 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K117 i)
    (hR0 : ∀ i, 0 ≤ R117 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B117 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b26lo j) (b26hi j)) :
    B117 - ∑ j, R117 j ≤ f x :=
  final_bound candsb26 candsb26_ne hR0 candsb26_sub
    (fun i y hy => hstep_of_shifted_concave (b26lo_le_b26hi i) (hK0 i)
      (hsl i) candsb26_eq y hy)
    hcorner x hx

/-- idx 118 chain: corner bound minus the grid rebate lower-bounds the margin (box 27; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx118 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b27lo i) (b27hi i))
        (fun t => f (Function.update y i t) - K118 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K118 i)
    (hR0 : ∀ i, 0 ≤ R118 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb27 j) → B118 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b27lo j) (b27hi j)) :
    B118 - ∑ j, R118 j ≤ f x :=
  final_bound candsb27 candsb27_ne hR0 candsb27_sub
    (fun i y hy => hstep_of_shifted_concave (b27lo_le_b27hi i) (hK0 i)
      (hsl i) candsb27_eq y hy)
    hcorner x hx

/-- idx 119 chain: corner bound minus the grid rebate lower-bounds the margin (box 28; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx119 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => f (Function.update y i t) - K119 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K119 i)
    (hR0 : ∀ i, 0 ≤ R119 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B119 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b28lo j) (b28hi j)) :
    B119 - ∑ j, R119 j ≤ f x :=
  final_bound candsb28 candsb28_ne hR0 candsb28_sub
    (fun i y hy => hstep_of_shifted_concave (b28lo_le_b28hi i) (hK0 i)
      (hsl i) candsb28_eq y hy)
    hcorner x hx

/-- idx 121 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R121v_def (i : Fin 6) : R121 i = K121 i * (b25hi i - b25lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R121, K121, b25lo, b25hi]

/-- idx 121 chain: corner bound minus the grid rebate lower-bounds the margin (box 25; REBATE coordinates per KENV). -/

theorem chain_idx121 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b25lo i) (b25hi i))
        (fun t => f (Function.update y i t) - K121 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K121 i)
    (hR0 : ∀ i, 0 ≤ R121 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb25 j) → B121 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b25lo j) (b25hi j)) :
    B121 - ∑ j, R121 j ≤ f x :=
  final_bound candsb25 candsb25_ne hR0 candsb25_sub
    (fun i y hy => by
      rw [R121v_def i]
      exact hstep_of_shifted_concave (b25lo_le_b25hi i) (hK0 i)
        (hsl i) candsb25_eq y hy)
    hcorner x hx

/-- idx 122 chain: corner bound minus the grid rebate lower-bounds the margin (box 27; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx122 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b27lo i) (b27hi i))
        (fun t => f (Function.update y i t) - K122 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K122 i)
    (hR0 : ∀ i, 0 ≤ R122 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb27 j) → B122 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b27lo j) (b27hi j)) :
    B122 - ∑ j, R122 j ≤ f x :=
  final_bound candsb27 candsb27_ne hR0 candsb27_sub
    (fun i y hy => hstep_of_shifted_concave (b27lo_le_b27hi i) (hK0 i)
      (hsl i) candsb27_eq y hy)
    hcorner x hx

/-- idx 123 chain: corner bound minus the grid rebate lower-bounds the margin (box 28; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx123 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => f (Function.update y i t) - K123 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K123 i)
    (hR0 : ∀ i, 0 ≤ R123 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B123 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b28lo j) (b28hi j)) :
    B123 - ∑ j, R123 j ≤ f x :=
  final_bound candsb28 candsb28_ne hR0 candsb28_sub
    (fun i y hy => hstep_of_shifted_concave (b28lo_le_b28hi i) (hK0 i)
      (hsl i) candsb28_eq y hy)
    hcorner x hx

/-- idx 124 chain: corner bound minus the grid rebate lower-bounds the margin (box 28; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx124 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b28lo i) (b28hi i))
        (fun t => f (Function.update y i t) - K124 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K124 i)
    (hR0 : ∀ i, 0 ≤ R124 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb28 j) → B124 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b28lo j) (b28hi j)) :
    B124 - ∑ j, R124 j ≤ f x :=
  final_bound candsb28 candsb28_ne hR0 candsb28_sub
    (fun i y hy => hstep_of_shifted_concave (b28lo_le_b28hi i) (hK0 i)
      (hsl i) candsb28_eq y hy)
    hcorner x hx

/-- idx 126 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R126v_def (i : Fin 6) : R126 i = K126 i * (b29hi i - b29lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R126, K126, b29lo, b29hi]

/-- idx 126 chain: corner bound minus the grid rebate lower-bounds the margin (box 29; REBATE coordinates per KENV). -/

theorem chain_idx126 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b29lo i) (b29hi i))
        (fun t => f (Function.update y i t) - K126 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K126 i)
    (hR0 : ∀ i, 0 ≤ R126 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb29 j) → B126 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b29lo j) (b29hi j)) :
    B126 - ∑ j, R126 j ≤ f x :=
  final_bound candsb29 candsb29_ne hR0 candsb29_sub
    (fun i y hy => by
      rw [R126v_def i]
      exact hstep_of_shifted_concave (b29lo_le_b29hi i) (hK0 i)
        (hsl i) candsb29_eq y hy)
    hcorner x hx

/-- idx 127 chain: corner bound minus the grid rebate lower-bounds the margin (box 30; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx127 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b30lo i) (b30hi i))
        (fun t => f (Function.update y i t) - K127 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K127 i)
    (hR0 : ∀ i, 0 ≤ R127 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb30 j) → B127 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b30lo j) (b30hi j)) :
    B127 - ∑ j, R127 j ≤ f x :=
  final_bound candsb30 candsb30_ne hR0 candsb30_sub
    (fun i y hy => hstep_of_shifted_concave (b30lo_le_b30hi i) (hK0 i)
      (hsl i) candsb30_eq y hy)
    hcorner x hx

/-- idx 128 chain: corner bound minus the grid rebate lower-bounds the margin (box 30; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx128 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b30lo i) (b30hi i))
        (fun t => f (Function.update y i t) - K128 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K128 i)
    (hR0 : ∀ i, 0 ≤ R128 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb30 j) → B128 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b30lo j) (b30hi j)) :
    B128 - ∑ j, R128 j ≤ f x :=
  final_bound candsb30 candsb30_ne hR0 candsb30_sub
    (fun i y hy => hstep_of_shifted_concave (b30lo_le_b30hi i) (hK0 i)
      (hsl i) candsb30_eq y hy)
    hcorner x hx

/-- idx 129 chain: corner bound minus the grid rebate lower-bounds the margin (box 30; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx129 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b30lo i) (b30hi i))
        (fun t => f (Function.update y i t) - K129 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K129 i)
    (hR0 : ∀ i, 0 ≤ R129 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb30 j) → B129 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b30lo j) (b30hi j)) :
    B129 - ∑ j, R129 j ≤ f x :=
  final_bound candsb30 candsb30_ne hR0 candsb30_sub
    (fun i y hy => hstep_of_shifted_concave (b30lo_le_b30hi i) (hK0 i)
      (hsl i) candsb30_eq y hy)
    hcorner x hx

/-- idx 131 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R131v_def (i : Fin 6) : R131 i = K131 i * (b31hi i - b31lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R131, K131, b31lo, b31hi]

/-- idx 131 chain: corner bound minus the grid rebate lower-bounds the margin (box 31; REBATE coordinates per KENV). -/

theorem chain_idx131 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b31lo i) (b31hi i))
        (fun t => f (Function.update y i t) - K131 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K131 i)
    (hR0 : ∀ i, 0 ≤ R131 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb31 j) → B131 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b31lo j) (b31hi j)) :
    B131 - ∑ j, R131 j ≤ f x :=
  final_bound candsb31 candsb31_ne hR0 candsb31_sub
    (fun i y hy => by
      rw [R131v_def i]
      exact hstep_of_shifted_concave (b31lo_le_b31hi i) (hK0 i)
        (hsl i) candsb31_eq y hy)
    hcorner x hx

/-- idx 132 chain: corner bound minus the grid rebate lower-bounds the margin (box 32; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx132 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b32lo i) (b32hi i))
        (fun t => f (Function.update y i t) - K132 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K132 i)
    (hR0 : ∀ i, 0 ≤ R132 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb32 j) → B132 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b32lo j) (b32hi j)) :
    B132 - ∑ j, R132 j ≤ f x :=
  final_bound candsb32 candsb32_ne hR0 candsb32_sub
    (fun i y hy => hstep_of_shifted_concave (b32lo_le_b32hi i) (hK0 i)
      (hsl i) candsb32_eq y hy)
    hcorner x hx

/-- idx 133 chain: corner bound minus the grid rebate lower-bounds the margin (box 32; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx133 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b32lo i) (b32hi i))
        (fun t => f (Function.update y i t) - K133 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K133 i)
    (hR0 : ∀ i, 0 ≤ R133 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb32 j) → B133 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b32lo j) (b32hi j)) :
    B133 - ∑ j, R133 j ≤ f x :=
  final_bound candsb32 candsb32_ne hR0 candsb32_sub
    (fun i y hy => hstep_of_shifted_concave (b32lo_le_b32hi i) (hK0 i)
      (hsl i) candsb32_eq y hy)
    hcorner x hx

/-- idx 134 chain: corner bound minus the grid rebate lower-bounds the margin (box 33; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx134 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b33lo i) (b33hi i))
        (fun t => f (Function.update y i t) - K134 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K134 i)
    (hR0 : ∀ i, 0 ≤ R134 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb33 j) → B134 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b33lo j) (b33hi j)) :
    B134 - ∑ j, R134 j ≤ f x :=
  final_bound candsb33 candsb33_ne hR0 candsb33_sub
    (fun i y hy => hstep_of_shifted_concave (b33lo_le_b33hi i) (hK0 i)
      (hsl i) candsb33_eq y hy)
    hcorner x hx

/-- idx 136 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R136v_def (i : Fin 6) : R136 i = K136 i * (b31hi i - b31lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R136, K136, b31lo, b31hi]

/-- idx 136 chain: corner bound minus the grid rebate lower-bounds the margin (box 31; REBATE coordinates per KENV). -/

theorem chain_idx136 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b31lo i) (b31hi i))
        (fun t => f (Function.update y i t) - K136 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K136 i)
    (hR0 : ∀ i, 0 ≤ R136 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb31 j) → B136 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b31lo j) (b31hi j)) :
    B136 - ∑ j, R136 j ≤ f x :=
  final_bound candsb31 candsb31_ne hR0 candsb31_sub
    (fun i y hy => by
      rw [R136v_def i]
      exact hstep_of_shifted_concave (b31lo_le_b31hi i) (hK0 i)
        (hsl i) candsb31_eq y hy)
    hcorner x hx

/-- idx 137 chain: corner bound minus the grid rebate lower-bounds the margin (box 32; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx137 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b32lo i) (b32hi i))
        (fun t => f (Function.update y i t) - K137 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K137 i)
    (hR0 : ∀ i, 0 ≤ R137 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb32 j) → B137 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b32lo j) (b32hi j)) :
    B137 - ∑ j, R137 j ≤ f x :=
  final_bound candsb32 candsb32_ne hR0 candsb32_sub
    (fun i y hy => hstep_of_shifted_concave (b32lo_le_b32hi i) (hK0 i)
      (hsl i) candsb32_eq y hy)
    hcorner x hx

/-- idx 138 chain: corner bound minus the grid rebate lower-bounds the margin (box 33; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx138 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b33lo i) (b33hi i))
        (fun t => f (Function.update y i t) - K138 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K138 i)
    (hR0 : ∀ i, 0 ≤ R138 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb33 j) → B138 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b33lo j) (b33hi j)) :
    B138 - ∑ j, R138 j ≤ f x :=
  final_bound candsb33 candsb33_ne hR0 candsb33_sub
    (fun i y hy => hstep_of_shifted_concave (b33lo_le_b33hi i) (hK0 i)
      (hsl i) candsb33_eq y hy)
    hcorner x hx

/-- idx 139 chain: corner bound minus the grid rebate lower-bounds the margin (box 34; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx139 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b34lo i) (b34hi i))
        (fun t => f (Function.update y i t) - K139 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K139 i)
    (hR0 : ∀ i, 0 ≤ R139 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb34 j) → B139 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b34lo j) (b34hi j)) :
    B139 - ∑ j, R139 j ≤ f x :=
  final_bound candsb34 candsb34_ne hR0 candsb34_sub
    (fun i y hy => hstep_of_shifted_concave (b34lo_le_b34hi i) (hK0 i)
      (hsl i) candsb34_eq y hy)
    hcorner x hx

/-! ### Axiom audit -/

#print axioms chain_idx101

#print axioms chain_idx102

#print axioms chain_idx103

#print axioms chain_idx104

#print axioms chain_idx106

#print axioms chain_idx107

#print axioms chain_idx108

#print axioms chain_idx109

#print axioms chain_idx111

#print axioms chain_idx112

#print axioms chain_idx113

#print axioms chain_idx114

#print axioms chain_idx116

#print axioms chain_idx117

#print axioms chain_idx118

#print axioms chain_idx119

#print axioms chain_idx121

#print axioms chain_idx122

#print axioms chain_idx123

#print axioms chain_idx124

#print axioms chain_idx126

#print axioms chain_idx127

#print axioms chain_idx128

#print axioms chain_idx129

#print axioms chain_idx131

#print axioms chain_idx132

#print axioms chain_idx133

#print axioms chain_idx134

#print axioms chain_idx136

#print axioms chain_idx137

#print axioms chain_idx138

#print axioms chain_idx139

end Kepler.Text
