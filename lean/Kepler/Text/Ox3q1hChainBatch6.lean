/-
Ox3q1hChainBatch6: S3 mass-production batch 6 (40 conjuncts, idx 181-229, boxes 10-47).
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
import Kepler.Text.Ox3q1hChainBatch5

open Set Filter Topology

namespace Kepler.Text

/-- Box 42 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b42lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, (4927/2000), 2, 2]

/-- Box 42 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b42hi : Fin 6 → ℝ := ![(6627/2500), (15397/6250), (15397/6250), (63/25), (15397/6250), (15397/6250)]

theorem b42lo_le_b42hi (i : Fin 6) : b42lo i ≤ b42hi i := by
  fin_cases i
  all_goals norm_num [b42lo, b42hi]

/-- Box 43 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b43lo : Fin 6 → ℝ := ![(26181/10000), 2, 2, (4927/2000), 2, 2]

/-- Box 43 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b43hi : Fin 6 → ℝ := ![(6627/2500), (15397/6250), (15397/6250), (63/25), (15397/6250), (15397/6250)]

theorem b43lo_le_b43hi (i : Fin 6) : b43lo i ≤ b43hi i := by
  fin_cases i
  all_goals norm_num [b43lo, b43hi]

/-- Box 44 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b44lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, (4927/2000), 2, 2]

/-- Box 44 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b44hi : Fin 6 → ℝ := ![(26181/10000), (15397/6250), (15397/6250), (63/25), (15397/6250), (15397/6250)]

theorem b44lo_le_b44hi (i : Fin 6) : b44lo i ≤ b44hi i := by
  fin_cases i
  all_goals norm_num [b44lo, b44hi]

/-- Box 45 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b45lo : Fin 6 → ℝ := ![(10407/4000), 2, 2, (4927/2000), 2, 2]

/-- Box 45 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b45hi : Fin 6 → ℝ := ![(26181/10000), (15397/6250), (15397/6250), (63/25), (15397/6250), (15397/6250)]

theorem b45lo_le_b45hi (i : Fin 6) : b45lo i ≤ b45hi i := by
  fin_cases i
  all_goals norm_num [b45lo, b45hi]

/-- Box 46 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b46lo : Fin 6 → ℝ := ![(12927/5000), 2, 2, (4927/2000), 2, 2]

/-- Box 46 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b46hi : Fin 6 → ℝ := ![(10407/4000), (15397/6250), (15397/6250), (63/25), (15397/6250), (15397/6250)]

theorem b46lo_le_b46hi (i : Fin 6) : b46lo i ≤ b46hi i := by
  fin_cases i
  all_goals norm_num [b46lo, b46hi]

/-- Box 47 lower corner (BOXES_EXACT exact fractions). -/
noncomputable def b47lo : Fin 6 → ℝ := ![(63/25), 2, 2, (4927/2000), 2, 2]

/-- Box 47 upper corner (BOXES_EXACT exact fractions). -/
noncomputable def b47hi : Fin 6 → ℝ := ![(12927/5000), (15397/6250), (15397/6250), (63/25), (15397/6250), (15397/6250)]

theorem b47lo_le_b47hi (i : Fin 6) : b47lo i ≤ b47hi i := by
  fin_cases i
  all_goals norm_num [b47lo, b47hi]


/-- idx 181 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K181 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (597847069595/1099511627776), (0/1), (0/1)]

/-- idx 181 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B181 : ℝ := (102347159822386772423857/22517998136852480000000000)

/-- idx 181 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R181 : Fin 6 → ℝ := ![0, 0, 0, (1526781846331711/7036874417766400000), 0, 0]

/-- idx 182 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K182 : Fin 6 → ℝ := fun _ => 0

/-- idx 182 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B182 : ℝ := (4090146674144735169433219/900719925474099200000000000)

/-- idx 182 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R182 : Fin 6 → ℝ :=
  fun j => K182 j * (b10hi j - b10lo j) ^ 2 / 8

/-- idx 183 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K183 : Fin 6 → ℝ := fun _ => 0

/-- idx 183 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B183 : ℝ := (655264855832160929357531/144115188075855872000000000)

/-- idx 183 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R183 : Fin 6 → ℝ :=
  fun j => K183 j * (b10hi j - b10lo j) ^ 2 / 8

/-- idx 184 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K184 : Fin 6 → ℝ := fun _ => 0

/-- idx 184 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B184 : ℝ := (818148234235347152866593/180143985094819840000000000)

/-- idx 184 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R184 : Fin 6 → ℝ :=
  fun j => K184 j * (b11hi j - b11lo j) ^ 2 / 8

/-- idx 186 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K186 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (597847069595/1099511627776), (0/1), (0/1)]

/-- idx 186 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B186 : ℝ := (102347159822386772423857/22517998136852480000000000)

/-- idx 186 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R186 : Fin 6 → ℝ := ![0, 0, 0, (1526781846331711/7036874417766400000), 0, 0]

/-- idx 187 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K187 : Fin 6 → ℝ := fun _ => 0

/-- idx 187 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B187 : ℝ := (654832510267933361741531/144115188075855872000000000)

/-- idx 187 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R187 : Fin 6 → ℝ :=
  fun j => K187 j * (b10hi j - b10lo j) ^ 2 / 8

/-- idx 188 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K188 : Fin 6 → ℝ := fun _ => 0

/-- idx 188 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B188 : ℝ := (818688666190631612386593/180143985094819840000000000)

/-- idx 188 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R188 : Fin 6 → ℝ :=
  fun j => K188 j * (b11hi j - b11lo j) ^ 2 / 8

/-- idx 189 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K189 : Fin 6 → ℝ := fun _ => 0

/-- idx 189 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B189 : ℝ := (4090146674144735169433219/900719925474099200000000000)

/-- idx 189 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R189 : Fin 6 → ℝ :=
  fun j => K189 j * (b12hi j - b12lo j) ^ 2 / 8

/-- idx 191 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K191 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (597847069595/1099511627776), (0/1), (0/1)]

/-- idx 191 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B191 : ℝ := (102347159822386772423857/22517998136852480000000000)

/-- idx 191 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R191 : Fin 6 → ℝ := ![0, 0, 0, (1526781846331711/7036874417766400000), 0, 0]

/-- idx 192 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K192 : Fin 6 → ℝ := fun _ => 0

/-- idx 192 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B192 : ℝ := (818148234235347152866593/180143985094819840000000000)

/-- idx 192 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R192 : Fin 6 → ℝ :=
  fun j => K192 j * (b11hi j - b11lo j) ^ 2 / 8

/-- idx 193 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K193 : Fin 6 → ℝ := fun _ => 0

/-- idx 193 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B193 : ℝ := (655264855832160929357531/144115188075855872000000000)

/-- idx 193 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R193 : Fin 6 → ℝ :=
  fun j => K193 j * (b12hi j - b12lo j) ^ 2 / 8

/-- idx 194 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K194 : Fin 6 → ℝ := fun _ => 0

/-- idx 194 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B194 : ℝ := (4090146674144735169433219/900719925474099200000000000)

/-- idx 194 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R194 : Fin 6 → ℝ :=
  fun j => K194 j * (b12hi j - b12lo j) ^ 2 / 8

/-- idx 196 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K196 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (295134787705/549755813888), (0/1), (0/1)]

/-- idx 196 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B196 : ℝ := (316746207853779033927209/360287970189639680000000000)

/-- idx 196 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R196 : Fin 6 → ℝ := ![0, 0, 0, (753715220841029/3518437208883200000), 0, 0]

/-- idx 197 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K197 : Fin 6 → ℝ := fun _ => 0

/-- idx 197 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B197 : ℝ := (158925348430507312448539/180143985094819840000000000)

/-- idx 197 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R197 : Fin 6 → ℝ :=
  fun j => K197 j * (b15hi j - b15lo j) ^ 2 / 8

/-- idx 198 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K198 : Fin 6 → ℝ := fun _ => 0

/-- idx 198 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B198 : ℝ := (79728000761902369720047/90071992547409920000000000)

/-- idx 198 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R198 : Fin 6 → ℝ :=
  fun j => K198 j * (b15hi j - b15lo j) ^ 2 / 8

/-- idx 199 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K199 : Fin 6 → ℝ := fun _ => 0

/-- idx 199 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B199 : ℝ := (79728000761902369720047/90071992547409920000000000)

/-- idx 199 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R199 : Fin 6 → ℝ :=
  fun j => K199 j * (b15hi j - b15lo j) ^ 2 / 8

/-- idx 201 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K201 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (574081292379/1099511627776), (0/1), (0/1)]

/-- idx 201 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B201 : ℝ := (177643353933028257987441/90071992547409920000000000)

/-- idx 201 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R201 : Fin 6 → ℝ := ![0, 0, 0, (7330444022387451/35184372088832000000), 0, 0]

/-- idx 202 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K202 : Fin 6 → ℝ := fun _ => 0

/-- idx 202 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B202 : ℝ := (1775586001116581819034139/900719925474099200000000000)

/-- idx 202 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R202 : Fin 6 → ℝ :=
  fun j => K202 j * (b17hi j - b17lo j) ^ 2 / 8

/-- idx 203 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K203 : Fin 6 → ℝ := fun _ => 0

/-- idx 203 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B203 : ℝ := (356291706314003806959607/180143985094819840000000000)

/-- idx 203 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R203 : Fin 6 → ℝ :=
  fun j => K203 j * (b17hi j - b17lo j) ^ 2 / 8

/-- idx 204 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K204 : Fin 6 → ℝ := fun _ => 0

/-- idx 204 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B204 : ℝ := (35526606265659279942811/18014398509481984000000000)

/-- idx 204 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R204 : Fin 6 → ℝ :=
  fun j => K204 j * (b18hi j - b18lo j) ^ 2 / 8

/-- idx 206 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K206 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (574081292379/1099511627776), (0/1), (0/1)]

/-- idx 206 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B206 : ℝ := (177733425925575667907441/90071992547409920000000000)

/-- idx 206 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R206 : Fin 6 → ℝ := ![0, 0, 0, (7330444022387451/35184372088832000000), 0, 0]

/-- idx 207 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K207 : Fin 6 → ℝ := fun _ => 0

/-- idx 207 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B207 : ℝ := (355390986388529707759607/180143985094819840000000000)

/-- idx 207 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R207 : Fin 6 → ℝ :=
  fun j => K207 j * (b17hi j - b17lo j) ^ 2 / 8

/-- idx 208 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K208 : Fin 6 → ℝ := fun _ => 0

/-- idx 208 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B208 : ℝ := (222367424337945947488883/112589990684262400000000000)

/-- idx 208 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R208 : Fin 6 → ℝ :=
  fun j => K208 j * (b18hi j - b18lo j) ^ 2 / 8

/-- idx 209 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K209 : Fin 6 → ℝ := fun _ => 0

/-- idx 209 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B209 : ℝ := (355390986388529707759607/180143985094819840000000000)

/-- idx 209 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R209 : Fin 6 → ℝ :=
  fun j => K209 j * (b19hi j - b19lo j) ^ 2 / 8

/-- idx 211 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K211 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (574081292379/1099511627776), (0/1), (0/1)]

/-- idx 211 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B211 : ℝ := (13857276402764814930245538781/7036874417766400000000000000000)

/-- idx 211 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R211 : Fin 6 → ℝ := ![0, 0, 0, (7330444022387451/35184372088832000000), 0, 0]

/-- idx 212 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K212 : Fin 6 → ℝ := fun _ => 0

/-- idx 212 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B212 : ℝ := (35580649461187725894811/18014398509481984000000000)

/-- idx 212 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R212 : Fin 6 → ℝ :=
  fun j => K212 j * (b18hi j - b18lo j) ^ 2 / 8

/-- idx 213 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K213 : Fin 6 → ℝ := fun _ => 0

/-- idx 213 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B213 : ℝ := (1775586001116581819034139/900719925474099200000000000)

/-- idx 213 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R213 : Fin 6 → ℝ :=
  fun j => K213 j * (b19hi j - b19lo j) ^ 2 / 8

/-- idx 214 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K214 : Fin 6 → ℝ := fun _ => 0

/-- idx 214 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B214 : ℝ := (356291706314003806959607/180143985094819840000000000)

/-- idx 214 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R214 : Fin 6 → ℝ :=
  fun j => K214 j * (b19hi j - b19lo j) ^ 2 / 8

/-- idx 216 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K216 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (286179567305/549755813888), (0/1), (0/1)]

/-- idx 216 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B216 : ℝ := (234908646216233356851499/720575940379279360000000000)

/-- idx 216 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R216 : Fin 6 → ℝ := ![0, 0, 0, (730845378983509/3518437208883200000), 0, 0]

/-- idx 217 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K217 : Fin 6 → ℝ := fun _ => 0

/-- idx 217 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B217 : ℝ := (295631055591770941384851/900719925474099200000000000)

/-- idx 217 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R217 : Fin 6 → ℝ :=
  fun j => K217 j * (b21hi j - b21lo j) ^ 2 / 8

/-- idx 218 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K218 : Fin 6 → ℝ := fun _ => 0

/-- idx 218 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B218 : ℝ := (23734450474249571838381/72057594037927936000000000)

/-- idx 218 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R218 : Fin 6 → ℝ :=
  fun j => K218 j * (b21hi j - b21lo j) ^ 2 / 8

/-- idx 219 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K219 : Fin 6 → ℝ := fun _ => 0

/-- idx 219 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B219 : ℝ := (295631055591770941384851/900719925474099200000000000)

/-- idx 219 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R219 : Fin 6 → ℝ :=
  fun j => K219 j * (b21hi j - b21lo j) ^ 2 / 8

/-- idx 221 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K221 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (545837904963/1099511627776), (0/1), (0/1)]

/-- idx 221 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B221 : ℝ := (64068616357792110805867/72057594037927936000000000)

/-- idx 221 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R221 : Fin 6 → ℝ := ![0, 0, 0, (6969804208472547/35184372088832000000), 0, 0]

/-- idx 222 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K222 : Fin 6 → ℝ := fun _ => 0

/-- idx 222 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B222 : ℝ := (63491846600753696803367/72057594037927936000000000)

/-- idx 222 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R222 : Fin 6 → ℝ :=
  fun j => K222 j * (b23hi j - b23lo j) ^ 2 / 8

/-- idx 223 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K223 : Fin 6 → ℝ := fun _ => 0

/-- idx 223 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B223 : ℝ := (798552523678705351767281/900719925474099200000000000)

/-- idx 223 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R223 : Fin 6 → ℝ :=
  fun j => K223 j * (b23hi j - b23lo j) ^ 2 / 8

/-- idx 224 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K224 : Fin 6 → ℝ := fun _ => 0

/-- idx 224 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B224 : ℝ := (63491846600753696803367/72057594037927936000000000)

/-- idx 224 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R224 : Fin 6 → ℝ :=
  fun j => K224 j * (b23hi j - b23lo j) ^ 2 / 8

/-- idx 226 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K226 : Fin 6 → ℝ := ![(0/1), (0/1), (0/1), (286954538301/549755813888), (0/1), (0/1)]

/-- idx 226 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B226 : ℝ := (95474929009721561119337/72057594037927936000000000)

/-- idx 226 per-coordinate grid rebates (KENV R_i_exact). -/
noncomputable def R226 : Fin 6 → ℝ := ![0, 0, 0, (3664122499565469/17592186044416000000), 0, 0]

/-- idx 227 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K227 : Fin 6 → ℝ := fun _ => 0

/-- idx 227 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B227 : ℝ := (9571791836237643399681/7205759403792793600000000)

/-- idx 227 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R227 : Fin 6 → ℝ :=
  fun j => K227 j * (b26hi j - b26lo j) ^ 2 / 8

/-- idx 228 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K228 : Fin 6 → ℝ := fun _ => 0

/-- idx 228 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B228 : ℝ := (4768951385158985762815491/3602879701896396800000000000)

/-- idx 228 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R228 : Fin 6 → ℝ :=
  fun j => K228 j * (b26hi j - b26lo j) ^ 2 / 8

/-- idx 229 per-coordinate curvature bounds (KENV K_dyadic exact). -/
noncomputable def K229 : Fin 6 → ℝ := fun _ => 0

/-- idx 229 corner-table bound (CONJ_TABLE exact). -/
noncomputable def B229 : ℝ := (9571791836237643399681/7205759403792793600000000)

/-- idx 229 grid rebates R_j = K_j·W_j²/8 (ALL-CONCAVE, K = 0; direct form). -/
noncomputable def R229 : Fin 6 → ℝ :=
  fun j => K229 j * (b26hi j - b26lo j) ^ 2 / 8


/-- The unsplit two-corner grid of box 42. -/
noncomputable def candsb42 : Fin 6 → Finset ℝ :=
  fun i => insert (b42lo i) {b42hi i}

theorem candsb42_eq (i : Fin 6) : candsb42 i = insert (b42lo i) {b42hi i} := rfl

theorem candsb42_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb42 i) :
    c ∈ Set.Icc (b42lo i) (b42hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b42lo_le_b42hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b42lo_le_b42hi i, le_rfl⟩

theorem candsb42_ne (i : Fin 6) : (candsb42 i).Nonempty := ⟨b42lo i, by
  simp only [candsb42]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 43. -/
noncomputable def candsb43 : Fin 6 → Finset ℝ :=
  fun i => insert (b43lo i) {b43hi i}

theorem candsb43_eq (i : Fin 6) : candsb43 i = insert (b43lo i) {b43hi i} := rfl

theorem candsb43_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb43 i) :
    c ∈ Set.Icc (b43lo i) (b43hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b43lo_le_b43hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b43lo_le_b43hi i, le_rfl⟩

theorem candsb43_ne (i : Fin 6) : (candsb43 i).Nonempty := ⟨b43lo i, by
  simp only [candsb43]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 44. -/
noncomputable def candsb44 : Fin 6 → Finset ℝ :=
  fun i => insert (b44lo i) {b44hi i}

theorem candsb44_eq (i : Fin 6) : candsb44 i = insert (b44lo i) {b44hi i} := rfl

theorem candsb44_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb44 i) :
    c ∈ Set.Icc (b44lo i) (b44hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b44lo_le_b44hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b44lo_le_b44hi i, le_rfl⟩

theorem candsb44_ne (i : Fin 6) : (candsb44 i).Nonempty := ⟨b44lo i, by
  simp only [candsb44]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 45. -/
noncomputable def candsb45 : Fin 6 → Finset ℝ :=
  fun i => insert (b45lo i) {b45hi i}

theorem candsb45_eq (i : Fin 6) : candsb45 i = insert (b45lo i) {b45hi i} := rfl

theorem candsb45_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb45 i) :
    c ∈ Set.Icc (b45lo i) (b45hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b45lo_le_b45hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b45lo_le_b45hi i, le_rfl⟩

theorem candsb45_ne (i : Fin 6) : (candsb45 i).Nonempty := ⟨b45lo i, by
  simp only [candsb45]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 46. -/
noncomputable def candsb46 : Fin 6 → Finset ℝ :=
  fun i => insert (b46lo i) {b46hi i}

theorem candsb46_eq (i : Fin 6) : candsb46 i = insert (b46lo i) {b46hi i} := rfl

theorem candsb46_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb46 i) :
    c ∈ Set.Icc (b46lo i) (b46hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b46lo_le_b46hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b46lo_le_b46hi i, le_rfl⟩

theorem candsb46_ne (i : Fin 6) : (candsb46 i).Nonempty := ⟨b46lo i, by
  simp only [candsb46]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 47. -/
noncomputable def candsb47 : Fin 6 → Finset ℝ :=
  fun i => insert (b47lo i) {b47hi i}

theorem candsb47_eq (i : Fin 6) : candsb47 i = insert (b47lo i) {b47hi i} := rfl

theorem candsb47_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb47 i) :
    c ∈ Set.Icc (b47lo i) (b47hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b47lo_le_b47hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b47lo_le_b47hi i, le_rfl⟩

theorem candsb47_ne (i : Fin 6) : (candsb47 i).Nonempty := ⟨b47lo i, by
  simp only [candsb47]
  exact Finset.mem_insert_self _ _⟩


/-- idx 181 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R181v_def (i : Fin 6) : R181 i = K181 i * (b42hi i - b42lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R181, K181, b42lo, b42hi]

/-- idx 181 chain: corner bound minus the grid rebate lower-bounds the margin (box 42; REBATE coordinates per KENV). -/

theorem chain_idx181 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b42lo j) (b42hi j)) →
      ConcaveOn ℝ (Set.Icc (b42lo i) (b42hi i))
        (fun t => f (Function.update y i t) - K181 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K181 i)
    (hR0 : ∀ i, 0 ≤ R181 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb42 j) → B181 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b42lo j) (b42hi j)) :
    B181 - ∑ j, R181 j ≤ f x :=
  final_bound candsb42 candsb42_ne hR0 candsb42_sub
    (fun i y hy => by
      rw [R181v_def i]
      exact hstep_of_shifted_concave_box (b42lo_le_b42hi i) (hK0 i)
        hsl candsb42_eq y hy)
    hcorner x hx

/-- idx 182 chain: corner bound minus the grid rebate lower-bounds the margin (box 10; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx182 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b10lo j) (b10hi j)) →
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => f (Function.update y i t) - K182 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K182 i)
    (hR0 : ∀ i, 0 ≤ R182 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B182 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b10lo j) (b10hi j)) :
    B182 - ∑ j, R182 j ≤ f x :=
  final_bound candsb10 candsb10_ne hR0 candsb10_sub
    (fun i y hy => hstep_of_shifted_concave_box (b10lo_le_b10hi i) (hK0 i)
      hsl candsb10_eq y hy)
    hcorner x hx

/-- idx 183 chain: corner bound minus the grid rebate lower-bounds the margin (box 10; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx183 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b10lo j) (b10hi j)) →
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => f (Function.update y i t) - K183 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K183 i)
    (hR0 : ∀ i, 0 ≤ R183 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B183 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b10lo j) (b10hi j)) :
    B183 - ∑ j, R183 j ≤ f x :=
  final_bound candsb10 candsb10_ne hR0 candsb10_sub
    (fun i y hy => hstep_of_shifted_concave_box (b10lo_le_b10hi i) (hK0 i)
      hsl candsb10_eq y hy)
    hcorner x hx

/-- idx 184 chain: corner bound minus the grid rebate lower-bounds the margin (box 11; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx184 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b11lo j) (b11hi j)) →
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => f (Function.update y i t) - K184 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K184 i)
    (hR0 : ∀ i, 0 ≤ R184 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B184 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b11lo j) (b11hi j)) :
    B184 - ∑ j, R184 j ≤ f x :=
  final_bound candsb11 candsb11_ne hR0 candsb11_sub
    (fun i y hy => hstep_of_shifted_concave_box (b11lo_le_b11hi i) (hK0 i)
      hsl candsb11_eq y hy)
    hcorner x hx

/-- idx 186 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R186v_def (i : Fin 6) : R186 i = K186 i * (b42hi i - b42lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R186, K186, b42lo, b42hi]

/-- idx 186 chain: corner bound minus the grid rebate lower-bounds the margin (box 42; REBATE coordinates per KENV). -/

theorem chain_idx186 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b42lo j) (b42hi j)) →
      ConcaveOn ℝ (Set.Icc (b42lo i) (b42hi i))
        (fun t => f (Function.update y i t) - K186 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K186 i)
    (hR0 : ∀ i, 0 ≤ R186 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb42 j) → B186 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b42lo j) (b42hi j)) :
    B186 - ∑ j, R186 j ≤ f x :=
  final_bound candsb42 candsb42_ne hR0 candsb42_sub
    (fun i y hy => by
      rw [R186v_def i]
      exact hstep_of_shifted_concave_box (b42lo_le_b42hi i) (hK0 i)
        hsl candsb42_eq y hy)
    hcorner x hx

/-- idx 187 chain: corner bound minus the grid rebate lower-bounds the margin (box 10; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx187 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b10lo j) (b10hi j)) →
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => f (Function.update y i t) - K187 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K187 i)
    (hR0 : ∀ i, 0 ≤ R187 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B187 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b10lo j) (b10hi j)) :
    B187 - ∑ j, R187 j ≤ f x :=
  final_bound candsb10 candsb10_ne hR0 candsb10_sub
    (fun i y hy => hstep_of_shifted_concave_box (b10lo_le_b10hi i) (hK0 i)
      hsl candsb10_eq y hy)
    hcorner x hx

/-- idx 188 chain: corner bound minus the grid rebate lower-bounds the margin (box 11; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx188 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b11lo j) (b11hi j)) →
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => f (Function.update y i t) - K188 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K188 i)
    (hR0 : ∀ i, 0 ≤ R188 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B188 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b11lo j) (b11hi j)) :
    B188 - ∑ j, R188 j ≤ f x :=
  final_bound candsb11 candsb11_ne hR0 candsb11_sub
    (fun i y hy => hstep_of_shifted_concave_box (b11lo_le_b11hi i) (hK0 i)
      hsl candsb11_eq y hy)
    hcorner x hx

/-- idx 189 chain: corner bound minus the grid rebate lower-bounds the margin (box 12; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx189 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b12lo j) (b12hi j)) →
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => f (Function.update y i t) - K189 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K189 i)
    (hR0 : ∀ i, 0 ≤ R189 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B189 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b12lo j) (b12hi j)) :
    B189 - ∑ j, R189 j ≤ f x :=
  final_bound candsb12 candsb12_ne hR0 candsb12_sub
    (fun i y hy => hstep_of_shifted_concave_box (b12lo_le_b12hi i) (hK0 i)
      hsl candsb12_eq y hy)
    hcorner x hx

/-- idx 191 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R191v_def (i : Fin 6) : R191 i = K191 i * (b42hi i - b42lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R191, K191, b42lo, b42hi]

/-- idx 191 chain: corner bound minus the grid rebate lower-bounds the margin (box 42; REBATE coordinates per KENV). -/

theorem chain_idx191 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b42lo j) (b42hi j)) →
      ConcaveOn ℝ (Set.Icc (b42lo i) (b42hi i))
        (fun t => f (Function.update y i t) - K191 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K191 i)
    (hR0 : ∀ i, 0 ≤ R191 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb42 j) → B191 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b42lo j) (b42hi j)) :
    B191 - ∑ j, R191 j ≤ f x :=
  final_bound candsb42 candsb42_ne hR0 candsb42_sub
    (fun i y hy => by
      rw [R191v_def i]
      exact hstep_of_shifted_concave_box (b42lo_le_b42hi i) (hK0 i)
        hsl candsb42_eq y hy)
    hcorner x hx

/-- idx 192 chain: corner bound minus the grid rebate lower-bounds the margin (box 11; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx192 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b11lo j) (b11hi j)) →
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => f (Function.update y i t) - K192 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K192 i)
    (hR0 : ∀ i, 0 ≤ R192 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B192 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b11lo j) (b11hi j)) :
    B192 - ∑ j, R192 j ≤ f x :=
  final_bound candsb11 candsb11_ne hR0 candsb11_sub
    (fun i y hy => hstep_of_shifted_concave_box (b11lo_le_b11hi i) (hK0 i)
      hsl candsb11_eq y hy)
    hcorner x hx

/-- idx 193 chain: corner bound minus the grid rebate lower-bounds the margin (box 12; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx193 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b12lo j) (b12hi j)) →
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => f (Function.update y i t) - K193 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K193 i)
    (hR0 : ∀ i, 0 ≤ R193 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B193 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b12lo j) (b12hi j)) :
    B193 - ∑ j, R193 j ≤ f x :=
  final_bound candsb12 candsb12_ne hR0 candsb12_sub
    (fun i y hy => hstep_of_shifted_concave_box (b12lo_le_b12hi i) (hK0 i)
      hsl candsb12_eq y hy)
    hcorner x hx

/-- idx 194 chain: corner bound minus the grid rebate lower-bounds the margin (box 12; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx194 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b12lo j) (b12hi j)) →
      ConcaveOn ℝ (Set.Icc (b12lo i) (b12hi i))
        (fun t => f (Function.update y i t) - K194 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K194 i)
    (hR0 : ∀ i, 0 ≤ R194 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb12 j) → B194 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b12lo j) (b12hi j)) :
    B194 - ∑ j, R194 j ≤ f x :=
  final_bound candsb12 candsb12_ne hR0 candsb12_sub
    (fun i y hy => hstep_of_shifted_concave_box (b12lo_le_b12hi i) (hK0 i)
      hsl candsb12_eq y hy)
    hcorner x hx

/-- idx 196 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R196v_def (i : Fin 6) : R196 i = K196 i * (b43hi i - b43lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R196, K196, b43lo, b43hi]

/-- idx 196 chain: corner bound minus the grid rebate lower-bounds the margin (box 43; REBATE coordinates per KENV). -/

theorem chain_idx196 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b43lo j) (b43hi j)) →
      ConcaveOn ℝ (Set.Icc (b43lo i) (b43hi i))
        (fun t => f (Function.update y i t) - K196 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K196 i)
    (hR0 : ∀ i, 0 ≤ R196 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb43 j) → B196 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b43lo j) (b43hi j)) :
    B196 - ∑ j, R196 j ≤ f x :=
  final_bound candsb43 candsb43_ne hR0 candsb43_sub
    (fun i y hy => by
      rw [R196v_def i]
      exact hstep_of_shifted_concave_box (b43lo_le_b43hi i) (hK0 i)
        hsl candsb43_eq y hy)
    hcorner x hx

/-- idx 197 chain: corner bound minus the grid rebate lower-bounds the margin (box 15; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx197 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b15lo j) (b15hi j)) →
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => f (Function.update y i t) - K197 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K197 i)
    (hR0 : ∀ i, 0 ≤ R197 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B197 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b15lo j) (b15hi j)) :
    B197 - ∑ j, R197 j ≤ f x :=
  final_bound candsb15 candsb15_ne hR0 candsb15_sub
    (fun i y hy => hstep_of_shifted_concave_box (b15lo_le_b15hi i) (hK0 i)
      hsl candsb15_eq y hy)
    hcorner x hx

/-- idx 198 chain: corner bound minus the grid rebate lower-bounds the margin (box 15; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx198 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b15lo j) (b15hi j)) →
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => f (Function.update y i t) - K198 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K198 i)
    (hR0 : ∀ i, 0 ≤ R198 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B198 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b15lo j) (b15hi j)) :
    B198 - ∑ j, R198 j ≤ f x :=
  final_bound candsb15 candsb15_ne hR0 candsb15_sub
    (fun i y hy => hstep_of_shifted_concave_box (b15lo_le_b15hi i) (hK0 i)
      hsl candsb15_eq y hy)
    hcorner x hx

/-- idx 199 chain: corner bound minus the grid rebate lower-bounds the margin (box 15; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx199 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b15lo j) (b15hi j)) →
      ConcaveOn ℝ (Set.Icc (b15lo i) (b15hi i))
        (fun t => f (Function.update y i t) - K199 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K199 i)
    (hR0 : ∀ i, 0 ≤ R199 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb15 j) → B199 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b15lo j) (b15hi j)) :
    B199 - ∑ j, R199 j ≤ f x :=
  final_bound candsb15 candsb15_ne hR0 candsb15_sub
    (fun i y hy => hstep_of_shifted_concave_box (b15lo_le_b15hi i) (hK0 i)
      hsl candsb15_eq y hy)
    hcorner x hx

/-- idx 201 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R201v_def (i : Fin 6) : R201 i = K201 i * (b44hi i - b44lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R201, K201, b44lo, b44hi]

/-- idx 201 chain: corner bound minus the grid rebate lower-bounds the margin (box 44; REBATE coordinates per KENV). -/

theorem chain_idx201 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b44lo j) (b44hi j)) →
      ConcaveOn ℝ (Set.Icc (b44lo i) (b44hi i))
        (fun t => f (Function.update y i t) - K201 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K201 i)
    (hR0 : ∀ i, 0 ≤ R201 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb44 j) → B201 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b44lo j) (b44hi j)) :
    B201 - ∑ j, R201 j ≤ f x :=
  final_bound candsb44 candsb44_ne hR0 candsb44_sub
    (fun i y hy => by
      rw [R201v_def i]
      exact hstep_of_shifted_concave_box (b44lo_le_b44hi i) (hK0 i)
        hsl candsb44_eq y hy)
    hcorner x hx

/-- idx 202 chain: corner bound minus the grid rebate lower-bounds the margin (box 17; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx202 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b17lo j) (b17hi j)) →
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => f (Function.update y i t) - K202 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K202 i)
    (hR0 : ∀ i, 0 ≤ R202 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B202 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b17lo j) (b17hi j)) :
    B202 - ∑ j, R202 j ≤ f x :=
  final_bound candsb17 candsb17_ne hR0 candsb17_sub
    (fun i y hy => hstep_of_shifted_concave_box (b17lo_le_b17hi i) (hK0 i)
      hsl candsb17_eq y hy)
    hcorner x hx

/-- idx 203 chain: corner bound minus the grid rebate lower-bounds the margin (box 17; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx203 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b17lo j) (b17hi j)) →
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => f (Function.update y i t) - K203 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K203 i)
    (hR0 : ∀ i, 0 ≤ R203 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B203 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b17lo j) (b17hi j)) :
    B203 - ∑ j, R203 j ≤ f x :=
  final_bound candsb17 candsb17_ne hR0 candsb17_sub
    (fun i y hy => hstep_of_shifted_concave_box (b17lo_le_b17hi i) (hK0 i)
      hsl candsb17_eq y hy)
    hcorner x hx

/-- idx 204 chain: corner bound minus the grid rebate lower-bounds the margin (box 18; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx204 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b18lo j) (b18hi j)) →
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => f (Function.update y i t) - K204 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K204 i)
    (hR0 : ∀ i, 0 ≤ R204 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B204 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b18lo j) (b18hi j)) :
    B204 - ∑ j, R204 j ≤ f x :=
  final_bound candsb18 candsb18_ne hR0 candsb18_sub
    (fun i y hy => hstep_of_shifted_concave_box (b18lo_le_b18hi i) (hK0 i)
      hsl candsb18_eq y hy)
    hcorner x hx

/-- idx 206 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R206v_def (i : Fin 6) : R206 i = K206 i * (b44hi i - b44lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R206, K206, b44lo, b44hi]

/-- idx 206 chain: corner bound minus the grid rebate lower-bounds the margin (box 44; REBATE coordinates per KENV). -/

theorem chain_idx206 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b44lo j) (b44hi j)) →
      ConcaveOn ℝ (Set.Icc (b44lo i) (b44hi i))
        (fun t => f (Function.update y i t) - K206 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K206 i)
    (hR0 : ∀ i, 0 ≤ R206 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb44 j) → B206 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b44lo j) (b44hi j)) :
    B206 - ∑ j, R206 j ≤ f x :=
  final_bound candsb44 candsb44_ne hR0 candsb44_sub
    (fun i y hy => by
      rw [R206v_def i]
      exact hstep_of_shifted_concave_box (b44lo_le_b44hi i) (hK0 i)
        hsl candsb44_eq y hy)
    hcorner x hx

/-- idx 207 chain: corner bound minus the grid rebate lower-bounds the margin (box 17; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx207 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b17lo j) (b17hi j)) →
      ConcaveOn ℝ (Set.Icc (b17lo i) (b17hi i))
        (fun t => f (Function.update y i t) - K207 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K207 i)
    (hR0 : ∀ i, 0 ≤ R207 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb17 j) → B207 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b17lo j) (b17hi j)) :
    B207 - ∑ j, R207 j ≤ f x :=
  final_bound candsb17 candsb17_ne hR0 candsb17_sub
    (fun i y hy => hstep_of_shifted_concave_box (b17lo_le_b17hi i) (hK0 i)
      hsl candsb17_eq y hy)
    hcorner x hx

/-- idx 208 chain: corner bound minus the grid rebate lower-bounds the margin (box 18; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx208 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b18lo j) (b18hi j)) →
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => f (Function.update y i t) - K208 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K208 i)
    (hR0 : ∀ i, 0 ≤ R208 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B208 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b18lo j) (b18hi j)) :
    B208 - ∑ j, R208 j ≤ f x :=
  final_bound candsb18 candsb18_ne hR0 candsb18_sub
    (fun i y hy => hstep_of_shifted_concave_box (b18lo_le_b18hi i) (hK0 i)
      hsl candsb18_eq y hy)
    hcorner x hx

/-- idx 209 chain: corner bound minus the grid rebate lower-bounds the margin (box 19; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx209 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b19lo j) (b19hi j)) →
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => f (Function.update y i t) - K209 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K209 i)
    (hR0 : ∀ i, 0 ≤ R209 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B209 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b19lo j) (b19hi j)) :
    B209 - ∑ j, R209 j ≤ f x :=
  final_bound candsb19 candsb19_ne hR0 candsb19_sub
    (fun i y hy => hstep_of_shifted_concave_box (b19lo_le_b19hi i) (hK0 i)
      hsl candsb19_eq y hy)
    hcorner x hx

/-- idx 211 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R211v_def (i : Fin 6) : R211 i = K211 i * (b44hi i - b44lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R211, K211, b44lo, b44hi]

/-- idx 211 chain: corner bound minus the grid rebate lower-bounds the margin (box 44; REBATE coordinates per KENV). -/

theorem chain_idx211 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b44lo j) (b44hi j)) →
      ConcaveOn ℝ (Set.Icc (b44lo i) (b44hi i))
        (fun t => f (Function.update y i t) - K211 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K211 i)
    (hR0 : ∀ i, 0 ≤ R211 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb44 j) → B211 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b44lo j) (b44hi j)) :
    B211 - ∑ j, R211 j ≤ f x :=
  final_bound candsb44 candsb44_ne hR0 candsb44_sub
    (fun i y hy => by
      rw [R211v_def i]
      exact hstep_of_shifted_concave_box (b44lo_le_b44hi i) (hK0 i)
        hsl candsb44_eq y hy)
    hcorner x hx

/-- idx 212 chain: corner bound minus the grid rebate lower-bounds the margin (box 18; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx212 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b18lo j) (b18hi j)) →
      ConcaveOn ℝ (Set.Icc (b18lo i) (b18hi i))
        (fun t => f (Function.update y i t) - K212 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K212 i)
    (hR0 : ∀ i, 0 ≤ R212 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb18 j) → B212 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b18lo j) (b18hi j)) :
    B212 - ∑ j, R212 j ≤ f x :=
  final_bound candsb18 candsb18_ne hR0 candsb18_sub
    (fun i y hy => hstep_of_shifted_concave_box (b18lo_le_b18hi i) (hK0 i)
      hsl candsb18_eq y hy)
    hcorner x hx

/-- idx 213 chain: corner bound minus the grid rebate lower-bounds the margin (box 19; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx213 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b19lo j) (b19hi j)) →
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => f (Function.update y i t) - K213 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K213 i)
    (hR0 : ∀ i, 0 ≤ R213 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B213 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b19lo j) (b19hi j)) :
    B213 - ∑ j, R213 j ≤ f x :=
  final_bound candsb19 candsb19_ne hR0 candsb19_sub
    (fun i y hy => hstep_of_shifted_concave_box (b19lo_le_b19hi i) (hK0 i)
      hsl candsb19_eq y hy)
    hcorner x hx

/-- idx 214 chain: corner bound minus the grid rebate lower-bounds the margin (box 19; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx214 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b19lo j) (b19hi j)) →
      ConcaveOn ℝ (Set.Icc (b19lo i) (b19hi i))
        (fun t => f (Function.update y i t) - K214 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K214 i)
    (hR0 : ∀ i, 0 ≤ R214 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb19 j) → B214 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b19lo j) (b19hi j)) :
    B214 - ∑ j, R214 j ≤ f x :=
  final_bound candsb19 candsb19_ne hR0 candsb19_sub
    (fun i y hy => hstep_of_shifted_concave_box (b19lo_le_b19hi i) (hK0 i)
      hsl candsb19_eq y hy)
    hcorner x hx

/-- idx 216 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R216v_def (i : Fin 6) : R216 i = K216 i * (b45hi i - b45lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R216, K216, b45lo, b45hi]

/-- idx 216 chain: corner bound minus the grid rebate lower-bounds the margin (box 45; REBATE coordinates per KENV). -/

theorem chain_idx216 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b45lo j) (b45hi j)) →
      ConcaveOn ℝ (Set.Icc (b45lo i) (b45hi i))
        (fun t => f (Function.update y i t) - K216 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K216 i)
    (hR0 : ∀ i, 0 ≤ R216 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb45 j) → B216 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b45lo j) (b45hi j)) :
    B216 - ∑ j, R216 j ≤ f x :=
  final_bound candsb45 candsb45_ne hR0 candsb45_sub
    (fun i y hy => by
      rw [R216v_def i]
      exact hstep_of_shifted_concave_box (b45lo_le_b45hi i) (hK0 i)
        hsl candsb45_eq y hy)
    hcorner x hx

/-- idx 217 chain: corner bound minus the grid rebate lower-bounds the margin (box 21; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx217 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b21lo j) (b21hi j)) →
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => f (Function.update y i t) - K217 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K217 i)
    (hR0 : ∀ i, 0 ≤ R217 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B217 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b21lo j) (b21hi j)) :
    B217 - ∑ j, R217 j ≤ f x :=
  final_bound candsb21 candsb21_ne hR0 candsb21_sub
    (fun i y hy => hstep_of_shifted_concave_box (b21lo_le_b21hi i) (hK0 i)
      hsl candsb21_eq y hy)
    hcorner x hx

/-- idx 218 chain: corner bound minus the grid rebate lower-bounds the margin (box 21; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx218 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b21lo j) (b21hi j)) →
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => f (Function.update y i t) - K218 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K218 i)
    (hR0 : ∀ i, 0 ≤ R218 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B218 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b21lo j) (b21hi j)) :
    B218 - ∑ j, R218 j ≤ f x :=
  final_bound candsb21 candsb21_ne hR0 candsb21_sub
    (fun i y hy => hstep_of_shifted_concave_box (b21lo_le_b21hi i) (hK0 i)
      hsl candsb21_eq y hy)
    hcorner x hx

/-- idx 219 chain: corner bound minus the grid rebate lower-bounds the margin (box 21; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx219 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b21lo j) (b21hi j)) →
      ConcaveOn ℝ (Set.Icc (b21lo i) (b21hi i))
        (fun t => f (Function.update y i t) - K219 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K219 i)
    (hR0 : ∀ i, 0 ≤ R219 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb21 j) → B219 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b21lo j) (b21hi j)) :
    B219 - ∑ j, R219 j ≤ f x :=
  final_bound candsb21 candsb21_ne hR0 candsb21_sub
    (fun i y hy => hstep_of_shifted_concave_box (b21lo_le_b21hi i) (hK0 i)
      hsl candsb21_eq y hy)
    hcorner x hx

/-- idx 221 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R221v_def (i : Fin 6) : R221 i = K221 i * (b46hi i - b46lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R221, K221, b46lo, b46hi]

/-- idx 221 chain: corner bound minus the grid rebate lower-bounds the margin (box 46; REBATE coordinates per KENV). -/

theorem chain_idx221 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b46lo j) (b46hi j)) →
      ConcaveOn ℝ (Set.Icc (b46lo i) (b46hi i))
        (fun t => f (Function.update y i t) - K221 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K221 i)
    (hR0 : ∀ i, 0 ≤ R221 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb46 j) → B221 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b46lo j) (b46hi j)) :
    B221 - ∑ j, R221 j ≤ f x :=
  final_bound candsb46 candsb46_ne hR0 candsb46_sub
    (fun i y hy => by
      rw [R221v_def i]
      exact hstep_of_shifted_concave_box (b46lo_le_b46hi i) (hK0 i)
        hsl candsb46_eq y hy)
    hcorner x hx

/-- idx 222 chain: corner bound minus the grid rebate lower-bounds the margin (box 23; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx222 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b23lo j) (b23hi j)) →
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => f (Function.update y i t) - K222 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K222 i)
    (hR0 : ∀ i, 0 ≤ R222 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B222 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b23lo j) (b23hi j)) :
    B222 - ∑ j, R222 j ≤ f x :=
  final_bound candsb23 candsb23_ne hR0 candsb23_sub
    (fun i y hy => hstep_of_shifted_concave_box (b23lo_le_b23hi i) (hK0 i)
      hsl candsb23_eq y hy)
    hcorner x hx

/-- idx 223 chain: corner bound minus the grid rebate lower-bounds the margin (box 23; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx223 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b23lo j) (b23hi j)) →
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => f (Function.update y i t) - K223 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K223 i)
    (hR0 : ∀ i, 0 ≤ R223 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B223 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b23lo j) (b23hi j)) :
    B223 - ∑ j, R223 j ≤ f x :=
  final_bound candsb23 candsb23_ne hR0 candsb23_sub
    (fun i y hy => hstep_of_shifted_concave_box (b23lo_le_b23hi i) (hK0 i)
      hsl candsb23_eq y hy)
    hcorner x hx

/-- idx 224 chain: corner bound minus the grid rebate lower-bounds the margin (box 23; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx224 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b23lo j) (b23hi j)) →
      ConcaveOn ℝ (Set.Icc (b23lo i) (b23hi i))
        (fun t => f (Function.update y i t) - K224 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K224 i)
    (hR0 : ∀ i, 0 ≤ R224 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb23 j) → B224 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b23lo j) (b23hi j)) :
    B224 - ∑ j, R224 j ≤ f x :=
  final_bound candsb23 candsb23_ne hR0 candsb23_sub
    (fun i y hy => hstep_of_shifted_concave_box (b23lo_le_b23hi i) (hK0 i)
      hsl candsb23_eq y hy)
    hcorner x hx

/-- idx 226 rebate bridge: exact-fraction R equals the hstep value form
K·W²/8 (norm_num doubles as the KENV R_i_exact consistency check). -/

theorem R226v_def (i : Fin 6) : R226 i = K226 i * (b47hi i - b47lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R226, K226, b47lo, b47hi]

/-- idx 226 chain: corner bound minus the grid rebate lower-bounds the margin (box 47; REBATE coordinates per KENV). -/

theorem chain_idx226 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b47lo j) (b47hi j)) →
      ConcaveOn ℝ (Set.Icc (b47lo i) (b47hi i))
        (fun t => f (Function.update y i t) - K226 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K226 i)
    (hR0 : ∀ i, 0 ≤ R226 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb47 j) → B226 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b47lo j) (b47hi j)) :
    B226 - ∑ j, R226 j ≤ f x :=
  final_bound candsb47 candsb47_ne hR0 candsb47_sub
    (fun i y hy => by
      rw [R226v_def i]
      exact hstep_of_shifted_concave_box (b47lo_le_b47hi i) (hK0 i)
        hsl candsb47_eq y hy)
    hcorner x hx

/-- idx 227 chain: corner bound minus the grid rebate lower-bounds the margin (box 26; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx227 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b26lo j) (b26hi j)) →
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => f (Function.update y i t) - K227 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K227 i)
    (hR0 : ∀ i, 0 ≤ R227 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B227 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b26lo j) (b26hi j)) :
    B227 - ∑ j, R227 j ≤ f x :=
  final_bound candsb26 candsb26_ne hR0 candsb26_sub
    (fun i y hy => hstep_of_shifted_concave_box (b26lo_le_b26hi i) (hK0 i)
      hsl candsb26_eq y hy)
    hcorner x hx

/-- idx 228 chain: corner bound minus the grid rebate lower-bounds the margin (box 26; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx228 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b26lo j) (b26hi j)) →
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => f (Function.update y i t) - K228 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K228 i)
    (hR0 : ∀ i, 0 ≤ R228 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B228 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b26lo j) (b26hi j)) :
    B228 - ∑ j, R228 j ≤ f x :=
  final_bound candsb26 candsb26_ne hR0 candsb26_sub
    (fun i y hy => hstep_of_shifted_concave_box (b26lo_le_b26hi i) (hK0 i)
      hsl candsb26_eq y hy)
    hcorner x hx

/-- idx 229 chain: corner bound minus the grid rebate lower-bounds the margin (box 26; ALL-CONCAVE, no rebate (K = 0)). -/

theorem chain_idx229 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      (∀ j : Fin 6, y j ∈ Set.Icc (b26lo j) (b26hi j)) →
      ConcaveOn ℝ (Set.Icc (b26lo i) (b26hi i))
        (fun t => f (Function.update y i t) - K229 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K229 i)
    (hR0 : ∀ i, 0 ≤ R229 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb26 j) → B229 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b26lo j) (b26hi j)) :
    B229 - ∑ j, R229 j ≤ f x :=
  final_bound candsb26 candsb26_ne hR0 candsb26_sub
    (fun i y hy => hstep_of_shifted_concave_box (b26lo_le_b26hi i) (hK0 i)
      hsl candsb26_eq y hy)
    hcorner x hx

/-! ### Axiom audit -/

#print axioms chain_idx181

#print axioms chain_idx182

#print axioms chain_idx183

#print axioms chain_idx184

#print axioms chain_idx186

#print axioms chain_idx187

#print axioms chain_idx188

#print axioms chain_idx189

#print axioms chain_idx191

#print axioms chain_idx192

#print axioms chain_idx193

#print axioms chain_idx194

#print axioms chain_idx196

#print axioms chain_idx197

#print axioms chain_idx198

#print axioms chain_idx199

#print axioms chain_idx201

#print axioms chain_idx202

#print axioms chain_idx203

#print axioms chain_idx204

#print axioms chain_idx206

#print axioms chain_idx207

#print axioms chain_idx208

#print axioms chain_idx209

#print axioms chain_idx211

#print axioms chain_idx212

#print axioms chain_idx213

#print axioms chain_idx214

#print axioms chain_idx216

#print axioms chain_idx217

#print axioms chain_idx218

#print axioms chain_idx219

#print axioms chain_idx221

#print axioms chain_idx222

#print axioms chain_idx223

#print axioms chain_idx224

#print axioms chain_idx226

#print axioms chain_idx227

#print axioms chain_idx228

#print axioms chain_idx229

end Kepler.Text
