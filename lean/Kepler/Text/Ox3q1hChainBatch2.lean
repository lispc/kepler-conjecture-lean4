/-
Ox3q1hChainBatch2: S3 mass-production batch 2 (32 conjuncts, idx 20-59,
boxes 4-11). ALL-CONCAVE (24) + Y4_PATCH (4) + SPLIT_PLAN (4).

All chains use the per-coordinate R_i from KENV exact fractions and
conclude `B_i - ∑ R_i ≤ f x` under hypotheses hsl/hK0/hR0/hcorner.

The Y4_PATCH (idx 21/26/31/36) and SPLIT_PLAN (idx 41/46/51/56) rows
carry their m-split / y4-patch R-computation obligations documented:
the KENV R_i_exact values are the batch's data interface, with the
per-row-type R-computation formulas supplied by the follow-up batches.
-/
import Mathlib
import Kepler.Text.Ox3q1hChain3

open Set Filter Topology

namespace Kepler.Text

/-- Box 1 lower corner. -/
noncomputable def b1lo : Fin 6 → ℝ := ![4927/2000, 2, 2, 2, 2, 2]

/-- Box 1 upper corner. -/
noncomputable def b1hi : Fin 6 → ℝ := ![63/25, 15397/6250, 15397/6250, 15397/6250, 15397/6250, 15397/6250]

theorem b1lo_le_b1hi (i : Fin 6) : b1lo i ≤ b1hi i := by
  fin_cases i
  all_goals norm_num [b1lo, b1hi]

/-- Box 2 lower corner. -/
noncomputable def b2lo : Fin 6 → ℝ := ![4927/2000, 2, 2, 8927/4000, 2, 2]

/-- Box 2 upper corner. -/
noncomputable def b2hi : Fin 6 → ℝ := ![63/25, 15397/6250, 15397/6250, 15397/6250, 15397/6250, 15397/6250]

theorem b2lo_le_b2hi (i : Fin 6) : b2lo i ≤ b2hi i := by
  fin_cases i
  all_goals norm_num [b2lo, b2hi]

/-- Box 3 lower corner. -/
noncomputable def b3lo : Fin 6 → ℝ := ![4927/2000, 2, 2, 2, 2, 2]

/-- Box 3 upper corner. -/
noncomputable def b3hi : Fin 6 → ℝ := ![63/25, 15397/6250, 15397/6250, 27897/12500, 15397/6250, 15397/6250]

theorem b3lo_le_b3hi (i : Fin 6) : b3lo i ≤ b3hi i := by
  fin_cases i
  all_goals norm_num [b3lo, b3hi]

/-- Box 4 lower corner. -/
noncomputable def b4lo : Fin 6 → ℝ := ![4927/2000, 2, 2, 4927/2000, 2, 2]

/-- Box 4 upper corner. -/
noncomputable def b4hi : Fin 6 → ℝ := ![63/25, 15397/6250, 15397/6250, 63/25, 15397/6250, 15397/6250]

theorem b4lo_le_b4hi (i : Fin 6) : b4lo i ≤ b4hi i := by
  fin_cases i
  all_goals norm_num [b4lo, b4hi]

/-- Box 5 lower corner. -/
noncomputable def b5lo : Fin 6 → ℝ := ![63/25, 2, 2, 63/25, 2, 2]

/-- Box 5 upper corner. -/
noncomputable def b5hi : Fin 6 → ℝ := ![6627/2500, 15397/6250, 15397/6250, 6627/2500, 15397/6250, 15397/6250]

theorem b5lo_le_b5hi (i : Fin 6) : b5lo i ≤ b5hi i := by
  fin_cases i
  all_goals norm_num [b5lo, b5hi]

/-- Box 6 lower corner. -/
noncomputable def b6lo : Fin 6 → ℝ := ![63/25, 2, 2, 2, 2, 2]

/-- Box 6 upper corner. -/
noncomputable def b6hi : Fin 6 → ℝ := ![6627/2500, 15397/6250, 15397/6250, 15397/6250, 15397/6250, 15397/6250]

theorem b6lo_le_b6hi (i : Fin 6) : b6lo i ≤ b6hi i := by
  fin_cases i
  all_goals norm_num [b6lo, b6hi]

/-- Box 7 lower corner. -/
noncomputable def b7lo : Fin 6 → ℝ := ![63/25, 2, 2, 8927/4000, 2, 2]

/-- Box 7 upper corner. -/
noncomputable def b7hi : Fin 6 → ℝ := ![6627/2500, 15397/6250, 15397/6250, 15397/6250, 15397/6250, 15397/6250]

theorem b7lo_le_b7hi (i : Fin 6) : b7lo i ≤ b7hi i := by
  fin_cases i
  all_goals norm_num [b7lo, b7hi]

/-- Box 8 lower corner. -/
noncomputable def b8lo : Fin 6 → ℝ := ![63/25, 2, 2, 2, 2, 2]

/-- Box 8 upper corner. -/
noncomputable def b8hi : Fin 6 → ℝ := ![6627/2500, 15397/6250, 15397/6250, 27897/12500, 15397/6250, 15397/6250]

theorem b8lo_le_b8hi (i : Fin 6) : b8lo i ≤ b8hi i := by
  fin_cases i
  all_goals norm_num [b8lo, b8hi]

/-- Box 9 lower corner. -/
noncomputable def b9lo : Fin 6 → ℝ := ![12927/5000, 2, 2, 63/25, 2, 2]

/-- Box 9 upper corner. -/
noncomputable def b9hi : Fin 6 → ℝ := ![6627/2500, 15397/6250, 15397/6250, 6627/2500, 15397/6250, 15397/6250]

theorem b9lo_le_b9hi (i : Fin 6) : b9lo i ≤ b9hi i := by
  fin_cases i
  all_goals norm_num [b9lo, b9hi]

/-- Box 10 lower corner. -/
noncomputable def b10lo : Fin 6 → ℝ := ![12927/5000, 2, 2, 2, 2, 2]

/-- Box 10 upper corner. -/
noncomputable def b10hi : Fin 6 → ℝ := ![6627/2500, 15397/6250, 15397/6250, 27897/12500, 15397/6250, 15397/6250]

theorem b10lo_le_b10hi (i : Fin 6) : b10lo i ≤ b10hi i := by
  fin_cases i
  all_goals norm_num [b10lo, b10hi]

/-- Box 11 lower corner. -/
noncomputable def b11lo : Fin 6 → ℝ := ![12927/5000, 2, 2, 16927/8000, 2, 2]

/-- Box 11 upper corner. -/
noncomputable def b11hi : Fin 6 → ℝ := ![6627/2500, 15397/6250, 15397/6250, 27897/12500, 15397/6250, 15397/6250]

theorem b11lo_le_b11hi (i : Fin 6) : b11lo i ≤ b11hi i := by
  fin_cases i
  all_goals norm_num [b11lo, b11hi]

/-- idx 21 per-coordinate curvature bounds (KENV). -/
noncomputable def K21 : Fin 6 → ℝ := ![0/1, 0/1, 0/1, 625057162349/1099511627776, 0/1, 0/1]

/-- idx 21 corner-table bound (CONJ_TABLE). -/
noncomputable def B21 : ℝ := 4895826076609267045505263/1801439850948198400000000000

/-- idx 21 per-coordinate grid rebates (KENV exact). -/
noncomputable def R21 : Fin 6 → ℝ := ![0, 0, 0, 7981354906034381/35184372088832000000, 0, 0]

/-- idx 22 per-coordinate curvature bounds (KENV). -/
noncomputable def K22 : Fin 6 → ℝ := fun _ => 0

/-- idx 22 corner-table bound (CONJ_TABLE). -/
noncomputable def B22 : ℝ := 391755953970611721873027/144115188075855872000000000

/-- idx 22 per-coordinate grid rebates (KENV exact). -/
noncomputable def R22 : Fin 6 → ℝ := fun _ => 0

/-- idx 23 per-coordinate curvature bounds (KENV). -/
noncomputable def K23 : Fin 6 → ℝ := fun _ => 0

/-- idx 23 corner-table bound (CONJ_TABLE). -/
noncomputable def B23 : ℝ := 9816462584030802937566801/3602879701896396800000000000

/-- idx 23 per-coordinate grid rebates (KENV exact). -/
noncomputable def R23 : Fin 6 → ℝ := fun _ => 0

/-- idx 24 per-coordinate curvature bounds (KENV). -/
noncomputable def K24 : Fin 6 → ℝ := fun _ => 0

/-- idx 24 corner-table bound (CONJ_TABLE). -/
noncomputable def B24 : ℝ := 391525641827483180239857/144115188075855872000000000

/-- idx 24 per-coordinate grid rebates (KENV exact). -/
noncomputable def R24 : Fin 6 → ℝ := fun _ => 0

/-- idx 26 per-coordinate curvature bounds (KENV). -/
noncomputable def K26 : Fin 6 → ℝ := ![0/1, 0/1, 0/1, 625057162349/1099511627776, 0/1, 0/1]

/-- idx 26 corner-table bound (CONJ_TABLE). -/
noncomputable def B26 : ℝ := 4898078236710922483144943/1801439850948198400000000000

/-- idx 26 per-coordinate grid rebates (KENV exact). -/
noncomputable def R26 : Fin 6 → ℝ := ![0, 0, 0, 7981354906034381/35184372088832000000, 0, 0]

/-- idx 27 per-coordinate curvature bounds (KENV). -/
noncomputable def K27 : Fin 6 → ℝ := fun _ => 0

/-- idx 27 corner-table bound (CONJ_TABLE). -/
noncomputable def B27 : ℝ := 391755953970611721873027/144115188075855872000000000

/-- idx 27 per-coordinate grid rebates (KENV exact). -/
noncomputable def R27 : Fin 6 → ℝ := fun _ => 0

/-- idx 28 per-coordinate curvature bounds (KENV). -/
noncomputable def K28 : Fin 6 → ℝ := fun _ => 0

/-- idx 28 corner-table bound (CONJ_TABLE). -/
noncomputable def B28 : ℝ := 392390332955938315471857/144115188075855872000000000

/-- idx 28 per-coordinate grid rebates (KENV exact). -/
noncomputable def R28 : Fin 6 → ℝ := fun _ => 0

/-- idx 29 per-coordinate curvature bounds (KENV). -/
noncomputable def K29 : Fin 6 → ℝ := fun _ => 0

/-- idx 29 corner-table bound (CONJ_TABLE). -/
noncomputable def B29 : ℝ := 391755953970611721873027/144115188075855872000000000

/-- idx 29 per-coordinate grid rebates (KENV exact). -/
noncomputable def R29 : Fin 6 → ℝ := fun _ => 0

/-- idx 31 per-coordinate curvature bounds (KENV). -/
noncomputable def K31 : Fin 6 → ℝ := ![0/1, 0/1, 0/1, 625057162349/1099511627776, 0/1, 0/1]

/-- idx 31 corner-table bound (CONJ_TABLE). -/
noncomputable def B31 : ℝ := 391762464992251800366721/144115188075855872000000000

/-- idx 31 per-coordinate grid rebates (KENV exact). -/
noncomputable def R31 : Fin 6 → ℝ := ![0, 0, 0, 7981354906034381/35184372088832000000, 0, 0]

/-- idx 32 per-coordinate curvature bounds (KENV). -/
noncomputable def K32 : Fin 6 → ℝ := fun _ => 0

/-- idx 32 corner-table bound (CONJ_TABLE). -/
noncomputable def B32 : ℝ := 391669757015559036111857/144115188075855872000000000

/-- idx 32 per-coordinate grid rebates (KENV exact). -/
noncomputable def R32 : Fin 6 → ℝ := fun _ => 0

/-- idx 33 per-coordinate curvature bounds (KENV). -/
noncomputable def K33 : Fin 6 → ℝ := fun _ => 0

/-- idx 33 corner-table bound (CONJ_TABLE). -/
noncomputable def B33 : ℝ := 392620645099066857105027/144115188075855872000000000

/-- idx 33 per-coordinate grid rebates (KENV exact). -/
noncomputable def R33 : Fin 6 → ℝ := fun _ => 0

/-- idx 34 per-coordinate curvature bounds (KENV). -/
noncomputable def K34 : Fin 6 → ℝ := fun _ => 0

/-- idx 34 corner-table bound (CONJ_TABLE). -/
noncomputable def B34 : ℝ := 9789929248523780961261137/3602879701896396800000000000

/-- idx 34 per-coordinate grid rebates (KENV exact). -/
noncomputable def R34 : Fin 6 → ℝ := fun _ => 0

/-- idx 36 per-coordinate curvature bounds (KENV). -/
noncomputable def K36 : Fin 6 → ℝ := ![0/1, 0/1, 0/1, 588977957083/1099511627776, 0/1, 0/1]

/-- idx 36 corner-table bound (CONJ_TABLE). -/
noncomputable def B36 : ℝ := 169003679070000176490327241168231/75244594461734338560000000000000000

/-- idx 36 per-coordinate grid rebates (KENV exact). -/
noncomputable def R36 : Fin 6 → ℝ := ![0, 0, 0, 7520659533992827/35184372088832000000, 0, 0]

/-- idx 37 per-coordinate curvature bounds (KENV). -/
noncomputable def K37 : Fin 6 → ℝ := fun _ => 0

/-- idx 37 corner-table bound (CONJ_TABLE). -/
noncomputable def B37 : ℝ := 126679907057025841756863/56294995342131200000000000

/-- idx 37 per-coordinate grid rebates (KENV exact). -/
noncomputable def R37 : Fin 6 → ℝ := fun _ => 0

/-- idx 38 per-coordinate curvature bounds (KENV). -/
noncomputable def K38 : Fin 6 → ℝ := fun _ => 0

/-- idx 38 corner-table bound (CONJ_TABLE). -/
noncomputable def B38 : ℝ := 252969903718818119827/112589990684262400000000

/-- idx 38 per-coordinate grid rebates (KENV exact). -/
noncomputable def R38 : Fin 6 → ℝ := fun _ => 0

/-- idx 39 per-coordinate curvature bounds (KENV). -/
noncomputable def K39 : Fin 6 → ℝ := fun _ => 0

/-- idx 39 corner-table bound (CONJ_TABLE). -/
noncomputable def B39 : ℝ := 126679907057025841756863/56294995342131200000000000

/-- idx 39 per-coordinate grid rebates (KENV exact). -/
noncomputable def R39 : Fin 6 → ℝ := fun _ => 0

/-- idx 41 per-coordinate curvature bounds (KENV). -/
noncomputable def b2K41 : Fin 6 → ℝ := ![0/1, 24116497483/137438953472, 24116497483/137438953472, 949858192033/1099511627776, 24116497483/137438953472, 24116497483/137438953472]

/-- idx 41 corner-table bound (CONJ_TABLE). -/
noncomputable def b2B41 : ℝ := 10410645719309171611178167/3602879701896396800000000000

/-- idx 41 per-coordinate grid rebates (KENV exact). -/
noncomputable def b2R41 : Fin 6 → ℝ := ![0, 202400333824303147/42949672960000000000, 202400333824303147/42949672960000000000, 101567386615896657/54975581388800000000, 202400333824303147/42949672960000000000, 202400333824303147/42949672960000000000]

/-- idx 42 per-coordinate curvature bounds (KENV). -/
noncomputable def K42 : Fin 6 → ℝ := fun _ => 0

/-- idx 42 corner-table bound (CONJ_TABLE). -/
noncomputable def B42 : ℝ := 1300659138202979573854401/450359962737049600000000000

/-- idx 42 per-coordinate grid rebates (KENV exact). -/
noncomputable def R42 : Fin 6 → ℝ := fun _ => 0

/-- idx 43 per-coordinate curvature bounds (KENV). -/
noncomputable def K43 : Fin 6 → ℝ := fun _ => 0

/-- idx 43 corner-table bound (CONJ_TABLE). -/
noncomputable def B43 : ℝ := 2082705277710028748963121/720575940379279360000000000

/-- idx 43 per-coordinate grid rebates (KENV exact). -/
noncomputable def R43 : Fin 6 → ℝ := fun _ => 0

/-- idx 44 per-coordinate curvature bounds (KENV). -/
noncomputable def K44 : Fin 6 → ℝ := fun _ => 0

/-- idx 44 corner-table bound (CONJ_TABLE). -/
noncomputable def B44 : ℝ := 520351686966608802787793/180143985094819840000000000

/-- idx 44 per-coordinate grid rebates (KENV exact). -/
noncomputable def R44 : Fin 6 → ℝ := fun _ => 0

/-- idx 46 per-coordinate curvature bounds (KENV). -/
noncomputable def K46 : Fin 6 → ℝ := ![0/1, 24116497483/137438953472, 24116497483/137438953472, 949858192033/1099511627776, 24116497483/137438953472, 24116497483/137438953472]

/-- idx 46 corner-table bound (CONJ_TABLE). -/
noncomputable def b2B46 : ℝ := 10407763415547654493738167/3602879701896396800000000000

/-- idx 46 per-coordinate grid rebates (KENV exact). -/
noncomputable def R46 : Fin 6 → ℝ := ![0, 202400333824303147/42949672960000000000, 202400333824303147/42949672960000000000, 101567386615896657/54975581388800000000, 202400333824303147/42949672960000000000, 202400333824303147/42949672960000000000]

/-- idx 47 per-coordinate curvature bounds (KENV). -/
noncomputable def K47 : Fin 6 → ℝ := fun _ => 0

/-- idx 47 corner-table bound (CONJ_TABLE). -/
noncomputable def B47 : ℝ := 2599672155598563389141859/900719925474099200000000000

/-- idx 47 per-coordinate grid rebates (KENV exact). -/
noncomputable def R47 : Fin 6 → ℝ := fun _ => 0

/-- idx 48 per-coordinate curvature bounds (KENV). -/
noncomputable def K48 : Fin 6 → ℝ := fun _ => 0

/-- idx 48 corner-table bound (CONJ_TABLE). -/
noncomputable def B48 : ℝ := 520892118921893262307793/180143985094819840000000000

/-- idx 48 per-coordinate grid rebates (KENV exact). -/
noncomputable def R48 : Fin 6 → ℝ := fun _ => 0

/-- idx 49 per-coordinate curvature bounds (KENV). -/
noncomputable def K49 : Fin 6 → ℝ := fun _ => 0

/-- idx 49 corner-table bound (CONJ_TABLE). -/
noncomputable def B49 : ℝ := 2599672155598563389141859/900719925474099200000000000

/-- idx 49 per-coordinate grid rebates (KENV exact). -/
noncomputable def R49 : Fin 6 → ℝ := fun _ => 0

/-- idx 51 per-coordinate curvature bounds (KENV). -/
noncomputable def K51 : Fin 6 → ℝ := ![0/1, 24116497483/137438953472, 24116497483/137438953472, 949858192033/1099511627776, 24116497483/137438953472, 24116497483/137438953472]

/-- idx 51 corner-table bound (CONJ_TABLE). -/
noncomputable def B51 : ℝ := 10410645719309171611178167/3602879701896396800000000000

/-- idx 51 per-coordinate grid rebates (KENV exact). -/
noncomputable def R51 : Fin 6 → ℝ := ![0, 202400333824303147/42949672960000000000, 202400333824303147/42949672960000000000, 101567386615896657/54975581388800000000, 202400333824303147/42949672960000000000, 202400333824303147/42949672960000000000]

/-- idx 52 per-coordinate curvature bounds (KENV). -/
noncomputable def K52 : Fin 6 → ℝ := fun _ => 0

/-- idx 52 corner-table bound (CONJ_TABLE). -/
noncomputable def B52 : ℝ := 16654401013328868680957/5764607523034234880000000

/-- idx 52 per-coordinate grid rebates (KENV exact). -/
noncomputable def R52 : Fin 6 → ℝ := fun _ => 0

/-- idx 53 per-coordinate curvature bounds (KENV). -/
noncomputable def K53 : Fin 6 → ℝ := fun _ => 0

/-- idx 53 corner-table bound (CONJ_TABLE). -/
noncomputable def B53 : ℝ := 2082705277710028748963121/720575940379279360000000000

/-- idx 53 per-coordinate grid rebates (KENV exact). -/
noncomputable def R53 : Fin 6 → ℝ := fun _ => 0

/-- idx 54 per-coordinate curvature bounds (KENV). -/
noncomputable def K54 : Fin 6 → ℝ := fun _ => 0

/-- idx 54 corner-table bound (CONJ_TABLE). -/
noncomputable def B54 : ℝ := 2599672155598563389141859/900719925474099200000000000

/-- idx 54 per-coordinate grid rebates (KENV exact). -/
noncomputable def R54 : Fin 6 → ℝ := fun _ => 0

/-- idx 56 per-coordinate curvature bounds (KENV). -/
noncomputable def K56 : Fin 6 → ℝ := ![0/1, 46446597/268435456, 46446597/268435456, 236299718527/274877906944, 46446597/268435456, 46446597/268435456]

/-- idx 56 corner-table bound (CONJ_TABLE). -/
noncomputable def B56 : ℝ := 9662398472678640545419551/1801439850948198400000000000

/-- idx 56 per-coordinate grid rebates (KENV exact). -/
noncomputable def R56 : Fin 6 → ℝ := ![0, 389808128001573/83886080000000000, 389808128001573/83886080000000000, 25267292602373583/13743895347200000000, 389808128001573/83886080000000000, 389808128001573/83886080000000000]

/-- idx 57 per-coordinate curvature bounds (KENV). -/
noncomputable def K57 : Fin 6 → ℝ := fun _ => 0

/-- idx 57 corner-table bound (CONJ_TABLE). -/
noncomputable def B57 : ℝ := 2411278762556442976863527/450359962737049600000000000

/-- idx 57 per-coordinate grid rebates (KENV exact). -/
noncomputable def R57 : Fin 6 → ℝ := fun _ => 0

/-- idx 58 per-coordinate curvature bounds (KENV). -/
noncomputable def K58 : Fin 6 → ℝ := fun _ => 0

/-- idx 58 corner-table bound (CONJ_TABLE). -/
noncomputable def B58 : ℝ := 1932823063922836623361699/360287970189639680000000000

/-- idx 58 per-coordinate grid rebates (KENV exact). -/
noncomputable def R58 : Fin 6 → ℝ := fun _ => 0

/-- idx 59 per-coordinate curvature bounds (KENV). -/
noncomputable def K59 : Fin 6 → ℝ := fun _ => 0

/-- idx 59 corner-table bound (CONJ_TABLE). -/
noncomputable def B59 : ℝ := 96477166132911695178113/18014398509481984000000000

/-- idx 59 per-coordinate grid rebates (KENV exact). -/
noncomputable def R59 : Fin 6 → ℝ := fun _ => 0

/-- The unsplit two-corner grid of box 1. -/
noncomputable def candsb1 : Fin 6 → Finset ℝ :=
  fun i => insert (b1lo i) {b1hi i}

theorem candsb1_eq (i : Fin 6) : candsb1 i = insert (b1lo i) {b1hi i} := rfl

theorem candsb1_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb1 i) :
    c ∈ Set.Icc (b1lo i) (b1hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b1lo_le_b1hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b1lo_le_b1hi i, le_rfl⟩

theorem candsb1_ne (i : Fin 6) : (candsb1 i).Nonempty := ⟨b1lo i, by
  simp only [candsb1]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 2. -/
noncomputable def candsb2 : Fin 6 → Finset ℝ :=
  fun i => insert (b2lo i) {b2hi i}

theorem candsb2_eq (i : Fin 6) : candsb2 i = insert (b2lo i) {b2hi i} := rfl

theorem candsb2_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb2 i) :
    c ∈ Set.Icc (b2lo i) (b2hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b2lo_le_b2hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b2lo_le_b2hi i, le_rfl⟩

theorem candsb2_ne (i : Fin 6) : (candsb2 i).Nonempty := ⟨b2lo i, by
  simp only [candsb2]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 3. -/
noncomputable def candsb3 : Fin 6 → Finset ℝ :=
  fun i => insert (b3lo i) {b3hi i}

theorem candsb3_eq (i : Fin 6) : candsb3 i = insert (b3lo i) {b3hi i} := rfl

theorem candsb3_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb3 i) :
    c ∈ Set.Icc (b3lo i) (b3hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b3lo_le_b3hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b3lo_le_b3hi i, le_rfl⟩

theorem candsb3_ne (i : Fin 6) : (candsb3 i).Nonempty := ⟨b3lo i, by
  simp only [candsb3]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 4. -/
noncomputable def candsb4 : Fin 6 → Finset ℝ :=
  fun i => insert (b4lo i) {b4hi i}

theorem candsb4_eq (i : Fin 6) : candsb4 i = insert (b4lo i) {b4hi i} := rfl

theorem candsb4_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb4 i) :
    c ∈ Set.Icc (b4lo i) (b4hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b4lo_le_b4hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b4lo_le_b4hi i, le_rfl⟩

theorem candsb4_ne (i : Fin 6) : (candsb4 i).Nonempty := ⟨b4lo i, by
  simp only [candsb4]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 5. -/
noncomputable def candsb5 : Fin 6 → Finset ℝ :=
  fun i => insert (b5lo i) {b5hi i}

theorem candsb5_eq (i : Fin 6) : candsb5 i = insert (b5lo i) {b5hi i} := rfl

theorem candsb5_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb5 i) :
    c ∈ Set.Icc (b5lo i) (b5hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b5lo_le_b5hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b5lo_le_b5hi i, le_rfl⟩

theorem candsb5_ne (i : Fin 6) : (candsb5 i).Nonempty := ⟨b5lo i, by
  simp only [candsb5]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 6. -/
noncomputable def candsb6 : Fin 6 → Finset ℝ :=
  fun i => insert (b6lo i) {b6hi i}

theorem candsb6_eq (i : Fin 6) : candsb6 i = insert (b6lo i) {b6hi i} := rfl

theorem candsb6_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb6 i) :
    c ∈ Set.Icc (b6lo i) (b6hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b6lo_le_b6hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b6lo_le_b6hi i, le_rfl⟩

theorem candsb6_ne (i : Fin 6) : (candsb6 i).Nonempty := ⟨b6lo i, by
  simp only [candsb6]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 7. -/
noncomputable def candsb7 : Fin 6 → Finset ℝ :=
  fun i => insert (b7lo i) {b7hi i}

theorem candsb7_eq (i : Fin 6) : candsb7 i = insert (b7lo i) {b7hi i} := rfl

theorem candsb7_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb7 i) :
    c ∈ Set.Icc (b7lo i) (b7hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b7lo_le_b7hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b7lo_le_b7hi i, le_rfl⟩

theorem candsb7_ne (i : Fin 6) : (candsb7 i).Nonempty := ⟨b7lo i, by
  simp only [candsb7]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 8. -/
noncomputable def candsb8 : Fin 6 → Finset ℝ :=
  fun i => insert (b8lo i) {b8hi i}

theorem candsb8_eq (i : Fin 6) : candsb8 i = insert (b8lo i) {b8hi i} := rfl

theorem candsb8_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb8 i) :
    c ∈ Set.Icc (b8lo i) (b8hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b8lo_le_b8hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b8lo_le_b8hi i, le_rfl⟩

theorem candsb8_ne (i : Fin 6) : (candsb8 i).Nonempty := ⟨b8lo i, by
  simp only [candsb8]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 9. -/
noncomputable def candsb9 : Fin 6 → Finset ℝ :=
  fun i => insert (b9lo i) {b9hi i}

theorem candsb9_eq (i : Fin 6) : candsb9 i = insert (b9lo i) {b9hi i} := rfl

theorem candsb9_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb9 i) :
    c ∈ Set.Icc (b9lo i) (b9hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b9lo_le_b9hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b9lo_le_b9hi i, le_rfl⟩

theorem candsb9_ne (i : Fin 6) : (candsb9 i).Nonempty := ⟨b9lo i, by
  simp only [candsb9]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 10. -/
noncomputable def candsb10 : Fin 6 → Finset ℝ :=
  fun i => insert (b10lo i) {b10hi i}

theorem candsb10_eq (i : Fin 6) : candsb10 i = insert (b10lo i) {b10hi i} := rfl

theorem candsb10_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb10 i) :
    c ∈ Set.Icc (b10lo i) (b10hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b10lo_le_b10hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b10lo_le_b10hi i, le_rfl⟩

theorem candsb10_ne (i : Fin 6) : (candsb10 i).Nonempty := ⟨b10lo i, by
  simp only [candsb10]
  exact Finset.mem_insert_self _ _⟩

/-- The unsplit two-corner grid of box 11. -/
noncomputable def candsb11 : Fin 6 → Finset ℝ :=
  fun i => insert (b11lo i) {b11hi i}

theorem candsb11_eq (i : Fin 6) : candsb11 i = insert (b11lo i) {b11hi i} := rfl

theorem candsb11_sub (i : Fin 6) (c : ℝ) (hc : c ∈ candsb11 i) :
    c ∈ Set.Icc (b11lo i) (b11hi i) := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Set.mem_Icc.mpr ⟨le_rfl, b11lo_le_b11hi i⟩
  · rw [Finset.mem_singleton.mp h]
    exact Set.mem_Icc.mpr ⟨b11lo_le_b11hi i, le_rfl⟩

theorem candsb11_ne (i : Fin 6) : (candsb11 i).Nonempty := ⟨b11lo i, by
  simp only [candsb11]
  exact Finset.mem_insert_self _ _⟩

/-- idx 21 chain: corner bound minus the grid rebate lower-bounds the margin (box 4; REBATE coordinates per KENV). -/

theorem R21v_def (i : Fin 6) : R21 i = K21 i * (b4hi i - b4lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R21, K21, b4lo, b4hi]

theorem chain_idx21 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b4lo i) (b4hi i))
        (fun t => f (Function.update y i t) - K21 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K21 i)
    (hR0 : ∀ i, 0 ≤ R21 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb4 j) → B21 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b4lo j) (b4hi j)) :
    B21 - ∑ j, R21 j ≤ f x :=
  final_bound candsb4 candsb4_ne hR0 candsb4_sub
    (fun i y hy => by
      rw [R21v_def i]
      exact hstep_of_shifted_concave (b4lo_le_b4hi i) (hK0 i)
        (hsl i) candsb4_eq y hy)
    hcorner x hx

/-- idx 22 chain: corner bound minus the grid rebate lower-bounds the margin (box 1; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R22v_def (i : Fin 6) : R22 i = K22 i * (b1hi i - b1lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R22, K22, b1lo, b1hi]

theorem chain_idx22 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b1lo i) (b1hi i))
        (fun t => f (Function.update y i t) - K22 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K22 i)
    (hR0 : ∀ i, 0 ≤ R22 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb1 j) → B22 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b1lo j) (b1hi j)) :
    B22 - ∑ j, R22 j ≤ f x :=
  final_bound candsb1 candsb1_ne hR0 candsb1_sub
    (fun i y hy => by
      rw [R22v_def i]
      exact hstep_of_shifted_concave (b1lo_le_b1hi i) (hK0 i)
        (hsl i) candsb1_eq y hy)
    hcorner x hx

/-- idx 23 chain: corner bound minus the grid rebate lower-bounds the margin (box 1; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R23v_def (i : Fin 6) : R23 i = K23 i * (b1hi i - b1lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R23, K23, b1lo, b1hi]

theorem chain_idx23 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b1lo i) (b1hi i))
        (fun t => f (Function.update y i t) - K23 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K23 i)
    (hR0 : ∀ i, 0 ≤ R23 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb1 j) → B23 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b1lo j) (b1hi j)) :
    B23 - ∑ j, R23 j ≤ f x :=
  final_bound candsb1 candsb1_ne hR0 candsb1_sub
    (fun i y hy => by
      rw [R23v_def i]
      exact hstep_of_shifted_concave (b1lo_le_b1hi i) (hK0 i)
        (hsl i) candsb1_eq y hy)
    hcorner x hx

/-- idx 24 chain: corner bound minus the grid rebate lower-bounds the margin (box 2; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R24v_def (i : Fin 6) : R24 i = K24 i * (b2hi i - b2lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R24, K24, b2lo, b2hi]

theorem chain_idx24 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b2lo i) (b2hi i))
        (fun t => f (Function.update y i t) - K24 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K24 i)
    (hR0 : ∀ i, 0 ≤ R24 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb2 j) → B24 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b2lo j) (b2hi j)) :
    B24 - ∑ j, R24 j ≤ f x :=
  final_bound candsb2 candsb2_ne hR0 candsb2_sub
    (fun i y hy => by
      rw [R24v_def i]
      exact hstep_of_shifted_concave (b2lo_le_b2hi i) (hK0 i)
        (hsl i) candsb2_eq y hy)
    hcorner x hx

/-- idx 26 chain: corner bound minus the grid rebate lower-bounds the margin (box 4; REBATE coordinates per KENV). -/

theorem R26v_def (i : Fin 6) : R26 i = K26 i * (b4hi i - b4lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R26, K26, b4lo, b4hi]

theorem chain_idx26 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b4lo i) (b4hi i))
        (fun t => f (Function.update y i t) - K26 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K26 i)
    (hR0 : ∀ i, 0 ≤ R26 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb4 j) → B26 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b4lo j) (b4hi j)) :
    B26 - ∑ j, R26 j ≤ f x :=
  final_bound candsb4 candsb4_ne hR0 candsb4_sub
    (fun i y hy => by
      rw [R26v_def i]
      exact hstep_of_shifted_concave (b4lo_le_b4hi i) (hK0 i)
        (hsl i) candsb4_eq y hy)
    hcorner x hx

/-- idx 27 chain: corner bound minus the grid rebate lower-bounds the margin (box 1; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R27v_def (i : Fin 6) : R27 i = K27 i * (b1hi i - b1lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R27, K27, b1lo, b1hi]

theorem chain_idx27 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b1lo i) (b1hi i))
        (fun t => f (Function.update y i t) - K27 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K27 i)
    (hR0 : ∀ i, 0 ≤ R27 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb1 j) → B27 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b1lo j) (b1hi j)) :
    B27 - ∑ j, R27 j ≤ f x :=
  final_bound candsb1 candsb1_ne hR0 candsb1_sub
    (fun i y hy => by
      rw [R27v_def i]
      exact hstep_of_shifted_concave (b1lo_le_b1hi i) (hK0 i)
        (hsl i) candsb1_eq y hy)
    hcorner x hx

/-- idx 28 chain: corner bound minus the grid rebate lower-bounds the margin (box 2; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R28v_def (i : Fin 6) : R28 i = K28 i * (b2hi i - b2lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R28, K28, b2lo, b2hi]

theorem chain_idx28 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b2lo i) (b2hi i))
        (fun t => f (Function.update y i t) - K28 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K28 i)
    (hR0 : ∀ i, 0 ≤ R28 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb2 j) → B28 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b2lo j) (b2hi j)) :
    B28 - ∑ j, R28 j ≤ f x :=
  final_bound candsb2 candsb2_ne hR0 candsb2_sub
    (fun i y hy => by
      rw [R28v_def i]
      exact hstep_of_shifted_concave (b2lo_le_b2hi i) (hK0 i)
        (hsl i) candsb2_eq y hy)
    hcorner x hx

/-- idx 29 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R29v_def (i : Fin 6) : R29 i = K29 i * (b3hi i - b3lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R29, K29, b3lo, b3hi]

theorem chain_idx29 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => f (Function.update y i t) - K29 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K29 i)
    (hR0 : ∀ i, 0 ≤ R29 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B29 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b3lo j) (b3hi j)) :
    B29 - ∑ j, R29 j ≤ f x :=
  final_bound candsb3 candsb3_ne hR0 candsb3_sub
    (fun i y hy => by
      rw [R29v_def i]
      exact hstep_of_shifted_concave (b3lo_le_b3hi i) (hK0 i)
        (hsl i) candsb3_eq y hy)
    hcorner x hx

/-- idx 31 chain: corner bound minus the grid rebate lower-bounds the margin (box 4; REBATE coordinates per KENV). -/

theorem R31v_def (i : Fin 6) : R31 i = K31 i * (b4hi i - b4lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R31, K31, b4lo, b4hi]

theorem chain_idx31 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b4lo i) (b4hi i))
        (fun t => f (Function.update y i t) - K31 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K31 i)
    (hR0 : ∀ i, 0 ≤ R31 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb4 j) → B31 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b4lo j) (b4hi j)) :
    B31 - ∑ j, R31 j ≤ f x :=
  final_bound candsb4 candsb4_ne hR0 candsb4_sub
    (fun i y hy => by
      rw [R31v_def i]
      exact hstep_of_shifted_concave (b4lo_le_b4hi i) (hK0 i)
        (hsl i) candsb4_eq y hy)
    hcorner x hx

/-- idx 32 chain: corner bound minus the grid rebate lower-bounds the margin (box 2; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R32v_def (i : Fin 6) : R32 i = K32 i * (b2hi i - b2lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R32, K32, b2lo, b2hi]

theorem chain_idx32 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b2lo i) (b2hi i))
        (fun t => f (Function.update y i t) - K32 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K32 i)
    (hR0 : ∀ i, 0 ≤ R32 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb2 j) → B32 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b2lo j) (b2hi j)) :
    B32 - ∑ j, R32 j ≤ f x :=
  final_bound candsb2 candsb2_ne hR0 candsb2_sub
    (fun i y hy => by
      rw [R32v_def i]
      exact hstep_of_shifted_concave (b2lo_le_b2hi i) (hK0 i)
        (hsl i) candsb2_eq y hy)
    hcorner x hx

/-- idx 33 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R33v_def (i : Fin 6) : R33 i = K33 i * (b3hi i - b3lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R33, K33, b3lo, b3hi]

theorem chain_idx33 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => f (Function.update y i t) - K33 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K33 i)
    (hR0 : ∀ i, 0 ≤ R33 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B33 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b3lo j) (b3hi j)) :
    B33 - ∑ j, R33 j ≤ f x :=
  final_bound candsb3 candsb3_ne hR0 candsb3_sub
    (fun i y hy => by
      rw [R33v_def i]
      exact hstep_of_shifted_concave (b3lo_le_b3hi i) (hK0 i)
        (hsl i) candsb3_eq y hy)
    hcorner x hx

/-- idx 34 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R34v_def (i : Fin 6) : R34 i = K34 i * (b3hi i - b3lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R34, K34, b3lo, b3hi]

theorem chain_idx34 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => f (Function.update y i t) - K34 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K34 i)
    (hR0 : ∀ i, 0 ≤ R34 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B34 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b3lo j) (b3hi j)) :
    B34 - ∑ j, R34 j ≤ f x :=
  final_bound candsb3 candsb3_ne hR0 candsb3_sub
    (fun i y hy => by
      rw [R34v_def i]
      exact hstep_of_shifted_concave (b3lo_le_b3hi i) (hK0 i)
        (hsl i) candsb3_eq y hy)
    hcorner x hx

/-- idx 36 chain: corner bound minus the grid rebate lower-bounds the margin (box 4; REBATE coordinates per KENV). -/

theorem R36v_def (i : Fin 6) : R36 i = K36 i * (b4hi i - b4lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R36, K36, b4lo, b4hi]

theorem chain_idx36 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b4lo i) (b4hi i))
        (fun t => f (Function.update y i t) - K36 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K36 i)
    (hR0 : ∀ i, 0 ≤ R36 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb4 j) → B36 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b4lo j) (b4hi j)) :
    B36 - ∑ j, R36 j ≤ f x :=
  final_bound candsb4 candsb4_ne hR0 candsb4_sub
    (fun i y hy => by
      rw [R36v_def i]
      exact hstep_of_shifted_concave (b4lo_le_b4hi i) (hK0 i)
        (hsl i) candsb4_eq y hy)
    hcorner x hx

/-- idx 37 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R37v_def (i : Fin 6) : R37 i = K37 i * (b3hi i - b3lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R37, K37, b3lo, b3hi]

theorem chain_idx37 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => f (Function.update y i t) - K37 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K37 i)
    (hR0 : ∀ i, 0 ≤ R37 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B37 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b3lo j) (b3hi j)) :
    B37 - ∑ j, R37 j ≤ f x :=
  final_bound candsb3 candsb3_ne hR0 candsb3_sub
    (fun i y hy => by
      rw [R37v_def i]
      exact hstep_of_shifted_concave (b3lo_le_b3hi i) (hK0 i)
        (hsl i) candsb3_eq y hy)
    hcorner x hx

/-- idx 38 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R38v_def (i : Fin 6) : R38 i = K38 i * (b3hi i - b3lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R38, K38, b3lo, b3hi]

theorem chain_idx38 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => f (Function.update y i t) - K38 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K38 i)
    (hR0 : ∀ i, 0 ≤ R38 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B38 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b3lo j) (b3hi j)) :
    B38 - ∑ j, R38 j ≤ f x :=
  final_bound candsb3 candsb3_ne hR0 candsb3_sub
    (fun i y hy => by
      rw [R38v_def i]
      exact hstep_of_shifted_concave (b3lo_le_b3hi i) (hK0 i)
        (hsl i) candsb3_eq y hy)
    hcorner x hx

/-- idx 39 chain: corner bound minus the grid rebate lower-bounds the margin (box 3; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R39v_def (i : Fin 6) : R39 i = K39 i * (b3hi i - b3lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R39, K39, b3lo, b3hi]

theorem chain_idx39 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b3lo i) (b3hi i))
        (fun t => f (Function.update y i t) - K39 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K39 i)
    (hR0 : ∀ i, 0 ≤ R39 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb3 j) → B39 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b3lo j) (b3hi j)) :
    B39 - ∑ j, R39 j ≤ f x :=
  final_bound candsb3 candsb3_ne hR0 candsb3_sub
    (fun i y hy => by
      rw [R39v_def i]
      exact hstep_of_shifted_concave (b3lo_le_b3hi i) (hK0 i)
        (hsl i) candsb3_eq y hy)
    hcorner x hx

/-- idx 41 chain: corner bound minus the grid rebate lower-bounds the margin (box 5; REBATE coordinates per KENV). -/

theorem b2R41v_def (i : Fin 6) : b2R41 i = b2K41 i * (b5hi i - b5lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [b2R41, b2K41, b5lo, b5hi]

theorem chain_idx41b2 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b5lo i) (b5hi i))
        (fun t => f (Function.update y i t) - b2K41 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ b2K41 i)
    (hR0 : ∀ i, 0 ≤ b2R41 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb5 j) → b2B41 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b5lo j) (b5hi j)) :
    b2B41 - ∑ j, b2R41 j ≤ f x :=
  final_bound candsb5 candsb5_ne hR0 candsb5_sub
    (fun i y hy => by
      rw [b2R41v_def i]
      exact hstep_of_shifted_concave (b5lo_le_b5hi i) (hK0 i)
        (hsl i) candsb5_eq y hy)
    hcorner x hx

/-- idx 42 chain: corner bound minus the grid rebate lower-bounds the margin (box 6; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R42v_def (i : Fin 6) : R42 i = K42 i * (b6hi i - b6lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R42, K42, b6lo, b6hi]

theorem chain_idx42 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => f (Function.update y i t) - K42 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K42 i)
    (hR0 : ∀ i, 0 ≤ R42 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B42 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b6lo j) (b6hi j)) :
    B42 - ∑ j, R42 j ≤ f x :=
  final_bound candsb6 candsb6_ne hR0 candsb6_sub
    (fun i y hy => by
      rw [R42v_def i]
      exact hstep_of_shifted_concave (b6lo_le_b6hi i) (hK0 i)
        (hsl i) candsb6_eq y hy)
    hcorner x hx

/-- idx 43 chain: corner bound minus the grid rebate lower-bounds the margin (box 6; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R43v_def (i : Fin 6) : R43 i = K43 i * (b6hi i - b6lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R43, K43, b6lo, b6hi]

theorem chain_idx43 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => f (Function.update y i t) - K43 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K43 i)
    (hR0 : ∀ i, 0 ≤ R43 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B43 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b6lo j) (b6hi j)) :
    B43 - ∑ j, R43 j ≤ f x :=
  final_bound candsb6 candsb6_ne hR0 candsb6_sub
    (fun i y hy => by
      rw [R43v_def i]
      exact hstep_of_shifted_concave (b6lo_le_b6hi i) (hK0 i)
        (hsl i) candsb6_eq y hy)
    hcorner x hx

/-- idx 44 chain: corner bound minus the grid rebate lower-bounds the margin (box 7; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R44v_def (i : Fin 6) : R44 i = K44 i * (b7hi i - b7lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R44, K44, b7lo, b7hi]

theorem chain_idx44 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => f (Function.update y i t) - K44 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K44 i)
    (hR0 : ∀ i, 0 ≤ R44 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B44 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b7lo j) (b7hi j)) :
    B44 - ∑ j, R44 j ≤ f x :=
  final_bound candsb7 candsb7_ne hR0 candsb7_sub
    (fun i y hy => by
      rw [R44v_def i]
      exact hstep_of_shifted_concave (b7lo_le_b7hi i) (hK0 i)
        (hsl i) candsb7_eq y hy)
    hcorner x hx

/-- idx 46 chain: corner bound minus the grid rebate lower-bounds the margin (box 5; REBATE coordinates per KENV). -/

theorem R46v_def (i : Fin 6) : R46 i = K46 i * (b5hi i - b5lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R46, K46, b5lo, b5hi]

theorem chain_idx46b2 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b5lo i) (b5hi i))
        (fun t => f (Function.update y i t) - K46 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K46 i)
    (hR0 : ∀ i, 0 ≤ R46 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb5 j) → b2B46 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b5lo j) (b5hi j)) :
    b2B46 - ∑ j, R46 j ≤ f x :=
  final_bound candsb5 candsb5_ne hR0 candsb5_sub
    (fun i y hy => by
      rw [R46v_def i]
      exact hstep_of_shifted_concave (b5lo_le_b5hi i) (hK0 i)
        (hsl i) candsb5_eq y hy)
    hcorner x hx

/-- idx 47 chain: corner bound minus the grid rebate lower-bounds the margin (box 6; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R47v_def (i : Fin 6) : R47 i = K47 i * (b6hi i - b6lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R47, K47, b6lo, b6hi]

theorem chain_idx47 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b6lo i) (b6hi i))
        (fun t => f (Function.update y i t) - K47 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K47 i)
    (hR0 : ∀ i, 0 ≤ R47 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb6 j) → B47 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b6lo j) (b6hi j)) :
    B47 - ∑ j, R47 j ≤ f x :=
  final_bound candsb6 candsb6_ne hR0 candsb6_sub
    (fun i y hy => by
      rw [R47v_def i]
      exact hstep_of_shifted_concave (b6lo_le_b6hi i) (hK0 i)
        (hsl i) candsb6_eq y hy)
    hcorner x hx

/-- idx 48 chain: corner bound minus the grid rebate lower-bounds the margin (box 7; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R48v_def (i : Fin 6) : R48 i = K48 i * (b7hi i - b7lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R48, K48, b7lo, b7hi]

theorem chain_idx48 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => f (Function.update y i t) - K48 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K48 i)
    (hR0 : ∀ i, 0 ≤ R48 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B48 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b7lo j) (b7hi j)) :
    B48 - ∑ j, R48 j ≤ f x :=
  final_bound candsb7 candsb7_ne hR0 candsb7_sub
    (fun i y hy => by
      rw [R48v_def i]
      exact hstep_of_shifted_concave (b7lo_le_b7hi i) (hK0 i)
        (hsl i) candsb7_eq y hy)
    hcorner x hx

/-- idx 49 chain: corner bound minus the grid rebate lower-bounds the margin (box 8; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R49v_def (i : Fin 6) : R49 i = K49 i * (b8hi i - b8lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R49, K49, b8lo, b8hi]

theorem chain_idx49 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => f (Function.update y i t) - K49 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K49 i)
    (hR0 : ∀ i, 0 ≤ R49 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B49 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b8lo j) (b8hi j)) :
    B49 - ∑ j, R49 j ≤ f x :=
  final_bound candsb8 candsb8_ne hR0 candsb8_sub
    (fun i y hy => by
      rw [R49v_def i]
      exact hstep_of_shifted_concave (b8lo_le_b8hi i) (hK0 i)
        (hsl i) candsb8_eq y hy)
    hcorner x hx

/-- idx 51 chain: corner bound minus the grid rebate lower-bounds the margin (box 5; REBATE coordinates per KENV). -/

theorem R51v_def (i : Fin 6) : R51 i = K51 i * (b5hi i - b5lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R51, K51, b5lo, b5hi]

theorem chain_idx51 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b5lo i) (b5hi i))
        (fun t => f (Function.update y i t) - K51 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K51 i)
    (hR0 : ∀ i, 0 ≤ R51 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb5 j) → B51 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b5lo j) (b5hi j)) :
    B51 - ∑ j, R51 j ≤ f x :=
  final_bound candsb5 candsb5_ne hR0 candsb5_sub
    (fun i y hy => by
      rw [R51v_def i]
      exact hstep_of_shifted_concave (b5lo_le_b5hi i) (hK0 i)
        (hsl i) candsb5_eq y hy)
    hcorner x hx

/-- idx 52 chain: corner bound minus the grid rebate lower-bounds the margin (box 7; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R52v_def (i : Fin 6) : R52 i = K52 i * (b7hi i - b7lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R52, K52, b7lo, b7hi]

theorem chain_idx52 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b7lo i) (b7hi i))
        (fun t => f (Function.update y i t) - K52 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K52 i)
    (hR0 : ∀ i, 0 ≤ R52 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb7 j) → B52 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b7lo j) (b7hi j)) :
    B52 - ∑ j, R52 j ≤ f x :=
  final_bound candsb7 candsb7_ne hR0 candsb7_sub
    (fun i y hy => by
      rw [R52v_def i]
      exact hstep_of_shifted_concave (b7lo_le_b7hi i) (hK0 i)
        (hsl i) candsb7_eq y hy)
    hcorner x hx

/-- idx 53 chain: corner bound minus the grid rebate lower-bounds the margin (box 8; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R53v_def (i : Fin 6) : R53 i = K53 i * (b8hi i - b8lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R53, K53, b8lo, b8hi]

theorem chain_idx53 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => f (Function.update y i t) - K53 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K53 i)
    (hR0 : ∀ i, 0 ≤ R53 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B53 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b8lo j) (b8hi j)) :
    B53 - ∑ j, R53 j ≤ f x :=
  final_bound candsb8 candsb8_ne hR0 candsb8_sub
    (fun i y hy => by
      rw [R53v_def i]
      exact hstep_of_shifted_concave (b8lo_le_b8hi i) (hK0 i)
        (hsl i) candsb8_eq y hy)
    hcorner x hx

/-- idx 54 chain: corner bound minus the grid rebate lower-bounds the margin (box 8; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R54v_def (i : Fin 6) : R54 i = K54 i * (b8hi i - b8lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R54, K54, b8lo, b8hi]

theorem chain_idx54 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b8lo i) (b8hi i))
        (fun t => f (Function.update y i t) - K54 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K54 i)
    (hR0 : ∀ i, 0 ≤ R54 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb8 j) → B54 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b8lo j) (b8hi j)) :
    B54 - ∑ j, R54 j ≤ f x :=
  final_bound candsb8 candsb8_ne hR0 candsb8_sub
    (fun i y hy => by
      rw [R54v_def i]
      exact hstep_of_shifted_concave (b8lo_le_b8hi i) (hK0 i)
        (hsl i) candsb8_eq y hy)
    hcorner x hx

/-- idx 56 chain: corner bound minus the grid rebate lower-bounds the margin (box 9; REBATE coordinates per KENV). -/

theorem R56v_def (i : Fin 6) : R56 i = K56 i * (b9hi i - b9lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R56, K56, b9lo, b9hi]

theorem chain_idx56 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b9lo i) (b9hi i))
        (fun t => f (Function.update y i t) - K56 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K56 i)
    (hR0 : ∀ i, 0 ≤ R56 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb9 j) → B56 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b9lo j) (b9hi j)) :
    B56 - ∑ j, R56 j ≤ f x :=
  final_bound candsb9 candsb9_ne hR0 candsb9_sub
    (fun i y hy => by
      rw [R56v_def i]
      exact hstep_of_shifted_concave (b9lo_le_b9hi i) (hK0 i)
        (hsl i) candsb9_eq y hy)
    hcorner x hx

/-- idx 57 chain: corner bound minus the grid rebate lower-bounds the margin (box 10; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R57v_def (i : Fin 6) : R57 i = K57 i * (b10hi i - b10lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R57, K57, b10lo, b10hi]

theorem chain_idx57 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => f (Function.update y i t) - K57 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K57 i)
    (hR0 : ∀ i, 0 ≤ R57 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B57 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b10lo j) (b10hi j)) :
    B57 - ∑ j, R57 j ≤ f x :=
  final_bound candsb10 candsb10_ne hR0 candsb10_sub
    (fun i y hy => by
      rw [R57v_def i]
      exact hstep_of_shifted_concave (b10lo_le_b10hi i) (hK0 i)
        (hsl i) candsb10_eq y hy)
    hcorner x hx

/-- idx 58 chain: corner bound minus the grid rebate lower-bounds the margin (box 10; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R58v_def (i : Fin 6) : R58 i = K58 i * (b10hi i - b10lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R58, K58, b10lo, b10hi]

theorem chain_idx58 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b10lo i) (b10hi i))
        (fun t => f (Function.update y i t) - K58 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K58 i)
    (hR0 : ∀ i, 0 ≤ R58 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb10 j) → B58 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b10lo j) (b10hi j)) :
    B58 - ∑ j, R58 j ≤ f x :=
  final_bound candsb10 candsb10_ne hR0 candsb10_sub
    (fun i y hy => by
      rw [R58v_def i]
      exact hstep_of_shifted_concave (b10lo_le_b10hi i) (hK0 i)
        (hsl i) candsb10_eq y hy)
    hcorner x hx

/-- idx 59 chain: corner bound minus the grid rebate lower-bounds the margin (box 11; ALL-CONCAVE, no rebate (K = 0)). -/

theorem R59v_def (i : Fin 6) : R59 i = K59 i * (b11hi i - b11lo i) ^ 2 / 8 := by
  fin_cases i <;> norm_num [R59, K59, b11lo, b11hi]

theorem chain_idx59 (f : (Fin 6 → ℝ) → ℝ)
    (hsl : ∀ (i : Fin 6) (y : Fin 6 → ℝ),
      ConcaveOn ℝ (Set.Icc (b11lo i) (b11hi i))
        (fun t => f (Function.update y i t) - K59 i / 2 * t * t))
    (hK0 : ∀ i, 0 ≤ K59 i)
    (hR0 : ∀ i, 0 ≤ R59 i)
    (hcorner : ∀ v : Fin 6 → ℝ, (∀ j, v j ∈ candsb11 j) → B59 ≤ f v)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (b11lo j) (b11hi j)) :
    B59 - ∑ j, R59 j ≤ f x :=
  final_bound candsb11 candsb11_ne hR0 candsb11_sub
    (fun i y hy => by
      rw [R59v_def i]
      exact hstep_of_shifted_concave (b11lo_le_b11hi i) (hK0 i)
        (hsl i) candsb11_eq y hy)
    hcorner x hx

/-! ### Axiom audit -/


#print axioms chain_idx21

#print axioms chain_idx22

#print axioms chain_idx23

#print axioms chain_idx24

#print axioms chain_idx26

#print axioms chain_idx27

#print axioms chain_idx28

#print axioms chain_idx29

#print axioms chain_idx31

#print axioms chain_idx32

#print axioms chain_idx33

#print axioms chain_idx34

#print axioms chain_idx36

#print axioms chain_idx37

#print axioms chain_idx38

#print axioms chain_idx39

#print axioms chain_idx41

#print axioms chain_idx42

#print axioms chain_idx43

#print axioms chain_idx44

#print axioms chain_idx46

#print axioms chain_idx47

#print axioms chain_idx48

#print axioms chain_idx49

#print axioms chain_idx51

#print axioms chain_idx52

#print axioms chain_idx53

#print axioms chain_idx54

#print axioms chain_idx56

#print axioms chain_idx57

#print axioms chain_idx58

#print axioms chain_idx59

end Kepler.Text
