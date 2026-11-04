/-
Kepler.Text.PackingConcl — ASSEMBLY file: discharges the `pack_concl.hl`
interface statements of `Kepler.Text.PackingAuto2` (and the `OXLZLEZ1.hl`
family of `PackingAuto3`) from their downstream twins.

WHY AN ASSEMBLY FILE
  Every sorried `*_concl` in PackingAuto2 names a downstream twin that is
  supposed to discharge it, but the twins live in files that IMPORT
  PackingAuto2 (PackingAuto4-25), so Auto2 cannot cite them without an
  import cycle.  This file imports the full chain and performs the
  discharges.

MODE (2026-09-21, end-to-end assembly turn)
  The spine is truthy: `Kepler/Assembly.lean`'s `textCapstone` consumes
  `PackingAuto25.PACKING_CHAPTER_MAIN_CONCLUSION`.  An entry here therefore
  no longer mirrors the upstream `sorry`; it APPLIES the downstream twin
  (`exact twin ...`) even when that twin's own proof is still sorryAx-
  tainted — the axiom flows along the proof term, so this file's debt
  graph is the real reachable-debt expansion of the chapter.  An entry
  keeps `sorry` only when NO twin exists or the twin's shape genuinely
  mismatches (the mismatch is documented at the entry).

LEDGER (honest accounting; ground truth = `#print axioms`, not prose)
  Sorried `*_concl` interfaces found .................... 62
    PackingAuto2 (pack_concl.hl family) .................. 46
      (recount 2026-10-08: 7 of the 53 `*_concl` interfaces are now
      term-proved in place upstream — `GLTVHUM_concl`, `DUUNHOR_concl`,
      `OAPVION1-3_concl`, `RDWKARC_concl`, and `RHWVGNP_concl`
      (from `VORONOI_POLYHEDRON_concl`) — leaving 46 sorried)
    PackingAuto3 (OXLZLEZ1.hl family) ..................... 9
    PackingAuto24 (`GRUTOTI1_concl_p24`) .................. 1
      (private statement-copy of Auto2's `GRUTOTI1_concl`, re-exported
      publicly as `GRUTOTI1_concl_p24_pub`; accounted by the GRUTOTI1
      entry below — 61 explicit entries + this 1 accounted copy = 62)
  WIRED here (`exact twin ...`, sorryAx flows through where the twin or
  a bank antecedent is sorried) ........................ 54
    verbatim twin (term-level `:= twin` / eta) ........... 49
      (DUUNHOR joined in the 2026-10-08 r2 wave; recount also fixes the
      former 47+5≠53 arithmetic — 49 + 5 = 54.  The 9 Auto3
      OXLZLEZ1-family rows went verbatim in the CC4P4-exposure wave: PA4
      now states public `*_v11` twins over PA3's `CcV11`, so the
      parallel-private-encoding block is gone)
    shim/bridge ........................................... 5
      VORONOI_BALL2  <- PackingAuto5.VORONOI_BALL2 (discard unused
        `Packing V` / `v ∈ V`)
      MHFTTZN4       <- PackingAuto6.MHFTTZN4 (rewrite `q` to the
        circumcenter)
      KHEJKCI        <- PackingAuto6.KHEJKCI (`vorList` → `.1 barV`)
      KIZHLTL1       <- PackingAuto16.KIZHLTL1 (its public
        `voronoiOpenP16` is delta-equal to Auto2's PRIVATE
        `voronoiOpen`; statement here carries the unfolded body)
      OXLZLEZ        <- PackingAuto25.OXLZLEZ (the twin's two bank
        antecedents `pack_nonlinear_non_ox3q1h`/`ox3q1hP25` are
        upstream `Prop := sorry` placeholders — supplied `by sorry`
        here, so the twin's REAL by_contra kernel
        (CELL_CLUSTER_ESTIMATE_PROPS + GRHIDFA_concl) is on the
        reachable path)
  BLOCKED ............................................... 8, reasons:

  (a) Twin does not exist: 2
      RVFXZBU1_concl, RVFXZBU2_concl (Auto2:743,750; no twin anywhere
      in Auto3-25).

  (b) Twin exists but is NOT statement-compatible (shape mismatch,
      documented at the entry): 5
      XYOFCGX (twin needs `Packing V`, interface has none);
      IVFICRK (twin's second conjunct has two extra antecedents
        `i ∈ Icc 0 (k+1)`, `permutes σ (Icc 0 k)`);
      RVFXZBU3 (twin PA10.RVFXZBU is restricted to `i ∈ {0,1,2,3,4}`,
        interface quantifies over all `i`);
      MXI_EXISTS (PA12.MXI_EXPLICIT consumes this very interface —
        self-loop — and needs `ul = [u0,u1,u2,u3]` plus
        `hl (truncateSimplex 2 ul) < sqrt 2`, none carried);
      GOTCJAH (PA22.GOTCJAH is a different encoding: `fchanged c = WF`
        vs `topologicalComponentYfan`, `asn` vs `Real.arcsin`,
        `0 ∈ interior P` + facet-cardinality vs the interface's
        nonempty-facet/component hypotheses; PA22 not imported).

  (c) Twin exists only in a parallel PRIVATE encoding: 0 (was 9 — the
      whole Auto3 OXLZLEZ1.hl family: CHQSQEY, MTMLSRF, LXDEYBO,
      UNPNFVW, IPVICGW, RSIWAMP, UTEOITF, LUIKGMH, GRHIDFA_concl.
      RESOLVED: PA4's twins live over a private `structure CC4P4`, but
      PA4 now additionally states the nine rows as public `*_v11`
      theorems over PA3's `CcV11` — imported, wired above).

IMPORT SET
  PackingAuto 2,3,4,5,6,7,8,9,10,11,12,13,16,17,19,21,24,25 plus
  the transitive closure 14,15,18,20 (via 17/19/21/25 — the PA25 cc-block
  delegation and PA21/PA25 bring PA18/PA20 in anyway; neither hosts a
  twin).  PA4 joined in the CC4P4-exposure wave: its nine OXLZLEZ2 twins
  gained public `CcV11`-stated `*_v11` copies (PA4 imports PA3 —
  clash-free, PA3's closure is PA2/Polytope/Statement/Mathlib only).
  Deliberately NOT imported:
    PackingAuto1  — Space3-based `saturated`/`Packing` CLASH by full name
                    with the Auto2 encodings; no module can import both.
    PackingAuto22 — hosts only the shape-mismatched GOTCJAH twin; kept
                    out to hold the closure clash-free.
    PackingAuto23 — joined 2026-11-03 (lane island-wire-w1): its proved
                    `GRUTOTI` capstone (GT-5/GT-6, GRUTOTI.hl:60-8001) is the
                    shape-verbatim implementation of Auto2's
                    `GRUTOTI1_concl` interface; its import closure
                    {PA2, ConicCapVolume, PA6, PA12, PA15, PA17} is already
                    inside this file's transitive set, so the addition is
                    clash-free (standalone `-o` re-verified).
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto3
import Kepler.Text.PackingAuto4
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto9
import Kepler.Text.PackingAuto10
import Kepler.Text.PackingAuto11
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto13
import Kepler.Text.PackingAuto16
import Kepler.Text.PackingAuto17
import Kepler.Text.PackingAuto19
import Kepler.Text.PackingAuto21
import Kepler.Text.PackingAuto23
import Kepler.Text.PackingAuto24
import Kepler.Text.PackingAuto25

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory EuclideanGeometry

/-! ### PA25 materialization capstone (lane lv1112-w1, 2026-11-04, after the leftover-mat-scout-2 workorder LV11):
the 60 public top-level PackingAuto25 clean theorem exits (scout seeds_clean.txt PA25 group; the 21 sorried
`real_model_*` / `CC_3_SUM_*` / `leaf_CIHTIUM` / `GAMMAX_008*` family exits are NOT included -- their debt is carried by the
double-upstream stubs `pack_nonlinear_non_ox3q1h` (PackingAuto21:147) and `ox3q1hP25` (PackingAuto25:90 `Prop := sorry`,
Oxl_def.hl not ported) per the scout verdict table), of which 60 are statable from PackingConcl and are
re-exposed as ONE conjunction below; 0 exits are dropped per the no-forcing rule (each drop named in the
theorem docstring).
Self-contained section: pure insertion, zero new imports (PA25 already imported at :125), zero proof obligations
(body = the exit assembly itself), own `#print axioms` probe (the shared pa21 footer untouched; the lv910
PA4/PA15 sections below/above are untouched -- hunk-level disjoint).
The scoped heartbeat raise mirrors the lv910 PA4 section in this file: a conjunction statement of this size exceeds
the default 200000 budget during statement elaboration (lv910 measured; pa21 capstone uses 50000000).
-/

set_option maxHeartbeats 50000000 in

/-- PA25 materialization capstone (scout lane leftover-mat-scout-2
workorder LV11, implementation lane lv1112-w1, 2026-11-04).  The
60 public top-level Kepler.Text.PackingAuto25 theorem exits unreachable from every
e2e root (scout probe1/probe2: GROUP_VS_CONE fresh sorried-0, standard-three
axiom face on the axprobe sample); 60 of them are statable from
PackingConcl and are re-exposed as ONE conjunction.
Implemented here: 60 of the 60.
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its Kepler.Text.PackingAuto25 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the first depth-0 `:=` by the generator gen_items.py,
bracket-balance guarded); compiler-generated equation/aux lemmas have no
source statement anywhere, so their conjunct is the `#check @name` printer
dump verbatim and each passes a per-item sigtest (the `⟨...⟩` assembly below
must unify it definitionally with the constant's type; printer dumps with
proof-term elision `...` are dropped per the lv12-w1 t_eqlemma_microtest
evidence, each drop named above).  Semantic identity of every conjunct is
re-verified by that assembly (each element must have exactly its conjunct's
type); the per-conjunct comments carry each exit's Kepler.Text.PackingAuto25 declaration
line and file-local docstring HOL anchor.  Conjunct order: the scout
seed-list order (probe1 SEED list).  Body = the assembly of the exit
constants -- zero new proof obligations, zero new imports. -/
theorem pa25_wire_capstone_w1 :
    -- 1. Kepler.Text.AFF_DEP_COPLANAR (Kepler.Text.PackingAuto25:13347; HOL `AFF_DEP_COPLANAR`)
    (∀ (a b c d : V3)
          (hc : Set.ncard ({a, b, c, d} : Set V3) = 4),
    (affineDependent ({a, b, c, d} : Set V3) ↔ Coplanar ({a, b, c, d} : Set V3))
    ) ∧
    -- 2. Kepler.Text.AZIM_ZERO_SHIFT (Kepler.Text.PackingAuto25:13229; HOL `AZIM_ZERO_SHIFT`)
    (∀ (u0 u1 u2 w w' : V3)
          (h1 : ¬ Collinear3 u0 u1 u2) (h2 : ¬ Collinear3 u0 u1 w)
          (h3 : ¬ Collinear3 u0 u1 w'),
    (azim u0 u1 u2 w = azim u0 u1 u2 w' ↔ azim u0 u1 w w' = 0)
    ) ∧
    -- 3. Kepler.Text.CARD_INSERT_INTER_ALT (Kepler.Text.PackingAuto25:474; HOL `CARD_INSERT_INTER_ALT`)
    (∀ {α : Type*} (a : α) (A B : Set α) (hB : B.Finite),
    Set.ncard ((insert a A) ∩ B) =
          (if a ∈ B ∧ a ∉ A then 1 else 0) + Set.ncard (A ∩ B)
    ) ∧
    -- 4. Kepler.Text.CC_4_BETA_BUMP_EXPLICIT (Kepler.Text.PackingAuto25:7951; HOL `CC_4_BETA_BUMP_EXPLICIT`)
    (∀ (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
          (i : ℕ) (hp : Packing V) (hs : saturated V)
          (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n)
          (h4 : cc_4 V u0 u1 f i) (hcey : criticalEdgeY (dist u0 u1))
          (hcey' : criticalEdgeY (dist (f i) (f (i + 1))))
          (hd1 : dist u0 (f i) < 2 * hminus) (hd2 : dist u0 (f (i + 1)) < 2 * hminus)
          (hd3 : dist u1 (f i) < 2 * hminus) (hd4 : dist u1 (f (i + 1)) < 2 * hminus),
    betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) =
          bump (dist u0 u1 / 2) - bump (dist (f i) (f (i + 1)) / 2)
    ) ∧
    -- 5. Kepler.Text.COPLANAR_CONVEX_HULL_COPLANAR (Kepler.Text.PackingAuto25:673; HOL `COPLANAR_CONVEX_HULL_COPLANAR`)
    (∀ (s : Set V3),
    Coplanar (convexHull ℝ s) ↔ Coplanar s
    ) ∧
    -- 6. Kepler.Text.DIHV_EQ_0_PI_EQ_COPLANAR_ALT (Kepler.Text.PackingAuto25:13149; HOL `DIHV_EQ_0_PI_EQ_COPLANAR_ALT`)
    (∀ (v0 v1 w1 w2 : V3)
          (hnc : ¬ Coplanar ({v0, v1, w1, w2} : Set V3)),
    ¬ (dihV v0 v1 w1 w2 = 0)
    ) ∧
    -- 7. Kepler.Text.DIHV_EQ_0_PI_EQ_COPLANAR_ALT._abel_1_3 (Kepler.Text.PackingAuto25:13149; compiler-generated equation/aux lemma (parent def `DIHV_EQ_0_PI_EQ_COPLANAR_ALT` at Kepler.Text.PackingAuto25:13149; no source statement; sigtest = assembly elaboration))
    (∀ (v0 x : V3), x - v0 + v0 = x
    ) ∧
    -- 8. Kepler.Text.DIHV_EQ_0_PI_EQ_COPLANAR_ALT._abel_1_4 (Kepler.Text.PackingAuto25:13149; compiler-generated equation/aux lemma (parent def `DIHV_EQ_0_PI_EQ_COPLANAR_ALT` at Kepler.Text.PackingAuto25:13149; no source statement; sigtest = assembly elaboration))
    (∀ (v0 w1 : V3), w1 = v0 + (w1 - v0)
    ) ∧
    -- 9. Kepler.Text.DIST_IMP_COLLINEAR (Kepler.Text.PackingAuto25:1582; HOL `DIST_IMP_COLLINEAR`)
    (∀ (u0 u1 u2 : V3)
          (h1 : 2 ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) (h3 : 2 ≤ dist u1 u2)
          (h4 : dist u0 u1 < 4) (h5 : dist u0 u2 < 4) (h6 : dist u1 u2 < 4),
    ¬ Collinear3 u0 u1 u2
    ) ∧
    -- 10. Kepler.Text.DIST_IMP_COLLINEAR._abel_1_1 (Kepler.Text.PackingAuto25:1582; compiler-generated equation/aux lemma (parent def `DIST_IMP_COLLINEAR` at Kepler.Text.PackingAuto25:1582; no source statement; sigtest = assembly elaboration))
    (∀ (u0 u1 u2 : V3), u1 - u2 = u1 - u0 - (u2 - u0)
    ) ∧
    -- 11. Kepler.Text.DIST_IMP_UPS_X_POS (Kepler.Text.PackingAuto25:1645; HOL `DIST_IMP_UPS_X_POS`)
    (∀ (u0 u1 u2 : V3)
          (h1 : 2 ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) (h3 : 2 ≤ dist u1 u2)
          (h4 : dist u0 u1 < 4) (h5 : dist u0 u2 < 4) (h6 : dist u1 u2 < 4),
    0 < upsX (dist u0 u1 ^ 2) (dist u0 u2 ^ 2) (dist u1 u2 ^ 2)
    ) ∧
    -- 12. Kepler.Text.DIST_IMP_UPS_X_POS._abel_1_1 (Kepler.Text.PackingAuto25:1645; compiler-generated equation/aux lemma (parent def `DIST_IMP_UPS_X_POS` at Kepler.Text.PackingAuto25:1645; no source statement; sigtest = assembly elaboration))
    (∀ (u0 u1 u2 : V3), u1 - u0 - (u2 - u0) = u1 - u2
    ) ∧
    -- 13. Kepler.Text.EDGEX_PAIR (Kepler.Text.PackingAuto25:7430; HOL `EDGEX_PAIR`)
    (∀ (V : Set V3) (X : Set V3) (e : Set V3) (he : e ∈ edgeX V X),
    ∃ u v : V3, e = {u, v} ∧ u ≠ v
    ) ∧
    -- 14. Kepler.Text.ETA_Y_LEMMA (Kepler.Text.PackingAuto25:8851; HOL `ETA_Y_LEMMA`)
    (∀ (u0 u1 u2 : V3) (r : ℝ) (hnc : ¬ Collinear3 u0 u1 u2)
          (hr : 0 < r) (hrl : r ≤ hl [u0, u1, u2]),
    r ^ 2 ≤ eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) ^ 2
    ) ∧
    -- 15. Kepler.Text.ETA_Y_LEMMA_ALT (Kepler.Text.PackingAuto25:8866; HOL `ETA_Y_LEMMA_ALT`)
    (∀ (u0 u1 u2 : V3) (r : ℝ) (hnc : ¬ Collinear3 u0 u1 u2)
          (hrl : hl [u0, u1, u2] ≤ r),
    eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) ^ 2 ≤ r ^ 2
    ) ∧
    -- 16. Kepler.Text.FM_DEMOD (Kepler.Text.PackingAuto25:904; HOL `FM_DEMOD`)
    (∀ {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n) (hn : 1 < n)
          (i : ℕ),
    f (i % n) = f i ∧ f (i % n + n - 1) = f (i + n - 1)
    ) ∧
    -- 17. Kepler.Text.GAMMAX_NO_BETA (Kepler.Text.PackingAuto25:1793; HOL `GAMMAX_NO_BETA`)
    (∀ (V : Set V3) (ul : List V3) (X : Set V3) (e : Set V3) (k : ℕ)
          (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell k V ul)
          (hn : ¬ nullSet X) (hk : k < 4) (he : e ∈ criticalEdgeX V X)
          (hg : gammaX V X lmfun ≥ 0),
    gammaX V X lmfun * criticalWeight V X + betaBumpV1 V e X ≥ 0
    ) ∧
    -- 18. Kepler.Text.INITIAL_SUBLIST_TRUNCATE (Kepler.Text.PackingAuto25:13312; HOL `INITIAL_SUBLIST_TRUNCATE`)
    (∀ (vl ul : List V3) (hl : ul.length = 4)
          (h1 : initialSublist vl ul)
          (h2 : ¬ initialSublist vl (truncateSimplex 2 ul)),
    vl = ul
    ) ∧
    -- 19. Kepler.Text.IXPOTPA_MERGED (Kepler.Text.PackingAuto25:12450; HOL `IXPOTPA_MERGED`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
          (hcey : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
          (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
          (hb4 : Real.sqrt 8 ≤ y4) (hb4' : y4 ≤ y5 + y6)
          (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus) (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus)
          (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
          (hdi1 : dihY y1 y2 y3 y4 y5 y6 ≤ 2.089)
          (hdi2 : 1.946 ≤ dihY y1 y2 y3 y4 y5 y6)
          (he1 : eta_y y1 y2 y6 ^ 2 ≤ 1.34 ^ 2) (he2 : eta_y y1 y3 y5 ^ 2 ≤ 1.34 ^ 2),
    3 * 0.0057 ≤ gamma3f y1 y2 y6 (Real.sqrt 2) lmfun +
          gamma3f y1 y3 y5 (Real.sqrt 2) lmfun +
          (dihY y1 y2 y3 y4 y5 y6 -
              (dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 +
                dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2))) * 0.008
    ) ∧
    -- 20. Kepler.Text.JSP_BOUNDS (Kepler.Text.PackingAuto25:12115; HOL `JSP_BOUNDS`)
    (∀ (u0 u1 u2 : V3) (hnl : pack_nonlinear_non_ox3q1h)
          (hnc : ¬ Collinear3 u0 u1 u2) (hhl : hl [u0, u1, u2] ≤ 1.34)
          (h1 : 2 * hminus ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) (h3 : 2 ≤ dist u1 u2),
    dist u0 u2 < 2 * hminus ∧ dist u1 u2 < 2 * hminus
    ) ∧
    -- 21. Kepler.Text.LEAF_RANKING_LEMMA (Kepler.Text.PackingAuto25:2105; HOL `LEAF_RANKING_LEMMA`)
    (∀ (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
          (hn : 0 < n) (hp : Packing V) (hs : saturated V)
          (hsize : HasSizeP25 (s_leaf V ul) n) (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0),
    ∃ f : ℕ → V3, f '' (univ : Set ℕ) = s_leaf V ul ∧
          (∀ i, f (i + n) = f i) ∧
          (∀ i j, i < n → j < n → i < j →
            azim (elV ul 0) (elV ul 1) w0 (f i) < azim (elV ul 0) (elV ul 1) w0 (f j))
    ) ∧
    -- 22. Kepler.Text.LEAF_RANK_TRUNCATE (Kepler.Text.PackingAuto25:4721; HOL `LEAF_RANK_TRUNCATE`)
    (∀ (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3),
    leaf_rank V ul w0 n f = leaf_rank V [elV ul 0, elV ul 1] w0 n f
    ) ∧
    -- 23. Kepler.Text.MCELL2_CRITICAL_WEIGHT1 (Kepler.Text.PackingAuto25:11932; HOL `MCELL2_CRITICAL_WEIGHT1`)
    (∀ (V : Set V3) (X : Set V3) (u0 u1 : V3)
          (vl : List V3) (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V)
          (hs : saturated V) (hcey : criticalEdgeY (dist u0 u1))
          (hX : X = mcell2 V vl) (he : {u0, u1} ∈ edgeX V X) (hb : barV V 3 vl),
    criticalWeight V X = 1
    ) ∧
    -- 24. Kepler.Text.MCELL3_CRITICAL_WEIGHT (Kepler.Text.PackingAuto25:11967; HOL `MCELL3_CRITICAL_WEIGHT`)
    (∀ (V : Set V3) (X : Set V3) (u0 u1 v1 v2 : V3)
          (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
          (hcey : criticalEdgeY (dist u0 u1)) (hX : X = mcell3 V [u0, u1, v1, v2])
          (he : {u0, u1} ∈ edgeX V X) (hb : barV V 3 [u0, u1, v1, v2]),
    criticalWeight V X =
          1 / (wtcount3Y (dist u0 u1) (dist u0 v1) (dist u1 v1))
    ) ∧
    -- 25. Kepler.Text.MCELL3_DIHX (Kepler.Text.PackingAuto25:3016; HOL `MCELL3_DIHX`)
    (∀ (V : Set V3) (X : Set V3) (ul : List V3) (hs : saturated V)
          (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell3 V ul)
          (he : {elV ul 0, elV ul 1} ∈ edgeX V X) (hn : ¬ nullSet X),
    dihX V X (elV ul 0, elV ul 1) =
          dihV (elV ul 0) (elV ul 1) (elV ul 2) (mxi V ul)
    ) ∧
    -- 26. Kepler.Text.MCELL3_EDGE_EXPLICIT (Kepler.Text.PackingAuto25:9581; HOL `MCELL3_EDGE_EXPLICIT`)
    (∀ (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
          (hs : saturated V) (hn : ¬ nullSet (mcell3 V [u0, u1, u2, u3]))
          (hb : barV V 3 [u0, u1, u2, u3]),
    edgeX V (mcell3 V [u0, u1, u2, u3]) =
          {{u0, u1}, {u0, u2}, {u1, u2}}
    ) ∧
    -- 27. Kepler.Text.MCELL3_EXTREME_CARD (Kepler.Text.PackingAuto25:3001; HOL `MCELL3_EXTREME_CARD`)
    (∀ (V : Set V3) (ul : List V3) (hp : Packing V)
          (hs : saturated V) (hb : barV V 3 ul)
          (hn : ¬ nullSet (mcell3 V ul)),
    Set.ncard ({elV ul 0, elV ul 1, elV ul 2, mxi V ul} : Set V3) = 4
    ) ∧
    -- 28. Kepler.Text.MCELL4_EDGE_EXPLICIT (Kepler.Text.PackingAuto25:7448; HOL `MCELL4_EDGE_EXPLICIT`)
    (∀ (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
          (hs : saturated V) (hn : ¬ nullSet (mcell4 V [u0, u1, u2, u3]))
          (hb : barV V 3 [u0, u1, u2, u3]),
    edgeX V (mcell4 V [u0, u1, u2, u3]) =
          {{u0, u1}, {u0, u2}, {u0, u3}, {u1, u2}, {u1, u3}, {u2, u3}}
    ) ∧
    -- 29. Kepler.Text.MOD_PERIOD_BOUNDED_ALT (Kepler.Text.PackingAuto25:822; HOL `MOD_PERIOD_BOUNDED_ALT`)
    (∀ {k n : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
          (x : ℕ) (h : (x + k) % n = x % n),
    n ≤ k
    ) ∧
    -- 30. Kepler.Text.MOD_REFL_ALT (Kepler.Text.PackingAuto25:829; HOL `MOD_REFL_ALT`)
    (∀ (m : ℕ),
    m % 1 = 0
    ) ∧
    -- 31. Kepler.Text.NUMSEG_LT (Kepler.Text.PackingAuto25:484; HOL `NUMSEG_LT`)
    (∀ (r : ℕ) (hr : r ≠ 0),
    (Finset.Icc 0 (r - 1) : Set ℕ) = {i | i < r}
    ) ∧
    -- 32. Kepler.Text.ORDER_AZIM_SUM2Pi0 (Kepler.Text.PackingAuto25:13240; HOL `ORDER_AZIM_SUM2Pi0`)
    (∀ (x y z : V3) (n : ℕ) (g : ℕ → V3)
          (h1 : ¬ Collinear3 x y z) (h2 : ∀ i, i < n → ¬ Collinear3 x y (g i))
          (h3 : g n = g 0) (hn : 1 < n)
          (h4 : ∀ j k, j < n → k < n → j < k → azim x y z (g j) < azim x y z (g k)),
    ∑ i ∈ Finset.Icc 0 (n - 1), azim x y (g i) (g (i + 1)) = 2 * Real.pi
    ) ∧
    -- 33. Kepler.Text.STRICT_SORT_FINITE (Kepler.Text.PackingAuto25:715; HOL `STRICT_SORT_FINITE`)
    (∀ {α : Type*} [Nonempty α] {lt : α → α → Prop} (s : Set α) (n : ℕ)
          (hirr : ∀ x y, x ∈ s → y ∈ s → lt x y → lt y x → x = y)
          (htr : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → lt x y → lt y z → lt x z)
          (hs : s.Finite ∧ s.ncard = n),
    ∃ f : ℕ → α, s = f '' Set.Icc 1 n ∧
          ∀ j k, j ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → j < k → ¬lt (f k) (f j)
    ) ∧
    -- 34. Kepler.Text.S_LEAF_CARD2 (Kepler.Text.PackingAuto25:3481; HOL `S_LEAF_CARD2`)
    (∀ (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
          (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)),
    2 ≤ Set.ncard (s_leaf V [elV ul 0, elV ul 1])
    ) ∧
    -- 35. Kepler.Text.S_LEAF_TRUNCATE (Kepler.Text.PackingAuto25:2423; HOL `S_LEAF_TRUNCATE`)
    (∀ (V : Set V3) (ul : List V3),
    s_leaf V ul = s_leaf V [elV ul 0, elV ul 1]
    ) ∧
    -- 36. Kepler.Text.TEWNSCJ_MERGED (Kepler.Text.PackingAuto25:12563; HOL `TEWNSCJ_MERGED`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
          (hcey : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
          (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
          (hb4 : 2 ≤ y4) (hb4' : y4 ≤ Real.sqrt 8)
          (hrad : 2 ≤ rad2YP25 y1 y2 y3 y4 y5 y6)
          (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus) (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus)
          (he1 : eta_y y1 y2 y6 ^ 2 ≤ 1.34 ^ 2) (he2 : eta_y y1 y3 y5 ^ 2 ≤ 1.34 ^ 2),
    a_spine5 + b_spine5 * dihY y1 y2 y3 y4 y5 y6 ≤
          gamma3f y1 y2 y6 (Real.sqrt 2) lmfun +
            gamma3f y1 y3 y5 (Real.sqrt 2) lmfun +
            (dihY y1 y2 y3 y4 y5 y6 -
                (dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 +
                  dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2))) * 0.008
    ) ∧
    -- 37. Kepler.Text.TXQTPVC_MERGED (Kepler.Text.PackingAuto25:12517; HOL `TXQTPVC_MERGED`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
          (hcey : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
          (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
          (hb4 : 2 ≤ y4) (hb4' : y4 ≤ y5 + y6)
          (hrad : 2 ≤ rad2YP25 y1 y2 y3 y4 y5 y6)
          (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus) (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus)
          (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
          (hdi1 : dihY y1 y2 y3 y4 y5 y6 ≤ 2.089)
          (hdi2 : 1.946 ≤ dihY y1 y2 y3 y4 y5 y6)
          (he1 : eta_y y1 y2 y6 ^ 2 ≤ 1.34 ^ 2) (he2 : eta_y y1 y3 y5 ^ 2 ≤ 1.34 ^ 2),
    3 * 0.0057 ≤ gamma3f y1 y2 y6 (Real.sqrt 2) lmfun +
          gamma3f y1 y3 y5 (Real.sqrt 2) lmfun +
          (dihY y1 y2 y3 y4 y5 y6 -
              (dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 +
                dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2))) * 0.008
    ) ∧
    -- 38. Kepler.Text.bankGenMid.eq_1 (Kepler.Text.PackingAuto25:0; compiler-generated equation/aux lemma (parent def `bankGenMid` at Text.PackingAuto21:678; no source statement; sigtest = assembly elaboration))
    (∀ (i : ℕ), bankGenMid i = if i = 1 then 1 else 0
    ) ∧
    -- 39. Kepler.Text.bank_ZTGIJCF4hi.eq_1 (Kepler.Text.PackingAuto25:0; compiler-generated equation/aux lemma (parent def `bank_ZTGIJCF4hi` at Text.PackingAuto21:847; no source statement; sigtest = assembly elaboration))
    (∀ (i : ℕ), bank_ZTGIJCF4hi i = if i = 0 then 2 * hminus else √8
    ) ∧
    -- 40. Kepler.Text.bank_ZTGIJCF4lo.eq_1 (Kepler.Text.PackingAuto25:0; compiler-generated equation/aux lemma (parent def `bank_ZTGIJCF4lo` at Text.PackingAuto21:844; no source statement; sigtest = assembly elaboration))
    (∀ (i : ℕ), bank_ZTGIJCF4lo i = if i = 0 then 2 else 2 * hminus
    ) ∧
    -- 41. Kepler.Text.betaBumpLb.eq_1 (Kepler.Text.PackingAuto25:0; compiler-generated equation/aux lemma (parent def `betaBumpLb` at Text.IneqClosureDefs:493; no source statement; sigtest = assembly elaboration))
    (betaBumpLb = -5e-3
    ) ∧
    -- 42. Kepler.Text.beta_bumpA_lb0P25 (Kepler.Text.PackingAuto25:10486; HOL `beta_bumpA_lb0`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ)
          (hdisj : ¬ criticalEdgeY y1 ∨ criticalEdgeY y2 ∨ criticalEdgeY y3 ∨
            criticalEdgeY y5 ∨ criticalEdgeY y6 ∨ ¬ criticalEdgeY y4),
    (0 : ℝ) ≤ beta_bumpA_yP25 y1 y2 y3 y4 y5 y6
    ) ∧
    -- 43. Kepler.Text.beta_bumpA_yP25.eq_1 (Kepler.Text.PackingAuto25:111; compiler-generated equation/aux lemma (parent def `beta_bumpA_yP25` at Kepler.Text.PackingAuto25:111; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          beta_bumpA_yP25 y1 y2 y3 y4 y5 y6 =
            ((((((if criticalEdgeY y1 then 1 else 0) * if y2 < 2 * hminus then 1 else 0) * if y3 < 2 * hminus then 1 else 0) *
                    if criticalEdgeY y4 then 1 else 0) *
                  if y5 < 2 * hminus then 1 else 0) *
                if y6 < 2 * hminus then 1 else 0) *
              (bump (y1 / 2) - bump (y4 / 2))
    ) ∧
    -- 44. Kepler.Text.c1946 (Kepler.Text.PackingAuto25:12366; HOL `c1946`)
    (Real.pi - 1.946 < Real.arctan (Real.sqrt 6.45)
    ) ∧
    -- 45. Kepler.Text.c2089 (Kepler.Text.PackingAuto25:12318; HOL `c2089`)
    (Real.arctan (Real.sqrt 3.07) < Real.pi - 2.089
    ) ∧
    -- 46. Kepler.Text.cc_4.eq_1 (Kepler.Text.PackingAuto25:439; compiler-generated equation/aux lemma (parent def `cc_4` at Kepler.Text.PackingAuto25:439; no source statement; sigtest = assembly elaboration))
    (∀ (V : Set V3) (u0 u1 : V3) (f : ℕ → V3) (i : ℕ),
          cc_4 V u0 u1 f i =
            ∃ ul, barV V 3 ul ∧ {u0, u1} ∈ edgeX V (mcell4 V ul) ∧ mcell4 V ul ⊆ wedgeGe u0 u1 (f i) (f (i + 1))
    ) ∧
    -- 47. Kepler.Text.critical_weight1 (Kepler.Text.PackingAuto25:9894; HOL `critical_weight1`)
    (∀ (V : Set V3) (u0 u1 u2 : V3)
          (hcey : criticalEdgeY (dist u0 u1)) (hd1 : dist u0 u2 < 2 * hminus)
          (hd2 : dist u1 u2 < 2 * hminus) (hk : ccKe V [u0, u1, u2] = 3)
          (hp : Packing V) (hs : saturated V)
          (hb : barV V 3 (ccUh V [u0, u1, u2])) (hl' : leaf V [u0, u1, u2])
          (hnn : ¬ nullSet (ccCell V [u0, u1, u2])),
    criticalWeight V (ccCell V [u0, u1, u2]) = 1
    ) ∧
    -- 48. Kepler.Text.critical_weight1a (Kepler.Text.PackingAuto25:9913; HOL `critical_weight1a`)
    (∀ (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
          (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
          (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
          (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
          (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
          (hno4 : ¬ cc_4 V u0 u1 f i)
          (hd : dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus),
    criticalWeight V (ccCell V [u0, u1, f i]) = 1
    ) ∧
    -- 49. Kepler.Text.critical_weight1b (Kepler.Text.PackingAuto25:9927; HOL `critical_weight1b`)
    (∀ (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
          (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
          (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
          (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
          (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
          (hno4 : ¬ cc_4 V u0 u1 f i)
          (hd : dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus),
    criticalWeight V (ccCell V [u1, u0, f (i + 1)]) = 1
    ) ∧
    -- 50. Kepler.Text.gamma4fgcy_sym26 (Kepler.Text.PackingAuto25:11611; HOL `gamma4fgcy_sym26`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ),
    gamma4fgcyP25 y1 y2 y3 y4 y5 y6 f = gamma4fgcyP25 y1 y6 y5 y4 y3 y2 f
    ) ∧
    -- 51. Kepler.Text.initial_sublist_cons (Kepler.Text.PackingAuto25:663; HOL `initial_sublist_cons`)
    (∀ (a b : V3) (x y : List V3),
    initialSublist (a :: x) (b :: y) ↔ a = b ∧ initialSublist x y
    ) ∧
    -- 52. Kepler.Text.mcell3_dihX_dih_y (Kepler.Text.PackingAuto25:9461; HOL `mcell3_dihX_dih_y`)
    (∀ (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
          (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
          (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
          (hcey : criticalEdgeY (dist u0 u1)) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
          (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i),
    dihX V (ccCell V [u0, u1, f i]) (u0, u1) =
          dihY (dist u0 u1) (dist u0 (f i)) (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2)
            (dist u1 (f i))
    ) ∧
    -- 53. Kepler.Text.mcell3_dihXb_dih_y (Kepler.Text.PackingAuto25:9515; HOL `mcell3_dihXb_dih_y`)
    (∀ (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
          (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
          (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
          (hcey : criticalEdgeY (dist u0 u1)) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
          (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i),
    dihX V (ccCell V [u1, u0, f (i + 1)]) (u0, u1) =
          dihY (dist u0 u1) (dist u0 (f (i + 1))) (Real.sqrt 2) (Real.sqrt 2)
            (Real.sqrt 2) (dist u1 (f (i + 1)))
    ) ∧
    -- 54. Kepler.Text.periodic_o (Kepler.Text.PackingAuto25:832; HOL `periodic_o`)
    (∀ {α β : Type*} (g : α → β) {f : ℕ → α} {n : ℕ}
          (h : periodic f n),
    periodic (g ∘ f) n
    ) ∧
    -- 55. Kepler.Text.periodic_shift (Kepler.Text.PackingAuto25:836; HOL `periodic_shift`)
    (∀ {α : Type*} (k : ℕ) {f : ℕ → α} {n : ℕ}
          (h : periodic f n),
    periodic (fun i => f (i + k)) n
    ) ∧
    -- 56. Kepler.Text.rad2XP25.eq_1 (Kepler.Text.PackingAuto25:98; compiler-generated equation/aux lemma (parent def `rad2XP25` at Kepler.Text.PackingAuto25:98; no source statement; sigtest = assembly elaboration))
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ), rad2XP25 x1 x2 x3 x4 x5 x6 = rad2X x1 x2 x3 x4 x5 x6
    ) ∧
    -- 57. Kepler.Text.s_leaf.eq_1 (Kepler.Text.PackingAuto25:391; compiler-generated equation/aux lemma (parent def `s_leaf` at Kepler.Text.PackingAuto25:391; no source statement; sigtest = assembly elaboration))
    (∀ (V : Set V3) (ul : List V3),
          s_leaf V ul =
            {u | leaf V [elV ul 0, elV ul 1, u] ∧ (ccKe V [elV ul 0, elV ul 1, u] = 4 ∨ ccKe V [elV ul 1, elV ul 0, u] = 4)}
    ) ∧
    -- 58. Kepler.Text.wtcount6Y_unfold_band (Kepler.Text.PackingAuto25:10529; no HOL anchor line in file docstring)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ)
          (hc1 : criticalEdgeY y1) (h2 : y2 < 2 * hminus),
    wtcount6Y y1 y2 y3 y4 y5 y6 =
          1 + (if criticalEdgeY y3 then 1 else 0) + (if criticalEdgeY y4 then 1 else 0) +
            (if criticalEdgeY y5 then 1 else 0) + (if criticalEdgeY y6 then 1 else 0)
    ) ∧
    -- 59. Kepler.Text.ztg4_shard_finish_m0 (Kepler.Text.PackingAuto25:10600; no HOL anchor line in file docstring)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ)
          (hc1 : criticalEdgeY y1) (h2 : y2 < 2 * hminus) (h3 : y3 < 2 * hminus)
          (h4 : y4 < 2 * hminus) (h5 : y5 < 2 * hminus) (h6 : y6 < 2 * hminus)
          (h2lo : (2 : ℝ) ≤ y2) (h3lo : (2 : ℝ) ≤ y3) (h4lo : (2 : ℝ) ≤ y4)
          (h5lo : (2 : ℝ) ≤ y5) (h6lo : (2 : ℝ) ≤ y6)
          (hrad : rad2YP25 y1 y2 y3 y4 y5 y6 < 2)
          (hshard : bank_ZTGIJCF4_0_0_0_0),
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / (wtcount6Y y1 y2 y3 y4 y5 y6 : ℝ) +
            beta_bumpA_yP25 y1 y2 y3 y4 y5 y6 >
          aSpine5 + bSpine5 * dihY y1 y2 y3 y4 y5 y6
    ) ∧
    -- 60. Kepler.Text.ztg4_shard_finish_m1 (Kepler.Text.PackingAuto25:10546; no HOL anchor line in file docstring)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ)
          (hc1 : criticalEdgeY y1) (h2 : y2 < 2 * hminus) (h3 : y3 < 2 * hminus)
          (h2lo : (2 : ℝ) ≤ y2) (h3lo : (2 : ℝ) ≤ y3)
          (h4lo : 2 * hminus ≤ y4) (h4' : y4 ≤ 2 * hplus) (h5 : y5 < 2 * hminus)
          (h5lo : (2 : ℝ) ≤ y5) (h6 : y6 < 2 * hminus) (h6lo : (2 : ℝ) ≤ y6)
          (hrad : rad2YP25 y1 y2 y3 y4 y5 y6 < 2)
          (hshard : bank_ZTGIJCF4_0_1_0_0),
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / (wtcount6Y y1 y2 y3 y4 y5 y6 : ℝ) +
            beta_bumpA_yP25 y1 y2 y3 y4 y5 y6 >
          aSpine5 + bSpine5 * dihY y1 y2 y3 y4 y5 y6
    ) :=
⟨_root_.Kepler.Text.AFF_DEP_COPLANAR, _root_.Kepler.Text.AZIM_ZERO_SHIFT,
      _root_.Kepler.Text.CARD_INSERT_INTER_ALT, _root_.Kepler.Text.CC_4_BETA_BUMP_EXPLICIT,
      _root_.Kepler.Text.COPLANAR_CONVEX_HULL_COPLANAR,
      _root_.Kepler.Text.DIHV_EQ_0_PI_EQ_COPLANAR_ALT,
      _root_.Kepler.Text.DIHV_EQ_0_PI_EQ_COPLANAR_ALT._abel_1_3,
      _root_.Kepler.Text.DIHV_EQ_0_PI_EQ_COPLANAR_ALT._abel_1_4,
      _root_.Kepler.Text.DIST_IMP_COLLINEAR, _root_.Kepler.Text.DIST_IMP_COLLINEAR._abel_1_1,
      _root_.Kepler.Text.DIST_IMP_UPS_X_POS, _root_.Kepler.Text.DIST_IMP_UPS_X_POS._abel_1_1,
      _root_.Kepler.Text.EDGEX_PAIR, _root_.Kepler.Text.ETA_Y_LEMMA,
      _root_.Kepler.Text.ETA_Y_LEMMA_ALT, _root_.Kepler.Text.FM_DEMOD,
      _root_.Kepler.Text.GAMMAX_NO_BETA, _root_.Kepler.Text.INITIAL_SUBLIST_TRUNCATE,
      _root_.Kepler.Text.IXPOTPA_MERGED, _root_.Kepler.Text.JSP_BOUNDS,
      _root_.Kepler.Text.LEAF_RANKING_LEMMA, _root_.Kepler.Text.LEAF_RANK_TRUNCATE,
      _root_.Kepler.Text.MCELL2_CRITICAL_WEIGHT1, _root_.Kepler.Text.MCELL3_CRITICAL_WEIGHT,
      _root_.Kepler.Text.MCELL3_DIHX, _root_.Kepler.Text.MCELL3_EDGE_EXPLICIT,
      @_root_.Kepler.Text.MCELL3_EXTREME_CARD, _root_.Kepler.Text.MCELL4_EDGE_EXPLICIT,
      _root_.Kepler.Text.MOD_PERIOD_BOUNDED_ALT, _root_.Kepler.Text.MOD_REFL_ALT,
      _root_.Kepler.Text.NUMSEG_LT, _root_.Kepler.Text.ORDER_AZIM_SUM2Pi0,
      _root_.Kepler.Text.STRICT_SORT_FINITE, _root_.Kepler.Text.S_LEAF_CARD2,
      _root_.Kepler.Text.S_LEAF_TRUNCATE, _root_.Kepler.Text.TEWNSCJ_MERGED,
      _root_.Kepler.Text.TXQTPVC_MERGED, _root_.Kepler.Text.bankGenMid.eq_1,
      _root_.Kepler.Text.bank_ZTGIJCF4hi.eq_1, _root_.Kepler.Text.bank_ZTGIJCF4lo.eq_1,
      _root_.Kepler.Text.betaBumpLb.eq_1, _root_.Kepler.Text.beta_bumpA_lb0P25,
      _root_.Kepler.Text.beta_bumpA_yP25.eq_1, _root_.Kepler.Text.c1946,
      _root_.Kepler.Text.c2089, _root_.Kepler.Text.cc_4.eq_1,
      _root_.Kepler.Text.critical_weight1, _root_.Kepler.Text.critical_weight1a,
      _root_.Kepler.Text.critical_weight1b, _root_.Kepler.Text.gamma4fgcy_sym26,
      _root_.Kepler.Text.initial_sublist_cons, _root_.Kepler.Text.mcell3_dihX_dih_y,
      _root_.Kepler.Text.mcell3_dihXb_dih_y, _root_.Kepler.Text.periodic_o,
      _root_.Kepler.Text.periodic_shift, _root_.Kepler.Text.rad2XP25.eq_1,
      _root_.Kepler.Text.s_leaf.eq_1, _root_.Kepler.Text.wtcount6Y_unfold_band,
      _root_.Kepler.Text.ztg4_shard_finish_m0, _root_.Kepler.Text.ztg4_shard_finish_m1⟩

-- Self-check.  Ground truth = `#print axioms`, not prose: expect exactly the standard three
-- [propext, Classical.choice, Quot.sound] and NO sorryAx (the scout group closure is sorried-0).
#print axioms pa25_wire_capstone_w1

/-! ### PA4 materialization capstone (lane lv910-w1, 2026-11-04, after the leftover-mat-scout-2 workorder LV9):
the 71 public top-level PackingAuto4 clean theorem exits (scout seeds_clean.txt PA4 group; the 9 sorried
BumpP4.MCELL*_PARAM/_CELL_PARAMETERS_EXIST skeleton exits are NOT included -- NO-GO half assigned to the PA17
spare-parts line by the scout), of which 41 are statable from PackingConcl and are re-exposed as ONE conjunction below;
30 exits are dropped per the no-forcing rule (their statements name PackingAuto4-module PRIVATE constants -- the `private abbrev ccBoolModelP4` /
CC4P4 kit family -- and cannot be restated outside the module; each drop is named in the theorem docstring).
Self-contained section: pure insertion, zero new imports (PA4 already imported at :109), zero proof obligations (body = the exit assembly itself).
The scoped heartbeat raise mirrors the file's own `set_option maxHeartbeats` usage (see the pa21 section below): the conjunction statement exceeds the default
200000 budget during statement elaboration (measured on the first compile attempt; the pa21 capstone uses 50000000).
-/

set_option maxHeartbeats 50000000 in

/-- PA4 materialization capstone (scout lane leftover-mat-scout-2
workorder LV9, implementation lane lv910-w1, 2026-11-04).  The
71 public top-level Kepler.Text.PackingAuto4 theorem exits unreachable from every
e2e root (scout probe1/probe2: GROUP_VS_CONE fresh sorried-0, standard-three
axiom face on the axprobe sample); 41 of them are statable from
PackingConcl and are re-exposed as ONE conjunction.
Implemented here: 41 of the 71.  Dropped per the workorder no-forcing rule, mechanically detected by the generator:
--   Kepler.Text.BumpP4.BETA_BUMP_INVOLUTION_BIJ: statement names module-private constant(s) BumpP4.BIJP4 (unstatable from PackingConcl)
--   Kepler.Text.CARD5_1074_LE_QYI: statement names module-private constant(s) Text.ccAzimP4, Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.aSpine5P4, Text.bSpine5P4, Text.cc4CellP4, Text.ccAzimP4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccCardP4, Text.ccGgP4, Text.ccQyP4, Text.ccRealModelP4, Text.periodicP4 (unstatable from PackingConcl)
--   Kepler.Text.CC_4CELL_QUQX: statement names module-private constant(s) Text.CC4P4, Text.cc4CellP4, Text.ccQuP4, Text.ccQxP4 (unstatable from PackingConcl)
--   Kepler.Text.CC_CARD_LESS_THAN_5: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccCardP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.CHQSQEY: statement names module-private constant(s) Text.cc4CellP4, Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccRealModelP4, Text.ccSizeP4 (unstatable from PackingConcl)
--   Kepler.Text.EXISTS_QY_CARD5: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccCardP4, Text.ccQyP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.GRHIDFA: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.GRHIDFA_ALT: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccCardP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.IPVICGW: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccRealModelP4, Text.ccSmallP4 (unstatable from PackingConcl)
--   Kepler.Text.IPVICGW_C33: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccCardP4, Text.ccRealModelP4, Text.ccSmallP4 (unstatable from PackingConcl)
--   Kepler.Text.IPVICGW_C43_C44: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccCardP4, Text.ccRealModelP4, Text.ccSmallP4 (unstatable from PackingConcl)
--   Kepler.Text.LEAST_BOUND_CC_GG: statement names module-private constant(s) Text.ccEpsP4, Text.CC4P4, Text.ccGgP4, Text.ccQuP4, Text.ccQxP4, Text.ccQyP4 (unstatable from PackingConcl)
--   Kepler.Text.LITTLE_CC_GG3AA: statement names module-private constant(s) Text.ccGg3aP4, Text.ccQyP4, Text.CC4P4, Text.ccGg3aP4, Text.ccGgP4, Text.ccQuP4, Text.ccQxP4, Text.ccQyP4, Text.periodicP4, Text.periodicPropP4 (unstatable from PackingConcl)
--   Kepler.Text.LITTLE_CC_GG3BB: statement names module-private constant(s) Text.CC4P4, Text.ccGg3bP4, Text.ccGgP4, Text.ccQuP4, Text.ccQxP4, Text.ccQyP4 (unstatable from PackingConcl)
--   Kepler.Text.LUIKGMH: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccCardP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.LXDEYBO: statement names module-private constant(s) Text.cc4CellP4, Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccRealModelP4, Text.ccSizeP4 (unstatable from PackingConcl)
--   Kepler.Text.MTMLSRF: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.cc4CellP4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccGgP4, Text.ccQuP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.NOT_QY_LEM: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccRealModelP4, Text.ccQyP4 (unstatable from PackingConcl)
--   Kepler.Text.PERIODIC_IMAGE_EQUAL: statement names module-private constant(s) Text.periodicP4 (unstatable from PackingConcl)
--   Kepler.Text.PRE_IPVICGW: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccCardP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.QU_OR_QXY: statement names module-private constant(s) Text.CC4P4, Text.ccQuP4, Text.ccQxP4, Text.ccQyP4 (unstatable from PackingConcl)
--   Kepler.Text.QX_NN00: statement names module-private constant(s) Text.CC4P4, Text.ccBoolModelP4, Text.ccGgP4, Text.ccQxP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.QY_NN00: statement names module-private constant(s) Text.CC4P4, Text.ccBoolModelP4, Text.ccGgP4, Text.ccQyP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.RSIWAMP: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccCardP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.THREE_LE_CC_CARD: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccCardP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.UNIQUE_QY: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccQyP4, Text.ccRealModelP4, Text.ccQyP4 (unstatable from PackingConcl)
--   Kepler.Text.UNIQUE_QY2: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccQyP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.UNPNFVW: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.ccQyP4, Text.CC4P4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccRealModelP4, Text.ccSizeP4 (unstatable from PackingConcl)
--   Kepler.Text.UTEOITF: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.cc4CellP4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccRealModelP4 (unstatable from PackingConcl)
--   Kepler.Text.WKR_COMPTED: statement names module-private constant(s) Text.ccCardP4, Text.ccGgP4, Text.CC4P4, Text.cc4CellP4, Text.ccBoolModelP4, Text.ccBoolPrepP4, Text.ccRealModelP4 (unstatable from PackingConcl)

Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its Kepler.Text.PackingAuto4 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the first depth-0 `:=` by the generator gen_items.py,
bracket-balance guarded); compiler-generated equation lemmas have no source
statement anywhere, so their conjunct is the `#check @name` printer dump
verbatim and each passes a per-item sigtest (the `⟨...⟩` assembly below must
unify it definitionally with the constant's type).  Semantic identity of
every conjunct is re-verified by that assembly (each element must have
exactly its conjunct's type); the per-conjunct comments carry each exit's
Kepler.Text.PackingAuto4 declaration line and file-local docstring HOL anchor.
Conjunct order: the scout seed-list order (probe1 SEED list,
seeds_clean.txt).  Body = the assembly of the exit constants -- zero new
proof obligations, zero new imports. -/
theorem pa4_wire_capstone_w1 :
    -- 1. Kepler.Text.BumpP4.BETA_BUMP_ALT (Kepler.Text.PackingAuto4:2180; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (X : Set V3) (r : Set V3 → Set V3) (e : Set V3)
          (_hs : saturated V) (_hp : Packing V) (_hm : X ∈ mcellSet V)
          (hr : (fun e => VX V X \ e) = r),
    betaBump V e X =
          if ¬nullSet X ∧ e ∈ criticalEdgeX V X ∧ r e ∈ criticalEdgeX V X ∧
              (∀ f ∈ edgeX V X, f = e ∨ f = r e ∨ f ∈ subcriticalEdgeX V X) then
            bump (radV e) - bump (radV (r e))
          else 0
    ) ∧
    -- 2. Kepler.Text.BumpP4.BETA_ORDERED_PAIR_THM (Kepler.Text.PackingAuto4:1320; no HOL anchor line in file docstring)
    (∀ {α β γ : Type} (g : α → β → γ) (x : α × β),
    (fun p => g p.1 p.2) x = g x.1 x.2
    ) ∧
    -- 3. Kepler.Text.BumpP4.BIJ_SUM (Kepler.Text.PackingAuto4:1324; no HOL anchor line in file docstring)
    (∀ {α β : Type} [Fintype α] [Fintype β] (A : Set α) (B : Set β)
          (f : β → ℝ) (ab : α ≃ β) (_h : Set.BijOn ab A B),
    setSum A (fun a => f (ab a)) = setSum B f
    ) ∧
    -- 4. Kepler.Text.BumpP4.CARD2_EDGEX (Kepler.Text.PackingAuto4:1939; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (X : Set V3) (e : Set V3) (he : e ∈ edgeX V X),
    Nat.card e = 2
    ) ∧
    -- 5. Kepler.Text.BumpP4.CRITICAL_EDGEX_ALT (Kepler.Text.PackingAuto4:2042; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (X : Set V3) (e : Set V3),
    e ∈ criticalEdgeX V X ↔ e ∈ edgeX V X ∧ hminus ≤ radV e ∧ radV e ≤ hplus
    ) ∧
    -- 6. Kepler.Text.BumpP4.EDGE_MCELL_EL (Kepler.Text.PackingAuto4:1877; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (X : Set V3) (e : Set V3) (he : e ∈ edgeX V X),
    ∃ u v : V3, e = {u, v} ∧ u ≠ v
    ) ∧
    -- 7. Kepler.Text.BumpP4.EL_EXPLICIT (Kepler.Text.PackingAuto4:1342; no HOL anchor line in file docstring)
    (∀ (h : V3) (t : List V3),
    elV (h :: t) 0 = h ∧ elV (h :: t) 1 = hdV t
    ) ∧
    -- 8. Kepler.Text.BumpP4.HDTFNFZ_SUBSET (Kepler.Text.PackingAuto4:1543; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (ul : List V3) (k : ℕ) (X : Set V3)
          (_hs : saturated V) (_hp : Packing V) (_hb : barV V 3 ul) (_hX : X = mcell k V ul),
    VX V X ⊆ V ∩ X
    ) ∧
    -- 9. Kepler.Text.BumpP4.LENGTH1 (Kepler.Text.PackingAuto4:1349; no HOL anchor line in file docstring)
    (∀ {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 1),
    ul = [ul.getD 0 default]
    ) ∧
    -- 10. Kepler.Text.BumpP4.LENGTH2 (Kepler.Text.PackingAuto4:1357; no HOL anchor line in file docstring)
    (∀ {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 2),
    ul = [ul.getD 0 default, ul.getD 1 default]
    ) ∧
    -- 11. Kepler.Text.BumpP4.LENGTH3 (Kepler.Text.PackingAuto4:1366; no HOL anchor line in file docstring)
    (∀ {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 3),
    ul = [ul.getD 0 default, ul.getD 1 default, ul.getD 2 default]
    ) ∧
    -- 12. Kepler.Text.BumpP4.LENGTH4 (Kepler.Text.PackingAuto4:1376; no HOL anchor line in file docstring)
    (∀ {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 4),
    ul = [ul.getD 0 default, ul.getD 1 default, ul.getD 2 default,
          ul.getD 3 default]
    ) ∧
    -- 13. Kepler.Text.BumpP4.MCELL0 (Kepler.Text.PackingAuto4:1678; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (ul : List V3),
    mcell0 V ul = mcell 0 V ul
    ) ∧
    -- 14. Kepler.Text.BumpP4.MCELL3_SET_OF_LIST_VX (Kepler.Text.PackingAuto4:1832; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (ul : List V3) (X : Set V3)
          (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell3 V ul)
          (_hn : ¬nullSet X) (_hb : barV V 3 ul),
    setOfList (truncateSimplex 2 ul) = V ∩ X
    ) ∧
    -- 15. Kepler.Text.BumpP4.MCELL4_EDGE_OPP (Kepler.Text.PackingAuto4:2084; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (ul : List V3) (_hp : Packing V)
          (_hs : saturated V) (_hb : barV V 3 ul) (_hn : ¬nullSet (mcell4 V ul)),
    VX V (mcell4 V ul) \ {elV ul 0, elV ul 1} = {elV ul 2, elV ul 3}
    ) ∧
    -- 16. Kepler.Text.BumpP4.MCELL4_SET_OF_LIST_VX (Kepler.Text.PackingAuto4:1818; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (ul : List V3) (X : Set V3)
          (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell4 V ul)
          (_hn : ¬nullSet X) (_hb : barV V 3 ul),
    setOfList ul = V ∩ X
    ) ∧
    -- 17. Kepler.Text.BumpP4.MCELL4_VX (Kepler.Text.PackingAuto4:1786; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (ul : List V3) (X : Set V3) (_hp : Packing V)
          (_hs : saturated V) (_hX : X = mcell4 V ul) (_hb : barV V 3 ul),
    VX V X ⊆ setOfList (cellParams V X).2
    ) ∧
    -- 18. Kepler.Text.BumpP4.MCELL_BUMP_OPP (Kepler.Text.PackingAuto4:2136; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (ul : List V3) (_hp : Packing V)
          (_hs : saturated V) (_hb : barV V 3 ul) (_hn : ¬nullSet (mcell4 V ul))
          (_hc : ({elV ul 2, elV ul 3} : Set V3) ∉ criticalEdgeX V (mcell4 V ul)),
    betaBump V {elV ul 0, elV ul 1} (mcell4 V ul) = 0
    ) ∧
    -- 19. Kepler.Text.BumpP4.REAL_ABS_TRIANGLE_BOUND (Kepler.Text.PackingAuto4:2386; no HOL anchor line in file docstring)
    (∀ (a b x : ℝ) (ha : a ≤ x) (hb : x ≤ b),
    abs x ≤ abs a + abs b
    ) ∧
    -- 20. Kepler.Text.BumpP4.SUBCRITICAL_EDGEX_ALT (Kepler.Text.PackingAuto4:2063; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (X : Set V3) (e : Set V3),
    e ∈ subcriticalEdgeX V X ↔ e ∈ edgeX V X ∧ radV e < hminus
    ) ∧
    -- 21. Kepler.Text.BumpP4.VORONOI_V (Kepler.Text.PackingAuto4:1560; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (w : V3) (hw : w ∈ V),
    V ∩ voronoiClosed V w = {w}
    ) ∧
    -- 22. Kepler.Text.BumpP4.V_CELL0_EMPTY (Kepler.Text.PackingAuto4:1573; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (vl : List V3) (_hs : saturated V)
          (_hp : Packing V) (_hb : barV V 3 vl),
    V ∩ mcell0 V vl = ∅
    ) ∧
    -- 23. Kepler.Text.BumpP4.set_of_list2 (Kepler.Text.PackingAuto4:1409; no HOL anchor line in file docstring)
    (∀ {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 2),
    setOfList ul = {ul.getD 0 default, ul.getD 1 default}
    ) ∧
    -- 24. Kepler.Text.BumpP4.set_of_list2_explicit (Kepler.Text.PackingAuto4:1388; no HOL anchor line in file docstring)
    (∀ {α : Type} (a b : α),
    setOfList [a, b] = {a, b}
    ) ∧
    -- 25. Kepler.Text.BumpP4.set_of_list3 (Kepler.Text.PackingAuto4:1422; no HOL anchor line in file docstring)
    (∀ {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 3),
    setOfList ul =
          {ul.getD 0 default, ul.getD 1 default, ul.getD 2 default}
    ) ∧
    -- 26. Kepler.Text.BumpP4.set_of_list3_explicit (Kepler.Text.PackingAuto4:1395; no HOL anchor line in file docstring)
    (∀ {α : Type} (a b c : α),
    setOfList [a, b, c] = {a, b, c}
    ) ∧
    -- 27. Kepler.Text.BumpP4.set_of_list4 (Kepler.Text.PackingAuto4:1439; no HOL anchor line in file docstring)
    (∀ {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 4),
    setOfList ul =
          {ul.getD 0 default, ul.getD 1 default, ul.getD 2 default,
            ul.getD 3 default}
    ) ∧
    -- 28. Kepler.Text.CARD_MOD_NUMSEG (Kepler.Text.PackingAuto4:515; no HOL anchor line in file docstring)
    (∀ (n m i : ℕ) (_hm : m ≤ n),
    Nat.card {x : ℕ | ∃ k < m, x = (i + k) % n} = m
    ) ∧
    -- 29. Kepler.Text.FINITE_INITIAL_SEG2 (Kepler.Text.PackingAuto4:509; no HOL anchor line in file docstring)
    (∀ (n : ℕ),
    {i : ℕ | i < n}.Finite
    ) ∧
    -- 30. Kepler.Text.MOD_INJ1 (Kepler.Text.PackingAuto4:384; no HOL anchor line in file docstring)
    (∀ (n k : ℕ) (hn : n ≠ 0) (hk : k < n) (hk0 : k ≠ 0) (x : ℕ),
    x % n ≠ (x + k) % n
    ) ∧
    -- 31. Kepler.Text.MOD_NUMSEG (Kepler.Text.PackingAuto4:519; no HOL anchor line in file docstring)
    (∀ (n i : ℕ) (hn : n ≠ 0),
    (Finset.Icc 0 (n - 1) : Set ℕ) = (fun x => (i + x) % n) '' {x | x < n}
    ) ∧
    -- 32. Kepler.Text.MOD_PERIOD_BOUNDED (Kepler.Text.PackingAuto4:444; no HOL anchor line in file docstring)
    (∀ (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) (x : ℕ),
    (x + k) % n = x % n → n ≤ k
    ) ∧
    -- 33. Kepler.Text.MOD_PERIOD_BOUNDED2 (Kepler.Text.PackingAuto4:452; no HOL anchor line in file docstring)
    (∀ (nn m i k : ℕ) (hnn : nn ≠ 0) (hmk : m ≤ k)
          (h : (i + k) % nn ∈ (fun x => (i + x) % nn) '' {x | x < m}),
    nn ≤ k
    ) ∧
    -- 34. Kepler.Text.NUMSEG_INTER_22 (Kepler.Text.PackingAuto4:586; no HOL anchor line in file docstring)
    (∀ (nn i x : ℕ) (hnn : nn ≠ 0),
    (i ≤ x ∧ x ≤ i + nn - 1) ↔ ∃ k < nn, x = i + k
    ) ∧
    -- 35. Kepler.Text.NUMSEG_SET_VER (Kepler.Text.PackingAuto4:503; no HOL anchor line in file docstring)
    (∀ (m : ℕ),
    (Finset.Icc 0 m : Set ℕ) = {i | i ≤ m}
    ) ∧
    -- 36. Kepler.Text.SUM_BETA (Kepler.Text.PackingAuto4:273; no HOL anchor line in file docstring)
    (∀ {α : Type*} (S : Set α) (f : α → ℝ),
    setSum S (fun x => f x) = setSum S f
    ) ∧
    -- 37. Kepler.Text.SUM_POS_LT_NUMSEG (Kepler.Text.PackingAuto4:266; no HOL anchor line in file docstring)
    (∀ (m n : ℕ) (f : ℕ → ℝ) (hmn : m ≤ n)
          (h : ∀ p, m ≤ p → p ≤ n → 0 < f p),
    0 < Finset.sum (Finset.Icc m n) f
    ) ∧
    -- 38. Kepler.Text.THREE_MOD_CONSECUTIVES (Kepler.Text.PackingAuto4:429; no HOL anchor line in file docstring)
    (∀ (i n : ℕ) (hi : 0 < i) (hn : 3 ≤ n),
    ¬((i - 1) % n = i % n ∨ i % n = (i + 1) % n ∨ (i + 1) % n = (i - 1) % n)
    ) ∧
    -- 39. Kepler.Text.betaBump.eq_1 (Kepler.Text.PackingAuto4:1040; compiler-generated equation lemma (parent def `betaBump` at Kepler.Text.PackingAuto4:1040; no source statement; sigtest = assembly elaboration))
    (∀ (V e X : Set V3),
          betaBump V e X =
            if
                X ∈ mcellSet V ∧
                  ¬nullSet X ∧
                    e ∈ criticalEdgeX V X ∧
                      VX V X \ e ∈ criticalEdgeX V X ∧ ∀ f ∈ edgeX V X, f = e ∨ f = VX V X \ e ∨ f ∈ subcriticalEdgeX V X then
              bump (radV e) - bump (radV (VX V X \ e))
            else 0
    ) ∧
    -- 40. Kepler.Text.hplus.eq_1 (Kepler.Text.PackingAuto4:0; compiler-generated equation lemma (parent def `hplus` at PA2:436; no source statement; sigtest = assembly elaboration))
    (hplus = 1.3254
    ) ∧
    -- 41. Kepler.Text.subcriticalEdgeX.eq_1 (Kepler.Text.PackingAuto4:0; compiler-generated equation lemma (parent def `subcriticalEdgeX` at PA2:484; no source statement; sigtest = assembly elaboration))
    (∀ (V X : Set V3),
          subcriticalEdgeX V X = {e | ∃ u v, e = {u, v} ∧ e ∈ edgeX V X ∧ hl [u, v] < hminus}
    ) :=
    ⟨BumpP4.BETA_BUMP_ALT, BumpP4.BETA_ORDERED_PAIR_THM, BumpP4.BIJ_SUM, BumpP4.CARD2_EDGEX,
      BumpP4.CRITICAL_EDGEX_ALT, BumpP4.EDGE_MCELL_EL, BumpP4.EL_EXPLICIT,
      @BumpP4.HDTFNFZ_SUBSET, BumpP4.LENGTH1, BumpP4.LENGTH2, BumpP4.LENGTH3, BumpP4.LENGTH4,
      BumpP4.MCELL0, BumpP4.MCELL3_SET_OF_LIST_VX, BumpP4.MCELL4_EDGE_OPP,
      BumpP4.MCELL4_SET_OF_LIST_VX, @BumpP4.MCELL4_VX, BumpP4.MCELL_BUMP_OPP,
      BumpP4.REAL_ABS_TRIANGLE_BOUND, BumpP4.SUBCRITICAL_EDGEX_ALT, BumpP4.VORONOI_V,
      BumpP4.V_CELL0_EMPTY, BumpP4.set_of_list2, BumpP4.set_of_list2_explicit,
      BumpP4.set_of_list3, BumpP4.set_of_list3_explicit, BumpP4.set_of_list4, CARD_MOD_NUMSEG,
      FINITE_INITIAL_SEG2, MOD_INJ1, MOD_NUMSEG, MOD_PERIOD_BOUNDED, MOD_PERIOD_BOUNDED2,
      NUMSEG_INTER_22, NUMSEG_SET_VER, SUM_BETA, SUM_POS_LT_NUMSEG, THREE_MOD_CONSECUTIVES,
      betaBump.eq_1, hplus.eq_1, subcriticalEdgeX.eq_1⟩

-- Self-check.  Ground truth = `#print axioms`, not prose: expect exactly the standard three
-- [propext, Classical.choice, Quot.sound] and NO sorryAx (the scout group closure is sorried-0).
#print axioms pa4_wire_capstone_w1

/-! ## Discharges (PackingAuto2 `pack_concl.hl` interfaces) -/

/-- `PackingAuto2.GLTVHUM_concl` (Auto2:548), discharged by
`PackingAuto6.GLTVHUM` (Rogers.hl:1152).  Shape-verbatim. -/
theorem GLTVHUM_concl_discharged :
    ∀ (V : Set V3) (u0 p : V3), Packing V ∧ saturated V → u0 ∈ V →
    (p ∈ voronoiClosed V u0 ↔
      ∃ vl : List V3, barV V 3 vl ∧ p ∈ rogers V vl ∧ truncateSimplex 0 vl = [u0]) :=
  fun V u0 p h hu0 => GLTVHUM V u0 p h hu0

/-- `PackingAuto2.DUUNHOR_concl` (Auto2:3500), discharged by
`PackingAuto6.DUUNHOR` (Rogers.hl:1682).  R2 STATEMENT-FIX (item 13;
harvest wave 1, 2026-10-08): the interface formerly mirrored the bare
`barV`-only pack_concl.hl shape, which left the twin — whose Auto2 kernel
(`DUUNHOR_concl`, really proved over the §6.5/§6.6 p2g kit) carries the
widened `Packing V`/`saturated V` antecedents — inapplicable and this
entry sorried.  The weak shape had no consumers repo-wide, so both the
Auto2 interface (already widened upstream) and this entry now carry the
r2 form: shape-verbatim, sorry-free discharge. -/
theorem DUUNHOR_concl_discharged :
    ∀ (V : Set V3) (ul vl : List V3), Packing V → saturated V →
      barV V 3 ul → barV V 3 vl →
      rogers V ul ≠ rogers V vl → Coplanar (rogers V ul ∩ rogers V vl) :=
  fun V ul vl hP hs hul hvl hne => DUUNHOR V ul vl hP hs hul hvl hne

/-- `PackingAuto2.QXSKIIT_concl` (Auto2:561), discharged by
`PackingAuto6.QXSKIIT` (Rogers.hl:3732).  Shape-verbatim. -/
theorem QXSKIIT_concl_discharged :
    ∀ {A : Type} (vf : A → V3) (b : A → ℝ),
    (vf '' (Set.univ : Set A)).Finite → ¬affineDependent (vf '' (Set.univ : Set A)) →
    (∀ i j : A, vf i = vf j → b i = b j) →
    ∃! p : V3, p ∈ (affineSpan ℝ (vf '' (Set.univ : Set A)) : Set V3) ∧
      ∀ i j : A, p ⬝ᵥ (vf i - vf j) = b i - b j :=
  @QXSKIIT

/-- `PackingAuto2.OAPVION1_concl` (Auto2:570), discharged by
`PackingAuto6.OAPVION1` (Rogers.hl:3843).  Shape-verbatim. -/
theorem OAPVION1_concl_discharged :
    ∀ S : Set V3, S ≠ ∅ → ¬affineDependent S →
      circumcenter S ∈ (affineSpan ℝ S : Set V3) :=
  OAPVION1

/-- `PackingAuto2.OAPVION2_concl` (Auto2:576), discharged by
`PackingAuto6.OAPVION2` (Rogers.hl:3851).  Shape-verbatim. -/
theorem OAPVION2_concl_discharged :
    ∀ S : Set V3, ¬affineDependent S →
      ∀ w ∈ S, radV S = dist (circumcenter S) w :=
  OAPVION2

/-- `PackingAuto2.OAPVION3_concl` (Auto2:582), discharged by
`PackingAuto6.OAPVION3` (Rogers.hl:3892).  Shape-verbatim. -/
theorem OAPVION3_concl_discharged :
    ∀ S : Set V3, ¬affineDependent S →
      ∀ p : V3, p ∈ (affineSpan ℝ S : Set V3) → (∃ c : ℝ, ∀ w ∈ S, dist p w = c) →
        p = circumcenter S :=
  OAPVION3

/-- `PackingAuto2.MHFTTZN1_concl` (Auto2:589), discharged by
`PackingAuto6.MHFTTZN1` (Rogers.hl:4862) — the twin needs neither
`k ≤ 3` nor saturation, so the interface's weaker hypotheses suffice. -/
theorem MHFTTZN1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), k ≤ 3 → saturated V →
      Packing V → barV V k ul → affDim (setOfList ul) = (k : ℤ) :=
  fun V ul k _ _ hP hbar => MHFTTZN1 V ul k hP hbar

/-- `PackingAuto2.MHFTTZN2_concl` (Auto2:595), discharged by
`PackingAuto6.MHFTTZN2` (Rogers.hl:4871).  The interface's `bis` is a
PRIVATE def of PackingAuto2, so the statement here carries its unfolded
body; `exact` closes the goal by delta on that def. -/
theorem MHFTTZN2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), k ≤ 3 → saturated V →
      Packing V → barV V k ul →
      ∀ p : V3, p ∈ (affineSpan ℝ (voronoiList V ul) : Set V3) ↔
        ∀ u ∈ setOfList ul, p ∈ {x : V3 | dist x (hdV ul) = dist x u} :=
  fun V ul k _ _ hP hbar => MHFTTZN2 V ul k hP hbar

/-- `PackingAuto2.MHFTTZN3_concl` (Auto2:604), discharged by
`PackingAuto6.MHFTTZN3` (Rogers.hl:4881).  Shape-verbatim. -/
theorem MHFTTZN3_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), k ≤ 3 → saturated V →
      Packing V → barV V k ul →
      ((affineSpan ℝ (voronoiList V ul) : Set V3) ∩
          (affineSpan ℝ (setOfList ul) : Set V3)) =
        {circumcenter (setOfList ul)} :=
  fun V ul k _ _ hP hbar => MHFTTZN3 V ul k hP hbar

/-- `PackingAuto2.MHFTTZN4_concl` (Auto2:612), discharged by
`PackingAuto6.MHFTTZN4` (Rogers.hl:4985) — shim: the twin states the
orthogonality at the circumcenter; the interface's `q` is rewritten to
it by its defining hypothesis. -/
theorem MHFTTZN4_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ) (u v q : V3), k ≤ 3 →
      saturated V → Packing V → barV V k ul → q = circumcenter (setOfList ul) →
      u ∈ (affineSpan ℝ (voronoiList V ul) : Set V3) →
      v ∈ (affineSpan ℝ (setOfList ul) : Set V3) →
      (u - q) ⬝ᵥ (v - q) = 0 :=
  fun V ul k u v q _ _ hP hbar hq hu hv => by
    rw [hq]; exact MHFTTZN4 V ul k u v hP hbar hu hv

/-- `PackingAuto2.XYOFCGX_concl` (Auto2:621).  TWIN MISMATCH:
`PackingAuto7.XYOFCGX` (Rogers.hl:6559) requires `Packing V`, which the
interface does not carry (nor do the `XYOFCGX_*_0` case lemmas). -/
theorem XYOFCGX_concl_discharged :
    ∀ (V S : Set V3) (p : V3), S ⊆ V → ¬affineDependent S →
      p = circumcenter S → radV S < Real.sqrt 2 →
      ∀ u v : V3, u ∈ S → v ∈ V \ S → dist v p > dist u p := by
  sorry

/-- `PackingAuto2.XNHPWAB1_concl` (Auto2:629), discharged by
`PackingAuto7.XNHPWAB1` (Rogers.hl:7194) — the twin needs neither `k ≤ 3`
nor saturation. -/
theorem XNHPWAB1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
      omegaList V ul = circumcenter (setOfList ul) :=
  fun V ul k _ hP _ hbar hl2 => XNHPWAB1 V ul k hP hbar hl2

/-- `PackingAuto2.XNHPWAB2_concl` (Auto2:636), discharged by
`PackingAuto7.XNHPWAB2` (Rogers.hl:7497). -/
theorem XNHPWAB2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
      omegaList V ul ∈ convexHull ℝ (setOfList ul) :=
  fun V ul k _ hP _ hbar hl2 => XNHPWAB2 V ul k hP hbar hl2

/-- `PackingAuto2.XNHPWAB3_concl` (Auto2:642), discharged by
`PackingAuto7.XNHPWAB3` (Rogers.hl:7926). -/
theorem XNHPWAB3_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
      affDim {omegaListN V ul j | j ∈ Finset.Icc 0 k} = (k : ℤ) :=
  fun V ul k _ hP _ hbar hl2 => XNHPWAB3 V ul k hP hbar hl2

/-- `PackingAuto2.XNHPWAB4_concl` (Auto2:648), discharged by
`PackingAuto7.XNHPWAB4` (Rogers.hl:7691). -/
theorem XNHPWAB4_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
      ∀ i j : ℕ, i < j → j ≤ k →
        hl (truncateSimplex i ul) < hl (truncateSimplex j ul) :=
  fun V ul k _ hP _ hbar hl2 => XNHPWAB4 V ul k hP hbar hl2

/-- `PackingAuto2.WAUFCHE1_concl` (Auto2:656), discharged by
`PackingAuto7.WAUFCHE1` (Rogers.hl:8186). -/
theorem WAUFCHE1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → barV V k ul → hl ul ≤ dist (omegaList V ul) (hdV ul) :=
  fun V ul k _ hP hbar => WAUFCHE1 V ul k hP hbar

/-- `PackingAuto2.WAUFCHE2_concl` (Auto2:661), discharged by
`PackingAuto7.WAUFCHE2` (Rogers.hl:8249). -/
theorem WAUFCHE2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → barV V k ul → hl ul < Real.sqrt 2 →
      hl ul = dist (omegaList V ul) (hdV ul) :=
  fun V ul k _ hP hbar hl2 => WAUFCHE2 V ul k hP hbar hl2

/-- `PackingAuto2.YIFVQDV_concl` (Auto2:667), discharged by
`PackingAuto7.YIFVQDV` (Rogers.hl:9118) — hypothesis reorder only. -/
theorem YIFVQDV_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ) (p : Equiv.Perm ℕ),
      Packing V → saturated V → barV V k ul → hl ul < Real.sqrt 2 →
      permutes p (Set.Icc 0 k) →
      barV V k (leftActionList p ul) ∧
        omegaList V (leftActionList p ul) = omegaList V ul :=
  fun V ul k p hP _ hbar hl2 hperm => YIFVQDV V ul k p hP hbar hl2 hperm

/-- `PackingAuto2.KSOQKWL_concl` (Auto2:676), discharged by
`PackingAuto7.KSOQKWL` (Rogers.hl:9588) — hypothesis reorder only.
STATEMENT-FIX 项 25 (2026-09-30 用户批准): 接口同步补 `hpout`（SF15 同形），
调用点加参穿透——PA7 补前提后本文件源重建曾坏，此处即修复。 -/
theorem KSOQKWL_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (p : Equiv.Perm ℕ) (k : ℕ),
      saturated V → Packing V → barV V k ul → hl ul < Real.sqrt 2 →
      permutes p (Set.Icc 0 k) → (∀ x : ℕ, k < x → p x = x) →
      rogers V ul = rogers V (leftActionList p ul) → p = Equiv.refl ℕ :=
  fun V ul p k _ hP hbar hl2 hperm hpout hrog =>
    KSOQKWL V ul p k hP hbar hl2 hperm hpout hrog

/-- `PackingAuto2.IVFICRK_concl` (Auto2:684).  TWIN MISMATCH:
`PackingAuto7.IVFICRK` (Rogers.hl:9929) carries the same BijOn witness
but its second conjunct has two EXTRA antecedents (`i ∈ Icc 0 (k+1)`,
`permutes σ (Icc 0 k)`) that the interface's pointwise statement does
not allow — the twin is strictly weaker than the interface. -/
theorem IVFICRK_concl_discharged :
    ∀ {A : Type} [Inhabited A] (k : ℕ),
      ∃ g : ℕ × Equiv.Perm ℕ → Equiv.Perm ℕ,
        Set.BijOn g {q : ℕ × Equiv.Perm ℕ | q.1 ∈ Set.Icc 0 (k + 1) ∧
            permutes q.2 (Set.Icc 0 k)}
          {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k + 1))} ∧
        ∀ (ul : List A) (i : ℕ) (σ : Equiv.Perm ℕ) (j : ℕ), ul.length = k + 2 →
          j ≤ k →
          (leftActionList (g (i, σ)) ul).getD j default =
            (leftActionList σ (dropIth ul i)).getD j default := by
  sorry

/-- `PackingAuto2.WQPRRDY_concl` (Auto2:699), discharged by
`PackingAuto7.WQPRRDY` (Rogers.hl:10534). -/
theorem WQPRRDY_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → barV V k ul → hl ul < Real.sqrt 2 →
      convexHull ℝ (setOfList ul) =
        ⋃₀ ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p ul)) ''
          {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 k)}) :=
  fun V ul k _ hP hbar hl2 => WQPRRDY V ul k hP hbar hl2

/-- `PackingAuto2.MXI_EXISTS_concl` (SF37 form: the pack_concl.hl:120-123
interface plus the marchal2.hl:2516 truncation guard).  NO USABLE TWIN: the
only downstream carrier, `PackingAuto12.MXI_EXPLICIT` (marchal2.hl:2516),
consumes THIS interface in its own proof (self-loop); of its two extra
needs the truncation guard is now an interface hypothesis (SF37 — barV
does not bound proper truncations), while `ul = [u0,u1,u2,u3]` is
`BARV_3_EXPLICIT`-derivable from `barV V 3 ul`. -/
theorem MXI_EXISTS_concl_discharged :
    ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
      barV V 3 ul → hl (truncateSimplex 2 ul) < Real.sqrt 2 →
      Real.sqrt 2 ≤ hl ul →
      mxi V ul ∈ convexHull ℝ {omegaListN V ul 2, omegaListN V ul 3} ∧
        dist (mxi V ul) (hdV ul) = Real.sqrt 2 := by
  sorry

/-- `PackingAuto2.EMNWUUS1_concl` (Auto2:716), discharged by
`PackingAuto9.EMNWUUS1` (EMNWUUS.hl:56).  Shape-verbatim. -/
theorem EMNWUUS1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
      barV V 3 ul → (hl ul < Real.sqrt 2 ↔ mcell4 V ul ≠ ∅) :=
  EMNWUUS1

/-- `PackingAuto2.EMNWUUS2_concl` (Auto2:721), discharged by
`PackingAuto9.EMNWUUS2` (EMNWUUS.hl:81).  Shape-verbatim. -/
theorem EMNWUUS2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
      barV V 3 ul →
      (hl ul < Real.sqrt 2 ↔
        mcell0 V ul = ∅ ∧ mcell1 V ul = ∅ ∧ mcell2 V ul = ∅ ∧ mcell3 V ul = ∅) :=
  fun V ul hs hp hbar => EMNWUUS2 V ul hs hp hbar

/-- `PackingAuto2.SLTSTLO1_concl` (Auto2:727), discharged by
`PackingAuto13.SLTSTLO1` (SLTSTLO.hl).  Shape-verbatim. -/
theorem SLTSTLO1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (p : V3), saturated V →
      Packing V → barV V 3 ul → p ∈ rogers V ul →
      ∃ i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul :=
  fun V ul p hs hp hb hpr => SLTSTLO1 V ul p hs hp hb hpr

/-- `PackingAuto2.SLTSTLO2_concl` (Auto2:734), discharged by
`PackingAuto13.SLTSTLO2` (SLTSTLO.hl:582).  Shape-verbatim. -/
theorem SLTSTLO2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3),
      ∃ Z : Set V3, ∀ p : V3, saturated V → Packing V → barV V 3 ul →
        nullSet Z ∧ (p ∈ rogers V ul \ Z → ∃! i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul) :=
  SLTSTLO2

/-- `PackingAuto2.RVFXZBU1_concl` (Auto2:741).  NO TWIN: no downstream
module states the cross-list null-overlap fact (PA13's SLTSTLO2 proof
notes it as NEEDS RVFXZBU1/Auto10, which never landed). -/
theorem RVFXZBU1_concl_discharged :
    ∀ (V : Set V3) (ul vl : List V3) (i j : ℕ), saturated V →
      Packing V → barV V 3 ul → barV V 3 vl → i ≠ j →
      nullSet (mcell i V ul ∩ mcell j V vl) := by
  sorry

/-- `PackingAuto2.RVFXZBU2_concl` (Auto2:748).  NO TWIN anywhere in
Auto3-25 (permutation-forcing from non-null same-index overlap). -/
theorem RVFXZBU2_concl_discharged :
    ∀ (V : Set V3) (ul vl : List V3) (i : ℕ), saturated V →
      Packing V → barV V 3 ul → barV V 3 vl →
      ¬nullSet (mcell i V ul ∩ mcell i V vl) →
      ∃ p : Equiv.Perm ℕ, permutes p (Set.Icc 0 (i - 1)) ∧ vl = leftActionList p ul := by
  sorry

/-- `PackingAuto2.RVFXZBU3_concl` (Auto2:756).  TWIN MISMATCH:
`PackingAuto10.RVFXZBU` (its ENCODING-FIX twin) is restricted to
`i ∈ {0,1,2,3,4}` (its `i = 2,3` branches are still sorried), while the
interface quantifies over ALL `i`; for `i ≥ 5` the tail-fixedness window
`[4, i)` is uncontrolled, so no bridge. -/
theorem RVFXZBU3_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (i : ℕ) (p : Equiv.Perm ℕ),
      saturated V → Packing V → barV V 3 ul → permutes p (Set.Icc 0 (i - 1)) →
      (∀ j : ℕ, i ≤ j → p j = j) →
      mcell i V (leftActionList p ul) = mcell i V ul := by
  sorry

/-- `PackingAuto2.LEPJBDJ_concl` (Auto2:767), discharged by
`PackingAuto11.LEPJBDJ` (LEPJBDJ.hl:29).  Shape-verbatim. -/
theorem LEPJBDJ_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → barV V 3 ul → 1 ≤ k → k ≤ 4 → mcell k V ul ≠ ∅ →
      V ∩ mcell k V ul = setOfList (truncateSimplex (k - 1) ul) :=
  fun V ul k hs hp hb h1 h4 hne => LEPJBDJ V ul k hs hp hb h1 h4 hne

/-- `PackingAuto2.LEPJBDJ_0_concl` (Auto2:774), discharged by
`PackingAuto11.LEPJBDJ_0` (LEPJBDJ.hl:34).  Shape-verbatim. -/
theorem LEPJBDJ_0_concl_discharged :
    ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
      barV V 3 ul → V ∩ mcell 0 V ul = ∅ :=
  fun V ul hs hp hb => LEPJBDJ_0 V ul hs hp hb

/-- `PackingAuto2.HDTFNFZ_concl` (Auto2:779), discharged by
`PackingAuto10.HDTFNFZ`.  Shape-verbatim (implicit binders). -/
theorem HDTFNFZ_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ) (v : V3) (X : Set V3),
      saturated V → Packing V → barV V 3 ul → X = mcell k V ul → ¬nullSet X →
      VX V X = V ∩ X :=
  fun V ul k v X hs hp hb hX hn => @HDTFNFZ V ul k v X hs hp hb hX hn

/-- `PackingAuto2.URRPHBZ1_concl` (Auto2:786), discharged by
`PackingAuto10.URRPHBZ1` (URRPHBZ1.hl:686).  Shape-verbatim. -/
theorem URRPHBZ1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → barV V 3 ul → MeasurableSet (mcell k V ul) :=
  fun V ul k hs hp hb => URRPHBZ1 V ul k hs hp hb

/-- `PackingAuto2.URRPHBZ2_concl` (Auto2:791), discharged by
`PackingAuto13.URRPHBZ2`.  Shape-verbatim. -/
theorem URRPHBZ2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ) (v : V3),
      saturated V → Packing V → barV V 3 ul → v ∈ V →
      EventuallyRadial v (mcell k V ul) :=
  fun V ul k v hs hp hb hv => URRPHBZ2 V ul k v hs hp hb hv

/-- `PackingAuto2.URRPHBZ3_concl` (Auto2:798), discharged by
`PackingAuto17.URRPHBZ3` (via `hdtfnfz_p17` + `CLOSED_MCELL`).  The twin
is genuinely proved (sorry-free kernel); shape-verbatim. -/
theorem URRPHBZ3_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ) (v : V3),
      saturated V → Packing V → barV V 3 ul → ¬nullSet (mcell k V ul) →
      v ∈ V \ VX V (mcell k V ul) →
      ∃ t : ℝ, t > 0 ∧ ∀ p ∈ mcell k V ul, t < dist p v :=
  fun V ul k v hs hp hb hn hv => URRPHBZ3 hs hp hb hn hv

/-- `PackingAuto2.QZYZMJC_concl` (Auto2:806), discharged by
`PackingAuto16.QZYZMJC`.  Shape-verbatim. -/
theorem QZYZMJC_concl_discharged :
    ∀ (V : Set V3) (v : V3), saturated V → Packing V → v ∈ V →
      setSum {X | mcellSet V X ∧ v ∈ VX V X} (fun t => sol v t) = 4 * Real.pi :=
  fun V v hs hp hv => QZYZMJC V v hs hp hv

/-- `PackingAuto2.KIZHLTL1_concl` (Auto2:812), discharged by
`PackingAuto16.KIZHLTL1` (KIZHLTL.hl:46).  DELTA BRIDGE: the twin's
conclusion is stated over its public `voronoiOpenP16`, whose body is
identical to Auto2's PRIVATE `voronoiOpen`; the statement here carries
the unfolded body and `exact` closes by delta. -/
theorem KIZHLTL1_concl_discharged :
    ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V →
      1 ≤ r →
      setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} volume.real +
          c * r ^ 2 ≤
        setSum (V ∩ Metric.ball 0 r)
          (fun u => volume.real {x : V3 | ∀ w ∈ V, w ≠ u → dist x u < dist x w}) :=
  KIZHLTL1

/-- `PackingAuto2.KIZHLTL2_concl` (Auto2:820), discharged by
`PackingAuto16.KIZHLTL2` (KIZHLTL.hl:285).  Shape-verbatim. -/
theorem KIZHLTL2_concl_discharged :
    ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V →
      1 ≤ r →
      ((Nat.card ((V ∩ Metric.ball 0 r : Set V3)) : ℕ) : ℝ) * 8 * mm1 + c * r ^ 2 ≤
        (2 * mm1 / Real.pi) *
          setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} (totalSolid V) :=
  KIZHLTL2

/-- `PackingAuto2.KIZHLTL3_concl` (Auto2:828), discharged by
`PackingAuto16.KIZHLTL3`.  Shape-verbatim (NOTE: no HL proof exists for
this general-`f` form anywhere; the twin is sorried, taint flows). -/
theorem KIZHLTL3_concl_discharged :
    ∀ (V : Set V3) (f : ℝ → ℝ), ∃ c : ℝ, ∀ r : ℝ,
      saturated V → Packing V → 1 ≤ r →
      (∃ c1 : ℝ, ∀ x : ℝ, 2 ≤ x ∧ x < Real.sqrt 8 → |f x| ≤ c1) →
      ((8 * mm2 / Real.pi) *
            setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
              (fun X => setSum (edgeX V X) fun e =>
                let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
                dihX V X (q.1, q.2) * f (hl [q.1, q.2]))
          + c * r ^ 2 ≤
        8 * mm2 * setSum (V ∩ Metric.ball 0 r)
          (fun u => setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v < Real.sqrt 8}
            (fun v => f (hl [u, v])))) :=
  KIZHLTL3

/-- `PackingAuto2.OXLZLEZ_concl` (Auto2:843), discharged by
`PackingAuto25.OXLZLEZ` — THE CAPSTONE wiring.  The twin's kernel
(by_contra → CELL_CLUSTER_ESTIMATE_PROPS → GRHIDFA_concl) is real, but it
is conditional on the two Merge_ineq/Oxl_def bank antecedents
`pack_nonlinear_non_ox3q1h` (PackingAuto21:147) and `ox3q1hP25`
(PackingAuto25:88), both upstream `Prop := sorry` placeholders the
interface does not carry; they are supplied `by sorry` here, so the
reachable debt is exactly the twin's kernel plus the two bank leaves. -/
theorem OXLZLEZ_concl_discharged :
    ∀ V : Set V3, saturated V → Packing V →
      cellClusterInequality V :=
  fun V hs hp => OXLZLEZ V (by sorry) (by sorry) hp hs

/-- `PackingAuto2.UPFZBZM_concl` (Auto2:854), discharged by
`PackingAuto19.UPFZBZM` (UPFZBZM.hl:227).  Shape-verbatim; the twin's
witness is real but leans on the sorried `NEGLIGIBLE_FUNC`/
`FCC_COMPATABILITY_FUNC` pair — taint flows. -/
theorem UPFZBZM_concl_discharged :
    ∀ V : Set V3, saturated V → Packing V →
      cellClusterInequality V → TSKAJXY_statement → lmfunInequality V →
      ∃ G : V3 → ℝ, negligibleFun0 G V ∧ fccCompatible G V :=
  fun V hs hp hcc hT hlm => UPFZBZM V hs hp hcc hT hlm

/-! ## F1 transplant: `RDWKARC_concl` assembly over `PackingAuto19.UPFZBZM`

Lane `packingconcl-c1-stage1` (2026-11-03).  This is the port of
`f1-upfzbzm-rewire`'s `rdwkarcConcl_p25` into the e2e consumer endpoint:
`Kepler.Assembly.textCapstone` consumes the packing-chapter capstone through
this file, so the F1 re-wire lands here rather than in PA25 (PA25 / PA19 /
PA2 stay untouched).  The three private kit lemmas below are the only pieces
of the `_p2` kit of `PackingAuto2` that are not publicly available
(`hlPairAdd`, `setSumCongr`, `setSumImage`); the translation/radius and
`JGXZYGW_KY` kits are consumed from `PackingAuto19` (public, proved).
`rdwkarcConcl_pc` re-derives the `RDWKARC_concl` assembly verbatim with
`UPFZBZM` (PackingAuto19, real proof) in place of the interface constant
`UPFZBZM_concl` (PackingAuto2). -/

/-- `hl` re-indexing bridge: `hl [0, a] = hl [u, a + u]` for `a ≠ 0`
(RDWKARC.hl closing segment; via `RADV_TRANS_EQ` and the `setOfList` pair
form, same route as PA2's private `hlPairAdd_p2`). -/
private theorem hlPairAdd_pc {a u : V3} (ha : a ≠ 0) : hl [0, a] = hl [u, a + u] := by
  have hsl : ∀ x y : V3, setOfList [x, y] = {x, y} := by
    intro x y
    ext b
    simp [setOfList]
  have hkey := RADV_TRANS_EQ (0 : V3) a u (Ne.symm ha)
  rw [zero_add] at hkey
  show radV (setOfList [0, a]) = radV (setOfList [u, a + u])
  rw [hsl, hsl]
  exact hkey

/-- `setSum` respects pointwise congruence of the summand (same route as PA2's
private `setSumCongr_p2`). -/
private theorem setSumCongr_pc {α : Type*} {s : Set α} {f g : α → ℝ}
    (h : ∀ a ∈ s, f a = g a) : setSum s f = setSum s g := by
  by_cases hs : Set.Finite s
  · unfold setSum
    rw [dif_pos hs, dif_pos hs]
    exact Finset.sum_congr rfl fun a ha => h a (hs.mem_toFinset.mp ha)
  · unfold setSum
    rw [dif_neg hs, dif_neg hs]

/-- `setSum` re-indexes along an injective image (Lean form of HOL
`SUM_EQ_GENERAL_INVERSES`; junk convention wagers finiteness on both sides,
same route as PA2's private `setSumImage_p2`). -/
private theorem setSumImage_pc (g : V3 → V3) (A : Set V3) (f : V3 → ℝ)
    (hinj : Set.InjOn g A) (hA : A.Finite) :
    setSum (g '' A) f = setSum A (fun a => f (g a)) := by
  classical
  have himg : (g '' A).Finite := hA.image g
  unfold setSum
  rw [dif_pos himg, dif_pos hA, Set.Finite.toFinset_image g hA himg,
    Finset.sum_image (fun a ha b hb h => hinj (hA.mem_toFinset.mp ha)
      (hA.mem_toFinset.mp hb) h)]

/-- HOL `RDWKARC` (RDWKARC.hl:180-314), `_pc` re-wiring of the
`RDWKARC_concl` assembly: unpack `¬kepler_conjecture` to a failing witness
`V`; if `lmfunInequality V` held, `UPFZBZM` (PackingAuto19) + `JGXZYGW_KY`
would give the density bound — contradiction; hence some `u ∈ V` has edge
lmfun-sum `> 12`; the witness `{v | v + u ∈ V} ∩ ballAnnulus` is a packing
(`PACKING_TRANS`) inside the annulus, and its annulus sum re-indexes along
`v ↦ v + u` to the `V`-edge sum (`setSumImage_pc` / `setSumCongr_pc`,
packing separation for the `v = u` junk case, `hl` translation invariance via
`RADV_TRANS_EQ`).

Replaces the `PackingAuto2.RDWKARC_concl` consumer edge of
`PACKING_CHAPTER_MAIN_CONCLUSION` (F1 UPFZBZM re-wire, 2026-11-03). -/
theorem rdwkarcConcl_pc : ¬keplerConjecture →
    (∀ V : Set V3, Packing V → saturated V → cellClusterInequality V) →
    TSKAJXY_statement →
    ∃ V : Set V3, Packing V ∧ V ⊆ ballAnnulus ∧ ¬localAnnulusInequality V := by
  intro hkc hcc hT
  -- RDWKARC.hl:189-193 — unpack `¬kepler_conjecture` to a failing witness.
  obtain ⟨V, hP, hs, hden⟩ : ∃ V : Set V3, Packing V ∧ saturated V ∧
      ¬(∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
        volume.real (((⋃ v ∈ V, Metric.ball v 1) ∩ Metric.ball 0 r : Set V3)) /
          volume.real (Metric.ball (0 : V3) r) ≤ Real.pi / Real.sqrt 18 + c / r) := by
    by_contra hex
    refine hkc fun V hV => ?_
    by_contra hc
    exact hex ⟨V, hV.1, hV.2, hc⟩
  -- RDWKARC.hl:196-215 — `lmfunInequality V` would give the density bound
  -- via UPFZBZM + JGXZYGW_KY; contradiction.
  have hnlm : ¬lmfunInequality V := by
    intro hlm
    obtain ⟨G, hG0, hGf⟩ := UPFZBZM V hs hP (hcc V hP hs) hT hlm
    exact hden (JGXZYGW_KY V hP hs ⟨G, hGf, hG0⟩)
  -- RDWKARC.hl:217-222 — extract `u ∈ V` with edge lmfun-sum > 12.
  obtain ⟨u, hu, hsum⟩ : ∃ u : V3, u ∈ V ∧
      12 < setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
        (fun v => lmfun (hl [u, v])) := by
    by_contra hall
    push Not at hall
    exact hnlm hall
  have hPT : Packing {v : V3 | v + u ∈ V} := PACKING_TRANS V hP u
  -- Membership of the witness in terms of distances (annulus ↔ edge set).
  have hAann : ∀ v : V3, v ∈ {w : V3 | w + u ∈ V} ∩ ballAnnulus →
      v + u ∈ V ∧ dist 0 v ≤ 2 * h0 ∧ 2 ≤ dist 0 v := by
    intro v hv
    rw [Set.mem_inter_iff] at hv
    obtain ⟨hm, hann⟩ := hv
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball] at hann
    refine ⟨hm, ?_, ?_⟩
    · rw [dist_comm]; exact hann.1
    · rw [dist_comm]; exact le_of_not_gt hann.2
  have hballmem : ∀ v : V3, dist 0 v ≤ 2 * h0 → 2 ≤ dist 0 v → v ∈ ballAnnulus := by
    intro v hle h2
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball]
    refine ⟨?_, ?_⟩
    · rw [dist_comm]; exact hle
    · intro hb
      rw [dist_comm] at hb
      exact absurd hb (not_lt.2 h2)
  have hAfin : ({v : V3 | v + u ∈ V} ∩ ballAnnulus).Finite := by
    refine Set.Finite.subset (hPT.finite_inter_ball (2 * h0 + 1)) ?_
    intro v hv
    obtain ⟨hm, hle, -⟩ := hAann v hv
    refine Set.mem_inter hm (Metric.mem_ball.2 ?_)
    rw [dist_comm]
    linarith
  refine ⟨{v : V3 | v + u ∈ V} ∩ ballAnnulus, ?_, Set.inter_subset_right, ?_⟩
  · -- packing of the witness: PACKING_TRANS then subset.
    intro a ha b hb hlt
    rw [Set.mem_inter_iff] at ha hb
    exact hPT a ha.1 b hb.1 hlt
  · -- RDWKARC.hl:226-314 — the annulus sum re-indexes to the V-edge sum.
    intro hLAI
    have hinj : Set.InjOn (fun a : V3 => a + u)
        ({v : V3 | v + u ∈ V} ∩ ballAnnulus) := fun _ _ _ _ h => add_right_cancel h
    have hTeq : {v : V3 | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0} =
        (fun a : V3 => a + u) '' ({v : V3 | v + u ∈ V} ∩ ballAnnulus) := by
      ext w
      constructor
      · rintro ⟨hwV, hwu, hdu⟩
        have hdu2 : dist 0 (w - u) = dist u w := by
          rw [dist_eq_norm, dist_eq_norm]; abel
        have h2wu : 2 ≤ dist u w := Packing.dist_ge_two hP hu hwV (Ne.symm hwu)
        have hVin : w - u + u = w := by abel
        have hinV : (w - u) + u ∈ V := by rw [hVin]; exact hwV
        have hle : dist 0 (w - u) ≤ 2 * h0 := by rw [hdu2]; exact hdu
        have h2 : 2 ≤ dist 0 (w - u) := by rw [hdu2]; exact h2wu
        refine ⟨w - u, Set.mem_inter hinV (hballmem _ hle h2), hVin⟩
      · rintro ⟨a, ha, rfl⟩
        show a + u ∈ {v : V3 | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
        obtain ⟨haV, hle, ha2⟩ := hAann a ha
        have ha0 : a ≠ 0 := by
          intro h0
          rw [h0] at ha2
          rw [dist_self] at ha2
          linarith
        refine ⟨haV, ?_, ?_⟩
        · intro h
          have h' : a + u = (0 : V3) + u := by rw [zero_add]; exact h
          exact ha0 (add_right_cancel h')
        · have hd : dist u (a + u) = dist 0 a := by
            rw [dist_eq_norm, dist_eq_norm]; abel
          rw [hd]; exact hle
    have key : setSum ({v : V3 | v + u ∈ V} ∩ ballAnnulus)
        (fun w => lmfun (hl [0, w])) =
        setSum {v : V3 | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
          (fun v => lmfun (hl [u, v])) := by
      rw [hTeq, setSumImage_pc (fun a : V3 => a + u) _ _ hinj hAfin]
      refine setSumCongr_pc fun a ha => ?_
      obtain ⟨-, -, ha2⟩ := hAann a ha
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0] at ha2
        rw [dist_self] at ha2
        linarith
      show lmfun (hl [0, a]) = lmfun (hl [u, a + u])
      rw [hlPairAdd_pc ha0]
    unfold localAnnulusInequality at hLAI
    rw [key] at hLAI
    linarith

/- Note (lane packingconcl-c1-stage1): the body below is now `rdwkarcConcl_pc`
(PA19 `UPFZBZM` re-derivation); the statement is frozen verbatim. -/
/-- `PackingAuto2.RDWKARC_concl` (Auto2:860), discharged by
`PackingAuto19.RDWKARC` (RDWKARC.hl).  Shape-verbatim. -/
theorem RDWKARC_concl_discharged :
    ¬keplerConjecture →
    (∀ V : Set V3, Packing V → saturated V → cellClusterInequality V) →
    TSKAJXY_statement →
    ∃ V : Set V3, Packing V ∧ V ⊆ ballAnnulus ∧ ¬localAnnulusInequality V :=
  rdwkarcConcl_pc

/-- `PackingAuto25.PACKING_CHAPTER_MAIN_CONCLUSION` (PA25:12302), the e2e
packing-chapter capstone.  Statement verbatim to the PA25 anchor; the body
routes through `rdwkarcConcl_pc` (PA19 `UPFZBZM` real proof) and supplies
the two `RDWKARC_concl` antecedents from the caller's `hnl` / `hox`:
`hcc` is the `OXLZLEZ` kernel and the pointwise `TSKAJXY_statement` is
PA21's `TSKAJXY` at the bank `hnl`. -/
theorem PACKING_CHAPTER_MAIN_CONCLUSION_discharged (hkc : ¬ keplerConjecture)
    (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25) :
    ∃ V : Set V3, Packing V ∧ V ⊆ ballAnnulus ∧ ¬ localAnnulusInequality V := by
  refine rdwkarcConcl_pc hkc ?_ ?_
  · intro V hp hs
    exact OXLZLEZ V hnl hox hp hs
  · intro V X hs hp hm hcrit
    exact TSKAJXY V X hnl hs hp hm hcrit


/-- `PackingAuto2.GOTCJAH_concl` (Auto2:867).  TWIN MISMATCH:
`PackingAuto22.GOTCJAH` (counting_spheres.hl:4366) is a different
encoding — `fchanged c = WF` vs the interface's
`topologicalComponentYfan` membership, `asn` vs `Real.arcsin`,
`0 ∈ interior P`/`0 < b`/facet-cardinality vs the interface's
nonempty-facet + component + `extremePoints`-card hypotheses.  No bridge
without real geometry; PA22 deliberately not imported. -/
theorem GOTCJAH_concl_discharged :
    ∀ (s : Set V3) (f : Set V3) (v : V3) (b : ℝ) (WF : Set V3)
      (h : ℝ) (k : ℕ), polyhedron s → Bornology.IsBounded s →
      (∃ r : ℝ, r > 0 ∧ Metric.ball 0 r ⊆ s) → FacetOf f s →
      f = {p : V3 | p ⬝ᵥ v = b} ∩ s →
      WF ∈ Kepler.Text.Fan.topologicalComponentYfan 0 (fanOfPolyhedron s).1
        (fanOfPolyhedron s).2 →
      f ∩ WF ≠ ∅ →
      rconeGt 0 v h ⊆ WF →
      k = Nat.card {u : V3 | u ∈ Set.extremePoints ℝ f} →
      2 * Real.pi - 2 * (k : ℝ) * Real.arcsin (h * Real.sin (Real.pi / k)) ≤
        sol 0 WF := by
  sorry

/-- `PackingAuto2.TIWWFYQ_concl` (Auto2:884), discharged by
`PackingAuto5.TIWWFYQ` (pack3.hl:564).  Shape-verbatim. -/
theorem TIWWFYQ_concl_discharged :
    ∀ (V : Set V3) (p : V3), Packing V → saturated V →
      ∃ v : V3, v ∈ V ∧ p ∈ voronoiClosed V v :=
  fun V p hV hs => TIWWFYQ V p hV hs

/-- `PackingAuto2.VORONOI_BALL2_concl` (Auto2:889), discharged by
`PackingAuto5.VORONOI_BALL2` (pack3.hl:767).  Shim: the twin needs only
`saturated V`; the interface's `Packing V` and `v ∈ V` are discarded. -/
theorem VORONOI_BALL2_concl_discharged :
    ∀ (V : Set V3) (v : V3), Packing V → saturated V → v ∈ V →
      voronoiClosed V v ⊆ Metric.ball v 2 :=
  fun V v _ hs _ => VORONOI_BALL2 V v hs

/-- `PackingAuto2.VORONOI_INTER_BIS_LE_concl` (Auto2:894), discharged by
`PackingAuto5.VORONOI_INTER_BIS_LE` (pack3.hl:823).  Shape-verbatim
(twin is sorried; taint flows). -/
theorem VORONOI_INTER_BIS_LE_concl_discharged :
    ∀ (V : Set V3) (v : V3), Packing V → saturated V →
      v ∈ V →
      voronoiClosed V v =
        ⋂₀ ((fun u : V3 => bisLe v u) ''
          {u : V3 | u ∈ V ∧ u ∈ Metric.ball v 4 ∧ u ≠ v}) :=
  fun V v hV hs hv => VORONOI_INTER_BIS_LE V v hV hs hv

/-- `PackingAuto2.VORONOI_POLYHEDRON_concl` (Auto2:902), discharged by
`PackingAuto5.VORONOI_POLYHEDRON` (pack3.hl:916; sorried — taint
flows). -/
theorem VORONOI_POLYHEDRON_concl_discharged :
    ∀ (V : Set V3) (v : V3), Packing V → saturated V →
      v ∈ V → polyhedron (voronoiClosed V v) :=
  fun V v hV hs hv => VORONOI_POLYHEDRON V v hV hs hv

/-- `PackingAuto2.DRUQUFE_concl` (Auto2:913), discharged by
`PackingAuto5.DRUQUFE` (pack3.hl:970).  Shape-verbatim. -/
theorem DRUQUFE_concl_discharged :
    ∀ (V : Set V3) (v : V3), Packing V → saturated V →
      IsCompact (voronoiClosed V v) ∧ Convex ℝ (voronoiClosed V v) ∧
        MeasurableSet (voronoiClosed V v) :=
  DRUQUFE

/-- `PackingAuto2.KHEJKCI_concl` (Auto2:919), discharged by
`PackingAuto6.KHEJKCI` (Rogers.hl:142) — shim: the interface's
`vorList V k ul` is `barV V k ul ∧ hl ul < sqrt 2` (Auto2:278), and the
twin needs only the `.1` conjunct. -/
theorem KHEJKCI_concl_discharged :
    ∀ (V : Set V3) (k : ℕ) (ul : List V3), saturated V →
      Packing V → vorList V k ul →
      FaceOf (voronoiList V ul) (voronoiClosed V (hdV ul)) :=
  fun V k ul hs hp hv => KHEJKCI V k ul hs hp hv.1

/-- `PackingAuto2.GRUTOTI1_concl` (Auto2:926), discharged by
`PackingAuto23.GRUTOTI` (GRUTOTI.hl:60-8001; proved in the GT-5/GT-6
waves, 2026-10-10) — shape-verbatim over this interface, so the wiring
is a direct rename. The PA24 statement-copy
(`GRUTOTI1_concl_p24_pub`) is off the discharge path since 2026-10-12;
it stays in PA24 because the EV20 duplicate-provision conditions do not
hold (PA23's provider is named `GRUTOTI`, and the twin's set-builder
carries an explicit `: Set V3` binder ascription). Residual taint in
the axiom footprint is PA23's own upstream chain (AJRIPQN et al.), no
longer the Auto2 interface.
2026-11-03 (lane island-wire-w1): the documented direct rename is now
executed at term level — the proof term is `GRUTOTI` itself (PA23 joined
the import set above; its closure is clash-free), so `GRUTOTI1_concl_p24_pub`
is truly consumer-free as its own docstring states. -/
theorem GRUTOTI1_concl_discharged :
    ∀ (V : Set V3) (u0 u1 : V3) (e : Set V3), saturated V →
      Packing V → u0 ∈ V → u1 ∈ V → u0 ≠ u1 → hl [u0, u1] < Real.sqrt 2 →
      e = {u0, u1} →
      setSum {X | mcellSet V X ∧ e ∈ edgeX V X} (fun t => dihX V t (u0, u1)) =
        2 * Real.pi :=
  GRUTOTI

/-- `PackingAuto2.REUHADY_concl` (Auto2:935), discharged by
`PackingAuto24.REUHADY_p24` (REUHADY.hl) — statement-identical
(discharge candidate marked at the PA24 copy; sorried — taint flows). -/
theorem REUHADY_concl_discharged :
    ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3) (v1 v2 : V3)
      (e : Set V3) (w1 w2 : V3), saturated V → Packing V → dist u0 u1 < Real.sqrt 8 →
      e = {u0, u1} → ¬(azim u0 u1 w1 w2 = 0) →
      hl vl1 < Real.sqrt 2 ∧ hl vl2 < Real.sqrt 2 →
      barV V 2 vl1 ∧ barV V 2 vl2 →
      setOfList (truncateSimplex 1 vl1) = e ∧
      setOfList (truncateSimplex 1 vl2) = e ∧
      v1 = elV vl1 2 ∧ v2 = elV vl2 2 ∧
      (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
        X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) →
      setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
          X ⊆ wedgeGe u0 u1 v1 v2} (fun t => dihX V t (u0, u1)) =
        azim u0 u1 v1 v2 :=
  REUHADY_p24

/-- `PackingAuto2.REUHADY_concl_version2` (Auto2:953), discharged by
`PackingAuto24.REUHADY_version2_p24` — statement-identical (sorried —
taint flows). -/
theorem REUHADY_concl_version2_discharged :
    ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3)
      (v1 v2 : V3) (e : Set V3), saturated V → Packing V → dist u0 u1 < Real.sqrt 8 →
      e = {u0, u1} →
      wedgeGe u0 u1 v1 v2 ∩ wedgeGe u0 u1 v2 v1 ⊆
        affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} →
      hl vl1 < Real.sqrt 2 ∧ hl vl2 < Real.sqrt 2 →
      barV V 2 vl1 ∧ barV V 2 vl2 →
      setOfList (truncateSimplex 1 vl1) = e ∧
      setOfList (truncateSimplex 1 vl2) = e ∧
      v1 = elV vl1 2 ∧ v2 = elV vl2 2 ∧
      (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
        X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) →
      setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
          X ⊆ wedgeGe u0 u1 v1 v2} (fun t => dihX V t (u0, u1)) =
        azim u0 u1 v1 v2 :=
  REUHADY_version2_p24

/-! ## Auto3 `OXLZLEZ1.hl` family — discharged via PA4's public `*_v11` twins

All nine interfaces live over `PackingAuto3.CcV11`.  Their downstream
carriers in `PackingAuto4` (the OXLZLEZ2 wave: `CHQSQEY`, `MTMLSRF`,
`LXDEYBO`, `UNPNFVW`, `IPVICGW`, `RSIWAMP`, `UTEOITF`, `LUIKGMH`,
`GRHIDFA`) are stated over a PRIVATE `structure CC4P4` with private
accessors — a parallel encoding of the same HL content that no other
module could name, which kept this family blocked.  The CC4P4-exposure
wave added public `CcV11`-stated `*_v11` rows to PA4 (verbatim to the
`*_concl` interfaces below); PA4 is now imported and each entry is a
term-level discharge.  The `*_v11` bodies are `sorry` (skeleton batch —
PA4's private `CC4P4` twins are the eventual proof bank), so sorryAx
flows through every entry here.  (PA25's cc-block consumes these
interfaces via `cc_data_v8`, it does not prove them.) -/

/-- `PackingAuto3.CHSQSQEY_concl` (OXLZLEZ1.hl:135), discharged by
`PackingAuto4.CHQSQEY_v11` — the PA4 twin newly exposed in this wave as a
PUBLIC `CcV11`-stated row (previously reachable only over PA4's private
`CC4P4`); its body is `sorry` (skeleton batch), so taint flows. -/
theorem CHQSQEY_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    3 ≤ cc_size_v11 cc (cc_4cell_v11 cc) :=
  CHQSQEY_v11 cc _hb _hp _hr _hsum

/-- `PackingAuto3.MTMLSRF_concl` (OXLZLEZ1.hl:138), discharged by
`PackingAuto4.MTMLSRF_v11` (public `CcV11` twin; sorry body — taint
flows). -/
theorem MTMLSRF_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∃ i, 0 < i ∧ cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧
      cc_4cell_v11 cc (i + 1) ∧ cc_4cell_v11 cc (i - 1) :=
  MTMLSRF_v11 cc _hb _hp _hr _hsum

/-- `PackingAuto3.LXDEYBO_concl` (OXLZLEZ1.hl:142), discharged by
`PackingAuto4.LXDEYBO_v11` (public `CcV11` twin; sorry body — taint
flows). -/
theorem LXDEYBO_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_size_v11 cc (cc_4cell_v11 cc) ≤ 4 :=
  LXDEYBO_v11 cc _hb _hp _hr _hsum

/-- `PackingAuto3.UNPNFVW_concl` (OXLZLEZ1.hl:145), discharged by
`PackingAuto4.UNPNFVW_v11` (public `CcV11` twin; sorry body — taint
flows). -/
theorem UNPNFVW_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_size_v11 cc (cc_qy_v11 cc) ≤ 1 :=
  UNPNFVW_v11 cc _hb _hp _hr _hsum

/-- `PackingAuto3.IPVICGW_concl` (OXLZLEZ1.hl:156), discharged by
`PackingAuto4.IPVICGW_v11` (public `CcV11` twin; sorry body — taint
flows). -/
theorem IPVICGW_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∀ i, cc_small_v11 cc i :=
  IPVICGW_v11 cc _hb _hp _hr _hsum

/-- `PackingAuto3.RSIWAMP_concl` (OXLZLEZ1.hl:159), discharged by
`PackingAuto4.RSIWAMP_v11` (public `CcV11` twin; sorry body — taint
flows). -/
theorem RSIWAMP_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_card_v11 cc ≤ 4 :=
  RSIWAMP_v11 cc _hb _hp _hr _hsum

/-- `PackingAuto3.UTEOITF_concl` (OXLZLEZ1.hl:167), discharged by
`PackingAuto4.UTEOITF_v11` (public `CcV11` twin; sorry body — taint
flows). -/
theorem UTEOITF_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∀ i, cc_4cell_v11 cc i :=
  UTEOITF_v11 cc _hb _hp _hr _hsum

/-- `PackingAuto3.LUIKGMH_concl` (OXLZLEZ1.hl:170), discharged by
`PackingAuto4.LUIKGMH_v11` (public `CcV11` twin; sorry body — taint
flows). -/
theorem LUIKGMH_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    4 ≤ cc_card_v11 cc :=
  LUIKGMH_v11 cc _hb _hp _hr _hsum

/-- `PackingAuto3.GRHIDFA_concl` (OXLZLEZ1.hl:173), discharged by
`PackingAuto4.GRHIDFA_v11` (public `CcV11` twin; sorry body — taint
flows).  (PA25.OXLZLEZ 的 kernel 在等价的 v11 数据上消费本条目。) -/
theorem GRHIDFA_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    False :=
  GRHIDFA_v11 cc _hb _hp _hr _hsum

-- Self-checks.  Ground truth = `#print axioms`, not prose:
--  * the first three are the sorry-free discharges of the previous wave
--    (expect exactly `[propext, Classical.choice, Quot.sound]`);
--  * the wired entries below are EXPECTED to list `sorryAx` — that is the
--    honest reachable-debt expansion (taint flows through the twins /
--    bank placeholders).
#print axioms EMNWUUS1_concl_discharged
#print axioms VORONOI_BALL2_concl_discharged
#print axioms DRUQUFE_concl_discharged
#print axioms OXLZLEZ_concl_discharged
#print axioms REUHADY_concl_discharged
#print axioms REUHADY_concl_version2_discharged
-- GRUTOTI1 wave: twin un-privatized via PA24's `GRUTOTI1_concl_p24_pub`;
-- 2026-11-03 island-wire-w1: term re-pointed to PA23's proved `GRUTOTI`
-- (residual `sorryAx`, if any, is PA23's own upstream chain — AJRIPQN et al.
-- — no longer the Auto2 interface).
#print axioms GRUTOTI1_concl_discharged
#print axioms URRPHBZ3_concl_discharged
-- CC4P4-exposure wave: the nine newly verbatim-wired Auto3-family rows
-- (expect `sorryAx` on each — the PA4 `*_v11` twins are sorried).
#print axioms CHQSQEY_concl_discharged
#print axioms MTMLSRF_concl_discharged
#print axioms LXDEYBO_concl_discharged
#print axioms UNPNFVW_concl_discharged
#print axioms IPVICGW_concl_discharged
#print axioms RSIWAMP_concl_discharged
#print axioms UTEOITF_concl_discharged
#print axioms LUIKGMH_concl_discharged
#print axioms GRHIDFA_concl_discharged

/-! ### PA21 materialization capstone (lane lv8-pa21-w1, 2026-11-04,
after the leftover-mat-scout workorder LV8): the 110 public top-level
PackingAuto21 clean theorem exits that no e2e root reaches, re-exposed
as ONE conjunction (fresh re-probe measured before this edit; scout logs,
seeds_clean.txt 1..110).  Self-contained section: pure insertion,
zero new imports (PA21 already imported at :122), zero proof
obligations (body = the exit assembly itself).  -/

/-- PA21 materialization capstone (scout lane leftover-mat-scout,
implementation lane lv8-pa21-w1, 2026-11-04).  The 110 public top-level
PackingAuto21 theorem exits unreachable from every e2e root (orphan
census: PA21 294 orphans = 110 top-public clean + 116 private + 66
simp-derived + 2 defs; fresh re-probe (logs/pa21_probe_fresh.out):
GROUP_VS_CONE fresh 136 sorried
0, i.e. the new closure is sorried-0,
K_SORRIED 134 and the standard-three axiom face
unchanged) are re-exposed as ONE conjunction (none dropped).
Anchors (no fabricated edges): every conjunct is asserted in the
verbatim wording of its exit's complete elaborated signature -- the
`#check @name` printer dump (logs/pa21_probe_fresh.out), the only
uniform verbatim source since ~60 of the 110 exits are compiler-
generated equation lemmas (`*.eq_1` / `*._abel_*`) with no source
statement anywhere; semantic identity is re-verified by the `⟨...⟩`
assembly below (each element must unify definitionally with its
conjunct); the per-conjunct comments carry the exit's PA21 source
declaration line / HOL docstring anchor where one exists.
Conjunct order: the scout seed-list order (seeds_clean.txt 1..110,
probe1 PA21 SEED list sorted).  Body = the assembly of the exit
constants -- zero new proof obligations, zero new imports. -/
theorem pa21_capstone_w1 :
    -- 1. Kepler.Text.ATN2_Y_NEG (PA21:6175; HOL `ATN2_Y_NEG`)
    (∀ (x y : ℝ), y < 0 → atn2 x y = -(Real.pi / 2) - Real.arctan (x / y)
    ) ∧
    -- 2. Kepler.Text.ATN_DIV (PA21:6161; HOL `ATN_DIV`)
    (∀ (x y : ℝ), 0 < x → 0 < y → Real.arctan (x / y) = Real.pi / 2 - Real.arctan (y / x)
    ) ∧
    -- 3. Kepler.Text.BALL_SUBSET_BIS_LE (PA21:9016; HOL `BALL_SUBSET_BIS_LE`)
    (∀ (u v : V3) (r : ℝ), 2 * r ≤ dist u v → Metric.ball u r ⊆ bisLe u v
    ) ∧
    -- 4. Kepler.Text.BALL_SUBSET_BIS_LT (PA21:9029; HOL `BALL_SUBSET_BIS_LT`)
    (∀ (u v : V3) (r : ℝ), 2 * r ≤ dist u v → Metric.ball u r ⊆ {y | dist y u < dist y v}
    ) ∧
    -- 5. Kepler.Text.BIS_LE_INTER (PA21:5958; HOL `BIS_LE_INTER`)
    (∀ (u0 u1 : V3), bisLe u0 u1 ∩ bisLe u1 u0 = bis u0 u1
    ) ∧
    -- 6. Kepler.Text.BIS_LE_UNION (PA21:5968; HOL `BIS_LE_UNION`)
    (∀ (u0 u1 : V3), bisLe u0 u1 ∪ bisLe u1 u0 = univ
    ) ∧
    -- 7. Kepler.Text.BIS_LT_NORM (PA21:7302; HOL `BIS_LT_NORM`)
    (∀ (u v x : V3), dist x u < dist x v ↔ (x - u).ofLp ⬝ᵥ (v.ofLp - u.ofLp) < ‖v - u‖ ^ 2 / 2
    ) ∧
    -- 8. Kepler.Text.CONV_CONVEX_HULL (PA21:5797; HOL `CONV_CONVEX_HULL`)
    (∀ (s : Set V3), Convex ℝ s ↔ (convexHull ℝ) s = s
    ) ∧
    -- 9. Kepler.Text.DIFF_INTER (PA21:5625; HOL `DIFF_INTER`)
    (∀ (X Y Z : Set V3), X \ Y ∩ Z = (X ∩ Z) \ Y
    ) ∧
    -- 10. Kepler.Text.DIST_LAW_OF_COS_ALT (PA21:6143; HOL `DIST_LAW_OF_COS_ALT`)
    (∀ (u v w : V3),
          dist v w ^ 2 = dist u v ^ 2 + dist u w ^ 2 - 2 * dist u v * dist u w * Real.cos (arcV u v w)
    ) ∧
    -- 11. Kepler.Text.DIST_LAW_OF_COS_ALT._abel_1_1 (PA21:6143 (parent of compiler-generated lemma `DIST_LAW_OF_COS_ALT._abel_1_1`); no HOL anchor line in file docstring)
    (∀ (u v w : V3), v - u - (w - u) = v - w
    ) ∧
    -- 12. Kepler.Text.MCELL1_SOL_RESTRICT (PA21:5773; HOL `MCELL1_SOL_RESTRICT`)
    (∀ (V X : Set V3) (ul : List V3),
          saturated V →
            Packing V →
              barV V 3 ul → X = mcell1 V ul → ¬nullSet X → sol (elV ul 0) X = sol (elV ul 0) (X ∩ Metric.ball (elV ul 0) √2)
    ) ∧
    -- 13. Kepler.Text.MCELL2_PARAM_D_UL (PA21:5896; HOL `MCELL2_PARAM_D_UL`)
    (∀ (V : Set V3) (ul ul' vl : List V3) (X : Set V3),
          Packing V →
            saturated V →
              X = mcell2 V ul →
                barV V 3 ul →
                  ¬nullSet X →
                    initialSublist ul' ul → vl = (cellParamsD V X ul').2 → X = mcell2 V vl ∧ barV V 3 vl ∧ initialSublist ul' vl
    ) ∧
    -- 14. Kepler.Text.NULLSET_MCELL1 (PA21:4647; HOL `NULLSET_MCELL1`)
    (∀ (V : Set V3) (ul : List V3),
          Packing V → saturated V → barV V 3 ul → ¬nullSet (mcell1 V ul) → ¬nullSet (rogers V ul)
    ) ∧
    -- 15. Kepler.Text.NULL_SDIFF_TRANS (PA21:6579; HOL `NULL_SDIFF_TRANS`)
    (∀ (X Y Z : Set V3), nullSet (symmDiff X Y) → nullSet (symmDiff Y Z) → nullSet (symmDiff X Z)
    ) ∧
    -- 16. Kepler.Text.RADIAL_LE (PA21:9041; HOL `RADIAL_LE`)
    (∀ (r r' : ℝ) (x : V3) (C : Set V3),
          r' ≤ r → 0 < r' → radialNorm r x (C ∩ Metric.ball x r) → radialNorm r' x (C ∩ Metric.ball x r')
    ) ∧
    -- 17. Kepler.Text.RCONE_GE_COS (PA21:6085; HOL `RCONE_GE_COS`)
    (∀ (u v : V3) (a : ℝ), u ≠ v → rconeGe u v a = {u} ∪ {x | a ≤ Real.cos (arcV u v x)}
    ) ∧
    -- 18. Kepler.Text.RCONE_GT_SCALE (PA21:6036; HOL `RCONE_GT_SCALE`)
    (∀ (u0 u1 u : V3) (a t : ℝ), 0 < t → u0 + u ∈ rconeGt u0 u1 a → u0 + t • u ∈ rconeGt u0 u1 a
    ) ∧
    -- 19. Kepler.Text.RCONE_GT_SCALE._abel_1_1 (PA21:6036 (parent of compiler-generated lemma `RCONE_GT_SCALE._abel_1_1`); no HOL anchor line in file docstring)
    (∀ (u0 u : V3), u0 + u - u0 = u
    ) ∧
    -- 20. Kepler.Text.RCONE_GT_SCALE._abel_1_2 (PA21:6036 (parent of compiler-generated lemma `RCONE_GT_SCALE._abel_1_2`); no HOL anchor line in file docstring)
    (∀ (u0 u : V3) (t : ℝ), u0 + t • u - u0 = t • u
    ) ∧
    -- 21. Kepler.Text.REAL_DIV_NEG (PA21:6170; HOL `REAL_DIV_NEG`)
    (∀ (x y : ℝ), x / -y = -(x / y)
    ) ∧
    -- 22. Kepler.Text.SDIFF_SUBSET (PA21:6566; HOL `SDIFF_SUBSET`)
    (∀ (X Y Z : Set V3), symmDiff (X ∩ Z) (Y ∩ Z) ⊆ symmDiff X Y
    ) ∧
    -- 23. Kepler.Text.SDIFF_SYM (PA21:7338; HOL `SDIFF_SYM`)
    (∀ (X Y : Set V3), symmDiff X Y = symmDiff Y X
    ) ∧
    -- 24. Kepler.Text.SDIFF_TRANS (PA21:6573; HOL `SDIFF_TRANS`)
    (∀ (X Y Z : Set V3), symmDiff X Z ⊆ symmDiff X Y ∪ symmDiff Y Z
    ) ∧
    -- 25. Kepler.Text.compose6.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (f p1 p2 p3 p4 p5 p6 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x1 x2 x3 x4 x5 x6 : ℝ),
          compose6 f p1 p2 p3 p4 p5 p6 x1 x2 x3 x4 x5 x6 =
            f (p1 x1 x2 x3 x4 x5 x6) (p2 x1 x2 x3 x4 x5 x6) (p3 x1 x2 x3 x4 x5 x6) (p4 x1 x2 x3 x4 x5 x6) (p5 x1 x2 x3 x4 x5 x6)
              (p6 x1 x2 x3 x4 x5 x6)
    ) ∧
    -- 26. Kepler.Text.constant6.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (c _x1 _x2 _x3 _x4 _x5 _x6 : ℝ), constant6 c _x1 _x2 _x3 _x4 _x5 _x6 = c
    ) ∧
    -- 27. Kepler.Text.frustt.eq_1 (PA21:992 (parent of compiler-generated lemma `frustt.eq_1`); no HOL anchor line in file docstring)
    (∀ (u v : V3) (h a : ℝ), frustt u v h a = frustum u v h a ∩ rconeGt u v a
    ) ∧
    -- 28. Kepler.Text.frustum.eq_1 (PA21:987 (parent of compiler-generated lemma `frustum.eq_1`); no HOL anchor line in file docstring)
    (∀ (u v : V3) (h _a : ℝ),
          frustum u v h _a = {x | 0 ≤ (x - u).ofLp ⬝ᵥ (v.ofLp - u.ofLp) ∧ (x - u).ofLp ⬝ᵥ (v.ofLp - u.ofLp) ≤ h * ‖v - u‖}
    ) ∧
    -- 29. Kepler.Text.gamma2_x_div_azim_v2.eq_1 (PA21:156 (parent of compiler-generated lemma `gamma2_x_div_azim_v2.eq_1`); no HOL anchor line in file docstring)
    (∀ (m x : ℝ),
          gamma2_x_div_azim_v2 m x =
            (8 - x) * √x / 24 - (2 * (2 * mm1 / Real.pi) * (1 - √x / √8) - 8 * mm2 / Real.pi * m * lfun (√x / 2))
    ) ∧
    -- 30. Kepler.Text.gamma3fXDivSqrtdelta.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (m4 m5 m6 : ℝ),
          gamma3fXDivSqrtdelta m4 m5 m6 =
            constant6 (1 / 12) -
              (scalar6
                  (mk456 (rotate5 solEulerXDivSqrtdelta) + mk456 (rotate6 solEulerXDivSqrtdelta) +
                    mk456 (rotate4 solEulerXDivSqrtdelta))
                  (2 * mm1 / Real.pi) -
                scalar6
                  (scalar6 (uni lfun (scalar6 projY4 0.5)) m4 * mk456 (rotate4 dihXDivSqrtdeltaPosbranch) +
                      scalar6 (uni lfun (scalar6 projY5 0.5)) m5 * mk456 (rotate5 dihXDivSqrtdeltaPosbranch) +
                    scalar6 (uni lfun (scalar6 projY6 0.5)) m6 * mk456 (rotate6 dihXDivSqrtdeltaPosbranch))
                  (8 * mm2 / Real.pi))
    ) ∧
    -- 31. Kepler.Text.h0cut.eq_1 (PA21:172 (parent of compiler-generated lemma `h0cut.eq_1`); no HOL anchor line in file docstring)
    (∀ (x : ℝ), h0cut x = if x ≤ 2 * h0 then 1 else 0
    ) ∧
    -- 32. Kepler.Text.initialSublist.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (xl zl : List V3), initialSublist xl zl = ∃ yl, zl = xl ++ yl
    ) ∧
    -- 33. Kepler.Text.ldih2XDivSqrtdeltaPosbranch.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          ldih2XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 = rotate2 ldihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6
    ) ∧
    -- 34. Kepler.Text.ldih3XDivSqrtdeltaPosbranch.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          ldih3XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 = rotate3 ldihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6
    ) ∧
    -- 35. Kepler.Text.ldih5XDivSqrtdeltaPosbranch.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          ldih5XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 = rotate5 ldihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6
    ) ∧
    -- 36. Kepler.Text.ldih6XDivSqrtdeltaPosbranch.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          ldih6XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 = rotate6 ldihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6
    ) ∧
    -- 37. Kepler.Text.ldihXDivSqrtdeltaPosbranch.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          ldihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 = lfun (√x1 / 2) * dihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6
    ) ∧
    -- 38. Kepler.Text.mi_201_le_sqrt8 (PA21:1955; no HOL anchor line in file docstring)
    (2.01 ≤ √8
    ) ∧
    -- 39. Kepler.Text.mi_201_le_two_h0 (PA21:1953; no HOL anchor line in file docstring)
    (2.01 ≤ 2 * h0
    ) ∧
    -- 40. Kepler.Text.mi_delta_x4_pos (PA21:2006; HOL `delta_x4_pos`)
    (∀ (x4 x5 x6 : ℝ), 4 ≤ x4 → 4 ≤ x5 → 0 < x6 → x6 < 8 → 0 < deltaX4 x6 2 x5 2 x4 2
    ) ∧
    -- 41. Kepler.Text.mi_dih_gt_pi2 (PA21:3283; HOL `dih_gt_pi2`)
    (∀ {x1 x2 x3 x4 x5 x6 : ℝ},
          0 < x1 → 0 < deltaX x1 x2 x3 x4 x5 x6 → Real.pi / 2 < dihXf x1 x2 x3 x4 x5 x6 → deltaX4 x1 x2 x3 x4 x5 x6 < 0
    ) ∧
    -- 42. Kepler.Text.mi_eta_y_nn (PA21:1664; HOL `eta_y_nn`)
    (∀ (y4 y5 y6 : ℝ), 0 ≤ upsX (y4 * y4) (y5 * y5) (y6 * y6) → 0 ≤ eta_y y4 y5 y6
    ) ∧
    -- 43. Kepler.Text.mi_gamma3_x_gamma3f (PA21:3846; HOL `gamma3_x_gamma3f`)
    (∀ (a b c y4 y5 y6 : ℝ),
          2 * hminus ≤ y4 →
            2 ≤ y5 →
              y5 ≤ 2 * hminus →
                2 ≤ y6 → y6 ≤ 2 * hminus → gamma3f y4 y5 y6 (√2) lmfun = gamma3X (h0cut y4) a b c (y4 * y4) (y5 * y5) (y6 * y6)
    ) ∧
    -- 44. Kepler.Text.mi_gamma3fYDivSqrtdelta_arg3 (PA21:2064; HOL `gamma3f_y_div_sqrtdelta_arg3`)
    (∀ (m4 m5 m6 : ℝ → ℝ) (y1 y2 y3 y4 y5 y6 : ℝ),
          yOfX (gamma3fXDivSqrtdelta (m4 y4) (m5 y5) (m6 y6)) y1 y2 y3 y4 y5 y6 =
            yOfX (gamma3fXDivSqrtdelta (m4 y4) (m5 y5) (m6 y6)) 1 1 1 y4 y5 y6
    ) ∧
    -- 45. Kepler.Text.mi_lindihpi_gt (PA21:3363; HOL `lindihpi_gt`)
    (∀ {u x1 x2 x3 x4 x5 x6 : ℝ},
          |u| < Real.pi / 2 →
            0 < x1 →
              deltaX4 x1 x2 x3 x4 x5 x6 < 0 →
                (Real.pi - u < dihXf x1 x2 x3 x4 x5 x6 ↔
                  √(4 * x1 * deltaX x1 x2 x3 x4 x5 x6) < -Real.tan u * deltaX4 x1 x2 x3 x4 x5 x6)
    ) ∧
    -- 46. Kepler.Text.mi_lindihpi_gt_y (PA21:3501; HOL `lindihpi_gt_y`)
    (∀ {a y1 y2 y3 y4 y5 y6 : ℝ},
          0 < y1 →
            0 < a →
              0 < deltaY y1 y2 y3 y4 y5 y6 →
                delta4Y y1 y2 y3 y4 y5 y6 < 0 →
                  (Real.pi - Real.arctan a < dihY y1 y2 y3 y4 y5 y6 ↔
                    4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6 < a ^ 2 * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6)
    ) ∧
    -- 47. Kepler.Text.mi_lindihpi_lt (PA21:3320; HOL `lindihpi_lt`)
    (∀ {u x1 x2 x3 x4 x5 x6 : ℝ},
          |u| < Real.pi / 2 →
            0 < x1 →
              deltaX4 x1 x2 x3 x4 x5 x6 < 0 →
                (dihXf x1 x2 x3 x4 x5 x6 < Real.pi - u ↔
                  -Real.tan u * deltaX4 x1 x2 x3 x4 x5 x6 < √(4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
    ) ∧
    -- 48. Kepler.Text.mi_lindihpi_lt_y (PA21:3450; HOL `lindihpi_lt_y`)
    (∀ {a y1 y2 y3 y4 y5 y6 : ℝ},
          0 < y1 →
            0 < a →
              0 < deltaY y1 y2 y3 y4 y5 y6 →
                delta4Y y1 y2 y3 y4 y5 y6 < 0 →
                  (dihY y1 y2 y3 y4 y5 y6 < Real.pi - Real.arctan a ↔
                    a ^ 2 * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6 < 4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6)
    ) ∧
    -- 49. Kepler.Text.mi_two_hminus_le_sqrt8 (PA21:1943; no HOL anchor line in file docstring)
    (2 * hminus ≤ √8
    ) ∧
    -- 50. Kepler.Text.mi_two_hminus_le_two_sqrt2 (PA21:1946; no HOL anchor line in file docstring)
    (2 * hminus ≤ 2 * √2
    ) ∧
    -- 51. Kepler.Text.mi_two_hplus_le_two_sqrt2 (PA21:1949; no HOL anchor line in file docstring)
    (2 * hplus ≤ 2 * √2
    ) ∧
    -- 52. Kepler.Text.mi_two_le_two_hminus (PA21:1940; no HOL anchor line in file docstring)
    (2 ≤ 2 * hminus
    ) ∧
    -- 53. Kepler.Text.mi_y_bounds (PA21:1962; HOL `y_bounds`)
    (∀ (y : ℝ),
          (y ≤ 2 * hminus → y ≤ √8) ∧
            (y ≤ √8 → y ≤ 2 * √2) ∧
              (y ≤ 2 * √2 → y < 4) ∧
                (y < 2 * hminus → y ≤ 2 * hminus) ∧
                  (y < 2 * hminus → y ≤ 2 * √2) ∧
                    (2 ≤ y → 0 < y) ∧
                      (2 * hminus ≤ y → 2 ≤ y) ∧
                        (2 ≤ y → 0 ≤ y) ∧
                          (2 * hminus ≤ y → 0 ≤ y) ∧ (y ≤ 2 * hminus → y ≤ 2 * h0) ∧ (y ≤ 2 * hplus → y ≤ 2 * √2)
    ) ∧
    -- 54. Kepler.Text.mk456.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ), mk456 f = compose6 f two6 two6 two6 projX4 projX5 projX6
    ) ∧
    -- 55. Kepler.Text.pA_ball_subset_bis_lt (PA21:8445; no HOL anchor line in file docstring)
    (∀ (u v : V3) (r : ℝ), 2 * r ≤ dist u v → Metric.ball u r ⊆ {y | dist y u < dist y v}
    ) ∧
    -- 56. Kepler.Text.pA_coll_of_ne (PA21:8400; no HOL anchor line in file docstring)
    (∀ {a b : V3}, a = b → Collinear3 a b b
    ) ∧
    -- 57. Kepler.Text.pA_sphere_null (PA21:8455; no HOL anchor line in file docstring)
    (∀ (x : V3) (r : ℝ), volume (Metric.sphere x r) = 0
    ) ∧
    -- 58. Kepler.Text.projX4.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (_x1 _x2 _x3 x4 _x5 _x6 : ℝ), projX4 _x1 _x2 _x3 x4 _x5 _x6 = x4
    ) ∧
    -- 59. Kepler.Text.projX5.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (_x1 _x2 _x3 _x4 x5 _x6 : ℝ), projX5 _x1 _x2 _x3 _x4 x5 _x6 = x5
    ) ∧
    -- 60. Kepler.Text.projX6.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (_x1 _x2 _x3 _x4 _x5 x6 : ℝ), projX6 _x1 _x2 _x3 _x4 _x5 x6 = x6
    ) ∧
    -- 61. Kepler.Text.projY4.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (_x1 _x2 _x3 x4 _x5 _x6 : ℝ), projY4 _x1 _x2 _x3 x4 _x5 _x6 = √x4
    ) ∧
    -- 62. Kepler.Text.projY5.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (_x1 _x2 _x3 _x4 x5 _x6 : ℝ), projY5 _x1 _x2 _x3 _x4 x5 _x6 = √x5
    ) ∧
    -- 63. Kepler.Text.projY6.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (_x1 _x2 _x3 _x4 _x5 x6 : ℝ), projY6 _x1 _x2 _x3 _x4 _x5 x6 = √x6
    ) ∧
    -- 64. Kepler.Text.proj_bank_1965189142a (PA21:3547; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_1965189142a
    ) ∧
    -- 65. Kepler.Text.proj_bank_1965189142x34 (PA21:3552; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_1965189142x34
    ) ∧
    -- 66. Kepler.Text.proj_bank_6096597438a (PA21:3542; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_6096597438a
    ) ∧
    -- 67. Kepler.Text.proj_bank_6096597438b (PA21:3537; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_6096597438b
    ) ∧
    -- 68. Kepler.Text.proj_bank_BIXPCGWb (PA21:3682; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_BIXPCGWb
    ) ∧
    -- 69. Kepler.Text.proj_bank_FHBVYXZa (PA21:3627; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_FHBVYXZa
    ) ∧
    -- 70. Kepler.Text.proj_bank_FHBVYXZb (PA21:3622; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_FHBVYXZb
    ) ∧
    -- 71. Kepler.Text.proj_bank_GCKBQEA (PA21:3822; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_GCKBQEA
    ) ∧
    -- 72. Kepler.Text.proj_bank_GLFVCVK4y4crit (PA21:3712; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_GLFVCVK4y4crit
    ) ∧
    -- 73. Kepler.Text.proj_bank_GLFVCVK4y4subcrit (PA21:3702; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_GLFVCVK4y4subcrit
    ) ∧
    -- 74. Kepler.Text.proj_bank_GLFVCVK4y4supercrit (PA21:3707; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_GLFVCVK4y4supercrit
    ) ∧
    -- 75. Kepler.Text.proj_bank_IXPOTPA (PA21:3522; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_IXPOTPA
    ) ∧
    -- 76. Kepler.Text.proj_bank_MKFKQWUhalfwt (PA21:3727; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_MKFKQWUhalfwt
    ) ∧
    -- 77. Kepler.Text.proj_bank_PEMKWU (PA21:3577; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_PEMKWU
    ) ∧
    -- 78. Kepler.Text.proj_bank_QITNPEA1_1_0 (PA21:3667; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA1_1_0
    ) ∧
    -- 79. Kepler.Text.proj_bank_QITNPEA1_1_1 (PA21:3662; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA1_1_1
    ) ∧
    -- 80. Kepler.Text.proj_bank_QITNPEA1_1_2 (PA21:3657; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA1_1_2
    ) ∧
    -- 81. Kepler.Text.proj_bank_QITNPEA1_2_0 (PA21:3652; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA1_2_0
    ) ∧
    -- 82. Kepler.Text.proj_bank_QITNPEA1_2_1 (PA21:3647; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA1_2_1
    ) ∧
    -- 83. Kepler.Text.proj_bank_QITNPEA1_2_2 (PA21:3642; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA1_2_2
    ) ∧
    -- 84. Kepler.Text.proj_bank_QITNPEA3725403817 (PA21:3567; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA3725403817
    ) ∧
    -- 85. Kepler.Text.proj_bank_QITNPEA4003532128a (PA21:3562; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA4003532128a
    ) ∧
    -- 86. Kepler.Text.proj_bank_QITNPEA5400790175a (PA21:3587; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA5400790175a
    ) ∧
    -- 87. Kepler.Text.proj_bank_QITNPEA5400790175b (PA21:3582; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA5400790175b
    ) ∧
    -- 88. Kepler.Text.proj_bank_QITNPEA5814748276 (PA21:3597; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEA5814748276
    ) ∧
    -- 89. Kepler.Text.proj_bank_QITNPEAv24003532128 (PA21:3572; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_QITNPEAv24003532128
    ) ∧
    -- 90. Kepler.Text.proj_bank_RQWUDDU (PA21:3827; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_RQWUDDU
    ) ∧
    -- 91. Kepler.Text.proj_bank_TEWNSCJ (PA21:3532; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_TEWNSCJ
    ) ∧
    -- 92. Kepler.Text.proj_bank_TXQTPVC (PA21:3527; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_TXQTPVC
    ) ∧
    -- 93. Kepler.Text.proj_bank_ZTGIJCF0 (PA21:3817; no HOL anchor line in file docstring)
    (pack_nonlinear_non_ox3q1h → bank_ZTGIJCF0
    ) ∧
    -- 94. Kepler.Text.rad2X.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          rad2X x1 x2 x3 x4 x5 x6 = rhoX x1 x2 x3 x4 x5 x6 / (deltaX x1 x2 x3 x4 x5 x6 * 4)
    ) ∧
    -- 95. Kepler.Text.rhoX.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          rhoX x1 x2 x3 x4 x5 x6 =
            -x1 * x1 * x4 * x4 - x2 * x2 * x5 * x5 - x3 * x3 * x6 * x6 + 2 * x1 * x2 * x4 * x5 + 2 * x1 * x3 * x4 * x6 +
              2 * x2 * x3 * x5 * x6
    ) ∧
    -- 96. Kepler.Text.rotate2.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x1 x2 x3 x4 x5 x6 : ℝ),
          rotate2 f x1 x2 x3 x4 x5 x6 = f x2 x3 x1 x5 x6 x4
    ) ∧
    -- 97. Kepler.Text.rotate3.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x1 x2 x3 x4 x5 x6 : ℝ),
          rotate3 f x1 x2 x3 x4 x5 x6 = f x3 x1 x2 x6 x4 x5
    ) ∧
    -- 98. Kepler.Text.rotate4.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x1 x2 x3 x4 x5 x6 : ℝ),
          rotate4 f x1 x2 x3 x4 x5 x6 = f x4 x2 x6 x1 x5 x3
    ) ∧
    -- 99. Kepler.Text.rotate5.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x1 x2 x3 x4 x5 x6 : ℝ),
          rotate5 f x1 x2 x3 x4 x5 x6 = f x5 x3 x4 x2 x6 x1
    ) ∧
    -- 100. Kepler.Text.rotate6.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x1 x2 x3 x4 x5 x6 : ℝ),
          rotate6 f x1 x2 x3 x4 x5 x6 = f x6 x1 x5 x3 x4 x2
    ) ∧
    -- 101. Kepler.Text.scalar6.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (r x1 x2 x3 x4 x5 x6 : ℝ),
          scalar6 f r x1 x2 x3 x4 x5 x6 = f x1 x2 x3 x4 x5 x6 * r
    ) ∧
    -- 102. Kepler.Text.solEuler156XDivSqrtdelta.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          solEuler156XDivSqrtdelta x1 x2 x3 x4 x5 x6 = rotate6 solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6
    ) ∧
    -- 103. Kepler.Text.solEuler246XDivSqrtdelta.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          solEuler246XDivSqrtdelta x1 x2 x3 x4 x5 x6 = rotate4 solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6
    ) ∧
    -- 104. Kepler.Text.solEuler345XDivSqrtdelta.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          solEuler345XDivSqrtdelta x1 x2 x3 x4 x5 x6 = rotate5 solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6
    ) ∧
    -- 105. Kepler.Text.solX.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          solX x1 x2 x3 x4 x5 x6 = dihXf x1 x2 x3 x4 x5 x6 + dihXf x2 x3 x1 x5 x6 x4 + dihXf x3 x1 x2 x6 x4 x5 - Real.pi
    ) ∧
    -- 106. Kepler.Text.solY.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          solY y1 y2 y3 y4 y5 y6 = dihY y1 y2 y3 y4 y5 y6 + dihY y2 y3 y1 y5 y6 y4 + dihY y3 y1 y2 y6 y4 y5 - Real.pi
    ) ∧
    -- 107. Kepler.Text.two6.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (two6 = constant6 2
    ) ∧
    -- 108. Kepler.Text.uni.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (f : ℝ → ℝ) (x : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x1 x2 x3 x4 x5 x6 : ℝ),
          uni f x x1 x2 x3 x4 x5 x6 = f (x x1 x2 x3 x4 x5 x6)
    ) ∧
    -- 109. Kepler.Text.vol3f456.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (m4 : ℝ),
          vol3f456 m4 =
            scalar6 (mk456 (rotate5 solX) + mk456 (rotate6 solX) + mk456 (rotate4 solX)) (2 * mm1 / Real.pi) -
              scalar6
                (scalar6 (uni lfun (scalar6 projY4 0.5)) m4 * mk456 (rotate4 dihXf) +
                    uni lfun (scalar6 projY5 0.5) * mk456 (rotate5 dihXf) +
                  uni lfun (scalar6 projY6 0.5) * mk456 (rotate6 dihXf))
                (8 * mm2 / Real.pi)
    ) ∧
    -- 110. Kepler.Text.volXf.eq_1 (no PA21 source anchor (Lean equation lemma, declaring module per probe SEEDMOD); no HOL anchor line in file docstring)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ), volXf x1 x2 x3 x4 x5 x6 = √(deltaX x1 x2 x3 x4 x5 x6) / 12
    ) :=
    ⟨ATN2_Y_NEG, ATN_DIV, BALL_SUBSET_BIS_LE, BALL_SUBSET_BIS_LT, BIS_LE_INTER, BIS_LE_UNION,
      BIS_LT_NORM, CONV_CONVEX_HULL, DIFF_INTER, DIST_LAW_OF_COS_ALT,
      DIST_LAW_OF_COS_ALT._abel_1_1, MCELL1_SOL_RESTRICT, MCELL2_PARAM_D_UL, NULLSET_MCELL1,
      NULL_SDIFF_TRANS, RADIAL_LE, RCONE_GE_COS, RCONE_GT_SCALE, RCONE_GT_SCALE._abel_1_1,
      RCONE_GT_SCALE._abel_1_2, REAL_DIV_NEG, @SDIFF_SUBSET, SDIFF_SYM, @SDIFF_TRANS,
      compose6.eq_1, constant6.eq_1, frustt.eq_1, frustum.eq_1, gamma2_x_div_azim_v2.eq_1,
      gamma3fXDivSqrtdelta.eq_1, h0cut.eq_1, initialSublist.eq_1,
      ldih2XDivSqrtdeltaPosbranch.eq_1, ldih3XDivSqrtdeltaPosbranch.eq_1,
      ldih5XDivSqrtdeltaPosbranch.eq_1, ldih6XDivSqrtdeltaPosbranch.eq_1,
      ldihXDivSqrtdeltaPosbranch.eq_1, mi_201_le_sqrt8, mi_201_le_two_h0, mi_delta_x4_pos,
      mi_dih_gt_pi2, mi_eta_y_nn, mi_gamma3_x_gamma3f, mi_gamma3fYDivSqrtdelta_arg3,
      mi_lindihpi_gt, mi_lindihpi_gt_y, mi_lindihpi_lt, mi_lindihpi_lt_y, mi_two_hminus_le_sqrt8,
      mi_two_hminus_le_two_sqrt2, mi_two_hplus_le_two_sqrt2, mi_two_le_two_hminus, mi_y_bounds,
      mk456.eq_1, pA_ball_subset_bis_lt, pA_coll_of_ne, pA_sphere_null, projX4.eq_1, projX5.eq_1,
      projX6.eq_1, projY4.eq_1, projY5.eq_1, projY6.eq_1, proj_bank_1965189142a,
      proj_bank_1965189142x34, proj_bank_6096597438a, proj_bank_6096597438b, proj_bank_BIXPCGWb,
      proj_bank_FHBVYXZa, proj_bank_FHBVYXZb, proj_bank_GCKBQEA, proj_bank_GLFVCVK4y4crit,
      proj_bank_GLFVCVK4y4subcrit, proj_bank_GLFVCVK4y4supercrit, proj_bank_IXPOTPA,
      proj_bank_MKFKQWUhalfwt, proj_bank_PEMKWU, proj_bank_QITNPEA1_1_0, proj_bank_QITNPEA1_1_1,
      proj_bank_QITNPEA1_1_2, proj_bank_QITNPEA1_2_0, proj_bank_QITNPEA1_2_1,
      proj_bank_QITNPEA1_2_2, proj_bank_QITNPEA3725403817, proj_bank_QITNPEA4003532128a,
      proj_bank_QITNPEA5400790175a, proj_bank_QITNPEA5400790175b, proj_bank_QITNPEA5814748276,
      proj_bank_QITNPEAv24003532128, proj_bank_RQWUDDU, proj_bank_TEWNSCJ, proj_bank_TXQTPVC,
      proj_bank_ZTGIJCF0, rad2X.eq_1, rhoX.eq_1, rotate2.eq_1, rotate3.eq_1, rotate4.eq_1,
      rotate5.eq_1, rotate6.eq_1, scalar6.eq_1, solEuler156XDivSqrtdelta.eq_1,
      solEuler246XDivSqrtdelta.eq_1, solEuler345XDivSqrtdelta.eq_1, solX.eq_1, solY.eq_1,
      two6.eq_1, uni.eq_1, vol3f456.eq_1, volXf.eq_1⟩

-- Self-check.  Ground truth = `#print axioms`, not prose: expect exactly
-- the standard three [propext, Classical.choice, Quot.sound] and NO sorryAx
-- (the scout group closure is sorried-0).
#print axioms pa21_capstone_w1

/-! ### PA18 materialization capstone (lane lv1314-w1, 2026-11-04, after the leftover-mat-scout-2 workorder LV14):
the 80 public top-level PackingAuto18 clean theorem exits (scout seeds_clean.txt PA18 group: 94 exits of which 80 clean; the 14 sorried
WEDGE/AZIM/arc-length kit stubs `AFFINE_DEPENDENT_EXPLICIT_4`, `AZIM_SPLIT_POINT`, `CLOSED_WEDGE`, `CLOSED_WEDGE_EQ_PI`, `CLOSED_WEDGE_LT_PI`, `IN_CONV0_IMP_AZIM_PI_ALT`, `MCELL_EDGE_FIRST`, `PERMUTE_BARV3`, `WEDGE_GE_ALMOST_DISJOINT`, `YSSKQOY`, `arc_derivative`, `arc_derivative2`, `arc_length1_increasing`, `arc_length2_increasing` are NOT included -- their debt is the file-local leaf/arc geometry kit self-debt (YSSKQOY arc family PackingAuto18:1593-1622) per the scout verdict table), of which 80 are statable from PackingConcl and are
re-exposed as ONE conjunction below; 0 exits are dropped per the no-forcing rule (each drop named in the theorem docstring).
Self-contained section: pure insertion, zero new imports (PA18 already visible transitively: PackingConcl:121 imports PackingAuto19, PackingAuto19:134 imports PackingAuto18), zero proof obligations
(body = the exit assembly itself), own `#print axioms` probe (the lv910 PA4/PA15 sections and the lv8 pa21 / lv1112 pa25 sections are untouched -- hunk-level disjoint).
The scoped heartbeat raise mirrors the lv910 PA4 section in this file: a conjunction statement of this size exceeds
the default 200000 budget during statement elaboration (lv910 measured; pa21 capstone uses 50000000).
-/

open ComplexConjugate in
set_option maxHeartbeats 50000000 in

/-- PA18 materialization capstone (scout lane leftover-mat-scout-2
workorder LV14, implementation lane lv1314-w1, 2026-11-04).  The
80 public top-level Kepler.Text.PackingAuto18 theorem exits unreachable from every
e2e root (scout probe1/probe2: GROUP_VS_CONE fresh sorried-0, standard-three
axiom face on the axprobe sample); 80 of them are statable from
PackingConcl and are re-exposed as ONE conjunction.
Implemented here: 80 of the 80.
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its Kepler.Text.PackingAuto18 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the first depth-0 `:=` by the generator gen_items.py,
bracket-balance guarded); compiler-generated equation/aux lemmas have no
source statement anywhere, so their conjunct is the `#check @name` printer
dump verbatim and each passes a per-item sigtest (the `⟨...⟩` assembly below
must unify it definitionally with the constant's type; printer dumps with
proof-term elision `...` are dropped per the lv12-w1 t_eqlemma_microtest
evidence, each drop named above).  Semantic identity of every conjunct is
re-verified by that assembly (each element must have exactly its conjunct's
type); the per-conjunct comments carry each exit's Kepler.Text.PackingAuto18 declaration
line and file-local docstring HOL anchor.  Conjunct order: the scout
seed-list order (probe1 SEED list).  Body = the assembly of the exit
constants -- zero new proof obligations, zero new imports.  The scoped
`open ... in` prefix before the heartbeat raise (if any) reproduces the
source file's own open context for the verbatim conjunct texts --
mechanically computed as the source-file open tokens missing from the
host's; scoped to this one theorem, zero effect elsewhere in the host.
-/
theorem pa18_wire_capstone_w1 :
    -- 1. Kepler.Text.AFF_GE_MONO_TRANS_pa18 (Kepler.Text.PackingAuto18:3267; HOL `AFF_GE_MONO_TRANS_pa18`)
    (∀ {X Y S : Set V3} (h : S ⊆ X),
    affGe (X \ S) (Y ∪ S) ⊆ affGe X Y
    ) ∧
    -- 2. Kepler.Text.AFF_GT_0_2 (Kepler.Text.PackingAuto18:7729; HOL `AFF_GT_0_2`, HOL `affsign`)
    (∀ (v w : V3),
    conv0 {v, w} = {y | ∃ t2 t3 : ℝ, 0 < t2 ∧ 0 < t3 ∧ t2 + t3 = 1 ∧
          y = t2 • v + t3 • w}
    ) ∧
    -- 3. Kepler.Text.AFF_GT_SUBSET_AFFINE_HULL (Kepler.Text.PackingAuto18:10767; HOL `AFF_GT_SUBSET_AFFINE_HULL`)
    (∀ (s t : Set V3),
    affGt s t ⊆ (affineSpan ℝ (s ∪ t) : Set V3)
    ) ∧
    -- 4. Kepler.Text.ARG_0_DIV (Kepler.Text.PackingAuto18:1277; HOL `ARG_0_DIV`)
    (∀ (u v : ℂ),
    u / v = 0 ↔ u = 0 ∨ v = 0
    ) ∧
    -- 5. Kepler.Text.ARG_CNJ (Kepler.Text.PackingAuto18:1288; HOL `ARG_CNJ`)
    (∀ (z w : ℂ) (hw : w ≠ 0),
    Complex.arg (z / w) = Complex.arg (z * conj w)
    ) ∧
    -- 6. Kepler.Text.CARD_UNION_EQ (Kepler.Text.PackingAuto18:1349; HOL `CARD_UNION_EQ`)
    (∀ {α : Type*} {s t u : Set α} (hu : u.Finite)
          (hst : s ∩ t = ∅) (huni : s ∪ t = u),
    Nat.card s + Nat.card t = Nat.card u
    ) ∧
    -- 7. Kepler.Text.CHI_MSB_IMP_COPLANAR (Kepler.Text.PackingAuto18:2917; HOL `CHI_MSB_IMP_COPLANAR`)
    (∀ (ul : List V3) (p : V3) (h : chiMsb ul p = 0),
    Coplanar ({ul.getD 0 0, ul.getD 1 0, ul.getD 2 0, p} : Set V3)
    ) ∧
    -- 8. Kepler.Text.CONDS_IN_CONV2_pa18 (Kepler.Text.PackingAuto18:4018; HOL `CONDS_IN_CONV2_pa18`)
    (∀ {v w : V3} {t2 t3 : ℝ} (h2 : 0 ≤ t2) (h3 : 0 ≤ t3)
          (hne : ¬(t2 = 0 ∧ t3 = 0)),
    (t2 / (t2 + t3)) • v + (t3 / (t2 + t3)) • w ∈ convexHull ℝ ({v, w} : Set V3)
    ) ∧
    -- 9. Kepler.Text.COS_ARG_VECTOR_ANGLE (Kepler.Text.PackingAuto18:1312; HOL `COS_ARG_VECTOR_ANGLE`)
    (∀ (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0),
    Real.cos (Complex.arg (u / v)) =
          Real.cos (Real.arccos (complexDot u v / (‖u‖ * ‖v‖)))
    ) ∧
    -- 10. Kepler.Text.DIST_EQ_HALF_PLANE (Kepler.Text.PackingAuto18:2502; HOL `DIST_EQ_HALF_PLANE`)
    (∀ (x a b : V3),
    dist x a = dist x b ↔ (a - b) ⬝ᵥ (2 • x - (a + b)) = 0
    ) ∧
    -- 11. Kepler.Text.DIST_LE_HALF_PLANE (Kepler.Text.PackingAuto18:2494; HOL `DIST_LE_HALF_PLANE`)
    (∀ (x a b : V3),
    dist x a ≤ dist x b ↔ 0 ≤ (a - b) ⬝ᵥ (2 • x - (a + b))
    ) ∧
    -- 12. Kepler.Text.DOT_COMPLEX (Kepler.Text.PackingAuto18:1267; HOL `DOT_COMPLEX`)
    (∀ (x y x' y' : ℝ),
    complexDot (x + y * Complex.I) (x' + y' * Complex.I) = x * x' + y * y'
    ) ∧
    -- 13. Kepler.Text.DOT_RE (Kepler.Text.PackingAuto18:1272; HOL `DOT_RE`)
    (∀ (z1 z2 : ℂ),
    complexDot z1 z2 = (z1 * conj z2).re
    ) ∧
    -- 14. Kepler.Text.FINITE_CARD1_IMP_SINGLETON_pa18 (Kepler.Text.PackingAuto18:6129; HOL `FINITE_CARD1_IMP_SINGLETON_pa18`)
    (∀ {α : Type*} {S : Set α}
          (h : Nat.card S = 1),
    ∃ x, S = {x}
    ) ∧
    -- 15. Kepler.Text.FUZBZGI_0 (Kepler.Text.PackingAuto18:2545; HOL `FUZBZGI_0`)
    (∀ {V : Set V3} {ul : List V3} {p1 p2 : V3} {t1 t2 : ℝ}
          (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
          (hv : voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3)) (hne : p1 ≠ p2)
          (hc : circumcenter (setOfList ul) = t1 • p1 + t2 • p2) (hts : t1 + t2 = 1)
          (hfac : ∀ f, FacetOf f (voronoiList V ul) → f = {p1} ∨ f = {p2}),
    0 < t2
    ) ∧
    -- 16. Kepler.Text.FUZBZGI_1 (Kepler.Text.PackingAuto18:2679; HOL `FUZBZGI_1`)
    (∀ {V : Set V3} {ul : List V3} (hp : Packing V)
          (hs : saturated V) (hl' : leaf V ul),
    ∃ p1 p2 : V3, ∃ t1 t2 : ℝ, voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3) ∧
          p1 ≠ p2 ∧ circumcenter (setOfList ul) = t1 • p1 + t2 • p2 ∧ t1 + t2 = 1 ∧
          0 < t1 ∧ 0 < t2
    ) ∧
    -- 17. Kepler.Text.FUZBZGI_1._abel_1_1 (Kepler.Text.PackingAuto18:2679; compiler-generated equation/aux lemma (parent def `FUZBZGI_1` at Kepler.Text.PackingAuto18:2679; no source statement; sigtest = assembly elaboration))
    (∀ (p1 p2 : V3) (r : ℝ), (1 - r) • p1 + r • p2 = r • p2 + (1 - r) • p1
    ) ∧
    -- 18. Kepler.Text.INJ_IFF_SURJ (Kepler.Text.PackingAuto18:1403; HOL `INJ_IFF_SURJ`)
    (∀ {α β : Type*} {a : Set α} {b : Set β} {f : α → β}
          (ha : a.Finite) (hb : b.Finite) (hcard : Nat.card a = Nat.card b)
          (hmem : ∀ x ∈ a, f x ∈ b),
    Set.InjOn f a ↔ ∀ y ∈ b, ∃ x, x ∈ a ∧ f x = y
    ) ∧
    -- 19. Kepler.Text.INJ_SURJ (Kepler.Text.PackingAuto18:1363; HOL `INJ_SURJ`, HOL `INJ f a b`)
    (∀ {α β : Type*} {a : Set α} {b : Set β} {f : α → β}
          (ha : a.Finite) (hb : b.Finite) (hcard : Nat.card a = Nat.card b)
          (hi : Set.InjOn f a) (hmem : ∀ x ∈ a, f x ∈ b),
    ∀ y ∈ b, ∃ x, x ∈ a ∧ f x = y
    ) ∧
    -- 20. Kepler.Text.JDHAWAY_0 (Kepler.Text.PackingAuto18:2937; HOL `JDHAWAY_0`)
    (∀ {V : Set V3} {ul : List V3} {p1 p2 : V3} {t1 t2 : ℝ}
          (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
          (hv : voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3)) (hne : p1 ≠ p2)
          (hc : circumcenter (setOfList ul) = t1 • p1 + t2 • p2) (hts : t1 + t2 = 1)
          (hpos : 0 < t1 ∧ 0 < t2),
    chiMsb ul p1 ≠ 0
    ) ∧
    -- 21. Kepler.Text.JDWAWAY (Kepler.Text.PackingAuto18:2988; HOL `JDWAWAY`)
    (∀ {V : Set V3} {ul : List V3} {p1 p2 : V3} {t1 t2 : ℝ}
          (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
          (hv : voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3)) (hne : p1 ≠ p2)
          (hc : circumcenter (setOfList ul) = t1 • p1 + t2 • p2) (hts : t1 + t2 = 1)
          (hpos : 0 < t1 ∧ 0 < t2),
    chiMsb ul p1 ≠ 0 ∧ chiMsb ul p2 ≠ 0 ∧ (chiMsb ul p1 < 0 ↔ 0 < chiMsb ul p2)
    ) ∧
    -- 22. Kepler.Text.JDWAWAY._abel_1_1 (Kepler.Text.PackingAuto18:2988; compiler-generated equation/aux lemma (parent def `JDWAWAY` at Kepler.Text.PackingAuto18:2988; no source statement; sigtest = assembly elaboration))
    (∀ {p1 p2 : V3} {t1 t2 : ℝ}, t1 • p1 + t2 • p2 = t2 • p2 + t1 • p1
    ) ∧
    -- 23. Kepler.Text.MCELL2_SUBSET_AFF_GE (Kepler.Text.PackingAuto18:4008; HOL `MCELL2_SUBSET_AFF_GE`)
    (∀ (V : Set V3) (ul : List V3),
    mcell2 V ul ⊆ affGe {hdV ul, hdV ul.tail} {mxi V ul, omegaListN V ul 3}
    ) ∧
    -- 24. Kepler.Text.MIDPOINT_IN_CONV0 (Kepler.Text.PackingAuto18:7794; HOL `MIDPOINT_IN_CONV0`)
    (∀ (p q : V3),
    ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) ∈ conv0 {p, q}
    ) ∧
    -- 25. Kepler.Text.PERMUTES_a_PERMUTES_b (Kepler.Text.PackingAuto18:2228; HOL `PERMUTES_a_PERMUTES_b`, HOL `0..a`)
    (∀ {p : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b)
          (h : Permutes p ((Finset.range (a + 1) : Finset ℕ))),
    Permutes p ((Finset.range (b + 1) : Finset ℕ))
    ) ∧
    -- 26. Kepler.Text.RE_CEXP_CX (Kepler.Text.PackingAuto18:1283; HOL `RE_CEXP_CX`)
    (∀ (x : ℝ),
    (Complex.exp (Complex.I * x)).re = Real.cos x
    ) ∧
    -- 27. Kepler.Text.RE_EQVL_IMP_SYM (Kepler.Text.PackingAuto18:1739; HOL `RE_EQVL_IMP_SYM`)
    (∀ {a b : ℝ} (h : reEqvl a b),
    reEqvl b a
    ) ∧
    -- 28. Kepler.Text.RE_EQVL_REFL (Kepler.Text.PackingAuto18:1770; HOL `RE_EQVL_REFL`)
    (∀ (a : ℝ),
    reEqvl a a
    ) ∧
    -- 29. Kepler.Text.RE_EQVL_SCALE1 (Kepler.Text.PackingAuto18:1748; HOL `RE_EQVL_SCALE1`)
    (∀ (a b t : ℝ) (ht : 0 < t),
    reEqvl (t * a) b ↔ reEqvl a b
    ) ∧
    -- 30. Kepler.Text.RE_EQVL_SCALE2 (Kepler.Text.PackingAuto18:1759; HOL `RE_EQVL_SCALE2`)
    (∀ (a b t : ℝ) (ht : 0 < t),
    reEqvl a (t * b) ↔ reEqvl a b
    ) ∧
    -- 31. Kepler.Text.RE_EQVL_SYM (Kepler.Text.PackingAuto18:1744; HOL `RE_EQVL_SYM`)
    (∀ (a b : ℝ),
    reEqvl a b ↔ reEqvl b a
    ) ∧
    -- 32. Kepler.Text.RE_NORM_1 (Kepler.Text.PackingAuto18:1302; HOL `RE_NORM_1`)
    (∀ (z : ℂ) (h : ‖z‖ = 1),
    z.re = Real.cos (Complex.arg z)
    ) ∧
    -- 33. Kepler.Text.SEC_DOT (Kepler.Text.PackingAuto18:1448; HOL `SEC_DOT`)
    (∀ (u v : V3) (r ψ : ℝ) (hr : 0 < r) (hψ1 : 0 ≤ ψ)
          (hψ2 : ψ < Real.pi / 2) (hv : ‖v‖ = r / Real.cos ψ) (hu : ‖u‖ = r)
          (hcos : Real.cos (vectorAngle u v) = Real.cos ψ),
    u ⬝ᵥ (v - u) = 0
    ) ∧
    -- 34. Kepler.Text.SET2_INSERT1 (Kepler.Text.PackingAuto18:6140; HOL `SET2_INSERT1`)
    (∀ {a b x y z : V3} (hsub : ({a, b} : Set V3) ⊆ {x, y, z})
          (hne : a ≠ b),
    ∃ c : V3, ({a, b, c} : Set V3) = {x, y, z}
    ) ∧
    -- 35. Kepler.Text.TRI_UPS_X_STRICT_POS (Kepler.Text.PackingAuto18:1430; HOL `TRI_UPS_X_STRICT_POS`)
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
          (h1 : c < a + b) (h2 : a < b + c) (h3 : b < c + a),
    0 < upsX (a * a) (b * b) (c * c)
    ) ∧
    -- 36. Kepler.Text.WEDGE_GE_NULL (Kepler.Text.PackingAuto18:2058; HOL `WEDGE_GE_NULL`)
    (∀ (u0 u1 v1 v2 : V3) (h1 : ¬Collinear3 u0 u1 v1)
          (h2 : ¬Collinear3 u0 u1 v2) (haz : azim u0 u1 v1 v2 = 0),
    wedgeGe u0 u1 v1 v2 = affGe {u0, u1} {v1}
    ) ∧
    -- 37. Kepler.Text.WEDGE_GE_SPLIT (Kepler.Text.PackingAuto18:7661; HOL `WEDGE_GE_SPLIT`)
    (∀ (u0 u1 u2 u3 w : V3)
          (h2 : ¬Collinear3 u0 u1 u2) (h3 : ¬Collinear3 u0 u1 u3)
          (hw : w ∈ wedge u0 u1 u2 u3),
    ¬Collinear3 u0 u1 w ∧
          wedgeGe u0 u1 u2 u3 = wedgeGe u0 u1 u2 w ∪ wedgeGe u0 u1 w u3
    ) ∧
    -- 38. Kepler.Text.YBZFUPO (Kepler.Text.PackingAuto18:2188; HOL `YBZFUPO`)
    (∀ {V : Set V3} {ul : List V3} (hp : Packing V) (hs : saturated V)
          (hl' : leaf V ul),
    ∃ p1 p2 : V3, voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3) ∧ p1 ≠ p2 ∧
          ∀ f, FacetOf f (voronoiList V ul) → f = {p1} ∨ f = {p2}
    ) ∧
    -- 39. Kepler.Text.affDim_p7.eq_1 (Kepler.Text.PackingAuto18:0; compiler-generated equation/aux lemma (parent def `affDim_p7` at Text.PolyAuto7:111; no source statement; sigtest = assembly elaboration))
    (∀ (s : Set V3), affDim_p7 s = if s = ∅ then -1 else ↑(Module.finrank ℝ ↥(vectorSpan ℝ s))
    ) ∧
    -- 40. Kepler.Text.affine_invert (Kepler.Text.PackingAuto18:3415; HOL `affine_invert`)
    (∀ {u : ℝ} {p q : V3} {s : Set V3} (hu : u ≠ 0)
          (haff : affineSpan ℝ s = s)
          (hm : (1 - u) • p + u • q ∈ s) (hp : p ∈ s),
    q ∈ s
    ) ∧
    -- 41. Kepler.Text.affine_invert._abel_1_1 (Kepler.Text.PackingAuto18:3415; compiler-generated equation/aux lemma (parent def `affine_invert` at Kepler.Text.PackingAuto18:3415; no source statement; sigtest = assembly elaboration))
    (∀ {u : ℝ} {p q : V3}, q - p = u⁻¹ • p - p + q - u⁻¹ • p
    ) ∧
    -- 42. Kepler.Text.arcLength.eq_1 (Kepler.Text.PackingAuto18:1118; compiler-generated equation/aux lemma (parent def `arcLength` at Kepler.Text.PackingAuto18:1118; no source statement; sigtest = assembly elaboration))
    (∀ (a b c : ℝ),
          arcLength a b c = Real.pi / 2 + atn2 (√(upsX (a * a) (b * b) (c * c))) (c * c - a * a - b * b)
    ) ∧
    -- 43. Kepler.Text.arc_sym (Kepler.Text.PackingAuto18:1502; HOL `Arc_properties.arc_sym`)
    (∀ (a b c : ℝ),
    arcLength a b c = arcLength b a c
    ) ∧
    -- 44. Kepler.Text.arclength2 (Kepler.Text.PackingAuto18:1510; HOL `arclength2`)
    (∀ {h : ℝ} (h1 : 1 ≤ h) (h2 : h ≤ h0),
    arcLength 2 (2 * h) 2 = Real.arccos (h / 2)
    ) ∧
    -- 45. Kepler.Text.ccA0.eq_1 (Kepler.Text.PackingAuto18:1102; compiler-generated equation/aux lemma (parent def `ccA0` at Kepler.Text.PackingAuto18:1102; no source statement; sigtest = assembly elaboration))
    (∀ (ul : List V3), ccA0 ul = affGt {ul[0]!, ul[1]!} {ul[2]!}
    ) ∧
    -- 46. Kepler.Text.cellCluster.eq_1 (Kepler.Text.PackingAuto18:0; compiler-generated equation/aux lemma (parent def `cellCluster` at Text.PackingAuto2:510; no source statement; sigtest = assembly elaboration))
    (∀ (V e : Set V3), cellCluster V e = {X | e ∈ criticalEdgeX V X ∧ X ∈ mcellSet V}
    ) ∧
    -- 47. Kepler.Text.chiMsb.eq_1 (Kepler.Text.PackingAuto18:0; compiler-generated equation/aux lemma (parent def `chiMsb` at Text.SphereKit:64; no source statement; sigtest = assembly elaboration))
    (∀ (ul : List V3) (p : V3),
          chiMsb ul p = (crossProduct (ul[1]! - ul[0]!).ofLp) (ul[2]! - ul[0]!).ofLp ⬝ᵥ (p - ul[0]!).ofLp
    ) ∧
    -- 48. Kepler.Text.chi_msb_additive_a (Kepler.Text.PackingAuto18:2744; HOL `chi_msb_additive_a`)
    (∀ (a b c d : V3) (t1 t2 t3 t4 : ℝ) (ht : t1 + t2 + t3 + t4 = 1),
    chiMsb [t1 • a + t2 • b + t3 • c + t4 • d, b, c] d
          = t1 * chiMsb [a, b, c] d
    ) ∧
    -- 49. Kepler.Text.chi_msb_swap_12 (Kepler.Text.PackingAuto18:2735; HOL `chi_msb_swap_12`)
    (∀ (a b c d : V3),
    chiMsb [a, b, c] d = -chiMsb [a, c, b] d
    ) ∧
    -- 50. Kepler.Text.clusterGamma.eq_1 (Kepler.Text.PackingAuto18:0; compiler-generated equation/aux lemma (parent def `clusterGamma` at Text.PackingAuto2:525; no source statement; sigtest = assembly elaboration))
    (∀ (V e : Set V3) (Z : Set (Set V3)),
          clusterGamma V e Z = setSum Z fun X => gammaX V X lmfun * criticalWeight V X + betaBumpV1 V e X
    ) ∧
    -- 51. Kepler.Text.complexDot.eq_1 (Kepler.Text.PackingAuto18:1130; compiler-generated equation/aux lemma (parent def `complexDot` at Kepler.Text.PackingAuto18:1130; no source statement; sigtest = assembly elaboration))
    (∀ (z1 z2 : ℂ), complexDot z1 z2 = z1.re * z2.re + z1.im * z2.im
    ) ∧
    -- 52. Kepler.Text.conv0.eq_1 (Kepler.Text.PackingAuto18:206; compiler-generated equation/aux lemma (parent def `conv0` at Kepler.Text.PackingAuto18:206; no source statement; sigtest = assembly elaboration))
    (∀ (S : Set V3), conv0 S = affGt ∅ S
    ) ∧
    -- 53. Kepler.Text.deltaP.eq_1 (Kepler.Text.PackingAuto18:0; compiler-generated equation/aux lemma (parent def `deltaP` at Text.SphereKit:55; no source statement; sigtest = assembly elaboration))
    (∀ (x12 x13 x14 x23 x24 x34 : ℝ),
          deltaP x12 x13 x14 x23 x24 x34 =
            -(x12 * x13 * x23) - x12 * x14 * x24 - x13 * x14 * x34 - x23 * x24 * x34 +
                  x12 * x34 * (-x12 + x13 + x14 + x23 + x24 - x34) +
                x13 * x24 * (x12 - x13 + x14 + x23 - x24 + x34) +
              x14 * x23 * (x12 + x13 - x14 - x23 + x24 + x34)
    ) ∧
    -- 54. Kepler.Text.deltaX.eq_1 (Kepler.Text.PackingAuto18:0; compiler-generated equation/aux lemma (parent def `deltaX` at Text.SphereKit:46; no source statement; sigtest = assembly elaboration))
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ),
          deltaX x1 x2 x3 x4 x5 x6 =
            x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6) + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6) +
                      x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) -
                    x2 * x3 * x4 -
                  x1 * x3 * x5 -
                x1 * x2 * x6 -
              x4 * x5 * x6
    ) ∧
    -- 55. Kepler.Text.norm_normalize (Kepler.Text.PackingAuto18:1344; HOL `norm_normalize`)
    (∀ (v : V3) (h : v ≠ 0),
    ‖normalize v‖ = 1
    ) ∧
    -- 56. Kepler.Text.normalize.eq_1 (Kepler.Text.PackingAuto18:1133; compiler-generated equation/aux lemma (parent def `normalize` at Kepler.Text.PackingAuto18:1133; no source statement; sigtest = assembly elaboration))
    (∀ (v : V3), normalize v = ‖v‖⁻¹ • v
    ) ∧
    -- 57. Kepler.Text.pa18_affSpan2_collinear (Kepler.Text.PackingAuto18:10699; no HOL anchor line in file docstring)
    (∀ {u0 u1 x : V3}
          (hx : x ∈ (affineSpan ℝ ({u0, u1} : Set V3) : Set V3)),
    Collinear3 u0 u1 x
    ) ∧
    -- 58. Kepler.Text.pa18_affSpan2_subset_affGe (Kepler.Text.PackingAuto18:10776; HOL `AFFINE_HULL_SUBSET_AFF_GE`)
    (∀ {u0 u1 v : V3} (h01 : u0 ≠ u1)
          (hv : v ∉ ({u0, u1} : Set V3)),
    (affineSpan ℝ ({u0, u1} : Set V3) : Set V3)
          ⊆ affGe ({u0, u1} : Set V3) ({v} : Set V3)
    ) ∧
    -- 59. Kepler.Text.pa18_azim_ne0_ncol (Kepler.Text.PackingAuto18:10873; HOL `Local_lemmas.AZIM_DEGENERATE`)
    (∀ {u0 u1 v1 v2 : V3} (h : azim u0 u1 v1 v2 ≠ 0),
    ¬Collinear3 u0 u1 v1 ∧ ¬Collinear3 u0 u1 v2
    ) ∧
    -- 60. Kepler.Text.pa18_azim_range (Kepler.Text.PackingAuto18:10894; HOL `Local_lemmas.AZIM_RANGE`)
    (∀ (u0 u1 v1 v2 : V3),
    0 ≤ azim u0 u1 v1 v2 ∧ azim u0 u1 v1 v2 < 2 * Real.pi
    ) ∧
    -- 61. Kepler.Text.pa18_azim_sym2_ne (Kepler.Text.PackingAuto18:10883; HOL `Local_lemmas.AZIM_EQ_0_SYM2`)
    (∀ {u0 u1 v1 v2 : V3} (h : azim u0 u1 v1 v2 ≠ 0),
    azim u0 u1 v2 v1 ≠ 0
    ) ∧
    -- 62. Kepler.Text.pa18_ccCell_apex_pos (Kepler.Text.PackingAuto18:4951; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {ul : List V3} (hp : Packing V)
          (hs : saturated V) (hl' : leaf V ul),
    ∃ a : V3, a ∈ ccCell V ul ∧ 0 < chiMsb ul a
    ) ∧
    -- 63. Kepler.Text.pa18_ccCell_chi_nonneg (Kepler.Text.PackingAuto18:4973; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {u0 u1 u2 : V3} (hp : Packing V)
          (hs : saturated V) (hl' : leaf V [u0, u1, u2]),
    ∀ z ∈ ccCell V [u0, u1, u2], 0 ≤ chiMsb [u0, u1, u2] z
    ) ∧
    -- 64. Kepler.Text.pa18_ccCell_swap_ne (Kepler.Text.PackingAuto18:5023; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {u0 u1 u2 : V3} (hp : Packing V)
          (hs : saturated V) (hl : leaf V [u0, u1, u2]),
    ccCell V [u0, u1, u2] ≠ ccCell V [u1, u0, u2]
    ) ∧
    -- 65. Kepler.Text.pa18_chi_halfspace_convex (Kepler.Text.PackingAuto18:4941; no HOL anchor line in file docstring)
    (∀ (ul : List V3),
    Convex ℝ {z : V3 | 0 ≤ chiMsb ul z}
    ) ∧
    -- 66. Kepler.Text.pa18_collinear3_affSpan2 (Kepler.Text.PackingAuto18:10725; HOL `COLLINEAR_3_IN_AFFINE_HULL`)
    (∀ {u0 u1 x : V3} (h01 : u0 ≠ u1)
          (hcol : Collinear3 u0 u1 x),
    x ∈ (affineSpan ℝ ({u0, u1} : Set V3) : Set V3)
    ) ∧
    -- 67. Kepler.Text.pa18_collinear3_affSpan2._abel_1_1 (Kepler.Text.PackingAuto18:10725; compiler-generated equation/aux lemma (parent def `pa18_collinear3_affSpan2` at Kepler.Text.PackingAuto18:10725; no source statement; sigtest = assembly elaboration))
    (∀ {u0 x : V3}, x - u0 + u0 = x
    ) ∧
    -- 68. Kepler.Text.pa18_ncol3_disjoint (Kepler.Text.PackingAuto18:10687; HOL `Fan.th3a`)
    (∀ {u0 u1 v : V3} (h : ¬Collinear3 u0 u1 v),
    Disjoint ({u0, u1} : Set V3) ({v} : Set V3)
    ) ∧
    -- 69. Kepler.Text.pa18_notCollinear3_ne (Kepler.Text.PackingAuto18:10657; HOL `Collect_geom.NOT_COLLINEAR_IMP_2_UNEQUAL`)
    (∀ {a b c : V3} (h : ¬Collinear3 a b c),
    a ≠ b ∧ a ≠ c ∧ b ≠ c
    ) ∧
    -- 70. Kepler.Text.pa18_nullSet_affGe2 (Kepler.Text.PackingAuto18:10839; HOL `Conforming.NEGLIGIBLE_AFF_GE_2_1`)
    (∀ (u0 u1 v : V3),
    nullSet (affGe ({u0, u1} : Set V3) ({v} : Set V3))
    ) ∧
    -- 71. Kepler.Text.pa18_nullSet_subset (Kepler.Text.PackingAuto18:10866; HOL `NEGLIGIBLE_SUBSET`)
    (∀ {s t : Set V3} (hsub : t ⊆ s) (hs : nullSet s),
    nullSet t
    ) ∧
    -- 72. Kepler.Text.pa18_nullSet_union (Kepler.Text.PackingAuto18:10854; HOL `NULLSET_RULES`)
    (∀ {s t : Set V3} (hs : nullSet s) (ht : nullSet t),
    nullSet (s ∪ t)
    ) ∧
    -- 73. Kepler.Text.pa18c_two_rearrangement_lemma_alt (Kepler.Text.PackingAuto18:6072; HOL `TWO_REARRANGEMENT_LEMMA_ALT`)
    (∀ {V : Set V3} {ul : List V3}
          {u0 u1 u2 u3 : V3} (_hp : Packing V) (_hs : saturated V) (_hb : barV V 3 ul)
          (hul : ul = [u0, u1, u2, u3]),
    ∃ p : Equiv.Perm ℕ, permutes p (Set.Icc 0 1) ∧
          [u1, u0, u2, u3] = leftActionList p ul
    ) ∧
    -- 74. Kepler.Text.selectd.eq_1 (Kepler.Text.PackingAuto18:1125; compiler-generated equation/aux lemma (parent def `selectd` at Kepler.Text.PackingAuto18:1125; no source statement; sigtest = assembly elaboration))
    (∀ {α : Type u_1} [inst : Nonempty α] (P : α → Prop) (d : α),
          selectd P d = if ∃ r, P r then epsilon P else d
    ) ∧
    -- 75. Kepler.Text.selectd_cases (Kepler.Text.PackingAuto18:1252; HOL `selectd_cases`)
    (∀ {α : Type*} [Nonempty α] (P : α → Prop) (d : α),
    P (selectd P d) ∨ selectd P d = d
    ) ∧
    -- 76. Kepler.Text.selectd_exists (Kepler.Text.PackingAuto18:1261; HOL `selectd_exists`)
    (∀ {α : Type*} [Nonempty α] {P : α → Prop} {d : α}
          (h : ∃ r, P r),
    P (selectd P d)
    ) ∧
    -- 77. Kepler.Text.truncate_set_of_list (Kepler.Text.PackingAuto18:2390; HOL `truncate_set_of_list`)
    (∀ {vl : List V3} {k : ℕ}
          (hk : 0 < k) (hlen : vl.length = k + 1),
    setOfList vl ⊆ setOfList (truncateSimplex (k - 1) vl) ∪ {vl.getD k 0}
    ) ∧
    -- 78. Kepler.Text.upsX.eq_1 (Kepler.Text.PackingAuto18:0; compiler-generated equation/aux lemma (parent def `upsX` at Text.SphereKit:72; no source statement; sigtest = assembly elaboration))
    (∀ (x1 x2 x6 : ℝ), upsX x1 x2 x6 = -(x1 * x1) - x2 * x2 - x6 * x6 + 2 * x1 * x6 + 2 * x1 * x2 + 2 * x2 * x6
    ) ∧
    -- 79. Kepler.Text.ups_x_pos (Kepler.Text.PackingAuto18:1438; HOL `ups_x_pos`)
    (∀ (a b : ℝ) (h1 : 2 ≤ a) (h2 : a ≤ 2.52) (h3 : 2 ≤ b)
          (h4 : b ≤ 2.52),
    0 < upsX (a ^ 2) (b ^ 2) 4
    ) ∧
    -- 80. Kepler.Text.yssk_reduction (Kepler.Text.PackingAuto18:1561; HOL `yssk_reduction`)
    (∀ (hmono : ∀ a1 a2 b1 b2 : ℝ, 2 ≤ a1 → a1 ≤ a2 → a2 ≤ 2 * h0 →
            2 ≤ b1 → b1 ≤ b2 → b2 ≤ 2 * h0 →
            0 ≤ arcLength a2 b2 2 - arcLength a1 b2 2 - arcLength a2 b1 2 +
              arcLength a1 b1 2)
          {h h' : ℝ} (hh1 : 1 ≤ h) (hh2 : h ≤ h0) (hh1' : 1 ≤ h') (hh2' : h' ≤ h0),
    Real.arccos (h / 2) + Real.arccos (h' / 2) - Real.pi / 3 ≤
          arcLength (2 * h) (2 * h') 2
    ) :=
⟨@_root_.Kepler.Text.AFF_GE_MONO_TRANS_pa18, _root_.Kepler.Text.AFF_GT_0_2,
      @_root_.Kepler.Text.AFF_GT_SUBSET_AFFINE_HULL, _root_.Kepler.Text.ARG_0_DIV,
      _root_.Kepler.Text.ARG_CNJ, _root_.Kepler.Text.CARD_UNION_EQ,
      _root_.Kepler.Text.CHI_MSB_IMP_COPLANAR, _root_.Kepler.Text.CONDS_IN_CONV2_pa18,
      _root_.Kepler.Text.COS_ARG_VECTOR_ANGLE, _root_.Kepler.Text.DIST_EQ_HALF_PLANE,
      _root_.Kepler.Text.DIST_LE_HALF_PLANE, _root_.Kepler.Text.DOT_COMPLEX,
      _root_.Kepler.Text.DOT_RE, _root_.Kepler.Text.FINITE_CARD1_IMP_SINGLETON_pa18,
      _root_.Kepler.Text.FUZBZGI_0, _root_.Kepler.Text.FUZBZGI_1,
      _root_.Kepler.Text.FUZBZGI_1._abel_1_1, _root_.Kepler.Text.INJ_IFF_SURJ,
      _root_.Kepler.Text.INJ_SURJ, _root_.Kepler.Text.JDHAWAY_0, _root_.Kepler.Text.JDWAWAY,
      _root_.Kepler.Text.JDWAWAY._abel_1_1, @_root_.Kepler.Text.MCELL2_SUBSET_AFF_GE,
      _root_.Kepler.Text.MIDPOINT_IN_CONV0, _root_.Kepler.Text.PERMUTES_a_PERMUTES_b,
      _root_.Kepler.Text.RE_CEXP_CX, _root_.Kepler.Text.RE_EQVL_IMP_SYM,
      _root_.Kepler.Text.RE_EQVL_REFL, _root_.Kepler.Text.RE_EQVL_SCALE1,
      _root_.Kepler.Text.RE_EQVL_SCALE2, _root_.Kepler.Text.RE_EQVL_SYM,
      _root_.Kepler.Text.RE_NORM_1, _root_.Kepler.Text.SEC_DOT, _root_.Kepler.Text.SET2_INSERT1,
      _root_.Kepler.Text.TRI_UPS_X_STRICT_POS, _root_.Kepler.Text.WEDGE_GE_NULL,
      _root_.Kepler.Text.WEDGE_GE_SPLIT, _root_.Kepler.Text.YBZFUPO,
      _root_.Kepler.Text.affDim_p7.eq_1, _root_.Kepler.Text.affine_invert,
      _root_.Kepler.Text.affine_invert._abel_1_1, _root_.Kepler.Text.arcLength.eq_1,
      _root_.Kepler.Text.arc_sym, _root_.Kepler.Text.arclength2, _root_.Kepler.Text.ccA0.eq_1,
      _root_.Kepler.Text.cellCluster.eq_1, _root_.Kepler.Text.chiMsb.eq_1,
      _root_.Kepler.Text.chi_msb_additive_a, _root_.Kepler.Text.chi_msb_swap_12,
      _root_.Kepler.Text.clusterGamma.eq_1, _root_.Kepler.Text.complexDot.eq_1,
      _root_.Kepler.Text.conv0.eq_1, _root_.Kepler.Text.deltaP.eq_1,
      _root_.Kepler.Text.deltaX.eq_1, _root_.Kepler.Text.norm_normalize,
      _root_.Kepler.Text.normalize.eq_1, _root_.Kepler.Text.pa18_affSpan2_collinear,
      @_root_.Kepler.Text.pa18_affSpan2_subset_affGe, _root_.Kepler.Text.pa18_azim_ne0_ncol,
      _root_.Kepler.Text.pa18_azim_range, _root_.Kepler.Text.pa18_azim_sym2_ne,
      _root_.Kepler.Text.pa18_ccCell_apex_pos, _root_.Kepler.Text.pa18_ccCell_chi_nonneg,
      _root_.Kepler.Text.pa18_ccCell_swap_ne, _root_.Kepler.Text.pa18_chi_halfspace_convex,
      _root_.Kepler.Text.pa18_collinear3_affSpan2,
      _root_.Kepler.Text.pa18_collinear3_affSpan2._abel_1_1,
      _root_.Kepler.Text.pa18_ncol3_disjoint, _root_.Kepler.Text.pa18_notCollinear3_ne,
      _root_.Kepler.Text.pa18_nullSet_affGe2, _root_.Kepler.Text.pa18_nullSet_subset,
      _root_.Kepler.Text.pa18_nullSet_union,
      _root_.Kepler.Text.pa18c_two_rearrangement_lemma_alt, _root_.Kepler.Text.selectd.eq_1,
      _root_.Kepler.Text.selectd_cases, _root_.Kepler.Text.selectd_exists,
      @_root_.Kepler.Text.truncate_set_of_list, _root_.Kepler.Text.upsX.eq_1,
      _root_.Kepler.Text.ups_x_pos, _root_.Kepler.Text.yssk_reduction⟩

-- Self-check.  Ground truth = `#print axioms`, not prose: expect exactly the standard three
-- [propext, Classical.choice, Quot.sound] and NO sorryAx (the scout group closure is sorried-0).
#print axioms pa18_wire_capstone_w1

/-! ### PA15 materialization capstone (lane lv910-w1, 2026-11-04, after the leftover-mat-scout-2 workorder LV10):
the 31 public top-level PackingAuto15 theorem exits -- all clean (MCELL_ID_MXI 45/0 family; scout seeds_clean.txt PA15 group), of which 31 are statable from PackingConcl and are re-exposed as ONE conjunction below
(0 dropped per the no-forcing rule, each named in the theorem docstring).  PA15 is visible transitively via the PackingAuto16 import
(PackingAuto16:117 imports PackingAuto15; no import cycle, scout-verified).  Self-contained section: pure insertion,
zero proof obligations (body = the exit assembly itself).  -/

/-- PA15 materialization capstone (scout lane leftover-mat-scout-2
workorder LV10, implementation lane lv910-w1, 2026-11-04).  The
31 public top-level Kepler.Text.PackingAuto15 theorem exits unreachable from every
e2e root (scout probe1/probe2: GROUP_VS_CONE fresh sorried-0, standard-three
axiom face on the axprobe sample); 31 of them are statable from
PackingConcl and are re-exposed as ONE conjunction.
Implemented here: 31 of the 31.
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its Kepler.Text.PackingAuto15 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the first depth-0 `:=` by the generator gen_items.py,
bracket-balance guarded); compiler-generated equation lemmas have no source
statement anywhere, so their conjunct is the `#check @name` printer dump
verbatim and each passes a per-item sigtest (the `⟨...⟩` assembly below must
unify it definitionally with the constant's type).  Semantic identity of
every conjunct is re-verified by that assembly (each element must have
exactly its conjunct's type); the per-conjunct comments carry each exit's
Kepler.Text.PackingAuto15 declaration line and file-local docstring HOL anchor.
Conjunct order: the scout seed-list order (probe1 SEED list,
seeds_clean.txt).  Body = the assembly of the exit constants -- zero new
proof obligations, zero new imports. -/
theorem pa15_wire_capstone_w1 :
    -- 1. Kepler.Text.AFFINE_HULL_3_INSERT (Kepler.Text.PackingAuto15:2869; no HOL anchor line in file docstring)
    (∀ (a : V3) (S : Set V3) (h : a ∈ (affineSpan ℝ S : Set V3)),
    (affineSpan ℝ (insert a S) : Set V3) = (affineSpan ℝ S : Set V3)
    ) ∧
    -- 2. Kepler.Text.BETA_PAIR_THM (Kepler.Text.PackingAuto15:4715; no HOL anchor line in file docstring)
    (∀ {β : Type*} [Nonempty β] (g : V3 → V3 → β) (u' v' : V3)
          (h : ∀ u v : V3, g u v = g v u),
    patternPair g {u', v'} = g u' v'
    ) ∧
    -- 3. Kepler.Text.BETA_SET_2_THM (Kepler.Text.PackingAuto15:6247; no HOL anchor line in file docstring)
    (∀ {β : Type*} [Nonempty β] (g : Set V3 → β) (u0 v0 : V3),
    patternPair (fun u v => g {u, v}) {u0, v0} = g {u0, v0}
    ) ∧
    -- 4. Kepler.Text.BOUNDED_SING (Kepler.Text.PackingAuto15:1866; no HOL anchor line in file docstring)
    (∀ (a : V3),
    Bornology.IsBounded ({a} : Set V3)
    ) ∧
    -- 5. Kepler.Text.BOUND_GAMMA_X_lmfun (Kepler.Text.PackingAuto15:6973; no HOL anchor line in file docstring)
    (∃ c : ℝ, ∀ (V : Set V3) (X : Set V3), Packing V → saturated V → mcellSet V X →
          gammaX V X lmfun ≤ c
    ) ∧
    -- 6. Kepler.Text.CARD_BOUNDARY_INT_BALL_BOUND (Kepler.Text.PackingAuto15:787; no HOL anchor line in file docstring)
    (∀ (x : V3) (k1 k2 : ℝ),
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
          (((Nat.card ↥((intBall x (r + k1)) \ (intBall x (r - k2))) : ℕ) : ℝ)) ≤ C * r ^ 2
    ) ∧
    -- 7. Kepler.Text.CARD_BOUNDARY_INT_BALL_BOUND_1 (Kepler.Text.PackingAuto15:703; no HOL anchor line in file docstring)
    (∀ (x : V3) (k1 k2 : ℝ) (hk1 : 0 < k1) (hk2 : 0 < k2),
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
          (((Nat.card ↥((intBall x (r + k1)) \ (intBall x (r - k2))) : ℕ) : ℝ)) ≤ C * r ^ 2
    ) ∧
    -- 8. Kepler.Text.CARD_EDGEX_LE_16 (Kepler.Text.PackingAuto15:6751; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (X : Set V3) (hp : Packing V) (hs : saturated V)
          (hm : mcellSet V X),
    Nat.card (edgeX V X) ≤ 16
    ) ∧
    -- 9. Kepler.Text.CARD_LIST_klemma (Kepler.Text.PackingAuto15:6371; no HOL anchor line in file docstring)
    (∀ {α : Type*} (s : Set α) (t : Set (List α)) (hs : s.Finite)
          (ht : t.Finite),
    Nat.card {y : List α | ∃ u0 ∈ s, ∃ y1 ∈ t, y = u0 :: y1} = Nat.card s * Nat.card t
    ) ∧
    -- 10. Kepler.Text.CARD_LIST_klemma_2 (Kepler.Text.PackingAuto15:6388; no HOL anchor line in file docstring)
    (∀ {α : Type*} (s : Set α) (t : Set (List α)) (hs : s.Finite)
          (ht : t.Finite),
    Nat.card {y : List α | ∃ u0 ∈ s, ∃ y1 ∈ t, y = u0 :: y1} = Nat.card s * Nat.card t
    ) ∧
    -- 11. Kepler.Text.CONIC_CAP_AFF_GT_EQ_0 (Kepler.Text.PackingAuto15:4479; no HOL anchor line in file docstring)
    (∀ (v0 v1 : V3) (a r : ℝ) (w1 w2 : V3) (ha : a < 1) (hr : 0 < r)
          (h : volume.real (conicCap v0 v1 r a ∩ affGt {v0, v1} {w1, w2}) = 0),
    Coplanar ℝ ({v0, v1, w1, w2} : Set V3)
    ) ∧
    -- 12. Kepler.Text.CONIC_CAP_WEDGE_EQ_0 (Kepler.Text.PackingAuto15:4432; no HOL anchor line in file docstring)
    (∀ (v0 v1 : V3) (a r : ℝ) (w1 w2 : V3) (ha : a < 1) (hr : 0 < r)
          (h : volume.real (conicCap v0 v1 r a ∩ wedge v0 v1 w1 w2) = 0),
    Coplanar ℝ ({v0, v1, w1, w2} : Set V3)
    ) ∧
    -- 13. Kepler.Text.CONTINUOUS_ON_LIFT_DOT2 (Kepler.Text.PackingAuto15:3080; no HOL anchor line in file docstring)
    (∀ {X : Type*} [TopologicalSpace X] {s : Set X}
          {f g : X → V3} (hf : ContinuousOn f s) (hg : ContinuousOn g s),
    ContinuousOn (fun x : X => (fun _ : Fin 1 => f x ⬝ᵥ g x)) s
    ) ∧
    -- 14. Kepler.Text.FINITE_LIST_KY_LEMMA_2 (Kepler.Text.PackingAuto15:4630; no HOL anchor line in file docstring)
    (∀ {α : Type*} (s : Set α) (hs : s.Finite),
    {y : List α | ∃ u0 ∈ s, ∃ u1 ∈ s, y = [u0, u1]}.Finite
    ) ∧
    -- 15. Kepler.Text.LEFT_ACTION_LIST_2_EXISTS (Kepler.Text.PackingAuto15:5049; HOL `0..2`)
    (∀ {α : Type*} [Inhabited α] (u0 u1 u2 d x y z : α)
          (hcard : Nat.card ({u0, u1, u2, d} : Set α) = 4) (hset : ({x, y, z} : Set α) = {u0, u1, u2}),
    ∃ p : Equiv.Perm ℕ, permutes p (Set.Iic 2) ∧
          [x, y, z, d] = leftActionList p [u0, u1, u2, d]
    ) ∧
    -- 16. Kepler.Text.LEFT_ACTION_LIST_3_EXISTS (Kepler.Text.PackingAuto15:5083; HOL `0..3`)
    (∀ {α : Type*} [Inhabited α] (u0 u1 u2 u3 x y z t : α)
          (hcard : Nat.card ({u0, u1, u2, u3} : Set α) = 4)
          (hset : ({x, y, z, t} : Set α) = {u0, u1, u2, u3}),
    ∃ p : Equiv.Perm ℕ, permutes p (Set.Iic 3) ∧
          [x, y, z, t] = leftActionList p [u0, u1, u2, u3]
    ) ∧
    -- 17. Kepler.Text.LIFT_DIV_CONTINUOUS_ON (Kepler.Text.PackingAuto15:3099; no HOL anchor line in file docstring)
    (∀ {X : Type*} [TopologicalSpace X] {s : Set X}
          {f g : X → ℝ} (hf : ContinuousOn (fun x : X => (fun _ : Fin 1 => f x)) s)
          (hg : ContinuousOn (fun x : X => (fun _ : Fin 1 => g x)) s)
          (h0 : ∀ x ∈ s, g x ≠ 0),
    ContinuousOn (fun x : X => (fun _ : Fin 1 => f x / g x)) s
    ) ∧
    -- 18. Kepler.Text.LIFT_DOT_CONTINUOUS_ON (Kepler.Text.PackingAuto15:3110; no HOL anchor line in file docstring)
    (∀ (a b : V3) (s : Set V3),
    ContinuousOn (fun x : V3 => (fun _ : Fin 1 => (x - a) ⬝ᵥ b)) s
    ) ∧
    -- 19. Kepler.Text.LIFT_MUL_CONTINUOUS_ON (Kepler.Text.PackingAuto15:3089; no HOL anchor line in file docstring)
    (∀ {X : Type*} [TopologicalSpace X] {s : Set X}
          {f g : X → ℝ} (hf : ContinuousOn (fun x : X => (fun _ : Fin 1 => f x)) s)
          (hg : ContinuousOn (fun x : X => (fun _ : Fin 1 => g x)) s),
    ContinuousOn (fun x : X => (fun _ : Fin 1 => f x * g x)) s
    ) ∧
    -- 20. Kepler.Text.LIFT_NORM_CONTINUOUS_ON (Kepler.Text.PackingAuto15:3118; no HOL anchor line in file docstring)
    (∀ (a : V3) (s : Set V3),
    ContinuousOn (fun x : V3 => (fun _ : Fin 1 => norm (x - a))) s
    ) ∧
    -- 21. Kepler.Text.MCELL_ID_MXI (Kepler.Text.PackingAuto15:2860; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (i j : ℕ) (ul vl : List V3) (hp : Packing V)
          (hs : saturated V) (hul : barV V 3 ul) (hvl : barV V 3 vl) (hhd : hdV ul = hdV vl)
          (heq : mcell i V ul = mcell j V vl) (hnel : ¬nullSet (mcell i V ul))
          (hi : i ∈ ({2, 3} : Set ℕ)) (hj : j ∈ ({2, 3} : Set ℕ)),
    mxi V ul = mxi V vl
    ) ∧
    -- 22. Kepler.Text.MEASURABLE_BALL_AFF_GE (Kepler.Text.PackingAuto15:4624; HOL `measurable`)
    (∀ (z : V3) (r : ℝ) (s t : Set V3),
    NullMeasurableSet (Metric.ball z r ∩ affGe s t) volume
    ) ∧
    -- 23. Kepler.Text.REAL_DIV_LE_1_TACTICS (Kepler.Text.PackingAuto15:1917; no HOL anchor line in file docstring)
    (∀ (m n : ℝ) (hn : 0 < n) (h : m ≤ n),
    m / n ≤ 1
    ) ∧
    -- 24. Kepler.Text.REAL_DIV_LT_1_TACTICS (Kepler.Text.PackingAuto15:1921; no HOL anchor line in file docstring)
    (∀ (m n : ℝ) (hn : 0 < n) (h : m < n),
    m / n < 1
    ) ∧
    -- 25. Kepler.Text.SUBSPACE_BOUNDED_EQ_TRIVIAL (Kepler.Text.PackingAuto15:1873; HOL `real^N`)
    (∀ (s : Submodule ℝ V3),
    Bornology.IsBounded (s : Set V3) ↔ (s : Set V3) = {0}
    ) ∧
    -- 26. Kepler.Text.WELLDEFINED_FUNCTION_2 (Kepler.Text.PackingAuto15:4681; no HOL anchor line in file docstring)
    (∀ {A B C D : Type*} [Nonempty D] (s : A → B → C)
          (t : A → B → D),
    (∃ f : C → D, ∀ x y, f (s x y) = t x y) ↔
          ∀ x x' y y', s x y = s x' y' → t x y = t x' y'
    ) ∧
    -- 27. Kepler.Text.gamma_y_lmfun_bound2 (Kepler.Text.PackingAuto15:6757; no HOL anchor line in file docstring)
    (∃ d : ℝ, ∀ (V : Set V3) (X : Set V3) (e : Set V3), Packing V → saturated V →
          mcellSet V X → edgeX V X e → gammaY V X lmfun e ≤ d
    ) ∧
    -- 28. Kepler.Text.gamma_y_pos_le (Kepler.Text.PackingAuto15:6362; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (X : Set V3) (e : Set V3) (hp : Packing V)
          (hs : saturated V) (hm : mcellSet V X) (he : edgeX V X e),
    0 ≤ gammaY V X lmfun e
    ) ∧
    -- 29. Kepler.Text.p15w1_intBall_finite (Kepler.Text.PackingAuto15:487; no HOL anchor line in file docstring)
    (∀ (c : V3) (r : ℝ),
    (intBall c r).Finite
    ) ∧
    -- 30. Kepler.Text.pre_beta (Kepler.Text.PackingAuto15:4663; HOL `\{u,v}. g u v`)
    (∀ {β : Type*} [Nonempty β] (g : V3 → V3 → β) (u' v' : V3)
          (h : ∃ f : Set V3 → β, ∀ u v : V3, f {u, v} = g u v),
    patternPair g {u', v'} = g u' v'
    ) ∧
    -- 31. Kepler.Text.well_defined_unordered_pair (Kepler.Text.PackingAuto15:4698; no HOL anchor line in file docstring)
    (∀ {β : Type*} [Nonempty β] (g : V3 → V3 → β),
    (∃ f : Set V3 → β, ∀ u v : V3, f {u, v} = g u v) ↔ ∀ u v : V3, g u v = g v u
    ) :=
    ⟨AFFINE_HULL_3_INSERT, BETA_PAIR_THM, BETA_SET_2_THM, BOUNDED_SING, BOUND_GAMMA_X_lmfun,
      CARD_BOUNDARY_INT_BALL_BOUND, CARD_BOUNDARY_INT_BALL_BOUND_1, CARD_EDGEX_LE_16,
      CARD_LIST_klemma, CARD_LIST_klemma_2, CONIC_CAP_AFF_GT_EQ_0, CONIC_CAP_WEDGE_EQ_0,
      CONTINUOUS_ON_LIFT_DOT2, FINITE_LIST_KY_LEMMA_2, LEFT_ACTION_LIST_2_EXISTS,
      LEFT_ACTION_LIST_3_EXISTS, LIFT_DIV_CONTINUOUS_ON, LIFT_DOT_CONTINUOUS_ON,
      LIFT_MUL_CONTINUOUS_ON, LIFT_NORM_CONTINUOUS_ON, MCELL_ID_MXI, MEASURABLE_BALL_AFF_GE,
      REAL_DIV_LE_1_TACTICS, REAL_DIV_LT_1_TACTICS, SUBSPACE_BOUNDED_EQ_TRIVIAL,
      WELLDEFINED_FUNCTION_2, gamma_y_lmfun_bound2, gamma_y_pos_le, p15w1_intBall_finite,
      pre_beta, well_defined_unordered_pair⟩

-- Self-check.  Ground truth = `#print axioms`, not prose: expect exactly the standard three
-- [propext, Classical.choice, Quot.sound] and NO sorryAx (the scout group closure is sorried-0).
#print axioms pa15_wire_capstone_w1

end Kepler.Text
