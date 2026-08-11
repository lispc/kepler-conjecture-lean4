/-
Quad seed (p = 1) enumeration certificate wiring.
Evaluation-side file: `native_decide` allowed (DECISIONS.md 2026-08-10);
every assembly proof is a pure kernel proof.  Mirrors CertTri.lean.
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.QuadTop
import Kepler.Graphs.Worklist
import Kepler.Graphs.CertShards.Quad.K003
import Kepler.Graphs.CertShards.Quad.K004
import Kepler.Graphs.CertShards.Quad.K006
import Kepler.Graphs.CertShards.Quad.K007
import Kepler.Graphs.CertShards.Quad.K008
import Kepler.Graphs.CertShards.Quad.K009
import Kepler.Graphs.CertShards.Quad.K010
import Kepler.Graphs.CertShards.Quad.K011
import Kepler.Graphs.CertShards.Quad.K012
import Kepler.Graphs.CertShards.Quad.K013
import Kepler.Graphs.CertShards.Quad.K014
import Kepler.Graphs.CertShards.Quad.K015
import Kepler.Graphs.CertShards.QuadR.K000
import Kepler.Graphs.CertShards.QuadR.K001
import Kepler.Graphs.CertShards.QuadR.K002
import Kepler.Graphs.CertShards.QuadR.K003
import Kepler.Graphs.CertShards.QuadR.K004
import Kepler.Graphs.CertShards.QuadR.K005
import Kepler.Graphs.CertShards.QuadR.K006
import Kepler.Graphs.CertShards.QuadR.K007
import Kepler.Graphs.CertShards.QuadR.K008
import Kepler.Graphs.CertShards.QuadR.K009
import Kepler.Graphs.CertShards.QuadR.K010
import Kepler.Graphs.CertShards.QuadR.K011
import Kepler.Graphs.CertShards.QuadR.K012
import Kepler.Graphs.CertShards.QuadR.K013
import Kepler.Graphs.CertShards.QuadR.K014
import Kepler.Graphs.CertShards.QuadR.K015
import Kepler.Graphs.CertShards.QuadR.K016
import Kepler.Graphs.CertShards.QuadR.K017
import Kepler.Graphs.CertShards.QuadR.K018
import Kepler.Graphs.CertShards.QuadR.K019
import Kepler.Graphs.CertShards.QuadR.K020
import Kepler.Graphs.CertShards.QuadR.K021
import Kepler.Graphs.CertShards.QuadR.K022
import Kepler.Graphs.CertShards.QuadR.K023
import Kepler.Graphs.CertShards.QuadR.K024
import Kepler.Graphs.CertShards.QuadR.K025
import Kepler.Graphs.CertShards.QuadR.K026
import Kepler.Graphs.CertShards.QuadR.K027
import Kepler.Graphs.CertShards.QuadR.K028
import Kepler.Graphs.CertShards.QuadR.K029
import Kepler.Graphs.CertShards.QuadR.K030
import Kepler.Graphs.CertShards.QuadR.K031
import Kepler.Graphs.CertShards.QuadR.K032
import Kepler.Graphs.CertShards.QuadR.K033
import Kepler.Graphs.CertShards.QuadR.K034
import Kepler.Graphs.CertShards.QuadR.K035
import Kepler.Graphs.CertShards.QuadR.K036
import Kepler.Graphs.CertShards.QuadR.K037
import Kepler.Graphs.CertShards.QuadR.K038
import Kepler.Graphs.CertShards.QuadR.K039
import Kepler.Graphs.CertShards.QuadR.K040
import Kepler.Graphs.CertShards.QuadR.K041
import Kepler.Graphs.CertShards.QuadR.K042
import Kepler.Graphs.CertShards.QuadR.K043
import Kepler.Graphs.CertShards.QuadR.K044
import Kepler.Graphs.CertShards.QuadR.K045
import Kepler.Graphs.CertShards.QuadR.K046
import Kepler.Graphs.CertShards.QuadR.K047
import Kepler.Graphs.CertShards.QuadR.K048
import Kepler.Graphs.CertShards.QuadR.K049
import Kepler.Graphs.CertShards.QuadR.K050
import Kepler.Graphs.CertShards.QuadR.K051
import Kepler.Graphs.CertShards.QuadR.K052
import Kepler.Graphs.CertShards.QuadR.K053
import Kepler.Graphs.CertShards.QuadR.K054
import Kepler.Graphs.CertShards.QuadR.K055
import Kepler.Graphs.CertShards.QuadR.K056
import Kepler.Graphs.CertShards.QuadR.K057
import Kepler.Graphs.CertShards.QuadR.K058
import Kepler.Graphs.CertShards.QuadR.K059
import Kepler.Graphs.CertShards.QuadR.K060
import Kepler.Graphs.CertShards.QuadR.K061
import Kepler.Graphs.CertShards.QuadR.K062
import Kepler.Graphs.CertShards.QuadR.K063
import Kepler.Graphs.CertShards.QuadR.K064
import Kepler.Graphs.CertShards.QuadR.K065
import Kepler.Graphs.CertShards.QuadR.K066
import Kepler.Graphs.CertShards.QuadR.K067
import Kepler.Graphs.CertShards.QuadR.K068
import Kepler.Graphs.CertShards.QuadR.K069
import Kepler.Graphs.CertShards.QuadR.K070
import Kepler.Graphs.CertShards.QuadR.K071
import Kepler.Graphs.CertShards.QuadR.K072
import Kepler.Graphs.CertShards.QuadR.K073
import Kepler.Graphs.CertShards.QuadR.K074
import Kepler.Graphs.CertShards.QuadR.K075
import Kepler.Graphs.CertShards.QuadR.K076
import Kepler.Graphs.CertShards.QuadR.K077
import Kepler.Graphs.CertShards.QuadR.K078
import Kepler.Graphs.CertShards.QuadR.K079

namespace Kepler.Graphs

/-- Replay: every top node's `next_tame 1` children are exactly its tagged
children table entries. -/
theorem quad_top_replay : (List.range QuadTop.length).all (fun i =>
    decide (next_tame 1 QuadTop[i]! =
      (QuadTopChildren[i]!).map (resolveChild QuadTop QuadFrontier))) = true := by
  native_decide

/-- Bounds: every tagged child index is in range of its target list. -/
theorem quad_top_bounds : (List.range QuadTopChildren.length).all (fun i =>
    (QuadTopChildren[i]!).all (fun t =>
      (t.1 && decide (t.2 < QuadFrontier.length)) ||
        (!t.1 && decide (t.2 < QuadTop.length)))) = true := by
  native_decide

/-- `QuadTop` is closed under `next_tame 1` up to `QuadFrontier`. -/
theorem quad_top_closed : ∀ x ∈ QuadTop, ∀ c ∈ next_tame 1 x,
    c ∈ QuadTop ∨ c ∈ QuadFrontier :=
  closed_of_replay rfl quad_top_replay quad_top_bounds

/-- No final graphs in the Quad top. -/
theorem quad_top_no_finals : (QuadTop.all (fun g => !g.final)) = true := by
  native_decide

theorem quad_top_final_archive :
    ∀ g ∈ QuadTop, g.final = true → inIso g.fgraph Archive :=
  top_final_archive_of_no_finals quad_top_no_finals

/-- Every `QuadData` entry satisfies `pre_iso_test`. -/
theorem quad_archive_pre : (QuadData.all (fun a => preIsoTestB a)) = true := by
  native_decide

theorem quad_archive_pre_iso : ∀ a ∈ QuadData, pre_iso_test a := fun a ha =>
  preIsoTestB_correct ((List.all_eq_true.mp quad_archive_pre) a ha)

/-- The seed-1 (`Quad`) case of the enumeration-completeness certificate. -/
theorem same_1 : ∀ g, TameEnumP 1 g → inIso g.fgraph Archive := by
  intro g htep
  obtain ⟨hr, hfin⟩ := htep
  have h0 : QuadTop[0]'(by decide) = Seed 1 := by decide
  have hseed : Seed 1 ∈ QuadTop := h0 ▸ List.getElem_mem _
  rcases frontier_cut QuadTop QuadFrontier hseed quad_top_closed hr
    with hS | ⟨h, hF, hrh⟩
  · exact quad_top_final_archive g hS hfin
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hF
    have hlenN : QuadFrontier.length = 1583 := rfl
    rw [hlenN] at hj
    have hloopE : ∃ fuel, loop (next_tame 1) (checkFinal (buildBuckets QuadData))
        fuel [QuadFrontier[j]!] = some true :=
      if h0 : j < 5 then
        quadr_shardE_0 j
          (List.mem_range'_1.mpr ⟨Nat.zero_le j, h0⟩)
      else if h1 : j < 10 then
        quadr_shardE_5 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h0, h1⟩)
      else if h2 : j < 15 then
        quadr_shardE_10 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h1, h2⟩)
      else if h3 : j < 20 then
        quadr_shardE_15 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h2, h3⟩)
      else if h4 : j < 25 then
        quadr_shardE_20 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h3, h4⟩)
      else if h5 : j < 30 then
        quadr_shardE_25 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h4, h5⟩)
      else if h6 : j < 35 then
        quadr_shardE_30 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h5, h6⟩)
      else if h7 : j < 40 then
        quadr_shardE_35 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h6, h7⟩)
      else if h8 : j < 45 then
        quadr_shardE_40 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h7, h8⟩)
      else if h9 : j < 50 then
        quadr_shardE_45 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h8, h9⟩)
      else if h10 : j < 55 then
        quadr_shardE_50 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h9, h10⟩)
      else if h11 : j < 60 then
        quadr_shardE_55 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h10, h11⟩)
      else if h12 : j < 65 then
        quadr_shardE_60 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h11, h12⟩)
      else if h13 : j < 70 then
        quadr_shardE_65 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h12, h13⟩)
      else if h14 : j < 75 then
        quadr_shardE_70 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h13, h14⟩)
      else if h15 : j < 80 then
        quadr_shardE_75 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h14, h15⟩)
      else if h16 : j < 85 then
        quadr_shardE_80 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h15, h16⟩)
      else if h17 : j < 90 then
        quadr_shardE_85 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h16, h17⟩)
      else if h18 : j < 95 then
        quadr_shardE_90 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h17, h18⟩)
      else if h19 : j < 100 then
        quadr_shardE_95 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h18, h19⟩)
      else if h20 : j < 105 then
        quadr_shardE_100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h19, h20⟩)
      else if h21 : j < 110 then
        quadr_shardE_105 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h20, h21⟩)
      else if h22 : j < 115 then
        quadr_shardE_110 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h21, h22⟩)
      else if h23 : j < 120 then
        quadr_shardE_115 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h22, h23⟩)
      else if h24 : j < 125 then
        quadr_shardE_120 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h23, h24⟩)
      else if h25 : j < 130 then
        quadr_shardE_125 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h24, h25⟩)
      else if h26 : j < 135 then
        quadr_shardE_130 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h25, h26⟩)
      else if h27 : j < 140 then
        quadr_shardE_135 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h26, h27⟩)
      else if h28 : j < 145 then
        quadr_shardE_140 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h27, h28⟩)
      else if h29 : j < 150 then
        quadr_shardE_145 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h28, h29⟩)
      else if h30 : j < 155 then
        quadr_shardE_150 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h29, h30⟩)
      else if h31 : j < 160 then
        quadr_shardE_155 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h30, h31⟩)
      else if h32 : j < 165 then
        quadr_shardE_160 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h31, h32⟩)
      else if h33 : j < 170 then
        quadr_shardE_165 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h32, h33⟩)
      else if h34 : j < 175 then
        quadr_shardE_170 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h33, h34⟩)
      else if h35 : j < 180 then
        quadr_shardE_175 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h34, h35⟩)
      else if h36 : j < 185 then
        quadr_shardE_180 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h35, h36⟩)
      else if h37 : j < 190 then
        quadr_shardE_185 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h36, h37⟩)
      else if h38 : j < 195 then
        quadr_shardE_190 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h37, h38⟩)
      else if h39 : j < 200 then
        quadr_shardE_195 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h38, h39⟩)
      else if h40 : j < 205 then
        quadr_shardE_200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h39, h40⟩)
      else if h41 : j < 210 then
        quadr_shardE_205 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h40, h41⟩)
      else if h42 : j < 215 then
        quadr_shardE_210 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h41, h42⟩)
      else if h43 : j < 220 then
        quadr_shardE_215 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h42, h43⟩)
      else if h44 : j < 225 then
        quadr_shardE_220 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h43, h44⟩)
      else if h45 : j < 230 then
        quadr_shardE_225 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h44, h45⟩)
      else if h46 : j < 235 then
        quadr_shardE_230 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h45, h46⟩)
      else if h47 : j < 240 then
        quadr_shardE_235 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h46, h47⟩)
      else if h48 : j < 245 then
        quadr_shardE_240 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h47, h48⟩)
      else if h49 : j < 250 then
        quadr_shardE_245 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h48, h49⟩)
      else if h50 : j < 255 then
        quadr_shardE_250 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h49, h50⟩)
      else if h51 : j < 260 then
        quadr_shardE_255 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h50, h51⟩)
      else if h52 : j < 265 then
        quadr_shardE_260 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h51, h52⟩)
      else if h53 : j < 270 then
        quadr_shardE_265 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h52, h53⟩)
      else if h54 : j < 275 then
        quadr_shardE_270 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h53, h54⟩)
      else if h55 : j < 280 then
        quadr_shardE_275 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h54, h55⟩)
      else if h56 : j < 285 then
        quadr_shardE_280 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h55, h56⟩)
      else if h57 : j < 290 then
        quadr_shardE_285 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h56, h57⟩)
      else if h58 : j < 295 then
        quadr_shardE_290 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h57, h58⟩)
      else if h59 : j < 300 then
        quadr_shardE_295 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h58, h59⟩)
      else if h60 : j < 400 then
        quad_shardE_300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h59, h60⟩)
      else if h61 : j < 500 then
        quad_shardE_400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h60, h61⟩)
      else if h62 : j < 505 then
        quadr_shardE_500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h61, h62⟩)
      else if h63 : j < 510 then
        quadr_shardE_505 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h62, h63⟩)
      else if h64 : j < 515 then
        quadr_shardE_510 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h63, h64⟩)
      else if h65 : j < 520 then
        quadr_shardE_515 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h64, h65⟩)
      else if h66 : j < 525 then
        quadr_shardE_520 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h65, h66⟩)
      else if h67 : j < 530 then
        quadr_shardE_525 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h66, h67⟩)
      else if h68 : j < 535 then
        quadr_shardE_530 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h67, h68⟩)
      else if h69 : j < 540 then
        quadr_shardE_535 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h68, h69⟩)
      else if h70 : j < 545 then
        quadr_shardE_540 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h69, h70⟩)
      else if h71 : j < 550 then
        quadr_shardE_545 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h70, h71⟩)
      else if h72 : j < 555 then
        quadr_shardE_550 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h71, h72⟩)
      else if h73 : j < 560 then
        quadr_shardE_555 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h72, h73⟩)
      else if h74 : j < 565 then
        quadr_shardE_560 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h73, h74⟩)
      else if h75 : j < 570 then
        quadr_shardE_565 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h74, h75⟩)
      else if h76 : j < 575 then
        quadr_shardE_570 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h75, h76⟩)
      else if h77 : j < 580 then
        quadr_shardE_575 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h76, h77⟩)
      else if h78 : j < 585 then
        quadr_shardE_580 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h77, h78⟩)
      else if h79 : j < 590 then
        quadr_shardE_585 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h78, h79⟩)
      else if h80 : j < 595 then
        quadr_shardE_590 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h79, h80⟩)
      else if h81 : j < 600 then
        quadr_shardE_595 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h80, h81⟩)
      else if h82 : j < 700 then
        quad_shardE_600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h81, h82⟩)
      else if h83 : j < 800 then
        quad_shardE_700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h82, h83⟩)
      else if h84 : j < 900 then
        quad_shardE_800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h83, h84⟩)
      else if h85 : j < 1000 then
        quad_shardE_900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h84, h85⟩)
      else if h86 : j < 1100 then
        quad_shardE_1000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h85, h86⟩)
      else if h87 : j < 1200 then
        quad_shardE_1100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h86, h87⟩)
      else if h88 : j < 1300 then
        quad_shardE_1200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h87, h88⟩)
      else if h89 : j < 1400 then
        quad_shardE_1300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h88, h89⟩)
      else if h90 : j < 1500 then
        quad_shardE_1400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h89, h90⟩)
      else if h91 : j < 1583 then
        quad_shardE_1500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h90, h91⟩)
      else
        absurd hj h91
    obtain ⟨fuel, hloop⟩ := hloopE
    rw [getElem!_pos QuadFrontier j hj] at hloop
    have hcheck := loop_some_true hloop g
      ⟨QuadFrontier[j]'hj, List.mem_singleton_self _, hrh⟩
    obtain ⟨a, ha, hiso⟩ := checkFinal_correct quad_archive_pre_iso hcheck hfin
    refine ⟨a, ?_, hiso⟩
    show a ∈ TriData ++ QuadData ++ PentData ++ HexData
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha))

end Kepler.Graphs
