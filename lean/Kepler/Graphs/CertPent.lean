/-
Pent seed (p = 2) enumeration certificate wiring.
Evaluation-side file: `native_decide` allowed (DECISIONS.md 2026-08-10);
every assembly proof is a pure kernel proof.  Mirrors CertTri.lean.
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.PentTop
import Kepler.Graphs.Worklist
import Kepler.Graphs.CertShards.Pent.K003
import Kepler.Graphs.CertShards.Pent.K004
import Kepler.Graphs.CertShards.Pent.K005
import Kepler.Graphs.CertShards.Pent.K006
import Kepler.Graphs.CertShards.Pent.K007
import Kepler.Graphs.CertShards.Pent.K008
import Kepler.Graphs.CertShards.Pent.K009
import Kepler.Graphs.CertShards.Pent.K010
import Kepler.Graphs.CertShards.Pent.K011
import Kepler.Graphs.CertShards.Pent.K012
import Kepler.Graphs.CertShards.Pent.K013
import Kepler.Graphs.CertShards.Pent.K014
import Kepler.Graphs.CertShards.Pent.K015
import Kepler.Graphs.CertShards.Pent.K016
import Kepler.Graphs.CertShards.Pent.K017
import Kepler.Graphs.CertShards.Pent.K018
import Kepler.Graphs.CertShards.Pent.K019
import Kepler.Graphs.CertShards.Pent.K020
import Kepler.Graphs.CertShards.Pent.K021
import Kepler.Graphs.CertShards.Pent.K022
import Kepler.Graphs.CertShards.Pent.K023
import Kepler.Graphs.CertShards.Pent.K024
import Kepler.Graphs.CertShards.Pent.K025
import Kepler.Graphs.CertShards.Pent.K026
import Kepler.Graphs.CertShards.Pent.K027
import Kepler.Graphs.CertShards.Pent.K028
import Kepler.Graphs.CertShards.Pent.K029
import Kepler.Graphs.CertShards.Pent.K030
import Kepler.Graphs.CertShards.Pent.K031
import Kepler.Graphs.CertShards.Pent.K032
import Kepler.Graphs.CertShards.Pent.K033
import Kepler.Graphs.CertShards.Pent.K034
import Kepler.Graphs.CertShards.Pent.K035
import Kepler.Graphs.CertShards.Pent.K036
import Kepler.Graphs.CertShards.Pent.K038
import Kepler.Graphs.CertShards.Pent.K039
import Kepler.Graphs.CertShards.Pent.K040
import Kepler.Graphs.CertShards.Pent.K041
import Kepler.Graphs.CertShards.Pent.K042
import Kepler.Graphs.CertShards.Pent.K043
import Kepler.Graphs.CertShards.Pent.K044
import Kepler.Graphs.CertShards.Pent.K045
import Kepler.Graphs.CertShards.Pent.K046
import Kepler.Graphs.CertShards.Pent.K047
import Kepler.Graphs.CertShards.Pent.K048
import Kepler.Graphs.CertShards.Pent.K049
import Kepler.Graphs.CertShards.Pent.K050
import Kepler.Graphs.CertShards.Pent.K051
import Kepler.Graphs.CertShards.Pent.K052
import Kepler.Graphs.CertShards.Pent.K053
import Kepler.Graphs.CertShards.Pent.K054
import Kepler.Graphs.CertShards.Pent.K055
import Kepler.Graphs.CertShards.Pent.K056
import Kepler.Graphs.CertShards.Pent.K057
import Kepler.Graphs.CertShards.Pent.K058
import Kepler.Graphs.CertShards.Pent.K059
import Kepler.Graphs.CertShards.Pent.K060
import Kepler.Graphs.CertShards.Pent.K061
import Kepler.Graphs.CertShards.Pent.K062
import Kepler.Graphs.CertShards.Pent.K063
import Kepler.Graphs.CertShards.Pent.K064
import Kepler.Graphs.CertShards.Pent.K065
import Kepler.Graphs.CertShards.Pent.K066
import Kepler.Graphs.CertShards.Pent.K067
import Kepler.Graphs.CertShards.Pent.K068
import Kepler.Graphs.CertShards.Pent.K069
import Kepler.Graphs.CertShards.Pent.K070
import Kepler.Graphs.CertShards.Pent.K071
import Kepler.Graphs.CertShards.Pent.K072
import Kepler.Graphs.CertShards.Pent.K073
import Kepler.Graphs.CertShards.Pent.K074
import Kepler.Graphs.CertShards.Pent.K075
import Kepler.Graphs.CertShards.Pent.K076
import Kepler.Graphs.CertShards.Pent.K077
import Kepler.Graphs.CertShards.Pent.K078
import Kepler.Graphs.CertShards.Pent.K079
import Kepler.Graphs.CertShards.Pent.K080
import Kepler.Graphs.CertShards.Pent.K081
import Kepler.Graphs.CertShards.Pent.K082
import Kepler.Graphs.CertShards.Pent.K083
import Kepler.Graphs.CertShards.Pent.K084
import Kepler.Graphs.CertShards.Pent.K085
import Kepler.Graphs.CertShards.Pent.K086
import Kepler.Graphs.CertShards.Pent.K087
import Kepler.Graphs.CertShards.Pent.K088
import Kepler.Graphs.CertShards.Pent.K089
import Kepler.Graphs.CertShards.Pent.K090
import Kepler.Graphs.CertShards.Pent.K091
import Kepler.Graphs.CertShards.Pent.K092
import Kepler.Graphs.CertShards.Pent.K093
import Kepler.Graphs.CertShards.Pent.K094
import Kepler.Graphs.CertShards.Pent.K095
import Kepler.Graphs.CertShards.Pent.K096
import Kepler.Graphs.CertShards.Pent.K097
import Kepler.Graphs.CertShards.Pent.K098
import Kepler.Graphs.CertShards.Pent.K099
import Kepler.Graphs.CertShards.Pent.K100
import Kepler.Graphs.CertShards.Pent.K101
import Kepler.Graphs.CertShards.Pent.K102
import Kepler.Graphs.CertShards.Pent.K103
import Kepler.Graphs.CertShards.Pent.K104
import Kepler.Graphs.CertShards.Pent.K105
import Kepler.Graphs.CertShards.Pent.K106
import Kepler.Graphs.CertShards.Pent.K107
import Kepler.Graphs.CertShards.Pent.K108
import Kepler.Graphs.CertShards.Pent.K109
import Kepler.Graphs.CertShards.Pent.K110
import Kepler.Graphs.CertShards.Pent.K111
import Kepler.Graphs.CertShards.Pent.K112
import Kepler.Graphs.CertShards.Pent.K113
import Kepler.Graphs.CertShards.Pent.K114
import Kepler.Graphs.CertShards.Pent.K115
import Kepler.Graphs.CertShards.Pent.K116
import Kepler.Graphs.CertShards.Pent.K117
import Kepler.Graphs.CertShards.Pent.K118
import Kepler.Graphs.CertShards.Pent.K119
import Kepler.Graphs.CertShards.Pent.K120
import Kepler.Graphs.CertShards.Pent.K121
import Kepler.Graphs.CertShards.Pent.K122
import Kepler.Graphs.CertShards.Pent.K123
import Kepler.Graphs.CertShards.Pent.K124
import Kepler.Graphs.CertShards.Pent.K125
import Kepler.Graphs.CertShards.Pent.K126
import Kepler.Graphs.CertShards.Pent.K127
import Kepler.Graphs.CertShards.Pent.K128
import Kepler.Graphs.CertShards.Pent.K129
import Kepler.Graphs.CertShards.Pent.K130
import Kepler.Graphs.CertShards.Pent.K131
import Kepler.Graphs.CertShards.Pent.K132
import Kepler.Graphs.CertShards.Pent.K133
import Kepler.Graphs.CertShards.Pent.K134
import Kepler.Graphs.CertShards.Pent.K135
import Kepler.Graphs.CertShards.Pent.K136
import Kepler.Graphs.CertShards.Pent.K137
import Kepler.Graphs.CertShards.Pent.K138
import Kepler.Graphs.CertShards.Pent.K139
import Kepler.Graphs.CertShards.Pent.K140
import Kepler.Graphs.CertShards.Pent.K141
import Kepler.Graphs.CertShards.Pent.K142
import Kepler.Graphs.CertShards.Pent.K143
import Kepler.Graphs.CertShards.Pent.K144
import Kepler.Graphs.CertShards.Pent.K145
import Kepler.Graphs.CertShards.PentR.K000
import Kepler.Graphs.CertShards.PentR.K001
import Kepler.Graphs.CertShards.PentR.K002
import Kepler.Graphs.CertShards.PentR.K003
import Kepler.Graphs.CertShards.PentR.K004
import Kepler.Graphs.CertShards.PentR.K005
import Kepler.Graphs.CertShards.PentR.K006
import Kepler.Graphs.CertShards.PentR.K007
import Kepler.Graphs.CertShards.PentR.K008
import Kepler.Graphs.CertShards.PentR.K009
import Kepler.Graphs.CertShards.PentR.K010
import Kepler.Graphs.CertShards.PentR.K011
import Kepler.Graphs.CertShards.PentR.K012
import Kepler.Graphs.CertShards.PentR.K013
import Kepler.Graphs.CertShards.PentR.K014
import Kepler.Graphs.CertShards.PentR.K015
import Kepler.Graphs.CertShards.PentR.K016
import Kepler.Graphs.CertShards.PentR.K017
import Kepler.Graphs.CertShards.PentR.K018
import Kepler.Graphs.CertShards.PentR.K019

namespace Kepler.Graphs

/-- Replay: every top node's `next_tame 2` children are exactly its tagged
children table entries. -/
theorem pent_top_replay : (List.range PentTop.length).all (fun i =>
    decide (next_tame 2 PentTop[i]! =
      (PentTopChildren[i]!).map (resolveChild PentTop PentFrontier))) = true := by
  native_decide

/-- Bounds: every tagged child index is in range of its target list. -/
theorem pent_top_bounds : (List.range PentTopChildren.length).all (fun i =>
    (PentTopChildren[i]!).all (fun t =>
      (t.1 && decide (t.2 < PentFrontier.length)) ||
        (!t.1 && decide (t.2 < PentTop.length)))) = true := by
  native_decide

/-- `PentTop` is closed under `next_tame 2` up to `PentFrontier`. -/
theorem pent_top_closed : ∀ x ∈ PentTop, ∀ c ∈ next_tame 2 x,
    c ∈ PentTop ∨ c ∈ PentFrontier :=
  closed_of_replay rfl pent_top_replay pent_top_bounds

/-- No final graphs in the Pent top. -/
theorem pent_top_no_finals : (PentTop.all (fun g => !g.final)) = true := by
  native_decide

theorem pent_top_final_archive :
    ∀ g ∈ PentTop, g.final = true → inIso g.fgraph Archive :=
  top_final_archive_of_no_finals pent_top_no_finals

/-- Every `PentData` entry satisfies `pre_iso_test`. -/
theorem pent_archive_pre : (PentData.all (fun a => preIsoTestB a)) = true := by
  native_decide

theorem pent_archive_pre_iso : ∀ a ∈ PentData, pre_iso_test a := fun a ha =>
  preIsoTestB_correct ((List.all_eq_true.mp pent_archive_pre) a ha)

/-- The seed-2 (`Pent`) case of the enumeration-completeness certificate. -/
theorem same_2 : ∀ g, TameEnumP 2 g → inIso g.fgraph Archive := by
  intro g htep
  obtain ⟨hr, hfin⟩ := htep
  have h0 : PentTop[0]'(by decide) = Seed 2 := by decide
  have hseed : Seed 2 ∈ PentTop := h0 ▸ List.getElem_mem _
  rcases frontier_cut PentTop PentFrontier hseed pent_top_closed hr
    with hS | ⟨h, hF, hrh⟩
  · exact pent_top_final_archive g hS hfin
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hF
    have hlenN : PentFrontier.length = 7263 := rfl
    rw [hlenN] at hj
    have hloopE : ∃ fuel, loop (next_tame 2) (checkFinal (buildBuckets PentData))
        fuel [PentFrontier[j]!] = some true :=
      if h0 : j < 10 then
        pentr_shardE_0 j
          (List.mem_range'_1.mpr ⟨Nat.zero_le j, h0⟩)
      else if h1 : j < 20 then
        pentr_shardE_10 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h0, h1⟩)
      else if h2 : j < 30 then
        pentr_shardE_20 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h1, h2⟩)
      else if h3 : j < 40 then
        pentr_shardE_30 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h2, h3⟩)
      else if h4 : j < 50 then
        pentr_shardE_40 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h3, h4⟩)
      else if h5 : j < 60 then
        pentr_shardE_50 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h4, h5⟩)
      else if h6 : j < 70 then
        pentr_shardE_60 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h5, h6⟩)
      else if h7 : j < 80 then
        pentr_shardE_70 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h6, h7⟩)
      else if h8 : j < 90 then
        pentr_shardE_80 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h7, h8⟩)
      else if h9 : j < 100 then
        pentr_shardE_90 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h8, h9⟩)
      else if h10 : j < 110 then
        pentr_shardE_100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h9, h10⟩)
      else if h11 : j < 120 then
        pentr_shardE_110 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h10, h11⟩)
      else if h12 : j < 130 then
        pentr_shardE_120 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h11, h12⟩)
      else if h13 : j < 140 then
        pentr_shardE_130 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h12, h13⟩)
      else if h14 : j < 150 then
        pentr_shardE_140 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h13, h14⟩)
      else if h15 : j < 200 then
        pent_shardE_150 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h14, h15⟩)
      else if h16 : j < 250 then
        pent_shardE_200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h15, h16⟩)
      else if h17 : j < 300 then
        pent_shardE_250 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h16, h17⟩)
      else if h18 : j < 350 then
        pent_shardE_300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h17, h18⟩)
      else if h19 : j < 400 then
        pent_shardE_350 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h18, h19⟩)
      else if h20 : j < 450 then
        pent_shardE_400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h19, h20⟩)
      else if h21 : j < 500 then
        pent_shardE_450 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h20, h21⟩)
      else if h22 : j < 550 then
        pent_shardE_500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h21, h22⟩)
      else if h23 : j < 600 then
        pent_shardE_550 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h22, h23⟩)
      else if h24 : j < 650 then
        pent_shardE_600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h23, h24⟩)
      else if h25 : j < 700 then
        pent_shardE_650 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h24, h25⟩)
      else if h26 : j < 750 then
        pent_shardE_700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h25, h26⟩)
      else if h27 : j < 800 then
        pent_shardE_750 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h26, h27⟩)
      else if h28 : j < 850 then
        pent_shardE_800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h27, h28⟩)
      else if h29 : j < 900 then
        pent_shardE_850 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h28, h29⟩)
      else if h30 : j < 950 then
        pent_shardE_900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h29, h30⟩)
      else if h31 : j < 1000 then
        pent_shardE_950 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h30, h31⟩)
      else if h32 : j < 1050 then
        pent_shardE_1000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h31, h32⟩)
      else if h33 : j < 1100 then
        pent_shardE_1050 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h32, h33⟩)
      else if h34 : j < 1150 then
        pent_shardE_1100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h33, h34⟩)
      else if h35 : j < 1200 then
        pent_shardE_1150 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h34, h35⟩)
      else if h36 : j < 1250 then
        pent_shardE_1200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h35, h36⟩)
      else if h37 : j < 1300 then
        pent_shardE_1250 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h36, h37⟩)
      else if h38 : j < 1350 then
        pent_shardE_1300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h37, h38⟩)
      else if h39 : j < 1400 then
        pent_shardE_1350 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h38, h39⟩)
      else if h40 : j < 1450 then
        pent_shardE_1400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h39, h40⟩)
      else if h41 : j < 1500 then
        pent_shardE_1450 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h40, h41⟩)
      else if h42 : j < 1550 then
        pent_shardE_1500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h41, h42⟩)
      else if h43 : j < 1600 then
        pent_shardE_1550 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h42, h43⟩)
      else if h44 : j < 1650 then
        pent_shardE_1600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h43, h44⟩)
      else if h45 : j < 1700 then
        pent_shardE_1650 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h44, h45⟩)
      else if h46 : j < 1750 then
        pent_shardE_1700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h45, h46⟩)
      else if h47 : j < 1800 then
        pent_shardE_1750 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h46, h47⟩)
      else if h48 : j < 1850 then
        pent_shardE_1800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h47, h48⟩)
      else if h49 : j < 1860 then
        pentr_shardE_1850 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h48, h49⟩)
      else if h50 : j < 1870 then
        pentr_shardE_1860 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h49, h50⟩)
      else if h51 : j < 1880 then
        pentr_shardE_1870 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h50, h51⟩)
      else if h52 : j < 1890 then
        pentr_shardE_1880 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h51, h52⟩)
      else if h53 : j < 1900 then
        pentr_shardE_1890 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h52, h53⟩)
      else if h54 : j < 1950 then
        pent_shardE_1900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h53, h54⟩)
      else if h55 : j < 2000 then
        pent_shardE_1950 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h54, h55⟩)
      else if h56 : j < 2050 then
        pent_shardE_2000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h55, h56⟩)
      else if h57 : j < 2100 then
        pent_shardE_2050 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h56, h57⟩)
      else if h58 : j < 2150 then
        pent_shardE_2100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h57, h58⟩)
      else if h59 : j < 2200 then
        pent_shardE_2150 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h58, h59⟩)
      else if h60 : j < 2250 then
        pent_shardE_2200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h59, h60⟩)
      else if h61 : j < 2300 then
        pent_shardE_2250 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h60, h61⟩)
      else if h62 : j < 2350 then
        pent_shardE_2300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h61, h62⟩)
      else if h63 : j < 2400 then
        pent_shardE_2350 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h62, h63⟩)
      else if h64 : j < 2450 then
        pent_shardE_2400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h63, h64⟩)
      else if h65 : j < 2500 then
        pent_shardE_2450 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h64, h65⟩)
      else if h66 : j < 2550 then
        pent_shardE_2500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h65, h66⟩)
      else if h67 : j < 2600 then
        pent_shardE_2550 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h66, h67⟩)
      else if h68 : j < 2650 then
        pent_shardE_2600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h67, h68⟩)
      else if h69 : j < 2700 then
        pent_shardE_2650 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h68, h69⟩)
      else if h70 : j < 2750 then
        pent_shardE_2700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h69, h70⟩)
      else if h71 : j < 2800 then
        pent_shardE_2750 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h70, h71⟩)
      else if h72 : j < 2850 then
        pent_shardE_2800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h71, h72⟩)
      else if h73 : j < 2900 then
        pent_shardE_2850 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h72, h73⟩)
      else if h74 : j < 2950 then
        pent_shardE_2900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h73, h74⟩)
      else if h75 : j < 3000 then
        pent_shardE_2950 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h74, h75⟩)
      else if h76 : j < 3050 then
        pent_shardE_3000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h75, h76⟩)
      else if h77 : j < 3100 then
        pent_shardE_3050 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h76, h77⟩)
      else if h78 : j < 3150 then
        pent_shardE_3100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h77, h78⟩)
      else if h79 : j < 3200 then
        pent_shardE_3150 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h78, h79⟩)
      else if h80 : j < 3250 then
        pent_shardE_3200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h79, h80⟩)
      else if h81 : j < 3300 then
        pent_shardE_3250 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h80, h81⟩)
      else if h82 : j < 3350 then
        pent_shardE_3300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h81, h82⟩)
      else if h83 : j < 3400 then
        pent_shardE_3350 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h82, h83⟩)
      else if h84 : j < 3450 then
        pent_shardE_3400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h83, h84⟩)
      else if h85 : j < 3500 then
        pent_shardE_3450 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h84, h85⟩)
      else if h86 : j < 3550 then
        pent_shardE_3500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h85, h86⟩)
      else if h87 : j < 3600 then
        pent_shardE_3550 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h86, h87⟩)
      else if h88 : j < 3650 then
        pent_shardE_3600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h87, h88⟩)
      else if h89 : j < 3700 then
        pent_shardE_3650 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h88, h89⟩)
      else if h90 : j < 3750 then
        pent_shardE_3700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h89, h90⟩)
      else if h91 : j < 3800 then
        pent_shardE_3750 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h90, h91⟩)
      else if h92 : j < 3850 then
        pent_shardE_3800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h91, h92⟩)
      else if h93 : j < 3900 then
        pent_shardE_3850 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h92, h93⟩)
      else if h94 : j < 3950 then
        pent_shardE_3900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h93, h94⟩)
      else if h95 : j < 4000 then
        pent_shardE_3950 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h94, h95⟩)
      else if h96 : j < 4050 then
        pent_shardE_4000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h95, h96⟩)
      else if h97 : j < 4100 then
        pent_shardE_4050 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h96, h97⟩)
      else if h98 : j < 4150 then
        pent_shardE_4100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h97, h98⟩)
      else if h99 : j < 4200 then
        pent_shardE_4150 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h98, h99⟩)
      else if h100 : j < 4250 then
        pent_shardE_4200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h99, h100⟩)
      else if h101 : j < 4300 then
        pent_shardE_4250 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h100, h101⟩)
      else if h102 : j < 4350 then
        pent_shardE_4300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h101, h102⟩)
      else if h103 : j < 4400 then
        pent_shardE_4350 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h102, h103⟩)
      else if h104 : j < 4450 then
        pent_shardE_4400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h103, h104⟩)
      else if h105 : j < 4500 then
        pent_shardE_4450 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h104, h105⟩)
      else if h106 : j < 4550 then
        pent_shardE_4500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h105, h106⟩)
      else if h107 : j < 4600 then
        pent_shardE_4550 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h106, h107⟩)
      else if h108 : j < 4650 then
        pent_shardE_4600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h107, h108⟩)
      else if h109 : j < 4700 then
        pent_shardE_4650 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h108, h109⟩)
      else if h110 : j < 4750 then
        pent_shardE_4700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h109, h110⟩)
      else if h111 : j < 4800 then
        pent_shardE_4750 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h110, h111⟩)
      else if h112 : j < 4850 then
        pent_shardE_4800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h111, h112⟩)
      else if h113 : j < 4900 then
        pent_shardE_4850 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h112, h113⟩)
      else if h114 : j < 4950 then
        pent_shardE_4900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h113, h114⟩)
      else if h115 : j < 5000 then
        pent_shardE_4950 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h114, h115⟩)
      else if h116 : j < 5050 then
        pent_shardE_5000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h115, h116⟩)
      else if h117 : j < 5100 then
        pent_shardE_5050 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h116, h117⟩)
      else if h118 : j < 5150 then
        pent_shardE_5100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h117, h118⟩)
      else if h119 : j < 5200 then
        pent_shardE_5150 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h118, h119⟩)
      else if h120 : j < 5250 then
        pent_shardE_5200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h119, h120⟩)
      else if h121 : j < 5300 then
        pent_shardE_5250 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h120, h121⟩)
      else if h122 : j < 5350 then
        pent_shardE_5300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h121, h122⟩)
      else if h123 : j < 5400 then
        pent_shardE_5350 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h122, h123⟩)
      else if h124 : j < 5450 then
        pent_shardE_5400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h123, h124⟩)
      else if h125 : j < 5500 then
        pent_shardE_5450 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h124, h125⟩)
      else if h126 : j < 5550 then
        pent_shardE_5500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h125, h126⟩)
      else if h127 : j < 5600 then
        pent_shardE_5550 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h126, h127⟩)
      else if h128 : j < 5650 then
        pent_shardE_5600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h127, h128⟩)
      else if h129 : j < 5700 then
        pent_shardE_5650 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h128, h129⟩)
      else if h130 : j < 5750 then
        pent_shardE_5700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h129, h130⟩)
      else if h131 : j < 5800 then
        pent_shardE_5750 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h130, h131⟩)
      else if h132 : j < 5850 then
        pent_shardE_5800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h131, h132⟩)
      else if h133 : j < 5900 then
        pent_shardE_5850 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h132, h133⟩)
      else if h134 : j < 5950 then
        pent_shardE_5900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h133, h134⟩)
      else if h135 : j < 6000 then
        pent_shardE_5950 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h134, h135⟩)
      else if h136 : j < 6050 then
        pent_shardE_6000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h135, h136⟩)
      else if h137 : j < 6100 then
        pent_shardE_6050 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h136, h137⟩)
      else if h138 : j < 6150 then
        pent_shardE_6100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h137, h138⟩)
      else if h139 : j < 6200 then
        pent_shardE_6150 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h138, h139⟩)
      else if h140 : j < 6250 then
        pent_shardE_6200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h139, h140⟩)
      else if h141 : j < 6300 then
        pent_shardE_6250 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h140, h141⟩)
      else if h142 : j < 6350 then
        pent_shardE_6300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h141, h142⟩)
      else if h143 : j < 6400 then
        pent_shardE_6350 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h142, h143⟩)
      else if h144 : j < 6450 then
        pent_shardE_6400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h143, h144⟩)
      else if h145 : j < 6500 then
        pent_shardE_6450 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h144, h145⟩)
      else if h146 : j < 6550 then
        pent_shardE_6500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h145, h146⟩)
      else if h147 : j < 6600 then
        pent_shardE_6550 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h146, h147⟩)
      else if h148 : j < 6650 then
        pent_shardE_6600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h147, h148⟩)
      else if h149 : j < 6700 then
        pent_shardE_6650 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h148, h149⟩)
      else if h150 : j < 6750 then
        pent_shardE_6700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h149, h150⟩)
      else if h151 : j < 6800 then
        pent_shardE_6750 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h150, h151⟩)
      else if h152 : j < 6850 then
        pent_shardE_6800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h151, h152⟩)
      else if h153 : j < 6900 then
        pent_shardE_6850 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h152, h153⟩)
      else if h154 : j < 6950 then
        pent_shardE_6900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h153, h154⟩)
      else if h155 : j < 7000 then
        pent_shardE_6950 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h154, h155⟩)
      else if h156 : j < 7050 then
        pent_shardE_7000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h155, h156⟩)
      else if h157 : j < 7100 then
        pent_shardE_7050 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h156, h157⟩)
      else if h158 : j < 7150 then
        pent_shardE_7100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h157, h158⟩)
      else if h159 : j < 7200 then
        pent_shardE_7150 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h158, h159⟩)
      else if h160 : j < 7250 then
        pent_shardE_7200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h159, h160⟩)
      else if h161 : j < 7263 then
        pent_shardE_7250 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h160, h161⟩)
      else
        absurd hj h161
    obtain ⟨fuel, hloop⟩ := hloopE
    rw [getElem!_pos PentFrontier j hj] at hloop
    have hcheck := loop_some_true hloop g
      ⟨PentFrontier[j]'hj, List.mem_singleton_self _, hrh⟩
    obtain ⟨a, ha, hiso⟩ := checkFinal_correct pent_archive_pre_iso hcheck hfin
    refine ⟨a, ?_, hiso⟩
    show a ∈ TriData ++ QuadData ++ PentData ++ HexData
    exact List.mem_append_left _ (List.mem_append_right _ ha)

end Kepler.Graphs
