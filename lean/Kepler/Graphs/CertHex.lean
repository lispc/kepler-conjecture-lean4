/-
Hex seed (p = 3) enumeration certificate wiring.
Evaluation-side file: `native_decide` allowed (DECISIONS.md 2026-08-10);
every assembly proof is a pure kernel proof.  Mirrors CertTri.lean.
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.HexTop
import Kepler.Graphs.Worklist
import Kepler.Graphs.CertShards.Hex.K001
import Kepler.Graphs.CertShards.Hex.K002
import Kepler.Graphs.CertShards.Hex.K006
import Kepler.Graphs.CertShards.Hex.K008
import Kepler.Graphs.CertShards.Hex.K009
import Kepler.Graphs.CertShards.Hex.K010
import Kepler.Graphs.CertShards.Hex.K011
import Kepler.Graphs.CertShards.Hex.K012
import Kepler.Graphs.CertShards.Hex.K013
import Kepler.Graphs.CertShards.Hex.K014
import Kepler.Graphs.CertShards.Hex.K015
import Kepler.Graphs.CertShards.Hex.K016
import Kepler.Graphs.CertShards.Hex.K018
import Kepler.Graphs.CertShards.Hex.K019
import Kepler.Graphs.CertShards.Hex.K020
import Kepler.Graphs.CertShards.Hex.K021
import Kepler.Graphs.CertShards.Hex.K022
import Kepler.Graphs.CertShards.Hex.K023
import Kepler.Graphs.CertShards.Hex.K024
import Kepler.Graphs.CertShards.Hex.K025
import Kepler.Graphs.CertShards.Hex.K027
import Kepler.Graphs.CertShards.Hex.K028
import Kepler.Graphs.CertShards.Hex.K029
import Kepler.Graphs.CertShards.Hex.K030
import Kepler.Graphs.CertShards.Hex.K031
import Kepler.Graphs.CertShards.Hex.K032
import Kepler.Graphs.CertShards.Hex.K034
import Kepler.Graphs.CertShards.Hex.K036
import Kepler.Graphs.CertShards.Hex.K037
import Kepler.Graphs.CertShards.Hex.K038
import Kepler.Graphs.CertShards.Hex.K039
import Kepler.Graphs.CertShards.Hex.K040
import Kepler.Graphs.CertShards.Hex.K041
import Kepler.Graphs.CertShards.Hex.K042
import Kepler.Graphs.CertShards.Hex.K044
import Kepler.Graphs.CertShards.Hex.K045
import Kepler.Graphs.CertShards.Hex.K047
import Kepler.Graphs.CertShards.Hex.K048
import Kepler.Graphs.CertShards.Hex.K049
import Kepler.Graphs.CertShards.Hex.K050
import Kepler.Graphs.CertShards.Hex.K051
import Kepler.Graphs.CertShards.Hex.K052
import Kepler.Graphs.CertShards.Hex.K053
import Kepler.Graphs.CertShards.Hex.K054
import Kepler.Graphs.CertShards.Hex.K055
import Kepler.Graphs.CertShards.Hex.K056
import Kepler.Graphs.CertShards.Hex.K057
import Kepler.Graphs.CertShards.Hex.K058
import Kepler.Graphs.CertShards.Hex.K059
import Kepler.Graphs.CertShards.Hex.K060
import Kepler.Graphs.CertShards.Hex.K061
import Kepler.Graphs.CertShards.Hex.K062
import Kepler.Graphs.CertShards.Hex.K063
import Kepler.Graphs.CertShards.Hex.K064
import Kepler.Graphs.CertShards.Hex.K065
import Kepler.Graphs.CertShards.Hex.K066
import Kepler.Graphs.CertShards.Hex.K067
import Kepler.Graphs.CertShards.Hex.K068
import Kepler.Graphs.CertShards.Hex.K069
import Kepler.Graphs.CertShards.Hex.K070
import Kepler.Graphs.CertShards.Hex.K071
import Kepler.Graphs.CertShards.Hex.K072
import Kepler.Graphs.CertShards.Hex.K073
import Kepler.Graphs.CertShards.Hex.K074
import Kepler.Graphs.CertShards.Hex.K075
import Kepler.Graphs.CertShards.Hex.K076
import Kepler.Graphs.CertShards.HexR.K001
import Kepler.Graphs.CertShards.HexR.K002
import Kepler.Graphs.CertShards.HexR.K003
import Kepler.Graphs.CertShards.HexR.K004
import Kepler.Graphs.CertShards.HexR.K005
import Kepler.Graphs.CertShards.HexR.K006
import Kepler.Graphs.CertShards.HexR.K007
import Kepler.Graphs.CertShards.HexR.K008
import Kepler.Graphs.CertShards.HexR.K009
import Kepler.Graphs.CertShards.HexR.K010
import Kepler.Graphs.CertShards.HexR.K011
import Kepler.Graphs.CertShards.HexR.K012
import Kepler.Graphs.CertShards.HexR.K013
import Kepler.Graphs.CertShards.HexR.K014
import Kepler.Graphs.CertShards.HexR.K015
import Kepler.Graphs.CertShards.HexR.K016
import Kepler.Graphs.CertShards.HexR.K017
import Kepler.Graphs.CertShards.HexR.K018
import Kepler.Graphs.CertShards.HexR.K019
import Kepler.Graphs.CertShards.HexR.K020
import Kepler.Graphs.CertShards.HexR.K021
import Kepler.Graphs.CertShards.HexR.K022
import Kepler.Graphs.CertShards.HexR.K023
import Kepler.Graphs.CertShards.HexR.K024
import Kepler.Graphs.CertShards.HexR.K025
import Kepler.Graphs.CertShards.HexR.K026
import Kepler.Graphs.CertShards.HexR.K027
import Kepler.Graphs.CertShards.HexR.K028
import Kepler.Graphs.CertShards.HexR.K029
import Kepler.Graphs.CertShards.HexR.K030
import Kepler.Graphs.CertShards.HexR.K031
import Kepler.Graphs.CertShards.HexR.K032
import Kepler.Graphs.CertShards.HexR.K033
import Kepler.Graphs.CertShards.HexR.K034
import Kepler.Graphs.CertShards.HexR.K035
import Kepler.Graphs.CertShards.HexR.K036
import Kepler.Graphs.CertShards.HexR.K037
import Kepler.Graphs.CertShards.HexR.K038
import Kepler.Graphs.CertShards.HexR.K039
import Kepler.Graphs.CertShards.HexR.K040
import Kepler.Graphs.CertShards.HexR.K041
import Kepler.Graphs.CertShards.HexR.K042
import Kepler.Graphs.CertShards.HexR.K043
import Kepler.Graphs.CertShards.HexR.K044
import Kepler.Graphs.CertShards.HexR.K045
import Kepler.Graphs.CertShards.HexR.K046
import Kepler.Graphs.CertShards.HexR.K047
import Kepler.Graphs.CertShards.HexR.K048
import Kepler.Graphs.CertShards.HexR.K049
import Kepler.Graphs.CertShards.HexR.K050
import Kepler.Graphs.CertShards.HexR.K051
import Kepler.Graphs.CertShards.HexR.K052
import Kepler.Graphs.CertShards.HexR.K053
import Kepler.Graphs.CertShards.HexR.K054
import Kepler.Graphs.CertShards.HexR.K055
import Kepler.Graphs.CertShards.HexR.K056
import Kepler.Graphs.CertShards.HexR.K057
import Kepler.Graphs.CertShards.HexR.K058
import Kepler.Graphs.CertShards.HexR.K059
import Kepler.Graphs.CertShards.HexR.K060
import Kepler.Graphs.CertShards.HexR.K061
import Kepler.Graphs.CertShards.HexR.K062
import Kepler.Graphs.CertShards.HexR.K063
import Kepler.Graphs.CertShards.HexR.K064
import Kepler.Graphs.CertShards.HexR.K065
import Kepler.Graphs.CertShards.HexR.K066
import Kepler.Graphs.CertShards.HexR.K067
import Kepler.Graphs.CertShards.HexR.K068
import Kepler.Graphs.CertShards.HexR.K069
import Kepler.Graphs.CertShards.HexR.K070
import Kepler.Graphs.CertShards.HexR.K071
import Kepler.Graphs.CertShards.HexR.K072
import Kepler.Graphs.CertShards.HexR.K073
import Kepler.Graphs.CertShards.HexR.K074
import Kepler.Graphs.CertShards.HexR.K075
import Kepler.Graphs.CertShards.HexR.K076
import Kepler.Graphs.CertShards.HexR.K077
import Kepler.Graphs.CertShards.HexR.K078
import Kepler.Graphs.CertShards.HexR.K079
import Kepler.Graphs.CertShards.HexR.K080
import Kepler.Graphs.CertShards.HexR.K081
import Kepler.Graphs.CertShards.HexR.K082
import Kepler.Graphs.CertShards.HexR.K083
import Kepler.Graphs.CertShards.HexR.K084
import Kepler.Graphs.CertShards.HexR.K085
import Kepler.Graphs.CertShards.HexR.K086
import Kepler.Graphs.CertShards.HexR.K087
import Kepler.Graphs.CertShards.HexR.K088
import Kepler.Graphs.CertShards.HexR.K089
import Kepler.Graphs.CertShards.HexR.K090
import Kepler.Graphs.CertShards.HexR.K091
import Kepler.Graphs.CertShards.HexR.K092
import Kepler.Graphs.CertShards.HexR.K093
import Kepler.Graphs.CertShards.HexR.K094
import Kepler.Graphs.CertShards.HexR.K095
import Kepler.Graphs.CertShards.HexR.K096
import Kepler.Graphs.CertShards.HexR.K097
import Kepler.Graphs.CertShards.HexR.K098
import Kepler.Graphs.CertShards.HexR.K099
import Kepler.Graphs.CertShards.HexR.K100
import Kepler.Graphs.CertShards.HexR.K101
import Kepler.Graphs.CertShards.HexR.K102
import Kepler.Graphs.CertShards.HexR.K103
import Kepler.Graphs.CertShards.HexR.K104
import Kepler.Graphs.CertShards.HexR.K105
import Kepler.Graphs.CertShards.HexR.K106
import Kepler.Graphs.CertShards.HexR.K107
import Kepler.Graphs.CertShards.HexR.K108
import Kepler.Graphs.CertShards.HexR.K109
import Kepler.Graphs.CertShards.HexR.K110
import Kepler.Graphs.CertShards.HexR.K111
import Kepler.Graphs.CertShards.HexR.K112
import Kepler.Graphs.CertShards.HexR.K113
import Kepler.Graphs.CertShards.HexR.K114
import Kepler.Graphs.CertShards.HexR.K115
import Kepler.Graphs.CertShards.HexR.K116
import Kepler.Graphs.CertShards.HexR.K117
import Kepler.Graphs.CertShards.HexR.K118
import Kepler.Graphs.CertShards.HexR.K119
import Kepler.Graphs.CertShards.HexR.K120
import Kepler.Graphs.CertShards.HexR.K121
import Kepler.Graphs.CertShards.HexR.K122
import Kepler.Graphs.CertShards.HexR.K123
import Kepler.Graphs.CertShards.HexR.K124
import Kepler.Graphs.CertShards.HexR.K125
import Kepler.Graphs.CertShards.HexR.K126
import Kepler.Graphs.CertShards.HexR.K127
import Kepler.Graphs.CertShards.HexR.K128
import Kepler.Graphs.CertShards.HexR.K129
import Kepler.Graphs.CertShards.HexR.K130
import Kepler.Graphs.CertShards.HexR.K131
import Kepler.Graphs.CertShards.HexR.K132
import Kepler.Graphs.CertShards.HexR.K133
import Kepler.Graphs.CertShards.HexR.K134
import Kepler.Graphs.CertShards.HexR.K135
import Kepler.Graphs.CertShards.HexR.K136
import Kepler.Graphs.CertShards.HexR.K137
import Kepler.Graphs.CertShards.HexR.K138
import Kepler.Graphs.CertShards.HexR.K139
import Kepler.Graphs.CertShards.HexR.K140
import Kepler.Graphs.CertShards.HexR.K141
import Kepler.Graphs.CertShards.HexR.K142
import Kepler.Graphs.CertShards.HexR.K143
import Kepler.Graphs.CertShards.HexR.K144
import Kepler.Graphs.CertShards.HexR.K145
import Kepler.Graphs.CertShards.HexR.K146
import Kepler.Graphs.CertShards.HexR.K147
import Kepler.Graphs.CertShards.HexR.K148
import Kepler.Graphs.CertShards.HexR.K149
import Kepler.Graphs.CertShards.HexR.K150
import Kepler.Graphs.CertShards.HexR.K151
import Kepler.Graphs.CertShards.HexR.K152
import Kepler.Graphs.CertShards.HexR.K153
import Kepler.Graphs.CertShards.HexR.K154
import Kepler.Graphs.CertShards.HexR.K155
import Kepler.Graphs.CertShards.HexR.K156
import Kepler.Graphs.CertShards.HexR.K157
import Kepler.Graphs.CertShards.HexR.K158
import Kepler.Graphs.CertShards.HexR.K159
import Kepler.Graphs.CertShards.HexR.K160
import Kepler.Graphs.CertShards.HexR.K161
import Kepler.Graphs.CertShards.HexR.K162
import Kepler.Graphs.CertShards.HexR.K163
import Kepler.Graphs.CertShards.HexR.K164
import Kepler.Graphs.CertShards.HexR.K165
import Kepler.Graphs.CertShards.HexR.K166
import Kepler.Graphs.CertShards.HexR.K167
import Kepler.Graphs.CertShards.HexR.K168
import Kepler.Graphs.CertShards.HexR.K169
import Kepler.Graphs.CertShards.HexR.K170
import Kepler.Graphs.CertShards.HexR.K171
import Kepler.Graphs.CertShards.HexR.K172
import Kepler.Graphs.CertShards.HexR.K173
import Kepler.Graphs.CertShards.HexR.K174
import Kepler.Graphs.CertShards.HexR.K175
import Kepler.Graphs.CertShards.HexR.K176
import Kepler.Graphs.CertShards.HexR.K177
import Kepler.Graphs.CertShards.HexR.K178
import Kepler.Graphs.CertShards.HexR.K179
import Kepler.Graphs.CertShards.HexR.K180
import Kepler.Graphs.CertShards.HexR.K181
import Kepler.Graphs.CertShards.HexR.K182
import Kepler.Graphs.CertShards.HexR.K183
import Kepler.Graphs.CertShards.HexR.K184
import Kepler.Graphs.CertShards.HexR.K185
import Kepler.Graphs.CertShards.HexR.K186
import Kepler.Graphs.CertShards.HexR.K187
import Kepler.Graphs.CertShards.HexR.K188
import Kepler.Graphs.CertShards.HexR.K189
import Kepler.Graphs.CertShards.HexR.K190
import Kepler.Graphs.CertShards.HexR.K191
import Kepler.Graphs.CertShards.HexR.K192
import Kepler.Graphs.CertShards.HexR.K193
import Kepler.Graphs.CertShards.HexR.K194
import Kepler.Graphs.CertShards.HexR.K195
import Kepler.Graphs.CertShards.HexR.K196
import Kepler.Graphs.CertShards.HexR.K197
import Kepler.Graphs.CertShards.HexR.K198
import Kepler.Graphs.CertShards.HexR.K199
import Kepler.Graphs.CertShards.HexR.K200
import Kepler.Graphs.CertShards.HexR.K201
import Kepler.Graphs.CertShards.HexR.K202
import Kepler.Graphs.CertShards.HexR.K203
import Kepler.Graphs.CertShards.HexR.K204
import Kepler.Graphs.CertShards.HexR.K205
import Kepler.Graphs.CertShards.HexR.K206
import Kepler.Graphs.CertShards.HexR.K207
import Kepler.Graphs.CertShards.HexR.K208
import Kepler.Graphs.CertShards.HexR.K209
import Kepler.Graphs.CertShards.HexR.K210
import Kepler.Graphs.CertShards.HexR.K211
import Kepler.Graphs.CertShards.HexR.K212
import Kepler.Graphs.CertShards.HexR.K213
import Kepler.Graphs.CertShards.HexR.K214
import Kepler.Graphs.CertShards.HexR.K215
import Kepler.Graphs.CertShards.HexR.K216
import Kepler.Graphs.CertShards.HexR.K217
import Kepler.Graphs.CertShards.HexR.K218
import Kepler.Graphs.CertShards.HexR.K219
import Kepler.Graphs.CertShards.HexR2.K000
import Kepler.Graphs.CertShards.HexR2.K001
import Kepler.Graphs.CertShards.HexR2.K002
import Kepler.Graphs.CertShards.HexR2.K003
import Kepler.Graphs.CertShards.HexR2.K004

set_option maxRecDepth 100000

namespace Kepler.Graphs

/-- Replay: every top node's `next_tame 3` children are exactly its tagged
children table entries. -/
theorem hex_top_replay : (List.range HexTop.length).all (fun i =>
    decide (next_tame 3 HexTop[i]! =
      (HexTopChildren[i]!).map (resolveChild HexTop HexFrontier))) = true := by
  native_decide

/-- Bounds: every tagged child index is in range of its target list. -/
theorem hex_top_bounds : (List.range HexTopChildren.length).all (fun i =>
    (HexTopChildren[i]!).all (fun t =>
      (t.1 && decide (t.2 < HexFrontier.length)) ||
        (!t.1 && decide (t.2 < HexTop.length)))) = true := by
  native_decide

/-- `HexTop` is closed under `next_tame 3` up to `HexFrontier`. -/
theorem hex_top_closed : ∀ x ∈ HexTop, ∀ c ∈ next_tame 3 x,
    c ∈ HexTop ∨ c ∈ HexFrontier :=
  closed_of_replay rfl hex_top_replay hex_top_bounds

/-- No final graphs in the Hex top. -/
theorem hex_top_no_finals : (HexTop.all (fun g => !g.final)) = true := by
  native_decide

theorem hex_top_final_archive :
    ∀ g ∈ HexTop, g.final = true → inIso g.fgraph Archive :=
  top_final_archive_of_no_finals hex_top_no_finals

/-- Every `HexData` entry satisfies `pre_iso_test`. -/
theorem hex_archive_pre : (HexData.all (fun a => preIsoTestB a)) = true := by
  native_decide

theorem hex_archive_pre_iso : ∀ a ∈ HexData, pre_iso_test a := fun a ha =>
  preIsoTestB_correct ((List.all_eq_true.mp hex_archive_pre) a ha)

/-- The seed-3 (`Hex`) case of the enumeration-completeness certificate. -/
theorem same_3 : ∀ g, TameEnumP 3 g → inIso g.fgraph Archive := by
  intro g htep
  obtain ⟨hr, hfin⟩ := htep
  have h0 : HexTop[0]'(by decide) = Seed 3 := by decide
  have hseed : Seed 3 ∈ HexTop := h0 ▸ List.getElem_mem _
  rcases frontier_cut HexTop HexFrontier hseed hex_top_closed hr
    with hS | ⟨h, hF, hrh⟩
  · exact hex_top_final_archive g hS hfin
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hF
    have hlenN : HexFrontier.length = 7684 := rfl
    rw [hlenN] at hj
    have hloopE : ∃ fuel, loop (next_tame 3) (checkFinal (buildBuckets HexData))
        fuel [HexFrontier[j]!] = some true :=
      if h0 : j < 1 then
        hexr2_shardE_0 j
          (List.mem_range'_1.mpr ⟨Nat.zero_le j, h0⟩)
      else if h1 : j < 2 then
        hexr2_shardE_1 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h0, h1⟩)
      else if h2 : j < 3 then
        hexr2_shardE_2 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h1, h2⟩)
      else if h3 : j < 4 then
        hexr2_shardE_3 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h2, h3⟩)
      else if h4 : j < 5 then
        hexr2_shardE_4 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h3, h4⟩)
      else if h5 : j < 10 then
        hexr_shardE_5 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h4, h5⟩)
      else if h6 : j < 15 then
        hexr_shardE_10 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h5, h6⟩)
      else if h7 : j < 20 then
        hexr_shardE_15 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h6, h7⟩)
      else if h8 : j < 25 then
        hexr_shardE_20 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h7, h8⟩)
      else if h9 : j < 30 then
        hexr_shardE_25 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h8, h9⟩)
      else if h10 : j < 35 then
        hexr_shardE_30 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h9, h10⟩)
      else if h11 : j < 40 then
        hexr_shardE_35 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h10, h11⟩)
      else if h12 : j < 45 then
        hexr_shardE_40 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h11, h12⟩)
      else if h13 : j < 50 then
        hexr_shardE_45 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h12, h13⟩)
      else if h14 : j < 55 then
        hexr_shardE_50 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h13, h14⟩)
      else if h15 : j < 60 then
        hexr_shardE_55 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h14, h15⟩)
      else if h16 : j < 65 then
        hexr_shardE_60 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h15, h16⟩)
      else if h17 : j < 70 then
        hexr_shardE_65 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h16, h17⟩)
      else if h18 : j < 75 then
        hexr_shardE_70 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h17, h18⟩)
      else if h19 : j < 80 then
        hexr_shardE_75 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h18, h19⟩)
      else if h20 : j < 85 then
        hexr_shardE_80 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h19, h20⟩)
      else if h21 : j < 90 then
        hexr_shardE_85 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h20, h21⟩)
      else if h22 : j < 95 then
        hexr_shardE_90 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h21, h22⟩)
      else if h23 : j < 100 then
        hexr_shardE_95 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h22, h23⟩)
      else if h24 : j < 200 then
        hex_shardE_100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h23, h24⟩)
      else if h25 : j < 300 then
        hex_shardE_200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h24, h25⟩)
      else if h26 : j < 305 then
        hexr_shardE_300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h25, h26⟩)
      else if h27 : j < 310 then
        hexr_shardE_305 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h26, h27⟩)
      else if h28 : j < 315 then
        hexr_shardE_310 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h27, h28⟩)
      else if h29 : j < 320 then
        hexr_shardE_315 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h28, h29⟩)
      else if h30 : j < 325 then
        hexr_shardE_320 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h29, h30⟩)
      else if h31 : j < 330 then
        hexr_shardE_325 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h30, h31⟩)
      else if h32 : j < 335 then
        hexr_shardE_330 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h31, h32⟩)
      else if h33 : j < 340 then
        hexr_shardE_335 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h32, h33⟩)
      else if h34 : j < 345 then
        hexr_shardE_340 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h33, h34⟩)
      else if h35 : j < 350 then
        hexr_shardE_345 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h34, h35⟩)
      else if h36 : j < 355 then
        hexr_shardE_350 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h35, h36⟩)
      else if h37 : j < 360 then
        hexr_shardE_355 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h36, h37⟩)
      else if h38 : j < 365 then
        hexr_shardE_360 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h37, h38⟩)
      else if h39 : j < 370 then
        hexr_shardE_365 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h38, h39⟩)
      else if h40 : j < 375 then
        hexr_shardE_370 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h39, h40⟩)
      else if h41 : j < 380 then
        hexr_shardE_375 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h40, h41⟩)
      else if h42 : j < 385 then
        hexr_shardE_380 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h41, h42⟩)
      else if h43 : j < 390 then
        hexr_shardE_385 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h42, h43⟩)
      else if h44 : j < 395 then
        hexr_shardE_390 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h43, h44⟩)
      else if h45 : j < 400 then
        hexr_shardE_395 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h44, h45⟩)
      else if h46 : j < 405 then
        hexr_shardE_400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h45, h46⟩)
      else if h47 : j < 410 then
        hexr_shardE_405 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h46, h47⟩)
      else if h48 : j < 415 then
        hexr_shardE_410 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h47, h48⟩)
      else if h49 : j < 420 then
        hexr_shardE_415 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h48, h49⟩)
      else if h50 : j < 425 then
        hexr_shardE_420 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h49, h50⟩)
      else if h51 : j < 430 then
        hexr_shardE_425 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h50, h51⟩)
      else if h52 : j < 435 then
        hexr_shardE_430 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h51, h52⟩)
      else if h53 : j < 440 then
        hexr_shardE_435 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h52, h53⟩)
      else if h54 : j < 445 then
        hexr_shardE_440 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h53, h54⟩)
      else if h55 : j < 450 then
        hexr_shardE_445 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h54, h55⟩)
      else if h56 : j < 455 then
        hexr_shardE_450 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h55, h56⟩)
      else if h57 : j < 460 then
        hexr_shardE_455 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h56, h57⟩)
      else if h58 : j < 465 then
        hexr_shardE_460 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h57, h58⟩)
      else if h59 : j < 470 then
        hexr_shardE_465 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h58, h59⟩)
      else if h60 : j < 475 then
        hexr_shardE_470 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h59, h60⟩)
      else if h61 : j < 480 then
        hexr_shardE_475 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h60, h61⟩)
      else if h62 : j < 485 then
        hexr_shardE_480 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h61, h62⟩)
      else if h63 : j < 490 then
        hexr_shardE_485 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h62, h63⟩)
      else if h64 : j < 495 then
        hexr_shardE_490 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h63, h64⟩)
      else if h65 : j < 500 then
        hexr_shardE_495 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h64, h65⟩)
      else if h66 : j < 505 then
        hexr_shardE_500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h65, h66⟩)
      else if h67 : j < 510 then
        hexr_shardE_505 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h66, h67⟩)
      else if h68 : j < 515 then
        hexr_shardE_510 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h67, h68⟩)
      else if h69 : j < 520 then
        hexr_shardE_515 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h68, h69⟩)
      else if h70 : j < 525 then
        hexr_shardE_520 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h69, h70⟩)
      else if h71 : j < 530 then
        hexr_shardE_525 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h70, h71⟩)
      else if h72 : j < 535 then
        hexr_shardE_530 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h71, h72⟩)
      else if h73 : j < 540 then
        hexr_shardE_535 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h72, h73⟩)
      else if h74 : j < 545 then
        hexr_shardE_540 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h73, h74⟩)
      else if h75 : j < 550 then
        hexr_shardE_545 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h74, h75⟩)
      else if h76 : j < 555 then
        hexr_shardE_550 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h75, h76⟩)
      else if h77 : j < 560 then
        hexr_shardE_555 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h76, h77⟩)
      else if h78 : j < 565 then
        hexr_shardE_560 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h77, h78⟩)
      else if h79 : j < 570 then
        hexr_shardE_565 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h78, h79⟩)
      else if h80 : j < 575 then
        hexr_shardE_570 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h79, h80⟩)
      else if h81 : j < 580 then
        hexr_shardE_575 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h80, h81⟩)
      else if h82 : j < 585 then
        hexr_shardE_580 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h81, h82⟩)
      else if h83 : j < 590 then
        hexr_shardE_585 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h82, h83⟩)
      else if h84 : j < 595 then
        hexr_shardE_590 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h83, h84⟩)
      else if h85 : j < 600 then
        hexr_shardE_595 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h84, h85⟩)
      else if h86 : j < 700 then
        hex_shardE_600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h85, h86⟩)
      else if h87 : j < 705 then
        hexr_shardE_700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h86, h87⟩)
      else if h88 : j < 710 then
        hexr_shardE_705 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h87, h88⟩)
      else if h89 : j < 715 then
        hexr_shardE_710 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h88, h89⟩)
      else if h90 : j < 720 then
        hexr_shardE_715 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h89, h90⟩)
      else if h91 : j < 725 then
        hexr_shardE_720 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h90, h91⟩)
      else if h92 : j < 730 then
        hexr_shardE_725 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h91, h92⟩)
      else if h93 : j < 735 then
        hexr_shardE_730 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h92, h93⟩)
      else if h94 : j < 740 then
        hexr_shardE_735 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h93, h94⟩)
      else if h95 : j < 745 then
        hexr_shardE_740 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h94, h95⟩)
      else if h96 : j < 750 then
        hexr_shardE_745 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h95, h96⟩)
      else if h97 : j < 755 then
        hexr_shardE_750 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h96, h97⟩)
      else if h98 : j < 760 then
        hexr_shardE_755 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h97, h98⟩)
      else if h99 : j < 765 then
        hexr_shardE_760 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h98, h99⟩)
      else if h100 : j < 770 then
        hexr_shardE_765 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h99, h100⟩)
      else if h101 : j < 775 then
        hexr_shardE_770 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h100, h101⟩)
      else if h102 : j < 780 then
        hexr_shardE_775 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h101, h102⟩)
      else if h103 : j < 785 then
        hexr_shardE_780 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h102, h103⟩)
      else if h104 : j < 790 then
        hexr_shardE_785 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h103, h104⟩)
      else if h105 : j < 795 then
        hexr_shardE_790 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h104, h105⟩)
      else if h106 : j < 800 then
        hexr_shardE_795 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h105, h106⟩)
      else if h107 : j < 900 then
        hex_shardE_800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h106, h107⟩)
      else if h108 : j < 1000 then
        hex_shardE_900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h107, h108⟩)
      else if h109 : j < 1100 then
        hex_shardE_1000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h108, h109⟩)
      else if h110 : j < 1200 then
        hex_shardE_1100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h109, h110⟩)
      else if h111 : j < 1300 then
        hex_shardE_1200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h110, h111⟩)
      else if h112 : j < 1400 then
        hex_shardE_1300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h111, h112⟩)
      else if h113 : j < 1500 then
        hex_shardE_1400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h112, h113⟩)
      else if h114 : j < 1600 then
        hex_shardE_1500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h113, h114⟩)
      else if h115 : j < 1700 then
        hex_shardE_1600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h114, h115⟩)
      else if h116 : j < 1705 then
        hexr_shardE_1700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h115, h116⟩)
      else if h117 : j < 1710 then
        hexr_shardE_1705 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h116, h117⟩)
      else if h118 : j < 1715 then
        hexr_shardE_1710 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h117, h118⟩)
      else if h119 : j < 1720 then
        hexr_shardE_1715 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h118, h119⟩)
      else if h120 : j < 1725 then
        hexr_shardE_1720 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h119, h120⟩)
      else if h121 : j < 1730 then
        hexr_shardE_1725 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h120, h121⟩)
      else if h122 : j < 1735 then
        hexr_shardE_1730 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h121, h122⟩)
      else if h123 : j < 1740 then
        hexr_shardE_1735 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h122, h123⟩)
      else if h124 : j < 1745 then
        hexr_shardE_1740 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h123, h124⟩)
      else if h125 : j < 1750 then
        hexr_shardE_1745 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h124, h125⟩)
      else if h126 : j < 1755 then
        hexr_shardE_1750 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h125, h126⟩)
      else if h127 : j < 1760 then
        hexr_shardE_1755 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h126, h127⟩)
      else if h128 : j < 1765 then
        hexr_shardE_1760 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h127, h128⟩)
      else if h129 : j < 1770 then
        hexr_shardE_1765 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h128, h129⟩)
      else if h130 : j < 1775 then
        hexr_shardE_1770 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h129, h130⟩)
      else if h131 : j < 1780 then
        hexr_shardE_1775 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h130, h131⟩)
      else if h132 : j < 1785 then
        hexr_shardE_1780 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h131, h132⟩)
      else if h133 : j < 1790 then
        hexr_shardE_1785 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h132, h133⟩)
      else if h134 : j < 1795 then
        hexr_shardE_1790 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h133, h134⟩)
      else if h135 : j < 1800 then
        hexr_shardE_1795 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h134, h135⟩)
      else if h136 : j < 1900 then
        hex_shardE_1800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h135, h136⟩)
      else if h137 : j < 2000 then
        hex_shardE_1900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h136, h137⟩)
      else if h138 : j < 2100 then
        hex_shardE_2000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h137, h138⟩)
      else if h139 : j < 2200 then
        hex_shardE_2100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h138, h139⟩)
      else if h140 : j < 2300 then
        hex_shardE_2200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h139, h140⟩)
      else if h141 : j < 2400 then
        hex_shardE_2300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h140, h141⟩)
      else if h142 : j < 2500 then
        hex_shardE_2400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h141, h142⟩)
      else if h143 : j < 2600 then
        hex_shardE_2500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h142, h143⟩)
      else if h144 : j < 2605 then
        hexr_shardE_2600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h143, h144⟩)
      else if h145 : j < 2610 then
        hexr_shardE_2605 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h144, h145⟩)
      else if h146 : j < 2615 then
        hexr_shardE_2610 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h145, h146⟩)
      else if h147 : j < 2620 then
        hexr_shardE_2615 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h146, h147⟩)
      else if h148 : j < 2625 then
        hexr_shardE_2620 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h147, h148⟩)
      else if h149 : j < 2630 then
        hexr_shardE_2625 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h148, h149⟩)
      else if h150 : j < 2635 then
        hexr_shardE_2630 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h149, h150⟩)
      else if h151 : j < 2640 then
        hexr_shardE_2635 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h150, h151⟩)
      else if h152 : j < 2645 then
        hexr_shardE_2640 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h151, h152⟩)
      else if h153 : j < 2650 then
        hexr_shardE_2645 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h152, h153⟩)
      else if h154 : j < 2655 then
        hexr_shardE_2650 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h153, h154⟩)
      else if h155 : j < 2660 then
        hexr_shardE_2655 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h154, h155⟩)
      else if h156 : j < 2665 then
        hexr_shardE_2660 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h155, h156⟩)
      else if h157 : j < 2670 then
        hexr_shardE_2665 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h156, h157⟩)
      else if h158 : j < 2675 then
        hexr_shardE_2670 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h157, h158⟩)
      else if h159 : j < 2680 then
        hexr_shardE_2675 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h158, h159⟩)
      else if h160 : j < 2685 then
        hexr_shardE_2680 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h159, h160⟩)
      else if h161 : j < 2690 then
        hexr_shardE_2685 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h160, h161⟩)
      else if h162 : j < 2695 then
        hexr_shardE_2690 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h161, h162⟩)
      else if h163 : j < 2700 then
        hexr_shardE_2695 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h162, h163⟩)
      else if h164 : j < 2800 then
        hex_shardE_2700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h163, h164⟩)
      else if h165 : j < 2900 then
        hex_shardE_2800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h164, h165⟩)
      else if h166 : j < 3000 then
        hex_shardE_2900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h165, h166⟩)
      else if h167 : j < 3100 then
        hex_shardE_3000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h166, h167⟩)
      else if h168 : j < 3200 then
        hex_shardE_3100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h167, h168⟩)
      else if h169 : j < 3300 then
        hex_shardE_3200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h168, h169⟩)
      else if h170 : j < 3305 then
        hexr_shardE_3300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h169, h170⟩)
      else if h171 : j < 3310 then
        hexr_shardE_3305 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h170, h171⟩)
      else if h172 : j < 3315 then
        hexr_shardE_3310 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h171, h172⟩)
      else if h173 : j < 3320 then
        hexr_shardE_3315 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h172, h173⟩)
      else if h174 : j < 3325 then
        hexr_shardE_3320 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h173, h174⟩)
      else if h175 : j < 3330 then
        hexr_shardE_3325 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h174, h175⟩)
      else if h176 : j < 3335 then
        hexr_shardE_3330 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h175, h176⟩)
      else if h177 : j < 3340 then
        hexr_shardE_3335 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h176, h177⟩)
      else if h178 : j < 3345 then
        hexr_shardE_3340 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h177, h178⟩)
      else if h179 : j < 3350 then
        hexr_shardE_3345 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h178, h179⟩)
      else if h180 : j < 3355 then
        hexr_shardE_3350 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h179, h180⟩)
      else if h181 : j < 3360 then
        hexr_shardE_3355 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h180, h181⟩)
      else if h182 : j < 3365 then
        hexr_shardE_3360 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h181, h182⟩)
      else if h183 : j < 3370 then
        hexr_shardE_3365 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h182, h183⟩)
      else if h184 : j < 3375 then
        hexr_shardE_3370 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h183, h184⟩)
      else if h185 : j < 3380 then
        hexr_shardE_3375 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h184, h185⟩)
      else if h186 : j < 3385 then
        hexr_shardE_3380 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h185, h186⟩)
      else if h187 : j < 3390 then
        hexr_shardE_3385 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h186, h187⟩)
      else if h188 : j < 3395 then
        hexr_shardE_3390 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h187, h188⟩)
      else if h189 : j < 3400 then
        hexr_shardE_3395 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h188, h189⟩)
      else if h190 : j < 3500 then
        hex_shardE_3400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h189, h190⟩)
      else if h191 : j < 3505 then
        hexr_shardE_3500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h190, h191⟩)
      else if h192 : j < 3510 then
        hexr_shardE_3505 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h191, h192⟩)
      else if h193 : j < 3515 then
        hexr_shardE_3510 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h192, h193⟩)
      else if h194 : j < 3520 then
        hexr_shardE_3515 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h193, h194⟩)
      else if h195 : j < 3525 then
        hexr_shardE_3520 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h194, h195⟩)
      else if h196 : j < 3530 then
        hexr_shardE_3525 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h195, h196⟩)
      else if h197 : j < 3535 then
        hexr_shardE_3530 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h196, h197⟩)
      else if h198 : j < 3540 then
        hexr_shardE_3535 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h197, h198⟩)
      else if h199 : j < 3545 then
        hexr_shardE_3540 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h198, h199⟩)
      else if h200 : j < 3550 then
        hexr_shardE_3545 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h199, h200⟩)
      else if h201 : j < 3555 then
        hexr_shardE_3550 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h200, h201⟩)
      else if h202 : j < 3560 then
        hexr_shardE_3555 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h201, h202⟩)
      else if h203 : j < 3565 then
        hexr_shardE_3560 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h202, h203⟩)
      else if h204 : j < 3570 then
        hexr_shardE_3565 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h203, h204⟩)
      else if h205 : j < 3575 then
        hexr_shardE_3570 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h204, h205⟩)
      else if h206 : j < 3580 then
        hexr_shardE_3575 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h205, h206⟩)
      else if h207 : j < 3585 then
        hexr_shardE_3580 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h206, h207⟩)
      else if h208 : j < 3590 then
        hexr_shardE_3585 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h207, h208⟩)
      else if h209 : j < 3595 then
        hexr_shardE_3590 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h208, h209⟩)
      else if h210 : j < 3600 then
        hexr_shardE_3595 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h209, h210⟩)
      else if h211 : j < 3700 then
        hex_shardE_3600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h210, h211⟩)
      else if h212 : j < 3800 then
        hex_shardE_3700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h211, h212⟩)
      else if h213 : j < 3900 then
        hex_shardE_3800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h212, h213⟩)
      else if h214 : j < 4000 then
        hex_shardE_3900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h213, h214⟩)
      else if h215 : j < 4100 then
        hex_shardE_4000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h214, h215⟩)
      else if h216 : j < 4200 then
        hex_shardE_4100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h215, h216⟩)
      else if h217 : j < 4300 then
        hex_shardE_4200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h216, h217⟩)
      else if h218 : j < 4305 then
        hexr_shardE_4300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h217, h218⟩)
      else if h219 : j < 4310 then
        hexr_shardE_4305 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h218, h219⟩)
      else if h220 : j < 4315 then
        hexr_shardE_4310 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h219, h220⟩)
      else if h221 : j < 4320 then
        hexr_shardE_4315 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h220, h221⟩)
      else if h222 : j < 4325 then
        hexr_shardE_4320 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h221, h222⟩)
      else if h223 : j < 4330 then
        hexr_shardE_4325 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h222, h223⟩)
      else if h224 : j < 4335 then
        hexr_shardE_4330 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h223, h224⟩)
      else if h225 : j < 4340 then
        hexr_shardE_4335 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h224, h225⟩)
      else if h226 : j < 4345 then
        hexr_shardE_4340 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h225, h226⟩)
      else if h227 : j < 4350 then
        hexr_shardE_4345 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h226, h227⟩)
      else if h228 : j < 4355 then
        hexr_shardE_4350 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h227, h228⟩)
      else if h229 : j < 4360 then
        hexr_shardE_4355 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h228, h229⟩)
      else if h230 : j < 4365 then
        hexr_shardE_4360 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h229, h230⟩)
      else if h231 : j < 4370 then
        hexr_shardE_4365 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h230, h231⟩)
      else if h232 : j < 4375 then
        hexr_shardE_4370 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h231, h232⟩)
      else if h233 : j < 4380 then
        hexr_shardE_4375 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h232, h233⟩)
      else if h234 : j < 4385 then
        hexr_shardE_4380 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h233, h234⟩)
      else if h235 : j < 4390 then
        hexr_shardE_4385 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h234, h235⟩)
      else if h236 : j < 4395 then
        hexr_shardE_4390 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h235, h236⟩)
      else if h237 : j < 4400 then
        hexr_shardE_4395 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h236, h237⟩)
      else if h238 : j < 4500 then
        hex_shardE_4400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h237, h238⟩)
      else if h239 : j < 4600 then
        hex_shardE_4500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h238, h239⟩)
      else if h240 : j < 4605 then
        hexr_shardE_4600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h239, h240⟩)
      else if h241 : j < 4610 then
        hexr_shardE_4605 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h240, h241⟩)
      else if h242 : j < 4615 then
        hexr_shardE_4610 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h241, h242⟩)
      else if h243 : j < 4620 then
        hexr_shardE_4615 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h242, h243⟩)
      else if h244 : j < 4625 then
        hexr_shardE_4620 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h243, h244⟩)
      else if h245 : j < 4630 then
        hexr_shardE_4625 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h244, h245⟩)
      else if h246 : j < 4635 then
        hexr_shardE_4630 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h245, h246⟩)
      else if h247 : j < 4640 then
        hexr_shardE_4635 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h246, h247⟩)
      else if h248 : j < 4645 then
        hexr_shardE_4640 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h247, h248⟩)
      else if h249 : j < 4650 then
        hexr_shardE_4645 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h248, h249⟩)
      else if h250 : j < 4655 then
        hexr_shardE_4650 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h249, h250⟩)
      else if h251 : j < 4660 then
        hexr_shardE_4655 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h250, h251⟩)
      else if h252 : j < 4665 then
        hexr_shardE_4660 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h251, h252⟩)
      else if h253 : j < 4670 then
        hexr_shardE_4665 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h252, h253⟩)
      else if h254 : j < 4675 then
        hexr_shardE_4670 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h253, h254⟩)
      else if h255 : j < 4680 then
        hexr_shardE_4675 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h254, h255⟩)
      else if h256 : j < 4685 then
        hexr_shardE_4680 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h255, h256⟩)
      else if h257 : j < 4690 then
        hexr_shardE_4685 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h256, h257⟩)
      else if h258 : j < 4695 then
        hexr_shardE_4690 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h257, h258⟩)
      else if h259 : j < 4700 then
        hexr_shardE_4695 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h258, h259⟩)
      else if h260 : j < 4800 then
        hex_shardE_4700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h259, h260⟩)
      else if h261 : j < 4900 then
        hex_shardE_4800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h260, h261⟩)
      else if h262 : j < 5000 then
        hex_shardE_4900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h261, h262⟩)
      else if h263 : j < 5100 then
        hex_shardE_5000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h262, h263⟩)
      else if h264 : j < 5200 then
        hex_shardE_5100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h263, h264⟩)
      else if h265 : j < 5300 then
        hex_shardE_5200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h264, h265⟩)
      else if h266 : j < 5400 then
        hex_shardE_5300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h265, h266⟩)
      else if h267 : j < 5500 then
        hex_shardE_5400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h266, h267⟩)
      else if h268 : j < 5600 then
        hex_shardE_5500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h267, h268⟩)
      else if h269 : j < 5700 then
        hex_shardE_5600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h268, h269⟩)
      else if h270 : j < 5800 then
        hex_shardE_5700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h269, h270⟩)
      else if h271 : j < 5900 then
        hex_shardE_5800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h270, h271⟩)
      else if h272 : j < 6000 then
        hex_shardE_5900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h271, h272⟩)
      else if h273 : j < 6100 then
        hex_shardE_6000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h272, h273⟩)
      else if h274 : j < 6200 then
        hex_shardE_6100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h273, h274⟩)
      else if h275 : j < 6300 then
        hex_shardE_6200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h274, h275⟩)
      else if h276 : j < 6400 then
        hex_shardE_6300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h275, h276⟩)
      else if h277 : j < 6500 then
        hex_shardE_6400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h276, h277⟩)
      else if h278 : j < 6600 then
        hex_shardE_6500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h277, h278⟩)
      else if h279 : j < 6700 then
        hex_shardE_6600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h278, h279⟩)
      else if h280 : j < 6800 then
        hex_shardE_6700 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h279, h280⟩)
      else if h281 : j < 6900 then
        hex_shardE_6800 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h280, h281⟩)
      else if h282 : j < 7000 then
        hex_shardE_6900 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h281, h282⟩)
      else if h283 : j < 7100 then
        hex_shardE_7000 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h282, h283⟩)
      else if h284 : j < 7200 then
        hex_shardE_7100 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h283, h284⟩)
      else if h285 : j < 7300 then
        hex_shardE_7200 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h284, h285⟩)
      else if h286 : j < 7400 then
        hex_shardE_7300 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h285, h286⟩)
      else if h287 : j < 7500 then
        hex_shardE_7400 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h286, h287⟩)
      else if h288 : j < 7600 then
        hex_shardE_7500 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h287, h288⟩)
      else if h289 : j < 7684 then
        hex_shardE_7600 j
          (List.mem_range'_1.mpr ⟨le_of_not_gt h288, h289⟩)
      else
        absurd hj h289
    obtain ⟨fuel, hloop⟩ := hloopE
    rw [getElem!_pos HexFrontier j hj] at hloop
    have hcheck := loop_some_true hloop g
      ⟨HexFrontier[j]'hj, List.mem_singleton_self _, hrh⟩
    obtain ⟨a, ha, hiso⟩ := checkFinal_correct hex_archive_pre_iso hcheck hfin
    refine ⟨a, ?_, hiso⟩
    show a ∈ TriData ++ QuadData ++ PentData ++ HexData
    exact List.mem_append_right _ ha

end Kepler.Graphs
