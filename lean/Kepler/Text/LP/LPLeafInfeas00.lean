/-
  Kepler/Text/LP/LPLeafInfeas00 — LP 终端 per-record 骨架层（T2 波 2026-10-08，机器生成，勿手改）。

  生成器：`lean/scripts/gen_lp_skeleton.py`（infeasible 记录叶（PLACEHOLDER(LP-infeas) 语义）；再生成会覆盖本文件）。
  记录清单来源：reference/flyspeck/formal_lp/glpk/binary
  的 {easy,hard}_*.dat 确定性重放（parse_lpcert.py 已提交读器，
  DFS 序 = ti 序）。信任模型：叶 = open `sorry` 骨架（deferred-compute），
  闭合 = LP 重跑产物模块（`socert.py --col-major` 形，PilotCM204880136538
  在库样板）转发；语义核心与退化防线见 `Kepler.Text.LP.LPCert`。
-/
import Kepler.Text.LP.LPIds
import Kepler.LP.T121582585038t0004
import Kepler.LP.T121582585038t0007
import Kepler.LP.T121582585038t0009
import Kepler.LP.T124346922881t0002
import Kepler.LP.T124346922881t0007
import Kepler.LP.T124346922881t0010
import Kepler.LP.T15806819252t0001
import Kepler.LP.T15806819252t0004
import Kepler.LP.T15806819252t0006
import Kepler.LP.T15806819252t0007
import Kepler.LP.T15806819252t0009
import Kepler.LP.T161847242261t0082
import Kepler.LP.T161847242261t0122
import Kepler.LP.T161847242261t0124
import Kepler.LP.T161847242261t0126
import Kepler.LP.T161847242261t0923
import Kepler.LP.T161847242261t0938
import Kepler.LP.T161847242261t0940
import Kepler.LP.T161847242261t0998
import Kepler.LP.T161847242261t1097
import Kepler.LP.T161847242261t1120
import Kepler.LP.T161847242261t1141
import Kepler.LP.T161847242261t1176
import Kepler.LP.T161847242261t1183
import Kepler.LP.T161847242261t1187
import Kepler.LP.T161847242261t1208
import Kepler.LP.T161847242261t1210
import Kepler.LP.T161847242261t1212
import Kepler.LP.T161847242261t1225
import Kepler.LP.T161847242261t1227
import Kepler.LP.T161847242261t1324
import Kepler.LP.T161847242261t1353
import Kepler.LP.T161847242261t1355
import Kepler.LP.T161847242261t1362
import Kepler.LP.T161847242261t1369
import Kepler.LP.T161847242261t1370
import Kepler.LP.T161847242261t1372
import Kepler.LP.T161847242261t1411
import Kepler.LP.T161847242261t1413
import Kepler.LP.T161847242261t1447
import Kepler.LP.T161847242261t1604
import Kepler.LP.T161847242261t1607
import Kepler.LP.T161847242261t1613
import Kepler.LP.T161847242261t1625
import Kepler.LP.T161847242261t1627
import Kepler.LP.T161847242261t1629
import Kepler.LP.T161847242261t1635
import Kepler.LP.T161847242261t1637
import Kepler.LP.T161847242261t1677
import Kepler.LP.T161847242261t1679
import Kepler.LP.T161847242261t1686
import Kepler.LP.T161847242261t1691
import Kepler.LP.T161847242261t1693
import Kepler.LP.T161847242261t1695
import Kepler.LP.T161847242261t1700
import Kepler.LP.T161847242261t1701
import Kepler.LP.T161847242261t1703
import Kepler.LP.T161847242261t1753
import Kepler.LP.T161847242261t1755
import Kepler.LP.T161847242261t1782
import Kepler.LP.T161847242261t1824
import Kepler.LP.T161847242261t1826
import Kepler.LP.T161847242261t1827
import Kepler.LP.T161847242261t1828
import Kepler.LP.T161847242261t1829
import Kepler.LP.T161847242261t1933
import Kepler.LP.T161847242261t1934
import Kepler.LP.T161847242261t1939
import Kepler.LP.T161847242261t1965
import Kepler.LP.T161847242261t1972
import Kepler.LP.T161847242261t1974
import Kepler.LP.T161847242261t2017
import Kepler.LP.T161847242261t2019
import Kepler.LP.T161847242261t2049
import Kepler.LP.T161847242261t2063
import Kepler.LP.T161847242261t2064
import Kepler.LP.T161847242261t2068
import Kepler.LP.T161847242261t2070
import Kepler.LP.T161847242261t2102
import Kepler.LP.T161847242261t2104
import Kepler.LP.T161847242261t2105
import Kepler.LP.T161847242261t2107
import Kepler.LP.T161847242261t2138
import Kepler.LP.T161847242261t2220
import Kepler.LP.T161847242261t2227
import Kepler.LP.T161847242261t2232
import Kepler.LP.T161847242261t2236
import Kepler.LP.T161847242261t2238
import Kepler.LP.T161847242261t2247
import Kepler.LP.T161847242261t2250
import Kepler.LP.T161847242261t2252
import Kepler.LP.T161847242261t2261
import Kepler.LP.T161847242261t2265
import Kepler.LP.T161847242261t2267
import Kepler.LP.T161847242261t2275
import Kepler.LP.T161847242261t2278
import Kepler.LP.T161847242261t2426
import Kepler.LP.T161847242261t2429
import Kepler.LP.T161847242261t2435
import Kepler.LP.T161847242261t2447
import Kepler.LP.T161847242261t2449
import Kepler.LP.T161847242261t2451
import Kepler.LP.T161847242261t2457
import Kepler.LP.T161847242261t2460
import Kepler.LP.T161847242261t2501
import Kepler.LP.T161847242261t2508
import Kepler.LP.T161847242261t2510
import Kepler.LP.T161847242261t2515
import Kepler.LP.T161847242261t2516
import Kepler.LP.T161847242261t2518
import Kepler.LP.T161847242261t2520
import Kepler.LP.T161847242261t2526
import Kepler.LP.T161847242261t2528
import Kepler.LP.T161847242261t2573
import Kepler.LP.T161847242261t2574
import Kepler.LP.T161847242261t2576
import Kepler.LP.T161847242261t2580
import Kepler.LP.T161847242261t2583
import Kepler.LP.T161847242261t2585
import Kepler.LP.T161847242261t2671
import Kepler.LP.T161847242261t2672
import Kepler.LP.T161847242261t2674
import Kepler.LP.T161847242261t2675
import Kepler.LP.T161847242261t2677
import Kepler.LP.T161847242261t2692
import Kepler.LP.T161847242261t2708
import Kepler.LP.T161847242261t2710
import Kepler.LP.T161847242261t2718
import Kepler.LP.T161847242261t2805
import Kepler.LP.T161847242261t2810
import Kepler.LP.T161847242261t2814
import Kepler.LP.T161847242261t2818
import Kepler.LP.T161847242261t2822
import Kepler.LP.T161847242261t2824
import Kepler.LP.T161847242261t2833
import Kepler.LP.T161847242261t2838
import Kepler.LP.T161847242261t2846
import Kepler.LP.T161847242261t2852
import Kepler.LP.T161847242261t2859
import Kepler.LP.T161847242261t2862
import Kepler.LP.T161847242261t2868
import Kepler.LP.T161847242261t2870
import Kepler.LP.T161847242261t2878
import Kepler.LP.T161847242261t2881
import Kepler.LP.T161847242261t2893
import Kepler.LP.T179189825656t0000
import Kepler.LP.T195512614336t0024
import Kepler.LP.T195512614336t0027
import Kepler.LP.T195512614336t0029
import Kepler.LP.T201843411127t0004
import Kepler.LP.T201843411127t0007
import Kepler.LP.T201843411127t0009
import Kepler.LP.T206134563629t0002
import Kepler.LP.T206134563629t0007
import Kepler.LP.T206134563629t0010
import Kepler.LP.T215863975889t0019
import Kepler.LP.T215863975889t0083
import Kepler.LP.T215863975889t0100
import Kepler.LP.T215863975889t0102
import Kepler.LP.T215863975889t0104
import Kepler.LP.T215863975889t0115
import Kepler.LP.T215863975889t0134
import Kepler.LP.T215863975889t0136
import Kepler.LP.T215863975889t0149
import Kepler.LP.T215863975889t0175
import Kepler.LP.T215863975889t0178
import Kepler.LP.T215863975889t0180
import Kepler.LP.T216661698775t0004
import Kepler.LP.T216661698775t0009
import Kepler.LP.T216661698775t0012
import Kepler.LP.T216661698775t0014
import Kepler.LP.T216661698775t0017
import Kepler.LP.T216661698775t0019
import Kepler.LP.T223336279535t2552
import Kepler.LP.T234511714565t0000
import Kepler.LP.T250379175175t0014
import Kepler.LP.T250379175175t0017
import Kepler.LP.T250379175175t0019
import Kepler.LP.T50329387098t0004
import Kepler.LP.T50329387098t0007
import Kepler.LP.T50329387098t0009
import Kepler.LP.T50329387098t0018
import Kepler.LP.T50329387098t0021
import Kepler.LP.T50329387098t0023
import Kepler.LP.T62586200165t0001
import Kepler.LP.T62586200165t0004
import Kepler.LP.T62586200165t0006
import Kepler.LP.T62586200165t0007
import Kepler.LP.T62586200165t0009
set_option maxRecDepth 4096

namespace Kepler.Text.LP

/-- `234511714565_t0000`（easy_1#392 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT234511714565t0000 : LpTerminalInfeasibleCertified "234511714565_t0000" :=
  ⟨Kepler.LP.T234511714565t0000.rowCore, Kepler.LP.T234511714565t0000.row_check⟩

/-- `50329387098_t0004`（easy_11#486 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT50329387098t0004 : LpTerminalInfeasibleCertified "50329387098_t0004" :=
  ⟨Kepler.LP.T50329387098t0004.rowCore, Kepler.LP.T50329387098t0004.row_check⟩

/-- `50329387098_t0007`（easy_11#486 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT50329387098t0007 : LpTerminalInfeasibleCertified "50329387098_t0007" :=
  ⟨Kepler.LP.T50329387098t0007.rowCore, Kepler.LP.T50329387098t0007.row_check⟩

/-- `50329387098_t0009`（easy_11#486 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT50329387098t0009 : LpTerminalInfeasibleCertified "50329387098_t0009" :=
  ⟨Kepler.LP.T50329387098t0009.rowCore, Kepler.LP.T50329387098t0009.row_check⟩

/-- `50329387098_t0018`（easy_11#486 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT50329387098t0018 : LpTerminalInfeasibleCertified "50329387098_t0018" :=
  ⟨Kepler.LP.T50329387098t0018.rowCore, Kepler.LP.T50329387098t0018.row_check⟩

/-- `50329387098_t0021`（easy_11#486 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT50329387098t0021 : LpTerminalInfeasibleCertified "50329387098_t0021" :=
  ⟨Kepler.LP.T50329387098t0021.rowCore, Kepler.LP.T50329387098t0021.row_check⟩

/-- `50329387098_t0023`（easy_11#486 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT50329387098t0023 : LpTerminalInfeasibleCertified "50329387098_t0023" :=
  ⟨Kepler.LP.T50329387098t0023.rowCore, Kepler.LP.T50329387098t0023.row_check⟩

/-- `250379175175_t0014`（easy_14#556 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT250379175175t0014 : LpTerminalInfeasibleCertified "250379175175_t0014" :=
  ⟨Kepler.LP.T250379175175t0014.rowCore, Kepler.LP.T250379175175t0014.row_check⟩

/-- `250379175175_t0017`（easy_14#556 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT250379175175t0017 : LpTerminalInfeasibleCertified "250379175175_t0017" :=
  ⟨Kepler.LP.T250379175175t0017.rowCore, Kepler.LP.T250379175175t0017.row_check⟩

/-- `250379175175_t0019`（easy_14#556 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT250379175175t0019 : LpTerminalInfeasibleCertified "250379175175_t0019" :=
  ⟨Kepler.LP.T250379175175t0019.rowCore, Kepler.LP.T250379175175t0019.row_check⟩

/-- `195512614336_t0024`（easy_14#829 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT195512614336t0024 : LpTerminalInfeasibleCertified "195512614336_t0024" :=
  ⟨Kepler.LP.T195512614336t0024.rowCore, Kepler.LP.T195512614336t0024.row_check⟩

/-- `195512614336_t0027`（easy_14#829 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT195512614336t0027 : LpTerminalInfeasibleCertified "195512614336_t0027" :=
  ⟨Kepler.LP.T195512614336t0027.rowCore, Kepler.LP.T195512614336t0027.row_check⟩

/-- `195512614336_t0029`（easy_14#829 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT195512614336t0029 : LpTerminalInfeasibleCertified "195512614336_t0029" :=
  ⟨Kepler.LP.T195512614336t0029.rowCore, Kepler.LP.T195512614336t0029.row_check⟩

/-- `216661698775_t0004`（easy_16#487 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT216661698775t0004 : LpTerminalInfeasibleCertified "216661698775_t0004" :=
  ⟨Kepler.LP.T216661698775t0004.rowCore, Kepler.LP.T216661698775t0004.row_check⟩

/-- `216661698775_t0009`（easy_16#487 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT216661698775t0009 : LpTerminalInfeasibleCertified "216661698775_t0009" :=
  ⟨Kepler.LP.T216661698775t0009.rowCore, Kepler.LP.T216661698775t0009.row_check⟩

/-- `216661698775_t0012`（easy_16#487 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT216661698775t0012 : LpTerminalInfeasibleCertified "216661698775_t0012" :=
  ⟨Kepler.LP.T216661698775t0012.rowCore, Kepler.LP.T216661698775t0012.row_check⟩

/-- `216661698775_t0014`（easy_16#487 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT216661698775t0014 : LpTerminalInfeasibleCertified "216661698775_t0014" :=
  ⟨Kepler.LP.T216661698775t0014.rowCore, Kepler.LP.T216661698775t0014.row_check⟩

/-- `216661698775_t0017`（easy_16#487 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT216661698775t0017 : LpTerminalInfeasibleCertified "216661698775_t0017" :=
  ⟨Kepler.LP.T216661698775t0017.rowCore, Kepler.LP.T216661698775t0017.row_check⟩

/-- `216661698775_t0019`（easy_16#487 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT216661698775t0019 : LpTerminalInfeasibleCertified "216661698775_t0019" :=
  ⟨Kepler.LP.T216661698775t0019.rowCore, Kepler.LP.T216661698775t0019.row_check⟩

/-- `121582585038_t0004`（easy_17#362 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT121582585038t0004 : LpTerminalInfeasibleCertified "121582585038_t0004" :=
  ⟨Kepler.LP.T121582585038t0004.rowCore, Kepler.LP.T121582585038t0004.row_check⟩

/-- `121582585038_t0007`（easy_17#362 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT121582585038t0007 : LpTerminalInfeasibleCertified "121582585038_t0007" :=
  ⟨Kepler.LP.T121582585038t0007.rowCore, Kepler.LP.T121582585038t0007.row_check⟩

/-- `121582585038_t0009`（easy_17#362 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT121582585038t0009 : LpTerminalInfeasibleCertified "121582585038_t0009" :=
  ⟨Kepler.LP.T121582585038t0009.rowCore, Kepler.LP.T121582585038t0009.row_check⟩

/-- `15806819252_t0001`（easy_18#172 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT15806819252t0001 : LpTerminalInfeasibleCertified "15806819252_t0001" :=
  ⟨Kepler.LP.T15806819252t0001.rowCore, Kepler.LP.T15806819252t0001.row_check⟩

/-- `15806819252_t0004`（easy_18#172 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT15806819252t0004 : LpTerminalInfeasibleCertified "15806819252_t0004" :=
  ⟨Kepler.LP.T15806819252t0004.rowCore, Kepler.LP.T15806819252t0004.row_check⟩

/-- `15806819252_t0006`（easy_18#172 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT15806819252t0006 : LpTerminalInfeasibleCertified "15806819252_t0006" :=
  ⟨Kepler.LP.T15806819252t0006.rowCore, Kepler.LP.T15806819252t0006.row_check⟩

/-- `15806819252_t0007`（easy_18#172 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT15806819252t0007 : LpTerminalInfeasibleCertified "15806819252_t0007" :=
  ⟨Kepler.LP.T15806819252t0007.rowCore, Kepler.LP.T15806819252t0007.row_check⟩

/-- `15806819252_t0009`（easy_18#172 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT15806819252t0009 : LpTerminalInfeasibleCertified "15806819252_t0009" :=
  ⟨Kepler.LP.T15806819252t0009.rowCore, Kepler.LP.T15806819252t0009.row_check⟩

/-- `201843411127_t0004`（easy_20#67 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT201843411127t0004 : LpTerminalInfeasibleCertified "201843411127_t0004" :=
  ⟨Kepler.LP.T201843411127t0004.rowCore, Kepler.LP.T201843411127t0004.row_check⟩

/-- `201843411127_t0007`（easy_20#67 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT201843411127t0007 : LpTerminalInfeasibleCertified "201843411127_t0007" :=
  ⟨Kepler.LP.T201843411127t0007.rowCore, Kepler.LP.T201843411127t0007.row_check⟩

/-- `201843411127_t0009`（easy_20#67 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT201843411127t0009 : LpTerminalInfeasibleCertified "201843411127_t0009" :=
  ⟨Kepler.LP.T201843411127t0009.rowCore, Kepler.LP.T201843411127t0009.row_check⟩

/-- `124346922881_t0002`（easy_23#838 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT124346922881t0002 : LpTerminalInfeasibleCertified "124346922881_t0002" :=
  ⟨Kepler.LP.T124346922881t0002.rowCore, Kepler.LP.T124346922881t0002.row_check⟩

/-- `124346922881_t0007`（easy_23#838 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT124346922881t0007 : LpTerminalInfeasibleCertified "124346922881_t0007" :=
  ⟨Kepler.LP.T124346922881t0007.rowCore, Kepler.LP.T124346922881t0007.row_check⟩

/-- `124346922881_t0010`（easy_23#838 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT124346922881t0010 : LpTerminalInfeasibleCertified "124346922881_t0010" :=
  ⟨Kepler.LP.T124346922881t0010.rowCore, Kepler.LP.T124346922881t0010.row_check⟩

/-- `206134563629_t0002`（easy_24#184 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT206134563629t0002 : LpTerminalInfeasibleCertified "206134563629_t0002" :=
  ⟨Kepler.LP.T206134563629t0002.rowCore, Kepler.LP.T206134563629t0002.row_check⟩

/-- `206134563629_t0007`（easy_24#184 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT206134563629t0007 : LpTerminalInfeasibleCertified "206134563629_t0007" :=
  ⟨Kepler.LP.T206134563629t0007.rowCore, Kepler.LP.T206134563629t0007.row_check⟩

/-- `206134563629_t0010`（easy_24#184 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT206134563629t0010 : LpTerminalInfeasibleCertified "206134563629_t0010" :=
  ⟨Kepler.LP.T206134563629t0010.rowCore, Kepler.LP.T206134563629t0010.row_check⟩

/-- `62586200165_t0001`（easy_5#21 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT62586200165t0001 : LpTerminalInfeasibleCertified "62586200165_t0001" :=
  ⟨Kepler.LP.T62586200165t0001.rowCore, Kepler.LP.T62586200165t0001.row_check⟩

/-- `62586200165_t0004`（easy_5#21 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT62586200165t0004 : LpTerminalInfeasibleCertified "62586200165_t0004" :=
  ⟨Kepler.LP.T62586200165t0004.rowCore, Kepler.LP.T62586200165t0004.row_check⟩

/-- `62586200165_t0006`（easy_5#21 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT62586200165t0006 : LpTerminalInfeasibleCertified "62586200165_t0006" :=
  ⟨Kepler.LP.T62586200165t0006.rowCore, Kepler.LP.T62586200165t0006.row_check⟩

/-- `62586200165_t0007`（easy_5#21 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT62586200165t0007 : LpTerminalInfeasibleCertified "62586200165_t0007" :=
  ⟨Kepler.LP.T62586200165t0007.rowCore, Kepler.LP.T62586200165t0007.row_check⟩

/-- `62586200165_t0009`（easy_5#21 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT62586200165t0009 : LpTerminalInfeasibleCertified "62586200165_t0009" :=
  ⟨Kepler.LP.T62586200165t0009.rowCore, Kepler.LP.T62586200165t0009.row_check⟩

/-- `161847242261_t0082`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t0082 : LpTerminalInfeasibleCertified "161847242261_t0082" :=
  ⟨Kepler.LP.T161847242261t0082.rowCore, Kepler.LP.T161847242261t0082.row_check⟩

/-- `161847242261_t0122`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t0122 : LpTerminalInfeasibleCertified "161847242261_t0122" :=
  ⟨Kepler.LP.T161847242261t0122.rowCore, Kepler.LP.T161847242261t0122.row_check⟩

/-- `161847242261_t0124`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t0124 : LpTerminalInfeasibleCertified "161847242261_t0124" :=
  ⟨Kepler.LP.T161847242261t0124.rowCore, Kepler.LP.T161847242261t0124.row_check⟩

/-- `161847242261_t0126`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t0126 : LpTerminalInfeasibleCertified "161847242261_t0126" :=
  ⟨Kepler.LP.T161847242261t0126.rowCore, Kepler.LP.T161847242261t0126.row_check⟩

/-- `161847242261_t0923`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t0923 : LpTerminalInfeasibleCertified "161847242261_t0923" :=
  ⟨Kepler.LP.T161847242261t0923.rowCore, Kepler.LP.T161847242261t0923.row_check⟩

/-- `161847242261_t0938`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t0938 : LpTerminalInfeasibleCertified "161847242261_t0938" :=
  ⟨Kepler.LP.T161847242261t0938.rowCore, Kepler.LP.T161847242261t0938.row_check⟩

/-- `161847242261_t0940`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t0940 : LpTerminalInfeasibleCertified "161847242261_t0940" :=
  ⟨Kepler.LP.T161847242261t0940.rowCore, Kepler.LP.T161847242261t0940.row_check⟩

/-- `161847242261_t0998`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t0998 : LpTerminalInfeasibleCertified "161847242261_t0998" :=
  ⟨Kepler.LP.T161847242261t0998.rowCore, Kepler.LP.T161847242261t0998.row_check⟩

/-- `161847242261_t1097`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1097 : LpTerminalInfeasibleCertified "161847242261_t1097" :=
  ⟨Kepler.LP.T161847242261t1097.rowCore, Kepler.LP.T161847242261t1097.row_check⟩

/-- `161847242261_t1120`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1120 : LpTerminalInfeasibleCertified "161847242261_t1120" :=
  ⟨Kepler.LP.T161847242261t1120.rowCore, Kepler.LP.T161847242261t1120.row_check⟩

/-- `161847242261_t1141`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1141 : LpTerminalInfeasibleCertified "161847242261_t1141" :=
  ⟨Kepler.LP.T161847242261t1141.rowCore, Kepler.LP.T161847242261t1141.row_check⟩

/-- `161847242261_t1176`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1176 : LpTerminalInfeasibleCertified "161847242261_t1176" :=
  ⟨Kepler.LP.T161847242261t1176.rowCore, Kepler.LP.T161847242261t1176.row_check⟩

/-- `161847242261_t1183`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1183 : LpTerminalInfeasibleCertified "161847242261_t1183" :=
  ⟨Kepler.LP.T161847242261t1183.rowCore, Kepler.LP.T161847242261t1183.row_check⟩

/-- `161847242261_t1187`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1187 : LpTerminalInfeasibleCertified "161847242261_t1187" :=
  ⟨Kepler.LP.T161847242261t1187.rowCore, Kepler.LP.T161847242261t1187.row_check⟩

/-- `161847242261_t1208`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1208 : LpTerminalInfeasibleCertified "161847242261_t1208" :=
  ⟨Kepler.LP.T161847242261t1208.rowCore, Kepler.LP.T161847242261t1208.row_check⟩

/-- `161847242261_t1210`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1210 : LpTerminalInfeasibleCertified "161847242261_t1210" :=
  ⟨Kepler.LP.T161847242261t1210.rowCore, Kepler.LP.T161847242261t1210.row_check⟩

/-- `161847242261_t1212`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1212 : LpTerminalInfeasibleCertified "161847242261_t1212" :=
  ⟨Kepler.LP.T161847242261t1212.rowCore, Kepler.LP.T161847242261t1212.row_check⟩

/-- `161847242261_t1225`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1225 : LpTerminalInfeasibleCertified "161847242261_t1225" :=
  ⟨Kepler.LP.T161847242261t1225.rowCore, Kepler.LP.T161847242261t1225.row_check⟩

/-- `161847242261_t1227`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1227 : LpTerminalInfeasibleCertified "161847242261_t1227" :=
  ⟨Kepler.LP.T161847242261t1227.rowCore, Kepler.LP.T161847242261t1227.row_check⟩

/-- `161847242261_t1324`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1324 : LpTerminalInfeasibleCertified "161847242261_t1324" :=
  ⟨Kepler.LP.T161847242261t1324.rowCore, Kepler.LP.T161847242261t1324.row_check⟩

/-- `161847242261_t1353`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1353 : LpTerminalInfeasibleCertified "161847242261_t1353" :=
  ⟨Kepler.LP.T161847242261t1353.rowCore, Kepler.LP.T161847242261t1353.row_check⟩

/-- `161847242261_t1355`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1355 : LpTerminalInfeasibleCertified "161847242261_t1355" :=
  ⟨Kepler.LP.T161847242261t1355.rowCore, Kepler.LP.T161847242261t1355.row_check⟩

/-- `161847242261_t1362`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1362 : LpTerminalInfeasibleCertified "161847242261_t1362" :=
  ⟨Kepler.LP.T161847242261t1362.rowCore, Kepler.LP.T161847242261t1362.row_check⟩

/-- `161847242261_t1369`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1369 : LpTerminalInfeasibleCertified "161847242261_t1369" :=
  ⟨Kepler.LP.T161847242261t1369.rowCore, Kepler.LP.T161847242261t1369.row_check⟩

/-- `161847242261_t1370`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1370 : LpTerminalInfeasibleCertified "161847242261_t1370" :=
  ⟨Kepler.LP.T161847242261t1370.rowCore, Kepler.LP.T161847242261t1370.row_check⟩

/-- `161847242261_t1372`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1372 : LpTerminalInfeasibleCertified "161847242261_t1372" :=
  ⟨Kepler.LP.T161847242261t1372.rowCore, Kepler.LP.T161847242261t1372.row_check⟩

/-- `161847242261_t1411`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1411 : LpTerminalInfeasibleCertified "161847242261_t1411" :=
  ⟨Kepler.LP.T161847242261t1411.rowCore, Kepler.LP.T161847242261t1411.row_check⟩

/-- `161847242261_t1413`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1413 : LpTerminalInfeasibleCertified "161847242261_t1413" :=
  ⟨Kepler.LP.T161847242261t1413.rowCore, Kepler.LP.T161847242261t1413.row_check⟩

/-- `161847242261_t1447`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1447 : LpTerminalInfeasibleCertified "161847242261_t1447" :=
  ⟨Kepler.LP.T161847242261t1447.rowCore, Kepler.LP.T161847242261t1447.row_check⟩

/-- `161847242261_t1604`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1604 : LpTerminalInfeasibleCertified "161847242261_t1604" :=
  ⟨Kepler.LP.T161847242261t1604.rowCore, Kepler.LP.T161847242261t1604.row_check⟩

/-- `161847242261_t1607`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1607 : LpTerminalInfeasibleCertified "161847242261_t1607" :=
  ⟨Kepler.LP.T161847242261t1607.rowCore, Kepler.LP.T161847242261t1607.row_check⟩

/-- `161847242261_t1613`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1613 : LpTerminalInfeasibleCertified "161847242261_t1613" :=
  ⟨Kepler.LP.T161847242261t1613.rowCore, Kepler.LP.T161847242261t1613.row_check⟩

/-- `161847242261_t1625`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1625 : LpTerminalInfeasibleCertified "161847242261_t1625" :=
  ⟨Kepler.LP.T161847242261t1625.rowCore, Kepler.LP.T161847242261t1625.row_check⟩

/-- `161847242261_t1627`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1627 : LpTerminalInfeasibleCertified "161847242261_t1627" :=
  ⟨Kepler.LP.T161847242261t1627.rowCore, Kepler.LP.T161847242261t1627.row_check⟩

/-- `161847242261_t1629`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1629 : LpTerminalInfeasibleCertified "161847242261_t1629" :=
  ⟨Kepler.LP.T161847242261t1629.rowCore, Kepler.LP.T161847242261t1629.row_check⟩

/-- `161847242261_t1635`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1635 : LpTerminalInfeasibleCertified "161847242261_t1635" :=
  ⟨Kepler.LP.T161847242261t1635.rowCore, Kepler.LP.T161847242261t1635.row_check⟩

/-- `161847242261_t1637`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1637 : LpTerminalInfeasibleCertified "161847242261_t1637" :=
  ⟨Kepler.LP.T161847242261t1637.rowCore, Kepler.LP.T161847242261t1637.row_check⟩

/-- `161847242261_t1677`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1677 : LpTerminalInfeasibleCertified "161847242261_t1677" :=
  ⟨Kepler.LP.T161847242261t1677.rowCore, Kepler.LP.T161847242261t1677.row_check⟩

/-- `161847242261_t1679`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1679 : LpTerminalInfeasibleCertified "161847242261_t1679" :=
  ⟨Kepler.LP.T161847242261t1679.rowCore, Kepler.LP.T161847242261t1679.row_check⟩

/-- `161847242261_t1686`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1686 : LpTerminalInfeasibleCertified "161847242261_t1686" :=
  ⟨Kepler.LP.T161847242261t1686.rowCore, Kepler.LP.T161847242261t1686.row_check⟩

/-- `161847242261_t1691`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1691 : LpTerminalInfeasibleCertified "161847242261_t1691" :=
  ⟨Kepler.LP.T161847242261t1691.rowCore, Kepler.LP.T161847242261t1691.row_check⟩

/-- `161847242261_t1693`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1693 : LpTerminalInfeasibleCertified "161847242261_t1693" :=
  ⟨Kepler.LP.T161847242261t1693.rowCore, Kepler.LP.T161847242261t1693.row_check⟩

/-- `161847242261_t1695`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1695 : LpTerminalInfeasibleCertified "161847242261_t1695" :=
  ⟨Kepler.LP.T161847242261t1695.rowCore, Kepler.LP.T161847242261t1695.row_check⟩

/-- `161847242261_t1700`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1700 : LpTerminalInfeasibleCertified "161847242261_t1700" :=
  ⟨Kepler.LP.T161847242261t1700.rowCore, Kepler.LP.T161847242261t1700.row_check⟩

/-- `161847242261_t1701`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1701 : LpTerminalInfeasibleCertified "161847242261_t1701" :=
  ⟨Kepler.LP.T161847242261t1701.rowCore, Kepler.LP.T161847242261t1701.row_check⟩

/-- `161847242261_t1703`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1703 : LpTerminalInfeasibleCertified "161847242261_t1703" :=
  ⟨Kepler.LP.T161847242261t1703.rowCore, Kepler.LP.T161847242261t1703.row_check⟩

/-- `161847242261_t1753`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1753 : LpTerminalInfeasibleCertified "161847242261_t1753" :=
  ⟨Kepler.LP.T161847242261t1753.rowCore, Kepler.LP.T161847242261t1753.row_check⟩

/-- `161847242261_t1755`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1755 : LpTerminalInfeasibleCertified "161847242261_t1755" :=
  ⟨Kepler.LP.T161847242261t1755.rowCore, Kepler.LP.T161847242261t1755.row_check⟩

/-- `161847242261_t1782`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1782 : LpTerminalInfeasibleCertified "161847242261_t1782" :=
  ⟨Kepler.LP.T161847242261t1782.rowCore, Kepler.LP.T161847242261t1782.row_check⟩

/-- `161847242261_t1824`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1824 : LpTerminalInfeasibleCertified "161847242261_t1824" :=
  ⟨Kepler.LP.T161847242261t1824.rowCore, Kepler.LP.T161847242261t1824.row_check⟩

/-- `161847242261_t1826`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1826 : LpTerminalInfeasibleCertified "161847242261_t1826" :=
  ⟨Kepler.LP.T161847242261t1826.rowCore, Kepler.LP.T161847242261t1826.row_check⟩

/-- `161847242261_t1827`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1827 : LpTerminalInfeasibleCertified "161847242261_t1827" :=
  ⟨Kepler.LP.T161847242261t1827.rowCore, Kepler.LP.T161847242261t1827.row_check⟩

/-- `161847242261_t1828`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1828 : LpTerminalInfeasibleCertified "161847242261_t1828" :=
  ⟨Kepler.LP.T161847242261t1828.rowCore, Kepler.LP.T161847242261t1828.row_check⟩

/-- `161847242261_t1829`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1829 : LpTerminalInfeasibleCertified "161847242261_t1829" :=
  ⟨Kepler.LP.T161847242261t1829.rowCore, Kepler.LP.T161847242261t1829.row_check⟩

/-- `161847242261_t1933`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1933 : LpTerminalInfeasibleCertified "161847242261_t1933" :=
  ⟨Kepler.LP.T161847242261t1933.rowCore, Kepler.LP.T161847242261t1933.row_check⟩

/-- `161847242261_t1934`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1934 : LpTerminalInfeasibleCertified "161847242261_t1934" :=
  ⟨Kepler.LP.T161847242261t1934.rowCore, Kepler.LP.T161847242261t1934.row_check⟩

/-- `161847242261_t1939`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1939 : LpTerminalInfeasibleCertified "161847242261_t1939" :=
  ⟨Kepler.LP.T161847242261t1939.rowCore, Kepler.LP.T161847242261t1939.row_check⟩

/-- `161847242261_t1965`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1965 : LpTerminalInfeasibleCertified "161847242261_t1965" :=
  ⟨Kepler.LP.T161847242261t1965.rowCore, Kepler.LP.T161847242261t1965.row_check⟩

/-- `161847242261_t1972`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1972 : LpTerminalInfeasibleCertified "161847242261_t1972" :=
  ⟨Kepler.LP.T161847242261t1972.rowCore, Kepler.LP.T161847242261t1972.row_check⟩

/-- `161847242261_t1974`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t1974 : LpTerminalInfeasibleCertified "161847242261_t1974" :=
  ⟨Kepler.LP.T161847242261t1974.rowCore, Kepler.LP.T161847242261t1974.row_check⟩

/-- `161847242261_t2017`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2017 : LpTerminalInfeasibleCertified "161847242261_t2017" :=
  ⟨Kepler.LP.T161847242261t2017.rowCore, Kepler.LP.T161847242261t2017.row_check⟩

/-- `161847242261_t2019`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2019 : LpTerminalInfeasibleCertified "161847242261_t2019" :=
  ⟨Kepler.LP.T161847242261t2019.rowCore, Kepler.LP.T161847242261t2019.row_check⟩

/-- `161847242261_t2049`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2049 : LpTerminalInfeasibleCertified "161847242261_t2049" :=
  ⟨Kepler.LP.T161847242261t2049.rowCore, Kepler.LP.T161847242261t2049.row_check⟩

/-- `161847242261_t2063`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2063 : LpTerminalInfeasibleCertified "161847242261_t2063" :=
  ⟨Kepler.LP.T161847242261t2063.rowCore, Kepler.LP.T161847242261t2063.row_check⟩

/-- `161847242261_t2064`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2064 : LpTerminalInfeasibleCertified "161847242261_t2064" :=
  ⟨Kepler.LP.T161847242261t2064.rowCore, Kepler.LP.T161847242261t2064.row_check⟩

/-- `161847242261_t2068`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2068 : LpTerminalInfeasibleCertified "161847242261_t2068" :=
  ⟨Kepler.LP.T161847242261t2068.rowCore, Kepler.LP.T161847242261t2068.row_check⟩

/-- `161847242261_t2070`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2070 : LpTerminalInfeasibleCertified "161847242261_t2070" :=
  ⟨Kepler.LP.T161847242261t2070.rowCore, Kepler.LP.T161847242261t2070.row_check⟩

/-- `161847242261_t2102`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2102 : LpTerminalInfeasibleCertified "161847242261_t2102" :=
  ⟨Kepler.LP.T161847242261t2102.rowCore, Kepler.LP.T161847242261t2102.row_check⟩

/-- `161847242261_t2104`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2104 : LpTerminalInfeasibleCertified "161847242261_t2104" :=
  ⟨Kepler.LP.T161847242261t2104.rowCore, Kepler.LP.T161847242261t2104.row_check⟩

/-- `161847242261_t2105`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2105 : LpTerminalInfeasibleCertified "161847242261_t2105" :=
  ⟨Kepler.LP.T161847242261t2105.rowCore, Kepler.LP.T161847242261t2105.row_check⟩

/-- `161847242261_t2107`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2107 : LpTerminalInfeasibleCertified "161847242261_t2107" :=
  ⟨Kepler.LP.T161847242261t2107.rowCore, Kepler.LP.T161847242261t2107.row_check⟩

/-- `161847242261_t2138`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2138 : LpTerminalInfeasibleCertified "161847242261_t2138" :=
  ⟨Kepler.LP.T161847242261t2138.rowCore, Kepler.LP.T161847242261t2138.row_check⟩

/-- `161847242261_t2220`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2220 : LpTerminalInfeasibleCertified "161847242261_t2220" :=
  ⟨Kepler.LP.T161847242261t2220.rowCore, Kepler.LP.T161847242261t2220.row_check⟩

/-- `161847242261_t2227`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2227 : LpTerminalInfeasibleCertified "161847242261_t2227" :=
  ⟨Kepler.LP.T161847242261t2227.rowCore, Kepler.LP.T161847242261t2227.row_check⟩

/-- `161847242261_t2232`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2232 : LpTerminalInfeasibleCertified "161847242261_t2232" :=
  ⟨Kepler.LP.T161847242261t2232.rowCore, Kepler.LP.T161847242261t2232.row_check⟩

/-- `161847242261_t2236`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2236 : LpTerminalInfeasibleCertified "161847242261_t2236" :=
  ⟨Kepler.LP.T161847242261t2236.rowCore, Kepler.LP.T161847242261t2236.row_check⟩

/-- `161847242261_t2238`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2238 : LpTerminalInfeasibleCertified "161847242261_t2238" :=
  ⟨Kepler.LP.T161847242261t2238.rowCore, Kepler.LP.T161847242261t2238.row_check⟩

/-- `161847242261_t2247`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2247 : LpTerminalInfeasibleCertified "161847242261_t2247" :=
  ⟨Kepler.LP.T161847242261t2247.rowCore, Kepler.LP.T161847242261t2247.row_check⟩

/-- `161847242261_t2250`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2250 : LpTerminalInfeasibleCertified "161847242261_t2250" :=
  ⟨Kepler.LP.T161847242261t2250.rowCore, Kepler.LP.T161847242261t2250.row_check⟩

/-- `161847242261_t2252`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2252 : LpTerminalInfeasibleCertified "161847242261_t2252" :=
  ⟨Kepler.LP.T161847242261t2252.rowCore, Kepler.LP.T161847242261t2252.row_check⟩

/-- `161847242261_t2261`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2261 : LpTerminalInfeasibleCertified "161847242261_t2261" :=
  ⟨Kepler.LP.T161847242261t2261.rowCore, Kepler.LP.T161847242261t2261.row_check⟩

/-- `161847242261_t2265`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2265 : LpTerminalInfeasibleCertified "161847242261_t2265" :=
  ⟨Kepler.LP.T161847242261t2265.rowCore, Kepler.LP.T161847242261t2265.row_check⟩

/-- `161847242261_t2267`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2267 : LpTerminalInfeasibleCertified "161847242261_t2267" :=
  ⟨Kepler.LP.T161847242261t2267.rowCore, Kepler.LP.T161847242261t2267.row_check⟩

/-- `161847242261_t2275`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2275 : LpTerminalInfeasibleCertified "161847242261_t2275" :=
  ⟨Kepler.LP.T161847242261t2275.rowCore, Kepler.LP.T161847242261t2275.row_check⟩

/-- `161847242261_t2278`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2278 : LpTerminalInfeasibleCertified "161847242261_t2278" :=
  ⟨Kepler.LP.T161847242261t2278.rowCore, Kepler.LP.T161847242261t2278.row_check⟩

/-- `161847242261_t2426`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2426 : LpTerminalInfeasibleCertified "161847242261_t2426" :=
  ⟨Kepler.LP.T161847242261t2426.rowCore, Kepler.LP.T161847242261t2426.row_check⟩

/-- `161847242261_t2429`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2429 : LpTerminalInfeasibleCertified "161847242261_t2429" :=
  ⟨Kepler.LP.T161847242261t2429.rowCore, Kepler.LP.T161847242261t2429.row_check⟩

/-- `161847242261_t2435`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2435 : LpTerminalInfeasibleCertified "161847242261_t2435" :=
  ⟨Kepler.LP.T161847242261t2435.rowCore, Kepler.LP.T161847242261t2435.row_check⟩

/-- `161847242261_t2447`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2447 : LpTerminalInfeasibleCertified "161847242261_t2447" :=
  ⟨Kepler.LP.T161847242261t2447.rowCore, Kepler.LP.T161847242261t2447.row_check⟩

/-- `161847242261_t2449`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2449 : LpTerminalInfeasibleCertified "161847242261_t2449" :=
  ⟨Kepler.LP.T161847242261t2449.rowCore, Kepler.LP.T161847242261t2449.row_check⟩

/-- `161847242261_t2451`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2451 : LpTerminalInfeasibleCertified "161847242261_t2451" :=
  ⟨Kepler.LP.T161847242261t2451.rowCore, Kepler.LP.T161847242261t2451.row_check⟩

/-- `161847242261_t2457`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2457 : LpTerminalInfeasibleCertified "161847242261_t2457" :=
  ⟨Kepler.LP.T161847242261t2457.rowCore, Kepler.LP.T161847242261t2457.row_check⟩

/-- `161847242261_t2460`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2460 : LpTerminalInfeasibleCertified "161847242261_t2460" :=
  ⟨Kepler.LP.T161847242261t2460.rowCore, Kepler.LP.T161847242261t2460.row_check⟩

/-- `161847242261_t2501`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2501 : LpTerminalInfeasibleCertified "161847242261_t2501" :=
  ⟨Kepler.LP.T161847242261t2501.rowCore, Kepler.LP.T161847242261t2501.row_check⟩

/-- `161847242261_t2508`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2508 : LpTerminalInfeasibleCertified "161847242261_t2508" :=
  ⟨Kepler.LP.T161847242261t2508.rowCore, Kepler.LP.T161847242261t2508.row_check⟩

/-- `161847242261_t2510`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2510 : LpTerminalInfeasibleCertified "161847242261_t2510" :=
  ⟨Kepler.LP.T161847242261t2510.rowCore, Kepler.LP.T161847242261t2510.row_check⟩

/-- `161847242261_t2515`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2515 : LpTerminalInfeasibleCertified "161847242261_t2515" :=
  ⟨Kepler.LP.T161847242261t2515.rowCore, Kepler.LP.T161847242261t2515.row_check⟩

/-- `161847242261_t2516`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2516 : LpTerminalInfeasibleCertified "161847242261_t2516" :=
  ⟨Kepler.LP.T161847242261t2516.rowCore, Kepler.LP.T161847242261t2516.row_check⟩

/-- `161847242261_t2518`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2518 : LpTerminalInfeasibleCertified "161847242261_t2518" :=
  ⟨Kepler.LP.T161847242261t2518.rowCore, Kepler.LP.T161847242261t2518.row_check⟩

/-- `161847242261_t2520`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2520 : LpTerminalInfeasibleCertified "161847242261_t2520" :=
  ⟨Kepler.LP.T161847242261t2520.rowCore, Kepler.LP.T161847242261t2520.row_check⟩

/-- `161847242261_t2526`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2526 : LpTerminalInfeasibleCertified "161847242261_t2526" :=
  ⟨Kepler.LP.T161847242261t2526.rowCore, Kepler.LP.T161847242261t2526.row_check⟩

/-- `161847242261_t2528`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2528 : LpTerminalInfeasibleCertified "161847242261_t2528" :=
  ⟨Kepler.LP.T161847242261t2528.rowCore, Kepler.LP.T161847242261t2528.row_check⟩

/-- `161847242261_t2573`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2573 : LpTerminalInfeasibleCertified "161847242261_t2573" :=
  ⟨Kepler.LP.T161847242261t2573.rowCore, Kepler.LP.T161847242261t2573.row_check⟩

/-- `161847242261_t2574`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2574 : LpTerminalInfeasibleCertified "161847242261_t2574" :=
  ⟨Kepler.LP.T161847242261t2574.rowCore, Kepler.LP.T161847242261t2574.row_check⟩

/-- `161847242261_t2576`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2576 : LpTerminalInfeasibleCertified "161847242261_t2576" :=
  ⟨Kepler.LP.T161847242261t2576.rowCore, Kepler.LP.T161847242261t2576.row_check⟩

/-- `161847242261_t2580`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2580 : LpTerminalInfeasibleCertified "161847242261_t2580" :=
  ⟨Kepler.LP.T161847242261t2580.rowCore, Kepler.LP.T161847242261t2580.row_check⟩

/-- `161847242261_t2583`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2583 : LpTerminalInfeasibleCertified "161847242261_t2583" :=
  ⟨Kepler.LP.T161847242261t2583.rowCore, Kepler.LP.T161847242261t2583.row_check⟩

/-- `161847242261_t2585`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2585 : LpTerminalInfeasibleCertified "161847242261_t2585" :=
  ⟨Kepler.LP.T161847242261t2585.rowCore, Kepler.LP.T161847242261t2585.row_check⟩

/-- `161847242261_t2671`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2671 : LpTerminalInfeasibleCertified "161847242261_t2671" :=
  ⟨Kepler.LP.T161847242261t2671.rowCore, Kepler.LP.T161847242261t2671.row_check⟩

/-- `161847242261_t2672`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2672 : LpTerminalInfeasibleCertified "161847242261_t2672" :=
  ⟨Kepler.LP.T161847242261t2672.rowCore, Kepler.LP.T161847242261t2672.row_check⟩

/-- `161847242261_t2674`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2674 : LpTerminalInfeasibleCertified "161847242261_t2674" :=
  ⟨Kepler.LP.T161847242261t2674.rowCore, Kepler.LP.T161847242261t2674.row_check⟩

/-- `161847242261_t2675`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2675 : LpTerminalInfeasibleCertified "161847242261_t2675" :=
  ⟨Kepler.LP.T161847242261t2675.rowCore, Kepler.LP.T161847242261t2675.row_check⟩

/-- `161847242261_t2677`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2677 : LpTerminalInfeasibleCertified "161847242261_t2677" :=
  ⟨Kepler.LP.T161847242261t2677.rowCore, Kepler.LP.T161847242261t2677.row_check⟩

/-- `161847242261_t2692`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2692 : LpTerminalInfeasibleCertified "161847242261_t2692" :=
  ⟨Kepler.LP.T161847242261t2692.rowCore, Kepler.LP.T161847242261t2692.row_check⟩

/-- `161847242261_t2708`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2708 : LpTerminalInfeasibleCertified "161847242261_t2708" :=
  ⟨Kepler.LP.T161847242261t2708.rowCore, Kepler.LP.T161847242261t2708.row_check⟩

/-- `161847242261_t2710`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2710 : LpTerminalInfeasibleCertified "161847242261_t2710" :=
  ⟨Kepler.LP.T161847242261t2710.rowCore, Kepler.LP.T161847242261t2710.row_check⟩

/-- `161847242261_t2718`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2718 : LpTerminalInfeasibleCertified "161847242261_t2718" :=
  ⟨Kepler.LP.T161847242261t2718.rowCore, Kepler.LP.T161847242261t2718.row_check⟩

/-- `161847242261_t2805`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2805 : LpTerminalInfeasibleCertified "161847242261_t2805" :=
  ⟨Kepler.LP.T161847242261t2805.rowCore, Kepler.LP.T161847242261t2805.row_check⟩

/-- `161847242261_t2810`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2810 : LpTerminalInfeasibleCertified "161847242261_t2810" :=
  ⟨Kepler.LP.T161847242261t2810.rowCore, Kepler.LP.T161847242261t2810.row_check⟩

/-- `161847242261_t2814`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2814 : LpTerminalInfeasibleCertified "161847242261_t2814" :=
  ⟨Kepler.LP.T161847242261t2814.rowCore, Kepler.LP.T161847242261t2814.row_check⟩

/-- `161847242261_t2818`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2818 : LpTerminalInfeasibleCertified "161847242261_t2818" :=
  ⟨Kepler.LP.T161847242261t2818.rowCore, Kepler.LP.T161847242261t2818.row_check⟩

/-- `161847242261_t2822`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2822 : LpTerminalInfeasibleCertified "161847242261_t2822" :=
  ⟨Kepler.LP.T161847242261t2822.rowCore, Kepler.LP.T161847242261t2822.row_check⟩

/-- `161847242261_t2824`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2824 : LpTerminalInfeasibleCertified "161847242261_t2824" :=
  ⟨Kepler.LP.T161847242261t2824.rowCore, Kepler.LP.T161847242261t2824.row_check⟩

/-- `161847242261_t2833`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2833 : LpTerminalInfeasibleCertified "161847242261_t2833" :=
  ⟨Kepler.LP.T161847242261t2833.rowCore, Kepler.LP.T161847242261t2833.row_check⟩

/-- `161847242261_t2838`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2838 : LpTerminalInfeasibleCertified "161847242261_t2838" :=
  ⟨Kepler.LP.T161847242261t2838.rowCore, Kepler.LP.T161847242261t2838.row_check⟩

/-- `161847242261_t2846`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2846 : LpTerminalInfeasibleCertified "161847242261_t2846" :=
  ⟨Kepler.LP.T161847242261t2846.rowCore, Kepler.LP.T161847242261t2846.row_check⟩

/-- `161847242261_t2852`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2852 : LpTerminalInfeasibleCertified "161847242261_t2852" :=
  ⟨Kepler.LP.T161847242261t2852.rowCore, Kepler.LP.T161847242261t2852.row_check⟩

/-- `161847242261_t2859`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2859 : LpTerminalInfeasibleCertified "161847242261_t2859" :=
  ⟨Kepler.LP.T161847242261t2859.rowCore, Kepler.LP.T161847242261t2859.row_check⟩

/-- `161847242261_t2862`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2862 : LpTerminalInfeasibleCertified "161847242261_t2862" :=
  ⟨Kepler.LP.T161847242261t2862.rowCore, Kepler.LP.T161847242261t2862.row_check⟩

/-- `161847242261_t2868`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2868 : LpTerminalInfeasibleCertified "161847242261_t2868" :=
  ⟨Kepler.LP.T161847242261t2868.rowCore, Kepler.LP.T161847242261t2868.row_check⟩

/-- `161847242261_t2870`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2870 : LpTerminalInfeasibleCertified "161847242261_t2870" :=
  ⟨Kepler.LP.T161847242261t2870.rowCore, Kepler.LP.T161847242261t2870.row_check⟩

/-- `161847242261_t2878`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2878 : LpTerminalInfeasibleCertified "161847242261_t2878" :=
  ⟨Kepler.LP.T161847242261t2878.rowCore, Kepler.LP.T161847242261t2878.row_check⟩

/-- `161847242261_t2881`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2881 : LpTerminalInfeasibleCertified "161847242261_t2881" :=
  ⟨Kepler.LP.T161847242261t2881.rowCore, Kepler.LP.T161847242261t2881.row_check⟩

/-- `161847242261_t2893`（hard_1#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT161847242261t2893 : LpTerminalInfeasibleCertified "161847242261_t2893" :=
  ⟨Kepler.LP.T161847242261t2893.rowCore, Kepler.LP.T161847242261t2893.row_check⟩

/-- `179189825656_t0000`（hard_10#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT179189825656t0000 : LpTerminalInfeasibleCertified "179189825656_t0000" :=
  ⟨Kepler.LP.T179189825656t0000.rowCore, Kepler.LP.T179189825656t0000.row_check⟩

/-- `215863975889_t0019`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0019 : LpTerminalInfeasibleCertified "215863975889_t0019" :=
  ⟨Kepler.LP.T215863975889t0019.rowCore, Kepler.LP.T215863975889t0019.row_check⟩

/-- `215863975889_t0083`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0083 : LpTerminalInfeasibleCertified "215863975889_t0083" :=
  ⟨Kepler.LP.T215863975889t0083.rowCore, Kepler.LP.T215863975889t0083.row_check⟩

/-- `215863975889_t0100`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0100 : LpTerminalInfeasibleCertified "215863975889_t0100" :=
  ⟨Kepler.LP.T215863975889t0100.rowCore, Kepler.LP.T215863975889t0100.row_check⟩

/-- `215863975889_t0102`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0102 : LpTerminalInfeasibleCertified "215863975889_t0102" :=
  ⟨Kepler.LP.T215863975889t0102.rowCore, Kepler.LP.T215863975889t0102.row_check⟩

/-- `215863975889_t0104`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0104 : LpTerminalInfeasibleCertified "215863975889_t0104" :=
  ⟨Kepler.LP.T215863975889t0104.rowCore, Kepler.LP.T215863975889t0104.row_check⟩

/-- `215863975889_t0115`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0115 : LpTerminalInfeasibleCertified "215863975889_t0115" :=
  ⟨Kepler.LP.T215863975889t0115.rowCore, Kepler.LP.T215863975889t0115.row_check⟩

/-- `215863975889_t0134`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0134 : LpTerminalInfeasibleCertified "215863975889_t0134" :=
  ⟨Kepler.LP.T215863975889t0134.rowCore, Kepler.LP.T215863975889t0134.row_check⟩

/-- `215863975889_t0136`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0136 : LpTerminalInfeasibleCertified "215863975889_t0136" :=
  ⟨Kepler.LP.T215863975889t0136.rowCore, Kepler.LP.T215863975889t0136.row_check⟩

/-- `215863975889_t0149`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0149 : LpTerminalInfeasibleCertified "215863975889_t0149" :=
  ⟨Kepler.LP.T215863975889t0149.rowCore, Kepler.LP.T215863975889t0149.row_check⟩

/-- `215863975889_t0175`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0175 : LpTerminalInfeasibleCertified "215863975889_t0175" :=
  ⟨Kepler.LP.T215863975889t0175.rowCore, Kepler.LP.T215863975889t0175.row_check⟩

/-- `215863975889_t0178`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0178 : LpTerminalInfeasibleCertified "215863975889_t0178" :=
  ⟨Kepler.LP.T215863975889t0178.rowCore, Kepler.LP.T215863975889t0178.row_check⟩

/-- `215863975889_t0180`（hard_12#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT215863975889t0180 : LpTerminalInfeasibleCertified "215863975889_t0180" :=
  ⟨Kepler.LP.T215863975889t0180.rowCore, Kepler.LP.T215863975889t0180.row_check⟩

/-- `223336279535_t2552`（hard_7#0 · infeasible 支）— 闭合：Farkas 重跑产物模块转发（列主序证书 + 列→行桥 LPFarkasCM；gen_lp_skeleton --emit-closure 落账）。 -/
theorem lpT223336279535t2552 : LpTerminalInfeasibleCertified "223336279535_t2552" :=
  ⟨Kepler.LP.T223336279535t2552.rowCore, Kepler.LP.T223336279535t2552.row_check⟩

/-- 本片量化装配（真实推导，逐叶具名分发；189 条）。 -/
theorem lpAllInfeas00 : AllLpTerminalInfeasibleCertified lpInfeasIds00 := by
  intro id hid
  simp only [lpInfeasIds00, List.mem_cons] at hid
  rcases hid with rfl | hid
  · exact lpT234511714565t0000
  rcases hid with rfl | hid
  · exact lpT50329387098t0004
  rcases hid with rfl | hid
  · exact lpT50329387098t0007
  rcases hid with rfl | hid
  · exact lpT50329387098t0009
  rcases hid with rfl | hid
  · exact lpT50329387098t0018
  rcases hid with rfl | hid
  · exact lpT50329387098t0021
  rcases hid with rfl | hid
  · exact lpT50329387098t0023
  rcases hid with rfl | hid
  · exact lpT250379175175t0014
  rcases hid with rfl | hid
  · exact lpT250379175175t0017
  rcases hid with rfl | hid
  · exact lpT250379175175t0019
  rcases hid with rfl | hid
  · exact lpT195512614336t0024
  rcases hid with rfl | hid
  · exact lpT195512614336t0027
  rcases hid with rfl | hid
  · exact lpT195512614336t0029
  rcases hid with rfl | hid
  · exact lpT216661698775t0004
  rcases hid with rfl | hid
  · exact lpT216661698775t0009
  rcases hid with rfl | hid
  · exact lpT216661698775t0012
  rcases hid with rfl | hid
  · exact lpT216661698775t0014
  rcases hid with rfl | hid
  · exact lpT216661698775t0017
  rcases hid with rfl | hid
  · exact lpT216661698775t0019
  rcases hid with rfl | hid
  · exact lpT121582585038t0004
  rcases hid with rfl | hid
  · exact lpT121582585038t0007
  rcases hid with rfl | hid
  · exact lpT121582585038t0009
  rcases hid with rfl | hid
  · exact lpT15806819252t0001
  rcases hid with rfl | hid
  · exact lpT15806819252t0004
  rcases hid with rfl | hid
  · exact lpT15806819252t0006
  rcases hid with rfl | hid
  · exact lpT15806819252t0007
  rcases hid with rfl | hid
  · exact lpT15806819252t0009
  rcases hid with rfl | hid
  · exact lpT201843411127t0004
  rcases hid with rfl | hid
  · exact lpT201843411127t0007
  rcases hid with rfl | hid
  · exact lpT201843411127t0009
  rcases hid with rfl | hid
  · exact lpT124346922881t0002
  rcases hid with rfl | hid
  · exact lpT124346922881t0007
  rcases hid with rfl | hid
  · exact lpT124346922881t0010
  rcases hid with rfl | hid
  · exact lpT206134563629t0002
  rcases hid with rfl | hid
  · exact lpT206134563629t0007
  rcases hid with rfl | hid
  · exact lpT206134563629t0010
  rcases hid with rfl | hid
  · exact lpT62586200165t0001
  rcases hid with rfl | hid
  · exact lpT62586200165t0004
  rcases hid with rfl | hid
  · exact lpT62586200165t0006
  rcases hid with rfl | hid
  · exact lpT62586200165t0007
  rcases hid with rfl | hid
  · exact lpT62586200165t0009
  rcases hid with rfl | hid
  · exact lpT161847242261t0082
  rcases hid with rfl | hid
  · exact lpT161847242261t0122
  rcases hid with rfl | hid
  · exact lpT161847242261t0124
  rcases hid with rfl | hid
  · exact lpT161847242261t0126
  rcases hid with rfl | hid
  · exact lpT161847242261t0923
  rcases hid with rfl | hid
  · exact lpT161847242261t0938
  rcases hid with rfl | hid
  · exact lpT161847242261t0940
  rcases hid with rfl | hid
  · exact lpT161847242261t0998
  rcases hid with rfl | hid
  · exact lpT161847242261t1097
  rcases hid with rfl | hid
  · exact lpT161847242261t1120
  rcases hid with rfl | hid
  · exact lpT161847242261t1141
  rcases hid with rfl | hid
  · exact lpT161847242261t1176
  rcases hid with rfl | hid
  · exact lpT161847242261t1183
  rcases hid with rfl | hid
  · exact lpT161847242261t1187
  rcases hid with rfl | hid
  · exact lpT161847242261t1208
  rcases hid with rfl | hid
  · exact lpT161847242261t1210
  rcases hid with rfl | hid
  · exact lpT161847242261t1212
  rcases hid with rfl | hid
  · exact lpT161847242261t1225
  rcases hid with rfl | hid
  · exact lpT161847242261t1227
  rcases hid with rfl | hid
  · exact lpT161847242261t1324
  rcases hid with rfl | hid
  · exact lpT161847242261t1353
  rcases hid with rfl | hid
  · exact lpT161847242261t1355
  rcases hid with rfl | hid
  · exact lpT161847242261t1362
  rcases hid with rfl | hid
  · exact lpT161847242261t1369
  rcases hid with rfl | hid
  · exact lpT161847242261t1370
  rcases hid with rfl | hid
  · exact lpT161847242261t1372
  rcases hid with rfl | hid
  · exact lpT161847242261t1411
  rcases hid with rfl | hid
  · exact lpT161847242261t1413
  rcases hid with rfl | hid
  · exact lpT161847242261t1447
  rcases hid with rfl | hid
  · exact lpT161847242261t1604
  rcases hid with rfl | hid
  · exact lpT161847242261t1607
  rcases hid with rfl | hid
  · exact lpT161847242261t1613
  rcases hid with rfl | hid
  · exact lpT161847242261t1625
  rcases hid with rfl | hid
  · exact lpT161847242261t1627
  rcases hid with rfl | hid
  · exact lpT161847242261t1629
  rcases hid with rfl | hid
  · exact lpT161847242261t1635
  rcases hid with rfl | hid
  · exact lpT161847242261t1637
  rcases hid with rfl | hid
  · exact lpT161847242261t1677
  rcases hid with rfl | hid
  · exact lpT161847242261t1679
  rcases hid with rfl | hid
  · exact lpT161847242261t1686
  rcases hid with rfl | hid
  · exact lpT161847242261t1691
  rcases hid with rfl | hid
  · exact lpT161847242261t1693
  rcases hid with rfl | hid
  · exact lpT161847242261t1695
  rcases hid with rfl | hid
  · exact lpT161847242261t1700
  rcases hid with rfl | hid
  · exact lpT161847242261t1701
  rcases hid with rfl | hid
  · exact lpT161847242261t1703
  rcases hid with rfl | hid
  · exact lpT161847242261t1753
  rcases hid with rfl | hid
  · exact lpT161847242261t1755
  rcases hid with rfl | hid
  · exact lpT161847242261t1782
  rcases hid with rfl | hid
  · exact lpT161847242261t1824
  rcases hid with rfl | hid
  · exact lpT161847242261t1826
  rcases hid with rfl | hid
  · exact lpT161847242261t1827
  rcases hid with rfl | hid
  · exact lpT161847242261t1828
  rcases hid with rfl | hid
  · exact lpT161847242261t1829
  rcases hid with rfl | hid
  · exact lpT161847242261t1933
  rcases hid with rfl | hid
  · exact lpT161847242261t1934
  rcases hid with rfl | hid
  · exact lpT161847242261t1939
  rcases hid with rfl | hid
  · exact lpT161847242261t1965
  rcases hid with rfl | hid
  · exact lpT161847242261t1972
  rcases hid with rfl | hid
  · exact lpT161847242261t1974
  rcases hid with rfl | hid
  · exact lpT161847242261t2017
  rcases hid with rfl | hid
  · exact lpT161847242261t2019
  rcases hid with rfl | hid
  · exact lpT161847242261t2049
  rcases hid with rfl | hid
  · exact lpT161847242261t2063
  rcases hid with rfl | hid
  · exact lpT161847242261t2064
  rcases hid with rfl | hid
  · exact lpT161847242261t2068
  rcases hid with rfl | hid
  · exact lpT161847242261t2070
  rcases hid with rfl | hid
  · exact lpT161847242261t2102
  rcases hid with rfl | hid
  · exact lpT161847242261t2104
  rcases hid with rfl | hid
  · exact lpT161847242261t2105
  rcases hid with rfl | hid
  · exact lpT161847242261t2107
  rcases hid with rfl | hid
  · exact lpT161847242261t2138
  rcases hid with rfl | hid
  · exact lpT161847242261t2220
  rcases hid with rfl | hid
  · exact lpT161847242261t2227
  rcases hid with rfl | hid
  · exact lpT161847242261t2232
  rcases hid with rfl | hid
  · exact lpT161847242261t2236
  rcases hid with rfl | hid
  · exact lpT161847242261t2238
  rcases hid with rfl | hid
  · exact lpT161847242261t2247
  rcases hid with rfl | hid
  · exact lpT161847242261t2250
  rcases hid with rfl | hid
  · exact lpT161847242261t2252
  rcases hid with rfl | hid
  · exact lpT161847242261t2261
  rcases hid with rfl | hid
  · exact lpT161847242261t2265
  rcases hid with rfl | hid
  · exact lpT161847242261t2267
  rcases hid with rfl | hid
  · exact lpT161847242261t2275
  rcases hid with rfl | hid
  · exact lpT161847242261t2278
  rcases hid with rfl | hid
  · exact lpT161847242261t2426
  rcases hid with rfl | hid
  · exact lpT161847242261t2429
  rcases hid with rfl | hid
  · exact lpT161847242261t2435
  rcases hid with rfl | hid
  · exact lpT161847242261t2447
  rcases hid with rfl | hid
  · exact lpT161847242261t2449
  rcases hid with rfl | hid
  · exact lpT161847242261t2451
  rcases hid with rfl | hid
  · exact lpT161847242261t2457
  rcases hid with rfl | hid
  · exact lpT161847242261t2460
  rcases hid with rfl | hid
  · exact lpT161847242261t2501
  rcases hid with rfl | hid
  · exact lpT161847242261t2508
  rcases hid with rfl | hid
  · exact lpT161847242261t2510
  rcases hid with rfl | hid
  · exact lpT161847242261t2515
  rcases hid with rfl | hid
  · exact lpT161847242261t2516
  rcases hid with rfl | hid
  · exact lpT161847242261t2518
  rcases hid with rfl | hid
  · exact lpT161847242261t2520
  rcases hid with rfl | hid
  · exact lpT161847242261t2526
  rcases hid with rfl | hid
  · exact lpT161847242261t2528
  rcases hid with rfl | hid
  · exact lpT161847242261t2573
  rcases hid with rfl | hid
  · exact lpT161847242261t2574
  rcases hid with rfl | hid
  · exact lpT161847242261t2576
  rcases hid with rfl | hid
  · exact lpT161847242261t2580
  rcases hid with rfl | hid
  · exact lpT161847242261t2583
  rcases hid with rfl | hid
  · exact lpT161847242261t2585
  rcases hid with rfl | hid
  · exact lpT161847242261t2671
  rcases hid with rfl | hid
  · exact lpT161847242261t2672
  rcases hid with rfl | hid
  · exact lpT161847242261t2674
  rcases hid with rfl | hid
  · exact lpT161847242261t2675
  rcases hid with rfl | hid
  · exact lpT161847242261t2677
  rcases hid with rfl | hid
  · exact lpT161847242261t2692
  rcases hid with rfl | hid
  · exact lpT161847242261t2708
  rcases hid with rfl | hid
  · exact lpT161847242261t2710
  rcases hid with rfl | hid
  · exact lpT161847242261t2718
  rcases hid with rfl | hid
  · exact lpT161847242261t2805
  rcases hid with rfl | hid
  · exact lpT161847242261t2810
  rcases hid with rfl | hid
  · exact lpT161847242261t2814
  rcases hid with rfl | hid
  · exact lpT161847242261t2818
  rcases hid with rfl | hid
  · exact lpT161847242261t2822
  rcases hid with rfl | hid
  · exact lpT161847242261t2824
  rcases hid with rfl | hid
  · exact lpT161847242261t2833
  rcases hid with rfl | hid
  · exact lpT161847242261t2838
  rcases hid with rfl | hid
  · exact lpT161847242261t2846
  rcases hid with rfl | hid
  · exact lpT161847242261t2852
  rcases hid with rfl | hid
  · exact lpT161847242261t2859
  rcases hid with rfl | hid
  · exact lpT161847242261t2862
  rcases hid with rfl | hid
  · exact lpT161847242261t2868
  rcases hid with rfl | hid
  · exact lpT161847242261t2870
  rcases hid with rfl | hid
  · exact lpT161847242261t2878
  rcases hid with rfl | hid
  · exact lpT161847242261t2881
  rcases hid with rfl | hid
  · exact lpT161847242261t2893
  rcases hid with rfl | hid
  · exact lpT179189825656t0000
  rcases hid with rfl | hid
  · exact lpT215863975889t0019
  rcases hid with rfl | hid
  · exact lpT215863975889t0083
  rcases hid with rfl | hid
  · exact lpT215863975889t0100
  rcases hid with rfl | hid
  · exact lpT215863975889t0102
  rcases hid with rfl | hid
  · exact lpT215863975889t0104
  rcases hid with rfl | hid
  · exact lpT215863975889t0115
  rcases hid with rfl | hid
  · exact lpT215863975889t0134
  rcases hid with rfl | hid
  · exact lpT215863975889t0136
  rcases hid with rfl | hid
  · exact lpT215863975889t0149
  rcases hid with rfl | hid
  · exact lpT215863975889t0175
  rcases hid with rfl | hid
  · exact lpT215863975889t0178
  rcases hid with rfl | hid
  · exact lpT215863975889t0180
  · exact lpT223336279535t2552

