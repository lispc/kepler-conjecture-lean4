/-
  Kepler/Text/LP/LPAll — LP 终端 per-record 骨架层（T2 波 2026-10-08，机器生成，勿手改）。

  生成器：`lean/scripts/gen_lp_skeleton.py`（量化装配：段总量 + bound 总量（内核真证）；再生成会覆盖本文件）。
  记录清单来源：reference/flyspeck/formal_lp/glpk/binary
  的 {easy,hard}_*.dat 确定性重放（parse_lpcert.py 已提交读器，
  DFS 序 = ti 序）。信任模型：叶 = open `sorry` 骨架（deferred-compute），
  闭合 = LP 重跑产物模块（`socert.py --col-major` 形，PilotCM204880136538
  在库样板）转发；语义核心与退化防线见 `Kepler.Text.LP.LPCert`。
-/
import Kepler.Text.LP.LPLeafInfeas00
import Kepler.Text.LP.LPLeafRoot00
import Kepler.Text.LP.LPLeafRoot01
import Kepler.Text.LP.LPLeafRoot02
import Kepler.Text.LP.LPLeafRoot03
import Kepler.Text.LP.LPLeafRoot04
import Kepler.Text.LP.LPLeafRoot05
import Kepler.Text.LP.LPLeafRoot06
import Kepler.Text.LP.LPLeafRoot07
import Kepler.Text.LP.LPLeafRoot08
import Kepler.Text.LP.LPLeafRoot09
import Kepler.Text.LP.LPLeafRoot10
import Kepler.Text.LP.LPLeafRoot11
import Kepler.Text.LP.LPLeafRoot12
import Kepler.Text.LP.LPLeafRoot13
import Kepler.Text.LP.LPLeafRoot14
import Kepler.Text.LP.LPLeafRoot15
import Kepler.Text.LP.LPLeafRoot16
import Kepler.Text.LP.LPLeafRoot17
import Kepler.Text.LP.LPLeafRoot18
import Kepler.Text.LP.LPLeafRoot19
import Kepler.Text.LP.LPLeafRoot20
import Kepler.Text.LP.LPLeafRoot21
import Kepler.Text.LP.LPLeafRoot22
import Kepler.Text.LP.LPLeafRoot23
import Kepler.Text.LP.LPLeafRoot24
import Kepler.Text.LP.LPLeafRoot25
import Kepler.Text.LP.LPLeafRoot26
import Kepler.Text.LP.LPLeafRoot27
import Kepler.Text.LP.LPLeafRoot28
import Kepler.Text.LP.LPLeafRoot29
import Kepler.Text.LP.LPLeafRoot30
import Kepler.Text.LP.LPLeafRoot31
import Kepler.Text.LP.LPLeafRoot32
import Kepler.Text.LP.LPLeafRoot33
import Kepler.Text.LP.LPLeafRoot34
import Kepler.Text.LP.LPLeafRoot35
import Kepler.Text.LP.LPLeafRoot36
import Kepler.Text.LP.LPLeafRoot37
import Kepler.Text.LP.LPLeafRoot38
import Kepler.Text.LP.LPLeafRoot39
import Kepler.Text.LP.LPLeafRoot40
import Kepler.Text.LP.LPLeafRoot41
import Kepler.Text.LP.LPLeafRoot42
import Kepler.Text.LP.LPLeafRoot43
import Kepler.Text.LP.LPLeafRoot44
import Kepler.Text.LP.LPLeafRoot45
import Kepler.Text.LP.LPLeafRoot46
import Kepler.Text.LP.LPLeafRoot47
import Kepler.Text.LP.LPLeafRoot48
import Kepler.Text.LP.LPLeafRoot49
import Kepler.Text.LP.LPLeafRoot50
import Kepler.Text.LP.LPLeafRoot51
import Kepler.Text.LP.LPLeafRoot52
import Kepler.Text.LP.LPLeafRoot53
import Kepler.Text.LP.LPLeafRoot54
import Kepler.Text.LP.LPLeafRoot55
import Kepler.Text.LP.LPLeafRoot56
import Kepler.Text.LP.LPLeafRoot57
import Kepler.Text.LP.LPLeafRoot58
import Kepler.Text.LP.LPLeafRoot59
import Kepler.Text.LP.LPLeafRoot60
import Kepler.Text.LP.LPLeafRoot61
import Kepler.Text.LP.LPLeafRoot62
import Kepler.Text.LP.LPLeafRoot63
import Kepler.Text.LP.LPLeafRoot64
import Kepler.Text.LP.LPLeafRoot65
import Kepler.Text.LP.LPLeafRoot66
import Kepler.Text.LP.LPLeafRoot67
import Kepler.Text.LP.LPLeafRoot68
import Kepler.Text.LP.LPLeafRoot69
import Kepler.Text.LP.LPLeafRoot70
import Kepler.Text.LP.LPLeafRoot71
import Kepler.Text.LP.LPLeafRoot72
import Kepler.Text.LP.LPLeafRoot73
import Kepler.Text.LP.LPLeafRoot74
import Kepler.Text.LP.LPLeafRoot75
import Kepler.Text.LP.LPLeafRoot76
import Kepler.Text.LP.LPLeafEasy00
import Kepler.Text.LP.LPLeafEasy01
import Kepler.Text.LP.LPLeafEasy02
import Kepler.Text.LP.LPLeafEasy03
import Kepler.Text.LP.LPLeafEasy04
import Kepler.Text.LP.LPLeafEasy05
import Kepler.Text.LP.LPLeafEasy06
import Kepler.Text.LP.LPLeafEasy07
import Kepler.Text.LP.LPLeafEasy08
import Kepler.Text.LP.LPLeafEasy09
import Kepler.Text.LP.LPLeafEasy10
import Kepler.Text.LP.LPLeafEasy11
import Kepler.Text.LP.LPLeafEasy12
import Kepler.Text.LP.LPLeafEasy13
import Kepler.Text.LP.LPLeafEasy14
import Kepler.Text.LP.LPLeafEasy15
import Kepler.Text.LP.LPLeafEasy16
import Kepler.Text.LP.LPLeafEasy17
import Kepler.Text.LP.LPLeafHard00
import Kepler.Text.LP.LPLeafHard01
import Kepler.Text.LP.LPLeafHard02
import Kepler.Text.LP.LPLeafHard03
import Kepler.Text.LP.LPLeafHard04
import Kepler.Text.LP.LPLeafHard05
import Kepler.Text.LP.LPLeafHard06
import Kepler.Text.LP.LPLeafHard07
import Kepler.Text.LP.LPLeafHard08
import Kepler.Text.LP.LPLeafHard09
import Kepler.Text.LP.LPLeafHard10
import Kepler.Text.LP.LPLeafHard11
import Kepler.Text.LP.LPLeafHard12
import Kepler.Text.LP.LPLeafHard13
import Kepler.Text.LP.LPLeafHard14
import Kepler.Text.LP.LPLeafHard15
import Kepler.Text.LP.LPLeafHard16
import Kepler.Text.LP.LPLeafHard17
import Kepler.Text.LP.LPLeafHard18
import Kepler.Text.LP.LPLeafHard19
import Kepler.Text.LP.LPLeafHard20
import Kepler.Text.LP.LPLeafHard21
import Kepler.Text.LP.LPLeafHard22
import Kepler.Text.LP.LPLeafHard23
import Kepler.Text.LP.LPLeafHard24
import Kepler.Text.LP.LPLeafHard25
import Kepler.Text.LP.LPLeafHard26
import Kepler.Text.LP.LPLeafHard27
import Kepler.Text.LP.LPLeafHard28
import Kepler.Text.LP.LPLeafHard29
import Kepler.Text.LP.LPLeafHard30
import Kepler.Text.LP.LPLeafHard31
import Kepler.Text.LP.LPLeafHard32
import Kepler.Text.LP.LPLeafHard33
import Kepler.Text.LP.LPLeafHard34
import Kepler.Text.LP.LPLeafHard35
import Kepler.Text.LP.LPLeafHard36
import Kepler.Text.LP.LPLeafHard37
import Kepler.Text.LP.LPLeafHard38
import Kepler.Text.LP.LPLeafHard39
import Kepler.Text.LP.LPLeafHard40
import Kepler.Text.LP.LPLeafHard41
import Kepler.Text.LP.LPLeafHard42
import Kepler.Text.LP.LPLeafHard43
import Kepler.Text.LP.LPLeafHard44
import Kepler.Text.LP.LPLeafHard45
import Kepler.Text.LP.LPLeafHard46
import Kepler.Text.LP.LPLeafHard47
import Kepler.Text.LP.LPLeafHard48
import Kepler.Text.LP.LPLeafHard49
import Kepler.Text.LP.LPLeafHard50
import Kepler.Text.LP.LPLeafHard51
import Kepler.Text.LP.LPLeafHard52
import Kepler.Text.LP.LPLeafHard53
import Kepler.Text.LP.LPLeafHard54
import Kepler.Text.LP.LPLeafHard55
import Kepler.Text.LP.LPLeafHard56
import Kepler.Text.LP.LPLeafHard57
import Kepler.Text.LP.LPLeafHard58
import Kepler.Text.LP.LPLeafHard59
import Kepler.Text.LP.LPLeafHard60
import Kepler.Text.LP.LPLeafHard61
import Kepler.Text.LP.LPLeafHard62
import Kepler.Text.LP.LPLeafHard63
import Kepler.Text.LP.LPLeafHard64
import Kepler.Text.LP.LPLeafHard65
import Kepler.Text.LP.LPLeafHard66
import Kepler.Text.LP.LPLeafHard67
import Kepler.Text.LP.LPLeafHard68
import Kepler.Text.LP.LPLeafHard69
import Kepler.Text.LP.LPLeafHard70
import Kepler.Text.LP.LPLeafHard71
import Kepler.Text.LP.LPLeafHard72
import Kepler.Text.LP.LPLeafHard73
import Kepler.Text.LP.LPLeafHard74
import Kepler.Text.LP.LPLeafHard75
import Kepler.Text.LP.LPLeafHard76
import Kepler.Text.LP.LPLeafHard77
set_option maxRecDepth 4096

namespace Kepler.Text.LP

/-- `infeas` 段总量（真实推导；1 chunk 链分发）。 -/
theorem lpAllInfeas : AllLpTerminalInfeasibleCertified lpInfeasIds := by
  intro id hid
  exact lpAllInfeas00 id hid

/-- `root` 段总量（真实推导；77 chunk 链分发）。 -/
theorem lpAllRoot : AllLpTerminalCertified lpRootIds := by
  intro id hid
  simp only [lpRootIds, List.mem_append] at hid
  rcases hid with hid | hid
  · rcases hid with hid | hid
    · rcases hid with hid | hid
      · rcases hid with hid | hid
        · rcases hid with hid | hid
          · rcases hid with hid | hid
            · rcases hid with hid | hid
              · rcases hid with hid | hid
                · rcases hid with hid | hid
                  · rcases hid with hid | hid
                    · rcases hid with hid | hid
                      · rcases hid with hid | hid
                        · rcases hid with hid | hid
                          · rcases hid with hid | hid
                            · rcases hid with hid | hid
                              · rcases hid with hid | hid
                                · rcases hid with hid | hid
                                  · rcases hid with hid | hid
                                    · rcases hid with hid | hid
                                      · rcases hid with hid | hid
                                        · rcases hid with hid | hid
                                          · rcases hid with hid | hid
                                            · rcases hid with hid | hid
                                              · rcases hid with hid | hid
                                                · rcases hid with hid | hid
                                                  · rcases hid with hid | hid
                                                    · rcases hid with hid | hid
                                                      · rcases hid with hid | hid
                                                        · rcases hid with hid | hid
                                                          · rcases hid with hid | hid
                                                            · rcases hid with hid | hid
                                                              · rcases hid with hid | hid
                                                                · rcases hid with hid | hid
                                                                  · rcases hid with hid | hid
                                                                    · rcases hid with hid | hid
                                                                      · rcases hid with hid | hid
                                                                        · rcases hid with hid | hid
                                                                          · rcases hid with hid | hid
                                                                            · rcases hid with hid | hid
                                                                              · rcases hid with hid | hid
                                                                                · rcases hid with hid | hid
                                                                                  · rcases hid with hid | hid
                                                                                    · rcases hid with hid | hid
                                                                                      · rcases hid with hid | hid
                                                                                        · rcases hid with hid | hid
                                                                                          · rcases hid with hid | hid
                                                                                            · rcases hid with hid | hid
                                                                                              · rcases hid with hid | hid
                                                                                                · rcases hid with hid | hid
                                                                                                  · rcases hid with hid | hid
                                                                                                    · rcases hid with hid | hid
                                                                                                      · rcases hid with hid | hid
                                                                                                        · rcases hid with hid | hid
                                                                                                          · rcases hid with hid | hid
                                                                                                            · rcases hid with hid | hid
                                                                                                              · rcases hid with hid | hid
                                                                                                                · rcases hid with hid | hid
                                                                                                                  · rcases hid with hid | hid
                                                                                                                    · rcases hid with hid | hid
                                                                                                                      · rcases hid with hid | hid
                                                                                                                        · rcases hid with hid | hid
                                                                                                                          · rcases hid with hid | hid
                                                                                                                            · rcases hid with hid | hid
                                                                                                                              · rcases hid with hid | hid
                                                                                                                                · rcases hid with hid | hid
                                                                                                                                  · rcases hid with hid | hid
                                                                                                                                    · rcases hid with hid | hid
                                                                                                                                      · rcases hid with hid | hid
                                                                                                                                        · rcases hid with hid | hid
                                                                                                                                          · rcases hid with hid | hid
                                                                                                                                            · rcases hid with hid | hid
                                                                                                                                              · rcases hid with hid | hid
                                                                                                                                                · rcases hid with hid | hid
                                                                                                                                                  · rcases hid with hid | hid
                                                                                                                                                    · rcases hid with hid | hid
                                                                                                                                                      · rcases hid with hid | hid
                                                                                                                                                        · exact lpAllRoot00 id hid
                                                                                                                                                        · exact lpAllRoot01 id hid
                                                                                                                                                      · exact lpAllRoot02 id hid
                                                                                                                                                    · exact lpAllRoot03 id hid
                                                                                                                                                  · exact lpAllRoot04 id hid
                                                                                                                                                · exact lpAllRoot05 id hid
                                                                                                                                              · exact lpAllRoot06 id hid
                                                                                                                                            · exact lpAllRoot07 id hid
                                                                                                                                          · exact lpAllRoot08 id hid
                                                                                                                                        · exact lpAllRoot09 id hid
                                                                                                                                      · exact lpAllRoot10 id hid
                                                                                                                                    · exact lpAllRoot11 id hid
                                                                                                                                  · exact lpAllRoot12 id hid
                                                                                                                                · exact lpAllRoot13 id hid
                                                                                                                              · exact lpAllRoot14 id hid
                                                                                                                            · exact lpAllRoot15 id hid
                                                                                                                          · exact lpAllRoot16 id hid
                                                                                                                        · exact lpAllRoot17 id hid
                                                                                                                      · exact lpAllRoot18 id hid
                                                                                                                    · exact lpAllRoot19 id hid
                                                                                                                  · exact lpAllRoot20 id hid
                                                                                                                · exact lpAllRoot21 id hid
                                                                                                              · exact lpAllRoot22 id hid
                                                                                                            · exact lpAllRoot23 id hid
                                                                                                          · exact lpAllRoot24 id hid
                                                                                                        · exact lpAllRoot25 id hid
                                                                                                      · exact lpAllRoot26 id hid
                                                                                                    · exact lpAllRoot27 id hid
                                                                                                  · exact lpAllRoot28 id hid
                                                                                                · exact lpAllRoot29 id hid
                                                                                              · exact lpAllRoot30 id hid
                                                                                            · exact lpAllRoot31 id hid
                                                                                          · exact lpAllRoot32 id hid
                                                                                        · exact lpAllRoot33 id hid
                                                                                      · exact lpAllRoot34 id hid
                                                                                    · exact lpAllRoot35 id hid
                                                                                  · exact lpAllRoot36 id hid
                                                                                · exact lpAllRoot37 id hid
                                                                              · exact lpAllRoot38 id hid
                                                                            · exact lpAllRoot39 id hid
                                                                          · exact lpAllRoot40 id hid
                                                                        · exact lpAllRoot41 id hid
                                                                      · exact lpAllRoot42 id hid
                                                                    · exact lpAllRoot43 id hid
                                                                  · exact lpAllRoot44 id hid
                                                                · exact lpAllRoot45 id hid
                                                              · exact lpAllRoot46 id hid
                                                            · exact lpAllRoot47 id hid
                                                          · exact lpAllRoot48 id hid
                                                        · exact lpAllRoot49 id hid
                                                      · exact lpAllRoot50 id hid
                                                    · exact lpAllRoot51 id hid
                                                  · exact lpAllRoot52 id hid
                                                · exact lpAllRoot53 id hid
                                              · exact lpAllRoot54 id hid
                                            · exact lpAllRoot55 id hid
                                          · exact lpAllRoot56 id hid
                                        · exact lpAllRoot57 id hid
                                      · exact lpAllRoot58 id hid
                                    · exact lpAllRoot59 id hid
                                  · exact lpAllRoot60 id hid
                                · exact lpAllRoot61 id hid
                              · exact lpAllRoot62 id hid
                            · exact lpAllRoot63 id hid
                          · exact lpAllRoot64 id hid
                        · exact lpAllRoot65 id hid
                      · exact lpAllRoot66 id hid
                    · exact lpAllRoot67 id hid
                  · exact lpAllRoot68 id hid
                · exact lpAllRoot69 id hid
              · exact lpAllRoot70 id hid
            · exact lpAllRoot71 id hid
          · exact lpAllRoot72 id hid
        · exact lpAllRoot73 id hid
      · exact lpAllRoot74 id hid
    · exact lpAllRoot75 id hid
  · exact lpAllRoot76 id hid

/-- `easy` 段总量（真实推导；18 chunk 链分发）。 -/
theorem lpAllEasy : AllLpTerminalCertified lpEasyIds := by
  intro id hid
  simp only [lpEasyIds, List.mem_append] at hid
  rcases hid with hid | hid
  · rcases hid with hid | hid
    · rcases hid with hid | hid
      · rcases hid with hid | hid
        · rcases hid with hid | hid
          · rcases hid with hid | hid
            · rcases hid with hid | hid
              · rcases hid with hid | hid
                · rcases hid with hid | hid
                  · rcases hid with hid | hid
                    · rcases hid with hid | hid
                      · rcases hid with hid | hid
                        · rcases hid with hid | hid
                          · rcases hid with hid | hid
                            · rcases hid with hid | hid
                              · rcases hid with hid | hid
                                · rcases hid with hid | hid
                                  · exact lpAllEasy00 id hid
                                  · exact lpAllEasy01 id hid
                                · exact lpAllEasy02 id hid
                              · exact lpAllEasy03 id hid
                            · exact lpAllEasy04 id hid
                          · exact lpAllEasy05 id hid
                        · exact lpAllEasy06 id hid
                      · exact lpAllEasy07 id hid
                    · exact lpAllEasy08 id hid
                  · exact lpAllEasy09 id hid
                · exact lpAllEasy10 id hid
              · exact lpAllEasy11 id hid
            · exact lpAllEasy12 id hid
          · exact lpAllEasy13 id hid
        · exact lpAllEasy14 id hid
      · exact lpAllEasy15 id hid
    · exact lpAllEasy16 id hid
  · exact lpAllEasy17 id hid

/-- `hard` 段总量（真实推导；78 chunk 链分发）。 -/
theorem lpAllHard : AllLpTerminalCertified lpHardIds := by
  intro id hid
  simp only [lpHardIds, List.mem_append] at hid
  rcases hid with hid | hid
  · rcases hid with hid | hid
    · rcases hid with hid | hid
      · rcases hid with hid | hid
        · rcases hid with hid | hid
          · rcases hid with hid | hid
            · rcases hid with hid | hid
              · rcases hid with hid | hid
                · rcases hid with hid | hid
                  · rcases hid with hid | hid
                    · rcases hid with hid | hid
                      · rcases hid with hid | hid
                        · rcases hid with hid | hid
                          · rcases hid with hid | hid
                            · rcases hid with hid | hid
                              · rcases hid with hid | hid
                                · rcases hid with hid | hid
                                  · rcases hid with hid | hid
                                    · rcases hid with hid | hid
                                      · rcases hid with hid | hid
                                        · rcases hid with hid | hid
                                          · rcases hid with hid | hid
                                            · rcases hid with hid | hid
                                              · rcases hid with hid | hid
                                                · rcases hid with hid | hid
                                                  · rcases hid with hid | hid
                                                    · rcases hid with hid | hid
                                                      · rcases hid with hid | hid
                                                        · rcases hid with hid | hid
                                                          · rcases hid with hid | hid
                                                            · rcases hid with hid | hid
                                                              · rcases hid with hid | hid
                                                                · rcases hid with hid | hid
                                                                  · rcases hid with hid | hid
                                                                    · rcases hid with hid | hid
                                                                      · rcases hid with hid | hid
                                                                        · rcases hid with hid | hid
                                                                          · rcases hid with hid | hid
                                                                            · rcases hid with hid | hid
                                                                              · rcases hid with hid | hid
                                                                                · rcases hid with hid | hid
                                                                                  · rcases hid with hid | hid
                                                                                    · rcases hid with hid | hid
                                                                                      · rcases hid with hid | hid
                                                                                        · rcases hid with hid | hid
                                                                                          · rcases hid with hid | hid
                                                                                            · rcases hid with hid | hid
                                                                                              · rcases hid with hid | hid
                                                                                                · rcases hid with hid | hid
                                                                                                  · rcases hid with hid | hid
                                                                                                    · rcases hid with hid | hid
                                                                                                      · rcases hid with hid | hid
                                                                                                        · rcases hid with hid | hid
                                                                                                          · rcases hid with hid | hid
                                                                                                            · rcases hid with hid | hid
                                                                                                              · rcases hid with hid | hid
                                                                                                                · rcases hid with hid | hid
                                                                                                                  · rcases hid with hid | hid
                                                                                                                    · rcases hid with hid | hid
                                                                                                                      · rcases hid with hid | hid
                                                                                                                        · rcases hid with hid | hid
                                                                                                                          · rcases hid with hid | hid
                                                                                                                            · rcases hid with hid | hid
                                                                                                                              · rcases hid with hid | hid
                                                                                                                                · rcases hid with hid | hid
                                                                                                                                  · rcases hid with hid | hid
                                                                                                                                    · rcases hid with hid | hid
                                                                                                                                      · rcases hid with hid | hid
                                                                                                                                        · rcases hid with hid | hid
                                                                                                                                          · rcases hid with hid | hid
                                                                                                                                            · rcases hid with hid | hid
                                                                                                                                              · rcases hid with hid | hid
                                                                                                                                                · rcases hid with hid | hid
                                                                                                                                                  · rcases hid with hid | hid
                                                                                                                                                    · rcases hid with hid | hid
                                                                                                                                                      · rcases hid with hid | hid
                                                                                                                                                        · rcases hid with hid | hid
                                                                                                                                                          · exact lpAllHard00 id hid
                                                                                                                                                          · exact lpAllHard01 id hid
                                                                                                                                                        · exact lpAllHard02 id hid
                                                                                                                                                      · exact lpAllHard03 id hid
                                                                                                                                                    · exact lpAllHard04 id hid
                                                                                                                                                  · exact lpAllHard05 id hid
                                                                                                                                                · exact lpAllHard06 id hid
                                                                                                                                              · exact lpAllHard07 id hid
                                                                                                                                            · exact lpAllHard08 id hid
                                                                                                                                          · exact lpAllHard09 id hid
                                                                                                                                        · exact lpAllHard10 id hid
                                                                                                                                      · exact lpAllHard11 id hid
                                                                                                                                    · exact lpAllHard12 id hid
                                                                                                                                  · exact lpAllHard13 id hid
                                                                                                                                · exact lpAllHard14 id hid
                                                                                                                              · exact lpAllHard15 id hid
                                                                                                                            · exact lpAllHard16 id hid
                                                                                                                          · exact lpAllHard17 id hid
                                                                                                                        · exact lpAllHard18 id hid
                                                                                                                      · exact lpAllHard19 id hid
                                                                                                                    · exact lpAllHard20 id hid
                                                                                                                  · exact lpAllHard21 id hid
                                                                                                                · exact lpAllHard22 id hid
                                                                                                              · exact lpAllHard23 id hid
                                                                                                            · exact lpAllHard24 id hid
                                                                                                          · exact lpAllHard25 id hid
                                                                                                        · exact lpAllHard26 id hid
                                                                                                      · exact lpAllHard27 id hid
                                                                                                    · exact lpAllHard28 id hid
                                                                                                  · exact lpAllHard29 id hid
                                                                                                · exact lpAllHard30 id hid
                                                                                              · exact lpAllHard31 id hid
                                                                                            · exact lpAllHard32 id hid
                                                                                          · exact lpAllHard33 id hid
                                                                                        · exact lpAllHard34 id hid
                                                                                      · exact lpAllHard35 id hid
                                                                                    · exact lpAllHard36 id hid
                                                                                  · exact lpAllHard37 id hid
                                                                                · exact lpAllHard38 id hid
                                                                              · exact lpAllHard39 id hid
                                                                            · exact lpAllHard40 id hid
                                                                          · exact lpAllHard41 id hid
                                                                        · exact lpAllHard42 id hid
                                                                      · exact lpAllHard43 id hid
                                                                    · exact lpAllHard44 id hid
                                                                  · exact lpAllHard45 id hid
                                                                · exact lpAllHard46 id hid
                                                              · exact lpAllHard47 id hid
                                                            · exact lpAllHard48 id hid
                                                          · exact lpAllHard49 id hid
                                                        · exact lpAllHard50 id hid
                                                      · exact lpAllHard51 id hid
                                                    · exact lpAllHard52 id hid
                                                  · exact lpAllHard53 id hid
                                                · exact lpAllHard54 id hid
                                              · exact lpAllHard55 id hid
                                            · exact lpAllHard56 id hid
                                          · exact lpAllHard57 id hid
                                        · exact lpAllHard58 id hid
                                      · exact lpAllHard59 id hid
                                    · exact lpAllHard60 id hid
                                  · exact lpAllHard61 id hid
                                · exact lpAllHard62 id hid
                              · exact lpAllHard63 id hid
                            · exact lpAllHard64 id hid
                          · exact lpAllHard65 id hid
                        · exact lpAllHard66 id hid
                      · exact lpAllHard67 id hid
                    · exact lpAllHard68 id hid
                  · exact lpAllHard69 id hid
                · exact lpAllHard70 id hid
              · exact lpAllHard71 id hid
            · exact lpAllHard72 id hid
          · exact lpAllHard73 id hid
        · exact lpAllHard74 id hid
      · exact lpAllHard75 id hid
    · exact lpAllHard76 id hid
  · exact lpAllHard77 id hid

/-- bound 形总量（真实推导；三段分发，左结合递归）。 -/
theorem lpTerminalBoundAll : AllLpTerminalCertified lpTerminalBoundIds := by
  intro id hid
  simp only [lpTerminalBoundIds, List.mem_append] at hid
  rcases hid with hid | hid
  · rcases hid with hid | hid
    · exact lpAllRoot id hid
    · exact lpAllEasy id hid
  · exact lpAllHard id hid

/- 记录覆盖对账（数据层）：master 清单 = infeasible 段 ++ bound 段，
两总量分治覆盖；长度定理见 LPIds（盘点基线 43,078 = 189 + 42,889）。
NEEDS(deferred-compute): 42,889 bound 叶逐条重跑转发 + 189
infeasible 证书通道定形；接口级消费 = Assembly §2d' 记账段。 -/
