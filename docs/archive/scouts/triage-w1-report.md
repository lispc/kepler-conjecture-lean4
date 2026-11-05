# triage-report — 直源 151 全量分诊（triage-w1）

- 基线：`4ff27ac1`（核对一致，主仓零写入、零构建）。
- 输入：`docs/e2e-reachability-map.tsv`（2026-10-27 重扫）SORRIED 直源 **151**（实数核对：
  `NF==3 && $3~/^parent=/` 恰 151 行；另 624 行 2 字段为 AXIOMS，不入账）。
- 交付：`direct-source-triage.tsv`（151 行 × 7 列；names+lines 与定位索引 `loc-151.tsv` 全量 diff 通过）。

## 1. 分布统计

### 1.1 按级

| 级 | 数 | 说明 |
|---|---|---|
| **A-银行** | **3** | LA22 `is_scs_3T1_p22`/`is_scs_3T5_p22`/`is_scs_3M1_p22`——显式 funlist 表逐格求值 + 基数计数（decide 级；先例 SCS_6I1_IS_SCS 真证、la5-bank-w1 模式） |
| **B-装配** | **28** | LA1 `*_concl` 箭头注册表 20 + `WKEIDFT_concl` 1 + LA20 3 + LA27 `EAPGLE_p27` 1 + PA2 `UPFZBZM_concl` 1 + **A2 在飞 `nliRestQITNPEA3725403817` 1**（:739，标 in-flight） |
| **C-真数学** | **14** | Assembly 3（`fcdjdot`/`jcajydu`/`tameCorrespondenceIso`）+ LA22 `OCBICBY_p22` 1 + LA23 2 + LA24 `XWITCCN_CASE_3..6` 4 + TameLp `fully_surrounded_perimeter_bound` 1 + PA25 LEAF 族 3 |
| **D-陈述SF** | **0** | 无一例纯误植；SF-53/54/55/56 已清的口径与实扫一致 |
| **E-farm** | **106** | Assembly nli\* 76（rest 56 + tsk 8 + cell3 7 + 直挂 5）+ hLP 1 + LA1 `main_nonlinear_terminal_v11` 1 + PA25 bank 叶 28（ox3q1hP25、ox3q1h_merge、26 real_model\*） |
| **F-文档** | **0** | 151 个位点全部实证为真 sorry 债，无 docstring/注记误报 |
| 合计 | **151** | A3 + B28 + C14 + D0 + E106 + F0 |

### 1.2 按文件

| 文件 | 条 | 级别构成 |
|---|---|---|
| `lean/Kepler/Assembly.lean` | 81 | B1（:739 in-flight）+ C3 + E77 |
| `lean/Kepler/Text/PackingAuto25.lean` | 31 | C3（LEAF 族）+ E28（bank 叶） |
| `lean/Kepler/Text/LocalAuto1.lean` | 23 | B22（registry+`WKEIDFT_concl`）+ E1（mnt11 def） |
| `lean/Kepler/Text/LocalAuto22.lean` | 4 | A3 + C1（OCBICBY） |
| `lean/Kepler/Text/LocalAuto24.lean` | 4 | C4 |
| `lean/Kepler/Text/LocalAuto20.lean` | 3 | B3 |
| `lean/Kepler/Text/LocalAuto23.lean` | 2 | C2 |
| `lean/Kepler/Text/LocalAuto27.lean` | 1 | B1 |
| `lean/Kepler/Text/PackingAuto2.lean` | 1 | B1（UPFZBZM_concl） |
| `lean/Kepler/Text/TameLp.lean` | 1 | C1 |

### 1.3 形状事实（逐位点实证）

- Assembly 77 条 nli\* 全部为 `theorem nliX : bank_X := sorry` 一行桩，docstring 统一
  "deferred-compute + NEEDS G4 证书发射 + 粘合入 §2a 查表"；仅 :739（A2 件）注明
  "内核闭合证书在库外（964,984 叶，2026-09-18，公理标准三）"。A1 模板件
  `nliRestFWGKMBZ`（:812）已真证（证书 605 分片在库 + evalReal 粘合），为 farm 波的
  逐条复制样板。
- 直挂 5（§0 的"直挂若干"= 恰 5）：`nliOx3q1h`/`nliMainNonlinearTerminalV11`/
  `nliLpIneqs`/`nliPackIneqDefA`/`nliKcblrqcIneqDef`，均为**语句级+证书级双缺口**
  （opaque def 或占位清单），非纯证书。
- textCapstone（Assembly:6290）证明体本身为真推导，其唯三 Assembly 级 sorry 消费点
  = `fcdjdot`/`jcajydu`/`tameCorrespondenceIso`（hTC 3），与 §0 完全一致。
- LA1 的 22 条箭头 = `scsArrowV39` 记录展开族（appendix.hl:1390–1510 注册表），
  `scsArrowV39 S1 S2 := (∀ s∈S2, isScsV39 s) ∧ ((∀ s∈S1, MMs=∅) ∨ ∃ s∈S2, MMs≠∅)`；
  闭法 = transferV39 孪生 + arrowSetRight/FZIOTEF_TRANS 代数，先例
  `YXIONXL1_discharged`（LocalConcl:500）已真。
- PA25 real_model\* 27 枚全部为 pkrmQu/Qx/Qy/Azim/Quarter 五真装配枢纽的 **bank 叶**
  （deferred-compute 外部认证锚），枢纽本体均已真推导。

## 2. 对账（地图口径 vs 队列 §0 口径）

| 项 | §0 / 任务书 | 实扫 | 结论 |
|---|---|---|---|
| M0 直源总数 | 151 | **151** | ✓ |
| Assembly / Text | 81 / 70 | 81 / 70 | ✓ |
| Text 细分 | PA25 31 + LA1 23 + LA20–27 14 + PA2/TameLp 各 1 | PA25 31 + LA1 23 + (LA20 3+LA22 4+LA23 2+LA24 4+LA27 1)=14 + PA2 1 + TameLp 1 | ✓ |
| hNL | 77 条 nli\*（57 rest + 8 tskBank + 7 cell3Bank + 直挂若干） | 77 = 57 + 8 + 7 + **5**（直挂恰为上列五件） | ✓（"若干"定为 5） |
| hLP | 1（`lpArchiveCertificatesDebt`，§0 注 Assembly:6224） | 1，实际 **:6236** | ✓ 条数；行号漂 12（纯行漂，非差异） |
| hTC | 3（fcdjdot/jcajydu/tameCorrespondenceIso） | 3，逐一实证为 textCapstone 真体的唯三 sorry 消费点 | ✓ |
| A2 in-flight rest 9 | 1 源（CQITNPEAx3725403817） | `nliRestQITNPEA3725403817` Assembly.lean:739，docstring 与 A2 事实吻合，标 in-flight→B | ✓ |
| poolc-w3 口径 | "32 枚锥直源"（基线 e2c636ec） | 现 PA25 = 31（real_model 27 + LEAF 3 + ox3q1hP25）；差 1 = poolc-w3 `430d1f48` 已闭 real_model_fhbv2 | ✓（时点差，非矛盾） |
| §0 hTC 句"Text 层 ~74 条" | ~74 | 70 | **差异 1（约数漂移）**：§0 该句为约数（"~"），TSV 2026-10-27 重扫 70 已含 poolc 系 −3/-1 的进账；以 TSV 为准，建议 §0 下次周对表改"~70" |

**结论：无实质对账差异。** 唯二记档：① §0 hTC 句的 "Text ~74" 为约数漂移（实 70）；
② lpArchiveCertificatesDebt 行号 6224→6236（文件行漂）。均为记档级，不动口径。

## 3. 终局清账波次建议（可达性 × 难度，5 波覆盖 151）

| 波 | 条目 | 构成 | 代表件 | 一句理由 |
|---|---|---|---|---|
| **W1 银行·装配波**（建议首发） | **30** | A3 + B27：LA1 registry 22 + LA20 3 + LA22 is_scs 3 + LA27 1 + PA2 1 | `OTMTOTJ1_concl`、`is_scs_3M1_p22`、`UPFZBZM_concl` | 全树剩余唯一的大面机械/装配区：kit（is_scs_funlist_basic_p22）+ transferV39 孪生补齐 + F1 改线（已批）即批量闭，零 farm 依赖；副产 = EAPGLE_p27 所需 is_scs 注册表面一并扫清 |
| **W2 A2 完工波**（在飞收口） | **1** | B1（in-flight） | `nliRestQITNPEA3725403817` | A2-W2b′ 构建+回灌+Glue 落库即 −1，任务书钦定样板件 |
| **W3 poolc-w3 PA25 波**（在飞） | **31** | C3 + E28 | `pkLeafRankCriticalEdge`、`real_model_sum_azim` | 在飞车道：LEAF 三件真移植先行（上游 :2286/:2449/三 wedge 件），27 bank 叶按 fhbv2 已证模板转 G4 证书排产，ox3q1h 双件（ox3q1hP25+merge）与 nliOx3q1h 同根并案 |
| **W4 nli/lp farm 总波** | **78** | E78：Assembly nli 76 + hLP 1 + LA1 mnt11 1 | `nliRestFWGKMBZ` 模板复制、`lpArchiveCertificatesDebt`、`main_nonlinear_terminal_v11`（与 Assembly:1221 同根双闭） | 纯产能波：A1 模板流水 + nli-prep 切界通道 + lp-w1/W6 系；mnt11 一闭同时解锁 W1 的 SCS_6I1_BERAK_BY_CSTAB 与 W5 的 OCBICBY/LFLACKU 前提 |
| **W5 C 真数学尾波** | **11** | C11：Assembly 3 + OCBICBY 1 + LA23 2 + LA24 4 + TameLp 1 | `fcdjdot`、`XWITCCN_CASE_3..6`、`fully_surrounded_perimeter_bound` | 章级移植（FNJLBXS 柱②③ / UXCKFPE 四 case / WMLNYMD / Local_lemmas 三桥），依赖 W1/W4 部分产出后收尾 |

合计 30+1+31+78+11 = **151**。依赖提示：W5 的 `tameCorrespondenceIso`/`jcajydu` 是
textCapstone 最后两根 Assembly 级柱；`fcdjdot` 独立最深（DLWCHEM/XULJEPR 计数 GIANT）。

## 4. 关键发现（≤3 条）

1. **D/F 均为零**：151 个直源全部实证为真债，无陈述误报、无文档误报——M0 账面干净，
   清账即纯证明/证书工作。
2. **farm 面占 70%（106/151）**，且其中 77 条 nli 桩形状逐字同一（`: bank_X := sorry`），
   A1（FWGKMBZ `286d11b8`）模板 + A2 在飞件已把边际成本压到"发射-粘合"两步；
   直挂 5 件是 farm 波里仅有的语句级前置（opaque def / 占位清单）。
3. **B 面 28 件几乎全部住在 LA1 registry 及其卫星文件**（§2 排队第 6 项 BO LA1 注册表
   侦察的预判"多为 scs 记录展开"实证成立），单波可清；其中 `EAPGLE_p27` 与
   `SCS_6I1_BERAK_BY_CSTAB` 闭时会把 LA22 is_scs 注册表族（场外 ~10 桩）拉入锥，
   M0 口径届时需预公告（同 JEJTVGB +36 教训）。
