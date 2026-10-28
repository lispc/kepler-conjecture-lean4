# fidconf-report — fidelity-v2 的 166 条配对冲突静态分诊

- 车道: fidconf-w1; 基线 `8bcbfba3`（fidelity-v2 落库后）; 主仓零改动、零构建零锁。
- 上游: `docs/scouts/fidelity-audit-v2.tsv` + `fidelity-audit-v2.md` + `lean/scripts/fidelity_check_v2.py`（判定语义）。
- 交付: `fidconf-triage.tsv`（165 行, 每行 = conflict id / 类 / 机理·新锚·宿主 / 置信 / 抽验标记 / 全套证据列）。

## 0. 数据源事实与重建方法（先读）

v2 移交的"166 条冲突清单"**没有机器可读全量落盘**：md 冲突表硬截断
`cf[:25]`（其余 141 条"从略"），TSV 无冲突列，清单只存在于 v2 脚本运行内存。
本车道硬约束禁 python3，故以 **awk 静态复刻** v2 冲突检测全链路：

- `pass1_index.awk`：HOL 索引（PROVE/NEWDEF/FORMULA/ADD 四正则 + 反引号 span +
  goal_ref 行号改写 + basename packing-first 排序），复刻 v1 `build_hol_index`。
- `pass2_conflicts.awk`：Lean 注释 span → docstring/上邻链/体注（块级归属规则）
  → V2 指针池 → V2 解析语义（包含 ±0/2 最内起者赢 → 最近 ≤6 → 大小写回退，
  多 basename 歧义不解析）→ 锚配对声明的冲突抽查；另复刻未配对声明的
  UNRESOLVED/AMBIGUOUS 通路用于对拍。

**保真度校验（多重 oracle, 全部逐字通过）**：

| oracle | 结果 |
|---|---|
| HOL 记录 16728 / 408 文件（md 统计表） | 16728 / 408 **精确** |
| TSV 全部 7806 个 v1 锚（hol_file:hol_line）反查索引 | 0 失配 |
| 7806 锚 route 复推记录身份（pointer/pointer~/name/docname/name-ci） | 0 失配 |
| md 冲突表可见 25 行 | **逐行精确一致** |
| md UNRESOLVED 表可见 60 行（锚+指针+原因+区） | **逐行精确一致**；总数 167=167 |
| md AMBIGUOUS 表 5 行 | **逐行精确一致**；总数 5=5 |

复刻中修掉的 bug（均为对 oracle 的偏差驱动）：formula 记录 start 误用反引号
偏移；`add {` 跨行块（恰补齐缺口 136 条 ineq 记录）；指针池基名漏 `.hl`；
python `\s` 含 `\f\v`（Text 文件大量以 `\v` 作行内空隙，如 `appendix.hl:\v719`）。

**残差披露**：冲突总数复刻 **165 vs 移交 166**。差 1 条位于 md 从略区、无任何
可观测 oracle 覆盖；所有可见 oracle（25+60+5 行）逐字通过，块级 keep/drop、
above 链、bound、seen 去重等可疑层均已逐一对照排除。同簇均有多条同机理样本，
1 条残差不影响簇级结论；若编排者可跑 v2 脚本，`--diff` 一跑即知。

## 1. 四类分布

| 类 | 条数 | 占比 |
|---|---|---|
| ARTIFACT 配对伪影 | **160** | 97.0% |
| POINTER-ROT 指针朽坏 | **5** | 3.0% |
| RESTATEMENT 内核重述 | **0** | 0 |
| REAL-Q 真问题 | **0** | 0 |

ARTIFACT 亚族（160 条）：

| 亚族 | 条数 | 一句话机理 |
|---|---|---|
| 多锚提及注记 | 73 | 同一 docstring/体注并列多个 HOL 锚，v1 取首锚，第二锚成冲突行 |
| registry/concl 宿主注记 | 34 | 证明件/接口件引注其 registry concl 或 statement-let 宿主，双锚并存 |
| 缺口/未移植清单注记 | 15 | 体注"缺口清单"并列多个未移植 HOL 锚（fan/Conforming/hypermap 簇） |
| 证明原料/装配路线注记 | 11 | 证明所用的其他 HOL 引理/条目引证（如 GRKIBMP 的 ineq.hl:1520 原料） |
| 双正本/副本注记 | 10 | 语料同一定义两处副本（`HDPLYGY.hl:35 = localization.hl:135` 类），注记并列双锚 |
| CI 变体基名引注 | 8 | 大小写变体基名（`Fan.hl`/`Nkezbfc.hl`/`Hdplygy.hl`/`Hvihvec.hl`/`sgtrnaf.hl`），v2 回退命中正文名，指针与实文一致 |
| NEEDS 依赖注记（_pN 副本件） | 5 | `-- NEEDS:` 行指上游正本（LocalAuto13 族） |
| 重复定义注记 | 2 | `pack1.hl:329/332` 为 `pack_defs` 正本的副本，注记自证 |
| 草稿注记 | 1 | `marchal_quartic` 草稿被注释（pack_defs.hl:134-138），活性版即 v1 锚 |
| 名误行准 | 1 | CHQSQEY docstring 误书 "MTMLSRF_concl" 但行号 :135 即本体，解析中靶 |

## 2. POINTER-ROT 子簇（唯一实质发现, 5 条, 已核新锚）

`OXLZLEZ1.hl` 的 concl 行号在 Lean docstring 里与实文错位（对实文逐行核实，
结论记录实位：CHQSQEY:135 / MTMLSRF:138 / LXDEYBO:142 / UNPNFVW:145 /
IPVICGW:156 / RSIWAMP:159（重复副本 :162）/ UTEOITF:167）：

| 行 | Lean 锚 | 引注 | 实文 | 误落记录 |
|---|---|---|---|---|
| 142 | PackingAuto3:2773 `p3i_IPVICGW` | OXLZLEZ1.hl:548 | **:156** | :553 PERIODIC_PROPERTY |
| 146 | PackingAuto4:372 `MTMLSRF` | OXLZLEZ1.hl:135 | **:138** | CHQSQEY_concl:135 |
| 148 | PackingAuto4:464 `UNPNFVW` | OXLZLEZ1.hl:139 | **:145** | MTMLSRF_concl:138 |
| 149 | PackingAuto4:669 `IPVICGW` | OXLZLEZ1.hl:548 | **:156** | :553 PERIODIC_PROPERTY |
| 150 | PackingAuto4:678 `RSIWAMP` | OXLZLEZ1.hl:554 | **:159** | :553 PERIODIC_PROPERTY |

注意：PackingAuto3 侧同簇六条（138/139/140/141/143/144）行号全对——错位集中
在 PackingAuto4 全件与 PackingAuto3 的 IPVICGW 一条，机理是按旧版行号誊抄。
这 6 处 docstring（含 147 名误）为**注释级勘误 SF 候选包**，不涉任何陈述改动；
v1 配对本体全部正确（都走 OXLZLEZ2 证明件锚）。

附带 corpus 瑕疵（非 Lean 侧）：`OXLZLEZ1.hl:159` 与 `:162` 是逐字重复的
`RSIWAMP_concl` 定义，引用方按首现取 :159 即可，无行动项。

## 3. 抽验记录（真开文件人工复核 33 行, 防自我确认）

每类抽验满足 ≥3；实文核对覆盖 ARTIFACT 各亚族 + POINTER-ROT 全部：

- **ARTIFACT-证明引理化（17）**：ContraFan.lean:786 `ESTD_fan6`——docstring 引
  CKQOWSA_4.hl:45 `estd_non_collinear_lemma`；核 CKQOWSA.hl:79-88 原证
  `MATCH_MP_TAC estd_non_collinear_lemma` ✓ 注记=证明所用引理，v1 锚正确。
- **ARTIFACT-母定义/出处注记（21,22,23）**：IneqClosureDefs.lean:95/136/173——
  核 nonlin_def.hl:132（母定义 dih_x_div_sqrtdelta）、:138-146（posbranch 族）✓、
  sphere.hl:525（lfun）✓、sphere.hl:830-833（eulerA_x 体）✓，引文与实文一致。
- **ARTIFACT-双正本（50,76,77）**：localization.hl:20=has_orders、:135=a_ear0 ✓，
  HDPLYGY.hl:35=a_ear0 ✓ 双锚注记准确。
- **ARTIFACT-CI 变体（53,60,75,78,79）**：SGTRNAF.hl:166、fan.hl:711
  （UNIQUE_AZIM_POINT_FAN）、HVIHVEC.hl:34、HDPLYGY.hl:35、NKEZBFC.hl:1348
  （order）✓ 全部实文命中。
- **ARTIFACT-别名/最近邻（95）**：LocalConcl.lean:1153 `DRNDRDV_discharged`——
  核 OCBICBY.hl:766（derived_form_xrr 正本 ✓）、:849（`let DRNDRDV = …` 别名行,
  非记录）→ ≤6 容差落 :851 derived_form_unique ✓ 机理解释成立。
- **ARTIFACT-待移植依赖（102,104）**：PackingAuto10.lean:1006/1214——v1 锚
  RVFXZBU.hl:32 / YNHYJIT.hl:33 与 Lean 声明逐字同构 ✓；marchal2.hl:5848=
  LEFT_ACTION_LIST_1_PROPERTIES ✓，"ports the core"=sorry 案的待移植依赖注记。
- **ARTIFACT-重复定义/草稿（119,120,121）**：pack1.hl:329/332 副本 ✓；
  pack_defs.hl:134-138 注释草稿 ✓ 且活性版 sphere.hl:519 与 Lean 体一致
  （草稿与活性版代数恒等、符号两次翻转，docstring"differs"仅语法层）。
- **ARTIFACT-符号对照（127）/证明原料（128）**：PackingAuto21.lean:268/1055——
  ineq.hl:355（TSKAJXY-GXSABWC DIV，x-space 平方长度盒 ✓）、merge_ineq.hl:1159
  gamma4fgcy_div_sqrtdelta ✓、merge_ineq.hl:3794 GRKIBMP prove ✓、
  ineq.hl:1516-1520（add 块起点 vs idv 行, 解析正确落块首）✓。
- **ARTIFACT-discharge 策略（154）**：PackingConcl.lean:337 "NO USABLE TWIN"——
  marchal2.hl:2515 MXI_EXPLICIT ✓，注记指下游自环消费者。
- **POINTER-ROT（142,146,147,148,149,150 + 对照组 138-145）**：OXLZLEZ1.hl
  130-172/545-560 与 OXLZLEZ2.hl 402/564/1322/3308 实文逐点核对（见 §2 表）。

## 4. RESTATEMENT / REAL-Q 核查记录（0 条的依据）

- **RESTATEMENT=0**：冲突行里 rx 与 Lean 声明呈"证明内核"关系的候选语境
  全部开文件核实并排除——"ports the core of marchal2.hl:5848"（102/104）实为
  RVFXZBU/YNHYJIT 正本件的待移植依赖注记（正本锚逐字同构）；"only restates a
  _new_concl"（112）是解释**为何不取**该锚的注记；cf4_etaP_box 型"内核重述"
  在本批 165 条中无第二例。
- **REAL-Q=0**：对全部 165 条触发语境做了陈述级分歧扫描——符号类（127 的
  sign 对照注记）、"differs"（121，代数恒等仅语法异）、"NO USABLE TWIN"
  （154）、误誊史（冲突行 30：LocalAuto11.lean:174 `x1DeltaY_p11` 的
  delta_x1→delta_x 已在体内修正，现体与 sphere.hl:840 `x1_delta_x` 逐字同构）
  均落 ARTIFACT。未发现陈述级
  分歧或疑似漏件；**无 SF 立案级、无 NEEDS 件**。

## 5. 建议

1. **SF 候选（注释级勘误包, 一个 bundle）**：§2 的 6 处 docstring 行号/名误
   （PackingAuto3:2773、PackingAuto4:372/409/464/669/678）。不涉陈述，纯注释。
2. **v3 规则**：冲突清单**不值得**为归并进 v3 配对规则——160/165 是"注记并列
   多锚"的信息性冲突（第二锚往往正是下游需要的另一条线索），改规则只会丢信息。
   值得做的只有一件小事：对 OXLZLEZ1 这类**同文件内 `_concl` 高密度区**
   （135-171 间隔 3 行），把最近邻容差从 ≤6 收紧到 ≤2 可让 5 条 POINTER-ROT
   在扫描层直接显形为"解析失败"而不是错配；代价与收益都小, 由编排者定夺。
3. **移交口径勘误**：下一车道任务书不应写"TSV 内含冲突清单 166 条"——实际是
   md 截断 25 条 + 脚本内存；建议 v3 落库时把 conflicts 全量写进 TSV 或独立
   conflicts.tsv（本车道 pass2 已具备该能力）。
