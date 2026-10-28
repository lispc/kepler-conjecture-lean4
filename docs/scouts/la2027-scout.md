# LA20–27 直源 14 条侦察报告（la2027-scout）

- 车道：la2027-scout（只读侦察；队列「Text 层下一大簇波次图」）
- 基线：`1bd6a3fd`（开工 `git log -1` 实录；任务书基线 b226b2a6 之后）
- 方法论：`docs/scouts/bola1-registry-scout.md` 同款（清点→锚定→分级→波次）
  + `docs/scouts/direct-source-triage.tsv` :137-150 为 14 行底稿
- HOL 正本：`reference/flyspeck/text_formalization/local/`（hexagons/OCBICBY/
  JOTSWIX/UXCKFPE/AYQJTMD/ZITHLQN/QKNVMLB/LKGRQUI 等逐条锚定）
- 快照：`/Users/zhangzhuo/c17_backup/lane_snapshots/la2027-scout/`
- 硬约束遵守：主仓零写入、零构建零锁、shell 仅 grep/rg/ls/wc/sed/awk + git 只读。

---

## 1. 清点对账（14 = 14，零差）

`docs/e2e-reachability-map.tsv` 中 LocalAuto20–27 直源恰 **14 行**，与
triage tsv :137-150 的 14 行**逐名对应、零缺漏**：

| 文件 | 直源 | e2e parent |
|---|---|---|
| LA20 (3) | AQICLXA、FZIOTEF、SCS_6I1_BERAK_BY_CSTAB | OEHDBEN×2、OEHDBEN_PRIME |
| LA22 (4) | is_scs_3T1/3T5/3M1_p22、OCBICBY_p22 | BKOSSGE_p16×3、JEJTVGB_case_breakdown_p16 |
| LA23 (2) | LFLACKU_p23、s_init_list_alt_p23 | JEJTVGB_case_breakdown_p16 |
| LA24 (4) | XWITCCN_CASE_3/4/5/6_IS_SCS_p24 | UXCKFPE_p24 |
| LA27 (1) | EAPGLE_p27 | JEJTVGB_case_breakdown_p16 |

LA21/LA25/LA26 无直源。triage 的 Lean 行号全部仍精确（AQICLXA:984、
FZIOTEF:1006、BERAK:1218、1668/1688/1703/1930、:310/:318、1383/1124/1159/1192、
:867）；14 条现状全部 sorry（零翻案、零已闭）。唯一行号失真在**锚注**：
LA20 两处 NEEDS 记 `PROP_EQU_IS_SCS (LocalAuto12:424)`，现漂移至 **LA12:579**
（triage :137 同错）；YXIONXL3 同文件 :1220。

## 2. LA20 四处过时 NEEDS 核实（w1asm 翻案属实，另有加码）

1. **AQICLXA NEEDS（2 处）**：记 `LocalAuto1.YXIONXL3_concl (…, proof pending)`
   与 `PROP_EQU_IS_SCS (LocalAuto12:424, proof pending)`。实况：**LA12.YXIONXL3
   (:1220) 与 PROP_EQU_IS_SCS (:579) 均已真证**（完整 tactic 证明体）；LA1 的
   `_concl` 孪生 (:1683) 仍 sorry，但半箭头 `{propEqu s 1} → {s}` 的施工现在
   直接用 LA12 孪生 + 幂等 mod-k 塌缩（LA12:712/983 已给复合恒等）装配。
2. **FZIOTEF NEEDS（2 处）**：同上两件（shift 3 版）。
3. **加码一**：SCS_6M1/6I1_IMP_SCS_6T1 的 NEEDS 记 `PEDSLGV2 (proof pending)`
   —— **PEDSLGV2_concl 已于 2026-10-08 证（LA1:2362）**。
4. **加码二**：同 NEEDS 记 `MXQTIED_concl (proof pending)` —— **已证
   （LA1:1891，完整证明体）**。即「mnt11 四 concl」实为**三**（RRCWNSJ:2211、
   JCYFMRP:2219、JLXFDMJ:2248 仍 sorry）。
5. **加码三**：LA20 头注 ledger「all 7 blockers still open」整段过时。
6. **反向过时（勿信头注）**：LA23 头注记 `s_init_list_alt_p23 (proved)`，
   实况 **sorry**（git 追溯 `5699d337` W4 half1 引入即为 sorry，从未闭过）。
   triage 对该条的行号与分级无误。

结论：**AQICLXA/FZIOTEF 的半箭头已全部就绪**，本体只剩
AQICLXA_SLICE/FUNOUYH_SLICE（见 §4 枢纽 1）。

## 3. 逐条锚定与分级（R3 / S4 / M4 / X3，D = 0）

| 条目 | Lean 锚 | HOL 锚 | 分级 | 关键判据 |
|---|---|---|---|---|
| is_scs_3T1_p22 | LA22:1668 | OCBICBY.hl:4015 | **R** | HOL 三连 12 行脚本（is_scs_funlist_basic+NUM_REDUCE+FUNLIST_EXPLICIT+sqrt8_flyspeck）；Lean 生成器 `is_scs_funlist_basic_p22`(:1333) **已证**；k=3 有限模类 decide 级 |
| is_scs_3T5_p22 | LA22:1688 | :4085 | **R** | 同脚本；先例 is_scs_6I1/5I1 等 12 条 _p22 已证 |
| is_scs_3M1_p22 | LA22:1703 | :4029 | **R** | 同脚本；**树内已有同语句已证孪生 `SCS_3M1_IS_SCS`（LA20:209，58 行直证）**——LA20 import LA22 故反向不可引，需上游移植（或挪生成器） |
| s_init_list_alt_p23 | LA23:318 | JOTSWIX.hl:216 | **S** | HOL 全脚本在：前 6 项 rfl；7/8 两项 = aPro↔funlist_v39 k=5(6 格)/k=4(3 格) 恒等 + periodic2_mod_reduce；Lean 侧 aPro 已内联于 sInitListV39(LA1:551)，PSORT_5_EXPLICIT/periodic2_funlist_p20 已证 |
| EAPGLE_p27 | LA27:867 | AYQJTMD.hl:222 | **S** | HOL 8 行胶合（ZITHLQN+AYQJTMD+taustar 二分）；AYQJTMD_p27 已证、**LA25 八 CASE（3/4/5/6/4_3/5_sqrt8/5_pro_cs/4_pro_cs）全证**；只差 ZITHLQN 总装（ZITHLQN_p25:1004 是 LA1:653 sorry 的 re-export） |
| AQICLXA | LA20:984 | hexagons.hl:1449 | **S**（受阻） | 本体纯装配（TRANS+SLICE+UNION+YXIONXL3）；FZIOTEF_TRANS/UNION、半箭头全✓；唯一前置 AQICLXA_SLICE |
| FZIOTEF | LA20:1006 | :1592 | **S**（受阻） | 同形；唯一前置 FUNOUYH_SLICE |
| XWITCCN_CASE_4_IS_SCS_p24 | LA24:1124 | UXCKFPE.hl:432 | **M** | 5 件 DISCHARGES 链全 sorried（stable system + NOT_EMPTY_4 + HDPLYGY 极小化 + 显式行解码 + IN_NOT_EMPTY_4 + TAUSTAR_EQ_4 负性转移）；HOL 本体 ~80 行实质 |
| XWITCCN_CASE_5_IS_SCS_p24 | LA24:1159 | :889 | **M** | CASE_4 镜像（k=5，UXCKFPE.hl:547-995 见证层） |
| XWITCCN_CASE_6_IS_SCS_p24 | LA24:1192 | :1374 | **M** | CASE_4 镜像（k=6，:1003-1483） |
| XWITCCN_CASE_3_IS_SCS_p24 | LA24:1383 | :2495 | **M**（最重） | 6 件链（tri-stable kit + NOT_EMPTY_3 + IN_B_SY1_COLLINEAR + HDPLYGY_CASE_30 + IN_NOT_EMPTY_3 + TAUSTAR_EQ_3）；UXCKFPE.hl:1488-2597 整章；FINITE_J1_TS/tri_sy_explicit 已证可复用 |
| SCS_6I1_BERAK_BY_CSTAB | LA20:1218 | :1831 | **X** | SCS_6I1_IMP_SCS_6T1 ← SCS_6M1_IMP ← mnt11 银行三件 RRCWNSJ/JCYFMRP/JLXFDMJ（MXQTIED/PEDSLGV2 已证后仅此三）；LA28 Nuxcoea 两件已证，LA20 数值件全✓ |
| OCBICBY_p22 | LA22:1930 | OCBICBY.hl:4755 | **X** | 模板 pos_imp_scs_arrow_empty_p22(:1922) 已证；缺 14 支 T-系统「BBs→taustar≥0」正性 = HOL arrow_rewrite_list(:4746) = Terminal.empty_3T1..3T7/4T1-4T5/5T1/6T1（mnt11 同族银行） |
| LFLACKU_p23 | LA23:310 | JOTSWIX.hl:191 | **X** | taustar_taum_dfun/FUNLIST_EXPLICIT 桥未移植 + TAUM_STD_POS_p23(:299 sorry ← mnt11 终端条目 5541487347/OMKYNLT)；taum_attains_inf/TAUM_EXTREMAL 同链 sorry |

**D（陈述 SF 候选）：0 条**——14 条 Lean 陈述与 HOL 同形（XWITCCN 四条的
HOL `dimindex(:M)` 类型毛刺已在 Lean 侧合法消解；is_scs_3T6′ 带撇系注册表
正名，不在直源内）。

**对 triage 的分级修正**：
- is_scs_3T1/3T5/3M1_p22：triage 记 A 级——维持，本报告细化记 **R**（生成器
  已证 + 3M1 有现成孪生，比「机械求值」更廉）。
- s_init_list_alt_p23：triage 记 C 级 W5——**下调难度至 S**（HOL 脚本完备、
  周边件全✓、无 mnt11），且**不应排在 W5**，应进首发波（EAPGLE 消费族前置）。
- 其余 B/C 判定与现状相符。

## 4. 跨文件依赖与枢纽件

import 骨架：LA22←LA1+SphereKit；LA20←LA1+LA22；LA23←LA1+LA4+SphereKit；
LA24←LA1+LA17+LA20+LA23；LA27←LA1+LA24。LA21/25/26 不被 14 条直接依赖
（LA25 经 ZITHLQN 总装间接进入 EAPGLE）。

**枢纽件（闭一件解锁一片，按杠杆排序）**：

1. **AQICLXA_SLICE + FUNOUYH_SLICE（LA20:954/996）**：AQICLXA+FZIOTEF 的唯一
   前置。其 MMs 半需要 QKNVMLB 切片输运（QKNVMLB1/2/3_concl LA1:2801/2811/
   2823 全 sorry；LA35 忠实孪生 QKNVMLB1_LE4F/EQ4F/1/2/3_LE4/3_Eq4 全 sorry；
   HOL QKNVMLB.hl 10,699 行）。**修正 bola1 §8 波 1 定位**：`LKGRQUI→
   AQICLXA/FUNOUYH` 不是 W1 装配——SLICE 对是被 QKNVMLB kit 挡住的真数学
   （LKGRQUI 本体 HOL 269 行也调 QKNVMLB1 + SCS_HALF_SLICE_IS_A_SCS）。
   AQICLXA/FZIOTEF 本体（各 ≤60 行）应挂 W2* 待 SLICE，或随 QKNVMLB 波。
2. **OEHDBEN（LA20:1480，已证）**：纯装配枢纽，恰在等 3 个直源子件
   （BERAK/AQICLXA/FZIOTEF）；三者闭后 OEHDBEN 立即 cone-clean 并以 a01
   身份进 JEJTVGB_case_breakdown。OEHDBEN_PRIME(:1462)/SET_EQ_DIAG_STAB_6I1
   均✓。这是「子件闭→父链自愈」的样板：**14 条里 LA20 三条的下游父件全部
   已建好，债全在叶上**。
3. **ZITHLQN 总装（LA25:1004 处的 re-export 缺口）**：EAPGLE 唯一深前置。
   LA25 CASE 八件 + exists_vv3 + SMALL_BALL_ANNULUS_6 三件 + s_init_J_empty +
   dsv_scs_init 全✓，仅总装 kill 链（六项 JEJTVGB 逐项反证接线）缺位，
   估 150–350 行 S 级。闭 ZITHLQN 总装 → ZITHLQN_concl(LA1:653) 同步真化 →
   EAPGLE_p27 + EAPGLE_concl(LA1:757) 双闭。
4. **is_scs_funlist_basic_p22（LA22:1333，已证）**：三 R 件公共生成器；
   同 file 尚有 4T3-4T5/3T2-3T4/3T6-3T7/4I3/4M1/4M3-4M8 等 16 条同 kit
   可批量复制（其中 5 条已有 LA20 直证孪生）。
5. **BKOSSGE_p16（LA16:254，sorry 但已写大半）**：isScs 半直引
   is_scs_3T1/3T5_p22；MMs 半引 is_scs_3M1_p22 + XWNHLMD_MM_p26 +
   MMS_IMP_BBS_p28(✓)。波 1 三 R 件落地后只差 XWNHLMD 一族即可产 a23。

**消费面**：14 条几乎全为叶（外部消费文件 ≤3）：FZIOTEF→LocalConcl/LA29/
LA32；is_scs_3T1_p22→LA16/LA29；EAPGLE_p27/LFLACKU_p23→LA16/LocalConcl；
XWITCCN_CASE_*→0 外部（仅 UXCKFPE_p24 罩顶）；BERAK→0 外部（LA20 内部
OEHDBEN_PRIME）。**JEJTVGB_case_breakdown_p16（LA16:384，23 箭头假设箭头，
本体 sorry）**是 14 条中 6 条的共同下游根，其上游 kill 链（JEJTVGB.hl
「final kill」= 逐系统 {s}→∅ + EAPGLE + s_init_list_alt + LFLACKU）正是
s_init_list_alt/LFLACKU/OCBICBY/AQICLXA 族的汇聚点——但该根的施工主体属
JEJTVGL/mnt11 主线，不在本车道展开。

## 5. 波次方案（1–3 波）

### 波 1（首发波，机械/小件，预估 350–550 行）
- **清单**：is_scs_3T1_p22 → is_scs_3T5_p22 → is_scs_3M1_p22（生成器直套，
  3M1 可整段移植 LA20:209）；s_init_list_alt_p23（HOL JOTSWIX.hl:216-257
  直译，先证 aPro↔funlist k=5/k=4 两条恒等，再 rfl 六项）。
- **闸**：`THM @is_scs_3T1_p22` 等四件 + `#print axioms` 无 sorryAx 抽样；
  e2e 直源 **−4**。
- **红利**：BKOSSGE_p16 isScs 半即刻真化；is_scs_3M1 在图内双落（SCS_3M1_IS_SCS
  与 is_scs_3M1_p22 汇合后可择一去重）。
- **风险**：低。唯一注意点是 aPro 在 sInitListV39 是 let-内联（非独立 def），
  恒等两条要对内联体 unfold 后逐格 norm_num。

### 波 2（M 主攻 + EAPGLE，预估 2,500–4,000 行）
- **清单**：XWITCCN_CASE_4（先立模板：stable system→NOT_EMPTY→HDPLYGY 极小化
  →行解码→IN_NOT_EMPTY→TAUSTAR_EQ 负性转移）→ CASE_5/CASE_6 镜像 →
  CASE_3（tri_sy capstone，最重）；EAPGLE_p27（ZITHLQN 总装，不依赖波 1，
  可与 CASE 链并行）。
- **闸**：`THM @UXCKFPE_p24`（四 CASE 全闭后该总装 cone-clean）+
  `THM @EAPGLE_p27`；e2e 直源累计 **−9**。
- **风险**：CASE 链的 LA23 stable/tri-stable 前提（torsor 展开）是硬骨头，
  建议 CASE_4 支撑链走一遍再批量；ZITHLQN 总装的六项 JEJTVGB kill 接线
  形状要对 HOL ZITHLQN.hl:2465-§ 尾逐段对译，防「循环再出口」复发
  （ZITHLQN_p25 现状即教训）。
- **波 2*（条件位）**：若 QKNVMLB kit 单独立项并落地，AQICLXA/FZIOTEF
  （各 ≤60 行）在本波尾收割；否则滑波 3。

### 波 3（X 银行，与 mnt11/terminal 车道合并立项，本车道只留接口）
- **清单**：SCS_6I1_BERAK_BY_CSTAB（mnt11 三件 RRCWNSJ/JCYFMRP/JLXFDMJ）、
  OCBICBY_p22（Terminal.empty_* ×14）、LFLACKU_p23（taustar_taum_dfun 桥 +
  TAUM kit）、（QKNVMLB 未落地时的）AQICLXA/FZIOTEF。
- **闸**：e2e 直源 14→0；`JEJTVGB` 主链（mnt11 ⇒ JEJTVGB_assume_v39，
  JEJTVGB.hl:216）Lean 重放为总验收。
- **风险**：与 nli/terminal 银行同一座山（mnt11 109 条同根），不应在本
  车道发起；LA20 数值件（h0_LT_B/B_LE_CSTAB 等）已全✓，银行落地后装配
  侧当日可清。

### 下一编译窗首发建议
**波 1 四件**（is_scs_3T1/3T5/3M1_p22 + s_init_list_alt_p23）：全机械、
零 mnt11 依赖、HOL 脚本完备、预估 ≤550 行，可在一个编译窗内含 fix 循环
完成；战果确定（e2e 直源 −4，另红利 BKOSSGE_p16 半闭）。若窗口有裕量，
加插 **EAPGLE_p27/ZITHLQN 总装**（S 级、输入全✓、独立于波 1），把「装配
收尾」的红利提前兑现。

## 6. 与 LA1 经验（bola1）的最大差异

LA1 的折差主叙事是「LocalConcl 翻案 82→40」（直源位点虚高）；本簇相反——
**位点数 ≈ 真实施工量**（14 条sorry 全为真实债，无已闭翻案），折差发生在
**纵深**上：LA20 两条的 4 处阻塞注记已过时（半箭头免费），而 SLICE 前置
却被 bola1 低估为 W1 装配（实为 QKNVMLB 10,699 行真数学）——一升一降后
LA20 两件的净结论从「波 1 可收」改判「波 2* 待 kit」。

## 7. 未决问题

1. ZITHLQN 总装落点：写回 LA25（ZITHLQN_p25 位置，去 re-export 化）还是
   LA1（ZITHLQN_concl）——涉及 LA1 注册表冻结惯例，需编排者裁。
2. is_scs_3M1_p22 的施工法：整段移植 LA20:209 直证（快）vs 把 LA20 五条
   直证统一改走 is_scs_funlist_basic_p22 生成器（净，但动 LA20 已证件）——
   建议前者，留后者给 dedup 轮。
3. XWITCCN_CASE_3 的 HDPLYGY_CASE_30 连续性链（CONTINUOUS_ATTAINS_INF 一族）
   是否值得单独切给 euler/lp 车道复用，待 CASE_4 模板落地后评估。
4. LA23 头注「(proved)」错记与 LA20 五处过时 NEEDS 的注释翻新，建议随
   波 1 同窗顺手提交（纯注释 diff，零语义）。
