# DEF-FIX 章程：SCS_6I1 链上移 LocalConcl（方案 1B + LA16 勘误，2026-11-12，defix-small-w1）

> 依据：`~/c17_backup/lane_snapshots/dagcut-eval-w1/EVAL.md` §2.4 判词 **GO-DEF-FIX（方案 1B）**；
> 用户已批（`docs/priority-queue.md` 续1022，commit `e1c6d72e` 落账）。AGENTS §2：本单**不改任何
> 定义体/陈述**，只改**声明归属模块**，属 DEF-FIX 通道；零重命名、零 sorry 增减（净 ±3 是工单
> 钦定的纯位置债）。

## 0. 一句话

LA20 的 SCS_6I1 六边形 5 件（3 链 + `OEHDBEN_PRIME`/`OEHDBEN` 对）逐字节上移 `LocalConcl`，
零 import 边变化；**勘误**：EVAL 漏扫了 LA16:503 的活引用 `JEJTVGB_p16`（消费 `OEHDBEN`，而
LA16 无法 import LocalConcl——会形成环），其强制闭包 `JEJTVGB_p16` +
`nonlinear_imp_lp_main_estimate_p16` 两件随同上移；7 件全为纯搬运，树级 sorry 多重集不变。

## 1. 对象与勘误证据

- 工单原文（EVAL §2.3 方案 1B）：5 件、~60 行，活消费者 = `LocalConcl:5398` + `LocalConcl:5218`。
- **勘误（机器证据）**：`LocalAuto16.lean:503`（live code，`theorem JEJTVGB_p16` 证明体内）
  引用 `OEHDBEN h`；LA16 imports LA20（:99），而 LocalConcl imports LA16（:496）——LA16 若改
  import LocalConcl 即成环。只搬 5 件 ⇒ LA16 编译必炸（unknown identifier）。
- 勘误闭包：`OEHDBEN` 的外部消费者全树测绘 = {LA16:503, LocalConcl:5220, LocalConcl:5398}；
  `JEJTVGB_p16` 的外部消费者 = {LA16:532 `nonlinear_imp_lp_main_estimate_p16`}，后者**再无**
  外部消费者（LocalConcl 侧持有独立孪生 `_discharged`  twins，不受影响）。故强制搬迁闭包
  = 5 + 2 = **7 件**。两件 LA16 定理均为真证（非 sorry），sorry 净差保持工单钦定的 LA20 −3 /
  LocalConcl +3。
- 原工单"3 链 + OEHDBEN 对不可拆分"：LA20 内部 `OEHDBEN_PRIME:1922` 消费
  `SCS_6I1_BERAK_BY_CSTAB`、`OEHDBEN:1945` 消费 `OEHDBEN_PRIME`——只搬 3 链会炸留在 LA20 的
  OEHDBEN 对；只搬对又炸 LA16。结论：要么 7 件同搬，要么全不搬。

## 2. 搬迁清单（7 件，全部逐字节；零 import 边变化）

| # | 声明 | 性质 | donor（HEAD 位置） | target（patched） | 行数 |
|---|---|---|---|---|---|
| 1 | `SCS_6M1_IMP_SCS_6T1` | theorem（sorry） | LA20:1626–1635 | LocalConcl 新节 | 10 |
| 2 | `SCS_6I1_IMP_SCS_6T1` | theorem（sorry） | LA20:1637–1644 | 同节 | 8 |
| 3 | `SCS_6I1_BERAK_BY_CSTAB` | theorem（sorry） | LA20:1646–1652 | 同节 | 7 |
| 4 | `OEHDBEN_PRIME` | theorem（真证） | LA20:1906–1922 | 同节 | 17 |
| 5 | `OEHDBEN` | theorem（真证） | LA20:1924–1945（含 doc） | 同节 | 22 |
| 6 | `JEJTVGB_p16` | theorem（真证） | LA16:493–519 | 同节 | 27 |
| 7 | `nonlinear_imp_lp_main_estimate_p16` | theorem（真证） | LA16:529–532 | 同节 | 4 |

- 插入点：LocalConcl `/-! ### (d) Twin proved but the shape delta... -/` 节之前，新立
  `/-! ### SCS_6I1 hexagon chain upshift ... -/` 节；全部 7 件先于其消费者
  （`OEHDBEN_discharged`、`JEJTVGB_p16_discharged`）出现，作用域成立。
- 零 import 边变化：LocalConcl 已 import LA1–LA38 全部（含 LA20/LA16），LA20/LA16 无新增 import。
  SCC 图不变 ⇒ 零环（LocalConcl 零 importer）。
- 附带的注释卫生修订（非陈述）：LA20 头部账本（过期"7 sorries"清零注记）、LA16 FILE MAP 与
  Section A 头、LocalConcl 三处消费点 doc 引用（`LocalAuto16.JEJTVGB_p16` → 本文件自有）。
- **预存 staleness 说明**：LA20 头部"Remaining sorries (7)"在 HEAD 即已过期（AQICLXA/FZIOTEF
  四件 la20-bank-w1 波已真证），HEAD 实际 code sorry = 3 = 本次搬走的 3 件；本 patch 顺手更正。

## 3. 陈述冻结证据（机器自检）

`logs/byte_check_6i1.py`（sha256 比对，RC=0 全 OK）：

- 7 个搬迁块 donor HEAD 文本 vs LocalConcl patched 文本**逐字节相等**（7/7 OK）。
- 7 个名字在 patched LA20/LA16 **全部缺席**、在 LocalConcl **各恰好声明一次**（7/7 OK）。
- `logs/selfcheck_final.log`：全树多重集比对（comment/string-aware 扫描器）——DECL 名字+kind
  多重集、SORRY/`native_decide`/`admit` 总数全等；首轮 run 的 SORRY 总数差 +3 经查证 = **并发
  落库的 dagcut-w2/w2 波改了 LA27（3 个 sorry 证真、陈述未动，DECL/SIG 故不变）的基线偏斜**，
  与本 patch 无关（本 patch 文件级 delta：LA20 3→0、LocalConcl 21→24，净 0）。排除 LA27 复跑
  全等。搬迁块的陈述级逐字节由 byte_check 承担（SIG 全等首轮亦已 PASS：122831 条）。

## 4. 编译验证（岛协议 farm，串行 nice -n 19，压力级 1）

方法：`.lake/build/lib/lean` 逐 entry 符号链接 farm（跨卷不能 hardlink）；重编模块先
`rm farm/.../<mod>.olean` 再 `lean -o` 进 farm（防止经链接写回主 .lake）；下游按序对 farm 解析。

| 编译对象 | RC | errors | sorry-decls | 备注 |
|---|---|---|---|---|
| LA20（donor，删 5 件） | 0 | 0 | 0 | 头部账本修订后重编同 RC=0 |
| LA16（donor，删 2 件，对 farm 新 LA20 olean） | 0 | 0 | 1 | = 基线（JEJTVGB_case_breakdown 等仍在） |
| **LocalConcl（target，+7 件）** | **0** | **0** | **24** | = 基线 21 + 3（搬入的 3 件 sorry），符合工单 |
| LocalConcl `#print axioms` 抽检 | — | — | — | `JEJTVGB_p16_discharged`/`OEHDBEN_discharged` 等带 `sorryAx` 的面与基线同因（消费搬后 `OEHDBEN`，声明逐字节未变） |

## 5. 不验证项与留给闸门/编排者的验收

- `Kepler.Assembly`/根面未重编（体量决策；Assembly 消费 LocalConcl 的 `_discharged` twins，
  其上游声明面不变）。根面 `#print axioms` 由编排者亲跑（AGENTS §4 验收口径 ③）。
- 全树其余模块：LA20/LA16 的**被删名字**的外部消费测绘 = {LocalConcl×2, LA16×2}，已全部
  在 patch 内消化；其余导出名字未动。闸门的模块步/roots 步兜底。
- `git apply --check`：相对基线 HEAD `e7672ae5`（`logs/git_apply_check_6i1.log`）。

## 6. 落库后下一步（不在本补丁）

证明波在 LocalConcl 就地证 3 件 sorry（JCYFMRP_p27 / JLXFDMJ_p27 / RRCWNSJ_p26 / MXQTIED_p26
hmn-ful 路线全开；hmn-free 路线 LA1 四 `*_concl` wire 仍在用户保留区）。LocalConcl:5398 的
`(OEHDBEN h)` 已变本文件局部引用，无需再改。
