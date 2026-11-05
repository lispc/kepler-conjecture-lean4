# case-format.md — case JSON / cert JSON / 发射模块格式解剖 + 22 条 tmpl 族参数锚

车道 missingcert-scout，2026-10-27。样本：入库先例
`lean/Kepler/Interval/Cases/CTSKAJXY_delta_x4.lean`（单叶单目标）、
`pipeline/interval/out/cases/QITNPEA_2134082733.json`（与 tmpl 族同构的
显式 disj 案）、`lean/Kepler/Interval/Cases/C6096597438b{.lean,/}`（N2
rest 1 分片 disj 先例）、`nli-b-toolchain` 快照两张历史 cert。

## 1. case JSON（emit_rpn.py v1 schema；`arb-layer.md §1` 对齐）

| 字段 | 型 | 语义/实测样值（QITNPEA_2134082733.json） |
|---|---|---|
| `id` | str | 原始 idv 逐字（`"QITNPEA 2134082733"`）；文件名 = safe_name(idv) = `re.sub(r"[^A-Za-z0-9._-]+","_",idv).strip("_")+".json"` |
| `orig_op` | str | 核心比较算子；多路析取时 `"disj"` |
| `vars` | [str] | 有序变量表；**hminus 在场时恒为第 0 维**：`["hminus","y1".."y6"]`（7 维）。tmpl 族两案均触 hminus（γ/dih_y 闭包内）→ 7 维 |
| `box` | [{num,den}]²ⁿ | 与 vars 同序的精确有理端点，dyadic 外扩到 2^-q 网格；样值 §4 表 |
| `q` | int | 网格指数，默认 −30 |
| `prog` | RPN 流 | 主目标（第一析取项）a−b 编码，叶闭合判据 **lo > 0**（严格） |
| `disj` | list | 其余析取项：`{"prog":[…],"orig_op":">"}`（同 lo>0 闭合）或 `{"var_lt":[i,j]}`（判据 hi_i < lo_j）；tmpl 族恰 1 条（rad2X>2） |
| `notes` | [str] | 语义裁剪记录；tmpl 族预期出现「核心为 2 路析取…」「choice const hminus: 特征方程丢弃, 按外扩盒 [6/5,13/10] 处理」 |
| `stats` | {ops,ite,depth} | 对照件 2134082733：ops=20,940 / ite=63 / depth=4 |

RPN 指令（栈机、扁交流）：`["push_var",i]`、`["push_const",{num,den}]`、
`add/sub/mul/neg/div/sqrt/atan/sin/cos/abs/log`（二元者弹二压一）；
`{"ite":{"cond":…,"then":…,"else":…,"mode":"lt"|"eq"}}` 结构化 guard 占流
一位（lt：hi<0→then、lo≥0→else、跨 0→STRADDLE 二分；eq：恰 [0,0]→then）。
命名常量展开期全部内联（pi→4·atan(1)、sqrt8→sqrt(8)、其余查 defs.json；
acos/asin 半角恒等式化掉；log=matan 负分支规格偏离，**tmpl 族不触**，
若出现即停线）。hminus 的 choice 定义按 [6/5,13/10] 外扩盒处理
（超集，sound）。

## 2. cert JSON（bb_arb `--cert` 输出）

```json
{ "id": "<idv>", "prec": 64,
  "root_box": [[{"num":..,"den":..},{..}]×n],          // = case.box（应逐端点一致）
  "leaves": [ {"box": […×n], "hit": "main"|"disj:N"} , …],
  "nodes": <总结点数> }
```
- `hit:"main"` → 叶由 case.prog 闭合；`"disj:N"` → 由 case.disj[N] 闭合
  （var_lt 析取项闭合时标签含 var_lt 信息；tmpl 族无）。
- 精确复核器：本目录 `exact_recheck.py`（Fraction 栈机全量重放；已双向
  验证：TSKAJXY 1/1 PASS、RQWUDDU spbug2 历史件 0/46 FAIL）。

## 3. 发射产物（gen-11 emit_lean.py）两形

**单叶单目标形**（先例 CTSKAJXY_delta_x4.lean，入库全文 45 行）：
`<Mod>Expr : IExpr n`（RPN 镜像为 IExpr 项）+ `<Mod>Box : Fin n → DInterval`
（`![]` 字面 dyadic 端点）+ `checkPos … = true := by decide` +
`.leaf` 树 + `covers := trivial` + `boxSub`（fin_cases+decide）+
`<Mod>_pos : ∀ ρ, boxMem Box ρ → 0 < evalReal ρ := bb_sound …`。

**分片 disj 形**（先例 C6096597438b，78 叶；atan/sqrt 案经 Stage A/B）：
`<Mod>Goals`（目标列表）+ `BBTreeGD`（`.posLeaf box k e el rfl (Sem _) (by decide)` /
`.varLtLeaf`）+ `{Mod}MkExprK` 参数化工厂 + `rfl` 桥 `{Mod}SemK` +
`<Mod>_pos : ∀ ρ, boxMem … → ∃ g ∈ Goals, g.eval ρ := bb_sound_disjG …`。
文件布局：`Cases/<Mod>.lean`（顶部装配）+ `Cases/<Mod>/{Base.lean,Shard<N>.lean}`。
模块名 = out.lean basename（无 --name 时）。`#print axioms <Mod>_pos`
期望标准三（propext/Classical.choice/Quot.sound）。

## 4. 22 条 tmpl 族参数锚（RUNBOOK 通路 A 的合成输入依据）

### 4.0 盒端点 dyadic 词典（实测自 2134082733.json，q=−30 外扩）

| 模板词 | 精确值 | case 端点 dyadic |
|---|---|---|
| `&2` | 2 | `2/1` |
| `&2 * hminus`（choice [6/5,13/10]） | 2·[1.2,1.3] | lo `2576980377/2^30`，hi `2791728743/2^30` |
| `&2 * hplus`（=1.3254） | 2.6508 | hi `711568707/2^28` |
| `sqrt8` | √8≈2.8284271247 | hi `759250125/2^28` |
| hminus（第 0 维） | [6/5,13/10] | `[322122547/2^28, 348966093/2^28]` |

### 4.1 QITNPEA1 族 ×6（PA21:657-702；ineq.hl:827-862）

盒：y1∈[2hmin,2hpl]，y2∈[2,2hmin]，y3∈[x i3,X i3]，y4∈[x i4,X i4]，
y5,y6∈[2,2hmin]；x=[2, 2hmin, 2hplus, √8]，X i=x(i+1)。
目标：`gamma4fgcy y1..y6 lmfun / w > 0.0057 ∨ yOfX rad2X … > 2`；
**w = 1 + [i3=1] + [i4=1]**（beta_bump_lb 项按 2012-12-01 注记删除，
PA21 转录同口径——「参数来源」已由 PA21 `example` 机器锚锁定，非猜测）。

| idv | case 文件名 | i3,i4 | y3 盒 | y4 盒 | w |
|---|---|---|---|---|---|
| `QITNPEA1 2 2 9063653052 A` | QITNPEA1_2_2_9063653052_A.json | 2,2 | [2hpl,√8] | [2hpl,√8] | 1 |
| `QITNPEA1 2 1 …` | …_2_1_… | 2,1 | [2hpl,√8] | [2hmin,2hpl] | 2 |
| `QITNPEA1 2 0 …` | …_2_0_… | 2,0 | [2hpl,√8] | [2,2hmin] | 1 |
| `QITNPEA1 1 2 …` | …_1_2_… | 1,2 | [2hmin,2hpl] | [2hpl,√8] | 2 |
| `QITNPEA1 1 1 …` | …_1_1_… | 1,1 | [2hmin,2hpl] | [2hmin,2hpl] | 3 |
| `QITNPEA1 1 0 …` | …_1_0_… | 1,0 | [2hmin,2hpl] | [2,2hmin] | 2 |

锚：Assembly.lean:901-931（rest 25-30 桩）↔ PA21:692-702
bank_QITNPEA1_2_2…1_0 ↔ lo/hi/genMid 定义 PA21:670-678。

### 4.2 ZTGIJCF4 族 ×16（PA21:835-901；ineq.hl:456-499）

盒：y1∈[2hmin,2hpl]，y2∈[2,2hmin]，y3..y6∈[x i,X i]；x=[2, 2hmin, √8]。
目标：`gamma4fgcy … / w + m·beta_bump_lb > aSpine5 + bSpine5·dihY ∨ rad2X > 2`；
**w = 1 + #[i∈{1}] over i3..i6；m = 1 当且仅当 (i3,i4,i5,i6)=(0,1,0,0)**
（w=2 ∧ i4=1；PA21:905-911 example 机器锚）。
常数：a_spine5=0.0560305、b_spine5=−0.0445813、beta_bump_lb=−0.005
（defs.json 字面）。

| (i3,i4,i5,i6) | w | m | 备注（rest-params 注记） |
|---|---|---|---|
| 0,0,0,0 | 1 | 0 | 全 [2,2hmin]、分母 1、乘子恒 0 —— **校准首例** |
| 0,0,0,1 / 0,0,1,0 | 2 | 0 | |
| 0,0,1,1 / 0,1,0,0 / 1,0,0,0 | 2 | 1 仅 (0,1,0,0) | (0,1,0,0)=恰 y4 critical，乘子=1 |
| 0,1,0,1 / 0,1,1,0 / 1,0,0,1 / 1,0,1,0 | 3 | 0 | i4=1 案乘子=0（Σ≠2） |
| 0,1,1,1 / 1,0,1,1 / 1,1,0,0 | 4 | 0 | |
| 1,1,0,1 / 1,1,1,0 / 1,1,1,1 | 5(m=0) | 0 | 全 critical w=5 |

锚：Assembly.lean:1021-1111（rest 32-47 桩）↔ PA21:864-896
bank_ZTGIJCF4_* ↔ lo/hi PA21:844-847；**全簇最重例外 = 1_1_1_1**。

### 4.3 prep 件参数对照（通路 B 用；与 4.1/4.2 的差异）

`out/ineqs_prep_ast.json` 记录 idv `prep-<族> <参数> split(k/N)`：
ZTGIJCF4 ×162（N=2..32，16 例齐）、QITNPEA1 ×24（N=2..8，6 例齐），
vars = `["x1".."x6"]`（x_i=y_i²）、盒为平方词表
（如 (2hmin)² = `#2.0*hminus*#2.0*hminus`，2h0=2.52 截断），
体为 γ 线性展开（含 unit6/vol_x/gchi*_x/dih_x，β→beta_bumpA_y 近似）。
split 维 = 最右非退化维（如 1111 切 x6 32 段；QITNPEA1 2 2 切 x3/x4 各 2 段）。
defs_prep.json 为配套闭包（hminus/a_spine5/… 全在）。
HOL 侧 bank 桥规格：merge_ineq.hl:1813-2303（ztg4 合并）/:4796+（QITNPEA1）。

## 5. 已知格式雷区

1. **safe_name 尾下划线**：idv 含 `(`/`)`/空格 → 文件名多 `_`；id 字段
   才是权威（PEMKWU↔PEMKWKU 型漂移在步 1a 拦截——本两族 idv 与 bank
   名去前缀后一致，无漂移）。
2. **hminus 第 0 维**：发射模块为 Fin 7 → 粘合 boxMem 第 0 维必须
   `mi_hminus_prop`（勿抄 A1 的 6 维形态）。
3. **双空格 idv**：库内存在 `QITNPEA  5400790175 a`（双空格）型 idv；
   tmpl 族 idv 为单空格，emit_rpn --ids 匹配是全串精确匹配，逗号串里
   勿多空格。
4. **var_lt**：两族无 var_lt 析取项；如 A2 核查发现 var_lt 出现即说明
   合成源错位，停线。
