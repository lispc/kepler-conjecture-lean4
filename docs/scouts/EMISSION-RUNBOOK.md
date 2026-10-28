# EMISSION-RUNBOOK — 22 张 MISSING 证书（ZTGIJCF4×16 + QITNPEA1×6）生成器式发射

> 车道 missingcert-scout，2026-10-27。基线 `1bd6a3fd`。**本 RUNBOOK 由侦察
> 车道按「只查不发」纪律产出：其中任何命令在写就时点均未执行过**；编排者
> 首跑时从 §A0 冒烟开始，勿跳过校准步。

## ⚠️ 头部纪律（先读，违反即报废）

1. **9-20 农场纪律（spbug2）**：2026-09-20 W6 修复「spbug2 栈污染」前的
   旧版 bb_arb 产的**一切带析取证书按不健全处理**（disj 判据读错栈位 ⇒
   任意盒假命中 disj；实证：RQWUDDU 历史证书精确复核 0/46 通过，
   QITNPEAv2 0/16，证据链见 nli-b-toolchain 快照 DELIVERY §3 +
   本目录 `exact_recheck.py` 双向复验）。**本次 22 条重发射必须用现役
   HEAD 版 bb_arb.c 重编的二进制**（§A0 配方），并逐案过 §A4 精确复核。
2. **var_lt 修复已入库**（emit_rpn.py，commit 39251711）：现役源码为修复
   版，直接可用；不得用旧工作区副本发射（两族 case 无 var_lt 析取项，
   但纪律上统一）。
3. **零主仓写**：case/cert/params/StageA/模块产物全入工作克隆
   `/tmp/<lane>/repo`（APFS 克隆）与车道快照目录；主仓只在 integrate_lane
   落库时经 pathspec 限定提交触及（farm-runbook 步 8）。
4. **锁**：一切 `lake build` 走 `/tmp/kepler_build_lock.sh`
   （`source` 后 `lock_build nice -n 19 lake build <target>`）； harness
   60 min 杀后台 → 到点重跑同一条命令（lake 按 olean 断点续跑）。

## 0. 发射对象与两条通路

22 条 = PA21 生成族（语句级忠实性已由 PA21 `example`/`rfl` 机器锚锁定）：

| 族 | 条数 | HOL idv 模板 | Assembly 桩 | bank（PA21） |
|---|---|---|---|---|
| QITNPEA1 | 6 | `QITNPEA1 i3 i4 9063653052 A`，i3∈{1,2}, i4∈{0,1,2} | Assembly.lean:901-931 | bank_QITNPEA1tmpl :681（γ/w > 0.0057 ∨ rad2X > 2） |
| ZTGIJCF4 | 16 | `ZTGIJCF4 i3 i4 i5 i6 1821661595`，i∈{0,1}⁴ | Assembly.lean:1021-1111 | bank_ZTGIJCF4tmpl :850（γ/w + m·β > a+b·dih ∨ rad2X > 2） |

- **通路 A（直配，推荐先走）**：本目录 `ineqs_tmpl_ast.json`（22 条
  y-空间 AST 记录，由 `gen_tmpl_ast.py` 合成并过 PA21 机器锚自检）→
  emit_rpn 出 case → bb_arb 解 → 复核 → gen-11 发射。case 语句与 bank
  语句**逐字同构**，胶水走 farm B3+B4 桥（同 2134082733 形）。
- **通路 B（prep 兜底）**：`out/ineqs_prep_ast.json` 已含 186 条 prep
  剖分件（ZTGIJCF4×162 split 2-32/例 + QITNPEA1×24 split 2-8/例），
  case 层零新代码；但 prep 件是 x-空间 + 2h0 截断 + γ 展开
  （prep.hl:26431+），与 bank 之间的桥 = merge_ineq.hl:1813（ztg4 合并）
  / :4796（QITNPEA1）的 Lean 移植，**数学胶水量大且无库内先例**。仅当
  通路 A 某 (i3..i6) 实例在 §A3 阶梯顶预算仍 rc=2 时按例启用，且需先发
  prep 桥设计车道。

## A. 通路 A：直配发射（两族命令序列）

记 `REPO=/Users/zhangzhuo/repos/kepler-conjecture-lean4`、
`SNAP=/Users/zhangzhuo/c17_backup/lane_snapshots/missingcert-scout`、
`LANE=/tmp/<lane>`（工作克隆 `$(REPO)` 的 APFS clone 放 `$LANE/repo`）。

### A0 工具链自举（一次性；/tmp 旧产物已被清，必须重编）

```sh
# Homebrew flint 3.6.0（nli-b-toolchain DELIVERY §1 配方，现役 HEAD 源）
clang -O2 $REPO/pipeline/interval/test_arb.c -o $LANE/test_arb \
  -I/opt/homebrew/include -L/opt/homebrew/lib -lflint -lmpfr -lgmp -lm
clang -O2 -std=c99 -Wall -Wextra $REPO/pipeline/interval/bb_arb.c -o $LANE/bb_arb \
  -I/opt/homebrew/include -L/opt/homebrew/lib -lflint -lmpfr -lgmp -lm
$LANE/test_arb          # 期望 rc=0 且打印 OK（53-bit π/√2 球自检）
$LANE/bb_arb            # 期望打印 usage（exit 3）＝二进制可用
# 冒烟（可选但推荐）：1 叶案端到端
$LANE/bb_arb $REPO/pipeline/interval/out/cases/TSKAJXY-delta_x4.json \
  --cert $LANE/TSKAJXY.smoke.cert.json --max-nodes 65536   # 期望 rc=0, 1 叶
python3 $SNAP/exact_recheck.py $REPO/pipeline/interval/out/cases/TSKAJXY-delta_x4.json \
  $LANE/TSKAJXY.smoke.cert.json                            # 期望 1/1 PASS rc=0
```

### A1 case 生成（emit_rpn；AST 已备好，见本目录 ineqs_tmpl_ast.json）

```sh
mkdir -p $LANE/cases && cd $REPO
python3 pipeline/interval/emit_rpn.py \
  --ineqs $SNAP/ineqs_tmpl_ast.json \
  --defs  $REPO/pipeline/interval/out/defs.json \
  --outdir $LANE/cases --no-xcheck \
  --ids "QITNPEA1 2 2 9063653052 A,QITNPEA1 2 1 9063653052 A,QITNPEA1 2 0 9063653052 A,QITNPEA1 1 2 9063653052 A,QITNPEA1 1 1 9063653052 A,QITNPEA1 1 0 9063653052 A"
# ZTGIJCF4 同法，--ids 逗号串 = 16 个
#   "ZTGIJCF4 i3 i4 i5 i6 1821661595"（(i3,i4,i5,i6) 跑遍 {0,1}⁴）
```
产物（safe_name 规则）：`$LANE/cases/QITNPEA1_2_2_9063653052_A.json`、
`$LANE/cases/ZTGIJCF4_1_1_1_1_1821661595.json` 等 22 件。
emit_rpn 自检（Fraction 求值器）会在开头跑，须「全部通过」才继续。

### A2 case 入库前核查（每案 ~2 min，人工）

```sh
python3 - <<'EOF'
import json,sys
p=sys.argv[1]; d=json.load(open(p))
assert d['id']==p.split('/')[-1], d['id']
assert d['vars']==['hminus','y1','y2','y3','y4','y5','y6'], d['vars']   # 7 维（hminus=第0维，盒[6/5,13/10] choice 外扩）
assert len(d['box'])==7 and d['orig_op']=='disj'
assert len(d['disj'])==1, d['disj']                                     # 恰 1 条备选（rad2X>2）
assert not any('"log"' in json.dumps(x) for x in [d]), 'matan/log 分支出现→停，报告编排者'
print('OK', d['id'], 'ops=', d['stats']['ops'], 'ite=', d['stats']['ite'])
EOF
```
另人工核两点：① notes 无「特征方程丢弃」以外的意外语义裁剪；② 主 prog
含 atan/sqrt/ite（dih_y 巢）属预期（与 QITNPEA_2134082733.json 同形，
对照件在主仓 out/cases/）。

### A3 求解（bb_arb；阶梯预算，先校准后铺开）

**首两案校准（量级实测，约机时 0.5-2h）**：
`ZTGIJCF4 0 0 0 0`（rest-params 注记的最简实例：盒全 [2,2hminus]、w=1、
条件乘子恒 0）与 `QITNPEA1 1 1`（w=3、y3/y4 均 [2hmin,2hplus]）。

```sh
mkdir -p $LANE/certs
CASE="ZTGIJCF4_0_0_0_0_1821661595"    # 校准例 1；校准例 2 = QITNPEA1_1_1_9063653052_A
$LANE/bb_arb $LANE/cases/$CASE.json --cert $LANE/certs/$CASE.cert.json \
  --max-nodes 65536                                    # 第 1 档（~64k）
# rc=0 → 进 A4；rc=2 → 逐档加码（nli-b-toolchain §2 阶梯）：
#   --ite-hull2 --tm-div2 --max-nodes 4000000
#   仍 rc=2 → --max-nodes 20000000（TM closed 计数看日志）
#   20M 仍不闭 → 该案转通路 B（prep 剖分件）或 prep 车道，勿硬泡
```
其余 20 案按校准结果选档铺开（互独立，可串行 nice 19 或多机分发）。

### A4 精确有理复核（每案必过；9-20 纪律的机械执行点）

```sh
python3 $SNAP/exact_recheck.py $LANE/cases/$CASE.json $LANE/certs/$CASE.cert.json -v
# 期望尾部: PASS N / FAIL 0 / UNVERIFIED 0，rc=0
# FAIL>0     → 证书不健全（spbug2 型假命中或求解 bug）→ 该案作废重解/上报
# UNVERIFIED>0 → 出现 div 跨 0/log 分支等脚本不覆盖语义 → 人工核，不得计通过
```
（已双向验证：TSKAJXY 好证书 1/1 PASS；RQWUDDU spbug2 历史证书 0/46 FAIL。）

### A5 gen-11 发射（emit_lean.py；atan/sqrt 案走两段参数化）

```sh
MOD=CZTGIJCF4_0_0_0_0          # 命名 = C + bank 去 bank_（CZTGIJCF4_1_1_1_1 / CQITNPEA1_2_2 …）
mkdir -p $LANE/$MOD
# Stage A：sqrt/atan 槽参数化驱动（产 params JSON）
python3 $REPO/pipeline/interval/emit_lean.py $LANE/cases/$CASE.json \
  $LANE/certs/$CASE.cert.json $LANE/$MOD/StageA.lean --fill --stage-a
cd $LANE/repo/lean && lake env lean --run $LANE/$MOD/StageA.lean > $LANE/$MOD/params.txt
# Stage B：BBTreeGD 分片（disj 案标准通路，rest 1 6096597438b 先例）
python3 $REPO/pipeline/interval/emit_lean.py $LANE/cases/$CASE.json \
  $LANE/certs/$CASE.cert.json $LANE/repo/lean/Kepler/Interval/Cases/$MOD.lean \
  --bbg --disj-gd --params=$LANE/$MOD/params.txt
```
产物 = `$MOD.lean`（顶装配 `bb_sound_disjG`，形同 C6096597438b.lean）+
`Cases/$MOD/{Base,Shard*.lean}`；模块 7 维（ρ : Fin 7 → ℝ，第 0 维 hminus）。

### A6 构建闸 + 探针（farm-runbook 步 3/4/5 原样）

```sh
cd $LANE/repo/lean && source /tmp/kepler_build_lock.sh
lock_build nice -n 19 lake build Kepler.Interval.CertG        # 前置闸：demo 债拦截（farm 步 3）
lock_build nice -n 19 lake build Kepler.Interval.Cases.$MOD   # 分段，~90min/段，计数
ls .lake/build/lib/lean/Kepler/Interval/Cases/$MOD/ | grep -c '\.olean$'
cat > $LANE/probe.lean <<'EOF'
import Kepler.Interval.Cases.CZTGIJCF4_0_0_0_0
#print axioms Kepler.Interval.Cases.CZTGIJCF4_0_0_0_0_pos
EOF
lake env lean $LANE/probe.lean   # 期望标准三 [propext, Classical.choice, Quot.sound]
```
（`decide=false` 复现 CertG.lean:248/:420 → 按 RUNBOOK-G4 §1 选项 A/B 处理。）

### A7 入库与粘合

- 证书模块：farm-runbook 步 6（olean 回灌）→ 步 8（integrate_lane）；
- 粘合：GlueTemplate 实例化，桥类 = **B3（gamma4fgcy）+ B4（spine
  aSpine5+bSpine5·dihY）+ B1（dihY atn2）+ rad2X 支 B0 候选**；ZTGIJCF4
  另有条件乘子 `if Σ=2 ∧ i4=1`——除 (0,1,0,0) 外全部 simp 闭（rest-params
  逐例注记：1_0_1_1 等案 Σ≠2 乘子=0；(0,1,0,0) 恒最简）；盒端点第 0 维
  用 `mi_hminus_prop`（A1/A2 先例），√8/2hplus/2hminus 端点 dyadic 外扩
  值见 case-format.md §4。

## B. 通路 B：prep 兜底（仅按例启用）

```sh
cd $REPO && python3 pipeline/interval/emit_rpn.py \
  --ineqs pipeline/interval/out/ineqs_prep_ast.json \
  --defs  pipeline/interval/out/defs_prep.json \
  --outdir $LANE/cases_prep --no-xcheck \
  --ids "prep-ZTGIJCF4 1 1 1 1 1821661595 split(0/32),…(该实例全部 split)"
# 求解同 A3（Azure 实测 per split 85–2313 s，机器 2014 年代 → 本机应更快）
# ⚠️ 上游差异：prep 件为 x-空间（x_i=y_i²）+ y1 截 2h0 + γ 线性展开 +
#    β→beta_bumpA_y 近似；Lean 侧 bank 桥 = merge_ineq.hl:1813-2303（ztg4）
#    / :4796（QITNPEA1）移植，无库内先例 —— 启用本通路前先发桥设计车道。
```

## C. 校验汇总与回滚点

| 闸 | 命令 | 期望 |
|---|---|---|
| case 语义 | A2 核查脚本 | 7 维、disj=1、无 log、id 对桩 |
| 证书健全 | A4 `exact_recheck.py` | FAIL=0 且 UNVERIFIED=0 |
| 产物对桩 | emit_lean 头注 + farm 步 2 | box 逐端点、叶数与 cert 一致 |
| 内核 | A6 `lake build` + `#print axioms` | 标准三，零 sorryAx |
| 落库 | farm 步 8 integrate_lane + 步 9 计数 | `grep -c 'nliRest.*:= sorry' Assembly.lean` 57→逐条 −1 |

回滚点（对应 farm §2 四点，+本通路特有两条）：
1. **AST 层**：`ineqs_tmpl_ast.json` 是唯一合成源，入快照目录存档；case
   异常 → 改 generator → 重跑 A1（case 文件全部可弃重生成，零成本）。
2. **求解层**：cert 每案独立；某案 rc=2/复核 FAIL → 只弃该案，重解或转
   通路 B，不阻塞他案（分片相互独立）。
3. 发射/构建/回灌/落库层：farm §2 四点原样（源 md5 核对、快照目录备齐
   才动主仓、单条独立 commit 可 revert、批末三处计数对账）。

## D. 发射量级估计（两族）

| 项 | QITNPEA1 ×6 | ZTGIJCF4 ×16 |
|---|---|---|
| case 维度/ops | 7 维；预计 ~21k ops（对照 2134082733 同形案 20,940） | 同左（w/m 不同仅常数） |
| 求解预算 | 64k 起步；盒较小（y5,y6 亚临界） | 64k→4M→20M 阶梯；√8 角盒最多 4 维 |
| 求解机时/案 | 分钟–tens of min（Azure 同族 prep split 85–2,313 s 锚） | 分钟–小时级；20M 不闭率未知（首两案校准定） |
| 叶数 | 未知；参考同族 FB 案百–千叶级 | 未知；同上 |
| 发射+构建/案 | 百叶级 ≈ 1h（farm §3）；万叶级按 86 分片/h 外推 | 同左；16 条建议 3 小批（farm B5 计划） |
| 人工胶水/案 | 桥齐后 1.5–2.5 h（farm §3 tmpl 行） | 同左（B3 首例另计 6-10 h） |

## E. 风险清单（发射前必读）

1. **直配求解闭合性未知（最大不确定）**：Azure 原管线从未直配求解过
   y-空间 tmpl 件（全部走 prep 剖分）；ZTGIJCF4 的 √8 角盒 + γ/dih 双
   曲面可能重演 RQWUDDU 型切界层卡死。缓解：§A3 首两案校准 + 20M 阶梯
   上限 + 通路 B 按例兜底。
2. **case 语义漂移**：合成 AST 若与 ineq.hl 模板有出入（如 beta_bump_lb
   项——QITNPEA1 按 2012-12-01 注记删除、PA21 转录同口径），粘合会在
   evalReal 桥断裂。缓解：gen_tmpl_ast.py 已对 PA21 机器锚自检；首件
   发射后人工对一遍 bank_QITNPEA1tmpl/bank_ZTGIJCF4tmpl 逐节点。
3. **log/matan 与脚本盲区**：两族理论上不触 matan（176 条中仅 6 条触及，
   均非本两族形状），A2 脚本会硬拦；exact_recheck 不覆盖 log——出现即
   上报而非带病通过。其余 UNVERIFIED（div 跨 0）同。

—— 完 ——
