# EVIDENCE — `nli-bank-triage`（只读侦察）

HEAD: `0abccb51`（`git log --oneline -1`）。平台 darwin/arm64，`lean-toolchain` = `leanprover/lean4:v4.32.2`。
**本车道未写任何主仓 tracked 文件、未 commit**；探针全部在 `/tmp/nlibank/`，产物在
`~/c17_backup/lane_snapshots/nli-bank-triage/`。

> **收尾时 `git status` 的 `M lean/Kepler/Assembly.lean` 不是本车道造成的**：
> 并行 DEF-FIX 车道 `adm3-realify`（2026-11-06）把 `Adm3` 的占位 `True` 尾换成了真结论
> （`Kepler.Text.TameLp.aTame ≤ setSum (setOfTrianglesMeetingNode H x) w`），
> diff = 1 hunk / +6 −2，与本车道无关。本车道全程只读该文件。

---

## §1 68 条的枚举（可复现）

```
$ cd lean
$ grep -c "theorem nliRest.*:= sorry" Kepler/Assembly.lean      → 55
$ grep -c "theorem nliTsk.*:= sorry"  Kepler/Assembly.lean      → 8
$ grep -c "theorem nliCell3.*:= sorry" Kepler/Assembly.lean     → 5
$ wc -l Kepler/Assembly.lean                                    → 7202
```
55+8+5 = **68**，与工单锚点一致（`nliRest*` 55 / `nliTsk*` 8 / `nliCell3*` 5）。

银行定义位置（`Kepler/Text/PackingAuto21.lean`）：
```
206 bank_QZECFICwt0   214 …corner   221 …sqrt8   230 …wt1   241 …wt2A
268 bank_TSKAJXYGXSA  308 XLLIPLS   316 WKGUESBsym 326 IYOUOBFsharpv2 334 IYOUOBFsym
343 RIBCYXUsym        354 RIBCYXUsharp 362 TADIAMB
437 bank_1965189142a … 681 bank_QITNPEA1tmpl … 850 bank_ZTGIJCF4tmpl … 915 ZTGIJCF0
920 bank_GCKBQEA      928 bank_RQWUDDU
```

## §2 探针环境基线（证明 `lake env lean` 单文件可用、oleans 已就绪）

`/tmp/nlibank/probes/p000_harness.lean`（15 行）：
```lean
import Kepler.Text.PackingAuto21
namespace NliBankProbe
open Kepler.Text
theorem trivial_test : bank_6096597438a := by
  intro h _ _
  have hne : (h0 - 1 : ℝ) ≠ 0 := by norm_num [h0]
  have hlf : lfun 1 = 1 := by unfold lfun; exact div_self hne
  rw [hlf]; norm_num
#print axioms NliBankProbe.trivial_test
end NliBankProbe
```
```
$ nice -n 19 lake env lean /tmp/nlibank/probes/p000_harness.lean ; echo RC=$?
'NliBankProbe.trivial_test' depends on axioms: [propext, Classical.choice, Quot.sound]
RC=0                                    # wall 5.1s
```

## §3 朴素路线失败（记录，避免后人重踩）

`p010_bixpcgwb.lean`（19 行）：直接对 `60 < deltaY` 上 `nlinarith [sq_nonneg y1, …]`。
```
$ nice -n 19 lake env lean /tmp/nlibank/probes/p010_bixpcgwb.lean
... a✝ : 0 ≤ deltaX … ⊢ False
failed
'NliBankProbe.gwb_try' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
原因：`deltaY` 对 `x_i = y_i²` 是**三次**（不是二次），`nlinarith` 的二次乘积证书找不到；
`deltaX` 的逐项区间界在盒上是 −2550 量级（真值 +96），符号全丢。必须走"单独凹 + 角点"结构证明。

## §4 **PURE-LEAN 探针**：`nliRestBIXPCGWb`（`bank_BIXPCGWb`）

文件 `/tmp/nlibank/probes/p011_bixpcgwb.lean`，**211 行**。
```
$ nice -n 19 lake env lean /tmp/nlibank/probes/p011_bixpcgwb.lean ; echo RC=$?
'NliBankProbe.bixpcgwb_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
RC=0
real 0m28.682s   user 0m37.60s        # 日志：logs/probe_p011.log
```
- 无 `sorry` / `axiom` / `native_decide`（`grep -nE "sorry|native_decide|^axiom" p011…` 0 命中）。
- 陈述逐字未动：探针定理的类型就是 `bank_BIXPCGWb`（PA21:732 原文）。
- 结构：6 枚 `dX_concave_i`（`deltaX` 单独凹，二次系数 = −配对变量）+ 1 枚盒判决
  `dX_box_ge : (92:ℝ) ≤ deltaX x1 … x6`（有理放大盒 64 角点，`norm_num [deltaX]` 判决）
  + 把 `y` 盒翻译到 `x = y²` 盒（`2hminus ≥ 2.4`、`2hplus = 2.6508 ≤ 2.66`、`√8 ≤ 2.83`）。
- 数值锚（浮点，仅供对照）：该盒上 `deltaY` 的真最小值 ≈ **96.11**（在 (2.65,2,2,2.65,2,2)），
  证明里用的阈值是 92（> 60），余量 1.6 倍。
- 交叉验证（独立来源）：`pipeline/interval/out/prep_queue.jsonl` 里 `prep-BIXPCGW b` 的
  `probe = {"status":"closed","leaves":154721,"wall_s":1.614}`、`tier_source = measured`（唯一一条
  实测闭合的 68 条成员）。

## §5 落地形态（E）四个实验

### §5.1 `p020_landing_clash.lean` —— 新文件（不 import Assembly）+ 同名 FQN
```
$ nice -n 19 lake env lean /tmp/nlibank/probes/p020_landing_clash.lean ; echo RC=$?
/tmp/nlibank/probes/p020_landing_clash.lean:6:8: warning: declaration uses `sorry`
RC=0
```
⇒ 只要**不** import `Kepler.Assembly`，`Kepler.Assembly.nliRestBIXPCGWb` 这个 FQN 在本模块里是自由的
（因为 Assembly.lean 不在 import 闭包内）。这**不能**用于落地：见 §5.3。

### §5.2 `p021_no_cycle.lean` —— 新 namespace + 消费形态
```
$ nice -n 19 lake env lean /tmp/nlibank/probes/p021_no_cycle.lean ; echo RC=$?
'Kepler.NliBanks.consumer_form' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
RC=0
```
（`sorryAx` 只是这个实验体里的占位；真证明见 §4/§5.4。）

### §5.3 `p022_clash_with_assembly.lean` —— import Assembly 后再声明同名
```
$ nice -n 19 lake env lean /tmp/nlibank/probes/p022_clash_with_assembly.lean ; echo RC=$?
/tmp/nlibank/probes/p022_clash_with_assembly.lean:6:8: error: `Kepler.Assembly.nliRestBIXPCGWb` has already been declared
RC=1
```
⇒ **同名重声明在 Assembly 被 import 后直接报 duplicate declaration**；不 import 又能声明但 Assembly
无法 import 该文件（同样 duplicate）。所以候选 3（新文件证同名）是死路。

### §5.4 `p023_landing_e2e.lean` —— 真证明 + Assembly 侧一行替换（端到端）
文件 225 行（含 §4 的完整真证明，命名空间改为 `Kepler.NliBanks`）：
```lean
import Kepler.Assembly
import Kepler.Text.PackingAuto21
namespace Kepler.NliBanks
open Kepler.Text
… (6 枚 dX_concave_* + dX_box_ge + bixpcgwb_probe，无 sorry)
end Kepler.NliBanks
namespace Kepler.Assembly
theorem nliRestBIXPCGWb_FIXED : Kepler.Text.bank_BIXPCGWb := Kepler.NliBanks.bixpcgwb_probe
end Kepler.Assembly
#print axioms Kepler.NliBanks.bixpcgwb_probe
#print axioms Kepler.Assembly.nliRestBIXPCGWb_FIXED
```
```
$ nice -n 19 lake env lean /tmp/nlibank/probes/p023_landing_e2e.lean ; echo RC=$?
'Kepler.NliBanks.bixpcgwb_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Assembly.nliRestBIXPCGWb_FIXED' depends on axioms: [propext, Classical.choice, Quot.sound]
RC=0                                   # wall 39.7s（日志 logs/probe_p023.log）
```
⇒ 同一 Prop（`Kepler.Text.bank_BIXPCGWb`）在新模块与 Assembly 语境里都能以标准三公理给出，
**无环**（PA21 的 26 条 import 中 0 条是 `Kepler.Assembly` 本体）。注意：这是 **proof-level**
验证；真正落库仍需岛协议重编 Assembly.olean（本波按规则未做）。

## §6 浮点 triage 的口径声明（不是证明）

`/tmp/nlibank/num/tri.py` 用 Python float 复刻 `deltaX / rhoX / rad2X / upsX / etaY / dihY(atan2) / volY / vol4f`，
只用于**排序与判死**（找最紧角点、量余量），**不作为任何 `PURE-LEAN` 依据**。
其中 `Real.sqrt` 的负值语义按 Lean 的 `sqrt x = 0`（x<0）复刻；`hminus` 由 ε-定义数值求解
（`marchalQuartic h = lmfun h`，`1.2 ≤ h < 1.3`）得 `hminus ≈ 1.2317544220903044`
（高精度 30 位：`1.2317544220903043901`），与 PA21 `mi_hminus_prop` 的区间一致。

关键高精度（mpmath 30 位）事实：
```
g4(2,2,2,2,2,2)        = +1.77e−30   → gamma4f 在正则点是精确 0
g4(√8,2,2,2,2,2)       = −1.08e−30   → 第二个精确 0（lmfun(√8/2)=0 分支）
g4(2hplus,2,2,2,2,2)   = +2.4128e−6
g4(2hminus,2,2,2,2,2)  = +9.8039e−5
g4(2.001,…,2.001)      = +4.9571e−4
```
这两处"精确 0"是把 `nliTskRIBCYXUsharp` / `nliTskIYOUOBFsharpv2` 判成 **NEEDS-MATH** 的依据：
目标是非严格不等式而等号在盒内点取得，有理区间证书不可能在超越点 (=√8, =2) 上闭合等号。

## §7 C 列素材：`prep_queue.jsonl` 交叉（原始文件 812 行）

抽取命令（完整表：`logs/prep_by_bank.tsv`、`logs/prep_queue_relevant.tsv`）：
```
$ cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
$ python3 - <<'EOF'
import json
rows=[json.loads(l) for l in open('pipeline/interval/out/prep_queue.jsonl')]
...
EOF
```
68 条中**唯一** `probe.status=closed` 的是 `prep-BIXPCGW b`
（`closed / 154721 叶 / 1.614s / tier_source=measured / T6`）；
`probe.status=limit` 的有 4 条（`MKFKQWU` 2.773s、`MKFKQWU halfwt` 2.601s、
`TSKAJXY-TADIAMB` 2.350s、`QITNPEA 4003532128 a` 2.189s，全 `tier_source=static`）；
`timeout` 1 条（`QZECFIC wt0` 20.004s / 7033 ops）；其余无 probe（多为 `split(k/n)` 记账行）。
这与 mnt11 ERRATA E2 的口径一致：**静态档位不能作为成本依据，只有 measured/closed 才算数。**

## §8 产物清单

```
~/c17_backup/lane_snapshots/nli-bank-triage/
  TRIAGE.tsv              68 行 × 9 列（表头逐字）
  TMPL-LEVERAGE.md        B1/B2/B3
  PURELEAN-LIST.md        D（可闭清单 + 小计 + 结论句）
  D-LANDING.md            E（落地形态 + 环检测 + 与 F 的接口）
  EVIDENCE.md             本文件
  probes/                 p000,p010,p011,p020,p021,p022,p023（7 个 .lean）
  logs/                   probe_p000/p011/p020/p021/p022/p023.log,
                          prep_by_bank.tsv, prep_queue_relevant.tsv
```
