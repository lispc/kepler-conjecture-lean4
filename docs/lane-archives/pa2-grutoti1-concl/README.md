# pa2-grutoti1-concl — Lane-draft 归档（未闭合，未落库）

**基线**：任务发车于 `ceef5a91` 附近；交付验证对 `fd3c5651` `git apply --check` PASS。
**预算**：~80/120 调用、~3.5h（超 0.5h，10 轮编译驱动收敛）。

**为什么不落库（2026-11-03 深夜）**

按「kit 只含 RC=0」政策：kit 态整文件**未达 RC=0**——残余 45 个 unknown identifier
（`ext_final3.txt` 精确清单，40 个为已拷连锁件缺依赖）+ 12 条疑为错误恢复二阶效应的
unsolved goals。目标 `GRUTOTI1_concl`（PA2:5843）在 kit 态已替换为 PA23 `GRUTOTI`
capstone 真证体逐字（陈述冻结 True、零新 sorry、唯一删除行 `  sorry`），但不得据此声称
闭合；HEAD 上该 sorry 原样未动。

**规模与结构（重要，决定下波路线）**

- kit `+28,362/−1`：PA23 GRUTOTI 章 :218–6385 **逐字** + 外部 Kepler 依赖 628 件 `p2e_*`
  改名私拷（13 模块）。如此规模若落库，将制造约 2.8 万行的复制债（T4 去重负担）。
- **为什么用拷贝**：PA23 :204 `import Kepler.Text.PackingAuto2` ⟹ PA2 import PA23 成环，
  零新 import 约束下只能拷。**下波应先裁决替代路线**：(a) 沿本 kit 收尾（1–2 编译轮，
  代价是复制债）；(b) 桥文件模式（仿 AzimBridge，PA2 不动、桥文件 import PA23 消费
  `GRUTOTI`，再由消费点 rewire——需核 `GRUTOTI1_concl` 的消费链能否搬出 PA2）；
  (c) SF 可见性转正（PA23 侧件升 public/桥出，需闸模式与审批）。
- 链上已核净版：PA17 `AJRIPQN`、PA14 `QZKSYKG1/2` 已闭合（文件头注记过时）；
  预期终态 `GRUTOTI1_concl` 公理面脱离直接 sorryAx（错误恢复态读数
  `[propext, sorryAx, choice, Quot.sound]` 不作最终值，RC=0 后 #print 复核）。

**消费条件**

1. 先裁决路线 (a)/(b)/(c)（(b)/(c) 会使本 kit 大部作废，故先裁决再动工）。
2. (a) 路线：补齐 45 缺依赖 + 消 12 goals → 整文件 RC=0 → `#print axioms` 目标脱离
   直接 sorryAx → 闸（`LANE_FILES=Kepler/Text/PackingAuto2.lean`，THM=GRUTOTI1_concl）。
3. 预算内闭不完就再次 Lane-draft，不得硬落。

**对应 queue**：§8 续 260；`Kit-draft-pa2-grutoti1-concl.lean` / `WorkAx.lean` /
`build2.py`（幂等生成器）/ `ext_*.txt` 在 `lane_snapshots/pa2-grutoti1-concl/`（不入库）。

**工件 sha256**

```
见 docs/lane-archives/pa2-grutoti1-concl/ 下三文件；kit 仓内副本即权威。
```
