# 填证工人手册（Fill Worker Playbook）

> 面向 ZCode sub agent 填证工人（Phase 5 Text 章 `sorry` 清偿）。**开工必读本文**；
> 编排者任务书只给三件事：lane 文件、本轮目标、特殊提示——规则一律以本文为准。
> 维护者：主 agent。每波 launch 前更新 §5 地图，每波收工后更新 §6 教训日志。
> （历史文档 `phase5-worker-template.md` 是 opencode CLI 时代的工人模板，已退役，仅作参考。）

## 0. 开工检查单

1. 读本文全文；
2. 从任务书确认：lane 文件（你的唯一工作文件）、本轮目标、特殊提示；
3. 环境：`export PATH="$HOME/.elan/bin:$PATH"`，一切命令在 `lean/` 目录下跑；
   依赖 olean 已全部建好（Text 全链首建 ~5 分钟已由编排者完成，你无需等）；
4. 本机是 macOS：**没有 `timeout` 命令**（别用）；路径无 `/home/scroll`（旧文档已作废）。

## 1. 硬性纪律（`auto_gate.sh` 五道机械闸会机器检查，违反即废）

- **只改 lane 文件这一个 tracked 文件**；草稿/探针一律放 `/tmp`；
- **只允许删除：sorry 行（bare 或带行尾注记，如 `sorry -- NEEDS: ...`）/ 空行 /
  纯注释行**；一切结构性代码行（theorem/def/lemma/namespace/证明内容行）禁止删除，
  一切定理/定义陈述冻结（闸门第 ② 道机械检查）；
- **新增行禁词：`sorry` / `admit` / `native_decide`——连注释里都不行**；
- 新增辅助引理必须自身完全证明（不得带 sorry）；
- **绝不 `git commit`，绝不自己跑 `scripts/auto_gate.sh`**（编排者统一验收：
  `LANE_FILES` 多 lane 轮换 + stash，闸过即 commit+push）；
- 验收构建必须自然退出（中途掐死时 error 未 flush 是假绿）。

## 2. 效率纪律（每条都来自真实战报的教训，见 §6）

1. **分块读取**：先 `grep -n` 定位，只读目标 ±60 行邻域；**禁止整读 >500 行的文件**；
   已读过的内容不重复读（拿不准就记笔记）。整读大文件+重复读是 token 预算的头号黑洞。
2. **三分类先行**：动手填第一枚之前，先通览 lane 文件全部 sorry 的 NEEDS/DISCHARGES
   注记，产出分类清单：`机械可填 / 卡具名桥或外部锚（跳过）/ 疑似假陈述（记录，跳过）`。
   本轮目标 = 机械题的 ~70%，**不是编排者给的固定数**——固定数只是下限参考。
3. **查重前置**：写任何新辅助引理之前，先 grep 全树找现成同型：
   `grep -rn "<关键词>" lean/Kepler/Text/SphereKit.lean lean/Kepler/Geom/ lean/Kepler/Text/*Auto*.lean`。
   能引既有 kit 就引；本项目最痛的历史债务就是孪生定义泛滥（SphereKit 波次合并了
   80+ 个 `_pNN` twins），不要新增孪生。
4. **批量编译**：每填 3–5 枚跑一次自查（见 §3，单次 1–3 分钟）；**同一目标证明尝试
   失败 2 次就跳过**，原位 NEEDS 注记写一句卡点，下一枚。恋战是第二号时间黑洞。
5. **备份习惯**：动手前 `cp <lane文件> /tmp/orig<文件名>.lean`，弄坏了能回。
6. **学习环境**：动手前读 lane 文件 10–20 个**已证明**定理，吃透本文件的证明习惯
   （策略组合、私有引理惯例、命名风格）再下笔——照着周围代码写，成功率远高于自由发挥。

## 3. 自查命令（收工必做）

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean
lake env lean Kepler/Text/<你的文件>.lean 2>&1 | grep -c ": error:"
# 必须为 0。sorry 警告（declaration uses 'sorry'）是正常的，不用管。
```

注意：`lake env lean` 不会自动补建依赖 olean——如果你怀疑依赖陈旧，报告里说明，
让编排者处理；自己不要跑 `lake build` 大目标。

## 4. 最终报告格式

1. **填证清单**：定理名列表（按文件内顺序，一句话证法摘要）；
2. **剩余 sorry**：填前 N → 填后 M（定理证明 sorry 与 def 桩分开计）;
3. **三分类统计**：机械未填 n / 卡桥或外部锚 n（逐枚具名）/ 疑似假陈述 n；
4. **陈述问题清单**（若发现疑似假陈述：定理名 + 反例或一句话理由）；
5. **给下一波的上下文笔记**：你在探索中发现的地图信息（哪个引理在哪、哪条路通），
   编排者会合入 §5 供后续 lane 复用——这是你最重要的遗产。

## 5. 预置地图（编排者每波更新；欢迎工人修正/补充，写进报告第 5 项）

### 5.1 跳过清单（外部锚与证书依赖，见了直接跳，不要尝试）

- `main_nonlinear_terminal_v11`（`LocalAuto1.lean:815`，sorry-typed def，等 G4/非线性章）；
  全树 grep `main_nonlinear_terminal` 找到全部消费点；
- LP registry / 证书依赖项（OWZLKVY*、EAR_*、quad_*、ineq_asym、taud_x_taum_x、
  empty_3T2 等，注记带 "+LP" 的）；
- def 桩（`_p38` 式 `def ... := sorry`——闸门禁新增 sorry，def 桩只能等外部落）；
- 已知假陈述：`SUM_INTER`（`LocalAuto38.lean:441` 附近，junk 分支有反例
  `A=univ, B={0}, f=const 1`；需加 `A.Finite` 前提才能关闭，等陈述修复波）。

### 5.2 桥引理位置表（找工具先看这里，别全树乱摸）

| 引理/工具 | 位置 | 状态 | 备注 |
|---|---|---|---|
| `taum_dih_y` | LocalAuto16:459 | open | LA38 tau3_taum 族 6 枚的钥匙 |
| `AZIM_LE_PI_EQ_DIHV` | LocalAuto5:1788 | open | LA38 vv_quad_split 族 |
| `DIHV_EQ_DIH_Y` | 未移植 | 缺 | azim/dihV 解析桥 |
| `sum4_azim_fan` | TopologyFan | 已证可引 | LA38 扇残差族可用 |
| `wedgeInFanGe` = wedgeGe | PackingAuto2:268 | 已证可引 | ConvexLocalFan 第三合取 |
| `HL_EQ_DIST0` / `CIRCUMCENTER_2` | PA6/PA7/PA11/PA12 | 已证可引 | 公共 hl 恒等式 |
| `deltaY`/`deltaX`/`atn2`/`taum`/`solY` 等 kit | SphereKit.lean | canonical | 别再定义本地副本 |
| AzimBridge（azimCycle↔sigmaFan 主桥） | Text/AzimBridge.lean | 808 行 0 sorry | azim 族先查这里 |

### 5.3 各 lane 已知卡点速查（收工后追加）

- **LA38**（58 remaining @2026-09-28）：14 def 桩封 ~11 枚；15 枚卡
  `main_nonlinear_terminal_v11`/LP；6 枚卡 `DIHV_EQ_DIH_Y`+`taum_dih_y`；
  11 枚扇几何残差卡 `LOCAL_FAN_RHO_NODE_PROS2`/`sum4_azim_fan` 导入/
  `AZIM_LE_PI_EQ_DIHV`/`DELTA_Y_POS_4POINTS`/chi_msb 二分。
  **下一轮解锁路径**：在 LA38 内自证 `taum_dih_y`（纯算术）→ 开 6 枚。

## 6. 教训日志（编排者每波收工后追加；工人有观察也写报告里）

### 2026-09-28 · Wave 1（LA38：66→58，8 枚+17 辅助；PA25 进行中）

- **成本基线**：84 min / 39.5M tokens / 196 工具调用 / +513 行。token/产出比偏差的
  四个根因 → 全部固化为 §2：①整读+重复读大文件（LA38 2.4k 行、TopologyFan 4.3k 行）
  ②分类滞后（目标 ≥15 定在分类前，实际机械题只有 ~10）③17 个新引理零查重
  ④1-2 枚一验的编译节奏。
- **正面经验**（复用）：①`sigmaFan 0 univ E (vv i) (vv (i+1))` 是两点集 epsilon 唯一性
  计算，**不需要扇几何**——看似几何的题先找纯集合/算术内核；②HOL 的 LP 论证有
  时可用初等算术复现（`delta_4680581274`：配方法拆成 `−4(c−4)²<0` + 恒正项）；
  ③动手前备份原文件到 /tmp（`orig38.lean` 救场待命）。
- **闸门 mac 适配完成**：perl timeout shim / Text 七收官根替代 Kepler 全根 /
  `LANE_FILES` 并行 lane 轮换验收（b0bed032）。工人无需关心，编排者操作。
