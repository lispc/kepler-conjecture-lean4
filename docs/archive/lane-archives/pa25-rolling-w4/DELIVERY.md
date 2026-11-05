# DELIVERY — lane pa25-rolling-w4

- 日期：2026-11-05
- 基线：主仓 HEAD `4ab6a8e7`（PA25 **14,393 行 / 25 裸 `sorry` / 26 条编译器
  `declaration uses 'sorry'` 警告**；基线文件 MD5 `ca2eaedb3d421951635dd07119dbde9e`，
  与 w3 交付 MD5 一致）
- 工作副本：`/tmp/pa25-rolling-w4/Work.lean`（从主仓 HEAD 文件逐字节拷贝后只改目标体；
  **主仓 tracked 零改动，工作期间仓内零未跟踪文件**）
- 终稿：`Work.lean`，**MD5 `2fe12c2150f5aee916d5fd89efda08ca`**，
  **14,547 行 / 22 裸 `sorry` / 23 条编译器 sorry 警告 / 0 error**
- patch：`patch-pa25-rolling-w4.diff`（相对 `4ab6a8e7` 的 PA25 字节，只含 PA25），
  **+157 / −3，3 hunks**；`git apply --check` = **PASS (RC=0)**，
  `git apply --stat` 只显示 `lean/Kepler/Text/PackingAuto25.lean`
- **HEAD 漂移说明**：本波期间主仓 HEAD 由并发车道推进到 `8c003d0d`（PA22/队列变更），
  但 `4ab6a8e7..8c003d0d` 对 `PackingAuto25.lean` 零 diff（两处 MD5 均
  `ca2eaedb3d421951635dd07119dbde9e`）；patch 在 `8c003d0d` 上重跑
  `git apply --check` 仍 RC=0。

## 1. 本波闭合 3 件（全部 `#print axioms` = 标准三，零 `sorryAx`）

| # | 定理 | 终稿行 | 证明体行数 | 锥内(地图) | hnl 消费 | 证法一句话 |
|---|---|---|---|---|---|---|
| 1 | `gamma4fgcy_POS` | 12198 | 11 | N（0 行） | 消费 `hnl`（`proj_bank_GLFVCVK4 hnl`） | `bank_GLFVCVK4` 三分支：γ>0 支 `exact`（`gamma4fgcyP25` 与 PA20 `gamma4fgcy` 定义性同体，直接过）；norm2hh 支 `ztg4w1_quarter_norm2hh` 给 y2..y6 全 `<2hminus` 撞 `hnot`；rad2 支 `rad2YP25 = yOfX rad2X` 为 `rfl` 桥后 `linarith` 撞 `hrad` |
| 2 | `cc_prep_model_data` | 6311 | 78 | **Y（地图行 parent=LEAF_RANK_PROPS）** | hnl-free | HOL OXLZLEZ3.hl:4021–4185 相邻性：见证 `ccUh [u0,u1,f(i+1)]`；`CC_KE_34` 分案——`ccKe=4` 支 `K4_CC_WI_ALT` 直接入楔 (i+1)；`ccKe=3` 支 `S_LEAF_SYM` 换位茎得反向 `ccKe=4`，`K4_CC_WIM` 把该胞送入回卷楔 `(i+1)+(n-1)=i`，撞假设 `¬cc_4 i` |
| 3 | `EDGE_IMP_K23` | 12535 | 71 | N（0 行） | 语句带 hnl，**证明零消费**（`have _ := hnl`） | `mcellSet` 取参数 `(k,ul)`：`k≤1` 由 `BumpP4.EDGE_IMP_K2`（`edgeX=∅`）排除；`k≥4` 归一到 `mcell4` 撞 `hno4`；`k=2/3` 分别用 PA18 已证 `MCELL2_EDGE_FIRST`/`MCELL3_EDGE_FIRST` 重根，`BARV_3_EXPLICIT` + `getD` 归一拼回 `[u0,u1,v1,v2]` |

> 说明：第 1/3 件语句带 `hnl`（第 1 件真消费 bank 投影，第 3 件零消费）；第 2 件
> 语句与证明均 hnl-free。三件的证明均未引入任何新 `private` 声明、未新增 `import`。

## 2. 陈述冻结

`statement_cmp_w4.py`（按 w3 `statement_cmp_w3.py` 同构，比对
`PackingAuto25.orig.lean`(=HEAD 字节) 与 `Work.lean` 的 `theorem NAME … := by`
前缀切片）：

```
gamma4fgcy_POS: IDENTICAL
cc_prep_model_data: IDENTICAL
EDGE_IMP_K23: IDENTICAL
RESULT=PASS
```

日志：`logs/statement_cmp.log`。全文件 diff 仅 3 个 hunk，每个 hunk 只删一行
`  sorry`（`grep -n '^-'` 除 `---` 头外 = 3 行）。

## 3. 搬债审计（以 `docs/e2e-reachability-map.tsv` 地图行为准）

原则：体内新引用的每个 **sorried** 件都必须查地图；0 行 = 不在锥（锥外）。

本波三件体内新引用的声明与地图 grep（`grep -c "Kepler.Text.<name>\t"`）：

| 引用件 | 地图行 | 判定 |
|---|---|---|
| `proj_bank_GLFVCVK4` / `ztg4w1_quarter_norm2hh` / `gamma4fgcy` / `gamma4fgcyP25` / `rad2YP25` / `yOfX` / `rad2X` | 0 | 非 sorried（在库真证），不在锥 |
| `LEAF_RANK_PERIODIC` / `LEAF_RANK_S_LEAF` / `s_leaf_leaf` / `S_LEAF_SET` / `S_LEAF_SYM` / `EL_CC_UH` / `cc_uh_exists` / `STEM_EDGEX` / `K4_CC_WI_ALT` / `K4_CC_WIM` / `CC_KE_34` / `F_SUC_PRE` | 0 | 非 sorried（在库真证），不在锥 |
| `mcellSet` / `BumpP4.EDGE_IMP_K2` / `MCELL2_EDGE_FIRST` / `MCELL3_EDGE_FIRST` / `BARV_3_EXPLICIT` | 0 | 非 sorried（在库真证），不在锥 |
| `cc_prep_model_data` | 1（parent=`Kepler.Text.LEAF_RANK_PROPS`） | **锥内**；本波已闭，地图快照过时 |

结论：**零搬债**。三件所引用的全部声明均可追到真证（`#print axioms` 三件皆
`[propext, Classical.choice, Quot.sound]`，可传递地排除 `sorryAx`）。
注意 `MCELL_EDGE_FIRST`（PA18:3183）仍是 sorry，但本波未引用它；用的是已证的
`MCELL2_EDGE_FIRST`（PA18:6105）与 `MCELL3_EDGE_FIRST`（PA18:6161）。

## 4. 残件精确缺口表

**无残件**：本波 3/3 全部真证落盘，`Kit-draft-pa25-rolling-w4.lean` 未生成
（硬约束要求 kit 只装 RC=0 的未闭内容；本次没有未闭内容）。

未动件（不在本波 §1 A/B/C 范围，属 w5 候选）及其精确缺口（仅列已侦察到的）：

| 件 | 位置 | 缺口 |
|---|---|---|
| `GAMMAX_008a` / `GAMMAX_008b` | 12902 / 12914 | 0.008·dihX 侧的 wtcount3 银行项未定位（需先 grep `bank_` 的 0.008/CIHTIUM 条目；`bank_CIHTIUM` 已被 `leaf_CIHTIUM` 消费）；核心可仿已证 `real_model_3a` 装配 |
| `real_model_gamma8` / `gamma8b` | 12231 / 12247 | 假设形是「i 楔小、i+1 楔非小」（与已证 `fhbv2` 的五小形不同），bank 实例化需先定 `GLFVCVK4y4crit/subcrit/supercrit` 哪张对应此构型 |
| `CELL_CLUSTER_ESTIMATE_REDUCE` | 6155 | 未侦察（非 hnl、非 ox3q1h 的锥外大件，~300 行） |
| 3 胞 kit（gamma10/11、pema/pemb、txq/tew、gr、gckb、sum_azim、quqy…） | — | 未侦察；共享前置 `CC_3_PROPS`/`MCELL3_*` 已在库绿，但各件 bank 配置未逐一定位 |

## 5. 预算自报

- 工具调用：约 60 / 120；墙钟：约 0.4h（12:50–13:10）/ 3h。
- 全文件 standalone 编译 5 次：基线、W4-A 后、W4-B 后、W4-C+axioms、终稿
  `Work.lean` 本身（均 RC=0；终稿 `logs/final_WORK.log`：0 error / 23 sorry 警告）。
- 探针：`probe_A`/`probe_A2`/`probe_B`/`probe_C` 各 1–3 轮，全部 `nice -n 19` 单进程串行。

## 6. 复核命令（编排者用）

```sh
# 1) patch 只读校验（主仓 4ab6a8e7，工作区干净）
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
git apply --check /Users/zhangzhuo/c17_backup/lane_snapshots/pa25-rolling-w4/patch-pa25-rolling-w4.diff ; echo $?   # 0
git apply --stat /Users/zhangzhuo/c17_backup/lane_snapshots/pa25-rolling-w4/patch-pa25-rolling-w4.diff
  # 1 file changed, 157 insertions(+), 3 deletions(-)

# 2) 整文件复核（standalone，不碰 .lake）
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q <log> lean /Users/zhangzhuo/c17_backup/lane_snapshots/pa25-rolling-w4/Work.lean
tr -d '\r' < <log> | grep -c ': error:'                    # 0
tr -d '\r' < <log> | grep -c 'declaration uses `sorry`'    # 23
```
