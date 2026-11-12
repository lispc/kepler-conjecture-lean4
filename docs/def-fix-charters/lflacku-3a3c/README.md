# DEF-FIX 章程：LFLACKU 3A+3C（2026-11-12，defix-small-w1；含勘误+修复）

> 依据：`~/c17_backup/lane_snapshots/dagcut-eval-w1/EVAL.md` §4.4 判词 **GO-DEF-FIX（3A+3C）**；
> 用户已批（pq 续1022 / `e1c6d72e`）。AGENTS §2：本单**不改任何定义体/陈述**——3A 只动 import 边、
> 3C 纯搬运一个声明；零重命名、零 sorry 增减。执行中工单一处事实错误经机器证据修正（见 §1 勘误）。

## 0. 一句话

删赘边 `LA38→LA23`（LA38 对 LA23 **自有**声明 0 活引用）并反向补 `LA23→LA38`；同波补
`LA38→LA4` 一条（勘误：LA38 实际活引用 LA23 转发的 LA4 件 `ballAnnulus_norm_bounds` ×4）。
`pos_imp_scs_arrow_empty_p22`（LA22:4070-4088，19 行）逐字节下移 LA1——LFLACKU_p23 的
一层上游 DAG 阻塞解除（**仍卡 hNL `TAUM_STD_POS_p23`，用户保留区**，本单无证明侧收益）。

## 1. 对象与勘误证据

- **勘误（EVAL §4.2 的事实错误）**：EVAL 称"LA38 对 LA23 声明 live-code 使用 = 0，唯一命中是
  LA38:197 注释英文 instead"。机器证据（岛协议重编 LA38 RC=1）：
  `error(lean.unknownIdentifier): Unknown identifier ballAnnulus_norm_bounds` ×
  LA38:658/1316/1344/2622。根因：`ballAnnulus_norm_bounds` 声明在 **LA4:402**，LA38 经
  `LA38→LA23→LA4` 传递转发解析；EVAL 只扫了 LA23 自有声明名，漏掉 re-export 消费
  （正是 EVAL §6.1 自标的"实例/notation 级使用扫不出"类盲区，实锤）。
- **修复**：LA38 补 `import Kepler.Text.LocalAuto4`（无环：patched 图上 LA4 ↛ LA38、LA4 ↛ LA23
  程序验证；LA4 只 import Polytope/PackingAuto2/PackingAuto5/Fan/Mathlib）。重编后 LA38
  RC=0 零 error，且全文件仅此一名缺失（其余 error 均为其 rcases 级联）。
- 3C 下移证据（EVAL §4.2 + 本车道复核）：依赖 100% 在 LA1（`BBsV39`:416 / `taustarV39`:437 /
  `BBprimeV39`:674 / `BBprime2V39`:687 / `MMsV39`:691 / `scsArrowV39`:805，全在插入点之前）；
  LA22 内零活引用；全树唯一外部活消费者 = LocalConcl:6316（`⟨...⟩` bundle 实名项，live code），
  LocalConcl 已 import LA1 ⇒ 搬后改经 LA1 解析，无歧义。
- EVAL 判 DEFER 的 3B（拖 52 声明/1,353 行 LA38 闭包下移）**未走**。

## 2. 操作清单（4 文件；3 行 import + 19 行搬运）

| # | 文件 | 操作 | 行数 |
|---|---|---|---|
| 3A | `LocalAuto38.lean` | 删 `import Kepler.Text.LocalAuto23`（:128）；**加** `import Kepler.Text.LocalAuto4`（勘误修复，LocalAuto1 之后） | −1/+1 |
| 3A | `LocalAuto23.lean` | 加 `import Kepler.Text.LocalAuto38`（LocalAuto9 之后） | +1 |
| 3C | `LocalAuto22.lean` | 删 `pos_imp_scs_arrow_empty_p22` 整块（:4070-4088 + 尾空行） | −20 |
| 3C | `LocalAuto1.lean` | 同块插入 scs 定义段后（`scs3M1` 与 `Conclusions, part 4` 之间） | +20 |

`taustar_taum_dfun`/`FUNLIST_EXPLICIT`（LA38）**原地不动**（工单钦定）。

## 3. 图不变量（机器自检，`logs/scc_check_lflacku.log`）

patched 树全图重算（540 模块）：edges = 基线 2138 + 1（LA38→LA4）= **2139**；边差集恰好 =
LA38−LA23 / LA38+LA4 / LA23+LA38，逐文件比对零其它变化；**SCC 全单点、零自环**；
`LA38 ↛ LA23` ✓、`LA23 → LA38` ✓、`LA22 → LA23` 保持 ✓、`LA1 ↛ LA23` ✓。
（EVAL 的 2137 口径系 `04ab3cac` 时代；`e7672ae5` 已含其后落库边故基线 2138。）

## 4. 陈述冻结证据（机器自检）

- 搬迁块逐字节：`pos_imp_scs_arrow_empty_p22` donor（LA22 HEAD）vs LA1 patched 文本
  sha256 相等（19 行含 doc）；byte_check 6/6 PASS（`logs/byte_check_lflacku.log`）。
- `logs/selfcheck_final.log`：全树 DECL/SORRY+ND 多重集基线 vs patched 全等（LA27 因并发落库的
  w2 波偏斜 21→18 已排除并独立证实，与本单无关）；受影响文件 sorry 计数 comment-aware 实测：
  LA22 63→63、LA1 78→78、LA38 45→45、LA23 24→24（搬迁件无 sorry，守恒）。
- 零 `axiom`/`native_decide` 增删（两单 diff 全文不含这些词）。

## 5. 编译验证（岛协议 farm，串行 nice -n 19）

farm 重编：LA1（+1 件）→ LA38（−LA23 +LA4）→ LA23（+LA38）→ LA22（−1 件）→
**LocalConcl 消费者 typecheck**（:6316 bundle 实名消费 `pos_imp_scs_arrow_empty_p22`，
import LA1+LA22 双通道解析验证）。全部 RC=0 零 error（`logs/logs_lflacku_*.txt`）。

## 6. 闸口留给编排者的验收

- 模块闸 + 根面 `#print axioms` 亲跑（AGENTS §4 口径③）。
- 首轮回编 LA38 曾 RC=1（勘误发现过程），修复后全绿；若闸门在其它 LA38-importer 上见
  同类"经 LA38 转发"断名，机制与本勘误相同，处理法 = 给该 importer 补直通的低层 import。
- `git apply --check`：相对 `e7672ae5` PASS（`logs/git_apply_check_lflacku.log`）。

## 7. 落库后下一步（不在本补丁）

hNL 注册表（`main_nonlinear_terminal_v11`，TAUM_STD_POS_p23）落地后，LFLACKU_p23 证明波
在 LA23 就地开工；LA23→LA38 新边即为其取 `taustar_taum_dfun`/`FUNLIST_EXPLICIT` 的通道。
