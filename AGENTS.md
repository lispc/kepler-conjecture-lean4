# AGENTS.md — 本仓库的硬规则

> 给所有接手本仓库的 agent。**先读这 60 行，再动手。**
> 违反下面任何一条，产出作废——不是"下次注意"，是作废。

## 1. 目标与验收

- 终局（**用户 2026-11-06 裁决**）：**不比 Flyspeck/Isabelle 更差**，不是完美标准三。
  验收式：`#print axioms Kepler.the_kepler_conjecture_e2e`（`lean/Kepler/Final.lean:22`）
  = `[propext, Classical.choice, Quot.sound]` ∪ **约 585 条地面 `native_decide` 公理**，且
  1. **零 `sorryAx`**（锥内 79 条 sorry 是唯一还算"债"的东西）；
  2. 每条公理的陈述是**封闭可判定的地面事实**（无自由变量、无对无限类型的量词），
     进 manifest、可 replay、注明数据源与生成器版本；
  3. 与原文形式化的 `same*`/`pre_iso_test*` **同数据、同信任类别**（见
     `docs/handoff-2026-11-06.md` §0.1：HOL 跳过分类定理；HOL 零公理真证 `good_list`；
     Isabelle 用 8 条 `by eval` 做枚举）。
- 当前根面 625 = 621 native + 标准三 + `sorryAx`。**621 是信任基座，不是债**
  （基线 R，`docs/priority-queue.md` 文件头）。
- 在此原则下**明确不做**：把 580 条枚举 shard 拉进内核重放（实测 4,450–6,550 核时 +
  内存不可行）、证书农场、"真·标准三"。**但**下面这些没有 parity 借口，必须修：
  `Prop := sorry` 型定义、`else True` 回落、索引盲谓词、空量化注册表。
- 唯一验收语言：`#print axioms`。任何"完成了"的说法都必须附这条命令的输出。

## 2. 禁造边（最高优先）

- 不许**新增** `axiom` / `sorry` / `admit` / `native_decide` / 假定理。
  （在库的 ~621 条 `native_decide` shard 是 §1 声明的**信任基座**，不是违例；但也**不许再添一条**。
  能改 kernel `decide` 的必须改，改不动的不许换新的 `native_decide` 顶上。）
- 不许改陈述来让证明通过。陈述改动只走 **SF 通道**（`docs/statement-fix-proposals.md`）；
  定义改动只走 **DEF-FIX 通道**（章程在 `docs/def-fix-charters/`）。
- 不许删 `sorry` 假装关闭；删除面必须恰好等于被真证的声明。
- 上游是**假桩**（如 `POLYHEDRON_TGJISOK` 空洞化、`BIJ_DART_POLYEDGE` 在现桩下为假）
  时，判 **BLOCKED** 并报告，不许绕着假桩凑证。

## 3. 车道纪律

- 车道在 `/tmp/<lane>/` 工作；**主仓 tracked 文件零改动**。
- 产物（`patch.diff` / `DELIVERY.md` / `Evidence.md` / `logs/`）放
  `~/c17_backup/lane_snapshots/<lane>/`。
- 只允许独立 `nice -n 19 lake env lean <单文件>`；并发 ≤3。
- **禁止** `lake build`、`scripts/auto_gate.sh`、地图仪器（`e2e_reach_map` /
  `global_reach_map` / `orphan_histogram`）。这些由编排者跑。
- 所有子任务派发必须**异步**（`run_in_background: true`），不阻塞主会话。

## 4. 本机限制

- 禁重型计算：证书农场、全库构建、LP/非线性重放一律挂起。
- **Assembly 级 `lake build` 永久禁止**（会触发全树重编与 shard trace 洪泛）。
  需要验证 Assembly 时走岛协议：standalone `lean -o /tmp/.../Kepler/Assembly.olean`
  + `LEAN_PATH` 探针 + 与基线根面逐字节比对 + olean 回灌。
- 用户保留项：certtm 的 TM3 / Mono* hold；D 证书层解冻 hold。不要单方面动。

## 5. 落库流程

1. 车道交 `patch.diff`（相对某个 HEAD），编排者 `git apply --check` 后应用。
2. 编排者跑闸：`cd lean && bash scripts/auto_gate.sh Kepler/Text/<File>.lean <THM>`。
   新文件先 `git add -N`。零删除 diff 会被 NOTES-LANE 豁免（规则 5 跳过）。
3. 闸 PASS 才 commit；**一个落库一笔 commit**，message 写清 文件/件数/commit 关系。
4. 对表：更新 `docs/priority-queue.md` §1（在飞）与 §8（一条日志）。

## 6. 文档纪律

- `docs/priority-queue.md` 是**唯一**实时账本（在飞 + 排队 + 最近日志）。
- 数字**只引用不抄**：同一指标不许在多个文档各写一份。写数带
  `(实测 <commit>，<日期>)` 或标 `stale`。
- `docs/history/` 与 `docs/archive/` 只增不改；纠正加 `ERRATA`，不覆写原文。
- `docs/statement-fix-proposals.md` 必须留在原路径：`auto_gate.sh:83` 按路径 +
  `^## N.` 切节读它。移动/拆分必须同 commit 改脚本。
- 旧看板（STATUS/HANDOFF/DEBT）已归档，别再往根目录加"总览"。

## 7. 止损比硬凑好

- 单件超过 ~450 行或 3 轮结构性卡死就止损，写清卡点交班。
- 侦察结论与工单冲突时，**以机器证据为准**（编译通过/`#print axioms`/probe），
  并把勘误写进交付。
- 不确定就标 UNRESOLVED。编造比空手更糟。
