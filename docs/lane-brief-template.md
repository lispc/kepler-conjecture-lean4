# 车道工单模板（编排者 → sub-agent）

> 固化于 2026-11-03（scsgeneric W5c 七波实战稿，w5cB2 工单为蓝本）。编排者发车时整段复制，
> 只替换 `<…>` 槽位；§0 硬约束**逐字不改**（每条都有事故出处，见 `fill-worker-playbook.md` §1/§6）。
> 车道规则以 `docs/fill-worker-playbook.md` 为准，本模板是其发车时的具体化。

---

你是车道 **<lane-name>**（<一句话：哪个程序/哪座塔/第几波>）。主仓 `/Users/zhangzhuo/repos/kepler-conjecture-lean4`，HEAD = **<hash>**（<上波落库了什么；目标文件现状：行数 / own-sorry>）。

## 0. 硬约束（逐字，违反即废）
- **主仓 tracked 零改动，且不得在仓内留下任何未跟踪文件**（含日志、`.log`、`*.lean` 草稿）。你的 cwd 固定为 `/tmp/<lane-name>/`（自建）；所有草稿、日志、kit 放 `$S=/Users/zhangzhuo/c17_backup/lane_snapshots/<lane-name>/`（自建）**根下，不要建同名子目录**。
- **禁止任何 `lake` 子命令**；不触 `lean/.lake/`；不写 `/tmp/lfainteg/`、`/tmp/pm12_oleans`、`/tmp/orch_*`、`/tmp/lane_*`、其它车道的 scratch。
- 编译只用 standalone：`LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q <log> lean <file>`（读日志先 `tr -d '\r'`；`grep 'declaration uses \`sorry\`'` 要带反引号）。探针单进程串行；探针报 olean 不存在 → 等 2 min 重试。`#print axioms` 用全名 `Kepler.Text.<name>`；本 Lean 4.32 在 `open Classical` 下把 `Classical.choice` 打印为 `choice`。
- **禁 `open Classical`（含 `open Classical in` 局部形式）**；需可判定性用 `classical` tactic。目标文件头部若有遗留 `open … Classical`，不得效仿、不得再加。
- **陈述冻结逐字**：目标定理的签名（含隐式/显式参数、docstring 前的 `set_option … in`）一字不改；单行 `:= sorry` 骨架则前缀逐字重现后接 `:= by`。新件零 sorry/admit/native_decide。`set_option … in` 放 docstring 之前。
- **kit 只含整文件 RC=0 的内容**：修不完的件连同仅它们消费的助件移 `$S/Kit-draft-<lane-name>.lean`（禁 sorry 占位、禁进 kit），kit 中目标体恢复原 `sorry`。kit 头形 `diff --git a/lean/Kepler/Text/<File>.lean b/lean/Kepler/Text/<File>.lean` 仓相对双头，`git apply --stat` 只显示仓内路径，对 HEAD `git apply --check` PASS。
- **零新 import**（确需则附 BFS 无环证明 + 全文件漂移核（import 前后 warning 谱面逐条一致 + ≥10 件既有件 `#print axioms` 零漂移）+ grep 新进闭包模块公开名与下游重名——同文件加 import **不是行为保持变换**）。
- **搬债审计以 `docs/e2e-reachability-map.tsv` 地图行为准**（`grep <name>`，0 行 = 不在锥），不得以 import 闭包替代；体内新引用的每个 sorried 件都要查。
- 截断探针须落在声明边界。诚实口径优先：卡住交精确缺口清单（哪个 goal、哪个 API、error 原文），备料式 fallback 可接受。
- 预算 ≤120 调用 / ≤3h；满 ~55 调用用 SendMessage 给编排者发中途简报（闭合件数、剩余错误数、是否需要裁定）。
- 报告里的计数附命令原文与读数（`grep -c ': error:'` 等）；编排者按日志复核，不按自报。
- **验收口径（2026-11-03 起，用户拍板）**：主指标 = **K-REACH / COVERAGE / SHIMS / ORPHANS**；
  `K-SORRIED` 为信息项（不设单调目标）；`K-AXIOM` 为护栏。own-sorry 只作台账，不作为验收闸。
- **未落库工件入库归档**：`kit-*.diff` + `DELIVERY.md` + `Evidence.md` 必须放
  `docs/lane-archives/<lane>/`（Work.lean 不入库，可由 kit + HEAD 重建）；主仓 tracked 改动仅限落库文件。
- **REWIRE 闸**（陈述冻结的证明项换 donor）：`GATE_MODE=REWIRE RW_ALLOW=<allowlist> RW_DONOR=<donor>
  LANE_FILES="a,b" bash scripts/auto_gate.sh <file> <THM>`；删除行必须在 allowlist，且不得删声明头/签名。

## 1. 起点（上波遗产，先读）
- `$S0=/Users/zhangzhuo/c17_backup/lane_snapshots/<prev-lane>/`：`DELIVERY.md`（§… 消费图 / 残件表 / 下波工单）、`Evidence.md`（API 陷阱档）、`Kit-draft-<prev>.lean`（<件数> 草稿，零 sorry，未 RC=0）、`logs/`、`Work.lean`（<说明：是整文件拼接态还是草稿工作件>）。
- 上波逐条定位的坑（不要重踩）：<列表>。
- HOL 源：`lean/scripts/local/<File>.hl:<行段>`。

## 2. 目标（`lean/Kepler/Text/<File>.lean`，行号 @<hash>）
按「助件最少依赖 → 体」顺序：
1. `<目标1>`（:<行>）——<证法一句 / 需要的助件>。
2. …
**不碰**：<清单：别的塔的件 / 需要新 import 的件 / 清单外件>。

**验收期望**：<File> own-sorry <N> → **≤<M>**；最低 ≥<K> 件闭合。所有闭合件 `#print axioms` = `[propext, choice, Quot.sound]`（零 sorryAx）；<大目标们> 公理面零漂移。助件 private、前缀 `<prefix>_`，不得与已落库件重名。

## 3. 工作法
- 把草稿按原设计插回目标位置（助件放在首个消费者之前，同一 `namespace` 内），整文件编译，按 error 逐条修；每轮日志存 `$S/logs/`。
- **先修助件再修体**；绿了就固定不动。名先小探针核实（`#check`/`exact?`）再进整文件编译。
- 每闭一件，立即在当轮探针尾追加 `#print axioms Kepler.Text.<name>`（文件末 `end Kepler.Text` 之后）。
- 结束前：剥离探针尾 → `Work.lean` = 仓 HEAD + 你的改动（整文件拼接态）→ 整文件 RC=0 & 0 error 复核 → 生成 `kit-<lane-name>.diff` → 在主仓 `git apply --check`（只读，不 apply）→ 未闭的件全部移到 `Kit-draft-<lane-name>.lean`。

## 4. 交付（`$S/` 根下）
`kit-<lane-name>.diff`、`Work.lean`、`Kit-draft-<lane-name>.lean`（如有残件）、`DELIVERY.md`（闭合件表 + 每件证法一句 + 残件精确缺口表（goal/API/error 原文）+ 搬债审计（地图 grep 结果）+ 下波工单 + 预算自报）、`Evidence.md`（`#print axioms` 原文 + 整文件 RC/错误数/sorry 声明计数 N→M）、`logs/`。

最终回复给编排者：闭合件数与名字、公理面、own-sorry N → M、整文件 RC、`git apply --check` 结果、残件数与下一波估算、预算。

---

## 编排者验收协议（每条车道，顺序固定）

1. kit 头形 + `git apply --stat/--check`；删除行只许 sorry / 空行 / 注释 / docstring（规则 2）；禁词 grep；import 区零改动。
2. scratch：`/tmp/orch_lfaverify/<lane>/` 仓文件 + `patch -p1` → cmp 车道 `Work.lean`（若车道交的是草稿工作件则以 仓+kit 为准）→ 追加 `#print axioms` 探针（全名，**先核名字存在**）→ standalone 编译 → 0 error、sorry 声明数、公理面逐件。零删除 diff ⇒ 闸 rule 5 跳过 ⇒ 探针**必做**。
3. 落仓：`git apply` → cmp scratch 验证件 → 闸 `cd lean && source scripts/kepler_build_lock.sh && lock_build nice -n 19 bash scripts/auto_gate.sh <File-rel-to-lean> <THM>`（`LANE_FILES="a,b"` 多文件；后台 `(nohup bash -c '…' > /tmp/orch_gate_<lane>.log 2>&1 &)`，macOS 无 `setsid`）。看 `/tmp/auto_gate_build.log` 的 `Built <Module> (Xs)` 行确认真重建而非 Replayed。
4. 提交（pathspec 只含 lean 文件 + 账本）→ `docs/priority-queue.md` §8 顶部插 `续 N`（列表索引 126 = 第 127 行）→ push → 校 U+FFFD（python 字符计数，`grep -c` 只计行）。
5. 闸时长分层：无根消费者文件 ~30 s；← LocalConcl 根的文件 ~1–4 min（LA 文件本体 5–6 s + LocalConcl 16 s + 8,800 job 新鲜度核）；LA35 ~18 min；LA1/LA23 全树 ~20 min。
6. docstring-only 改动过不了标准闸（NOTES-LANE 豁免只认 `--` 注释，docstring 行删除会触发「no sorry consumed」）——并入一个消费 sorry 的 diff 一起落，或先落再 `LANE_FILES` 连带。
