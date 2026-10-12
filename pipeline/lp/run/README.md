# run/ — root 区 LP 终端批量灌装驱动（跨机适配版）

`driver.py`（批量驱动）+ `gen_one.py`（单记录生成链 gen_data → glpsol →
flatten → SoPlex exact → socert 发射）+ `glpsol_dual.py`（SoPlex 放弃时走
glpsol --exact 基座恢复精确对偶）。一切生成/发射均为 **untrusted codegen**；
信任面 = Lean 内核 `decide` 重放发射出的 Bench.lean。

原机（Linux, /home/scroll）的绝对路径已全部环境变量化（2026-10-12 C1d）；
本机（macOS / Apple Silicon）零改动可跑。

## 依赖（macOS）

```bash
brew install glpk soplex
```

- **glpk 5.0**（`/opt/homebrew/bin/glpsol`）：AModel 展开（model2.mod）与
  `--exact` 对偶恢复通道。
- **SoPlex 钉定 8.1.0**（`/opt/homebrew/bin/soplex`，GMP 精确有理模式）：
  版本必须钉定——精确对偶解的分子/分母位宽随求解器版本可漂移，钉版是
  证书可复现性（results.jsonl 的 sha256_Data/D_bits 对账）的前提。升级
  SoPlex 须整批重跑并在本轮记录中注记。
- Lean 工具链：`~/.elan/bin/lean`（driver 只调 `lean`，不触 repo 的 lake）。

## 环境变量（全部可选；不设即用下列默认）

| 变量 | 默认 | 用途 |
|---|---|---|
| `LPRUN_ROOT` | `/dev/shm/lprun`（无 /dev/shm 的机器：`<tmpdir>/lprun`） | 工作根：`gen/`（产物）、`work/`（scratch）、`results.jsonl`、`progress.json` |
| `LPRUN_REPO` | 脚本位置上两级（即本 repo 的 `pipeline/lp`） | 上游脚本/参考件根（gen_data/flatten_lp/socert/exact.set） |
| `GLPSOL` | `/opt/homebrew/bin/glpsol` → `/usr/local/bin/glpsol` → repo `pipeline/tools/glpk-5.0/bin/glpsol` → PATH | gen_one/glpsol_dual 用 |
| `SOPLEX` | repo `pipeline/tools/soplex-8.0.3/bin/soplex`（存在时）→ PATH 的 `soplex` | socert 用（socert.py 同名变量；或 `--soplex` 显式传） |
| `KEPLER_REF` | `<repo>/reference/flyspeck/formal_lp/glpk` | head.mod/body.mod 与 binary/*.dat（make_tasks* 用 `LPBIN` 指 binary 子目录） |
| `LPRUN_LEAN` | `~/.elan/bin/lean` | driver 核验用 lean |
| `LPRUN_LOGS` | `$LPRUN_ROOT/logs` | results.jsonl 镜像备份（5 分钟周期） |
| `LPGEN_OUTDIR` | repo `lean/Kepler/Text/LP` | （gen_lp_skeleton.py）骨架/叶输出树重定向，`--emit-closure` /tmp 彩排用；产物模块根随之取 `OUTDIR.parents[1]/LP` |

driver 还要求 `$LPRUN_ROOT/leanpath.txt` 存在（LEXP路径一行，取法：

```bash
cd <repo>/lean && lake env printenv LEAN_PATH > "$LPRUN_ROOT/leanpath.txt"
```

），work_one 以它为 LEAN_PATH 独立跑 `lean Bench.lean`（不触 repo .lake）。

## 单记录冒烟（~1 分钟）

```bash
export LPRUN_ROOT=/tmp/lprun-smoke
mkdir -p $LPRUN_ROOT
cd <repo>/lean && lake env printenv LEAN_PATH > $LPRUN_ROOT/leanpath.txt
cd <repo>/pipeline/lp/run
python3 gen_one.py --hypermap-string "<hypermap 串>" --module T<id去_> \
    --workdir $LPRUN_ROOT/work/<id>     # D_bits 打在最后一行
```

## 批量（root 区 19,237 条）

```bash
python3 make_tasks2a.py / make_tasks_hard.py   # 任务清单 JSON（LPBIN/LPRUN_ROOT）
python3 driver.py --tasks batch2a_tasks.json --workers 2
```

`results.jsonl` 每记录一行账：`{id, graph, ti, exit, seconds, sha256_Data,
rss_kb, D_bits, msg}`。**`D_bits` = 该记录整数化证书分母 D 的位宽**（证书
重放负载的首要相关量；异动 = 求解器/链路漂移报警，配合 sha256_Data 对账）。
Resume：已 PASS（exit 0）的 id 自动跳过。

## 灌装链（产物 → 叶闭合，LPSchema 手册 5 步）

```bash
# 第 1-2 步：发射产物模块 + 手册第 2 步 pin（根模块别名一并发射）
python3 socert.py <flat.lp> --col-major --terminal-bound 12 \
    --record-id <graphId>_t<ti>          # 模块名默认 T<id 去 _>
# 第 3 步：批量叶闭合（占位行 → 单行转发，叶名不变，LPAll 零改动）
LPGEN_OUTDIR=<输出树> python3 lean/scripts/gen_lp_skeleton.py --emit-closure
# 第 4 步：对账自检 / 第 5 步审计红线见 lean/Kepler/Text/LP/LPSchema.lean 模块头
```

## 本机实测基线（M3 Pro，2026-10-12 C1d）

- pilot A `114084514923_t0000`（664 vars × 2767 rows）：gen_data 0.04 s →
  glpsol 0.04 s → flatten 0.1 s → SoPlex exact ~1 s → socert 发射 4.4 s；
  Data.lean 编译 ~30 s，Assembly.lean（含 pin）~18 s（单核）。
- 记录 A `204880136538_t0000`（915 vars × 3882 rows，root 区首位）：发射链
  同量级；Data ~40 s，Assembly ~23 s。
- 每记录全程 ~50 s 量级 → 19,237 条 ≈ 267 核时 ≈ 2 核 5.6 天。
