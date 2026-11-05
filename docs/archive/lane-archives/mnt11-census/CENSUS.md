# CENSUS — mnt11-census（88 条 NEEDS-CERT 的 bb_arb 成本普查）

- 车道：`mnt11-census`；工作单：`/tmp/mnt11-census-workorder.md`
- 起始 HEAD：`a97790a1`（ERRATA E3 落库点）。探测期间其他车道继续提交，交付时 HEAD 已漂移到 `8cefdc7a`；
  本车道的输入快照未变（`TRIAGE.tsv` mtime 16:05、`prep_queue.jsonl` mtime Oct 23，均早于本车道 19:24 启动）。
- 性质：**纯计算普查，只探不发证**。零 `lake`/`lean`/`emit_lean.py` 调用，零 olean，零主仓 tracked 改动。

## 1. 结论先行

- 88 条 NEEDS-CERT：**7 条有 closed 证书叶数**（M4 复用 3 + 本次新探 4），**9 条 limit**，**53 条 timeout**，**19 条无 case 不可探**。
- 分档：**A = 4 条**（60 min 单轮可闭），**B = 2 条**（2–4 轮），**C = 82 条**（本轮不做）。
- 按 60 min 单件预算，**88 条里能一轮闭的是 4 条**：`8405387449`、`5557288534`、`4821120729`、`6459846571`。
- 已知 7 条闭环的投影编译机时 **16.12 h**（A+B 仅 4.58 h）；加 4 条 S 的 stage-A（各 ≥15 min）后约 **17.1 h**。
  对应 olean **14.04–17.54 GiB**（A+B 3.32–4.15 GiB），相对 249 GiB 可用磁盘占 **5.6–7.0%**，磁盘不是瓶颈。
- 全 88 条**当前不可排期**：81 条没有 closed 叶数（53 timeout / 9 limit / 19 无 case），瓶颈是收敛路线与
  sqrt/stage-A，不是磁盘或公式。

## 2. 输入偏差（必须先看）

1. **`case_json` 路径全部失效**：队列里 88/88 指向 `pipeline/interval/out/cases_prep_all/prep-*.json`，
   该目录不存在。本次用 `emit_rpn.py` 从 `out/ineqs_prep_ast.json` + `out/defs_prep.json`
   现场再生 66 条 case（**8.4 s**，纯 Python，非 Lean）。3 条 M4 复用件未再生。
2. **19 条不可探**：队列 `emit_status=skip:recursion limit`，`ops=None`、无 `case_json`。
   以 `sys.setrecursionlimit(200000)` 重试仍立即 `RecursionError`（疑似定义展开成环，非深度不足），
   标记 `no_case` 并归 C。它们全部是 `mixed`/大 ops 候选（15 条 `7550003505*` + 4 条 poly），
   要探必须先修 emitter，不在本车道范围。
3. **工单模板的 `--vars=6` 不被二进制接受**：`bb_arb.c` 对未识别 `-` 参数直接 `usage()` 退出；
   `vars` 从 case JSON 读取。实际探针命令**不含 `--vars`**，M4 日志里的 `vars=6` 也是回显而非入参。
4. **旧 probe 记录不是 3 条而是 8 条**：3 条 closed（复用）、4 条 limit、1 条 timeout。
   后 5 条已按 `2M/180s` 重探：`5744538693` 由 limit 变 **closed（936,162 叶）**，其余仍 limit/timeout。

## 3. 方法（可复现）

```sh
# case 再生（66 条；纯 Python）
python3 pipeline/interval/emit_rpn.py --ids <66 个 idv> \
  --outdir /tmp/mnt11census/cases --no-xcheck \
  --ineqs pipeline/interval/out/ineqs_prep_ast.json \
  --defs  pipeline/interval/out/defs_prep.json

# 探针（nice 19；并发 3；180 s 墙钟 SIGKILL 进程组）
nice -n 19 /Users/zhangzhuo/c17_backup/tools/prep-p2/bb_arb <case.json> \
  --prec 64 --max-nodes 2000000 \
  --cert /tmp/mnt11census/certs/<safe-id>.cert.json
```

- 二进制：`/Users/zhangzhuo/c17_backup/tools/prep-p2/bb_arb`，sha256 `ab459f5a…d1c12`（与 `prep1/tools` 同文件）。
- 单条记录：`status / leaves / nodes / pending / wall_s / cert_bytes`；cert 记录字节数后**立即删除**（磁盘保护，
  `5744538693` 单件 cert 299 MB，`6459846571` 16.6 MB）。
- 总探针墙钟：主批 **3,286 s（54.8 min）** + 冒烟批 189 s ≈ **58 min**，低于 90 min 上限；主批 CPU 累计 9,516 s。
- 结果 JSONL 与逐条 log 见 `logs/`，索引见 `logs/probe_index.tsv`。53 条 timeout 的 `probe_*.log` 为 0 字节
  （stdout/stderr 重定向到文件时块缓冲，SIGKILL 前未 flush），其 pending 数不可得。

## 4. 结果统计

| probe_status | 条数 | 说明 |
|---|---:|---|
| closed | 7 | 复用 3（M4）+ 新探 4 |
| limit | 9 | 2M 节点封顶；pending 9–37，`1834976363` 例外 609 |
| timeout | 53 | 180 s 墙钟；其中 52 主批 + 1 冒烟 |
| no_case | 19 | `skip:recursion limit`，无 case JSON |
| **合计** | **88** | |

| bucket | 条数 | 其中 S |
|---|---:|---:|
| A（T ≤ 3600 s） | 4 | 3 |
| B（3600 < T ≤ 14400 s） | 2 | 1 |
| C（T > 14400 s 或未 closed） | 82 | 73 |
| **合计** | **88** | **77** |

> S 判据：`class=sqrt` 或 `sqrt_ops>0` 或（`ops` 缺失时）`flags` 含 `sqrt`。按 E3.2，S 件主编译之外
> 还要 **≥15 min stage-A，且可能整批 FAIL**（M4 实测 163/133,228 叶恒定 FAIL）。

## 5. A/B 档逐条（可排期件）

| id | L | ops | T_pred | rounds | bucket | S | 备注 |
|---|---:|---:|---:|---:|---|---|---|
| `8405387449` | 40,785 | 229 | 2,052.3 s / 34.21 min | 1 | A | 否 | M4 复用；E3 已实测 2,050 s，吻合 |
| `5557288534` | 4,264 | 572 | 331.6 s / 5.53 min | 1 | A | 是 | 新探 closed；stage-A ≥15 min |
| `4821120729` | 1 | 46 | 0.036 s | 1 | A | 是 | 新探 closed；stage-A 成本主导 |
| `6459846571` | 36,047 | 83 | 1,392.9 s / 23.21 min | 1 | A | 是 | 新探 closed；stage-A ≥15 min |
| `4680581274 delta issue-cayleytr` | 75,965 | 598 | 6,065.0 s / 101.08 min | 2 | B | 否 | M4 复用；M4 实测 3,614 s 停在 528/891 shard |
| `4680581274 1x` | 133,228 | 223 | 6,640.1 s / 110.67 min | 2 | B | 是 | M4 复用；另有 stage-A 实测 14m16s 且 params 不可用 |

**A 档合计**：3,776.8 s = 1.05 h 编译；加 3 条 S 的 stage-A（≥45 min）约 **1.8 h**；olean 0.93–1.16 GiB。
**A+B 合计**：16,481.9 s = 4.58 h 编译；加 4 条 S 的 stage-A（≥1 h）约 **5.6 h**；olean 3.32–4.15 GiB。

**C 档中唯一 closed**：`5744538693`，L=936,162、ops=155、T_pred=41,565.6 s（**11.55 h / 12 轮**），
olean 10.71–13.39 GiB。单这一条就是 A+B 总量的 2.5 倍；本轮不做。

## 6. 总账与磁盘

- 已知 7 条 closed 的投影编译机时：**58,047.5 s = 16.12 h**；stage-A 后约 **17.1 h**。
- 已知 7 条 olean：**14.04–17.54 GiB**；其中 `5744538693` 独占 10.71–13.39 GiB。
- 可用磁盘：**249 GiB**（编排者实测；交付时 `df` 248 GiB）。已知件占 **5.6–7.0%**；即使放大 10 倍也 <180 GiB。
- 剩余 81 条**无法给出机时投影**：53 timeout 无叶数、9 limit 无叶数、19 无 case。必须先改路线
  （`--bbg --disj-gd` + stage-A manifest、修 emitter、或换 case 划分）再回到本公式。

## 7. 可行性判断（一句话）

**按 60 min 单件预算，88 条里能一轮闭的是 4 条（A）；加 B 档共 6 条可在 2–4 轮内完成，
合计 4.58 h 编译 + ≥1 h stage-A、3.3–4.2 GiB olean；全 88 条当前不可行——81 条没有 closed 证书，
瓶颈是 sqrt/stage-A 与 plain B&B 不收敛，磁盘 249 GiB 完全够用。**

## 8. 风险/未决

1. **公式外推**：E3.1 由 3 条（L ≤ 133k）拟合；`5744538693` 的 936k 叶是 7× 外推，11.55 h 未实测。
2. `wall_s` 是 **bb_arb 运行时间**，不是 Lean 编译时间；T_pred 只用 L/ops，wall 仅作参考。
3. 静态档位仍不可作成本依据（E2）：A/B 里 `5557288534`(T3)、`4821120729`(T2)、`6459846571`(T1) 全是
   `tier_source=static`；实测证明 T1/T2 也可能极便宜（1 叶/36k 叶），反之 T0 的 19 条连 case 都发不出。
4. limit 的 pending 很小（9–37，`1834976363` 609）不等于可闭：这些是曲面/guard 边界叶，plain 细分停滞，
   需 disj 专用路线；不要按 pending 数外推剩余时间。
5. 53 条 timeout 未区分「接近 limit」与「远未收敛」；180 s 内无输出，pending 不可得。若需细化，应加
   `--max-nodes` 阶梯或改为可 flush 的 pty 捕获，而不是延长单条墙钟。
6. stage-A 是**第二遍全叶编译器**，不是顺手回填；4 条 S 的 +1 h 是下限，整批 FAIL 风险按 E3.2 保留。
7. S 的 77 条是宽口径（含 flags 推断）；真正进入排期的 S 只有 A/B 的 4 条。
8. cert 已删除，只保留字节数；若后续要复用证书，需重探（closed 件都很快：≤11.7 s）。

## 9. 产物

- `COST-MATRIX.tsv`：88 行 × 15 列，表头逐字按工单。
- `CENSUS.md`：本文件。
- `logs/probe_*.log`：66 条探针原始 stdout/stderr（timeout 件为空，原因见 §3）。
- `logs/probe_index.tsv`：66 条探针的 status/leaves/nodes/pending/wall/cert_bytes/log 索引。
- `logs/probe_results.jsonl`：探针原始 JSONL（含 smoke 与主批）。
- `logs/emit_cases.log`、`logs/runner_stdout.log`：case 再生与调度器日志。
