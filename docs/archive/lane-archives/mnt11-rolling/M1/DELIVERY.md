# DELIVERY — `mnt11-rolling` M1

- 基线：HEAD `2a7ed0b2`（2026-11-05）。
- 范围：只做 M0 判定的 1 条 `PROVABLE`：`6843920790`（`mainEstimate_6843920790`）。
- 证书农场：未运行；88 条 NEEDS-CERT 只做静态队列（`CERT-QUEUE.md`）。

## 1. 落点选择（新文件 vs 追加 T11Glue）

**选择：新文件 `lean/Kepler/T11Proofs.lean`（111 行）**。理由：

1. `T11Glue.lean` 的定位是「证书 glue」（每条 = 一个 `Interval.Cases.C*` 证书的粘合），
   本件是 **cert-free 算术证明**，混进去会污染两类产物的审计面。
2. 新文件只 `import Kepler.Text.LocalAuto1`，不引入 Assembly/LocalConcl；
   `T11Glue` 则拉入 20 个 C* 证书模块。单开新文件让本件的 import 面最小。
3. 常驻宪法建议 `T11Proofs.lean` 作为后续 cert-free 证明的落点；M1 先立骨架。

定理名：**`Kepler.Text.T11Proofs.t11_6843920790`**（不叫 `glue_C…`：本件不是证书 glue，
`t11_` 与车道 id 约定一致）。

## 2. 验收（standalone）

命令：

```bash
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean
nice -n 19 lake env lean Kepler/T11Proofs.lean
```

实测：

- **RC=0**；`real 23.70 / user 21.44 / sys 2.80`（秒）；`error` = **0**。
- 仅 3 条 `push_neg` deprecated warning（不影响）。
- 源码静态检查：`grep -nE "sorry|admit|native_decide"` → **零命中**；无 `axiom` 声明。
- 未改 `LocalAuto1.lean` 任何陈述（本件只 import）。

`#print axioms`（校验副本 `logs/T11Proofs_check.lean`，RC=0）：

```
'Kepler.Text.T11Proofs.t11_6843920790' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. patch

- `patch.diff`：仅新增 `lean/Kepler/T11Proofs.lean`（111 行，1 个 `+++` 文件）。
- 基于 `2a7ed0b2`；在干净 detached worktree（`git worktree add --detach … 2a7ed0b2`）里
  `git apply --check patch.diff` → **RC=0**。
- 主仓 worktree 的 tracked 改动 = 本件之前已存在的他车道改动（DECISIONS/SF-102/Reduction5 等）；
  本件只新增未跟踪文件 `lean/Kepler/T11Proofs.lean`，不触碰任何 tracked 文件。落库请用 `patch.diff`。

## 4. CERT-QUEUE（只读产出）

`CERT-QUEUE.md`：88 条 NEEDS-CERT 的静态发射队列。

- 输入：`prep.hl` 的 `ineq [...]` 盒 + 目标表达式；既有 `Interval/Cases/*` 头注
  `cert: N leaf/leaves`、顶层行数、`Shard*.lean` 数。
- 每条含：idv / prep 盒 `F/I`（固定 vs 区间，含具体维）/ 目标函数 / 同族 C* 参照
  （行/分片/叶）/ 档位。
- 档位分布：**S 5 / M 15 / L 27 / XL 41**（XL 中 35 条是 `7550003505 *` T755 模板批，
  一次发射共享；非模板 XL 仅 6 条）。
- 无 solver、无证书发射；真实 leaf 数 UNRESOLVED，档位是静态相对成本。

## 5. 文件

```
patch.diff                 # 新增 T11Proofs.lean 的 patch（基于 2a7ed0b2）
T11Proofs.lean             # 交付副本（源头在 lean/Kepler/T11Proofs.lean）
CERT-QUEUE.md              # 88 条 NEEDS-CERT 静态队列
logs/T11Proofs_build.log   # standalone RC=0 输出
logs/T11Proofs_axioms.log  # #print axioms 实测
logs/T11Proofs_check.lean  # 带 #print 的校验副本
logs/cert_table.md         # 队列原始表
```
