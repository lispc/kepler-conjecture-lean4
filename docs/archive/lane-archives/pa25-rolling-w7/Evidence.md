# Evidence — pa25-rolling-w7

所有读数为命令原文 + 原始输出。cwd = `/tmp/pa25-rolling-w7/`（车道 scratch），
`$S = /Users/zhangzhuo/c17_backup/lane_snapshots/pa25-rolling-w7/`。

## E1. 基线（继承字节 ≠ 已验证，开工先整文件打绿）

```
$ md5 lean/Kepler/Text/PackingAuto25.lean
MD5 (lean/Kepler/Text/PackingAuto25.lean) = 766b6b2a86f6aacce24190a14d9a6077
$ wc -l lean/Kepler/Text/PackingAuto25.lean
   15417 lean/Kepler/Text/PackingAuto25.lean

$ cp .../PackingAuto25.lean /tmp/pa25-rolling-w7/Work-baseline.lean
$ LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
    script -q /tmp/pa25-rolling-w7/logs/base-full.log lean Work-baseline.lean
RC=0
$ tr -d '\r' < logs/base-full.log | grep -c 'declaration uses `sorry`'
13
$ tr -d '\r' < logs/base-full.log | grep -c 'error'
0
$ tr -d '\r' < logs/base-full.log | grep -c ': warning:'
175
```

与 w6 DELIVERY 记载的 15,417 行 / 12 裸 sorry / 13 sorry 警告 / 0 error / MD5
`766b6b2a…` **完全一致**。基线确认。

## E2. 12 裸 sorry 的宿主声明（逐行上溯）

```
$ for L in 6155 6503 9877 9954 10581 10598 12201 12221 13883 13895 14569 14580; do
    awk -v L=$L 'NR<L && /^(theorem|lemma|def|...)/{ln=NR;txt=$0} END{...}' ...
  done
6155  -> theorem CELL_CLUSTER_ESTIMATE_REDUCE
6503  -> theorem CELL_CLUSTER_N_LE_1
9877  -> theorem pkLeafRankCriticalEdge
9954  -> theorem real_model_ox3q1h_merge
10581 -> theorem real_model_quqy
10598 -> theorem real_model_quqy_sym
12201 -> theorem real_model_gamma10
12221 -> theorem real_model_gamma11
13883 -> theorem real_model_pema
13895 -> theorem real_model_pemb
14569 -> theorem real_model_txq
14580 -> theorem real_model_tew
```

第 90 行 `def ox3q1hP25 : Prop := sorry` = 第 13 条（冻结，不动）。

## E3. 探针链（每件小探针打通再整文件）

探针提速：`lean/.lake/build/lib/lean/Kepler/Text/PackingAuto25.olean`
（Nov 5 14:46，与 HEAD 源同版）可用，故探针 `import Kepler.Text.PackingAuto25`
后单轮 ~20s，而非整文件 5–6 min。

```
$ p0.lean: import Kepler.Text.PackingAuto25 ; #check / #print on 5 件
RC=0
real_model_cell23_008 : ∀ (V : Set Kepler.Geom.V3) ... (Kepler.Packing V) ...
CC_3_PROPS : ∀ ... (Kepler.Packing V) ...
（注：`Packing` 需全名 `Kepler.Packing`，`open Kepler.Text` 不够）

$ lean p-txq.lean   -> RC=0
$ lean p-tew.lean   -> RC=0
$ lean p-pema.lean  -> RC=0
$ lean p-pemb.lean  -> RC=0
```

迭代记录（每轮 error 数）：txq 2→1→“le_of_not_lt 不存在”+3→1→0；
tew 3→2→0（重写为 y4 见证 + `b_spine5 ≤ 0`）；pema 4→1→1→1→0；
pemb 1→0。全部单进程串行。

关键修正（备 w8 复用）：
- `le_of_not_lt` 在本 Mathlib 无 → 用 `not_lt.mp`。
- `intro i hno4 hltA …` 失败：`∀ i, (A ∧ B ∧ …) → C` 只有 **两个** binder，须
  `intro i h; obtain ⟨…⟩ := h`。
- `mul_self_le_mul_self` 签名是 `(0 ≤ a) → (a ≤ b) → a*a ≤ b*b`（非反过来）。
- `rad2YP25` vs `yOfX rad2X` 是 defeq 但非 syntactic：`rw` 前须
  `have h2' : rad2YP25 … := h2`（elaborator 接受 defeq）。
- `linarith [hbank, hEq, hc23]` 中 `hEq` 必须是等式（**不是** `rw [← hEq]`）；
  若等式方向记错，`rw` 报「pattern 不在目标中」而非等式错误。

## E4. 整文件集成（4 件入 Work.lean）

```
$ python3 集成脚本（替换 4 条 `  sorry` + 前置 helper 块）
decl starts: {'real_model_pema': 13873, 'real_model_pemb': 13885,
              'real_model_txq': 14559, 'real_model_tew': 14571}
replaced: {'real_model_txq', 'real_model_pemb', 'real_model_tew', 'real_model_pema'}
lines: 15856   （含尾部空行；$S/Work.lean wc -l = 15855）
裸 sorry 行数: 8

$ LEAN_PATH=… nice -n 19 script -q logs/w7a-full.log lean Work-w7.lean
RC=0
$ grep -c ': error:'                                     -> 0
$ grep -c 'declaration uses `sorry`'                     -> 9
```

## E5. 公理面（4 件 + 4 枚新私件）

```
$ LEAN_PATH=… nice -n 19 script -q logs/w7-axioms.log \
    lean $S/axioms-probe-pa25-rolling-w7.lean
RC=0
': error:'      -> 0
': warning:'    -> 171
'declaration uses `sorry`' -> 9

'Kepler.Text.real_model_pema' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_pemb' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_txq'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_tew'  depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«…».0.Kepler.Text.p25w7_rhoX_sym23' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«…».0.Kepler.Text.p25w7_rad2X_sym23' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«…».0.Kepler.Text.p25w7_rad2Y_sym23' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«…».0.Kepler.Text.p25w7_gamma23Keep135X_yOfX_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

8/8 标准三，零 sorryAx。

## E6. 陈述冻结（与 HEAD 逐字 cmp）

```
$ python3 正则抽 theorem <name> … := by 整段，两份文件对照
real_model_pema IDENTICAL 619
real_model_pemb IDENTICAL 619
real_model_txq  IDENTICAL 614
real_model_tew  IDENTICAL 572
ox3q1hP25 line90 identical: True
$ sed -n '90p' Work.lean
def ox3q1hP25 : Prop := sorry
```

## E7. 补丁与 `git apply --check`（只读）

```
$ git -C <repo> diff --no-index --src-prefix=a/ --dst-prefix=b/ \
    <repo>/lean/Kepler/Text/PackingAuto25.lean /tmp/pa25-rolling-w7/Work-w7.lean
（路径重写为 a/lean/Kepler/Text/PackingAuto25.lean,
             b/lean/Kepler/Text/PackingAuto25.lean）

$ head -4 $S/patch-pa25-rolling-w7.diff
diff --git a/lean/Kepler/Text/PackingAuto25.lean b/lean/Kepler/Text/PackingAuto25.lean
index 781e0aae..02d47f5d 100644
--- a/lean/Kepler/Text/PackingAuto25.lean
+++ b/lean/Kepler/Text/PackingAuto25.lean

$ git apply --stat $S/patch-pa25-rolling-w7.diff
 lean/Kepler/Text/PackingAuto25.lean |  446 +++++++++++++++++++++++++++++++++++
 1 file changed, 442 insertions(+), 4 deletions(-)

$ git apply --check $S/patch-pa25-rolling-w7.diff && echo PASS
APPLY-CHECK: PASS          （HEAD a509e470；PA25 MD5 仍 766b6b2a…）

$ grep -c '^@@' patch   -> 5
@@ -13870,6 +13870,59 @@  theorem JSP_BOUNDS …
@@ -13880,7 +13933,108 @@ theorem real_model_pema …
@@ -13892,7 +14046,105 @@ theorem real_model_pemb …
@@ -14566,7 +14818,111 @@ theorem real_model_txq …
@@ -14577,7 +14933,89 @@  theorem real_model_tew …
```

5 hunk 全落在 4 件 + helper 块，**无附带漂移**（`ox3q1hP25` 与 624 shard 面零触碰）。

## E8. 主仓 tracked 零改动

```
入场时 git status --porcelain:
 A lean/Kepler/Text/TameCorrBase.lean       （他车道 staged，未触碰）
?? docs/archive/lane-archives/pa25-rolling-w6/  （w6 归档，未触碰）

工作期间 HEAD 由 726faa79 → a509e470（他车道：TameCorrBase 落库，PA25 未变）。

本车道结束前 git status --porcelain:
 M docs/priority-queue.md                   （他车道的改动，非本车道）
```

本车道**未修改任何 tracked 文件**；唯一新增为显式要求的归档目录
`docs/archive/lane-archives/pa25-rolling-w7/`（patch + DELIVERY + Evidence +
WORKORDER-w8；Work.lean 不入库，与 w6 惯例一致）。

## E9. 缺失件盘点（W7-C 侦察，供 w8）

```
$ grep -rn "theorem rad2_x_eta_x|UPS_X_POS|rad2X_sym03|betaBumpA_y|beta_bumpA_lb1" \
    --include=*.lean Kepler/Text/
（以上全部 0 命中）

命中（在库）：etaX (IneqClosureDefs:606)、betaBumpLb (IneqClosureDefs:493)、
norm2hh (IneqClosureDefs:335)、beta_bumpA_yP25 真体 (PA25:113)、
GG_MCELL_GENERAL (PA25:9233)、wtcount6_y_sym23 (PA25:10929)、
beta_bumpA_y_sym23 (PA25:10943)、ztg4w1_quarter_norm2hh (PA25:11291)、
proj_bank_GLFVCVK4* / proj_bank_QITNPEA5400790175a,b / proj_bank_FWGKMBZ (PA21)
```

`gamma10_gamma11_ALT` / `gamma10_gamma11` 在 Lean 全无（HOL
`merge_ineq.hl:3997-4085`）；`gamma4fgcy_sym23` 无同名件。
