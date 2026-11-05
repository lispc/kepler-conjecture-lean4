# EVIDENCE — pa25-rolling-w8

> 全部输出为机器实测；命令均在 `/tmp/pa25-rolling-w8/` 车道内执行，
> `LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt)`，`nice -n 19`。

## E1. 基线核对

```
$ cd . && git log --oneline -1          # 开波时
aa4732a9 归档 pa25-rolling-w7 交付 (DELIVERY/Evidence/WORKORDER-w8/patch)
$ md5 lean/Kepler/Text/PackingAuto25.lean
MD5 (...) = 6363af3367799573760fdef59983a46d        # 与 WORKORDER-w8 头一致
$ wc -l lean/Kepler/Text/PackingAuto25.lean
15855
$ grep -n '^  sorry$' lean/Kepler/Text/PackingAuto25.lean
6155, 6503, 9877, 9954, 10581, 10598, 12201, 12221   # 8 裸 sorry
90: def ox3q1hP25 : Prop := sorry                        # DEFHOLE
```

收尾时主仓 HEAD 已被其它车道推进到 `7e5ed1c1`（docs），但
`lean/Kepler/Text/PackingAuto25.lean` 仍为基线字节（MD5 同上、15,855 行），
patch 在该 HEAD 上 `git apply --check` 仍通过。

## E2. W8-A/B/C 探针（olean 快路径，每轮 ~20 s）

`logs/probe1.log`：

```
'Kepler.Text.p25w8_rad2_x_eta_x' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_rad2_eta2'    depends on axioms: [propext, Classical.choice, Quot.sound]
RC=0
```

`logs/probe2.log`：

```
'Kepler.Text.p25w8_g_quqya'            depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_real_model_quqy'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_real_model_quqy_sym' depends on axioms: [propext, Classical.choice, Quot.sound]
RC=0
```

`logs/probe3.log`：

```
'Kepler.Text.p25w8_gamma10_gamma11'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_real_model_gamma10'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_real_model_gamma11'  depends on axioms: [propext, Classical.choice, Quot.sound]
RC=0
```

探针源码：`logs/probe1.lean`（W8-A kit）、`logs/probe2.lean`（g_quqya + quqy×2）、
`logs/probe3.lean`（gamma10/11 分析核 + 装配×2）。三份均 `import
Kepler.Text.PackingAuto25` + 新名，故不污染主文件。

## E3. 首轮整编（暴露前向引用，留档）

```
$ nice -n 19 lean /tmp/pa25-rolling-w8/work/lean/Kepler/Text/PackingAuto25.lean
/tmp/.../PackingAuto25.lean:10734:6: error(lean.unknownIdentifier): Unknown identifier `gamma4fgcy_sym23P25`
/tmp/.../PackingAuto25.lean:10721:61: error: unsolved goals
RC=1
```

原因：`gamma4fgcy_sym23P25`(11032)/`rad2YP25_sym23P25`(10970) 定义在 quqy(10709)
之后（Lean 无前向引用）。修复：改用同文件更早的私件 `p25w4_gamma4fgcy_sym23`(9521)
/`p25w4_rad2YP25_sym23`(9509)。`logs/full_w8a_b_c.log` 为原始留档。

## E4. 收尾整编 + `#print axioms`（决定性证据）

文件：`work/print_version.lean` = 交付文件 + 末尾 8 行 `#print axioms`
（print 行不入 patch）。命令：

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) \
  nice -n 19 script -q /tmp/pa25-rolling-w8/logs/full_print.log \
  lean /tmp/pa25-rolling-w8/work/print_version.lean
RC=0
```

日志统计（`logs/full_print.log`）：

```
errors: 0
'Kepler.Text.real_model_quqy'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_quqy_sym'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_gamma10'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_gamma11'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_rad2_eta2'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_rad2_x_eta_x'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_g_quqya'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_gamma10_gamma11' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`declaration uses 'sorry'` 警告 5 条，全部为遗留：

```
print_version.lean:90:4    ox3q1hP25 (DEFHOLE)
print_version.lean:6150:8  CELL_CLUSTER_ESTIMATE_REDUCE
print_version.lean:6498:8  CELL_CLUSTER_N_LE_1
print_version.lean:9869:8  pkLeafRankCriticalEdge
print_version.lean:9930:8  real_model_ox3q1h_merge
```

=> 裸 sorry 8→4；编译器 sorry 警告 9→5；error 0。

## E5. patch 与主仓状态

```
$ diff -u -L a/lean/Kepler/Text/PackingAuto25.lean \
         -L b/lean/Kepler/Text/PackingAuto25.lean \
         <base> work/lean/Kepler/Text/PackingAuto25.lean > patch.diff
$ cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
$ git apply --check /tmp/pa25-rolling-w8/patch.diff && echo APPLY-CHECK-OK
APPLY-CHECK-OK
$ git apply --stat /tmp/pa25-rolling-w8/patch.diff
 lean/Kepler/Text/PackingAuto25.lean | 340 +++++++++++++++++++++++++++++++++++
 1 file changed, 336 insertions(+), 4 deletions(-)
$ grep '^-' patch.diff | grep -v '^---'
-  sorry
-  sorry
-  sorry
-  sorry
$ md5 /tmp/.../work/lean/Kepler/Text/PackingAuto25.lean
2c18464087f8f871ae0b92468900b4bd   （16,187 行）
```

删除面逐行 = 4 条裸 `  sorry`；无其它删除。主仓 `git status` 仅开波前既有的
`M docs/priority-queue.md`（非本车道改动）。

## E6. 新增声明清单（新文件行号）

```
10567 private p25w8_deltaX_sym14     (deltaX (1 4)(2 5)-槽对称，ring)
10571 private p25w8_rhoX_sym14       (rhoX 同槽对称，ring)
10575 private p25w8_rad2X_sym14      (rad2X 同槽对称)
10582        p25w8_upsX_sq_pos       (HOL UPS_X_POS：2≤a,b,c<4 → 0<upsX(a²,b²,c²))
10600        p25w8_rad2_x_eta_x      (HOL merge_ineq.hl:3841)
10628        p25w8_rad2_eta2         (HOL merge_ineq.hl:3869)
10656        p25w8_g_quqya           (HOL g_quqya_goal :3907)
12368        p25w8_gamma10_gamma11    (HOL gamma10_gamma11 :3997)
```

证明体替换：10709 quqy、10748 quqy_sym、12455 gamma10、12502 gamma11
（陈述与 docstring 一字未动）。
