# Evidence — lane pa25-farm-plan

所有读数均为只读；主仓 tracked 零改动（`git status --short` = 0 行）。命令原文与输出如下，
可逐条复跑。交付时 HEAD 有并发车道漂移，见 E1。

## E1. 基线 / 工作树 / PA25 身份

```sh
$ cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
$ git rev-parse --short HEAD
a34cb699
$ git log --oneline -3
a34cb699 pa19-rdwkarc 落库: PA19 RDWKARC 真装配 ... queue 续255
1c0b328f map-metrics-v2 落库: 树优先指标 v2 ... queue 续254
a31177c9 packingconcl-c1-stage1 落库: PackingConcl 进 e2e Stage 1 ... queue 续253
$ git status --short | wc -l
0
$ wc -l lean/Kepler/Text/PackingAuto25.lean
12566
$ md5 -q lean/Kepler/Text/PackingAuto25.lean
a72280c8886c477bb0eb0e52578dcef1
$ stat -f '%Sm' -t '%Y-%m-%d %H:%M' lean/.lake/build/lib/lean/Kepler/Text/PackingAuto25.olean
2026-11-03 12:11
$ stat -f '%Sm' -t '%Y-%m-%d %H:%M' lean/Kepler/Text/PackingAuto25.lean
2026-11-03 12:14
```

**漂移说明**：任务书基线 `1c0b328f`；交付时 HEAD = `a34cb699`（并发 pa19-rdwkarc）。
两者之间只改两个文件，PA25 不在内：

```sh
$ git diff --stat 1c0b328f..HEAD
 docs/priority-queue.md              |  14 ++--
 lean/Kepler/Text/PackingAuto19.lean | 142 +++++++++++++++++++++++++++++++++++-
 2 files changed, 150 insertions(+), 6 deletions(-)
$ git rev-parse 1c0b328f:lean/Kepler/Text/PackingAuto25.lean HEAD:lean/Kepler/Text/PackingAuto25.lean
1ce617cc072c2cc46930862a49d366f6a0811050
1ce617cc072c2cc46930862a49d366f6a0811050
$ git diff --numstat 1c0b328f..HEAD -- lean/Kepler/Text/PackingAuto25.lean
(empty)
```

PA25 源 mtime 12:14 比 olean 12:11 新 3 分钟，但 blob 与 12:11 重编时的 HEAD 源一致
（queue 续253 ④ 记录：12:11 用 HEAD 源重编 PA25；12:14 是后续 checkout/touch）。
本报告的行号/计数对 `1c0b328f` 与 `a34cb699` 都成立。

## E2. 源级 sorry 计数（56 = 55 theorem + 1 def；任务书 57 = 旧 theorem 计数）

复现脚本：`logs/count_sorries.py`（去嵌套 `/- -/`、`--` 行注释、字符串；按最近前置
`theorem/lemma/def/abbrev` 归属）。

```sh
$ python3 -I logs/count_sorries.py /tmp/pa25-farm-plan/ours_head.lean
tokens=56 decls=56 admits=0
90      ox3q1hP25
2457    MCELL_WEDGE_UNIQUE
2756    LEAF_RANK_BIJ
2767    LEAF_RANK_GRUTOTI
2778    LEAF_RANK_GG_SUM
3168    MCELL3_DOMAIN
3176    TSKAJXY_3
5714    CELL_CLUSTER_ESTIMATE_REDUCE
5874    cc_prep_model_data
5986    CELL_CLUSTER_N_LE_1
8817    real_model_gamma_qu
8941    real_model_fhbv2_sym
9062    real_model_gckb
9071    real_model_sum_azim
9119    pkLeafRankCriticalEdge
9133    pkLeafRankAzimPointwise
9192    real_model_ox3q1h_merge
9535    critical_weight1
9546    critical_weight1a
9557    critical_weight1b
9573    real_model_quqy
9590    real_model_quqy_sym
9613    real_model_azim1
9626    real_model_gaz4
9639    real_model_gaz6
9652    real_model_gamma_qx
9665    real_model_g_qxd
10940   real_model_gamma10
10960   real_model_gamma11
10967   leaf_CIHTIUM
11032   gamma4fgcy_POS
11048   real_model_gamma8
11064   real_model_gamma8b
11080   real_model_gaz9
11098   real_model_azim2
11114   CC_3_SUM_SET
11129   CC_3_SUM_fn
11143   EDGE_IMP_K23
11156   CC_2_PROPS
11164   MCELL2_CRITICAL_WEIGHT1
11173   MCELL3_CRITICAL_WEIGHT
11182   MCELL3_008
11200   real_model_008
11214   real_model_cell23
11231   real_model_cell23_008
11243   GAMMAX_008a
11255   GAMMAX_008b
11266   real_model_3a
11277   real_model_3b
11287   real_model_gr
11329   real_model_pema
11341   real_model_pemb
11777   CC_3_AZIM_LT_PI_COPLANAR
11789   real_model_txq
11800   real_model_tew
12564   HL_IMP_BARV
```

- `def` 1 条 = `ox3q1hP25`（:90）；其余 55 条 theorem。
- 原始 `grep -c sorry` = **74** 行（含 18 处注释/docstring 里的 "sorry" 字样）。
- ztg4-w1 前后（`git show a3de6b76^` / `a3de6b76`）：

```sh
$ python3 -I logs/count_sorries.py /tmp/pa25-farm-plan/pa25_before_ztg4.lean | head -1
tokens=58 decls=58 admits=0
$ python3 -I logs/count_sorries.py /tmp/pa25-farm-plan/pa25_after_ztg4.lean | head -1
tokens=56 decls=56 admits=0
```

⇒ 任务书 "57 declaration-level" = ztg4-w1 **前**的 theorem 计数（58 项 − 1 def = 57）；
HEAD = 56 项 − 1 def = **55 theorem**。B0 replay 后 merged = 40 项（见 E6）。

## E3. 30 直源与 map 对账

```sh
$ awk -F'\t' 'NF==3 && $3 ~ /^parent=/ && $1=="Kepler.Text.PackingAuto25"' \
    docs/e2e-reachability-map.tsv | wc -l
30
$ awk -F'\t' 'NF==3 && $3 ~ /^parent=/ && $1=="Kepler.Text.PackingAuto25"' \
    docs/e2e-reachability-map.tsv | cut -f2,3 | sort
Kepler.Text.cc_prep_model_data      parent=Kepler.Text.LEAF_RANK_PROPS
Kepler.Text.ox3q1hP25               parent=Kepler.Assembly.textCapstone
Kepler.Text.pkLeafRankAzimPointwise parent=Kepler.Text.LEAF_RANK_PROPS
Kepler.Text.pkLeafRankCriticalEdge  parent=Kepler.Text.LEAF_RANK_PROPS
Kepler.Text.real_model_3a           parent=Kepler.Text.pkrmQy
... (26 real_model 全表见 logs/map_pa25_30.tsv)
```

`logs/map_pa25_30.tsv` = 30 行，逐字来自上述命令。

## E4. HOL 锚 / 证书 ID / 盒

### E4.1 HOL `real_model_*` 块的 bank/lemma（OXLZLEZ3.hl）

用只读 Python 按 `let real_model_* = prove_by_refinement(` 切块，提取
`get_pack_nonlinear_non_ox3q1h "..."`、`Merge_ineq.*`、`INTRO_TAC <name>`：

| Lean 源 | HOL 行 | 关键消费 |
|---|---|---|
| real_model_gamma_qu | 5716 | `MCELL4_DOMAIN`; `BIXPCGW 9455898160` |
| real_model_fhbv2_sym | 5853 | `MCELL4_DOMAIN`; `FHBVYXZv2 a`; `rad2_y` |
| real_model_gckb | 6026 | `GCKBQEA`; `MCELL4_DOMAIN`; `c_4_azim_mcell_dih_y` |
| real_model_sum_azim | 6070 | `LEAF_RANK_GRUTOTI`; `HL_2`; `critical_edge_y` |
| real_model_ox3q1h_merge | 6099 | `real_model_sum_azim`; `GG_MCELL_BETA/QUARTER`; periodic sums |
| real_model_quqy | 6564 | `mcell3_gammaX_gamma3f`; `GG_MCELL_QUARTER`; `g_quqya_g_quqyb_ALT`; `gamma4fgcy_sym23`; `rad2_y_sym` |
| real_model_quqy_sym | 6616 | `mcell3_gammaXb_gamma3f`; `GG_MCELL_QUARTER`; `g_quqya_g_quqyb_ALT` |
| real_model_azim1 | 6705 | `QITNPEA 5653753305`; `MCELL4_DOMAIN` |
| real_model_gaz4 | 6748 | `QITNPEA 6206775865`; `MCELL4_DOMAIN` |
| real_model_gaz6 | 6790 | `QITNPEA 3848804089`; `MCELL4_DOMAIN` |
| real_model_gamma_qx | 6832 | `gamma_qx_ALT`; `MCELL4_DOMAIN` |
| real_model_g_qxd | 6872 | `g_qxd_ALT`; `MCELL4_DOMAIN`; `wtcount6_y`; `beta_bumpA_y` |
| real_model_gamma10 | 6947 | `gamma10_gamma11_ALT`; `gamma4fgcy_sym23`; `wtcount6_y_sym23`; `beta_bumpA_y_sym23`; `MCELL4_DOMAIN` |
| real_model_gamma11 | 7008 | `gamma10_gamma11_ALT`; `CIHTIUM`; `GLFVCVK4 2477216213`; `quarter_norm2hh` |
| real_model_gamma8 | 7138 | `QITNPEA4 9063653052_weak_ALT`; `gamma4fgcy_POS`; `leaf_CIHTIUM`; `CC_4_PROPS` |
| real_model_gamma8b | 7221 | 同上（23-换位镜像） |
| real_model_gaz9 | 7310 | `QITNPEA 2134082733`; `QITNPEA 9939613598`; `gamma4fgcy_POS`; `gamma_wt`; `beta_bumpA_lb1` |
| real_model_azim2 | 7386 | `QITNPEA 9939613598`; `MCELL4_DOMAIN`; `CC_3_PROPS` |
| real_model_008 | 7849 | `SUM_LE`; `EDGE_IMP_K23`; `MCELL_BUMP_0`; `MCELL2_CRITICAL_WEIGHT1`; `CC_2_PROPS`; `MCELL3_008` |
| real_model_cell23 | 7924 | `CC_3_SUM_fn`; `CC_3_PROPS`; `real_model_008`; `DIHX_POS` |
| real_model_cell23_008 | 7975 | `real_model_008`; `MCELL3` 结构 |
| real_model_3a | 8127 | `TSKAJXY_3`; `CC_3_PROPS`; `CRITICAL_WEIGHT_POS_LE` |
| real_model_3b | 8162 | 同上 b 侧 |
| real_model_gr | 8197 | `real_model_cell23_008`; `GAMMAX_008a/b` |
| real_model_pema | 8258 | `real_model_cell23_008`; `PEMKWKU` |
| real_model_pemb | 8369 | `real_model_cell23_008`; `PEMKWKU`; `IXPOTPA`; `TXQTPVC`; `TEWNSCJ`; `FCHKUGT` |
| real_model_txq | 8713 | `real_model_cell23_008`; `GDRQXLGv3`; `CC_3_AZIM_LT_PI_COPLANAR` |
| real_model_tew | 8837 | `real_model_cell23_008`; `TEWNSCJ` |

> `Oxl_def.hl` / `Oxl_real.hl` / `Merge_ineq.hl` **不在仓内**：
> `find reference -name 'Oxl_def.hl' -o -name 'Oxl_real.hl' -o -name 'Merge_ineq.hl'`
> 返回空；`reference/flyspeck/text_formalization/packing/` 只有 `OXLZLEZ1.hl`。
> 因此 `ox3q1hP25` / `pkLeafRank*` 的 HOL 正本只能引用 triage/docstring，不能补写。

### E4.2 盒（PA21 `bank_*` def 原文）

```sh
$ python3 -I  # 按 def bank_<name> : Prop := ... 切块（只读）
```
关键盒（12 参 = y1..y6，`hminus/hplus` 为 PA21 常数）：

| bank | 盒 |
|---|---|
| `bank_BIXPCGW9455898160` | `[2hmin,2hplus]×[2,2hmin]⁵`；`γ4 > −0.00569` |
| `bank_FHBVYXZv2a` | `[2hmin,2hplus]×[2,2hmin]⁵`；`γ4>0.0057 ∨ rad2>2 ∨ eta(y1,y3,y5)²<1.34²` |
| `bank_GCKBQEA` | `[2hmin,2hplus]×[2,√8]⁵`；`dihY>0.606` |
| `bank_QITNPEA5653753305` | `[2hmin,2hplus]×[2,2hmin]⁵`；`γ4+0.0659−0.042·dihY>0` |
| `bank_QITNPEA6206775865` | `[2hmin,2hplus]×[2,2hmin]⁵`；`γ4+0.0142852−0.00609451·dihY>0` |
| `bank_QITNPEA3848804089` | `[2hmin,2hplus]×[2,2hmin]⁵`；`γ4−0.161517+0.119482·dihY>0` |
| `bank_QITNPEA9939613598` | `[2hmin,2hplus]×[2,2hmin]³×[2hplus,√8]×[2,2hmin]²` |
| `bank_QITNPEA2134082733` | `[2hmin,2hplus]×[2,2hmin]³×[2hmin,√8]×[2,2hmin]²` |
| `bank_GLFVCVK4` | `[2hmin,2hplus]×[2,√8]⁵` |
| `bank_GLFVCVK4a8328676778` | `[2hmin,2hplus]×[2,2hmin]³×[2hmin,2hplus]×[2,2hmin]²` |
| `bank_BIXPCGW1738910218a2` | `[2hmin,2hplus]×[2,√8]²×[2,2hplus]×[2,√8]²`；`dihY<2.3` |
| `bank_BIXPCGW7080972881a2` | `[2hmin,2hplus]×[2hmin,√8]×[2,√8]⁴`；`dihY<2.3` |
| `bank_BIXPCGW7274157868a` | `[2hmin,2hplus]×[2,2hmin]³×[2hplus,√8]×[2,2hmin]²`；`γ4>0.0057 ∨ dihY<2.3` |
| `bank_PEMKWU` | `[2hmin,2hplus]×[2,√8]×[2,2hmin]×[2,√8]×[2,2hmin]×[2,√8]` |
| `bank_TXQTPVC` | `[2hmin,2hplus]×[2,2hmin]²×[2,√8]×[2,2hmin]²` |
| `bank_TEWNSCJ` | `[2hmin,2hplus]×[2,2hmin]³×[2,√8]×[2,2hmin]²` |

> 全部 `bank_*` 是 `def : Prop`（PA21），由 `pack_nonlinear_non_ox3q1h` 合取承载；
> `proj_bank_*` 是 `hnl → bank_*` 的具名投影。Lean 闭包消费它们**不需要**重新发射证书。

## E5. 只读 API 探针（导入既有 PA25 olean）

命令（cwd `/tmp/pa25-farm-plan`，不在仓内）：

```sh
$ cd /tmp/pa25-farm-plan
$ LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) \
  nice -n 19 script -q probe_api.log lean probe_api.lean
$ echo $?
1
$ tr -d '\r' < probe_api.log | grep -c error
1
$ tr -d '\r' < probe_api.log | grep -cE '^[A-Za-z_].* : |^@[A-Za-z_].* : '
41
```

唯一 error（非本计划依赖）：

```
probe_api.lean:22:8: error(lean.unknownIdentifier): Unknown identifier `Kepler.Text.MCELL4`
```

（`MCELL4` 在 `PackingAuto4`，不在 PA25 namespace；删掉该行即可 0 error。）

41 项 `#check` 全通过，关键签名原文（节选，完整见 `logs/probe_api.log`）：

```
cc_4 : Set V3 → V3 → V3 → (ℕ → V3) → ℕ → Prop
cc_qy_v11 : CcV11 → ℕ → Prop
cc_bool_prep_v11 : CcV11 → Prop
cc_real_dat_def : ... (cc_qy_v11 (cc_data_v8 V f u0 u1) = fun i => ¬cc_4 V u0 u1 f i) ∧ ...
K4_CC_WI_ALT : ... ccKe V [elV ul 0, elV ul 1, f i] = 4 →
  ccCell V [elV ul 0, elV ul 1, f i] ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))
K4_CC_WIM : ... ccKe V [elV ul 1, elV ul 0, f i] = 4 →
  ccCell V [elV ul 1, elV ul 0, f i] ⊆ wedgeGe (elV ul 0) (elV ul 1) (f (i + (n - 1))) (f i)
CC_KE_34 : ∀ V ul, ccKe V ul = 3 ∨ ccKe V ul = 4
@EL_CC_UH : ... leaf V ul → (ccUh V ul).getD 0 0 = ul.getD 0 0 ∧ ...
@STEM_EDGEX : ... leaf V ul → {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0} ∈ edgeX V (ccCell V ul)
@ZASUVOR : ... leaf V [u0, u1, u2] → leaf V [u1, u0, u2] ∧ stem [u0,u1,u2] = stem [u1,u0,u2]
s_leaf_leaf : ∀ V ul, ∀ x ∈ s_leaf V ul, leaf V [elV ul 0, elV ul 1, x]
LEAF_RANK_S_LEAF : ... leaf_rank V ul w0 n f → f i ∈ s_leaf V ul
LEAF_RANK_TRUNCATE : ... leaf_rank V ul w0 n f = leaf_rank V [elV ul 0, elV ul 1] w0 n f
@PERIODIC_EQ_IMAGE : ... n ≠ 0 → periodic f n → i % n = j % n → f i = f j
@CC_CELL_NOT_NULLSET : ... leaf V ul → ¬nullSet (ccCell V ul)
GG_MCELL_GENERAL / QUARTER / BETA / NONBETA : ...（签名见 log）
c_4_azim_mcell_dih_y : ... cc_4 V u0 u1 f i → azim_mcell V f u0 u1 i = dihY ...
MCELL4_DOMAIN : ... cc_4 V u0 u1 f i → 2*hminus ≤ dist u0 u1 ∧ ... ∧ rad2YP25 ... < 2 ∧ 0 < deltaY ...
CC_3_PROPS : ... ¬cc_4 V u0 u1 f i → ccKe ... = 3 ∧ ... ∧ azim_mcell ... = azim ...
CC_3_SUM_fn : ... setSum {X | ...} fn = fn (ccCell V [u0,u1,f i]) + fn (ccCell V [u1,u0,f(i+1)]) + ...
real_model_008 : ... ¬cc_4 ... → setSum ... 0.008*dihX ≤ setSum ... γ*W + betaBumpV1
real_model_cell23_008 : ... ¬cc_4 ... → γ(A)W − 0.008*dihX(A) + (γ(B)W − 0.008*dihX(B)) + 0.008*azim ≤ gg
GAMMAX_008a : ... 0.008*dihX(ccCell A) ≤ γ(A)W
gamma4fgcy_POS : ... rad2YP25 ... < 2 → criticalEdgeY y1 → ... → 0 < gamma4fgcyP25 ...
leaf_CIHTIUM : ... leaf V [u0,u1,u2] → criticalEdgeY (dist u0 u1) → ... → False
critical_weight1a/1b : ... ¬cc_4 ... → criticalWeight ... = 1
cell3_from_ineq_thm : cell3_bank → cell3_from_ineq
mcell3_gammaX_gamma3f / mcell3_gammaXb_gamma3f : ... ¬cc_4 ... → gammaX ... = gamma3f ...
proj_bank_BIXPCGW9455898160 / FHBVYXZv2a / QITNPEA6206775865 / GLFVCVK4 /
QITNPEA2134082733 / BIXPCGW7274157868a / PEMKWU / GCKBQEA : pack_nonlinear_non_ox3q1h → bank_*
```

## E6. B0 replay 候选：三方合并 + kit 检查

基线/候选：

```sh
$ git show 76771f7e:lean/Kepler/Text/PackingAuto25.lean > base_76771f7e.lean   # 11714 行
$ wc -l base_76771f7e.lean
11714
$ wc -l /Users/zhangzhuo/c17_backup/lane_snapshots/poolc-w6-replay/PackingAuto25.replay-candidate.lean
12539
```

三方合并（ours = HEAD 的 PA25；base = 76771f7e；theirs = replay 候选）：

```sh
$ git merge-file -p --diff3 ours_head.lean base_76771f7e.lean theirs_candidate.lean > merged.lean
$ echo $?
0
$ grep -c '^<<<<<<<' merged.lean
0
$ wc -l merged.lean
13391
```

计数：

```sh
$ python3 -I logs/count_sorries.py ours_head.lean | head -1
tokens=56 decls=56 admits=0
$ python3 -I logs/count_sorries.py merged.lean | head -1
tokens=40 decls=40 admits=0
```

merged 关闭的 16 项 = 11 直源（gamma_qu、fhbv2_sym、azim1、gaz4、gaz6、gamma_qx、
g_qxd、gaz9、azim2、3a、3b）+ 5 kit（critical_weight1/1a/1b、
MCELL2_CRITICAL_WEIGHT1、MCELL3_CRITICAL_WEIGHT）；无重复声明
（`p25w5_bump_mem` / `gamma4fgcy_sym23P25` / 11 源各 1 处 `theorem` 声明）。

kit 生成与检查：

```sh
$ diff -u --label a/lean/Kepler/Text/PackingAuto25.lean \
         --label b/lean/Kepler/Text/PackingAuto25.lean ours_head.lean merged.lean \
  > kit-pa25-replay-w4w5w6.diff
$ git apply --stat kit-pa25-replay-w4w5w6.diff
 lean/Kepler/Text/PackingAuto25.lean | 857 ++++++++++++++++++++++++++++++++++-
 1 file changed, 841 insertions(+), 16 deletions(-)
$ git apply --check kit-pa25-replay-w4w5w6.diff
(no output; rc=0)
$ grep -E '^-' kit-pa25-replay-w4w5w6.diff | grep -v '^---' | sort | uniq -c
  16 -  sorry
```

删除面 = 恰 16 行裸 `sorry`，零结构行/注释/docstring 删除；import 区零改动。
**未在 HEAD 编译**；旧基线 76771f7e 的验证证据（poolc-w6-replay DELIVERY）：

- `pa25_replay_check1.log`：全文件 elaboration `EXIT=0`、0 error、36.9s、sorry 警告 42。
- `pa25_replay_probe5.log`：21 项 axioms 全 `[propext, choice, Quot.sound]`、零 sorryAx。
- `DELIVERY.md`：16/16 REPLAY-AS-IS，翻案 0，BLOCKED 0；唯一调整 G1
  （`p25w5_bump_mem` 用 HEAD/SF-76 副本，弃快照副本）。

## E7. poolc 快照逐件证据（证书/证体状态）

- `poolc-w4/DELIVERY.md`：闭源 7（gaz4/gaz6/azim1/gamma_qu/fhbv2_sym/gamma_qx/azim2），
  每件 bank 与证法一句；axioms 探针 7 件 + 私件全标准三；`pa25check1/2/3.log`
  三次全文件 `lake env lean` EXIT=0。
- `poolc-w5/DELIVERY.md`：闭源 2（g_qxd/gaz9）；`probe_w5.lean` 探针；
  gamma8b 定级下调为 **bank 级缺口**；gaz9 用 `p25w5_bump_mem` 私件。
- `poolc-w6/DELIVERY.md`：闭源 2（3a/3b），`cell3_from_ineq_thm` 路径实证；
  quqy/quqy_sym 仍卡 `GG_MCELL_GENERAL` 桩（注：该桩已被 SF-76 `4d706f1e` 关闭，
  下一波需重评）；gamma10/11、txq/tew/pema/pemb/gr 卡 3-胞 kit。
- `poolc-w6-replay/DELIVERY.md`：−11 维持；21/21 标准三；单提交方案。
- `poolc-w3/DELIVERY.md`：fhbv2 直源 −1（430d1f48 已落库）；fhbv2_sym/gamma_qu
  的"bank 缺口"经 w4 勘误为非缺口。

## E8. PackingConcl c1 证据

```sh
$ grep -n "rdwkarcConcl_pc\|PACKING_CHAPTER_MAIN_CONCLUSION_discharged\|RDWKARC_concl_discharged" \
    lean/Kepler/Text/PackingConcl.lean lean/Kepler/Assembly.lean
PackingConcl.lean:591:theorem rdwkarcConcl_pc : ¬keplerConjecture → ...
PackingConcl.lean:703:theorem RDWKARC_concl_discharged : ... := rdwkarcConcl_pc
PackingConcl.lean:716:theorem PACKING_CHAPTER_MAIN_CONCLUSION_discharged ...
Assembly.lean:6989:  obtain ⟨W, hWp, hWsub, hWlai⟩ := PACKING_CHAPTER_MAIN_CONCLUSION_discharged hneg hpnn hox3
```

- `rdwkarcConcl_pc` 体（PackingConcl:591–697）只消费 `UPFZBZM`（PA19）、`JGXZYGW_KY`、
  `PACKING_TRANS`、`RADV_TRANS_EQ`、三个私 kit；`hcc`/`hT` 是**参数**，未引用 PA25。
- `PACKING_CHAPTER_MAIN_CONCLUSION_discharged` 体（:716–723）：
  `refine rdwkarcConcl_pc hkc ?_ ?_`；第一支 `intro V hp hs; exact OXLZLEZ V hnl hox hp hs`
  → 30 源全在祖先锥；第二支 `exact TSKAJXY ...`（PA21，不涉 30 源）。
- c1 commit `a31177c9` 的 Assembly diff：`- PACKING_CHAPTER_MAIN_CONCLUSION hneg hpnn hox3`
  `+ PACKING_CHAPTER_MAIN_CONCLUSION_discharged hneg hpnn hox3`（一行 rewire + import）。
- PA25 端：`PACKING_CHAPTER_MAIN_CONCLUSION` :12302 → `OXLZLEZ` :12284 →
  `CELL_CLUSTER_ESTIMATE_PROPS` :12260 → `LEAF_RANK_PROPS` :9140 + `cc_real_model_data` :12228。

## E9. 26 非直源"当前零 Lean 引用"实证

对 26 个名字做去注释后的 token 扫描（排除自身声明行），全部 `refs=0`：

```sh
$ python3 -I  # 去注释/字符串后，按最近前置声明归属，排除 owner==name
MCELL_WEDGE_UNIQUE refs=0
LEAF_RANK_BIJ refs=0
LEAF_RANK_GRUTOTI refs=0
LEAF_RANK_GG_SUM refs=0
MCELL3_DOMAIN refs=0
TSKAJXY_3 refs=0
CELL_CLUSTER_ESTIMATE_REDUCE refs=0
CELL_CLUSTER_N_LE_1 refs=0
critical_weight1 refs=0
critical_weight1a refs=0
critical_weight1b refs=0
leaf_CIHTIUM refs=0
gamma4fgcy_POS refs=0
CC_3_SUM_SET refs=0
CC_3_SUM_fn refs=0
EDGE_IMP_K23 refs=0
CC_2_PROPS refs=0
MCELL2_CRITICAL_WEIGHT1 refs=0
MCELL3_CRITICAL_WEIGHT refs=0
MCELL3_008 refs=0
real_model_008 refs=0
real_model_cell23_008 refs=0
GAMMAX_008a refs=0
GAMMAX_008b refs=0
CC_3_AZIM_LT_PI_COPLANAR refs=0
HL_IMP_BARV refs=0
```

⇒ 它们不在 map 直源表（没有 proved 声明引用它们），是"填 30 源体后才会被消费"的 kit；
其中 `HL_IMP_BARV` 在 Lean 里连 HOL 的 `RAD_PI_IMP_WEDGE4` 路线都没走（Lean
`RAD_PI_IMP_WEDGE4` 已证且不引用它），故判**树外死 kit**。

## E10. 4 非 farm 依赖 grep

```sh
$ for n in K4_CC_WI_ALT K4_CC_WIM CC_KE_34 EL_CC_UH STEM_EDGEX ZASUVOR \
           s_leaf_leaf LEAF_RANK_S_LEAF LEAF_RANK_TRUNCATE PERIODIC_EQ_IMAGE; do
    grep -rn "theorem $n\|def $n" lean/Kepler/Text/*.lean | head -1; done
K4_CC_WI_ALT       PackingAuto25.lean:5219
K4_CC_WIM          PackingAuto25.lean:5320
CC_KE_34           PackingAuto18.lean:3038
EL_CC_UH           PackingAuto18.lean:3220
STEM_EDGEX         PackingAuto18.lean:7388
ZASUVOR            PackingAuto18.lean:2345
s_leaf_leaf        PackingAuto25.lean:1913
LEAF_RANK_S_LEAF   PackingAuto25.lean:4728
LEAF_RANK_TRUNCATE PackingAuto25.lean:4721
PERIODIC_EQ_IMAGE  PackingAuto25.lean:883
```

全部在库且已证（`#check` 探针 E5 通过）。HOL `cc_prep_model_data` 证法在
`lean/scripts/packing/OXLZLEZ3.hl:4021–4128`（~100 行 MESON：`CC_KE_34` 分 k=4/k=3，
k=4 用 `K4_CC_WI_ALT`，k=3 先证 b 侧 `ccKe=4` 再用 `K4_CC_WIM` + 周期性）。

## E11. 约束遵守 / 预算

- 主仓 tracked：`git status --short` = 0 行；未 `git apply` 任何 kit。
- 未跑 `lake`；未跑 G4/bb_arb/emit_rpn/emit_lean；未构建重片；未写 `/tmp/lfainteg`。
- 唯一编译类动作：E5 的 `lean probe_api.lean`（导入既有 PA25 olean，只读；41 项 `#check`）。
- 预算：约 44 调用 / 1h50m（上限 120 / 3h）。
- 交付目录 `$S=/Users/zhangzhuo/c17_backup/lane_snapshots/pa25-farm-plan/`：
  `DELIVERY.md`、`Evidence.md`、`kit-pa25-replay-w4w5w6.diff`、`logs/`。
