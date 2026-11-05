# Evidence — lane `la26-rrcwnsj-w1`（`RRCWNSJ_p26`）

HEAD `8c003d0d4d31269dfd5c3af404b668b8a49a37dc`；cwd `/tmp/la26-rrcwnsj-w1/`；
`$S=/Users/zhangzhuo/c17_backup/lane_snapshots/la26-rrcwnsj-w1/`。
所有日志均 `script -q` pty 产出，读取一律 `tr -d '\r'`。

## 1. 主仓基线（开工时）

```
$ cd /Users/zhangzhuo/repos/kepler-conjecture-lean4 && git rev-parse HEAD
8c003d0d4d31269dfd5c3af404b668b8a49a37dc
$ git status --porcelain
A  docs/archive/lane-archives/pa25-rolling-w4/DELIVERY.md
A  docs/archive/lane-archives/pa25-rolling-w4/Evidence.md
A  docs/archive/lane-archives/pa25-rolling-w4/README.md
A  docs/archive/lane-archives/pa25-rolling-w4/kit-pa25-rolling-w4.diff
?? docs/archive/lane-archives/cone-text-triage-w1/
```
（以上 5 行为**他车道**预存状态，非本车道写入；本车道收工前复核见 §8。）

```
$ git show HEAD:lean/Kepler/Text/LocalAuto26.lean > $S/Work.lean
$ md5 $S/Work.lean lean/Kepler/Text/LocalAuto26.lean
78b3088caf43bbce68e07589acc901c7  (双侧一致)
$ wc -l $S/Work.lean
2095
```

## 2. 整文件编译（standalone，无 lake）

命令模板：
```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q $S/logs/<log> lean $S/<file>
```

| 日志 | 文件 | exit | `grep -c ': error:'` | `grep -c 'declaration uses `sorry`'` |
|---|---|---|---|---|
| `logs/base.log` | HEAD 原样 Work.lean | 0 | **0** | **3** |
| `logs/work1.log` | + 降维件（第 1 版） | 1 | 1 | 3 |
| `logs/work2.log` | + 降维件（第 2 版） | 1 | 1 | 3 |
| `logs/work3.log` | + 降维件（第 3 版，定稿） | **0** | **0** | **3** |

- 首轮 error 原文（`logs/work1.log`）：
  `Work.lean:847:4: error: Type mismatch` / `JKQEWGV2_p23 s v hs hk hBB hta has type ¬Circular (range v) ((fun i => {v i, v (i + 1)}) '' univ) but is expected to have type ¬Circular (v '' univ) (range fun i => {v i, v (i + 1)})`（`rw [← Set.image_univ]` 误改了第一个参数）；另 `:852:34 unknown identifier 'hlf'`（`obtain` 消耗假设）。
- 第二轮 error 原文（`logs/work2.log`）：`:835:16: error: (kernel) invalid projection ⋯.1`（`LocalFan` 投影 `.2.2.2.2.2` 不可用，改为 `obtain` 六元组重构）。
- 第三轮定稿：**0 error**。

own-sorry 三条（`grep -n "sorry" $S/Work.lean` 的实语句行）：`873`＝目标 `RRCWNSJ_p26`（未动）、`2079`＝`TAU_FUN_LE_p26`、`2112`＝`TAU_STAR_POS_p26`（后两条为本文件既有、未触）。
整文件 own-sorry **N=3 → M=3**（目标未闭合）。

Warning 谱面（`sed -n 's/.*warning: \(.*\)/\1/p' | sort | uniq -c`）base vs work3 **逐类一致**：
```
2 This simp argument is unused:
1 Try `simp at this` instead of `simpa using this`
3 `push_neg` has been deprecated. Prefer using `push Not` instead.
3 declaration uses sorry
```

## 3. HOL 原文核对（`lean/scripts/local/RRCWNSJ.hl`，878 行）

```
$ grep -c "JCYFMRP\|JLXFDMJ" lean/scripts/local/RRCWNSJ.hl
0
$ grep -n "ODXLSTCv2\|IMJXPHRv2" lean/scripts/local/RRCWNSJ.hl
345:THEN MRESAL_TAC ODXLSTCv2[`s`;`k`;`v`;`SUC x`][DE_MORGAN_THM;]
511:MRESAL_TAC IMJXPHRv2[`s`;`k`;`v`;`SUC x`][dist]
615:THEN MRESAL_TAC ODXLSTCv2[`s`;`k`;`v`;`x+k-1`][DE_MORGAN_THM;]
802:MRESAL_TAC IMJXPHRv2[`s`;`k`;`v`;`x+k-1`][dist]
$ grep -n "JKQEWGV2\|CIZMRRH\|AXJRPNC\|SYNQIWN\|JKQEWGV3" lean/scripts/local/RRCWNSJ.hl
259:THEN MRESAL_TAC JKQEWGV2[...]
263:THEN MP_TAC Wrgcvdr_cizmrrh.CIZMRRH
273:THEN MRESA_TAC Axjrpnc.AXJRPNC[...]
838:THEN MRESAL_TAC JKQEWGV3[...]
844:THEN MP_TAC SYNQIWN
```
结论：**JCYFMRP_V3 / JLXFDMJ 零命中**（分诊猜疑不成立）；阻塞件是 `ODXLSTCv2`/`IMJXPHRv2`。

## 4. 公理面（`#print axioms`，探针文件 `$S/AxCheck.lean` = Work.lean + 尾部 7 行；`logs/ax1.log`）

```
'_private._stdin.0.Kepler.Text.w5sgd_generic_of_no_lunar_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.RRCWNSJ_p26'   depends on axioms: [propext, sorryAx, choice, Quot.sound]
'Kepler.Text.AXJRPNC_p26'   depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.JKQEWGV2_p23'  depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.CIZMRRH'       depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.SYNQIWN_p22'   depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.JKQEWGV3_p23'  depends on axioms: [propext, choice, Quot.sound]
```
exit=0，`grep -c ': error:'` = 0。
（Lean 4.32 在此把 `Classical.choice` 打印为 `choice`，与工单口径一致。）

## 5. 缺口探针（`$S/ProbeGap.lean`：`import Kepler.Text.{LocalAuto1,28,31,34}` + 9 条 `#print axioms`；`logs/probegap.log`）

```
'Kepler.Text.ODXLSTCv2_concl'  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.IMJXPHRv2_concl' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.ZLZTHIC_concl'   depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.MHAEYJN_concl'   depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.RRCWNSJ_concl'   depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.ODXLSTCv2_p28'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.IMJXPHRv2_p28'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.ODXLSTCv2_p31'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.IMJXPHR_p34'     depends on axioms: [propext, Classical.choice, Quot.sound]
```
（LA1 的 `_concl` 是 `sorry`；LA28 的 `_p28` 真证，但 LA28 不在 LA26 闭包。）

## 6. 闭包 × 公理双验（`$S/PrereqCheck.lean` = Work.lean + 尾部 `#check`/`#print axioms`；`logs/prereq.log`）

`#check` 成功（在闭包内）且标准三：`WL_IN_E_p26`、`LUNAR_IN_V_p26`、`B_LE_2h0_A_EQ2_IN_CASES_6_p26`、`J_EMPY_CASES_6_p26`、`BB_RHO_NODE_IVS_p26`、`BB_F_SUC_PRE_p26`、`DIST_LE_2h0_IN_CASES_6_p26`、`DIST_EDGE_IN_BB_LE_2_p26`、`NORM_V_IN_BB_LE_CSTAB_p26`、`AXJRPNC_p26`、`OIQKKEP_p26`、`PPBTYDQ_p26`、`JKQEWGV2_p23`、`JKQEWGV3_p23`、`SYNQIWN_p22`、`CIZMRRH`、`CVLF_LF_F`、`HKIRPEP`、`LUNAR_COMM`、`LOCAL_FAN_CHARACTER_OF_RHO_NODE2`、`LOFA_IMP_NOT_COLL_IVS`、`LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT`、`IS_SCS_NOT_COLLINEAR_BBs_CASE_3_p23`、`MHAEYJN_p37`、`ZLZTHIC_p14`。

`#check` 成功但 **TAINTED**：
```
'Kepler.Text.ODXLSTCv2_concl'  depends on axioms: [propext, sorryAx, choice, Quot.sound]
'Kepler.Text.IMJXPHRv2_concl' depends on axioms: [propext, sorryAx, choice, Quot.sound]
```
`#check` 失败（闭包外，error 原文）：
```
PrereqCheck.lean:2157:7: error(lean.unknownIdentifier): Unknown identifier `Kepler.Text.CARD_V_EQ_SCS_K1_p31`
PrereqCheck.lean:2161:7: error(lean.unknownIdentifier): Unknown identifier `Kepler.Text.ODXLSTCv2_p28`
PrereqCheck.lean:2162:7: error(lean.unknownIdentifier): Unknown identifier `Kepler.Text.IMJXPHRv2_p28`
PrereqCheck.lean:2180/2181: Unknown constant `Kepler.Text.CARD_V_EQ_SCS_K1_p31`
```
（探针 exit=1 仅因上述 3 个刻意 `#check`；文件本体 0 error。）

## 7. 陈述冻结机检

```
$ git show HEAD:lean/Kepler/Text/LocalAuto26.lean | sed -n '/^theorem RRCWNSJ_p26 :/,/^  sorry$/p' > tgt_head.txt
$ sed -n '/^theorem RRCWNSJ_p26 :/,/^  sorry$/p' Work.lean > tgt_work.txt
$ md5 tgt_head.txt tgt_work.txt
23c6800c80a4c8800379b1f8b57c3e7b  (双侧一致)
$ wc -l tgt_head.txt   -> 8
$ cmp tgt_head.txt tgt_work.txt -> BYTE-IDENTICAL
```
即签名 8 行（含 `main_nonlinear_terminal_v11 →` 前件与全部显式/隐式参数）逐字未动，骨架仍单行 `:= by` + `sorry`。

## 8. 搬债审计与收工复核

```
$ grep -c "Kepler.Text.RRCWNSJ_p26" docs/e2e-reachability-map.tsv   -> 1
$ grep -n "Kepler.Text.RRCWNSJ_p26" docs/e2e-reachability-map.tsv
103:Kepler.Text.LocalAuto26	Kepler.Text.RRCWNSJ_p26	parent=Kepler.Text.RRCWNSJ_discharged
$ grep -c "AXJRPNC_p26"       docs/e2e-reachability-map.tsv         -> 0
$ grep -c "JCYFMRP_V3_p29"    docs/e2e-reachability-map.tsv         -> 0
$ grep -c "JLXFDMJ_p27"       docs/e2e-reachability-map.tsv         -> 0
$ grep -c "ODXLSTCv2_concl"   docs/e2e-reachability-map.tsv         -> 0
$ grep -c "IMJXPHRv2_concl"   docs/e2e-reachability-map.tsv         -> 0
$ grep -c "ZLZTHIC_concl"     docs/e2e-reachability-map.tsv         -> 0
$ grep -c "MHAEYJN_concl"     docs/e2e-reachability-map.tsv         -> 0
```
收工 `git status --porcelain`：仅新增本车道归档三件（staged）+ 他车道预存 5 行；无本车道未跟踪残留；`lean/Kepler/Text/LocalAuto26.lean` 与 HEAD 逐字相同（`git diff --stat` 空）。

## 9. olean 时效核（探针读的是 `.lake` 既有 olean）

`lean/.lake/build/lib/lean/Kepler/Text/` 下 olean 与源文件 mtime 对照：

```
LocalAuto1.lean   mtime 06:57:34   LocalAuto1.olean   mtime 06:58:03   （olean 后于源 ✓）
LocalAuto28.lean  mtime 11:46:02   LocalAuto28.olean  mtime 12:29:40   （✓）
LocalAuto26.lean  mtime 00:47:53   LocalAuto26.olean  mtime 12:23:14   （✓）
```
（LA1 最近提交时间 07:32:48 晚于其文件 mtime，属 `git add`+`commit` 不改写工作文件所致；工作树 `git status` 干净，故 olean 与 HEAD 源一致。）

独立于 olean 的**源级**复核（`git show HEAD:`）：

```
$ git show HEAD:lean/Kepler/Text/LocalAuto1.lean | sed -n '/^theorem ODXLSTCv2_concl/,/^$/p' | tail -2
    False := by
  sorry
$ ... IMJXPHRv2_concl ... | tail -2
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1))) := by
  sorry
```
→ TAINTED 判定为**源级**结论，不依赖 olean 新旧。

HEAD 在本车道收工前推进 `8c003d0d` → `d4bfa0cf`（他车道落库）；`git show d4bfa0cf:lean/Kepler/Text/LocalAuto26.lean` 的 md5 仍为 `78b3088caf43bbce68e07589acc901c7`，与本车道基线逐字相同，故 §2–§7 的实测读数在新 HEAD 上等效。

## 10. 已知陷阱（供后续车道）

1. 本文件 **EOF 没有 `end Kepler.Text`**：`#print axioms` 探针必须直接追加在 EOF（在 namespace 内），公共名仍可写全名；私有名写短名。
2. `LocalFan` 的 6 元组投影 `.2.2.2.2.2` 会触发 `(kernel) invalid projection`；用 `obtain ⟨hfan, x, hx, hFFeq, hDih, h2reg⟩ := hclf.1` 再重构。
3. `obtain` 会清除原假设；需保留时先 `have` 再 `obtain` 或显式重构。
4. `rw [← Set.image_univ]` 只对目标里的边像用，不要同时 `rw` 掉顶点 `Set.range v`（会把 `range v` 变成 `v '' univ` 造成 mismatch）。
