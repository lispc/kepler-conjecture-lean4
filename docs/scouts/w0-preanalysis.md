# W0 桌审静态预分析（w0prep-w1）

- 车道：w0prep-w1 ｜ 基线：`c200dac95e98c7f737156fa70dfe83b120e8e7b2`
  （2026-10-28 09:37:33 +0800）
- 上游输入：`docs/scouts/bola1-registry-scout.md`、
  `docs/scouts/bola1-dep-map.tsv`、`lean/Kepler/Text/LocalConcl.lean`
- 硬约束遵守：主仓 tracked 文件零写入；零构建零锁（`lake`/`lean` 未执行，
  探针只生成）；shell 仅 grep/rg/ls/wc/sed -n/awk + git 只读。
- **性质声明：本报告全部结论是静态先验，不是金标准。** W0 桌审的金标准是
  编译窗内对 62 条 WIRE 跑 `#print axioms`（探针 `w0probe.lean` +
  `run_w0.sh` 已备好，分钟级可完成）；两者逐条 diff 由 `run_w0.sh`
  步骤 3 自动产出 `w0-diff.txt`。

---

## 1. WIRE 清单口径（62 条的权威来源）

bola1 报告的「WIRE 62 = 16 classic + 46 assembly」在本树有一个更权威的
实文锚：**`LocalConcl.lean` 文件尾自带的 `#print axioms` debt ledger
（L1586-1613）恰好 62 行**，每行一条 `<name>_discharged`，全部位于
`namespace Kepler.Text`（L430-1615 实文核实）。该文件共 90 个
`_discharged` 定理出口，其余 28 条是 HOLD（证明体 `: by sorry`：HFNXPZA、
EQTTNZI1/2、EFLYGAU、BJTDWPS、ZITHLQN、WGDHPPI、TUAPYYU、YEBWJNG、
WKZZEEH、PWEIWBZ、VASYYAU、WKEIDFT、PEDSLGV1/2、OIQKKEP、YXIONXL2、
SYNQIWN、CQAOQLR、JLXFDMJ、LFLACKU、QKNVMLB1/2/3、OEHDBEN、TBRMXRZ1、
VPWSHTO、XWNHLMD —— 28 条，与 bola1 口径一致），**不进探针**。

与 `bola1-dep-map.tsv` 交叉核对：TSV 标 WIRE 的恰为同一组 62 条
（零缺漏零多余）；预测分布 CLEAN 7 / TAINTED 55 / UNKNOWN 0，62/62
名字与 ledger 逐一 diff 通过（`INVENTORY == LEDGER (62/62)`）。

## 2. 方法（自定，逐条可复核）

对每条 WIRE，从其在 `LocalConcl.lean` 的证明体出发做**引用闭包静态追踪**：

1. **读证明体**：term-mode 直接引用（`:= @Twin`）记孪生为唯一父件；
   tactic-mode 的 shim（`arrowSetRight` 置换、假设重排、`omega` 下标搬运、
   本文件 private 引理）先确认 shim 自身无 sorry（`arrowSetRight`
   L454、`continuousAt_cross3_right_lc` L439、`continuousAt_sqrt_upsX_mid`
   L473、`mkSimplex1_eq_p11` L463 均已证），再记真实父件。
2. **污染源判据**：闭包内出现 (i) 直接 `sorry` 证明体、(ii) 注入锚
   `mnt11_anchor`（LocalConcl:487）或 `p21_anchor`（L493）——两者本体
   就是 `sorry`——即判 TAINTED 并给锚点；闭包内所有引用均可证无 sorry
   到达才判 CLEAN。
3. **传递深度**：孪生→其依赖→再一层（LA24 case bank、LA22 记录件、
   LA33 slice/OPP 件均已下探两层）；Mathlib 侧只认三个标准公理
   propext / Classical.choice / Quot.sound，不算污染。
4. **注记时效**：2026-09-21 的 ledger/docstring 注记一律不用作结论，
   逐条对当前树实文复核（多处已过时，见 §4）。

预测三值：CLEAN（预测无 sorryAx 传递）/ TAINTED（预测 sorryAx 传递 +
污染源锚点）/ UNKNOWN（无法判定；本预测无一条落入）。

## 3. 预测分布与两张条件账

**分布：CLEAN 7 / TAINTED 55 / UNKNOWN 0**（逐条见
`w0-wire-inventory.tsv`）。

CLEAN 7：YXIONXL3、EYYPQDW、EYYPQDW2、EYYPQDW3、unadorned_MMs、
HXHYTIJ、DRNDRDV。前六条与 LocalConcl 尾注 debt ledger 的 2026-09-21
自述（"six are sorry-free"）一致，本次在当前树独立复核通过；
DRNDRDV 是唯一自带 sorry-free 注记且复核通过的 assembly wire
（闭包 = `derived_form_xrr_p22` → `hasDerivWithinAt_quad_p22`，
LA22:197-207，纯求导计算）。

### 直源口径

`docs/e2e-reachability-map.tsv` 的 LA1 23 直源行（实文核实）：
21 条 scs_arrow_v39 箭头（parent=`JEJTVGB_p16`：OTMTOTJ1-4、HIJQAHA、
CNICGSF1-5、ARDBZYE、FYSSVEV、AUEAHEH、VQFYMZY、BNAWVNH、RAWZDIB、
MFKLVDK、RYPDIXT、NWDGKXH、YOBIMPP、MIQMCSN）+ `WKEIDFT_concl`
（parent=EQ_DIAG_STAB_6I1_03）+ `main_nonlinear_terminal_v11`
（parent=textCapstone）。

其中 **21 条箭头的 LocalConcl 出口恰是 21 条 WIRE**；WKEIDFT 的出口是
HOLD(b)（显式 sorry，非 WIRE，W0 不适用）；mnt11 本身就是被注入的
锚 Prop（W0 不适用）。

### 账一（上限情形：W0 实测 21 条箭头 WIRE 全 cone-clean）

若金标准实测 21 条箭头 WIRE 全部无 sorryAx，则 21 条直源全部记「已闭」，
e2e 直源 **23 → 2**（立减 21；仅剩 WKEIDFT_concl 与
main_nonlinear_terminal_v11）。这是理论天花板——与静态先验矛盾度极大，
预期仅作对照锚。

### 账二（本预测情形：55 TAINTED / 7 CLEAN）

21 条箭头 WIRE 预测**全部 TAINTED**（逐条污染源见 TSV），故 W0 按先验
**立减 0，直源保持 23**。7 条 CLEAN WIRE 无一是直源出口，其 W0 价值是
**给波 1 提供已实证的干净孪生底座**（尤其 `YXIONXL3`：它是 CNICGSF
五条路线与 OTMTOTJ/FUNOUYH 路线共用的旋转半箭头引擎；`DRNDRDV` 是
ASSWPOW/终端链的 xrr 微擎）。两张账合并读：**W0 的直源立减数 =
21 条中实测 CLEAN 的条数，先验为 0；每实测翻案一条 CLEAN 即立减 +1。**

另记两条「改道即脱 taint」的 W0 可裁项（不改 e2e 行则不算立减）：
`MXQTIED_discharged`、`YRTAFYH_discharged` 虽预测 TAINTED（孪生
sorry），但其 LA1 本体 `MXQTIED_concl` / `YRTAFYH_concl` 已证
（2026-09-30/10-08）——若 W0 后把 e2e 行指向本体出口，这两件的清洁度
不受 WIRE taint 影响（本体侧 `#print axioms` 需另行审计，不在本 62 条内）。

## 4. 与 bola1「W0 后立减 5+」对账

**结论：立减 5 在 W0 不成立，须延后到波 1；「+」同样不成立。** bola1
§7 修正 1 的原话是条件句（"若 taint 来自已证输入则 e2e 直源立减 5
（CNICGSF1-5）"），本次静态追踪给出了该条件的实测答案——**taint 来自
未证输入**：

- `CNICGSF1-5_p18`（LA18:1158/1179/1198/1216/1235）五条孪生虽为真证，
  但每条各消费一个 **仍 sorried 的 LKGRQUI-lane slice 巨件**：
  `SCS_5I1_SLICE_02_p18`（LA18:1047）、`SCS_5I2_SLICE_02_p18`（:1056）、
  `SCS_5M1_SLICE_02/03/24_p18`（:1064/1072/1080）；
  且五条还共同消费 **LA1 本体 `YXIONXL3_concl`（LocalAuto1.lean:1683），
  其证明体至今仍是 `sorry`**——这是 bola1 报告没点名的第二污染源
  （TSV 只记了本体 sorry，未把它记为 CNICGSF 的污染路径）。
  → 五条 WIRE 预测 TAINTED，「立减 5」解锁前提 = 波 1 关闭 LKGRQUI
  slice 五件 + `YXIONXL3_concl` 本体灌证。
- 「+」的候选（LA33 六箭头 AUEAHEH/VQFYMZY/BNAWVNH/RAWZDIB/MFKLVDK/
  RYPDIXT）同样全部 TAINTED：`GSXRFWM1_p33`（LA33:524）、
  `SCS_4I1_SLICE_02_p33`（:1516）、`OPP_IS_SCS_p33`（:126，ZNLLLDL/
  VQFYMZY 经 4I3 箭头链间接消费）、四个 4M*-slice 件（:2032/2213/2347/
  2354/2536）均仍 sorry。解锁前提 = 波 1/波 2 的 LA33 slice+OPP kit。
- 附带翻案两则（记档）：
  (i) `ARDBZYE_p33`/`FYSSVEV_p33` 现为**直接 sorry**（LA33:1285/1506），
  LocalConcl docstring「PROVED ... modulo the anchor」已过时；
  (ii) `XWITCCN2_p27`/`AYQJTMD_p27` 孪生确已证，但闭包经
  `UXCKFPE2_p27`→`UXCKFPE_p24`（LA24:1395）落到 **k=3/4/5/6 四个 case
  lemma 全 sorry**（LA24:1387/1128/1163/1196）——TSV「已证」注记在
  axiom 意义下不成立，正是 W0 审计要抓的「已证 ≠ sorry-free」。
  (iii) `BKOSSGE_p16` 本体无 sorry（w1asm 车道翻案属实，LA16:254 真证），
  但闭包含 `is_scs_3T1/3T5/3M1_p22`（LA22:1668/1688/1703 全 sorry）→
  WIRE 仍 TAINTED。

## 5. 风险与不确定性（最大一条）

**最大不确定性：静态追踪的传递深度有限。** 本预测对孪生闭包下探约两层
（孪生→直接依赖→关键子件），不是编译器级的完整 axiom 闭包：CLEAN 7 条
中若某条的上游已证件在更深处引用了未展开的 sorried def 或
`Classical.epsilon` 之外的.choice 重导出，静态判读会漏；反之 TAINTED
55 条的污染源锚点是高置信的（绝大多数是直接 sorry 或注入锚）。
run_w0.sh 的 diff 步骤就是为吸收这个残差设计的——窗口期实测若翻案，
以 `w0-diff.txt` 的 MISMATCH 清单为准修订本表。

次要风险：基线在 W0 执行前若前移（任一波次合入），`YXIONXL3_concl`
本体灌证或 LKGRQUI slice 关闭都会使 CNICGSF 五条翻 CLEAN，届时预测表
第 4 列需按 `w0-diff.txt` 修订，立减 5 即时生效（直源 23→18）。

## 6. 交付物清单

| 文件 | 内容 |
|---|---|
| `w0-wire-inventory.tsv` | 62 行 = {name, wire 锚, 孪生锚, 预测, 污染源/依据}，与 LocalConcl ledger 62/62 diff 通过 |
| `w0probe.lean` | `import Kepler.Text.LocalConcl` + 62 行全限定 `#print axioms Kepler.Text.<name>_discharged`（ledger 序），只生成未运行 |
| `run_w0.sh` | 窗口期一键：`lake env lean` 跑探针 → 规范化 `w0-result.tsv` → 与预测表 join 出 `w0-diff.txt`（MISMATCH 清单）；`bash -n` 语法检查通过，未运行 |
| `w0-preanalysis.md` | 本报告 |
| `DELIVERY.md` | 交付清单 + 预测分布 + 一句风险 |
| `PROGRESS.md` | 车道进度快照 |
