# DECISIONS.md — 决策日志

> 依据 PLAN.md §2：任何偏离已锁定决策的变更必须先在此记录理由并向人类汇报。
> 新条目追加在顶部（倒序）。

## 2026-11-06 — Reduction5 口径改口 + PA22 `k` 因子一并走 SF（用户裁决）

**背景**：`reduction5-scout`（只读）实测推翻了两项既有判断。

**拍板 1（用户选「接受口径 + 先发 W0」）：`Reduction5` 从"一波"改为"长周期背景工程"**。

- **实测规模**：最小闭包（`reduction1..5` + `betwn_core*`，18,887 有效 HOL 行）
  → Lean **24,400–39,400 行**；真实模块闭包（45 模块 / 48,052 未移植有效行）
  → **63,100–102,000 行**。原裁决「1,500–3,000 行」**低 8–26 倍**（真实闭包低 21–42 倍）。
  倍数取自本仓实测经验比（`tame_list` 1.30x / `AUQTZYZ` 1.60x / `DANGEYJ` 1.70x /
  `RXOKSKC` 2.07x / `hypermap` 0.91x）。
- **`jcajydu` 本体反而比原估计乐观**：约 **100–250 行**（原估 300–800），
  但四个装配件 `RXOKSKC`/`JXBJOAB`/`GNBEVVU`/`DAKEFCC` 锁在环后。
- **两项判定**：① TameSpine 岛**没有** `Reduction5` 移植（是移植不是接线；
  岛 75 文件头注映射 0 个 `reduction*.hl`）；② HOL `hypermap` 与 Lean
  `IsHypermapOfListTl` **是同一概念**（类型层/实例层/规格层逐槽对上，
  `TameCorrBase` 的 `isHypermapOfListTl_iff_eq_hypermapOfList` 把规格≡构造接起来）
  ⇒ 施工口径：落到 `hypermapOfList L hL` 的构造形，不停在 `∃ H` 形。
- **落点（已定）**：两级新叶 `Kepler/Text/Reduction5Base.lean`（defs）+
  `Kepler/Text/Reduction5.lean`（theorems），唯一 import 走 `TameLp` + `Graphs.ListAux`
  （两者闭包零 `Kepler.Assembly`，而 `Assembly` 今天已 import `TameLp` ⇒ 可被 Assembly 直接消费、零环）。
  **否决**并入 `TameCorrBase`（毁其 174 行可审计不变式）与落岛（74/75 成环 ⇒ e2e 收益恒 0）。
- **强制前置**：reduction 链的 `core`/`parts`/`quotient_list`/`transform_list`/`ntrans`/
  `rtrans`/`ytrans`/`ztrans`/`transform_count`/`ifbetwn` 等**只在岛内定义**，必须从 HOL 重落
  （这就是 W0）。`betwn`/`split_at` 已在 `Kepler.Graphs.ListAux`（环自由）。
- **执行**：W0 立刻发（600–950 行，环自由，standalone RC=0 + 标准三可独立验收）；
  W1–W5 按波滚动，单笔 ≤450 行。落库瞬间对锥/union **+0**；W5 装配才解锁子树。
- **另立一项**（scout 建议，**未批**，等用户单独裁决）：「岛去 Assembly 化」
  —— 岛 74/75 经 `TameList1:37 import Kepler.Assembly` 传递成环，它是 `jcajydu`
  与全部 A9 接口从"建好"到"接电"的总闸，但属高风险重构。

**拍板 2（用户选「一并走 SF」）：`regular_spherical_polygon_area_asnFnhk` 的 `k` 因子一并修**。

- `PackingAuto22.lean:2712` 陈述右端为 `2 * Real.pi - 2 * k * asnFnhkP22 h k 1 1 1 1`，
  HOL `counting_spheres.hl:946` **无 `k` 因子** ⇒ 陈述比 HOL 强且真化后为**假命题**。
- 与 `_797` 真化（DEF-FIX）**同批处理但分两笔**：SF 修陈述（先），DEF-FIX 改定义体（后）。
  两者同文件不同行，但 `auto_gate.sh` 的 diff-vs-patch 比对要求树面只含本笔改动 ⇒ **必须串行落库**。

## 2026-11-06 — mnt11 设常驻车道（用户指令）

**拍板**（用户，2026-11-06）：「好，之后一直保留一个 lane 做 mnt11 吧」。

1. **常驻编制**：车道池 5 个名额中**永久保留 1 个**给 `main_nonlinear_terminal_v11` 工作，
   代号 `mnt11-rolling`。它按波滚动，不因单波收工而释放；其余 4 个名额照常轮转。
2. **为什么值得常驻**（实测，当前 HEAD `424b8ff7`）：
   - mnt11 = 109 条 `mainEstimate_*`（LA1:2139 `∀ id ∈ ids, get_main_nonlinear id`），
     **语句层已完成、零 `:= True` 桩**，长度 `rfl` 钉死 109；
   - 证明层 **19–20/109 有证**，但全在 `Kepler/T11Glue.lean`（814 行、零真 sorry、
     **零 importer、无 olean、不在宇宙/锥**）——典型的"建好没接电梯"；
   - 余 ~89 条无证明路径，是 hNL 第三合取的主债；`nliMainNonlinearTerminalV11 := sorry`（Assembly 分量 3/6）；
   - 它同时是四条 registry `_concl` 的 HOL 前提（`VASYYAU.hl:292/720/1126/2366`），
     所以 ④ SF 落地后 mnt11 的消费面只会变大。
3. **车道宪法（长期约束，每波继承）**：
   - **证明写在新文件**（`Kepler/T11Proofs.lean`，或 `T11Glue.lean` 追加），
     **不改 LocalAuto1 的 109 条陈述**——避免与 SF 通道及其他车道在同一文件上交替打补丁。
   - 每件验收 `#print axioms` = 标准三；不许 `axiom`/`sorry`/`admit`/`native_decide`/改陈述。
   - 账本随波更新：109 条逐条状态（已证 / 可证待做 / 需证书 / 需新数学）落
     `docs/archive/lane-archives/mnt11-rolling/TRIAGE.tsv`，只增不改。
   - 证书农场仍属**本机禁重型计算**：凡判"需证书"的不施工，只登记。
4. **首波（M0）范围**：109 条全量分诊 + 建 `T11Glue` 的 olean（23 shard 重建完成后可行）
   + 判定 20 条已证件的接线价值（接线不闭合 mnt11，故只判不做，除非顺带零成本）。

## 2026-11-06 — 四项接口/陈述裁决（用户「你的建议都同意」）

**拍板**（用户，2026-11-06，在四项展开说明后全盘采纳编排者建议）：

1. **`_797` / `arclength22` / `packIneqDefAP22` → 真化（选项 A，DEF-FIX）**。
   `arclength22 := 0`（PA22:13927）使 `PACK_INEQ_DEF_A_797` 可反驳（`v = −v0` 时
   LHS `1.3206 > 0 = RHS`）；`packIneqDefAP22`/`Assembly.PackIneqDefA` 是 `:= True` 桩。
   修法：移植 HOL `arclength2`（`YSSKQOY.hl:297`）+ `arcV↔arclength` 桥，
   `PackIneqDefA` 改成三条具名不等式（`UKBRPFE`/`WAZLDCD`/`BIEFJHU`）的真合取
   （与 `LpIneqs` 的 `AllCertified` 同型）。**代价**：hNL 分量诚实 +1；
   `XULJEPR` 由此有希望转标准三。走 DEF-FIX 通道。
2. **四条 registry 陈述 → 补 `mnt11` 前提（选项 A，SF 通道）**。
   对象：`VASYYAU`/`PWEIWBZ`/`WKZZEEH`/`YEBWJNG` 的 `_concl`。HOL 证明需要
   `main_nonlinear_terminal_v11`，Lean 陈述省了它 → 陈述比规格强且不可证；
   LA25 的 `_p25` 又由这些 sorry 定义 → 循环。加前提 = **恢复保真度**，
   不是弱化。连带改 LA25 re-export 与 `LocalConcl` 绑定。
3. **`jcajydu` G1 → 先移植 `Reduction5`（选项 B）**。HOL `JCAJYDU` 是
   "列表级命题 ⇒ hypermap 级结论"的归约；Lean 只写了结论半，列表级命题
   （`Reduction5.restricted_hypermaps_are_planegraphs_thm`）全仓只有注释。
   **不加前提**（那会把未证假设塞进 e2e 信任链），先证列表级命题
   （估 1,500–3,000 行），`jcajydu` 本体随后降到 300–800 行。
   下一步 = `reduction5-scout` 摸边界。
4. **`HFNXPZA`/`EQTTNZI1`/`EQTTNZI2`/`EFLYGAU`/`BJTDWPS` → 销账（选项 A）**。
   五件是上游语料的**陈述级欠债**：只有 `appendix.hl:710/1110/1115/1500/1506`
   的 `let X_concl = \`...\`` 绑定，无证明文件、名字全语料不再出现、消费的
   `restriction_typ*_v39` 零外部消费者（`LocalConcl` 2026-09-21 RULING IV）。
   动作：标 `CORPUS-UNPROVED`，从"待施工"清单移除，保留 sorry 不再当债追；
   LA 的 A 类根口径 29 → 24。零消费者，对锥无影响。

## 2026-11-06 — LA21/LA18 终端锚点重编码（R-fix；用户裁决）

**拍板**（用户，2026-11-06，在 `la21-general482-recon-w1` 的证据呈报后选 **R-fix**）：

1. **问题**：`LocalAuto21.lean:140` 的
   `def mainNonlinearTerminalV11_p21 : Prop := ∀ y : Fin 6 → ℝ, (2 ≤ y 0 ∧ … ∧ y 4 = 2 ∧ y 5 = 2)`
   **可反驳**——取 `y ≡ 0` 与 `2 ≤ y 0` 矛盾；探针 `not_p21_anchor` 已用标准三证出
   `¬ mainNonlinearTerminalV11_p21`。HOL `local/terminal.hl:37` 的
   `main_nonlinear_terminal_v11` 是 **109 条不等式的合取**，不是「∀ y 都落在盒子里」。
   `LocalAuto18.lean:206` 的 `mainNonlinearTerminalV11_p18` 同病（30 处引用）。
2. **修法**：把两个锚点改成 `main_nonlinear_terminal_v11`（`LocalAuto1.lean:2139`，
   109 合取的忠实渲染）的**定义别名**；盒谓词 `MainNonlinearTerminalV11_p21/p18`
   保留（作为普通谓词，不再当锚点）。走 **DEF-FIX 通道**（章程
   `docs/def-fix-charters/p21-anchor/`），闸模式 `GATE_MODE=DEF-FIX`。
3. **影响**：`LocalConcl.p21_anchor := sorry` 从此代表**真银行债**而非假命题；
   LA21 全链（`general_482` / `CUXVZOZ_p21` / `CJBDXXN_p21`）的陈述恢复真值，
   其 864 行证明工作重新有意义。
4. **拒绝的选项**：R-freeze（冻结 LA21 链）与 R-ex（承认空真、5 行 `ex falso` 闭合）——
   后者会得到无数学内容的真命题，并让 `p21_anchor` 变成「已证矛盾」，污染信任审计。
5. **验收**：DEF-FIX GATE-PASS（各文件）；受影响文件依赖序全绿（LA18/19/21 →
   LocalConcl）；`#print mainNonlinearTerminalV11_p21` 显示别名；零新增 sorry。
6. **回退**：单 commit `git revert`。

## 2026-11-06 — tame-correspondence 三波程序获批（用户「好」）

**拍板**（用户，2026-11-06，在 `jcajydu` / `tameCorrespondenceIso` 工作量评估后）：
把 hTC 剩下的两件**合成一个三波程序**，不各开独立车道。

1. **W1 — P6-C 桥 + `RXOKSKC` 移植**：目标 `IsHypermapOfList L (hypermapOfList L)`
   （`TameLp` 侧构造已存在，`Assembly.lean:2231` 在用；缺的是 Assembly 层桥），
   外加 HOL `RXOKSKC.hl`（1,105 行）的列表/唯一性机器。产出**新模块**，不动 Assembly。
2. **W2 — `jcajydu`**：HOL `JCAJYDU.hl` 本体 99 行（单证明，把列表版结论提升到任意
   hypermap，核心一步 `INTRO_TAC Rxokskc.RXOKSKC`），消费 W1 产物。
3. **W3 — `tameCorrespondenceIso`**：HOL `WMLNYMD.hl` 1,515 行 / 40+ 引理
   （`tame9a/10/11a/11b/12o` 的图谓词↔列表谓词对应、`finalGraph_except`、
   `facesAt2_list`、长度/过滤/三角四边形分类簿记）。

**理由（实测，非估计）**：两件的真实闭包 ≈ 2,000–4,500 行 HOL，而不是 `tame/` 整章的
91,841 行 / 4.6MB——`jcajydu` 本体只有 99 行，`WMLNYMD` 才是主体；两件共享同一座
graph↔list↔hypermap 桥；`asfutbf`（`hypermap_of_fan_neg`）与 `elllnyz` 早已收口。

**验收**：每波 `#print axioms` = 标准三；W2/W3 落库后 `Assembly.jcajydu` /
`tameCorrespondenceIso` 的 sorry 消失，`textCapstone` 公理面相应收窄。

**排期**：队列 2-γ，排在 2-α（`fcdjdot` 柱③）与 2-β（`general_482` 侦察）之后，
不占当前池。

**风险/止损**：W1 若发现 `TameLp.hypermapOfList` 与 `Assembly.IsHypermapOfList` 语义有
偏差，可能触发 SF/DEF-FIX 裁决——届时停手报告，不自行改陈述。

## 2026-11-05 — SF-99 定义层根修执行（用户批准方案 (a)）

**拍板**（用户，2026-11-05 早，听取 SF-99 展开说明后答「按你建议执行吧」）：

1. **对象**：`Deformation`（`LocalAuto1.lean:129`）与独立复制体 `deformation_p2`
   （`LocalAuto2.lean:300`）由 `Set.Icc a b` 改为 `Set.Ioo a b`，对齐 HOL
   `real_interval (a,b)`（`localization.hl:128-131`，开区间 ⇒ `a < 0 < b`）。
2. **通道**：`GATE_MODE=DEF-FIX`（2026-09-29「planar 编码定义纠正」立项的闸模式）；
   章程 `docs/def-fix-charters/sf99/`（README + 5 个逐文件围栏），用户批准后逐字应用。
3. **范围**：5 声明/12 行；零陈述改动；`zlz_azim_p14` 一行转调已证的
   `w9_zlz_azim_strict`（own-sorry −1）；LA37 两件 + 6 份 Prop 孪生零改动恢复真值。
4. **验收**：5×DEF-FIX GATE-PASS；14 模块依赖序 + Text 七根全绿；Assembly 岛协议
   根公理面 628 行/37,969B/sha `97fba420…` 逐字节不变；落库 `fe6ec9c2`。
5. **回退**：单 commit `git revert fe6ec9c2`；无数据迁移。
6. **遗留**：LA37 MHAEYJN 证明缺口（G1/G3/G4）另立项；`_hpin/_haff/h4` 的 `Icc`
   （更强假设）单独立项。

## 2026-11-03 — 树增长物化程序 A/B/C 获批；Hypermap / LA35 提到队首（用户「同意」+「hypermap 和 la35 优先级提到 pending queue 最前面」）

**拍板**（用户，2026-11-03 深夜，在 orphan-scout 量尺结论呈报后）：

1. **获批**：A = Hypermap 物化（1,299 孤儿，侦察先行）；B = LA35（741）+ CertTM（618，先核 SF-42 TM demo 健全性）物化；C = 孤儿岛接入（Text.LP 205 + Text.TameSpine 75 + 8 个零 import 消费者单文件，~+300）。
2. **提级**：补位首发序 = hypermap-mat-scout → la35-mat-scout → CertTM 侦察 → 孤儿岛接入（queue §2 头注 + §2-13..16）。
3. **未批**：D = 机械证书层解冻（Interval.Cases 13,293 + LP 证书 ~952 在 universe 外）——仍待用户解冻令，编排者不单方面动。
4. **量级口径**（orphan-scout，`docs/archive/scouts/orphan-scout.md`）：现有根集合内可测上行 ≤ 1,214（接线）+ 5,644（影子上界）；>13K 增长只能来自新根物化与证书层解冻。接线波（S1 `localconcl-wiring-w1`）预期 SORRIED 可视化上升，K_AXIOM 624 为护栏。

## 2026-11-03 — lane 选题原则改为「最快增大 e2e tree」；T0 接口物化记录（用户「同意」）

**拍板**（用户，2026-11-03 晚，问「如果安排 lane 的原则是最快增大 e2e tree，该做什么」并对编排者方案「同意」）：

1. **选题原则**：批 3 起按「预期新节点 ÷ agent 时」选槽。机制依据：`:= sorry` 声明体就是
   sorryAx、只贡献 1 个节点，其潜在依赖子树完全不在锥内；填证/接线才解锁子树。
2. **杠杆排序**（编排者提、用户认可）：① 整文件孤儿接线（PA19 模式，单文件 1–2k+ 节点）
   > ② 多根差额接线（union − e2e ≈ +1,200，含 2 个笔误根）> ③ 大影子源填证 > ④ 陈述物化
   扫描（T0 模式，~+100–200/条，零证明风险）> ⑤ 证书层粘合（解冻后的鲸：554 分片链不在
   当前 2.094M universe 内）。
3. **量尺先行**：`orphan-scout` 测量车道随批 2 发车（孤儿直方图 / 每源影子子树 / 批 3 榜单）。
   **纪律**：接线边必须标注数学依据（concl-变体↔正本、接口↔实现、capstone↔装配），
   禁止为刷 K_REACH 造边。
4. **T0 接口物化记录**（批 1 工单内批准，2026-11-03 落库 `a522078c`）：e2e 接口
   `Kepler.Text.main_nonlinear_terminal_v11` 从 `def … : Prop := sorry`（任意 Prop）物化为
   `∀ id ∈ mainNonlinearTerminalV11Ids_t11, get_main_nonlinear id`（109 条具名
   `mainEstimate_*` 的查表合取，与 HOL `terminal.hl` 同构）。name/type 冻结；e2e sorry 源
   −1；109 条子债从"1 个黑盒"变为树内可数可派工的陈述节点；证书 glue（T1）留待解冻。
   v1 因 `IneqClosureDefs` 与 `PackingAuto22` 的 `sqrt3` 跨根撞名被 4b 闸打回，v2 以 11 个
   ICD 定义本地化实现零新 import。
5. **批 2 池 4/3**：批 2 三车道 + 量尺（纯读零冲突），超出原上限 3 的事由在此记录。

**影响**：M0 对表以「基线 C」为当前基线（K_REACH 2,078,505 / SORRIED 123，`a522078c`）；
`docs/e2e-reachability-map.md` v2.3 节 + TSV 已重生。

## 2026-11-03 — 方向切换：以「树越大越好」为主指标；PackingConcl 进 e2e（用户「都同意。执行吧」）

**拍板**（用户，2026-11-03 下午）：

1. **主指标改为真实可达图**：不再追求 e2e `SORRIED` 单调下降；以 **K-REACH / COVERAGE / ORPHANS / SHIMS**
   为主，`K-SORRIED` 为信息项（不设单调目标），`K-AXIOM` 为护栏。根集合 = e2e 根 + 各装配出口
   （PackingConcl / LocalConcl 的 `*_discharged`）+ 各章 capstone；“树”只认 proof-term 可达，不认 import 闭包。
2. **PackingConcl 进 e2e**：Stage 1 = PackingConcl 新增 `rdwkarcConcl_pc`（F1 重推件移植）+ 修假
   `RDWKARC_concl_discharged`（原 `:= RDWKARC`，而 PA19 `RDWKARC` 是 sorry）+ 新 capstone
   `PACKING_CHAPTER_MAIN_CONCLUSION_discharged` + Assembly import/一行 rewire；Stage 2 = used-interface
   全量接线 + 假 discharge 清理 + 多根覆盖。
3. **批准 `REWIRE` 闸模式**：`auto_gate.sh` 新增 `GATE_MODE=REWIRE`（`RW_ALLOW` allowlist + `RW_DONOR`
   + 禁删声明头/签名），用于“陈述冻结的证明项换 donor”。F1 kit 回归测试 PASS；空 allowlist 负测试 PASS。
4. **未落库工件入库归档**：`docs/archive/lane-archives/<lane>/` 放 `kit.diff` + `DELIVERY.md` + `Evidence.md`
   （Work.lean 不入库，可由 kit + HEAD 重建）。
5. **build 覆盖**：零 importer 装配文件（PackingConcl 等）加入周期性 typecheck，防止静默腐烂。
6. **批 1 三槽**：`packingconcl-c1-stage1` / `map-metrics-v2` / `tower-b4`。

**影响**：Stage 1 预计 e2e `SORRIED` 123 → 129（+6），属真实债显形，不作为失败；验收改看
K-REACH/COVERAGE/SHIMS/ORPHANS + axiom 护栏。F1 不再单独落库，其 kit 作为 Stage 1 的供体。

## 2026-11-03 — 本机禁重型计算：hNL/mnt/rest 证书农场全面暂停；冻结期不启动任何 sub-agent（用户「本机还是暂时不允许跑重型计算，所以 mnt / rest 这些都暂时不跑。现在先不要启动任何 sub agents，等我们讨论清楚确认再启动」）

**拍板**（用户，2026-11-03 上午，在编排者给出 hNL/mnt 核时估算之后——mnt 109 全链 ≈1,600–7,700 核时、本机 50 片/h 内存限并发、
rest 55 更重 1.5–5×）：
1. **本机暂不允许重型计算** ⟹ 非线性不等式证书农场（mnt11 T0–T3、nli rest 55、tsk 8、cell3 5、PA25 real_model 26）
   **全面暂停**，含 T0（4717061266 粘合首例——其闸的 `lake build` 会触发 554 分片构建，同属重型）。重启条件 = 用户解除本机限制，
   或提供独立机/云机（核时账见 queue 续 248 前后的估算：mnt 本机 3–4 周连续 / 云 64 核 256 GB 4–5 天）。
2. **冻结期不启动任何 sub-agent**：池 0/3 持位；下一批车道由编排者提案、**用户逐批确认后**才发。既有「上限 3」政策不变；
   原 bodyclosed / pm12 两程序槽的归属问题因农场暂停而失效——冻结解除后三槽默认全归 LA 侧（scsgeneric 程序 + 机动），
   以用户对首批提案的确认为准。
3. 编排者自身的非重型工作不受限：文档/账本、SF 立案与 STATEMENT-FIX 闸（LA 文件秒级编译）、stale 注记清理等可照常，
   但不发 sub-agent。

**补记（2026-11-03 中午）**：编排者提案下一批三槽（`scsgeneric-w5cC2` LA31 收尾 / `scsgeneric-w5cB3` LA37 SUB_LUNAR 分段 / `f1-upfzbzm-rewire` PA25-PA2 M0 −1），用户「不反对」= **已批**；用户换 session，新 session 开工即发（规格见 handoff #35 (d)）。SF-97 与轻量注记清理亦经「不反对」执行完毕。

**影响**：M0 在冻结期的现实下降来源只剩 F1 UPFZBZM 重接线（−1，纯 Lean，已批未做）；scsgeneric 四塔 → RRCWNSJ → 5T1/LA33
装配可继续推进但 e2e 计数不动（债收敛到 farm 根 CUXVZOZ / P_BBQUESTION / ear_acute，均在暂停的农场内）。

## 2026-11-02 — 车道池上限逐步降为 3（用户「以后我们 agent 数量逐渐降到三个。bodyclosed 至少留一个，la35/pa12 至少留一个」）

**拍板**（用户，2026-11-02 傍晚，紧接 18:02 的 5 小时 API quota 中断事件之后）：并发 sub-agent 车道上限从 5
（当日午后曾临时放宽到 6）**逐步降到 3**。组成约束：**bodyclosed 程序 ≥ 1 条**（CLOSED_SY_cs / W6–W7 收口链），
**LA35/pm12 程序 ≥ 1 条**（pmPlaneCrowding_p35 根闭合 → stack → 落 LA35 → 闸 → e2e −1；「pa12」按上下文读作 pm12），
第三槽机动（scsgeneric 巨人族 / LA 零头 / 其它）。

**编排者执行口径**：
- 「逐步」= 不打断在飞车道；完成一条不补一条，直到池 ≤ 3；此后严格 3/3。
- 补槽优先序：先满足两条组成约束，再用机动槽；机动槽按 priority-queue 既定阶段计划（bodyClosed 主攻 > pm12 收官 > scsgeneric 预装配 > LA 零头）。
- pm12 程序全部落地（LA35 own-sorry 0、地图 −1）后，「LA35/pm12 ≥ 1」约束自然失效——届时编排者在报告中标明并请用户指定该槽新归属；在得到指示前该槽按机动槽处理。
- 发车当刻的池状态记入 priority-queue §8 对应条目（「在飞 n/3」）。

**背景**：当日 18:02 五条并发车道中三条（pm12-feedfree-w2 / scsgeneric-w2b / scsgeneric-w3）触发「5 小时使用上限」被中断，
18:06 以原上下文 SendMessage 恢复；两条 bodyclosed 车道未受影响。降并发同时降低 quota 触顶与整文件编译互相拖慢（feedfree-w1
与 k5tree 并发时整文件轮 22–28 min/轮）的风险。

## 2026-11-02 — SF 常态化自主授权（用户「都批。以后 sf 你觉得合理的，都批准，不用事事问我」）

**拍板**（用户，2026-11-02 清晨）：① SF-80（LA24 k=3 体集 builder 行索引正本形，§80）与
SF-89b（LA23 `bodyClosed_p23` 前提升级为全 `stableSystem_p23` 载体，§93）当场批准；
② **此后 statement-fix 提案由编排者按合理性自主裁决并应用，不再逐项呈批**。

**编排者自设护栏**（2026-09-28 STATEMENT-FIX 机制不变，只改审批人）：
- **自动批准范围**：分级 A/B，且 (a) HOL 正本逐字引用在册 + 前提可满足性机检（SF-92 附录
  配方，python witness 级以上）在册 + 消费者普查在册 + 归档 patch 由真实 diff 生成；应用仍走
  `GATE_MODE=STATEMENT-FIX` 闸（patch 逐行多重集一致）。
- **仍呈批**：分级 C/E；无 HOL 锚或 HOL 本身存疑；触及 def 层编码（DEF-FIX 模式）且消费者
  > 10 处；任何「陈述弱化到可能丢失 HOL 结论强度」的方向；以及编排者自己拿不准的。
- 每次自批在 `docs/statement-fix-proposals.md` 该项 (f) 状态注明「编排者依 2026-11-02
  常态化授权批」，并在 queue §8 记账；用户可随时撤回本授权。

## 2026-10-13 — Phase 4 求解策略路由表批准（用户"按建议全部批准"）

- **原问题形式废止**："TM vs BBTreeGD 二选一"经 W1/W1b/W2 三波受控实验修正为
  **按表达式族路由的混合策略**（详见 docs/archive/projects/phase4-routing-decision.md）。
  实证：TM 多项式族碾压（TADIAMB 251k 叶 100%@101.2s）与 sqrt 族结构性无力
  （TEWNSCJ closed=0 非正底 100%）并存；BBTreeGD 广覆盖骨干（BIX 92.9%）与
  锐边界 438× 叶膨胀并存——二选一必有一半错。
- **路由表**：R1 多项式/有理→TM 主攻；R2 ite/guard→BB 域切分+ite-hull2+TM 临界带
  （BIX 实证混合管线）；R3 sqrt/log→第三武器（radicand 零等值面预切分/t=√u 换元，
  QZECFIC 探针证切负底半域后 TM 即闭合）；R4 非严格/角点→手证路线（B V2 先例）；
  残叶归 G4 数据波。Lean 侧 CertTM/BBTreeD 双内核均在树，路由表零新基建。
- **已批准执行项**：①第三武器 R&D 立项（Phase4 常驻车道 W4-W5，formal_ineqs
  考古先行，验收锚=TEWNSCJ/QZECFIC 对照组闭合）；②92 prep 族成分画像车道
  （812 记录按表达式族分类，半天脚本）；③强机器日 runbook 引用本路由表分批灌装。
- **对既有决策的关系**：不改变"证书化计算/native_decide 禁用"信任模型
  （第三武器的证书仍是 Lean 内核可回放的 interval/TM 数据）；2026-08-09 的
  "非线性：dReal 优先，Arb 球算术兜底"为旧机时代求解器选型，本文的 TM/BBTreeGD
  是其证书发射层策略细化，不冲突。

## 2026-10-09 — SF 31 批准（用户"31 批，方案 a1"）

- **项 31**（PA23 `grutoti_sum_volD` 前提面不足——冻结陈述可反驳，M）：方案
  (a1) 签名扩至 region_data 门族逐字 + `0 < r ∧ d < 1` + 四条显式测度前提
  （可测性/两两零测/体积有限/覆盖恒等式），主体变 `FINITE_EDGE_X2` +
  `p23_measure_setSum_biUnion` 两件纯装配；GRUTOTI capstone 调用点同车重接线
  （陈述不动），测度债打包进新债务桥私件 `p23_grutoti_sum_volD_measure_facts`
  （NEEDS 定点：hcov=TIWWFYQ 族/hpair=AJRIPQN 实例/hmeas+hvol=可证支）。
  执行版补丁 `docs/statement-fix-proposals-patches/31-pa23-sum-volD.patch`。
  背景：冻结版仅 `he : e = {u0,u1}` 一条前提，`V := ∅` 即机器验证反例
  （docs/assets/grutoti/）。

## 2026-10-01 — SF 28/29/30 三连批准（用户"同意。按你的想法来吧。"）

- **项 28**（PA23 `grutoti_cell_vol` 缺窄性前提，A′）：签名补窄性前提或沿
  `grutoti_region` witness 重述，随 SF28+29+cell_vol 波应用；
- **项 29**（PA23 `grutoti_cell_vol` ε-junk 角，A′）：签名加
  `truncateSimplex 1 (cellParams V X).2 = [u0, u1]` 型前提封角，同车；
- **项 30**（PA22 bisector 家族 holArg 同缺陷，M）：与 SF22/27 同车改述
  `holArg`，随 bisector refill 波应用（注意 holArg 对 Complex.arg 无单调性，
  仅单射——refill 推理不得用"arg 序⟹holArg 序"）。
- 状态翻转台账于同日补录（周休眠打断所致迟账）。

## 2026-09-29 — "planar 编码定义纠正"单独立项（用户拍板：同意）

**背景**：提案官两轮裁决实证 PA22 的 `facetOfC`（弱化为"真面"）与 `polyhedronC`
（对 flyspeck polyhedron H-表示的误移植，注释声称"每点属于面"）系**定义级误移植**
（HOL `facet_of` = polytope1.ml:1506：face_of ∧ ≠∅ ∧ aff_dim 条件）——14 枚
planar-kit 填证在陈述冻结下合法但**空洞化**；提案 12（affine_facet_hyper，C 级）
与 13a（pad2d3d_facet，C 级）冻结待本立项。wave3 另发现同族：`cone0P22 := affGe`
（应为严格 affGt）使 CONE0_FCHANGED 家族 5 枚假化。

**授权范围**：
1. 定义纠正 = `facetOfC`/`polyhedronC`/`cone0P22` 三个 def 对齐 HOL 语义
   （含 ℂ 上 affDim 支撑件如需）；
2. 闸门豁免形态 = STATEMENT-FIX 模式的定义扩展（DEF-FIX）：同样**只许逐字应用
   已批准补丁**（SF_PATCH 机制复用），提案官出定义补丁草案 → 用户审定 → 修复波
   应用；
3. 波及面先清点后动手：14 枚 planar-kit 空洞化填证的重填清单 + 12/13a 解冻 +
   CONE0 族 5 枚假陈述修复，全部在该项目内闭环；
4. 执行顺序：(a) 定义补丁草案 + 波及面清单 + 重填路线（侦察轮，只读）→
   (b) 用户审定补丁 → (c) 应用 + 重填波。

## 2026-09-28 — STATEMENT-FIX 闸门模式批准 + 陈述修复波授权

**拍板**（用户）：新增 `auto_gate.sh` STATEMENT-FIX 模式（c5d9f7cc）——陈述修改
唯一合法形态 = **逐字应用已批准的补丁草案**。机制：`GATE_MODE=STATEMENT-FIX` +
`SF_PATCH`（`docs/statement-fix-proposals-patches/` 存档补丁）+ `SF_ITEM`
（提案项号）；闸门校验 ①工作区 diff 与补丁逐行多重集一致（上下文漂移不敏感、
内容严格）②提案项含 (a) HOL 出处 ③规则③④⑤照常（⑤要求修复后定理无 sorryAx）。

**修复波执行序**（提案官 10 项裁决 + 增补，见 `docs/statement-fix-proposals.md`）：
项 7 `RELATIVE_INTERIOR_AFFINE_FACE`（复核无病，免豁免原位填证，第 1 顺位）→
项 1 `SUM_INTER`（A 级，加 `A.Finite` 前提，补丁 01 已存档）→
项 13 `DUUNHOR_concl`（编排者同意补前提：HOL Rogers.hl:1682 证明第一步即消费
packing，PA6:837"前提未用"注记不实；修复波先尝试无前提版反例，反例成立或按
保真对齐原则补 `Packing V ∧ saturated V` 并同步 PA6:841 背引用加参）→
B 类 7 枚等 def 落地后按各项 (d) 节路线闭合。PA22 r2 新增 4 疑似假
（facet_rep_uniq/affine_facet_hyper/ARG_ORDER/pad2d3d_facet）待提案官立项后
同流程处理；其 `polyhedronC` 定义误移植问题（14 枚空洞化填证的根源）一并立项评估。

## 2026-09-28 — 硬件迁移：旧服务器报废 + 工人通道换 ZCode sub agent + 重型计算挂起

**事件**：旧生产服务器（128 核 / 503G RAM）于 2026-09-28 确认硬件报废，磁盘不可恢复。
仓库本体零损失（git 全量，origin GitHub，cron 自动 push 保持至 2026-09-26 HEAD
`a5b5aba8`）；**仅存本机外部存储的产物随盘丢失**：

- `cert549_tight.json`（549 全量重演输入，212,798 叶 tight 证书，原在 /tmp）
- LP 43,078 持久化产物 + 账本（~/lprun-persist、~/lprun-logs）
- bb_arb 重跑证书 35 份（~/bb-cert-rerun/certs）
- 549/257 内核构建分片源 + olean（kepler-g4e 工作树，6,321 + 12,553 shard）
- 全量 `.lake` 构建缓存（Phase 2 分片 ~7 天重建成本归零重来）

以上全部可由 git 内工具链重生成；重算在新硬件基线下重估，**不因换机降低验收标准**。

**新硬件基线与算力政策**：Apple M3 Pro（12 核 6P+6E / 36GB / 磁盘余 183GB）。
运行预算上限：kernel decide ≤2 路、native_decide ≤4 路、stage-A ≤8 路、lake `-J 6`。
**重型批处理挂起待强机器**：549 全量重演主体（single+straddle）、LP 43,078 持久化
重跑、145 证书批量重跑、Phase 2 CertShards 全量重建、92 prep 家族重解。
期间主力 = Phase 5 填证 + 轻量 Lean 任务（单文件编译级）+ 小时级单进程 C。

**工人通道变更**：Phase 5 填证与卫星任务的 LLM 工人从 opencode CLI（deepseek 等
外部通道）改为 **ZCode Agent sub agents**。`auto_pipeline.sh` 五道机械闸与
`auto_gate.sh` 验收流程不变（闸与工人实现本就解耦）；HANDOFF 中 opencode 特有
经验（auth.json、external_directory、配额重置等）转为历史记录。

**政策强化（数据丢失教训）**：证书/大产物"仅活在本机外部存储"不再可接受。今后
批次产物落盘即登记 `certificates/README.md`（该表自项目启动起仍为空，即此教训）
并同步第二份外部存储（私有仓/release/协作强机器），哈希清单与本体分离存储的旧
做法补充"本体必须有异机副本"。

**审批状态**：已执行（2026-09-28 用户在会话中确认换机并批准新工作模式：
"只跑非重型计算任务……主要用 sub agents 干活"）。

## 2026-09-25 — native_decide scoped exception 扩展至 `Kepler.Interval.Cases.C549*`（549 加速项目）

> **状态：已批准（2026-09-26，用户拍板"允许 native decide"）。** native_decide
> 允许范围在 2026-08-10 与 2026-09-19 两条（`Kepler.Graphs.Cert*` +
> `Kepler.Assembly.GoodListShard*`）之上，新增 `Kepler.Interval.Cases.C549*`，
> 形态与审计要求按下文执行（50 叶合取 = 1 axiom/shard、逐 shard `#print axioms`
> 台账、sorryAx/Classical.choice 出现即 fail）。量产 native 发射自本批准起开闸。

**变更（拟议）**：在上述两条范围之上，另允许 `native_decide` 出现在
`Kepler.Interval.Cases.C549*`（5490182221 案例的 hull/HullD2/mono 折叠/
ArcBatch 等证书 shard 模块及其汇总定理）。用途：549 全量 212,798 叶证书的
内核验证提速——kernel `decide` 21.4 s/叶 → `native_decide` ~3.5 s/叶
（6.1×，C549HullSpeed 实测）；全量口径 **529 → 109 core·h**（mono 折叠 +
cert 瘦身 + rung-128 + 曲率紧致化组合口径）。

**公理形态（推荐：50 叶/shard 一次 native = 1 axiom/shard）**：

- 推荐发射形态：每 shard 对"50 叶合取"整体做**一次** `native_decide`，
  逐叶定理用 `.1`/`.2` 投影导出——每 shard 恰 **1** 条 scoped axiom
  `<shard>._native.native_decide.ax_1_1 : decide P = true`。
- **已有实测证据**（构建捕获）：`C549Hull200Shard_speed depends on axioms:
  [propext, Quot.sound, C549Hull200Shard_speed._native.native_decide.ax_1_1]`
  （`C549HullSpeed.lean` 文件头 FOLLOW-UP 记录）。
- 形态与 2026-08-10 / 2026-09-19 两批**逐字同形**：本工具链（v4.32.2）的
  公理足迹 = 每定理一条作用域公理（`Lean.Meta.nativeEqTrue`，
  Lean.Meta/Native.lean:31-33）；`#print axioms` = propext + Quot.sound +
  N 条 scoped axiom，无 sorryAx、无 Classical.choice。
- 对照：逐叶 native 形态（同文件叶 2..50）为 49 axiom/50 叶 shard，全量
  ~2×10⁵ 条；合取形态把公理面压 ~50×。合取形态另有共享求值收益（
  `C549Hull200Expr` 单 AST 一次求值 vs 逐叶内核重复展开），十五更外推
  全量可再降至 **~11 core·h**（逼近 M5 ≤ 10 core·h；以全量重演实测为准）。

**影响面（axiom 面数字）**：549 全量 **~10,600 shard → ~10,600 条 scoped
axioms**（1 条/shard；确切 shard 数以全量重演实际发射为准，straddle 修复后
叶数或再降）。相对现存两批总量（2026-08-10 批 ~624 + 2026-09-19 批 23 =
~647 条）约 **16×**。TCB 增量类别不变：Lean 编译器+运行时进 TCB，与
2026-08-10 条同一性质，无新信任基类别。

**审计要求**：

- 每 shard 模块尾部固定 `#print axioms <shard 汇总定理>`（既有惯例，同
  `C549HullSpeed.lean` 与 CertTM 曲率轮 :1683-1688 print 块），并入
  `lean/scripts/AxiomAudit.lean` 台账（逐 shard 行或每族代表行 + 计数台账，
  批准时定案）；
- 审计口径：propext + Quot.sound + N 条 `..._native.native_decide.ax_1_1`；
  出现 sorryAx / Classical.choice / 任何非预期公理即 fail；
- native axiom 计数随轮次入 `docs/archive/handoffs/549-lane-log.md` 阶段位置节（可度量、
  可对账）。

**结构配套**：发射器默认产 50 叶合取 shard（模块叶数上限沿用管线缺口单的
stage-A shard 化参数 ≤20-50）；`make check` 纪律与双回归（裸路径逐字节）
照旧；549 全量重演（十六更第 1 项）先行，量产 native 发射在本条获批后
开闸。

**风险**：

1. TCB：信任边界 = Lean 编译器+运行时正确性；被决策命题 `decide P = true`
   本身内核可读，撤销后 kernel `decide` 可独立重验任一 shard。
2. 公理面规模：~10,600 条使 `#print axioms` 输出与审计台账线性膨胀
   （~16× 现存）；以 shard 汇总定理为审计单位控制输出体积。
3. 形态漂移：549 全量重演未完成，shard 尺寸/合取结构可能调整；形态微调
   不需新条目，但 axiom 面数字须随轮次在 lane log 更新。
4. 双路径一致性：native 与 kernel decide 消费同一命题，不存在两套判据；
   唯一风险源是编译器误编译——与既有两批同型。

**撤销路径**：发射器单旗标切回 kernel `decide` 重发（正确性零影响，成本
退回 529 core·h 口径），或整体回退本条范围（CI/lint 恢复零命中拦截）。
任何一次审计出现非预期公理 = 即时撤销 + 全量排查，无需另行决议。

**审批状态**：[DRAFT 待批准]。批准后在本节追加批准日期与批准人，并将标题
的 [DRAFT 待批准] 改记为已决。

## 2026-09-19 — P6-C：native_decide scoped exception 扩展至 `Kepler.Assembly.GoodList*`

**变更**：2026-08-10 条"native_decide 只允许出现在 `Kepler.Graphs.Cert*`"
扩展为——另允许出现在 `Kepler.Assembly.GoodListShard*`（archive 逐图
`good_list` 量产分片，23 片覆盖全部 19715 图：Tri 9 / Quad 1253 /
Pent 16080 / Hex 2373）。用途：闭合装配脊柱第 4 个接口占位
`Kepler.Assembly.goodListArchive : AllGoodList tameArchiveLists`
（HOL `Good_list_archive.good_list_archive`）。

**信任基影响**：与 2026-08-10 条完全相同——Lean 编译器+运行时进 TCB。
本工具链（v4.32.2）`native_decide` 的公理足迹为每定理一条作用域公理
`<thm>._native.native_decide.ax_1_1 : decide P = true`
（`Lean.Meta.nativeEqTrue`，Lean.Meta/Native.lean:31-33），与既有
`Kepler.Graphs.Cert*` 分片的足迹逐字一致；`#print axioms goodListArchive`
= propext + Quot.sound + 23 条 native_decide 公理，无 sorryAx、无
Classical.choice。组合器 `Kepler/Assembly/GoodListAll.lean` 为纯内核
（`List.take_append_drop`/`List.all_append` 链），不做任何计算。

**结构配套**：`GoodList`/`listOfDarts`/`tameArchiveLists` 等纯列表机器
从 `Assembly.lean` §1a/§1c 下沉至 `Kepler/Assembly/GoodListDefs.lean`
（本脊柱改为 import 之，对外签名不变），分片因而不必 import 装配脊柱，
接口 sorry 不进入分片公理审计。生成器 `lean/scripts/gen_goodlist_shards.py`
（slice=1000），runner `lean/scripts/run_goodlist_shards.sh`（幂等，
状态文件 `p6c_goodlist.status`）。

## 2026-09-17 — main 分支允许携带 sorry 债务（原"main 零 sorry"纪律放宽）

**变更**：原纪律"main 上除 `Statement.lean` sanctioned 占位外零 sorry"
（2026-09-13 已放宽为"在制骨架 sorry 可短暂存在"）正式修订为——
**main 允许携带 sorry 债务，债务以 `DEBT.md`（由 `lean/scripts/debt_ledger.py`
生成）为唯一权威刻度**。wip/auto-packing（packing 25 模块 + local 39 模块，
64 模块骨架）已合入 main（`aad4fb35`）。**已向人类汇报并获批准**
（2026-09-17 会话，用户原话："我考虑去掉 main 不能有 sorry 这个限制"）。

**理由**：

- packing/local 骨架（64 模块、~3000 定理陈述）长期养在 wip 分支上，
  合入代价随时间单调上升（跨模块撞名、接口漂移）；
- 终验标准不变、只是推迟：主定理证明本体零 sorry 可达 + 公理仅标准三
  （+ Phase 2 限定 native_decide）仍是项目终点验收条件；
- Lean 编译器即判官：sorry 无法冒充证明，`#print axioms` 里的 `sorryAx`
  永远可见；债务账本使"慢慢填"成为可度量的烧账过程而非口头承诺。

**配套约束**：

- 陈述保真审查成为唯一质量阀门：sorry 定理的**陈述**（尤其装配脊柱接口与
  各章 capstone）必须过 `docs/statement-fidelity.md` 审查，不得随本政策放宽；
- 每批次闭合后刷新 DEBT.md；新增未经授权的 sorry 会在 diff 中现形；
- G4 生成的巨型案例证书文件（百万行级）暂缓合 main，按波次验收后分批合入。


## 2026-08-10 — 修订"禁用 native_decide"：枚举完备性计算改为限定范围 native_decide

**变更**：PLAN.md §2 的"`native_decide` 禁用"修订为——**仅** tame 图枚举的
完备性计算（`next_tame` 工作列表闭包 + 终图同构比对的 Bool 求值）允许
`native_decide`；其余一切（全部数学证明、Archive 数据、checker 正确性定理、
主定理组装）维持内核检验不变。**已向人类汇报并获批准**（2026-08-10 会话）。

**理由**（实测数据）：

- 全枚举树规模（AFP `ArchStat.thy` 官方 `count` 注释，Python 复算 Tri 逐位吻合）：
  Tri 312,764 / Quad 134,291,356 / Pent 1,401,437,009 / Hex 334,466,383，
  合计 ~18.7 亿次扩展；AFP 用编译代码 `by eval` 需 11 小时。
- 实测 Lean 内核 `decide` 重放：~5-13 s/节点（Pent 规模；瓶颈
  `generatePolygonTame` 的候选过滤，比 Python 慢 ~2000×，系内核 whnf
  本质速度，预期优化空间 10-50×，不够）。全树内核重放 ≈ 10⁶ 核时 +
  TB 级证书数据——差 4-5 个数量级，不可行。
- 枚举完备性不存在非对称证书：验证"没有漏图" = 重新枚举，逐节点证书
  只改变并行度不改变总内核工作量。
- 同构意义上的去重（worklist 模同构）在数学上对本枚举器**不成立**
  （`minimalFace` 平局打破依赖面列表顺序，非同构不变），故无法借此
  缩小闭包集。AFP 的 trie worklist 也只对收集集去重、照样全树扩展。
- 信任基影响：`#print axioms tame_classification` 将多出
  `Lean.ofReduceBool`（Lean 编译器+运行时进 TCB），与 AFP `eval`、
  HOL Light Flyspeck 的信任基持平，仍远优于 1998 年不可信代码。
- 缓解：Tri 种子（312k 节点，内核重放 ≈ 26 核时）另行做**纯内核
  `decide`** 版本，与 native 路径交叉校验同一套 checker 代码语义。

**范围控制**：`native_decide` 只允许出现在 `Kepler.Graphs.Cert*`
（枚举闭包分片定理）中；CI/lint 检查其余文件零命中。

## 2026-08-09 — Phase 2 启动：两个工具链决定

1. **求解器版本锁定方式：pinned 源码包 + sha256，而非 nix/docker**（对 PLAN.md §3
   建议的偏离，在此记录）。理由：本机无 nix；docker 对 plantri 这类单文件 C
   程序是过度工程；源码包（plantri55.tar.gz，sha256 记入 `reference/LOCK.md`）
   已满足可复现性。若后续求解器（SoPlex/dReal）依赖复杂，再评估 docker 并另行记录。
2. **Phase 2 蓝本从 flyspeck 仓库内的 `formal_graph/isabelle_tame` 换成 AFP 条目
   Flyspeck-Tame**。理由：AFP 版是维护中的完整版本（含 `Invariants.thy`、
   `TameEnumProps.thy` 等剪枝正确性证明，flyspeck 仓库副本缺这些 Props 理论）；
   两者共有文件内容一致（Archive 四个 .ML 逐字节相同）。不构成对 §2
   锁定决策的变更（"参考 Nipkow–Bauer 的 Isabelle 工作"不变，只是取更全的副本）。
3. **Phase 2 证书策略微调**：枚举函数已移植为 Lean 可执行定义，因此完备性靠
   移植剪枝正确性定理（Invariants/GeneratorProps/TameEnumProps）+ 逐图可达性
   证书在内核重放，而非导出整棵搜索树。与 PLAN.md §4 Phase 2 的精神一致
   （"枚举树 + 剪枝依据作为完备性证书"），但载体从"数据"变为"逐图见证 +
   一次性数学证明"。详见 `docs/architecture.md` Phase 2 节。

## 2026-08-09 — 初始化：确认 PLAN.md §2 全部锁定决策

- 证明助手：Lean 4 + Mathlib。toolchain 锁定 `leanprover/lean4:v4.32.2`（elan），
  Mathlib 锁定 tag `v4.32.2`（见 `lean/lean-toolchain` 与 `lean/lakefile.toml`）。
- 计算信任模型：证书化计算；`native_decide` 项目内禁用。
- 证明蓝图：Hales《Dense Sphere Packings》(Cambridge, 2012)。
- 图枚举：plantri/nauty 生成 + 完备性证书 + Lean checker。
- LP：SoPlex exact / QSopt_ex 有理精确求解 + VIPR 证书；HiGHS 仅交叉验证。
- 非线性：dReal 优先，Arb 球算术分支定界兜底。
- 硬件：本机（128 核 / 1 TB RAM）。
- 参考库只读克隆于 `reference/`，commit hash 记入 `reference/LOCK.md`。
