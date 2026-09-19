# 交接文档（Handoff）— 2026-09-10

> 面向接手者（人类或 agent）。本文件描述项目现状、验证纪律、环境细节、
> 待办与优先级。一页进度看板见 `STATUS.md`（每日刷新），长期设计决策见
> `DECISIONS.md`，阶段计划见 `PLAN.md`，模块对照见 `docs/module-map.md`。

## 0. 一句话现状

main @ `48ff904`（`make check` 全绿，唯一 sorry = `Statement.lean`
sanctioned 主定理占位）。**Phase 2/3 已闭合；Phase 4 求解层 160/176（91%），
内核闭合（G4）未开工；Phase 5：hypermap/fan/topology/planarity 100% 进 main**
——其中 planarity 收官所依赖的**体积/测度论层已从零建成**
（`Kepler/Geom/{Volume,SectorArea,WedgeVolume,LuneVolume,SolidAngle}.lean`，
含 HOL Light `VOLUME_BALL_WEDGE`/`HAS_MEASURE_LUNE`/`VOLUME_SOLID_TRIANGLE`，
零 sorry）。下一步 Conforming.hl，流水线 `scripts/auto_pipeline_conforming.sh`
已在 wip/auto-phase5 跑（commits to wip only；待 `DWFBRQY` 等依赖 solid_of 的
定理补齐后可合 main）。

## 1. 项目目标（不变）

Lean 4 + Mathlib（toolchain `leanprover/lean4:v4.32.2`）形式化开普勒猜想：

```
开普勒猜想（密度 ≤ π/√18）
  └── Phase 5 文字证明：堆积 → fan → hypermap → 归约为"tame 图得分 < 12"
        ├── Phase 2：tame 平面图分类（19,715 张）✅
        ├── Phase 3：每图 LP 上界（43,078 个终端 LP）✅
        └── Phase 4：176 条非线性不等式（支撑 LP 松弛与局部估计）🟡 91%
```

## 2. 各 Phase 状态

### Phase 2 — 图枚举 ✅ 闭合

- 19,715 张 tame 图全量枚举 + 内核验证（585 个 CertShards 分片）；
  公理 = 标准三公理 + 601 个限定范围 native_decide，零 sorryAx。
- **绝对不要** `rm -rf lean/.lake`：分片全量重建需 ~7 天。

### Phase 3 — LP ✅ 闭合（2026-09-07）

- 43,078/43,078 终端 LP 内核验证通过（SoPlex 精确模式 + 51 例
  glpsol --exact 对偶通道兜底）。账本 `~/lprun-logs/results.jsonl`。
- 链路细节与 SoPlex 用法（`-X/-Y` 有理输出才可信）见 `pipeline/lp/README.md`。

### Phase 4 — 非线性不等式 🟡 求解层 91% / 内核闭合 0%

- 流水线：ineq.hl 181 记录 → AST 176 → case JSON（y 空间 176 +
  prep 空间 745）→ bb_arb（C/FLINT 分支定界，二进制 /tmp/bb_arb_verify，
  编译命令在 `pipeline/interval/README.md`）。
- **2026-09-09 家族级对账**：176 条 = 68 y 空间闭合 + 92 prep 家族
  闭合（prep = Flyspeck 官方 x=y² 归一化，745/745 全闭合）+
  **16 条真残余**（清单 `pipeline/interval/out/residue16.txt`：
  TSKAJXY 系 4、TEWNSCJ/PEMKWKU/TXQTPVC/IXPOTPA、QZECFIC wt0 ×2、
  GRKIBMP B V2 等）。
- 待办：16 条逐条定策略（GRKIBMP B V2 有真反例叶=尖锐边界组，需 ε 余量
  或弱编码）；然后 **G4：BBTree 证书 → Lean 内核闭合**（bb_arb 已能出
  cert JSON；Lean 侧需扩 IExpr abs 节点 / TKind ln / Cert 叶带 guard
  符号+disj 备选——规格 `pipeline/interval/arb-layer.md` §3/§4）。

### Phase 5 — 文字证明 🟡 planarity 99%，流水线已 FAIL-STOP（等压轴攻坚）

- 已收官：hypermap.hl 13,575 行 100%、fan.hl 系列 ~7,800 行 100%、
  topology.hl 4,718 行 100%。
- **planarity.hl（15,463 行）**：main 覆盖至 :15280（98.8%，批次 1-15 全部
  自动闭合，~150 枚定理）。**批次 16（收官批）FAIL-STOP**：剩 2 枚在 wip
  `PlanarityAuto16.lean` 带 sorry：
  1. `solid_of_dartset_leads_into_fan_triangle_fan`（:15370）——卡在前置
     `VOLUME_SOLID_TRIANGLE` 未移植。**它不在 planarity.hl，在 HOL Light 本体
     `Multivariate/flyspeck.ml:5883`**（measure(ball∩aff_gt) = Girard 盈余·r³/3；
     测度论证明链长）；`sol`/`dihV`/`AZIM_DIVH` 也未移植（骨架 docstring 内有
     sol 的 Classical.epsilon 规格编码方案和所有已就绪引理的 file:line）。
  2. `MOZNWEH`（:15443，全书主定理）——纯 MESON 组装，solid_of 闭合后秒过。
  攻坚路线：专项移植 VOLUME_SOLID_TRIANGLE 链（独立文件，原文需从
  flyspeck.ml 粘进 prompt——工人读不了仓库外路径）→ 补 solid_of → MOZNWEH →
  批次 16 审计进 main。**流水线目前处于停止状态**，清堵后删除
  `PlanarityAuto16.lean` 的 2 个 sorry 并 ff 合 main，整个 planarity.hl 即收官。
- 后续队列：Conforming.hl 17,033 → polyhedron ~3,200 → packing/ ~28,000 →
  local/ ~30,000 → assembly（auto_pipeline 改 HL 变量即可复用）。
- **全自动流水线**（`lean/scripts/auto_pipeline.sh`，2026-09-10 上线）：
  1. 从 `lean/scripts/auto_pipeline_state.txt` 读当前位置（起始行+批次号）；
  2. deepseek 设计骨架（陈述冻结，docstring 嵌 HOL 原文+证法+候选引理）；
  3. `auto_loop.sh` 逐定理派 deepseek 填空，**机械闸五道**（单文件 diff /
     签名冻结=删除行只能是 sorry / 禁词扫描 / lake build 绿 / 公理白名单），
     过闸自动 commit；单定理 3 次失败跳过、连续 3 跳闸熔断；
  4. 批次审计（全量 build + 冻结核验 + 全定理公理）→ ff main + push；
  5. 推进状态文件，下一批。FAIL-STOP 即停等人类。
- **Kimi 的残余职责**：每 4h 汇报 + STATUS.md + 陈述保真抽查 +
  处理 FAIL-STOP/NEEDS-HUMAN。
- 工人模板与历史教训：`docs/phase5-worker-template.md`。

## 3. 验证纪律（红线）

1. **main 零 sorry**（唯一例外 `Statement.lean:111`）；wip 分支允许骨架
   sorry，但 wip 只有在"所有被 import 的文件均无 sorry"时才合入 main。
2. `native_decide` 只允许 `Kepler/Graphs.Cert*`（601 个限定信任公理）。
3. 内核无法归约 Rat 算术——checker 检查层用 Int/dyadic，语义层 cast 桥接。
4. 合 main 前：`lake build Kepler` 全绿 + 签名冻结核验 + 公理白名单。
5. 不信任任何生成器/求解器，信任基 = Lean 内核 + 项目内 checker。

## 4. 环境备忘（本机）

- 128 核 / 503G RAM / 磁盘 98G（紧）。tmpfs 在 `/dev/shm`（252G，
  重启即失）；`/tmp` 不是 tmpfs。
- Lean 命令前 `export PATH="$HOME/.elan/bin:$PATH"`；项目在 `lean/`。
- 参考库浅克隆在 `/dev/shm/kepler-ref/`，symlink 回 `reference/`；
  重启后重克隆约半分钟（命令见 git 历史或 `reference/LOCK.md`）。
  **关键参考已入库**：`lean/scripts/planarity.hl`。
- LLM 通道（`~/.local/share/opencode/auth.json`）：
  `deepseek/deepseek-v4-flash`（付费，现任主力，~1-2 分钟/定理），
  `opencode/big-pickle`（免费，前主力），
  `zhipuai-coding-plan/glm-5.3`（订阅，设计/兜底），`glm-5.3-flash`（备胎）。
  调用：`cd lean && timeout 5400 opencode run -m <model> "<prompt>"`。
- git 身份 Zhang Zhuo <mycinbrin@gmail.com>（仓库级已设）。
- 双 3090 GPU 是别人生产容器，**绝不碰**。

## 5. 当前运行中的东西

- **auto_pipeline.sh 已 FAIL-STOP（2026-09-11，批次 16 剩 2 枚，见 §2 Phase 5）**。
  清堵后重启：`cd lean && nohup bash scripts/auto_pipeline.sh >> /tmp/auto_pipeline_driver.log 2>&1 &`
  （但需先把状态文件指到收官之后或手工收尾批次 16）。
- 日志：`/tmp/auto_pipeline.log` / `/tmp/auto_loop.log` / `/tmp/auto_gate.log`；
  状态 `lean/scripts/auto_pipeline_state.txt`。
- Kimi 侧巡检 cron：每 4h 汇报+抽查（会话内，换会话即失效需重建）。

## 6. 待办队列（优先级序）

1. ~~**Phase 5 planarity 收官攻坚**~~ ✅ **已完成（2026-09-11，main `48ff904`）**：
   体积层从零建成（`Volume/SectorArea/WedgeVolume/LuneVolume/SolidAngle`），
   `solid_of`+`MOZNWEH` 已证，planarity.hl 100% 进 main。
2. **Conforming.hl 移植（进行中，wip/auto-phase5）**：定义层
   `Kepler/Text/ConformingDefs.lean` 已就位；流水线
   `scripts/auto_pipeline_conforming.sh` 已跑批次 1-2。**关键更新**：原 blocked 的
   `DWFBRQY`（Conforming.hl:550）依赖的 `solid_of` 现已可证——应把
   `auto_pipeline_conforming.sh` 的 `BLOCKED` 清空（或从 wip 里已跳过的
   `DWFBRQY`/`nonconformin_fan_imp_n_fan_ge0` 重新派工），跑通后即可把
   Conforming 合 main。Conforming 228 定理中仅极少数依赖立体角公式，其余为
   `sol` 代数/测度/径向（`sol_spec` 即可）。
3. Phase 4：16 条残余策略 + G4 内核闭合（见 §2 Phase 4）。
4. Phase 6：主定理装配 + 终验。
5. 零散：`Kepler.Text.fan80/fan81` 重复定义去重；`ineqdata3q1h.hl` 解析。

### 体积层文件（2026-09-11，全部零 sorry、仅标准三公理）

`Kepler/Geom/` 下（均 import 进 `Kepler.lean`）：
- `Volume.lean`：`radialNorm`、`EventuallyRadial`、`sol`、`sol_spec`、
  `volume_real_add_left/right`、`volume_real_smul`、`radialNorm.volume_scaling`。
- `SectorArea.lean`：`sector_area`（2D 扇形面积 = ρ²θ/2）。
- `WedgeVolume.lean`：`volume_ball_wedge`（HOL `VOLUME_BALL_WEDGE`）。
- `LuneVolume.lean`：`arcV`/`dihV`、`azim_dihv_same`、`wedge_eq_affGt`
  （`WEDGE_LUNE_GT`）、`volume_ball_affGt(_simple)`（`HAS_MEASURE_LUNE(_SIMPLE)`）。
- `SolidAngle.lean`：`volume_solid_triangle`（HOL `VOLUME_SOLID_TRIANGLE`）。
HOL 源在仓库内：`lean/scripts/flyspeck_multivariate.ml`（供后续 Volume/Packing
章节引用）。

### 体积层新文件（2026-09-11）

`Kepler/Geom/Volume.lean`（已 import 进 `Kepler.lean`，`lake build Kepler` 绿）：
- `radialNorm r x C`（HOL `radial_norm`）
- `EventuallyRadial x C`（HOL `eventually_radial`）
- `sol x C`（HOL `sol`，`Classical.choose` 选择见证半径）
- `volume_real_add_left/right`、`volume_real_smul`（实值体积的平移/标度）
- `radialNorm.volume_scaling`（HOL `lemma_r_r'`）
- `sol_radius_independent`、`sol_spec`（HOL `sol_spec`）
公理审计：仅 `[propext, Classical.choice, Quot.sound]`，零 sorry。

## 7. 已知坑（近期新增；历史坑见 git 历史与 worker 模板）

- **闸的三个已修 bug**（教训：GATE-FAIL 先怀疑闸）：git diff 路径要
  `--relative`；公理全名=命名空间.定理名（非模块名）；`#print axioms`
  长输出会折行，匹配前先 `tr '\n' ' '`，另有 "does not depend on any
  axioms" 合法情形。
- 改动正在运行的 bash 脚本会被 bash 按字节偏移续读——先停再改。
- `pkill -f 'opencode run'` 会自匹配杀自己——用 `pkill -f '[o]pencode run'`。
- nohup 包装壳的 pid ≠ 真循环 pid，用 `pgrep -f 'auto_l[o]op.sh'` 取。
- 验收构建必须自然退出：掐死时 error 未 flush，grep 0 是假绿。
- 整条命令链末尾加 `&` 会把整条链后台化，前台输出全丢——分两条命令。
- 工人（opencode）读不了仓库外路径（external_directory auto-reject
  会杀会话）：HOL 原文一律粘贴进 prompt 或放仓库内。
- 标量-标量乘在 ascription 里写 `*` 不写 `•`（isDefEq 死循环）。

## 8. 快速自检（接手后第一件事）

```sh
cd /home/scroll/repos/kepler-conjecture-lean4
export PATH="$HOME/.elan/bin:$PATH"
git log --oneline -3 main
make check                      # build + 公理审计，应全绿
tail -20 /tmp/auto_pipeline.log # 流水线状态（若在跑）
```

## 2026-09-12 里程碑：Conforming.hl 全书收官（main @ d77c13f）
- **fan/Conforming.hl（17,033 行）23 批 ~230 枚定理全部闭合，零 sorry、标准公理，已合入 main**（`make check` 绿）。批次 1-18 由 opencode-CLI 流水线完成；批次 19-23（含巨证 `lemma_connect_hypermap`，HOL 证明 ~1900 行）由主 agent 直接以 Task sub-agent 完成——CLI 派发方式已废弃（ARG_MAX 128KiB 上限 + 无必要）。
- **新架构**：主 agent 编排（派 worker / 跑 `auto_gate.sh` 验收 / git / state），sub-agent 干活；多批次用 `git worktree` 分道（lane-bNN 分支 + `cp -al` 硬链接 `.lake`）并行，完成后 merge 回 wip 再合 main。
- **两阶段攻坚法**（难定理标配）：先派"规划者"出可执行证明计划（目标分解+have 链+辅助引理清单+读取预算），再派"执行者"照计划落地——TXFBALB、`conforming_diagonal_fanadd1`、`lemma_connect_hypermap` 均如此拿下。
- **教训**：W2 曾冻结出假辅助命题（单面 vs 相邻双面，正四面体反例），被 W3 用反例挡下，W4 重述为交叉式（下侧∈face(w,v)、上侧∈face(v,w)，由 azim 符号决定）后闭合。假命题审查是流程的一部分。
- **state**：`scripts/auto_pipeline_conforming_state.txt = DONE 23`。下一目标：`polyhedron.hl`（~3.2k 行，依赖 Conforming 已就绪）→ packing → local → assembly。

## 2026-09-14 里程碑：polyhedron.hl 全书收官（main @ c425db2）
- **fan/polyhedron.hl（3,200 行，71 条定理）全部闭合，零 sorry，已合 main**（`make check` 绿）。附带新基层 `Kepler/Text/Polytope.lean`（~2,500 行：Brøndsted 开线段 FaceOf/FacetOf/edgeOf/edges/polyhedron/polytope 定义 + FACE/FACET_OF_POLYHEDRON_EXPLICIT + RELATIVE_INTERIOR_OF_POLYHEDRON + FINITE_POLYHEDRON_EXTREME_POINTS + COLLINEAR_FACES + AFF_GE_SING_CONVEX_HULL_ALT + exposed/segment kit）。G4 轨道同期闭合 logI 全链（log2D/lnI_sound/TKind.lnK，已进 main）。
- **多文件并行架构（成熟）**：7 条 `git worktree` lane（kepler-p1..p7，`.lake` 用 `cp -al` 硬链接共享）+ 主 agent 中央编排。教训三条：① lane 收割后**立即** `reset --hard` 同步，否则 lane 重置会抹掉未提交成果（PolyAuto2 FAN7 被抹 3 次）；② 硬链接 .lake 的 trace 会互相污染——「phantom error/幻影绿」都源于此，判定编译状态必须 `rm <module>.{olean,ilean,trace}` 后重来；③ 巨证拆解到「一个 worker 一个引理」粒度（flvns_p1..p5 + 组装）比整段交付成功率高得多。
- **编码纪律**：FaceOf 必须 OPEN 线段（Brøndsted）；闭线段编码退化（非空⇒f=s）曾诱发 6 枚「爆炸式空洞证明」，已全部诚实重做。自动提交的 cron 刷新**不得**搬动 PolyAuto*/工作文件到 main（曾与 wip 合并产生 add/add 冲突）。
- **下一目标**：`packing/`（~28k 行，Rogers/OXLZLEZ3/REUHADY…）→ `local/`（~30k 行）→ assembly。Polytope 基层与测度/体积层可直接复用。

## 2026-09-18 LocalAuto35/36 证明完成波次（单 lane 工人）

- **LocalAuto35（QKNVMLB）**：36 → 22 sorry（+14 证明）。已闭合：SCS_K_PRIME_CASE_4/5/6（CASE_DIAGONAL_MOD 残差演算，interval_cases+omega）、SCS_K_PRIME_LE_GE、W_EW_K_SCS_ADD_P（k'≡q 残差链）、SCS_J_DIAG_EQ、SCS_J_PRIME_SUBSET_SCS_J、INTER_SLICE_SCS_EMPTY1/EMPTY、CARD_V_EQ_SCS_K（range_periodic_image_p23+VV_INJ）、DIST_DIAG_LE_CSTAB（ear-flag→bm-override=cstab）、SCS_SLICE_SYM、IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_PRIME_3（LA4 NONPARALLEL_BALL_ANNULUS）、DIAG_NOT_IN_EDGES（hd2+injectivity，纯残差）。新增 import：LocalAuto4/23。
- **LocalAuto36（XWITCCN）**：48 → 46（+2 定义-shim）：wedgeInFanGt_p36:=wedgeInFanGt_p3、slicev_p36:=slicev_p8（LA2 不可导入的替代渲染；merge 时去重）。另新增 import LocalAuto3/8。
- **⚠️ 主树编译被跨 lane 重复名阻断**：SphereKit.lean（9-17 BODY-FIX）新增公开 `Kepler.Text.deltaX4/deltaX5`，与 LocalAuto1:766/776 的旧副本在 import-合并层冲突——任何同时 import Polytope 闭包（经 PlanarityAuto16→PA20→SphereKit）与 LA1 的文件都会触发 `environment already contains 'Kepler.Text.deltaX5'`。修复 = LocalAuto1 删除这两份旧副本（SphereKit 版为 canonical）。LA1 自身单独编译 0 error；沙盒（/tmp/opencode/sbox，LA1 副本已 private 化）内两文件 0 error。轮询脚本 /tmp/opencode/probe_status.log 持续监测。
- **LA36 陈述层疑点（merge 前需裁定，未动陈述）**：① TAUSTAR_EQ_TAU_STAR_4/5/6/4_3/5_sqrt8/4_sqrt8/5_pro_cs 的 `hs1 : s1 = scsToStableSy_p23 s` 把记录 d 槽定为 0，而 HOL 源携带 `scs_d_v39 s`（dTame 4=0.206 等），与 dsv_v39=s.d 项相差 0.206——陈述疑假，需 s1.d:=s.d 或改写；② IN_NOT_EMPTY_CASE_3（k=3）误用含 CONDITION2 的 B_SY1_p4，HOL 的 k=3 body 无 CONDITION2（应采 LA24 的 CONDITION2-free body）。
- 已填 16 枚全部沙盒 0-error 验证；剩余 sorry 的诚实 NEEDS 注记未动。

- **LocalAuto12/14/17 填充波（本轮，沙盒 0-error 验证 /tmp/opencode/lakesnap）**：
  - **LocalAuto12（YXIONXL）**：12 → 1 sorry（+11 证明）。全链 prop_equ 不变性闭合：PROP_EQU_IS_SCS/TRANS_BBINDEX_ID/PROP_EQU_IS_SCS-ncard（残差双射 y↦(y+k−i%k)%k + Set.InjOn.ncard_congr）、PRO_EQU_IS_EAR（3-cycle J-singleton + PRO_EQU_ID1 逆推；新增私件 PRO_EQU_IS_EAR_FWD/J_shift3/propEqu_comp_eq）、PRO_EQU_DSV_EQ（setSum 重索引 setSum_image_bij）、PRO_EQU_TAUSTAR_EQ（k≤3 tau3 循环对称；k>3 直接用 TRANS_V/E/FF range-等式改写——HOL 的 SUM_AZIM_EQ_ANGLE_LE4 绕路不必要）、TRANS_SCS_BBPRIME/PROP_EQU_EQ_BBPRIME/TRANS_IMAGE_BBINDEX_EQ/TRANS_BBINDEX_MIN_EQ/TRANS_BBPRIME2_SUBSET/TRANS_MMS_SUBSET/YXIONXL3。新增 kit：periodic2_shift_pair/dist_shift_pair/psi_key/mod_pair_roundtrip/mod_pair_cancel(')/setSum_image_bij。仅剩 sgtrnaf_p12 锚（ blockade：unadorned_MMs_p27/UXCKFPE2 仍 sorry，LA27 lane）。
  - **LocalAuto17（EYYPQDW+YRTAFYH+deformation）**：13 → 11 sorry（+2：EYYPQDW_SCALAR_POS_p17（cross3 线性 kit+lagrange+field_simp）、lemma_1_p17（AFF_GE_1_1_0 + scale-invariance，含 x'=0 情形））。新增 `_p17` fill-kit：cross3_smul/add/sub/self/anticomm/X_smul、dot smul/add/comm 桥（后续 NORMV3/NORM_V3_V1/EYYPQDW_p17/lemma_2 的下一波基础）。
  - **LocalAuto14（ZLZTHIC）**：39 → 39（未动；azim 连续性/cycle 序/deformation kit 的命名 blocker 均未落地，维持 NEEDS）。
  - **⚠️ 主树仍被 deltaX4/deltaX5 双份阻断**（SphereKit-canonical vs LocalAuto1 旧副本；LA1.olean 17:17 仍未重建）——LA12/17 已在沙盒 0-error，主树修复（LA1 删两份旧副本）后即可合入。沙盒：/tmp/opencode/lakesnap。

## 2026-09-19 LocalAuto4/15/36 填充波（单 lane 工人）

- **LocalAuto36（XWITCCN）**：46 → 34 sorry（+12）。闭合：8× `SCS_*_IS_TRI_STABLE`
  （新增私件：csAdj/aPro 值表三分支 disjunction、`constraintSystem_succ_empty_p36`
  /`stableSystem_csAdj_succ_p36`/`triStable_csAdj_succ_p36`/`stableSystem_aPro_succ_p36`
  通用构造器——复用文件内已证的 `torsor_succ_mod_p36`；h0=1.26/cstab=3.01 全部数值化）、
  `IN_NOT_EMPTY_B1_SY_3`、`NOT_COLLINEAR_BBs_CASE_3` + `IN_B_SY1_COLLINEAR_CASE_3`
  （新私件：annulus 点对 + 表距 2..2h0 ⇒ 与 0 不共线；`bFlat3_p36`/`rowSy_bFlat3_p36`
  flatten↔行往返；`tau3_cycle_p36` shim，LA12 同名私件不可导入）、`TAUSTAR_EQ_TAU_STAR_3`
  （dTame 3 = 0 + dsv J-empty）。**阻塞澄清（写入 NEEDS 注记）**：① k≥4 的
  `TAUSTAR_EQ_TAU_STAR_*`（7）按现陈述不可证——`scsToStableSy_p23` 的 d 槽 =0 而
  taustarV39 扣 dTame k≠0（HANDOFF ① 的具体化；修法 s1.d := dTame k，本轮未动陈述）；
  ② k≥4 的 `IN_NOT_EMPTY_CASE/B1_SY`（14）需要**fan 定义桥**：registry `ConvexLocalFan`
  （sigmaFan/ee/wedgeGe）↔ `convexLocalFan_p4`（azimCycle_p4/EE_p4/wedgeGe_p4）——
  树内无此桥（Fan.lean 无 azimCycle）；③ `IN_NOT_EMPTY_CASE_3` 陈述疑假（HANDOFF ②，
  k=3 的 B_SY1 体含 CONDITION2 但 BBsV39 的 fan 合取支在 k=3 取左空枝）；
  ④ `XWITCCN_CASE_*` 仍压在 ①+HDPLYGY 极小元之下。0 error，34 sorry。
- **LocalAuto4（dih2k）**：46 → 40 sorry（+6）。闭合 Section-F 机械层：
  `DART_FAN_SY`/`DART_FAN_SY1`（hyp_p4 FAN 枝 = hypermapOfFan，darts coe =
  dart1OfFan——沿用 ConformingAuto14 的 change/coe_toFinset 模式）、`EQ_EDGE_E_SY`/
  `EQ_EDGE_E_SY1`（pair-set + finNext≠i）、`SET_OF_EDGE_CARD_EQ2`（setOfEdge
  邻居二枝枚举，纯 E_SY 组合）、`F_SY_INTER_IMAGE_NN_EMPTY`（finNext² = i ⇒
  m ∣ 2 矛盾；私件 `finNext_ne_self_p4`、`hyp_darts_eq_p4`、`mem_dart1_of_fan_p4`）。
  剩 40：5 ball-annulus 仿射引理（AFF_GT_1_2 等显式形在 Planarity.lean——**未导入**
  以免扩大 LA15/LA36 闭包；NEEDS 注记已写）+ 35 枚 azim-cycle/hypermap 巨证
  （需 fan 级 azimCycle↔sigmaFan 桥，树内无）。0 error。
- **LocalAuto15（VPWSHTO）**：12 → 12（未动）。逐项 grep 复核：MAX_COPLANAR_4POINT、
  SUM_4ANGLE、EQ_DIAGONAL_MIN、TWO_DIAGONAL_AT_MOST(1)、MAX_IF_COPLANAR(1)、
  VPWSHTO1/200/2、VPWSHTO、POINTS_IN_BALL_ANNULUS 在全树均无已证孪生/阻塞
  （「contract registry」结论维持）；纯代数项已在上波闭合。0 error。
- 三文件联合编译 0 error（rm trace 后重验 LA4→LA15/LA36 依赖链）。

## PackingAuto21 填充波（2026-09-19）

- **PackingAuto21（TSKAJXY2/3）**：43 → 37 sorry（+6 闭合）。本轮闭合：
  `BIS_HYPERPLANE`（内积代数：PA5 `bis_mem_eq` 的超平面形；新私件 `p21_sq_eq`）、
  `RCONE_GT_SCALE`（顶点射线正齐次性）、`RCONE_GE_COS`（顶点 + `cos arcV` 区域；
  新私件 `p21_cos_arcV`：`abs_real_inner_le_norm`+`inner_eq_dot` 的 Cauchy–Schwarz 桥，
  分母退化由 `0/0=0`+dot-消失吸收）、`DIST_LAW_OF_COS_ALT`（`norm_sub_sq_real`+私件
  `p21_cos_arcV_mul`/`p21_cos_arcV_inner`，退化 junk 情形同样成立）、
  `MCELL2_INTER_BIS_LE_MEASURABLE`（`MEASURABLE_MCELL` + `bis_le` 闭半空间 Borel）、
  `RCONE_PAIR`（无坐标二次代数：bisector 半 `2A≤‖v-u‖²`、cone 半 `A≥t‖v-u‖‖x-u‖`、
  `t≤1` 平方比较闭环；新私件 `p21_smul_dotP`/`p21_sum_smul_dotP`）。0 error。
- **NEEDS 注记（未闭合，已写入文件内 NEEDS 块）**：`MCELL2_SPLIT`/`MCELL2_VOL_SPLIT`
  的真正阻塞 = 从 `¬nullSet (mcell2 V ul)` 导出 `elV ul 0 ≠ elV ul 1`（u=v ⇒ 细胞 ⊆
  `u + span{mxi-u, omega-u}` 平移真子空间 ⇒ 零测——草稿已试，`Finset.sum`-membership
  在 `ofLp`-coercion 下的 conv/rw 组合过于脆弱，本轮放弃）；`MCELL2_VOL_SPLIT` 另需
  ENNReal-级并-交可加性（`measure_union_add_inter`）+ 零测双 bisector 交
  （`BIS_HYPERPLANE` + 仿射超平面零测）。`MCELL2_SPLIT` 的 `RCONE_PAIR`-半已就绪，
  剩 affGe-半即闭合。0 error，37 sorry。
