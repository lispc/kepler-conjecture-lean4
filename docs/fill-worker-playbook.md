# 填证工人手册（Fill Worker Playbook）

> 面向 ZCode sub agent 填证工人（Phase 5 Text 章 `sorry` 清偿）。**开工必读本文**；
> 编排者任务书只给三件事：lane 文件、本轮目标、特殊提示——规则一律以本文为准。
> 维护者：主 agent。每波 launch 前更新 §5 地图，每波收工后更新 §6 教训日志。
> （历史文档 `phase5-worker-template.md` 是 opencode CLI 时代的工人模板，已退役，仅作参考。）

## 0. 开工检查单

1. 读本文全文；
2. 从任务书确认：lane 文件（你的唯一工作文件）、本轮目标、特殊提示；
3. 环境：`export PATH="$HOME/.elan/bin:$PATH"`，一切命令在 `lean/` 目录下跑；
   依赖 olean 已全部建好（Text 全链首建 ~5 分钟已由编排者完成，你无需等）；
4. 本机是 macOS：**没有 `timeout` 命令**（别用）；路径无 `/home/scroll`（旧文档已作废）。

## 1. 硬性纪律（`auto_gate.sh` 五道机械闸会机器检查，违反即废）

- **只改 lane 文件这一个 tracked 文件**；草稿/探针一律放 `/tmp`；
- **只允许删除：sorry 行（bare 或带行尾注记，如 `sorry -- NEEDS: ...`）/ 空行 /
  纯注释行**；一切结构性代码行（theorem/def/lemma/namespace/证明内容行）禁止删除，
  一切定理/定义陈述冻结（闸门第 ② 道机械检查）；
- **新增行禁词：`sorry` / `admit` / `native_decide`——连注释里都不行**；
- 新增辅助引理必须自身完全证明（不得带 sorry）；
- **绝不 `git commit`，绝不自己跑 `scripts/auto_gate.sh`**（编排者统一验收：
  `LANE_FILES` 多 lane 轮换 + stash，闸过即 commit+push）；
- 验收构建必须自然退出（中途掐死时 error 未 flush 是假绿）。

## 2. 效率纪律（每条都来自真实战报的教训，见 §6）

1. **分块读取**：先 `grep -n` 定位，只读目标 ±60 行邻域；**禁止整读 >500 行的文件**；
   已读过的内容不重复读（拿不准就记笔记）。整读大文件+重复读是 token 预算的头号黑洞。
2. **三分类先行**：动手填第一枚之前，先通览 lane 文件全部 sorry 的 NEEDS/DISCHARGES
   注记，产出分类清单：`机械可填 / 卡具名桥或外部锚（跳过）/ 疑似假陈述（记录，跳过）`。
   本轮目标 = 机械题的 ~70%，**不是编排者给的固定数**——固定数只是下限参考。
3. **查重前置**：写任何新辅助引理之前，先 grep 全树找现成同型：
   `grep -rn "<关键词>" lean/Kepler/Text/SphereKit.lean lean/Kepler/Geom/ lean/Kepler/Text/*Auto*.lean`。
   能引既有 kit 就引；本项目最痛的历史债务就是孪生定义泛滥（SphereKit 波次合并了
   80+ 个 `_pNN` twins），不要新增孪生。
4. **批量编译**：每填 3–5 枚跑一次自查（见 §3，单次 1–3 分钟）；**同一目标证明尝试
   失败 2 次就跳过**，原位 NEEDS 注记写一句卡点，下一枚。恋战是第二号时间黑洞。
5. **备份习惯**：动手前 `cp <lane文件> /tmp/orig<文件名>.lean`，弄坏了能回。
6. **学习环境**：动手前读 lane 文件 10–20 个**已证明**定理，吃透本文件的证明习惯
   （策略组合、私有引理惯例、命名风格）再下笔——照着周围代码写，成功率远高于自由发挥。
7. **收笔终查**：**最后一枚填完、最后一行改完之后**，必须再跑一次 §3 自查并确认为 0。
   "中途验过 = 终态没验"是真实翻车源（wave1 PA25：末段编辑后未终查，闸门拦下 5 个
   编译错误整单打回）。

## 3. 自查命令（收工必做）

**终验（收笔终查）必须用闸门同款构建**——`lake env lean` 会假绿（本波 PA2/PA4 lane
实测：env-lean 对 `abs_add` 等改名/模块模式可见性差异全部放行，`lake build` 全部拒绝；
grep 双格式防不住这种分歧）：

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean
lake build Kepler.Text.<你的文件模块名>        # 终验：必须自然退出且 0 error
```

中途快速迭代可以用（每 3–5 枚一次）：

```bash
lake env lean Kepler/Text/<你的文件>.lean 2>&1 | grep -cE '(^|[ :])error:'
```

⚠️ 两个已知陷阱：
- **env-lean 假绿**（见上）——它只配当迭代工具，不配当终验；
- **错误行格式随依赖 olean 新旧翻转**——`路径:行:列: error: msg` 与
  `error: 路径:行:列: msg` 两种都出现，grep 用双格式 `(^|[ :])error:`，
  不要用单一 `": error:"`（wave1 PA25 假阴性翻车案例）。
- sorry 警告（declaration uses 'sorry'）是正常的，不用管。

注意：`lake env lean` 不会自动补建依赖 olean——如果你怀疑依赖陈旧，报告里说明，
让编排者处理；自己不要跑 `lake build` 大目标。

## 4. 最终报告格式

1. **填证清单**：定理名列表（按文件内顺序，一句话证法摘要）；
2. **剩余 sorry**：填前 N → 填后 M（定理证明 sorry 与 def 桩分开计）;
3. **三分类统计**：机械未填 n / 卡桥或外部锚 n（逐枚具名）/ 疑似假陈述 n；
4. **陈述问题清单**（若发现疑似假陈述：定理名 + 反例或一句话理由）；
5. **给下一波的上下文笔记**：你在探索中发现的地图信息（哪个引理在哪、哪条路通），
   编排者会合入 §5 供后续 lane 复用——这是你最重要的遗产。

## 5. 预置地图（编排者每波更新；欢迎工人修正/补充，写进报告第 5 项）

### 5.1 跳过清单（外部锚与证书依赖，见了直接跳，不要尝试）

- `main_nonlinear_terminal_v11`（`LocalAuto1.lean:815`，sorry-typed def，等 G4/非线性章）；
  全树 grep `main_nonlinear_terminal` 找到全部消费点；
- LP registry / 证书依赖项（OWZLKVY*、EAR_*、quad_*、ineq_asym、taud_x_taum_x、
  empty_3T2 等，注记带 "+LP" 的）；
- def 桩（`_p38` 式 `def ... := sorry`——闸门禁新增 sorry，def 桩只能等外部落）；
- 已知假陈述：`SUM_INTER`（`LocalAuto38.lean:441` 附近，junk 分支有反例
  `A=univ, B={0}, f=const 1`；需加 `A.Finite` 前提才能关闭，等陈述修复波）。
- **DUUNHOR_concl（PA2:557）前提缺失疑点（侦察 lane 2026-09-28）**：比 HOL
  （Rogers.hl:1682）少 `Packing V ∧ saturated V`；HOL 证明第一步即经
  `VORONOI_CLOSED_EQ_LEMMA`（Rogers.hl:1256，带 packing）消费 packing，
  PA6:837"前提未用"注记与原文不符。补前提会破坏 PA6:841 背引用（需同步加参）。
  已入假陈述修复提案清单。
- **PA22 桩致假 8 枚（wave2，修复 = 等 def 落地或改陈述前提，均一句话反例已核）**：
  `regular_spherical_polygon_area_asnFnhk`（asnFnhkP22=0 桩）、`vol_solid_triangle_ortho`、
  `EDGE_PAIR_pr23`（eFanP22 恒等桩）、`BIJ_FACET_HYPERFACE`/`HYPERFACE_EXISTS`
  （落空 faceSet）、`RELATIVE_INTERIOR_AFFINE_FACE`（f=∅ 反例；
  **已有修复版 helper `p22_face_of_affine_rint`**：加 `f.Nonempty` 前提即可关闭）、
  `BIJ_DART_POLYEDGE`、`PACK_INEQ_DEF_A_797`（卡 arclength 落地）。

### 5.2 桥引理位置表（找工具先看这里，别全树乱摸）

| 引理/工具 | 位置 | 状态 | 备注 |
|---|---|---|---|
| `taum_dih_y` | LocalAuto16:459 | open | LA38 tau3_taum 族 6 枚的钥匙 |
| `AZIM_LE_PI_EQ_DIHV` | LocalAuto5:1788 | open | LA38 vv_quad_split 族 |
| `DIHV_EQ_DIH_Y` | 未移植 | 缺 | azim/dihV 解析桥 |
| `sum4_azim_fan` | TopologyFan | 已证可引 | LA38 扇残差族可用 |
| `wedgeInFanGe` = wedgeGe | PackingAuto2:268 | 已证可引 | ConvexLocalFan 第三合取 |
| `HL_EQ_DIST0` / `CIRCUMCENTER_2` | PA6/PA7/PA11/PA12 | 已证可引 | 公共 hl 恒等式 |
| `deltaY`/`deltaX`/`atn2`/`taum`/`solY` 等 kit | SphereKit.lean | canonical | 别再定义本地副本 |
| AzimBridge（azimCycle↔sigmaFan 主桥） | Text/AzimBridge.lean | 808 行 0 sorry | azim 族先查这里 |

### 5.3 本 toolchain 的 Mathlib 改名速查（工人训练数据多为旧名，这里是雷区清单）

| 旧名（训练数据常见） | 本 toolchain（v4.32.2/Mathlib v4.32.2）正确名 |
|---|---|
| `Basis ι R M` | `Module.Basis ι R M` |
| `Basis.span_eq` | `Module.Basis.span_eq` |
| `List.mem_nil` | `List.Mem.nil`（或改用 `List.not_mem_nil` 语义） |
| `abs_add` | `abs_add_le` |
| `neg_le_abs_self` | `neg_le_abs` |
| `div_le_div_iff(_right)`（ℝ 上） | 不可用；改 `div_eq_inv_mul` + `mul_le_mul_of_nonneg_left/right` |
| `le_or_lt` | `le_or_gt` |
| `List.take_all_of_le` / `take_eq_self_iff` | 不可见（模块模式），换 `List.take_take`/长度推理 |
| `Classical.epsilon` 消除 | `epsilon_spec (p := …)` 显式给谓词 |

（发现新的改名陷阱：写报告第 5 项，编排者入表。**改名类错误只有 `lake build` 能稳定
暴露**，env-lean 会放行旧名——见 §3。）

技巧：build 模式下 `simp only [edgeX, Set.mem_setOf_eq] at h` 会清掉假设导致
后续 Unknown identifier；拆 setOf 定义用 defeq-lambda 最稳：
`(fun hx : e ∈ edgeX V X => (hx : ∃ u v, …)) he`。

**lake build vs env-lean 可见性差异清单（PA22 wave2 实测）**：点链式 dot-notation
（`hfin.toFinset`/`hfin.mem_toFinset`）build 下不可解析，必须全限定
`Set.Finite.toFinset hfin`/`Finite.mem_toFinset hfin`（mem_toFinset 已迁根 `Finite`
命名空间且 x 为显式参）；`measure_biUnion_finset`→`MeasureTheory.measure_biUnion_finset`、
`volume`→`MeasureTheory.volume`；`Set.mem_diff`→`Set.mem_sdiff`（x 显式，
`(Set.mem_sdiff x).mp h`）；`Set.not_mem_empty`→`Set.notMem_empty`；
`Module.finrank_mono`→`Submodule.finrank_mono`（需 `[Module.Finite ℝ ↥t]` 实例）；
`div_le_iff`→`div_le_iff₀`、`one_lt_inv`→`one_lt_inv₀`；
`Set.Finite.exists_maximal_wrt` 不存在，用 `Set.Finite.sSup_mem`/`Finset.max'`。

### 5.4 各 lane 已知卡点速查（收工后追加）

- **LA38**（52 remaining @二轮后：38 tactic sorry + 14 def 桩）：二轮闭合 6 枚
  （DELTA_Y_POS_4POINTS 走 **Gram 行列式路线** `det M²≥0` 纯线性代数，Collect_geom
  移植非必需；vv_split_azim/vv_quad_split 三件套用 `sum4_azim_fan`+私件
  `p38_azim_eq_dihV`——**AZIM_LE_PI_EQ_DIHV 已不必等 LocalAuto5**，LuneVolume 的
  `azim_dihv_same`/`azim_dihv_compl` 拼合即得）。tau3_taum/taustar_taum 族 6 枚
  **只差 `DIHV_EQ_DIH_Y` 一座桥**（taum 侧恒等式已闭合：私件 `p38_taum_dih_y`/
  `p38_const1_eq`/`p38_dihY222222`=arccos(1/3) 纯算术）；其余 13 枚卡
  `main_nonlinear_terminal_v11`/LP、4 枚卡 enclosedP38 桩、3 枚卡 cayleyR 桩、
  12 枚深扇几何/外部。
  **【重大坑】`i+(k-1)` 与 `i+k-1` 符号 k 下不 defeq**，直传参数 → elaborator
  whnf 死循环（10M 心跳不够）；先 `have hik : … = … := by omega` 归一索引形再动手。
- **LA5**（123 remaining @wave2）：本轮私件 `la5_not_face_card_one`（FF 单点即矛盾的
  基数引擎）+ `la5_FF_subset_darts`/`la5_dart_mem_V` 已编译可用；解锁路径 = 基数法
  推广到 dih2k `hasOrders` 可清 `LOFA_CARD_EE_V_1` 簇；SPAN 桥 4 枚的系数提取已就位
  （`la5_conv02_extract`）、affGe 简化语义（符号条件**只约束第二个集合**）模板
  `la5_affGe2_extract`。
  **命名/战术坑（LA5 实测）**：`Function.iterate_succ_apply` 是 `f^[n+1] x = f^[n] (f x)`
  （与惯常相反，`'` 版才是 `f (f^[n] x)`，且 f 显式首参）；`Finset.mem_singleton_iff`
  不存在（用 `Finset.mem_singleton`；Set 侧才是 `Set.mem_singleton_iff`）；
  `obtain … := h` 会清除 h（先 `have hkeep := h`）；同文件禁前向引用；
  U+209D 不是合法标识符字符。
- **PA18**（71 remaining @wave2）：本轮落下**三座 azim↔affine 桥**（private，
  回灌时去 private）：`pa18_azim_zero_affGe`（azim=0 ↔ affGe，即 LA5:1312
  AZIM_EQ_0_GE_ALT2 的证明版）、`pa18_affGe_affGt_of_ncol`、
  `pa18_collinear3_line_affGe`。cc 簇最短解锁路径：**MHFTTZN3（PA6:848）可由
  MHFTTZN4+BARV_CIRCUMCENTER_EXISTS+XYOFCGX(PA7:343) 自证** → JDHAWAY_0 →
  cc_pe_exists → PA25 全通；FUZBZGI_0 链另需 PA12 VORONOI_LIST_3_SINGLETON_EXPLICIT。
  azim 工具箱全在 `Geom/AzimLemmas.lean`（azim_eq_azim_iff(_alt)/azim_compl/
  azim_frame_spec 全已证）+ `Geom/Aff.lean` 的 Affsign。
  命名坑补充：`smul_right_injective` 存在；`Set.not_mem_empty` 不存在（用 simp）；
  `direction_eq_vectorSpan` 要 `AffineSubspace.` 前缀；`convex_segment` 的 𝕜 隐式；
  `linear_combination (norm := module)` 方向敏感（用 `first |…|…` 双向）；
  归约 if 用一条 `simp only [h01, h0w.symm, …]` 而非顺序 rw。
- **效率招：/tmp 隔离迭代法**：新私理在 `lake env lean /tmp/test.lean`（import 所需
  模块、私有依赖自带副本）分钟级迭代，定稿再粘回 lane——避免大文件反复全编。
- **PA2**（52 remaining @2026-09-28 桥 lane 后）：`OAPVION1/2/3_concl` 三件套已闭合
  （Mathlib `AffineIndependent.existsUnique_dist_eq` 路线，可复用于一切
  circumcenter/radV-epsilon 类桥）；其余大多卡各章 capstone。
  `GLTVHUM_concl`(:550)/`DUUNHOR_concl`(:557) 已侦察定级 **GIANT**（NEEDS 注记在
  原位）：GLTVHUM = "Voronoi 胞 = 根在 u0 的 Rogers 单形之并"（Marchal 分解等价形，
  非 OAPVION 族），攻坚顺序 = PA6:418 FACET_OF_POLYHEDRON_EXPLICIT_BIS（先扫
  Polytope.lean）→ PA6:431 IDBEZAL（saturation 进场）→ PA6:439
  VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS（~130 行）→ PA6:487 GLTVHUM_lemma1
  （k-归纳 ~325 行）→ PA2:550 装配；DUUNHOR 另需 ROGERS_AFF_DIM_FULL(PA6:763)、
  POLYHEDRON_VORONOI_LIST(PA5:1454)、OMEGA_LIST_N_LEMMA(PA5:1502)。两桥闭合即自动
  变绿 PA6:497/838 零内容背引用。
- **PA4**（39 remaining @攻坚后，原 65）：**簇解锁路径已修正**——bump 簇真阻塞是
  `HDTFNFZ`（VX V X = V∩X，经 PA11 LEPJBDJ kit 可证，PA17 `hdtfnfz_p17` 有示范），
  **不是 AJRIPQN**：DIFF_EDGEX（MCELL_EDGE×2 + 4>3 鸽笼）与 MCELL_BUMP_0 已绕开
  AJRIPQN 闭合。AJRIPQN 真实解锁面 = cellParams 唯一性族 **9 枚**
  （MCELL_CELL_PARAMETERS_EXIST 及 MCELL{4,3,2}_CELL_PARAMETERS_EXIST/PARAM_UL、
  MCELL3_VX），其上游短缺点 = **GLTVHUM_concl（PA2:550，已侦察定级 GIANT：
  ~600 HOL 行五级链，需专门移植波，见 PA2 条，非单桥 lane）**；
  DUUNHOR_concl(PA2:557)、SLTSTLO1/2(PA13，3100 行 GIANT)、DDZUPHJ、QZKSYKG1/2
  (PA14，1900 行 GIANT) 仍未证；TIWWFYQ(PA5)、RVFXZBU(PA10) 已变真。
  另：OXLZLEZ2 cc_*_v11 案例分析巨石 ~30 枚（非本簇）。
  `MCELL4_EDGE`(:1021) 与 `MCELL_EDGE`(:1039) 在 ¬nullSet 下疑似不相容，
  陈述修复波需复核（攻坚轮复核维持此疑点）。
  可复用：`hdtfnfz_p4` kit（16 个 `_p4` 私件）、`(by simpa using (Finset.mem_filter.1 he).1)`
  桥、`Set.ncard_insert_of_notMem + Set.ncard_le_ncard` 计数安全路
  （`Finset.card_le_card` 已单参、`Set.Finite.card_le_card`/`toFinset_cong` 不存在或签名变）。
- **PA22**（73 remaining @wave2）：钥匙引理 = `TopologyFan.sum4/sum5_azim_fan`
  （azim 三点加法，PA2-15 传递可见）+ `Geom.AzimLemmas.azim_compl`（补角）——
  组合可解全部 azim 排序族。**Polytope.lean 是 PA22 最大未开发富矿**：
  `faceOf_eq_affineInter`/`faceOf_disjoint_rinterior`/`minrep_skolem`（经
  FACET_OF_POLYHEDRON_EXPLICIT 公开入口）/`affDim_hyperplane`/
  `FINITE_POLYHEDRON_FACETS/FACES`/`mem_rint_iff`，攻 planar-面 15 枚前先扫。
  桩真值表：`hypermap1OfFanxP22` 的 faceSet/darts=∅；`eFanP22`=恒等；
  `weaklySaturatedP22`/`localAnnulusInequalityP22`/`packIneqDefAP22`=True；
  `regularSphericalPolygonAreaP22` 是真公式。
  isDefEq 超时坑：V3 标量-smul 恒等式深 rw 链会 5M 心跳超时——把恒等式
  整体 `have` 出来用 `smul_smul`+`mul_div_cancel₀` 显式闭合。
- **PA25**（144 remaining）：~40 卡具名桥（PA2 OAPVION2 ✅已解除；PA18
  `cc_uh_exists`/`cc_pe_exists`；Bump 通道等 AJRIPQN；`ORDER_AZIM_SUM2Pi0`；
  `coplanar_delta_y`/`ETA_Y_*`）；~90 是 certified bank 外部锚（等接口 2 LP 桥，
  **不可填证解决**）。

## 6. 教训日志（编排者每波收工后追加；工人有观察也写报告里）

### 2026-09-28 · Wave 1（LA38：66→58，8 枚+17 辅助；PA25：155→144，11 枚+6 辅助；桥 lane：PA2+PA4）

**编排侧新招与教训（wave2 实战）**：
- **scratch-root 闸门技巧**：并行 lane 弄脏所有自然收官根时，用**未跟踪** scratch
  模块做 GATE_ROOTS（git diff 看不见它，不触闸门①；import 选干净近邻织撞名网；
  用完即删）。PA22 用 {PA22,PA23,Polytope,TopologyFan}、LA5 用 {LA5,LA2,LA3}。
  **选根前必须核对闭包**：LA7→PA18、PA25→PA18、TameLp→LA5 这些边不看 import 列表
  根本想不到。
- **import 耦合的 lane 编排**：同波 lane 文件有 import 边时，下游 lane 的终验会被
  上游 lane 的编辑中状态卡死（LA38-r2 被 PA18 卡 → 协调为"工人停止轮询交报告，
  编排者统一终验"）。以后排 wave 尽量让 import 相邻文件不同波；否则默认
  工人自验+编排者统一构建。
- **闸门规则②再次演进**：骨架普遍是单行陈述 `theorem FOO … := sorry`，工人删整行
  重写时陈述文本随之进 diff——允许 `… := sorry` 整行删除但**陈述前缀必须在新增行
  逐字重现**（sed 提取前缀 + grep -F 校验），冻结语义不变。

- **成本基线**：84 min / 39.5M tokens / 196 工具调用 / +513 行。token/产出比偏差的
  四个根因 → 全部固化为 §2：①整读+重复读大文件（LA38 2.4k 行、TopologyFan 4.3k 行）
  ②分类滞后（目标 ≥15 定在分类前，实际机械题只有 ~10）③17 个新引理零查重
  ④1-2 枚一验的编译节奏。
- **PA25 打回事件**：末段编辑后未终查 + `": error:"` 单一 grep 假阴性 → 5 个编译错误
  整单被闸门拦下打回（返工仅 11 min/8.3M tokens，闸门价值实证）→ §2.7 收笔终查 +
  §3 双格式。
- **桥 lane 实证 `lake env lean` 假绿**：env-lean 放行 `abs_add` 等旧名/模块模式
  不可见项，`lake build` 拒绝 → §3 终验升级为 lake build 同款。**这是环境级发现，
  不是个例。**
- **桥 lane 战果**：OAPVION2_concl 闭合（Mathlib `existsUnique_dist_eq` 路线 + 附带
  OAPVION1/3）；MCELL_BUMP_0 精确 NEEDS → 根子是 AJRIPQN 未移植（§5.4 PA4 条）。
  "桥作为 lane 目标"模式验证成功：一份投入解锁下游成簇。
- **编排侧教训（GATE_ROOTS）**：被并行 lane 半成品污染的收官根会让无关 lane 的闸门
  误伤——用 GATE_ROOTS 换成"干净的中段模块根"（如 PA12 覆盖 packing 家族撞名网）；
  选根前先确认其 import 闭包不含 dirty 文件（TameLp 竟能经某链到达 LA5）。
- **正面经验**（复用）：①`sigmaFan 0 univ E (vv i) (vv (i+1))` 是两点集 epsilon 唯一性
  计算，**不需要扇几何**——看似几何的题先找纯集合/算术内核；②HOL 的 LP 论证有
  时可用初等算术复现（`delta_4680581274`：配方法拆成 `−4(c−4)²<0` + 恒正项）；
  ③Mathlib 现成的 `AffineIndependent.existsUnique_dist_eq` 能整链复刻 HOL 的
  CIRCUMCENTER_LEMMA——先查 Mathlib 再手搓；④动手前备份原文件到 /tmp。
- **闸门 mac 适配完成**：perl timeout shim / Text 七收官根替代 Kepler 全根 /
  `LANE_FILES` 并行 lane 轮换验收（b0bed032）。工人无需关心，编排者操作。
- **NOTES-LANE 定型（2026-09-28）**：侦察/桥 lane 的合法交付物 = 纯注释 NEEDS
  注记（零删行），不强行填错题——GLTVHUM lane 零填证但产出五级链地图 + 一条
  陈述分歧，就是成功。闸门已配套：规则②⑤对零删行 diff 自动豁免
  （54d9ed0f/2a9cfed9）。编排侧footgun：`LANE_FILES` 是**替换式**白名单，
  设置时必须把 lane 文件本身也列进去（已两次踩坑）。
