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
- 已知假陈述：`SUM_INTER`（LocalAuto38:419，**移植错误非桩**：HOL `sum` 按支撑集取
  junk、项目 `setSum` 按集合取 junk，反例 `A=univ, B={0}, f=const 1` 机器证实；
  修复 = 加 `A.Finite` 前提，新陈述+证明已端到端编译验证，全树零消费者）。
  提案已入库 `docs/statement-fix-proposals.md` 项 1（A 级，等闸门豁免拍板）。
- **DUUNHOR_concl（PA2:557）前提缺失疑点（侦察 lane 2026-09-28）**：比 HOL
  （Rogers.hl:1682）少 `Packing V ∧ saturated V`；HOL 证明第一步即经
  `VORONOI_CLOSED_EQ_LEMMA`（Rogers.hl:1256，带 packing）消费 packing，
  PA6:837"前提未用"注记与原文不符。补前提会破坏 PA6:841 背引用（需同步加参）。
  已入假陈述修复提案清单。
- **PA22 桩致假 8 枚（wave2，修复 = 等 def 落地或改陈述前提，均一句话反例已核）**：
  `regular_spherical_polygon_area_asnFnhk`（asnFnhkP22=0 桩）、`vol_solid_triangle_ortho`、
  `EDGE_PAIR_pr23`（eFanP22 恒等桩）、`BIJ_FACET_HYPERFACE`/`HYPERFACE_EXISTS`
  （落空 faceSet）、`RELATIVE_INTERIOR_AFFINE_FACE`（**无病**：提案官复核 f=∅ 时
  `p ∈ affineSpan ℝ ∅` 不可满足，原"f=∅ 反例"指控不成立；原陈述经已证 helper
  `p22_face_of_affine_rint` 逐字填证通过——免豁免、无需加前提，修复波第 1 顺位）、
  `BIJ_DART_POLYEDGE`、`PACK_INEQ_DEF_A_797`（卡 arclength 落地）。
- **PA22 r2 新增疑似假 4 枚（2026-09-28 立项）——【2026-09-29：DEF-FIX 定义纠正
  已落地，`docs/planar-encoding-fix.md` §2 补丁已应用】**：`facetOfC` 补 ≠∅+affDimC、
  `polyhedronC` 改 H-表示、`cone0P22` 改严格 `affGt`。据此：
  项 12 `affine_facet_hyper` 与项 13a `pad2d3d_facet` **定义纠正已落地**（陈述即
  HOL 镜像，解冻前置就绪；仍冻结待 §2.3 kit：affDimC kit / FACET_OF_POLYHEDRONC
  _EXPLICIT / FACET_OF_LINEAR_IMAGE ℂ 版，落地前不入重填队列）；项 11
  `facet_rep_uniq` 的 ≠∅ 前提已由新 `facetOfC` 自带（补丁 11 撤回勿再应用）；
  `ARG_ORDER`（holArg 改述）与 DEF-FIX 无关、维持 A′。**CONE0 族：定义纠正已落地**
  （`affGe→affGt` + 陈述侧三处同病纠正 + `gotcjah_sol_half`），弱语义假化解除，
  CONE0_FCHANGED 家族各枚为真待重填（移出"假陈述"黑名单、入重填队列）。
  r2 的 14 枚 planar-kit 填证已按章程回退为 `sorry -- DEF-FIX`，待按 HOL 原文重填
  （优先序见章程 §3d；`gotcjah_sol_half` 仍归 GOTCJAH 专项）。
- **PA7 疑似假 2 枚（r2 报告，待提案官立项）**：`KSOQKWL`——`permutes` 弱集合
  稳定编码下为假（p 在固定段 0..k 之外可动，hrog 平凡成立而结论 p = refl 不成立）；
  `IVFICRK` 同编码可疑。

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
| `affineSpan_empty` | 无此名；`AffineSubspace.span_empty` + `bot_coe` |
| `Real.pi_lt_22_div_7` | 无此名；用 `Real.pi_lt_four` |
| `Module.Basis.constr`（旧签名） | `hb.constr ℝ f`/`hb.constr_basis ℝ f i`——**R 与目标模显式**（`Module.Basis ι R M` 的 R 也显式） |
| `div_mul_cancel₀` | 无；用 `div_mul_cancel`（PA7 r2 实测） |
| `Nat.card (Set.range f)` 基数 | `Nat.card_range_of_injective`；`Set.Finite.ofFinset` 为 iff-binder 形状 |

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

**PackingJGXZYGW 实测新增（2026-09-29，lane J）**：`volume_empty` 不存在→
`MeasureTheory.measure_empty`；`Set.Finite.image` 实为根命名空间
`Finite.image (f) (hs)`（**函数在前**）；`rfl`-pattern 在 `var = 定理级变量` 上
env-lean 与 build 的 subst 方向相反（env 替换 var、build 替换定理变量），一律改
显式 `have hwS : w = S` + 定向 `rw`——这是 env-lean 两度假绿的典型来源；
`EuclideanSpace.volume_ball_fin_three` 形状是 `ofReal r^3 * ofReal (π*4/3)`
（ofReal 在幂内层）；`Real.sqrt_mul {x} (hx : 0 ≤ x) (y)` 首因子由 hx 固定；
`div_le_iff₀ (hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c`（mp 需要 `≤ a*c` 形状）。

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
- **LA5**（115 remaining @r2，wave2-r2 已落 8 枚：SPAN 桥 4 + affGe 2 + SELF_CYCLIC 2
  + 10 私件）：**WRGCVDR 巨石是 LOFA 簇根阻塞**（LOFA_CARD_EE_V_1/EXISTS_INVERSE_OF_V/
  LOCAL_FAN_ORBIT_MAP_V——"每点恰 2 邻"就是轨道循环性内容本身，纯计数路线不可行）。
  orbit 引擎（la5_orbit_period/la5_iterate_mod/la5_min_period 等）已就位可白捡 4 枚：
  LOOP_MAP_IMP_DIFF_FIRST_ELMS(:866，早于私件块 :962，需内联 la5_self_cyclic_finite
  5 行论证)→LE_CARDV_IMP_CARD_DETERED(:1424)→LOOP_SET_DETER_FIRTS_ELMS(:1443)→
  LOOP_SET_ITER_CARD_ID(:1731)；:1735 仍卡 WRGCVDR。SPAN 套件邻簇直接清：
  CONDS_FOR_INTER_AFF_CONV0(:1142)/INTER_AFF_GT_LT_IMP_INTER_AFF_CONV0(:1148)/
  NOT_INTER_EQ_EM_IMP_AFF_SUBSET(:1339)（la5_conv02_partner 的 1/β 射线构造）；
  AFF2_DET_BY_TWO_POINTS(:1122) bonus 路线 = lineMap 参数 s/(s−t) 研磨。
  lunar/HKIRPEP 深簇按指令跳过。
  **命名/战术坑（LA5 实测）**：`Function.iterate_succ_apply` 是 `f^[n+1] x = f^[n] (f x)`
  （与惯常相反，`'` 版才是 `f (f^[n] x)`，且 f 显式首参）；`Function.iterate_add_apply`
  全显式参；`Nat.find_min` 首参 `(h : ∃ n, p n)` 显式、`Nat.find_le` 收见证项不收
  hex；`(q-1)+1` 被 elaboration 归一为 `(q-1).succ`（show/omega 按 succ 形态写）；
  omega 不做符号 div/mod（用 `Nat.div_add_mod'`）；`Set.BijOn` 的 SurjOn 是 ∀-def
  **必须 intro 风格**不能用匿名构造器；`mem_affineSpan_pair_iff_exists_lineMap_eq`
  方向 = `∃ r, lineMap p₁ p₂ r = p`；`AffineMap.lineMap_mem` 三显式参；
  目标里 `(affineSpan … : Set V3)` 的 SetLike coe 挡 rw，先 `rw [SetLike.mem_coe]`；
  单点等式代换用 `nth_rewrite 1`（rw 殃及所有出现）；`Finset.mem_singleton_iff`
  不存在（用 `Finset.mem_singleton`；Set 侧才是 `Set.mem_singleton_iff`）；
  `obtain … := h` 会清除 h（先 `have hkeep := h`）；同文件禁前向引用；
  U+209D 不是合法标识符字符。
- **PA18**（71 remaining @wave2）：本轮落下**三座 azim↔affine 桥**（private，
  回灌时去 private）：`pa18_azim_zero_affGe`（azim=0 ↔ affGe，即 LA5:1312
  AZIM_EQ_0_GE_ALT2 的证明版）、`pa18_affGe_affGt_of_ncol`、
  `pa18_collinear3_line_affGe`。cc 簇最短解锁路径：**MHFTTZN3（PA6:848）可由
  MHFTTZN4+BARV_CIRCUMCENTER_EXISTS+XYOFCGX(PA7:343) 自证**（⚠ 时效：PA7 r2 已
  整体回退，BARV_CIRCUMCENTER_EXISTS 等待按 `docs/pa7-proofdump.md` 落盘，
  见 PA6+PA7 条）→ JDHAWAY_0 →
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
  `MCELL4_EDGE`(:1524) 与 `MCELL_EDGE`(:1561) 疑点已**解除**（提案官 2026-09-28）：
  两陈述各与 bump.hl:766/816 逐字同义，论域被 k<4 挡死不相交，且两定理及 helper
  链已全部无 sorry——一致内核内不可能不相容，无需修复。
  可复用：`hdtfnfz_p4` kit（16 个 `_p4` 私件）、`(by simpa using (Finset.mem_filter.1 he).1)`
  桥、`Set.ncard_insert_of_notMem + Set.ncard_le_ncard` 计数安全路
  （`Finset.card_le_card` 已单参、`Set.Finite.card_le_card`/`toFinset_cong` 不存在或签名变）。
- **PA6+PA7**（wave2-r2 零净填充，两文件 pristine 双绿 = 干净起跑线）：r2 写好
  env-0-error 的 PA7 19 枚 + PA6 多枚，被 lake build ~50 系统性偏差打回
  （**env-lean 假绿最大实证**，见 §6）。证明全文 + 逐错误诊断落盘于
  `docs/pa7-proofdump.md`（下一轮按图施工）。下一轮优先级：① PA7 逐枚落盘
  （HL_DECREASE/投影簇/TRUNCATE kit 等，多为小错）② PA6 MHFTTZN3 +
  p6_affdep_of_dim（PA18 钥匙；**BARV_AFFINE_INDEPENDENT 解锁链**：
  MHFTTZN_lemma2.1 → `List.toFinset_card_le` →
  `Submodule.exists_finset_span_eq_linearIndepOn` + `linearIndepOn_id_range_iff` +
  `affineIndependent_set_iff_linearIndependent_vsub`，API 已验证存在）
  ③ HALFSPACE_EQ 分量法重写。**分量法（`ext i` + `Fin.sum_univ_three` + ring）
  是 ⬝ᵥ/WithLp 证明唯一稳定路线**，rw 深链全灭。回退不攻：
  ANGLE_EQ_DIHV、AFFINES_INTER_BALL_EQ_IMP_EQ（ofLp-rw 沼泽）。
- **PA22**（53 remaining @r2，wave2-r2 已落 20 枚）：**万能钥匙 `p22_ball_face_contra`**
  （PA22:135：polyhedronC P → 0<r → 球含于 P → False——planar-面 kit 14 枚全走它）；
  arcV 桥三私件（`p22_arcV_eq_angle`/`p22_cos_arcV`/`p22_arcV_mem_Icc`）azim/arc
  族可复用；GOTCJAH 三枚（gotcjah_sol_half/lemma/GOTCJAH）需锥体立体角测度计算
  （数百行，独立专项）；eus1 为实质深题（HOL ~75 行）。钥匙引理 = `TopologyFan.sum4/sum5_azim_fan`
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
- **PA21**（34 remaining；2026-09-29 侦察结案）：被消费主结论 = `TSKAJXY`
  （:1407），唯一链上消费点 PA25:3704 `exact TSKAJXY …`；其 0/3/4 臂 sorry
  （:1428）**GIANT 结案，勿再盲目重试**——三重硬阻断：①`pack_nonlinear_non_ox3q1h`
  （:147）是不透明 Prop 银行（19 条子不等式无从抽取，且与 `tsk_hyp` 不 defeq，
  探针实证）②`Merge_ineq.GRKIBMP`/`cell3_from_ineq_thm` 全树未移植
  （merge_ineq.hl:3794/:3507，依赖 Optimize.h0cutB、nonf_gamma2_x1_div_a_v2、
  ineq-演算 ~200 行）③`eta_y`（:131）body 缺失（PA25:160 亦有记载）。
  收口路径：银行结构化（陈述级，走 STATEMENT-FIX）→ 移植两分发器及其依赖 →
  :1428 机械闭合 `exact TSKAJXY_034 ⟨GRKIBMP …, cell3_from_ineq_thm …, …⟩ …`。
  HOL 锚点：TSKAJXY3.hl:2251（capstone，0/3/4 臂 2255-2272）、TSKAJXY2.hl:61-92
  （特形件）、merge_ineq.hl:118-134（银行 def）。1/2-cell 臂已闭合（:1419/:1425）。
- **PA6**（14 remaining；2026-09-29 MHFTTZN3 已闭合 + 新增 public `p6_affdep_of_dim`）：
  链上剩余模于 `MHFTTZN_lemma`（Rogers.hl:4053，~290 行归纳）与
  `MHFTTZN_lemma2`（:4340，~520 行归纳）两枚上游 sorry；`MHFTTZN_lemma` 的关键步
  `VORONOI_LIST_INTER_BIS` 在 PA5:1410 本身是 sorry（跨文件，需专项），
  另需 affDim(∩超平面)=affDim−1（Polytope.lean:203 `affDim_hyperplane` 可作原料）。
  PA18 钥匙三件套（MHFTTZN1 + BARV_IMP_LENGTH_EQ_CARD[PA7,仍 sorry] +
  p6_affdep_of_dim）可闭合 `BARV_AFFINE_INDEPENDENT`（PA7:374）。
- **ContraFan**（2 remaining；2026-09-29 侦察结案，见 docs/contrafan-scout.md）：
  两枚陈述与 HOL 逐字同义无弱编码。CF-3 = `LEMMA_3_POINTS_FINAL`（:400）走路线 B：
  Mathlib `angle_eq_angle_add_add_angle_add_of_mem_span` + 纯有理数余弦界
  （cos ≤ 2719/3969、cos ≥ 1031/7938，数值见证已手算）+ 现成 `annulus_ray_absurd`，
  250-400 行中等档。CF-4 = `LEMMA_4_POINTS_FINAL`（:414）忠实移植 GIANT
  2000-3000 行，建独立模块 ContraFanDeep.lean（import Geom.Aff+PackingAuto2，
  无环，ContraFan 仅 2 行转发），切 CF-4a/4b/4c 三波，依赖 CF-3。
  陷阱：PA21:131 `eta_y := sorry` 是 def-sorry 严禁依赖；V3 内积一律走
  `inner ℝ` 泛型（避 ⬝ᵥ/ofLp 假绿）；`affGe` 闭锥是忠实移植，勿"修正"为 affGt。
- **PA19**（UPFZBZM W1 已清 @abfd2fcb）：NEGLIGIBLE_FUNC 架构已真证；`let q :=
  …` 出现在 goal 内时先 `simp only []` zeta 归一再 rewrite（本轮主要坑）；
  `Finset.sum_const` 产生 ℕ-smul，走 `nsmul_eq_mul` + `Nat.card_coe_set_eq`；
  voronoiOpen P16→P19 差异用定义性 ascription 吸收（`hb1 : … := hc1 …`），零 shim。
  余债 = 上游四巨物（KIZHLTL1/2/4+SUM_GAMMAX）。
- **PackingJGXZYGW**（JGXZ 链已全清 @83f5ea04，公共件可直接 import 复用）：
  `jgxzygw_p` 公开 capstone + 33 枚 `jg_` private（测度主点
  `MeasureTheory.measure_biUnion_finset`+PairwiseDisjoint、negligible 系、
  step1-4 全套）——后续任何 voronoi 测度链 lane 先看本模块，勿重写。

## 6. 教训日志（编排者每波收工后追加；工人有观察也写报告里）

### 2026-09-29 · Wave 6（Merge_ineq 波2a-3 / UPFZBZM W1 / JGXZ 全链 / 双 shim / 双侦察降档）

- **规则⑤审计目标必须是公开名**：private 定理（如 `JGXZYGW_KY_p2`）在
  `#print axioms` 外部文件里是 Unknown constant——闸门审计目标一律选本文件
  公开消费者（同陈述或直接下游），不要为过闸把 private 改公开。
- **闸门演化 10**：规则② docstring 内行豁免自引入以来是死代码——dels 扫
  opener 的近似在"首行留作上下文"的改写下找不到被删块开头，且 cmt 收集带
  `-` 前缀与比对侧剥前缀永不相等。改为从 HEAD 文件内容收集（同 DEF-FIX
  dint 法）+ `· --` 战术位注释行入硬过滤豁免。首次真实行使即暴露。
- **新模块 lane 的 shim 串行协议**：新叶模块（PackingJGXZYGW）与既有银行文件
  （PA2/PA19）的双向债，拆两个 lane 时 shim 一律由 lane 交付**补丁文本**、
  编排者在两 lane 落地后串行贴+闸——否则两工人同写 PA19 必撞车。
- **侦察先行降档实测两连**：JGXZ"GIANT"实为 PA1 半成品山（12/22 已证，210-360
  行，单 lane 全清）；UPFZBZM"GIANT"实为装配 100% 完成 + 一枚 bare sorry。
  定级先看树内存量（骨架覆盖度），再决定侦察 or 直接填——侦察报告就是规格书。
- **新文件闸门流程**：untracked 文件规则①看不见 → 编排者先 `git add` 再跑闸
  （ContraFanDeep/PackingJGXZYGW 两次实践）；`git show HEAD:新文件` 在 cmt
  收集处 fatal 到 stderr 但 `$( )` 吞掉不致死——无害，可忽略。
- **env-lean 两度假绿的系统性根治**：rfl-pattern 在 `var = 定理级变量` 上
  env/build 替换方向相反（JGXZ lane 三处返工）——一律显式 `have` + 定向 `rw`；
  收工终验必须 `lake build`（§3 已有，本波再+1 实证）。

### 2026-09-29 · Wave 4 六 lane 批（PA22 波1 / TameLp W1 / PA21 / PA6 / LA38 / ContraFan）

- **不透明 Prop 臂先探针后动工**：PA21 TSKAJXY 0/3/4 臂侦察实证——目标臂的
  消费前提是不透明 Prop（`:= sorry` 银行）时，先写 5 行 defeq 探针（`lake env lean`
  里直接试 `exact`）再决定是否填证；本次 5 分钟的探针拦下了数小时的无效证明
  写作（Type mismatch 实证：两个不透明 Prop 连合取投影都拿不到）。
- **侦察结案必须回流债务图**：GIANT 结案不是"白跑"——e2e-debt-map B 表加行 +
  playbook §5.4 加条，下一波就不会对同一目标重复侦察（B 表行同步给出收口路径，
  把"填不了"转成"差什么"）。

### 2026-09-29 · Wave 5（CF-3 / MHFTTZN 上游 / TameLp keystone / Merge_ineq 波0-1 / 五 lane 批）

- **工人严禁声称用户授权**：超任务书的改动只能上报编排者裁定；编排者按技术
  优劣独立审定（merge-ineq 波 0 的 arcLengthICD 改名即例——技术判定接受，
  但 agent 报告中"经用户在会话中授权"系虚构，已记录在案）。
- **import 级冲突复查 = 全链消费模块的附加 import 集求交**：同名声明碰撞
  （IneqClosureDefs vs PA18 的 `arcLength`）在单模块/直接消费者检查中不可见，
  只在 PA25 = PA21 ∪ PA18 的组装构建时爆。新 import 落地前先算闭包。
- **伞模块搭便车陷阱**：`GoodListDefs` import `Kepler.Graphs` 伞即拖入
  TameClassification → 全部 585 证书片（9017 jobs）；收窄为实际使用的
  PlaneGraphIso + ArchiveData 后闭包 955 jobs 全缓存。教训：下沉模块的
  import 按"实际使用的名字"收窄，不为图方便挂伞。
- **闸门演化 7-9**：⑦匿名 `intro _ _ …` 占位行豁免（新增行含 intro 重引入
  为条件）；⑧STATEMENT-FIX 模式跳过行首 sorry 净数（多重集相等已钉死
  sorry 面，且前缀计数对 def 体 sorry 失明）；⑨`NEW_SORRY_ALLOW` 带账
  脚手架（建设型 lane 的显式 NEEDS sorry，上限 + 等量注记双约束）。
- **落账轮刷新冻结文本**：定理真化后其 docstring/模块头仍写"骨架占位
  （sorry）"会误导下一波工人（ContraFan :30/:505 前科）——每个 commit
  收尾时同步刷新 DISCHARGES 行。
- **工人禁碰 Assembly.*/Graphs 构建 + 单 lean 进程配额**（2026-09-29 CPU 事故）：
  TameLp keystone lane 为探 GoodListDefs 命名跑了 `lake build Kepler.Assembly.GoodListDefs`，
  其闭包含整个 CertShards 链（9000+ jobs），拉起 12 worker 吃满全机，且被杀后
  无限重试。工程细则：①lane 的编译校验只允许 `lake env lean <自己的文件>`；
  ②探命名一律 grep/Read 源码；③缺 olean 时报告缺件名而非构建依赖；④任意时刻
  至多 1 个 lean 进程。编排者响应：先 SendMessage 叫停源（杀进程治标，
  agent 会重试），再清孤儿（批量 kill 可能静默失败，逐个 kill -9 + 立即 ps 验证），
  最后删除被并发写的可疑 olean 让喂片重建。

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
- **环境事故（2026-09-28，全波通报）**：worktree+共享 packages 符号链接的隔离方案
  引发 lake 缺 manifest→mathlib 重克隆，与并行 lane 并发竞争，共享 mathlib olean
  全失。**禁令**：①工人不得自建 worktree/符号链接共享 `.lake`——隔离迭代一律走
  untracked scratch 模块路线（§2）；②任何 lane 不得并发跑 lake 环境级操作
  （update/cache get/重克隆）；③环境修复由编排者串行接管，其他 lane 见构建报错
  统一口径"环境事故，恢复后重试秒过，不要自行修复环境"。恢复路径：
  杀源码编 Mathlib 进程 → `lake exe cache get!`（cloud cache，5-15 分钟）→
  smoke build 后统一放行。
- **假陈述提案轮（2026-09-28）**：10 项裁决 A=2/B=7/解除=1/C=0——8 枚 PA22 陈述
  全部与 HOL 逐字同义（无一移植错误），假陈述主要来源是**桩语义**而非抄错。
  方法论：①进黑名单前反例必须机器验证（本轮"f=∅ 反例"指控被复核推翻——纸面
  反例不可靠）；②交付物 = 提案文档 + 补丁草案（已存档
  `docs/statement-fix-proposals-patches/`）+ scratch 验证后删除，零 .lean 改动；
  ③RELATIVE_INTERIOR_AFFINE_FACE 无病可原位填证，不占豁免额度（修复波第 1 顺位）；
  ④"移植错误"（SUM_INTER junk 约定失配）与"桩依赖"要分开定级。
- **r2 波方法论沉淀（LA5+PA22，2026-09-28）**：①PA22 "全树副本到 /tmp + 脏文件
  `git show HEAD:` 还原 + 注入本 lane 文件"终验法 ≈ 编排者 stash 验收条件——
  import 耦合严重时的自助终验模板（副本须 diff 确认逐字节一致；此法为**整树复制**
  而非符号链接共享，不触环境事故禁令）；②linarith 不解构 Set.Mem 形假设
  （`hu : u ∈ Ioo 0 π` 显式传 `hu.1`），by 块作多参引理首参会提前 elaboration
  （metavar 未固定→假失败，用 `(x := u)` 具名参修复）；③Mathlib 富矿：
  `InnerProductGeometry.angle_le_angle_add_angle`/`Real.strictAntiOn_cos`/
  `exists_deriv_eq_slope`（MVT）/`ConcaveOn.le_map_sum`（Jensen）/
  `convexOn_of_hasDerivWithinAt2_nonneg`；④假陈述定级再+1 来源：**定义误移植**
  （polyhedronC/facetOfC 弱化）可使一族陈述空洞化为真——修复定义则整族需重填；
  ⑤编排者自教训：playbook 行级字节手术用 perl -i 遇宽字符可整文件清空——文档修订
  一律走 Edit 工具（本条即为付出 297 行回滚代价换来的）。
- **PA6+PA7 回退事件（2026-09-28）**：env-lean 0-error / lake ~50 error 的**最大规模
  假绿实证**——偏差模式（`⬝ᵥ` 的 WithLp.ofLp 包裹形状、`mpr ⟨w⟩` 方向、beta-redex
  上的匿名构造器）固化进 §5.4 PA6+PA7 条，分量法为唯一稳定解；预算耗尽前整体
  回退 pristine 保住双绿基线，证明文本落盘 `docs/pa7-proofdump.md`——"宁可零填充
  不留半成品"是正确止损。同日 `.lake/packages/mathlib` 波内第二次中途消失
  （`lake exe cache get` 11 秒恢复）——共享包目录稳定性存疑，波收尾排查根因。
- **Wave 2/2r 收官（2026-09-28 深夜）**：五 lane 过闸（PA18/PA4/LA38/PA22/LA5）+
  闸门五演进（①逐字加回豁免=纯块移动合法化 ②docstring 闭合行 `-/` 归注释
  ③拆行骨架 `… := by`+换行 sorry 转项模式填的尾行豁免 ④规则③ sorry 净计数制
  ⑤规则⑤ sorryAx 转白——填证消费在树债务合法，债务走账本）。编排者 footgun
  再犯一次：LANE_FILES 替换式忘带 lane 文件自身（第 3 次）——已写进本条防再犯。
- **脊柱探针本机结构性阻塞**：spine_axioms.py 信任 Graphs 缓存 olean，本机没有
  （重型计算档）；已 mac 移植（SPINE_CACHE_ROOT）入库，Graphs olean 就位即复跑。
  M5′ 度量暂走 docs/e2e-debt-map.md（结构性手工图，每波更新）。
- **修复工单模式定型**：编排者统一构建→精确错误清单+回退规程（30 分钟修不动=
  逐字节还原 HEAD 该定理）→修理工一次清多文件编译错（本轮 PA18 3+PA4 3+LA38
  ~19 全清）。比逐 lane 打回快一个量级。
