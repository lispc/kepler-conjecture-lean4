# orphan-scout — 孤儿直方图 + 影子子树量尺（2026-11-03 晚，续 259 入库）

> 车道交付原文（`lane_snapshots/orphan-scout/DELIVERY.md`）入库存档；测量脚本已落仓：
> `lean/scripts/orphan_histogram.lean`（157 根 union 孤儿直方图 + WIRE/PAIR_HINT/RDWKARC 探针）
> + `lean/scripts/shadow_map.lean`（每直源影子子树 shadow/alloc）。重建命令见脚本头注。

    # orphan-scout 交付（2026-11-03）
    
    测量车道：A 孤儿直方图 + B 每源影子子树 + C 混合榜单。纯测量，主仓 tracked 零改动
    （脚本以未跟踪新文件 `lean/scripts/orphan_histogram.lean` / `lean/scripts/shadow_map.lean`
    交付，diff 见 `scripts.diff`，待审后落库）。
    
    ## 0. 口径（必须随读数引用）
    
    - **冻结源码 ref**：起测时 HEAD = `50ad72b9`（批1收官对表）；测量窗口内又落了
      `e3de2d0b`（viz 文档，无代码）与 `ed6b5a1e`（pa25-b0-replay，PA25 11 直源闭）。
    - **olean 口径 = 测量时刻共享 .lake**：
      - `orphan_hist_full.out`：e2e CALIB K_REACH **2,078,505 / K_SORRIED 123**，与编排者
        基线 C（@a522078c）逐位一致 → pa25-b0 落库前态。
      - `shadow_full.out`：e2e CALIB K_REACH **2,078,646 / 直源 112**（+141/−11）→
        pa25-b0-replay 后态（`LocalConcl.olean` 15:36 重建）。两次读数漂移 = 该落库本身；
        **所有排名类结论对 ±几百节点/±11 源漂移不敏感**。
      - 直方图环境 `import Kepler + Kepler.Assembly + Kepler.Text.PackingConcl`（与
        global_reach_map v2 同宇宙，K_UNIVERSE 2,094,560）；影子环境 `import Kepler.Assembly`
        （与 e2e_reach_map 同宇宙，K_UNIVERSE 2,094,306）。两宇宙差 ~254 声明。
    - 工具纪律：地图进程全程单进程串行（另一车道 map 跑完才起跑），`nice -n 19`，
      未做 2M DUMP_TREE。
    - 已知标注：直方图 CALIB 的 `TOTAL_VALUE_DECLS` 列实为「处理的 Kepler 声明数」
      （= K_REACH，含 axiom），语义与 e2e_reach_map 的同名列不同，勿混用。
    
    ## 1. A — 孤儿直方图（in-env，K_UNIVERSE − 157 根 union）
    
    基线：157 根（e2e 1 + PackingConcl discharged **62** + LocalConcl discharged 92 +
    章 capstone 2 全命中）。**UNION K_REACH 2,079,719**；**ORPHANS_TOTAL 14,841**
    （非机械证书层 **13,284** + 机械证书层 1,557）。
    
    ### Top 10 模块（非机械证书层孤儿）
    
    | # | module | 孤儿 | theorem | def | 备注 |
    |--:|---|---:|---:|---:|---|
    | 1 | `Kepler.Text.Hypermap` | **1,299** | 1,157 | 138 | HOL hypermap.hl 核心层移植；**≥500 整文件孤儿候选** |
    | 2 | `Kepler.Text.LocalAuto35` | **741** | 735 | 6 | Local Fan 章 appendix 余件（QKNVMLB，全 `_p35`）**≥500** |
    | 3 | `Kepler.Interval.CertTM` | **618** | 369 | 228(+14 axiom) | TM0 Taylor-model 试点 **≥500** |
    | 4 | `Kepler.Text.PackingAuto21` | 305 | 303 | 2 | TSKAJXY2/3 链（hub PA20），capstone 已被链内消费、kit 未用 |
    | 5 | `Kepler.Text.LocalAuto38` | 291 | 269 | 22 | |
    | 6 | `Kepler.Text.LocalAuto13` | 290 | 222 | 65 | |
    | 7 | `Kepler.Text.PackingAuto25` | 283 | 283 | 0 | 最终 packing capstone；kit 未用面 |
    | 8 | `Kepler.Text.LocalAuto9` | 264 | 216 | 44 | |
    | 9 | `Kepler.Text.LocalAuto34` | 255 | 239 | 16 | |
    | 10 | `Kepler.Text.PackingAuto4` | 254 | 208 | 43 | |
    
    GE500 恰 3 个（上表 #1–3）。11–30 名长尾：LocalAuto36/22/18/5/19/28/31/32/1/37、
    PackingAuto15/18/24/12、`Kepler.Interval.Expr` 234、`Kepler.Assembly` 199 等（全表
    `logs/orphan_hist_full.out` HIST 段，180 个模块）。长尾形态 = 「章 kit 引理无人消费」，
    不是整文件孤儿。
    
    **PA19 探针（rdwkarc 名字扫描，4 命中）**：
    `Kepler.Text.RDWKARC`（PA19 正本，sorried=**false**，真证）：**不在锥、不在 union**，
    接线增量 vs 锥 / union 均 **8**；孪生 `rdwkarcConcl_pc` 已在锥内（增量 0）；
    `RDWKARC_concl`（PA2）在 union 不在锥（增量 14）；`RDWKARC_concl_discharged` 在 union
    （增量 1）。PA19 模块整模块孤儿仅 27 —— **PA19 已不是大额接线目标**（早前「整文件
    树外」态已被 PackingConcl discharge + pc 孪生消化，剩下的只有正本 RDWKARC 本体 + 8）。
    
    ### 机械证书层（单列，1,557 孤儿 / 26 模块，不计入直方图）
    
    `Interval.Cases.C3397113841.Shard*` 为主（最大 Shard8 127，全是 thm+1 def）。
    这是 IneqPilot 试点只消费了 C3397113841 一个案例、其余 22 个 Shard 未入树的直接体现。
    解冻后的鲸鱼，不在本 lane 排序内。
    
    ### A′ — universe 外整文件孤儿岛（env.header diff，新发现）
    
    源码 `lean/Kepler/**` 共 18,959 个模块文件，其中 **14,735 个不在直方图 env 的
    import 闭包里**（`logs/orphan_scout_files_not_in_env.txt`）：
    
    | 岛 | 文件数 | 性质 |
    |---|---:|---|
    | `Interval.Cases.*` | 13,293 | 机械证书层冻结（已知；env 只入了 IneqPilot 试点案例 C3397113841 的子树） |
    | `Kepler.LP.Pilot*/W6Align/RandShard12x20/T62586200165*` | ~952 | LP 机械证书层 |
    | `Kepler.Text.LP.*`（LPAll/LPCert/LPFarkas/LPLeaf*×180/W6Data*×15） | **205** | LP 章本体，只被 LP 证书岛 import（互相抱团、无人接入 e2e 宇宙） |
    | `Kepler.Text.TameSpine.*`（TameList1-72/GoodGraph/Keystone/TameOpposite1） | **75** | tame spine 岛，只内部互 import |
    | 单文件 | **8** | `Text.PackingAuto1`、`Text.PackingAuto22`、`Text.PackingAuto23`、`Text.LocalBridge`、`Text.LocalAuto6`、`Text.LocalAuto7`、`Text.LocalAuto10`、`Text.LocalAnchors` —— **零 import 消费者**（PackingAuto1 即 JGXZYGW 正本，PA19 的 `_p19` 拷贝在等它） |
    
    （Hypermap / Conforming* / Polytope / SphereKit / AzimBridge 等**在** env 内——首轮
    diff 因 comm 未排序误报过，已纠正。）
    
    ### 建议接线边（每条附依据，禁止凭空造边）
    
    | 边（孤儿侧 → 消费侧） | 依据 |
    |---|---|
    | `LocalConcl` 未接线 discharged 根（GSXRFWM/JKQEWGV2/JKQEWGV3/AQICLXA/EYYPQDW 等 130 条）→ e2e 链（LocalAuto1 对应 `*_concl` 接口改 consume discharged 版） | `LocalConcl.lean:611-616`（`GSXRFWM_discharged := LocalAuto33.GSXRFWM_p33` verbatim twin 注）、`:207`（注册表）、`:281/294`（WIRED 38 / 未接线清单）、`:2280-2288`（`WIRE LocalAuto1.JKQEWGV1_concl <- JKQEWGV1_p23` 既有先例注释） |
    | `Kepler.Text.RDWKARC`（PA19 正本）→ `PackingAuto2.RDWKARC_concl`（`RDWKARC_concl_discharged` 改引正本） | PA19 文件头 §DISCHARGES convention："`RDWKARC` matches the interface verbatim: DISCHARGES PackingAuto2.RDWKARC_concl (PackingAuto2.lean:856)"；探针实测正本树外 |
    | `Assembly.IdLists.certLookupDomain` / `TheNonlinearInequalitiesFilled` / `AllCertifiedMirror` / `CertifiedIneqHoldsMirror`（17 孤儿）→ `Assembly.certifiedIneqHolds` 注册表量产波 | `Assembly.lean:250-262`（查表体 = IneqPilot 样板、回落 True、"ID 清单 = 查表定义域"不变量点名 IdLists.certLookupDomain）；`IdLists.lean` 文件头（HOL 锚 `the_nonlinear_inequalities` 六分量镜像）；T0 落库词「109 id 与 Assembly.IdLists 逐条同序」 |
    | `Assembly.IneqPilot.certifiedIneqHolds_pilot` 等试点件（4 孤儿）→量产注册表 | `IneqPilot.lean` 头（"Assembly 脊柱非线性接口的目标形态示范"、"量产评估见 DECISIONS"） |
    | `Kepler.Text.Hypermap` 1,299 → 消费侧需**新 capstone**（Conforming 章/LP 的 hypermap 结论入 e2e 链） | Hypermap 文件头（HOL 锚 `hypermap.hl:25-205` 全定义层移植）；importer 面 ConformingAuto12-15+/AzimBridge/LP 在用，但章结论无人接 e2e |
    | `Kepler.Text.LocalAuto35` 741 → LocalConcl 注册表 v3 sweep / 章装配 | LA35 文件头（"Local Fan chapter appendix leftovers…toolkit in LocalAuto1"，HOL 锚 QKNVMLB.hl） |
    | `Kepler.Interval.CertTM` 618 → Taylor-model 路线物化 | CertTM 文件头（"Phase 5, TM0 pilot"，`taylor-model-design.md` §4） |
    
    PAIR_HINT 段另报 30 条机械配对（`*_concl`↔正本，多为「接口孤儿、正本在树」的注册表
    余件）；**双孤儿 4 条**：`IVFICRK_concl`/`REUHADY_concl_version2`（PA2）、
    `PEDSLGV1/2_concl`（LA1）——正本与接口都不在树。已知缺口：`X_discharged` ↔ `X_concl`
    配对未实现（只剥离一层后缀），由 global map 的 SHIMS 段补 coverage。
    
    ## 2. B — 每源影子子树（pa25-b0 后态：e2e 直源 112）
    
    口径：`shadow(M) = |closure(valued(M)∖C_e2e) − C_e2e|`（模块 unlock ceiling，
    优化：锥内种子闭包 ⊆ 锥故只播种非锥有值声明）；`alloc(D) = shadow(M)/nSources(M)`。
    **局限**：模块代理测「M 自己的未用材料」；Assembly 类消费桩的填证增益（引用他模块
    材料）不在口径内——Assembly 77 源实测模块 shadow 仅 1,764（alloc 22），坐实
    「填 e2e 直源 = 债务缩减、低 K_REACH 增益」。真证明间会重叠，shadow 合计是上界。
    
    ### 模块 shadow 全表（12 个含源模块，按 alloc 降序）
    
    | module | nSources | seeds(非锥有值) | shadow(M) | alloc/源 |
    |---|---:|---:|---:|---:|
    | `Kepler.Text.LocalConcl` | 1 | 175 | **1,080** | 1,080 |
    | `Kepler.Text.LocalAuto23` | 1 | 422 | **852** | 852 |
    | `Kepler.Text.LocalAuto22` | 1 | 251 | 262 | 262 |
    | `Kepler.Text.LocalAuto33` | 3 | 242 | 724 | 241 |
    | `Kepler.Text.PackingAuto2` | 1 | 151 | 151 | 151 |
    | `Kepler.Text.TameLp` | 1 | 122 | 125 | 125 |
    | `Kepler.Text.LocalAuto29` | 1 | 96 | 106 | 106 |
    | `Kepler.Text.PackingAuto16` | 1 | 37 | 37 | 37 |
    | `Kepler.Text.LocalAuto32` | 3 | 188 | 188 | 62 |
    | `Kepler.Text.LocalAuto20` | 3 | 96 | 107 | 35 |
    | `Kepler.Assembly` | 77 | 198 | 1,764 | 22 |
    | `Kepler.Text.PackingAuto25` | 19 | 210 | 248 | 13 |
    
    SHADOW_SUM_UPPERBOUND **5,644**（跨模块有重叠，非可加）。
    
    ### Shadow Top 20 源
    
    | # | alloc | 源 | module | kind | parent |
    |--:|--:|---|---|---|---|
    | 1 | 1,080 | `_private…LocalConcl.0…mnt11_anchor` | LocalConcl | theorem(混合) | `MIQMCSN_discharged` |
    | 2 | 852 | `LFLACKU_p23` | LocalAuto23 | theorem | `JEJTVGB_case_breakdown_p16` |
    | 3 | 262 | `OCBICBY_p22` | LocalAuto22 | theorem | `JEJTVGB_case_breakdown_p16` |
    | 4 | 241 | `MM_4I2_IMP_4T2_4T1_p33` | LocalAuto33 | theorem | `ARDBZYE_p33` |
    | 5 | 241 | `SCS_4I2_IMP_SCS_4T1_p33` | LocalAuto33 | theorem | `ARDBZYE_p33` |
    | 6 | 241 | `SCS_4I1_IMP_SCS_4I2_p33` | LocalAuto33 | theorem | `SCS_4I1_ARROW_SCS_4I2_STAB_4I1_p33` |
    | 7 | 151 | `GRUTOTI1_concl` | PackingAuto2 | theorem | `KIZHLTL4` |
    | 8 | 125 | `TameLp.fully_surrounded_perimeter_bound` | TameLp | theorem | `TameLp.MQMSMAB` |
    | 9 | 106 | `SCS_5M2_IMP_SCS_5T1_p29` | LocalAuto29 | theorem | `HIJ_STEP_1_p29` |
    | 10-12 | 62 | `YOBIMPP_p32` / `MIQMCSN_p32` / `NWDGKXH_p32` | LocalAuto32 | theorem | 各自 `_discharged` |
    | 13 | 37 | `QZYZMJC` | PackingAuto16 | theorem | `KIZHLTL2` |
    | 14-16 | 35 | `SCS_6I1_BERAK_BY_CSTAB` / `AQICLXA` / `FZIOTEF` | LocalAuto20 | theorem | `OEHDBEN(_PRIME)` |
    | 17-20 | 22 | `lpArchiveCertificatesDebt` / `tameCorrespondenceIso` / `jcajydu` / `fcdjdot` | Assembly | theorem | `lpArchiveCertificates`/`textCapstone` |
    
    （0 条纯 stub——112 源全部是带骨架的混合源；「值里只有 sorryAx」的纯桩不在 e2e 直源里。）
    
    ## 3. C — 榜单（预期新节点 ÷ 预估 agent 时）
    
    测得的总量级（先说结论）：**现有根集合内的全部可测上行 ≈ 接线 1,214（union−cone
    精确值）+ 影子上界 5,644（重叠未扣）**；>13K in-env 孤儿与 >14K universe 外文件
    只能靠**新 capstone/新根（物化）**解锁。填证大头的真实形态是「接线」：top shadow
    源（mnt11_anchor/LFLACKU_p23/p33 族）与 top WIRE 根（GSXRFWM/JKQEWGV2/3）是同一批
    子树的两面——把 LocalConcl 未接线 discharged 根接进 e2e ≈ 填掉 LocalConcl/LA23/LA33
    的直源。
    
    ### GO（低风险、有精确测值、agent 时短）
    
    | 目标 | 预期新节点 | 依据 | 预估时 |
    |---|---:|---|---|
    | **S1. LocalConcl 未接线 discharged 接线波**：GSXRFWM(522)+JKQEWGV2(462)+JKQEWGV3(384)+AQICLXA(45)+EYYPQDW(43)+FUNOUYH/JKQEWGV1(35×2)+VPWSHTO(28)+…（全 130 根 distinct 上界 1,214 已精确测得）；顺带即填掉 top1 shadow 源 mnt11_anchor(1,080) 与 LA23 `LFLACKU_p23`(852) | **≤1,214（distinct，精确）** | WIRE 段逐根测值；LocalConcl.lean:611-616/207/281/294/2280；先例 lane `la1concl-reroute-w1` | ~1 车道 |
    | **S2. Packing 接口小尾巴**：PA2 `GRUTOTI1_concl` 填证(151) + PA19 `RDWKARC` 接线(8，DISCHARGES verbatim) + PA16 `QZYZMJC` 填证(37) ≈ **+196** | 151+8+37 | shadow top7/13；PA19 文件头 §DISCHARGES；KIZHLTL1/2/4 家族 | ~0.5-1 车道 |
    
    ### GO-with-risk（测值明确，但会把 sorried master 债拉进锥，K_SORRIED 上升）
    
    | 目标 | 预期新节点 | 风险 |
    |---|---:|---|
    | JKQEWGV2/3 接线若走 p23 master：master 本体 sorried（LocalConcl:294） | 含在 S1 | 锥内 K_SORRIED 上升（信息项，护栏 K_AXIOM 不动）；建议接线时保留 discharged shim 形态 |
    | LA33 三源（SCS_4I2/MM_4I2/SCS_4I1，shadow 241×3，模块 724） | ~≤724，与 S1 高度重叠（GSXRFWM_discharged:=GSXRFWM_p33 同族） | `GSXRFWM1_p33` sorried 在案（LocalConcl:612 注）；**排 S1 落地后重测再定** |
    | LA22 `OCBICBY_p22`(262)、LA29(106)、LA32 3×62、LA20 3×35 | ~400 合计（重叠未扣） | 同上；均为 case_breakdown/p16 与 OEHDBEN 族 |
    
    ### 需用户裁决（量级大但要新建根/改架构，非「接线/填证」可归纳）
    
    1. **Hypermap 物化**（1,299 孤儿，HOL 核心层已 100% 在库）：给 Conforming/LP 章
       结论开新 capstone 进 e2e 链 —— 唯一三位数以上的一块，但等于「把 conforming 章
       接进脊柱」的架构决定。
    2. **LocalAuto35**（741）：LocalConcl 注册表 v3 sweep 或章装配，同属架构。
    3. **CertTM**（618）：Taylor-model 路线（TM0）物化与否是 pipeline 设计决策。
    4. **universe 外岛**：TameSpine(75 文件)/Text.LP(205)/LP 证书层(~952)/单文件
       PackingAuto1/22/23、LocalBridge、LocalAuto6/7/10、LocalAnchors(8) —— 是否值得
       import 接入（PackingAuto1 = JGXZYGW 正本，PA19 `_p19` 拷贝在等它）。
    5. **机械证书层**（Interval.Cases 13,293 文件 / in-env 1,557 声明）：解冻决策，超出本 lane。
    
    ### 下一批 3 槽提名
    
    1. **S1 LocalConcl 接线波**（GO）：+≤1,214 精确、1 车道、有先例、风险仅 K_SORRIED
       可视化 —— 单位节点成本全场最低。
    2. **S2 Packing 接口小尾巴**（GO）：+~196，0.5-1 车道，同时清掉 PA2/PA16/PA19 三个
       接口债家族的显形余件。
    3. **S3 Hypermap 物化侦察**（需用户点头后转 GO）：不写证明，先出「conforming/LP 章
       哪个结论做第一个 Hypermap 消费 capstone」的侦察件（对照 1,299 孤儿的闭包构成），
       为 4b 之后的大额树增长铺路。
    
    ## 4. 局限
    
    1. olean 漂移：测量窗口内 pa25-b0-replay 落库（123→112 源，+141 节点），直方图与影子
       两次读数不同构；排名结论不受影响。
    2. shadow 模块代理低估「消费桩填证引用他模块材料」的收益（Assembly alloc 22 即此
       口径的体现）；高估模块间重叠（上界非可加）。
    3. `X_discharged ↔ X_concl` PAIR 配对缺一层剥离，coverage 由 SHIMS 段补。
    4. 两个章 capstone：`OXLZLEZ` 已在锥内（无 WIRE 行）；`PACKING_CHAPTER_MAIN_CONCLUSION`
       增量仅 15 —— 笔误修复后的接线收益可忽略，已被脊柱消化。
    5. universe 口径随 import 集合而变（2,094,560 vs 2,094,306）；跨文档比较需注明环境。
