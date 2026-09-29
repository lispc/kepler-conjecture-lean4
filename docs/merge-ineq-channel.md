# merge-ineq-channel.md — "Merge_ineq 通道"立项章程（MERGE-INEQ）

> 立项依据：`docs/fill-worker-playbook.md` §5.4 PA21 条（2026-09-29 侦察结案）+
> `docs/e2e-debt-map.md` B 表 "TSKAJXY 0/3/4 臂（:1428）" 行。本文 = 立项章程
> （只读侦察交付物），五节 = ①HOL 语义基准 ②陈述补丁草案（STATEMENT-FIX 地盘，
> 只写草案不执行）③波及面清单 ④闸门规程与执行顺序 ⑤与 MQMSMAB 通道的合流
> 评估，另附 §6 风险清单。
> 侦察纪律：零 .lean 改动、零 tracked 文件改动，唯一仓库写入 = 本文档；
> 不跑 lake / auto_gate / git 写操作。所有 file:line 均经 grep/sed 实测核对。
> 对照基准：`reference/flyspeck`（text_formalization/nonlinear/merge_ineq.hl 6573 行、
> nonlinear/ineq.hl 4011 行、general/sphere.hl、packing/TSKAJXY2.hl 731 行、
> packing/TSKAJXY3.hl 2288 行）。
>
> **核心结论先行**：
> ① PA21:1428 的 0/3/4 臂收口 = 三波：银行结构化（陈述级，波 0）→ 两分发器
> 移植（GRKIBMP ~50 行机械；cell3_from_ineq_thm GIANT ~900 行，切 2a/2b）→
> `exact TSKAJXY_034 …` 机械步（波 3）；
> ② **PA25 适配可免**：`pack_nonlinear_non_ox3q1h` 同名换体后 PA25:3704
> `exact TSKAJXY V X hnl …` 的 elaboration 只看参数类型（常量名不变即 typecheck），
> 全库 grep 实证无任何 unfold/rw 触及该 def（§2.3 逐条论证，diff 为空）；
> ③ **银行口径精确化**：HOL 银行是 Ineq 数据库的**全库过滤合取**（快照 81 条，
> `IdLists.lean:128` rfl 钉死），任务背景所述"19 条"是 **TSKAJXY 消费切片**
> （`tsk_required_ineq`，TSKAJXY3.hl:2240）。本章 §2 采"19 切片材料化 + 62 条
> 单叶挂账"的折中形态（路线 A′，§2.0 裁决矩阵），与 81 条口径的桥登记折算点；
> ④ **eta_y 的忠实体已在树内**：`IneqClosureDefs.lean:620 etaY`（经 :606 etaX，
> sphere.hl:131-135 逐字）——PA21:131 的 `:= sorry` 只需一行重指向，零新证明，
> 且顺带解锁 PA25 的 ETA_Y_* 填证队列（RADV_ETAY :825、ETA_Y_POS_LE_ALT :2808 等）；
> ⑤ 19 条切片的 Lean 树**同义件覆盖度 = 0/19**（无一以独立定理存在），但其
> 全部函数 kit 已备齐（§6.3 缺口仅 4 个小 def + 常数算术 kit）。

---

## §1 HOL 语义基准（逐字锚点）

### 1.1 银行 def — merge_ineq.hl:113-134

HOL 原文（`reference/flyspeck/text_formalization/nonlinear/merge_ineq.hl`）：

```ocaml
let packing_ineq_data =                                           (* :113-116 *)
  filter (fun ind ->
	    has_flypaper_tag ["UKBRPFE";"BIEFJHU";"OXLZLEZ";"TSKAJXY"] ind &&
	 not(is_ox3q1h ind)) (!Ineq.ineqs);;

let mk_pack_nonlinear =                                           (* :118-122 *)
  let ineql = map (fun idv -> idv.ineq) packing_ineq_data in
  let packing_ineq_conj = end_itlist (curry mk_conj) ineql in
  let _ = new_definition (mk_eq (`pack_nonlinear_non_ox3q1h:bool`,packing_ineq_conj)) in
    ();;

let get_pack_nonlinear_non_ox3q1h =                               (* :124-134 *)
  let ineql = map (fun ind -> ind.ineq) packing_ineq_data in
  let sl = map (fun ind -> ind.idv) packing_ineq_data in
  ...
    fun s -> let i = index s sl in
      let th2 = funpow i CONJUNCT2 th1 in
	co1 th2;;   (* co1 = 末层取 CONJUNCT1 *)
```

机制要点：
- `is_ox3q1h`（:107-111）= idv 前缀 `"OXLZLEZ 6346351218"`（ineqdata3q1h.hl 的
  230 条 3q1h 件，另行合取为 `ox3q1h`，PA25 `ox3q1hP25` 对应）；
- `has_flypaper_tag`（:103-105）= 条目任一 `Flypaper` 标签串与四键相交非空；
- **银行规模**：按上述过滤对 Ineq 数据库全量取合取。Lean 侧权威注册表
  `Kepler/Assembly/IdLists.lean:43-126` `packNonlinearNonOx3q1hIds` 给出 81 条
  清单（生成器 `gen_idlists.py`，`Ineq.add` 前插内存序，IdLists:36-39），条数由
  `packNonlinearNonOx3q1hIds_length`（IdLists.lean:128）`rfl` 钉死 `= 81`。
  **任务背景"19 条具名不等式合取"精确化为：19 = TSKAJXY 消费切片
  （`tsk_required_ineq`，TSKAJXY3.hl:2240-2249），81 = 银行全量**。
- 每个条目本体是 `all_forall (ineq [box] concl)`（`ineq.hl` 经 `add` 注册），
  其中 `Sphere.ineq`（sphere.hl:27-29）是 list 递归的区间蕴含包装：

```ocaml
let ineq = define
 `(!c. ineq [] c <=> c)
    /\ (!a x b xs c. ineq (CONS (a,x,b) xs) c <=> a <= x /\ x <= b ==> ineq xs c)`;;
```

  `all_forall`（sphere.hl:31-33）= 对自由变元（排序后）做全称闭包。

### 1.2 TSKAJXY 消费的 19 条切片（逐条名字 + 原文行号）

抽取序 = `tsk_required_ineq`（TSKAJXY3.hl:2240-2249）= `cell3_hyp @ tsk @ grk`，
三组分别镜像 merge_ineq.hl 的 `cell3_hyp`（:3490-3495）、`tsk_hyp`（:1370-1377）、
`add_hyp ["GRKIBMP A V2"; "GRKIBMP B V2"]`（:3795）。"原文行号"= ineq.hl 中
`add {idv=…}` 注册块首行（idv 行）。

**cell3 组（7 条，cell3_hyp 序）**：

| # | idv | ineq.hl 行 | 域 box（六段 [下,y,上]） | 结论 |
|---|---|---|---|---|
| 1 | `QZECFIC wt0` | :1372 | [1,1]×[1,1]×[1,1]×[2.01,2·hminus]×[2,2·hminus]×[2,2·hminus] | `y_of_x (gamma3f_x_div_sqrtdelta 1 1 1) … > 0` |
| 2 | `QZECFIC wt0 corner` | :1389 | [1,1]³×[2,2.01]³ | 同上函数 `≥ 0` |
| 3 | `QZECFIC wt0 sqrt8` | :1406 | [1,1]³×[2·hplus,√8]×[2,2·hminus]×[2,2·hminus] | `(0,1,1)` 版 `> 0 ∨ eta_y(y4,y5,y6)² > 2` |
| 4 | `QZECFIC wt1` | :1425 | [√2,√2]³×[2·hminus,2·hplus]×[2,2·hminus]×[2,2·hminus] | `(h0cut y4,1,1)` 版 `> 0.008·y_of_x dih4_…posbranch ∨ eta_y² > 2` |
| 5 | `QZECFIC wt2 A` | :1443 | [√2,√2]³×[2·hminus,√8]×[2·hminus,√8]×[2,2·hminus] | `(h0cut y4,h0cut y5,1)` 版 `/2 > 0.008·dih4 ∨ eta_y² > 2` |
| 6 | `CIHTIUM` | :1462 | [1,1]³×[2·hminus,√8]³ | `eta_y y4 y5 y6 ² > 2` |
| 7 | `CJFZZDW` | :1479 | [1,1]³×[2·hplus,√8]×[2·hplus,√8]×[2,√8] | `eta_y y4 y5 y6 ² > 2` |

**tsk 组（10 条，tsk_hyp 序，merge_ineq.hl:1370-1377 字符串序）**：

| # | idv | ineq.hl 行 | 域 box | 结论 |
|---|---|---|---|---|
| 8 | `TSKAJXY-GXSABWC DIV` | :359 | [2.8²,8]×[4,2.01²]×[4,2.01²]×[2.8²,8]×[4,2.01²]×[4,2.01²] | `1/12 − (2·mm1/π)(sol_euler+345+156+246)_x_div_sqrtdelta − (8·mm2/π)(ldih2+3+5+6)_x_div_sqrtdelta_posbranch ≥ 0 ∨ delta_x < 0` |
| 9 | `TSKAJXY-delta_x4` | :341 | [4,2.01²]×[4,2.01²]×[2.8²,8]×[4,2.01²]×[4,2.01²]×[2.8²,8] | `delta_x4 … > 0` |
| 10 | `TSKAJXY-eulerA` | :324 | [2.8²,8]×[4,2.01²]×[4,2.01²]×[2.8²,8]×[4,2.01²]×[4,2.01²] | `eulerA_x … > 0` |
| 11 | `TSKAJXY-XLLIPLS` | :304 | [2·hplus,√8]×[2,2.01]×[2,2.01]×[2·hplus,2.8]×[2,2.01]×[2,2.01] | `gamma4fgcy … lmfun > 0` |
| 12 | `TSKAJXY-WKGUESB sym` | :281 | [2·hplus,√8]×[2.01,2·hminus]×[2,2·hminus]×[2·hplus,√8]×[2,2·hminus]×[2,2·hminus] | `gamma4fgcy … lmfun > 0 ∨ (y2<y3 ∨ y2<y5 ∨ y2<y6 ∨ y1<y4)` |
| 13 | `TSKAJXY-IYOUOBF sharp v2` | :242 | [2·hplus,√8]×[2,2.001]×[2,2.001]×[2,2·hminus]×[2,2.001]×[2,2.001] | `gamma4fgcy … lmfun ≥ 0` |
| 14 | `TSKAJXY-IYOUOBF sym` | :223 | [2·hplus,√8]×[2.001,2·hminus]×[2,2·hminus]×[2,2·hminus]×[2,2·hminus]×[2,2·hminus] | `≥ 0 ∨ (y2<y3 ∨ y2<y5 ∨ y2<y6)` |
| 15 | `TSKAJXY-RIBCYXU sym` | :183 | [2.001,2·hminus]×[2,2·hminus]⁵ | `> 0 ∨ (y1<y2 ∨ y1<y3 ∨ y1<y4 ∨ y1<y5 ∨ y1<y6 ∨ y2<y3 ∨ y2<y5 ∨ y2<y6)` |
| 16 | `TSKAJXY-RIBCYXU sharp` | :165 | [2,2.001]⁶ | `gamma4fgcy … lmfun ≥ 0` |
| 17 | `TSKAJXY-TADIAMB` | :127 | [2·hplus,√8]×[2·hplus,√8]×[2,√8]⁴ | `y_of_x rad2_x … > 2` |

**grk 组（2 条）**：注意**定义**在 ineq.hl（非 merge_ineq.hl）；任务背景给的
:4294/:4619 是 merge_ineq.hl 内的两个 `add_hyp ["GRKIBMP A V2"]` **消费点**
（`gamma23_full8_x_gamma` :4292-4312、`gamma23_keep135_x_gamma` :4617-4637），
本章程按下表校正锚点：

| # | idv | 定义（ineq.hl） | 域 box | 结论 |
|---|---|---|---|---|
| 18 | `GRKIBMP A V2` | **:1520-1535** | [2,2·hplus]×[1,1]⁵ | `y_of_x (gamma2_x1_div_a_v2 (h0cut y1)) y1 1 1 1 1 1 > 0.008`（"gamma2 ≥ 0.008 per azim along critical edge"） |
| 19 | `GRKIBMP B V2` | **:1537-1552** | [2·hplus,√8]×[1,1]⁵ | `y_of_x (gamma2_x1_div_a_v2 0) y1 1 1 1 1 1 ≥ 0`（"gamma2 nonnegative in general"） |

19 条之外的同库条目（如 `JSPEVYT` :1496、`IXPOTPA` :1266、`ZTGIJCF4` 生成族
16 条、`QITNPEA` 族等）属"其余 62 条"，本章不材料化（§2.0 路线 A′），PA25 的
`IXPOTPA/TXQTPVC/TEWNSCJ_MERGED`、`JSP_BOUNDS`、`leaf_CIHTIUM` 等将来填证时
从挂账叶取（§6.3、§6.4）。

### 1.3 分发器 — cell3_from_ineq_thm 与 GRKIBMP

**`add_hyp`**（merge_ineq.hl:53-56）：`add_hyp s concl = (∧_{t∈s} Ineq.getexact t.ineq) → concl`
——分发器的标准"从银行按名抽条目做前提"形态。

**cell3 件**：
- `cell3_from_ineq`（**语句**，merge_ineq.hl:**3446-3451**；TSKAJXY2.hl:61-70 同文）：

```ocaml
let cell3_from_ineq = `!y4 y5 y6.
   &2 <= y4 /\ &2 <= y5 /\ &2 <= y6 /\
    y4 <= &2 * sqrt(&2) /\ y5 <= &2 * sqrt(&2) /\ y6 <= &2 * sqrt(&2) /\
    eta_y (y4) (y5) (y6) < sqrt(&2) ==>
    &0 <= gamma3f y4 y5 y6 sqrt2 lmfun `;;
```

- `cell3_hyp`（merge_ineq.hl:**3490-3495**）= 上表 1-7 的合取；
- `cell3_from_ineq_thm`（merge_ineq.hl:**3507**，`mk_imp(cell3_hyp, cell3_from_ineq)`，
  证明体 ~240 行至 :3745）。证明 = 9 段 COMMENT 轨道：1 remove excess variables
  （`ineq_constant` :3428 削 y1-y3=√2 常量段）→ 2 insert Q → 3 remove eta_y
  （`eta_y_nn` :3452 + `ETA_Y_BOUNDS` :3223 把 `eta_y² > 2` 析取支杀死）→
  4 remove dih_4（`dih_y_div_sqrtdelta_pos` :3264）→ 5 make strict / insert
  h0cut y4∈{1,0}, y5, y6（`Optimize.h0cutA` :138 / `h0cutB` :146 分支替换）→
  7 gamma3f（`gamma3f_gamma3f_x_div_sqrtdelta` :3292）→ 8 symmetry reduction
  （`gamma3f_sym` :3354 + `Collect_geom.ETA_Y_SYYM` + `REAL_WLOG_SIMPLEX_3d`
  :3412）→ 9 2hminus < y4 收尾。变体 `cell3_from_ineq_thm_ALT`（:3746）；
- `eta_y_nn`（:3452-3462）：`0 ≤ ups_x … → 0 ≤ eta_y …`（sqrt 单调 + 积非负）。

**GRKIBMP 件**：
- `GRKIBMP_concl`（merge_ineq.hl:**3788-3790**；TSKAJXY2.hl:73-75 同文）：

```ocaml
let GRKIBMP_concl =
  `!y. &2 <= y /\ y <= sqrt8 ==>
     &0 <= gamma2_x_div_azim_v2 (h0cut y) (y* y)`;;
```

- `GRKIBMP`（merge_ineq.hl:**3794-3816**）= `add_hyp ["GRKIBMP A V2"; "GRKIBMP B V2"] GRKIBMP_concl`。
  证明 ~20 行：两银行条目对 `y2..y6 := 1` 实例化 → 展开 `Sphere.ineq`/`y_of_x`/
  `Functional_equation.nonf_gamma2_x1_div_a_v2` → 按 `2·hplus ≤ y` 分支：
  长边侧 `h0cut y = 0`（`Optimize.h0cutB` :146 + `Nonlinear_lemma.h0_lt_hplus`），
  短边侧 A 条目直接给 > 0.008（临界边侧），REAL_ARITH 收拢。
- `gamma2_x_div_azim_v2`（nonlin_def.hl:341-343；TSKAJXY3.hl:2065-2068 同文副本）
  与 `gamma2_x1_div_a_v2`（nonlin_def.hl:346-347，`= promote1_to_6 …` 六元提升）。

### 1.4 依赖件

| 件 | HOL 锚点 | Lean 现状 |
|---|---|---|
| `h0cut` | sphere.hl:**517** `h0cut y = if y <= 2*h0 then 1 else 0`（pack_defs.hl 同族） | ✅ PA21:**136**（同体） |
| `h0`/`hplus`/`hminus` | sphere.hl:**203**/**515**/**529**（pack_defs.hl:149/:132/:153） | ✅ PA2:**458**/:431/:468（hminus = `Classical.epsilon`） |
| `lfun`/`lmfun`/`mm1`/`mm2` | sphere.hl:**525**/**523**；pack_defs.hl:130-131 | ✅ PA2:461/:464/:425/:428 |
| `Optimize.h0cutA`/`h0cutB`/`h0cutC` | optimize.hl:**138**/**146**/**159** | ❌ 未移植（= if 展开两引理，机械） |
| `Functional_equation.nonf_gamma2_x1_div_a_v2` | functional_equation.hl:**1237-1244**（funext + promote1_to_6） | ❌ 未移植 |
| `gamma2_x1_div_a_v2` | nonlin_def.hl:346-347 | ❌ 未移植（6 元提升 def，~6 行） |
| ineq-演算族（~200 行） | `ineq_APPEND` :377、`ineq_pathL_pathR` :413、`ineq_critical_edge` :1606、`ineq_branch_edge` :1627、`ineq_branch_2hmin` :1939、`ineq_T` :1964、`ineq_MP` :1976、`ineq_CONJ` :1991、`ineq_af` :2007、`ineq_monotone` :2023、`ineq_constant` :3428、`ineq_branch_edge_strict` :3470、`ineq_critical_edge2/3/4` :4672/:4703/:4751、`ineq_mp_simple` :5642；tactics `CHOP_LIST_TAC`/`BRANCH_TAC(_STRICT)`/`CRIT4_TAC`、`SPLIT_H0_TAC`（optimize.hl:155-176） | ❌ 未移植（箭头形下大部分退化为平凡蕴含组合，见 §6.2 决策） |
| `eta_y`/`eta_x`/`ups_x` | sphere.hl:**131-135**/**127-129**/**122-124** | ⚠️ PA21:**131** `eta_y := sorry`；忠实体已在 `IneqClosureDefs.lean:620 etaY`（经 :606 etaX）+ `upsX`（SphereKit:72） |
| `ETA_Y_BOUNDS` | merge_ineq.hl:**3223-3253**（[2,√8]³ ∧ eta_y<√2 → 0 < ups_x ∧ 0 < delta_x 2 2 2） | ❌ |
| `ETA_Y_LE_IMP_LT_ALL` :3214、`UPS_X_POS` :2917、`cell_3_delta_x_eta_x` :2873、`lmfun_h0cut` :2889、`y_bounds` :3810、`gamma3f_sym` :3354、`REAL_WLOG_SIMPLEX_3d` :3412、`gamma3f_gamma3f_x_div_sqrtdelta` :3292、`dih_y_div_sqrtdelta_pos` :3264 | merge_ineq.hl | ❌ |
| `Flyspeck_constants.bounds`、`Nonlinear_lemma.sqrt8_sqrt2`/`sqrt2_sqrt2`/`hminus_lt_h0`/`h0_lt_hplus`/`hminus_prop`、`Collect_geom.ETA_Y_SYYM` | Flyspeck_constants / Nonlinear_lemma / Collect_geom | ❌（常数算术，2.01 ≤ 2·1.26 = 2.52 < 2·hminus < 2·hplus = 2.6508 < √8·… 数值级） |
| `gamma3f_x_div_sqrtdelta` | functional_equation.hl:**1252-1265**（`constant6`/`scalar6`/`mk_456` 算子组合） | ❌ def 本体；**算子 kit 已备**：IneqClosureDefs:273-371（`constant6`/`compose6`/`mk456`/`scalar6`/`uni`/`dummy6`/`projX*`/`projY4-6`） |
| `dih4_x_div_sqrtdelta_posbranch` | nonlin_def.hl:163-164 | ✅ IneqClosureDefs:**127** `dih4XDivSqrtdeltaPosbranch` |
| `ldih2/3/5/6_x_div_sqrtdelta_posbranch`、`sol_euler_x_div_sqrtdelta`(+345/156/246) | nonlin_def.hl:144-158/:115-128 | ✅ IneqClosureDefs:136-162/:173-202 |
| `eulerA_x` | sphere.hl:**830-833**（= `solEulerXDivSqrtdelta` 的 let-`a`，IneqClosureDefs:171-172 注记） | ❌ def（~10 行，材料可抄 :173-176） |
| `delta_x4` | sphere.hl:110 | ✅ SphereKit:**78** `deltaX4` |
| `rad2_x`/`rad2_y` | sphere.hl:271-273 / y_of_x | ✅ `rad2X` IneqClosureDefs:**628**（真体）；`rad2YP25` PA25:91 为 sorry 桩（§6.3） |
| `y_of_x` | sphere.hl:538 | ✅ SphereKit:**118** `yOfX` |
| `gamma4fgcy`/`gamma3f`/`dih_y` | sphere.hl:566/582/159 | ✅ PA20:117/:134、SphereKit:103 `dihY` |

### 1.5 消费端（Lean 侧锚点）

```
TSKAJXY3.hl:2240-2249  tsk_required_ineq（19 键字符串清单）
TSKAJXY3.hl:2251-2258  TSKAJXY 语句（pack_nonlinear_non_ox3q1h /\ … ==> gammaX ≥ 0）
TSKAJXY3.hl:2262-2274  0/3/4 臂：:2265 EVERY(map get_pack_nonlinear_non_ox3q1h) 逐条抽取
                       → :2268 MATCH_MP Merge_ineq.GRKIBMP + :2270 cell3_from_ineq_thm
                       → :2272 TSKAJXY_statement_special_case 收
TSKAJXY3.hl:2275-2283  1-cell 臂 TSKAJXY_1 / 2-cell 臂 TSKAJXY_2
TSKAJXY2.hl:61-70/73-75/77-78/80-88/92  cell3_from_ineq / GRKIBMP_concl /
                       tsk_hyp_new / TSKAJXY_statement_special_case(new_definition) /
                       TSKAJXY_034（~600 refinement 步至 :722）

Lean 现状（PackingAuto21.lean，下称 PA21）：
PA21:118-121  gamma2_x_div_azim_v2        ✅ 忠实（nonlin_def.hl:341-343）
PA21:131      eta_y := sorry              ❌ body 缺（PA25:160 记载在案）
PA21:136      h0cut                       ✅ 忠实
PA21:142      tsk_hyp := sorry            ❌ 不透明（HOL = 10 条合取，:1370-1377）
PA21:147      pack_nonlinear_non_ox3q1h := sorry  ❌ 不透明银行
PA21:163-166  cell3_from_ineq（Prop def）  ✅ 语句忠实（无需证明）
PA21:169-173  GRKIBMP_concl / tsk_hyp_new ✅ 语句忠实
PA21:177-185  TSKAJXY_statement_special_case ✅；TSKAJXY_034 :184 sorry
PA21:1382-1385 TSKAJXY_2（2-cell 臂）     sorry（不在本章范围）
PA21:1407-1428 TSKAJXY capstone：1/2-cell 臂已接（:1419/:1425）；
               0/3/4 臂 :1426-1428 = 注记 + sorry（本章收口目标）
PA25:3704     PACKING_CHAPTER_MAIN_CONCLUSION 内
              `exact TSKAJXY V X hnl hs hp hm hcrit`（唯一链上消费点）
```

---

## §2 陈述补丁草案（STATEMENT-FIX 地盘，只写草案不执行）

### 2.0 路线裁决矩阵

| 路线 | 内容 | 裁决 |
|---|---|---|
| A. 同名换体 + 全 81 条查表注册 | `BankEntry : String → Prop` 模式匹配 81 键，`pack_nonlinear… := ∀ id ∈ packNonlinearNonOx3q1hIds, BankEntry id` | 否决（本轮）：62 条陈述须同批誊写（含 ZTGIJCF4 生成族 16 条），且 `CertifiedIneqHolds`（Assembly.lean:170 PLACEHOLDER(G4)）语义未冻结，过早钉死形态有返工风险；留给 G4 主案一次性接线（IdLists:673 注记的 IneqPilot 样板） |
| **A′. 同名换体 + 19 切片材料化 + 62 条单叶挂账** | 三组显式合取（cell3 7 + tsk 10 + grk 2）+ `pack_nonlinear_rest := sorry` 单叶 | **采纳**。收口只需 19 条可投影；62 条不假装存在（诚实挂账，债务 -1 净减）；PA25:3704 零适配（§2.3） |
| B. 同名换体为纯 19 条合取（无 rest） | `:= cell3_bank ∧ tsk_bank ∧ grk_bank` | 否决：Assembly.lean:197-199 `TheNonlinearInequalities` 第一分量语义从 81 条缩水到 19 条；PA25 的 `IXPOTPA/TXQTPVC/TEWNSCJ_MERGED`、`JSP_BOUNDS`、`leaf_CIHTIUM` 等消费的条目在 62 条内，其未来填证将拿不到前提 |
| C. 新名 `NewBank` + 过渡桥 | PA21 内新 def，旧名 `:= NewBank` 转发 | 否决：纯增名；桥本身无信息量（同名换体已自动桥接，§2.3）；徒增 §3 波及面 |

合取**顺序**与 HOL 银行的 Ineq 前插序（IdLists:36-39）不同（本章按
cell3/tsk/grk 消费组排布）——合取交换律下无语义差，作为折算点登记
（statement-fidelity 附录惯例，§4 验收第 8 条）。

### 2.1 eta_y body 材料化（先行微补丁，可独立落地）

HOL 原文（sphere.hl:122-135）：`ups_x x1 x2 x6 = −x1²−x2²−x6²+2x1x6+2x1x2+2x2x6`、
`eta_x x1 x2 x3 = sqrt((x1·x2·x3)/ups_x x1 x2 x3)`、`eta_y y1 y2 y3 = eta_x (y1²) (y2²) (y3²)`。
Lean 忠实体**已存在**：`IneqClosureDefs.lean:606 etaX` + `:620 etaY`（带
rfl 数值阀），PA21 已 import 该模块的依赖闭包且**无环、无名冲突**（实测：
IneqClosureDefs 仅 import {SphereKit, PackingAuto2}，不 import PA21；
`etaX/etaY/sqrt8/sqrt2/matan/rotate*/aSpine5` 等名字在 PA21 依赖闭包内无占用，
PA4 的 `aSpine5P4` 为 private 异名）。

```diff
 --- a/lean/Kepler/Text/PackingAuto21.lean
 +++ b/lean/Kepler/Text/PackingAuto21.lean
+import Kepler.Text.IneqClosureDefs
 import Kepler.Text.Polytope        -- （既有 import 块内按字母序插入）
 
-/-- HOL `eta_y` (sphere.hl): the 3-leg auxiliary entering
-`cell3_from_ineq`.  The upstream body is not among local sources (use
-sites pin it only through that statement, whose consumers are sorried);
-opaque constant of the right type. -/
-noncomputable def eta_y (y4 y5 y6 : ℝ) : ℝ := sorry
+/-- HOL `eta_y` (sphere.hl:131-135): `eta_x` at squared lengths, i.e.
+`sqrt(x1*x2*x3/ups_x …)`（忠实体 = `IneqClosureDefs.etaY`，单一来源）. -/
+noncomputable def eta_y (y4 y5 y6 : ℝ) : ℝ := etaY y4 y5 y6
```

连带（纯注释，两处行号陈旧）：`IneqClosureDefs.lean:579` 与 `:618` 的
"PackingAuto21.lean:177" 应为 ":131"。落地即解锁 PA25 的 ETA_Y_* 填证队列
（`RADV_ETAY` :825、`ETA_Y_POS_LE_ALT` :2808、`ETA_Y_LEMMA` :2813、
`ETA_Y_LEMMA_ALT` :2819、leaf-chord 族 :2879-2880、JSP 族 :3569/:3587/:3602）
——该队列不属本章，随填随销。

### 2.2 银行结构化主补丁（19 切片材料化，PA21:138-147 换体）

命名规约：条目 def 前缀 `bank_` + idv 的去空格连写；docstring 携带 HOL idv
字符串与 ineq.hl 行号。三组合取 def 镜像 HOL `cell3_hyp`（merge_ineq.hl:3490）、
`tsk_hyp`（:1370）、`add_hyp ["GRKIBMP A V2"; "GRKIBMP B V2"]`（:3795）。

```lean
/-! ## Merge_ineq 银行（19 条 TSKAJXY 切片，MERGE-INEQ 波 0） -/

/-- HOL ineq 条目 `QZECFIC wt0`（ineq.hl:1372）。域 [1,1]³×[2.01,2hmin]×[2,2hmin]²。 -/
def bank_QZECFICwt0 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 1 ≤ y1 → y1 ≤ 1 → 1 ≤ y2 → y2 ≤ 1 → 1 ≤ y3 → y3 ≤ 1 →
    2.01 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus → 2 ≤ y6 → y6 ≤ 2 * hminus →
    0 < yOfX (gamma3fXDivSqrtdelta 1 1 1) y1 y2 y3 y4 y5 y6
/-- …（bank_QZECFICwt0corner :1389、bank_QZECFICwt0sqrt8 :1406、bank_QZECFICwt1 :1425、
   bank_QZECFICwt2A :1443、bank_CIHTIUM :1462、bank_CJFZZDW :1479 同构，box 与结论
   按 §1.2 表逐字；析取支 `∨ eta_y y4 y5 y6 ^ 2 > 2` 照抄）… -/
/-- HOL ineq 条目 `TSKAJXY-GXSABWC DIV`（ineq.hl:359）。x-空间条目（变量即平方长）。 -/
def bank_TSKAJXYGXSA : Prop :=
  ∀ x1 x2 x3 x4 x5 x6 : ℝ, 2.8^2 ≤ x1 → x1 ≤ 8 → 4 ≤ x2 → x2 ≤ 2.01^2 → … →
    1/12 - (2 * mm1 / Real.pi) *
        (solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 + solEuler345XDivSqrtdelta …
          + solEuler156XDivSqrtdelta … + solEuler246XDivSqrtdelta …)
      - (8 * mm2 / Real.pi) *
        (ldih2XDivSqrtdeltaPosbranch … + ldih3… + ldih5… + ldih6…) ≥ 0
      ∨ deltaX x1 x2 x3 x4 x5 x6 < 0
/-- …bank_TSKAJXYdx4 :341、bank_TSKAJXYeulerA :324、bank_TSKAJXYXLLIPLS :304、
   bank_TSKAJXYWKGUESBsym :281、bank_TSKAJXYIYOUOBFsharpv2 :242、
   bank_TSKAJXYIYOUOBFsym :223、bank_TSKAJXYRIBCYXUsym :183、
   bank_TSKAJXYRIBCYXUsharp :165、bank_TSKAJXYTADIAMB :127（rad2 侧 =
   `yOfX rad2X … > 2`，rad2X = IneqClosureDefs:628）… -/
/-- HOL ineq 条目 `GRKIBMP A V2`（ineq.hl:1520）。 -/
def bank_GRKIBMPAV2 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 ≤ y1 → y1 ≤ 2 * hplus → 1 ≤ y2 → y2 ≤ 1 → … →
    0.008 < yOfX (gamma2x1DivAV2 (h0cut y1)) y1 y2 y3 y4 y5 y6
/-- HOL ineq 条目 `GRKIBMP B V2`（ineq.hl:1537）。 -/
def bank_GRKIBMPBV2 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 → … →
    0 ≤ yOfX (gamma2x1DivAV2 0) y1 y2 y3 y4 y5 y6

/-- HOL `cell3_hyp`（merge_ineq.hl:3490-3495）。 -/
def cell3_bank : Prop :=
  bank_QZECFICwt0 ∧ bank_QZECFICwt0corner ∧ bank_QZECFICwt0sqrt8 ∧
    bank_QZECFICwt1 ∧ bank_QZECFICwt2A ∧ bank_CIHTIUM ∧ bank_CJFZZDW
/-- HOL `tsk_hyp`（merge_ineq.hl:1370-1377）。 -/
def tsk_bank : Prop :=
  bank_TSKAJXYGXSA ∧ bank_TSKAJXYIYOUOBFsharpv2 ∧ bank_TSKAJXYIYOUOBFsym ∧
    bank_TSKAJXYRIBCYXUsharp ∧ bank_TSKAJXYRIBCYXUsym ∧ bank_TSKAJXYTADIAMB ∧
    bank_TSKAJXYWKGUESBsym ∧ bank_TSKAJXYXLLIPLS ∧ bank_TSKAJXYdx4 ∧
    bank_TSKAJXYeulerA
/-- HOL 银行条目 `GRKIBMP A V2` ∧ `GRKIBMP B V2`（add_hyp 序，:3795）。 -/
def grk_bank : Prop := bank_GRKIBMPAV2 ∧ bank_GRKIBMPBV2

/-- HOL 银行其余 62 条（IdLists.lean:43-126 之差集：JSPEVYT、IXPOTPA、TXQTPVC、
TEWNSCJ、QITNPEA 族、ZTGIJCF0/4 生成族、GCKBQEA、RQWUDDU、6096597438、
1965189142 等）。PLACEHOLDER(G4)：随 CertifiedIneqHolds 填实拆单叶。 -/
def pack_nonlinear_rest : Prop := sorry -- MERGE-INEQ: 62-entry remainder, G4/P6-E

/-- HOL `pack_nonlinear_non_ox3q1h`（merge_ineq.hl:118-122）。结构化形态：
19 条 TSKAJXY 切片（§1.2 表）+ 62 条挂账叶；与 81 条全库合取相差
"顺序重排 + rest 合并"，折算登记见 §4 验收第 8 条。 -/
def pack_nonlinear_non_ox3q1h : Prop :=
  cell3_bank ∧ tsk_bank ∧ grk_bank ∧ pack_nonlinear_rest

/-- HOL `tsk_hyp`（PA21 旧体 `sorry` → 真体）。 -/
def tsk_hyp : Prop := tsk_bank
```

配套新 def（§1.4 缺口件，随波 0/2 落地）：

```lean
/-- HOL `gamma2_x1_div_a_v2`（nonlin_def.hl:346-347）：六元提升。 -/
noncomputable def gamma2x1DivAV2 (m : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 _x2 _x3 _x4 _x5 _x6 => gamma2_x_div_azim_v2 m x1   -- promote1_to_6
/-- HOL `gamma3f_x_div_sqrtdelta`（functional_equation.hl:1252-1265）：
constant6/scalar6/mk_456 算子组合（算子 kit = IneqClosureDefs:273-371）。 -/
noncomputable def gamma3fXDivSqrtdelta (m4 m5 m6 : ℝ) : ℝ → … → ℝ := …（逐字誊写）
/-- HOL `eulerA_x`（sphere.hl:830-833）。 -/
noncomputable def eulerAX … := …（= solEulerXDivSqrtdelta 的 let-`a`，:173-176 可抄）
```

**投影引理组**（收口专用，禁裸 `.1.2` 位置链，见 §6.5）：

```lean
theorem proj_cell3_bank (h : pack_nonlinear_non_ox3q1h) : cell3_bank := h.1
theorem proj_tsk_bank   (h : pack_nonlinear_non_ox3q1h) : tsk_bank   := h.2.1
theorem proj_grk_bank   (h : pack_nonlinear_non_ox3q1h) : grk_bank   := h.2.2.1
```

陈述冻结核对：所有 19 条陈述 = §1.2 表的逐字镜像（box 端点、不等号向、
析取支一个不少）；19 条之外零新增陈述性内容（新增 def 均为函数体誊写）。

### 2.3 PA25 适配判定：**可免（diff 为空）**

逐条论证：
1. **类型不变**：PA25:3704 `exact TSKAJXY V X hnl hs hp hm hcrit` 中
   `hnl : pack_nonlinear_non_ox3q1h` 的类型是常量 `Kepler.Text.pack_nonlinear_non_ox3q1h`
   本身；换体（def body 替换）不改变该常量的类型 `Prop`，应用处的 elaboration
   与 defeq 检查均不展开 body——typecheck 自动保持。PA21:1382（TSKAJXY_2）、
   :1407（TSKAJXY）的参数同理。
2. **无展开点**：全库 grep `unfold pack_nonlinear|unfold eta_y|unfold tsk_hyp|
   rw [pack_nonlinear|eta_y|tsk_hyp]` = 0 命中；`pack_nonlinear_non_ox3q1h` 的
   全部 76 处消费（PA21 3 + PA25 ~70 + PackingConcl 1 + Assembly 2）均为
   假设位/参数位/合取项位，对 body 透明。
3. **PA25 侧逐点核查**：~70 处 `hnl` 反 Palatino 前提（行号表见 §3）零改动；
   `PACKING_CHAPTER_MAIN_CONCLUSION`（PA25:3692-3704）的注释（:3685-3691
   "the bank antecedent … exactly this theorem's hnl"）继续成立；
   PackingConcl.lean:499-505 `OXLZLEZ V (by sorry) (by sorry) hp hs` 的
   `by sorry` 供给零改动。
4. **间接影响只向好**：PA25 各 sorry 定理将来填证时，`hnl` 可提供的条目信息
   从"无"（opaque）变为"19 条可投影"（其余仍 rest 挂账）——只会更易，不会破坏。

若审定者仍要求显式桥（例如为 G4 镜像粘合预留），最小桥为一组
`theorem bank_entry_iff_CertifiedIneqHolds_<i> : bank_<name> ↔ CertifiedIneqHolds "<idv>"`
（占位语义下左右皆平凡，G4 填实后逐条替换），随 §2.2 落地，不影响 PA25。

### 2.4 收口步形态（波 3 目标代码，预置于此供审定）

```lean
    · -- the 0/3/4-cell arm（PA21:1426-1428 现状 sorry 的替换体）
      have hgrk : GRKIBMP_concl := GRKIBMP (proj_grk_bank hnl)
      have hc3  : cell3_from_ineq := cell3_from_ineq_thm (proj_cell3_bank hnl)
      exact TSKAJXY_034 ⟨hgrk, hc3, proj_tsk_bank hnl⟩
```

（`tsk_hyp_new := GRKIBMP_concl ∧ cell3_from_ineq ∧ tsk_hyp`（PA21:173）与
`tsk_hyp := tsk_bank`（§2.2）defeq，匿名构造器直接可用；HOL 对应
TSKAJXY3.hl:2263-2273。）

---

## §3 波及面清单（全库 grep 实测；"零改动" = 该消费点不需要任何编辑）

### 3a. `pack_nonlinear_non_ox3q1h`

| 消费点 | 位置 | 形态 | 判定 |
|---|---|---|---|
| def 本体 | PA21:144-147 | `def … : Prop := sorry` | **换体**（§2.2 主补丁） |
| TSKAJXY 参数 | PA21:1407 | `(hnl : …)` | 零改动 |
| TSKAJXY_2 参数 | PA21:1382 | `(hnl : …)` | 零改动 |
| PA25 前提位（~70 处） | PA25:1788, 2119, 2171, 2200, 2241, 2256, 2301, 2695, 2714, 2732, 2747, 2763, 2780, 2796, 2826, 2840, 2854, 2898, 2907, 2916, 2943, 2953, 2964, 2975, 3004, 3015, 3026, 3042, 3059, 3069, 3082, 3095, 3108, 3121, 3151, 3171, 3190(leaf_CIHTIUM), 3251(gamma4fgcy_POS), 3263, 3279, 3295, 3311, 3330, 3345, 3361, 3374, 3387, 3395, 3404, 3414, 3431, 3445, 3462, 3474, 3486, 3497, 3508, 3517(JSP_BOUNDS), 3525, 3537, 3561(IXPOTPA_MERGED), 3578(TXQTPVC_MERGED), 3596(TEWNSCJ_MERGED), 3613, 3624, 3636, 3648, 3658, 3674(OXLZLEZ), 3693(PACKING_CHAPTER_MAIN_CONCLUSION) | `(hnl : …)` | 零改动（§2.3） |
| PA25:3704 | PACKING_CHAPTER_MAIN_CONCLUSION 收口行 | `exact TSKAJXY V X hnl …` | 零改动（本章关键约束，已证可免） |
| PackingConcl | PackingConcl.lean:49（注记）、:497-505（`OXLZLEZ_concl_discharged` 的 `by sorry` 供给） | 假设供给 | 零改动 |
| Assembly | Assembly.lean:154（六分量注释）、:193（真化注记）、:197-199（`TheNonlinearInequalities` 第一分量） | 合取项 | 行零改动；语义注记：81 ↔ (19+rest) 折算入 §4 验收第 8 条 |
| IdLists | IdLists.lean:42-128（81 条清单 + rfl） | 数据注册表 | 零改动；G4 接线桥 = §2.3 尾注 |

### 3b. `eta_y`

| 消费点 | 位置 | 判定 |
|---|---|---|
| def 本体 | PA21:127-131 | **换体**（§2.1 微补丁） |
| cell3_from_ineq 内 | PA21:166 | 零改动（defeq 重指向自动生效） |
| PA25 `RADV_ETAY` | PA25:825-826 | 零改动；body 落地解锁其填证 |
| PA25 mcell2 域族 | PA25:1781, 2194 | 零改动 |
| PA25 `ETA_Y_POS_LE_ALT`/`ETA_Y_LEMMA`/`ETA_Y_LEMMA_ALT` | PA25:2808-2809/:2813-2815/:2819-2821 | 零改动；解锁 |
| PA25 leaf-chord 族 | PA25:2879-2880 | 零改动；解锁 |
| PA25 JSP/leaf 族 | PA25:3569, 3587, 3602 | 零改动；解锁 |
| IneqClosureDefs | :579/:618 注释（"PA21:177" 陈旧） | **注释行号修正**（:131），随 §2.1 |
| IneqClosureDefs `etaY` | :606-623 | 零改动（成为单一权威体） |

### 3c. `tsk_hyp` / `tsk_hyp_new` / 周边语句件

| 消费点 | 位置 | 判定 |
|---|---|---|
| `tsk_hyp` def | PA21:138-142 | **换体**（`:= tsk_bank`，§2.2） |
| `tsk_hyp_new` | PA21:172-173 | 零改动（`GRKIBMP_concl ∧ cell3_from_ineq ∧ tsk_hyp` 形态不变） |
| `TSKAJXY_034` | PA21:182-185 | 零改动（陈述冻结；证明体留波 2/3 消费） |
| `TSKAJXY_statement_special_case` / `cell3_from_ineq` / `GRKIBMP_concl` | PA21:175-170 | 零改动 |
| PA25:45 注记 | PA25 头部 ENCODING NOTES | 零改动（"opaque"措辞在波 0 落地后由文档轮更新，非闸门项） |
| `tsk_required_ineq` | PA21:1390-1399 | 零改动（文档性清单，与 bank 组序对照） |

### 3d. 新增面（波 0 唯一结构性新增）

- PA21 import 块 +1 行：`import Kepler.Text.IneqClosureDefs`（无环实测：
  IneqClosureDefs 仅 import {SphereKit, PackingAuto2}；PA21 已 import SphereKit，
  atn2 冲突无新增）；名字冲突 grep 实测 0（`etaX/etaY/sqrt8/sqrt2/matan/
  rotate2-6/aSpine5/bSpine5/projX*/projY*` 在 PA21 依赖闭包无占用）。
- §2.2 的 19 条目 def + 3 组 def + rest 叶 + 投影引理 3 枚；§2.1 尾注两处注释修正。

---

## §4 闸门规程与执行顺序

### 4.1 机制

- **波 0 = STATEMENT-FIX**：`GATE_MODE=STATEMENT-FIX` + `SF_PATCH`
  （补丁存档 `docs/statement-fix-proposals-patches/MERGE-INEQ-bank.patch`）+
  `SF_ITEM=merge-ineq-bank`（本章程）；同时在 `docs/statement-fix-proposals.md`
  增提案条目（内容 = §2.1 + §2.2，状态"章程已审定待执行"）。
- **波 1/2/3 = 普通填证**（五道闸标准流程），分别在 PA21 内完成。

### 4.2 执行顺序（对应 playbook §5.4 收口路径）

1. **波 0（陈述级，先行止血）**：§2.1 eta_y 重指向 + §2.2 银行结构化 +
   §2.4 注释修正 + PA21 内预置 `GRKIBMP`/`cell3_from_ineq_thm` 两枚
   `sorry -- MERGE-INEQ: <HOL 锚点>` 骨架（不接 :1428，防假绿）。
   落地同日：DEBT.md 刷新（净变化见 4.3）、statement-fidelity 折算登记
   （合取顺序 + rest 挂账 + `gamma3fXDivSqrtdelta` 等 def 的算子折算）。
2. **波 1（GRKIBMP 移植，机械档，预估 ~50-80 行）**：h0cutA/B（if 展开）、
   `gamma2x1DivAV2` + `nonf_gamma2_x1_div_a_v2`（funext/rfl）、
   `bank_GRKIBMPAV2/BV2` 投影、常数算术（`h0_lt_hplus`：2.52 < 2.6508 数值；
   `norm_num` 亲和）→ `GRKIBMP` 真体（HOL :3794-3816 逐段）。
3. **波 2（cell3_from_ineq_thm 移植，GIANT，切两子波）**：
   - **2a（kit 波，~400 行）**：`gamma3fXDivSqrtdelta` def、`eulerAX` def、
     `eta_y_nn`（:3452）、`UPS_X_POS`（:2917）、`cell_3_delta_x_eta_x`（:2873）、
     `ETA_Y_BOUNDS`（:3223）、`ETA_Y_LE_IMP_LT_ALL`（:3214）、
     `dih_y_div_sqrtdelta_pos`（:3264）、`gamma3f_gamma3f_x_div_sqrtdelta`
     （:3292）、`gamma3f_sym`（:3354）、`REAL_WLOG_SIMPLEX_3d`（:3412）、
     `lmfun_h0cut`（:2889）、`y_bounds`（:3810）、常数性质 kit
     （hminus ∈ [1.2,1.3)、hminus < h0、2.01 ≤ 2·h0 等）；
   - **2b（主定理波，~500 行）**：9 段 COMMENT 轨道逐段（§1.3）；
     ineq-演算不整体移植（§6.2），按箭头形逐处退化为 `impl` 组合。
4. **波 3（收口机械步）**：PA21:1426-1428 替换为 §2.4 的三行 `exact`；
   `TSKAJXY` 的 `#print axioms` 应仅剩经 `pack_nonlinear_rest` 与 19 条
   银行叶（若走假设化则无）+ TSKAJXY_034 上游的 sorryAx——注意本章收口后
   该臂的直接 sorry 归零，透传债 = TSKAJXY_034（:184，仍是独立大件）+ 19 条
   银行叶（G4 级）。
5. **收尾**：playbook §5.4 PA21 条改写（"三重阻断"→"波 0 已落地/分发器已
   移植"）、e2e-debt-map B 表该行更新、DECISIONS 追加闭环注记。
   项目关闭条件 = :1428 离账 + 波 0 台账三件套完成（TSKAJXY_034 本体与
   19 条证书真化分属 TSKAJXY_034 专项与 G4 主案，不在本章关闭判据内）。

### 4.3 验收清单（闸门逐道）

1. **逐字一致性**（波 0）：工作区 diff 与 SF_PATCH 逐行多重集一致；
2. **陈述冻结**：19 条陈述逐条对照 §1.2 表（box 端点数值、不等号向、
   析取支完整；x-空间条目变量名 x 不换 y）；三语句件
   （`cell3_from_ineq`/`GRKIBMP_concl`/`TSKAJXY_statement_special_case`）
   与 `TSKAJXY_034`/`TSKAJXY`/`TSKAJXY_2` 陈述行零改动；
3. **名字存在性**：新增 def 引用的每个名字
   （`etaY/upsX/deltaX/deltaX4/yOfX/gamma3f/gamma4fgcy/dihY/lmfun/lfun/mm1/mm2/
   h0/hplus/hminus/solEuler*Posbranch/ldih*/dih4XDivSqrtdeltaPosbranch/rad2X/
   constant6/scalar6/mk456/uni/compose6`）已在依赖闭包（§1.4 表逐项）；
4. **波及面核对**：diff 触及的名字 ∈ §3 清单，超出即拒（防借道夹带）；
5. **构建绿**：`lake build Kepler.Text.PackingAuto21` 及下游
   （PA25 → Assembly 收官根）0 error；
6. **sorry 台账**：波 0 净变化 = `tsk_hyp`/`pack_nonlinear_non_ox3q1h`/`eta_y`
   三枚 def-sorry 消失，新增 `pack_nonlinear_rest` 1 枚 + `GRKIBMP`/
   `cell3_from_ineq_thm` 2 枚骨架 = 净 +0（3 消 3 增，全部带
   `-- MERGE-INEQ:` 标签可追溯）；波 1 消 1（GRKIBMP）、波 2 消 1
   （cell3_from_ineq_thm）、波 3 消 1（:1428 臂）；
7. **PA25 回归**：PA25 构建绿 + PA25:3704 应用 typecheck（§2.3 论证的机器
   落点）；PackingConcl 构建绿；
8. **折算登记**（statement-fidelity 附录）：①合取顺序 81 前插序 → 消费组序；
   ②62 条并入 `pack_nonlinear_rest` 单叶（G4 拆单叶的既定路线）；
   ③`gamma3fXDivSqrtdelta` 等 def 的 constant6/scalar6 算子折算
   （IneqClosureDefs batch-2 已定的"算子保留"口径）；
9. **章程附录联动**：波 0 落地后把 §2.2 的 19 键 ↔ IdLists 序对照表补进
   IdLists.lean 头注（纯注释），供 G4/mqmsmab 复用。

---

## §5 与 MQMSMAB 通道的合流评估

**共同点**：两章同属"非线性不等式注册表忠实化"——把 Lean 侧的弱编码占位
换成与 HOL Ineq 数据库逐条对账的真形。对象分别是 packing 侧
`pack_nonlinear_non_ox3q1h`（本章，PA21 def 重打型 + 分发器移植）与 tame 侧
`kcblrqc_ineq_def`（mqmsmab，Assembly.lean:**189** `KcblrqcIneqDef := True`
占位 → TameLp.lean:**510** 四切片真形重指向；见 docs/mqmsmab-scout.md §6.1
Step 0）。

**机制差异**（合流成本的核心）：

| 维度 | 本章（MERGE-INEQ） | MQMSMAB Step 0 |
|---|---|---|
| 现状形态 | opaque `sorry` Prop（结构未知） | `True` 占位（结构已知，真形已在 TameLp:510-532） |
| 动作 | 重打型 + 19 条陈述新材料化 + 两个分发器移植（GIANT） | 一行 def 重指向 + 一行 import（分钟级） |
| 收口判据 | PA21:1428 `exact` 臂 | mqmsmab 定理（TameLp 侧）直通 |
| 对 CertifiedIneqHolds(G4) | 19 键桥表（§2.3 尾注）为 G4 接线样板第一块 | 同一 G4 主案的另一分量 |

**交汇点仅两处，均无语义耦合**：
1. **Assembly.lean 同文件触碰**（本章 :197-199 语义注记 vs mqmsmab :189 def
   替换）：零共同 def、零共同证明件，纯 commit 卫生问题 → 排序建议：两章
   各自独立 commit，mqmsmab Step 0 无须等待本章任何波（反之亦然）；
2. **远期 G4 主案**：两章产物都汇入 `CertifiedIneqHolds` 查表填实
   （IdLists 六清单 + `certifiedIneqHolds_pilot` 样板，IdLists:673）。

**建议：分立立项，不合章。** 理由：①本章 GIANT 波 2 是周级工作量，不应
阻塞 mqmsmab 的分钟级 Step 0；②两章的审定对象不同（本章审定 19 条陈述
逐字镜像 + PA25 免适配论证；mqmsmab 审定重指向一行），绑章会让两套审定
互相拖累（同 planar-encoding-fix §4.3 的"分开 commit"理由）；③共用基础设施
（G4 查表、桥表格式）通过 §4.3 验收第 9 条的附录联动解决，无需章级合并。
若编排者希望统一节奏：唯一硬约束是 **mqmsmab Step 0 与本章波 0 不放同一个
commit**（同文件）。

---

## §6 风险清单

1. **junk 口径**：
   - 十进制字面量：HOL `#2.01/#2.001/#2.8/#0.008` = 十进有理数；Lean 侧
     `2.01` 等浮点字面量在 ℝ 上即 `201/100` 精确值（of_scientific），无 junk；
     `#2.8 pow 2` 写 `(2.8 : ℝ)^2`（= 196/25 = 7.84 < √8² = 8，box 端点核对）；
   - `√8`/`√2`：IneqClosureDefs.sqrt8/sqrt2（:585/:588）与 PA2 内联
     `Real.sqrt 8` 同体（defeq），波 0 选定 `Real.sqrt 8` 内联形（与 PA21/PA25
     现行风格一致）并登记；
   - **hminus 的 choice 语义**：PA2:468 `Classical.epsilon`（sphere.hl:529
     `@x. …` 同构）。box 端点含 `2·hminus` 的条目（wt0/wt1/wt2/CIHTIUM/
     RIBCYXU sym/IYOUOBF*）与波 1/2 的常数事实依赖 hminus 的性质
     （`1.2 ≤ hminus < 1.3`、`hminus < h0`、`marchalQuartic hminus = lmfun hminus`）
     ——Nonlinear_lemma 的对应件未移植，波 2a 需补"epsilon 选出的点满足
     谓词"引理（`Classical.epsilon_spec` + 谓词非空的存在性由
     marchal_quartic 连续性/介值给出——**这是波 2a 唯一非机械点**，HOL 侧
     `hminus_prop` 的对应存在性论证要逐字核对；若介值论证超预算，备胎 =
     对 hminus 的三条性质按 Flyspeck_constants 口径作为已证小簇单独填证）；
   - `h0cut` 的 if 体在 `y = 2·h0` 点取 1（`≤` 侧）——与 PA21:136 一致，
     波 1 的 `h0cutA/h0cutB` 分支边界按此钉死。
2. **`ineq` 包装钉死**：HOL `ineq`（sphere.hl:27-29）是 `≤` 的 list-record
   包装（`ineq ((a,x,b)::xs) c <=> a ≤ x ∧ x ≤ b → ineq xs c`，空表恒等）。
   **Lean 侧决策：不移植包装，条目直接展为箭头形**（§2.2 的
   `∀ y1 … , a1 ≤ y1 → y1 ≤ b1 → … → concl`）——理由：包装只有两个消费者
   （条目注册与演算引理），箭头形下 `ineq_monotone`/`ineq_T`/`ineq_MP`/
   `CHOP_LIST_TAC`/`BRANCH_TAC` 全部退化为平凡蕴含运算（`imp_refl`/`fun h => …`
   级），整体移植是负资产。此决策与 IneqClosureDefs batch-2 的"算子保留、
   命题层坍缩"（IneqClosureDefs:217-230）精神一致，登记折算。
   `all_forall` 闭包序：6 变元条目按 `y1..y6`（x-空间按 `x1..x6`）排，与
   HOL 排序后 frees 一致，无观测差。
3. **19 条的 Lean 同义件覆盖度（grep 全树实证 = 0/19）**：没有任何一条
   以独立定理存在。近邻辨析：PA25 `leaf_CIHTIUM`（:3190）是消费 `hnl` 的
   叶子级应用定理，**不是** CIHTIUM 本体；PA25 `IXPOTPA/TXQTPVC/TEWNSCJ_
   MERGED`（:3561/:3578/:3596）是三个**库内其余条目**（62 条成员，非 19 切片）
   的 merged 推论，其未来填证将向 `pack_nonlinear_rest` 取前提——即 rest 叶
   最终必须由 G4 拆单，路线已定（§2.0 A′）；PA25 `JSP_BOUNDS`/`JSPEVYT_
   EXPLICIT`（:3517/:2119）同理（JSPEVYT ∈ 62）。
   **已备 kit**（§1.4 表）：19 条所需的全部函数件在树内（SphereKit/PA2/PA20/
   IneqClosureDefs），def 缺口仅 4 个小件（`gamma3fXDivSqrtdelta`、`eulerAX`、
   `gamma2x1DivAV2`、`rad2_y` 可 `yOfX rad2X` 内联）+ 常数算术 kit（§6.1）。
4. **银行口径 81 vs 19**：任务背景"19 条合取"已按 §1.1/§1.2 精确化。若审定
   者要求一步到位的全 81 注册形态（路线 A），§2.0 给出改道判据——届时波 0
   体量 ×4，且与 G4 主案合并执行，:1428 收口排期相应后移。
5. **位置投影脆弱性**：`hnl.2.2.1` 型裸投影对合取布局敏感；收口与后续填证
   一律走 §2.2 具名投影引理（`proj_cell3_bank` 等），闸门第 4 条可机检
   （diff 内禁新增 `.1.2.1` 链）。
6. **文档行号陈旧**：IneqClosureDefs:579/:618 引 "PackingAuto21.lean:177"
   实为 :131（波 0 顺带修）；PA25:46 "TSKAJXY <-> PackingAuto21:1114" 实为
   :1407（非闸门项，文档轮统一）。
7. **收口后的剩余债边界**（防"收口=通道结束"误读）：:1428 离账后 TSKAJXY
   链仍透明的债 = `TSKAJXY_034`（PA21:184，~600 步 GIANT，独立专项）+
   19 条银行叶（G4 级证书）+ `pack_nonlinear_rest`（G4）；本章关闭判据按
   §4.2 第 5 条，不以 sorryAx 清零为判据。
8. **行数预估不确定性**：波 2b 的"9 段轨道"中第 8 段（`REAL_WLOG_SIMPLEX_3d`
   对称归约，HOL :3690-3710 一带）在 Lean 无现成 wlog 基建，可能需手写
   6 变元置换 case binge（预估 +100-200 行）；波 2a 的 hminus 存在性论证
   见 §6.1 备胎。两处均建议单独 checkpoint，证出即交付不留半成品。

---

## 附：编排者审定意见（2026-09-29）

**结论：章程审定通过**，附两条执行条件：

1. **§2 路线 A′ 批准**（同名换体 = 19 切片材料化 + `pack_nonlinear_rest := sorry`
   62 条单叶挂账）——承重论证 §2.3（PA25 适配可免）复核无异议：换体不改常量
   类型、全库零展开点、76 处消费点逐条透明；§2.4 收口步形态与 PA21 侦察
   （playbook §5.4）完全一致。`pack_nonlinear_rest` 必须以 `-- NEEDS: G4 主案`
   注记入 DEBT 台账，不得无账。
2. **§5 合流裁决采纳**：与 MQMSMAB 分立立项；两者同落 Assembly.lean，
   硬约束"不进同一 commit"由编排者在闸门排队时保证。

执行授权待项目 owner 拍板（周级 GIANT 投入）；波 0（eta_y 一行重指向，
STATEMENT-FIX，分钟级）与波 1（GRKIBMP ~50 行机械）可在批准后立即发车，
波 2（GIANT ~900 行）建议等 Graphs 链收官、本机核数回笼后再开。
