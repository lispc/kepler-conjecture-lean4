# statement-fidelity.md — 陈述保真度对照（Phase 1 交付）

目的（PLAN.md §4 Phase 1）：论证 `lean/Kepler/Statement.lean` 中的
`Kepler.the_kepler_conjecture` 与 Flyspeck 的 `the_kepler_conjecture`
语义一致，防止"证错了定理"。

对照基准：`reference/flyspeck` @ `1ce0353`
`text_formalization/general/the_main_statement.hl:19-24`：

```
the_kepler_conjecture <=>
  (!V. packing V
         ==> (?c. !r. &1 <= r
                      ==> &(CARD(V INTER ball(vec 0,r))) <=
                          pi * r pow 3 / sqrt(&18) + c * r pow 2))
```

本项目（`lean/Kepler/Statement.lean`）：

```lean
theorem the_kepler_conjecture :
    ∀ V : Set Space3, Packing V →
      ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
        ((V ∩ Metric.ball 0 r).ncard : ℝ) ≤
          Real.pi * r ^ 3 / Real.sqrt 18 + c * r ^ 2
```

## 逐项对照

| Flyspeck (HOL Light) | 本项目 (Lean 4) | 说明 |
|---|---|---|
| `V : real^3 -> bool` | `V : Set Space3`，`Space3 := EuclideanSpace ℝ (Fin 3)` | HOL Light 的 `real^3` 即带欧氏度量的 ℝ³；Mathlib 的 `EuclideanSpace ℝ (Fin 3)` 是其标准模型，`dist` 同为欧氏距离。唯一表示差异，无语义差别。 |
| `packing V`（`general/sphere.hl:425`） | `Packing V` | 逐字相同：`∀ u v ∈ V, dist u v < 2 → u = v`（单位球心两两距离 ≥ 2）。 |
| `CARD (V INTER ball (vec 0, r))` | `(V ∩ Metric.ball 0 r).ncard` | 两者对无限集都约定为 0；在 `Packing` 假设下该集合必有限（见下），此时两者都等于真实计数。 |
| `&(CARD ...)` | `((...).ncard : ℝ)` | 自然数到实数的强制转换。 |
| `ball (vec 0, r)` | `Metric.ball 0 r` | 均为**开**球。 |
| `pi * r pow 3 / sqrt(&18)` | `Real.pi * r ^ 3 / Real.sqrt 18` | HOL 的 `sqrt(&18)` 是实数开方；`Real.sqrt 18`（`18 : ℝ`）相同。 |
| `?c. !r. &1 <= r` | `∃ c : ℝ, ∀ r : ℝ, 1 ≤ r` | 量词顺序与约束相同；`c` 均无符号约束。 |

## 有限性补注

HOL Light 的 `CARD` 与 Lean 的 `Set.ncard` 对无限集均返回 0。
在 `Packing V` 下 `V ∩ ball 0 r` 必为有限集——`Kepler.Packing.finite_inter_ball`
已给出**完整证明**（无 sorry）：球心两两距离 ≥ 2 ⇒ 半径 1 的开球两两不交
且全部落入 `ball 0 (r+1)`，体积计数给出 `(T.card : ℝ) ≤ (r+1)³`。
因此两个系统中的计数都等于真实球心数，无"无限集退化为 0"的语义陷阱。

## 与 Flyspeck 另一形态的关系

`text_formalization/packing/pack_defs.hl:24` 另有一个体积比形态
`kepler_conjecture`（含 `saturated V` 与球体积比），Flyspeck 用
`kc_imp_the_kc`（`the_main_statement.hl:82-107`）由它推出计数形态。
Flyspeck 最终审计（`general/audit_formal_proof.hl:49`）以计数形态
`the_kepler_conjecture` 为终点定理，本项目与之对齐。

## 结论

除 `real^3` ↔ `EuclideanSpace ℝ (Fin 3)` 这一标准表示差异外，
陈述逐项对应；无常数篡改（`π`、`√18`、指数 3、2、阈值 `1 ≤ r` 均一致）。
已知偏差：无。

---

## 附录：Phase 6 装配脊柱的折算点（2026-09-19，P6-B 复审登记）

`Kepler/Assembly.lean`（设计 `docs/phase6-spine.md`）的接口陈述经 P6-B 逐条
对照 HOL 原文复审通过。以下折算点已知晓并记录，消除接口 sorry 时必须随附补证：

1. **`the_nonlinear_inequalities` 量化折算**（用户批准 2026-09-19）：HOL 的 993 条
   字面合取 → Lean 的"ID 清单（数据）+ `AllCertified` 量化命题"。**当前六个 ID 清单
   为空、`CertifiedIneqHolds := True` 占位**——脊柱冻结的是形状；填实由 G4 负责，
   届时每条 ID 到字面不等式的映射表本身也是保真对象，须逐条抽查。
2. **`FAN 0 V (ESTD V)` 显式前提**：HOL `hypermap_of_fan` 为全函数，Lean
   `hypermapOfFan` proof-parameterized；消 LP 接口 sorry 时需补
   `Contravening V → FAN 0 V (ESTD V)`（surrounded_node 合取项给出）。
3. **dart 编码差**：Lean 用 `dart1OfFan`（不含孤立 dart），HOL 用 `dart_of_fan`；
   Contravening 语境下无孤立点，两编码一致，消 sorry 时补证。
4. **`IsHypermapOfList` 规格级镜像**：`hypermap_of_list` 的构造属 P6-C；
   落地后须证 `IsHypermapOfList L (hypermapOfList L)` 并展开回 HOL 原句。
5. **镜像语义**：`iso_fgraph`（允许镜像，improper）与 HOL 一致；hypermap 层
   `Iso` 保定向——两层之间必须是 ELLLNYZ 形析取桥（镜像分支走镜像 fan 绕行：
   `hypermap_of_fan_neg` + `contravening_negative`），属 Phase 5 capstone 内部债务。
6. **`CARD`/`sum` 的无限集约定**：均取 0，与 HOL 垃圾值约定一致。

---

## 附录 B：六 ID 清单的构造折算（2026-09-20，P6-E 接口侧登记）

`lean/scripts/gen_idlists.py` 把 HOL 的六件生成式合取翻译为六张 ID 清单
（产物 `lean/Kepler/Assembly/IdLists.lean`，对应 Assembly.lean:171-183 六个
PLACEHOLDER 字段）。以下折算点均已登记并附生成期校验（脚本 `validate` /
`cross_check_json`，任一失败即拒产）：

1. **注册表重建口径**：`!Ineq.ineqs` 的全部注入点只有
   `nonlinear/ineq.hl` 与 `nonlinear/main_estimate_ineq.hl`
   （全库 `Ineq.add` 扫描；`optimize.hl:35` 绑定 `add` 但从不调用；
   `prep.hl:14-16` 用独立注册表 `Prep.prep_ineqs`，745 条 `prep-` 案例
   **不进**任何分量清单）。`Ineq.add` 前插（ineq.hl:39-42），故内存序 =
   逆文本序；载入序 ineq.hl 先于 main_estimate_ineq.hl
   （`build/build.hl:86-87`）。清单顺序按此重建（无语义影响，仅为逐项
   对照可审计）。
2. **程序化记录的机械展开**（OCaml 循环/函数应用逐条展开，带源行）：
   ineq.hl `make_F4` 循环 16 条（`ZTGIJCF4 …`）、`add_QITNPEA1` 循环 6 条、
   `mk_3q1h_all` 230 条、`mk_iqd` 6 条（`181212899 d`）、`iqd` 17 条、
   命名记录 `add i4750199435;;` 等 6 条；main_estimate_ineq.hl `make_hex_ear`
   循环 35 条（`7550003505 i j k`）。`skip {…}` 块（ineq.hl 8 处、
   main_estimate_ineq.hl 8 处）与 ineq.hl:2620 注释掉的 `(* add *)` 块
   **不计入**注册表。
3. **每分量的标签→清单过滤规则**（逐条翻译，源行见 IdLists.lean 头注释）：
   `pack_nonlinear_non_ox3q1h` = Flypaper ∩ {UKBRPFE,BIEFJHU,OXLZLEZ,TSKAJXY}
   非空且 idv 无 "OXLZLEZ 6346351218" 前缀（merge_ineq.hl:98-116，81 条）；
   `ox3q1h` = "OXLZLEZ 6346351218 i n"（i∈0..4，n∈0..45，**定义序** n 主 i 次，
   merge_ineq.hl:78-92，230 条）；`main_nonlinear_terminal_v11` = Main_estimate
   标签（terminal.hl:24-44，109 条）；`lp_ineqs` = Lp/Tablelp/Lp_aux 标签或
   idv="6170936724"，剔除 deprecated_quads（the_main_statement.hl:29-45，
   127 条）；`pack_ineq_def_a` = Flypaper ∩ {UKBRPFE,WAZLDCD,BIEFJHU} 非空
   （YSSKQOY.hl:24-28，5 条）；`kcblrqc_ineq_def` = Flypaper ∩ {KCBLRQC} 非空
   或 idv ∈ extra_ids（3+quad_idv 17），剔除 deprecated_quads
   （tame_lemmas-compiled.hl:34-46，28 条）。
4. **deprecated_quads 剔除**（tame_lemmas-compiled.hl:6-13，6 条）：
   非平凡——其中 4 条（`3862621143 revised`、`4240815464 a`、`6944699408 a`、
   `7043724150 a`）带 Lp/Tablelp 标签，不剔除就会进 lp_ineqs（实测 131→127）；
   生成期 assert 钉死"剔除后六条均不在 lp_ineqs / kcblrqc_ineq_def"。
5. **`"6170936724"` 特例**：其标签为 Cfsqp/Xconvert/Tex/Penalty，无 Lp 系
   标签，仅靠 the_main_statement.hl:39 的 `ineq_ids` 硬编码进 lp_ineqs；
   生成期 assert + Lean 侧位置式成员钉子（IdLists.lean 末节）。
6. **terminal.hl 的 `hd (Ineq.getexact t)` 重解析**（terminal.hl:33）在
   id 唯一时是恒等映射：实测注册表 547 条记录无重复 idv（生成期 assert），
   故 ID 清单不受 `getexact` 影响。
7. **lp_ineqs 的 `setify` 是项级去重**（the_main_statement.hl:43）：HOL 合取
   项数 ≤ ID 数（若两条 id 的字面项相同，HOL 合取只留一项）。Lean 注册表
   量化按 ID 计，语义强度不降（同一项证两遍等价于证一遍）；消接口 sorry 时
   若需逐项对齐 HOL 合取，按此折算说明。
8. **交叉校验**：ineq.hl 字面记录解析与 g4e pipeline `ineqs.json`（独立
   解析器）逐 id 对齐——176 个唯一 id 集合相等、标签名逐 id 相等；非
   skip/orphan 的 JSON id 全部落入注册表。
9. **外部锚点**：`kcblrqc_ineq_def` 过滤结果与 mk_all_ineq.hl:119-125 的
   硬编码 `kcblrqc_ineq_s`（28 条，`nonlinear_imp_the_nonlinear_inequalities`
   证明实际消费）集合相等（生成期 assert）；`ox3q1h` 230 条与
   merge_ineq.hl:22-24 的 "5*46 / 230 inequalities" 注释对齐。其余分量
   HOL 侧无数量注释，记实测值。
10. **每分量 3 条手工抽查**（2026-09-20，与 HOL 原文逐条目检）：
    pack_nonlinear——`TSKAJXY-DERIVED`（ineq.hl:96-120，Flypaper
    ["OXLZLEZ";"TSKAJXY"] ✓）、`QITNPEA1 1 0 9063653052 A`（ineq.hl:845-862
    循环模板，Flypaper["OXLZLEZ"] ✓）、`6096597438 b`（ineq.hl:1661-1663，
    Flypaper["UKBRPFE"] ✓）；ox3q1h——`OXLZLEZ 6346351218 0 0` / `0 23` /
    `4 45`（ineq.hl:1563-1577 sprintf 模式 + merge_ineq.hl:78-92 ✓）；
    main——`2125338128`（main_estimate_ineq.hl:1948-1952，Main_estimate ✓）、
    `7550003505 1 1 1`（hex_ear 循环模板，Main_estimate ✓）、`4717061266`
    （ineq.hl:1698-1711，Main_estimate ✓）；lp_ineqs——`6184614449`
    （main_estimate_ineq.hl:1067-1070，Lp_aux+Tablelp ✓）、`7761782916`
    （ineq.hl:3081-3084，Lp ✓）、`JNTEFVP 1`（ineq.hl:1755-1760，Lp_aux+
    Tablelp ✓）；pack_ineq_def_a——`6096597438 b`（UKBRPFE ✓）、`8055810915`
    （ineq.hl:1634-1636，WAZLDCD ✓）、`1965189142 34`（ineq.hl:1587-1589，
    BIEFJHU ✓）；kcblrqc——`6184614449`、`8425800388`、`JNTEFVP 1`
    （均 ∈ quad_idv extra_ids ✓，且集合级锚点见折算 9）。
11. **数量口径勘误**：Assembly.lean:152 与 docs/phase6-spine.md:20,43,59 的
    "993 条"说法在 HOL 源中无对应数量注释；按上述规则实测六分量合计
    **580 条 ID**（分量间有重叠；去重并集 539，注册表总 547）。580 与
    "993" 的差距未在 HOL 侧找到解释——本附录以实测值为准；Assembly.lean
    本体注释的修正留待接口解封时一并处理（本次按任务约束不改本体）。
12. **ox3q1h 数据状态更正**：STATUS.md:92 的"ineqdata3q1h.hl 7 条
    Mathematica record 未解析"有误——实测 `raw_nonlindatah` 为 **46 条**
    record（生成期由源文件机械计数，与 merge_ineq.hl "5*46" 注释一致）。
    46 条 record 的**内容**解析仍是 Phase 4 债务，但 ID 清单只依赖
    `Printf.sprintf "OXLZLEZ 6346351218 %d %d"` 的机械 idv（ineq.hl:1570），
    故 230 条 ID 可先填实，不等待 record 解析。
