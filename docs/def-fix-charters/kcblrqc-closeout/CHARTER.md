# 章程 · kcblrqc 收口（**非**语义 DEF-FIX；侦察先行）

立案：2026-11-09。立案人：编排者。触发：对 28 条 `kcblrqcIneqDefIds` 的资产盘点。
本文件的作用是**钉死裁定**，防止后续车道把 XL 批当成 kcblrqc 的前置。

---

## 1. HOL 锚

- `tame/ssreflect/tame_lemmas-compiled.hl:34-46`：
  `kcblrqc_ineq_tml = end_itlist mk_conj (map (λt. t.ineq) idl)`，
  `idl = filter (λt. t.idv ∉ deprecated_quads ∧ (KCBLRQC ∈ flypaper_ids t ∨ t.idv ∈ extra_ids)) !Ineq.ineqs`。
  ⇒ **`kcblrqc_ineq_def` 是 `!Ineq.ineqs` 的一个子集合取**（与 `lp_ineqs` 同表同构造）。
- 消费链：`CDTETAT.hl:179/306`、`MQMSMAB-compiled.hl:25`（`add_section_hyp "ineqs"`）。

## 2. Lean 现状（机器核实，2026-11-09）

| 事实 | 证据 |
|---|---|
| `kcblrqcIneqDefIds`(28) **⊂** `lpIneqsIds`(127) | 交集 = 28/28（脚本比对 `IdLists.lean:630` 与 `lpIneqsIds`） |
| 28 条全部解析到**真命题**（非 `True` 回落） | `lpIneqProp` 先判 `id ∈ lpIneqIds` → `lpIneqStatement_xxx` 查表 |
| `nliKcblrqcIneqDefIds : AllCertified …` **零消费者**、**不在 78 条锥内** | 全树 grep；`docs/e2e-reachability-map.tsv` `--- SORRIED ---` 段无此条 |
| 锥内只有 `nliKcblrqcIneqDef : KcblrqcIneqDef`（Assembly:1973 → 装配 :7112） | 同上 |
| `TameLp.KcblrqcIneqDef` 是**四类事实的消费切片** | `TameLp.lean:516`（含 docstring 四类：azim 双界 / b_tame r=0 / r>0 数值矛盾 / (5,0,1) 下界） |
| 切片**点名**的机器不等式只有 **`5490182221` + `5735387903`** | `TameLp.lean:505`；b_tame 各行以 `hmain : lp_main_estimate` 为假设，不直接取证书 |
| 这两个 id **都没有证书源** | `Kepler/Interval/Cases/` 无 `C5490182221*` / `C5735387903*` |
| 三棵 XL 树服务的是**别的 id** | `3253650737`/`8425800388`/`6078657299` ∈ 28 但不在切片点名集；11,714 模块 / 7.65M 行 / **olean 0** |
| SF-39 已于 2026-10-14 批准并应用 | `mqmsmabWired` 已取 `hkcblrqc : TameLp.KcblrqcIneqDef` |

## 3. 裁定

1. **不做语义 DEF-FIX。** `KcblrqcIneqDef` 保持 = `TameLp.KcblrqcIneqDef` 的转发；切片是**消费形**，注册表是**数据库形**，两者是"由数据库推消费形"的关系（定理），不是定义等价。
2. **XL 批与 kcblrqc 锥内项解耦。** 12–13 h 的 XL 重建只服务 3 个别的 id，**不在本锥项的路径上**；`AllCertified 28` 本身零消费者、不在锥内。
3. **唯一允许的定义侧改动（纯文档，零语义）**：清掉 `Assembly.lean:1967-1982` 的过时措辞（"PLACEHOLDER(P6-E)"、"Assembly §1c 同名占位（`True`）独立维持"——SF-39 应用后已不成立），并在 `TameLp.lean:516` docstring 补一句"本切片由 `5490182221`/`5735387903` + `lp_main_estimate` 推得，不依赖 XL 树"。

## 4. 执行路线（R1→R4）

- **R1 考古**：CDTETAT / KCBLRQC.vhl `lp_data` / BDJYFFB1/2 到底吃哪些机器 id（除点名的 2 个外，b_tame 表行是否另有直接取用的 id）。产出"最小 id 集"。
- **R2 证书**：只为 R1 的最小 id 集发射/生成证书（首选 bb_arb plain + stage-A 全量硬闸，沿用 BIEFJHU-a 的做法）。
- **R3 切片证明**：`KcblrqcIneqDef` 四个合取逐条证明（第 2–4 类走 `hmain : lp_main_estimate` 与常数算术，第 1 类走 R2 证书）。
- **R4 接线**：`nliKcblrqcIneqDef` 换真证；`#print axioms` 标准三；`sorry` 净减 1。

## 5. 禁止与闸门

- 禁止：跑 XL 批；新增 `axiom`/`sorry`/`native_decide`；改任何定理陈述；动 `AllCertified` 形状。
- 闸门：岛协议编译 RC=0；`#print axioms` 目标即标准三；`sorry` 计数净变 ≤ 0（本项预期 −1）；pit10 扫描零禁词。
- 回滚：R2 证书与 R3/R4 各自独立 commit，任何一个失败只回滚该 commit。

---

## 6. ERRATA（2026-11-09 18:55，`kcblrqc-w1` 侦察推翻本章程 §2/§3 的两处判断）

**本节的结论覆盖 §2/§3 的对应条目。原文保留不删（历史层纪律）。**

### 6.1 最小 id 集不是 2 条

- 切片类 1（azim 双界）真正要 **3 条**：`5735387903`（0.852 下界）、`5490182221`（1.893 上界）、**`2570626711`**（非三角 `1.15` 下界，经 `non_triangular_face_azim_dart_bound → DIH_Y_INEQ`，`Inequalities.hl:647`）。§2 只数了 `TameLp.lean:505` 点名的 2 条。
- **类 2–4 不能只靠 `hmain`**：HOL 20 个 r=0 行里 **17/20** 需要机器 ineq（仅 `(2,2)/(0,3)/(1,3)` 三行等于逐面 `d_tame` 和）；6 个 r>0 型与 `(5,0,1)` 行全要。反例：`b_tame(4,0)=0.347 > d_tame(4)=0.206`。
- HOL 忠实闭法的最小集 = **26 条**（10 直取 + 16 经 `quad_nonlinear_v10`），其中 **3 条是 XL**（`6078657299`/`8425800388`/`3253650737`，属 `Lp_details.quad_idv`(17) ⊂ `kcblrqcIneqDefIds`(28)）。**§3 第 2 条"XL 与本锥项解耦"只在字面切片类 1 上成立，对 HOL 忠实的类 2 不成立。**
- `2327525027` 在 28 里但 q3/q4 都不用。
- 已核：`mk_all_ineq.hl:119-125` 的 28-id 表与 `IdLists.lean:630-658` 逐字相同。

### 6.2 成本是实测的，且判 NOT FEASIBLE

| 项 | 数值 |
|---|---|
| bb_arb 裸叶数 | `5490182221` **1,354,264**；`2570626711` **1,880,802**；`5735387903` 撞 4M 节点上限 rc=2 ⇒ **≥~2M** |
| 合计 | **≥5.23M 叶** |
| 内核单价（atan/sqrt 档，非 poly） | **16.5 s/叶**（rung 128）– **51.5 s/叶**（hull decide） |
| 折算 | **≥0.55M–4.5M 核·分**（9k–75k 核·时）；**~10.8M 行 Lean**（2.06 行/叶） |
| 唯一有生产数据的 id | `549`：折叠池 165,219 叶已实测 **2,245 核·时 / 12.32 GB olean / 2.9 GB 源** ——仍是最初 XL 批（12–13 h）的 **~170 倍** |
| 证书现状纠正 | `C549*` 全是 pilot/sample（`C549ArcBatch` 142/160、`ProdK` 468/500、val1000 977/1000），**无全盒 covers**；`C2570626711p200` 是 279 叶子盒 sample。真正全量在库只有 `6184614449`(9,424 叶)、`JNTEFVP 1`(3,142 叶)、三棵 XL |

**判词：证书路线 NOT FEASIBLE。** §3 第 3 条"R3 类 2–4 走 hmain + 常数算术"作废；R3 前提若按证
书路线 = 26 张证书（不可行）。

### 6.3 决策点（编排者已上报用户，未决）

1. **(a) SF 结构**：把 28 条机器 ineq 以显式前提挂回切片 / `mqmsmab`（HOL 的 section hypothesis 形态）。
2. **(b) 26 张证书**：判 NOT FEASIBLE，不开波。
3. **(c) 原创路线重估**：Flyspeck 的 `prepared_nonlinear` 离线证明能否在 Lean 侧重放（AGENTS §8 原版对照），尚未评估。
4. 在裁决前：**kcblrqc 不再发任何证书/发射波**；`nliKcblrqcIneqDef` 保持 sorry，不动陈述。
