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
