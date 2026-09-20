# 波2 disj+sqrt 家族设计（FillParams 扩 disj + repair hit 继承）

> 2026-09-19，Kimi。前置调研基于 wip/g4-emit @ `184d4a86`（含未提交 N=2048 改动），
> 行号引用以该树为准。目标：6 份 disj+sqrt 家族证书（79~83 sqrt 主 prog）的内核闭合通路。

## 1. 输入实测（决定设计形状的事实）

| cert | disj 数 | sqrt(主) | sqrt(disj 支) | atan(主) | 叶数 | hit 分布 |
|---|---|---|---|---|---|---|
| BIXPCGW_7274157868_a | 1 prog | 79 | disj0: **4 sqrt + 7 atan + 1 abs** | 143 | 70,870 | 全 `disj:0` |
| FHBVYXZ_a | 2 prog | 79 | disj1: 2 | 143 | 47,096 | 全 `disj:0` |
| FHBVYXZv2_a | 2 prog | 79 | disj1: 2 | 143 | 47,096 | 全 `disj:0` |
| GLFVCVK4_2477216213 | 2 prog | 79 | 0 | 143 | 205,418 | 全 `disj:0` |
| QITNPEA_2134082733 | 1 prog | 83 | 0 | 150 | 44,295 | 全 `disj:0` |
| QITNPEA_5400790175_a | 2 prog | 79 | disj1: 2 | 143 | 44,295 | 全 `disj:0` |

关键事实：

1. **六份证书全部叶 hit = `disj:0`**——主 prog（79~83 sqrt）从未被命中，
   var_lt 支也未被命中。bb_arb 是 first-hit-wins（`bb_arb.c:1100-1182`：主先试，
   不中才按序试 disj 支），hit 只是见证而非唯一成立支。
2. **被命中的 disj0 支除 BIXPCGW 外都是纯代数式**（无 sqrt/trans），
   唯一需要 FillParams 填参的命中支是 **BIXPCGW 的 disj0（4 sqrt + 7 atan + 1 abs）**。
3. **证书冗余**：FHBVYXZ_a / FHBVYXZv2_a（及 FHBVYXZ_b）cert 逐字节相同（仅 id 异）；
   QITNPEA_5400790175_a/_b 同理。6 份实际独立证书 **5 份**。但各 case 的 goals 列表
   内容不同（主 prog/disj 数不同），Lean 侧仍须逐 case 发射；disj0 支 prog 相同者
   params 可复用（优化项，非必须）。
4. 证书叶 JSON 只有 `{box, hit}` 两字段，无任何参数（参数全靠 FillParams 编译态重算）。
5. 主 prog 含 `ite`，disj 支不含。

## 2. 缺口定位（调研结论）

**缺口 (a) FillParams 不处理 disj 叶**：
- `emit_lean.py:700-704` die 点（`fill pipeline: disj cases unsupported`）；
- `CertDisj.lean:64-67` BBTreeD 叶 = `(box, k : Fin goals.length, hcert)`，
  表达式引用全局 goals，**没有逐叶参数槽位**（对照 `CertG.lean:36-38` 的
  `leaf box el hsame hcert`）；
- `build_goals`（`emit_lean.py:196-219`）用无参 v1 RPN，disj 支遇 sqrt/trans
  在 `RPN.emit_pair:291/298` die；
- `parse_params`（`:496-521`）假设每叶恰好 `2k` int、`k = count_op(case["prog"])`
  只数主 prog——多支各有 sqrt 数（BIXPCGW：主 79 / disj0 4），扁平行无支标签；
- stage-A 驱动 `fillMkExpr`（`:478-493`）是单表达式工厂。

**缺口 (b) repair 的 hit 继承**：
- `repair_leaves.py:129-130` die 点（注释已自认 hit inheritance is goal-specific）；
- 修复驱动只建主 prog expr（`:132-134`），PASS 判据 = 主 prog 填参后 lo>0——
  disj-hit 叶会全报 FAIL 无限二分；
- 子叶 hit verbatim 继承父（`:170-172`）——二分后成立支可变，错 hit 会被内核
  `decide` 拒收（sound 的失败模式但阻塞）。

**次要坑**：ladder 三处复制（FillParams.lean:171 / stagea_merge.py:21 /
params_merge.py:27）；BIXPCGW disj0 含 500 push_var，其 7 个 atan 多半含变量 →
走全局 rung 阶梯，阶梯顶 (128,-100) 可能不够（BESTFAIL 死路）；repair 走源码
字面量模式，大单可能撞 elaboration 瓶颈（数据文件模式 `runMainFile` 已就位未用）。

## 3. 设计决策

### D1：Lean 侧新结构 `BBTreeGD`（BBTreeG × BBTreeD 混合）

新文件 `lean/Kepler/Interval/CertGD.lean`：

```lean
inductive GDLeaf (n : ℕ) (goals : List (DisjGoal n)) where
  /-- pos 支：逐叶特化表达式 + rfl 语义桥（同 BBTreeG） -/
  | posLeaf (box) (k : Fin goals.length) (el : IExpr n)
      (hsame : el.evalReal = (goals.get k).expr.evalReal)  -- pos 支的 expr 投影
      (hcert : checkPos el box = true)
  /-- varLt 支：无参数，直接盒判定（同 BBTreeD 现形） -/
  | varLtLeaf (box) (k : Fin goals.length) (hcert : …check box = true)
```

- `DisjGoal` 需暴露 pos 支的 `expr` 投影（或给 `check`/`eval` 加引理层）。
- soundness `bb_sound_disj_g`：覆盖 + 根含目标 ⟹ `∃ g ∈ goals, g.eval ρ`，
  证明 = BBTreeG 的逐叶桥 + BBTreeD 的析取收束拼接，无新数学。
- `CertBool.lean` 加 `coversB` 的 GD 版本（整树覆盖一次内核 `decide`）。
- 对 varLt 叶不需要参数槽——两构造器分开比统一 dummy 更干净。

### D2：hit 在 stage-A 重算，repair 不继承（核心简化）

bb_arb 的 hit 只是"哪个支先中"的见证；内核只要求每叶给出**某个**成立支 + 证据。
因此：

- stage-A 驱动携带**全部** goals 表达式（主 + 各 disj prog），逐叶判定：
  按固定顺序（varLt 精确盒判定最先，便宜；然后各 pos 支填参求值）取首个成立支，
  输出 `i PASS <k> <params…>`。
- **repair 不再继承 hit**：失败叶二分后，子叶直接走同一个 stage-A 驱动重算 hit。
  这把缺口 (b) 化掉——hit 继承问题不存在，因为 hit 本来就是重算的。
  `repair_leaves.py` 只需：驱动构建从"只建主 prog"改为"建全 goals 驱动"，
  删除 `:129-130` 的 die 与 `:170-172` 的继承逻辑。
- 证书的 `"hit"` 字段降级为**提示/校验**：stage-A 重算结果可与原 hit 比对告警
  （不一致不阻塞，以重算为准——原 hit 是另一精度的见证，重算 hit 同样合法）。

### D3：params schema v2（带支标签）

```
RUNG <N> <out>            # 全局 rung 不变
<i> PASS <k> s1 t1 …      # k = 命中的 goal 下标；参数个数 = 2·sqrt数(goals[k])
<i> PASSV <k>             # varLt 命中，无参数
```

- `parse_params` 按 goals[k] 的 sqrt 数校验长度；主 prog 的 sqrt 槽位
  不再出现在每叶行里（主 prog 命中时 k=0，带主 prog 的参数——实测不会发生但结构支持）。
- 单一事实源：把 ladder + 各支 sqrt 数写进 stage-A 产出的 `manifest.json`，
  stagea_merge/params_merge 读 manifest，消除三处 ladder 复制（顺带修次要坑 1）。

### D4：stage-A 驱动多表达式化

- `stage_a_file` 接受 goals 列表：主 prog + 各 disj prog 各自 `fillMkExpr`
  （sqrt 槽位 dummy、open trans 走 rung、closed trans 固定 (2048,-64)）。
- FillParams.lean 加 `runMainDisj`：读盒 → 逐支判定（§D2 顺序）→ 打 hit+params。
  数据文件模式（`runMainFile` :281-291）优先，大单避免 elaboration 瓶颈（次要坑 7）。
- rung 裁定语义不变：全局 rung = 所有 pos 支（含主 prog 与 disj prog 支）
  统一阶梯 max。主 prog 虽未命中但仍在 goals 里——**主 prog 不参与 rung 裁定**
  （它不填参），rung 只对有命中 pos 支裁定；逐支各记 rung 或全局取 max 均可，
  取 max 简单（BIXPCGW 只有 disj0 一支有 open trans，实际就是它定 rung）。

### D5：发射与验证

- `emit_lean.py` 新增 `--bbg --disj-gd` 路径：goals 全发（含未命中支——
  goals 列表是命题骨架，必须全；未命中支的 sqrt 槽位用 dummy `(0,0)`，
  因为 soundness 不要求未命中支成立）。
  - 注意：未命中支带 dummy 参数也要能**编译**（表达式构造合法即可，
    `checkPos` 不会在这些支上被调用——hcert 只针对命中支的 el）。
- 叶发射：hit pos → `.posLeaf box k el hsame (by decide)`；hit varLt → `.varLtLeaf`。
- 根 + 覆盖 decide + 公理审计照旧（标准三 + 无新特许）。

### D6：批次顺序与复用

1. **BIXPCGW 先行**（唯一需要填参命中支，风险最高：7 atan 是否含变量决定
   rung 需求；若 (128,-100) 不够则扩阶梯——扩法 = FillParams.lean ladder 加档，
   manifest 化后只改一处）。70,870 叶规模友好。
2. QITNPEA_2134082733（44k，disj0 纯代数）——其实纯代数 disj0 走 v1 路径
   已可发射（C6078657299 先例：全 main-hit 纯代数 BBTreeD 已闭合）；
   **注意这类（5/6 份）可能不需要 BBTreeGD 也能闭合**：hit 支无参数需求时
   v1 BBTreeD 结构已够，缺口只在"发射端遇 disj 支 sqrt die"与 repair。
   策略：5 份纯代数 hit 的走 v1 修补路径（build_goals 对未命中含参支打 dummy +
   跳过 die），BIXPCGW 走 BBTreeGD。两条路径并存，BBTreeGD 是通用兜底。
3. 重复证书（FHBVYXZ_a/v2_a、5400790175_a/_b）：若 disj0 prog 逐字相同，
   stage-A params 可算一次复用（校验 prog hash 后拷贝），发射仍逐 case。

## 4. 工作量分解

| 步骤 | 内容 | 估计 |
|---|---|---|
| W0 | manifest 化（ladder/支参数数单一事实源）+ BIXPCGW disj0 atan 变量依赖性核实 | 0.5 天 |
| W1 | `CertGD.lean`：BBTreeGD + soundness + coversB（含 DisjGoal expr 投影引理） | 1-2 天（Lean 证明活） |
| W2 | FillParams.lean `runMainDisj` 逐支判定 + stage-A 多表达式驱动 | 0.5-1 天 |
| W3 | emit_lean.py：schema v2 解析、`--disj-gd` 发射、v1 路径 dummy 放行 | 0.5 天 |
| W4 | repair_leaves.py：全 goals 驱动 + hit 重算（删继承） | 0.5 天 |
| W5 | BIXPCGW 端到端（stage-A → merge → 发射 → 内核构建） | 1-2 天（含阶梯扩展风险） |
| W6 | 其余 4 份独立证书量产（v1 修补路径为主） | 1 天（机时为主） |

总计约 4-6 个工作日（穿插 549/2570626711 构建机时不冲突：均为轻编译 + 短内核）。
风险集中在 W5 的 rung 是否越顶；若越顶，阶梯每加一档 open-trans 叶内核成本
线性上升（N 翻倍 ≈ decide 时间翻倍），2048 档已在 closed 侧验证过可行。

## 5. 明确不做

- 不给主 prog 填参（79~83 sqrt 主支未命中，填了也没用；3112-sqrt 怪物案另行）。
- 不做"最优 hit"选择（first-pass-wins，与 bb_arb 同序但独立判定）。
- 不动已闭合的 8+ 案例与 Q/549 在制管线。

## 6. W0 实测结论（2026-09-20）

精确复刻 `emit_pair` 的 closed 语义（ite 三支独立栈、closed = 无 push_var）分析各 case
**被命中支 disj0**：

| case | disj0 atan | 含变量 | disj0 sqrt | 含变量 |
|---|---|---|---|---|
| BIXPCGW_7274157868_a | 7 | **3** | 4 | 4 |
| FHBVYXZ_a / FHBVYXZv2_a | 0 | 0 | 0 | 0 |
| GLFVCVK4_2477216213 | 0 | 0 | 0 | 0 |
| QITNPEA_2134082733 | 0 | 0 | 0 | 0 |
| QITNPEA_5400790175_a | 0 | 0 | 0 | 0 |

结论：
- D6 两路径策略成立——5 份命中支纯代数（v1 修补路径），仅 BIXPCGW 需 BBTreeGD。
- BIXPCGW disj0：4 sqrt 全含变量 → 逐叶 mantissa 槽位（每叶 8 int）；
  7 atan 中 4 个 closed → 固定 (2048,-64)，**3 个 open → 全局 rung 阶梯**。
  阶梯顶 (128,-100) 是否够由 stage-A 实测裁定（BESTFAIL 即扩档，只改 FillParams.lean
  一处 + manifest 同步）。

## 7. W2+W4 实施结论（2026-09-20，`bb87a1e0`）

落地：FillParams.lean `runMainDisj`/`runMainFileDisj`（逐支判定：varLt 盒判定优先，pos 支按序，
first-hit-wins）；emit_lean.py `fill_goals`/`stage_a_driver_disj` + manifest.json（schema v2，
ladder 单一事实源）；repair_leaves.py 删 hit 继承，子叶重算。549 全量重发射与在跑目录逐字节
一致（不回归已实证）。BIXPCGW pilot 20 叶：16 叶 PASS 1（hit 与原证一致，参数长度 ✓）。

**两个 W5 前置风险（实测坐实）**：
1. **深叶 BESTFAIL 与 N 无关**：4 个最深叶全档位 FAIL 且 best 停首档——瓶颈不是 open-atan
   阶梯，疑似 div/atan 的 out=-64 粒度在巨 mantissa 深盒的绝对误差。对策 = seeded repair
   二分（子叶更浅更松），W5 第一轮先验证可解性；不可解再诊断 evalFill 的 FAIL 区间来源。
2. **性能炸弹（W2.5 必修）**：每叶每档 ≈250s——主 prog（83 sqrt + 143 closed atan @N=2048）
   恒失败但 evalFill 全量求值，closed 子式叶间不变。70,870 叶 ≈ 单机 200+ 天，不可行。
   处方：stage-A 驱动对 **closed（var-free）子式做 chunk 级记忆化**（每 chunk 只算一次），
   或按 hit 分布裁剪主 prog（语义注意：hit 重算是权威判定，主 prog 理论上可能在个别叶
   成立，裁剪主 prog 会改变 hit 重算的语义完备性——优先记忆化，不裁剪）。
