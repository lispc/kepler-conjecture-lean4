# TM1 进度笔记（多元 + div + BIXPCGW 失败叶实测）

> 接力记录。工作树 `/home/scroll/repos/kepler-g4e`（wip/g4-emit）。
> TM0 已合入（commit 456011b5 / 942f0df5），详见 tm0-progress.md。

## 0. 对齐与计划（2026-09-21）

TM0 的代数路线（∃a-Valid 纯代数合成）已是一般 n，g'' 债已化解。TM1 实际
剩余（按任务书修正版）：

1. evalTM 扩 div：商规则 f/g = f·(1/g)（`TaylorM.inv` 合成子 + `valid_inv`
   + `valid_div` = valid_mul ∘ valid_inv）。inv 余项初等推导：
   `1/s − 1/t = (t−s)/(s·t)` → `1/f(ρ) − 1/f(y) − q·Δf = Δf²/(f(ρ)·f(y)²)`，
   `q = −1/f(y)²`，`|·| ≤ W²/c³`，c = 盒上 |f| 的认证下界（正侧 fB.lo − W，
   负侧 −(fB.hi + W)，否则 none）。**无需 sqrtI 证书**——InvTMP 只有三个
   recip 粒度 o0（值 1/f(y) 的包围）/o1（斜率 1/f(y)²）/o2（曲率 1/c³）。
2. 参数结构改为 `TMParams := ⟨sqrtCerts : List SqrtTMP, invCerts : List
   InvTMP⟩`（同类节点各自按遍历序消费，避免 sum-type match 的证明痛苦）。
   CertG 的 taylorLeaf 与两个 TM0 pilot 随之迁移。
3. TMSafe 谓词（语法层：排除 abs/ite/trans；div/sqrt 语义安全由 Option 规则
   在求值时检查）。
4. 多元临界例（CertG 尾部 TM1 节）：
   - A（2D 依赖丢失）：`x·y − x − y + 1 + 1/64` 于 `[15/16, 17/16]²`——
     裸区间根盒 lo = w² − 4w + ε < 0 失败（O(w) 依赖误差），TM 根盒即闭合
     （err = w² = 1/256 < ε = 1/64）。实测对照断言：TM 根过 / 裸根不过。
   - B（3D + sqrt）：`√(x²+y²+1) − z` 于 `[−1/8,1/8]² × [7/8, 15/16]`——
     根盒 sqrt 证书粒度受限导致裸区间/TM 都失败，沿 z 二分一层闭合。
   - C（2D + div）：`x/(1+y) − 4/9` 于 `[1, 3/2]×[1/2, 1]`——根盒 TM 失败
     （线性项吞余量），沿 x 二分一层闭合，练 div 链。
5. BIXPCGW 失败叶实测：Repair 的 chunk 输出在
   `lean/Kepler/Interval/Cases/Repair/CRepair*.d/chunk*.txt`；驱动
   `driver.lean` + `FillParams.runMainFileDisj`。样本：repair round 1-2
   的 FAIL 盒 100-200 片，emit 一个小 probe 文件跑 checkPosTM 统计通过率。
   注意机时（27K-op 文件 elaboration 35-50min，样本控制规模）。

## 1. CertTM div 扩展（进行中）

（待填）

## 1. CertTM div 扩展（完成）

做了：`InvTMP`（o0/o1/o2 三个 recip 粒度，无 sqrt 证书）、`TMParams :=
⟨sqrtCerts, invCerts⟩`（同类节点各自按遍历序消费）、`TaylorM.invCore`/`inv`
（c := fB.lo − W 正侧 / −(fB.hi + W) 负侧，皆不然 none）、`valid_invCore`
（初等恒等式 1/s − 1/t = (t−s)/(s·t)，余项 Δf²/(fρ·fy²) ≤ W²/c³）、
`valid_inv`（两侧符号分情形）、`valid_div`（= valid_mul ∘ valid_inv，
div_eq_mul_inv）；evalTM 加 div 臂（ps₂.invCerts.head? 消费），
evalTM_sound 加 div case；checkPosTM 签名迁到 TMParams；新增
`IExpr.TMSafe`（语法层排除 abs/ite/trans）。CertG 两个 TM0 pilot 迁移到
TMParams（exGTMP := ⟨[⟨2,2,2,−3,−2⟩], []⟩；exTM2 用 .empty）。

验证：`lake build Kepler.Interval.CertTM` 绿（8662 jobs）；`lake env lean
CertG.lean` 零错误，三条 #print axioms 仍仅标准三（回归无恙）。

注意：lake env lean 用的是已构建 olean——改 CertTM 后必须先 lake build
CertTM 再 lean CertG，否则看到旧签名（踩过一次）。

下一步：多元临界例（2D 依赖丢失 / 3D+sqrt / 2D+div），scratch 迭代证书，
然后 BIXPCGW 失败叶实测。

## 2. 多元临界例（进行中）

（待填）

## 2. 多元临界例 + hybrid 回退（完成）

CertG 三个多元 pilot（全部内核闭合 + #print axioms 仅标准三）：
- A（2D 依赖丢失）：`x·y − x − y + 1 + 1/64` on `[15/16,17/16]²`：
  `exTM1A_bare_root`（裸区间根盒 false，O(w) 依赖误差 w²−4w+ε）/
  `exTM1A_cert`（TM 根盒即闭合：中心梯度为零，err = w² = 1/256 < 1/64）。
  单叶 taylorLeaf，end-to-end `0 < x*y − x − y + 1 + 1/64`。
- B（3D + sqrt）：`√(x²+y²+1) − z` on `[−1/8,1/8]²×[7/8,15/16]`：
  `exTM1B_bare_root` false（根盒 sqrt 证书粒度 ⌊√62⌋=7 @2⁻³ 太粗），
  TM 根盒单叶闭合（证书 ⟨16,16,31,−4,−12⟩：√(256·2⁻⁸) → 16，
  √(248·2⁻⁸) → 31；**mantissa 依赖 dyadic 表示**，scratch 迭代定出）。
  end-to-end `0 < √(x*x + y*y + 1) − z`。
- C（2D + div）：`x/(1+y) − 7/16` on `[1,3/2]×[1/2,1]`：TM 根盒 false
  （线性项吞余量），深度 2 树（x 半分再 y 半分，4 叶）闭合，
  inv 证书统一 ⟨−12,−12,−12⟩（granularity-only，随盒自适应）。
  end-to-end `0 < x/(1+y) − 7/16`。

CertTM 新增 hybrid：`fallbackTM`（零阶平凡模型：盒包围 + 零斜率 +
err = 宽度；trans/ite/abs 与失败的 div/sqrt 规则的回退，trans 包围是
rung-紧的 ~2⁻⁶⁴ 所以代数部分 TM 优势保留）、`evalTMH`、`evalTMH_sound`、
`checkPosTMH`、`checkPosTMH_sound`。严格 `evalTM`/`TMSafe` 的 none 退路
原样保留。验证：`lake build Kepler.Interval.CertTM Kepler.Interval.CertG`
绿（8665 jobs），零 sorry。

下一步：BIXPCGW 失败叶探针（CRepairBIXPCGWx7274157868xaW1R12_m64.d 的
chunk00000 取前 ~150 个 FAIL 盒，fillMkExpr0/1 @ (12, −64)，VM 跑
auto-cert 版 evalTMH 统计通过率）。

## 3. BIXPCGW 失败叶实测（进行中）

（待填）

### 3a. 探针建设与首跑（中途记录）

- 探针：`Cases/Repair/TM1ProbeBIXPCGW.d/`（driver.lean 由
  `pipeline/interval/tm1_probe_gen.py` 生成：抽取 W1R12 修复驱动的
  fillMkExpr0/1 @ rung (12, −64)，样本 = chunk00000 前 150 个 FAIL 叶）。
- 关键坑 1：repair 驱动走 **FillParams 填充层**（sqrt mantissa 槽由
  `Dyadic.sqrtFloor` 现场填充、closed trans 走 memo cache），裸 `IExpr.eval`
  在 dummy 槽 (0,0) 上直接 none——探针的 fallback 必须走 `evalFillC`。
  （首跑 0/150 即此 bug：连已知 PASS 盒都 none。）
- 关键坑 2：`nice 19` 应为 `nice -n 19`（本机 nice 在 /usr/bin/nice）。
- 诊断（diag 模式，5 PASS + 10 FAIL 对照）：
  - PASS 盒：bare1（goal 1）lo > 0 闭合；TM loBound ≈ −1e-1 —— TM 在这些
    表达式上**比裸区间差**：`err ~ O(1)`。
  - FAIL 盒：bare 双侧皆负、TM 也负（loBound ≈ −1e-1 … −1e0）。
- 失败形态分析（diag2 分解 fBlo/err/lo）：TM err ~ O(1) 的来源是
  **零阶 fallback 的 err = 包围宽度**：BIXPCGW 主 prog 的
  `trans arctan (非闭式参数)` 等节点在临界盒上的包围宽度可达 O(1)
  （arctan 值域天然 [−π/2, π/2]），fallback 的 |f(ρ)−f(y)| ≤ width 项
  乘进上层 mul 链后淹没余项。∃a-线性模型对"宽度本身 O(1)"的子式本来就
  无从改进——裸区间在单调 trans 段本来就是紧的。也就是说 BIXPCGW 的
  plateau 叶的过估**不在** TM1 已覆盖的代数段里，而在 trans/ite/abs 段
  （TM2 的 trans 合成规则才是真解），或边缘裕度本身 ≈ 0（需二分）。
- 教训：hybrid fallback 语义上安全但对"宽而紧"的 trans 节点会把 err 撑到
  包围宽度；TM1 的 +−×÷√ 代数核对这类表达式族无增益。≥95% 目标对
  "FAIL 叶直接判定（不二分）"口径预期达不到——等 150 叶全量数字确认后
  如实报告。

### 3b. 全量 150 叶结果（2026-09-21，VM 测量）

- 运行：`lake env lean --run TM1ProbeBIXPCGW.d/driver.lean boxes.txt`
  （setsid + nice -n 19，probe.out/status.txt 留档于该目录，未入库——
  与 Repair/*.d 工作目录惯例一致；再生方式：
  `python3 pipeline/interval/tm1_probe_gen.py`）。
- **结果：TMRATE pass=0 fail=150 total=150**（rung (12,−64)，hybrid
  auto-cert evalTMH 镜像）。对照组（同 chunk 前 5 个 PASS 叶）TM 也全负
  ——hybrid TM 在此表达式族上**一致差于裸区间**。
- 目标 ≥95% **未达到**，如实报告。失败形态（diag2 分解，PASS/FAIL 对照）：
  - TM err ~ O(1)：零阶 fallback（trans/ite/abs 与失败 div/sqrt 规则）的
    err = 包围宽度项主导；BIXPCGW 临界盒上 `arctan(非闭式参数)` 等节点的
    包围宽度天然 O(1)（值域限制），∃a-线性模型对宽度 O(1) 的子式无增益，
    且 err 沿 mul 链放大。
  - FAIL 叶的裸区间双侧 lo 与 TM loBound 同为小负值（~−1e-1），说明这些
    叶要么真边缘 ≈ 0（零曲面穿盒，任何判定都须二分），要么过估在
    trans/ite/abs 段——都不在 TM1 的 +−×÷√ 代数核覆盖范围内。
- 结论：TM0/TM1 的代数核对**纯代数临界形**有效（CertG pilot A/B/C 实证：
  裸区间失败处 TM 闭合），但 BIXPCGW 的 plateau 叶的瓶颈在 trans 段——
  **TM2 的 trans 合成规则（atan/ln/sin 的 TM 原生规则）才是通过率杠杆**；
  设计文档 TM1 验收"≥95%"的"纯代数段"限定词在此案例上不成立（FAIL 叶
  几乎全部经过 trans 节点）。建议 TM2 优先做 arctan 的 TM 规则
  （g' = 1/(1+t²)，g'' = −2t/(1+t²)² 区间界，初等代数可证，同 sqrt/inv
  路线），并保留 fallback 作为 ite/abs 的退路。
- 探针机制本身已跑通（fill 层镜像 + auto-cert + 逐叶 TMRATE 输出），
  TM2 的 trans 规则落地后可直接复测同一样本。

