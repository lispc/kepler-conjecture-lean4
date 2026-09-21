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
