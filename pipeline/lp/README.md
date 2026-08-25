# pipeline/lp — SoPlex 精确有理 LP 冒烟测试

Phase 3 工具链引导：从源码构建的 SoPlex（exact rational 模式，GMP 开启）
对 hello-world LP 做精确求解验证。构建细节（distfile、sha256）见
`reference/LOCK.md`；安装位置 `pipeline/tools/`（m4 1.4.19、GMP 6.3.0、
SoPlex 8.0.3；CMake 4.4.2 官方二进制解压于 /dev/shm，仅构建期使用）。

## 文件

- `hello.lp` — max x+y，s.t. 2x+y ≤ 4, x+2y ≤ 5, x,y ≥ 0（LP 格式默认非负）。
  精确最优解 x=1, y=2，目标值 3。
- `hello-frac.lp` — 右端项改为 5/5 的变体，最优解 x=y=5/3，目标值 10/3，
  用于验证分数形式输出。
- `rand-12x20.lp` / `rand-30x40.lp` — `gen_rand.py` 生成的随机有界可行 LP
  （整数系数、全非负矩阵、每列至少一个正元故目标有界）。
- `exact.set` — SoPlex 精确模式参数集（复制自源码包 `settings/exact.set`）。
- `gen_rand.py` — 随机 LP 生成器：`gen_rand.py ROWS COLS SEED > file.lp`。
- `socert.py` — 不受信转换器：SoPlex 精确解 → Lean 证书（见下节）。

## 全链路试点：求解器 → 证书 → Lean checker → 定理（2026-08-24 打通）

`socert.py`（**不受信**，可用任意技巧；信任全部由 Lean 侧内核 `decide`
重放建立）把一个 .lp 文件变成 `lean/Kepler/LP/Cert<Name>.lean`：

1. 解析 .lp 子集（Maximize/Minimize、带标签的线性 `<=`/`>=` 约束、
   整数/分数/小数码系数、默认非负界；暂不支持 `=` 约束与 Bounds 段，
   数据通分后必须为整数）为 (c, A, b)；
2. 调 `soplex --loadset=exact.set -X -Y -c file.lp`，要求
   "Solved to optimality" 与原始/对偶精确检验通过；
3. 解析有理原始/对偶解（`-Y` 段按约束名给出分数乘子，缺失为 0）；
4. 用 Fraction 精确算术做不受信验证：x ≥ 0、A·x ≤ b、y ≥ 0、
   Aᵀy ≥ c、cᵀx = bᵀy（强对偶，任一失败即大声报错）；
5. 通分：D = lcm(y 的分母)，Y = D·y，G = bᵀY（即 y = Y/D、γ = G/D），
   按 `Kepler.LP.Cert` 的 `(numVars, c, A, Y, D, G)` 稀疏格式发射 Lean 文件：
   `dual_check := by decide`（内核重放）+ `bound`（经 `checkDual_sound`
   得到"所有有理可行点目标值 ≤ γ"）+ 原始解为整数时附 `primal_check`。

用法（在 `pipeline/lp/` 下）：

```sh
python3 socert.py hello.lp            # → lean/Kepler/LP/CertHello.lean
python3 socert.py hello-frac.lp       # → CertHelloFrac.lean（γ = 10/3，primal 为分数故跳过）
python3 gen_rand.py 12 20 7 > rand-12x20.lp
python3 socert.py rand-12x20.lp       # → CertRand12x20.lean
cd ../../lean && lake build Kepler.LP.CertHello Kepler.LP.CertHelloFrac \
  Kepler.LP.CertRand12x20 Kepler.LP.CertRand30x40
```

已验证结果（内核 `decide` 闭合，公理仅 propext/Classical.choice/Quot.sound）：

| LP | 规模 | γ（最优值） | `dual_check` 构建耗时 |
|---|---|---|---|
| hello | 2×2 | 3 | 秒级 |
| hello-frac | 2×2 | 10/3 | 秒级 |
| rand-12x20 | 12×20, 163 nz | 19969/111 | ~78 s |
| rand-30x40 | 30×40, 850 nz | 44669256618739/149705792664 | ~83 s（全模块 119 s） |

**规模观察**：checker 每列重新扫描所有行支撑（`colDotI` → 每行
`coeffs.get j`），内核代价 ~O(变量数 × 非零元数) 次 whnf 归约；30×40
需 ~83 s，说明 >10² 规模必须走 Cert.lean 文件头注释里的分片
（sharding）/转置预计算路线，试点的 `decide` 直放只适合小案例。

## 分片原型设计（2026-08-25，方案记录 → `Cert.lean` "Sharded checking" 节）

**问题**：`checkDual` 的最贵合取项是列循环 `AᵀY ≥ D·c`——`colDotI` 每列
重扫全部行支撑，内核工作量 ~ `numVars × nnz` 次归约。真实图试点
（915 变量 × 3882 行 × 8056 非零，Y 为 ~300 位整数）单块 `decide` 实测
25304 s（7h）；43,078 个终端 LP 裸跑完全不可行。

**分片粒度选择**：候选有二——(a) 按对偶约束逐列（列循环拆分），
(b) 按约束行分组。选 **(a) 逐列分片**：成本驱动项就是列循环，列间无
任何数据依赖，每列工作量 ~O(nnz) 完全均匀；行分组拆的是廉价合取项
（`wf` 扫描 O(nnz) 与 `bᵀY` 一次性求值），留在 `checkDualBase` 里一次
`decide` 即可。

**结构**（`Cert.lean` 新增，通用部分只证一次）：

- `checkDualBase lp Y D G` — 除列循环外的一切（D>0、尺寸、wf、Y≥0、bᵀY≤G）；
- `checkDualCols lp Y D s len` — 列循环限制在 `[s, s+len)`；
- `checkDualColShards lp Y D n k count` — `&&` 链聚合 count 片（对 count
  结构递归，内核友好；片 i 覆盖 `[i·k, i·k+min k (n−i·k))`）；
- `checkDualColShards_correct/sound` + `checkDual_of_shards` — 一次性通用
  组装：片数覆盖 `numVars ≤ count·k` 时合回 `checkDual = true`。

**生成布局**（`socert.py --shard-cols K`，模块目录 `Kepler/LP/<Mod>/`）：

- `Data.lean`：字面量只**阐明一次**（`lp`/`certY`/`certD`/`certG`），
  附 `base_check := by decide`；
- `Cols<i>.lean`：每片一个独立模块一个定理
  `shard_<i> : checkDualCols lp certY certD s len = true := by decide`——
  相互无依赖，可任意并行构建，单进程内存有界；
- `Assembly.lean`：链式组装 `cols_<i+1> := Bool.and_eq_true_iff.mpr
  ⟨cols_<i>, shard_<i>⟩`（**term 模式，不做内核重算**），`dual_check`
  经 `checkDual_of_shards`，`bound` 经 `checkDual_sound`，外加 Flyspeck
  终端条件 `gamma_lt : certG < 12·certD := by decide` 与
  `bound_lt : cᵀx < 12`。

组装链是 O(片数) 的 elaborator 工作，内核不重新求值任何片；每片内核
`decide` 只扫 `len` 列 × 全部行支撑。信任基不变（零 sorry、零
native_decide、零自引入 axiom）。

实测数据与复现命令见"真实图再生试点"小节末尾。

## 真实图再生试点（2026-08-24，hypermap 204880136538）

从 Flyspeck easy 证书出发，端到端复刻一张真实 tame 图的 LP 上界证明：
**证书分支树 → 数据段 → glpsol 展开 .lp → SoPlex exact → socert → Lean**。
选图：`easy_1.dat` 第 1 号证书（15 节点、21 面：5 四边形 + 16 三角形），
分支树为**单终端**（precision=3, infeasible=false）——根 LP 一次解决，
无需复刻分支。链路各环节：

1. **证书解析** `parse_lpcert.py`：纯 Python OCaml-Marshal 读器（小格式
   魔数 84 95 a6 be；int64 为 custom block `"_j"`；共享引用按对象表偏移），
   解出 `lp_certificate list`（类型见 `formal_lp/hypermap/main/lp_certificate.hl`）。
   `easy_1.dat`：424 张图，终端数直方图 1→370、5→30、9→8、…、49→2；
   370 张单终端图全部 infeasible=false。
2. **数据段生成** `gen_data.py`：Python 重实现 `convert_to_list3`（超图串
   →面表）、`order_list`（分支排序：6/4/5/3 面分组，组内按节点出现数
   降序、稳定）、`mk_order_bb`（根 bb：所有 apex/edge/node 集合为空）、
   `modify_hex_cases`（六边形面移入 std56_flat_free；本图无六边形）、
   `ampl_of_bb`（~20 条 set/param 赋值）。输出与 `lpproc.ml` 逐条对照。
3. **模型**：`head.mod + body.mod` 施加与 `build_certificates.hl:50-65`
   （`make_models false` → model2）相同的三条 sed：删 `main: sum ln >= 12`、
   目标改为 `maximize objective: sum{i in node} ln[i];`、删 `lnsum_def`。
   语义：max Σln（证书语义即"所有可行点 Σln ≤ γ"，γ < 12 即 Flyspeck
   的 `scriptL > 12` 终端条件）。
4. **展开**：`glpsol -m model2.mod -d data.txt --wcpxlp out.lp`
   （GLPK 5.0，构建见 `reference/LOCK.md`）。glpsol 生成即是对数据段的
   强校验（`within` 声明全部通过；dart 数 68 = 2E 与 Euler 公式一致）。
   本图：1654 行 × 913 列，浮点最优 11.77525932，与单终端证书一致
   （≤ 11.9999 阈值）。注意 .lp 文本常数是 glpsol 的 15 位小数打印
   （π → 3.14159265358979）——Flyspeck 自己的证书管线同样以 .lp 文本
   为准（LP-HL.exe 读的就是它），故这是忠实复刻而非额外舍入。
5. **扁平化** `flatten_lp.py`：等式拆 `__le`/`__ge` 两行、Bounds 段转为
   显式行（默认下界 0 保持隐式）、自由变量（仅报表变量 ynsum/sqdeficit）
   正负拆分。所有常数按精确有限小数输出（SoPlex `readmode=1` 精确读入；
   **不要**在此步整数化——×10¹⁴ 的行缩放会使 SoPlex 浮点预处理的
   容差校验误判 infeasible，整数化已移到 socert 发射期）。转换等价性由
   glpsol 复解确认（目标值逐位一致）。
6. **求解+证书** `socert.py`（已扩展：接受有理数据，发射期按行通分；
   SoPlex 对 max 问题的 `>=` 行报告**负**对偶乘子，解析时按行翻转符号；
   大证书自动加 `set_option maxRecDepth 100000`——深列表字面量与内核
   `decide` 都需要）。SoPlex exact 求解仅 **2.75 s**（"Solved to
   optimality"，原始/对偶精确检验 violation = 0）。
7. **Lean**：`lean/Kepler/LP/CertPilot204880136538.lean`（830 KB，
   915 变量 × 3882 行 × 8056 非零；D 为 ~300 位整数，γ = G/D ≈ 11.77525932，
   距阈值 12 余量 0.2247）。**不**加入 `Kepler.lean` 主 import 树，
   按需 `lake build Kepler.LP.CertPilot204880136538`。

复现（在 `pipeline/lp/` 下）：

```sh
python3 parse_lpcert.py ../../reference/flyspeck/formal_lp/glpk/binary/easy_1.dat
python3 gen_data.py --from-dat ../../reference/flyspeck/formal_lp/glpk/binary/easy_1.dat \
  --index 1 > pilot/data_204880136538.txt
cat ../../reference/flyspeck/formal_lp/glpk/{head,body}.mod > pilot/model2.mod
sed -i -e 's/main:.*//' \
  -e 's/maximize objective:.*/maximize objective: sum{i in node} ln[i];/' \
  -e 's/lnsum_def:.*//' pilot/model2.mod
../tools/glpk-5.0/bin/glpsol -m pilot/model2.mod -d pilot/data_204880136538.txt \
  --wcpxlp pilot/pilot_204880136538.lp
python3 flatten_lp.py pilot/pilot_204880136538.lp pilot/pilot_204880136538_flat.lp
python3 socert.py pilot/pilot_204880136538_flat.lp --module CertPilot204880136538
cd ../../lean && lake build Kepler.LP.CertPilot204880136538
```

**`lake build Kepler.LP.CertPilot204880136538` 三次尝试（2026-08-24）**：

| 尝试 | 设置 | 结果 |
|---|---|---|
| 1 | 默认 | 2m26s 失败：`maximum recursion depth`（深列表字面量与 `decide` 归约都触发） |
| 2 | `maxRecDepth 100000` | 4m02s 失败：`whnf` 达 `maxHeartbeats` 上限（elaborator 侧 `decide` 求值） |
| 3 | `maxRecDepth 100000` + `maxHeartbeats 0` | 运行 2h06m 后人工终止：lean worker 满速单核，RSS 线性涨至 29.8GB 无收敛迹象 |

按 rand-30x40（83 s）的 O(变量数 × 非零元数) 内核代价外推，本实例
（915 变量 × 8056 非零，Y 为 ~300 位整数）需数天级机时与数百 GB 内存，
**确认全量化前必须先落地 `Cert.lean` 文件头注释里的分片/转置预计算
路线**——这是本试点的主要后续工作项，与 Phase 3 试点结论一致。
socert 生成的小证书（hello/rand 系列，同一代码路径）内核闭合早已验证，
故路线可行性不受此瓶颈影响：缺的是内核重放的扩展性，不是链路本身。

### 分片原型实测（2026-08-25，hypermap 204880136538，方案见上文"分片原型设计"）

`socert.py --shard-cols 1 --terminal-bound 12` 生成
`lean/Kepler/LP/Pilot204880136538/`（Data + 915 个单列 Cols 分片 +
Assembly），`build_shards.py` 进程池并行构建（oleans 写入 lake 规范路径
`.lake/build/lib/lean/...`——Lean 的 `SearchPath.findWithExt` 按包根
`Kepler/` 取第一个 LEAN_PATH 条目，独立输出树不可行，这是本机实测
确认的行为）。结果（全部 `decide` 内核闭合，`#print axioms` 仅
propext/Classical.choice/Quot.sound，`gamma_lt` 零公理）：

| 阶段 | 内容 | 耗时 |
|---|---|---|
| Data | 字面量阐明（830KB）+ `base_check`（wf/尺寸/Y≥0/bᵀY≤G） | 198 s（wall 3m41s，RSS 7.9GB） |
| 915 列分片 | 单片 = 1 列 × 3882 行支撑扫描 + ~13s 进程启动；无争用采样 **42 s/片**（净 decide ≈ 28 s，与 25304s/915 ≈ 27.7s 吻合）；96 并发满载 med 131 s / max 150 s | **wall 1255 s（21 min）**，sum 117308 s（争用膨胀） |
| Assembly | 915 个 term 模式链式组装 + `dual_check` + `bound` + `gamma_lt`/`bound_lt` | 65.5 s |
| **端到端** | Data + 分片 + Assembly | **≈ 1542 s（25.7 min）** |

**相对单块 25304 s（7h02m）加速 ≈ 16.4×**（96 并发且与机器上其他负载
争用；无争用理论值 ~50×：单片 42 s × 915 / 128 + 固定开销 ≈ 6-8 min）。
关键性质：每片内存有界（~1.5GB/进程，96 并发峰值 ~150GB/503GB）、
失败可单片重试（`--only`）、组装不做内核重算。

**对 43,078 终端 LP 的外推**：分片把墙钟压到 ~26 min/LP，但总内核工作量
不变（O(numVars×nnz) ≈ 7.1 core-h/LP + 915×13s 启动 ≈ 3.3 core-h；k=8
可把启动开销降到 ~0.4 core-h）。按 7h core/LP 估计：43078 × 7h ≈
34 core-年，128 核 ≈ **~100 天**——分片单独不足以全量化。出路是
`Cert.lean` 头注释记录的转置（列主序）证书表示：对偶检查变为 O(nnz)，
单 LP 内核时间降至 ~30 s 量级（43,078 LP ≈ 1-2 core-天），届时瓶颈转为
每 LP 的 Data 字面量阐明（~4 min，可分片或优化）。这是下一步主工作项。

复现：

```sh
python3 socert.py pilot/pilot_204880136538_flat.lp --module Pilot204880136538 \
  --shard-cols 1 --terminal-bound 12
cd ../../lean && lake build Kepler.LP.Pilot204880136538.Data
cd ../pipeline/lp && python3 build_shards.py Pilot204880136538 --procs 96
```

### 全量化（19700 图）初步估计

- 证书解析：~27 s/文件（424 图），20 个 easy 文件 ~10 min 一次性。
- 单图链路：gen_data ~1 s + glpsol ~0.6 s + flatten ~2 s + SoPlex exact
  ~3 s + socert ~3.5 min（瓶颈：Fraction 大整数通分/不受信验证，可优化
  一至两个数量级）。多数图为单终端；多终端图需按分支树逐终端复刻
  （分支结构在证书中，但分支语义——split4/split5/6 的 apex 集合构造——
  尚未重实现，见"未做"）。
- **Lean 内核 `decide` 是主要瓶颈**：915×3882 规模远超 rand-30x40（83 s）
  外推范围，必须落地 `Cert.lean` 文件头注释里的分片（sharding）/转置
  预计算路线后才能全量化。
- 未做：分支节点（非根）数据段（apex_sup_flat/apex_flat/apex_A/apex4/5、
  d_edge_*、node_*、std3_big/small 集合的构造，即 `switch3/4/5/6` 与
  `modify_bb` 的重实现）；infeasible 终端（easy_1.dat 仅第 0 号图一例，
  需要不可行证书的 Farkas 形式，`Cert.lean` 当前只支持对偶上界）。

## 精确模式用法（已验证）

## 精确模式用法（已验证）

关键在三个设置（`exact.set` 内容）：

- `int:readmode = 1` — 以有理数读入 LP 文件（系数精确，不舍入为 double）；
- `int:solvemode = 2` — 精确有理求解（浮点单纯形 + iterative refinement +
  rational reconstruction，产出精确最优基）；
- `int:checkmode = 2` + `real:feastol = 0` + `real:opttol = 0` —
  以精确算术做事后可行性/最优性检验，零容差。

运行命令：

```sh
SOPLEX=/home/scroll/repos/kepler-conjecture-lean4/pipeline/tools/soplex-8.0.3/bin/soplex
cd /home/scroll/repos/kepler-conjecture-lean4/pipeline/lp
$SOPLEX --loadset=exact.set -X -c hello.lp
```

- `--loadset=exact.set` 载入上述精确参数（命令行 `--solvemode=2` 也可用，
  但 `checkmode` 等无对应短参数，settings 文件最省事）；
- `-X` 以有理数（分数）形式打印原始解（`-Y` 为对偶）；
- `-c` 在原始问题上对解做最终精确检验。

## 验证结果（2026-08-24）

- `hello.lp`：`x = 1, y = 2`，Objective value 3，
  "Primal/Dual solution feasible in original problem (max. violation = 0)"。
- `hello-frac.lp`：`x = 5/3, y = 5/3`，Objective value 3.33333333e+00（= 10/3），
  分数输出确认。
- `ldd $SOPLEX | grep gmp` 指向 `pipeline/tools/gmp-6.3.0/lib/libgmp.so.10`；
  启动横幅显示 `[rational: GMP 6.3.0]`。

## 备注

- 二进制带 RUNPATH 指向 `pipeline/tools/gmp-6.3.0/lib` 与
  `pipeline/tools/soplex-8.0.3/lib`，无需 LD_LIBRARY_PATH；若移动
  `pipeline/tools` 位置需重设 rpath 重建（见 LOCK.md 中的 distfile）。
- 构建期坑：本机无 m4（GMP 构建需要，故先装 m4 1.4.19）；SoPlex 8 的
  `src/CMakeLists.txt` 覆盖 INSTALL_RPATH，首次安装后 ldd 链到系统
  GMP 6.2.1，须通过 `CMAKE_EXE_LINKER_FLAGS`/`CMAKE_SHARED_LINKER_FLAGS`
  注入 `-Wl,-rpath,<gmp>/lib` 重新链接。
