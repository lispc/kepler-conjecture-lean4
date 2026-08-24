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
