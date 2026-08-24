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
- `exact.set` — SoPlex 精确模式参数集（复制自源码包 `settings/exact.set`）。

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
