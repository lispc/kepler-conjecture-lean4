# pipeline/interval — Phase 4 非线性不等式验证工具链

两层验证（PLAN.md §4）：

1. **dReal 4.21.06.2** — δ-complete SMT 求解器（第一层自动证明）
2. **FLINT 3.3.1（内置 Arb）+ MPFR 4.2.2 + GMP 6.3.0** — 球算术分支定界（第二层兜底）

所有工具均为用户态安装，位于 `pipeline/tools/`，无需 sudo。源码 tar 包原件存
`reference/_distfiles/`，锁定信息见 `reference/LOCK.md`。

## Lean 侧区间 checker（证书验证层）

求解器输出（dReal δ-证明 / Arb 球）需转换为 Lean 内核可检查的证书，由
`lean/Kepler/Interval/` 的 checker 验证（检查层只用 `Int`/dyadic ——
内核不能归约 `Rat` 算术；语义层在 ℝ 上陈述 soundness）：

| 文件 | 内容 |
|---|---|
| `Basic.lean` | dyadic `m·2^e` 端点区间 `+ - × Neg`、`IExpr` AST、`checkPos_sound` |
| `Div.lean` | `divFloorQ`（粒度 `2^out` 的带显式 ulp 误差除法）、区间 `recip`/`div` |
| `Sqrt.lean` | 证书式 `sqrtI`（内核仅验证 `s²≤n<(s+1)²`；`Int.sqrt` 不可内核归约） |
| `Ball.lean` | 中点半径包装 `Ball`、与 `DInterval` 双向换算、sound 的球算术 |
| `Trans.lean` | Leibniz 交替级数界 + `sin` 的 Taylor dyadic 区间/球（[0,1]） |

证书生成约定：求解侧用 MPFR/Arb（或 Python）算出各 `out` 粒度下的
mantissa（如 √ 的 `s`、Taylor 各项的 floor），Lean 侧 `decide` 只做
大整数比较与 `Int` 算术重放。

## 目录

| 路径 | 内容 |
|---|---|
| `pipeline/tools/dreal-4.21.06.2/` | dReal 二进制前缀（bin/include/lib/share，deb 解压 + 依赖库补齐） |
| `pipeline/tools/gmp-6.3.0/` | GMP 6.3.0（Phase 3 已建） |
| `pipeline/tools/mpfr-4.2.2/` | MPFR 4.2.2，链接本地 GMP |
| `pipeline/tools/flint-3.3.1/` | FLINT 3.3.1（含 Arb 球算术），链接本地 GMP/MPFR |
| `test_sqrt2.smt2` | dReal 冒烟测试公式 |
| `test_arb.c` | Arb 冒烟测试（π、√2 的 53-bit 球） |

## dReal 用法

`bin/dreal` 是包装脚本，自动注入随包依赖库（libibex 2.7.4、nlopt 2.7.1、
Coin-OR Clp 1.17.5、gmpxx，均在 `lib/` 下），直接调用即可：

```sh
pipeline/tools/dreal-4.21.06.2/bin/dreal --precision 0.001 pipeline/interval/test_sqrt2.smt2
# 输出: unsat   （即 forall x in [1.5,2], x^2-2 > 0 成立，δ=1e-3）
```

- 输入为 SMT-LIB2，`QF_NRA` 逻辑；`--precision` 即 δ。
- 输出 `unsat` = 否定式 δ-不可满足 ⇒ 原不等式（严格）成立；
  输出 `delta-sat with delta = ...` = 找到一个 δ-扰动下的解（可能真 sat，也可能落在 δ 带内，需收紧精度或转第二层）。
- 常用选项：`--model`（sat 时打印模型）、`--proof`（输出证明痕迹）、`--local-optimization`。

## 编译链接本地 GMP/MPFR/FLINT

FLINT 3 是单一大库 `libflint`，Arb 头文件在 `flint/arb.h`（不是独立的 `arb.h`）。
编译时用 `-I` 指三个前缀的 `include`，`-L` + `-lflint -lmpfr -lgmp`，并加
`-Wl,-rpath` 免去运行期 `LD_LIBRARY_PATH`：

```sh
TOOLS=$(pwd)/pipeline/tools
gcc -O2 pipeline/interval/test_arb.c -o /tmp/test_arb \
  -I$TOOLS/flint-3.3.1/include -I$TOOLS/mpfr-4.2.2/include -I$TOOLS/gmp-6.3.0/include \
  -L$TOOLS/flint-3.3.1/lib -lflint \
  -L$TOOLS/mpfr-4.2.2/lib -lmpfr \
  -L$TOOLS/gmp-6.3.0/lib -lgmp -lm \
  -Wl,-rpath,$TOOLS/flint-3.3.1/lib \
  -Wl,-rpath,$TOOLS/mpfr-4.2.2/lib \
  -Wl,-rpath,$TOOLS/gmp-6.3.0/lib
/tmp/test_arb
# 输出 pi、sqrt(2) 的 53-bit 球，并自检真值落在球内，最后打印 OK
```

C++ 项目同理（`-lflint -lmpfr -lgmp` 顺序保持被依赖者靠后）。

## 重建方法（机器重装 / /dev/shm 清空后）

源码原件都在 `reference/_distfiles/`：

```sh
# MPFR（依赖本地 GMP）
tar -xf reference/_distfiles/mpfr-4.2.2.tar.xz
cd mpfr-4.2.2
./configure --prefix=$PWD/../../pipeline/tools/mpfr-4.2.2 \
  --with-gmp=$PWD/../../pipeline/tools/gmp-6.3.0
make -j && make check && make install

# FLINT（依赖本地 GMP+MPFR；configure 需要 m4，用项目本地 m4）
export PATH=$PWD/../../pipeline/tools/m4-1.4.19/bin:$PATH
tar -xf reference/_distfiles/flint-3.3.1.tar.gz
cd flint-3.3.1
./configure --prefix=$PWD/../../pipeline/tools/flint-3.3.1 \
  --with-gmp=$PWD/../../pipeline/tools/gmp-6.3.0 \
  --with-mpfr=$PWD/../../pipeline/tools/mpfr-4.2.2
make -j && make check && make install
```

dReal 重建：重新下载 deb（URL 见 LOCK.md），`ar x` + 解 `data.tar.gz`，
再按 `pipeline/tools/dreal-4.21.06.2/` 现状补齐 `lib/` 下的依赖库
（来源：Ubuntu jammy 仓库 libnlopt0/libgmpxx4ldbl/coinor-libclp1/coinor-libcoinutils3v5/coinor-libosi1v5，
以及 launchpad PPA `ppa:dreal/dreal` 的 libibex-dev 2.7.4 jammy 包）。
