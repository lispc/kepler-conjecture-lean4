# reference/LOCK.md — 只读参考库锁定

克隆日期：2026-08-09。均为 `--depth 1` 浅克隆，只读使用，禁止修改。

| 仓库 | 路径 | commit hash | 用途 |
|---|---|---|---|
| flyspeck/flyspeck | `reference/flyspeck` | `1ce0353008eba83d3c76ae9a25c3c242e4802d53` | Flyspeck 形式化库（HOL Light/Isabelle），定理陈述与证明对照 |
| flyspeck/kepler98 | `reference/kepler98` | `90350ab8b897a577c16cff2bd72643b3f9e32227` | 1998 原始代码与数据（图 Archive、LP 数据等的来源索引） |

## 下载锁定的参考资料

| 资料 | 路径 | 来源与校验 | 用途 |
|---|---|---|---|
| AFP Flyspeck-Tame | `reference/afp-flyspeck-tame` | `afp-Flyspeck-Tame-current.tar.gz`，2026-08-09 自 isa-afp.org，sha256 `3a0ed0fa89a9812e4952350bcea2a3cee77f32483a3bb35931596df10973f164`（原件存 `reference/_distfiles/`） | tame 图枚举完备性证明蓝本（Phase 2 核心参考） |
| plantri v5.5 源码 | `pipeline/graphs/tools/plantri55` | `plantri55.tar.gz`，2026-08-09 自 users.cecs.anu.edu.au/~bdm/plantri/，sha256 `911cdf5bcca7294eb80f8f79fefc148183f7ba81da15b3aa4d6d2401a3bc7ded` | 交叉验证生成器（仅报警用） |
| GMP 6.3.0 源码 | `pipeline/tools/gmp-6.3.0` | `gmp-6.3.0.tar.xz`，2026-08-24 自 gmplib.org/download/gmp/，sha256 `a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898`（原件存 `reference/_distfiles/`） | 精确有理算术库，SoPlex exact 模式依赖 |
| m4 1.4.19 源码 | `pipeline/tools/m4-1.4.19` | `m4-1.4.19.tar.xz`，2026-08-24 自 ftp.gnu.org/gnu/m4/，sha256 `63aede5c6d33b6d9b13511cd0be2cac046f2e70fd0a07aa9573a04a82783af96`（原件存 `reference/_distfiles/`） | GMP 构建期依赖（本机无系统 m4） |
| CMake 4.4.2 官方二进制 | 解压即用（/dev/shm，易失） | `cmake-4.4.2-linux-x86_64.tar.gz`，2026-08-24 自 github.com/Kitware/CMake releases，sha256 `3ada9a3f5d8a85413579bdd0ea6aa8e8da86efdd6d15c91a1afa517f2021956c`（原件存 `reference/_distfiles/`） | SoPlex 构建工具（本机无系统 cmake） |
| SoPlex 8.0.3 源码 | `pipeline/tools/soplex-8.0.3` | `soplex-8.0.3.tar.gz`，2026-08-24 自 github.com/scipopt/soplex tag `v8.0.3`，sha256 `224eca4c49a2509a2a893a1d4b63e510e2ddb4ff374699cc6afc36f12af4e621`（原件存 `reference/_distfiles/`） | 精确有理 LP 求解器（Phase 3 核心，GMP 开启） |
| GLPK 5.0 源码 | `pipeline/tools/glpk-5.0` | `glpk-5.0.tar.gz`，2026-08-24 自 ftp.gnu.org/gnu/glpk/，sha256 `4a1013eebb50f728fc601bdd833b0b2870333c3b3e5a816eeba921d95bec6f15`（原件存 `reference/_distfiles/`） | glpsol：GMPL 模型+数据段展开为 CPLEX-LP（Flyspeck LP 再生，见 `pipeline/lp/README.md`） |
| dReal 4.21.06.2 二进制 | `pipeline/tools/dreal-4.21.06.2` | `dreal_4.21.06.2_amd64.deb`，2026-08-24 自 github.com/dreal/dreal4 release `4.21.06.2`，sha256 `c1798357bd967bf84b06fdaf7e962e102ff6703b3dee546fdc02862a1ecc09f1`（原件存 `reference/_distfiles/`） | δ-complete SMT 求解器（Phase 4 第一层自动证明） |
| dReal 运行期依赖库 | `pipeline/tools/dreal-4.21.06.2/lib` | `libibex-dev_2.7.4+git352eeeb~22.04_amd64.deb`（launchpad PPA ppa:dreal/dreal jammy）sha256 `40f767e737871070d48a46ac068bb3a7cfc958554c0737762449a6b57ab4811c`；`libnlopt0_2.7.1-3build1` sha256 `74f0e5177b5ed338d989bd65ec03097b71bf583010b68758e10532034155d6b2`、`libgmpxx4ldbl_6.2.1+dfsg-3ubuntu1` sha256 `73e8145633a86c8f01466bb42c5b0734665268f7b2656e82365c1659525f7874`、`coinor-libclp1_1.17.5+repack1-1` sha256 `06fa26721dff9cc8e176833dd994b16b5a1265c765033195115941bd5b265903`、`coinor-libcoinutils3v5_2.11.4+repack1-2` sha256 `a7e28aa7cb550cb2fc9830dd8540d8403a1ef7dc6ffae3aa3e311318b5501c07`、`coinor-libosi1v5_0.108.6+repack1-2` sha256 `a14b2b54e1d016f7cebc0af55e67f1edd2d1240c930fe00c62cf27ca95acc470`（后五个 2026-08-24 自 Ubuntu jammy 仓库；原件均存 `reference/_distfiles/`） | dReal deb 不随包的共享库（libibex/nlopt/Clp/CoinUtils/Osi/gmpxx），本地解压进 dReal 前缀 |
| MPFR 4.2.2 源码 | `pipeline/tools/mpfr-4.2.2` | `mpfr-4.2.2.tar.xz`，2026-08-24 自 mpfr.org/mpfr-current/，sha256 `b67ba0383ef7e8a8563734e2e889ef5ec3c3b898a01d00fa0a6869ad81c6ce01`（原件存 `reference/_distfiles/`） | 任意精度浮点库，FLINT/Arb 依赖；`--with-gmp` 用项目本地 GMP 6.3.0 |
| FLINT 3.3.1 源码 | `pipeline/tools/flint-3.3.1` | `flint-3.3.1.tar.gz`，2026-08-24 自 flintlib.org/download/，sha256 `64d70e513076cfa971e0410b58c1da5d35112913e9a56b44e2c681b459d3eafb`（原件存 `reference/_distfiles/`） | 球算术分支定界（FLINT 3 内置 Arb，Phase 4 第二层兜底） |

## 关键文件索引（Phase 1/2 会用到）

- Flyspeck 主定理陈述：`reference/flyspeck/text_formalization/general/the_kepler_conjecture.hl`（由 `load_flyspeck.ml:42` 载入）
- tame 图 Archive：`reference/flyspeck/formal_graph/archive/`（`string_archive.txt` 等；以仓库文件为准，不硬编码数量）
- 非线性不等式：`reference/flyspeck/text_formalization/nonlinear/`
- LP 相关：`reference/flyspeck/formal_lp/`
