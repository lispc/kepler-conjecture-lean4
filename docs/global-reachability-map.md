# 全局可达图（多根）v2

> 2026-11-03。验收口径「树优先」（DECISIONS 2026-11-03「树越大越好」）：
> 主指标 = **K-REACH / COVERAGE / SHIMS / ORPHANS**；`K-SORRIED` 为信息项；
> `K-AXIOM` 为护栏。
>
> **树只认 proof-term 可达，不认 import 闭包。** 遍历器从每个根出发，只展开
> `ConstantInfo.value? true`（theorem/opaque 的值），子节点只收
> `Kepler.*` / `_private.Kepler.*`。`import` 进来但不在任何根证明项里的声明
> **不计入** K-REACH——它们就是 ORPHANS。
>
> 脚本：`lean/scripts/global_reach_map.lean`（standalone，不用 lake）。
> e2e 单根指标见 [`e2e-reachability-map.md`](e2e-reachability-map.md)。

## 1. 根集合（ROOTS）

| 根族 | 取法 | 基线枚举数 |
|---|---|---:|
| e2e | `Kepler.Assembly.the_kepler_conjecture_from_interfaces` | 1 |
| PackingConcl | 模块 = `Kepler.Text.PackingConcl` 且名字后缀 `_discharged`（自动枚举） | 61 |
| LocalConcl | 模块 = `Kepler.Text.LocalConcl` 且名字后缀 `_discharged`（自动枚举） | 92 |
| 章 capstone（手动清单） | `Kepler.Text.OXLZLEZ`、`Kepler.Text.PACKING_CHAPTER_MAIN_CONCLUSION` | 2（见 §6 注） |
| **合计（去重后）** | | **154（本次运行）/ 156（补上 capstone 后）** |

枚举口径：`env.constants` 逐项看最后一段名字后缀（`lastNamePart`，不分配整串），
命中后再用 `moduleOf env n` 判模块。枚举数会打印为
`ROOTS_PACKINGCONCL_ENUMERATED` / `ROOTS_LOCALCONCL_ENUMERATED` /
`ROOTS_CAPSTONE_MANUAL_PRESENT` / `ROOTS_TOTAL`，缺根打印 `ROOT_SKIP`。

## 2. 指标定义

| 指标 | 定义 |
|---|---|
| **K_REACH** | distinct 可达 Kepler 声明数（树节点；含 axiom/opaque） |
| **K_SORRIED** | 值里**直接**含 `sorryAx` 的可达声明数（信息项） |
| **K_AXIOM** | 可达 Kepler 公理数（护栏；含 `native_decide` 的 `*_native_decide.ax_*`） |
| **K_MODULES** | 可达声明所在的不同模块数 |
| **K_UNIVERSE** | 当前 env（`import Kepler` + `Kepler.Assembly` + `Kepler.Text.PackingConcl` 闭包）中全部 Kepler 声明数 = COVERAGE 分母 |
| **COVERAGE** | union K_REACH / K_UNIVERSE |
| **UNION** | 全部根的多源 BFS 去重结果（不是各根 K_REACH 的和） |
| **ORPHANS** | K_UNIVERSE − union K_REACH；`ORPHANS_PUBLIC` / `ORPHANS_PRIVATE` 分开计数 |
| **SHIMS** | union 树内每个 `Kepler.Text.*_concl`，若存在 `*_concl_discharged` 或 `*_discharged` 则计为 shim；并标注该 `*_concl` 是否 sorried（`SHIMS_SORRIED`） |

**每根 K_REACH 是独立 BFS 的 distinct 闭包**（不是 union 里的分摊数）；根之间大量重叠，
所以 `Σ 每根 K_REACH` 远大于 union。

## 3. 基线读数（HEAD `5384f11d`，仪器校准后）

| 指标 | 值 |
|---|---:|
| 根总数 | 154（PackingConcl 61 + LocalConcl 92 + e2e 1；capstone 2 见 §6） |
| **UNION K_REACH** | **2,079,502** |
| **UNION K_SORRIED** | **190** |
| UNION K_AXIOM | 624 |
| UNION K_MODULES | 4,179 |
| UNION TOTAL (legacy) | 2,078,800 |
| K_UNIVERSE | 2,094,326 |
| COVERAGE | 99.29%（2,079,502 / 2,094,326） |
| ORPHANS | **14,824**（public 11,295 / private 3,529） |
| SHIMS | **21**（其中 `SHIMS_SORRIED` = 3） |
| K_SORRIED > 0 的根 | 73 / 154 |

对比 e2e 单根（同 HEAD）：K_REACH 2,078,095 / K_SORRIED 123。多根只增加
**+1,407 个树节点 / +67 个直接 sorry 源**——packing chapter 与 local 装配出口的
真实债只在多根视图里显形（e2e 根到不了它们）。

### 每根 Top 10（按 K_REACH）

| 根 | K_REACH | K_SORRIED |
|---|---:|---:|
| `Assembly.the_kepler_conjecture_from_interfaces`（e2e） | 2,078,095 | 123 |
| `Text.nonlinear_imp_lp_main_estimate_p16_discharged` | 5,858 | 14 |
| `Text.JEJTVGB_p16_discharged` | 5,855 | 14 |
| `Text.OXLZLEZ_concl_discharged` | 4,586 | **31** |
| `Text.HIJQAHA_discharged` | 4,540 | 3 |
| `Text.RAWZDIB_discharged` | 4,153 | 0 |
| `Text.BNAWVNH_discharged` | 4,149 | 0 |
| `Text.RYPDIXT_discharged` | 4,133 | 0 |
| `Text.MFKLVDK_discharged` | 3,691 | 0 |
| `Text.AUEAHEH_discharged` | 3,546 | 0 |

### 每根 Top 10（按 K_SORRIED）

| 根 | K_SORRIED | K_REACH |
|---|---:|---:|
| `Assembly.the_kepler_conjecture_from_interfaces`（e2e） | 123 | 2,078,095 |
| `Text.OXLZLEZ_concl_discharged` | 31 | 4,586 |
| `Text.nonlinear_imp_lp_main_estimate_p16_discharged` | 14 | 5,858 |
| `Text.JEJTVGB_p16_discharged` | 14 | 5,855 |
| `Text.UPFZBZM_concl_discharged` | 7 | 1,938 |
| `Text.OEHDBEN_discharged` | 4 | 414 |
| `Text.ARDBZYE_discharged` | 4 | 285 |
| `Text.KIZHLTL2_concl_discharged` | 3 | 804 |
| `Text.HIJQAHA_discharged` | 3 | 4,540 |
| `Text.YOBIMPP_discharged` | 3 | 264 |

### union SORRIED 按模块（前 10）

| 模块 | 直接 sorry 源 |
|---|---:|
| `Kepler.Assembly` | 77 |
| `Kepler.Text.PackingAuto25` | 30 |
| `Kepler.Text.LocalConcl` | 23 |
| `Kepler.Text.PackingConcl` | 8 |
| `Kepler.Text.PackingAuto15` | 5 |
| `Kepler.Text.LocalAuto26` | 4 |
| `Kepler.Text.PackingAuto7` | 3 |
| `Kepler.Text.PackingAuto2` | 3 |
| `Kepler.Text.LocalAuto33` | 3 |
| `Kepler.Text.LocalAuto32` | 3 |

> union 190 与 e2e 123 的差集 = 73 个只在非 e2e 根上显形的源；`OXLZLEZ_concl_discharged`
> 单根就占 31 个（PA25 packing chapter 的 `real_model_*` 等）。这解释了为什么
> 只盯 e2e 会把 packing/local 装配出口的债记为 0。

## 4. ORPHANS（import 闭包有、树里没有）

- 定义：`K_UNIVERSE − union K_REACH` = **14,824**；其中 public `Kepler.*` 11,295、
  private `_private.Kepler.*` 3,529。
- 含义：这些声明被 `import` 拉进环境，但没有任何一个根（e2e / PackingConcl /
  LocalConcl）的 proof-term 引用它们。它们是「import 闭包 ≠ 树」的直接证据；
  ORPHANS 变大通常意味着新增了未被任何出口消费的模块/接口，而不是树变小。
- 前 10（完整前 50 见运行日志 `--- ORPHANS FIRST 50 ---`）：

| 模块 | 声明 |
|---|---|
| `Kepler.Assembly.IdLists` | `Kepler.Assembly.AllCertifiedMirror` |
| `Kepler.Assembly.IdLists` | `Kepler.Assembly.CertifiedIneqHoldsMirror` |
| `Kepler.Assembly` | `Kepler.Assembly.IsHypermapOfList.casesOn` |
| `Kepler.Assembly` | `Kepler.Assembly.IsHypermapOfList.mk._flat_ctor` |
| `Kepler.Assembly` | `Kepler.Assembly.IsHypermapOfList.rec` |
| `Kepler.Assembly` | `Kepler.Assembly.IsHypermapOfList.recOn` |
| `Kepler.Assembly.IdLists` | `Kepler.Assembly.TheNonlinearInequalitiesFilled` |
| `Kepler.Assembly.IneqPilot` | `Kepler.Assembly.allCertified_pilot` |
| `Kepler.Assembly.IdLists` | `Kepler.Assembly.certLookupDomain` |
| `Kepler.Assembly` | `Kepler.Assembly.certifiedIneqHoldsPilotCase` |

> 注：ORPHANS 含编译器生成的辅助声明（`casesOn` / `recOn` / `_flat_ctor` 等），
> 页面展示时可按 `kind` 过滤；人工核孤儿优先看 `theorem` / `def`。

## 5. SHIMS（可被 discharge 的 `*_concl` 接口）

判定：union 树内、名字以 `_concl` 结尾的 `Kepler.Text.*` 声明，若存在
`<name>_discharged` 或 `<name 去掉 _concl>_discharged`，计为 shim。共 **21** 条，
其中 3 条自身仍 sorried（`SHIMS_SORRIED = 3`）：

| `*_concl`（树内） | 对应 discharge | concl 自身 sorried |
|---|---|---|
| `Kepler.Text.CHQSQEY_concl` | `CHQSQEY_concl_discharged` | false |
| `Kepler.Text.DUUNHOR_concl` | `DUUNHOR_concl_discharged` | false |
| `Kepler.Text.GLTVHUM_concl` | `GLTVHUM_concl_discharged` | false |
| `Kepler.Text.GRHIDFA_concl` | `GRHIDFA_concl_discharged` | false |
| `Kepler.Text.GRUTOTI1_concl` | `GRUTOTI1_concl_discharged` | **true** |
| `Kepler.Text.IPVICGW_concl` | `IPVICGW_concl_discharged` | false |
| `Kepler.Text.LUIKGMH_concl` | `LUIKGMH_concl_discharged` | false |
| `Kepler.Text.LXDEYBO_concl` | `LXDEYBO_concl_discharged` | false |
| `Kepler.Text.MTMLSRF_concl` | `MTMLSRF_concl_discharged` | false |
| `Kepler.Text.OAPVION1_concl` | `OAPVION1_concl_discharged` | false |
| `Kepler.Text.OAPVION2_concl` | `OAPVION2_concl_discharged` | false |
| `Kepler.Text.OAPVION3_concl` | `OAPVION3_concl_discharged` | false |
| `Kepler.Text.QXSKIIT_concl` | `QXSKIIT_concl_discharged` | **true** |
| `Kepler.Text.RDWKARC_concl` | `RDWKARC_concl_discharged` | false |
| `Kepler.Text.RSIWAMP_concl` | `RSIWAMP_concl_discharged` | false |
| `Kepler.Text.UNPNFVW_concl` | `UNPNFVW_concl_discharged` | false |
| `Kepler.Text.UPFZBZM_concl` | `UPFZBZM_concl_discharged` | **true** |
| `Kepler.Text.UTEOITF_concl` | `UTEOITF_concl_discharged` | false |
| `Kepler.Text.WKEIDFT_concl` | `WKEIDFT_discharged` | false |
| `Kepler.Text.YRTAFYH_concl` | `YRTAFYH_discharged` | false |
| `Kepler.Text.unadorned_MMs_concl` | `unadorned_MMs_discharged` | false |

> 有 3 条 concl 自身仍 sorried 但已存在 discharge（`GRUTOTI1` / `QXSKIIT` / `UPFZBZM`）：
> 这是 F1 / Stage-1 类「假债」的候选——页面应把「有 discharge 但 concl 仍 sorry」标红。
> 其余 18 条 concl 的 proof-term 已通过 discharge 走通（`sorried=false`），是健康的
> 接口 shim。

## 6. 本次运行的口径注记（必须随读数一起引用）

1. **capstone 根未计入**：本次运行（`GLOBAL_ROOTS_LIMIT` 未设）脚本里的手动清单写成了
   `Kepler.Text.PackingAuto25.OXLZLEZ` / `...PACKING_CHAPTER_MAIN_CONCLUSION`，实际全名是
   `Kepler.Text.OXLZLEZ` / `Kepler.Text.PACKING_CHAPTER_MAIN_CONCLUSION`，因此两条都打印了
   `ROOT_SKIP`，`ROOTS_TOTAL` 是 **154 / 156**。**union 读数是下界**：补上两个 capstone 后
   K_REACH / K_SORRIED 只会增加。交付的脚本已修正为正确全名（`docs` 本页保留本次读数，
   §3 明确标注 154/156）。
2. **`K_UNIVERSE` 口径**：脚本 `import Kepler` + `Kepler.Assembly` + `Kepler.Text.PackingConcl`
   的 env 中 Kepler 声明总数；不是整个 Mathlib 宇宙。
3. **每根 K_REACH**：独立 BFS 的 distinct 闭包；不是 union 分摊。
4. **根枚举**：`_discharged` 后缀按最后一段名字匹配，不解析源码；`PackingConcl` /
   `LocalConcl` 模块归属由 `env.getModuleIdxFor?` 决定。
5. **性能**：`env.constants` 全扫描（枚举 / K_UNIVERSE / ORPHANS）在解释器里约 7 min；
   154 根 per-root 总耗时约 6–8 min；union BFS 约 2 min。整轮 ≈ 20–25 min（本机）。

## 7. 运行命令（standalone，不用 lake）

先按 [`e2e-reachability-map.md` §v2.2](e2e-reachability-map.md) 建 scratch farm
（硬链接镜像 `.lake` 的 Kepler olean，再用 `git show <ref>:<path>` 的源重建被污染模块；
**不要**直接用主仓现成 olean 校准）。

```bash
REPO=/Users/zhangzhuo/repos/kepler-conjecture-lean4
LP=$(cat /tmp/lfainteg/asm_check/leanpath.txt)
FARM=/tmp/reachfarm/lib
cd $REPO

# 全量多根（默认；约 20–25 min）
LEAN_PATH=$FARM:$LP nice -n 19 lean lean/scripts/global_reach_map.lean > /tmp/global_reach.out

# 冒烟（只跑前 3 个根；union/ORPHANS/SHIMS 仍按全根计算）
LEAN_PATH=$FARM:$LP GLOBAL_ROOTS_LIMIT=3 \
  nice -n 19 lean lean/scripts/global_reach_map.lean > /tmp/global_smoke.out
```

输出段：`ROOTS_*` → `--- PER-ROOT ---`（154 行）→ `--- UNION ---` →
`--- UNION SORRIED ---` → `--- UNION AXIOMS ---` → `--- ORPHANS ---`
（计数 + 前 50）→ `--- SHIMS ---`（21 行）→ `--- END ---`。

## 8. 下一步建议

1. **补跑 156 根**：交付脚本已修正 capstone 全名；补跑后把 §3 的 union 读数升级为
   156 根版本（预期 K_REACH 增加 PA25 `OXLZLEZ` + `PACKING_CHAPTER_MAIN_CONCLUSION`
   的闭包，K_SORRIED 至少增加 `OXLZLEZ` 的 31 个源中的未重叠部分）。
2. **ORPHANS 分诊**：先过滤编译器生成件（`casesOn`/`recOn`/`_flat_ctor`/`rec`），
   再看 theorem/def 孤儿；`Assembly.IdLists` / `IneqPilot` 是当前最大孤儿簇，判断是
   「未接线资产」还是「死代码」。
3. **SHIMS 3 条红线**：`GRUTOTI1_concl` / `QXSKIIT_concl` / `UPFZBZM_concl` 已有
   discharge 但仍 sorried，优先核对 discharge 是否真正承接（Stage-1/F1 类假债）。
4. **页面数据**：e2e 节点表用 `DUMP_TREE=1`（见 e2e 文档 §v2.4），`generated` 列
   默认可折叠 2M 级证书层；模块聚合表（TOP30 by nodes / TOP10 by sorries）会先于
   节点表打印。
