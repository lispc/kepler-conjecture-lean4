# WORK ORDER — `textside-triage`（用户已同意：Text 侧 23 条 triage，只侦察不施工）

> 状态：**用户 2026-11-06 已同意**（"二。同意。"）。
> 性质：**只读侦察**。不写 Lean、不改主仓、不编译。允许 grep / python3。

## 0. 为什么做

锥内 82 条 sorry = **59（Assembly）+ 23（Text 侧）**。这 23 条**从没作为一组处理过**：
它们不依赖证书、不依赖 `weaklySaturatedP22`，多数是"HOL 80–200 行"的中等件——是当前
**ROI 最高**的一块。先摸清每条的 HOL 源、在树前置、估行数，再决定批次。

## 1. 对象（23 条，**权威清单** = `docs/e2e-reachability-map.tsv` 的 `--- SORRIED ---` 段中非 Assembly 的 23 行）

```
LocalAuto15.VPWSHTO_p15                         LocalAuto30.UAGHHBM_p30
LocalAuto20.SCS_6I1_BERAK_BY_CSTAB              LocalAuto32.MIQMCSN_p32
LocalAuto21.general_482_deformation_p21         LocalAuto32.NWDGKXH_p32
LocalAuto22.OCBICBY_p22                         LocalAuto32.YOBIMPP_p32
LocalAuto23.LFLACKU_p23                         LocalAuto33.MM_4I2_IMP_4T2_4T1_p33
LocalAuto26.RRCWNSJ_p26                         LocalAuto33.SCS_4I1_IMP_SCS_4I2_p33
LocalAuto27.JCYFMRP_p27                         LocalAuto33.SCS_4I2_IMP_SCS_4T1_p33
LocalAuto27.TFITSKC_p27                         LocalConcl.{mnt11_anchor, p21_anchor}
LocalAuto29.SCS_5M2_IMP_SCS_5T1_p29             PackingAuto13.URRPHBZ2
                                                PackingAuto25.{ox3q1hP25, pkLeafRankCriticalEdge,
                                                               real_model_ox3q1h_merge}
                                                TameLp.fully_surrounded_perimeter_bound
```

## 2. 每条要填（输出 TSV）

| 列 | 含义 |
|---|---|
| `decl` / `module` / `line` | 位置 |
| `hol_src` | HOL 出处（文件名:行号；在 `reference/flyspeck/` 里 grep 得到） |
| `stmt_kind` | 命题类型（实分析界 / 图论 / 组合计数 / 定义搬运 / 其它） |
| `prereq_state` | 它依赖的每个前置：`在树已证` / `在树但 sorry` / `不在树` |
| `blocked_by` | 若不可做，卡在谁 |
| `cert_free` | 是否需要证书（这批应当全是 `yes`） |
| `est_lines` | 估行数（30 / 80 / 150 / 300+） |
| `risk` | 低/中/高 |
| `batch` | 建议批次（同前置/同型归一组） |
| `notes` | 已知坑（例如 `ox3q1hP25` 是 `Prop := sorry` 语句级缺口、`*_anchor` 是局部锚） |

## 3. 必须特别标注的三条

1. **`ox3q1hP25`**（`PackingAuto25:90`）：`def … : Prop := sorry` —— **语句级缺口**，
   不是"没证"而是"命题未知"。它的 HOL 真身是 `Oxl_def.hl`，属 C（占位桩审计）那一类，
   请标注它与 `w5-stub-audit` 的交叉。
2. **`mnt11_anchor` / `p21_anchor`**（`LocalConcl`）：私有锚件，弄清它们是否只是"占位转接"。
3. **`fully_surrounded_perimeter_bound`**（`TameLp`）：与 tame 章的 perimeter 界相关，
   查它是否已被 tameCorr 章的某件替代（`docs/archive/lane-archives/tamecorr-w3/`）。

## 4. 硬纪律

- **不写 Lean、不改主仓、不编译 Lean**；`/tmp/texttriage/` 工作；产物 → `~/c17_backup/lane_snapshots/textside-triage/`。
- 引用 HOL 行号必须真 grep 到，不许"大概在某文件"。
- 引用在树前置必须给 `文件:行号`，并标注是否 sorry（用 `docs/e2e-reachability-map.tsv` 的 SORRIED 段落交叉验证）。

## 5. 交付

`~/c17_backup/lane_snapshots/textside-triage/{TEXT23.tsv,TEXT23.md,scripts/,logs/}`。
回我 ≤15 行：可做（cert-free 且前置全绿）几条（逐条 decl + 估行数）、需先补前置几条、
语句级缺口几条、建议的前两批（含共享件）、以及"保守能闭多少条"的一句判断。
