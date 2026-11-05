# WORKORDER-next — `RRCWNSJ_p26`（LA26:829）解堵前置

基线 HEAD `8c003d0d`。本车道（la26-rrcwnsj-w1）判 **BLOCKED**；本文给出精确解堵清单。
证据见 `DELIVERY.md` §1/§3 与 `Evidence.md` §3/§5/§6。

## 0. 先纠正分诊的两条口径

1. **`JCYFMRP_V3_p29` / `JLXFDMJ_p27` 不在本件证明路径上**：
   `grep -c "JCYFMRP\|JLXFDMJ" lean/scripts/local/RRCWNSJ.hl` = **0**。
   分诊/RANKED §车道1 的"若 Lean 侧确实需要"猜疑不成立；工单要求附的 25 行 HOL 锚
   `HIJQAHA.hl:3487-3512` 属 **`SCS_4I2_IMP_SCS_4T1_p33` → `HIJ_STEP_1` 那条链**（m1a-root-w4
   DELIVERY 已记），与本件无关，此处仅登记备查，**不是**本件的解堵项。
   → 后续若再派人做本件，不要在 `JCYFMRP_V3`/`JLXFDMJ`/`CUXVZOZ`/`general_482_deformation`
   上花预算。

2. **补一个分诊没列的真前置**：HOL 的 624 行 bash 实引 `ODXLSTCv2`（`RRCWNSJ.hl:345`、
   `:615`）与 `IMJXPHRv2`（`:511`、`:802`），这两台是 k=6 lunar 案核（ears 析取 +
   a-紧性），HOL 原体分别在 `ODXLSTC.hl` / `IMJXPHR.hl`（11028 行）。分诊的前置清单
   漏了它们。

## 1. 目标的可证性现状（已机器验证）

已交付并编译通过（`Work.lean` / `Kit-draft-la26-rrcwnsj-w1.lean`）：

```
w5sgd_generic_of_no_lunar_p26 :
  isScsV39 s → MMsV39 s v → 3 < s.k →
  (¬ ∃ v' w, Lunar v' w (Set.range v) (Set.range fun i => {v i, v (i+1)})) →
  scsGeneric v
```
`#print axioms` = `[propext, choice, Quot.sound]`；整文件 RC=0、0 error、own-sorry 3（未变）。

即：**目标 = 单一命题 `hnoLunar`**（无 `Lunar` 对），其余装配（¬Circular、CIZMRRH 三分、
fan 桥、lunar_p3 ↔ Lunar）全部真证可用。剩余工作量集中在 `hnoLunar`。

## 2. 解堵项（按性价比排序）

### 阻塞项 B1（必需）：拿到 clean 的 `ODXLSTCv2` / `IMJXPHRv2`

| 形 | 位置 | 实测公理面 | 在 LA26 闭包 |
|---|---|---|---|
| `ODXLSTCv2_concl` | LA1:2917 | `sorryAx` | ✓（但 TAINTED） |
| `IMJXPHRv2_concl` | LA1:2928 | `sorryAx` | ✓（但 TAINTED） |
| `ODXLSTCv2_p28` | LA28:8077 | 标准三 | ✗ `#check` unknown |
| `IMJXPHRv2_p28` | LA28:8057 | 标准三 | ✗ `#check` unknown |

三条路线：

- **路线 A（推荐，最省）**：给 `lean/Kepler/Text/LocalAuto26.lean` 加
  `import Kepler.Text.LocalAuto28`，目标体消费 `ODXLSTCv2_p28` / `IMJXPHRv2_p28`。
  - 无环证明（BFS，`closures28.py`）：LA28 闭包 = 115 模块，含
    `{LA1,17,34,35,37, OdxlstcBridge, Mathlib…}`，**不含 LA26**；LA26 的上游导入者只有
    `{LA16, LA29, LA33, LocalConcl}`，故 `LA26 → LA28` 无环。
  - 但要按车道契约做**全文件漂移核**：import 前后 warning 谱面逐条一致；≥10 件既有件
    `#print axioms` 零漂移；`grep` LA28 新进闭包的公开名与 LA26/下游重名；下游
    （LA16/LA29/LA33/LocalConcl）重建核。**这不是行为保持变换**，需单独立项。
  - 工作量估计：漂移核 1 波（约 30–50 调用），装配 1 波。
- **路线 B**：在 LA26 文内就地重制两台引擎（沿 `_p28` 的证法）。需要 `IMJXPHR_p34`
  级 V3_DEFOR / MHAEYJN / ZLZTHIC 变形机器（LA34 闭包外，11028 行章）；本车道判不可靠。
- **路线 C**：在 LA1 原位补 `ODXLSTCv2_concl`/`IMJXPHRv2_concl`。**注意 LA1 在 LA28 之下**，
  不能用 `_p28` 反委托；只能在 LA1 重写巨件，等价路线 B 且更贵。不推荐。

### 阻塞项 B2（装配期要处理的排序问题，非数学阻塞）

`AXJRPNC_p26`（LA26:1307）与 `w3sg_helim_p26`（:1274）、`DIST_LE_2h0_IN_CASES_6_p26`（:841）、
`DIST_EDGE_IN_BB_LE_2_p26`（:855）都在目标（:829）**之后**。两种处理：
- 把目标定理块整体下移（例如移到 `AXJRPNC_p26` 之后）——纯位置调整，签名逐字不动；
- 或把 `AXJRPNC_p26` + `w3sg_helim_p26` + `DIST_LE_2h0_IN_CASES_6_p26` +
  `DIST_EDGE_IN_BB_LE_2_p26` + 其消费的 `w3sg_*`/`DIST_LE2_BB_CASSE_4/5` 块上移。
  （本车道不改排序，避免在 BLOCKED 状态下制造大 diff。）

## 3. 解堵后的装配配方（HOL 逐段 → Lean）

| HOL 段 | 内容 | Lean 落点 |
|---|---|---|
| :251-273 | strip、MMs→BBprime、JKQEWGV2、BBS→ConvexLocalFan、CVLF_LF_F、CIZMRRH、LUNAR_IN_V、AXJRPNC | **已由 `w5sgd_generic_of_no_lunar_p26` 覆盖到最后一步**；AXJRPNC 用 `AXJRPNC_p26`（标准三）或 `w5sg3b_axjrpnc_p26`+`helim` |
| :274-291 | `norm (v (SUC x)) = 2 ∨ norm (v x - v (SUC x)) = 2` | `B_LE_2h0_A_EQ2_IN_CASES_6_p26`（a=2）+ `IMJXPHRv2_p28`（tightness）→ dist=2 |
| :291-338 | 严格 a 界（`∀ i, ¬(i≡x+1) → a < dist`） + `CHANGE_W/A_SCS_MOD` | 文内 `periodic2_mod_eq_p26` 已覆盖 `CHANGE_*`；`scsDiag` mod 不变式用 `w5sg_diag_mod_p26` |
| :341-401 | `J_EMPY_CASES_6` + `ODXLSTCv2` + `JKQEWGV3` → 两个 `¬lunar` 子目标 | `J_EMPY_CASES_6_p26` + `ODXLSTCv2_p28`(l=SUC x) + `JKQEWGV3_p23` |
| :419-527 | `azim = π` 支（`BB_RHO_NODE_IVS`、`CARD_V_EQ_SCS_K1`、`VV_SUC_EQ_RHO_NODE_PRIME`、`LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT`、`decomposition_planar_by_angle_fan`、`POINT_IN_AFF_GE_IMP_IN_EDGE`、`IMJXPHRv2`） | `BB_RHO_NODE_IVS_p26` ✓；`CARD V = k` 用 `w5sg3b_axjrpnc_p26` 内的就地重制路线或 `w5sg_hedge` 系；`VV_SUC_EQ_RHO_NODE_PRIME` 需就地重制（LA35 闭包外不便）或避开；其余 LA5/Planarity 件在闭包内（实测标准三） |
| :530-803 | 上述 `x+k-1` 处逐条镜像 | 同表，l := x+k-1；`w5sg_diag_ends_p26` + `B_LE_2h0…`/`DIST_LE_2h0…` 供 `hc : cstab ≤ dist` |
| :816-855 | 终局：`DIST_LE_2h0_IN_CASES_6` + diag `cstab ≤ dist` + `JKQEWGV3`(<π/2) vs `SYNQIWN`(>π/2) + `BB_RHO_NODE_IVS` | 全绿：`JKQEWGV3_p23`、`SYNQIWN_p22`、`BB_RHO_NODE_IVS_p26`、`w5sg_diag_ends_p26`（均实测标准三） |

## 4. 验收（解堵波应达到）

- `#print axioms Kepler.Text.RRCWNSJ_p26` = `[propext, Classical.choice, Quot.sound]`；
- 整文件 standalone RC=0、`grep -c ': error:'` = 0、own-sorry 3 → 2；
- kit 只含 `lean/Kepler/Text/LocalAuto26.lean`；若走路线 A，kit 含 1 行 `import`，必须附
  漂移核证据（warning 谱面逐条、≥10 件 axioms 零漂移、重名 grep）；
- 陈述冻结：目标签名 8 行 md5 与 HEAD 一致（本车道已给基线 md5 `23c6800c…`）。

## 5. 预算建议

- 路线 A：漂移核 + 装配 ≈ 2 波、每波 ≤120 调用；装配体量估计 **150–250 行 Lean**（w5a
  DELIVERY §6 同估）。
- 路线 B/C：不建议在单车道内尝试（LA34/LA31 巨件闭包外，或需在 LA1 重写 11028 行章）。
