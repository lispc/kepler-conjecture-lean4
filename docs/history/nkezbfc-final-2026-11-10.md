# NKEZBFC_FINAL — stepB 链结案报告（v4 收口 + 边界清单 + HOL 对应）

## 0. 一句话
`0 ≤ solLocal_p9`（stepB）的新链**除单一 w 侧 1_2 边界外全部在库、全部标准三
零 sorryAx**；该边界与 HOL 的对应关系 = **隐式依赖**（NKEZBFC.hl 脚本内不可
独立摘录；HOL 证明本身完整无 sorry——不得写成「HOL 假设形」）。

## 1. 链最终形态（v4 层 + 边界）
```
pW19_nkezbfc_prep_p9_v4 (h := EJRCFJD_concl_p9) (hslots := (hstep-run, hprev-v2))
  └─ pW24_stepB_sol_nonneg_v4        -- hstep-run + hprevC1 + hprevC2
       └─ pW19_stepB_sol_nonneg_v4   -- hstep-run + hprev-v2（w 侧 pW5w_telescope 逐字 v2）
            └─ pW6k8_stepB_sol_nonneg_affGe_v4   -- hstep-run 直传；w affGe→径向零点
                 └─ pW6k7_stepB_sol_nonneg_v4     -- K 案 u 侧放电 = pW28_slot_u_at
```
**槽状态**：
- `hstep`（run 前件形）→ **可消**：`pW30_hstepEG`（EGHNAVX 语境，放电 =
  一行 `pW26_hstep_at_run`）；抽象槽补全 = `pW30_hstep_wire`（端点补强三项，全部在库）。
- `hslot_w`（诚实域 `0<j`，W27 桥）→ **仍为边界**（w 侧 1_2 族）。
- `hprevC1` → **后跳段在库**（`pW30_hprevC1`：`i+2 ≤ n ≤ k−1`）；前跳段
  `2 ≤ n ≤ i+1` 仍为边界（同源）。
- `hprevC2`（= cross-dot/det 绕序）→ **边界**（= hslot_w 同一缺口）。

## 2. 边界清单（唯一真几何缺口）
**B1 = w 侧 1_2 族**：`∀m, (跳跃后段) → vv m ∈ affGt ({0}) {p, vv(m-1)}`
（含 hprevC2 与 hslot_w 消费面）。等价网（全在库 std3）：
`pW20_hprev_iff_21`（hprev ⟺ C1∧C2）、`pW22_c2_iff_det`（C2 ⟺ det<0）、
`pW24_c2_iff_crossdot`（C2 ⟺ cross-dot<0）、`pW5w6_radial_iff_azim`。
形式化边界件：`WindingSlot V FF`（LocalFanStepW32.lean，WINDING_SCOUT §5 签名，
def 零公理；"与 hstep/hprev 同级、DIFFERS 记档"）。

## 3. 与 HOL 的对应关系（逐项）
| 面 | HOL | 我们 | 状态 |
|---|---|---|---|
| th3 簇 | fan.hl:357–388 | `pW36_th3a12/th3a/th3b/th3b1/th3c/th3d/th3`（LocalFanStepW36） | ✅ 逐字对件 |
| u-run hstep 直供 | EGHNAVX 首 run（:2271–:2300） | `pW26_hstep_at_run` | ✅ |
| w 侧 union 望远镜（∀j） | NKEZBFC.hl:2345–2400 | `pW35_union_of_family`（骨架，hfam 接口） | ✅ 结构 / hfam=边界 |
| 早一格排除 | :2455–2583（EE 路线） | `pW33_edge_cone_excl`（+mirror，更短原语） | ✅ |
| J 收尾 wrap 基点 | :2499–2583（j=0 端） | `pW34_rho_last_mem` | ✅ |
| **w 侧 1_2（H 步 h4）** | **隐式依赖**（:2376–2406 的 `ASM_REWRITE` 关闭，无可见供给；W38/W39 两波机器核：假设束零 aff、G 段仅 2_1、全文件 1_2 成员零命中） | `WindingSlot` 边界 | ⚠️ **隐式依赖**（非假设形） |

## 4. 件清单（全库 std3 零 sorryAx，按波）
W6K3① `pW6k2_affGt_nonempty`（117 行）· W26 `pW26_hstep_at_run`（62）·
W27 `pW27_wslot_zero_false`/`pW27_hslot_w_iff`（103）· W28
`pW6k7_stepB_sol_nonneg_v4`/`pW6k8_stepB_sol_nonneg_affGe_v4`（319，含私支）·
W29 `pW19_stepB_sol_nonneg_v4`/`pW19_nkezbfc_prep_p9_v4`/`pW24_stepB_sol_nonneg_v4`（167）·
W30 `pW30_hprevC1`/`pW30_hstepEG`/`pW30_hstep_wire`（120）· W32 `pW32_w_cone`+`WindingSlot`（109）·
W33 `pW33_edge_cone_excl`/`_mirror`（99）· W34 `pW34_rho_last_mem`（68）·
W35 `pW35_union_of_family`（124）· W36 th3×7（140）。

## 5. 判读与建议
1. **NKEZBFC stepB 现可条件形收口**：唯一显式边界 = `WindingSlot`/1_2 族；
   其余槽（hstep）已真放电，C1 后跳段已供。
2. **与 HOL 同信任类别的判读**：HOL 对 1_2 为隐式依赖且证明完整；我们保留
   显式边界属**同等信任类别**的合理定案（标注「隐式依赖」，不写「假设形」）。
3. 若要把 B1 从边界降为定理：唯一正确入口 = 重新取得 HOL 对应段的**可执行
   proof state**（本地无 HOL 工具链，脚本静态分析已到极限：W37/W38/W39 三波
   机器核已把「可见文本面」穷尽）。备选 = 新立项独立攻 w 侧 1_2 几何
   （W23 绕序核心，估 200–400，成功率未定）。

## 6. 附录（W40 追加，append-only；commit `ae463ff8`，2026-11-10 11:43）

§4 件清单追加 6 件（`LocalFanStepW40.lean`，263 行，全 std3 零 sorryAx）：
`pW40_G1_u_mem`（HOL :2063，2_1 u 侧锥）· `pW40_G2_w_mem`（:2081，经
`vv(k−1)=ivs` + 周期回卷；**域注 `i+1 < k−1`**，边沿归 wrap 支，未覆盖）·
`pW40_G3_azim_range`（:2120/:2123）· `pW40_G7_rho_g_mem`（:2194/:2224，
`azim_eq_azim_iff` 链）· `pW40_G6_union`（:2143，成员 iff 形，HOL 集合等式经
`Set.ext` 还原）· `pW40_slot_of_family`（W35 §2 补全：hfam ⇒ J 收尾
`ρ(vv(i+1)) ∈ affGe{0}{v, vv(i+1)}`）。

**未单列对表**：W37 钉死的 G4（`ρu=w`）/G5（`ιw=u`）——G4 = `iterate_succ`
恒等（消费时一行）；G5 需 ivs-周期引理（`ivsRhoNode1 (vv(i+1)) = vv i` 经
`(ρ)^[k−1]` + 周期；未验证，消费时补）。当前链无消费者，不造件充数。

**ERRATA（W40 自纠，whnf 4M 超时根因）**：真根因**不是** Nat 减法下标，而是
`have hnc : ¬Collinear3 … := LOCAL_FAN_CHARACTER_OF_RHO_NODE2 …` 的**类型注解**
（插件结论含 `ρ(vv(i+1))`，与注解 `vv(i+2)` 非 defeq ⇒ 统一死循环）；修复 =
未注解原形 + `show; rw[←hρ]; exact`。同机理解释 W35 §2 旧超时。

**边界判读不变**：B1 = w 侧 1_2 族仍是唯一真几何缺口（§2/§3 不动）。

## 7. 附录二（W42 追加，append-only；commit `ddec2058`，2026-11-10 12:03）

**v4 链签名最终收紧**（W42A，407 行 5 件）：weak 形 hstep 槽（`hflat/hnc`
前件、域 `n+1≤i`）在端点缺三项补强（W30 证据）⇒ 不作假设；全部换 EGHNAVX
语境形，`pW30_hstepEG` 定理一行放电。五件 `pW42_pW6k7_v4 / pW6k8_v4 /
pW19_v4 / pW24_v4 / prep_v4`；与 v4 原件 body 机器 diff：pW6k8/pW24 零差异、
pW6k7 仅 K 案 hS3 放电调用、其余仅注释。

**hNKE provider（hia 形）**（W42B，124 行 3 件）：`pW42_hNKE_hia (hB1)` ——
hB1 = hslots.2 逐字；极扇凸性/generic 由 `p11w2_polar_*_of_eq` @ hia 供
（HOL polar_fan.hl:2552–2568 的 hia 分支同形；W13F 的 hNKE 无 hia 槽是渲染
时漏前提）。`pW42_WSEWPCH_hia_aux` 与 W13F aux body 机器 diff 仅 1 行；
`pW42_perimeter_hia_v4 (hB1) (hcl) (hedge) : fanPerimeter ≤ 2π`。

**父件条件形**（`20506a3a`，编排者亲作）：`pW43_parent_perimeterBound_of_fullySurrounded
(hB1) (hfan) (hfs) : PerimeterBound V E hfan`。TameLp 无条件陈述零改动。

**结论更新（取代 §5.1 的槽状态）**：`hstep` 已**真放电**（定理，不进签名）；
唯一显式边界 = **B1**（w 侧 1_2 族）。条件形链路完整：B1 ⇒ PerimeterBound。
