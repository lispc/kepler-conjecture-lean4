# LA3 WRGCVDR 巨人波交接（2026-10-09）——BIJ_BETWEEN_FF_AND_V 真证落地

## 结论

**主目标 `BIJ_BETWEEN_FF_AND_V`（LocalAuto3.lean，WRGCVDR.hl:2548）真证闭合**，
连带填掉 6 条上下游前置。LA3 sorry 18 → 11，全部 7 条 axiom audit =
`[propext, choice, Quot.sound]`（零 sorryAx、零新公理）。

## 本波闭合（7 条）

1. **`BIJ_BETWEEN_FF_AND_V`**（主目标）——绕开 HOL 的 TOW_BIJS 组装（那需要
   FAN_IMP_BIJ_V_NODE_OF_HYP/LOCAL_FAN_IMP_BIJ_FF_NODES 两个 ∃-form 巨人，
   其本体需构造 Hypermap 结构 = FIRST_AAUHTVE，仍 sorry），改直构：MapsTo
   （FF⊆darts）；SurjOn（`DIH_IMP_EVERY_NODE_INTER_FACE` + `choose_nd_point`）；
   InjOn（同 fst ⟹ 同 node-orbit（单循环性）⟹ 同 face-orbit
   （`HAS_ORDK_IN_ORBIT_IMP_SAME_ORBIT`）⟹ `Simple` 消灭）。
2. **`CYCLIC_SET_IMP_STABLE_SET2`**（hl:2080）——关键外部供给：TopologyFan
   已证的 `orbit_eq_setOfEdge`（σ-轨道=setOfEdge 单循环性）+ LA3 已证
   `ITER_AZIM_CYCLE_EQ_ITER_SIGMA`。新增 `import Kepler.Text.TopologyFan`
   （无环，下游接口零变化）。
3. **`IN_NODE_IMP_FIRST_EQ`**（hl:2519）——nnOfHyp 两分支都保 first 分量。
4-7. **`DIH2K_IMP_PRE_SIMPLE_HYP`/`DIH2K_IMP_SIMPLE_HYPERMAP`/
   `DIH_IMP_EVERY_NODE_INTER_FACE`/`DIH2K_IMP_NODE_MAP_X_DIFF_X`**——抽象
   hypermap 四件套（基数反证 + hasOrders-2 轨道刻画 + dart 覆盖分解）。

新增私件 7 条（全 `private`，插在 CYCLIC 前）：`p3_nodeMem_iterate`/
`p3_faceEqOrbit`/`p3_fst_iterate`/`p3_preSimple`/`p3_simple`/`p3_everyNode`/
`p3_same_fst_node`（组合论核：同 fst dart 同 node-orbit）。

## 级联验证报告（LA5 只读，未触碰）

- **数学核已打通**：HOL `local_lemmas.hl:69` 的 `LOCAL_FAN_RHO_NODE_PROS` 从
  BIJ_BETWEEN 仅 15 行可导（ρ 用 SURJ 见证、FF 内第二分量由 INJ 唯一化）→
  LA5 的 `LOCAL_FAN_RHO_NODE_PROS/PROS2`（:186/:1008）、
  `LOCAL_FAN_CHARACTER_OF_RHO_NODE` 随之机械闭合；orbit 侧经 WRGCVDR 主定理
  → `LOCAL_FAN_ORBIT_MAP_V`（:1003）→ `LOFA_IMP_BIJ_VV`（:1812，
  `SELF_CYCLIC_IMP_BIJ` LA5 已证）→ OZQVSFF（:1833）→ LUNAR（:2925 处已写好
  实例化，自动转真）。
- **剩余断点（诚实）**：OZQVSFF 在 **p2 lane**，其前置全部是
  `localFan_p2`/`rhoNode1_p2` 词表；p2 侧 **`WRGCVDR_BIJ`（LocalAuto2.lean:545）
  本轮未动**。LA5 的 `LOFA_IMP_BIJ_FF_V := WRGCVDR_BIJ h`、
  `LOFA_IMP_CARD_FF_V_EQ`（已写好真体）随其转真。
- **下轮配方（~400-500 行）**：把本波私件块镜像到 LA2 的 `_p2` 词表——
  `orbit_eq_setOfEdge` 直接 import TopologyFan 可用；需移植
  `AZIM_CYCLE_EQ_SIGMA_FAN` p2 版（~50 行，SIGMA_FAN/unique_azim_point_fan
  均 Fan 模块可 import）、`ITER_AZIM_CYCLE_EQ_ITER_SIGMA`/`N_HYP_TO_AZIM_CYCLE_LEM`
  p2 版（~80 行）；或 lane-dedup 合并时 p2 消费者直接取 p3 证。
- LA3 剩余 11 巨人中与本链相关的：`WRGCVDR` orbit 半（face-orbit 展开，
  hl:2622 后半）；`FAN_IMP_BIJ_V_NODE_OF_HYP`/`LOCAL_FAN_IMP_BIJ_FF_NODES`
  （需 FIRST_AAUHTVE 的 `e∘n∘f=I` 构造，可由 `IVS_AZIM_PROPERTIES` 得，
  ~80 行，非级联必需）。

## 新雷区（本波实测）

1. **本 Mathlib 的 `Set.ncard` 是 ℕ 值**（非 ℕ∞）——基数反证直接 omega 收尾，
   勿标 ℕ∞ 强制转换。
2. `Set.ncard_image_le` 的 `hs` 是 autoParam(finiteness)，超类链复杂处会炸
   "could not synthesize 'hs'"——显式 `(hs := hfin)`。
3. `Equiv.Perm` 的 `^n` 与 `f^[n]` 的桥是 `Equiv.Perm.coe_pow`；`Hypermap.Simple`
   是 def，`rw` 无方程引理，用 `intro`/`show` 直接进 ∀。
4. 冻结陈述里 `_h`/`_hd` 等下划线前缀假设在证明体不可达——用
   `‹localFan_p3 V E FF›` 型标注取回。
5. `rw` 产生的 eta 展开目标（`(fun d => d.1) t`）会挡 `rw [引理]` 的语法匹配
   ——改 `exact 引理 参数`（beta 可解）。
