# RANKED — 下一批 3 条车道建议（锥内 Text 层，除 PA25）

读时 HEAD：`8a91eaaa` → 期间其他车道推进到 `b49461bb`（PA25 w3 6c27796d / LA11 4ab6a8e7 落库）。
下列行号按 `b49461bb` 工作树复核过；若再推进需重核。

判据口径见 `DELIVERY.md` §1（class=可证性闸门；BLOCKED 行在 next_action 里带本体尺度与最近前置）。

---

## 车道 1（推荐首选）：`w4_rrcwnsj_p26`

- **目标件**：`Kepler.Text.RRCWNSJ_p26` — `lean/Kepler/Text/LocalAuto26.lean:829`
- **前置是否全绿**：**是**（按 DISCHARGES/NEEDS 注记点名的 3 件，递归闭包 0 sorry）
  - `MMS_IMP_BBPRIME_p28` — `lean/Kepler/Text/LocalAuto28.lean:194`，`:= by` 体，闭包 0 sorry
  - `JKQEWGV2_p23` — `lean/Kepler/Text/LocalAuto23.lean:4759`，`:= by` 体，闭包 0 sorry
  - `BBS_IMP_CONVEX_LOCAL_FAN_p34` — `lean/Kepler/Text/LocalAuto34.lean:1025`，`:= by` 体，闭包 0 sorry
  - HOL 侧其余件也已在库且已证：`CIZMRRH`（LocalAuto3:2734）、`CVLF_LF_F`（LocalAuto5:6740）、`LUNAR_IN_V_p26`（LocalAuto26:224）、`AXJRPNC_p26`（LocalAuto26:1307）、`DIST_EDGE_IN_BB_LE_2_p26`（LocalAuto26:855）、`B_LE_2h0_A_EQ2_IN_CASES_6_p26`（LocalAuto26:230）、`CHANGE_A_SCS_MOD_p28`（LocalAuto28:230）、`CHANGE_W_IN_BBS_MOD_IS_SCS_p28`（LocalAuto28:255）
- **预计行数**：**M，250–400 行**（HOL `reference/.../local/RRCWNSJ.hl:248-872` = 624 行 tactic bash，多为既有引理的 `MRESAL_TAC` 分派）
- **验收期望**：`LocalAuto26.lean` own-sorry N→N−1；`#print axioms Kepler.Text.RRCWNSJ_p26` = `[propext, Classical.choice, Quot.sound]`（当前含 sorryAx，见 Evidence.md 探针）
- **如果这条也 BLOCKED，最可能卡在哪**：HOL 证明体除 NEEDS 三件外**还引** `JCYFMRP_V3`（Lean 孪生 `JCYFMRP_V3_p29`，`LocalAuto29:3601`，sorry）与 `JLXFDMJ`（孪生 `JLXFDMJ_p27`，`LocalAuto27:559`，sorry）。若 Lean 侧确实需要，则卡在
  - `JCYFMRP_V3_p29`（S，HOL `HIJQAHA.hl:3487-3512` = 25 行）← `JCYFMRP_p27`（M，363 HOL 行）← `CUXVZOZ_p21`（LocalAuto21:1203 已证）← `general_482_deformation_p21`（L，640 HOL 行，自身 7 条前置全 sorry）
  - `JLXFDMJ_p27`（L，HOL `JLXFDMJ.hl:227-819` = 592 行）
  → 这条车道应**先做 100 行以内的可行性探针**：把 HOL 证明逐段映射到 Lean，确认 `JCYFMRP_V3/JLXFDMJ` 是否真的必需；若必需，本车道降级为 BLOCKED，改发车道 3。

---

## 车道 2：`w4_la33_straight`

- **目标件**（3 件，一条链）：
  1. `SCS_4I2_STRAIGHT_p33` — `lean/Kepler/Text/LocalAuto33.lean:2059`
  2. `SCS_4I2_STRAIGHT_ALL_p33` — `lean/Kepler/Text/LocalAuto33.lean:2065`
  3. `MM_4I2_IMP_4T2_4T1_p33` — `lean/Kepler/Text/LocalAuto33.lean:2126`
- **前置是否全绿**：**是**（全部 `:= by`，闭包 0 sorry）
  - `ear_acute_p33` — `LocalAuto33:2002`（proved，STRAIGHT 的唯一外部几何输入）
  - `ASSUME_MIN_DIAG_p33` — `LocalAuto33:1930`；`XWNHLMD_MM_p33` — `LocalAuto33:527`
  - `SCS_4I2_3_LE_A_p33` — `LocalAuto33:1957`；`SCS_4I2_STRAIGHT_ALL_p33` 的 4 个 azim 结论按 residue 实例化
  - `DIST_DIAG_2_CASES_EQ_3_p33` — `LocalAuto33:1900`；`SCS_DIAG_ADD1_p33` — `LocalAuto33:1922`；`BB_VV_FUN_EQ_p26` — `LocalAuto26:198`；`MMS_IMP_BBS_p28` — `LocalAuto28:194`
  - `SCS_4T1_IS_SCS_p33` / `SCS_4T2_IS_SCS_p33` — `LocalAuto33:1363/1367`
- **预计行数**：**S + S + M ≈ 210–310 行**（HOL：STRAIGHT `ARDBZYE.hl:1813-1919`=106 行、STRAIGHT_ALL `:1919-1965`=46 行、MM_4I2 `:2339-2514`=175 行）
- **验收期望**：`LocalAuto33.lean` own-sorry N→N−3；三件 `#print axioms` 均标准三
- **如果这条也 BLOCKED，最可能卡在哪**：
  - `SCS_4I2_STRAIGHT_p33` 需要把 `ear_acute_p33` 的结论接到 `azim 0 (v i) (v (i+1)) (v (i+3)) < π`，中间要 `4I2` 实现的 y-坐标显式化（HOL 走 `SCS_4I2_GENERIC` + `BB_RHO_NODE_IVS`）；若 `BB_RHO_NODE_IVS_p26`（LocalAuto26:325，proved）的 Lean 接口形不匹配，会卡在角度/方位桥。
  - `MM_4I2_IMP_4T2_4T1_p33` 的 `ASSUME_MIN_DIAG` 应用处要逐槽给隐参（参考 playbook §6 NC2 七条），否则 unifier 烧穿。
  - 注意：`SCS_4I2_IMP_SCS_4T1_p33` 的 NEEDS 注记声称吃 `EDGE_EQ_2_4I2_*`，但 HOL 证明体（`:1357-1439`）实引 `RRCWNSJ/JCYFMRP_V3/JLXFDMJ/XWNHLMD_MM`；本车道 3 件**不需要** `EDGE_EQ_2_4I2_*`（那 4 条自身又卡 `CUXVZOZ`）。

---

## 车道 3：`w4_la32_4m6`

- **目标件**（5 件，4M6 分支一条线性梯子）：
  1. `EXTREMAL_SCS_4M6_p32` — `LocalAuto32:993`（M，80–120 行）
  2. `BB_4M6_IMP_scs_4T3_p32` — `LocalAuto32:1002`（S，~40 行）
  3. `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32` — `LocalAuto32:1020`（M，80–120 行）
  4. `MM_4M6_IMP_MM_4T3_p32` — `LocalAuto32:1010`（S，~30 行）
  5. `NWDGKXH_p32` — `LocalAuto32:1030`（S，~30 行；TSV 锥内行）
- **前置是否全绿**：**是**（第 1 件的 4 条前置 + 梯子其余装配件全 proved）
  - `MMS_IMP_BBS_p28` — `LocalAuto28:194`；`BB_VV_FUN_EQ_p26` — `LocalAuto26:198`
  - `SCS_4M6_STAND_OR_PRO_p32` — `LocalAuto32:960`；`VASYYAU_p25` — `LocalAuto25:2541`
  - `STAB_MOD` — `LocalAuto20:1655`；`YRTAFYH_p17` — `LocalAuto17:1129`；`SET_STAB_4M6_ARROW_4T5_p33` — `LocalAuto33:4298`
- **预计行数**：**M + S + M + S + S ≈ 260–340 行**
- **验收期望**：`LocalAuto32.lean` own-sorry N→N−5；`NWDGKXH_p32` `#print axioms` 标准三（锥内 SORRIED −1）
- **如果这条也 BLOCKED，最可能卡在哪**：
  - `EXTREMAL_SCS_4M6_p32` 的 `str` 分支（`SCS_4M6_STAND_OR_PRO_p32` + `VASYYAU_p25`）的**形式匹配**——HOL 是 `case split on str`，Lean 侧 `ScsV39.str` 字段的命题形若与 HOL 不同，需要一次 DEF-FIX 级核对。
  - `scsArrowV39` 展开后 `{scs4T3} ∪ stabDiag` 的集合成员证明（`Set.mem_union`/`mem_insert` 逐槽），是历史 unifier 烧穿高发点；按 playbook §6 用显式 `rcases`/`refine` 逐槽物化。

---

## 不推荐（本批）

- `TFITSKC_p27`：本体只有 ~13 行（已有人写过），但前置 `TFITSKCv1_p27` 卡 `CUXVZOZ→general_482`（L）+ `LocalAuto7:954`，且 2026-11-05 已被判「搬债拒收」（`docs/priority-queue.md:171`）。
- `VPWSHTO_p15`：整章 11 sorries（Section A 7 条 yardstick + 3 条直链 + 本体），虽无外部缺口，但是单章 >800 行的真数学，不属「下一批」。
- `URRPHBZ2`：前置 `U0_NOT_IN_CONVEX_HULL_FROM_ROGERS`（geometric giant）+ 本体逐 index case bash，L。
