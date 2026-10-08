# /tmp/la5_handoff.md — LocalAuto5 lane 交接（2026-10-08，本轮结束）

## 状态
- `lean/Kepler/Text/LocalAuto5.lean`：本轮从 97 个 sorried 声明推进到 **84**
  （sorry 文本出现 98 → 85，其中 1 处为头注释）。全文件探针编译 **绿**
  （`lake env lean` 0 error，探针副本 = 落盘副本）。
- 本轮闭合 13（按文件序）：
  1. `AFF_GE_MONO_TRANS`   2. `AFF_GT_MONO_TRANS`   3. `LOFA_IMP_CARD_FF_V_EQ`
  4. `CONV0_SUBSET_AFF_GT` 5. `AFF_GT_MONO`         6. `AFF_GT_SUB_AFF_UNION`
  7. `IN_CONV0_IMP_COLL_IFF` 8. `IN_CONV0_IMP_COLL_ENDS_AFF`
  9. `USEFULL_THHM`       10. `COLL_IN_AFF_GT_TOO` 11. `AFF_GT_IN_IMP_SUBSET`
  12. `INVS_IN_AFF_GT`    13. `COLL_IN_AFF_GT_AFF_GT_EQ`
- 新增私有 helper（全部已验证）：
  - `la5_affsign_mono`（Affsign 支撑扩张，t2 ⊆ t1 即可保号）
  - `la5_conv02_comm`、`la5_span_pair_eq`、`la5_affSpan_pair_comm`
  - `la5_affComb3_in_span`、`la5_affComb3_mem_affSpan`、`la5_smul_div_solve`（未用上，
    可删可留）
  - `la5_affGt212_extract` / `la5_affGt212_intro`（affGt {x,y} {z} 三系数提取/回填）
  - `la5_conv02_partner`、`la5_conv02_extract`、`la5_affComb_mem_affSpan`（上轮残留）

## 下一批建议目标（按性价比）
1. `CONV0_AFF_GT_EQ`（hl:5328）：affGt {x,a} {v} = affGt {x,a,b} {v}，用
   `la5_affGt212_extract/intro` + span-swap 应可机械闭合。
2. `AFF_GT_NOT_INTERSECTION` 族、`IN_CONV_LINE_SEPERATABLE` 下游的 affGt 集合等式。
3. `IN_CONV0_IMP_AZIM_PI`：需 azim 机器（azimSpec/azim_frame_spec，Geom/Azim.lean）。
4. `DIHV_NOT_CHANGE`（hl:5903）：**本轮攻而未克，探针残留=/tmp/la5_probe（烂）**。
   已回滚落盘。要点：
   - V3 的 `⬝ᵥ` 展开为 `ofLp`-形式的 Pi-dot，但 smul/add 传输 `rfl` 不成立，
     需走 `WithLp.ofLp_smul/ofLp_add`（rfl-引理）+ Pi 层
     `smul_dotProduct`/`dotProduct_smul`/`dotProduct_add`（注意：本 Mathlib 中
     `dotProduct_smul` 是**右** smul 形式 `v₁ ⬝ a•v₂`，左 smul 用 `smul_dotProduct`）。
   - arcV 缩放引里 `dist` 走 `dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
     abs_of_pos`（LuneVolume.lean:191 先例）；分子分母配平用 `mul_div_mul_left`。
   - dihV 的 let-体对 `rfl` 展开**成立**（hL := rfl 验证过）。
   - 剩余难点：DIHV 证明骨架里 `hvap`（vap′ = c•vap）的 module 收尾与
     `fz * fz⁻¹` 类残差——`linear_combination` 需要正确符号 + `(norm := field_simp)`
     或按 `mul_left_cancel₀ + mul_div_cancel₀` 手推（本轮 mul_div_assoc 方向写错：
     应为 `mul_div_assoc'`）。
5. 远山：rho-orbit 巨人（`LOFA_IMP_ITER_RHO_NODE_ID`、`LOOP_SET_*`、
   `ITER_CARD_MINUS1_EQ_IVS_RN1` 等）依赖 orbitF_p2 facts（1003 行仍是 sorry）。

## 纪律提醒（下轮必读）
- 探针：`cd lean && lake env lean /tmp/la5_probe/LocalAuto5.lean`；**勿 grep '^error'**，
  用 `grep -E ': error:'`。单 lean 进程；本轮多次撞见兄弟 lane 的
  auto_gate 重建共享 olean（PackingAuto10 一度缺失），遇
  "object file does not exist" 等几十秒重试即可。
- 依赖 olean：LocalAuto5 的构建 olean 是 9/29 的陈旧物（lane 一贯如此），
  权威门 = `make check`（全树 + AxiomAudit），由总 lane 负责。
- dotProduct 在 Pi 层的形态：左 smul = `smul_dotProduct`，右 smul =
  `dotProduct_smul`；加法 `dotProduct_add` 是**右**加形式。
