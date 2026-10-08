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

---

# 续作交接（2026-10-08 第二轮结束）

## 状态
- `lean/Kepler/Text/LocalAuto5.lean`：85 → **81** 个 sorry 文本出现
  （84 → **80** 个 sorried 声明；1 处为头注释）。全文件探针编译**绿**
  （`lake env lean /tmp/la5_probe/LocalAuto5.lean` 0 error；探针副本 = 落盘副本）。
- 本轮闭合 4（按 handoff 顺序全部完成）：
  1. `CONV0_AFF_GT_EQ`（hl:5328）：⊆ 方向用新私件 `la5_affsign_insert`
     （Affsign 自由支撑插入一点零系数保号，by_cases q ∈ s∪t 两分支）；
     ⊇ 方向 b = x / b = a 退化用 `Set.insert_eq_of_mem` 改写假设，
     主情形拿 conv0 系数 α β，`hbdec`（b = (1/β)•x + -(α/β)•a）+ 逐帧见证
     替换（set g + gx/ga/gv 三条求值引理，simp only [hgdef, if_neg …, reduceIte]）。
     教训：simp only 里 `if_pos rfl` 会把 `q = q` 归一成 True 卡住 ite——
     要么 `if_pos (rfl : a = a)` 显式类型，要么 `reduceIte`；
     rw 的 kabstract 不做 β 归约，lambda 应用后要 `show`/先 `simp only [hgdef]`。
  2. `IN_CONV_LINE_SEPERATABLE`（hl:4119）：affineSpan {a,b} =
     affGe {x}{a} ∪ affGe {x}{b}。⊇ 用 `affGe_ray`（Aff.lean 已有）+
     `la5_affComb_mem_affSpan`；⊆ 用 `mem_affineSpan_pair_iff_exists_lineMap_eq`
     （注意方向：`∃ r, lineMap a b r = z`，lineMap 在前！）+ 按 a-侧/b-侧
     系数符号拆分 + 新私件 `la5_affGe2_intro`（两点 affGe 见证构造，需 p ≠ q，
     主情形 x ≠ a/x ≠ b 由 `IN_CONV0_EQ_EQ` 从 a ≠ b 导出）。
     a = b 退化单独处理（两侧都塌缩成 {a}，affGe {a}{a} = {a}）。
     教训：`mul_div_cancel₀` 是左消形式（β * ?b / β），右消要用
     `mul_div_cancel_right₀`；`div_le_one` 要 0 < 除数（用 hα 不是 hα0）。
  3. `IN_CONV0_IMP_AZIM_PI`（hl:5031）：azim x e a b = π。配方：
     `azimSpec_exists` 拿 θ + `azim_eq_of_spec`，再自构
     `AzimSpec x e a b Real.pi` 用 `azimSpec_unique` 夹出 θ = π。
     π-见证全盘复用 Azim.lean 的 zOf 复极坐标机器：`zOf_ne_zero_iff`
     （zOf ≠ 0 ↔ ¬Collinear3，喂 h1/h2）、`Complex.norm_mul_exp_arg_mul_I`
     （**方向是 ‖A‖*exp(arg A*I) = A，要 .symm**）、`rep_of_zOf`
     （**y 参数传点 a 本身，不是 a - x**）给出 a-分解；
     b-分解不碰 inner：b - x = (α/β)•(x - a)（hbx2，linear_combination
     (norm := module) hxab + hsum''），把 a-分解缩放 -(α/β) 后
     linear_combination (norm := module) hbx2 - hdecA2 收尾
     （**scalar * eq 会类型错，线性组合里不许 (α/β) * hdecA，
     要先 `have hdecA2` 预缩放**）。h2c 用 frame-free 形式
     ((b-x)⬝(e-x))/dist²，桥接 `hco3`（∀ y: (y-x)⬝(e-x) = dist*(y-x)⬝e3，
     inner_comm + real_inner_smul_left——**第一参数 smul 的
     real_inner_smul_left 是本文件唯一可靠路径，第二参数的
     real_inner_smul_right 在 V3/toLp 实例上 rw 匹配会失败**；
     inner_eq_dot 转换要用 term 级 `(inner_eq_dot a b).symm`，
     rw 版会产生 ofLp 摆放不同的语法项导致 rfl 失败）+ `hkab`
     （(b-x)⬝e3 = -(α/β)*(a-x)⬝e3，hsub + 第一参数 smul_left）。
     教训：AzimSpec 的 ∃ h1 h2 在 ∀ 框架之前——h1/h2 必须 frame-free，
     不能引用 e3。
  4. `DIHV_NOT_CHANGE`（hl:5903）：handoff 配方成功。dihV let-体 show 展开 ✓；
     新投影 vap' = c•vap：hva（w2-x = b•(y-x)+c•(v-x)，
     linear_combination (norm := module) hsumv）+ hvap
     （rw [hva, hVAdef, smul_add, dot_add_l, dot_smul_l ×2, smul_smul ×2]; module，
     b-项沿轴自动消去）；arcV 缩放 hscale：rw [arcV, arcV]（**两个 arcV 都要
     展开**）+ coez（((0:V3):Fin3→ℝ) = 0 := rfl，Pi 侧 0 要先归一 sub_zero 才能咬）
     + simp only [sub_zero, dist_eq_norm, …, norm_smul, Real.norm_eq_abs,
     abs_of_pos hc] + field_simp。Pi-dot 运输私件（LuneVolume 同款）：
     dot_smul_l/dot_add_l/dot_smul_r 直接 `fun … => smul_dotProduct …` 一行
     term 定义即可（V3-dot 对 Pi-dotProduct defeq，exact 级别够用）。

## 新增私有 helper（全部已验证）
- `la5_affsign_insert`（Affsign 支撑插入保号；CONV0_AFF_GT_EQ 的 ⊆ 方向）
- `la5_affGe2_intro`（两点 affGe 见证构造；IN_CONV_LINE_SEPERATABLE 用）
（DIHV_NOT_CHANGE 的 dot_smul_l/dot_add_l/dot_smul_r/hsumv 等是定理内
 have，非文件级私件。）

## 下一批建议（按性价比）
1. `AFF_GT_SAME_WITH_ENDS`（hl:5375）与 `NOT_INTERSECTION_BWT_AFF_GTS`、
   `NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT`/2：依赖 lunar_p2 下的 rhoNode/ivs
   事实（`LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI` hl:4222 仍是 sorry 且是前置），
   建议先攻 LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI（0 ∈ conv0_p2 {v,w} +
   rhoNode/ivs ∈ affineSpan {u,v,w}），这批 affGt 集合等式随后机械化。
2. `FAN_IMP_NOT_IN_AFF_GE`（hl:4034）/`IN_AFF_LT_IMP_IN_CONV`（hl:4061）/
   `FAN_SUB_NOT_EQ_COLL_IN_CONV0`（hl:4090）：小型 fan 引理，可能机械。
3. `USEFULL_THHM` 下游 affGt 三点等式若再遇到，本轮的
   la5_affGt212_extract/intro + la5_affsign_insert 组合可直接复用。
4. 远山不变：rho-orbit 巨人依赖 orbitF_p2（hl:1003 仍 sorry）。

## 纪律提醒（不变，另补）
- 探针：`cd lean && lake env lean /tmp/la5_probe/LocalAuto5.lean`；
  错误扫 `grep -E ': error:'`。本轮多次撞兄弟 lane 的 olean 重建：
  **"Unknown constant" 类错误若上一轮同区域是绿的，先 sleep 30 重跑再诊断**
  （本轮 la5_affsign_insert 区域两次误报 Set.Finite.mem_toFinset.mpr）。
- `Set.Finite.mem_toFinset` 作为 rw-step 在 metavar 位置会炸；
  用 term 级 `.mpr/.not.mpr`（本轮已用）。`by simp` 作为 rewrite-rule 参数
  会拿到未实例化的目标——一律带类型体注或用确定性 term。
