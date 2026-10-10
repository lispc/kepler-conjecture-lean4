# /tmp/la32_handoff.md — LocalAuto32 lane 交接（2026-10-08，本轮结束）

## 状态
- `lean/Kepler/Text/LocalAuto32.lean`（原 1217 行，现 ~1310 行）：本轮从 69 个
  sorried 声明推进到 **66**（sorry 文本 82 → 79，其余为注释）。全文件探针编译
  **绿**（`lake env lean /tmp/la32_full_probe2.lean`，0 error）。
- 本轮闭合 3：
  1. `EXPAND_STAB_DIAG_4M7_p32`（mod-4 残差枚举 → (0,2)/(1,3) 两记录）
  2. `EXPAND_STAB_DIAG_4M8_p32`（同款 on scs_4M8）
  3. `PROP_OPP_DIAG_4M8_13_p32`（stab(1,3) = PropEqu 2 (opp (stab(0,2)))——
     16 格残差扫描：反射 j ↦ 4-((2+j)%4+1) 保 a-表、换 cstab-类 (1,3)↔(0,2)）
- 无新增私有 helper（全部用本文件已有的 PROVED `stabDiag_mod_p32` +
  LA20 的 `STAB_SYM`——`interval_cases i % 4` 逐案 + `omega` 出 j%4）。
- PROP_OPP 打法备忘（可复用到 4M7 的孪生件）：两侧先 `STAB_SYM` 转成字面
  索引类 (3,1)/(2,0)；`show` 一整个 `ScsV39.mk …`（defeq 展开 stab/PropEqu/
  opp/peropp2/peropp 全套）；`ScsV39.mk.injEq.mpr ⟨rfl, rfl, funext ha,
  funext ha, funext hb, funext hb, rfl ×5⟩`；ha/hb 各 16 格
  `interval_cases j % 4 <;> interval_cases j' % 4 <;> simp only [scs4M8,
  mkUnadornedV39, funlistV39, psort, assocdV39] <;> simp [Nat.add_mod] <;> omega`。

## 下一批建议（按性价比）
1. **PROP_OPP_DIAG_4M7 孪生件不存在**——但 `SCS_4M6_OPP_IS_SCS_p32`（:907）
   的 NEEDS（peropp/peropp2 mod-4 周期性 + 对称 + 序 + scs4M6' 计数界）正是
   PROP_OPP 同款 16 格扫描 + isScs 21 合取骨架，isScs_mkFunlist 直证可试
   （中等体积）。
2. **SET_EQ_DIAG_STAB_4M7/4M8**（:491/:585 区）：comp2（MMs 空性二支）无素材
   ——需 STAB_4M8_02_ARROW（被 YXIONXL2/OPP_IS_SCS 堵，LA32 无此件）或
   MM_4M8_IMP_STAB_4M8（被 XWNHLMD_MM 堵）。两条路都要先收 comp1
   isScs(stab 4Mx 0 2 / 1 3)（同上 21 合取直证）。顺序：先 2 的 isScs 直证，
   再挂 PROP_OPP（已收）+ FZIOTEF_UNION。
3. **STAB_4M8_02_ARROW_4M8_13_p32**（:600）：现仅差 comp1 isScs 两记录 +
   YXIONXL2（opp 箭头）/SCS_OPP_REFL——检查 LA20/LA29 是否有 SCS_OPP_REFL
   已证件可 import 委托（LA32 现 import LA1+LA20，扩 import 须查环）。
4. MIN_NOT_STAND_4M7/4M8、BB/MM_4M7→4M6 八件、BB/MM_4M8→4M6_02/13/23/01 八件、
   SLICE 族、YOBIMPP、NWDGKXH、MIQMCSN：VASYYAU / main_nonlinear_terminal_v11
   / LKGRQUI 深巨人，维持 NEEDS。

## 纪律提醒（下轮必读）
- 探针：`cd lean && ~/.elan/bin/lake env lean /tmp/<probe>.lean`；错误扫描
  `grep -E ': error:'`；单 lean 进程；撞共享 olean（"object file does not
  exist"）等几十秒重试；禁 lake build / git。
- 本文件 `stabDiag_mod_p32`（只需 s.k ≠ 0，不需 isScs！）是最顺手的基座；
  STAB_MOD（LA20）要 isScs，本文件没有 4M6/4M7/4M8 的 isScs 已证件
  （仅 SCS_3T7_IS_SCS_p32 :268），凡走 STAB_MOD 的路先补 isScs。
- `scs4M7.k = 4` / `scs4M8.k = 4` 均 `rfl`（K_SCS_4M7_p32 同款）。
