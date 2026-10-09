# grutoti_sum_volD 攻坚结论——冻结陈述为假，SF 立案（2026-10-09）

> 判定：`grutoti_sum_volD`（PA23，private）冻结前提面（仅 `he : e = {u0,u1}`，
> V/u0/u1/r/d 全自由）不足以使陈述为真——**可反驳，非难证**。按红线"前提面
> 需改动 → 停下报告"，PA23 一字未动，立案 docs/statement-fix-proposals.md
> 条目 31（DRAFT 待批）。

## 反例（全真证、零 sorry，机器验证）

取 V := ∅（任取 u0 ≠ u1，r := 1，d := 1/2，e := {u0,u1}）：

- `barV ∅ 3 ul` 恒假（voronoiNondg 门要求非空初始子列的 `setOfList ⊆ ∅`，
  长度 4 的列必有成员）⇒ `mcellSet ∅ = ∅` ⇒ `grutotiEdgeCells ∅ e = ∅`
  ⇒ `setSum ∅ _ = 0`；
- 但 `volume.real (grutotiConicCap u0 u1 1 (1/2)) > 0`（公共件
  `volumeConicCapPos`，ConicCapVolume.lean:961——即 `grutoti_volD_pos` 的
  共享版；ccvConicCap 与 grutotiConicCap 同体 `rfl`）；
- 故恒等式 `0 = 正数` 假。探针给了强形式：对每一对 u0 ≠ u1（无需任何
  V-成员/装填/饱和前提）陈述即假，另有封闭推论（PA23:4418-4423 逐字全量词
  形式 → False）。

## 前提面差距（sum_volD vs region_data 供给面）

- 冻结面 1 条（he）；`p23_region_data`/`grutoti_region` 门 7 条
  （hs hp hu0 hu1 hne hhl he）——差 6 条。capstone 调用点 GRUTOTI
  （:4484-4494）scope 内六条全有，SF 后接线零阻尼。
- **有限性支**：只补 `hp hs` 即一行——`FINITE_EDGE_X2 V e u0 u1 hp hs he`
  （PA15:775，真证），其结论 `{X | mcellSet V X ∧ edgeX V X e}.Finite` 与
  grutotiEdgeCells V e ∈-同体。探针内已机验（`probe_finite_with_hp_hs`）。
- **体积支**：补齐六条后对任意 r d 仍不可填——边 cell 迹只在 region-block D
  （region_data 的见证 r d）上零测覆盖 D；测度覆盖
  （D ∖ ⋃₀迹 = 0 + 两两零测）是**未证数学内容**（TIWWFYQ/GLTVHUM/SLTSTLO1
  + PA17 AJRIPQN 上游 sorry；消费端桥 `p23_measure_setSum_biUnion` 已
  banked）。注意 `p23_region_data` 供给的是 mcell-**分类** cover，不是测度
  覆盖——它不解渴。

## SF 方案（条目 31 (c)，二选一）

(a1) 最小门 = region_data 同款 + `0 < r ∧ d < 1` + 显式覆盖/两两零测前提
⇒ sum_volD 变 FINITE_EDGE_X2 + p23_measure_setSum_biUnion 纯装配；
(a2) ∃-式沿 grutoti_region 见证重述。
两者都需 GRUTOTI capstone 调用点同一 SF 打包联动；覆盖数学缺口（TIWWFYQ 族）
是独立新巨型。

## 附带修正（随 SF 落档）

GT-2 lane note 的反例 sketch 称 "mcell 4 cells carry e" 不成立——远点族上
hl ≥ √2 ⇒ `mcell4 V ul = ∅` ⇒ nullSet ⇒ `VX = ∅` 无边；无穷性支路应走远点
Delaunay 族上的 mcell0/2/3（非零测、互异、VX 含 u0,u1）。不影响本波结论
（探针走 vol 支），但避免后续误工。

## 探针落盘硬条款（已执行）

- 落盘路径：`docs/grutoti-assets/probe_sum_volD_falsity.lean`
- /tmp 副本 EXIT=0 → cp 落盘 → diff 字节一致 → 真路径复探 **EXIT=0** →
  **error 扫描 0**（log 空，零警告）
- 三件内容：`probe_sum_volD_frozen_false`（强形式反例）、
  `probe_frozen_statement_contra`（冻结陈述逐字 → False）、
  `probe_finite_with_hp_hs`（SF 最小面下有限性支一行机验）
- 改动面：仅 docs/grutoti-assets/；PA23 未动；无 git 写操作、无全项目
  build、无 gate。
