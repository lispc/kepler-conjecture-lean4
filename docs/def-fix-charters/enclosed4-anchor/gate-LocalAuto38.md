# DEF-FIX 闸门章程 · `LocalAuto38.lean`（LA38 `_p38` 锚桩 enclosed/cayleyR 填体）

HOL 锚：`reference/flyspeck/text_formalization/leg/cayleyR_def.hl:32`（`cayleyR`）、
`reference/flyspeck/text_formalization/leg/enclosed_def.hl:22-24`（`enclosed`）、
`reference/flyspeck/text_formalization/leg/muR_def.hl:40-42`（`muR`，保持 `rfl` 不动）。

对象：`cayleyRP38`（LA38:193-195 改前）、`enclosedP38`（LA38:165-167 改前，声明块
下移至 `muRP38` 后）。只改两个 def 的文档串与体；`enclosedP38` 位置移动不改名字/
签名。同 patch 可含 `enclosed_sym`/`enclosed_sym2` 两条真证明（逐字稿见
`~/c17_backup/lane_snapshots/enclosed4-w1/DELIVERY.md` §4.3；证明内需
`set_option maxRecDepth 65536 in`）。

### 围栏

- `DF_NAMES="cayleyRP38 enclosedP38"`；`DF_SORRY_NET=-4`（2 桩体 + 2 定理真证明）。
- 其余 `_p38` 锚桩（`solXP38`/`rhazimP38`/`unit6P38`/`taudP38`/`taudXP38`/
  `taumXP38`/`tauResidualXP38`/`flatTermXP38`/`eulerAXP38`/`cayleytrP38`/
  `tauqP38`/`scsTerminalV116_p38`）原样 `sorry`，不在本波。
- 零新 import（主变体）或恰一条 `+import Kepler.Text.IneqClosureDefs`（替代变体，
  闭包零环已证）；零新 sorry/axiom；`muR_ALT`/`muR_alt`/
  `quad_cross_diag2_x_cayleyR` 等 `rfl` 件保持 `rfl`。
- 本文件其余行零改动；enclosed 集群 4 定理的陈述逐字节不动。
- 闸门核对：`#print axioms enclosed_sym` = `[propext, Classical.choice,
  Quot.sound]`（同 `enclosed_sym2`），`IN_V_IMP_AZIM_LESS_PI_ALT` 已在前一波
  独立落库（enclosed4-w1 patch.diff，探针同标准三）。
