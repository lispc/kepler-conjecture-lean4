# DEF-FIX 闸门章程 · `LocalAuto14.lean`（SF-99 PROOF-FIX）

HOL 锚：`reference/flyspeck/text_formalization/local/localization.hl:128`；
第三合取止于 `localization.hl:131`。`zlz_azim` 的 π 分支需要负半窗（`a < 0 < b`），
旧 `Deformation` 给不了；新定义首合取即 `a < 0 ∧ 0 < b`，严格形
`w9_zlz_azim_strict`（本文件 :3811，已标准三）可直接消费。

对象：`zlz_azim_p14`（`LocalAuto14:3914`）。只把 `sorry` 换成一行转调；
陈述逐字不动，own-sorry −1。同文件的 w9 docstring 订正属注释面，闸门按
docstring interior 豁免（不在围栏内）。

### 2.1 改动围栏

```diff
-  sorry
+  exact w9_zlz_azim_strict a b V E FF f h1 h2 h3 h3.1.1 h3.1.2 h4
```

### 2.2 白名单与范围外

- `DF_NAMES="zlz_azim_p14 w9_zlz_azim_strict"`；`DF_SORRY_NET=-1`。
- `XIV_DEFORMATION_p14` 的严格形 `w17_xiv_deformation_strict` 已备，但本波
  不动其冻结陈述（留给 LA14 链下一波一行转移）。
