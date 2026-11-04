# DEF-FIX 闸门章程 · `LocalAuto34.lean`（SF-99 k1 适配）

HOL 锚：`reference/flyspeck/text_formalization/local/localization.hl:128`；
第三合取止于 `localization.hl:131`。新定义首合取直接给 `c < 0 ∧ 0 < d`
（旧 Icc 只能 `le_of_lt`）；连续性成员需严格区间。

对象：`DEFORMATION_SMALL_INTERVAL_p34`（`LocalAuto34:2538`，全库唯一窗口收缩
入口，14 个引用）。只改证明体两行，陈述不动。

### 2.1 改动围栏

```diff
-  refine ⟨⟨le_of_lt hc, le_of_lt hd⟩, ?_, hfix⟩
+  refine ⟨⟨hc, hd⟩, ?_, hfix⟩
-  exact hcont v hv r ⟨le_trans hac hr.1, le_trans hr.2 hdb⟩
+  exact hcont v hv r ⟨lt_of_le_of_lt hac hr.1, lt_of_lt_of_le hr.2 hdb⟩
```

### 2.2 白名单与范围外

- `DF_NAMES="DEFORMATION_SMALL_INTERVAL_p34"`；`DF_SORRY_NET=0`。
- 本文件其余行零改动。
