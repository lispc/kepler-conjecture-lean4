# DEF-FIX 闸门章程 · `LocalAuto21.lean`（SF-99 k1 适配）

HOL 锚：`reference/flyspeck/text_formalization/local/localization.hl:128`；
第三合取止于 `localization.hl:131`。新定义首合取给 `0 < e`（旧 Icc 给
`0 ≤ e`），`deformation_restrict_p21` 的 `he0` 需从严格版取弱形式。

对象：`deformation_restrict_p21`（`LocalAuto21:534`）。只改证明体一行，陈述不动。

### 2.1 改动围栏

```diff
-  have he0 : 0 ≤ e := h0.2
+  have he0 : 0 ≤ e := le_of_lt h0.2
```

### 2.2 白名单与范围外

- `DF_NAMES="deformation_restrict_p21"`；`DF_SORRY_NET=0`。
- 末尾 `hc` 成员证明 `⟨by linarith [hr.1, hee], ...⟩` 对 Ioo 天然成立，未改。
