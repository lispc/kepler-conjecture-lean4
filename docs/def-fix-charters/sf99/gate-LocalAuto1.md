# DEF-FIX 闸门章程 · `LocalAuto1.lean`（SF-99 ROOT）

HOL 锚：`reference/flyspeck/text_formalization/local/localization.hl:128`（`deformation`
定义头，`(&0) IN real_interval (a,b)`）；同一断言的第三合取止于
`localization.hl:131`。`real_interval (a,b)` = 开区间，故 Lean 侧必须 `Set.Ioo`。

对象：`Deformation`（`LocalAuto1:129`）。只改定义体，签名/陈述不动。

### 2.1 改动围栏

```diff
-  (0 : ℝ) ∈ Icc a b ∧ (∀ v ∈ V, ∀ r ∈ Icc a b, ContinuousAt (f v) r) ∧
+  (0 : ℝ) ∈ Ioo a b ∧ (∀ v ∈ V, ∀ r ∈ Ioo a b, ContinuousAt (f v) r) ∧
```

### 2.2 白名单与范围外

- `DF_NAMES="Deformation"`；`DF_SORRY_NET=0`。
- 本文件其余行零改动；消费者适配见 `gate-LocalAuto21.md` / `gate-LocalAuto14.md`。
