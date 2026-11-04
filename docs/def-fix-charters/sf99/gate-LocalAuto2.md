# DEF-FIX 闸门章程 · `LocalAuto2.lean`（SF-99 TWIN-ROOT）

HOL 锚：`reference/flyspeck/text_formalization/local/localization.hl:128`；
同一断言的第三合取止于 `localization.hl:131`。`deformation_p2` 是独立复制的
同一定义（自己的三处 `Set.Icc`），根修不传播；**必须与 ROOT 同 patch**，
否则 `LocalAuto2:1423` / `LocalAuto6:1432` 携带闭区间语义且因 sorry 静默失保真。

对象：`deformation_p2`（`LocalAuto2:300`）。只改定义体与注释，签名不动。

### 2.1 改动围栏

```diff
-closed interval `Set.Icc a b`, `continuous atreal` ↦ `ContinuousAt`. NEEDS:
+open interval `Set.Ioo a b`, `continuous atreal` ↦ `ContinuousAt`. NEEDS:
-  (0 : ℝ) ∈ Set.Icc a b ∧
-    (∀ v : V3, v ∈ V → ∀ r : ℝ, r ∈ Set.Icc a b → ContinuousAt (ff v) r) ∧
+  (0 : ℝ) ∈ Set.Ioo a b ∧
+    (∀ v : V3, v ∈ V → ∀ r : ℝ, r ∈ Set.Ioo a b → ContinuousAt (ff v) r) ∧
```

### 2.2 白名单与范围外

- `DF_NAMES="deformation_p2"`；`DF_SORRY_NET=0`。
- 本文件其余行零改动。
