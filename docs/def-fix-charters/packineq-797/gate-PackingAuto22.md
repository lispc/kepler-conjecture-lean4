# DEF-FIX 闸门章程 · `Kepler/Text/PackingAuto22.lean`
# （`_797` 真化：`arclength22` / `asnFnhkP22` / `packIneqDefAP22`）

HOL 锚：`general/sphere.hl:258`（`arclength a b c`）、`general/sphere.hl:786`（`asnFnhk`）、
`packing/YSSKQOY.hl:30`（`pack_ineq_def_a` = `filter has_packid !Ineq.ineqs` 的合取）、
`nonlinear/ineq.hl:1635`（WAZLDCD `8055810915`）、`nonlinear/ineq.hl:1662`（UKBRPFE `6096597438 b`）、
`nonlinear/ineq.hl:1599`（BIEFJHU `1965189142 a`）。

对象（改前）：`arclength22`（`:14342`，`:= 0` 假桩）、`asnFnhkP22`（`:284`，`:= 0` 假桩）、
`packIneqDefAP22`（`:306`，`:= True` 桩）；另删本地 `sqrt3`（`:176`，与
`IneqClosureDefs.lean:719` **同名同体** —— 这是加 `import IneqClosureDefs` 的唯一硬阻塞，
`rfl` 级同体，删后所有引用零变化）。

`DF_SORRY_NET=0`：不闭合、不新增任何 `sorry`（实测 `declaration uses sorry` 14→14）。
`DF_NAMES`：`sqrt3 arclength22 asnFnhkP22 packIneqDefAP22 UKBRPFE_bank WAZLDCD_bank BIEFJHU_bank`。
**围栏不含 `---`/`+++`/`diff --git` 头**（闸门用 `grep -E '^-'` 抓删除行，会把 `--- a/…` 误当删除行）。

### 2.1 改动围栏

```diff
@@ -103,6 +103,7 @@ import Kepler.Text.PackingAuto12
 import Kepler.Text.PackingAuto13
 import Kepler.Text.PackingAuto15
 import Kepler.Text.Polytope
+import Kepler.Text.IneqClosureDefs
 import Mathlib
 
 set_option maxHeartbeats 5000000
@@ -172,8 +173,10 @@ noncomputable def asn (x : ℝ) : ℝ := Real.arcsin x
 /-- HOL `acs` (arccos). -/
 noncomputable def acs (x : ℝ) : ℝ := Real.arccos x
 
-/-- HOL `sqrt3`. -/
-noncomputable def sqrt3 : ℝ := Real.sqrt 3
+/-- HOL `arclength` (sphere.hl:258): `pi/2 + atn2(sqrt(ups_x(a²,b²,c²)),
+c² - a² - b²)`.  Alias of the canonical `IneqClosureDefs.arcLengthICD`
+(same term, single source of truth; the A4 body is its definition body). -/
+noncomputable def arclength22 (r h d : ℝ) : ℝ := arcLengthICD r h d
 
 /-- Planar copy of HOL `aff_dim` (convex1.ml:3784; twin of Polytope.affDim):
 `∅ ↦ -1`, else the finrank of the direction of the affine hull. -/
@@ -280,8 +283,9 @@ def pad2d3dP22 (z : ℂ) : V3 :=
 def dropout3P22 (v : V3) : ℂ :=
   Complex.mk ((v : Fin 3 → ℝ) 0) ((v : Fin 3 → ℝ) 1)
 
-/-- NEEDS `asnFnhk h k a b c d` (Ysskqoy.hl; PackingAuto18 bank). Stub: 0. -/
-noncomputable def asnFnhkP22 (h : ℝ) (k : ℕ) (_a _b _c _d : ℝ) : ℝ := 0
+/-- HOL `asnFnhk` (sphere.hl:786-787) — alias of the canonical
+`IneqClosureDefs.asnFnhk` (same body; `k : ℕ` cast to `ℝ`). -/
+noncomputable def asnFnhkP22 (h : ℝ) (k : ℕ) (a b c d : ℝ) : ℝ := asnFnhk h (k : ℝ) a b c d
 
 /-- HOL `regular_spherical_polygon_area th k`, closed form `2*pi - 2*k*asn
 (th * sin (pi/k))` (`th` taken as the cosine of the half-angle, matching the
@@ -301,9 +305,42 @@ def weaklySaturatedP22 (V : Set V3) (r c : ℝ) : Prop := True
 本体 = PA2:541 `localAnnulusInequality`（定义转发，下游签名零改）。 -/
 def localAnnulusInequalityP22 (V : Set V3) : Prop := localAnnulusInequality V
 
-/-- NEEDS HOL `pack_ineq_def_a` (pack1.hl: the numerical packing-inequality
-conjunction). Stub. -/
-def packIneqDefAP22 : Prop := True
+/-- HOL `6096597438 b` + `6096597438 a` (ineq.hl:1662/1651, Flypaper
+`UKBRPFE`): the `cos 0.797` area bound in the verbatim HOL boxes
+`[3,64]×[1,1]⁵` and `[1,1]`. -/
+def UKBRPFE_bank : Prop :=
+  (∀ x1 x2 x3 x4 x5 x6 : ℝ, 3 ≤ x1 → x1 ≤ 64 → 1 ≤ x2 → x2 ≤ 1 → 1 ≤ x3 → x3 ≤ 1 →
+    1 ≤ x4 → x4 ≤ 1 → 1 ≤ x5 → x5 ≤ 1 → 1 ≤ x6 → x6 ≤ 1 →
+    2 * Real.pi - 2 * asn797k x1 x2 x3 x4 x5 x6 >
+      0.591 - 0.0331 * x1 + 0.506 * lfun 1 + 1) ∧
+  (∀ h : ℝ, 1 ≤ h → h ≤ 1 → 0.591 - 0.0331 * 64 + 0.506 * lfun 1 + 1 < 0)
+
+/-- HOL `8055810915` (ineq.hl:1635, Flypaper `WAZLDCD`): non-overlap of the
+unit-sphere disks, verbatim HOL box `[4, 2.52²]×[4,4]×[(2h0)²,(2h0)²]×[1,1]³`. -/
+def WAZLDCD_bank : Prop :=
+  ∀ x1 x2 x3 x4 x5 x6 : ℝ,
+    4 ≤ x1 → x1 ≤ (2.52 : ℝ) ^ 2 → 4 ≤ x2 → x2 ≤ 4 →
+    (2 * h0) ^ 2 ≤ x3 → x3 ≤ (2 * h0) ^ 2 →
+    1 ≤ x4 → x4 ≤ 1 → 1 ≤ x5 → x5 ≤ 1 → 1 ≤ x6 → x6 ≤ 1 →
+    0.797 + acs (Real.sqrt x1 / 4) - Real.pi / 6 <
+      arclength22 (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3)
+
+/-- HOL `1965189142 a` + `1965189142 34` (ineq.hl:1599/1588, Flypaper
+`BIEFJHU`): the `h`-family area bound in the verbatim HOL boxes
+`[1,1.26]×[3,34]×[1,1]⁴` and `[1,1.26]×[1,1]⁵`. -/
+def BIEFJHU_bank : Prop :=
+  (∀ x1 x2 x3 x4 x5 x6 : ℝ, 1 ≤ x1 → x1 ≤ 1.26 → 3 ≤ x2 → x2 ≤ 34 →
+    1 ≤ x3 → x3 ≤ 1 → 1 ≤ x4 → x4 ≤ 1 → 1 ≤ x5 → x5 ≤ 1 → 1 ≤ x6 → x6 ≤ 1 →
+    2 * Real.pi - 2 * asnFnhk x1 x2 x3 x4 x5 x6 >
+      0.591 - 0.0331 * x2 + 0.506 * lfunY1 x1 x2 x3 x4 x5 x6) ∧
+  (∀ x1 x2 x3 x4 x5 x6 : ℝ, 1 ≤ x1 → x1 ≤ 1.26 → 1 ≤ x2 → x2 ≤ 1 →
+    1 ≤ x3 → x3 ≤ 1 → 1 ≤ x4 → x4 ≤ 1 → 1 ≤ x5 → x5 ≤ 1 → 1 ≤ x6 → x6 ≤ 1 →
+    0.591 - 0.0331 * 34 + 0.506 * lfunY1 x1 x2 x3 x4 x5 x6 < 0)
+
+/-- HOL `pack_ineq_def_a` (YSSKQOY.hl:30-31): the conjunction of the five
+`ineq` entries tagged `UKBRPFE`/`WAZLDCD`/`BIEFJHU` (ineq.hl:1587-1662),
+grouped by Flypaper family. -/
+def packIneqDefAP22 : Prop := UKBRPFE_bank ∧ WAZLDCD_bank ∧ BIEFJHU_bank
 
 /-! ## #1 Finiteness, annulus membership, facet representations -/
 
@@ -14341,9 +14378,6 @@ theorem YSSKQOY_VECTOR (v w : V3) (theta : V3 → ℝ)
   linarith
 
 
-/-- NEEDS HOL `arclength` (pack1.hl; PackingAuto1, no olean). Stub: 0. -/
-noncomputable def arclength22 (r h : ℝ) (d : ℝ) : ℝ := 0
-
 /-- HOL `PACK_INEQ_DEF_A_797` (counting_spheres.hl:6540). GIANT. -/
 theorem PACK_INEQ_DEF_A_797 (v v0 : V3) (hpa : packIneqDefAP22)
     (hv0 : ‖v0‖ = 2) (hd : 2 * h0 ≤ dist v v0)
```

### 2.2 验收

- `arclength22` 体 = `IneqClosureDefs.arcLengthICD`（该定义体与 HOL `sphere.hl:258` 逐字相同，
  `rfl` 实测）；`asnFnhkP22` 体 = `IneqClosureDefs.asnFnhk`（HOL `sphere.hl:786-787`，含 `k`）。
- `packIneqDefAP22` = `UKBRPFE_bank ∧ WAZLDCD_bank ∧ BIEFJHU_bank`，三族各自是
  HOL 5 条 `ineq` 条目的**逐字盒式渲染**（`ineq.hl:1587-1662`）。
- 与 Assembly 的 `PackIneqDefA` 分两笔：本文件只改 PA22；Assembly 那笔走岛协议另核。
- 编排者实测：`lake env lean Kepler/Text/PackingAuto22.lean` **RC=0 / 0 error**。
