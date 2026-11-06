# DEF-FIX 闸门章程（草稿） · `Kepler/Text/PackingAuto22.lean`
# （`weaklySaturatedP22` 桩真化 = `PackingAuto3.weakly_saturated` 别名；
#   连带真证 `weak_saturation`、真证 `#10 EXISTS_M_POLYHEDRON`，私有
#   `BIJ_SUM` 改名 `BIJ_SUM_p22` 以避撞名）

车道：`pa22-10-chain`。基线 HEAD `da8c2df2`（2026-11-06，实测）。
用户 2026-11-06 已批：`#10 EXISTS_M_POLYHEDRON` 走路线 (a) 全做；
工单 `docs/workorders/2026-11-06/w1-pa22-10-chain.md`。

HOL 锚（本笔定义/陈述的来源行）：
`packing/counting_spheres.hl:1527`（`weak_saturation`）、
`packing/counting_spheres.hl:5888`（`EXISTS_M_POLYHEDRON`）、
`packing/counting_spheres.hl:6221`（`SATURATE_BALL_ANNULUS`，下游消费方）、
`packing/counting_spheres.hl:5706`（`FACET_OF_POLYHEDRON_EXPLICIT_ALT`）、
`packing/counting_spheres.hl:5518`（`RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT`）、
`packing/TARJJUW.hl:21-25`（`weakly_saturated` 真身）、
`packing/TARJJUW.hl:555-574`（`TARJJUW`，boundedness 消费方）、
`general/sphere.hl:290`（`cone0`，rcone 编码锚）、
`polytope1.ml:1506`（`facet_of`）、`polytope1.ml:2546`（`polyhedron`）。

对象（改前）：
- `weaklySaturatedP22`（`:357`）：`Prop := True` 桩；
- `weak_saturation`（`:6884`）：`trivial` 填桩的假绿；
- `EXISTS_M_POLYHEDRON`（`:14402`）：`sorry`；桩语义下**陈述为假**
  （过原点平面上的正六边形 ⇒ `P` 含整条 z 轴 ⇒ `IsBounded` 假）；
- `private BIJ_SUM`（`:14517`）：与 PackingAuto3:476 的公开 `BIJ_SUM` 同名。
改后：
- `weaklySaturatedP22 := weakly_saturated`（别名，零 body 复制）；
- `weak_saturation`：基数极大化真证（`card_packing_annulus` +
  `FINITE_MAX_EXISTS` + `PACKING_INSERT`），陈述逐字不动；
- `EXISTS_M_POLYHEDRON`：真证（`TARJJUW` + `FACET_OF_POLYHEDRON_EXPLICIT_ALT`
  + `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT` + `rcone_gt_facet`），陈述逐字不动；
- `BIJ_SUM` → `BIJ_SUM_p22`（零消费者的私有件，改名纯避撞）。
- 新增 `import Kepler.Text.PackingAuto3`（P3 只 import Polytope/Statement/Mathlib，
  不成环；Assembly 本来就经 PackingAuto25/PackingConcl 引入 P3）。

`DF_SORRY_NET=-1`：`declaration uses sorry` 5 → 4（`EXISTS_M_POLYHEDRON`
的 `sorry` 被真证替换；`insert_v` / `vol_solid_triangle_ortho` /
`BIJ_EDGES_DART_FACE` / `BIJ_DART_POLYEDGE` 四条不动）。

`DF_NAMES`：`weaklySaturatedP22 weak_saturation EXISTS_M_POLYHEDRON
p22w10_v_scale_lt p22w10_x_scale_lt p22w10_v_scale_tight BIJ_SUM`。

`#print axioms`（实测，见 `Evidence.md`）：`weak_saturation` /
`SATURATE_BALL_ANNULUS` / `EXISTS_M_POLYHEDRON` / `DLWCHEM_full` /
`XULJEPR_full` 全部 `[propext, Classical.choice, Quot.sound]`。

## 2. 应用围栏

### 2.1 改动围栏

```diff
@@ -83,12 +83,15 @@ ENCODING NOTES
   - `regular_spherical_polygon_area th k` is DEFINED here in closed form
     `2*pi - 2*k*asn(cos th * sin (pi/k))` (matches its flyspeck value at
     `th = cos 0.797`, i.e. theorem regular_spherical_polygon_area_797);
-    `asnFnhk`, `vol_solid_triangle`, `weakly_saturated`,
-    `local_annulus_inequality`, `pack_ineq_def_a` are `_p22` stubs.
+    `asnFnhk`, `vol_solid_triangle`, `local_annulus_inequality`,
+    `pack_ineq_def_a` are `_p22` stubs (`weakly_saturated` now aliases the
+    real PackingAuto3 definition, DEF-FIX 2026-11-06).
 
 ## NEEDS (giant fill-in markers)
-  - `weaklySaturatedP22`: NEEDS PackingAuto3 (pack3.hl) — no olean on this
-    branch.  `localAnnulusInequalityP22`, `packIneqDefAP22`: NEEDS pack1.hl
+  - `weaklySaturatedP22`: DEF-FIX 2026-11-06 (lane `pa22-10-chain`): the
+    former `True` stub is now the alias `weakly_saturated` of PackingAuto3
+    (import added; the real `weak_saturation` proof below consumes it).
+    `localAnnulusInequalityP22`, `packIneqDefAP22`: NEEDS pack1.hl
     (PackingAuto1, no olean).  `asnFnhkP22`: NEEDS Ysskqoy.hl
     (PackingAuto18 bank, no olean).  `volSolidTriangleP22`: NEEDS sphere.hl
     vol_solid_triangle.  `THETA_BOUNDS`: NEEDS Flyspeck_constants.bounds
@@ -96,6 +99,7 @@ ENCODING NOTES
 -/
 
 import Kepler.Text.PackingAuto2
+import Kepler.Text.PackingAuto3
 import Kepler.Text.PackingAuto5
 import Kepler.Text.PackingAuto6
 import Kepler.Text.PackingAuto7
@@ -353,9 +357,12 @@ noncomputable def regularSphericalPolygonAreaP22 (th : ℝ) (k : ℕ) : ℝ :=
 /-- NEEDS HOL `vol_solid_triangle x u v w r` (sphere.hl). Stub: 0. -/
 noncomputable def volSolidTriangleP22 (x u v w : V3) (r : ℝ) : ℝ := 0
 
-/-- NEEDS HOL `weakly_saturated V r c` (pack3.hl; PackingAuto3, no olean).
-Stub. -/
-def weaklySaturatedP22 (V : Set V3) (r c : ℝ) : Prop := True
+/-- HOL `weakly_saturated V r c` (TARJJUW.hl:21-25) — DEF-FIX 2026-11-06
+(lane `pa22-10-chain`): the former stub `True` is replaced by an alias of the
+in-tree real definition `PackingAuto3.weakly_saturated` (single source of
+truth, no body copy; `PackingAuto3` only imports Polytope/Statement/Mathlib,
+so this is acyclic).  Downstream statement sites are textually unchanged. -/
+def weaklySaturatedP22 (V : Set V3) (r c : ℝ) : Prop := weakly_saturated V r c
 
 /-- HOL `local_annulus_inequality` (pack_defs.hl:202-203) — SF-43: stub 换
 本体 = PA2:541 `localAnnulusInequality`（定义转发，下游签名零改）。 -/
@@ -6887,9 +6894,81 @@ theorem weak_saturation (W S : Set V3) (r : ℝ) (hr : 2 ≤ r ∧ r ≤ 2 * h0)
     ∃ V : Set V3, V ⊆ ballAnnulus ∧ Packing V ∧ weaklySaturatedP22 V r (2 * h0) ∧
       V.Finite ∧ W ⊆ V ∧
       (∀ v w : V3, S v → V w → dist v w < r → v = w) := by
-  -- under the `weaklySaturatedP22` stub (= True) the extension `V := W`
-  -- already satisfies every conjunct; finiteness is `fat_lemma1`.
-  exact ⟨W, hW, hP, trivial, fat_lemma1 W hP hW, le_refl W, hsep⟩
+  classical
+  -- cardinal maximality (HOL counting_spheres.hl:1527-1663): every admissible
+  -- `V` is finite with `ncard ≤ n`; take one of maximal cardinality `a`.
+  obtain ⟨n, hn⟩ := card_packing_annulus
+  set WW : Set (Set V3) :=
+    {V | W ⊆ V ∧ Packing V ∧ V ⊆ ballAnnulus ∧
+      (∀ v w : V3, S v → V w → dist v w < r → v = w)} with hWW
+  have hWmem : W ∈ WW := by
+    simp only [hWW, Set.mem_setOf_eq]
+    exact ⟨fun w hw => hw, hP, hW, hsep⟩
+  have hbound : ∀ V ∈ WW, V.Finite ∧ V.ncard ≤ n := by
+    intro V hV
+    simp only [hWW, Set.mem_setOf_eq] at hV
+    exact hn V hV.2.1 hV.2.2.1
+  have hImgFin : (Set.ncard '' WW).Finite := by
+    refine Set.Finite.subset (Set.finite_Iic n) ?_
+    rintro k ⟨V, hV, rfl⟩
+    exact (hbound V hV).2
+  have hImgNe : (Set.ncard '' WW) ≠ ∅ := by
+    intro h
+    have hmem : W.ncard ∈ (Set.ncard '' WW) := ⟨W, hWmem, rfl⟩
+    rw [h] at hmem
+    simp at hmem
+  obtain ⟨a, ha, hamax⟩ := FINITE_MAX_EXISTS (Set.ncard '' WW) hImgNe hImgFin
+  obtain ⟨x, hxWW, hxa⟩ := ha
+  obtain ⟨hWx, hxP, hxann, hxsep⟩ :
+      W ⊆ x ∧ Packing x ∧ x ⊆ ballAnnulus ∧
+        (∀ v w : V3, S v → x w → dist v w < r → v = w) := by
+    simpa only [hWW, Set.mem_setOf_eq] using hxWW
+  have hxfin : x.Finite := (hbound x hxWW).1
+  refine ⟨x, hxann, hxP, ?_, hxfin, hWx, hxsep⟩
+  -- weak saturation of `x`: any annulus point `v` is covered
+  intro v hv2 hvc
+  by_contra hcon
+  have hxne0 : ∀ u ∈ x, u ≠ 0 := fun u hu =>
+    ((ckq_in_ball_annulus u).mp (hxann hu)).2.2
+  -- `v` itself is not in `x` (otherwise it is its own witness)
+  have hvx : v ∉ x := by
+    intro hv
+    exact hcon ⟨v, hv, by intro h; rw [h] at hv2; norm_num at hv2, by
+      rw [dist_self]; linarith [hr.1]⟩
+  -- nothing in `x` is closer than `r` to `v`
+  have hno : ∀ u ∈ x, ¬ dist u v < r := fun u hu hlt =>
+    hcon ⟨u, hu, hxne0 u hu, hlt⟩
+  have hge : ∀ u ∈ x, 2 ≤ dist v u := by
+    intro u hu
+    rw [dist_comm]
+    linarith [le_of_not_gt (hno u hu), hr.1]
+  -- `v` lies in the annulus
+  have hvann : v ∈ ballAnnulus := by
+    rw [ckq_in_ball_annulus]
+    exact ⟨by simpa only [dist_zero_left] using hv2,
+      by simpa only [dist_zero_left] using hvc,
+      by intro h; rw [h] at hv2; norm_num at hv2⟩
+  -- `insert v x` is admissible ...
+  have hyW : W ⊆ insert v x := Subset.trans hWx (Set.subset_insert v x)
+  have hyP : Packing (insert v x) := PACKING_INSERT v x hxP hvx hge
+  have hyann : insert v x ⊆ ballAnnulus := by
+    intro u hu
+    rcases hu with rfl | hu
+    · exact hvann
+    · exact hxann hu
+  have hysep : ∀ p q : V3, S p → (insert v x) q → dist p q < r → p = q := by
+    intro p q hp hq hd
+    rcases hq with rfl | hqx
+    · exact absurd hd (hno p (hWx (hSW hp)))
+    · exact hxsep p q hp hqx hd
+  have hyWW : insert v x ∈ WW := by
+    simp only [hWW, Set.mem_setOf_eq]
+    exact ⟨hyW, hyP, hyann, hysep⟩
+  -- ... and one point bigger, contradicting maximality
+  have hcard : (insert v x).ncard ≤ a :=
+    hamax _ ⟨insert v x, hyWW, rfl⟩
+  rw [Set.ncard_insert_of_notMem hvx hxfin, hxa] at hcard
+  omega
 
 /-- HOL `dropout_pad2d3d` (counting_spheres.hl:1664). -/
 theorem dropout_pad2d3d (x : ℂ) : dropout3P22 (pad2d3dP22 x) = x := by
@@ -14398,7 +14477,65 @@ theorem FACET_OF_POLYHEDRON_EXPLICIT_ALT (V : Set (V3 × ℝ)) (P : Set V3)
     show P ∩ {p : V3 | (sel h).1 ⬝ᵥ p = (sel h).2} = c
     rw [hceq]
 
-/-- HOL `EXISTS_M_POLYHEDRON` (counting_spheres.hl:5888). GIANT. -/
+/-- Strict inequality of the `v`-scaled point `(b v / (v·v)) • v` against every
+other constraint `w ≠ v` (HOL `EXISTS_M_POLYHEDRON`, `COMMENT "1f"` block:
+`rcone_gt_facet` at `p := v`, `q := (b v / (v dot v)) % v`). -/
+private theorem p22w10_v_scale_lt {V : Set V3} {theta : V3 → ℝ}
+    (hne0 : ∀ v ∈ V, v ≠ 0)
+    (hthetapos : ∀ v ∈ V, 0 < theta v ∧ theta v < Real.pi / 2)
+    (htheta : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → theta v + theta w ≤ arcV 0 v w)
+    {v w : V3} (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w) :
+    w ⬝ᵥ (((‖v‖ * Real.cos (theta v)) / (v ⬝ᵥ v)) • v)
+      < ‖w‖ * Real.cos (theta w) := by
+  have h1 := hthetapos v hv
+  have h2 := hthetapos w hw
+  have hv0 : v ≠ 0 := hne0 v hv
+  have hc1 : Real.cos (theta v) < 1 := (cos_bounds_0_Pi2 _ h1.1 h1.2).2
+  have hp : v ∈ rconeGt 0 v (Real.cos (theta v)) := rcone_refl v _ hc1 hv0
+  have hgt := rcone_gt_facet (theta v) (theta w) v w
+    (((‖v‖ * Real.cos (theta v)) / (v ⬝ᵥ v)) • v) v h1 h2 (hne0 w hw) hp rfl
+    (htheta v hv w hw hvw)
+  -- `(s • v) ⬝ᵥ w = w ⬝ᵥ (s • v)` (`s = ‖v‖ cos θv / (v·v)`)
+  calc w ⬝ᵥ (((‖v‖ * Real.cos (theta v)) / (v ⬝ᵥ v)) • v)
+      = (((‖v‖ * Real.cos (theta v)) / (v ⬝ᵥ v)) • v) ⬝ᵥ w := dotV_comm w _
+    _ < ‖w‖ * Real.cos (theta w) := hgt
+
+/-- Strict inequality of the rcone point scaled to the hyperplane of `v`
+against every other constraint `w ≠ v` (HOL `EXISTS_M_POLYHEDRON`,
+`COMMENT "1g"` block: `rcone_gt_facet` at `p := x`, `q := (b v / (x dot v)) % x`). -/
+private theorem p22w10_x_scale_lt {V : Set V3} {theta : V3 → ℝ}
+    (hne0 : ∀ v ∈ V, v ≠ 0)
+    (hthetapos : ∀ v ∈ V, 0 < theta v ∧ theta v < Real.pi / 2)
+    (htheta : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → theta v + theta w ≤ arcV 0 v w)
+    {v w x : V3} (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
+    (hx : x ∈ rconeGt 0 v (Real.cos (theta v))) :
+    (((‖v‖ * Real.cos (theta v)) / (x ⬝ᵥ v)) • x) ⬝ᵥ w < ‖w‖ * Real.cos (theta w) := by
+  have h1 := hthetapos v hv
+  have h2 := hthetapos w hw
+  exact rcone_gt_facet (theta v) (theta w) v w _ x h1 h2 (hne0 w hw) hx rfl
+    (htheta v hv w hw hvw)
+
+/-- The `v`-scaled point is tight at `v` (same HOL block). -/
+private theorem p22w10_v_scale_tight {V : Set V3} {theta : V3 → ℝ}
+    (hne0 : ∀ v ∈ V, v ≠ 0) {v : V3} (hv : v ∈ V) :
+    v ⬝ᵥ (((‖v‖ * Real.cos (theta v)) / (v ⬝ᵥ v)) • v)
+      = ‖v‖ * Real.cos (theta v) := by
+  have hv0 : v ≠ 0 := hne0 v hv
+  have hvv : v ⬝ᵥ v ≠ 0 := by
+    have hpos : 0 < v ⬝ᵥ v := by rw [← norm_sq_eq_dot]; exact pow_pos (norm_pos_iff.mpr hv0) 2
+    linarith
+  rw [dotV_smul_right]
+  exact div_mul_cancel₀ _ hvv
+
+/-- HOL `EXISTS_M_POLYHEDRON` (counting_spheres.hl:5888). GIANT.
+
+Filled 2026-11-06 (lane `pa22-10-chain`) after the `weaklySaturatedP22`
+DEF-FIX: `b := ‖v‖ cos θv`, `h v := {p | v·p ≤ b v}`, `P := ⋂ v ∈ V, h v`,
+`f v := P ∩ {p | v·p = b v}`; `polyhedron P` by construction, boundedness by
+`TARJJUW`, `0 ∈ interior P` by the finite minimum margin `b v / ‖v‖`, the
+facet bijection by `FACET_OF_POLYHEDRON_EXPLICIT_ALT`, and
+`rconeGt ⊆ fchanged` by `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT` +
+`rcone_gt_facet`. -/
 theorem EXISTS_M_POLYHEDRON (V : Set V3) (theta : V3 → ℝ) (r : ℝ) (n : ℝ)
     (hV : V ⊆ ballAnnulus) (hP : Packing V)
     (hws : weaklySaturatedP22 V r (2 * h0))
@@ -14416,7 +14553,155 @@ theorem EXISTS_M_POLYHEDRON (V : Set V3) (theta : V3 → ℝ) (r : ℝ) (n : ℝ
       (∀ v ∈ V, b v = ‖v‖ * Real.cos (theta v)) ∧
       (∀ v ∈ V, rconeGt 0 v (Real.cos (theta v)) ⊆ fchanged (f v)) ∧
       (∀ v ∈ V, 0 < Real.cos (theta v) ∧ Real.cos (theta v) < 1) := by
-  sorry
+
+  classical
+  have hfin : V.Finite := hsize.1
+  have hVne : V.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
+  have hann : ∀ v ∈ V, 2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * h0 ∧ v ≠ 0 :=
+    fun v hv => (ckq_in_ball_annulus v).mp (hV hv)
+  have hne0 : ∀ v ∈ V, v ≠ 0 := fun v hv => (hann v hv).2.2
+  have hcos : ∀ v ∈ V, 0 < Real.cos (theta v) ∧ Real.cos (theta v) < 1 :=
+    fun v hv => cos_bounds_0_Pi2 _ (hthetapos v hv).1 (hthetapos v hv).2
+  -- HOL `COMMENT "0"`: the four witnesses
+  let b : V3 → ℝ := fun v => ‖v‖ * Real.cos (theta v)
+  let h : V3 → Set V3 := fun v => {p : V3 | v ⬝ᵥ p ≤ b v}
+  let P : Set V3 := ⋂ v ∈ V, h v
+  let f : V3 → Set V3 := fun v => P ∩ {p : V3 | v ⬝ᵥ p = b v}
+  have hbpos : ∀ v ∈ V, 0 < b v := by
+    intro v hv
+    exact mul_pos (by linarith [(hann v hv).1]) (hcos v hv).1
+  -- HOL `COMMENT "1"`: `polyhedron P`
+  have hpoly : polyhedron P := by
+    refine ⟨h '' V, hfin.image h, ?_, ?_⟩
+    · rw [Set.sInter_image]
+    · rintro g ⟨v, hv, rfl⟩
+      exact ⟨v, b v, hne0 v hv, rfl⟩
+  -- HOL `COMMENT "1c"/"1d"`: `0` is interior, with the finite minimum margin
+  obtain ⟨v0, hv0V, hv0min⟩ := Set.exists_min_image V (fun v => b v / ‖v‖) hfin hVne
+  have hnorm0 : 0 < ‖v0‖ := by linarith [(hann v0 hv0V).1]
+  have hεpos : 0 < b v0 / ‖v0‖ := div_pos (hbpos v0 hv0V) hnorm0
+  have hball : Metric.ball (0 : V3) (b v0 / ‖v0‖) ⊆ P := by
+    intro p hp
+    rw [Metric.mem_ball, dist_zero_right] at hp
+    show p ∈ ⋂ v ∈ V, h v
+    refine Set.mem_iInter₂.2 fun w hw => ?_
+    show w ⬝ᵥ p ≤ b w
+    have hwpos : 0 < ‖w‖ := by linarith [(hann w hw).1]
+    have hbw : ‖w‖ * (b v0 / ‖v0‖) ≤ b w := by
+      have hkey : b v0 / ‖v0‖ ≤ b w / ‖w‖ := hv0min w hw
+      calc ‖w‖ * (b v0 / ‖v0‖) ≤ ‖w‖ * (b w / ‖w‖) :=
+            mul_le_mul_of_nonneg_left hkey hwpos.le
+        _ = b w := mul_div_cancel₀ _ (ne_of_gt hwpos)
+    have hdot : w ⬝ᵥ p ≤ ‖w‖ * ‖p‖ := by
+      have hle : |w ⬝ᵥ p| ≤ ‖w‖ * ‖p‖ := by
+        rw [← Kepler.Geom.inner_eq_dot]
+        exact abs_real_inner_le_norm w p
+      exact le_trans (le_abs_self _) hle
+    calc w ⬝ᵥ p ≤ ‖w‖ * ‖p‖ := hdot
+      _ ≤ ‖w‖ * (b v0 / ‖v0‖) := mul_le_mul_of_nonneg_left hp.le hwpos.le
+      _ ≤ b w := hbw
+  have h0int : (0 : V3) ∈ interior P := by
+    rw [mem_interior_iff_mem_nhds]
+    exact Filter.mem_of_superset (Metric.ball_mem_nhds 0 hεpos) hball
+  -- HOL `COMMENT "1e"`: bounded, via `TARJJUW`
+  have hbdd : Bornology.IsBounded P := by
+    have hVuniv : V ⊆ univ \ Metric.ball (0 : V3) 2 := by
+      intro v hv
+      refine ⟨trivial, ?_⟩
+      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
+      linarith [(hann v hv).1]
+    have hPinter : P = ⋂₀ ((fun w => half_spaces w (b w)) '' V) := by
+      rw [Set.sInter_image]
+      rfl
+    obtain ⟨B, hB⟩ := TARJJUW (V := V) (P := P) (g := b) (r := r) (r' := 2 * h0)
+      hr.1 hr.2 hVuniv hfin hP hVne hws hPinter
+    refine (Metric.isBounded_iff_subset_closedBall (0 : V3)).2 ⟨B, ?_⟩
+    intro p hp
+    rw [Metric.mem_closedBall, dist_zero_right]
+    exact hB p hp
+  -- HOL `COMMENT "1f"`: the facet bijection via `FACET_OF_POLYHEDRON_EXPLICIT_ALT`
+  have hbij : Set.BijOn f V {c : Set V3 | FacetOf c P} := by
+    set V' : Set (V3 × ℝ) := (fun v : V3 => (v, b v)) '' V with hV'def
+    have hV'fin : V'.Finite := hfin.image _
+    have hV'pos : ∀ x ∈ V', 0 < x.2 := by
+      rintro x ⟨v, hv, rfl⟩
+      exact hbpos v hv
+    have hV'int : (⋂ x ∈ V', {p : V3 | x.1 ⬝ᵥ p ≤ x.2}) = P := by
+      ext p
+      constructor
+      · intro hp
+        rw [Set.mem_iInter₂] at hp ⊢
+        intro v hv
+        exact hp (v, b v) ⟨v, hv, rfl⟩
+      · intro hp
+        rw [Set.mem_iInter₂] at hp ⊢
+        rintro ⟨v, bv⟩ ⟨w, hw, he⟩
+        have h1 : v = w := (congrArg Prod.fst he).symm
+        have h2 : bv = b w := (congrArg Prod.snd he).symm
+        rw [h1, h2]
+        exact hp w hw
+    have hV'ne : ∀ x ∈ V', x.1 ≠ 0 := by
+      rintro x ⟨v, hv, rfl⟩
+      exact hne0 v hv
+    have hV'strict : ∀ x ∈ V', ∃ p : V3, x.1 ⬝ᵥ p = x.2 ∧
+        ∀ y ∈ V', y ≠ x → y.1 ⬝ᵥ p < y.2 := by
+      rintro x ⟨v, hv, rfl⟩
+      refine ⟨((‖v‖ * Real.cos (theta v)) / (v ⬝ᵥ v)) • v, ?_, ?_⟩
+      · exact p22w10_v_scale_tight hne0 hv
+      · rintro y ⟨w, hw, rfl⟩ hyne
+        refine p22w10_v_scale_lt hne0 hthetapos htheta hv hw ?_
+        intro hvw
+        exact hyne (by rw [hvw])
+    have hbij' := FACET_OF_POLYHEDRON_EXPLICIT_ALT V' P hV'fin h0int hV'pos hV'int
+      hV'ne hV'strict
+    have hpair : Set.BijOn (fun v : V3 => (v, b v)) V V' := by
+      refine ⟨?_, ?_, ?_⟩
+      · intro v hv
+        exact ⟨v, hv, rfl⟩
+      · intro v _ w _ he
+        exact congrArg Prod.fst he
+      · rintro x ⟨v, hv, rfl⟩
+        exact ⟨v, hv, rfl⟩
+    have hcomp := hbij'.comp hpair
+    have hfeq : ((fun x : V3 × ℝ => P ∩ {p : V3 | x.1 ⬝ᵥ p = x.2}) ∘
+        (fun v : V3 => (v, b v))) = f := by
+      funext v
+      rfl
+    rwa [hfeq] at hcomp
+  -- HOL `COMMENT "1g"/"1h"`: `rcone_gt ⊆ fchanged`
+  have hrcone : ∀ v ∈ V, rconeGt 0 v (Real.cos (theta v)) ⊆ fchanged (f v) := by
+    intro v hv x hx
+    have hxv : 0 < x ⬝ᵥ v := rcone_dot_pos v (Real.cos (theta v)) x (hcos v hv).1 hx
+    have hnum : 0 < ‖v‖ * Real.cos (theta v) :=
+      mul_pos (by linarith [(hann v hv).1]) (hcos v hv).1
+    set s : ℝ := (‖v‖ * Real.cos (theta v)) / (x ⬝ᵥ v) with hs
+    have hspos : 0 < s := div_pos hnum hxv
+    refine ⟨s • x, 1 / s, ?_, ?_, ?_⟩
+    · rw [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hspos), one_smul]
+    · -- `s • x` is in the relative interior of `f v`
+      show s • x ∈ intrinsicInterior ℝ (P ∩ {p : V3 | v ⬝ᵥ p = b v})
+      refine RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT h id b (s • x) v hfin
+        (fun w _ => rfl) rfl hv ?_ ?_
+      · -- tightness at `v`
+        show v ⬝ᵥ (s • x) = b v
+        calc v ⬝ᵥ (s • x) = s * (v ⬝ᵥ x) := dotV_smul_right v s x
+          _ = s * (x ⬝ᵥ v) := by rw [dotV_comm]
+          _ = b v := by
+                rw [hs]
+                exact div_mul_cancel₀ _ (ne_of_gt hxv)
+      · -- strict at the other `w`
+        intro w hw hwv
+        have hscale := p22w10_x_scale_lt hne0 hthetapos htheta hv hw hwv.symm hx
+        show w ⬝ᵥ (s • x) < b w
+        calc w ⬝ᵥ (s • x) = s * (w ⬝ᵥ x) := dotV_smul_right w s x
+          _ = (((‖v‖ * Real.cos (theta v)) / (x ⬝ᵥ v)) • x) ⬝ᵥ w := by
+                rw [hs, dotV_smul_left, dotV_comm x w]
+          _ < ‖w‖ * Real.cos (theta w) := hscale
+          _ = b w := rfl
+    · exact one_div_pos.mpr hspos
+  exact ⟨b, f, h, P, fun v _ => rfl, rfl, hbpos, hpoly, hbdd, h0int, hbij,
+    (fun v _ => rfl), (fun v _ => rfl), hrcone, hcos⟩
+
 
 /-- HOL `LMFUN_LE_1` (counting_spheres.hl:6155). -/
 theorem LMFUN_LE_1 (h : ℝ) (hh : 1 ≤ h) : lmfun h ≤ 1 := by
@@ -14437,8 +14722,14 @@ theorem FACET_FINITE (p f : Set V3) (hp : polyhedron p) (hf : FacetOf f p) :
 
 /-- HOL `BIJ_SUM` (counting_spheres.hl:6308). Filled: the image of `A`'s
 finset under the `BijOn` map is `B`'s finset (`Finset.sum_image` needs the
-`InjOn` in finset form). -/
-private theorem BIJ_SUM {a i : Type*} [DecidableEq a] [DecidableEq i] {A : Set a} {B : Set i}
+`InjOn` in finset form).
+
+Named `_p22` (2026-11-06, lane `pa22-10-chain`): PA22 now imports
+`PackingAuto3`, which already declares a (different, `Finset`-based)
+non-private `Kepler.Text.BIJ_SUM` (PackingAuto3:476); a same-named `private`
+declaration is rejected by Lean.  This helper has no consumers, so the rename
+is local to this file. -/
+private theorem BIJ_SUM_p22 {a i : Type*} [DecidableEq a] [DecidableEq i] {A : Set a} {B : Set i}
     [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
     (f : i → ℝ) (ab : a → i) (h : Set.BijOn ab A B) (hA : A.Finite) (hB : B.Finite) :
     (∑ x ∈ hA.toFinset, f (ab x)) = (∑ y ∈ hB.toFinset, f y) := by
@@ -15787,8 +16078,8 @@ theorem LMFUN_INEQ_CENTER_SUBSET (V W : Set V3) (hfV : V.Finite) (hfW : W.Finite
     (fun i _ _ => lmfun_nonneg_p22 _)
 
 /-! ### E. HOL `SATURATE_BALL_ANNULUS`（counting_spheres.hl:6221）
-真证：经 :6783 `weak_saturation`（其 `weaklySaturatedP22` 合取维持桩依赖，
-其余合取全部实装）+ D 组两件。-/
+真证：经 :6783 `weak_saturation`（其 `weaklySaturatedP22` 合取自 2026-11-06 DEF-FIX 起
+是真语义，其余合取全部实装）+ D 组两件。-/
 
 theorem SATURATE_BALL_ANNULUS (W S : Set V3) (r : ℝ) (hP : Packing W)
     (hW : W ⊆ ballAnnulus) (hloc : ¬ localAnnulusInequality W) (hSW : S ⊆ W)
```

### 2.2 验收

- `EXISTS_M_POLYHEDRON` 陈述逐字不动；`weak_saturation` 陈述逐字不动；
  `weaklySaturatedP22` 仅 def body 变（用户已批的 DEF-FIX）。
- 真证结构：`b v = ‖v‖ cos θv`、`h v = {p | v·p ≤ b v}`、
  `P = ⋂ v ∈ V, h v`、`f v = P ∩ {p | v·p = b v}`；`polyhedron P` 构造即得，
  `IsBounded` 走 `TARJJUW`，`0 ∈ interior P` 取有限最小边距
  `min_v b v / ‖v‖`，facet 双射走 `FACET_OF_POLYHEDRON_EXPLICIT_ALT`，
  `rconeGt ⊆ fchanged` 走 `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT` +
  `rcone_gt_facet`。
- 编排者实测（车道日志原样）：`lake env lean Kepler/Text/PackingAuto22.lean`
  **RC=0 / 0 error** / `declaration uses sorry` = 4（改前 5）。
- 下游：`LocalBridge`（唯一非 Assembly 的 PA22 消费者）standalone
  RC=0 / 0 error；Assembly 面未由车道构建（按 AGENTS §4 岛协议由编排者跑）。

### 2.3 编排者独立复核（2026-11-06，闸前实测，不采信车道自述）

- patch：相对 HEAD `da8c2df2` 8 hunk / +307−16，`git apply --check` **RC=0**；
  删除面逐行核对 = 旧 def body + 旧 `trivial` 证明体 + 旧 `sorry` +`BIJ_SUM`
  私有声明头 + 过期 docstring，**无任何定理陈述行**。
- PA22 独立编译：`lake env lean -o .lake/build/lib/lean/Kepler/Text/PackingAuto22.olean
  Kepler/Text/PackingAuto22.lean` ⇒ **RC=0 / 0 error / `declaration uses sorry` = 4**
  / 120.36s（改前 5；余 4 条 = `insert_v:2080` / `vol_solid_triangle_ortho:6777` /
  `BIJ_EDGES_DART_FACE:13623` / `BIJ_DART_POLYHEDGE:14057`，均不在柱③路径）。
- `#print axioms` 独立复跑（`/tmp/pillar3_probe/verify1.lean`）：
  `weak_saturation` / `SATURATE_BALL_ANNULUS` / `DLWCHEM_full` / `XULJEPR_full` /
  `EXISTS_M_POLYHEDRON` **全部 = `[propext, Classical.choice, Quot.sound]`**。
- `#print weaklySaturatedP22` = `fun V r c => Kepler.Text.weakly_saturated V r c`
  —— 桩已真化为别名，零 body 复制。
- **桩已消失的阴性对照**：改前后都是同一批 sorry（只少 #10 一条），
  说明不是靠新增 `sorry` 换出来的绿色。
- Assembly 岛协议重建（AGENTS §4）：`lake env lean -o .../Assembly.olean Kepler/Assembly.lean`
  ⇒ **RC=0 / 0 error / 64 条 `declaration uses sorry`** / 46.90s，与基线 64 一致。
- 根面（北极星口径）：`lake env lean Kepler/Final.lean` ⇒ **628 行 = 624
  `native_decide` + `propext` + `Classical.choice` + `Quot.sound` + `sorryAx`**，
  与基线 P 逐项一致 ⇒ 本笔**不扰动根面**（PA22 仍未被根 reach）。
