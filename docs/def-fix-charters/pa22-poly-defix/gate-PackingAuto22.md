# DEF-FIX 闸门章程 · `Kepler/Text/PackingAuto22.lean`
# （多面体 fan 假桩真化：`hypermap1OfFanxP22` / `verticesP22` / `edgesP22` /
#   `eFanP22` / `d1FanP22` / `dartsetLeadsIntoFanP22` /
#   `topologicalComponentYfanP22` + 新增 `WBLARHH_BIJ`）

车道：`pa22-poly-defix`（`fcdjdot` 柱③ 的唯一通路；上游侦察
`pa22-fanstub-scout` 的 C3/C4/D3/D4）。基线 HEAD `17d1df89`（工单写的
`b07a1722` 与 HEAD 对 PackingAuto22 逐字节相同：`git diff b07a1722 17d1df89 --
lean/Kepler/Text/PackingAuto22.lean` 为空）。

HOL 锚（本笔定义/陈述的来源行）：
`packing/counting_spheres.hl:4821`（`BIJ_FACET_HYPERFACE`）、
`packing/counting_spheres.hl:4842`（`POLYHEDRON_CONFORMING_FAN`）、
`packing/counting_spheres.hl:4855`（`POLYHEDRON_D1_D`）、
`packing/counting_spheres.hl:4866`（`POLYHEDRON_PLAIN`）、
`packing/counting_spheres.hl:4905`（`POLYHEDRON_NODE_3`）、
`packing/counting_spheres.hl:4955`（`POLYHEDRON_TGJISOK`）、
`packing/counting_spheres.hl:5003`（`EDGE_PAIR_pr23`）、
`packing/counting_spheres.hl:5020`（`EDGE_pr23`）、
`packing/counting_spheres.hl:5119`（`INJ_EDGES_FACE_pr23`）、
`packing/counting_spheres.hl:5178`（`BIJ_EDGES_DART_FACE`）、
`packing/counting_spheres.hl:5286`（`HYPERFACE_EXISTS`）、
`packing/counting_spheres.hl:5301`（`BIJ_DART_POLYEDGE`）；
`packing/polyhedron.hl:3158`（`WBLARHH`）、
`packing/polyhedron.hl:3180`（`WBLARHH_BIJ`）；
`fan/fan_defs.hl:128`（contracted dart）、`fan/fan_defs.hl:131-150`（e/n/f fan）、
`fan/fan_defs.hl:952`（`d1_fan`）、`fan/fan_defs.hl:244-275`（`topological_component_yfan`）；
`flyspeck_multivariate.ml:6884`（`vertices`）、`flyspeck_multivariate.ml:6887`（`edges`）、
`polytope1.ml:1506`（`facet_of`，`FacetOf` 陈述）、`polytope1.ml:2546`（`polyhedron`）、
`polytope1.ml:2847`（`edge_of`，`edges` 陈述）；`conforming.hl:2249`
（`pr23 = (x,y,z,t) ↦ (y,z)`）；`general/sphere.hl:292`（`cone0`）、
`general/sphere.hl:258`（`arclength`，**本笔不改**，仅作 PA22 上下文）。
注：工单要求的 `ineq.hl` 锚在本 checkout 不存在（`find . -name 'ineq.hl'`
空），那批数值银行属 `_797` 章程，与本笔定义层无关。

对象（改前，7 个假桩 + 1 个派生）：
`hypermap1OfFanxP22`（`:236`，空 hypermap）、`dFanP22`（`:242`）、
`d1FanP22`（`:247`，`∅`）、`eFanP22`（`:251`，`id`）、
`verticesP22`（`:258`，`∅`）、`edgesP22`（`:262`，`∅`）、
`dartsetLeadsIntoFanP22`（`:265`，`∅`）、
`topologicalComponentYfanP22`（`:269`，`True`）；另 `Dart3 = V3×V3×V3`
（fan 章真实的 contracted dart 是 `V3×V3`，见 `fan_defs.hl:128`）。
改后分别接线到树内真件：`Fan.hypermapOfFan` / `Fan.dart1OfFan` /
`Fan.eFanPair` / `Set.extremePoints ℝ p` / `Polytope.edges p` /
`dartsetLeadsIntoFan` / `Fan.topologicalComponentYfan`
（全部 `#print axioms` = 标准三，实测见 `Evidence.md`）。

`DF_SORRY_NET=-3`：`declaration uses sorry` 13 → 10（真证 #4/#5/#6/#7 四处
`sorry`；`BIJ_EDGES_DART_FACE` 由空 faceSet 的假真空证明转为真陈述后缺
`Cfyxfty.CFYXFTY0/1`（未移植）→ 保留一处 `sorry`）。
`DF_NAMES`：`Dart3 pr2 pr3 hypermap1OfFanxP22 dFanP22 d1FanP22 eFanP22
verticesP22 edgesP22 dartsetLeadsIntoFanP22 topologicalComponentYfanP22
edgesP22_eq_edgesP7 dFanP22_eq_dart1 fanOfPolyhedronP22
hypermapOfPolyhedronP22 setOfEdgeP22_eq_fan p22_pair_ne p22_edgeMap_eq
p22_edgeMap_fix p22_plain_edgeMap p22_edgeMap_ne conformingFanOfPolyhedronP22
WBLARHH_BIJ BIJ_FACET_HYPERFACE POLYHEDRON_CONFORMING_FAN POLYHEDRON_D1_D
POLYHEDRON_PLAIN POLYHEDRON_NODE_3 POLYHEDRON_TGJISOK EDGE_PAIR_pr23
EDGE_pr23 INJ_EDGES_FACE_pr23 BIJ_EDGES_DART_FACE HYPERFACE_EXISTS
BIJ_DART_POLYEDGE`。
**围栏不含 `---`/`+++`/`diff --git` 头**（闸门用 `grep -E '^-'` 抓删除行，
会把 `--- a/…` 误当删除行）。

### 2.1 改动围栏

```diff
@@ -65,13 +65,19 @@
     `Icc a b`; `has_real_derivative f f' (atreal x within s)` <->
     `HasDerivWithinAt f f' s x`; the Calc_derivative artifact `derived_form`
     is encoded pointwise as `derivedFormP22 f f' x s`.
-  - Fan/hypermap kit: `hypermap1_of_fanx (x,V,E)` is NOT ported anywhere in
-    this checkout (ConformingDefs.lean:26), so it is stubbed here as
-    `hypermap1OfFanxP22 : Hypermap Dart3` (Dart3 = V3 × V3 × V3); flyspeck
+  - Fan/hypermap kit: `hypermap1_of_fanx (x,V,E)` is `Fan.hypermapOfFan`
+    (Fan.lean:1189; the `hfan : FAN x V E` proof argument is the same
+    irrelevance-witness convention as ConformingDefs.lean:14-18); flyspeck
     `dart/edge_map/face_map/node/face_set/number_of_faces/plain_hypermap/
-    simple_hypermap H` map to the `Hypermap` API fields; `d1_fan`, `e_fan`,
-    `vertices p`, `edges p`, `dartset_leads_into_fan`,
-    `topological_component_yfan` are `_p22` opaque stubs.
+    simple_hypermap H` map to the `Hypermap` API fields.  DEF-FIX
+    (`docs/def-fix-charters/pa22-poly-defix/gate-PackingAuto22.md`): the
+    former `_p22` stubs (`verticesP22`/`edgesP22`/`dartsetLeadsIntoFanP22`
+    = `∅`, `topologicalComponentYfanP22` = `True`, `d1FanP22` = `∅`,
+    `eFanP22` = `id`, `hypermap1OfFanxP22` = the empty hypermap) are now
+    `Set.extremePoints ℝ p`, `Polytope.edges p`, `Fan.dart1OfFan`,
+    `Fan.eFanPair`, `dartsetLeadsIntoFan`, `Fan.topologicalComponentYfan`,
+    `Fan.hypermapOfFan`.  The dart type is the contracted pair `V3 × V3`
+    (`Fan.contractedDart`, fan_defs.hl:128), matching `Fan.hypermapOfFan`.
   - `cone0 x U` is DEFINED here as `affGt {x} U` (flyspeck cone0 = aff_gt of
     the apex through U; CONE0_AFF_GT becomes rfl).
   - `regular_spherical_polygon_area th k` is DEFINED here in closed form
@@ -81,9 +87,6 @@
     `local_annulus_inequality`, `pack_ineq_def_a` are `_p22` stubs.
 
 ## NEEDS (giant fill-in markers)
-  - `hypermap1OfFanxP22`: NEEDS `hypermap1_of_fanx` (fan.hl / Planarity lane).
-  - `verticesP22`, `edgesP22`, `dartsetLeadsIntoFanP22`,
-    `topologicalComponentYfanP22`: NEEDS polytope/topology fan lanes.
   - `weaklySaturatedP22`: NEEDS PackingAuto3 (pack3.hl) — no olean on this
     branch.  `localAnnulusInequalityP22`, `packIneqDefAP22`: NEEDS pack1.hl
     (PackingAuto1, no olean).  `asnFnhkP22`: NEEDS Ysskqoy.hl
@@ -104,6 +107,8 @@
 import Kepler.Text.PackingAuto15
 import Kepler.Text.Polytope
 import Kepler.Text.IneqClosureDefs
+import Kepler.Text.PolyAuto7
+import Kepler.Text.ConformingAuto23
 import Mathlib
 
 set_option maxHeartbeats 5000000
@@ -215,59 +220,109 @@
 /-- HOL `measurable s` (measure.hl) on ℝ³. -/
 def measurableP22 (s : Set V3) : Prop := MeasurableSet s
 
-/-! ## `_p22` stub layer (missing upstream defs; see NEEDS in header) -/
+/-! ## `_p22` fan kit: DEF-FIX wiring to the in-tree fan/polytope API
 
-/-- HOL dart type: `real^3#3` (the `hypermap1_of_fanx` darts are `(u,v,w)`
-vertex triples). -/
-abbrev Dart3 := V3 × V3 × V3
+  (`docs/def-fix-charters/pa22-poly-defix/gate-PackingAuto22.md`)
 
-noncomputable instance : DecidableEq Dart3 := Classical.decEq _
+  The former stubs here (`hypermap1OfFanxP22` = the empty hypermap,
+  `verticesP22`/`edgesP22`/`dartsetLeadsIntoFanP22` = `∅`,
+  `topologicalComponentYfanP22` = `True`, `d1FanP22` = `∅`, `eFanP22` =
+  `id`) made the six statements #4–#8 FALSE-AS-STATED.  They are now the
+  real Flyspeck objects, all already ported and standard-three:
+  `Fan.hypermapOfFan`, `Set.extremePoints`, `Polytope.edges`,
+  `Fan.dart1OfFan`, `Fan.eFanPair`, `dartsetLeadsIntoFan`,
+  `Fan.topologicalComponentYfan`.  Darts are the contracted pairs of the
+  fan chapter (HOL 4-tuples `(x,v,w,w1)` ↦ `(v,w)`, `Fan.contractedDart`),
+  so `pr2`/`pr3` (HOL `pr23 = (x,y,z,t) ↦ (y,z)`, conforming.hl:2249) are
+  the two components. -/
 
-/-- HOL `pr2 (u,v,w) = v`. -/
-def pr2 (d : Dart3) : V3 := d.2.1
+/-- HOL dart type: the contracted dart `(v,w)` of `hypermap1_of_fanx`
+(`real^3#2`; `Fan.contractedDart`, fan_defs.hl:128). -/
+abbrev Dart3 := V3 × V3
 
-/-- HOL `pr3 (u,v,w) = w`. -/
-def pr3 (d : Dart3) : V3 := d.2.2
+/-- HOL `pr2` (conforming.hl:2249 `pr23 = (x,y,z,t) ↦ (y,z)`): the second
+dart component. -/
+def pr2 (d : Dart3) : V3 := d.1
 
-/-- NEEDS `hypermap1_of_fanx (x,V,E)` (fan.hl; Planarity lane). Stub value:
-the empty hypermap. -/
-theorem permutesOn_refl (s : Finset α) : PermutesOn (Equiv.refl α) s := fun _ _ => rfl
+/-- HOL `pr3` (conforming.hl:2249): the third dart component. -/
+def pr3 (d : Dart3) : V3 := d.2
 
-def hypermap1OfFanxP22 (x : V3) (V : Set V3) (E : Set (Set V3)) : Hypermap Dart3 :=
-  { darts := ∅, edgeMap := .refl _, nodeMap := .refl _, faceMap := .refl _,
-    edgeMap_permutes := permutesOn_refl _, nodeMap_permutes := permutesOn_refl _,
-    faceMap_permutes := permutesOn_refl _, comp_eq_one := rfl }
+/-- HOL `hypermap1_of_fanx (x,V,E)` (fan.hl) — the proof-parameterized
+`Fan.hypermapOfFan` (`Hypermap (V3 × V3)`; `hfan` is its irrelevance
+witness, the convention of `ConformingDefs.lean:14-18`). -/
+noncomputable def hypermap1OfFanxP22 (x : V3) (V : Set V3) (E : Set (Set V3))
+    (hfan : Fan.FAN x V E) : Hypermap Dart3 :=
+  Fan.hypermapOfFan x V E hfan
 
-/-- HOL `d_fan (x,V,E)`: the darts of `hypermap1_of_fanx (x,V,E)`. -/
-def dFanP22 (x : V3) (V : Set V3) (E : Set (Set V3)) : Set Dart3 :=
-  (hypermap1OfFanxP22 x V E).darts
-
-/-- NEEDS HOL `d1_fan (x,V,E)` (fan.hl; distinct from `d_fan` a priori).
-Stub: empty. -/
-def d1FanP22 (x : V3) (V : Set V3) (E : Set (Set V3)) : Set Dart3 := ∅
+/-- HOL `d_fan (x,V,E)` = `dart (hypermap1_of_fanx (x,V,E))`. -/
+noncomputable def dFanP22 (x : V3) (V : Set V3) (E : Set (Set V3))
+    (hfan : Fan.FAN x V E) : Set Dart3 :=
+  (hypermap1OfFanxP22 x V E hfan).darts
 
-/-- NEEDS HOL `e_fan (x,V,E) d` (fan.hl): next dart around `pr2 d`.
-Stub: identity. -/
-def eFanP22 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : Dart3) : Dart3 := d
+/-- HOL `d1_fan (x,V,E)` (fan.hl:952, the `(x,v,w,σ v w)` darts): under
+the contracted encoding its `(v,w)` projection is `Fan.dart1OfFan`. -/
+def d1FanP22 (x : V3) (V : Set V3) (E : Set (Set V3)) : Set Dart3 :=
+  Fan.dart1OfFan V E
 
+/-- HOL `e_fan (x,V,E)` (fan.hl): the edge swap `Fan.eFanPair`. -/
+def eFanP22 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : Dart3) : Dart3 :=
+  Fan.eFanPair V E d
+
 /-- HOL `set_of_edge v V E`: vertices adjacent to `v`. -/
 def setOfEdgeP22 (v : V3) (V : Set V3) (E : Set (Set V3)) : Set V3 :=
   {w : V3 | {v, w} ∈ E}
 
-/-- NEEDS HOL `vertices p` (polytope vertex set; polytope lane). Stub: ∅. -/
-def verticesP22 (p : Set V3) : Set V3 := ∅
+/-- HOL `vertices p` (flyspeck_multivariate.ml:6884): the extreme points. -/
+def verticesP22 (p : Set V3) : Set V3 := Set.extremePoints ℝ p
 
-/-- NEEDS HOL `edges p` polytope-edge set (polytope lane; Polytope.`edges`
-exists but is not wired to the fan kit). Stub: ∅. -/
-def edgesP22 (p : Set V3) : Set (Set V3) := ∅
+/-- HOL `edges p` (flyspeck_multivariate.ml:6887) = `Polytope.edges`
+(`{e | ∃ v w, e = {v,w} ∧ edgeOf (segment ℝ v w) p}`). -/
+def edgesP22 (p : Set V3) : Set (Set V3) := edges p
 
-/-- NEEDS HOL `dartset_leads_into_fan (x,V,E) f` (fan.hl). Stub: ∅. -/
+/-- HOL `dartset_leads_into_fan (x,V,E) f` (fan.hl): `dartsetLeadsIntoFan`. -/
 def dartsetLeadsIntoFanP22 (x : V3) (V : Set V3) (E : Set (Set V3))
-    (f : Set Dart3) : Set V3 := ∅
+    (f : Set Dart3) : Set V3 :=
+  dartsetLeadsIntoFan x V E f
 
-/-- NEEDS HOL `topological_component_yfan (x,V,E) U` (yfan.hl). Stub. -/
+/-- HOL `topological_component_yfan (x,V,E) U` (yfan.hl): membership in
+`Fan.topologicalComponentYfan`. -/
 def topologicalComponentYfanP22 (x : V3) (V : Set V3) (E : Set (Set V3))
-    (U : Set V3) : Prop := True
+    (U : Set V3) : Prop :=
+  U ∈ Fan.topologicalComponentYfan x V E
+
+/-- DEF-FIX bridge: `Polytope.edges p` agrees with the edge set used by
+`POLYHEDRON_FAN`/`WBLARHH`/`AMHFNXP_BIJ` (`edges_p7`, which unpacks
+`edgeOf` inline and replaces `affDim (segment ℝ v w) = 1` by `v ≠ w`,
+cf. `affDim_segment`). -/
+theorem edgesP22_eq_edgesP7 (p : Set V3) : edgesP22 p = edges_p7 p := by
+  ext e
+  constructor
+  · rintro ⟨v, w, rfl, hface, hdim⟩
+    exact ⟨v, w, rfl, (affDim_segment v w).mp hdim, hface.1, hface.2.1, hface.2.2⟩
+  · rintro ⟨v, w, rfl, hvw, hsub, hconv, hface⟩
+    exact ⟨v, w, rfl, ⟨hsub, hconv, hface⟩, (affDim_segment v w).mpr hvw⟩
+
+/-- DEF-FIX bridge: `dFanP22` is the contracted HOL `d1_fan` (the
+`finite_dart1_fan` finset of `hypermapOfFan` is exactly `dart1OfFan`). -/
+theorem dFanP22_eq_dart1 (x : V3) (V : Set V3) (E : Set (Set V3))
+    (hfan : Fan.FAN x V E) : dFanP22 x V E hfan = Fan.dart1OfFan V E := by
+  have h := (Fan.finite_dart1_fan hfan).coe_toFinset
+  simpa only [dFanP22, hypermap1OfFanxP22, Fan.hypermapOfFan] using h
+
+/-- The `FAN` witness of a bounded polyhedron (`POLYHEDRON_FAN` inlined as
+in counting_spheres.hl:4842, with `edgesP22 = Polytope.edges`). -/
+theorem fanOfPolyhedronP22 (p : Set V3) (hb : Bornology.IsBounded p)
+    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) :
+    Fan.FAN 0 (verticesP22 p) (edgesP22 p) := by
+  rw [edgesP22_eq_edgesP7]
+  exact POLYHEDRON_FAN hb hp hi
+
+/-- `hypermap1_of_fanx (vec 0, vertices p, edges p)` for a bounded
+polyhedron (the term used by `BIJ_FACET_HYPERFACE`/`HYPERFACE_EXISTS`/
+`BIJ_DART_POLYEDGE`). -/
+noncomputable def hypermapOfPolyhedronP22 (p : Set V3) (hb : Bornology.IsBounded p)
+    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) : Hypermap Dart3 :=
+  hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p) (fanOfPolyhedronP22 p hb hp hi)
 
 /-- HOL `cone0 x U` (sphere.hl:290 `cone0 v S = affsign sgn_gt {v} S`), i.e.
 the open cone `aff_gt {x} U` (`Kepler.Geom.affGt`, counting_spheres.hl:3770
@@ -12768,67 +12823,282 @@
     rw [hxmem.2]
     exact hex
 
-/-- HOL `BIJ_FACET_HYPERFACE` (counting_spheres.hl:4821). GIANT. -/
+/-- `setOfEdgeP22` agrees with `Fan.setOfEdge` under `FAN` (the extra
+`w ∈ V` conjunct is implied by `⋃₀ E ⊆ V`). -/
+private theorem setOfEdgeP22_eq_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
+    (hfan : Fan.FAN x V E) (v : V3) :
+    setOfEdgeP22 v V E = Fan.setOfEdge v V E := by
+  ext w
+  simp only [setOfEdgeP22, Fan.setOfEdge, Set.mem_setOf_eq]
+  exact ⟨fun hw => ⟨hw, hfan.1 (Set.mem_sUnion.mpr ⟨{v, w}, hw, by simp⟩)⟩,
+    fun hw => hw.1⟩
+
+/-- Two distinct vertices of an edge of a `FAN` (edges have cardinality two,
+`Fan.Graph`). -/
+private theorem p22_pair_ne {x : V3} {V : Set V3} {E : Set (Set V3)}
+    (hfan : Fan.FAN x V E) {a b : V3} (hab : ({a, b} : Set V3) ∈ E) : a ≠ b := by
+  have h2 : ({a, b} : Set V3).ncard = 2 := by
+    obtain ⟨hf, hc⟩ := hfan.2.1 _ hab
+    rw [← hc, Set.ncard_eq_toFinset_card _ hf]
+  intro heq
+  have hsingle : ({a, b} : Set V3) = {b} := by ext z; simp [heq]
+  rw [hsingle, Set.ncard_singleton] at h2
+  norm_num at h2
+
+/-- `conforming_fan` of a bounded polyhedron (counting_spheres.hl:4842):
+`POLYHEDRON_FAN` + `POLYTOPE_FAN80` + `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`
+into `PIIJBJK`. -/
+theorem conformingFanOfPolyhedronP22 (p : Set V3) (hb : Bornology.IsBounded p)
+    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) :
+    conformingFan 0 (verticesP22 p) (edgesP22 p) (fanOfPolyhedronP22 p hb hp hi) := by
+  have hfan := fanOfPolyhedronP22 p hb hp hi
+  refine PIIJBJK 0 (verticesP22 p) (edgesP22 p) hfan ⟨hfan, ?_, ?_⟩
+  · intro v hv
+    have h := CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON hb hp hi v hv
+    rwa [← edgesP22_eq_edgesP7 p] at h
+  · have h := POLYTOPE_FAN80 hb hp hi
+    rwa [← edgesP22_eq_edgesP7 p] at h
+
+/-- HOL `WBLARHH_BIJ` (polyhedron.hl:3180): `dartset_leads_into_fan` is a
+bijection from the face set onto the topological components — the ~12-line
+corollary of `WBLARHH` (:3158) + `PIIJBJK`.  (Left unported by PolyAuto7;
+added here because #4/#7 consume it.) -/
+theorem WBLARHH_BIJ (p : Set V3) (hb : Bornology.IsBounded p) (hp : polyhedron p)
+    (hi : (0 : V3) ∈ interior p) :
+    Set.BijOn (dartsetLeadsIntoFanP22 0 (verticesP22 p) (edgesP22 p))
+      ((hypermapOfPolyhedronP22 p hb hp hi).faceSet : Set (Set Dart3))
+      (Fan.topologicalComponentYfan 0 (verticesP22 p) (edgesP22 p)) := by
+  let hfan : Fan.FAN 0 (verticesP22 p) (edgesP22 p) := fanOfPolyhedronP22 p hb hp hi
+  have hcard : ∀ v ∈ verticesP22 p,
+      1 < (Fan.setOfEdge v (verticesP22 p) (edgesP22 p)).ncard := by
+    intro v hv
+    have h := CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON hb hp hi v hv
+    rwa [← edgesP22_eq_edgesP7 p] at h
+  have h80 : fan80 0 (verticesP22 p) (edgesP22 p) := by
+    have h := POLYTOPE_FAN80 hb hp hi
+    rwa [← edgesP22_eq_edgesP7 p] at h
+  have hbij := (conformingFanOfPolyhedronP22 p hb hp hi).2.2.1
+  refine ⟨?_, ?_, ?_⟩
+  · intro f hf
+    exact dartset_leads_into_is_topological_component_yfan hfan hcard h80 hf
+  · intro f1 hf1 f2 hf2 heq
+    have hs := dartset_leads_into_is_topological_component_yfan hfan hcard h80 hf1
+    obtain ⟨g, -, huniq⟩ := hbij _ hs
+    exact (huniq f1 ⟨hf1, rfl⟩).trans (huniq f2 ⟨hf2, heq⟩).symm
+  · intro s hs
+    obtain ⟨f, ⟨hf, hsf⟩, -⟩ := hbij s hs
+    exact ⟨f, hf, hsf.symm⟩
+
+/-- HOL `BIJ_FACET_HYPERFACE` (counting_spheres.hl:4821): `BIJ_TRANS`
+through `topological_component_yfan` — `AMHFNXP_BIJ` (facets → components)
+composed with `WBLARHH_BIJ` (faces → components). -/
 theorem BIJ_FACET_HYPERFACE (p : Set V3) (hp : polyhedron p) (hb : Bornology.IsBounded p)
     (hi : (0 : V3) ∈ interior p) :
     ∃ b : Set V3 → Set Dart3, Set.BijOn b
       {f : Set V3 | FacetOf f p}
-      ((hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).faceSet : Set (Set Dart3)) := by
-  sorry
+      ((hypermapOfPolyhedronP22 p hb hp hi).faceSet : Set (Set Dart3)) := by
+  have h1 : Set.BijOn fchanged_p7 {f : Set V3 | FacetOf_p7 f p}
+      (Fan.topologicalComponentYfan 0 (verticesP22 p) (edgesP22 p)) := by
+    rw [edgesP22_eq_edgesP7]
+    exact AMHFNXP_BIJ hb hp hi
+  haveI : Nonempty (Set Dart3) := ⟨∅⟩
+  obtain ⟨g, hg⟩ := BIJ_SYM
+    ((hypermapOfPolyhedronP22 p hb hp hi).faceSet : Set (Set Dart3))
+    (Fan.topologicalComponentYfan 0 (verticesP22 p) (edgesP22 p))
+    ⟨_, WBLARHH_BIJ p hb hp hi⟩
+  exact BIJ_TRANS _ _ _ ⟨_, h1⟩ ⟨g, hg⟩
 
-/-- HOL `POLYHEDRON_CONFORMING_FAN` (counting_spheres.hl:4842). GIANT. -/
+/-- HOL `POLYHEDRON_CONFORMING_FAN` (counting_spheres.hl:4842). -/
 theorem POLYHEDRON_CONFORMING_FAN (p : Set V3) (hb : Bornology.IsBounded p)
     (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) :
     ∃ h : Fan.FAN 0 (verticesP22 p) (edgesP22 p),
-      conformingFan 0 (verticesP22 p) (edgesP22 p) h := by
-  sorry
+      conformingFan 0 (verticesP22 p) (edgesP22 p) h :=
+  ⟨fanOfPolyhedronP22 p hb hp hi, conformingFanOfPolyhedronP22 p hb hp hi⟩
 
-/-- HOL `POLYHEDRON_D1_D` (counting_spheres.hl:4855). Both sides are the empty
-dart set under the `hypermap1OfFanxP22`/`d1FanP22` stub encoding. -/
+/-- HOL `POLYHEDRON_D1_D` (counting_spheres.hl:4855): `d_fan = d1_fan`
+(both are the contracted `dart1OfFan` under the `hypermapOfFan` encoding). -/
 theorem POLYHEDRON_D1_D (p : Set V3) (hb : Bornology.IsBounded p) (hp : polyhedron p)
     (hi : (0 : V3) ∈ interior p) :
-    dFanP22 0 (verticesP22 p) (edgesP22 p) = d1FanP22 0 (verticesP22 p) (edgesP22 p) := by
-  simp [dFanP22, d1FanP22, hypermap1OfFanxP22]
+    dFanP22 0 (verticesP22 p) (edgesP22 p) (fanOfPolyhedronP22 p hb hp hi)
+      = d1FanP22 0 (verticesP22 p) (edgesP22 p) :=
+  dFanP22_eq_dart1 0 (verticesP22 p) (edgesP22 p) (fanOfPolyhedronP22 p hb hp hi)
 
-/-- HOL `POLYHEDRON_PLAIN` (counting_spheres.hl:4866). The stub hypermap has
-identity edge map, hence is plain. -/
-theorem POLYHEDRON_PLAIN (p : Set V3) (hb : Bornology.IsBounded p) (hp : polyhedron p)
-    (hi : (0 : V3) ∈ interior p) :
-    (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).Plain := by
-  simp only [hypermap1OfFanxP22, Hypermap.Plain]
-  exact Equiv.Perm.ext fun _ => rfl
+/-- `hypermapOfFan` 的 `edgeMap` 在 dart 上就是 `eFanPair`（HOL
+`hypermap_of_fan_rep` 的 e-分量；同 ConformingAuto23 的私有版本）。 -/
+private theorem p22_edgeMap_eq (x : V3) (V : Set V3) (E : Set (Set V3))
+    (hfan : Fan.FAN x V E) {d : Dart3} (hd : d ∈ Fan.dart1OfFan V E) :
+    (Fan.hypermapOfFan x V E hfan).edgeMap d = Fan.eFanPair V E d := by
+  unfold Fan.hypermapOfFan Fan.extendPerm
+  simp only [Equiv.ofBijective_apply]
+  unfold Fan.res
+  rw [if_pos (by simpa [(Fan.finite_dart1_fan hfan).coe_toFinset] using hd)]
 
-/-- HOL `POLYHEDRON_NODE_3` (counting_spheres.hl:4905). Vacuous: the stub dart
-set is empty. -/
-theorem POLYHEDRON_NODE_3 (p : Set V3) (x : Dart3) (hb : Bornology.IsBounded p)
-    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p)
-    (hx : x ∈ dFanP22 0 (verticesP22 p) (edgesP22 p)) :
-    3 ≤ ((hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).node x).ncard := by
-  simp [dFanP22, hypermap1OfFanxP22] at hx
+/-- dart 集外 `edgeMap` 恒等。 -/
+private theorem p22_edgeMap_fix (x : V3) (V : Set V3) (E : Set (Set V3))
+    (hfan : Fan.FAN x V E) {d : Dart3} (hd : d ∉ Fan.dart1OfFan V E) :
+    (Fan.hypermapOfFan x V E hfan).edgeMap d = d := by
+  unfold Fan.hypermapOfFan Fan.extendPerm
+  simp only [Equiv.ofBijective_apply]
+  unfold Fan.res
+  rw [if_neg (by simpa [(Fan.finite_dart1_fan hfan).coe_toFinset] using hd)]
 
-/-- HOL `POLYHEDRON_TGJISOK` (counting_spheres.hl:4955). The stub dart set is
-empty, so the (truncated) `ℕ` inequality holds trivially. -/
+/-- `edge_fan` 是换位对合，故 hypermap 是 plain。 -/
+private theorem p22_plain_edgeMap (x : V3) (V : Set V3) (E : Set (Set V3))
+    (hfan : Fan.FAN x V E) :
+    (Fan.hypermapOfFan x V E hfan).edgeMap * (Fan.hypermapOfFan x V E hfan).edgeMap = 1 := by
+  refine Equiv.Perm.ext fun d => ?_
+  by_cases hd : d ∈ Fan.dart1OfFan V E
+  · have h1 := p22_edgeMap_eq x V E hfan hd
+    have h2 := p22_edgeMap_eq x V E hfan (Fan.eFanPair_mem_dart1 hd)
+    simp only [Equiv.Perm.mul_apply, h1, h2, Fan.eFanPair_sq d hd, Equiv.Perm.one_apply]
+  · simp only [Equiv.Perm.mul_apply, p22_edgeMap_fix x V E hfan hd, Equiv.Perm.one_apply]
+
+/-- `e_fan` 无不动点（HOL `e_fan_no_fix_point` 的打包形态）。 -/
+private theorem p22_edgeMap_ne (x : V3) (V : Set V3) (E : Set (Set V3))
+    (hfan : Fan.FAN x V E) :
+    ∀ d ∈ (Fan.hypermapOfFan x V E hfan).darts,
+      (Fan.hypermapOfFan x V E hfan).edgeMap d ≠ d := by
+  intro d hd
+  have hd1 : d ∈ Fan.dart1OfFan V E := by
+    rw [← (Fan.finite_dart1_fan hfan).coe_toFinset]
+    exact hd
+  rw [p22_edgeMap_eq x V E hfan hd1]
+  exact Fan.e_fan_no_fix hfan d hd1
+
+/-- HOL `POLYHEDRON_PLAIN` (counting_spheres.hl:4866): the `hypermapOfFan`
+edge map is `e_fan (v,w) = (w,v)`, an involution. -/
+theorem POLYHEDRON_PLAIN (p : Set V3) (hb : Bornology.IsBounded p) (hp : polyhedron p)
+    (hi : (0 : V3) ∈ interior p) :
+    (hypermapOfPolyhedronP22 p hb hp hi).Plain :=
+  p22_plain_edgeMap 0 (verticesP22 p) (edgesP22 p) (fanOfPolyhedronP22 p hb hp hi)
+
+/-- HOL `POLYHEDRON_NODE_3` (counting_spheres.hl:4905): the node of a dart
+has ≥ 3 darts (`SUM_AZIM_FAN_OF_NODE_EQ_2PI_I_FAN` gives sum `2π`, `BSXAQBQ`
+bounds every azimuth strictly below `π`). -/
+theorem POLYHEDRON_NODE_3 (p : Set V3) (x : Dart3) (hb : Bornology.IsBounded p)
+    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p)
+    (hx : x ∈ dFanP22 0 (verticesP22 p) (edgesP22 p) (fanOfPolyhedronP22 p hb hp hi)) :
+    3 ≤ ((hypermapOfPolyhedronP22 p hb hp hi).node x).ncard := by
+  let hfan : Fan.FAN 0 (verticesP22 p) (edgesP22 p) := fanOfPolyhedronP22 p hb hp hi
+  let H : Hypermap Dart3 := hypermapOfPolyhedronP22 p hb hp hi
+  have hdarts : (↑H.darts : Set Dart3) = Fan.dart1OfFan (verticesP22 p) (edgesP22 p) :=
+    dFanP22_eq_dart1 0 (verticesP22 p) (edgesP22 p) hfan
+  have hxD : x ∈ H.darts := hx
+  have hcard : ∀ v ∈ verticesP22 p,
+      1 < (Fan.setOfEdge v (verticesP22 p) (edgesP22 p)).ncard := by
+    intro v hv
+    have h := CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON hb hp hi v hv
+    rwa [← edgesP22_eq_edgesP7 p] at h
+  have hnode : H.node x ∈ H.nodeSet := ⟨x, hxD, rfl⟩
+  have hsum : (∑ᶠ y ∈ H.node x,
+      azimFan 0 (verticesP22 p) (edgesP22 p) y.1 y.2) = 2 * Real.pi :=
+    SUM_AZIM_FAN_OF_NODE_EQ_2PI_I_FAN hfan hnode hcard
+  have hazim : ∀ y ∈ H.node x,
+      azimFan 0 (verticesP22 p) (edgesP22 p) y.1 y.2 < Real.pi := by
+    intro y hy
+    have hyD : y ∈ (↑H.darts : Set Dart3) := Hypermap.node_subset_darts H hxD hy
+    have hy1 : y ∈ Fan.dart1OfFan (verticesP22 p) (edgesP22 p) := by rwa [hdarts] at hyD
+    have hy2 : y ∈ Fan.dartOfFan (verticesP22 p) (edgesP22 p) := Set.subset_union_right hy1
+    have hy3 : y ∈ Fan.dartOfFan (Set.extremePoints ℝ p) (edges_p7 p) := by
+      rw [edgesP22_eq_edgesP7 p] at hy2
+      exact hy2
+    have hres := BSXAQBQ hb hp hi hy3
+    rwa [edgesP22_eq_edgesP7 p]
+  have hfin : (H.node x).Finite := Hypermap.node_finite H x
+  have hsum_lt : (∑ᶠ y ∈ H.node x,
+        azimFan 0 (verticesP22 p) (edgesP22 p) y.1 y.2) <
+      (∑ᶠ y ∈ H.node x, Real.pi) := by
+    have hle : ∀ y ∈ hfin.toFinset,
+        azimFan 0 (verticesP22 p) (edgesP22 p) y.1 y.2 ≤ Real.pi :=
+      fun y hy => le_of_lt (hazim y ((Set.Finite.mem_toFinset hfin).mp hy))
+    have hlt : ∃ y ∈ hfin.toFinset,
+        azimFan 0 (verticesP22 p) (edgesP22 p) y.1 y.2 < Real.pi :=
+      ⟨x, (Set.Finite.mem_toFinset hfin).mpr (Hypermap.mem_node_self H x),
+        hazim x (Hypermap.mem_node_self H x)⟩
+    rw [finsum_mem_eq_finite_toFinset_sum
+      (fun y => azimFan 0 (verticesP22 p) (edgesP22 p) y.1 y.2) hfin,
+      finsum_mem_eq_finite_toFinset_sum (fun _ => Real.pi) hfin]
+    exact Finset.sum_lt_sum hle hlt
+  have hconst : (∑ᶠ _ ∈ H.node x, Real.pi) = ((H.node x).ncard : ℝ) * Real.pi := by
+    rw [finsum_mem_eq_finite_toFinset_sum (fun _ : Dart3 => Real.pi) hfin,
+      Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card (H.node x) hfin]
+  have h2 : (2 : ℝ) < ((H.node x).ncard : ℝ) := by
+    have h : 2 * Real.pi < ((H.node x).ncard : ℝ) * Real.pi := by
+      rw [← hsum, ← hconst]
+      exact hsum_lt
+    nlinarith [Real.pi_pos]
+  have h2' : 2 < (H.node x).ncard := by exact_mod_cast h2
+  show 3 ≤ (H.node x).ncard
+  omega
+
+/-- HOL `POLYHEDRON_TGJISOK` (counting_spheres.hl:4955): `darts_card_le`
+(`lemmaTGJISOK`, Hypermap.lean:1637) fed by `Connected` (`WGVWSKE`), `Plain`
+(`POLYHEDRON_PLAIN`), `Planar` (`GGRLKHP`) and node-3/edge-no-fix
+nondegeneracy. -/
 theorem POLYHEDRON_TGJISOK (p : Set V3) (hb : Bornology.IsBounded p)
     (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) :
-    (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).darts.card ≤
-      6 * (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).numberOfFaces - 12 := by
-  simp only [hypermap1OfFanxP22]
-  exact Nat.zero_le _
+    (hypermapOfPolyhedronP22 p hb hp hi).darts.card ≤
+      6 * (hypermapOfPolyhedronP22 p hb hp hi).numberOfFaces - 12 := by
+  let H : Hypermap Dart3 := hypermapOfPolyhedronP22 p hb hp hi
+  have hfan : Fan.FAN 0 (verticesP22 p) (edgesP22 p) := fanOfPolyhedronP22 p hb hp hi
+  have hconf : conformingFan 0 (verticesP22 p) (edgesP22 p) hfan :=
+    conformingFanOfPolyhedronP22 p hb hp hi
+  have hconn : H.Connected := WGVWSKE 0 (verticesP22 p) (edgesP22 p) hfan hconf
+  have hplain : H.Plain := POLYHEDRON_PLAIN p hb hp hi
+  have hplanar : H.Planar := GGRLKHP 0 (verticesP22 p) (edgesP22 p) hfan hconf
+  have hnondeg : ∀ x ∈ H.darts, H.edgeMap x ≠ x ∧ 3 ≤ (H.node x).ncard := by
+    intro x hx
+    have hx' : x ∈ dFanP22 0 (verticesP22 p) (edgesP22 p) hfan := hx
+    exact ⟨p22_edgeMap_ne 0 (verticesP22 p) (edgesP22 p) hfan x hx,
+      POLYHEDRON_NODE_3 p x hb hp hi hx'⟩
+  exact Hypermap.darts_card_le H hconn hplain hplanar hnondeg
 
-/-- HOL `EDGE_PAIR_pr23` (counting_spheres.hl:5003). GIANT. -/
+/-- HOL `EDGE_PAIR_pr23` (counting_spheres.hl:5003): `e_fan (v,w) = (w,v)`
+immediately gives the crossed projections. -/
 theorem EDGE_PAIR_pr23 (x : V3) (V : Set V3) (E : Set (Set V3)) (d d' : Dart3)
     (h : eFanP22 x V E d = d') : pr2 d = pr3 d' ∧ pr3 d = pr2 d' := by
-  sorry
+  have h' : d' = (d.2, d.1) := by simpa [eFanP22, Fan.eFanPair] using h.symm
+  subst h'
+  simp [pr2, pr3]
 
-/-- HOL `EDGE_pr23` (counting_spheres.hl:5020). Vacuous: the stub `d1FanP22`
-is empty. -/
+/-- HOL `EDGE_pr23` (counting_spheres.hl:5020): two distinct darts on the
+same underlying edge are the two orientations of it. -/
 theorem EDGE_pr23 (x : V3) (V : Set V3) (E : Set (Set V3)) (y y1 : Dart3)
     (hfan : Fan.FAN x V E)
     (hcard : ∀ v ∈ V, (setOfEdgeP22 v V E).ncard > 1)
     (hy : y ∈ d1FanP22 x V E) (hy1 : y1 ∈ d1FanP22 x V E)
     (hpr : ({pr2 y, pr3 y} : Set V3) = {pr2 y1, pr3 y1}) (hne : y ≠ y1) :
-    (hypermap1OfFanxP22 x V E).edgeMap y1 = y := by
-  simp [d1FanP22] at hy
+    (hypermap1OfFanxP22 x V E hfan).edgeMap y1 = y := by
+  have hy1' : y1 ∈ Fan.dart1OfFan V E := hy1
+  have hedge : (hypermap1OfFanxP22 x V E hfan).edgeMap y1 = Fan.eFanPair V E y1 :=
+    p22_edgeMap_eq x V E hfan hy1'
+  rw [hedge]
+  have hy1ne : y1.1 ≠ y1.2 :=
+    p22_pair_ne hfan hy1'
+  have hpr' : ({y.1, y.2} : Set V3) = {y1.1, y1.2} := hpr
+  have h1 : y.1 ∈ ({y1.1, y1.2} : Set V3) := by
+    rw [← hpr']; exact Set.mem_insert _ _
+  have h2 : y.2 ∈ ({y1.1, y1.2} : Set V3) := by
+    rw [← hpr']; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
+  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
+  rcases h1 with h1 | h1
+  all_goals rcases h2 with h2 | h2
+  · exfalso
+    have hpair : ({y.1, y.2} : Set V3) = {y1.1} := by ext z; simp [h1, h2]
+    have hy12mem : y1.2 ∈ ({y.1, y.2} : Set V3) := by
+      rw [hpr']; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
+    rw [hpair, Set.mem_singleton_iff] at hy12mem
+    exact hy1ne hy12mem.symm
+  · exfalso; exact hne (Prod.ext h1 h2)
+  · have hy : y = (y1.2, y1.1) := Prod.ext h1 h2
+    rw [hy]
+    simp [Fan.eFanPair]
+  · exfalso
+    have hpair : ({y.1, y.2} : Set V3) = {y1.2} := by ext z; simp [h1, h2]
+    have hy11mem : y1.1 ∈ ({y.1, y.2} : Set V3) := by
+      rw [hpr']; exact Set.mem_insert _ _
+    rw [hpair, Set.mem_singleton_iff] at hy11mem
+    exact hy1ne hy11mem
 
 /-- HOL `SIMPLE_FACE_EDGE_INJ` (counting_spheres.hl:5066). GIANT. -/
 theorem SIMPLE_FACE_EDGE_INJ {α : Type*} [DecidableEq α] (H : Hypermap α) (y y1 : α)
@@ -12859,33 +13129,64 @@
   rw [hsingle, Set.ncard_singleton] at hnode
   norm_num at hnode
 
-/-- Under the `hypermap1OfFanxP22` stub (empty dart set) the face set is
-empty. -/
-private theorem p22_faceSet_stub (x : V3) (V : Set V3) (E : Set (Set V3)) :
-    (hypermap1OfFanxP22 x V E).faceSet = (∅ : Set (Set Dart3)) := by
-  simp [hypermap1OfFanxP22, Hypermap.faceSet, setOfOrbits]
-
-/-- HOL `INJ_EDGES_FACE_pr23` (counting_spheres.hl:5119).  Vacuous: the stub
-`faceSet` is empty, so the face-membership hypothesis is contradictory. -/
+/-- HOL `INJ_EDGES_FACE_pr23` (counting_spheres.hl:5119): inside one face of
+the fan the underlying edge determines the dart.  HOL proof: `SIMPLE_FACE_EDGE_INJ`
+(with `SRPRNPL`/`POLYHEDRON_NODE_3`) rules out the opposite orientation, and
+`EDGE_pr23` identifies the only remaining dart. -/
 theorem INJ_EDGES_FACE_pr23 (p : Set V3) (f : Set Dart3) (y1 y : Dart3)
     (hb : Bornology.IsBounded p) (hp : polyhedron p) (hi : (0 : V3) ∈ interior p)
-    (hf : f ∈ (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).faceSet)
+    (hf : f ∈ (hypermapOfPolyhedronP22 p hb hp hi).faceSet)
     (hy : y ∈ f) (hy1 : y1 ∈ f)
     (hpr : ({pr2 y, pr3 y} : Set V3) = {pr2 y1, pr3 y1}) : y = y1 := by
-  rw [p22_faceSet_stub] at hf
-  exact absurd hf (Set.notMem_empty f)
+  let hfan : Fan.FAN 0 (verticesP22 p) (edgesP22 p) := fanOfPolyhedronP22 p hb hp hi
+  let H : Hypermap Dart3 := hypermapOfPolyhedronP22 p hb hp hi
+  have hconf : conformingFan 0 (verticesP22 p) (edgesP22 p) hfan :=
+    conformingFanOfPolyhedronP22 p hb hp hi
+  have hdarts : (↑H.darts : Set Dart3) = Fan.dart1OfFan (verticesP22 p) (edgesP22 p) :=
+    dFanP22_eq_dart1 0 (verticesP22 p) (edgesP22 p) hfan
+  obtain ⟨z, hz, hzf⟩ := hf
+  have hzf' : H.face z = f := hzf
+  have hyz : y ∈ H.face z := hzf' ▸ hy
+  have hy1z : y1 ∈ H.face z := hzf' ▸ hy1
+  have hfy : y ∈ H.face y1 := by
+    rw [← Hypermap.face_eq_of_mem H hy1z]
+    exact hyz
+  have hyD : y ∈ H.darts := Hypermap.face_subset_darts H hz hyz
+  by_contra hne
+  have hnode : 1 < (H.node (H.faceMap y)).ncard := by
+    have hfaceD : H.faceMap y ∈ H.darts := H.faceMap_permutes.apply_mem hyD
+    have h3 : 3 ≤ (H.node (H.faceMap y)).ncard :=
+      POLYHEDRON_NODE_3 p (H.faceMap y) hb hp hi hfaceD
+    omega
+  have hnot : y ≠ H.edgeMap y1 :=
+    SIMPLE_FACE_EDGE_INJ H y y1 (SRPRNPL hfan hconf) hnode hyD hfy
+  have hy1D : y1 ∈ Fan.dart1OfFan (verticesP22 p) (edgesP22 p) := by
+    have h := Hypermap.face_subset_darts H hz hy1z
+    rwa [hdarts] at h
+  have hyD1 : y ∈ Fan.dart1OfFan (verticesP22 p) (edgesP22 p) := by
+    have hyD' : y ∈ (↑H.darts : Set Dart3) := hyD
+    rwa [hdarts] at hyD'
+  have hcard : ∀ v ∈ verticesP22 p, (setOfEdgeP22 v (verticesP22 p) (edgesP22 p)).ncard > 1 := by
+    intro v hv
+    rw [setOfEdgeP22_eq_fan hfan v]
+    have h := CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON hb hp hi v hv
+    rwa [← edgesP22_eq_edgesP7 p] at h
+  exact hnot (EDGE_pr23 0 (verticesP22 p) (edgesP22 p) y y1 hfan hcard hyD1 hy1D hpr hne).symm
 
-/-- HOL `BIJ_EDGES_DART_FACE` (counting_spheres.hl:5178).  Vacuous: the stub
-`faceSet` is empty, so the face-membership hypothesis is contradictory. -/
+/-- HOL `BIJ_EDGES_DART_FACE` (counting_spheres.hl:5178): `edges f1` is in
+bijection with the face orbit `f`.  HOL's proof rewrites
+`edges f1 = {{pr2 e, pr3 e} | e ∈ f}` via `Cfyxfty.CFYXFTY0/1` (NOT ported in
+this tree) and then uses `BIJ_SYM` + `INJ_EDGES_FACE_pr23`; the missing
+`CFYXFTY` half is the remaining gap — kept `sorry` (real statement after the
+DEF-FIX wiring, no statement change). -/
 theorem BIJ_EDGES_DART_FACE (p : Set V3) (f : Set Dart3) (f1 : Set V3)
     (hb : Bornology.IsBounded p) (hp : polyhedron p) (hi : (0 : V3) ∈ interior p)
-    (hf : f ∈ (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).faceSet)
+    (hf : f ∈ (hypermapOfPolyhedronP22 p hb hp hi).faceSet)
     (hf1 : FacetOf f1 p)
     (hlead : fchanged f1 =
       dartsetLeadsIntoFanP22 0 (verticesP22 p) (edgesP22 p) f) :
     ∃ b, Set.BijOn b (edges f1) f := by
-  rw [p22_faceSet_stub] at hf
-  exact absurd hf (Set.notMem_empty f)
+  sorry
 
 /-- HOL `SEGMENT_EDGE_ONTO` (counting_spheres.hl:5206). GIANT. -/
 theorem SEGMENT_EDGE_ONTO (p : Set V3) (e : Set V3) (hp : polyhedron p)
@@ -13293,19 +13594,29 @@
     · show convexHull ℝ ({v, w} : Set V3) = u
       rw [convexHull_pair, ← hvw]
 
-/-- HOL `HYPERFACE_EXISTS` (counting_spheres.hl:5286). GIANT. -/
+/-- HOL `HYPERFACE_EXISTS` (counting_spheres.hl:5286): the topological
+components biject with the faces (`WBLARHH_BIJ`), so each component `U` has a
+unique face. -/
 theorem HYPERFACE_EXISTS (P : Set V3) (U : Set V3) (hb : Bornology.IsBounded P)
     (hp : polyhedron P) (hi : (0 : V3) ∈ interior P)
     (hU : topologicalComponentYfanP22 0 (verticesP22 P) (edgesP22 P) U) :
-    ∃! f : Set Dart3, f ∈ (hypermap1OfFanxP22 0 (verticesP22 P) (edgesP22 P)).faceSet ∧
+    ∃! f : Set Dart3, f ∈ (hypermapOfPolyhedronP22 P hb hp hi).faceSet ∧
       dartsetLeadsIntoFanP22 0 (verticesP22 P) (edgesP22 P) f = U := by
-  sorry
+  obtain ⟨-, hinj, hsurj⟩ := WBLARHH_BIJ P hb hp hi
+  obtain ⟨f, hfA, hfU⟩ := hsurj hU
+  refine ⟨f, ⟨hfA, hfU⟩, ?_⟩
+  intro g hg
+  exact hinj hg.1 hfA (hg.2.trans hfU.symm)
 
-/-- HOL `BIJ_DART_POLYEDGE` (counting_spheres.hl:5301). GIANT. -/
+/-- HOL `BIJ_DART_POLYEDGE` (counting_spheres.hl:5301): the fan darts biject
+with the facet-edge pairs.  The statement is now the real HOL one (DEF-FIX);
+the HOL proof goes through `PREIMAGE_BIJ` + `BIJ_EDGES_DART_FACE`, whose
+`Cfyxfty.CFYXFTY0/1` ingredient is not ported in this tree — kept `sorry`
+(UNRESOLVED; no statement change). -/
 theorem BIJ_DART_POLYEDGE (P : Set V3) (hb : Bornology.IsBounded P)
     (hp : polyhedron P) (hi : (0 : V3) ∈ interior P) :
     ∃ b : Dart3 → Set V3 × Set V3, Set.BijOn b
-      ((hypermap1OfFanxP22 0 (verticesP22 P) (edgesP22 P)).darts : Set Dart3)
+      ((hypermapOfPolyhedronP22 P hb hp hi).darts : Set Dart3)
       {fe : Set V3 × Set V3 | FacetOf fe.2 fe.1 ∧ FacetOf fe.1 P} := by
   sorry
 
```

### 2.2 验收

- 7 个假桩各自接线（见上）且 `dFanP22` 的 `hfan` 见证沿用
  `ConformingDefs.lean:14-18` 的 proof-parameterization 约定；`Dart3` 换成
  contracted pair `V3 × V3`，`pr2/pr3 = .1/.2`（`conforming.hl:2249`）。
- 新桥 `edgesP22_eq_edgesP7`：`Polytope.edges p = edges_p7 p`（同一 HOL
  `edges`：`edgeOf` 的 `affDim (segment ℝ v w) = 1` 对 `v ≠ w` 用
  `affDim_segment` 互译）；`fanOfPolyhedronP22` 由此把 `POLYHEDRON_FAN`
  的 `FAN 0 (extremePoints p) edges` 搬到 `FAN 0 (verticesP22 p) (edgesP22 p)`。
- 重证并转标准三（实测 `#print axioms` = `[propext, Classical.choice,
  Quot.sound]`）：`BIJ_FACET_HYPERFACE`（#4，`BIJ_TRANS` = `AMHFNXP_BIJ` ∘
  `BIJ_SYM WBLARHH_BIJ`）、`POLYHEDRON_CONFORMING_FAN`（#5，`PIIJBJK` +
  `POLYTOPE_FAN80` + `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`）、
  `EDGE_PAIR_pr23`（#6，`eFanPair` 换位）、`HYPERFACE_EXISTS`（#7，
  `WBLARHH_BIJ` 的 `∃!` 形式）。
- 顺带把 6 条「假真空」件改成真陈述并真证（原先靠 `∅`/`id`/`True` 空洞
  通过）：`POLYHEDRON_D1_D`、`POLYHEDRON_PLAIN`、`POLYHEDRON_NODE_3`
  （`SUM_AZIM_FAN_OF_NODE_EQ_2PI_I_FAN` + `BSXAQBQ`）、
  `POLYHEDRON_TGJISOK`（`Hypermap.darts_card_le`）、`EDGE_pr23`、
  `INJ_EDGES_FACE_pr23`；删除私有的 `p22_faceSet_stub`（改后为假）。
- `BIJ_EDGES_DART_FACE` / `BIJ_DART_POLYEDGE`（#8）陈述已转真，但证明缺
  `Cfyxfty.CFYXFTY0/1`（HOL 未移植）→ 保留 `sorry`，如实记账，**未改陈述**。
- 编排者实测：`lake env lean Kepler/Text/PackingAuto22.lean` **RC=0 / 0 error**，
  `declaration uses sorry` = 10（改前 13，`DF_SORRY_NET=-3`）。
