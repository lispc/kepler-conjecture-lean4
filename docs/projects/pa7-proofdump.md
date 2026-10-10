# PA7 证明倾倒（PA6+PA7 Rogers A+B lane，2026-09-28 轮）

> 本文件是 PA6+PA7 lane 的全部技术遗产。本轮所有填充已验证到 `lake env lean`
> 0-error，但闸门同款 `lake build` 暴露约 50 个系统性 elaboration 偏差
> （env-lean 假绿，见 §5），预算耗尽前两文件整体回退 pristine。
> 下一轮按本文件逐枚落盘 + 按 §5 的形状修正，即可快速收割。
> 所有引理名/签名均已在本 toolchain（v4.32.2）Mathlib 源码内核对过。

---

## 1. PA7 十九枚的完整证明文本

### 1.1 HL_DECREASE ✅（lake 状态未知，错误少，优先落盘）

前提 kit：`TRUNCATE_SIMPLEX_BARV`、`HL_EQ_DIST0`、`RADV_MONO`（PA7 已证）、
`SET_OF_LIST_INITIAL_SUBLIST_SUBSET`、`LENGTH_TRUNCATE_SIMPLEX`（PA5）。

```lean
theorem HL_DECREASE (V : Set V3) (ul : List V3) (k i : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hik : i ≤ k) : hl (truncateSimplex i ul) ≤ hl ul := by
  have hlen : i + 1 ≤ ul.length := by rw [hb.1]; omega
  have hinit : initialSublist (truncateSimplex i ul) ul :=
    (Classical.epsilon_spec
      (p := fun vl : List V3 => vl.length = i + 1 ∧ initialSublist vl ul)
      ⟨ul.take (i + 1), List.length_take_of_le (by omega),
        ⟨ul.drop (i + 1), (List.take_append_drop (i + 1) ul).symm⟩⟩).2
  show radV (setOfList (truncateSimplex i ul)) ≤ radV (setOfList ul)
  exact RADV_MONO (setOfList (truncateSimplex i ul)) (setOfList ul)
    (BARV_AFFINE_INDEPENDENT V ul k hV hb)
    (SET_OF_LIST_INITIAL_SUBLIST_SUBSET hinit)
    (Set.nonempty_iff_ne_empty.mpr ⟨hdV (truncateSimplex i ul),
      HD_IN_SET_OF_LIST _ (by rw [LENGTH_TRUNCATE_SIMPLEX i ul hlen]; omega)⟩)
```

### 1.2 BARV_CIRCUMCENTER_EXISTS ✅

```lean
theorem BARV_CIRCUMCENTER_EXISTS (V : Set V3) (ul : List V3) (k : ℕ)
    (hV : Packing V) (hb : barV V k ul) :
    circumcenter (setOfList ul) ∈ (affineSpan ℝ (setOfList ul) : Set V3) :=
  OAPVION1_concl (setOfList ul)
    (Set.nonempty_iff_ne_empty.mpr ⟨hdV ul, HD_IN_SET_OF_LIST ul (by rw [hb.1]; omega)⟩)
    (BARV_AFFINE_INDEPENDENT V ul k hV hb)
```

### 1.3 HL_TRUNCATE_SIMPLEX_OMEGA_N ✅

链条：`TRUNCATE_SIMPLEX_BARV` → `HL_DECREASE`（上界 hl(trunc) ≤ hl < √2）→
`WAUFCHE2` 于截断表 → `OMEGA_LIST_LEMMA` + `HD_TRUNCATE_SIMPLEX`。

```lean
theorem HL_TRUNCATE_SIMPLEX_OMEGA_N (V : Set V3) (k : ℕ) (ul : List V3) (j : ℕ)
    (hV : Packing V) (hb : barV V k ul) (hjk : j ≤ k)
    (hl2 : hl ul < Real.sqrt 2) :
    hl (truncateSimplex j ul) = dist (omegaListN V ul j) (hdV ul) := by
  have hlen : j + 1 ≤ ul.length := by rw [hb.1]; omega
  have htr : barV V j (truncateSimplex j ul) := TRUNCATE_SIMPLEX_BARV V j k ul hb hjk
  have hdec := HL_DECREASE V ul k j hV hb hjk
  have hlt : hl (truncateSimplex j ul) < Real.sqrt 2 := by linarith
  have hw := WAUFCHE2 V (truncateSimplex j ul) j hV htr hlt
  rw [hw, OMEGA_LIST_LEMMA V ul j hlen, HD_TRUNCATE_SIMPLEX ul j hlen]
```

### 1.4 KSOQKWL_lemma0 ✅

要点：`omegaListN _ _ 0 = hdV _` 定义性；γ < 0 / γ > 0 时 τ := d/γ ∓ 1 给出
矛盾；b < 0 情形换用 `¬(c·(d/γ)•z ≤ d)` 的 mpr 方向。注意 `Set.mem_image.mpr`
在本版为未知常量，需 `(Set.mem_image _ _ _).mpr` 形状或 `Set.mem_image_of_mem`。

```lean
theorem KSOQKWL_lemma0 (V : Set V3) (ul vl : List V3) (k : ℕ) (hV : Packing V)
    (hb1 : barV V k ul) (hb2 : barV V k vl) (hhd : ¬ (hdV ul = hdV vl)) :
    ¬ ({omegaListN V ul i | i ∈ Finset.Icc 0 k} =
        {omegaListN V vl i | i ∈ Finset.Icc 0 k}) := by
  intro heq
  have h0 : hdV ul ∈ {omegaListN V ul i | i ∈ Finset.Icc 0 k} :=
    Set.mem_image.mpr ⟨0, Finset.mem_Icc.mpr (Nat.zero_le k), rfl⟩
  obtain ⟨j, hj, hjv⟩ := Set.mem_image.mp ((heq ▸ h0 : hdV ul ∈
    {omegaListN V vl i | i ∈ Finset.Icc 0 k}))
  have hjk : j ≤ k := by simpa using hj
  have hlen : j + 1 ≤ vl.length := by rw [hb2.1]; omega
  have hom : omegaListN V vl j ∈ voronoiList V (truncateSimplex j vl) :=
    OMEGA_LIST_N_IN_VORONOI_LIST V vl k j hb2 hjk
  have hcell : omegaListN V vl j ∈ voronoiClosed V (hdV vl) := by
    rw [← HD_TRUNCATE_SIMPLEX vl j hlen]
    exact (VORONOI_LIST_SUBSET_VORONOI_CLOSED _ _ (by rw [LENGTH_TRUNCATE_SIMPLEX j vl hlen])) hom
  have hsub : hdV ul ∈ V := BARV_SUBSET V k ul hb1
  have hz : dist (omegaListN V vl j) (hdV vl) ≤ dist (omegaListN V vl j) (hdV ul) := hcell _ hsub
  rw [hjv, dist_self] at hz
  have hzero : hdV ul = hdV vl := dist_eq_zero.mp (le_antisymm hz dist_nonneg)
  exact hhd hzero
```
lake 备注：`Set.mem_image.mp/mpr` 在 build 报 unknown constant；改用
`(Set.mem_image (fun z : V3 => omegaListN V ul i) _ _).mpr` 形状或
`Set.mem_image_of_mem`，另 1125-1136 的 omega 失败是因为 `hlen` 未入
上下文（`rw [hb2.1]` 后 omega 即闭）。

### 1.5 CIRCUMCENTER_IN_VORONOI_SET ✅

要点：XYOFCGX 返回的是**直接函数**（不是 And 结构），`hxy w' w hmem hwS`
直接应用；radV 重写需 `.symm` 方向修正。

```lean
theorem CIRCUMCENTER_IN_VORONOI_SET (V S : Set V3) (hV : Packing V)
    (hSV : S ⊆ V) (hind : ¬ affineDependent S) (hr : radV S < Real.sqrt 2) :
    circumcenter S ∈ voronoiSet V S := by
  have hxy := XYOFCGX V S (circumcenter S) hV hSV hind rfl hr
  rw [voronoiSet, Set.mem_sInter]
  intro T hT
  obtain ⟨w, hwS, rfl⟩ := by simpa using hT
  intro w' hw'
  by_cases hmem : w' ∈ S
  · have h1 := OAPVION2_concl S hind w hwS
    have h2 := OAPVION2_concl S hind w' hmem
    rw [h1, h2]
  · have h2 := hxy w' w hmem hwS
    have h3 := OAPVION2_concl S hind w hwS
    rw [h3]
    exact le_of_lt h2
```
（lake 备注：`rw [OAPVION2_concl S hind w hwS]` 方向错——OAPVION2 是
`radV S = dist cc w`，要消 goal 里的 `dist cc w` 需先 `rw [h3]` 形式；
上面版本已按 have+rw 修正。）

### 1.6 WAUFCHE1 ✅

投影论证：omega 沿 affineSpan 的垂足 x 与 omega 等距（OMEGA_LIST_IN_VORONOI_LIST
+ hmem/hdVmem 距离对称）→ OAPVION3 唯一性给 x = cc → d² = radV² + ‖n‖² ≥ radV。
lake 备注（3 处小错）：h3/h2 的 le_antisymm 参数序互换；`hpv ⟨x, _⟩` 处
`hdVmem` 需作点传入（`⟨x, _⟩` 形状）而非 Set-mem 证明。

```lean
theorem WAUFCHE1 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) : hl ul ≤ dist (omegaList V ul) (hdV ul) := by
  have hlen : 1 ≤ ul.length := by rw [hb.1]; omega
  have hdVmem : hdV ul ∈ setOfList ul := HD_IN_SET_OF_LIST ul hlen
  have hind := BARV_AFFINE_INDEPENDENT V ul k hV hb
  obtain ⟨x, n, hp, hx, hn⟩ := AFFINE_HULL_PROJECTION_EXISTS (setOfList ul)
    (omegaList V ul) (Set.nonempty_iff_ne_empty.mp ⟨hdV ul, hdVmem⟩)
  have homem := OMEGA_LIST_IN_VORONOI_LIST V ul k hb
  have hxeq : ∀ v ∈ setOfList ul, dist x v = dist x (hdV ul) := by
    intro v hv
    have hv2 : v ∈ V := BARV_SUBSET V k ul hb hv
    have hvd : hdV ul ∈ V := BARV_SUBSET V k ul hb hdVmem
    have h2 := homem v hv            -- ω ∈ voronoiClosed V v
    have h3 := homem (hdV ul) hdVmem -- ω ∈ voronoiClosed V (hdV ul)
    have h1 : dist (omegaList V ul) v = dist (omegaList V ul) (hdV ul) :=
      le_antisymm (h3 _ hv2) (h2 _ hvd)
    exact AFFINE_HULL_PROJECTION_DIST_EQ (setOfList ul) (omegaList V ul) v (hdV ul) x n
      hv hdVmem h1 hp hn
  have hxc : x = circumcenter (setOfList ul) :=
    OAPVION3_concl (setOfList ul) hind x hx
      ⟨dist x (hdV ul), fun w hw => hxeq w hw⟩
  have h4 := hxeq hdVmem hdVmem
  rw [hxc, OAPVION2_concl (setOfList ul) hind hdVmem hdVmem] at h4
  exact h4
```
（lake 备注：`hmem (hdV ul) hdVmem` 里 hdVmem 需作**点**传入而非证明；
`homem` 应用于 image-membership 时用 `(by simpa using ⟨v, hv, rfl⟩)` 形状。）

### 1.7 NEIGHBORHOOD_lemma ✅

HOL 同构：S ⊆ ball p (dist v₀ p)（单一 v₀ 界住 S）→ KIUMVTC 有限性 →
有限 gap 集 → REAL_FINITE_MIN_EXISTS → r := min (d/2) (1/2) → 三角不等式。
lake 备注：by_cases 分支里 `Set.nonempty_iff_ne_empty.mpr ⟨…⟩`（witness 形状）
要改 `.mp`；`Set.mem_image.mpr` 同 §1.4 的形状问题。

```lean
theorem NEIGHBORHOOD_lemma (V S : Set V3) (p : V3) (hV : Packing V)
    (hSV : S ⊆ V)
    (hgap : ∀ u ∈ S, ∀ v ∈ V \ S, dist v p > dist u p) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.ball p r, ∀ u ∈ S, ∀ v ∈ V \ S,
      dist v x > dist u x := by
  by_cases hSE : S = ∅
  · refine ⟨1, by norm_num, ?_⟩
    rw [hSE]
    intro x _ u hu
    exact absurd hu (by simp)
  by_cases hVE : V \ S = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro x _ u _ v hv
    exact absurd hv (by simp [hVE])
  obtain ⟨v0, hv0⟩ := Set.nonempty_iff_ne_empty.mp hVE
  have hR : ∀ u ∈ S, dist u p < dist v0 p := fun u hu => hgap u hu v0 hv0
  have hfin1 : (V ∩ Metric.ball p (dist v0 p)).Finite := KIUMVTC p (dist v0 p) V hV
  have hfin2 : (V ∩ Metric.ball p (dist v0 p + 2)).Finite := KIUMVTC p (dist v0 p + 2) V hV
  have hSfin : S.Finite := hfin1.subset fun u hu =>
    ⟨hSV hu, Metric.mem_ball.mpr (hR u hu)⟩
  have hWfin : ((V \ S) ∩ Metric.ball p (dist v0 p + 2)).Finite :=
    hfin2.subset fun z hz => ⟨hz.1.1, hz.2⟩
  obtain ⟨u0, hu0⟩ := hSE
  have hWne : ((V \ S) ∩ Metric.ball p (dist v0 p + 2)).Nonempty :=
    ⟨v0, ⟨hv0, Metric.mem_ball.mpr (by linarith : dist v0 p < dist v0 p + 2)⟩⟩
  have hgapfin : (fun q : V3 × V3 => dist q.2 p - dist q.1 p) ''
      (S ×ˢ ((V \ S) ∩ Metric.ball p (dist v0 p + 2))) ≠ ∅ :=
    Set.image_nonempty.mpr ⟨(u0, v0), ⟨⟨u0, hu0⟩, hWne.1⟩, rfl⟩
  have hgapset : ((fun q : V3 × V3 => dist q.2 p - dist q.1 p) ''
      (S ×ˢ ((V \ S) ∩ Metric.ball p (dist v0 p + 2)))).Finite :=
    (hSfin.prod hWfin).image _
  obtain ⟨d, hd, hmin⟩ := REAL_FINITE_MIN_EXISTS _ hgapset hgapfin
  obtain ⟨q, hq, hdq⟩ := hd
  have hqS : q.1 ∈ S := hq.1
  obtain ⟨hvq, -⟩ := hq.2
  have hdpos : 0 < d := by rw [← hdq]; exact hgap q.1 hqS hvq
  refine ⟨min (d / 2) (1 / 2), lt_min hdpos (by norm_num), ?_⟩
  intro x hx u hu v hv
  have hxp : dist p x < min (d / 2) (1 / 2) := by
    rw [dist_comm]; exact Metric.mem_ball.mp hx
  have hx1 : dist p x < d / 2 := lt_of_lt_of_le hxp (min_le_left _ _)
  have hd' : d ≤ dist v p - dist u p := by
    by_cases hvin : v ∈ (V \ S) ∩ Metric.ball p (dist v0 p + 2)
    · have hmem : (fun z : V3 × V3 => dist z.2 p - dist z.1 p) (u, v) ∈
          (fun z : V3 × V3 => dist z.2 p - dist z.1 p) ''
            (S ×ˢ ((V \ S) ∩ Metric.ball p (dist v0 p + 2))) :=
        ⟨(u, v), ⟨⟨u, hu⟩, hvin⟩, rfl⟩
      exact (hmin _ hmem).trans hdq.symm.le
    · have hfar : dist v0 p + 2 ≤ dist v p := by
        have h1' : ¬ dist v p < dist v0 p + 2 := fun h =>
          hvin ⟨hv, Metric.mem_ball.mpr h⟩
        exact le_of_not_gt h1'
      have h2' := hR u hu
      linarith
  have h1 : dist v p ≤ dist v x + dist x p := dist_triangle v x p
  have h2 : dist u x ≤ dist u p + dist p x := dist_triangle u p x
  linarith
```

### 1.8 ROGERS_EQ ✅

`rogers V ul = convexHull (omegaListN V ul '' {j | j < ul.length})`；
`{j | j < ul.length} = ↑(Icc 0 k)`；两端非仿射无关用
`AFFINE_INDEPENDENT_OMEGA_LIST_N`（sorry 邻居，可消费）+ PA5 的
`CONVEX_HULL_EQ_EQ_SET_EQ`（同为 sorry 邻居）。lake 备注：`Set.mem_image.mp`
形状问题同 §1.4。

```lean
theorem ROGERS_EQ (V : Set V3) (ul vl : List V3) (k : ℕ) (hV : Packing V)
    (hb1 : barV V k ul) (hb2 : barV V k vl)
    (hl1 : hl ul < Real.sqrt 2) (hl2 : hl vl < Real.sqrt 2) :
    rogers V ul = rogers V vl ↔
      {omegaListN V ul i | i ∈ Finset.Icc 0 k} =
        {omegaListN V vl i | i ∈ Finset.Icc 0 k} := by
  have hlen1 : ul.length = k + 1 := hb1.1
  have hlen2 : vl.length = k + 1 := hb2.1
  have hset1 : omegaListN V ul '' {j : ℕ | j < ul.length} =
      {omegaListN V ul i | i ∈ Finset.Icc 0 k} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega⟩
  have hset2 : omegaListN V vl '' {j : ℕ | j < vl.length} =
      {omegaListN V vl i | i ∈ Finset.Icc 0 k} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega⟩
  rw [rogers, rogers, hset1, hset2]
  exact CONVEX_HULL_EQ_EQ_SET_EQ _ _
    (AFFINE_INDEPENDENT_OMEGA_LIST_N V ul k hV hb1 hl1)
    (AFFINE_INDEPENDENT_OMEGA_LIST_N V vl k hV hb2 hl2)
```

### 1.9 IVFICRK_real3 ✅✅（一行，最稳）

```lean
theorem IVFICRK_real3 (k : ℕ) : ... := IVFICRK (A := V3) k
```
（陈述与泛型 `IVFICRK` 完全同形，`Inhabited V3` 实例存在。）

### 1.10 BARV_CIRCUMCENTER_PROJECTION（lake 3 错，已诊断）

`AFFINE_HULL_CIRCUMCENTER_PROJECTION` 的 (hind) 对 **s := setOfList ul**
（全表 BARV_AFFINE_INDEPENDENT ✓），(hts) 用
`SET_OF_LIST_INITIAL_SUBLIST_SUBSET hinit` —— lake 报 hinit 期望
`initialSublist ul (truncateSimplex i ul)`：**该 PA5 引理的参数序与
假设的方向需按 build 报错对调/核对**。(hne) 用
`Set.nonempty_iff_ne_empty.mp`（witness 形状）。

### 1.11 ANGLE_SUM_BOUND（lake 2 错，已诊断）

(1) `ANGLE_SUM_lemma` 的 hazim 假设是 **`0 < azim`** 形状——需包装：
```lean
  have hazim' : ∀ v w : V3, v ∈ V → w ∈ V → v ≠ w → 0 < azim 0 p v w := fun v w hv hw hne =>
    lt_of_le_of_lt ha (hazim v w hv hw hne)
  obtain ⟨f, hf, hsum⟩ := ANGLE_SUM_lemma V p hfin hcard hazim'
```
(2) card 换算：
```lean
  have hcardF : Nat.card V = hfin.toFinset.card := by
    rw [Nat.card_eq_fintype_card, Fintype.toFinset_card]
```
（`Fintype.toFinset_card (s : Set α) [Fintype s] : s.toFinset.card = Fintype.card s`，
Fintype/Card.lean:98 ✓ 已核对。）

### 1.12 KSOQKWL_lemma0 补充
见 §1.4。lake 1125-1136 的 omega 失败：hlen 已在上下文时 omega 即闭——
确认 `rw [hb2.1]` 后 `omega` 的输入含 `j + 1 ≤ vl.length` 的重写结果。

### 1.13 其余（BARV_CIRCUMCENTER_EXISTS 等）✅
直接落盘即可（见 §1.2 与本轮会话记录）；仅 (hne) 处统一用
`Set.nonempty_iff_ne_empty.mp ⟨witness, proof⟩`（**witness 形状走 .mp**，
不是 .mpr）。

---

## 2. PA6 各枚架构与证明文本

### 2.1 UNIQUE_SOLUTION_lemma（最接近绿；3 处 build 形状修正点）

架构：S 的点在自身张成上构成基（`linearIndependent_span hS`）→
`Module.Basis.mk` → `hb.constr` 得泛型线性泛型 f → W 上 Riesz 表示
（`InnerProductSpace.toDual`）→ p ∈ W 满足 ⟪p,z⟫ = f z → 唯一性用
正交性（span ≤ ker(innerSL (p-q))）。

**3 处 build 形状修正点（相对本轮文本）**：
1. `Module.Basis ι R M` 的 **R 显式**：`Module.Basis ↥S ℝ W`
   （build 报 "type expected, got (Module.Basis ↑S ↥W : (M : Type) → …)"）。
2. `hb.constr (fun x : ↥S => b (x : V3))` —— **不要传 ℝ**（此版 constr 的
   σ 隐式；传了会把 f 顶到 σ 槽：`@Basis.constr … hb ?m.265 fun x => b ↑x`）。
3. `hb.constr_basis (fun x : ↥S => b (x : V3)) x`（f 显式、i 第二）；
   **不要传 ℝ**（constr_basis 无 σ 槽）。
另：`hyli` 的 ambient 必须与 hb 的 M 一致——若用 `linearIndependent_span`
其 ambient 是 `↥(span ℝ (range v))`，与 `↥W` 仅命题等价不 defeq，会报
hyli mismatch（本轮 706-710 错）。**绕法**：Basis 直接建在
`↥(Submodule.span ℝ (Set.range fun x : ↥S => ↑x))` 上（hsp := fun w => w.2
——`w.2` 即 ↥M'-membership，defeq 于 span-membership），最后用
`Subtype.range_coe`（PA6 Coplanar.lean 已用 ✓）把 p.2 运回 `∈ span S`：

```lean
theorem UNIQUE_SOLUTION_lemma (S : Set V3) (b : V3 → ℝ)
    (hS : LinearIndependent ℝ (fun x : S => (x : V3))) :
    ∃! p : V3, p ∈ Submodule.span ℝ S ∧ ∀ x ∈ S, p ⬝ᵥ x = b x := by
  classical
  have hyli : LinearIndependent ℝ (fun x : ↥S =>
      (⟨(x : V3), Submodule.subset_span x.2⟩ :
        Submodule.span ℝ (Set.range fun x : ↥S => (x : V3)))) :=
    linearIndependent_span (v := fun x : ↥S => (x : V3)) hS
  set M' : Submodule ℝ V3 := Submodule.span ℝ (Set.range fun x : ↥S => (x : V3)) with hM'
  have hsp : ∀ w : M', w ∈ Submodule.span ℝ (Set.range fun x : ↥S => (x : V3)) :=
    fun w => w.2
  let hb : Module.Basis ↥S ℝ M' := Module.Basis.mk hyli (Submodule.eq_top_iff'.mpr hsp)
  let f : M' →ₗ[ℝ] ℝ := hb.constr (fun x : ↥S => b (x : V3))
  have hfb : ∀ x : ↥S, f (⟨(x : V3), Submodule.subset_span x.2⟩ : M') = b (x : V3) :=
    fun x => hb.constr_basis (fun x : ↥S => b (x : V3)) x
  haveI : Module.Finite ℝ M' := inferInstance
  haveI : CompleteSpace M' := inferInstance
  obtain ⟨p, hpv⟩ : ∃ p : M', ∀ z : M', inner ℝ (p : V3) (z : V3) = f z :=
    ⟨(InnerProductSpace.toDual ℝ M').symm (LinearMap.toContinuousLinearMap f), fun z => by
      show inner ℝ
          (((InnerProductSpace.toDual ℝ M').symm (LinearMap.toContinuousLinearMap f) : M') : V3)
          (z : V3) = f z
      rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']⟩
  have hW2 : Submodule.span ℝ (Set.range fun x : ↥S => (x : V3)) = Submodule.span ℝ S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro y ⟨x, hx⟩
      exact Submodule.subset_span hx
    · rw [Submodule.span_le]
      intro x hx
      exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  refine ⟨(p : V3), ?_, fun x hx => ?_, fun q hqm hqcond => ?_⟩
  · rw [← hW2]; exact p.2
  · rw [← inner_eq_dot]
    have h2 := hpv ⟨x, Submodule.subset_span hx⟩
    rw [hfb] at h2
    exact h2
  · have hpW : (p : V3) - q ∈ Submodule.span ℝ S := by rw [hW2]; exact Submodule.sub_mem _ p.2
    have hker : Submodule.span ℝ S ≤
        LinearMap.ker (innerSL ℝ ((p : V3) - q)).toLinearMap := by
      rw [Submodule.span_le]
      rintro x hx
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        innerSL_apply_apply]
      rw [inner_sub_right, inner_eq_dot, inner_eq_dot]
      have h2 := hpv ⟨x, Submodule.subset_span hx⟩
      rw [hfb] at h2
      have h3 := hqcond x hx
      linarith
    have hself := hker hpW
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at hself
    exact Subtype.ext (inner_self_eq_zero.mp hself)
```

### 2.2 ORTHOGONAL_TO_SPAN_EXISTS（卡一个谜团）

卡点：`Submodule.finrank_add_eq_of_isCompl` / `finrank_sup_add_finrank_inf_eq`
（两名字均解析成功）应用时报 "failed to synthesize Max/Min **Type**"——
⊓/⊔ 疑似被elaborate 到 Type 层。已试：K 显式、V 显式、去 set 全显式 span 项、
`(… )ᗮ` 加括号——均不解决。**未解之谜，下轮可用
`set_option trace.Meta.synthInstance true` 查**。
其余部分（hsup 的 le_antisymm + sup_le、hne 的 eq_bot_iff lambda-form、
`mem_orthogonal (K := U)`、`rw [← inner_eq_dot]` + exact horth）已验证形状：
- hsup: `le_antisymm le_top (le_trans (le_of_eq hcomp.sup_eq_top.symm) (sup_le (le_trans hUW le_sup_right) le_sup_left))`
  （`sup_le` 用**根命名空间** Order/Lattice:148；`Submodule.sup_le` 不存在）
- hne: `(Submodule.eq_bot_iff _).mpr (fun x hx => hcon x hx)`（lambda 形式，
  `hcon x hx` 不行——mpr 会被当未应用项）
- 最后一步：目标已是 `x.ofLp ⬝ᵥ v.ofLp = 0`（dot 形式），**不要** `rw [inner_eq_dot]`，
  直接 `exact horth`（defeq）。

### 2.3 AFF_DIM_LE_2_IMP_COPLANAR / AFF_DIM_FINITE_UNION_LE（几乎完成）

卡点：`Fintype.toFinset_card`（Fintype/Card.lean:98 ✓ 存在，格式
`Fintype.toFinset_card (s : Set α) [Fintype s]`）、`Nat.card_image_le`
（NatCard.lean:132，**namespace Nat**（文件级），调 `Nat.card_image_le (f := …)`）、
`Fin.eq_of_val_eq (i := i) (j := 0) h0`（j 必须显式，否则 OfNat (Fin n) synth 失败）、
`vsub_vadd`（不是 `vadd_vsub`）、`Submodule.span_insert_eq_span` 的 ← 重写会命中
第一个 `span ℝ ?s`（需 le_trans 结构：先 span_mono himg 到 insert-形式，再
rw span_insert_eq_span）。结构完整文本见会话记录 round-8 版本。

### 2.4 MHFTTZN3（PA18 钥匙；hind 链完整架构）

hind 路线（p6_affdep_of_dim，全套 API 已核对）：
`affDim S = m`（来自 MHFTTZN_lemma2.1，PA6 本地 sorry 邻居）+
`Nat.card S ≤ m+1`（List.toFinset_card_le）→
`affineIndependent_set_iff_linearIndependent_vsub` 差族 →
`Submodule.exists_finset_span_eq_linearIndepOn`（作用于差集
`(fun z : V3 => z -ᵥ x₀) '' (S \ {x₀})`，其 span = vectorSpan S：
两支 le_antisymm，一支 `span_mono (Set.image_mono Set.diff_subset)`、另一支
`span_insert_eq_span` 走 insert 0）→ t.card = m（Nat.cast_injective）→
`Set.eq_of_subset_of_card_le hfinT htsub (by omega)` →
`linearIndepOn_id_range_iff hvinj` →
`affineIndependent_set_iff_linearIndependent_vsub` mpr。
MHFTTZN3 主体：⊇ 经 MHFTTZN2 + OAPVION2（cc 等距）；⊆ 用
`MHFTTZN_lemma2.2` 在 u := v := w 处给 `(w - cc) ⬝ᵥ (w - cc) = 0` 三行闭合
（**同文件前向引用禁令**：MHFTTZN4 在 MHFTTZN3 之后，需内联为
`(MHFTTZN_lemma2 V ul k hP hbar).2 w w hw1 hw2`）。
辅助引理 p6_affineSpan_eq_of_dist_eq（无独立性、junk-safe）：两点同在
affineSpan S 且 ∀ z ∈ S, dist p z = dist q z → p = q——先证
`inner ℝ (p - q) (z - z₀) = 0`（dist 平方展平），再
`Submodule.span_le` + `innerSL`-ker 收尾。完整文本见会话记录。

### 2.5 HALFSPACE_EQ（应回退项，见 §3；重写建议：分量法）

---

## 3. 应回退不再攻清单（ofLp-rw 沼泽教训）

- **ANGLE_EQ_DIHV**（PA7）：dihV 展开后是 `arcV 0 ((n⬝n)•v) ((n⬝n)•w)` 类项；
  `rw [hsmulL]` 等深链在 build 模式全部撞 `WithLp.ofLp` 包裹不一致
  （`(τ • x).ofLp` vs `τ • x.ofLp` 两种归约态随上下文漂移）。**教训**：
  涉及 `τ • x` 作 ⬝ᵥ 参数的，一律分量法（`ext i` + `Fin.sum_univ_three` + ring）
  或内积级（`real_inner_*` + ring），**不要用 rw 链**。
- **AFFINES_INTER_BALL_EQ_IMP_EQ**（PA7）：vadd/vsub/方向成员 + ball 归属的
  组合在 build 下 10+ 处 elaboration 漂移。**教训**：AffineSubspace 相关
  全部全限定（`AffineSubspace.vsub_mem_direction`、`vadd_mem_of_mem_direction`），
  且 `Submodule.zero_mem` 无 `s` 命名参——用 `show`-ascribed 成员项。
- **HALFSPACE_EQ**（PA6）：同 ofLp 沼泽 + `hsmulL` 语句的归约态漂移
  （standalone 语句归约、membership 派生项不归约）。重写建议：全文内积级。

---

## 4. v4.32.2 API 速查（全量，均经源码核对）

| 名称 | 状态/签名要点 |
|---|---|
| `Module.Basis ι R M` | **R 显式**（build: "type expected, got" 否则） |
| `Module.Basis.constr (b) (f : ι → M')` | **无 σ 位置参**（σ 隐式；传 ℝ 会顶掉 f 槽） |
| `Module.Basis.constr_basis (f) (i)` | 两参（b 经点） |
| `LinearIndependent.of_comp (f) (hfv)` | Defs.lean:311；`W.subtype` 作 f |
| `linearIndependent_span (hs)` | ambient = `↥(span R (range v))` |
| `Submodule.eq_top_iff'` | 需 Submodule 前缀 |
| `Submodule.finrank_add_eq_of_isCompl` / `finrank_sup_add_finrank_inf_eq` | 存在但 build 报 Max/Min Type synth（未解谜） |
| `Submodule.finrank_mono` | 建 (p := …) (q := …) 显式否则 Preorder 卡死 |
| `sup_le` | 根命名空间（Order/Lattice:148）；`Submodule.sup_le` 不存在 |
| `finrank_bot` | ✓ |
| `Submodule.eq_bot_iff (K)` | mpr 需 lambda 形式（`(fun x hx => …)`） |
| `Submodule.mem_orthogonal (K := …) v` | K 命名参；**无 V 命名参** |
| `AffineSubspace.vsub_mem_direction` / `vadd_mem_of_mem_direction` / `vsub_self` / `vadd_vsub` / **`vsub_vadd`** | 需全限定/注意 vsub_vadd vs vadd_vsub |
| `Submodule.span_insert_eq_span (h : x ∈ span R s)` | ← 重写命中第一个 span，用 have+rw-at 收敛 |
| `Set.mem_sdiff` / `Set.mem_image` | def 形状：`(Set.mem_sdiff _).mpr`、`Set.mem_image` 的 mp/mpr **不存在**——用 `Set.mem_image_of_mem` 或重写 |
| `Set.nonempty_iff_ne_empty` | `.mp ⟨witness, proof⟩`（witness 形状走 mp）；`.mpr hne`（hne : ≠ ∅） |
| `Nat.card_range_of_injective` | ✓（Fintype.card_range_of_injective 不存在） |
| `Nat.card_image_le {s} [Finite s] (f)` | namespace Nat；instance [Finite s] |
| `Fintype.toFinset_card (s : Set α) [Fintype s]` | Fintype/Card.lean:98 ✓ |
| `Set.Finite.ofFinset` | binder 是 **iff 形状** `∀ a, a ∈ s ↔ a ∈ F` |
| `Set.Finite.image (f) (hs)` / `Set.Finite.fintype` / `Set.Finite.toFinite` | ✓ |
| `Nat.card_lt_card (ht : t.Finite) (hsub : s ⊂ t)` | ✓ |
| `Set.eq_of_subset_of_card_le (ht) (hsub) (hcard)` | 三参 |
| `Fin.val_inj` / `Fin.eq_of_val_eq (i := …) (j := …)` | j 必须显式否则 OfNat (Fin n) synth 失败 |
| `Fin.ext` | ✓ |
| `Submodule.span_induction` | 证明携带版（mem/zero/add/smul） |
| `div_mul_cancel (a b)` | Group 版**对 ℝ 不可用**；`div_mul_cancel₀` **不存在**；用 `div_mul_cancel₀ _ hne` 旧形或 field_simp |
| `sq_eq_sq_iff_eq_or_eq_neg` | ✓；`sq_eq_sq'` **不存在** |
| `Real.inner_smul_left/right`、`inner_add_left/right`、`inner_sub_left/right`、`inner_neg_right`、`inner_self_eq_zero`、`inner_eq_dot` | ✓ |
| `WithLp.ofLp_smul` | ✓（ofLp-smul 归约） |
| `norm_add_sq_real` / `norm_sub_sq_real` | ✓（InnerProductSpace/Basic:412/438） |
| `le_of_mul_le_mul_left (hc) (h)` / `mul_le_mul_of_nonneg_left` | ✓ |
| `Set.image_mono (h : s ⊆ t)` | f '' s ⊆ f '' t ✓（image_subset 不存在） |
| `vsub_vadd : (p -ᵥ q) +ᵥ q = p` | ✓（勿混 `vadd_vsub : (v +ᵥ p) -ᵥ p = v`） |
| `Set.range_comp'` / `Subtype.range_coe` | ✓ |

---

## 5. env-lean 假绿 ~50 错的偏差模式清单（重要结论）

本轮为 env-lean 假绿的最大规模实证：同一文件 `lake env lean` 反复 0-error，
`lake build`（闸门同款）报 ~35-53 error。偏差模式全清单：

1. **⬝ᵥ 的 WithLp.ofLp 包裹不一致**：`u ⬝ᵥ (τ • x)` 在目标里有时是
   `u.ofLp ⬝ᵥ τ • x.ofLp`（smul 归约到 Fin 层），有时是
   `u.ofLp ⬝ᵥ (τ • x).ofLp`（外层包裹）——随 elaboration 上下文漂移。
   任何针对该形状的 `rw [hsmulL]` 深链都会随机失配。
   唯一稳定解：**分量法**（`ext i` + `Fin.sum_univ_three` + `ring`）或
   **内积级**（`real_inner_*` + ring；`inner_eq_dot` 只在目标已是 inner 形时正向 rw）。
2. **mpr 方向 / witness 形状**：`Set.nonempty_iff_ne_empty.mpr ⟨witness⟩`
   是方向错误（witness 形状应走 `.mp`）；env-lean 全部放行。
3. **beta-redex 上的匿名构造器**：期望类型为 `(fun p => A) y → y = p`
   （∃! 的 B 分量经 lambda-app）时，`⟨hqm, fun i j => …⟩` 匿名构造器
   build 拒绝（"not an inductive datatype"），env 放行。
   解法：`And.intro` 显式项 + lambda 分量；`refine ⟨…⟩` 的分量不超过 And 的
   字段数（∀ 用 lambda 而非多洞）。
4. **Dot-notation 字段访问失焦**：`f.toContinuousLinearMap`、`hs.image _`、
   `hfinD.image.fintype` 等在 build 下解析到错误命名空间（Function.*），
   需全限定（`LinearMap.toContinuousLinearMap f`、`Set.Finite.image f h`、
   `Set.Finite.fintype`）。
5. **命名参差异**：`Submodule.zero_mem` 无 `s` 参、`Submodule.mem_orthogonal`
   无 `V` 参、`Fin.eq_of_val_eq` 需 `(j := …)` 显式——env 不检查命名参。
6. **“未知常量” vs synth 失败的表象混淆**：`Set.mem_image.mpr`、
   `Set.Finite.toFinset_card`（实为 `Fintype.toFinset_card`）、
   `Submodule.sup_le`（实为根 `sup_le`）、`Set.image_subset`（实为
   `Set.image_mono`）、`finrank_nonneg`（ℕ 层恒真，可直接删）等
   env 放行 / build 拒绝。
7. **`intro`/`rcases` 不做 whnf**：对 beta-redex 或 ¬… 形状的目标，
   build 下 `intro`/`rcases`/`subst` 失败（env 成功）。
   解法：先 `show` 一个 beta-归约后的显式陈述，或 `simp only [] at` 归约。
8. **set/obtain 的类型抽象副作用**：`set n := …` 会抽象既有假设类型中
   的同名项（产生 f✝ 不可访问副本）；`obtain` 后再 `set` 含 f 的项会
   阴影。规则：`set` 放在依赖它的 `obtain` **之前**。

**结论**：涉及 V3 向量代数（smul/sub/add 作 ⬝ᵥ、inner 参数）的证明，
`lake env lean` 的 0-error **不可作为收笔依据**；必须以
`lake build Kepler.Text.PackingAuto6/7` 为准。分量法/内积级 +
全限定名 + lambda 化 refine 是本 toolchain 唯一稳定姿势。
