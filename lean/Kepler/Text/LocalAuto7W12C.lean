/-
LocalAuto7W12C: W12(b2a) — straight 支的 `FAN 0 V' E'`（HOL polar_fan.hl:2761-2900 的
`FAN_ECONOMIZED_SIMPLE` 六合取）。

`V' = p12b_V V v`、`E' = p12b_E V FF v`、`r = p12b_R FF v`（W12B 定义）。
本文件只做 FAN 六合取（unions / Graph / fan1 / fan2 / fan6 / fan7-economized）；
`localFan_p2`/convexity 留 b2b/b2c，`fanPerimeter` 拆分+IH 留 c。

依赖（全标准三）：
* W12B：`p12b_R_mem` / `p12b_R_ne` / `p12b_card` / `p12b_V_subset` / `p12b_rho_FF` /
  `p12b_straight_mem`；
* W12A：`p12a_smul_mem_affLt`；
* LA7：`UNION_AFF_GE_1_2`（61c2f9aa 真证）、`FAN_ECONOMIZED_SIMPLE`、
  `FAN_SUB_NOT_EQ_COLL_IN_CONV0`、`LOCAL_RHO_NODE_PAIR_E`、`PRE_IVS_RHO_NODE1_DETE`、
  `LOCAL_FAN_CHARACTER_OF_RHO_NODE2`、`IVS_RHO_NODE1_IN_V`、`LOFA_IN_V_SO_DO_RHO_NODE_V`。

件表：`p12c_E_mem` / `p12c_graph` / `p12c_unions` / `p12c_fan1` / `p12c_fan2` /
`p12c_fan6` / `p12c_fan7` / **`p12c_FAN`**。
-/
import Kepler.Text.LocalAuto7W12B

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## 基础引理 -/

/-- `v ≠ ρv`（非共线 `{0,v,ρv}` 的退化推论；W12B 私件 `p12b_v_ne_rho` 的本地副本）。 -/
private theorem p12c_v_ne_rho {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) : v ≠ rhoNode1 FF v := by
  intro he
  have hρv : rhoNode1 FF v = v := he.symm
  exact LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h hv (by
    show Collinear ℝ ({0, v, rhoNode1 FF v} : Set V3)
    have hset : ({0, v, rhoNode1 FF v} : Set V3) = ({0, v} : Set V3) := by
      rw [hρv]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ (0:V3) v)

/-- `w ∈ V'` 且 `ρw = v` ⟹ `w = ιv`（special edge 判别）。 -/
private theorem p12c_eq_ivs_of_rho_eq {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w : V3} (hw : w ∈ p12b_V V v) (hρ : rhoNode1 FF w = v) :
    w = ivsRhoNode1 FF v := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hdart : (w, rhoNode1 FF w) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS h2).1 w hw.1
  rw [hρ] at hdart
  exact (PRE_IVS_RHO_NODE1_DETE h2 hdart).symm

/-- `conv0_p2 {a,b}` 的系数提取（`a ≠ b`；全正系数）。 -/
private theorem p12c_conv0_pair_extract {a b x : V3} (hab : a ≠ b)
    (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧ r + s = 1 ∧ x = r • a + s • b := by
  simp only [conv0_p2, Set.mem_setOf_eq, Affsign] at hx
  obtain ⟨f, hfin, hvec, hsgn, hone⟩ := hx
  have htf : hfin.toFinset = ({a, b} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_empty_iff_false,
      false_or, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert,
      Finset.mem_singleton]
  refine ⟨f a, f b, hsgn a (by simp), hsgn b (by simp), ?_, ?_⟩
  · rw [htf, Finset.sum_insert (by simp [hab]), Finset.sum_singleton] at hone
    exact hone
  · rw [htf, Finset.sum_insert (by simp [hab]), Finset.sum_singleton] at hvec
    exact hvec

/-- `E'` 的边归属：`{w, r w} ∈ E` 或等于 special edge `{ιv, ρv}`（HOL 的
`E' ⊆ insert {ιv,ρv} E`）。 -/
theorem p12c_E_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    ∀ w ∈ p12b_V V v,
      ({w, p12b_R FF v w} : Set V3) ∈ E ∪
        ({{ivsRhoNode1 FF v, rhoNode1 FF v}} : Set (Set V3)) := by
  intro w hw
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  by_cases hρ : rhoNode1 FF w = v
  · have hwι : w = ivsRhoNode1 FF v := p12c_eq_ivs_of_rho_eq hcl hedge hw hρ
    have hr : p12b_R FF v w = rhoNode1 FF v := by
      unfold p12b_R
      rw [if_pos hρ]
    rw [hr, hwι]
    exact Set.mem_union_right _ (Set.mem_singleton _)
  · have hr : p12b_R FF v w = rhoNode1 FF w := by
      unfold p12b_R
      rw [if_neg hρ]
    rw [hr]
    exact Set.mem_union_left _ (LOCAL_RHO_NODE_PAIR_E h2 hw.1)

/-- `Graph E'`（`{w, r w}` 恰两点：`w ≠ r w`）。 -/
theorem p12c_graph {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) : Graph (p12b_E V FF v) := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := he
  have hne : w ≠ p12b_R FF v w := (p12b_R_ne hcl hedge hv hw).symm
  refine ⟨(Set.finite_singleton _).insert _, ?_⟩
  have htf : ((Set.finite_singleton (p12b_R FF v w)).insert w).toFinset
      = ({w, p12b_R FF v w} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
  rw [htf, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

/-- `⋃₀ E' ⊆ V'`。 -/
theorem p12c_unions {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) : (⋃₀ p12b_E V FF v) ⊆ p12b_V V v := by
  intro z hz
  obtain ⟨e, he, hze⟩ := Set.mem_sUnion.mp hz
  obtain ⟨w, hw, rfl⟩ := he
  rcases Set.mem_insert_iff.mp hze with h | h
  · rw [h]
    exact hw
  · rw [Set.mem_singleton_iff] at h
    rw [h]
    exact p12b_R_mem hcl hedge hv hw

/-- `fan1 0 V' E'`（有限 + 非空；非空用 `3 ≤ V.ncard`）。 -/
theorem p12c_fan1 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) {v : V3} (hv : v ∈ V) (hcard : 3 ≤ V.ncard) :
    fan1 (0:V3) (p12b_V V v) (p12b_E V FF v) := by
  obtain ⟨hfin, hcard'⟩ := p12b_card hcl hv
  refine ⟨hfin, ?_⟩
  have hpos : 0 < (p12b_V V v).ncard := by omega
  exact Set.nonempty_iff_ne_empty.mp ((Set.ncard_pos hfin).mp hpos)

/-- `fan2 0 V' E'`（原点不在 `V'`；由 `V' ⊆ V` 与 `fan2 0 V E`）。 -/
theorem p12c_fan2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (v : V3) : fan2 (0:V3) (p12b_V V v) (p12b_E V FF v) := by
  have h0V : (0:V3) ∉ V := (hcl.1.1).2.2.2.1
  exact fun h => h0V (p12b_V_subset V v h)

/-- `fan6 0 V' E'`：`{0, w, r w}` 非共线。普通边用 `LOCAL_FAN_CHARACTER_OF_RHO_NODE2`；
special edge `{ιv, ρv}` 用 `FAN_SUB_NOT_EQ_COLL_IN_CONV0` + `Generic` 反证
（HOL 2771-2819）。 -/
theorem p12c_fan6 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V) :
    fan6 (0:V3) (p12b_V V v) (p12b_E V FF v) := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := he
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hwV : w ∈ V := hw.1
  have hιV : ivsRhoNode1 FF v ∈ V := IVS_RHO_NODE1_IN_V hcl.1 hedge v hv
  have hρvV : rhoNode1 FF v ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 hv
  have h0V : (0:V3) ∉ V := (hcl.1.1).2.2.2.1
  by_cases hρ : rhoNode1 FF w = v
  · -- special edge：`w = ιv`，边 = `{ιv, ρv}`
    have hwι : w = ivsRhoNode1 FF v := p12c_eq_ivs_of_rho_eq hcl hedge hw hρ
    have hr : p12b_R FF v w = rhoNode1 FF v := by
      unfold p12b_R
      rw [if_pos hρ]
    rw [hr, hwι]
    intro hcol
    have hne : ivsRhoNode1 FF v ≠ rhoNode1 FF v := by
      intro heq
      have hv0 : rhoNode1 FF (ivsRhoNode1 FF v) = v := LOCAL_FAN_RHO_NODE_IVS h2 hv
      rw [heq] at hv0
      exact LOCAL_FAN_IMP_NOT_SEMI_IDE h2 hv hv0
    have hsub : ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) ⊆ V := by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with h | h
      · rw [h]; exact hιV
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact hρvV
    have hconv := FAN_SUB_NOT_EQ_COLL_IN_CONV0 hcl.1.1 hsub hne hcol
    obtain ⟨a, b, ha, hb, hsum, hrep⟩ := p12c_conv0_pair_extract hne hconv
    -- `y := −a • ιv = b • ρv`
    have hy : (-(a)) • ivsRhoNode1 FF v = b • rhoNode1 FF v := by
      have h1 : a • ivsRhoNode1 FF v = -(b • rhoNode1 FF v) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hrep.symm
      calc (-(a)) • ivsRhoNode1 FF v = -(a • ivsRhoNode1 FF v) := by rw [neg_smul]
        _ = -(-(b • rhoNode1 FF v)) := by rw [h1]
        _ = b • rhoNode1 FF v := by rw [neg_neg]
    -- `y ∈ affGe {0}{v, ρv}`
    have hmem1 : (-(a)) • ivsRhoNode1 FF v ∈
        affGe ({0} : Set V3) ({v, rhoNode1 FF v} : Set V3) := by
      rw [hy]
      have hdisj : Disjoint ({0} : Set V3) ({v, rhoNode1 FF v} : Set V3) := by
        refine Set.disjoint_left.mpr ?_
        intro z hz1 hz2
        rw [Set.mem_singleton_iff] at hz1
        rw [hz1] at hz2
        exact h0V (by
          rcases Set.mem_insert_iff.mp hz2 with h | h
          · rw [h]; exact hv
          · rw [Set.mem_singleton_iff] at h; rw [h]; exact hρvV)
      have hvne : v ≠ rhoNode1 FF v := by
        intro heq
        have hρv : rhoNode1 FF v = v := heq.symm
        exact LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hv (by
          show Collinear ℝ ({0, v, rhoNode1 FF v} : Set V3)
          have hset : ({0, v, rhoNode1 FF v} : Set V3) = ({0, v} : Set V3) := by
            rw [hρv]
            ext z
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            tauto
          rw [hset]
          exact collinear_pair ℝ (0:V3) v)
      refine (mem_affGe_singleton_pair (x := (0:V3)) (v := v)
        (w := rhoNode1 FF v) hdisj hvne).mpr ⟨1 - b, 0, b, by linarith [hsum, ha],
          hb.le, by ring, ?_⟩
      simp
    -- `y ∈ affLt {0}{ιv}`
    have hι0 : ivsRhoNode1 FF v ≠ 0 := fun h0 => h0V (h0 ▸ hιV)
    have hmem2 : (-(a)) • ivsRhoNode1 FF v ∈
        affLt ({0} : Set V3) ({ivsRhoNode1 FF v} : Set V3) :=
      p12a_smul_mem_affLt hι0 (by linarith)
    have hbot : (-(a)) • ivsRhoNode1 FF v ∈
        affGe ({0} : Set V3) ({v, rhoNode1 FF v} : Set V3) ∩
          affLt ({0} : Set V3) ({ivsRhoNode1 FF v} : Set V3) := ⟨hmem1, hmem2⟩
    rw [hg v (rhoNode1 FF v) (ivsRhoNode1 FF v)
      (LOCAL_RHO_NODE_PAIR_E h2 hv) hιV] at hbot
    exact hbot
  · -- 普通边
    have hr : p12b_R FF v w = rhoNode1 FF w := by
      unfold p12b_R
      rw [if_neg hρ]
    rw [hr]
    exact LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hwV

/-- `fan7 0 V' E'`（economized 形）：`E'` 的 special edge `{ιv,ρv}` 经
`UNION_AFF_GE_1_2` 拆成 `{ιv,v}` 与 `{v,ρv}` 两条原边，其余用原 fan7
（HOL 2820-2895）。 -/
theorem p12c_fan7 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) :
    ∀ e1 ∈ p12b_E V FF v ∪ (image (fun z : V3 => {z}) (p12b_V V v)),
      ∀ e2 ∈ p12b_E V FF v ∪ (image (fun z : V3 => {z}) (p12b_V V v)),
        e1 ∩ e2 = ∅ →
          affGe ({0} : Set V3) e1 ∩ affGe ({0} : Set V3) e2 = ({0} : Set V3) := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hιV : ivsRhoNode1 FF v ∈ V := IVS_RHO_NODE1_IN_V hcl.1 hedge v hv
  have hρvV : rhoNode1 FF v ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 hv
  have h0V : (0:V3) ∉ V := (hcl.1.1).2.2.2.1
  have hv0 : v ≠ 0 := fun h0 => h0V (h0 ▸ hv)
  have hι0 : ivsRhoNode1 FF v ≠ 0 := fun h0 => h0V (h0 ▸ hιV)
  have hρv0 : rhoNode1 FF v ≠ 0 := fun h0 => h0V (h0 ▸ hρvV)
  have hιv : rhoNode1 FF (ivsRhoNode1 FF v) = v := LOCAL_FAN_RHO_NODE_IVS h2 hv
  -- 原 fan7（economized）
  have hf7 : ∀ e1 ∈ E ∪ (image (fun z : V3 => {z}) V),
      ∀ e2 ∈ E ∪ (image (fun z : V3 => {z}) V), e1 ∩ e2 = ∅ →
        affGe ({0} : Set V3) e1 ∩ affGe ({0} : Set V3) e2 = ({0} : Set V3) := by
    have h := (FAN_ECONOMIZED_SIMPLE (0:V3) V E).mp hcl.1.1
    exact h.2.2.2.2.2
  -- 拆锥
  have hsplit : affGe ({0} : Set V3) ({ivsRhoNode1 FF v, v} : Set V3) ∪
      affGe ({0} : Set V3) ({v, rhoNode1 FF v} : Set V3)
      = affGe ({0} : Set V3) ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) :=
    UNION_AFF_GE_1_2 (a := (0:V3)) (u := ivsRhoNode1 FF v) (v := v)
      (w := rhoNode1 FF v) (p12b_straight_mem hcl hedge hg hv hpi) hι0 hv0 hρv0
  -- `{ιv,v} ∈ E`、`{v,ρv} ∈ E`
  have hA : ({ivsRhoNode1 FF v, v} : Set V3) ∈ E := by
    have h := LOCAL_RHO_NODE_PAIR_E h2 hιV
    have hset : ({ivsRhoNode1 FF v,
        rhoNode1_p2 FF (ivsRhoNode1 FF v)} : Set V3) = {ivsRhoNode1 FF v, v} := by
      rw [show rhoNode1_p2 FF (ivsRhoNode1 FF v) = v from hιv]
    rwa [hset] at h
  have hB : ({v, rhoNode1 FF v} : Set V3) ∈ E := LOCAL_RHO_NODE_PAIR_E h2 hv
  -- `E'` 元素归类
  have hclass : ∀ e ∈ p12b_E V FF v,
      e ∈ E ∨ e = ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := he
    rcases p12c_E_mem hcl hedge hv w hw with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mp h)
  have hnorm : ∀ e ∈ p12b_E V FF v ∪ (image (fun z : V3 => {z}) (p12b_V V v)),
      e ∈ E ∪ (image (fun z : V3 => {z}) V) ∨
        e = ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) := by
    intro e he
    rcases he with he | he
    · rcases hclass e he with h | h
      · exact Or.inl (Set.mem_union_left _ h)
      · exact Or.inr h
    · obtain ⟨z, hz, rfl⟩ := he
      exact Or.inl (Set.mem_union_right _ ⟨z, p12b_V_subset V v hz, rfl⟩)
  -- `v ∉ e2`（`e2 ∈ E' ∪ singletons(V')`）
  have hv_not : ∀ e2 ∈ p12b_E V FF v ∪ (image (fun z : V3 => {z}) (p12b_V V v)),
      v ∉ e2 := by
    intro e2 he2 hve
    rcases he2 with he2 | he2
    · obtain ⟨x, hx, rfl⟩ := he2
      rcases Set.mem_insert_iff.mp hve with h | h
      · exact hx.2 h.symm
      · rw [Set.mem_singleton_iff] at h
        by_cases hρ : rhoNode1 FF x = v
        · rw [show p12b_R FF v x = rhoNode1 FF v from by
            unfold p12b_R; rw [if_pos hρ]] at h
          exact p12c_v_ne_rho h2 hv h
        · rw [show p12b_R FF v x = rhoNode1 FF x from by
            unfold p12b_R; rw [if_neg hρ]] at h
          exact hρ h.symm
    · obtain ⟨z, hz, rfl⟩ := he2
      rw [Set.mem_singleton_iff] at hve
      exact hz.2 hve.symm
  -- special-left 情形
  have hspec_left : ∀ e2 ∈ p12b_E V FF v ∪ (image (fun z : V3 => {z}) (p12b_V V v)),
      ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) ∩ e2 = ∅ →
        affGe ({0} : Set V3) ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) ∩
          affGe ({0} : Set V3) e2 = ({0} : Set V3) := by
    intro e2 he2 hdisj2
    have hιe : ivsRhoNode1 FF v ∉ e2 := by
      intro hmem
      have h : ivsRhoNode1 FF v ∈
          ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) ∩ e2 :=
        ⟨Set.mem_insert _ _, hmem⟩
      rw [hdisj2] at h
      exact h
    have hρe : rhoNode1 FF v ∉ e2 := by
      intro hmem
      have h : rhoNode1 FF v ∈
          ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) ∩ e2 :=
        ⟨Set.mem_insert_of_mem _ (Set.mem_singleton _), hmem⟩
      rw [hdisj2] at h
      exact h
    have hve : v ∉ e2 := hv_not e2 he2
    have hdA : ({ivsRhoNode1 FF v, v} : Set V3) ∩ e2 = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨z, hz⟩
      obtain ⟨hz1, hz2⟩ := hz
      rcases Set.mem_insert_iff.mp hz1 with h | h
      · exact hιe (h ▸ hz2)
      · rw [Set.mem_singleton_iff] at h
        exact hve (h ▸ hz2)
    have hdB : ({v, rhoNode1 FF v} : Set V3) ∩ e2 = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨z, hz⟩
      obtain ⟨hz1, hz2⟩ := hz
      rcases Set.mem_insert_iff.mp hz1 with h | h
      · exact hve (h ▸ hz2)
      · rw [Set.mem_singleton_iff] at h
        exact hρe (h ▸ hz2)
    rcases hnorm e2 he2 with hE2 | hS2
    · rw [← hsplit, Set.union_inter_distrib_right,
        hf7 _ (Set.mem_union_left _ hA) e2 hE2 hdA,
        hf7 _ (Set.mem_union_left _ hB) e2 hE2 hdB]
      exact Set.union_self _
    · exfalso
      have hne : ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3).Nonempty :=
        ⟨ivsRhoNode1 FF v, Set.mem_insert _ _⟩
      rw [hS2, Set.inter_self] at hdisj2
      exact hne.ne_empty hdisj2
  intro e1 he1 e2 he2 hdisj
  rcases hnorm e1 he1 with hE1 | hS1
  · rcases hnorm e2 he2 with hE2 | hS2
    · exact hf7 e1 hE1 e2 hE2 hdisj
    · rw [hS2, Set.inter_comm]
      refine hspec_left e1 he1 ?_
      rw [← hS2]
      rwa [Set.inter_comm] at hdisj
  · rw [hS1] at hdisj ⊢
    exact hspec_left e2 he2 hdisj

/-- **`FAN 0 V' E'`**（b2a 收口）：六合取经 `FAN_ECONOMIZED_SIMPLE` 组装。 -/
theorem p12c_FAN {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) (hcard : 3 ≤ V.ncard) :
    FAN (0:V3) (p12b_V V v) (p12b_E V FF v) := by
  rw [FAN_ECONOMIZED_SIMPLE]
  exact ⟨p12c_unions hcl hedge hv, p12c_graph hcl hedge hv,
    p12c_fan1 hcl hv hcard, p12c_fan2 hcl v,
    p12c_fan6 hcl hedge hg hv, p12c_fan7 hcl hedge hg hv hpi⟩

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12c_E_mem
#print axioms Kepler.Text.p12c_graph
#print axioms Kepler.Text.p12c_unions
#print axioms Kepler.Text.p12c_fan1
#print axioms Kepler.Text.p12c_fan2
#print axioms Kepler.Text.p12c_fan6
#print axioms Kepler.Text.p12c_fan7
#print axioms Kepler.Text.p12c_FAN

end Kepler.Text
