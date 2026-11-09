/-
Kepler/Text/LocalFanStepBW4.lean — wave C-W4（B 支第一波，W4a）：u 侧 flat-run 与 telescope。

HOL 锚：`NKEZBFC.hl:2049-2270`（u 侧，B/跳跃支）。本件交 W4a 的两块：

* `pW4_flat_run`：EGHNAVX 第一个条件式合取（前件 `bta i = 0 ∧ i < k`）给出
  u 侧 flat-run 集合包含 `{vv n | 0<n≤i} ⊆ affGt {0,v}{vv 1}`，从而
  `u = vv i ∈ affGt {0,v}{ρv}`（HOL:2063-2079）。
* `pW4_telescope_u`：u 侧 telescope 恒等式
  `∀ j < i, affGe {0}{v, vv(j+1)} = ⋃₀ {affGe {0}{vv j1, vv(j1+1)} | j1 ≤ j}`
  （HOL:2143-2163），逐步步进用 `AFF_GE_EQ_AFF_GE_UNION_p9`。

逐步步进的几何前提 `hstep`（`vv n ∈ affGt {0}{v, vv(n+1)}`，即
HOL:2184-2242 的 flat 平面推理）作为**显式条件**接收；它的推导与
dart 级包含（HOL:2242-2270）留给 W4b。本件不依赖 W7。
-/
import Kepler.Text.LocalFanStepBW3c

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §0 本地私有 -/

private theorem pW4_0notinV (hcl : convexLocalFan_p2 V E FF) : (0 : V3) ∉ V :=
  (CVLF_LF_F hcl).2.2.2.2.1

private theorem pW4_disj0 (hcl : convexLocalFan_p2 V E FF) {a b : V3}
    (ha : a ∈ V) (hb : b ∈ V) : Disjoint ({0} : Set V3) {a, b} := by
  have h0V := pW4_0notinV hcl
  refine Set.disjoint_singleton_left.mpr ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨fun h => h0V (h ▸ ha), fun h => h0V (h ▸ hb)⟩

/-! ## §1 EGHNAVX flat-run：u 侧点包含（HOL:2063-2079） -/

/-- **u 侧 flat-run**：跳跃索引 `i`（`bta i = 0`）处 EGHNAVX 给
`{vv n | 0<n≤i} ⊆ affGt {0,v}{ρv}`；特别地 `u = vv i ∈ affGt {0,v}{ρv}`。 -/
theorem pW4_flat_run
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k)
    (hiter : ∀ i, (rhoNode1_p2 FF)^[i] v = vv i)
    (hbta : ∀ i, azim 0 v (vv 1) (vv i) = bta i)
    {i : ℕ} (hi : i < k) (hi0 : 0 < i) (hbi : bta i = 0) :
    vv i ∈ affGt ({0, v} : Set V3) {rhoNode1_p2 FF v} ∧
      ∀ n, 0 < n → n ≤ i → vv n ∈ affGt ({0, v} : Set V3) {rhoNode1_p2 FF v} := by
  have hl : localFan_p2 V E FF := hcl.1
  have hcol : ∀ w ∈ V, w ≠ v → ¬ Collinear ℝ ({0, v, w} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hl (fun _ _ => trivial) hg v hv
  have hegh := EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hv hk hcol hiter hbta
  obtain ⟨-, -, -, hD⟩ := hegh
  have hsub := ((hD i).1 ⟨hbi, hi⟩).2
  have hv1 : vv 1 = rhoNode1_p2 FF v := by
    rw [← hiter 1]
    simp
  have hmem : ∀ n, 0 < n → n ≤ i → vv n ∈ affGt ({0, v} : Set V3) {vv 1} := by
    intro n hn0 hni
    exact hsub ⟨n, hn0, hni, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← hv1]
    exact hmem i hi0 (le_refl i)
  · intro n hn0 hni
    rw [← hv1]
    exact hmem n hn0 hni

/-! ## §2 u 侧 telescope（HOL:2143-2163） -/

/-- **u 侧 telescope 恒等式**：逐步步进的几何前提 `hstep` 显式接收
（`vv n` 落在 `affGt {0}{v, vv(n+1)}`；HOL 由 flat 平面推理供给）。 -/
theorem pW4_telescope_u
    (hcl : convexLocalFan_p2 V E FF)
    {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {i : ℕ}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    (hstep : ∀ n, 0 < n → n + 1 ≤ i →
      vv n ∈ affGt ({0} : Set V3) {v, vv (n + 1)}) :
    ∀ j, j < i → ∀ z : V3,
      z ∈ affGe ({0} : Set V3) {v, vv (j + 1)}
        ↔ ∃ j1, j1 ≤ j ∧ z ∈ affGe ({0} : Set V3) {vv j1, vv (j1 + 1)} := by
  have hvv0 : vv 0 = v := by
    rw [← hiter 0]
    simp
  have hVV : ∀ n, vv n ∈ V := by
    intro n
    rw [← hiter n]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hcl.1 hv n
  intro j
  induction j with
  | zero =>
      intro _ z
      constructor
      · intro hz
        exact ⟨0, le_refl 0, by simpa [hvv0] using hz⟩
      · rintro ⟨j1, hj1, hz⟩
        have hje : j1 = 0 := by omega
        rw [hje] at hz
        simpa [hvv0] using hz
  | succ j ih =>
      intro hj z
      have hj' : j < i := by omega
      have hIH := ih hj'
      have hst : vv (j + 1) ∈ affGt ({0} : Set V3) {v, vv (j + 1 + 1)} :=
        hstep (j + 1) (by omega) (by omega)
      have hEq := AFF_GE_EQ_AFF_GE_UNION_p9 (x := (0 : V3)) (v := v)
        (u := vv (j + 1 + 1)) (v1 := vv (j + 1))
        (pW4_disj0 hcl hv (hVV (j + 1 + 1)))
        (pW4_disj0 hcl hv (hVV (j + 1)))
        (pW4_disj0 hcl (hVV (j + 1)) (hVV (j + 1 + 1)))
        hst
      rw [hEq, Set.mem_union]
      constructor
      · rintro (hz | hz)
        · obtain ⟨j1, hj1, hz'⟩ := (hIH z).mp hz
          exact ⟨j1, by omega, hz'⟩
        · exact ⟨j + 1, le_refl _, hz⟩
      · rintro ⟨j1, hj1, hz⟩
        rcases Nat.lt_or_ge j1 (j + 1) with hlt | hge
        · exact Or.inl ((hIH z).mpr ⟨j1, by omega, hz⟩)
        · right
          have hje : j1 = j + 1 := by omega
          rwa [hje] at hz

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW4_flat_run
#print axioms Kepler.Text.pW4_flat_run
#check @Kepler.Text.pW4_telescope_u
#print axioms Kepler.Text.pW4_telescope_u
