/-
Kepler/Text/LocalFanStepW40.lean — wave W40：G 接口移植 + W35 §2 补全（本战线最后一笔施工）。

## HOL 对表（NKEZBFC.hl:2049–2270 G 段；签名逐字，除注明外）
* §1 `pW40_G1_u_mem`：`u ∈ aff_gt {0,v}{ρv}`（:2063，2_1）——**消费面：u 侧锥，
  进将来 Assembly 的 u 侧并集分解输入**。
* §1 `pW40_G2_w_mem`：`w ∈ aff_gt {0,v}{ιv}`（:2081，2_1；经 `vv(k−1)=ιv`
  恒等 = `pW6k6_iter_ivs @ n:=V.ncard` + 周期回卷）——**消费面：w 侧锥，同上**。
  域注：非边沿 `i+1 < k−1`（边沿 `i+1 = k−1` 归 wrap 支，与 hslot_w 的
  `i+2 = k` 子支同处——本件不覆盖，如实记）。
* §1 `pW40_G3_azim_range`：`0 < azim 0 v ρv w ∧ azim 0 v ρv w < 2π`
  （:2120/:2123）——**消费面：correspondence 完备性**（azim 区间供将来方位
  论证；当前链不消费）。前提 `0 < bta(k−1)`/`bta(k−1) ≤ π` 显式列出，
  来源 = K 案事实（HOL :1909 与 EGHNAVX 第三合取）。
* §1 `pW40_G7_rho_g_mem`：`ρg ∈ aff_gt {0,v}{g}`（:2194/:2208/:2224，
  经 AZIM_EQ 两用 = `azim_eq_azim_iff` 链）——**消费面：w 侧 g 区锥，同上**。
* §2 `pW40_G6_union`：**u 侧前向 union 归纳**（:2143）——
  `aff_ge{0}{v, vv(j+1)} = ⋃_{j1≤j} aff_ge{0}{vv j1, vv(j1+1)}`（成员 iff 形；
  HOL 为集合等式，`Set.ext` 可还原）——**消费面：将来 Assembly 的 u 侧并集
  分解**。h4 = `pW5_flat_cone_order`/`pW5b_hstep` 形的 hstep（在库），零新几何。
* §3 `pW40_slot_of_family`：W35 §2 补全——`hfam`（w 侧 1_2 族接口）⇒ J 收尾
  `ρ(vv(i+1)) ∈ affGe{0}{v, vv(i+1)}`（下标引理具名化解决 whnf 超时；
  `pW35_union_of_family` 在 `j := k−i−2` 的实例 + 平凡对成员）。hfam 仍为边界。
-/
import Kepler.Text.LocalFanStepW35

set_option maxHeartbeats 4000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 G 接口四组 -/

/-- **G1（HOL :2063）**：`u = vv i ∈ aff_gt {0,v}{ρv}`（2_1；EGHNAVX 首 run）。
消费面：u 侧锥供给（将来 Assembly 的 u 侧并集分解输入）。 -/
theorem pW40_G1_u_mem (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k) (hiter : ∀ i, (rhoNode1_p2 FF)^[i] p = vv i)
    (hbta : ∀ i, azim 0 p (vv 1) (vv i) = bta i)
    {i : ℕ} (hi0 : 0 < i) (hik : i < k) (hbi : bta i = 0) :
    vv i ∈ affGt ({0, p} : Set V3) {rhoNode1_p2 FF p} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have hcol : ∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg p hp
  obtain ⟨-, -, -, hEG⟩ := EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hp hk hcol hiter hbta
  have hrun := (hEG i).1 ⟨hbi, hik⟩
  have hmem : vv i ∈ affGt ({0, p} : Set V3) {vv 1} :=
    hrun.2 ⟨i, hi0, le_rfl, rfl⟩
  have hρ : rhoNode1_p2 FF p = vv 1 := by
    have h := hiter 1
    simpa using h
  rwa [hρ]

/-- **G2（HOL :2081）**：`w = vv(i+1) ∈ aff_gt {0,v}{ιv}`（2_1；EGHNAVX 次 run
+ `vv(k−1) = ιv`）。消费面：w 侧锥供给。域注：`i+1 < k−1`（边沿归 wrap 支）。 -/
theorem pW40_G2_w_mem (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k) (hiter : ∀ i, (rhoNode1_p2 FF)^[i] p = vv i)
    (hbta : ∀ i, azim 0 p (vv 1) (vv i) = bta i)
    (hkpos : 0 < k)
    {i : ℕ} (hik2 : i + 1 < k - 1) (hbilast : bta (i + 1) = bta (k - 1)) :
    vv (i + 1) ∈ affGt ({0, p} : Set V3) {ivsRhoNode1_p2 FF p} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have hcol : ∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg p hp
  obtain ⟨-, -, -, hEG⟩ := EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hp hk hcol hiter hbta
  have hbr := (hEG (i + 1)).2 ⟨hbilast, by omega, hik2⟩
  have hmem : vv (i + 1) ∈ affGt ({0, p} : Set V3) {vv (k - 1)} :=
    hbr.2 ⟨i + 1, le_rfl, by omega, rfl⟩
  -- vv(k−1) = ιp（pW6k6_iter_ivs @ n := V.ncard + 周期回卷）
  have hvvk : vv (V.ncard) = p := (hiter V.ncard).symm.trans (LOFA_IMP_ITER_RHO_NODE_ID hlf hp)
  have hι : ivsRhoNode1_p2 FF p = vv (k - 1) := by
    have h := pW6k6_iter_ivs hlf hp hiter (show 0 < V.ncard from by omega)
    rw [hvvk, hk] at h
    exact h
  rwa [hι]

/-- **G3（HOL :2120/:2123）**：`0 < azim 0 v ρv w ∧ azim 0 v ρv w < 2π`。
消费面：correspondence 完备性（azim 区间）；前提 `0 < bta(k−1)`/`≤ π` 显式。 -/
theorem pW40_G3_azim_range
    {p : V3} {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hiter : ∀ i, (rhoNode1_p2 FF)^[i] p = vv i)
    (hbta : ∀ i, azim 0 p (vv 1) (vv i) = bta i)
    {i : ℕ} (hbilast : bta (i + 1) = bta (k - 1))
    (hbk : 0 < bta (k - 1)) (hbl : bta (k - 1) ≤ Real.pi) :
    0 < azim 0 p (rhoNode1_p2 FF p) (vv (i + 1)) ∧
      azim 0 p (rhoNode1_p2 FF p) (vv (i + 1)) < 2 * Real.pi := by
  have hρ : rhoNode1_p2 FF p = vv 1 := by
    have h := hiter 1
    simpa using h
  have he : azim 0 p (rhoNode1_p2 FF p) (vv (i + 1)) = bta (k - 1) := by
    rw [hρ, hbta, hbilast]
  constructor
  · rw [he]; exact hbk
  · rw [he]
    nlinarith [Real.pi_pos]

/-- **G7（HOL :2194/:2208/:2224）**：`ρg ∈ aff_gt {0,v}{g}`（2_1；
`azim_eq_azim_iff` 链）。消费面：w 侧 g 区锥供给。 -/
theorem pW40_G7_rho_g_mem (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k) (hiter : ∀ i, (rhoNode1_p2 FF)^[i] p = vv i)
    (hbta : ∀ i, azim 0 p (vv 1) (vv i) = bta i)
    {i g : ℕ} (hik2 : i + 1 < k - 1) (hbilast : bta (i + 1) = bta (k - 1))
    (hg1 : i + 1 ≤ g) (hgk : g + 1 < k) :
    vv (g + 1) ∈ affGt ({0, p} : Set V3) {vv g} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have hvvV : ∀ m : ℕ, vv m ∈ V := fun m => by
    rw [← hiter m]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp m
  have hcol : ∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg p hp
  obtain ⟨-, -, -, hEG⟩ := EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hp hk hcol hiter hbta
  have hbr := (hEG (i + 1)).2 ⟨hbilast, by omega, hik2⟩
  have hrun : ∀ m : ℕ, i + 1 ≤ m → m < k → vv m ∈ affGt ({0, p} : Set V3) {vv (k - 1)} :=
    fun m hm1 hm2 => hbr.2 ⟨m, hm1, hm2, rfl⟩
  have hgn := hrun g hg1 (by omega)
  have hgn1 := hrun (g + 1) (by omega) hgk
  have hnc_base : ¬ Collinear3 (0 : V3) p (rhoNode1_p2 FF p) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf hp
  have hρeq : rhoNode1_p2 FF p = vv 1 := by
    have h := hiter 1
    simpa using h
  have hne : ∀ m : ℕ, 0 < m → m < k → vv m ≠ p := by
    intro m hm0 hm
    have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 m hm0 (by omega)
    rw [hiter m, show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
    exact hd
  have hncm : ∀ m : ℕ, 0 < m → m < k → ¬ Collinear3 (0 : V3) p (vv m) := by
    intro m hm0 hm
    have h := PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg p hp
      (vv m) (hvvV m) (hne m hm0 hm)
    simpa only [Kepler.Geom.Collinear3] using h
  have hnc_last := hncm (k - 1) (by omega) (by omega)
  have hnc_g := hncm g (by omega) (by omega)
  have hnc_g1 := hncm (g + 1) (by omega) hgk
  have e1 : azim 0 p (rhoNode1_p2 FF p) (vv (k - 1)) =
      azim 0 p (rhoNode1_p2 FF p) (vv g) :=
    (azim_eq_azim_iff (v0 := (0 : V3)) (v1 := p) (w := rhoNode1_p2 FF p)
      (x := vv (k - 1)) (y := vv g) hnc_base hnc_last hnc_g).mpr hgn
  have e2 : azim 0 p (rhoNode1_p2 FF p) (vv (k - 1)) =
      azim 0 p (rhoNode1_p2 FF p) (vv (g + 1)) :=
    (azim_eq_azim_iff (v0 := (0 : V3)) (v1 := p) (w := rhoNode1_p2 FF p)
      (x := vv (k - 1)) (y := vv (g + 1)) hnc_base hnc_last hnc_g1).mpr hgn1
  have e3 : azim 0 p (rhoNode1_p2 FF p) (vv g) =
      azim 0 p (rhoNode1_p2 FF p) (vv (g + 1)) := (e2.symm.trans e1).symm
  exact (azim_eq_azim_iff (v0 := (0 : V3)) (v1 := p) (w := rhoNode1_p2 FF p)
    (x := vv g) (y := vv (g + 1)) hnc_base hnc_g hnc_g1).mp e3

/-! ## §2 G6：u 侧前向 union 归纳（HOL :2143） -/

/-- **G6（HOL :2143）**：u 侧前向 union 望远镜（成员 iff 形）。
`hstep` = 前向 1_2（`pW5_flat_cone_order`/`pW5b_hstep` 消费形，在库）。
消费面：将来 Assembly 的 u 侧并集分解。 -/
theorem pW40_G6_union (hcl : convexLocalFan_p2 V E FF)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {i : ℕ}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] p = vv n)
    (hstep : ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)}) :
    ∀ j : ℕ, j < i →
      (∀ z : V3,
        z ∈ affGe ({0} : Set V3) {p, vv (j + 1)} ↔
          ∃ j1, j1 ≤ j ∧ z ∈ affGe ({0} : Set V3) {vv j1, vv (j1 + 1)}) := by
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hvvV : ∀ m : ℕ, vv m ∈ V := fun m => by
    rw [← hiter m]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hcl.1 hp m
  have hdisj : ∀ a b : V3, a ∈ V → b ∈ V → Disjoint ({0} : Set V3) {a, b} := by
    intro a b ha hb
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => h0V (h ▸ ha), fun h => h0V (h ▸ hb)⟩
  intro j
  induction j with
  | zero =>
    intro _
    have hv0 : vv 0 = p := by
      have h := hiter 0
      simpa using h.symm
    intro z
    constructor
    · intro hz
      exact ⟨0, Nat.zero_le 0, by simpa [hv0] using hz⟩
    · rintro ⟨j1, hj1, hz⟩
      have hj0 : j1 = 0 := by omega
      subst hj0
      simpa [hv0] using hz
  | succ j ih =>
    intro hj
    have hU := AFF_GE_EQ_AFF_GE_UNION_p9 (x := (0 : V3)) (v := p)
      (u := vv (j + 2)) (v1 := vv (j + 1))
      (h1 := hdisj p (vv (j + 2)) hp (hvvV (j + 2)))
      (h2 := hdisj p (vv (j + 1)) hp (hvvV (j + 1)))
      (h3 := hdisj (vv (j + 1)) (vv (j + 2)) (hvvV (j + 1)) (hvvV (j + 2)))
      (h4 := hstep (j + 1) (by omega) (by omega))
    have hj' : j < i := by omega
    intro z
    rw [hU, Set.mem_union]
    constructor
    · rintro (hz | hz)
      · obtain ⟨j1, hj1, hz'⟩ := (ih hj' z).mp hz
        exact ⟨j1, by omega, hz'⟩
      · refine ⟨j + 1, by omega, ?_⟩
        simpa [Set.pair_comm, show j + 1 + 1 = j + 2 from by omega] using hz
    · rintro ⟨j1, hj1, hz⟩
      rcases Nat.lt_or_ge j1 (j + 1) with h | h
      · exact Or.inl ((ih hj' z).mpr ⟨j1, by omega, hz⟩)
      · have hj1e : j1 = j + 1 := by omega
        subst hj1e
        exact Or.inr (by
          simpa [Set.pair_comm, show j + 1 + 1 = j + 2 from by omega] using hz)

/-! ## §3 W35 §2 补全：hfam ⇒ J 收尾（下标引理具名化） -/

/-- **W35 §2 补全**：`hfam`（w 侧 1_2 族接口）⇒ J 收尾
`ρ(vv(i+1)) ∈ affGe{0}{v, vv(i+1)}`。`pW35_union_of_family` 在 `j := k−i−2`
的实例 + 平凡对成员（`point_in_aff_ge`）；下标引理 `hidx1/hidx2` 具名化，
消除原 whnf 超时。hfam 仍为边界（WindingSlot 同源）。 -/
theorem pW40_slot_of_family (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {k : ℕ} (hk : V.ncard = k)
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    (hfam : ∀ n : ℕ, 2 ≤ n → n ≤ k - 1 → vv n ∈ affGt ({0} : Set V3) {v, vv (n - 1)})
    {i : ℕ} (hi0 : 0 < i) (hik : i + 1 < k - 1) :
    rhoNode1_p2 FF (vv (i + 1)) ∈ affGe ({0} : Set V3) {v, vv (i + 1)} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have hvvV : ∀ n : ℕ, vv n ∈ V := fun n => by
    rw [← hiter n]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hv n
  -- 下标引理（先具名，避免 rw-in-∃ 的 whnf 爆炸）
  have hidx1 : k - (k - i - 2) - 1 = i + 1 := by omega
  have hidx2 : k - (k - i - 2) = i + 2 := by omega
  have hj : k - i - 2 < k - 2 := by omega
  have hρ : rhoNode1_p2 FF (vv (i + 1)) = vv (i + 2) := by
    rw [← hiter (i + 1), ← hiter (i + 2), show i + 2 = Nat.succ (i + 1) from rfl]
    exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) (i + 1) v).symm
  have hncρ : ¬ Collinear ℝ ({0, vv (i + 1), rhoNode1_p2 FF (vv (i + 1))} : Set V3) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf (hvvV (i + 1))
  have hnc : ¬ Collinear3 (0 : V3) (vv (i + 1)) (vv (i + 2)) := by
    show ¬ Collinear ℝ ({0, vv (i + 1), vv (i + 2)} : Set V3)
    rw [← hρ]
    exact hncρ
  have hpair : vv (i + 2) ∈ affGe ({0} : Set V3) {vv (i + 1), vv (i + 2)} :=
    (point_in_aff_ge hnc).2.2
  have hpair' : vv (i + 2) ∈
      affGe ({0} : Set V3) {vv (k - (k - i - 2) - 1), vv (k - (k - i - 2))} := by
    rwa [hidx1, hidx2]
  have hunion := pW35_union_of_family hcl hv hk hiter hfam (k - i - 2) hj
  have key : vv (i + 2) ∈ affGe ({0} : Set V3) {v, vv (k - (k - i - 2) - 1)} :=
    (hunion (vv (i + 2))).mpr ⟨k - i - 2, le_rfl, hpair'⟩
  rw [hρ]
  rwa [hidx1] at key

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW40_G1_u_mem
#print axioms Kepler.Text.pW40_G2_w_mem
#print axioms Kepler.Text.pW40_G3_azim_range
#print axioms Kepler.Text.pW40_G7_rho_g_mem
#print axioms Kepler.Text.pW40_G6_union
#print axioms Kepler.Text.pW40_slot_of_family
