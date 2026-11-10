/-
Kepler/Text/LocalFanStepW32.lean — wave W32：WINDING_CORE 试作（w 侧 azim-eq 路线镜像）。

HOL 对表（NKEZBFC.hl:2271–2498 H/I 段）：
* H 段 = u 侧 hS3 内容（UNIONS + point_in_aff_ge + ITER_CARD_MINUS1_EQ_IVS_RN1）
  + w 侧望远镜 union 等式（= 在库 `pW5w_telescope`，已核）；
* I 段 = **w 侧 azim-eq 路线**：EGHNAVX 第二支（run ⊆ affGt{0,v}{vv(k-1)}）⇒
  对 run 点 g、ρg 用 `AZIM_EQ`（= 在库 `azim_eq_azim_iff`，AzimLemmas:193；
  语句逐字：`azim v0 v1 w x = azim v0 v1 w y ↔ y ∈ affGt {v0,v1} {x}`）得 azim
  等式 ⇒ 2_1 锥成员 `g ∈ affGt{0,v}{ρg}`；
* I 段后半 + J 段 = 经 `decomposition_planar_by_angle_fan` + `LOFA_IMP_EE_TWO_ELMS`
  排除第二析取，得 1_2 形 mirror hstep（本波两轮上限内未收，见 DELIVERY 卡点）。

本件交付 = I 段前半的 **2_1 锥镜像件** `pW32_w_cone`（azim-eq 路线核心，
全部在库装配）。
-/
import Kepler.Text.LocalFanStepW30

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 w 侧 2_1 锥（azim-eq 路线） -/

/-- **w 侧 run 锥件（2_1 形，azim-eq 路线）**：EGHNAVX 第二支的 run 锥
（`vv n, vv(n+1) ∈ affGt{0,p}{vv(k-1)}`）+ `azim_eq_azim_iff` 两次 ⇒
`vv n ∈ affGt{0,p}{vv(n+1)}`（跳跃后段 `i+1 ≤ n`、`n+1 < k`）。
= HOL I 段前半（:2426–:2448 的 AZIM_EQ 链）的 Lean 镜像。 -/
theorem pW32_w_cone (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k) (hiter : ∀ i, (rhoNode1_p2 FF)^[i] p = vv i)
    (hbta : ∀ i, azim 0 p (vv 1) (vv i) = bta i)
    {i : ℕ} (hi : i < k - 1) (hbilast : bta (i + 1) = bta (k - 1)) :
    ∀ n : ℕ, i + 1 ≤ n → n + 1 < k → vv n ∈ affGt ({0, p} : Set V3) {vv (n + 1)} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have hvvV : ∀ m : ℕ, vv m ∈ V := fun m => by
    rw [← hiter m]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp m
  have hcol : ∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg p hp
  intro n hn1 hn2
  have hk1 : 0 < k := by omega
  by_cases hik : i + 1 < k - 1
  · -- run 锥（EGHNAVX 第二支 @ i+1）
    obtain ⟨-, -, -, hEG⟩ := EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hp hk hcol hiter hbta
    have hbr := (hEG (i + 1)).2 ⟨hbilast, by omega, hik⟩
    have hrun : ∀ m : ℕ, i + 1 ≤ m → m < k → vv m ∈ affGt ({0, p} : Set V3) {vv (k - 1)} :=
      fun m hm1 hm2 => hbr.2 ⟨m, hm1, hm2, rfl⟩
    have hgn := hrun n hn1 (by omega)
    have hgn1 := hrun (n + 1) (by omega) hn2
    -- 非共线（扇 + generic）
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
    have hnc_n := hncm n (by omega) (by omega)
    have hnc_n1 := hncm (n + 1) (by omega) hn2
    -- AZIM_EQ 链：均等于基准点 (k-1) 的 azim
    have e1 : azim 0 p (rhoNode1_p2 FF p) (vv (k - 1)) =
        azim 0 p (rhoNode1_p2 FF p) (vv n) :=
      (azim_eq_azim_iff (v0 := (0 : V3)) (v1 := p) (w := rhoNode1_p2 FF p)
        (x := vv (k - 1)) (y := vv n) hnc_base hnc_last hnc_n).mpr hgn
    have e2 : azim 0 p (rhoNode1_p2 FF p) (vv (k - 1)) =
        azim 0 p (rhoNode1_p2 FF p) (vv (n + 1)) :=
      (azim_eq_azim_iff (v0 := (0 : V3)) (v1 := p) (w := rhoNode1_p2 FF p)
        (x := vv (k - 1)) (y := vv (n + 1)) hnc_base hnc_last hnc_n1).mpr hgn1
    have e3 : azim 0 p (rhoNode1_p2 FF p) (vv (n + 1)) =
        azim 0 p (rhoNode1_p2 FF p) (vv n) := e2.symm.trans e1
    exact (azim_eq_azim_iff (v0 := (0 : V3)) (v1 := p) (w := rhoNode1_p2 FF p)
      (x := vv (n + 1)) (y := vv n) hnc_base hnc_n1 hnc_n).mp e3
  · -- 空段（i+1 = k-1）：域为空
    exfalso
    omega

/-! ## §2 绕序显式槽（止损兜底，W23 先例；DIFFERS 记档） -/

/-- **绕序显式槽**（WINDING_SCOUT §5 签名原样）：ρ-run 相邻对相对基 `(p, ιp)`
的 cross-dot 符号一致性（`bta` 单调为背景假设）。与 `hstep`/`hprev` 同级
信任边界——下游以假设形态消费；DIFFERS 记档：HOL 无对应显式槽（其绕序内容
内嵌于 NKEZBFC.hl:2049–2614 证体）。 -/
def WindingSlot (V : Set V3) (FF : Set (V3 × V3)) : Prop :=
  ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3), (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
  ∀ (bta : ℕ → ℝ), (∀ n, azim 0 p (vv 1) (vv n) = bta n) →
  (∀ i j, i < j → j < V.ncard → bta i ≤ bta j) →
  ∀ n : ℕ, 1 ≤ n → n + 2 < V.ncard →
    (crossProduct ((vv n : V3) : Fin 3 → ℝ) ((vv (n + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ
      (crossProduct ((p : V3) : Fin 3 → ℝ) ((ivsRhoNode1_p2 FF p : V3) : Fin 3 → ℝ)) < 0

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW32_w_cone
#check @Kepler.Text.WindingSlot
