/-
Kepler/Text/LocalFanStepBW3a.lean — wave C-W3a：传播引理的案例 1（扇角 = π）。

HOL 锚：`NKEZBFC.hl:871-972`（`azim 0 x.1 x.2 (ι x.1) = π` 支）。

内容：
* 在 dart `x` 的扇角 = π 时，把 `wedgeInFanGt_p2 x E` 严格半空间化
  （`AZIM_PI_WEDGE_CROSS_DOT_p9`：`wedge = {z | 0 < (x.1 × x.2)·z}`）；
* 用基包含 `affGt {0}{v,w} ⊆ wedgeInFanGt_p2 (v,ρv) E` 得
  `CONDITION_INANGLE_CROSS_DOT_p9` 的两个严格叉积点积；
* 用 `v×w ∥ x.1×x.2`（BACCAB）与闭楔符号（`AZIM_PI_WEDGE_GE_CROSS_DOT`）
  导出矛盾，从而 `affGt {0}{v,w} ⊆ wedge 0 x.1 x.2 (ι x.1)`。

不包含：案例 2（`azim < π`，HOL :973-1234）与总装/缺口支收口（W3b/W3c）。
本件不消费 `LocalAuto9.PROPERTIES_AFF_GT_SUBSET_WEDGE_p9`（该桩为 `sorry`）。
-/
import Kepler.Text.LocalFanStepBW2b

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## 标量/叉积小工具（本地私有，避免 LA9/XivphksKit 的 private 名） -/

/-- `dot3_p9` 在第二个变量上可加。 -/
private theorem pW3a_dot_add (u x y : V3) :
    dot3_p9 u (x + y) = dot3_p9 u x + dot3_p9 u y := by
  rw [dot3_p9, dot3_p9, dot3_p9]
  exact dotProduct_add _ _ _

/-- `dot3_p9` 在第二个变量上齐次。 -/
private theorem pW3a_dot_smul (u x : V3) (r : ℝ) :
    dot3_p9 u (r • x) = r * dot3_p9 u x := by
  rw [dot3_p9, dot3_p9]
  have h : ((r • x : V3) : Fin 3 → ℝ) = r • ((x : V3) : Fin 3 → ℝ) := rfl
  rw [h, dotProduct_smul, smul_eq_mul]

/-- `cross3_p9` 的系数（`WithLp` 包装的定义展开）。 -/
private theorem pW3a_coe_cross (a b : V3) :
    ((cross3_p9 a b : V3) : Fin 3 → ℝ)
      = crossProduct ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ) := by
  rw [cross3_p9, coe_toLp]

/-- 非共线三元组 ⇒ 叉积非零（`local_fan_p2` 的 dart 端点用它）。 -/
private theorem pW3a_cross_ne_zero {a b : V3} (h : ¬ Collinear3 (0 : V3) a b) :
    cross3_p9 a b ≠ 0 := by
  intro hc
  have ha0 : (a : V3) ≠ 0 := fun h0 => h (collinear3_of_eq (v := (0 : V3)) (w := a) h0)
  have hb0 : (b : V3) ≠ 0 := fun h0 =>
    h (collinear3_pair_left (v0 := (0 : V3)) (v1 := a) (x := b) h0)
  have hz : ((cross3_p9 a b : V3) : Fin 3 → ℝ) = 0 := by rw [hc]; rfl
  rw [pW3a_coe_cross] at hz
  have hnotli : ¬ LinearIndependent ℝ
      (![((a : V3) : Fin 3 → ℝ), ((b : V3) : Fin 3 → ℝ)]) := by
    rw [← crossProduct_ne_zero_iff_linearIndependent]
    exact fun hne => hne hz
  have ha0' : ((a : V3) : Fin 3 → ℝ) ≠ 0 := by
    intro h0
    exact ha0 (by
      have := congrArg (fun p : Fin 3 → ℝ => (WithLp.toLp 2 p : V3)) h0
      simpa using this)
  have hmul : ∀ c : ℝ, c • ((a : V3) : Fin 3 → ℝ) ≠ ((b : V3) : Fin 3 → ℝ) := by
    intro c hc'
    apply h
    rw [collinear3_iff_smul (v := (0 : V3)) (w := a) (w1 := b) ha0]
    refine ⟨c, ?_⟩
    have := congrArg (fun p : Fin 3 → ℝ => (WithLp.toLp 2 p : V3)) hc'.symm
    simpa using this
  apply hnotli
  rw [LinearIndependent.pair_iff' ha0']
  intro c
  exact hmul c

/-! ## `EE`/`azimCycle` 的展开（dart `x`） -/

/-- dart `x ∈ FF` 的 `EE` 基数为 2。 -/
private theorem pW3a_card_EE (h : localFan_p2 V E FF) {x : V3 × V3} (hx : x ∈ FF) :
    (EE_p2 x.1 E).ncard = 2 := by
  obtain ⟨hx1V, -, -, -⟩ := LOCAL_FAN_IMP_IN_V h hx hx
  exact LOFA_CARD_EE_V_1 h hx1V

/-- dart `x ∈ FF` 的 `azimCycle` 等于 `ι x.1`。 -/
private theorem pW3a_azimCycle (h : localFan_p2 V E FF) {x : V3 × V3} (hx : x ∈ FF) :
    azimCycle_p2 (EE_p2 x.1 E) (0 : V3) x.1 x.2 = ivsRhoNode1_p2 FF x.1 := by
  obtain ⟨hx1V, -, -, -⟩ := LOCAL_FAN_IMP_IN_V h hx hx
  have hιV : ivsRhoNode1_p2 FF x.1 ∈ V := LOCAL_FAN_IVS_IN_V h hx1V
  have hρ : rhoNode1_p2 FF (ivsRhoNode1_p2 FF x.1) = x.1 :=
    LOCAL_FAN_RHO_NODE_IVS h hx1V
  have hrho2 : rhoNode1_p2 FF x.1 = x.2 := DETER_RHO_NODE h hx
  have hEE : (EE_p2 x.1 E) = ({x.2, ivsRhoNode1_p2 FF x.1} : Set V3) := by
    rw [LOFA_IMP_EE_TWO_ELMS h hιV hρ, hrho2]
  rw [hEE]
  exact AZIM_CYCLE_TWO_POINT_SET x.2 (ivsRhoNode1_p2 FF x.1) (0 : V3) x.1

/-- 闭楔符号：`y ∈ V` ⇒ `0 ≤ (x.1 × x.2)·y`（`x` 的扇角 = π 时）。 -/
private theorem pW3a_wedgeGe_nonneg (hcl : convexLocalFan_p2 V E FF)
    {x : V3 × V3} (hx : x ∈ FF)
    (hpi : azim 0 x.1 x.2 (ivsRhoNode1_p2 FF x.1) = Real.pi)
    {y : V3} (hy : y ∈ V) :
    0 ≤ dot3_p9 (cross3_p9 x.1 x.2) y := by
  have hl : localFan_p2 V E FF := hcl.1
  have hconv := hcl.2
  have hmem : y ∈ wedgeInFanGe_p2 x E := (hconv x hx).2 hy
  unfold wedgeInFanGe_p2 at hmem
  rw [if_pos (by rw [pW3a_card_EE hl hx]; norm_num), pW3a_azimCycle hl hx] at hmem
  rw [AZIM_PI_WEDGE_GE_CROSS_DOT (u := (0 : V3)) (v := x.1) (w := x.2)
    (ww := ivsRhoNode1_p2 FF x.1) hpi] at hmem
  simpa [dot3_p9, cross3_p9, coe_toLp] using hmem

/-- 基包含展开：`wedgeInFanGt_p2 (v,ρv) E = wedge 0 v ρv ιv`。 -/
private theorem pW3a_base_unfold (h : localFan_p2 V E FF) {v w : V3} (hv : v ∈ V)
    (hbase : affGt ({0} : Set V3) {v, w}
      ⊆ wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E) :
    affGt ({0} : Set V3) {v, w}
      ⊆ wedge (0 : V3) v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) := by
  have hι : ivsRhoNode1_p2 FF v ∈ V := LOCAL_FAN_IVS_IN_V h hv
  have hρ : rhoNode1_p2 FF (ivsRhoNode1_p2 FF v) = v := LOCAL_FAN_RHO_NODE_IVS h hv
  have hEE : (EE_p2 v E) = ({rhoNode1_p2 FF v, ivsRhoNode1_p2 FF v} : Set V3) :=
    LOFA_IMP_EE_TWO_ELMS h hι hρ
  have hcard : 1 < (EE_p2 v E).ncard := by
    rw [LOFA_CARD_EE_V_1 h hv]; norm_num
  have hcyc : azimCycle_p2 (EE_p2 v E) (0 : V3) v (rhoNode1_p2 FF v)
      = ivsRhoNode1_p2 FF v := by
    rw [hEE]
    exact AZIM_CYCLE_TWO_POINT_SET _ _ _ _
  intro z hz
  have hz' := hbase hz
  unfold wedgeInFanGt_p2 at hz'
  rwa [if_pos hcard, hcyc] at hz'

/-- `affGt {0}{v,w}` 的两正系数分解。 -/
private theorem pW3a_decomp {v w z : V3} (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hvw : v ≠ w)
    (hnc : ¬ Collinear3 (0 : V3) v w)
    (hz : z ∈ affGt ({0} : Set V3) {v, w}) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ z = a • v + b • w := by
  have hnc0 : ¬ Collinear ℝ ({0, v, w} : Set V3) := hnc
  rw [aff_gt_inter_aff_gt (x := (0 : V3)) (v := v) (w := w) hnc0] at hz
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨c, hc0, h, hz1'⟩ :=
    (affGt_pair_iff (v0 := (0 : V3)) (v1 := v) (x := w) (y := z)
      (Ne.symm hv0) hw0 (Ne.symm hvw)).mp hz1
  obtain ⟨c', hc'0, h', hz2'⟩ :=
    (affGt_pair_iff (v0 := (0 : V3)) (v1 := w) (x := v) (y := z)
      (Ne.symm hw0) hv0 hvw).mp hz2
  have h1 : z = c • w + h • v := by simpa using hz1'
  have h2 : z = c' • v + h' • w := by simpa using hz2'
  -- 转到 `Fin 3 → ℝ` 世界做系数比较
  set A : Fin 3 → ℝ := ((v : V3) : Fin 3 → ℝ) with hAdef
  set B : Fin 3 → ℝ := ((w : V3) : Fin 3 → ℝ) with hBdef
  set Zh : Fin 3 → ℝ := ((z : V3) : Fin 3 → ℝ) with hZdef
  have h1' : Zh = c • B + h • A := by
    rw [hZdef, hBdef, hAdef]
    have := congrArg (fun p : V3 => (p : Fin 3 → ℝ)) h1
    simpa using this
  have h2' : Zh = c' • A + h' • B := by
    rw [hZdef, hAdef, hBdef]
    have := congrArg (fun p : V3 => (p : Fin 3 → ℝ)) h2
    simpa using this
  have heq' : c • B + h • A = c' • A + h' • B := by rw [← h1', ← h2']
  have h0' : (c - h') • B + (h - c') • A = 0 := by
    rw [sub_smul, sub_smul]
    linear_combination heq'
  -- `w×v ≠ 0`（非共线）
  have hwv_nc : ¬ Collinear3 (0 : V3) w v := by
    intro hc
    apply hnc
    have hset : ({0, v, w} : Set V3) = {0, w, v} := by
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    simpa [Collinear3, hset] using hc
  have hBAne : crossProduct B A ≠ 0 := by
    intro hzero
    apply pW3a_cross_ne_zero hwv_nc
    rw [cross3_p9]
    have hzero' : crossProduct ((w : V3) : Fin 3 → ℝ) ((v : V3) : Fin 3 → ℝ) = 0 := by
      rw [hBdef, hAdef] at hzero
      exact hzero
    rw [hzero']
    simp
  have hcv : crossProduct ((c - h') • B + (h - c') • A) A = 0 := by
    rw [h0']
    simp
  have hkey : (c - h') • crossProduct B A = 0 := by
    simpa [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] using hcv
  have hc_eq : c = h' := by
    have := (smul_eq_zero.mp hkey).resolve_right hBAne
    exact sub_eq_zero.mp this
  have hAne : A ≠ 0 := by
    rw [hAdef]
    intro h0A
    apply hv0
    have := congrArg (fun p : Fin 3 → ℝ => (WithLp.toLp 2 p : V3)) h0A
    simpa using this
  have hh_eq : h = c' := by
    have heq'' := heq'
    rw [hc_eq] at heq''
    have hv_eq : h • A = c' • A := by
      have hcancel : c • B + h • A = c • B + c' • A := by
        rw [← hc_eq] at heq''
        rw [heq'']
        exact add_comm _ _
      exact add_left_cancel hcancel
    have hsub : (h - c') • A = 0 := by rw [sub_smul, hv_eq, sub_eq_zero]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hAne)
  exact ⟨h, c, by rw [hh_eq]; exact hc'0, hc0, by rw [add_comm]; exact h1⟩

/-! ## 主定理（案例 1：扇角 = π） -/

/-- **传播引理案例 1**：若 dart `x` 在 `x.1` 处的扇角 = π，则基包含传播到 `x`。
（HOL `NKEZBFC.hl:871-972`；W3a。） -/
theorem pW3a_affGt_subset_wedge_pi
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {v w : V3} (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (haz : azimInFan_p2 (v, rhoNode1_p2 FF v) E < Real.pi)
    (hbase : affGt ({0} : Set V3) {v, w}
      ⊆ wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E)
    {x : V3 × V3} (hx : x ∈ FF)
    (hpi : azim 0 x.1 x.2 (ivsRhoNode1_p2 FF x.1) = Real.pi) :
    affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E := by
  have hl : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hv0 : v ≠ 0 := fun h0 => h0V (h0 ▸ hv)
  have hw0 : w ≠ 0 := fun h0 => h0V (h0 ▸ hw)
  have hcol_v : ¬ Collinear ℝ ({0, v, w} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hl (fun _ _ => trivial) hg v hv w hw (Ne.symm hvw)
  have hnc_vw : ¬ Collinear3 (0 : V3) v w := hcol_v
  obtain ⟨hx1V, hx2V, -, -⟩ := LOCAL_FAN_IMP_IN_V hl hx hx
  have hx12 : x.1 ≠ x.2 := LOCAL_FAN_IN_FF_DISTINCT hl hx
  have hcol_x : ¬ Collinear3 (0 : V3) x.1 x.2 :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hl (fun _ _ => trivial) hg x.1 hx1V x.2 hx2V (Ne.symm hx12)
  -- 目标：把 wedgeInFanGt_p2 x E 严格半空间化
  unfold wedgeInFanGt_p2
  rw [if_pos (by rw [pW3a_card_EE hl hx]; norm_num), pW3a_azimCycle hl hx]
  rw [AZIM_PI_WEDGE_CROSS_DOT_p9 (0 : V3) x.1 x.2
    (ivsRhoNode1_p2 FF x.1) hpi]
  -- 严格半空间：`0 < (x.1 × x.2)·z`
  intro z hz
  simp only [Set.mem_setOf_eq, sub_zero]
  -- 基包含 ⇒ 两个严格叉积点积
  have hρV : rhoNode1_p2 FF v ∈ V := LOCAL_FAN_ITER_RHO_NODE_IN_V hl hv 1
  have hιV : ivsRhoNode1_p2 FF v ∈ V := LOCAL_FAN_IVS_IN_V hl hv
  have h5 : azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) < Real.pi := by
    have h := CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_p9 hcl v hv
    show interiorAngle1_p2 0 FF v < Real.pi
    rw [h]
    exact haz
  have hcond := CONDITION_INANGLE_CROSS_DOT_p9 (0 : V3) v w
    (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v)
    (pW3a_base_unfold hl hv hbase) hnc_vw
    (by rw [show ({0, v, rhoNode1_p2 FF v} : Set V3) = {0, v, rhoNode1_p2 FF v} from rfl];
        exact LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hl hv)
    (LOFA_IMP_NOT_COLL_IVS hl hv) h5
  obtain ⟨hA, hB⟩ := hcond
  -- 系数分解
  obtain ⟨a, b, ha0, hb0, hzrep⟩ :=
    pW3a_decomp hv0 hw0 hvw hnc_vw hz
  -- 闭楔符号
  have hNv : 0 ≤ dot3_p9 (cross3_p9 x.1 x.2) v := pW3a_wedgeGe_nonneg hcl hx hpi hv
  have hNw : 0 ≤ dot3_p9 (cross3_p9 x.1 x.2) w := pW3a_wedgeGe_nonneg hcl hx hpi hw
  have hNρ : 0 ≤ dot3_p9 (cross3_p9 x.1 x.2) (rhoNode1_p2 FF v) :=
    pW3a_wedgeGe_nonneg hcl hx hpi hρV
  have hNι : 0 ≤ dot3_p9 (cross3_p9 x.1 x.2) (ivsRhoNode1_p2 FF v) :=
    pW3a_wedgeGe_nonneg hcl hx hpi hιV
  -- 至少一个 `N·v`、`N·w` 严格正
  have hpos : 0 < dot3_p9 (cross3_p9 x.1 x.2) v ∨
      0 < dot3_p9 (cross3_p9 x.1 x.2) w := by
    rcases lt_or_eq_of_le hNv with h | h
    · exact Or.inl h
    · rcases lt_or_eq_of_le hNw with h2 | h2
      · exact Or.inr h2
      · exfalso
        -- `N·v = N·w = 0` 与 `v×w ∥ N`、两个严格符号矛盾
        -- 全部转到 `Fin 3 → ℝ` 世界
        set A : Fin 3 → ℝ := ((v : V3) : Fin 3 → ℝ) with hAdef
        set B : Fin 3 → ℝ := ((w : V3) : Fin 3 → ℝ) with hBdef
        set N : Fin 3 → ℝ := ((cross3_p9 x.1 x.2 : V3) : Fin 3 → ℝ) with hNdef
        set R : Fin 3 → ℝ := ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ) with hRdef
        set I : Fin 3 → ℝ := ((ivsRhoNode1_p2 FF v : V3) : Fin 3 → ℝ) with hIdef
        have hAN : A ⬝ᵥ N = 0 := by
          rw [hNdef, hAdef]
          simpa [dot3_p9, dotProduct_comm] using h.symm
        have hBN : B ⬝ᵥ N = 0 := by
          rw [hNdef, hBdef]
          simpa [dot3_p9, dotProduct_comm] using h2.symm
        have hApos : 0 < (A ⨯₃ R) ⬝ᵥ B := by
          rw [hAdef, hRdef, hBdef]
          simpa [dot3_p9, pW3a_coe_cross] using hA
        have hBpos : 0 < (A ⨯₃ B) ⬝ᵥ I := by
          rw [hAdef, hBdef, hIdef]
          simpa [dot3_p9, pW3a_coe_cross] using hB
        have hRN : 0 ≤ N ⬝ᵥ R := by
          rw [hNdef, hRdef]
          simpa [dot3_p9] using hNρ
        have hIN : 0 ≤ N ⬝ᵥ I := by
          rw [hNdef, hIdef]
          simpa [dot3_p9] using hNι
        -- `N ≠ 0`
        have hNne : N ≠ 0 := by
          rw [hNdef]
          have hc : cross3_p9 x.1 x.2 ≠ 0 := pW3a_cross_ne_zero hcol_x
          intro hz0
          exact hc (by
            have := congrArg (fun p : Fin 3 → ℝ => (WithLp.toLp 2 p : V3)) hz0
            simpa using this)
        have hNN : N ⬝ᵥ N ≠ 0 := fun h0 => hNne (dotProduct_self_eq_zero.mp h0)
        have hNNpos : 0 < N ⬝ᵥ N :=
          lt_of_le_of_ne (by simpa using dotProduct_star_self_nonneg (v := N))
            (Ne.symm hNN)
        -- `(A×B)×N = 0`
        have hcross0 : (A ⨯₃ B) ⨯₃ N = 0 := by
          rw [cross_cross_eq_smul_sub_smul, hAN, hBN, zero_smul, zero_smul,
            sub_zero]
        -- `X = μ•N`
        have hXX : (A ⨯₃ B) ⨯₃ N ⨯₃ N = 0 := by rw [hcross0]; simp
        have hBAC := cross_cross_eq_smul_sub_smul (A ⨯₃ B) N N
        rw [hXX] at hBAC
        -- hBAC : 0 = ((A×B)·N)•N - (N·N)•(A×B)
        set μ : ℝ := ((A ⨯₃ B) ⬝ᵥ N) / (N ⬝ᵥ N) with hμdef
        have hXeq : A ⨯₃ B = μ • N := by
          have hX : A ⨯₃ B = (((A ⨯₃ B) ⬝ᵥ N) / (N ⬝ᵥ N)) • N := by
            have h0 : ((A ⨯₃ B) ⬝ᵥ N) • N = (N ⬝ᵥ N) • (A ⨯₃ B) :=
              sub_eq_zero.mp hBAC.symm
            calc A ⨯₃ B = (1 / (N ⬝ᵥ N)) • ((N ⬝ᵥ N) • (A ⨯₃ B)) := by
                  rw [smul_smul, one_div_mul_cancel hNN, one_smul]
              _ = (1 / (N ⬝ᵥ N)) • (((A ⨯₃ B) ⬝ᵥ N) • N) := by rw [h0]
              _ = (((A ⨯₃ B) ⬝ᵥ N) / (N ⬝ᵥ N)) • N := by
                  rw [smul_smul]; ring_nf
          rw [hX, hμdef]
        -- 两个交叉点积恒等式
        have hident1 : (A ⨯₃ R) ⬝ᵥ B = - (μ * (N ⬝ᵥ R)) := by
          -- `(A×R)·B = R·(B×A) = -R·(A×B) = -μ (R·N) = -μ (N·R)`
          have h1 : (A ⨯₃ R) ⬝ᵥ B = R ⬝ᵥ (B ⨯₃ A) := by
            rw [dotProduct_comm]
            rw [triple_product_permutation]
            rw [triple_product_permutation]
          have h2 : B ⨯₃ A = - (A ⨯₃ B) := by
            rw [← cross_anticomm]
          have h3 : R ⬝ᵥ (A ⨯₃ B) = μ * (N ⬝ᵥ R) := by
            rw [hXeq, dotProduct_smul, smul_eq_mul, dotProduct_comm R N]
          rw [h1, h2, dotProduct_neg, h3]
        have hident2 : (A ⨯₃ B) ⬝ᵥ I = μ * (N ⬝ᵥ I) := by
          rw [hXeq, smul_dotProduct, smul_eq_mul]
        -- 线性收尾
        have hNRpos : 0 < N ⬝ᵥ R := by
          rcases lt_or_eq_of_le hRN with h' | h'
          · exact h'
          · exfalso
            rw [hident1, ← h', mul_zero, neg_zero] at hApos
            exact lt_irrefl _ hApos
        have hμneg : μ < 0 := by nlinarith [hApos, hident1, hNRpos]
        have hNIneg : N ⬝ᵥ I < 0 := by nlinarith [hBpos, hident2, hμneg]
        linarith [hIN]
  -- 收尾：`N·z = a (N·v) + b (N·w) > 0`
  have hNz : dot3_p9 (cross3_p9 x.1 x.2) z
      = a * dot3_p9 (cross3_p9 x.1 x.2) v
        + b * dot3_p9 (cross3_p9 x.1 x.2) w := by
    rw [hzrep, pW3a_dot_add, pW3a_dot_smul, pW3a_dot_smul]
  rw [hNz]
  rcases hpos with h | h
  · nlinarith [mul_pos ha0 h, mul_nonneg hb0.le hNw]
  · nlinarith [mul_nonneg ha0.le hNv, mul_pos hb0 h]

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW3a_affGt_subset_wedge_pi
#print axioms Kepler.Text.pW3a_affGt_subset_wedge_pi
