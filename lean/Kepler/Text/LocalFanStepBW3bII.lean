/-
Kepler/Text/LocalFanStepBW3bII.lean — wave C-W3b-ii：传播引理案例 2（扇角 < π）。

HOL 锚：`NKEZBFC.hl:973-1234`（`azim 0 x.1 x.2 (ι x.1) < π` 支）。

路线（W3b-i 的件 + 公开库）：
* `wedge_eq_affGt`（LuneVolume:646）把 `wedge 0 x.1 x.2 (ιx.1)` 化为
  `affGt {0,x.1}{x.2,ιx.1}`；
* `inter_aff_gt_3_1_is_aff_gt_2_2` + 两次 `aff_gt_3_1_rep_cross_dot`
  把目标化为两个严格叉积点积（法向量 `N = x.1×x.2` 与 `d×x.1`，d = ιx.1）；
* 两个 `hpos` 由 `pW3b_crossdot_pos_of_azim_lt_pi`（W3b-i）供给；
* 非严格侧（y ∈ V）由 `WEDGE_GE_EQ_AFF_GE` + `AFF_GE_2_2_p9` 分解直接算符号
  （不经任何 Coplanar 前件，规避 Mathlib/Geom 两种 `Coplanar` 读法混用）；
* 零情形把 W3a 案例 1 的 BACCAB 矛盾一般化为 `pW3bII_norm_pos`（任意法向量 n），
  对 n = N 与 n = d×x.1 各实例化一次；
* W3a 的分解件在本文件本地重证（`pW3a_*` 为 private，不可跨文件消费）。

不包含：`= π ∨ < π` 二分与坏 dart 收口（W3c）。
-/
import Kepler.Text.LocalFanStepBW3bI

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §0 标量桥（本地私有） -/

private theorem pW3bII_crossdot_eq (a b y : V3) :
    dot3_p9 (cross3_p9 a b) y
      = (crossProduct ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ))
          ⬝ᵥ ((y : V3) : Fin 3 → ℝ) := by
  rw [dot3_p9, cross3_p9, coe_toLp]

private theorem pW3bII_dot_add (u x y : V3) :
    dot3_p9 u (x + y) = dot3_p9 u x + dot3_p9 u y := by
  rw [dot3_p9, dot3_p9, dot3_p9]
  exact dotProduct_add _ _ _

private theorem pW3bII_dot_smul (u x : V3) (r : ℝ) :
    dot3_p9 u (r • x) = r * dot3_p9 u x := by
  rw [dot3_p9, dot3_p9]
  have h : ((r • x : V3) : Fin 3 → ℝ) = r • ((x : V3) : Fin 3 → ℝ) := rfl
  rw [h, dotProduct_smul, smul_eq_mul]

private theorem pW3bII_dot_zero (u : V3) : dot3_p9 u (0 : V3) = 0 := by
  rw [dot3_p9]
  simp

/-- `(a×b)·a = 0`。 -/
private theorem pW3bII_dot_cross_left (a b : V3) : dot3_p9 (cross3_p9 a b) a = 0 := by
  rw [pW3bII_crossdot_eq]
  rw [dotProduct_comm]
  exact dot_self_cross _ _

/-- `(a×b)·b = 0`。 -/
private theorem pW3bII_dot_cross_right (a b : V3) : dot3_p9 (cross3_p9 a b) b = 0 := by
  rw [pW3bII_crossdot_eq]
  rw [dotProduct_comm]
  exact dot_cross_self _ _

/-- 三重积循环：`(a×b)·c = (b×c)·a`。 -/
private theorem pW3bII_triple_cyclic (a b c : V3) :
    dot3_p9 (cross3_p9 a b) c = dot3_p9 (cross3_p9 b c) a := by
  rw [pW3bII_crossdot_eq, pW3bII_crossdot_eq, dotProduct_comm]
  rw [triple_product_permutation]
  rw [dotProduct_comm]

/-- dart `x ∈ FF` 的 `EE` 基数为 2（本地重证）。 -/
private theorem pW3bII_card_EE (h : localFan_p2 V E FF) {x : V3 × V3} (hx : x ∈ FF) :
    (EE_p2 x.1 E).ncard = 2 := by
  obtain ⟨hx1V, -, -, -⟩ := LOCAL_FAN_IMP_IN_V h hx hx
  exact LOFA_CARD_EE_V_1 h hx1V

/-- dart `x ∈ FF` 的 `azimCycle` 等于 `ι x.1`（本地重证）。 -/
private theorem pW3bII_azimCycle (h : localFan_p2 V E FF) {x : V3 × V3} (hx : x ∈ FF) :
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

/-- 非共线三元组 ⇒ 叉积非零（本地重证；`pW3a_cross_ne_zero` 为 private）。 -/
private theorem pW3bII_cross_ne_zero {a b : V3} (h : ¬ Collinear3 (0 : V3) a b) :
    cross3_p9 a b ≠ 0 := by
  intro hc
  have ha0 : (a : V3) ≠ 0 := fun h0 => h (collinear3_of_eq (v := (0 : V3)) (w := a) h0)
  have hb0 : (b : V3) ≠ 0 := fun h0 =>
    h (collinear3_pair_left (v0 := (0 : V3)) (v1 := a) (x := b) h0)
  have hz : ((cross3_p9 a b : V3) : Fin 3 → ℝ) = 0 := by rw [hc]; rfl
  rw [show ((cross3_p9 a b : V3) : Fin 3 → ℝ)
      = crossProduct ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ)
      from by rw [cross3_p9, coe_toLp]] at hz
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

/-- 基包含展开（本地重证）。 -/
private theorem pW3bII_base_unfold (h : localFan_p2 V E FF) {v w : V3} (hv : v ∈ V)
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

/-- `affGt {0}{v,w}` 的两正系数分解（本地重证）。 -/
private theorem pW3bII_decomp {v w z : V3} (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hvw : v ≠ w)
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
    apply pW3bII_cross_ne_zero hwv_nc
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

/-! ## §1 一般法向量的零情形矛盾（W3a 案例 1 的 BACCAB 论证一般化） -/

/-- 若 `n ≠ 0`，且 `n` 对 `v,w,ρ,ι` 的四个点积非负、两个基包含严格符号成立，
则 `n·v`、`n·w` 不可能同时为 0。 -/
private theorem pW3bII_norm_pos (n v w ρ ι : V3) (hn : n ≠ 0)
    (hA : 0 < dot3_p9 (cross3_p9 v ρ) w)
    (hB : 0 < dot3_p9 (cross3_p9 v w) ι)
    (hnv : 0 ≤ dot3_p9 n v) (hnw : 0 ≤ dot3_p9 n w)
    (hnρ : 0 ≤ dot3_p9 n ρ) (hnι : 0 ≤ dot3_p9 n ι) :
    0 < dot3_p9 n v ∨ 0 < dot3_p9 n w := by
  rcases lt_or_eq_of_le hnv with h | h
  · exact Or.inl h
  · rcases lt_or_eq_of_le hnw with h2 | h2
    · exact Or.inr h2
    · exfalso
      set A : Fin 3 → ℝ := ((v : V3) : Fin 3 → ℝ) with hAdef
      set B : Fin 3 → ℝ := ((w : V3) : Fin 3 → ℝ) with hBdef
      set N : Fin 3 → ℝ := ((n : V3) : Fin 3 → ℝ) with hNdef
      set R : Fin 3 → ℝ := ((ρ : V3) : Fin 3 → ℝ) with hRdef
      set I : Fin 3 → ℝ := ((ι : V3) : Fin 3 → ℝ) with hIdef
      have hAN : A ⬝ᵥ N = 0 := by
        rw [hNdef, hAdef]
        simpa [dot3_p9, dotProduct_comm] using h.symm
      have hBN : B ⬝ᵥ N = 0 := by
        rw [hNdef, hBdef]
        simpa [dot3_p9, dotProduct_comm] using h2.symm
      have hApos : 0 < (A ⨯₃ R) ⬝ᵥ B := by
        rw [hAdef, hRdef, hBdef]
        simpa only [pW3bII_crossdot_eq] using hA
      have hBpos : 0 < (A ⨯₃ B) ⬝ᵥ I := by
        rw [hAdef, hBdef, hIdef]
        simpa only [pW3bII_crossdot_eq] using hB
      have hRN : 0 ≤ N ⬝ᵥ R := by
        rw [hNdef, hRdef]
        simpa [dot3_p9] using hnρ
      have hIN : 0 ≤ N ⬝ᵥ I := by
        rw [hNdef, hIdef]
        simpa [dot3_p9] using hnι
      have hNne : N ≠ 0 := by
        rw [hNdef]
        intro hz0
        apply hn
        have := congrArg (fun p : Fin 3 → ℝ => (WithLp.toLp 2 p : V3)) hz0
        simpa using this
      have hNN : N ⬝ᵥ N ≠ 0 := fun h0 => hNne (dotProduct_self_eq_zero.mp h0)
      have hcross0 : (A ⨯₃ B) ⨯₃ N = 0 := by
        rw [cross_cross_eq_smul_sub_smul, hAN, hBN, zero_smul, zero_smul, sub_zero]
      have hXX : (A ⨯₃ B) ⨯₃ N ⨯₃ N = 0 := by rw [hcross0]; simp
      have hBAC := cross_cross_eq_smul_sub_smul (A ⨯₃ B) N N
      rw [hXX] at hBAC
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
      have hident1 : (A ⨯₃ R) ⬝ᵥ B = - (μ * (N ⬝ᵥ R)) := by
        have h1 : (A ⨯₃ R) ⬝ᵥ B = R ⬝ᵥ (B ⨯₃ A) := by
          rw [dotProduct_comm]
          rw [triple_product_permutation]
          rw [triple_product_permutation]
        have h2' : B ⨯₃ A = - (A ⨯₃ B) := by
          rw [← cross_anticomm]
        have h3 : R ⬝ᵥ (A ⨯₃ B) = μ * (N ⬝ᵥ R) := by
          rw [hXeq, dotProduct_smul, smul_eq_mul, dotProduct_comm R N]
        rw [h1, h2', dotProduct_neg, h3]
      have hident2 : (A ⨯₃ B) ⬝ᵥ I = μ * (N ⬝ᵥ I) := by
        rw [hXeq, smul_dotProduct, smul_eq_mul]
      have hNRpos : 0 < N ⬝ᵥ R := by
        rcases lt_or_eq_of_le hRN with h' | h'
        · exact h'
        · exfalso
          rw [hident1, ← h', mul_zero, neg_zero] at hApos
          exact lt_irrefl _ hApos
      have hμneg : μ < 0 := by nlinarith [hApos, hident1, hNRpos]
      have hNIneg : N ⬝ᵥ I < 0 := by nlinarith [hBpos, hident2, hμneg]
      linarith [hIN]

/-! ## §2 主定理（案例 2：扇角 < π） -/

/-- **传播引理案例 2**：`azim 0 x.1 x.2 (ι x.1) < π` 时基包含传播到 `x`
（HOL `NKEZBFC.hl:973-1234`；W3b-ii）。 -/
theorem pW3b_affGt_subset_wedge_lt_pi
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {v w : V3} (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (haz : azimInFan_p2 (v, rhoNode1_p2 FF v) E < Real.pi)
    (hbase : affGt ({0} : Set V3) {v, w}
      ⊆ wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E)
    {x : V3 × V3} (hx : x ∈ FF)
    (hlt : azim 0 x.1 x.2 (ivsRhoNode1_p2 FF x.1) < Real.pi) :
    affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E := by
  have hl : localFan_p2 V E FF := hcl.1
  have hconv := hcl.2
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hv0 : v ≠ 0 := fun h0 => h0V (h0 ▸ hv)
  have hw0 : w ≠ 0 := fun h0 => h0V (h0 ▸ hw)
  have hcol_v : ¬ Collinear ℝ ({0, v, w} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hl (fun _ _ => trivial) hg v hv w hw (Ne.symm hvw)
  have hnc_vw : ¬ Collinear3 (0 : V3) v w := hcol_v
  obtain ⟨hx1V, hx2V, -, -⟩ := LOCAL_FAN_IMP_IN_V hl hx hx
  have hx12 : x.1 ≠ x.2 := LOCAL_FAN_IN_FF_DISTINCT hl hx
  have hcol_x : ¬ Collinear3 (0 : V3) x.1 x.2 :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hl (fun _ _ => trivial) hg x.1 hx1V x.2 hx2V
      (Ne.symm hx12)
  have hx1ne0 : x.1 ≠ 0 := fun h0 => h0V (h0 ▸ hx1V)
  have hιV : ivsRhoNode1_p2 FF x.1 ∈ V := LOCAL_FAN_IVS_IN_V hl hx1V
  have hnc1d : ¬ Collinear3 (0 : V3) x.1 (ivsRhoNode1_p2 FF x.1) :=
    LOFA_IMP_NOT_COLL_IVS hl hx1V
  -- d := ι x.1
  set d : V3 := ivsRhoNode1_p2 FF x.1 with hddef
  have hdV : d ∈ V := by rw [hddef]; exact hιV
  -- 0 < azim 0 x.1 x.2 d
  have h0 : 0 < azim 0 x.1 x.2 d := by
    have hpos := INTERIOR_ANGLE1_POS hl hx1V
    have hrho : rhoNode1_p2 FF x.1 = x.2 := DETER_RHO_NODE hl hx
    have heq : azim 0 x.1 x.2 d = azim 0 x.1 (rhoNode1_p2 FF x.1)
        (ivsRhoNode1_p2 FF x.1) := by
      rw [hrho, hddef]
    rw [heq]
    exact hpos
  -- 两个严格 hpos
  have hposN : 0 < dot3_p9 (cross3_p9 x.1 x.2) d := by
    have hfin : 0 < (crossProduct ((x.1 : V3) : Fin 3 → ℝ)
        ((x.2 : V3) : Fin 3 → ℝ)) ⬝ᵥ ((d : V3) : Fin 3 → ℝ) :=
      pW3b_crossdot_pos_of_azim_lt_pi x.1 x.2 d hx1ne0 hcol_x hnc1d h0 hlt
    rwa [pW3bII_crossdot_eq]
  have hposD : 0 < dot3_p9 (cross3_p9 d x.1) x.2 := by
    rw [pW3bII_triple_cyclic]
    exact hposN
  -- 四个点（v,w,ρv,ιv）的闭楔符号
  have hdis : Disjoint ({0, x.1} : Set V3) ({x.2, d} : Set V3) := by
    refine Set.disjoint_left.mpr ?_
    intro y hy1 hy2
    rcases Set.mem_insert_iff.mp hy1 with h | h
    · subst h
      rcases Set.mem_insert_iff.mp hy2 with h' | h'
      · exact h0V (h' ▸ hx2V)
      · exact h0V (h' ▸ hdV)
    · subst h
      rcases Set.mem_insert_iff.mp hy2 with h' | h'
      · exact hx12 h'
      · exact hnc1d (by rw [← h']; exact collinear3_pair_right rfl)
  have hsigns : ∀ y ∈ V, 0 ≤ dot3_p9 (cross3_p9 x.1 x.2) y ∧
      0 ≤ dot3_p9 (cross3_p9 d x.1) y := by
    intro y hy
    have hmem : y ∈ wedgeInFanGe_p2 x E := (hconv x hx).2 hy
    unfold wedgeInFanGe_p2 at hmem
    rw [if_pos (by rw [pW3bII_card_EE hl hx]; norm_num), pW3bII_azimCycle hl hx] at hmem
    rw [WEDGE_GE_EQ_AFF_GE (v0 := (0 : V3)) (v1 := x.1) (w1 := x.2)
      (w2 := ivsRhoNode1_p2 FF x.1) hlt hcol_x hnc1d] at hmem
    rw [← hddef] at hmem
    rw [AFF_GE_2_2_p9 (0 : V3) x.1 x.2 d hdis] at hmem
    simp only [Set.mem_setOf_eq] at hmem
    obtain ⟨t1, t2, t3, t4, ht3, ht4, hsum, hy'⟩ := hmem
    constructor
    · have hexp : dot3_p9 (cross3_p9 x.1 x.2) y
          = t3 * dot3_p9 (cross3_p9 x.1 x.2) x.2
            + t4 * dot3_p9 (cross3_p9 x.1 x.2) d := by
        rw [hy']
        rw [pW3bII_dot_add, pW3bII_dot_add, pW3bII_dot_add]
        rw [pW3bII_dot_smul, pW3bII_dot_smul, pW3bII_dot_smul, pW3bII_dot_smul]
        rw [pW3bII_dot_zero, pW3bII_dot_cross_left, pW3bII_dot_cross_right]
        ring
      rw [hexp, pW3bII_dot_cross_right, mul_zero, zero_add]
      exact mul_nonneg ht4 hposN.le
    · have hexp : dot3_p9 (cross3_p9 d x.1) y
          = t3 * dot3_p9 (cross3_p9 d x.1) x.2 := by
        rw [hy']
        rw [pW3bII_dot_add, pW3bII_dot_add, pW3bII_dot_add]
        rw [pW3bII_dot_smul, pW3bII_dot_smul, pW3bII_dot_smul, pW3bII_dot_smul]
        rw [pW3bII_dot_zero, pW3bII_dot_cross_left, pW3bII_dot_cross_right]
        ring
      rw [hexp, pW3bII_triple_cyclic d x.1 x.2]
      exact mul_nonneg ht3 hposN.le
  -- 严格符号（两法向量各一次）
  have hρV : rhoNode1_p2 FF v ∈ V := LOCAL_FAN_ITER_RHO_NODE_IN_V hl hv 1
  have hιVv : ivsRhoNode1_p2 FF v ∈ V := LOCAL_FAN_IVS_IN_V hl hv
  have h5 : azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) < Real.pi := by
    have h := CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_p9 hcl v hv
    show interiorAngle1_p2 0 FF v < Real.pi
    rw [h]
    exact haz
  have hcond := CONDITION_INANGLE_CROSS_DOT_p9 (0 : V3) v w
    (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v)
    (pW3bII_base_unfold hl hv hbase) hnc_vw
    (LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hl hv)
    (LOFA_IMP_NOT_COLL_IVS hl hv) h5
  obtain ⟨hA, hB⟩ := hcond
  have hstrictN : 0 < dot3_p9 (cross3_p9 x.1 x.2) v ∨
      0 < dot3_p9 (cross3_p9 x.1 x.2) w :=
    pW3bII_norm_pos (cross3_p9 x.1 x.2) v w (rhoNode1_p2 FF v)
      (ivsRhoNode1_p2 FF v) (pW3bII_cross_ne_zero hcol_x)
      (by simpa using hA) (by simpa using hB)
      (hsigns v hv).1 (hsigns w hw).1 (hsigns (rhoNode1_p2 FF v) hρV).1
      (hsigns (ivsRhoNode1_p2 FF v) hιVv).1
  have hnc_d1 : ¬ Collinear3 (0 : V3) d x.1 := by
    intro hc
    apply hnc1d
    have hset : ({0, x.1, d} : Set V3) = {0, d, x.1} := by
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    simpa [Collinear3, hset] using hc
  have hstrictD : 0 < dot3_p9 (cross3_p9 d x.1) v ∨
      0 < dot3_p9 (cross3_p9 d x.1) w :=
    pW3bII_norm_pos (cross3_p9 d x.1) v w (rhoNode1_p2 FF v)
      (ivsRhoNode1_p2 FF v) (pW3bII_cross_ne_zero hnc_d1)
      (by simpa using hA) (by simpa using hB)
      (hsigns v hv).2 (hsigns w hw).2 (hsigns (rhoNode1_p2 FF v) hρV).2
      (hsigns (ivsRhoNode1_p2 FF v) hιVv).2
  -- 目标：wedge → affGt → 两个 3_1 片
  have hcop_main : ¬ Coplanar ({0, x.1, x.2, d} : Set V3) := by
    have h := pW3b_not_coplanar_of_azim_between hcl hx h0 hlt
    simpa using h
  have hcop1 : ¬ Coplanar ({0, d, x.1, x.2} : Set V3) := by
    intro hc
    apply hcop_main
    have hset : ({0, x.1, x.2, d} : Set V3) = {0, d, x.1, x.2} := by
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset]
  have hposDfin : 0 < (crossProduct ((d - 0 : V3) : Fin 3 → ℝ)
      ((x.1 - 0 : V3) : Fin 3 → ℝ)) ⬝ᵥ ((x.2 - 0 : V3) : Fin 3 → ℝ) := by
    simpa [sub_zero, pW3bII_crossdot_eq] using hposD
  have hposNfin : 0 < (crossProduct ((x.1 - 0 : V3) : Fin 3 → ℝ)
      ((x.2 - 0 : V3) : Fin 3 → ℝ)) ⬝ᵥ ((d - 0 : V3) : Fin 3 → ℝ) := by
    simpa [sub_zero, pW3bII_crossdot_eq] using hposN
  unfold wedgeInFanGt_p2
  rw [if_pos (by rw [pW3bII_card_EE hl hx]; norm_num), pW3bII_azimCycle hl hx]
  rw [show ivsRhoNode1_p2 FF x.1 = d from hddef.symm]
  rw [show Kepler.Text.wedge (0 : V3) x.1 x.2 d
      = Kepler.Geom.wedge (0 : V3) x.1 x.2 d from rfl]
  rw [wedge_eq_affGt (v0 := (0 : V3)) (v1 := x.1) (w1 := x.2) (w2 := d)
    hcol_x hnc1d h0 hlt]
  rw [show ({x.2, d} : Set V3) = {d, x.2} from Set.pair_comm x.2 d]
  rw [← inter_aff_gt_3_1_is_aff_gt_2_2 (x := (0 : V3)) (v := d) (u := x.1)
    (w := x.2) hcop1]
  intro z hz
  constructor
  · rw [aff_gt_3_1_rep_cross_dot (0 : V3) d x.1 x.2 hcop1 hposDfin]
    simp only [Set.mem_setOf_eq, sub_zero]
    rw [← pW3bII_crossdot_eq]
    obtain ⟨a, b, ha0, hb0, hzrep⟩ := pW3bII_decomp hv0 hw0 hvw hnc_vw hz
    have hlin : dot3_p9 (cross3_p9 d x.1) z
        = a * dot3_p9 (cross3_p9 d x.1) v
          + b * dot3_p9 (cross3_p9 d x.1) w := by
      rw [hzrep, pW3bII_dot_add, pW3bII_dot_smul, pW3bII_dot_smul]
    rw [hlin]
    rcases hstrictD with h | h
    · nlinarith [mul_pos ha0 h, mul_nonneg hb0.le (hsigns w hw).2]
    · nlinarith [mul_nonneg ha0.le (hsigns v hv).2, mul_pos hb0 h]
  · rw [aff_gt_3_1_rep_cross_dot (0 : V3) x.1 x.2 d hcop_main hposNfin]
    simp only [Set.mem_setOf_eq, sub_zero]
    rw [← pW3bII_crossdot_eq]
    obtain ⟨a, b, ha0, hb0, hzrep⟩ := pW3bII_decomp hv0 hw0 hvw hnc_vw hz
    have hlin : dot3_p9 (cross3_p9 x.1 x.2) z
        = a * dot3_p9 (cross3_p9 x.1 x.2) v
          + b * dot3_p9 (cross3_p9 x.1 x.2) w := by
      rw [hzrep, pW3bII_dot_add, pW3bII_dot_smul, pW3bII_dot_smul]
    rw [hlin]
    rcases hstrictN with h | h
    · nlinarith [mul_pos ha0 h, mul_nonneg hb0.le (hsigns w hw).1]
    · nlinarith [mul_nonneg ha0.le (hsigns v hv).1, mul_pos hb0 h]

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW3b_affGt_subset_wedge_lt_pi
#print axioms Kepler.Text.pW3b_affGt_subset_wedge_lt_pi
