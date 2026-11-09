/-
LocalAuto7W22dG: W22d — `localization_simple_hypermap` 主体（HOL `local/RNSYJXM-compiled.hl:182-258`）。

HOL 原形：`f ∈ face_set (hypermap_of_fan (V,E)) ∧ 2 ≤ CARD f ∧ simple_hypermap (hypermap_of_fan (V,E))
  ⇒ simple_hypermap (hypermap_of_fan (v_prime V f, e_prime E f))`。

本件 `p22d_locSimple_hypermap`：`p22d_simple_expand`（件 1）之后第 3 段逐点证
`H2.node z ∩ H2.face z = {z}`。两分支（`DARTS_E_PRIME_GT1_SWITCH`：`H2.darts = FF ∪ FFᵀ`）：
* `z ∈ FF`：`nn` 保第一分量（`p22dG_nn_fst_iter`）⇒ 交点落在 `FF` 同一顶点；
  `p22dG_face_start_unique` 用 `H1.Simple` + `CYCLIC_SET_IMP_STABLE_SET2`（σ-轨道 = 邻集）。
* `z ∉ FF`：逆面封闭——`p22dG_rev_step`（`AZIM_CY_FST_Y_IN_FF` 前驱 + 2 元邻集 +
  `BIJ_AZIM_CYCLE_EE` 唯一性），归纳 `p22dG_rev_face_iter`，终点唯一 `p22dG_face_end_unique`。

DIFFERS：HOL `fst_node_hypermap_of_fan` ⇒ 定义展开 `p22dG_nn_fst`；HOL `localization_node_subset`
未用（只需第一分量守恒）。W22dA–F / W22c* / W22b / W22a / W21 / LA2 / LA3 / LA9 / LA10 零改动。
-/
import Kepler.Text.LocalAuto7W22dF

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `IsHypOn_p10` 的 dart 集成员（Set ↔ Finset 桥）。 -/
private theorem p22dG_mem_darts {x : V3} {V : Set V3} {E : Set (Set V3)}
    {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 x V E HS) {d : V3 × V3}
    (hd : d ∈ dartsOfHyp_p3 E V) : d ∈ HS.darts :=
  Finset.mem_coe.mp (by rw [hHS.1]; exact hd)

/-- `nnOfHyp_p3` 保第一分量（HOL `fst_node_hypermap_of_fan` 的定义展开形）。 -/
private theorem p22dG_nn_fst (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    (nnOfHyp_p3 x V E d).1 = d.1 := by
  by_cases hd : d ∈ dartsOfHyp_p3 E V
  · rw [show nnOfHyp_p3 x V E d = if d ∈ dartsOfHyp_p3 E V then
        (d.1, azimCycle_p3 (EE_p3 d.1 E) x d.1 d.2) else d from rfl, if_pos hd]
  · rw [show nnOfHyp_p3 x V E d = if d ∈ dartsOfHyp_p3 E V then
        (d.1, azimCycle_p3 (EE_p3 d.1 E) x d.1 d.2) else d from rfl, if_neg hd]

/-- `nnOfHyp_p3` 的迭代保第一分量。 -/
private theorem p22dG_nn_fst_iter (x : V3) (V : Set V3) (E : Set (Set V3)) :
    ∀ (n : ℕ) (d : V3 × V3), ((nnOfHyp_p3 x V E)^[n] d).1 = d.1 := by
  intro n
  induction n with
  | zero => intro d; rfl
  | succ k ih =>
    intro d
    rw [Function.iterate_succ_apply']
    exact (p22dG_nn_fst x V E ((nnOfHyp_p3 x V E)^[k] d)).trans (ih d)

/-- 超映射的 `node` 成员 = 底层函数迭代（`orbitMap` 的迭代形）。 -/
private theorem p22dG_node_iter {α : Type*} [DecidableEq α] {H : Hypermap α}
    {f : α → α} (hn : (H.nodeMap : α → α) = f) (d y : α) :
    y ∈ H.node d ↔ ∃ n : ℕ, f^[n] d = y := by
  rw [Hypermap.mem_node_iff]
  constructor
  · rintro ⟨n, h⟩
    refine ⟨n, ?_⟩
    rw [← hn]
    exact (congrFun (Equiv.Perm.coe_pow H.nodeMap n) d).symm.trans h.symm
  · rintro ⟨n, h⟩
    refine ⟨n, ?_⟩
    rw [← h, ← hn]
    exact (congrFun (Equiv.Perm.coe_pow H.nodeMap n) d).symm

/-- **面上起点唯一**：`z ∈ FF` 且 `y ∈ FF` 同在第一分量 ⇒ `y = z`
（`H1.Simple` + `σ`-轨道 = 邻集）。 -/
private theorem p22dG_face_start_unique {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {x z : V3 × V3} {FF : Set (V3 × V3)} (hFF : FF = H1.face x)
    (hx : x ∈ dartsOfHyp_p3 E V) (hcard : 1 < FF.ncard) (hsimp : H1.Simple)
    (hz : z ∈ FF) {y : V3 × V3} (hy : y ∈ FF) (hy1 : y.1 = z.1) : y = z := by
  have hxmem : x ∈ H1.darts := p22dG_mem_darts h1 hx
  have hdarts : ∀ d ∈ FF, d ∈ dartsOfHyp_p3 E V := by
    intro d hd
    have h : d ∈ (↑H1.darts : Set (V3 × V3)) :=
      H1.face_subset_darts hxmem (by rw [← hFF]; exact hd)
    rwa [h1.1] at h
  have hzface : H1.face z = FF := by
    rw [hFF]
    exact (H1.face_eq_of_mem (hFF ▸ hz)).symm
  have hedge : ∀ d ∈ FF, ({d.1, d.2} : Set V3) ∈ E :=
    CARD_FF_GT1_FF_SUBSET hfan h1 hFF hcard
  have hzEE : z.2 ∈ EE_p3 z.1 E := (IN_EE_IFF_IN_E z.1 z.2).mpr (hedge z hz)
  have hyEE : y.2 ∈ EE_p3 z.1 E := by
    rw [← hy1]
    exact (IN_EE_IFF_IN_E y.1 y.2).mpr (hedge y hy)
  have hstable := CYCLIC_SET_IMP_STABLE_SET2 hfan (hedge z hz) z.2 hzEE
  obtain ⟨n, hn⟩ : ∃ n : ℕ, y.2 = (azimCycle_p3 (EE_p3 z.1 E) 0 z.1)^[n] z.2 := by
    rw [hstable] at hyEE
    exact hyEE
  have hnn : (nnOfHyp_p3 0 V E)^[n] z = (z.1, y.2) := by
    have hN := N_HYP_TO_AZIM_CYCLE_LEM hfan (u := z.1) (v := z.2) (hdarts z hz) n
    simpa [hn] using hN
  have hy_eq : y = (z.1, y.2) := by rw [← hy1]
  have hnode : y ∈ H1.node z := by
    rw [p22dG_node_iter (H := H1) (f := nnOfHyp_p3 0 V E) h1.2.2.1 z y]
    exact ⟨n, hnn.trans hy_eq.symm⟩
  have hsingle := hsimp z (p22dG_mem_darts h1 (hdarts z hz))
  have hmem : y ∈ H1.node z ∩ H1.face z := ⟨hnode, by rw [hzface]; exact hy⟩
  rw [hsingle] at hmem
  exact Set.mem_singleton_iff.mp hmem

/-- **面上终点唯一**：`(u,w) ∈ FF` 且 `y ∈ FF` 同一第二分量 ⇒ `y = (u,w)`。
（`H1.faceMap` 把两条同终点 dart 送到同一始点，再用起点唯一 + 单射。） -/
private theorem p22dG_face_end_unique {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {x : V3 × V3} {FF : Set (V3 × V3)} (hFF : FF = H1.face x)
    (hx : x ∈ dartsOfHyp_p3 E V) (hcard : 1 < FF.ncard) (hsimp : H1.Simple)
    {u w : V3} (huw : (u, w) ∈ FF) {y : V3 × V3} (hy : y ∈ FF) (hy2 : y.2 = w) :
    y = (u, w) := by
  have hxmem : x ∈ H1.darts := p22dG_mem_darts h1 hx
  have hdarts : ∀ d ∈ FF, d ∈ dartsOfHyp_p3 E V := by
    intro d hd
    have h : d ∈ (↑H1.darts : Set (V3 × V3)) :=
      H1.face_subset_darts hxmem (by rw [← hFF]; exact hd)
    rwa [h1.1] at h
  have hface_ref : H1.face (u, w) = FF := by
    rw [hFF]
    exact (H1.face_eq_of_mem (hFF ▸ huw)).symm
  have hface_y : H1.face y = FF := by
    rw [hFF]
    exact (H1.face_eq_of_mem (hFF ▸ hy)).symm
  have himg_ref : (H1.faceMap : V3 × V3 → V3 × V3) (u, w) ∈ FF := by
    have hm : (H1.faceMap : V3 × V3 → V3 × V3) (u, w) ∈ H1.face (u, w) := by
      simpa using H1.pow_faceMap_mem_face (u, w) 1
    rwa [hface_ref] at hm
  have himg_y : (H1.faceMap : V3 × V3 → V3 × V3) y ∈ FF := by
    have hm : (H1.faceMap : V3 × V3 → V3 × V3) y ∈ H1.face y := by
      simpa using H1.pow_faceMap_mem_face y 1
    rwa [hface_y] at hm
  have hfst_ref : ((H1.faceMap : V3 × V3 → V3 × V3) (u, w)).1 = w := by
    rw [h1.2.2.2]
    rw [show ffOfHyp_p3 0 V E (u, w) =
      if (u, w) ∈ dartsOfHyp_p3 E V then
        ((u, w).2, ivsAzimCycle_p3 (EE_p3 (u, w).2 E) 0 (u, w).2 (u, w).1)
      else (u, w) from rfl, if_pos (hdarts (u, w) huw)]
  have hfst_y : ((H1.faceMap : V3 × V3 → V3 × V3) y).1 = y.2 := by
    rw [h1.2.2.2]
    rw [show ffOfHyp_p3 0 V E y =
      if y ∈ dartsOfHyp_p3 E V then
        (y.2, ivsAzimCycle_p3 (EE_p3 y.2 E) 0 y.2 y.1) else y
      from rfl, if_pos (hdarts y hy)]
  have heq := p22dG_face_start_unique hfan h1 hFF hx hcard hsimp himg_ref himg_y
    (by rw [hfst_y, hfst_ref, hy2])
  exact H1.faceMap.injective heq

/-- **逆面一步**：`(u,w) ∈ FF` ⇒ `(ivs (EE' u) 0 u w, u) ∈ FF`
（HOL `RNSYJXM:228-247` 的核心：逆面在 `FFᵀ` 内封闭的一步）。 -/
private theorem p22dG_rev_step {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {x : V3 × V3} {FF : Set (V3 × V3)} (hFF : FF = H1.face x)
    (hx : x ∈ dartsOfHyp_p3 E V) (hcard : 1 < FF.ncard) (hsimp : H1.Simple)
    {u w : V3} (huw : (u, w) ∈ FF) :
    (ivsAzimCycle_p3 (EE_p3 u (ePrime_p3 E FF)) 0 u w, u) ∈ FF := by
  have hfan' : FAN 0 (vPrime_p3 V FF) (ePrime_p3 E FF) :=
    IMP_FAN_V_PRIME_E_PRIME hfan
      ⟨H1, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, x, p22dG_mem_darts h1 hx, hFF⟩
  have hedge : ∀ d ∈ FF, ({d.1, d.2} : Set V3) ∈ E :=
    CARD_FF_GT1_FF_SUBSET hfan h1 hFF hcard
  have hξFF : (azimCycle_p3 (EE_p3 u E) 0 u w, u) ∈ FF :=
    (AZIM_CY_FST_Y_IN_FF hfan h1 hx hFF huw).1
  have hwE' : w ∈ EE_p3 u (ePrime_p3 E FF) :=
    (IN_EE_IFF_IN_E u w).mpr ⟨u, w, rfl, hedge (u, w) huw, huw⟩
  have hξE' : azimCycle_p3 (EE_p3 u E) 0 u w ∈ EE_p3 u (ePrime_p3 E FF) := by
    refine (IN_EE_IFF_IN_E u _).mpr
      ⟨azimCycle_p3 (EE_p3 u E) 0 u w, u, ?_, hedge _ hξFF, hξFF⟩
    exact Set.pair_comm u (azimCycle_p3 (EE_p3 u E) 0 u w)
  have hEEsub : EE_p3 u (ePrime_p3 E FF) ⊆
      ({w, azimCycle_p3 (EE_p3 u E) 0 u w} : Set V3) := by
    intro a ha
    obtain ⟨p, q, hpq, hEpq, hpqFF⟩ := (IN_EE_IFF_IN_E u a).mp ha
    rcases Set.pair_eq_pair_iff.mp hpq with h | h
    · -- `(u,a) ∈ FF`：起点与 `(u,w)` 相同
      have hFF' : (u, a) ∈ FF := by
        rw [← h.1, ← h.2] at hpqFF
        exact hpqFF
      have haw : a = w := by
        have hwa := p22dG_face_start_unique hfan h1 hFF hx hcard hsimp huw hFF' rfl
        exact congrArg Prod.snd hwa
      rw [Set.mem_insert_iff]
      exact Or.inl haw
    · -- `(a,u) ∈ FF`：终点与 `(ξ0,u)` 相同
      have hFF' : (a, u) ∈ FF := by
        rw [← h.2, ← h.1] at hpqFF
        exact hpqFF
      have hξa : azimCycle_p3 (EE_p3 u E) 0 u w = a := by
        have hpa := p22dG_face_end_unique hfan h1 hFF hx hcard hsimp hξFF hFF' rfl
        exact (congrArg Prod.fst hpa).symm
      rw [Set.mem_insert_iff]
      exact Or.inr (Set.mem_singleton_iff.mpr hξa.symm)
  have hEEeq : EE_p3 u (ePrime_p3 E FF) =
      ({w, azimCycle_p3 (EE_p3 u E) 0 u w} : Set V3) := by
    refine Set.Subset.antisymm hEEsub ?_
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hwE'
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hξE'
  have hξcycle : azimCycle_p3 (EE_p3 u (ePrime_p3 E FF)) 0 u
      (azimCycle_p3 (EE_p3 u E) 0 u w) = w := by
    by_cases hsub : EE_p3 u (ePrime_p3 E FF) ⊆ {azimCycle_p3 (EE_p3 u E) 0 u w}
    · rw [W_SUBSET_SINGLETON_IMP_IDE hsub]
      exact (Set.mem_singleton_iff.mp (hsub hwE')).symm
    · have hfin : (EE_p3 u (ePrime_p3 E FF)).Finite := by
        rw [hEEeq]
        exact (Set.finite_singleton _).insert _
      have hp := AZIM_CYCLE_PROPERTIES hsub hfin 0 u
      rw [hEEeq] at hp ⊢
      rcases Set.mem_insert_iff.mp hp.2.1 with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hp.1
  have hivs : ivsAzimCycle_p3 (EE_p3 u (ePrime_p3 E FF)) 0 u w =
      azimCycle_p3 (EE_p3 u E) 0 u w := by
    have hprop := PROPERTIES_OF_IVS_AZIM_CYCLE2 hfan' hwE'
    exact (BIJ_AZIM_CYCLE_EE hfan' u).1 hprop.1 hξE' (hprop.2.trans hξcycle.symm)
  rw [hivs]
  exact hξFF

/-- **逆面封闭**：`(z.2,z.1) ∈ FF` ⇒ 局部化面轨道的每一步都保持同一逆关系。 -/
private theorem p22dG_rev_face_iter {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {x : V3 × V3} {FF : Set (V3 × V3)} (hFF : FF = H1.face x)
    (hx : x ∈ dartsOfHyp_p3 E V) (hcard : 1 < FF.ncard) (hsimp : H1.Simple)
    {H2 : Hypermap (V3 × V3)}
    (h2 : IsHypOn_p10 0 (vPrime_p3 V FF) (ePrime_p3 E FF) H2)
    {z : V3 × V3} (hzrev : (z.2, z.1) ∈ FF) :
    ∀ n : ℕ, (((H2.faceMap ^ n) z).2, ((H2.faceMap ^ n) z).1) ∈ FF := by
  intro n
  induction n with
  | zero => simpa using hzrev
  | succ k ih =>
    have hdval : (H2.faceMap : V3 × V3 → V3 × V3) ((H2.faceMap ^ k) z) =
        ffOfHyp_p3 0 (vPrime_p3 V FF) (ePrime_p3 E FF) ((H2.faceMap ^ k) z) := by
      rw [h2.2.2.2]
    rw [pow_succ', Equiv.Perm.mul_apply, hdval]
    by_cases hd : ((H2.faceMap ^ k) z) ∈
        dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF)
    · rw [show ffOfHyp_p3 0 (vPrime_p3 V FF) (ePrime_p3 E FF) ((H2.faceMap ^ k) z) =
        if ((H2.faceMap ^ k) z) ∈
            dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) then
          (((H2.faceMap ^ k) z).2, ivsAzimCycle_p3
            (EE_p3 ((H2.faceMap ^ k) z).2 (ePrime_p3 E FF)) 0
            ((H2.faceMap ^ k) z).2 ((H2.faceMap ^ k) z).1)
        else ((H2.faceMap ^ k) z) from rfl, if_pos hd]
      exact p22dG_rev_step hfan h1 hFF hx hcard hsimp ih
    · rw [show ffOfHyp_p3 0 (vPrime_p3 V FF) (ePrime_p3 E FF) ((H2.faceMap ^ k) z) =
        if ((H2.faceMap ^ k) z) ∈
            dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) then
          (((H2.faceMap ^ k) z).2, ivsAzimCycle_p3
            (EE_p3 ((H2.faceMap ^ k) z).2 (ePrime_p3 E FF)) 0
            ((H2.faceMap ^ k) z).2 ((H2.faceMap ^ k) z).1)
        else ((H2.faceMap ^ k) z) from rfl, if_neg hd]
      exact ih

/-- **`localization_simple_hypermap` 主体**（HOL `local/RNSYJXM-compiled.hl:182-258`）：
局部化超映射保持 `Simple`。 -/
theorem p22d_locSimple_hypermap {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) {FF : Set (V3 × V3)}
    (hFF : FF = H1.face x) {H2 : Hypermap (V3 × V3)}
    (h2 : IsHypOn_p10 0 (vPrime_p3 V FF) (ePrime_p3 E FF) H2)
    (hcard : 2 ≤ FF.ncard) (hsimp : H1.Simple) : H2.Simple := by
  have hgt1 : 1 < FF.ncard := by omega
  have hffx : FF = H2.face x := (LVDUCXU hfan h1 hx hFF h2).1
  have hdarts' : dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) =
      FF ∪ {p : V3 × V3 | (p.2, p.1) ∈ FF} :=
    DARTS_E_PRIME_GT1_SWITCH hfan h1 hFF hgt1
  intro z hz
  have hzS : z ∈ (↑H2.darts : Set (V3 × V3)) := hz
  rw [h2.1, hdarts'] at hzS
  ext y
  constructor
  · intro hy
    rw [Set.mem_inter_iff] at hy
    obtain ⟨hyn, hyf⟩ := hy
    have hy1 : y.1 = z.1 := by
      rw [p22dG_node_iter (H := H2)
        (f := nnOfHyp_p3 0 (vPrime_p3 V FF) (ePrime_p3 E FF)) h2.2.2.1 z y] at hyn
      obtain ⟨n, hn⟩ := hyn
      rw [← hn]
      exact p22dG_nn_fst_iter 0 (vPrime_p3 V FF) (ePrime_p3 E FF) n z
    rcases (Set.mem_union _ _ _).mp hzS with hzFF | hzT
    · -- `z ∈ FF`：局部化面 = `FF`，起点唯一
      have hzfx : z ∈ H2.face x := by rw [← hffx]; exact hzFF
      have hfacez : H2.face z = FF := by
        rw [hffx]
        exact (H2.face_eq_of_mem hzfx).symm
      have hyFF : y ∈ FF := by rw [← hfacez]; exact hyf
      exact Set.mem_singleton_iff.mpr
        (p22dG_face_start_unique hfan h1 hFF hx hgt1 hsimp hzFF hyFF hy1)
    · -- `z ∉ FF`（故 `(z.2,z.1) ∈ FF`）：逆面封闭 + 终点唯一
      rw [Hypermap.face] at hyf
      obtain ⟨n, hn⟩ := hyf
      have hyrev : (y.2, y.1) ∈ FF := by
        rw [← hn]
        exact p22dG_rev_face_iter hfan h1 hFF hx hgt1 hsimp h2 hzT n
      have hyz : y = z := by
        have hp := p22dG_face_end_unique hfan h1 hFF hx hgt1 hsimp hzT hyrev hy1
        exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)
      exact Set.mem_singleton_iff.mpr hyz
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact ⟨H2.mem_node_self z, H2.mem_face_self z⟩

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22d_locSimple_hypermap

end Kepler.Text
