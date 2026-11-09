/-
LocalAuto7W12B: W12(b1) — WSEWPCH straight 支的 `V' = V ∖ {v}` 结构层
（HOL polar_fan.hl:2649-2698），含首个消费点
`p12a_straight_aff_ge` 对 `(u, v, w) = (ιv, v, ρv)` 的实例化。

HOL straight 支（2648 起）：取内角 = π 的点 `v`，
`V' = V DIFF {v}`、`r u = if ρu = v then ρv else ρu`、
`E' = {{w, r w} | w ∈ V'}`、`FF' = {(w, r w) | w ∈ V'}`。
本文件只做**结构层**（定义 + 5 条基本事实 + straight 点落 `affGe {0}{ιv,ρv}`）；
`(V',E',FF')` 的 `FAN`/`localFan`/`ConvexLocalFan`/`Generic` 传递与 perimeter
拆分分别留给 W12(b2)/W12(c)（规模见交付 DELIVERY）。

件表：
* `p12b_V` / `p12b_R` / `p12b_E` / `p12b_FF`（defs）；
* `p12b_R_mem`（`r w ∈ V'`）/ `p12b_R_inj`（`r` 在 `V'` 上单射）/
  `p12b_R_ne`（`r w ≠ w`）/ `p12b_rho_FF`（`ρ_{FF'} w = r w`）/
  `p12b_card`（`V'` 有限且 `CARD V' + 1 = CARD V`）/ `p12b_card_lt`；
* **`p12b_straight_mem`**：`v ∈ affGe {0} {ιv, ρv}`（消费 `p12a_straight_aff_ge`）。
-/
import Kepler.Text.LocalAuto7W12A

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## 定义（HOL 2649-2653） -/

/-- `V' = V DIFF {v}`（straight 支删点集）。 -/
def p12b_V (V : Set V3) (v : V3) : Set V3 := V \ {v}

/-- `r u = if ρu = v then ρv else ρu`（straight 支改写的 rho）。 -/
noncomputable def p12b_R (FF : Set (V3 × V3)) (v u : V3) : V3 :=
  if rhoNode1 FF u = v then rhoNode1 FF v else rhoNode1 FF u

/-- `E' = {{w, r w} | w ∈ V'}`。 -/
noncomputable def p12b_E (V : Set V3) (FF : Set (V3 × V3)) (v : V3) : Set (Set V3) :=
  {e | ∃ w ∈ p12b_V V v, e = {w, p12b_R FF v w}}

/-- `FF' = {(w, r w) | w ∈ V'}`。 -/
noncomputable def p12b_FF (V : Set V3) (FF : Set (V3 × V3)) (v : V3) : Set (V3 × V3) :=
  {d | ∃ w ∈ p12b_V V v, d = (w, p12b_R FF v w)}

/-! ## 基本事实（HOL 2654-2698） -/

/-- epsilon 唯一性坍塌（LA7 `w6a_epsilon_fixed` 的本地副本；LA7 私件不可跨模块）。 -/
private theorem p12b_epsilon_fixed {α : Type*} [Nonempty α] {p : α → Prop} {a : α}
    (hpa : p a) (huniq : ∀ y, p y → y = a) : Classical.epsilon p = a := by
  by_contra hne
  exact hne (huniq _ (Classical.epsilon_spec ⟨a, hpa⟩))

/-- `v ≠ ρv`（非共线 `{0,v,ρv}` 的退化推论）。 -/
private theorem p12b_v_ne_rho {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
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

/-- `r w ∈ V'`（HOL 2654-2660）。 -/
theorem p12b_R_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {u : V3} (hu : u ∈ p12b_V V v) :
    p12b_R FF v u ∈ p12b_V V v := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have huV : u ∈ V := hu.1
  have hvne : v ≠ rhoNode1 FF v := p12b_v_ne_rho h2 hv
  have hρV : rhoNode1 FF u ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 huV
  have hρvV : rhoNode1 FF v ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 hv
  unfold p12b_R p12b_V
  by_cases hcase : rhoNode1 FF u = v
  · rw [if_pos hcase]
    exact ⟨hρvV, hvne.symm⟩
  · rw [if_neg hcase]
    exact ⟨hρV, by simpa using hcase⟩

/-- `r` 在 `V'` 上单射（HOL 2661-2670）。 -/
theorem p12b_R_inj {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v x y : V3} (hv : v ∈ V) (hx : x ∈ p12b_V V v) (hy : y ∈ p12b_V V v)
    (heq : p12b_R FF v x = p12b_R FF v y) : x = y := by
  have hxV : x ∈ V := hx.1
  have hyV : y ∈ V := hy.1
  unfold p12b_R at heq
  by_cases hx1 : rhoNode1 FF x = v
  · by_cases hy1 : rhoNode1 FF y = v
    · rw [if_pos hx1, if_pos hy1] at heq
      exact (RHO_NODE1_INJECTIVE hcl.1 hedge x hxV y hyV).mp (by rw [hx1, hy1])
    · rw [if_pos hx1, if_neg hy1] at heq
      have hyv : y = v := (RHO_NODE1_INJECTIVE hcl.1 hedge y hyV v hv).mp heq.symm
      exact absurd hyv (by simpa using hy.2)
  · by_cases hy1 : rhoNode1 FF y = v
    · rw [if_neg hx1, if_pos hy1] at heq
      have hxv : x = v := (RHO_NODE1_INJECTIVE hcl.1 hedge x hxV v hv).mp heq
      exact absurd hxv (by simpa using hx.2)
    · rw [if_neg hx1, if_neg hy1] at heq
      exact (RHO_NODE1_INJECTIVE hcl.1 hedge x hxV y hyV).mp heq

/-- `r w ≠ w`（HOL 2671-2681）。 -/
theorem p12b_R_ne {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v) :
    p12b_R FF v w ≠ w := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hwV : w ∈ V := hw.1
  have hnsv : rhoNode1 FF (rhoNode1 FF v) ≠ v := LOCAL_FAN_IMP_NOT_SEMI_IDE h2 hv
  have hnsw : rhoNode1 FF (rhoNode1 FF w) ≠ w := LOCAL_FAN_IMP_NOT_SEMI_IDE h2 hwV
  unfold p12b_R
  by_cases hcase : rhoNode1 FF w = v
  · rw [if_pos hcase]
    intro heq
    exact hnsv (by rw [heq]; exact hcase)
  · rw [if_neg hcase]
    intro heq
    exact hnsw (by rw [heq, heq])

/-- `ρ_{FF'} w = r w`（HOL 2682-2688；epsilon 唯一性）。 -/
theorem p12b_rho_FF {V : Set V3} {FF : Set (V3 × V3)} {v w : V3}
    (hw : w ∈ p12b_V V v) :
    rhoNode1 (p12b_FF V FF v) w = p12b_R FF v w := by
  have hmem : (w, p12b_R FF v w) ∈ p12b_FF V FF v := ⟨w, hw, rfl⟩
  refine p12b_epsilon_fixed hmem ?_
  intro y hy
  obtain ⟨u, -, hud⟩ := hy
  have hu1 : w = u := congrArg Prod.fst hud
  have hu2 : y = p12b_R FF v u := by simpa using congrArg Prod.snd hud
  rw [← hu1] at hu2
  exact hu2

/-- `V'` 有限且 `CARD V' + 1 = CARD V`（HOL 2689-2699）。 -/
theorem p12b_card {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) {v : V3} (hv : v ∈ V) :
    (p12b_V V v).Finite ∧ (p12b_V V v).ncard + 1 = V.ncard := by
  have hfin : V.Finite := (hcl.1.1).2.2.1.1
  have hfin' : (p12b_V V v).Finite := hfin.sdiff
  refine ⟨hfin', ?_⟩
  show (V \ {v}).ncard + 1 = V.ncard
  exact Set.ncard_sdiff_singleton_add_one hv hfin

/-- `CARD V' < CARD V`（HOL 2700-2702）。 -/
theorem p12b_card_lt {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) {v : V3} (hv : v ∈ V) :
    (p12b_V V v).ncard < V.ncard := by
  have h := (p12b_card hcl hv).2
  omega

/-- `V' ⊆ V`。 -/
theorem p12b_V_subset (V : Set V3) (v : V3) : p12b_V V v ⊆ V :=
  fun _ h => h.1

/-! ## straight 点落 `affGe {0}{ιv, ρv}`（HOL 2703-2710，消费 W12(a) 主件） -/

/-- **`v ∈ affGe {0} {ιv, ρv}`**：`p12a_straight_aff_ge` 的实例化
（`azim 0 v ρv ιv = π` 由 `interiorAngle1 0 FF v = π` 直接给出，两者同体；
`hdis` 由 `Generic V E` 在边 `{v,ρv}`、点 `ιv` 处实例化）。 -/
theorem p12b_straight_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) :
    v ∈ affGe ({0} : Set V3) ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hιV : ivsRhoNode1 FF v ∈ V := IVS_RHO_NODE1_IN_V hcl.1 hedge v hv
  have hnc1 : ¬ Collinear3 (0:V3) v (ivsRhoNode1 FF v) := LOFA_IMP_NOT_COLL_IVS h2 hv
  have hnc2 : ¬ Collinear3 (0:V3) v (rhoNode1 FF v) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hv
  have haz : azim 0 v (rhoNode1 FF v) (ivsRhoNode1 FF v) = Real.pi := hpi
  have hdart : (v, rhoNode1 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS h2).1 v hv
  have he : ({v, rhoNode1 FF v} : Set V3) ∈ E :=
    (LOCAL_FAN_IN_FF_IN_ORD_PAIRS2 h2 hdart hdart).1
  have hdis : affGe ({0} : Set V3) ({v, rhoNode1 FF v} : Set V3) ∩
      affLt ({0} : Set V3) ({ivsRhoNode1 FF v} : Set V3) = ∅ :=
    hg v (rhoNode1 FF v) (ivsRhoNode1 FF v) he hιV
  exact p12a_straight_aff_ge hnc1 hnc2 haz hdis

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12b_R_mem
#print axioms Kepler.Text.p12b_R_inj
#print axioms Kepler.Text.p12b_R_ne
#print axioms Kepler.Text.p12b_rho_FF
#print axioms Kepler.Text.p12b_card
#print axioms Kepler.Text.p12b_card_lt
#print axioms Kepler.Text.p12b_V_subset
#print axioms Kepler.Text.p12b_straight_mem

end Kepler.Text
