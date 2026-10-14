/-
  Kepler.Text.TameSpine.TameList15 — B1 Tame_list 地基批 15：Hypermap_iso 桥章 +
  iso 章余件（tamespine-port-plan §4 批次表 B1 行；接续批 14 = TameList14.lean，
  批 14 终点 = HOL :9275，本批起点 = Hypermap_iso 桥章 + HOL :9276
  iso_is_no_double_joins）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353）：

  桥章（text_formalization/fan/hypermap_iso.vhl）：
  `hyp_iso_dart` :418 / `hyp_iso_edge_node` :394（Iff）/ `hyp_iso_card_components`
  :471 / `components_iso_image`（formal_lp/hypermap/ineqs/lp_gen_theory.vhl，
  经 hypermap_iso.vhl `iso_components` :461 同构折算）。桥件取 `Hypermap.Iso`
  解包形（显式 f + BijOn + 三映射交换 = HOL `hyp_iso f (K,H)` 定义体的逐字段
  镜像；f 由存在封装即 `K.Iso H`，下游 `obtain ⟨f, hbij, hmaps⟩` 后直引）。

  iso 章（text_formalization/tame/tame_list.hl）：
  `iso_is_no_double_joins` :9276 / `iso_card_face` :9304 /
  `hyp_iso_restricted` :9319。

  诚实记账（本批跳过/合并/短路线）：
  - 桥章 Lean 化判定：HOL `hyp_iso_edge_face`/`hyp_iso_edge_node` 是
    "三映射交换 ↔ 双映射交换" 的 Iff，其逆向在 HOL 经 inverse2_hypermap_maps +
    hypermap_cyclic 重造第三映射；Lean 侧 `Hypermap.faceMap_eq_inv`
    （Hypermap.lean:830，= comp_eq_one 的逆元变形）已把该恒等式收为现成件，
    逆向一步共轭反演即得（零收窄）。
  - `components_iso_image`（Lp_gen_theory 版只含 node/face 两分量）按
    `iso_components` 的同构证明折算：轨道像运输（§0 私件 orbitImageOfMem =
    批 5 nodeLiftImage 的泛化：conjPowMem 共轭幂引擎 + 双包含各只需正向
    交换，双射性不进轨道像论证）。
  - `hyp_iso_card_components` 的 HOL CARD_IMAGE_INJ + EDGE/FACE/NODE_FINITE
    前置在 Lean 侧合并为 `Set.InjOn.ncard_image`（ncard 自带有限性记账）。
  - `hyp_iso_restricted`（tame_list.hl:9319）装配所需的全部分量
    （darts≠∅ / planar / plain / connected / simple / no_double_joins /
    edge_nondegenerate / node_nondegenerate / card_face≥3 九合取的
    iso-不变性）在本文件 §2/§3 全量落地：其中 planar/connected 经
    iso_path_imp/iso_path_inv（hypermap_iso.vhl :587/:597）→ comb_component
    运输（:631）→ set_of_components/四轨道族像-基数运输（:643-:689）链，
    HOL 同构。
  - 批 14 短路线范式（Iso 字段点态反证）逐枚适用性判定：
    * `iso_is_node_nondegenerate`（批 14 已落，点态短路线 ✓ 原样沿用）；
    * `iso_edge_nondegenerate`（hypermap_iso.vhl:552）——同样点态形，
      短路线 ✓（三交换第 1 分量两步反证）；
    * `iso_is_no_double_joins`（:9276）——点态 + 一次轨道像运输，短路线 ✓
      （HOL 的 hyp_iso_edge_node 绕行步在 Lean 冗余：Iso 三交换直接可用）；
    * `iso_card_face`（:9304）——结论是 ncard 数值不等式，无点态形可走，
      必须经 hyp_iso_card_components（HOL 同构，短路线 ✗ 如实走桥）；
    * `hyp_iso_restricted`（:9319）——九合取装配，其中 plain 的 HOL 证明
      用 h_map_outside（集合外恒等）+ 双射收口：Lean `PermutesOn` 定义
      即含集合外恒等，HOL 同构；其余合取走对应分量件（短路线不适用处
      如实走 §2/§3 运输链）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 16 接续点：HOL :9359 `iso_restricted`（Iff 版，经 Iso.symm
  两向折算，本批 §4 已给出单向 hypIsoRestricted，Iff 装配 ~10 行）及其后
  quotient_list 章（tame_list.hl :9380 起，前置 quotient_hypermap 机制）。
-/

import Kepler.Text.TameSpine.TameList14

namespace Kepler.Text.TameSpine

/-! ### §0 桥章私有引擎（共轭幂提升 + 轨道像运输） -/

/-- 共轭幂提升：`q ∘ g = g ∘ p` 在 dart 集上 ⇒ 幂亦共轭（批 5 私件
nodeMapPowLift 的泛化引擎，private 不跨文件可见）。 -/
private theorem conjPowMem {α β : Type*} {p : Equiv.Perm α} {q : Equiv.Perm β}
    {g : α → β} {s : Finset α} (hp : PermutesOn p s)
    (hcomm : ∀ z ∈ s, q (g z) = g (p z)) (n : ℕ) :
    ∀ z ∈ s, (q ^ n) (g z) = g ((p ^ n) z) := by
  induction n with
  | zero => intro z _; rfl
  | succ k ih =>
    intro z hz
    have hzD : (p ^ k) z ∈ s := hp.pow_apply_mem k hz
    have e1 : (q ^ (k + 1)) (g z) = q ((q ^ k) (g z)) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have e2 : (p ^ (k + 1)) z = p ((p ^ k) z) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [e1, ih z hz, hcomm _ hzD, e2]

/-- 轨道像运输：`q ∘ g = g ∘ p` 在 dart 集上 ⇒ `g` 把 `p`-轨道送到 `q`-轨道
（`iso_components` 的引擎；双包含各只需正向交换，双射性不进论证）。 -/
private theorem orbitImageOfMem {α β : Type*} [DecidableEq α] [DecidableEq β]
    {p : Equiv.Perm α} {q : Equiv.Perm β} {g : α → β} {s : Finset α}
    (hp : PermutesOn p s) (hcomm : ∀ z ∈ s, q (g z) = g (p z)) {z : α}
    (hz : z ∈ s) : orbitMap q (g z) = g '' orbitMap p z := by
  have hpow := conjPowMem hp hcomm
  ext y
  simp only [orbitMap, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨(p ^ n) z, ⟨n, rfl⟩, (hpow n z hz).symm⟩
  · rintro ⟨w, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, hpow n z hz⟩

/-! ### §0 桥章记法与公开件（hypermap_iso.vhl / lp_gen_theory.vhl） -/

/-- HOL `hyp_iso` 定义体第二合取的具名镜像：三映射交换组（供下游以显式
假设组消费；`Hypermap.Iso` 封装存在量词后与之同体）。 -/
def IsoCommutes {α β : Type*} [DecidableEq α] [DecidableEq β]
    (K : Hypermap α) (f : α → β) (H : Hypermap β) : Prop :=
  ∀ x ∈ K.darts, H.edgeMap (f x) = f (K.edgeMap x) ∧
    H.nodeMap (f x) = f (K.nodeMap x) ∧ H.faceMap (f x) = f (K.faceMap x)

/-- `K.Iso H` = 显式 f 形（解包桥；两向按定义体逐字段搬运，零收窄）。 -/
theorem iso_iff_exists_commutes {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} :
    K.Iso H ↔ ∃ f : α → β, Set.BijOn f (↑K.darts) (↑H.darts) ∧ IsoCommutes K f H :=
  ⟨fun h => match h with
    | ⟨f, hb, hm⟩ => ⟨f, hb, hm⟩,
    fun h => match h with
    | ⟨f, hb, hm⟩ => ⟨f, hb, hm⟩⟩

/-- **HOL `hyp_iso_dart`**（hypermap_iso.vhl:418）
`x IN dart K ==> f x IN dart H`（= BijOn 的 mapsTo 分量）。 -/
theorem hypIsoDart {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} {f : α → β}
    (hbij : Set.BijOn f (↑K.darts) (↑H.darts)) {x : α} (hx : x ∈ K.darts) :
    f x ∈ H.darts := hbij.mapsTo hx

/-- **HOL `hyp_iso_inj`**（hypermap_iso.vhl:413）
dart 集上 `f x = f y ⇒ x = y`（= BijOn 的 injOn 分量）。 -/
theorem hypIsoInj {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} {f : α → β}
    (hbij : Set.BijOn f (↑K.darts) (↑H.darts)) : Set.InjOn f (↑K.darts) :=
  hbij.injOn

/-- **HOL `hyp_iso_surj`**（hypermap_iso.vhl:416）
`y IN dart H ==> ?x. x IN dart K /\ f x = y`（= BijOn 的 surjOn 分量）。 -/
theorem hypIsoSurj {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} {f : α → β}
    (hbij : Set.BijOn f (↑K.darts) (↑H.darts)) {y : β} (hy : y ∈ H.darts) :
    ∃ x ∈ K.darts, f x = y := hbij.surjOn hy

/-- **HOL `hyp_iso_edge_node`**（hypermap_iso.vhl:394，Iff）
`hyp_iso f (K,H) <=> BIJ f (dart K) (dart H) /\ (!x. x IN dart K ==>
edge_map H (f x) = f (edge_map K x) /\ node_map H (f x) = f (node_map K x))`
——逆向经 `Hypermap.faceMap_eq_inv`（= comp_eq_one 的逆元变形）共轭反演
重造 face 交换（HOL 的 inverse2_hypermap_maps + hypermap_cyclic 同构）。 -/
theorem hypIsoEdgeNode {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} {f : α → β} :
    (Set.BijOn f (↑K.darts) (↑H.darts) ∧
        ∀ x ∈ K.darts, H.edgeMap (f x) = f (K.edgeMap x) ∧
          H.nodeMap (f x) = f (K.nodeMap x)) ↔
      (Set.BijOn f (↑K.darts) (↑H.darts) ∧
        ∀ x ∈ K.darts, H.edgeMap (f x) = f (K.edgeMap x) ∧
          H.nodeMap (f x) = f (K.nodeMap x) ∧ H.faceMap (f x) = f (K.faceMap x)) := by
  constructor
  · rintro ⟨hbij, hmaps⟩
    refine ⟨hbij, fun x hx => ?_⟩
    have hfaceK : K.faceMap = (K.edgeMap * K.nodeMap).symm := K.faceMap_eq_inv
    have hfaceH : H.faceMap = (H.edgeMap * H.nodeMap).symm := H.faceMap_eq_inv
    have hPinv : ((K.edgeMap * K.nodeMap).symm) x ∈ K.darts := by
      rw [← hfaceK]; exact K.faceMap_apply_mem hx
    have hkey : (H.edgeMap * H.nodeMap) (f ((K.edgeMap * K.nodeMap).symm x))
        = f x := by
      show H.edgeMap (H.nodeMap (f ((K.edgeMap * K.nodeMap).symm x))) = f x
      rw [(hmaps ((K.edgeMap * K.nodeMap).symm x) hPinv).2]
      rw [(hmaps (K.nodeMap ((K.edgeMap * K.nodeMap).symm x))
        (K.nodeMap_apply_mem hPinv)).1]
      show f ((K.edgeMap * K.nodeMap) ((K.edgeMap * K.nodeMap).symm x)) = f x
      rw [Equiv.apply_symm_apply]
    refine ⟨(hmaps x hx).1, (hmaps x hx).2, ?_⟩
    show H.faceMap (f x) = f (K.faceMap x)
    rw [hfaceH, hfaceK]
    refine Equiv.injective (H.edgeMap * H.nodeMap) ?_
    show (H.edgeMap * H.nodeMap) ((H.edgeMap * H.nodeMap).symm (f x))
      = (H.edgeMap * H.nodeMap) (f ((K.edgeMap * K.nodeMap).symm x))
    rw [Equiv.apply_symm_apply, hkey]
  · rintro ⟨hbij, hmaps⟩
    refine ⟨hbij, fun x hx => ?_⟩
    exact ⟨(hmaps x hx).1, (hmaps x hx).2.1⟩

/-- **HOL `components_iso_image`**（lp_gen_theory.vhl:68；按 hypermap_iso.vhl
`iso_components` :461 同构折算）`d IN dart K ==> node H (f d) = IMAGE f (node K d)
/\ face H (f d) = IMAGE f (face K d)`。 -/
theorem componentsIsoImage {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} {f : α → β}
    (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) {d : α} (hd : d ∈ K.darts) :
    H.node (f d) = f '' K.node d ∧ H.face (f d) = f '' K.face d :=
  ⟨orbitImageOfMem K.nodeMap_permutes (fun z hz => (hmaps z hz).2.1) hd,
    orbitImageOfMem K.faceMap_permutes (fun z hz => (hmaps z hz).2.2) hd⟩

/-- **HOL `hyp_iso_card_components`**（hypermap_iso.vhl:471）
`x IN dart K ==> CARD (face K x) = CARD (face H (f x)) /\
CARD (node K x) = CARD (node H (f x)) /\ CARD (edge K x) = CARD (edge H (f x))`
——轨道像运输 + InjOn.ncard_image（HOL CARD_IMAGE_INJ + *_FINITE 同构）。 -/
theorem hypIsoCardComponents {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} {f : α → β}
    (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) {x : α} (hx : x ∈ K.darts) :
    (K.face x).ncard = (H.face (f x)).ncard ∧
      (K.node x).ncard = (H.node (f x)).ncard ∧
      (K.edge x).ncard = (H.edge (f x)).ncard := by
  have hface : H.face (f x) = f '' K.face x :=
    (componentsIsoImage hbij hmaps hx).2
  have hnode : H.node (f x) = f '' K.node x :=
    (componentsIsoImage hbij hmaps hx).1
  have hedge : H.edge (f x) = f '' K.edge x :=
    orbitImageOfMem K.edgeMap_permutes (fun z hz => (hmaps z hz).1) hx
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rw [hface, Set.InjOn.ncard_image
      (hbij.injOn.mono (K.face_subset_darts hx))]
  · rw [hnode, Set.InjOn.ncard_image
      (hbij.injOn.mono (K.node_subset_darts hx))]
  · rw [hedge, Set.InjOn.ncard_image
      (hbij.injOn.mono (K.edge_subset_darts hx))]

/-! ### §1 iso 章（tame_list.hl:9276-:9317） -/

/-- **HOL `iso_is_no_double_joins`**（tame_list.hl:9276-:9302）
`hyp_iso f (K,H) /\ is_no_double_joins H ==> is_no_double_joins K`——
v ∈ node u ⇒ v ∈ dart K（node ⊆ dart）；两次轨道像运输把前提共轭到 H 侧
（HOL 的 hyp_iso_edge_node 绕行步在 Lean 冗余：Iso 三交换直接可用），
IsNoDoubleJoins 点态收口 + BijOn 单射性回传（= hyp_iso_bij）。 -/
theorem isoIsNoDoubleJoins {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} (h : K.Iso H)
    (hnd : H.IsNoDoubleJoins) : K.IsNoDoubleJoins := by
  obtain ⟨f, hbij, hmaps⟩ := h
  intro u v hu hv hj
  have hfu : f u ∈ H.darts := hbij.mapsTo hu
  have hvd : v ∈ K.darts := K.node_subset_darts hu hv
  have hfv : f v ∈ H.darts := hbij.mapsTo hvd
  have himgN : H.node (f u) = f '' K.node u :=
    (componentsIsoImage hbij hmaps hu).1
  have hfvN : f v ∈ H.node (f u) := by
    rw [himgN]; exact Set.mem_image_of_mem _ hv
  have hme : H.edgeMap (f v) = f (K.edgeMap v) := (hmaps v hvd).1
  have hmu : H.edgeMap (f u) = f (K.edgeMap u) := (hmaps u hu).1
  have hj' : H.edgeMap (f v) ∈ H.node (H.edgeMap (f u)) := by
    rw [hme, hmu,
      (componentsIsoImage hbij hmaps (K.edgeMap_apply_mem hu)).1]
    exact Set.mem_image_of_mem _ hj
  exact hbij.injOn hu hvd (hnd (f u) (f v) hfu hfvN hj')

/-- **HOL `iso_card_face`**（tame_list.hl:9304-:9317）
`hyp_iso f (K,H) /\ (!x. x IN dart H ==> 3 <= CARD (face H x)) ==>
!x. x IN dart K ==> 3 <= CARD (face K x)`——hyp_iso_dart 前件 + face 分量
card 保形（hyp_iso_card_components 第 1 合取；短路线不适用：结论是
ncard 数值式，如实走桥，见文件头记账）。 -/
theorem isoCardFace {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} (h : K.Iso H)
    (hf : ∀ x ∈ H.darts, 3 ≤ (H.face x).ncard) :
    ∀ x ∈ K.darts, 3 ≤ (K.face x).ncard := by
  obtain ⟨f, hbij, hmaps⟩ := h
  intro x hx
  rw [(hypIsoCardComponents hbij hmaps hx).1]
  exact hf (f x) (hbij.mapsTo hx)

/-! ### §2 restricted 分量件 I：点态族（hypermap_iso.vhl :545-:559） -/

/-- **HOL `iso_edge_nondegenerate_imp`**（hypermap_iso.vhl:552）
`is_edge_nondegenerate H ==> is_edge_nondegenerate K`——批 14 点态短路线
范式适用（三交换第 1 分量两步反证）。 -/
theorem isoEdgeNondegenerate {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} (h : K.Iso H)
    (he : H.EdgeNondegenerate) : K.EdgeNondegenerate := by
  obtain ⟨f, hbij, hmaps⟩ := h
  intro x hx hcon
  exact he (f x) (hbij.mapsTo hx) (by rw [(hmaps x hx).1, hcon])

/-- **HOL `iso_plain_imp`**（hypermap_iso.vhl:545）
`plain_hypermap H ==> plain_hypermap K`——Plain 是全域置换等式：dart 侧
两次交换共轭 + 单射收口；集合外点由 `PermutesOn` 定义性恒等（HOL
h_map_outside 同构，PermutesOn 内置）。 -/
theorem isoPlain {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} (h : K.Iso H)
    (hp : H.Plain) : K.Plain := by
  obtain ⟨f, hbij, hmaps⟩ := h
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ K.darts
  · show K.edgeMap (K.edgeMap x) = x
    have h1 : f x = H.edgeMap (H.edgeMap (f x)) := by
      rw [← Equiv.Perm.mul_apply H.edgeMap H.edgeMap (f x), hp,
        Equiv.Perm.one_apply]
    have h3 : H.edgeMap (f (K.edgeMap x)) = f (K.edgeMap (K.edgeMap x)) :=
      (hmaps (K.edgeMap x) (K.edgeMap_apply_mem hx)).1
    have h4 : K.edgeMap (K.edgeMap x) ∈ K.darts :=
      K.edgeMap_apply_mem (K.edgeMap_apply_mem hx)
    refine hbij.injOn h4 hx ?_
    rw [h1, ← h3, ← (hmaps x hx).1]
  · have h5 : K.edgeMap x = x := K.edgeMap_permutes x hx
    show K.edgeMap (K.edgeMap x) = x
    rw [h5, h5]

/-! ### §3 restricted 分量件 II：simple（hypermap_iso.vhl :559） -/

/-- **HOL `iso_simple_imp`**（hypermap_iso.vhl:559）
`simple_hypermap H ==> simple_hypermap K`——node/face 轨道像运输把交合取
共轭到 H 侧（HOL image_inter_inj_gen 的点态同构，免 image-inter 引理），
单射收口回 K 侧。 -/
theorem isoSimple {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} (h : K.Iso H)
    (hs : H.Simple) : K.Simple := by
  obtain ⟨f, hbij, hmaps⟩ := h
  intro x hx
  have hfx : f x ∈ H.darts := hbij.mapsTo hx
  have hcomm := componentsIsoImage hbij hmaps hx
  have hsimple := hs (f x) hfx
  ext y
  constructor
  · intro hy
    have hyd : y ∈ K.darts := K.node_subset_darts hx hy.1
    have h1 : f y ∈ H.node (f x) := by
      rw [hcomm.1]; exact Set.mem_image_of_mem _ hy.1
    have h2 : f y ∈ H.face (f x) := by
      rw [hcomm.2]; exact Set.mem_image_of_mem _ hy.2
    have h3 : f y ∈ H.node (f x) ∩ H.face (f x) := ⟨h1, h2⟩
    rw [hsimple] at h3
    exact hbij.injOn hyd hx (Set.mem_singleton_iff.mp h3)
  · intro hy
    rw [Set.mem_singleton_iff.mp hy]
    exact ⟨K.mem_node_self x, K.mem_face_self x⟩


/-! ### §4 路径与连通分量运输（hypermap_iso.vhl :361-:689 的 restricted 链） -/

section Transport

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
  {K : Hypermap α} {H : Hypermap β} {f : α → β}

/-- 私件（HOL `hyp_path_subset`，hypermap_iso.vhl:361）：路径成员不离开
dart 集。 -/
private theorem isPathDartsSubset (K : Hypermap α) {p : ℕ → α} :
    ∀ n : ℕ, K.isPath p n → p 0 ∈ K.darts → ∀ i ≤ n, p i ∈ K.darts := by
  intro n
  induction n with
  | zero =>
    intro _hp h0 i hi
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    rw [hi0]; exact h0
  | succ k ih =>
    intro hp h0 i hi
    rw [K.isPath_succ] at hp
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · exact ih hp.1 h0 i (Nat.lt_succ_iff.mp hlt)
    · have heq : i = k + 1 := by omega
      subst heq
      have hpn : p k ∈ K.darts := ih hp.1 h0 k le_rfl
      rcases hp.2 with h | h | h
      · rw [h]; exact K.edgeMap_apply_mem hpn
      · rw [h]; exact K.nodeMap_apply_mem hpn
      · rw [h]; exact K.faceMap_apply_mem hpn

/-- 私件（HOL `iso_path_imp`，hypermap_iso.vhl:587）：路径沿 iso 前推。 -/
private theorem isoPathImp (hmaps : IsoCommutes K f H) {p : ℕ → α} {n : ℕ}
    (hp : K.isPath p n) (h0 : p 0 ∈ K.darts) : H.isPath (fun i => f (p i)) n := by
  induction n with
  | zero => trivial
  | succ k ih =>
    have hpk : K.isPath p k := K.isPath_mono hp (Nat.le_succ k)
    rw [H.isPath_succ]
    refine ⟨ih hpk, ?_⟩
    have hpn : p k ∈ K.darts := isPathDartsSubset K k hpk h0 k le_rfl
    rcases K.goOneStep_of_isPath hp le_rfl with h | h | h
    · left; show f (p (k + 1)) = H.edgeMap (f (p k))
      rw [h, (hmaps (p k) hpn).1]
    · right; left; show f (p (k + 1)) = H.nodeMap (f (p k))
      rw [h, (hmaps (p k) hpn).2.1]
    · right; right; show f (p (k + 1)) = H.faceMap (f (p k))
      rw [h, (hmaps (p k) hpn).2.2]

/-- 私件（HOL `iso_path_inv`，hypermap_iso.vhl:597）：路径沿 iso 回拉——
逐点在 dart 集上取原像（越界点以 q 0 的原像兜底，保函数全性），单射性
回传步关系。 -/
private theorem isoPathInv (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) {q : ℕ → β} {n : ℕ}
    (hq : H.isPath q n) (h0 : q 0 ∈ H.darts) :
    ∃ p : ℕ → α, (∀ i ≤ n, q i = f (p i)) ∧ p 0 ∈ K.darts ∧ K.isPath p n := by
  have hqD : ∀ i ≤ n, q i ∈ H.darts := isPathDartsSubset H n hq h0
  obtain ⟨z0, hz01, hz02⟩ := hbij.surjOn h0
  classical
  have hpchoice : ∀ i : ℕ, ∃ z : α, q i ∈ H.darts → z ∈ K.darts ∧ f z = q i := by
    intro i
    by_cases h : q i ∈ H.darts
    · exact ⟨Classical.choose (hbij.surjOn h), fun _ =>
        Classical.choose_spec (hbij.surjOn h)⟩
    · exact ⟨z0, fun hq => absurd hq h⟩
  choose p hpval using hpchoice
  refine ⟨p, fun i hi => (hpval i (hqD i hi)).2.symm, (hpval 0 h0).1, ?_⟩
  have hisp : ∀ m ≤ n, K.isPath p m := by
    intro m
    induction m with
    | zero => intro _; trivial
    | succ k ih =>
      intro hm
      rw [K.isPath_succ]
      refine ⟨ih (Nat.le_trans (Nat.le_succ k) hm), ?_⟩
      have hk : k ≤ n := Nat.le_trans (Nat.le_succ k) hm
      have hpk : p k ∈ K.darts := (hpval k (hqD k hk)).1
      have hpk1 : p (k + 1) ∈ K.darts := (hpval (k + 1) (hqD (k + 1) hm)).1
      have hqk : q k = f (p k) := (hpval k (hqD k hk)).2.symm
      have hqk1 : q (k + 1) = f (p (k + 1)) :=
        (hpval (k + 1) (hqD (k + 1) hm)).2.symm
      rcases H.goOneStep_of_isPath hq hm with h | h | h
      · left; show p (k + 1) = K.edgeMap (p k)
        refine hbij.injOn hpk1 (K.edgeMap_apply_mem hpk) ?_
        rw [← (hmaps (p k) hpk).1, ← hqk1, h, hqk]
      · right; left; show p (k + 1) = K.nodeMap (p k)
        refine hbij.injOn hpk1 (K.nodeMap_apply_mem hpk) ?_
        rw [← (hmaps (p k) hpk).2.1, ← hqk1, h, hqk]
      · right; right; show p (k + 1) = K.faceMap (p k)
        refine hbij.injOn hpk1 (K.faceMap_apply_mem hpk) ?_
        rw [← (hmaps (p k) hpk).2.2, ← hqk1, h, hqk]
  exact hisp n (Nat.le_refl n)

/-- 私件（HOL `iso_comb_component`，hypermap_iso.vhl:631）：组合分量沿
iso 搬运。 -/
private theorem isoCombComponent (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) {d : α} (hd : d ∈ K.darts) :
    H.combComponent (f d) = f '' K.combComponent d := by
  ext y
  simp only [Hypermap.combComponent, Hypermap.isInComponent, Set.mem_setOf_eq,
    Set.mem_image]
  constructor
  · rintro ⟨q, n, hq0, hqn, hpath⟩
    obtain ⟨p, hqfp, hp0, hppath⟩ :=
      isoPathInv hbij hmaps hpath (by rw [hq0]; exact hbij.mapsTo hd)
    have hp0d : p 0 = d := by
      refine hbij.injOn hp0 hd ?_
      rw [← hqfp 0 (Nat.zero_le n), hq0]
    refine ⟨p n, ⟨p, n, hp0d, rfl, hppath⟩, ?_⟩
    rw [← hqfp n (Nat.le_refl n)]
    exact hqn
  · intro hy
    obtain ⟨z, hw, hfeq⟩ := hy
    obtain ⟨p, n, hp0, hpn, hpath⟩ := hw
    subst hfeq
    exact ⟨fun i => f (p i), n, by show f (p 0) = f d; rw [hp0],
      by show f (p n) = f z; rw [hpn],
      isoPathImp hmaps hpath (by rw [hp0]; exact hd)⟩

/-- 私件：组合分量不离开 dart 集（`lemma_component_subset` 的 Lean 形）。 -/
private theorem combComponentSubset (K : Hypermap α) {d : α} (hd : d ∈ K.darts) :
    K.combComponent d ⊆ ↑K.darts := by
  intro y hy
  simp only [Hypermap.combComponent, Hypermap.isInComponent, Set.mem_setOf_eq] at hy
  obtain ⟨p, n, hp0, hpn, hpath⟩ := hy
  rw [← hpn]
  exact isPathDartsSubset K n hpath (by rw [hp0]; exact hd) n (Nat.le_refl n)

/-- 私件：单射下像相等 ⇒ 集相等（HOL `image_inj_gen` 的 Lean 形）。 -/
private theorem imageInjOnSet (hinj : Set.InjOn f (↑K.darts)) {A B : Set α}
    (hA : A ⊆ ↑K.darts) (hB : B ⊆ ↑K.darts) (h : f '' A = f '' B) : A = B := by
  ext y
  constructor
  · intro hy
    have hyf : f y ∈ f '' B := by rw [← h]; exact ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hfy⟩ := hyf
    have hy'y : y' = y := hinj (hB hy') (hA hy) hfy
    rw [← hy'y]; exact hy'
  · intro hy
    have hyf : f y ∈ f '' A := by rw [h]; exact ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hfy⟩ := hyf
    have hy'y : y' = y := hinj (hA hy') (hB hy) hfy
    rw [← hy'y]; exact hy'

/-- **HOL `iso_node_set`**（hypermap_iso.vhl:487）：node 轨道族沿 iso 搬运
（H 侧 = K 侧轨道的像族）。 -/
private theorem isoNodeSetImage (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) :
    H.nodeSet = (fun s : Set α => f '' s) '' K.nodeSet := by
  ext s
  simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hyD, hs⟩
    obtain ⟨x, hxD, hfx⟩ := hbij.surjOn hyD
    refine ⟨K.node x, ⟨x, hxD, rfl⟩, ?_⟩
    rw [← hs, ← hfx]
    exact (orbitImageOfMem K.nodeMap_permutes
      (fun z hz => (hmaps z hz).2.1) hxD).symm
  · rintro ⟨s', hs', rfl⟩
    obtain ⟨x, hxD, hs⟩ := hs'
    refine ⟨f x, hbij.mapsTo hxD, ?_⟩
    rw [← hs]
    exact orbitImageOfMem K.nodeMap_permutes (fun z hz => (hmaps z hz).2.1) hxD

/-- **HOL `iso_edge_set`**（hypermap_iso.vhl:497）：edge 轨道族沿 iso 搬运。 -/
private theorem isoEdgeSetImage (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) :
    H.edgeSet = (fun s : Set α => f '' s) '' K.edgeSet := by
  ext s
  simp only [Hypermap.edgeSet, setOfOrbits, Set.mem_setOf_eq, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hyD, hs⟩
    obtain ⟨x, hxD, hfx⟩ := hbij.surjOn hyD
    refine ⟨K.edge x, ⟨x, hxD, rfl⟩, ?_⟩
    rw [← hs, ← hfx]
    exact (orbitImageOfMem K.edgeMap_permutes
      (fun z hz => (hmaps z hz).1) hxD).symm
  · rintro ⟨s', hs', rfl⟩
    obtain ⟨x, hxD, hs⟩ := hs'
    refine ⟨f x, hbij.mapsTo hxD, ?_⟩
    rw [← hs]
    exact orbitImageOfMem K.edgeMap_permutes (fun z hz => (hmaps z hz).1) hxD

/-- **HOL `iso_face_set`**（hypermap_iso.vhl:507）：face 轨道族沿 iso 搬运。 -/
private theorem isoFaceSetImage (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) :
    H.faceSet = (fun s : Set α => f '' s) '' K.faceSet := by
  ext s
  simp only [Hypermap.faceSet, setOfOrbits, Set.mem_setOf_eq, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hyD, hs⟩
    obtain ⟨x, hxD, hfx⟩ := hbij.surjOn hyD
    refine ⟨K.face x, ⟨x, hxD, rfl⟩, ?_⟩
    rw [← hs, ← hfx]
    exact (orbitImageOfMem K.faceMap_permutes
      (fun z hz => (hmaps z hz).2.2) hxD).symm
  · rintro ⟨s', hs', rfl⟩
    obtain ⟨x, hxD, hs⟩ := hs'
    refine ⟨f x, hbij.mapsTo hxD, ?_⟩
    rw [← hs]
    exact orbitImageOfMem K.faceMap_permutes (fun z hz => (hmaps z hz).2.2) hxD

/-- **HOL `iso_set_part_components`**（hypermap_iso.vhl:653）：分量族沿 iso
搬运。 -/
private theorem isoSetOfComponentsImage (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) :
    H.setOfComponents = (fun s : Set α => f '' s) '' K.setOfComponents := by
  ext s
  simp only [Hypermap.setOfComponents, Hypermap.setPartComponents, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hyD, hs⟩
    obtain ⟨x, hxD, hfx⟩ := hbij.surjOn hyD
    refine ⟨K.combComponent x, ⟨x, hxD, rfl⟩, ?_⟩
    rw [← hs, ← hfx]
    exact (isoCombComponent hbij hmaps hxD).symm
  · rintro ⟨s', hs', rfl⟩
    obtain ⟨x, hxD, hs⟩ := hs'
    refine ⟨f x, hbij.mapsTo hxD, ?_⟩
    rw [← hs]
    exact isoCombComponent hbij hmaps hxD

/-- **HOL `iso_number_of_nodes`**（hypermap_iso.vhl:515）。 -/
theorem isoNumberOfNodes (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) : K.numberOfNodes = H.numberOfNodes := by
  have himg := isoNodeSetImage hbij hmaps
  have hinj : Set.InjOn (fun s : Set α => f '' s) K.nodeSet := by
    intro s₁ hs₁ s₂ hs₂ hseq
    obtain ⟨x₁, hx₁D, hx₁⟩ := hs₁
    obtain ⟨x₂, hx₂D, hx₂⟩ := hs₂
    subst hx₁
    subst hx₂
    exact imageInjOnSet hbij.injOn (K.node_subset_darts hx₁D)
      (K.node_subset_darts hx₂D) hseq
  show K.nodeSet.ncard = H.nodeSet.ncard
  rw [himg, Set.InjOn.ncard_image hinj]

/-- **HOL `iso_number_of_edges`**（hypermap_iso.vhl:525）。 -/
theorem isoNumberOfEdges (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) : K.numberOfEdges = H.numberOfEdges := by
  have himg := isoEdgeSetImage hbij hmaps
  have hinj : Set.InjOn (fun s : Set α => f '' s) K.edgeSet := by
    intro s₁ hs₁ s₂ hs₂ hseq
    obtain ⟨x₁, hx₁D, hx₁⟩ := hs₁
    obtain ⟨x₂, hx₂D, hx₂⟩ := hs₂
    subst hx₁
    subst hx₂
    exact imageInjOnSet hbij.injOn (K.edge_subset_darts hx₁D)
      (K.edge_subset_darts hx₂D) hseq
  show K.edgeSet.ncard = H.edgeSet.ncard
  rw [himg, Set.InjOn.ncard_image hinj]

/-- **HOL `iso_number_of_faces`**（hypermap_iso.vhl:535）。 -/
theorem isoNumberOfFaces (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) : K.numberOfFaces = H.numberOfFaces := by
  have himg := isoFaceSetImage hbij hmaps
  have hinj : Set.InjOn (fun s : Set α => f '' s) K.faceSet := by
    intro s₁ hs₁ s₂ hs₂ hseq
    obtain ⟨x₁, hx₁D, hx₁⟩ := hs₁
    obtain ⟨x₂, hx₂D, hx₂⟩ := hs₂
    subst hx₁
    subst hx₂
    exact imageInjOnSet hbij.injOn (K.face_subset_darts hx₁D)
      (K.face_subset_darts hx₂D) hseq
  show K.faceSet.ncard = H.faceSet.ncard
  rw [himg, Set.InjOn.ncard_image hinj]

/-- **HOL `iso_number_of_components`**（hypermap_iso.vhl:661）。 -/
theorem isoNumberOfComponents (hbij : Set.BijOn f (↑K.darts) (↑H.darts))
    (hmaps : IsoCommutes K f H) :
    K.numberOfComponents = H.numberOfComponents := by
  have himg := isoSetOfComponentsImage hbij hmaps
  have hinj : Set.InjOn (fun s : Set α => f '' s) K.setOfComponents := by
    intro s₁ hs₁ s₂ hs₂ hseq
    obtain ⟨x₁, hx₁D, hx₁⟩ := hs₁
    obtain ⟨x₂, hx₂D, hx₂⟩ := hs₂
    subst hx₁
    subst hx₂
    exact imageInjOnSet hbij.injOn (combComponentSubset K hx₁D)
      (combComponentSubset K hx₂D) hseq
  show K.setOfComponents.ncard = H.setOfComponents.ncard
  rw [himg, Set.InjOn.ncard_image hinj]

/-- **HOL `iso_card_dart`**（hypermap_iso.vhl:671）。 -/
theorem isoCardDart (hbij : Set.BijOn f (↑K.darts) (↑H.darts)) :
    K.darts.card = H.darts.card := by
  have hnc := Set.BijOn.ncard_eq hbij
  rwa [Set.ncard_coe_finset, Set.ncard_coe_finset] at hnc

/-- **HOL `iso_planar_imp`**（hypermap_iso.vhl:643）：Euler 公式五量全部
保形。 -/
theorem isoPlanar (h : K.Iso H) (hp : H.Planar) : K.Planar := by
  obtain ⟨_, hbij, hmaps⟩ := h
  show K.numberOfNodes + K.numberOfEdges + K.numberOfFaces
    = K.darts.card + 2 * K.numberOfComponents
  rw [isoNumberOfNodes hbij hmaps, isoNumberOfEdges hbij hmaps,
    isoNumberOfFaces hbij hmaps, isoCardDart hbij,
    isoNumberOfComponents hbij hmaps]
  exact hp

/-- **HOL `iso_connected_imp`**（hypermap_iso.vhl:649）。 -/
theorem isoConnected (h : K.Iso H) (hc : H.Connected) : K.Connected := by
  obtain ⟨_, hbij, hmaps⟩ := h
  show K.numberOfComponents = 1
  rw [isoNumberOfComponents hbij hmaps]
  exact hc

end Transport

/-! ### §5 iso 章装配（tame_list.hl:9319-:9357） -/

/-- **HOL `hyp_iso_restricted`**（tame_list.hl:9319-:9357）
`hyp_iso f (K,H) /\ is_restricted H ==> is_restricted K`——九合取逐槽装配：
darts ≠ ∅ 经 surjOn 取原像；plain/edge_nondegenerate/simple/no_double_joins/
node_nondegenerate/card_face 走 §0-§3 分量件；planar/connected 走 §4
计数运输链（HOL 同构，零收窄）。 -/
theorem hypIsoRestricted {α β : Type*} [DecidableEq α] [DecidableEq β]
    {K : Hypermap α} {H : Hypermap β} (h : K.Iso H)
    (hr : H.IsRestricted) : K.IsRestricted := by
  have hcopy := h
  obtain ⟨_, hbij, _⟩ := hcopy
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hr.1
  obtain ⟨x, hxK, _hfx⟩ := hbij.surjOn hy
  have hKne : K.darts.Nonempty := ⟨x, hxK⟩
  refine ⟨(Finset.nonempty_iff_ne_empty (s := K.darts)).mp hKne,
    isoPlanar h hr.2.1,
    isoPlain h hr.2.2.1, isoConnected h hr.2.2.2.1, isoSimple h hr.2.2.2.2.1,
    isoIsNoDoubleJoins h hr.2.2.2.2.2.1,
    isoEdgeNondegenerate h hr.2.2.2.2.2.2.1,
    isoIsNodeNondegenerate h hr.2.2.2.2.2.2.2.1,
    isoCardFace h hr.2.2.2.2.2.2.2.2⟩

/-- **HOL `iso_restricted`**（tame_list.hl:9359-:9374，批 16 接续件提前落）
`iso H K ==> (is_restricted H <=> is_restricted K)`——两向各走
hypIsoRestricted；逆向经 `Iso.symm`（需 `Nonempty α`：HOL 类型恒非空，
Lean 侧与 Hypermap.Iso.symm 自身要求一致，零收窄记账）。 -/
theorem isoRestrictedIff {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Nonempty α] {K : Hypermap α} {H : Hypermap β} (h : K.Iso H) :
    H.IsRestricted ↔ K.IsRestricted :=
  ⟨hypIsoRestricted h, fun hrK => hypIsoRestricted h.symm hrK⟩

end Kepler.Text.TameSpine
