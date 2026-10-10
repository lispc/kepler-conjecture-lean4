/-
  Kepler.Text.TameSpine.TameList1 — B1 Tame_list 地基批 1：S2/S6 重点件抽取
  （tamespine-port-plan §4 批次表 B1 行；A9 装配件 GNBEVVU/JXBJOAB/DAKEFCC）。

  立项：`docs/tamespine-port-plan.md` §4 批次表 B1 行「tame_list.hl（前 2 批先抽
  S2/S6 重点件：map_good_list/hypermap_of_list_map/JXBJOAB/GNBEVVU/DAKEFCC，
  其余直译）」+ §3 A9 行「Tame_list(JXBJOAB/GNBEVVU/DAKEFCC) + S1 + S6」。
  深侦：`docs/tame-chapter-scout.md` §3.3-S2/S6 + §6-R3。

  镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353）：
  - `text_formalization/tame/tame_defs2.hl:62-69`（`iso_list`/`isop_list` def）；
  - `text_formalization/tame/tame_list.hl:3403`（`map_good_list`）、`:3450`
    （`find_face_map`）、`:3486`（`hypermap_of_list_map`）、`:3540`（`GNBEVVU`）、
    `:3554`（`iso_list_good_list`，别名 `PEUTLZH` :3568）、`:3733`（`JXBJOAB`）、
    `:9343`（`iso_restricted`，别名 `DAKEFCC` :9360）。

  批内分工记账（S2/S6 五重点件 → 本模块或既有件）：
  - `map_good_list`/`find_face_map`/`hypermap_of_list_map`：**TameLp 已真**
    （W1/B-D1 先行 lane：`la7_mapGoodList` TameLp.lean:3129、
    `la7_findFace_map` :3226、类型层 `hypermapOfList_iso_map` :3577）——
    本模块只补 `inj_on phi (elements_of_list L)` 的 `Set.InjOn` 桥形入口
    （`inj_on_INJ` 同型折算），零新证明内容。
  - `GNBEVVU`/`JXBJOAB`/`DAKEFCC`：本批新证（真证明零 sorry）。

  DAKEFCC（`iso_restricted`）证明要点：Lean `Hypermap` 结构层把 HOL `res` 语义
  内置（`PermutesOn f s := ∀ x ∉ s, f x = x`，Hypermap.lean:678），故 is_restricted
  九合取项全部沿 `Iso` 运输：dart 级项（Planar/Connected 计数、Simple、
  no-double-joins、边·节点非退化、face ≥ 3）经 orbit 幂传输逐项搬运；全局
  `Plain`（edgeMap² = 1）在 dart 上由 Iso 交换律 + H 侧全等式给出、dart 外由
  K 侧 PermutesOn 恒等给出——**无任何附加前提**，与 HOL 原文
  `iso H K ⇒ (is_restricted H ⇔ is_restricted K)` 逐字对齐
  （symm 方向需 `Nonempty α`，HOL 类型恒非空的对应折算）。
  orbit/路径/计数传输辅助件全部落本模块私有层（R3 纪律：不动 Hypermap.lean）。

  红线遵守：本模块零 sorry、零既有文件触碰、零 git 写操作。
-/
import Kepler.Assembly
import Kepler.Text.TameLp
import Kepler.Text.Hypermap
import Kepler.Text.TameSpine.Keystone

namespace Kepler.Text.TameSpine

open Kepler.Text (Hypermap orbitMap)
open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList listOfDarts findFaceDarts)
open Kepler.Text.TameLp (hypermapOfList elementsOfList)

/-! ### §1 `iso_list`/`isop_list` def 层（tame_defs2.hl:62-69） -/

/-- HOL `isop_list`（tame_defs2.hl:66-69
`isop_list phi (L,N) (L',N') <=> inj_on phi (elements_of_list L) /\
L' = MAP (MAP phi) L /\ N' = MAP (MAP (\u. phi (FST u), phi (SND u))) N`）的
显式 φ 形。折算：`elements_of_list` ↦ `TameLp.elementsOfList`（undup·flatten
集合形）、`MAP (MAP phi)` ↦ `L.map (List.map phi)`、dart 提升对
`\u. phi (FST u), phi (SND u)` ↦ `fun u => (phi u.1, phi u.2)`。
（HOL 把 L N 捆成对 `(L,N)` 作单参数；Lean 侧按四参数平铺，语义逐槽一致。） -/
def IsopListSpine (phi : ℕ → ℕ) (L L' : fgraph ℕ)
    (N N' : List (List (ℕ × ℕ))) : Prop :=
  Set.InjOn phi (elementsOfList L) ∧
    L' = L.map (List.map phi) ∧
    N' = N.map (fun s => s.map (fun u => (phi u.1, phi u.2)))

/-- HOL `iso_list`（tame_defs2.hl:62-65，`iso_list (L,N) (L',N') <=> ?phi.
inj_on phi (elements_of_list L) /\ ...`）的存在 φ 形（IsopListSpine 的
∃-折叠；isop_list 与 iso_list 的两向关系即 `∃` 展开）。 -/
def IsoListSpine (L L' : fgraph ℕ) (N N' : List (List (ℕ × ℕ))) : Prop :=
  ∃ phi, IsopListSpine phi L L' N N'

/-- 显式 φ 形 ⟹ 存在 φ 形（`∃` 引入，桥件供下游免 `obtain` 消费）。 -/
theorem isopListSpine_isoListSpine {phi : ℕ → ℕ} {L L' : fgraph ℕ}
    {N N' : List (List (ℕ × ℕ))} (h : IsopListSpine phi L L' N N') :
    IsoListSpine L L' N N' := ⟨phi, h⟩

/-- HOL `inj_on phi (elements_of_list L)` ↔ flatten 层逐点单射
（`inj_on_INJ`（tame_list.hl:3308）同型折算；`elementsOfList L =
{x | x ∈ L.flatten.eraseDups}` 经 core `List.mem_eraseDups` 消解）。 -/
theorem injOn_elementsOfList_iff {L : fgraph ℕ} {phi : ℕ → ℕ} :
    Set.InjOn phi (elementsOfList L) ↔
      ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, phi u = phi v → u = v := by
  constructor
  · intro hinj u hu v hv huv
    have hu' : u ∈ elementsOfList L := List.mem_eraseDups.mpr hu
    have hv' : v ∈ elementsOfList L := List.mem_eraseDups.mpr hv
    exact hinj hu' hv' huv
  · intro h x₁ hx₁ x₂ hx₂ heq
    have f1 : x₁ ∈ L.flatten :=
      List.mem_eraseDups.mp (by show x₁ ∈ TameLp.listOfElements L; exact hx₁)
    have f2 : x₂ ∈ L.flatten :=
      List.mem_eraseDups.mp (by show x₂ ∈ TameLp.listOfElements L; exact hx₂)
    exact h x₁ f1 x₂ f2 heq

/-! ### §2 S2 map 家族的 `Set.InjOn` 桥形入口（TameLp 已真件） -/

/-- HOL `map_good_list`（tame_list.hl:3403-3407
`good_list x /\ inj_on phi (elements_of_list x) ==> good_list (MAP (MAP phi) x)`）
的 InjOn 桥形——本体 = TameLp W1/B-D1 先行件 `la7_mapGoodList`
（TameLp.lean:3129，flatten 层单射形）经 `injOn_elementsOfList_iff` 折算。 -/
theorem mapGoodList_injOn {L : fgraph ℕ} {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) (hgood : GoodList L) :
    GoodList (L.map (List.map phi)) :=
  Kepler.Text.TameLp.la7_mapGoodList L (injOn_elementsOfList_iff.mp hinj) hgood

/-- HOL `find_face_map`（tame_list.hl:3450-3454 `find_face (MAP (MAP phi) x)
(phi p1,phi p2) = MAP (\d. phi (FST d),phi (SND d)) (find_face x (p1,p2))`）
的 InjOn 桥形——本体 = `la7_findFace_map`（TameLp.lean:3226）。 -/
theorem findFace_map_injOn {L : fgraph ℕ} {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L))
    (d : ℕ × ℕ) (hd : d ∈ listOfDarts L) :
    findFaceDarts (L.map (List.map phi)) (phi d.1, phi d.2)
      = (findFaceDarts L d).map (fun x : ℕ × ℕ => (phi x.1, phi x.2)) :=
  Kepler.Text.TameLp.la7_findFace_map L (injOn_elementsOfList_iff.mp hinj) d hd

/-- HOL `hypermap_of_list_map`（tame_list.hl:3486-3488
`iso (hypermap_of_list x) (hypermap_of_list (MAP (MAP phi) x))`）的 InjOn
桥形——本体 = TameLp 类型层 `hypermapOfList_iso_map`（TameLp.lean:3577，
同构函数 = pair-lift）。S2 的 Hypermap 类型层出口件（A7/A9 消费形）。 -/
theorem hypermapOfList_iso_map_injOn {L : fgraph ℕ} {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) (hgood : GoodList L) :
    Hypermap.Iso (hypermapOfList L hgood)
      (hypermapOfList (L.map (List.map phi)) (mapGoodList_injOn hinj hgood)) :=
  Kepler.Text.TameLp.hypermapOfList_iso_map L (injOn_elementsOfList_iff.mp hinj) hgood

/-! ### §3 S6 重点件：iso_list 运输与 GNBEVVU / JXBJOAB -/

/-- HOL `iso_list_good_list`（tame_list.hl:3554-3557，别名 `PEUTLZH` :3568
`iso_list (L,[]) (L',[]) /\ good_list L ==> good_list L'`）的显式 φ 形。
证明同 HOL：unfold iso_list 后即 `map_good_list`（N' 方程在本件中不起作用，
与 HOL `ASM_REWRITE_TAC` 同构）。 -/
theorem isopListSpine_goodList {L L' : fgraph ℕ}
    {N N' : List (List (ℕ × ℕ))} {phi : ℕ → ℕ}
    (h : IsopListSpine phi L L' N N') (hgood : GoodList L) : GoodList L' := by
  obtain ⟨hinj, hL', -⟩ := h
  rw [hL']
  exact mapGoodList_injOn hinj hgood

/-- HOL `iso_list_good_list`（tame_list.hl:3554；存在 φ 形）。 -/
theorem isoListSpine_goodList {L L' : fgraph ℕ}
    {N N' : List (List (ℕ × ℕ))} (h : IsoListSpine L L' N N')
    (hgood : GoodList L) : GoodList L' := by
  obtain ⟨phi, h⟩ := h
  exact isopListSpine_goodList h hgood

/-- HOL `PEUTLZH`（tame_list.hl:3568 `let PEUTLZH = iso_list_good_list;;`）
别名件（逐字同体，供下游按 HOL 名检索）。 -/
theorem PEUTLZH {L L' : fgraph ℕ} {N N' : List (List (ℕ × ℕ))}
    (h : IsoListSpine L L' N N') (hgood : GoodList L) : GoodList L' :=
  isoListSpine_goodList h hgood

/-- **HOL `GNBEVVU`**（tame_list.hl:3540-3543
`!L N L'. good_list L /\ iso_list (L,N) (L',N') ==> iso (hypermap_of_list L)
(hypermap_of_list L')`，S6/A9 装配件）。

证明同 HOL（unfold iso_list 后即 `hypermap_of_list_map`，N 方程不起作用）：
`hypermapOfList_iso_map_injOn` + L' 方程重写。A9 的 JCAJYDU 装配
（`Jcajydu ← Tame_list(GNBEVVU)`）自此有出料口。 -/
theorem GNBEVVU {L L' : fgraph ℕ} {N N' : List (List (ℕ × ℕ))}
    (hgood : GoodList L) (hiso : IsoListSpine L L' N N') :
    Hypermap.Iso (hypermapOfList L hgood)
      (hypermapOfList L' (isoListSpine_goodList hiso hgood)) := by
  obtain ⟨phi, hinj, hL', -⟩ := hiso
  subst hL'
  exact hypermapOfList_iso_map_injOn hinj hgood

/-- **HOL `JXBJOAB`**（tame_list.hl:3733-3744
`!L. ?Ln. iso_list (L,[]) (Ln,[])`，S6/A9 装配件）。

诚实收窄记账（typing-artifact，非 GIANT）：HOL 原文对任意类型 `A` 成立——
内容 = 经 `INJ_NUM_EXISTS`（tame_list.hl:3719，有限集的 num 编码）把载体
换成 `num`。tame 章 Lean spine 全域 ℕ-monomorphic（`fgraph ℕ`，GoodList/
hypermapOfList 均钉死 ℕ），类型更换义务在编码层已被吸收，恒等重标号 `id`
即为证人。跨类型推广（`[Countable α]` 的 `α → ℕ` 编码形）对 spine 消费侧
（A9 JCAJYDU 装配全在 ℕ 层）无消费点，不展开——`-- NEEDS` 不挂号。 -/
theorem JXBJOAB (L : fgraph ℕ) : ∃ Ln : fgraph ℕ, IsoListSpine L Ln [] [] :=
  ⟨L, id, fun _ _ _ _ h => h, by simp, rfl⟩

/-! ### §4 S6 重点件：DAKEFCC（`iso_restricted`，tame_list.hl:9343/:9360） -/

section IsoTransport

variable {α : Type*} [DecidableEq α] {β : Type*} [DecidableEq β]
  {H : Hypermap α} {K : Hypermap β} {f : α → β} {x : α}

omit [DecidableEq α] in
/-- `PermutesOn` 的 dart 外恒等（def 展开；Hypermap.lean:678
`PermutesOn f s := ∀ x ∉ s, f x = x`，HOL `res` 语义的 Lean 内置形）。 -/
theorem permutesOn_eq_of_notMem {p : Equiv.Perm α} {D : Finset α}
    (hp : PermutesOn p D) (hx : x ∉ D) : p x = x := hp x hx

omit [DecidableEq β] in
/-- 幂传输（私有）：dart 上的映射交换律提升到幂。 -/
private theorem perm_pow_transport {p : Equiv.Perm α} {q : Equiv.Perm β}
    (hp : PermutesOn p H.darts)
    (hcomm : ∀ y ∈ H.darts, q (f y) = f (p y)) :
    ∀ (n : ℕ) (x : α), x ∈ H.darts → (q ^ n) (f x) = f ((p ^ n) x) := by
  intro n
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
    intro x hx
    have hpx : p x ∈ H.darts := hp.apply_mem hx
    show (q ^ n) (q (f x)) = f ((p ^ n) (p x))
    rw [hcomm x hx, ih (p x) hpx]

omit [DecidableEq β] in
/-- 轨道传输（私有）：同构下的 orbit 恰为像轨道。 -/
private theorem perm_orbitMap_image {p : Equiv.Perm α} {q : Equiv.Perm β}
    (hp : PermutesOn p H.darts)
    (hcomm : ∀ y ∈ H.darts, q (f y) = f (p y))
    (hx : x ∈ H.darts) :
    orbitMap q (f x) = f '' orbitMap p x := by
  ext y
  simp only [orbitMap, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨n, hn⟩
    rw [perm_pow_transport hp hcomm n x hx] at hn
    exact ⟨(p ^ n) x, ⟨n, rfl⟩, hn⟩
  · rintro ⟨z, ⟨n, hz⟩, rfl⟩
    exact ⟨n, (perm_pow_transport hp hcomm n x hx).trans (congrArg f hz)⟩

omit [DecidableEq β] [DecidableEq α] in
/-- dart 内点 orbit ⊆ dart 集（`PermutesOn.pow_apply_mem`）。 -/
private theorem orbit_subset_darts {p : Equiv.Perm α} (D : Finset α)
    (hp : PermutesOn p D) (hx : x ∈ D) : orbitMap p x ⊆ (↑D : Set α) := by
  rintro y ⟨n, rfl⟩
  exact hp.pow_apply_mem n hx

/-- 路径点落在 dart 集（私有；`isPath` 对 n 归纳 + goOneStep 分情况）。 -/
private theorem isPath_mem_darts (H : Hypermap α) {p : ℕ → α} (h0 : p 0 ∈ H.darts) :
    ∀ n, H.isPath p n → ∀ i, i ≤ n → p i ∈ H.darts := by
  intro n
  induction n with
  | zero => intro _ i hi; rw [Nat.le_zero.mp hi]; exact h0
  | succ k ih =>
    intro hpath i hi
    by_cases hik : i = k + 1
    · subst hik
      obtain ⟨_, hstep⟩ := H.isPath_succ p k |>.mp hpath
      have hpd : p k ∈ H.darts := ih hpath.1 k (Nat.le_refl k)
      have hor : p (k + 1) = H.edgeMap (p k) ∨ p (k + 1) = H.nodeMap (p k) ∨
        p (k + 1) = H.faceMap (p k) := hstep
      rcases hor with hc | hc | hc
      · rw [hc]; exact H.edgeMap_permutes.apply_mem hpd
      · rw [hc]; exact H.nodeMap_permutes.apply_mem hpd
      · rw [hc]; exact H.faceMap_permutes.apply_mem hpd
    · exact ih hpath.1 i (Nat.lt_succ_iff.mp (lt_of_le_of_ne hi hik))

/-- 路径的像仍是路径（私有；逐步交换律）。 -/
private theorem isPath_image
    (hcomm : ∀ y ∈ H.darts, K.edgeMap (f y) = f (H.edgeMap y) ∧
      K.nodeMap (f y) = f (H.nodeMap y) ∧ K.faceMap (f y) = f (H.faceMap y))
    {p : ℕ → α} :
    ∀ n, H.isPath p n → (∀ i, i ≤ n → p i ∈ H.darts) →
      K.isPath (fun i => f (p i)) n := by
  intro n
  induction n with
  | zero => intro _ _; trivial
  | succ k ih =>
    intro hpath hmem
    rw [K.isPath_succ]
    refine ⟨ih hpath.1 (fun i hi => hmem i (le_trans hi (Nat.le_succ k))), ?_⟩
    have hor : p (k + 1) = H.edgeMap (p k) ∨ p (k + 1) = H.nodeMap (p k) ∨
      p (k + 1) = H.faceMap (p k) := hpath.2
    rcases hor with hc | hc | hc
    · exact Or.inl (by rw [hc, (hcomm (p k) (hmem k (Nat.le_succ k))).1])
    · exact Or.inr (Or.inl (by rw [hc, (hcomm (p k) (hmem k (Nat.le_succ k))).2.1]))
    · exact Or.inr (Or.inr (by rw [hc, (hcomm (p k) (hmem k (Nat.le_succ k))).2.2]))

/-- edge 轨道传输（Iso 拆件形）。 -/
private theorem iso_edge_image
    (hmaps : ∀ y ∈ H.darts, K.edgeMap (f y) = f (H.edgeMap y) ∧
      K.nodeMap (f y) = f (H.nodeMap y) ∧ K.faceMap (f y) = f (H.faceMap y))
    (hx : x ∈ H.darts) :
    K.edge (f x) = f '' H.edge x :=
  perm_orbitMap_image H.edgeMap_permutes (fun y hy => (hmaps y hy).1) hx

/-- node 轨道传输（Iso 拆件形）。 -/
private theorem iso_node_image
    (hmaps : ∀ y ∈ H.darts, K.edgeMap (f y) = f (H.edgeMap y) ∧
      K.nodeMap (f y) = f (H.nodeMap y) ∧ K.faceMap (f y) = f (H.faceMap y))
    (hx : x ∈ H.darts) :
    K.node (f x) = f '' H.node x :=
  perm_orbitMap_image H.nodeMap_permutes (fun y hy => (hmaps y hy).2.1) hx

/-- face 轨道传输（Iso 拆件形）。 -/
private theorem iso_face_image
    (hmaps : ∀ y ∈ H.darts, K.edgeMap (f y) = f (H.edgeMap y) ∧
      K.nodeMap (f y) = f (H.nodeMap y) ∧ K.faceMap (f y) = f (H.faceMap y))
    (hx : x ∈ H.darts) :
    K.face (f x) = f '' H.face x :=
  perm_orbitMap_image H.faceMap_permutes (fun y hy => (hmaps y hy).2.2) hx

omit [DecidableEq β] in
/-- 集族的像映射在族上单射（私有；族成员均为 dart 集子集 + f 在 dart 集上
单射时）。nodeSet/edgeSet/faceSet/setOfComponents 四处共用。 -/
private theorem injOn_image_of_setFamily {S : Set (Set α)}
    (hSsub : ∀ T, T ∈ S → ∀ z, z ∈ T → z ∈ (↑H.darts : Set α))
    (hinjE : ∀ a ∈ (↑H.darts : Set α), ∀ b ∈ (↑H.darts : Set α), f a = f b → a = b) :
    Set.InjOn (fun O : Set α => f '' O) S := by
  intro O1 hO1 O2 hO2 hEq
  ext z
  constructor
  · intro hz
    have hyd : z ∈ (↑H.darts : Set α) := hSsub O1 hO1 z hz
    have hmemO1 : f z ∈ (fun O : Set α => f '' O) O1 := Set.mem_image_of_mem f hz
    rw [hEq] at hmemO1
    simp only [Set.mem_image] at hmemO1
    obtain ⟨z', hz', hfz'⟩ := hmemO1
    have hzz : z' = z := hinjE z' (hSsub O2 hO2 z' hz') z hyd hfz'
    rw [hzz] at hz'
    exact hz'
  · intro hz
    have hyd : z ∈ (↑H.darts : Set α) := hSsub O2 hO2 z hz
    have hmemO2 : f z ∈ (fun O : Set α => f '' O) O2 := Set.mem_image_of_mem f hz
    rw [← hEq] at hmemO2
    simp only [Set.mem_image] at hmemO2
    obtain ⟨z', hz', hfz'⟩ := hmemO2
    have hzz : z' = z := hinjE z' (hSsub O1 hO1 z' hz') z hyd hfz'
    rw [hzz] at hz'
    exact hz'

/-- nodeSet 像传输（Iso 拆件形）。 -/
private theorem nodeSet_image_of_iso
    (hbij : Set.BijOn f (↑H.darts : Set α) (↑K.darts : Set β))
    (hmaps : ∀ y ∈ H.darts, K.edgeMap (f y) = f (H.edgeMap y) ∧
      K.nodeMap (f y) = f (H.nodeMap y) ∧ K.faceMap (f y) = f (H.faceMap y)) :
    K.nodeSet = (fun O : Set α => f '' O) '' H.nodeSet := by
  ext T
  simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hbij.2.2 (Finset.mem_coe.mpr hy)
    exact ⟨H.node x, ⟨x, hx, rfl⟩, (iso_node_image hmaps hx).symm⟩
  · rintro ⟨O, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨f x, Finset.mem_coe.mpr (hbij.1 (Finset.mem_coe.mpr hx)), ?_⟩
    exact iso_node_image hmaps hx

/-- edgeSet 像传输（Iso 拆件形）。 -/
private theorem edgeSet_image_of_iso
    (hbij : Set.BijOn f (↑H.darts : Set α) (↑K.darts : Set β))
    (hmaps : ∀ y ∈ H.darts, K.edgeMap (f y) = f (H.edgeMap y) ∧
      K.nodeMap (f y) = f (H.nodeMap y) ∧ K.faceMap (f y) = f (H.faceMap y)) :
    K.edgeSet = (fun O : Set α => f '' O) '' H.edgeSet := by
  ext T
  simp only [Hypermap.edgeSet, setOfOrbits, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hbij.2.2 (Finset.mem_coe.mpr hy)
    exact ⟨H.edge x, ⟨x, hx, rfl⟩, (iso_edge_image hmaps hx).symm⟩
  · rintro ⟨O, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨f x, Finset.mem_coe.mpr (hbij.1 (Finset.mem_coe.mpr hx)), ?_⟩
    exact iso_edge_image hmaps hx

/-- faceSet 像传输（Iso 拆件形）。 -/
private theorem faceSet_image_of_iso
    (hbij : Set.BijOn f (↑H.darts : Set α) (↑K.darts : Set β))
    (hmaps : ∀ y ∈ H.darts, K.edgeMap (f y) = f (H.edgeMap y) ∧
      K.nodeMap (f y) = f (H.nodeMap y) ∧ K.faceMap (f y) = f (H.faceMap y)) :
    K.faceSet = (fun O : Set α => f '' O) '' H.faceSet := by
  ext T
  simp only [Hypermap.faceSet, setOfOrbits, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hbij.2.2 (Finset.mem_coe.mpr hy)
    exact ⟨H.face x, ⟨x, hx, rfl⟩, (iso_face_image hmaps hx).symm⟩
  · rintro ⟨O, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨f x, Finset.mem_coe.mpr (hbij.1 (Finset.mem_coe.mpr hx)), ?_⟩
    exact iso_face_image hmaps hx

/-- 连通分支传输（私有；⊆ 向把 K 路径逐点拉回 H、⊇ 向把 H 路径推前为 K）。 -/
private theorem iso_combComponent_image
    (hbij : Set.BijOn f (↑H.darts : Set α) (↑K.darts : Set β))
    (hmaps : ∀ y ∈ H.darts, K.edgeMap (f y) = f (H.edgeMap y) ∧
      K.nodeMap (f y) = f (H.nodeMap y) ∧ K.faceMap (f y) = f (H.faceMap y))
    (hx : x ∈ H.darts) :
    K.combComponent (f x) = f '' H.combComponent x := by
  have hinj : Set.InjOn f (↑H.darts : Set α) := hbij.2.1
  have hmapsTo : ∀ y ∈ (↑H.darts : Set α), f y ∈ (↑K.darts : Set β) := hbij.1
  ext y
  simp only [Hypermap.mem_combComponent, Hypermap.isInComponent, Set.mem_image]
  constructor
  · -- ⊆：K 路径逐点 SurjOn 拉回 H 路径
    rintro ⟨p, n, hp0, hpn, hpathK⟩
    have hp0K : p 0 ∈ K.darts := by rw [hp0]; exact Finset.mem_coe.mpr (hmapsTo x hx)
    have hdartsK : ∀ i, i ≤ n → p i ∈ K.darts := isPath_mem_darts K hp0K n hpathK
    have hex : ∀ i, ∃ z, z ∈ H.darts ∧ (i ≤ n → f z = p i) := by
      intro i
      by_cases hi : i ≤ n
      · obtain ⟨z, hz, hfz⟩ := hbij.2.2 (Finset.mem_coe.mpr (hdartsK i hi))
        exact ⟨z, hz, fun _ => hfz⟩
      · exact ⟨x, hx, fun hle => absurd hle hi⟩
    choose q hqD hqF using hex
    have hq0 : q 0 = x :=
      hinj (Finset.mem_coe.mpr (hqD 0)) (Finset.mem_coe.mpr hx)
        (by rw [hqF 0 (Nat.zero_le n), hp0])
    have hstep : ∀ j, j + 1 ≤ n →
        q (j + 1) = H.edgeMap (q j) ∨ q (j + 1) = H.nodeMap (q j) ∨
          q (j + 1) = H.faceMap (q j) := by
      intro j hj
      have hqj : q j ∈ H.darts := hqD j
      have hqj1 : q (j + 1) ∈ H.darts := hqD (j + 1)
      have hor : p (j + 1) = K.edgeMap (p j) ∨ p (j + 1) = K.nodeMap (p j) ∨
        p (j + 1) = K.faceMap (p j) := K.goOneStep_of_isPath hpathK hj
      rcases hor with hc | hc | hc
      · refine Or.inl (hinj (Finset.mem_coe.mpr hqj1)
          (Finset.mem_coe.mpr (H.edgeMap_permutes.apply_mem hqj)) ?_)
        rw [hqF (j + 1) hj, hc, ← hqF j (Nat.le_of_succ_le hj), (hmaps (q j) hqj).1]
      · refine Or.inr (Or.inl (hinj (Finset.mem_coe.mpr hqj1)
          (Finset.mem_coe.mpr (H.nodeMap_permutes.apply_mem hqj)) ?_))
        rw [hqF (j + 1) hj, hc, ← hqF j (Nat.le_of_succ_le hj), (hmaps (q j) hqj).2.1]
      · refine Or.inr (Or.inr (hinj (Finset.mem_coe.mpr hqj1)
          (Finset.mem_coe.mpr (H.faceMap_permutes.apply_mem hqj)) ?_))
        rw [hqF (j + 1) hj, hc, ← hqF j (Nat.le_of_succ_le hj), (hmaps (q j) hqj).2.2]
    have hall : ∀ m, m ≤ n → H.isPath q m := by
      intro m
      induction m with
      | zero => intro _; trivial
      | succ k ihk =>
        intro hle
        rw [H.isPath_succ]
        exact ⟨ihk (Nat.le_of_succ_le hle), hstep k hle⟩
    refine ⟨q n, ⟨q, n, hq0, rfl, hall n (Nat.le_refl n)⟩, ?_⟩
    rw [hqF n (Nat.le_refl n)]
    exact hpn
  · -- ⊇：H 路径推前为 K 路径
    rintro ⟨z, ⟨q, n, hq0, hqn, hpathH⟩, rfl⟩
    have hq0D : q 0 ∈ H.darts := by rw [hq0]; exact hx
    refine ⟨fun i => f (q i), n, congrArg f hq0, congrArg f hqn, ?_⟩
    exact isPath_image hmaps n hpathH (isPath_mem_darts H hq0D n hpathH)

/-- setOfComponents 像传输（Iso 拆件形）。 -/
private theorem setOfComponents_image_of_iso
    (hbij : Set.BijOn f (↑H.darts : Set α) (↑K.darts : Set β))
    (hmaps : ∀ y ∈ H.darts, K.edgeMap (f y) = f (H.edgeMap y) ∧
      K.nodeMap (f y) = f (H.nodeMap y) ∧ K.faceMap (f y) = f (H.faceMap y)) :
    K.setOfComponents = (fun O : Set α => f '' O) '' H.setOfComponents := by
  ext T
  simp only [Hypermap.setOfComponents, Hypermap.setPartComponents, Set.mem_setOf_eq,
    Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hbij.2.2 (Finset.mem_coe.mpr hy)
    exact ⟨H.combComponent x, ⟨x, hx, rfl⟩, (iso_combComponent_image hbij hmaps hx).symm⟩
  · rintro ⟨O, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨f x, Finset.mem_coe.mpr (hbij.1 (Finset.mem_coe.mpr hx)), ?_⟩
    rw [iso_combComponent_image hbij hmaps hx]

end IsoTransport

/-- **HOL `iso_restricted`**（tame_list.hl:9343-9353）单向：`is_restricted`
沿 `iso` 正向运输（九合取项逐项传输，见模块头注证明要点）。 -/
private theorem iso_isRestricted_of_iso {α : Type*} [DecidableEq α]
    {β : Type*} [DecidableEq β] {H : Hypermap α} {K : Hypermap β}
    (h : H.Iso K) (hres : H.IsRestricted) : K.IsRestricted := by
  obtain ⟨f, hbij, hmaps⟩ := h
  have hmapsTo : ∀ y ∈ (↑H.darts : Set α), f y ∈ (↑K.darts : Set β) := hbij.1
  have hinj : Set.InjOn f (↑H.darts : Set α) := hbij.2.1
  have hsurj : ∀ y ∈ (↑K.darts : Set β), ∃ z ∈ H.darts, f z = y := hbij.2.2
  -- 1. dart 集非空
  have hdarts : K.darts ≠ ∅ := by
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hres.1
    exact Finset.nonempty_iff_ne_empty.mp
      (show K.darts.Nonempty from ⟨f x, Finset.mem_coe.mp (hmapsTo x hx)⟩)
  -- 2. Plain：dart 上由交换律与 H.Plain 给出，dart 外由 PermutesOn 给出
  have hplainK : K.Plain := by
    have hHp : ∀ x, x ∈ H.darts → H.edgeMap (H.edgeMap x) = x := by
      intro x _
      have h2 : (H.edgeMap * H.edgeMap) x = (1 : Equiv.Perm α) x :=
        congrArg (· x) hres.plain
      simpa using h2
    refine Equiv.Perm.ext fun d => ?_
    by_cases hd : d ∈ K.darts
    · obtain ⟨x, hx, rfl⟩ := hsurj d (Finset.mem_coe.mpr hd)
      have h2 : K.edgeMap (f (H.edgeMap x)) = f (H.edgeMap (H.edgeMap x)) :=
        (hmaps (H.edgeMap x) (H.edgeMap_permutes.apply_mem hx)).1
      show K.edgeMap (K.edgeMap (f x)) = f x
      rw [(hmaps x hx).1, h2, hHp x hx]
    · show K.edgeMap (K.edgeMap d) = d
      rw [K.edgeMap_permutes d hd, K.edgeMap_permutes d hd]
  -- 3. 计数层传输：darts.card / nodeSet / edgeSet / faceSet / 组件数
  have hcard : H.darts.card = K.darts.card := by
    have himg : (fun z => f z) '' (↑H.darts : Set α) = (↑K.darts : Set β) := by
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hmapsTo z hz
      · intro hy
        obtain ⟨z, hz, rfl⟩ := hsurj y hy
        exact ⟨z, hz, rfl⟩
    have h1 : (↑H.darts : Set α).ncard = (↑K.darts : Set β).ncard := by
      rw [← himg, hinj.ncard_image]
    calc H.darts.card = (↑H.darts : Set α).ncard := (Set.ncard_coe_finset H.darts).symm
      _ = (↑K.darts : Set β).ncard := h1
      _ = K.darts.card := Set.ncard_coe_finset K.darts
  have hnodeSetFin : H.nodeSet.Finite := setOfOrbits_finite H.darts H.nodeMap
  have hedgeSetFin : H.edgeSet.Finite := setOfOrbits_finite H.darts H.edgeMap
  have hfaceSetFin : H.faceSet.Finite := setOfOrbits_finite H.darts H.faceMap
  have hsubNode : ∀ T ∈ H.nodeSet, T ⊆ (↑H.darts : Set α) := by
    intro T hT z hz
    simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq] at hT
    obtain ⟨x, hx, rfl⟩ := hT
    exact orbit_subset_darts H.darts H.nodeMap_permutes hx hz
  have hsubEdge : ∀ T ∈ H.edgeSet, T ⊆ (↑H.darts : Set α) := by
    intro T hT z hz
    simp only [Hypermap.edgeSet, setOfOrbits, Set.mem_setOf_eq] at hT
    obtain ⟨x, hx, rfl⟩ := hT
    exact orbit_subset_darts H.darts H.edgeMap_permutes hx hz
  have hsubFace : ∀ T ∈ H.faceSet, T ⊆ (↑H.darts : Set α) := by
    intro T hT z hz
    simp only [Hypermap.faceSet, setOfOrbits, Set.mem_setOf_eq] at hT
    obtain ⟨x, hx, rfl⟩ := hT
    exact orbit_subset_darts H.darts H.faceMap_permutes hx hz
  have hinjOnNodeSet : Set.InjOn (fun O : Set α => f '' O) H.nodeSet :=
    injOn_image_of_setFamily hsubNode hinj
  have hinjOnEdgeSet : Set.InjOn (fun O : Set α => f '' O) H.edgeSet :=
    injOn_image_of_setFamily hsubEdge hinj
  have hinjOnFaceSet : Set.InjOn (fun O : Set α => f '' O) H.faceSet :=
    injOn_image_of_setFamily hsubFace hinj
  have hnn : K.numberOfNodes = H.numberOfNodes := by
    show K.nodeSet.ncard = H.nodeSet.ncard
    rw [nodeSet_image_of_iso hbij hmaps]
    exact hinjOnNodeSet.ncard_image
  have hne : K.numberOfEdges = H.numberOfEdges := by
    show K.edgeSet.ncard = H.edgeSet.ncard
    rw [edgeSet_image_of_iso hbij hmaps]
    exact hinjOnEdgeSet.ncard_image
  have hnf : K.numberOfFaces = H.numberOfFaces := by
    show K.faceSet.ncard = H.faceSet.ncard
    rw [faceSet_image_of_iso hbij hmaps]
    exact hinjOnFaceSet.ncard_image
  have hcomp : K.numberOfComponents = H.numberOfComponents := by
    have hsub : ∀ T ∈ H.setOfComponents, T ⊆ (↑H.darts : Set α) := by
      intro T hT z hz
      simp only [Hypermap.setOfComponents, Hypermap.setPartComponents,
        Set.mem_setOf_eq] at hT
      obtain ⟨x, hx, rfl⟩ := hT
      simp only [Hypermap.mem_combComponent, Hypermap.isInComponent] at hz
      obtain ⟨p, n, hp0, hpn, hpath⟩ := hz
      have h0 : p 0 ∈ H.darts := by rw [hp0]; exact hx
      have hpnD : p n ∈ H.darts := isPath_mem_darts H h0 n hpath n (Nat.le_refl n)
      rwa [hpn] at hpnD
    have hinjOnComp : Set.InjOn (fun O : Set α => f '' O) H.setOfComponents :=
      injOn_image_of_setFamily hsub hinj
    show K.setOfComponents.ncard = H.setOfComponents.ncard
    rw [setOfComponents_image_of_iso hbij hmaps]
    exact hinjOnComp.ncard_image
  have hplanarK : K.Planar := by
    show K.numberOfNodes + K.numberOfEdges + K.numberOfFaces
      = K.darts.card + 2 * K.numberOfComponents
    rw [hnn, hne, hnf, ← hcard, hcomp]
    exact hres.planar
  have hconnK : K.Connected := hcomp.trans hres.connected
  -- 4. Simple：交集轨道的像交集
  have hsimpleK : K.Simple := by
    have hs := hres.simple
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y (Finset.mem_coe.mpr hy)
    have hnd : H.node x ⊆ (↑H.darts : Set α) :=
      orbit_subset_darts H.darts H.nodeMap_permutes hx
    have hfd : H.face x ⊆ (↑H.darts : Set α) :=
      orbit_subset_darts H.darts H.faceMap_permutes hx
    have hinjU : Set.InjOn f (H.node x ∪ H.face x) := fun a ha b hb heq =>
      hinj (Set.union_subset hnd hfd ha) (Set.union_subset hnd hfd hb) heq
    have hinter : (f '' H.node x) ∩ (f '' H.face x) = f '' (H.node x ∩ H.face x) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_image]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, b, hb, hfab⟩
        have hab : a = b :=
          hinjU (Set.mem_union_left _ ha) (Set.mem_union_right _ hb) hfab.symm
        exact ⟨b, ⟨hab ▸ ha, hb⟩, hfab⟩
      · rintro ⟨c, ⟨hc1, hc2⟩, rfl⟩
        exact ⟨⟨c, hc1, rfl⟩, c, hc2, rfl⟩
    rw [iso_node_image hmaps hx, iso_face_image hmaps hx, hinter, hs x hx,
      Set.image_singleton]
  -- 5. no-double-joins / 边·节点非退化 / face ≥ 3
  have hndjK : K.IsNoDoubleJoins := by
    have hndj := hres.noDoubleJoins
    intro u v hu hv1 hv2
    obtain ⟨u0, hu0, rfl⟩ := hsurj u (Finset.mem_coe.mpr hu)
    rw [iso_node_image hmaps hu0] at hv1
    obtain ⟨w, hw1, rfl⟩ := hv1
    have hwd : w ∈ H.darts :=
      orbit_subset_darts H.darts H.nodeMap_permutes hu0 hw1
    rw [(hmaps w hwd).1, (hmaps u0 hu0).1,
      iso_node_image hmaps (H.edgeMap_permutes.apply_mem hu0)] at hv2
    simp only [Set.mem_image] at hv2
    obtain ⟨z, hz1, hz2⟩ := hv2
    have hzd : z ∈ H.darts :=
      orbit_subset_darts H.darts H.nodeMap_permutes
        (H.edgeMap_permutes.apply_mem hu0) hz1
    have hzw : z = H.edgeMap w :=
      hinj (Finset.mem_coe.mpr hzd)
        (Finset.mem_coe.mpr (H.edgeMap_permutes.apply_mem hwd)) hz2
    rw [hzw] at hz1
    exact congrArg f (hndj u0 w hu0 hw1 hz1)
  have heneK : K.EdgeNondegenerate := by
    have he := hres.edgeNondegenerate
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y (Finset.mem_coe.mpr hy)
    rw [(hmaps x hx).1]
    intro hcon
    exact he x hx (hinj (Finset.mem_coe.mpr (H.edgeMap_permutes.apply_mem hx))
      (Finset.mem_coe.mpr hx) hcon)
  have hnneK : K.NodeNondegenerate := by
    have he := hres.nodeNondegenerate
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y (Finset.mem_coe.mpr hy)
    rw [(hmaps x hx).2.1]
    intro hcon
    exact he x hx (hinj (Finset.mem_coe.mpr (H.nodeMap_permutes.apply_mem hx))
      (Finset.mem_coe.mpr hx) hcon)
  have hface3 : ∀ y ∈ K.darts, 3 ≤ (K.face y).ncard := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y (Finset.mem_coe.mpr hy)
    rw [iso_face_image hmaps hx]
    have hfd : H.face x ⊆ (↑H.darts : Set α) :=
      orbit_subset_darts H.darts H.faceMap_permutes hx
    have hinjFace : Set.InjOn f (H.face x) := fun a ha b hb heq => hinj (hfd ha) (hfd hb) heq
    rw [hinjFace.ncard_image]
    exact hres.three_le_ncard_face hx
  refine ⟨hdarts, hplanarK, hplainK, hconnK,
    hsimpleK, hndjK, heneK, hnneK, hface3⟩

/-- **HOL `DAKEFCC`**（tame_list.hl:9360 = `iso_restricted` :9343-9353
`!H K. iso H K ==> (is_restricted H <=> is_restricted K)`，S6/A9 装配件）：
restricted 性是超映射 Iso 不变量。证明要点见模块头注；`Nonempty α` 为
HOL 类型恒非空的折算（H.IsRestricted 本身蕴含之；`Iso.symm` 需要它把
dart 间双射延拓成全函数）。 -/
theorem DAKEFCC {α : Type*} [DecidableEq α] {β : Type*} [DecidableEq β]
    {H : Hypermap α} {K : Hypermap β} [Nonempty α] (h : H.Iso K) :
    H.IsRestricted ↔ K.IsRestricted :=
  ⟨iso_isRestricted_of_iso h, iso_isRestricted_of_iso h.symm⟩

/-- HOL 原名 `iso_restricted` 的别名件（逐字同体，供下游按 HOL 名检索）。 -/
theorem isoRestricted {α : Type*} [DecidableEq α] {β : Type*} [DecidableEq β]
    {H : Hypermap α} {K : Hypermap β} [Nonempty α] (h : H.Iso K) :
    H.IsRestricted ↔ K.IsRestricted := DAKEFCC h

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.GNBEVVU
#print axioms Kepler.Text.TameSpine.JXBJOAB
#print axioms Kepler.Text.TameSpine.DAKEFCC
#print axioms Kepler.Text.TameSpine.PEUTLZH
-/
