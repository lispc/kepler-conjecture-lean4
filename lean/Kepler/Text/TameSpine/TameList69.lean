/-
  Kepler.Text.TameSpine.TameList69 — B3 D 链第十批：RXOKSKC 五槽 + A9 主件落地
  （HOL 对账段：RXOKSKC.hl :523-:1105；接续批 68 = TameList68.lean 516 行，
  md5 2168e7b76e945112cd5c1d376bca6781）。本批 = RXOKSKC.hl 章收官。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ 落点：32 声明（25 公开 = 24 定理 + 1 def；7 枚 §0' 私桥），零 sorry、
  │ 零 axiom 声明；`lake build Kepler.Text.TameSpine.TameList69` 9501 jobs
  │ 全绿（clone /tmp/p4t21，单发串行、零旗标、零 -K）。
  │ axiom 探针 25/25 全公开件 = [propext, Classical.choice, Quot.sound]
  │ 标准三内，零 sorryAx（快照 t69_axiom_audit.log 全文）。
  │
  │ 五槽到达（HOL 顺序 (a)→(b)→(c)→(d)；证明内部把 (c) 提到 (b) 之前，
  │ 机理记档见下）：
  │ (a) uniq s / good_list：allUniq_L（HOL :542-:554）+ uniqDarts_L
  │   （UNIQ_LIST_OF_DARTS :25 实例化；跨片不交 = f_pair 分解 +
  │   ONE_TO_ONE_DART 钉同面 + hSinj 反克）+ swapDart_mem（SYM_LIST_DART
  │   :507 换位闭包）+ goodList_L（:556-:651）。
  │ (b) good_list_nodes：goodListNodes_L（tame_defs2.hl:38 / HOL :723-:783）
  │   = `nodeSet (hypermapOfListG L hL) = rxNodesOfListSet L`；经 §2 iso 的
  │   节点轨道共轭（isoMap_node_pow / orbit_iso）把每条 N-轨道转移为
  │   FST-fiber（isoMap_image_node），再以 mem_elements_iff 换指标集。
  │ (c) iso e/n/f 三槽：isoMap（x ↦ (node x, node (F x))）+
  │   isoMap_bijOn（MapsTo/SurjOn/InjOn 三槽，单射 = ONE_TO_ONE_DART）+
  │   isoMap_edge（:906-:923，SYM_LIST_DART）+ isoMap_node（:928-:1065 全章
  │   最重段：rxFindFace_eq_of_mem 定位 + f_prev_pair + SYM_LIST_DART +
  │   pow_pred_succ_apply 指标折算）+ isoMap_face（:1073-:1089：
  │   nextElListPairsG + f_next）+ iso_hypermapOfListG =
  │   `H.Iso (hypermapOfListG D.L hL)`。
  │ (d) RXOKSKC（:523）：`∃ L hL, all uniq L ∧ good_list_nodes L ∧
  │   H.Iso (hypermap_of_list L)` 全件落地。**A9 接口意义**：TameSpine 线
  │   对 Assembly 接口 9（tame GIANT）的第一次实质供数——iso 把几何
  │   hypermap 钉到有限 list 表示（dart x ↦ (node x, node (F x))；边 =
  │   换位、节点 = FST 纤维、面 = f_list），装配线可据此把任意受限
  │   hypermap 读档为有限数据，与 FanHypermapIsoList（Assembly.lean:183）
  │   的 A9 出口合流。
  │
  │ 底座消费（在册不重落）：TameList67 hypermapOfListG 四槽 + bijOn 三件 +
  │ darts_eq_iUnion_* / iterateMapValuation / pow_mod_eq / face_eq_orbit_range /
  │ hypMapsInvs / prevEl_eq_getD_idxOf / nextElListPairsG；TameList68
  │ RxOkData.L + f_* 原子件；TameList66 rxUniqListOfDarts / oneToOneDart /
  │ existsListFaceNodeFunc / listCorFaceSet1；TameList65 symListDart。
  │ 本文件供给批 70：goodList_L / goodListNodes_L / iso_hypermapOfListG /
  │ RXOKSKC 四主件 + isoMap 桥群。
  └──────────────────────────────────────────────────────────────

  证明顺序偏差记档（非语句失真）：HOL 在 :723 先证 good_list_nodes、:782 再
  证 iso；本批先证 iso（§2）再经 iso 转移证 good_list_nodes（§3）。原因是
  good_list_nodes 是几何条件而非 good_list 的纯组合推论——反例：两球面仅
  共用顶点 a 的 list（[[a,b,c],[b,a,d],[c,b,d],[a,c,d]] 并
  [[a,e,f],[e,a,g],[f,e,g],[a,f,g]]）满足 good_list（dart 无重 + 换位闭包）
  但 a 的 FST-fiber 分裂为两条 N-轨道；必须消费 H 的连通/面覆盖（hScov）
  经 iso 把轨道与纤维对齐。语句与 HOL 逐字对应，仅证明路线不同。

  新雷区（本批实测记档，编号承批 68 的 #177）：
  - #178 namespace 内 `H` 未声明为 section 变量：`namespace RxOkData` 内直接
    写 `(D : RxOkData H)` 会把 H 自动绑定成 `{H : Hypermap ?α}`（?α 与
    section 的 α 脱钩），`D.L` 的 `[DecidableEq α]` 卡在元变量上
    （"typeclass instance problem is stuck DecidableEq ?m"），并让后续
    `def isoMap` 级联成 "Invalid field"。RxOkData 内部必须补
    `variable {H : Hypermap α}`（TameList68 正是这样写的）。
  - #179 `Set.mem_image` 方向：`y ∈ f '' s ↔ ∃ a, a ∈ s ∧ f a = y`（像在
    左），`refine ⟨x, hx, ?_⟩` 的目标是 `f x = y`；nodeSet 反向包含若按
    直觉写 `orbit = isoImage` 会与目标相反，须 `(orbit_iso …).symm`。
  - #180 `face_eq_orbit_range` 的 `Set.mem_image` 元是 beta-redex
    `(fun k => (F^k) y) i = x`：直接 `rw [hiy]` 报 pattern 不匹配（目标里
    是 `(F^i) y`），须先 `simp only [] at hiy` 做 beta 归约
    （swapDart_mem / isoMap_mem / mem_elements_iff 三处实测）。
  - #181 `rw` 多重改写顺序与 def 穿透：def 应用 `D.isoMap z` 不直接展开，
    需 `show` 展开形或 `isoMap_pow` 显式桥；且 `rw [hrhs, hsym.1, hzp,
    hsym.2]` 中 hzp 若先跑会改写 hsym.2 的匹配位（pattern 失配），正确
    顺序 = `rw [hrhs, hsym.1, hsym.2, hzp]`。
  - #182 `H.node_subset_darts` 的显式第二参是 membership proof（x 隐式）：
    `H.node_subset_darts z hz hw` 报应用类型错，正确 `H.node_subset_darts hz hw`。
  - #183 Finset 成员 vs Set 成员：`rw [darts_hypermapOfListG]` 对目标
    `d ∈ G.darts`（Finset 成员）不匹配；先
    `have h : d ∈ (↑G.darts : Set _) := hd` 再 rw。同面复发 #165：
    `rw [rxElementsOfList, …]` 不解 def，用 `change` 做 delta 展开。

  批 70 接续点（精确）：
  - RXOKSKC.hl :523-:1105 全章收官（本章最后一行即 RXOKSKC 主件）；本文件
    末 `end Kepler.Text.TameSpine` 之后无遗留子目标。
  - 下一站 = B3 D 链下一 HOL 章（由编排者按总账裁定）；本文件可直接被消费
    的四主件 = `RxOkData.goodList_L` / `RxOkData.goodListNodes_L` /
    `RxOkData.iso_hypermapOfListG` / `RXOKSKC`。
  - 若编排者续接装配侧：A9 出口折算走 Keystone.hypermapIso_of_iso
    （Assembly.HypermapIso ↔ Hypermap.Iso），无需重证。
-/
import Kepler.Text.TameSpine.TameList68

/-! # RXOKSKC 五槽（uniq s / good_list / good_list_nodes / iso e-n-f）+ 主件

HOL 对账：`RXOKSKC.hl:523-:1105`。
-/

namespace Kepler.Text.TameSpine

variable {α : Type*} [DecidableEq α]

open Kepler.Assembly (listPairs nextEl prevEl)


/-! ### §0' 本地私桥（TameList65/67/68 的 private 件跨模块不可见，按批 63
§0' 体例逐字本地复制；命名加 69 后缀避撞） -/

/-- find? 命中 l' ⟹ rxFindFace = listPairs l' 且 d 落其中
（TameList67 `rxFindFace_some` 同体复制）。 -/
private theorem rxFindFace_some69 {L : List (List α)} {d : α × α} {l' : List α}
    (hfeq : (L.find? fun l => decide (d ∈ listPairs l)) = some l') :
    rxFindFace L d = listPairs l' ∧ d ∈ listPairs l' := by
  constructor
  · unfold rxFindFace
    rw [hfeq]
    rfl
  · exact of_decide_eq_true
      (List.find?_some (p := fun l => decide (d ∈ listPairs l)) hfeq)

/-- find? 命中唯一性（TameList67 `rxFindFace_eq_of_mem` 同体复制）：
d 落某面片的 pair 列表 ⟹ findFace 命中的就是该列表。 -/
private theorem rxFindFace_eq_of_mem69 {L : List (List α)} (hn : (rxListOfDarts L).Nodup)
    {l : List α} (hl : l ∈ L) {d : α × α} (hd : d ∈ listPairs l) :
    rxFindFace L d = listPairs l := by
  have hflat : ((L.map listPairs).flatten).Nodup := hn
  by_cases hval : (L.find? fun l => decide (d ∈ listPairs l)) = none
  · rw [List.find?_eq_none] at hval
    have hnc := hval l hl
    simp at hnc
    exact absurd hd hnc
  · obtain ⟨l', hl''⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : (L.find? fun l => decide (d ∈ listPairs l)) = some l' := hl''.symm
    obtain ⟨heq, hdl'⟩ := rxFindFace_some69 hfeq
    rw [heq]
    refine TameLp.flatten_nodup_inj hflat (List.mem_map.mpr
      ⟨l', List.mem_of_find?_eq_some hfeq, rfl⟩)
      (List.mem_map.mpr ⟨l, hl, rfl⟩) hdl' hd

/-- `edgeMap = nodeMap ∘ faceMap` 的点态形（TameList65 私桥同体复制）。 -/
private theorem edgeMap_apply69 (H : Hypermap α) (hp : H.Plain) (w : α) :
    H.edgeMap w = H.nodeMap (H.faceMap w) := by
  rw [H.plain_iff_edgeMap_eq.1 hp]
  rfl

omit [DecidableEq α] in
/-- `(a % n + 1) % n = (a + 1) % n`（TameList68 `mod_succ_mod68` 同体复制）。 -/
private theorem mod_succ_mod69 (a n : ℕ) (hn : 0 < n) :
    (a % n + 1) % n = (a + 1) % n := by
  rcases Nat.lt_or_ge 1 n with h2 | h2
  · rw [Nat.add_mod a 1 n, Nat.mod_eq_of_lt h2]
  · have hn1 : n = 1 := by omega
    subst hn1
    simp

omit [DecidableEq α] in
/-- `((a + n - 1) % n + 1) % n = a % n`（TameList68 `mod_pred_succ68` 同体复制）。 -/
private theorem mod_pred_succ69 (a n : ℕ) (hn : 0 < n) :
    ((a + n - 1) % n + 1) % n = a % n := by
  rw [mod_succ_mod69 _ _ hn]
  have hk : a + n - 1 + 1 = a + n := by omega
  rw [hk, Nat.add_mod a n n, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-- 面轨道前进一步后再折回：`F^(p+1) y = F^i y`（p = (i + CARD - 1) % CARD；
iso n 槽的指标折算件）。 -/
private theorem pow_pred_succ_apply (H : Hypermap α) (y : α) (i : ℕ)
    (hiC : i < (H.face y).ncard) :
    (H.faceMap ^ ((i + (H.face y).ncard - 1) % (H.face y).ncard + 1)) y =
      (H.faceMap ^ i) y := by
  have hC : 0 < (H.face y).ncard := lt_of_le_of_lt (Nat.zero_le i) hiC
  have hC0 : (H.face y).ncard ≠ 0 := Nat.ne_of_gt hC
  rw [← pow_mod_eq hC0 (H.pow_card_face_apply_self y)
      ((i + (H.face y).ncard - 1) % (H.face y).ncard + 1),
    mod_pred_succ69 i (H.face y).ncard hC, Nat.mod_eq_of_lt hiC]


namespace RxOkData

variable {H : Hypermap α}

/-! ### §1 槽 (a)：`all uniq L`（uniq s）+ `good_list L`

HOL 对账 `RXOKSKC.hl:542-:554`（all uniq L）、`:556-:651`（good_list L：
非空 / uniq L / UNIQ_LIST_OF_DARTS / SYM_LIST_DART 换位闭包）。 -/

/-- **槽 (a) 之一**：`L` 逐片无重（HOL `all uniq L`；`f_nodup` + `hSd`）。 -/
theorem allUniq_L (D : RxOkData H) : ∀ l ∈ D.L, l.Nodup := by
  intro l hl
  obtain ⟨x, hx, rfl⟩ := D.mem_L.mp hl
  exact D.f_nodup (D.hSd x hx)

/-- 不同代表点的面片 pair 表两两不交（HOL :618-:651 的交集空论证：
pair 重合 ⟹ ONE_TO_ONE_DART 钉出同面 ⟹ hSinj 反克 a ≠ b）。 -/
private theorem disjoint_listPairs_faces (D : RxOkData H) {a b : α}
    (ha : a ∈ D.S) (hb : b ∈ D.S) (hab : a ≠ b) :
    List.Disjoint (listPairs (D.f a)) (listPairs (D.f b)) := by
  intro e hea heb
  have haD : a ∈ H.darts := D.hSd a ha
  have hbD : b ∈ H.darts := D.hSd b hb
  obtain ⟨i, _hiC, heqa⟩ := D.f_pair haD hea
  obtain ⟨j, _hjC, heqb⟩ := D.f_pair hbD heb
  have hpair : (H.node ((H.faceMap ^ i) a), H.node ((H.faceMap ^ (i + 1)) a)) =
      (H.node ((H.faceMap ^ j) b), H.node ((H.faceMap ^ (j + 1)) b)) := by
    rw [← heqa, ← heqb]
  have h1 : H.node ((H.faceMap ^ i) a) = H.node ((H.faceMap ^ j) b) :=
    congrArg Prod.fst hpair
  have h2 : H.node ((H.faceMap ^ (i + 1)) a) = H.node ((H.faceMap ^ (j + 1)) b) :=
    congrArg Prod.snd hpair
  have h2' : H.node (H.faceMap ((H.faceMap ^ i) a)) =
      H.node (H.faceMap ((H.faceMap ^ j) b)) := by
    simpa [pow_succ', Equiv.Perm.mul_apply] using h2
  have hziD : (H.faceMap ^ i) a ∈ H.darts := H.faceMap_permutes.pow_apply_mem i haD
  have hzjD : (H.faceMap ^ j) b ∈ H.darts := H.faceMap_permutes.pow_apply_mem j hbD
  have heqij : (H.faceMap ^ i) a = (H.faceMap ^ j) b :=
    oneToOneDart H D.hr hziD hzjD h1 h2'
  have hface : H.face a = H.face b := by
    calc H.face a = H.face ((H.faceMap ^ i) a) :=
          H.face_eq_of_mem (H.pow_faceMap_mem_face a i)
      _ = H.face ((H.faceMap ^ j) b) := by rw [heqij]
      _ = H.face b := (H.face_eq_of_mem (H.pow_faceMap_mem_face b j)).symm
  exact hab (D.hSinj a ha b hb hface)

/-- **槽 (a) 之二**：`(list_of_darts L).Nodup` = HOL `UNIQ_LIST_OF_DARTS`
（RXOKSKC.hl:25，批 66 在册）在 `L := D.L` 的实例化：三前件由
`L_nodup` / `allUniq_L` / `disjoint_listPairs_faces` 供。 -/
theorem uniqDarts_L (D : RxOkData H) : (rxListOfDarts D.L).Nodup := by
  apply rxUniqListOfDarts D.L_nodup
  · intro l hl
    obtain ⟨a, ha, rfl⟩ := D.mem_L.mp hl
    exact D.f_nodup (D.hSd a ha)
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := D.mem_L.mp hx
    obtain ⟨b, hb, rfl⟩ := D.mem_L.mp hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    exact D.disjoint_listPairs_faces ha hb hab

/-- **槽 (a) 之三**：good_list 的换位闭包（HOL :651-:720 SYM_LIST_DART 段）：
dart `d` 落某面片 ⟹ `(d.2, d.1)` 亦落 dart 表。证明 = `f_pair` 写
`d = (node F^i a, node F^(i+1) a)`；SYM_LIST_DART（z = F^i a）把换位对
重写成下一节点对 `(node z1, node (F z1))`；`hScov` 把 z1 送入某面片后
`f_pair_mem` 收。 -/
theorem swapDart_mem (D : RxOkData H) {d : Set α × Set α}
    (hd : d ∈ rxListOfDarts D.L) : (d.2, d.1) ∈ rxListOfDarts D.L := by
  obtain ⟨l, hl, hdl⟩ := rxMemListDarts.mp hd
  obtain ⟨a, haS, rfl⟩ := D.mem_L.mp hl
  have haD : a ∈ H.darts := D.hSd a haS
  obtain ⟨i, _hiC, heq⟩ := D.f_pair haD hdl
  rw [heq]
  have hzD : (H.faceMap ^ i) a ∈ H.darts := H.faceMap_permutes.pow_apply_mem i haD
  have hz1D : H.nodeMap (H.faceMap ((H.faceMap ^ i) a)) ∈ H.darts :=
    H.nodeMap_permutes.apply_mem (H.faceMap_permutes.apply_mem hzD)
  obtain ⟨y, hyS, hzy⟩ := D.hScov _ hz1D
  rw [face_eq_orbit_range] at hzy
  obtain ⟨j, _hjRange, hjy⟩ := hzy
  simp only [] at hjy
  have hyD : y ∈ H.darts := D.hSd y hyS
  have hsym := symListDart H D.hr (z := (H.faceMap ^ i) a)
    (z1 := H.nodeMap (H.faceMap ((H.faceMap ^ i) a))) rfl
  refine rxMemListDarts.mpr ⟨D.f y, D.mem_L.mpr ⟨y, hyS, rfl⟩, ?_⟩
  have hp : (H.node ((H.faceMap ^ (i + 1)) a), H.node ((H.faceMap ^ i) a)) =
      (H.node ((H.faceMap ^ j) y), H.node ((H.faceMap ^ (j + 1)) y)) := by
    refine Prod.ext ?_ ?_
    · rw [show (H.faceMap ^ (i + 1)) a = H.faceMap ((H.faceMap ^ i) a) from by
        rw [pow_succ', Equiv.Perm.mul_apply]]
      rw [← hsym.1, hjy]
    · rw [show (H.faceMap ^ (j + 1)) y = H.faceMap ((H.faceMap ^ j) y) from by
        rw [pow_succ', Equiv.Perm.mul_apply]]
      rw [hjy]
      exact hsym.2.symm
  rw [hp]
  exact D.f_pair_mem hyD j

/-- **槽 (a) 收口：HOL `good_list L`**（tame_defs2.hl:31 = RXOKSKC 第一合取；
三组件 = `uniqDarts_L` / `f_ne_nil` / `swapDart_mem`）。 -/
theorem goodList_L (D : RxOkData H) : rxGoodList D.L :=
  ⟨D.uniqDarts_L,
   fun l hl => by
     obtain ⟨a, ha, rfl⟩ := D.mem_L.mp hl
     exact D.f_ne_nil (D.hSd a ha),
   fun _d hd => D.swapDart_mem hd⟩

/-! ### §2 槽 (c)：iso 之 e/n/f 三槽（HOL :906-:923 / :928-:1065 /
:1073-:1089；全章最重段）

iso 映射 `x ↦ (node H x, node H (F x))`（HOL :804 GEXISTS_TAC 的 λ 项）。
dart 目标为 `list_of_darts L`；e/n/f 三槽分别由 SYM_LIST_DART / n_list
（`f_prev_pair`）/ f_list（`f_next` + `nextElListPairsG`）钉死。 -/

/-- iso 映射（HOL :804 `\x. node H x, node H (face_map H x)`）。 -/
def isoMap (_D : RxOkData H) (x : α) : Set α × Set α :=
  (H.node x, H.node (H.faceMap x))

/-- `isoMap (F^i y)` 的节点对展开形（逐槽共用换算件）。 -/
theorem isoMap_pow (D : RxOkData H) (y : α) (i : ℕ) :
    D.isoMap ((H.faceMap ^ i) y) =
      (H.node ((H.faceMap ^ i) y), H.node ((H.faceMap ^ (i + 1)) y)) := by
  simp [isoMap, pow_succ', Equiv.Perm.mul_apply]

/-- `isoMap (F^i y)` 落面片 `D.f y` 的 pair 表（`f_pair_mem` 的 iso 形）。 -/
theorem isoMap_mem_listPairs (D : RxOkData H) {y : α} (hy : y ∈ H.darts) (i : ℕ) :
    D.isoMap ((H.faceMap ^ i) y) ∈ listPairs (D.f y) := by
  rw [D.isoMap_pow y i]
  exact D.f_pair_mem hy i

/-- iso 映射把 dart 送入 `list_of_darts L`（HOL :810-:900 正映射段）：
`hScov` 给出 `x = F^i y`，再消费 `f_pair_mem`。 -/
theorem isoMap_mem (D : RxOkData H) {x : α} (hx : x ∈ H.darts) :
    D.isoMap x ∈ rxListOfDarts D.L := by
  obtain ⟨y, hyS, hxy⟩ := D.hScov x hx
  rw [face_eq_orbit_range] at hxy
  obtain ⟨i, _hiRange, hiy⟩ := hxy
  simp only [] at hiy
  have hyD : y ∈ H.darts := D.hSd y hyS
  rw [← hiy]
  exact rxMemListDarts.mpr ⟨D.f y, D.mem_L.mpr ⟨y, hyS, rfl⟩,
    D.isoMap_mem_listPairs hyD i⟩

/-- iso 映射对 dart 表的满射（HOL :810-:900 反向段）：dart 落 `f y` 的
pair 表即由 `f_pair` 分解为 `isoMap (F^i y)`。 -/
theorem isoMap_surjOn (D : RxOkData H) :
    Set.SurjOn D.isoMap ↑H.darts {d | d ∈ rxListOfDarts D.L} := by
  intro d hd
  obtain ⟨l, hl, hdl⟩ := rxMemListDarts.mp hd
  obtain ⟨y, hyS, rfl⟩ := D.mem_L.mp hl
  have hyD : y ∈ H.darts := D.hSd y hyS
  obtain ⟨i, _hiC, heq⟩ := D.f_pair hyD hdl
  refine ⟨(H.faceMap ^ i) y, Finset.mem_coe.mpr
    (H.faceMap_permutes.pow_apply_mem i hyD), ?_⟩
  rw [heq]
  exact D.isoMap_pow y i

/-- iso 映射在 dart 上的单射（HOL :889-:905 的 iso 单射槽；ONE_TO_ONE_DART
直接消费）。 -/
theorem isoMap_injOn (D : RxOkData H) : Set.InjOn D.isoMap ↑H.darts := by
  intro x hx y hy hxy
  exact oneToOneDart H D.hr (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy)
    (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)

/-- iso 映射的 `MapsTo`（目标集为 `list_of_darts L`）。 -/
theorem isoMap_mapsTo (D : RxOkData H) :
    Set.MapsTo D.isoMap ↑H.darts {d | d ∈ rxListOfDarts D.L} :=
  fun _x hx => D.isoMap_mem (Finset.mem_coe.mp hx)

/-- iso 映射对 `hypermapOfListG D.L hL` 的 dart 集是双射（HOL :780-:905
`BIJ` 三槽）。 -/
theorem isoMap_bijOn (D : RxOkData H) (hL : rxGoodList D.L) :
    Set.BijOn D.isoMap ↑H.darts ↑(hypermapOfListG D.L hL).darts := by
  have hbij : Set.BijOn D.isoMap ↑H.darts {d | d ∈ rxListOfDarts D.L} :=
    ⟨D.isoMap_mapsTo, D.isoMap_injOn, D.isoMap_surjOn⟩
  rwa [← darts_hypermapOfListG D.L hL] at hbij

/-- `isoMap x` 落 `hypermapOfListG D.L hL` 的 dart 集。 -/
theorem isoMap_mem_hypermap (D : RxOkData H) (hL : rxGoodList D.L) {x : α}
    (hx : x ∈ H.darts) : D.isoMap x ∈ (hypermapOfListG D.L hL).darts := by
  have h' : D.isoMap x ∈ (↑(hypermapOfListG D.L hL).darts : Set (Set α × Set α)) := by
    rw [darts_hypermapOfListG D.L hL]
    exact D.isoMap_mem hx
  exact h'

/-- **槽 (c) 之 e（HOL :906-:923）**：`e_list_ext (isoMap x) = isoMap (E x)`。
LHS 经 `edgeMap_hypermapOfListG` 化 `rxESwap (node x, node (F x))`；RHS 经
`edgeMap_apply` 化 `E x = N (F x)` 后由 SYM_LIST_DART（z = x）钉住
`(node (F x), node x)`。 -/
theorem isoMap_edge (D : RxOkData H) (hL : rxGoodList D.L) {x : α}
    (hx : x ∈ H.darts) :
    (hypermapOfListG D.L hL).edgeMap (D.isoMap x) = D.isoMap (H.edgeMap x) := by
  rw [edgeMap_hypermapOfListG D.L hL (D.isoMap_mem_hypermap hL hx)]
  rw [edgeMap_apply69 H D.hr.plain x]
  have hsym := symListDart H D.hr (z := x)
    (z1 := H.nodeMap (H.faceMap x)) rfl
  show (H.node (H.faceMap x), H.node x) =
    (H.node (H.nodeMap (H.faceMap x)),
      H.node (H.faceMap (H.nodeMap (H.faceMap x))))
  rw [hsym.1, hsym.2]

/-- **槽 (c) 之 n（HOL :928-:1065，全章最重段）**：
`n_list_ext (isoMap x) = isoMap (N x)`。`x = F^i y` 后，`rxFindFace` 由
`rxFindFace_eq_of_mem` 钉到 `listPairs (f y)`；`f_prev_pair` 给出上一节点对；
RHS 由 SYM_LIST_DART（z = F^p y，p = (i+CARD-1)%CARD）+ 指标折算
`pow_pred_succ_apply` 收成同一节点对。 -/
theorem isoMap_node (D : RxOkData H) (hL : rxGoodList D.L) {x : α}
    (hx : x ∈ H.darts) :
    (hypermapOfListG D.L hL).nodeMap (D.isoMap x) = D.isoMap (H.nodeMap x) := by
  obtain ⟨y, hyS, hxy⟩ := D.hScov x hx
  rw [face_eq_orbit_range] at hxy
  obtain ⟨i, hiRange, hiy⟩ := hxy
  have hiC : i < (H.face y).ncard := Finset.mem_range.mp hiRange
  have hyD : y ∈ H.darts := D.hSd y hyS
  simp only [] at hiy
  subst x
  have hLmem : D.f y ∈ D.L := D.mem_L.mpr ⟨y, hyS, rfl⟩
  have hfaceEq : rxFindFace D.L (D.isoMap ((H.faceMap ^ i) y)) = listPairs (D.f y) :=
    rxFindFace_eq_of_mem69 D.uniqDarts_L hLmem (D.isoMap_mem_listPairs hyD i)
  rw [nodeMap_hypermapOfListG D.L hL (D.isoMap_mem_hypermap hL hx)]
  show rxESwap (prevEl (rxFindFace D.L (D.isoMap ((H.faceMap ^ i) y)))
      (D.isoMap ((H.faceMap ^ i) y))) = D.isoMap (H.nodeMap ((H.faceMap ^ i) y))
  rw [hfaceEq, D.isoMap_pow y i, D.f_prev_pair hyD i]
  show (H.node ((H.faceMap ^ i) y),
      H.node ((H.faceMap ^ ((i + (H.face y).ncard - 1) % (H.face y).ncard)) y)) =
    D.isoMap (H.nodeMap ((H.faceMap ^ i) y))
  have hzp : H.faceMap ((H.faceMap ^ ((i + (H.face y).ncard - 1) %
      (H.face y).ncard)) y) = (H.faceMap ^ i) y := by
    simpa [pow_succ', Equiv.Perm.mul_apply] using pow_pred_succ_apply H y i hiC
  have hrhs : D.isoMap (H.nodeMap ((H.faceMap ^ i) y)) =
      (H.node (H.nodeMap (H.faceMap ((H.faceMap ^ ((i + (H.face y).ncard - 1) %
        (H.face y).ncard)) y))),
       H.node (H.faceMap (H.nodeMap (H.faceMap ((H.faceMap ^ ((i + (H.face y).ncard - 1) %
        (H.face y).ncard)) y))))) := by
    rw [hzp]
    rfl
  have hsym := symListDart H D.hr
    (z := (H.faceMap ^ ((i + (H.face y).ncard - 1) % (H.face y).ncard)) y)
    (z1 := H.nodeMap (H.faceMap ((H.faceMap ^ ((i + (H.face y).ncard - 1) %
      (H.face y).ncard)) y))) rfl
  rw [hrhs, hsym.1, hsym.2, hzp]

/-- **槽 (c) 之 f（HOL :1073-:1089）**：`f_list_ext (isoMap x) = isoMap (F x)`。
`nextElListPairsG` 把 `next_el (list_pairs (f y))` 化 `(node F^(i+1) y,
nextEl (f y) (node F^(i+1) y))`，`f_next` 再走一步。 -/
theorem isoMap_face (D : RxOkData H) (hL : rxGoodList D.L) {x : α}
    (hx : x ∈ H.darts) :
    (hypermapOfListG D.L hL).faceMap (D.isoMap x) = D.isoMap (H.faceMap x) := by
  obtain ⟨y, hyS, hxy⟩ := D.hScov x hx
  rw [face_eq_orbit_range] at hxy
  obtain ⟨i, _hiRange, hiy⟩ := hxy
  have hyD : y ∈ H.darts := D.hSd y hyS
  simp only [] at hiy
  subst x
  have hLmem : D.f y ∈ D.L := D.mem_L.mpr ⟨y, hyS, rfl⟩
  have hfaceEq : rxFindFace D.L (D.isoMap ((H.faceMap ^ i) y)) = listPairs (D.f y) :=
    rxFindFace_eq_of_mem69 D.uniqDarts_L hLmem (D.isoMap_mem_listPairs hyD i)
  rw [faceMap_hypermapOfListG D.L hL (D.isoMap_mem_hypermap hL hx)]
  show nextEl (rxFindFace D.L (D.isoMap ((H.faceMap ^ i) y)))
      (D.isoMap ((H.faceMap ^ i) y)) = D.isoMap (H.faceMap ((H.faceMap ^ i) y))
  rw [hfaceEq, D.isoMap_pow y i, nextElListPairsG (D.f_nodup hyD) (D.f_pair_mem hyD i),
    D.f_next hyD (i + 1)]
  show (H.node ((H.faceMap ^ (i + 1)) y), H.node ((H.faceMap ^ (i + 1 + 1)) y)) =
    (H.node (H.faceMap ((H.faceMap ^ i) y)),
      H.node (H.faceMap (H.faceMap ((H.faceMap ^ i) y))))
  simp [pow_succ', Equiv.Perm.mul_apply]

/-- **iso 到达（HOL :782-:1090 的 `iso H (hypermap_of_list L)`）**：
`H.Iso (hypermapOfListG D.L hL)`，见证 = `isoMap`，三槽 = e/n/f。 -/
theorem iso_hypermapOfListG (D : RxOkData H) (hL : rxGoodList D.L) :
    H.Iso (hypermapOfListG D.L hL) :=
  ⟨D.isoMap, D.isoMap_bijOn hL,
    fun _x hx => ⟨D.isoMap_edge hL hx, D.isoMap_node hL hx, D.isoMap_face hL hx⟩⟩

/-! ### §3 槽 (b)：`good_list_nodes L`（tame_defs2.hl:38 = RXOKSKC 第二合取）

HOL :723-:783 的 `good_list_nodes` 段以 node_set 的轨道-纤维对应收口。
Lean 侧证明路线：先取 §2 的 iso（语句顺序偏差，机理等价——good_list_nodes
是几何条件，非 good_list 的纯组合推论；见头注雷区 #178），再经 iso 把
`nodeSet (hypermapOfListG L hL)` 逐轨道转移为 FST-fiber：

  nodeSet G = { isoMap '' (node H z) | z ∈ dart H } = { FST-fiber (node H z) }
            = { FST-fiber x | x ∈ elements_of_list L } = rxNodesOfListSet L。

其中 `isoMap '' (node H z) = FST-fiber (node H z)` 由 §2 的 n 槽
（节点轨道共轭）与 `snd_node` 守恒收。 -/

/-- iso 共轭下的节点轨道（`G.nodeMap^k (isoMap z) = isoMap (N^k z)`）。 -/
theorem isoMap_node_pow (D : RxOkData H) (hL : rxGoodList D.L) (k : ℕ) {z : α}
    (hz : z ∈ H.darts) :
    ((hypermapOfListG D.L hL).nodeMap ^ k) (D.isoMap z) =
      D.isoMap ((H.nodeMap ^ k) z) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    have hz' : (H.nodeMap ^ k) z ∈ H.darts := H.nodeMap_permutes.pow_apply_mem k hz
    rw [D.isoMap_node hL hz']
    congr 1
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- 节点轨道在 iso 下的像（HOL :728-:761 `set_of_orbits` 转移步）。 -/
theorem orbit_iso (D : RxOkData H) (hL : rxGoodList D.L) {z : α}
    (hz : z ∈ H.darts) :
    orbitMap (hypermapOfListG D.L hL).nodeMap (D.isoMap z) =
      D.isoMap '' orbitMap H.nodeMap z := by
  ext w
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨(H.nodeMap ^ k) z, ⟨k, rfl⟩, (D.isoMap_node_pow hL k hz).symm.trans hk⟩
  · rintro ⟨v, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, D.isoMap_node_pow hL k hz⟩

/-- `nodeSet G` 的轨道像形（HOL :728-:770）。 -/
theorem nodeSet_iso (D : RxOkData H) (hL : rxGoodList D.L) :
    (hypermapOfListG D.L hL).nodeSet =
      (fun z : α => D.isoMap '' H.node z) '' ↑H.darts := by
  ext N
  constructor
  · intro hN
    simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq] at hN
    obtain ⟨d, hd, rfl⟩ := hN
    have hd' : d ∈ rxListOfDarts D.L := by
      have h : d ∈ (↑(hypermapOfListG D.L hL).darts : Set (Set α × Set α)) := hd
      rw [darts_hypermapOfListG D.L hL] at h
      exact h
    obtain ⟨z, hz, hzd⟩ := D.isoMap_surjOn hd'
    refine ⟨z, hz, ?_⟩
    rw [← hzd]
    show D.isoMap '' H.node z =
      orbitMap (hypermapOfListG D.L hL).nodeMap (D.isoMap z)
    exact (D.orbit_iso hL hz).symm
  · rintro ⟨z, hz, rfl⟩
    simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq]
    refine ⟨D.isoMap z, D.isoMap_mem_hypermap hL (Finset.mem_coe.mp hz), ?_⟩
    show orbitMap (hypermapOfListG D.L hL).nodeMap (D.isoMap z) = D.isoMap '' H.node z
    exact D.orbit_iso hL (Finset.mem_coe.mp hz)

/-- `isoMap '' (node H z)` = `node H z` 上的 FST-fiber（HOL :723-:760 的
`fst_node_hypermap_of_list` / node 表示转移件）。 -/
theorem isoMap_image_node (D : RxOkData H) {z : α} (hz : z ∈ H.darts) :
    D.isoMap '' H.node z = {d : Set α × Set α | d ∈ rxListOfDarts D.L ∧ d.1 = H.node z} := by
  ext d
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwD : w ∈ H.darts := Finset.mem_coe.mp (H.node_subset_darts hz hw)
    exact ⟨D.isoMap_mem hwD, by
      show H.node w = H.node z
      exact (H.node_eq_of_mem hw).symm⟩
  · rintro ⟨hd, hd1⟩
    obtain ⟨w, hwD, hwd⟩ := D.isoMap_surjOn hd
    have hnd : H.node w = H.node z := by
      have h1 := congrArg Prod.fst hwd
      simp only [isoMap] at h1
      exact h1.trans hd1
    refine ⟨w, ?_, hwd⟩
    rw [← hnd]
    exact H.mem_node_self w

/-- elements_of_list 的节点像形：`x ∈ elements_of_list L ↔ x = node H z`
（z ∈ dart H）（HOL :724-:783 的 `set_of_list (list_of_elements L) =
node_set H` 段）。 -/
theorem mem_elements_iff (D : RxOkData H) {x : Set α} :
    x ∈ rxElementsOfList D.L ↔ ∃ z ∈ H.darts, H.node z = x := by
  constructor
  · intro hx
    have hx' : x ∈ D.L.flatten := by
      simpa [rxElementsOfList, rxListOfElements] using hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx'
    obtain ⟨y, hyS, rfl⟩ := D.mem_L.mp hl
    have hyD : y ∈ H.darts := D.hSd y hyS
    obtain ⟨i, _hiC, hxi⟩ := (D.f_mem_iff hyD).mp hxl
    exact ⟨(H.faceMap ^ i) y, H.faceMap_permutes.pow_apply_mem i hyD, hxi.symm⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, hyS, hzy⟩ := D.hScov z hz
    rw [face_eq_orbit_range] at hzy
    obtain ⟨i, hiRange, hiz⟩ := hzy
    simp only [] at hiz
    have hiC : i < (H.face y).ncard := Finset.mem_range.mp hiRange
    have hyD : y ∈ H.darts := D.hSd y hyS
    change H.node z ∈ D.L.flatten.dedup
    rw [List.mem_dedup, List.mem_flatten]
    refine ⟨D.f y, D.mem_L.mpr ⟨y, hyS, rfl⟩, ?_⟩
    rw [← hiz]
    exact (D.f_mem_iff hyD).mpr ⟨i, hiC, rfl⟩

/-- `rxNodesOfListSet L` 的节点像形（FST-fiber 族的指标集换成
`{node H z | z ∈ dart H}`）。 -/
theorem nodesOfListSet_eq (D : RxOkData H) :
    rxNodesOfListSet D.L =
      (fun z : α => {d : Set α × Set α | d ∈ rxListOfDarts D.L ∧ d.1 = H.node z}) ''
        ↑H.darts := by
  unfold rxNodesOfListSet
  conv_lhs => rw [show rxElementsOfList D.L =
    {x : Set α | ∃ z ∈ H.darts, H.node z = x} from Set.ext (fun x => D.mem_elements_iff)]
  ext S
  constructor
  · rintro ⟨x, ⟨z, hz, hxz⟩, rfl⟩
    exact ⟨z, hz, by rw [← hxz]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨H.node z, ⟨z, hz, rfl⟩, rfl⟩

/-- **槽 (b) 收口：HOL `good_list_nodes L`**。 -/
theorem goodListNodes_L (D : RxOkData H) (hL : rxGoodList D.L) :
    rxGoodListNodes D.L hL := by
  unfold rxGoodListNodes
  calc (hypermapOfListG D.L hL).nodeSet
      = (fun z : α => D.isoMap '' H.node z) '' ↑H.darts := D.nodeSet_iso hL
    _ = (fun z : α => {d : Set α × Set α | d ∈ rxListOfDarts D.L ∧ d.1 = H.node z}) ''
          ↑H.darts := by
        apply Set.image_congr
        intro z hz
        exact D.isoMap_image_node (Finset.mem_coe.mp hz)
    _ = rxNodesOfListSet D.L := (D.nodesOfListSet_eq).symm

end RxOkData

/-! ### §4 槽 (d)：`RXOKSKC`（HOL :523）主件 —— A9 接口

HOL 语句（:523-:525）：
`!H:(A)hypermap. is_restricted H ==>
   (?L:((A->bool)list)list. good_list L /\ good_list_nodes L /\ all uniq L /\
      iso H (hypermap_of_list L))`。

**A9 接口意义**：这是 TameSpine 线对 Assembly 接口 9（tame GIANT）的第一次
实质供数——`iso H (hypermap_of_list L)` 把几何 hypermap `H` 钉死到有限
list 表示 `L`（dart `x ↦ (node x, node (F x))`；边 = 换位、节点 = list 的
FST 纤维、面 = `f_list`）。装配线据此可把任意受限 hypermap 读档为
`fgraph` 形有限数据，与 `FanHypermapIsoList`（Assembly.lean:183）的 A9 出口
合流。 -/

/-- **HOL `RXOKSKC`**（RXOKSKC.hl:523-:1105）：受限 hypermap 存在满足
good_list / good_list_nodes / all uniq 且与之同构的有限 list 表示。 -/
theorem RXOKSKC (H : Hypermap α) (hr : H.IsRestricted) :
    ∃ L : List (List (Set α)), ∃ hL : rxGoodList L,
      (∀ l ∈ L, l.Nodup) ∧ rxGoodListNodes L hL ∧ H.Iso (hypermapOfListG L hL) := by
  obtain ⟨f, hf⟩ := existsListFaceNodeFunc H hr
  obtain ⟨S, hSd, hScov, hSinj, _hScard, _hSfaces⟩ := listCorFaceSet1 H
  let D : RxOkData H :=
    { hr := hr, f := f, S := S, hf := hf, hSd := hSd, hScov := hScov, hSinj := hSinj }
  have hL : rxGoodList D.L := D.goodList_L
  exact ⟨D.L, hL, D.allUniq_L, D.goodListNodes_L hL, D.iso_hypermapOfListG hL⟩

end Kepler.Text.TameSpine
