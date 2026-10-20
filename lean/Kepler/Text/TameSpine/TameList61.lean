/-
  Kepler.Text.TameSpine.TameList61 — B3 D 链第二批：AUQTZYZ.hl atom/
  loop_of_face 块（:354-:572）。Local Fan 结论链入口章续（tamespine-port-
  plan §2 拓扑 `Rxokskc ← Auqtzyz`；§4 批次表 B3 行）。接续批 60 =
  TameList60.lean（7854f380，AUQTZYZ.hl :23-:349 补圈理论 + samsara 算术）；
  本批起点 = AUQTZYZ.hl :354（`atom_refl`），收口至 :572
  （CARD_ITER_K_EK_IMP_DIST_FUNTION 尾）；批 62 接续点 = :574
  （EXISTS_PATH_COMPLEMENT，1,277 行大件独批）。行号按主仓
  reference/flyspeck（commit 1ce0353）实测。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ 射程 :354-:572 十三件：十二落件 + 一记档不落——
  │ · `atom_refl` :354-:360 记档不落：与在册 `Hypermap.atom_reflect`
  │   （Hypermap.lean:6570，hypermap.hl:7773）逐字同句（HOL :7773
  │   `!H L x. x IN atom H L x` = AUQTZYZ :354 `x IN atom H L x`
  │   自由变元全称化；AUQTZYZ 系 hypermap 层同句局部 restatement），
  │   本章消费面 `H.atom_reflect` 一发直取。
  │ 全件零 sorry；公理面 12 探针全件标准三内（propext/Classical.
  │ choice/Quot.sound；point_imp_function 零公理，IMAGE_ATOM_LOOP/
  │ atomsOfLoopRep 仅 propext+Quot.sound）。构建：纯 lake build 单发
  │ 串行零旗标零 -K，Build completed successfully（9493 jobs），本件
  │ 零诊断。
  └──────────────────────────────────────────────────────────────

  载体侦察裁定（开工普查三结论 + 章内对拍）：

  - **在册命中面普查**：十三件名主仓 TameSpine 全零命中；全库 grep
    （含 LocalAuto 族）唯一形近命中 `atom_refl` 的前缀形
    `Hypermap.atom_reflect`（:6570）——逐字对账后即上条记档不落判定，
    非预收重复（其余十二件名全库零命中，批 61 射程净土）。
  - **定义层全在册，零新增 Spine def**：`atom`（Hypermap.lean:6566）、
    `is_node_going`（IsNodeGoing :6562）、`loop_of_face`（loopOfFace
    :8360）、`dart_of_loop` ↦ `Loop.darts`（:5711 结构字段）、
    `in_dart_of_loop` ↦ `x ∈ L.darts`（批 60 EXTRA_COMP_LOOP 已立体
    例）、`atoms_of_loop`（atomsOfLoop :7939）、`complement_index`
    （complementIndex :9138）、`is_restricted`（IsRestricted :9645）。
  - **依赖件在册映射**：`loop_of_face_rep` ↦ loopOfFace_darts :8380；
    `lemma_inverse_res` ↦ loopOfFace_invMap_apply :8387；
    `lemma_face_identity` ↦ face_eq_of_mem :2486；
    `lemma_power_inverse_in_face`/`…_face2` ↦ faceMap_symm_pow_mem_face
    :8577 / faceMap_symm_pow_mem_face_self :8582；
    `in_face_imp_in_dart`（RNSYJXM）↦ face_subset_darts :854；
    `lemma_node_nondegenerate` ↦ nodeNondegenerate_two_le :9095（本批
    is_restricted_card_node 的核即 two_le_node_ncard_faceSymm :9131
    假设面重包）；`simple_hypermap` ↦ Simple :1058（IsRestricted.simple
    访问）；`lemma_increasing_index` ↦ complementIndex_lt_of_lt/of_le
    :9184/:9195；`SUC_LE_PRE`/`complement_index_face_le1` ↦
    TameList60 :464/:306 直取。
  - **四件内联/重推导裁定（免 B3 链底座引 LocalAuto 重依赖，承批 60
    体例）**：`Hypermap.LE_SUC_PRE`（hypermap.hl 纯算术件
    `1<=n ==> SUC(PRE n)=n`）= Nat.succ_pred_eq_of_pos / omega，内联
    记档；`Lvducxu.HYP_MAPS_INVS`（LocalAuto10:346 六合取）在 lemma_
    atom_tail 只消费 faceMap 一对 = Equiv.apply_symm_apply 一词，内联
    记档；`Wrgcvdr_cizmrrh.CARD_ITER_K_EK_IMP_DIST`（LocalAuto3:551）
    按批 60「公开件同证重推导」体例落私桥 cardIterKEkImpDist（ncard
    面，Finset.card_image_iff 一发）；`Hypermap.FACE_FINITE` 在
    card_atom_loop_of_face 的消费由 Mathlib `Set.InjOn.ncard_image`
    （encard 面）免除——有限性无需单列。
  - **atom 映射的型面**：HOL `atom H L x` 是集合（`A->bool`），故
    `g = (\x1. atom H L x1)` 在本章全部消费点（inj_atom / image_face_
    atom / IMAGE_ATOM_LOOP）都是 `α → Set α`，其 IMAGE 是**集合的
    集合**（face 的原子族 ⊆ P(A)）；CARD 作用在该族上（ncard 于
    Set (Set α)，encard 面无需 Set 层可判定等式）——不能按直觉收窄成
    `α → α`（首版误收窄，构建期整改，雷区 #125）。

  新雷区（本批实测记档，编号承批 60 的 #116-#119）：
  - **#120 同句异名记档判定**：AUQTZYZ 的 `atom_refl` = hypermap 层
    `atom_reflect`（:7773）的局部 restatement，非同名引理误撞——按
    「逐字同句记档不落」处理时必须对到 HOL 源行号（两处 let 名不同），
    不得只凭 Lean 面名字相近即判记档。
  - **#121 Finset/Set 双面桥**：集族含 `x1 ∈ L.darts`（Finset.Mem）
    时，`f '' s`（Set.Mem）形态的桥件 rw 匹配不上（头常数不同）——
    桥件必须以 Finset 形态陈述 `{y | ∃ x, y = f x ∧ x ∈ t} = f '' ↑t`；
    消费 `loopOfFace_darts`（↑darts = face）后三件（IMAGE_ATOM_LOOP /
    FINITE_ATOM_LOOP / card_atom_loop_of_face）连发直取。
  - **#122 inj_atom 的 node 侧免 POWER 换算**：IsNodeGoing 定义面第二
    分量在 i = k 处直接给 `(nodeMap.symm^k) y1 = (L.map^k) y1`，配合
    nodeMap_symm_pow_mem_node_self（:8594，无条件件），HOL 的
    power_res_face_map + lemma_face_identity + lemma_power_inverse_
    in_node2 长链在 Lean 面塌缩为两行（面侧 membership 走假设 +
    face_eq_of_mem 平移）；两侧同构，Simple 单点面收口——证明体与
    HOL 分叉但终点同（PEUTLZH 体例记档，语句面逐字不动）。
  - **#123 幂原子还原方向**：complement_index 递归式
    complementIndex_succ_eq(_sub) 语句含 `(faceMap.symm^(i+1)) x`
    幂原子；使用前须 `rw [← h]` 把证人 y1 还原成幂形——正向 rw 匹配
    不上（目标/递归式里只有 y1，方向反了零命中）。
  - **#124 无属词集族就地互化**：`{y | ∃ n, n < k ∧ y = f^[n] x}`
    （CARD_ITER 件）不含 `∈ s` 合取项，通用 Finset 桥不适用——就地
    `ext + simp [Set.mem_image, Set.mem_setOf_eq]` 双向 rintro rfl，
    勿强套桥件。
  - **#125 atom 映射收窄禁令**：见「atom 映射的型面」条——`g` 必须
    `α → Set α`；桥件/InjOn/ncard 全链按此型走，image 结果在
    `Set (Set α)` 层，`Set.InjOn.ncard_image` 不需要面族有限性。
  - **#126 桥件显式参防 eta 漂移**：rw 消费 setOf_exists_eq_image 时
    若留参自适应，高阶合一可能选出 eta 约简形 `f := H.atom L`（与
    语句面 `fun x1 => H.atom L x1` 差一层 eta），下游与 injAtom 的
    rfl 实例接不上——桥件 rw 一律显式传 f 与 t（两型同构时再走
    exact/rfl 的 defeq 收口）。
  - **#127 omega 的 sub-EQ 假设下界门槛（S 系探针实测，详注见 §4
    后附块）**：本环境（lean 4.32.2）omega 对 `X - 1 = n` 型 ℕ 截断
    减法**等式**假设仅在伴随**同原子** `1 ≤ X` 时内化；无同原子下界
    整条丢弃（连 case-split 都不做，报 "No usable constraints"）且
    **不做跨原子链接**（下界在异原子上也救不回）——complement_index
    算术段凡 PRE(ci …) 型假设先 `rw [hcf] at hn` 同原子化或走
    `hn.symm.trans (Nat.succ_pred_eq_of_pos …)` term 面。sub-LE /
    ℤ-eq / sub-在目标 三形正常。

  本批镜像对象（HOL Light Flyspeck，AUQTZYZ.hl :354-:572，十二落件
  + 一记档不落 + 二私桥）：

  §0 私桥：setOf_exists_eq_image（集族 ⇄ image，Finset 形态，雷区
    #121/#126）/ cardIterKEkImpDist（CARD_ITER_K_EK_IMP_DIST 重推导）。
  §1 atom 基础（:354-:427）：`atom_refl` :354 记档不落（≡
    H.atom_reflect）；`atom_eq_in` :362-:365 ↦ atomEqIn（atom_reflect
    + 等式回写一发）；`inj_atom` :367-:427 ↦ injAtom（雷区 #122 两侧
    同构，Simple 单点收口）。
  §2 face 原子族计数（:429-:491）：`image_face_atom` :429 ↦
    imageFaceAtom（loopOfFace_darts + 桥件，集合恒等）；`card_atom_
    loop_of_face` :441 ↦ cardAtomLoopOfFace（imageFaceAtom + injAtom
    + InjOn.ncard_image 三发）；`IMAGE_ATOM_LOOP` :470 ↦ 一名直投
    （桥件）；`FINITE_ATOM_LOOP` :479 ↦ 一名直投（finite_toSet.image，
    loop_lemma 有限性面免除）；`atoms_of_loop_rep` :486 ↦
    atomsOfLoopRep（atomsOfLoop 定义面双向）。
  §3 loop 尾映射与 node 基数（:493-:544）：`lemma_atom_tail` :493 ↦
    lemmaAtomTail（loopOfFace_invMap_apply + apply_symm_apply，HYP_
    MAPS_INVS face 对内联）；`is_restricted_card_node` :502 ↦
    isRestrictedCardNode（two_le_node_ncard_faceSymm 假设面重包）；
    `complement_index_bound` :510-:544 ↦ complementIndexBound
    （complementIndex_succ_eq_sub + complementIndexFaceLe1 +
    complementIndex_le_of_le，omega 收口，雷区 #123）。
  §4 迭代函数单性（:546-:572）：`point_imp_function` :546 ↦ 一名直投
    （congrFun 一发）；`CARD_ITER_K_EK_IMP_DIST_FUNTION` :553 ↦ 一名
    直投（cardIterKEkImpDist + point_imp_function，`f^[0] x = x` simp）。

  批 62 接续点：EXISTS_PATH_COMPLEMENT（AUQTZYZ.hl :574-:1850，
  1,277 行大件）**独批**。处方（大件拆段建议）：
  - 结构：`!H x. is_restricted H /\ x IN dart H ==> ?L. 十二合取`——
    is_loop / path_of_loop L (complement x 0) = complement x（函数
    等式）/ in_dart_of_loop (complement x 0) L / node 分裂（?y z）
    / dart_of_loop L ∩ face x = ∅ / 两条 in_dart-or-in_face 闭包 /
    CARD (atoms_of_loop L) = CARD (face x) / atoms_of_loop ∩
    face-atom 族 = ∅ / 两条 atom↔face 双射桥 / in_dart (node_map x1) L。
  - 拆四段（Lean 面 refine ⟨…⟩ 逐合取 or 私件化）：①证人 L 支
    （is_loop/path_of_loop/in_dart 三支）吃批 60 EXTRA_COMP_LOOP 同族
    构造 + complementPermuter/complementMod（path_of_loop 函数等式经
    powerDiv 取模；complementPt x 0 = nodeMap x 为基点面，batch60
    complementCycle 已立）；②node 分裂支吃本批 is_restricted_card_
    node / complement_index_bound + Simple 单点面；③card 支吃本批
    atoms_of_loop_rep + CARD_ITER_K_EK_IMP_DIST_FUNTION + 在册
    atomsOfLoop_inj（:7950）；④atom↔face 双射桥吃本批 lemma_atom_tail
    + complementIndex 递归式（:9161）+ faceMap_symm_pow_mem_face_self
    （:8582）/ inverse_power_function（:1183）/ faceMap_and_darts
    （:805）。
  - 缺口预警：HOL 证体内 `Hypermap_and_fan.INVERSE_ADD_EXPONENTS`
    全库无载体（grep 零命中），批 62 到达时按 Perm 幂面两行重推导
    （inverse face_map/node_map 交换 + 幂加法）或按需补 Hypermap 层
    公开件；`Lvducxu.HYP_MAPS_INVS` 消费同本批内联体例。
  - 其后 AUQTZYZ_concl :1851-:1858 + AUQTZYZ :1859-:2624（765 行压尾）
    再独批；AUQTZYZ_list.hl（329 行 1 件）容量富余可插批。本章毕接
    RXOKSKC.hl（1,105 行；**:523 RXOKSKC 是 A9 接口件，到达时单独
    标注**）。
-/
import Kepler.Text.TameSpine.TameList60

/-! # AUQTZYZ 前段之二：atom / loop_of_face 块（AUQTZYZ.hl :354-:572） -/

namespace Kepler.Text.TameSpine

variable {α : Type*} [DecidableEq α]

/-! ### §0 私桥件（集族 ⇄ image 的 Finset 形态桥；CARD_ITER 重推导） -/

/-- HOL `{y | ?x. y = f x /\ x IN dart_of_loop L}` 型集族（`x ∈ t` 合取
项，t : Finset α）与 `f '' ↑t` 的互化（雷区 #121/#126：Set 形态桥的 rw
头常数是 Set.Mem，对 Finset.Mem 集族匹配不上；rw 消费时显式传 f 与 t
防 eta 漂移）。 -/
private theorem setOf_exists_eq_image {α β : Type*} (f : α → β) (t : Finset α) :
    {y | ∃ x, y = f x ∧ x ∈ t} = f '' (t : Set α) := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨x, rfl, hx⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, rfl, hx⟩

/-- `WRGCVDR.hl:575 CARD_ITER_K_EK_IMP_DIST` 的重推导（在册公开件
`LocalAuto3.CARD_ITER_K_EK_IMP_DIST` :551 同证；为免 B3 D 链底座引入
LocalAuto 重依赖链，按批 60「公开件同证重推导」体例落私桥）：
迭代像满基数 ⟹ 迭代在 `n < k` 上单性（ncard 面：`Set.ncard_coe_finset`
+ `Finset.card_image_iff` 一发；`{n | n < k}` 与 `↑(range k)` 的换算
就地 ext/simp）。 -/
private theorem cardIterKEkImpDist {f : α → α} {x : α} {k : ℕ}
    (h : Set.ncard ((fun n => f^[n] x) '' {n : ℕ | n < k}) = k) :
    ∀ i j, i < k → j < k → i ≠ j → f^[i] x ≠ f^[j] x := by
  have hset : {n : ℕ | n < k} = ((Finset.range k : Finset ℕ) : Set ℕ) := by
    ext n; simp
  rw [hset] at h
  have h2 : (Finset.image (fun n => f^[n] x) (Finset.range k)).card
      = (Finset.range k).card := by
    rw [← Set.ncard_coe_finset (Finset.image (fun n => f^[n] x) (Finset.range k)),
      Finset.coe_image, h, Finset.card_range]
  have hinj : Set.InjOn (fun n => f^[n] x) ((Finset.range k : Finset ℕ) : Set ℕ) :=
    Finset.card_image_iff.mp h2
  intro i j hi hj hij hfe
  exact hij (hinj (by simpa using hi) (by simpa using hj) hfe)

/-! ### §1 atom 基础（AUQTZYZ.hl :354-:427） -/

/- **HOL `atom_refl`**（AUQTZYZ.hl:354-:360）`x IN atom H L x`
记档不落：与在册 `Hypermap.atom_reflect`（:6570，hypermap.hl:7773）
逐字同句（自由变元全称化），本章消费面 `H.atom_reflect` 直取。 -/

/-- **HOL `atom_eq_in`**（AUQTZYZ.hl:362-:365）
`atom H L y = atom H L x ==> y IN atom H L x`
——atom_reflect 的等式回写一发（HOL 走 SET_RULE 换向 + atom_refl 同面）。 -/
theorem atomEqIn (H : Hypermap α) {L : Loop α} {x y : α}
    (h : H.atom L y = H.atom L x) : y ∈ H.atom L x := by
  rw [← h]
  exact H.atom_reflect L y

/-- **HOL `inj_atom`**（AUQTZYZ.hl:367-:427）
`is_restricted H /\ x IN dart H /\ (\x1. atom H (loop_of_face H x) x1)=g
/\ CARD(face H x)= cf ==> (!x1 y1. x1 IN face H x /\ y1 IN face H x /\
g x1 = g y1 ==> x1 = y1)`
——雷区 #125：g : α → Set α（atom 值是集合）；雷区 #122：atom 成员展开
后 IsNodeGoing 定义面第二分量在 i = k 处直接给 nodeMap.symm 幂形，配
nodeMap_symm_pow_mem_node_self（:8594 无条件件）得 node 侧；面侧走
假设 + face_eq_of_mem 平移；两侧同构，Simple 单点面收口（HOL 的
power_res_face_map / lemma_face_identity / lemma_power_inverse_in_
node2 长链塌缩，终点同、语句面逐字不动）。 -/
theorem injAtom (H : Hypermap α) (hr : H.IsRestricted) {x : α} (hx : x ∈ H.darts)
    (g : α → Set α) (hg : (fun x1 => H.atom (H.loopOfFace x) x1) = g) (_cf : ℕ)
    (_hcf : (H.face x).ncard = _cf) {x1 y1 : α} (h1 : x1 ∈ H.face x)
    (h2 : y1 ∈ H.face x) (hgy : g x1 = g y1) : x1 = y1 := by
  rw [← hg] at hgy
  have heq : H.atom (H.loopOfFace x) x1 = H.atom (H.loopOfFace x) y1 := hgy
  have hx1self : x1 ∈ H.atom (H.loopOfFace x) x1 := H.atom_reflect (H.loopOfFace x) x1
  rw [heq] at hx1self
  have hdisj : H.IsNodeGoing (H.loopOfFace x) y1 x1 ∨
      H.IsNodeGoing (H.loopOfFace x) x1 y1 := hx1self
  rcases hdisj with hgoing | hgoing
  · -- x1 ∈ node H y1（node 侧）∧ x1 ∈ face H y1（假设平移）⟹ x1 = y1
    obtain ⟨k, hkx, hgo⟩ := hgoing
    have hx1node : x1 ∈ H.node y1 := by
      rw [hkx, hgo k (Nat.le_refl k)]
      exact H.nodeMap_symm_pow_mem_node_self y1 k
    have hy1d : y1 ∈ H.darts := H.face_subset_darts hx h2
    have hfid : H.face x = H.face y1 := H.face_eq_of_mem h2
    have hx1face : x1 ∈ H.face y1 := by rw [← hfid]; exact h1
    have hs := hr.simple y1 hy1d
    have hmem : x1 ∈ H.node y1 ∩ H.face y1 := ⟨hx1node, hx1face⟩
    rw [hs] at hmem
    exact Set.mem_singleton_iff.mp hmem
  · -- 对称支：y1 ∈ node H x1 ∧ y1 ∈ face H x1 ⟹ y1 = x1
    obtain ⟨k, hky, hgo⟩ := hgoing
    have hy1node : y1 ∈ H.node x1 := by
      rw [hky, hgo k (Nat.le_refl k)]
      exact H.nodeMap_symm_pow_mem_node_self x1 k
    have hx1d : x1 ∈ H.darts := H.face_subset_darts hx h1
    have hfid : H.face x = H.face x1 := H.face_eq_of_mem h1
    have hy1face : y1 ∈ H.face x1 := by rw [← hfid]; exact h2
    have hs := hr.simple x1 hx1d
    have hmem : y1 ∈ H.node x1 ∩ H.face x1 := ⟨hy1node, hy1face⟩
    rw [hs] at hmem
    exact (Set.mem_singleton_iff.mp hmem).symm

/-! ### §2 face 原子族计数（AUQTZYZ.hl :429-:491） -/

/-- **HOL `image_face_atom`**（AUQTZYZ.hl:429-:439）
`is_restricted H /\ x IN dart H /\ (\x1. atom H (loop_of_face H x) x1)=g
/\ CARD (face H x)= cf ==> IMAGE g (face H x)= {y | ?x1. y = atom H
(loop_of_face H x) x1 /\ in_dart_of_loop x1 (loop_of_face H x)}`
——纯集合恒等：in_dart_of_loop x1 (loop_of_face H x) 经
loop_of_face_rep（loopOfFace_darts :8380）即 x1 ∈ face H x；雷区 #125
g : α → Set α（face 的原子族是集合的集合）；HOL 的 is_restricted/
dart/CARD 假设消费后未用，逐字保留（RESA_TAC 同面）。 -/
theorem imageFaceAtom (H : Hypermap α) (_hr : H.IsRestricted) {x : α}
    (_hx : x ∈ H.darts) (g : α → Set α)
    (hg : (fun x1 => H.atom (H.loopOfFace x) x1) = g) (_cf : ℕ)
    (_hcf : (H.face x).ncard = _cf) :
    g '' H.face x = {y | ∃ x1, y = H.atom (H.loopOfFace x) x1 ∧
      x1 ∈ (H.loopOfFace x).darts} := by
  rw [← hg, setOf_exists_eq_image (fun x1 => H.atom (H.loopOfFace x) x1)
    (H.loopOfFace x).darts, H.loopOfFace_darts]

/-- **HOL `card_atom_loop_of_face`**（AUQTZYZ.hl:441-:455）
`is_restricted H /\ x IN dart H ==> CARD {y | ?x1. y = atom H
(loop_of_face H x) x1 /\ in_dart_of_loop x1 (loop_of_face H x)} =
CARD(face H x)`——imageFaceAtom + injAtom + `Set.InjOn.ncard_image`
三发（HOL 走 CARD_IMAGE_INJ + FACE_FINITE；Mathlib ncard/encard 面
免除有限性单列，见载体侦察裁定；桥件显式参防 eta 漂移，雷区 #126）。 -/
theorem cardAtomLoopOfFace (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) :
    {y | ∃ x1, y = H.atom (H.loopOfFace x) x1 ∧
      x1 ∈ (H.loopOfFace x).darts}.ncard = (H.face x).ncard := by
  have himg : {y | ∃ x1, y = H.atom (H.loopOfFace x) x1 ∧
      x1 ∈ (H.loopOfFace x).darts}
      = (fun x1 => H.atom (H.loopOfFace x) x1) '' H.face x := by
    rw [setOf_exists_eq_image (fun x1 => H.atom (H.loopOfFace x) x1)
      (H.loopOfFace x).darts, H.loopOfFace_darts]
  rw [himg]
  have hinj : Set.InjOn (fun x1 => H.atom (H.loopOfFace x) x1) (H.face x) := by
    intro a ha b hb hab
    exact injAtom H hr hx _ rfl _ rfl ha hb hab
  exact Set.InjOn.ncard_image hinj

/-- **HOL `IMAGE_ATOM_LOOP`**（AUQTZYZ.hl:470-:477）
`(\x1. atom H L x1) = g ==> IMAGE g (dart_of_loop L)= {y | ?x. y =
atom H L x /\ in_dart_of_loop x L}`——in_dart_of_loop ↦ `x ∈ L.darts`
（批 60 体例）；雷区 #125：g : α → Set α。 -/
theorem IMAGE_ATOM_LOOP (H : Hypermap α) (L : Loop α) (g : α → Set α)
    (hg : (fun x1 => H.atom L x1) = g) :
    g '' (L.darts : Set α) = {y | ∃ x, y = H.atom L x ∧ x ∈ L.darts} := by
  rw [← hg]
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, rfl, hx⟩
  · rintro ⟨x, rfl, hx⟩; exact ⟨x, hx, rfl⟩

/-- **HOL `FINITE_ATOM_LOOP`**（AUQTZYZ.hl:479-:484）
`FINITE {y | ?x. y = atom H L x /\ in_dart_of_loop x L}`——
finite_toSet.image 一发（HOL 走 IMAGE_ATOM_LOOP + FINITE_IMAGE +
loop_lemma；dart_of_loop 有限性在 Finset 编码下为 finite_toSet，
记档）。 -/
theorem FINITE_ATOM_LOOP (H : Hypermap α) (L : Loop α) :
    {y | ∃ x, y = H.atom L x ∧ x ∈ L.darts}.Finite := by
  have himg : {y | ∃ x, y = H.atom L x ∧ x ∈ L.darts}
      = (fun x => H.atom L x) '' (L.darts : Set α) :=
    setOf_exists_eq_image (fun x => H.atom L x) L.darts
  rw [himg]
  exact L.darts.finite_toSet.image fun x => H.atom L x

/-- **HOL `atoms_of_loop_rep`**（AUQTZYZ.hl:486-:491）
`atoms_of_loop H L = {y | ?x. y = atom H L x /\ in_dart_of_loop x L}`
——atomsOfLoop 定义面（:7939 `{a | ∃ x ∈ L.darts, a = H.atom L x}`）
双向。 -/
theorem atomsOfLoopRep (H : Hypermap α) (L : Loop α) :
    H.atomsOfLoop L = {y | ∃ x, y = H.atom L x ∧ x ∈ L.darts} := by
  ext a
  simp only [Hypermap.atomsOfLoop, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, rfl, hx⟩
  · rintro ⟨x, rfl, hx⟩; exact ⟨x, hx, rfl⟩

/-! ### §3 loop 尾映射与 node 基数（AUQTZYZ.hl :493-:544） -/

/-- **HOL `lemma_atom_tail`**（AUQTZYZ.hl:493-:500）
`!H x y. y IN face H x ==> y = face_map H (inv_loop_map (loop_of_face H x) y)`
——loopOfFace_invMap_apply（:8387，lemma_inverse_res）+
`Equiv.apply_symm_apply` 一发；HOL 证体的 HYP_MAPS_INVS（Lvducxu，
LocalAuto10:346 六合取）此处只消费 faceMap 对 = apply_symm_apply 一词，
内联记档（免 LocalAuto 重依赖）。 -/
theorem lemmaAtomTail (H : Hypermap α) (x y : α) (hy : y ∈ H.face x) :
    y = H.faceMap ((H.loopOfFace x).invMap y) := by
  rw [H.loopOfFace_invMap_apply hy]
  exact (Equiv.apply_symm_apply H.faceMap y).symm

/-- **HOL `is_restricted_card_node`**（AUQTZYZ.hl:502-:508）
`is_restricted H /\ x IN dart H /\ (inverse (face_map H) POWER i) x = y1
==> 2 <= CARD (node H y1)`——在册 `two_le_node_ncard_faceSymm`（:9131，
补指数递增的来源件）假设面重包两行（HOL 走 lemma_power_inverse_in_face
+ in_face_imp_in_dart 的 darts 面已含于 faceMap_symm_pow_mem_darts
:9085）。 -/
theorem isRestrictedCardNode (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (i : ℕ) {y1 : α} (h : (H.faceMap.symm ^ i) x = y1) :
    2 ≤ (H.node y1).ncard := by
  rw [← h]
  exact H.two_le_node_ncard_faceSymm hr.nodeNondegenerate hx i

/-- **HOL `complement_index_bound`**（AUQTZYZ.hl:510-:544）
`is_restricted H /\ x IN dart H /\ PRE (complement_index H x cf) = n /\
CARD (face H x) = cf /\ (inverse (face_map H) POWER SUC i) x = y1 /\
CARD (node H y1) = cn /\ i < cf ==> SUC (complement_index H x i) +
PRE (PRE cn) <= SUC n`——补指数递归步（ci (i+1) = ci i + PRE cn，经
complementIndex_succ_eq_sub，雷区 #123 幂原子还原）+ 补指数对 cf 的
单调（complementIndex_le_of_le）+ 端点换算（SUC n = ci cf 经
complementIndexFaceLe1）+ cn ≥ 2（is_restricted_card_node），omega
收口；HOL 的 LE_SUC_PRE/SUC_LE_PRE 支为同一线性算术（内联记档）。 -/
theorem complementIndexBound (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (cf n : ℕ) (hn : H.complementIndex x cf - 1 = n)
    (hcf : (H.face x).ncard = cf) (i : ℕ) {y1 : α}
    (h : (H.faceMap.symm ^ (i + 1)) x = y1) (cn : ℕ)
    (hcn : (H.node y1).ncard = cn) (hi : i < cf) :
    H.complementIndex x i + 1 + (cn - 1 - 1) ≤ n + 1 := by
  have hnn := hr.nodeNondegenerate
  have h2cn : 2 ≤ (H.node y1).ncard := by
    rw [← h]
    exact H.two_le_node_ncard_faceSymm hnn hx (i + 1)
  have hstep : H.complementIndex x (i + 1)
      = H.complementIndex x i + ((H.node y1).ncard - 1) := by
    rw [← h]
    exact H.complementIndex_succ_eq_sub hnn hx i
  have h1cf : 1 ≤ H.complementIndex x (H.face x).ncard :=
    complementIndexFaceLe1 H hnn hx
  -- 雷区 #127：omega 不跨原子链接——hn 的原子 ci x cf 的下界在 h1cf 里
  -- 是异原子 ci x (face).ncard，先 hcf 同原子化，随后 term 面收口
  -- （sub-EQ 假设无同原子下界即被 omega 整条丢弃，见 §4 后 #127 详注）。
  have hsucn : n + 1 = H.complementIndex x cf := by
    rw [← hcf] at hn ⊢
    rw [← hn]
    exact Nat.succ_pred_eq_of_pos h1cf
  have hle : H.complementIndex x (i + 1) ≤ H.complementIndex x cf :=
    H.complementIndex_le_of_le hnn hx (by omega)
  omega

/-! ### §4 迭代函数单性（AUQTZYZ.hl :546-:572） -/

/- **HOL `point_imp_function`**（AUQTZYZ.hl:546-:551）
`(!i. 0 < i /\ i < k ==> ~(ITER i f x = x)) ==> (!i. 0 < i /\ i < k ==>
~(ITER i f = I))`——congrFun 一发（HOL 走 FUN_EQ_THM + NOT_FORALL 同
面；ITER 面 = `f^[i]`，I_DEF 面 = `id`）。 -/
omit [DecidableEq α] in
theorem point_imp_function {f : α → α} {x : α} {k : ℕ}
    (h : ∀ i, 0 < i → i < k → f^[i] x ≠ x) :
    ∀ i, 0 < i → i < k → f^[i] ≠ id := by
  intro i h0 hik heq
  exact h i h0 hik (congrFun heq x)

/-- **HOL `CARD_ITER_K_EK_IMP_DIST_FUNTION`**（AUQTZYZ.hl:553-:560）
`CARD {ITER n f x | n < k} = k ==> (!i. 0 < i /\ i < k ==>
~(ITER i f = I))`——cardIterKEkImpDist（私桥重推导）+ point_imp_
function；`f^[0] x = x` 走 simp（HOL 的 THAYTHEL_TAC [`i`;`0`][ITER]
同面；`n < k` 无属词形就地 ext 互化，雷区 #124）。 -/
theorem CARD_ITER_K_EK_IMP_DIST_FUNTION {f : α → α} {x : α} {k : ℕ}
    (h : {y | ∃ n, n < k ∧ y = f^[n] x}.ncard = k) :
    ∀ i, 0 < i → i < k → f^[i] ≠ id := by
  have himg : {y | ∃ n, n < k ∧ y = f^[n] x}
      = (fun n => f^[n] x) '' {n : ℕ | n < k} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  rw [himg] at h
  refine point_imp_function (x := x) ?_
  intro j hj0 hjk
  have hne : j ≠ 0 := by omega
  have hd := cardIterKEkImpDist h j 0 hjk (by omega) hne
  simpa using hd

/-! ### 附：omega 环境行为实测（雷区 #127 详注，S 系探针实测于本仓
lean 4.32.2，lake env 与 lake build 行为一致）——`X - 1 = n` 型 ℕ 截断
减法**等式**假设仅在伴随**同原子** `1 ≤ X` 下界时被 omega 内化
（S7/S8/S10 过，批 60 全部 23 处 omega 均避开无下界形故曾绿）；无同
原子下界则整条假设被丢、连 case-split 都不做（`h : m - 1 = n ⊢
n + 1 = m` 报 "No usable constraints"，S3/S9/P1 灭）。sub-LE 假设
（S2 过）、sub-在目标（R5 过）、ℤ-sub-eq（S1 过）均正常。本章 hsucn
失败根因：hn 的原子 `ci x cf` 与下界 h1cf 的原子 `ci x (face).ncard`
异原子，omega 不做跨原子链接（主条见雷区 #127）。后续批到达补指数
算术段时，凡 PRE(complement_index …) 型假设一律先 `rw [hcf] at hn`
同原子化或走 `hn.symm.trans (Nat.succ_pred_eq_of_pos …)` term 面。
另：docstring（`/-- -/` 形）与 `omit … in` 不兼容（解析器要 lemma），
需 omit 的件注释用块注释形（本件 point_imp_function 体例）。 -/

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；本批十二落件——
#print axioms Kepler.Text.TameSpine.atomEqIn
#print axioms Kepler.Text.TameSpine.injAtom
#print axioms Kepler.Text.TameSpine.imageFaceAtom
#print axioms Kepler.Text.TameSpine.cardAtomLoopOfFace
#print axioms Kepler.Text.TameSpine.IMAGE_ATOM_LOOP
#print axioms Kepler.Text.TameSpine.FINITE_ATOM_LOOP
#print axioms Kepler.Text.TameSpine.atomsOfLoopRep
#print axioms Kepler.Text.TameSpine.lemmaAtomTail
#print axioms Kepler.Text.TameSpine.isRestrictedCardNode
#print axioms Kepler.Text.TameSpine.complementIndexBound
#print axioms Kepler.Text.TameSpine.point_imp_function
#print axioms Kepler.Text.TameSpine.CARD_ITER_K_EK_IMP_DIST_FUNTION
-/
