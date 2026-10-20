/-
  Kepler.Text.TameSpine.TameList60 — B3 D 链首批（port-plan §7 W2 起跑）：
  AUQTZYZ.hl 前段补圈理论 + samsara 算术。Local Fan 结论链入口章
  （tamespine-port-plan §2 拓扑 `Rxokskc ← Auqtzyz`；§4 批次表 B3 行）。
  接续批 59 = TameList59.lean（B1 全本收官 f0361c78）；本批起点 =
  AUQTZYZ.hl :23（`lemma_inverse_res_power`），收口至 :349
  （`lemma_samsara_power_add0` 尾）；批 61 接续点 = :354（`atom_refl`，
  atom/loop_of_face 块）。行号按主仓 reference/flyspeck（commit 1ce0353）实测。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ AUQTZYZ.hl 实测 37 枚定理绑定（:23-:572 前段 35 + 大件
  │ EXISTS_PATH_COMPLEMENT :574 / AUQTZYZ :1859）。本批射程
  │ :23-:349：二十落件 + 两记档不落——
  │ · `COMPLEMENT_LARGE_INDEX` :108-:116 记档不落：与在册
  │   `Hypermap.le_complementIndex`（Hypermap.lean:9201，hypermap.hl:10718
  │   `lemma_lower_bound_index`）逐字同句（is_node_nondegenerate 假设面
  │   同形；HOL :108 证明体的归纳在 Lean 面即 :9201 的归纳原样）。
  │ · `lemma` :241-:251 记档不落：`(\x. face_map H x) = face_map H`
  │   纯 funext 平凡件，Lean 面 `funext` 一词，无信息量（其证体内容
  │   已并入 CARD_FACE_LE3 的载体面）。
  │ 全件零 sorry；公理面 propext/Classical.choice/Quot.sound 三标准件。
  └──────────────────────────────────────────────────────────────

  载体侦察裁定（开工普查三结论 + 章内对拍）：

  - **在册命中面普查**：全库 grep（含 LocalAuto 族）AUQTZYZ 37 件名
    零命中（`atom_refl` 五文件误中为 Mathlib/其他同名泛用词）；批 19
    TameList19.lean:20 / 批 25 TameList25.lean:42 的 AUQTZYZ 字样均为
    下游消费注记（e_list_pairs_rev → AUQTZYZ_list、quotient_list 处
    泛型幅度裁定），非预收移植件——本章零重复移植，B3 入口净土。
  - **定义层全在册，零新增 Spine def**：AUQTZYZ 消费词汇
    `atom`/`atoms_of_loop`/`complement_index`/`complement0`/`complement`/
    `samsara`/`support_of_sequence`/`is_inj_list`/`is_contour`/
    `is_restricted`/`loop_of_face`/`is_normal`/`atoms_of_family`/
    `atom_choice`/`darts_of_family` 已全部有 Hypermap.lean 载体
    （atom :6566、atomsOfLoop :7939、complementIndex :9138、
    complementAux :9145、complementPt :9155、samsara :5999、
    pathSupport :5985、IsInjList :5981、ofPath :6110、IsRestricted
    :9645、IsNormalFamily :6808、atomsOfFamily :6821、atomChoice :6896、
    dartsOfFamily :6826）；Hypermap 层泛 α 形直投，无 list 章的
    ℕ 定形问题。
  - **依赖引理面全在册**：`lemma_complement_path`（hypermap.hl:10920）
    在册为五分解件（complementPt_compIndex_eval :9318 /
    complementPt_compIndex_succ_eval :9290 / faceMap_complementPt_pivot
    :9355 / complementPt_add_eval :9276 / isContour_complementPt :9378），
    本批消费 :9318/:9276 两件；`lemma_complement_index`（hypermap.hl:12375）
    ↦ `Hypermap.exists_complementIndex_decomp`（:11044，Lean 形多一枚
    `i < m` 合取项——按 HOL 名引件时匿名丢弃）；`lemma_lower_bound_index`
    ↦ le_complementIndex :9201；`lemma_make_contour_loop`/
    `lemma_generate_loop`/`lemma_samsara_power`/`lemma_samsara_permute`
    ↦ ofPath / isLoopOf_ofPath / samsaraPerm_pow_apply /
    samsaraPerm_permutes（:6110/:6122/:6092/:6084）——本批
    EXTRA_COMP_LOOP 的 is_loop 支按语句直展（:6122 消费 isInjContour
    合成型，HOL :43 的假设面是 is_contour + is_inj_list 分立形，直展
    免 iff 桥）。
  - **INVERSE_FACE_CYCLE 免重依赖重推导**：在册公开件
    `LocalAuto10.INVERSE_FACE_CYCLE`（LocalAuto10.lean:371，
    LVDUCXU.hl:1812）；为免 B3 D 链底座引入 LocalAuto 重依赖链，
    本批按 Hypermap 层两行重推导落公开件 `inverseFaceCycle`
    （pow_card_face_apply_self :6380 + pow_apply_iff_inv_pow_apply
    :1184；LocalAuto10 内部同为 lvd_symmPow_pow_apply 两行构造），
    批 61+ 消费本章时直取。
  - **POWER/ITER 面 Perm 化**：HOL `POWER` 为函数迭代；本章全部消费点
    （samsara p n、inverse (node_map H)、inverse (face_map H)、
    loop_map L）在 Lean 面皆 Equiv.Perm——`power_div` :36 按 Perm 形
    落（LocalAuto10 记档体例「ITER n f ↔ f^[n]; POWER n f collapses
    likewise」）；仅 lemma_samsara_power_add(+0) 两件的 `samsara p n
    POWER j` 是函数迭代，私桥 perm_apply_iterate/samsara_iterate_eq_pow
    （各两行归纳）换算。
  - **FACE_NOT_EMPTY 假设面**：orbit 编码下 `x ∈ face H x` 无条件
    （mem_orbitMap_self，n=0 项；HOL face_refl :908 同为无条件），
    hypermap.hl:3951 的 node_nondegenerate 假设在 Lean 面为冗余，记账。

  新雷区（本批实测记档，编号承批 59 的 #111-115）：
  - **#116 补圈周期是 complement_index x (CARD face) 不是 CARD face**：
    `complement H x (i + SUC n) = complement H x i` 的周期 `SUC n` =
    `complement_index H x (CARD (face H x))`（PRE 抵消后）；若按
    「周期 = 面基数」直觉折算，会在 complement_index_add 的线性算术段
    把 `(H.face x).ncard` 与 `H.complementIndex x (H.face x).ncard`
    当同一原子混写（二者无任何等式相连——换算必须经
    complement_index_add :156：`ci k + ci cf = ci (k + cf)`，平移量
    ci cf 对应 complementIndex 论元处的面基数 cf）。
  - **#117 loop_map 等式的类型面**：HOL `loop_map L = samsara p n`
    两侧皆 `A->A`；Lean `Loop.map : Equiv.Perm α`——语句面以
    `(L.map : α → α) = Loop.samsara p n` 函数等式逐字承载
    （ofPath 结构投射 + samsaraPerm toFun 定义面 rfl）。
  - **#118 omega 段 Nat.pred 需先换算**：complementIndex 递归式的
    无条件面 `H.complementIndex_succ_eq` 尾项是
    `Nat.pred (node …).ncard`，omega 不稳定吃；以
    `have e : … = … + (ncard - 1) := H.complementIndex_succ_eq …`
    型别体位（Nat.pred M 与 M - 1 定义等价，ascription 处消化）换
    减法形再入 omega——比 congrArg 消 pred 更稳（pred 级等式
    omega 同样不稳）。
  - **#119 Nat.div_add_mod 乘序**：Mathlib `Nat.div_add_mod m k :
    k * (m / k) + m % k = m`（除数在前）；power_div 的 HOL 形
    `m = q*n + r` 要 `(m/k) * k` 序——`rw [Nat.mul_comm];
    exact Nat.div_add_mod …` 两步，勿直接 exact 原版。

  本批镜像对象（HOL Light Flyspeck，AUQTZYZ.hl:23-:349，二十落件
  + 两记档不落 + 三私桥）：

  §0 私桥：perm_apply_iterate / samsara_iterate_eq_pow（POWER 的
    Perm 化底座，LocalAuto10 记档体例）。
  §1 逆限制映射幂（:23-:105）：`lemma_inverse_res_power` :23-:32 ↦
    lemmaInverseResPower（`res (face_map H) (face H x)` 的逆即
    `(H.loopOfFace x).invMap`，loopOfFace_invMap_apply :8387 一步 +
    face 轨道在 faceMap.symm 下封闭）；`inverseFaceCycle` =
    INVERSE_FACE_CYCLE 重推导（公开件，见上）；`power_div` :36-:40 ↦
    powerDiv（Perm 形）；`EXTRA_COMP_LOOP` :43-:105 ↦ EXTRA_COMP_LOOP
    （证人 ofPath p n hinj；path_of_loop 函数等式经 powerDiv 取模 +
    samsaraPerm_pow_apply；is_loop 支按 samsara_apply_of_lt/
    samsara_apply_last 双支直展）。
  §2 补圈理论（:108-:235）：`COMPLEMENT_LARGE_INDEX` :108 记档不落
    （≡ le_complementIndex）；`lemma_complement_index_exists`
    :119-:130 ↦ lemmaComplementIndexExists（exists_complementIndex_
    decomp m=k=n 直投，`i < m` 合取项匿名丢弃）；`complement_index_
    face_le1` :133-:141 ↦ complementIndexFaceLe1；`complement_cycle`
    :144-:154 ↦ complementCycle（complementPt_compIndex_eval +
    inverseFaceCycle + rfl 三发）；`complement_index_add` :156-:165 ↦
    complementIndexAdd（归纳 + 幂周期化，雷区 #118）；`complement_
    permuter` :169-:213 ↦ complementPermuter（私件 complementPt_
    period：t=0 支即 complement_cycle 面，t≥1 支 =
    exists_complementIndex_decomp + complementPt_add_eval 双向 +
    幂周期化）；`complement_permuter1` :216-:223 ↦ complementPermuter1；
    `complement_mod` :226-:234 ↦ complementMod。
  §3 face/node 基础件（:239-:309）：`CARD_FACE_LE3` :239-:251 ↦
    CARD_FACE_LE3（orbitMap_singleton_iff 反向 + ncard 单点）；`lemma`
    :241 记档不落；`node_node_map_eq` :254-:257 ↦ nodeNodeMapEq
    （orbitMap_eq_of_mem + mem_orbitMap_self）；`suc_pre_face`
    :261-:263 ↦ sucPreFace；`SUC_LE_PRE` :266-:274 ↦ SUC_LE_PRE
    （omega）；`inverse_node_mod` :278-:287 ↦ inverseNodeMod
    （powerDiv + pow_card_node_symm_apply_self 一发）；`lemma_via_
    inverse_face_map` :291-:301 ↦ lemmaViaInverseFaceMap
    （PermutesOn.orbitMap_symm + exists_lt_ncard_pow_apply，即 HOL
    FACE_NODE_EDGE_ORBIT_INVERSE + lemma_index_on_orbit 两桥在册形）；
    `atoms_of_family_eq` :305-:308 ↦ atomsOfFamilyEq（atomChoice_eq_
    atom / atom_mem_atomsOfFamily 双向）。
  §4 算术杂件与 samsara（:313-:349）：`PRE_LT_LE` :313-:316 ↦
    PRE_LT_LE（omega）；`lemma_samsara_power_add` :321-:332 ↦
    lemmaSamsaraPowerAdd（对 j 归纳 + samsara_apply_of_lt）；
    `lemma_samsara_power_add0` :336-:349 ↦ lemmaSamsaraPowerAdd0
    （化到 p 0 基点 + 幂周期一步）。

  批 61 接续点：AUQTZYZ.hl :354（`atom_refl`）起，顺次吃 atom/
  loop_of_face 块 :354-:572（atom_refl、atom_eq_in、inj_atom、
  image_face_atom、card_atom_loop_of_face、IMAGE_ATOM_LOOP、
  FINITE_ATOM_LOOP、atoms_of_loop_rep、lemma_atom_tail、
  is_restricted_card_node、complement_index_bound、point_imp_function、
  CARD_ITER_K_EK_IMP_DIST_FUNTION 十三件）至 :572；EXISTS_PATH_
  COMPLEMENT :574（1,277 行大件）建议独批。AUQTZYZ_list.hl（329 行
  1 件）同簇排队，依赖 Tame_list 已全在册，可插批。本章收完接
  RXOKSKC.hl（1,105 行；**:523 RXOKSKC 是 A9 接口件，到达时单独
  标注**）。
-/
import Kepler.Text.TameSpine.TameList59

/-! # AUQTZYZ 前段：补圈理论 + samsara 算术（AUQTZYZ.hl :23-:349） -/

namespace Kepler.Text.TameSpine

variable {α : Type*} [DecidableEq α]

/-! ### §0 私桥件（Perm 幂 ⇄ 函数迭代；POWER 的 Perm 化底座） -/

/-- HOL `POWER`/`ITER` 面换算：置换幂在点上的求值 = 函数迭代求值
（LocalAuto10 记档「ITER n f ↔ f^[n]」的 Perm 形两行桥）。 -/
private theorem perm_apply_iterate {α : Type*} (p : Equiv.Perm α) (k : ℕ) (x : α) :
    (p ^ k) x = (p : α → α)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ l ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, Function.iterate_succ_apply, ← ih]

/-! ### §1 逆限制映射幂（AUQTZYZ.hl :23-:105） -/

/-- `LVDUCXU.hl:1812 INVERSE_FACE_CYCLE` 的 Hypermap 层两行重推导
（在册公开件 `LocalAuto10.INVERSE_FACE_CYCLE` :371 同句；为免 B3 D 链
底座引入 LocalAuto 重依赖链，按批 58「公开件同证重推导」体例落本文件，
批 61+ 直取本件）。 -/
theorem inverseFaceCycle (H : Hypermap α) (x : α) :
    (H.faceMap.symm ^ (H.face x).ncard) x = x := by
  have h := H.pow_card_face_apply_self x
  exact ((pow_apply_iff_inv_pow_apply H.faceMap (H.face x).ncard x x).mp h.symm).symm

/-- **HOL `lemma_inverse_res_power`**（AUQTZYZ.hl:23-:32）
`!n. (inverse (res (face_map H) (face H x)) POWER n) x =
(inverse (face_map H) POWER n) x`
——`res (face_map H) (face H x)` 即 `loop_of_face H x` 的映射（loop_of_face
def hypermap.hl:10053），Lean 面 `(H.loopOfFace x).invMap`；归纳步
loopOfFace_invMap_apply（:8387，lemma_inverse_res :10065）+ face 轨道在
faceMap.symm 下封闭（PermutesOn.orbitMap_symm :6158，Lvducxu.
FACE_NODE_EDGE_ORBIT_INVERSE face 支的在册形）。x ∈ face x 由
mem_orbitMap_self 无条件给出（HOL 语句无假设，本件同形）。 -/
theorem lemmaInverseResPower (H : Hypermap α) (x : α) (n : ℕ) :
    ((H.loopOfFace x).invMap ^ n) x = (H.faceMap.symm ^ n) x := by
  have hx : x ∈ H.face x := mem_orbitMap_self H.faceMap x
  have hmem : ∀ k, (H.faceMap.symm ^ k) x ∈ H.face x := by
    intro k
    have h1 : (H.faceMap.symm ^ k) x ∈ orbitMap H.faceMap.symm x :=
      pow_apply_mem_orbitMap H.faceMap.symm k x
    rwa [PermutesOn.orbitMap_symm H.faceMap_permutes x] at h1
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih,
      H.loopOfFace_invMap_apply (hmem k), pow_succ', Equiv.Perm.mul_apply]

/-- **HOL `power_div`**（AUQTZYZ.hl:36-:40）
`(f POWER n) x = x /\ m = q*n+r ==> (f POWER m) x = (f POWER r) x`
——HOL POWER 为函数迭代；本章全部消费点为置换，按 LocalAuto10 记档体例
落 Perm 形（q*n 乘序承 HOL 原句；Nat.div_add_mod 乘序雷区 #119）。 -/
theorem powerDiv {α : Type*} (f : Equiv.Perm α) {x : α} {m n q r : ℕ}
    (h : (f ^ n) x = x) (hm : m = q * n + r) : (f ^ m) x = (f ^ r) x := by
  subst hm
  have hshift : (f ^ n) ((f ^ r) x) = (f ^ r) x := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm, pow_add,
      Equiv.Perm.mul_apply, h]
  have hfix : ∀ t : ℕ, (f ^ (t * n)) ((f ^ r) x) = (f ^ r) x := by
    intro t
    induction t with
    | zero => simp
    | succ l ih =>
      rw [Nat.succ_mul, pow_add, Equiv.Perm.mul_apply, hshift]
      exact ih
  rw [pow_add, Equiv.Perm.mul_apply, hfix]

/-- **HOL `EXTRA_COMP_LOOP`**（AUQTZYZ.hl:43-:105）
`!H p n i j. ~(node H (p i) = node H (p j)) /\ i <= n /\ j <= n /\
is_contour H p (SUC n) /\ is_inj_list p n /\ (!m. p (m MOD SUC n) = p m) ==>
(?L. is_loop H L /\ path_of_loop L (p 0) = p /\ in_dart_of_loop (p 0) L
/\ (?y z. in_dart_of_loop y L /\ in_dart_of_loop z L /\ ~(node H y = node H z))
/\ dart_of_loop L = support_of_sequence p n /\ loop_map L = samsara p n)`
——证人 `Loop.ofPath p n hinj`（lemma_generate_loop :7181 在册形
:6110）；is_loop 支按 samsara_apply_of_lt / samsara_apply_last 双支直展
（HOL 走 lemma_make_contour_loop，其 isInjContour 合成前提由假设分立面
直展替代）；`in_dart_of_loop` ↦ `x ∈ L.darts`（hypermap.hl:6717 def
直译，darts = pathSupport p n 承 support_of_sequence）；`loop_map L =
samsara p n` 的函数等式承雷区 #117；path_of_loop 函数等式经 powerDiv
取模 + samsaraPerm_pow_apply（lemma_samsara_power :7163）。 -/
theorem EXTRA_COMP_LOOP (H : Hypermap α) (p : ℕ → α) (n i j : ℕ)
    (hnode : H.node (p i) ≠ H.node (p j)) (hi : i ≤ n) (hj : j ≤ n)
    (hcont : H.isContour p (n + 1)) (hinj : Loop.IsInjList p n)
    (hmod : ∀ m, p (m % (n + 1)) = p m) :
    ∃ L : Loop α, Loop.IsLoopOf H L ∧ L.pathOf (p 0) = p ∧ p 0 ∈ L.darts ∧
      (∃ y z, y ∈ L.darts ∧ z ∈ L.darts ∧ H.node y ≠ H.node z) ∧
      ↑L.darts = (Loop.pathSupport p n : Set α) ∧
      (L.map : α → α) = Loop.samsara p n := by
  have hpn1 : p (n + 1) = p 0 := by
    have h := hmod (n + 1)
    rw [Nat.mod_self] at h
    exact h.symm
  have hclose : H.oneStepContour (p n) (p 0) := by
    have h1 := H.oneStepContour_of_isContour hcont (le_refl (n + 1))
    rwa [hpn1] at h1
  refine ⟨Loop.ofPath p n hinj, ?_, ?_, ?_, ⟨p i, p j, ?_, ?_, hnode⟩, ?_, ?_⟩
  · -- is_loop H L（Loop.IsLoopOf 定义面直展，HOL :50-:62 支）
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Loop.mem_pathSupport.mp hz
    show H.oneStepContour (p k) (Loop.samsara p n (p k))
    rcases lt_or_eq_of_le hk with hlt | heq
    · rw [Loop.samsara_apply_of_lt p n hinj hlt]
      exact H.oneStepContour_of_isContour hcont (by omega)
    · rw [heq, Loop.samsara_apply_last p n hinj]
      exact hclose
  · -- path_of_loop L (p 0) = p（函数等式；HOL :63-:83 的 power_div 面）
    funext k
    have hfix := (Loop.samsaraPerm_pow_apply p n hinj).1
    have hstep := (Loop.samsaraPerm_pow_apply p n hinj).2
    show (Loop.samsaraPerm hinj ^ k) (p 0) = p k
    have hsplit : k = (k / (n + 1)) * (n + 1) + k % (n + 1) :=
      (Nat.div_add_mod' k (n + 1)).symm
    rw [powerDiv (Loop.samsaraPerm hinj) hfix hsplit,
      hstep (k % (n + 1)) (Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega)))]
    exact hmod k
  · -- in_dart_of_loop (p 0) L（HOL :84-:91 支）
    show p 0 ∈ Loop.pathSupport p n
    exact Loop.mem_pathSupport.mpr ⟨0, Nat.zero_le _, rfl⟩
  · exact Loop.mem_pathSupport.mpr ⟨i, hi, rfl⟩
  · exact Loop.mem_pathSupport.mpr ⟨j, hj, rfl⟩
  · rfl
  · rfl

/-! ### §2 补圈理论（AUQTZYZ.hl :108-:235） -/

/-- **HOL `lemma_complement_index_exists`**（AUQTZYZ.hl:119-:130）
`is_node_nondegenerate H /\ x IN dart H /\ 1 <= n ==> ?i j.
n = complement_index H x i + j /\
j < CARD (node H ((inverse (face_map H) POWER SUC i) x)) /\ 1 <= j`
——`Hypermap.exists_complementIndex_decomp`（:11044，hypermap.hl:12375
`lemma_complement_index`）m = k = n 直投；Lean 形多一枚 `i < m` 合取项
匿名丢弃（COMPLEMENT_LARGE_INDEX :108 支 = le_complementIndex 在册直投，
记档不落）。 -/
theorem lemmaComplementIndexExists (H : Hypermap α) (hnn : H.NodeNondegenerate)
    {x : α} (hx : x ∈ H.darts) {n : ℕ} (hn : 1 ≤ n) :
    ∃ i j : ℕ, n = H.complementIndex x i + j ∧
      j < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard ∧ 1 ≤ j := by
  obtain ⟨i, j, _, hj1, hjlt, hsum⟩ :=
    H.exists_complementIndex_decomp hnn hx hn (H.le_complementIndex hnn hx n)
  exact ⟨i, j, hsum, hjlt, hj1⟩

/-- **HOL `complement_index_face_le1`**（AUQTZYZ.hl:133-:141）
`is_node_nondegenerate H /\ x IN dart H ==> 1 <= (complement_index H x
(CARD (face H x)))`——HOL 的 FACE_NOT_EMPTY 支在 orbit 编码下由
mem_orbitMap_self 无条件给出（面基数正性），COMPLEMENT_LARGE_INDEX 支 =
le_complementIndex。 -/
theorem complementIndexFaceLe1 (H : Hypermap α) (hnn : H.NodeNondegenerate)
    {x : α} (hx : x ∈ H.darts) : 1 ≤ H.complementIndex x (H.face x).ncard := by
  have hle := H.le_complementIndex hnn hx (H.face x).ncard
  have hpos : 0 < (H.face x).ncard := by
    show 0 < (orbitMap H.faceMap x).ncard
    rw [Set.ncard_pos (orbitMap_finite H.faceMap_permutes x)]
    exact ⟨x, mem_orbitMap_self H.faceMap x⟩
  omega

/-- **HOL `complement_cycle`**（AUQTZYZ.hl:144-:154）
`is_restricted H /\ (x IN dart H) /\ PRE (complement_index H x
(CARD (face H x))) = n ==> complement H x (SUC n) = complement H x 0`
——HOL 走 lemma_complement_path 第十七结论 + INVERSE_FACE_CYCLE；Lean 面
complementPt_compIndex_eval（:9318）+ inverseFaceCycle + rfl 三发
（complementPt x 0 = nodeMap x 为 complementAux 定义面）。 -/
theorem complementCycle (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) (hn : H.complementIndex x (H.face x).ncard - 1 = n) :
    H.complementPt x (n + 1) = H.complementPt x 0 := by
  have hnn := hr.nodeNondegenerate
  have h1 := complementIndexFaceLe1 H hnn hx
  rw [show n + 1 = H.complementIndex x (H.face x).ncard by omega,
    H.complementPt_compIndex_eval hnn hx, inverseFaceCycle]
  rfl

/-- **HOL `complement_index_add`**（AUQTZYZ.hl:156-:165）
`!i. complement_index H x i + complement_index H x (CARD (face H x)) =
complement_index H x (i + (CARD (face H x)))`——HOL 无假设面（证明体仅
INVERSE_FACE_CYCLE + 定义式）；归纳步幂周期化 + 减法形换算（雷区
#118：Nat.pred M 与 M - 1 定义等价，ascription 处消化）+ omega。 -/
theorem complementIndexAdd (H : Hypermap α) (x : α) (i : ℕ) :
    H.complementIndex x i + H.complementIndex x (H.face x).ncard
      = H.complementIndex x (i + (H.face x).ncard) := by
  induction i with
  | zero => simp only [H.complementIndex_zero_eq, Nat.zero_add]
  | succ k ih =>
    have hpow : (H.faceMap.symm ^ ((k + (H.face x).ncard) + 1)) x
        = (H.faceMap.symm ^ (k + 1)) x := by
      rw [show (k + (H.face x).ncard) + 1 = (k + 1) + (H.face x).ncard by ring,
        pow_add, Equiv.Perm.mul_apply, inverseFaceCycle]
    have ecard : (H.node ((H.faceMap.symm ^ ((k + (H.face x).ncard) + 1)) x)).ncard
        = (H.node ((H.faceMap.symm ^ (k + 1)) x)).ncard :=
      congrArg (fun v => (H.node v).ncard) hpow
    have e2 : H.complementIndex x (k + 1)
        = H.complementIndex x k
          + ((H.node ((H.faceMap.symm ^ (k + 1)) x)).ncard - 1) :=
      H.complementIndex_succ_eq x k
    have eR : H.complementIndex x ((k + 1) + (H.face x).ncard)
        = H.complementIndex x (k + (H.face x).ncard)
          + ((H.node ((H.faceMap.symm ^ ((k + (H.face x).ncard) + 1)) x)).ncard
            - 1) := by
      rw [show (k + 1) + (H.face x).ncard = (k + (H.face x).ncard) + 1 by ring]
      exact H.complementIndex_succ_eq x (k + (H.face x).ncard)
    rw [e2, eR, ecard]
    omega

/-- HOL :169-:213 证明体的周期件：补圈以 `complement_index H x (CARD
(face H x))` 为周期（雷区 #116——周期不是面基数本身；换算经
complement_index_add）。t = 0 支即 complement_cycle 面；t ≥ 1 支 =
exists_complementIndex_decomp + complementPt_add_eval 双向 + 幂周期化。 -/
private theorem complementPt_period (H : Hypermap α) (hr : H.IsRestricted)
    {x : α} (hx : x ∈ H.darts) (t : ℕ) :
    H.complementPt x (t + H.complementIndex x (H.face x).ncard)
      = H.complementPt x t := by
  have hnn := hr.nodeNondegenerate
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · rw [Nat.zero_add, H.complementPt_compIndex_eval hnn hx, inverseFaceCycle]
    rfl
  · obtain ⟨k, j, -, hj1, hjlt, hsum⟩ :=
      H.exists_complementIndex_decomp hnn hx ht0 (H.le_complementIndex hnn hx t)
    have hadd := complementIndexAdd H x k
    have hpow : (H.faceMap.symm ^ ((k + (H.face x).ncard) + 1)) x
        = (H.faceMap.symm ^ (k + 1)) x := by
      rw [show (k + (H.face x).ncard) + 1 = (k + 1) + (H.face x).ncard by ring,
        pow_add, Equiv.Perm.mul_apply, inverseFaceCycle]
    have hjlt2 : j < (H.node ((H.faceMap.symm ^ ((k + (H.face x).ncard) + 1)) x)).ncard := by
      rw [hpow]
      exact hjlt
    have eL : H.complementPt x (t + H.complementIndex x (H.face x).ncard)
        = (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ (k + 1)) x) := by
      have ht2 : t + H.complementIndex x (H.face x).ncard
          = H.complementIndex x (k + (H.face x).ncard) + j := by omega
      rw [ht2, H.complementPt_add_eval hnn hx (k + (H.face x).ncard) j hj1 hjlt2,
        hpow]
    have eR : H.complementPt x t
        = (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ (k + 1)) x) := by
      rw [hsum, H.complementPt_add_eval hnn hx k j hj1 hjlt]
    rw [eL, eR]

/-- **HOL `complement_permuter`**（AUQTZYZ.hl:169-:213）
`is_restricted H /\ (x IN dart H) /\ PRE (complement_index H x
(CARD (face H x))) = n ==> !i. complement H x (i + SUC n) =
complement H x i`——周期换算（SUC n = complement_index x (CARD face)，
雷区 #116）+ 私件 complementPt_period。 -/
theorem complementPermuter (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) (hn : H.complementIndex x (H.face x).ncard - 1 = n)
    (i : ℕ) : H.complementPt x (i + (n + 1)) = H.complementPt x i := by
  have hnn := hr.nodeNondegenerate
  have h1 := complementIndexFaceLe1 H hnn hx
  rw [show n + 1 = H.complementIndex x (H.face x).ncard by omega]
  exact complementPt_period H hr hx i

/-- **HOL `complement_permuter1`**（AUQTZYZ.hl:216-:223）
`… ==> !m. complement H x (m * SUC n + j) = complement H x j`
——对 m 归纳，步支即 complementPermuter（HOL 同构：SUC a*b+j =
(a*b+j)+b）。 -/
theorem complementPermuter1 (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) (hn : H.complementIndex x (H.face x).ncard - 1 = n)
    (m j : ℕ) : H.complementPt x (m * (n + 1) + j) = H.complementPt x j := by
  induction m with
  | zero => rw [Nat.zero_mul, Nat.zero_add]
  | succ k ih =>
    have he : (k + 1) * (n + 1) + j = (k * (n + 1) + j) + (n + 1) := by ring
    rw [he, complementPermuter H hr hx n hn]
    exact ih

/-- **HOL `complement_mod`**（AUQTZYZ.hl:226-:234）
`… ==> !m. complement H x (m MOD SUC n) = complement H x m`
——DIVISION 分解 + complementPermuter1（HOL 同构）。 -/
theorem complementMod (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) (hn : H.complementIndex x (H.face x).ncard - 1 = n)
    (m : ℕ) : H.complementPt x (m % (n + 1)) = H.complementPt x m := by
  have h := complementPermuter1 H hr hx n hn (m / (n + 1)) (m % (n + 1))
  rw [Nat.div_add_mod'] at h
  exact h.symm

/-! ### §3 face/node 基础件（AUQTZYZ.hl :239-:309） -/

/-- **HOL `CARD_FACE_LE3`**（AUQTZYZ.hl:239-:251；:241 `lemma` 记档不落）
`3 <= CARD (face H x) ==> ~(face_map H x = x)`——faceMap 不动点 ⟹ 轨道
单点（orbitMap_singleton_iff :744 反向）⟹ 基数 1 矛盾（HOL 走
orbit_one_point + CARD_SING 同面）。 -/
theorem CARD_FACE_LE3 (H : Hypermap α) {x : α} (h : 3 ≤ (H.face x).ncard) :
    H.faceMap x ≠ x := by
  intro hfix
  have hface : H.face x = {x} := (orbitMap_singleton_iff H.faceMap x).mpr hfix
  rw [hface] at h
  simp at h

/-- **HOL `node_node_map_eq`**（AUQTZYZ.hl:254-:257）
`node H (node_map H d) = node H d`——轨道在自身映射下不变
（orbitMap_eq_of_mem :1207 + mem_orbitMap_self；HOL 走 node_map_and_darts
+ lemma_orbit_power 同面）。 -/
theorem nodeNodeMapEq (H : Hypermap α) (d : α) : H.node (H.nodeMap d) = H.node d :=
  orbitMap_eq_of_mem H.nodeMap_permutes (pow_apply_mem_orbitMap H.nodeMap 1 d)

/-- **HOL `suc_pre_face`**（AUQTZYZ.hl:261-:263）
`SUC (PRE (CARD (face H x))) = (CARD (face H x))`——面基数正性
（mem_orbitMap_self 面；HOL 走 LE_SUC_PRE + FACE_NOT_EMPTY）。 -/
theorem sucPreFace (H : Hypermap α) (x : α) :
    Nat.succ (Nat.pred (H.face x).ncard) = (H.face x).ncard := by
  have hpos : 0 < (H.face x).ncard := by
    show 0 < (orbitMap H.faceMap x).ncard
    rw [Set.ncard_pos (orbitMap_finite H.faceMap_permutes x)]
    exact ⟨x, mem_orbitMap_self H.faceMap x⟩
  exact Nat.succ_pred_eq_of_pos hpos

/-- **HOL `SUC_LE_PRE`**（AUQTZYZ.hl:266-:274）
`!a b. SUC b <= a ==> b <= PRE a`——纯算术（omega）。 -/
theorem SUC_LE_PRE (a b : ℕ) (h : b + 1 ≤ a) : b ≤ a - 1 := by omega

/-- **HOL `inverse_node_mod`**（AUQTZYZ.hl:278-:287）
`(inverse (node_map H) POWER j) x =
(inverse (node_map H) POWER (j MOD (CARD (node H x)))) x`
——lemma_node_inverse_cycle（pow_card_node_symm_apply_self :6405）+
power_div（本批 Perm 形）一发；HOL 的 DIVISION 支在 Lean 面
Nat.div_add_mod 无需 node 非空（% 对 0 良定义，HOL 同值）。 -/
theorem inverseNodeMod (H : Hypermap α) (x : α) (j : ℕ) :
    (H.nodeMap.symm ^ j) x
      = (H.nodeMap.symm ^ (j % (H.node x).ncard)) x := by
  exact powerDiv H.nodeMap.symm (H.pow_card_node_symm_apply_self x)
    (Nat.div_add_mod' j (H.node x).ncard).symm

/-- **HOL `lemma_via_inverse_face_map`**（AUQTZYZ.hl:291-:301）
`!H x y. y IN face H x ==> ?j. j < CARD (face H x) /\
y = (inverse (face_map H) POWER j) x`
——Lvducxu.FACE_NODE_EDGE_ORBIT_INVERSE（face 支）↦
PermutesOn.orbitMap_symm（:6158），lemma_index_on_orbit（hypermap.hl:2064）
↦ PermutesOn.exists_lt_ncard_pow_apply（:2367）双桥在册直投。 -/
theorem lemmaViaInverseFaceMap (H : Hypermap α) {x y : α} (hy : y ∈ H.face x) :
    ∃ j : ℕ, j < (H.face x).ncard ∧ y = (H.faceMap.symm ^ j) x := by
  have hsymm : orbitMap H.faceMap.symm x = H.face x :=
    PermutesOn.orbitMap_symm H.faceMap_permutes x
  rw [← hsymm] at hy
  obtain ⟨j, hj, hjeq⟩ :=
    PermutesOn.exists_lt_ncard_pow_apply H.faceMap_permutes.symm hy
  exact ⟨j, by rw [← hsymm]; exact hj, hjeq⟩

/-- **HOL `atoms_of_family_eq`**（AUQTZYZ.hl:305-:308）
`is_normal H NF ==> atoms_of_family H NF =
{atm | (?x. x IN darts_of_family NF /\ atm = atom_choice H NF x)}`
——atomChoice_eq_atom（:6907，unique_atom_choice）/atom_mem_atomsOfFamily
（:6917，lemma_in_quotient）双向；`is_normal` ↦ `IsNormalFamily`
（:6808 与 hypermap.hl:8122 def 四合取逐字同构）。 -/
theorem atomsOfFamilyEq (H : Hypermap α) {NF : Set (Loop α)}
    (hnf : H.IsNormalFamily NF) :
    H.atomsOfFamily NF = {atm | ∃ x, x ∈ Hypermap.dartsOfFamily NF ∧
      atm = H.atomChoice NF x} := by
  ext a
  constructor
  · rintro ⟨L, hL, x, hx, rfl⟩
    exact ⟨x, Hypermap.mem_dartsOfFamily hL hx, (H.atomChoice_eq_atom hnf hL hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨L, hL, hxL⟩ := Hypermap.mem_dartsOfFamily_iff.mp hx
    exact ⟨L, hL, x, hxL, H.atomChoice_eq_atom hnf hL hxL⟩

/-! ### §4 算术杂件与 samsara（AUQTZYZ.hl :313-:349） -/

/-- **HOL `PRE_LT_LE`**（AUQTZYZ.hl:313-:316）
`1 <= a ==> (!b. b <= PRE a <=> b < a)`——纯算术（omega）。 -/
theorem PRE_LT_LE {a : ℕ} (h : 1 ≤ a) (b : ℕ) : (b ≤ a - 1 ↔ b < a) := by
  omega

/-- `samsara p n` 的函数迭代 ⇄ `samsaraPerm` 置换幂（samsaraPerm toFun
定义面；lemma_samsara_power_add 两件的 POWER 消费桥，私件）。 -/
private theorem samsara_iterate_eq_pow
    (p : ℕ → α) (n : ℕ) (hinj : Loop.IsInjList p n) (k : ℕ) (y : α) :
    (Loop.samsara p n)^[k] y = ((Loop.samsaraPerm hinj) ^ k) y :=
  (perm_apply_iterate (Loop.samsaraPerm hinj) k y).symm

/-- **HOL `lemma_samsara_power_add`**（AUQTZYZ.hl:321-:332）
`!p n. is_inj_list p n ==> (!i j. i + j <= n ==>
(samsara p n POWER j) (p i) = p (i + j))`
——对 j 归纳 + samsara_apply_of_lt（evaluation_samsara 第二支 :6037），
全程函数迭代面（rw 为 syntactic 匹配，Perm 桥不入场）。 -/
theorem lemmaSamsaraPowerAdd (p : ℕ → α) (n : ℕ)
    (hinj : Loop.IsInjList p n) (i j : ℕ) (h : i + j ≤ n) :
    (Loop.samsara p n)^[j] (p i) = p (i + j) := by
  induction j with
  | zero => rfl
  | succ k ih =>
    have hik : i + k ≤ n := by omega
    rw [Function.iterate_succ_apply', ih hik,
      Loop.samsara_apply_of_lt p n hinj (by omega)]
    exact congrArg p (by omega)

/-- **HOL `lemma_samsara_power_add0`**（AUQTZYZ.hl:336-:349）
`!p n. is_inj_list p n ==> (!i j. i + j = SUC n /\ 1 <= j ==>
(samsara p n POWER j) (p i) = p (0))`
——化到 p 0 基点（lemma_samsara_power_add 反向铺 i 步）+ 幂周期一步
（samsaraPerm_pow_apply 第一支，lemma_samsara_power :7163）。 -/
theorem lemmaSamsaraPowerAdd0 (p : ℕ → α) (n : ℕ)
    (hinj : Loop.IsInjList p n) (i j : ℕ) (h : i + j = n + 1) (hj : 1 ≤ j) :
    (Loop.samsara p n)^[j] (p i) = p 0 := by
  have hi : i ≤ n := by omega
  have hstep := lemmaSamsaraPowerAdd p n hinj 0 i (by omega)
  rw [Nat.zero_add] at hstep
  have htot : (Loop.samsara p n)^[j] ((Loop.samsara p n)^[i] (p 0))
      = (Loop.samsara p n)^[i + j] (p 0) := by
    rw [Nat.add_comm, Function.iterate_add_apply]
  rw [← hstep, htot, h, samsara_iterate_eq_pow p n hinj,
    (Loop.samsaraPerm_pow_apply p n hinj).1]

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；本批二十落件——
#print axioms Kepler.Text.TameSpine.inverseFaceCycle
#print axioms Kepler.Text.TameSpine.lemmaInverseResPower
#print axioms Kepler.Text.TameSpine.powerDiv
#print axioms Kepler.Text.TameSpine.EXTRA_COMP_LOOP
#print axioms Kepler.Text.TameSpine.lemmaComplementIndexExists
#print axioms Kepler.Text.TameSpine.complementIndexFaceLe1
#print axioms Kepler.Text.TameSpine.complementCycle
#print axioms Kepler.Text.TameSpine.complementIndexAdd
#print axioms Kepler.Text.TameSpine.complementPermuter
#print axioms Kepler.Text.TameSpine.complementPermuter1
#print axioms Kepler.Text.TameSpine.complementMod
#print axioms Kepler.Text.TameSpine.CARD_FACE_LE3
#print axioms Kepler.Text.TameSpine.nodeNodeMapEq
#print axioms Kepler.Text.TameSpine.sucPreFace
#print axioms Kepler.Text.TameSpine.SUC_LE_PRE
#print axioms Kepler.Text.TameSpine.inverseNodeMod
#print axioms Kepler.Text.TameSpine.lemmaViaInverseFaceMap
#print axioms Kepler.Text.TameSpine.atomsOfFamilyEq
#print axioms Kepler.Text.TameSpine.PRE_LT_LE
#print axioms Kepler.Text.TameSpine.lemmaSamsaraPowerAdd
#print axioms Kepler.Text.TameSpine.lemmaSamsaraPowerAdd0
-/
