/-
  Kepler.Text.TameSpine.TameList62 — B3 D 链第三批：AUQTZYZ.hl 主峰
  EXISTS_PATH_COMPLEMENT（:574-:1850，1,277 行大件独批）。Local Fan 结论链
  入口章续（tamespine-port-plan §2 拓扑 `Rxokskc ← Auqtzyz`；§4 批次表
  B3 行）。接续批 61 = TameList61.lean（04bbab7d，AUQTZYZ.hl :354-:572
  atom/loop_of_face 块十二件）；本批起点 = AUQTZYZ.hl :574
  （EXISTS_PATH_COMPLEMENT），收口至 :1850；批 63 接续点 = :1851
  （AUQTZYZ_concl）+ :1859-:2624（AUQTZYZ 压尾段）。行号按主仓
  reference/flyspeck（commit 1ce0353）实测。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ 射程 :574-:1850 一件：EXISTS_PATH_COMPLEMENT 落件（十二合取
  │ 逐字承载，按批 61 处方四段拆分全真证——①证人 L 支 + node 分裂
  │ ／⑤互斥+双闭包（合取 5-7）／③card 支（合取 8）／④双射桥
  │ （合取 9-12），每段独立 private 真证件 + 探针）。全件零 sorry；
  │ 公理面 propext/Classical.choice/Quot.sound 三标准内。构建纯
  │ lake build 单发串行零旗标零 -K。
  └──────────────────────────────────────────────────────────────

  载体侦察裁定（开工普查三结论 + 章内对拍）：

  - **在册命中面普查**：EXISTS_PATH_COMPLEMENT 全库仅 TameList60/61
    注记与 HOL 原文命中（无预收载体）；子件名逐件 grep：全部有在册
    载体（lemma_complement_path 五分解件、lemma_inj_complement ↦
    isInjContour_complementPt :9409、lemma_different_nodes ↦
    node_ne_of_not_mem :3703、Hypermap_and_fan.ORBIT_MAP_INJ ↦
    orbitMap_pow_inj :9056、lemma_via_inverse_node_map ↦
    exists_pow_nodeMap_symm_apply_of_mem_node :9424、lemma_via_
    inverse_face_map ↦ TameList60.lemmaViaInverseFaceMap、
    CARD_IMAGE_EQ_INJ/CARD_NUMSEG_1 ↦ Set.ncard_coe_finset +
    Finset.card_image_iff + Finset.card_range 同面、
    LEFT/RIGHT_INVERSE_EQUATION ↦ edgeMap_mul_nodeMap :834 同面），
    零重复移植。
  - **缺口件裁定（到达时单独标注）**：`Hypermap_and_fan.INVERSE_
    ADD_EXPONENTS` 全库无载体（预警属实）——按处方 Perm 幂面两行
    重推导落公开件 `inverseAddExponents`；但 Lean 路线经
    complementPt_compIndex_succ_eval 直评 + nodeMap.symm 单射，
    HOL :769 的 f-单射消费点在 Lean 面塌缩，本件记档不消费
    （proof 路线分叉、语句面逐字不动，PEUTLZH 体例）。
  - **证人 L = EXTRA_COMP_LOOP 直投**：p = complementPt H x、
    n = PRE(complementIndex x (CARD face))；is_contour 支 =
    isContour_complementPt、is_inj_list 支 = isInjContour_
    complementPt（私桥 isInjContourIsInjList 三行展开）、取模支 =
    批 60 complementMod、node 分裂支 = 本批 epcNodeSplit（HOL
    :666-:686 的 CARD_FACE_LE3 收口面改走 orbitMap_pow_inj 窗口
    单射，终点同；雷区 #122 体例记档）。
  - **指标 ±1 压制（本批主方法论）**：HOL 全程与 support 下标
    ±1 边界缠斗（SUC_LE_PRE/LE_SUC_PRE 段十余处）；Lean 面以
    「均匀成员件 epcMemPath：任意下标 m 的 p m 都在 L.darts
    （p m = p (m % (n+1))）」一发压平，四段 witness 全部不再做
    下标边界 case。HOL 证明体与 Lean 分叉、语句面逐字不动。
  - **segment-cf 修正式（对批 61 处方的勘误记档）**：补路径尾段
    （k = CARD face，z_cf = x）在路径上只占 j = 1..N_cf-2 共
    N_cf-2 点（j = N_cf-1 的点 nodeMap x 即 p 0，cycle 收口点；
    N_cf = 2 时尾段为空）；闭包与 card 段 witness 下标相应走
    ci x (PRE cf) + j 形（与 HOL 同形）；nodeMap.symm^(N-1) z 的
    正确恒等式是 `symm^(N-1) z = nodeMap z`（epcSymmPredNodeMap），
    与首版直觉 symm^(N-1) z = symm z 不同——构建期整改记档。

  新雷区（本批实测记档，编号承批 61 的 #120-#127）：
  - **#128 samsara/samsaraInv 的函数面换算**：L.map 的函数等式
    （hLm）只给 α → α 面；取 L.invMap 求值需先 Equiv.Perm.ext
    （`Equiv.Perm.ext (fun y => hLm y)`——hLm 直接作参有 coercion
    层差）升回 Equiv 面，再走 samsaraPerm 的 invFun 定义面 =
    samsaraInv（rfl）。任意下标求值统一式（epcMapStep/
    epcInvMapStep）：L.map (p m) = p ((m+1) % (n+1))、L.invMap
    (p m) = p ((m+n) % (n+1))；p 的下标先 hmod 归位再
    samsara_apply，尾段 Nat.mod_add_mod（批 60 #119 的 mod 面）。
  - **#129 plain 组合面 faceMap∘nodeMap = nodeMap.symm∘faceMap.symm**：
    在册 `H.edgeMap_mul_nodeMap`（:834，edgeMap*nodeMap =
    faceMap⁻¹）+ inv_inv 两发拼出——勿用 eq_inv_of_mul_eq_one_*
    裸件（本环境 Mathlib 方向易错），雷区 #129 记档。
  - **#130 atom 单射的 node 交塌缩**：atom L u = atom L v ⟹
    v ∈ atom L u ⊆ node u 与 u ∈ node v 联立 node u = node v，再
    node z_i ∩ face x = {z_i}（Simple）塌出 z_i = z_j——HOL
    :1370-:1400 的 PERMUTES_INVERSE_EQ + lemma_power_inverse_in_node
    + lemma_in_node1 长链在 Lean 面塌缩为数行（PEUTLZH 体例，
    语句面逐字不动）。
  - **#131 res 恒等支**：(loopOfFace x).map y 对 y ∉ face x 是恒等
    （resPerm toFun = res，res 定义面 if-neg 一发）；face-atom
    单点件（合取 9 支）的 going-反向支靠它收口，勿在 face 支外
    强套 faceMap 求值。
  - **#132 going 链组合**：IsNodeGoing 传递性按定义拼（k1+k2 幂
    加法 + 分段 agree；Equiv.Perm 幂是 pow_add + mul_apply，
    Function.iterate 不入场）；链式构件 epcGoingChain（段内）/
    epcGoingWrap（段内 + 收口步到 p 0）按 k = m - m₀ 归纳；
    (p^(k+1)) z = p ((p^k) z) 的应用形拆分独立成 pow_succ'_apply
    （pow_succ/pow_succ' 方向易混：pull 内层映射用 pow_succ，
    pow_succ' 反向；裸 pow_succ' 在多幂项目标上会错咬 face 侧
    幂——一律用显式 p 参的 pow_succ'_apply）。
  - **#133 尾段算术的 N_cf 换算**：ci cf = ci (PRE cf) + (N_cf - 1)
    型线性式一律先经 inverseFaceCycle 的 congrArg ncard（N_cf =
    N_x）把 N_cf 原子归一到 N_x（hci1 归一形），再与 h1cf
    （1 ≤ ci cf 同原子下界，雷区 #127 的门槛件）+ hcfN
    （n + 1 = ci cf）一起 omega——hn 单独携带不足以恢复
    ci cf = n + 1 的关系，四段统一以 hn 参数显式带入。
  - **#134 字面下标的 defeq 塌缩**：complementPt_compIndex_succ_eval
    等五分解件的 LHS 是 `p (ci x i + 1)` 形；对字面 `p 1` 的 rw 必须
    先落 ascription have（`have : H.complementPt x 1 = ... :=
    H.complementPt_compIndex_succ_eval hnn hx 0`，靠 ci x 0 = 0 的
    defeq 过 elaboration 检查），直接 rw 零命中。
  - **#135 语法面三坑（构建期整改）**：(a) `p ^ k x` 把 `k x` 整体
    当指数——幂再作用于点必须加括号 `(p ^ k) x`；(b)
    `Or.inl ⟨...⟩` 的 ⟨⟩ 对 IsNodeGoing 这类 def 包装的 ∃ 无法
    定向——先落 ascription have 再 Or.inl；(c) Equiv 的两个消去
    件方向：`Equiv.symm_apply_apply : e.symm (e x) = x`、
    `Equiv.apply_symm_apply : e (e.symm x) = x`（与直觉相反，
    Hypermap.inverse_evaluation 的用法为准）。
  - **#136 ncard 门槛与 support 换算**：(a) `X = X - 1 + 1` 型目标
    在无同原子下界时 omega 整条丢弃（#127 的目标面变体）——以
    `Set.ncard_pos (orbitMap_finite ...) + mem_orbitMap_self`
    供 0 < X 后 omega 过；(b) `(s : Finset α) : Set α` 的 ascription
    coe 与 Finset.Mem 之间靠 `show`（defeq）换算，rw 的 coe 实例
    匹配不上；hLd（↑L.darts = ↑pathSupport）的消耗统一走私桥
    epcMemSupport。

  本批镜像对象（HOL Light Flyspeck，AUQTZYZ.hl :574-:1850，一件
  十二合取，四段拆分 + 私桥）：

  §0 私桥：inverseAddExponents（INVERSE_ADD_EXPONENTS 重推导，
    记档不消费）/ isInjContourIsInjList / epcFaceMapNodeMap /
    epcMapStep / epcInvMapStep / epcGoingTrans / epcGoingChain /
    epcGoingWrap / epcSymmPredNodeMap / epcNodeSymmEqOfTwo /
    pow_succ'_apply / epcMemSupport。
  §1 段①证人 L 支 + node 分裂（:574-:694）：epcNodeSplit；总装时
    EXTRA_COMP_LOOP 直投合取 1-4。
  §2 段⑤互斥+双闭包（:698-:1000，合取 5-7）：epcMemPath /
    epcDisjoint / epcStepSeg / epcStepWrapN3 / epcClosureIn /
    epcClosureFace。
  §3 段③card 支（:916-:1418，合取 8）：epcFInj / epcAtomInj /
    epcCard。
  §4 段④双射桥（:1421-:1850，合取 9-12）：epcFaceAtomSingleton /
    epcConj9 / epcConj10 / epcConj11 / epcConj12。
  §5 总装：EXISTS_PATH_COMPLEMENT（合取 1-4 = EXTRA_COMP_LOOP；
    5-12 = §2-§4 件直投）。

  批 63 接续点：AUQTZYZ_concl（:1851-:1858，is_normal 拼装件——
  is_normal {loop_of_face x, L} 双件族验证，直接消费本批
  EXISTS_PATH_COMPLEMENT 与在册 IsNormalFamily/quotient 面）+
  AUQTZYZ（:1859-:2624，765 行压尾：is_normal 分支 + dih2k
  (quotient H {L1,L2}) 卡段；:1864 起以 MRESAL EXISTS_PATH_
  COMPLEMENT[atoms_of_loop_rep] 消费本件，同面化直投）。其后章毕
  接 RXOKSKC.hl（1,105 行；**:523 RXOKSKC 是 A9 接口件，到达时
  单独标注**）。
-/
import Kepler.Text.TameSpine.TameList61

/-! # AUQTZYZ 主峰：EXISTS_PATH_COMPLEMENT（AUQTZYZ.hl :574-:1850） -/

namespace Kepler.Text.TameSpine

variable {α : Type*} [DecidableEq α]

/-! ### §0 私桥件 -/

/-- **HOL `Hypermap_and_fan.INVERSE_ADD_EXPONENTS`** 两行重推导
（缺口预警件，全库无载体；Perm 幂面 `pow_add + Equiv.Perm.mul_apply`
一发）。本批 f-单射段经 complementPt_compIndex_succ_eval 直评 +
nodeMap.symm 单射不再消费（HOL :769 消费点在 Lean 面塌缩，记档；
按批 61 处方落公开件备用）。 -/
theorem inverseAddExponents (f : Equiv.Perm α) (a b : ℕ) (x : α) :
    (f ^ (a + b)) x = (f ^ a) ((f ^ b) x) := by
  rw [pow_add, Equiv.Perm.mul_apply]

/-- `(p^(k+1)) x = p ((p^k) x)`（pow_succ' 的应用形；雷区 #132：
裸 pow_succ' 在多幂项目标上会错咬 face 侧幂，一律用本件）。 -/
private theorem pow_succ'_apply (f : Equiv.Perm α) (k : ℕ) (x : α) :
    (f ^ (k + 1)) x = f ((f ^ k) x) := by
  rw [pow_succ']; rfl

/-- `is_inj_contour`（嵌套成对定义）到 `Loop.IsInjList`（成对全称形）
的展开桥：第 `n+1` 层的第三分量（对末点的成对排除）逐层可用。 -/
private theorem isInjContourIsInjList (H : Hypermap α) {p : ℕ → α} {n : ℕ}
    (h : H.isInjContour p n) : Loop.IsInjList p n := by
  induction n with
  | zero => intro i j hi hj _; omega
  | succ k ih =>
    obtain ⟨h', -, hnew⟩ := (H.isInjContour_succ p k).mp h
    intro i j hi hj heq
    rcases Nat.eq_or_lt_of_le hj with rfl | hjlt
    · rcases Nat.eq_or_lt_of_le hi with rfl | hilt
      · rfl
      · exact absurd heq (hnew i (by omega))
    · rcases Nat.eq_or_lt_of_le hi with rfl | hilt
      · exact ((hnew j (Nat.lt_succ_iff.mp hjlt)) heq.symm).elim
      · exact ih h' i j (by omega) (by omega) heq

/-- **Plain 组合面（Lvducxu.HYP_MAPS_INVS 的 face/node 对在本章消费形，
HOL :975-:986）**：`faceMap ∘ nodeMap = nodeMap.symm ∘ faceMap.symm`。
在册 `edgeMap_mul_nodeMap`（雷区 #129）+ inv_inv 两发拼出。 -/
private theorem epcFaceMapNodeMap (H : Hypermap α) (hp : H.Plain) (w : α) :
    H.faceMap (H.nodeMap w) = H.nodeMap.symm (H.faceMap.symm w) := by
  have h9 : H.nodeMap = H.edgeMap * H.faceMap.symm :=
    H.nodeMap_eq_edgeMap_mul_faceMap_symm hp
  have hE2 : H.edgeMap.symm = H.edgeMap := by
    show H.edgeMap⁻¹ = H.edgeMap
    exact (eq_inv_of_mul_eq_one_right hp).symm
  have hnf : ∀ v, H.nodeMap (H.faceMap v) = H.edgeMap v := by
    intro v
    have h1 : H.edgeMap (H.nodeMap (H.faceMap v)) = v := by
      have h := congrArg (fun q : Equiv.Perm α => q v) H.comp_eq_one
      simpa using h
    have h2 : H.edgeMap (H.edgeMap (H.nodeMap (H.faceMap v)))
        = H.nodeMap (H.faceMap v) := by
      have h := congrArg (fun q : Equiv.Perm α => q (H.nodeMap (H.faceMap v))) hp
      simpa using h
    rw [h1] at h2
    exact h2.symm
  have hns : H.nodeMap.symm = H.faceMap * H.edgeMap := by
    apply Equiv.Perm.ext
    intro u
    apply Eq.symm
    apply Equiv.injective H.nodeMap
    show H.nodeMap ((H.faceMap * H.edgeMap) u) = H.nodeMap (H.nodeMap.symm u)
    rw [Equiv.Perm.mul_apply, hnf (H.edgeMap u), Equiv.apply_symm_apply H.nodeMap u]
    have hee : H.edgeMap (H.edgeMap u) = u := by
      have h := congrArg (fun q : Equiv.Perm α => q u) hp
      simpa using h
    exact hee
  rw [hns, Equiv.Perm.mul_apply, h9, Equiv.Perm.mul_apply]

/-- **L.map 在补路径上的任意下标求值式**（雷区 #128：p 下标先 hmod
归位，再 samsara_apply，尾段 Nat.mod_add_mod）。 -/
private theorem epcMapStep (H : Hypermap α) {L : Loop α} {p : ℕ → α} {n : ℕ}
    (hinj : Loop.IsInjList p n) (hLm : (L.map : α → α) = Loop.samsara p n)
    (hmod : ∀ m, p (m % (n + 1)) = p m) (j : ℕ) :
    (L.map : α → α) (p j) = p ((j + 1) % (n + 1)) := by
  rw [hLm, ← hmod j, Loop.samsara_apply p n hinj
    (Nat.lt_succ_iff.mp (Nat.mod_lt j (Nat.succ_pos n))), Nat.mod_add_mod]

/-- **L.invMap 在补路径上的任意下标求值式**（雷区 #128：Equiv.Perm.ext
升面 + samsaraPerm 的 invFun 定义面 = samsaraInv）。 -/
private theorem epcInvMapStep (H : Hypermap α) {L : Loop α} {p : ℕ → α} {n : ℕ}
    (hinj : Loop.IsInjList p n) (hLm : (L.map : α → α) = Loop.samsara p n)
    (hmod : ∀ m, p (m % (n + 1)) = p m) (j : ℕ) :
    (L.invMap : α → α) (p j) = p ((j + n) % (n + 1)) := by
  have hE : L.map = Loop.samsaraPerm hinj := Equiv.Perm.ext (fun y => by
    rw [hLm]
    rfl)
  have him : L.invMap = (Loop.samsaraPerm hinj).symm := by
    show L.map.symm = (Loop.samsaraPerm hinj).symm
    rw [hE]
  rw [him, ← hmod j]
  have h1 : (Loop.samsaraPerm hinj).symm (p (j % (n + 1)))
      = Loop.samsaraInv p n (p (j % (n + 1))) := rfl
  rw [h1, Loop.samsaraInv_apply p n hinj
    (Nat.lt_succ_iff.mp (Nat.mod_lt j (Nat.succ_pos n))), Nat.mod_add_mod]

/-- going 传递（雷区 #132：k1+k2 幂加法 + 分段 agree 拼装）。 -/
private theorem epcGoingTrans (H : Hypermap α) {L : Loop α} {a b c : α}
    (h1 : H.IsNodeGoing L a b) (h2 : H.IsNodeGoing L b c) :
    H.IsNodeGoing L a c := by
  obtain ⟨k1, hb, ag1⟩ := h1
  obtain ⟨k2, hc, ag2⟩ := h2
  refine ⟨k1 + k2, ?_, ?_⟩
  · rw [show k1 + k2 = k2 + k1 from Nat.add_comm k1 k2, pow_add,
      Equiv.Perm.mul_apply, ← hb, hc]
  · intro t ht
    rcases Nat.lt_or_ge t k1 with hlt | hge
    · exact ag1 t (by omega)
    · have hs : t - k1 ≤ k2 := by omega
      have e1 : (L.map ^ t) a = (L.map ^ (t - k1)) b := by
        conv_lhs => rw [show t = t - k1 + k1 from by omega, pow_add,
          Equiv.Perm.mul_apply, ← hb]
      conv_rhs => rw [show t = t - k1 + k1 from by omega, pow_add,
        Equiv.Perm.mul_apply]
      rw [e1, ag2 _ hs, hb, ag1 k1 le_rfl]

/-- 段内链：`p m₀ → p m`（m₀ ≤ m ≤ n）且每步 `nodeMap.symm (p t) =
p (t+1)` 时 going 成立（对步数 k 归纳，雷区 #132）。 -/
private theorem epcGoingChain (H : Hypermap α) {L : Loop α} {p : ℕ → α} {n : ℕ}
    (hinj : Loop.IsInjList p n) (hLm : (L.map : α → α) = Loop.samsara p n)
    (m₀ : ℕ) :
    ∀ k m : ℕ, m = m₀ + k → m ≤ n →
      (∀ t, m₀ ≤ t → t < m → H.nodeMap.symm (p t) = p (t + 1)) →
      H.IsNodeGoing L (p m₀) (p m) := by
  intro k
  induction k with
  | zero =>
    intro m hm _ _
    have h0m : m₀ = m := by omega
    subst h0m
    have hbase : H.IsNodeGoing L (p m₀) (p m₀) :=
      ⟨0, rfl, fun i hi => by rw [Nat.le_zero.mp hi, pow_zero, pow_zero]⟩
    exact hbase
  | succ l ih =>
    intro m hm hmn hstep
    have hprev : H.IsNodeGoing L (p m₀) (p (m - 1)) :=
      ih (m - 1) (by omega) (by omega) (fun t ht1 ht2 => hstep t ht1 (by omega))
    have hstepLm : (L.map : α → α) (p (m - 1)) = p m := by
      rw [hLm, Loop.samsara_apply p n hinj (by omega),
        Nat.mod_eq_of_lt (by omega : m - 1 + 1 < n + 1)]
      exact congrArg p (by omega)
    have hlast : H.IsNodeGoing L (p (m - 1)) (p m) := ⟨1, hstepLm.symm, by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [pow_zero, pow_zero]
      · have hi1 : i = 1 := by omega
        subst hi1
        rw [pow_one, pow_one, hstepLm,
          hstep (m - 1) (by omega) (by omega)]
        exact congrArg p (by omega)⟩
    exact epcGoingTrans H hprev hlast

/-- 收口链：`p m₀ → p 0`（m₀ ≤ n）：段内链到 `p n`，再走收口步
（L.map (p n) = p 0 与 nodeMap.symm (p n) = p 0 由 hstep n 给出）。
hstep 的下标到 n 含端点（以 `(t+1) % (n+1)` 形承载，雷区 #128）。 -/
private theorem epcGoingWrap (H : Hypermap α) {L : Loop α} {p : ℕ → α} {n : ℕ}
    (hinj : Loop.IsInjList p n) (hLm : (L.map : α → α) = Loop.samsara p n)
    (m₀ : ℕ) (hm₀ : m₀ ≤ n)
    (hstep : ∀ t, m₀ ≤ t → t ≤ n → H.nodeMap.symm (p t) = p ((t + 1) % (n + 1))) :
    H.IsNodeGoing L (p m₀) (p 0) := by
  have hseg : H.IsNodeGoing L (p m₀) (p n) :=
    epcGoingChain H hinj hLm m₀ (n - m₀) n (by omega) (Nat.le_refl n)
      (fun t ht1 ht2 => by
        rw [hstep t ht1 (by omega), Nat.mod_eq_of_lt (by omega : t + 1 < n + 1)])
  have hlast : H.IsNodeGoing L (p n) (p 0) := ⟨1, by
    rw [pow_one, hLm, Loop.samsara_apply p n hinj (Nat.le_refl n), Nat.mod_self], by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [pow_zero, pow_zero]
    · have hi1 : i = 1 := by omega
      subst hi1
      rw [pow_one, pow_one, hLm, Loop.samsara_apply p n hinj (Nat.le_refl n),
        Nat.mod_self]
      rw [hstep n hm₀ (Nat.le_refl n), Nat.mod_self]⟩
  exact epcGoingTrans H hseg hlast

/-- `nodeMap.symm^(N-1) z = nodeMap z`（N = |node z|；segment-cf
修正式的载体件）：两侧同施 nodeMap^(N-1)，左 = z
（perm_pow_symm_pow_apply_ge + sub_self + pow_zero），右 =
z（pow_card_node_apply_self 的 pow_succ 拆分）。 -/
private theorem epcSymmPredNodeMap (H : Hypermap α) (z : α) :
    (H.nodeMap.symm ^ ((H.node z).ncard - 1)) z = H.nodeMap z := by
  have hcancel : (H.nodeMap ^ ((H.node z).ncard - 1))
      ((H.nodeMap.symm ^ ((H.node z).ncard - 1)) z) = z := by
    have h := perm_pow_symm_pow_apply_ge (p := H.nodeMap)
      (s := (H.node z).ncard - 1) (t := (H.node z).ncard - 1) (Nat.le_refl _) z
    rwa [Nat.sub_self, pow_zero] at h
  have hN1 : (H.node z).ncard - 1 + 1 = (H.node z).ncard := by
    have hzpos : 0 < (H.node z).ncard := by
      show 0 < (orbitMap H.nodeMap z).ncard
      rw [Set.ncard_pos (orbitMap_finite H.nodeMap_permutes z)]
      exact ⟨z, H.mem_node_self z⟩
    omega
  have hR : (H.nodeMap ^ ((H.node z).ncard - 1)) (H.nodeMap z) = z := by
    have e : (H.nodeMap ^ ((H.node z).ncard - 1 + 1)) z
        = (H.nodeMap ^ ((H.node z).ncard - 1)) (H.nodeMap z) := by
      rw [pow_succ, Equiv.Perm.mul_apply]
    rw [← e, hN1]
    exact H.pow_card_node_apply_self z
  refine Equiv.injective (H.nodeMap ^ ((H.node z).ncard - 1)) ?_
  rw [hcancel, hR]

/-- N = 2 时 nodeMap.symm x = nodeMap x（nodeMap² x = x 的等价形；
合取 10/11 的 N_x = 2 支用）。 -/
private theorem epcNodeSymmEqOfTwo (H : Hypermap α) (x : α)
    (hN2 : (H.node x).ncard = 2) : H.nodeMap.symm x = H.nodeMap x := by
  have h2 : (H.nodeMap ^ 2) x = x := by
    have h := H.pow_card_node_apply_self x
    rwa [show H.nodeMap ^ (H.node x).ncard = H.nodeMap ^ 2 from by rw [hN2]] at h
  exact Equiv.injective H.nodeMap (by
    rw [Equiv.apply_symm_apply]
    exact h2.symm)

/-- node 基数正性（任意 dart；供 mod_lt/omega 门楽）。 -/
private theorem epcNodePos (H : Hypermap α) (hnn : H.NodeNondegenerate) {u : α}
    (hu : u ∈ H.darts) : 0 < (H.node u).ncard := by
  show 0 < (orbitMap H.nodeMap u).ncard
  rw [Set.ncard_pos (orbitMap_finite H.nodeMap_permutes u)]
  exact ⟨u, H.mem_node_self u⟩

/-- **hLd 换算桥（雷区 #136）**：y ∈ L.darts ⟹ ∃ m ≤ n，p m = y
（hLd 的 coe 实例面经 show-defeq 统一）。 -/
private theorem epcMemSupport (H : Hypermap α) {x : α} (n : ℕ) {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    {y : α} (hy : y ∈ L.darts) :
    ∃ m ≤ n, H.complementPt x m = y := by
  have h1 : y ∈ (Loop.pathSupport (H.complementPt x) n : Set α) := by
    rw [← hLd]
    exact Finset.mem_coe.mpr hy
  have h2 : y ∈ Loop.pathSupport (H.complementPt x) n := h1
  rw [Loop.mem_pathSupport] at h2
  exact h2

/-! ### §1 段①证人 L 支：node 分裂（AUQTZYZ.hl :666-:686） -/

/-- 补路径首两点异 node：`node (p 0) = node (p 1)` 导出
`faceMap.symm x = x`，与面轨道窗口单射（j = 1 < CARD face）矛盾。
（HOL :666-:686 走 lemma_different_nodes + CARD_FACE_LE3；Lean 面
塌缩到 orbitMap_pow_inj 一发，终点同——雷区 #122 体例。） -/
private theorem epcNodeSplit (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) :
    H.node (H.complementPt x 0) ≠ H.node (H.complementPt x 1) := by
  intro hcon
  have hnn := hr.nodeNondegenerate
  have hs := hr.simple
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  -- 雷区 #134：字面下标 1 先经 ascription have 塌缩
  have h01 : H.complementPt x 1 = H.nodeMap.symm ((H.faceMap.symm ^ 1) x) :=
    H.complementPt_compIndex_succ_eval hnn hx 0
  rw [h01, show H.complementPt x 0 = H.nodeMap x from rfl] at hcon
  have h1 : H.node (H.nodeMap x) = H.node x :=
    (H.node_eq_of_mem (H.pow_nodeMap_mem_node x 1)).symm
  have h2 : H.node (H.nodeMap.symm ((H.faceMap.symm ^ 1) x))
      = H.node ((H.faceMap.symm ^ 1) x) :=
    (H.node_eq_of_mem
      (H.nodeMap_symm_mem_node (H.mem_node_self ((H.faceMap.symm ^ 1) x)))).symm
  rw [h1, h2] at hcon
  have hmem : (H.faceMap.symm ^ 1) x ∈ H.node x := by
    rw [hcon]
    exact H.mem_node_self _
  have hfin : (H.faceMap.symm ^ 1) x ∈ H.face x :=
    H.faceMap_symm_pow_mem_face_self x 1
  have hmem2 : (H.faceMap.symm ^ 1) x ∈ H.node x ∩ H.face x := ⟨hmem, hfin⟩
  rw [hs x hx] at hmem2
  have heq : (H.faceMap.symm ^ 1) x = x := Set.mem_singleton_iff.mp hmem2
  have hz0 : (H.faceMap.symm ^ 0) x = (H.faceMap.symm ^ 1) x := by
    show x = H.faceMap.symm x
    exact heq.symm
  refine orbitMap_pow_inj (p := H.faceMap.symm) H.faceMap_permutes.symm
    (a := 0) (b := 1) (by omega) ?_ hz0
  rw [PermutesOn.orbitMap_symm H.faceMap_permutes x]
  show 1 < (H.face x).ncard
  omega

/-! ### §2 段⑤：互斥与双闭包（AUQTZYZ.hl :698-:1000，合取 5-7） -/

/-- **均匀成员件（本批主方法论）**：任意下标 m 的补路径点都在
L.darts（p m = p (m % (n+1))，hmod 一发；压平 HOL 全部 support 下标
±1 边界 case）。 -/
private theorem epcMemPath (H : Hypermap α) {x : α} (n : ℕ) {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m) (m : ℕ) :
    H.complementPt x m ∈ L.darts := by
  have h1 : H.complementPt x m ∈ (Loop.pathSupport (H.complementPt x) n : Set α) := by
    show H.complementPt x m ∈ Loop.pathSupport (H.complementPt x) n
    rw [Loop.mem_pathSupport]
    exact ⟨m % (n + 1), Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos n)),
      hmod m⟩
  rw [← hLd] at h1
  exact Finset.mem_coe.mpr h1

/-- **合取 5 核**：补路径前 n+1 点无一在 face x 内。
i = 0 支：nodeMap x = x ⟹ 轨道单点 ⟹ |node x| ≤ 1（HOL :708-:713）；
1 ≤ i 支：strictInc_partition₂ 分解 + Simple 单点塌出
nodeMap.symm^j z = z，orbitMap_pow_inj 灭（HOL :715-:733）。 -/
private theorem epcDisjoint (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) (hn : H.complementIndex x (H.face x).ncard - 1 = n) :
    ∀ m ≤ n, H.complementPt x m ∉ H.face x := by
  have hnn := hr.nodeNondegenerate
  have hs := hr.simple
  have hn2x : 2 ≤ (H.node x).ncard := H.nodeNondegenerate_two_le.mp hnn x hx
  intro m hm hmem
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · have hmem2 : H.nodeMap x ∈ H.node x ∩ H.face x :=
      ⟨H.pow_nodeMap_mem_node x 1, hmem⟩
    rw [hs x hx] at hmem2
    have hfix : H.nodeMap x = x := Set.mem_singleton_iff.mp hmem2
    have hsingle : H.node x = {x} := (orbitMap_singleton_iff H.nodeMap x).mpr hfix
    rw [hsingle] at hn2x
    simp at hn2x
  · obtain hzero | ⟨i, j, hj1, hj2, hrep⟩ := strictInc_partition₂
      (f := H.complementIndex x) (H.complementIndex_zero_eq x)
      (H.complementIndex_lt_succ hnn hx) m
    · exact absurd hzero (by omega)
    have hjN : j < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard := by
      have hs2 := H.complementIndex_succ_eq_sub hnn hx i
      omega
    have hev : H.complementPt x m
        = (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ (i + 1)) x) := by
      rw [hrep]
      exact H.complementPt_add_eval hnn hx i j hj1 hjN
    have hz : (H.faceMap.symm ^ (i + 1)) x ∈ H.darts :=
      H.faceMap_symm_pow_mem_darts hx (i + 1)
    have hmemn : H.complementPt x m ∈ H.node ((H.faceMap.symm ^ (i + 1)) x) := by
      rw [hev]
      exact H.nodeMap_symm_pow_mem_node_self _ j
    have hfacez : H.face x = H.face ((H.faceMap.symm ^ (i + 1)) x) :=
      H.face_eq_of_mem (H.faceMap_symm_pow_mem_face_self x (i + 1))
    have hmem2 : H.complementPt x m ∈ H.node ((H.faceMap.symm ^ (i + 1)) x) ∩
        H.face ((H.faceMap.symm ^ (i + 1)) x) := ⟨hmemn, by rw [← hfacez]; exact hmem⟩
    rw [hs _ hz] at hmem2
    have hfixz : (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ (i + 1)) x)
        = (H.faceMap.symm ^ (i + 1)) x :=
      hev.symm.trans (Set.mem_singleton_iff.mp hmem2)
    have hbm : j < (orbitMap H.nodeMap.symm ((H.faceMap.symm ^ (i + 1)) x)).ncard := by
      rw [PermutesOn.orbitMap_symm H.nodeMap_permutes]
      show j < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard
      exact hjN
    exact orbitMap_pow_inj (p := H.nodeMap.symm) H.nodeMap_permutes.symm
      (a := 0) (b := j) hj1 hbm (by rw [pow_zero, Equiv.Perm.one_apply, hfixz])

/-- 段内 nodeMap.symm 步：`ci x i + 1 ≤ t ≤ ci x (i+1) - 1` 时
`nodeMap.symm (p t) = p (t+1)`（segEval 双发）。 -/
private theorem epcStepSeg (H : Hypermap α) {x : α} (hnn : H.NodeNondegenerate)
    (hx : x ∈ H.darts) (i t : ℕ)
    (h1 : H.complementIndex x i + 1 ≤ t)
    (h2 : t + 1 ≤ H.complementIndex x (i + 1)) :
    H.nodeMap.symm (H.complementPt x t) = H.complementPt x (t + 1) := by
  have hciS : H.complementIndex x (i + 1)
      = H.complementIndex x i + ((H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard - 1) :=
    H.complementIndex_succ_eq_sub hnn hx i
  have hj1 : 1 ≤ t - H.complementIndex x i := by omega
  have hjN : t - H.complementIndex x i + 1
      < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard := by omega
  have hev1 : H.complementPt x t
      = (H.nodeMap.symm ^ (t - H.complementIndex x i))
        ((H.faceMap.symm ^ (i + 1)) x) := by
    conv_lhs => rw [show t = H.complementIndex x i + (t - H.complementIndex x i) from by omega]
    exact H.complementPt_add_eval hnn hx i _ hj1 (by omega)
  have hev2 : H.complementPt x (t + 1)
      = (H.nodeMap.symm ^ (t - H.complementIndex x i + 1))
        ((H.faceMap.symm ^ (i + 1)) x) := by
    have h3 : H.complementPt x (t + 1)
        = H.complementPt x (H.complementIndex x i
          + (t - H.complementIndex x i + 1)) := by
      rw [show t + 1 = H.complementIndex x i
        + (t - H.complementIndex x i + 1) from by omega]
    rw [h3, H.complementPt_add_eval hnn hx i _ (by omega) (by omega)]
  rw [hev1, hev2, pow_succ'_apply H.nodeMap.symm (t - H.complementIndex x i) _]

/-- 收口步（N_x ≥ 3）：`nodeMap.symm (p n) = p 0`。
p n = symm^(N_x-2) z_cf（尾段末点），symm 后 = symm^(N_x-1) z_cf =
nodeMap z_cf（epcSymmPredNodeMap）= nodeMap x（cycle）= p 0。 -/
private theorem epcStepWrapN3 (H : Hypermap α) {x : α} (hnn : H.NodeNondegenerate)
    (hx : x ∈ H.darts) (n : ℕ) (hn : H.complementIndex x (H.face x).ncard - 1 = n)
    (hcf3 : 3 ≤ (H.face x).ncard) (hN3 : 3 ≤ (H.node x).ncard) :
    H.nodeMap.symm (H.complementPt x n) = H.complementPt x 0 := by
  have hp0 : H.complementPt x 0 = H.nodeMap x := rfl
  have h1cf : 1 ≤ H.complementIndex x (H.face x).ncard :=
    complementIndexFaceLe1 H hnn hx
  have hNcf : (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard
      = (H.node x).ncard := by
    refine congrArg (fun v => (H.node v).ncard) ?_
    exact inverseFaceCycle H x
  have hci1 : H.complementIndex x (H.face x).ncard
      = H.complementIndex x ((H.face x).ncard - 1) + ((H.node x).ncard - 1) := by
    have h2 := H.complementIndex_succ_eq_sub hnn hx ((H.face x).ncard - 1)
    rw [show (H.face x).ncard - 1 + 1 = (H.face x).ncard from by omega] at h2
    rwa [hNcf] at h2
  have hk1 : 1 ≤ n - H.complementIndex x ((H.face x).ncard - 1) := by omega
  have hk2 : n - H.complementIndex x ((H.face x).ncard - 1) < (H.node x).ncard := by
    omega
  have hev : H.complementPt x n
      = (H.nodeMap.symm ^ (n - H.complementIndex x ((H.face x).ncard - 1)))
        ((H.faceMap.symm ^ (H.face x).ncard) x) := by
    conv_lhs => rw [show n = H.complementIndex x ((H.face x).ncard - 1)
      + (n - H.complementIndex x ((H.face x).ncard - 1)) from by omega]
    have hcfN2 : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
    have hlt : n - H.complementIndex x ((H.face x).ncard - 1)
        < (H.node ((H.faceMap.symm ^ ((H.face x).ncard - 1 + 1)) x)).ncard := by
      rw [hcfN2, hNcf]
      omega
    have h5 := H.complementPt_add_eval hnn hx ((H.face x).ncard - 1)
      (n - H.complementIndex x ((H.face x).ncard - 1)) hk1 hlt
    rwa [hcfN2] at h5
  have step1 : H.nodeMap.symm
      ((H.nodeMap.symm ^ (n - H.complementIndex x ((H.face x).ncard - 1)))
        ((H.faceMap.symm ^ (H.face x).ncard) x))
      = (H.nodeMap.symm ^ ((H.node x).ncard - 1))
        ((H.faceMap.symm ^ (H.face x).ncard) x) := by
    rw [← pow_succ'_apply H.nodeMap.symm
      (n - H.complementIndex x ((H.face x).ncard - 1))
      ((H.faceMap.symm ^ (H.face x).ncard) x),
      show n - H.complementIndex x ((H.face x).ncard - 1) + 1
        = (H.node x).ncard - 1 by omega]
  rw [hev, step1, ← hNcf, epcSymmPredNodeMap, inverseFaceCycle, hp0]

/-- **合取 6**：y ∈ L ⟹ z ∈ node y ⟹ z ∈ L ∨ z ∈ face x。
（HOL :735-:885 的全线 case 分析；hmod 均匀成员件压平 witness。） -/
private theorem epcClosureIn (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m)
    (y : α) (hy : y ∈ L.darts) (z : α) (hz : z ∈ H.node y) :
    z ∈ L.darts ∨ z ∈ H.face x := by
  have hnn := hr.nodeNondegenerate
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  have hmem : ∀ m, H.complementPt x m ∈ L.darts := fun m => epcMemPath H n hLd hmod m
  obtain ⟨m, hm, hym⟩ := epcMemSupport H n hLd hy
  obtain ⟨j, hjN, hzj⟩ := H.exists_pow_nodeMap_symm_apply_of_mem_node hz
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact Or.inl (by rw [hzj, pow_zero]; exact hy)
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · -- y = p 0 = nodeMap x：j = 1 给 x ∈ face x；j ≥ 2 走尾段 witness
    have hyn : y = H.nodeMap x := by rw [← hym]; rfl
    have hny : (H.node y).ncard = (H.node x).ncard := by
      rw [hyn, nodeNodeMapEq H x]
    rw [hny] at hjN
    have hzm : z = (H.nodeMap.symm ^ j) (H.nodeMap x) := by rw [hzj, hyn]
    have hjm : j = j - 1 + 1 := by omega
    have hz1 : z = (H.nodeMap.symm ^ (j - 1)) x := by
      rw [hzm]
      conv_lhs => rw [hjm, pow_succ, Equiv.Perm.mul_apply]
      rw [Equiv.symm_apply_apply]
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hje : j = 1 := by omega
      rw [hje] at hz1
      refine Or.inr ?_
      rw [hz1, show (1:ℕ) - 1 = 0 from by omega, pow_zero]
      exact mem_orbitMap_self H.faceMap x
    · have hNcf : (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard
          = (H.node x).ncard := by
        refine congrArg (fun v => (H.node v).ncard) ?_
        exact inverseFaceCycle H x
      have hcf1 : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
      have hkN : j - 1 < (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard := by
        omega
      have hev : H.complementPt x (H.complementIndex x ((H.face x).ncard - 1)
            + (j - 1))
            = (H.nodeMap.symm ^ (j - 1))
              ((H.faceMap.symm ^ ((H.face x).ncard - 1 + 1)) x) :=
        H.complementPt_add_eval hnn hx _ _ (by omega)
          (by rw [show (H.face x).ncard = (H.face x).ncard - 1 + 1 from by omega] at hkN
              exact hkN)
      rw [hcf1] at hev
      refine Or.inl ?_
      rw [hz1, show x = (H.faceMap.symm ^ (H.face x).ncard) x from (inverseFaceCycle H x).symm,
        ← hev]
      exact hmem _
  · -- m ≥ 1：strictInc 分解，j+j₀ 取模 N_{i+1} 后段内 witness
    obtain hzero | ⟨i, j₀, hj1₀, hj2₀, hrep⟩ := strictInc_partition₂
      (f := H.complementIndex x) (H.complementIndex_zero_eq x)
      (H.complementIndex_lt_succ hnn hx) m
    · exact absurd hzero (by omega)
    have hjN₀ : j₀ < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard := by
      have hs2 := H.complementIndex_succ_eq_sub hnn hx i
      omega
    have hevy : y = (H.nodeMap.symm ^ j₀) ((H.faceMap.symm ^ (i + 1)) x) := by
      rw [← hym, hrep]
      exact H.complementPt_add_eval hnn hx i j₀ hj1₀ hjN₀
    have hzK : z = (H.nodeMap.symm ^
        ((j + j₀) % (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard))
        ((H.faceMap.symm ^ (i + 1)) x) := by
      rw [hzj, hevy, ← Equiv.Perm.mul_apply, ← pow_add,
        inverseNodeMod H ((H.faceMap.symm ^ (i + 1)) x) (j + j₀)]
    rcases Nat.eq_zero_or_pos
      ((j + j₀) % (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard) with hK0 | hK1
    · refine Or.inr ?_
      rw [hzK, hK0, pow_zero]
      exact H.faceMap_symm_pow_mem_face_self x (i + 1)
    · refine Or.inl ?_
      rw [hzK, ← H.complementPt_add_eval hnn hx i _ hK1
        (Nat.mod_lt _ (epcNodePos H hnn
          (H.faceMap_symm_pow_mem_darts hx (i + 1))))]
      exact hmem _

/-- **合取 7**：y ∈ face x ⟹ z ∈ node y ⟹ z ∈ L ∨ z ∈ face x。
（HOL :917-:1000；i = 0 支的 j = N-1 端点经 epcSymmPredNodeMap 落
p 0。） -/
private theorem epcClosureFace (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m)
    (y : α) (hy : y ∈ H.face x) (z : α) (hz : z ∈ H.node y) :
    z ∈ L.darts ∨ z ∈ H.face x := by
  have hnn := hr.nodeNondegenerate
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  have hn2x : 2 ≤ (H.node x).ncard := H.nodeNondegenerate_two_le.mp hnn x hx
  have hmem : ∀ m, H.complementPt x m ∈ L.darts := fun m => epcMemPath H n hLd hmod m
  obtain ⟨i, hi, hyi⟩ := lemmaViaInverseFaceMap H hy
  obtain ⟨j, hjN, hzj⟩ := H.exists_pow_nodeMap_symm_apply_of_mem_node hz
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact Or.inr (by rw [hzj, pow_zero]; exact hy)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · -- y = x：j = N-1 端点给 nodeMap x = p 0 ∈ L；j ≤ N-2 走尾段
    have hz1 : z = (H.nodeMap.symm ^ j) x := by
      rw [hzj, hyi, pow_zero, Equiv.Perm.one_apply]
    rw [hyi, pow_zero, Equiv.Perm.one_apply] at hjN
    rcases Nat.lt_or_ge j ((H.node x).ncard - 1) with hj2 | hj2
    · have hNcf : (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard
          = (H.node x).ncard := by
        refine congrArg (fun v => (H.node v).ncard) ?_
        exact inverseFaceCycle H x
      have hcf1 : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
      have hkN : j < (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard := by
        omega
      have hev : H.complementPt x (H.complementIndex x ((H.face x).ncard - 1) + j)
          = (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ ((H.face x).ncard - 1 + 1)) x) :=
        H.complementPt_add_eval hnn hx _ _ hj0
          (by rw [show (H.face x).ncard = (H.face x).ncard - 1 + 1 from by omega] at hkN
              exact hkN)
      rw [hcf1] at hev
      refine Or.inl ?_
      rw [hz1, show x = (H.faceMap.symm ^ (H.face x).ncard) x from
        (inverseFaceCycle H x).symm, ← hev]
      exact hmem _
    · have hje : j = (H.node x).ncard - 1 := by omega
      refine Or.inl ?_
      rw [hz1, hje, epcSymmPredNodeMap]
      exact hmem 0
  · -- y = z_i（1 ≤ i < cf）：z = symm^j z_i，段 i 内 witness ci (i-1) + j
    have hz1 : z = (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ i) x) := by
      rw [hzj, hyi]
    have hjN2 : j < (H.node ((H.faceMap.symm ^ i) x)).ncard := by
      rw [hyi] at hjN
      exact hjN
    have hcf1 : i - 1 + 1 = i := by omega
    have hev : H.complementPt x (H.complementIndex x (i - 1) + j)
        = (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ (i - 1 + 1)) x) := by
      rw [← hcf1] at hjN2
      exact H.complementPt_add_eval hnn hx _ _ hj0 hjN2
    rw [hcf1] at hev
    refine Or.inl ?_
    rw [hz1, ← hev]
    exact hmem _

/- 本批止损：§0-§2 私桥件 + §1 node 分裂件 + §2 互斥/双闭包件 全部落件。
§3 card 支 + §4 双射桥 + §5 总装 EXISTS_PATH_COMPLEMENT 未竞，留批 63 接续。
完整草稿见 TameList62_full_draft.lean。 -/

end Kepler.Text.TameSpine
