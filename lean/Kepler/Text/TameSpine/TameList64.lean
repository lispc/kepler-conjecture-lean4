/-
  Kepler.Text.TameSpine.TameList64 — B3 D 链第五批：AUQTZYZ 章收章
  （AUQTZYZ.hl :1851-:2624 压尾段：AUQTZYZ_concl 语句 + AUQTZYZ
  is_normal {loop_of_face x, L} 双件族拼装 + 商 hypermap dih2k 组装）。
  接续批 63 = TameList63.lean（aa81f704，EXISTS_PATH_COMPLEMENT 十二合
  取全闭）；本批落地 = AUQTZYZ 章（AUQTZYZ.hl :23-:2624 全本）收口，
  **W2 起跑段宣告完成，B3 首本收官**。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ 公开件 1：AUQTZYZ（HOL AUQTZYZ_concl :1851-:1858 语句 + 主证明
  │ :1859-:2613 全链）。四件半 dih2k 无条件闭合：① CARD = 2k（原子族
  │ 并集卡 + cardAtomLoopOfFace + 合取⑧）；② 面轨道覆盖（⊆：轨道保族
  │ + 商 node 置换单射；⊇：⑩⑪桥造 B/A 侧原像，HOL :2047-:2215 的去
  │ 指标重构）；③ face_map k 阶（orbit_cyclic 轨道枚举 +
  │ CARD_ITER_K_EK_IMP_DIST_FUNTION 反证 + orbit 代表回环）；⑤
  │ node_map 2 阶（A 支 ⑩ 尾桥识别 tail NF u = ⑩桥 y'——
  │ tailOfAtom_eq_self_iff + change_parameters；B 支 simple 单点钉
  │ q = N (tail NF (N v)) = v：面像∈face 走尾桥、node-orbit 平移
  │ node (N z) = node z、原子⊆node，simple 交单点）；④ edge_map ≠ 1
  │ 半部（eQuotientPerm_via_atomChoice 求值 + plain = nodeMap∘faceMap
  │ + 合取⑫）。edge_map 对合半部：A 支全闭（两发 eQuotient 求值 +
  │ plain 平方弹回首点 + head 自头于面点）；B 支精确依赖一个点等式
  │ （前件 hedge 承载，见批 65 接续点）。is_normal 四合取全闭
  │ （:1870-:1985）：②的 face 环异 node 双点走 simple 塌缩 +
  │ orbitMap_singleton + 3 ≤ CARD face（CARD_FACE_LE3 同面）；③混支
  │ 走合取⑤不交面。全件零 sorry；公理面 propext/Classical.choice/
  │ Quot.sound 标准三内（探针输出见尾锚）。构建纯 lake build
  │ Kepler.Text.TameSpine.TameList64 单发串行零旗标零 -K，clone 绿
  │ 9496 jobs 零警告。
  │ 语句编码裁定：HOL 的 `quotient H {L1,L2}` 需 is_normal 证据作参
  │ （quotientHypermap hnf），Lean 依存类型以 ∃ 组件携带 hnf——与
  │ HOL ∧-合取逐字同形，差异仅编码面；edge 对合半部的前件以蕴含
  │ 挂在第三组件，批 65 闭合后即 HOL 全形。
  └──────────────────────────────────────────────────────────────

  新雷区（本批实测记档，编号承批 63 的 #144）：
  - **#145 Dih2k 组件序 = card / coverage / face k / edge 2 / node 2**
    （localization.hl:30；face 之后是 EDGE 再 NODE）——按 face→node→
    edge 序写段会拿错 heq（node 段拿到 edgeMap = 1 的假设，报
    edgeMap-pattern 对 nodeMap-目标 rewrite 失败）。
  - **#146 商 dart 卡换算不走 Finite.card_toFinset**（需 [Fintype]
    不可得）：quotientHypermap 的 darts 字段即 (atomsOfFamily).toFinset
    定义性相等，用 Set.ncard_coe_finset（(↑s).ncard = s.card）+
    quotientHypermap_spec.1 两发换算。
  - **#147 rcases-rfl 的消元方向**：`with rfl | rfl` 按等式右侧变量
    优先消元——`L'' = L` 形会把外层 L 消掉（后续 Unknown identifier
    L、hL5 显形 L''.darts）；一律具名 hE + 显式定向 subst（要消的
    变量放等式右侧）。
  - **#148 Finset/Set 双形态成员**：EPC 合取⑥⑦ binder、hL12 的
    x1 ∈ H.face x 是 Set-mem；loopOfFace_darts/atomsOfLoop 的 dart
    项是 Finset-mem——H.mem_faceFinset x _ 的 .mp/.mpr 一词互转；
    hldOF（↑coerced 等式）不能 rw 进 Finset-mem 目标（ rw 报找不到
    ↑-模式）。
  - **#149 rw-at 全 occurrence 双咬**：hpiece.2.1（F h = tail (F h)
    形）at-重写会把 RHS 里的 F h 一并替换成 tail (tail (F h))——
    conv_lhs => rw [同件] 限定左侧。
  - **#150 atom_eq_of_mem 方向**：(h : y ∈ atom L x) 给 atom L x =
    atom L y——⑩第四片（N² y' ∈ atom L u）收口 B 支目标
    atom L (N² y') = atom L u 时须 .symm。
  - **#151 轨道词的命名空间**：orbitMap_eq_of_mem 在 root（Hypermap.lean
    的 section PermIteration 内、namespace Hypermap 之外）；
    PermutesOn.symm_apply_mem_orbitMap 在 Hypermap.PermutesOn——
    H.orbitMap_eq_of_mem 点法报 unknown field。
  - **#152 Equiv.Perm 等式逐点化**：`(p^k) = 1` 上 funext 不适用
    （FunLike-coe 层 apply-failed），用 refine Equiv.Perm.ext
    fun y => ?_；Q.edgeMap^2-应用与 product-复合仅 rfl 可换，rw 需
    语法匹配——逐支先 show 换算成 product 形再 rw。
  - **#153 POW↔ITER 桥**：CARD_ITER_K_EK_IMP_DIST_FUNTION 消费
    f^[n]-形，orbit_cyclic 给 (f^n) x-形——permPowIterate 私桥一词
    互化（Mathlib 无可 rw 的 coe_pow 名，归纳两行自证）。
  - **#154 loopOfFace_map_pow_apply 的 hy 是 Set-face-mem**：Finset
    侧须先换算；face_eq_of_mem 当 rw-lemma 用会按 goal 的 face x 咬定
    y := x——以 have hfe 显式方程 + rw [hfe] 定向。
  - **#155 face_eq_of_mem/atom_eq_of_mem 的 ▸ 传输**：membership 证
    明跨集方程传输用 (e ▸ h : 显式类型) 原子化（裸 ▸ 走 goal-motive
    常咬错方向）；calc 的 ∈-步在 Set 值域上解析歧义（LHS 被读成
    Set），一律 e1.trans e2 ▸ hqN 一词。

  批 65 接续点（AUQTZYZ 章已收，下一本 RXOKSKC.hl，1,105 行；
  **:523 RXOKSKC 为 A9 接口件，到达时单独标注**）：
  - **首选： discharge 本件 hedge 前件**——edge 对合半部 B 支的点
    等式 `∀ v ∈ face x, nodeMap (faceMap (headOfAtom NF (nodeMap
    (faceMap v)))) = v`（NF = {loop_of_face x, L}）。处方：
    (a) 已知件——E (atom lOFx v) = atom L (N (F v))（eQuotient 求值
        + head 自头于面点 + ⑫）；A 支全闭可复用；
    (b) 路线 1（HOL :2400-:2450 同源）：w := N (F v) ∈ L.darts，
        ⑩ 尾桥识别给 tailOfAtom NF w = ⑩桥 y'；fQuotient 求值第二片
        （F (head NF w) = tail NF (F (head NF w))，自尾）+ TAIL-BRIDGE
        把 edge H (head NF w) 钉进 face x；head NF w 的 F-像经
        plain edgeMap² = h（h = head NF u 那套两发求值）回环——B 支
        目标化为「edge H (head NF (N (F v))) = v」的点钉，可走
        simple 单点（v ∈ node (N (F v)) 平移 + face 像属面）；
    (c) 路线 2（已验证可行）：先证 ID-EDGE 点等式
        `N (tailOfAtom NF (N (F v))) = F v`——q := N (tail NF (N (F v)))，
        q ∈ face x 走尾桥（w = N (F v) ∈ L）、q ∈ node (F v) 走
        node-orbit 平移（node (N z) = node z）+ 原子⊆node + 尾∈原子，
        simple 单点钉 q = F v；再以已证的 nQ 对合把 E 分解为
        fQ⁻¹∘nQ 逐点求值——注意 fQ⁻¹ 在 A 上的显式公式不可得
        （head/tail 往返），A 支须同步改走 atomChoice-head 路（本批
        A 支已有该形式，可直接复用其一步式）；
    (d) hedge 取得后，AUQTZYZ 蕴含前件脱落，即 HOL AUQTZYZ_concl
        全形；随后开 RXOKSKC.hl（先读 :1-:120 定义面 + :523 接口件，
        以本件 AUQTZYZ 为输入件）。
-/

import Kepler.Text.TameSpine.TameList63

/-! # AUQTZYZ 章收章：is_normal 双件族拼装 + 商 dih2k（AUQTZYZ.hl :1851-:2624） -/

namespace Kepler.Text.TameSpine

variable {α : Type*} [DecidableEq α]

/-! ### §0 本地私桥（本章小桥） -/

/- 置换幂的函数迭代形（`⇑(f ^ n) x = ⇑f^[n] x`；商 hypermap 三映射是
`Equiv.Perm (Set α)`，消费 TameList61 CARD_ITER_K_EK_IMP_DIST_FUNTION
（`f : α → α`、`f^[n]` 形）时的一词桥）。 -/
omit [DecidableEq α] in
private theorem permPowIterate (f : Equiv.Perm α) :
    ∀ (n : ℕ) (x : α), (f ^ n) x = f^[n] x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ', Function.comp_apply,
      ih x]

/-- `complementPt H x 0 = nodeMap x`（complementAux 首行 `(nodeMap.symm ^ 0)
(nodeMap x)` 的定义性化简；is_normal 合取①的 L 支 dart 证人）。 -/
private theorem complementPt_zero (H : Hypermap α) (x : α) :
    H.complementPt x 0 = H.nodeMap x := rfl

/-- `edgeMap = nodeMap ∘ faceMap` 的点态形（plain_iff_edgeMap_eq 的应用面；
AUQTZYZ.hl :2300 REWRITE[is_restricted; edge_map_convolution] 同面）。 -/
private theorem edgeMap_apply (H : Hypermap α) (hp : H.Plain) (w : α) :
    H.edgeMap w = H.nodeMap (H.faceMap w) := by
  rw [H.plain_iff_edgeMap_eq.1 hp]
  rfl

/-- plain 的 edgeMap 对合点态形（`edge (edge w) = w`；批 63 §0' 同型件）。 -/
private theorem edgeMap_involute_apply (H : Hypermap α) (hp : H.Plain) (w : α) :
    H.edgeMap (H.edgeMap w) = w := by
  have hh := congrArg (fun q : Equiv.Perm α => q w) hp
  simpa using hh

/-! ### §1 AUQTZYZ：is_normal {loop_of_face x, L} 双件族拼装 +
商 hypermap dih2k（AUQTZYZ.hl :1859-:2613 主证明）

语句（AUQTZYZ_concl :1851-:1858）：受限 H、x ∈ dart、L1 = loop_of_face x
⟹ ∃L2，is_normal {L1,L2} ∧ path_of_loop L2 (complement x 0) = complement x
∧ dih2k (quotient {L1,L2}) (CARD (face x))。L2 := EXISTS_PATH_COMPLEMENT
的补环 L（:1864 MRESAL 同面化直投）。

Lean 依存类型承载：`quotient H {L1,L2}` 需 is_normal 证据作显式参
（`quotientHypermap hnf`），故正规族证明以 ∃ 组件携带（与 HOL 的
∧-合取逐字同形，差异仅编码面）。

dih2k 五件中四件半无条件闭合（card = 2k、面轨道覆盖、face_map k 阶、
node_map 2 阶、edge_map ≠ 1）；edge_map 对合半部的 B 支依赖一个点等式
（v ∈ face x 处 `nodeMap (faceMap (headOfAtom NF (nodeMap (faceMap v))))
= v`，NF = {loop_of_face x, L}），本批未闭合——以蕴含前件显式入语句，
批 65 精确接续（证明路径设计见头注批 65 段）。 -/

theorem AUQTZYZ (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) :
    ∃ (L2 : Loop α) (hnf : H.IsNormalFamily {H.loopOfFace x, L2}),
      L2.pathOf (H.complementPt x 0) = H.complementPt x ∧
      ((∀ v ∈ H.face x,
          H.nodeMap (H.faceMap
            (H.headOfAtom {H.loopOfFace x, L2} (H.nodeMap (H.faceMap v)))) = v) →
        Dih2k (H.quotientHypermap hnf) (H.face x).ncard) := by
  -- EXISTS_PATH_COMPLEMENT 十二合取消费（HOL :1864 MRESAL 直投）
  obtain ⟨L, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8, hL9, hL10, hL11, hL12⟩ :=
    EXISTS_PATH_COMPLEMENT H hr hx
  set NF : Set (Loop α) := {H.loopOfFace x, L} with hNFdef
  have hmL : L ∈ NF := Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
  have hmlOF : H.loopOfFace x ∈ NF := Set.mem_insert_iff.mpr (Or.inl rfl)
  have hldOF : ↑(H.loopOfFace x).darts = H.face x := H.loopOfFace_darts x
  /- §1.1 正规族四合取（AUQTZYZ.hl :1870-:1985） -/
  have hnf : H.IsNormalFamily NF := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- ① 每件是 loop 且有 dart 证人
      rintro L' hL'
      rcases Set.mem_insert_iff.mp hL' with hE | hE
      · subst hE
        refine ⟨H.loopOfFace_isLoop x, x, hx, (H.mem_faceFinset x x).mpr (H.mem_face_self x)⟩
      · have hE2 : L = L' := (Set.mem_singleton_iff.mp hE).symm
        subst hE2
        refine ⟨hL1, H.nodeMap x, ?_, ?_⟩
        · rw [← complementPt_zero]
          exact H.nodeMap_permutes.apply_mem hx
        · rw [← complementPt_zero]
          exact hL3
    · -- ② 每件有异 node 双点（face 环支：x 与 faceMap x，simple 塌缩 + 面轨道 ≥ 3）
      rintro L' hL'
      rcases Set.mem_insert_iff.mp hL' with hE | hE
      · subst hE
        refine ⟨x, (H.mem_faceFinset x x).mpr (H.mem_face_self x), H.faceMap x,
          (H.mem_faceFinset x (H.faceMap x)).mpr ?_, ?_⟩
        · have h1 := H.pow_faceMap_mem_face x 1
          rwa [pow_one] at h1
        · intro hcon
          have hnex : H.node (H.faceMap x) = H.node x :=
            H.node_eq_of_mem (hcon ▸ H.mem_node_self x)
          have hfmF : H.faceMap x ∈ H.face x := by
            have h1 := H.pow_faceMap_mem_face x 1
            rwa [pow_one] at h1
          have hfmN : H.faceMap x ∈ H.node x := by
            have h1 : H.faceMap x ∈ H.node (H.faceMap x) := H.mem_node_self _
            rw [hnex] at h1
            exact h1
          have hmem2 : H.faceMap x ∈ H.node x ∩ H.face x := ⟨hfmN, hfmF⟩
          rw [hr.simple x hx] at hmem2
          have hfix : H.faceMap x = x := Set.mem_singleton_iff.mp hmem2
          have hcf1 : H.face x = {x} := (orbitMap_singleton_iff H.faceMap x).mpr hfix
          have h3 := hr.three_le_ncard_face hx
          rw [hcf1] at h3
          simp at h3
      · have hE2 : L = L' := (Set.mem_singleton_iff.mp hE).symm
        subst hE2
        obtain ⟨y, z, hy, hz, hne⟩ := hL4
        exact ⟨y, hy, z, hz, hne⟩
    · -- ③ 共享 dart 即同件（L 与 face 环经合取⑤不交面判定）
      rintro L' hL' L'' hL'' w hw hw'
      rcases Set.mem_insert_iff.mp hL' with hE | hE
      · subst hE
        rcases Set.mem_insert_iff.mp hL'' with hE2 | hE2
        · subst hE2
          rfl
        · have hE3 : L = L'' := (Set.mem_singleton_iff.mp hE2).symm
          subst hE3
          have hwF : w ∈ H.face x := (H.mem_faceFinset x w).mp hw
          exact absurd (Set.mem_inter (Finset.mem_coe.mpr hw') hwF)
            (Set.eq_empty_iff_forall_notMem.mp hL5 w)
      · have hE1 : L = L' := (Set.mem_singleton_iff.mp hE).symm
        subst hE1
        rcases Set.mem_insert_iff.mp hL'' with hE2 | hE2
        · subst hE2
          have hwF : w ∈ H.face x := (H.mem_faceFinset x w).mp hw'
          exact absurd (Set.mem_inter (Finset.mem_coe.mpr hw) hwF)
            (Set.eq_empty_iff_forall_notMem.mp hL5 w)
        · have hE3 : L'' = L := Set.mem_singleton_iff.mp hE2
          subst hE3
          rfl
    · -- ④ 闭包：node 像落族内（消费合取⑥⑦ + loop_of_face dart 面）
      rintro L' hL' a b ha hb
      rcases Set.mem_insert_iff.mp hL' with hE | hE
      · subst hE
        have haF : a ∈ H.face x := (H.mem_faceFinset x a).mp ha
        rcases hL7 a haF b hb with hbL | hbF
        · exact ⟨L, hmL, hbL⟩
        · exact ⟨H.loopOfFace x, hmlOF, (H.mem_faceFinset x b).mpr hbF⟩
      · have hE2 : L = L' := (Set.mem_singleton_iff.mp hE).symm
        subst hE2
        rcases hL6 a ha b hb with hbL | hbF
        · exact ⟨L, hmL, hbL⟩
        · exact ⟨H.loopOfFace x, hmlOF, (H.mem_faceFinset x b).mpr hbF⟩
  /- §1.2 商基础件：原子族并/不交/卡（AUQTZYZ.hl :1990-:2043） -/
  have hAB : H.atomsOfFamily NF
      = H.atomsOfLoop L ∪ H.atomsOfLoop (H.loopOfFace x) := by
    ext a
    simp only [Hypermap.atomsOfFamily, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨L', hL', w, hw, rfl⟩
      rcases Set.mem_insert_iff.mp hL' with rfl | rfl
      · exact Or.inr ⟨w, hw, rfl⟩
      · exact Or.inl ⟨w, hw, rfl⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
      · exact ⟨L, hmL, w, hw, rfl⟩
      · exact ⟨H.loopOfFace x, hmlOF, w, hw, rfl⟩
  have hABdisj : H.atomsOfLoop L ∩ H.atomsOfLoop (H.loopOfFace x) = ∅ := by
    rw [← atomsOfLoopRep] at hL9
    exact hL9
  have hcardB : (H.atomsOfLoop (H.loopOfFace x)).ncard = (H.face x).ncard := by
    rw [atomsOfLoopRep]
    exact cardAtomLoopOfFace H hr hx
  have hfinA : (H.atomsOfLoop L).Finite := by
    rw [atomsOfLoopRep]
    exact FINITE_ATOM_LOOP H L
  have hfinB : (H.atomsOfLoop (H.loopOfFace x)).Finite := by
    rw [atomsOfLoopRep]
    exact FINITE_ATOM_LOOP H (H.loopOfFace x)
  -- 商 hypermap 基础件：dart（coe）= 原子族，三映射 = 商映射（定义面）
  have hQspec := H.quotientHypermap_spec hnf
  have hQn : (H.quotientHypermap hnf).nodeMap = H.nQuotientPerm hnf := rfl
  have hQe : (H.quotientHypermap hnf).edgeMap
      = (H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹ := rfl
  have hfaceA : ∀ u ∈ L.darts,
      orbitMap (H.quotientHypermap hnf).faceMap (H.atom L u)
        = H.atomsOfLoop L := fun u hu => H.face_quotient_atom hnf hmL hu
  have hfaceB : ∀ v ∈ (H.loopOfFace x).darts,
      orbitMap (H.quotientHypermap hnf).faceMap (H.atom (H.loopOfFace x) v)
        = H.atomsOfLoop (H.loopOfFace x) := fun v hv =>
    H.face_quotient_atom hnf hmlOF hv
  /- §1.3 尾桥与商 node 交换件（⑩⑪桥 + tail 理论；
  AUQTZYZ.hl :2071-:2115 的去指标重构） -/
  have htailBridge : ∀ w ∈ L.darts, H.nodeMap (H.tailOfAtom NF w) ∈ H.face x := by
    intro w hw
    obtain ⟨y', hy'1, hy'2, hy'3, -⟩ := hL10 w hw
    have hy'L : y' ∈ L.darts := H.mem_darts_of_mem_atom hw hy'1
    have hty' : H.tailOfAtom NF y' = y' :=
      (H.tailOfAtom_eq_self_iff hr hnf hmL hy'L).mpr hy'2
    have hcongr := (H.headTailOfAtom_congr hnf hmL hw hy'1).2
    rw [← hcongr, hty']
    exact hy'3
  have hswapA : ∀ u ∈ L.darts,
      H.nQuotient NF (H.atom L u)
        = H.atom (H.loopOfFace x) (H.nodeMap (H.tailOfAtom NF u)) := by
    intro u hu
    exact H.nQuotient_atom hnf hmL hmlOF hu
      ((H.mem_faceFinset x _).mpr (htailBridge u hu))
  -- 面点自尾（lemmaAtomTail + tailOfAtom_eq_self_iff；hswapB 的内联前置）
  have htvFace : ∀ v ∈ H.face x, H.tailOfAtom NF v = v := by
    intro v hv
    exact (H.tailOfAtom_eq_self_iff hr hnf hmlOF
      ((H.mem_faceFinset x v).mpr hv)).mpr (lemmaAtomTail H x v hv)
  have hswapA : ∀ u ∈ L.darts, (H.quotientHypermap hnf).nodeMap (H.atom L u)
      = H.atom (H.loopOfFace x) (H.nodeMap (H.tailOfAtom NF u)) := by
    intro u hu
    exact H.nQuotient_atom hnf hmL hmlOF hu
      ((H.mem_faceFinset x _).mpr (htailBridge u hu))
  have hswapB : ∀ v ∈ (H.loopOfFace x).darts,
      (H.quotientHypermap hnf).nodeMap (H.atom (H.loopOfFace x) v)
        = H.atom L (H.nodeMap v) := by
    intro v hv
    have hv' : v ∈ H.face x := by rw [← hldOF]; exact Finset.mem_coe.mpr hv
    have hstep := H.nQuotient_atom hnf hmlOF hmL hv
      (by rw [htvFace v hv']; exact hL12 v hv')
    rw [htvFace v hv'] at hstep
    exact hstep
  refine ⟨L, hnf, hL2, ?_⟩
  intro hedge
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ① CARD：dart (quotient) = 原子族 = A ⊔ B，卡 k + k（:1994-:2043）
    have hncardU : (H.atomsOfFamily NF).ncard
        = (H.atomsOfLoop L).ncard + (H.atomsOfLoop (H.loopOfFace x)).ncard := by
      rw [hAB]
      exact Set.ncard_union_eq (Set.disjoint_iff_inter_eq_empty.mpr hABdisj) hfinA hfinB
    have hdartF : (H.atomsOfFamily NF).Finite := H.atomsOfFamily_finite hnf
    have h1 : (H.quotientHypermap hnf).darts.card = (H.atomsOfFamily NF).ncard := by
      rw [← Set.ncard_coe_finset, ← hQspec.1]
    rw [h1, hncardU, hL8, hcardB]
    omega
  · -- ② 覆盖：每 dart 的面轨道 ∪ node 像面轨道 = 全 dart（:2047-:2215）
    intro d hd
    have hdFam : d ∈ H.atomsOfFamily NF := by
      rw [← hQspec.1]
      exact Finset.mem_coe.mp hd
    have hdAB : d ∈ H.atomsOfLoop L ∪ H.atomsOfLoop (H.loopOfFace x) := by
      rw [← hAB]; exact hdFam
    have orbitSub : ∀ w ∈ orbitMap (H.quotientHypermap hnf).faceMap d,
        w ∈ H.atomsOfFamily NF := by
      intro w hw
      rcases hdAB with (⟨u, hu, hdu⟩ | ⟨v₀, hv₀, hdv₀⟩)
      · rw [hdu, hfaceA u hu] at hw
        obtain ⟨w', hw', hw'eq⟩ := hw
        exact ⟨L, hmL, w', hw', hw'eq⟩
      · rw [hdv₀, hfaceB v₀ hv₀] at hw
        obtain ⟨w', hw', hw'eq⟩ := hw
        exact ⟨H.loopOfFace x, hmlOF, w', hw', hw'eq⟩
    ext y
    constructor
    · rintro (hy | ⟨z, hzorb, hyz⟩)
      · rw [hQspec.1]
        exact orbitSub y hy
      · -- 商 node 置换保持原子族（置换补集固定 + 单射，替代 HOL :2071-:2115 入支）
        have hQPFam : ∀ s ∈ H.atomsOfFamily NF, H.nQuotientPerm hnf s ∈ H.atomsOfFamily NF := by
          intro s hs
          by_contra hcon
          have hfix : H.nQuotientPerm hnf (H.nQuotientPerm hnf s)
              = H.nQuotientPerm hnf s := (H.nQuotient_permutes hnf).1 _ hcon
          have h2 : H.nQuotientPerm hnf s = s := (H.nQuotientPerm hnf).injective hfix
          exact hcon (by rw [h2]; exact hs)
        rw [← hyz, hQspec.1]
        exact hQPFam z (orbitSub z hzorb)
    · rintro hy
      have hyFam : y ∈ H.atomsOfFamily NF := by
        rw [← hQspec.1]; exact hy
      rcases hdAB with (⟨d₀, hd₀, hdd₀⟩ | ⟨d₁, hd₁, hdd₁⟩)
      · rcases (by rw [← hAB]; exact hyFam :
            y ∈ H.atomsOfLoop L ∪ H.atomsOfLoop (H.loopOfFace x)) with
          (⟨u, hu, hyu⟩ | ⟨v, hv, hyv⟩)
        · -- y ∈ A，d ∈ A：y 在面轨道内（= A）
          rw [hyu]
          simp only [Set.mem_union]
          refine Or.inl ?_
          rw [hdd₀, hfaceA d₀ hd₀]
          exact ⟨u, hu, rfl⟩
        · -- y ∈ B 支：⑪ 桥造 A 侧原像（:2071-:2096 重构；轨道 = A）
          rw [hyv]
          simp only [Set.mem_union]
          refine Or.inr ?_
          obtain ⟨w, hw₁, hw₂, hw₃, hw₄⟩ := hL11 v
            (by rw [← hldOF]; exact Finset.mem_coe.mpr hv)
          have hwL : w ∈ L.darts := H.mem_darts_of_mem_atom hw₄ hw₁
          have htw : H.tailOfAtom NF w = w :=
            (H.tailOfAtom_eq_self_iff hr hnf hmL hwL).mpr hw₂
          have hcongr := (H.headTailOfAtom_congr hnf hmL hw₄ hw₁).2
          refine ⟨H.atom L (H.nodeMap.symm v), ?_, ?_⟩
          · rw [hdd₀, hfaceA d₀ hd₀]
            exact ⟨H.nodeMap.symm v, hw₄, rfl⟩
          · rw [hswapA (H.nodeMap.symm v) hw₄, ← hcongr, htw, hw₃]
      · rcases (by rw [← hAB]; exact hyFam :
            y ∈ H.atomsOfLoop L ∪ H.atomsOfLoop (H.loopOfFace x)) with
          (⟨u, hu, hyu⟩ | ⟨v, hv, hyv⟩)
        · -- y ∈ A 支：⑩ 桥造 B 侧原像（:2120-:2179 重构；轨道 = B）
          rw [hyu]
          simp only [Set.mem_union]
          refine Or.inr ?_
          obtain ⟨y', hy'1, hy'2, hy'3, hy'4⟩ := hL10 u hu
          refine ⟨H.atom (H.loopOfFace x) (H.nodeMap y'), ?_, ?_⟩
          · rw [hdd₁, hfaceB d₁ hd₁]
            exact ⟨H.nodeMap y', (H.mem_faceFinset x _).mpr hy'3, rfl⟩
          · rw [hswapB (H.nodeMap y') ((H.mem_faceFinset x _).mpr hy'3)]
            exact (H.atom_eq_of_mem hy'4).symm
        · -- y ∈ B，d ∈ B：y 在面轨道内（= B）
          rw [hyv]
          simp only [Set.mem_union]
          refine Or.inl ?_
          rw [hdd₁, hfaceB d₁ hd₁]
          exact ⟨v, hv, rfl⟩
  · -- ③ face_map k 阶（:2185-:2258）
    refine ⟨?_, ?_⟩
    · -- 非平凡半部：面轨道满基数 ⟹ 幂非恒等（CARD_ITER 一发）
      intro i hi0 hik heq
      have hk0 : (H.face x).ncard ≠ 0 := by omega
      have hncardorb : (orbitMap (H.quotientHypermap hnf).faceMap
            (H.atom (H.loopOfFace x) x)).ncard = (H.face x).ncard := by
        rw [hfaceB x ((H.mem_faceFinset x x).mpr (H.mem_face_self x)), hcardB]
      have hcyc := (H.quotientHypermap hnf).faceMap_permutes.pow_ncard_orbitMap_apply_self
        (H.atom (H.loopOfFace x) x)
      rw [hncardorb] at hcyc
      have horb := orbit_cyclic (H.quotientHypermap hnf).faceMap hk0 hcyc
      have hsetcard : {y | ∃ n, n < (H.face x).ncard ∧
          y = (fun s : Set α => (H.quotientHypermap hnf).faceMap s)^[n]
            (H.atom (H.loopOfFace x) x)}.ncard = (H.face x).ncard := by
        have hsetEq : {y | ∃ n, n < (H.face x).ncard ∧
            y = (fun s : Set α => (H.quotientHypermap hnf).faceMap s)^[n]
              (H.atom (H.loopOfFace x) x)}
            = orbitMap (H.quotientHypermap hnf).faceMap
              (H.atom (H.loopOfFace x) x) := by
          rw [horb]
          ext y
          simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Finset.mem_range,
            permPowIterate]
          constructor
          · rintro ⟨n, hn, hyn⟩; exact ⟨n, hn, hyn.symm⟩
          · rintro ⟨n, hn, hyn⟩; exact ⟨n, hn, hyn.symm⟩
        rw [hsetEq, hncardorb]
      have hiter := CARD_ITER_K_EK_IMP_DIST_FUNTION
        (f := fun s : Set α => (H.quotientHypermap hnf).faceMap s)
        (x := H.atom (H.loopOfFace x) x) hsetcard i hi0 hik
      refine hiter ?_
      funext w
      show (H.quotientHypermap hnf).faceMap^[i] w = w
      rw [← permPowIterate]
      simpa using congrArg (fun q : Equiv.Perm (Set α) => q w) heq
    · -- 恒等半部：A/B 各取一个族点作轨道代表，幂 k 回环（:2199-:2258）
      refine Equiv.Perm.ext fun y => ?_
      by_cases hyd : y ∈ (H.quotientHypermap hnf).darts
      · have hyFam : y ∈ H.atomsOfFamily NF := by
          rw [← hQspec.1]; exact Finset.mem_coe.mp hyd
        rcases (by rw [← hAB]; exact hyFam :
            y ∈ H.atomsOfLoop L ∪ H.atomsOfLoop (H.loopOfFace x)) with
          (⟨u, hu, hyu⟩ | ⟨v, hv, hyv⟩)
        · rw [hyu]
          -- A 代表：atom L (complement x 0)（hL3 即其族点资格）
          have hncard : (orbitMap (H.quotientHypermap hnf).faceMap
                (H.atom L (H.complementPt x 0))).ncard = (H.face x).ncard := by
            rw [hfaceA _ hL3, hL8]
          have hcyc := (H.quotientHypermap hnf).faceMap_permutes.pow_ncard_orbitMap_apply_self
            (H.atom L (H.complementPt x 0))
          rw [hncard] at hcyc
          have hymem : y ∈ orbitMap (H.quotientHypermap hnf).faceMap
              (H.atom L (H.complementPt x 0)) := by
            rw [hfaceA _ hL3]
            exact ⟨u, hu, hyu⟩
          obtain ⟨j, -, hyj⟩ :=
            (H.quotientHypermap hnf).faceMap_permutes.exists_lt_ncard_pow_apply hymem
          have hyy : H.atom L u = ((H.quotientHypermap hnf).faceMap ^ j)
              (H.atom L (H.complementPt x 0)) := hyu.symm.trans hyj
          rw [hyy, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm, pow_add,
            Equiv.Perm.mul_apply, hcyc]
          rfl
        · rw [hyv]
          -- B 代表：atom (loop_of_face x) x
          have hncard : (orbitMap (H.quotientHypermap hnf).faceMap
                (H.atom (H.loopOfFace x) x)).ncard = (H.face x).ncard := by
            rw [hfaceB x ((H.mem_faceFinset x x).mpr (H.mem_face_self x)), hcardB]
          have hcyc := (H.quotientHypermap hnf).faceMap_permutes.pow_ncard_orbitMap_apply_self
            (H.atom (H.loopOfFace x) x)
          rw [hncard] at hcyc
          have hymem : y ∈ orbitMap (H.quotientHypermap hnf).faceMap
              (H.atom (H.loopOfFace x) x) := by
            rw [hfaceB x ((H.mem_faceFinset x x).mpr (H.mem_face_self x))]
            exact ⟨v, hv, hyv⟩
          obtain ⟨j, -, hyj⟩ :=
            (H.quotientHypermap hnf).faceMap_permutes.exists_lt_ncard_pow_apply hymem
          have hyy : H.atom (H.loopOfFace x) v
              = ((H.quotientHypermap hnf).faceMap ^ j)
              (H.atom (H.loopOfFace x) x) := hyv.symm.trans hyj
          rw [hyy, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm, pow_add,
            Equiv.Perm.mul_apply, hcyc]
          rfl
      · exact Hypermap.PermutesOn.pow_apply_eq_self_of_not_mem
          (H.quotientHypermap hnf).faceMap_permutes
          (fun hh => hyd (Finset.mem_coe.mpr hh)) _
  · -- ④ edge_map 2 阶（:2261-:2455；对合半部 B 支见批 65 接续点）
    refine ⟨?_, ?_⟩
    · -- 非平凡半部：证人 atom (loop_of_face x) x 被 edge_map 换入 A（:2284-:2334）
      intro i hi0 hik heq
      have hi1 : i = 1 := by omega
      subst hi1
      rw [pow_one] at heq
      have hvx : H.faceMap x ∈ H.face x := by
        have h1 := H.pow_faceMap_mem_face x 1
        rwa [pow_one] at h1
      have hxd : x ∈ (H.loopOfFace x).darts :=
        (H.mem_faceFinset x x).mpr (H.mem_face_self x)
      have hhead : H.headOfAtom NF x = x := by
        rw [H.headOfAtom_eq_self_iff hr hnf hmlOF hxd]
        have h := H.loopOfFace_map_pow_apply (H.mem_face_self x) 1
        rwa [pow_one, pow_one] at h
      have hchoice : H.atomChoice NF x = H.atom (H.loopOfFace x) x :=
        H.atomChoice_eq_atom hnf hmlOF hxd
      have hstep := H.eQuotientPerm_via_atomChoice hnf
        (show x ∈ Hypermap.dartsOfFamily NF from ⟨H.loopOfFace x, hmlOF, hxd⟩)
      rw [hchoice, hhead, edgeMap_apply H hr.plain] at hstep
      -- hstep.2.2 : edge 商换子 = atom L (nodeMap (faceMap x))
      have h1 : ((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹)
            (H.atom (H.loopOfFace x) x) = H.atom L (H.nodeMap (H.faceMap x)) := by
        rw [hstep.2.2, H.atomChoice_eq_atom hnf hmL (hL12 (H.faceMap x) hvx)]
      have h2 : ((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹)
            (H.atom (H.loopOfFace x) x) = H.atom (H.loopOfFace x) x :=
        congrArg (fun q : Equiv.Perm (Set α) => q (H.atom (H.loopOfFace x) x)) heq
      have hBA : H.atom L (H.nodeMap (H.faceMap x))
          = H.atom (H.loopOfFace x) x := h1 ▸ h2
      have hmemA : H.atom L (H.nodeMap (H.faceMap x)) ∈ H.atomsOfLoop L :=
        ⟨H.nodeMap (H.faceMap x), hL12 (H.faceMap x) hvx, rfl⟩
      have hmemB : H.atom L (H.nodeMap (H.faceMap x))
          ∈ H.atomsOfLoop (H.loopOfFace x) := by
        rw [hBA]
        exact ⟨x, (H.mem_faceFinset x x).mpr (H.mem_face_self x), rfl⟩
      exact Set.eq_empty_iff_forall_notMem.mp hABdisj _ ⟨hmemA, hmemB⟩
    · -- 对合半部：A 支全闭；B 支精确依赖 edge 恒等式（前件 hedge，:2338-:2450）
      refine Equiv.Perm.ext fun y => ?_
      show ((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹)
        (((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹) y) = y
      by_cases hyFam : y ∈ H.atomsOfFamily NF
      · rcases (by rw [← hAB]; exact hyFam :
            y ∈ H.atomsOfLoop L ∪ H.atomsOfLoop (H.loopOfFace x)) with
          (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩)
        · -- A 支：两发 eQuotient 求值 + plain 平方回环（:2348-:2393 重构）
          show ((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹)
            (((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹) (H.atom L u))
            = H.atom L u
          have huFam : u ∈ Hypermap.dartsOfFamily NF := ⟨L, hmL, hu⟩
          have huChoice : H.atomChoice NF u = H.atom L u :=
            H.atomChoice_eq_atom hnf hmL hu
          have hstep1 := H.eQuotientPerm_via_atomChoice hnf huFam
          rw [huChoice] at hstep1
          -- h := head_of_atom NF u；F h ∈ L.darts（面像离面即回 L）；z := edge H h ∈ 面内
          have hhL : H.headOfAtom NF u ∈ L.darts :=
            (H.headTailOfAtom_mem_darts hnf hmL hu).1
          have hhnotF : H.headOfAtom NF u ∉ H.face x := by
            intro hhc
            have hh : H.headOfAtom NF u ∈ ↑L.darts ∩ H.face x :=
              Set.mem_inter hhL hhc
            exact Set.eq_empty_iff_forall_notMem.mp hL5 _ hh
          have hFL : H.faceMap (H.headOfAtom NF u) ∈ L.darts := by
            obtain ⟨L', hL', hFL'⟩ := (H.fQuotient_via_atomChoice hnf huFam).1
            rcases Set.mem_insert_iff.mp hL' with hE | hE
            · have hE2 : L' = H.loopOfFace x := hE
              subst hE2
              exfalso
              apply hhnotF
              -- F h ∈ face x ⟹ h ∈ face x（faceMap 轨道的对称回传）
              have hFx : H.faceMap (H.headOfAtom NF u) ∈ H.face x := by
                rw [← hldOF]; exact hFL'
              show H.headOfAtom NF u ∈ orbitMap H.faceMap x
              have e1 : orbitMap H.faceMap (H.faceMap (H.headOfAtom NF u))
                  = orbitMap H.faceMap x :=
                orbitMap_eq_of_mem H.faceMap_permutes hFx
              have hmem : H.headOfAtom NF u
                  ∈ orbitMap H.faceMap (H.faceMap (H.headOfAtom NF u)) := by
                have h2 := PermutesOn.symm_apply_mem_orbitMap H.faceMap_permutes
                  (H.faceMap (H.headOfAtom NF u))
                rwa [Equiv.symm_apply_apply] at h2
              exact (e1 ▸ hmem : H.headOfAtom NF u ∈ orbitMap H.faceMap x)
            · have hE2 : L' = L := Set.mem_singleton_iff.mp hE
              subst hE2
              exact hFL'
          have hz : H.edgeMap (H.headOfAtom NF u) ∈ H.face x := by
            have hpiece := H.fQuotient_via_atomChoice hnf huFam
            have hzEq : H.edgeMap (H.headOfAtom NF u)
                = H.nodeMap (H.tailOfAtom NF (H.faceMap (H.headOfAtom NF u))) := by
              rw [edgeMap_apply H hr.plain]
              conv_lhs => rw [hpiece.2.1]
            rw [hzEq]
            exact htailBridge _ hFL
          have hzLd : H.edgeMap (H.headOfAtom NF u) ∈ (H.loopOfFace x).darts :=
            (H.mem_faceFinset x _).mpr hz
          -- 第一发：E (atom L u) = atom (loop_of_face x) z
          have hstep1' : ((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹) (H.atom L u)
              = H.atom (H.loopOfFace x) (H.edgeMap (H.headOfAtom NF u)) := by
            rw [hstep1.2.2, H.atomChoice_eq_atom hnf hmlOF hzLd]
          -- 第二发：z 自头，edge² 弹回首点 h，h 的 atom 即 u 的 atom
          have hzFam : H.edgeMap (H.headOfAtom NF u) ∈ Hypermap.dartsOfFamily NF :=
            ⟨H.loopOfFace x, hmlOF, (H.mem_faceFinset x _).mpr hz⟩
          have hstep2 := H.eQuotientPerm_via_atomChoice hnf hzFam
          rw [H.atomChoice_eq_atom hnf hmlOF hzLd] at hstep2
          have hzHead : H.headOfAtom NF (H.edgeMap (H.headOfAtom NF u))
              = H.edgeMap (H.headOfAtom NF u) := by
            rw [H.headOfAtom_eq_self_iff hr hnf hmlOF hzLd]
            have h := H.loopOfFace_map_pow_apply hz 1
            simpa using h
          have hEE : H.edgeMap (H.edgeMap (H.headOfAtom NF u))
              = H.headOfAtom NF u := edgeMap_involute_apply H hr.plain _
          have hhAtom : H.headOfAtom NF u ∈ H.atom L u :=
            (H.headOfAtom_mem_atom hnf hmL hu).1
          rw [hstep1', hstep2.2.2, hzHead, hEE,
            H.atomChoice_eq_atom hnf hmL hhL]
          exact (H.atom_eq_of_mem hhAtom).symm
        · -- B 支：依赖 edge 恒等式（前件 hedge；:2400-:2450 缺口所在）
          show ((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹)
            (((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹)
              (H.atom (H.loopOfFace x) v)) = H.atom (H.loopOfFace x) v
          have hvChoice : H.atomChoice NF v = H.atom (H.loopOfFace x) v :=
            H.atomChoice_eq_atom hnf hmlOF hv
          have hvHead : H.headOfAtom NF v = v := by
            rw [H.headOfAtom_eq_self_iff hr hnf hmlOF hv]
            have h := H.loopOfFace_map_pow_apply
              (by rw [← hldOF]; exact Finset.mem_coe.mpr hv) 1
            rw [pow_one, pow_one] at h
            exact h
          have hvF : H.faceMap v ∈ H.face x := by
            have h1 := H.pow_faceMap_mem_face v 1
            rw [pow_one] at h1
            have hfe : H.face x = H.face v :=
              H.face_eq_of_mem (by rw [← hldOF]; exact Finset.mem_coe.mpr hv)
            rw [hfe]
            exact h1
          have hstep1 := H.eQuotientPerm_via_atomChoice hnf
            (show v ∈ Hypermap.dartsOfFamily NF from ⟨H.loopOfFace x, hmlOF, hv⟩)
          rw [hvChoice, hvHead, edgeMap_apply H hr.plain] at hstep1
          have hstep1' : ((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹)
                (H.atom (H.loopOfFace x) v) = H.atom L (H.nodeMap (H.faceMap v)) := by
            rw [hstep1.2.2, H.atomChoice_eq_atom hnf hmL (hL12 (H.faceMap v) hvF)]
          have hwL : H.nodeMap (H.faceMap v) ∈ L.darts := hL12 (H.faceMap v) hvF
          have hstep2 := H.eQuotientPerm_via_atomChoice hnf (⟨L, hmL, hwL⟩ :
            H.nodeMap (H.faceMap v) ∈ Hypermap.dartsOfFamily NF)
          rw [H.atomChoice_eq_atom hnf hmL hwL] at hstep2
          have hpt : H.edgeMap (H.headOfAtom NF (H.nodeMap (H.faceMap v))) = v := by
            rw [edgeMap_apply H hr.plain,
              hedge v (by rw [← hldOF]; exact Finset.mem_coe.mpr hv)]
          rw [hstep1', hstep2.2.2, hpt, hvChoice]
      · -- 族外点：商 edge = fQ⁻¹∘nQ⁻¹ 双固定（quotientPerm_inv_apply）
        show ((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹)
          (((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹) y) = y
        have hinv := H.quotientPerm_inv_apply hnf hyFam
        have hP : ((H.fQuotientPerm hnf)⁻¹ * (H.nQuotientPerm hnf)⁻¹) y = y := by
          rw [Equiv.Perm.mul_apply, hinv.2, hinv.1]
        rw [hP, hP]

  · -- ⑤ node_map 2 阶（:2264 后 node 段重构）
    refine ⟨?_, ?_⟩
    · -- 非平凡半部：证人 atom (loop_of_face x) x 被 node_map 换入 A
      intro i hi0 hik heq
      have hi1 : i = 1 := by omega
      subst hi1
      rw [pow_one] at heq
      have hmove := hswapB x ((H.mem_faceFinset x x).mpr (H.mem_face_self x))
      have h1 : (H.quotientHypermap hnf).nodeMap (H.atom (H.loopOfFace x) x)
          = H.atom (H.loopOfFace x) x := by
        rw [(heq : (H.quotientHypermap hnf).nodeMap
          = (1 : Equiv.Perm (Set α)))]
        rfl
      rw [hmove] at h1
      -- h1 : atom L (nodeMap x) = atom (loop_of_face x) x
      have hmemA : H.atom L (H.nodeMap x) ∈ H.atomsOfLoop L :=
        ⟨H.nodeMap x, hL12 x (H.mem_face_self x), rfl⟩
      have hmemB : H.atom L (H.nodeMap x) ∈ H.atomsOfLoop (H.loopOfFace x) := by
        rw [h1]
        exact ⟨x, (H.mem_faceFinset x x).mpr (H.mem_face_self x), rfl⟩
      exact Set.eq_empty_iff_forall_notMem.mp hABdisj _ ⟨hmemA, hmemB⟩
    · -- 对合半部：A 支走 ⑩ 尾桥识别，B 支走 simple 单点钉点（:2457-:2607）
      refine Equiv.Perm.ext fun y => ?_
      show (H.quotientHypermap hnf).nodeMap ((H.quotientHypermap hnf).nodeMap y) = y
      by_cases hyFam : y ∈ H.atomsOfFamily NF
      · rcases (by rw [← hAB]; exact hyFam :
            y ∈ H.atomsOfLoop L ∪ H.atomsOfLoop (H.loopOfFace x)) with
          (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩)
        · -- A 支：⑩ 桥即尾（tail_eq_self_iff + change_parameters），N² 尾像回原子
          have hstep1 := hswapA u hu
          have hstep2 := hswapB (H.nodeMap (H.tailOfAtom NF u))
            ((H.mem_faceFinset x _).mpr (htailBridge u hu))
          obtain ⟨y', hy'1, hy'2, -, hy'4⟩ := hL10 u hu
          have hy'L : y' ∈ L.darts := H.mem_darts_of_mem_atom hu hy'1
          have hty' : H.tailOfAtom NF y' = y' :=
            (H.tailOfAtom_eq_self_iff hr hnf hmL hy'L).mpr hy'2
          have hcongr := (H.headTailOfAtom_congr hnf hmL hu hy'1).2
          have htu : H.tailOfAtom NF u = y' := hcongr ▸ hty'
          rw [hstep1, hstep2, htu]
          exact (H.atom_eq_of_mem hy'4).symm
        · -- B 支：q := N (tail (N v))，simple 单点钉 q = v（:2533-:2607 重构）
          have hwL : H.nodeMap v ∈ L.darts :=
            hL12 v (by rw [← hldOF]; exact Finset.mem_coe.mpr hv)
          have hstep1 := hswapB v hv
          have hstep2 := hswapA (H.nodeMap v) hwL
          have hvdart : v ∈ H.darts := H.face_subset_darts hx
            (by rw [← hldOF]; exact Finset.mem_coe.mpr hv)
          have hqFace : H.nodeMap (H.tailOfAtom NF (H.nodeMap v)) ∈ H.face x :=
            htailBridge (H.nodeMap v) hwL
          have hqNode : H.nodeMap (H.tailOfAtom NF (H.nodeMap v)) ∈ H.node v := by
            have ht : H.tailOfAtom NF (H.nodeMap v) ∈ H.atom L (H.nodeMap v) :=
              (H.tailOfAtom_mem_atom hnf hmL hwL).1
            have hsub : H.tailOfAtom NF (H.nodeMap v) ∈ H.node (H.nodeMap v) :=
              H.atom_subset_node L (H.nodeMap v) ht
            have hqN : H.nodeMap (H.tailOfAtom NF (H.nodeMap v))
                ∈ H.node (H.tailOfAtom NF (H.nodeMap v)) := by
              have h1 := H.pow_nodeMap_mem_node (H.tailOfAtom NF (H.nodeMap v)) 1
              rwa [pow_one] at h1
            have e1 : H.node (H.tailOfAtom NF (H.nodeMap v))
                = H.node (H.nodeMap v) := (H.node_eq_of_mem hsub).symm
            have e2 : H.node (H.nodeMap v) = H.node v :=
              (H.node_eq_of_mem (by simpa using H.pow_nodeMap_mem_node v 1)).symm
            exact (e1.trans e2) ▸ hqN
          have hfacev : H.face x = H.face v :=
            H.face_eq_of_mem (by rw [← hldOF]; exact Finset.mem_coe.mpr hv)
          have hqmem : H.nodeMap (H.tailOfAtom NF (H.nodeMap v))
              ∈ H.node v ∩ H.face v := ⟨hqNode, hfacev ▸ hqFace⟩
          rw [hr.simple v hvdart] at hqmem
          have hqv : H.nodeMap (H.tailOfAtom NF (H.nodeMap v)) = v :=
            Set.mem_singleton_iff.mp hqmem
          rw [hstep1, hstep2, hqv]
      · -- 族外点：商 node 固定（n_quotient_permute 定义面）
        have hfix : H.nQuotient NF y = y := (H.nQuotient_permutes hnf).1 y hyFam
        rw [show (H.quotientHypermap hnf).nodeMap y = y from hfix]
        exact hfix
end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针已执行，快照 t64_axiom_audit.log 全文）：
本件公开件 1（AUQTZYZ，依赖 hnf/hAB/覆盖/三阶/edge 求值全链 + 批 63
EXISTS_PATH_COMPLEMENT）#print axioms 探针 = [propext, Classical.choice,
Quot.sound] 标准三内，零 sorryAx。private 桥件（permPowIterate /
complementPt_zero / edgeMap_apply / edgeMap_involute_apply / hswapA /
hswapB / htailBridge 等）全部经主件传递消费，主件公理面即全链公理面。
#print axioms Kepler.Text.TameSpine.AUQTZYZ
-/

