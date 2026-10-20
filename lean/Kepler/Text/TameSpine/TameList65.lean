/-
  Kepler.Text.TameSpine.TameList65 — B3 D 链第六批：AUQTZYZ HOL 全形
  （hedge 前件 discharge）+ RXOKSKC 开链。接续批 64 = TameList64.lean
  （9fd64f83）。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ 公开件 3：
  │ ① AUQTZYZ_hol（任务 1 = 批 64 诚实保真缺口 discharge）：HOL
  │   AUQTZYZ_concl（AUQTZYZ.hl :1851-:1858）原形全承载——消费批 64
  │   弱化形 AUQTZYZ（蕴含前件 hedge 挂第三组件），对打包的 L2 无条件
  │   证出 hedge 后供 hdih 作左项；弱化形保留在 TameList64 记账。
  │   hedge 闭路 = 第三路线（比批 64 双处方短一个量级）：w := N (F v)
  │   必自头——闭合域（is_normal 第 4 字段）给 w 落在某族环 L''，分
  │   情形：落面环 loop_of_face x 时逐点 map = faceMap；落 L2 时环映
  │   射二择一（loopMap_eq_faceMap_or_nodeMap_symm），faceMap 支即自
  │   头，nodeMap.symm 支推出 F v = L2.map w ∈ L2.darts（map 保环）与
  │   F v ∈ (loop_of_face x).darts 共点，由 ③ 共点同环
  │   （IsNormalFamily.eq_of_mem_of_mem）得 L2 = loop_of_face x 仍归
  │   面环自头。故恒 head NF w = w（headOfAtom_eq_self_iff），hedge
  │   化为 N (F w) = v = plain 对合 edgeMap (edgeMap v) = v 的平移
  │   （w = edgeMap v）。批 64 处方路线 1（HOL :2400-:2450 head/tail
  │   回环）与路线 2（ID-EDGE N (tail NF (N (F v))) = F v + nQ 对合
  │   分解 E = fQ⁻¹∘nQ）全程未动用——缺口在 is_normal 自身内闭合。
  │ ② rxMemListDarts（RXOKSKC.hl :496 MEM_LIST_DARTS）；③ symListDart
  │ （RXOKSKC.hl :507 SYM_LIST_DART——节点对换位件，任务 2 拓扑消费
  │ 件：消费在册 nodeNodeMapEq 与 plain 对合）。定义层 rx 件 3 枚
  │ （rxListOfDarts / rxListOfFaces / rxDartsOfList，泛型 α；list_pairs
  │ 泛型件经 qualified open 消费 Kepler.Assembly.listPairs——在册去
  │ 重，见雷区 #157）。
  │ 拓扑边件发现：Rxokskc ← Auqtzyz 的具名边 node_node_map_eq
  │ （AUQTZYZ.hl :254）**已在册**（批 60 TameList60.lean:448 公开件
  │ nodeNodeMapEq），本批直接消费未重落。
  │ 全件零 sorry；公理面三件探针 = AUQTZYZ_hol/symListDart
  │ [propext, Classical.choice, Quot.sound]、rxMemListDarts
  │ [propext, Quot.sound]（prop 件无 choice）标准内零 sorryAx（锚见
  │ 尾注）。构建纯 lake build Kepler.Text.TameSpine.TameList65 单发
  │ 串行零旗标零 -K，clone 绿 9497 jobs。
  └──────────────────────────────────────────────────────────────

  新雷区（本批实测记档，编号承批 64 的 #155）：
  - **#156 edgeMap 恒等式的语法形分层**：edgeMap_involute_apply 的
    LHS 是 edge (edge z) 形而非 N∘F 语法形——congrArg N.symm 喂入后
    Equiv.symm_apply_apply（pattern `Equiv.symm ?e (?e ?x)`）咬不住，
    build surfaced rewrite failed；须经 e1/e2-have 链先把目标折算成
    N (F (N (F z))) 语法形（symListDart 的 key calc 链）再作用 N.symm。
  - **#157 在册普查的 camelCase 盲区**：首查 pattern 用 HOL snake_case
    （list_pairs/list_of_darts）漏掉在册 camelCase 重名件——
    nodeNodeMapEq（TameList60:448）、listOfFaces（TameList31:100）、
    listPairs（Assembly 泛型）三处到 build 才 surfaced（already been
    declared）；且同 namespace（TameList31.listOfFaces）一撞即爆、异
    namespace（Assembly.listPairs）不报但属重复定义。普查必须双
    casing 发（snake + camel）+ namespace 归属检查。
  - **#158 omit-in 与 docstring 次序**：`/-- doc -/ omit [I] in
    theorem` 解析爆（docstring 后期望声明关键词，unexpected token
    'omit'）；正确形 `omit [I] in /-- doc -/ theorem`——docstring 属
    声明语法段，须落在 in 之后。
  - **#159 双层同型目标的多发 rw 先咬不确定**（预判记档，源自批 64
    #149 同类）：rw [← e] 在 N (F (N (F v))) 上内层 ?x := v 与外层
    ?x := N (F v) 两可，首个匹配实例化决定全部替换位——AUQTZYZ_hol
    尾段以 e1/e2/e3-have + .symm.trans calc 链规避，零 rw 发。

  任务 2 断点记档：RXOKSKC.hl（1,105 行）本批收到 :507——定义层
  （list_pairs 消费在册 / rxListOfDarts / rxListOfFaces / rxDartsOfList）
  + :496 MEM_LIST_DARTS + :507 SYM_LIST_DART。在册缺口语普查：
  iterate_map_valuation / DART_EQ_UNIONS / FINITE_ORBIT_MAP
  （Hypermap_and_fan 侧）零在册；hypermap_of_list 定义件（res 限析 +
  Hypermap 构造）、good_list/good_list_nodes 泛型层（Assembly 的
  GoodListNodes 是 True 桩）未落。

  批 66 接续点（RXOKSKC.hl 精确接续）：
  - 首任务：UNIQ_LIST_OF_DARTS（:25，泛型 Nodup 层：L.Nodup + 逐片
    Nodup + 跨片 pair 列表不交 ⟹ dart 表 Nodup；需 listPairs 保 Nodup
    件——Mathlib Nodup.zip 或 induction 自证）；
  - 次任务：EXISTS_LIST_FACE_NODE（:133，枚举层门件：i < n ≤
    CARD (face x) 处 node (F^i x) 互异——simple 单点钉 + face 轨道周
    期（orbit_cyclic 已在册）+ List.ofFn 构造 LENGTH/EL 槽）；
  - 后续链：EXISTS_LIST_FACE_NODE_FUNC（:229 Skolem 化）→
    LIST_COR_FACE_SET（:293 代表集归纳）→ LIST_COR_FACE_SET1（:418）
    → ONE_TO_ONE_DART（:474；faceMap/nodeMap_injective +
    dart_invariant 已在册）→ **RXOKSKC（:523，A9 接口件，到达时单独
    标注）**：iso H (hypermap_of_list L) 是 Assembly 接口 9 的消费目
    标——把几何 hypermap 钉死到有限 list 表示（iso 映射 dart x ↦
    (node x, node (F x))，e/n/f 三槽分别由 SYM_LIST_DART / n_list /
    f_list 对应），是装配线读档同构的入轨件。
-/

import Kepler.Text.TameSpine.TameList64

/-! # AUQTZYZ HOL 全形（hedge discharge）+ RXOKSKC 开链 -/

namespace Kepler.Text.TameSpine

variable {α : Type*} [DecidableEq α]

/-! ### §0 本地私桥（TameList64 §0 件 private 跨模块不可见，按批 63
§0' 体例逐字本地复制，文本取已构建绿实库） -/

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

/-! ### §1 AUQTZYZ_hol：HOL AUQTZYZ_concl（:1851-:1858）原形全承载 -/

/-- **HOL `AUQTZYZ_concl`**（AUQTZYZ.hl :1851-:1858 语句原形，无 hedge
前件）：受限 H、x ∈ dart ⟹ ∃L2，is_normal {loop_of_face x, L2} ∧
path_of_loop L2 (complement x 0) = complement x ∧ dih2k (quotient
{loop_of_face x, L2}) (CARD (face x))。

证明 = 消费 TameList64 的弱化形 AUQTZYZ（蕴含前件 hedge 挂第三组件），
对打包 L2 无条件证 hedge 后供出（hedge 作左项）。 -/
theorem AUQTZYZ_hol (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) :
    ∃ (L2 : Loop α) (hnf : H.IsNormalFamily {H.loopOfFace x, L2}),
      L2.pathOf (H.complementPt x 0) = H.complementPt x ∧
      Dih2k (H.quotientHypermap hnf) (H.face x).ncard := by
  obtain ⟨L2, hnf, hpath, hdih⟩ := AUQTZYZ H hr hx
  refine ⟨L2, hnf, hpath, hdih ?_⟩
  -- hedge：∀ v ∈ face x, N (F (head NF (N (F v)))) = v
  intro v hv
  have hmL2 : L2 ∈ ({H.loopOfFace x, L2} : Set (Loop α)) :=
    Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
  have hmLOF : H.loopOfFace x ∈ ({H.loopOfFace x, L2} : Set (Loop α)) :=
    Set.mem_insert_iff.mpr (Or.inl rfl)
  have hvF : H.faceMap v ∈ H.face x := by
    have hfe : H.face x = H.face v := H.face_eq_of_mem hv
    have h1 := H.pow_faceMap_mem_face v 1
    rw [pow_one] at h1
    rw [hfe]
    exact h1
  have hv' : H.faceMap v ∈ (H.loopOfFace x).darts :=
    (H.mem_faceFinset x _).mpr hvF
  have hwNode : H.nodeMap (H.faceMap v) ∈ H.node (H.faceMap v) := by
    have h1 := H.pow_nodeMap_mem_node (H.faceMap v) 1
    rwa [pow_one] at h1
  -- 闭合域：w := N (F v) 落在某族环 L''（is_normal 第 4 字段）
  obtain ⟨L'', hL'', hw''⟩ := hnf.2.2.2 (H.loopOfFace x) hmLOF _ _ hv' hwNode
  have hhead : H.headOfAtom ({H.loopOfFace x, L2} : Set (Loop α))
      (H.nodeMap (H.faceMap v)) = H.nodeMap (H.faceMap v) := by
    have selfHead : ∀ Lm : Loop α, Lm ∈ ({H.loopOfFace x, L2} : Set (Loop α)) →
        H.nodeMap (H.faceMap v) ∈ Lm.darts →
        H.headOfAtom ({H.loopOfFace x, L2} : Set (Loop α)) (H.nodeMap (H.faceMap v))
          = H.nodeMap (H.faceMap v) := by
      rintro Lm hLm hwLm
      rcases Set.mem_insert_iff.mp hLm with hE | hE
      · -- 支 1：w 落面环 loop_of_face x——面环逐点 map = faceMap，自头
        rw [hE] at hwLm
        rw [H.headOfAtom_eq_self_iff hr hnf hmLOF hwLm]
        have hpm := H.loopOfFace_map_pow_apply
          (by rw [← H.loopOfFace_darts x]; exact Finset.mem_coe.mpr hwLm) 1
        rwa [pow_one, pow_one] at hpm
      · -- 支 2：w 落 L2——环映射二择一
        have hE2 : L2 = Lm := (Set.mem_singleton_iff.mp hE).symm
        rw [← hE2] at hwLm
        rw [H.headOfAtom_eq_self_iff hr hnf hmL2 hwLm]
        rcases H.loopMap_eq_faceMap_or_nodeMap_symm hnf hmL2 hwLm with h | h
        · exact h
        · -- nodeMap.symm 支：L2.map w = N.symm w = F v ∈ L2.darts（map 保环）
          -- 与 F v ∈ (loop_of_face x).darts 共点 ⟹ L2 = loop_of_face x（③）
          have e : L2.map (H.nodeMap (H.faceMap v)) = H.faceMap v := by
            rw [h, Equiv.symm_apply_apply]
          have hFv : H.faceMap v ∈ L2.darts :=
            (e ▸ L2.map_mem hwLm : H.faceMap v ∈ L2.darts)
          have hLL : L2 = H.loopOfFace x :=
            hnf.eq_of_mem_of_mem hmL2 hmLOF hFv hv'
          rw [hLL] at hwLm ⊢
          have hpm := H.loopOfFace_map_pow_apply
            (by rw [← H.loopOfFace_darts x]; exact Finset.mem_coe.mpr hwLm) 1
          rwa [pow_one, pow_one] at hpm
    exact selfHead L'' hL'' hw''
  rw [hhead]
  -- plain 对合回环：N (F w) = edge w = edge (edge v) = v（w = edge v）
  have e1 : H.edgeMap v = H.nodeMap (H.faceMap v) := edgeMap_apply H hr.plain v
  have e2 : H.edgeMap (H.edgeMap v) = v := edgeMap_involute_apply H hr.plain v
  have e3 : H.edgeMap (H.nodeMap (H.faceMap v)) = v := by rw [← e1]; exact e2
  exact (edgeMap_apply H hr.plain (H.nodeMap (H.faceMap v))).symm.trans e3

/-! ### §2 RXOKSKC 开链：list_hypermap 定义层 + 拓扑消费件
（RXOKSKC.hl，1,105 行；首件层。）§2 拓扑 Rxokskc ← Auqtzyz 的具名边
`node_node_map_eq`（AUQTZYZ.hl:254）**已在册**：批 60 TameList60.lean:448
公开件 nodeNodeMapEq，本件直接消费（symListDart :507 即其 RXOKSKC 侧
首个消费件）。定义层在册去重：list_pairs 泛型件 = Kepler.Assembly.listPairs
（经 TameList31 已在本链 import 闭包内， qualified open 消费；
TameList31.listOfFaces 为 fgraph ℕ 专件，泛型层以 rx 前缀新落）。
**RXOKSKC.hl:523 为 A9 接口件，本批未到达**——它是 Assembly 接口 9 的
消费目标：iso H (hypermap_of_list L) 把几何 hypermap 钉死到有限 list
表示（dart x ↦ (node x, node (F x))），是装配线读档同构的入轨件，
批 66 到达时单独标注。 -/

open Kepler.Assembly (listPairs)

/-- HOL `list_of_darts`（list_hypermap-compiled.hl:23-24）泛型 α 层：
`foldr (λlist a. list_pairs list ++ a) [] L = (MAP list_pairs L).flatten`
（Kepler.Assembly.listOfDarts 为 fgraph ℕ 专件；此处按 RXOKSKC 的抽象
α 定义层落地，节点为元、节点对为 dart）。 -/
def rxListOfDarts (L : List (List α)) : List (α × α) := (L.map listPairs).flatten

/-- HOL `list_of_faces`（list_hypermap-compiled.hl:26）泛型 α 层。 -/
def rxListOfFaces (L : List (List α)) : List (List (α × α)) := L.map listPairs

/-- HOL `darts_of_list`（list_hypermap-compiled.hl:24，`set_of_list` 的
Lean 侧 Finset 形）。 -/
def rxDartsOfList (L : List (List α)) : Finset (α × α) :=
  (rxListOfDarts L).toFinset

omit [DecidableEq α] in
/-- **HOL `MEM_LIST_DARTS`**（RXOKSKC.hl:496）：dart 落列表超映射的
dart 表 ⟹ 它是某面片节点对的像。 -/
theorem rxMemListDarts {d : α × α} {L : List (List α)} :
    d ∈ rxListOfDarts L ↔ ∃ x ∈ L, d ∈ listPairs x := by
  simp [rxListOfDarts]

/-- **HOL `SYM_LIST_DART`**（RXOKSKC.hl:507）：z1 := N (F z) 的节点对 =
z 的节点对之换位——list 超映射的 e_list（换位）在 iso（x ↦ (node x,
node (F x))）下的对应件。证明消费在册 nodeNodeMapEq（Auqtzyz 拓扑边）
与 plain 对合的 N.symm 平移。 -/
theorem symListDart (H : Hypermap α) (hr : H.IsRestricted) {z z1 : α}
    (h : z1 = H.nodeMap (H.faceMap z)) :
    H.node z1 = H.node (H.faceMap z) ∧ H.node (H.faceMap z1) = H.node z := by
  subst h
  refine ⟨nodeNodeMapEq H _, ?_⟩
  -- 平凡回环链：N (F (N (F z))) = z（plain 对合的 N∘F 语法形展开）
  have key : H.nodeMap (H.faceMap (H.nodeMap (H.faceMap z))) = z := by
    have e2 : H.edgeMap z = H.nodeMap (H.faceMap z) := edgeMap_apply H hr.plain z
    have e1 : H.edgeMap (H.nodeMap (H.faceMap z))
        = H.nodeMap (H.faceMap (H.nodeMap (H.faceMap z))) :=
      edgeMap_apply H hr.plain _
    calc H.nodeMap (H.faceMap (H.nodeMap (H.faceMap z)))
        = H.edgeMap (H.nodeMap (H.faceMap z)) := e1.symm
      _ = H.edgeMap (H.edgeMap z) := by rw [e2]
      _ = z := edgeMap_involute_apply H hr.plain z
  -- F (N (F z)) = N.symm z：key 作用 N.symm 后 Equiv.symm_apply_apply 收
  have hF : H.faceMap (H.nodeMap (H.faceMap z)) = H.nodeMap.symm z := by
    have h2 := congrArg (fun w : α => H.nodeMap.symm w) key
    rwa [Equiv.symm_apply_apply] at h2
  rw [hF]
  -- node (N.symm z) = node z（逆元落 node 轨道）
  have hs : H.nodeMap.symm z ∈ H.node z :=
    H.nodeMap_permutes.symm_apply_mem_orbitMap z
  exact (H.node_eq_of_mem hs).symm

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针已执行，快照 t65_axiom_audit.log 全文）：
本件公开件 3 探针——AUQTZYZ_hol（消费批 64 AUQTZYZ 全链 +
TameList63 EXISTS_PATH_COMPLEMENT）、symListDart（消费在册
nodeNodeMapEq + §0 私桥 plain 对合）= [propext, Classical.choice,
Quot.sound] 标准三内；rxMemListDarts = [propext, Quot.sound]
（prop 件无 choice）——全件零 sorryAx。定义层 3 枚（rxListOfDarts /
rxListOfFaces / rxDartsOfList）为 def 不携公理；private 桥件
（edgeMap_apply / edgeMap_involute_apply）经 symListDart 传递消费。
#print axioms Kepler.Text.TameSpine.AUQTZYZ_hol
-/
