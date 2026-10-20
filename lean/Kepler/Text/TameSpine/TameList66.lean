/-
  Kepler.Text.TameSpine.TameList66 — B3 D 链第七批：RXOKSKC 六站前件全闭
  （UNIQ_LIST_OF_DARTS → ONE_TO_ONE_DART，RXOKSKC.hl :25-:492 全段）。
  接续批 65 = TameList65.lean（89608ac9）。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ 公开件 6（六站前件 :25-:492 全段零 sorry 真证）：
  │ ① rxUniqListOfDarts（:25 UNIQ_LIST_OF_DARTS，泛型 Nodup 层）——
  │   uniq ↦ Nodup、不交 ↦ List.Disjoint，机理 = Mathlib nodup_flatten
  │   （flatten 无重 ↔ 逐片无重 + Pairwise 不交）；zip 三小件
  │   （mem_zip_fst / nodup_zip_of_nodup_left / mem_zip_ex）自证——
  │   Mathlib 无现成 mem_zip（雷区 #168）。
  │ ② existsListFaceNode（:133 EXISTS_LIST_FACE_NODE，枚举层门件）+
  │   existsListFaceNode2（:223 满长特化）——构造 = List.ofFn；
  │   无重核心 = simple 单点钉（F^j x ∈ node ∩ face = {F^j x} ⟹
  │   F^i x = F^j x）+ card_orbit_le 反克（CARD (face x) ≤ j - i <
  │   j < CARD (face x)），HOL lemma_different_nodes +
  │   lemma_congruence_on_face 的反向 card 路线。
  │ ③ existsListFaceNodeFunc（:229 EXISTS_LIST_FACE_NODE_FUNC，Skolem
  │   化门件）——f 经 choose 全域化（x ∉ dart 处占位空表）；
  │   list_pairs 分解 = mem_zip_ex + rot1 下标折算
  │   getElem_rot1（(drop 1 ++ take 1)[i]? = L[(i+1) % len]?），尾回环
  │   槽由 F^(CARD (face x)) x = x（pow_card_face_apply_self，在册）收。
  │ ④ listCorFaceSet（:293 LIST_COR_FACE_SET）+ listCorFaceSet1（:418
  │   LIST_COR_FACE_SET1）——代表集归纳 + InjOn.ncard_image 鸽巢
  │   （CARD_IMAGE_EQ_INJ 机理）；SET1 的 {face y | y ∈ S} = face_set
  │   以 eq_of_subset_of_ncard_le 收（HOL DART_EQ_UNIONS +
  │   CARD_SUBSET_EQ 路线的 Lean 短路，覆盖槽由 face x ∈ face_set 自身
  │   收；并集层底座留批 67 的 RXOKSKC 大证消费）。
  │ ⑤ oneToOneDart（:474 ONE_TO_ONE_DART）——is_no_double_joins 槽
  │   一次作用：node x = node y 给 y ∈ node x；node (F x) = node (F y)
  │   经在册 nodeNodeMapEq（TameList60:448，Auqtzyz 拓扑边）+ plain
  │   edge_map 恒等式（§0 私桥逐字复制）给 edge y ∈ node (edge x)。
  │ ⑥ 站 6 消费件泛型 def 层 5 枚（rxESwap / rxFindFace / rxFList /
  │   rxNList / rxGoodList，list_hypermap-compiled.hl:47-65 +
  │   tame_defs2.hl:31-36 泛型 α 首落；具象 fgraph ℕ 层 =
  │   Assembly.GoodListDefs + TameLp hypermapOfList 在册去重）。
  │ 诚实记档：HOL :118 MEM_CONS / :122 LIST_OF_SET_SING 为 inline 级
  │ 平凡件，被 List.ofFn / Finset 路线吸收不落；EL 槽以 `?`-some 形
  │ 渲染（HOL EL i L = v 的诚实全形，泛型 α 免 Inhabited 桩）。
  │ 全件零 sorry；公理探针 6 件 = rxUniqListOfDarts [propext,
  │ Quot.sound]（prop 件无 choice），existsListFaceNode /
  │ existsListFaceNodeFunc / listCorFaceSet / listCorFaceSet1 /
  │ oneToOneDart = [propext, Classical.choice, Quot.sound] 标准三内
  │ 零 sorryAx（锚见尾注）。构建纯 lake build
  │ Kepler.Text.TameSpine.TameList66 单发串行零旗标零 -K，clone 绿
  │ 9498 jobs 零警告。
  └──────────────────────────────────────────────────────────────

  新雷区（本批实测记档，编号承批 65 的 #159）：
  - **#160 泛型层 EL 槽的 Inhabited 陷阱**：`L[i]!`（getElem!）需
    [Inhabited α]——泛型 α 层语句全部爆 TC 失败；EL 槽须 `?`-some 形
    （L[i]? = some v，HOL EL 的诚实全渲染），元素拔取走
    Option.some.inj（两侧 ?-等式 trans 后投影）。
  - **#161 幂作用的结合序**：HOL `node H ((face_map H POWER i) x)` 的
    Lean 渲染必须 `H.node ((H.faceMap ^ i) x)`（幂先作用于 x 再进
    node）；漏内层括号成 `H.node (H.faceMap ^ i) x` 按函数复合解析，
    报 "Equiv.Perm α expected α" 连环错。
  - **#162 List.Disjoint vs 根 Disjoint**：Pairwise Disjoint（nodup_
    flatten 槽）的不交是 List.Disjoint（Batteries，成员不交）；裸
    Disjoint 解析为 Order.Disjoint，索 PartialOrder (List α) 爆实例
    错——泛型 List 语境的不交一律写全名 List.Disjoint。
  - **#163 Pairwise.cons 的子关系形 + induction 自动 revert**：
    List.Pairwise.cons : Pairwise (R a) l → Pairwise R (a :: l)——
    尾槽 IH 是 Pairwise R t（同 R）但头槽是子关系 Pairwise (R a) t，
    `.cons ?_ ih` 两槽不可同源；且 induction L 自动 revert 上下文中
    依赖 L 的 h1/h2/h3 进 ih 前件——须显式 revert + intro + 对 t 逐
    weakening 供 ih。
  - **#164 依赖下标的 rw 动机爆**：rw [Nat.mod_eq_of_lt h] 在带证明槽
    的 getElem（(f x)[(i+1) % C]'_）上下标上 motive 不型正；?-form
    （getElem? 无证明槽）重写免此雷——getElem_rot1 与 mod 折算全程
    ?-form，元素提取只用 he.symm.trans + Option.some.inj。
  - **#165 rw [def名] 无方程**：rw [rxListOfDarts] 不解 def（非 Eq
    项）；def 展开用 simp only [def名]（equational lemma 自动生成）。
  - **#166 by_cases 否定支的非严格性**：¬(i < j) 只给 j ≤ i——strict
    分裂须 rcases Nat.lt_or_eq_of_le 再分 j < i / i = j（后者即结
    论）；直接 have hji : j < i := by omega 爆反例。
  - **#167 card_orbit_le 的命名空间归属**：hypermap.hl 轨道选摘落在
    Kepler.Text 的 section PermIteration（section 不加名）——全名
    Kepler.Text.card_orbit_le，从 TameSpine 用裸名 card_orbit_le 解
    析；`Hypermap.card_orbit_le`（Kepler.Text.Hypermap 前缀）反而
    Unknown constant。同族 orbit_cyclic / orbitMap / orbitMap_eq_of_
    mem / pow_apply_mem_orbitMap 全在 Kepler.Text；Hypermap 结构域件
    （mem_node_self 等）才走 H. 点记法。
  - 卫生记档：push_neg 已弃用（warning）——∃-否定的展开用
    not_exists.mp + not_not.mp 组合；section variable [DecidableEq α]
    对纯 List 件自动纳入未用——private 件逐件 omit [DecidableEq α]
    in（docstring 前，雷区 #158 同源）。

  任务断点记档：RXOKSKC.hl（1,105 行）本批收到 :492——六站前件全段
  （UNIQ_LIST_OF_DARTS :25 / EXISTS_LIST_FACE_NODE :133 / :223 /
  FUNC :229 / LIST_COR_FACE_SET :293 / LIST_COR_FACE_SET1 :418 /
  ONE_TO_ONE_DART :474）。**:523 RXOKSKC（A9 接口件）未到达**。

  批 67 接续点（RXOKSKC.hl :523 处方，站 6 主目标）：
  - 底座一（bijOn 群泛型化，TameLp:3900-4035 机理照搬，参数化
    {L : List (List α)} (hn : (rxListOfDarts L).Nodup)）：
    rxFindFace congruence（findFaceDarts_congr_of_mem）、
    mem_darts_of_mem_rxFindFace、rxFList_mem_darts、
    rxFList_rxFindFace_prev_inverse / prev_rxFindFace_inverse、
    rxESwap_inj、rxNList_rxFList（nList_fList 机理）、
    bijOn_rxESwap / bijOn_rxNList / bijOn_rxFList。
  - 底座二（hypermapOfListG）：extendPerm (rxListOfDarts L).toFinset
    (res 型 Fan.bijOn_res + Fan.extendPerm，在册泛型) 三槽 +
    comp_eq_one 经 rxNList_rxFList（TameLp:3993-4035 形逐条泛型化）；
    darts/edgeMap/nodeMap/faceMap 四槽 hypermapOfList 同面。
  - 缺口底座（零在册重推导，RXOKSKC 大证消费）：DART_EQ_UNIONS
    (dart = ⋃ face_set/node_set/edge_set 三槽：⊆ orbit 自含 + ⊇
    orbit ⊆ dart)、FINITE_ORBIT_MAP（card_orbit_le + orbit_cyclic
    反向枚举形，均在册可拼）、iterate_map_valuation（p (p^n x) =
    p^(SUC n) x = 一步 pow_succ'）。iso 消费在册 Kepler.Text.Hypermap
    的 Iso（:8249-8296，TameLp S3 白捡件同体）或 HOL iso 泛型 def
    （hypermap.hl:9614）逐字落地。
  - RXOKSKC 大证（HOL :527-:1098，五槽）：s := f '' S（f =
    existsListFaceNodeFunc 的 Skolem，S = listCorFaceSet1 的代表集），
    L := s.toList；uniq s 槽（:605-:634）：f x' = f x'' 逐点 EL 相等
    → (F^i x'') = (F^i' x') → ONE_TO_ONE_DART（本批）+ 幂 dart 不变
    + face_eq_of_mem 链 → x'' = x'；good_list 槽（:639-:666）：Nodup
    由 rxUniqListOfDarts（本批）+ uniq s 供 h3、非空由 station-3、
    对合闭包 (SND,FST) 槽经 SYM_LIST_DART（TameList65）+
    DART_EQ_UNIONS + FINITE_ORBIT_MAP；good_list_nodes 槽（:723-:783）：
    nodeSet (hypermapOfListG L) = FST-fiber 集
    （size_list_of_nodes / good_list_nodes_condition 机理）；iso 槽
    （:784-:1098）：dart x ↦ (H.node x, H.node (H.faceMap x))，e 槽 =
    SYM_LIST_DART + edge_map_convolution（:906-:923），n 槽 = n_eq_e_fi
    （:1073-:1089，需 HYP_MAPS_INVS 槽，Lvducxu 零在册），f 槽 =
    find_face_eq + next_el（:928-:1065 最重段，FINITE_ORBIT_MAP +
    iterate_map_valuation 逐指标）。
-/

import Kepler.Text.TameSpine.TameList65

/-! # RXOKSKC 六站前件（:25-:492）+ 泛型 def 层地基 -/

namespace Kepler.Text.TameSpine

variable {α : Type*} [DecidableEq α]

open Kepler.Assembly (listPairs nextEl prevEl)

/-! ### §0 本地私桥（TameList65 §0 件 private 跨模块不可见，按批 63
§0' 体例逐字本地复制，文本取已构建绿实库 TameList65.lean:98-103） -/

/-- `edgeMap = nodeMap ∘ faceMap` 的点态形（plain_iff_edgeMap_eq 的应用面；
AUQTZYZ.hl :2300 REWRITE[is_restricted; edge_map_convolution] 同面）。 -/
private theorem edgeMap_apply (H : Hypermap α) (hp : H.Plain) (w : α) :
    H.edgeMap w = H.nodeMap (H.faceMap w) := by
  rw [H.plain_iff_edgeMap_eq.1 hp]
  rfl

/-! ### §1 站 1 UNIQ_LIST_OF_DARTS（RXOKSKC.hl:25-:116，泛型 Nodup 层）

HOL 前件：`uniq L ∧ ALL uniq L ∧ (∀x y ∈ L, x ≠ y → list_pairs x 与
list_pairs y 不交)`；结论 `uniq (list_of_darts L)`。Lean 侧 uniq ↦
List.Nodup、不交 ↦ List.Disjoint，机理 = Mathlib nodup_flatten（flatten
无重 ↔ 逐片无重 + 两两不交）。 -/

omit [DecidableEq α] in
/-- zip 表的左投影成员件：`p ∈ l₁.zip l₂ → p.1 ∈ l₁`（Mathlib 无现成
mem_zip，本批自证；站 1/站 3 双消费）。 -/
private theorem mem_zip_fst {l₁ l₂ : List α} {p : α × α} (h : p ∈ l₁.zip l₂) :
    p.1 ∈ l₁ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp at h
  | cons a t ih =>
    cases l₂ with
    | nil => simp at h
    | cons b t' =>
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

omit [DecidableEq α] in
/-- zip 表左列无重 ⟹ zip 表无重（左列元素钉位）。 -/
private theorem nodup_zip_of_nodup_left {l₁ l₂ : List α} (h : l₁.Nodup) :
    (l₁.zip l₂).Nodup := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a t ih =>
    cases l₂ with
    | nil => simp
    | cons b t' =>
      rw [List.zip_cons_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih (List.nodup_cons.mp h).2⟩
      exact List.nodup_cons.mp h |>.1 (mem_zip_fst hm)

omit [DecidableEq α] in
/-- zip 表成员的指标存在形（`?`-some 形，泛型 α 免 Inhabited 桩；站 3
list_pairs 分解的消费件）。 -/
private theorem mem_zip_ex {l₁ l₂ : List α} {p : α × α} (h : p ∈ l₁.zip l₂) :
    ∃ i : ℕ, i < l₁.length ∧ i < l₂.length ∧ l₁[i]? = some p.1 ∧ l₂[i]? = some p.2 := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp at h
  | cons a t ih =>
    cases l₂ with
    | nil => simp at h
    | cons b t' =>
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, by simp, by simp, rfl, rfl⟩
      · obtain ⟨i, hi1, hi2, e1, e2⟩ := ih h
        exact ⟨i + 1, by simp only [List.length_cons]; omega,
          by simp only [List.length_cons]; omega, by simpa using e1, by simpa using e2⟩

omit [DecidableEq α] in
/-- **HOL `UNIQ_LIST_OF_DARTS`**（RXOKSKC.hl:25-:26）：L 无重 + 逐片无重 +
跨片 pair 列表两两不交 ⟹ dart 表 `(L.map listPairs).flatten` 无重。 -/
theorem rxUniqListOfDarts {L : List (List α)} (h1 : L.Nodup)
    (h2 : ∀ l ∈ L, l.Nodup)
    (h3 : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → List.Disjoint (listPairs x) (listPairs y)) :
    (rxListOfDarts L).Nodup := by
  simp only [rxListOfDarts, List.nodup_flatten, List.pairwise_map]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
    exact nodup_zip_of_nodup_left (h2 x hx)
  · revert h1 h2 h3
    induction L with
    | nil => intro _ _ _; exact .nil
    | cons a t ih =>
      intro h1 h2 h3
      refine List.Pairwise.cons ?_ (ih (List.nodup_cons.mp h1).2
        (fun l hl => h2 l (List.mem_cons_of_mem _ hl)) ?_)
      · intro b hb
        exact h3 a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb)
          fun h => (List.nodup_cons.mp h1).1 (h ▸ hb)
      · intro x hx y hy hne
        exact h3 x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hne

/-! ### §2 站 2 EXISTS_LIST_FACE_NODE（RXOKSKC.hl:133-:220 + :223-:225，
枚举层门件）

EL 槽以 `?`-some 形渲染（HOL `EL i L = v` 的诚实全形：`L[i]? = some v`，
泛型 α 免 Inhabited 桩）。无重核心机理（HOL :186-:215
lemma_different_nodes + simple 单点 + lemma_congruence_on_face 反向）：
i < j < CARD (face x) 处 node (F^i x) = node (F^j x) 不可能——F^j x 落
simple 交 ⟨node (F^j x), face (F^j x)⟩ 的单点，钉出 F^i x = F^j x，
card_orbit_le 反克（CARD (face x) ≤ j - i < j < CARD (face x)）。 -/

/-- 站 2 无重核心：i < j < CARD (face x) 且 node (F^i x) = node (F^j x)
给出矛盾。 -/
private theorem faceNode_core (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) {i j : ℕ} (hlt : i < j)
    (heq : H.node ((H.faceMap ^ i) x) = H.node ((H.faceMap ^ j) x))
    (hjC : j < (H.face x).ncard) : False := by
  have hjd : (H.faceMap ^ j) x ∈ H.darts := H.faceMap_permutes.pow_apply_mem j hx
  have hid : (H.faceMap ^ i) x ∈ H.node ((H.faceMap ^ j) x) := by
    have h0 : (H.faceMap ^ i) x ∈ H.node ((H.faceMap ^ i) x) := H.mem_node_self _
    rw [heq] at h0
    exact h0
  have hfj : H.face x = H.face ((H.faceMap ^ j) x) :=
    H.face_eq_of_mem (H.pow_faceMap_mem_face x j)
  have hif : (H.faceMap ^ i) x ∈ H.face ((H.faceMap ^ j) x) := by
    rw [← hfj]; exact H.pow_faceMap_mem_face x i
  have hin : (H.faceMap ^ i) x ∈ H.node ((H.faceMap ^ j) x) ∩ H.face ((H.faceMap ^ j) x) :=
    ⟨hid, hif⟩
  rw [hr.simple _ hjd] at hin
  have heij : (H.faceMap ^ i) x = (H.faceMap ^ j) x := Set.mem_singleton_iff.mp hin
  have h1 : (H.faceMap ^ i) ((H.faceMap ^ (j - i)) x) = (H.faceMap ^ j) x := by
    have hle : i + (j - i) = j := Nat.add_sub_cancel' (Nat.le_of_lt hlt)
    rw [← Equiv.Perm.mul_apply, ← pow_add, hle]
  have hfix : x = (H.faceMap ^ (j - i)) x :=
    (H.faceMap ^ i).injective (heij.trans h1.symm)
  have hcard : (H.face x).ncard ≤ j - i := by
    show (orbitMap H.faceMap x).ncard ≤ j - i
    exact card_orbit_le H.faceMap (by omega) hfix.symm
  omega

/-- 站 2 无重引理：i, j < n ≤ CARD (face x) 处 node (F^i x) =
node (F^j x) ⟹ i = j。 -/
private theorem faceNode_inj (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) {n i j : ℕ} (hi : i < n) (hj : j < n)
    (hn : n ≤ (H.face x).ncard)
    (heq : H.node ((H.faceMap ^ i) x) = H.node ((H.faceMap ^ j) x)) : i = j := by
  by_cases hlt : i < j
  · have hC : j < (H.face x).ncard := by omega
    exact (faceNode_core H hr hx hlt heq hC).elim
  · rcases Nat.lt_or_eq_of_le (Nat.not_lt.mp hlt) with hji | hij
    · have hC : i < (H.face x).ncard := by omega
      exact (faceNode_core H hr hx hji heq.symm hC).elim
    · exact hij.symm

/-- **HOL `EXISTS_LIST_FACE_NODE`**（RXOKSKC.hl:133-:220）：受限 H、
x ∈ dart、n ≤ CARD (face x) ⟹ 存在长 n 无重列表逐项枚举
node (F^i x)（i < n）。构造 = List.ofFn（LENGTH/EL 槽由 length_ofFn /
getElem_ofFn 收，uniq 槽由 nodup_ofFn + faceNode_inj 收）。 -/
theorem existsListFaceNode (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) (hn : n ≤ (H.face x).ncard) :
    ∃ L : List (Set α), (∀ i < n, L[i]? = some (H.node ((H.faceMap ^ i) x))) ∧
      L.length = n ∧ L.Nodup := by
  refine ⟨List.ofFn fun i : Fin n => H.node ((H.faceMap ^ (i : ℕ)) x), ?_,
    List.length_ofFn, ?_⟩
  · intro i hi
    rw [List.getElem?_eq_some_iff]
    refine ⟨by rw [List.length_ofFn]; exact hi, ?_⟩
    rw [List.getElem_ofFn (by rw [List.length_ofFn]; exact hi)]
  · rw [List.nodup_ofFn]
    intro i j hij
    exact Fin.ext (faceNode_inj H hr hx i.isLt j.isLt hn hij)

/-- **HOL `EXISTS_LIST_FACE_NODE2`**（RXOKSKC.hl:223-:225）：满长特化
n := CARD (face x)。 -/
theorem existsListFaceNode2 (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) :
    ∃ L : List (Set α),
      (∀ i < (H.face x).ncard, L[i]? = some (H.node ((H.faceMap ^ i) x))) ∧
      L.length = (H.face x).ncard ∧ L.Nodup :=
  existsListFaceNode H hr hx _ (Nat.le_refl _)

/-! ### §3 站 3 EXISTS_LIST_FACE_NODE_FUNC（RXOKSKC.hl:229-:290，Skolem
化门件）

Skolem 函数经 choose 全域化（x ∉ dart 处取占位空表）；list_pairs 分解
（HOL :256-:274 rot 1 / zip / EL_APPEND 机理）= mem_zip_ex + rot1 下标
折算 `(L.drop 1 ++ L.take 1)[i]? = L[(i+1) % L.length]?`，尾回环槽由
F^(CARD (face x)) x = x（pow_card_face_apply_self，在册）收。 -/

omit [DecidableEq α] in
/-- rot1 下标折算：`list_pairs` 的第二列（`drop 1 ++ take 1`）在
i < L.length 处取到 `L[(i+1) % L.length]`（HOL Seq.rot1_cons 同面）。 -/
private theorem getElem_rot1 (L : List α) (i : ℕ) (hi : i < L.length) :
    (L.drop 1 ++ L.take 1)[i]? = L[(i + 1) % L.length]? := by
  rcases Nat.lt_or_ge i (L.length - 1) with hlt | hge
  · have h1 : i < (L.drop 1).length := by
      simp only [List.length_drop]; omega
    rw [List.getElem?_append_left h1, List.getElem?_drop,
      show (i + 1) % L.length = i + 1 from Nat.mod_eq_of_lt (by omega),
      Nat.add_comm 1 i]
  · have hilen : i = L.length - 1 := by omega
    have h2 : (L.drop 1).length ≤ i := by
      simp only [List.length_drop]; omega
    rw [List.getElem?_append_right h2,
      show i - (L.drop 1).length = 0 by simp only [List.length_drop]; omega,
      List.getElem?_take_of_lt (by omega),
      show (i + 1) % L.length = 0 from by
        have hz : i + 1 = L.length := by omega
        rw [hz, Nat.mod_self]]

/-- **HOL `EXISTS_LIST_FACE_NODE_FUNC`**（RXOKSKC.hl:229-:234）。 -/
theorem existsListFaceNodeFunc (H : Hypermap α) (hr : H.IsRestricted) :
    ∃ f : α → List (Set α), ∀ x ∈ H.darts,
      (∀ i < (H.face x).ncard, (f x)[i]? = some (H.node ((H.faceMap ^ i) x))) ∧
      (f x).length = (H.face x).ncard ∧ (f x).Nodup ∧ (f x ≠ []) ∧
      (∀ e ∈ listPairs (f x), ∃ i < (H.face x).ncard,
        e = (H.node ((H.faceMap ^ i) x), H.node ((H.faceMap ^ (i + 1)) x))) := by
  have hex : ∀ x : α, ∃ L : List (Set α), x ∈ H.darts →
      (∀ i < (H.face x).ncard, L[i]? = some (H.node ((H.faceMap ^ i) x))) ∧
      L.length = (H.face x).ncard ∧ L.Nodup := by
    intro x
    by_cases hx : x ∈ H.darts
    · exact ⟨(existsListFaceNode2 H hr hx).choose,
        fun _ => (existsListFaceNode2 H hr hx).choose_spec⟩
    · exact ⟨[], fun h => absurd h hx⟩
  choose f hf using hex
  refine ⟨f, ?_⟩
  intro x hx
  obtain ⟨hEL, hlen, hnod⟩ := hf x hx
  have h3le : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  refine ⟨hEL, hlen, hnod, fun h0 => by rw [h0, List.length_nil] at hlen; omega, ?_⟩
  intro e he
  simp only [listPairs] at he
  obtain ⟨i, hi1, hi2, he1, he2⟩ := mem_zip_ex he
  rw [getElem_rot1 (f x) i hi1, hlen] at he2
  -- he1 : (f x)[i]? = some e.1，he2 : (f x)[(i+1) % C]? = some e.2（?-form 免依赖重写）
  have w1 : e.1 = H.node ((H.faceMap ^ i) x) :=
    Option.some.inj (he1.symm.trans (hEL i (by rw [← hlen]; exact hi1)))
  rcases Nat.lt_or_ge (i + 1) (H.face x).ncard with hlt | hge
  · have w2 : e.2 = H.node ((H.faceMap ^ (i + 1)) x) := by
      rw [Nat.mod_eq_of_lt hlt] at he2
      exact Option.some.inj (he2.symm.trans (hEL (i + 1) (by omega)))
    exact ⟨i, by omega, Prod.ext w1 w2⟩
  · -- i + 1 = C：尾回环 (F^C x = x)
    have hiC : i + 1 = (H.face x).ncard := by omega
    have hmod : (i + 1) % (H.face x).ncard = 0 := by rw [hiC, Nat.mod_self]
    rw [hmod] at he2
    have w2 : e.2 = H.node ((H.faceMap ^ (H.face x).ncard) x) := by
      have h0 : e.2 = H.node x :=
        Option.some.inj (he2.symm.trans (hEL 0 (by omega)))
      rw [h0, H.pow_card_face_apply_self x]
    refine ⟨(H.face x).ncard - 1, by omega, ?_⟩
    have hi' : i = (H.face x).ncard - 1 := by omega
    have hCC : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
    subst hi'
    rw [hCC]
    exact Prod.ext w1 w2

/-! ### §4 站 4 LIST_COR_FACE_SET（RXOKSKC.hl:293-:415）+ LIST_COR_FACE_SET1
（RXOKSKC.hl:418-:468，代表集归纳）

机理（HOL :321-:339）：image ⊆ face_set 时二择一——相等则由 face 在 S
上单射（CARD_IMAGE_EQ_INJ 机理 = InjOn.ncard_image）CARD S = CARD
face_set 反克归纳前件；不等则取新面拉 x₀ ∈ dart 扩集。SET1 以
eq_of_subset_of_ncard_le 收 {face y | y ∈ S} = face_set，覆盖槽由
face x ∈ face_set 自身收（HOL DART_EQ_UNIONS + CARD_SUBSET_EQ 路线的
Lean 短路——并集层留批 67 的 RXOKSKC 大证消费）。 -/

/-- **HOL `LIST_COR_FACE_SET`**（RXOKSKC.hl:293-:296）：n ≤ CARD (face_set H)
⟹ 存在 n 元 dart 代表集，face 在其上单射。 -/
theorem listCorFaceSet (H : Hypermap α) :
    ∀ n : ℕ, n ≤ (H.faceSet).ncard →
      ∃ S : Finset α, (∀ x ∈ S, x ∈ H.darts) ∧
        (∀ x ∈ S, ∀ y ∈ S, H.face x = H.face y → x = y) ∧ S.card = n := by
  intro n
  induction n with
  | zero => intro _; exact ⟨∅, by simp, by simp, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨S, hSd, hSinj, hScard⟩ := ih (by omega)
    have hinj : Set.InjOn (fun y : α => H.face y) (↑S) := hSinj
    have himg_sub : (fun y : α => H.face y) '' (↑S) ⊆ H.faceSet := by
      rintro F ⟨y, hy, rfl⟩
      exact (Hypermap.PermutesOn.mem_iff_orbitMap_mem_setOfOrbits H.faceMap_permutes
        y).mp (hSd y hy)
    by_cases himg : (fun y : α => H.face y) '' (↑S) = H.faceSet
    · exfalso
      have h1 : ((fun y : α => H.face y) '' (↑S)).ncard = S.card := by
        rw [hinj.ncard_image, Set.ncard_coe_finset]
      rw [himg] at h1
      omega
    · have hget : ∃ a ∈ H.faceSet, a ∉ (fun y : α => H.face y) '' (↑S) := by
        by_contra hall
        have hall' : ∀ a : Set α, a ∈ H.faceSet →
            a ∈ (fun y : α => H.face y) '' (↑S) := fun a ha =>
          not_not.mp fun hmem => not_exists.mp hall a ⟨ha, hmem⟩
        exact himg (Set.Subset.antisymm himg_sub hall')
      obtain ⟨a, haF, hane⟩ := hget
      obtain ⟨x₀, hx₀d, hax₀⟩ := haF
      have hface₀ : H.face x₀ = a := hax₀
      have hx₀nS : x₀ ∉ S := fun hmem => hane ⟨x₀, hmem, hface₀⟩
      refine ⟨S ∪ {x₀}, ?_, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · exact hSd z hz
        · rw [Finset.mem_singleton.mp hz]
          exact hx₀d
      · intro z hz w hw hzw
        rcases Finset.mem_union.mp hz with hz | hz
        · rcases Finset.mem_union.mp hw with hw | hw
          · exact hSinj z hz w hw hzw
          · rw [Finset.mem_singleton.mp hw] at hzw
            exact absurd ⟨z, hz, hzw.trans hface₀⟩ hane
        · rcases Finset.mem_union.mp hw with hw | hw
          · rw [Finset.mem_singleton.mp hz] at hzw
            exact absurd ⟨w, hw, (hface₀.symm.trans hzw).symm⟩ hane
          · exact (Finset.mem_singleton.mp hz).trans (Finset.mem_singleton.mp hw).symm
      · rw [Finset.card_union_of_disjoint
          (Finset.disjoint_singleton_right.mpr hx₀nS), Finset.card_singleton, hScard]

/-- **HOL `LIST_COR_FACE_SET1`**（RXOKSKC.hl:418-:424）：满势代表集
（dart 覆盖 + face 单射 + 势 = CARD face_set + 像集 = face_set）。 -/
theorem listCorFaceSet1 (H : Hypermap α) :
    ∃ S : Finset α, (∀ x ∈ S, x ∈ H.darts) ∧
      (∀ x ∈ H.darts, ∃ y ∈ S, x ∈ H.face y) ∧
      (∀ x ∈ S, ∀ y ∈ S, H.face x = H.face y → x = y) ∧
      S.card = (H.faceSet).ncard ∧
      {F | ∃ y ∈ S, F = H.face y} = H.faceSet := by
  obtain ⟨S, hSd, hSinj, hScard⟩ := listCorFaceSet H _ (Nat.le_refl _)
  have hinj : Set.InjOn (fun y : α => H.face y) (↑S) := hSinj
  have himg_sub : (fun y : α => H.face y) '' (↑S) ⊆ H.faceSet := by
    rintro F ⟨y, hy, rfl⟩
    exact (Hypermap.PermutesOn.mem_iff_orbitMap_mem_setOfOrbits H.faceMap_permutes
      y).mp (hSd y hy)
  have himg : (fun y : α => H.face y) '' (↑S) = H.faceSet :=
    Set.eq_of_subset_of_ncard_le himg_sub
      (by rw [hinj.ncard_image, Set.ncard_coe_finset]; exact hScard.ge)
      (setOfOrbits_finite H.darts H.faceMap)
  have himg' : {F | ∃ y ∈ S, F = H.face y} = H.faceSet := by
    ext F
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← himg]
      exact ⟨y, Finset.mem_coe.mpr hy, rfl⟩
    · intro hF
      rw [← himg] at hF
      obtain ⟨y, hy, rfl⟩ := hF
      exact ⟨y, Finset.mem_coe.mp hy, rfl⟩
  refine ⟨S, hSd, ?_, hSinj, hScard, himg'⟩
  intro x hx
  have hmem : H.face x ∈ (fun y : α => H.face y) '' (↑S) := by
    rw [himg]
    exact (Hypermap.PermutesOn.mem_iff_orbitMap_mem_setOfOrbits H.faceMap_permutes
      x).mp hx
  simp only [Set.mem_image] at hmem
  obtain ⟨y, hyS, hfy⟩ := hmem
  refine ⟨y, Finset.mem_coe.mp hyS, ?_⟩
  rw [hfy]
  exact H.mem_face_self x

/-! ### §5 站 5 ONE_TO_ONE_DART（RXOKSKC.hl:474-:492）

机理（HOL :477-:492 is_no_double_joins 槽）：node x = node y 给
y ∈ node x；node (F x) = node (F y) 经 node_node_map_eq（Auqtzyz 拓扑
边，在册 TameList60:448）+ plain edge_map 恒等式给 edge y ∈
node (edge x)——noDoubleJoins 直接钉 x = y。 -/

/-- **HOL `ONE_TO_ONE_DART`**（RXOKSKC.hl:474-:476）：受限 H 中节点对
相等的两 dart 相等。 -/
theorem oneToOneDart (H : Hypermap α) (hr : H.IsRestricted) {x y : α}
    (hx : x ∈ H.darts) (_hy : y ∈ H.darts)
    (h1 : H.node x = H.node y) (h2 : H.node (H.faceMap x) = H.node (H.faceMap y)) :
    x = y := by
  refine hr.noDoubleJoins x y hx ?_ ?_
  · rw [h1]; exact H.mem_node_self y
  · have e1 : H.edgeMap y = H.nodeMap (H.faceMap y) := edgeMap_apply H hr.plain y
    have e2 : H.edgeMap x = H.nodeMap (H.faceMap x) := edgeMap_apply H hr.plain x
    rw [e1, e2, nodeNodeMapEq H (H.faceMap x)]
    have m : H.nodeMap (H.faceMap y) ∈ H.node (H.nodeMap (H.faceMap y)) :=
      H.mem_node_self _
    rw [nodeNodeMapEq H (H.faceMap y), ← h2] at m
    exact m

/-! ### §6 批 67 接续底座：RXOKSKC.hl:523 站 6 消费件的泛型 def 层

HOL list_hypermap-compiled.hl:47-65 的泛型 α 定义层（具象 fgraph ℕ 层
= Kepler.Assembly.GoodListDefs:44-66 + TameLp hypermapOfList，泛型层本批
首落）。批 67 在其上补 bijOn 群（findFace congruence / fList_mem_darts /
nList_fList / prev-next 逆，TameLp:3900-4035 机理泛型化）+ hypermapOfListG
构造 + RXOKSKC 大证。 -/

/-- HOL `e_list`（list_hypermap-compiled.hl:55，泛型 α 层；Assembly.eList
为 ℕ × ℕ 专件）。 -/
def rxESwap (d : α × α) : α × α := (d.2, d.1)

/-- HOL `find_face`（list_hypermap-compiled.hl:53 经 find_list）：`L` 中
第一个以 `d` 为 dart 的面（list_pairs 含 d）的 dart 列表；无则 `[]`。 -/
def rxFindFace (L : List (List α)) (d : α × α) : List (α × α) :=
  listPairs ((L.find? fun l => decide (d ∈ listPairs l)).getD [])

/-- HOL `f_list`（list_hypermap-compiled.hl:54）。 -/
def rxFList (L : List (List α)) (d : α × α) : α × α :=
  nextEl (rxFindFace L d) d

/-- HOL `n_list`（list_hypermap-compiled.hl:56）。 -/
def rxNList (L : List (List α)) (d : α × α) : α × α :=
  rxESwap (prevEl (rxFindFace L d) d)

/-- HOL `good_list`（tame_defs2.hl:31-36 = list_hypermap-compiled.hl:63，
泛型 α 层；Assembly.GoodList 为 fgraph ℕ 专件）。 -/
def rxGoodList (L : List (List α)) : Prop :=
  (rxListOfDarts L).Nodup ∧ (∀ l ∈ L, l ≠ []) ∧
    ∀ d ∈ rxListOfDarts L, (d.2, d.1) ∈ rxListOfDarts L

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针已执行，快照 t66_axiom_audit.log 全文）：
本件公开件 6 探针——rxUniqListOfDarts = [propext, Quot.sound]（prop 件
无 choice）；existsListFaceNode / existsListFaceNodeFunc / listCorFaceSet /
listCorFaceSet1 / oneToOneDart = [propext, Classical.choice, Quot.sound]
标准三内——全件零 sorryAx。def 层 5 枚（rxESwap / rxFindFace / rxFList /
rxNList / rxGoodList）为 def 不携公理；private 桥件（edgeMap_apply）经
oneToOneDart 传递消费。
#print axioms Kepler.Text.TameSpine.oneToOneDart
-/
