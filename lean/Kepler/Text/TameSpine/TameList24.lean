/-
  Kepler.Text.TameSpine.TameList24 — B1 Tame_list 地基批 24：Seed 章收尾
  （tamespine-port-plan §4 批次表 B1 行；接续批 23 = TameList22→TameList23.lean，
  批 23 终点 = HOL :10707（list_of_elements_seed 已落，:10709 起留本批）；
  本批起点 = HOL :10709）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:10709-:10794）——Seed 章收尾五件全量：

  `good_vertices_set2_seed` :10709-:10718
  `!p. vertices_set2 (Seed p) = elements_of_list (fgraph (Seed p))`；
  `all_uniq_seed` :10720-:10730
  `!p. all uniq (fgraph (Seed p))`；
  `good_facesAt_seed` :10732-:10750
  `!p. !v. v IN vertices_set2 (Seed p) ==> facesAt (Seed p) v =
    FILTER (\f. MEM v (FST f)) (faces (Seed p))`；
  `uniq_inj_on` :10752-:10783（大件）
  `!u v. sizel u = sizel v /\ uniq u /\ uniq v ==> ?(f:A->B).
    inj_on f (set_of_list u) /\ v = MAP f u`；
  `elements_of_list_pr` :10785-:10794
  `!u. elements_of_list [u;rev u] = set_of_list u`。
  :10796 起 dih2k 章（:10812 有同名 `fgraph_seed` 再证，dih2k_list 展开面）
  自然边界收批，不在本批射程。

  载体定名侦察定论（本批新核，任务面 vertices_set2 双载体裁定）：
  · `vertices_set2`（tame_defs.hl:392 `set_of_list (vertices_graph g)`）
    双载体侦察：批 2 `verticesGraphAlt`（TameList2.lean:121，AFP Graph
    `(Graph.mk fs n f h).vertices = List.range n` 投影面，rfl）与 GoodGraph
    AFP 面 `verticesSet2`（GoodGraph.lean:59 `{v | v ∈ g.vertices}`，
    `Set ℕ`）。裁定：**语句载体取 GoodGraph.verticesSet2**（六合取
    VerticesSet2EqSpine（GoodGraph.lean:117）同槽的现成载体，集合等式
    陈述逐字镜像 HOL EXTENSION 面；批 2 verticesGraphAlt/graphAlt 作
    证明内展开机器）。两载体相容：`verticesSet2` 体内 `g.vertices` 即
    批 2 投影面的左端（Graph.lean:98
    `Graph.vertices g = List.range g.countVertices`）。
  · `elements_of_list`（list_hypermap-compiled.hl:29 集合形）↦
    `TameLp.elementsOfList`（TameLp.lean:4071 `{x | x ∈ listOfElements L}`，
    与 GoodGraph VerticesSet2EqSpine 同载体）——与批 23 的列表形
    `listOfElements`（flatten.eraseDups，:4069）为 set-of 同源两形，
    成员谓词经 `Set.mem_setOf` 互换。
  · `facesAt`（tame_defs.hl:399 `EL v (faceListAt g)`）↦
    `Graph.facesAt`（Graph.lean:103 `faceListAt.getD v []`，越界
    Isabelle undefined ↦ getD [] 约定在案）；`FACE_LIST_AT`（:138）↦
    批 2 `faceListAtGraph` 投影面；FILTER 形恰为 GoodGraph.facesAtV2
    （GoodGraph.lean:66，tame_defs2.hl:31 载体）的定义体——本件即
    Seed 上 facesAt = facesAt_v2 的逐点等式强化（GoodFacesV3Spine 的
    Perm 陈述在 Seed 退化为 Perm.refl 可达）。
  · `uniq` ↦ `List.Nodup`；`sizel` ↦ `List.length`；`MAP` ↦
    `List.map f u`（**泛型 α β 异宇宙下 `f <$> u` 不可用**——Functor.map
    的函数域/值域同宇宙约束 `{α β : Type u}`，`Type*` 两参不同宇宙时
    `List ?u_1 ?m ≟ List β` 合一失败即语句行 elaboration error，本批
    新雷区）；`inj_on f (set_of_list u)` ↦
    `Set.InjOn f {x | x ∈ u}`（批 11 setOfListSpine `{x | x ∈ r}` 同体
    泛型化；批 4 InjOn 载体先例）。

  层级侦察定论（全量形记档，本批新核）：
  · :10709 证明体（:10712-:10718）EXTENSION + IN_SET_OF_LIST 后成员面
    `MESON_TAC[Seq.mem_rev;REVERSE_rev]`：两侧成员各一步化到
    `x < maxGon p`——左侧经 verticesSet2→Graph.vertices→range
    （countVertices 投影 rfl 面 = 批 2 verticesGraphAlt）；右侧经批 23
    listOfElementsSeed（成员形）+ List.mem_reverse，收口零 Meson。
  · :10720 证明体 fgraph_graph/MAP/Seq.all/rev_uniq/iota_uniq 的 Lean 面：
    `fgraphSeed p` 两元素列表逐元素 `List.nodup_range` /
    `List.nodup_reverse`（批 21 已用面）直拼。
  · :10732 证明体 facesAt/FACE_LIST_AT/upt0/Seq.mem_iota/EL_REPLICATE/
    Seq.all_filterP/filter_FILTER 面：EL_REPLICATE ↦ 批 2 `elReplicate`
    （TameList2.lean:962，getD 形在案，门槛 `v < maxGon p` 由成员面供入）；
    filter 全过支（REPLICATE 逐点 MEM v (FST f) 由 mem_iota 两面同为
    `v < maxGon p`）↦ `List.filter_eq_self`；`0 + n = n /\ 0 <= n`
    算术支在 range 成员形下解散。
  · :10752 uniq_inj_on（大件）Lean 面重构造（HOL 证体 indexl/index_el/
    index_uniq 链 ↦ Mathlib idxOf 家族：`List.idxOf_lt_length_iff` +
    `List.getElem?_idxOf` + `List.get_idxOf`（nodup 面 = HOL index_uniq
    载体形，用于 MAP 支逐点）+ `List.Nodup.getElem_inj_iff`（iff .mp 形）
    + `List.ext_getElem?'`）。语句形诚实记账：HOL `?(f:A->B)` 中 A、B
    为 HOL 类型（恒非空），Lean 载体需 junk 值填 `x ∉ u` 支——取
    `[Nonempty β]` + `Classical.arbitrary β`（批 4 existsInverseOfInjOn
    的 `else 0` junk 先例的 Nonempty 泛型化）；junk 支不可达（InjOn 只
    约束 `x ∈ u`、MAP 等式只消费成员值）。sizel 前提用于 idx 界
    `u.idxOf x < u.length = v.length` 的换算。
  · :10785 elements_of_list_pr（set 面，轻）：`ext` 后成员链
    flatten_cons/flatten_nil/append_nil（批 23 同款 simp 集）+
    mem_eraseDups + mem_append + mem_reverse 两步 or 幂等收口
    （HOL SET_OF_LIST_APPEND/set_of_list_rev/UNION_IDEMPOT 合一面）。

  依赖面（全为在案真件，零新增债）：批 2 `graphAlt`/`verticesGraphAlt`
  （rfl 投影面）/`elReplicate` + 批 21 `fgraphSeed` + 批 23
  `listOfElementsSeed` + GoodGraph `verticesSet2`/`facesAtV2`（def 层）+
  TameLp `elementsOfList`/`listOfElements` + Mathlib List.mem_range/
  nodup_range/nodup_reverse/filter_eq_self/mem_append/mem_reverse/
  mem_eraseDups/flatten_cons/flatten_nil/append_nil/ext_getElem?'/
  getElem_map/idxOf_lt_length_iff/getElem?_eq_getElem/idxOf_inj/
  get_idxOf/Nodup.getElem_inj_iff。import 边：本模块新增
  `import …GoodGraph`（verticesSet2 载体）；GoodGraph 只依赖
  Keystone/Assembly/TameLp，无环。

  诚实记账：本批五件全部真证，零新增记账债（零止损件）。uniq_inj_on
  语句形的 Nonempty β 记账见上（唯一选择点）；其余四面均为载体
  定义方程直译。公理审计实测（#print axioms，2026-10-19，隔离 clone
  /tmp/p4t21）：goodVerticesSet2Seed 仅 [propext, Quot.sound]，
  allUniqSeed/goodFacesAtSeed/uniqInjOn 标准三
  [propext, Classical.choice, Quot.sound]，elementsOfListPr 仅
  [propext, Quot.sound]——零 sorryAx、零记账传入（审计锚见文末注释块）。

  本批新雷区三条入册（uniq_inj_on 大件证体迭代实录）：
  ① 泛型异宇宙 `<$>` 不可用（见上载体折算条）——HOL `MAP f u` 泛型
  载体一律 `List.map f u`。
  ② 证人函数 hoist 须 tactic `let`（zeta 可穿透，`dif_pos` 能打穿
  `fwit x`）；`have` 绑定不透明，`dif_pos`/`rfl` 全部打不开。且
  lambda/let 内 getElem 界证明引用外部假设（`hlen.le`）时，lambda 体内
  固化了 v.length 出现点，外部再 `rw [等式] at` 涉该 lambda 的项会
  motive 不型正（本批 `rw [hmeq] at hn` 实败例）——hoist 后 rw 目标
  （`(List.map fwit u).length`）不含 lambda 体即无毒。
  ③ `rw [idx 等式]` 于 `u[u.idxOf x]'hibx` 形目标（getElem 证明参数
  依赖被重写项）motive 不型正——按官方报错提示改 `simp only`（可处理
  proof-dependent 重写），或本批终选 `List.idxOf_inj` 直接免重写收口；
  `congrArg (fun k => v[k]'hn1) h` 同型陷阱（k 泛化后 hn1 类型不匹配）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 25 接续点：HOL :10796 `iso_list_imp_dih2k` 起 dih2k 章
  （`iso_list (L,[]) (L',[]) /\ dih2k_list L ==> dih2k_list L'`，
  dih2k_list/iso_list 展开面；章内 :10812 有同名 `fgraph_seed` 再证
  不重落）。
-/

import Kepler.Text.TameSpine.TameList23
import Kepler.Text.TameSpine.GoodGraph

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph Seed maxGon Vertex)
open Kepler.Text.TameLp (listOfElements elementsOfList)

/-! ### §1 good_vertices_set2_seed（tame_list.hl:10709-:10718） -/

/-- **HOL `good_vertices_set2_seed`**（tame_list.hl:10709-:10718）
`!p. vertices_set2 (Seed p) = elements_of_list (fgraph (Seed p))`——
语句载体 = GoodGraph.verticesSet2（双载体裁定见头部）；EXTENSION 后
两侧成员各一步化 `x < maxGon p`：左经 Graph.vertices = range
countVertices（批 2 verticesGraphAlt 投影面），右经批 23
listOfElementsSeed + List.mem_reverse（HOL Seq.mem_rev + REVERSE_rev 面），
零 Meson。 -/
theorem goodVerticesSet2Seed (p : ℕ) :
    verticesSet2 (Seed p) = elementsOfList (facesVertexLists (Seed p)) := by
  ext x
  have key : x ∈ (List.range (p + 3)).reverse ↔
      x ∈ listOfElements (facesVertexLists (Seed p)) := (listOfElementsSeed p x).symm
  constructor
  · intro h
    have hx : x < maxGon p := List.mem_range.mp h
    exact key.mp (List.mem_reverse.mpr (List.mem_range.mpr hx))
  · intro h
    have hx : x < p + 3 := List.mem_range.mp (List.mem_reverse.mp (key.mpr h))
    exact List.mem_range.mpr hx

/-! ### §2 all_uniq_seed（tame_list.hl:10720-:10730） -/

/-- **HOL `all_uniq_seed`**（tame_list.hl:10720-:10730）
`!p. all uniq (fgraph (Seed p))`——语句形 = GoodGraph AllUniqSpine 体
（`∀ l ∈ g.fgraph, l.Nodup`）；HOL 证体 Seq.all/rev_uniq/iota_uniq 链
在 Lean 面为 fgraphSeed 两元素列表逐元素 nodup_range / nodup_reverse
直拼（批 21 已用面）。 -/
theorem allUniqSeed (p : ℕ) : ∀ l ∈ facesVertexLists (Seed p), l.Nodup := by
  rw [fgraphSeed p]
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact List.nodup_range
  · exact List.nodup_reverse.mpr List.nodup_range

/-! ### §3 good_facesAt_seed（tame_list.hl:10732-:10750） -/

/-- **HOL `good_facesAt_seed`**（tame_list.hl:10732-:10750）
`!p. !v. v IN vertices_set2 (Seed p) ==> facesAt (Seed p) v =
FILTER (\f. MEM v (FST f)) (faces (Seed p))`——facesAt ↦
`Graph.facesAt`（getD 形），FILTER 形即 GoodGraph.facesAtV2 定义体
（Seed 上 facesAt = facesAt_v2 逐点等式，GoodFacesV3Spine Perm 陈述的
强化点）。HOL 证体 EL_REPLICATE（↦ 批 2 elReplicate）+ filter 全过支
（↦ `List.filter_eq_self`，REPLICATE 逐点 MEM v (FST f) 由 mem_iota
两面同为 `v < maxGon p`）。 -/
theorem goodFacesAtSeed (p : ℕ) :
    ∀ v ∈ verticesSet2 (Seed p),
      (Seed p).facesAt v = (Seed p).faces.filter (fun f => v ∈ f.vertices) := by
  intro v hv
  have hx : v < maxGon p := List.mem_range.mp hv
  have hl : (Seed p).facesAt v =
      [Kepler.Graphs.Face.mk (List.range (maxGon p)) true,
        Kepler.Graphs.Face.mk (List.range (maxGon p)).reverse false] :=
    elReplicate hx
  have hr : (Seed p).faces =
      [Kepler.Graphs.Face.mk (List.range (maxGon p)) true,
        Kepler.Graphs.Face.mk (List.range (maxGon p)).reverse false] :=
    rfl
  rw [hl, hr]
  refine (List.filter_eq_self.mpr ?_).symm
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact decide_eq_true (List.mem_range.mpr hx)
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact decide_eq_true (List.mem_reverse.mpr (List.mem_range.mpr hx))
    · nomatch hf

/-! ### §4 uniq_inj_on（tame_list.hl:10752-:10783） -/

/-- **HOL `uniq_inj_on`**（tame_list.hl:10752-:10783）
`!u v. sizel u = sizel v /\ uniq u /\ uniq v ==> ?(f:A->B).
inj_on f (set_of_list u) /\ v = MAP f u`——HOL 证体 indexl/index_el/
index_uniq 链的 Lean 面一步化为 idxOf 家族：证人（`let fwit`，zeta 可
穿透——`have` 不透明，`dif_pos` 打不开，本批新雷区②）`f x =
v[u.idxOf x]`（x ∈ u 支，界 `u.idxOf x < v.length` 经
`List.idxOf_lt_length_iff` + sizel 前提换算 `Nat.lt_of_lt_of_le …
hlen.le`）。inj_on 支：`dif_pos` 两支剥壳 + v-nodup
`List.Nodup.getElem_inj_iff`（iff .mp 形，雷区 3）得 idx 相等，终经
`List.idxOf_inj` 免重写收 x = y（绕开雷区③ rw-motive 陷阱）；MAP 支经
`List.ext_getElem?'` 逐点 `List.getElem_map` + `List.get_idxOf`
（nodup 面 = HOL index_uniq 载体形）+ `simp only` 剥索引相等。
诚实记账：HOL 类型恒非空，Lean junk 支（x ∉ u）取
`Classical.arbitrary β`（`[Nonempty β]`，批 4 existsInverseOfInjOn
junk 先例的泛型化），支不可达。MAP 陈述载体 `List.map f u`（异宇宙
雷区①）。 -/
theorem uniqInjOn {α β : Type*} [BEq α] [LawfulBEq α] [Nonempty β]
    {u : List α} {v : List β} (hlen : u.length = v.length)
    (hu : u.Nodup) (hv : v.Nodup) :
    ∃ f : α → β, Set.InjOn f {x | x ∈ u} ∧ v = List.map f u := by
  classical
  let fwit : α → β := fun x => if h : x ∈ u then
    v[u.idxOf x]'(Nat.lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr h) hlen.le)
    else Classical.arbitrary β
  refine ⟨fwit, ?_, ?_⟩
  · intro x hx y hy hxy
    have h1 : fwit x = v[u.idxOf x]'(Nat.lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hx) hlen.le) :=
      dif_pos (show x ∈ u from hx)
    have h2 : fwit y = v[u.idxOf y]'(Nat.lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hy) hlen.le) :=
      dif_pos (show y ∈ u from hy)
    rw [h1, h2] at hxy
    exact (List.idxOf_inj hx).mp
      ((List.Nodup.getElem_inj_iff hv).mp hxy)
  · have h1 : ∀ (z : α) (hz : z ∈ u),
        fwit z = v[u.idxOf z]'(Nat.lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hz) hlen.le) :=
      fun z hz => dif_pos hz
    have hmeq : v.length = (List.map fwit u).length := by
      rw [List.length_map]; exact hlen.symm
    refine List.ext_getElem?' (fun n hn => ?_)
    rw [hmeq] at hn
    rw [Nat.max_self] at hn
    have hn2 : n < (List.map fwit u).length := hn
    have hn1 : n < v.length := hmeq.symm ▸ hn
    have hnu : n < u.length := Nat.lt_of_lt_of_le hn1 hlen.symm.le
    have hum : u[n]'hnu ∈ u := List.getElem_mem _
    rw [List.getElem?_eq_getElem hn1, List.getElem?_eq_getElem hn2, List.getElem_map,
      h1 (u[n]'hnu) hum]
    have hidxn : u.idxOf (u[n]'hnu) = n := List.get_idxOf hu ⟨n, hnu⟩
    simp only [hidxn]

/-! ### §5 elements_of_list_pr（tame_list.hl:10785-:10794） -/

/-- **HOL `elements_of_list_pr`**（tame_list.hl:10785-:10794）
`!u. elements_of_list [u;rev u] = set_of_list u`——set 面：`ext` 后成员链
flatten_cons/flatten_nil/append_nil（批 23 同款 simp 集）+ mem_eraseDups
+ mem_append + mem_reverse 两步 or 幂等收口（HOL
SET_OF_LIST_APPEND/set_of_list_rev/UNION_IDEMPOT 合一面）。 -/
theorem elementsOfListPr (u : List ℕ) :
    elementsOfList [u, u.reverse] = {x | x ∈ u} := by
  ext x
  show x ∈ ([u, u.reverse].flatten).eraseDups ↔ x ∈ u
  simp only [List.mem_eraseDups, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.mem_append, List.mem_reverse]
  exact ⟨fun h => h.elim id id, Or.inl⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.goodVerticesSet2Seed
#print axioms Kepler.Text.TameSpine.allUniqSeed
#print axioms Kepler.Text.TameSpine.goodFacesAtSeed
#print axioms Kepler.Text.TameSpine.uniqInjOn
#print axioms Kepler.Text.TameSpine.elementsOfListPr
-/
