/-
  Kepler.Text.TameSpine.TameList43 — B1 Tame_list 地基批 43：final_list
  运输章（tamespine-port-plan §4 批次表 B1 行；接续批 42 =
  TameList42.lean，批 42 终点 = HOL :12406；本批起点 = HOL :12408
  `iso_list_final_list`。行号均按主仓 reference/flyspeck（commit
  1ce0353）实测。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:12408-:12516）：

  主件一：`iso_list_final_list` :12408-:12447
  `!L L' N N' r r'. iso_list (L,(r::N)) (L',(r'::N')) /\ MEM r N /\
  good_list L /\ normal_list L N /\ final_list L r ==> final_list L' r'`
  ↦ `isoListFinalListSpine`（真证）。HOL 证体 final_list 展开（Seq.allP
  点式化）+ iso_list 展开 CONS_11 拆条（r' = MAP nphi r）+ MEM_MAP 取
  证人 x ∈ r（d' = nphi x）+ f_list_map（:3840）正面 + next_el_MEM_map
  （:1011）+ inj_on_dart_of_list（:3746）供 r 上点式单射（darts 槽经
  normal_list_list_of_darts 折算）逐槽收口；Lean 面 d ∈ r' 逐点化
  （List.mem_map 拆 x ∈ r ∧ nphi x = d）+ fList 槽
  la7_hypermapOfList_map 第 2 合取直投（hL'eq 换装）+ nextEl 槽
  la7_nextEl_map（r 上点式单射由 injOnDartOfList +
  normalListListOfDarts 组装）+ hfinal 逐点回喂 rfl 收口。

  主件二：`iso_list_sym_normal_cat` :12449-:12477
  `!L N L' N' n n'. normal_list L N /\ set_of_list (flatten n) SUBSET
  set_of_list (flatten N) /\ iso_list (L,cat n N) (L',cat n' N') ==>
  iso_list (L',cat n' N') (L,cat n N)`
  ↦ `isoListSymNormalCat`（真证）。HOL 证体 iso_list_sym（:3328）直
  MATCH，两组 SUBSET 前提 ENOUGH_TO_SHOW 化归 `set_of_list (MAP FST/SND
  (flatten N)) SUBSET elements_of_list L`（SUBSET 假设把 n 段并入 N 段
  + normal_list_list_of_darts + mem_list_of_darts_imp_mem_list_of_
  elements_alt 逐点）后 MESON 收口；Lean 面同链——批 4
  isoListSpineSym 直投，两 elements 槽 = 批 5 isoListSpineSymNormal
  同款 memDartsImpMemElements 组装（(n ++ N).flatten 逐点 mem_flatten
  + mem_append 分段，n 段经 hsub 并入 N 段）。

  主件三：`iso_list_final_list_eq` :12479-:12516
  `!L L' N N' r r'. iso_list (L,(r::N)) (L',(r'::N')) /\ MEM r N /\
  good_list L /\ normal_list L N ==> (final_list L' r' <=> final_list
  L r)`
  ↦ `isoListFinalListEqSpine`（真证）。HOL 证体 EQ_EXPAND 双向：⇐ 向
  iso_list_final_list 正向实例直投；⇒ 向反向实例三槽预件——
  iso_list (L',(r'::N')) (L,(r::N)) 槽经 GSYM cat1s（cat [r] N 换装）
  MATCH iso_list_sym_normal_cat（n := [r] 段 SUBSET 槽 flatten 单点
  并入 flatten N）、MEM r' N' 槽经 N 侧方程 CONS_11 拆条 + MEMf_MAP
  （:157）、normal_list L' N' 槽经 iso_list_cons（:11737）+
  iso_list_normal（:4166）链收口；Lean 面 cat [r] N 槽按批 35 cat↦++
  惯例载 `[r] ++ N`（cons_append 定义式同体，免显式 cat1s 镜像件），
  normal_list L' N' 槽 = isoListCons hiso + isoListNormal 一步，MEM
  r' N' 槽 = List.map_cons + injection 双层拆条 + memfMap。

  载体折算盘点（批 42 头注预记侦察面，经全库 grep（含 LocalAuto 族）
  对拍——零撞车）：
  - `next_el_MEM_map`（tame_list.hl:1011-:1044）= TameLp
    `la7_nextEl_map`（TameLp.lean:4376；批 2/11 记账）。诚实记账：
    Lean 面免 HOL `uniq y` 前提（la7_nextEl_map 只需点式单射 + MEM，
    单射槽已含 uniq 信息——HOL 证体 normal_list_uniq_nonnil 的 uniq
    槽 Lean 侧零消费，批 6 normalListUniqNonnil 本批免引）；
  - `f_list_map`（tame_list.hl:3840-:3860）= TameLp
    `la7_hypermapOfList_map`（TameLp.lean:4870）第 2 合取 fList 槽
    （good_list L 槽 = hgood 显式参、inj_on 槽 = flatten 点式形经批 1
    injOn_elementsOfList_iff 桥、MEM x (list_of_darts L) 槽逐字同形；
    批 37 头注预记载体链本批兑现）；
  - `inj_on_dart_of_list`（tame_list.hl:3746）= 批 5 injOnDartOfList
    （点式本体 = 批 2 injOnLiftListOfDarts）；
  - `normal_list_list_of_darts`（tame_list.hl:3643）= 批 5
    normalListListOfDarts；
  - `mem_list_of_darts_imp_mem_list_of_elements_alt`（tame_list.hl:1082）
    = 批 2 memDartsImpMemElements；
  - `iso_list_sym`（tame_list.hl:3328）= 批 4 isoListSpineSym；
  - `iso_list_sym_normal`（tame_list.hl:3673）= 批 5
    isoListSpineSymNormal（先例同款两槽组装）；
  - `iso_list_nilfamily`（tame_list.hl:11684）/`iso_list_cons`
   （:11737）= 批 36 isoListNilFamily/isoListCons（本批主件三消费
    isoListCons 面）；
  - `iso_list_good_list`（tame_list.hl:3554）= 批 1
    isoListSpine_goodList（经 isoListNormal 内部消费）；
    `iso_list_normal`（tame_list.hl:4166）= 批 5 isoListNormal；
  - `MEMf_MAP`（tame_list.hl:157）= 批 2 memfMap；
  - `Seq.cat` 换装 = `++`（批 35 惯例；`Seq.cat1s` 槽 `[r] ++ N` 经
    cons_append 与 `r :: N` 定义式同体，本批免显式 cat1s 镜像件）；
    `Seq.flatten_cat` = core `List.flatten_append`；`upper_case`/
    `lower_case`（tame_list.hl:1397-:1401）= HOL Seq→List 换装包零
    折算负担；`final_list`（tame_defs2.hl:126）= 批 7
    finalListSpine（结论槽 `all ...` ↦ `∀ d ∈ r'` 定义式展开）。
  全库无 final_list 运输现成载体（批 42 isoListAllSizeSpine 系 size
  面、批 17 hyp 系 final_list 判消非运输）——本批主件一即镜像本体。

  新落地载体：零（纯消费批）。私件：零。

  诚实记账：主件三件全真证，零新 def、零 sorry、零止损件、零记账债。
  hsub（set_of_list SUBSET 槽）按 isoListSpineSym 先例逐点 ∈ 形平铺
  （批 5 头注同款记账）。红线遵守：零既有文件触碰、零 git 写操作。
  批 44 接续点：HOL :12518 `find_list_map`（find_list 章——
  `!f r d. uniq (flatten r) /\ MEM d (flatten r) /\ (!x y. MEM x
  (flatten r) /\ MEM y (flatten r) /\ f x = f y ==> x = y) ==>
  find_list (MAP (MAP f) r) (f d) = MAP f (find_list r d)`；侦察面
  findListSpine（批 7）在册，find_list_uniq（:5731）等 find_list 章
  载体待对拍）→ 其后 :12546 `marked_list_x_last`。
-/

import Kepler.Text.TameSpine.TameList42

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (elementsOfList)

/-! ### §1 iso_list_final_list（tame_list.hl:12408-:12447） -/

/-- **HOL `iso_list_final_list`**（tame_list.hl:12408-:12447）
`iso_list (L,(r::N)) (L',(r'::N')) /\ MEM r N /\ good_list L /\
normal_list L N /\ final_list L r ==> final_list L' r'`——final_list
沿 iso 运输：d ∈ r' 逐点化出证人 x ∈ r（d = nphi x），fList 槽
f_list_map（= la7_hypermapOfList_map 第 2 合取）正面、nextEl 槽
next_el_MEM_map（= la7_nextEl_map，r 上点式单射由 inj_on_dart_of_list
+ normal_list_list_of_darts 组装），末槽 hfinal 逐点回喂。 -/
theorem isoListFinalListSpine {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} {r r' : List (ℕ × ℕ)}
    (hiso : IsoListSpine L L' (r :: N) (r' :: N'))
    (hN : NormalListSpine hL N) (hr : r ∈ N) (hfinal : finalListSpine L r) :
    finalListSpine L' r' := by
  intro d hd
  obtain ⟨phi, hinj, hL'eq, hN'eq⟩ := hiso
  -- N 侧方程 CONS_11 拆条（雷 #36 injection 双层：头槽 r'、尾槽 N'）
  have hEq : r' :: N' = (r :: N).map (fun s => s.map (fun u => (phi u.1, phi u.2))) := hN'eq
  simp only [List.map_cons] at hEq
  injection hEq with hhead _
  rw [hhead] at hd
  -- 证人：d = nphi x，x ∈ r（HOL MEM_MAP 槽）
  obtain ⟨x, hx, hdx⟩ := List.mem_map.mp hd
  subst hdx
  -- r 上点式单射（HOL inj_on_dart_of_list 槽，darts 成员经
  -- normal_list_list_of_darts + MEM r N 的 flatten 折算）
  have hmemDarts : ∀ u ∈ r, u ∈ listOfDarts L := fun u hu =>
    normalListListOfDarts hN u (List.mem_flatten.mpr ⟨r, hr, hu⟩)
  have hinjR : ∀ u ∈ r, ∀ v ∈ r,
      (phi u.1, phi u.2) = (phi v.1, phi v.2) → u = v := fun u hu v hv huv =>
    injOnDartOfList L hinj (hmemDarts u hu) (hmemDarts v hv) huv
  -- f_list_map 面（la7_hypermapOfList_map 第 2 合取）
  have hinjFlatten : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, phi u = phi v → u = v :=
    injOn_elementsOfList_iff.mp hinj
  have hxF := (Kepler.Text.TameLp.la7_hypermapOfList_map L hinjFlatten hL).2 x (hmemDarts x hx)
  rw [hhead, hL'eq, hxF.2.1,
    Kepler.Text.TameLp.la7_nextEl_map (f := fun u : ℕ × ℕ => (phi u.1, phi u.2)) hinjR hx,
    hfinal x hx]

/-! ### §2 iso_list_sym_normal_cat（tame_list.hl:12449-:12477） -/

/-- **HOL `iso_list_sym_normal_cat`**（tame_list.hl:12449-:12477）
`normal_list L N /\ set_of_list (flatten n) SUBSET set_of_list
(flatten N) /\ iso_list (L,cat n N) (L',cat n' N') ==> iso_list
(L',cat n' N') (L,cat n N)`——iso 对称的 cat 分段版：批 4
isoListSpineSym 直投，两 elements 槽由 (n ++ N).flatten 逐点化
（mem_flatten + mem_append 分段；n 段经 SUBSET 前提并入 N 段）+
normal_list_list_of_darts + memDartsImpMemElements 组装（批 5
isoListSpineSymNormal 同款）。SUBSET 前提按 isoListSpineSym 先例
逐点 ∈ 形平铺；`cat n N` 按批 35 惯例载 `n ++ N`。 -/
theorem isoListSymNormalCat {L L' : fgraph ℕ} {hL : GoodList L}
    {N n N' n' : List (List (ℕ × ℕ))}
    (hN : NormalListSpine hL N) (hsub : ∀ d ∈ n.flatten, d ∈ N.flatten)
    (hiso : IsoListSpine L L' (n ++ N) (n' ++ N')) :
    IsoListSpine L' L (n' ++ N') (n ++ N) := by
  have hmemDarts : ∀ d ∈ (n ++ N).flatten, d ∈ listOfDarts L := by
    intro d hd
    obtain ⟨s, hs, hds⟩ := List.mem_flatten.mp hd
    rcases List.mem_append.mp hs with hs' | hs'
    · exact normalListListOfDarts hN d (hsub d (List.mem_flatten.mpr ⟨s, hs', hds⟩))
    · exact normalListListOfDarts hN d (List.mem_flatten.mpr ⟨s, hs', hds⟩)
  refine isoListSpineSym hiso (fun p hp => ?_) (fun p hp => ?_)
  · exact (memDartsImpMemElements L (hmemDarts p hp)).1
  · exact (memDartsImpMemElements L (hmemDarts p hp)).2

/-! ### §3 iso_list_final_list_eq（tame_list.hl:12479-:12516） -/

/-- **HOL `iso_list_final_list_eq`**（tame_list.hl:12479-:12516）
`iso_list (L,(r::N)) (L',(r'::N')) /\ MEM r N /\ good_list L /\
normal_list L N ==> (final_list L' r' <=> final_list L r)`——双向：
⇐ 向 iso_list_final_list 正向实例直投；⇒ 向反向实例，三槽预件
iso_list (L',(r'::N')) (L,(r::N))（isoListSymNormalCat，n := [r] 段）
+ MEM r' N'（List.map_cons + injection 拆条 + memfMap）+
normal_list L' N'（isoListCons + isoListNormal）。 -/
theorem isoListFinalListEqSpine {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} {r r' : List (ℕ × ℕ)}
    (hiso : IsoListSpine L L' (r :: N) (r' :: N'))
    (hN : NormalListSpine hL N) (hr : r ∈ N) :
    (finalListSpine L' r' ↔ finalListSpine L r) := by
  obtain ⟨phi, hinj, hL'eq, hN'eq⟩ := hiso
  -- N 侧方程 CONS_11 拆条：头槽 r' = r.map nphi、尾槽 N' = N.map nphi
  have hEq : r' :: N' = (r :: N).map (fun s => s.map (fun u => (phi u.1, phi u.2))) := hN'eq
  simp only [List.map_cons] at hEq
  injection hEq with hhead htail
  have hiso' : IsoListSpine L L' (r :: N) (r' :: N') := ⟨phi, hinj, hL'eq, hN'eq⟩
  have hcons' : IsoListSpine L L' N N' := isoListCons hiso'
  -- MEM r' N' 槽（HOL MEMf_MAP 槽）
  have hr' : r' ∈ N' := by
    rw [hhead, htail]
    exact memfMap hr
  constructor
  · -- ⇒ 向：iso_list_final_list 反向实例（HOL INTRO_TAC 换位）
    intro hfin
    refine isoListFinalListSpine
      (isoListSymNormalCat (N := N) (n := [r]) (N' := N') (n' := [r']) hN ?_ hiso')
      (isoListNormal hcons' hN) hr' hfin
    intro d hd
    rw [List.flatten_cons, List.flatten_nil, List.mem_append] at hd
    rcases hd with hd | hd
    · exact List.mem_flatten.mpr ⟨r, hr, hd⟩
    · exact absurd hd (by simp)
  · -- ⇐ 向：iso_list_final_list 正向实例直投
    intro hfin
    exact isoListFinalListSpine hiso' hN hr hfin

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；三件预期零 sorryAx）：
#print axioms Kepler.Text.TameSpine.isoListFinalListSpine
#print axioms Kepler.Text.TameSpine.isoListSymNormalCat
#print axioms Kepler.Text.TameSpine.isoListFinalListEqSpine
-/
