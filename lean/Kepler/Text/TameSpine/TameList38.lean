/-
  Kepler.Text.TameSpine.TameList38 — B1 Tame_list 地基批 38：one_step/contour
  运输章 + Seq-index 收束（tamespine-port-plan §4 批次表 B1 行；接续批 37 =
  TameList37.lean，批 37 终点 = HOL :11944（last_flatten 已落，:11831
  contour_list_hd_dart 已随收）；本批起点 = HOL :11797
  `inj_on_one_step_list`。行号均按主仓 reference/flyspeck（commit 1ce0353）
  实测。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11797-:11904）：

  主件一：`inj_on_one_step_list` :11797-:11829
  `!phi L h1 h2. good_list L /\ inj_on phi (elements_of_list L) /\
  MEM h1 (list_of_darts L) /\ MEM h2 (list_of_darts L) ==>
  (let nphi = (\u. phi (FST u),phi (SND u)) in one_step_list (MAP (MAP phi) L)
  (nphi h1) (nphi h2) = one_step_list L h1 h2)`
  ↦ `injOnOneStepList`（真证，one_step 运输章开局；HOL bool 等式 ↦ Iff，
  LET_THM 的 nphi 按 β-归约后 pair-lift 显式内联陈述）。HOL 证体
  REWRITE[one_step_list;e_list_fun;List_hypermap.e_list] + f_list_map 双发 +
  good_list_e_list 证人 + mem_f_list + inj_on_imp_inj_dart meson 收口；
  Lean 面同链：⇒ 向两支各经 fListMap（批 5 f_list_map）把 mapped f_list
  拉回 nphi (f_list L _) 形，再 injOnLiftListOfDarts（批 2
  inj_on_imp_inj_dart，pair-eq 槽）+ fList_mem_darts（TameLp mem_f_list
  :7255，Nodup 槽 = hL.1）收口；⇐ 向 e_list 支先 eListFun（批 5
  e_list_fun）换面，两支 fListMap 正向回填，其中 e_list h1 ∈ darts 由
  goodListEList（批 5 good_list_e_list）供给。

  主件二：`inj_on_contour_list` :11841-:11877
  `!phi L s. good_list L /\ inj_on phi (elements_of_list L) ==> contour_list
  L s ==> contour_list (MAP (MAP phi) L) (MAP nphi s)`
  ↦ `injOnContourList`（真证）。HOL 双重 LIST_INDUCT 在 Lean 侧免归纳——
  ContourListSpine 两分量逐槽构造：darts 分量经 la7_listOfDarts_map
  （TameLp，map_list_of_darts :1051）+ mem_map（HOL map_list_of_darts 重写
  + MEMf_MAP :1059 两步合成一步）；one_step 分量 `(s.map nφ)[i]!` 逐槽经
  getElem!Map 私件换形后由主件一 Iff .mpr 直取（前提槽：hc.1 供两 dart
  成员，length_map 消解 SUC i < sizel (MAP nphi s) 义务）。

  主件三：`eqseq_cat3` :11879-:11904
  `~(s1 = []) /\ ~(s2 = []) /\ LAST s1 = LAST s2 /\ uniq (cat s1 s3) /\
  cat s1 s3 = cat s2 s4 ==> (s1 = s2 /\ s3 = s4)`
  ↦ `eqseqCat3`（真证）。HOL ENOUGH_TO_SHOW 长度半边 + Seq.eqseq_cat 收口；
  长度半边在 Lean 侧不经 indexl 机制：末端元 getLast! 经
  getElem_append_left + getLast 换形落到拼接表 len-1 槽，由 idxOf_getElem
  （TameLp，uniq 表首现下标 = 指定下标——indexl_LAST :5605 的对应物，
  比 HOL indexl_LAST (uniq,ne) 更普适）双发：同元在两拼接表中首现下标
  各为 len-1，拼接表相等 + LAST 相等 ⇒ 同表同元，两方程交 omega 得长度
  半边。Seq.size_eq0 ↦ length_pos_of_ne_nil、Seq.cat_uniq ↦
  nodup_append、MEM_LAST ↦ getElem 通路，均平凡折算免移植。

  批内分工记账（桥引不重移植；批 37 头注预记缺口勘误）：
  - 批 37 头注预记「fList↔findFaceDarts 连接层展开 + good_list_e_list
    （:3883）载体缺口」——实际批 5 已全数在库：goodListEList
    （TameList5.lean:336）、fListMap（f_list_map :3840，TameList5.lean:300，
    find_face_map 连接层已封装其证体）、eListFun（:3827，
    TameList5.lean:291）。系批 37 侦察面漏（对拍 TameList5 头注即见），
    本批更正记档，零新载体落地；
  - `inj_on_imp_inj_dart` :1100 = 批 2 injOnLiftListOfDarts
    （TameList2.lean:857，pair-eq 形）；
  - `mem_f_list` :7255 = TameLp fList_mem_darts（TameLp.lean:3918，
    (listOfDarts L).Nodup 前提由 hL.1 供给）；
  - `map_list_of_darts` :1051 = TameLp la7_listOfDarts_map
    （TameLp.lean:4529）；`MEMf_MAP` = 批 2 memfMap（TameList2.lean:195）
    （本批经 mem_map 一步合成，未单引）；
  - `eqseq_cat`（Seq，:6124）= 批 9 eqseqCat2（TameList9.lean:826）；
  - `indexl_LAST` :5605 / `Seq.index_cat` / `MEM_LAST` 机制面见主件三
    （idxOf_getElem + getElem_append_left 替代，indexl 本体免移植）。

  私件（惯例同证重推导，非新领土）：getLast!_eq_getLast（批 37 同证）、
  getElem!Eq（批 13 同证）+ 新面 getElem!Mem/getElem!Map（map 槽
  getElem! 换形，HOL MAP nphi s 逐槽下标搬运的消费载体）。

  跳过项（非止损，记档体例）：
  · :11831 `contour_list_hd_dart`——批 37 已随收（TameList37.lean:201）；
  · :11906 `flatten_eq_nil` / :11922 `last_flatten`——批 37 已收；
  · :11783-:11793 `e_list_map` 注释块——批 37 已记档跳过（区间属上批
    终点前，本批起点回看无涉）。

  终点自然边界：:11904 后 :11946 入 `parts_characterize`（parts 章归纳
  主体，批 39 领土——size_induct 载体已在库 TameList9 sizeInduct
  （HOL :6296 同源），需侦察 parts_cases/parts_pure/parts_cat/cat_from/
  mem_imp_not_uniq_cat 载体面后成批）。

  诚实记账：本批三件全部真证，零新 def、零 sorry、零止损件、零记账债
  （私件同证重推导 + 桥引批 1-9 既有载体；批 37 预记缺口勘误一处入档，
  非债——载体实存）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零
  git 写操作。批 39 接续点：HOL :11946 `parts_characterize`
  `!L r prt. ~(r=[]) /\ uniq r /\ flatten prt = r /\
  all (\p. ~(p=[])) prt /\ (!p d. MEM p prt /\ MEM d p /\ ~(d = LAST r)
  ==> (~(next_el r d = f_list L (e_list d)) <=> d = LAST p)) ==>
  parts L r = prt`（size_induct 归纳主体，sizeInduct 在库）。
-/

import Kepler.Text.TameSpine.TameList37

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList listOfDarts eList fList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList elementsOfList)

/-! ### §0 私件：getLast! / getElem! 换形器（惯例同证重推导 + map 槽新面） -/

/-- 非空表 `getLast!` 即 `getLast`（批 37 私件同证重推导）。 -/
private theorem getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  simp

/-- `l[i]!` 与 `l[i]'h` 的换形器（下标在界内时 getElem! 消歧；批 13 私件
同证重推导）。 -/
private theorem getElem!Eq {l : List (ℕ × ℕ)} {i : ℕ} (hi : i < l.length) :
    l[i]! = l[i]'hi := by
  refine Eq.trans (List.getElem!_eq_getElem?_getD ..) ?_
  refine Eq.trans (congrArg (fun o : Option (ℕ × ℕ) => o.getD default)
    ((List.getElem_eq_iff hi).mp rfl)) ?_
  rfl

/-- 界内 `getElem!` 是成员（getElem!Eq + getElem_mem）。 -/
private theorem getElem!Mem {l : List (ℕ × ℕ)} {i : ℕ} (hi : i < l.length) :
    l[i]! ∈ l := by
  rw [getElem!Eq hi]
  exact List.getElem_mem hi

/-- map 的 getElem! 换形：`(s.map f)[i]! = f (s[i]!)`（HOL `MAP nphi s`
逐槽下标搬运的消费载体；cons 零/后继两拆归纳）。 -/
private theorem getElem!Map {f : ℕ × ℕ → ℕ × ℕ} {s : List (ℕ × ℕ)} :
    ∀ (i : ℕ), i < s.length → (s.map f)[i]! = f s[i]! := by
  induction s with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons a t ih =>
    intro i hi
    cases i with
    | zero => simp
    | succ j =>
      rw [List.getElem!_cons_succ]
      exact ih j (by have hlc : (a :: t).length = t.length + 1 := rfl; omega)

/-! ### §1 inj_on_one_step_list（tame_list.hl:11797-:11829）——one_step 运输章开局 -/

/-- **HOL `inj_on_one_step_list`**（tame_list.hl:11797-:11829）
`good_list L /\ inj_on phi (elements_of_list L) /\ MEM h1 (list_of_darts L)
/\ MEM h2 (list_of_darts L) ==> one_step_list (MAP (MAP phi) L) (nphi h1)
(nphi h2) = one_step_list L h1 h2`（nphi = pair-lift，bool 等式 ↦ Iff）
——⇒ 向 fListMap 双发拉回 + injOnLiftListOfDarts 收口；⇐ 向 eListFun 换面
+ fListMap 正向回填（e_list h1 ∈ darts 由 goodListEList）。 -/
theorem injOnOneStepList {L : fgraph ℕ} {hL : GoodList L} {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) {h1 h2 : ℕ × ℕ}
    (hh1 : h1 ∈ listOfDarts L) (hh2 : h2 ∈ listOfDarts L) :
    oneStepListSpine (L.map (List.map phi)) (phi h1.1, phi h1.2)
        (phi h2.1, phi h2.2) ↔ oneStepListSpine L h1 h2 := by
  constructor
  · intro hstep
    unfold oneStepListSpine at hstep ⊢
    rcases hstep with h | h
    · refine Or.inl (injOnLiftListOfDarts L hinj hh2
        (Kepler.Text.TameLp.fList_mem_darts hL.1 hh1) ?_)
      rw [h, fListMap (hL := hL) hinj hh1]
    · refine Or.inr (injOnLiftListOfDarts L hinj hh2
        (Kepler.Text.TameLp.fList_mem_darts hL.1 (goodListEList hL hh1)) ?_)
      rw [h, eListFun, fListMap (hL := hL) hinj (goodListEList hL hh1)]
  · intro hstep
    unfold oneStepListSpine at hstep ⊢
    rcases hstep with h | h
    · refine Or.inl ?_
      rw [h, fListMap (hL := hL) hinj hh1]
    · refine Or.inr ?_
      rw [h, eListFun, ← fListMap (hL := hL) hinj (goodListEList hL hh1)]

/-! ### §2 inj_on_contour_list（tame_list.hl:11841-:11877）——contour 运输 -/

/-- **HOL `inj_on_contour_list`**（tame_list.hl:11841-:11877）
`good_list L /\ inj_on phi (elements_of_list L) ==> contour_list L s ==>
contour_list (MAP (MAP phi) L) (MAP nphi s)`——免归纳两分量逐槽构造：
darts 槽 la7_listOfDarts_map（map_list_of_darts）+ mem_map；one_step 槽
getElem!Map 换形后主件一 Iff .mpr 直取。 -/
theorem injOnContourList {L : fgraph ℕ} {hL : GoodList L} {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) {s : List (ℕ × ℕ)}
    (hc : ContourListSpine L s) :
    ContourListSpine (L.map (List.map phi))
      (s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Kepler.Text.TameLp.la7_listOfDarts_map]
    exact List.mem_map.mpr ⟨y, hc.1 y hy, rfl⟩
  · intro i hi
    rw [List.length_map] at hi
    have hi' : i < s.length := by omega
    rw [getElem!Map _ hi', getElem!Map _ hi]
    exact (injOnOneStepList (hL := hL) hinj (hc.1 _ (getElem!Mem hi'))
      (hc.1 _ (getElem!Mem hi))).mpr (hc.2 i hi)

/-! ### §3 eqseq_cat3（tame_list.hl:11879-:11904）——Seq-index 收束 -/

/-- **HOL `eqseq_cat3`**（tame_list.hl:11879-:11904）
`~(s1 = []) /\ ~(s2 = []) /\ LAST s1 = LAST s2 /\ uniq (cat s1 s3) /\
cat s1 s3 = cat s2 s4 ==> (s1 = s2 /\ s3 = s4)`——长度半边经
idxOf_getElem 双发（末端元在拼接表 len-1 槽首现下标唯一）+ omega；
收口 = 批 9 eqseqCat2。 -/
theorem eqseqCat3 {s1 s2 s3 s4 : List (ℕ × ℕ)} (hne1 : s1 ≠ [])
    (hne2 : s2 ≠ []) (hlast : s1.getLast! = s2.getLast!)
    (hun : (s1 ++ s3).Nodup) (hcat : s1 ++ s3 = s2 ++ s4) :
    s1 = s2 ∧ s3 = s4 := by
  have hpos1 : 0 < s1.length := List.length_pos_of_ne_nil hne1
  have hpos2 : 0 < s2.length := List.length_pos_of_ne_nil hne2
  have hun2 : (s2 ++ s4).Nodup := by rw [← hcat]; exact hun
  have ib1 : s1.length - 1 < (s1 ++ s3).length := by
    rw [List.length_append]; omega
  have ib2 : s2.length - 1 < (s2 ++ s4).length := by
    rw [List.length_append]; omega
  have hlast1 : (s1 ++ s3)[s1.length - 1]'ib1 = s1.getLast! := by
    rw [List.getElem_append_left (show s1.length - 1 < s1.length by omega),
      getLast!_eq_getLast hne1, List.getLast_eq_getElem hne1]
  have hlast2 : (s2 ++ s4)[s2.length - 1]'ib2 = s2.getLast! := by
    rw [List.getElem_append_left (show s2.length - 1 < s2.length by omega),
      getLast!_eq_getLast hne2, List.getLast_eq_getElem hne2]
  have i1 : (s1 ++ s3).idxOf ((s1 ++ s3)[s1.length - 1]'ib1)
      = s1.length - 1 := Kepler.Text.TameLp.idxOf_getElem hun ib1
  have i2 : (s2 ++ s4).idxOf ((s2 ++ s4)[s2.length - 1]'ib2)
      = s2.length - 1 := Kepler.Text.TameLp.idxOf_getElem hun2 ib2
  rw [hlast1] at i1
  rw [hlast2] at i2
  rw [hcat, hlast] at i1
  -- i1 : (s2 ++ s4).idxOf s2.getLast! = s1.length - 1，与 i2 同 LHS 交 omega
  have hlen : s1.length = s2.length := by omega
  have hcatlen := congrArg List.length hcat
  simp only [List.length_append] at hcatlen
  exact (eqseqCat2 (by omega)).mp hcat

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；三件预期零 sorryAx）：
#print axioms Kepler.Text.TameSpine.injOnOneStepList
#print axioms Kepler.Text.TameSpine.injOnContourList
#print axioms Kepler.Text.TameSpine.eqseqCat3
-/
