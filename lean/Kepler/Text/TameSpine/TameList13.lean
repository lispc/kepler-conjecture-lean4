/-
  Kepler.Text.TameSpine.TameList13 — B1 Tame_list 地基批 13：contour/旗塔章
  （tamespine-port-plan §4 批次表 B1 行；接续批 12 = TameList12.lean，
  B1 链 :23-:9125 无缺口，下一批起点 = HOL :9127 simple_hypermap_list）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl）——旗塔章全量 6 枚：

  `contour_list_cons` :8868 / `contour_list_is_contour` :8901 /
  `face_map_list_power` :8928 / `hyp_S_list` :8946 /
  `marked_list_empty_flagged` :8974 / `marked_list_s_flagged` :9045。
  （编排者任务书行号 :8921/:8972/:8994/:9015/:9042 相对库内副本偏移
  +53~-68 行，章内容一致，见交付报告记账。）

  诚实记账（本批跳过/合并/桥引件）：
  - `face_map_list_power`（:8928）在 `f_list_ext L ↦ faceMap`（批 6 载体
    约定）下与批 12 `fListExtFListPower`（HOL f_list_ext_f_list_power
    :8588）为同一幂等式：本批以定义性转引落名（HOL POWER_0/POWER 归纳
    步由批 12 幂引擎承担，零收窄）；
  - `s_list`（tame_defs2.hl:491-493 `MAP (\i. (f_list L POWER i) d)
    (iota 1 (l'm L r d))`）↦ 新公开载体 `sListSpine`（`iota 1 n ↦
    (range n).map (· + 1)`，`POWER ↦ Function.iterate`）；
  - `flag_list`（tame_defs2.hl:512-527）/`s_flag_list`（:495-510）↦ 新
    公开载体 `FlagListSpine`/`SFlagListSpine`（批 7 延期的 marked_list
    块 5 进场；`HD/LAST ↦ head!/getLast!`、`set_of_list SUBSET
    set_of_list ↦ ∀ ∈ → ∈`、`cat ↦ List.append`）；
  - `marked_list`（tame_defs2.hl:550-570）全量载体 ↦ 新公开
    `MarkedListSpineFull` = 批 7 前 7 合取块 `MarkedListSpine` + flag
    双分支（批 7 头注明记"旗塔随 reduction 波批次定义层进场补全"，
    本批即该进场点；语义零收窄）；
  - `empty_flagged`/`s_flagged`（Hypermap.lean:10025/:10035 已真）直引；
    `support_of_sequence p k`（Hypermap 层裁定不移植）在结论里沿批 8
    双载体折算：序列等式侧 `supportOfSequenceSpine`/`supportOfSequenceList`
    （批 8），结论块沿 Lean `EmptyFlagged` 的 Finset 版
    `Loop.pathSupport`（mem_pathSupport 与 {p i | i ≤ k} 成员逐点互转，
    语义零收窄）；
  - `is_contour`（Hypermap.lean:1666）直引，`lemma_def_contour` ↦
    `Hypermap.isContour_iff`；
  - `head_of_atom_parts`（批 11）/`parts_flatten`/`parts_uniq_nonnil`/
    `parts_all_nonnil`/`find_list_uniq`（批 9）/`parts_darts`（批 10）/
    `darts_in_final_loops_list_eq`/`final_loops_list`/`final_loops_conv`/
    `contour_list` 载体（批 8）/`in_dart_loop_of_list`/`loop_map_next_el`
    （批 6）/`marked_list_split_condition_list`/`hyp_m_l_m`（批 12）/
    `split_condition_list_of_darts`（批 12）全直引零复制；
  - `LAST_EL`（HOL p k = LAST s 支）↦ `List.getLast!_eq_getElem!`；
    find_list 命中块（批 12 同款 10 行）就地重推导（批 9 命中件私有）；
    `getLast! ∈ l`/`l[0]! = head!`/`l[i]! ∈ l` 私件按批 7→12 惯例同证。

  载体折算（沿批 1-12 约定）：`set_of_list ↦ {x | x ∈ _}`、`EL ↦
  getElem!`（junk 按默认值吸收，消费侧配非空折算）、`sizel ↦ length`、
  `PRE (sizel s) ↦ s.length - 1`、`contour_list ↦ ContourListSpine`、
  `one_step_list ↦ oneStepListSpine`（批 5）、`uniq ↦ List.Nodup`。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 14 接续点：HOL :9127 `simple_hypermap_list` 起的
  simple-hypermap 章（simple_hypermap_list :9127 / list_pairs_not_uniq
  :9173 / simple_hypermap_all_uniq :9210 / simple_hypermap_uniq :9254）。
-/

import Kepler.Text.TameSpine.TameList12

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList fList GoodList listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl faceMap_hypermapOfList
  edgeMap_hypermapOfList)

/-! ### §0 私有 getElem! 引擎（批 8/9/12 私件不跨文件，惯例同证重推导） -/

/-- `l[i]!` 与 `l[i]'h` 的换形器（下标在界内时 getElem! 消歧；批 8 同证）。 -/
private theorem getElem!Eq {l : List (ℕ × ℕ)} {i : ℕ} (hi : i < l.length) :
    l[i]! = l[i]'hi := by
  refine Eq.trans (List.getElem!_eq_getElem?_getD ..) ?_
  refine Eq.trans (congrArg (fun o : Option (ℕ × ℕ) => o.getD default)
    ((List.getElem_eq_iff hi).mp rfl)) ?_
  rfl

/-- 界内下标的 `getElem!` 成员性（HOL `MEM_EL` 的 getElem! 折算）。 -/
private theorem getElem!Mem {l : List (ℕ × ℕ)} {i : ℕ} (hi : i < l.length) :
    l[i]! ∈ l := by
  rw [getElem!Eq hi]
  exact List.getElem_mem hi

/-- 非空表 `l[0]! = l.head!`（HOL `HD` 折算）。 -/
private theorem getElem!Zero {l : List (ℕ × ℕ)} (h : l ≠ []) : l[0]! = l.head! := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-- 非空表 `l.getLast! ∈ l`（批 12 私件同证重推导）。 -/
private theorem getLastMem {l : List (ℕ × ℕ)} (h : l ≠ []) : l.getLast! ∈ l := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-! ### §1 contour_list 基础件（:8868-:8944） -/

/-- **HOL `contour_list_cons`**（tame_list.hl:8868-:8900）
`contour_list L [] /\ (contour_list L [h] <=> MEM h (list_of_darts L)) /\
(contour_list L (h1::h2::s) <=> MEM h1 (list_of_darts L) /\
one_step_list L h1 h2 /\ contour_list L (h2::s))`——载体逐句镜像
（nil/单元素支由长度条件真空；cons-cons 支 i = 0 / SUC j 两拆）。 -/
theorem contourListCons (L : fgraph ℕ) :
    ContourListSpine L [] ∧
    (∀ h : ℕ × ℕ, ContourListSpine L [h] ↔ h ∈ listOfDarts L) ∧
    (∀ (h1 h2 : ℕ × ℕ) (s : List (ℕ × ℕ)),
      ContourListSpine L (h1 :: h2 :: s) ↔
        h1 ∈ listOfDarts L ∧ oneStepListSpine L h1 h2 ∧
        ContourListSpine L (h2 :: s)) := by
  refine ⟨⟨fun x hx => (List.not_mem_nil hx).elim, fun i hi => absurd hi
    (by simp)⟩, ?_, ?_⟩
  · intro h
    constructor
    · intro hc
      exact hc.1 h (List.mem_singleton_self h)
    · intro hd
      refine ⟨fun x hx => ?_, fun i hi => absurd hi (by simp)⟩
      rcases List.mem_singleton.mp hx with hxs
      rw [hxs]
      exact hd
  · intro h1 h2 s
    have hlen : (h1 :: h2 :: s).length = s.length + 2 := by simp
    have hmem1 : h1 ∈ h1 :: h2 :: s := by simp
    have hmem2 : h2 ∈ h1 :: h2 :: s := by simp
    constructor
    · rintro ⟨hmem, hstep⟩
      refine ⟨hmem h1 hmem1, ?_, ⟨fun x hx => ?_, fun i hi => ?_⟩⟩
      · exact hstep 0 (by rw [hlen]; omega)
      · rcases List.mem_cons.mp hx with hxs | hxs
        · rw [hxs]
          exact hmem h2 hmem2
        · exact hmem _ (List.mem_cons_of_mem h1 (List.mem_cons_of_mem h2 hxs))
      · have hi2 : i + 1 + 1 < s.length + 2 := by
          simp only [List.length_cons] at hi
          omega
        have hp := hstep (i + 1) (by rw [hlen]; omega)
        simpa using hp
    · rintro ⟨hd1, hstep, htail⟩
      refine ⟨fun x hx => ?_, fun i hi => ?_⟩
      · rcases List.mem_cons.mp hx with hxs | hxs
        · rw [hxs]
          exact hd1
        · rcases List.mem_cons.mp hxs with hxs' | hxs'
          · rw [hxs']
            exact htail.1 h2 (by simp)
          · exact htail.1 _ (List.mem_cons_of_mem h2 hxs')
      · rcases Nat.eq_zero_or_pos i with hi0 | his
        · rw [hi0]
          simpa using hstep
        · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt his)
          rw [hj]
          have hi2 : j + 1 < s.length + 1 := by
            simp only [List.length_cons] at hi
            omega
          simpa using htail.2 j hi2

/-- **HOL `contour_list_is_contour`**（tame_list.hl:8901-:8926）
`good_list L /\ contour_list L s ==> is_contour (hypermap_of_list L)
(\i. EL i s) (PRE (sizel s))`——`Hypermap.isContour_iff` +
one_step_list 两支：faceMap 支 = `faceMap_hypermapOfList`（TameLp），
nodeMap-symm 支 = `inverseNodeMapList`（批 8）；成员性由 MEM_EL 折算
（§0 getElem!Mem）。 -/
theorem contourListIsContour (L : fgraph ℕ) (hL : GoodList L)
    {s : List (ℕ × ℕ)} (hc : ContourListSpine L s) :
    (hypermapOfList L hL).isContour (fun i => s[i]!) (s.length - 1) := by
  rw [Kepler.Text.Hypermap.isContour_iff]
  intro i hi
  have hilt : i + 1 < s.length := by omega
  have hilt2 : i < s.length := by omega
  have hmem : s[i]! ∈ s := getElem!Mem hilt2
  have hxd : s[i]! ∈ listOfDarts L := hc.1 _ hmem
  rcases hc.2 i hilt with hd | hd
  · refine Or.inl ?_
    rw [faceMap_hypermapOfList L hL (List.mem_toFinset.mpr hxd)]
    exact hd
  · refine Or.inr ?_
    rw [inverseNodeMapList hL hxd]
    exact hd

/-- **HOL `face_map_list_power`**（tame_list.hl:8928-:8944）
`good_list L /\ MEM d (list_of_darts L) ==> (face_map (hypermap_of_list L)
POWER i) d = (f_list L POWER i) d`——`f_list_ext L ↦ faceMap`（批 6 载体
约定）下与批 12 `fListExtFListPower`（HOL f_list_ext_f_list_power :8588）
为同一幂等式：定义性转引（POWER_0/POWER 归纳步由批 12 幂引擎承担）。 -/
theorem faceMapListPower (L : fgraph ℕ) (hL : GoodList L) (i : ℕ) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    ((hypermapOfList L hL).faceMap ^ i) d = (fList L)^[i] d :=
  fListExtFListPower L hL hd i

/-! ### §2 s_list 载体与 hyp_S_list（:8946-:8972） -/

/-- HOL `s_list`（tame_defs2.hl:491-493
`s_list L r d = MAP (\i. (f_list L POWER i) d) (iota 1 (l'm L r d))`）
逐句镜像（`iota 1 n ↦ (range n).map (· + 1)`，`POWER ↦ Function.iterate`，
`l'm ↦ lMSpine`（批 12））。 -/
noncomputable def sListSpine (L : fgraph ℕ) (r : List (ℕ × ℕ))
    (d : ℕ × ℕ) : List (ℕ × ℕ) :=
  (List.range (lMSpine L r d)).map (fun i => (fList L)^[i + 1] d)

/-- **HOL `hyp_S_list`**（tame_list.hl:8946-:8972）
`good_list L /\ good_list_nodes L /\ all uniq L /\ next_el r d = f_list L d /\
~final_list L r /\ split_condition_list L N r d ==> hyp'S (hypermap_of_list L)
(loop_family_of_list N) (loop_of_list r) d = set_of_list (s_list L r d)`——
EXTENSION：`hypMLm`（批 12）换 `hyp'm` 为 `l'm`，ENOUGH_TO_SHOW 段 =
`faceMapListPower`（本批，即 HOL face_map_list_power +
split_condition_list_of_darts 拼装，HOL 同构）。 -/
theorem hypSList (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {d : ℕ × ℕ} (hnext : nextEl r d = fList L d)
    (hsc : splitConditionListSpine hL N r d) :
    (hypermapOfList L hL).hypS (loopFamilyOfListSpine N) (loopOfListSpine r) d
      = {x | x ∈ sListSpine L r d} := by
  have hmemD : d ∈ listOfDarts L := splitConditionListOfDarts hsc
  ext x
  constructor
  · intro hx
    simp only [Kepler.Text.Hypermap.hypS, Set.mem_image, Set.mem_Icc] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    rw [hypMLm L hL hgn hunL hnext hsc] at hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    show x ∈ sListSpine L r d
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega),
      (fListExtFListPower L hL hmemD (j + 1)).symm.trans hxi⟩
  · intro hx
    simp only [Set.mem_setOf_eq, sListSpine, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    show (fList L)^[j + 1] d ∈
      (fun i : ℕ => ((hypermapOfList L hL).faceMap ^ i) d) ''
        Set.Icc 1 ((hypermapOfList L hL).hypM (loopFamilyOfListSpine N)
          (loopOfListSpine r) d)
    rw [hypMLm L hL hgn hunL hnext hsc]
    refine ⟨j + 1, ⟨by omega, by omega⟩, ?_⟩
    exact fListExtFListPower L hL hmemD (j + 1)

/-! ### §3 flag 载体（tame_defs2.hl:512-527 / :495-510；批 7 延期件进场） -/

/-- HOL `flag_list`（tame_defs2.hl:512-527）逐句镜像
（`final_dart_list ↦ FinalDartListSpine`（批 8）、`HD/LAST ↦
head!/getLast!`、`set_of_list SUBSET set_of_list ↦ ∀ ∈ → ∈`、
`e_list ↦ eList`）。 -/
def FlagListSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) : Prop :=
  (∀ u : ℕ × ℕ, u ∈ FinalDartListSpine L N → ∀ v : ℕ × ℕ,
      v ∈ FinalDartListSpine L N →
      ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
        s.getLast! = v ∧ ∀ z ∈ s, z ∈ FinalDartListSpine L N) ∧
  ∀ (r' : List (ℕ × ℕ)) (p : List (ℕ × ℕ)) (y : ℕ × ℕ),
    y = p.getLast! → p ∈ partsSpine L r' → r' ∈ N → ¬finalListSpine L r' →
    eList y ∈ FinalDartListSpine L N

/-- HOL `s_flag_list`（tame_defs2.hl:495-510）逐句镜像
（首合取与 flag_list 同形；`cat ↦ List.append`、`s_list ↦ sListSpine`）。 -/
def SFlagListSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) : Prop :=
  (∀ u : ℕ × ℕ, u ∈ FinalDartListSpine L N → ∀ v : ℕ × ℕ,
      v ∈ FinalDartListSpine L N →
      ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
        s.getLast! = v ∧ ∀ z ∈ s, z ∈ FinalDartListSpine L N) ∧
  ∀ (r' : List (ℕ × ℕ)) (p : List (ℕ × ℕ)) (y : ℕ × ℕ),
    y = p.getLast! → p ∈ partsSpine L r' → r' ∈ N → ¬finalListSpine L r' →
    ¬(y ∈ sListSpine L r x) →
    eList y ∈ sListSpine L r x ++ FinalDartListSpine L N

/-- HOL `marked_list`（tame_defs2.hl:550-570）全量载体：批 7 前 7 合取块
`MarkedListSpine` + flag 双分支（marked_list 块 5）。批 7 头注明记
"旗塔随 reduction 波批次定义层进场补全"，本批即该进场点（语义零收窄）。 -/
def MarkedListSpineFull {L : fgraph ℕ} (hL : GoodList L)
    (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ) : Prop :=
  MarkedListSpine hL N r x ∧
  (finalListSpine L r → FlagListSpine L N) ∧
  (¬finalListSpine L r → SFlagListSpine L N r x)

/-! ### §4 旗塔两件（:8974-:9125） -/

/-- 旗塔第一合取（EmptyFlagged/SFlagged 同形）：flag 首合取 ⇒ contour
序列存在块——`contourListIsContour`（本批）+ `supportOfSequenceList`
（批 8，support_of_sequence_list）+ `dartsInFinalLoopsListEq`（批 8）
+ §0 getElem! 引擎（HOL LAST_EL/HD 支）。 -/
private theorem flagContourSeq (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (h1 : ∀ u : ℕ × ℕ, u ∈ FinalDartListSpine L N → ∀ v : ℕ × ℕ,
      v ∈ FinalDartListSpine L N →
      ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
        s.getLast! = v ∧ ∀ z ∈ s, z ∈ FinalDartListSpine L N) :
    ∀ x ∈ (hypermapOfList L hL).dartsInFinalLoops (loopFamilyOfListSpine N),
      ∀ y ∈ (hypermapOfList L hL).dartsInFinalLoops (loopFamilyOfListSpine N),
      ∃ p : ℕ → ℕ × ℕ, ∃ k : ℕ, p 0 = x ∧ p k = y ∧
        (hypermapOfList L hL).isContour p k ∧
        ↑(Loop.pathSupport p k)
          ⊆ (hypermapOfList L hL).dartsInFinalLoops
            (loopFamilyOfListSpine N) := by
  intro x hx y hy
  rw [dartsInFinalLoopsListEq hL hn] at hx hy
  have hx2 : x ∈ FinalDartListSpine L N := hx
  have hy2 : y ∈ FinalDartListSpine L N := hy
  obtain ⟨s, hcs, hsne, hhd, hlast, hsub⟩ := h1 x hx2 y hy2
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hsne
  refine ⟨fun i => s[i]!, s.length - 1, ?_, ?_, contourListIsContour L hL hcs,
    ?_⟩
  · show s[0]! = x
    rw [getElem!Zero hsne]
    exact hhd
  · rw [List.getLast!_eq_getElem!] at hlast
    exact hlast
  · intro z hz
    rw [Finset.mem_coe, Loop.mem_pathSupport] at hz
    obtain ⟨j, hj, hzj⟩ := hz
    have hzj' : s[j]! = z := hzj
    subst hzj'
    have hjmem : s[j]! ∈ s := getElem!Mem (by omega)
    rw [dartsInFinalLoopsListEq hL hn]
    exact hsub _ hjmem

/-- **HOL `marked_list_empty_flagged`**（tame_list.hl:8974-:9043）
`good_list L /\ all uniq L /\ good_list_nodes L /\ marked_list L N r d /\
final_list L r ==> empty_flagged (hypermap_of_list L)
(loop_family_of_list N)`——首合取 = flagContourSeq；edge 对称支：
headOfAtomParts（批 11）+ find_list 命中块（批 9/12 同款）+ parts_darts
（批 10）+ flag 次合取 + dartsInFinalLoopsListEq/finalLoopsList（批 8）。 -/
theorem markListEmptyFlagged (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r d) (hf : finalListSpine L r) :
    (hypermapOfList L hL).EmptyFlagged (loopFamilyOfListSpine N) := by
  have hres := hm.1.1
  have hn := hm.1.2.1
  have hflag := hm.2.1 hf
  refine ⟨flagContourSeq L hL hn hflag.1, ?_⟩
  intro L' hL' x hx hLnot
  obtain ⟨r', hr'N, rfl⟩ := hL'
  obtain ⟨hr'1, hr'2⟩ := normalListUniqNonnil hn hr'N
  have hxr : x ∈ r' := (inDartLoopOfList hr'1 hr'2 x).mp hx
  have hfin' : ¬finalListSpine L r' := fun hcon =>
    hLnot (finalLoopsList hL hn hr'N hcon)
  have hflat : (partsSpine L r').flatten = r' := partsFlatten L hr'1 hr'2
  have hmemfl : x ∈ (partsSpine L r').flatten := by rw [hflat]; exact hxr
  obtain ⟨l, hlmem, hlmemd⟩ := List.mem_flatten.mp hmemfl
  have hpflnod : (partsSpine L r').flatten.Nodup := by rw [hflat]; exact hr'1
  have hfeq : findListSpine (partsSpine L r') x = l :=
    findListUniq hpflnod hlmemd hlmem
  have hp : findListSpine (partsSpine L r') x ∈ partsSpine L r' := by
    rw [hfeq]; exact hlmem
  have hxP : x ∈ findListSpine (partsSpine L r') x := by
    rw [hfeq]; exact hlmemd
  have hyne : findListSpine (partsSpine L r') x ≠ [] :=
    partsAllNonnil L hr'1 hr'2 (findListSpine (partsSpine L r') x) hp
  have hyl : (findListSpine (partsSpine L r') x).getLast!
      ∈ findListSpine (partsSpine L r') x := getLastMem hyne
  have hD : (findListSpine (partsSpine L r') x).getLast! ∈ listOfDarts L :=
    partsDarts L hn hr'N hp hyl
  have hprem : eList (findListSpine (partsSpine L r') x).getLast!
      ∈ FinalDartListSpine L N :=
    hflag.2 r' (findListSpine (partsSpine L r') x)
      (findListSpine (partsSpine L r') x).getLast! rfl hp hr'N hfin'
  rw [headOfAtomParts L hL hgn hres hn hunL hr'N hp hxP,
    edgeMap_hypermapOfList L hL (List.mem_toFinset.mpr hD),
    dartsInFinalLoopsListEq hL hn]
  exact hprem

/-- **HOL `marked_list_s_flagged`**（tame_list.hl:9045-:9125）
`good_list L /\ all uniq L /\ good_list_nodes L /\ marked_list L N r d /\
~final_list L r ==> s_flagged (hypermap_of_list L) (loop_family_of_list N)
(loop_of_list r) d`——首合取 = flagContourSeq（s_flag 同形）；edge 对称支
同 empty 支，次合取换 s_flag：`hyp_S_list`（本批）把 head-of-atom 预注
转为 ¬MEM y (s_list)，结论经 mem_append 双支并入并集。 -/
theorem markListSFlagged (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r d) (hf : ¬finalListSpine L r) :
    (hypermapOfList L hL).SFlagged (loopFamilyOfListSpine N)
      (loopOfListSpine r) d := by
  have hres := hm.1.1
  have hn := hm.1.2.1
  have hnext := hm.1.2.2.2.2.2.1
  have hsf := hm.2.2 hf
  have hsc := markListSplitConditionList L hL hm.1 hf
  refine ⟨flagContourSeq L hL hn hsf.1, ?_⟩
  intro L' hL' y hy hLnot hhead
  obtain ⟨r', hr'N, rfl⟩ := hL'
  obtain ⟨hr'1, hr'2⟩ := normalListUniqNonnil hn hr'N
  have hyr : y ∈ r' := (inDartLoopOfList hr'1 hr'2 y).mp hy
  have hfin' : ¬finalListSpine L r' := fun hcon =>
    hLnot (finalLoopsList hL hn hr'N hcon)
  have hflat : (partsSpine L r').flatten = r' := partsFlatten L hr'1 hr'2
  have hmemfl : y ∈ (partsSpine L r').flatten := by rw [hflat]; exact hyr
  obtain ⟨l, hlmem, hlmemd⟩ := List.mem_flatten.mp hmemfl
  have hpflnod : (partsSpine L r').flatten.Nodup := by rw [hflat]; exact hr'1
  have hfeq : findListSpine (partsSpine L r') y = l :=
    findListUniq hpflnod hlmemd hlmem
  have hp : findListSpine (partsSpine L r') y ∈ partsSpine L r' := by
    rw [hfeq]; exact hlmem
  have hyP : y ∈ findListSpine (partsSpine L r') y := by
    rw [hfeq]; exact hlmemd
  have hyne : findListSpine (partsSpine L r') y ≠ [] :=
    partsAllNonnil L hr'1 hr'2 (findListSpine (partsSpine L r') y) hp
  have hyl : (findListSpine (partsSpine L r') y).getLast!
      ∈ findListSpine (partsSpine L r') y := getLastMem hyne
  have hD : (findListSpine (partsSpine L r') y).getLast! ∈ listOfDarts L :=
    partsDarts L hn hr'N hp hyl
  have hH := headOfAtomParts L hL hgn hres hn hunL hr'N hp hyP
  rw [hH] at hhead
  rw [hypSList L hL hgn hunL hnext hsc] at hhead
  simp only [Set.mem_setOf_eq] at hhead
  have hprem : eList (findListSpine (partsSpine L r') y).getLast!
      ∈ sListSpine L r d ++ FinalDartListSpine L N :=
    hsf.2 r' (findListSpine (partsSpine L r') y)
      (findListSpine (partsSpine L r') y).getLast! rfl hp hr'N hfin' hhead
  rw [hH, edgeMap_hypermapOfList L hL (List.mem_toFinset.mpr hD),
    dartsInFinalLoopsListEq hL hn, hypSList L hL hgn hunL hnext hsc]
  rcases List.mem_append.mp hprem with hmemS | hmemF
  · exact Set.mem_union_right _ hmemS
  · exact Set.mem_union_left _ hmemF

end Kepler.Text.TameSpine
