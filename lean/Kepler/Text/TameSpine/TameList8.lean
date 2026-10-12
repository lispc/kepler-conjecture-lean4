/-
  Kepler.Text.TameSpine.TameList8 — B1 Tame_list 地基批 8：hypermap-of-list 补件 +
  rot/轨道词典 + final_loops 群（tamespine-port-plan §4 批次表 B1 行；接续批 7 =
  TameList7.lean，HOL :4387-:4700 已由批 7 落，本批从 `mem_find_list1` :4706 起）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:4706-:5579）：

  - hypermap-of-list 补件 :4706-:4957（`mem_find_list1`/`normal_list_mem_n`/
    `inverse_node_map_list`/`loop_list_f_or_ni`/`edge_nondeg_f_xor_ni`/`index_hd0`；
    `n_list_ext_n_list` :4717 与 `face_map_list` :4907 在 Lean 载体下已被
    TameLp `nodeMap_hypermapOfList`/`faceMap_hypermapOfList` 逐字覆盖，零移植）；
  - rot/轨道词典块 :4958-:5190（`next_el_power_eq`/`rot_eq_rot`/`next_el_power_rot`/
    `final_list_power`/`final_list_rot`/`rot_sym`/`set_of_list_rot`/
    `loop_of_face_list`）；
  - final_loops 群 :5190-:5560（`final_list_face`/`marked_list_edge_map_final`/
    `darts_in_final_loops_list`/`final_loops_list`/`face_loop_imp_final_list`/
    `darts_in_final_loops_conv`/`final_loops_conv`/`final_loops_list_eq`/
    `darts_in_final_loops_list_eq`）；
  - `support_of_sequence_list` :5561（`support_of_sequence` 引擎在 Lean
    Hypermap 层按其头注裁定不移植——仅被 is_inj_list 消费；本批给出
    列表层镜像 `supportOfSequenceSpine` 直接证）。

  旗塔回填点（tame_defs2.hl:469-:535 定义层，按批 7 报告节奏：本批只落两件
  简单 def，`s_list`/`l'm` 的 min_num 折算（Nat.find? + junk-0）与
  `flag_list`/`s_flag_list`/`MarkedListSpine` 末两合取块随 reduction 波进场）：
  - `contour_list`（tame_defs2.hl:88-:91）↦ `ContourListSpine`；
  - `final_dart_list`（tame_defs2.hl:146-:147）↦ `FinalDartListSpine`，并被
    `dartsInFinalLoopsListEq`（= HOL :5537）首次非平凡消费（两个方向的
    集合等式都过它，非 junk 定义）。

  诚实记账（本批跳过件与边界）：
  - **Graph/枚举机械件 :4750-:4887 整块跳过**（`MEM_splitFace2`/
    `splitFace_split_face`/`HEIGHTS`/`mapAt`/`foldr2`/`sumn`/`NOT_IMP_THM`/
    `IMP_IMP_THM`/`C_EL_REC`/`list_update_ALT`/`sub1_ALT`/`sub_nth`）：
    splitFace/Graph 访问器已由 Isabelle AFP 移植层 `Kepler.Graphs.FaceDivision*`
    承载（`splitFace_split_face` 正名已在那里），其余为 Mathlib List/逻辑
    平凡件（「Mathlib/Graphs 已有则跳过」惯例）；本模块 import 闭包不含
    Kepler.Graphs.FaceDivision*，其消费定理出现时再桥引；
  - `n_list_ext_n_list` :4717/`face_map_list` :4907 = TameLp 点态件逐字
    （Lean 的 `_ext` 载体就是 edgeMap/nodeMap/faceMap），零移植零收窄；
  - `next_el_cat` 族（:5580-:5683）、`LAST/HD` 词典（:5696-:5998）、
    `partition_into_atom0r` 块（:6007 起）留给批 9（本批在 final_loops 群
    自然边界收批，`darts_in_final_loops_list_eq` 是批 7 `MarkedListSpine`
    旗塔两合取块的直接上游，优先级更高）；
  - 批 7 私件 `faceOrbitSubsetFindFace` 为 private 不跨文件可见，本批在
    §0 以 `faceOrbitSubsetFaceTable` 重推导（逐字同证），并补出 ⊇ 向
    `faceTableSubsetFaceOrbit`（`loop_of_face_list` 的 darts 字段需要双向）。

  批内分工记账（桥引不重移植）：
  - 批 2/6/7 接口直接 import：`rotateSpineAdd`/`rotateSpineNil`（批 2 rotate 桥）/
    `loopOfListSpine`/`loopOfListSpine_real`/`loopFamilyOfListSpine`/
    `loopMapNextEl`/`inDartLoopOfList`/`dartLoopOfList`/`isLoopOfList`/
    `normalListUniqNonnil`/`normalListListOfDarts`/`uniqSublistUnique`/
    `NormalListSpine`/`loopListSpine`/`finalListSpine`/`findListSpine`/
    `MarkedListSpine`/`inverseNListExt`/`goodListEList`；
  - TameLp 既有件全限定/开名桥引：`hypermapOfList` 三映射点态件、
    `findFaceDarts_eq_of_mem`/`findFaceDarts_congr_of_mem`/`findFaceDarts_nodup`/
    `findFace_fList`/`fList_mem_darts`/`dart_in_face`/`mem_darts_of_mem_findFace`/
    `nextEl_mem_of_mem`/`getElem_idxOf`/`idxOf_getElem`/`getD_eq_getElem_of_lt`/
    `nextEl_eq_getD`/`la7_eList_involutory`/`nList_fList`；
  - Hypermap 引擎件：`loopOfFace`/`loopOfFace_darts`/`mem_faceFinset`/
    `faceFinset_coe`/`finalLoops`/`dartsInFinalLoops`（含
    `mem_dartsInFinalLoops(_iff)`）/`EdgeNondegenerate`（`edgeNondegenerate_iff`）/
    `Loop.ext`；Kepler.Text 的 `res`/`res_apply_of_mem(_not_mem)` 与
    Kepler.Text.Fan 的 `extendPerm`（本批 map 字段走 `loopMapNextEl` 全域形，
    不需要 res/extendPerm 旁支点态件）；Mathlib `List.getElem_rotate` 直接
    承担 HOL `Seq2.rot_to_index`/`next_el_rot_eq` 的 getElem 载体。

  载体折算（沿批 1-7 约定）：
  - `rot n s` ↦ `s.rotate n`（批 2 载体；HOL `rot` 的 drop++take 无 mod 形经
    `rotateSpineRot` 折算，`rot_oversize` 等无 mod 特有件不进入本批）；
  - `cat s t` ↦ `s ++ t`、`indexl` ↦ `List.idxOf`、`set_of_list` ↦ 成员集载体
    `{x | x ∈ _}`、`LAST`/`HD` ↦ `getLast!`/`head!`（junk 按默认值吸收，
    消费侧全部携带非空折算）；
  - `next_el` 幂 ↦ `Function.iterate (nextEl s)`；HOL `POWER_0`/`POWER` ↦
    `pow_zero`/`pow_succ'` + `Function.iterate` 的复合形；
  - `loop_of_face` ↦ `(hypermapOfList L hL).loopOfFace x`（Hypermap 类型层），
    Loop 等式经 `Loop.ext` 双字段（darts/map）闭合，map 字段经
    `res_apply_of_mem` + `faceMap_hypermapOfList` + `nextElRotateFunc` 收口；
  - `support_of_sequence f n` ↦ `supportOfSequenceSpine f n = {f i | i ≤ n}`
    （列表层镜像，见 :5561 记账）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git 写操作。
-/

import Kepler.Text.TameSpine.TameList7

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs nextEl prevEl listOfDarts GoodList findFaceDarts
  eList fList nList)
open Kepler.Graphs (fgraph)
open Kepler.Text (PermutesOn orbitMap)
open Kepler.Text.Fan (extendPerm extendPerm_permutes)
open Kepler.Text.TameLp (hypermapOfList elementsOfList nodesOfListSet GoodListNodesTl
  listOfElements nList_fList faceMap_hypermapOfList nodeMap_hypermapOfList
  edgeMap_hypermapOfList fList_mem_darts dart_in_face findFaceDarts_nodup
  findFaceDarts_eq_of_mem findFaceDarts_congr_of_mem findFace_fList
  getElem_idxOf idxOf_getElem getD_eq_getElem_of_lt nextEl_eq_getD
  la7_eList_involutory nextEl_mem_of_mem getLastD_eq_getElem_last
  headD_eq_getD_zero mem_darts_of_mem_findFace)
open Kepler.Text.TameSpine (rotateSpineAdd rotateSpineNil loopOfListSpine
  loopFamilyOfListSpine finalListSpine findListSpine NormalListSpine
  normalListUniqNonnil normalListListOfDarts loopListSpine oneStepListSpine
  uniqSublistUnique inDartLoopOfList dartLoopOfList loopMapNextEl isLoopOfList
  inverseNListExt goodListEList)

open scoped Classical

/-! ### §0 next_el 轨道私有引擎（轨道枚举 + 旋转不变性 + face 表双向） -/

/-- 同表两下标相等则取元相等（proof-irrelevant getElem 换形器）。 -/
private theorem getElemCon {l : List (ℕ × ℕ)} {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (hab : a = b) : l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- 单步轨道：nodup 表第 `j` 项的 `next_el` = 第 `(j+1) mod len` 项。 -/
private theorem nextElStep {s : List (ℕ × ℕ)} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (hj1 : (j + 1) % s.length < s.length) :
    nextEl s (s[j]'hj) = s[(j + 1) % s.length]'hj1 := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  rw [nextEl_eq_getD (List.getElem_mem hj), idxOf_getElem hsn hj,
    getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]

/-- 轨道枚举：nodup 表上 `next_el` 幂从第 `j` 项出发按 mod 下标走
（HOL `Seq2.next_el_power` 的载体形）。 -/
private theorem nextElIterateGetElem {s : List (ℕ × ℕ)} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (n : ℕ) (hjn : (j + n) % s.length < s.length) :
    (nextEl s)^[n] (s[j]'hj) = s[(j + n) % s.length]'hjn := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact getElemCon hj hjn (by rw [Nat.add_zero, Nat.mod_eq_of_lt hj])
  | succ k ih =>
    have hjk : (j + k) % s.length < s.length := Nat.mod_lt _ hpos
    rw [Function.iterate_succ_apply', ih,
      nextElStep hsn hjk (Nat.mod_lt ((j + k) % s.length) hpos)]
    refine getElemCon (Nat.mod_lt _ hpos) hjn ?_
    have hmod : ((j + k) % s.length + 1) % s.length = (j + k + 1) % s.length :=
      Nat.mod_add_mod (j + k) s.length 1
    rw [hmod, Nat.add_assoc]

/-- 轨道不离开表。 -/
private theorem nextElIterateMem {s : List (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ s) :
    ∀ n : ℕ, (nextEl s)^[n] x ∈ s := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-- 表外 `next_el` 恒等（junk 支；非空表）。 -/
private theorem nextElOfNotMem' {s : List (ℕ × ℕ)} (hne : s ≠ []) {x : ℕ × ℕ}
    (hx : x ∉ s) : nextEl s x = x := by
  have hidx : s.idxOf x = s.length := List.idxOf_eq_length hx
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  show (if s.idxOf x = s.length - 1 then s.headD x
    else s.getD (s.idxOf x + 1) x) = x
  rw [if_neg (by omega : ¬(s.idxOf x = s.length - 1)), hidx,
    List.getD_eq_default s x (by omega)]

/-- nodup 表旋转后 `next_el` 函数不变（HOL `Seq2.next_el_rot_eq`）。 -/
private theorem nextElRotateFunc {s : List (ℕ × ℕ)} (hsn : s.Nodup) (k : ℕ) :
    nextEl (s.rotate k) = nextEl s := by
  refine funext fun z => ?_
  by_cases hz : z ∈ s.rotate k
  · have hmem : z ∈ s := List.mem_rotate.mp hz
    have hzl : 0 < (s.rotate k).length := List.length_pos_of_mem hz
    have hsl : 0 < s.length := List.length_pos_of_mem hmem
    have hiz : (s.rotate k).idxOf z < (s.rotate k).length :=
      List.idxOf_lt_length_iff.mpr hz
    have h1 : (s.rotate k)[(s.rotate k).idxOf z]'hiz = z := getElem_idxOf hz
    rw [List.getElem_rotate s k _ hiz] at h1
    have hz2 : s[s.idxOf z]'(List.idxOf_lt_length_iff.mpr hmem) = z :=
      getElem_idxOf hmem
    have hkey : ((s.rotate k).idxOf z + k) % s.length = s.idxOf z :=
      (hsn.getElem_inj_iff (hi := Nat.mod_lt _ hsl)
        (hj := List.idxOf_lt_length_iff.mpr hmem)).mp (h1.trans hz2.symm)
    show nextEl (s.rotate k) z = nextEl s z
    rw [nextEl_eq_getD hz, nextEl_eq_getD hmem,
      getD_eq_getElem_of_lt (Nat.mod_lt _ hzl),
      getD_eq_getElem_of_lt (Nat.mod_lt _ hsl),
      List.getElem_rotate s k _ (Nat.mod_lt _ hzl)]
    have hEq : (((s.rotate k).idxOf z + 1) % (s.rotate k).length + k)
        % s.length = (s.idxOf z + 1) % s.length := by
      rw [List.length_rotate s k, Nat.mod_add_mod]
      have hass2 : (s.rotate k).idxOf z + 1 + k
          = (s.rotate k).idxOf z + k + 1 := by omega
      rw [hass2, ← Nat.mod_add_mod, hkey]
    exact getElemCon (Nat.mod_lt _ hsl) (Nat.mod_lt _ hsl) hEq
  · rcases Nat.eq_zero_or_pos s.length with h0 | hpos0
    · have hs0 : s = [] := List.length_eq_zero_iff.mp h0
      subst hs0
      show nextEl (([] : List (ℕ × ℕ)).rotate k) z = nextEl [] z
      rfl
    · have hzm : z ∉ s := fun hc => hz (List.mem_rotate.mpr hc)
      have hne : s ≠ [] := by
        intro hc
        rw [hc] at hpos0
        simp at hpos0
      have hrk : s.rotate k ≠ [] := fun hc => hne (List.rotate_eq_nil_iff.mp hc)
      rw [nextElOfNotMem' hrk hz, nextElOfNotMem' hne hzm]

/-- face 轨道 ⊆ 面表（HOL `f_list_ext_orbit` 的 ⊆ 半向；批 7 私件
`faceOrbitSubsetFindFace` 的同证重推导，private 不跨文件可见）。 -/
private theorem faceOrbitSubsetFaceTable {L : fgraph ℕ} (hL : GoodList L)
    {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) :
    (hypermapOfList L hL).face d ⊆ {y | y ∈ findFaceDarts L d} := by
  have key : ∀ n : ℕ, ((hypermapOfList L hL).faceMap ^ n) d ∈ findFaceDarts L d := by
    intro n
    induction n with
    | zero => simpa using dart_in_face L d |>.mpr hd
    | succ k ih =>
      have hz : ((hypermapOfList L hL).faceMap ^ k) d
          ∈ (hypermapOfList L hL).darts :=
        (hypermapOfList L hL).faceMap_permutes.pow_apply_mem k
          (List.mem_toFinset.mpr hd)
      have hFFz : findFaceDarts L (((hypermapOfList L hL).faceMap ^ k) d)
          = findFaceDarts L d := findFaceDarts_congr_of_mem hL.1 hd ih
      rw [pow_succ', Equiv.Perm.mul_apply, faceMap_hypermapOfList L hL hz]
      show nextEl (findFaceDarts L (((hypermapOfList L hL).faceMap ^ k) d))
        (((hypermapOfList L hL).faceMap ^ k) d) ∈ findFaceDarts L d
      rw [hFFz]
      exact nextEl_mem_of_mem ih
  rintro y hy
  simp only [Kepler.Text.Hypermap.face, orbitMap, Set.mem_setOf_eq] at hy
  obtain ⟨n, hn⟩ := hy
  subst hn
  exact key n

/-- face 轨道 ⊇ 面表（面表 = `next_el` 面-表的循环，轨道走遍全表；
`loop_of_face_list` darts 字段的 ⊇ 向引擎）。 -/
private theorem faceTableSubsetFaceOrbit {L : fgraph ℕ} (hL : GoodList L)
    {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) :
    {y | y ∈ findFaceDarts L d} ⊆ (hypermapOfList L hL).face d := by
  have hdd : d ∈ findFaceDarts L d := dart_in_face L d |>.mpr hd
  have hFFnodup : (findFaceDarts L d).Nodup := findFaceDarts_nodup hL.1 d
  have hpos : 0 < (findFaceDarts L d).length := List.length_pos_of_mem hdd
  -- faceMap 在面表上逐点 = nextEl 面表
  have hfaceTbl : ∀ z ∈ findFaceDarts L d,
      (hypermapOfList L hL).faceMap z = nextEl (findFaceDarts L d) z := by
    intro z hz
    have hzD : z ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr (mem_darts_of_mem_findFace L hz)
    rw [faceMap_hypermapOfList L hL hzD]
    show nextEl (findFaceDarts L z) z = nextEl (findFaceDarts L d) z
    rw [findFaceDarts_congr_of_mem hL.1 hd hz]
  -- 幂交换
  have hpow : ∀ n : ℕ, ((hypermapOfList L hL).faceMap ^ n) d
      = (nextEl (findFaceDarts L d))^[n] d := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, Function.iterate_zero]
      rfl
    | succ k ih =>
      have hmem := nextElIterateMem hdd k
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hfaceTbl _ hmem,
        Function.iterate_succ_apply']
  rintro y hy
  simp only [Kepler.Text.Hypermap.face, orbitMap, Set.mem_setOf_eq]
  -- 轨道走遍全表：从 d 走 (idxOf y - idxOf d) mod len 步
  have hidd : (findFaceDarts L d).idxOf d < (findFaceDarts L d).length :=
    List.idxOf_lt_length_iff.mpr hdd
  have hidy : (findFaceDarts L d).idxOf y < (findFaceDarts L d).length :=
    List.idxOf_lt_length_iff.mpr hy
  refine ⟨((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
      - (findFaceDarts L d).idxOf d) % (findFaceDarts L d).length, ?_⟩
  rw [hpow]
  have hiter := nextElIterateGetElem hFFnodup hidd
    (((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
      - (findFaceDarts L d).idxOf d) % (findFaceDarts L d).length)
    (Nat.mod_lt _ hpos)
  rw [getElem_idxOf hdd] at hiter
  rw [hiter]
  refine Eq.trans (getElemCon _ _ hkey) ?_
  exact getElem_idxOf hy
  have hkey : ((findFaceDarts L d).idxOf d
        + (((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
          - (findFaceDarts L d).idxOf d) % (findFaceDarts L d).length))
      % (findFaceDarts L d).length = (findFaceDarts L d).idxOf y := by
    rw [Nat.add_comm (findFaceDarts L d).idxOf d _, Nat.mod_add_mod]
    have h2 : (findFaceDarts L d).idxOf y + (findFaceDarts L d).length
        - (findFaceDarts L d).idxOf d + (findFaceDarts L d).idxOf d
        = (findFaceDarts L d).length + (findFaceDarts L d).idxOf y := by omega
    rw [h2, Nat.add_comm (findFaceDarts L d).length (findFaceDarts L d).idxOf y,
      Nat.add_mod_left, Nat.mod_eq_of_lt hidy]
  exact hkey

/-! ### §1 hypermap-of-list 补件（tame_list.hl:4706-:4957） -/

/-- **HOL `find_list` 定位件**（`mem_find_list1` :4706 与 `mem_find_list`
命中半向的合并载体件）：`x ∈ flatten N` 时 `findListSpine N x` 命中且 ∈ N。 -/
private theorem findListSpineHit {N : List (List (ℕ × ℕ))} {x : ℕ × ℕ}
    (hx : x ∈ N.flatten) : findListSpine N x ∈ N ∧ x ∈ findListSpine N x := by
  induction N with
  | nil => exact absurd hx (by simp)
  | cons h t ih =>
    rw [List.flatten_cons, List.mem_append] at hx
    by_cases hmem : x ∈ h
    · have hf : (h :: t).find? (fun r => decide (x ∈ r)) = some h := by
        rw [List.find?_cons, decide_eq_true hmem]
      simp only [findListSpine, hf, Option.getD_some]
      exact ⟨List.mem_cons_self .., decide_eq_true_eq.mp (decide_eq_true hmem)⟩
    · have hp : decide (x ∈ h) = false := decide_eq_false hmem
      have hf : (h :: t).find? (fun r => decide (x ∈ r))
          = t.find? (fun r => decide (x ∈ r)) := by
        rw [List.find?_cons, hp]
      obtain ⟨hm1, hm2⟩ := ih (by
        rcases hx with hx | hx
        · exact absurd hx hmem
        · exact hx)
      simp only [findListSpine, hf]
      exact ⟨List.mem_cons_of_mem _ hm1, hm2⟩

/-- **HOL `mem_find_list1`**（tame_list.hl:4706-:4714）
`!L x. MEM x (flatten L) ==> MEM x (find_list L x)`。 -/
theorem memFindList1 {N : List (List (ℕ × ℕ))} {x : ℕ × ℕ}
    (hx : x ∈ N.flatten) : x ∈ findListSpine N x :=
  (findListSpineHit hx).2

/-- **HOL `mem_find_list` 命中半向**（list_hypermap-compiled.hl）：
`x ∈ flatten N` 时 `find_list N x ∈ N`（`markedListEdgeMapFinal` 消费）。 -/
theorem findListSpineMemN {N : List (List (ℕ × ℕ))} {x : ℕ × ℕ}
    (hx : x ∈ N.flatten) : findListSpine N x ∈ N :=
  (findListSpineHit hx).1

/-- **HOL `normal_list_mem_n`**（tame_list.hl:4728-:4748）
`good_list L /\ normal_list L N /\ MEM d (flatten N) ==> MEM (n_list L d) (flatten N)`
——node 轨道 ⊆ flatten N（normal_list 末合取项）+ nodeMap 幺步 ∈ node。 -/
theorem normalListMemN {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N) {d : ℕ × ℕ}
    (hd : d ∈ N.flatten) : nList L d ∈ N.flatten := by
  have hsub := h.2.2.2.2 d hd
  have hdD : d ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr (normalListListOfDarts h d hd)
  have hmem : (hypermapOfList L hL).nodeMap d ∈ (hypermapOfList L hL).node d := by
    show (hypermapOfList L hL).nodeMap d ∈
      orbitMap (hypermapOfList L hL).nodeMap d
    exact ⟨1, by rw [pow_one]⟩
  rw [nodeMap_hypermapOfList L hL hdD] at hmem
  exact hsub hmem

/-- **HOL `inverse_node_map_list`**（tame_list.hl:4889-:4905）
`good_list L /\ MEM d (list_of_darts L) ==>
  inverse(node_map (hypermap_of_list L)) d = f_list L (e_list d)`
——经 `inverseNListExt`（批 6）点态化 + edge/face 映射点态件。 -/
theorem inverseNodeMapList {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    (hypermapOfList L hL).nodeMap.symm d = fList L (eList d) := by
  show (hypermapOfList L hL).nodeMap.symm d = fList L (eList d)
  rw [inverseNListExt hL, Equiv.Perm.mul_apply,
    edgeMap_hypermapOfList L hL (List.mem_toFinset.mpr hd)]
  exact faceMap_hypermapOfList L hL (List.mem_toFinset.mpr (goodListEList hL hd))

/-- **HOL `loop_list_f_or_ni`**（tame_list.hl:4921-:4929）
`loop_list L r /\ MEM x r ==> (next_el r x = f_list L x \/
  next_el r x = f_list L (e_list x))`——`loop_list` 合取项直取。 -/
theorem loopListFOrNi {L : fgraph ℕ} {r : List (ℕ × ℕ)} (h : loopListSpine L r)
    {x : ℕ × ℕ} (hx : x ∈ r) :
    nextEl r x = fList L x ∨ nextEl r x = fList L (eList x) :=
  (h x hx).2

/-- **HOL `edge_nondeg_f_xor_ni`**（tame_list.hl:4933-:4944）
`good_list L /\ MEM x (list_of_darts L) /\
  is_edge_nondegenerate (hypermap_of_list L) ==> ~(f_list L x = f_list L (e_list x))`
——`edgeNondegenerate_iff` + `inverseNodeMapList`。 -/
theorem edgeNondegFXorNi {L : fgraph ℕ} (hL : GoodList L)
    (hne : (hypermapOfList L hL).EdgeNondegenerate) {x : ℕ × ℕ}
    (hx : x ∈ listOfDarts L) : fList L x ≠ fList L (eList x) := by
  have hxD : x ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hx
  intro hcon
  exact ((hypermapOfList L hL).edgeNondegenerate_iff.mp hne) x hxD
    (by rw [faceMap_hypermapOfList L hL hxD, inverseNodeMapList hL hx]; exact hcon)

/-- **HOL `index_hd0`**（tame_list.hl:4950-:4956）
`~(s = []) ==> indexl (HD s) s = 0`。 -/
theorem indexHd0 {s : List (ℕ × ℕ)} (hs : s ≠ []) : s.idxOf s.head! = 0 := by
  match s, hs with
  | [], h => exact absurd h (by simp)
  | a :: t, _ => exact List.idxOf_cons_self

/-! ### §2 rot/轨道词典块（tame_list.hl:4958-:5190） -/

/-- **HOL `next_el_power_eq`**（tame_list.hl:4958-:5012）
`~(s = []) /\ ~(t = []) /\ uniq s /\ uniq t /\
  (!i. (next_el s POWER i) (HD s) = (next_el t POWER i) (HD t)) ==> (s = t)`
——轨道枚举（§0 引擎）+ 长度夹逼（nodup 双下标矛盾）。 -/
theorem nextElPowerEq {s t : List (ℕ × ℕ)} (hs : s ≠ []) (ht : t ≠ [])
    (hsn : s.Nodup) (htn : t.Nodup)
    (h : ∀ i : ℕ, (nextEl s)^[i] s.head! = (nextEl t)^[i] t.head!) :
    s = t := by
  have hsl : 0 < s.length := List.length_pos_of_ne_nil hs
  have htl : 0 < t.length := List.length_pos_of_ne_nil ht
  have hheadS : s[0]'hsl = s.head! := by
    match s with
    | [] => simp at hs
    | a :: t => rfl
  have hheadT : t[0]'htl = t.head! := by
    match t with
    | [] => simp at ht
    | a :: t => rfl
  have h0st : s.head! = t.head! := by
    have h0' := h 0
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply] at h0'
    exact h0'
  have hno : ¬(s.length < t.length) := by
    intro hlt
    have h1 : (nextEl s)^[s.length] s.head! = s.head! := by
      rw [← hheadS,
        nextElIterateGetElem hsn hsl s.length
          (by rw [Nat.zero_add, Nat.mod_self]; exact hsl)]
      have hgc : s[(0 + s.length) % s.length]'(Nat.mod_lt _ hsl) = s[0]'hsl :=
        getElemCon _ _ (by rw [Nat.zero_add, Nat.mod_self])
      exact Eq.trans hgc hheadS
    have h2 : (nextEl t)^[s.length] t.head! = t[s.length]'hlt := by
      rw [← hheadT,
        nextElIterateGetElem htn htl s.length
          (by rw [Nat.zero_add]; exact Nat.mod_lt s.length htl)]
      exact getElemCon (Nat.mod_lt _ htl) hlt
        (by rw [Nat.zero_add, Nat.mod_eq_of_lt hlt])
    have h3 : t[s.length]'hlt = t[0]'htl := by
      rw [← h2, ← h s.length, h1, h0st, hheadT]
    have hz := (htn.getElem_inj_iff (hi := htl) (hj := hlt)).mp h3.symm
    omega
  have hno2 : ¬(t.length < s.length) := by
    intro hlt
    have h1 : (nextEl t)^[t.length] t.head! = t.head! := by
      rw [← hheadT,
        nextElIterateGetElem htn htl t.length
          (by rw [Nat.zero_add, Nat.mod_self]; exact htl)]
      have hgc : t[(0 + t.length) % t.length]'(Nat.mod_lt _ htl) = t[0]'htl :=
        getElemCon _ _ (by rw [Nat.zero_add, Nat.mod_self])
      exact Eq.trans hgc hheadT
    have h2 : (nextEl s)^[t.length] s.head! = s[t.length]'hlt := by
      rw [← hheadS,
        nextElIterateGetElem hsn hsl t.length
          (by rw [Nat.zero_add]; exact Nat.mod_lt s.length htl)]
      exact getElemCon (Nat.mod_lt _ hsl) hlt
        (by rw [Nat.zero_add, Nat.mod_eq_of_lt hlt])
    have h3 : s[t.length]'hlt = s[0]'hsl := by
      rw [← h2, h t.length, h1, ← h0st, ← hheadS]
    have hz := (hsn.getElem_inj_iff (hi := hsl) (hj := hlt)).mp h3.symm
    omega
  have hlen : s.length = t.length := by omega
  refine List.ext_get hlen fun i hi1 hi2 => ?_
  show s[i]'hi1 = t[i]'hi2
  calc s[i]'hi1
      = s[(0 + i) % s.length]'(Nat.mod_lt _ hsl) :=
        getElemCon hi1 (Nat.mod_lt _ hsl)
          (by rw [Nat.zero_add, Nat.mod_eq_of_lt hi1])
    _ = (nextEl s)^[i] s.head! := by
        rw [← hheadS]
        exact Eq.symm (nextElIterateGetElem hsn hsl i (Nat.mod_lt (0 + i) hsl))
    _ = (nextEl t)^[i] t.head! := h i
    _ = t[i]'hi2 := by
        rw [← hheadT]
        refine Eq.trans (nextElIterateGetElem htn htl i (Nat.mod_lt (0 + i) htl)) ?_
        exact getElemCon (Nat.mod_lt _ htl) hi2
          (by rw [Nat.zero_add, Nat.mod_eq_of_lt hi2])
