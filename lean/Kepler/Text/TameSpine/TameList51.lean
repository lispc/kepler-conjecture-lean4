/-
  Kepler.Text.TameSpine.TameList51 — B1 Tame_list 地基批 51：
  quotient 收官 capstone（tamespine-port-plan §4 批次表 B1 行；接续批 50 =
  TameList50.lean，批 50 终点 = HOL :13155；本批起点 = HOL :13158
  `hypermap_of_quotient_list_final`，章主体一件。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测。

  槽面侦察裁定（批 50 头注预记面的对拍结论）：

  - **final_list_quotient**（tame_list.hl:12802 `good_list L /\
    is_edge_nondegenerate (hypermap_of_list L) /\ normal_list L N /\
    all (final_list L) N ==> quotient_list L N = MAP (MAP FST) N`）：
    预记已册确认——批 47 finalListQuotient（TameList47.lean:155，前提
    序 hnedg/hnorm/hfinal）直投，零镜像零重落。
  - **hypermap_of_list_perm**（list_hypermap_iso-compiled.hl:370-:372
    `perm_eq L1 L2 /\ good_list L1 ==> hypermap_of_list L1 =
    hypermap_of_list L2`）：批 50 尾处方「在册性未侦察」，本批全库
    grep（含 LocalAuto 族 + core v4.32.2/mathlib/batteries 三处）确认
    Lean 零载体 → **裁定自证落地**（本批 §1）。HOL 证体逐槽：
    `good_list_perm` 槽（good2 承接）↦ Lean 形 `hL2 : GoodList L2`
    显式证人参数化（批 49 rotHypermapOfListEq 载体语义记档同款，
    hypermapOfList 消费侧两侧均需 GoodList，终语句零收窄）；
    `list_of_darts_perm` + `perm_eq_mem` 槽 ↦ core `List.Perm.map`/
    `List.Perm.flatten`/`Perm.mem_iff` 直投（darts 字段集合面——
    载体记档：darts 成员面经 face 级 perm 的 map listPairs+flatten
    搬运，非 hp.mem_iff 直投）；`perm_eq_set_of_list_eq` 面 ↦
    darts_hypermapOfList（TameLp）+ Finset 成员桥（批 49 §1 私件
    hmemBridge 同证重落，private 不跨文件雷区既档）；三置换字段
    res/funext 面 ↦ `Hypermap.ext'`（Hypermap.lean:3349）+
    edgeMap/nodeMap/faceMap_hypermapOfList 逐点写。face 一致性核心：
    HOL good_list 单面性（d 属至多一面）隐含 `find_face L1 d =
    find_face L2 d`——Lean 显式化：memFindFace（批 49）取 L2 侧面
    l2 + dart_in_face（TameLp）+ Perm 搬运 l2 ∈ L1 + findFaceEq
    （批 50）↔ 单面唯一性合流（hfind）。
  - **Seq2.perm_eq_map**（text_formalization/tame/ssreflect/
    seq2-compiled.hl:546 `perm_eq s1 s2 ==> perm_eq (map f s1)
    (map f s2)`）：core `List.Perm.map`（Init/Data/List/Perm.lean:213
    逐字同语句）零镜像记档（批 48 rotate_perm 体例）。
  - **Seq.perm_eq_sym**（jHOLLight/Examples/seq-compiled.hl:2139
    `!s1 s2. perm_eq s1 s2 = perm_eq s2 s1`）：core `List.Perm.symm`
    同证件零镜像；两槽在本批证明内化（Perm 代数面），不占领土。
  - **lower_case**（tame_list.hl:1397）：`end_itlist CONJ
    [GSYM Seq.map_MAP; GSYM Seq.size; filter_FILTER; REVERSE_rev;
    GSYM last_LAST; APPEND_cat; Seq2.ALL_all]`——重写集打包件非单体
    定理（upper_case :1401 = GSYM lower_case 同），零镜像，capstone
    ENOUGH 段经 fstListOfFaces（批 50）+ Perm 代数整体内化。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:13158-:13190）：

  章主体：`hypermap_of_quotient_list_final` :13158 `!L N. good_list L
  /\ normal_list L N /\ all (final_list L) N /\
  is_edge_nondegenerate (hypermap_of_list L) /\ all uniq L /\
  connected_hypermap (hypermap_of_list L) /\ ~(N = []) ==>
  hypermap_of_list (quotient_list L N) = hypermap_of_list L` ↦
  `hypermapOfQuotientListFinal`（真证；LHS 证人 = goodListQuotient
  项式直投，批 49 缺口②既档约定，终语句零收窄）。HOL 证体逐槽：
  - INTRO_TAC normal_list_as_list_of_faces + 剥存在 ↦ 批 49
    normalListAsListOfFaces 七元 obtain（N'/hQ'/normal/final/非空/
    hypermap 等式/成员面，逐字）；
  - `FIRST_X_ASSUM_ST '=' (SUBST1_TAC o GSYM)`（hypermap_of_list
    (quotient_list L N') = … (quotient_list L N) 右→左换面）↦
    `rw [← hpermeq]`——整应用匹配（雷区既档：逐子项换 hypermap 槽
    会撞证人依赖）；
  - `perm_eq N' (list_of_faces L)` 子目标（normal_list_perm_eq_faces
    八前提 ASM 全配）↦ 批 50 normalListPermEqFaces 直投；
  - `GMATCH_SIMP_TAC final_list_quotient` ↦ 批 47 finalListQuotient
    ——Lean 侧雷区记档（新）：rw 直接打主目标 `hypermapOfList
    (quotientListSpine L N') hQ'` 会 motive 不型正（hQ' : GoodList
    (quotientListSpine L N') 的型含被重写项，rw 抽象首参后证人槽失
    型）；裁定走 `refine hypermapOfListPerm hQ' hL ?_` 槽位化，rw 落
    在零证人依赖的 Perm 槽目标 `quotientListSpine L N' ~ L` 上；
  - ENOUGH `perm_eq L (MAP (MAP FST) N')`（ASM_MESON
    [hypermap_of_list_perm] 收残差）↦ hpm = hpermN'.map
    (fun r => r.map Prod.fst) + fstListOfFaces（批 50）+ core
    Perm.map/trans 代数；
  - ENOUGH `MAP (MAP FST) (list_of_faces L) = L`（DISCH GSYM 换面 +
    lower_case + Seq2.perm_eq_map + Seq.perm_eq_sym + 尾
    fst_list_of_faces）↦ 同 hpm 合流（fstListOfFaces 逐字即该
    ENOUGH 语句；语法面记档：finalListQuotient RHS 写
    `(fun x => x.1)`、fstListOfFaces 写 `Prod.fst`，中间面 hpm 统一
    取 fstListOfFaces 同款 Prod.fst 保 rw 语法匹配，跨语法桥由
    exact 全 defeq 收口）。
  载体雷区既档沿用：perm_eq = core `List.Perm`（批 48）、
  `MAP (MAP FST)` 顶点级 quotient 面 = quotientListSpine（批 7）+
  finalListQuotient（批 47）（fgraph ℕ 载体是点表，两侧同为
  Hypermap (ℕ × ℕ)）。

  本批范围边界：:13192 `XWCNBMA = hypermap_of_quotient_list_final`
  系纯别名件（obfuscation 名，零新内容）——照批 35 :11703
  `iso_list_marked_rN = 0` 占位/别名先例**记档跳过（纪律非止损）**；
  :13194 `(* aad *)` 新章标记，:13196 `mem_minimalFace_nonFinals`
  起新章判批 52（见尾注）。

  新落地载体：零（§1 hypermap_of_list_perm 系槽镜像首落 + capstone
  消费链全在册复用；§1 内 hmemBridge 为批 49 private 同证重落，不占
  新领土）。

  诚实记账：两件全真证（hypermapOfListPerm/
  hypermapOfQuotientListFinal），零新 def、零 sorry、零止损件、零
  记账债；XWCNBMA 别名记档跳过如上（非止损件）。范围决策：批 51
  射程收口至 :13192（capstone + 别名件，自然边界）。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 52 接续点：HOL :13196 `mem_minimalFace_nonFinals`（aad 新章首
  件：`!g. ~(nonFinals g = []) ==> MEM (minimalFace (nonFinals g))
  (nonFinals g)`，HOL 证体 = minimalFace 定义展开 + mem_minimal_el
  槽两行收口；nonFinals/minimalFace/mem_minimal_el 定义层与槽在册性
  未侦察——tame_defs 系与 mathlib Order/WellFounded 双面开工先核；
  其后 :13203 COMPLETE_INDUCT（自记「same as num_WF」，mathlib
  Nat.strongRecOn/WF 面侦察后或零镜像）随章收口）。
-/

import Kepler.Text.TameSpine.TameList50

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList listOfDarts listPairs findFaceDarts eList nList
  fList nextEl prevEl)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList dart_in_face darts_hypermapOfList
  edgeMap_hypermapOfList nodeMap_hypermapOfList faceMap_hypermapOfList)

/-! ### §1 hypermap_of_list_perm 槽（list_hypermap_iso-compiled.hl
:370-:372；批 50 尾处方「在册性未侦察」件，全库 grep 零载体裁定自证，
见头注） -/

/-- **HOL `hypermap_of_list_perm`**（list_hypermap_iso-compiled.hl
:370-:372）`perm_eq L1 L2 /\ good_list L1 ==> hypermap_of_list L1 =
hypermap_of_list L2`——载体语义记档：Lean 形加 `hL2 : GoodList L2`
显式证人前提（hypermapOfList 消费侧两侧均需 GoodList，HOL 无类型无
此前提；HOL 证体 good_list_perm 槽由此参数化内化，批 49
rotHypermapOfListEq 同款）。证体：darts 字段 = core `List.Perm.map`/
`List.Perm.flatten`/`Perm.mem_iff` 直投（hdartperm）+ Finset 成员桥
（批 49 §1 hmemBridge 同证重落）；e/n/f 三置换字段 =
`Hypermap.ext'` + 逐点 face 一致性 hfind——find_face 单面性
（good_list uniq 槽）经 memFindFace（批 49）+ dart_in_face +
findFaceEq（批 50）↔ 面显式合流。 -/
theorem hypermapOfListPerm {L1 L2 : fgraph ℕ} (hL1 : GoodList L1)
    (hL2 : GoodList L2) (hp : L1.Perm L2) :
    hypermapOfList L1 hL1 = hypermapOfList L2 hL2 := by
  -- darts 成员面搬运（list_of_darts_perm + perm_eq_mem 槽：face 级
  -- perm 的 map listPairs + flatten 直投）
  have hdartperm : ∀ x : ℕ × ℕ, x ∈ listOfDarts L1 ↔ x ∈ listOfDarts L2 := fun x =>
    (hp.map listPairs).flatten.mem_iff
  -- find_face 单面性合流槽：d ∈ darts L1 ⇒ find_face L1 d = find_face L2 d
  have hfind : ∀ d ∈ listOfDarts L1, findFaceDarts L1 d = findFaceDarts L2 d := by
    intro d hd
    have hd2 : d ∈ listOfDarts L2 := hdartperm d |>.mp hd
    obtain ⟨l2, hl2, hfl2⟩ := List.mem_map.mp (memFindFace L2 hd2)
    have hdl2 : d ∈ listPairs l2 := by
      rw [hfl2]
      exact dart_in_face L2 d |>.mpr hd2
    have hl21 : l2 ∈ L1 := hp.symm.mem_iff.mp hl2
    exact ((findFaceEq hL1 hd (listPairs l2)).mpr
      ⟨List.mem_map.mpr ⟨l2, hl21, rfl⟩, hdl2⟩).trans hfl2
  -- Finset 成员桥（批 49 §1 hmemBridge 同证重落，private 不跨文件）
  have hmemBridge : ∀ (L : fgraph ℕ) (hG : GoodList L) (x : ℕ × ℕ),
      x ∈ (hypermapOfList L hG).darts ↔ x ∈ listOfDarts L := by
    intro L hG x
    constructor
    · intro hx
      have h2 : x ∈ ((hypermapOfList L hG).darts : Set (ℕ × ℕ)) := hx
      rw [darts_hypermapOfList L hG] at h2
      exact h2
    · intro hx
      have h2 : x ∈ ((hypermapOfList L hG).darts : Set (ℕ × ℕ)) := by
        rw [darts_hypermapOfList L hG]
        exact hx
      exact h2
  have hdartmem : ∀ x : ℕ × ℕ,
      x ∈ (hypermapOfList L1 hL1).darts ↔ x ∈ (hypermapOfList L2 hL2).darts := by
    intro x
    constructor
    · intro hx
      exact (hmemBridge L2 hL2 x).mpr (hdartperm x |>.mp ((hmemBridge L1 hL1 x).mp hx))
    · intro hx
      exact (hmemBridge L1 hL1 x).mpr (hdartperm x |>.mpr ((hmemBridge L2 hL2 x).mp hx))
  refine Kepler.Text.Hypermap.ext' ?_ ?_ ?_ ?_
  · ext x
    exact hdartmem x
  · refine Equiv.Perm.ext fun x => ?_
    by_cases hx : x ∈ (hypermapOfList L1 hL1).darts
    · have hx2 : x ∈ (hypermapOfList L2 hL2).darts := hdartmem x |>.mp hx
      rw [edgeMap_hypermapOfList L1 hL1 hx, edgeMap_hypermapOfList L2 hL2 hx2]
    · have hx2 : x ∉ (hypermapOfList L2 hL2).darts := fun hc => hx (hdartmem x |>.mpr hc)
      rw [(hypermapOfList L1 hL1).edgeMap_permutes x hx,
        (hypermapOfList L2 hL2).edgeMap_permutes x hx2]
  · refine Equiv.Perm.ext fun x => ?_
    by_cases hx : x ∈ (hypermapOfList L1 hL1).darts
    · have hx2 : x ∈ (hypermapOfList L2 hL2).darts := hdartmem x |>.mp hx
      rw [nodeMap_hypermapOfList L1 hL1 hx, nodeMap_hypermapOfList L2 hL2 hx2]
      show eList (prevEl (findFaceDarts L1 x) x) = eList (prevEl (findFaceDarts L2 x) x)
      rw [hfind x ((hmemBridge L1 hL1 x).mp hx)]
    · have hx2 : x ∉ (hypermapOfList L2 hL2).darts := fun hc => hx (hdartmem x |>.mpr hc)
      rw [(hypermapOfList L1 hL1).nodeMap_permutes x hx,
        (hypermapOfList L2 hL2).nodeMap_permutes x hx2]
  · refine Equiv.Perm.ext fun x => ?_
    by_cases hx : x ∈ (hypermapOfList L1 hL1).darts
    · have hx2 : x ∈ (hypermapOfList L2 hL2).darts := hdartmem x |>.mp hx
      rw [faceMap_hypermapOfList L1 hL1 hx, faceMap_hypermapOfList L2 hL2 hx2]
      show nextEl (findFaceDarts L1 x) x = nextEl (findFaceDarts L2 x) x
      rw [hfind x ((hmemBridge L1 hL1 x).mp hx)]
    · have hx2 : x ∉ (hypermapOfList L2 hL2).darts := fun hc => hx (hdartmem x |>.mpr hc)
      rw [(hypermapOfList L1 hL1).faceMap_permutes x hx,
        (hypermapOfList L2 hL2).faceMap_permutes x hx2]

/-! ### §2 quotient 收官 capstone（tame_list.hl:13158-:13190） -/

/-- **HOL `hypermap_of_quotient_list_final`**（tame_list.hl:13158
-:13190，quotient 收官后的 hypermap 同一 capstone）`!L N. good_list L
/\ normal_list L N /\ all (final_list L) N /\
is_edge_nondegenerate (hypermap_of_list L) /\ all uniq L /\
connected_hypermap (hypermap_of_list L) /\ ~(N = []) ==>
hypermap_of_list (quotient_list L N) = hypermap_of_list L` ↦
`hypermapOfQuotientListFinal`（真证；LHS 证人 = goodListQuotient 项式
直投，批 49 缺口②既档约定）。证体逐槽见模块头注：批 49
normalListAsListOfFaces 剥存在 + 批 50 normalListPermEqFaces +
批 47 finalListQuotient（Perm 槽位化 rw 免 motive，见头注新雷区）+
hpm（core Perm.map + 批 50 fstListOfFaces）+ 本批 §1
hypermapOfListPerm 收口；lower_case/Seq2.perm_eq_map/Seq.perm_eq_sym
三槽内化零镜像。 -/
theorem hypermapOfQuotientListFinal (L : fgraph ℕ) {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (hnorm : NormalListSpine hL N)
    (hfinal : ∀ r ∈ N, finalListSpine L r)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup)
    (hconn : (hypermapOfList L hL).Connected)
    (hne : N ≠ []) :
    hypermapOfList (quotientListSpine L N)
        (goodListQuotient L hL hnorm hnedg hunL) = hypermapOfList L hL := by
  -- INTRO_TAC normal_list_as_list_of_faces 槽：剥出 N' 侧七元组
  obtain ⟨N', hQ', hnorm', hfinal', hNne', hpermeq, hmemN'⟩ :=
    normalListAsListOfFaces L hL hnorm hfinal hne hnedg hunL
  -- perm_eq N' (list_of_faces L) 槽（normal_list_perm_eq_faces 八前提）
  have hpermN' : N'.Perm (L.map listPairs) :=
    normalListPermEqFaces L hnorm' hfinal' hnedg hunL hconn hNne' hmemN'
  -- ENOUGH 两段合流：perm_eq L (MAP (MAP FST) N') 面
  -- （语法面：hpm 统一取 fstListOfFaces 同款 Prod.fst，见头注）
  have hpm : (N'.map (fun r => r.map Prod.fst)).Perm L := by
    have h1 := hpermN'.map (fun r => r.map Prod.fst)
    rwa [fstListOfFaces] at h1
  -- FIRST_X_ASSUM_ST '=' GSYM 换面槽（整应用匹配，雷区既档）
  rw [← hpermeq]
  -- final_list_quotient 槽：rw 落在零证人依赖的 Perm 槽目标（新雷区记档）
  refine hypermapOfListPerm hQ' hL ?_
  rw [finalListQuotient (N := N') hnedg hnorm' hfinal']
  exact hpm

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；两件正文 + 消费链槽全绿零 sorryAx——
探针十行：两主件 + 八槽件仅 propext/Classical.choice/Quot.sound 标准
三轴（hypermapOfListPerm 零新公理面，Classical 轴自 findFaceEq 上游
批 47-50 消费链与 goodListQuotient 批 46 链汇入）：
#print axioms Kepler.Text.TameSpine.hypermapOfListPerm
#print axioms Kepler.Text.TameSpine.hypermapOfQuotientListFinal
#print axioms Kepler.Text.TameSpine.normalListAsListOfFaces
#print axioms Kepler.Text.TameSpine.normalListPermEqFaces
#print axioms Kepler.Text.TameSpine.finalListQuotient
#print axioms Kepler.Text.TameSpine.goodListQuotient
#print axioms Kepler.Text.TameSpine.fstListOfFaces
#print axioms Kepler.Text.TameSpine.findFaceEq
#print axioms Kepler.Text.TameSpine.memFindFace
#print axioms Kepler.Text.TameLp.dart_in_face
-/
