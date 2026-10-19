/-
  Kepler.Text.TameSpine.TameList49 — B1 Tame_list 地基批 49：
  quotient 收官章（tamespine-port-plan §4 批次表 B1 行；接续批 48 =
  TameList48.lean，批 48 终点 = HOL :12998；本批起点 = HOL :13001
  `normal_list_as_list_of_faces`，章主体一件。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测。

  两缺口侦察与裁定（批 48 尾处方预记面的对拍结论）：

  - **缺口①**（`List_hypermap_iso.rot_hypermap_of_list_eq`，
    formal_lp/hypermap/ssreflect/list_hypermap_iso-compiled.hl:424
    `ALL2 (\f1 f2. ?n. f2 = rot n f1) L1 L2 /\ uniq (list_of_darts L1)
    ==> hypermap_of_list L2 = hypermap_of_list L1`）：全库 grep（含
    LocalAuto 族 + core v4.32.2/mathlib/batteries 三处）确认 Lean 零
    载体——**裁定自证，规模为小链**。侦察发现证体大半槽链已在册：
    `find_face`/`f_list`/`n_list`/`e_list` 定义层与
    `uniq_find_face`（list_hypermap-compiled.hl:244）↦ TameLp S1 层
    findFaceDarts_nodup（TameLp:3901）、`dart_in_face`（
    list_hypermap-compiled.hl 侧同域件）↦ TameLp dart_in_face
    （:3824）、超映射记录等式 ↦ 公开件 `Hypermap.ext'`
    （Hypermap.lean:3349，`lemma_hypermap_eq` 结构版：dart 集 + 三
    置换决定）；`perm_eq` 面 = 批 48 已决 `List.Perm` 载体 + 批 48
    perm_eq_set_of_list_eq 面（`Set.ext` + Perm.mem_iff）同款；
    `next_el_rot_eq`/`prev_el_rot_eq`（seq2-compiled.hl:1866/:1909）
    一般 n 形 ↦ la7_nextEl_rotOne/la7_prevEl_rotOne（n = 1，
    TameLp:4287/:4306）归纳提升——Assembly.lean 有 private 同证件
    ell_prevEl_rotate（:1714）/ell_nextEl_rotate（:1726）/
    ell_listPairs_rotate（:1745），private 不跨文件（雷区既档），
    本批按批 48 §0 体例同证重落；`rot_list_pairs`
    （list_hypermap-compiled.hl:1225 `rot n (list_pairs s) =
    list_pairs (rot n s)`）重落为 listPairsRotate（ell_listPairs_
    rotate 同证件，经 `List.zipWith_rotate_distrib`
    mathlib Rotate.lean:186）。全新自证四件：rotListOfDartsPerm
    （:413 rot_list_of_darts_perm）、findFaceRot（:399 find_face_rot）、
    rotHypermapOfListEq（:424 capstone）、memFindFace（:107
    mem_find_face）。载体语义记档：rotHypermapOfListEq 的 Lean 形加
    `hL2 : GoodList L2` 显式证人前提——HOL 无类型无此前提
    （`uniq (list_of_darts L1)` ↦ hL1.1），而 Lean `hypermapOfList`
    消费侧两侧均需 GoodList；本批消费点（:13001）两侧证人由
    goodListQuotient 项式直投，终语句零收窄。
  - **缺口②**（quotient 级 `hypermap_of_list` 需
    `GoodList (quotientListSpine L N')` 证人，两案裁定——**合流**）：
    证人产制面复用在册件，零新载体件——批 10 goodListQuotient
    （TameList10.lean:816-821，HOL `good_list_quotient`
    tame_list.hl:7152-:7166）恰为 `GoodList (quotientListSpine L N)`
    的三合取组装件（listOfDartsQuotientUniq / quotientAllNonnil /
    listOfDartsQuotientSym），前提（GoodList L + NormalListSpine +
    EdgeNondegenerate + all uniq L）与 :13001 语境逐字相合，N' 侧由
    normalListRot（批 48）供 NormalListSpine 后同件直投；陈述形面改
    **存在证人形**——批 48 尾处方两案中的存在证人形：GoodList 证人
    以 `∃` 显式绑定进终语句（hypermapOfList 消费必需，HOL 无类型无
    此前提的载体语义缺口由此封闭），证人在证明内由 goodListQuotient
    项式直投，无额外产制负担。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:13001-:13055）：

  件零（§1 槽链四件，见缺口①）。

  件一（章主体）：`normal_list_as_list_of_faces` :13001
  `!L N. good_list L /\ normal_list L N /\ all (final_list L) N /\
  ~(N=[]) /\ is_edge_nondegenerate (hypermap_of_list L) /\
  all uniq L ==> (?N'. normal_list L N' /\ all (final_list L) N' /\
  ~(N'=[]) /\ hypermap_of_list (quotient_list L N') =
  hypermap_of_list (quotient_list L N) /\ all (\r. MEM r
  (list_of_faces L)) N')` ↦ `normalListAsListOfFaces`（真证；
  `hypermap_of_list (quotient_list L _)` 槽的 GoodList 证人按缺口②
  裁定以 `∃ hQ'` 显式绑定，RHS 侧证人项式直投）。HOL 证体七段逐槽：
  - 选择段（`!r. ?nv. MEM r N ==> rot nv r = find_face L (HD r)`，
    RIGHT_EXISTS_IMP_THM 面）+ SKOLEM_THM 槽 ↦ `Classical.choose`
    形（批 48 尾在册决定）；`final_list_rot`（tame_list.hl:5097）槽
    ↦ 批 8 finalListRot（TameList8.lean:563，批 48 头注
    「final_list_rot = 本批 rotFinalList」系误记：rotFinalList =
    :12831 rot_final_list，:5097 final_list_rot 另有批 8 在册件，
    本批对拍更正记档）；`normal_list_uniq_nonnil` 槽 = 批 6
    normalListUniqNonnil、`MEM_HD` 面 ↦ `List.head!_mem_self`、
    `normal_list_list_of_darts` 槽（:3643）= 批 5
    normalListListOfDarts + `Seq2.mem_flatten` ↦ List.mem_flatten；
  - witness 段 `MAP (\r. rot (nv r) r) N` + ALL2 面 ↦ 批 48
    all2Map2（ALL2_MAP2 :12991）.mpr 直拼；
  - `MAP_EQ_NIL` 非空搬运 ↦ `List.map_eq_nil_iff`；
  - normal_list / all-final 两槽 = 批 48 normalListRot /
    allFinalListRot 直投；
  - 超映射等式槽 = 本批 rotHypermapOfListEq + `list_of_darts_
    quotient_uniq` 槽 = 批 10 listOfDartsQuotientUniq（经
    goodListQuotient 进证人）+ `quotient_list_rot` 槽 = 批 48
    quotientListRot（HOL :12962；结论序恰为 rot_hypermap_of_list_eq
    所需 N 前N' 后形）；
  - 尾段 `all (\r. MEM r (list_of_faces L)) N'`（GSYM Seq.allP +
    MEM_MAP 面）↦ `∀ r ∈ N', r ∈ L.map listPairs`：witness 项经
    hnv 写成 find_face L (HD r) ↦ findFaceDarts L r.head!，本批
    memFindFace 收口（`List_hypermap.mem_find_face` 面）；批 48 尾
    在册决定「List_hypermap.mem_find_face = TameLp dart_in_face」
    对拍更正记档：dart_in_face 是 `MEM d (find_face L d) <=> MEM d
    (list_of_darts L)` 对偶面，mem_find_face 是 `MEM (find_face L d)
    (list_of_faces L)` 属局面，两者互补不互换，本批 memFindFace
    镜像后者。
  `list_of_faces` 面（list_hypermap-compiled.hl:26 `MAP list_pairs L`）
  ↦ `L.map listPairs`（fgraph ℕ 面载体是点表，批 5 载体决定既档）。

  新落地载体：零（缺口②证人产制在册复用 + 陈述形存在证人形记档；
  缺口① hL2 显式证人为陈述形载体语义记档，非新载体件；§0 三私件为
  Assembly ell_* 同证重落 + TameLp la7 归纳式，不占新领土）。

  诚实记账：五件全真证（rotListOfDartsPerm/findFaceRot/memFindFace/
  rotHypermapOfListEq/normalListAsListOfFaces），零新 def、零 sorry、
  零止损件、零记账债。范围决策：批 49 射程收口至 :13055（:13001 章
  主体 + 两缺口，自然边界）；备选件 :13060 `normal_list_perm_eq_faces`
  判批 50——四槽清点：`uniq_flatten`/`uniq_list_of_faces`/
  `find_face_eq`（list_hypermap-compiled.hl:1257 后段）在册性未核、
  `uniq_perm_eq_map` 未侦察，另需 connected_hypermap 前提（批 46 章
  面）；:13118 `fst_zip`（`sizel s <= sizel t ==> MAP FST (zip s t)
  = s`，sizel/zip 小件）判批 50 候选——mathlib zip 词典块
  （List.zip_map_fst 族）开工先侦察。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 50 接续点：HOL :13060 `normal_list_perm_eq_faces`（槽 uniq_flatten/
  uniq_list_of_faces/find_face_eq/uniq_perm_eq_map 清点先核，批次表
  尾段同章候选 :13118 fst_zip/:13126 fst_list_pairs 小件随收）。
-/

import Kepler.Text.TameSpine.TameList48

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList listOfDarts listPairs findFaceDarts eList nList
  fList nextEl prevEl)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList dart_in_face findFaceDarts_none
  findFaceDarts_some findFaceDarts_nodup la7_nextEl_rotOne la7_prevEl_rotOne
  darts_hypermapOfList edgeMap_hypermapOfList nodeMap_hypermapOfList
  faceMap_hypermapOfList)

/-! ### §0 旋转私件重落（private 不跨文件；Assembly ell_* 同证 +
TameLp la7 归纳式提升，批 48 §0 体例） -/

/-- `l.rotate 1` 的 drop/take 内联形（Assembly ell_rotateOne 同证重落）。 -/
private theorem rotateOneEq (l : List ℕ) : l.rotate 1 = l.drop 1 ++ l.take 1 := by
  cases l with
  | nil => simp [List.rotate]
  | cons a t =>
    cases t with
    | nil => simp [List.rotate]
    | cons b s =>
      have hmod : 1 % (s.length + 2) = 1 := Nat.mod_eq_of_lt (by omega)
      simp [List.rotate, hmod]

/-- `listPairs` 与 `rotate` 交换（HOL `rot_list_pairs`
list_hypermap-compiled.hl:1225 `rot n (list_pairs s) = list_pairs
(rot n s)` 的 rotate 形；Assembly ell_listPairs_rotate 同证重落，
mathlib `List.zipWith_rotate_distrib` 搬面）。 -/
private theorem listPairsRotate (l : List ℕ) (n : ℕ) :
    listPairs (l.rotate n) = (listPairs l).rotate n := by
  have hlen : l.length = (l.drop 1 ++ l.take 1).length := by simp; omega
  have hfold : listPairs l = List.zipWith Prod.mk l (l.drop 1 ++ l.take 1) :=
    List.zip_eq_zipWith
  calc listPairs (l.rotate n)
      = List.zipWith Prod.mk (l.rotate n) ((l.rotate n).drop 1 ++ (l.rotate n).take 1) :=
        List.zip_eq_zipWith
    _ = List.zipWith Prod.mk (l.rotate n) ((l.rotate n).rotate 1) := by
        rw [rotateOneEq]
    _ = List.zipWith Prod.mk (l.rotate n) (l.rotate (n + 1)) := by rw [List.rotate_rotate]
    _ = List.zipWith Prod.mk (l.rotate n) ((l.rotate 1).rotate n) := by
        rw [List.rotate_rotate, Nat.add_comm]
    _ = (List.zipWith Prod.mk l (l.rotate 1)).rotate n :=
        (List.zipWith_rotate_distrib Prod.mk l (l.rotate 1) n
          (List.length_rotate l 1).symm).symm
    _ = (List.zipWith Prod.mk l (l.drop 1 ++ l.take 1)).rotate n := by rw [rotateOneEq l]
    _ = (listPairs l).rotate n := by rw [hfold]

/-- `prevEl` 的旋转不变式（一般 n；HOL `Seq2.prev_el_rot_eq`
seq2-compiled.hl:1909；Assembly ell_prevEl_rotate 同证重落，la7
n = 1 件归纳提升）。 -/
private theorem prevElRotateFunc {l : List (ℕ × ℕ)} (hn : l.Nodup) (n : ℕ)
    {x : ℕ × ℕ} (hx : x ∈ l) : prevEl (l.rotate n) x = prevEl l x := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc prevEl (l.rotate (k + 1)) x
        = prevEl ((l.rotate k).rotate 1) x := by rw [List.rotate_rotate]
      _ = prevEl (l.rotate k) x :=
          la7_prevEl_rotOne (List.nodup_rotate.mpr hn) (List.mem_rotate.mpr hx)
      _ = prevEl l x := ih

/-- `nextEl` 的旋转不变式（一般 n；HOL `Seq2.next_el_rot_eq`
seq2-compiled.hl:1866；Assembly ell_nextEl_rotate 同证重落，la7
n = 1 件归纳提升）。 -/
private theorem nextElRotateFunc {l : List (ℕ × ℕ)} (hn : l.Nodup) (n : ℕ)
    (x : ℕ × ℕ) : nextEl (l.rotate n) x = nextEl l x := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc nextEl (l.rotate (k + 1)) x
        = nextEl ((l.rotate k).rotate 1) x := by rw [List.rotate_rotate]
      _ = nextEl (l.rotate k) x :=
          la7_nextEl_rotOne (List.nodup_rotate.mpr hn) x
      _ = nextEl l x := ih

/-! ### §1 缺口①槽链（list_hypermap_iso-compiled.hl:399-:451） -/

/-- **HOL `rot_list_of_darts_perm`**（list_hypermap_iso-compiled.hl
:413-:422）`ALL2 (\f1 f2. ?n. f2 = rot n f1) L1 L2 ==> perm_eq
(list_of_darts L1) (list_of_darts L2)`——Forall₂ induction；cons 支
`list_of_darts` 定义展开（foldr 面 ↦ map/flatten，批 5 载体）+
listPairsRotate + core `List.Perm.append` 拼接 + mathlib
`List.rotate_perm`（Rotate.lean:156）；基座支 `Perm.refl` 定义式。 -/
theorem rotListOfDartsPerm {L1 L2 : fgraph ℕ}
    (h : List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n) L1 L2) :
    (listOfDarts L1).Perm (listOfDarts L2) := by
  induction h with
  | nil => exact List.Perm.refl _
  | @cons h1 h2 t1 t2 hab _ ih =>
    obtain ⟨n, hn⟩ := hab
    simp only [listOfDarts, List.map_cons, List.flatten_cons, hn, listPairsRotate]
    exact List.Perm.append (List.rotate_perm _ n).symm ih

/-- **HOL `find_face_rot`**（list_hypermap_iso-compiled.hl:399-:412）
`ALL2 (\f1 f2. ?n. f2 = rot n f1) L1 L2 ==> ?n. find_face L2 d =
rot n (find_face L1 d)`——Forall₂ induction；cons 支 `find_face_cons`
面（list_hypermap-compiled.hl:1275）↦ `List.find?_cons` 分派 +
listPairsRotate 双向成员搬运；基座支 rot_nil 面 = `List.rotate_zero`。 -/
theorem findFaceRot {L1 L2 : fgraph ℕ}
    (h : List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n) L1 L2) :
    ∀ d : ℕ × ℕ, ∃ n, findFaceDarts L2 d = (findFaceDarts L1 d).rotate n := by
  induction h with
  | nil => intro d; exact ⟨0, by rw [List.rotate_zero]⟩
  | @cons h1 h2 t1 t2 hab _ ih =>
    obtain ⟨n, hn⟩ := hab
    intro d
    by_cases hd : d ∈ listPairs h1
    · have hd2 : d ∈ listPairs h2 := by
        rw [hn, listPairsRotate]
        exact List.mem_rotate.mpr hd
      have e1 : ((h1 :: t1).find? fun l => decide (d ∈ listPairs l)) = some h1 := by
        simp [hd]
      have e2 : ((h2 :: t2).find? fun l => decide (d ∈ listPairs l)) = some h2 := by
        simp [hd2]
      have f1 : findFaceDarts (h1 :: t1) d = listPairs h1 := by
        show listPairs (((h1 :: t1).find? fun l => decide (d ∈ listPairs l)).getD [])
            = listPairs h1
        rw [e1]
        rfl
      have f2 : findFaceDarts (h2 :: t2) d = listPairs h2 := by
        show listPairs (((h2 :: t2).find? fun l => decide (d ∈ listPairs l)).getD [])
            = listPairs h2
        rw [e2]
        rfl
      exact ⟨n, by rw [f2, f1, hn, listPairsRotate]⟩
    · have hd2 : d ∉ listPairs h2 := by
        intro hc
        rw [hn, listPairsRotate] at hc
        exact hd (List.mem_rotate.mp hc)
      have e1 : ((h1 :: t1).find? fun l => decide (d ∈ listPairs l))
          = t1.find? fun l => decide (d ∈ listPairs l) := by
        simp [hd]
      have e2 : ((h2 :: t2).find? fun l => decide (d ∈ listPairs l))
          = t2.find? fun l => decide (d ∈ listPairs l) := by
        simp [hd2]
      have f1 : findFaceDarts (h1 :: t1) d = findFaceDarts t1 d := by
        show listPairs (((h1 :: t1).find? fun l => decide (d ∈ listPairs l)).getD [])
            = listPairs ((t1.find? fun l => decide (d ∈ listPairs l)).getD [])
        rw [e1]
      have f2 : findFaceDarts (h2 :: t2) d = findFaceDarts t2 d := by
        show listPairs (((h2 :: t2).find? fun l => decide (d ∈ listPairs l)).getD [])
            = listPairs ((t2.find? fun l => decide (d ∈ listPairs l)).getD [])
        rw [e2]
      obtain ⟨m, hm⟩ := ih d
      exact ⟨m, by rw [f2, f1, hm]⟩

/-- **HOL `mem_find_face`**（list_hypermap-compiled.hl:107）
`MEM d (list_of_darts L) ==> MEM (find_face L d) (list_of_faces L)`
——`find?` 分派两支：none 支经 `dart_in_face`（TameLp :3824）收矛盾；
some 支 `List.mem_map` 直拼。 -/
theorem memFindFace (L : fgraph ℕ) {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) :
    findFaceDarts L d ∈ L.map listPairs := by
  by_cases hval : L.find? (fun l => decide (d ∈ listPairs l)) = none
  · exact absurd (dart_in_face L d |>.mpr hd)
      (by rw [findFaceDarts_none hval]; simp)
  · obtain ⟨l', hl''⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : L.find? (fun l => decide (d ∈ listPairs l)) = some l' := hl''.symm
    exact List.mem_map.mpr ⟨l', List.mem_of_find?_eq_some hfeq,
      (findFaceDarts_some hfeq).1.symm⟩

/-- **HOL `rot_hypermap_of_list_eq`**（list_hypermap_iso-compiled.hl
:424-:451，缺口① capstone）`ALL2 (\f1 f2. ?n. f2 = rot n f1) L1 L2 /\
uniq (list_of_darts L1) ==> hypermap_of_list L2 = hypermap_of_list
L1`——载体语义记档：Lean 形加 `hL2 : GoodList L2` 显式证人前提
（hypermapOfList 消费侧两侧均需 GoodList，HOL 无类型无此前提；
消费点两侧由 goodListQuotient 直投，见头注）。证体：darts 字段 =
rotListOfDartsPerm + 批 48 perm_eq_set_of_list_eq 面（Perm.mem_iff）；
e/n/f 三置换字段 = `Hypermap.ext'`（Hypermap.lean:3349
lemma_hypermap_eq 结构版）+ 逐点 face_eq 槽（findFaceRot）+
prevElRotateFunc/nextElRotateFunc 换装（`uniq_find_face` 槽 ↦
TameLp findFaceDarts_nodup、`dart_in_face` 槽）；e_list 字段
L 无关直同。 -/
theorem rotHypermapOfListEq {L1 L2 : fgraph ℕ} (hL1 : GoodList L1)
    (hL2 : GoodList L2)
    (hall2 : List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n) L1 L2) :
    hypermapOfList L2 hL2 = hypermapOfList L1 hL1 := by
  have hperm := rotListOfDartsPerm hall2
  have hface := findFaceRot hall2
  have hpnf : ∀ d ∈ listOfDarts L1, nList L2 d = nList L1 d ∧ fList L2 d = fList L1 d := by
    intro d hd
    obtain ⟨n, hn⟩ := hface d
    have hmem : d ∈ findFaceDarts L1 d := dart_in_face L1 d |>.mpr hd
    have hnod : (findFaceDarts L1 d).Nodup := findFaceDarts_nodup hL1.1 d
    refine ⟨?_, ?_⟩
    · show eList (prevEl (findFaceDarts L2 d) d) = eList (prevEl (findFaceDarts L1 d) d)
      rw [hn, prevElRotateFunc hnod n hmem]
    · show nextEl (findFaceDarts L2 d) d = nextEl (findFaceDarts L1 d) d
      rw [hn, nextElRotateFunc hnod n d]
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
  have hset : {d | d ∈ listOfDarts L2} = {d | d ∈ listOfDarts L1} := by
    ext x
    exact hperm.mem_iff.symm
  have hdartmem : ∀ x : ℕ × ℕ,
      x ∈ (hypermapOfList L2 hL2).darts ↔ x ∈ (hypermapOfList L1 hL1).darts := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ ({d | d ∈ listOfDarts L2} : Set (ℕ × ℕ)) :=
        (hmemBridge L2 hL2 x).mp hx
      exact (hmemBridge L1 hL1 x).mpr (hset.subset hx')
    · intro hx
      have hx' : x ∈ ({d | d ∈ listOfDarts L1} : Set (ℕ × ℕ)) :=
        (hmemBridge L1 hL1 x).mp hx
      exact (hmemBridge L2 hL2 x).mpr (hset.symm.subset hx')
  have hdartL1 : ∀ x : ℕ × ℕ, x ∈ (hypermapOfList L2 hL2).darts →
      x ∈ listOfDarts L1 := by
    intro x hx
    have hx' : x ∈ ({d | d ∈ listOfDarts L2} : Set (ℕ × ℕ)) :=
      (hmemBridge L2 hL2 x).mp hx
    exact hset.subset hx'
  refine Kepler.Text.Hypermap.ext' ?_ ?_ ?_ ?_
  · ext x
    exact hdartmem x
  · refine Equiv.Perm.ext fun x => ?_
    by_cases hx : x ∈ (hypermapOfList L2 hL2).darts
    · have hx1 : x ∈ (hypermapOfList L1 hL1).darts := hdartmem x |>.mp hx
      rw [edgeMap_hypermapOfList L2 hL2 hx, edgeMap_hypermapOfList L1 hL1 hx1]
    · have hx1 : x ∉ (hypermapOfList L1 hL1).darts := fun hc => hx (hdartmem x |>.mpr hc)
      rw [(hypermapOfList L2 hL2).edgeMap_permutes x hx,
        (hypermapOfList L1 hL1).edgeMap_permutes x hx1]
  · refine Equiv.Perm.ext fun x => ?_
    by_cases hx : x ∈ (hypermapOfList L2 hL2).darts
    · have hx1 : x ∈ (hypermapOfList L1 hL1).darts := hdartmem x |>.mp hx
      rw [nodeMap_hypermapOfList L2 hL2 hx, nodeMap_hypermapOfList L1 hL1 hx1]
      exact (hpnf x (hdartL1 x hx)).1
    · have hx1 : x ∉ (hypermapOfList L1 hL1).darts := fun hc => hx (hdartmem x |>.mpr hc)
      rw [(hypermapOfList L2 hL2).nodeMap_permutes x hx,
        (hypermapOfList L1 hL1).nodeMap_permutes x hx1]
  · refine Equiv.Perm.ext fun x => ?_
    by_cases hx : x ∈ (hypermapOfList L2 hL2).darts
    · have hx1 : x ∈ (hypermapOfList L1 hL1).darts := hdartmem x |>.mp hx
      rw [faceMap_hypermapOfList L2 hL2 hx, faceMap_hypermapOfList L1 hL1 hx1]
      exact (hpnf x (hdartL1 x hx)).2
    · have hx1 : x ∉ (hypermapOfList L1 hL1).darts := fun hc => hx (hdartmem x |>.mpr hc)
      rw [(hypermapOfList L2 hL2).faceMap_permutes x hx,
        (hypermapOfList L1 hL1).faceMap_permutes x hx1]

/-! ### §2 normal_list_as_list_of_faces 章（tame_list.hl:13001-:13055） -/

/-- **HOL `normal_list_as_list_of_faces`**（tame_list.hl:13001-:13055，
章主体）`!L N. good_list L /\ normal_list L N /\ all (final_list L) N
/\ ~(N=[]) /\ is_edge_nondegenerate (hypermap_of_list L) /\ all uniq L
==> (?N'. normal_list L N' /\ all (final_list L) N' /\ ~(N'=[]) /\
hypermap_of_list (quotient_list L N') = hypermap_of_list
(quotient_list L N) /\ all (\r. MEM r (list_of_faces L)) N')` ↦
`normalListAsListOfFaces`（真证；`hypermap_of_list (quotient_list L
_)` 槽的 GoodList 证人按缺口②裁定以 `∃ hQ'` 显式绑定——存在证人
形，RHS 侧证人项式直投）。HOL 证体七段逐槽：选择段 = finalListRot
（批 8，final_list_rot :5097）+ normalListUniqNonnil（批 6）+
normalListListOfDarts（批 5）+ Classical choose 形（SKOLEM_THM 槽）；
witness `MAP (\r. rot (nv r) r) N` + ALL2 面 = all2Map2（批 48）.mpr；
`MAP_EQ_NIL` 非空搬运 ↦ List.map_eq_nil_iff；normal_list / all-final
两槽 = normalListRot/allFinalListRot（批 48）直投；超映射等式槽 =
rotHypermapOfListEq（本批 §1）+ quotientListRot（批 48，:12962）+
goodListQuotient（批 10，good_list_quotient :7152——缺口②在册复用
裁定，见头注）双侧证人直投；尾段 list_of_faces 属局面 = memFindFace
（本批 §1，mem_find_face 面）+ witness 项 hnv 换装。`all uniq L`
前提前折算 `∀ l ∈ L, l.Nodup`（Seq.all 面零镜像）。 -/
theorem normalListAsListOfFaces (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hnorm : NormalListSpine hL N)
    (hfinal : ∀ r ∈ N, finalListSpine L r) (hNne : N ≠ [])
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) :
    ∃ (N' : List (List (ℕ × ℕ))) (hQ' : GoodList (quotientListSpine L N')),
      NormalListSpine hL N' ∧ (∀ r ∈ N', finalListSpine L r) ∧ N' ≠ [] ∧
      hypermapOfList (quotientListSpine L N') hQ' =
        hypermapOfList (quotientListSpine L N)
          (goodListQuotient L hL hnorm hnedg hunL) ∧
      (∀ r ∈ N', r ∈ L.map listPairs) := by
  classical
  -- 选择段：!r. MEM r N ==> ?nv. rot nv r = find_face L (HD r)
  have hsub : ∀ r ∈ N, ∃ nv : ℕ, r.rotate nv = findFaceDarts L r.head! := by
    intro r hr
    obtain ⟨hun, hne⟩ := normalListUniqNonnil hnorm hr
    have hhd : r.head! ∈ r := List.head!_mem_self hne
    exact finalListRot hL (hfinal r hr) hhd hun
      (normalListListOfDarts hnorm r.head! (List.mem_flatten.mpr ⟨r, hr, hhd⟩))
  obtain ⟨nv, hnv⟩ : ∃ nv : List (ℕ × ℕ) → ℕ, ∀ r ∈ N,
      r.rotate (nv r) = findFaceDarts L r.head! :=
    ⟨fun r => if h : r ∈ N then Classical.choose (hsub r h) else 0,
      fun r hr => by
        show r.rotate (if h : r ∈ N then Classical.choose (hsub r h) else 0)
            = findFaceDarts L r.head!
        rw [dif_pos hr]
        exact Classical.choose_spec (hsub r hr)⟩
  -- witness + ALL2 面（ALL2_MAP2 槽）
  have hall2 : List.Forall₂ (fun f1 f2 => ∃ n, f2 = f1.rotate n) N
      (N.map (fun r => r.rotate (nv r))) :=
    (all2Map2 (fun r => r.rotate (nv r)) N).mpr fun r _ => ⟨nv r, rfl⟩
  -- normal_list / all-final 两槽（normal_list_rot / all_final_list_rot）
  have hnorm' : NormalListSpine hL (N.map (fun r => r.rotate (nv r))) :=
    normalListRot hnorm hfinal hall2
  have hfinal' : ∀ r ∈ N.map (fun r => r.rotate (nv r)), finalListSpine L r :=
    allFinalListRot hfinal hnorm hall2
  have hNne' : N.map (fun r => r.rotate (nv r)) ≠ [] := fun hc =>
    hNne (List.map_eq_nil_iff.mp hc)
  refine ⟨N.map (fun r => r.rotate (nv r)),
    goodListQuotient L hL hnorm' hnedg hunL, hnorm', hfinal', hNne', ?_, ?_⟩
  · -- 超映射等式槽（rot_hypermap_of_list_eq + quotient_list_rot）
    refine rotHypermapOfListEq
      (hL1 := goodListQuotient L hL hnorm hnedg hunL)
      (hL2 := goodListQuotient L hL hnorm' hnedg hunL) ?_
    exact quotientListRot hnorm hnedg hfinal hall2
  · -- 尾段：all (\r. MEM r (list_of_faces L)) N'
    intro r' hr'
    obtain ⟨r, hr, hr'eq⟩ := List.mem_map.mp hr'
    rw [← hr'eq, hnv r hr]
    refine memFindFace L ?_
    obtain ⟨hun, hne⟩ := normalListUniqNonnil hnorm hr
    exact normalListListOfDarts hnorm r.head!
      (List.mem_flatten.mpr ⟨r, hr, List.head!_mem_self hne⟩)

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；五件正文 + 批 48/批 10/批 8 槽预期
零 sorryAx——探针九行全绿：九件仅 propext/Classical.choice/
Quot.sound 标准三轴（all2Map2 零公理；Classical 轴自上游消费链
[TameLp S1 层/mathlib 件证体] 与本件 SKOLEM 选择段汇入，
rotListOfDartsPerm/findFaceRot/rotHypermapOfListEq 经
quotientListRot/goodListQuotient/finalListRot 同），§0 三私件为
private 探针不可外引，其消费链经 rotHypermapOfListEq 轴面旁证零
sorry）：
#print axioms Kepler.Text.TameSpine.rotListOfDartsPerm
#print axioms Kepler.Text.TameSpine.findFaceRot
#print axioms Kepler.Text.TameSpine.memFindFace
#print axioms Kepler.Text.TameSpine.rotHypermapOfListEq
#print axioms Kepler.Text.TameSpine.normalListAsListOfFaces
#print axioms Kepler.Text.TameSpine.quotientListRot
#print axioms Kepler.Text.TameSpine.goodListQuotient
#print axioms Kepler.Text.TameSpine.finalListRot
#print axioms Kepler.Text.TameSpine.all2Map2
-/
