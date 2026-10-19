/-
  Kepler.Text.TameSpine.TameList50 — B1 Tame_list 地基批 50：
  perm_eq_faces 章 + fst 词典块（tamespine-port-plan §4 批次表 B1 行；
  接续批 49 = TameList49.lean，批 49 终点 = HOL :13055；本批起点 =
  HOL :13060 `normal_list_perm_eq_faces`，章主体一件；尾段 fst 词典块
  随收至 :13155，自然边界 = :13158 `hypermap_of_quotient_list_final`
  （判批 51，接续点见尾注）。行号均按主仓 reference/flyspeck
  （commit 1ce0353）实测。

  四槽清点裁定（批 49 尾处方预记面的对拍结论）：

  - **uniq_flatten**（list_hypermap-compiled.hl:540 `uniq (flatten L) /\
    all (\l. ~(l = [])) L ==> uniq L`，外层表 nodup 形）：全库 grep
    确认在册仅三类——批 5 uniqFlattenUniq（tame_list.hl:3872 成员级
    `uniq (flatten L) /\ MEM s L ==> uniq s`，另一语句形）、批 9/批 10
    private nodupOfFlattenNodup（同语句 private 不跨文件）→ 裁定本批
    公开泛型落地 uniqFlatten（批 9 同证重落 + 泛型 α 提升；头∉尾支
    批 9 的 nodupAppendFlattenContra 依赖就地换 flatten-Nodup 双成员
    算术直收）。
  - **uniq_list_of_faces**（list_hypermap-compiled.hl:863 `good_list L
    ==> uniq (list_of_faces L)`）：零载体 → 本批落地。HOL 证体
    map_inj_uniq/good_list_uniq 路线换 uniq_flatten 直投路线
    （list_of_darts = flatten (MAP list_pairs L) 定义式，GoodList.1
    即 flatten-Nodup，配全非空成员）；`list_pairs_empty` 槽（:73）↦
    私件 listPairsNeNil（length_zip 算术面，泛型 α）。
  - **find_face_eq**（list_hypermap-compiled.hl:1282——批 49 头注
    「:1257 后段」粗定位，本批实测 :1282）`uniq (list_of_darts L) /\
    MEM d (list_of_darts L) ==> (find_face L d = f <=> MEM f
    (list_of_faces L) /\ MEM d f)`：零载体 → 本批落地。正向两槽 =
    memFindFace（批 49）+ dart_in_face（TameLp:3824）逐字；反向 =
    `find_pair_list_unique` 槽（list_hypermap-compiled.hl:234；批 11
    private findPairListSpine_unique 同证内联重落：find? 分派 none 支
    矛盾/some 支 `uniq_imp_unique_list` 槽 ↦ flatten_nodup_inj
    （TameLp:3795 公开件，双面含同一 dart → 相等））+ `find_face_alt`
    槽（:86）= findFaceDarts 定义式（find? 形即 alt 形零距离）+
    listPairs 单射槽 = 批 11 private listPairsInj 同域件，本批经
    fstListPairs（core map_fst_zip，见下）公开落地。
  - **uniq_perm_eq_map**（tame_list.hl:822 `!x y. uniq x /\ uniq y /\
    set_of_list x = set_of_list y ==> perm_eq x y`）：侦察确认零载体 →
    本批落地。载体 perm_eq = core `List.Perm`（批 48 既档），
    set_of_list 等 = `{d | d ∈ _}` 集合等式（批 47 finalListComplete
    载体约定）；证明件 = batteries `List.perm_ext_iff_of_nodup`
    （Batteries/Data/List/Perm.lean:145 `Nodup l1 → Nodup l2 →
    (l1 ~ l2 ↔ ∀ a, a ∈ l1 ↔ a ∈ l2)`）薄封装——HOL 证体
    Seq.uniq_perm_eq 槽即其同证件（batteries 在册，零重落）。

  fst 词典块侦察（批 49 尾处方开工先核；core/mathlib/batteries 三处
  grep 清点）：**fst_zip**（tame_list.hl:13118 `!s t. sizel s <= sizel
  t ==> MAP FST (zip s t) = s`）↦ core **List.map_fst_zip**（leanprover
  v4.32.2 Init/Data/List/Zip.lean:314，逐字同语句）——**零镜像记档**
  （批 48 rot_eq_nil 纯消费 core 体例）；mathlib Zip.lean/batteries 无
  同名件（mathlib Zip.lean:126 仅消费面，Plausible 同）。本批落地
  **fst_list_pairs**（:13131 `!s. MAP FST (list_pairs s) = s`，泛型
  α；批 11 private listPairsMapFst 同域件公开重落，证体换 core
  map_fst_zip + rotate 桥私件 listPairsZipRotate——批 49 §0
  rotateOneEq 同证重落）与 **fst_list_of_faces**（:13143
  `!L. MAP (MAP FST) (list_of_faces L) = L`，泛型 α；ENOUGH_TO_SHOW
  `MAP (MAP FST o list_pairs) L = MAP I L` 槽逐字折算为 map_map +
  map_congr_left + map_id 三步）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:13060-:13155）：

  章主体：`normal_list_perm_eq_faces` :13060 `!L N. good_list L /\
  normal_list L N /\ all (final_list L) N /\ is_edge_nondegenerate
  (hypermap_of_list L) /\ all uniq L /\ connected_hypermap
  (hypermap_of_list L) /\ ~(N = []) /\ all (\r. MEM r (list_of_faces
  L)) N ==> perm_eq N (list_of_faces L)` ↦ `normalListPermEqFaces`
  （真证；uniq_perm_eq_map 承接 = 本批 uniqPermEqMap，Perm 载体）。
  HOL 证体逐槽：
  - `uniq N` 槽 = MATCH_MP uniq_flatten + normal_list 定义展开前两合
    取项（HOL ASM_MESON_TAC[normal_list] 面）↦ uniqFlatten（本批 §2）+
    NormalListSpine .1/.2.1 投影（批 5 定义）；
  - `uniq (list_of_faces L)` 槽 = uniq_list_of_faces ↦ uniqListOfFaces
    （本批 §2）；
  - EXTENSION/IN_SET_OF_LIST 面 ↦ `Set.ext` + `{d | d ∈ _}` 载体
    （批 47 约定）；正向 all(\r. MEM r (list_of_faces L)) N 槽 =
    hmem 前提直取（Seq.allP 面零镜像）；
  - 反向 = INTRO_TAC final_list_complete（tame_list.hl:12760）↦ 批 47
    finalListComplete（connected/非空/normal/all-final 四前提逐字），
    darts 资格 = MEM_HD 面 ↦ List.head!_mem_self + list_of_darts_alt
    面（mem_flatten，批 5 载体）+ 集合等式 subset 搬运；
  - `find_face L (HD x) = x` / `= l` 双槽（:13107/:13112）=
    find_face_eq ×2 ↦ findFaceEq（本批 §2）双 .mpr（enough_to_show
    面的 x = l 由 find_face 单值性合流收口）。
  `~(N = [])`、`all uniq L`、`is_edge_nondegenerate` 三前提 HOL 证体
  未消费，逐字随语句入册（纯前提保真，零证体负担）。

  新落地载体：零（四槽 + fst 双件 + 章主体皆 mirror 落地；两私件为
  批 49 rotateOneEq 同证重落 + list_pairs_empty 对偶面，不占新领土）。

  诚实记账：七件全真证（uniqFlatten/uniqPermEqMap/uniqListOfFaces/
  findFaceEq/fstListPairs/fstListOfFaces/normalListPermEqFaces），
  零新 def、零 sorry、零止损件、零记账债。范围决策：批 50 射程收口
  至 :13155（章主体 + 四槽 + fst 词典块，自然边界）；备选件 :13158
  `hypermap_of_quotient_list_final` 判批 51——需 final_list_quotient
  （批 47 finalListQuotient 已册）+ `hypermap_of_list_perm`
  （list_hypermap_iso-compiled.hl，在册性未侦察）+ Seq2.perm_eq_map
  面 + perm_eq_sym 面 + 本批 fst_list_of_faces。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 51 接续点：HOL :13158 `hypermap_of_quotient_list_final`
  （:13158-:13190，quotient 收官后的 hypermap 同一 capstone；槽
  hypermap_of_list_perm/perm_eq_map/perm_eq_sym 清点先核，
  finalListQuotient/fstListOfFaces 批 47/本批直投）。
-/

import Kepler.Text.TameSpine.TameList49

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList listOfDarts listPairs findFaceDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList dart_in_face findFaceDarts_none
  findFaceDarts_some flatten_nodup_inj flatten_nodup_mem)

/-! ### §0 私件（zip/rotate 桥 + list_pairs 非空；private 不跨文件，
批 49 §0 体例同证重落） -/

/-- `listPairs` 的 zip/rotate 桥（批 49 §0 rotateOneEq 同证重落为
泛型桥件；HOL `list_pairs` 定义 `zip list (rot 1 list)` 的 n = 1
内联面，ssreflect `rot n s = drop n s ++ take n s`）。 -/
private theorem listPairsZipRotate {α : Type*} (l : List α) :
    listPairs l = l.zip (l.rotate 1) := by
  cases l with
  | nil => rfl
  | cons a t =>
    cases t with
    | nil => simp [listPairs, List.rotate]
    | cons b s =>
      have hmod : 1 % (s.length + 2) = 1 := Nat.mod_eq_of_lt (by omega)
      simp [listPairs, List.rotate, hmod]

/-- `listPairs` 非空面（HOL `list_pairs_empty`
list_hypermap-compiled.hl:73 `list_pairs s = [] <=> s = []` 的非空向；
length_zip 算术路线）。 -/
private theorem listPairsNeNil {α : Type*} {l : List α} (hne : l ≠ []) :
    listPairs l ≠ [] := by
  intro hc
  have h1 : (l.drop 1 ++ l.take 1).length = l.length := by simp; omega
  have h3 : (listPairs l).length = l.length := by
    show (l.zip (l.drop 1 ++ l.take 1)).length = l.length
    rw [List.length_zip, h1]
    simp
  rw [hc] at h3
  simp at h3
  exact hne (List.length_eq_zero_iff.mp h3.symm)

/-! ### §1 fst 词典块（tame_list.hl:13118-:13155；fst_zip = core
List.map_fst_zip 零镜像记档，见头注） -/

/-- **HOL `fst_list_pairs`**（tame_list.hl:13131-:13141）`!s. MAP FST
(list_pairs s) = s`——rotate 桥（本批 §0）+ core `List.map_fst_zip`
（fst_zip 槽直投：length_rotate 供 `sizel s <= sizel (rot 1 s)` 面，
HOL Seq.size_rot 槽零镜像）；批 11 private listPairsMapFst 同域件
公开重落。 -/
theorem fstListPairs {α : Type*} (l : List α) :
    (listPairs l).map Prod.fst = l := by
  rw [listPairsZipRotate, List.map_fst_zip (by rw [List.length_rotate])]

/-- **HOL `fst_list_of_faces`**（tame_list.hl:13143-:13155）`!L. MAP
(MAP FST) (list_of_faces L) = L`——ENOUGH_TO_SHOW 槽
`MAP (MAP FST o list_pairs) L = MAP I L` 逐字折算：map_map 平铺 +
map_congr_left 逐点 fstListPairs + map_id 收口（MAP_I/I_THM 槽零
镜像）。 -/
theorem fstListOfFaces {α : Type*} (L : List (List α)) :
    (L.map listPairs).map (fun r => r.map Prod.fst) = L := by
  calc (L.map listPairs).map (fun r => r.map Prod.fst)
      = L.map (fun l => (listPairs l).map Prod.fst) := by
        rw [List.map_map]
        rfl
    _ = L.map id := List.map_congr_left fun l _ => fstListPairs l
    _ = L := List.map_id L

/-! ### §2 四槽件（批 49 尾处方清点裁定，见头注） -/

/-- **HOL `uniq_flatten`**（list_hypermap-compiled.hl:540）`uniq
(flatten L) /\ all (\l. ~(l = [])) L ==> uniq L`——flatten cons 分解 +
nodup_append 拆块：ih 支 sublist 面降幂；头∉尾支 = flatten-Nodup 双
成员算术直收（批 9 nodupOfFlattenNodup 同证重落 + 泛型 α 提升，
private 不跨文件雷区既档）。 -/
theorem uniqFlatten {α : Type*} {L : List (List α)}
    (hun : L.flatten.Nodup) (hn : ∀ l ∈ L, l ≠ []) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    rw [List.flatten_cons] at hun
    obtain ⟨_, h2, h3⟩ := List.nodup_append.mp hun
    rw [List.nodup_cons]
    refine ⟨fun ha => ?_, ih h2 (fun x hx => hn x (List.mem_cons_of_mem _ hx))⟩
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil a (hn a (List.mem_cons_self ..))
    exact absurd rfl (h3 z hz z (List.mem_flatten.mpr ⟨a, ha, hz⟩))

/-- **HOL `uniq_perm_eq_map`**（tame_list.hl:822-:828）`!x y. uniq x /\
uniq y /\ set_of_list x = set_of_list y ==> perm_eq x y`——perm_eq 载体
= core `List.Perm`（批 48 既档）、set_of_list 等 = `{d | d ∈ _}` 集合
等式（批 47 载体约定）；证明件 = batteries `List.perm_ext_iff_of_
nodup`（Perm.lean:145）薄封装，HOL Seq.uniq_perm_eq 槽即其同证件。 -/
theorem uniqPermEqMap {α : Type*} {x y : List α}
    (hx : x.Nodup) (hy : y.Nodup)
    (h : {d | d ∈ x} = {d | d ∈ y}) : x.Perm y := by
  refine (List.perm_ext_iff_of_nodup hx hy).mpr fun a => ⟨fun hxa => ?_,
    fun hya => ?_⟩
  · exact h.subset hxa
  · exact h.symm.subset hya

/-- **HOL `uniq_list_of_faces`**（list_hypermap-compiled.hl:863-:868）
`good_list L ==> uniq (list_of_faces L)`——uniq_flatten 直投路线：
GoodList.1 即 `(L.map listPairs).flatten.Nodup`（list_of_darts 定义
式，批 5 载体）+ 全非空成员（`list_pairs_empty` 槽 ↦ §0
listPairsNeNil）；HOL map_inj_uniq/good_list_uniq 路线的对拍记档见
头注。 -/
theorem uniqListOfFaces {L : fgraph ℕ} (hL : GoodList L) :
    (L.map listPairs).Nodup := by
  refine uniqFlatten hL.1 ?_
  intro q hq
  obtain ⟨l, hl, hql⟩ := List.mem_map.mp hq
  intro hc
  have hlne : l ≠ [] := hL.2.1 l hl
  have hq0 : listPairs l = [] := hql.trans hc
  exact absurd hq0 (listPairsNeNil hlne)

/-- **HOL `find_face_eq`**（list_hypermap-compiled.hl:1282-:1300）
`uniq (list_of_darts L) /\ MEM d (list_of_darts L) ==> (find_face L d
= f <=> MEM f (list_of_faces L) /\ MEM d f)`——正向 = memFindFace
（批 49，mem_find_face 槽）+ dart_in_face（TameLp:3824）逐字；反向 =
find? 分派：none 支 `find?_eq_none` 矛盾收，some 支 find_pair_list_
unique 面（list_hypermap-compiled.hl:234；`uniq_imp_unique_list` 槽
↦ flatten_nodup_inj 双面同 dart 相等）+ listPairs 单射槽 ↦ 本批
fstListPairs + `find_face_alt` 槽（:86）= findFaceDarts 定义式。 -/
theorem findFaceEq {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) (f : List (ℕ × ℕ)) :
    findFaceDarts L d = f ↔ f ∈ L.map listPairs ∧ d ∈ f := by
  constructor
  · intro hcon
    refine ⟨?_, ?_⟩
    · rw [← hcon]
      exact memFindFace L hd
    · rw [← hcon]
      exact dart_in_face L d |>.mpr hd
  · intro hpair
    obtain ⟨l, hl, hfl⟩ := List.mem_map.mp hpair.1
    obtain rfl : listPairs l = f := hfl
    by_cases hval : L.find? (fun l => decide (d ∈ listPairs l)) = none
    · exfalso
      have h9 := List.find?_eq_none.mp hval l hl
      simp only [decide_eq_true_eq] at h9
      exact h9 hpair.2
    · obtain ⟨l₀, hl₀⟩ := Option.ne_none_iff_exists.mp hval
      have hfeq : L.find? (fun l => decide (d ∈ listPairs l)) = some l₀ :=
        hl₀.symm
      obtain ⟨hfl₀, hdl₀, hl₀mem⟩ := findFaceDarts_some hfeq
      have hinj : listPairs l₀ = listPairs l :=
        flatten_nodup_inj hL.1 (List.mem_map.mpr ⟨l₀, hl₀mem, rfl⟩)
          (List.mem_map.mpr ⟨l, hl, rfl⟩) hdl₀ hpair.2
      rw [hfl₀]
      have hl₀l : l₀ = l := (fstListPairs l₀).symm.trans (hinj ▸ fstListPairs l)
      rw [hl₀l]

/-! ### §3 normal_list_perm_eq_faces 章（tame_list.hl:13060-:13115） -/

/-- **HOL `normal_list_perm_eq_faces`**（tame_list.hl:13060-:13115，
章主体）`!L N. good_list L /\ normal_list L N /\ all (final_list L) N
/\ is_edge_nondegenerate (hypermap_of_list L) /\ all uniq L /\
connected_hypermap (hypermap_of_list L) /\ ~(N = []) /\ all (\r. MEM r
(list_of_faces L)) N ==> perm_eq N (list_of_faces L)` ↦
`normalListPermEqFaces`（真证；perm_eq 载体 = core `List.Perm`，批 48
既档）。证体逐槽见模块头注：uniq_perm_eq_map 承接（本批 §2）+ 前两
槽 uniqFlatten/uniqListOfFaces 直投 + 反向 finalListComplete（批 47）
集合搬运 + findFaceEq 双 .mpr 合流。 -/
theorem normalListPermEqFaces (L : fgraph ℕ) {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (hnorm : NormalListSpine hL N)
    (hfinal : ∀ r ∈ N, finalListSpine L r)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup)
    (hconn : (hypermapOfList L hL).Connected)
    (hne : N ≠ [])
    (hmem : ∀ r ∈ N, r ∈ L.map listPairs) :
    N.Perm (L.map listPairs) := by
  -- uniq N / uniq (list_of_faces L) 两槽（uniq_flatten + uniq_list_of_faces）
  refine uniqPermEqMap (uniqFlatten hnorm.1 hnorm.2.1) (uniqListOfFaces hL) ?_
  -- EXTENSION/IN_SET_OF_LIST 面：{d | d ∈ N} = {d | d ∈ list_of_faces L}
  refine Set.ext fun d => ⟨hmem d, fun hd => ?_⟩
  obtain ⟨l, hl, hdl⟩ := List.mem_map.mp hd
  have hlne : l ≠ [] := hL.2.1 l hl
  have hdne : listPairs l ≠ [] := listPairsNeNil hlne
  have hhdd : (listPairs l).head! ∈ listPairs l := List.head!_mem_self hdne
  -- HD x ∈ list_of_darts L 槽（list_of_darts_alt + mem_flatten 面）
  have hdart : (listPairs l).head! ∈ listOfDarts L :=
    List.mem_flatten.mpr ⟨listPairs l, List.mem_map.mpr ⟨l, hl, rfl⟩, hhdd⟩
  -- final_list_complete 槽：set_of_list (flatten N) = darts_of_list L
  have hflat : (listPairs l).head! ∈ N.flatten :=
    (finalListComplete (L := L) (hL := hL) hconn hne hnorm hfinal).symm.subset hdart
  obtain ⟨s, hs, hhead⟩ := List.mem_flatten.mp hflat
  -- find_face L (HD x) = l / = x 双槽（find_face_eq ×2）→ x = l 合流
  have hfs : findFaceDarts L (listPairs l).head! = s :=
    (findFaceEq hL hdart s).mpr ⟨hmem s hs, hhead⟩
  have hfd : findFaceDarts L (listPairs l).head! = listPairs l :=
    (findFaceEq hL hdart (listPairs l)).mpr ⟨List.mem_map.mpr ⟨l, hl, rfl⟩, hhdd⟩
  rw [hfd, hdl] at hfs
  exact hfs ▸ hs

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；七件正文 + 批 47/批 49/TameLp 槽全绿
零 sorryAx——探针十一行：十一件仅 propext/Classical.choice/Quot.sound
标准三轴（uniqFlatten/uniqListOfFaces/findFaceEq/fstListPairs/
fstListOfFaces/memFindFace/dart_in_face/flatten_nodup_inj 八件双轴
[propext, Quot.sound]；uniqPermEqMap 经 batteries
perm_ext_iff_of_nodup 证体 + normalListPermEqFaces/finalListComplete
经 normalListComplete 批 46 消费链汇入 Classical.choice 三轴），
§0 两私件为 private 探针不可外引，其消费链经 uniqListOfFaces/
normalListPermEqFaces 轴面旁证零 sorry）：
#print axioms Kepler.Text.TameSpine.uniqFlatten
#print axioms Kepler.Text.TameSpine.uniqPermEqMap
#print axioms Kepler.Text.TameSpine.uniqListOfFaces
#print axioms Kepler.Text.TameSpine.findFaceEq
#print axioms Kepler.Text.TameSpine.fstListPairs
#print axioms Kepler.Text.TameSpine.fstListOfFaces
#print axioms Kepler.Text.TameSpine.normalListPermEqFaces
#print axioms Kepler.Text.TameSpine.finalListComplete
#print axioms Kepler.Text.TameSpine.memFindFace
#print axioms Kepler.Text.TameLp.dart_in_face
#print axioms Kepler.Text.TameLp.flatten_nodup_inj
-/
