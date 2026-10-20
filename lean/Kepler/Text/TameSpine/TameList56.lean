/-
  Kepler.Text.TameSpine.TameList56 — B1 Tame_list 地基批 56：
  final_list_snd_is_fst / is_restricted 章收口（tamespine-port-plan §4
  批次表 B1 行；接续批 55 = TameList55.lean，批 55 终点 = HOL :13803
  （FST_o_FST）/越章随收 :13863（indexToVertexList_nil 已落）；本批起点
  = HOL :13805 `final_list_snd_is_fst`。行号均按主仓 reference/flyspeck
  （commit 1ce0353）实测；批 55 尾注预记 :13805/:13831/:13865/:13875/
  :13900 五锚点与实测一致，零偏移。

  载体侦察裁定（批 55 尾注预记面的对拍结论）：

  - **final_list 载体既档**：`final_list L r`（tame_defs2.hl:138-:140
    `final_list L r <=> all (\d. f_list L d = next_el r d) r`）↦
    `finalListSpine`（批 7 TameList7.lean:481，定义形即逐点 ∀∈，零展开
    步）。**行号勘误入档**（批 31 头注体例）：批 55 尾注预记
    「tame_defs2.hl:142」实为注释内 removed-2014 变体行
    （:142-:145 `all (\p. sizel p = 1) (parts L r)`），活定义在 :138-:140；
    批 7 头注所记 :126 亦偏，一并勘误；normal_list 载体
    `NormalListSpine`（批 5 TameList5.lean:127，GoodList 参化形）与 HOL
    `normal_list L N /\ all uniq L` 前提形对拍：HOL `all uniq L` ↦
    `∀ l ∈ L, l.Nodup`（批 14 体例既档，独立前提，不入 NormalListSpine
    ——HOL normal_list 首合取是 `uniq (flatten N)` = NormalListSpine 第
    1 合取，两处 uniq 异面，批 55 预记「开工先核」命中：前提形为
    fgraph 面元素表 uniq，非 N.flatten）；`f_list_fst_snd` :6702 ↦ 批 10
    fListFstSnd（TameList10.lean:319）；`normal_list_list_of_darts`
    :3643 ↦ 批 5 normalListListOfDarts（TameList5.lean:146，loop_list
    合取项的 flatten 提升形）；mem_flatten 槽 = core List.mem_flatten；
    mem_next_el 槽 = TameLp `nextEl_mem_of_mem`（TameLp.lean:3614）——
    批 55 预记「批 3 memNextEl 为 private」先核命中：公开件原在 TameLp
   （section GenericList，{α} [BEq α] [LawfulBEq α] [DecidableEq α]，
    ℕ × ℕ 具体层实例自解，无批 53 隐式槽雷）。
  - **is_restricted 载体既档**：`is_restricted`（hypermap.hl:11174 八合取
    折取形）↦ `Hypermap.IsRestricted`（Hypermap.lean:9645，尾合取即
    `∀ x ∈ H.darts, 3 ≤ (H.face x).ncard`）+ 访问件
    `IsRestricted.three_le_ncard_face`（Hypermap.lean:9669，批 6
    isRestrictedNonnil/EListNondeg 同层）；`dart_hypermap_of_list`
    :4095 ↦ 批 5 dartHypermapOfList（TameList5.lean:445）；**两件
    List_hypermap 引擎件首落**：`mem_face_lemma`（list_hypermap.vhl:596）
    ↦ memFaceLemma、`card_face_of_list`（list_hypermap.vhl:1081）↦
    cardFaceOfList——前者消费批 31 faceRep（TameList31.lean:152）+
    TameLp findFaceDarts_eq_of_mem（TameLp.lean:3870，即 HOL
    find_pair_list_unique/find_face_alt 的 Lean 面）+ la7_length_listPairs
    （TameLp.lean:4431）；后者消费 face-轨道双向刻画（批 7/8/14 私件
    faceOrbitSubsetFindFace/faceTableSubsetFaceOrbit 惯例同证重推导，
    private 不跨文件雷区既档）+ findFaceDarts_nodup（TameLp.lean:3901，
    uniq_find_face 面）+ Set.ncard_coe_finset + List.toFinset_card_of_nodup
    （CARD (set_of_list) = sizel 面）。
  - **enumerator 载体半缺首落**：`enumAppend`（tame_defs2.hl:211）批 52
    enumAppendSpine 已落（TameList52.lean:192）；`enumBase`（tame_defs2.hl
    :208）/`enumerator`（tame_defs2.hl:218，LET_THM 两槽 + POWER）不在册
    ——本批新 def 二枚（enumBaseSpine/enumeratorSpine，逐句镜像，POWER ↦
    Function.iterate，upt ↦ Upt 批 2 载体）。
  - **replace 载体既档**：批 55 预记「replace 载体不在册先核」实测勘误：
    `replace`（tame_defs.hl:317-320）批 17 replaceSpine 已落
    （TameList17.lean:75，逐句镜像）；filter/has 面：Seq.filter ↦ core
    List.filter（decide 装箱，批 42 体例），`filter_nil`/`has_filter`
    合发 ↦ core List.filter_eq_nil_iff（`has P s` ↦ `∃ x ∈ s, P x`）。
  - **snd_setFinal 载体既档**：FORALL_PAIR_THM 语句形先核命中——HOL
    `!f. SND (setFinal f)` 的 f 即 pair（tame_defs.hl:379 `setFinal
    (vs,f) = (vs,T)`），Lean 侧 pair ↦ Face 结构（vertices/isFinal 字段
    对，批 2 setFinalAlt 载体），SND ↦ `.isFinal`，∀-pair 在 Lean 原生，
    结论 = 定义性 rfl（HOL REWRITE_TAC[setFinal] 一发的 Lean 面）。
  - **sizel 载体既档**：`sizel = LENGTH`（seq.vhl:159）↦ List.length；
    finalGraph/finals/nonFinals 面 = 批 2 既有 Kepler.Graphs（Graph.lean
    :116/:119/:125，finals = filter Face.final、nonFinals = filter
    (¬·.final)、Graph.final = nonFinals.isEmpty）。

  新雷区（本批实测记档）：
  - **Bool 载体 defs 的 simp only 展开 boundary**：`unfold
    enumeratorSpine at hx` 后 List.mem_map.mp 证人方程含 β-归约未展开的
    lambda 应用形（def 体 `map fun is => ...` 的 let 无 → 证人方程保持
    `(fun is => ...) is = x` 原文）——`rw [← hxis] at hnil` 后须
    `simp only [List.cons_append]` 一步做 β + `[0] ++ l` 双事（rw 不做
    β，List.singleton_append 虽 rfl 也打不进未 β 面；批 52「mem_range'
    泛化形」雷的证人方程面变体）。
  - **Graph.final 三层面名分割**：HOL finalGraph（谓词）在 Lean 是
    `Graph.final`（Bool 字段式 def，Graph.lean:125）而 `Face.final`
    （Graph.lean:53）是 `isFinal` 的别名 def——`filter Face.final` 与
    `fun f => !f.final` 两个 filter 谓词在 nonFinals/finals 各用其一，
    消费 List.filter_eq_self/filter_eq_nil_iff 时两侧谓词不换名直投
    （Face.final 可 defeq 展开 isFinal，simp 面各自独立，禁止跨件统一
    换名——否则 filter 谓词实例不匹配）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:13805-:13942，九件；
  越章载体二件 memFaceLemma/cardFaceOfList 自 list_hypermap.vhl 首落）：

  §1 主件：`final_list_snd_is_fst` :13805-:13829 ↦ finalListSndIsFst
    （真证；HOL 证体七行逐槽：REWRITE[final_list] ↦ finalListSpine
    定义形零展开；f_list_fst_snd ANTS 槽 = normalListListOfDarts +
    mem_flatten（HOL ASM_MESON_TAC[normal_list_list_of_darts;Seq.allP;
    Seq2.mem_flatten] 三发的 Lean 显式展开）；SUBST1_TAC o GSYM 槽 =
    FST 换装直投（ Lean mem_map.mpr 证人侧组装，免 HOL 中转方程）；
    MEMf_MAP 槽 = List.mem_map.mpr；Seq2.mem_next_el 槽 =
    TameLp nextEl_mem_of_mem——HOL 六步链 Lean 三步收口，机制简化
    记档非语义损失）。
  §2 is_restricted 章：`is_restricted_size_face` :13831-:13850 ↦
    isRestrictedSizeFace（真证；尾合取槽 three_le_ncard_face + darts 槽
    dartHypermapOfList + card_face_of_list 槽 + mem_face_lemma 槽四发
    逐句）；越章首落 memFaceLemma/cardFaceOfList 两件（载体侦察如上；
    face-轨道双向刻画私有引擎六件按批 7→8→…→14 惯例同证重推导）。
  §3 枚举件：`enumerator_nil` :13865-:13876 ↦ enumeratorNil（真证；
    MEM_MAP 槽 = List.mem_map；尾墙 ~(x = []) 槽 = cons 形 +
    List.cons_ne_nil；enumBaseSpine/enumeratorSpine 定义层首落）。
  §4 `filter_replace` :13875-:13898 ↦ filterReplace（真证；fs 归纳两支
    ——命中支 replaceSpine if_pos + filter_append + filter_eq_nil_iff
    （all-P 前提）+ filter_cons_of_neg（~P f 前提）；未命中支 filter_cons
    双发 + P z 分流 + 归纳假设回喂；HOL ENOUGH_TO_SHOW_TAC 两槽
    （filter P xs = [] / ~has P xs）被 core filter_eq_nil_iff 一发吸收，
    机制简化记档）。
  §5 `snd_setFinal` :13900-:13906 ↦ sndSetFinal（rfl 零镜像直投件——
    载体在册（批 2 Face 结构），非止损）。
  §6 边界随收三件：`filter_nil` :13908-:13910 ↦ filterNil（core
    filter_eq_nil_iff 逐字同语句 + has 换装）；`finalGraph_filter`
    :13916-:13924 ↦ finalGraphFilter（filter_eq_self/filter_eq_nil_iff
    双向 + Graph.final isEmpty 桥）；`size_flatten_le` :13926-:13942 ↦
    sizeFlattenLe（sizel = LENGTH 载体 + flatten_cons/length_append 归纳
    + length_pos_of_ne_nil 非 nil 槽——HOL sumn/MAP 机制面被 core
    length_append 吸收，机制简化记档）。

  诚实记账：九件全真证（finalListSndIsFst/isRestrictedSizeFace/
  memFaceLemma/cardFaceOfList/enumeratorNil/filterReplace/sndSetFinal/
  filterNil/finalGraphFilter/sizeFlattenLe——十件含越章二件），零 sorry、
  零止损件、零记账债；新 def 三枚（enumBaseSpine/enumeratorSpine +
  越章零）。
  范围决策：批 56 射程收口至 :13942（final_list_snd_is_fst 主件 +
  is_restricted face 章 + 枚举/filter/snd 随收 + 边界三件——自然边界：
  下一件 :13944 `inj_on_list_of_faces` 起为 inj_on/map_list_pairs 新章）。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 57 接续点：HOL :13944 `inj_on_list_of_faces`
  `!L phi. inj_on phi (elements_of_list L) ==> list_of_faces (MAP (MAP
  phi) L) = MAP (MAP (\u. phi (FST u), phi (SND u))) (list_of_faces L)`
  （REWRITE[list_of_faces;GSYM MAP_o] + MAP_EQ + map_list_pairs 面——
  map_list_pairs 载体（list_pairs (MAP phi l) 逐点形）在册性开工先核；
  elements_of_list 载体 = TameLp elementsOfList 批 5 既档；inj_on ↦
  Set.InjOn 批 2 既档）→ 其后 :13959 `inj_on_list_of_darts`（同章对偶
  面）。
-/

import Kepler.Text.TameSpine.TameList55

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs nextEl fList listOfDarts GoodList findFaceDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text (orbitMap)
open Kepler.Text.TameLp (hypermapOfList nextEl_eq_getD getD_eq_getElem_of_lt
  getElem_idxOf idxOf_getElem dart_in_face findFaceDarts_eq_of_mem
  findFaceDarts_congr_of_mem findFaceDarts_nodup mem_darts_of_mem_findFace
  nextEl_mem_of_mem la7_length_listPairs faceMap_hypermapOfList)

variable {α : Type*}

/-! ### §1 final_list_snd_is_fst 主件（tame_list.hl:13805） -/

/-- **HOL `final_list_snd_is_fst`**（tame_list.hl:13805-:13829
`!L N r d. final_list L r /\ normal_list L N /\ all uniq L /\ MEM r N /\
MEM d r ==> MEM (SND d) (MAP FST (flatten N))`）。
证体：f_list_fst_snd（:6702 ↦ 批 10 fListFstSnd）ANTS 槽 =
normalListListOfDarts（批 5）+ List.mem_flatten（HOL
ASM_MESON_TAC[normal_list_list_of_darts;Seq.allP;Seq2.mem_flatten] 三发
的显式展开）；final_list 逐点方程 finalListSpine 定义形直取（批 7）；
SUBST1_TAC o GSYM 的 FST 换装并入 mem_map.mpr 证人侧；Seq2.mem_next_el
槽 = TameLp `nextEl_mem_of_mem`。 -/
theorem finalListSndIsFst (L : fgraph ℕ) {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hfin : finalListSpine L r) (hnl : NormalListSpine hL N)
    (hunL : ∀ l ∈ L, l.Nodup) (hrN : r ∈ N) (hd : d ∈ r) :
    d.2 ∈ N.flatten.map Prod.fst := by
  -- ANTS 槽：d ∈ list_of_darts L（normal_list_list_of_darts :3643 链）
  have hdD : d ∈ listOfDarts L :=
    normalListListOfDarts hnl d (List.mem_flatten.mpr ⟨r, hrN, hd⟩)
  have hfs : (fList L d).1 = d.2 := fListFstSnd L hunL hdD
  have hfl : fList L d = nextEl r d := hfin d hd
  refine List.mem_map.mpr ⟨nextEl r d,
    List.mem_flatten.mpr ⟨r, hrN, nextEl_mem_of_mem hd⟩, ?_⟩
  rw [← hfl]
  exact hfs

/-! ### §2 is_restricted 章（tame_list.hl:13831；载体 list_hypermap.vhl
     :596/:1081 越章首落） -/

/-! #### §2.0 face-轨道私有引擎（批 7/8/14 私件不跨文件，惯例同证重推导） -/

/-- 同表两下标相等则取元相等（proof-irrelevant getElem 换形器；泛用版）。 -/
private theorem getElemCon {α : Type*} {l : List α} {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a = b) :
    l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- 单步轨道：nodup 表第 `j` 项的 `next_el` = 第 `(j+1) mod len` 项。 -/
private theorem nextElStep {s : List (ℕ × ℕ)} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (hj1 : (j + 1) % s.length < s.length) :
    nextEl s (s[j]'hj) = s[(j + 1) % s.length]'hj1 := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  rw [nextEl_eq_getD (List.getElem_mem hj), idxOf_getElem hsn hj,
    getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]

/-- 轨道枚举：nodup 表上 `next_el` 幂从第 `j` 项出发按 mod 下标走。 -/
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
    rw [Function.iterate_succ_apply', ih hjk,
      nextElStep hsn hjk (Nat.mod_lt ((j + k) % s.length + 1) hpos)]
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

/-- face 轨道 ⊆ 面表（HOL `f_list_ext_orbit` 的 ⊆ 半向；批 7/8 私件同证
重推导，private 不跨文件可见）。 -/
private theorem faceOrbitSubsetFindFace {L : fgraph ℕ} (hL : GoodList L)
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

/-- face 轨道 ⊇ 面表（面表 = `next_el` 面-表的循环，轨道走遍全表；批 8
私件同证重推导）。 -/
private theorem faceTableSubsetFaceOrbit {L : fgraph ℕ} (hL : GoodList L)
    {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) :
    {y | y ∈ findFaceDarts L d} ⊆ (hypermapOfList L hL).face d := by
  have hdd : d ∈ findFaceDarts L d := dart_in_face L d |>.mpr hd
  have hFFnodup : (findFaceDarts L d).Nodup := findFaceDarts_nodup hL.1 d
  have hpos : 0 < (findFaceDarts L d).length := List.length_pos_of_mem hdd
  -- faceMap 在面表上逐点 = next_el 面表
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
  have hkey : ((findFaceDarts L d).idxOf d
        + (((findFaceDarts L d).idxOf y + (findFaceDarts L d).length
          - (findFaceDarts L d).idxOf d) % (findFaceDarts L d).length))
      % (findFaceDarts L d).length = (findFaceDarts L d).idxOf y := by
    rw [Nat.add_comm, Nat.mod_add_mod]
    have h2 : (findFaceDarts L d).idxOf y + (findFaceDarts L d).length
        - (findFaceDarts L d).idxOf d + (findFaceDarts L d).idxOf d
        = (findFaceDarts L d).length + (findFaceDarts L d).idxOf y := by omega
    rw [h2, Nat.add_mod_left, Nat.mod_eq_of_lt hidy]
  exact Eq.trans (getElemCon _ _ hkey) (getElem_idxOf hy)

/-! #### §2.1 mem_face_lemma / card_face_of_list 首落 -/

/-- **HOL `mem_face_lemma`**（list_hypermap.vhl:596
`good_list L /\ MEM f (list_of_faces L) ==> ?d. MEM d (list_of_darts L) /\
f = find_face L d`）。证体：face_rep 槽（批 31 faceRep）证人 f0 +
`HD f` 槽折算 = `listPairs f0` 首元（la7_length_listPairs 非空支）；
f = find_face 槽 = TameLp `findFaceDarts_eq_of_mem`（HOL
find_pair_list_unique 面的 Lean 件，(list_of_darts L).Nodup 前提 = GoodList
首合取）。 -/
theorem memFaceLemma (L : fgraph ℕ) (hL : GoodList L) {f : List (ℕ × ℕ)}
    (hf : f ∈ listOfFaces L) :
    ∃ d : ℕ × ℕ, d ∈ listOfDarts L ∧ f = findFaceDarts L d := by
  obtain ⟨f0, hEq, hf0, _⟩ := faceRep L f hf
  have hlen : 0 < (listPairs f0).length := by
    rw [la7_length_listPairs]
    exact List.length_pos_of_ne_nil (hL.2.1 f0 hf0)
  have hd' : (listPairs f0)[0]'hlen ∈ listPairs f0 := List.getElem_mem hlen
  refine ⟨(listPairs f0)[0]'hlen, ?_, ?_⟩
  · exact dart_in_face L _ |>.mp
      (by rw [findFaceDarts_eq_of_mem hL.1 hf0 hd']; exact hd')
  · rw [findFaceDarts_eq_of_mem hL.1 hf0 hd']
    exact hEq.symm

/-- **HOL `card_face_of_list`**（list_hypermap.vhl:1081
`good_list L /\ MEM d (list_of_darts L) ==> CARD (face (hypermap_of_list L)
d) = sizel (find_face L d)`）——sizel ↦ List.length；face_of_list 双向刻画
（§2.0 私有引擎）+ findFaceDarts_nodup（TameLp，uniq_find_face 面）+
Set.ncard_coe_finset + List.toFinset_card_of_nodup（card_set_of_list_uniq
面）。 -/
theorem cardFaceOfList (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    ((hypermapOfList L hL).face d).ncard = (findFaceDarts L d).length := by
  have hIff : (hypermapOfList L hL).face d = {y | y ∈ findFaceDarts L d} := by
    ext y
    exact ⟨fun hy => faceOrbitSubsetFindFace hL hd hy,
      fun hy => faceTableSubsetFaceOrbit hL hd hy⟩
  have hset : {y | y ∈ findFaceDarts L d}
      = ((findFaceDarts L d).toFinset : Set (ℕ × ℕ)) := by
    ext y
    exact ⟨fun h => Finset.mem_coe.mpr (List.mem_toFinset.mpr h),
      fun h => List.mem_toFinset.mp (Finset.mem_coe.mp h)⟩
  rw [hIff, hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (findFaceDarts_nodup hL.1 d)]

/-- **HOL `is_restricted_size_face`**（tame_list.hl:13831-:13850
`!L f. good_list L /\ is_restricted (hypermap_of_list L) /\
MEM f (list_of_faces L) ==> 3 <= sizel f`）。证体：is_restricted 尾合取槽
= `IsRestricted.three_le_ncard_face`（Hypermap.lean:9669）；darts 槽 =
dartHypermapOfList（批 5，批 6 isRestrictedEListNondeg 同式
List.mem_toFinset 折算）；card_face_of_list / mem_face_lemma 槽 = §2.1
两件——HOL 四发链（REWRITE[is_restricted] + mem_face_lemma +
card_face_of_list + dart_hypermap_of_list）逐句。 -/
theorem isRestrictedSizeFace (L : fgraph ℕ) (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted) {f : List (ℕ × ℕ)}
    (hf : f ∈ listOfFaces L) : 3 ≤ f.length := by
  obtain ⟨d, hdD, hff⟩ := memFaceLemma L hL hf
  have hdD2 : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
  have h3 := hres.three_le_ncard_face hdD2
  rwa [cardFaceOfList L hL hdD, ← hff] at h3

/-! ### §3 enumerator 章（tame_list.hl:13865） -/

/-- HOL `enumBase`（tame_defs2.hl:208-209
`enumBase nmax = MAP (\i. [i]) (upt 0 (SUC nmax))`）逐句镜像（upt ↦ Upt
批 2 载体，SUC nmax ↦ nmax + 1）。 -/
def enumBaseSpine (nmax : ℕ) : List (List ℕ) :=
  (Upt 0 (nmax + 1)).map fun i => [i]

/-- HOL `enumerator`（tame_defs2.hl:218-228，LET_THM 两槽 nmax = outer-2 /
k = inner-3 内联展开，POWER ↦ Function.iterate）逐句镜像。 -/
def enumeratorSpine (inner outer : ℕ) : List (List ℕ) :=
  ((enumAppendSpine (outer - 2))^[inner - 3] (enumBaseSpine (outer - 2))).map
    fun is => [0] ++ (is ++ [outer - 1])

/-- **HOL `enumerator_nil`**（tame_list.hl:13865-:13876
`!x i n. MEM x (enumerator i n) ==> ~(x = [])`）。MEM_MAP 槽 =
List.mem_map；尾墙 `~(x = [])` 槽：像元 `[0] ++ (is ++ [n-1])` 的 cons 形
（β + List.cons_append 一发，新雷区既档）+ List.cons_ne_nil
（HOL NOT_CONS_NIL 面）。 -/
theorem enumeratorNil {x : List ℕ} {i n : ℕ} (hx : x ∈ enumeratorSpine i n) :
    x ≠ [] := by
  unfold enumeratorSpine at hx
  obtain ⟨is, _, hxis⟩ := List.mem_map.mp hx
  intro hnil
  rw [← hxis] at hnil
  simp only [List.cons_append] at hnil
  exact List.cons_ne_nil 0 (is ++ [n - 1]) hnil

/-! ### §4 filter_replace（tame_list.hl:13875） -/

/-- **HOL `filter_replace`**（tame_list.hl:13875-:13898
`!fs P f xs. ~(P f) /\ all (\x. ~(P x)) xs ==> filter P (replace f xs fs) =
(filter P fs)`）。载体：replace 批 17 replaceSpine（tame_defs.hl:317 逐句
镜像）；Seq.filter ↦ List.filter（decide 装箱）。证体：fs 归纳两支——
命中支 `z = f`：replaceSpine if_pos + filter_append + filter_eq_nil_iff
（all-P 前提，HOL ENOUGH_TO_SHOW `filter P xs = []` 槽）+
filter_cons_of_neg（~P f 前提）；未命中支：filter_cons 双发 + `P z`
分流 + 归纳假设回喂（HOL MESON_TAC[Seq.allP] 面）。 -/
theorem filterReplace {α : Type*} [DecidableEq α] (P : α → Prop)
    [DecidablePred P] (f : α) (xs : List α) (hPf : ¬ P f)
    (hxs : ∀ x ∈ xs, ¬ P x) (fs : List α) :
    (replaceSpine f xs fs).filter (fun x => decide (P x)) =
      fs.filter (fun x => decide (P x)) := by
  induction fs with
  | nil => rfl
  | cons z zs ih =>
    by_cases hz : z = f
    · subst hz
      rw [replaceSpine, if_pos rfl, List.filter_append,
        List.filter_eq_nil_iff.mpr (fun x hx => by simpa using hxs x hx),
        List.nil_append, List.filter_cons_of_neg (by simpa using hPf)]
    · rw [replaceSpine, if_neg hz, List.filter_cons, List.filter_cons, ih]

/-! ### §5 snd_setFinal（tame_list.hl:13900） -/

/-- **HOL `snd_setFinal`**（tame_list.hl:13900-:13906
`!f. SND (setFinal f)`）。FORALL_PAIR_THM 面语句形先核命中：HOL
setFinal（tame_defs.hl:379 `setFinal (vs,f) = (vs,T)`）的 pair 载体 ↦
Face 结构（批 2 setFinalAlt 同层，vertices/isFinal 字段对），SND ↦
`.isFinal`，∀-pair 在 Lean 原生；HOL REWRITE_TAC[setFinal] 一发的
Lean 面 = 定义性 rfl（零镜像直投件——载体在册，非止损）。 -/
theorem sndSetFinal (f : Kepler.Graphs.Face) :
    (Kepler.Graphs.setFinal f).isFinal = true := rfl

/-! ### §6 边界随收（tame_list.hl:13908/:13916/:13926） -/

/-- **HOL `filter_nil`**（tame_list.hl:13908-:13910
`!P s. filter P s = [] <=> ~has P s`）——`has P s` ↦ `∃ x ∈ s, P x`
（Seq.has 载体折算）；mathlib/core List.filter_eq_nil_iff 逐字同语句。 -/
theorem filterNil {α : Type*} (P : α → Prop) [DecidablePred P] (s : List α) :
    s.filter (fun x => decide (P x)) = [] ↔ ¬ ∃ x ∈ s, P x := by
  rw [List.filter_eq_nil_iff]
  constructor
  · intro h hex
    obtain ⟨x, hx, hPx⟩ := hex
    exact h x hx (by simpa using hPx)
  · intro h x hx hPx
    exact h ⟨x, hx, by simpa using hPx⟩

/-- **HOL `finalGraph_filter`**（tame_list.hl:13916-:13924
`finalGraph g <=> (finals g = faces g)`）——载体批 2 既有（Graph.lean
:116/:119/:125；finalGraph ↦ Graph.final = nonFinals.isEmpty，新雷区
既档三层面名分割）；HOL all_filterP/filter_nil 链 ↦ core
List.filter_eq_self / List.filter_eq_nil_iff 双向。 -/
theorem finalGraphFilter (g : Kepler.Graphs.Graph) :
    Kepler.Graphs.Graph.final g = true ↔ Kepler.Graphs.finals g = g.faces := by
  show (g.faces.filter (fun f => !f.final)).isEmpty = true ↔
    g.faces.filter Kepler.Graphs.Face.final = g.faces
  rw [List.isEmpty_iff]
  constructor
  · intro h
    refine List.filter_eq_self.2 fun f hf => ?_
    by_contra hcon
    exact List.filter_eq_nil_iff.1 h f hf (by simpa using hcon)
  · intro h
    refine List.filter_eq_nil_iff.2 fun f hf hcon => ?_
    have hall := List.filter_eq_self.1 h f hf
    simp [hall] at hcon

/-- **HOL `size_flatten_le`**（tame_list.hl:13926-:13942
`!ss. all (\x. ~(x=[])) ss ==> sizel ss <= sizel (flatten ss)`）——
sizel = LENGTH（seq.vhl:159 载体既档）；flatten_cons/length_append 归纳
+ 非 nil 槽 length_pos_of_ne_nil（HOL sumn/MAP 机制面被 core
length_append 吸收，机制简化记档）。 -/
theorem sizeFlattenLe {α : Type*} {ss : List (List α)}
    (h : ∀ x ∈ ss, x ≠ []) : ss.length ≤ ss.flatten.length := by
  induction ss with
  | nil => exact Nat.le_refl _
  | cons x ss' ih =>
    rw [List.flatten_cons, List.length_cons, List.length_append]
    have hx : 0 < x.length := List.length_pos_of_ne_nil (h x List.mem_cons_self)
    have hih := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；十件正文 + 消费链槽全绿零 sorryAx——
#print axioms Kepler.Text.TameSpine.finalListSndIsFst
#print axioms Kepler.Text.TameSpine.memFaceLemma
#print axioms Kepler.Text.TameSpine.cardFaceOfList
#print axioms Kepler.Text.TameSpine.isRestrictedSizeFace
#print axioms Kepler.Text.TameSpine.enumeratorNil
#print axioms Kepler.Text.TameSpine.filterReplace
#print axioms Kepler.Text.TameSpine.sndSetFinal
#print axioms Kepler.Text.TameSpine.filterNil
#print axioms Kepler.Text.TameSpine.finalGraphFilter
#print axioms Kepler.Text.TameSpine.sizeFlattenLe
-/
